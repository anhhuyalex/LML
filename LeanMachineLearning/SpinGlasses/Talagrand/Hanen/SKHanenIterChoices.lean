/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIteratedDeriv
public import Mathlib.Data.Fin.Embedding

/-!
# Canonical choices in the iterated cavity derivative

The recursive choice type records the actual three-family index selected at every derivative.
Its weights and endpoint positions retain the data needed for exact pairing identities,
where an existential expansion and a total absolute-weight bound are insufficient.
-/

@[expose] public section

open Finset
open scoped BigOperators
namespace SpinGlasses

/-- A sequence of actual replica-pair choices in the iterated derivative.
Each step adds two replicas before the subsequent choices are made. -/
def SKCavityDerivativeChoices : ℕ → ℕ → Type
  | 0, _ => Unit
  | m + 1, n => SKCavityReplicaPair n × SKCavityDerivativeChoices m (n + 2)

instance (m n : ℕ) : Fintype (SKCavityDerivativeChoices m n) := by
  induction m generalizing n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ m ih =>
    letI := ih (n + 2)
    exact inferInstanceAs (Fintype (SKCavityReplicaPair n × SKCavityDerivativeChoices m (n + 2)))

/-- Positions of the original replicas after all fresh replicas have been introduced. -/
def skCavityIterOldEmbedding : (m n : ℕ) → Fin n ↪ Fin (skCavityIterReplicaCount m n)
  | 0, _ => Function.Embedding.refl _
  | m + 1, n => ((Fin.succEmb n).trans (Fin.succEmb (n + 1))).trans
      (skCavityIterOldEmbedding m (n + 2))

/-- The exact signed weight of a derivative choice sequence. -/
noncomputable def skCavityChoiceWeight : (m n : ℕ) → SKCavityDerivativeChoices m n → ℝ
  | 0, _, _ => 1
  | m + 1, n, c => skCavityReplicaPairWeight n c.1 * skCavityChoiceWeight m (n + 2) c.2

/-- The derivative endpoints, expressed in the final common replica family. -/
def skCavityChoiceEndpoints : (m n : ℕ) → SKCavityDerivativeChoices m n →
    Fin m → Fin (skCavityIterReplicaCount m n) × Fin (skCavityIterReplicaCount m n)
  | 0, _, _ => fun r => r.elim0
  | m + 1, n, c => Fin.cons
      (skCavityIterOldEmbedding m (n + 2)
          (skCavityReplicaEquiv n (skCavityReplicaPairMap c.1).1),
        skCavityIterOldEmbedding m (n + 2)
          (skCavityReplicaEquiv n (skCavityReplicaPairMap c.1).2))
      (skCavityChoiceEndpoints m (n + 2) c.2)

/-- The two endpoints chosen at any derivative step are distinct. -/
theorem skCavityChoiceEndpoints_ne (m n : ℕ) (c : SKCavityDerivativeChoices m n) (r : Fin m) :
    (skCavityChoiceEndpoints m n c r).1 ≠ (skCavityChoiceEndpoints m n c r).2 := by
  induction m generalizing n with
  | zero => exact r.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun r => ?_) r
    · simp only [skCavityChoiceEndpoints]
      exact (skCavityIterOldEmbedding m (n + 2)).injective.ne
        ((skCavityReplicaEquiv n).injective.ne (skCavityReplicaPair_ne c.1))
    · exact ih (n + 2) c.2 r

/-- The original replicas occupy the final interval starting at position `2*m`. -/
@[simp] theorem skCavityIterOldEmbedding_val (m n : ℕ) (r : Fin n) :
    (skCavityIterOldEmbedding m n r).val = r.val + 2 * m := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    change (skCavityIterOldEmbedding m (n + 2) r.succ.succ).val = _
    rw [ih]
    simp only [Fin.val_succ]
    omega

/-- Exact canonical expansion of the iterated cavity kernel.
All weights and endpoint positions are the recursively defined data above. -/
theorem skCavityIterKernel_eq_choice_sum (N m n : ℕ) (β q : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (τ : Fin (skCavityIterReplicaCount m n) → Fin (N + 1) → ℤˣ) :
    skCavityIterKernel N β q m n f τ =
      f (fun r => τ (skCavityIterOldEmbedding m n r)) *
        ∑ c : SKCavityDerivativeChoices m n, skCavityChoiceWeight m n c *
          ∏ r : Fin m, skCavityPathKernel N β q
            (τ (skCavityChoiceEndpoints m n c r).1) (τ (skCavityChoiceEndpoints m n c r).2) := by
  induction m generalizing n with
  | zero =>
    simp only [skCavityIterKernel, skCavityChoiceWeight, Fin.prod_univ_zero, mul_one]
    change f τ = f τ * ∑ _ : Unit, (1 : ℝ)
    simp
  | succ m ih =>
    rw [skCavityIterKernel, ih]
    unfold skCavityPathStep
    rw [skCavityPathDerivKernel_eq_pair_sum]
    simp only [SKCavityDerivativeChoices, skCavityChoiceWeight, skCavityChoiceEndpoints,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    erw [Fintype.sum_prod_type]
    rw [mul_assoc, Finset.sum_mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => sum_congr rfl fun c _ => ?_
    ring

/-- A final replica is original exactly when its index is at least `2*m`. -/
theorem mem_range_skCavityIterOldEmbedding (m n : ℕ)
    (r : Fin (skCavityIterReplicaCount m n)) :
    (∃ i, skCavityIterOldEmbedding m n i = r) ↔ 2 * m ≤ r.val := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [skCavityIterOldEmbedding_val]
    omega
  · intro hr
    have hlt : r.val < n + 2 * m := by
      simpa only [skCavityIterReplicaCount_eq] using r.isLt
    let i : Fin n := ⟨r.val - 2 * m, by omega⟩
    refine ⟨i, Fin.ext ?_⟩
    rw [skCavityIterOldEmbedding_val]
    dsimp only [i]
    omega

/-- If the second endpoint of the first choice is original, that choice belongs to the
old-old family. Both fresh-replica families have a second endpoint below `2*(m+1)`. -/
theorem skCavityChoiceHead_old (m n : ℕ) (c : SKCavityDerivativeChoices (m + 1) n)
    (hsupport : 2 * (m + 1) ≤ (skCavityChoiceEndpoints (m + 1) n c 0).2.val) :
    ∃ p : FinPairs n, c.1 = .inl p := by
  rcases c with ⟨j, c⟩
  cases j with
  | inl j => exact ⟨j, rfl⟩
  | inr j =>
    cases j with
    | inl j =>
      change 2 * (m + 1) ≤ (skCavityIterOldEmbedding m (n + 2)
        (skCavityReplicaEquiv n (some none))).val at hsupport
      rw [skCavityIterOldEmbedding_val] at hsupport
      change 2 * (m + 1) ≤ 1 + 2 * m at hsupport
      omega
    | inr j =>
      change 2 * (m + 1) ≤ (skCavityIterOldEmbedding m (n + 2)
        (skCavityReplicaEquiv n none)).val at hsupport
      rw [skCavityIterOldEmbedding_val] at hsupport
      change 2 * (m + 1) ≤ 0 + 2 * m at hsupport
      omega

/-- A choice sequence whose endpoints are all original has signed weight exactly one.
Every fresh-replica family is excluded by its endpoint position, rather than by a bound. -/
theorem skCavityChoiceWeight_eq_one_of_old (m n : ℕ) (c : SKCavityDerivativeChoices m n)
    (hsupport : ∀ r : Fin m,
      2 * m ≤ (skCavityChoiceEndpoints m n c r).1.val ∧
      2 * m ≤ (skCavityChoiceEndpoints m n c r).2.val) :
    skCavityChoiceWeight m n c = 1 := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rcases c with ⟨j, c⟩
    obtain ⟨p, rfl⟩ := skCavityChoiceHead_old m n (j, c) (hsupport 0).2
    change skCavityReplicaPairWeight n (.inl p) * skCavityChoiceWeight m (n + 2) c = 1
    rw [skCavityReplicaPairWeight, one_mul]
    apply ih
    intro r
    have hs := hsupport r.succ
    change 2 * (m + 1) ≤ (skCavityChoiceEndpoints m (n + 2) c r).1.val ∧
      2 * (m + 1) ≤ (skCavityChoiceEndpoints m (n + 2) c r).2.val at hs
    omega

end SpinGlasses
