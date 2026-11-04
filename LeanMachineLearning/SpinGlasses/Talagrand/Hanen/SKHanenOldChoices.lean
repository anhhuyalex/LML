/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIterChoices

/-!
# Original-replica choices in the iterated cavity derivative

An ordered tuple of pairs of original replicas determines a unique derivative choice sequence.
Conversely every sequence supported on original replicas arises this way. This separates the
recursive introduction of fresh replicas from the later matching and orientation sums.
-/

@[expose] public section

open Finset
open scoped BigOperators
namespace SpinGlasses

/-- Realize an ordered tuple of original-replica pairs as actual derivative choices. -/
def skCavityOldChoices : (m n : ℕ) → (Fin m → FinPairs n) → SKCavityDerivativeChoices m n
  | 0, _, _ => ()
  | m + 1, n, p => (.inl (p 0), skCavityOldChoices m (n + 2) (fun r =>
      ⟨((p r.succ).val.1.succ.succ, (p r.succ).val.2.succ.succ),
        by simpa only [Fin.succ_lt_succ_iff] using (p r.succ).property⟩))

/-- The endpoints of an original-replica choice tuple are its original pairs, embedded
into the final replica family. -/
@[simp] theorem skCavityChoiceEndpoints_old (m n : ℕ) (p : Fin m → FinPairs n) (r : Fin m) :
    skCavityChoiceEndpoints m n (skCavityOldChoices m n p) r =
      (skCavityIterOldEmbedding m n (p r).val.1,
        skCavityIterOldEmbedding m n (p r).val.2) := by
  induction m generalizing n with
  | zero => exact r.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun r => ?_) r
    · rfl
    · exact ih (n + 2) _ r

/-- Different ordered tuples give different derivative choice sequences. -/
theorem skCavityOldChoices_injective (m n : ℕ) : Function.Injective (skCavityOldChoices m n) := by
  intro p q hpq
  funext r
  have h := congrArg (fun c => skCavityChoiceEndpoints m n c r) hpq
  simp only [skCavityChoiceEndpoints_old, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext ((skCavityIterOldEmbedding m n).injective h.1)
    ((skCavityIterOldEmbedding m n).injective h.2))

/-- Every derivative choice sequence supported on original replicas comes from an
ordered tuple of original pairs. The inverse is obtained without choosing a matching. -/
theorem exists_skCavityOldChoices_of_old (m n : ℕ) (c : SKCavityDerivativeChoices m n)
    (hsupport : ∀ r : Fin m,
      2 * m ≤ (skCavityChoiceEndpoints m n c r).1.val ∧
      2 * m ≤ (skCavityChoiceEndpoints m n c r).2.val) :
    ∃ p, skCavityOldChoices m n p = c := by
  induction m generalizing n with
  | zero =>
    change Unit at c
    cases c
    exact ⟨Fin.elim0, rfl⟩
  | succ m ih =>
    rcases c with ⟨j, c⟩
    obtain ⟨j, rfl⟩ := skCavityChoiceHead_old m n (j, c) (hsupport 0).2
    have htail (r : Fin m) :
        2 * m ≤ (skCavityChoiceEndpoints m (n + 2) c r).1.val ∧
        2 * m ≤ (skCavityChoiceEndpoints m (n + 2) c r).2.val := by
      have hs := hsupport r.succ
      change 2 * (m + 1) ≤ (skCavityChoiceEndpoints m (n + 2) c r).1.val ∧
        2 * (m + 1) ≤ (skCavityChoiceEndpoints m (n + 2) c r).2.val at hs
      omega
    obtain ⟨p, rfl⟩ := ih (n + 2) c htail
    have hp (r : Fin m) : 2 ≤ (p r).val.1.val ∧ 2 ≤ (p r).val.2.val := by
      have hs := hsupport r.succ
      change 2 * (m + 1) ≤
          (skCavityChoiceEndpoints m (n + 2) (skCavityOldChoices m (n + 2) p) r).1.val ∧
        2 * (m + 1) ≤
          (skCavityChoiceEndpoints m (n + 2) (skCavityOldChoices m (n + 2) p) r).2.val at hs
      simp only [skCavityChoiceEndpoints_old, skCavityIterOldEmbedding_val] at hs
      omega
    let q : Fin m → FinPairs n := fun r =>
      ⟨(⟨(p r).val.1.val - 2, by have := (p r).val.1.isLt; omega⟩,
        ⟨(p r).val.2.val - 2, by have := (p r).val.2.isLt; omega⟩), by
          have := (p r).property
          have := hp r
          change (p r).val.1.val - 2 < (p r).val.2.val - 2
          omega⟩
    refine ⟨Fin.cons j q, ?_⟩
    change (Sum.inl j, skCavityOldChoices m (n + 2) _) = _
    congr 2
    funext r
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;>
      simp only [Fin.cons_succ, Fin.val_succ] <;> dsimp only [q] <;>
      have := hp r <;> omega

/-- A sum supported on original-replica choices is exactly the sum over ordered tuples
of original pairs. This identity applies to any additive commutative monoid of weights. -/
theorem sum_skCavityOldChoices {A : Type*} [AddCommMonoid A] (m n : ℕ)
    (G : SKCavityDerivativeChoices m n → A)
    (hsupport : ∀ c, G c ≠ 0 → ∀ r : Fin m,
      2 * m ≤ (skCavityChoiceEndpoints m n c r).1.val ∧
      2 * m ≤ (skCavityChoiceEndpoints m n c r).2.val) :
    ∑ c, G c = ∑ p : Fin m → FinPairs n, G (skCavityOldChoices m n p) := by
  symm
  refine Fintype.sum_of_injective _ (skCavityOldChoices_injective m n) _ G ?_ (fun _ => rfl)
  intro c hc
  by_contra hnonzero
  exact hc (exists_skCavityOldChoices_of_old m n c (hsupport c hnonzero))

end SpinGlasses
