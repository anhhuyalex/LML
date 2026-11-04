/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTContractions

/-!
# Fresh-replica contractions in the pair-factor recurrence

At the decoupled endpoint, a leading pair factor contracts only with another pair factor
having the same unordered original labels. Single and global factors give zero. Disjoint
sum-type labels enforce freshness, without an enumeration of quartic spin moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

private theorem fresh_rect_incidence {R J : Type*} [DecidableEq R] [DecidableEq J]
    (x y a b : R) (hxy : x ≠ y) (p u : J) (hpu : p ≠ u) (L S : Bool) :
    let A : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
      if L && i.1 then .inl a else .inr (.inl u)
    let B : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
      if S && i.2 then .inl b else .inr (.inr u)
    let c : Bool × Bool → ℝ := fun i =>
      (if L then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
      (if S then if i.2 then 1 else -1 else if i.2 then 1 else 0)
    (∑ i : Bool × Bool, c i * (
      ((((if (Sum.inl x : R ⊕ (J ⊕ J)) = A i then 1 else 0) +
          (if (Sum.inl x : R ⊕ (J ⊕ J)) = B i then 1 else 0) : ℕ) : ℝ) -
        (((if (Sum.inr (.inl p) : R ⊕ (J ⊕ J)) = A i then 1 else 0) +
          (if (Sum.inr (.inl p) : R ⊕ (J ⊕ J)) = B i then 1 else 0) : ℕ) : ℝ)) *
      ((((if (Sum.inl y : R ⊕ (J ⊕ J)) = A i then 1 else 0) +
          (if (Sum.inl y : R ⊕ (J ⊕ J)) = B i then 1 else 0) : ℕ) : ℝ) -
        (((if (Sum.inr (.inr p) : R ⊕ (J ⊕ J)) = A i then 1 else 0) +
          (if (Sum.inr (.inr p) : R ⊕ (J ⊕ J)) = B i then 1 else 0) : ℕ) : ℝ)))) =
      if L && S then (if x = a ∧ y = b then 1 else 0) +
        (if x = b ∧ y = a then 1 else 0) else 0 := by
  intro A B c
  cases L <;> cases S <;>
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
    simp_all [Fintype.sum_prod_type, A, B, c]

/-- **The two flagged replicas of a factor are distinct.** For the four Boolean-flagged choices
of a pair of replicas in a fresh-replica expansion (original label `a`, `b` when the flag is on,
the fresh replica of `j` otherwise), the two replicas never coincide. This is the distinctness
hypothesis `a ≠ b` of Eq. (1.297) for the rewritten factor. -/
theorem flagged_pair_ne {R J : Type*} (a b : R) (j : J) (L S : Bool)
    (hab : L = true → S = true → a ≠ b) (i : Bool × Bool) :
    (if L && i.1 then (Sum.inl a : R ⊕ (J ⊕ J)) else .inr (.inl j)) ≠
      (if S && i.2 then .inl b else .inr (.inr j)) := by
  rcases i with ⟨i, k⟩
  cases L <;> cases S <;> cases i <;> cases k <;> simp_all

/-- **The decoupled coefficient in Eq. (1.312), for all three factor classes.**
The Boolean pair `(true,true)` represents a pair factor, `(true,false)` a single factor,
and `(false,false)` a global factor. Only the pair case can survive, and only when its
unordered original labels match those of the leading pair. All old-spin observables are
allowed. The exact identity needs no high-temperature hypothesis. -/
theorem sk_cavity_decoupled_fresh_factor (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂gaussianReal 0 1 = q)
    {R J : Type*} [Fintype R] [Fintype J] [DecidableEq R]
    (x y a b : R) (hxy : x ≠ y) (p u : J) (hpu : p ≠ u) (L S : Bool)
    (hab : L = true → S = true → a ≠ b)
    (G : ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let e0 : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      ((ε (.inl x) : ℝ) - (ε (.inr (.inl p)) : ℝ)) *
        ((ε (.inl y) : ℝ) - (ε (.inr (.inr p)) : ℝ))
    let eu : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      (if L then (ε (.inl a) : ℝ) - (ε (.inr (.inl u)) : ℝ)
        else (ε (.inr (.inl u)) : ℝ)) *
      (if S then (ε (.inl b) : ℝ) - (ε (.inr (.inr u)) : ℝ)
        else (ε (.inr (.inr u)) : ℝ))
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R ⊕ (J ⊕ J) → Fin (N + 1) → ℤˣ,
      G (fun r i => σ r i.castSucc) *
        (e0 (fun r => σ r (Fin.last N)) * eu (fun r => σ r (Fin.last N)))
      ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    ((∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1) - 2 * q + 1) *
      (if L && S then (if x = a ∧ y = b then 1 else 0) +
        (if x = b ∧ y = a then 1 else 0) else 0) *
      ∫ g', ∫ ρ : (R ⊕ (J ⊕ J)) → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  classical
  intro B E e0 eu
  let A : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
    if L && i.1 then .inl a else .inr (.inl u)
  let bb : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
    if S && i.2 then .inl b else .inr (.inr u)
  let c : Bool × Bool → ℝ := fun i =>
    (if L then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  have hpair (i : Bool × Bool) : A i ≠ bb i := flagged_pair_ne a b u L S hab i
  have hpoint (ε : R ⊕ (J ⊕ J) → ℤˣ) :
      eu ε = ∑ i : Bool × Bool, c i * ((ε (A i) : ℝ) * (ε (bb i) : ℝ)) := by
    cases L <;> cases S <;> simp [Fintype.sum_prod_type, A, bb, c, eu] <;> ring
  have hk := sk_cavity_decoupled_rect_lincomb N β q h hfix c A bb hpair
    (x₁ := Sum.inl x) (x₂ := Sum.inr (Sum.inl p))
    (y₁ := Sum.inl y) (y₂ := Sum.inr (Sum.inr p))
    (by simpa using hxy) (by simp) (by simp) (by simp) G
  have hc := fresh_rect_incidence x y a b hxy p u hpu L S
  simp only [hpoint, e0]
  rw [hk, hc]

end SpinGlasses
