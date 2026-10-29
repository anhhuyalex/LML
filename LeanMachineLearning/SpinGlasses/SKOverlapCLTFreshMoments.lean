/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSiteSymmetry
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas

/-!
# Disorder-averaged fresh-replica representation of mixed T-moments

Talagrand's Eq. (1.305), including the disorder average. The Gibbs mean in a T-factor
depends on the disorder; the fresh-factor integrand on the other side does not.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **Eq. (1.305) under the actual SK disorder average.** Finite types enumerate pair,
single and global factors. Repeated original labels and empty factor types are allowed.
No high-temperature or fixed-point hypothesis is needed for this exact identity. -/
theorem sk_mixed_T_moment_eq_fresh (N : ℕ) (β h q : ℝ)
    {R P S G : Type*} [Fintype R] [Fintype P] [Fintype S] [Fintype G]
    (a a' : P → R) (d : S → R) :
    let J := P ⊕ (S ⊕ G)
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let b : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ((∏ p : P, (N + 1 : ℝ)⁻¹ * ∑ i,
          ((ρ (a p) i : ℝ) - b g i) * ((ρ (a' p) i : ℝ) - b g i)) *
        ∏ s : S, (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ (d s) i : ℝ) - b g i) * b g i) *
        (∏ _v : G, (((N + 1 : ℝ)⁻¹ * ∑ i, b g i * b g i) - q))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, ∫ σ : R ⊕ (J ⊕ J) → Fin (N + 1) → ℤˣ,
        ((∏ p : P, (N + 1 : ℝ)⁻¹ * ∑ i,
          ((σ (.inl (a p)) i : ℝ) - (σ (.inr (.inl (.inl p))) i : ℝ)) *
            ((σ (.inl (a' p)) i : ℝ) - (σ (.inr (.inr (.inl p))) i : ℝ))) *
        ∏ s : S, (N + 1 : ℝ)⁻¹ * ∑ i,
          ((σ (.inl (d s)) i : ℝ) - (σ (.inr (.inl (.inr (.inl s)))) i : ℝ)) *
            (σ (.inr (.inr (.inr (.inl s)))) i : ℝ)) *
        (∏ v : G, (((N + 1 : ℝ)⁻¹ * ∑ i,
          (σ (.inr (.inl (.inr (.inr v)))) i : ℝ) *
            (σ (.inr (.inr (.inr (.inr v)))) i : ℝ)) - q))
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro J E b
  apply integral_congr_ae (ae_of_all _ fun g => ?_)
  exact (MeasureTheory.integral_replica_centered_products
    (R := R) (P := P) (S := S) (G := G) (Measure.count.tilted (E g))
    (fun (σ : Fin (N + 1) → ℤˣ) (i : Fin (N + 1)) => (σ i : ℝ))
    (b g) (fun _ => rfl) (N + 1 : ℝ)⁻¹ q a a' d).symm


/-- **The disorder-averaged identity (1.305) on any selected factor subset.** Boolean
flags encode pair, single and global T-factors. The surrounding fresh replica family
stays fixed when factors are deleted, as needed by the moment recurrence. -/
theorem sk_flagged_T_moment_eq_fresh (N : ℕ) (β h q : ℝ)
    {R J : Type*} [Fintype R] [Fintype J]
    (a a' : J → R) (L S : J → Bool) (s : Finset J) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let b : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ j ∈ s,
      (((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - b g i else b g i) *
        (if S j then (ρ (a' j) i : ℝ) - b g i else b g i)) -
        (if L j || S j then 0 else q))
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, ∫ σ : R ⊕ (J ⊕ J) → Fin (N + 1) → ℤˣ, ∏ j ∈ s,
        (((N + 1 : ℝ)⁻¹ * ∑ i,
          (if L j then (σ (.inl (a j)) i : ℝ) - (σ (.inr (.inl j)) i : ℝ)
            else (σ (.inr (.inl j)) i : ℝ)) *
          (if S j then (σ (.inl (a' j)) i : ℝ) - (σ (.inr (.inr j)) i : ℝ)
            else (σ (.inr (.inr j)) i : ℝ))) - (if L j || S j then 0 else q))
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro E b
  apply integral_congr_ae (ae_of_all _ fun g => ?_)
  exact (MeasureTheory.integral_finset_prod_flagged_fresh_eq
    (R := R) (J := J) (Measure.count.tilted (E g))
    (fun (σ : Fin (N + 1) → ℤˣ) (i : Fin (N + 1)) => (σ i : ℝ))
    (b g) (fun _ => rfl) (N + 1 : ℝ)⁻¹ q a a' L S s).symm

end SpinGlasses
