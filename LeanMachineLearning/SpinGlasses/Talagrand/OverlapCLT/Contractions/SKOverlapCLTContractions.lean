/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKRectangularDerivative

/-!
# Decoupled contractions for the mixed-overlap recurrence

The last-site part of every fresh-replica factor is a finite linear combination of spin
pairs. Extend the existing rectangular monomial identity by the existing nested Gibbs
linearity theorem, keeping its exact incidence coefficient. This is the common contraction
needed to evaluate the term I of Talagrand's Eq. (1.312).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The rectangular last-site factor contracted against any finite linear combination of
spin pairs. Its coefficient is the signed sum of the existing incidence products; no new
spin-moment expansion is needed. The old-spin observable is arbitrary and the replica index
may be any finite type. -/
theorem sk_cavity_decoupled_rect_lincomb (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q)
    {R : Type*} [Fintype R] [DecidableEq R] {x₁ x₂ y₁ y₂ : R}
    {I : Type*} [Fintype I] (c : I → ℝ) (a b : I → R) (hab : ∀ i, a i ≠ b i)
    (hx₁y₁ : x₁ ≠ y₁) (hx₁y₂ : x₁ ≠ y₂) (hx₂y₁ : x₂ ≠ y₁) (hx₂y₂ : x₂ ≠ y₂)
    (G : (R → Fin N → ℤˣ) → ℝ) :
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
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : R → Fin (N + 1) → ℤˣ,
          G (fun r i => σ r i.castSucc) *
            ((((σ x₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ x₂ (Fin.last N) : ℤˣ) : ℝ)) *
              (((σ y₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ y₂ (Fin.last N) : ℤˣ) : ℝ)) *
              (∑ i : I, c i * (((σ (a i) (Fin.last N) : ℤˣ) : ℝ) *
                ((σ (b i) (Fin.last N) : ℤˣ) : ℝ))))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    ((∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1) *
      (∑ i : I, c i * (((((if x₁ = a i then 1 else 0) + (if x₁ = b i then 1 else 0) : ℕ) : ℝ) -
        (((if x₂ = a i then 1 else 0) + (if x₂ = b i then 1 else 0) : ℕ) : ℝ)) *
      ((((if y₁ = a i then 1 else 0) + (if y₁ = b i then 1 else 0) : ℕ) : ℝ) -
        (((if y₂ = a i then 1 else 0) + (if y₂ = b i then 1 else 0) : ℕ) : ℝ)))) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  have hEm (s : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) =>
        E (π / 2) x.1 x.2 s) := by
    dsimp [E, B]
    fun_prop
  let H : I → (R → Fin (N + 1) → ℤˣ) → ℝ := fun i σ =>
    G (fun r v => σ r v.castSucc) *
      (((σ x₁ (Fin.last N) : ℝ) - (σ x₂ (Fin.last N) : ℝ)) *
        ((σ y₁ (Fin.last N) : ℝ) - (σ y₂ (Fin.last N) : ℝ)) *
        ((σ (a i) (Fin.last N) : ℝ) * (σ (b i) (Fin.last N) : ℝ)))
  have hpoint (σ : R → Fin (N + 1) → ℤˣ) :
      G (fun r v => σ r v.castSucc) *
        (((σ x₁ (Fin.last N) : ℝ) - (σ x₂ (Fin.last N) : ℝ)) *
          ((σ y₁ (Fin.last N) : ℝ) - (σ y₂ (Fin.last N) : ℝ)) *
          (∑ i : I, c i * ((σ (a i) (Fin.last N) : ℝ) * (σ (b i) (Fin.last N) : ℝ)))) =
        ∑ i : I, c i * H i σ := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by dsimp [H]; ring
  simp_rw [hpoint]
  rw [integral_nested_gibbs_finset_sum
    (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    (E (π / 2)) hEm]
  -- Keep the integrals opaque when distributing the finite coefficient sum.
  generalize hO : (∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = O
  generalize hA : (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4
    ∂gaussianReal 0 1) = A
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := sk_cavity_decoupled_rect_monomial N β q h hfix
    (hab i) hx₁y₁ hx₁y₂ hx₂y₁ hx₂y₂ G
  change c i * (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ, H i σ
    ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
    ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = _
  dsimp only [H]
  rw [hi, hO, hA]
  ring

end SpinGlasses
