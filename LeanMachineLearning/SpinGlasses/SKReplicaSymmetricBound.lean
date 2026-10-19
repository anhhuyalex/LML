/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.SpinGlasses.SKDecoupled
public import LeanMachineLearning.SpinGlasses.SKFirstMoment

/-!
# The Gaussian cavity field in Guerra's replica-symmetric interpolation

This module begins the smart-path calculation from Talagrand, *Spin Glasses*,
Section 1.3.  The independent cavity field has the explicit form
`β √q ∑ i, z i * σ i`, where the `z i` are independent standard Gaussians.
Its covariance is `β² q (σ ⬝ᵥ τ)`.  The result is deliberately stated for
arbitrary finite real vectors, rather than only hypercube configurations, so it
can be reused by spherical and relaxed spin models.

The remaining smart-path derivative and the replica-symmetric bound are not
formalized in this module yet.

## Main declaration

* `SpinGlasses.integral_decoupled_gaussian_field_mul`: covariance of Guerra's
  independent site-Gaussian field.
* `SpinGlasses.integral_sk_pair_field_mul`: covariance of the pair-indexed SK
  Gaussian field before its off-diagonal coefficient sum is simplified.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I,
  Section 1.3, Eq. (1.64).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

variable {ι : Type*} [Fintype ι]

/-- The covariance of two Gaussian linear forms, with the SK normalization made explicit.
This is stated for arbitrary coefficient vectors on any finite index type so that the same
calculation can be reused for pair, tensor, or cavity Gaussian fields. -/
theorem integral_normalized_gaussian_linear_form_mul {κ : Type*} [Fintype κ]
    (n β : ℝ) (hn : 0 ≤ n) (a b : κ → ℝ) :
    ∫ g : κ → ℝ,
      ((Real.sqrt n)⁻¹ * β * ∑ k, g k * a k) *
        ((Real.sqrt n)⁻¹ * β * ∑ k, g k * b k)
      ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
      n⁻¹ * β ^ 2 * (a ⬝ᵥ b) := by
  have ha (g : κ → ℝ) : ∑ k, g k * a k = a ⬝ᵥ g := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hb (g : κ → ℝ) : ∑ k, g k * b k = b ⬝ᵥ g := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp_rw [ha, hb]
  calc
    ∫ g : κ → ℝ, ((Real.sqrt n)⁻¹ * β * (a ⬝ᵥ g)) *
        ((Real.sqrt n)⁻¹ * β * (b ⬝ᵥ g))
        ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
        ((Real.sqrt n)⁻¹ * β) ^ 2 *
          ∫ g : κ → ℝ, (a ⬝ᵥ g) * (b ⬝ᵥ g)
            ∂(Measure.pi fun _ : κ => gaussianReal 0 1) := by
      have h_integrand :
          (fun g : κ → ℝ => ((Real.sqrt n)⁻¹ * β * (a ⬝ᵥ g)) *
            ((Real.sqrt n)⁻¹ * β * (b ⬝ᵥ g))) =
            fun g => ((Real.sqrt n)⁻¹ * β) ^ 2 * ((a ⬝ᵥ g) * (b ⬝ᵥ g)) := by
        ext g
        ring
      rw [h_integrand, integral_const_mul]
    _ = n⁻¹ * β ^ 2 * (a ⬝ᵥ b) := by
      rw [ProbabilityTheory.integral_dotProduct_mul_dotProduct_pi_gaussianReal]
      have hsquare : (Real.sqrt n)⁻¹ ^ 2 = n⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hn]
      rw [mul_pow, hsquare]

/-- The covariance of the pair-indexed SK Gaussian field before the elementary off-diagonal
sum is rewritten in terms of the overlap. -/
theorem integral_sk_pair_field_mul {N : ℕ} (β : ℝ)
    (σ τ : Fin N → ℤˣ) :
    ∫ g : FinPairs N → ℝ,
      ((Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
        ((Real.sqrt N)⁻¹ * β *
          ∑ p : FinPairs N, g p * ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      (N : ℝ)⁻¹ * β ^ 2 *
        ∑ p : FinPairs N,
          (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
            ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ) := by
  let a : FinPairs N → ℝ := fun p => ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)
  let b : FinPairs N → ℝ := fun p => ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ)
  have hmain := integral_normalized_gaussian_linear_form_mul (N : ℝ) β
    (Nat.cast_nonneg N) a b
  simpa only [a, b, dotProduct, mul_assoc] using hmain

/-- The covariance of Guerra's independent site-Gaussian field.  This is the
decoupled contribution to the covariance difference in Eq. (1.64). -/
theorem integral_decoupled_gaussian_field_mul (β q : ℝ) (hq : 0 ≤ q)
    (σ τ : ι → ℝ) :
    ∫ z : ι → ℝ,
      (β * Real.sqrt q * ∑ i, z i * σ i) *
        (β * Real.sqrt q * ∑ i, z i * τ i)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      β ^ 2 * q * (σ ⬝ᵥ τ) := by
  have hσ (z : ι → ℝ) : ∑ i, z i * σ i = σ ⬝ᵥ z := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hτ (z : ι → ℝ) : ∑ i, z i * τ i = τ ⬝ᵥ z := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [hσ, hτ]
  calc
    ∫ z : ι → ℝ, (β * Real.sqrt q * (σ ⬝ᵥ z)) *
        (β * Real.sqrt q * (τ ⬝ᵥ z)) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
        (β * Real.sqrt q) ^ 2 *
          ∫ z : ι → ℝ, (σ ⬝ᵥ z) * (τ ⬝ᵥ z)
            ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
      have h_integrand :
          (fun z : ι → ℝ => (β * Real.sqrt q * (σ ⬝ᵥ z)) *
            (β * Real.sqrt q * (τ ⬝ᵥ z))) =
            fun z => (β * Real.sqrt q) ^ 2 * ((σ ⬝ᵥ z) * (τ ⬝ᵥ z)) := by
        ext z
        ring
      rw [h_integrand, integral_const_mul]
    _ = β ^ 2 * q * (σ ⬝ᵥ τ) := by
      rw [ProbabilityTheory.integral_dotProduct_mul_dotProduct_pi_gaussianReal,
        mul_pow, Real.sq_sqrt hq]

/-- The algebraic covariance difference used by Guerra's smart path.  The hypotheses are the
interacting and decoupled covariance computations; the conclusion is Eq. (1.64), written with
the conventional factor one half in the Gaussian interpolation covariance difference. -/
theorem smart_path_half_covariance_difference_eq [Nonempty ι] (β q : ℝ)
    (σ τ : ι → ℝ) (C D : ℝ)
    (hC : C = (Fintype.card ι : ℝ) * β ^ 2 / 2 *
      (((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ 2 - (Fintype.card ι : ℝ)⁻¹))
    (hD : D = β ^ 2 * q * (σ ⬝ᵥ τ)) :
    (Fintype.card ι : ℝ)⁻¹ * ((C - D) / 2) =
      β ^ 2 / 4 *
        (((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ) - q) ^ 2 - q ^ 2 -
          (Fintype.card ι : ℝ)⁻¹) := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hdot : (σ ⬝ᵥ τ) = (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) := by
    calc
      σ ⬝ᵥ τ = 1 * (σ ⬝ᵥ τ) := by ring
      _ = ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)⁻¹) * (σ ⬝ᵥ τ) := by
        rw [mul_inv_cancel₀ hN]
      _ = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) := by
        ring
  rw [hC, hD, hdot]
  field_simp
  ring

end SpinGlasses
