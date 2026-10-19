/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.SpinGlasses.SKDecoupled

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

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I,
  Section 1.3, Eq. (1.64).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

variable {ι : Type*} [Fintype ι]

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

end SpinGlasses
