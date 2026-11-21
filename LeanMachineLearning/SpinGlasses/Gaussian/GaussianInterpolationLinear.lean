/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianInterpolationBounded
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram

/-!
# Gaussian interpolation of linear forms of i.i.d. Gaussians

For two families of linear forms `X l = a l ⬝ ξ`, `Y l = b l ⬝ ξ` of an i.i.d. standard Gaussian
vector `ξ` with `a l ⬝ b k = 0`, `hasDerivAt_integral_comp_trig_boundedC2` reads with the
covariances replaced by dot products of the coefficient vectors. In Talagrand's cavity in `M`
(Section 2.3) the coefficient vectors are `cavityCoef σ` (old part) and `√q` (common `z`).

* `SpinGlasses.hasDerivAt_integral_comp_trig_boundedC2_dotProduct`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Real

namespace SpinGlasses

variable {κ K T : Type*} [Fintype κ] [DecidableEq κ] [Fintype K]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- **Interpolation of linear forms of a standard Gaussian vector.** -/
theorem hasDerivAt_integral_comp_trig_boundedC2_dotProduct (a b : κ → K → ℝ)
    (hab : ∀ l k, a l ⬝ᵥ b k = 0) {F : T × (κ → ℝ) → ℝ} (hF : BoundedC2 F)
    {τ τ' : ℝ → T} (hτ : ∀ s, HasDerivAt τ (τ' s) s) {A : ℝ} (hA : ∀ s, ‖τ' s‖ ≤ A) (t : ℝ) :
    HasDerivAt (fun s => ∫ ξ, F (τ s, fun l => Real.cos s * (a l ⬝ᵥ ξ) + Real.sin s * (b l ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : K => gaussianReal 0 1))
      ((Real.sin t * Real.cos t * ∑ l, ∑ k, (b l ⬝ᵥ b k - a l ⬝ᵥ a k) *
        ∫ ξ, fderiv ℝ (fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single l 1))
          (fun m => Real.cos t * (a m ⬝ᵥ ξ) + Real.sin t * (b m ⬝ᵥ ξ)) (Pi.single k 1)
          ∂(Measure.pi fun _ : K => gaussianReal 0 1)) +
        ∫ ξ, fderiv ℝ F (τ t, fun m => Real.cos t * (a m ⬝ᵥ ξ) + Real.sin t * (b m ⬝ᵥ ξ))
          (τ' t, 0) ∂(Measure.pi fun _ : K => gaussianReal 0 1)) t := by
  have hXY : HasGaussianLaw (fun (ξ : K → ℝ) (s : κ ⊕ κ) => Sum.elim a b s ⬝ᵥ ξ)
      (Measure.pi fun _ : K => gaussianReal 0 1) := hasGaussianLaw_dotProduct_family _
  have heq : (fun (ξ : K → ℝ) (s : κ ⊕ κ) =>
      Sum.elim (fun l (ξ : K → ℝ) => a l ⬝ᵥ ξ) (fun l (ξ : K → ℝ) => b l ⬝ᵥ ξ) s ξ) =
      fun ξ s => Sum.elim a b s ⬝ᵥ ξ := by
    funext ξ s
    cases s <;> rfl
  have key := hasDerivAt_integral_comp_trig_boundedC2
    (P := Measure.pi fun _ : K => gaussianReal 0 1) (X := fun l ξ => a l ⬝ᵥ ξ)
    (Y := fun l ξ => b l ⬝ᵥ ξ) (by rw [heq]; exact hXY)
    (fun l => integral_dotProduct_pi_gaussianReal _)
    (fun l => integral_dotProduct_pi_gaussianReal _)
    (fun l k => by rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal, hab]) hF hτ hA t
  simpa only [integral_dotProduct_mul_dotProduct_pi_gaussianReal] using key

end SpinGlasses
