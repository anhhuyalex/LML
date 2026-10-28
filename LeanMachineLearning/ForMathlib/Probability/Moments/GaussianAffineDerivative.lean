/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Variance derivative of a Gaussian average of a smooth function

For `f` with bounded first and second derivatives `f'`, `f''` and `γ = N(0,1)`, put
`G(w) = 𝔼 f(w z + h)`.  Stein's lemma gives `𝔼 [f'(w z + h) z] = w 𝔼 f''(w z + h)`, and
differentiation under the integral sign then gives `G'(w) = w 𝔼 f''(w z + h)`
(Talagrand, *Spin Glasses*, Eq. (1.75), after the substitution `w = β √x`).

## Main declarations

* `ProbabilityTheory.integral_deriv_comp_affine_mul_id_gaussianReal`: the Stein identity.
* `ProbabilityTheory.hasDerivAt_integral_comp_affine_gaussianReal`: the derivative in `w`.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace ProbabilityTheory

variable {f f' f'' : ℝ → ℝ} {C₁ C₂ : ℝ}

/-- **Stein's lemma for an affine Gaussian argument:** if `f'` has a bounded continuous derivative
`f''` and is itself bounded, then `𝔼 [f'(w z + h) z] = w 𝔼 f''(w z + h)` for `z ~ N(0,1)`. -/
theorem integral_deriv_comp_affine_mul_id_gaussianReal (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf''c : Continuous f'') (hC₁ : ∀ y, |f' y| ≤ C₁) (hC₂ : ∀ y, |f'' y| ≤ C₂) (h w : ℝ) :
    ∫ z, f' (w * z + h) * z ∂(gaussianReal 0 1) =
      w * ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1) := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have hF : ∀ z, HasDerivAt (fun y => f' (w * y + h)) (w * f'' (w * z + h)) z := fun z => by
    have hl : HasDerivAt (fun y : ℝ => w * y + h) w z := by
      simpa using ((hasDerivAt_id' z).const_mul w).add_const h
    exact ((hf' (w * z + h)).comp z hl).congr_deriv (mul_comm _ _)
  have hxF : Integrable (fun z : ℝ => z * f' (w * z + h)) (gaussianReal 0 1) := by
    refine ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).norm.const_mul C₁).mono'
      (((continuous_id'.mul (hf'c.comp (by fun_prop : Continuous fun z : ℝ => w * z + h))))
        |>.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hC₁ _).trans le_rfl) (abs_nonneg _)
  have hF' : Integrable (fun z : ℝ => w * f'' (w * z + h)) (gaussianReal 0 1) :=
    (integrable_const (|w| * C₂)).mono'
      ((continuous_const.mul (hf''c.comp (by fun_prop))).aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hC₂ _) (abs_nonneg _))
  have := integral_id_mul_gaussianReal_eq 1 hF hxF hF'
  simp only [NNReal.coe_one, one_mul] at this
  rw [← integral_const_mul]
  simpa [mul_comm] using this

/-- **Derivative of the Gaussian average in the standard deviation:** under the assumptions of
`integral_deriv_comp_affine_mul_id_gaussianReal`, and if `f` is an antiderivative of `f'` with
`f(w z + h)` integrable, `(d/dw) 𝔼 f(w z + h) = w 𝔼 f''(w z + h)`. -/
theorem hasDerivAt_integral_comp_affine_gaussianReal (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y) (hf''c : Continuous f'') (hC₁ : ∀ y, |f' y| ≤ C₁)
    (hC₂ : ∀ y, |f'' y| ≤ C₂) (h w : ℝ)
    (hint : Integrable (fun z => f (w * z + h)) (gaussianReal 0 1)) :
    HasDerivAt (fun v => ∫ z, f (v * z + h) ∂(gaussianReal 0 1))
      (w * ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1)) w := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have h_diff : HasDerivAt (fun v => ∫ z, f (v * z + h) ∂(gaussianReal 0 1))
      (∫ z, f' (w * z + h) * z ∂(gaussianReal 0 1)) w := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
      (F := fun v z => f (v * z + h)) (F' := fun v z => f' (v * z + h) * z)
      univ_mem
      (Eventually.of_forall fun v =>
        (hfc.comp (by fun_prop : Continuous fun z : ℝ => v * z + h)).aestronglyMeasurable)
      hint
      ((hf'c.comp (by fun_prop : Continuous fun z : ℝ => w * z + h)).mul
        continuous_id').aestronglyMeasurable
      (bound := fun z => C₁ * |z|)
      (ae_of_all _ fun z v _ => ?_)
      ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).norm.const_mul C₁)
      (ae_of_all _ fun z v _ => ?_)).2
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC₁ _) (abs_nonneg _)
    · have hl : HasDerivAt (fun v : ℝ => v * z + h) z v := by
        simpa using ((hasDerivAt_id' v).mul_const z).add_const h
      exact (hf (v * z + h)).comp v hl
  rwa [integral_deriv_comp_affine_mul_id_gaussianReal hf' hf''c hC₁ hC₂ h w] at h_diff

end ProbabilityTheory
