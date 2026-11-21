/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GaussianSmoothingRegularity

/-!
# Regularity of the cavity smoothing `ψ`

Talagrand Section 2.3. For a potential `u` that is `C²` with `u ≤ D`, `|u'| ≤ D₁`, `|u''| ≤ D₂`,
the function `g = exp ∘ u` is `C²` with `g ≤ e^D`, `|g'| ≤ e^D D₁`, `|g''| ≤ e^D (D₁² + D₂)`, so the
two-Gaussian smoothing `ψ(τ, y) = ∬ e^{u (y + τ₁ b + τ₂ ξ)} dγ dγ` is `C²` in `(τ, y)`.

* `SpinGlasses.contDiff_two_integral_exp_comp_gaussian`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {u : ℝ → ℝ}

theorem deriv_exp_comp_of_contDiff_two (hu : ContDiff ℝ 2 u) (x : ℝ) :
    deriv (fun x => Real.exp (u x)) x = Real.exp (u x) * deriv u x :=
  ((hu.differentiable (by norm_num) x).hasDerivAt.exp).deriv

theorem deriv_deriv_exp_comp_of_contDiff_two (hu : ContDiff ℝ 2 u) (x : ℝ) :
    deriv (deriv fun x => Real.exp (u x)) x =
      Real.exp (u x) * (deriv u x ^ 2 + deriv (deriv u) x) := by
  have h1 : deriv (fun x => Real.exp (u x)) = fun x => Real.exp (u x) * deriv u x :=
    funext (deriv_exp_comp_of_contDiff_two hu)
  have hdu := hu.differentiable_deriv_two x
  have hu1 := (hu.differentiable (by norm_num) x).hasDerivAt
  rw [h1]
  have := (hu1.exp).mul hdu.hasDerivAt
  rw [show (fun x => Real.exp (u x) * deriv u x) =
    (fun x => Real.exp (u x)) * deriv u from rfl, this.deriv]
  ring

/-- **The cavity smoothing is `C²`.** With `g = exp ∘ u` for a `C²` potential `u ≤ D` with
`|u'| ≤ D₁`, `|u''| ≤ D₂`, the map `(τ₁, τ₂, y) ↦ ∬ e^{u (y + τ₁ b + τ₂ ξ)} dγ(b) dγ(ξ)` is `C²`. -/
theorem contDiff_two_integral_exp_comp_gaussian (hu : ContDiff ℝ 2 u) {D D₁ D₂ : ℝ}
    (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) :
    ContDiff ℝ 2 (fun p : (ℝ × ℝ) × ℝ => ∫ η, Real.exp (u (p.2 + η.1 * p.1.1 + η.2 * p.1.2))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
  refine contDiff_two_integral_gaussian_smoothing (g := fun x => Real.exp (u x))
    (B₀ := Real.exp D) (B₁ := Real.exp D * D₁) (B₂ := Real.exp D * (D₁ ^ 2 + D₂))
    (Real.contDiff_exp.comp hu) (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hD x)
  · rw [deriv_exp_comp_of_contDiff_two hu, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.2 (hD x)) (hD₁ x) (abs_nonneg _) (Real.exp_pos _).le
  · rw [deriv_deriv_exp_comp_of_contDiff_two hu, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (Real.exp_le_exp.2 (hD x)) ?_ (abs_nonneg _) (Real.exp_pos _).le
    refine (abs_add_le _ _).trans (add_le_add ?_ (hD₂ x))
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hD₁ x) 2

end SpinGlasses
