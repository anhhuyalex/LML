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

/-- **The cavity smoothing is `C²` with bounded derivatives.** With `g = exp ∘ u` for a `C²`
potential `u ≤ D` with `|u'| ≤ D₁`, `|u''| ≤ D₂`, the map
`(τ₁, τ₂, y) ↦ ∬ e^{u (y + τ₁ b + τ₂ ξ)} dγ(b) dγ(ξ)` is `BoundedC2`. -/
theorem boundedC2_integral_exp_comp_gaussian {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (ℓ A Bf : P →L[ℝ] ℝ) (hu : ContDiff ℝ 2 u) {D D₁ D₂ : ℝ}
    (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) :
    BoundedC2 (fun p : P => ∫ η, Real.exp (u (ℓ p + η.1 * A p + η.2 * Bf p))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
  refine boundedC2_integral_gaussian_smoothing ℓ A Bf (g := fun x => Real.exp (u x))
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

/-- **The cavity smoothing is `C²`.** -/
theorem contDiff_two_integral_exp_comp_gaussian {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (ℓ A Bf : P →L[ℝ] ℝ) (hu : ContDiff ℝ 2 u) {D D₁ D₂ : ℝ}
    (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) :
    ContDiff ℝ 2 (fun p : P => ∫ η, Real.exp (u (ℓ p + η.1 * A p + η.2 * Bf p))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) :=
  (boundedC2_integral_exp_comp_gaussian ℓ A Bf hu hD hD₁ hD₂).contDiff

/-- **Lower bound for the cavity smoothing.** If `-B ≤ u ≤ D` then
`e^{-B} ≤ ∬ e^{u (y + τ₁ b + τ₂ ξ)} dγ dγ ≤ e^D`. -/
theorem exp_neg_le_integral_exp_comp_gaussian (hu : Continuous u) {B D : ℝ}
    (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D) (y a b : ℝ) :
    Real.exp (-B) ≤ ∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hint : Integrable (fun η : ℝ × ℝ => Real.exp (u (y + η.1 * a + η.2 * b)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    Integrable.of_bound (C := Real.exp D)
      ((Real.continuous_exp.comp (hu.comp (by fun_prop))).aestronglyMeasurable)
      (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (hD _))
  have := integral_mono (integrable_const (Real.exp (-B))) hint
    (fun η => Real.exp_le_exp.2 (hB _))
  simpa using this

/-- **The cavity replica ratio is `C²` with bounded derivatives.** For a `C²` potential with
`-B ≤ u ≤ D`, `|u'| ≤ D₁`, `|u''| ≤ D₂`, positive weights `w` on a finite spin set `κ` and any
observable `f` of `R`-tuples of spins, the function of the smoothing parameters `τ = (τ₁, τ₂)` and
the spin fields `v : κ → ℝ`
`(∑_ā f ā ∏_r w (ā r) ψ_τ (v (ā r))) / (∑_a w a ψ_τ (v a)) ^ |R|`, with
`ψ_τ (y) = ∬ e^{u (y + τ₁ b + τ₂ ξ)} dγ dγ`, is `BoundedC2` on `ℝ² × (κ → ℝ)`. -/
theorem boundedC2_cavityRatio {κ R : Type*} [Fintype κ] [Fintype R] [DecidableEq R] [Nonempty κ]
    (hu : ContDiff ℝ 2 u) {B D D₁ D₂ : ℝ} (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    {w : κ → ℝ} (hw : ∀ a, 0 < w a) (f : (R → κ) → ℝ) :
    BoundedC2 (fun x : (ℝ × ℝ) × (κ → ℝ) =>
      (∑ ā : R → κ, f ā * ∏ r, (w (ā r) * ∫ η, Real.exp (u (x.2 (ā r) + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))) /
      (∑ a, w a * ∫ η, Real.exp (u (x.2 a + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ^ Fintype.card R) := by
  let A : ((ℝ × ℝ) × (κ → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (κ → ℝ))
  let Bf : ((ℝ × ℝ) × (κ → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (κ → ℝ))
  let L : κ → ((ℝ × ℝ) × (κ → ℝ)) →L[ℝ] ℝ := fun a =>
    (ContinuousLinearMap.proj a).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (κ → ℝ))
  have hψ : ∀ a, BoundedC2 (fun x : (ℝ × ℝ) × (κ → ℝ) =>
      ∫ η, Real.exp (u (x.2 a + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := fun a => by
    simpa [L, A, Bf] using boundedC2_integral_exp_comp_gaussian (L a) A Bf hu hD hD₁ hD₂
  exact BoundedC2.replicaRatio hψ hw (Real.exp_pos (-B)) (fun a x =>
    exp_neg_le_integral_exp_comp_gaussian hu.continuous hB hD _ _ _) f

end SpinGlasses
