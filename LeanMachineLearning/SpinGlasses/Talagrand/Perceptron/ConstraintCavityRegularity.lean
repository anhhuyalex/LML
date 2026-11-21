/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GaussianSmoothingRegularity
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianSmoothingPath
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianReplicaRatioHessian
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianInterpolationLinear
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityCovariance

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

/-- **Upper bound for the cavity smoothing.** If `u ≤ D` then `ψ ≤ e^D`. -/
theorem integral_exp_comp_gaussian_le {D : ℝ} (hD : ∀ x, u x ≤ D) (y a b : ℝ) :
    ∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) ≤ Real.exp D := by
  have := norm_integral_le_of_norm_le_const
    (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (f := fun η : ℝ × ℝ => Real.exp (u (y + η.1 * a + η.2 * b))) (C := Real.exp D)
    (ae_of_all _ fun η => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (hD _))
  simpa using (le_abs_self _).trans this

/-- **The cavity smoothing is positive.** -/
theorem integral_exp_comp_gaussian_pos (hu : Continuous u) {B D : ℝ} (hB : ∀ x, -B ≤ u x)
    (hD : ∀ x, u x ≤ D) (y a b : ℝ) :
    0 < ∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  (Real.exp_pos _).trans_le (exp_neg_le_integral_exp_comp_gaussian hu hB hD y a b)

/-- **The logarithm of the cavity smoothing lies in `[-B, D]`**, so two values differ by at most
`B + D`. -/
theorem abs_log_integral_exp_comp_gaussian_sub_le (hu : Continuous u) {B D : ℝ}
    (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D) (y a b y' a' b' : ℝ) :
    |Real.log (∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) -
      Real.log (∫ η, Real.exp (u (y' + η.1 * a' + η.2 * b'))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))| ≤ B + D := by
  have hlow : ∀ y a b : ℝ, -B ≤ Real.log (∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := fun y a b => by
    rw [← Real.log_exp (-B)]
    exact Real.log_le_log (Real.exp_pos _) (exp_neg_le_integral_exp_comp_gaussian hu hB hD y a b)
  have hup : ∀ y a b : ℝ, Real.log (∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ≤ D := fun y a b => by
    rw [← Real.log_exp D]
    exact Real.log_le_log (integral_exp_comp_gaussian_pos hu hB hD y a b)
      (integral_exp_comp_gaussian_le hD y a b)
  rw [abs_le]
  constructor <;> linarith [hlow y a b, hup y a b, hlow y' a' b', hup y' a' b']

/-- **The log-derivative of the cavity smoothing is bounded.** With `−B ≤ u ≤ D`,
`|∬ g'| / ∬ g ≤ e^{D + B} D₁`, `g = e^u`. -/
theorem abs_integral_deriv_exp_comp_div_le (hu : ContDiff ℝ 2 u) {B D D₁ : ℝ}
    (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁) (y a b : ℝ) :
    |∫ η, deriv (fun x => Real.exp (u x)) (y + η.1 * a + η.2 * b)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))| /
      ∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) ≤ Real.exp (D + B) * D₁ := by
  have hlow := exp_neg_le_integral_exp_comp_gaussian hu.continuous hB hD y a b
  have hpos : 0 < ∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := (Real.exp_pos _).trans_le hlow
  have hnum : |∫ η, deriv (fun x => Real.exp (u x)) (y + η.1 * a + η.2 * b)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))| ≤ Real.exp D * D₁ := by
    have := norm_integral_le_of_norm_le_const
      (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
      (f := fun η : ℝ × ℝ => deriv (fun x => Real.exp (u x)) (y + η.1 * a + η.2 * b))
      (C := Real.exp D * D₁)
      (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, deriv_exp_comp_of_contDiff_two hu, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (Real.exp_le_exp.2 (hD _)) (hD₁ _) (abs_nonneg _) (Real.exp_pos _).le)
    simpa using this
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0)
  rw [div_le_iff₀ hpos]
  calc _ ≤ Real.exp D * D₁ := hnum
    _ = Real.exp (D + B) * D₁ * Real.exp (-B) := by
        rw [Real.exp_add]; field_simp; rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (mul_nonneg (Real.exp_pos _).le hD₁0)

/-- **The cavity smoothing is `C²` in the spin variable** for fixed smoothing parameters. -/
theorem contDiff_two_integral_exp_comp_gaussian_section (hu : ContDiff ℝ 2 u) {D D₁ D₂ : ℝ}
    (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) (c₁ c₂ : ℝ) :
    ContDiff ℝ 2 (fun y : ℝ => ∫ η, Real.exp (u (y + η.1 * c₁ + η.2 * c₂))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
  have h := contDiff_two_integral_exp_comp_gaussian
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))
    hu hD hD₁ hD₂
  have hmap : ContDiff ℝ 2 (fun y : ℝ => (((c₁, c₂) : ℝ × ℝ), y)) :=
    contDiff_const.prodMk contDiff_id
  simpa [Function.comp_def] using h.comp hmap

/-- **The first two `y`-derivatives of the cavity smoothing.** With `g = e^u` and
`ψ_τ (y) = ∬ g (y + b τ₁ + ξ τ₂) dγ dγ`, `ψ_τ' = ∬ g'` and `ψ_τ'' = ∬ g''`, for a `C²` potential
with `u ≤ D`, `|u'| ≤ D₁`, `|u''| ≤ D₂`. -/
theorem hasDerivAt_integral_exp_comp_gaussian_y (hu : ContDiff ℝ 2 u) {D D₁ D₂ : ℝ}
    (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) (τ₁ τ₂ y : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ η, Real.exp (u (y + η.1 * τ₁ + η.2 * τ₂))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      (∫ η, deriv (fun x => Real.exp (u x)) (y + η.1 * τ₁ + η.2 * τ₂)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) y ∧
    HasDerivAt (fun y : ℝ => ∫ η, deriv (fun x => Real.exp (u x)) (y + η.1 * τ₁ + η.2 * τ₂)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      (∫ η, deriv (deriv fun x => Real.exp (u x)) (y + η.1 * τ₁ + η.2 * τ₂)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) y := by
  have hg : ContDiff ℝ 2 fun x => Real.exp (u x) := Real.contDiff_exp.comp hu
  have hg1 : Differentiable ℝ fun x => Real.exp (u x) := hg.differentiable (by norm_num)
  have hdg : Differentiable ℝ (deriv fun x => Real.exp (u x)) := hg.differentiable_deriv_two
  have hdg' : ContDiff ℝ 1 (deriv fun x => Real.exp (u x)) := by
    have h : ContDiff ℝ (1 + 1) fun x => Real.exp (u x) := by simpa [one_add_one_eq_two] using hg
    exact (contDiff_succ_iff_deriv.1 h).2.2
  have b0 : ∀ x, |Real.exp (u x)| ≤ Real.exp D := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hD x)
  have b1 : ∀ x, |deriv (fun x => Real.exp (u x)) x| ≤ Real.exp D * D₁ := fun x => by
    rw [deriv_exp_comp_of_contDiff_two hu, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.2 (hD x)) (hD₁ x) (abs_nonneg _) (Real.exp_pos _).le
  have b2 : ∀ x, |deriv (deriv fun x => Real.exp (u x)) x| ≤ Real.exp D * (D₁ ^ 2 + D₂) :=
    fun x => by
    rw [deriv_deriv_exp_comp_of_contDiff_two hu, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (Real.exp_le_exp.2 (hD x)) ?_ (abs_nonneg _) (Real.exp_pos _).le
    refine (abs_add_le _ _).trans (add_le_add ?_ (hD₂ x))
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hD₁ x) 2
  refine ⟨hasDerivAt_integral_gaussian_smoothing_y (g := fun x => Real.exp (u x))
    (fun x => (hg1 x).hasDerivAt) (hg.continuous_deriv (by norm_num)) b0 b1 τ₁ τ₂ y, ?_⟩
  exact hasDerivAt_integral_gaussian_smoothing_y (g := deriv fun x => Real.exp (u x))
    (fun x => (hdg x).hasDerivAt) (hdg'.continuous_deriv le_rfl) b1 b2 τ₁ τ₂ y

/-- **Time derivative of the cavity smoothing along the interpolation.** Along
`τ(s) = (cos s · a₀, sin s √(1 - q))`, for `q ≤ 1`,
`d/ds ∬ e^{u (x + cos s a₀ b + sin s √(1-q) ξ)} dγ dγ = sin s cos s (1 - q - a₀²) ψ_{τ(s)}''(x)`
with `ψ'' = ∬ g''`, `g = e^u` (the heat equation of the two-Gaussian smoothing). -/
theorem hasDerivAt_integral_exp_comp_gaussian_time (hu : ContDiff ℝ 2 u) {D D₁ D₂ : ℝ}
    (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {q : ℝ} (hq : q ≤ 1) (a₀ x t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ η, Real.exp (u (x + Real.cos s * a₀ * η.1 +
          Real.sin s * Real.sqrt (1 - q) * η.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      (Real.sin t * Real.cos t * (1 - q - a₀ ^ 2) *
        ∫ η, deriv (deriv fun x => Real.exp (u x))
          (x + Real.cos t * a₀ * η.1 + Real.sin t * Real.sqrt (1 - q) * η.2)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) t := by
  have hg : ContDiff ℝ 2 fun x => Real.exp (u x) := Real.contDiff_exp.comp hu
  have hg1 : Differentiable ℝ fun x => Real.exp (u x) := hg.differentiable (by norm_num)
  have hdg : Differentiable ℝ (deriv fun x => Real.exp (u x)) := hg.differentiable_deriv_two
  have hdg' : ContDiff ℝ 1 (deriv fun x => Real.exp (u x)) := by
    have h : ContDiff ℝ (1 + 1) fun x => Real.exp (u x) := by simpa [one_add_one_eq_two] using hg
    exact (contDiff_succ_iff_deriv.1 h).2.2
  have b0 : ∀ x, |Real.exp (u x)| ≤ Real.exp D := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hD x)
  have b1 : ∀ x, |deriv (fun x => Real.exp (u x)) x| ≤ Real.exp D * D₁ := fun x => by
    rw [deriv_exp_comp_of_contDiff_two hu, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.2 (hD x)) (hD₁ x) (abs_nonneg _) (Real.exp_pos _).le
  have b2 : ∀ x, |deriv (deriv fun x => Real.exp (u x)) x| ≤ Real.exp D * (D₁ ^ 2 + D₂) :=
    fun x => by
    rw [deriv_deriv_exp_comp_of_contDiff_two hu, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (Real.exp_le_exp.2 (hD x)) ?_ (abs_nonneg _) (Real.exp_pos _).le
    refine (abs_add_le _ _).trans (add_le_add ?_ (hD₂ x))
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hD₁ x) 2
  have ha : ∀ s, HasDerivAt (fun s => Real.cos s * a₀) (-(Real.sin s * a₀)) s := fun s => by
    simpa using (Real.hasDerivAt_cos s).mul_const a₀
  have hb : ∀ s, HasDerivAt (fun s => Real.sin s * Real.sqrt (1 - q))
      (Real.cos s * Real.sqrt (1 - q)) s := fun s => by
    simpa using (Real.hasDerivAt_sin s).mul_const (Real.sqrt (1 - q))
  have key := hasDerivAt_integral_gaussian_pair_path (f := fun x => Real.exp (u x))
    (f' := deriv fun x => Real.exp (u x)) (f'' := deriv (deriv fun x => Real.exp (u x)))
    (fun x => (hg1 x).hasDerivAt) (fun x => (hdg x).hasDerivAt) (hdg'.continuous_deriv le_rfl)
    b0 b1 b2 (A := |a₀|) (B := Real.sqrt (1 - q)) ha hb
    (fun s => by
      rw [abs_neg, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one s))
    (fun s => by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (Real.abs_cos_le_one s)) x t
  refine key.congr_deriv ?_
  have hs : Real.sqrt (1 - q) * Real.sqrt (1 - q) = 1 - q :=
    Real.mul_self_sqrt (sub_nonneg.2 hq)
  congr 1
  linear_combination (Real.sin t * Real.cos t) * hs

/-- **The `τ`-derivative of the cavity ratio along the interpolation.** For `F(c, v)` the cavity
replica ratio and `τ(s) = (cos s a₀, sin s √(1 - q))`, `q ≤ 1`,
`D_τ F (τ t, y) (τ' t, 0) = ∑_l sin t cos t (1 - q - a₀²) (ψ_t''/ψ_t)(y_l) ⟨(N_l - n G_l) f⟩`
with `ψ_t'' = ∬ g''`. -/
theorem fderiv_cavityRatio_time {κ R : Type*} [Fintype κ] [Fintype R] [DecidableEq R]
    [DecidableEq κ] [Nonempty κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (hu : ContDiff ℝ 2 u) {B D D₁ D₂ : ℝ} (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {q : ℝ} (hq : q ≤ 1)
    {w : κ → ℝ} (hw : ∀ a, 0 < w a) (f : (R → κ) → ℝ) (a₀ t : ℝ) (y : κ → ℝ) :
    fderiv ℝ (fun x : (ℝ × ℝ) × (κ → ℝ) =>
      (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ∫ η, Real.exp (u (x.2 (σ r) + η.1 * x.1.1 +
          η.2 * x.1.2)) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))) /
      (∑ a, w a * ∫ η, Real.exp (u (x.2 a + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ^ Fintype.card R)
      ((Real.cos t * a₀, Real.sin t * Real.sqrt (1 - q)), y)
      ((-(Real.sin t * a₀), Real.cos t * Real.sqrt (1 - q)), 0) =
    ∑ l, (Real.sin t * Real.cos t * (1 - q - a₀ ^ 2) *
        ∫ η, deriv (deriv fun x => Real.exp (u x)) (y l + η.1 * (Real.cos t * a₀) +
          η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) /
        (∫ η, Real.exp (u (y l + η.1 * (Real.cos t * a₀) +
          η.2 * (Real.sin t * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) *
      ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (fun a => Real.log (w a) + Real.log
            (∫ η, Real.exp (u (y a + η.1 * (Real.cos t * a₀) +
              η.2 * (Real.sin t * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod
                (gaussianReal 0 1))))).real {l}) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (fun a => Real.log (w a) + Real.log
          (∫ η, Real.exp (u (y a + η.1 * (Real.cos t * a₀) +
            η.2 * (Real.sin t * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod
              (gaussianReal 0 1))))) := by
  have hFd := (boundedC2_cavityRatio (R := R) hu hB hD hD₁ hD₂ hw f).differentiable
  have hpos : ∀ (s x : ℝ), 0 < ∫ η, Real.exp (u (x + η.1 * (Real.cos s * a₀) +
      η.2 * (Real.sin s * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    fun s x => (Real.exp_pos _).trans_le (exp_neg_le_integral_exp_comp_gaussian hu.continuous hB hD
      x _ _)
  have hψ : ∀ x : ℝ, HasDerivAt (fun s : ℝ => ∫ η, Real.exp (u (x + η.1 * (Real.cos s * a₀) +
      η.2 * (Real.sin s * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      (Real.sin t * Real.cos t * (1 - q - a₀ ^ 2) *
        ∫ η, deriv (deriv fun x => Real.exp (u x)) (x + η.1 * (Real.cos t * a₀) +
          η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) t
      := fun x => by
    have h := hasDerivAt_integral_exp_comp_gaussian_time hu hD hD₁ hD₂ hq a₀ x t
    have e : ∀ (s : ℝ) (η : ℝ × ℝ), x + η.1 * (Real.cos s * a₀) +
        η.2 * (Real.sin s * Real.sqrt (1 - q)) =
        x + Real.cos s * a₀ * η.1 + Real.sin s * Real.sqrt (1 - q) * η.2 := fun s η => by ring
    simpa only [e] using h
  have param := hasDerivAt_replicaRatio_param (R := R) (κ := κ) (w := w)
    (ψ := fun s x => ∫ η, Real.exp (u (x + η.1 * (Real.cos s * a₀) +
      η.2 * (Real.sin s * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (dψ := fun x => Real.sin t * Real.cos t * (1 - q - a₀ ^ 2) *
        ∫ η, deriv (deriv fun x => Real.exp (u x)) (x + η.1 * (Real.cos t * a₀) +
          η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    hw hpos hψ f y
  have ha : HasDerivAt (fun s => Real.cos s * a₀) (-(Real.sin t * a₀)) t := by
    simpa using (Real.hasDerivAt_cos t).mul_const a₀
  have hb : HasDerivAt (fun s => Real.sin s * Real.sqrt (1 - q))
      (Real.cos t * Real.sqrt (1 - q)) t := by
    simpa using (Real.hasDerivAt_sin t).mul_const (Real.sqrt (1 - q))
  have hpath : HasDerivAt (fun s : ℝ => ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)), y))
      ((-(Real.sin t * a₀), Real.cos t * Real.sqrt (1 - q)), (0 : κ → ℝ)) t :=
    (ha.prodMk hb).prodMk (hasDerivAt_const t y)
  have h1 := (hFd ((Real.cos t * a₀, Real.sin t * Real.sqrt (1 - q)), y)).hasFDerivAt
    |>.comp_hasDerivAt t hpath
  exact h1.unique param

section Vectors

variable {N : ℕ}

/-- The quenched part of `S_{M,t}(σ)` as the linear form `cavityCoef σ ⬝ (g_M, a_M)` of the full
Gaussian block `ξ = ((g_M, a_M), z)`: its coefficient vector (zero on `z`). -/
theorem cavityVecA_dotProduct (σ τ : PerceptronSpin N) (t : ℝ) :
    (Sum.elim (cavityCoef N t σ) (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ
      (Sum.elim (cavityCoef N t τ) (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) =
      cavityCoef N t σ ⬝ᵥ cavityCoef N t τ := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- The common field `√q z` as the coefficient vector `(0, √q)`; the covariance of two such forms
is `q`. -/
theorem cavityVecB_dotProduct {q : ℝ} (hq : 0 ≤ q) :
    (Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ
      (Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) = q := by
  simp [dotProduct, Fintype.sum_sum_type, Real.mul_self_sqrt hq]

/-- The old part and the common field are uncorrelated. -/
theorem cavityVecA_dotProduct_cavityVecB (σ : PerceptronSpin N) (t q : ℝ) :
    (Sum.elim (cavityCoef N t σ) (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ
      (Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) = 0 := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- **The cavity interpolation for a `BoundedC2` functional.** With
`X_σ = cavityCoef σ ⬝ (g_M, a_M)` and `Y_σ = √q z` linear forms of the i.i.d. Gaussian block
`ξ = ((g_M, a_M), z)`, the derivative of
`s ↦ 𝔼_ξ F(τ s, cos s X + sin s Y)` at `t` is
`sin t cos t ∑_{σ,σ'} (q - C(σ,σ')) 𝔼 ∂²_{σσ'} F + 𝔼 D_τ F (τ t, ·) (τ' t, 0)` with
`C(σ,σ') = cavityCoef σ ⬝ cavityCoef σ'`. -/
theorem hasDerivAt_integral_comp_trig_boundedC2_cavity {T : Type*} [NormedAddCommGroup T]
    [NormedSpace ℝ T] {F : T × (PerceptronSpin N → ℝ) → ℝ} (hF : BoundedC2 F) {q : ℝ}
    (p : ℝ) (hq : 0 ≤ q) {τ τ' : ℝ → T} (hτ : ∀ s, HasDerivAt τ (τ' s) s) {A : ℝ}
    (hA : ∀ s, ‖τ' s‖ ≤ A) (t : ℝ) :
    HasDerivAt (fun s => ∫ ξ, F (τ s, fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ)
          (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) +
        Real.sin s * ((Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1))
      ((Real.sin t * Real.cos t * ∑ σ, ∑ σ', (q - cavityCoef N p σ ⬝ᵥ cavityCoef N p σ') *
        ∫ ξ, fderiv ℝ (fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single σ 1))
          (fun m => Real.cos t * ((Sum.elim (cavityCoef N p m) (fun _ : Unit => (0 : ℝ)) :
            (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin t * ((Sum.elim
            (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
            (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) (Pi.single σ' 1)
          ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) +
        ∫ ξ, fderiv ℝ F (τ t, fun m => Real.cos t * ((Sum.elim (cavityCoef N p m)
          (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) +
          Real.sin t * ((Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ))
            (fun _ : Unit => Real.sqrt q) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) (τ' t, 0)
          ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) t := by
  have key := hasDerivAt_integral_comp_trig_boundedC2_dotProduct
    (K := (Fin N ⊕ Unit) ⊕ Unit)
    (fun σ => (Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
      (Fin N ⊕ Unit) ⊕ Unit → ℝ))
    (fun σ => (Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
      (Fin N ⊕ Unit) ⊕ Unit → ℝ))
    (fun σ τ => cavityVecA_dotProduct_cavityVecB σ p q) hF hτ hA t
  simpa only [cavityVecA_dotProduct, cavityVecB_dotProduct hq] using key

end Vectors

section Combined

variable {N : ℕ} {R : Type*} [Fintype R] [DecidableEq R]

/-- **The pathwise derivative of the quenched cavity average for a spin-only observable.** For the
cavity replica ratio `F`, the Gaussian block `ξ = ((g_M, a_M), z)`,
`X_σ = cavityCoef_p σ ⬝ (g_M, a_M)` (smart-path parameter `p`), `Y_σ = √q z` and
`y_σ(ξ) = cos t X_σ + sin t Y_σ` (angle `t`), with the smoothing `ψ_t` and its derivatives
`ψ₁ = ∬ g'`, `ψ₂ = ∬ g''` (`g = e^u`), the derivative of `s ↦ 𝔼_ξ F(τ s, cos s X + sin s Y)` at
the angle `t` is `sin t cos t 𝔼_ξ ⟨f Θ⟩`, where `⟨·⟩` is the `R`-replica Gibbs average for the site
energies `log w + log ψ_t (y(ξ))`, `u_σ = ψ₁/ψ_t (y_σ)`, `c_{σσ'} = q - C_p(σ,σ')`,
`X_σ = N_σ - n G_σ` and `Θ = ∑_{σ,σ'} c u u (X X' - n G (1[σ=σ'] - G')) - ∑_σ c_{σσ} u_σ² X_σ` (the
diagonal cancellation of (2.58)). -/
theorem hasDerivAt_integral_cavityRatio_theta (hu : ContDiff ℝ 2 u) {B D D₁ D₂ : ℝ}
    (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {w : PerceptronSpin N → ℝ} (hw : ∀ a, 0 < w a) (f : (R → PerceptronSpin N) → ℝ)
    (a₀ t p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (ha₀ : a₀ ^ 2 = (1 - p) / (N + 1))
    (F : (ℝ × ℝ) × (PerceptronSpin N → ℝ) → ℝ)
    (hF : ∀ x, F x = (∑ σ : R → PerceptronSpin N, f σ * ∏ r, (w (σ r) *
        ∫ η, Real.exp (u (x.2 (σ r) + η.1 * x.1.1 + η.2 * x.1.2))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))) /
      (∑ a, w a * ∫ η, Real.exp (u (x.2 a + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ^ Fintype.card R)
    (ψ ψ₁ ψ₂ : ℝ → ℝ)
    (hψ : ∀ x, ψ x = ∫ η, Real.exp (u (x + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hψ₁ : ∀ x, ψ₁ x = ∫ η, deriv (fun x => Real.exp (u x)) (x + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hψ₂ : ∀ x, ψ₂ x = ∫ η, deriv (deriv fun x => Real.exp (u x)) (x + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (Y : ((Fin N ⊕ Unit) ⊕ Unit → ℝ) → PerceptronSpin N → ℝ)
    (hY : ∀ ξ l, Y ξ l = Real.cos t * ((Sum.elim (cavityCoef N p l) (fun _ : Unit => (0 : ℝ)) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin t * ((Sum.elim
        (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) :
    HasDerivAt (fun s => ∫ ξ, F ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
        fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1))
      (Real.sin t * Real.cos t * ∫ ξ, (∑ l, ∑ k, (q - cavityCoef N p l ⬝ᵥ cavityCoef N p k) *
          (ψ₁ (Y ξ l) / ψ (Y ξ l)) * (ψ₁ (Y ξ k) / ψ (Y ξ k)) *
          ∫ σ, (((∑ r, if σ r = l then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) *
            ((∑ r, if σ r = k then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k}) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l} *
            ((if l = k then 1 else 0) - (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k})) * f σ
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))) -
        ∑ l, (q - cavityCoef N p l ⬝ᵥ cavityCoef N p l) * (ψ₁ (Y ξ l) / ψ (Y ξ l)) ^ 2 *
          ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) * f σ
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) t := by
  have hFfun : F = fun x : (ℝ × ℝ) × (PerceptronSpin N → ℝ) =>
      (∑ σ : R → PerceptronSpin N, f σ * ∏ r, (w (σ r) *
        ∫ η, Real.exp (u (x.2 (σ r) + η.1 * x.1.1 + η.2 * x.1.2))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))) /
      (∑ a, w a * ∫ η, Real.exp (u (x.2 a + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ^ Fintype.card R := funext hF
  have hFb : BoundedC2 F := by
    rw [hFfun]
    exact boundedC2_cavityRatio (R := R) hu hB hD hD₁ hD₂ hw f
  have ha : ∀ s, HasDerivAt (fun s => Real.cos s * a₀) (-(Real.sin s * a₀)) s := fun s => by
    simpa using (Real.hasDerivAt_cos s).mul_const a₀
  have hb : ∀ s, HasDerivAt (fun s => Real.sin s * Real.sqrt (1 - q))
      (Real.cos s * Real.sqrt (1 - q)) s := fun s => by
    simpa using (Real.hasDerivAt_sin s).mul_const (Real.sqrt (1 - q))
  have hτ : ∀ s, HasDerivAt (fun s : ℝ => (Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)))
      (-(Real.sin s * a₀), Real.cos s * Real.sqrt (1 - q)) s := fun s => (ha s).prodMk (hb s)
  have hA : ∀ s, ‖((-(Real.sin s * a₀), Real.cos s * Real.sqrt (1 - q)) : ℝ × ℝ)‖ ≤ |a₀| + 1 :=
    fun s => by
      rw [Prod.norm_def, max_le_iff]
      refine ⟨?_, ?_⟩
      · rw [Real.norm_eq_abs, abs_neg, abs_mul]
        nlinarith [Real.abs_sin_le_one s, abs_nonneg a₀, abs_nonneg (Real.sin s)]
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        have h1 : Real.sqrt (1 - q) ≤ 1 := by
          rw [Real.sqrt_le_one]; linarith [hq.1]
        nlinarith [Real.abs_cos_le_one s, abs_nonneg a₀, Real.sqrt_nonneg (1 - q),
          abs_nonneg (Real.cos s)]
  have key := hasDerivAt_integral_comp_trig_boundedC2_cavity (N := N) hFb p hq.1 hτ hA t
  refine key.congr_deriv ?_
  -- the smoothing `ψ` as a function of `y` and its first two derivatives
  have hpos : ∀ x, 0 < ψ x := fun x => by
    rw [hψ]
    exact (Real.exp_pos _).trans_le (exp_neg_le_integral_exp_comp_gaussian hu.continuous hB hD
      x _ _)
  have hy := hasDerivAt_integral_exp_comp_gaussian_y hu hD hD₁ hD₂
    (Real.cos t * a₀) (Real.sin t * Real.sqrt (1 - q))
  have hψ' : ∀ x, HasDerivAt ψ (ψ₁ x) x := fun x => by
    have h := (hy x).1
    have e1 : ψ = fun y => ∫ η, Real.exp (u (y + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      funext hψ
    rw [e1, hψ₁]
    exact h
  have hψ₁' : ∀ x, HasDerivAt ψ₁ (ψ₂ x) x := fun x => by
    have h := (hy x).2
    have e1 : ψ₁ = fun y => ∫ η, deriv (fun x => Real.exp (u x)) (y + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      funext hψ₁
    rw [e1, hψ₂]
    exact h
  have hL' : ∀ x, HasDerivAt (fun x => ψ₁ x / ψ x) (ψ₂ x / ψ x - (ψ₁ x / ψ x) ^ 2) x :=
    fun x => ((hψ₁' x).div (hψ' x) (hpos x).ne').congr_deriv (by field_simp)
  have hψc : ContDiff ℝ 2 ψ := by
    have e1 : ψ = fun y : ℝ => ∫ η, Real.exp (u (y + η.1 * (Real.cos t * a₀) +
        η.2 * (Real.sin t * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      funext hψ
    rw [e1]
    exact contDiff_two_integral_exp_comp_gaussian_section hu hD hD₁ hD₂ _ _
  have hFG : (fun y : PerceptronSpin N → ℝ => F ((Real.cos t * a₀,
      Real.sin t * Real.sqrt (1 - q)), y)) = fun y =>
      (∑ σ : R → PerceptronSpin N, f σ * ∏ r, (w (σ r) * ψ (y (σ r)))) /
        (∑ a, w a * ψ (y a)) ^ Fintype.card R :=
    funext fun y => by rw [hF]; simp only [← hψ]
  have hH : ∀ ξ (l k : PerceptronSpin N),
      fderiv ℝ (fun y => fderiv ℝ (fun y => F ((Real.cos t * a₀,
        Real.sin t * Real.sqrt (1 - q)), y)) y (Pi.single l 1)) (Y ξ) (Pi.single k 1) =
      (if l = k then ψ₂ (Y ξ l) / ψ (Y ξ l) - (ψ₁ (Y ξ l) / ψ (Y ξ l)) ^ 2 else 0) *
        ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))) +
        ψ₁ (Y ξ l) / ψ (Y ξ l) * (ψ₁ (Y ξ k) / ψ (Y ξ k)) *
        ∫ σ, (((∑ r, if σ r = l then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) *
            ((∑ r, if σ r = k then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k}) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l} *
            ((if l = k then 1 else 0) - (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k})) * f σ
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))) := fun ξ l k => by
    rw [hFG]
    exact fderiv_fderiv_replicaRatio_single (ψ'' := fun x => ψ₂ x / ψ x - (ψ₁ x / ψ x) ^ 2)
      hw hpos hψc hψ' hL' f (Y ξ) k l
  have hT : ∀ ξ, fderiv ℝ F ((Real.cos t * a₀, Real.sin t * Real.sqrt (1 - q)), Y ξ)
      ((-(Real.sin t * a₀), Real.cos t * Real.sqrt (1 - q)), 0) =
      ∑ l, (Real.sin t * Real.cos t * (1 - q - a₀ ^ 2) * ψ₂ (Y ξ l)) / ψ (Y ξ l) *
        ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))) := fun ξ => by
    rw [hFfun]
    have := fderiv_cavityRatio_time (R := R) hu hB hD hD₁ hD₂ hq.2 hw f a₀ t (Y ξ)
    simpa only [← hψ, ← hψ₂] using this
  have hYfun : ∀ ξ, (fun m : PerceptronSpin N => Real.cos t * ((Sum.elim (cavityCoef N p m)
      (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin t * ((Sum.elim
      (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
      (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) = Y ξ := fun ξ => (funext (hY ξ)).symm
  have hYc : Continuous Y := by
    have : Y = fun ξ l => Real.cos t * ((Sum.elim (cavityCoef N p l) (fun _ : Unit => (0 : ℝ)) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin t * ((Sum.elim
        (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) := funext fun ξ => funext (hY ξ)
    rw [this]
    refine continuous_pi fun l => ?_
    simp only [dotProduct]
    fun_prop
  simp only [hYfun]
  have hint1 : ∀ σ σ' : PerceptronSpin N, Integrable (fun ξ => fderiv ℝ
      (fun y => fderiv ℝ (fun y => F ((Real.cos t * a₀, Real.sin t * Real.sqrt (1 - q)), y)) y
        (Pi.single σ 1)) (Y ξ) (Pi.single σ' 1))
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := fun σ σ' =>
    integrable_fderiv_fderiv_section hFb _ σ' σ hYc
  have hint2 : Integrable (fun ξ => fderiv ℝ F ((Real.cos t * a₀, Real.sin t * Real.sqrt (1 - q)),
      Y ξ) ((-(Real.sin t * a₀), Real.cos t * Real.sqrt (1 - q)), 0))
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) :=
    integrable_fderiv_param hFb _ _ hYc
  have hlin : ∑ σ, ∑ σ', (q - cavityCoef N p σ ⬝ᵥ cavityCoef N p σ') *
      ∫ ξ, fderiv ℝ (fun y => fderiv ℝ (fun y => F ((Real.cos t * a₀,
        Real.sin t * Real.sqrt (1 - q)), y)) y (Pi.single σ 1)) (Y ξ) (Pi.single σ' 1)
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) =
      ∫ ξ, ∑ σ, ∑ σ', (q - cavityCoef N p σ ⬝ᵥ cavityCoef N p σ') *
        fderiv ℝ (fun y => fderiv ℝ (fun y => F ((Real.cos t * a₀,
        Real.sin t * Real.sqrt (1 - q)), y)) y (Pi.single σ 1)) (Y ξ) (Pi.single σ' 1)
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := by
    rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun σ' _ =>
      (hint1 σ σ').const_mul _]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_finsetSum _ fun σ' _ => (hint1 σ σ').const_mul _]
    exact Finset.sum_congr rfl fun σ' _ => (integral_const_mul _ _).symm
  rw [hlin, ← integral_const_mul, ← integral_add
    ((integrable_finsetSum _ fun σ _ => integrable_finsetSum _ fun σ' _ =>
      (hint1 σ σ').const_mul _).const_mul _) hint2, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  beta_reduce
  rw [hT ξ]
  simp only [hH ξ]
  have hc : ∀ l : PerceptronSpin N, (q - cavityCoef N p l ⬝ᵥ cavityCoef N p l) =
      -(1 - q - a₀ ^ 2) := fun l => by
    have h := cavityCoef_dotProduct_self_add (N := N) hp l
    rw [Real.sq_sqrt (div_nonneg (sub_nonneg.2 hp.2) (by positivity)), ← ha₀] at h
    linarith
  have hid := integral_sum_hessian_add_tau_term
    (Measure.pi fun _ : R => Measure.count.tilted
      (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
    (fun l k => q - cavityCoef N p l ⬝ᵥ cavityCoef N p k) (1 - q - a₀ ^ 2)
    (fun l => hc l) (fun l => ψ₁ (Y ξ l) / ψ (Y ξ l))
    (fun l => ψ₂ (Y ξ l) / ψ (Y ξ l) - (ψ₁ (Y ξ l) / ψ (Y ξ l)) ^ 2)
    (fun l => (Measure.count.tilted (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) f
  have h2 := congrArg (fun z => Real.sin t * Real.cos t * z) hid
  convert h2 using 1
  · rw [mul_add]
    refine congrArg₂ _ rfl ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [mul_sub, mul_sub]
    refine congrArg₂ _ (congrArg _ (Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun k _ => by ring))
      (congrArg _ (Finset.sum_congr rfl fun l _ => by ring))


end Combined

/-- The cavity smoothing is measurable in the spin variable. -/
theorem measurable_integral_exp_comp_gaussian (hu : ContDiff ℝ 2 u) {D D₁ D₂ : ℝ}
    (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (a b : ℝ) :
    Measurable fun y : ℝ => ∫ η, Real.exp (u (y + η.1 * a + η.2 * b))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  (contDiff_two_integral_exp_comp_gaussian_section hu hD hD₁ hD₂ a b).continuous.measurable

/-- **The spin field of the extended system is measurable in the Gaussian block.** -/
theorem measurable_cavityField (N : ℕ) (p q s : ℝ) (l : PerceptronSpin N) :
    Measurable fun ξ : (Fin N ⊕ Unit) ⊕ Unit → ℝ => Real.cos s * ((Sum.elim (cavityCoef N p l)
      (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
      (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
      (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) := by
  refine Continuous.measurable ?_
  simp only [dotProduct]
  fun_prop

end SpinGlasses
