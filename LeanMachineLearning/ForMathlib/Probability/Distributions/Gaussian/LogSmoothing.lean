/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.LogConcaveMarginal
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPPotential
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.MillsRatio

/-!
# The Gaussian log-Laplace smoothing of a potential

For a potential `u ≤ 0` with bounded first two derivatives, `x ↦ log 𝔼 exp u (x + c ξ)`, where `ξ`
is a standard Gaussian, is twice differentiable; its derivative is nonnegative when `u` is
nondecreasing, and its second derivative is nonpositive when `u` is concave (Talagrand,
*Spin Glasses*, Vol. I, Lemma 3.3.10 and Lemma 3.2.3).

## Main declarations

* `ProbabilityTheory.hasDerivAt_integral_mul_exp_comp_add_gaussianReal`: differentiation of
  `x ↦ ∫ f (x + c ξ) exp (u (x + c ξ))`.
* `ProbabilityTheory.exists_sq_integral_id_mul_exp_comp_div_le`: Lemma 3.3.8 for the
  smoothing, without derivatives of `u`.
* `ProbabilityTheory.hasDerivAt_log_integral_exp_comp_add_gaussianReal`: the first two
  derivatives of the smoothing.
* `ProbabilityTheory.integral_deriv_two_add_sq_mul_exp_div_le_sq`,
  `ProbabilityTheory.integral_deriv_two_add_sq_div_le_integral_sq_div`: the pointwise and
  averaged inequalities behind `r̄ ≤ r` (Lemma 3.2.3).
* `ProbabilityTheory.integrable_exp_comp_add_gaussianReal`,
  `ProbabilityTheory.integrable_mul_exp_comp_add_gaussianReal_of_abs_deriv_le`: integrability
  for `u ≤ 0`, or for `u` with bounded derivative.
* `ProbabilityTheory.measurable_integral_mul_exp_comp_add_gaussianReal`,
  `ProbabilityTheory.abs_integral_mul_exp_comp_add_div_le`: measurability and bounds for the
  ratios `A / Z`, `K / Z`.
* `ProbabilityTheory.exists_sq_mul_integral_deriv_mul_exp_div_le`: Lemma 3.3.8 for the smoothing,
  `(c A / Z)² ≤ (max ((τ - y) / c) 0)² + L`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

variable {u : ℝ → ℝ}

/-- For `u ≤ 0` and bounded `f`, `ξ ↦ f (y + c ξ) e^{u (y + c ξ)}` is integrable. -/
theorem integrable_mul_exp_comp_add_gaussianReal (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (y c : ℝ) :
    Integrable (fun ξ => f (y + c * ξ) * Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
  have haff : Measurable fun ξ : ℝ => y + c * ξ := by fun_prop
  refine Integrable.of_bound ((hf.comp haff).mul (hu.comp haff).exp).aestronglyMeasurable B
    (ae_of_all _ fun ξ => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))).trans (hB _)

/-- For `u ≤ 0`, the weight `ξ ↦ e^{u (y + c ξ)}` is integrable. -/
theorem integrable_exp_comp_add_gaussianReal (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (y c : ℝ) :
    Integrable (fun ξ => Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
  simpa only [one_mul] using integrable_mul_exp_comp_add_gaussianReal hu hu0
    (f := fun _ => 1) measurable_const (B := 1) (fun _ => by simp) y c

/-- For `u ≤ 0`, the normalisation `𝔼 e^{u (y + c ξ)}` is positive. -/
theorem integral_exp_comp_add_gaussianReal_pos (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (y c : ℝ) : 0 < ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) :=
  integral_exp_pos (integrable_exp_comp_add_gaussianReal hu hu0 y c)

/-- For `u` with bounded derivative, `g ξ e^{u (y + c ξ)}` is integrable when `g` grows at most
like a power of `|ξ|`. No upper bound on `u` is needed. -/
theorem integrable_mul_exp_comp_add_gaussianReal_of_abs_deriv_le (hu : Differentiable ℝ u)
    {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} {k : ℕ}
    (hgb : ∀ ξ, |g ξ| ≤ C * |ξ| ^ k) (y c : ℝ) :
    Integrable (fun ξ => g ξ * Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hC : 0 ≤ C * 1 := by
    simpa using (abs_nonneg _).trans (hgb 1)
  rw [mul_one] at hC
  have haff : Measurable fun ξ : ℝ => y + c * ξ := by fun_prop
  have hum : Measurable u := hu.continuous.measurable
  refine ((integrable_exp_mul_abs_gaussianReal (m := 0) (v := 1) (k + D * |c|)).const_mul
    (C * Real.exp (u y))).mono' (hg.mul (hum.comp haff).exp).aestronglyMeasurable
    (ae_of_all _ fun ξ => ?_)
  have hlip : u (y + c * ξ) ≤ u y + D * |c| * |ξ| := by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hu x)
      (fun x _ => by simpa only [Real.norm_eq_abs] using hD x) (mem_univ y)
      (mem_univ (y + c * ξ))
    rw [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, ← mul_assoc] at h
    linarith [le_abs_self (u (y + c * ξ) - u y)]
  have hpow : |ξ| ^ k ≤ Real.exp (k * |ξ|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [Real.add_one_le_exp |ξ|]) k
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine (mul_le_mul ((hgb ξ).trans (mul_le_mul_of_nonneg_left hpow hC))
    (Real.exp_le_exp.2 hlip) (Real.exp_pos _).le (by positivity)).trans_eq ?_
  rw [add_mul, Real.exp_add, Real.exp_add]
  ring

/-- The ratio `𝔼 [f e^{u}] / 𝔼 e^{u}` at `y + c ξ` is bounded by any bound of `|f|`, as soon as
the weight is integrable. -/
theorem abs_integral_mul_exp_comp_add_div_le {f : ℝ → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    {y c : ℝ} (hexpi : Integrable (fun ξ => Real.exp (u (y + c * ξ))) (gaussianReal 0 1)) :
    |(∫ ξ, f (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
      ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)| ≤ B := by
  rw [← integral_tilted_eq_div (fun ξ => u (y + c * ξ)) fun ξ => f (y + c * ξ)]
  exact abs_integral_tilted_le hexpi fun _ => hB _

/-- Measurability in `ω` of `∫ f (a ω + c ξ) e^{u (a ω + c ξ)}`. -/
theorem measurable_integral_mul_exp_comp_add_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    (hu : Measurable u) {f : ℝ → ℝ} (hf : Measurable f) {a : Ω → ℝ} (ha : Measurable a)
    (c : ℝ) : Measurable fun ω =>
      ∫ ξ, f (a ω + c * ξ) * Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1) := by
  have hshift : Measurable fun p : Ω × ℝ => a p.1 + c * p.2 :=
    (ha.comp measurable_fst).add (measurable_snd.const_mul c)
  exact (((hf.comp hshift).mul (hu.comp hshift).exp).stronglyMeasurable.integral_prod_right'
    (ν := gaussianReal 0 1)).measurable

/-- Measurability in `ω` of the ratio `𝔼 [f e^{u}] / 𝔼 e^{u}` at `a ω + c ξ`. With
`abs_integral_mul_exp_comp_add_div_le` this gives a bounded measurable function of `ω`. -/
theorem measurable_integral_mul_exp_comp_add_div {Ω : Type*} [MeasurableSpace Ω]
    (hu : Measurable u) {f : ℝ → ℝ} (hf : Measurable f) {a : Ω → ℝ} (ha : Measurable a)
    (c : ℝ) : Measurable fun ω =>
      (∫ ξ, f (a ω + c * ξ) * Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1) := by
  refine (measurable_integral_mul_exp_comp_add_gaussianReal hu hf ha c).div ?_
  simpa only [one_mul] using
    measurable_integral_mul_exp_comp_add_gaussianReal hu (f := fun _ => 1) measurable_const ha c

/-- Bounds `|u'| ≤ D` and `|u''| ≤ D₂` bound `u'' + u'²`. -/
theorem abs_deriv_deriv_add_sq_deriv_le {D D₂ : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) (x : ℝ) :
    |deriv (deriv u) x + deriv u x ^ 2| ≤ D₂ + D ^ 2 := by
  refine (abs_add_le _ _).trans (add_le_add (hD₂ _) ?_)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hD _) 2

/-- Differentiation under the Gaussian integral: if `u ≤ 0` and `f` are differentiable with
`|u'| ≤ D`, `|f| ≤ B`, `|f'| ≤ B'`, then
`d/dx ∫ f (x + c ξ) e^{u (x + c ξ)} = ∫ (f' + f u') (x + c ξ) e^{u (x + c ξ)}`. -/
theorem hasDerivAt_integral_mul_exp_comp_add_gaussianReal (hu : Differentiable ℝ u)
    (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D) {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) {B B' : ℝ} (hB : ∀ x, |f x| ≤ B) (hB' : ∀ x, |deriv f x| ≤ B')
    (c x : ℝ) :
    HasDerivAt (fun x => ∫ ξ, f (x + c * ξ) * Real.exp (u (x + c * ξ)) ∂(gaussianReal 0 1))
      (∫ ξ, (deriv f (x + c * ξ) + f (x + c * ξ) * deriv u (x + c * ξ)) *
        Real.exp (u (x + c * ξ)) ∂(gaussianReal 0 1)) x := by
  have hum : Measurable u := hu.continuous.measurable
  have hfm : Measurable f := hf.continuous.measurable
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have haff : ∀ y : ℝ, Measurable fun ξ : ℝ => y + c * ξ := fun y => by fun_prop
  have hexp : ∀ y, Real.exp (u y) ≤ 1 := fun y => Real.exp_le_one_iff.2 (hu0 y)
  have hmeas : ∀ y, AEStronglyMeasurable (fun ξ => f (y + c * ξ) * Real.exp (u (y + c * ξ)))
      (gaussianReal 0 1) := fun y =>
    ((hfm.comp (haff y)).mul (hum.comp (haff y)).exp).aestronglyMeasurable
  have hint : Integrable (fun ξ => f (x + c * ξ) * Real.exp (u (x + c * ξ)))
      (gaussianReal 0 1) :=
    Integrable.of_bound (hmeas x) B (ae_of_all _ fun ξ => by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hexp _)).trans (hB _))
  have hd : ∀ y ξ : ℝ, HasDerivAt (fun y => f (y + c * ξ) * Real.exp (u (y + c * ξ)))
      ((deriv f (y + c * ξ) + f (y + c * ξ) * deriv u (y + c * ξ)) *
        Real.exp (u (y + c * ξ))) y := fun y ξ => by
    have h1 := (hf (y + c * ξ)).hasDerivAt.comp_add_const y (c * ξ)
    have h2 := ((hu (y + c * ξ)).hasDerivAt.comp_add_const y (c * ξ)).exp
    refine (h1.mul h2).congr_deriv ?_
    ring
  have hdm : AEStronglyMeasurable (fun ξ => (deriv f (x + c * ξ) +
      f (x + c * ξ) * deriv u (x + c * ξ)) * Real.exp (u (x + c * ξ))) (gaussianReal 0 1) :=
    ((((measurable_deriv f).comp (haff x)).add ((hfm.comp (haff x)).mul
      ((measurable_deriv u).comp (haff x)))).mul
        (hum.comp (haff x)).exp).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun y ξ => f (y + c * ξ) * Real.exp (u (y + c * ξ)))
    (bound := fun _ => B' + B * D) Filter.univ_mem (Filter.Eventually.of_forall hmeas) hint hdm
    (ae_of_all _ fun ξ y _ => ?_) (integrable_const _) (ae_of_all _ fun ξ y _ => hd y ξ)).2
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  refine (mul_le_of_le_one_right (abs_nonneg _) (hexp _)).trans ((abs_add_le _ _).trans
    (add_le_add (hB' _) ?_))
  rw [abs_mul]
  exact mul_le_mul (hB _) (hD _) (abs_nonneg _) hB0

/-- **Talagrand, Lemma 3.3.10:** the first two derivatives of `v x = log 𝔼 e^{u (x + c ξ)}` are
`v' = A / Z` and `v'' = K / Z - (A / Z)²`, where `Z = 𝔼 e^{u}`, `A = 𝔼 u' e^{u}` and
`K = 𝔼 (u'' + u'²) e^{u}`. -/
theorem hasDerivAt_log_integral_exp_comp_add_gaussianReal (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (hu0 : ∀ x, u x ≤ 0) {D D₂ : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) (c x : ℝ) :
    let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
    let A : ℝ → ℝ := fun y =>
      ∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
    let K : ℝ → ℝ := fun y => ∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
      Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
    0 < Z x ∧ HasDerivAt (fun y => Real.log (Z y)) (A x / Z x) x ∧
      HasDerivAt (fun y => A y / Z y) (K x / Z x - (A x / Z x) ^ 2) x := by
  intro Z A K
  have hum : Measurable u := hu.continuous.measurable
  have hZ0 : ∀ y, 0 < Z y := fun y => integral_exp_comp_add_gaussianReal_pos hum hu0 y c
  have hZd : HasDerivAt Z (A x) x := by
    have h := hasDerivAt_integral_mul_exp_comp_add_gaussianReal hu hu0 hD
      (f := fun _ => 1) (differentiable_const 1) (B := 1) (B' := 0) (fun _ => by simp)
      (fun _ => by simp) c x
    simp only [one_mul, deriv_const', zero_add] at h
    exact h
  have hAd : HasDerivAt A (K x) x := by
    have h := hasDerivAt_integral_mul_exp_comp_add_gaussianReal hu hu0 hD
      (f := deriv u) hu' hD hD₂ c x
    simp only [← sq] at h
    exact h
  refine ⟨hZ0 x, hZd.log (hZ0 x).ne', ?_⟩
  refine (hAd.div hZd (hZ0 x).ne').congr_deriv ?_
  have := (hZ0 x).ne'
  field_simp

/-- **The pointwise form of `r̄ ≤ r`** (Talagrand, Lemma 3.2.3): for concave `u` with
bounded first two derivatives and all `a, c`,
`𝔼[(u'' + u'²)(θ) e^{u θ}] / 𝔼 e^{u θ} ≤ (𝔼[u' θ e^{u θ}] / 𝔼 e^{u θ})²`, where `θ = a + c ξ` and
`ξ` is a standard Gaussian. The case `c = 0` is included, and no upper bound on `u` is
needed. -/
theorem integral_deriv_two_add_sq_mul_exp_div_le_sq {u : ℝ → ℝ} (hu : ConcaveOn ℝ univ u)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u)) {D D₂ : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) (a c : ℝ) :
    (∫ ξ, (deriv (deriv u) (a + c * ξ) + deriv u (a + c * ξ) ^ 2) *
          Real.exp (u (a + c * ξ)) ∂(gaussianReal 0 1)) /
        (∫ ξ, Real.exp (u (a + c * ξ)) ∂(gaussianReal 0 1)) ≤
      ((∫ ξ, deriv u (a + c * ξ) * Real.exp (u (a + c * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (a + c * ξ)) ∂(gaussianReal 0 1)) ^ 2 := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h2 : deriv (deriv u) a ≤ 0 := by
      have hanti : Antitone (deriv u) := fun x y hxy =>
        hu.antitoneOn_deriv (fun z _ => hu1 z) (mem_univ x) (mem_univ y) hxy
      exact hanti.deriv_nonpos
    simp only [zero_mul, add_zero, integral_const, probReal_univ, one_smul]
    rw [mul_div_cancel_right₀ _ (Real.exp_pos _).ne',
      mul_div_cancel_right₀ _ (Real.exp_pos _).ne']
    linarith
  have haff : ∀ x : ℝ, HasDerivAt (fun x => a + c * x) c x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul c).const_add a
  set v : ℝ → ℝ := fun x => u (a + c * x) with hv
  have hvd : Differentiable ℝ v := fun x => ((hu1 _).hasDerivAt.comp x (haff x)).differentiableAt
  have hvc : ConcaveOn ℝ univ v := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    have h := hu.2 (mem_univ (a + c * x)) (mem_univ (a + c * y)) hs ht hst
    have e : a + c * (s • x + t • y) = s • (a + c * x) + t • (a + c * y) := by
      simp only [smul_eq_mul]
      linear_combination (-a) * hst
    simp only [hv, e]
    exact h
  have hum : Measurable u := hu1.continuous.measurable
  have hint : ∀ {g : ℝ → ℝ}, Measurable g → ∀ {C : ℝ} {k : ℕ}, (∀ ξ, |g ξ| ≤ C * |ξ| ^ k) →
      Integrable (fun x => g x * Real.exp (v x)) (gaussianReal 0 1) := fun hg _ _ hgb =>
    integrable_mul_exp_comp_add_gaussianReal_of_abs_deriv_le hu1 hD hg hgb a c
  have hu1m : Measurable fun x => deriv u (a + c * x) :=
    (measurable_deriv u).comp (by fun_prop)
  have h0 : Integrable (fun x => Real.exp (v x)) (gaussianReal 0 1) := by
    simpa only [one_mul] using hint (g := fun _ => 1) measurable_const (C := 1) (k := 0)
      (fun _ => by simp)
  have h1 : Integrable (fun x => x * Real.exp (v x)) (gaussianReal 0 1) :=
    hint measurable_id (C := 1) (k := 1) fun _ => by simp
  have h2 : Integrable (fun x => x ^ 2 * Real.exp (v x)) (gaussianReal 0 1) :=
    hint (measurable_id.pow_const 2) (C := 1) (k := 2) fun _ => by simp
  have hK1 : Integrable (fun x => deriv u (a + c * x) * Real.exp (v x)) (gaussianReal 0 1) :=
    hint hu1m (C := D) (k := 0) fun x => by simpa using hD (a + c * x)
  have hxK1 : Integrable (fun x => x * deriv u (a + c * x) * Real.exp (v x))
      (gaussianReal 0 1) :=
    hint (measurable_id.mul hu1m) (C := D) (k := 1) fun x => by
      rw [abs_mul, pow_one, mul_comm D]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  have hK2 : Integrable (fun x => (deriv (deriv u) (a + c * x) + deriv u (a + c * x) ^ 2) *
      Real.exp (v x)) (gaussianReal 0 1) :=
    hint (g := fun x => deriv (deriv u) (a + c * x) + deriv u (a + c * x) ^ 2)
      (((measurable_deriv (deriv u)).comp (by fun_prop : Measurable fun x : ℝ => a + c * x)).add
        (hu1m.pow_const 2)) (C := D₂ + D ^ 2) (k := 0) fun x => by
      simpa using abs_deriv_deriv_add_sq_deriv_le hD hD₂ (a + c * x)
  obtain ⟨x₀, -, -, hle⟩ := exists_integral_sub_sq_mul_exp_le_gaussianReal hvd hvc
  -- first integration by parts: `𝔼 [ξ e^v] = c 𝔼 [u' e^u]`
  have hIBP1 : ∫ x, x * Real.exp (v x) ∂(gaussianReal 0 1) =
      c * ∫ x, deriv u (a + c * x) * Real.exp (v x) ∂(gaussianReal 0 1) := by
    have hd : ∀ x, HasDerivAt (fun x => Real.exp (v x))
        (c * (deriv u (a + c * x) * Real.exp (v x))) x := fun x => by
      refine (((hu1 _).hasDerivAt.comp x (haff x)).exp).congr_deriv ?_
      simp only [hv, Function.comp_apply]
      ring
    rw [integral_id_mul_gaussianReal_eq 1 hd h1 (hK1.const_mul c), NNReal.coe_one, one_mul,
      integral_const_mul]
  -- second integration by parts: `𝔼 [ξ² e^v] = 𝔼 e^v + c² 𝔼 [(u'' + u'²) e^u]`
  have hIBP2 : ∫ x, x ^ 2 * Real.exp (v x) ∂(gaussianReal 0 1) =
      (∫ x, Real.exp (v x) ∂(gaussianReal 0 1)) +
        c ^ 2 * ∫ x, (deriv (deriv u) (a + c * x) + deriv u (a + c * x) ^ 2) * Real.exp (v x)
          ∂(gaussianReal 0 1) := by
    have hd : ∀ x, HasDerivAt (fun x => x * Real.exp (v x))
        (Real.exp (v x) + c * (x * deriv u (a + c * x) * Real.exp (v x))) x := fun x => by
      refine ((hasDerivAt_id x).mul (((hu1 _).hasDerivAt.comp x (haff x)).exp)).congr_deriv ?_
      simp only [hv, Function.comp_apply, id_eq]
      ring
    have hxx : Integrable (fun x => x * (x * Real.exp (v x))) (gaussianReal 0 1) :=
      h2.congr (ae_of_all _ fun x => by ring)
    have h := integral_id_mul_gaussianReal_eq 1 hd hxx (h0.add (hxK1.const_mul c))
    rw [NNReal.coe_one, one_mul, integral_add h0 (hxK1.const_mul c), integral_const_mul] at h
    have hmid : ∫ x, x * deriv u (a + c * x) * Real.exp (v x) ∂(gaussianReal 0 1) =
        c * ∫ x, (deriv (deriv u) (a + c * x) + deriv u (a + c * x) ^ 2) * Real.exp (v x)
          ∂(gaussianReal 0 1) := by
      have h' := integral_id_mul_deriv_u_mul_exp_affine_gaussianReal_of_integrable 1
        (u := u) (u' := deriv u) (u'' := deriv (deriv u)) (fun x => (hu1 x).hasDerivAt)
        (fun x => (hu2 x).hasDerivAt) a c (hxK1.congr (ae_of_all _ fun x => by
          simp only [hv]
          ring)) hK2
      rw [NNReal.coe_one, one_mul] at h'
      refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) h'
      simp only [hv]
      ring
    have e : ∫ x, x ^ 2 * Real.exp (v x) ∂(gaussianReal 0 1) =
        ∫ x, x * (x * Real.exp (v x)) ∂(gaussianReal 0 1) :=
      integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [e, h, hmid]
    ring
  set Z := ∫ x, Real.exp (v x) ∂(gaussianReal 0 1) with hZ
  set K1 := ∫ x, deriv u (a + c * x) * Real.exp (v x) ∂(gaussianReal 0 1) with hK1d
  set K2 := ∫ x, (deriv (deriv u) (a + c * x) + deriv u (a + c * x) ^ 2) * Real.exp (v x)
    ∂(gaussianReal 0 1) with hK2d
  have hZ0 : 0 < Z := integral_exp_pos h0
  have hexpand : ∫ x, (x - x₀) ^ 2 * Real.exp (v x) ∂(gaussianReal 0 1) =
      (Z + c ^ 2 * K2) - 2 * x₀ * (c * K1) + x₀ ^ 2 * Z := by
    have e : (fun x => (x - x₀) ^ 2 * Real.exp (v x)) = fun x =>
        x ^ 2 * Real.exp (v x) - 2 * x₀ * (x * Real.exp (v x)) + x₀ ^ 2 * Real.exp (v x) := by
      funext x; ring
    have hi : Integrable (fun x => x ^ 2 * Real.exp (v x) -
        2 * x₀ * (x * Real.exp (v x))) (gaussianReal 0 1) := h2.sub (h1.const_mul _)
    rw [e, integral_add hi (h0.const_mul _), integral_sub h2 (h1.const_mul _),
      integral_const_mul, integral_const_mul, hIBP2, hIBP1]
  have hkey : c ^ 2 * (K2 * Z - K1 ^ 2) ≤ 0 := by
    rw [hexpand] at hle
    nlinarith [sq_nonneg (x₀ * Z - c * K1), hZ0]
  have h3 : K2 * Z ≤ K1 ^ 2 := by
    have hc2 : 0 < c ^ 2 := by positivity
    have := nonpos_of_mul_nonpos_right hkey hc2
    linarith
  rw [div_pow, div_le_div_iff₀ hZ0 (pow_pos hZ0 2)]
  nlinarith [mul_le_mul_of_nonneg_right h3 hZ0.le]

/-- **The averaged form of `r̄ ≤ r`** (Talagrand, Lemma 3.2.3): for concave `u` with bounded
first two derivatives and any measurable shift `a` on a finite measure space,
`∫ K (a ω) / Z (a ω) ≤ ∫ (A (a ω) / Z (a ω))²`, in the notation of
`hasDerivAt_log_integral_exp_comp_add_gaussianReal`. Both integrands are integrable. -/
theorem integral_deriv_two_add_sq_div_le_integral_sq_div {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hu : ConcaveOn ℝ univ u)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u)) {D D₂ : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {a : Ω → ℝ}
    (ha : Measurable a) (c : ℝ) :
    ∫ ω, (∫ ξ, (deriv (deriv u) (a ω + c * ξ) + deriv u (a ω + c * ξ) ^ 2) *
          Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) /
        (∫ ξ, Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) ∂μ ≤
      ∫ ω, ((∫ ξ, deriv u (a ω + c * ξ) * Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) ^ 2 ∂μ := by
  have hum : Measurable u := hu1.continuous.measurable
  have hexpi : ∀ y, Integrable (fun ξ => Real.exp (u (y + c * ξ))) (gaussianReal 0 1) :=
      fun y => by
    simpa only [one_mul] using integrable_mul_exp_comp_add_gaussianReal_of_abs_deriv_le hu1 hD
      (g := fun _ => 1) measurable_const (C := 1) (k := 0) (fun _ => by simp) y c
  have hratio := fun (f : ℝ → ℝ) (B : ℝ) (hf : ∀ y, |f y| ≤ B) (y : ℝ) =>
    abs_integral_mul_exp_comp_add_div_le hf (hexpi y)
  refine integral_mono ?_ ?_ fun ω =>
    integral_deriv_two_add_sq_mul_exp_div_le_sq hu hu1 hu2 hD hD₂ (a ω) c
  · exact Integrable.of_bound (measurable_integral_mul_exp_comp_add_div hum
      (f := fun y => deriv (deriv u) y + deriv u y ^ 2) ((measurable_deriv (deriv u)).add
        ((measurable_deriv u).pow_const 2)) ha c).aestronglyMeasurable (D₂ + D ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact hratio (fun y => deriv (deriv u) y + deriv u y ^ 2) _
          (abs_deriv_deriv_add_sq_deriv_le hD hD₂) (a ω))
  · exact Integrable.of_bound ((measurable_integral_mul_exp_comp_add_div hum (measurable_deriv u)
      ha c).pow_const 2).aestronglyMeasurable (D ^ 2) (ae_of_all _ fun ω => by
        rw [norm_pow, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hratio (deriv u) D hD (a ω)) 2)

/-- **Talagrand, Lemma 3.3.8, Eq. (3.138):** there is a universal `L` with
`(𝔼 [ξ e^{u}] / 𝔼 e^{u})² ≤ (max ((τ - y) / c) 0)² + L` at `y + c ξ`, for every nondecreasing
`u ≤ 0` vanishing on `[τ, ∞)`. No derivative of `u` is involved; a concave `u` with these two
properties is nondecreasing (`ConcaveOn.monotone_of_forall_ge_eq`). -/
theorem exists_sq_integral_id_mul_exp_comp_div_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ → ℝ, Monotone u → (∀ x, u x ≤ 0) →
      ∀ τ : ℝ, (∀ x, τ ≤ x → u x = 0) → ∀ c : ℝ, 0 < c → ∀ y : ℝ,
        ((∫ ξ, ξ * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
            ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) ^ 2 ≤
          max ((τ - y) / c) 0 ^ 2 + L := by
  obtain ⟨L, hL0, hL⟩ := exists_sq_integral_id_mul_exp_div_le
  refine ⟨L, hL0, fun u hmono hu0 τ hτ c hc y => ?_⟩
  exact hL (fun ξ => u (y + c * ξ)) ((τ - y) / c)
    (fun x x' hx => hmono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hx hc.le)))
    (fun ξ => hu0 _) (fun ξ hξ => hτ _ (by rw [div_le_iff₀ hc] at hξ; linarith))

/-- **Lemma 3.3.8 for the smoothing:** there is a universal `L` with
`(c A y / Z y)² ≤ (max ((τ - y) / c) 0)² + L` for every nondecreasing `u ≤ 0` vanishing on
`[τ, ∞)`, where `Z = 𝔼 e^{u}` and `A = 𝔼 u' e^{u}` at `y + c ξ`. -/
theorem exists_sq_mul_integral_deriv_mul_exp_div_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ → ℝ, Differentiable ℝ u → Monotone u → (∀ x, u x ≤ 0) →
      ∀ τ : ℝ, (∀ x, τ ≤ x → u x = 0) → ∀ D : ℝ, (∀ x, |deriv u x| ≤ D) → ∀ c : ℝ, 0 < c →
      ∀ y : ℝ,
        (c * (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
            ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) ^ 2 ≤
          max ((τ - y) / c) 0 ^ 2 + L := by
  obtain ⟨L, hL0, hL⟩ := exists_sq_integral_id_mul_exp_comp_div_le
  refine ⟨L, hL0, fun u hu hmono hu0 τ hτ D hD c hc y => ?_⟩
  have hum : Measurable u := hu.continuous.measurable
  have h := hL u hmono hu0 τ hτ c hc y
  have hIBP : ∫ ξ, ξ * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) =
      c * ∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
    have hd : ∀ ξ, HasDerivAt (fun ξ => Real.exp (u (y + c * ξ)))
        (c * (deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)))) ξ := fun ξ => by
      have h1 : HasDerivAt (fun ξ => y + c * ξ) c ξ := by
        simpa using ((hasDerivAt_id ξ).const_mul c).const_add y
      refine (((hu _).hasDerivAt.comp ξ h1).exp).congr_deriv ?_
      simp only [Function.comp_apply]
      ring
    have hid : Integrable (fun ξ : ℝ => ξ) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 1).integrable le_rfl
    have hwi : Integrable (fun ξ => ξ * Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
      refine hid.abs.mono' (measurable_id.mul
        (hum.comp (by fun_prop : Measurable fun ξ : ℝ => y + c * ξ)).exp).aestronglyMeasurable
        (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))
    rw [integral_id_mul_gaussianReal_eq 1 hd hwi
      ((integrable_mul_exp_comp_add_gaussianReal hum hu0 (measurable_deriv u) hD y c).const_mul c),
      NNReal.coe_one, one_mul, integral_const_mul]
  rwa [hIBP] at h

/-- **Concavity and bounds of the Gaussian log-Laplace smoothing** (`u_v` in Eq. (3.99)): for
concave `u ≤ 0` with `u, u'` differentiable and `|u'| ≤ D`, `|u''| ≤ D₂`, and any scale `c`, the
function `y ↦ log 𝔼 e^{u (y + c ξ)}` is concave, nonpositive, has `|v'| ≤ D`, and satisfies
`-D (1 + |c| + |y|) + u 0 ≤ v y` (so `-D' (1 + |y|) ≤ v y` with `D' = |u 0| + D (1 + |c|)`). -/
theorem concaveOn_and_bounds_log_integral_exp_comp_add_gaussianReal {u : ℝ → ℝ}
    (huc : ConcaveOn ℝ univ u) (hu0 : ∀ x, u x ≤ 0) (hu1 : Differentiable ℝ u)
    (hu2 : Differentiable ℝ (deriv u)) {D D₂ : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) (c : ℝ) :
    let v : ℝ → ℝ := fun y => Real.log (∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1))
    ConcaveOn ℝ univ v ∧ (∀ y, v y ≤ 0) ∧ Differentiable ℝ v ∧ (∀ y, |deriv v y| ≤ D) ∧
      ∀ y, -(|u 0| + D * (1 + |c|)) * (1 + |y|) ≤ v y := by
  intro v
  have hum : Measurable u := hu1.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hd : ∀ y, HasDerivAt v
      ((∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) y := fun y =>
    (hasDerivAt_log_integral_exp_comp_add_gaussianReal hu1 hu2 hu0 hD hD₂ c y).2.1
  have hd2 : ∀ y, HasDerivAt (deriv v)
      ((∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
          Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
        (∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) -
        ((∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
          ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) ^ 2) y := fun y => by
    have h := (hasDerivAt_log_integral_exp_comp_add_gaussianReal hu1 hu2 hu0 hD hD₂ c y).2.2
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => (hd z).deriv)
  have hv_diff : Differentiable ℝ v := fun y => (hd y).differentiableAt
  have hv_conc : ConcaveOn ℝ univ v := by
    have hanti : AntitoneOn (deriv v) univ :=
      antitoneOn_of_deriv_nonpos convex_univ
        (fun y _ => (hd2 y).continuousAt.continuousWithinAt)
        (fun y _ => (hd2 y).differentiableAt.differentiableWithinAt) fun y _ => by
          rw [(hd2 y).deriv]
          linarith [integral_deriv_two_add_sq_mul_exp_div_le_sq huc hu1 hu2 hD hD₂ y c]
    exact (hanti.mono interior_subset).concaveOn_of_deriv convex_univ
        hv_diff.continuous.continuousOn
      hv_diff.differentiableOn
  have hv0 : ∀ y, v y ≤ 0 := fun y => by
    have hZ1 : ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) ≤ 1 :=
      (integral_mono (integrable_exp_comp_add_gaussianReal hum hu0 y c) (integrable_const 1)
        fun ξ => Real.exp_le_one_iff.2 (hu0 _)).trans_eq (by simp)
    exact Real.log_nonpos (integral_exp_comp_add_gaussianReal_pos hum hu0 y c).le hZ1
  have hvD : ∀ y, |deriv v y| ≤ D := fun y => by
    rw [(hd y).deriv]
    exact abs_integral_mul_exp_comp_add_div_le hD
      (integrable_exp_comp_add_gaussianReal hum hu0 y c)
  have hlow : ∀ y, -(|u 0| + D * (1 + |c|)) * (1 + |y|) ≤ v y := fun y => by
    have hlip : ∀ x, -(|u 0| + D * |x|) ≤ u x := fun x => by
      have h1 := Convex.norm_image_sub_le_of_norm_deriv_le (f := u) (s := univ)
        (fun z _ => hu1 z) (fun z _ => by simpa only [Real.norm_eq_abs] using hD z) convex_univ
        (mem_univ 0) (mem_univ x)
      rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h1
      linarith [(abs_le.1 h1).1, neg_abs_le (u 0)]
    have hξ1 : ∫ ξ, |ξ| ∂(gaussianReal 0 1) ≤ 1 := by
      have h1 := sq_norm_integral_le_integral_sq_norm (μ := gaussianReal 0 1)
        (f := fun ξ : ℝ => |ξ|) (memLp_id_gaussianReal (μ := 0) (v := 1) 2).abs
      have h2 : ∫ ξ : ℝ, ‖|ξ|‖ ^ 2 ∂(gaussianReal 0 1) = 1 := by
        simp only [Real.norm_eq_abs, abs_abs, sq_abs]
        simpa using integral_pow_add_two_gaussianReal 0
      rw [h2, Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h1
      nlinarith [integral_nonneg (μ := gaussianReal 0 1) fun ξ : ℝ => abs_nonneg ξ]
    have hexp_ge : Real.exp (-(|u 0| + D * |y| + D * |c|)) ≤
        ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
      have hid_i : Integrable (fun ξ : ℝ => |ξ|) (gaussianReal 0 1) :=
        integrable_abs_id_gaussianReal
      have hg_i : Integrable (fun ξ : ℝ => -(|u 0| + D * |y| + D * |c| * |ξ|))
          (gaussianReal 0 1) := ((integrable_const _).add (hid_i.const_mul _)).neg
      have hge_i : Integrable (fun ξ : ℝ => Real.exp (-(|u 0| + D * |y| + D * |c| * |ξ|)))
          (gaussianReal 0 1) := by
        refine (integrable_const (1 : ℝ)).mono'
          (by fun_prop : Measurable fun ξ : ℝ =>
            Real.exp (-(|u 0| + D * |y| + D * |c| * |ξ|))).aestronglyMeasurable
          (ae_of_all _ fun ξ => ?_)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
        positivity
      have hjensen := convexOn_exp.map_integral_le (μ := gaussianReal 0 1)
        Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => mem_univ _)
        hg_i hge_i
      have hint_ge : -(|u 0| + D * |y| + D * |c|) ≤
          ∫ ξ, -(|u 0| + D * |y| + D * |c| * |ξ|) ∂(gaussianReal 0 1) := by
        rw [integral_neg, integral_add (integrable_const _) (hid_i.const_mul _),
          integral_const, probReal_univ, one_smul, integral_const_mul]
        nlinarith [mul_nonneg hD0 (abs_nonneg c)]
      refine (Real.exp_le_exp.2 hint_ge).trans (hjensen.trans ?_)
      refine integral_mono hge_i (integrable_exp_comp_add_gaussianReal hum hu0 y c) fun ξ => ?_
      refine Real.exp_le_exp.2 (le_trans ?_ (hlip (y + c * ξ)))
      have : |y + c * ξ| ≤ |y| + |c| * |ξ| := (abs_add_le _ _).trans_eq (by rw [abs_mul])
      nlinarith [mul_le_mul_of_nonneg_left this hD0]
    have hlog := Real.log_le_log (Real.exp_pos _) hexp_ge
    rw [Real.log_exp] at hlog
    refine le_trans ?_ hlog
    nlinarith [abs_nonneg (u 0), abs_nonneg y, abs_nonneg c, mul_nonneg hD0 (abs_nonneg c),
      mul_nonneg (abs_nonneg (u 0)) (abs_nonneg y),
      mul_nonneg (mul_nonneg hD0 (abs_nonneg c)) (abs_nonneg y)]
  exact ⟨hv_conc, hv0, hv_diff, hvD, hlow⟩

end ProbabilityTheory
