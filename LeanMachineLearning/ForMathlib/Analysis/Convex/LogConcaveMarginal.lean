/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.Variance
public import LeanMachineLearning.ForMathlib.Analysis.Convex.PrekopaLeindler
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPPotential

/-!
# Marginals and variances of log-concave densities

## Main declarations

* `MeasureTheory.concaveOn_log_integral_exp`: the marginal of a log-concave function is
  log-concave (Talagrand, *Spin Glasses*, Vol. I, Lemma 3.2.5).
* `MeasureTheory.mul_integral_sub_sq_mul_exp_le`: if `c (x - x₀)² ≤ -w' x (x - x₀)`, then
  `c ∫ (x - x₀)² exp (w x) ≤ ∫ exp (w x)` (Lemma 3.2.2, Eq. (3.70)).
* `MeasureTheory.abs_integral_volume_tilted_concave_sub_mul_sq_le`: for the density
  proportional to `exp (f x - κ x² + d x)` with `f` concave, the mean is at most
  `(2 κ)^{-1/2} + |f' 0 + d| / (2 κ)` in absolute value (Eq. (3.86)).
* `MeasureTheory.hasDerivAt_log_integral_exp_sum_comp_add_mul`: differentiation of
  `x ↦ log ∫ exp (∑ k, u (a k ρ + c k x) + V ρ) dμ ρ`.
* `ProbabilityTheory.variance_id_tilted_gaussianReal_le_one`: a standard Gaussian tilted by a
  differentiable concave function has variance at most `1` (Lemma 3.2.3, Eqs. (3.71)--(3.73)).
* `ProbabilityTheory.integral_deriv_two_add_sq_mul_exp_div_le_sq`: Eq. (3.73) for the potential
  `ξ ↦ u (a + c ξ)` after Gaussian integration by parts, the pointwise form of `r̄ ≤ r`.
* `ProbabilityTheory.volume_tilted_mul_sub_mul_sq_eq_gaussianReal` and its moments: the density
  proportional to `exp (d x - a x² / 2)` is `𝒩(d / a, 1 / a)`, the computation behind
  Eqs. (3.78)--(3.80).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- **The marginal of a log-concave density is log-concave** (Talagrand, Lemma 3.2.5): if `F` is
concave on `E₁ × E₂` and `exp (F (·, y))` is integrable for every `y`, then
`y ↦ log (∫ exp (F (x, y)) dμ x)` is concave. Here `μ` is an additive Haar measure on a
finite-dimensional space and `E₂` is an arbitrary real vector space. -/
theorem concaveOn_log_integral_exp {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [T2Space E₁]
    [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁] [AddCommGroup E₂]
    [Module ℝ E₂] (μ : Measure E₁) [μ.IsAddHaarMeasure] {F : E₁ × E₂ → ℝ}
    (hF : ConcaveOn ℝ univ F) (hint : ∀ y, Integrable (fun x => Real.exp (F (x, y))) μ) :
    ConcaveOn ℝ univ fun y => Real.log (∫ x, Real.exp (F (x, y)) ∂μ) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha0
  · rw [zero_add] at hab
    simp [hab]
  rcases hb.eq_or_lt with rfl | hb0
  · rw [add_zero] at hab
    simp [hab]
  have hb1 : b = 1 - a := by linarith
  have ha1 : a < 1 := by linarith
  have : NeZero μ := ⟨Measure.measure_univ_ne_zero.1
    (isOpen_univ.measure_ne_zero μ univ_nonempty)⟩
  have hpos : ∀ y, 0 < ∫ x, Real.exp (F (x, y)) ∂μ := fun y => integral_exp_pos (hint y)
  have hlin : ∀ y, ∫⁻ x, ENNReal.ofReal (Real.exp (F (x, y))) ∂μ =
      ENNReal.ofReal (∫ x, Real.exp (F (x, y)) ∂μ) := fun y =>
    (ofReal_integral_eq_lintegral_ofReal (hint y) (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  have hae : ∀ y, AEMeasurable (fun x => ENNReal.ofReal (Real.exp (F (x, y)))) μ := fun y =>
    (hint y).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have key := lintegral_prekopa_leindler_addHaar μ ha0 ha1 (hae y₁) (hae y₂)
    (hae (a • y₁ + b • y₂)) fun x z => by
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _), ← Real.exp_mul,
        ← Real.exp_mul, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have h := hF.2 (mem_univ (x, y₁)) (mem_univ (z, y₂)) ha hb hab
      simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at h
      rw [← hb1]
      linarith
  rw [hlin, hlin, hlin, ← hb1, ENNReal.ofReal_rpow_of_pos (hpos _),
    ENNReal.ofReal_rpow_of_pos (hpos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hpos _).le _),
    ENNReal.ofReal_le_ofReal_iff (hpos _).le] at key
  have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (hpos _) _)
    (Real.rpow_pos_of_pos (hpos _) _)) key
  rwa [Real.log_mul (Real.rpow_pos_of_pos (hpos _) _).ne'
    (Real.rpow_pos_of_pos (hpos _) _).ne', Real.log_rpow (hpos _),
    Real.log_rpow (hpos _)] at h

/-- **Variance around the mode** (Talagrand, Lemma 3.2.2, Eq. (3.70)): if `w` has derivative
`w'` and `c (x - x₀)² ≤ -w' x (x - x₀)` for all `x`, with `c > 0`, then `exp (w x)` and
`(x - x₀)² exp (w x)` are integrable and `c ∫ (x - x₀)² exp (w x) ≤ ∫ exp (w x)`.
No regularity of `w'` is assumed. -/
theorem mul_integral_sub_sq_mul_exp_le {c x₀ : ℝ} (hc : 0 < c) {w w' : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (w' x) x) (h : ∀ x, c * (x - x₀) ^ 2 ≤ -w' x * (x - x₀)) :
    Integrable (fun x => Real.exp (w x)) ∧
      Integrable (fun x => (x - x₀) ^ 2 * Real.exp (w x)) ∧
        c * ∫ x, (x - x₀) ^ 2 * Real.exp (w x) ≤ ∫ x, Real.exp (w x) := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun x => (hw x).continuousAt
  -- Gaussian decay
  have hdecay : ∀ x, w x ≤ w x₀ - c / 2 * (x - x₀) ^ 2 := by
    set φ : ℝ → ℝ := fun x => w x + c / 2 * (x - x₀) ^ 2 with hφ
    have hφd : ∀ x, HasDerivAt φ (w' x + c * (x - x₀)) x := fun x => by
      have h1 : HasDerivAt (fun x => c / 2 * (x - x₀) ^ 2) (c * (x - x₀)) x := by
        have := (((hasDerivAt_id x).sub_const x₀).pow 2).const_mul (c / 2)
        refine this.congr_deriv ?_
        simp only [id_eq]
        ring
      exact (hw x).add h1
    have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφd x).continuousAt
    have hsign : ∀ x, (w' x + c * (x - x₀)) * (x - x₀) ≤ 0 := fun x => by
      have := h x
      nlinarith
    intro x
    suffices φ x ≤ φ x₀ by
      simp only [hφ, sub_self] at this
      linarith
    rcases le_total x₀ x with hx | hx
    · refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici x₀) hφc.continuousOn
        (fun y _ => (hφd y).hasDerivWithinAt) (fun y hy => ?_) self_mem_Ici hx hx
      rw [interior_Ici] at hy
      have hy' : 0 < y - x₀ := sub_pos.2 hy
      exact nonpos_of_mul_nonpos_left (hsign y) hy'
    · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic x₀) hφc.continuousOn
        (fun y _ => (hφd y).hasDerivWithinAt) (fun y hy => ?_) hx self_mem_Iic hx
      rw [interior_Iic] at hy
      have hy' : y - x₀ < 0 := sub_neg.2 hy
      have := hsign y
      nlinarith
  have hgauss : ∀ b : ℝ, 0 < b → Integrable fun x : ℝ => Real.exp (-b * (x - x₀) ^ 2) :=
    fun b hb => (integrable_exp_neg_mul_sq hb).comp_sub_right x₀
  have hexp : Integrable fun x => Real.exp (w x) := by
    refine Integrable.mono' ((hgauss (c / 2) (half_pos hc)).const_mul (Real.exp (w x₀)))
      (Real.continuous_exp.comp hwc).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add, Real.exp_le_exp]
    linarith [hdecay x]
  have hsq : Integrable fun x => (x - x₀) ^ 2 * Real.exp (w x) := by
    refine Integrable.mono' ((hgauss (c / 4) (by positivity)).const_mul
      (Real.exp (w x₀) * (4 / c)))
      (((continuous_id.sub continuous_const).pow 2).mul
        (Real.continuous_exp.comp hwc)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    have h1 : (x - x₀) ^ 2 ≤ 4 / c * Real.exp (c / 4 * (x - x₀) ^ 2) := by
      have := Real.add_one_le_exp (c / 4 * (x - x₀) ^ 2)
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
    have h2 : Real.exp (w x) ≤ Real.exp (w x₀) * Real.exp (-(c / 2) * (x - x₀) ^ 2) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      linarith [hdecay x]
    refine (mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)).trans_eq ?_
    rw [show Real.exp (-(c / 4) * (x - x₀) ^ 2) = Real.exp (c / 4 * (x - x₀) ^ 2) *
      Real.exp (-(c / 2) * (x - x₀) ^ 2) by rw [← Real.exp_add]; congr 1; ring]
    ring
  refine ⟨hexp, hsq, ?_⟩
  -- the primitive of the defect, minus the boundary term, is monotone
  set f : ℝ → ℝ := fun x => Real.exp (w x) - c * ((x - x₀) ^ 2 * Real.exp (w x)) with hf
  have hfc : Continuous f := by
    have := Real.continuous_exp.comp hwc
    exact this.sub ((((continuous_id.sub continuous_const).pow 2).mul this).const_mul c)
  have hfi : Integrable f := hexp.sub (hsq.const_mul c)
  set Φ : ℝ → ℝ := fun x => (∫ t in x₀..x, f t) - (x - x₀) * Real.exp (w x) with hΦ
  have hΦd : ∀ x, HasDerivAt Φ ((-w' x * (x - x₀) - c * (x - x₀) ^ 2) * Real.exp (w x)) x :=
    fun x => by
      have h1 := intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable x₀ x)
        (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt
      have h2 := ((hasDerivAt_id x).sub_const x₀).mul (hw x).exp
      refine (h1.sub h2).congr_deriv ?_
      simp only [hf, id_eq]
      ring
  have hΦm : Monotone Φ := monotone_of_hasDerivAt_nonneg hΦd fun x =>
    mul_nonneg (sub_nonneg.2 (h x)) (Real.exp_pos _).le
  have hΦ0 : Φ x₀ = 0 := by simp [hΦ]
  have hint : ∀ a b : ℝ, a ≤ x₀ → x₀ ≤ b → 0 ≤ ∫ t in a..b, f t := fun a b ha hb => by
    have h1 := hΦm hb
    have h2 := hΦm ha
    rw [hΦ0] at h1 h2
    simp only [hΦ] at h1 h2
    have h3 : 0 ≤ (b - x₀) * Real.exp (w b) := mul_nonneg (sub_nonneg.2 hb) (Real.exp_pos _).le
    have h4 : (a - x₀) * Real.exp (w a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ha) (Real.exp_pos _).le
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable a x₀)
      (hfc.intervalIntegrable x₀ b), intervalIntegral.integral_symm x₀ a]
    linarith
  have hlim : Tendsto (fun R : ℝ => ∫ t in (-R)..R, f t) atTop (𝓝 (∫ t, f t)) :=
    intervalIntegral_tendsto_integral hfi tendsto_neg_atTop_atBot tendsto_id
  have h0 : 0 ≤ ∫ t, f t := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (|x₀|)] with R hR
    exact hint _ _ (by linarith [neg_abs_le x₀]) ((le_abs_self x₀).trans hR)
  rw [hf, integral_sub hexp (hsq.const_mul c), integral_const_mul] at h0
  linarith

/-- **The mode of a concave potential minus a quadratic.** For `v` concave and differentiable
and `κ > 0`, the function `w x = v x - κ x² + d x` has a point `x₀` (its maximizer) with
`2 κ (x - x₀)² ≤ -w' x (x - x₀)` for every `x`, the input of `mul_integral_sub_sq_mul_exp_le`. -/
theorem exists_mode_concave_sub_mul_sq {v v' : ℝ → ℝ} (hv : ConcaveOn ℝ univ v)
    (hvd : ∀ x, HasDerivAt v (v' x) x) {κ : ℝ} (hκ : 0 < κ) (d : ℝ) :
    ∃ x₀ : ℝ, ∀ x, 2 * κ * (x - x₀) ^ 2 ≤ -(v' x - 2 * κ * x + d) * (x - x₀) := by
  set w : ℝ → ℝ := fun x => v x - κ * x ^ 2 + d * x with hw
  have hwd : ∀ x, HasDerivAt w (v' x - 2 * κ * x + d) x := fun x => by
    have h := ((hvd x).sub (((hasDerivAt_id x).pow 2).const_mul κ)).add
      ((hasDerivAt_id x).const_mul d)
    refine h.congr_deriv ?_
    simp only [id_eq]
    push_cast
    ring
  have hanti : Antitone v' := fun x y hxy => by
    have h := hv.antitoneOn_deriv (fun z _ => (hvd z).differentiableAt) (mem_univ x)
      (mem_univ y) hxy
    rwa [(hvd x).deriv, (hvd y).deriv] at h
  have htan : ∀ x, v x ≤ v 0 + v' 0 * x := fun x => by
    rcases lt_trichotomy x 0 with h | rfl | h
    · have := hv.le_slope_of_hasDerivAt (mem_univ x) (mem_univ 0) h (hvd 0)
      rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
      linarith
    · simp
    · have := hv.slope_le_of_hasDerivAt (mem_univ 0) (mem_univ x) h (hvd 0)
      rw [slope_def_field, sub_zero, div_le_iff₀ h] at this
      linarith
  have hfar : ∀ x, |v' 0 + d| / κ ≤ |x| → w x ≤ w 0 := fun x hx => by
    have h1 : |v' 0 + d| ≤ κ * |x| := by
      rw [div_le_iff₀ hκ] at hx
      linarith
    have h2 : (v' 0 + d) * x ≤ κ * x ^ 2 := by
      calc (v' 0 + d) * x ≤ |v' 0 + d| * |x| := (le_abs_self _).trans_eq (abs_mul _ _)
        _ ≤ κ * |x| * |x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = κ * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
    have h3 := htan x
    simp only [hw]
    linarith
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ y, w y ≤ w x₀ := by
    refine (continuous_iff_continuousAt.2 fun x => (hwd x).continuousAt).exists_forall_ge' 0 ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (|v' 0 + d| / κ)] with x hx
    exact hfar x (by rwa [Real.norm_eq_abs] at hx)
  have hmax : IsLocalMax w x₀ := Filter.Eventually.of_forall hx₀
  have hcrit : v' x₀ - 2 * κ * x₀ + d = 0 := hmax.hasDerivAt_eq_zero (hwd x₀)
  refine ⟨x₀, fun x => ?_⟩
  have h1 : (v' x - v' x₀) * (x - x₀) ≤ 0 := by
    rcases le_total x x₀ with h | h
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hanti h)) (sub_nonpos.2 h)
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hanti h)) (sub_nonneg.2 h)
  have e : -(v' x - 2 * κ * x + d) * (x - x₀) =
      2 * κ * (x - x₀) ^ 2 - (v' x - v' x₀) * (x - x₀) := by
    rw [show v' x₀ = 2 * κ * x₀ - d by linarith]
    ring
  linarith

/-- **The mean of a one-dimensional strongly log-concave density** (Talagrand, Eq. (3.86)): for
`f` concave and differentiable and `κ > 0`, the probability measure with density proportional to
`exp (f x - κ x² + d x)` has a finite mean, of absolute value at most
`√((2 κ)⁻¹) + |f' 0 + d| / (2 κ)`. -/
theorem abs_integral_volume_tilted_concave_sub_mul_sq_le {f f' : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    (hfd : ∀ x, HasDerivAt f (f' x) x) {κ : ℝ} (hκ : 0 < κ) (d : ℝ) :
    |∫ x, x ∂((volume : Measure ℝ).tilted fun x => f x - κ * x ^ 2 + d * x)| ≤
      Real.sqrt (2 * κ)⁻¹ + |f' 0 + d| / (2 * κ) := by
  set w : ℝ → ℝ := fun x => f x - κ * x ^ 2 + d * x with hw
  set w' : ℝ → ℝ := fun x => f' x - 2 * κ * x + d with hw'
  have hwd : ∀ x, HasDerivAt w (w' x) x := fun x => by
    have h := ((hfd x).sub (((hasDerivAt_id x).pow 2).const_mul κ)).add
      ((hasDerivAt_id x).const_mul d)
    refine h.congr_deriv ?_
    simp only [hw', id_eq]
    push_cast
    ring
  obtain ⟨x₀, hkey⟩ : ∃ x₀ : ℝ, ∀ x, 2 * κ * (x - x₀) ^ 2 ≤ -w' x * (x - x₀) :=
    exists_mode_concave_sub_mul_sq hf hfd hκ d
  have h2κ : 0 < 2 * κ := by linarith
  obtain ⟨hi, hi2, hvar⟩ := mul_integral_sub_sq_mul_exp_le h2κ hwd hkey
  have hprob : IsProbabilityMeasure ((volume : Measure ℝ).tilted w) :=
    isProbabilityMeasure_tilted hi
  set G := (volume : Measure ℝ).tilted w with hG
  have hsq : Integrable (fun x => (x - x₀) ^ 2) G := by
    rw [hG, integrable_tilted_iff hi]
    simpa only [smul_eq_mul, mul_comm] using hi2
  have hsqle : ∫ x, (x - x₀) ^ 2 ∂G ≤ (2 * κ)⁻¹ := by
    have hZ : 0 < ∫ x, Real.exp (w x) := integral_exp_pos hi
    have e : ∫ x, (x - x₀) ^ 2 ∂G =
        (∫ x, (x - x₀) ^ 2 * Real.exp (w x)) / ∫ x, Real.exp (w x) := by
      rw [hG, integral_tilted_eq_div]
    rw [e, div_le_iff₀ hZ, inv_mul_eq_div, le_div_iff₀' h2κ]
    exact hvar
  have hL2 : MemLp (fun x => x - x₀) 2 G :=
    (memLp_two_iff_integrable_sq (by fun_prop : Measurable fun x : ℝ => x - x₀
      ).aestronglyMeasurable).2 hsq
  have hid : Integrable (fun x : ℝ => x) G :=
    ((hL2.integrable one_le_two).add (integrable_const x₀)).congr
      (ae_of_all _ fun x => by simp)
  have hmean : |(∫ x, x ∂G) - x₀| ≤ Real.sqrt (2 * κ)⁻¹ := by
    refine Real.abs_le_sqrt (le_trans ?_ hsqle)
    have h1 := variance_nonneg (fun x => x - x₀) G
    rw [variance_eq_sub hL2] at h1
    simp only [Pi.pow_apply] at h1
    rw [integral_sub hid (integrable_const x₀), integral_const, probReal_univ, one_smul] at h1
    linarith
  have hx0 : |x₀| ≤ |f' 0 + d| / (2 * κ) := by
    have h1 := hkey 0
    have h2 : -w' 0 * (0 - x₀) = (f' 0 + d) * x₀ := by
      simp only [hw']
      ring
    have h3 : 2 * κ * |x₀| * |x₀| ≤ |f' 0 + d| * |x₀| := by
      rw [mul_assoc, ← sq, sq_abs, ← abs_mul]
      refine le_trans ?_ (le_abs_self _)
      rw [← h2]
      simpa using h1
    rcases (abs_nonneg x₀).eq_or_lt with h | h
    · rw [← h]
      positivity
    · rw [le_div_iff₀' h2κ]
      exact le_of_mul_le_mul_right h3 h
  calc |∫ x, x ∂G| = |((∫ x, x ∂G) - x₀) + x₀| := by rw [sub_add_cancel]
    _ ≤ |(∫ x, x ∂G) - x₀| + |x₀| := abs_add_le _ _
    _ ≤ _ := add_le_add hmean hx0

/-- Differentiation of the logarithm of a partition function: if `u ≤ 0` is differentiable with
`|u'| ≤ D` and `exp V` is integrable and nonzero, then
`d/dx log ∫ exp (∑ k, u (a k ρ + c k x) + V ρ) = ∑ k, c k ⟨u' (a k ρ + c k x)⟩_x`, where
`⟨·⟩_x` is the average for the normalized weight. -/
theorem hasDerivAt_log_integral_exp_sum_comp_add_mul {A ι : Type*} [MeasurableSpace A]
    [Fintype ι] {μ : Measure A} [NeZero μ] {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D) {a : ι → A → ℝ}
    (ha : ∀ k, Measurable (a k)) (c : ι → ℝ) {V : A → ℝ} (hV : Measurable V)
    (hVi : Integrable (fun ρ => Real.exp (V ρ)) μ) (x : ℝ) :
    HasDerivAt (fun x => Real.log (∫ ρ, Real.exp ((∑ k, u (a k ρ + c k * x)) + V ρ) ∂μ))
      (∑ k, c k * ∫ ρ, deriv u (a k ρ + c k * x)
        ∂(μ.tilted fun ρ => (∑ k, u (a k ρ + c k * x)) + V ρ)) x := by
  have hum : Measurable u := hu.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  set E : ℝ → A → ℝ := fun x ρ => (∑ k, u (a k ρ + c k * x)) + V ρ with hE
  set E' : ℝ → A → ℝ := fun x ρ => ∑ k, c k * deriv u (a k ρ + c k * x) with hE'
  have hEm : ∀ x, Measurable (E x) := fun x =>
    (Finset.measurable_sum _ fun k _ => hum.comp ((ha k).add_const _)).add hV
  have hE'm : ∀ x, Measurable (E' x) := fun x =>
    Finset.measurable_sum _ fun k _ =>
      ((measurable_deriv u).comp ((ha k).add_const _)).const_mul _
  have hle : ∀ x ρ, Real.exp (E x ρ) ≤ Real.exp (V ρ) := fun x ρ =>
    Real.exp_le_exp.2 (add_le_of_nonpos_left (Finset.sum_nonpos fun _ _ => hu0 _))
  have hEi : ∀ x, Integrable (fun ρ => Real.exp (E x ρ)) μ := fun x =>
    hVi.mono' (hEm x).exp.aestronglyMeasurable (ae_of_all _ fun ρ => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hle x ρ)
  have hbd : ∀ x ρ, |E' x ρ| ≤ ∑ k, |c k| * D := fun x ρ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _))
  have hder : HasDerivAt (fun x => ∫ ρ, Real.exp (E x ρ) ∂μ)
      (∫ ρ, Real.exp (E x ρ) * E' x ρ ∂μ) x := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun x ρ => Real.exp (E x ρ)) (F' := fun x ρ => Real.exp (E x ρ) * E' x ρ)
      (bound := fun ρ => (∑ k, |c k| * D) * Real.exp (V ρ)) Filter.univ_mem
      (Filter.Eventually.of_forall fun x => (hEm x).exp.aestronglyMeasurable) (hEi x)
      ((hEm x).exp.mul (hE'm x)).aestronglyMeasurable (ae_of_all _ fun ρ y _ => ?_)
      (hVi.const_mul _) (ae_of_all _ fun ρ y _ => ?_)).2
    · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul (hbd y ρ) (hle y ρ) (Real.exp_pos _).le
        (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) hD0)
    · have h : HasDerivAt (fun y => E y ρ) (E' y ρ) y := by
        have h1 : ∀ k ∈ Finset.univ, HasDerivAt (fun y => u (a k ρ + c k * y))
            (c k * deriv u (a k ρ + c k * y)) y := fun k _ => by
          have h2 : HasDerivAt (fun y => a k ρ + c k * y) (c k) y := by
            simpa using ((hasDerivAt_id y).const_mul (c k)).const_add (a k ρ)
          exact ((hu _).hasDerivAt.comp y h2).congr_deriv (mul_comm _ _)
        exact (HasDerivAt.fun_sum h1).add_const (V ρ)
      exact h.exp
  have hZ : 0 < ∫ ρ, Real.exp (E x ρ) ∂μ := integral_exp_pos (hEi x)
  refine (hder.log hZ.ne').congr_deriv ?_
  have hint : ∀ k, Integrable (fun ρ => Real.exp (E x ρ) * (c k * deriv u (a k ρ + c k * x)))
      μ := fun k => by
    refine ((hEi x).mul_const (|c k| * D)).mono' ((hEm x).exp.mul
      (((measurable_deriv u).comp ((ha k).add_const _)).const_mul _)).aestronglyMeasurable
      (ae_of_all _ fun ρ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _))
      (Real.exp_pos _).le
  have e : ∫ ρ, Real.exp (E x ρ) * E' x ρ ∂μ =
      ∑ k, ∫ ρ, Real.exp (E x ρ) * (c k * deriv u (a k ρ + c k * x)) ∂μ := by
    rw [← integral_finsetSum _ fun k _ => hint k]
    exact integral_congr_ae (ae_of_all _ fun ρ => by
      simp only [hE', Finset.mul_sum])
  rw [e, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_tilted_eq_div, ← mul_div_assoc, ← integral_const_mul]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun ρ => by ring)

end MeasureTheory

namespace ProbabilityTheory

/-- **A log-concave perturbation of a standard Gaussian has variance at most one** (Talagrand,
Lemma 3.2.3, Eqs. (3.71)--(3.73)): for differentiable concave `v` such that `exp v` is
integrable against `𝒩(0, 1)`, some `x₀` satisfies
`∫ (x - x₀)² exp (v x) dγ ≤ ∫ exp (v x) dγ`, with integrability. -/
theorem exists_integral_sub_sq_mul_exp_le_gaussianReal {v : ℝ → ℝ} (hv : Differentiable ℝ v)
    (hconc : ConcaveOn ℝ univ v) :
    ∃ x₀ : ℝ, Integrable (fun x => Real.exp (v x)) (gaussianReal 0 1) ∧
      Integrable (fun x => (x - x₀) ^ 2 * Real.exp (v x)) (gaussianReal 0 1) ∧
        ∫ x, (x - x₀) ^ 2 * Real.exp (v x) ∂(gaussianReal 0 1) ≤
          ∫ x, Real.exp (v x) ∂(gaussianReal 0 1) := by
  set w : ℝ → ℝ := fun x => v x - x ^ 2 / 2 with hw
  have hwd : ∀ x, HasDerivAt w (deriv v x - x) x := fun x => by
    refine ((hv x).hasDerivAt.sub ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv ?_
    ring
  obtain ⟨x₀, hx₀⟩ := MeasureTheory.exists_mode_concave_sub_mul_sq hconc
    (fun x => (hv x).hasDerivAt) (by norm_num : (0 : ℝ) < 1 / 2) 0
  have hineq : ∀ x, 1 * (x - x₀) ^ 2 ≤ -(deriv v x - x) * (x - x₀) := fun x => by
    have h := hx₀ x
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul x, add_zero, one_mul] at h
    rwa [one_mul]
  obtain ⟨h1, h2, h3⟩ := mul_integral_sub_sq_mul_exp_le one_pos hwd hineq
  rw [one_mul] at h3
  have hdens : ∀ f : ℝ → ℝ, (fun x => (gaussianPDF 0 1 x).toReal * (f x * Real.exp (v x))) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ * (f x * Real.exp (w x)) := fun f => by
    funext x
    rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [show Real.exp (w x) = Real.exp (v x) * Real.exp (-x ^ 2 / 2) by
      rw [← Real.exp_add]; congr 1; simp only [hw]; ring]
    ring
  have hI : ∀ f : ℝ → ℝ, Integrable (fun x => f x * Real.exp (w x)) →
      Integrable (fun x => f x * Real.exp (v x)) (gaussianReal 0 1) ∧
        ∫ x, f x * Real.exp (v x) ∂(gaussianReal 0 1) =
          (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x, f x * Real.exp (w x) := fun f hf => by
    constructor
    · rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
        integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
          (ae_of_all _ fun _ => gaussianPDF_lt_top)]
      simp only [smul_eq_mul, hdens]
      exact hf.const_mul _
    · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      have := congrFun (hdens f) x
      rwa [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)] at this
  have hone := hI (fun _ => 1) (by simpa using h1)
  simp only [one_mul] at hone
  have hsq := hI (fun x => (x - x₀) ^ 2) h2
  refine ⟨x₀, hone.1, hsq.1, ?_⟩
  rw [hsq.2, hone.2]
  exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 (Real.sqrt_nonneg _))

/-- **Talagrand, Lemma 3.2.3, Eq. (3.73) as a variance bound:** under the standard Gaussian
tilted by a differentiable concave function, the variance is at most `1`. -/
theorem variance_id_tilted_gaussianReal_le_one {v : ℝ → ℝ} (hv : Differentiable ℝ v)
    (hconc : ConcaveOn ℝ univ v) : Var[id; (gaussianReal 0 1).tilted v] ≤ 1 := by
  obtain ⟨x₀, h1, h2, h3⟩ := exists_integral_sub_sq_mul_exp_le_gaussianReal hv hconc
  have : IsProbabilityMeasure ((gaussianReal 0 1).tilted v) := isProbabilityMeasure_tilted h1
  have hvm : AEStronglyMeasurable (fun x : ℝ => x - x₀) ((gaussianReal 0 1).tilted v) :=
    (continuous_id.sub continuous_const).aestronglyMeasurable
  have hle : Var[fun x => x - x₀; (gaussianReal 0 1).tilted v] ≤ 1 := by
    refine (variance_le_expectation_sq hvm).trans ?_
    have hZ : 0 < ∫ x, Real.exp (v x) ∂(gaussianReal 0 1) := integral_exp_pos h1
    simp only [Pi.pow_apply]
    rw [integral_tilted]
    have e : ∀ x : ℝ, (Real.exp (v x) / ∫ y, Real.exp (v y) ∂(gaussianReal 0 1)) • (x - x₀) ^ 2 =
        (x - x₀) ^ 2 * Real.exp (v x) / ∫ y, Real.exp (v y) ∂(gaussianReal 0 1) := fun x => by
      rw [smul_eq_mul]; ring
    simp_rw [e]
    rw [integral_div, div_le_one hZ]
    exact h3
  have e := variance_sub_const (μ := (gaussianReal 0 1).tilted v) aestronglyMeasurable_id x₀
  simp only [id_eq] at e
  rwa [e] at hle

/-- **The pointwise form of `r̄ ≤ r`** (Talagrand, Lemma 3.2.3): for concave `u ≤ 0` with
bounded first two derivatives and all `a, c`,
`𝔼[(u'' + u'²)(θ) e^{u θ}] / 𝔼 e^{u θ} ≤ (𝔼[u' θ e^{u θ}] / 𝔼 e^{u θ})²`, where `θ = a + c ξ` and
`ξ` is a standard Gaussian. The case `c = 0` is included. -/
theorem integral_deriv_two_add_sq_mul_exp_div_le_sq {u : ℝ → ℝ} (hu : ConcaveOn ℝ univ u)
    (hu0 : ∀ x, u x ≤ 0) (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u)) {D D₂ : ℝ}
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
  have hu1m : Measurable fun x => deriv u (a + c * x) :=
    (measurable_deriv u).comp (by fun_prop)
  have hu2m : Measurable fun x => deriv (deriv u) (a + c * x) :=
    (measurable_deriv (deriv u)).comp (by fun_prop)
  have hem : Measurable fun x => Real.exp (v x) := Real.measurable_exp.comp
    hvd.continuous.measurable
  have hexp1 : ∀ x, Real.exp (v x) ≤ 1 := fun x => Real.exp_le_one_iff.2 (hu0 _)
  have hbd : ∀ {f g : ℝ → ℝ}, Measurable f → Integrable g (gaussianReal 0 1) →
      (∀ x, |f x| ≤ g x) → Integrable (fun x => f x * Real.exp (v x)) (gaussianReal 0 1) :=
    fun {f g} hf hg h => by
      refine hg.mono' (hf.mul hem).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hexp1 x)).trans (h x)
  have hid : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have h0 : Integrable (fun x => Real.exp (v x)) (gaussianReal 0 1) := by
    simpa using hbd (f := fun _ => 1) (g := fun _ => 1) measurable_const (integrable_const 1)
      (fun _ => by simp)
  have h1 : Integrable (fun x => x * Real.exp (v x)) (gaussianReal 0 1) :=
    hbd measurable_id hid fun _ => le_rfl
  have hK1 : Integrable (fun x => deriv u (a + c * x) * Real.exp (v x)) (gaussianReal 0 1) :=
    hbd hu1m (integrable_const D) fun x => hD _
  have hxK1 : Integrable (fun x => x * deriv u (a + c * x) * Real.exp (v x))
      (gaussianReal 0 1) :=
    hbd (measurable_id.mul hu1m) (hid.mul_const D) fun x => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  have hK2 : Integrable (fun x => (deriv (deriv u) (a + c * x) + deriv u (a + c * x) ^ 2) *
      Real.exp (v x)) (gaussianReal 0 1) :=
    hbd (hu2m.add (hu1m.pow_const 2)) (integrable_const (D₂ + D ^ 2)) fun x => by
      refine (abs_add_le _ _).trans (add_le_add (hD₂ _) ?_)
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hD _) 2
  obtain ⟨x₀, -, hsqi, hle⟩ := exists_integral_sub_sq_mul_exp_le_gaussianReal hvd hvc
  have h2 : Integrable (fun x => x ^ 2 * Real.exp (v x)) (gaussianReal 0 1) :=
    hbd (measurable_id.pow_const 2)
      ((memLp_id_gaussianReal 2).integrable_sq) fun x => by simp
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
      have h' := integral_id_mul_deriv_u_mul_exp_affine_gaussianReal 1
        (u := u) (u' := deriv u) (u'' := deriv (deriv u)) (fun x => (hu1 x).hasDerivAt)
        (fun x => (hu2 x).hasDerivAt) (B := 0) hu0 hD hD₂ a c
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

/-- The probability measure on `ℝ` with density proportional to `exp (d x - a x² / 2)`,
`a > 0`, is the Gaussian `𝒩(d / a, 1 / a)`. -/
theorem volume_tilted_mul_sub_mul_sq_eq_gaussianReal {a : ℝ} (ha : 0 < a) (d : ℝ) :
    (volume : Measure ℝ).tilted (fun x => d * x - a * x ^ 2 / 2) =
      gaussianReal (d / a) a⁻¹.toNNReal := by
  have hv : a⁻¹.toNNReal ≠ 0 := by
    simp [Real.toNNReal_eq_zero, not_le, ha]
  have hva : (a⁻¹.toNNReal : ℝ) = a⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 ha.le)
  set c : ℝ := (Real.sqrt (2 * Real.pi * a⁻¹))⁻¹ * Real.exp (-(d ^ 2 / (2 * a))) with hc
  have hc0 : 0 < c := mul_pos (inv_pos.2 (Real.sqrt_pos.2 (by positivity))) (Real.exp_pos _)
  have hpdf : ∀ x, gaussianPDFReal (d / a) a⁻¹.toNNReal x =
      c * Real.exp (d * x - a * x ^ 2 / 2) := fun x => by
    rw [gaussianPDFReal, hva, hc,
      mul_assoc ((Real.sqrt (2 * Real.pi * a⁻¹))⁻¹), ← Real.exp_add]
    congr 2
    field_simp
    ring
  have hI : ∫ x, Real.exp (d * x - a * x ^ 2 / 2) = c⁻¹ := by
    have h := integral_gaussianPDFReal_eq_one (d / a) hv
    simp only [hpdf] at h
    rw [integral_const_mul] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [gaussianReal_of_var_ne_zero _ hv, Measure.tilted]
  congr 1
  funext x
  rw [gaussianPDF, hpdf, hI, div_inv_eq_mul, mul_comm]

/-- The first two moments of the density proportional to `exp (d x - a x² / 2)`:
the mean is `d / a` and the second moment is `1 / a + (d / a)²` (Talagrand, Eqs. (3.78)--(3.80)). -/
theorem integral_id_and_sq_volume_tilted_mul_sub_mul_sq {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ∫ x, x ∂((volume : Measure ℝ).tilted fun x => d * x - a * x ^ 2 / 2) = d / a ∧
      ∫ x, x ^ 2 ∂((volume : Measure ℝ).tilted fun x => d * x - a * x ^ 2 / 2) =
        a⁻¹ + (d / a) ^ 2 := by
  rw [volume_tilted_mul_sub_mul_sq_eq_gaussianReal ha d]
  refine ⟨integral_id_gaussianReal, ?_⟩
  have h := variance_eq_sub (μ := gaussianReal (d / a) a⁻¹.toNNReal) (X := id)
    (memLp_id_gaussianReal 2)
  simp only [variance_id_gaussianReal, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    Real.coe_toNNReal _ (inv_nonneg.2 ha.le)] at h
  linarith

end ProbabilityTheory
