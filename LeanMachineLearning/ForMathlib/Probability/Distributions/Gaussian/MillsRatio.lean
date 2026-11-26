/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# Tail of the standard Gaussian, the inverse Mills ratio and truncated moments

With `p = gaussianPDFReal 0 1` and `T v = ℙ (ξ ≥ v)` for a standard Gaussian `ξ`, this file proves
the classical bounds `v T v ≤ p v` and `v p v ≤ (1 + v²) T v`, differentiates the inverse Mills
ratio `A = p / T`, and proves two estimates built on them (Talagrand, *Spin Glasses*, Vol. I,
Lemmas 3.3.7--3.3.9).

## Main declarations

* `ProbabilityTheory.mul_measureReal_gaussianReal_Ici_le`: Eq. (3.133), `v T v ≤ p v`.
* `ProbabilityTheory.mul_gaussianPDFReal_le_one_add_sq_mul`: Eq. (3.136).
* `ProbabilityTheory.hasDerivAt_measureReal_gaussianReal_Ici`: `T' = -p`.
* `ProbabilityTheory.hasDerivAt_gaussianPDFReal_div_measureReal_Ici`: Eq. (3.134), `A' = A² - v A`,
  with `A' ≥ 0`.
* `ProbabilityTheory.mul_gaussianPDFReal_lt_one_add_sq_mul`: the strict form of Eq. (3.136).
* `ProbabilityTheory.monotone_gaussianPDFReal_div_measureReal_Ici`,
  `ProbabilityTheory.exists_gaussianPDFReal_div_measureReal_Ici_le`,
  `ProbabilityTheory.exists_abs_log_measureReal_gaussianReal_Ici_le`: monotonicity and growth of
  the inverse Mills ratio and of `log ℙ (ξ ≥ v)`.
* `ProbabilityTheory.continuous_integral_min_sub_zero_sq` and
  `ProbabilityTheory.integral_min_zero_sq_of_map_neg_eq`: Lemma 3.3.9 for any finite measure with
  a second moment, respectively any symmetric one.
* `ProbabilityTheory.integral_min_zero_sq_gaussianReal`: Eq. (3.143).
* `ProbabilityTheory.neg_integral_id_mul_le_sqrt`: Cauchy--Schwarz on the negative half-line.
* `ProbabilityTheory.exists_sq_integral_id_mul_exp_div_le`: Lemma 3.3.8.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProbabilityTheory

/-- A function integrable against the standard Gaussian is integrable against its density. -/
theorem integrable_mul_gaussianPDFReal_of_integrable {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable fun t => f t * gaussianPDFReal 0 1 t := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hf
  refine hf.congr (ae_of_all _ fun t => ?_)
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
  rw [mul_comm]

/-- The standard Gaussian integral over `[v, ∞)` as an integral against the density. -/
theorem setIntegral_Ici_gaussianReal (f : ℝ → ℝ) (v : ℝ) :
    ∫ t in Ici v, f t ∂(gaussianReal 0 1) = ∫ t in Ioi v, f t * gaussianPDFReal 0 1 t := by
  rw [← integral_indicator measurableSet_Ici, integral_gaussianReal_eq_integral_smul one_ne_zero,
    ← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ Ici v
  · simp only [indicator_of_mem ht, smul_eq_mul, mul_comm]
  · simp only [indicator_of_notMem ht, smul_zero]

/-- `ℙ (ξ ≥ v) = ∫_v^∞ p`. -/
theorem measureReal_gaussianReal_Ici (v : ℝ) :
    (gaussianReal 0 1).real (Ici v) = ∫ t in Ioi v, gaussianPDFReal 0 1 t := by
  simpa using setIntegral_Ici_gaussianReal (fun _ => 1) v

/-- The tail of the standard Gaussian is positive. -/
theorem measureReal_gaussianReal_Ici_pos (v : ℝ) : 0 < (gaussianReal 0 1).real (Ici v) := by
  rw [measureReal_gaussianReal_Ici,
    setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun t => gaussianPDFReal_nonneg _ _ _)
      (integrable_gaussianPDFReal 0 1).integrableOn]
  have : Function.support (gaussianPDFReal 0 1) = univ :=
    eq_univ_of_forall fun t => (gaussianPDFReal_pos _ _ _ one_ne_zero).ne'
  rw [this, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

private theorem integrable_pow_mul_gaussianPDFReal (n : ℕ) :
    Integrable fun t : ℝ => t ^ n * gaussianPDFReal 0 1 t := by
  refine integrable_mul_gaussianPDFReal_of_integrable ?_
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) n).integrable_norm_pow'
  refine Integrable.mono' h (by fun_prop) (ae_of_all _ fun t => ?_)
  rw [norm_pow, id_eq]

private theorem hasDerivAt_neg_gaussianPDFReal (t : ℝ) :
    HasDerivAt (fun x => -gaussianPDFReal 0 1 x) (t * gaussianPDFReal 0 1 t) t := by
  refine (hasDerivAt_gaussianPDFReal_zero one_ne_zero t).neg.congr_deriv ?_
  rw [NNReal.coe_one, div_one]
  ring

/-- `∫_v^∞ t p t = p v`. -/
theorem integral_Ioi_id_mul_gaussianPDFReal (v : ℝ) :
    ∫ t in Ioi v, t * gaussianPDFReal 0 1 t = gaussianPDFReal 0 1 v := by
  have h1 : Integrable fun t : ℝ => t * gaussianPDFReal 0 1 t := by
    simpa using integrable_pow_mul_gaussianPDFReal 1
  have hlim : Tendsto (fun x => -gaussianPDFReal 0 1 x) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := v)
      (fun t _ => hasDerivAt_neg_gaussianPDFReal t) h1.integrableOn
      (integrable_gaussianPDFReal 0 1).neg.integrableOn
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hasDerivAt_neg_gaussianPDFReal t)
    h1.integrableOn hlim]
  ring

/-- `∫_v^∞ t² p t = v p v + ℙ (ξ ≥ v)`. -/
theorem integral_Ioi_sq_mul_gaussianPDFReal (v : ℝ) :
    ∫ t in Ioi v, t ^ 2 * gaussianPDFReal 0 1 t =
      v * gaussianPDFReal 0 1 v + (gaussianReal 0 1).real (Ici v) := by
  have h1 : Integrable fun t : ℝ => t * gaussianPDFReal 0 1 t := by
    simpa using integrable_pow_mul_gaussianPDFReal 1
  have h2 := integrable_pow_mul_gaussianPDFReal 2
  have h0 := integrable_gaussianPDFReal 0 1
  have hd : ∀ t, HasDerivAt (fun x => x * -gaussianPDFReal 0 1 x)
      (t ^ 2 * gaussianPDFReal 0 1 t - gaussianPDFReal 0 1 t) t := fun t => by
    refine ((hasDerivAt_id t).mul (hasDerivAt_neg_gaussianPDFReal t)).congr_deriv ?_
    simp only [id_eq]
    ring
  have hi : IntegrableOn (fun t => t ^ 2 * gaussianPDFReal 0 1 t - gaussianPDFReal 0 1 t)
      (Ioi v) := (h2.sub h0).integrableOn
  have hlim : Tendsto (fun x => x * -gaussianPDFReal 0 1 x) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := v) (fun t _ => hd t) hi
      (h1.neg.congr (ae_of_all _ fun t => by
        change -(t * gaussianPDFReal 0 1 t) = t * -gaussianPDFReal 0 1 t
        ring)).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hi hlim
  rw [integral_sub h2.integrableOn h0.integrableOn, ← measureReal_gaussianReal_Ici] at h
  linarith

/-- **Eq. (3.133):** `v ℙ (ξ ≥ v) ≤ p v` for every `v`. -/
theorem mul_measureReal_gaussianReal_Ici_le (v : ℝ) :
    v * (gaussianReal 0 1).real (Ici v) ≤ gaussianPDFReal 0 1 v := by
  rw [measureReal_gaussianReal_Ici, ← integral_const_mul,
    ← integral_Ioi_id_mul_gaussianPDFReal v]
  have h1 : Integrable fun t : ℝ => t * gaussianPDFReal 0 1 t := by
    simpa using integrable_pow_mul_gaussianPDFReal 1
  exact setIntegral_mono_on ((integrable_gaussianPDFReal 0 1).const_mul v).integrableOn
    h1.integrableOn measurableSet_Ioi fun t ht =>
      mul_le_mul_of_nonneg_right (le_of_lt ht) (gaussianPDFReal_nonneg _ _ _)

/-- **Eq. (3.136):** `v p v ≤ (1 + v²) ℙ (ξ ≥ v)` for every `v`. -/
theorem mul_gaussianPDFReal_le_one_add_sq_mul (v : ℝ) :
    v * gaussianPDFReal 0 1 v ≤ (1 + v ^ 2) * (gaussianReal 0 1).real (Ici v) := by
  have h1 : Integrable fun t : ℝ => t * gaussianPDFReal 0 1 t := by
    simpa using integrable_pow_mul_gaussianPDFReal 1
  have h2 := integrable_pow_mul_gaussianPDFReal 2
  have h0 := integrable_gaussianPDFReal 0 1
  have hnn : 0 ≤ ∫ t in Ioi v, (t - v) ^ 2 * gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ =>
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg _ _ _)
  have e : (fun t => (t - v) ^ 2 * gaussianPDFReal 0 1 t) = fun t =>
      t ^ 2 * gaussianPDFReal 0 1 t - 2 * v * (t * gaussianPDFReal 0 1 t) +
        v ^ 2 * gaussianPDFReal 0 1 t := by
    funext t; ring
  have h3 : IntegrableOn (fun t => t ^ 2 * gaussianPDFReal 0 1 t -
      2 * v * (t * gaussianPDFReal 0 1 t)) (Ioi v) := (h2.sub (h1.const_mul _)).integrableOn
  rw [e, integral_add h3 (h0.const_mul _).integrableOn,
    integral_sub h2.integrableOn (h1.const_mul _).integrableOn, integral_const_mul,
    integral_const_mul, integral_Ioi_sq_mul_gaussianPDFReal,
    integral_Ioi_id_mul_gaussianPDFReal, ← measureReal_gaussianReal_Ici] at hnn
  linarith

/-- The derivative of the Gaussian tail is minus the density. -/
theorem hasDerivAt_measureReal_gaussianReal_Ici (v : ℝ) :
    HasDerivAt (fun x => (gaussianReal 0 1).real (Ici x)) (-gaussianPDFReal 0 1 v) v := by
  have h0 := integrable_gaussianPDFReal 0 1
  have hc : Continuous (gaussianPDFReal 0 1) :=
    continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_gaussianPDFReal_zero one_ne_zero x).continuousAt
  have e : (fun x => (gaussianReal 0 1).real (Ici x)) = fun x =>
      (gaussianReal 0 1).real (Ici 0) - ∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t := by
    funext x
    rw [measureReal_gaussianReal_Ici, measureReal_gaussianReal_Ici,
      ← intervalIntegral.integral_interval_add_Ioi (a := 0) (b := x) h0.integrableOn
        h0.integrableOn]
    ring
  rw [e]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 v)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_sub _

/-- **Lemma 3.3.7, Eq. (3.134):** the inverse Mills ratio `A v = p v / ℙ (ξ ≥ v)` satisfies
`A' = A² - v A ≥ 0`. -/
theorem hasDerivAt_gaussianPDFReal_div_measureReal_Ici (v : ℝ) :
    ∀ A : ℝ → ℝ, (∀ x, A x = gaussianPDFReal 0 1 x / (gaussianReal 0 1).real (Ici x)) →
      HasDerivAt A (A v ^ 2 - v * A v) v ∧ 0 ≤ A v ^ 2 - v * A v := by
  intro A hA
  have hT := measureReal_gaussianReal_Ici_pos v
  constructor
  · have h := (hasDerivAt_gaussianPDFReal_zero one_ne_zero v).div
      (hasDerivAt_measureReal_gaussianReal_Ici v) hT.ne'
    have e : A = fun x => gaussianPDFReal 0 1 x / (gaussianReal 0 1).real (Ici x) := funext hA
    rw [e]
    refine h.congr_deriv ?_
    simp only [NNReal.coe_one, div_one]
    field_simp
    ring
  · have h1 : v ≤ A v := by
      rw [hA, le_div_iff₀ hT]
      exact mul_measureReal_gaussianReal_Ici_le v
    have h2 : 0 ≤ A v := by
      rw [hA]
      exact div_nonneg (gaussianPDFReal_nonneg _ _ _) hT.le
    nlinarith

/-- The strict form of Eq. (3.136): `v p v < (1 + v²) ℙ (ξ ≥ v)`. -/
theorem mul_gaussianPDFReal_lt_one_add_sq_mul (v : ℝ) :
    v * gaussianPDFReal 0 1 v < (1 + v ^ 2) * (gaussianReal 0 1).real (Ici v) := by
  refine (mul_gaussianPDFReal_le_one_add_sq_mul v).lt_of_ne fun h => ?_
  -- equality at `v` would make `v` a minimum of the nonnegative gap, so its derivative vanishes
  set g : ℝ → ℝ := fun x =>
    (1 + x ^ 2) * (gaussianReal 0 1).real (Ici x) - x * gaussianPDFReal 0 1 x with hg
  have hmin : IsLocalMin g v := Eventually.of_forall fun x => by
    have h0 : g v = 0 := by simp only [hg, h, sub_self]
    exact h0.trans_le (sub_nonneg.2 (mul_gaussianPDFReal_le_one_add_sq_mul x))
  have hd : HasDerivAt g (2 * v * (gaussianReal 0 1).real (Ici v) -
      2 * gaussianPDFReal 0 1 v) v := by
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * v) v := by
      simpa using (hasDerivAt_pow 2 v).const_add 1
    refine ((h1.mul (hasDerivAt_measureReal_gaussianReal_Ici v)).sub ((hasDerivAt_id v).mul
      (hasDerivAt_gaussianPDFReal_zero one_ne_zero v))).congr_deriv ?_
    simp only [NNReal.coe_one, div_one, id_eq]
    ring
  have h0 := hmin.hasDerivAt_eq_zero hd
  have h1 : v * (gaussianReal 0 1).real (Ici v) = gaussianPDFReal 0 1 v := by linarith
  have h2 : (gaussianReal 0 1).real (Ici v) = 0 := by
    rw [← h1] at h
    linear_combination -h
  exact (measureReal_gaussianReal_Ici_pos v).ne' h2

/-- The inverse Mills ratio is nonnegative. -/
theorem gaussianPDFReal_div_measureReal_Ici_nonneg (v : ℝ) :
    0 ≤ gaussianPDFReal 0 1 v / (gaussianReal 0 1).real (Ici v) :=
  div_nonneg (gaussianPDFReal_nonneg _ _ _) measureReal_nonneg

/-- The inverse Mills ratio is nondecreasing. -/
theorem monotone_gaussianPDFReal_div_measureReal_Ici :
    Monotone fun v => gaussianPDFReal 0 1 v / (gaussianReal 0 1).real (Ici v) := by
  have h := fun v => hasDerivAt_gaussianPDFReal_div_measureReal_Ici v _ fun _ => rfl
  exact monotone_of_deriv_nonneg (fun v => (h v).1.differentiableAt)
    fun v => (h v).1.deriv ▸ (h v).2

/-- The inverse Mills ratio grows at most linearly. -/
theorem exists_gaussianPDFReal_div_measureReal_Ici_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v, gaussianPDFReal 0 1 v / (gaussianReal 0 1).real (Ici v) ≤ C + |v| := by
  refine ⟨gaussianPDFReal 0 1 1 / (gaussianReal 0 1).real (Ici 1) + 1,
    add_nonneg (gaussianPDFReal_div_measureReal_Ici_nonneg 1) zero_le_one, fun v => ?_⟩
  have h1 := gaussianPDFReal_div_measureReal_Ici_nonneg 1
  rcases le_total v 1 with hv | hv
  · have := monotone_gaussianPDFReal_div_measureReal_Ici hv
    have := abs_nonneg v
    linarith
  · have hv0 : 0 < v := one_pos.trans_le hv
    have h : gaussianPDFReal 0 1 v / (gaussianReal 0 1).real (Ici v) ≤ v + 1 := by
      rw [div_le_iff₀ (measureReal_gaussianReal_Ici_pos v)]
      refine le_of_mul_le_mul_left ((mul_gaussianPDFReal_le_one_add_sq_mul v).trans ?_) hv0
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ measureReal_nonneg
      nlinarith
    rw [abs_of_pos hv0]
    linarith

/-- `d/dv log ℙ (ξ ≥ v) = -p v / ℙ (ξ ≥ v)` (Talagrand, Eq. (3.132)). -/
theorem hasDerivAt_log_measureReal_gaussianReal_Ici (v : ℝ) :
    HasDerivAt (fun x => Real.log ((gaussianReal 0 1).real (Ici x)))
      (-(gaussianPDFReal 0 1 v / (gaussianReal 0 1).real (Ici v))) v := by
  rw [← neg_div]
  exact (hasDerivAt_measureReal_gaussianReal_Ici v).log (measureReal_gaussianReal_Ici_pos v).ne'

/-- The logarithm of the Gaussian tail grows at most quadratically. -/
theorem exists_abs_log_measureReal_gaussianReal_Ici_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, |Real.log ((gaussianReal 0 1).real (Ici v))| ≤ C * (1 + |v|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_gaussianPDFReal_div_measureReal_Ici_le
  set c0 := |Real.log ((gaussianReal 0 1).real (Ici (0 : ℝ)))| with hc0
  refine ⟨c0 + C + 1, by positivity, fun v => ?_⟩
  have h := (convex_uIcc (0 : ℝ) v).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_log_measureReal_gaussianReal_Ici x).hasDerivWithinAt)
    (C := C + |v|) (fun x hx => by
      rw [norm_neg, Real.norm_of_nonneg (gaussianPDFReal_div_measureReal_Ici_nonneg x)]
      refine (hC x).trans (add_le_add le_rfl ?_)
      simpa using abs_sub_left_of_mem_uIcc hx)
    left_mem_uIcc right_mem_uIcc
  rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have h1 := (abs_sub_abs_le_abs_sub _ _).trans h
  rw [← hc0] at h1
  have h2 := abs_nonneg v
  have h3 : 0 ≤ c0 := abs_nonneg _
  nlinarith [mul_nonneg h3 h2, mul_nonneg h3 (sq_nonneg |v|), mul_nonneg hC0 h2,
    mul_nonneg hC0 (sq_nonneg |v|)]

/-- **Lemma 3.3.9:** `b ↦ ∫ (min (z - b) 0)² dμ`, that is `∫_{z ≤ b} (z - b)² dμ`, is continuous
for every finite measure with a second moment. -/
theorem continuous_integral_min_sub_zero_sq {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : MemLp id 2 μ) : Continuous fun b => ∫ z, min (z - b) 0 ^ 2 ∂μ := by
  refine continuous_iff_continuousAt.2 fun b₀ => ?_
  have hdom : Integrable (fun z => (|z| + (|b₀| + 1)) ^ 2) μ :=
    ((hμ.norm.add (memLp_const (|b₀| + 1))).integrable_sq).congr (ae_of_all _ fun z => rfl)
  refine continuousAt_of_dominated (Eventually.of_forall fun b => ?_) ?_ hdom
    (ae_of_all _ fun z => by fun_prop)
  · exact (by fun_prop : Continuous fun z : ℝ => min (z - b) 0 ^ 2).aestronglyMeasurable
  filter_upwards [Metric.ball_mem_nhds b₀ one_pos] with b hb
  refine ae_of_all _ fun z => ?_
  rw [Metric.mem_ball, Real.dist_eq] at hb
  have hb' : |b| ≤ |b₀| + 1 := by
    have := abs_sub_abs_le_abs_sub b b₀
    linarith
  have h1 : |min (z - b) 0| ≤ |z| + (|b₀| + 1) := by
    have h2 : |min (z - b) 0| ≤ |z - b| := by
      rcases le_total (z - b) 0 with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, abs_zero]; exact abs_nonneg _
    exact h2.trans ((abs_sub _ _).trans (add_le_add le_rfl hb'))
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- For a symmetric measure with a second moment, `∫_{z ≤ 0} z² = (1/2) ∫ z²`; for a standard
Gaussian the value is `1/2` (Talagrand, Eq. (3.143)). -/
theorem integral_min_zero_sq_of_map_neg_eq {μ : Measure ℝ} (hμ : MemLp id 2 μ)
    (hsym : μ.map Neg.neg = μ) :
    ∫ z, min z 0 ^ 2 ∂μ = (∫ z, z ^ 2 ∂μ) / 2 := by
  have hmin : ∀ f : ℝ → ℝ, (∀ z, |f z| ≤ |z|) → Continuous f →
      Integrable (fun z => f z ^ 2) μ := fun f hf hfc => by
    refine Integrable.mono' hμ.integrable_sq (hfc.pow 2).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_pow, Real.norm_eq_abs, id_eq, ← sq_abs z]
    exact pow_le_pow_left₀ (abs_nonneg _) (hf z) 2
  have habs : ∀ z : ℝ, |min z 0| ≤ |z| := fun z => by
    rcases le_total z 0 with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, abs_zero]; exact abs_nonneg _
  have h1 := hmin (fun z => min z 0) habs (by fun_prop)
  have h2 := hmin (fun z => min (-z) 0) (fun z => (habs (-z)).trans_eq (abs_neg z)) (by fun_prop)
  have hflip : ∫ z, min (-z) 0 ^ 2 ∂μ = ∫ z, min z 0 ^ 2 ∂μ := by
    conv_rhs => rw [← hsym]
    rw [integral_map measurable_neg.aemeasurable
      (by fun_prop : Continuous fun z : ℝ => min z 0 ^ 2).aestronglyMeasurable]
  have hsum : ∫ z, z ^ 2 ∂μ = (∫ z, min z 0 ^ 2 ∂μ) + ∫ z, min (-z) 0 ^ 2 ∂μ := by
    rw [← integral_add h1 h2]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    rcases le_total z 0 with h | h
    · simp [min_eq_left h, min_eq_right (neg_nonneg.2 h)]
    · simp [min_eq_right h, min_eq_left (neg_nonpos.2 h)]
  rw [hsum, hflip]
  ring

/-- `𝔼 (min ξ 0)² = 1 / 2` for a standard Gaussian `ξ` (Talagrand, Eq. (3.143)). -/
theorem integral_min_zero_sq_gaussianReal :
    ∫ z, min z 0 ^ 2 ∂(gaussianReal 0 1) = 1 / 2 := by
  have hsq : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := id) aemeasurable_id
      integral_id_gaussianReal
    rw [variance_id_gaussianReal, NNReal.coe_one] at h
    simpa only [id_eq] using h.symm
  have hsym : (gaussianReal 0 1).map Neg.neg = gaussianReal 0 1 := by
    rw [show (Neg.neg : ℝ → ℝ) = fun x => -x from rfl, gaussianReal_map_neg, neg_zero]
  rw [integral_min_zero_sq_of_map_neg_eq (memLp_id_gaussianReal' 2 (by simp)) hsym, hsq]

/-- Cauchy--Schwarz on the negative half-line: for `V ≥ 0`,
`-∫ x V x dμ ≤ (∫ (min x 0)² dμ · ∫ V² dμ)^(1/2)`. -/
theorem neg_integral_id_mul_le_sqrt {μ : Measure ℝ} (hμ : MemLp id 2 μ) {V : ℝ → ℝ}
    (hV : MemLp V 2 μ) (hV0 : ∀ x, 0 ≤ V x) :
    -∫ x, x * V x ∂μ ≤ Real.sqrt ((∫ x, min x 0 ^ 2 ∂μ) * ∫ x, V x ^ 2 ∂μ) := by
  have hm : MemLp (fun x : ℝ => -min x 0) 2 μ := by
    refine hμ.mono (by fun_prop : Measurable fun x : ℝ => -min x 0).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_neg, id_eq]
    rcases le_total x 0 with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, norm_zero]; exact norm_nonneg _
  have hm0 : ∀ x : ℝ, 0 ≤ -min x 0 := fun x => neg_nonneg.2 (min_le_right _ _)
  have hxV : Integrable (fun x => x * V x) μ := hμ.integrable_mul hV
  have hle : -∫ x, x * V x ∂μ ≤ ∫ x, -min x 0 * V x ∂μ := by
    rw [← integral_neg]
    refine integral_mono hxV.neg (hm.integrable_mul hV) fun x => ?_
    change -(x * V x) ≤ -min x 0 * V x
    rw [neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hV0 x)
  refine hle.trans ?_
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (f := fun x => -min x 0) (g := V) Real.HolderConjugate.two_two (ae_of_all _ hm0)
    (ae_of_all _ hV0) (by simpa using hm) (by simpa using hV)
  simp only [Real.rpow_two, neg_sq] at hCS
  rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul (integral_nonneg fun _ => sq_nonneg _)] at hCS

/-- **Lemma 3.3.8:** there is a universal `L` such that for every nondecreasing `v ≤ 0` which
vanishes on `[Y, ∞)`, `(𝔼 [ξ e^{v ξ}] / 𝔼 e^{v ξ})² ≤ (max Y 0)² + L` for a standard Gaussian
`ξ`. -/
theorem exists_sq_integral_id_mul_exp_div_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (v : ℝ → ℝ) (Y : ℝ), Monotone v → (∀ x, v x ≤ 0) →
      (∀ x, Y ≤ x → v x = 0) →
      ((∫ ξ, ξ * Real.exp (v ξ) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (v ξ) ∂(gaussianReal 0 1)) ^ 2 ≤ max Y 0 ^ 2 + L := by
  set p1 := (gaussianReal 0 1).real (Ici (1 : ℝ)) with hp1
  have hp10 : 0 < p1 := measureReal_gaussianReal_Ici_pos 1
  refine ⟨max 3 (p1⁻¹ ^ 2), le_trans (by norm_num) (le_max_left _ _),
    fun v Y hv hv0 hvY => ?_⟩
  set γ := gaussianReal 0 1 with hγ
  have hvm : Measurable fun x => Real.exp (v x) := Real.measurable_exp.comp hv.measurable
  have hexp1 : ∀ x, Real.exp (v x) ≤ 1 := fun x => Real.exp_le_one_iff.2 (hv0 x)
  have h0 : Integrable (fun x => Real.exp (v x)) γ :=
    Integrable.of_bound hvm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hexp1 x)
  have hid : Integrable (fun x : ℝ => x) γ := (memLp_id_gaussianReal 1).integrable le_rfl
  have h1 : Integrable (fun x => x * Real.exp (v x)) γ := by
    refine hid.abs.mono' (measurable_id.mul hvm).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hexp1 x)
  set N := ∫ ξ, ξ * Real.exp (v ξ) ∂γ with hN
  set Z := ∫ ξ, Real.exp (v ξ) ∂γ with hZ
  have hZ0 : 0 < Z := integral_exp_pos h0
  have hN0 : 0 ≤ N := by
    have hpt : ∀ x, 0 ≤ x * (Real.exp (v x) - Real.exp (v 0)) := fun x => by
      rcases le_total 0 x with h | h
      · exact mul_nonneg h (sub_nonneg.2 (Real.exp_le_exp.2 (hv h)))
      · exact mul_nonneg_of_nonpos_of_nonpos h
          (sub_nonpos.2 (Real.exp_le_exp.2 (hv h)))
    have e : (fun x => x * (Real.exp (v x) - Real.exp (v 0))) =
        fun x => x * Real.exp (v x) - Real.exp (v 0) * x := by
      funext x; ring
    have h : 0 ≤ ∫ x, x * (Real.exp (v x) - Real.exp (v 0)) ∂γ := integral_nonneg hpt
    rw [e, integral_sub h1 (hid.const_mul _), integral_const_mul] at h
    have h2 : ∫ x, x ∂γ = 0 := integral_id_gaussianReal
    rw [h2, mul_zero, sub_zero] at h
    exact h
  have htail : ∀ a : ℝ, Y ≤ a → ∫ x in Ici a, Real.exp (v x) ∂γ = γ.real (Ici a) := fun a ha => by
    rw [setIntegral_congr_fun (g := fun _ => (1 : ℝ)) measurableSet_Ici fun x hx => by
      rw [hvY x (ha.trans hx), Real.exp_zero], setIntegral_const, smul_eq_mul, mul_one]
  rcases le_total 1 Y with hY | hY
  · have hY0 : 0 < Y := one_pos.trans_le hY
    set U := ∫ x in Iio Y, Real.exp (v x) ∂γ with hU
    have hZs : Z = U + γ.real (Ici Y) := by
      rw [hZ, ← integral_add_compl measurableSet_Iio h0, compl_Iio, htail Y le_rfl]
    have hNs : N ≤ Y * U + gaussianPDFReal 0 1 Y := by
      have hA : ∫ x in Iio Y, x * Real.exp (v x) ∂γ ≤ Y * U := by
        rw [hU, ← integral_const_mul]
        exact setIntegral_mono_on h1.integrableOn (h0.const_mul Y).integrableOn
          measurableSet_Iio fun x hx =>
            mul_le_mul_of_nonneg_right (le_of_lt hx) (Real.exp_pos _).le
      have hB : ∫ x in Ici Y, x * Real.exp (v x) ∂γ = gaussianPDFReal 0 1 Y := by
        rw [setIntegral_congr_fun (g := fun x => x) measurableSet_Ici fun x hx => by
              rw [hvY x hx, Real.exp_zero, mul_one], setIntegral_Ici_gaussianReal,
          integral_Ioi_id_mul_gaussianPDFReal]
      have hsplit := integral_add_compl (measurableSet_Iio (a := Y)) h1
      rw [compl_Iio] at hsplit
      rw [hN, ← hsplit]
      exact add_le_add hA hB.le
    have hU0 : 0 ≤ U := integral_nonneg fun _ => (Real.exp_pos _).le
    have hmills : gaussianPDFReal 0 1 Y ≤ (Y + 1 / Y) * γ.real (Ici Y) := by
      have h := mul_gaussianPDFReal_le_one_add_sq_mul Y
      rw [← hγ] at h
      have e : (Y + 1 / Y) * γ.real (Ici Y) = (1 + Y ^ 2) * γ.real (Ici Y) / Y := by
        field_simp; ring
      rw [e, le_div_iff₀ hY0, mul_comm]
      exact h
    have hratio : N / Z ≤ Y + 1 / Y := by
      rw [div_le_iff₀ hZ0, hZs, mul_add]
      refine hNs.trans (add_le_add ?_ hmills)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hU0
    have hsq := pow_le_pow_left₀ (div_nonneg hN0 hZ0.le) hratio 2
    refine hsq.trans ?_
    rw [max_eq_left hY0.le]
    have h2 : (Y + 1 / Y) ^ 2 = Y ^ 2 + 2 + (1 / Y) ^ 2 := by
      field_simp; ring
    have h3 : (1 / Y) ^ 2 ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      rw [div_le_one hY0]; exact hY
    have h4 : (3 : ℝ) ≤ max 3 (p1⁻¹ ^ 2) := le_max_left _ _
    linarith
  · have hNle : N ≤ 1 := by
      have h2 : N ≤ ∫ x, |x| ∂γ :=
        integral_mono h1 hid.abs fun x => (le_abs_self _).trans (by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_of_le_one_right (abs_nonneg _) (hexp1 x))
      have h3 : (∫ x, |x| ∂γ) ^ 2 ≤ 1 := by
        have habs : MemLp (fun x : ℝ => |x|) 2 γ := by
          have h : MemLp (id : ℝ → ℝ) 2 γ := memLp_id_gaussianReal' 2 (by simp)
          exact h.norm.ae_eq (ae_of_all _ fun x => Real.norm_eq_abs x)
        have hv' := variance_nonneg (fun x : ℝ => |x|) γ
        rw [variance_eq_sub habs] at hv'
        simp only [Pi.pow_apply, sq_abs] at hv'
        have h4 : ∫ x, x ^ 2 ∂γ = 1 := by
          have h := variance_of_integral_eq_zero (μ := γ) (X := id) aemeasurable_id
            integral_id_gaussianReal
          rw [variance_id_gaussianReal, NNReal.coe_one] at h
          simpa only [id_eq] using h.symm
        linarith
      have h5 : ∫ x, |x| ∂γ ≤ 1 := by
        have h6 : 0 ≤ ∫ x, |x| ∂γ := integral_nonneg fun _ => abs_nonneg _
        nlinarith
      exact h2.trans h5
    have hZge : p1 ≤ Z := by
      rw [hp1, ← htail 1 hY]
      exact setIntegral_le_integral h0 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    have hratio : N / Z ≤ p1⁻¹ := by
      rw [div_le_iff₀ hZ0]
      refine hNle.trans ?_
      rw [inv_mul_eq_div, le_div_iff₀ hp10, one_mul]
      exact hZge
    have hsq := pow_le_pow_left₀ (div_nonneg hN0 hZ0.le) hratio 2
    exact hsq.trans ((le_max_right _ _).trans (le_add_of_nonneg_left (sq_nonneg _)))

end ProbabilityTheory
