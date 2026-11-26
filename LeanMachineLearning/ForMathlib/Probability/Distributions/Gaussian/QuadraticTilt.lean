/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import LeanMachineLearning.ForMathlib.Probability.StdGaussianRadial

/-!
# Densities with a quadratic confinement

Integrals against `exp (-b ‖v‖² + ⟪a, v⟫)` on a finite-dimensional real inner product space.

## Main declarations

* `integrable_exp_neg_mul_sq_norm_add_inner`, `integral_exp_neg_mul_sq_norm_add_inner`:
  the Gaussian integral with a linear term.
* `integrable_one_add_norm_pow_mul_exp`: polynomials are integrable against a confining weight.
* `integral_mul_exp_neg_mul_sq_norm`: the weight `exp (-b ‖v‖²)` is a rescaled standard Gaussian.
* `integral_abs_inner_stdGaussian_le`: `𝔼 |⟪a, z⟫| ≤ ‖a‖`.
* `integral_tilted_restrict_neg_half_sq_norm`: conditioning a standard Gaussian on a set.
* `hasDerivAt_integral_tilted_sum_comp_inner_line`: differentiation of `⟨F⟩` along a line of the
  vectors defining the density proportional to
  `exp (∑ k, u ⟪v k, σ⟫ - κ ‖σ‖² + ⟪a, σ⟫)`.
* `integrable_exp_add_neg_mul_sq_norm_add_inner` and
  `integral_exp_half_sq_norm_tilted_le`: for a nonpositive perturbation `U`, the density
  proportional to `exp (U v - κ ‖v‖² + ⟪a, v⟫)` satisfies
  `∫ exp (κ ‖v‖² / 2) ≤ Z⁻¹ (2 π / κ) ^ (d / 2) exp (‖a‖² / (2 κ))`
  (Talagrand, *Spin Glasses*, Vol. I, Lemma 3.1.5).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem cexp_neg_mul_sq_norm_add_inner (b : ℝ) (a v : E) :
    Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + 1 * (⟪a, v⟫ : ℂ)) =
      ((Real.exp (-b * ‖v‖ ^ 2 + ⟪a, v⟫) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- `exp (-b ‖v‖² + ⟪a, v⟫)` is integrable for `b > 0`. -/
theorem integrable_exp_neg_mul_sq_norm_add_inner {b : ℝ} (hb : 0 < b) (a : E) :
    Integrable fun v : E => Real.exp (-b * ‖v‖ ^ 2 + ⟪a, v⟫) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (b : ℂ))
    (by simpa using hb) 1 a
  refine h.re.congr (ae_of_all _ fun v => ?_)
  exact (congrArg Complex.re (cexp_neg_mul_sq_norm_add_inner b a v)).trans (Complex.ofReal_re _)

/-- A polynomial times the exponential of a confining quadratic is integrable. -/
theorem integrable_one_add_norm_pow_mul_exp {κ : ℝ} (hκ : 0 < κ) (B : ℝ) (n : ℕ) :
    Integrable fun x : E => (1 + ‖x‖) ^ n * Real.exp (B * ‖x‖ - κ * ‖x‖ ^ 2) := by
  have hbase := integrable_exp_neg_mul_sq_norm_add_inner (E := E) (half_pos hκ) 0
  simp only [inner_zero_left, add_zero] at hbase
  refine (hbase.const_mul (Real.exp ((B + n) ^ 2 / (2 * κ)))).mono'
    (by fun_prop : Continuous fun x : E =>
      (1 + ‖x‖) ^ n * Real.exp (B * ‖x‖ - κ * ‖x‖ ^ 2)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← Real.exp_add]
  have h1 : (1 + ‖x‖) ^ n ≤ Real.exp (n * ‖x‖) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ‖x‖]) n
  refine (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have h2 : 0 ≤ (κ * ‖x‖ - (B + n)) ^ 2 / (2 * κ) := by positivity
  have h3 : (κ * ‖x‖ - (B + n)) ^ 2 / (2 * κ) =
      κ / 2 * ‖x‖ ^ 2 - (B + n) * ‖x‖ + (B + n) ^ 2 / (2 * κ) := by
    field_simp
    ring
  linarith

/-- **Gaussian integral with a linear term:**
`∫ exp (-b ‖v‖² + ⟪a, v⟫) = (π / b) ^ (d / 2) exp (‖a‖² / (4 b))`. -/
theorem integral_exp_neg_mul_sq_norm_add_inner {b : ℝ} (hb : 0 < b) (a : E) :
    ∫ v : E, Real.exp (-b * ‖v‖ ^ 2 + ⟪a, v⟫) =
      (π / b) ^ ((finrank ℝ E : ℝ) / 2) * Real.exp (‖a‖ ^ 2 / (4 * b)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := E) (b := (b : ℂ))
    (by simpa using hb) 1 a
  rw [integral_congr_ae (ae_of_all _ (cexp_neg_mul_sq_norm_add_inner b a)),
    integral_complex_ofReal] at h
  have hpow : ((π : ℂ) / (b : ℂ)) ^ ((finrank ℝ E : ℂ) / 2) =
      (((π / b) ^ ((finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hexp : Complex.exp ((1 : ℂ) ^ 2 * (‖a‖ : ℂ) ^ 2 / (4 * (b : ℂ))) =
      ((Real.exp (‖a‖ ^ 2 / (4 * b)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hpow, hexp, ← Complex.ofReal_mul] at h
  exact_mod_cast h

/-- **The quadratic weight is a rescaled standard Gaussian:**
`∫ f v exp (-b ‖v‖²) dv = (π / b) ^ (d / 2) 𝔼 f (z / √(2 b))`. -/
theorem integral_mul_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) (f : E → ℝ) :
    ∫ v : E, f v * Real.exp (-b * ‖v‖ ^ 2) =
      (π / b) ^ ((finrank ℝ E : ℝ) / 2) *
        ∫ z, f ((Real.sqrt (2 * b))⁻¹ • z) ∂stdGaussian E := by
  set c : ℝ := (Real.sqrt (2 * b))⁻¹ with hc
  have h2b : 0 < 2 * b := by positivity
  have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 h2b)
  set d : ℝ := (finrank ℝ E : ℝ) with hd
  have hsq : c ^ 2 = (2 * b)⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt h2b.le]
  have hstd : ∫ z, f (c • z) ∂stdGaussian E =
      (2 * π) ^ (-d / 2) * ∫ z : E, f (c • z) * Real.exp (-b * ‖c • z‖ ^ 2) := by
    rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have he : -b * ‖c • z‖ ^ 2 = -‖z‖ ^ 2 / 2 := by
      rw [norm_smul, Real.norm_of_nonneg hc0.le, mul_pow, hsq]
      field_simp
    change (ENNReal.ofReal ((2 * π) ^ (-d / 2) * Real.exp (-‖z‖ ^ 2 / 2))).toReal • f (c • z) =
      (2 * π) ^ (-d / 2) * (f (c • z) * Real.exp (-b * ‖c • z‖ ^ 2))
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul, he]
    ring
  rw [hstd, Measure.integral_comp_smul_of_nonneg volume
    (fun v : E => f v * Real.exp (-b * ‖v‖ ^ 2)) c (hR := hc0.le), smul_eq_mul]
  have hconst : (π / b) ^ (d / 2) * ((2 * π) ^ (-d / 2) * (c ^ finrank ℝ E)⁻¹) = 1 := by
    have h1 : (c ^ finrank ℝ E)⁻¹ = (2 * b) ^ (d / 2) := by
      rw [hc, inv_pow, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2b.le,
        ← hd]
      ring_nf
    rw [h1, neg_div, Real.rpow_neg (by positivity), mul_left_comm,
      ← Real.mul_rpow (by positivity) h2b.le,
      show π / b * (2 * b) = 2 * π by field_simp,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos (by positivity) _).ne']
  rw [← mul_assoc ((2 * π) ^ (-d / 2)), ← mul_assoc, hconst, one_mul]

/-- The mean absolute value of a linear form of a standard Gaussian is at most the norm of its
coefficient vector. -/
theorem integral_abs_inner_stdGaussian_le (a : E) :
    ∫ z, |⟪a, z⟫| ∂stdGaussian E ≤ ‖a‖ := by
  set L : StrongDual ℝ E := innerSL ℝ a with hL
  have hLz : ∀ z, L z = ⟪a, z⟫ := fun z => rfl
  have hmem : MemLp L 2 (stdGaussian E) := IsGaussian.memLp_dual _ L 2 (by norm_num)
  have h2 : ∫ z, ⟪a, z⟫ ^ 2 ∂stdGaussian E = ‖a‖ ^ 2 := by
    have hv := variance_dual_stdGaussian L
    rw [variance_of_integral_eq_zero hmem.aemeasurable (integral_strongDual_stdGaussian L),
      show ‖L‖ = ‖a‖ from innerSL_apply_norm ℝ a] at hv
    simpa only [hLz] using hv
  have habs : MemLp (fun z => |⟪a, z⟫|) 2 (stdGaussian E) := by
    simpa only [Real.norm_eq_abs, hLz] using hmem.norm
  have hvar := variance_nonneg (fun z => |⟪a, z⟫|) (stdGaussian E)
  rw [variance_eq_sub habs] at hvar
  simp only [Pi.pow_apply, sq_abs, h2] at hvar
  exact le_of_sq_le_sq (by linarith) (norm_nonneg a)

/-- **Conditioning a standard Gaussian on a measurable set** is the probability measure with
density proportional to `exp (-‖v‖² / 2)` on that set. -/
theorem integral_tilted_restrict_neg_half_sq_norm {C : Set E} (hC : MeasurableSet C)
    (f : E → ℝ) :
    ∫ v, f v ∂((volume.restrict C).tilted fun v => -(‖v‖ ^ 2 / 2)) =
      (∫ v in C, f v ∂stdGaussian E) / (stdGaussian E).real C := by
  have key : ∀ g : E → ℝ, ∫ v in C, g v * Real.exp (-(‖v‖ ^ 2 / 2)) =
      (π / (1 / 2)) ^ ((finrank ℝ E : ℝ) / 2) * ∫ v in C, g v ∂stdGaussian E := fun g => by
    have h := integral_mul_exp_neg_mul_sq_norm (E := E) (by norm_num : (0 : ℝ) < 1 / 2)
      (C.indicator g)
    rw [show Real.sqrt (2 * (1 / 2)) = 1 by norm_num, inv_one] at h
    simp only [one_smul] at h
    rw [← integral_indicator hC, ← integral_indicator hC, ← h]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have e : -(1 / 2 : ℝ) * ‖v‖ ^ 2 = -(‖v‖ ^ 2 / 2) := by ring
    by_cases hv : v ∈ C
    · simp only [Set.indicator_of_mem hv, e]
    · simp [hv]
  have h1 := key fun _ => 1
  simp only [one_mul, setIntegral_const, smul_eq_mul, mul_one] at h1
  have h2 : ∀ Z : ℝ, ∫ v in C, (Real.exp (-(‖v‖ ^ 2 / 2)) / Z) • f v =
      (∫ v in C, f v * Real.exp (-(‖v‖ ^ 2 / 2))) / Z := fun Z => by
    rw [← integral_div]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [smul_eq_mul]
    ring
  rw [integral_tilted, h2, key f, h1]
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos (by positivity) _).ne'

section NonpositivePerturbation

variable {U : E → ℝ} {κ : ℝ}

/-- For `U ≤ 0` the weight `exp (U v - κ ‖v‖² + ⟪a, v⟫)` is integrable. -/
theorem integrable_exp_add_neg_mul_sq_norm_add_inner (hU : Measurable U) (hU0 : ∀ v, U v ≤ 0)
    (hκ : 0 < κ) (a : E) :
    Integrable fun v : E => Real.exp (U v - κ * ‖v‖ ^ 2 + ⟪a, v⟫) := by
  refine Integrable.mono' (integrable_exp_neg_mul_sq_norm_add_inner hκ a)
    (by fun_prop : Measurable fun v : E =>
      Real.exp (U v - κ * ‖v‖ ^ 2 + ⟪a, v⟫)).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  linarith [hU0 v]

/-- **Talagrand, Lemma 3.1.5.** If `U ≤ 0` and `μ` has density proportional to
`exp (U v - κ ‖v‖² + ⟪a, v⟫)`, with normalizer `Z`, then
`∫ exp (κ ‖v‖² / 2) dμ ≤ Z⁻¹ (2 π / κ) ^ (d / 2) exp (‖a‖² / (2 κ))`.
Integrability is part of the conclusion. -/
theorem integral_exp_half_sq_norm_tilted_le (hU : Measurable U) (hU0 : ∀ v, U v ≤ 0)
    (hκ : 0 < κ) (a : E) :
    Integrable (fun v : E => Real.exp (κ / 2 * ‖v‖ ^ 2))
        (volume.tilted fun v => U v - κ * ‖v‖ ^ 2 + ⟪a, v⟫) ∧
      ∫ v, Real.exp (κ / 2 * ‖v‖ ^ 2)
          ∂(volume.tilted fun v => U v - κ * ‖v‖ ^ 2 + ⟪a, v⟫) ≤
        (∫ v : E, Real.exp (U v - κ * ‖v‖ ^ 2 + ⟪a, v⟫))⁻¹ *
          ((2 * π / κ) ^ ((finrank ℝ E : ℝ) / 2) * Real.exp (‖a‖ ^ 2 / (2 * κ))) := by
  set W : E → ℝ := fun v => U v - κ * ‖v‖ ^ 2 + ⟪a, v⟫ with hW
  set Z : ℝ := ∫ v, Real.exp (W v) with hZ
  have hWi : Integrable fun v => Real.exp (W v) :=
    integrable_exp_add_neg_mul_sq_norm_add_inner hU hU0 hκ a
  have hZ0 : 0 < Z := integral_exp_pos hWi
  have hκ2 : 0 < κ / 2 := by positivity
  have hdom := integrable_exp_neg_mul_sq_norm_add_inner hκ2 a
  have hpt : ∀ v, Real.exp (W v) * Real.exp (κ / 2 * ‖v‖ ^ 2) ≤
      Real.exp (-(κ / 2) * ‖v‖ ^ 2 + ⟪a, v⟫) := fun v => by
    rw [← Real.exp_add, Real.exp_le_exp, hW]
    linarith [hU0 v]
  have hprod : Integrable fun v => Real.exp (W v) * Real.exp (κ / 2 * ‖v‖ ^ 2) :=
    Integrable.mono' hdom (by fun_prop : Measurable fun v : E =>
        Real.exp (U v - κ * ‖v‖ ^ 2 + ⟪a, v⟫) *
          Real.exp (κ / 2 * ‖v‖ ^ 2)).aestronglyMeasurable (ae_of_all _ fun v => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt v)
  refine ⟨(integrable_tilted_iff hWi _).2 (by simpa only [smul_eq_mul] using hprod), ?_⟩
  rw [integral_tilted]
  have e : ∀ v, (Real.exp (W v) / Z) • Real.exp (κ / 2 * ‖v‖ ^ 2) =
      Z⁻¹ * (Real.exp (W v) * Real.exp (κ / 2 * ‖v‖ ^ 2)) := fun v => by
    rw [smul_eq_mul]; ring
  simp_rw [← hZ, e]
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ((integral_mono hprod hdom hpt).trans_eq ?_)
    (inv_nonneg.2 hZ0.le)
  rw [integral_exp_neg_mul_sq_norm_add_inner hκ2 a]
  congr 2
  · field_simp
  · congr 1
    ring

end NonpositivePerturbation

section RidgePotential

variable {ι : Type*} [Fintype ι]

/-- **Differentiation of a Gibbs average along a line of the parameters.** Let the density be
proportional to `exp (∑ k, u ⟪v k, σ⟫ - κ ‖σ‖² + ⟪a, σ⟫)`, with `u ≤ 0` differentiable and
`|u'| ≤ D`. For an observable of at most quadratic growth, `r ↦ ⟨F⟩` along
`(v + r w, a + r c)` has derivative `⟨F X⟩ - ⟨F⟩ ⟨X⟩` at `t`, where
`X σ = ∑ k, u' ⟪v k + t w k, σ⟫ ⟪w k, σ⟫ + ⟪c, σ⟫`. -/
theorem hasDerivAt_integral_tilted_sum_comp_inner_line {κ : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    (v w : ι → E) (a c : E) {F : E → ℝ} (hF : Measurable F) {C : ℝ}
    (hFb : ∀ σ, |F σ| ≤ C * (1 + ‖σ‖ ^ 2)) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ σ, F σ ∂(volume.tilted fun σ =>
        (∑ k, u ⟪v k + r • w k, σ⟫) - κ * ‖σ‖ ^ 2 + ⟪a + r • c, σ⟫))
      ((∫ σ, F σ * ((∑ k, deriv u ⟪v k + t • w k, σ⟫ * ⟪w k, σ⟫) + ⟪c, σ⟫)
          ∂(volume.tilted fun σ =>
            (∑ k, u ⟪v k + t • w k, σ⟫) - κ * ‖σ‖ ^ 2 + ⟪a + t • c, σ⟫)) -
        (∫ σ, F σ ∂(volume.tilted fun σ =>
            (∑ k, u ⟪v k + t • w k, σ⟫) - κ * ‖σ‖ ^ 2 + ⟪a + t • c, σ⟫)) *
          ∫ σ, (∑ k, deriv u ⟪v k + t • w k, σ⟫ * ⟪w k, σ⟫) + ⟪c, σ⟫
            ∂(volume.tilted fun σ =>
              (∑ k, u ⟪v k + t • w k, σ⟫) - κ * ‖σ‖ ^ 2 + ⟪a + t • c, σ⟫)) t := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hFb 0)
    simpa using this
  have hum : Measurable u := hu.continuous.measurable
  set e : ℝ → E → ℝ := fun r σ =>
    (∑ k, u ⟪v k + r • w k, σ⟫) - κ * ‖σ‖ ^ 2 + ⟪a + r • c, σ⟫ with he
  set X : ℝ → E → ℝ := fun r σ =>
    (∑ k, deriv u ⟪v k + r • w k, σ⟫ * ⟪w k, σ⟫) + ⟪c, σ⟫ with hX
  set L : ℝ := D * (∑ k, ‖w k‖) + ‖c‖ with hL
  set R : ℝ := ‖a‖ + (|t| + 1) * ‖c‖ with hR
  have hL0 : 0 ≤ L := by
    have : 0 ≤ ∑ k, ‖w k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity
  have hXb : ∀ r σ, |X r σ| ≤ L * ‖σ‖ := fun r σ => by
    have h1 : |∑ k, deriv u ⟪v k + r • w k, σ⟫ * ⟪w k, σ⟫| ≤ D * (∑ k, ‖w k‖) * ‖σ‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (hD _) (abs_real_inner_le_norm _ _) (abs_nonneg _) hD0
    rw [hX, hL, add_mul]
    exact (abs_add_le _ _).trans (add_le_add h1 (abs_real_inner_le_norm _ _))
  have hconf : ∀ r ∈ Metric.ball t 1, ∀ σ : E, e r σ ≤ R * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun r hr σ => by
    have hr' : |r| ≤ |t| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hr
      have := abs_sub_abs_le_abs_sub r t
      linarith
    have h1 : ∑ k, u ⟪v k + r • w k, σ⟫ ≤ 0 := Finset.sum_nonpos fun k _ => hu0 _
    have h2 : ⟪a + r • c, σ⟫ ≤ R * ‖σ‖ := by
      refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hr' (norm_nonneg _)
    simp only [he]
    linarith
  set b : E → ℝ := fun σ => (1 + C) * Real.exp ((R + L + 2) ^ 2 / (2 * κ)) *
    Real.exp (-(κ / 2) * ‖σ‖ ^ 2) with hb
  have hbi : Integrable b := by
    have := integrable_exp_neg_mul_sq_norm_add_inner (E := E) (half_pos hκ) 0
    simp only [inner_zero_left, add_zero] at this
    exact this.const_mul _
  have hder : ∀ (σ : E) (r : ℝ), HasDerivAt (fun q => e q σ) (X r σ) r := fun σ r => by
    have hlin : ∀ x y : E, HasDerivAt (fun q : ℝ => ⟪x + q • y, σ⟫) ⟪y, σ⟫ r := fun x y => by
      have e : (fun q : ℝ => ⟪x + q • y, σ⟫) = fun q => ⟪x, σ⟫ + q * ⟪y, σ⟫ := by
        funext q
        rw [inner_add_left, real_inner_smul_left]
      rw [e]
      simpa using ((hasDerivAt_id r).mul_const ⟪y, σ⟫).const_add ⟪x, σ⟫
    have hsum : HasDerivAt (fun q => ∑ k, u ⟪v k + q • w k, σ⟫)
        (∑ k, deriv u ⟪v k + r • w k, σ⟫ * ⟪w k, σ⟫) r :=
      HasDerivAt.fun_sum fun k _ => (hu _).hasDerivAt.comp r (hlin (v k) (w k))
    exact (hsum.sub_const (κ * ‖σ‖ ^ 2)).add (hlin a c)
  have hem : ∀ r, Measurable (e r) := fun r => by
    refine Measurable.add (Measurable.sub ?_ (by fun_prop)) (by fun_prop)
    exact Finset.measurable_sum _ fun k _ => hum.comp (by fun_prop)
  have hXm : Measurable (X t) := by
    refine Measurable.add (Finset.measurable_sum _ fun k _ => ?_) (by fun_prop)
    exact ((measurable_deriv u).comp (by fun_prop : Measurable fun σ : E =>
      ⟪v k + t • w k, σ⟫)).mul (by fun_prop)
  refine hasDerivAt_integral_tilted_of_envelope (μ := volume) (s := Metric.ball t 1) (e := e)
    (e' := X) (Metric.ball_mem_nhds t one_pos) (fun r _ => hem r) hXm hF hbi
    (fun r hr σ => ?_) (fun σ r _ => hder σ r)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, ‖σ‖ = s := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ norm_nonneg _
  have h1 : 1 + |F σ| ≤ (1 + C) * Real.exp (2 * s) := by
    have h2 : 1 + s ^ 2 ≤ Real.exp (2 * s) := by
      have := Real.quadratic_le_exp_of_nonneg (mul_nonneg zero_le_two hs0)
      nlinarith
    have h3 : 1 + |F σ| ≤ (1 + C) * (1 + s ^ 2) := by
      have := hFb σ
      rw [hs] at this
      nlinarith [sq_nonneg s]
    exact h3.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  have h4 : 1 + |X r σ| ≤ Real.exp (L * s) :=
    hs ▸ (add_le_add le_rfl (hXb r σ)).trans ((add_comm _ _).trans_le (Real.add_one_le_exp _))
  have h5 : e r σ ≤ R * s - κ * s ^ 2 := hs ▸ hconf r hr σ
  refine (mul_le_mul (mul_le_mul h1 h4 (by positivity) (by positivity))
    (Real.exp_le_exp.2 h5) (Real.exp_pos _).le (by positivity)).trans ?_
  rw [hb]
  simp only
  rw [hs, mul_assoc (1 + C), mul_assoc (1 + C), mul_assoc (1 + C), ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith)
  have hsq : (R + L + 2) * s ≤ (R + L + 2) ^ 2 / (2 * κ) + κ / 2 * s ^ 2 := by
    have h0 : 0 ≤ (κ * s - (R + L + 2)) ^ 2 / (2 * κ) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have e : (κ * s - (R + L + 2)) ^ 2 / (2 * κ) =
        (R + L + 2) ^ 2 / (2 * κ) + κ / 2 * s ^ 2 - (R + L + 2) * s := by
      field_simp
      ring
    linarith
  nlinarith

end RidgePotential
