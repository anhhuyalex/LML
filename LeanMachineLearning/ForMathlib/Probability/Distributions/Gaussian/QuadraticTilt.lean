/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import LeanMachineLearning.ForMathlib.Probability.StdGaussianRadial

/-!
# Densities with a quadratic confinement

Integrals against `exp (-b ‖v‖² + ⟪a, v⟫)` on a finite-dimensional real inner product space.

## Main declarations

* `integrable_exp_neg_mul_sq_norm_add_inner`, `integral_exp_neg_mul_sq_norm_add_inner`:
  the Gaussian integral with a linear term.
* `integral_mul_exp_neg_mul_sq_norm`: the weight `exp (-b ‖v‖²)` is a rescaled standard Gaussian.
* `integral_abs_inner_stdGaussian_le`: `𝔼 |⟪a, z⟫| ≤ ‖a‖`.
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
