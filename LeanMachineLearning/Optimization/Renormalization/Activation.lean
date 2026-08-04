/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Real.Sign
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Activation functions for neural networks

This file gives one shared definition of the scalar activations used in the neural-network chapter.
The definitions are independent of any particular network representation.  In particular, the
threshold activation is only claimed to be measurable: it is discontinuous at the origin.

The GELU is defined as `x * Φ(x)` using Mathlib's standard-normal CDF.  The pinned Mathlib revision
does not define `Real.erf`, so an error-function formula is not used as a definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter

open scoped NNReal

namespace NeuralNetwork

/-- The threshold (Heaviside) activation, with value one at the origin. -/
noncomputable abbrev threshold (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

/-- The logistic activation `x ↦ 1 / (1 + exp (-x))`. -/
def logistic (x : ℝ) : ℝ := (1 + Real.exp (-x))⁻¹

/-- The rectified linear unit. -/
noncomputable abbrev relu (x : ℝ) : ℝ := max x 0

/-- A scalar linear activation with slope `a`. -/
def linear (a x : ℝ) : ℝ := a * x

/-- Leaky ReLU with negative-side slope `a`. -/
def leakyRelu (a x : ℝ) : ℝ := if 0 ≤ x then x else a * x

/-- The softplus activation. -/
def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

/-- The SWISH activation. -/
def swish (x : ℝ) : ℝ := x * logistic x

/-- The standard-normal CDF. -/
def standardNormalCDF : ℝ → ℝ := ProbabilityTheory.cdf (gaussianReal 0 1)

/-- The exact Gaussian error linear unit, `x ↦ x Φ(x)`. -/
def gelu (x : ℝ) : ℝ := x * standardNormalCDF x

/-- The signed version of the historical perceptron activation mentioned in the source footnote. -/
noncomputable def signedThreshold (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- The real error function, defined exactly by the integral displayed in Chapter 2. -/
def gaussianErf (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- The exponential Taylor expansion used in the chapter's function-approximation introduction. -/
theorem exp_eq_tsum_div_factorial (x : ℝ) :
    Real.exp x = ∑' k : ℕ, x ^ k / Nat.factorial k := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

@[simp] theorem signedThreshold_of_nonneg {x : ℝ} (hx : 0 ≤ x) : signedThreshold x = 1 := by
  simp [signedThreshold, hx]

@[simp] theorem signedThreshold_of_neg {x : ℝ} (hx : x < 0) : signedThreshold x = -1 := by
  simp [signedThreshold, not_le.mpr hx]

/-- The source's alternative perceptron is the sign function away from the convention-sensitive
origin. -/
theorem signedThreshold_eq_sign {x : ℝ} (hx : x ≠ 0) : signedThreshold x = Real.sign x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [signedThreshold_of_neg hx, Real.sign_of_neg hx]
  · rw [signedThreshold_of_nonneg hx.le, Real.sign_of_pos hx]

lemma measurable_threshold : Measurable threshold := by
  unfold threshold
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma threshold_nonneg (x : ℝ) : 0 ≤ threshold x := by
  simp only [threshold]
  split_ifs <;> norm_num

lemma threshold_le_one (x : ℝ) : threshold x ≤ 1 := by
  simp only [threshold]
  split_ifs <;> norm_num

@[simp] lemma threshold_of_nonneg {x : ℝ} (hx : 0 ≤ x) : threshold x = 1 := by
  simp [threshold, hx]

@[simp] lemma threshold_of_neg {x : ℝ} (hx : x < 0) : threshold x = 0 := by
  simp [threshold, not_le.mpr hx]

/-- The threshold activation is discontinuous at the origin.

Informal proof: `threshold 0 = 1`, whereas `threshold (-1 / (n+1)) = 0` and the latter inputs
converge to zero.  Continuity would force their outputs to converge to one, contradicting the
constant-zero limit.  See
<https://en.wikipedia.org/wiki/Heaviside_step_function#Analytic_approximations>. -/
theorem not_continuousAt_threshold_zero : ¬ ContinuousAt threshold 0 := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hclose⟩ := h (1 / 2 : ℝ) (by norm_num)
  have hx : dist (-δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq]
    rw [sub_zero, show -δ / 2 = -(δ / 2) by ring, abs_neg,
      abs_of_nonneg (div_nonneg hδ.le (by norm_num))]
    linarith
  have hout := hclose hx
  have hxneg : -δ / 2 < 0 := by linarith
  rw [threshold_of_neg hxneg, threshold_of_nonneg (le_refl 0)] at hout
  norm_num [Real.dist_eq] at hout

lemma continuous_logistic : Continuous logistic := by
  unfold logistic
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

lemma measurable_logistic : Measurable logistic := continuous_logistic.measurable

lemma logistic_pos (x : ℝ) : 0 < logistic x := by
  simp only [logistic]
  positivity

lemma logistic_lt_one (x : ℝ) : logistic x < 1 := by
  unfold logistic
  apply inv_lt_one_of_one_lt₀
  linarith [Real.exp_pos (-x)]

lemma continuous_relu : Continuous relu := by
  unfold relu
  fun_prop

lemma measurable_relu : Measurable relu := continuous_relu.measurable

lemma continuous_linear (a : ℝ) : Continuous (linear a) := by
  unfold linear
  fun_prop

lemma measurable_linear (a : ℝ) : Measurable (linear a) := (continuous_linear a).measurable

lemma continuous_leakyRelu (a : ℝ) : Continuous (leakyRelu a) := by
  unfold leakyRelu
  apply continuous_if_le (f := fun _ : ℝ => 0) (g := id)
      continuous_const continuous_id continuous_id.continuousOn
      (continuous_const.mul continuous_id).continuousOn
  intro x hx
  change 0 = x at hx
  change x = a * x
  rw [← hx]
  simp

lemma measurable_leakyRelu (a : ℝ) : Measurable (leakyRelu a) :=
  (continuous_leakyRelu a).measurable

lemma continuous_softplus : Continuous softplus := by
  unfold softplus
  exact Continuous.log (by fun_prop) (fun x => by positivity)

lemma measurable_softplus : Measurable softplus := continuous_softplus.measurable

lemma continuous_swish : Continuous swish := by
  unfold swish
  exact continuous_id.mul continuous_logistic

lemma measurable_swish : Measurable swish := continuous_swish.measurable

lemma measurable_standardNormalCDF : Measurable standardNormalCDF := by
  exact (ProbabilityTheory.monotone_cdf (gaussianReal 0 1)).measurable

lemma measurable_gelu : Measurable gelu := by
  unfold gelu
  exact measurable_id.mul measurable_standardNormalCDF

theorem tendsto_standardNormalCDF_atTop : Tendsto standardNormalCDF atTop (nhds 1) :=
  ProbabilityTheory.tendsto_cdf_atTop _

theorem tendsto_standardNormalCDF_atBot : Tendsto standardNormalCDF atBot (nhds 0) :=
  ProbabilityTheory.tendsto_cdf_atBot _

lemma continuous_tanhActivation : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
    funext x
    exact Real.tanh_eq_sinh_div_cosh x]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

lemma measurable_tanhActivation : Measurable Real.tanh := continuous_tanhActivation.measurable

lemma continuous_sinActivation : Continuous Real.sin := Real.continuous_sin

lemma measurable_sinActivation : Measurable Real.sin := Real.continuous_sin.measurable

theorem tanhActivation_zero : Real.tanh 0 = 0 := Real.tanh_zero

theorem sinActivation_zero : Real.sin 0 = 0 := Real.sin_zero

theorem sinActivation_periodic : Function.Periodic Real.sin (2 * Real.pi) := Real.sin_periodic

@[simp] theorem logistic_zero : logistic 0 = 1 / 2 := by
  norm_num [logistic]

@[simp] theorem softplus_zero : softplus 0 = Real.log 2 := by
  unfold softplus
  congr 1
  norm_num

@[simp] theorem swish_zero : swish 0 = 0 := by
  simp [swish]

@[simp] theorem gelu_zero : gelu 0 = 0 := by
  simp [gelu]

/-- The first exact exponential formula for `tanh` displayed in Chapter 2. -/
theorem tanh_eq_exp_div (x : ℝ) :
    Real.tanh x = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) :=
  Real.tanh_eq x

/-- The second exact exponential formula for `tanh` displayed in Chapter 2.

Informal proof: start from `tanh_eq_exp_div`, multiply numerator and denominator by `exp x`, and
use `exp x * exp x = exp (2*x)` and `exp (-x) * exp x = 1`.  See
<https://en.wikipedia.org/wiki/Hyperbolic_functions#Exponential_definitions>. -/
-- Clearing the inverse in a `tanh`-style quotient: for `a ≠ 0`, the quotient
-- `(a - a⁻¹) / (a + a⁻¹)` equals the single-square form `(a * a - 1) / (a * a + 1)`.
-- This is the algebraic core of `tanh_eq_exp_two_mul`, independent of `exp`.
private lemma div_sub_inv_eq (a : ℝ) (ha : a ≠ 0) :
    (a - a⁻¹) / (a + a⁻¹) = (a * a - 1) / (a * a + 1) := by
  field_simp [ha]

-- Doubling the argument of the real exponential: `exp (2 * x) = exp x * exp x`.
-- This notation conversion is used in `tanh_eq_exp_two_mul` to turn the
-- double-angle exponential into a square of `exp x`.
private lemma exp_two_mul (x : ℝ) : Real.exp (2 * x) = Real.exp x * Real.exp x := by
  rw [two_mul, Real.exp_add]

theorem tanh_eq_exp_two_mul (x : ℝ) :
    Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq, Real.exp_neg, exp_two_mul,
    div_sub_inv_eq (Real.exp x) (Real.exp_ne_zero x)]

-- Specializing `tanh_eq_exp_two_mul` to the half-argument: `tanh (x / 2)` is the
-- single-exponential quotient `(exp x - 1) / (exp x + 1)`.  This is the exponential
-- quotient substituted into the logistic/tanh identity below.
private lemma tanh_half_eq (x : ℝ) :
    Real.tanh (x / 2) = (Real.exp x - 1) / (Real.exp x + 1) := by
  rw [tanh_eq_exp_two_mul, show 2 * (x / 2) = x by ring]

-- Algebraic core of the logistic/tanh identity: for `a ≠ 0` with `a + 1 ≠ 0`, the
-- reciprocal `(1 + a⁻¹)⁻¹` equals `1 / 2 + 1 / 2 * ((a - 1) / (a + 1))`.  This is the
-- denominator-clearing step of `logistic_eq_half_add_half_tanh`, independent of `exp`
-- (compare `div_sub_inv_eq` above).
private lemma inv_add_one_eq_half_add_half (a : ℝ) (ha : a ≠ 0) (ha1 : a + 1 ≠ 0) :
    (1 + a⁻¹)⁻¹ = 1 / 2 + 1 / 2 * ((a - 1) / (a + 1)) := by
  field_simp [ha, ha1]
  ring

/-- The logistic/tanh identity in the source.

Informal proof: substitute the exponential quotient for `tanh (x / 2)`, multiply numerator and
denominator by `exp (x / 2)`, and use `exp (x / 2)^2 = exp x`.  This is the standard identity
recorded, for example, at
<https://en.wikipedia.org/wiki/Logistic_function#Mathematical_properties>. -/
theorem logistic_eq_half_add_half_tanh (x : ℝ) :
    logistic x = 1 / 2 + 1 / 2 * Real.tanh (x / 2) := by
  rw [logistic, tanh_half_eq, Real.exp_neg,
    inv_add_one_eq_half_add_half (Real.exp x) (Real.exp_ne_zero x) (by positivity)]

-- The standard-normal density integrates to `1 / 2` on the non-positive half-line.  The density
-- is even and its total mass is one, so the two half-lines carry equal mass.
private lemma standardGaussianIntegral_Iic_zero :
    (∫ t in Set.Iic (0 : ℝ), gaussianPDFReal 0 1 t) = 1 / 2 := by
  have hsplit : (∫ t in Set.Iic 0, gaussianPDFReal 0 1 t) +
      (∫ t in Set.Ioi 0, gaussianPDFReal 0 1 t) = 1 := by
    rw [intervalIntegral.integral_Iic_add_Ioi (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn]
    exact integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hhalf : (∫ t in Set.Ioi 0, gaussianPDFReal 0 1 t) =
      ∫ t in Set.Iic 0, gaussianPDFReal 0 1 t := by
    rw [setIntegral_congr_fun (g := fun t => gaussianPDFReal 0 1 (-t)) measurableSet_Ioi
      (fun t _ => by simp [gaussianPDFReal])]
    simp
  linarith

/-- Split the standard-normal CDF at the origin.

Informal proof: unfold `standardNormalCDF` as `cdf (gaussianReal 0 1)` and use
`ProbabilityTheory.cdf_eq_real` together with
`ProbabilityTheory.gaussianReal_apply_eq_integral` to rewrite it as the integral of
`gaussianPDFReal 0 1` over `Set.Iic x`.  The Gaussian density is even, and the total mass is one,
so the integral over `(-∞,0]` is `1/2`.  Splitting `Set.Iic x` at `0` (with a case split on
`x ≤ 0`/`0 ≤ x` and using `intervalIntegral.integral_symm` for the negative case) gives the
oriented interval-integral formula below.  This is the first half of the standard identity recorded
at <https://en.wikipedia.org/wiki/Normal_distribution#Cumulative_distribution_function>. -/
private lemma standardNormalCDF_eq_half_add_standardGaussianIntegral (x : ℝ) :
    standardNormalCDF x = 1 / 2 + ∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t := by
  have hIic : standardNormalCDF x = ∫ t in Set.Iic x, gaussianPDFReal 0 1 t := by
    rw [standardNormalCDF, ProbabilityTheory.cdf_eq_real, measureReal_def,
      gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (Set.Iic x),
      ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Iic (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  have hsplit : (∫ t in Set.Iic x, gaussianPDFReal 0 1 t) =
      (∫ t in Set.Iic 0, gaussianPDFReal 0 1 t) + ∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t := by
    rw [← intervalIntegral.integral_Iic_sub_Iic (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn]
    ring
  rw [hIic, hsplit, standardGaussianIntegral_Iic_zero]

/-- The oriented integral of the standard-normal density from `0` to `x` is half of `gaussianErf`.

Informal proof: unfold `gaussianPDFReal 0 1` and `gaussianErf`.  In the integral
`∫ t in 0..x, (√(2π))⁻¹ * exp (-t^2/2)`, make the linear change of variables
`t = √2 * u`, equivalently `u = t / √2`, using
`intervalIntegral.smul_integral_comp_mul_left`.  Since `(√2 * u)^2 / 2 = u^2` and
`√2 / √(2π) = 1 / √π`, the transformed integral is
`(1 / √π) * ∫ u in 0..x/√2, exp (-u^2)`, which is exactly
`1/2 * gaussianErf (x/√2)`.  The interval integral is oriented, so the same calculation covers
negative `x`.  See also ProofWiki's derivation:
<https://proofwiki.org/wiki/Normal_Distribution_CDF_in_terms_of_Gauss_Error_Function>. -/
private lemma standardGaussianIntegral_eq_half_gaussianErf (x : ℝ) :
    (∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t) =
      1 / 2 * gaussianErf (x / Real.sqrt 2) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)
  have hsqrtpi : Real.sqrt π ≠ 0 := Real.sqrt_ne_zero'.2 Real.pi_pos
  have hpdf : ∀ u : ℝ, gaussianPDFReal 0 1 (Real.sqrt 2 * u) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-u ^ 2) := by
    intro u
    calc
      gaussianPDFReal 0 1 (Real.sqrt 2 * u) =
          (Real.sqrt (2 * π))⁻¹ * Real.exp (-(Real.sqrt 2 * u) ^ 2 / 2) := by
        simp [gaussianPDFReal]
      _ = (Real.sqrt (2 * π))⁻¹ * Real.exp (-u ^ 2) := by
        congr
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
  calc
    (∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t)
        = Real.sqrt 2 * ∫ u in (0 : ℝ)..(x / Real.sqrt 2),
            gaussianPDFReal 0 1 (Real.sqrt 2 * u) := by
          rw [← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_left (c := Real.sqrt 2)]
          congr 1
          · norm_num
          · rw [mul_comm, div_mul_cancel₀ x hsqrt]
    _ = Real.sqrt 2 * ∫ u in (0 : ℝ)..(x / Real.sqrt 2),
          (Real.sqrt (2 * π))⁻¹ * Real.exp (-u ^ 2) := by
          simp_rw [hpdf]
    _ = (Real.sqrt π)⁻¹ * ∫ u in (0 : ℝ)..(x / Real.sqrt 2), Real.exp (-u ^ 2) := by
          rw [intervalIntegral.integral_const_mul, ← mul_assoc,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) π]
          field_simp [hsqrt, hsqrtpi]
    _ = 1 / 2 * gaussianErf (x / Real.sqrt 2) := by
          rw [gaussianErf]
          field_simp [hsqrtpi]

/-- The CDF definition of GELU agrees with the error-function display in the source.

Informal proof: substitute `u = t / sqrt 2` in the standard-normal density integral.  The integral
from `-∞` to zero contributes `1/2`, and the remaining integral is one half of `gaussianErf`.
See the standard normal CDF/error-function identity at
<https://en.wikipedia.org/wiki/Normal_distribution#Cumulative_distribution_function>. -/
theorem standardNormalCDF_eq_erf (x : ℝ) :
    standardNormalCDF x = 1 / 2 + 1 / 2 * gaussianErf (x / Real.sqrt 2) := by
  rw [standardNormalCDF_eq_half_add_standardGaussianIntegral,
    standardGaussianIntegral_eq_half_gaussianErf]

theorem gelu_eq_erf (x : ℝ) :
    gelu x = (1 / 2 + 1 / 2 * gaussianErf (x / Real.sqrt 2)) * x := by
  rw [gelu, standardNormalCDF_eq_erf]
  ring

/-- The logistic activation is smooth. -/
theorem contDiff_logistic : ContDiff ℝ ⊤ logistic := by
  unfold logistic
  apply ContDiff.inv (f := fun x => 1 + Real.exp (-x))
  · fun_prop
  · intro x
    positivity

/-- `tanh` is smooth.

Informal proof: `sinh` and `cosh` are smooth and `cosh` is nowhere zero.  See
<https://en.wikipedia.org/wiki/Hyperbolic_functions#Derivatives>. -/
theorem contDiff_tanhActivation : ContDiff ℝ ⊤ Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
    funext x
    exact Real.tanh_eq_sinh_div_cosh x]
  exact Real.contDiff_sinh.div Real.contDiff_cosh fun x => (Real.cosh_pos x).ne'

/-- `sin` is smooth. -/
theorem contDiff_sinActivation : ContDiff ℝ ⊤ Real.sin := Real.contDiff_sin

/-- Softplus is smooth. -/
theorem contDiff_softplus : ContDiff ℝ ⊤ softplus := by
  unfold softplus
  exact (contDiff_const.add (Real.contDiff_exp)).log (fun x => by positivity)

/-- SWISH is smooth. -/
theorem contDiff_swish : ContDiff ℝ ⊤ swish := by
  unfold swish
  exact contDiff_id.mul contDiff_logistic

-- The Taylor coefficients of the odd power series for `gaussianErf`: the term of degree
-- `2*n + 1` is `(-1)^n / (n! * (2*n + 1))`.  These are the coefficients obtained by
-- integrating the Maclaurin series of `exp (-t^2)` term by term.
private def erfSeriesCoeff (n : ℕ) : ℝ := (-1 : ℝ) ^ n / (Nat.factorial n * (2 * n + 1))

-- `exp (-t^2)` expands as the alternating Maclaurin series `∑ n, (-1)^n * t^(2*n) / n!`.
-- This is `exp_eq_tsum_div_factorial` specialized to `z = -t^2`.
private lemma exp_neg_sq_tsum (t : ℝ) :
    Real.exp (-(t ^ 2)) = ∑' n : ℕ, (-1 : ℝ) ^ n * t ^ (2 * n) / Nat.factorial n := by
  rw [exp_eq_tsum_div_factorial]
  refine tsum_congr ?_
  intro n
  have hpow : (-(t ^ 2)) ^ n = (-1 : ℝ) ^ n * t ^ (2 * n) := by
    calc
      (-(t ^ 2)) ^ n = ((-1 : ℝ) * t ^ 2) ^ n := by ring
      _ = (-1 : ℝ) ^ n * (t ^ 2) ^ n := by rw [mul_pow]
      _ = (-1 : ℝ) ^ n * t ^ (2 * n) := by rw [pow_mul]
  rw [hpow]
  ring

-- The integral over `[0, x]` of the Maclaurin series of `exp (-t^2)` equals the termwise
-- integral.  Each monomial `t^(2*n)` integrates to `x^(2*n+1) / (2*n+1)`, giving the odd power
-- series `∑ n, erfSeriesCoeff n * x^(2*n+1)`.  Termwise integration is justified by the
-- dominated convergence theorem via `tsum_intervalIntegral_eq_of_summable_norm`; the required
-- summability of the sup norms on `uIcc 0 x` follows from the bound `‖term n‖ ≤ x^(2*n) / n!`
-- and the convergence of `∑ x^(2*n) / n!` (a subseries of the exponential series).
private lemma gaussianIntegral_eq_tsum (x : ℝ) :
    (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))) =
      ∑' n : ℕ, erfSeriesCoeff n * x ^ (2 * n + 1) := by
  let f : ℕ → C(ℝ, ℝ) := fun n => ⟨fun t => (-1 : ℝ) ^ n * t ^ (2 * n) / Nat.factorial n, by
    fun_prop⟩
  have hf_sum :
      Summable fun n => ‖(f n).restrict (⟨uIcc 0 x, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    refine Summable.of_norm_bounded (fun n => x ^ (2 * n) / Nat.factorial n) ?_ ?_
    · simpa [pow_mul] using (Real.summable_pow_div_factorial (x ^ 2) :
        Summable fun n : ℕ => (x ^ 2) ^ n / Nat.factorial n)
    · intro n
      rw [ContinuousMap.norm_le]
      · intro t
        have ht_le : |(t : ℝ)| ≤ |x| := by
          rcases Set.mem_uIcc.mp t.property with h | h
          · rw [abs_of_nonneg h.1]
            exact h.2.trans (le_abs_self x)
          · rw [abs_of_nonpos h.2]
            have hx : |x| = -x := abs_of_nonpos (h.1.trans h.2)
            rw [hx]
            linarith
        have hxpow : |x| ^ (2 * n) = x ^ (2 * n) := by
          calc
            |x| ^ (2 * n) = (|x| ^ 2) ^ n := by rw [← pow_mul]
            _ = (x ^ 2) ^ n := by rw [sq_abs]
            _ = x ^ (2 * n) := by rw [pow_mul]
        calc
          ‖(f n) t‖ = |(-1 : ℝ) ^ n * (t : ℝ) ^ (2 * n) / Nat.factorial n| := rfl
          _ = |(-1 : ℝ) ^ n * (t : ℝ) ^ (2 * n)| / Nat.factorial n := by
            rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
          _ = |(t : ℝ)| ^ (2 * n) / Nat.factorial n := by
            have hmul : |(-1 : ℝ) ^ n * (t : ℝ) ^ (2 * n)| = |(t : ℝ)| ^ (2 * n) := by
              rw [abs_mul, abs_pow, abs_pow]
              norm_num
            rw [hmul]
          _ ≤ x ^ (2 * n) / Nat.factorial n := by
            exact div_le_div_of_nonneg_right
              ((pow_le_pow_left₀ (abs_nonneg (t : ℝ)) ht_le (2 * n)).trans (le_of_eq hxpow))
              (Nat.cast_nonneg _)
      · positivity
  have htsum : ∑' n : ℕ, ∫ t in (0 : ℝ)..x, f n t = ∫ t in (0 : ℝ)..x, ∑' n, f n t :=
    tsum_intervalIntegral_eq_of_summable_norm hf_sum
  have hpoint : ∀ t : ℝ, (∑' n : ℕ, f n t) = Real.exp (-(t ^ 2)) := by
    intro t
    exact (exp_neg_sq_tsum t).symm
  have hterm : ∀ n : ℕ, (∫ t in (0 : ℝ)..x, f n t) =
      erfSeriesCoeff n * x ^ (2 * n + 1) := by
    intro n
    calc
      (∫ t in (0 : ℝ)..x, f n t) = ∫ t in (0 : ℝ)..x, ((-1 : ℝ) ^ n / Nat.factorial n) * t ^ (2 * n) := by
        congr 1
        funext t
        field_simp [Nat.factorial_ne_zero n]
        ring
      _ = ((-1 : ℝ) ^ n / Nat.factorial n) * ∫ t in (0 : ℝ)..x, t ^ (2 * n) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ((-1 : ℝ) ^ n / Nat.factorial n) * (x ^ (2 * n + 1) - 0 ^ (2 * n + 1)) / (2 * n + 1) := by
        rw [integral_pow]
      _ = erfSeriesCoeff n * x ^ (2 * n + 1) := by
        simp [erfSeriesCoeff]
        ring
  calc
    (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))) = ∫ t in (0 : ℝ)..x, ∑' n, f n t := by
      congr 1
      funext t
      exact (hpoint t).symm
    _ = ∑' n : ℕ, ∫ t in (0 : ℝ)..x, f n t := htsum.symm
    _ = ∑' n : ℕ, erfSeriesCoeff n * x ^ (2 * n + 1) := by
      exact tsum_congr fun n => hterm n

-- The coefficients decay like `1 / n!`, which is exactly what is needed for the comparison test
-- below: `‖erfSeriesCoeff n‖ = 1 / (n! * (2*n + 1)) ≤ 1 / n!`.
private lemma erfSeriesCoeff_norm_le (n : ℕ) : ‖erfSeriesCoeff n‖ ≤ 1 / Nat.factorial n := by
  unfold erfSeriesCoeff
  rw [norm_div]
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hodd : (2 * n + 1 : ℝ) ≠ 0 := by norm_num
  simp [hfac, hodd]
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.le_factorial_self n)

-- The odd power series for `gaussianErf` has infinite radius of convergence: bounding the terms
-- by `x^n / n!` reduces the comparison test to the everywhere-convergent exponential series.
private lemma erfSeries_radius_top : (ofScalars ℝ erfSeriesCoeff).radius = ⊤ := by
  apply (ofScalars ℝ erfSeriesCoeff).radius_eq_top_of_summable_norm
  intro r
  refine Summable.of_norm_bounded (fun n => (r : ℝ) ^ n / Nat.factorial n) ?_ ?_
  · simpa using (Real.summable_pow_div_factorial (r : ℝ) :
      Summable fun n : ℕ => (r : ℝ) ^ n / Nat.factorial n)
  · intro n
    calc
      ‖ofScalars ℝ erfSeriesCoeff n‖ * (r : ℝ) ^ n = ‖erfSeriesCoeff n‖ * (r : ℝ) ^ n := by
        rw [ofScalars_norm]
      _ ≤ (1 / Nat.factorial n) * (r : ℝ) ^ n := by
        exact mul_le_mul_of_nonneg_right (erfSeriesCoeff_norm_le n) (pow_nonneg (NNReal.coe_nonneg r) n)
      _ = (r : ℝ) ^ n / Nat.factorial n := by ring

-- A power series with infinite radius of convergence is analytic on all of `ℝ`: it admits
-- `HasFPowerSeriesOnBall` on the whole line, and change of origin gives analyticity at every point.
private lemma ofScalarsSum_erfSeries_analyticOnNhd :
    AnalyticOnNhd ℝ (ofScalarsSum ℝ erfSeriesCoeff) Set.univ := by
  have hpos : 0 < (ofScalars ℝ erfSeriesCoeff).radius := by
    rw [erfSeries_radius_top]
    exact ENNReal.top_pos
  have hfps : HasFPowerSeriesOnBall (ofScalarsSum ℝ erfSeriesCoeff) (ofScalars ℝ erfSeriesCoeff) 0
      (ofScalars ℝ erfSeriesCoeff).radius := by
    exact (ofScalars ℝ erfSeriesCoeff).hasFPowerSeriesOnBall hpos
  intro x hx
  exact hfps.analyticAt_of_mem (by simp)

-- The termwise-integrated series is exactly `x * ∑ n, erfSeriesCoeff n * (x^2)^n`, i.e. the
-- product of `x` with the `ofScalarsSum` series evaluated at `x^2`.  This is the analytic
-- expression of `gaussianErf` used below.
private lemma gaussianErf_eq_mul_ofScalarsSum (x : ℝ) :
    gaussianErf x = (2 / Real.sqrt Real.pi) * (x * ofScalarsSum ℝ erfSeriesCoeff (x ^ 2)) := by
  have hint := gaussianIntegral_eq_tsum x
  have hsum : (∑' n : ℕ, erfSeriesCoeff n * x ^ (2 * n + 1)) =
      x * ofScalarsSum ℝ erfSeriesCoeff (x ^ 2) := by
    calc
      (∑' n : ℕ, erfSeriesCoeff n * x ^ (2 * n + 1))
          = ∑' n : ℕ, x * (erfSeriesCoeff n * x ^ (2 * n)) := by
            refine tsum_congr ?_
            intro n
            rw [show 2 * n + 1 = (2 * n) + 1 by omega, pow_succ]
            ring
      _ = x * ∑' n : ℕ, erfSeriesCoeff n * x ^ (2 * n) := by
            rw [tsum_mul_left]
      _ = x * ofScalarsSum ℝ erfSeriesCoeff (x ^ 2) := by
            congr 1
            rw [ofScalars_sum_eq]
            refine tsum_congr ?_
            intro n
            simp [pow_mul]
  calc
    gaussianErf x = (2 / Real.sqrt Real.pi) * (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))) := rfl
    _ = (2 / Real.sqrt Real.pi) * (∑' n : ℕ, erfSeriesCoeff n * x ^ (2 * n + 1)) := by
      rw [hint]
    _ = (2 / Real.sqrt Real.pi) * (x * ofScalarsSum ℝ erfSeriesCoeff (x ^ 2)) := by
      rw [hsum]

/-- The real error function is analytic on all of `ℝ`.

Informal proof: expand `exp (-t^2)` into its everywhere-convergent Maclaurin series
`∑ n, (-1)^n * t^(2*n) / n!`, integrate term-by-term on each compact interval, and obtain
`gaussianErf x = (2 / √π) * ∑ n, (-1)^n * x^(2*n+1) / (n! * (2*n+1))`.  The ratio test gives
infinite radius of convergence, so this power series defines an analytic function on every
neighborhood.  This is the standard Taylor-series proof that `erf` is entire; see, for example,
<https://en.wikipedia.org/wiki/Error_function#Taylor_series> and
<https://mathworld.wolfram.com/Erf.html>. -/
private lemma analyticOnNhd_gaussianErf : AnalyticOnNhd ℝ gaussianErf Set.univ := by
  -- Rewrite `gaussianErf` as the product of a constant with `x * g(x^2)` where `g` is the
  -- everywhere-convergent odd power series, then assemble analyticity from its pieces.
  have hsum_an : AnalyticOnNhd ℝ (ofScalarsSum ℝ erfSeriesCoeff) Set.univ :=
    ofScalarsSum_erfSeries_analyticOnNhd
  intro x hx
  have h1 : AnalyticAt ℝ (fun x : ℝ => x) x := analyticAt_id
  have h2 : AnalyticAt ℝ (fun x : ℝ => x ^ 2) x := by fun_prop
  have h3 : AnalyticAt ℝ (fun x : ℝ => ofScalarsSum ℝ erfSeriesCoeff (x ^ 2)) x := by
    simpa [Function.comp_def] using (hsum_an (x ^ 2) trivial).comp h2
  have h4 : AnalyticAt ℝ (fun x : ℝ => x * ofScalarsSum ℝ erfSeriesCoeff (x ^ 2)) x := h1.mul h3
  have h5 : AnalyticAt ℝ (fun x : ℝ =>
      (2 / Real.sqrt Real.pi) * (x * ofScalarsSum ℝ erfSeriesCoeff (x ^ 2))) x := by
    simpa using (analyticAt_const.mul h4)
  rw [show gaussianErf = fun x : ℝ =>
      (2 / Real.sqrt Real.pi) * (x * ofScalarsSum ℝ erfSeriesCoeff (x ^ 2)) by
    funext x
    exact gaussianErf_eq_mul_ofScalarsSum x]
  exact h5

/-- `gaussianErf` is smooth.

Informal proof: the previous lemma records the stronger fact that the error function is analytic
(on all of `ℝ`), and analytic functions are `C^n` for every differentiability order `n`, including
`⊤`. -/
theorem contDiff_gaussianErf : ContDiff ℝ ⊤ gaussianErf := by
  exact analyticOnNhd_gaussianErf.contDiff

/-- The standard-normal CDF is smooth.

Informal proof: transfer smoothness from `gaussianErf` along the identity
`standardNormalCDF_eq_erf`. -/
theorem contDiff_standardNormalCDF : ContDiff ℝ ⊤ standardNormalCDF := by
  have h : standardNormalCDF = fun x => 1 / 2 + 1 / 2 * gaussianErf (x / Real.sqrt 2) := by
    funext x
    exact standardNormalCDF_eq_erf x
  rw [h]
  exact contDiff_const.add (contDiff_const.mul (contDiff_gaussianErf.comp
    (contDiff_id.div_const _)))

/-- GELU is smooth. -/
theorem contDiff_gelu : ContDiff ℝ ⊤ gelu := by
  unfold gelu
  exact contDiff_id.mul contDiff_standardNormalCDF

theorem continuous_standardNormalCDF : Continuous standardNormalCDF :=
  contDiff_standardNormalCDF.continuous

theorem continuous_gelu : Continuous gelu := contDiff_gelu.continuous

/-- The source's statement that `tanh x ≈ x` near zero, made exact by its derivative.

Informal proof: differentiating `sinh x / cosh x` gives `1 / cosh x ^ 2`, which equals one at zero.
See <https://en.wikipedia.org/wiki/Hyperbolic_functions#Derivatives>. -/
theorem hasDerivAt_tanh_zero : HasDerivAt Real.tanh 1 0 := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
    funext x
    exact Real.tanh_eq_sinh_div_cosh x]
  refine (((Real.hasDerivAt_sinh 0).div (Real.hasDerivAt_cosh 0)
      (Real.cosh_pos 0).ne').congr_deriv ?_)
  norm_num [Real.sinh_zero, Real.cosh_zero]

/-- Logistic saturates to `1` at `+∞`.

Informal proof: divide the logistic expression by the dominant exponential. -/
theorem tendsto_logistic_atTop : Tendsto logistic atTop (nhds 1) := by
  unfold logistic
  have h : Tendsto (fun x => 1 + Real.exp (-x)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds (1 : ℝ))).add
      Real.tendsto_exp_neg_atTop_nhds_zero
  simpa using h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

/-- Logistic saturates to `0` at `-∞`.

Informal proof: divide the logistic expression by the dominant exponential. -/
theorem tendsto_logistic_atBot : Tendsto logistic atBot (nhds 0) := by
  have he : Tendsto (fun x => Real.exp x) atBot (nhds 0) := Real.tendsto_exp_atBot
  have hd : Tendsto (fun x => 1 + Real.exp x) atBot (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (nhds (1 : ℝ))).add he
  have h : Tendsto (fun x => Real.exp x / (1 + Real.exp x)) atBot (nhds 0) := by
    change Tendsto ((fun x => Real.exp x) / (fun x => 1 + Real.exp x)) atBot (nhds 0)
    simpa using he.div hd (by norm_num : (1 : ℝ) ≠ 0)
  have hlog : (fun x => logistic x) = fun x => Real.exp x / (1 + Real.exp x) := by
    funext x
    unfold logistic
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero x]
    ring
  simpa [hlog] using h

/-- `tanh` saturates to `1` at `+∞`.

Informal proof: divide the exponential expression for `tanh` by the dominant exponential.  See
<https://en.wikipedia.org/wiki/Hyperbolic_functions#Definitions>. -/
theorem tendsto_tanh_atTop : Tendsto Real.tanh atTop (nhds 1) := by
  have hz : Tendsto (fun x => (Real.exp (2 * x) + 1)⁻¹) atTop (nhds 0) := by
    have h : Tendsto (fun x => Real.exp (2 * x)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have h' : Tendsto (fun x => Real.exp (2 * x) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 h
    exact tendsto_inv_atTop_zero.comp h'
  have h : Tendsto (fun x => 1 - 2 * (Real.exp (2 * x) + 1)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hz.const_mul 2)
  have htanh : (fun x => Real.tanh x) = fun x => 1 - 2 * (Real.exp (2 * x) + 1)⁻¹ := by
    funext x
    rw [tanh_eq_exp_two_mul]
    field_simp
    ring
  simpa [htanh] using h

/-- `tanh` saturates to `-1` at `-∞`.

Informal proof: divide the exponential expression for `tanh` by the dominant exponential.  See
<https://en.wikipedia.org/wiki/Hyperbolic_functions#Definitions>. -/
theorem tendsto_tanh_atBot : Tendsto Real.tanh atBot (nhds (-1)) := by
  have he : Tendsto (fun x => Real.exp (2 * x)) atBot (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num : (0 : ℝ) < 2))
  have hd : Tendsto (fun x => Real.exp (2 * x) + 1) atBot (nhds 1) := by
    simpa using he.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (nhds (1 : ℝ)))
  have h : Tendsto (fun x => (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1)) atBot (nhds (-1)) :=
    by
    have hnum : Tendsto (fun x => Real.exp (2 * x) - 1) atBot (nhds (-1)) := by
      simpa using he.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (nhds (1 : ℝ)))
    change Tendsto ((fun x => Real.exp (2 * x) - 1) / (fun x => Real.exp (2 * x) + 1))
      atBot (nhds (-1))
    simpa using hnum.div hd (by norm_num : (1 : ℝ) ≠ 0)
  have htanh : (fun x => Real.tanh x) = fun x =>
      (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
    funext x
    exact tanh_eq_exp_two_mul x
  simpa [htanh] using h

/-- Softplus agrees with the identity to within a vanishing error at `+∞`.

Informal proof: `log (1 + exp x) - x = log (1 + exp (-x)) → log 1 = 0`.  See
<https://en.wikipedia.org/wiki/Softplus>. -/
theorem tendsto_softplus_sub_id_atTop : Tendsto (fun x => softplus x - x) atTop (nhds 0) := by
  have h : (fun x => softplus x - x) = fun x => Real.log (1 + Real.exp (-x)) := by
    funext x
    unfold softplus
    calc
      Real.log (1 + Real.exp x) - x = Real.log (1 + Real.exp x) - Real.log (Real.exp x) := by
        rw [Real.log_exp x]
      _ = Real.log ((1 + Real.exp x) / Real.exp x) := by
        rw [← Real.log_div (by positivity : (1 + Real.exp x) ≠ 0) (Real.exp_ne_zero x)]
      _ = Real.log (1 + Real.exp (-x)) := by
        congr 1
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero x]
        ring
  rw [h]
  have hz : Tendsto (fun x => 1 + Real.exp (-x)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds (1 : ℝ))).add
      Real.tendsto_exp_neg_atTop_nhds_zero
  have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
  simpa [Function.comp_def, Real.log_one] using hc.tendsto.comp hz

/-- Softplus matches the dominant exponential at `-∞`.

Informal proof: `log (1 + exp x) / exp x → 1` using `log (1 + y) / y → 1` as `y → 0`. See
<https://en.wikipedia.org/wiki/Softplus>. -/
theorem tendsto_softplus_div_exp_atBot :
    Tendsto (fun x => softplus x / Real.exp x) atBot (nhds 1) := by
  have hslope : Tendsto (fun y : ℝ => Real.log (1 + y) / y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hd : HasDerivAt Real.log (1 : ℝ) 1 := by
      simpa using Real.hasDerivAt_log (x := 1) one_ne_zero
    have hzero := hd.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)
    refine hzero.congr' ?_
    filter_upwards with y
    dsimp
    simp [Real.log_one]
    ring
  have hg : Tendsto (fun x => Real.exp x) atBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    Real.tendsto_exp_atBot_nhdsGT
  have hlim : Tendsto (fun x => Real.log (1 + Real.exp x) / Real.exp x) atBot (nhds 1) :=
    hslope.comp hg
  have h : (fun x => softplus x / Real.exp x) = fun x =>
      Real.log (1 + Real.exp x) / Real.exp x := by
    funext x
    unfold softplus
    rfl
  simpa [h] using hlim

/-- SWISH agrees with the identity to within a vanishing error at `+∞`.

Informal proof: multiply the `+∞` logistic limit against `x`, using that the correction term
`x * logistic (-x)` is dominated by the exponential decay of `logistic (-x)`. -/
theorem tendsto_swish_sub_id_atTop : Tendsto (fun x => swish x - x) atTop (nhds 0) := by
  have h1 : Tendsto (fun x => x * Real.exp (-x)) atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  have h2 : Tendsto (fun x => (Real.exp (-x) + 1)⁻¹) atTop (nhds 1) := by
    have h : Tendsto (fun x => Real.exp (-x) + 1) atTop (nhds 1) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.add
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds (1 : ℝ)))
    simpa using h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h : Tendsto (fun x => (x * Real.exp (-x)) * (Real.exp (-x) + 1)⁻¹) atTop (nhds 0) := by
    simpa using h1.mul h2
  have hswish : (fun x => swish x - x) = fun x =>
      -((x * Real.exp (-x)) * (Real.exp (-x) + 1)⁻¹) := by
    funext x
    unfold swish logistic
    field_simp
    ring
  rw [hswish]
  simpa using h.neg

/-- SWISH vanishes at `-∞`.

Informal proof: `swish x = x * logistic x` with `logistic x` decaying like `exp x`, so the product
of the linearly growing `|x|` against the exponentially decaying `logistic x` vanishes. -/
theorem tendsto_swish_atBot : Tendsto swish atBot (nhds 0) := by
  have hxexp : Tendsto (fun x => x * Real.exp x) atBot (nhds 0) := by
    have h : Tendsto (fun y : ℝ => -(y * Real.exp (-y))) atTop (nhds 0) := by
      simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).neg
    simpa [Function.comp_def, neg_mul, neg_neg] using h.comp tendsto_neg_atBot_atTop
  have hd : Tendsto (fun x => 1 + Real.exp x) atBot (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (nhds (1 : ℝ))).add
      Real.tendsto_exp_atBot
  have hinv : Tendsto (fun x => (1 + Real.exp x)⁻¹) atBot (nhds 1) := by
    simpa using hd.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h : Tendsto (fun x => (x * Real.exp x) * (1 + Real.exp x)⁻¹) atBot (nhds 0) := by
    simpa using hxexp.mul hinv
  have hswish : (fun x => swish x) = fun x => (x * Real.exp x) * (1 + Real.exp x)⁻¹ := by
    funext x
    unfold swish logistic
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero x]
    ring
  simpa [hswish] using h

/-- GELU agrees with the identity to within a vanishing error at `+∞`.

Informal proof: use the `+∞` standard-normal CDF limit together with Gaussian tail decay for the
vanishing correction term. -/
theorem tendsto_gelu_sub_id_atTop : Tendsto (fun x => gelu x - x) atTop (nhds 0) := by
  sorry

/-- GELU vanishes at `-∞`.

Informal proof: `gelu x = x * standardNormalCDF x` with `standardNormalCDF x` decaying faster than
any polynomial, so the product with the linearly growing `|x|` vanishes. -/
theorem tendsto_gelu_atBot : Tendsto gelu atBot (nhds 0) := by
  sorry

/-- Positive one-homogeneity of a scalar activation. -/
def PosHomogeneous (σ : ℝ → ℝ) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ x, σ (c * x) = c * σ x

lemma PosHomogeneous.zero {σ : ℝ → ℝ} (hσ : PosHomogeneous σ) : σ 0 = 0 := by
  have h := hσ (by norm_num : (0 : ℝ) < 2) 0
  norm_num at h ⊢
  linarith

/-- The historical perceptron activation is not positively homogeneous. -/
theorem not_posHomogeneous_threshold : ¬ PosHomogeneous threshold := by
  intro h
  have h0 := h.zero
  simp [threshold] at h0

/-- Logistic is not positively homogeneous; in particular, it does not pass through the origin. -/
theorem not_posHomogeneous_logistic : ¬ PosHomogeneous logistic := by
  intro h
  have h0 := h.zero
  rw [logistic_zero] at h0
  norm_num at h0

lemma posHomogeneous_linear (a : ℝ) : PosHomogeneous (linear a) := by
  intro c _ x
  simp only [linear]
  ring

lemma posHomogeneous_relu : PosHomogeneous relu := by
  intro c hc x
  simp only [relu]
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_left (mul_nonneg hc.le hx)]
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    rw [max_eq_right hx', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc.le hx')]
    ring

lemma posHomogeneous_leakyRelu (a : ℝ) : PosHomogeneous (leakyRelu a) := by
  intro c hc x
  simp only [leakyRelu]
  by_cases hx : 0 ≤ x
  · simp [hx, mul_nonneg hc.le hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hcx : ¬ 0 ≤ c * x := not_le.mpr (mul_neg_of_pos_of_neg hc hx')
    simp [hx, hcx]
    ring

/-- The activations described by the source as introducing an intrinsic scale are not positively
one-homogeneous.

Informal proof: positive homogeneity forces a scalar function to be piecewise linear on the two
half-lines.  `tanh`, softplus, SWISH, and GELU have nonconstant slope on the positive half-line;
softplus also already contradicts the necessary equation `σ 0 = 0`.  See the elementary
classification proof below and the discussion of homogeneous functions at
<https://en.wikipedia.org/wiki/Homogeneous_function#Positive_homogeneity>. -/
theorem nonhomogeneous_activations :
    ¬ PosHomogeneous Real.tanh ∧ ¬ PosHomogeneous softplus ∧
      ¬ PosHomogeneous swish ∧ ¬ PosHomogeneous gelu := by
  constructor
  · intro h
    have h2 : Real.tanh 2 = 2 * Real.tanh 1 := by
      have hh := h (by norm_num : (0 : ℝ) < 2) 1
      simpa using hh
    have hlt : Real.tanh 2 < 1 := Real.tanh_lt_one 2
    have hgt : (1 : ℝ) < 2 * Real.tanh 1 := by
      have htanh1 : 1 / 2 < Real.tanh 1 := by
        rw [tanh_eq_exp_two_mul]
        have hgt3 : (3 : ℝ) < Real.exp 2 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith [Real.add_one_le_exp 1]
        field_simp
        nlinarith
      nlinarith
    nlinarith [h2, hlt, hgt]
  · constructor
    · intro h
      have h0 := h.zero
      have hz : Real.log 2 = 0 := by
        rw [softplus_zero] at h0
        exact h0
      have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    · constructor
      · intro h
        have h2 := h (by norm_num : (0 : ℝ) < 2) 1
        have hc : logistic 2 = logistic 1 := by
          have hs2 : swish 2 = 2 * logistic 2 := by simp [swish]
          have hs1 : swish 1 = logistic 1 := by simp [swish]
          have h2' : 2 * logistic 2 = 2 * logistic 1 := by
            simpa [hs2, hs1] using h2
          exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h2'
        have hne : ¬ logistic 2 = logistic 1 := by
          intro h'
          have hl : logistic 1 < logistic 2 := by
            unfold logistic
            have he : Real.exp (-2) < Real.exp (-1) := by
              exact Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < -1)
            have hsum : 1 + Real.exp (-2) < 1 + Real.exp (-1) := by linarith
            exact (inv_lt_inv₀ (by positivity : 0 < 1 + Real.exp (-1))
              (by positivity : 0 < 1 + Real.exp (-2))).2 hsum
          exact (ne_of_lt hl) h'.symm
        exact hne hc
      · intro h
        have h2 := h (by norm_num : (0 : ℝ) < 2) 1
        have hc : standardNormalCDF 2 = standardNormalCDF 1 := by
          have hg2 : gelu 2 = 2 * standardNormalCDF 2 := by simp [gelu]
          have hg1 : gelu 1 = standardNormalCDF 1 := by simp [gelu]
          have h2' : 2 * standardNormalCDF 2 = 2 * standardNormalCDF 1 := by
            simpa [hg2, hg1] using h2
          exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h2'
        have hne : ¬ standardNormalCDF 2 = standardNormalCDF 1 := by
          intro hc_eq
          have hdiff : standardNormalCDF 2 - standardNormalCDF 1 =
              ∫ t in (1 : ℝ)..2, gaussianPDFReal 0 1 t := by
            rw [standardNormalCDF_eq_half_add_standardGaussianIntegral 2,
              standardNormalCDF_eq_half_add_standardGaussianIntegral 1]
            have hadd : (∫ t in (0 : ℝ)..2, gaussianPDFReal 0 1 t) =
                (∫ t in (0 : ℝ)..1, gaussianPDFReal 0 1 t) +
                  ∫ t in (1 : ℝ)..2, gaussianPDFReal 0 1 t := by
              rw [intervalIntegral.integral_add_adjacent_intervals
                (integrable_gaussianPDFReal 0 1).intervalIntegrable
                (integrable_gaussianPDFReal 0 1).intervalIntegrable]
            linarith
          have hpos : 0 < ∫ t in (1 : ℝ)..2, gaussianPDFReal 0 1 t := by
            exact intervalIntegral.intervalIntegral_pos_of_pos
              (integrable_gaussianPDFReal 0 1).intervalIntegrable
              (fun x => gaussianPDFReal_pos 0 1 x (by norm_num : (1 : ℝ≥0) ≠ 0))
              (by norm_num : (1 : ℝ) < 2)
          linarith
        exact hne hc

theorem not_posHomogeneous_tanh : ¬ PosHomogeneous Real.tanh := nonhomogeneous_activations.1

theorem not_posHomogeneous_softplus : ¬ PosHomogeneous softplus :=
  nonhomogeneous_activations.2.1

theorem not_posHomogeneous_swish : ¬ PosHomogeneous swish :=
  nonhomogeneous_activations.2.2.1

theorem not_posHomogeneous_gelu : ¬ PosHomogeneous gelu :=
  nonhomogeneous_activations.2.2.2

/-- A scalar map with independently specified slopes on the two half-lines.
This is the correct normal form for a positively homogeneous function on `ℝ`;
`leakyRelu a` is the special case `piecewiseLinear 1 a`. -/
def piecewiseLinear (aPos aNeg x : ℝ) : ℝ :=
  if 0 ≤ x then aPos * x else aNeg * x

/-- A positively homogeneous scalar activation has a genuine kink at zero exactly when its two
half-line slopes differ.

Informal proof: the right derivative of `piecewiseLinear aPos aNeg` at zero is `aPos` and the left
derivative is `aNeg`; differentiability forces equality.  If they agree, the function is globally
linear.  See <https://en.wikipedia.org/wiki/Piecewise_linear_function>. -/
theorem differentiableAt_piecewiseLinear_zero_iff (aPos aNeg : ℝ) :
    DifferentiableAt ℝ (piecewiseLinear aPos aNeg) 0 ↔ aPos = aNeg := by
  constructor
  · intro hd
    have hslope := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have hright : Tendsto (fun y : ℝ => aPos) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (deriv (piecewiseLinear aPos aNeg) 0)) := by
      have h := hslope.mono_left (nhdsGT_le_nhdsNE 0)
      refine h.congr' ?_
      change ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        slope (piecewiseLinear aPos aNeg) 0 y = aPos
      rw [eventually_nhdsWithin_iff]
      filter_upwards with y hy
      dsimp [slope, piecewiseLinear]
      simp [le_of_lt (Set.mem_Ioi.mp hy)]
      have hy0 : y ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hy)
      field_simp [hy0]
    have hleft : Tendsto (fun y : ℝ => aNeg) (nhdsWithin (0 : ℝ) (Set.Iio 0))
        (nhds (deriv (piecewiseLinear aPos aNeg) 0)) := by
      have h := hslope.mono_left (nhdsLT_le_nhdsNE 0)
      refine h.congr' ?_
      change ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Iio 0),
        slope (piecewiseLinear aPos aNeg) 0 y = aNeg
      rw [eventually_nhdsWithin_iff]
      filter_upwards with y hy
      dsimp [slope, piecewiseLinear]
      simp [not_le.mpr (Set.mem_Iio.mp hy)]
      have hy0 : y ≠ 0 := ne_of_lt (Set.mem_Iio.mp hy)
      field_simp [hy0]
    have haPos : aPos = deriv (piecewiseLinear aPos aNeg) 0 := tendsto_const_nhds_iff.mp hright
    have haNeg : aNeg = deriv (piecewiseLinear aPos aNeg) 0 := tendsto_const_nhds_iff.mp hleft
    exact haPos.trans haNeg.symm
  · intro h
    have hf : piecewiseLinear aPos aNeg = fun x : ℝ => aPos * x := by
      funext x
      rw [h]
      by_cases hx : 0 ≤ x
      · simp [piecewiseLinear, hx]
      · simp [piecewiseLinear, hx]
    rw [hf]
    exact (hasDerivAt_const_mul aPos).differentiableAt

@[simp]
lemma piecewiseLinear_one (a x : ℝ) : piecewiseLinear 1 a x = leakyRelu a x := by
  simp [piecewiseLinear, leakyRelu]

lemma posHomogeneous_piecewiseLinear (aPos aNeg : ℝ) :
    PosHomogeneous (piecewiseLinear aPos aNeg) := by
  intro c hc x
  by_cases hx : 0 ≤ x
  · have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
    simp [piecewiseLinear, hx, hcx]
    ring
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hcx : ¬ 0 ≤ c * x := not_le.mpr (mul_neg_of_pos_of_neg hc hxneg)
    simp [piecewiseLinear, hx, hcx]
    ring

/-- Every positively one-homogeneous scalar function is linear on each of the
two half-lines, with slopes `σ 1` and `-σ (-1)`. -/
theorem PosHomogeneous.eq_piecewiseLinear {σ : ℝ → ℝ} (hσ : PosHomogeneous σ) :
    σ = piecewiseLinear (σ 1) (-σ (-1)) := by
  funext x
  by_cases hx : 0 ≤ x
  · by_cases hx0 : x = 0
    · simp [hx0, piecewiseLinear, hσ.zero]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have h := hσ hxpos 1
      rw [piecewiseLinear, if_pos hx]
      simpa only [mul_one] using h.trans (mul_comm x (σ 1))
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hpos : 0 < -x := neg_pos.mpr hxneg
    have h := hσ hpos (-1)
    have harg : (-x) * (-1 : ℝ) = x := by ring
    rw [harg] at h
    rw [piecewiseLinear, if_neg hx]
    calc
      σ x = (-x) * σ (-1) := h
      _ = (-σ (-1)) * x := by ring

/-- Classification of positive one-homogeneous scalar activations. -/
theorem posHomogeneous_iff_eq_piecewiseLinear {σ : ℝ → ℝ} :
    PosHomogeneous σ ↔ σ = piecewiseLinear (σ 1) (-σ (-1)) := by
  constructor
  · exact PosHomogeneous.eq_piecewiseLinear
  · intro h
    rw [h]
    exact posHomogeneous_piecewiseLinear _ _

/-- The one-parameter leaky-ReLU classification is valid after normalizing the
positive-side slope to one. -/
theorem posHomogeneous_and_apply_one_iff_eq_leakyRelu {σ : ℝ → ℝ} :
    (PosHomogeneous σ ∧ σ 1 = 1) ↔ ∃ a : ℝ, σ = leakyRelu a := by
  constructor
  · rintro ⟨hσ, h1⟩
    refine ⟨-σ (-1), ?_⟩
    calc
      σ = piecewiseLinear (σ 1) (-σ (-1)) := hσ.eq_piecewiseLinear
      _ = piecewiseLinear 1 (-σ (-1)) := by rw [h1]
      _ = leakyRelu (-σ (-1)) := by
        funext x
        exact piecewiseLinear_one _ _
  · rintro ⟨a, rfl⟩
    refine ⟨posHomogeneous_leakyRelu a, ?_⟩
    simp [leakyRelu]

end NeuralNetwork

end

end
