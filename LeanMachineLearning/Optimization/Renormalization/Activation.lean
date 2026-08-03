/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

@[simp] theorem tanhActivation_zero : Real.tanh 0 = 0 := Real.tanh_zero

@[simp] theorem sinActivation_zero : Real.sin 0 = 0 := Real.sin_zero

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
  -- Total mass of the standard-normal density is one.
  have htotal : (∫ t, gaussianPDFReal 0 1 t) = 1 :=
    integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : ℝ≥0) ≠ 0)
  -- The density is even, so the positive half-line carries the same mass as the negative one.
  have heven : ∀ t : ℝ, gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t := by
    intro t
    simp [gaussianPDFReal]
  -- Splitting the full integral at zero and using evenness gives `2 * ∫ Iic 0 = 1`.
  have hsplit : (∫ t in Set.Iic 0, gaussianPDFReal 0 1 t) + (∫ t in Set.Ioi 0, gaussianPDFReal 0 1 t) = 1 := by
    rw [intervalIntegral.integral_Iic_add_Ioi]
    · exact htotal
    · exact (integrable_gaussianPDFReal 0 1).integrableOn
    · exact (integrable_gaussianPDFReal 0 1).integrableOn
  have hhalf : (∫ t in Set.Ioi 0, gaussianPDFReal 0 1 t) = ∫ t in Set.Iic 0, gaussianPDFReal 0 1 t := by
    calc
      (∫ t in Set.Ioi 0, gaussianPDFReal 0 1 t) = ∫ t in Set.Ioi 0, gaussianPDFReal 0 1 (-t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact (heven t).symm
      _ = ∫ t in Set.Iic 0, gaussianPDFReal 0 1 t := by
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
  -- Step 1: the CDF is the real measure of `Iic x`, i.e. the density integral over `Iic x`.
  have hIic : standardNormalCDF x = ∫ t in Set.Iic x, gaussianPDFReal 0 1 t := by
    rw [standardNormalCDF, ProbabilityTheory.cdf_eq_real]
    rw [measureReal_def]
    rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (Set.Iic x)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Iic (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  -- Step 2: `∫ Iic x = ∫ Iic 0 + ∫ 0..x` by cutting the half-line at zero.
  have hsplit : (∫ t in Set.Iic x, gaussianPDFReal 0 1 t) =
      (∫ t in Set.Iic 0, gaussianPDFReal 0 1 t) + ∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t := by
    rw [← intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x) (f := gaussianPDFReal 0 1)
        (integrable_gaussianPDFReal 0 1).integrableOn (integrable_gaussianPDFReal 0 1).integrableOn]
    ring
  -- Step 3: the half-line integral is `1 / 2`, giving the desired formula.
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
  -- Step 1: the scaled density `gaussianPDFReal 0 1 (√2 * u)` is the Gaussian kernel.
  have hpdf : ∀ u : ℝ, gaussianPDFReal 0 1 (Real.sqrt 2 * u) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-u ^ 2) := by
    intro u
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    calc
      gaussianPDFReal 0 1 (Real.sqrt 2 * u) = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(Real.sqrt 2 * u) ^ 2 / 2) := by
        simp [gaussianPDFReal]
      _ = (Real.sqrt (2 * π))⁻¹ * Real.exp (-u ^ 2) := by
        congr 1
        congr 1
        rw [mul_pow, hsq]
        ring
  -- Step 2: `√2 * (√(2π))⁻¹ = (√π)⁻¹`, i.e. `√(2π) = √2 * √π`.
  have hsqrtmul : Real.sqrt 2 * (Real.sqrt (2 * π))⁻¹ = (Real.sqrt π)⁻¹ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) π]
    field_simp [hsqrt, hsqrtpi]
  -- Step 3: change of variables `t = √2 * u` and simplify the kernel to `gaussianErf`.
  calc
    (∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t)
        = Real.sqrt 2 * ∫ u in (0 : ℝ)..(x / Real.sqrt 2), gaussianPDFReal 0 1 (Real.sqrt 2 * u) := by
          symm
          rw [← smul_eq_mul]
          rw [intervalIntegral.smul_integral_comp_mul_left (c := Real.sqrt 2) (f := gaussianPDFReal 0 1)
            (a := 0) (b := x / Real.sqrt 2)]
          congr 1
          · norm_num
          · rw [mul_comm, div_mul_cancel₀ x hsqrt]
    _ = Real.sqrt 2 * ∫ u in (0 : ℝ)..(x / Real.sqrt 2),
          (Real.sqrt (2 * π))⁻¹ * Real.exp (-u ^ 2) := by
          simp_rw [hpdf]
    _ = (Real.sqrt π)⁻¹ * ∫ u in (0 : ℝ)..(x / Real.sqrt 2), Real.exp (-u ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
          rw [← mul_assoc, hsqrtmul]
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

/-- The source's smooth activations are genuinely smooth, not merely continuous.

Informal proof: exponential, logarithm on the positive range `1 + exp x`, sine, sinh, and cosh are
smooth and smoothness is closed under sums, products, quotients with nonzero denominator, and
composition.  Differentiating the defining interval integral gives the smooth Gaussian integrand;
the CDF/error-function identity transfers smoothness to the standard-normal CDF and GELU.  See
<https://en.wikipedia.org/wiki/Activation_function#Comparison_of_activation_functions>. -/
theorem smooth_activations :
    ContDiff ℝ ⊤ logistic ∧ ContDiff ℝ ⊤ Real.tanh ∧ ContDiff ℝ ⊤ Real.sin ∧
      ContDiff ℝ ⊤ softplus ∧ ContDiff ℝ ⊤ swish ∧ ContDiff ℝ ⊤ gaussianErf ∧
      ContDiff ℝ ⊤ standardNormalCDF ∧ ContDiff ℝ ⊤ gelu := by
  sorry

theorem continuous_standardNormalCDF : Continuous standardNormalCDF :=
  smooth_activations.2.2.2.2.2.2.1.continuous

theorem continuous_gelu : Continuous gelu := smooth_activations.2.2.2.2.2.2.2.continuous

/-- The source's statement that `tanh x ≈ x` near zero, made exact by its derivative.

Informal proof: differentiating `sinh x / cosh x` gives `1 / cosh x ^ 2`, which equals one at zero.
See <https://en.wikipedia.org/wiki/Hyperbolic_functions#Derivatives>. -/
theorem hasDerivAt_tanh_zero : HasDerivAt Real.tanh 1 0 := by
  sorry

/-- Saturation and ReLU-like asymptotics asserted in Chapter 2, stated as actual limits.

Informal proof: divide the logistic expressions by the dominant exponential at each end.  For
softplus use `log (1 + exp x) - x = log (1 + exp (-x))` at `+∞` and
`log (1+y)/y → 1` with `y = exp x` at `-∞`.  SWISH follows by multiplying the logistic limits.
For GELU use the standard-normal CDF limits together with Gaussian tail decay.  References:
<https://en.wikipedia.org/wiki/Logistic_function#Mathematical_properties> and
<https://en.wikipedia.org/wiki/Normal_distribution#Cumulative_distribution_function>. -/
theorem activation_asymptotics :
    Tendsto logistic atTop (nhds 1) ∧
    Tendsto logistic atBot (nhds 0) ∧
    Tendsto Real.tanh atTop (nhds 1) ∧
    Tendsto Real.tanh atBot (nhds (-1)) ∧
    Tendsto (fun x => softplus x - x) atTop (nhds 0) ∧
    Tendsto (fun x => softplus x / Real.exp x) atBot (nhds 1) ∧
    Tendsto (fun x => swish x - x) atTop (nhds 0) ∧
    Tendsto swish atBot (nhds 0) ∧
    Tendsto (fun x => gelu x - x) atTop (nhds 0) ∧
    Tendsto gelu atBot (nhds 0) := by
  sorry

theorem tendsto_logistic_atTop : Tendsto logistic atTop (nhds 1) := activation_asymptotics.1

theorem tendsto_logistic_atBot : Tendsto logistic atBot (nhds 0) := activation_asymptotics.2.1

theorem tendsto_tanh_atTop : Tendsto Real.tanh atTop (nhds 1) := activation_asymptotics.2.2.1

theorem tendsto_tanh_atBot : Tendsto Real.tanh atBot (nhds (-1)) :=
  activation_asymptotics.2.2.2.1

theorem tendsto_softplus_sub_id_atTop :
    Tendsto (fun x => softplus x - x) atTop (nhds 0) := activation_asymptotics.2.2.2.2.1

theorem tendsto_softplus_div_exp_atBot :
    Tendsto (fun x => softplus x / Real.exp x) atBot (nhds 1) :=
  activation_asymptotics.2.2.2.2.2.1

theorem tendsto_swish_sub_id_atTop :
    Tendsto (fun x => swish x - x) atTop (nhds 0) := activation_asymptotics.2.2.2.2.2.2.1

theorem tendsto_swish_atBot : Tendsto swish atBot (nhds 0) :=
  activation_asymptotics.2.2.2.2.2.2.2.1

theorem tendsto_gelu_sub_id_atTop :
    Tendsto (fun x => gelu x - x) atTop (nhds 0) :=
  activation_asymptotics.2.2.2.2.2.2.2.2.1

theorem tendsto_gelu_atBot : Tendsto gelu atBot (nhds 0) :=
  activation_asymptotics.2.2.2.2.2.2.2.2.2

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
  sorry

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
  sorry

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
