/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

open MeasureTheory ProbabilityTheory Real

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

/-- Positive one-homogeneity of a scalar activation. -/
def PosHomogeneous (σ : ℝ → ℝ) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ x, σ (c * x) = c * σ x

lemma PosHomogeneous.zero {σ : ℝ → ℝ} (hσ : PosHomogeneous σ) : σ 0 = 0 := by
  have h := hσ (by norm_num : (0 : ℝ) < 2) 0
  norm_num at h ⊢
  linarith

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

/-- A scalar map with independently specified slopes on the two half-lines.
This is the correct normal form for a positively homogeneous function on `ℝ`;
`leakyRelu a` is the special case `piecewiseLinear 1 a`. -/
def piecewiseLinear (aPos aNeg x : ℝ) : ℝ :=
  if 0 ≤ x then aPos * x else aNeg * x

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
