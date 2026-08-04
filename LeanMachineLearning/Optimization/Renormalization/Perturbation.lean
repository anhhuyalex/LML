/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Cumulant
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Exponential perturbations of probability measures

This file fixes the sign and normalization conventions for perturbing a base measure by a
potential.  Normalizability is an explicit predicate, and every theorem that promotes a deformed
measure to a probability measure takes the corresponding integrability proof as an argument.

Deferred proof references:

* Mathlib's tilted-measure API:
  <https://github.com/leanprover-community/mathlib4/blob/abb22825db7e020c94f38a007ae3fffe6c3a7532/Mathlib/MeasureTheory/Measure/Tilted.lean>.
* The dominated-convergence argument and quadratic exponential remainder are recorded in
  `LML/blueprint/src/chapters/renormalization.tex`, Section "Actions as exponential
  deformations".

Every deferred theorem below includes its own informal proof.  All one-sided asymptotic statements
display the filter `nhdsWithin 0 (Set.Ici 0)` in their conclusions.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace Renormalization

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Exponential deformation by the action `ε V`, with the minus sign fixed by convention. -/
def deform (μ : Measure Ω) (V : Ω → ℝ) (ε : ℝ) : Measure Ω :=
  μ.tilted (fun x ↦ -ε * V x)

/-- Partition function relative to the base measure. -/
def partitionFunction (μ : Measure Ω) (V : Ω → ℝ) (ε : ℝ) : ℝ :=
  ∫ x, Real.exp (-ε * V x) ∂μ

/-- The exact integrability condition that makes `deform μ V ε` a probability measure when the
base measure is nonzero. -/
def Normalizable (μ : Measure Ω) (V : Ω → ℝ) (ε : ℝ) : Prop :=
  Integrable (fun x ↦ Real.exp (-ε * V x)) μ

/-- The unnormalized numerator of a deformed expectation. -/
def weightedIntegral [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (V : Ω → ℝ) (O : Ω → E) (ε : ℝ) : E :=
  ∫ x, Real.exp (-ε * V x) • O x ∂μ

/-- Covariance of a Banach-valued observable with a real potential. -/
def covarianceWith [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (O : Ω → E) (V : Ω → ℝ) : E :=
  (∫ x, V x • O x ∂μ) - (∫ x, V x ∂μ) • ∫ x, O x ∂μ

/-- The exact normalized-expectation identity.

This is a direct specialization of `MeasureTheory.integral_tilted`; no integrability hypothesis is
needed for the equality because Mathlib defines a nonnormalizable tilt to be the zero measure. -/
theorem integral_deform [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (V : Ω → ℝ) (O : Ω → E) (ε : ℝ) :
    ∫ x, O x ∂deform μ V ε =
      ∫ x, (Real.exp (-ε * V x) / partitionFunction μ V ε) • O x ∂μ := by
  simpa only [deform, partitionFunction] using
    (MeasureTheory.integral_tilted (μ := μ) (fun x ↦ -ε * V x) O)

/-- An explicit normalizability proof promotes a deformation to a probability measure. -/
theorem isProbabilityMeasure_deform [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (ε : ℝ) (hnorm : Normalizable μ V ε) :
    IsProbabilityMeasure (deform μ V ε) := by
  exact MeasureTheory.isProbabilityMeasure_tilted hnorm

-- The exponential of an (a.e.) measurable real function is (a.e.) measurable.
-- This isolates the measurability step of `normalizable_of_nonnegative`.
private lemma aemeasurable_exp {f : Ω → ℝ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ Real.exp (f x)) μ :=
  Real.continuous_exp.measurable.comp_aemeasurable' hf

-- For `ε ≥ 0` and `v ≥ 0`, the scalar `exp (-ε * v)` lies in `[0, 1]`.
-- This is the pointwise content behind "the exponential lies between zero and one":
-- the exponent `-ε * v` is nonpositive, so the exponential is positive and at most `exp 0 = 1`.
private lemma exp_neg_mul_nonneg_mem_Icc {ε v : ℝ} (hε : 0 ≤ ε) (hv : 0 ≤ v) :
    Real.exp (-ε * v) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le,
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hε) hv)⟩

/-- A nonnegative potential is normalizable for every nonnegative coupling.

Informal proof: for `ε ≥ 0` and `V ≥ 0`, the exponential lies between zero and one.  Its strong
measurability follows from that of `V`, and the constant one function is integrable under a finite
measure; domination gives integrability. -/
theorem normalizable_of_nonnegative [IsFiniteMeasure μ] {V : Ω → ℝ}
    (hVmeas : AEStronglyMeasurable V μ) (hVnonneg : 0 ≤ V) {ε : ℝ} (hε : 0 ≤ ε) :
    Normalizable μ V ε := by
  refine Integrable.of_mem_Icc 0 1 (aemeasurable_exp (hVmeas.aemeasurable.const_mul (-ε))) ?_
  filter_upwards with x using exp_neg_mul_nonneg_mem_Icc hε (hVnonneg x)

/-- The partition function of a normalizable nonzero base measure is strictly positive.

Informal proof: unfold the partition function and apply positivity of the integral of an
integrable strictly positive exponential. -/
theorem partitionFunction_pos [NeZero μ] {V : Ω → ℝ} {ε : ℝ}
    (hnorm : Normalizable μ V ε) :
    0 < partitionFunction μ V ε := by
  sorry

/-! ## First-order response -/

/-- Right derivative of the relative partition function at zero.

Informal proof: for nonnegative `ε` and `V`, differentiate the exponential pointwise and dominate
the difference quotient by `V`.  Dominated convergence gives the derivative `-∫ V`; probability
normalization gives `Z(0)=1`. -/
theorem hasDerivWithinAt_partitionFunction_zero [IsProbabilityMeasure μ]
    {V : Ω → ℝ} (hVnonneg : 0 ≤ V) (hV : Integrable V μ) :
    HasDerivWithinAt (partitionFunction μ V) (-(∫ x, V x ∂μ)) (Set.Ici 0) 0 := by
  sorry

/-- Right derivative of an unnormalized weighted integral at zero.

Informal proof: differentiate `exp (-ε V x) • O x` pointwise.  On the right half-line the
difference quotient is dominated in norm by `|V| * ‖O‖`; the hypothesis on `V • O` supplies the
integrable envelope, so dominated convergence gives the displayed derivative. -/
theorem hasDerivWithinAt_weightedIntegral_zero
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hO : Integrable O μ) (hVO : Integrable (fun x ↦ V x • O x) μ) :
    HasDerivWithinAt (weightedIntegral μ V O) (-(∫ x, V x • O x ∂μ))
      (Set.Ici 0) 0 := by
  sorry

/-- Linear response of a normalized expectation along the nonnegative-coupling half-line.

Informal proof: use `integral_deform` to write the expectation as the weighted numerator divided by
the partition function.  Apply the preceding two derivative lemmas and the quotient rule; at zero
the denominator is one, and the resulting derivative is `-covarianceWith μ O V`. -/
theorem hasDerivWithinAt_integral_deform_zero [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hV : Integrable V μ) (hO : Integrable O μ)
    (hVO : Integrable (fun x ↦ V x • O x) μ) :
    HasDerivWithinAt (fun ε ↦ ∫ x, O x ∂deform μ V ε) (-covarianceWith μ O V)
      (Set.Ici 0) 0 := by
  sorry

/-! ## Quadratic remainders -/

/-- Quadratic right-hand remainder for the partition function.

Informal proof: apply `|exp (-t)-1+t| ≤ t²/2` with `t=ε V x`, integrate the bound using
integrability of `V²`, and read the resulting uniform estimate as `IsBigO` at the displayed
right-neighborhood filter. -/
theorem partitionFunction_sub_linear_isBigO [IsProbabilityMeasure μ]
    {V : Ω → ℝ} (hVnonneg : 0 ≤ V) (hV : Integrable V μ)
    (hV2 : Integrable (fun x ↦ V x ^ 2) μ) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ partitionFunction μ V ε - 1 + ε * ∫ x, V x ∂μ)
      (fun ε : ℝ ↦ ε ^ 2) := by
  sorry

/-- Quadratic right-hand remainder for an unnormalized weighted integral.

Informal proof: use the same pointwise exponential remainder and multiply its bound by `‖O x‖`.
The `V² • O` hypothesis is exactly the integrable dominating function required after integration. -/
theorem weightedIntegral_sub_linear_isBigO
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hO : Integrable O μ) (hVO : Integrable (fun x ↦ V x • O x) μ)
    (hV2O : Integrable (fun x ↦ V x ^ 2 • O x) μ) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ weightedIntegral μ V O ε - (∫ x, O x ∂μ) +
        ε • ∫ x, V x • O x ∂μ)
      (fun ε : ℝ ↦ ε ^ 2) := by
  sorry

/-- Quadratic right-hand remainder for the normalized deformed expectation.

Informal proof: combine the numerator and denominator expansions above.  Positivity and continuity
of the partition function bound its reciprocal on a sufficiently small right-neighborhood of zero;
the quotient algebra leaves the covariance as the linear coefficient and an `O(ε²)` remainder. -/
theorem integral_deform_sub_linear_isBigO [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hV : Integrable V μ) (hO : Integrable O μ)
    (hVO : Integrable (fun x ↦ V x • O x) μ)
    (hV2 : Integrable (fun x ↦ V x ^ 2) μ)
    (hV2O : Integrable (fun x ↦ V x ^ 2 • O x) μ) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ (∫ x, O x ∂deform μ V ε) - (∫ x, O x ∂μ) +
        ε • covarianceWith μ O V)
      (fun ε : ℝ ↦ ε ^ 2) := by
  sorry

end Renormalization

end

end
