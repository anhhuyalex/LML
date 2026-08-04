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
open Filter
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
    MeasureTheory.integral_tilted (μ := μ) (fun x ↦ -ε * V x) O

/-- An explicit normalizability proof promotes a deformation to a probability measure. -/
theorem isProbabilityMeasure_deform [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (ε : ℝ) (hnorm : Normalizable μ V ε) :
    IsProbabilityMeasure (deform μ V ε) :=
  MeasureTheory.isProbabilityMeasure_tilted hnorm

-- The exponential of an (a.e.) measurable real function is (a.e.) measurable.
-- This isolates the measurability step of `normalizable_of_nonnegative`.
private lemma aemeasurable_exp {f : Ω → ℝ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ Real.exp (f x)) μ :=
  hf.exp

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
    Normalizable μ V ε :=
  Integrable.of_mem_Icc 0 1 (aemeasurable_exp (hVmeas.aemeasurable.const_mul (-ε)))
    (ae_of_all μ fun x => exp_neg_mul_nonneg_mem_Icc hε (hVnonneg x))

/-- The partition function of a normalizable nonzero base measure is strictly positive.

Informal proof: unfold the partition function and apply positivity of the integral of an
integrable strictly positive exponential. -/
theorem partitionFunction_pos [NeZero μ] {V : Ω → ℝ} {ε : ℝ}
    (hnorm : Normalizable μ V ε) :
    0 < partitionFunction μ V ε :=
  MeasureTheory.integral_exp_pos (f := fun x ↦ -ε * V x) hnorm

/-! ## First-order response -/

-- For `t ≥ 0`, the difference between `exp (-t)` and `1` is bounded by `t`:
-- `exp (-t) ≤ 1` makes `|exp (-t) - 1| = 1 - exp (-t)`, and convexity of the exponential
-- (`Real.one_sub_le_exp_neg`) gives `1 - exp (-t) ≤ t`.
private lemma abs_exp_neg_sub_one_le {t : ℝ} (ht : 0 ≤ t) : |Real.exp (-t) - 1| ≤ t := by
  have h_nonpos : Real.exp (-t) - 1 ≤ 0 := sub_nonpos.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ht))
  calc
    |Real.exp (-t) - 1| = 1 - Real.exp (-t) := by simpa using abs_of_nonpos h_nonpos
    _ ≤ t := by
      have h := Real.one_sub_le_exp_neg t
      linarith

-- For `h > 0` and `v ≥ 0`, the right difference quotient of `exp (-h * v)` at zero is
-- dominated by `v`: `|(exp (-h * v) - 1) / h| = |exp (-h * v) - 1| / h ≤ (h * v) / h = v`.
-- This is the pointwise domination used in the dominated convergence theorem below.
private lemma abs_diffQuot_exp_neg_mul_le {h v : ℝ} (hh : 0 < h) (hv : 0 ≤ v) :
    |(Real.exp (-h * v) - 1) / h| ≤ v := by
  calc
    |(Real.exp (-h * v) - 1) / h| = |Real.exp (-h * v) - 1| / h := by
      rw [abs_div, abs_of_pos hh]
    _ ≤ (h * v) / h := by
      exact div_le_div_of_nonneg_right (by
        simpa using abs_exp_neg_sub_one_le (mul_nonneg hh.le hv)) hh.le
    _ = v := by
      rw [div_eq_mul_inv, mul_comm, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

-- Pointwise, the right difference quotient of `fun h ↦ exp (-h * v)` converges to `-v` at
-- zero.  This is the scalar derivative of `exp` (chain rule) restricted to the right half-line.
private lemma tendsto_diffQuot_exp_neg_mul {v : ℝ} :
    Tendsto (fun h : ℝ => (Real.exp (-h * v) - 1) / h) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (-v)) := by
  have hderiv : HasDerivWithinAt (fun h : ℝ => Real.exp (-h * v)) (-v) (Set.Ioi (0 : ℝ)) 0 := by
    have hlin : HasDerivAt (fun h : ℝ => -h * v) (-v) 0 := by
      simpa [mul_comm] using ((hasDerivAt_id' 0).const_mul (-v))
    have hderivAt : HasDerivAt (fun h : ℝ => Real.exp (-h * v)) (-v) 0 := by
      simpa using hlin.exp
    exact hderivAt.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0 : ℝ)) (x := 0) (by simp)] at hderiv
  convert hderiv using 1
  funext h
  simp [slope_def_field]

-- For `ε ≥ 0`, the exponential `x ↦ exp (-ε * V x)` is integrable: it is measurable and lies
-- pointwise in `[0, 1]`, while the base measure is finite.
private lemma integrable_exp_neg_mul_nonneg [IsFiniteMeasure μ] {V : Ω → ℝ}
    (hVmeas : AEStronglyMeasurable V μ) (hVnonneg : 0 ≤ V) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun x : Ω => Real.exp (-ε * V x)) μ :=
  Integrable.of_mem_Icc 0 1
    ((Real.continuous_exp.comp_aestronglyMeasurable (hVmeas.const_mul (-ε))).aemeasurable)
    (ae_of_all μ fun x => exp_neg_mul_nonneg_mem_Icc hε (hVnonneg x))

-- The slope of the integrated exponential equals the integral of the pointwise difference
-- quotients, as functions on the right half-line `𝓝[Ioi 0] 0`.  This lets us read the limit of
-- the slopes off the dominated-convergence limit of the integrated difference quotients.
private lemma slope_integral_exp_neg_mul_eq_integral_diffQuot [IsFiniteMeasure μ]
    {V : Ω → ℝ} (hVnonneg : 0 ≤ V) (hV : Integrable V μ) :
    (fun h : ℝ => slope (fun ε : ℝ => ∫ x, Real.exp (-ε * V x) ∂μ) 0 h) =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ => ∫ x, (Real.exp (-h * V x) - 1) / h ∂μ) := by
  filter_upwards [self_mem_nhdsWithin] with h hh
  -- For `0 < h` the slope is the integral of the pointwise difference quotients: pull the
  -- scalar `h⁻¹` through the integral and combine the two resulting integrals with
  -- `integral_sub` (both exponentials are integrable by `integrable_exp_neg_mul_nonneg`).
  have h_int_exp : Integrable (fun x : Ω => Real.exp (-h * V x)) μ :=
    integrable_exp_neg_mul_nonneg hV.aestronglyMeasurable hVnonneg hh.le
  have h_int_zero : Integrable (fun x : Ω => Real.exp (-0 * V x)) μ :=
    integrable_exp_neg_mul_nonneg hV.aestronglyMeasurable hVnonneg (by simp)
  calc
    slope (fun ε : ℝ => ∫ x, Real.exp (-ε * V x) ∂μ) 0 h
        = h⁻¹ * ((∫ x, Real.exp (-h * V x) ∂μ) - (∫ x, Real.exp (-0 * V x) ∂μ)) := by
            rw [slope_def_module]
            simp
    _ = h⁻¹ * (∫ x, (Real.exp (-h * V x) - Real.exp (-0 * V x)) ∂μ) := by
            rw [integral_sub h_int_exp h_int_zero]
    _ = ∫ x, h⁻¹ * (Real.exp (-h * V x) - Real.exp (-0 * V x)) ∂μ := by
            rw [← integral_const_mul]
    _ = ∫ x, h⁻¹ * (Real.exp (-h * V x) - 1) ∂μ := by
            apply integral_congr_ae
            refine ae_of_all μ ?_
            intro x
            simp
    _ = ∫ x, (Real.exp (-h * V x) - 1) / h ∂μ := by
            apply integral_congr_ae
            refine ae_of_all μ ?_
            intro x
            change h⁻¹ * (Real.exp (-h * V x) - 1) = (Real.exp (-h * V x) - 1) / h
            rw [div_eq_mul_inv]
            ring

/-- Right differentiation under the integral for a nonnegative exponential tilt at the origin.

This is the reusable analytic core of `hasDerivWithinAt_partitionFunction_zero`.

Informal proof: by `hasDerivWithinAt_iff_tendsto_slope`, it suffices to prove convergence of the
right-hand difference quotients.  For `h > 0` and `h ≥ 0`,
`(exp (-h * V x) - 1) / h → -V x` pointwise as `h → 0` by the scalar derivative of `exp` and the
chain rule.  The domination is
`‖(exp (-h * V x) - 1) / h‖ ≤ V x`: put `t = h * V x ≥ 0`, use `exp (-t) ≤ 1` and
`1 - exp (-t) ≤ t` (Mathlib lemma `Real.one_sub_le_exp_neg`, equivalently convexity of `exp`).
The bound `V` is integrable by hypothesis.  The filter-version dominated convergence theorem
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence` on `𝓝[Set.Ici 0] 0` then gives
`∫ x, (exp (-h * V x) - 1) / h ∂μ → ∫ x, -V x ∂μ`.  Finally, integral linearity and
`IsProbabilityMeasure.measure_univ = 1` identify these integrals with the slope of
`fun h ↦ ∫ x, exp (-h * V x) ∂μ` at zero.  This is the standard one-sided dominated-convergence
argument recorded in `blueprint/src/chapters/renormalization.tex`, Section "Actions as exponential
deformations"; the one-sided restriction is essential without exponential integrability for
negative couplings. -/
private theorem hasDerivWithinAt_integral_exp_neg_mul_zero [IsProbabilityMeasure μ]
    {V : Ω → ℝ} (hVnonneg : 0 ≤ V) (hV : Integrable V μ) :
    HasDerivWithinAt (fun ε : ℝ ↦ ∫ x, Real.exp (-ε * V x) ∂μ)
      (-(∫ x, V x ∂μ)) (Set.Ici 0) 0 := by
  -- The derivative is a limit of right difference quotients of the integrated exponential along
  -- the punctured right half-line `𝓝[Ioi 0] 0` (`hasDerivWithinAt_iff_tendsto_slope`).
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Set.Ici (0 : ℝ) \ {0} = Set.Ioi (0 : ℝ) := by
    ext x
    simp [Set.Ici, Set.Ioi, lt_iff_le_and_ne, eq_comm]
  rw [hs]

  -- Step 1: dominated convergence on the right half-line.  The difference quotients converge
  -- pointwise to `-V` (`tendsto_diffQuot_exp_neg_mul`) and are dominated by the integrable
  -- function `V` (`abs_diffQuot_exp_neg_mul_le`).
  have hDCT : Filter.Tendsto
      (fun h : ℝ => ∫ x, (Real.exp (-h * V x) - 1) / h ∂μ)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (∫ x, -V x ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[Set.Ioi (0 : ℝ)] 0)
      (F := fun h : ℝ => fun x : Ω => (Real.exp (-h * V x) - 1) / h)
      (f := fun x : Ω => -V x) V ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh
      -- `v ↦ (exp (-h * v) - 1) / h` is continuous for `h > 0`, so composing with the
      -- ae-strongly measurable `V` gives ae-strongly measurable difference quotients.
      have hc : Continuous (fun v : ℝ => (Real.exp (-h * v) - 1) / h) := by
        have h1 : Continuous (fun v : ℝ => Real.exp (-h * v)) :=
          Real.continuous_exp.comp (continuous_const.mul continuous_id)
        exact (h1.sub continuous_const).div continuous_const (fun _ => hh.ne')
      exact hc.comp_aestronglyMeasurable hV.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      refine ae_of_all μ ?_
      intro x
      simpa [Real.norm_eq_abs, abs_div] using abs_diffQuot_exp_neg_mul_le hh (hVnonneg x)
    · exact hV
    · refine ae_of_all μ ?_
      intro x
      exact tendsto_diffQuot_exp_neg_mul (v := V x)

  -- Step 2: on the right half-line the slope of the integral equals the integral of the
  -- pointwise difference quotients (`slope_integral_exp_neg_mul_eq_integral_diffQuot`), so the
  -- dominated-convergence limit is the slope limit, and `∫ -V = -∫ V` finishes the proof.
  exact (Filter.tendsto_congr' (slope_integral_exp_neg_mul_eq_integral_diffQuot (μ := μ) hVnonneg hV)).2
    (by simpa [integral_neg] using hDCT)

/-- Right derivative of the relative partition function at zero.

Informal proof: for nonnegative `ε` and `V`, differentiate the exponential pointwise and dominate
the difference quotient by `V`.  Dominated convergence gives the derivative `-∫ V`; probability
normalization gives `Z(0)=1`. -/
theorem hasDerivWithinAt_partitionFunction_zero [IsProbabilityMeasure μ]
    {V : Ω → ℝ} (hVnonneg : 0 ≤ V) (hV : Integrable V μ) :
    HasDerivWithinAt (partitionFunction μ V) (-(∫ x, V x ∂μ)) (Set.Ici 0) 0 := by
  change HasDerivWithinAt (fun ε : ℝ ↦ ∫ x, Real.exp (-ε * V x) ∂μ)
    (-(∫ x, V x ∂μ)) (Set.Ici 0) 0
  exact hasDerivWithinAt_integral_exp_neg_mul_zero (μ := μ) hVnonneg hV

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
