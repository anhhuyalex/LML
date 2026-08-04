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
  rw [abs_of_nonpos (sub_nonpos.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ht)))]
  linarith [Real.one_sub_le_exp_neg t]

-- For `h > 0` and `v ≥ 0`, the right difference quotient of `exp (-h * v)` at zero is
-- dominated by `v`: `|(exp (-h * v) - 1) / h| = |exp (-h * v) - 1| / h ≤ (h * v) / h = v`.
-- This is the pointwise domination used in the dominated convergence theorem below.
private lemma abs_diffQuot_exp_neg_mul_le {h v : ℝ} (hh : 0 < h) (hv : 0 ≤ v) :
    |(Real.exp (-h * v) - 1) / h| ≤ v := by
  simpa [abs_div, abs_of_pos hh, div_le_iff₀ hh, mul_comm] using
    abs_exp_neg_sub_one_le (mul_nonneg hh.le hv)

-- Pointwise, the right difference quotient of `fun h ↦ exp (-h * v)` converges to `-v` at
-- zero.  This is the scalar derivative of `exp` (chain rule) restricted to the right half-line.
private lemma tendsto_diffQuot_exp_neg_mul {v : ℝ} :
    Tendsto (fun h : ℝ => (Real.exp (-h * v) - 1) / h) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (-v)) := by
  have hderiv : HasDerivWithinAt (fun h : ℝ => Real.exp (-h * v)) (-v) (Set.Ioi (0 : ℝ)) 0 := by
    simpa [mul_comm] using (((hasDerivAt_id' 0).const_mul (-v)).exp.hasDerivWithinAt)
  simpa [slope_fun_def_field] using
    (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0 : ℝ)) (x := 0) (by simp)).mp hderiv

-- For `ε ≥ 0`, the exponential `x ↦ exp (-ε * V x)` is integrable: it is measurable and lies
-- pointwise in `[0, 1]`, while the base measure is finite.
private lemma integrable_exp_neg_mul_nonneg [IsFiniteMeasure μ] {V : Ω → ℝ}
    (hVmeas : AEStronglyMeasurable V μ) (hVnonneg : 0 ≤ V) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun x : Ω => Real.exp (-ε * V x)) μ :=
  Integrable.of_mem_Icc 0 1
    (hVmeas.aemeasurable.const_mul (-ε)).exp
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
  calc
    slope (fun ε : ℝ => ∫ x, Real.exp (-ε * V x) ∂μ) 0 h
        = h⁻¹ * ((∫ x, Real.exp (-h * V x) ∂μ) - (∫ x, 1 ∂μ)) := by
            simp [slope_def_module]
    _ = ∫ x, (Real.exp (-h * V x) - 1) / h ∂μ := by
            rw [← integral_sub (integrable_exp_neg_mul_nonneg hV.aestronglyMeasurable hVnonneg
              hh.le) (integrable_const (1 : ℝ)), ← integral_const_mul]
            exact integral_congr_ae (ae_of_all μ (fun x => by ring))

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
  rw [← hasDerivWithinAt_Ioi_iff_Ici (x := 0),
    hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0 : ℝ)) (x := 0) (by simp)]
  -- Step 1: dominated convergence on the right half-line.  The difference quotients converge
  -- pointwise to `-V` (`tendsto_diffQuot_exp_neg_mul`) and are dominated by the integrable
  -- function `V` (`abs_diffQuot_exp_neg_mul_le`).
  have hDCT : Tendsto
      (fun h : ℝ => ∫ x, (Real.exp (-h * V x) - 1) / h ∂μ)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (∫ x, -V x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[Set.Ioi (0 : ℝ)] 0)
      (F := fun h x => (Real.exp (-h * V x) - 1) / h)
      (f := fun x => -V x) V ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh
      -- `v ↦ (exp (-h * v) - 1) / h` is continuous for `h > 0`, so composing with the
      -- ae-strongly measurable `V` gives ae-strongly measurable difference quotients.
      exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
        continuous_const).div continuous_const (fun _ => hh.ne')).comp_aestronglyMeasurable
        hV.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact ae_of_all μ (fun x => by
        simpa [Real.norm_eq_abs, abs_div] using abs_diffQuot_exp_neg_mul_le hh (hVnonneg x))
    · exact hV
    · exact ae_of_all μ (fun x => tendsto_diffQuot_exp_neg_mul (v := V x))
  -- Step 2: on the right half-line the slope of the integral equals the integral of the
  -- pointwise difference quotients (`slope_integral_exp_neg_mul_eq_integral_diffQuot`), so the
  -- dominated-convergence limit is the slope limit, and `∫ -V = -∫ V` finishes the proof.
  exact (tendsto_congr' (slope_integral_exp_neg_mul_eq_integral_diffQuot (μ := μ) hVnonneg hV)).2
    (integral_neg V ▸ hDCT)

/-- Right derivative of the relative partition function at zero.

Informal proof: for nonnegative `ε` and `V`, differentiate the exponential pointwise and dominate
the difference quotient by `V`.  Dominated convergence gives the derivative `-∫ V`; probability
normalization gives `Z(0)=1`. -/
theorem hasDerivWithinAt_partitionFunction_zero [IsProbabilityMeasure μ]
    {V : Ω → ℝ} (hVnonneg : 0 ≤ V) (hV : Integrable V μ) :
    HasDerivWithinAt (partitionFunction μ V) (-(∫ x, V x ∂μ)) (Set.Ici 0) 0 :=
  hasDerivWithinAt_integral_exp_neg_mul_zero (μ := μ) hVnonneg hV

/-- On the punctured right half-line, the slope of the weighted numerator is the integral of
pointwise difference quotients.

This is the vector-valued analogue of `slope_integral_exp_neg_mul_eq_integral_diffQuot` above.
The proof is only algebra plus Bochner integral linearity: at `h > 0`, both weighted integrands are
integrable, so `integral_sub` and `integral_smul` move the difference quotient through the
integral. -/
private lemma slope_weightedIntegral_eq_integral_diffQuot
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hV : Integrable V μ) (hO : Integrable O μ) :
    (fun h : ℝ => slope (weightedIntegral μ V O) 0 h) =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ => ∫ x, ((Real.exp (-h * V x) - 1) / h) • O x ∂μ) := by
  filter_upwards [self_mem_nhdsWithin] with h hh
  have h_exp_meas : AEStronglyMeasurable
      (fun x : Ω => Real.exp (-h * V x)) μ :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
      hV.aestronglyMeasurable
  have h_exp_bound : ∀ᵐ x ∂μ, ‖Real.exp (-h * V x)‖ ≤ (1 : ℝ) :=
    ae_of_all μ (fun x => by
      simpa [Real.norm_eq_abs] using Real.exp_le_one_iff.2
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hh.le) (hVnonneg x)))
  have h_int_exp_smul : Integrable (fun x : Ω => Real.exp (-h * V x) • O x) μ :=
    hO.bdd_smul 1 h_exp_meas h_exp_bound
  calc
    slope (weightedIntegral μ V O) 0 h
        = h⁻¹ • ((∫ x, Real.exp (-h * V x) • O x ∂μ) - ∫ x, O x ∂μ) := by
            simp [slope_def_module, weightedIntegral]
    _ = ∫ x, ((Real.exp (-h * V x) - 1) / h) • O x ∂μ := by
            rw [← integral_sub h_int_exp_smul hO, ← integral_smul]
            exact integral_congr_ae (ae_of_all μ (fun x => by
              dsimp only
              rw [div_eq_inv_mul, smul_sub, smul_smul, ← sub_smul]
              exact congrArg (fun t : ℝ => t • O x) (by ring)))

-- Pointwise, the vector difference quotient of `fun h ↦ exp (-h * v) • z` at zero is dominated
-- by `‖v • z‖`.  This is the vector-valued analogue of `abs_diffQuot_exp_neg_mul_le`: the scalar
-- bound `|(exp (-h * v) - 1) / h| ≤ v` is multiplied through by the nonnegative factor `‖z‖`.
private lemma norm_smul_diffQuot_exp_neg_mul_le
    [NormedAddCommGroup E] [NormedSpace ℝ E] {h v : ℝ} {z : E}
    (hh : 0 < h) (hv : 0 ≤ v) :
    ‖((Real.exp (-h * v) - 1) / h) • z‖ ≤ ‖v • z‖ := by
  simpa [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hv] using
    mul_le_mul_of_nonneg_right (abs_diffQuot_exp_neg_mul_le hh hv) (norm_nonneg z)

-- Dominated convergence for the weighted difference quotients on the right half-line: the
-- quotients converge pointwise to `-V • O` (`tendsto_diffQuot_exp_neg_mul`), are dominated by the
-- integrable envelope `‖V • O‖` (`norm_smul_diffQuot_exp_neg_mul_le`), and are ae-strongly
-- measurable for `h > 0`.  `tendsto_integral_filter_of_dominated_convergence` then yields the
-- limit of the integrated quotients.
private lemma tendsto_integral_diffQuot_weighted
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hV : Integrable V μ) (hO : Integrable O μ)
    (hVO : Integrable (fun x ↦ V x • O x) μ) :
    Tendsto
      (fun h : ℝ => ∫ x, ((Real.exp (-h * V x) - 1) / h) • O x ∂μ)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (∫ x, (-V x) • O x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[Set.Ioi (0 : ℝ)] 0)
    (F := fun h x => ((Real.exp (-h * V x) - 1) / h) • O x)
    (f := fun x => (-V x) • O x)
    (fun x => ‖V x • O x‖) ?_ ?_ hVO.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact ((((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
      continuous_const).div continuous_const (fun _ => hh.ne')).comp_aestronglyMeasurable
        hV.aestronglyMeasurable).smul hO.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact ae_of_all μ (fun x => norm_smul_diffQuot_exp_neg_mul_le hh (hVnonneg x))
  · exact ae_of_all μ (fun x =>
      (tendsto_diffQuot_exp_neg_mul (v := V x)).smul_const (O x))

/-- Right derivative of an unnormalized weighted integral at zero.

Informal proof: differentiate `exp (-ε V x) • O x` pointwise.  On the right half-line the
difference quotient is dominated in norm by `‖V x • O x‖`; the hypothesis on `V • O` supplies the
integrable envelope, so dominated convergence gives the displayed derivative.  The extra
hypothesis `hV` supplies measurability of the scalar potential, which is needed to state the
Bochner dominated-convergence hypotheses for the difference quotients. -/
theorem hasDerivWithinAt_weightedIntegral_zero
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hV : Integrable V μ) (hO : Integrable O μ)
    (hVO : Integrable (fun x ↦ V x • O x) μ) :
    HasDerivWithinAt (weightedIntegral μ V O) (-(∫ x, V x • O x ∂μ))
      (Set.Ici 0) 0 := by
  -- The derivative is a limit of right difference quotients of the weighted numerator along the
  -- punctured right half-line (`hasDerivWithinAt_iff_tendsto_slope`).
  rw [← hasDerivWithinAt_Ioi_iff_Ici (x := 0),
    hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0 : ℝ)) (x := 0) (by simp)]
  -- Dominated convergence supplies the limit of the integrated difference quotients
  -- (`tendsto_integral_diffQuot_weighted`), which is the slope limit on the right half-line
  -- (`slope_weightedIntegral_eq_integral_diffQuot`); `∫ (-V) • O = -∫ V • O` finishes the proof.
  exact (tendsto_congr' (slope_weightedIntegral_eq_integral_diffQuot
      (μ := μ) hVnonneg hV hO)).2 (by
    simpa [integral_neg] using tendsto_integral_diffQuot_weighted (μ := μ) hVnonneg hV hO hVO)

-- For every coupling `ε`, the deformed expectation equals the normalized weighted numerator.
-- This is a pure notation conversion: `integral_deform` moves the tilt through the integral, and
-- `integral_smul` pulls the inverse partition function back inside, leaving the scalar times the
-- weighted integrand.  It is used by the linear-response theorem below to pass from the deformed
-- expectation to the quotient `Z⁻¹ • N` whose derivative is computed by
-- `hasDerivWithinAt_inv_partitionFunction_smul_weightedIntegral_zero`.
private lemma integral_deform_eq_inv_smul_weightedIntegral
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Ω → ℝ) (O : Ω → E) (ε : ℝ) :
    ∫ x, O x ∂deform μ V ε = (partitionFunction μ V ε)⁻¹ • weightedIntegral μ V O ε := by
  rw [integral_deform]
  dsimp [weightedIntegral]
  rw [← integral_smul]
  exact integral_congr_ae (ae_of_all μ (fun x => by
    simp [div_eq_mul_inv, mul_comm, smul_smul]))

-- The quotient rule at zero for the normalized weighted numerator `Z⁻¹ • N`, where
-- `Z = partitionFunction μ V` and `N = weightedIntegral μ V O`.  The reciprocal of the partition
-- function has derivative `∫ V` at zero because `Z 0 = 1`; the product rule then leaves
-- `-covarianceWith μ O V` as the derivative, using `N 0 = ∫ O` and the known derivatives of
-- `Z` and `N` from `hasDerivWithinAt_partitionFunction_zero` and
-- `hasDerivWithinAt_weightedIntegral_zero`.
private lemma hasDerivWithinAt_inv_partitionFunction_smul_weightedIntegral_zero
    [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : Ω → ℝ} {O : Ω → E} (hVnonneg : 0 ≤ V)
    (hV : Integrable V μ) (hO : Integrable O μ)
    (hVO : Integrable (fun x ↦ V x • O x) μ) :
    HasDerivWithinAt
      (fun ε : ℝ => (partitionFunction μ V ε)⁻¹ • weightedIntegral μ V O ε)
      (-covarianceWith μ O V) (Set.Ici 0) 0 := by
  let Z : ℝ → ℝ := partitionFunction μ V
  let N : ℝ → E := weightedIntegral μ V O
  have hZ0 : Z 0 = 1 := by
    simp [Z, partitionFunction]
  have hN0 : N 0 = ∫ x, O x ∂μ := by
    simp [N, weightedIntegral]
  have hN' : HasDerivWithinAt N (-(∫ x, V x • O x ∂μ)) (Set.Ici 0) 0 :=
    hasDerivWithinAt_weightedIntegral_zero (μ := μ) hVnonneg hV hO hVO
  have hZ' : HasDerivWithinAt Z (-(∫ x, V x ∂μ)) (Set.Ici 0) 0 :=
    hasDerivWithinAt_partitionFunction_zero (μ := μ) hVnonneg hV
  have hZinv' : HasDerivWithinAt Z⁻¹ (∫ x, V x ∂μ) (Set.Ici 0) 0 := by
    simpa [hZ0] using hZ'.inv (by simp [hZ0])
  have hprod : HasDerivWithinAt (Z⁻¹ • N) (-covarianceWith μ O V) (Set.Ici 0) 0 := by
    simpa [Z, N, hZ0, hN0, covarianceWith, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hZinv'.smul hN'
  simpa [Z, N, Pi.smul_def'] using hprod

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
  -- The deformed expectation equals the normalized numerator for every coupling
  -- (`integral_deform`), so the two functions agree on a neighborhood of zero and their
  -- derivatives coincide at zero.
  exact (hasDerivWithinAt_inv_partitionFunction_smul_weightedIntegral_zero (μ := μ)
      hVnonneg hV hO hVO).congr
    (fun ε _hε => integral_deform_eq_inv_smul_weightedIntegral (μ := μ) V O ε)
    (integral_deform_eq_inv_smul_weightedIntegral (μ := μ) V O 0)

/-! ## Quadratic remainders -/

-- For `t ≥ 0` the exponential satisfies the quadratic upper bound
-- `exp (-t) ≤ 1 - t + t ^ 2 / 2`.  Multiply the quadratic lower bound
-- `exp t ≥ 1 + t + t ^ 2 / 2` (`Real.quadratic_le_exp_of_nonneg`) by the nonnegative factor
-- `1 - t + t ^ 2 / 2`; the algebraic inequality
-- `(1 - t + t²/2) * (1 + t + t²/2) ≥ 1` then yields `1 ≤ (1 - t + t²/2) * exp t`, and inverting
-- through `Real.exp_neg` (`inv_le_iff_one_le_mul₀`) gives the claim.
private lemma exp_neg_le_one_sub_add {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos t)]
  nlinarith [sq_nonneg (t - 1), sq_nonneg (t ^ 2 / 2), Real.quadratic_le_exp_of_nonneg ht]

/-- Scalar Taylor bound for the exponential remainder on the nonnegative half-line.

Informal proof: Taylor's theorem with integral remainder gives
`exp (-t) = 1 - t + ∫ s in 0..t, (t - s) * exp (-s)`.  If `0 ≤ t`, then
`0 ≤ exp (-s) ≤ 1` for `s ∈ [0,t]`, hence the absolute value of the remainder is at most
`∫ s in 0..t, (t - s) = t ^ 2 / 2`.  Equivalently, the function
`1 - t + t ^ 2 / 2 - exp (-t)` has nonnegative second derivative on `[0,∞)` and vanishes to
first order at zero.  This is the scalar estimate used in the blueprint proof of the quadratic
response theorem. -/
private lemma abs_exp_neg_sub_one_add_le {t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-t) - 1 + t| ≤ t ^ 2 / 2 := by
  rw [abs_of_nonneg (by linarith [Real.one_sub_le_exp_neg t])]
  linarith [exp_neg_le_one_sub_add ht]

-- For `ε ≥ 0` and `v ≥ 0`, the quadratic Taylor remainder of `exp` at `t = ε * v` is bounded
-- by `(ε²/2) * v²`.  This is `abs_exp_neg_sub_one_add_le` with `t = ε * v`, multiplied out;
-- the product form is what survives integration against `V²` in the quadratic-response bounds.
private lemma abs_exp_neg_mul_add_le {ε v : ℝ} (hε : 0 ≤ ε) (hv : 0 ≤ v) :
    |Real.exp (-(ε * v)) - 1 + ε * v| ≤ (ε ^ 2 / 2) * v ^ 2 := by
  calc
    |Real.exp (-(ε * v)) - 1 + ε * v| ≤ (ε * v) ^ 2 / 2 :=
      abs_exp_neg_sub_one_add_le (mul_nonneg hε hv)
    _ = (ε ^ 2 / 2) * v ^ 2 := by ring

-- The partition-function linear remainder equals the integral of the pointwise remainder:
-- `Z(ε) - 1 + ε ∫ V = ∫ (exp (-ε V) - 1 + ε V)`.  This is Bochner-integral linearity
-- (`integral_sub`, `integral_const_mul`, `integral_add`) together with the probability
-- normalization `∫ 1 = 1`; the integrability of the tilted exponential is passed in as `hExp`.
private lemma integral_partitionFunction_sub_linear [IsProbabilityMeasure μ]
    {V : Ω → ℝ} {ε : ℝ}
    (hExp : Integrable (fun x : Ω ↦ Real.exp (-ε * V x)) μ)
    (hV : Integrable V μ) :
    partitionFunction μ V ε - 1 + ε * ∫ x, V x ∂μ =
      ∫ x, (Real.exp (-ε * V x) - 1 + ε * V x) ∂μ := by
  calc
    partitionFunction μ V ε - 1 + ε * ∫ x, V x ∂μ
        = (∫ x, Real.exp (-ε * V x) ∂μ) - (∫ x, (1 : ℝ) ∂μ) +
            ε * ∫ x, V x ∂μ := by
            simp [partitionFunction]
    _ = ∫ x, (Real.exp (-ε * V x) - 1) ∂μ + ε * ∫ x, V x ∂μ := by
            rw [integral_sub hExp (integrable_const (1 : ℝ))]
    _ = ∫ x, (Real.exp (-ε * V x) - 1) ∂μ + ∫ x, ε * V x ∂μ := by
            rw [integral_const_mul]
    _ = ∫ x, Real.exp (-ε * V x) - 1 + ε * V x ∂μ :=
            (integral_add (hExp.sub (integrable_const (1 : ℝ))) (hV.const_mul ε)).symm

/-- Integrated quadratic bound for the partition-function remainder.

Informal proof: for `t ≥ 0`, Taylor's theorem with the Lagrange (or integral) remainder gives
`|exp (-t) - 1 + t| ≤ t ^ 2 / 2`.  With `t = ε * V x`, using `ε ≥ 0` and `V x ≥ 0`, this yields
`|exp (-ε * V x) - 1 + ε * V x| ≤ (ε ^ 2 / 2) * V x ^ 2`.  The left-hand side of the displayed
estimate is the norm of the integral of this pointwise remainder (by linearity of the Bochner
integral and `μ univ = 1`).  Finally, `norm_integral_le_integral_norm`, integral monotonicity, and
integrability of `V²` give the claimed bound.  This is the standard second-order Taylor remainder
argument recorded in `blueprint/src/chapters/renormalization.tex`, Theorem
`thm:renorm:quadraticResponse`. -/
private lemma norm_partitionFunction_sub_linear_le [IsProbabilityMeasure μ]
    {V : Ω → ℝ} (hVnonneg : 0 ≤ V) (hV : Integrable V μ)
    (hV2 : Integrable (fun x ↦ V x ^ 2) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖partitionFunction μ V ε - 1 + ε * ∫ x, V x ∂μ‖ ≤
      ((∫ x, V x ^ 2 ∂μ) / 2) * ‖ε ^ 2‖ := by
  have hExp := integrable_exp_neg_mul_nonneg hV.aestronglyMeasurable hVnonneg hε
  -- Rewrite the linear remainder as the integral of the pointwise remainder
  -- (`integral_partitionFunction_sub_linear`); this is Bochner-integral linearity.
  rw [integral_partitionFunction_sub_linear hExp hV]
  let R : Ω → ℝ := fun x ↦ Real.exp (-ε * V x) - 1 + ε * V x
  let B : Ω → ℝ := fun x ↦ (ε ^ 2 / 2) * V x ^ 2
  have hR : Integrable R μ := (hExp.sub (integrable_const (1 : ℝ))).add (hV.const_mul ε)
  have hB : Integrable B μ := hV2.const_mul (ε ^ 2 / 2)
  -- Pointwise domination `‖R x‖ ≤ B x` via the scalar Taylor bound
  -- (`abs_exp_neg_mul_add_le`) applied with `v = V x`.
  have hRB : ∀ᵐ x ∂μ, ‖R x‖ ≤ B x :=
    ae_of_all μ (fun x ↦ by simpa [R, B] using abs_exp_neg_mul_add_le hε (hVnonneg x))
  -- `norm_integral_le_integral_norm` and integral monotonicity push the bound through the
  -- integral; `∫ B = (ε²/2) * ∫ V²` and `‖ε²‖ = ε²` finish the computation.
  calc
    ‖∫ x, R x ∂μ‖ ≤ ∫ x, ‖R x‖ ∂μ := norm_integral_le_integral_norm R
    _ ≤ ∫ x, B x ∂μ := integral_mono_ae hR.norm hB hRB
    _ = ((∫ x, V x ^ 2 ∂μ) / 2) * ‖ε ^ 2‖ := by
          rw [show (∫ x, B x ∂μ) = (ε ^ 2 / 2) * ∫ x, V x ^ 2 ∂μ by
            simp [B, integral_const_mul], Real.norm_of_nonneg (sq_nonneg ε)]
          ring

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
  exact Asymptotics.IsBigO.of_bound ((∫ x, V x ^ 2 ∂μ) / 2) (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_partitionFunction_sub_linear_le (μ := μ) hVnonneg hV hV2 hε)

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
