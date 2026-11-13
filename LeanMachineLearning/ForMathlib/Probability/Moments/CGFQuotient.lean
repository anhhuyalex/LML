/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.CGFConvex
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Difference quotients of cumulant-generating functions and real moments

This file develops the limit of `(1 / t) * cgf X μ t` and `(1 / t) * log ∫ Z^t ∂μ` as `t → 0+`.

When `0 ∈ interior (integrableExpSet X μ)` on a probability space, `cgf X μ` is analytic at 0,
`cgf X μ 0 = 0`, and `deriv (cgf X μ) 0 = ∫ X ∂μ`. By the definition of derivative as the limit of
difference quotients, `(cgf X μ t) / t → ∫ X ∂μ` as `t → 0`.

For a positive random variable `Z`, this yields the finite-system real-moment limit
`(1 / t) * log ∫ Z^t ∂μ → ∫ log Z ∂μ` as `t → 0+`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- If `exp (t * X)` is integrable for all `t` in an open ball around `0`, then `0` belongs to
the interior of the exponential integrability set. -/
lemma mem_interior_integrableExpSet_of_ball {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t ∈ Metric.ball (0 : ℝ) ε, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    0 ∈ interior (integrableExpSet X μ) := by
  have hsub : Metric.ball (0 : ℝ) ε ⊆ integrableExpSet X μ := fun t ht => h t ht
  exact interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self hε)

/-- If `exp (t * X)` is integrable for all `t : ℝ`, then `0` belongs to the interior of
`integrableExpSet X μ`. -/
lemma mem_interior_integrableExpSet_of_forall
    (h : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    0 ∈ interior (integrableExpSet X μ) := by
  have : integrableExpSet X μ = Set.univ := Set.eq_univ_of_forall h
  rw [this, interior_univ]
  exact Set.mem_univ 0

/-- On a probability space, the derivative of `cgf X μ` at 0 is the expectation `∫ X ∂μ`. -/
theorem hasDerivAt_cgf_zero [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (cgf X μ) (∫ ω, X ω ∂μ) 0 := by
  simpa only [deriv_cgf_zero h, probReal_univ, div_one]
    using (analyticAt_cgf h).differentiableAt.hasDerivAt

/-- The difference quotient `cgf X μ t / t` tends to `∫ X ∂μ` as `t → 0` along `𝓝[≠] 0`. -/
theorem tendsto_cgf_div_zero [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    Tendsto (fun t => cgf X μ t / t) (𝓝[≠] 0) (𝓝 (∫ ω, X ω ∂μ)) := by
  simpa only [zero_add, cgf_zero, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm]
    using (hasDerivAt_cgf_zero h).tendsto_slope_zero

/-- The difference quotient `cgf X μ t / t` tends to `∫ X ∂μ` as `t → 0+`. -/
theorem tendsto_cgf_div_zero_pos [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    Tendsto (fun t => cgf X μ t / t) (𝓝[>] 0) (𝓝 (∫ ω, X ω ∂μ)) :=
  (tendsto_cgf_div_zero h).mono_left (nhdsGT_le_nhdsNE 0)

/-- The quotient `(1 / t) * log ∫ exp (t * X) ∂μ` tends to `∫ X ∂μ` as `t → 0+`. -/
theorem tendsto_log_integral_exp_mul_div_zero_pos [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    Tendsto (fun t => Real.log (∫ ω, Real.exp (t * X ω) ∂μ) / t)
      (𝓝[>] 0) (𝓝 (∫ ω, X ω ∂μ)) :=
  tendsto_cgf_div_zero_pos h

/-- For a positive random variable `Z`, `(1 / t) * log ∫ Z^t ∂μ` tends to `∫ log Z ∂μ`
as `t → 0+`. -/
theorem tendsto_log_integral_rpow_div_zero_pos [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : ∀ᵐ ω ∂μ, 0 < Z ω)
    (h : 0 ∈ interior (integrableExpSet (fun ω => Real.log (Z ω)) μ)) :
    Tendsto (fun t => Real.log (∫ ω, Z ω ^ t ∂μ) / t)
      (𝓝[>] 0) (𝓝 (∫ ω, Real.log (Z ω) ∂μ)) := by
  have htend := tendsto_log_integral_exp_mul_div_zero_pos (X := fun ω => Real.log (Z ω)) h
  refine htend.congr fun t => ?_
  rw [integral_rpow_eq_mgf_log hZ]
  rfl

end ProbabilityTheory
