/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.MemLpExp
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Convexity of the cumulant-generating function

For a random variable `X` on a probability space, the cumulant-generating function
`t ↦ log 𝔼 exp (t X)` is convex on the interval `integrableExpSet X μ` where the exponential
moments are finite.  This is Hölder's inequality `𝔼 exp ((a s + b t) X) ≤ (𝔼 exp (s X))^a
(𝔼 exp (t X))^b` for `a + b = 1`.

## Main declarations

* `ProbabilityTheory.mgf_add_le_rpow_mul_rpow`: the Hölder inequality for the moment-generating
  function.
* `ProbabilityTheory.convexOn_cgf`: convexity of `cgf X μ` on `integrableExpSet X μ`.
* `ProbabilityTheory.integral_rpow_eq_mgf_log` and
  `ProbabilityTheory.convexOn_log_integral_rpow`: the same for the real moments `t ↦ log 𝔼 Z^t` of a
  positive random variable `Z`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- **Hölder's inequality for the moment-generating function:** for `a, b > 0` with `a + b = 1`,
`mgf X μ (a s + b t) ≤ (mgf X μ s) ^ a * (mgf X μ t) ^ b` when both exponential moments are
finite. -/
theorem mgf_add_le_rpow_mul_rpow (hX : AEMeasurable X μ) {a b s t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hs : Integrable (fun ω => Real.exp (s * X ω)) μ)
    (ht : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ (a * s + b * t) ≤ mgf X μ s ^ a * mgf X μ t ^ b := by
  have hpq := Real.HolderConjugate.inv_inv ha hb hab
  set f : Ω → ℝ := fun ω => Real.exp ((a * s) * X ω) with hf
  set g : Ω → ℝ := fun ω => Real.exp ((b * t) * X ω) with hg
  have hfp : ∀ ω, f ω ^ a⁻¹ = Real.exp (s * X ω) := fun ω => by
    rw [hf, ← Real.exp_mul]; congr 1; field_simp
  have hgq : ∀ ω, g ω ^ b⁻¹ = Real.exp (t * X ω) := fun ω => by
    rw [hg, ← Real.exp_mul]; congr 1; field_simp
  have hfL : MemLp f (ENNReal.ofReal a⁻¹) μ :=
    memLp_exp_mul_of_integrable_exp_mul hX.aestronglyMeasurable (inv_pos.2 ha)
      (by simpa only [inv_mul_cancel_left₀ ha.ne'] using hs)
  have hgL : MemLp g (ENNReal.ofReal b⁻¹) μ :=
    memLp_exp_mul_of_integrable_exp_mul hX.aestronglyMeasurable (inv_pos.2 hb)
      (by simpa only [inv_mul_cancel_left₀ hb.ne'] using ht)
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hfL hgL
  have hfg : ∀ ω, f ω * g ω = Real.exp ((a * s + b * t) * X ω) := fun ω => by
    rw [hf, hg, ← Real.exp_add]; congr 1; ring
  have e1 : (∫ ω, f ω * g ω ∂μ) = mgf X μ (a * s + b * t) :=
    integral_congr_ae (Filter.Eventually.of_forall hfg)
  have e2 : (∫ ω, f ω ^ a⁻¹ ∂μ) = mgf X μ s := integral_congr_ae (Filter.Eventually.of_forall hfp)
  have e3 : (∫ ω, g ω ^ b⁻¹ ∂μ) = mgf X μ t := integral_congr_ae (Filter.Eventually.of_forall hgq)
  rw [e1, e2, e3, one_div, one_div, inv_inv, inv_inv] at key
  exact key

/-- **Convexity of the cumulant-generating function** on the interval where the exponential moments
are finite. -/
theorem convexOn_cgf [IsProbabilityMeasure μ] (hX : AEMeasurable X μ) :
    ConvexOn ℝ (integrableExpSet X μ) (cgf X μ) := by
  refine ⟨convex_integrableExpSet, fun s hs t ht a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    simp
  have hmem := convex_integrableExpSet hs ht ha hb hab
  have hH := mgf_add_le_rpow_mul_rpow hX ha' hb' hab hs ht
  have hp0 := mgf_pos hs
  have hp1 := mgf_pos ht
  have hp2 := mgf_pos hmem
  simp only [cgf, smul_eq_mul]
  calc Real.log (mgf X μ (a * s + b * t)) ≤ Real.log (mgf X μ s ^ a * mgf X μ t ^ b) :=
        Real.log_le_log hp2 hH
    _ = a * Real.log (mgf X μ s) + b * Real.log (mgf X μ t) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hp0 a).ne' (Real.rpow_pos_of_pos hp1 b).ne',
          Real.log_rpow hp0, Real.log_rpow hp1]

/-- The real moment `∫ Z^t` of a positive random variable is the moment-generating function of
`log Z` at `t`. -/
theorem integral_rpow_eq_mgf_log {Z : Ω → ℝ} (hZ : ∀ᵐ ω ∂μ, 0 < Z ω) (t : ℝ) :
    ∫ ω, Z ω ^ t ∂μ = mgf (fun ω => Real.log (Z ω)) μ t := by
  refine integral_congr_ae ?_
  filter_upwards [hZ] with ω hω
  rw [Real.rpow_def_of_pos hω, mul_comm]

/-- **Convexity of the log real moments:** for a positive random variable `Z`, the map
`t ↦ log ∫ Z^t ∂μ` is convex on the interval where `Z^t` is integrable. -/
theorem convexOn_log_integral_rpow [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : ∀ᵐ ω ∂μ, 0 < Z ω) (hm : AEMeasurable Z μ) :
    ConvexOn ℝ (integrableExpSet (fun ω => Real.log (Z ω)) μ)
      (fun t => Real.log (∫ ω, Z ω ^ t ∂μ)) := by
  have h := convexOn_cgf (μ := μ) (X := fun ω => Real.log (Z ω)) hm.log
  refine h.congr fun t _ => ?_
  rw [cgf, integral_rpow_eq_mgf_log hZ]

end ProbabilityTheory
