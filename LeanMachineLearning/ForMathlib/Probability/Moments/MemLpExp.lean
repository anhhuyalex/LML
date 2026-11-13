/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# `L^p` membership of exponentials from exponential integrability

If `exp ((p c) X)` is integrable then `exp (c X)` lies in `L^p`, for any measure and any `p > 0`.
No sub-exponential or sub-Gaussian assumption is needed.

## Main declarations

* `ProbabilityTheory.memLp_exp_mul_of_integrable_exp_mul`
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- If `exp ((p * c) * X)` is integrable for some `p > 0`, then `exp (c * X)` lies in `L^p`. -/
lemma memLp_exp_mul_of_integrable_exp_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) {p c : ℝ} (hp : 0 < p)
    (hi : Integrable (fun ω => Real.exp ((p * c) * X ω)) μ) :
    MemLp (fun ω => Real.exp (c * X ω)) (ENNReal.ofReal p) μ := by
  have hm := Real.continuous_exp.comp_aestronglyMeasurable (hX.const_mul c)
  refine (integrable_norm_rpow_iff hm (by simpa using hp) ENNReal.ofReal_ne_top).1 ?_
  convert hi using 1
  funext ω
  rw [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_mul]
  congr 1
  ring

end ProbabilityTheory
