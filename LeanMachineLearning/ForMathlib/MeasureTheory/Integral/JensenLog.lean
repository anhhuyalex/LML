/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Jensen's inequality for the logarithm

`𝔼 log f ≤ log 𝔼 f` for a positive integrable `f` with integrable logarithm on a probability
space, from the elementary bound `log x ≤ x / c + log c - 1`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- **Jensen for the logarithm:** for an a.e. positive integrable `f` with integrable logarithm
on a probability space, `𝔼 log f ≤ log 𝔼 f`.  (From `log x ≤ x / c + log c - 1`.) -/
theorem integral_log_le_log_integral_of_ae_pos {Ω' : Type*} {m : MeasurableSpace Ω'}
    {P : Measure Ω'} [IsProbabilityMeasure P] {f : Ω' → ℝ} (hpos : ∀ᵐ ω ∂P, 0 < f ω)
    (hf : Integrable f P)
    (hlog : Integrable (fun ω => Real.log (f ω)) P) :
    ∫ ω, Real.log (f ω) ∂P ≤ Real.log (∫ ω, f ω ∂P) := by
  have hc : 0 < ∫ ω, f ω ∂P := by
    refine (integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le) hf).2 ?_
    have : Function.support f =ᵐ[P] Set.univ :=
      Filter.eventuallyEqSet_univ.2 (hpos.mono fun _ h => h.ne')
    rw [measure_congr this]
    simp
  set c := ∫ ω, f ω ∂P
  have hpt : ∀ᵐ ω ∂P, Real.log (f ω) ≤ f ω / c - 1 + Real.log c := hpos.mono fun ω h => by
    have := Real.log_le_sub_one_of_pos (div_pos h hc)
    rw [Real.log_div h.ne' hc.ne'] at this
    linarith
  calc ∫ ω, Real.log (f ω) ∂P ≤ ∫ ω, (f ω / c - 1 + Real.log c) ∂P :=
        integral_mono_ae hlog
          (((hf.div_const c).sub (integrable_const _)).add (integrable_const _)) hpt
    _ = Real.log c := by
        have h1 : Integrable (fun ω => f ω / c - 1) P :=
          (hf.div_const c).sub (integrable_const _)
        rw [integral_add h1 (integrable_const _),
          integral_sub (hf.div_const c) (integrable_const _), integral_div]
        have e : (∫ ω, f ω ∂P) / c = 1 := div_self hc.ne'
        simp [e]

/-- **Jensen for the logarithm:** for a positive integrable `f` with integrable logarithm on a
probability space, `𝔼 log f ≤ log 𝔼 f`. -/
theorem integral_log_le_log_integral {Ω' : Type*} {m : MeasurableSpace Ω'} {P : Measure Ω'}
    [IsProbabilityMeasure P] {f : Ω' → ℝ} (hpos : ∀ ω, 0 < f ω) (hf : Integrable f P)
    (hlog : Integrable (fun ω => Real.log (f ω)) P) :
    ∫ ω, Real.log (f ω) ∂P ≤ Real.log (∫ ω, f ω ∂P) :=
  integral_log_le_log_integral_of_ae_pos (ae_of_all _ hpos) hf hlog

end MeasureTheory
