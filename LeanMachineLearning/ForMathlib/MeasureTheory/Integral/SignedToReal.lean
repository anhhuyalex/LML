/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A real integral as a function of two lower integrals

The Bochner integral of a measurable `g : β → ℝ` is `∫⁻ ofReal g - ∫⁻ ofReal (-g)` (read in `ℝ`)
when both are finite, and `0` otherwise. This expresses it as a *measurable function* of the two
`ℝ≥0∞`-valued integrals, which is what is needed to transport equalities in law.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

/-- The real-valued difference of two `ℝ≥0∞` numbers, `0` unless both are finite. -/
noncomputable def signedToReal (a b : ℝ≥0∞) : ℝ :=
  if a ≠ ∞ ∧ b ≠ ∞ then a.toReal - b.toReal else 0

/-- The Bochner integral of a measurable real function through its positive and negative parts. -/
theorem integral_eq_signedToReal_lintegral {β : Type*} [MeasurableSpace β] (μ : Measure β)
    {g : β → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂μ =
      signedToReal (∫⁻ x, ENNReal.ofReal (g x) ∂μ) (∫⁻ x, ENNReal.ofReal (-g x) ∂μ) := by
  by_cases hi : Integrable g μ
  · have hp : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≠ ∞ :=
      ((lintegral_mono fun a => Real.ofReal_le_enorm (g a)).trans_lt hi.2).ne
    have hn : ∫⁻ x, ENNReal.ofReal (-g x) ∂μ ≠ ∞ :=
      ((lintegral_mono fun a => (Real.ofReal_le_enorm (-g a)).trans_eq (enorm_neg _))
        |>.trans_lt hi.2).ne
    simp only [signedToReal, hp, hn, ne_eq, not_false_eq_true, and_self, ite_true]
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
  · rw [integral_undef hi, signedToReal]
    refine (ite_eq_right_iff.2 fun h => ?_).symm
    exfalso
    obtain ⟨hp, hn⟩ := h
    refine hi ⟨hg.aestronglyMeasurable, ?_⟩
    have : ∀ a, ‖g a‖ₑ = ENNReal.ofReal (g a) + ENNReal.ofReal (-g a) := fun a => by
      rw [Real.enorm_eq_ofReal_abs]
      rcases le_total 0 (g a) with h | h
      · simp [abs_of_nonneg h, ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 h)]
      · simp [abs_of_nonpos h, ENNReal.ofReal_eq_zero.2 h]
    simp_rw [HasFiniteIntegral, this]
    rw [lintegral_add_left hg.ennreal_ofReal]
    exact ENNReal.add_lt_top.2 ⟨hp.lt_top, hn.lt_top⟩

/-- `signedToReal` is measurable. -/
theorem measurable_signedToReal : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => signedToReal p.1 p.2 := by
  unfold signedToReal
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact ((measurableSet_singleton ∞).compl.preimage measurable_fst).inter
    ((measurableSet_singleton ∞).compl.preimage measurable_snd)

end MeasureTheory
