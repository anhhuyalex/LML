/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Integrability of a series of nonnegative integrable functions

If `fᵢ ≥ 0` are measurable and integrable, indexed by a countable type, and `∑ᵢ ∫ fᵢ < ∞`, then
the series `∑ᵢ fᵢ a` converges for almost every `a` and its sum is integrable.  (Mathlib has the
interchange `∫ ∑' fᵢ = ∑' ∫ fᵢ` under this hypothesis, but not the integrability of the sum
nor the almost sure summability.)

## Main declarations

* `MeasureTheory.ae_summable_and_integrable_tsum_of_nonneg`: the statement above.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- **A convergent series of nonnegative integrable functions** converges almost everywhere to an
integrable function. -/
theorem ae_summable_and_integrable_tsum_of_nonneg {α ι : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [Countable ι] {f : ι → α → ℝ} (hm : ∀ i, AEMeasurable (f i) μ)
    (h0 : ∀ i a, 0 ≤ f i a) (hint : ∀ i, Integrable (f i) μ)
    (hsum : Summable fun i => ∫ a, f i a ∂μ) :
    (∀ᵐ a ∂μ, Summable fun i => f i a) ∧ Integrable (fun a => ∑' i, f i a) μ := by
  have hg : ∀ i, AEMeasurable (fun a => ENNReal.ofReal (f i a)) μ :=
    fun i => (hm i).ennreal_ofReal
  have hl : ∫⁻ a, ∑' i, ENNReal.ofReal (f i a) ∂μ ≠ ∞ := by
    rw [lintegral_tsum hg]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hint _) (Filter.Eventually.of_forall (h0 _))]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (h0 i)) hsum]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ a ∂μ, ∑' i, ENNReal.ofReal (f i a) ≠ ∞ :=
    (ae_lt_top' (AEMeasurable.tsum hg) hl).mono fun _ h => h.ne
  have hsumm : ∀ᵐ a ∂μ, Summable fun i => f i a := hae.mono fun a ha => by
    simpa [ENNReal.toReal_ofReal (h0 _ _)] using ENNReal.summable_toReal ha
  refine ⟨hsumm, (AEMeasurable.tsum hm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun a => tsum_nonneg (h0 · a))]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr_ae (hsumm.mono fun a ha => ?_)))
    (lt_top_iff_ne_top.2 hl)
  exact ENNReal.ofReal_tsum_of_nonneg (h0 · a) ha

end MeasureTheory
