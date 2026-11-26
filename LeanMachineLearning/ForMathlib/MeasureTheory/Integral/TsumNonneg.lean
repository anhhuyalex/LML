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
# Integrability of a series of integrable functions

If the `fᵢ`, indexed by a countable type, are integrable with `∑ᵢ ∫ ‖fᵢ‖ < ∞`, then the series
`∑ᵢ fᵢ a` converges for almost every `a` and its sum is integrable.  (Mathlib has the
interchange `∫ ∑' fᵢ = ∑' ∫ fᵢ` under this hypothesis, but not the integrability of the sum
nor the almost sure summability.)

## Main declarations

* `MeasureTheory.ae_summable_and_integrable_tsum_of_summable_integral_norm`: the statement above,
  for values in a Banach space.
* `MeasureTheory.ae_summable_and_integrable_tsum_of_nonneg`: the case of nonnegative functions.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- **A series of integrable functions whose integrals of norms are summable** converges almost
everywhere to an integrable function. -/
theorem ae_summable_and_integrable_tsum_of_summable_integral_norm {α ι E : Type*}
    {m : MeasurableSpace α} {μ : Measure α} [Countable ι] [NormedAddCommGroup E]
    [CompleteSpace E] {f : ι → α → E} (hint : ∀ i, Integrable (f i) μ)
    (hsum : Summable fun i => ∫ a, ‖f i a‖ ∂μ) :
    (∀ᵐ a ∂μ, Summable fun i => f i a) ∧ Integrable (fun a => ∑' i, f i a) μ := by
  have hg : ∀ i, AEMeasurable (fun a => ‖f i a‖ₑ) μ := fun i => (hint i).aestronglyMeasurable.enorm
  have hl : ∫⁻ a, ∑' i, ‖f i a‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum hg]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hint _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _) hsum]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ a ∂μ, ∑' i, ‖f i a‖ₑ < ∞ := ae_lt_top' (AEMeasurable.tsum hg) hl
  have hsumm : ∀ᵐ a ∂μ, Summable fun i => f i a := hae.mono fun a ha =>
    Summable.of_enorm ha.ne
  have hm : AEStronglyMeasurable (fun a => ∑' i, f i a) μ := by
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (f := fun s a => ∑ i ∈ s, f i a) (fun s => ?_) (hsumm.mono fun a ha => ha.hasSum)
    exact Finset.aestronglyMeasurable_fun_sum s fun i _ => (hint i).aestronglyMeasurable
  refine ⟨hsumm, hm, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_ae (hae.mono fun a ha => ?_)) (lt_top_iff_ne_top.2 hl)
  exact enorm_tsum_le_tsum_enorm

/-- **A convergent series of nonnegative integrable functions** converges almost everywhere to an
integrable function, with nonnegativity almost everywhere. -/
theorem ae_summable_and_integrable_tsum_of_ae_nonneg {α ι : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [Countable ι] {f : ι → α → ℝ} (h0 : ∀ i, 0 ≤ᵐ[μ] f i)
    (hint : ∀ i, Integrable (f i) μ) (hsum : Summable fun i => ∫ a, f i a ∂μ) :
    (∀ᵐ a ∂μ, Summable fun i => f i a) ∧ Integrable (fun a => ∑' i, f i a) μ :=
  ae_summable_and_integrable_tsum_of_summable_integral_norm hint <| hsum.congr fun i =>
    integral_congr_ae <| (h0 i).mono fun _ h => (Real.norm_of_nonneg h).symm

/-- **A convergent series of nonnegative integrable functions** converges almost everywhere to an
integrable function. -/
theorem ae_summable_and_integrable_tsum_of_nonneg {α ι : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [Countable ι] {f : ι → α → ℝ} (h0 : ∀ i a, 0 ≤ f i a)
    (hint : ∀ i, Integrable (f i) μ)
    (hsum : Summable fun i => ∫ a, f i a ∂μ) :
    (∀ᵐ a ∂μ, Summable fun i => f i a) ∧ Integrable (fun a => ∑' i, f i a) μ :=
  ae_summable_and_integrable_tsum_of_ae_nonneg (fun i => ae_of_all _ (h0 i)) hint hsum

end MeasureTheory
