/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Integral

/-!
# Jensen's inequality for the norm to a power

## Main statements

* `norm_integral_rpow_le_integral_norm_rpow`: for a probability measure `μ` and `1 ≤ p < ∞`,
  `‖∫ x, f x ∂μ‖ ^ p ≤ ∫ x, ‖f x‖ ^ p ∂μ`.
* `sq_norm_integral_le_integral_sq_norm`: the case `p = 2`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- **Jensen's inequality** for the convex function `x ↦ ‖x‖ ^ p`, `1 ≤ p`. -/
lemma norm_integral_rpow_le_integral_norm_rpow
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ) :
    ‖∫ x, f x ∂μ‖ ^ p.toReal ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := by positivity
  have hp1' : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp1
  calc ‖∫ x, f x ∂μ‖ ^ p.toReal
  _ ≤ (∫ x, ‖f x‖ ∂μ) ^ p.toReal := by
    gcongr
    exact norm_integral_le_integral_norm _
  _ ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
    ConvexOn.map_integral_le (convexOn_rpow hp1')
      (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
      (ae_of_all _ fun x ↦ norm_nonneg _) (hf.integrable hp1).norm
      ((integrable_norm_rpow_iff hf.aestronglyMeasurable hp0 hp_top).mpr hf)

/-- The squared norm of a mean is at most the mean of the squared norm. -/
lemma sq_norm_integral_le_integral_sq_norm
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    norm_integral_rpow_le_integral_norm_rpow one_le_two ENNReal.ofNat_ne_top hf

/-- **Concave Jensen's inequality for `x ↦ x ^ p` with `0 ≤ p ≤ 1`:** for an a.e. nonnegative
integrable `f` under a probability measure `μ`, `f ^ p` is integrable and
`∫ x, f x ^ p ∂μ ≤ (∫ x, f x ∂μ) ^ p`. -/
lemma integral_rpow_le_rpow_integral
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hf0 : 0 ≤ᵐ[μ] f)
    (hf : Integrable f μ) :
    Integrable (fun x => f x ^ p) μ ∧ ∫ x, f x ^ p ∂μ ≤ (∫ x, f x ∂μ) ^ p := by
  have hnorm_p : Integrable (fun x => ‖f x‖ ^ p) μ :=
    integrable_norm_rpow_of_le hf.aestronglyMeasurable hp0 zero_le_one hp1
      (by simpa only [Real.rpow_one] using hf.norm)
  have hfp : Integrable (fun x => f x ^ p) μ :=
    hnorm_p.congr (hf0.mono fun x hx => by rw [Real.norm_of_nonneg hx])
  refine ⟨hfp, ?_⟩
  exact ConcaveOn.le_map_integral (Real.concaveOn_rpow hp0 hp1)
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici hf0 hf hfp
