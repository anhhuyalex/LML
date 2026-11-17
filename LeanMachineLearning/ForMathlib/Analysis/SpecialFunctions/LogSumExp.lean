/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Elementary bounds on the logarithm of a finite sum of exponentials

This module contains uniform Lipschitz and absolute bounds on `log ∑ exp`:
* `abs_log_sum_exp_sub_le_of_forall`: `log ∑ exp (u + h)` is 1-Lipschitz for the supremum norm.
* `abs_log_sum_exp_sub_log_card_le`: `|log ∑ exp u - log (card α)| ≤ sup |u|`.
* `abs_log_sum_exp_le_of_forall`: bound on `|log ∑ exp u|` by `log (card α) + sup |u|`.
-/

@[expose] public section

open Finset Real

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **`log ∑ₐ exp (· + h)` is 1-Lipschitz for the sup norm:** if `|uₐ - vₐ| ≤ M` for all `a`, then
`|log ∑ₐ exp (uₐ + hₐ) - log ∑ₐ exp (vₐ + hₐ)| ≤ M`. -/
theorem abs_log_sum_exp_sub_le_of_forall (h u v : α → ℝ) {M : ℝ} (hM : ∀ a, |u a - v a| ≤ M) :
    |Real.log (∑ a, Real.exp (u a + h a)) - Real.log (∑ a, Real.exp (v a + h a))| ≤ M := by
  have key : ∀ u v : α → ℝ, (∀ a, u a - v a ≤ M) → Real.log (∑ a, Real.exp (u a + h a)) -
      Real.log (∑ a, Real.exp (v a + h a)) ≤ M := by
    intro u v huv
    have hu : 0 < ∑ a, Real.exp (u a + h a) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    have hv : 0 < ∑ a, Real.exp (v a + h a) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    rw [sub_le_iff_le_add', ← Real.log_exp M, ← Real.log_mul hv.ne' (Real.exp_pos _).ne']
    refine Real.log_le_log hu ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [huv a])
  rw [abs_le]
  constructor
  · have := key v u fun a => by linarith [neg_le_of_abs_le (hM a)]
    linarith
  · exact key u v fun a => le_of_abs_le (hM a)

/-- **`log ∑ₐ exp (uₐ)` is within `M` of `log (card α)`** when `|uₐ| ≤ M` for all `a`. -/
theorem abs_log_sum_exp_sub_log_card_le (u : α → ℝ) {M : ℝ} (hM : ∀ a, |u a| ≤ M) :
    |Real.log (∑ a, Real.exp (u a)) - Real.log (Fintype.card α)| ≤ M := by
  have h := abs_log_sum_exp_sub_le_of_forall (fun _ => 0) u (fun _ => 0) (by simpa using hM)
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

/-- Bound on `|log ∑ₐ exp (uₐ)|` by `log (card α) + M` when `|uₐ| ≤ M` for all `a`. -/
theorem abs_log_sum_exp_le_of_forall (u : α → ℝ) {M : ℝ} (hM : ∀ a, |u a| ≤ M) :
    |Real.log (∑ a, Real.exp (u a))| ≤ Real.log (Fintype.card α) + M := by
  have h_tri := abs_le.mp (abs_log_sum_exp_sub_log_card_le u hM)
  have h1 : 1 ≤ (Fintype.card α : ℝ) := by
    have : 1 ≤ Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hlog_nonneg : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg h1
  rw [abs_le]
  constructor
  · linarith [h_tri.1, hlog_nonneg]
  · linarith [h_tri.2]

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [Nonempty α] in
/-- The log-partition function of a finite measurable random energy is measurable. -/
theorem measurable_log_sum_exp {H : Ω → α → ℝ}
    (hmeas : ∀ a, Measurable fun ω => H ω a) (β : ℝ) :
    Measurable fun ω => Real.log (∑ a, Real.exp (β * H ω a)) :=
  (Finset.measurable_sum _ fun a _ => ((hmeas a).const_mul β).exp).log

/-- An integrable envelope for a finite random energy gives an integrable log-partition
function. The envelope may depend on the environment, for example through a Gaussian field. -/
theorem integrable_log_sum_exp_of_abs_le [IsFiniteMeasure μ] {E : Ω → α → ℝ}
    (hE : ∀ a, Measurable fun ω => E ω a) {B : Ω → ℝ} (hB : Integrable B μ)
    (hb : ∀ᵐ ω ∂μ, ∀ a, |E ω a| ≤ B ω) :
    Integrable (fun ω => Real.log (∑ a, Real.exp (E ω a))) μ := by
  refine ((integrable_const (Real.log (Fintype.card α))).add hB).mono'
    (by simpa only [one_mul] using (measurable_log_sum_exp hE 1).aestronglyMeasurable) ?_
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_log_sum_exp_le_of_forall (E ω) hω

/-- The expected log-partition function is within the expected energy envelope of `log card`.
This keeps an environment-dependent envelope rather than requiring a uniform constant. -/
theorem abs_integral_log_sum_exp_sub_log_card_le [IsProbabilityMeasure μ] {E : Ω → α → ℝ}
    (hE : ∀ a, Measurable fun ω => E ω a) {B : Ω → ℝ} (hB : Integrable B μ)
    (hb : ∀ᵐ ω ∂μ, ∀ a, |E ω a| ≤ B ω) :
    |(∫ ω, Real.log (∑ a, Real.exp (E ω a)) ∂μ) - Real.log (Fintype.card α)| ≤ ∫ ω, B ω ∂μ := by
  have hi := integrable_log_sum_exp_of_abs_le hE hB hb
  have hc : (∫ ω, Real.log (∑ a, Real.exp (E ω a)) ∂μ) - Real.log (Fintype.card α) =
      ∫ ω, Real.log (∑ a, Real.exp (E ω a)) - Real.log (Fintype.card α) ∂μ := by
    exact (integral_sub_const_of_isProbabilityMeasure μ _ _ hi).symm
  rw [hc, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hB ?_
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using abs_log_sum_exp_sub_log_card_le (E ω) hω

/-- A uniform energy bound bounds the expected log-partition function's difference from
`log card` by the same constant. -/
theorem abs_integral_log_sum_exp_sub_log_card_le_const [IsProbabilityMeasure μ]
    {E : Ω → α → ℝ} (hE : ∀ a, Measurable fun ω => E ω a) {B : ℝ}
    (hb : ∀ ω a, |E ω a| ≤ B) :
    |(∫ ω, Real.log (∑ a, Real.exp (E ω a)) ∂μ) - Real.log (Fintype.card α)| ≤ B := by
  simpa using abs_integral_log_sum_exp_sub_log_card_le (μ := μ) hE (B := fun _ => B)
    (integrable_const B) (ae_of_all _ hb)

end MeasureTheory
