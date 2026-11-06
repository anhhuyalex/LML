/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Moments.Tilted

/-!
# Bounded energies on arbitrary finite measure spaces

These estimates and derivatives use Mathlib's exponential tilt directly. The spin space
need not be finite, and bounds and measurability are only required almost everywhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {C : ℝ}

/-- An almost everywhere upper bound on a real energy gives exponential integrability
against any finite measure. A lower bound is unnecessary. -/
theorem integrable_exp_of_ae_le [IsFiniteMeasure μ] (hf : AEMeasurable f μ)
    (hbound : ∀ᵐ a ∂μ, f a ≤ C) : Integrable (fun a => Real.exp (f a)) μ := by
  refine (integrable_const (Real.exp C)).mono' hf.exp.aestronglyMeasurable ?_
  filter_upwards [hbound] with a ha
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ha

/-- The logarithmic partition function of a bounded energy on a probability space is
bounded by the same constant. This applies to continuous and singular base laws alike. -/
theorem abs_log_integral_exp_le_of_ae_abs_le [IsProbabilityMeasure μ]
    (hf : AEMeasurable f μ) (hbound : ∀ᵐ a ∂μ, |f a| ≤ C) :
    |Real.log (∫ a, Real.exp (f a) ∂μ)| ≤ C := by
  have hi := integrable_exp_of_ae_le hf (hbound.mono fun a ha =>
    (le_abs_self (f a)).trans ha)
  have hZ := integral_exp_pos hi
  have hupper : (∫ a, Real.exp (f a) ∂μ) ≤ Real.exp C := by
    calc
      _ ≤ ∫ _a : α, Real.exp C ∂μ := integral_mono_ae hi (integrable_const _)
        (hbound.mono fun a ha => Real.exp_le_exp.mpr ((le_abs_self _).trans ha))
      _ = _ := by simp
  have hlower : Real.exp (-C) ≤ ∫ a, Real.exp (f a) ∂μ := by
    calc
      _ = ∫ _a : α, Real.exp (-C) ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hi (hbound.mono fun a ha =>
        Real.exp_le_exp.mpr ((neg_le_neg ha).trans (neg_abs_le _)))
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hZ).mpr hlower,
    (Real.log_le_iff_le_exp hZ).mpr hupper⟩

end MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℝ} {C : ℝ}

/-- A bounded real variable has exponential moments at every real parameter on a finite
measure space; there is no restriction on the sign of the parameter. -/
theorem integrableExpSet_eq_univ_of_ae_abs_le [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ a ∂μ, |X a| ≤ C) :
    integrableExpSet X μ = univ := by
  apply Set.eq_univ_of_forall
  intro t
  apply integrable_exp_of_ae_le (hX.const_mul t) (C := |t| * C)
  filter_upwards [hbound] with a ha
  apply (le_abs_self _).trans
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ha (abs_nonneg t)

/-- The log-partition derivative for a bounded energy under an arbitrary finite base
measure is its tilted mean. This reuses Mathlib's analytic cumulant-generating function
and tilted-mean identity rather than a finite-configuration differentiation argument. -/
theorem hasDerivAt_log_integral_exp_mul_of_ae_abs_le [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ a ∂μ, |X a| ≤ C) (t : ℝ) :
    HasDerivAt (fun s => Real.log (∫ a, Real.exp (s * X a) ∂μ))
      (∫ a, X a ∂(μ.tilted (fun a => t * X a))) t := by
  have ht : t ∈ interior (integrableExpSet X μ) := by
    simp [integrableExpSet_eq_univ_of_ae_abs_le hX hbound]
  have hcgf : cgf X μ = (fun s => Real.log (∫ a, Real.exp (s * X a) ∂μ)) := rfl
  rw [← hcgf, integral_tilted_mul_self ht]
  exact (analyticAt_cgf ht).differentiableAt.hasDerivAt

end ProbabilityTheory
