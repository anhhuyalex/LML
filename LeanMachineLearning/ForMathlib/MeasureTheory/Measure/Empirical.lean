/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Empirical measures of finite families

For a finite family of points `x : ι → α`, the empirical measure
`empiricalMeasure x = (card ι)⁻¹ • ∑ i, dirac (x i)` is the uniform average of the Dirac masses at
the points.  It is a probability measure as soon as `ι` is nonempty, and integrating against it is
averaging over the family (`integral_empiricalMeasure`).

This is the finite-index case of the empirical measures studied in optimal transport (see
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Empirical`); it carries no dependency on that
repository and no neural-network content, so that mean-field limits of neuron ensembles can reuse
it verbatim.

## Main declarations

* `MeasureTheory.empiricalMeasure`: the measure `(card ι)⁻¹ • ∑ i, dirac (x i)`.
* `MeasureTheory.empiricalMeasure_comp_equiv`: the empirical measure is invariant under reindexing.
* `MeasureTheory.integral_empiricalMeasure`, `MeasureTheory.lintegral_empiricalMeasure`:
  `∫ g ∂(empiricalMeasure x) = (card ι)⁻¹ • ∑ i, g (x i)`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {ι α E : Type*} [Fintype ι] [MeasurableSpace α]

/-- The empirical measure `(card ι)⁻¹ • ∑ i, dirac (x i)` of a finite family of points. -/
noncomputable def empiricalMeasure (x : ι → α) : Measure α :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

@[simp]
lemma empiricalMeasure_univ [Nonempty ι] (x : ι → α) : empiricalMeasure x Set.univ = 1 := by
  have h0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp
  simp [empiricalMeasure, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _)]

instance instIsProbabilityMeasureEmpiricalMeasure [Nonempty ι] (x : ι → α) :
    IsProbabilityMeasure (empiricalMeasure x) :=
  ⟨empiricalMeasure_univ x⟩

/-- Reindexing the family by an equivalence does not change its empirical measure. -/
lemma empiricalMeasure_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (x : ι → α) :
    empiricalMeasure (x ∘ e) = empiricalMeasure x := by
  simp only [empiricalMeasure, Fintype.card_congr e, Function.comp_apply]
  rw [Equiv.sum_comp e (fun i => Measure.dirac (x i))]

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

/-- Integrating against an empirical measure is averaging over the family. No measurability or
integrability hypothesis is needed, since every function is integrable against a finite sum of
Dirac masses on a space with measurable singletons. -/
theorem integral_empiricalMeasure [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : ι → α) (g : α → E) :
    ∫ y, g y ∂(empiricalMeasure x) = (Fintype.card ι : ℝ)⁻¹ • ∑ i, g (x i) := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure fun i _ ↦ integrable_dirac (by simp)]
  simp [ENNReal.toReal_inv]

/-- The `ℝ≥0∞`-valued version of `integral_empiricalMeasure`. -/
theorem lintegral_empiricalMeasure (x : ι → α) (g : α → ℝ≥0∞) :
    ∫⁻ y, g y ∂(empiricalMeasure x) = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, g (x i) := by
  simp [empiricalMeasure, lintegral_finsetSum_measure, lintegral_dirac]

end MeasurableSingletonClass

end MeasureTheory
