/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Resampling one coordinate of a product measure

Replacing the `j`-th coordinate of a `Measure.pi μ`-distributed vector by an independent
`μ j`-distributed value does not change the law (`measurePreserving_update_pi`).  Consequently an
integral against `Measure.pi μ` is an iterated integral that first integrates the `j`-th
coordinate (`integral_pi_eq_integral_update`), which is the Fubini step behind coordinatewise
integration by parts for Gaussian vectors (`ForMathlib/Probability/Moments/GaussianStein.lean`).
-/

@[expose] public section

open MeasureTheory Function

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] (j : ι)

/-- Replacing the `j`-th coordinate of a `Measure.pi μ`-distributed vector by an independent
`μ j`-distributed value preserves the product measure. -/
theorem measurePreserving_update_pi :
    MeasurePreserving (fun p : (∀ i, X i) × X j => update p.1 j p.2)
      ((Measure.pi μ).prod (μ j)) (Measure.pi μ) := by
  have hm : Measurable (fun p : (∀ i, X i) × X j => update p.1 j p.2) := measurable_update'
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (∀ i, X i) × X j => update p.1 j p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (update s j Set.univ)) ×ˢ s j := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h j⟩
      by_cases hij : i = j
      · subst hij; simp
      · simpa [hij] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hij : i = j
      · subst hij; simpa using h2
      · simpa [hij] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => μ i (s i)) (Finset.mem_univ j)]
  rw [Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]]
  simp [mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The integrand `f (update x j t)` is integrable against `(Measure.pi μ).prod (μ j)`. -/
theorem integrable_update_pi {f : (∀ i, X i) → E} (hf : Integrable f (Measure.pi μ)) :
    Integrable (fun p : (∀ i, X i) × X j => f (update p.1 j p.2))
      ((Measure.pi μ).prod (μ j)) :=
  (measurePreserving_update_pi μ j).integrable_comp_of_integrable hf

/-- An integral against `Measure.pi μ` can be computed by first integrating out the `j`-th
coordinate: `∫ f ∂π = ∫ x, ∫ t, f (update x j t) ∂μ j ∂π`. -/
theorem integral_pi_eq_integral_update {f : (∀ i, X i) → E}
    (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂Measure.pi μ = ∫ x, ∫ t, f (update x j t) ∂μ j ∂Measure.pi μ := by
  rw [← integral_prod _ (integrable_update_pi μ j hf)]
  have hmp := measurePreserving_update_pi μ j
  have h := integral_map (f := f) hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h

end MeasureTheory
