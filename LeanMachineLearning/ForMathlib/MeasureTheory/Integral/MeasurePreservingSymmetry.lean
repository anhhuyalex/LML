/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals along measure preserving maps, and exchangeable families

* `MeasurePreserving.integral_comp_of_aestronglyMeasurable`: `∫ g (f x) dμ = ∫ g dν` for a
  measure preserving `f`, without a measurable embedding.
* `integral_comp_eq_of_perm_equivariant`: if every permutation of the index set is implemented by
  a measure preserving map of the base space, `F_i ∘ φ = F_{π i}`, then `𝔼 G(F_i)` does not
  depend on `i` (the "symmetry between sites" step of Talagrand's Corollary 1.7.8).
-/

@[expose] public section

namespace MeasureTheory

/-- Integral of a function composed with a measure-preserving map. Unlike
`MeasurePreserving.integral_comp` this needs no measurable embedding, which coordinate projections
are not. -/
theorem MeasurePreserving.integral_comp_of_aestronglyMeasurable {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → E} (hg : AEStronglyMeasurable g ν) : ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν :=
  calc ∫ x, g (f x) ∂μ = ∫ y, g y ∂(Measure.map f μ) :=
        (integral_map hf.measurable.aemeasurable (by rwa [hf.map_eq])).symm
    _ = ∫ y, g y ∂ν := by rw [hf.map_eq]

/-- **Exchangeability.**  If for every permutation `π` of the index type there is a measure
preserving `φ` with `F i (φ ω) = F (π i) ω`, then `∫ G (F i)` is the same for all `i`. -/
theorem integral_comp_eq_of_perm_equivariant {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ι → Ω → ℝ) (hF : ∀ i, Measurable (F i)) {G : ℝ → ℝ}
    (hG : Measurable G)
    (hsymm : ∀ π : Equiv.Perm ι, ∃ φ : Ω → Ω, MeasurePreserving φ P P ∧
      ∀ i ω, F i (φ ω) = F (π i) ω) (i j : ι) :
    ∫ ω, G (F i ω) ∂P = ∫ ω, G (F j ω) ∂P := by
  classical
  obtain ⟨φ, hφ, hφF⟩ := hsymm (Equiv.swap j i)
  have h := hφ.integral_comp_of_aestronglyMeasurable
    (g := fun ω => G (F j ω)) (hG.comp (hF j)).aestronglyMeasurable
  simp only [hφF, Equiv.swap_apply_left] at h
  exact h

end MeasureTheory
