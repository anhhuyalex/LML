/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi

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

/-- If a measure preserving map carries the observable `F i` to `F j` almost everywhere, then
`∫ G (F i) = ∫ G (F j)`, for observables in any measurable space and `G` vector-valued. -/
theorem integral_comp_eq_of_measurePreserving_ae_eq {Ω α E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : Measure Ω} {X Y : Ω → α} {G : α → E}
    {φ : Ω → Ω} (hφ : MeasurePreserving φ P P) (h : ∀ᵐ ω ∂P, X (φ ω) = Y ω)
    (hG : AEStronglyMeasurable (fun ω => G (X ω)) P) :
    ∫ ω, G (X ω) ∂P = ∫ ω, G (Y ω) ∂P :=
  (hφ.integral_comp_of_aestronglyMeasurable (g := fun ω => G (X ω)) hG).symm.trans
    (integral_congr_ae (h.mono fun _ h => congrArg G h))

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
  refine (integral_comp_eq_of_measurePreserving_ae_eq (X := F j) (Y := F i) (G := G) hφ
    (ae_of_all _ fun ω => ?_) (hG.comp (hF j)).aestronglyMeasurable).symm
  rw [hφF, Equiv.swap_apply_left]

/-- The integral of an almost everywhere strongly measurable function of two distinct
replicas agrees with its integral under the product law. -/
theorem integral_pi_pair_eq_prod_of_aestronglyMeasurable {α J : Type*}
    [MeasurableSpace α] [Fintype J] (ν : Measure α) [IsProbabilityMeasure ν] {x y : J} (hxy : x ≠ y)
    (φ : α → α → ℝ) (hφ : AEStronglyMeasurable (fun p : α × α => φ p.1 p.2) (ν.prod ν)) :
    ∫ σ : J → α, φ (σ x) (σ y) ∂(Measure.pi fun _ : J => ν) =
      ∫ p : α × α, φ p.1 p.2 ∂(ν.prod ν) := by
  have hρ : Function.Injective (![x, y] : Fin 2 → J) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Ne.symm hxy]
  have hmp := (measurePreserving_piFinTwo fun _ : Fin 2 => ν).comp
    (measurePreserving_pi_comp_injective ν hρ)
  have h := hmp.integral_comp_of_aestronglyMeasurable hφ
  simpa [Function.comp_def] using h

end MeasureTheory
