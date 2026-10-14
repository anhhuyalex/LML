/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.IdentDistrib

/-!
# Equivariant mixtures: invariance in law of `F (R, ξ)`

Let `R` be a random parameter and `ξ ~ γ` an independent noise.  Suppose a measurable map `φ` of
the parameter space leaves the law of `R` invariant, and that for almost every parameter `a`, the
law of `ρ (F (a, ξ))` equals the law of `F (φ a, ξ)`.  Then `ρ (F (R, ξ))` and `F (R, ξ)` have the
same law (`ProbabilityTheory.identDistrib_prod_comp_of_ae_map_eq`).  This is the mechanism by which
an exchangeable random covariance gives an exchangeable Gaussian array: `F` colors the noise with
the covariance, `φ` and `ρ` are the permutation actions on the covariance and on the array.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω Y Ξ Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Ξ]
  [MeasurableSpace Z]

/-- **Invariance in law of an equivariant mixture.** -/
theorem identDistrib_prod_comp_of_ae_map_eq {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : Measure Ξ} [IsProbabilityMeasure γ] {R : Ω → Y} (hR : Measurable R) {F : Y × Ξ → Z}
    (hF : Measurable F) {ρ : Z → Z} (hρ : Measurable ρ) {φ : Y → Y} (hφ : Measurable φ)
    (h1 : ∀ᵐ ω ∂P, γ.map (fun ξ => ρ (F (R ω, ξ))) = γ.map (fun ξ => F (φ (R ω), ξ)))
    (h2 : IdentDistrib (φ ∘ R) R P P) :
    IdentDistrib (fun z : Ω × Ξ => ρ (F (R z.1, z.2))) (fun z => F (R z.1, z.2))
      (P.prod γ) (P.prod γ) := by
  have hFR : Measurable fun z : Ω × Ξ => F (R z.1, z.2) :=
    hF.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hg : ∀ {S : Set Z}, MeasurableSet S → Measurable fun a : Y => γ {ξ | F (a, ξ) ∈ S} :=
    fun hS => measurable_measure_prodMk_left (hF hS)
  have hρF : Measurable fun z : Ω × Ξ => ρ (F (R z.1, z.2)) := hρ.comp hFR
  refine ⟨hρF.aemeasurable, hFR.aemeasurable, ?_⟩
  ext S hS
  have hS' : MeasurableSet (ρ ⁻¹' S) := hρ hS
  rw [Measure.map_apply hρF hS, Measure.map_apply hFR hS]
  have e1 : (P.prod γ) ((fun z : Ω × Ξ => ρ (F (R z.1, z.2))) ⁻¹' S) =
      ∫⁻ ω, γ {ξ | ρ (F (R ω, ξ)) ∈ S} ∂P := by
    rw [Measure.prod_apply (hρF hS)]; rfl
  have e2 : (P.prod γ) ((fun z : Ω × Ξ => F (R z.1, z.2)) ⁻¹' S) =
      ∫⁻ ω, γ {ξ | F (R ω, ξ) ∈ S} ∂P := by
    rw [Measure.prod_apply (hFR hS)]; rfl
  rw [e1, e2]
  have e3 : ∫⁻ ω, γ {ξ | ρ (F (R ω, ξ)) ∈ S} ∂P = ∫⁻ ω, γ {ξ | F (φ (R ω), ξ) ∈ S} ∂P := by
    refine lintegral_congr_ae (h1.mono fun ω hω => ?_)
    have hm1 : Measurable fun ξ => ρ (F (R ω, ξ)) :=
      hρ.comp (hF.comp (measurable_const.prodMk measurable_id))
    have hm2 : Measurable fun ξ => F (φ (R ω), ξ) :=
      hF.comp (measurable_const.prodMk measurable_id)
    calc γ {ξ | ρ (F (R ω, ξ)) ∈ S} = γ.map (fun ξ => ρ (F (R ω, ξ))) S :=
          (Measure.map_apply hm1 hS).symm
      _ = γ.map (fun ξ => F (φ (R ω), ξ)) S := by rw [hω]
      _ = γ {ξ | F (φ (R ω), ξ) ∈ S} := Measure.map_apply hm2 hS
  rw [e3]
  have e4 : ∫⁻ ω, γ {ξ | F (φ (R ω), ξ) ∈ S} ∂P = ∫⁻ ω, γ {ξ | F (R ω, ξ) ∈ S} ∂P := by
    have h := h2.map_eq
    have h3 := lintegral_map (hg hS) (hφ.comp hR) (μ := P)
    have h4 := lintegral_map (hg hS) hR (μ := P)
    rw [h] at h3
    exact h3.symm.trans h4
  exact e4

end ProbabilityTheory
