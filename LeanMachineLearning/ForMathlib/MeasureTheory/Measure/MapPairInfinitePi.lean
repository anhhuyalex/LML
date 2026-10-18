/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi

/-!
# Replacing an independent i.i.d. family by another with the same conditional laws

If `A` is a random parameter and `D = (Dᵢ)` is an i.i.d. family independent of `A`, the law of
`(A, (Φ(aᵢ(A), Dᵢ))ᵢ)` depends on `Φ` and on the law of `Dᵢ` only through the laws of the
random variables `Φ(θ, D₀)` for each fixed parameter `θ`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {ι 𝒜 Θ 𝒟 𝒟' E : Type*} [MeasurableSpace 𝒜] [MeasurableSpace Θ] [MeasurableSpace 𝒟]
  [MeasurableSpace 𝒟'] [MeasurableSpace E]

/-- The pair `(a, (Φ(aᵢ, dᵢ))ᵢ)` under `μ ⊗ ν^{⊗ι}` has a law that depends on `Φ` and `ν` only
through the laws `ν.map (Φ θ)`. -/
theorem map_prod_infinitePi_replace (μ : Measure 𝒜) [SFinite μ] (a : 𝒜 → ι → Θ)
    (ha : Measurable a) (ν : Measure 𝒟) [IsProbabilityMeasure ν]
    (ν' : Measure 𝒟') [IsProbabilityMeasure ν'] (Φ : Θ → 𝒟 → E) (Ψ : Θ → 𝒟' → E)
    (hΦ : Measurable (Function.uncurry Φ)) (hΨ : Measurable (Function.uncurry Ψ))
    (h : ∀ θ, ν.map (Φ θ) = ν'.map (Ψ θ)) :
    (μ.prod (infinitePi fun _ : ι => ν)).map
        (fun p => (p.1, fun i => Φ (a p.1 i) (p.2 i))) =
      (μ.prod (infinitePi fun _ : ι => ν')).map
        (fun p => (p.1, fun i => Ψ (a p.1 i) (p.2 i))) := by
  have hm1 : Measurable (fun p : 𝒜 × (ι → 𝒟) => (p.1, fun i => Φ (a p.1 i) (p.2 i))) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
      hΦ.comp (((measurable_pi_apply i).comp (ha.comp measurable_fst)).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  have hm2 : Measurable (fun p : 𝒜 × (ι → 𝒟') => (p.1, fun i => Ψ (a p.1 i) (p.2 i))) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
      hΨ.comp (((measurable_pi_apply i).comp (ha.comp measurable_fst)).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  ext s hs
  rw [map_apply hm1 hs, map_apply hm2 hs, prod_apply (hm1 hs), prod_apply (hm2 hs)]
  refine lintegral_congr fun x => ?_
  have hs' : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
  have hG : Measurable (fun d : ι → 𝒟 => fun i => Φ (a x i) (d i)) :=
    measurable_pi_iff.2 fun i => (hΦ.comp (measurable_prodMk_left (x := a x i))).comp
      (measurable_pi_apply i)
  have hG' : Measurable (fun d : ι → 𝒟' => fun i => Ψ (a x i) (d i)) :=
    measurable_pi_iff.2 fun i => (hΨ.comp (measurable_prodMk_left (x := a x i))).comp
      (measurable_pi_apply i)
  have e1 : infinitePi (fun _ : ι => ν) ((fun d => (x, fun i => Φ (a x i) (d i))) ⁻¹' s) =
      infinitePi (fun i => ν.map (Φ (a x i))) (Prod.mk x ⁻¹' s) := by
    rw [← infinitePi_map_pi (fun _ : ι => ν) (f := fun i => Φ (a x i))
      (fun i => hΦ.comp measurable_prodMk_left), map_apply hG hs']
    rfl
  have e2 : infinitePi (fun _ : ι => ν') ((fun d => (x, fun i => Ψ (a x i) (d i))) ⁻¹' s) =
      infinitePi (fun i => ν'.map (Ψ (a x i))) (Prod.mk x ⁻¹' s) := by
    rw [← infinitePi_map_pi (fun _ : ι => ν') (f := fun i => Ψ (a x i))
      (fun i => hΨ.comp measurable_prodMk_left), map_apply hG' hs']
    rfl
  refine e1.trans (Eq.trans ?_ e2.symm)
  simp only [h]

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

/-- Two functions of a parameter and an independent coordinate have the same joint-law image if
their fibre laws agree for almost every parameter. -/
theorem map_prod_eq_of_ae_map_fiber_eq (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (ρ : Measure γ) [SFinite ρ] {F : α × β → δ} {G : α × γ → δ}
    (hF : Measurable F) (hG : Measurable G)
    (h : ∀ᵐ a ∂μ, ν.map (fun b => F (a, b)) = ρ.map (fun c => G (a, c))) :
    (μ.prod ν).map F = (μ.prod ρ).map G := by
  ext s hs
  rw [map_apply hF hs, map_apply hG hs, prod_apply (hF hs), prod_apply (hG hs)]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with a ha
  have h1 : Measurable fun b => F (a, b) := hF.comp measurable_prodMk_left
  have h2 : Measurable fun c => G (a, c) := hG.comp measurable_prodMk_left
  have := congrArg (fun m => m s) ha
  simp only [map_apply h1 hs, map_apply h2 hs] at this
  exact this

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {Ω ι 𝒜 Θ ℰ F : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒜] [MeasurableSpace Θ]
  [MeasurableSpace ℰ] [MeasurableSpace F]

/-- **Conditional replacement.** Let `A` be a random parameter and `(Eⱼ)` an i.i.d. family
independent of `A`. A measurable functional of `(A, (Φ(θⱼ(A), Eⱼ))ⱼ)` has the same law when `Φ` is
replaced by `Ψ`, provided `Φ(θ, E₀)` and `Ψ(θ, E₀)` have the same law for every fixed `θ`. -/
theorem identDistrib_map_replace {P : Measure Ω} [IsProbabilityMeasure P] (A : Ω → 𝒜)
    (hA : Measurable A) (E : ι → Ω → ℰ) (hEm : ∀ j, Measurable (E j)) (hE : iIndepFun E P)
    (ν : Measure ℰ) [IsProbabilityMeasure ν] (hEl : ∀ j, HasLaw (E j) ν P)
    (hAE : IndepFun A (fun ω j => E j ω) P) (θ : 𝒜 → ι → Θ) (hθ : Measurable θ)
    (Φ Ψ : Θ → ℰ → F) (hΦ : Measurable (Function.uncurry Φ))
    (hΨ : Measurable (Function.uncurry Ψ)) (h : ∀ t, ν.map (Φ t) = ν.map (Ψ t))
    (G : 𝒜 × (ι → F) → ENNReal) (hG : Measurable G) :
    IdentDistrib (fun ω => G (A ω, fun j => Φ (θ (A ω) j) (E j ω)))
      (fun ω => G (A ω, fun j => Ψ (θ (A ω) j) (E j ω))) P P := by
  have hEvec : Measurable fun ω j => E j ω := measurable_pi_iff.2 hEm
  have hpair : P.map (fun ω => (A ω, fun j => E j ω)) =
      (P.map A).prod (Measure.infinitePi fun _ : ι => ν) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hEvec.aemeasurable).1 hAE,
      (HasLaw.infinitePi hEm hE hEl).map_eq]
  have hrep := Measure.map_prod_infinitePi_replace (P.map A) θ hθ ν ν Φ Ψ hΦ hΨ h
  have hpm : Measurable fun ω => (A ω, fun j => E j ω) := hA.prodMk hEvec
  have hm1 : Measurable fun p : 𝒜 × (ι → ℰ) => (p.1, fun j => Φ (θ p.1 j) (p.2 j)) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun j => hΦ.comp
      (((measurable_pi_apply j).comp (hθ.comp measurable_fst)).prodMk
        ((measurable_pi_apply j).comp measurable_snd)))
  have hm2 : Measurable fun p : 𝒜 × (ι → ℰ) => (p.1, fun j => Ψ (θ p.1 j) (p.2 j)) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun j => hΨ.comp
      (((measurable_pi_apply j).comp (hθ.comp measurable_fst)).prodMk
        ((measurable_pi_apply j).comp measurable_snd)))
  refine ⟨(hG.comp (hm1.comp hpm)).aemeasurable, (hG.comp (hm2.comp hpm)).aemeasurable, ?_⟩
  have e1 : (fun ω => G (A ω, fun j => Φ (θ (A ω) j) (E j ω))) =
      (G ∘ fun p : 𝒜 × (ι → ℰ) => (p.1, fun j => Φ (θ p.1 j) (p.2 j))) ∘
        fun ω => (A ω, fun j => E j ω) := rfl
  have e2 : (fun ω => G (A ω, fun j => Ψ (θ (A ω) j) (E j ω))) =
      (G ∘ fun p : 𝒜 × (ι → ℰ) => (p.1, fun j => Ψ (θ p.1 j) (p.2 j))) ∘
        fun ω => (A ω, fun j => E j ω) := rfl
  rw [e1, e2, ← Measure.map_map (hG.comp hm1) hpm, ← Measure.map_map (hG.comp hm2) hpm, hpair,
    ← Measure.map_map hG hm1, ← Measure.map_map hG hm2, hrep]

end ProbabilityTheory
