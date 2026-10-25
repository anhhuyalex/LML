/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# A function whose fibre laws are constant is independent of the parameter

If `F : α × β → γ` has, for almost every parameter `a`, the same law `lam` under `B` of
`b ↦ F (a, b)`, then under the product measure `A ⊗ B` the pair `(a, F (a, b))` has the law
`A ⊗ lam`; hence `F` has law `lam` and is independent of the parameter `a`.  This is the
"conditionally standard Gaussian, hence independent" step (Talagrand, Lemma 1.7.6).  The version
`indepFun_fst_comp_of_measurePreserving` transports it along a measure preserving map into the
product, e.g. the split of the disorder of an `(N+1)`-spin system into old and new couplings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **Constant fibre law ⟹ product law.**  If, for `A`-a.e. `a`, the law of `b ↦ F (a, b)` under
`B` is `lam`, then `(a, F (a, b))` has the law `A ⊗ lam` under `A ⊗ B`. -/
theorem map_prod_fst_eq_prod (A : Measure α) (B : Measure β) [SFinite A] [SFinite B]
    {lam : Measure γ} [SFinite lam] {F : α × β → γ} (hF : Measurable F)
    (h : ∀ᵐ a ∂A, B.map (fun b => F (a, b)) = lam) :
    (A.prod B).map (fun w => (w.1, F w)) = A.prod lam := by
  ext s hs
  have hG : Measurable fun w : α × β => (w.1, F w) := measurable_fst.prodMk hF
  rw [Measure.map_apply hG hs, Measure.prod_apply (hG hs), Measure.prod_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with a ha
  have hs' : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  have hFa : Measurable fun b => F (a, b) := hF.comp measurable_prodMk_left
  rw [← ha, Measure.map_apply hFa hs']
  rfl

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {α β γ Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace Ω]

/-- A function of `(a, b)` whose law in `b` is the same probability measure `lam` for a.e. `a` is
independent of `a` under `A ⊗ B`, and has law `lam`. -/
theorem indepFun_fst_of_ae_map_eq (A : Measure α) (B : Measure β) [IsProbabilityMeasure A]
    [IsProbabilityMeasure B] {lam : Measure γ} [IsProbabilityMeasure lam] {F : α × β → γ}
    (hF : Measurable F) (h : ∀ᵐ a ∂A, B.map (fun b => F (a, b)) = lam) :
    IndepFun (fun w : α × β => w.1) F (A.prod B) ∧ (A.prod B).map F = lam := by
  have hpair := Measure.map_prod_fst_eq_prod A B hF h
  have hmap : (A.prod B).map F = lam := by
    have : (A.prod B).map F = ((A.prod B).map (fun w => (w.1, F w))).map Prod.snd := by
      rw [Measure.map_map measurable_snd (measurable_fst.prodMk hF)]; rfl
    rw [this, hpair, Measure.map_snd_prod]; simp
  refine ⟨?_, hmap⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable hF.aemeasurable, hpair,
    hmap, Measure.map_fst_prod]
  simp

/-- **Transport along a measure preserving map.**  If `e : Ω → α × β` carries `P` to `A ⊗ B` and
`b ↦ F (a, b)` has the law `lam` for a.e. `a`, then `F ∘ e` has law `lam` under `P` and is
independent of the first component of `e`. -/
theorem indepFun_fst_comp_of_measurePreserving {P : Measure Ω} [IsProbabilityMeasure P] {A : Measure α} {B : Measure β}
    [IsProbabilityMeasure A] [IsProbabilityMeasure B] {lam : Measure γ}
    [IsProbabilityMeasure lam] {e : Ω → α × β} (he : MeasurePreserving e P (A.prod B))
    {F : α × β → γ} (hF : Measurable F) (h : ∀ᵐ a ∂A, B.map (fun b => F (a, b)) = lam) :
    IndepFun (fun ω => (e ω).1) (fun ω => F (e ω)) P ∧ P.map (fun ω => F (e ω)) = lam := by
  obtain ⟨hind, hlaw⟩ := indepFun_fst_of_ae_map_eq A B hF h
  have h1 : AEMeasurable (fun ω => (e ω).1) P := (measurable_fst.comp he.measurable).aemeasurable
  have h2 : AEMeasurable (fun ω => F (e ω)) P := (hF.comp he.measurable).aemeasurable
  have hmap : P.map (fun ω => F (e ω)) = lam := by
    rw [← hlaw, ← he.map_eq, Measure.map_map hF he.measurable]; rfl
  refine ⟨?_, hmap⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map h1 h2, hmap]
  have hG : Measurable fun w : α × β => (w.1, F w) := measurable_fst.prodMk hF
  have e1 : P.map (fun ω => ((e ω).1, F (e ω))) = (A.prod B).map (fun w => (w.1, F w)) := by
    rw [← he.map_eq, Measure.map_map hG he.measurable]; rfl
  have e2 : P.map (fun ω => (e ω).1) = A := by
    have : (A.prod B).map Prod.fst = A := by rw [Measure.map_fst_prod]; simp
    rw [← this, ← he.map_eq, Measure.map_map measurable_fst he.measurable]; rfl
  rw [e1, e2, Measure.map_prod_fst_eq_prod A B hF h]

end ProbabilityTheory
