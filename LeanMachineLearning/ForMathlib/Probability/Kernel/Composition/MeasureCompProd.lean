/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Lemmas about measure composition-product
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Kernel α β}

section AbsolutelyContinuous

lemma AbsolutelyContinuous.compProd_left_apply {γ : Type*} {mγ : MeasurableSpace γ}
    [IsSFiniteKernel η] {a : α} (hac : κ a ≪ η a) (ξ : Kernel (α × β) γ) :
    (κ ⊗ₖ ξ) a ≪ (η ⊗ₖ ξ) a := by
  by_cases hκ : IsSFiniteKernel κ
  · by_cases hξ : IsSFiniteKernel ξ
    · simp_rw [Kernel.compProd_apply_eq_compProd_sectR, hac.compProd_left _]
    · simp [Kernel.compProd_of_not_isSFiniteKernel_right _ _ hξ]
  · simp [Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ]

end AbsolutelyContinuous

section MapComap

/-- Transporting `μ ⊗ₘ η.comap f` along `f` in the first coordinate gives `μ.map f ⊗ₘ η`. -/
lemma map_compProd_comap {γ : Type*} {mγ : MeasurableSpace γ} (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f) :
    (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ (f p.1, p.2)) = μ.map f ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

end MapComap

end MeasureTheory.Measure
