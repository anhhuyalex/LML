/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Regrouping products and triples of coordinates -/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- **Coordinate marginal of a product law:** if `z` has the product law `Measure.pi μ`, then its
`i`-th coordinate has law `μ i`. -/
theorem Measure.map_apply_eq_of_map_eq_pi {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {P : Measure Ω} {μ : ∀ i, Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] {z : Ω → ∀ i, X i} (hz : Measurable z)
    (hl : P.map z = Measure.pi μ) (i : ι) : P.map (fun ω => z ω i) = μ i := by
  rw [show (fun ω => z ω i) = (fun x : ∀ i, X i => x i) ∘ z from rfl,
    ← Measure.map_map (measurable_pi_apply i) hz, hl]
  exact (measurePreserving_eval μ i).map_eq

/-- A triple of coordinates of an i.i.d. vector `Fin 3 → α` is a product measure. -/
theorem measurePreserving_finThreeArrow {α : Type*} {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] :
    MeasurePreserving (fun y : Fin 3 → α => (y 0, y 1, y 2)) (Measure.pi fun _ => μ)
      (μ.prod (μ.prod μ)) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_finTwoArrow μ)
  exact h2.comp h1

/-- Regrouping `((w, u), (v, x)) ↦ ((w, (u, v)), x)` preserves product measures. -/
theorem measurePreserving_prod_regroup {W U V X : Type*} {mW : MeasurableSpace W}
    {mU : MeasurableSpace U} {mV : MeasurableSpace V} {mX : MeasurableSpace X} (μW : Measure W)
    (μU : Measure U) (μV : Measure V) (μX : Measure X) [SFinite μW] [SFinite μU] [SFinite μV]
    [SFinite μX] :
    MeasurePreserving (fun p : (W × U) × (V × X) => ((p.1.1, (p.1.2, p.2.1)), p.2.2))
      ((μW.prod μU).prod (μV.prod μX)) ((μW.prod (μU.prod μV)).prod μX) := by
  have h1 := measurePreserving_prodAssoc μW μU (μV.prod μX)
  have h2 := (MeasurePreserving.id μW).prod
    (measurePreserving_prodAssoc μU μV μX).symm
  have h3 := (measurePreserving_prodAssoc μW (μU.prod μV) μX).symm
  exact h3.comp (h2.comp h1)

/-- **Fubini for two i.i.d. coordinates:** an integrable function of the two coordinates of a point
of `Fin 2 → α` integrates against the product measure as an iterated integral. -/
theorem integral_pi_fin_two_of_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {g : α → α → ℝ} (hg : Integrable (fun p : α × α => g p.1 p.2) (μ.prod μ)) :
    ∫ σ, g (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => μ) = ∫ x, ∫ y, g x y ∂μ ∂μ := by
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
  have := hmp.integral_comp' (g := fun p : α × α => g p.1 p.2)
  simp only [MeasurableEquiv.piFinTwo_apply] at this
  rw [this]
  exact integral_prod (fun p : α × α => g p.1 p.2) hg

/-- **Fubini for two replicas:** a function of the two coordinates of a point of `Fin 2 → α`
integrates against the product measure as an iterated integral. -/
theorem integral_pi_fin_two {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] (μ : Measure α) [IsFiniteMeasure μ] (g : α → α → ℝ) :
    ∫ σ, g (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => μ) = ∫ x, ∫ y, g x y ∂μ ∂μ :=
  integral_pi_fin_two_of_integrable μ Integrable.of_finite

end MeasureTheory
