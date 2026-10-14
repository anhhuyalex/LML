/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Regrouping products and triples of coordinates -/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

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

end MeasureTheory
