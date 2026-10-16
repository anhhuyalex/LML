/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.ProductMeasure

/-!
# Zipping two infinite product measures

The product of two infinite product measures `(⊗ᵢ μᵢ) ⊗ (⊗ᵢ νᵢ)` is carried by the coordinatewise
pairing `(x, y) ↦ (xᵢ, yᵢ)ᵢ` to the infinite product `⊗ᵢ (μᵢ ⊗ νᵢ)`. Mathlib has the finite
version (`measurePreserving_arrowProdEquivProdArrow`) and the cylinder criterion
`Measure.eq_infinitePi`, which we combine.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Pairing the coordinates of a pair of infinite product measures gives the infinite product of
the product measures. -/
theorem infinitePi_prod_map_zip (μ : ι → Measure X) (ν : ι → Measure Y)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((infinitePi μ).prod (infinitePi ν)).map (fun p i => (p.1 i, p.2 i)) =
      infinitePi fun i => (μ i).prod (ν i) := by
  have hz : Measurable fun p : (ι → X) × (ι → Y) => fun i => (p.1 i, p.2 i) :=
    measurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  refine eq_infinitePi (fun i => (μ i).prod (ν i)) fun s t ht => ?_
  rw [Measure.map_apply hz (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun p : (ι → X) × (ι → Y) => fun i => (p.1 i, p.2 i)) ⁻¹' Set.pi (↑s) t =
      Prod.map s.restrict s.restrict ⁻¹'
        ((MeasurableEquiv.arrowProdEquivProdArrow X Y s).symm ⁻¹'
          Set.univ.pi fun i : s => t i) := by
    ext p
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  have hmap : ((infinitePi μ).prod (infinitePi ν)).map (Prod.map s.restrict s.restrict) =
      (Measure.pi fun i : s => μ i).prod (Measure.pi fun i : s => ν i) := by
    rw [← Measure.map_prod_map _ _ (Finset.measurable_restrict s) (Finset.measurable_restrict s),
      infinitePi_map_restrict, infinitePi_map_restrict]
  have hbox : MeasurableSet (Set.univ.pi fun i : s => t i) :=
    MeasurableSet.univ_pi fun i => ht i
  rw [hpre, ← Measure.map_apply (Finset.measurable_restrict s |>.prodMap
    (Finset.measurable_restrict s)) ((MeasurableEquiv.measurable _) hbox), hmap,
    ((measurePreserving_arrowProdEquivProdArrow X Y s (fun i => μ i) (fun i => ν i)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow X Y s)).measure_preimage hbox.nullMeasurableSet,
    Measure.pi_pi]
  exact Finset.prod_coe_sort s fun i => ((μ i).prod (ν i)) (t i)

end MeasureTheory.Measure
