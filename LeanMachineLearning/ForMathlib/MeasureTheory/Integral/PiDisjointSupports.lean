/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integral of a product of functions of disjoint coordinate groups

For a product measure `Measure.pi (fun _ : D => μ)` on `D → α` and measurable functions
`Y v` that each depend only on the coordinates in a finite set `S v`, with the sets `S v`
pairwise disjoint, the integral of the product `∏ v ∈ W, Y v` is the product of the integrals.
This is the grouped form of `iIndepFun.integral_fun_prod_comp`, which handles one coordinate
per factor.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace MeasureTheory

/-- **Product of functions of disjoint coordinate groups.** If `Y v` is measurable and depends
only on the coordinates `S v`, and the sets `S v` are pairwise disjoint, then
`∫ ∏_{v ∈ W} Y v = ∏_{v ∈ W} ∫ Y v` under the product measure. No integrability is needed. -/
theorem integral_pi_prod_of_disjoint_supports {α D V : Type*} [MeasurableSpace α] [Inhabited α]
    [Fintype D] [DecidableEq D] [DecidableEq V] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : V → Finset D) (hS : ∀ v w, v ≠ w → Disjoint (S v) (S w)) (Y : V → (D → α) → ℝ)
    (hYm : ∀ v, Measurable (Y v))
    (hY : ∀ v (z z' : D → α), (∀ d ∈ S v, z d = z' d) → Y v z = Y v z') (W : Finset V) :
    ∫ z, ∏ v ∈ W, Y v z ∂(Measure.pi fun _ : D => μ) =
      ∏ v ∈ W, ∫ z, Y v z ∂(Measure.pi fun _ : D => μ) := by
  have hind : iIndepFun (fun (d : D) (z : D → α) => z d) (Measure.pi fun _ : D => μ) :=
    iIndepFun_pi (μ := fun _ : D => μ) (X := fun _ => (id : α → α)) (fun _ => aemeasurable_id)
  -- extension of a function on a coordinate group by the default value
  let ext : ∀ T : Finset D, (T → α) → D → α := fun T f d =>
    if h : d ∈ T then f ⟨d, h⟩ else default
  have hext_meas (T : Finset D) : Measurable (ext T) := by
    refine measurable_pi_iff.2 fun d => ?_
    by_cases h : d ∈ T
    · simp only [ext, h, dite_true]
      exact measurable_pi_apply _
    · simp only [ext, h, dite_false]
      exact measurable_const
  have hrestr (T : Finset D) (v : V) (hv : S v ⊆ T) (z : D → α) :
      Y v z = Y v (ext T fun i : T => z i) := by
    refine hY v _ _ fun d hd => ?_
    simp [ext, hv hd]
  induction W using Finset.induction_on with
  | empty => simp
  | insert w W hw ih =>
    have hprod : (fun z : D → α => ∏ v ∈ insert w W, Y v z) =
        fun z => Y w z * ∏ v ∈ W, Y v z := by
      funext z
      rw [Finset.prod_insert hw]
    rw [hprod, Finset.prod_insert hw, ← ih]
    let T : Finset D := W.biUnion S
    have hdisj : Disjoint (S w) T := by
      rw [Finset.disjoint_biUnion_right]
      exact fun v hv => hS w v fun h => hw (h ▸ hv)
    have hI := hind.indepFun_finset (S w) T hdisj (fun d => measurable_pi_apply d)
    have hSw : S w ⊆ S w := subset_rfl
    have hY1 : (fun z => Y w z) = (fun f : S w → α => Y w (ext (S w) f)) ∘
        (fun z (i : S w) => z i) := by
      funext z
      exact hrestr (S w) w subset_rfl z
    have hYW : (fun z => ∏ v ∈ W, Y v z) = (fun f : T → α => ∏ v ∈ W, Y v (ext T f)) ∘
        (fun z (i : T) => z i) := by
      funext z
      exact Finset.prod_congr rfl fun v hv =>
        hrestr T v (Finset.subset_biUnion_of_mem S hv) z
    have hmeas1 : Measurable (fun f : S w → α => Y w (ext (S w) f)) :=
      (hYm w).comp (hext_meas _)
    have hmeas2 : Measurable (fun f : T → α => ∏ v ∈ W, Y v (ext T f)) :=
      Finset.measurable_prod _ fun v _ => (hYm v).comp (hext_meas _)
    have hI' : IndepFun (fun z => Y w z) (fun z => ∏ v ∈ W, Y v z)
        (Measure.pi fun _ : D => μ) := by
      rw [hY1, hYW]
      exact hI.comp hmeas1 hmeas2
    exact hI'.integral_fun_mul_eq_mul_integral (hYm w).aestronglyMeasurable
      (Finset.measurable_prod _ fun v _ => hYm v).aestronglyMeasurable

end MeasureTheory
