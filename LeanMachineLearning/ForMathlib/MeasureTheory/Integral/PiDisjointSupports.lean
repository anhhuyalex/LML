/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integral of a product of functions of disjoint coordinate groups

For a product `Measure.pi μ` of probability measures and measurable functions
`Y v` that each depend only on the coordinates in a finite set `S v`, with the sets `S v`
pairwise disjoint, the integral of the product `∏ v ∈ W, Y v` is the product of the integrals.
This is the grouped form of `iIndepFun.integral_fun_prod_comp`, which handles one coordinate
per factor.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace MeasureTheory

/-- **Product of functions of disjoint coordinate groups.** For a product of probability measures
`μ d`, let `Y v`, `v ∈ W`, be measurable functions with values in `ℝ` or `ℂ` which depend only on
the coordinates `S v`, the sets `S v` being pairwise disjoint. Then
`∫ ∏_{v ∈ W} Y v = ∏_{v ∈ W} ∫ Y v`. No integrability is needed. -/
theorem integral_pi_prod_of_disjoint_supports_dep {D V 𝕜 : Type*} [RCLike 𝕜] [Fintype D]
    {α : D → Type*} [∀ d, MeasurableSpace (α d)] (μ : ∀ d, Measure (α d))
    [∀ d, IsProbabilityMeasure (μ d)] (S : V → Finset D) (Y : V → (∀ d, α d) → 𝕜) (W : Finset V)
    (hS : ∀ v ∈ W, ∀ w ∈ W, v ≠ w → Disjoint (S v) (S w)) (hYm : ∀ v ∈ W, Measurable (Y v))
    (hY : ∀ v ∈ W, ∀ z z' : ∀ d, α d, (∀ d ∈ S v, z d = z' d) → Y v z = Y v z') :
    ∫ z, ∏ v ∈ W, Y v z ∂(Measure.pi μ) = ∏ v ∈ W, ∫ z, Y v z ∂(Measure.pi μ) := by
  classical
  have : ∀ d, Nonempty (α d) := fun d => nonempty_of_isProbabilityMeasure (μ d)
  have hind : iIndepFun (fun (d : D) (z : ∀ d, α d) => z d) (Measure.pi μ) :=
    iIndepFun_pi (μ := μ) (X := fun d => (id : α d → α d)) (fun _ => aemeasurable_id)
  -- extension of a function on a coordinate group by an arbitrary value
  let ext : ∀ T : Finset D, (∀ i : T, α i) → ∀ d, α d := fun T f d =>
    if h : d ∈ T then f ⟨d, h⟩ else Classical.arbitrary (α d)
  have hext_meas (T : Finset D) : Measurable (ext T) := by
    refine measurable_pi_iff.2 fun d => ?_
    by_cases h : d ∈ T
    · simp only [ext, h, dite_true]
      exact measurable_pi_apply (⟨d, h⟩ : T)
    · simp only [ext, h, dite_false]
      exact measurable_const
  induction W using Finset.induction_on with
  | empty => simp
  | insert w W hw ih =>
    have hwmem : w ∈ insert w W := Finset.mem_insert_self w W
    have hsub : ∀ v ∈ W, v ∈ insert w W := fun v hv => Finset.mem_insert_of_mem hv
    have hrestr (T : Finset D) (v : V) (hvW : v ∈ insert w W) (hv : S v ⊆ T) (z : ∀ d, α d) :
        Y v z = Y v (ext T fun i : T => z i) := by
      refine hY v hvW _ _ fun d hd => ?_
      simp [ext, hv hd]
    have hprod : (fun z : ∀ d, α d => ∏ v ∈ insert w W, Y v z) =
        fun z => Y w z * ∏ v ∈ W, Y v z := by
      funext z
      rw [Finset.prod_insert hw]
    rw [hprod, Finset.prod_insert hw, ← ih (fun v hv u hu => hS v (hsub v hv) u (hsub u hu))
      (fun v hv => hYm v (hsub v hv)) (fun v hv => hY v (hsub v hv))]
    let T : Finset D := W.biUnion S
    have hdisj : Disjoint (S w) T := by
      rw [Finset.disjoint_biUnion_right]
      exact fun v hv => hS w hwmem v (hsub v hv) fun h => hw (h ▸ hv)
    have hI := hind.indepFun_finset (S w) T hdisj (fun d => measurable_pi_apply d)
    have hY1 : (fun z => Y w z) = (fun f : ∀ i : S w, α i => Y w (ext (S w) f)) ∘
        (fun z (i : S w) => z i) := by
      funext z
      exact hrestr (S w) w hwmem subset_rfl z
    have hYW : (fun z => ∏ v ∈ W, Y v z) =
        (fun f : ∀ i : T, α i => ∏ v ∈ W, Y v (ext T f)) ∘ (fun z (i : T) => z i) := by
      funext z
      exact Finset.prod_congr rfl fun v hv =>
        hrestr T v (hsub v hv) (Finset.subset_biUnion_of_mem S hv) z
    have hmeas1 : Measurable (fun f : ∀ i : S w, α i => Y w (ext (S w) f)) :=
      (hYm w hwmem).comp (hext_meas _)
    have hmeas2 : Measurable (fun f : ∀ i : T, α i => ∏ v ∈ W, Y v (ext T f)) :=
      Finset.measurable_prod _ fun v hv => (hYm v (hsub v hv)).comp (hext_meas _)
    have hI' : IndepFun (fun z => Y w z) (fun z => ∏ v ∈ W, Y v z) (Measure.pi μ) := by
      rw [hY1, hYW]
      exact hI.comp hmeas1 hmeas2
    exact hI'.integral_fun_mul_eq_mul_integral (hYm w hwmem).aestronglyMeasurable
      (Finset.measurable_prod _ fun v hv => hYm v (hsub v hv)).aestronglyMeasurable

/-- **Product of functions of disjoint coordinate groups**, for a power of one measure and real
functions: the homogeneous case of `integral_pi_prod_of_disjoint_supports_dep`. -/
theorem integral_pi_prod_of_disjoint_supports {α D V : Type*} [MeasurableSpace α] [Fintype D]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (S : V → Finset D) (hS : ∀ v w, v ≠ w → Disjoint (S v) (S w)) (Y : V → (D → α) → ℝ)
    (hYm : ∀ v, Measurable (Y v))
    (hY : ∀ v (z z' : D → α), (∀ d ∈ S v, z d = z' d) → Y v z = Y v z') (W : Finset V) :
    ∫ z, ∏ v ∈ W, Y v z ∂(Measure.pi fun _ : D => μ) =
      ∏ v ∈ W, ∫ z, Y v z ∂(Measure.pi fun _ : D => μ) :=
  integral_pi_prod_of_disjoint_supports_dep (fun _ => μ) S Y W (fun v _ w _ h => hS v w h)
    (fun v _ => hYm v) fun v _ => hY v

end MeasureTheory
