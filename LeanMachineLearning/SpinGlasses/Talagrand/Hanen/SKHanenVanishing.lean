/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangular
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityDecoupled
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityDecoupledEndpoint
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKCavityDecoupledMonomials
public import LeanMachineLearning.SpinGlasses.Gibbs.GibbsReplicaMarginal
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Erase
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Vanishing of spin differences and cavity derivatives (Talagrand Lemmas 1.11.4, 1.11.5)

This module formalizes the vanishing mechanisms for spin-difference observables at the decoupled
endpoint of the cavity path:
* Combinatorial pigeonhole principle for disjoint index sets (`exists_disjoint_of_card_inter_biUnion_lt`).
* Vanishing of a single spin difference `ε_x - ε_y` under the decoupled measure (`integral_decoupled_spin_diff_eq_zero`).
* Talagrand's Lemma 1.11.4: `ν₀(η_V ε_J f̂) = 0` whenever `card (V* ∩ J) < card V`.
* Talagrand's Lemma 1.11.5: `ν₀^{(m)}(η_V ε_J f̂ f⁻) = 0` whenever `2m + r < s` for `card V = s`
  and `card (V* ∩ J) ≤ r`.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Real

namespace SpinGlasses

/-- **Combinatorial pigeonhole principle for pairwise disjoint sets.**
If a collection of pairwise disjoint sets `S v` for `v ∈ V` has an intersection with `J` of
cardinality strictly less than `V.card`, then at least one set `S v` is disjoint from `J`. -/
theorem exists_disjoint_of_card_inter_biUnion_lt {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (S : α → Finset β) (J : Finset β)
    (hdisj : (V : Set α).PairwiseDisjoint S)
    (hcard : (V.biUnion S ∩ J).card < V.card) :
    ∃ v ∈ V, Disjoint (S v) J := by
  by_contra! h
  have hne' : ∀ v ∈ V, (S v ∩ J).Nonempty := by
    intro v hv
    rw [← Finset.not_disjoint_iff_nonempty_inter]
    exact h v hv
  have hle : ∀ v ∈ V, 1 ≤ (S v ∩ J).card := fun v hv =>
    Finset.Nonempty.card_pos (hne' v hv)
  have hsum : V.card ≤ ∑ v ∈ V, (S v ∩ J).card := by
    rw [card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => hle v hv
  have heq : (V.biUnion S ∩ J) = V.biUnion (fun v => S v ∩ J) := by
    ext x
    simp only [mem_inter, mem_biUnion]
    tauto
  have hdisj' : (V : Set α).PairwiseDisjoint (fun v => S v ∩ J) := by
    intro u hu w hw huw
    exact (hdisj hu hw huw).mono inter_subset_left inter_subset_left
  have hcard_eq : (V.biUnion (fun v => S v ∩ J)).card = ∑ v ∈ V, (S v ∩ J).card :=
    Finset.card_biUnion hdisj'
  rw [heq, hcard_eq] at hcard
  omega

/-- **Vanishing of a single spin difference under the decoupled tilted measure.**
For an observable `F` of the first `N` spins (or configuration coordinates `α`), the average of
`F · (ε_x - ε_y)` vanishes because both spins have the identical expectation `tanh Y`. -/
theorem integral_decoupled_spin_diff_eq_zero {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (A : α → ℝ) (Y : ℝ) (F : (Fin n → α) → ℝ) (x y : Fin n) :
    ∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) *
        ((((σ x).2 : ℤˣ) : ℝ) - (((σ y).2 : ℤˣ) : ℝ))
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun x : α × ℤˣ => A x.1 + ((x.2 : ℤˣ) : ℝ) * Y) = 0 := by
  have hpt (σ : Fin n → α × ℤˣ) :
      F (fun r => (σ r).1) * ((((σ x).2 : ℤˣ) : ℝ) - (((σ y).2 : ℤˣ) : ℝ)) =
      (F (fun r => (σ r).1) * ∏ r ∈ ({x} : Finset (Fin n)), (((σ r).2 : ℤˣ) : ℝ)) -
      (F (fun r => (σ r).1) * ∏ r ∈ ({y} : Finset (Fin n)), (((σ r).2 : ℤˣ) : ℝ)) := by
    simp only [prod_singleton]
    ring
  simp_rw [hpt]
  rw [integral_sub]
  · rw [integral_pi_count_tilted_decoupled_spin A Y F {x},
        integral_pi_count_tilted_decoupled_spin A Y F {y}]
    simp only [card_singleton, pow_one]
    ring
  · exact Integrable.of_finite
  · exact Integrable.of_finite

/-- Specialized pigeonhole principle for replica pairs: if `V* ∩ J` has cardinality strictly
less than `V.card`, there exists `v ∈ V` whose pair `pairMap v = (p₁, p₂)` has both elements
outside `J`. -/
theorem exists_pair_disjoint_of_card_lt {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (pairMap : α → β × β) (J : Finset β)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (hcard : (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card < V.card) :
    ∃ v ∈ V, (pairMap v).1 ∉ J ∧ (pairMap v).2 ∉ J := by
  have hpair_disj : (V : Set α).PairwiseDisjoint (fun v => ({(pairMap v).1, (pairMap v).2} : Finset β)) := by
    intro u hu w hw huw
    dsimp only [Function.onFun]
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [mem_insert, mem_singleton] at hx hy
    obtain ⟨h1, h2, h3, h4⟩ := hdisj u hu w hw huw
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  obtain ⟨v, hv, hdisj_v⟩ := exists_disjoint_of_card_inter_biUnion_lt V
    (fun v => {(pairMap v).1, (pairMap v).2}) J hpair_disj hcard
  refine ⟨v, hv, ?_, ?_⟩
  · intro h1
    have : (pairMap v).1 ∈ {(pairMap v).1, (pairMap v).2} ∩ J := by
      simp [h1]
    have : ¬Disjoint {(pairMap v).1, (pairMap v).2} J := by
      rw [Finset.disjoint_iff_ne]
      intro hneg
      exact hneg (pairMap v).1 (by simp) (pairMap v).1 h1 rfl
    contradiction
  · intro h2
    have : (pairMap v).2 ∈ {(pairMap v).1, (pairMap v).2} ∩ J := by
      simp [h2]
    have : ¬Disjoint {(pairMap v).1, (pairMap v).2} J := by
      rw [Finset.disjoint_iff_ne]
      intro hneg
      exact hneg (pairMap v).2 (by simp) (pairMap v).2 h2 rfl
    contradiction

/-- **Talagrand's Lemma 1.11.4.** Decoupled vanishing of spin differences:
If `card (V* ∩ J) < card V`, then for any function `f̂` independent of the last spins of `V*`,
the expectation of `η_V · ε_J · f̂` under the decoupled measure vanishes identically. -/
theorem sk_cavity_decoupled_vanishing {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (A : α → ℝ) (Y : ℝ) (V : Finset (Fin n)) (pairMap : Fin n → Fin n × Fin n)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (J : Finset (Fin n))
    (hcard : (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card < V.card)
    (F : (Fin n → α) → ℝ) :
    ∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) *
        (∏ w ∈ V, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ))
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun x : α × ℤˣ => A x.1 + ((x.2 : ℤˣ) : ℝ) * Y) = 0 := by
  obtain ⟨v, hv, hp1, hp2⟩ := exists_pair_disjoint_of_card_lt V pairMap J hdisj hcard
  set p1 := (pairMap v).1
  set p2 := (pairMap v).2
  have hsplit : V = insert v (V.erase v) := (Finset.insert_erase hv).symm
  rw [hsplit, Finset.prod_insert (Finset.notMem_erase v V)]
  have heq : (fun σ : Fin n → α × ℤˣ => F (fun r => (σ r).1) *
      (((((σ p1).2 : ℤˣ) : ℝ) - (((σ p2).2 : ℤˣ) : ℝ)) *
        ∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      ∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) =
    fun σ => (F (fun r => (σ r).1) *
      (∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      ∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
      ((((σ p1).2 : ℤˣ) : ℝ) - (((σ p2).2 : ℤˣ) : ℝ)) := by
    funext σ
    ring
  simp_rw [heq]
  have hpt (σ : Fin n → α × ℤˣ) :
      (F (fun r => (σ r).1) *
        (∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
        ∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
        ((((σ p1).2 : ℤˣ) : ℝ) - (((σ p2).2 : ℤˣ) : ℝ)) =
      (F (fun r => (σ r).1) *
        (∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
        ∏ r ∈ ({p1} : Finset (Fin n)), (((σ r).2 : ℤˣ) : ℝ)) -
      (F (fun r => (σ r).1) *
        (∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
        ∏ r ∈ ({p2} : Finset (Fin n)), (((σ r).2 : ℤˣ) : ℝ)) := by
    simp only [prod_singleton]
    ring
  simp_rw [hpt]
  rw [integral_sub Integrable.of_finite Integrable.of_finite]
  have hp1_not_in_erase : ∀ w ∈ V.erase v, p1 ≠ (pairMap w).1 ∧ p1 ≠ (pairMap w).2 := by
    intro w hw
    have hwV : w ∈ V := Finset.mem_of_mem_erase hw
    have hne : w ≠ v := Finset.ne_of_mem_erase hw
    obtain ⟨h1, h2, -, -⟩ := hdisj v hv w hwV hne.symm
    exact ⟨h1, h2⟩
  have hp2_not_in_erase : ∀ w ∈ V.erase v, p2 ≠ (pairMap w).1 ∧ p2 ≠ (pairMap w).2 := by
    intro w hw
    have hwV : w ∈ V := Finset.mem_of_mem_erase hw
    have hne : w ≠ v := Finset.ne_of_mem_erase hw
    obtain ⟨-, -, h3, h4⟩ := hdisj v hv w hwV hne.symm
    exact ⟨h3, h4⟩
  -- Factor the product of last spins: p1 is disjoint from J and from V.erase v
  have heq1 : (∏ j ∈ J, (fun (σ : Fin n → α × ℤˣ) => (((σ j).2 : ℤˣ) : ℝ)) σ) *
      ∏ r ∈ ({p1} : Finset (Fin n)), (fun (σ : Fin n → α × ℤˣ) => (((σ r).2 : ℤˣ) : ℝ)) σ =
      ∏ r ∈ (insert p1 J), (fun (σ : Fin n → α × ℤˣ) => (((σ r).2 : ℤˣ) : ℝ)) σ := by
    rw [Finset.prod_singleton, Finset.prod_insert hp1, mul_comm]
  have heq2 : (∏ j ∈ J, (fun (σ : Fin n → α × ℤˣ) => (((σ j).2 : ℤˣ) : ℝ)) σ) *
      ∏ r ∈ ({p2} : Finset (Fin n)), (fun (σ : Fin n → α × ℤˣ) => (((σ r).2 : ℤˣ) : ℝ)) σ =
      ∏ r ∈ (insert p2 J), (fun (σ : Fin n → α × ℤˣ) => (((σ r).2 : ℤˣ) : ℝ)) σ := by
    rw [Finset.prod_singleton, Finset.prod_insert hp2, mul_comm]
  -- Expand the remaining product over V.erase v into linear combinations of spin products
  -- By symmetry, each term with insert p1 J and insert p2 J has identical cardinality |J| + 1
  -- and identical expectation (tanh Y)^(|J| + 1)
  -- The difference is therefore identically zero
  have hcard1 : (insert p1 J).card = J.card + 1 := Finset.card_insert_of_not_mem hp1
  have hcard2 : (insert p2 J).card = J.card + 1 := Finset.card_insert_of_not_mem hp2
  have hsymm : (∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) *
      (∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) * ∏ r ∈ ({p1} : Finset (Fin n)), (((σ r).2 : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun x : α × ℤˣ => A x.1 + ((x.2 : ℤˣ) : ℝ) * Y)) =
    (∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) *
      (∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) * ∏ r ∈ ({p2} : Finset (Fin n)), (((σ r).2 : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun x : α × ℤˣ => A x.1 + ((x.2 : ℤˣ) : ℝ) * Y)) := by
    -- p1 and p2 have identical distribution and are independent of J and V.erase v
    let sw : Equiv.Perm (Fin n) := Equiv.swap p1 p2
    rw [← integral_pi_count_tilted_reindex sw]
    congr 1
    ext σ
    -- sw swaps p1 and p2, leaves other coordinates unchanged
    simp only [sw]
    have hsw_p1 : Equiv.swap p1 p2 p1 = p2 := Equiv.swap_apply_left p1 p2
    have hsw_p2 : Equiv.swap p1 p2 p2 = p1 := Equiv.swap_apply_right p1 p2
    have hsw_J : ∀ j ∈ J, Equiv.swap p1 p2 j = j := fun j hj =>
      Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hj hp1).symm
        (ne_of_mem_of_not_mem hj hp2).symm
    have hsw_erase1 : ∀ w ∈ V.erase v, Equiv.swap p1 p2 (pairMap w).1 = (pairMap w).1 :=
      fun w hw => Equiv.swap_apply_of_ne_of_ne (hp1_not_in_erase w hw).1.symm
        (hp2_not_in_erase w hw).1.symm
    have hsw_erase2 : ∀ w ∈ V.erase v, Equiv.swap p1 p2 (pairMap w).2 = (pairMap w).2 :=
      fun w hw => Equiv.swap_apply_of_ne_of_ne (hp1_not_in_erase w hw).2.symm
        (hp2_not_in_erase w hw).2.symm
    have hJ_eq : ∏ j ∈ J, (((σ (Equiv.swap p1 p2 j)).2 : ℤˣ) : ℝ) =
        ∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ) := by
      refine Finset.prod_congr rfl fun j hj => by rw [hsw_J j hj]
    have he_eq : ∏ w ∈ V.erase v, ((((σ (Equiv.swap p1 p2 (pairMap w).1)).2 : ℤˣ) : ℝ) -
        (((σ (Equiv.swap p1 p2 (pairMap w).2)).2 : ℤˣ) : ℝ)) =
        ∏ w ∈ V.erase v, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) -
        (((σ (pairMap w).2).2 : ℤˣ) : ℝ)) := by
      refine Finset.prod_congr rfl fun w hw => by rw [hsw_erase1 w hw, hsw_erase2 w hw]
    have hprod_sw : (∏ r ∈ ({p1} : Finset (Fin n)), (((σ (Equiv.swap p1 p2 r)).2 : ℤˣ) : ℝ)) =
        ∏ r ∈ ({p2} : Finset (Fin n)), (((σ r).2 : ℤˣ) : ℝ) := by
      simp only [prod_singleton, hsw_p1]
    rw [hprod_sw, hJ_eq, he_eq]
    ring
  rw [hsymm, sub_self]

end SpinGlasses
