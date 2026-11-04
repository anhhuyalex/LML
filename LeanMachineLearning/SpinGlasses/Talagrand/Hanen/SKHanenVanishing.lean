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
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiUpdate
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.CoordinatePair
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteTilted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Vanishing of spin differences and cavity derivatives (Talagrand Lemmas 1.11.4, 1.11.5)

This module formalizes the vanishing mechanisms for spin-difference observables at the decoupled
endpoint of the cavity path:
* Combinatorial pigeonhole principle for disjoint index sets
  (`exists_disjoint_of_card_inter_biUnion_lt`).
* General vanishing of coordinate differences under product measures
  (`integral_spin_diff_eq_zero_of_indep`).
* Decoupled vanishing for spin-difference products, including extra spin-pair factors.
  The derivative version is proved in `SKHanenPathVanishing.lean`.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Real

namespace SpinGlasses

/-- **Combinatorial pigeonhole principle for pairwise disjoint sets.**
If a collection of pairwise disjoint sets `S v` for `v ∈ V` has an intersection with `J` of
cardinality strictly less than `V.card`, then at least one set `S v` is disjoint from `J`. -/
theorem exists_disjoint_of_card_inter_biUnion_lt {α β : Type*} [DecidableEq β]
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
  have hdisj' : (V : Set α).PairwiseDisjoint (fun v => S v ∩ J) := by
    intro u hu w hw huw
    exact (hdisj hu hw huw).mono inter_subset_left inter_subset_left
  have hcard_eq : (V.biUnion (fun v => S v ∩ J)).card = ∑ v ∈ V, (S v ∩ J).card :=
    Finset.card_biUnion hdisj'
  rw [Finset.biUnion_inter, hcard_eq] at hcard
  omega

/-- **General vanishing of coordinate differences under a product measure.**
If `G` does not depend on coordinates `x` and `y`, and the coordinate functions `f_x` and `f_y` have
equal expectation under their respective coordinate measures, then the integral of
`(f_x(σ x) - f_y(σ y)) * G(σ)` vanishes identically under the product measure. -/
theorem integral_spin_diff_eq_zero_of_indep {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Finite (X i)] [(i : ι) → MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (x y : ι) (hxy : x ≠ y)
    (f_x : X x → ℝ) (f_y : X y → ℝ)
    (h_mean : (∫ t, f_x t ∂μ x) = (∫ t, f_y t ∂μ y))
    (G : (∀ i, X i) → ℝ)
    (hx : ∀ σ t, G (Function.update σ x t) = G σ)
    (hy : ∀ σ t, G (Function.update σ y t) = G σ) :
    ∫ σ, (f_x (σ x) - f_y (σ y)) * G σ ∂Measure.pi μ = 0 := by
  rw [integral_pi_mul_pair_of_invariant μ x y hxy (fun a b => f_x a - f_y b) G hx hy]
  have hm : (∫ a, ∫ b, f_x a - f_y b ∂μ y ∂μ x) =
      (∫ a, f_x a ∂μ x) - ∫ b, f_y b ∂μ y := by
    simp_rw [integral_sub Integrable.of_finite Integrable.of_finite,
      integral_const, probReal_univ, one_smul]
  rw [hm, h_mean, sub_self, zero_mul]

/-- Specialized pigeonhole principle for replica pairs: if `V* ∩ J` has cardinality strictly
less than `V.card`, there exists `v ∈ V` whose pair `pairMap v = (p₁, p₂)` has both elements
outside `J`. -/
theorem exists_pair_disjoint_of_card_lt {α β : Type*} [DecidableEq β]
    (V : Finset α) (pairMap : α → β × β) (J : Finset β)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (hcard : (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card < V.card) :
    ∃ v ∈ V, (pairMap v).1 ∉ J ∧ (pairMap v).2 ∉ J := by
  have hpair_disj :
      (V : Set α).PairwiseDisjoint (fun v => ({(pairMap v).1, (pairMap v).2} : Finset β)) := by
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
  obtain ⟨h1, h2⟩ := Finset.disjoint_insert_left.mp hdisj_v
  exact ⟨v, hv, h1, Finset.disjoint_singleton_left.mp h2⟩

/-- Cardinality bound for derivative index sets: adding `m` pairs of replica indices to `J`
increases the intersection with `V*` by at most `2 * m`. If `2 * m + r < card V` and
`card (V* ∩ J) ≤ r`, then the union still intersects `V*` strictly less than `card V`. -/
theorem card_inter_biUnion_union_pairs_lt {α β : Type*} [DecidableEq β]
    (V : Finset α) (S : α → Finset β) (J : Finset β)
    {m r : ℕ} (p : Fin m → β × β)
    (hcard : (V.biUnion S ∩ J).card ≤ r)
    (hr : 2 * m + r < V.card) :
    (V.biUnion S ∩ (J ∪ Finset.univ.biUnion (fun j => {(p j).1, (p j).2}))).card < V.card := by
  let Jpairs : Finset β := Finset.univ.biUnion (fun j => {(p j).1, (p j).2})
  have h_inter : V.biUnion S ∩ (J ∪ Jpairs) = (V.biUnion S ∩ J) ∪ (V.biUnion S ∩ Jpairs) :=
    Finset.inter_union_distrib_left (V.biUnion S) J Jpairs
  rw [h_inter]
  have h_le := card_union_le (V.biUnion S ∩ J) (V.biUnion S ∩ Jpairs)
  have h_sub : (V.biUnion S ∩ Jpairs).card ≤ Jpairs.card := card_le_card inter_subset_right
  have h_pairs : Jpairs.card ≤ 2 * m := by
    simpa [Jpairs, mul_comm] using
      Finset.card_biUnion_le_card_mul (univ : Finset (Fin m))
        (fun j => {(p j).1, (p j).2}) 2 (fun _ _ => card_insert_le _ _)
  omega

/-- A decoupled spin-difference product vanishes if one pair is missed by all extra spin
factors. This exact support criterion also applies at the critical derivative order,
where the numerical cardinality criterion is insufficient. -/
theorem sk_cavity_deriv_zero_vanishing_of_missing_pair {α κ : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (A : α → ℝ) (Y : ℝ) (V : Finset κ) (pairMap : κ → Fin n × Fin n)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (J : Finset (Fin n)) {m : ℕ} (p : Fin m → Fin n × Fin n)
    (v : κ) (hv : v ∈ V)
    (hmiss : (pairMap v).1 ∉ J ∪ univ.biUnion (fun j => {(p j).1, (p j).2}) ∧
      (pairMap v).2 ∉ J ∪ univ.biUnion (fun j => {(p j).1, (p j).2}))
    (F : (Fin n → α) → ℝ)
    (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    ∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) *
        (∏ w ∈ V, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
        (∏ j : Fin m, (((σ (p j).1).2 : ℤˣ) : ℝ) * (((σ (p j).2).2 : ℤˣ) : ℝ)) *
        fhat (fun r => (σ r).2)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun x : α × ℤˣ => A x.1 + ((x.2 : ℤˣ) : ℝ) * Y) = 0 := by
  classical
  have heq : (fun σ : Fin n → α × ℤˣ => F (fun r => (σ r).1) *
      (∏ w ∈ V, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
      (∏ j : Fin m, (((σ (p j).1).2 : ℤˣ) : ℝ) * (((σ (p j).2).2 : ℤˣ) : ℝ)) *
      fhat (fun r => (σ r).2)) =
    fun σ => F (fun r => (σ r).1) *
      ((∏ w ∈ V, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
      (∏ j : Fin m, (((σ (p j).1).2 : ℤˣ) : ℝ) * (((σ (p j).2).2 : ℤˣ) : ℝ)) *
      fhat (fun r => (σ r).2)) := by
    funext σ
    ring
  simp_rw [heq]
  rw [integral_pi_count_tilted_decoupled_prod A Y F
    (fun ε => (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, ((ε j : ℤˣ) : ℝ)) *
      (∏ j : Fin m, (((ε (p j).1 : ℤˣ) : ℝ) * ((ε (p j).2 : ℤˣ) : ℝ))) *
      fhat ε)]
  suffices hH : (∫ ε,
      (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, ((ε j : ℤˣ) : ℝ)) *
      (∏ j : Fin m, (((ε (p j).1 : ℤˣ) : ℝ) * ((ε (p j).2 : ℤˣ) : ℝ))) *
      fhat ε
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun s : ℤˣ => ((s : ℤˣ) : ℝ) * Y)) = 0 by
    rw [hH, mul_zero]
  let Jpairs : Finset (Fin n) := Finset.univ.biUnion (fun j => {(p j).1, (p j).2})
  obtain ⟨hp1_not, hp2_not⟩ := hmiss
  obtain ⟨hp1_J, hp1_pairs⟩ := Finset.notMem_union.mp hp1_not
  obtain ⟨hp2_J, hp2_pairs⟩ := Finset.notMem_union.mp hp2_not
  set p1 := (pairMap v).1
  set p2 := (pairMap v).2
  by_cases h12 : p1 = p2
  · have hzero (ε : Fin n → ℤˣ) : ((ε p1 : ℤˣ) : ℝ) - ((ε p2 : ℤˣ) : ℝ) = 0 := by
      rw [h12, sub_self]
    have hprod_zero (ε : Fin n → ℤˣ) :
        (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) = 0 := by
      rw [(Finset.insert_erase hv).symm, Finset.prod_insert (Finset.notMem_erase v V)]
      rw [mul_eq_zero]
      left
      exact hzero ε
    have hint_zero : (fun ε : Fin n → ℤˣ =>
        (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, ((ε j : ℤˣ) : ℝ)) *
        (∏ j : Fin m, (((ε (p j).1 : ℤˣ) : ℝ) * ((ε (p j).2 : ℤˣ) : ℝ))) *
        fhat ε) = fun _ => 0 := by
      funext ε
      simp [hprod_zero ε]
    simp_rw [hint_zero]
    exact integral_zero (α := Fin n → ℤˣ) (G := ℝ)
  · set G : (Fin n → ℤˣ) → ℝ := fun ε =>
        (∏ w ∈ V.erase v, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, ((ε j : ℤˣ) : ℝ)) *
        (∏ j : Fin m, (((ε (p j).1 : ℤˣ) : ℝ) * ((ε (p j).2 : ℤˣ) : ℝ))) *
        fhat ε
    have hsplit : V = insert v (V.erase v) := (Finset.insert_erase hv).symm
    have hp1_mem : p1 ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) := by
      rw [Finset.mem_biUnion]
      exact ⟨v, hv, by simp [p1]⟩
    have hp2_mem : p2 ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) := by
      rw [Finset.mem_biUnion]
      exact ⟨v, hv, by simp [p2]⟩
    have hG_p1 (ε : Fin n → ℤˣ) (t : ℤˣ) : G (Function.update ε p1 t) = G ε := by
      dsimp [G]
      congr 1
      · congr 1
        · congr 1
          · refine Finset.prod_congr rfl fun w hw => ?_
            have hwV : w ∈ V := Finset.mem_of_mem_erase hw
            have hne : w ≠ v := Finset.ne_of_mem_erase hw
            obtain ⟨h_u1, h_u2, -, -⟩ := hdisj v hv w hwV hne.symm
            rw [Function.update_of_ne h_u1.symm, Function.update_of_ne h_u2.symm]
          · refine Finset.prod_congr rfl fun j hj => ?_
            have : j ≠ p1 := ne_of_mem_of_not_mem hj hp1_J
            rw [Function.update_of_ne this]
        · refine Finset.prod_congr rfl fun j hj => ?_
          have h1 : (p j).1 ≠ p1 := by
            intro heq
            apply hp1_pairs
            rw [Finset.mem_biUnion]
            exact ⟨j, Finset.mem_univ j, by simp [heq]⟩
          have h2 : (p j).2 ≠ p1 := by
            intro heq
            apply hp1_pairs
            rw [Finset.mem_biUnion]
            exact ⟨j, Finset.mem_univ j, by simp [heq]⟩
          rw [Function.update_of_ne h1, Function.update_of_ne h2]
      · exact hfhat ε p1 t hp1_mem
    have hG_p2 (ε : Fin n → ℤˣ) (t : ℤˣ) : G (Function.update ε p2 t) = G ε := by
      dsimp [G]
      congr 1
      · congr 1
        · congr 1
          · refine Finset.prod_congr rfl fun w hw => ?_
            have hwV : w ∈ V := Finset.mem_of_mem_erase hw
            have hne : w ≠ v := Finset.ne_of_mem_erase hw
            obtain ⟨-, -, h_u1, h_u2⟩ := hdisj v hv w hwV hne.symm
            rw [Function.update_of_ne h_u1.symm, Function.update_of_ne h_u2.symm]
          · refine Finset.prod_congr rfl fun j hj => ?_
            have : j ≠ p2 := ne_of_mem_of_not_mem hj hp2_J
            rw [Function.update_of_ne this]
        · refine Finset.prod_congr rfl fun j hj => ?_
          have h1 : (p j).1 ≠ p2 := by
            intro heq
            apply hp2_pairs
            rw [Finset.mem_biUnion]
            exact ⟨j, Finset.mem_univ j, by simp [heq]⟩
          have h2 : (p j).2 ≠ p2 := by
            intro heq
            apply hp2_pairs
            rw [Finset.mem_biUnion]
            exact ⟨j, Finset.mem_univ j, by simp [heq]⟩
          rw [Function.update_of_ne h1, Function.update_of_ne h2]
      · exact hfhat ε p2 t hp2_mem
    have hpt (ε : Fin n → ℤˣ) :
        (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, ((ε j : ℤˣ) : ℝ)) *
        (∏ j : Fin m, (((ε (p j).1 : ℤˣ) : ℝ) * ((ε (p j).2 : ℤˣ) : ℝ))) *
        fhat ε =
        (((ε p1 : ℤˣ) : ℝ) - ((ε p2 : ℤˣ) : ℝ)) * G ε := by
      rw [hsplit, Finset.prod_insert (Finset.notMem_erase v V)]
      dsimp [G]
      ring
    simp_rw [hpt]
    exact integral_spin_diff_eq_zero_of_indep
      (fun _ : Fin n => Measure.count.tilted fun s : ℤˣ => ((s : ℤˣ) : ℝ) * Y)
      p1 p2 h12
      (fun s => ((s : ℤˣ) : ℝ)) (fun s => ((s : ℤˣ) : ℝ))
      rfl G hG_p1 hG_p2

/-- Decoupled vanishing for products with extra spin-pair factors:
For any finite label set `V` (of any type) of replica pairs with `card V = s`, and any index
set `J` with `card (V* ∩ J) ≤ r`, if `2 * m + r < s`, then the decoupled expectation of any
product formed by `F` (depending only on the first `N` spins), `η_V`, `ε_J`, `m` pairs of
derivative spins, and `f̂` (independent of `V*`), vanishes identically. This is a step towards Lemma 1.11.5;
the identification with the iterated cavity derivative is not part of this statement. -/
theorem sk_cavity_deriv_zero_vanishing {α κ : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (A : α → ℝ) (Y : ℝ) (V : Finset κ) (pairMap : κ → Fin n × Fin n)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (J : Finset (Fin n)) {m r : ℕ} (p : Fin m → Fin n × Fin n)
    (hcard : (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card ≤ r)
    (hr : 2 * m + r < V.card)
    (F : (Fin n → α) → ℝ)
    (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    ∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) *
        (∏ w ∈ V, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
        (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ)) *
        (∏ j : Fin m, (((σ (p j).1).2 : ℤˣ) : ℝ) * (((σ (p j).2).2 : ℤˣ) : ℝ)) *
        fhat (fun r => (σ r).2)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun x : α × ℤˣ => A x.1 + ((x.2 : ℤˣ) : ℝ) * Y) = 0 := by
  let Jpairs : Finset (Fin n) := univ.biUnion (fun j => {(p j).1, (p j).2})
  have hcard_union := card_inter_biUnion_union_pairs_lt V
    (fun v => {(pairMap v).1, (pairMap v).2}) J p hcard hr
  obtain ⟨v, hv, hp1, hp2⟩ := exists_pair_disjoint_of_card_lt V pairMap
    (J ∪ Jpairs) hdisj hcard_union
  exact sk_cavity_deriv_zero_vanishing_of_missing_pair A Y V pairMap hdisj J p
    v hv ⟨hp1, hp2⟩ F fhat hfhat

/-- Decoupled vanishing for a spin-difference product and a product of spins. -/
theorem sk_cavity_decoupled_vanishing {α κ : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (A : α → ℝ) (Y : ℝ) (V : Finset κ) (pairMap : κ → Fin n × Fin n)
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
  have h := sk_cavity_deriv_zero_vanishing A Y V pairMap hdisj J
    (m := 0) (r := (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card)
    (fun j => Fin.elim0 j) (le_refl _) (by simpa using hcard) F (fun _ => 1)
    (by intros; rfl)
  simpa using h

end SpinGlasses
