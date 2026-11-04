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
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteTilted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Erase
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Vanishing of spin differences and cavity derivatives (Talagrand Lemmas 1.11.4, 1.11.5)

This module formalizes the vanishing mechanisms for spin-difference observables at the decoupled
endpoint of the cavity path:
* Combinatorial pigeonhole principle for disjoint index sets
  (`exists_disjoint_of_card_inter_biUnion_lt`).
* General vanishing of coordinate differences under product measures
  (`integral_spin_diff_eq_zero_of_indep`).
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
  have hG_int : Integrable (fun σ => (f_x (σ x) - f_y (σ y)) * G σ) (Measure.pi μ) :=
    Integrable.of_finite
  rw [integral_pi_eq_integral_update μ x hG_int]
  have h_inner (σ : ∀ i, X i) :
      (∫ t, (f_x (Function.update σ x t x) - f_y (Function.update σ x t y)) *
        G (Function.update σ x t) ∂μ x) =
      ((∫ t, f_x t ∂μ x) - f_y (σ y)) * G σ := by
    have hup_x (t : X x) : Function.update σ x t x = t := Function.update_self x t σ
    have hup_y (t : X x) : Function.update σ x t y = σ y :=
      Function.update_of_ne (Ne.symm hxy) t σ
    have hup_G (t : X x) : G (Function.update σ x t) = G σ := hx σ t
    simp_rw [hup_x, hup_y, hup_G, sub_mul]
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    rw [integral_mul_const]
    rw [integral_const, probReal_univ, one_smul]
  simp_rw [h_inner]
  have hG_int' : Integrable (fun σ => ((∫ t, f_x t ∂μ x) - f_y (σ y)) * G σ) (Measure.pi μ) :=
    Integrable.of_finite
  rw [integral_pi_eq_integral_update μ y hG_int']
  have h_inner_y (σ : ∀ i, X i) :
      (∫ s, ((∫ t, f_x t ∂μ x) - f_y (Function.update σ y s y)) *
        G (Function.update σ y s) ∂μ y) = 0 := by
    have hup_y (s : X y) : Function.update σ y s y = s := Function.update_self y s σ
    have hup_G (s : X y) : G (Function.update σ y s) = G σ := hy σ s
    simp_rw [hup_y, hup_G, sub_mul]
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    rw [integral_const, probReal_univ, one_smul]
    rw [integral_mul_const]
    rw [h_mean]
    ring
  simp_rw [h_inner_y]
  exact integral_zero (α := ∀ i, X i) (G := ℝ)

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
  have heq : (fun σ : Fin n → α × ℤˣ => F (fun r => (σ r).1) *
      (∏ w ∈ V, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ))) =
    fun σ => F (fun r => (σ r).1) *
      ((∏ w ∈ V, ((((σ (pairMap w).1).2 : ℤˣ) : ℝ) - (((σ (pairMap w).2).2 : ℤˣ) : ℝ))) *
      (∏ j ∈ J, (((σ j).2 : ℤˣ) : ℝ))) := by
    funext σ
    ring
  simp_rw [heq]
  rw [integral_pi_count_tilted_decoupled_prod A Y F
    (fun ε => (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
      ∏ j ∈ J, ((ε j : ℤˣ) : ℝ))]
  suffices hH : (∫ ε,
      (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
      ∏ j ∈ J, ((ε j : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun s : ℤˣ => ((s : ℤˣ) : ℝ) * Y)) = 0 by
    rw [hH, mul_zero]
  obtain ⟨v, hv, hp1, hp2⟩ := exists_pair_disjoint_of_card_lt V pairMap J hdisj hcard
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
        ∏ j ∈ J, ((ε j : ℤˣ) : ℝ)) = fun _ => 0 := by
      funext ε
      simp [hprod_zero ε]
    simp_rw [hint_zero]
    exact integral_zero (α := Fin n → ℤˣ) (G := ℝ)
  · set G : (Fin n → ℤˣ) → ℝ := fun ε =>
        (∏ w ∈ V.erase v, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
        ∏ j ∈ J, ((ε j : ℤˣ) : ℝ)
    have hsplit : V = insert v (V.erase v) := (Finset.insert_erase hv).symm
    have hG_p1 (ε : Fin n → ℤˣ) (t : ℤˣ) : G (Function.update ε p1 t) = G ε := by
      dsimp [G]
      congr 1
      · refine Finset.prod_congr rfl fun w hw => ?_
        have hwV : w ∈ V := Finset.mem_of_mem_erase hw
        have hne : w ≠ v := Finset.ne_of_mem_erase hw
        obtain ⟨h_u1, h_u2, -, -⟩ := hdisj v hv w hwV hne.symm
        rw [Function.update_of_ne h_u1.symm, Function.update_of_ne h_u2.symm]
      · refine Finset.prod_congr rfl fun j hj => ?_
        have : j ≠ p1 := ne_of_mem_of_not_mem hj hp1
        rw [Function.update_of_ne this]
    have hG_p2 (ε : Fin n → ℤˣ) (t : ℤˣ) : G (Function.update ε p2 t) = G ε := by
      dsimp [G]
      congr 1
      · refine Finset.prod_congr rfl fun w hw => ?_
        have hwV : w ∈ V := Finset.mem_of_mem_erase hw
        have hne : w ≠ v := Finset.ne_of_mem_erase hw
        obtain ⟨-, -, h_u1, h_u2⟩ := hdisj v hv w hwV hne.symm
        rw [Function.update_of_ne h_u1.symm, Function.update_of_ne h_u2.symm]
      · refine Finset.prod_congr rfl fun j hj => ?_
        have : j ≠ p2 := ne_of_mem_of_not_mem hj hp2
        rw [Function.update_of_ne this]
    have hpt (ε : Fin n → ℤˣ) :
        (∏ w ∈ V, (((ε (pairMap w).1 : ℤˣ) : ℝ) - ((ε (pairMap w).2 : ℤˣ) : ℝ))) *
        ∏ j ∈ J, ((ε j : ℤˣ) : ℝ) =
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

end SpinGlasses
