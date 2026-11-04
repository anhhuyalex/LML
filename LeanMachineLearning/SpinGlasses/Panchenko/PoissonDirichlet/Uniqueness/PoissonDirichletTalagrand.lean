/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletUniquenessMoments
public import LeanMachineLearning.ForMathlib.Topology.Algebra.InfiniteSum.PiProd

/-!
# Partition observables for Talagrand's identities

A surjective map from replica positions to finite block labels describes a partition
without introducing a separate partition structure. The diagonal overlap indicator
imposes exactly the corresponding equality constraint on sampled labels.
-/

@[expose] public section

namespace SpinGlasses

/-- The product of two zero-one indicators is the indicator of the conjunction. -/
theorem ite_one_zero_mul {R : Type*} [MulZeroOneClass R] (p q : Prop) [Decidable p]
    [Decidable q] :
    (if p then (1 : R) else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  split_ifs <;> simp_all

/-- The product of overlap indicators for pairs of replicas in the same block
is the indicator that every block has a single sampled label. -/
theorem partition_overlap_indicator_eq {I K α : Type*} [Fintype I]
    [DecidableEq K] [DecidableEq α] (b : I → K) (σ : I → α) :
    (∏ i : I, ∏ j : I, if b i = b j then
      (if σ i = σ j then (1 : ℝ) else 0) else 1) =
      if ∀ i j, b i = b j → σ i = σ j then 1 else 0 := by
  by_cases h : ∀ i j, b i = b j → σ i = σ j
  · have hterm (i j : I) :
        (if b i = b j then (if σ i = σ j then (1 : ℝ) else 0) else 1) = 1 := by
      split_ifs with hij heq
      · rfl
      · exact False.elim (heq (h i j hij))
      · rfl
    simp only [hterm, Finset.prod_const_one, ite_eq_left h]
  · have hbad : ∃ i j, b i = b j ∧ σ i ≠ σ j := by
      push Not at h
      exact h
    obtain ⟨i, j, hij, hne⟩ := hbad
    have hinner : (∏ q : I, if b i = b q then
        (if σ i = σ q then (1 : ℝ) else 0) else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hij, hne])
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hinner]
    exact (ite_eq_right h).symm

/-- For nonnegative summable weights, a block-overlap observable has the
product-of-power-sums value dictated by the sizes of its fibers. -/
theorem tsum_partition_overlap_eq_powerSums {I K α : Type*}
    [Fintype I] [Fintype K] [DecidableEq K] [DecidableEq α]
    (b : I → K) (hb : Function.Surjective b)
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w) :
    (∑' σ : I → α, (∏ i, w (σ i)) *
      (∏ i : I, ∏ j : I, if b i = b j then
        (if σ i = σ j then (1 : ℝ) else 0) else 1)) =
      ∏ m : K, ∑' a, w a ^ Fintype.card {i : I // b i = m} := by
  simp_rw [partition_overlap_indicator_eq b]
  exact tsum_prod_pi_fiber_eq b hb hw0 hws

/-- An overlap between two labels either preserves a block constraint or merges
exactly the two blocks containing the labels. This formulation avoids relabeling
finite block indices. -/
theorem partition_overlap_merge_indicator {I K α : Type*} [Fintype I]
    [DecidableEq K] [DecidableEq α] (b : I → K) (σ : I → α)
    (r l : I) :
    (∏ i : I, ∏ j : I, if b i = b j then
      (if σ i = σ j then (1 : ℝ) else 0) else 1) *
        (if σ r = σ l then 1 else 0) =
      if (∀ i j, b i = b j → σ i = σ j) ∧ σ r = σ l then 1 else 0 := by
  rw [partition_overlap_indicator_eq, ite_one_zero_mul]

/-- If the two replicas are already in one block, their extra overlap factor
has no effect on the constrained replica observable. -/
theorem partition_overlap_same_block {I K α : Type*} [Fintype I]
    [DecidableEq K] [DecidableEq α] (b : I → K) (σ : I → α)
    (r l : I) (h : b r = b l) :
    (∏ i : I, ∏ j : I, if b i = b j then
      (if σ i = σ j then (1 : ℝ) else 0) else 1) *
        (if σ r = σ l then 1 else 0) =
      ∏ i : I, ∏ j : I, if b i = b j then
        (if σ i = σ j then (1 : ℝ) else 0) else 1 := by
  rw [partition_overlap_merge_indicator, partition_overlap_indicator_eq]
  by_cases hc : ∀ i j, b i = b j → σ i = σ j
  · simp [hc r l h]
  · simp [hc]

/-- A fresh replica attached to the block of `r` makes the old block
constraint exactly the fiber constraint of the extended block map. -/
theorem partition_overlap_fresh_indicator {I K α : Type*} [Fintype I]
    [DecidableEq K] [DecidableEq α] (b : I → K) (τ : Option I → α) (r : I) :
    (∏ i : I, ∏ j : I, if b i = b j then
      (if τ (some i) = τ (some j) then (1 : ℝ) else 0) else 1) *
        (if τ (some r) = τ none then 1 else 0) =
      if ∀ x y : Option I,
        x.elim (b r) b = y.elim (b r) b → τ x = τ y
      then 1 else 0 := by
  rw [partition_overlap_indicator_eq]
  have hiff :
      (∀ i j, b i = b j → τ (some i) = τ (some j)) ∧
        τ (some r) = τ none ↔
      ∀ x y : Option I,
        x.elim (b r) b = y.elim (b r) b → τ x = τ y := by
    constructor
    · rintro ⟨h, hr⟩ x y
      cases x with
      | none =>
        cases y with
        | none => exact fun _ => rfl
        | some j =>
          intro hj
          exact hr.symm.trans (h r j hj)
      | some i =>
        cases y with
        | none =>
          intro hi
          exact (h i r hi).trans hr
        | some j => exact h i j
    · intro h
      refine ⟨fun i j hij => h (some i) (some j) hij, ?_⟩
      exact h (some r) none rfl
  rw [ite_one_zero_mul]
  exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)

/-- The fresh-replica overlap series is the product of power sums with
one extra replica in the block containing `r`. -/
theorem tsum_partition_overlap_fresh_eq_powerSums {I K α : Type*}
    [Fintype I] [Fintype K] [DecidableEq K] [DecidableEq α]
    (b : I → K) (hb : Function.Surjective b) (r : I)
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w) :
    (∑' τ : Option I → α, (∏ o, w (τ o)) *
      ((∏ i : I, ∏ j : I, if b i = b j then
        (if τ (some i) = τ (some j) then (1 : ℝ) else 0) else 1) *
        (if τ (some r) = τ none then 1 else 0))) =
      ∏ m : K, ∑' a, w a ^
        Fintype.card {o : Option I // o.elim (b r) b = m} := by
  have hext : Function.Surjective (fun o : Option I => o.elim (b r) b) := by
    intro m
    obtain ⟨i, hi⟩ := hb m
    exact ⟨some i, hi⟩
  simp_rw [partition_overlap_fresh_indicator b]
  exact tsum_prod_pi_fiber_eq (fun o : Option I => o.elim (b r) b)
    hext hw0 hws

/-- A measurable block observable, formulated directly on overlap matrices. -/
theorem measurable_partition_overlap_observable {I K : Type*}
    [Fintype I] [DecidableEq K] (b : I → K) :
    Measurable (fun R : I → I → ℝ =>
      ∏ i : I, ∏ j : I, if b i = b j then R i j else 1) := by
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  split_ifs <;> fun_prop

/-- Merging two distinct blocks is again a fiber constraint, now for the
quotient block map that sends the second block to the first. -/
theorem partition_overlap_merge_as_fiber {I K α : Type*} [Fintype I]
    [DecidableEq K] [DecidableEq α] (b : I → K) (σ : I → α)
    (r l : I) :
    (∏ i : I, ∏ j : I, if b i = b j then
      (if σ i = σ j then (1 : ℝ) else 0) else 1) *
      (if σ r = σ l then 1 else 0) =
    if ∀ i j, (if b i = b l then b r else b i) =
      (if b j = b l then b r else b j) → σ i = σ j then 1 else 0 := by
  rw [partition_overlap_merge_indicator]
  congr 1
  apply propext
  constructor
  · rintro ⟨h, hrl⟩ i j hij
    by_cases hi : b i = b l <;> by_cases hj : b j = b l
    · exact h i j (hi.trans hj.symm)
    · have hbj : b j = b r := by simpa [hi, hj] using hij.symm
      exact (h i l hi).trans (hrl.symm.trans (h r j hbj.symm))
    · have hbi : b i = b r := by simpa [hi, hj] using hij
      exact (h i r hbi).trans (hrl.trans (h l j hj.symm))
    · exact h i j (by simpa [hi, hj] using hij)
  · intro h
    constructor
    · intro i j hij
      apply h i j
      rw [hij]
    · apply h r l
      simp

/-- Merging labels `b l` into `b r` preserves surjectivity onto the
remaining block labels. This supplies the domain for the partition-series
identity without choosing a new `Fin` numbering. -/
theorem partition_merge_surjective {I K : Type*} [DecidableEq K]
    (b : I → K) (hb : Function.Surjective b) (r l : I)
    (hbl : b r ≠ b l) :
    Function.Surjective (fun i : I =>
      (⟨if b i = b l then b r else b i, by
        split_ifs with hi
        · exact hbl
        · exact hi⟩ : {m : K // m ≠ b l})) := by
  intro m
  obtain ⟨i, hi⟩ := hb m.1
  refine ⟨i, ?_⟩
  apply Subtype.ext
  simp [hi, m.2]

/-- The fresh replica contributes one position to exactly one fiber. -/
theorem card_partition_fresh_fiber {I K : Type*} [Fintype I]
    [DecidableEq K] (b : I → K) (r : I) (m : K) :
    Fintype.card {o : Option I // o.elim (b r) b = m} =
      Fintype.card {i : I // b i = m} + if b r = m then 1 else 0 := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_option, Option.elim]
  exact add_comm _ _

/-- Merging two block labels evaluates the old-replica overlap as a product of
power sums on the remaining block-label subtype. No renumbering of `Fin k` is needed. -/
theorem tsum_partition_overlap_merged_eq_powerSums {I K α : Type*}
    [Fintype I] [Fintype K] [DecidableEq K] [DecidableEq α]
    (b : I → K) (hb : Function.Surjective b) (r l : I) (hbl : b r ≠ b l)
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w) :
    (∑' σ : I → α, (∏ i, w (σ i)) *
      ((∏ i : I, ∏ j : I, if b i = b j then
        (if σ i = σ j then (1 : ℝ) else 0) else 1) *
        (if σ r = σ l then 1 else 0))) =
      ∏ m : {m : K // m ≠ b l}, ∑' a, w a ^
        Fintype.card {i : I //
          (⟨if b i = b l then b r else b i, by
            split_ifs with hi
            · exact hbl
            · exact hi⟩ : {m : K // m ≠ b l}) = m} := by
  simp_rw [partition_overlap_merge_as_fiber b]
  convert tsum_prod_pi_fiber_eq _ (partition_merge_surjective b hb r l hbl)
    hw0 hws using 1
  · apply tsum_congr
    intro σ
    congr 1
    congr 1
    apply propext
    simp only [Subtype.mk.injEq]

/-- Pass a random sequence supported almost surely on the compact simplex to a
measurable simplex-valued version, preserving its law and integrals of observables. -/
theorem exists_measurable_poissonDirichletSimplex_version
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (v : Ω → ℕ → ℝ) (hv : Measurable v)
    (hV : ∀ᵐ ω ∂P, v ω ∈ 𝕍) :
    ∃ u : Ω → 𝕍,
      Measurable u ∧ (fun ω => (u ω : ℕ → ℝ)) =ᵐ[P] v := by
  have hne : Set.Nonempty 𝕍 := ⟨_, zero_mem_poissonDirichletSimplex⟩
  obtain ⟨g, hg, hmem, hvg⟩ :=
    hv.aemeasurable.exists_ae_eq_range_subset hV hne
  refine ⟨fun ω => ⟨g ω, hmem (Set.mem_range_self ω)⟩, hg.subtype_mk, ?_⟩
  exact hvg.symm

/-- A convenient measure-determination criterion for random decreasing weights:
compare mixed higher power sums on the original probability spaces, without
having to construct the simplex-valued versions explicitly. -/
theorem identDistrib_of_poissonDirichlet_powerSum_products
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : MeasureTheory.Measure Ω) (P' : MeasureTheory.Measure Ω')
    [MeasureTheory.IsProbabilityMeasure P] [MeasureTheory.IsProbabilityMeasure P']
    (v : Ω → ℕ → ℝ) (v' : Ω' → ℕ → ℝ)
    (hv : Measurable v) (hv' : Measurable v')
    (hV : ∀ᵐ ω ∂P, v ω ∈ 𝕍)
    (hV' : ∀ᵐ ω ∂P', v' ω ∈ 𝕍)
    (h : ∀ (k : ℕ) (s : Fin k → ℕ) (_hs : ∀ i, 2 ≤ s i),
      (∫ ω, ∏ i, (∑' j, v ω j ^ s i) ∂P) =
        ∫ ω, ∏ i, (∑' j, v' ω j ^ s i) ∂P') :
    ProbabilityTheory.IdentDistrib v v' P P' := by
  obtain ⟨u, hu, hvee⟩ :=
    exists_measurable_poissonDirichletSimplex_version P v hv hV
  obtain ⟨u', hu', hvee'⟩ :=
    exists_measurable_poissonDirichletSimplex_version P' v' hv' hV'
  have heq : P.map u = P'.map u' := by
    apply poissonDirichletSimplex_measure_ext_of_powerSum_products
    intro k s hs
    rw [MeasureTheory.integral_map hu.aemeasurable (by fun_prop),
      MeasureTheory.integral_map hu'.aemeasurable (by fun_prop)]
    have ha : (fun ω => ∏ i, (poissonDirichletPowerSum (s i) (hs i)) (u ω)) =ᵐ[P]
        fun ω => ∏ i, (∑' j, v ω j ^ s i) := by
      filter_upwards [hvee] with ω hω
      rw [← hω]
      rfl
    have hb : (fun ω => ∏ i, (poissonDirichletPowerSum (s i) (hs i)) (u' ω)) =ᵐ[P']
        fun ω => ∏ i, (∑' j, v' ω j ^ s i) := by
      filter_upwards [hvee'] with ω hω
      rw [← hω]
      rfl
    rw [MeasureTheory.integral_congr_ae ha, MeasureTheory.integral_congr_ae hb]
    exact h k s hs
  have heq' : P.map (fun ω => (u ω : ℕ → ℝ)) =
      P'.map (fun ω => (u' ω : ℕ → ℝ)) := by
    calc
      _ = (P.map u).map Subtype.val := (MeasureTheory.Measure.map_map
        measurable_subtype_coe hu).symm
      _ = (P'.map u').map Subtype.val := by rw [heq]
      _ = _ := MeasureTheory.Measure.map_map
        measurable_subtype_coe hu'
  refine ⟨hv.aemeasurable, hv'.aemeasurable, ?_⟩
  calc
    P.map v = P.map (fun ω => (u ω : ℕ → ℝ)) :=
      MeasureTheory.Measure.map_congr hvee.symm
    _ = P'.map (fun ω => (u' ω : ℕ → ℝ)) := heq'
    _ = P'.map v' := MeasureTheory.Measure.map_congr hvee'

end SpinGlasses
