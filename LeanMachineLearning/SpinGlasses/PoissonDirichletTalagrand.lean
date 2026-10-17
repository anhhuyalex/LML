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

/-- The product of overlap indicators for pairs of replicas in the same block
is the indicator that every block has a single sampled label. -/
theorem partition_overlap_indicator_eq {I K α : Type*} [Fintype I]
    [DecidableEq K] [DecidableEq α] (b : I → K) (σ : I → α) :
    (∏ i : I, ∏ j : I, if b i = b j then
      (if σ i = σ j then (1 : ℝ) else 0) else 1) =
      if ∀ i j, b i = b j → σ i = σ j then 1 else 0 := by
  classical
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
    have hz (p q : I) (hp : p = i) (hq : q = j) :
        (if b p = b q then (if σ p = σ q then (1 : ℝ) else 0) else 1) = 0 := by
      subst p
      subst q
      simp [hij, hne]
    have hinner : (∏ q : I, if b i = b q then
        (if σ i = σ q then (1 : ℝ) else 0) else 1) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ j) (hz i j rfl rfl)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hinner]
    exact (ite_eq_right h).symm

/-- For normalized nonnegative weights, a block-overlap observable has the
product-of-power-sums value dictated by the sizes of its fibers. -/
theorem tsum_partition_overlap_eq_powerSums {I K α : Type*}
    [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K] [DecidableEq α]
    (b : I → K) (hb : Function.Surjective b)
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) :
    (∑' σ : I → α, (∏ i, w (σ i)) *
      (∏ i : I, ∏ j : I, if b i = b j then
        (if σ i = σ j then (1 : ℝ) else 0) else 1)) =
      ∏ m : K, ∑' a, w a ^ Fintype.card {i : I // b i = m} := by
  classical
  simp_rw [partition_overlap_indicator_eq b]
  exact tsum_prod_pi_fiber_eq b hb hw0 hws hw

/-- Pass a random sequence supported almost surely on the compact simplex to a
measurable simplex-valued version, preserving its law and integrals of observables. -/
theorem exists_measurable_poissonDirichletSimplex_version
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (v : Ω → ℕ → ℝ) (hv : Measurable v)
    (hV : ∀ᵐ ω ∂P, v ω ∈ poissonDirichletSimplex) :
    ∃ u : Ω → poissonDirichletSimplex,
      Measurable u ∧ (fun ω => (u ω : ℕ → ℝ)) =ᵐ[P] v := by
  have hne : poissonDirichletSimplex.Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    exact ⟨fun _ => le_refl _, fun _ _ _ => le_refl _, by simp⟩
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
    (hV : ∀ᵐ ω ∂P, v ω ∈ poissonDirichletSimplex)
    (hV' : ∀ᵐ ω ∂P', v' ω ∈ poissonDirichletSimplex)
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
