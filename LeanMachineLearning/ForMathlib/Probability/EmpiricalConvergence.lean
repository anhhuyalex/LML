/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.Empirical
public import LeanMachineLearning.ForMathlib.Probability.StrongLawMixture
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Weak convergence of empirical measures (Varadarajan)

For an i.i.d. sequence `x` with law `ν` on a second countable space, the empirical measures
`(n + 1)⁻¹ ∑_{i ≤ n} δ_{x i}` converge weakly to `ν` almost surely
(`ProbabilityTheory.ae_tendsto_empiricalMeasure`).  The proof applies the strong law to the
indicators of the countably many finite unions of basic open sets, and the portmanteau theorem
`tendsto_of_forall_isOpen_le_liminf`: every open set is the directed union of such finite unions.

As a deterministic consequence, if the empirical measures of a sequence converge weakly to `ν`,
then every point of the support of `ν` is a cluster point of the sequence
(`MeasureTheory.mapClusterPt_of_tendsto_empiricalMeasure`); hence an i.i.d. sample is almost
surely dense in the support of its law (`ProbabilityTheory.ae_forall_mapClusterPt_of_mem_support`).

## Main declarations

* `ProbabilityTheory.ae_tendsto_empiricalMeasure`: Varadarajan's theorem.
* `MeasureTheory.measure_isOpen_eq_iSup_finset_biUnion`: the measure of an open set is the supremum
  of the measures of the finite unions of basic open sets inside it.
* `MeasureTheory.mapClusterPt_of_tendsto_empiricalMeasure`: support points are cluster points.
* `ProbabilityTheory.ae_forall_mapClusterPt_of_mem_support`: the almost sure form.
-/

@[expose] public section

open MeasureTheory Filter Finset Set TopologicalSpace
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

namespace MeasureTheory

/-- If the empirical measures `(n + 1)⁻¹ ∑_{i ≤ n} δ_{x i}` of a sequence converge weakly to `ν`,
then every point of the support of `ν` is a cluster point of the sequence. -/
theorem mapClusterPt_of_tendsto_empiricalMeasure [MetrizableSpace X] {x : ℕ → X}
    {ν : Measure X} [IsProbabilityMeasure ν]
    (hx : Tendsto (fun n : ℕ => (empiricalMeasure fun i : Fin (n + 1) => x i).toProbabilityMeasure)
      atTop (𝓝 ν.toProbabilityMeasure))
    {p : X} (hp : p ∈ ν.support) : MapClusterPt p atTop x := by
  rw [mapClusterPt_iff_frequently]
  intro U hU
  by_contra hfreq
  rw [not_frequently] at hfreq
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfreq
  have hpos : 0 < ν (interior U) :=
    (ν.mem_support_iff_forall p).1 hp _ (interior_mem_nhds.2 hU)
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hx (isOpen_interior (s := U))
  have hmeas : MeasurableSet (interior U) := isOpen_interior.measurableSet
  have hbound : ∀ n : ℕ, (empiricalMeasure fun i : Fin (n + 1) => x i) (interior U) ≤
      (N : ℝ≥0∞) * ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    rw [empiricalMeasure_apply _ hmeas, mul_comm]
    refine mul_le_mul' ?_ (by simp)
    rw [Fin.sum_univ_eq_sum_range (fun i => (interior U).indicator 1 (x i)) (n + 1)]
    calc ∑ i ∈ range (n + 1), (interior U).indicator (1 : X → ℝ≥0∞) (x i)
        ≤ ∑ i ∈ range N, (interior U).indicator (1 : X → ℝ≥0∞) (x i) :=
          sum_le_sum_of_ne_zero fun i _ hi => by
            rw [Finset.mem_range]
            by_contra hiN
            exact hi (indicator_of_notMem (fun hmem => hN i (not_lt.1 hiN)
              (interior_subset hmem)) _)
      _ ≤ ∑ i ∈ range N, (1 : ℝ≥0∞) := sum_le_sum fun i _ => by
          by_cases h : x i ∈ interior U <;> simp [h]
      _ = N := by simp
  have hzero : Tendsto (fun n : ℕ => (empiricalMeasure fun i : Fin (n + 1) => x i)
      (interior U)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
      hbound
    have h0 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ≥0∞)⁻¹) 1).2
        ENNReal.tendsto_inv_nat_nhds_zero |>.congr fun n => by simp
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.natCast_ne_top N))
  have hlim : atTop.liminf (fun n : ℕ => (((empiricalMeasure fun i : Fin (n + 1) => x i)
      |>.toProbabilityMeasure : ProbabilityMeasure X) : Measure X) (interior U)) = 0 :=
    hzero.liminf_eq
  rw [hlim] at hle
  exact hpos.ne' (le_antisymm hle zero_le)

omit [BorelSpace X] in
/-- **Inner regularity by finite unions of basic open sets.**  In a second countable space, an
open set `G` is the directed union of the finite unions of sets of the countable basis contained in
it, so `ν G` is the supremum of the measures of these finite unions. -/
theorem measure_isOpen_eq_iSup_finset_biUnion [SecondCountableTopology X] (ν : Measure X)
    {G : Set X} (hG : IsOpen G) :
    ν G = ⨆ F : {F : Finset (countableBasis X) // (⋃ b ∈ F, (b : Set X)) ⊆ G},
      ν (⋃ b ∈ F.1, (b : Set X)) := by
  have : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  have hdir : Directed (· ⊆ ·) (fun F : {F : Finset (countableBasis X) //
      (⋃ b ∈ F, (b : Set X)) ⊆ G} => ⋃ b ∈ F.1, (b : Set X)) :=
    fun F₁ F₂ => ⟨⟨F₁.1 ∪ F₂.1, by
      simpa only [Finset.set_biUnion_union] using union_subset F₁.2 F₂.2⟩,
      by simp only [Finset.set_biUnion_union]; exact subset_union_left,
      by simp only [Finset.set_biUnion_union]; exact subset_union_right⟩
  have hunion : ⋃ F : {F : Finset (countableBasis X) // (⋃ b ∈ F, (b : Set X)) ⊆ G},
      ⋃ b ∈ F.1, (b : Set X) = G := by
    refine subset_antisymm (iUnion_subset fun F => F.2) fun z hz => ?_
    obtain ⟨v, hv, hzv, hvG⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hz hG
    have hs : ⋃ b ∈ ({⟨v, hv⟩} : Finset (countableBasis X)), (b : Set X) = v := by
      simp only [Finset.set_biUnion_singleton]
    exact mem_iUnion.2 ⟨⟨{(⟨v, hv⟩ : countableBasis X)}, by rw [hs]; exact hvG⟩,
      by rw [hs]; exact hzv⟩
  rw [← hdir.measure_iUnion, hunion]

end MeasureTheory

namespace ProbabilityTheory

open MeasureTheory

/-- **Varadarajan's theorem.**  The empirical measures `(n + 1)⁻¹ ∑_{i ≤ n} δ_{x i}` of an i.i.d.
sequence with law `ν` on a second countable metrizable space converge weakly to `ν` almost
surely. -/
theorem ae_tendsto_empiricalMeasure [MetrizableSpace X] [SecondCountableTopology X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (empiricalMeasure fun i : Fin (n + 1) => x i).toProbabilityMeasure)
        atTop (𝓝 ν.toProbabilityMeasure) := by
  -- finite unions of the basic open sets
  set U : Finset (countableBasis X) → Set X := fun F => ⋃ b ∈ F, (b : Set X) with hU
  have hUo : ∀ F, IsOpen (U F) := fun F =>
    isOpen_biUnion fun b _ => isOpen_of_mem_countableBasis b.2
  -- the strong law for the indicators of all of them
  have hall : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν), ∀ F : Finset (countableBasis X),
      Tendsto (fun n : ℕ => (empiricalMeasure fun i : Fin (n + 1) => x i) (U F)) atTop
        (𝓝 (ν (U F))) := by
    have : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
    rw [ae_all_iff]
    intro F
    have hm : MeasurableSet (U F) := (hUo F).measurableSet
    filter_upwards [ae_tendsto_mean_infinitePi ν (g := (U F).indicator (1 : X → ℝ))
      (measurable_one.indicator hm) (integrable_indicator_iff hm |>.2
        (integrableOn_const (measure_ne_top _ _)))] with x hx
    have hx' := (tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i ∈ range n, (U F).indicator (1 : X → ℝ) (x i)) 1).2 hx
    rw [integral_indicator_one hm] at hx'
    have hE : ∀ n : ℕ, ((empiricalMeasure fun i : Fin (n + 1) => x i) (U F)).toReal =
        ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ range (n + 1), (U F).indicator (1 : X → ℝ) (x i) := by
      intro n
      rw [empiricalMeasure_apply_toReal _ hm,
        Fin.sum_univ_eq_sum_range (fun i => (U F).indicator (1 : X → ℝ) (x i)) (n + 1)]
      simp
    refine (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
    simpa only [hE, Measure.real] using hx'
  filter_upwards [hall] with x hx
  refine tendsto_of_forall_isOpen_le_liminf' fun G hG => ?_
  change ν G ≤ atTop.liminf fun n => (empiricalMeasure fun i : Fin (n + 1) => x i) G
  have : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  rw [measure_isOpen_eq_iSup_finset_biUnion ν hG]
  refine iSup_le fun F => ?_
  calc ν (U F.1) = atTop.liminf fun n => (empiricalMeasure fun i : Fin (n + 1) => x i) (U F.1) :=
        (hx F.1).liminf_eq.symm
    _ ≤ atTop.liminf fun n => (empiricalMeasure fun i : Fin (n + 1) => x i) G :=
        liminf_le_liminf (Eventually.of_forall fun n => measure_mono F.2)

/-- **An i.i.d. sample is dense in the support of its law:** almost surely, every point of the
support of `ν` is a cluster point of the sequence, i.e. is approached by infinitely many terms. -/
theorem ae_forall_mapClusterPt_of_mem_support [MetrizableSpace X] [SecondCountableTopology X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν), ∀ p ∈ ν.support, MapClusterPt p atTop x := by
  filter_upwards [ae_tendsto_empiricalMeasure ν] with x hx p hp
  exact mapClusterPt_of_tendsto_empiricalMeasure hx hp

end ProbabilityTheory
