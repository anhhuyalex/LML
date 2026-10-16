/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Probability.Distributions.Poisson.Basic
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.TsumNonneg

/-!
# Sums of Poisson random variables

This file extends the binary Poisson convolution theorem in Mathlib to finite independent
families. It is the finite-partial-sum engine for countable Poisson sums.
-/

@[expose] public section

open MeasureTheory Real Filter Topology
open scoped NNReal ENNReal Nat

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The series `∑ n, n * Po(r){n}` converges to the mean `r`. -/
theorem hasSum_natCast_poissonMeasure (r : ℝ≥0) :
    HasSum (fun n : ℕ => (rexp (-(r : ℝ)) * (r : ℝ) ^ n / (n)!) * n) (r : ℝ) := by
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  refine (hasSum_nat_add_iff' 1).1 ?_
  convert h using 1
  · ext n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · simp

/-- The mean of a Poisson random variable with rate `r` is `r`. -/
theorem integral_natCast_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂Po(r) = r := by
  rw [integral_poissonMeasure]
  exact (hasSum_natCast_poissonMeasure r).tsum_eq

/-- The natural-number embedding is integrable under every Poisson law. -/
theorem integrable_natCast_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) Po(r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_natCast] using (hasSum_natCast_poissonMeasure r).summable

/-- The mean of a Poisson law with rate `r`, as an extended nonnegative integral. -/
theorem lintegral_natCast_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂Po(r) = r := by
  change ∫⁻ n : ℕ, ((n : ℝ≥0) : ℝ≥0∞) ∂Po(r) = _
  rw [lintegral_coe_eq_integral _ (by simpa using integrable_natCast_poissonMeasure r)]
  rw [show (∫ n : ℕ, ((n : ℝ≥0) : ℝ) ∂Po(r)) = ∫ n : ℕ, (n : ℝ) ∂Po(r) from rfl,
    integral_natCast_poissonMeasure]
  simp

/-- On a countable discrete space, the measure of a finite set is the sum of its
singleton masses. -/
theorem measure_finset_eq_sum_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) (s : Finset α) :
    μ (s : Set α) = ∑ a ∈ s, μ {a} := by
  rw [show (s : Set α) = ⋃ a ∈ s, ({a} : Set α) by ext a; simp]
  exact measure_biUnion_finset
    (fun a ha b hb hab => Set.disjoint_singleton.2 hab)
    (fun _ _ => MeasurableSet.singleton _)

/-- The cumulative mass of a natural-number-valued measure is the finite sum of its
singleton masses. -/
theorem measure_Iic_eq_sum_singleton (μ : Measure ℕ) (k : ℕ) :
    μ (Set.Iic k) = ∑ n ∈ Finset.range (k + 1), μ {n} := by
  rw [← measure_finset_eq_sum_singleton]
  congr
  ext n
  simp

/-- A countable family of Poisson variables with summable rates is almost surely summable.
Independence is not needed for this conclusion. -/
theorem ae_summable_natCast_of_hasLaw_poissonMeasure [Countable ι] {X : ι → Ω → ℕ}
    {r : ι → ℝ≥0} (hLaw : ∀ i, HasLaw (X i) Po(r i) P) (hr : Summable r) :
    ∀ᵐ ω ∂P, Summable fun i => (X i ω : ℝ) := by
  have hcast : Measurable fun n : ℕ => (n : ℝ) := measurable_of_countable _
  have hm : ∀ i, AEMeasurable (fun ω => (X i ω : ℝ)) P := fun i =>
    hcast.comp_aemeasurable (hLaw i).aemeasurable
  have hint : ∀ i, Integrable (fun ω => (X i ω : ℝ)) P := fun i =>
    (hLaw i).integrable_comp (integrable_natCast_poissonMeasure (r i))
  have hmean : ∀ i, ∫ ω, (X i ω : ℝ) ∂P = r i := fun i => by
    calc
      ∫ ω, (X i ω : ℝ) ∂P = ∫ n, (n : ℝ) ∂Po(r i) :=
        (hLaw i).integral_comp hcast.aestronglyMeasurable
      _ = r i := integral_natCast_poissonMeasure (r i)
  refine (ae_summable_and_integrable_tsum_of_nonneg hm (fun _ _ => Nat.cast_nonneg _) hint ?_).1
  rw [show (fun i => ∫ ω, (X i ω : ℝ) ∂P) = fun i => (r i : ℝ) by ext i; exact hmean i]
  exact_mod_cast hr

/-- A natural-number series that is summable in `ℝ` is summable in `ℕ`: its terms eventually
vanish. -/
theorem summable_of_summable_natCast {f : ℕ → ℕ} (hf : Summable fun i => (f i : ℝ)) :
    Summable f := by
  have hlim := hf.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim 1 zero_lt_one
  have hzero : ∀ i ≥ N, f i = 0 := by
    intro i hi
    have hlt : (f i : ℝ) < 1 := by simpa [Real.dist_eq] using hN i hi
    by_contra hne
    exact (not_lt_of_ge (show (1 : ℝ) ≤ f i by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hne)) hlt
  apply summable_of_hasFiniteSupport
  exact Set.Finite.subset (Set.finite_Iio N) fun i hi => by
    by_contra hnot
    exact hi (hzero i (Nat.le_of_not_gt hnot))

/-- A natural-number series is bounded by `k` exactly when all its partial sums are. -/
private lemma tsum_le_iff_forall_sum_range_le {f : ℕ → ℕ} (hf : Summable fun i => (f i : ℝ))
    (k : ℕ) : (∑' i, f i) ≤ k ↔ ∀ n, (∑ i ∈ Finset.range n, f i) ≤ k := by
  have hfs := summable_of_summable_natCast hf
  constructor
  · intro hk n
    exact (hfs.sum_le_tsum (Finset.range n) fun _ _ => Nat.zero_le _).trans hk
  · intro hk
    exact le_of_tendsto hfs.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hk)

/-- The Poisson law of rate zero is the point mass at zero. -/
theorem poissonMeasure_zero : Po(0) = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n => ?_
  rcases n with _ | n <;> simp [poissonMeasure_singleton, zero_pow]

/-- A Poisson random variable of rate zero is almost surely zero. -/
theorem HasLaw.ae_eq_zero_of_poisson_zero [IsProbabilityMeasure P] {X : Ω → ℕ}
    (hX : HasLaw X Po(0) P) : ∀ᵐ ω ∂P, X ω = 0 := by
  have hd : HasLaw X (Measure.dirac 0) P := by rwa [poissonMeasure_zero] at hX
  exact hasLaw_dirac_iff.mp hd

/-- A finite sum of mutually independent Poisson random variables is Poisson, with rate equal
to the sum of the rates. -/
theorem iIndepFun.hasLaw_sum_poissonMeasure {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) Po(r i) P) (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω) Po(∑ i ∈ s, r i) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
      simpa only [Finset.sum_empty, poissonMeasure_zero] using
        hasLaw_dirac_of_ae_eq (P := P) (X := fun _ : Ω => 0) (x := 0) (Filter.EventuallyEq.refl _ _)
  | @insert i s hi hs =>
      have hsum : HasLaw (fun ω => ∑ j ∈ s, X j ω) Po(∑ j ∈ s, r j) P := hs
      have hindep : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) P := by
        convert (hX.indepFun_finsetSum_of_notMem₀
          (fun j => (hLaw j).aemeasurable) hi).symm using 1
        ext ω
        simp [Finset.sum_apply]
      have hadd := hindep.hasLaw_add_poissonMeasure (hLaw i) hsum
      rw [Finset.sum_insert hi]
      exact hadd.congr (ae_of_all P fun ω => by
        change (∑ j ∈ insert i s, X j ω) = X i ω + ∑ j ∈ s, X j ω
        rw [Finset.sum_insert hi])

/-- The cumulative law of a finite partial sum of independent Poisson variables. -/
theorem iIndepFun.measure_sum_range_le_eq {X : ℕ → Ω → ℕ} {r : ℕ → ℝ≥0}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) Po(r i) P) (n k : ℕ) :
    P {ω | (∑ i ∈ Finset.range n, X i ω) ≤ k} =
      ∑ j ∈ Finset.range (k + 1), Po(∑ i ∈ Finset.range n, r i) {j} :=
  ((hX.hasLaw_sum_poissonMeasure hLaw (Finset.range n)).measure_eq
    (p := fun x => x ∈ Set.Iic k) measurableSet_Iic).trans (measure_Iic_eq_sum_singleton _ _)

/-- The sum of countably many independent Poisson variables with summable rates is Poisson. -/
theorem iIndepFun.hasLaw_tsum_poissonMeasure {X : ℕ → Ω → ℕ} {r : ℕ → ℝ≥0}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) Po(r i) P) (hr : Summable r) :
    HasLaw (fun ω => ∑' i, X i ω) Po(∑' i, r i) P := by
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hsummable := ae_summable_natCast_of_hasLaw_poissonMeasure hLaw hr
  have hpartial (n : ℕ) := hX.hasLaw_sum_poissonMeasure hLaw (Finset.range n)
  have hrates : Tendsto (fun n => ∑ i ∈ Finset.range n, r i) atTop (𝓝 (∑' i, r i)) :=
    NNReal.hasSum_iff_tendsto_nat.1 hr.hasSum
  refine ⟨AEMeasurable.tsum fun i => (hLaw i).aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro k
  rw [Measure.map_apply_of_aemeasurable
    (AEMeasurable.tsum fun i => (hLaw i).aemeasurable) measurableSet_Iic]
  change P {ω | ∑' i, X i ω ∈ Set.Iic k} = _
  have hset : {ω | ∑' i, X i ω ∈ Set.Iic k} =ᵐ[P]
      ⋂ n, {ω | ∑ i ∈ Finset.range n, X i ω ∈ Set.Iic k} := by
    filter_upwards [hsummable] with ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_Iic, Set.mem_iInter]
    apply propext
    exact tsum_le_iff_forall_sum_range_le hω k
  rw [measure_congr hset]
  have hanti : Antitone fun n => {ω | ∑ i ∈ Finset.range n, X i ω ∈ Set.Iic k} := by
    intro a b hab ω hω
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun _ _ _ => Nat.zero_le _)).trans hω
  apply tendsto_nhds_unique (tendsto_measure_iInter_atTop
    (fun n => (hpartial n).aemeasurable.nullMeasurableSet_preimage measurableSet_Iic)
    hanti ⟨0, measure_ne_top P _⟩)
  have heq (n : ℕ) :
      P {ω | ∑ i ∈ Finset.range n, X i ω ∈ Set.Iic k} =
        ∑ j ∈ Finset.range (k + 1), Po(∑ i ∈ Finset.range n, r i) {j} :=
    hX.measure_sum_range_le_eq hLaw n k
  change Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, X i ω ∈ Set.Iic k}) atTop _
  rw [show (fun n => P {ω | ∑ i ∈ Finset.range n, X i ω ∈ Set.Iic k}) =
    fun n => ∑ j ∈ Finset.range (k + 1), Po(∑ i ∈ Finset.range n, r i) {j} by
      funext n
      exact heq n]
  rw [measure_Iic_eq_sum_singleton]
  apply tendsto_finsetSum (Finset.range (k + 1))
  intro i hi
  simp only [poissonMeasure_singleton]
  convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((Real.continuous_exp.comp continuous_neg).mul
      ((continuous_id.pow i).div_const (i.factorial : ℝ))).continuousAt.tendsto.comp
      ((NNReal.continuous_coe.tendsto _).comp hrates)) using 1
  · funext n
    simp [mul_div_assoc]
  · simp [mul_div_assoc]

/-- If the sum of the rates diverges, the finite partial sums of independent Poisson
variables tend to infinity almost surely. This is the appropriate formulation because a
natural-number-valued `tsum` cannot represent infinity. -/
theorem iIndepFun.ae_tendsto_sum_range_poissonMeasure_atTop {X : ℕ → Ω → ℕ}
    {r : ℕ → ℝ≥0} (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) Po(r i) P)
    (hr : ¬ Summable r) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ Finset.range n, X i ω) atTop atTop := by
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hpartial (n : ℕ) := hX.hasLaw_sum_poissonMeasure hLaw (Finset.range n)
  have hrates : Tendsto (fun n => ∑ i ∈ Finset.range n, (r i : ℝ)) atTop atTop :=
    not_summable_iff_tendsto_nat_atTop_of_nonneg (fun i => NNReal.zero_le_coe) |>.1
      (by exact_mod_cast hr)
  have hnull (k : ℕ) : P {ω | ∀ n, (∑ i ∈ Finset.range n, X i ω) ≤ k} = 0 := by
    have hanti : Antitone fun n => {ω | (∑ i ∈ Finset.range n, X i ω) ≤ k} := by
      intro a b hab ω hω
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
        (fun _ _ _ => Nat.zero_le _)).trans hω
    rw [show {ω | ∀ n, (∑ i ∈ Finset.range n, X i ω) ≤ k} =
      ⋂ n, {ω | (∑ i ∈ Finset.range n, X i ω) ≤ k} by ext; simp]
    apply tendsto_nhds_unique (tendsto_measure_iInter_atTop
      (fun n => (hpartial n).aemeasurable.nullMeasurableSet_preimage measurableSet_Iic)
      hanti ⟨0, measure_ne_top P _⟩)
    change Tendsto (fun n => P {ω | (∑ i ∈ Finset.range n, X i ω) ≤ k}) atTop (𝓝 0)
    have heq (n : ℕ) := hX.measure_sum_range_le_eq hLaw n k
    rw [show (fun n => P {ω | (∑ i ∈ Finset.range n, X i ω) ≤ k}) =
      fun n => ∑ j ∈ Finset.range (k + 1), Po(∑ i ∈ Finset.range n, r i) {j} by
        funext n
        exact heq n]
    have hj (j : ℕ) : Tendsto
        (fun n => Po(∑ i ∈ Finset.range n, r i) {j}) atTop (𝓝 0) := by
      simp only [poissonMeasure_singleton]
      have hreal := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero j).const_mul
        ((j.factorial : ℝ)⁻¹)).comp (by simpa only [NNReal.coe_sum] using hrates)
      have henn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
      convert henn using 1
      · funext n
        simp only [Function.comp_apply, NNReal.coe_sum, div_eq_mul_inv]
        congr 1
        ring
      · simp
    simpa using tendsto_finsetSum (Finset.range (k + 1)) (fun j _ => hj j)
  have hbad : P {ω | ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, X i ω)
      atTop atTop} = 0 := by
    apply measure_mono_null _ (measure_iUnion_null hnull)
    intro ω hω
    change ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, X i ω) atTop atTop at hω
    rw [tendsto_atTop_atTop] at hω
    simp only [not_forall, not_exists, not_le] at hω
    obtain ⟨k, hk⟩ := hω
    exact Set.mem_iUnion.2 ⟨k, fun n => by
      obtain ⟨m, hnm, hm⟩ := hk n
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
        (fun _ _ _ => Nat.zero_le _)).trans (Nat.le_of_lt hm)⟩
  filter_upwards [ae_iff.2 hbad] with ω hω
  exact hω

/-- The sum of a finite mutually independent family of Poisson random variables is Poisson. -/
theorem iIndepFun.hasLaw_fun_sum_poissonMeasure [Fintype ι] {X : ι → Ω → ℕ}
    {r : ι → ℝ≥0} (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) Po(r i) P) :
    HasLaw (fun ω => ∑ i, X i ω) Po(∑ i, r i) P := by
  simpa using hX.hasLaw_sum_poissonMeasure hLaw Finset.univ

end ProbabilityTheory
