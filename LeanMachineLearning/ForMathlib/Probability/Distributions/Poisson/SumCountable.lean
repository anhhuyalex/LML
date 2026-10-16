/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.TsumNonneg

/-!
# Sums of Poisson random variables

This file extends the binary Poisson convolution theorem in Mathlib to finite independent
families. It is the finite-partial-sum engine for countable Poisson sums.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma summable_poisson_nat (r : ℝ≥0) :
    Summable fun n : ℕ => (rexp (-(r : ℝ)) * (r : ℝ) ^ n / (n)!) * n := by
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  apply (summable_nat_add_iff 1).mp
  convert h.summable using 1
  ext n
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The mean of a Poisson random variable with rate `r` is `r`. -/
theorem integral_natCast_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂Po(r) = r := by
  rw [integral_poissonMeasure]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have h' : HasSum
      (fun n : ℕ => (rexp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1)!) * (n + 1))
      (r : ℝ) := by
    convert h using 1
    · ext n
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · ring
  calc
    ∑' n : ℕ, (rexp (-(r : ℝ)) * (r : ℝ) ^ n / (n)!) • (n : ℝ) =
        ∑' n : ℕ, (rexp (-(r : ℝ)) * (r : ℝ) ^ n / (n)!) * n := by
          congr 1
    _ = 0 + ∑' n : ℕ,
        (rexp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1)!) * (n + 1) := by
          simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, add_zero, Nat.cast_add,
            Nat.cast_one] using ((summable_poisson_nat r).sum_add_tsum_nat_add 1).symm
    _ = r := by simp [h'.tsum_eq]

/-- The natural-number embedding is integrable under every Poisson law. -/
theorem integrable_natCast_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) Po(r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_natCast] using summable_poisson_nat r

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

/-- A finite sum of mutually independent Poisson random variables is Poisson, with rate equal
to the sum of the rates. -/
theorem iIndepFun.hasLaw_sum_poissonMeasure {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) Po(r i) P) (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω) Po(∑ i ∈ s, r i) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
      refine ⟨by fun_prop, ?_⟩
      apply Measure.ext_of_singleton
      intro n
      rcases n with _ | n
      · simp [Measure.map_const, poissonMeasure_singleton]
      · simp [Measure.map_const, poissonMeasure_singleton, zero_pow]
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

/-- The sum of a finite mutually independent family of Poisson random variables is Poisson. -/
theorem iIndepFun.hasLaw_fun_sum_poissonMeasure [Fintype ι] {X : ι → Ω → ℕ}
    {r : ι → ℝ≥0} (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) Po(r i) P) :
    HasLaw (fun ω => ∑ i, X i ω) Po(∑ i, r i) P := by
  simpa using hX.hasLaw_sum_poissonMeasure hLaw Finset.univ

end ProbabilityTheory
