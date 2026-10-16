/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Sums of Poisson random variables

This file extends the binary Poisson convolution theorem in Mathlib to finite independent
families. It is the finite-partial-sum engine for countable Poisson sums.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

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
