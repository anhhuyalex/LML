/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Chebyshev's inequality for a weighted sum over a finite product measure

For an independent family `a j ~ ν` and centered `ℒ²` observables `g j`, the sum `∑ⱼ g j (a j)` has
variance `∑ⱼ Var[g j; ν]`, so Chebyshev bounds its scaled tail.

## Main declarations

* `ProbabilityTheory.measure_ge_abs_mul_sum_le_of_pairwise_covariance_eq_zero`: the bound for any
  pairwise uncorrelated centered observables.
* `ProbabilityTheory.measure_pi_ge_abs_mul_sum_le`: the Chebyshev bound
  `ν^ι {ε ≤ |c ∑ⱼ g j (a j)|} ≤ c² (∑ⱼ Var[g j; ν]) / ε²`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- **Chebyshev's inequality for a sum of pairwise uncorrelated centered `ℒ²` observables:**
`μ {ε ≤ |c ∑ⱼ g j|} ≤ c² (∑ⱼ Var[g j; μ]) / ε²`. -/
theorem measure_ge_abs_mul_sum_le_of_pairwise_covariance_eq_zero {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {g : ι → Ω → ℝ}
    (hg : ∀ j, MemLp (g j) 2 μ) (hmean : ∀ j, ∫ x, g j x ∂μ = 0)
    (hcov : Pairwise fun i j => cov[g i, g j; μ] = 0) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ {a | ε ≤ |c * ∑ j, g j a|} ≤ ENNReal.ofReal (c ^ 2 * (∑ j, Var[g j; μ]) / ε ^ 2) := by
  classical
  have hX : MemLp (fun a => c * ∑ j, g j a) 2 μ :=
    (memLp_finsetSum _ fun j _ => hg j).const_mul _
  have hmean_S : ∫ a, ∑ j, g j a ∂μ = 0 := by
    rw [integral_finsetSum _ fun j _ => (hg j).integrable one_le_two]
    exact Finset.sum_eq_zero fun j _ => hmean j
  have hvar : Var[fun a => ∑ j, g j a; μ] = ∑ j, Var[g j; μ] := by
    rw [variance_fun_sum fun j => hg j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => hcov hji.symm) (by simp),
      covariance_self (hg i).aemeasurable]
  have hcheb := meas_ge_le_variance_div_sq hX hε
  rw [integral_const_mul, hmean_S, mul_zero, variance_const_mul, hvar] at hcheb
  simpa only [sub_zero] using hcheb

/-- **Chebyshev's inequality for a sum of independent centered `ℒ²` observables.**  If
`a ~ ν^ι` and each `g j ∈ ℒ²(ν)` has mean zero, then
`ν^ι {a | ε ≤ |c ∑ⱼ g j (a j)|} ≤ c² (∑ⱼ Var[g j; ν]) / ε²`. -/
theorem measure_pi_ge_abs_mul_sum_le {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (g : ι → Ω → ℝ) (hg : ∀ j, MemLp (g j) 2 ν)
    (hmean : ∀ j, ∫ x, g j x ∂ν = 0) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : ι => ν) {a | ε ≤ |c * ∑ j, g j (a j)|} ≤
      ENNReal.ofReal (c ^ 2 * (∑ j, Var[g j; ν]) / ε ^ 2) := by
  have hcomp (j : ι) : MemLp (fun a : ι → Ω => g j (a j)) 2 (Measure.pi fun _ : ι => ν) :=
    (hg j).comp_measurePreserving (measurePreserving_eval (fun _ : ι => ν) j)
  have hind : iIndepFun (fun j (a : ι → Ω) => g j (a j)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi fun j => (hg j).aemeasurable
  have hmean' : ∀ j, ∫ a, g j (a j) ∂(Measure.pi fun _ : ι => ν) = 0 := fun j =>
    (integral_comp_eval (μ := fun _ : ι => ν) (i := j) (hg j).aestronglyMeasurable).trans
      (hmean j)
  have h := measure_ge_abs_mul_sum_le_of_pairwise_covariance_eq_zero
    (g := fun j (a : ι → Ω) => g j (a j)) hcomp hmean'
    (fun i j hij => (hind.indepFun hij).covariance_eq_zero (hcomp i) (hcomp j)) c hε
  have hvar : ∀ j, Var[fun a : ι → Ω => g j (a j); Measure.pi fun _ : ι => ν] = Var[g j; ν] :=
    fun j => (measurePreserving_eval (fun _ : ι => ν) j).variance_fun_comp (hg j).aemeasurable
  simpa only [hvar] using h

end ProbabilityTheory
