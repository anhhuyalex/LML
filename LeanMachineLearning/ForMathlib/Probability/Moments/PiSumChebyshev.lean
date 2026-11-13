/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Chebyshev's inequality for a weighted sum over a finite product measure

For an independent family `a j ~ ν` and centered `ℒ²` observables `g j`, the sum `∑ⱼ g j (a j)` has
variance `∑ⱼ Var[g j; ν]`, so Chebyshev bounds its scaled tail.

## Main declarations

* `ProbabilityTheory.measure_pi_ge_abs_mul_sum_le`: the Chebyshev bound
  `ν^ι {ε ≤ |c ∑ⱼ g j (a j)|} ≤ c² (∑ⱼ Var[g j; ν]) / ε²`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- **Chebyshev's inequality for a sum of independent centered `ℒ²` observables.**  If
`a ~ ν^ι` and each `g j ∈ ℒ²(ν)` has mean zero, then
`ν^ι {a | ε ≤ |c ∑ⱼ g j (a j)|} ≤ c² (∑ⱼ Var[g j; ν]) / ε²`. -/
theorem measure_pi_ge_abs_mul_sum_le {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (g : ι → Ω → ℝ) (hg : ∀ j, MemLp (g j) 2 ν)
    (hmean : ∀ j, ∫ x, g j x ∂ν = 0) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : ι => ν) {a | ε ≤ |c * ∑ j, g j (a j)|} ≤
      ENNReal.ofReal (c ^ 2 * (∑ j, Var[g j; ν]) / ε ^ 2) := by
  classical
  let μ : Measure (ι → Ω) := Measure.pi fun _ : ι => ν
  let S : (ι → Ω) → ℝ := ∑ j, fun a => g j (a j)
  have hcomp (j : ι) : MemLp (fun a : ι → Ω => g j (a j)) 2 μ :=
    (hg j).comp_measurePreserving (measurePreserving_eval (fun _ : ι => ν) j)
  have hS_mem : MemLp S 2 μ := memLp_finsetSum' _ fun j _ => hcomp j
  have hX_mem : MemLp (fun a => c * S a) 2 μ := hS_mem.const_mul _
  have hS_fun : S = fun a => ∑ j, g j (a j) := by funext a; simp [S, Finset.sum_apply]
  have hmean_S : μ[S] = 0 := by
    rw [hS_fun, integral_finsetSum _ fun j _ => (hcomp j).integrable (by norm_num)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show (∫ a, g j (a j) ∂μ) = ∫ x, g j x ∂ν from
      integral_comp_eval (μ := fun _ : ι => ν) (hg j).aestronglyMeasurable]
    exact hmean j
  have hvarS : Var[S; μ] = ∑ j, Var[g j; ν] := by
    simpa [S] using variance_sum_pi (μ := fun _ : ι => ν) hg
  have hcheb := meas_ge_le_variance_div_sq hX_mem hε
  rw [integral_const_mul, hmean_S, mul_zero, variance_const_mul, hvarS] at hcheb
  simpa [S, hS_fun] using hcheb
