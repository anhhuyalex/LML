/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKDecoupled

/-!
# The replica-symmetric fixed-point equation of the SK model

For `β, h ∈ ℝ`, the replica-symmetric overlap `q` solves (Talagrand, Eq. (1.74))
$$q = \mathbb{E}\tanh^2(\beta z\sqrt{q} + h), \qquad z \sim \mathcal{N}(0, 1).$$
This module shows that the map `ψ(x) = 𝔼 tanh²(β z √x + h)` is continuous and takes values in
`[0, 1]`, so that the equation has a solution `q ∈ [0, 1]` (intermediate value theorem). The
uniqueness for `β < 1` (via `ψ' ≤ β²`) is not formalized here.

## Main declarations

* `SpinGlasses.continuous_fixedPointMap`: continuity of `ψ`.
* `SpinGlasses.exists_fixedPoint`: the existence of a fixed point `q ∈ [0, 1]`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.3, Eq. (1.74).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace SpinGlasses

/-- `ψ(x) = 𝔼 tanh²(β z √x + h)` is continuous in `x`. -/
theorem continuous_fixedPointMap (β h : ℝ) :
    Continuous fun x : ℝ =>
      ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun x => ?_) (fun x => ?_)
    (integrable_const _) (ae_of_all _ fun z => ?_)
  · exact ((Real.continuous_tanh.comp (by fun_prop : Continuous fun z : ℝ =>
      β * Real.sqrt x * z + h)).pow 2).aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (Real.tanh_sq_lt_one _).le
  · exact (Real.continuous_tanh.comp (by fun_prop : Continuous fun x : ℝ =>
      β * Real.sqrt x * z + h)).pow 2

/-- `0 ≤ ψ(x) ≤ 1`. -/
theorem fixedPointMap_mem_Icc (β h x : ℝ) :
    ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun z => sq_nonneg _, ?_⟩
  calc ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)
      ≤ ∫ z : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) := by
        exact integral_mono (integrable_tanh_sq _ (by fun_prop)) (integrable_const _)
          fun z => (Real.tanh_sq_lt_one _).le
    _ = 1 := by simp

/-- A fixed point `q = ψ(q)` lies in `[0, 1]`. -/
theorem fixedPoint_mem_Icc {β h q : ℝ}
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    q ∈ Icc (0 : ℝ) 1 :=
  hfix ▸ fixedPointMap_mem_Icc β h q

/-- A fixed point `q = ψ(q)` satisfies `|q| ≤ 1`. -/
theorem abs_fixedPoint_le_one {β h q : ℝ}
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    |q| ≤ 1 :=
  abs_le.2 ⟨by linarith [(fixedPoint_mem_Icc hfix).1], (fixedPoint_mem_Icc hfix).2⟩

/-- **Existence of the replica-symmetric overlap (Eq. 1.74):** there is `q ∈ [0, 1]` with
`q = 𝔼 tanh²(β z √q + h)`. -/
theorem exists_fixedPoint (β h : ℝ) :
    ∃ q ∈ Icc (0 : ℝ) 1,
      q = ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  set ψ : ℝ → ℝ := fun x => ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)
  have hcont : ContinuousOn (fun x => ψ x - x) (Icc 0 1) :=
    ((continuous_fixedPointMap β h).sub continuous_id).continuousOn
  have h0 : 0 ≤ ψ 0 - 0 := by rw [sub_zero]; exact (fixedPointMap_mem_Icc β h 0).1
  have h1 : ψ 1 - 1 ≤ 0 := by linarith [(fixedPointMap_mem_Icc β h 1).2]
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont ⟨h1, h0⟩
  exact ⟨q, hq, by simp only [ψ] at hq0; linarith⟩

end SpinGlasses
