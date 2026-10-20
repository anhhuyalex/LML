/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Ring

/-!
# Weighted sums against a probability vector on a finite type

A probability vector `w : α → ℝ` (`w ≥ 0`, `∑ w = 1`) on a finite type `α` defines the average
`∑ₐ wₐ fₐ`.  This file collects the elementary facts about such averages used for finite Gibbs
states: Jensen's inequality, the average of a constant or centred function, the square of an
average as a double sum over two independent replicas, and the triangle inequality.

## Main declarations

* `Weights.sq_sum_mul_le_sum_mul_sq`: Jensen, `(∑ₐ wₐ fₐ)² ≤ ∑ₐ wₐ fₐ²`.
* `Weights.sq_sum_mul_eq`: `(∑ₐ wₐ fₐ)² = ∑ₐ ∑ᵦ wₐ wᵦ fₐ fᵦ`.
* `Weights.sum_sum_mul_centered`: two replicas of a centred function average to zero.
* `Weights.abs_sum_mul_le`, `Weights.abs_sum_mul_le_sum_mul_abs`, `Weights.abs_sum_sum_mul_le`:
  absolute values of averages.
-/

@[expose] public section

open Finset

namespace Weights

variable {α : Type*} [Fintype α]

/-- **Jensen for a probability vector:** `(∑ₐ wₐ fₐ)² ≤ ∑ₐ wₐ fₐ²` when `w ≥ 0` and `∑ w = 1`. -/
theorem sq_sum_mul_le_sum_mul_sq {w f : α → ℝ} (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) :
    (∑ a, w a * f a) ^ 2 ≤ ∑ a, w a * f a ^ 2 := by
  have := (Even.convexOn_pow (𝕜 := ℝ) even_two).map_sum_le (t := Finset.univ) (w := w)
    (p := f) (fun i _ => hw i) hw1 (fun _ _ => Set.mem_univ _)
  simpa [smul_eq_mul] using this

/-- A probability vector averages a constant to the constant. -/
theorem sum_mul_const_of_sum_eq_one {w : α → ℝ} (hw1 : ∑ a, w a = 1) (c : ℝ) :
    ∑ a, w a * c = c := by
  rw [← Finset.sum_mul, hw1, one_mul]

/-- The square of a weighted sum is the double weighted sum of the product. -/
theorem sq_sum_mul_eq (w f : α → ℝ) :
    (∑ a, w a * f a) ^ 2 = ∑ a, ∑ b, w a * w b * (f a * f b) := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- A centred function has zero Gibbs average. -/
theorem sum_mul_sub_avg {w : α → ℝ} (hw1 : ∑ a, w a = 1) (f : α → ℝ) :
    ∑ a, w a * (f a - ∑ b, w b * f b) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, sub_self]

/-- Two independent replicas of a centred function average to zero. -/
theorem sum_sum_mul_centered {w : α → ℝ} (hw1 : ∑ a, w a = 1) (f : α → ℝ) :
    ∑ a, ∑ b, w a * w b * ((f a - ∑ c, w c * f c) * (f b - ∑ c, w c * f c)) = 0 := by
  rw [← sq_sum_mul_eq, sum_mul_sub_avg hw1, zero_pow two_ne_zero]

/-- A probability vector averages a function bounded by `M` to a number bounded by `M`. -/
theorem abs_sum_mul_le {w f : α → ℝ} (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) {M : ℝ}
    (hf : ∀ a, |f a| ≤ M) : |∑ a, w a * f a| ≤ M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ a, |w a * f a| ≤ ∑ a, w a * M := Finset.sum_le_sum fun a _ => by
        rw [abs_mul, abs_of_nonneg (hw a)]
        exact mul_le_mul_of_nonneg_left (hf a) (hw a)
    _ = M := sum_mul_const_of_sum_eq_one hw1 M

/-- A weighted average of `c` is at most the weighted average of `|c|` in absolute value. -/
theorem abs_sum_mul_le_sum_mul_abs {w c : α → ℝ} (hw : ∀ a, 0 ≤ w a) :
    |∑ a, w a * c a| ≤ ∑ a, w a * |c a| :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => by
    rw [abs_mul, abs_of_nonneg (hw a)])

/-- The same for a weighted average over two independent replicas. -/
theorem abs_sum_sum_mul_le {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (c : α → α → ℝ) :
    |∑ a, ∑ a', w a * w a' * c a a'| ≤ ∑ a, ∑ a', w a * w a' * |c a a'| :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a' _ => by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hw a) (hw a'))]))

end Weights
