/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-!
# Bounds on dot products

* `abs_dotProduct_le_mul_sum_abs`: `|x ⬝ᵥ y| ≤ M ∑ᵢ |yᵢ|` when every `|xᵢ| ≤ M`.
* `two_mul_abs_dotProduct_le`: `2 |x ⬝ᵥ y| ≤ x ⬝ᵥ x + y ⬝ᵥ y`.
* `abs_dotProduct_le_of_self_le`: if two vectors have squared Euclidean length at most `B`, their
  dot product lies in `[-B, B]`. This is the polarization form of Cauchy–Schwarz that needs no
  square roots.
-/

@[expose] public section

open scoped Matrix

variable {ι R : Type*} [Fintype ι]

/-- A dot product is at most a uniform bound on one factor times the `ℓ¹` size of the other. -/
theorem abs_dotProduct_le_mul_sum_abs [Ring R] [LinearOrder R] [IsOrderedRing R] {x : ι → R}
    {M : R} (hx : ∀ i, |x i| ≤ M) (y : ι → R) : |x ⬝ᵥ y| ≤ M * ∑ i, |y i| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `2 |x ⬝ᵥ y| ≤ x ⬝ᵥ x + y ⬝ᵥ y` (polarization: `0 ≤ (x ± y) ⬝ᵥ (x ± y)`). -/
theorem two_mul_abs_dotProduct_le (x y : ι → R) : 2 * |x ⬝ᵥ y| ≤ x ⬝ᵥ x + y ⬝ᵥ y := by
  have h : ∀ z : ι → R, 0 ≤ z ⬝ᵥ z := fun z => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 := h (x + y)
  have h2 := h (x - y)
  simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    dotProduct_comm y x] at h1 h2
  rcases abs_cases (x ⬝ᵥ y) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> linarith

/-- The dot product of two vectors of squared length at most `B` has absolute value at
most `B`. -/
theorem abs_dotProduct_le_of_self_le {B : R} (x y : ι → R) (hx : x ⬝ᵥ x ≤ B)
    (hy : y ⬝ᵥ y ≤ B) : |x ⬝ᵥ y| ≤ B := by
  linarith [two_mul_abs_dotProduct_le x y]
