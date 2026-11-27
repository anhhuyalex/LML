/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-!
# Bounds on dot products

* `abs_dotProduct_le_mul_sum_abs`: `|x ⬝ᵥ y| ≤ M ∑ᵢ |yᵢ|` when every `|xᵢ| ≤ M`.
* `abs_dotProduct_le_of_self_le`: if two real vectors have squared Euclidean length at most `B`,
  their dot product lies in `[-B, B]`. This is the polarization form of Cauchy–Schwarz that needs
  no square roots.
-/

@[expose] public section

open scoped Matrix

/-- A dot product is at most a uniform bound on one factor times the `ℓ¹` size of the other. -/
theorem abs_dotProduct_le_mul_sum_abs {ι R : Type*} [Fintype ι] [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : ι → R} {M : R} (hx : ∀ i, |x i| ≤ M) (y : ι → R) :
    |x ⬝ᵥ y| ≤ M * ∑ i, |y i| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)

/-- The dot product of two real vectors of squared length at most `B` has absolute value at
most `B` (polarization: `0 ≤ (x ± y) ⬝ᵥ (x ± y)`). -/
theorem abs_dotProduct_le_of_self_le {ι : Type*} [Fintype ι] {B : ℝ} (x y : ι → ℝ)
    (hx : x ⬝ᵥ x ≤ B) (hy : y ⬝ᵥ y ≤ B) : |x ⬝ᵥ y| ≤ B := by
  have h1 : 0 ≤ (x + y) ⬝ᵥ (x + y) := dotProduct_self_star_nonneg _
  have h2 : 0 ≤ (x - y) ⬝ᵥ (x - y) := dotProduct_self_star_nonneg _
  simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    dotProduct_comm y x] at h1 h2
  rw [abs_le]
  constructor <;> linarith
