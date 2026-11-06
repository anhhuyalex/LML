/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Entries of a sandwiched matrix `M Γ Mᵀ`

The entries of `M Γ Mᵀ` are the bilinear forms `Γ` evaluated on the rows of `M`. This is the
row-wise form of the covariance propagation rule `Cov (M x) = M Cov (x) Mᵀ`. For a Gram matrix
`B = K Kᵀ`, Cauchy–Schwarz bounds the squared Frobenius norm by the squared trace.
-/

@[expose] public section

open Matrix

namespace Matrix

variable {p n R : Type*} [Fintype n] [CommSemiring R]

/-- **Entries of `M Γ Mᵀ`.** `(M Γ Mᵀ)ⱼₖ = Mⱼ ⬝ (Γ Mₖ)`, where `Mⱼ` is the `j`-th row of `M`. -/
theorem mul_mul_transpose_apply (M : Matrix p n R) (Γ : Matrix n n R) (j k : p) :
    (M * Γ * Mᵀ) j k = M j ⬝ᵥ (Γ *ᵥ M k) := by
  simp only [Matrix.mul_apply, mulVec, dotProduct, transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact mul_assoc _ _ _


/-- The squared Frobenius norm of a cross-Gram matrix is bounded by the product of the
total squared norms of its two families. The families may have different index types. -/
theorem sum_sq_mul_transpose_le_sum_sq_mul_sum_sq {p q n : Type*}
    [Fintype p] [Fintype q] [Fintype n] (A : Matrix p n ℝ) (B : Matrix q n ℝ) :
    ∑ i, ∑ j, ((A * Bᵀ) i j) ^ 2 ≤
      (∑ i, ∑ k, A i k ^ 2) * ∑ j, ∑ k, B j k ^ 2 := by
  calc
    _ ≤ ∑ i, ∑ j, (∑ k, A i k ^ 2) * ∑ k, B j k ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (B j)
    _ = _ := by rw [Finset.sum_mul_sum]

/-- Cauchy--Schwarz for contraction of a matrix against a rank-one tensor.
This form separates the two vector radii from the matrix's squared Frobenius norm. -/
theorem sq_sum_mul_mul_le {p q : Type*} [Fintype p] [Fintype q]
    (x : p → ℝ) (y : q → ℝ) (A : Matrix p q ℝ) :
    (∑ i, ∑ j, x i * y j * A i j) ^ 2 ≤
      (∑ i, x i ^ 2) * (∑ j, y j ^ 2) * ∑ i, ∑ j, A i j ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (p × q))
    (fun ij => x ij.1 * y ij.2) (fun ij => A ij.1 ij.2)
  simp only [Fintype.sum_prod_type, mul_pow] at hcs
  simpa only [Finset.sum_mul_sum] using hcs

/-- **A Gram matrix has Frobenius norm at most its trace.** For `B = K Kᵀ`,
`∑ᵢⱼ Bᵢⱼ² ≤ (tr B)²`: by Cauchy–Schwarz `Bᵢⱼ² ≤ Bᵢᵢ Bⱼⱼ`. -/
theorem sum_sq_mul_transpose_le_trace_sq {p n : Type*} [Fintype p] [Fintype n]
    (K : Matrix p n ℝ) :
    ∑ i, ∑ j, ((K * Kᵀ) i j) ^ 2 ≤ ((K * Kᵀ).trace) ^ 2 := by
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq] using
    sum_sq_mul_transpose_le_sum_sq_mul_sum_sq K K

/-- The dot product of `A x` and `A y` is the bilinear form of the Gram matrix:
`(A x) ⬝ (A y) = x ⬝ (Aᵀ A) y`. -/
theorem mulVec_dotProduct_mulVec {p n : Type*} [Fintype p] [Fintype n] (A : Matrix p n ℝ)
    (x y : n → ℝ) : (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ ((Aᵀ * A) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Aᵀ, Matrix.vecMul_transpose]

/-- A matrix with `Aᵀ A = 1` (an isometry, e.g. an orthogonal matrix) preserves dot products:
`(A x) ⬝ (A y) = x ⬝ y`. -/
theorem mulVec_dotProduct_mulVec_of_transpose_mul_self {p n : Type*} [Fintype p] [Fintype n]
    [DecidableEq n] (A : Matrix p n ℝ) (hA : Aᵀ * A = 1) (x y : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
  rw [mulVec_dotProduct_mulVec, hA, one_mulVec]

/-- The squared norm of `A x` is the quadratic form of the Gram matrix: `‖A x‖² = x ⬝ (Aᵀ A) x`. -/
theorem mulVec_dotProduct_mulVec_self {p n : Type*} [Fintype p] [Fintype n] (A : Matrix p n ℝ)
    (x : n → ℝ) : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) :=
  mulVec_dotProduct_mulVec A x x

end Matrix
