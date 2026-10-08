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
  simp only [mul_apply, mulVec, dotProduct, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact mul_assoc _ _ _


/-- **A Gram matrix has Frobenius norm at most its trace.** For `B = K Kᵀ`,
`∑ᵢⱼ Bᵢⱼ² ≤ (tr B)²`: by Cauchy–Schwarz `Bᵢⱼ² ≤ Bᵢᵢ Bⱼⱼ`. -/
theorem sum_sq_mul_transpose_le_trace_sq {p n : Type*} [Fintype p] [Fintype n]
    (K : Matrix p n ℝ) :
    ∑ i, ∑ j, ((K * Kᵀ) i j) ^ 2 ≤ ((K * Kᵀ).trace) ^ 2 := by
  have hentry : ∀ i j, (K * Kᵀ) i j = K i ⬝ᵥ K j := fun i j => by
    simp [Matrix.mul_apply, dotProduct]
  have hcs : ∀ i j, ((K * Kᵀ) i j) ^ 2 ≤ (K * Kᵀ) i i * (K * Kᵀ) j j := fun i j => by
    rw [hentry, hentry, hentry]
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (K i) (K j)
    simpa [dotProduct, sq] using this
  calc ∑ i, ∑ j, ((K * Kᵀ) i j) ^ 2 ≤ ∑ i, ∑ j, (K * Kᵀ) i i * (K * Kᵀ) j j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcs i j
    _ = ((K * Kᵀ).trace) ^ 2 := by
        simp only [Matrix.trace, Matrix.diag, sq, Finset.sum_mul_sum]

/-- The squared norm of `A x` is the quadratic form of the Gram matrix: `‖A x‖² = x ⬝ (Aᵀ A) x`. -/
theorem mulVec_dotProduct_mulVec_self {p n : Type*} [Fintype p] [Fintype n] (A : Matrix p n ℝ)
    (x : n → ℝ) : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Aᵀ, Matrix.vecMul_transpose]

end Matrix
