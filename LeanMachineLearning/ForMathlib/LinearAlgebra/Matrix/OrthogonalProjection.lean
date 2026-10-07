/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Orthogonal projection matrices

Pure real linear algebra for an orthogonal projection matrix `P` (`IsStarProjection P`, i.e.
`Pᵀ = P` and `P * P = P`): the complement `1 - P`, the exact decomposition `W = W P + W Pᗮ` of any
matrix, the residual `W Pᗮ` annihilating every `X` with `P X = X`, `‖P x‖² = x ⬝ P x ≤ ‖x‖²`, and
the resulting trace and Frobenius-norm identities for compressions `P A P`.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

/-- For real matrices, being a Mathlib star projection (self-adjoint idempotent) means being
symmetric and idempotent: `Pᵀ = P` and `P * P = P`. This is the form used throughout the NTK
files; an *orthogonal projection matrix* is exactly an `IsStarProjection` real matrix. -/
theorem isStarProjection_matrix_real_iff {p : Type*} [Fintype p] (P : Matrix p p ℝ) :
    IsStarProjection P ↔ Pᵀ = P ∧ P * P = P := by
  rw [isStarProjection_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, and_comm]

/-- The symmetry half of `IsStarProjection` for a real matrix: `Pᵀ = P`. -/
theorem _root_.IsStarProjection.transpose_eq {p : Type*} [Fintype p] {P : Matrix p p ℝ}
    (hP : IsStarProjection P) : Pᵀ = P :=
  ((isStarProjection_matrix_real_iff P).1 hP).1

/-- The complement of an orthogonal projection is an orthogonal projection. -/
theorem orthogonalComplement_isOrthogonalProjection {p : Type*} [Fintype p] [DecidableEq p]
    (P : Matrix p p ℝ) (hP : IsStarProjection P) :
    IsStarProjection (1 - P) :=
  hP.one_sub

/-- Orthogonal complement annihilates `P` from the right: `P * Pᗮ = 0`. -/
theorem mul_self_orthogonalComplement {p : Type*} [Fintype p] [DecidableEq p]
    (P : Matrix p p ℝ) (hP : IsStarProjection P) :
    P * (1 - P) = 0 :=
  hP.mul_one_sub_self

/-- Exact algebraic decomposition of any weight matrix into projected and complementary
components: `W = W P + W Pᗮ`. -/
theorem orthogonalDecomposition {n p : Type*} [Fintype p] [DecidableEq p]
    (W : Matrix n p ℝ) (P : Matrix p p ℝ) :
    W = W * P + W * (1 - P) := by
  rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

/-- If `P` projects onto the subspace containing the columns of `X` (`P * X = X`), then the
complementary residual `W * Pᗮ` annihilates `X`: `(W * Pᗮ) * X = 0`. -/
theorem residual_annihilates {n p q : Type*} [Fintype p] [DecidableEq p]
    (W : Matrix n p ℝ) (P : Matrix p p ℝ) (X : Matrix p q ℝ) (hX : P * X = X) :
    (W * (1 - P)) * X = 0 := by
  have h_comp : (1 - P) * X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hX, sub_self]
  rw [Matrix.mul_assoc, h_comp, Matrix.mul_zero]

/-- Forward propagation through layer weights `W` acting on features `X` depends purely on the
projected component `W * P`: `W * X = (W * P) * X`. -/
theorem orthogonalDecomposition_mul {n p q : Type*} [Fintype p]
    (W : Matrix n p ℝ) (P : Matrix p p ℝ) (X : Matrix p q ℝ) (hX : P * X = X) :
    W * X = (W * P) * X := by
  classical
  conv_lhs => rw [orthogonalDecomposition W P]
  rw [Matrix.add_mul, residual_annihilates W P X hX, add_zero]

/-- For an orthogonal projection `Q`, `‖Q x‖² = x ⬝ᵥ Q x`. -/
lemma mulVec_dot_self_eq {p : Type*} [Fintype p]
    (Q : Matrix p p ℝ) (hQ : IsStarProjection Q) (x : p → ℝ) :
    (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ (Q *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ.transpose_eq, Matrix.mulVec_mulVec,
    hQ.isIdempotentElem.eq,
    dotProduct_comm]

/-- An orthogonal projection does not increase the Euclidean norm. -/
lemma mulVec_dot_self_le {p : Type*} [Fintype p]
    (Q : Matrix p p ℝ) (hQ : IsStarProjection Q) (b : p → ℝ) :
    (Q *ᵥ b) ⬝ᵥ (Q *ᵥ b) ≤ b ⬝ᵥ b := by
  classical
  have h1 := mulVec_dot_self_eq Q hQ b
  have h2 := mulVec_dot_self_eq (1 - Q)
    (orthogonalComplement_isOrthogonalProjection Q hQ) b
  have h3 : ((1 - Q) *ᵥ b) = b - Q *ᵥ b := by
    simp [Matrix.sub_mulVec]
  have h4 : 0 ≤ ((1 - Q) *ᵥ b) ⬝ᵥ ((1 - Q) *ᵥ b) :=
    dotProduct_self_star_nonneg _
  rw [h2, h3] at h4
  simp only [dotProduct_sub] at h4
  linarith

/-- Left multiplication by an orthogonal projection does not increase the Frobenius norm. -/
lemma frobSq_projector_mul_le {p q : Type*} [Fintype p] [Fintype q]
    (Q : Matrix p p ℝ) (hQ : IsStarProjection Q) (B : Matrix p q ℝ) :
    ∑ k, ∑ l, (Q * B) k l ^ 2 ≤ ∑ k, ∑ l, B k l ^ 2 := by
  rw [Finset.sum_comm (f := fun k l => (Q * B) k l ^ 2),
    Finset.sum_comm (f := fun k l => B k l ^ 2)]
  refine Finset.sum_le_sum fun l _ => ?_
  have := mulVec_dot_self_le Q hQ (fun i => B i l)
  simpa [dotProduct, Matrix.mulVec, Matrix.mul_apply, sq] using this

/-- Right multiplication by an orthogonal projection does not increase the Frobenius norm. -/
lemma frobSq_mul_projector_le {p q : Type*} [Fintype p] [Fintype q]
    (Q : Matrix p p ℝ) (hQ : IsStarProjection Q) (B : Matrix q p ℝ) :
    ∑ k, ∑ l, (B * Q) k l ^ 2 ≤ ∑ k, ∑ l, B k l ^ 2 := by
  have h := frobSq_projector_mul_le Q hQ Bᵀ
  rw [Finset.sum_comm (f := fun k l => (B * Q) k l ^ 2),
    Finset.sum_comm (f := fun k l => B k l ^ 2)]
  have hT : (Q * Bᵀ) = (B * Q)ᵀ := by rw [Matrix.transpose_mul, hQ.transpose_eq]
  rw [hT] at h
  simpa using h

/-- Compression by an orthogonal projector does not increase the Frobenius norm:
`‖Q A Q‖_F ≤ ‖A‖_F`. -/
lemma frobSq_compress_le {p : Type*} [Fintype p]
    (Q : Matrix p p ℝ) (hQ : IsStarProjection Q) (A : Matrix p p ℝ) :
    ∑ k, ∑ l, (Q * A * Q) k l ^ 2 ≤ ∑ k, ∑ l, A k l ^ 2 := by
  rw [Matrix.mul_assoc]
  exact (frobSq_projector_mul_le Q hQ (A * Q)).trans (frobSq_mul_projector_le Q hQ A)

/-- Trace of a matrix compressed by an orthogonal projector: `tr(Q A Q) = tr(A Q)`. -/
lemma trace_compress_projector {p : Type*} [Fintype p] (Q A : Matrix p p ℝ)
    (hQ : IsStarProjection Q) : (Q * A * Q).trace = (A * Q).trace := by
  rw [Matrix.trace_mul_cycle, hQ.isIdempotentElem.eq, Matrix.trace_mul_comm]

/-- `tr(Pᗮ A Pᗮ) = tr A - tr(A P)`: the mean of the residual Gaussian quadratic form. -/
lemma trace_compress_orthogonalComplement {p : Type*} [Fintype p] [DecidableEq p]
    (P A : Matrix p p ℝ) (hP : IsStarProjection P) :
    ((1 - P) * A * (1 - P)).trace = A.trace - (A * P).trace := by
  rw [trace_compress_projector _ _ (orthogonalComplement_isOrthogonalProjection P hP)]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]

end Matrix

end
