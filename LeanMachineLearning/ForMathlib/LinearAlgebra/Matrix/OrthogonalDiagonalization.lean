/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Orthogonal conjugation and the diagonalization of a PSD weight

Two facts about real orthogonal change of basis (`Uᵀ U = 1`), stated for arbitrary finite index
types:

* `Matrix.inv_transpose_mul_mul_orthogonal`: `(Uᵀ M U)⁻¹ = Uᵀ M⁻¹ U` for every `M` (with the
  convention `0⁻¹ = 0` for singular `M`);
* `Matrix.exists_trace_mul_eq_sum_eigenvalues`: for a positive semidefinite `C` there are an
  orthogonal `U` and nonnegative weights `w` with `∑ w = tr C` and
  `tr (C N) = ∑ⱼ wⱼ (Uᵀ N U)ⱼⱼ` for every `N`. This reduces a trace against a PSD weight to a
  nonnegatively weighted sum of diagonal entries after a rotation.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

/-- The inverse of an orthogonal conjugate: `(Uᵀ M U)⁻¹ = Uᵀ M⁻¹ U` for `Uᵀ U = 1`. -/
theorem inv_transpose_mul_mul_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) : (Uᵀ * M * U)⁻¹ = Uᵀ * M⁻¹ * U := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have h1 : U⁻¹ = Uᵀ := Matrix.inv_eq_right_inv hU'
  have h2 : (Uᵀ)⁻¹ = U := Matrix.inv_eq_right_inv hU
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, h1, h2, Matrix.mul_assoc]

/-- A PSD weight is diagonalized by an orthogonal matrix: `tr (C N) = ∑ⱼ wⱼ (Uᵀ N U)ⱼⱼ` with
`w ≥ 0` the eigenvalues of `C`, so `∑ w = tr C`. -/
theorem exists_trace_mul_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    ∃ (U : Matrix ι ι ℝ) (w : ι → ℝ), Uᵀ * U = 1 ∧ (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = C.trace ∧
      ∀ N : Matrix ι ι ℝ, (C * N).trace = ∑ j, w j * (Uᵀ * N * U) j j := by
  have hH := hC.isHermitian
  refine ⟨(hH.eigenvectorUnitary : Matrix ι ι ℝ), hH.eigenvalues, ?_, hC.eigenvalues_nonneg, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · simpa using (hH.trace_eq_sum_eigenvalues).symm
  · intro N
    have hspec := hH.spectral_theorem
    set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
    have hC' : C = U * Matrix.diagonal hH.eigenvalues * Uᵀ := by
      conv_lhs => rw [hspec]
      simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, hUdef]
    have h : (C * N).trace = ((U * Matrix.diagonal hH.eigenvalues * Uᵀ) * N).trace :=
      congrArg (fun X : Matrix ι ι ℝ => (X * N).trace) hC'
    rw [h, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm U]
    simp only [Matrix.mul_assoc]
    simp [Matrix.trace, Matrix.diagonal_mul]

end Matrix

end
