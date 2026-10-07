/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# Orthogonal matrices act transitively on spheres

A Householder reflection `1 - 2 w wᵀ / ‖w‖²` with `w = x - y` swaps two vectors `x`, `y` of the same
Euclidean norm. This is the only fact about `O(n)` needed to move a fixed vector to a random one in
invariance arguments for Gaussian matrices.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Orthogonal matrices act transitively on spheres.** If `x ⬝ x = y ⬝ y` there is an orthogonal
matrix `U` (`U Uᵀ = Uᵀ U = 1`) with `U x = y`: the Householder reflection in `x - y`. -/
theorem exists_orthogonal_mulVec_eq (x y : n → ℝ) (h : x ⬝ᵥ x = y ⬝ᵥ y) :
    ∃ U : Matrix n n ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ U *ᵥ x = y := by
  by_cases hxy : x = y
  · exact ⟨1, by simp, by simp, by simp [hxy]⟩
  set w : n → ℝ := x - y with hw
  have hww : 0 < w ⬝ᵥ w := by
    rcases (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i) : 0 ≤ w ⬝ᵥ w).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h'.symm)) hxy
  set c : ℝ := 2 / (w ⬝ᵥ w) with hc
  set U : Matrix n n ℝ := 1 - c • vecMulVec w w with hU
  have hUT : Uᵀ = U := by simp [hU, transpose_sub, transpose_smul, transpose_vecMulVec]
  have hcw : c * (w ⬝ᵥ w) = 2 := div_mul_cancel₀ _ hww.ne'
  have hUU : U * U = 1 := by
    have h2 : vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
      rw [vecMulVec_mul_vecMulVec]
      simp [vecMulVec_smul]
    simp only [hU, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul,
      mul_one, h2]
    linear_combination (norm := module) hcw • (c • vecMulVec w w)
  refine ⟨U, by rw [hUT]; exact hUU, by rw [hUT]; exact hUU, ?_⟩
  have hwx : w ⬝ᵥ x * c = 1 := by
    have h4 : w ⬝ᵥ w = 2 * (w ⬝ᵥ x) := by
      simp only [hw, sub_dotProduct, dotProduct_sub]
      rw [dotProduct_comm y x]; linarith
    rw [h4] at hcw
    linarith
  ext i
  simp only [hU, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  have hwi : w i = x i - y i := by rw [hw]; rfl
  have : (x - y) ⬝ᵥ x = w ⬝ᵥ x := rfl
  rw [this, hwi]
  linear_combination (-(x i - y i)) * hwx

end Matrix
