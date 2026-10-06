/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Entries of a sandwiched matrix `M Γ Mᵀ`

The entries of `M Γ Mᵀ` are the bilinear forms `Γ` evaluated on the rows of `M`. This is the
row-wise form of the covariance propagation rule `Cov (M x) = M Cov (x) Mᵀ`.
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

end Matrix
