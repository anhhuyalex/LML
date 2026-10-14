/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix

/-!
# Positive semidefinite matrices: closedness and dot-product Gram matrices

* `Matrix.isClosed_setOf_posSemidef`: the cone of real positive semidefinite matrices is closed.
  It is the intersection of the (closed) symmetric matrices with the closed half-spaces
  `{M | 0 ≤ x ⬝ᵥ M *ᵥ x}`.
* `Matrix.PosSemidef.sum_mul_mul_nonneg`: the quadratic form as a double sum `∑ᵢ ∑ⱼ vᵢ vⱼ Mᵢⱼ ≥ 0`.
* `Matrix.posSemidef_of_const_mul_dotProduct`: the matrix `(c ⬝ᵥ-Gram of v)`
  `(l, l') ↦ c * (v l ⬝ᵥ v l')` is positive semidefinite for `c ≥ 0`.  For the overlaps of
  spin configurations `c = N⁻¹`.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Finite n]

/-- The cone of real positive semidefinite matrices is closed. -/
theorem isClosed_setOf_posSemidef : IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  have := Fintype.ofFinite n
  simp_rw [posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  · exact isClosed_eq (by fun_prop) continuous_id
  · fun_prop

omit [Finite n] in
/-- A positive semidefinite real matrix has a nonnegative quadratic form in the double-sum shape
`∑ᵢ ∑ⱼ vᵢ vⱼ Mᵢⱼ`. -/
theorem PosSemidef.sum_mul_mul_nonneg [Fintype n] {M : Matrix n n ℝ} (hM : M.PosSemidef)
    (v : n → ℝ) : 0 ≤ ∑ i, ∑ j, v i * v j * M i j := by
  have h := hM.dotProduct_mulVec_nonneg v
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at h
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  ring

/-- **Dot-product Gram matrices are positive semidefinite:** the matrix with entries
`c * (v l ⬝ᵥ v l')` is positive semidefinite whenever `0 ≤ c`. -/
theorem posSemidef_of_const_mul_dotProduct {κ : Type*} [Fintype κ] (v : n → κ → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : (Matrix.of fun l l' => c * (v l ⬝ᵥ v l')).PosSemidef := by
  have h := (posSemidef_self_mul_conjTranspose (Matrix.of v)).smul hc
  convert h using 1
  ext l l'
  simp [Matrix.mul_apply, dotProduct]

end Matrix
