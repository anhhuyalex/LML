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
* `Matrix.posSemidef_symm`: an infinite array all of whose finite principal submatrices are
  positive semidefinite is symmetric.
* `Matrix.posSemidef_comp`: if every finite principal submatrix of an infinite array is
  positive semidefinite, so is the array `(A (f l) (f l'))_{l, l'}` for any `f : ℕ → ℕ`.
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

/-- An infinite array all of whose finite principal submatrices are positive semidefinite is
symmetric. -/
theorem posSemidef_symm {A : ℕ → ℕ → ℝ}
    (hA : ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef) (a b : ℕ) :
    A a b = A b a := by
  simpa using (hA (max a b + 1)).isHermitian.apply ⟨b, by omega⟩ ⟨a, by omega⟩

/-- **Reindexing an infinite array** along any `f : ℕ → ℕ` (e.g. a permutation) preserves the
positive semidefiniteness of all finite principal submatrices. -/
theorem posSemidef_comp {A : ℕ → ℕ → ℝ}
    (hA : ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef) (f : ℕ → ℕ) (k : ℕ) :
    (Matrix.of fun l l' : Fin k => A (f l) (f l')).PosSemidef := by
  set N := (Finset.univ.sup fun l : Fin k => f l) + 1 with hN
  have hlt : ∀ l : Fin k, f l < N := fun l =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun l : Fin k => f l) (Finset.mem_univ l))
  have h := (hA N).submatrix (fun l : Fin k => (⟨f l, hlt l⟩ : Fin N))
  exact h

end Matrix
