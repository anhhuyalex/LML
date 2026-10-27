/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Projecting a linear system onto a left eigenvector

If `v = S + A v + R` and `w` is an eigenvector of `Aᵀ` with eigenvalue `lam`, then pairing the
system with `w` decouples one scalar equation.  The statement holds over any commutative ring and
any finite index type.  Commutativity of the scalars is needed, negatives are not.

## Main declarations

* `Matrix.dotProduct_system_of_transpose_eigenvector`
-/

@[expose] public section

open Matrix

namespace Matrix

/-- **Projection onto a left eigenvector.**  If `Aᵀ w = lam • w` and `v = S + A v + R`, then
`w ⬝ᵥ v = w ⬝ᵥ S + lam * (w ⬝ᵥ v) + w ⬝ᵥ R`. -/
theorem dotProduct_system_of_transpose_eigenvector {ι K : Type*} [Fintype ι] [CommSemiring K]
    (A : Matrix ι ι K) (w v S R : ι → K) (lam : K) (hw : Aᵀ *ᵥ w = lam • w)
    (hsys : v = S + A *ᵥ v + R) :
    w ⬝ᵥ v = w ⬝ᵥ S + lam * (w ⬝ᵥ v) + w ⬝ᵥ R := by
  have hp : w ⬝ᵥ (A *ᵥ v) = lam * (w ⬝ᵥ v) := by
    rw [← dotProduct_transpose_mulVec A v w, hw, dotProduct_smul, dotProduct_comm, smul_eq_mul]
  have h := congrArg (fun z => w ⬝ᵥ z) hsys
  simp only [dotProduct_add, hp] at h
  exact h

end Matrix
