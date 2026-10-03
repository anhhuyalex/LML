/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil

/-!
# The Gram Projector `Φ (Φᵀ Φ)⁻¹ Φᵀ`

The orthogonal projector onto the column span of a feature matrix `Φ` (the `m` forward features
`φ(h_k^α)` in the deep NTK), and the exact decomposition of a back-propagated vector
`Vᵀ u = Φ c + (V Pᗮ)ᵀ u` with `c = (Φᵀ Φ)⁻¹ (V Φ)ᵀ u`. The first summand depends on the weight
matrix `V` only through `V Φ`; the second is the residual used in the conditional Chebyshev bounds
of `Initialization/GaussianConditioning.lean`.
-/

@[expose]
public section

open Matrix

namespace NTK


/-- The orthogonal projector `Φ (Φᵀ Φ)⁻¹ Φᵀ` onto the column span of `Φ`. -/
noncomputable def gramProjector {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (Φ : Matrix n m ℝ) : Matrix n n ℝ :=
  Φ * (Φᵀ * Φ)⁻¹ * Φᵀ

theorem gramProjector_transpose {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (Φ : Matrix n m ℝ) : (gramProjector Φ)ᵀ = gramProjector Φ := by
  have hsymm : ((Φᵀ * Φ)⁻¹)ᵀ = (Φᵀ * Φ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  unfold gramProjector
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm,
    Matrix.mul_assoc]

theorem isOrthogonalProjection_gramProjector {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (Φ : Matrix n m ℝ) (h : IsUnit (Φᵀ * Φ).det) :
    IsStarProjection (gramProjector Φ) := by
  refine (isStarProjection_matrix_real_iff _).2 ⟨gramProjector_transpose Φ, ?_⟩
  · unfold gramProjector
    have hinv : (Φᵀ * Φ) * (Φᵀ * Φ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
    calc Φ * (Φᵀ * Φ)⁻¹ * Φᵀ * (Φ * (Φᵀ * Φ)⁻¹ * Φᵀ)
        = Φ * (Φᵀ * Φ)⁻¹ * ((Φᵀ * Φ) * (Φᵀ * Φ)⁻¹) * Φᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Φ * (Φᵀ * Φ)⁻¹ * Φᵀ := by rw [hinv, Matrix.mul_one]

theorem gramProjector_mul_self {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (Φ : Matrix n m ℝ) (h : IsUnit (Φᵀ * Φ).det) :
    gramProjector Φ * Φ = Φ := by
  unfold gramProjector
  have hinv : (Φᵀ * Φ)⁻¹ * (Φᵀ * Φ) = 1 := Matrix.nonsing_inv_mul _ h
  calc Φ * (Φᵀ * Φ)⁻¹ * Φᵀ * Φ = Φ * ((Φᵀ * Φ)⁻¹ * (Φᵀ * Φ)) := by
        simp only [Matrix.mul_assoc]
    _ = Φ := by rw [hinv, Matrix.mul_one]

/-- `gramProjector Φ` is an orthogonal projector for *every* `Φ`: when `Φᵀ Φ` is singular the
matrix inverse is `0` and `gramProjector Φ = 0`. This is what lets the projector be used as a
measurable function of the past without a case split on invertibility. -/
theorem isOrthogonalProjection_gramProjector_all {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (Φ : Matrix n m ℝ) : IsStarProjection (gramProjector Φ) := by
  by_cases h : IsUnit (Φᵀ * Φ).det
  · exact isOrthogonalProjection_gramProjector Φ h
  · have hz : gramProjector Φ = 0 := by
      unfold gramProjector
      rw [Matrix.nonsing_inv_apply_not_isUnit _ h]
      simp
    rw [hz]
    exact IsStarProjection.zero _

/-- The projector onto the column span of `Φ` has trace equal to the number of columns. -/
theorem trace_gramProjector {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (Φ : Matrix n m ℝ) (h : IsUnit (Φᵀ * Φ).det) :
    (gramProjector Φ).trace = Fintype.card m := by
  unfold gramProjector
  rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ h, Matrix.trace_one]

/-- The residual projector `Pᗮ` annihilates the features: `Pᗮ Φ = 0`. -/
theorem orthogonalComplement_gramProjector_mul {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (Φ : Matrix n m ℝ) (h : IsUnit (Φᵀ * Φ).det) :
    orthogonalComplement (gramProjector Φ) * Φ = 0 := by
  simp [orthogonalComplement, Matrix.sub_mul, gramProjector_mul_self Φ h]

/-- For invertible `Φᵀ Φ`, a weight matrix acts on the features only through its projected part:
`V Φ = (V P) Φ`. -/
theorem mul_eq_mul_gramProjector_mul {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] {k : Type*} (V : Matrix k n ℝ) (Φ : Matrix n m ℝ)
    (h : IsUnit (Φᵀ * Φ).det) : V * Φ = (V * gramProjector Φ) * Φ := by
  rw [Matrix.mul_assoc, gramProjector_mul_self Φ h]

/-- **Decomposition of a back-propagated vector.** For `P = Φ (Φᵀ Φ)⁻¹ Φᵀ`, any weight matrix
`V : Matrix k n ℝ` (the layer widths need not agree) and vector `u : k → ℝ`,
`Vᵀ u = Φ c + (V Pᗮ)ᵀ u` with `c = (Φᵀ Φ)⁻¹ (V Φ)ᵀ u`: the projected part depends on `V` only
through `V Φ`. -/
theorem transpose_mulVec_eq_gramProjector_add {k n m : Type*} [Fintype k] [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m] (Φ : Matrix n m ℝ) (V : Matrix k n ℝ)
    (u : k → ℝ) :
    Vᵀ *ᵥ u = Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ ((V * Φ)ᵀ *ᵥ u)) +
      (V * orthogonalComplement (gramProjector Φ))ᵀ *ᵥ u := by
  have hP := gramProjector_transpose Φ
  have h1 : (V * orthogonalComplement (gramProjector Φ))ᵀ *ᵥ u =
      Vᵀ *ᵥ u - gramProjector Φ *ᵥ (Vᵀ *ᵥ u) := by
    rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
    simp only [orthogonalComplement, Matrix.transpose_sub, Matrix.transpose_one, hP,
      Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec]
  have h2 : gramProjector Φ *ᵥ (Vᵀ *ᵥ u) = Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ ((V * Φ)ᵀ *ᵥ u)) := by
    unfold gramProjector
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h2]
  abel

end NTK

end
