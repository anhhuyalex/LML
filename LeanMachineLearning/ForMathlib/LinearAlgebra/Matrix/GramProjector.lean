/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.OrthogonalProjection
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# The Gram Projector `Φ (Φᵀ Φ)⁻¹ Φᵀ`

The orthogonal projector onto the column span of a feature matrix `Φ` (e.g. the `m` forward features
`φ(h_k^α)` in the deep NTK), and the exact decomposition of a back-propagated vector
`Vᵀ u = Φ c + (V Pᗮ)ᵀ u` with `c = (Φᵀ Φ)⁻¹ (V Φ)ᵀ u`. The first summand depends on the weight
matrix `V` only through `V Φ`; the second is the residual used in the conditional Chebyshev bounds
of `Initialization/GaussianConditioning.lean`.
-/

@[expose]
public section

open scoped Matrix

namespace Matrix

/-- The orthogonal projector `Φ (Φᵀ Φ)⁻¹ Φᵀ` onto the column span of `Φ`. -/
noncomputable def gramProjector {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (Φ : Matrix n m ℝ) : Matrix n n ℝ :=
  Φ * (Φᵀ * Φ)⁻¹ * Φᵀ

/-- The Gram projector is symmetric, `P_Φᵀ = P_Φ`, for every `Φ` (as `(ΦᵀΦ)⁻¹` is symmetric). -/
theorem gramProjector_transpose {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (Φ : Matrix n m ℝ) : (gramProjector Φ)ᵀ = gramProjector Φ := by
  have hsymm : ((Φᵀ * Φ)⁻¹)ᵀ = (Φᵀ * Φ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  unfold gramProjector
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm,
    Matrix.mul_assoc]

/-- If `ΦᵀΦ` is invertible, the Gram projector `P_Φ` is an orthogonal projection
(`IsStarProjection`). -/
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

/-- If `ΦᵀΦ` is invertible, the Gram projector fixes the features: `P_Φ Φ = Φ`. -/
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
      (V * (1 - gramProjector Φ))ᵀ *ᵥ u := by
  have hP := gramProjector_transpose Φ
  have h1 : (V * (1 - gramProjector Φ))ᵀ *ᵥ u =
      Vᵀ *ᵥ u - gramProjector Φ *ᵥ (Vᵀ *ᵥ u) := by
    rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, hP,
      Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec]
  have h2 : gramProjector Φ *ᵥ (Vᵀ *ᵥ u) = Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ ((V * Φ)ᵀ *ᵥ u)) := by
    unfold gramProjector
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h2]
  abel

/-- **Residual of the Gram projector.** `(1 - P_Φ) y = y - Φ (Φᵀ Φ)⁻¹ Φᵀ y`, i.e. the residual of
the least-squares fit of `y` on the columns of `Φ`. -/
theorem one_sub_gramProjector_mulVec {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (Φ : Matrix n m ℝ) (y : n → ℝ) :
    (1 - gramProjector Φ) *ᵥ y = y - Φ *ᵥ (((Φᵀ * Φ)⁻¹ * Φᵀ) *ᵥ y) := by
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, gramProjector, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- **The Gram projector has trace equal to the number of columns.** If `Φᵀ Φ` is invertible,
`Tr P_Φ = card m` (the rank of `Φ`), by cyclic invariance of the trace. -/
theorem trace_gramProjector {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (Φ : Matrix n m ℝ) (h : IsUnit (Φᵀ * Φ).det) :
    (gramProjector Φ).trace = (Fintype.card m : ℝ) := by
  rw [gramProjector, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ h, Matrix.trace_one]

/-- **Pythagoras for the Gram projector residual.** If `Φᵀ Φ` is invertible,
`‖(1 - P_Φ) y‖² = ‖y‖² - yᵀ P_Φ y`. -/
theorem dotProduct_one_sub_gramProjector_mulVec_self {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (Φ : Matrix n m ℝ) (h : IsUnit (Φᵀ * Φ).det) (y : n → ℝ) :
    ((1 - gramProjector Φ) *ᵥ y) ⬝ᵥ ((1 - gramProjector Φ) *ᵥ y) =
      y ⬝ᵥ y - y ⬝ᵥ (gramProjector Φ *ᵥ y) := by
  have hP := isOrthogonalProjection_gramProjector Φ h
  have h1 : IsStarProjection (1 - gramProjector Φ) := hP.one_sub
  have hsq : (1 - gramProjector Φ) * (1 - gramProjector Φ) = 1 - gramProjector Φ :=
    ((isStarProjection_matrix_real_iff _).1 h1).2
  rw [← Matrix.dotProduct_transpose_mulVec, h1.transpose_eq, Matrix.mulVec_mulVec, hsq,
    Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]


/-- The Gram projector only depends on the span of the columns: relabelling the columns by an
equivalence does not change it. -/
theorem gramProjector_submatrix_equiv {n m m' : Type*} [Fintype n] [Fintype m] [Fintype m']
    [DecidableEq m] [DecidableEq m'] (A : Matrix n m ℝ) (e : m' ≃ m) :
    gramProjector (A.submatrix id e) = gramProjector A := by
  have hG : (A.submatrix id e)ᵀ * (A.submatrix id e) = (Aᵀ * A).submatrix e e := by
    ext a b
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  ext i k
  simp only [gramProjector, hG, Matrix.inv_submatrix_equiv, Matrix.mul_apply,
    Matrix.submatrix_apply, Matrix.transpose_apply, id]
  rw [← Equiv.sum_comp e (fun b => (∑ a, A i a * (Aᵀ * A)⁻¹ a b) * A k b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Equiv.sum_comp e (fun a => A i a * (Aᵀ * A)⁻¹ a (e b))]

/-- **Equivariance of the Gram projector.** For a matrix `U` with orthonormal columns
(`Uᵀ U = 1`, e.g. an orthogonal matrix), `P_{U Φ} = U P_Φ Uᵀ`: the Gram matrix is unchanged,
`(U Φ)ᵀ (U Φ) = Φᵀ Φ`. -/
theorem gramProjector_orthonormal_mul {n n' m : Type*} [Fintype n] [Fintype n'] [Fintype m]
    [DecidableEq n]
    [DecidableEq m] (U : Matrix n' n ℝ) (hU : Uᵀ * U = 1) (Φ : Matrix n m ℝ) :
    gramProjector (U * Φ) = U * gramProjector Φ * Uᵀ := by
  have hG : (U * Φ)ᵀ * (U * Φ) = Φᵀ * Φ := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  unfold gramProjector
  rw [hG]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

universe u

/-- **Orthogonal projections factor through orthonormal rows.** An orthogonal projection matrix
`P` is `Oᵀ O` for a matrix `O` with orthonormal rows (`O Oᵀ = 1`), indexed by a type `κ` with
`card κ = Tr P`.

Proof: the spectral theorem gives `P = U D Uᵀ` with `U` orthogonal; idempotence forces the
eigenvalues in `D` to be `0` or `1`, and `O` keeps the rows of `Uᵀ` with eigenvalue `1`. -/
theorem exists_orthonormal_rows_of_isStarProjection {ι : Type u} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : IsStarProjection P) :
    ∃ (κ : Type u) (_ : Fintype κ) (_ : DecidableEq κ) (O : Matrix κ ι ℝ),
      O * Oᵀ = 1 ∧ Oᵀ * O = P ∧ (Fintype.card κ : ℝ) = P.trace := by
  classical
  have hidem : P * P = P := ((isStarProjection_matrix_real_iff _).1 hP).2
  have hH : P.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.transpose_eq
  obtain ⟨U, d, hspec, hUU, hUU'⟩ : ∃ (U : Matrix ι ι ℝ) (d : ι → ℝ),
      P = U * Matrix.diagonal d * Uᵀ ∧ Uᵀ * U = 1 ∧ U * Uᵀ = 1 := by
    refine ⟨(hH.eigenvectorUnitary : Matrix ι ι ℝ), hH.eigenvalues, ?_, ?_, ?_⟩
    · have := hH.spectral_theorem
      simpa [Unitary.conjStarAlgAut_apply, Function.comp_def,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
    · simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    · simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hD : Uᵀ * P * U = Matrix.diagonal d := by
    rw [hspec]
    calc Uᵀ * (U * Matrix.diagonal d * Uᵀ) * U
        = (Uᵀ * U) * Matrix.diagonal d * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  have hDD : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal d := by
    calc _ = Uᵀ * P * (U * Uᵀ) * P * U := by rw [← hD]; simp only [Matrix.mul_assoc]
      _ = Uᵀ * (P * P) * U := by rw [hUU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hidem, hD]
  have h01 : ∀ k, d k = 0 ∨ d k = 1 := fun k => by
    have := congrFun (congrFun hDD k) k
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at this
    have h2 : d k * (d k - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hsum : ∀ (f : ι → ℝ), ∑ s : {k // d k = 1}, f s.1 = ∑ k, d k * f k := fun f => by
    rw [← Finset.sum_subtype (Finset.univ.filter fun k => d k = 1) (fun k => by simp) f,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases h01 k with h | h <;> simp [h]
  refine ⟨{k // d k = 1}, inferInstance, inferInstance, Matrix.of fun s i => U i s.1, ?_, ?_, ?_⟩
  · ext s t
    have := congrFun (congrFun hUU s.1) t.1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] at this ⊢
    rw [show (∑ i, U i s.1 * U i t.1) = _ from this]
    simp [Matrix.one_apply, Subtype.ext_iff]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    have hij : P i j = ∑ k, U i k * d k * U j k := by
      conv_lhs => rw [hspec]
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    rw [hij, hsum (fun k => U i k * U j k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have : P.trace = ∑ k, d k := by
      rw [hspec, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul,
        Matrix.trace_diagonal]
    rw [this]
    have := hsum (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    exact this


/-- The row-space projector of a design `X` is `Xᵀ (X Xᵀ)⁻¹ X`. -/
theorem gramProjector_transpose_eq {m n₀ : Type*} [Fintype m] [Fintype n₀] [DecidableEq m]
    (X : Matrix m n₀ ℝ) :
    gramProjector Xᵀ = Xᵀ * (X * Xᵀ)⁻¹ * X := by
  simp [gramProjector]

/-- The row-space projector acts trivially on the design: `X P_X = X`. -/
theorem mul_gramProjector_transpose {m n₀ : Type*} [Fintype m] [Fintype n₀] [DecidableEq m]
    (X : Matrix m n₀ ℝ) (hX : IsUnit (X * Xᵀ).det) :
    X * gramProjector Xᵀ = X := by
  have h := gramProjector_mul_self Xᵀ (by simpa using hX)
  have := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, gramProjector_transpose] using this

/-- The residual projector annihilates the design: `X (1 - P_X) = 0`. -/
theorem mul_one_sub_gramProjector_transpose {m n₀ : Type*} [Fintype m] [Fintype n₀]
    [DecidableEq m] [DecidableEq n₀] (X : Matrix m n₀ ℝ) (hX : IsUnit (X * Xᵀ).det) :
    X * (1 - gramProjector Xᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, mul_gramProjector_transpose X hX, sub_self]

end Matrix

end
