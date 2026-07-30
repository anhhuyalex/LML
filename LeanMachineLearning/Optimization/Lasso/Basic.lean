/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import LeanMachineLearning.Optimization.ConvexOpt.Basic

/-!
# Lasso and Diagonal Linear Network Objectives

This file defines the base objectives for the lasso regularization path analysis.
-/

@[expose] public section

namespace Lasso

open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-- Cast a coordinate function into the Euclidean `L₂` model used throughout this folder. -/
noncomputable def euclideanOf (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm x

/--
The canonical continuous linear equivalence between the concrete `EuclideanSpace ℝ ι` model
used throughout this folder and the underlying function space `ι → ℝ`. Exposed once here so
that this construction (and `continuous_euclidean_apply` below) don't need to be rebuilt at
each call site that needs, e.g., continuity of a map built from coordinate projections.
-/
noncomputable def euclideanToPiEquiv : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv

/-- Coordinate projection `x ↦ x i` is continuous on `EuclideanSpace ℝ ι`. -/
lemma continuous_euclidean_apply (i : ι) :
    Continuous (fun x : EuclideanSpace ℝ ι => x i) :=
  (continuous_apply i).comp euclideanToPiEquiv.continuous

/--
Unfold an inner product against an `euclideanOf`-built vector into a coordinate sum. This is
the recurring first step ("unfold `euclideanOf`, rewrite via
`EuclideanSpace.inner_eq_star_dotProduct`, unfold `dotProduct`") in many coordinatewise
identities throughout this folder; stated once here so those proofs can `rw` this instead of
repeating the three-step unfold.
-/
lemma inner_euclideanOf_eq_sum (f : ι → ℝ) (h : EuclideanSpace ℝ ι) :
    inner ℝ (euclideanOf f) h = ∑ i, f i * h i := by
  dsimp [euclideanOf]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [dotProduct]
  simp [mul_comm]

/-- The all-ones vector. This is the vector denoted `𝟙` in `docs/Lasso.md`. -/
noncomputable def ones : EuclideanSpace ℝ ι :=
  euclideanOf (fun _ => 1)

/-- Coordinatewise nonnegativity. -/
def Nonnegative (x : EuclideanSpace ℝ ι) : Prop :=
  ∀ i, 0 ≤ x i

/-- Coordinatewise positivity. -/
def Positive (x : EuclideanSpace ℝ ι) : Prop :=
  ∀ i, 0 < x i

/-- Coordinatewise nonvanishing. Used for the nondegenerate DLN initializations. -/
def NonzeroCoordinates (x : EuclideanSpace ℝ ι) : Prop :=
  ∀ i, x i ≠ 0

/-- Coordinatewise product. -/
noncomputable def hadamard (x y : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun i => x i * y i)

/-- Coordinatewise square. -/
noncomputable def coordinateSquare (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun i => x i * x i)

omit [Fintype ι] in
/-- `hadamard` is commutative. -/
lemma hadamard_comm (x y : EuclideanSpace ℝ ι) : hadamard x y = hadamard y x := by
  ext i; simp [hadamard, euclideanOf]; ring

omit [Fintype ι] in
/-- `hadamard` is additive in its first argument. -/
lemma hadamard_add_left (x y v : EuclideanSpace ℝ ι) :
    hadamard (x + y) v = hadamard x v + hadamard y v := by
  ext i; simp [hadamard, euclideanOf]; ring

omit [Fintype ι] in
/-- `hadamard` is subtractive in its first argument. -/
lemma hadamard_sub_left (x y v : EuclideanSpace ℝ ι) :
    hadamard (x - y) v = hadamard x v - hadamard y v := by
  ext i; simp [hadamard, euclideanOf]; ring

omit [Fintype ι] in
/-- `hadamard` commutes with scalar multiplication in its first argument. -/
lemma hadamard_smul_left (c : ℝ) (x v : EuclideanSpace ℝ ι) :
    hadamard (c • x) v = c • hadamard x v := by
  ext i; simp [hadamard, euclideanOf, smul_eq_mul]; ring

/-- `hadamard · v` bundled as a linear map, for composing with derivative/continuity lemmas
that expect a `LinearMap` (mirrors `matVecLM` below). -/
noncomputable def hadamardLM (v : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := fun h => hadamard h v
  map_add' := fun x y => hadamard_add_left x y v
  map_smul' := fun c x => by
    simp only [RingHom.id_apply]
    exact hadamard_smul_left c x v

/-- The vector `M x`, cast back into `EuclideanSpace`. -/
noncomputable def matVec (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (M.mulVec x)

/--
Positive semidefiniteness in the concrete Euclidean model used by the lasso files.

Symmetry is part of the definition: nonnegativity of `xᵀ M x` alone only
constrains the symmetric part of an arbitrary real matrix.
-/
structure IsPositiveSemidefinite (M : Matrix ι ι ℝ) : Prop where
  symm : M.IsSymm
  nonneg : ∀ x : EuclideanSpace ℝ ι, 0 ≤ inner ℝ x (matVec M x)

lemma IsPositiveSemidefinite.get_symm
    {M : Matrix ι ι ℝ} (hM : IsPositiveSemidefinite M) : M.IsSymm := by
  cases hM
  rename_i symm _
  exact symm

lemma IsPositiveSemidefinite.get_nonneg
    {M : Matrix ι ι ℝ} (hM : IsPositiveSemidefinite M) (x : EuclideanSpace ℝ ι) :
    0 ≤ inner ℝ x (matVec M x) := by
  cases hM
  rename_i _ nonneg
  exact nonneg x

/--
The condition `r ∈ Span M` from the paper, represented as membership in the range
of the linear map `x ↦ M x`.
-/
def InMatrixSpan (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) : Prop :=
  ∃ y : EuclideanSpace ℝ ι, matVec M y = r

/--
The standing assumptions from Chapters 1--4 of `docs/Lasso.md`.
Keeping this bundled makes later theorem statements harder to accidentally weaken:
`M` is symmetric positive semidefinite, `r` lies in the span/range of `M`, and the explicit
weight decay `lambda` is nonnegative.
-/
structure ProblemData (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) :
    Prop where
  psd : IsPositiveSemidefinite M
  r_mem_span : InMatrixSpan M r
  lambda_nonneg : 0 ≤ lambda

/--
The quadratic loss function parameterized by a positive semidefinite matrix `M`
and vector `r`.
-/
noncomputable def quadraticLoss
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ x (matVec M x) - inner ℝ r x

/-- The lasso objective incorporating implicit regularization parameterized by `μ`. -/
noncomputable def lassoObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  quadraticLoss M r x + (lambda + 1 / μ) * ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖

/--
The positive lasso objective is the same expression as `lassoObjective`, but it is
intended to be minimized over `Nonnegative x`.
-/
noncomputable def positiveLassoObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  lassoObjective M r lambda μ x

/--
The smooth part of the positive lasso objective used in Chapter 4:
`\widetilde L(x) = \ell(x) + lambda * <1, x>`.
-/
noncomputable def tiltedLoss
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  quadraticLoss M r x + lambda * inner ℝ ones x

/-- The diagonal linear network (DLN) objective with explicit weight decay `lambda`. -/
noncomputable def dlnObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (u v : EuclideanSpace ℝ ι) : ℝ :=
  quadraticLoss M r (hadamard u v) + (lambda / 2) * (‖u‖^2 + ‖v‖^2)

/-- The positive DLN objective for the `u ∘ u` case with explicit weight decay `lambda`. -/
noncomputable def posDlnObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (u : EuclideanSpace ℝ ι) : ℝ :=
  quadraticLoss M r (coordinateSquare u) + lambda * ‖u‖^2

/-- The entropy mirror map `h(x) = 1/4 * Σᵢ (xᵢ log xᵢ - xᵢ)`. -/
noncomputable def entropyMirror (x : EuclideanSpace ℝ ι) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, (x i * Real.log (x i) - x i)

/--
The Bregman divergence associated with `entropyMirror`, written in the explicit
coordinate form used in Eq. (4.2). This definition is meant for positive
coordinates; Chapter 4 extends it to zero coordinates by continuity.
-/
noncomputable def entropyBregman (x y : EuclideanSpace ℝ ι) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, (x i * Real.log (x i / y i) - x i + y i)

/-- A selected minimizer of the lasso objective at inverse regularization `μ`. -/
def IsLassoMinimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) : Prop :=
  IsMinOn (lassoObjective M r lambda μ) Set.univ x

/-- A selected minimizer of the positive lasso objective at inverse regularization `μ`. -/
def IsPositiveLassoMinimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) : Prop :=
  Nonnegative x ∧ IsMinOn (positiveLassoObjective M r lambda μ) {x | Nonnegative x} x

/-- The augmented block matrix for reducing the signed lasso to positive lasso. -/
noncomputable def augmentedMatrix (M : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks M (-M) (-M) M

/-- The augmented vector for reducing the signed lasso to positive lasso. -/
noncomputable def augmentedVector (r : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm (Sum.elim r (-r))

/-- Matrix-vector multiplication for augmented matrix. -/
lemma augmentedMatrix_matVec
    (M : Matrix ι ι ℝ) (a b : EuclideanSpace ℝ ι) :
    matVec (augmentedMatrix M) (euclideanOf (Sum.elim a b)) =
      euclideanOf (Sum.elim (matVec M a - matVec M b) (-matVec M a + matVec M b)) := by
  ext j
  dsimp [augmentedMatrix, matVec, euclideanOf]
  cases j with
  | inl i => simp [Matrix.mulVec, dotProduct]; try ring
  | inr i => simp [Matrix.mulVec, dotProduct]; try ring

/-- Inner product with augmented vector. -/
lemma inner_augmentedVector_sumElim
    (r a b : EuclideanSpace ℝ ι) :
    inner ℝ (augmentedVector r) (euclideanOf (Sum.elim a b)) =
      inner ℝ r a - inner ℝ r b := by
  dsimp [augmentedVector, euclideanOf]
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [Real.inner_apply]
  change (∑ j, (Sum.elim r (-r)) j * (Sum.elim a b) j) = _
  have h_sum := Fintype.sum_sum_type (fun j => (Sum.elim r (-r)) j * (Sum.elim a b) j)
  rw [h_sum]
  have hs :
      (∑ i : ι, (Sum.elim r (-r)) (Sum.inl i) * (Sum.elim a b) (Sum.inl i)) +
          ∑ i : ι, (Sum.elim r (-r)) (Sum.inr i) * (Sum.elim a b) (Sum.inr i) =
        ∑ i : ι, (r i * a i + -r i * b i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [hs]
  have h_split :
      (∑ i : ι, (r i * a i + -r i * b i)) =
        (∑ i : ι, r i * a i) + ∑ i : ι, -r i * b i := by
    rw [Finset.sum_add_distrib]
  rw [h_split]
  have h_neg : (∑ i : ι, -r i * b i) = -(∑ i : ι, r i * b i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_neg, sub_eq_add_neg]

omit [Fintype ι] in
/-- The augmented block matrix is symmetric whenever the base matrix is. -/
lemma augmentedMatrix_isSymm (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    (augmentedMatrix M).IsSymm := by
  unfold Matrix.IsSymm augmentedMatrix
  rw [Matrix.fromBlocks_transpose, hM]
  congr 1
  · ext i j; simp [hM.apply i j]
  · ext i j; simp [hM.apply i j]

omit [Fintype ι] in
/-- Coordinatewise components of the augmented vector. -/
lemma augmentedVector_apply_inl (r : EuclideanSpace ℝ ι) (i : ι) :
    augmentedVector r (Sum.inl i) = r i := by
  simp [augmentedVector]

omit [Fintype ι] in
lemma augmentedVector_apply_inr (r : EuclideanSpace ℝ ι) (i : ι) :
    augmentedVector r (Sum.inr i) = -r i := by
  simp [augmentedVector]

omit [Fintype ι] in
/-- `coordinateSquare` distributes over a `Sum.elim` split. -/
lemma coordinateSquare_sumElim (a b : EuclideanSpace ℝ ι) :
    coordinateSquare (euclideanOf (Sum.elim a b)) =
      euclideanOf (Sum.elim (coordinateSquare a) (coordinateSquare b)) := by
  ext j
  cases j with
  | inl i => simp [coordinateSquare, euclideanOf]
  | inr i => simp [coordinateSquare, euclideanOf]

omit [Fintype ι] in
/-- The algebraic identity behind Section 5.1.2 of `docs/Lasso.md`:
`p_pos = (u+v)/2`, `p_neg = (u-v)/2` satisfy `p_pos^2 - p_neg^2 = u ∘ v`. -/
lemma coordinateSquare_half_add_sub_eq_hadamard (u v : EuclideanSpace ℝ ι) :
    coordinateSquare ((1/2 : ℝ) • (u + v)) - coordinateSquare ((1/2 : ℝ) • (u - v)) =
      hadamard u v := by
  ext i
  simp [coordinateSquare, euclideanOf, hadamard, smul_eq_mul]
  ring

/-- Inner product splits over Sum.elim. -/
lemma inner_sumElim (a b c d : EuclideanSpace ℝ ι) :
    inner ℝ (euclideanOf (Sum.elim a b)) (euclideanOf (Sum.elim c d)) =
      inner ℝ a c + inner ℝ b d := by
  dsimp [euclideanOf]
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [Real.inner_apply]
  change (∑ j, (Sum.elim a b) j * (Sum.elim c d) j) = _
  have h_sum := Fintype.sum_sum_type (fun j => (Sum.elim a b) j * (Sum.elim c d) j)
  rw [h_sum]
  apply congr_arg₂
  · apply Finset.sum_congr rfl; intro i _; rfl
  · apply Finset.sum_congr rfl; intro i _; rfl

/-- Matrix-vector multiplication is additive in the concrete Euclidean wrapper. -/
lemma matVec_add
    (M : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    matVec M (x + y) = matVec M x + matVec M y := by
  ext i
  simp [matVec, euclideanOf, Matrix.mulVec_add]

/-- Matrix-vector multiplication is subtractive in the concrete Euclidean wrapper. -/
lemma matVec_sub
    (M : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    matVec M (x - y) = matVec M x - matVec M y := by
  ext i
  simp [matVec, euclideanOf, Matrix.mulVec_sub]

/-- Matrix-vector multiplication commutes with scalar multiplication. -/
lemma matVec_smul_eq
    (M : Matrix ι ι ℝ) (c : ℝ) (x : EuclideanSpace ℝ ι) :
    matVec M (c • x) = c • matVec M x := by
  ext i
  simp [matVec, euclideanOf, Matrix.mulVec_smul]

/-- `matVec M` bundled as a linear map, for composing with continuity/derivative lemmas that
expect a `LinearMap` (e.g. `LinearMap.continuous_of_finiteDimensional`,
`LinearMap.isBigO_comp`) instead of the raw function together with `matVec_add`/`matVec_smul_eq`
separately. -/
noncomputable def matVecLM (M : Matrix ι ι ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := matVec M
  map_add' := matVec_add M
  map_smul' := matVec_smul_eq M

/-- Symmetry of `M` transfers the matrix from the second inner-product argument to the first. -/
lemma inner_matVec_comm_of_isSymm
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (x y : EuclideanSpace ℝ ι) :
    inner ℝ x (matVec M y) = inner ℝ (matVec M x) y := by
  dsimp [matVec, euclideanOf]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  dsimp
  rw [star_trivial, star_trivial]
  have H0 : (M *ᵥ y.ofLp) ⬝ᵥ x.ofLp = x.ofLp ⬝ᵥ (M *ᵥ y.ofLp) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [H0]
  have H1 : x.ofLp ⬝ᵥ (M *ᵥ y.ofLp) = (x.ofLp ᵥ* M) ⬝ᵥ y.ofLp :=
    Matrix.dotProduct_mulVec _ _ _
  rw [H1]
  have H2 : y.ofLp ⬝ᵥ (M *ᵥ x.ofLp) = (M *ᵥ x.ofLp) ⬝ᵥ y.ofLp := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [H2]
  congr 1
  ext i
  dsimp [Matrix.vecMul, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro j _
  change x.ofLp j * M j i = M i j * x.ofLp j
  have hm : M j i = M i j := (hM.apply j i).symm
  rw [hm]
  ring

/-- Completing the square in a quadratic loss when `M y = r`. -/
lemma quadraticLoss_complete_square
    (M : Matrix ι ι ℝ) (r x y : EuclideanSpace ℝ ι)
    (hM : M.IsSymm) (hy : matVec M y = r) :
    inner ℝ (x - y) (matVec M (x - y)) =
      2 * quadraticLoss M r x + inner ℝ y (matVec M y) := by
  have h_cross₁ : inner ℝ x (matVec M y) = inner ℝ r x := by
    rw [hy, real_inner_comm]
  have h_cross₂ : inner ℝ y (matVec M x) = inner ℝ r x := by
    rw [inner_matVec_comm_of_isSymm M hM y x, hy]
  rw [matVec_sub, inner_sub_left, inner_sub_right, inner_sub_right]
  rw [h_cross₁, h_cross₂]
  dsimp [quadraticLoss]
  ring

/-- The quadratic loss of a scalar multiple, in homogeneous coordinates. -/
lemma quadraticLoss_smul
    (M : Matrix ι ι ℝ) (r x : EuclideanSpace ℝ ι) (c : ℝ) :
    quadraticLoss M r (c • x) =
      (1 / 2 : ℝ) * c ^ 2 * inner ℝ x (matVec M x) - c * inner ℝ r x := by
  rw [quadraticLoss, matVec_smul_eq, inner_smul_left, inner_smul_right,
    inner_smul_right]
  simp only [RCLike.conj_to_real]
  ring

/-- A positive semidefinite matrix has nonnegative trace. -/
lemma IsPositiveSemidefinite.trace_nonnegative
    {M : Matrix ι ι ℝ} (hM : IsPositiveSemidefinite M) :
    0 ≤ ∑ i, M i i := by
  classical
  apply Finset.sum_nonneg
  intro i _
  simpa [matVec, euclideanOf, EuclideanSpace.inner_eq_star_dotProduct] using
    hM.nonneg (EuclideanSpace.single i 1)

/--
The squared norm of `M x` is controlled by the quadratic form of a positive
semidefinite matrix.  The trace is a convenient finite-dimensional constant.
-/
lemma matVec_norm_sq_le_trace_mul
    (M : Matrix ι ι ℝ) (hM : IsPositiveSemidefinite M)
    (x : EuclideanSpace ℝ ι) :
    ‖matVec M x‖ ^ 2 ≤ (∑ i, M i i) * inner ℝ x (matVec M x) := by
  classical
  let B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toLinearMap₂' ℝ M
  have hB_nonneg : ∀ z, 0 ≤ B z z := by
    intro z
    simpa [B, Matrix.toLinearMap₂'_apply', matVec, euclideanOf,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      hM.nonneg (euclideanOf z)
  have hB_symm : LinearMap.IsSymm B := by
    rw [LinearMap.isSymm_def]
    intro v w
    have h := inner_matVec_comm_of_isSymm M hM.symm (euclideanOf v) (euclideanOf w)
    simpa [B, Matrix.toLinearMap₂'_apply', matVec, euclideanOf,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, (matVec M x i) ^ 2
        ≤ ∑ i, M i i * inner ℝ x (matVec M x) := by
          apply Finset.sum_le_sum
          intro i _
          have hi := LinearMap.BilinForm.apply_sq_le_of_symm B hB_nonneg hB_symm
            (Pi.single i 1) x
          simpa [B, Matrix.toLinearMap₂'_apply', matVec, euclideanOf,
            EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hi
    _ = (∑ i, M i i) * inner ℝ x (matVec M x) := by
      rw [Finset.sum_mul]

/--
Cauchy-Schwarz inequality for the seminorm induced by a positive semidefinite matrix `M`:
`⟨x, My⟩² ≤ ⟨x, Mx⟩ * ⟨y, My⟩`. Same `B := Matrix.toLinearMap₂' ℝ M` construction as
`matVec_norm_sq_le_trace_mul` above, applied directly at `(x, y)` instead of at a coordinate
basis vector.
-/
lemma inner_matVec_sq_le_mul
    (M : Matrix ι ι ℝ) (hM : IsPositiveSemidefinite M) (x y : EuclideanSpace ℝ ι) :
    inner ℝ x (matVec M y) ^ 2 ≤ inner ℝ x (matVec M x) * inner ℝ y (matVec M y) := by
  classical
  let B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toLinearMap₂' ℝ M
  have hB_nonneg : ∀ z, 0 ≤ B z z := by
    intro z
    simpa [B, Matrix.toLinearMap₂'_apply', matVec, euclideanOf,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      hM.nonneg (euclideanOf z)
  have hB_symm : LinearMap.IsSymm B := by
    rw [LinearMap.isSymm_def]
    intro v w
    have h := inner_matVec_comm_of_isSymm M hM.symm (euclideanOf v) (euclideanOf w)
    simpa [B, Matrix.toLinearMap₂'_apply', matVec, euclideanOf,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h
  have hcs := LinearMap.BilinForm.apply_sq_le_of_symm B hB_nonneg hB_symm x.ofLp y.ofLp
  simpa [B, Matrix.toLinearMap₂'_apply', matVec, euclideanOf,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hcs

end Lasso

end
