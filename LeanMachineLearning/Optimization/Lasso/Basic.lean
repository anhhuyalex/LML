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

/-- The vector `M x`, cast back into `EuclideanSpace`. -/
noncomputable def matVec (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (M.mulVec x)

/-- Positive semidefiniteness in the concrete Euclidean model used by the lasso files. -/
def IsPositiveSemidefinite (M : Matrix ι ι ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ ι, 0 ≤ inner ℝ x (matVec M x)

/--
The condition `r ∈ Span M` from the paper, represented as membership in the range
of the linear map `x ↦ M x`.
-/
def InMatrixSpan (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) : Prop :=
  ∃ y : EuclideanSpace ℝ ι, matVec M y = r

/--
The standing assumptions from Chapters 1--4 of `docs/Lasso.md`.
Keeping this bundled makes later theorem statements harder to accidentally weaken:
`M` is positive semidefinite, `r` lies in the span/range of `M`, and the explicit
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

end Lasso

end
