/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import LeanMachineLearning.Optimization.ConvexOpt.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Matrix utilities for the NTK development

Linear-algebra facts with no neural-network content: a double-sum form of positive
semidefiniteness, Frobenius-norm bounds (used to bound how fast gradient flow can move),
Frobenius inner product and trace factorizations for rank-one matrices, and the
passage from positive definiteness to a uniform spectral gap.
-/
@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix

namespace NTK

/-- A positive semidefinite matrix has a nonnegative quadratic form in the double-sum shape
`∑ᵢ ∑ⱼ αᵢ αⱼ Mᵢⱼ`. -/
theorem posSemidef_sum_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (α : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, α i * α j * M i j := by
  have h := hM.dotProduct_mulVec_nonneg α
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at h
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  ring

/-- `x ⬝ᵥ x` is the sum of the coordinate squares for any vector over a commutative semiring. -/
theorem dotProduct_self_eq_sum_sq {ι : Type*} {R : Type*} [Fintype ι] [CommSemiring R]
    (x : ι → R) : x ⬝ᵥ x = ∑ k : ι, x k ^ 2 := by
  simp [dotProduct, pow_two]

/-! ### Rank-One Matrices, Trace, and Frobenius Inner Product

Generalized algebraic identities for rank-one outer products `vecMulVec u v`, their traces,
Frobenius inner products, and Hadamard products. These identities hold over general
commutative semirings and are used throughout the multilayer Neural Tangent Kernel (NTK)
decomposition across layers (Proposition 2.25).
-/

/-- Frobenius inner product of two rank-one matrices in transpose-second orientation:
`Tr((u vᵀ) (p qᵀ)ᵀ) = (u ⬝ᵥ p) * (v ⬝ᵥ q)`.
Holds over any commutative semiring and arbitrary finite index types `m` and `n`. -/
theorem trace_vecMulVec_mul_transpose_vecMulVec {m n : Type*} {R : Type*} [Fintype m] [Fintype n]
    [CommSemiring R]
    (u p : m → R) (v q : n → R) :
    Matrix.trace (Matrix.vecMulVec u v * (Matrix.vecMulVec p q)ᵀ) = (u ⬝ᵥ p) * (v ⬝ᵥ q) := by
  rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [dotProduct_smul, smul_eq_mul, mul_comm]

/-- Frobenius inner product of two rank-one matrices in transpose-first orientation:
`Tr((u vᵀ)ᵀ (p qᵀ)) = (u ⬝ᵥ p) * (v ⬝ᵥ q)`.
Holds over any commutative semiring and arbitrary finite index types `m` and `n`. -/
theorem trace_transpose_vecMulVec_mul_vecMulVec {m n : Type*} {R : Type*} [Fintype m] [Fintype n]
    [CommSemiring R]
    (u p : m → R) (v q : n → R) :
    Matrix.trace ((Matrix.vecMulVec u v)ᵀ * Matrix.vecMulVec p q) = (u ⬝ᵥ p) * (v ⬝ᵥ q) := by
  rw [Matrix.transpose_vecMulVec]
  have h := trace_vecMulVec_mul_transpose_vecMulVec (R := R) v q u p
  rw [Matrix.transpose_vecMulVec] at h
  rw [h, mul_comm]

/-- Sum of all entries of the Hadamard product of two rank-one matrices:
`∑ i, ∑ j, (u vᵀ ⊙ p qᵀ) i j = (u ⬝ᵥ p) * (v ⬝ᵥ q)`. -/
theorem sum_hadamard_vecMulVec {m n : Type*} {R : Type*} [Fintype m] [Fintype n] [CommSemiring R]
    (u p : m → R) (v q : n → R) :
    (∑ i, ∑ j, (Matrix.vecMulVec u v ⊙ Matrix.vecMulVec p q) i j) = (u ⬝ᵥ p) * (v ⬝ᵥ q) := by
  rw [Matrix.sum_hadamard_eq, trace_vecMulVec_mul_transpose_vecMulVec]

/-! ### Frobenius Norm Utilities and the Gradient Speed Bound

Reusable Cauchy-Schwarz-type norm bounds for the Frobenius norm on matrices, used to bound how
fast gradient flow can move (Step 1 of the Gap 5 lazy-training bootstrap in
`NTK.Training.GradientFlow.Bootstrap`).
-/

open scoped Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

/-- The squared Frobenius norm of a matrix is the sum of the squares of its entries. -/
lemma matrix_frobenius_norm_sq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs]
  rw [← Real.sqrt_eq_rpow]
  have hnonneg : 0 ≤ ∑ i, ∑ j, |A i j| ^ (2 : ℝ) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    positivity
  calc
    √(∑ i, ∑ j, |A i j| ^ (2 : ℝ)) ^ 2 =
        ∑ i, ∑ j, |A i j| ^ (2 : ℝ) := Real.sq_sqrt hnonneg
    _ = _ := by simp [sq_abs]

/-- The squared Frobenius norm of a real rank-one matrix `vecMulVec u v` factors into
the product of the squared Euclidean lengths: `‖vecMulVec u v‖^2 = (u ⬝ᵥ u) * (v ⬝ᵥ v)`. -/
theorem vecMulVec_frobenius_norm_sq {m n : Type*} [Fintype m] [Fintype n]
    (u : m → ℝ) (v : n → ℝ) :
    ‖Matrix.vecMulVec u v‖ ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  rw [matrix_frobenius_norm_sq]
  simp only [Matrix.vecMulVec_apply, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [dotProduct, sq]

/-- The Frobenius norm of a real rank-one matrix `vecMulVec u v` factors into
the product of Euclidean lengths: `‖vecMulVec u v‖ = √(u ⬝ᵥ u) * √(v ⬝ᵥ v)`. -/
theorem vecMulVec_frobenius_norm {m n : Type*} [Fintype m] [Fintype n]
    (u : m → ℝ) (v : n → ℝ) :
    ‖Matrix.vecMulVec u v‖ = Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by
  have hsq := vecMulVec_frobenius_norm_sq u v
  have hu_nonneg : 0 ≤ u ⬝ᵥ u := by
    simp only [dotProduct, ← sq]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  have h := congr_arg Real.sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hu_nonneg] at h
  exact h

/-- Cauchy-Schwarz bound for the dot product of two vectors in terms of the Frobenius norm
of their rank-one outer product: `|(u ⬝ᵥ v)| ≤ ‖vecMulVec u v‖ = √(u ⬝ᵥ u) * √(v ⬝ᵥ v)`. -/
theorem abs_dotProduct_le_vecMulVec_frobenius_norm {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    |u ⬝ᵥ v| ≤ ‖Matrix.vecMulVec u v‖ := by
  rw [vecMulVec_frobenius_norm]
  rw [dotProduct_self_eq_sum_sq u, dotProduct_self_eq_sum_sq v]
  have h_sq : (u ⬝ᵥ v) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have h_nonneg_u : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  rw [← Real.sqrt_mul h_nonneg_u]
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq_eq_abs] at h_sqrt

/-- A row of a matrix restricted to the first `n` columns has Euclidean norm at most the Frobenius
norm of the matrix, and every entry is at most the Frobenius norm. -/
lemma norm_row_castSucc_le {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    ‖(WithLp.toLp 2 (fun α : Fin n => A i (Fin.castSucc α)) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖A‖ ∧
      |A i (Fin.last n)| ≤ ‖A‖ := by
  have hrow : ∑ j : Fin (n + 1), A i j ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [matrix_frobenius_norm_sq]
    exact Finset.single_le_sum (f := fun i => ∑ j : Fin (n + 1), A i j ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsplit : ∑ j : Fin (n + 1), A i j ^ 2 =
      (∑ α : Fin n, A i (Fin.castSucc α) ^ 2) + A i (Fin.last n) ^ 2 := Fin.sum_univ_castSucc _
  constructor
  · refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (A i (Fin.last n))]
  · refine (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 ?_
    rw [sq_abs]
    nlinarith [Finset.sum_nonneg fun α (_ : α ∈ Finset.univ) => sq_nonneg (A i (Fin.castSucc α))]

/-- Cauchy-Schwarz bound on a matrix-vector product: `‖M w‖ ≤ ‖M‖_F ‖w‖`. Unlike Mathlib's
`Matrix.l2_opNorm_mulVec`, this is stated for the *Frobenius* norm, matching the norm instance
used throughout the NTK Lipschitz-propagation machinery (Gap 2 in
`NTK.Training.GradientFlow.KernelStability`). -/
theorem mulVec_frobenius_norm_le {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (w : EuclideanSpace ℝ (Fin b)) :
    ‖(WithLp.toLp 2 (M *ᵥ w.ofLp) : EuclideanSpace ℝ (Fin a))‖ ≤ ‖M‖ * ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow]
  rw [show ‖(WithLp.toLp 2 (M *ᵥ w.ofLp) : EuclideanSpace ℝ (Fin a))‖ ^ 2 =
      ∑ i : Fin a, ((M *ᵥ w.ofLp) i) ^ 2 from EuclideanSpace.real_norm_sq_eq _]
  rw [matrix_frobenius_norm_sq]
  have hw_sq : ‖w‖ ^ 2 = ∑ j : Fin b, (w.ofLp j) ^ 2 := EuclideanSpace.real_norm_sq_eq _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Matrix.mulVec_apply, dotProduct]
  calc
    (∑ j : Fin b, M i j * w.ofLp j) ^ 2 ≤
        (∑ j : Fin b, (M i j) ^ 2) * (∑ j : Fin b, (w.ofLp j) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) (fun j => w.ofLp j)
    _ = (∑ j : Fin b, (M i j) ^ 2) * ‖w‖ ^ 2 := by rw [hw_sq]

/-- The inner product on `EuclideanSpace ℝ (Fin n)` is the dot product of the underlying functions.
Not a simp lemma: it would rewrite every real inner product on `EuclideanSpace`. -/
lemma real_inner_eq_dotProduct {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫ = u.ofLp ⬝ᵥ v.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-! ### Matrices as continuous linear maps between Euclidean spaces -/

/-- The matrix `M` as a continuous linear map between Euclidean spaces (`v ↦ M v`): an abbreviation
for Mathlib's `Matrix.toEuclideanLin` made continuous (Mathlib bundles the continuous version,
`Matrix.toEuclideanCLM`, only for square matrices). -/
noncomputable abbrev matrixCLM {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    EuclideanSpace ℝ (Fin b) →L[ℝ] EuclideanSpace ℝ (Fin a) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

lemma matrixCLM_apply {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (v : EuclideanSpace ℝ (Fin b)) :
    matrixCLM M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := by
  simp [matrixCLM, Matrix.toLpLin_apply]

lemma matrixCLM_sub {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) :
    matrixCLM M - matrixCLM N = matrixCLM (M - N) := by
  ext v : 1
  simp [matrixCLM_apply, Matrix.sub_mulVec]

lemma norm_matrixCLM_le {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ‖matrixCLM M‖ ≤ ‖M‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
    rw [matrixCLM_apply]; exact mulVec_frobenius_norm_le M v

/-- `matrixCLM Mᵀ` is the adjoint of `matrixCLM M`. -/
lemma inner_matrixCLM_transpose {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (u : EuclideanSpace ℝ (Fin a)) (v : EuclideanSpace ℝ (Fin b)) :
    ⟪matrixCLM Mᵀ u, v⟫ = ⟪u, matrixCLM M v⟫ := by
  simp only [matrixCLM_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    RCLike.inner_apply, conj_trivial, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


/-- `matrixCLM Mᵀ` is the Hilbert-space adjoint of `matrixCLM M`. -/
lemma matrixCLM_transpose_eq_adjoint {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    matrixCLM Mᵀ = ContinuousLinearMap.adjoint (matrixCLM M) :=
  (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => (inner_matrixCLM_transpose M u v).symm ▸ rfl

/-! ### From Positive Definiteness to a Uniform Spectral Gap

The global lazy-training theorems assume a *shifted* positive semidefiniteness
`(K - lambda • 1).PosSemidef` with `lambda > 0`. For any positive definite matrix such a `lambda`
exists (take the smallest eigenvalue), so strict positive definiteness of a limiting kernel
-- for instance from linear independence of its features -- supplies the gap hypothesis. -/

/-- **A positive definite real matrix has a positive spectral gap.** If `A` is positive definite,
there is `c > 0` with `A - c • 1` positive semidefinite (`c` is the smallest eigenvalue). This is
the bridge from `Matrix.PosDef`, e.g. `Matrix.posDef_gram_iff_linearIndependent`, to the shifted-PSD
form `(K - lambda • 1).PosSemidef` used by the global theorems; it holds for any finite index type,
not only for an NTK. -/
theorem exists_pos_sub_smul_one_posSemidef_of_posDef {n : Type*} [Finite n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) : ∃ c : ℝ, 0 < c ∧ (A - c • 1).PosSemidef := by
  cases nonempty_fintype n
  have hH : A.IsHermitian := hA.isHermitian
  have hev : ∀ i, 0 < hH.eigenvalues i := hA.eigenvalues_pos
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, one_pos, by
      refine Matrix.posSemidef_iff_dotProduct_mulVec.2
        ⟨?_, fun x => by simp [Subsingleton.elim x 0]⟩
      ext i
      exact (IsEmpty.false i).elim⟩
  obtain ⟨c, hc⟩ : ∃ c, 0 < c ∧ ∀ i, c ≤ hH.eigenvalues i := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty hH.eigenvalues, ?_,
      fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
    rw [Finset.lt_inf'_iff]
    exact fun i _ => hev i
  refine ⟨c, hc.1, ?_⟩
  have h1 : A = (hH.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hH.eigenvalues *
      star (hH.eigenvectorUnitary : Matrix n n ℝ) := by
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using hH.spectral_theorem
  have hU : (hH.eigenvectorUnitary : Matrix n n ℝ) * star (hH.eigenvectorUnitary : Matrix n n ℝ)
      = 1 := by simp
  have hD : Matrix.diagonal (fun i => hH.eigenvalues i - c) =
      Matrix.diagonal hH.eigenvalues - c • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  have hshift : A - c • (1 : Matrix n n ℝ) =
      (hH.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal (fun i => hH.eigenvalues i - c) *
        star (hH.eigenvectorUnitary : Matrix n n ℝ) := by
    conv_lhs => rw [h1]
    rw [hD]
    simp [Matrix.mul_sub, Matrix.sub_mul, hU]
  rw [hshift]
  exact (Matrix.posSemidef_diagonal_iff.2 fun i => sub_nonneg.2 (hc.2 i)).mul_mul_conjTranspose_same
    _

/-! ### General Gram Matrices and Positive Semidefiniteness -/

/-- The unscaled Gram matrix `M * Mᵀ` formed by vector dot products is symmetric. -/
theorem gram_transpose {m n R : Type*} [Fintype n] [CommSemiring R] (M : Matrix m n R) :
    (Matrix.of fun α β => M α ⬝ᵥ M β)ᵀ = Matrix.of fun α β => M α ⬝ᵥ M β := by
  ext α β
  simp [Matrix.transpose_apply, dotProduct_comm]

/-- A scaled Gram matrix `c • (M * Mᵀ)` is symmetric. -/
theorem scaled_gram_transpose {m n R : Type*} [Fintype n] [CommSemiring R] (c : R)
    (M : Matrix m n R) :
    (Matrix.of fun α β => c * (M α ⬝ᵥ M β))ᵀ = Matrix.of fun α β => c * (M α ⬝ᵥ M β) := by
  ext α β
  simp [Matrix.transpose_apply, dotProduct_comm]

/-- A constant matrix `c • 1` is symmetric. -/
theorem const_matrix_transpose {m R : Type*} (c : R) :
    (Matrix.of fun _ _ : m => c)ᵀ = Matrix.of fun _ _ : m => c := by
  ext α β
  rfl

/-- The outer product `M * Mᵀ` of a real matrix is positive semidefinite. This is Mathlib's
`Matrix.posSemidef_self_mul_conjTranspose` in the real (`Mᴴ = Mᵀ`) form used throughout `NTK`. -/
theorem mul_transpose_posSemidef {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n ℝ) :
    (M * Mᵀ).PosSemidef := by
  simpa using Matrix.posSemidef_self_mul_conjTranspose M

/-- Quadratic form of a conjugated matrix: `uᵀ (W A Wᵀ) v = (Wᵀ u)ᵀ A (Wᵀ v)`. -/
theorem quadForm_mul_mul_transpose {m n R : Type*} [Fintype m] [Fintype n] [CommSemiring R]
    (W : Matrix m n R) (A : Matrix n n R) (u v : m → R) :
    u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) = (Wᵀ *ᵥ u) ⬝ᵥ (A *ᵥ (Wᵀ *ᵥ v)) := by
  have h1 : (W * A * Wᵀ) *ᵥ v = W *ᵥ (A *ᵥ (Wᵀ *ᵥ v)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose W u]

/-- The all-ones matrix is a right identity for the entrywise (Hadamard) product. Mathlib's
`Matrix.hadamard_of_one` is stated for `Matrix.of 1`, which `simp` does not match against the
`Matrix.of fun _ _ => 1` spelling used for terminal layers, so this is the simp-normal form here. -/
@[simp]
theorem hadamard_allOnes {m n α : Type*} [MulOneClass α] (A : Matrix m n α) :
    A ⊙ Matrix.of (fun _ _ => 1) = A :=
  Matrix.hadamard_of_one A

/-- The all-ones matrix is a left identity for the entrywise (Hadamard) product. -/
@[simp]
theorem allOnes_hadamard {m n α : Type*} [MulOneClass α] (A : Matrix m n α) :
    Matrix.of (fun _ _ => 1) ⊙ A = A :=
  Matrix.of_one_hadamard A

/-- The unscaled Gram matrix `M * Mᵀ` formed by vector dot products is positive semidefinite. -/
theorem gram_posSemidef {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n ℝ) :
    (Matrix.of fun α β => M α ⬝ᵥ M β).PosSemidef := by
  classical
  have h_eq : (Matrix.of fun α β => M α ⬝ᵥ M β) = M * Mᵀ := by
    ext α β
    simp [Matrix.mul_apply, dotProduct]
  rw [h_eq]
  exact mul_transpose_posSemidef M

/-- A non-negatively scaled Gram matrix `c • (M * Mᵀ)` is positive semidefinite. -/
theorem scaled_gram_posSemidef {m n : Type*} [Finite m] [Fintype n]
    (c : ℝ) (hc : 0 ≤ c) (M : Matrix m n ℝ) :
    (Matrix.of fun α β => c * (M α ⬝ᵥ M β)).PosSemidef := by
  have h_eq : (Matrix.of fun α β => c * (M α ⬝ᵥ M β)) = c • (Matrix.of fun α β => M α ⬝ᵥ M β) := by
    ext α β
    simp [Matrix.smul_apply]
  rw [h_eq]
  exact (gram_posSemidef M).smul hc

/-- The all-ones matrix `1_{m × m}` is positive semidefinite. -/
theorem posSemidef_allOnes {m : Type*} [Finite m] :
    (Matrix.of fun _ _ : m => (1 : ℝ)).PosSemidef := by
  have h_eq : (Matrix.of fun _ _ : m => (1 : ℝ)) =
      Matrix.of fun α β => (fun (_ : m) (_ : Unit) => (1 : ℝ)) α ⬝ᵥ
                           (fun (_ : m) (_ : Unit) => (1 : ℝ)) β := by
    ext α β
    simp [dotProduct]
  rw [h_eq]
  exact gram_posSemidef (fun _ _ => 1)


/-! ### Orthogonal Projection Algebra -/

/-- A square real matrix `P` is an orthogonal projection matrix if it is symmetric (`Pᵀ = P`)
and idempotent (`P * P = P`). -/
def isOrthogonalProjection {p : Type*} [Fintype p]
    (P : Matrix p p ℝ) : Prop :=
  Pᵀ = P ∧ P * P = P

/-- The complementary orthogonal projector `Pᗮ = I - P`. -/
def orthogonalComplement {p : Type*} [DecidableEq p]
    (P : Matrix p p ℝ) : Matrix p p ℝ :=
  1 - P

/-- The transpose of the complementary projector is itself. -/
theorem transpose_orthogonalComplement {p : Type*} [Fintype p] [DecidableEq p]
    (P : Matrix p p ℝ) (hP : isOrthogonalProjection P) :
    (orthogonalComplement P)ᵀ = orthogonalComplement P := by
  dsimp [orthogonalComplement]
  rw [Matrix.transpose_sub, Matrix.transpose_one, hP.1]

/-- The complementary projector is idempotent: `(I - P)² = I - P`. -/
theorem orthogonalComplement_idem {p : Type*} [Fintype p] [DecidableEq p]
    (P : Matrix p p ℝ) (hP : isOrthogonalProjection P) :
    orthogonalComplement P * orthogonalComplement P = orthogonalComplement P := by
  dsimp [orthogonalComplement]
  calc (1 - P) * (1 - P)
      = 1 * (1 - P) - P * (1 - P) := by rw [Matrix.sub_mul]
    _ = (1 - P) - (P * 1 - P * P) := by rw [Matrix.one_mul, Matrix.mul_sub]
    _ = 1 - P - (P - P) := by rw [Matrix.mul_one, hP.2]
    _ = 1 - P := by simp

/-- The complement of an orthogonal projection is an orthogonal projection. -/
theorem orthogonalComplement_isOrthogonalProjection {p : Type*} [Fintype p] [DecidableEq p]
    (P : Matrix p p ℝ) (hP : isOrthogonalProjection P) :
    isOrthogonalProjection (orthogonalComplement P) :=
  ⟨transpose_orthogonalComplement P hP, orthogonalComplement_idem P hP⟩

/-- Orthogonal complement annihilates `P` from the left: `Pᗮ * P = 0`. -/
theorem mul_orthogonalComplement_self {p : Type*} [Fintype p] [DecidableEq p]
    (P : Matrix p p ℝ) (hP : isOrthogonalProjection P) :
    orthogonalComplement P * P = 0 := by
  dsimp [orthogonalComplement]
  rw [Matrix.sub_mul, Matrix.one_mul, hP.2, sub_self]

/-- Orthogonal complement annihilates `P` from the right: `P * Pᗮ = 0`. -/
theorem mul_self_orthogonalComplement {p : Type*} [Fintype p] [DecidableEq p]
    (P : Matrix p p ℝ) (hP : isOrthogonalProjection P) :
    P * orthogonalComplement P = 0 := by
  dsimp [orthogonalComplement]
  rw [Matrix.mul_sub, Matrix.mul_one, hP.2, sub_self]

/-- Exact algebraic decomposition of any weight matrix into projected and complementary
components: `W = W P + W Pᗮ`. -/
theorem orthogonalDecomposition {n p : Type*} [Fintype p] [DecidableEq p]
    (W : Matrix n p ℝ) (P : Matrix p p ℝ) :
    W = W * P + W * orthogonalComplement P := by
  dsimp [orthogonalComplement]
  rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

/-- If `P` projects onto the subspace containing the columns of `X` (`P * X = X`), then the
complementary residual `W * Pᗮ` annihilates `X`: `(W * Pᗮ) * X = 0`. -/
theorem residual_annihilates {n p q : Type*} [Fintype p] [DecidableEq p]
    (W : Matrix n p ℝ) (P : Matrix p p ℝ) (X : Matrix p q ℝ) (hX : P * X = X) :
    (W * orthogonalComplement P) * X = 0 := by
  have h_comp : orthogonalComplement P * X = 0 := by
    dsimp [orthogonalComplement]
    rw [Matrix.sub_mul, Matrix.one_mul, hX, sub_self]
  rw [Matrix.mul_assoc, h_comp, Matrix.mul_zero]

/-- Forward propagation through layer weights `W` acting on features `X` depends purely on the
projected component `W * P`: `W * X = (W * P) * X`. -/
theorem orthogonalDecomposition_mul {n p q : Type*} [Fintype p]
    (W : Matrix n p ℝ) (P : Matrix p p ℝ) (X : Matrix p q ℝ) (hX : P * X = X) :
    W * X = (W * P) * X := by
  classical
  conv_lhs => rw [orthogonalDecomposition W P]
  rw [Matrix.add_mul, residual_annihilates W P X hX, add_zero]

/-- The trace of the orthogonal projector `X (Xᵀ X)⁻¹ Xᵀ` onto the column span of `X` is the
number of columns `m`, independently of the number of rows `n`. In the deep NTK this gives
`n⁻¹ tr P = m / n → 0` for the projector onto the `m` forward features. -/
theorem trace_orthogonalProjectionOfGram {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (X : Matrix n m ℝ) [Invertible (Xᵀ * X)] :
    (X * ⅟(Xᵀ * X) * Xᵀ).trace = Fintype.card m := by
  rw [Matrix.trace_mul_cycle, mul_invOf_self, Matrix.trace_one]

end NTK

end
