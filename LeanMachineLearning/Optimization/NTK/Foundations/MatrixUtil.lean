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
semidefiniteness, Frobenius-norm bounds (used to bound how fast gradient flow can move), and the
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
lemma matrix_frobenius_norm_sq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    ‖A‖ ^ 2 = ∑ i : Fin a, ∑ j : Fin b, (A i j) ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs]
  rw [← Real.sqrt_eq_rpow]
  have hnonneg : 0 ≤ ∑ i : Fin a, ∑ j : Fin b, |A i j| ^ (2 : ℝ) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    positivity
  calc
    √(∑ i : Fin a, ∑ j : Fin b, |A i j| ^ (2 : ℝ)) ^ 2 =
        ∑ i : Fin a, ∑ j : Fin b, |A i j| ^ (2 : ℝ) := Real.sq_sqrt hnonneg
    _ = _ := by simp [sq_abs]

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

lemma norm_matrixCLM_apply_le {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (w : EuclideanSpace ℝ (Fin b)) : ‖matrixCLM M w‖ ≤ ‖M‖ * ‖w‖ := by
  rw [matrixCLM_apply]; exact mulVec_frobenius_norm_le M w

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

end NTK

end
