/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianMatrix
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import LeanMachineLearning.Optimization.NTK.Initialization.Setup

/-!
# Gaussian Matrix Algebra: Moments, Joint Gaussianity and Independence of Linear Images

Facts about a standard Gaussian weight matrix `W ~ 𝒩(0,1)^{n×p}` that build on the architecture-
independent matrix algebra of `ForMathlib/Probability/Moments/GaussianMatrix.lean` (coordinate
moments, linear forms, joint Gaussianity); they complement the Gaussian *vector* algebra of
`Initialization/GaussianAlgebra.lean`.

1. **Bilinear Gaussian quadratic forms**: `integral_gaussianMatrix_quadForm`
   (`E[u ⬝ᵥ (W A Wᵀ) v] = (u ⬝ᵥ v) tr A`) and its normalized form
   `backward_empirical_quadForm_asymptotic_limit`.
2. **Linear images**: `integral_mul_entry_mul_mul_entry`
   (`E[(W A)_{ik} (W B)_{jl}] = δ_{ij} (Aᵀ B)_{kl}`) and
   `indepFun_gaussianInit_mul_of_transpose_mul_eq_zero` (`Aᵀ B = 0 → W A ⟂ W B`).
3. **One-sided conditioning (Lemma 2.26)**: for an orthogonal projector `P`, `W P ⟂ W Pᗮ`
   (`indepFun_gaussian_orthogonal_projection`), hence `W X ⟂ W Pᗮ` whenever `P X = X`
   (`indepFun_conditioned_weight_history`).

The deep-NTK application (backward sensitivities and Theorem 2.27) is in
`Deep/GaussianDecoupling.lean`.
-/

@[expose]
public section

open scoped Matrix Real BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix

namespace NTK

variable {n p q : ℕ}

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The `k`-th coordinate of `Wᵀ u` is the linear form `u ⬝ᵥ (W e_k)` of the matrix `W`. -/
lemma mulVec_transpose_apply_eq_dotProduct [DecidableEq κ] (W : ι → κ → ℝ) (u : ι → ℝ) (k : κ) :
    ((Matrix.of W)ᵀ *ᵥ u) k = u ⬝ᵥ (Matrix.of W *ᵥ Pi.single k 1) := by
  simp [mulVec, dotProduct, Pi.single_apply, mul_comm]

/-- Expectation of coordinate products of transpose vector multiplications:
`∫ (Wᵀ *ᵥ u) k * (Wᵀ *ᵥ v) l ∂(𝒩(0,1)^{ι×κ}) = if k = l then u ⬝ᵥ v else 0`.  This is the
bilinear covariance `integral_gaussianMatrix_bilinear_mul_bilinear` at the unit vectors `e_k`,
`e_l`. -/
lemma integral_mulVec_transpose_mul_apply [DecidableEq κ] (u v : ι → ℝ) (k l : κ) :
    ∫ W : ι → κ → ℝ, ((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l ∂(Measure.pi fun _ :
        ι => Measure.pi fun _ : κ => gaussianReal 0 1) =
      if k = l then u ⬝ᵥ v else 0 := by
  simp_rw [mulVec_transpose_apply_eq_dotProduct]
  rw [integral_gaussianMatrix_bilinear_mul_bilinear]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl, dotProduct_single]

/-- Integrability of coordinate products of transpose vector multiplications. -/
lemma integrable_mulVec_transpose_mul_apply (u v : ι → ℝ) (k l : κ) :
    Integrable (fun W : ι → κ → ℝ => ((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) := by
  classical
  simp_rw [mulVec_transpose_apply_eq_dotProduct]
  exact (memLp_linearForm_gaussianInit u _).integrable_mul (memLp_linearForm_gaussianInit v _)

/-- Expectation of the general bilinear Gaussian quadratic form (Proposition 2.27 Step 4):
`∫ u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) ∂(𝒩(0,1)^{ι×κ}) = (u ⬝ᵥ v) * A.trace`
for arbitrary real matrix `A ∈ ℝ^{κ × κ}` and vectors `u, v ∈ ℝ^ι`. -/
theorem integral_gaussianMatrix_quadForm (u v : ι → ℝ) (A : Matrix κ κ ℝ) :
    ∫ W : ι → κ → ℝ, u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v) ∂(Measure.pi fun _ :
        ι => Measure.pi fun _ : κ => gaussianReal 0 1) =
      (u ⬝ᵥ v) * A.trace := by
  classical
  have h_quad : ∀ W : ι → κ → ℝ, u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v) =
      ∑ k, ∑ l, A k l * (((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l) := fun W => by
    rw [quadForm_mul_mul_transpose (Matrix.of W) A u v]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring_nf
  have h_inner : ∀ k : κ, ∫ W : ι → κ → ℝ, ∑ l, A k l * (((Matrix.of W)ᵀ *ᵥ u) k *
        ((Matrix.of W)ᵀ *ᵥ v) l) ∂(Measure.pi fun _ : ι =>
          Measure.pi fun _ : κ => gaussianReal 0 1) = A k k * (u ⬝ᵥ v) := fun k => by
    rw [integral_finsetSum _ fun l _ =>
      (integrable_mulVec_transpose_mul_apply u v k l).const_mul (A k l)]
    rw [Finset.sum_eq_single k]
    · rw [integral_const_mul, integral_mulVec_transpose_mul_apply]
      simp
    · intro l _ hl
      rw [integral_const_mul, integral_mulVec_transpose_mul_apply]
      simp [Ne.symm hl]
    · exact fun h => absurd (Finset.mem_univ k) h
  simp_rw [h_quad]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrable_mulVec_transpose_mul_apply u v k l).const_mul (A k l)]
  rw [Finset.sum_congr rfl fun k _ => h_inner k, Matrix.trace, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.diag_apply, mul_comm]

/-- Normalized asymptotic form of the bilinear Gaussian expectation (Proposition 2.27 Step 4):
`(1/n²) ∫ u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) = (1/n u ⬝ᵥ v) * (1/n A.trace)`. -/
theorem backward_empirical_quadForm_asymptotic_limit (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
      ∫ W : Fin n → Fin p → ℝ,
        u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v) ∂(Measure.pi fun _ : Fin n => Measure.pi
            fun _ : Fin p => gaussianReal 0 1) =
      ((n : ℝ)⁻¹ * (u ⬝ᵥ v)) * ((n : ℝ)⁻¹ * A.trace) := by
  rw [integral_gaussianMatrix_quadForm]
  ring

/-! ### Linear Images of a Gaussian Matrix: Moments and Independence -/

variable {r : ℕ}

/-- Entries of a right-multiplied weight matrix as an explicit sum:
`(W A)_{ik} = ∑ a, A_{ak} W_{ia}`. -/
lemma matrix_mul_apply_eq_sum (W : Fin n → Fin p → ℝ) (A : Matrix (Fin p) (Fin q) ℝ)
    (i : Fin n) (k : Fin q) :
    (Matrix.of W * A) i k = ∑ a : Fin p, A a k * W i a := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- Each entry of `W A` is in `L²` for `W` a standard Gaussian matrix and `A` a fixed matrix. -/
lemma memLp_mul_entry (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) (k : Fin q) :
    MemLp (fun W : Fin n → Fin p → ℝ => (Matrix.of W * A) i k) 2 (Measure.pi fun _ : Fin n =>
        Measure.pi fun _ : Fin p => gaussianReal 0 1) := by
  simp_rw [matrix_mul_apply_eq_sum]
  exact memLp_finsetSum _ fun a _ => (memLp_entry i a).const_mul _

/-- Zero mean of the entries of `W * A`. -/
lemma integral_mul_entry (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) (k : Fin q) :
    ∫ W : Fin n → Fin p → ℝ, (Matrix.of W * A) i k ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ :
        Fin p => gaussianReal 0 1) = 0 := by
  simp_rw [matrix_mul_apply_eq_sum]
  rw [integral_finsetSum _ fun a _ => ((memLp_entry i a).integrable (by norm_num)).const_mul _]
  simp [integral_const_mul, integral_gaussianInit_entry]

/-- Second moments of two linear images `W * A`, `W * B` of a standard Gaussian matrix:
`E[(W A)_{ik} (W B)_{jl}] = δ_{ij} (Aᵀ B)_{kl}`. -/
lemma integral_mul_entry_mul_mul_entry (A : Matrix (Fin p) (Fin q) ℝ)
    (B : Matrix (Fin p) (Fin r) ℝ) (i j : Fin n) (k : Fin q) (l : Fin r) :
    ∫ W : Fin n → Fin p → ℝ, (Matrix.of W * A) i k * (Matrix.of W * B) j l ∂(Measure.pi fun _ : Fin
        n => Measure.pi fun _ : Fin p => gaussianReal 0 1) =
      if i = j then (Aᵀ * B) k l else 0 := by
  have h_eq : (fun W : Fin n → Fin p → ℝ => (Matrix.of W * A) i k * (Matrix.of W * B) j l) =
      fun W => ∑ a : Fin p, ∑ b : Fin p, (A a k * B b l) * (W i a * W j b) := by
    ext W
    rw [matrix_mul_apply_eq_sum, matrix_mul_apply_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h_eq, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_entry_mul_entry i j a b).const_mul _]
  have h_inner : ∀ a : Fin p,
      ∫ W : Fin n → Fin p → ℝ, ∑ b : Fin p, (A a k * B b l) * (W i a * W j b) ∂(Measure.pi fun _ :
          Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) =
        ∑ b : Fin p, (A a k * B b l) * (if i = j ∧ a = b then 1 else 0) := by
    intro a
    rw [integral_finsetSum _ fun b _ => (integrable_entry_mul_entry i j a b).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_gaussianInit_entry_mul_entry]
  simp_rw [h_inner]
  by_cases hij : i = j
  · simp [hij, Matrix.mul_apply, Matrix.transpose_apply]
  · simp [hij]

/-- **Uncorrelated linear images of a Gaussian matrix are independent.** If `Aᵀ B = 0` then
`W * A` and `W * B` are independent under `W ~ 𝒩(0,1)^{n×p}`. -/
theorem indepFun_gaussianInit_mul_of_transpose_mul_eq_zero
    (A : Matrix (Fin p) (Fin q) ℝ) (B : Matrix (Fin p) (Fin r) ℝ) (hAB : Aᵀ * B = 0) :
    IndepFun (fun W : Fin n → Fin p → ℝ => Matrix.of W * A)
      (fun W : Fin n → Fin p → ℝ => Matrix.of W * B) (Measure.pi fun _ : Fin n => Measure.pi fun _ :
          Fin p => gaussianReal 0 1) := by
  let X : Fin n × Fin q → (Fin n → Fin p → ℝ) → ℝ := fun ik W => (Matrix.of W * A) ik.1 ik.2
  let Y : Fin n × Fin r → (Fin n → Fin p → ℝ) → ℝ := fun jl W => (Matrix.of W * B) jl.1 jl.2
  -- the joint law of `(W A, W B)` is Gaussian, being a linear image of `W`
  have hjoint : HasGaussianLaw (fun W : Fin n → Fin p → ℝ => (fun ik => X ik W, fun jl => Y jl W))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) :=
    (hasGaussianLaw_gaussianInit_id (ι := Fin n) (κ := Fin p)).map_fun
      (LinearMap.toContinuousLinearMap (LinearMap.prod
        ((LinearEquiv.curry ℝ ℝ (Fin n) (Fin q)).symm.toLinearMap ∘ₗ
          mulRightLinearMap (Fin n) ℝ A)
        ((LinearEquiv.curry ℝ ℝ (Fin n) (Fin r)).symm.toLinearMap ∘ₗ
          mulRightLinearMap (Fin n) ℝ B)))
  have hcov : ∀ ik jl, cov[X ik, Y jl; (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p =>
      gaussianReal 0 1)] = 0 := by
    intro ik jl
    have := hjoint.isProbabilityMeasure
    rw [covariance_eq_sub (memLp_mul_entry A _ _) (memLp_mul_entry B _ _)]
    have h1 : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)[X
        ik] = 0 := integral_mul_entry A ik.1 ik.2
    have h2 : (X ik * Y jl : (Fin n → Fin p → ℝ) → ℝ) = fun W => X ik W * Y jl W := rfl
    rw [h1, zero_mul, sub_zero, h2]
    change ∫ W, (Matrix.of W * A) ik.1 ik.2 * (Matrix.of W * B) jl.1 jl.2 ∂(Measure.pi fun _ : Fin n
        => Measure.pi fun _ : Fin p => gaussianReal 0 1) = 0
    rw [integral_mul_entry_mul_mul_entry, hAB]
    simp
  have h_indep := HasGaussianLaw.indepFun_of_covariance_eval hjoint hcov
  have hmA : Measurable (fun f : Fin n × Fin q → ℝ =>
      (Matrix.of fun i k => f (i, k) : Matrix (Fin n) (Fin q) ℝ)) :=
    Measurable.of_eval fun i => Measurable.of_eval fun k => measurable_pi_apply (i, k)
  have hmB : Measurable (fun f : Fin n × Fin r → ℝ =>
      (Matrix.of fun i k => f (i, k) : Matrix (Fin n) (Fin r) ℝ)) :=
    Measurable.of_eval fun i => Measurable.of_eval fun k => measurable_pi_apply (i, k)
  exact h_indep.comp hmA hmB

/-! ### Lemma 2.26 One-Sided Gaussian Conditioning -/

/-- **Lemma 2.26 (One-Sided Gaussian Conditioning / Decoupling Identity)**:
Let `W ~ 𝒩(0,1)^{n×p}` and let `P ∈ ℝ^{p × p}` be an orthogonal projection onto the subspace
spanned by forward post-activations. Then the projected component `W * P` and the complementary
residual `W * Pᗮ` are statistically independent. -/
theorem indepFun_gaussian_orthogonal_projection (n p : ℕ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : IsStarProjection P) :
    IndepFun (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * P)
      (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * (1 - P))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) := by
  have hAB : Pᵀ * (1 - P) = 0 := by
    rw [hP.transpose_eq]; exact mul_self_orthogonalComplement P hP
  exact indepFun_gaussianInit_mul_of_transpose_mul_eq_zero P (1 - P) hAB

/-- Conditioning identity on the forward activation history:
When `P * X = X`, the forward outputs `W * X` and the residual `W * Pᗮ` are independent. -/
theorem indepFun_conditioned_weight_history (n p q : ℕ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : IsStarProjection P) (X : Matrix (Fin p) (Fin q) ℝ) (hX : P * X = X) :
    IndepFun (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * X)
      (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * (1 - P))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) := by
  have h_indep := indepFun_gaussian_orthogonal_projection n p P hP
  have h_meas_mul : Measurable (fun M : Matrix (Fin n) (Fin p) ℝ => M * X) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp (measurable_pi_apply i)).mul_const _
  have h_eq : (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * X) =
      (fun M : Matrix (Fin n) (Fin p) ℝ => M * X) ∘
        (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * P) := by
    funext W
    simp only [Function.comp_apply]
    exact orthogonalDecomposition_mul (Matrix.of W) P X hX
  rw [h_eq]
  exact h_indep.comp h_meas_mul measurable_id

end NTK

end
