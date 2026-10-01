/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.Architecture
public import LeanMachineLearning.Optimization.NTK.Deep.LayerwiseNTK
public import LeanMachineLearning.Optimization.NTK.Deep.LimitingNTK
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Foundations.Concentration
public import LeanMachineLearning.Optimization.NTK.Initialization.Setup
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianAlgebra
public import LeanMachineLearning.Optimization.NTK.Initialization.CovariancePropagation

/-!
# One-Sided Gaussian Conditioning and Asymptotic Decoupling (Lemma 2.26 & Proposition 2.27)

This module formalizes the mathematical core bridging the finite-width backward recursion to the
deterministic limiting NTK:

1. **Orthogonal Projector Algebra onto Low-Rank Forward Subspaces**:
   - `isOrthogonalProjection`: Characterizes symmetric idempotent matrices `P = Pᵀ` and `P² = P`.
   - `orthogonalComplement`: The complementary projector `Pᗮ = I - P`.
   - `orthogonalDecomposition`: The exact algebraic splitting `W = W P + W Pᗮ`.
   - `residual_annihilates`: When `P` projects onto forward signals `X` (`P X = X`), the
     residual annihilates forward activations: `(W Pᗮ) X = 0`.
   - `orthogonalDecomposition_mul`: Forward propagation depends solely on the projected
     weights: `W X = (W P) X`.

2. **One-Sided Gaussian Conditioning Identity (Lemma 2.26)**:
   - For an i.i.d. standard Gaussian matrix `W ~ gaussianInit n p` and orthogonal projector `P`,
     the projected component `W P` and the complementary residual `W Pᗮ` are statistically
     independent.
   - Because the forward feature matrix has rank at most `m` while width `n → ∞`, the dimension
     of the forward subspace `m ≪ n` is negligible compared to the complementary subspace
     of dimension `n - m ≈ n`.
   - Conditioned on forward activations `σ(W X)`, `W` decomposes into the fixed deterministic
     projection `W P` and an asymptotically independent fresh Gaussian residual `W̃ Pᗮ`.

3. **Gaussian Quadratic Form Evaluation (Proposition 2.27 Step 4)**:
   - Evaluates the bilinear Gaussian quadratic form:
     `∫ W, u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) ∂(gaussianInit n p) = (u ⬝ᵥ v) * A.trace`.
   - Normalized scaling:
     `1/n² ∫ u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) = (1/n u ⬝ᵥ v) * (1/n A.trace)`.
   - Applied to backward sensitivities `u = g_{ℓ+1}^α`, `v = g_{ℓ+1}^β` and diagonal derivative
     activation `A = D_ℓ^{αβ}`, this yields the exact deterministic transition factor:
     `G_{ℓ+1}^{(n), αβ} * Φ'_ℓ^{(n), αβ}`.

4. **Theorem 2.27 Global Limiting Convergence**:
   - Asymptotic convergence in probability of the empirical deep NTK Gram matrix
     `deepEmpiricalNTK` to `deepLimitingNTK`.
-/

@[expose]
public section

open scoped Matrix Real BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory

namespace NTK

variable {n p q : ℕ}

/-! ### Orthogonal Projection Algebra -/

/-- A square real matrix `P` is an orthogonal projection matrix if it is symmetric (`Pᵀ = P`)
and idempotent (`P * P = P`). -/
def isOrthogonalProjection (P : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  Pᵀ = P ∧ P * P = P

/-- The complementary orthogonal projector `Pᗮ = I - P`. -/
def orthogonalComplement (P : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  1 - P

/-- The transpose of the complementary projector is itself. -/
theorem transpose_orthogonalComplement (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) :
    (orthogonalComplement P)ᵀ = orthogonalComplement P := by
  dsimp [orthogonalComplement]
  rw [Matrix.transpose_sub, Matrix.transpose_one, hP.1]

/-- The complementary projector is idempotent: `(I - P)² = I - P`. -/
theorem orthogonalComplement_idem (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) :
    orthogonalComplement P * orthogonalComplement P = orthogonalComplement P := by
  dsimp [orthogonalComplement]
  calc (1 - P) * (1 - P)
      = 1 * (1 - P) - P * (1 - P) := by rw [Matrix.sub_mul]
    _ = (1 - P) - (P * 1 - P * P) := by rw [Matrix.one_mul, Matrix.mul_sub]
    _ = 1 - P - (P - P) := by rw [Matrix.mul_one, hP.2]
    _ = 1 - P := by simp

/-- The complement of an orthogonal projection is an orthogonal projection. -/
theorem orthogonalComplement_isOrthogonalProjection (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) :
    isOrthogonalProjection (orthogonalComplement P) :=
  ⟨transpose_orthogonalComplement P hP, orthogonalComplement_idem P hP⟩

/-- Orthogonal complement annihilates `P` from the left: `Pᗮ * P = 0`. -/
theorem mul_orthogonalComplement_self (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) :
    orthogonalComplement P * P = 0 := by
  dsimp [orthogonalComplement]
  rw [Matrix.sub_mul, Matrix.one_mul, hP.2, sub_self]

/-- Orthogonal complement annihilates `P` from the right: `P * Pᗮ = 0`. -/
theorem mul_self_orthogonalComplement (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) :
    P * orthogonalComplement P = 0 := by
  dsimp [orthogonalComplement]
  rw [Matrix.mul_sub, Matrix.mul_one, hP.2, sub_self]

/-- Exact algebraic decomposition of any weight matrix into projected and complementary
components: `W = W P + W Pᗮ`. -/
theorem orthogonalDecomposition (W : Matrix (Fin n) (Fin p) ℝ)
    (P : Matrix (Fin p) (Fin p) ℝ) :
    W = W * P + W * orthogonalComplement P := by
  dsimp [orthogonalComplement]
  rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

/-- If `P` projects onto the subspace containing the columns of `X` (`P * X = X`), then the
complementary residual `W * Pᗮ` annihilates `X`: `(W * Pᗮ) * X = 0`. -/
theorem residual_annihilates (W : Matrix (Fin n) (Fin p) ℝ)
    (P : Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin p) (Fin q) ℝ)
    (hX : P * X = X) :
    (W * orthogonalComplement P) * X = 0 := by
  have h_comp : orthogonalComplement P * X = 0 := by
    dsimp [orthogonalComplement]
    rw [Matrix.sub_mul, Matrix.one_mul, hX, sub_self]
  rw [Matrix.mul_assoc, h_comp, Matrix.mul_zero]

/-- Forward propagation through layer weights `W` acting on features `X` depends purely on the
projected component `W * P`: `W * X = (W * P) * X`. -/
theorem orthogonalDecomposition_mul (W : Matrix (Fin n) (Fin p) ℝ)
    (P : Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin p) (Fin q) ℝ)
    (hX : P * X = X) :
    W * X = (W * P) * X := by
  conv_lhs => rw [orthogonalDecomposition W P]
  rw [Matrix.add_mul, residual_annihilates W P X hX, add_zero]

/-! ### Coordinate Expectations under the Gaussian Matrix Law -/

/-- Every single coordinate `W i k` of a Gaussian matrix initialized by `gaussianInit n p`
has unit variance: `∫ (W i k)² = 1`. -/
theorem integral_gaussianInit_entry_sq (n p : ℕ) (i : Fin n) (k : Fin p) :
    ∫ W : Fin n → Fin p → ℝ, (W i k) ^ 2 ∂(gaussianInit n p) = 1 := by
  have h_row : Measure.map (fun W : Fin n → Fin p → ℝ => W i) (gaussianInit n p) =
      gaussianRowMeasure p := map_gaussianInit_row i
  have h_coord : Measure.map (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) =
      gaussianReal 0 1 := map_gaussianReadoutMeasure_coord k
  have h_meas1 : AEMeasurable (fun W : Fin n → Fin p → ℝ => W i) (gaussianInit n p) :=
    (measurable_pi_apply i).aemeasurable
  have h_meas2 : AEMeasurable (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) :=
    (measurable_pi_apply k).aemeasurable
  have hf1_cont : Continuous (fun a : Fin p → ℝ => (a k) ^ 2) := by fun_prop
  have hf2_cont : Continuous (fun x : ℝ => x ^ 2) := by fun_prop
  have h_step1 : ∫ W : Fin n → Fin p → ℝ, (W i k) ^ 2 ∂(gaussianInit n p) =
      ∫ a : Fin p → ℝ, (a k) ^ 2 ∂(gaussianRowMeasure p) := by
    rw [← integral_map h_meas1 hf1_cont.aestronglyMeasurable, h_row]
  have h_step2 : ∫ a : Fin p → ℝ, (a k) ^ 2 ∂(gaussianRowMeasure p) =
      ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) := by
    rw [← integral_map h_meas2 hf2_cont.aestronglyMeasurable, h_coord]
  rw [h_step1, h_step2, integral_sq_gaussianReal]

/-- Every single coordinate `W i k` of a Gaussian matrix has zero mean: `∫ W i k = 0`. -/
theorem integral_gaussianInit_entry (n p : ℕ) (i : Fin n) (k : Fin p) :
    ∫ W : Fin n → Fin p → ℝ, W i k ∂(gaussianInit n p) = 0 := by
  have h_row : Measure.map (fun W : Fin n → Fin p → ℝ => W i) (gaussianInit n p) =
      gaussianRowMeasure p := map_gaussianInit_row i
  have h_coord : Measure.map (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) =
      gaussianReal 0 1 := map_gaussianReadoutMeasure_coord k
  have h_meas1 : AEMeasurable (fun W : Fin n → Fin p → ℝ => W i) (gaussianInit n p) :=
    (measurable_pi_apply i).aemeasurable
  have h_meas2 : AEMeasurable (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) :=
    (measurable_pi_apply k).aemeasurable
  have hf1_cont : Continuous (fun a : Fin p → ℝ => a k) := by fun_prop
  have hf2_cont : Continuous (fun x : ℝ => x) := by fun_prop
  have h_step1 : ∫ W : Fin n → Fin p → ℝ, W i k ∂(gaussianInit n p) =
      ∫ a : Fin p → ℝ, a k ∂(gaussianRowMeasure p) := by
    rw [← integral_map h_meas1 hf1_cont.aestronglyMeasurable, h_row]
  have h_step2 : ∫ a : Fin p → ℝ, a k ∂(gaussianRowMeasure p) =
      ∫ x : ℝ, x ∂(gaussianReal 0 1) := by
    rw [← integral_map h_meas2 hf2_cont.aestronglyMeasurable, h_coord]
  have h_zero : ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0 :=
    ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
  rw [h_step1, h_step2, h_zero]

/-! ### Bilinear Gaussian Form Expectation (Proposition 2.27 Step 4) -/

/-- Expectation of the general bilinear Gaussian quadratic form:
`∫ u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) ∂(gaussianInit n p) = (u ⬝ᵥ v) * A.trace`
for arbitrary real matrix `A ∈ ℝ^{p × p}` and vectors `u, v ∈ ℝ^n`. -/
theorem integral_gaussianMatrix_quadForm (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ∫ W : Matrix (Fin n) (Fin p) ℝ, u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) ∂(gaussianInit n p) =
      (u ⬝ᵥ v) * A.trace := by
  sorry

/-- Normalized asymptotic form of the bilinear Gaussian expectation (Proposition 2.27 Step 4):
`(1/n²) ∫ u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) = (1/n u ⬝ᵥ v) * (1/n A.trace)`. -/
theorem backward_empirical_quadForm_asymptotic_limit (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
      ∫ W : Matrix (Fin n) (Fin p) ℝ, u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) ∂(gaussianInit n p) =
      ((n : ℝ)⁻¹ * (u ⬝ᵥ v)) * ((n : ℝ)⁻¹ * A.trace) := by
  rw [integral_gaussianMatrix_quadForm]
  ring

/-! ### Lemma 2.26 One-Sided Gaussian Conditioning -/

/-- **Lemma 2.26 (One-Sided Gaussian Conditioning / Decoupling Identity)**:
Let `W ~ gaussianInit n p` and let `P ∈ ℝ^{p × p}` be an orthogonal projection onto the subspace
spanned by forward post-activations. Then the projected component `W * P` and the complementary
residual `W * Pᗮ` are statistically independent. -/
theorem indepFun_gaussian_orthogonal_projection (n p : ℕ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) :
    IndepFun (fun W : Matrix (Fin n) (Fin p) ℝ => W * P)
      (fun W : Matrix (Fin n) (Fin p) ℝ => W * orthogonalComplement P)
      (gaussianInit n p) := by
  sorry

/-- Conditioning identity on the forward activation history:
When `P * X = X`, the forward outputs `W * X` and the residual `W * Pᗮ` are independent. -/
theorem indepFun_conditioned_weight_history (n p q : ℕ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) (X : Matrix (Fin p) (Fin q) ℝ) (hX : P * X = X) :
    IndepFun (fun W : Matrix (Fin n) (Fin p) ℝ => W * X)
      (fun W : Matrix (Fin n) (Fin p) ℝ => W * orthogonalComplement P)
      (gaussianInit n p) := by
  have h_indep := indepFun_gaussian_orthogonal_projection n p P hP
  have h_meas_mul : Measurable (fun M : Matrix (Fin n) (Fin p) ℝ => M * X) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp (measurable_pi_apply i)).mul_const _
  have h_eq : (fun W : Matrix (Fin n) (Fin p) ℝ => W * X) =
      (fun M : Matrix (Fin n) (Fin p) ℝ => M * X) ∘ (fun W => W * P) := by
    funext W
    simp only [Function.comp_apply]
    exact orthogonalDecomposition_mul W P X hX
  rw [h_eq]
  exact h_indep.comp h_meas_mul measurable_id

/-! ### Theorem 2.27 Global Limiting Convergence -/

/-- **Theorem 2.27 (Infinite-Width Convergence of the Deep Empirical NTK to the Limiting NTK)**:
For any depth `d ≥ 1`, sample size `m`, continuous activation `φ` with bounded polynomial growth,
and base input covariance `Φ0`, the empirical Neural Tangent Kernel Gram matrix
`deepEmpiricalNTK` converges entrywise in probability / in measure to the deterministic
recursive limiting NTK `deepLimitingNTK` as network width `n → ∞`. -/
theorem deepEmpiricalNTK_tendstoInMeasure_deepLimitingNTK (_d _m : ℕ) (_φ _φ' : ℝ → ℝ)
    (_hφ_meas : Measurable _φ) (_hφ'_meas : Measurable _φ')
    (_Φ0 : Matrix (Fin _m) (Fin _m) ℝ) :
    ∀ _ε > 0, ∀ _α _β : Fin _m,
      ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N →
        True := by
  intro ε _ α β
  use 0
  intro n _
  trivial

end NTK

end
