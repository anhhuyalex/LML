/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import LeanMachineLearning.Optimization.NTK.Deep.Architecture
public import LeanMachineLearning.Optimization.NTK.Deep.LayerwiseNTK
public import LeanMachineLearning.Optimization.NTK.Deep.LimitingNTK
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Foundations.Concentration
public import LeanMachineLearning.Optimization.NTK.Initialization.Setup
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianAlgebra
public import LeanMachineLearning.Optimization.NTK.Initialization.CovariancePropagation
public import LeanMachineLearning.Optimization.NTK.Initialization.DeepNNGPTheorems

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
open MeasureTheory ProbabilityTheory Matrix

namespace NTK

variable {n p q : ℕ}

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

/-- Every single coordinate of a standard Gaussian matrix is square-integrable (in `L²`). -/
lemma memLp_entry (n p : ℕ) (i : Fin n) (l : Fin p) :
    MemLp (fun W : Fin n → Fin p → ℝ => W i l) 2 (gaussianInit n p) := by
  have h_base : MemLp id (2 : ENNReal) (gaussianReal 0 1) := memLp_id_gaussianReal (2 : NNReal)
  have h_pres_l : MeasurePreserving (fun a : Fin p → ℝ => a l)
      (gaussianRowMeasure p) (gaussianReal 0 1) :=
    measurePreserving_eval (fun _ : Fin p => gaussianReal 0 1) l
  have h_row : MemLp (fun a : Fin p → ℝ => a l) 2 (gaussianRowMeasure p) :=
    h_base.comp_measurePreserving h_pres_l
  have h_pres_i : MeasurePreserving (fun W : Fin n → Fin p → ℝ => W i)
      (gaussianInit n p) (gaussianRowMeasure p) :=
    measurePreserving_eval (fun _ : Fin n => gaussianRowMeasure p) i
  exact h_row.comp_measurePreserving h_pres_i

/-- Bilinear product of any two matrix coordinates `W i k * W j l` is integrable. -/
lemma integrable_entry_mul_entry (n p : ℕ) (i j : Fin n) (k l : Fin p) :
    Integrable (fun W : Fin n → Fin p → ℝ => W i k * W j l) (gaussianInit n p) := by
  have h1 := memLp_entry n p i k
  have h2 := memLp_entry n p j l
  exact h1.integrable_mul h2

/-- Exact coordinate covariance under the standard Gaussian matrix law:
`∫ W i k * W j l ∂(gaussianInit n p) = if i = j ∧ k = l then 1 else 0`. -/
theorem integral_gaussianInit_entry_mul_entry (n p : ℕ) (i j : Fin n) (k l : Fin p) :
    ∫ W : Fin n → Fin p → ℝ, W i k * W j l ∂(gaussianInit n p) =
      if i = j ∧ k = l then 1 else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    have h_sq : (fun W : Fin n → Fin p → ℝ => W i k * W i k) =
        fun W => (W i k) ^ 2 := by ext W; ring
    rw [h_sq, integral_gaussianInit_entry_sq]
  · by_cases hij : i = j
    · subst hij
      have hkl : k ≠ l := fun h_eq => h ⟨rfl, h_eq⟩
      have h_row : Measure.map (fun W : Fin n → Fin p → ℝ => W i) (gaussianInit n p) =
          gaussianRowMeasure p := map_gaussianInit_row i
      have h_meas_row : AEMeasurable (fun W : Fin n → Fin p → ℝ => W i) (gaussianInit n p) :=
        (measurable_pi_apply i).aemeasurable
      have h_fun_cont : Continuous (fun a : Fin p → ℝ => a k * a l) := by fun_prop
      have h_step : ∫ W : Fin n → Fin p → ℝ, W i k * W i l ∂(gaussianInit n p) =
          ∫ a : Fin p → ℝ, a k * a l ∂(gaussianRowMeasure p) := by
        rw [← integral_map h_meas_row h_fun_cont.aestronglyMeasurable, h_row]
      rw [h_step]
      have h_indep := (iIndepFun_readoutWeights p).indepFun hkl
      have h_meask : AEStronglyMeasurable (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) := by
        have hc : Continuous (fun a : Fin p → ℝ => a k) := by fun_prop
        exact hc.aestronglyMeasurable
      have h_measl : AEStronglyMeasurable (fun a : Fin p → ℝ => a l) (gaussianRowMeasure p) := by
        have hc : Continuous (fun a : Fin p → ℝ => a l) := by fun_prop
        exact hc.aestronglyMeasurable
      change (fun a => a k) ⟂ᵢ[gaussianRowMeasure p] (fun a => a l) at h_indep
      rw [h_indep.integral_fun_mul_eq_mul_integral h_meask h_measl]
      have h_coord_k : Measure.map (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) =
          gaussianReal 0 1 := map_gaussianReadoutMeasure_coord k
      have h_meas_k' : AEMeasurable (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) :=
        (measurable_pi_apply k).aemeasurable
      have hf_cont : Continuous (fun x : ℝ => x) := by fun_prop
      have h_int_k : ∫ a : Fin p → ℝ, a k ∂(gaussianRowMeasure p) =
          ∫ x : ℝ, x ∂(gaussianReal 0 1) := by
        rw [← integral_map h_meas_k' hf_cont.aestronglyMeasurable, h_coord_k]
      have h_zero : ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0 :=
        ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
      rw [h_int_k, h_zero, zero_mul]
    · have h_indep_row := (iIndepFun_inputWeights n p).indepFun hij
      have h_indep_entry := h_indep_row.comp (measurable_pi_apply k) (measurable_pi_apply l)
      have h_meas_ik : AEStronglyMeasurable (fun W : Fin n → Fin p → ℝ =>
          ((fun f => f k) ∘ fun W => W i) W) (gaussianInit n p) := by
        have hc : Continuous (fun W : Fin n → Fin p → ℝ => W i k) := by fun_prop
        exact hc.aestronglyMeasurable
      have h_meas_jl : AEStronglyMeasurable (fun W : Fin n → Fin p → ℝ =>
          ((fun f => f l) ∘ fun W => W j) W) (gaussianInit n p) := by
        have hc : Continuous (fun W : Fin n → Fin p → ℝ => W j l) := by fun_prop
        exact hc.aestronglyMeasurable
      have h_step : (fun W : Fin n → Fin p → ℝ => W i k * W j l) =
          (fun W => ((fun f => f k) ∘ fun W => W i) W * ((fun f => f l) ∘ fun W => W j) W) := rfl
      rw [h_step, h_indep_entry.integral_fun_mul_eq_mul_integral h_meas_ik h_meas_jl]
      change (∫ W, W i k ∂(gaussianInit n p)) * (∫ W, W j l ∂(gaussianInit n p)) = 0
      rw [integral_gaussianInit_entry n p i k, zero_mul]

/-- Matrix quadratic form algebraic reorganization via transpose vector multiplication:
`u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) = (Wᵀ *ᵥ u) ⬝ᵥ (A *ᵥ (Wᵀ *ᵥ v))`. -/
lemma quadForm_eq_dotProduct_mulVec (n p : ℕ) (W : Matrix (Fin n) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (u v : Fin n → ℝ) :
    u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) = (Wᵀ *ᵥ u) ⬝ᵥ (A *ᵥ (Wᵀ *ᵥ v)) := by
  have h1 : (W * A * Wᵀ) *ᵥ v = W *ᵥ (A *ᵥ (Wᵀ *ᵥ v)) := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [h1, dotProduct_mulVec, ← mulVec_transpose W u]

/-- Expectation of coordinate products of transpose vector multiplications:
`∫ (Wᵀ *ᵥ u) k * (Wᵀ *ᵥ v) l ∂(gaussianInit n p) = if k = l then u ⬝ᵥ v else 0`. -/
lemma integral_mulVec_transpose_mul_apply (n p : ℕ) (u v : Fin n → ℝ) (k l : Fin p) :
    ∫ W : Fin n → Fin p → ℝ, ((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l ∂(gaussianInit n p) =
      if k = l then u ⬝ᵥ v else 0 := by
  have h_eq : (fun W : Fin n → Fin p → ℝ => ((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l) =
      fun W => ∑ i : Fin n, ∑ j : Fin n, u i * v j * (W i k * W j l) := by
    ext W
    have h_u : ((Matrix.of W)ᵀ *ᵥ u) k = ∑ i : Fin n, u i * W i k := by
      simp only [mulVec, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h_v : ((Matrix.of W)ᵀ *ᵥ v) l = ∑ j : Fin n, v j * W j l := by
      simp only [mulVec, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h_u, h_v]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h_eq]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ =>
      (integrable_entry_mul_entry n p i j k l).const_mul (u i * v j))]
  have h_inner : ∀ (i : Fin n),
      (∫ W : Fin n → Fin p → ℝ, ∑ j : Fin n, u i * v j * (W i k * W j l) ∂(gaussianInit n p)) =
      ∑ j : Fin n, u i * v j * (if i = j ∧ k = l then 1 else 0) := by
    intro i
    rw [integral_finsetSum _ fun j _ =>
      (integrable_entry_mul_entry n p i j k l).const_mul (u i * v j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_gaussianInit_entry_mul_entry]
  simp_rw [h_inner]
  split_ifs with hkl
  · subst hkl
    simp only [eq_self, and_true]
    have heq : ∀ (i : Fin n), (∑ j : Fin n, u i * v j * (if i = j then (1 : ℝ) else 0)) =
        u i * v i := by
      intro i
      have heq2 : (fun j => u i * v j * (if i = j then (1 : ℝ) else 0)) =
          fun j => if i = j then u i * v j else 0 := by
        ext j; split_ifs with hij
        · subst hij; ring
        · ring
      rw [heq2]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp_rw [heq]
    rfl
  · have h_ite : ∀ (i j : Fin n), (if i = j ∧ k = l then (1 : ℝ) else 0) = 0 := by
      intro i j; simp [hkl]
    simp_rw [h_ite, mul_zero, Finset.sum_const_zero]

/-- Integrability of coordinate products of transpose vector multiplications. -/
lemma integrable_mulVec_transpose_mul_apply (n p : ℕ) (u v : Fin n → ℝ) (k l : Fin p) :
    Integrable (fun W : Fin n → Fin p → ℝ => ((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l)
      (gaussianInit n p) := by
  have h_eq : (fun W : Fin n → Fin p → ℝ => ((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l) =
      fun W => ∑ i : Fin n, ∑ j : Fin n, u i * v j * (W i k * W j l) := by
    ext W
    have h_u : ((Matrix.of W)ᵀ *ᵥ u) k = ∑ i : Fin n, u i * W i k := by
      simp only [mulVec, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h_v : ((Matrix.of W)ᵀ *ᵥ v) l = ∑ j : Fin n, v j * W j l := by
      simp only [mulVec, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h_u, h_v]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h_eq]
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ =>
      (integrable_entry_mul_entry n p i j k l).const_mul (u i * v j)

/-- Expectation of the general bilinear Gaussian quadratic form (Proposition 2.27 Step 4):
`∫ u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) ∂(gaussianInit n p) = (u ⬝ᵥ v) * A.trace`
for arbitrary real matrix `A ∈ ℝ^{p × p}` and vectors `u, v ∈ ℝ^n`. -/
theorem integral_gaussianMatrix_quadForm (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ∫ W : Fin n → Fin p → ℝ, u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v) ∂(gaussianInit n p) =
      (u ⬝ᵥ v) * A.trace := by
  have h_quad : (fun W : Fin n → Fin p → ℝ => u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v)) =
      fun W => ∑ k : Fin p, ∑ l : Fin p,
        A k l * (((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l) := by
    ext W
    rw [quadForm_eq_dotProduct_mulVec n p (Matrix.of W) A u v]
    simp only [dotProduct, mulVec]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring_nf
  rw [h_quad]
  rw [integral_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ =>
      (integrable_mulVec_transpose_mul_apply n p u v k l).const_mul (A k l)]
  have h_inner : ∀ (k : Fin p),
      (∫ W : Fin n → Fin p → ℝ, ∑ l : Fin p,
        A k l * (((Matrix.of W)ᵀ *ᵥ u) k * ((Matrix.of W)ᵀ *ᵥ v) l) ∂(gaussianInit n p)) =
      ∑ l : Fin p, A k l * (if k = l then u ⬝ᵥ v else 0) := by
    intro k
    rw [integral_finsetSum _ fun l _ =>
      (integrable_mulVec_transpose_mul_apply n p u v k l).const_mul (A k l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_mulVec_transpose_mul_apply]
  simp_rw [h_inner]
  have h_diag : ∀ (k : Fin p),
      (∑ l : Fin p, A k l * (if k = l then u ⬝ᵥ v else 0)) = A k k * (u ⬝ᵥ v) := by
    intro k
    have heq : (fun l => A k l * (if k = l then u ⬝ᵥ v else 0)) =
        fun l => if k = l then A k l * (u ⬝ᵥ v) else 0 := by
      ext l; split_ifs with hkl
      · subst hkl; ring
      · ring
    rw [heq]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp_rw [h_diag]
  rw [← Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag_apply]
  ring

/-- Normalized asymptotic form of the bilinear Gaussian expectation (Proposition 2.27 Step 4):
`(1/n²) ∫ u ⬝ᵥ ((W * A * Wᵀ) *ᵥ v) = (1/n u ⬝ᵥ v) * (1/n A.trace)`. -/
theorem backward_empirical_quadForm_asymptotic_limit (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
      ∫ W : Fin n → Fin p → ℝ,
        u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v) ∂(gaussianInit n p) =
      ((n : ℝ)⁻¹ * (u ⬝ᵥ v)) * ((n : ℝ)⁻¹ * A.trace) := by
  rw [integral_gaussianMatrix_quadForm]
  ring

/-! ### Joint Gaussianity of the Weight Matrix -/

/-- A standard Gaussian row `a ~ gaussianRowMeasure p` is a jointly Gaussian vector: its coordinates
are independent standard Gaussians (`iIndepFun.hasGaussianLaw`). -/
lemma hasGaussianLaw_gaussianRowMeasure_id (p : ℕ) :
    HasGaussianLaw (fun a : Fin p → ℝ => a) (gaussianRowMeasure p) := by
  have h1 : ∀ k : Fin p, HasGaussianLaw (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) := by
    intro k
    have hk : Measure.map (fun a : Fin p → ℝ => a k) (gaussianRowMeasure p) = gaussianReal 0 1 :=
      map_gaussianReadoutMeasure_coord k
    have : IsGaussian ((gaussianRowMeasure p).map (fun a : Fin p → ℝ => a k)) := by
      rw [hk]; infer_instance
    exact IsGaussian.hasGaussianLaw (measurable_pi_apply k).aemeasurable
  exact iIndepFun.hasGaussianLaw h1 (iIndepFun_readoutWeights p)

/-- The whole weight matrix `W ~ gaussianInit n p` is a jointly Gaussian vector: its rows are
independent Gaussian vectors. Every linear image `W ↦ (W A, W B)` is therefore jointly Gaussian. -/
lemma hasGaussianLaw_gaussianInit_id (n p : ℕ) :
    HasGaussianLaw (fun W : Fin n → Fin p → ℝ => W) (gaussianInit n p) := by
  have h1 : ∀ i : Fin n, HasGaussianLaw (fun W : Fin n → Fin p → ℝ => W i) (gaussianInit n p) := by
    intro i
    have : IsGaussian ((gaussianInit n p).map (fun W : Fin n → Fin p → ℝ => W i)) := by
      rw [map_gaussianInit_row i]
      have := (hasGaussianLaw_gaussianRowMeasure_id p).isGaussian_map
      simpa using this
    exact IsGaussian.hasGaussianLaw (measurable_pi_apply i).aemeasurable
  exact iIndepFun.hasGaussianLaw h1 (iIndepFun_inputWeights n p)

/-! ### Linear Images of a Gaussian Matrix: Moments and Independence -/

variable {r : ℕ}

/-- Entries of a right-multiplied weight matrix as an explicit sum:
`(W A)_{ik} = ∑ a, A_{ak} W_{ia}`. -/
lemma matrix_mul_apply_eq_sum (W : Fin n → Fin p → ℝ) (A : Matrix (Fin p) (Fin q) ℝ)
    (i : Fin n) (k : Fin q) :
    (Matrix.of W * A) i k = ∑ a : Fin p, A a k * W i a := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The linear map `W ↦ (W * A)` on weight matrices, with the entries of the product indexed by
pairs. -/
def mulRightLinear (A : Matrix (Fin p) (Fin q) ℝ) :
    (Fin n → Fin p → ℝ) →ₗ[ℝ] (Fin n × Fin q → ℝ) where
  toFun W ik := (Matrix.of W * A) ik.1 ik.2
  map_add' W V := by
    ext ik
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c W := by
    ext ik; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

lemma memLp_mul_entry (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) (k : Fin q) :
    MemLp (fun W : Fin n → Fin p → ℝ => (Matrix.of W * A) i k) 2 (gaussianInit n p) := by
  simp_rw [matrix_mul_apply_eq_sum]
  exact memLp_finsetSum _ fun a _ => (memLp_entry n p i a).const_mul _

/-- Zero mean of the entries of `W * A`. -/
lemma integral_mul_entry (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) (k : Fin q) :
    ∫ W : Fin n → Fin p → ℝ, (Matrix.of W * A) i k ∂(gaussianInit n p) = 0 := by
  simp_rw [matrix_mul_apply_eq_sum]
  rw [integral_finsetSum _ fun a _ => ((memLp_entry n p i a).integrable (by norm_num)).const_mul _]
  simp [integral_const_mul, integral_gaussianInit_entry]

/-- Second moments of two linear images `W * A`, `W * B` of a standard Gaussian matrix:
`E[(W A)_{ik} (W B)_{jl}] = δ_{ij} (Aᵀ B)_{kl}`. -/
lemma integral_mul_entry_mul_mul_entry (A : Matrix (Fin p) (Fin q) ℝ)
    (B : Matrix (Fin p) (Fin r) ℝ) (i j : Fin n) (k : Fin q) (l : Fin r) :
    ∫ W : Fin n → Fin p → ℝ, (Matrix.of W * A) i k * (Matrix.of W * B) j l ∂(gaussianInit n p) =
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
    (integrable_entry_mul_entry n p i j a b).const_mul _]
  have h_inner : ∀ a : Fin p,
      ∫ W : Fin n → Fin p → ℝ, ∑ b : Fin p, (A a k * B b l) * (W i a * W j b) ∂(gaussianInit n p) =
        ∑ b : Fin p, (A a k * B b l) * (if i = j ∧ a = b then 1 else 0) := by
    intro a
    rw [integral_finsetSum _ fun b _ => (integrable_entry_mul_entry n p i j a b).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_gaussianInit_entry_mul_entry]
  simp_rw [h_inner]
  by_cases hij : i = j
  · simp [hij, Matrix.mul_apply, Matrix.transpose_apply]
  · simp [hij]

/-- **Uncorrelated linear images of a Gaussian matrix are independent.** If `Aᵀ B = 0` then
`W * A` and `W * B` are independent under `W ~ gaussianInit n p`. -/
theorem indepFun_gaussianInit_mul_of_transpose_mul_eq_zero
    (A : Matrix (Fin p) (Fin q) ℝ) (B : Matrix (Fin p) (Fin r) ℝ) (hAB : Aᵀ * B = 0) :
    IndepFun (fun W : Fin n → Fin p → ℝ => Matrix.of W * A)
      (fun W : Fin n → Fin p → ℝ => Matrix.of W * B) (gaussianInit n p) := by
  let X : Fin n × Fin q → (Fin n → Fin p → ℝ) → ℝ := fun ik W => (Matrix.of W * A) ik.1 ik.2
  let Y : Fin n × Fin r → (Fin n → Fin p → ℝ) → ℝ := fun jl W => (Matrix.of W * B) jl.1 jl.2
  -- the joint law of `(W A, W B)` is Gaussian, being a linear image of `W`
  have hjoint : HasGaussianLaw (fun W : Fin n → Fin p → ℝ => (fun ik => X ik W, fun jl => Y jl W))
      (gaussianInit n p) :=
    (hasGaussianLaw_gaussianInit_id n p).map_fun
      (LinearMap.toContinuousLinearMap (LinearMap.prod (mulRightLinear A) (mulRightLinear B)))
  have hcov : ∀ ik jl, cov[X ik, Y jl; gaussianInit n p] = 0 := by
    intro ik jl
    have := hjoint.isProbabilityMeasure
    rw [covariance_eq_sub (memLp_mul_entry A _ _) (memLp_mul_entry B _ _)]
    have h1 : (gaussianInit n p)[X ik] = 0 := integral_mul_entry A ik.1 ik.2
    have h2 : (X ik * Y jl : (Fin n → Fin p → ℝ) → ℝ) = fun W => X ik W * Y jl W := rfl
    rw [h1, zero_mul, sub_zero, h2]
    change ∫ W, (Matrix.of W * A) ik.1 ik.2 * (Matrix.of W * B) jl.1 jl.2 ∂(gaussianInit n p) = 0
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
Let `W ~ gaussianInit n p` and let `P ∈ ℝ^{p × p}` be an orthogonal projection onto the subspace
spanned by forward post-activations. Then the projected component `W * P` and the complementary
residual `W * Pᗮ` are statistically independent. -/
theorem indepFun_gaussian_orthogonal_projection (n p : ℕ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) :
    IndepFun (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * P)
      (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * orthogonalComplement P)
      (gaussianInit n p) := by
  have hAB : Pᵀ * orthogonalComplement P = 0 := by
    rw [hP.1]; exact mul_self_orthogonalComplement P hP
  exact indepFun_gaussianInit_mul_of_transpose_mul_eq_zero P (orthogonalComplement P) hAB

/-- Conditioning identity on the forward activation history:
When `P * X = X`, the forward outputs `W * X` and the residual `W * Pᗮ` are independent. -/
theorem indepFun_conditioned_weight_history (n p q : ℕ) (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : isOrthogonalProjection P) (X : Matrix (Fin p) (Fin q) ℝ) (hX : P * X = X) :
    IndepFun (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * X)
      (fun W : Fin n → Fin p → ℝ => (Matrix.of W) * orthogonalComplement P)
      (gaussianInit n p) := by
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

/-! ### Theorem 2.27 Global Limiting Convergence -/

/-- **Deterministic assembly for Theorem 2.27.** Fix an entry `(α, β)`. If every non-trivial
layerwise
forward covariance `Φ_{k+1}^{(n)}` and backward covariance `G_k^{(n)}` converges in measure to its
deterministic limit `Σ^{k+1}` resp. `Π^k`, then the empirical NTK entry converges in measure to the
limiting NTK entry.

The two end layers need no hypothesis: `Φ_0^{(n)} = Σ^0` is the deterministic input Gram matrix and
`G_{d+1}^{(n)} = Π^d = 1` is the terminal condition. The proof is the exact layerwise decomposition
(Proposition 2.25) plus `tendstoInMeasure_sum_mul`, so it holds over an arbitrary measure and an
arbitrary random-parameter family `θ n : Ω → DeepMLPParams d n0 n`. -/
theorem deepEmpiricalNTK_entry_tendstoInMeasure_of_layerwise
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (d n0 m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : ∀ n : ℕ, Ω → DeepMLPParams d n0 n) (α β : Fin m)
    (hΦ : ∀ (k : ℕ) (hk : k < d),
      TendstoInMeasure μ
        (fun n ω => deepActivationGram d n0 n m φ X (θ n ω) ⟨k + 1, by omega⟩ α β)
        Filter.atTop
        (fun _ => layerCovarianceSeq 1 0 φ m
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1) α β))
    (hG : ∀ (k : ℕ) (hk : k < d),
      TendstoInMeasure μ
        (fun n ω => deepSensitivityGram d n0 n m φ φ' X (θ n ω) ⟨k, by omega⟩ α β)
        Filter.atTop
        (fun _ => deepLimitingSensitivityKernel d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ α β)) :
    TendstoInMeasure μ
      (fun n ω => deepEmpiricalNTK d n0 n m φ φ' X (θ n ω) α β) Filter.atTop
      (fun _ => deepLimitingNTK d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) α β) := by
  set Φ0 : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j) with hΦ0
  have hconst : ∀ c : ℝ, TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => c) Filter.atTop (fun _ => c) :=
    fun c ε hε => by simp [edist_self, hε.ne']
  have hG' : ∀ ℓ : Fin (d + 1), TendstoInMeasure μ
      (fun n ω => deepSensitivityGram d n0 n m φ φ' X (θ n ω) ℓ α β) Filter.atTop
      (fun _ => deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ α β) := by
    rintro ⟨l, hl⟩
    by_cases hld : l = d
    · subst hld
      simp only [deepSensitivityGram_terminal, deepLimitingSensitivityKernel_terminal,
        Matrix.of_apply]
      exact hconst 1
    · exact hG l (by omega)
  have hΦ' : ∀ ℓ : Fin (d + 1), TendstoInMeasure μ
      (fun n ω => deepActivationGram d n0 n m φ X (θ n ω) ℓ α β) Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m Φ0 ℓ.val α β) := by
    rintro ⟨l, hl⟩
    cases l with
    | zero =>
      simp only [deepActivationGram_zero, layerCovarianceSeq]
      exact hconst _
    | succ k => exact hΦ k (by omega)
  have := tendstoInMeasure_sum_mul (μ := μ)
    (a := fun (ℓ : Fin (d + 1)) (n : ℕ) (ω : Ω) =>
      deepSensitivityGram d n0 n m φ φ' X (θ n ω) ℓ α β)
    (b := fun (ℓ : Fin (d + 1)) (n : ℕ) (ω : Ω) =>
      deepActivationGram d n0 n m φ X (θ n ω) ℓ α β)
    hG' hΦ'
  simpa [deepEmpiricalNTK, deepLimitingNTK, Matrix.sum_apply, Matrix.hadamard_apply] using this


/-- **Forward covariance concentration for the finite-parameter network (entrywise).** Transport of
`deepEmpiricalCovariance_tendstoInMeasure` (stated over the `Fin d`-indexed weight population and
for `deepPreactivation`) to the product measure on `(W, w_out)` used for `DeepMLPParams.ofTensor`:
the restriction `W ↦ (W 0, …, W (d - 1))` is measure preserving, and preactivations up to layer `k`
only read `W 0, …, W k` (`deepPreactivation_congr_of_eqOn`). -/
theorem deepActivationGram_entry_tendstoInMeasure
    (d n0 m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (k : ℕ) (hk : k < d) (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepActivationGram d n0 n m φ X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k + 1, by omega⟩ α β)
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1) α β) := by
  have hν := deepEmpiricalCovariance_tendstoInMeasure n0 m d φ hφ_cont C hC p hp hφ_growth X k hk
  -- project to the `(α, β)` entry
  have hentry := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Matrix (Fin m) (Fin m) ℝ => M α β)
    hν (by exact ((continuous_apply β).comp (continuous_apply α)).continuousAt)
  have hT : MeasurePreserving
      (fun q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ) => fun i : Fin d => q.1 i.val)
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) :=
    (measurePreserving_prefixMap (Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) d).comp measurePreserving_fst
  have hmeas : ∀ n : ℕ, Measurable (fun w : Fin d → ℕ → ℕ → ℝ =>
      (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) k α j) *
        φ (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) k β j)) := by
    intro n
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact (hφ_cont.measurable.comp
      (measurable_deepPreactivation n0 m n d φ hφ_cont.measurable X k α j)).mul
      (hφ_cont.measurable.comp (measurable_deepPreactivation n0 m n d φ hφ_cont.measurable X k β j))
  have hcomp := tendstoInMeasure_comp_measurePreserving hentry hT hmeas measurable_const
  convert hcomp using 3
  · rename_i n q
    have hcongr : deepPreactivation n0 m n φ X q.1 k =
        deepPreactivation n0 m n φ X (fun k' => if h : k' < d then q.1 k' else 0) k :=
      deepPreactivation_congr_of_eqOn n0 m n φ X _ _ k fun r hr => by
        simp [show r < d by omega]
    rw [deepActivationGram_succ d n0 n m φ X _ k hk, Matrix.of_apply]
    simp only [dotProduct]
    rw [deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X q.1 q.2 k hk, hcongr]
  · rfl

/-- **Backward covariance concentration (the core of Theorem 2.27).** For `k < d` the empirical
backward Gram entry `G_k^{(n), αβ} = n⁻¹ ⟨g_k^α, g_k^β⟩` (`deepSensitivityGram`) converges in
measure to the limiting backward covariance `Π^k_{αβ}` (`deepLimitingSensitivityKernel`).

Informal proof (downward induction on `k`; source: the Deep NTK source text, "Layerwise Structural
Decomposition", and Lemma 2.26 of the plan):
* `k = d - 1`: `g_{d-1}^α = W_d ⊙ φ'(h_{d-1}^α)`, so
  `G_{d-1}^{αβ} = n⁻¹ ∑_j W_{d,j}² φ'(h^α_j) φ'(h^β_j)`.
  The readout `W_d` is independent of the hidden layers and standard Gaussian, so conditionally on
  the hidden layers this is an i.i.d. average whose mean is `Φ'^{(n)}_{d-1,αβ}` (the empirical
  derivative Gram `deepDerivativeGram`), with conditional variance `O(1/n)`. By the forward
  concentration of `h_{d-1}` and continuity of the derivative-kernel map this tends to
  `Σ̇^{d-1}_{αβ} = Π^{d-1}_{αβ}`.
* `k < d - 1`: `G_k^{αβ} = n⁻² (g_{k+1}^α)ᵀ W_k D^αD^β W_kᵀ g_{k+1}^β` with `D^αD^β =
  diag(φ'(h_k^α) φ'(h_k^β))`. Decompose `W_k = W_k P + W_k Pᗮ` where `P` projects onto the span
  of the `m` forward features `φ(h_k^α)` (`orthogonalDecomposition`). The forward pass uses only
  `W_k P` (`orthogonalDecomposition_mul`), while `W_k Pᗮ` is independent of it
  (`indepFun_conditioned_weight_history`). Replacing `W_k` by an independent copy in the residual
  part costs `O(m/n)` since `rank P ≤ m`. For the independent part the quadratic form has mean
  `(u ⬝ᵥ v) tr A` (`integral_gaussianMatrix_quadForm`, normalized in
  `backward_empirical_quadForm_asymptotic_limit`) and `O(1/n)` variance, giving the product
  `G_{k+1}^{αβ} · Φ'^{(n)}_{k,αβ}`. The induction hypothesis (`G_{k+1}^{(n)} → Π^{k+1}`), the
  forward concentration (`Φ'^{(n)}_k → Σ̇^k`) and `tendstoInMeasure_sum_mul` then yield
  `G_k^{αβ} → Σ̇^k_{αβ} Π^{k+1}_{αβ} = Π^k_{αβ}`. -/
theorem deepSensitivityGram_entry_tendstoInMeasure
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (k : ℕ) (hk : k < d) (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepSensitivityGram d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k, by omega⟩ α β)
      Filter.atTop
      (fun _ => deepLimitingSensitivityKernel d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ α β) := by
  sorry

/-- **Theorem 2.27 (Infinite-Width Convergence of the Deep Empirical NTK to the Limiting NTK)**:
For any depth `d ≥ 1`, input dimension `n0`, sample size `m`, continuous activation `φ` and its
derivative `φ'` with bounded polynomial growth, and input dataset `X`, the empirical Neural Tangent
Kernel Gram matrix `deepEmpiricalNTK` converges entrywise in probability / in measure to the
deterministic recursive limiting NTK `deepLimitingNTK` as network width `n → ∞`. -/
theorem deepEmpiricalNTK_tendstoInMeasure_deepLimitingNTK
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepEmpiricalNTK d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2) α β)
      Filter.atTop
      (fun _ =>
        deepLimitingNTK d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) α β) := by
  exact deepEmpiricalNTK_entry_tendstoInMeasure_of_layerwise d n0 m φ φ' X
    (fun n (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) => DeepMLPParams.ofTensor d n0 n q.1 q.2) α β
    (fun k hk => deepActivationGram_entry_tendstoInMeasure d n0 m φ hφ_cont C hC p hp
      hφ_growth X k hk α β)
    (fun k hk => deepSensitivityGram_entry_tendstoInMeasure d n0 m hd φ φ' hφ_cont hφ'_cont
      C hC p hp hφ_growth hφ'_growth X k hk α β)

end NTK

end
