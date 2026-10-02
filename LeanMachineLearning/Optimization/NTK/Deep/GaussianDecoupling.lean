/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Independence.Integration
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
  sorry

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
      (fun n : ℕ => fun (W, w_out) =>
        deepEmpiricalNTK d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n W w_out) α β)
      Filter.atTop
      (fun _ =>
        deepLimitingNTK d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) α β) := by
  sorry

end NTK

end
