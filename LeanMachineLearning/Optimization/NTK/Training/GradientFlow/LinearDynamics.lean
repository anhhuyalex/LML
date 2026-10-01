/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.Convergence

/-!
# Gradient flow: closed-form linear dynamics

The closed-form output dynamics via the matrix exponential and the eigenmodes of the fixed-kernel
residual.

## Main results and proof outline

* `NTK.matrix_exp_smul_mulVec_of_eigenvector`, `NTK.inner_matrix_exp_mulVec_of_eigenvector`,
  `NTK.inner_eigenvectorBasis_matrix_exp_mulVec`, `NTK.matrix_exp_mulVec_eq_sum_eigenmodes`,
  `NTK.norm_sq_matrix_exp_mulVec_eq_sum`, `NTK.abs_inner_eigenvector_residual_sub_mode_le` :
  Phase 15 eigenmodes `⟪v_k, r(t)⟫ = exp(-λ_k t / m) ⟪v_k, r(0)⟫` of the frozen-kernel residual
  (Mathlib's `Matrix.IsHermitian.eigenvectorBasis`), Parseval energy, and the lazy-training
  comparison for the actual residual.
* `NTK.matrix_exp_residual_trajectory_zero` : Initial condition `r(0) = r₀`.
* `NTK.matrix_exp_output_trajectory_zero` : Initial condition `f(0) = f₀`.
* `NTK.matrix_exp_residual_eq_output_sub_y` : Residual relation `f(t) - y = r(t)`.
* `NTK.matrix_exp_residual_trajectory_hasDerivAt` : Residual ODE satisfaction
  via matrix exponential.
* `NTK.matrix_exp_output_trajectory_hasDerivAt` : Output ODE satisfaction via matrix exponential.
* `NTK.matrix_exp_residual_decay` : Exponential decay for explicit matrix exponential trajectory.
* `NTK.matrix_exp_loss_decay` : Exponential loss decay for explicit matrix exponential trajectory.

See
`LeanMachineLearning.Optimization.NTK.Training.GradientFlow`
for the overview of the whole development.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix Matrix.Norms.Frobenius Topology

namespace NTK

variable {ι : Type*} {d m P : ℕ}

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra

attribute [local instance 2000] instCompleteSpaceMatrix

/-! ### Closed-Form Linear Output Dynamics via Matrix Exponential -/

/-- Initial condition of the explicit matrix exponential residual trajectory:
  `exp(0) r₀ = r₀`. -/
theorem matrix_exp_residual_trajectory_zero
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) :
    (WithLp.toLp 2 ((NormedSpace.exp (-(0 * (m : ℝ)⁻¹) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m)) = r₀ := by
  simp

/-- Initial condition of the network prediction trajectory: `f(0) = f₀`. -/
theorem matrix_exp_output_trajectory_zero
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (y f₀ : EuclideanSpace ℝ (Fin m)) :
    y + (WithLp.toLp 2 ((NormedSpace.exp (-(0 * (m : ℝ)⁻¹) • K_inf)) *ᵥ (f₀ - y).ofLp) :
      EuclideanSpace ℝ (Fin m)) = f₀ := by
  simp

/-- Relationship between output and residual trajectories under the closed-form matrix exponential
solution: `f(t) - y = r(t)`. -/
theorem matrix_exp_residual_eq_output_sub_y
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (y f₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    let f_traj : EuclideanSpace ℝ (Fin m) :=
      y + WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp)
    let r_traj : EuclideanSpace ℝ (Fin m) :=
      WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp)
    f_traj - y = r_traj := by
  intro f_traj r_traj
  dsimp [f_traj, r_traj]
  abel

/-- Auxiliary lemma: evaluation of a constant continuous linear map preserves derivatives. -/
lemma hasDerivAt_clm_apply_const
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u : ℝ → E) (u' : E) (x : ℝ) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => L (u y)) (L u') x := by
  have hc : HasDerivAt (fun _ : ℝ => L) (0 : E →L[ℝ] F) x := hasDerivAt_const x L
  have h := hc.clm_apply hu
  simpa using h

/-- Continuous linear map realizing matrix-vector multiplication into `EuclideanSpace`. -/
noncomputable def toEuclideanVecCLM (v : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ →L[ℝ] (EuclideanSpace ℝ (Fin m)) :=
  { toLinearMap := {
      toFun := fun M => WithLp.toLp 2 (M *ᵥ v)
      map_add' := fun M N => by
        ext i
        simp [Matrix.add_mulVec]
      map_smul' := fun c M => by
        ext i
        simp [Matrix.smul_mulVec]
    }
    cont := by fun_prop }

private lemma exp_smul_eq (K_inf : Matrix (Fin m) (Fin m) ℝ) (u : ℝ) :
    u • (-(m : ℝ)⁻¹ • K_inf) = -(u / (m : ℝ)) • K_inf := by
  rw [smul_smul]
  congr 1
  ring

private lemma mat_vec_mul_assoc
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    ((-(m : ℝ)⁻¹ • K_inf) * M) *ᵥ v = -(m : ℝ)⁻¹ • (K_inf *ᵥ (M *ᵥ v)) := by
  rw [Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- The closed-form matrix exponential residual trajectory satisfies the linear autonomous ODE:
  `∂_t r(t) = - (1 / m) K_∞ r(t)`. -/
theorem matrix_exp_residual_trajectory_hasDerivAt
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt
      (fun s => (WithLp.toLp 2 ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp)))) t := by
  have h_exp := @hasDerivAt_exp_smul_const' ℝ (Matrix (Fin m) (Fin m) ℝ) _ _ _
    (instCompleteSpaceMatrix m) (-(m : ℝ)⁻¹ • K_inf) t
  have h_clm := hasDerivAt_clm_apply_const (toEuclideanVecCLM r₀.ofLp)
    (fun u => NormedSpace.exp (u • (-(m : ℝ)⁻¹ • K_inf)))
    ((-(m : ℝ)⁻¹ • K_inf) * NormedSpace.exp (t • (-(m : ℝ)⁻¹ • K_inf))) t h_exp
  change HasDerivAt
    (fun y => WithLp.toLp 2 (NormedSpace.exp (y • (-(m : ℝ)⁻¹ • K_inf)) *ᵥ r₀.ofLp))
    (WithLp.toLp 2 (((-(m : ℝ)⁻¹ • K_inf) *
      NormedSpace.exp (t • (-(m : ℝ)⁻¹ • K_inf))) *ᵥ r₀.ofLp)) t at h_clm
  simp_rw [exp_smul_eq K_inf] at h_clm
  rw [mat_vec_mul_assoc K_inf] at h_clm
  exact h_clm

/-- The closed-form network prediction trajectory satisfies the linear output ODE:
  `∂_t f(t) = - (1 / m) K_∞ (f(t) - y)`. -/
theorem matrix_exp_output_trajectory_hasDerivAt
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (y f₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt
      (fun s => y + (WithLp.toLp 2 ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp)))) t := by
  have h_res := matrix_exp_residual_trajectory_hasDerivAt K_inf (f₀ - y) t
  exact h_res.const_add y

/-- Exponential norm decay for the closed-form matrix exponential residual trajectory:
  `‖r(t)‖ ≤ ‖r₀‖ exp(- (lambda_min / m) t)`. -/
theorem matrix_exp_residual_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖(WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m))‖ ≤
      ‖r₀‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) := by
  have hr : ∀ s, HasDerivAt
      (fun u => (WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp)))) s :=
    fun s => matrix_exp_residual_trajectory_hasDerivAt K_inf r₀ s
  have h_decay := residual_norm_exponential_decay K_inf lambda_min h_rr
    (fun u => WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp))
    hr hm t ht
  have h0 : (WithLp.toLp 2 ((NormedSpace.exp (-(0 / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m)) = r₀ := by
    have h_zero : -(0 / (m : ℝ)) = -(0 * (m : ℝ)⁻¹) := by ring
    rw [h_zero]
    exact matrix_exp_residual_trajectory_zero K_inf r₀
  rw [h0] at h_decay
  exact h_decay

/-- Exponential loss decay for the closed-form matrix exponential trajectory:
  `(1 / 2m) ‖r(t)‖² ≤ ((1 / 2m) ‖r₀‖²) exp(- (2 lambda_min / m) t)`. -/
theorem matrix_exp_loss_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖(WithLp.toLp 2
      ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) : EuclideanSpace ℝ (Fin m))‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r₀‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have hr : ∀ s, HasDerivAt
      (fun u => (WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp)))) s :=
    fun s => matrix_exp_residual_trajectory_hasDerivAt K_inf r₀ s
  have h_decay := mse_loss_exponential_decay K_inf lambda_min h_rr
    (fun u => WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp))
    hr hm t ht
  have h0 : (WithLp.toLp 2 ((NormedSpace.exp (-(0 / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m)) = r₀ := by
    have h_zero : -(0 / (m : ℝ)) = -(0 * (m : ℝ)⁻¹) := by ring
    rw [h_zero]
    exact matrix_exp_residual_trajectory_zero K_inf r₀
  rw [h0] at h_decay
  exact h_decay

/-! ### Eigenmodes of the Fixed-Kernel Residual (Phase 15)

For a symmetric kernel `K` the closed-form residual `exp(-(t/m) K) r₀` decouples in the orthonormal
eigenbasis `v_k` of `K`: the coordinate `⟪v_k, r(t)⟫` decays as `exp(-λ_k t / m) ⟪v_k, r₀⟫`. The
statements use Mathlib's `Matrix.IsHermitian.eigenvectorBasis`; nothing about the spectral theorem
is reproved. -/

/-- The matrix exponential acts on an eigenvector by the scalar exponential:
`K v = λ v` implies `exp(s K) v = exp(s λ) v`. No symmetry is needed. -/
theorem matrix_exp_smul_mulVec_of_eigenvector (K : Matrix (Fin m) (Fin m) ℝ) (s : ℝ)
    {v : Fin m → ℝ} {lam : ℝ} (hv : K *ᵥ v = lam • v) :
    NormedSpace.exp (s • K) *ᵥ v = Real.exp (s * lam) • v := by
  have hpow : ∀ n : ℕ, (s • K) ^ n *ᵥ v = (s * lam) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, Matrix.smul_mulVec, hv,
        smul_smul, smul_smul]
      congr 1
      ring
  have hsum : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (s • K) ^ n)
      (NormedSpace.exp (s • K)) :=
    @NormedSpace.exp_series_hasSum_exp' ℝ (Matrix (Fin m) (Fin m) ℝ) _ _ _ _ _
      (instCompleteSpaceMatrix m) (s • K)
  have hsum' := (toEuclideanVecCLM v).hasSum hsum
  have hreal : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * (s * lam) ^ n) •
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m)))
      (Real.exp (s * lam) • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))) := by
    have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s * lam))
    have h2 := this.smul_const (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))
    simpa [Real.exp_eq_exp_ℝ, smul_eq_mul, mul_smul] using h2
  have hEq : (fun n : ℕ => (toEuclideanVecCLM v) ((n.factorial : ℝ)⁻¹ • (s • K) ^ n)) =
      fun n : ℕ => ((n.factorial : ℝ)⁻¹ * (s * lam) ^ n) •
        (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m)) := by
    funext n
    simp only [toEuclideanVecCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.smul_mulVec, hpow, smul_smul]
    ext i
    simp [mul_smul, mul_assoc]
  rw [hEq] at hsum'
  have h3 := congrArg WithLp.ofLp (hsum'.unique hreal)
  simpa [toEuclideanVecCLM] using h3

/-- For a symmetric matrix `K`, the exponential `exp(s K)` scales the coordinate of `r` along an
eigenvector `v` (`K v = λ v`) by `exp(s λ)`. -/
theorem inner_matrix_exp_mulVec_of_eigenvector {K : Matrix (Fin m) (Fin m) ℝ} (hK : Kᵀ = K)
    (s : ℝ) {v : Fin m → ℝ} {lam : ℝ} (hv : K *ᵥ v = lam • v) (r : EuclideanSpace ℝ (Fin m)) :
    ⟪(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m)),
        (matrixCLM (NormedSpace.exp (s • K)) r)⟫ =
      Real.exp (s * lam) * ⟪(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m)), r⟫ := by
  have hsymm : (NormedSpace.exp (s • K))ᵀ = NormedSpace.exp (s • K) := by
    apply Matrix.IsSymm.exp
    simp [Matrix.IsSymm, Matrix.transpose_smul, hK]
  have h1 := matrix_exp_smul_mulVec_of_eigenvector K s hv
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  conv_lhs => rw [← hsymm, Matrix.vecMul_transpose, h1]
  rw [smul_dotProduct, dotProduct_comm]
  rfl

/-- **Eigenmode coordinates of `exp(s K) r`.** For a Hermitian `K` with Mathlib's eigenbasis `v_k`
and eigenvalues `λ_k`, `⟪v_k, exp(s K) r⟫ = exp(s λ_k) ⟪v_k, r⟫`. With `s = -t / m` this is the
decoupled mode equation `r_k(t) = exp(-λ_k t / m) r_k(0)` of the frozen-kernel residual. -/
theorem inner_eigenvectorBasis_matrix_exp_mulVec {K : Matrix (Fin m) (Fin m) ℝ}
    (hK : K.IsHermitian) (s : ℝ) (r : EuclideanSpace ℝ (Fin m)) (k : Fin m) :
    ⟪hK.eigenvectorBasis k,
        (matrixCLM (NormedSpace.exp (s • K)) r)⟫ =
      Real.exp (s * hK.eigenvalues k) * ⟪hK.eigenvectorBasis k, r⟫ := by
  have hT : Kᵀ = K := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.eq
  exact inner_matrix_exp_mulVec_of_eigenvector hT s (hK.mulVec_eigenvectorBasis k) r

/-- **Spectral expansion of the frozen-kernel residual:**
`exp(s K) r = ∑_k exp(s λ_k) ⟪v_k, r⟫ v_k`. -/
theorem matrix_exp_mulVec_eq_sum_eigenmodes {K : Matrix (Fin m) (Fin m) ℝ}
    (hK : K.IsHermitian) (s : ℝ) (r : EuclideanSpace ℝ (Fin m)) :
    (matrixCLM (NormedSpace.exp (s • K)) r) =
      ∑ k, (Real.exp (s * hK.eigenvalues k) * ⟪hK.eigenvectorBasis k, r⟫) •
        hK.eigenvectorBasis k := by
  conv_lhs => rw [← hK.eigenvectorBasis.sum_repr
    (matrixCLM (NormedSpace.exp (s • K)) r)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [OrthonormalBasis.repr_apply_apply, inner_eigenvectorBasis_matrix_exp_mulVec hK s r k]

/-- **Modal energy (Parseval):** `‖exp(s K) r‖² = ∑_k exp(s λ_k)² ⟪v_k, r⟫²`. -/
theorem norm_sq_matrix_exp_mulVec_eq_sum {K : Matrix (Fin m) (Fin m) ℝ}
    (hK : K.IsHermitian) (s : ℝ) (r : EuclideanSpace ℝ (Fin m)) :
    ‖(matrixCLM (NormedSpace.exp (s • K)) r)‖ ^ 2 =
      ∑ k, Real.exp (s * hK.eigenvalues k) ^ 2 * ⟪hK.eigenvectorBasis k, r⟫ ^ 2 := by
  rw [← hK.eigenvectorBasis.sum_sq_inner_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_eigenvectorBasis_matrix_exp_mulVec hK s r k, mul_pow]

end NTK

end
