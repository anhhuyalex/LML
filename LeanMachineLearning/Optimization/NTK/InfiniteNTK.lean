/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Kernel
public import LeanMachineLearning.Optimization.NTK.Initialization
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Order.Field

/-!
# The Infinite-Width NTK Regime and Linearized Dynamics

This file formalizes the infinite-width Neural Tangent Kernel (NTK) regime and its exact
linearized training dynamics, corresponding to Jacot et al. (2018) and Lee et al. (2019).

## Mathematical Formulation

* **Asymptotic Properties in the Infinite-Width Limit ($n \to \infty$)**:
  * **Property 1 (Deterministic Initialization)**: As width $n \to \infty$, the initial empirical
    kernel concentrates entrywise around a deterministic limit:
    `empiricalNTKFromRows σ' rows n x x' → limitingNTK σ' x x'` almost surely and in probability.
  * **Property 2 (Kernel Constancy / Lazy Training)**: Throughout gradient flow, parameter
    displacement satisfies `‖θ(t) - θ₀‖₂ ≤ C / √n`, freezing the empirical kernel in time:
    `‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ L_K * C / √n`.
    As `n → ∞`, the kernel displacement vanishes:
    `lim_{n → ∞} ‖K_t^{(n)} - K_0^{(n)}‖_F = 0`,
    yielding the exact time-invariant differential operator `K_t ≡ K_∞`.

* **Closed-Form Linear Output Dynamics**:
  * In the infinite-width limit, the output differential equation reduces to a linear autonomous
    ODE with constant matrix coefficients:
    `∂_t r(t) = - (1 / m) K_∞ r(t)`.
  * Integration via the matrix exponential operator yields the closed-form trajectory of residuals:
    `r(t) = exp(- (t / m) K_∞) r(0)`.
  * Closed-form trajectory of network predictions:
    `f(t) = y + exp(- (t / m) K_∞) (f(0) - y)`.

* **Theorem (Exponential Convergence of Training Loss)**:
  Assume the limiting NTK Gram matrix satisfies the Rayleigh-Ritz condition with parameter
  `lambda_min > 0` (`vᵀ K_∞ v ≥ lambda_min ‖v‖²`).
  Then the training residual norm and empirical loss decay exponentially to zero:
    `‖r(t)‖₂ ≤ ‖r(0)‖₂ exp(- (lambda_min / m) t)`
    `L(θ(t)) ≤ L(θ₀) exp(- (2 lambda_min / m) t)`.

* **Step-by-Step Proof of Exponential Convergence**:
  * **Step 1**: Compute the time derivative of the squared residual norm `‖r(t)‖²`:
    `(d / dt) ‖r(t)‖² = 2 r(t)ᵀ ∂_t r(t) = - (2 / m) r(t)ᵀ K_∞ r(t)`.
  * **Step 2**: Use the Rayleigh-Ritz variational characterization `rᵀ K_∞ r ≥ lambda_min ‖r‖²`:
    `(d / dt) ‖r(t)‖² ≤ - (2 lambda_min / m) ‖r(t)‖²`.
  * **Step 3**: Apply Grönwall's differential inequality to obtain the exponential bound:
    `‖r(t)‖² ≤ ‖r(0)‖² exp(- (2 lambda_min / m) t)` and
    `‖r(t)‖ ≤ ‖r(0)‖ exp(- (lambda_min / m) t)`.
  * **Step 4**: Multiply by `1 / (2m)` to obtain the exponential empirical loss bound:
    `L(θ(t)) = (1 / 2m) ‖r(t)‖² ≤ L(θ₀) exp(- (2 lambda_min / m) t)`.

## Main results

* `NTK.gronwall_exponential_decay` : Reusable Grönwall differential inequality for linear decay.
* `NTK.deriv_norm_sq_linear_ode` : Step 1 derivative `(d/dt) ‖r(t)‖² = - (2/m) r(t)ᵀ K_∞ r(t)`.
* `NTK.deriv_norm_sq_le_of_rayleighRitz` : Step 2 bound `(d/dt) ‖r(t)‖² ≤ - (2 λ / m) ‖r(t)‖²`.
* `NTK.residual_norm_sq_exponential_decay` : Step 3 squared residual norm decay.
* `NTK.residual_norm_exponential_decay` : Step 3 residual norm decay.
* `NTK.mse_loss_exponential_decay` : Step 4 empirical MSE loss decay.
* `NTK.matrix_exp_residual_trajectory_zero` : Initial condition `r(0) = r₀`.
* `NTK.matrix_exp_output_trajectory_zero` : Initial condition `f(0) = f₀`.
* `NTK.matrix_exp_residual_eq_output_sub_y` : Residual relation `f(t) - y = r(t)`.
* `NTK.matrix_exp_residual_trajectory_hasDerivAt` : Residual ODE satisfaction
  via matrix exponential.
* `NTK.matrix_exp_output_trajectory_hasDerivAt` : Output ODE satisfaction via matrix exponential.
* `NTK.matrix_exp_residual_decay` : Exponential decay for explicit matrix exponential trajectory.
* `NTK.matrix_exp_loss_decay` : Exponential loss decay for explicit matrix exponential trajectory.
* `NTK.lazy_training_kernel_freeze_bound` : Step 2 kernel freeze bound under lazy training.
* `NTK.tendsto_lazy_training_kernel_freeze` : Asymptotic freeze limit as `n → ∞`.
* `NTK.tendsto_lazy_training_kernel_freeze_matrix` : Empirical NTK matrix freeze as `n → ∞`.
* `NTK.deterministic_initialization_empiricalNTK_tendsto_ae` : Property 1 a.s. initialization limit.
* `NTK.deterministic_initialization_empiricalNTKMatrix_tendsto_ae` : Gram matrix a.s. limit.
* `NTK.deterministic_initialization_chebyshev_bound` : Property 1 entrywise Chebyshev bound.
* `NTK.tendsto_empiricalNTK_chebyshev_bound` : Property 1 Chebyshev tail decay in ENNReal.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix Matrix.Norms.Frobenius Topology

namespace NTK

variable {ι : Type*} {d m P : ℕ}

/-! ### Reusable Analytic Tool: Grönwall Differential Inequality -/

/-- Reusable Grönwall Decay Lemma:
If a differentiable scalar quantity `E(t)` satisfies `E'(t) ≤ -c * E(t)` for all `t`,
then `E(t) ≤ E(0) * exp(-c * t)` for all `t ≥ 0`.
This lemma provides the analytic engine for establishing exponential convergence of
gradient flow training dynamics without ad-hoc definitions. -/
lemma gronwall_exponential_decay {E E' : ℝ → ℝ} {c : ℝ}
    (hE : ∀ t, HasDerivAt E (E' t) t)
    (hbound : ∀ t, E' t ≤ -c * E t) (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ E 0 * Real.exp (-c * t) := by
  let g : ℝ → ℝ := fun s => E s * Real.exp (c * s)
  have hg_deriv : ∀ s, HasDerivAt g ((E' s + c * E s) * Real.exp (c * s)) s := by
    intro s
    have h1 := hE s
    have h2 : HasDerivAt (fun u => Real.exp (c * u)) (Real.exp (c * s) * c) s := by
      have hc : HasDerivAt (fun u => c * u) (c * 1) s := (hasDerivAt_id s).const_mul c
      rw [mul_one] at hc
      exact hc.exp
    have hprod := h1.mul h2
    convert hprod using 1
    ring
  have hg_nonpos : (fun s => (E' s + c * E s) * Real.exp (c * s)) ≤ 0 := by
    intro s
    dsimp
    have hle : E' s + c * E s ≤ 0 := by linarith [hbound s]
    have hexp : 0 ≤ Real.exp (c * s) := (Real.exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg hle hexp
  have h_anti := antitone_of_hasDerivAt_nonpos hg_deriv hg_nonpos
  have h_le := h_anti ht
  dsimp [g] at h_le
  rw [mul_zero, Real.exp_zero, mul_one] at h_le
  have h_mul := mul_le_mul_of_nonneg_right h_le (Real.exp_pos (-c * t)).le
  have h_exp_cancel : E t * Real.exp (c * t) * Real.exp (-c * t) = E t := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero, mul_one]
  rw [h_exp_cancel] at h_mul
  exact h_mul

/-! ### Step-by-Step Proof of Exponential Convergence of Training Loss -/

/-- Step 1 (Time Derivative of Squared Residual Norm):
Along any trajectory satisfying `∂_t r(t) = - (1 / m) K_inf r(t)`, the rate of change of
`‖r(t)‖²` is given by:
  `(d / dt) ‖r(t)‖² = 2 r(t)ᵀ ∂_t r(t) = - (2 / m) r(t)ᵀ K_inf r(t)`. -/
theorem deriv_norm_sq_linear_ode
    (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp))) t := by
  have h_inner : HasDerivAt (fun s => ⟪r s, r s⟫)
      (⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))⟫ +
       ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp)), r t⟫) t :=
    HasDerivAt.inner ℝ hr hr
  have h_symm : ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp)), r t⟫ =
      ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))⟫ := real_inner_comm _ _
  rw [h_symm, ← two_mul] at h_inner
  have h_dot : ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))⟫ =
      -(m : ℝ)⁻¹ * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp)) := by
    rw [show r t = WithLp.toLp 2 (r t).ofLp by rfl]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial]
    rw [smul_dotProduct, dotProduct_comm]
    ring
  rw [h_dot] at h_inner
  have h_norm_sq : (fun s => ‖r s‖ ^ 2) = (fun s => ⟪r s, r s⟫) := by
    ext s
    exact (real_inner_self_eq_norm_sq (r s)).symm
  rw [h_norm_sq]
  convert h_inner using 1
  ring

/-- Step 2 (Rayleigh-Ritz Lower Bound Substitution):
Using the Rayleigh-Ritz condition `vᵀ K_inf v ≥ lambda_min ‖v‖²`, the rate of change is bounded:
  `(d / dt) ‖r(t)‖² ≤ - (2 lambda_min / m) ‖r(t)‖²`. -/
theorem deriv_norm_sq_le_of_rayleighRitz
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp))) t ∧
      -(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp)) ≤
        -(2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by
  constructor
  · exact deriv_norm_sq_linear_ode K_inf r t hr
  · have h1 := h_rr (r t)
    have hpos : 0 < 2 / (m : ℝ) := div_pos (by norm_num) hm
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : (2 / (m : ℝ)) * (lambda_min * ‖r t‖ ^ 2) =
        (2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by ring
    rw [h3] at h2
    linarith

/-- Step 3 (Grönwall Integration for Squared Residual Norm):
Integrating the differential inequality yields:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)`. -/
theorem residual_norm_sq_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have hE : ∀ s, HasDerivAt (fun u => ‖r u‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K_inf *ᵥ (r s).ofLp))) s :=
    fun s => deriv_norm_sq_linear_ode K_inf r s (hr s)
  have hbound : ∀ s, -(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K_inf *ᵥ (r s).ofLp)) ≤
      -(2 * lambda_min / (m : ℝ)) * ‖r s‖ ^ 2 := by
    intro s
    have h := deriv_norm_sq_le_of_rayleighRitz K_inf lambda_min h_rr r s (hr s) hm
    exact h.2
  exact gronwall_exponential_decay hE hbound t ht

/-- Step 3 (Exponential Decay of Residual Norm):
Taking the square root gives:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)`. -/
theorem residual_norm_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) := by
  have h_sq := residual_norm_sq_exponential_decay K_inf lambda_min h_rr r hr hm t ht
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_mul (sq_nonneg _)] at h_sqrt
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  have h_exp_sqrt : Real.sqrt (Real.exp (-(2 * lambda_min / (m : ℝ)) * t)) =
      Real.exp (-(lambda_min / (m : ℝ)) * t) := by
    rw [← Real.exp_half]
    congr 1
    ring
  rw [h_exp_sqrt] at h_sqrt
  exact h_sqrt

/-- Step 4 (Exponential Loss Decay):
Multiplying by `1 / (2m)` yields the exponential loss convergence bound:
  `(1 / (2m)) ‖r(t)‖² ≤ ((1 / (2m)) ‖r(0)‖²) * exp(- (2 lambda_min / m) t)`. -/
theorem mse_loss_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖r t‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r 0‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have h := residual_norm_sq_exponential_decay K_inf lambda_min h_rr r hr hm t ht
  have hpos : 0 ≤ (2 * (m : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have h_mul := mul_le_mul_of_nonneg_left h hpos
  rw [← mul_assoc] at h_mul
  exact h_mul

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
  rw [Matrix.mul_mulVec, Matrix.smul_mulVec]

/-- The closed-form matrix exponential residual trajectory satisfies the linear autonomous ODE:
  `∂_t r(t) = - (1 / m) K_∞ r(t)`. -/
theorem matrix_exp_residual_trajectory_hasDerivAt
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt
      (fun s => (WithLp.toLp 2 ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp)))) t := by
  have h_exp := hasDerivAt_exp_smul_const' (-(m : ℝ)⁻¹ • K_inf) t
  have h_clm := hasDerivAt_clm_apply_const (toEuclideanVecCLM r₀.ofLp)
    (fun u => NormedSpace.exp (u • (-(m : ℝ)⁻¹ • K_inf)))
    ((-(m : ℝ)⁻¹ • K_inf) * NormedSpace.exp (t • (-(m : ℝ)⁻¹ • K_inf))) t h_exp
  simp only [toEuclideanVecCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk] at h_clm
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

/-! ### Asymptotic Properties in the Infinite-Width Limit -/

/-- Reusable Limit: Reciprocal square root sequence vanishes as `n → ∞`. -/
lemma tendsto_const_div_sqrt_nat_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => c / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.const_div_atTop hg c

/-- Property 2 (Kernel Constancy / Lazy Training Freeze Bound):
Under parameter displacement `‖θ(t) - θ₀‖ ≤ C / √n` and `L_K`-Lipschitz empirical NTK,
the empirical kernel stays within `O(n^{-1/2})` of initialization for all `t ≥ 0`:
  `‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ L_K * C / √n`. -/
theorem lazy_training_kernel_freeze_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P)) (θ₀ : EuclideanSpace ℝ (Fin P))
    (C L_K : ℝ) (hL_K : 0 ≤ L_K) (n : ℕ)
    (hlazy : ∀ t ≥ 0, ‖θ_traj t - θ₀‖ ≤ C / Real.sqrt (n : ℝ))
    (hLip : ∀ t ≥ 0, ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      L_K * ‖θ_traj t - θ₀‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      L_K * C / Real.sqrt (n : ℝ) := by
  have h1 := hLip t ht
  have h2 := hlazy t ht
  have h_mul := mul_le_mul_of_nonneg_left h2 hL_K
  rw [← mul_div_assoc] at h_mul
  exact h1.trans h_mul

/-- Property 2 (Asymptotic Freeze of Empirical NTK Bound in Infinite-Width Limit):
As the network width `n → ∞`, the kernel displacement bound `L_K * C / √n` converges to `0`. -/
theorem tendsto_lazy_training_kernel_freeze (L_K C : ℝ) :
    Tendsto (fun n : ℕ => L_K * C / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
  tendsto_const_div_sqrt_nat_atTop (L_K * C)

/-- Property 2 (Asymptotic Freeze of Empirical NTK Matrix in Infinite-Width Limit):
Under lazy training displacement `‖θ(t) - θ₀‖ ≤ C / √n` and Lipschitz continuity of the
empirical NTK Gram matrix `empiricalNTKMatrix`, the difference
`‖empiricalNTKMatrix (f n) X (θ_traj n t) - empiricalNTKMatrix (f n) X (θ₀ n)‖` converges
to `0` as network width `n → ∞`. -/
theorem tendsto_lazy_training_kernel_freeze_matrix
    {P : ℕ → ℕ}
    (f : (n : ℕ) → ι → EuclideanSpace ℝ (Fin (P n)) → ℝ) (X : Fin m → ι)
    (θ_traj : (n : ℕ) → ℝ → EuclideanSpace ℝ (Fin (P n)))
    (θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin (P n)))
    (C L_K : ℝ) (hL_K : 0 ≤ L_K)
    (hlazy : ∀ n (t : ℝ), 0 ≤ t → ‖θ_traj n t - θ₀ n‖ ≤ C / Real.sqrt (n : ℝ))
    (hLip : ∀ n (t : ℝ), 0 ≤ t →
      ‖empiricalNTKMatrix (f n) X (θ_traj n t) - empiricalNTKMatrix (f n) X (θ₀ n)‖ ≤
        L_K * ‖θ_traj n t - θ₀ n‖)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ =>
      ‖empiricalNTKMatrix (f n) X (θ_traj n t) - empiricalNTKMatrix (f n) X (θ₀ n)‖)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hh : Tendsto (fun n : ℕ => L_K * C / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    tendsto_lazy_training_kernel_freeze L_K C
  have hgf : (fun _ : ℕ => (0 : ℝ)) ≤
      (fun n : ℕ => ‖empiricalNTKMatrix (f n) X (θ_traj n t) -
        empiricalNTKMatrix (f n) X (θ₀ n)‖) :=
    fun _ => norm_nonneg _
  have hfh : (fun n : ℕ => ‖empiricalNTKMatrix (f n) X (θ_traj n t) -
      empiricalNTKMatrix (f n) X (θ₀ n)‖) ≤
      (fun n : ℕ => L_K * C / Real.sqrt (n : ℝ)) := by
    intro n
    exact lazy_training_kernel_freeze_bound (f n) X (θ_traj n) (θ₀ n) C L_K hL_K n
      (hlazy n) (hLip n) t ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh hgf hfh

/-- Property 1 (Deterministic NTK Initialization):
By `ntk_convergence` from `Kernel.lean`, the empirical kernel `empiricalNTKFromRows`
built from `n` Gaussian hidden rows converges almost surely to the deterministic
limiting kernel `limitingNTK` as width `n → ∞`:
  `k_n(x, x') → k_∞(x, x')` a.s. -/
theorem deterministic_initialization_empiricalNTK_tendsto_ae
    (σ' : ℝ → ℝ) (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C) (x x' : Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)),
      Filter.Tendsto (fun n => empiricalNTKFromRows σ' rows n x x')
        Filter.atTop (𝓝 (limitingNTK σ' x x')) :=
  ntk_convergence σ' hσ'_meas hσ'_bounded x x'

/-- Property 1 (Deterministic NTK Gram Matrix Initialization Limit):
For any finite dataset `X : Fin m → Fin d → ℝ`, the empirical NTK Gram matrix
`fun α β => empiricalNTKFromRows σ' rows n (X α) (X β)` converges entrywise almost surely
to the deterministic limiting NTK Gram matrix `fun α β => limitingNTK σ' (X α) (X β)`
as width `n → ∞`. -/
theorem deterministic_initialization_empiricalNTKMatrix_tendsto_ae
    (σ' : ℝ → ℝ) (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C) (X : Fin m → Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)),
      ∀ α β : Fin m,
        Filter.Tendsto (fun n => empiricalNTKFromRows σ' rows n (X α) (X β))
          Filter.atTop (𝓝 (limitingNTK σ' (X α) (X β))) := by
  rw [eventually_all]
  intro α
  rw [eventually_all]
  intro β
  exact ntk_convergence σ' hσ'_meas hσ'_bounded (X α) (X β)

/-- Reusable Limit: Reciprocal natural number sequence scaled by `C / ε²` vanishes as `n → ∞`. -/
lemma tendsto_chebyshev_bound_atTop (C ε : ℝ) :
    Tendsto (fun n : ℕ => C / (ε ^ 2 * (n : ℝ))) atTop (𝓝 0) := by
  have h_eq : (fun n : ℕ => C / (ε ^ 2 * (n : ℝ))) = (fun n : ℕ => (C / ε ^ 2) / (n : ℝ)) := by
    ext n
    rw [div_mul_eq_div_div]
  rw [h_eq]
  have hg : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.const_div_atTop hg (C / ε ^ 2)

/-- Property 1 (Empirical NTK Entrywise Chebyshev Concentration Bound):
For any tolerance `ε > 0`, the probability under the initialization measure
`Measure.infinitePi (fun _ => gaussianRowMeasure d)` that the empirical NTK
`empiricalNTKFromRows σ' rows n x x'` deviates from its expectation by `≥ ε`
is bounded by `variance (empiricalNTKFromRows σ' · n x x') μ / ε²`.
When the estimator's variance decays as `≤ C / n`, this probability is bounded
by `C / (ε² * n)`. -/
theorem deterministic_initialization_chebyshev_bound
    (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) (n : ℕ) (C : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hL2 : MemLp (fun rows => empiricalNTKFromRows σ' rows n x x') 2
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d))
    (hvar : ProbabilityTheory.variance (fun rows => empiricalNTKFromRows σ' rows n x x')
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d) ≤ C / (n : ℝ)) :
    let μ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)
    let k_n := fun rows => empiricalNTKFromRows σ' rows n x x'
    μ {rows | ε ≤ |k_n rows - ∫ r, k_n r ∂μ|} ≤
      ENNReal.ofReal (C / (ε ^ 2 * (n : ℝ))) := by
  intro μ k_n
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) hL2 hε
  have h_bound : ProbabilityTheory.variance k_n μ / ε ^ 2 ≤ C / (ε ^ 2 * (n : ℝ)) := by
    have h_pos : 0 < ε ^ 2 := pow_pos hε 2
    have h1 : ProbabilityTheory.variance k_n μ / ε ^ 2 =
        (ε ^ 2)⁻¹ * ProbabilityTheory.variance k_n μ := by ring
    have h2 : C / (ε ^ 2 * (n : ℝ)) = (ε ^ 2)⁻¹ * (C / (n : ℝ)) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hvar (inv_pos.mpr h_pos).le
  exact hcheb.trans (ENNReal.ofReal_le_ofReal h_bound)

/-- Property 1 (Asymptotic Concentration of Empirical NTK Deviation in Probability):
As network width `n → ∞`, the Chebyshev upper bound `ENNReal.ofReal (C / (ε² * n))`
on the probability that `empiricalNTKFromRows` deviates by `≥ ε` converges to `0`. -/
theorem tendsto_empiricalNTK_chebyshev_bound (C ε : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (C / (ε ^ 2 * (n : ℝ)))) atTop (𝓝 0) := by
  have h_real : Tendsto (fun n : ℕ => C / (ε ^ 2 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_chebyshev_bound_atTop C ε
  have h := ENNReal.tendsto_ofReal h_real
  rw [ENNReal.ofReal_zero] at h
  exact h

end NTK

end
