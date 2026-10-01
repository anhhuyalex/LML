/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.Dynamics

/-!
# Gradient flow: Grönwall and exponential convergence of the loss

The Grönwall differential inequality and the step-by-step proof of exponential convergence of the
training loss under a positive kernel gap.

## Main results and proof outline

* `NTK.deriv_norm_sq_linear_ode` : Step 1 derivative `(d/dt) ‖r(t)‖² = - (2/m) r(t)ᵀ K_∞ r(t)`.
* `NTK.deriv_norm_sq_le_of_rayleighRitz` : Step 2 bound `(d/dt) ‖r(t)‖² ≤ - (2 λ / m) ‖r(t)‖²`.
* `NTK.residual_norm_sq_exponential_decay` : Step 3 squared residual norm decay.
* `NTK.residual_norm_exponential_decay` : Step 3 residual norm decay.
* `NTK.mse_loss_exponential_decay` : Step 4 empirical MSE loss decay.
* `NTK.deriv_norm_sq_timeVarying_ode` : Step 1 derivative for time-varying NTK `K(t)`.
* `NTK.deriv_norm_sq_le_of_rayleighRitz_timeVarying` : Step 2 Rayleigh-Ritz bound for `K(t)`.
* `NTK.residual_norm_sq_exponential_decay_timeVarying` : Step 3 squared residual decay for `K(t)`.
* `NTK.residual_norm_exponential_decay_timeVarying` : Step 3 residual norm decay for `K(t)`.
* `NTK.mse_loss_exponential_decay_timeVarying` : Step 4 MSE loss decay for `K(t)`.
* `NTK.residual_norm_sq_exponential_decay_timeVarying_Icc` : Local interval squared residual decay.
* `NTK.residual_norm_exponential_decay_timeVarying_Icc` : Local interval residual decay on `[0, T]`.

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

/-! ### Step-by-Step Proof of Exponential Convergence of Training Loss -/

/-- A positive semidefinite real matrix has a nonnegative quadratic form on `EuclideanSpace`. -/
lemma dotProduct_mulVec_nonneg_of_posSemidef {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef)
    (v : EuclideanSpace ℝ (Fin m)) : 0 ≤ v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) := by
  simpa using hA.dotProduct_mulVec_nonneg v.ofLp

/-- The Euclidean inner product `⟪v, A v⟫` equals the quadratic form `vᵀ A v`. -/
lemma inner_toLp_mulVec_eq_dotProduct (A : Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    ⟪v, (matrixCLM A v)⟫ = v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- Step 1 (Time Derivative of Squared Residual Norm under Time-Varying Kernel):
Along any trajectory satisfying `∂_t r(t) = - (1 / m) K(t) r(t)`, the rate of change of
`‖r(t)‖²` is given by:
  `(d / dt) ‖r(t)‖² = 2 r(t)ᵀ ∂_t r(t) = - (2 / m) r(t)ᵀ K(t) r(t)`. -/
theorem deriv_norm_sq_timeVarying_ode
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp))) t := by
  have h_inner : HasDerivAt (fun s => ⟪r s, r s⟫)
      (⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))⟫ +
       ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp)), r t⟫) t :=
    HasDerivAt.inner ℝ hr hr
  have h_symm : ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp)), r t⟫ =
      ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))⟫ := real_inner_comm _ _
  rw [h_symm, ← two_mul] at h_inner
  have h_dot : ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))⟫ =
      -(m : ℝ)⁻¹ * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp)) := by
    rw [real_inner_eq_dotProduct, WithLp.ofLp_toLp, dotProduct_smul, smul_eq_mul]
  rw [h_dot] at h_inner
  have h_norm_sq : (fun s => ‖r s‖ ^ 2) = (fun s => ⟪r s, r s⟫) := by
    ext s
    exact (real_inner_self_eq_norm_sq (r s)).symm
  rw [h_norm_sq]
  convert h_inner using 1
  ring_nf

/-- Step 1 (Time Derivative of Squared Residual Norm - Autonomous Specialization):
Along any trajectory satisfying `∂_t r(t) = - (1 / m) K_inf r(t)`:
  `(d / dt) ‖r(t)‖² = - (2 / m) r(t)ᵀ K_inf r(t)`. -/
theorem deriv_norm_sq_linear_ode
    (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp))) t :=
  deriv_norm_sq_timeVarying_ode (fun _ => K_inf) r t hr

/-- Step 2 (Rayleigh-Ritz Lower Bound with Time-Varying Kernel):
When `vᵀ K(t) v ≥ lambda_min ‖v‖²`, the rate of change is bounded:
  `(d / dt) ‖r(t)‖² ≤ - (2 lambda_min / m) ‖r(t)‖²`. -/
theorem deriv_norm_sq_le_of_rayleighRitz_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp))) t ∧
      -(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp)) ≤
        -(2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by
  constructor
  · exact deriv_norm_sq_timeVarying_ode K r t hr
  · have h1 := h_rr (r t)
    have hpos : 0 < 2 / (m : ℝ) := div_pos (by norm_num) hm
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : (2 / (m : ℝ)) * (lambda_min * ‖r t‖ ^ 2) =
        (2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by ring
    rw [h3] at h2
    linarith

/-- Step 2 (Rayleigh-Ritz Lower Bound Substitution - Autonomous Specialization):
Using the Rayleigh-Ritz condition `vᵀ K_inf v ≥ lambda_min ‖v‖²`:
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
        -(2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 :=
  deriv_norm_sq_le_of_rayleighRitz_timeVarying (fun _ => K_inf) lambda_min r t h_rr hr hm

/-- Grönwall Integration for Squared Residual Norm on a Closed Interval `[0, T]`:
Under a Rayleigh quotient lower bound on `K(s)` holding for all `s ∈ [0, T]`, the squared
residual norm decays exponentially:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)` for any `t ∈ [0, T]`.
The residual ODE is only needed on `(0, T)`, with continuity on `[0, T]`. -/
theorem residual_norm_sq_exponential_decay_timeVarying_Icc
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min T : ℝ) (hT : 0 ≤ T)
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (h_rr : ∀ s ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K s *ᵥ v.ofLp))
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have hE : ∀ s ∈ Set.Ioo 0 T, HasDerivAt (fun u => ‖r u‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K s *ᵥ (r s).ofLp))) s :=
    fun s hs => deriv_norm_sq_timeVarying_ode K r s (hr s hs)
  have hbound : ∀ s ∈ Set.Ioo 0 T,
      -(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K s *ᵥ (r s).ofLp)) ≤
        -(2 * lambda_min / (m : ℝ)) * ‖r s‖ ^ 2 := by
    intro s hs
    exact (deriv_norm_sq_le_of_rayleighRitz_timeVarying K lambda_min r s
      (h_rr s (Set.Ioo_subset_Icc_self hs)) (hr s hs) hm).2
  exact gronwall_exponential_decay_Icc hT (hrc.norm.pow 2) hE hbound t ht

/-- Exponential Decay of Residual Norm on a Closed Interval `[0, T]`:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)` for any `t ∈ [0, T]`. -/
theorem residual_norm_exponential_decay_timeVarying_Icc
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min T : ℝ) (hT : 0 ≤ T)
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (h_rr : ∀ s ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K s *ᵥ v.ofLp))
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) := by
  have h_sq :=
    residual_norm_sq_exponential_decay_timeVarying_Icc K lambda_min T hT r h_rr hrc hr hm t ht
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

/-- Step 3 (Grönwall Integration for Squared Residual Norm under Time-Varying Kernel):
Under a uniform-in-time Rayleigh lower bound on `K(t)`:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)`. -/
theorem residual_norm_sq_exponential_decay_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ t, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) :=
  residual_norm_sq_exponential_decay_timeVarying_Icc K lambda_min t ht r
    (fun s _ => h_rr s) (fun s _ => (hr s).continuousAt.continuousWithinAt) (fun s _ => hr s) hm t
    ⟨ht, le_rfl⟩

/-- Step 3 (Exponential Decay of Residual Norm under Time-Varying Kernel):
Taking the square root yields:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)`. -/
theorem residual_norm_exponential_decay_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ t, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) :=
  residual_norm_exponential_decay_timeVarying_Icc K lambda_min t ht r
    (fun s _ => h_rr s) (fun s _ => (hr s).continuousAt.continuousWithinAt) (fun s _ => hr s) hm t
    ⟨ht, le_rfl⟩

/-- Step 4 (Exponential Loss Decay under Time-Varying Kernel):
  `(1 / (2m)) ‖r(t)‖² ≤ ((1 / (2m)) ‖r(0)‖²) * exp(- (2 lambda_min / m) t)`. -/
theorem mse_loss_exponential_decay_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ t, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖r t‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r 0‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have h := residual_norm_sq_exponential_decay_timeVarying K lambda_min h_rr r hr hm t ht
  have hpos : 0 ≤ (2 * (m : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have h_mul := mul_le_mul_of_nonneg_left h hpos
  rw [← mul_assoc] at h_mul
  exact h_mul

/-- Step 3 (Grönwall Integration for Squared Residual Norm - Autonomous Specialization):
Integrating the differential inequality yields:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)`. -/
theorem residual_norm_sq_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) :=
  residual_norm_sq_exponential_decay_timeVarying (fun _ => K_inf) lambda_min
    (fun _ => h_rr) r hr hm t ht

/-- Step 3 (Exponential Decay of Residual Norm - Autonomous Specialization):
Taking the square root gives:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)`. -/
theorem residual_norm_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) :=
  residual_norm_exponential_decay_timeVarying (fun _ => K_inf) lambda_min
    (fun _ => h_rr) r hr hm t ht

/-- Step 4 (Exponential Loss Decay - Autonomous Specialization):
  `(1 / (2m)) ‖r(t)‖² ≤ ((1 / (2m)) ‖r(0)‖²) * exp(- (2 lambda_min / m) t)`. -/
theorem mse_loss_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖r t‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r 0‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) :=
  mse_loss_exponential_decay_timeVarying (fun _ => K_inf) lambda_min
    (fun _ => h_rr) r hr hm t ht

end NTK

end
