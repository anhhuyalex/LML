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

/-! ### Reusable Analytic Tool: Grönwall Differential Inequality -/

/-- Interval-Restricted Grönwall Decay Lemma:
If a scalar quantity `E(t)` is continuous on `[0, T]`, differentiable on `(0, T)`, and satisfies
`E'(t) ≤ -c * E(t)` there, then `E(t) ≤ E(0) * exp(-c * t)` for all `t ∈ [0, T]`.
Only interior differentiability is needed, so this applies to forward-time trajectories, and the
localized form enables continuous induction bootstrap arguments where the differential inequality
only holds while the state remains inside a bootstrap region. -/
lemma gronwall_exponential_decay_Icc {E E' : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hEc : ContinuousOn E (Set.Icc 0 T)) (hE : ∀ t ∈ Set.Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, E' t ≤ -c * E t) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    E t ≤ E 0 * Real.exp (-c * t) := by
  let g : ℝ → ℝ := fun s => E s * Real.exp (c * s)
  have hg_deriv : ∀ s ∈ Set.Ioo 0 T,
      HasDerivAt g ((E' s + c * E s) * Real.exp (c * s)) s := by
    intro s hs
    have h1 := hE s hs
    have h2 : HasDerivAt (fun u => Real.exp (c * u)) (Real.exp (c * s) * c) s := by
      have hc : HasDerivAt (fun u => c * u) (c * 1) s := (hasDerivAt_id s).const_mul c
      rw [mul_one] at hc
      exact hc.exp
    have hprod := h1.mul h2
    convert hprod using 1
    ring
  have hg_cont : ContinuousOn g (Set.Icc 0 T) := hEc.mul (by fun_prop)
  have hg_within : ∀ s ∈ interior (Set.Icc 0 T),
      HasDerivWithinAt g ((E' s + c * E s) * Real.exp (c * s)) (interior (Set.Icc 0 T)) s :=
    fun s hs => (hg_deriv s (by rwa [interior_Icc] at hs)).hasDerivWithinAt
  have hg_nonpos : ∀ s ∈ interior (Set.Icc 0 T), (E' s + c * E s) * Real.exp (c * s) ≤ 0 := by
    intro s hs
    have hle : E' s + c * E s ≤ 0 := by
      linarith [hbound s (by rwa [interior_Icc] at hs)]
    have hexp : 0 ≤ Real.exp (c * s) := (Real.exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg hle hexp
  have h_anti : AntitoneOn g (Set.Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hg_cont hg_within hg_nonpos
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have h_le := h_anti h0_mem ht ht.1
  dsimp [g] at h_le
  rw [mul_zero, Real.exp_zero, mul_one] at h_le
  have h_mul := mul_le_mul_of_nonneg_right h_le (Real.exp_pos (-c * t)).le
  have h_exp_cancel : E t * Real.exp (c * t) * Real.exp (-c * t) = E t := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero, mul_one]
  rw [h_exp_cancel] at h_mul
  exact h_mul

/-- Grönwall Differential Inequality for Exponential Decay:
If a differentiable scalar quantity `E(t)` satisfies `E'(t) ≤ -c * E(t)` with `c > 0`,
then `E(t) ≤ E(0) * exp(-c * t)` for all `t ≥ 0`.
Specialization of `gronwall_exponential_decay_Icc` to the interval `[0, t]`. -/
lemma gronwall_exponential_decay {E E' : ℝ → ℝ} {c : ℝ}
    (hE : ∀ t, HasDerivAt E (E' t) t)
    (hbound : ∀ t, E' t ≤ -c * E t) (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ E 0 * Real.exp (-c * t) :=
  gronwall_exponential_decay_Icc ht (fun s _ => (hE s).continuousAt.continuousWithinAt)
    (fun s _ => hE s) (fun s _ => hbound s) t ⟨ht, le_rfl⟩

/-- Mathlib's Grönwall bound is at most `(δ + ε x) e^{K x}` (for `K, ε ≥ 0`), an expression that is
monotone in the time `x ≥ 0` and easy to use for a priori estimates. -/
lemma gronwallBound_le_mul_exp {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases hK.eq_or_lt with rfl | hKpos
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hKpos.ne']
    have hexp : 0 < Real.exp (K * x) := Real.exp_pos _
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h2 := Real.one_sub_le_exp_neg (K * x)
      have h3 : Real.exp (K * x) * Real.exp (-(K * x)) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have h4 : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
      calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ε * x * Real.exp (K * x) := by field_simp
    nlinarith

/-! ### Step-by-Step Proof of Exponential Convergence of Training Loss -/

/-- A positive semidefinite real matrix has a nonnegative quadratic form on `EuclideanSpace`. -/
lemma dotProduct_mulVec_nonneg_of_posSemidef {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef)
    (v : EuclideanSpace ℝ (Fin m)) : 0 ≤ v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) := by
  simpa using hA.dotProduct_mulVec_nonneg v.ofLp

/-- The Euclidean inner product `⟪v, A v⟫` equals the quadratic form `vᵀ A v`. -/
lemma inner_toLp_mulVec_eq_dotProduct (A : Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    ⟪v, (WithLp.toLp 2 (A *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin m))⟫ = v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) := by
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
