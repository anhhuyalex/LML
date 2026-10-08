/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization
public import LeanMachineLearning.Optimization.NTK.Foundations.ODE

/-!
# Gradient flow: function-space dynamics and risk dissipation

The residual ODE `∂_t r(t) = -(1/m) K_t r(t)` (Proposition 2.15), the generalization to arbitrary
differentiable losses, the risk dissipation identity (Proposition 2.17) and the kinetic energy along
gradient flow.

## Main results and proof outline

* `NTK.hasDerivAt_trainingOutputs_coord` : Step 1 chain rule `∂_t f^α(t) = ⟨∇_θ f^α, ∂_t θ⟩`.
* `NTK.hasDerivAt_trainingOutputs_coord_sum` : Step 1 coordinate-sum chain rule.
* `NTK.hasDerivAt_euclideanSpace` : Helper relating vector- and coordinate-wise `HasDerivAt`.
* `NTK.generalizedEmpiricalRisk` : General empirical risk `L(θ) = (1/m) ∑_α ℓ(f^α(θ), y^α)`.
* `NTK.generalizedResidual` : General residual `r^α := ∂_f ℓ(f^α(θ), y^α)`.
* `NTK.hasDerivAt_squaredLoss` : Concrete example, squared loss residual `r^α = f^α - y^α`.
* `NTK.hasDerivAt_logisticLoss` : Concrete example, logistic loss residual `r^α = -y^α σ(-y^α f^α)`.
* `NTK.hasDerivAt_exponentialLoss` : Concrete example, exponential loss residual.
* `NTK.gradient_generalizedRisk` : Gradient of the generalized empirical risk.
* `NTK.gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad` : Step 2, generalized loss.
* `NTK.gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner` : Step 3, generalized loss.
* `NTK.gradient_flow_generalizedOutput_coord_ode` : Step 4, generalized loss.
* `NTK.gradient_flow_generalizedOutput_vector_ode` : Step 5, generalized output evolution
  `∂_t f(t) = - (1/m) K_t r(t)`.
* `NTK.gradient_flow_output_coord_deriv_eq_inner_grad` : Step 2 (squared loss), corollary.
* `NTK.gradient_flow_output_coord_deriv_eq_sum_inner` : Step 3 (squared loss), corollary.
* `NTK.gradient_flow_output_coord_ode` : Step 4 (squared loss), corollary.
* `NTK.gradient_flow_output_vector_ode` : Step 5 output ODE at learning rate `η`,
  `∂_t f(t) = - (η/m) K_t r(t)` (unit-rate gradient flow is `η = 1`).
* `NTK.gradient_flow_output_vector_ode_sub_y` : Step 5 output ODE
  `∂_t f(t) = - (1/m) K_t (f(t) - y)`.
* `NTK.gradient_flow_residual_vector_ode` : Step 5 residual ODE `∂_t r(t) = - (1/m) K_t r(t)`.
* `NTK.hasDerivAt_generalizedEmpiricalRisk_coord_sum` : Prop 2.17 Step 1, chain rule
  `∂_t L(θ(t)) = (1/m) r(t)ᵀ ∂_t f(t)`.
* `NTK.risk_dissipation_identity` : **Proposition 2.17**, risk dissipation identity
  `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`.
* `NTK.risk_dissipation_nonpos` : Monotone risk dissipation `∂_t L(θ(t)) ≤ 0` via PSD `K_t`.
* `NTK.risk_dissipation_le_of_rayleighRitz` : Strict dissipation bound
  `∂_t L(θ(t)) ≤ - (lambda_min / m²) ‖r(t)‖²` under a Rayleigh-Ritz condition on `K_t`.
* `NTK.norm_sq_gradient_generalizedRisk`, `NTK.norm_sq_gradient_mseLoss`,
  `NTK.norm_deriv_sq_eq_quadratic_form_of_forwardGF`, `NTK.mseLoss_sub_eq_integral_quadratic_form` :
  Kinetic energy: `‖∇L‖² = (1/m²) rᵀ K r`, `‖θ'‖² = (1/m²) rᵀ K r` along the forward flow,
  and `L(θ 0) - L(θ T) = ∫₀ᵀ (1/m²) rᵀ K r = ∫₀ᵀ ‖θ'‖²` (generic part in
  `ConvexOpt.ForwardGFTrajectory`).
* `NTK.hasDerivAt_coord_of_forwardGF` : Coordinate form `∂_t θ_k = -(1/m) [Jᵀ r]_k` of the
  training flow (the `a_i` and `W_{ij}` equations are in `NTK.Training.TwoLayer.Packing`).

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

local instance (priority := 2000) instCompleteSpaceMatrix (m : ℕ) :
    CompleteSpace (Matrix (Fin m) (Fin m) ℝ) :=
  FiniteDimensional.complete ℝ (Matrix (Fin m) (Fin m) ℝ)

/-! ### Continuous Gradient Flow and Function-Space Dynamics

This section formalizes the exact induced function-space training dynamics along the
continuous gradient flow trajectory:
  `∂_t θ(t) = - ∇_θ L(θ(t))`
under the empirical MSE loss. Across five sequential steps, we prove that the output vector
`f(t) ∈ ℝ^m` and residual error vector `r(t) = f(t) - y` satisfy the closed-form ODEs:
  `∂_t f(t) = - (1 / m) K_t (f(t) - y) = - (1 / m) K_t r(t)`
  `∂_t r(t) = - (1 / m) K_t r(t)`
where `K_t = J(θ(t)) J(θ(t))ᵀ ∈ ℝ^{m × m}` is the empirical NTK Gram matrix at time `t`.
In particular, for neural network architectures parameterized by width `n` (as in
`LeanMachineLearning.Optimization.NTK.Initialization`), `K_t` corresponds to the width-`n`
empirical kernel matrix `K_t^{(n)}`.
-/

/-- Helper: The inner product on `EuclideanSpace ℝ (Fin P)` equals the sum of entrywise products. -/
lemma euclideanSpace_inner_eq_sum (u v : EuclideanSpace ℝ (Fin P)) :
    ⟪u, v⟫ = ∑ j : Fin P, u j * v j :=
  real_inner_eq_dotProduct u v

/-- Step 1 (Multivariate Chain Rule - Inner Product Formulation):
Evaluate the time derivative of component output `f^α(t) ≡ f(x^α; θ(t))`:
  `∂_t f^α(t) = ⟨∇_θ f(x^α; θ(t)), ∂_t θ(t)⟩`. -/
theorem hasDerivAt_trainingOutputs_coord
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P))
    (θ' : ℝ → EuclideanSpace ℝ (Fin P)) (t : ℝ) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t))
    (hθ : HasDerivAt θ_traj (θ' t) t) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      ⟪tangentFeature f (X α) (θ_traj t), θ' t⟫ t := by
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hθ
  have hgrad : fderiv ℝ (fun θ' => f (X α) θ') (θ_traj t) (θ' t) =
      ⟪tangentFeature f (X α) (θ_traj t), θ' t⟫ := by
    rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply]
    rfl
  rw [hgrad] at hcomp
  exact hcomp

/-- Step 1 (Multivariate Chain Rule - Coordinate Sum Formulation):
Along any differentiable parameter curve `θ(t)`, the rate of change of the component
output satisfies:
  `∂_t f^α(t) = ∑_{j=1}^P (∂f(x^α; θ(t)) / ∂θ_j) · (dθ_j(t) / dt) = ⟨∇_θ f(x^α; θ(t)), ∂_t θ(t)⟩`.
-/
theorem hasDerivAt_trainingOutputs_coord_sum
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P))
    (θ' : ℝ → EuclideanSpace ℝ (Fin P)) (t : ℝ) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t))
    (hθ : HasDerivAt θ_traj (θ' t) t) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      (∑ j : Fin P, tangentFeature f (X α) (θ_traj t) j * θ' t j) t := by
  have h := hasDerivAt_trainingOutputs_coord f X θ_traj θ' t α hdiff hθ
  rw [euclideanSpace_inner_eq_sum] at h
  exact h

/-- Helper: a curve into `EuclideanSpace ℝ (Fin m)` has a derivative iff each of its coordinate
functions does, with matching coordinate derivatives. -/
lemma hasDerivAt_euclideanSpace (v : ℝ → EuclideanSpace ℝ (Fin m))
    (v' : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt v v' t ↔ ∀ i : Fin m, HasDerivAt (fun s => v s i) (v' i) t := by
  let e := (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearEquiv
  have h := hasDerivAt_pi (φ := fun s => e (v s)) (φ' := e v') (x := t)
  constructor
  · intro hv i
    have he := (e : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ)).hasFDerivAt.comp_hasDerivAt t hv
    exact (h.mp he) i
  · intro hi
    have he : HasDerivAt (fun s => e (v s)) (e v') t := h.mpr hi
    have h_orig :=
      (e.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).hasFDerivAt.comp_hasDerivAt t he
    convert h_orig
    · ext s; simp [e]
    · simp [e]

/-! ### Generalization to Arbitrary Differentiable Loss Functions

The residual ODE below (`gradient_flow_output_coord_deriv_eq_inner_grad` through
`gradient_flow_output_vector_ode`) specializes the empirical risk to the squared loss
`ℓ(f,y) = (1/2)(f - y)²`. More generally, for any pointwise loss `ℓ : ℝ → ℝ → ℝ` that is
differentiable in its first argument, define the empirical risk and the generalized scalar
residual:
  `L(θ) = (1/m) ∑_α ℓ(f(x^α; θ), y^α)`
  `r^α(t) = ∂_f ℓ(f^α(t), y^α)`
Concrete examples: squared loss `ℓ(f,y) = (1/2)(f-y)²` gives `r^α = f^α - y^α`; binary
logistic/cross-entropy loss `ℓ(f,y) = log(1 + exp(-y f))` gives `r^α = -y^α σ(-y^α f^α)`, where
`σ` is the sigmoid function; exponential loss `ℓ(f,y) = exp(-y f)` gives
`r^α = -y^α exp(-y^α f^α)`. By the multivariate chain rule, the parameter gradient and the output
evolution generalize to:
  `∇_θ L(θ(t)) = (1/m) ∑_β r^β(t) ∇_θ f(x^β; θ(t))`
  `∂_t f(t) = - (1/m) K_t r(t)`
The squared-loss theorems below are proved as corollaries of the general theorems here,
instantiated at `ℓ(f,y) = (1/2)(f-y)²`.
-/

/-- The generalized empirical risk under a pointwise loss `ℓ`:
  `L(θ) = (1 / m) ∑_α ℓ(f(x^α; θ), y^α)`. -/
noncomputable def generalizedEmpiricalRisk (ℓ : ℝ → ℝ → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) : ℝ :=
  (m : ℝ)⁻¹ * ∑ α : Fin m, ℓ (f (X α) θ) (y α)

private lemma generalizedEmpiricalRisk_squaredLoss_eq_mseLoss
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m)) :
    generalizedEmpiricalRisk (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y = mseLoss f X y := by
  funext θ
  rw [generalizedEmpiricalRisk, mseLoss_eq_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The generalized scalar residual `r^α := ∂_f ℓ(f^α(θ), y^α)`. -/
noncomputable def generalizedResidual (ℓ : ℝ → ℝ → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun α => deriv (fun f' => ℓ f' (y α)) (f (X α) θ))

/-- Concrete Example (Squared Loss): for `ℓ(f,y) = (1/2)(f-y)²`, the generalized residual is
`∂_f ℓ(f,y) = f - y`. -/
theorem hasDerivAt_squaredLoss (f y : ℝ) :
    HasDerivAt (fun f' => (1 / 2 : ℝ) * (f' - y) ^ 2) (f - y) f := by
  have h1 : HasDerivAt (fun f' : ℝ => f' - y) 1 f := (hasDerivAt_id f).sub_const y
  have h2 := h1.pow 2
  have h3 := h2.const_mul (1 / 2 : ℝ)
  convert h3 using 1
  push_cast
  ring

private lemma generalizedResidual_squaredLoss_eq_trainingResidual
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) :
    generalizedResidual (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y θ =
      trainingResidual f X y θ := by
  ext α
  change deriv (fun f' => (1 / 2 : ℝ) * (f' - y α) ^ 2) (f (X α) θ) = trainingResidual f X y θ α
  rw [(hasDerivAt_squaredLoss (f (X α) θ) (y α)).deriv]
  rfl

private lemma hasDerivAt_squaredLoss_generalizedResidual
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) (β : Fin m) :
    HasDerivAt (fun f' => (1 / 2 : ℝ) * (f' - y β) ^ 2)
      (generalizedResidual (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y θ β)
      (f (X β) θ) := by
  have hval : generalizedResidual (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y θ β =
      f (X β) θ - y β := by
    rw [generalizedResidual_squaredLoss_eq_trainingResidual]
    rfl
  rw [hval]
  exact hasDerivAt_squaredLoss (f (X β) θ) (y β)

/-- Concrete Example (Binary Logistic / Cross-Entropy Loss): for `ℓ(f,y) = log(1 + exp(-y f))`,
the generalized residual is `∂_f ℓ(f,y) = -y σ(-y f)`, where `σ` is the sigmoid function. -/
theorem hasDerivAt_logisticLoss (f y : ℝ) :
    HasDerivAt (fun f' => Real.log (1 + Real.exp (-y * f'))) (-y * Real.sigmoid (-y * f)) f := by
  have h1 : HasDerivAt (fun f' : ℝ => -y * f') (-y) f := by
    simpa using (hasDerivAt_id f).const_mul (-y)
  have h2 := h1.exp
  have h3 := h2.const_add (1 : ℝ)
  have hpos : (1 : ℝ) + Real.exp (-y * f) ≠ 0 := by positivity
  have h4 := h3.log hpos
  convert h4 using 1
  rw [Real.sigmoid_def, Real.exp_neg (-y * f)]
  have hexp_pos : (0 : ℝ) < Real.exp (-y * f) := Real.exp_pos _
  have hexp_ne : Real.exp (-y * f) ≠ 0 := hexp_pos.ne'
  have h1e_ne : (1 : ℝ) + Real.exp (-y * f) ≠ 0 := by positivity
  have h1einv_ne : (1 : ℝ) + (Real.exp (-y * f))⁻¹ ≠ 0 := by positivity
  field_simp
  ring

/-- Concrete Example (Exponential Loss): for `ℓ(f,y) = exp(-y f)`, the generalized residual is
`∂_f ℓ(f,y) = -y exp(-y f)`. -/
theorem hasDerivAt_exponentialLoss (f y : ℝ) :
    HasDerivAt (fun f' => Real.exp (-y * f')) (-y * Real.exp (-y * f)) f := by
  have h1 : HasDerivAt (fun f' : ℝ => -y * f') (-y) f := by
    simpa using (hasDerivAt_id f).const_mul (-y)
  have h2 := h1.exp
  convert h2 using 1
  ring

/-- The gradient of the generalized empirical risk with respect to parameters:
  `∇_θ L(θ) = (1 / m) ∑_α r^α(θ) ∇_θ f(x^α; θ)`. -/
theorem gradient_generalizedRisk (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ)
    (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hf : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ)
    (hℓ : ∀ α : Fin m, HasDerivAt (fun f' => ℓ f' (y α))
      (generalizedResidual ℓ f X y θ α) (f (X α) θ)) :
    gradient (generalizedEmpiricalRisk ℓ f X y) θ =
      (m : ℝ)⁻¹ • ∑ α : Fin m, (generalizedResidual ℓ f X y θ α) • tangentFeature f (X α) θ := by
  have h_term : ∀ α ∈ (Finset.univ : Finset (Fin m)),
      HasFDerivAt (fun θ' => ℓ (f (X α) θ') (y α))
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P))
          ((generalizedResidual ℓ f X y θ α) • tangentFeature f (X α) θ)) θ := by
    intro α _
    exact hasFDerivAt_generalizedLoss_term θ (hf α) (hℓ α)
  have h_sum := HasFDerivAt.sum (u := Finset.univ) (A := fun α θ' => ℓ (f (X α) θ') (y α)) h_term
  have h_sum_eq : (∑ α ∈ (Finset.univ : Finset (Fin m)), fun θ' => ℓ (f (X α) θ') (y α)) =
      (fun θ' => ∑ α : Fin m, ℓ (f (X α) θ') (y α)) := by
    ext θ'
    simp only [Finset.sum_apply]
  rw [h_sum_eq] at h_sum
  have h_scaled := h_sum.const_smul (m : ℝ)⁻¹
  have h_risk_eq : generalizedEmpiricalRisk ℓ f X y =
      fun θ' => (m : ℝ)⁻¹ * ∑ α : Fin m, ℓ (f (X α) θ') (y α) := rfl
  rw [h_risk_eq]
  have h_grad : HasGradientAt (fun θ' => (m : ℝ)⁻¹ * ∑ α : Fin m, ℓ (f (X α) θ') (y α))
      ((m : ℝ)⁻¹ • ∑ α : Fin m, (generalizedResidual ℓ f X y θ α) • tangentFeature f (X α) θ)
      θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h_scaled using 1
    ext v
    simp only [smul_apply, sum_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul,
      inner_smul_left, starRingEnd_apply, star_trivial, sum_inner, Finset.mul_sum]
  exact h_grad.gradient

/-- Step 2 (Substitution of Gradient Flow Law, Generalized Loss):
Insert the continuous gradient flow parameter ODE `∂_t θ(t) = -∇_θ L(θ(t))`:
  `∂_t f^α(t) = - ⟨∇_θ f(x^α; θ(t)), ∇_θ L(θ(t))⟩`. -/
theorem gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t)) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      (-⟪tangentFeature f (X α) (θ_traj t),
        gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)⟫) t := by
  have h := hasDerivAt_trainingOutputs_coord f X θ_traj
    (fun s => -gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj s)) t α hdiff hflow
  rw [inner_neg_right] at h
  exact h

/-- Step 3 (Insertion of Generalized Loss Gradient):
Substitute `∇_θ L(θ(t)) = (1/m) ∑_β r^β(t) ∇_θ f(x^β; θ(t))` into the rate of change:
  `∂_t f^α(t) = - (1/m) ∑_β ⟨∇_θ f^α(θ(t)), ∇_θ f^β(θ(t))⟩ r^β(t)`. -/
theorem gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (α : Fin m)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (generalizedResidual ℓ f X y (θ_traj t)) β) t := by
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad ℓ f X y t hflow α (hf α)
  rw [gradient_generalizedRisk ℓ f X y (θ_traj t) hf hℓ] at h
  have h_inner : -⟪tangentFeature f (X α) (θ_traj t),
      (m : ℝ)⁻¹ • ∑ β : Fin m,
        (generalizedResidual ℓ f X y (θ_traj t) β) • tangentFeature f (X β) (θ_traj t)⟫ =
      - (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (generalizedResidual ℓ f X y (θ_traj t)) β := by
    rw [inner_smul_right, inner_sum]
    simp only [inner_smul_right]
    rw [neg_mul]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [h_inner] at h
  exact h

/-- Step 4 (Assembly with Empirical NTK, Generalized Loss):
Recognizing the empirical NTK matrix entries `K_t^{α β} = ⟨∇_θ f(x^α; θ(t)), ∇_θ f(x^β; θ(t))⟩`:
  `∂_t f^α(t) = - (1/m) ∑_β K_t^{α β} r^β(t)`. -/
theorem gradient_flow_generalizedOutput_coord_ode
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (α : Fin m)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        (generalizedResidual ℓ f X y (θ_traj t)) β) t := by
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner ℓ f X y t hflow α hf hℓ
  have h_ntk : ∀ β : Fin m,
      ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ =
      empiricalNTKMatrix f X (θ_traj t) α β := by
    intro β
    exact (empiricalNTKMatrix_apply f X (θ_traj t) α β).symm
  simp_rw [h_ntk] at h
  exact h

/-- Step 5 (Generalized Output Evolution):
Along continuous gradient flow under an arbitrary differentiable pointwise loss `ℓ`, the training
output vector satisfies:
  `∂_t f(t) = - (1/m) K_t r(t)`,
where `r(t)` is the generalized residual vector `r^α(t) = ∂_f ℓ(f^α(t), y^α)`. -/
theorem gradient_flow_generalizedOutput_vector_ode
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => WithLp.toLp 2 (fun α => f (X α) (θ_traj s)))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
          (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t := by
  rw [hasDerivAt_euclideanSpace]
  intro α
  have h_coord := gradient_flow_generalizedOutput_coord_ode ℓ f X y t hflow α hf hℓ
  have h_eq : - (m : ℝ)⁻¹ *
      ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        (generalizedResidual ℓ f X y (θ_traj t)) β =
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
          (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) : EuclideanSpace ℝ (Fin m)) α := by
    change - (m : ℝ)⁻¹ *
      ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        (generalizedResidual ℓ f X y (θ_traj t)) β =
      (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) α
    have h_row : (empiricalNTKMatrix f X (θ_traj t)).row α =
      empiricalNTKMatrix f X (θ_traj t) α := rfl
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply, dotProduct, h_row]
  rw [h_eq] at h_coord
  exact h_coord

/-- Step 2 (Substitution of Gradient Flow Law):
Insert the continuous gradient flow parameter ODE `∂_t θ(t) = -∇_θ L(θ(t))`:
  `∂_t f^α(t) = - ⟨∇_θ f(x^α; θ(t)), ∇_θ L(θ(t))⟩`. -/
theorem gradient_flow_output_coord_deriv_eq_inner_grad
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t)) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      (-⟪tangentFeature f (X α) (θ_traj t), gradient (mseLoss f X y) (θ_traj t)⟫) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow ⊢
  exact gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad _ f X y t hflow α hdiff

/-- Step 3 (Insertion of Loss Gradient):
Substitute `∇_θ L(θ(t)) = (1 / m) ∑_β (f^β(t) - y^β) ∇_θ f(x^β; θ(t))` into the rate of change:
  `∂_t f^α(t) = - ⟨∇_θ f^α(θ(t)), (1 / m) ∑_β (f^β(t) - y^β) ∇_θ f^β(θ(t))⟩`
              `= - (1 / m) ∑_β ⟨∇_θ f^α(θ(t)), ∇_θ f^β(θ(t))⟩ (f^β(t) - y^β)`. -/
theorem gradient_flow_output_coord_deriv_eq_sum_inner
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t) (α : Fin m)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (trainingResidual f X y (θ_traj t)) β) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner _ f X y t hflow α hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 4 (Assembly with Empirical NTK):
Recognizing the empirical NTK matrix entries `K_t^{α β} = ⟨∇_θ f(x^α; θ(t)), ∇_θ f(x^β; θ(t))⟩`:
  `∂_t f^α(t) = - (1 / m) ∑_β K_t^{α β} (f^β(t) - y^β) = - (1 / m) ∑_β K_t^{α β} r^β(t)`. -/
theorem gradient_flow_output_coord_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t) (α : Fin m)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => (WithLp.toLp 2 (fun α => f (X α) (θ_traj s))) α)
      (- (m : ℝ)⁻¹ *
        ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
          (trainingResidual f X y (θ_traj t)) β) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_coord_ode _ f X y t hflow α hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 5 (Matrix-Vector Formulation for Output Vector), at learning rate `η`:
if the parameters move by `∂_t θ(t) = -η ∇_θ L(θ(t))`, the training output vector satisfies
  `∂_t f(t) = - (η / m) K_t r(t)`.
Gradient flow proper is the case `η = 1`; for the rate-`η` flow `K_t` is the same kernel and `η`
only rescales time. -/
theorem gradient_flow_output_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (η : ℝ) {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-(η • gradient (mseLoss f X y) (θ_traj t))) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => WithLp.toLp 2 (fun α => f (X α) (θ_traj s)))
      (WithLp.toLp 2 (-(η * (m : ℝ)⁻¹) •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  rw [hasDerivAt_euclideanSpace]
  intro α
  have h := hasDerivAt_trainingOutputs_coord f X θ_traj
    (fun s => -(η • gradient (mseLoss f X y) (θ_traj s))) t α (hdiff α) hflow
  convert h using 1
  have hR : ⟪tangentFeature f (X α) (θ_traj t), -(η • gradient (mseLoss f X y) (θ_traj t))⟫ =
      -(η * (m : ℝ)⁻¹) * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        trainingResidual f X y (θ_traj t) β := by
    rw [gradient_mseLoss f X y _ hdiff, inner_neg_right, inner_smul_right, inner_smul_right,
      inner_sum]
    simp only [inner_smul_right, empiricalNTKMatrix_apply]
    simp_rw [mul_comm ((trainingResidual f X y (θ_traj t)).ofLp _)]
    ring
  rw [hR]
  simp [Matrix.mulVec, dotProduct]

/-- Step 5 (Matrix-Vector Formulation with Explicit `f(t) - y`):
Along continuous gradient flow, the training output vector satisfies:
  `∂_t f(t) = - (1 / m) K_t (f(t) - y)`. -/
theorem gradient_flow_output_vector_ode_sub_y
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => WithLp.toLp 2 (fun α => f (X α) (θ_traj s)))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        ((WithLp.toLp 2 (fun α => f (X α) (θ_traj t))) - y).ofLp))) t := by
  have h := gradient_flow_output_vector_ode f X y 1 t (by rwa [one_smul]) hdiff
  rw [one_mul] at h
  exact h

/-- Step 5 (Matrix-Vector Formulation for Residual Vector):
Function-space residual ODE under gradient flow:
  `∂_t r(t) = - (1 / m) K_t r(t)`. -/
theorem gradient_flow_residual_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  have h_out := gradient_flow_output_vector_ode f X y 1 t (by rwa [one_smul]) hdiff
  rw [one_mul] at h_out
  have h_sub := h_out.sub_const y
  convert h_sub using 1
  ext s
  rfl

/-! ### Proposition 2.17: Risk Dissipation Identity

Along continuous gradient flow for the generalized empirical risk `L(θ) = (1/m) ∑_α ℓ(f^α(θ), y^α)`,
the instantaneous rate of risk dissipation is governed entirely by the empirical NTK Gram matrix
acting on the residual vector:
  `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`.
Since `K_t` is positive semidefinite (`empiricalNTKMatrix_quad_form_nonneg` in
`NTK.Shallow.DatasetNTK`), the empirical risk is monotonically non-increasing along gradient flow.
If the smallest Rayleigh quotient of `K_t` is bounded below by `lambda_min > 0`, the dissipation
rate is in addition bounded strictly away from zero whenever `r(t) ≠ 0`.
-/

/-- Step 1 (Chain Rule on Empirical Risk):
Along any curve `θ(t)` whose per-sample outputs `f^α(θ(t))` have known time derivatives `f'`, the
time derivative of the generalized empirical risk is the residual-weighted sum of output
derivatives:
  `∂_t L(θ(t)) = (1/m) ∑_α r^α(t) ∂_t f^α(t) = (1/m) r(t)ᵀ ∂_t f(t)`. -/
theorem hasDerivAt_generalizedEmpiricalRisk_coord_sum
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ_traj : ℝ → EuclideanSpace ℝ (Fin P)) (t : ℝ)
    (f' : Fin m → ℝ)
    (hf' : ∀ α : Fin m,
      HasDerivAt (fun s => WithLp.toLp 2 (fun β => f (X β) (θ_traj s)) α) (f' α) t)
    (hℓ : ∀ α : Fin m, HasDerivAt (fun v => ℓ v (y α))
      (generalizedResidual ℓ f X y (θ_traj t) α) (WithLp.toLp 2 (fun α => f (X α) (θ_traj t)) α)) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      ((m : ℝ)⁻¹ * ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ f')) t := by
  have h_term : ∀ α : Fin m,
      HasDerivAt ((fun v => ℓ v (y α)) ∘ fun s => WithLp.toLp 2 (fun α => f (X α) (θ_traj s)) α)
        (generalizedResidual ℓ f X y (θ_traj t) α * f' α) t :=
    fun α => HasDerivAt.comp t (hℓ α) (hf' α)
  have h_sum : HasDerivAt
      (fun s => ∑ α : Fin m,
        ((fun v => ℓ v (y α)) ∘ fun s' => WithLp.toLp 2 (fun β => f (X β) (θ_traj s')) α) s)
      (∑ α : Fin m, generalizedResidual ℓ f X y (θ_traj t) α * f' α) t :=
    HasDerivAt.fun_sum (fun α _ => h_term α)
  have h_scaled := h_sum.const_mul (m : ℝ)⁻¹
  have h_rhs_eq :
      (m : ℝ)⁻¹ * ∑ α : Fin m, generalizedResidual ℓ f X y (θ_traj t) α * f' α =
        (m : ℝ)⁻¹ * ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ f') := by
    congr 1
  rw [h_rhs_eq] at h_scaled
  exact h_scaled

/-- Step 2 (Substitution of Output Dynamics):
Insert the generalized output dynamics `∂_t f(t) = - (1/m) K_t r(t)` into the risk derivative
formula, and simplify the resulting double sum into the quadratic form `r(t)ᵀ K_t r(t)`.

**Proposition 2.17 (Risk Dissipation Identity).** Along continuous gradient flow, the instantaneous
rate of risk dissipation satisfies:
  `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`. -/
theorem risk_dissipation_identity
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun v => ℓ v (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      (-(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t := by
  set r := generalizedResidual ℓ f X y (θ_traj t) with hr_def
  set K := empiricalNTKMatrix f X (θ_traj t) with hK_def
  set f' : Fin m → ℝ := fun α => - (m : ℝ)⁻¹ * ∑ β : Fin m, K α β * r β with hf'_def
  have hf' : ∀ α : Fin m,
      HasDerivAt (fun s => WithLp.toLp 2 (fun β => f (X β) (θ_traj s)) α) (f' α) t := by
    intro α
    exact gradient_flow_generalizedOutput_coord_ode ℓ f X y t hflow α hf hℓ
  have h_step1 := hasDerivAt_generalizedEmpiricalRisk_coord_sum ℓ f X y θ_traj t f' hf' hℓ
  have h_val : (m : ℝ)⁻¹ * (r.ofLp ⬝ᵥ f') =
      -(((m : ℝ) ^ 2)⁻¹) * (r.ofLp ⬝ᵥ (K *ᵥ r.ofLp)) := by
    have h_sum_eq : r.ofLp ⬝ᵥ f' = - (m : ℝ)⁻¹ * (r.ofLp ⬝ᵥ (K *ᵥ r.ofLp)) := by
      have h_row : ∀ α : Fin m, K.row α = K α := fun _ => rfl
      simp only [dotProduct, hf'_def, Matrix.mulVec_apply, h_row, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      ring_nf
    rw [h_sum_eq]
    ring
  rw [h_val] at h_step1
  exact h_step1

/-- **Geometric and Stability Implications.**
Since `K_t` is positive semidefinite for any parameter state (`empiricalNTKMatrix_quad_form_nonneg`,
`NTK.Shallow.DatasetNTK`), the quadratic form `r(t)ᵀ K_t r(t)` is non-negative, so the empirical
risk is
monotonically non-increasing along gradient flow: `∂_t L(θ(t)) ≤ 0`. -/
theorem risk_dissipation_nonpos
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun v => ℓ v (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      (-(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t ∧
      -(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) ≤ 0 := by
  refine ⟨risk_dissipation_identity ℓ f X y t hflow hf hℓ, ?_⟩
  have h_nonneg := empiricalNTKMatrix_quad_form_nonneg f X (θ_traj t)
    (generalizedResidual ℓ f X y (θ_traj t)).ofLp
  have h_sq_nonneg : (0 : ℝ) ≤ ((m : ℝ) ^ 2)⁻¹ := by positivity
  have h_mul := mul_nonneg h_sq_nonneg h_nonneg
  linarith

/-- **Geometric and Stability Implications (Rayleigh-Ritz Bound).**
If the smallest Rayleigh quotient of `K_t` is bounded below by `lambda_min > 0`
(`lambda_min * ‖v‖² ≤ vᵀ K_t v` for all `v`), the risk dissipation rate is bounded away
from zero whenever `r(t) ≠ 0`:
  `∂_t L(θ(t)) ≤ - (lambda_min / m²) ‖r(t)‖²`. -/
theorem risk_dissipation_le_of_rayleighRitz
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun v => ℓ v (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t)))
    (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      (-(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t ∧
      -(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) ≤
      -(lambda_min / (m : ℝ) ^ 2) * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2 := by
  refine ⟨risk_dissipation_identity ℓ f X y t hflow hf hℓ, ?_⟩
  have h1 := h_rr (generalizedResidual ℓ f X y (θ_traj t))
  have h_sq_nonneg : (0 : ℝ) ≤ ((m : ℝ) ^ 2)⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 h_sq_nonneg
  have h3 : ((m : ℝ) ^ 2)⁻¹ * (lambda_min * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2) =
      (lambda_min / (m : ℝ) ^ 2) * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2 := by ring
  rw [h3] at h2
  linarith

/-! ### Kinetic energy along gradient flow

For the flow `θ' = -∇L(θ)` the speed is `‖θ'‖ = ‖∇L(θ)‖`, and the chain rule gives
`∂_t L(θ) = -‖θ'‖²`. Evaluating the gradient with `gradient_generalizedRisk` identifies the same
quantity with the kernel quadratic form of Proposition 2.17:
  `‖θ'(t)‖² = (1/m²) r(t)ᵀ K_t r(t)`.
Integrating over `[0, T]` gives the kinetic-energy form of the risk drop. The generic part lives in
`ConvexOpt.ForwardGFTrajectory`; here it is only tied to the empirical NTK. -/

/-- The squared norm of a linear combination is the Gram quadratic form of its coefficients:
`‖∑ c_α v_α‖² = cᵀ G c` with `G_{αβ} = ⟪v_α, v_β⟫`. -/
lemma norm_sq_sum_smul_eq_dotProduct {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : Fin m → ℝ) (v : Fin m → E) :
    ‖∑ α : Fin m, c α • v α‖ ^ 2 = c ⬝ᵥ (Matrix.of (fun α β => ⟪v α, v β⟫) *ᵥ c) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner, dotProduct]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [inner_sum, Matrix.mulVec_apply, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [inner_smul_left, inner_smul_right, Matrix.row_apply, Matrix.of_apply,
    starRingEnd_apply, star_trivial]
  ring

/-- **Gradient energy as a kernel quadratic form.** For any differentiable pointwise loss,
`‖∇_θ L(θ)‖² = (1/m²) r(θ)ᵀ K(θ) r(θ)`. Together with the chain rule `∂_t L = -‖θ'‖²` this
re-derives `risk_dissipation_identity` without evaluating the output dynamics. -/
theorem norm_sq_gradient_generalizedRisk (ℓ : ℝ → ℝ → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P))
    (hf : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ)
    (hℓ : ∀ α : Fin m, HasDerivAt (fun f' => ℓ f' (y α))
      (generalizedResidual ℓ f X y θ α) (f (X α) θ)) :
    ‖gradient (generalizedEmpiricalRisk ℓ f X y) θ‖ ^ 2 =
      ((m : ℝ) ^ 2)⁻¹ * ((generalizedResidual ℓ f X y θ).ofLp ⬝ᵥ
        (empiricalNTKMatrix f X θ *ᵥ (generalizedResidual ℓ f X y θ).ofLp)) := by
  rw [gradient_generalizedRisk ℓ f X y θ hf hℓ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_sq_sum_smul_eq_dotProduct]
  have hK : Matrix.of (fun α β => ⟪tangentFeature f (X α) θ, tangentFeature f (X β) θ⟫) =
      empiricalNTKMatrix f X θ := by
    ext α β
    simp [empiricalNTKMatrix_apply]
  rw [hK, inv_pow]

/-- Squared-loss case: `‖∇_θ L(θ)‖² = (1/m²) r(θ)ᵀ K(θ) r(θ)`. -/
theorem norm_sq_gradient_mseLoss (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) :
    ‖gradient (mseLoss f X y) θ‖ ^ 2 =
      ((m : ℝ) ^ 2)⁻¹ * ((trainingResidual f X y θ).ofLp ⬝ᵥ
        (empiricalNTKMatrix f X θ *ᵥ (trainingResidual f X y θ).ofLp)) := by
  have h := norm_sq_gradient_generalizedRisk (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y θ
    hdiff (fun β => hasDerivAt_squaredLoss_generalizedResidual f X y θ β)
  rwa [generalizedEmpiricalRisk_squaredLoss_eq_mseLoss,
    generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- **Kinetic energy of the training flow.** Along a forward gradient flow of the MSE loss, at every
positive time `‖θ'(t)‖² = (1/m²) r(t)ᵀ K_t r(t)`. -/
theorem norm_deriv_sq_eq_quadratic_form_of_forwardGF
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj) {t : ℝ} (ht : 0 < t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    ‖deriv θ_traj t‖ ^ 2 =
      ((m : ℝ) ^ 2)⁻¹ * ((trainingResidual f X y (θ_traj t)).ofLp ⬝ᵥ
        (empiricalNTKMatrix f X (θ_traj t) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp)) := by
  rw [hflow.norm_deriv_sq ht, norm_sq_gradient_mseLoss f X y _ hdiff]

/-- **Integrated kinetic energy.** Along a forward gradient flow of the MSE loss on `[0, T]`,
  `L(θ(0)) - L(θ(T)) = ∫₀ᵀ (1/m²) r(t)ᵀ K_t r(t) dt = ∫₀ᵀ ‖θ'(t)‖² dt`. -/
theorem mseLoss_sub_eq_integral_quadratic_form
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj) {T : ℝ} (hT : 0 ≤ T)
    (hdiff : ∀ t ∈ Set.Icc 0 T, ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    mseLoss f X y (θ_traj 0) - mseLoss f X y (θ_traj T) =
      ∫ t in (0 : ℝ)..T, ((m : ℝ) ^ 2)⁻¹ * ((trainingResidual f X y (θ_traj t)).ofLp ⬝ᵥ
        (empiricalNTKMatrix f X (θ_traj t) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp)) ∧
    mseLoss f X y (θ_traj 0) - mseLoss f X y (θ_traj T) =
      ∫ t in (0 : ℝ)..T, ‖deriv θ_traj t‖ ^ 2 := by
  have hL : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ (mseLoss f X y) (θ_traj t) := fun t ht =>
    (hasGradientAt_mseLoss f X y (θ_traj t) (hdiff t ht)).differentiableAt
  refine ⟨?_, (hflow.integral_norm_deriv_sq_eq_sub hT hL).symm⟩
  rw [← hflow.integral_norm_sq_gradient_eq_sub hT hL]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hT] at ht
  exact norm_sq_gradient_mseLoss f X y _ (hdiff t ht)

/-- **Coordinate form of the training flow.** Along a forward gradient flow of the MSE loss, every
parameter coordinate moves by `∂_t θ_k = -(1/m) [J(θ)ᵀ r(θ)]_k = -(1/m) ∑_α r^α ∂_{θ_k} f^α`.
Network-specific instances (the `a_i` and `W_{ij}` equations) follow by reading off the Jacobian
entry. -/
theorem hasDerivAt_coord_of_forwardGF
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj) {t : ℝ} (ht : 0 < t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) (k : Fin P) :
    HasDerivAt (fun s => θ_traj s k)
      (-((m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual f X y (θ_traj t) α *
        outputJacobian f X (θ_traj t) α k)) t := by
  have h := (hasDerivAt_euclideanSpace _ _ _).1 (hflow.ode t ht) k
  have hk := gradient_mseLoss_apply_j f X y (θ_traj t) hdiff k
  rw [Matrix.mulVec_apply, dotProduct] at hk
  simp only [PiLp.neg_apply, hk] at h
  convert h using 2
  refine congrArg _ (Finset.sum_congr rfl fun α _ => ?_)
  simp [Matrix.transpose_apply, Matrix.row_apply, mul_comm]

end NTK

end
