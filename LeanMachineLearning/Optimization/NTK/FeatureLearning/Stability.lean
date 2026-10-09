/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.FeatureLearning.ScalingRegimes
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.KernelStability
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.JacobianBounds
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.JointInit

/-!
# Feature learning: what stays order one and what moves

Two consequences of the scaling `γ`, `η` of `featureLearningNetwork`, both reusing the lazy-training
development of the NTK chapters rather than re-proving it.

## Main results and proof outline

* `tendsto_initial_trainingResidual_add_target` (**initial residual stability**): if the knob `γ n`
  tends to infinity (for instance the mean-field value `√n`) then, at Gaussian initialization,
  `r(0) = f(0) - y = -y + o_P(1)`.  Indeed `r(0) + y = γ⁻¹ (r₁(0) + y)`
  (`trainingResidual_featureLearningNetwork_add`), where `r₁` is the residual of `netFromParams` on
  the scaled dataset; `exists_initial_residual_radius` says that `r₁` is bounded in probability
  uniformly in the width, so dividing by `γ n → ∞` sends it to `0`.
* `kernel_drift_oneStep_le` (**kernel drift is controlled by the feature motion**): after one
  gradient step `θ₁ = θ₀ - η ∇L`, the normalized empirical NTK moves by at most
  `C · |η / (γ √n)|`.  This is the displacement `‖θ₁ - θ₀‖ ≤ (|η|/γ) · m⁻¹ M ρ`
  (`norm_oneStep_displacement_le`), the `K / √n` Lipschitz constant of the Jacobian
  (`outputJacobian_netFromParams_frobenius_sub_le`) and the kernel Lipschitz bound
  `‖K(θ₁) - K(θ₂)‖ ≤ 2 M L_J ‖θ₁ - θ₂‖` (`empiricalNTKMatrix_sub_le_of_jacobian_lipschitz`).  The
  factor `|η / (γ √n)|` is the square root of the feature motion of `Criterion`.
* `tendsto_kernel_drift_of_isLittleO` (**kernel freeze**): if `η = o(γ √n)`, in particular in the
  NTK regime `γ = 1`, `η = O(1)` (`isLittleO_sqrt_of_lazy_learningRate`), the kernel drift tends to
  zero.

The converse cannot be obtained from the feature-learning criterion alone: a Gram matrix can stay
put while every feature moves (a rotation of the hidden layer), so non-freezing needs a
non-degeneracy hypothesis on the activation and the data, which is not formalized.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Matrix Matrix.Norms.Frobenius Topology

namespace NTK

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

variable {φ : ℝ → ℝ} {n d m : ℕ}

/-! ### Initial residual stability -/

/-- **Initial residual stability.** Let the scaling knob `γ n` tend to infinity (the mean-field
value `γ n = √n` is the case of interest).  Then for every `ε > 0` the probability, under the
Gaussian initialization `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`, that the initial residual `r(0) = f(0) - y` of
`featureLearningNetwork (γ n)` is at distance at least `ε` from `-y` tends to `0`: the initial
prediction is negligible and the driving error `r(0)` is `-y + o_P(1) = Θ_P(1)`. -/
theorem tendsto_initial_trainingResidual_add_target
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (γ : ℕ → ℝ) (hγ : Tendsto γ atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1))
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ε ≤
          ‖trainingResidual (featureLearningNetwork (γ n) φ n d) X y (packParams p.1 p.2) + y‖})
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨R, -, hR⟩ := exists_initial_residual_radius φ X y hφ_meas hφ_L2 hδ
  filter_upwards [hγ.eventually_gt_atTop ((R + ‖y‖) / ε), hγ.eventually_gt_atTop 0]
    with n hn hpos
  refine le_trans (measure_mono ?_) (hR n)
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [trainingResidual_featureLearningNetwork_add, norm_smul, norm_inv,
    Real.norm_of_nonneg hpos.le, le_inv_mul_iff₀ hpos] at hp
  have h2 : R + ‖y‖ < γ n * ε := by rwa [div_lt_iff₀ hε] at hn
  have h3 := norm_add_le (trainingResidual (netFromParams φ n d)
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)) y
  linarith

/-! ### Kernel drift after one gradient step -/

section KernelDrift

/-- **Parameter displacement of one gradient step.** For `θ₁ = θ₀ - η ∇L(θ₀)` with
`L = mseLoss (featureLearningNetwork γ φ n d) X y`, `‖θ₁ - θ₀‖ ≤ (|η| / γ) · m⁻¹ M ρ`, where `M`
bounds the Jacobian of `netFromParams` on the scaled dataset and `ρ` bounds the residual: the
scaling knob `γ` enters only through the factor `γ⁻¹` of the gradient. -/
lemma norm_oneStep_displacement_le (hφ : Differentiable ℝ φ) {γ : ℝ} (hγ : 0 < γ) (η : ℝ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (θ₀ θ₁ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hstep : θ₁ = θ₀ - η • gradient (mseLoss (featureLearningNetwork γ φ n d) X y) θ₀)
    {M ρ : ℝ}
    (hJ₀ : ‖outputJacobian (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₀‖ ≤ M)
    (hr : ‖trainingResidual (featureLearningNetwork γ φ n d) X y θ₀‖ ≤ ρ) :
    ‖θ₁ - θ₀‖ ≤ |η| / γ * ((m : ℝ)⁻¹ * M * ρ) := by
  have hg := gradient_mseLoss_norm_le (featureLearningNetwork γ φ n d) X y θ₀
    fun α => differentiableAt_featureLearningNetwork γ hφ _ _
  rw [outputJacobian_featureLearningNetwork, norm_smul, norm_inv,
    Real.norm_of_nonneg hγ.le] at hg
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ₀
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hr
  have hdisp : ‖θ₁ - θ₀‖ = |η| * ‖gradient (mseLoss (featureLearningNetwork γ φ n d) X y) θ₀‖ := by
    rw [hstep, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
  rw [hdisp]
  calc |η| * ‖gradient (mseLoss (featureLearningNetwork γ φ n d) X y) θ₀‖
      ≤ |η| * ((m : ℝ)⁻¹ * (γ⁻¹ * M) * ρ) := by
        refine mul_le_mul_of_nonneg_left (hg.trans ?_) (abs_nonneg _)
        gcongr
    _ = |η| / γ * ((m : ℝ)⁻¹ * M * ρ) := by ring

/-- **The kernel drift of one gradient step is controlled by the feature motion.** Let
`θ₁ = θ₀ - η ∇L(θ₀)` be one gradient step on `mseLoss (featureLearningNetwork γ φ n d) X y`.
Suppose `φ` has `C₁`-bounded and `C₁`-Lipschitz-value derivative with `C₂`-Lipschitz derivative,
the readouts of `θ₁` are bounded by `R`, the Jacobian of `netFromParams` on the scaled dataset is
bounded by `M` at `θ₀` and `θ₁`, the initial residual by `ρ`, and `Kc` bounds the width-independent
Jacobian-Lipschitz constant of `outputJacobian_netFromParams_frobenius_sub_le`.  Then the
normalized empirical NTK `K = empiricalNTKMatrix (netFromParams φ n d)` of the scaled dataset moves
by at most `(2 M² ρ Kc / m) · |η / (γ √n)|`; the last factor is the square root of the feature
motion of `Criterion`. -/
theorem kernel_drift_oneStep_le (hn : 0 < n) (hφ : Differentiable ℝ φ) {C₁ C₂ R M ρ Kc : ℝ}
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hR : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hKc : Real.sqrt (∑ α : Fin m,
      (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, ((Real.sqrt (d : ℝ))⁻¹ * X α j) ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, ((Real.sqrt (d : ℝ))⁻¹ * X α j) ^ 2))) ≤ Kc)
    {γ : ℝ} (hγ : 0 < γ) (η : ℝ)
    (θ₀ θ₁ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hstep : θ₁ = θ₀ - η • gradient (mseLoss (featureLearningNetwork γ φ n d) X y) θ₀)
    (ha₁ : ∀ i : Fin n, |θ₁ (paramIndexEquiv n d (Sum.inr i))| ≤ R)
    (hJ₀ : ‖outputJacobian (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₀‖ ≤ M)
    (hJ₁ : ‖outputJacobian (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₁‖ ≤ M)
    (hr : ‖trainingResidual (featureLearningNetwork γ φ n d) X y θ₀‖ ≤ ρ) :
    ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₁ -
        empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₀‖ ≤
      (2 * M ^ 2 * ρ * Kc / m) * |η / (γ * Real.sqrt n)| := by
  have hdisp := norm_oneStep_displacement_le hφ hγ η X y θ₀ θ₁ hstep hJ₀ hr
  have hLip := outputJacobian_netFromParams_frobenius_sub_le φ n d m hn
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₁ θ₀ C₁ C₂ R hC₁ hC₂ hR hφ_lip hderiv_bound
    hderiv_lip (fun _ _ => hφ.differentiableAt) (fun _ _ => hφ.differentiableAt) ha₁
  dsimp only at hLip
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ₀
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hr
  have hKc0 : 0 ≤ Kc := (Real.sqrt_nonneg _).trans hKc
  have hLip' : ‖outputJacobian (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₁ - outputJacobian (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₀‖ ≤ (Kc / Real.sqrt n) * ‖θ₁ - θ₀‖ :=
    hLip.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hKc hsqrt.le) (norm_nonneg _))
  have hK := empiricalNTKMatrix_sub_le_of_jacobian_lipschitz (netFromParams φ n d)
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ₁ θ₀ M (Kc / Real.sqrt n) hJ₁ hJ₀ hLip'
  refine hK.trans ?_
  have h2 : 0 ≤ 2 * M * (Kc / Real.sqrt n) := by positivity
  refine (mul_le_mul_of_nonneg_left hdisp h2).trans_eq ?_
  rw [abs_div, abs_of_pos (mul_pos hγ hsqrt)]
  field_simp

/-- **Kernel freeze below the feature-learning scale.** Let `θ₁ n = θ₀ n - η n ∇L(θ₀ n)` be one
gradient step of the width-`n` network `featureLearningNetwork (γ n)`, with constants
`C₁ C₂ R M ρ Kc` uniform in the width as in `kernel_drift_oneStep_le`.  If the learning rate is
below the feature-learning scale, `η = o(γ √n)` (which excludes the criterion of
`featureLearning_criterion_iff_learningRate`), then the normalized empirical NTK drifts by `o(1)`:
the kernel is frozen at infinite width. -/
theorem tendsto_kernel_drift_of_isLittleO {C₁ C₂ R M ρ Kc : ℝ} (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hR : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hKc : Real.sqrt (∑ α : Fin m,
      (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, ((Real.sqrt (d : ℝ))⁻¹ * X α j) ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, ((Real.sqrt (d : ℝ))⁻¹ * X α j) ^ 2))) ≤ Kc)
    (γ η : ℕ → ℝ) (hγ : ∀ n, 0 < γ n)
    (θ₀ θ₁ : (n : ℕ) → EuclideanSpace ℝ (Fin (n * d + n)))
    (hstep : ∀ n, θ₁ n = θ₀ n -
      η n • gradient (mseLoss (featureLearningNetwork (γ n) φ n d) X y) (θ₀ n))
    (ha₁ : ∀ n (i : Fin n), |θ₁ n (paramIndexEquiv n d (Sum.inr i))| ≤ R)
    (hJ₀ : ∀ᶠ n : ℕ in atTop, ‖outputJacobian (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ₀ n)‖ ≤ M)
    (hJ₁ : ∀ᶠ n : ℕ in atTop, ‖outputJacobian (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ₁ n)‖ ≤ M)
    (hr : ∀ᶠ n : ℕ in atTop,
      ‖trainingResidual (featureLearningNetwork (γ n) φ n d) X y (θ₀ n)‖ ≤ ρ)
    (hlr : η =o[atTop] fun n : ℕ => γ n * Real.sqrt n) :
    Tendsto (fun n : ℕ =>
      ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ₁ n) -
        empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
          (θ₀ n)‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => |η n / (γ n * Real.sqrt n)|) atTop (𝓝 0) := by
    have h := (continuous_abs.tendsto 0).comp hlr.tendsto_div_nhds_zero
    rwa [abs_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hlim.const_mul (2 * M ^ 2 * ρ * Kc / m))
  filter_upwards [eventually_gt_atTop 0, hJ₀, hJ₁, hr] with n hn h0 h1 h2
  exact kernel_drift_oneStep_le hn hφ X y hC₁ hC₂ hR hφ_lip hderiv_bound hderiv_lip hKc (hγ n)
    (η n) (θ₀ n) (θ₁ n) (hstep n) (ha₁ n) h0 h1 h2

end KernelDrift

end NTK
