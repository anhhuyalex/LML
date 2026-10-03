/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.JointInit

/-!
# Two-layer network: end-to-end kernel-freeze bound

The Jacobian-norm and readout-weight concentrations combine through a union bound into a
high-probability event, on which the Jacobian Lipschitz bound propagates the Jacobian and readout
bounds through the displacement ball, giving `lazy_training_kernel_freeze_bound_of_gaussian_init`.

## Main results and proof outline

- `lazy_training_kernel_freeze_bound_of_gaussian_init` : the final, fully probabilistic end-to-end
kernel-freeze bound.
- `exists_measurableSet_initial_jacobian_and_readout_bounds` and
  `freeze_bound_of_initial_jacobian_and_readout_bounds` : the probabilistic and deterministic
  halves of `lazy_training_kernel_freeze_bound_of_gaussian_init`, split so that later theorems can
  reuse the measurable good event.

See `LeanMachineLearning.Optimization.NTK.Training.TwoLayer` for the overview of the whole
development.
-/

namespace NTK

open ConvexOpt MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

@[expose] public section

/-! ### End-to-End Kernel-Freeze Bound

Wires the packing bridge, the kernel Lipschitz propagation, the Jacobian concentration and Lipschitz
bounds and the lazy-training bootstrap together with the Gaussian-initialized two-layer network:
the Jacobian-norm concentration and the entrywise readout-weight concentration (both at `θ₀`)
combine via a union bound into one high-probability event; on that event, the Jacobian Lipschitz
bound propagates
both the Jacobian norm and the readout-weight bound through the displacement ball (the same
"ball propagation" pattern `rayleigh_quotient_lower_bound_of_displacement`/`h_rr_ball` already use
in `NTK.Training.GradientFlow.Bootstrap`); the result feeds directly into
`lazy_training_kernel_freeze_bound_of_ball_hypotheses`.
-/

/-- Deterministic ball-propagation of an entrywise readout-weight bound: if `θ₀`'s readout
weight `a i` is bounded by `R₀` and `θ` is within displacement `r` of `θ₀`, then `θ`'s readout
weight `a i` is bounded by `R₀ + r`. This is what lets a concentration bound established only at
the random initialization `θ₀` (readout-weight concentration) supply the uniform-over-a-ball bound
that the Jacobian Lipschitz
theorem needs. -/
private lemma abs_unpackA_le_of_displacement {n d : ℕ}
    (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n)))
    (i : Fin n) (R₀ r : ℝ) (h₀ : |unpackA θ₀ i| ≤ R₀) (hr : ‖θ - θ₀‖ ≤ r) :
    |unpackA θ i| ≤ R₀ + r := by
  have hproj : |(θ - θ₀).ofLp (idxA i)| ≤ ‖θ - θ₀‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (θ - θ₀) (idxA i)
  have heq : unpackA θ i - unpackA θ₀ i = (θ - θ₀).ofLp (idxA i) := by dsimp [unpackA]
  have hdiff : |unpackA θ i - unpackA θ₀ i| ≤ r := heq ▸ hproj.trans hr
  have h1 := abs_le.mp h₀
  have h2 := abs_le.mp hdiff
  rw [abs_le]
  constructor <;> linarith

/-- **Gaussian-initialization good event for the kernel-freeze bound.** There is a measurable event
`E` of `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-probability `≥ 1 - 2δ` on which both the initial Jacobian norm
and every
readout weight are controlled (the Jacobian-norm concentration and the readout-weight
concentration's entrywise
readout-weight concentration, combined by a union bound). Deterministic consequences of membership
in `E` are in `freeze_bound_of_initial_jacobian_and_readout_bounds`. -/
lemma exists_measurableSet_initial_jacobian_and_readout_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (hφ : Differentiable ℝ φ) (hφ_meas : Measurable φ) (hderiv_meas : Measurable (deriv φ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (M₀ : ℝ)
    (hE1 : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n =>
            gaussianReal 0 1)).real {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ M₀} ≥ 1 - δ) :
    ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)),
      MeasurableSet E ∧ ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
          gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - 2 *
              δ ∧
      ∀ p ∈ E,
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
          M₀ ∧
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) := by
  have hE2 := initMeasure_forall_abs_readout_ge n d hn hδ hδ1
  have hpi_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1 i j) := by
    intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  have hpre_meas : ∀ α : Fin m, ∀ i : Fin n,
      Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1 i ⬝ᵥ X α) := by
    intro α i
    unfold dotProduct
    exact Finset.measurable_sum _ (fun j _ => (hpi_meas i j).mul measurable_const)
  have hE1_meas : MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
        M₀} := by
    have hmeas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2) := by
      have heq : (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2) =
          (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
            (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d,
              (gradW φ n d (X α) (packParams p.1 p.2) i j) ^ 2) +
            ∑ α : Fin m, ∑ i : Fin n, (gradA φ n d (X α) (packParams p.1 p.2) i) ^ 2) := by
        funext p
        exact outputJacobian_netFromParams_frobenius_norm_sq φ n d m X (packParams p.1 p.2)
          (fun α i => hφ.differentiableAt)
      rw [heq]
      simp only [gradW, gradA, unpackW_packParams, unpackA_packParams]
      refine Measurable.add ?_ ?_
      · exact Finset.measurable_sum _ (fun α _ => Finset.measurable_sum _ (fun i _ =>
          Finset.measurable_sum _ (fun j _ => (((measurable_const.mul
            ((measurable_pi_apply i).comp measurable_snd)).mul
            (hderiv_meas.comp (hpre_meas α i))).mul measurable_const).pow_const 2)))
      · exact Finset.measurable_sum _ (fun α _ => Finset.measurable_sum _ (fun i _ =>
          (measurable_const.mul (hφ_meas.comp (hpre_meas α i))).pow_const 2))
    have hmeas' : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖) := by
      have heq2 : (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖) =
          fun p => Real.sqrt
            (‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2) := by
        funext p; rw [Real.sqrt_sq (norm_nonneg _)]
      rw [heq2]
      exact Real.continuous_sqrt.measurable.comp hmeas
    exact measurableSet_le hmeas' measurable_const
  have hE2_meas : MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} := by
    have hset : {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} =
        ⋂ i : Fin n, {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} := by
      ext p; simp
    rw [hset]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (continuous_abs.measurable.comp ((measurable_pi_apply i).comp measurable_snd))
      measurable_const)
  have hcombined := measureReal_inter_ge_of_ge ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin
      d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)) hE1_meas hE2_meas hE1 hE2
  have hδ2 : (1 : ℝ) - δ - δ = 1 - 2 * δ := by ring
  rw [hδ2] at hcombined
  exact ⟨_, hE1_meas.inter hE2_meas, hcombined, fun p hp => hp⟩

/-- **Jacobian bounds on a ball around a good initialization.** If at `θ₀ = packParams W a` the
Jacobian norm and all readout weights satisfy the Jacobian-norm and readout-weight concentration
bounds, then on the closed ball of
radius `r` around `θ₀` the output Jacobian is `M`-bounded and `L_J`-Lipschitz (relative to `θ₀`),
for any `M`, `L_J` dominating the concrete formulas. Shared by the gap and no-gap bootstraps. -/
lemma jacobian_ball_bounds_of_initial_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ) {δ : ℝ} (M₀ : ℝ)
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      M₀)
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (r L_J M : ℝ) (hr_nonneg : 0 ≤ r) (hL_J : 0 ≤ L_J)
    (hM_ge : M₀ + L_J * r ≤ M)
    (hL_J_ge : Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J) :
    (∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - packParams p.1 p.2‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ M) ∧
    (∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - packParams p.1 p.2‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ -
        outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
          L_J * ‖θ - packParams p.1 p.2‖) := by
  set θ₀ := packParams p.1 p.2 with hθ₀_def
  set R₀ : ℝ := Real.sqrt (2 * Real.log (2 * n / δ)) with hR₀_def
  have hR₀_i : ∀ i : Fin n, |unpackA θ₀ i| ≤ R₀ := by
    intro i
    have hival : unpackA θ₀ i = p.2 i := by
      rw [hθ₀_def]; exact congrFun (unpackA_packParams p.1 p.2) i
    rw [hival]; exact hp2 i
  -- the Jacobian Lipschitz bound, applied on the ball of radius `r`: the Jacobian is
  -- `L_J`-Lipschitz there, since
  -- every `θ` with `‖θ - θ₀‖ ≤ r` has readout weights bounded by `R₀ + r` (deterministic
  -- ball-propagation of the entrywise concentration bound, `abs_unpackA_le_of_displacement`).
  have hJ_lip_ball : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ -
        outputJacobian (netFromParams φ n d) X θ₀‖ ≤ L_J * ‖θ - θ₀‖ := by
    intro θ hθ
    have hRθ : ∀ i : Fin n, |unpackA θ i| ≤ R₀ + r :=
      fun i => abs_unpackA_le_of_displacement θ θ₀ i R₀ r (hR₀_i i) hθ
    have hKle := outputJacobian_netFromParams_frobenius_sub_le φ n d m hn X θ θ₀ C₁ C₂ (R₀ + r)
      hC₁_nonneg hC₂_nonneg (by positivity) hφ_lip hC₁_bdd hderiv_lip
      (fun _ _ => hφ.differentiableAt) (fun _ _ => hφ.differentiableAt) hRθ
    dsimp only at hKle
    exact hKle.trans (mul_le_mul_of_nonneg_right hL_J_ge (norm_nonneg _))
  have hJ_bdd_ball : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ M := by
    intro θ hθ
    have hstep : ‖outputJacobian (netFromParams φ n d) X θ‖ ≤
        ‖outputJacobian (netFromParams φ n d) X θ₀‖ +
        ‖outputJacobian (netFromParams φ n d) X θ - outputJacobian (netFromParams φ n d) X θ₀‖ :=
      norm_le_insert' _ _
    have h1 : ‖outputJacobian (netFromParams φ n d) X θ₀‖ ≤ M₀ := hp1
    have h2 : ‖outputJacobian (netFromParams φ n d) X θ -
        outputJacobian (netFromParams φ n d) X θ₀‖ ≤ L_J * r :=
      (hJ_lip_ball θ hθ).trans (mul_le_mul_of_nonneg_left hθ hL_J)
    calc
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ M₀ + L_J * r := hstep.trans (add_le_add h1 h2)
      _ ≤ M := hM_ge
  exact ⟨hJ_bdd_ball, hJ_lip_ball⟩

/-- **Deterministic half of the lazy-training bounds.** If the initial Jacobian norm and all
readout weights at `θ₀ = packParams W a` satisfy the Jacobian-norm and readout-weight concentration
bounds, then for any gradient flow
from `θ₀` and any radius/constant choice obeying the bootstrap and kernel-freeze relations, for all
`t ≥ 0`: the flow
stays within `C` of `θ₀`, the Rayleigh quotient stays above `lambda_min₀ / 2`, the empirical NTK
drifts by at most `(2 * M * L_J) * C`, and the residual norm and MSE loss decay exponentially.
`freeze_bound_of_initial_jacobian_and_readout_bounds` is the drift component. -/
lemma lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ)
    (hm : 0 < (m : ℝ)) {δ : ℝ} (M₀ : ℝ)
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      M₀)
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))) (lambda_min₀ r C M L_J : ℝ)
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2) θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r) (hCr : C < r) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) *ᵥ v.ofLp))
    (hM_ge : M₀ + L_J * r ≤ M)
    (hL_J_ge : Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual (netFromParams φ n d) X y (packParams p.1 p.2)‖ /
      (lambda_min₀ / 2) ≤ C)
    :
    ∀ t : ℝ, 0 ≤ t →
      ‖θ_traj t - packParams p.1 p.2‖ ≤ C ∧
      (∀ v : EuclideanSpace ℝ (Fin m), (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t)) *ᵥ v.ofLp)) ∧
      ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
        empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ (2 * M * L_J) * C ∧
      ‖trainingResidual (netFromParams φ n d) X y (θ_traj t)‖ ≤
        ‖trainingResidual (netFromParams φ n d) X y (packParams p.1 p.2)‖ *
          Real.exp (-((lambda_min₀ / 2) / (m : ℝ)) * t) ∧
      mseLoss (netFromParams φ n d) X y (θ_traj t) ≤
        mseLoss (netFromParams φ n d) X y (packParams p.1 p.2) *
          Real.exp (-(2 * (lambda_min₀ / 2) / (m : ℝ)) * t) := by
  obtain ⟨hJ_bdd_ball, hJ_lip_ball⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn X C₁
    C₂ hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ M₀ p hp1 hp2 r L_J M hr_nonneg hL_J
    hM_ge hL_J_ge
  exact lazy_training_global_bounds_of_ball_hypotheses (netFromParams φ n d) X y hflow
    hdiff M L_J lambda_min₀ r C hM hL_J hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀
    hJ_bdd_ball hJ_lip_ball

/-- **Deterministic half of the kernel-freeze bound.** If the initial Jacobian norm and all
readout weights at `θ₀ = packParams W a` satisfy the Jacobian-norm and readout-weight concentration
bounds (as they do on the event of
`exists_measurableSet_initial_jacobian_and_readout_bounds`), then for any gradient flow from `θ₀`
and any radius/constant choice obeying the bootstrap and kernel-freeze relations, the empirical NTK
stays within
`(2 * M * L_J) * C` of its initial value for all `t ≥ 0`. -/
lemma freeze_bound_of_initial_jacobian_and_readout_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ)
    (hm : 0 < (m : ℝ)) {δ : ℝ} (M₀ : ℝ)
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      M₀)
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))) (lambda_min₀ r C M L_J : ℝ)
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2) θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r) (hCr : C < r) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) *ᵥ v.ofLp))
    (hM_ge : M₀ + L_J * r ≤ M)
    (hL_J_ge : Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual (netFromParams φ n d) X y (packParams p.1 p.2)‖ /
      (lambda_min₀ / 2) ≤ C)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
      empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ (2 * M * L_J) * C :=
  (lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds φ n d m hn X y C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ hm M₀ p hp1 hp2 θ_traj lambda_min₀ r C M L_J
    hflow hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀ hM_ge hL_J_ge h_ball_gap hC_ge t ht).2.2.1

/-- **Fully probabilistic end-to-end kernel-freeze bound for the Gaussian-initialized
two-layer network.** With probability `≥ 1 - 2δ` over the joint Gaussian initialization
`(W, a)` of `netFromParams`, the following holds at `θ₀ := packParams W a`: for *any* gradient
flow starting at `θ₀` with a base spectral-gap `lambda_min₀` there, and *any* choice of ball
radius `r`, target bound `C`, Jacobian bound `M` and Lipschitz constant `L_J` satisfying the
bootstrap and kernel-freeze relations (`hCr`, `h_ball_gap`, `hC_ge`) and dominating the concrete
Jacobian-norm and Jacobian-Lipschitz formulas
(`hM_ge`, `hL_J_ge`), the empirical NTK matrix never drifts from its value at `θ₀` by more than
`(2 * M * L_J) * C`, for any `t ≥ 0`. No free `hlazy`/`hLip` hypotheses remain anywhere in this
chain - both are derived from the Gaussian initialization, not assumed. -/
theorem lazy_training_kernel_freeze_bound_of_gaussian_init
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (C₀ C₁ C₂ : ℝ) (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂)
    (hφ : Differentiable ℝ φ) (hφ_meas : Measurable φ) (hderiv_meas : Measurable (deriv φ))
    (hm : 0 < (m : ℝ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun
        _ : Fin n => gaussianReal 0 1)).real
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        let θ₀ := packParams p.1 p.2
        ∀ (θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)))
          (lambda_min₀ r C M L_J : ℝ),
          ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ_traj →
          (∀ t : ℝ, ∀ β : Fin m,
            DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t)) →
          0 < lambda_min₀ → 0 ≤ r → C < r → 0 ≤ M → 0 ≤ L_J →
          (∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
            v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X θ₀) *ᵥ v.ofLp)) →
          Real.sqrt ((m : ℝ) * C₀ ^ 2 +
              (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ) + L_J * r ≤ M →
          Real.sqrt (∑ α : Fin m,
              (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
                (∑ j : Fin d, X α j ^ 2) ^ 2 +
              3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J →
          2 * M * L_J * r ≤ lambda_min₀ / 2 →
          M * ‖trainingResidual (netFromParams φ n d) X y θ₀‖ / (lambda_min₀ / 2) ≤ C →
          ∀ t : ℝ, 0 ≤ t →
            ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
              empiricalNTKMatrix (netFromParams φ n d) X θ₀‖ ≤ (2 * M * L_J) * C} ≥
      1 - 2 * δ := by
  obtain ⟨E, -, hE, hpE⟩ := exists_measurableSet_initial_jacobian_and_readout_bounds
    φ n d m hn X hφ hφ_meas hderiv_meas hδ hδ1 _
    (outputJacobian_netFromParams_frobenius_norm_concentration φ n d m hn X C₀ C₁ hC₀ hC₁_bdd hφ hδ)
  refine hE.trans (MeasureTheory.measureReal_mono ?_)
  intro p hp
  obtain ⟨hp1, hp2⟩ := hpE p hp
  intro θ_traj lambda_min₀ r C M L_J hflow hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀
    hM_ge hL_J_ge h_ball_gap hC_ge t ht
  exact freeze_bound_of_initial_jacobian_and_readout_bounds φ n d m hn X y C₁ C₂ hC₁_bdd
    hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ hm _ p hp1 hp2 θ_traj lambda_min₀ r C M L_J hflow
    hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀ hM_ge hL_J_ge h_ball_gap hC_ge t ht

end

end NTK
