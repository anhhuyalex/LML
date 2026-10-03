/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.Bootstrap

/-!
# Gradient flow: asymptotic properties in the infinite-width limit

Kernel freeze as `n → ∞`, deterministic initialization limits and the
corresponding Chebyshev bounds.

## Main results and proof outline

* `NTK.empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound` : Kernel freeze bound
  `‖K(θ(t)) - K(θ₀)‖ ≤ (2 * M * L_J) * C` instantiated with Jacobian bounds
  (the `1/√n` decay lives in `L_J`, not in the displacement bound `C` - see
  `NTK.Shallow.DatasetNTK`'s `gradient_mseLoss_norm_le` and this file's Rayleigh-quotient stability
  theorems below).
* `NTK.lazy_training_kernel_freeze_bound` : Step 2 kernel freeze bound under lazy training.
* `NTK.tendsto_lazy_training_kernel_freeze` : Asymptotic freeze limit as `n → ∞`.
* `NTK.tendsto_lazy_training_kernel_freeze_matrix` : Empirical NTK matrix freeze as `n → ∞`.
* `NTK.deterministic_initialization_shallowEmpiricalNTK_tendsto_ae` :
  Property 1 a.s. initialization limit.
* `NTK.deterministic_initialization_empiricalNTKMatrix_tendsto_ae` : Gram matrix a.s. limit.
* `NTK.deterministic_initialization_chebyshev_bound` : Property 1 entrywise Chebyshev bound.
* `NTK.tendsto_shallowEmpiricalNTK_chebyshev_bound` : Property 1 Chebyshev tail decay in ENNReal.

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

/-- Property 2 (Kernel Freeze Bound instantiated with Jacobian Bounds):
When `θ_traj` satisfies lazy displacement `‖θ(t) - θ₀‖ ≤ C` and the output Jacobian
is bounded by `M` and `L_J`-Lipschitz along the trajectory, the empirical NTK matrix satisfies
`‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C`.
The width decay `1/√n` belongs on `L_J = Θ(1/√n)` (from the network parameterization factor
`n^{-1/2}` in `outputJacobian`), not on parameter displacement `hlazy`. -/
theorem empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P)) (θ₀ : EuclideanSpace ℝ (Fin P))
    (C M L_J : ℝ) (hL_J : 0 ≤ L_J)
    (hlazy : ∀ t ≥ 0, ‖θ_traj t - θ₀‖ ≤ C)
    (hJ_bdd : ∀ t ≥ 0, ‖outputJacobian f X (θ_traj t)‖ ≤ M)
    (hJ_bdd₀ : ‖outputJacobian f X θ₀‖ ≤ M)
    (hJ_lip : ∀ t ≥ 0, ‖outputJacobian f X (θ_traj t) - outputJacobian f X θ₀‖ ≤
      L_J * ‖θ_traj t - θ₀‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      (2 * M * L_J) * C := by
  have hLip : ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      (2 * M * L_J) * ‖θ_traj t - θ₀‖ :=
    empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X (θ_traj t) θ₀ M L_J
      (hJ_bdd t ht) hJ_bdd₀ (hJ_lip t ht)
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ_bdd₀
  have h2ML_nonneg : 0 ≤ 2 * M * L_J := by
    have : 0 ≤ 2 * M := by linarith
    exact mul_nonneg this hL_J
  have h_disp := hlazy t ht
  have h_bound := mul_le_mul_of_nonneg_left h_disp h2ML_nonneg
  exact hLip.trans h_bound

/-- **Global consequences of the ball hypotheses (positive-gap bootstrap).** Under the hypotheses of
Gap 5's bootstrap, for every `t ≥ 0` the gradient flow (i) stays within `C` of `θ₀`, (ii) keeps the
Rayleigh quotient of the empirical NTK at least `lambda_min₀ / 2`, (iii) moves the empirical NTK by
at most `(2 * M * L_J) * C`, and satisfies exponential decay (iv) of the residual norm and (v) of
the MSE loss, both at the rates given by `lambda_min₀ / 2`. -/
theorem lazy_training_global_bounds_of_ball_hypotheses
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (M L_J lambda_min₀ r C : ℝ) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J) (hm : 0 < (m : ℝ))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r)
    (hCr : C < r)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual f X y θ₀‖ / (lambda_min₀ / 2) ≤ C)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖) :
    ∀ t : ℝ, 0 ≤ t →
      ‖θ_traj t - θ₀‖ ≤ C ∧
      (∀ v : EuclideanSpace ℝ (Fin m), (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) ∧
      ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C ∧
      ‖trainingResidual f X y (θ_traj t)‖ ≤
        ‖trainingResidual f X y θ₀‖ * Real.exp (-((lambda_min₀ / 2) / (m : ℝ)) * t) ∧
      mseLoss f X y (θ_traj t) ≤
        mseLoss f X y θ₀ * Real.exp (-(2 * (lambda_min₀ / 2) / (m : ℝ)) * t) := by
  have hdisp := lazy_training_displacement_bound f X y hflow hdiff M L_J lambda_min₀ r C
    hM hL_J hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀ hJ_bdd hJ_lip
  have hJ_bdd_all : ∀ s ≥ 0, ‖outputJacobian f X (θ_traj s)‖ ≤ M :=
    fun s hs => hJ_bdd (θ_traj s) ((hdisp s hs).trans hCr.le)
  have hJ_lip_all : ∀ s ≥ 0, ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ ≤
      L_J * ‖θ_traj s - θ₀‖ :=
    fun s hs => hJ_lip (θ_traj s) ((hdisp s hs).trans hCr.le)
  have hray := rayleigh_lower_bound_on_ball f X M L_J lambda_min₀ r hM hL_J hr_nonneg h_ball_gap
    h_rr₀ hJ_bdd hJ_lip
  have hr_ode : ∀ t : ℝ, 0 < t → HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        (trainingResidual f X y (θ_traj t)).ofLp))) t :=
    fun t ht => gradient_flow_residual_vector_ode f X y t (hflow.ode t ht) (hdiff t)
  have hrc := continuousOn_trainingResidual_comp f X y (s := Set.Ici 0) hflow.continuousOn
    (fun t _ => hdiff t)
  have h0 : trainingResidual f X y (θ_traj 0) = trainingResidual f X y θ₀ := by rw [hflow.init]
  intro t ht
  have hrr : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ v : EuclideanSpace ℝ (Fin m),
      (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj s)) *ᵥ v.ofLp) :=
    fun s hs v => hray (θ_traj s) ((hdisp s hs.1).trans hCr.le) v
  refine ⟨hdisp t ht, fun v => hray (θ_traj t) ((hdisp t ht).trans hCr.le) v,
    empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound f X θ_traj θ₀ C M L_J hL_J hdisp
      hJ_bdd_all (hJ_bdd θ₀ (by simpa using hr_nonneg)) hJ_lip_all t ht, ?_, ?_⟩
  · have h := residual_norm_exponential_decay_timeVarying_Icc
      (fun s => empiricalNTKMatrix f X (θ_traj s)) (lambda_min₀ / 2) t ht
      (fun s => trainingResidual f X y (θ_traj s)) hrr (hrc.mono Set.Icc_subset_Ici_self)
      (fun s hs => hr_ode s hs.1) hm t ⟨ht, le_rfl⟩
    rwa [h0] at h
  · have h := residual_norm_sq_exponential_decay_timeVarying_Icc
      (fun s => empiricalNTKMatrix f X (θ_traj s)) (lambda_min₀ / 2) t ht
      (fun s => trainingResidual f X y (θ_traj s)) hrr (hrc.mono Set.Icc_subset_Ici_self)
      (fun s hs => hr_ode s hs.1) hm t ⟨ht, le_rfl⟩
    rw [h0] at h
    unfold mseLoss
    calc (2 * (m : ℝ))⁻¹ * ‖trainingResidual f X y (θ_traj t)‖ ^ 2
        ≤ (2 * (m : ℝ))⁻¹ * (‖trainingResidual f X y θ₀‖ ^ 2 *
            Real.exp (-(2 * (lambda_min₀ / 2) / (m : ℝ)) * t)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring

/-- **Phase 6: end-to-end kernel-freeze bound from ball-restricted Jacobian hypotheses.**
Wires Gap 5's bootstrap (`lazy_training_displacement_bound`) directly into
`empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound`: given a Jacobian bound `M` and
Lipschitz constant `L_J` on the ball `‖θ - θ₀‖ ≤ r` (exactly what a concentration argument like
Gap 3/4 supplies - never a bound uniform over the whole parameter space), plus a base
spectral-gap hypothesis `lambda_min₀` at `θ₀` and the radius/target-bound relations `hCr`,
`h_ball_gap`, `hC_ge` from Gap 5, the empirical NTK matrix never drifts from its value at `θ₀`
by more than `(2 * M * L_J) * C`. No free `hlazy`/`hLip` hypotheses remain - both are derived,
not assumed. -/
theorem lazy_training_kernel_freeze_bound_of_ball_hypotheses
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (M L_J lambda_min₀ r C : ℝ) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J) (hm : 0 < (m : ℝ))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r)
    (hCr : C < r)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual f X y θ₀‖ / (lambda_min₀ / 2) ≤ C)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C :=
  (lazy_training_global_bounds_of_ball_hypotheses f X y hflow hdiff M L_J lambda_min₀ r C hM hL_J
    hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀ hJ_bdd hJ_lip t ht).2.2.1

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
By `ntk_convergence` from `NTK.Shallow.Kernel`, the empirical kernel `shallowEmpiricalNTK`
built from `n` Gaussian hidden rows converges almost surely to the deterministic
limiting kernel `shallowLimitingNTK` as width `n → ∞`:
  `k_n(x, x') → k_∞(x, x')` a.s. -/
theorem deterministic_initialization_shallowEmpiricalNTK_tendsto_ae
    (σ' : ℝ → ℝ) (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C) (x x' : Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0
          1))),
      Filter.Tendsto (fun n => shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) x x')
        Filter.atTop (𝓝 (shallowLimitingNTK σ' x x')) :=
  ntk_convergence σ' hσ'_meas hσ'_bounded x x'

/-- Property 1 (Deterministic NTK Gram Matrix Initialization Limit):
For any finite dataset `X : Fin m → Fin d → ℝ`, the empirical NTK Gram matrix
`fun α β => shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) (X α) (X β)` converges
entrywise almost surely
to the deterministic limiting NTK Gram matrix `fun α β => shallowLimitingNTK σ' (X α) (X β)`
as width `n → ∞`. -/
theorem deterministic_initialization_empiricalNTKMatrix_tendsto_ae
    (σ' : ℝ → ℝ) (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C) (X : Fin m → Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0
          1))),
      ∀ α β : Fin m,
        Filter.Tendsto (fun n => shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) (X α) (X β))
          Filter.atTop (𝓝 (shallowLimitingNTK σ' (X α) (X β))) := by
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
`shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) x x'` deviates from its expectation by `≥ ε`
is bounded by
`variance (fun rows => shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) x x') μ / ε²`.
When the estimator's variance decays as `≤ C / n`, this probability is bounded
by `C / (ε² * n)`. -/
theorem deterministic_initialization_chebyshev_bound
    (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) (n : ℕ) (C : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hL2 : MemLp (fun rows => shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) x x') 2
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0
          1)))
    (hvar : ProbabilityTheory.variance
      (fun rows => shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) x x')
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0
          1)) ≤ C / (n : ℝ)) :
    let μ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => (Measure.pi fun _ : Fin d =>
        gaussianReal 0 1))
    let k_n := fun rows => shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) x x'
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
on the probability that `shallowEmpiricalNTK` deviates by `≥ ε` converges to `0`. -/
theorem tendsto_shallowEmpiricalNTK_chebyshev_bound (C ε : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (C / (ε ^ 2 * (n : ℝ)))) atTop (𝓝 0) := by
  have h_real : Tendsto (fun n : ℕ => C / (ε ^ 2 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_chebyshev_bound_atTop C ε
  have h := ENNReal.tendsto_ofReal h_real
  rw [ENNReal.ofReal_zero] at h
  exact h

end NTK

end
