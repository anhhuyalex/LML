/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.KernelStability

/-!
# Gradient flow: displacement-integral bound and continuous-induction bootstrap

lazy-training bootstrap: the displacement-integral bound, the continuous-induction bootstrap that
closes the
circularity between kernel stability and displacement, and the finite-horizon bootstrap that
needs no spectral gap.

## Main results and proof outline

* `NTK.rayleigh_lower_bound_on_ball`, `NTK.lazy_training_global_bounds_of_ball_hypotheses` :
  Rayleigh bound on the bootstrap ball and the global consequences (displacement, uniform gap,
  kernel drift, exponential residual and loss decay) of the positive-gap bootstrap.
* `NTK.tendsto_zero_of_le_mul_exp_neg` : exponential bound implies convergence to zero.
* `NTK.mseLoss_le_of_hasDerivWithinAt_neg_gradient`, `NTK.gronwallBound_le_mul_exp`,
  `NTK.continuousOn_trainingResidual_comp` : loss monotonicity along a local gradient-flow solution,
  an explicit bound on Mathlib's Grönwall function, and continuity of the residual along a curve.
* `NTK.displacement_le_integral_of_rayleigh`, `NTK.displacement_bound_of_psd` : displacement
  bounded by the integral of the speed bound; the `lambda_min = 0` case gives the no-gap linear
  bound.
* `NTK.finite_horizon_displacement_bound`, `NTK.finite_horizon_kernel_freeze_bound` : finite-horizon
  bootstrap and kernel freeze on `[0, T]` with no spectral gap.
* `NTK.restrictCoords`, `NTK.norm_restrictCoords_gradient_mseLoss_le`,
  `NTK.norm_map_sub_le_integral_of_gfTrajectory` : displacement of a *block of coordinates* (or any
  continuous linear image) of a gradient flow is at most the integral of the speed of that block;
  the block speed under MSE flow is `(1/m) ‖J_block‖ ‖r‖`.
* `NTK.displacement_integral_bound` : A `T`-independent displacement
  cap `(M * ‖r₀‖) / lambda_min` given a uniform-in-time Rayleigh bound on `[0, T]`.
* `NTK.lazy_training_displacement_bound` : The continuous-induction
  bootstrap discharging `hlazy` with a width-independent constant `C`.

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

/-! ### Step 1: The Displacement-Integral Bound

Given that a uniform-in-time Rayleigh-quotient lower bound holds on `[0, T]`, gradient flow's
instantaneous speed `‖∂_t θ(t)‖ = ‖∇_θ L(θ(t))‖` decays exponentially (Step 1's gradient-speed
bound, `NTK.Shallow.DatasetNTK`'s `gradient_mseLoss_norm_le`, combined with Step 1's time-varying
residual decay), and integrating this speed bound over `[0, T]` gives an explicit, `T`-independent
cap on
how far gradient flow can have moved from `θ₀` by time `T`. -/

section CoordinateBlocks

variable {κ ι' : Type*} [Fintype κ] [Fintype ι']

/-- The coordinate restriction `v ↦ (v (k o))_{o : κ}` along an enumeration `k : κ → ι'` of some
coordinates, as a continuous linear map between Euclidean spaces. -/
noncomputable def restrictCoords (k : κ → ι') :
    EuclideanSpace ℝ ι' →L[ℝ] EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun o => v (k o)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] lemma restrictCoords_apply (k : κ → ι') (v : EuclideanSpace ℝ ι') (o : κ) :
    restrictCoords k v o = v (k o) := rfl

lemma norm_sq_restrictCoords (k : κ → ι') (v : EuclideanSpace ℝ ι') :
    ‖restrictCoords k v‖ ^ 2 = ∑ o : κ, v (k o) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; rfl

/-- Cauchy–Schwarz for a block of coordinates of `Jᵀ r`. -/
lemma sum_sq_mulVec_transpose_le (r : Fin m → ℝ) (J : Fin m → κ → ℝ) :
    ∑ o : κ, (∑ α : Fin m, r α * J α o) ^ 2 ≤
      (∑ α : Fin m, r α ^ 2) * ∑ α : Fin m, ∑ o : κ, J α o ^ 2 := by
  calc ∑ o : κ, (∑ α : Fin m, r α * J α o) ^ 2
      ≤ ∑ o : κ, (∑ α : Fin m, r α ^ 2) * ∑ α : Fin m, J α o ^ 2 :=
        Finset.sum_le_sum fun o _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ α : Fin m, r α ^ 2) * ∑ α : Fin m, ∑ o : κ, J α o ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]

/-- **Speed of a block of coordinates under MSE gradient flow.** -/
theorem norm_restrictCoords_gradient_mseLoss_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) (k : κ → Fin P) :
    ‖restrictCoords k (gradient (mseLoss f X y) θ)‖ ≤
      (m : ℝ)⁻¹ * Real.sqrt (∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2) *
        ‖trainingResidual f X y θ‖ := by
  have hcoord : ∀ o : κ, gradient (mseLoss f X y) θ (k o) =
      (m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual f X y θ α * outputJacobian f X θ α (k o) := by
    intro o
    rw [gradient_mseLoss_apply_j f X y θ hdiff (k o), Matrix.mulVec_apply, dotProduct]
    congr 1
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  have hsq : ‖restrictCoords k (gradient (mseLoss f X y) θ)‖ ^ 2 ≤
      ((m : ℝ)⁻¹ * Real.sqrt (∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2) *
        ‖trainingResidual f X y θ‖) ^ 2 := by
    rw [norm_sq_restrictCoords]
    simp_rw [hcoord, mul_pow, ← Finset.mul_sum]
    have hres : ‖trainingResidual f X y θ‖ ^ 2 = ∑ α : Fin m, trainingResidual f X y θ α ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have hJnn : 0 ≤ ∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.sq_sqrt hJnn, hres]
    calc (m : ℝ)⁻¹ ^ 2 * ∑ o : κ, (∑ α : Fin m, trainingResidual f X y θ α *
            outputJacobian f X θ α (k o)) ^ 2
        ≤ (m : ℝ)⁻¹ ^ 2 * ((∑ α : Fin m, trainingResidual f X y θ α ^ 2) *
            ∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_sq_mulVec_transpose_le _ _) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

end CoordinateBlocks

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Displacement of a linear image of a forward gradient flow.** If the image under `Lin` of the
gradient at time `t` has norm at most `B t` on `[0, T]`, then `Lin (w T - w₀)` has norm at most
`∫₀ᵀ B`. Only the ODE for positive times and continuity on `[0, ∞)` are used. -/
theorem norm_map_sub_le_integral_of_forwardGF {f : E → ℝ} {w₀ : E} {w : ℝ → E}
    (hflow : ForwardGFTrajectory f w₀ w) (Lin : E →L[ℝ] F) {T : ℝ} (hT : 0 ≤ T) {B : ℝ → ℝ}
    (hB : ∀ t ∈ Set.Icc 0 T, ‖Lin (gradient f (w t))‖ ≤ B t)
    (hBi : IntervalIntegrable B volume 0 T) :
    ‖Lin (w T - w₀)‖ ≤ ∫ t in (0 : ℝ)..T, B t := by
  have hd : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => Lin (w s)) (Lin (-gradient f (w t))) t := fun t ht =>
    Lin.hasFDerivAt.comp_hasDerivAt t (hflow.ode t ht)
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le (f := fun s => Lin (w s)) hT
    (Lin.continuous.comp_continuousOn (hflow.continuousOn.mono Set.Icc_subset_Ici_self))
    (fun t ht => (hd t ht.1).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall fun t ht => by
      rw [(hd t ht.1).deriv, map_neg, norm_neg]
      exact hB t (Set.mem_Icc_of_Ioo ht)) hBi
  simpa [hflow.init, map_sub] using hmain

end

/-- **The MSE loss does not increase along a local gradient-flow solution.** If `θ` solves
`θ' = -∇L(θ)` on `[0, S]` (one-sided at the endpoints), then `L(θ(t)) ≤ L(θ(0))` there. Unlike
`ConvexOpt.gf_monotone_decrease` this needs neither a global trajectory nor differentiability of `L`
away from the curve. -/
lemma mseLoss_le_of_hasDerivWithinAt_neg_gradient (f : ι → EuclideanSpace ℝ (Fin P) → ℝ)
    (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m)) {θ : ℝ → EuclideanSpace ℝ (Fin P)} {S : ℝ}
    (hdiff : ∀ t ∈ Set.Icc 0 S, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ t))
    (hθ : ∀ t ∈ Set.Icc 0 S,
      HasDerivWithinAt θ (-gradient (mseLoss f X y) (θ t)) (Set.Icc 0 S) t) :
    ∀ t ∈ Set.Icc 0 S, mseLoss f X y (θ t) ≤ mseLoss f X y (θ 0) := by
  have hd : ∀ t ∈ Set.Icc 0 S, HasDerivWithinAt (fun s => mseLoss f X y (θ s))
      (-‖gradient (mseLoss f X y) (θ t)‖ ^ 2) (Set.Icc 0 S) t := by
    intro t ht
    exact hasDerivWithinAt_comp_of_neg_gradient
      (hasGradientAt_mseLoss f X y (θ t) (hdiff t ht)).differentiableAt (hθ t ht)
  have hanti : AntitoneOn (fun s => mseLoss f X y (θ s)) (Set.Icc 0 S) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S)
      (fun t ht => (hd t ht).continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).mono interior_subset) (fun t ht => ?_)
    have := neg_nonpos.2 (sq_nonneg ‖gradient (mseLoss f X y) (θ t)‖)
    exact this
  intro t ht
  exact hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

/-- The training residual along a curve is continuous on any set where the curve is continuous and
every output is differentiable at the curve. -/
lemma continuousOn_trainingResidual_comp (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) {θ : ℝ → EuclideanSpace ℝ (Fin P)} {s : Set ℝ}
    (hθ : ContinuousOn θ s)
    (hdiff : ∀ t ∈ s, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ t)) :
    ContinuousOn (fun t => trainingResidual f X y (θ t)) s := by
  intro t ht
  have hcoord : ∀ β : Fin m, ContinuousWithinAt (fun t => f (X β) (θ t) - y β) s t := fun β =>
    ((hdiff t ht β).continuousAt.comp_continuousWithinAt (hθ t ht)).sub continuousWithinAt_const
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).continuousAt.comp_continuousWithinAt
    (continuousWithinAt_pi.2 hcoord)

/-- **Displacement is at most the integral of the speed bound.** If the Rayleigh quotient of the
empirical NTK along the trajectory is bounded below by `lambda_min` (any real, in particular `0`
under positive semidefiniteness) and the output Jacobian is `M`-bounded on `[0, T]`, then
`‖θ(T) - θ₀‖ ≤ ∫₀ᵀ (M / m) ‖r₀‖ exp(-(lambda_min / m) t) dt`. Both the gap and the no-gap
displacement bounds are corollaries. -/
theorem displacement_le_integral_of_rayleigh
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (T : ℝ) (hT : 0 ≤ T) (M lambda_min : ℝ)
    (hm : 0 < (m : ℝ))
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hJ_bdd : ∀ t ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj t)‖ ≤ M)
    (h_rr : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) :
    ‖θ_traj T - θ₀‖ ≤ ∫ t in (0:ℝ)..T,
      (m : ℝ)⁻¹ * M * (‖trainingResidual f X y θ₀‖ *
        Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
  set r₀ : ℝ := ‖trainingResidual f X y θ₀‖ with hr₀_def
  have hr_ode : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        (trainingResidual f X y (θ_traj t)).ofLp))) t :=
    fun t ht => gradient_flow_residual_vector_ode f X y t (hflow.ode t ht.1) (hdiff t)
  have hrc := continuousOn_trainingResidual_comp f X y (s := Set.Icc 0 T)
    (hflow.continuousOn.mono Set.Icc_subset_Ici_self) (fun t _ => hdiff t)
  have hres_decay := residual_norm_exponential_decay_timeVarying_Icc
    (fun t => empiricalNTKMatrix f X (θ_traj t)) lambda_min T hT
    (fun s => trainingResidual f X y (θ_traj s)) h_rr hrc hr_ode hm
  have h0 : trainingResidual f X y (θ_traj 0) = trainingResidual f X y θ₀ := by
    rw [hflow.init]
  have hspeed : ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖gradient (mseLoss f X y) (θ_traj t)‖ ≤
        (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
    intro t ht
    have h1 := gradient_mseLoss_norm_le f X y (θ_traj t) (hdiff t)
    have h2 := hres_decay t ht
    rw [h0] at h2
    calc
      ‖gradient (mseLoss f X y) (θ_traj t)‖ ≤
          (m : ℝ)⁻¹ * ‖outputJacobian f X (θ_traj t)‖ * ‖trainingResidual f X y (θ_traj t)‖ := h1
      _ ≤ (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
        have hMnn : 0 ≤ M := (norm_nonneg _).trans (hJ_bdd t ht)
        have hstep1 : ‖trainingResidual f X y (θ_traj t)‖ ≤
            r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t) := h2
        have hstep2 : (m : ℝ)⁻¹ * ‖outputJacobian f X (θ_traj t)‖ ≤ (m : ℝ)⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hJ_bdd t ht) (by positivity)
        calc
          (m : ℝ)⁻¹ * ‖outputJacobian f X (θ_traj t)‖ * ‖trainingResidual f X y (θ_traj t)‖ ≤
              ((m : ℝ)⁻¹ * M) * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
            apply mul_le_mul hstep2 hstep1 (norm_nonneg _)
            positivity
          _ = (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by ring
  have hBcont : Continuous
      (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t))) := by
    fun_prop
  have hBi : IntervalIntegrable
      (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)))
      MeasureTheory.volume 0 T :=
    hBcont.intervalIntegrable 0 T
  simpa using norm_map_sub_le_integral_of_forwardGF hflow
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin P))) hT hspeed hBi

/-- Displacement-integral bound: if the empirical NTK's Rayleigh quotient along the trajectory is
bounded below by `lambda_min` throughout `[0, T]`, and the output Jacobian is `M`-bounded there
too, then gradient flow has moved by at most `(M * ‖r₀‖) / lambda_min` from `θ₀` by time `T` -
a bound with **no explicit dependence on `T`**, since the residual's exponential decay makes the
total distance traveled converge. -/
theorem displacement_integral_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (T : ℝ) (hT : 0 ≤ T) (M lambda_min : ℝ) (hm : 0 < (m : ℝ)) (hlam : 0 < lambda_min)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hJ_bdd : ∀ t ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj t)‖ ≤ M)
    (h_rr : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) :
    ‖θ_traj T - θ₀‖ ≤ (M * ‖trainingResidual f X y θ₀‖) / lambda_min := by
  have hmain := displacement_le_integral_of_rayleigh f X y hflow T hT M lambda_min hm hdiff
    hJ_bdd h_rr
  set r₀ : ℝ := ‖trainingResidual f X y θ₀‖ with hr₀_def
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hJ_bdd 0 ⟨le_refl 0, hT⟩)
  have hr0nn : 0 ≤ r₀ := norm_nonneg _
  have hintbound : ∫ t in (0:ℝ)..T,
      (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) ≤
      (M * r₀) / lambda_min := by
    rw [show (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t))) =
        (fun t : ℝ => ((m : ℝ)⁻¹ * M * r₀) * Real.exp (-(lambda_min / (m : ℝ)) * t)) from
        funext fun t => by ring]
    rw [intervalIntegral.integral_const_mul]
    have hc : 0 < lambda_min / (m : ℝ) := by positivity
    have hbound := integral_exp_neg_le (lambda_min / (m : ℝ)) T hc hT
    have hcoeff_nn : 0 ≤ (m : ℝ)⁻¹ * M * r₀ := by positivity
    calc
      ((m : ℝ)⁻¹ * M * r₀) * ∫ t in (0:ℝ)..T, Real.exp (-(lambda_min / (m : ℝ)) * t) ≤
          ((m : ℝ)⁻¹ * M * r₀) * (lambda_min / (m : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hbound hcoeff_nn
      _ = (M * r₀) / lambda_min := by
        field_simp
  calc
    ‖θ_traj T - θ₀‖ ≤ ∫ t in (0:ℝ)..T,
        (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := hmain
    _ ≤ (M * r₀) / lambda_min := hintbound


/-- **Displacement bound on a finite horizon, with no spectral gap.** Positive semidefiniteness of
the empirical NTK alone makes the residual norm nonincreasing, so if the output Jacobian is
`M`-bounded on `[0, T]` then `‖θ(T) - θ₀‖ ≤ T * M * ‖r₀‖ / m`. The bound grows linearly in `T`, as
it must without a gap. -/
theorem displacement_bound_of_psd
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (T : ℝ) (hT : 0 ≤ T) (M : ℝ) (hm : 0 < (m : ℝ))
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hJ_bdd : ∀ t ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj t)‖ ≤ M) :
    ‖θ_traj T - θ₀‖ ≤ T * M * ‖trainingResidual f X y θ₀‖ / m := by
  have h := displacement_le_integral_of_rayleigh f X y hflow T hT M 0 hm hdiff hJ_bdd
    fun t _ v => by
      simpa using dotProduct_mulVec_nonneg_of_posSemidef
        (empiricalNTKMatrix_posSemidef f X (θ_traj t)) v
  simp only [zero_div, neg_zero, zero_mul, Real.exp_zero, mul_one,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  calc ‖θ_traj T - θ₀‖ ≤ T * ((m : ℝ)⁻¹ * M * ‖trainingResidual f X y θ₀‖) := h
    _ = T * M * ‖trainingResidual f X y θ₀‖ / m := by ring

/-! ### Step 2: The Continuous-Induction Bootstrap

The Rayleigh-quotient lower bound used by `displacement_integral_bound` is only known to hold
while gradient flow stays within a ball around `θ₀` (Rayleigh-quotient stability, above). This
section closes the circularity: `displacement_integral_bound` shows that *while inside* a ball
of radius `r`, the trajectory in fact stays within the strictly smaller radius `C < r` - which,
by continuity, means it can never actually reach the boundary `r` in the first place. This is
formalized as a proof by contradiction using the infimum of the (assumed nonempty) set of "escape
times", ruling out escape entirely and discharging `hlazy` with the tight constant `C`. -/

/-- **Rayleigh lower bound on a ball.** If the Jacobian is `M`-bounded and `L_J`-Lipschitz (relative
to `θ₀`) on the closed ball of radius `r`, the initial Rayleigh quotient is at least `lambda_min₀`,
and `2 * M * L_J * r ≤ lambda_min₀ / 2`, then every `θ` in the ball has Rayleigh quotient at least
`lambda_min₀ / 2`. -/
theorem rayleigh_lower_bound_on_ball
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    {θ₀ : EuclideanSpace ℝ (Fin P)} (M L_J lambda_min₀ r : ℝ) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (hr_nonneg : 0 ≤ r) (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖) :
    ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ∀ v : EuclideanSpace ℝ (Fin m),
      (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v.ofLp) := by
  intro θ hθ v
  have hstep := rayleigh_quotient_lower_bound_of_displacement f X θ₀ θ M L_J lambda_min₀
    (hJ_bdd θ₀ (by simpa using hr_nonneg)) (hJ_bdd θ hθ) (hJ_lip θ hθ) h_rr₀ v
  have h2ML_J_nonneg : 0 ≤ 2 * M * L_J := by positivity
  have hCbound : 2 * M * L_J * ‖θ - θ₀‖ ≤ lambda_min₀ / 2 :=
    (mul_le_mul_of_nonneg_left hθ h2ML_J_nonneg).trans h_ball_gap
  have hge : lambda_min₀ - 2 * M * L_J * ‖θ - θ₀‖ ≥ lambda_min₀ / 2 := by linarith
  nlinarith [hstep, mul_le_mul_of_nonneg_right hge (sq_nonneg ‖v‖)]

/-- **Lazy-training bootstrap.** Given a base spectral-gap hypothesis `lambda_min₀` at `θ₀`, a
Jacobian
bound `M` and Lipschitz constant `L_J` that hold on the closed ball `‖θ - θ₀‖ ≤ r` (not globally -
matching how `empiricalNTKMatrix_lipschitz_of_jacobian_bound`, kernel Lipschitz propagation, is
already stated over an
arbitrary set `S`; concentration bounds like the Jacobian-norm and Jacobian-Lipschitz are
inherently local to a neighborhood of
`θ₀`, not uniform over the whole parameter space), and a radius `r` strictly larger than the
target displacement bound `C` chosen so that `r` itself keeps the Rayleigh quotient above
`lambda_min₀/2` (`h_ball_gap`) and `C` dominates the resulting displacement bound (`hC_ge`),
gradient flow never moves more than `C` from `θ₀`, for any `t ≥ 0`. This discharges
`lazy_training_kernel_freeze_bound`'s `hlazy` hypothesis with a **width-independent** `C`: the
`1/√n` decay belongs on `L_J`, not here. -/
theorem lazy_training_displacement_bound
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
    ∀ T : ℝ, 0 ≤ T → ‖θ_traj T - θ₀‖ ≤ C := by
  set lambda_min : ℝ := lambda_min₀ / 2 with hlm_def
  have hlambda_pos : 0 < lambda_min := by positivity
  have h_rr_ball := rayleigh_lower_bound_on_ball f X M L_J lambda_min₀ r hM hL_J hr_nonneg
    h_ball_gap h_rr₀ hJ_bdd hJ_lip
  -- Core claim: if the trajectory has stayed in the closed ball `[0, S]` for some `S`, its
  -- displacement at `S` is in fact bounded by the tighter constant `C`.
  have hcore : ∀ S : ℝ, 0 ≤ S → (∀ t ∈ Set.Icc (0:ℝ) S, ‖θ_traj t - θ₀‖ ≤ r) →
      ‖θ_traj S - θ₀‖ ≤ C := by
    intro S hS hballS
    have hJ_bdd' : ∀ t ∈ Set.Icc (0:ℝ) S, ‖outputJacobian f X (θ_traj t)‖ ≤ M :=
      fun t ht => hJ_bdd (θ_traj t) (hballS t ht)
    have h_rr' : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ v : EuclideanSpace ℝ (Fin m),
        lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp) :=
      fun t ht v => h_rr_ball (θ_traj t) (hballS t ht) v
    have hfinal := displacement_integral_bound f X y hflow S hS M lambda_min hm hlambda_pos
      hdiff hJ_bdd' h_rr'
    rw [hlm_def] at hfinal
    exact hfinal.trans hC_ge
  intro T hT
  exact le_of_forall_bootstrap (d := fun t => ‖θ_traj t - θ₀‖)
    ((hflow.continuousOn.sub continuousOn_const).norm.mono Set.Icc_subset_Ici_self) hCr hT
    (by simpa [hflow.init] using hr_nonneg) (fun S hS hb => hcore S hS.1 hb) T ⟨hT, le_rfl⟩

/-! ### Finite-Horizon Bootstrap Without a Spectral Gap

Positive semidefiniteness alone gives `‖r(t)‖ ≤ ‖r₀‖`, hence a displacement bound growing
linearly in the horizon (`displacement_bound_of_psd`). Closing the same continuous-induction
bootstrap as in the gap case then bounds the displacement, and thereby the kernel drift, on
`[0, T]` with no lower bound on the spectrum of the kernel. -/

/-- **Finite-horizon displacement bound without a spectral gap.** If the output Jacobian is
`M`-bounded on the closed ball of radius `r` around `θ₀` and `T * M * ‖r₀‖ / m ≤ C < r`, then a
gradient flow from `θ₀` stays within `C` of `θ₀` on `[0, T]`. -/
theorem finite_horizon_displacement_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (T M r C : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hm : 0 < (m : ℝ)) (hr : 0 ≤ r) (hCr : C < r)
    (hC_ge : T * M * ‖trainingResidual f X y θ₀‖ / m ≤ C)
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖θ_traj t - θ₀‖ ≤ C :=
  le_of_forall_bootstrap (d := fun t => ‖θ_traj t - θ₀‖)
    ((hflow.continuousOn.sub continuousOn_const).norm.mono Set.Icc_subset_Ici_self) hCr hT
    (by simpa [hflow.init] using hr) fun S hS hb =>
      (displacement_bound_of_psd f X y hflow S hS.1 M hm hdiff
        fun t ht => hJ_bdd _ (hb t ht)).trans
        (le_trans (by gcongr; exact hS.2) hC_ge)

/-- **Finite-horizon kernel freeze without a spectral gap.** Under the hypotheses of
`finite_horizon_displacement_bound` and `L_J`-Lipschitzness of the output Jacobian on the ball,
`‖K(θ(t)) - K(θ₀)‖ ≤ (2 * M * L_J) * C` for every `t ∈ [0, T]`. -/
theorem finite_horizon_kernel_freeze_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (T M L_J r C : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J) (hm : 0 < (m : ℝ)) (hr : 0 ≤ r)
    (hCr : C < r) (hC_ge : T * M * ‖trainingResidual f X y θ₀‖ / m ≤ C)
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C := by
  intro t ht
  have hdisp := finite_horizon_displacement_bound f X y hflow hdiff T M r C hT hM hm hr hCr hC_ge
    hJ_bdd t ht
  have hball : ‖θ_traj t - θ₀‖ ≤ r := hdisp.trans hCr.le
  exact (empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X (θ_traj t) θ₀ M L_J
    (hJ_bdd _ hball) (hJ_bdd θ₀ (by simpa using hr)) (hJ_lip _ hball)).trans
    (mul_le_mul_of_nonneg_left hdisp (by positivity))

/-- A nonnegative quantity bounded by `L₀ * exp (-c t)` with `c > 0` tends to `0`. Used to pass from
exponential loss decay to convergence of the training loss. -/
lemma tendsto_zero_of_le_mul_exp_neg {L : ℝ → ℝ} {L₀ c : ℝ} (hc : 0 < c)
    (hnn : ∀ t, 0 ≤ t → 0 ≤ L t) (hL : ∀ t, 0 ≤ t → L t ≤ L₀ * Real.exp (-c * t)) :
    Tendsto L atTop (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => L₀ * Real.exp (-c * t)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc))).const_mul L₀
    simpa [Function.comp_def] using h
  exact squeeze_zero' (eventually_atTop.2 ⟨0, hnn⟩) (eventually_atTop.2 ⟨0, hL⟩) hexp

end NTK

end
