/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.AffineDynamics

/-!
# Gradient flow: test-point prediction

Prediction at a test point along a gradient flow, with the deterministic core
`abs_inner_displacement_add_frozenPrediction_le(_of_exp_decay)`.

## Main results and proof outline

* `NTK.hasDerivAt_predictionError_abs_le`, `NTK.abs_inner_displacement_add_frozenPrediction_le`,
  `NTK.abs_sub_le_of_abs_deriv_le_exp`,
  `NTK.abs_inner_displacement_add_frozenPrediction_le_of_exp_decay` : Phase 14.2 - deterministic
  test-point prediction error along a gradient flow, on a finite window and uniformly in time under
  exponential residual decay.

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

/-! ### Test-Point Prediction Along a Gradient Flow

For a test input `x`, the linearized output change `⟪∇_θ f(x; θ₀), θ(t) - θ₀⟫` is compared with the
frozen-kernel prediction `-a ⬝ᵥ (r₀ - exp(-(t/m) K_∞) r₀)`, where `K_∞ a = k_∞` (`a = K_∞⁻¹ k_∞`
when `K_∞` is invertible). The comparison is a mean-value estimate whose pointwise derivative bound
involves only three drifts: Jacobian, cross-kernel `J(θ₀) ∇_θ f(x; θ₀)`, and residual versus the
matrix exponential (`residual_sub_matrix_exp_le`). -/

/-- Derivative along the flow of the test-feature projection of the displacement. -/
lemma hasDerivAt_inner_tangentFeature_displacement
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (g θ₀ : EuclideanSpace ℝ (Fin P)) {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)} {t : ℝ}
    (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => ⟪g, θ_traj s - θ₀⟫)
      (-(m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual f X y (θ_traj t) α *
        ⟪g, tangentFeature f (X α) (θ_traj t)⟫) t := by
  have h := (hasDerivAt_const t g).inner ℝ (hflow.sub_const θ₀)
  refine h.congr_deriv ?_
  rw [gradient_mseLoss f X y _ hdiff]
  simp [inner_neg_right, inner_smul_right, inner_sum, Finset.mul_sum]

/-- Derivative of the frozen-kernel prediction curve `s ↦ -a ⬝ᵥ (r₀ - exp(-(s/m) K_inf) r₀)`, where
`K_inf` is symmetric and `K_inf a = k_inf`: it equals `-(1/m) k_inf ⬝ᵥ exp(-(s/m) K_inf) r₀`. -/
lemma hasDerivAt_frozenPrediction (K_inf : Matrix (Fin m) (Fin m) ℝ) (hK : K_inf.IsHermitian)
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) (r₀ : EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    HasDerivAt (fun u : ℝ => -(a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)))
      (-(m : ℝ)⁻¹ * (k_inf ⬝ᵥ (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))) s := by
  have hρ := matrix_exp_residual_trajectory_hasDerivAt K_inf r₀ s
  have h := ((hasDerivAt_const s (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m))).inner ℝ hρ).sub_const
    (a ⬝ᵥ r₀.ofLp)
  have hfun : (fun u : ℝ => -(a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))) = fun u : ℝ =>
      ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)),
        (WithLp.toLp 2 (NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) :
          EuclideanSpace ℝ (Fin m))⟫ - a ⬝ᵥ r₀.ofLp := by
    funext u
    have hin : ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)),
        (WithLp.toLp 2 (NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) :
          EuclideanSpace ℝ (Fin m))⟫ =
        a ⬝ᵥ (NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) := by
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    rw [hin, dotProduct_sub]
    ring
  rw [hfun]
  refine h.congr_deriv ?_
  have hKt : K_infᵀ = K_inf := hK
  set v : Fin m → ℝ := NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp with hv
  have hin : ∀ u : Fin m → ℝ, ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)), WithLp.toLp 2 u⟫ =
      a ⬝ᵥ u := fun u => by simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [hin, inner_zero_left, add_zero, dotProduct_smul, Matrix.dotProduct_mulVec, smul_eq_mul]
  have : a ᵥ* K_inf = k_inf := by
    rw [← hKa, ← Matrix.vecMul_transpose, hKt]
  rw [this]

/-- Cauchy-Schwarz for the dot product of two vectors of `Fin m → ℝ`. -/
lemma abs_dotProduct_le_norm_mul_norm (u v : Fin m → ℝ) :
    |u ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m))‖ *
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ := by
  have := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m)) (WithLp.toLp 2 v)
  simpa [PiLp.inner_apply, dotProduct, mul_comm] using this

/-- **Pointwise derivative of the test-point prediction error.** Along a gradient flow, the error
curve `e(s) = ⟪g, θ(s) - θ₀⟫ + a ⬝ᵥ (r₀ - exp(-(s/m) K_inf) r₀)` (with `K_inf` symmetric and
`K_inf a = k_inf`) is differentiable at `c` with `|e'(c)| ≤ (1/m) (‖r(c)‖ (‖g‖ ‖J(θ(c)) - J(θ₀)‖ +
ε_k) + ‖k_inf‖ ‖r(c) - exp(-(c/m) K_inf) r₀‖)`, where `ε_k` bounds `‖J(θ₀) g - k_inf‖`. The three
terms are the Jacobian drift, the cross-kernel error and the residual-versus-frozen-exponential
error; the estimate uses no smallness beyond them. -/
lemma hasDerivAt_predictionError_abs_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (hm : 0 < (m : ℝ)) {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (g : EuclideanSpace ℝ (Fin P)) (K_inf : Matrix (Fin m) (Fin m) ℝ) (hKsymm : K_inf.IsHermitian)
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) (r₀ : EuclideanSpace ℝ (Fin m)) {c : ℝ}
    (hcflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj c)) c)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj c)) {ε_k : ℝ}
    (hk : ‖(WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ g.ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 k_inf‖ ≤ ε_k) :
    ∃ e' : ℝ, HasDerivAt (fun s => ⟪g, θ_traj s - θ₀⟫ + a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)) e' c ∧
      |e'| ≤ (m : ℝ)⁻¹ * (‖trainingResidual f X y (θ_traj c)‖ *
          (‖g‖ * ‖outputJacobian f X (θ_traj c) - outputJacobian f X θ₀‖ + ε_k) +
        ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
          ‖trainingResidual f X y (θ_traj c) -
            WithLp.toLp 2 (NormedSpace.exp (-(c / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)‖) := by
  have hd1 := hasDerivAt_inner_tangentFeature_displacement f X y g θ₀ hcflow hdiff
  have hd2 := (hasDerivAt_frozenPrediction K_inf hKsymm a k_inf hKa r₀ c).neg
  have hd2' : HasDerivAt (fun u : ℝ => a ⬝ᵥ (r₀.ofLp -
      NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))
      ((m : ℝ)⁻¹ * (k_inf ⬝ᵥ (NormedSpace.exp (-(c / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))) c := by
    convert hd2 using 1
    · funext u
      simp
    · ring
  refine ⟨_, hd1.add hd2', ?_⟩
  set rc : EuclideanSpace ℝ (Fin m) := trainingResidual f X y (θ_traj c) with hrc
  have hsum : ∑ α : Fin m, rc α * ⟪g, tangentFeature f (X α) (θ_traj c)⟫ =
      rc.ofLp ⬝ᵥ (outputJacobian f X (θ_traj c) *ᵥ g.ofLp) := by
    simp only [dotProduct, Matrix.mulVec, outputJacobian, Matrix.of_apply, tangentFeature,
      PiLp.inner_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
  rw [hsum]
  set Jc := outputJacobian f X (θ_traj c) with hJc
  set J₀ := outputJacobian f X θ₀ with hJ₀
  set ρv : Fin m → ℝ := NormedSpace.exp (-(c / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp with hρv
  have hdec : rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp) - k_inf ⬝ᵥ ρv =
      rc.ofLp ⬝ᵥ ((Jc - J₀) *ᵥ g.ofLp) + rc.ofLp ⬝ᵥ (J₀ *ᵥ g.ofLp - k_inf) +
        k_inf ⬝ᵥ (rc.ofLp - ρv) := by
    simp only [Matrix.sub_mulVec, dotProduct_sub, dotProduct_comm k_inf rc.ofLp]
    ring
  have hrcv : (WithLp.toLp 2 rc.ofLp : EuclideanSpace ℝ (Fin m)) = rc := rfl
  have b1 : |rc.ofLp ⬝ᵥ ((Jc - J₀) *ᵥ g.ofLp)| ≤ ‖rc‖ * (‖g‖ * ‖Jc - J₀‖) := by
    refine (abs_dotProduct_le_norm_mul_norm _ _).trans ?_
    rw [hrcv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (mulVec_frobenius_norm_le (Jc - J₀) g).trans (le_of_eq (mul_comm _ _))
  have b2 : |rc.ofLp ⬝ᵥ (J₀ *ᵥ g.ofLp - k_inf)| ≤ ‖rc‖ * ε_k := by
    refine (abs_dotProduct_le_norm_mul_norm _ _).trans ?_
    rw [hrcv]
    refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hk) (norm_nonneg _)
    congr 1
  have b3 : |k_inf ⬝ᵥ (rc.ofLp - ρv)| ≤ ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
      ‖rc - WithLp.toLp 2 ρv‖ := by
    refine (abs_dotProduct_le_norm_mul_norm _ _).trans (le_of_eq ?_)
    congr 2
  have hkey : |rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp) - k_inf ⬝ᵥ ρv| ≤
      ‖rc‖ * (‖g‖ * ‖Jc - J₀‖ + ε_k) + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
        ‖rc - WithLp.toLp 2 ρv‖ := by
    rw [hdec]
    refine (abs_add_three _ _ _).trans ?_
    nlinarith [b1, b2, b3]
  have hexp : -(m : ℝ)⁻¹ * (rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp)) + (m : ℝ)⁻¹ * (k_inf ⬝ᵥ ρv) =
      -(m : ℝ)⁻¹ * (rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp) - k_inf ⬝ᵥ ρv) := by ring
  rw [hexp, abs_mul, abs_neg, abs_of_pos (inv_pos.2 hm)]
  exact mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 hm.le)

/-- **Deterministic test-point prediction error along a gradient flow.** Let `θ(t)` be a forward
gradient flow of the MSE loss of `f` on `X`, `g = ∇_θ f(x; θ₀)` the tangent feature at a test input
`x`, `r₀` the initial residual, and `K_inf`, `k_inf` a symmetric positive semidefinite kernel matrix
and cross-kernel vector with `K_inf a = k_inf`. If on `[0, T]` the Jacobian stays within `ε_J` of
`J(θ₀)`, the empirical kernel within `ε_K` of `K_inf`, and `J(θ₀) g` within `ε_k` of `k_inf`, then
for
`t ∈ [0, T]`
`|⟪g, θ(t) - θ₀⟫ + a ⬝ᵥ (r₀ - exp(-(t/m) K_inf) r₀)| ≤ t m⁻¹ (‖g‖ ε_J ‖r₀‖ + ε_k ‖r₀‖ +
‖k_inf‖ m⁻¹ ε_K ‖r₀‖ T)`.
With `a = K_inf⁻¹ k_inf` this says the linearized output change `⟪g, θ(t) - θ₀⟫` equals the
kernel-regression prediction `k_inf K_inf⁻¹ (I - exp(-(t/m) K_inf)) (y - f₀)` up to the stated
error.
The proof is a mean-value estimate on the error curve, whose derivative is bounded pointwise by the
three drifts (Jacobian, cross-kernel, residual-vs-exponential); no integral formula is used. -/
theorem abs_inner_displacement_add_frozenPrediction_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (hm : 0 < (m : ℝ)) {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (g : EuclideanSpace ℝ (Fin P)) {T : ℝ} (hT : 0 ≤ T)
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (hK_inf : K_inf.PosSemidef)
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) {ε_J ε_K ε_k : ℝ}
    (hJ : ∀ s ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ ≤ ε_J)
    (hK : ∀ s ∈ Set.Icc 0 T, ‖empiricalNTKMatrix f X (θ_traj s) - K_inf‖ ≤ ε_K)
    (hk : ‖(WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ g.ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 k_inf‖ ≤ ε_k) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      |⟪g, θ_traj t - θ₀⟫ + a ⬝ᵥ ((trainingResidual f X y θ₀).ofLp -
          NormedSpace.exp (-(t / (m : ℝ)) • K_inf) *ᵥ (trainingResidual f X y θ₀).ofLp)| ≤
        t * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖trainingResidual f X y θ₀‖ +
          ε_k * ‖trainingResidual f X y θ₀‖ + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
            ((m : ℝ)⁻¹ * (ε_K * ‖trainingResidual f X y θ₀‖) * T))) := by
  set r₀ := trainingResidual f X y θ₀ with hr₀
  set r : ℝ → EuclideanSpace ℝ (Fin m) := fun s => trainingResidual f X y (θ_traj s) with hr
  have hKsymm : K_inf.IsHermitian := hK_inf.isHermitian
  have hrc : ContinuousOn r (Set.Icc 0 T) :=
    (continuousOn_trainingResidual_comp f X y (s := Set.Icc 0 T)
      (hflow.continuousOn.mono Set.Icc_subset_Ici_self) fun t _ => hdiff t)
  have hr_ode : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ •
      ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (r t).ofLp))) t := fun t ht =>
    gradient_flow_residual_vector_ode f X y t (hflow.ode t ht.1) (hdiff t)
  have hK_psd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ v : EuclideanSpace ℝ (Fin m),
      0 ≤ v.ofLp ⬝ᵥ (empiricalNTKMatrix f X (θ_traj s) *ᵥ v.ofLp) := fun s _ v => by
    simpa using dotProduct_mulVec_nonneg_of_posSemidef
      (empiricalNTKMatrix_posSemidef f X (θ_traj s)) v
  have hr0 : r 0 = r₀ := by simp [hr, hr₀, hflow.init]
  have hrnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖r s‖ ≤ ‖r₀‖ := fun s hs => by
    have h := residual_norm_exponential_decay_timeVarying_Icc
      (fun s => empiricalNTKMatrix f X (θ_traj s)) 0 T hT r
      (fun s hs v => by simpa using hK_psd s hs v) hrc hr_ode hm s hs
    simpa [hr0] using h
  have hres := residual_sub_matrix_exp_le (fun s => empiricalNTKMatrix f X (θ_traj s)) K_inf r hT hm
    hrc hr_ode hK_psd (fun v => by simpa using dotProduct_mulVec_nonneg_of_posSemidef hK_inf v) hK
  set ρ : ℝ → EuclideanSpace ℝ (Fin m) := fun s =>
    WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) with hρ
  set C : ℝ := (m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
    ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * T)) with hC
  -- the error curve
  set e : ℝ → ℝ := fun s => ⟪g, θ_traj s - θ₀⟫ + a ⬝ᵥ (r₀.ofLp -
    NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) with he
  have he0 : e 0 = 0 := by
    simp [he, hflow.init]
  have hecont : ContinuousOn e (Set.Icc 0 T) := by
    intro s hs
    have h1 : ContinuousWithinAt (fun s => ⟪g, θ_traj s - θ₀⟫) (Set.Icc 0 T) s :=
      ((continuous_const.inner (continuous_id.sub continuous_const)).comp_continuousOn
        (hflow.continuousOn.mono Set.Icc_subset_Ici_self)) s hs
    have h2 := (hasDerivAt_frozenPrediction K_inf hKsymm a k_inf hKa r₀ s).continuousAt
    have h2' : ContinuousAt (fun u : ℝ => a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)) s := by
      convert h2.neg using 1
      funext u
      simp
    exact h1.add h2'.continuousWithinAt
  have hεK : 0 ≤ ε_K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩)
  have hεJ : 0 ≤ ε_J := (norm_nonneg _).trans (hJ 0 ⟨le_rfl, hT⟩)
  have hεk : 0 ≤ ε_k := (norm_nonneg _).trans hk
  -- pointwise derivative bound
  have hbound : ∀ c ∈ Set.Ioo (0 : ℝ) T, ∃ e' : ℝ, HasDerivAt e e' c ∧ |e'| ≤ C := by
    intro c hc
    have hcI : c ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hc
    obtain ⟨e', hde, hbe⟩ := hasDerivAt_predictionError_abs_le f X y hm g K_inf hKsymm a k_inf hKa
      r₀ (hflow.ode c hc.1) (hdiff c) hk
    refine ⟨e', hde, hbe.trans ?_⟩
    have hres' := hres c hcI
    rw [hr0] at hres'
    have hrc_norm : ‖r c‖ ≤ ‖r₀‖ := hrnorm c hcI
    have hJc := hJ c hcI
    have hres'' : ‖r c - ρ c‖ ≤ (m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * T :=
      hres'.trans (mul_le_mul_of_nonneg_left hc.2.le (by positivity))
    rw [hC]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm.le)
    have hg0 := norm_nonneg g
    have hkn := norm_nonneg (WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))
    calc ‖r c‖ * (‖g‖ * ‖outputJacobian f X (θ_traj c) - outputJacobian f X θ₀‖ + ε_k) +
          ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ * ‖r c - ρ c‖
        ≤ ‖r₀‖ * (‖g‖ * ε_J + ε_k) + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
          ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * T) := by
          gcongr
      _ = _ := by ring
  intro t ht
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have := he0
    simp only [he] at this ⊢
    simpa using this
  · choose! e' he' hb using hbound
    obtain ⟨c, hc, hcs⟩ :=
      exists_hasDerivAt_eq_slope e e' hpos (hecont.mono (Set.Icc_subset_Icc_right ht.2))
      (fun x hx => he' x ⟨hx.1, hx.2.trans_le ht.2⟩)
    have hct : |e' c| ≤ C := hb c ⟨hc.1, hc.2.trans_le ht.2⟩
    have : e t = e' c * t := by
      rw [he0, sub_zero, sub_zero] at hcs
      field_simp at hcs
      linarith
    change |e t| ≤ t * C
    rw [this, abs_mul, abs_of_pos hpos, mul_comm]
    exact mul_le_mul_of_nonneg_left hct hpos.le

/-- **Exponentially decaying derivative gives a small tail.** If `e` is continuous on `[S, ∞)` and
differentiable on `(S, ∞)` with `|e'(s)| ≤ B exp(-ν s)`, `ν > 0`, then for every `t ≥ S`,
`|e t - e S| ≤ (B / ν) exp(-ν S)`. -/
lemma abs_sub_le_of_abs_deriv_le_exp {e : ℝ → ℝ} {S B ν : ℝ} (hν : 0 < ν)
    (hec : ContinuousOn e (Set.Ici S))
    (hd : ∀ s, S < s → ∃ e' : ℝ, HasDerivAt e e' s ∧ |e'| ≤ B * Real.exp (-ν * s))
    {t : ℝ} (ht : S ≤ t) : |e t - e S| ≤ B / ν * Real.exp (-ν * S) := by
  have hexp : ∀ s, HasDerivAt (fun s => B / ν * Real.exp (-ν * s)) (-(B * Real.exp (-ν * s))) s :=
    fun s => by
      have := ((hasDerivAt_id s).const_mul (-ν)).exp.const_mul (B / ν)
      refine this.congr_deriv ?_
      simp only [id_eq]
      field_simp
  have hcexp : Continuous fun s => B / ν * Real.exp (-ν * s) := by fun_prop
  have hdiff : DifferentiableOn ℝ e (interior (Set.Ici S)) := fun s hs => by
    rw [interior_Ici] at hs
    obtain ⟨e', he', -⟩ := hd s hs
    exact he'.differentiableAt.differentiableWithinAt
  -- antitone: e + (B/ν) exp(-ν ·)
  have hanti : AntitoneOn (fun s => e s + B / ν * Real.exp (-ν * s)) (Set.Ici S) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici S) (hec.add hcexp.continuousOn)
      (hdiff.add (fun s _ => (hexp s).differentiableAt.differentiableWithinAt)) fun s hs => ?_
    rw [interior_Ici] at hs
    obtain ⟨e', he', hb⟩ := hd s hs
    have h : HasDerivAt (fun s => e s + B / ν * Real.exp (-ν * s))
        (e' + -(B * Real.exp (-ν * s))) s := he'.add (hexp s)
    rw [h.deriv]
    linarith [(abs_le.1 hb).2]
  have hmono : MonotoneOn (fun s => e s - B / ν * Real.exp (-ν * s)) (Set.Ici S) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici S) (hec.sub hcexp.continuousOn)
      (hdiff.sub (fun s _ => (hexp s).differentiableAt.differentiableWithinAt)) fun s hs => ?_
    rw [interior_Ici] at hs
    obtain ⟨e', he', hb⟩ := hd s hs
    have h : HasDerivAt (fun s => e s - B / ν * Real.exp (-ν * s))
        (e' - -(B * Real.exp (-ν * s))) s := he'.sub (hexp s)
    rw [h.deriv]
    linarith [(abs_le.1 hb).1]
  have h1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have h2 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have hpos : 0 ≤ B / ν * Real.exp (-ν * t) := by
    have : 0 ≤ B := by
      obtain ⟨e', -, hb⟩ := hd (S + 1) (by linarith)
      exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((abs_nonneg _).trans hb)
    positivity
  rw [abs_le]
  simp only at h1 h2
  constructor <;> nlinarith

/-- **Uniform-in-time prediction error under exponential residual decay.** Suppose, in addition to
the hypotheses of `abs_inner_displacement_add_frozenPrediction_le` on a window `[0, S]`, that the
Jacobian drift is bounded by `ε_J` for *all* times, the residual decays like
`‖r(s)‖ ≤ ‖r₀‖ exp(-ν s)`, and `K_inf` has a spectral gap `lam` with `ν ≤ lam / m`. Then for every
`t ≥ 0`, the prediction error `|⟪g, θ(t) - θ₀⟫ + a ⬝ᵥ (r₀ - exp(-(t/m) K_inf) r₀)|` is at most the
finite-window bound `S m⁻¹ (‖g‖ ε_J ‖r₀‖ + ε_k ‖r₀‖ + ‖k_inf‖ m⁻¹ ε_K ‖r₀‖ S)` plus the tail
`(m⁻¹ ‖r₀‖ (‖g‖ ε_J + ε_k + 2 ‖k_inf‖) / ν) exp(-ν S)`. On `[0, S]` this is the finite-time
theorem; beyond `S` the error curve has derivative bounded by a multiple of `exp(-ν s)` (residual
and frozen residual both decay), so it moves by at most the tail
(`abs_sub_le_of_abs_deriv_le_exp`). -/
theorem abs_inner_displacement_add_frozenPrediction_le_of_exp_decay
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (hm : 0 < (m : ℝ)) {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (g : EuclideanSpace ℝ (Fin P)) {S : ℝ} (hS : 0 ≤ S)
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (hK_inf : K_inf.PosSemidef) {lam : ℝ}
    (hlam : ∀ v : EuclideanSpace ℝ (Fin m), lam * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) {ε_J ε_K ε_k ν : ℝ} (hν : 0 < ν)
    (hνlam : ν ≤ lam / m)
    (hJ : ∀ s : ℝ, 0 ≤ s → ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ ≤ ε_J)
    (hK : ∀ s ∈ Set.Icc 0 S, ‖empiricalNTKMatrix f X (θ_traj s) - K_inf‖ ≤ ε_K)
    (hk : ‖(WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ g.ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 k_inf‖ ≤ ε_k)
    (hr : ∀ s : ℝ, 0 ≤ s → ‖trainingResidual f X y (θ_traj s)‖ ≤
      ‖trainingResidual f X y θ₀‖ * Real.exp (-ν * s)) :
    ∀ t : ℝ, 0 ≤ t →
      |⟪g, θ_traj t - θ₀⟫ + a ⬝ᵥ ((trainingResidual f X y θ₀).ofLp -
          NormedSpace.exp (-(t / (m : ℝ)) • K_inf) *ᵥ (trainingResidual f X y θ₀).ofLp)| ≤
        S * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖trainingResidual f X y θ₀‖ +
          ε_k * ‖trainingResidual f X y θ₀‖ + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
            ((m : ℝ)⁻¹ * (ε_K * ‖trainingResidual f X y θ₀‖) * S))) +
        ((m : ℝ)⁻¹ * ‖trainingResidual f X y θ₀‖ * (‖g‖ * ε_J + ε_k +
          2 * ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖)) / ν * Real.exp (-ν * S) := by
  set r₀ := trainingResidual f X y θ₀ with hr₀
  set kn : ℝ := ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ with hkn
  have hKsymm : K_inf.IsHermitian := hK_inf.isHermitian
  have hfin := abs_inner_displacement_add_frozenPrediction_le f X y hm hflow hdiff g hS K_inf hK_inf
    a k_inf hKa (fun s hs => hJ s hs.1) hK hk
  set e : ℝ → ℝ := fun s => ⟪g, θ_traj s - θ₀⟫ + a ⬝ᵥ (r₀.ofLp -
    NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) with he
  have hεJ : 0 ≤ ε_J := (norm_nonneg _).trans (hJ 0 le_rfl)
  have hεk : 0 ≤ ε_k := (norm_nonneg _).trans hk
  have hεK : 0 ≤ ε_K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hS⟩)
  have hr0n := norm_nonneg r₀
  have hkn0 : 0 ≤ kn := norm_nonneg _
  have hg0 := norm_nonneg g
  set Bc : ℝ := (m : ℝ)⁻¹ * ‖r₀‖ * (‖g‖ * ε_J + ε_k + 2 * kn) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  have hecont : ContinuousOn e (Set.Ici 0) := by
    intro s hs
    have h1 : ContinuousWithinAt (fun s => ⟪g, θ_traj s - θ₀⟫) (Set.Ici 0) s :=
      ((continuous_const.inner (continuous_id.sub continuous_const)).comp_continuousOn
        hflow.continuousOn) s hs
    have h2 := (hasDerivAt_frozenPrediction K_inf hKsymm a k_inf hKa r₀ s).continuousAt
    have h2' : ContinuousAt (fun u : ℝ => a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)) s := by
      convert h2.neg using 1
      funext u
      simp
    exact h1.add h2'.continuousWithinAt
  have hSfin : |e S| ≤ S * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
      kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S))) := hfin S ⟨hS, le_rfl⟩
  have htail : ∀ t, S ≤ t → |e t - e S| ≤ Bc / ν * Real.exp (-ν * S) := fun t ht =>
    abs_sub_le_of_abs_deriv_le_exp hν (hecont.mono (Set.Ici_subset_Ici.2 hS)) (fun s hs => by
      have hs0 : 0 ≤ s := hS.trans hs.le
      obtain ⟨e', hde, hbe⟩ := hasDerivAt_predictionError_abs_le f X y hm g K_inf hKsymm a k_inf
        hKa r₀ (hflow.ode s (hS.trans_lt hs)) (hdiff s) hk
      refine ⟨e', hde, hbe.trans ?_⟩
      have hrs := hr s hs0
      have hρs : ‖(WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) :
          EuclideanSpace ℝ (Fin m))‖ ≤ ‖r₀‖ * Real.exp (-ν * s) :=
        (matrix_exp_residual_decay K_inf r₀ lam hlam hm s hs0).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hνlam)])) hr0n)
      have hdiffn : ‖trainingResidual f X y (θ_traj s) -
          WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)‖ ≤
          2 * (‖r₀‖ * Real.exp (-ν * s)) :=
        (norm_sub_le _ _).trans (by linarith)
      have hJs := hJ s hs0
      have hexp0 := Real.exp_pos (-ν * s)
      calc (m : ℝ)⁻¹ * (‖trainingResidual f X y (θ_traj s)‖ *
            (‖g‖ * ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ + ε_k) +
          kn * ‖trainingResidual f X y (θ_traj s) -
            WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)‖)
          ≤ (m : ℝ)⁻¹ * (‖r₀‖ * Real.exp (-ν * s) * (‖g‖ * ε_J + ε_k) +
            kn * (2 * (‖r₀‖ * Real.exp (-ν * s)))) := by
            gcongr
        _ = Bc * Real.exp (-ν * s) := by rw [hBc]; ring) ht
  intro t ht
  by_cases hts : t ≤ S
  · refine (hfin t ⟨ht, hts⟩).trans ?_
    have hbr : 0 ≤ (m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
        kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S)) := by positivity
    have : t * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
        kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S))) ≤ S * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
        kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S))) := mul_le_mul_of_nonneg_right hts hbr
    have htl : 0 ≤ Bc / ν * Real.exp (-ν * S) := by positivity
    linarith
  · have hSt : S ≤ t := (not_le.1 hts).le
    have h1 := htail t hSt
    have h2 : |e t| ≤ |e S| + |e t - e S| := by
      have := abs_add_le (e S) (e t - e S)
      simpa using this
    exact h2.trans (add_le_add hSfin h1)

end NTK

end
