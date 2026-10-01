/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.ODEStability

/-!
# Gradient flow: fixed-feature (affine) dynamics and minimum norm

Training with fixed features: the affine flow, its minimum-norm limit and the kernel-regression
interpolant.

## Main results and proof outline

* `NTK.minNorm_pythagoras`, `NTK.matrixCLM_transpose_eq_adjoint` : minimum-norm Pythagoras for any
  bounded linear map between real Hilbert spaces, and the adjoint identity for `matrixCLM`.
* `NTK.matrixCLM`, `NTK.inner_matrixCLM_transpose`, `NTK.hasDerivAt_affineFlowSolution`,
  `NTK.affineFlow_eq_solution`, `NTK.affine_minNorm_pythagoras`, `NTK.norm_affine_limit_le`,
  `NTK.eq_affine_limit_of_norm_le`, `NTK.tendsto_affineFlowSolution`, `NTK.inner_affine_limit` :
  Phase 14.1 - for an arbitrary matrix `J` with invertible Gram matrix `J Jᵀ`, the closed form of
  the affine gradient flow, its convergence to the minimum-norm interpolant `-Jᵀ (J Jᵀ)⁻¹ r₀`,
  the Pythagoras identity proving minimality, and the kernel-regression form of its prediction.

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

/-! ### Fixed-Feature (Affine) Dynamics and Minimum Norm

For a fixed matrix `J : Matrix (Fin m) (Fin P) ℝ` (the frozen output Jacobian at initialization) the
affine model `f₀ + J (θ - θ₀)` has residual `r₀ + J w`, `w = θ - θ₀`, and its gradient flow is
`w' = -(1/m) Jᵀ (r₀ + J w)`. Everything below is stated for an arbitrary `J`, independent of
networks; `Jᵀ (J Jᵀ)⁻¹` is the Moore-Penrose pseudo-inverse of a full-row-rank `J`. -/

/-- Solution of the affine (frozen-feature) gradient flow `w' = -(1/m) Jᵀ (r₀ + J w)`, `w 0 = 0`,
when the Gram matrix `J Jᵀ` is invertible:
`w(t) = -Jᵀ (J Jᵀ)⁻¹ (r₀ - exp(-(t/m) J Jᵀ) r₀)`. -/
theorem hasDerivAt_affineFlowSolution (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s => matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
        WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (Jᵀ *ᵥ (r₀.ofLp + J *ᵥ (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
        WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp))).ofLp)))) t := by
  have h := ((matrix_exp_residual_trajectory_hasDerivAt (J * Jᵀ) r₀ t).const_sub r₀)
  have h2 := (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹))).hasFDerivAt.comp_hasDerivAt t h
  refine h2.congr_deriv ?_
  set res : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp) with hres
  have hGinv : (J * Jᵀ) * (J * Jᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
  have hGinv' : (J * Jᵀ)⁻¹ * (J * Jᵀ) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
  simp only [matrixCLM_apply]
  have hJw : ∀ v : Fin m → ℝ, J *ᵥ (-(Jᵀ * (J * Jᵀ)⁻¹) *ᵥ v) = -v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_neg, ← Matrix.mul_assoc, hGinv, Matrix.neg_mulVec,
      Matrix.one_mulVec]
  congr 1
  rw [hJw]
  have hJT : ∀ v : Fin m → ℝ, -(Jᵀ * (J * Jᵀ)⁻¹) *ᵥ (-(-(m : ℝ)⁻¹ • ((J * Jᵀ) *ᵥ v))) =
      -(m : ℝ)⁻¹ • (Jᵀ *ᵥ v) := fun v => by
    rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, hGinv', Matrix.mul_one]
  simpa [hres] using hJT (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)

/-- **Minimum-norm Pythagoras for a bounded linear map between inner product spaces.** If
`wInf = A† a` interpolates (`A wInf = b`) -- the normal-equation solution, with `a` solving
`A A† a = b` -- then every `w'` with `A w' = b` satisfies `‖w'‖² = ‖wInf‖² + ‖w' - wInf‖²`; hence
`wInf` is the unique minimum-norm interpolant. The matrix statement `affine_minNorm_pythagoras` is
the case `A = matrixCLM J`. -/
theorem minNorm_pythagoras {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (b a : F) {wInf : E} (hw : wInf = ContinuousLinearMap.adjoint A a)
    (hinterp : A wInf = b) {w' : E} (hw' : A w' = b) :
    ‖w'‖ ^ 2 = ‖wInf‖ ^ 2 + ‖w' - wInf‖ ^ 2 := by
  have hk : A (w' - wInf) = 0 := by rw [map_sub, hw', hinterp, sub_self]
  have horth : ⟪wInf, w' - wInf⟫ = 0 := by
    calc ⟪wInf, w' - wInf⟫ = ⟪ContinuousLinearMap.adjoint A a, w' - wInf⟫ := by rw [← hw]
      _ = 0 := by rw [ContinuousLinearMap.adjoint_inner_left, hk, inner_zero_right]
  have h : w' = wInf + (w' - wInf) := by abel
  conv_lhs => rw [h]
  rw [norm_add_sq_real, horth]
  ring

/-- **Minimum-norm characterization of the affine-flow limit.** Let `J` have invertible Gram matrix
`J Jᵀ` and put `wInf = -Jᵀ (J Jᵀ)⁻¹ r₀`. Then `J wInf = -r₀`, and every `w'` with `J w' = -r₀`
satisfies `‖w'‖² = ‖wInf‖² + ‖w' - wInf‖²`; hence `wInf` is the unique minimum-norm solution of the
interpolation constraint `f₀ + J w = y` (`r₀ = f₀ - y`). The increment `wInf` lies in the range of
`Jᵀ` (`(ker J)ᗮ`), so it is orthogonal to `ker J`. This is proved directly by Pythagoras from the
adjoint identity `inner_matrixCLM_transpose`, which is all `LinearMap.orthogonal_ker` would
supply. -/
theorem affine_minNorm_pythagoras (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w' : EuclideanSpace ℝ (Fin P)}
    (hw' : J *ᵥ w'.ofLp = -r₀.ofLp) :
    J *ᵥ (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀).ofLp = -r₀.ofLp ∧
      ‖w'‖ ^ 2 = ‖matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ^ 2 +
        ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ^ 2 := by
  have hGinv : (J * Jᵀ) * (J * Jᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
  set wInf := matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ with hwInf
  have hJw : J *ᵥ wInf.ofLp = -r₀.ofLp := by
    rw [hwInf, matrixCLM_apply]
    change J *ᵥ (-(Jᵀ * (J * Jᵀ)⁻¹) *ᵥ r₀.ofLp) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_neg, ← Matrix.mul_assoc, hGinv, Matrix.neg_mulVec,
      Matrix.one_mulVec]
  refine ⟨hJw, ?_⟩
  have hrange : wInf = ContinuousLinearMap.adjoint (matrixCLM J) (matrixCLM (-(J * Jᵀ)⁻¹) r₀) := by
    rw [← matrixCLM_transpose_eq_adjoint, hwInf]
    ext i : 1
    simp [matrixCLM_apply, Matrix.mulVec_mulVec, Matrix.mul_neg]
  exact minNorm_pythagoras (matrixCLM J) (-r₀) _ hrange
    (by rw [matrixCLM_apply, hJw]; rfl) (by rw [matrixCLM_apply, hw']; rfl)

/-- The affine-flow limit `wInf` has the least norm among all solutions of `J w = -r₀`. -/
theorem norm_affine_limit_le (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w' : EuclideanSpace ℝ (Fin P)}
    (hw' : J *ᵥ w'.ofLp = -r₀.ofLp) :
    ‖matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ≤ ‖w'‖ := by
  have h := (affine_minNorm_pythagoras J hG r₀ hw').2
  exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖])
    (norm_nonneg _) |>.2

/-- Uniqueness of the minimum-norm interpolant. -/
theorem eq_affine_limit_of_norm_le (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w' : EuclideanSpace ℝ (Fin P)}
    (hw' : J *ᵥ w'.ofLp = -r₀.ofLp)
    (hle : ‖w'‖ ≤ ‖matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖) :
    w' = matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ := by
  have h := (affine_minNorm_pythagoras J hG r₀ hw').2
  have h0 : ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖, norm_nonneg w',
      norm_nonneg (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀)]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h0))


/-- **The minimum-norm interpolant predicts by kernel regression.** For the affine limit
`w∞ = -Jᵀ (J Jᵀ)⁻¹ r₀` and any feature vector `g`, `⟪g, w∞⟫ = -(J g) ⬝ᵥ ((J Jᵀ)⁻¹ r₀)`. With
`J = J(θ₀)`, `g = ∇f(x; θ₀)`, `r₀ = f₀(X) - y` this is `(J g)ᵀ (J Jᵀ)⁻¹ (y - f₀(X)) =
k₀(x, X)ᵀ K₀⁻¹ (y - f₀(X))`: the frozen-feature minimum-norm predictor is the kernel-regression
formula with the empirical kernels `K₀`, `k₀`. The limiting formula replaces them by `K_∞`,
`k_∞`. -/
theorem inner_affine_limit (J : Matrix (Fin m) (Fin P) ℝ) (r₀ : EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin P)) :
    ⟪g, matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀⟫ = -((J *ᵥ g.ofLp) ⬝ᵥ ((J * Jᵀ)⁻¹ *ᵥ r₀.ofLp)) := by
  have hrange : matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ =
      matrixCLM Jᵀ (matrixCLM (-(J * Jᵀ)⁻¹) r₀) := by
    ext i : 1
    simp [matrixCLM_apply, Matrix.mulVec_mulVec, Matrix.mul_neg]
  rw [hrange, real_inner_comm, inner_matrixCLM_transpose]
  simp [matrixCLM_apply, PiLp.inner_apply, dotProduct, Matrix.neg_mulVec]

/-- **Closed form of the affine (frozen-feature) gradient flow.** Let `J` have invertible Gram
matrix.
Any forward-time solution of `w' = -(1/m) Jᵀ (r₀ + J w)`, `w(0) = 0` -- the gradient flow of the
affine model `f₀ + J w` under the mean-squared loss with residual `r₀ + J w` -- equals
`w(t) = -Jᵀ (J Jᵀ)⁻¹ (r₀ - exp(-(t/m) J Jᵀ) r₀)` for `t ≥ 0`. In particular `w(t)` lies in the range
of `Jᵀ`. Uniqueness is `forwardFlow_unique` (the field is affine, hence Lipschitz). -/
theorem affineFlow_eq_solution (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w : ℝ → EuclideanSpace ℝ (Fin P)} (hw0 : w 0 = 0)
    (hwc : ContinuousOn w (Set.Ici 0))
    (hw : ∀ t : ℝ, 0 < t → HasDerivAt w
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (Jᵀ *ᵥ (r₀.ofLp + J *ᵥ (w t).ofLp)))) t) {t : ℝ} (ht : 0 ≤ t) :
    w t = matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)) := by
  set V : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin P) := fun x =>
    WithLp.toLp 2 (-(m : ℝ)⁻¹ • (Jᵀ *ᵥ (r₀.ofLp + J *ᵥ x.ofLp))) with hV
  have hVsub : ∀ x y, V x - V y = matrixCLM (-(m : ℝ)⁻¹ • (Jᵀ * J)) (x - y) := fun x y => by
    ext i : 1
    simp [hV, matrixCLM_apply, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.neg_mulVec, Matrix.smul_mulVec]
  have hLip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : EuclideanSpace ℝ (Fin P), ‖x‖ ≤ A → ‖y‖ ≤ A →
      ‖V x - V y‖ ≤ K * ‖x - y‖ := fun A =>
    ⟨‖matrixCLM (-(m : ℝ)⁻¹ • (Jᵀ * J))‖, norm_nonneg _, fun x y _ _ => by
      rw [hVsub]; exact (matrixCLM (-(m : ℝ)⁻¹ • (Jᵀ * J))).le_opNorm _⟩
  have hsolc : ContinuousOn (fun s : ℝ => matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp))) (Set.Ici 0) :=
    fun s _ => (hasDerivAt_affineFlowSolution J hG r₀ s).continuousAt.continuousWithinAt
  have h0 : matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(0 / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)) = 0 := by
    have := matrix_exp_residual_trajectory_zero (J * Jᵀ) r₀
    rw [show -(0 / (m : ℝ)) = -(0 * (m : ℝ)⁻¹) by ring, this, sub_self, map_zero]
  exact forwardFlow_unique V hLip hwc (fun s hs => hw s hs) hsolc
    (fun s _ => hasDerivAt_affineFlowSolution J hG r₀ s) (by rw [hw0, h0]) ht


/-- **The affine flow converges to the minimum-norm interpolant.** If the Gram matrix `J Jᵀ` is
positive definite, the closed-form affine flow `w(t)` converges to `w∞ = -Jᵀ (J Jᵀ)⁻¹ r₀`, with
exponential rate `λ_min(J Jᵀ) / m`; the limit interpolates (`J w∞ = -r₀`) and has least norm
(`norm_affine_limit_le`). -/
theorem tendsto_affineFlowSolution (hm : 0 < m) (J : Matrix (Fin m) (Fin P) ℝ)
    (hG : (J * Jᵀ).PosDef) (r₀ : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun t : ℝ => matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp))) atTop
      (𝓝 (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀)) := by
  obtain ⟨c, hc, hcgap⟩ := exists_pos_sub_smul_one_posSemidef_of_posDef hG
  have hrr := rayleigh_lower_bound_of_sub_smul_posSemidef _ c hcgap
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_zero_of_le_mul_exp_neg (L₀ := ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * ‖r₀‖)
    (c := c / m) (by positivity) (fun t _ => norm_nonneg _) fun t ht => ?_
  set res : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp) with hres
  have hdiff : matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ - res) - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ =
      matrixCLM (Jᵀ * (J * Jᵀ)⁻¹) res := by
    rw [← map_sub, sub_sub_cancel_left, map_neg]
    ext i : 1
    simp [matrixCLM_apply, Matrix.neg_mulVec]
  rw [hdiff]
  calc ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹) res‖ ≤ ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * ‖res‖ :=
        (matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)).le_opNorm _
    _ ≤ ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * (‖r₀‖ * Real.exp (-(c / (m : ℝ)) * t)) := by
        gcongr
        exact matrix_exp_residual_decay (J * Jᵀ) r₀ c hrr hmR t ht
    _ = ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * ‖r₀‖ * Real.exp (-(c / (m : ℝ)) * t) := by ring

end NTK

end
