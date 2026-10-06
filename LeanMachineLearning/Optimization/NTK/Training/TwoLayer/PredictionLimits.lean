/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.CrossKernel

/-!
# Training limits of the two-layer network: predictions and weak limits

train-test cross-kernel and finite-horizon: the trained residual and the test prediction follow
their closed-form
matrix-exponential predictors in probability, at fixed times and uniformly in time under a gap, and
converge to the ridgeless kernel-regression interpolant; plus the fixed-time weak limits of the
trained residual and outputs.

## Main results and proof outline

- `tendsto_measure_kernel_drift_finite_horizon`,
  `tendstoInDistribution_trainingResidual_matrix_exp`,
  `tendstoInDistribution_trainingOutputs_matrix_exp` : Finite-horizon kernel
  stationarity in probability and fixed-time weak limits of the trained residual and predictions
  (`exp(-(t / m) K_∞) (G - y)` and `y + exp(-(t / m) K_∞) (G - y)`), with no spectral gap.

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

/-- **Actual residual vs. frozen matrix-exponential residual, in probability.** If the trajectories
`θ n p` solve the gradient-flow ODE for almost every initialization, then at each fixed time `t ≥ 0`
the trained residual `r_n(t)` and the frozen residual `exp(-(t / m) K_∞) r_n(0)` are asymptotically
equal: for every `ε₀ > 0`, `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n) {ε₀ ≤ ‖r_n(t) - exp(-(t / m) K_∞) r_n(0)‖} → 0`
(outer probability, as for `tendsto_measure_kernel_drift_finite_horizon`). No spectral gap is
assumed. -/
theorem tendsto_measure_residual_sub_matrix_exp_finite_horizon
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)) {p | ε₀ ≤
        ‖trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t) -
          (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)).ofLp) :
            EuclideanSpace ℝ (Fin m))‖})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨c, hc, hcκ⟩ := exists_pos_real_ofReal_le hκ
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hφ := hact.differentiable
  have hC₁_bdd := hact.deriv_bdd
  have hderiv_lip := hact.deriv_lip
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  obtain ⟨hL2, hL2mul, hdL2, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ Xs α)) 2 (Measure.pi fun _ : Fin d =>
      gaussianReal 0 1) :=
    fun α => hL2 (Xs α)
  have hdφ_out_L2 : ∀ α, MemLp (fun w => deriv φ (w ⬝ᵥ Xs α)) 2 (Measure.pi fun _ : Fin d =>
      gaussianReal 0 1) :=
    fun α => hdL2 (Xs α)
  have hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⬝ᵥ Xs α) * φ (w ⬝ᵥ Xs β)) 2 (Measure.pi fun _ : Fin d =>
          gaussianReal 0 1) :=
    fun α β => hL2mul (Xs α) (Xs β)
  have hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⬝ᵥ Xs α) * deriv φ (w ⬝ᵥ Xs β)) 2 (Measure.pi fun _ : Fin d =>
          gaussianReal 0 1) :=
    fun α β => hdL2mul (Xs α) (Xs β)
  have hK_inf : ∀ v : EuclideanSpace ℝ (Fin m),
      0 ≤ v.ofLp ⬝ᵥ (limitingFullNTKMatrix φ X *ᵥ v.ofLp) :=
    dotProduct_mulVec_nonneg_of_posSemidef
      (limitingFullNTKMatrix_posSemidef φ X hmeasφ hderiv_meas hφ_out_L2 hdφ_out_L2)
  obtain ⟨R, freezeRate, N, hR, hrate, h⟩ := exists_measurableSet_finite_horizon_kernel_freeze hm φ
    hact X y t ht (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
    (min_le_left _ _) (by positivity)
  -- Kernel error budget `e`, chosen so that `(1 / m) * (2 e) * R * t < ε₀`.
  set cst : ℝ := (m : ℝ)⁻¹ * R * t with hcst
  have hcst_nonneg : 0 ≤ cst := by positivity
  set e : ℝ := ε₀ / (2 * (cst + 1)) with he_def
  have he : 0 < e := by positivity
  have hU := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X hφ_L2 hdφ_L2
    he
  filter_upwards [Filter.eventually_ge_atTop N, hrate.eventually (gt_mem_nhds he),
    hU.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
    with n hn hfr hUn
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  have hEc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ ≤ c / 2 := by
    rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  have hnull : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)) {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y)
      (packParams p.1 p.2) (θ n p)} = 0 := ae_iff.1 (hθ_flow n)
  calc ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
      fun _ : Fin n => gaussianReal 0 1)) {p | ε₀ ≤ ‖trainingResidual (netFromParams φ n d) Xs y
          (θ n p t) -
          (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)).ofLp) :
            EuclideanSpace ℝ (Fin m))‖}
      ≤ ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)) ((Eᶜ ∪ {p | e ≤ ‖empiricalNTKMatrix (netFromParams φ n
          d) Xs
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖}) ∪
          {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
            (θ n p)}) := by
        refine measure_mono fun p hp => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not,
          not_le] at hcon
        obtain ⟨⟨hpE, hpU⟩, hflow⟩ := hcon
        obtain ⟨hres0, hEK⟩ := hEp p hpE
        have hdiff : ∀ u : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
            (fun θ' => netFromParams φ n d (Xs β) θ') (θ n p u) := fun u β =>
          (hasFDerivAt_netFromParams φ n d (Xs β) (θ n p u)
            fun i => hφ.differentiableAt).differentiableAt
        have hKb : ∀ u ∈ Set.Icc (0 : ℝ) t,
            ‖empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p u) -
              limitingFullNTKMatrix φ X‖ ≤ 2 * e := by
          intro u hu
          have h1 := hEK (θ n p) hflow u hu
          have h2 := norm_sub_le_norm_sub_add_norm_sub
            (empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p u))
            (empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2))
            (limitingFullNTKMatrix φ X)
          linarith
        have happrox := residual_sub_matrix_exp_le
          (fun u => empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p u))
          (limitingFullNTKMatrix φ X)
          (fun u => trainingResidual (netFromParams φ n d) Xs y (θ n p u)) (T := t) ht hm'
          (continuousOn_trainingResidual_comp (netFromParams φ n d) Xs y (s := Set.Icc 0 t)
            (hflow.continuousOn.mono Set.Icc_subset_Ici_self) fun u _ => hdiff u)
          (fun u hu => gradient_flow_residual_vector_ode (netFromParams φ n d) Xs y u
            (hflow.ode u hu.1) (hdiff u))
          (fun u _ v => dotProduct_mulVec_nonneg_of_posSemidef
            (empiricalNTKMatrix_posSemidef _ _ _) v) hK_inf hKb t ⟨ht, le_rfl⟩
        simp only [hflow.init] at happrox
        have hbound : (m : ℝ)⁻¹ * (2 * e * ‖trainingResidual (netFromParams φ n d) Xs y
            (packParams p.1 p.2)‖) * t ≤ 2 * e * cst := by
          rw [hcst]
          have : 0 ≤ e := he.le
          calc (m : ℝ)⁻¹ * (2 * e * ‖trainingResidual (netFromParams φ n d) Xs y
                (packParams p.1 p.2)‖) * t ≤ (m : ℝ)⁻¹ * (2 * e * R) * t := by gcongr
            _ = 2 * e * ((m : ℝ)⁻¹ * R * t) := by ring
        have hlt : 2 * e * cst < ε₀ := by
          rw [he_def]
          have hpos : 0 < cst + 1 := by linarith
          rw [show 2 * (ε₀ / (2 * (cst + 1))) * cst = ε₀ * (cst / (cst + 1)) by
            field_simp]
          have : cst / (cst + 1) < 1 := (div_lt_one hpos).2 (by linarith)
          nlinarith
        rw [Set.mem_ofPred_eq] at hp
        linarith [hp, happrox, hbound, hlt]
    _ ≤ ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
        fun _ : Fin n => gaussianReal 0 1)) (Eᶜ ∪ {p | e ≤ ‖empiricalNTKMatrix
            (netFromParams φ n d) Xs
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖}) + 0 := by
        rw [← hnull]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 4) := by
        rw [add_zero]
        refine (measure_union_le _ _).trans (add_le_add ?_ hUn.le)
        exact measure_le_ofReal_of_measureReal_le _ hEc
    _ ≤ κ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hcκ

/-- **Fixed-time test prediction (finite horizon, no spectral gap).** Let `θ n p` be trajectories
solving the gradient-flow ODE for almost every initialization, let `K_∞ = limitingFullNTKMatrix φ X`
be invertible and `k_∞(x, X)_α` the train-test entry of the limiting NTK of the extended dataset
`(X, x)`. Then for every fixed `t ≥ 0`, test input `x` and `ε₀ > 0`, the probability that the
trained network output at `x` deviates from the kernel-regression prediction
`f₀(x) - a ⬝ᵥ (r₀ - exp(-(t / m) K_∞) r₀)`, `a = K_∞⁻¹ k_∞(x, X)`, `r₀ = f₀(X) - y`, by more than
`ε₀` tends to zero. Equivalently `f_t(x) ≈ f₀(x) + k_∞(x, X)ᵀ K_∞⁻¹ (I - exp(-(t / m) K_∞))
(y - f₀(X))`, the closed-form predictor of the source, where `f₀` is the (random) initial network.
The proof combines the Taylor bound at the test input, the Jacobian and kernel drift of the
finite-horizon lazy-training event, initialization concentration of the extended NTK Gram matrix
(whose last row is the train-test cross-kernel, so no separate cross-kernel concentration is
needed),
and the deterministic `abs_inner_displacement_add_frozenPrediction_le`. -/
theorem tendsto_measure_test_prediction_finite_horizon
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hKinv : IsUnit (limitingFullNTKMatrix φ X)) (t : ℝ) (ht : 0 ≤ t) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)) {p | ε₀ <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          ((limitingFullNTKMatrix φ X)⁻¹ *ᵥ (fun α : Fin m =>
            limitingFullNTKMatrix φ (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
              Fin d → ℝ) (Fin.last m) (Fin.castSucc α))) ⬝ᵥ
            ((trainingResidual (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X) *ᵥ
                (trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp)|})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  set xs : Fin d → ℝ := fun j => (Real.sqrt (d : ℝ))⁻¹ * x j with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L : Matrix (Fin m) (Fin m) ℝ := limitingFullNTKMatrix φ X with hL
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  set kv : Fin m → ℝ := fun α => L' (Fin.last m) (Fin.castSucc α) with hkv
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hC₁, hC₂, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd hact.deriv_lip hφ
  obtain ⟨hL2, hL2mul, hdL2, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hK_inf : L.PosSemidef :=
    limitingFullNTKMatrix_posSemidef φ X hmeasφ hderiv_meas (fun α => hL2 (Xs α))
      (fun α => hdL2 (Xs α))
  have hLa : L *ᵥ (L⁻¹ *ᵥ kv) = kv := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hKinv),
      Matrix.one_mulVec]
  refine (tendsto_measure_exists_gt_of_eventually_good_events (fun n => ((Measure.pi fun _ : Fin n
      => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1))) {t}
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t' => |netFromParams φ n d xs (θ n p t') -
        netFromParams φ n d xs (θ n p 0) +
      (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp -
        NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
          (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp)|) hθ_flow
    (ε₀ := ε₀) (fun c hc => ?hev)).congr (fun n => ?heq)
  case heq =>
    congr 1
    ext p
    simp
  case hev =>
    -- the finite-horizon lazy-training event
    obtain ⟨R, C, _, freezeRate, jacRate, taylorRate, N, hR0, hfr, hjr, -, h⟩ :=
      exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y t ht
        (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity)) (min_le_left _ _)
        (by positivity)
    set δ : ℝ := min 1 (c / 8) with hδ
    have hδpos : 0 < δ := lt_min one_pos (by positivity)
    -- constants of the error budget
    set kn : ℝ := ‖(WithLp.toLp 2 kv : EuclideanSpace ℝ (Fin m))‖ with hkn
    set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
    set A₁ : ℝ := t * ((m : ℝ)⁻¹ * (G₀ * R)) with hA₁
    set A₂ : ℝ := t * ((m : ℝ)⁻¹ * (kn * ((m : ℝ)⁻¹ * R * t))) with hA₂
    set a₁ : ℝ := t * ((m : ℝ)⁻¹ * R) + A₂ with ha₁
    have hA₁0 : 0 ≤ A₁ := by positivity
    have hA₂0 : 0 ≤ A₂ := by positivity
    have ha₁0 : 0 ≤ a₁ := by positivity
    set e : ℝ := min 1 (ε₀ / (4 * (a₁ + 1))) with he_def
    have he : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have hea : a₁ * e ≤ ε₀ / 4 := by
      have h1 : e ≤ ε₀ / (4 * (a₁ + 1)) := min_le_right _ _
      calc a₁ * e ≤ (a₁ + 1) * (ε₀ / (4 * (a₁ + 1))) :=
            mul_le_mul (by linarith) h1 he.le (by positivity)
        _ = ε₀ / 4 := by field_simp
    -- initialization concentration: training kernel and extended kernel
    have hU := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X
      (fun α β => hL2mul (Xs α) (Xs β)) (fun α β => hdL2mul (Xs α) (Xs β)) he
    have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ
      hderiv_meas X'
      (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) he
    have hτ := tendsto_testLinearizationRate xs C₁ C₂ C hδpos
    have hsmall : Filter.Tendsto (fun n => taylorRate n * 0 + 0) Filter.atTop (nhds 0) := by simp
    have hb : Filter.Tendsto (fun n : ℕ =>
        (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 *
        C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
        Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n) Filter.atTop
        (nhds 0) := by
      simpa using (hτ.add (hjr.const_mul A₁)).add (hfr.const_mul A₂)
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0,
      hb.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 2 by positivity)),
      hU.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity))),
      hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
      with n hn hn0 hbn hUn hUn'
    obtain ⟨E, hEm, hE, hEp⟩ := h n hn
    set U : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖} with hUdef
    set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
    have hUm : MeasurableSet U :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas Xs L e
    have hUm' : MeasurableSet U' :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' e
    have hUr : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real U ≤ c / 4 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hUn.le
    have hU'r : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real U' ≤ c / 4 := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
      simp only [hU'def, ← this]
      exact hUn'.le
    refine ⟨(E ∩ Uᶜ) ∩ U'ᶜ, (hEm.inter hUm.compl).inter hUm'.compl, ?_, ?_⟩
    · have hEc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ ≤ c / 4 + c / 4 := by
        rw [probReal_compl_eq_one_sub hEm]
        have := min_le_right 1 (c / 8)
        have h2 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
        linarith
      have := (measureReal_compl_inter_le ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
          gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) (E ∩ Uᶜ) U'ᶜ)
      have h2 := measureReal_compl_inter_le ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d
          => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) E Uᶜ
      rw [compl_compl] at this h2
      linarith
    · rintro p ⟨⟨hpE, hpU⟩, hpU'⟩ hflow t' ht'
      have ht'eq : t' = t := ht'
      obtain ⟨hres0, hp2, -, hall⟩ := hEp p hpE
      have hpU1 : ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖ < e :=
        not_le.1 hpU
      have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
          Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < e := not_le.1 hpU'
      set θ₀ := packParams p.1 p.2 with hθ₀
      set g : EuclideanSpace ℝ (Fin (n * d + n)) :=
        tangentFeature (netFromParams φ n d) xs θ₀ with hg
      simp only [ht'eq, hflow.init]
      have hdiff : ∀ u : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
          (fun θ' => netFromParams φ n d (Xs β) θ') (θ n p u) := fun u β =>
        (hasFDerivAt_netFromParams φ n d (Xs β) (θ n p u)
          fun i => hφ.differentiableAt).differentiableAt
      have hallt := fun s (hs : s ∈ Set.Icc (0 : ℝ) t) => hall (θ n p) hflow s hs
      have hJ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖outputJacobian (netFromParams φ n d) Xs (θ n p s) -
          outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ jacRate n := fun s hs => (hallt s hs).2.1
      have hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s) -
          L‖ ≤ freezeRate n + e := fun s hs => by
        have h1 := (hallt s hs).1
        have h2 := norm_sub_le_norm_sub_add_norm_sub
          (empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s))
          (empiricalNTKMatrix (netFromParams φ n d) Xs θ₀) L
        linarith
      have hrow := norm_row_castSucc_le
        (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
          Fin (m + 1) → Fin d → ℝ) θ₀ - L') (Fin.last m)
      have hk : ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ g.ofLp) :
          EuclideanSpace ℝ (Fin m)) - WithLp.toLp 2 kv‖ ≤ e := by
        refine le_of_eq_of_le ?_ (hrow.1.trans hpU2.le)
        congr 1
        ext α
        simp only [PiLp.sub_apply, Matrix.sub_apply, hg, hkv, hL']
        rw [outputJacobian_mulVec_tangentFeature, (empiricalNTKMatrix_snoc_last _ _ _ _ α).1]
      have hgnorm : ‖g‖ ≤ G₀ := by
        rw [hG₀]
        refine Real.le_sqrt_of_sq_le ?_
        have h1 : ‖g‖ ^ 2 = empiricalNTKMatrix (netFromParams φ n d)
            (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) θ₀
            (Fin.last m) (Fin.last m) := by
          rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2, hg,
            real_inner_self_eq_norm_sq]
        have h2 := hrow.2
        rw [Matrix.sub_apply] at h2
        have h3 := (abs_le.1 (h2.trans hpU2.le)).2
        have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
        rw [h1]
        linarith
      have hKa' := abs_inner_displacement_add_frozenPrediction_le (netFromParams φ n d) Xs y hm'
        hflow hdiff g ht L hK_inf (L⁻¹ *ᵥ kv) kv hLa hJ hK hk t ⟨ht, le_rfl⟩
      have hg' : gradParams φ n d xs θ₀ = g := (tangentFeature_netFromParams_of_differentiable φ
        hφ n d xs θ₀).symm
      have hreadout : ∀ i : Fin n, |θ₀ (paramIndexEquiv n d (Sum.inr i))| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) :=
        fun i => by simpa only [hθ₀, packParams_readout] using hp2 i
      have hdisp := (hallt t ⟨ht, le_rfl⟩).2.2.2
      have htay := abs_netFromParams_sub_linearization_le_of_disp hact hn0 xs hreadout hdisp
      rw [hg'] at htay
      -- collect the error budget
      have hjr0 : 0 ≤ jacRate n := (norm_nonneg _).trans (hJ 0 ⟨le_rfl, ht⟩)
      have hfr0 : 0 ≤ freezeRate n := (norm_nonneg _).trans (hallt 0 ⟨le_rfl, ht⟩).1
      have hr0 : ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤ R := hres0
      have hr00 := norm_nonneg (trainingResidual (netFromParams φ n d) Xs y θ₀)
      have hkn0 : 0 ≤ kn := norm_nonneg _
      have hbudget : t * ((m : ℝ)⁻¹ * (‖g‖ * jacRate n *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + e *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + kn *
            ((m : ℝ)⁻¹ * ((freezeRate n + e) *
              ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖) * t))) ≤
          A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
        have hgR : ‖g‖ * jacRate n * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤
            G₀ * jacRate n * R := by gcongr
        have hrR : kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖) * t) ≤
            kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) * R) * t) := by gcongr
        calc _ ≤ t * ((m : ℝ)⁻¹ * (G₀ * jacRate n * R + e * R +
              kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) * R) * t))) := by
              gcongr
          _ = A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
              rw [hA₁, hA₂, ha₁]; ring
      have hD : |netFromParams φ n d xs (θ n p t) - netFromParams φ n d xs θ₀ +
          (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
            NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
              (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)| ≤
          (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 + (A₁ * jacRate n + A₂ * freezeRate n + a₁ * e) := by
        have hsplit : netFromParams φ n d xs (θ n p t) - netFromParams φ n d xs θ₀ +
            (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
                (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp) =
            (netFromParams φ n d xs (θ n p t) - netFromParams φ n d xs θ₀ - ⟪g, θ n p t - θ₀⟫) +
              (⟪g, θ n p t - θ₀⟫ + (L⁻¹ *ᵥ kv) ⬝ᵥ
                ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
                  NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
                    (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)) := by ring
        rw [hsplit]
        exact (abs_add_le _ _).trans (add_le_add htay (hKa'.trans hbudget))
      have hbn' : (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n < ε₀ / 2 := hbn
      linarith

/-- **Test prediction uniformly in time under a positive limiting gap.** Let `K_∞ =
limitingFullNTKMatrix φ X` be positive definite (for instance under feature independence,
`limitingFullNTKMatrix_posDef_of_ae_independent`) and `θ n p` gradient-flow trajectories for almost
every initialization. For every test input `x` and `ε₀ > 0` the probability that, at *some* time
`t ≥ 0`, the trained output at `x` deviates from `f₀(x) - a ⬝ᵥ (r₀ - exp(-(t / m) K_∞) r₀)`,
`a = K_∞⁻¹ k_∞(x, X)`, by more than `ε₀` tends to zero. This is
`tendsto_measure_test_prediction_finite_horizon` with the horizon removed: the positive gap makes
the residual, the frozen residual and hence the error curve's derivative decay exponentially, which
controls the tail beyond a window
(`abs_inner_displacement_add_frozenPrediction_le_of_exp_decay`). -/
theorem tendsto_measure_test_prediction_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hKpd : (limitingFullNTKMatrix φ X).PosDef) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)) {p | ∃ t ∈ Set.Ici (0 : ℝ), ε₀ <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          ((limitingFullNTKMatrix φ X)⁻¹ *ᵥ (fun α : Fin m =>
            limitingFullNTKMatrix φ (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
              Fin d → ℝ) (Fin.last m) (Fin.castSucc α))) ⬝ᵥ
            ((trainingResidual (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X) *ᵥ
                (trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp)|})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  set xs : Fin d → ℝ := fun j => (Real.sqrt (d : ℝ))⁻¹ * x j with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L : Matrix (Fin m) (Fin m) ℝ := limitingFullNTKMatrix φ X with hL
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  set kv : Fin m → ℝ := fun α => L' (Fin.last m) (Fin.castSucc α) with hkv
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hC₁, hC₂, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd hact.deriv_lip hφ
  obtain ⟨hL2, hL2mul, hdL2, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hKinv : IsUnit L := hKpd.isUnit
  have hK_inf : L.PosSemidef := hKpd.posSemidef
  obtain ⟨lam, hlam, hgapK⟩ := exists_pos_sub_smul_one_posSemidef_of_posDef hKpd
  have hrr := rayleigh_lower_bound_of_sub_smul_posSemidef L lam hgapK
  have hLa : L *ᵥ (L⁻¹ *ᵥ kv) = kv := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hKinv),
      Matrix.one_mulVec]
  refine (tendsto_measure_exists_gt_of_eventually_good_events (fun n => ((Measure.pi fun _ : Fin n
      => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)))
    (Set.Ici (0 : ℝ))
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t' => |netFromParams φ n d xs (θ n p t') -
        netFromParams φ n d xs (θ n p 0) +
      (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp -
        NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
          (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp)|) hθ_flow
    (ε₀ := ε₀) (fun c hc => ?hev)).congr (fun n => ?heq)
  case heq => rfl
  case hev =>
    -- the global lazy-training event with a positive gap
    obtain ⟨freezeRate, jacRate, taylorRate, N, C, M, R, hfr, hjr, -, -, hC0, hM0, hR0, h⟩ :=
      exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lam hlam hgapK
        (δ := min 1 (c / 8)) (ε := c / 8) (lt_min one_pos (by positivity)) (min_le_left _ _)
        (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ) (κ := 0)
        (fun n _ => by simp)
    set δ : ℝ := min 1 (c / 8) with hδ
    have hδpos : 0 < δ := lt_min one_pos (by positivity)
    set ν : ℝ := lam / (4 * (m : ℝ)) with hν
    have hν0 : 0 < ν := by positivity
    have hνlam : ν ≤ lam / m := by
      rw [hν]
      exact div_le_div_of_nonneg_left hlam.le hm' (by linarith)
    -- constants of the error budget
    set kn : ℝ := ‖(WithLp.toLp 2 kv : EuclideanSpace ℝ (Fin m))‖ with hkn
    set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
    set Bmax : ℝ := (m : ℝ)⁻¹ * R * (G₀ + 1 + 2 * kn) with hBmax
    have hBmax0 : 0 ≤ Bmax := by positivity
    obtain ⟨S, hS0, hStail⟩ : ∃ S : ℝ, 0 ≤ S ∧ Bmax / ν * Real.exp (-ν * S) ≤ ε₀ / 4 := by
      have htend : Filter.Tendsto (fun S : ℝ => Bmax / ν * Real.exp (-ν * S)) Filter.atTop
          (nhds 0) := by
        have := (Real.tendsto_exp_atBot.comp
          (Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.const_mul_atTop hν0))).const_mul
            (Bmax / ν)
        simpa [Function.comp_def] using this
      obtain ⟨S, hS⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and
        (htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 4 by positivity)))).exists
      exact ⟨S, hS.1, hS.2.le⟩
    set A₁ : ℝ := S * ((m : ℝ)⁻¹ * (G₀ * R)) with hA₁
    set A₂ : ℝ := S * ((m : ℝ)⁻¹ * (kn * ((m : ℝ)⁻¹ * R * S))) with hA₂
    set a₁ : ℝ := S * ((m : ℝ)⁻¹ * R) + A₂ with ha₁
    have hA₁0 : 0 ≤ A₁ := by positivity
    have hA₂0 : 0 ≤ A₂ := by positivity
    have ha₁0 : 0 ≤ a₁ := by positivity
    set e : ℝ := min 1 (ε₀ / (4 * (a₁ + 1))) with he_def
    have he : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have hea : a₁ * e ≤ ε₀ / 4 := by
      have h1 : e ≤ ε₀ / (4 * (a₁ + 1)) := min_le_right _ _
      calc a₁ * e ≤ (a₁ + 1) * (ε₀ / (4 * (a₁ + 1))) :=
            mul_le_mul (by linarith) h1 he.le (by positivity)
        _ = ε₀ / 4 := by field_simp
    have hU := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X
      (fun α β => hL2mul (Xs α) (Xs β)) (fun α β => hdL2mul (Xs α) (Xs β)) he
    have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ
      hderiv_meas X' (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) he
    have hτ := tendsto_testLinearizationRate xs C₁ C₂ C hδpos
    have hb : Filter.Tendsto (fun n : ℕ =>
        (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 *
          C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
          Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n) Filter.atTop
        (nhds 0) := by
      simpa using (hτ.add (hjr.const_mul A₁)).add (hfr.const_mul A₂)
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0,
      hb.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 2 by positivity)),
      hjr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hU.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity))),
      hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
      with n hn hn0 hbn hjn hUn hUn'
    obtain ⟨E, hEm, hE, hEp⟩ := h n hn
    set U : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖} with hUdef
    set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
    have hUm : MeasurableSet U :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas Xs L e
    have hUm' : MeasurableSet U' :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' e
    have hUr : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real U ≤ c / 4 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hUn.le
    have hU'r : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real U' ≤ c / 4 := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
      simp only [hU'def, ← this]
      exact hUn'.le
    refine ⟨(E ∩ Uᶜ) ∩ U'ᶜ, (hEm.inter hUm.compl).inter hUm'.compl, ?_, ?_⟩
    · have hEc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ ≤ c / 4 + c / 4 := by
        rw [probReal_compl_eq_one_sub hEm]
        have := min_le_right 1 (c / 8)
        have h2 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
        linarith
      have := (measureReal_compl_inter_le ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
          gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) (E ∩ Uᶜ) U'ᶜ)
      have h2 := measureReal_compl_inter_le ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d
          => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) E Uᶜ
      rw [compl_compl] at this h2
      linarith
    · rintro p ⟨⟨hpE, hpU⟩, hpU'⟩ hflow t' ht'
      obtain ⟨-, -, hall, hp2⟩ := hEp p hpE
      obtain ⟨⟨horig, -⟩, hcert⟩ := hall (θ n p) hflow
      have hpU1 : ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖ < e :=
        not_le.1 hpU
      have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
          Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < e := not_le.1 hpU'
      set θ₀ := packParams p.1 p.2 with hθ₀
      set g : EuclideanSpace ℝ (Fin (n * d + n)) :=
        tangentFeature (netFromParams φ n d) xs θ₀ with hg
      simp only [hflow.init]
      have hdiff : ∀ u : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
          (fun θ' => netFromParams φ n d (Xs β) θ') (θ n p u) := fun u β =>
        (hasFDerivAt_netFromParams φ n d (Xs β) (θ n p u)
          fun i => hφ.differentiableAt).differentiableAt
      have hJ : ∀ s : ℝ, 0 ≤ s → ‖outputJacobian (netFromParams φ n d) Xs (θ n p s) -
          outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ jacRate n := fun s hs =>
        (hcert s hs).2.2.2.1
      have hK : ∀ s ∈ Set.Icc (0 : ℝ) S, ‖empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s) -
          L‖ ≤ freezeRate n + e := fun s hs => by
        have h1 := (horig s hs.1).2.1
        have h2 := norm_sub_le_norm_sub_add_norm_sub
          (empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s))
          (empiricalNTKMatrix (netFromParams φ n d) Xs θ₀) L
        linarith
      have hrow := norm_row_castSucc_le
        (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
          Fin (m + 1) → Fin d → ℝ) θ₀ - L') (Fin.last m)
      have hk : ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ g.ofLp) :
          EuclideanSpace ℝ (Fin m)) - WithLp.toLp 2 kv‖ ≤ e := by
        refine le_of_eq_of_le ?_ (hrow.1.trans hpU2.le)
        congr 1
        ext α
        simp only [PiLp.sub_apply, Matrix.sub_apply, hg, hkv, hL']
        rw [outputJacobian_mulVec_tangentFeature, (empiricalNTKMatrix_snoc_last _ _ _ _ α).1]
      have hgnorm : ‖g‖ ≤ G₀ := by
        rw [hG₀]
        refine Real.le_sqrt_of_sq_le ?_
        have h1 : ‖g‖ ^ 2 = empiricalNTKMatrix (netFromParams φ n d)
            (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) θ₀
            (Fin.last m) (Fin.last m) := by
          rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2, hg,
            real_inner_self_eq_norm_sq]
        have h2 := hrow.2
        rw [Matrix.sub_apply] at h2
        have h3 := (abs_le.1 (h2.trans hpU2.le)).2
        have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
        rw [h1]
        linarith
      have hres0 : ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤ R := by
        have := (hcert 0 le_rfl).2.2.1
        simpa [hflow.init, ν] using this
      have hglob := abs_inner_displacement_add_frozenPrediction_le_of_exp_decay
        (netFromParams φ n d) Xs y hm' hflow hdiff g hS0 L hK_inf hrr (L⁻¹ *ᵥ kv) kv hLa hν0
        hνlam hJ hK hk (fun s hs => by simpa [hν] using (horig s hs).2.2.1) t' ht'
      have hg' : gradParams φ n d xs θ₀ = g := (tangentFeature_netFromParams_of_differentiable φ
        hφ n d xs θ₀).symm
      have hreadout : ∀ i : Fin n, |θ₀ (paramIndexEquiv n d (Sum.inr i))| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) :=
        fun i => by simpa only [hθ₀, packParams_readout] using hp2 i
      have hdisp := (hcert t' ht').1
      have htay := abs_netFromParams_sub_linearization_le_of_disp hact hn0 xs hreadout hdisp
      rw [hg'] at htay
      have hjr0 : 0 ≤ jacRate n := (norm_nonneg _).trans (hJ 0 le_rfl)
      have hfr0 : 0 ≤ freezeRate n := (norm_nonneg _).trans (horig 0 le_rfl).2.1
      have hr00 := norm_nonneg (trainingResidual (netFromParams φ n d) Xs y θ₀)
      have hkn0 : 0 ≤ kn := norm_nonneg _
      have hg0 := norm_nonneg g
      have hbudget : S * ((m : ℝ)⁻¹ * (‖g‖ * jacRate n *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + e *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + kn *
            ((m : ℝ)⁻¹ * ((freezeRate n + e) *
              ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖) * S))) ≤
          A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
        have hgR : ‖g‖ * jacRate n * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤
            G₀ * jacRate n * R := by gcongr
        calc _ ≤ S * ((m : ℝ)⁻¹ * (G₀ * jacRate n * R + e * R +
              kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) * R) * S))) := by
              gcongr
          _ = A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
              rw [hA₁, hA₂, ha₁]; ring
      have htail : ((m : ℝ)⁻¹ * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ *
          (‖g‖ * jacRate n + e + 2 * kn)) / ν * Real.exp (-ν * S) ≤ ε₀ / 4 := by
        refine le_trans ?_ hStail
        have hexp : 0 ≤ Real.exp (-ν * S) := (Real.exp_pos _).le
        have : (m : ℝ)⁻¹ * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ *
            (‖g‖ * jacRate n + e + 2 * kn) ≤ Bmax := by
          rw [hBmax]
          have h1 : ‖g‖ * jacRate n ≤ G₀ * 1 := by gcongr
          have hmi : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.2 hm'.le
          calc (m : ℝ)⁻¹ * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ *
                (‖g‖ * jacRate n + e + 2 * kn)
              ≤ (m : ℝ)⁻¹ * R * (G₀ * 1 + 1 + 2 * kn) := by gcongr
            _ = _ := by ring
        gcongr
      have hD : |netFromParams φ n d xs (θ n p t') - netFromParams φ n d xs θ₀ +
          (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
            NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
              (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)| ≤
          (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 +
            ((A₁ * jacRate n + A₂ * freezeRate n + a₁ * e) + ε₀ / 4) := by
        have hsplit : netFromParams φ n d xs (θ n p t') - netFromParams φ n d xs θ₀ +
            (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
              NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
                (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp) =
            (netFromParams φ n d xs (θ n p t') - netFromParams φ n d xs θ₀ - ⟪g, θ n p t' - θ₀⟫) +
              (⟪g, θ n p t' - θ₀⟫ + (L⁻¹ *ᵥ kv) ⬝ᵥ
                ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
                  NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
                    (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)) := by ring
        rw [hsplit]
        exact (abs_add_le _ _).trans (add_le_add htay
          (hglob.trans (add_le_add hbudget htail)))
      have hbn' : (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n < ε₀ / 2 := hbn
      linarith

/-- **Kernel interpolation at a test point (ridgeless kernel regression).** Under the hypotheses of
`tendsto_measure_test_prediction_global_positive_gap`, the trained network converges, first as the
width grows and then as time grows, to the ridgeless kernel-regression interpolant: for every
`ε₀, c > 0` there is a time `T₀` such that for all large `n`, with probability at least `1 - c`,
`|f_t(x) - (f₀(x) + k_∞(x, X)ᵀ K_∞⁻¹ (y - f₀(X)))| ≤ ε₀` simultaneously for all `t ≥ T₀`. Here
`a ⬝ᵥ r₀ = -k_∞ᵀ K_∞⁻¹ (y - f₀(X))` with `a = K_∞⁻¹ k_∞` and `r₀ = f₀(X) - y`. (This is
zero-ridge regression, i.e. minimum-norm interpolation, not positive-ridge kernel ridge regression;
for the frozen empirical features it is the minimum-norm solution of `affine_minNorm_pythagoras`.)
The time `T₀` depends on `ε₀`, `c` and the tightness radius of the initial residual, not on `n`. -/
theorem test_prediction_kernel_interpolation_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hKpd : (limitingFullNTKMatrix φ X).PosDef) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ c : ℝ} (hε₀ : 0 < ε₀) (hc : 0 < c) :
    ∃ T₀ : ℝ, ∀ᶠ n in Filter.atTop, ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
            gaussianReal 0 1)) {p | ∃ t ∈ Set.Ici T₀, ε₀ <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          ((limitingFullNTKMatrix φ X)⁻¹ *ᵥ (fun α : Fin m =>
            limitingFullNTKMatrix φ (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
              Fin d → ℝ) (Fin.last m) (Fin.castSucc α))) ⬝ᵥ
            (trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp|} ≤
      ENNReal.ofReal c := by
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  set L : Matrix (Fin m) (Fin m) ℝ := limitingFullNTKMatrix φ X with hL
  set kv : Fin m → ℝ := fun α => limitingFullNTKMatrix φ
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) (Fin.last m)
      (Fin.castSucc α) with hkv
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hL2, -, -, -⟩ := activation_memLp_two hact (d := d)
  obtain ⟨lam, hlam, hgapK⟩ := exists_pos_sub_smul_one_posSemidef_of_posDef hKpd
  have hrr := rayleigh_lower_bound_of_sub_smul_posSemidef L lam hgapK
  -- tightness of the initial residual
  obtain ⟨R₁, hR₁0, hR₁⟩ := exists_initial_residual_radius φ X y hmeasφ (fun α => hL2 (Xs α))
    (ε := ENNReal.ofReal (c / 2)) (ENNReal.ofReal_pos.2 (by positivity))
  set an : ℝ := ‖(WithLp.toLp 2 (L⁻¹ *ᵥ kv) : EuclideanSpace ℝ (Fin m))‖ with han
  have han0 : 0 ≤ an := norm_nonneg _
  -- a time after which the frozen residual is negligible
  obtain ⟨T₀, hT₀0, hT₀⟩ : ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      an * R₁ * Real.exp (-(lam / (m : ℝ)) * T₀) ≤ ε₀ / 2 := by
    have htend : Filter.Tendsto (fun T : ℝ => an * R₁ * Real.exp (-(lam / (m : ℝ)) * T))
        Filter.atTop (nhds 0) := by
      have := (Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
        (Filter.tendsto_id.const_mul_atTop (show 0 < lam / (m : ℝ) by positivity)))).const_mul
          (an * R₁)
      simpa [Function.comp_def] using this
    obtain ⟨T, hT⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and
      (htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 2 by positivity)))).exists
    exact ⟨T, hT.1, hT.2.le⟩
  refine ⟨T₀, ?_⟩
  have hglob := tendsto_measure_test_prediction_global_positive_gap hm hd φ hact X y hKpd x θ
    hθ_flow (ε₀ := ε₀ / 2) (by positivity)
  filter_upwards [hglob.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2
    (show 0 < c / 2 by positivity)))] with n hn
  have hnull : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)) {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y)
      (packParams p.1 p.2) (θ n p)} = 0 := ae_iff.1 (hθ_flow n)
  calc _ ≤ ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)) (({p | ∃ t ∈ Set.Ici (0 : ℝ), ε₀ / 2 <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          (L⁻¹ *ᵥ kv) ⬝ᵥ
            ((trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
                (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp)|} ∪
        {p | R₁ < ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖}) ∪
        {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
          (θ n p)}) := by
        refine measure_mono fun p hp => ?_
        obtain ⟨t, ht, hgt⟩ := hp
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt,
          not_not] at hcon
        obtain ⟨⟨h1, h2⟩, hflow⟩ := hcon
        have h1t := h1 t (Set.mem_Ici.2 (hT₀0.trans ht))
        have hinit : θ n p 0 = packParams p.1 p.2 := hflow.init
        have hρ := matrix_exp_residual_decay L
          (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)) lam hrr hm' t (hT₀0.trans ht)
        rw [hinit] at h1t hρ hgt
        set r₀ := trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2) with hr₀
        set ρv : Fin m → ℝ := NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ r₀.ofLp with hρv
        have hdot : |(L⁻¹ *ᵥ kv) ⬝ᵥ ρv| ≤ ε₀ / 2 := by
          refine (abs_dotProduct_le_norm_mul_norm _ _).trans ?_
          have hρ' : ‖(WithLp.toLp 2 ρv : EuclideanSpace ℝ (Fin m))‖ ≤ R₁ *
              Real.exp (-(lam / (m : ℝ)) * T₀) := by
            refine hρ.trans ?_
            have hexp : Real.exp (-(lam / (m : ℝ)) * t) ≤ Real.exp (-(lam / (m : ℝ)) * T₀) :=
              Real.exp_le_exp.2 (by nlinarith [show 0 < lam / (m : ℝ) by positivity, ht.out])
            exact mul_le_mul h2 hexp (Real.exp_pos _).le hR₁0
          calc _ ≤ an * (R₁ * Real.exp (-(lam / (m : ℝ)) * T₀)) :=
                mul_le_mul_of_nonneg_left hρ' han0
            _ = an * R₁ * Real.exp (-(lam / (m : ℝ)) * T₀) := by ring
            _ ≤ ε₀ / 2 := hT₀
        have hsplit : netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
            netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (packParams p.1 p.2) +
            (L⁻¹ *ᵥ kv) ⬝ᵥ r₀.ofLp =
            (netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
              netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (packParams p.1 p.2) +
              (L⁻¹ *ᵥ kv) ⬝ᵥ (r₀.ofLp - ρv)) + (L⁻¹ *ᵥ kv) ⬝ᵥ ρv := by
          rw [dotProduct_sub]; ring
        rw [hsplit] at hgt
        have := (abs_add_le _ _).trans (add_le_add h1t hdot)
        linarith
    _ ≤ ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) + 0 := by
        rw [← hnull]
        refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add hn.le (hR₁ n))) le_rfl)
    _ = ENNReal.ofReal c := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The residual `θ ↦ r(θ)` of a differentiable-activation two-layer network is continuous in the
packed parameters. -/
private lemma continuous_trainingResidual_netFromParams {m : ℕ} (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (n d : ℕ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      trainingResidual (netFromParams φ n d) X y θ) := by
  have hnet : ∀ x : Fin d → ℝ, Continuous (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      netFromParams φ n d x θ) := fun x =>
    continuous_iff_continuousAt.2 fun θ =>
      (hasFDerivAt_netFromParams φ n d x θ fun i => hφ.differentiableAt).continuousAt
  exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => hnet (X α))).sub
    continuous_const

/-- **Fixed-time residual limit (no spectral gap).** Let `θ n p` be trajectories that are
measurable in the initialization and solve the gradient-flow ODE almost everywhere. Then for every
fixed `t ≥ 0` the trained residual on the paper's scaled dataset converges in distribution to the
frozen-kernel prediction `exp(-(t / m) K_∞) (G - y)` with `G ~ 𝒩(0, Φ^{(∞)})`. This is the residual
half of the finite-horizon target: the initial residual weak limit is pushed through the matrix
exponential and compared with the actual residual by
`tendsto_measure_residual_sub_matrix_exp_finite_horizon`. -/
theorem tendstoInDistribution_trainingResidual_matrix_exp
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) ((Measure.pi fun _ : Fin n => Measure.pi fun _
        : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        trainingResidual (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t))
      Filter.atTop
      (fun G : EuclideanSpace ℝ (Fin m) =>
        (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
          (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  have hcont : Continuous (fun v : EuclideanSpace ℝ (Fin m) =>
      (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
        v.ofLp) : EuclideanSpace ℝ (Fin m))) :=
    (Matrix.toEuclideanLin (NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X))
      ).continuous_of_finiteDimensional
  have hX := tendstoInDistribution_initial_trainingResidual φ X y hmeasφ fun α =>
    (activation_memLp_two hact (d := d)).1 _
  exact tendstoInDistribution_of_tendsto_measure_norm_sub _ _ _
    (hX.continuous_comp (g := fun v : EuclideanSpace ℝ (Fin m) =>
      (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
        v.ofLp) : EuclideanSpace ℝ (Fin m))) hcont)
    (fun ε₀ hε₀ => tendsto_measure_residual_sub_matrix_exp_finite_horizon hm hd φ hact X y t ht θ
      hθ_flow hε₀)
    fun n => (continuous_trainingResidual_netFromParams φ hφ n d _ y).measurable.comp_aemeasurable
      (hθ_meas n t)

/-- **Fixed-time prediction limit (no spectral gap).** The network predictions on the scaled
dataset converge in distribution to `y + exp(-(t / m) K_∞) (G - y)`; see
`tendstoInDistribution_trainingResidual_matrix_exp`. -/
theorem tendstoInDistribution_trainingOutputs_matrix_exp
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) ((Measure.pi fun _ : Fin n => Measure.pi fun _
        : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        WithLp.toLp 2 (fun α => netFromParams φ n d
          (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)))
      Filter.atTop
      (fun G : EuclideanSpace ℝ (Fin m) =>
        y + (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
          (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  have h := (tendstoInDistribution_trainingResidual_matrix_exp hm hd φ hact X y t ht θ hθ_meas
    hθ_flow).continuous_comp (g := fun v : EuclideanSpace ℝ (Fin m) => y + v) (by fun_prop)
  convert h using 3 with n p <;> first | rfl | simp [trainingResidual]

end

end NTK
