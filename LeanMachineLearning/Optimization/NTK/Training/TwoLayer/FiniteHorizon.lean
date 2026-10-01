/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.InitializationEvents

/-!
# Training limits of the two-layer network: finite horizon and Jacobian freezing

The finite-horizon lazy-training specification on `[0, T]` (no spectral gap), and the proved
consequences: kernel, Jacobian and linearization-error drift in probability on a finite horizon and
under a positive gap (Phase 12), including the test-input linearization error.

## Main results and proof outline

- `exists_measurableSet_finite_horizon_lazy_training_event`,
  `tendsto_measure_exists_gt_of_good_events`, `tendsto_measure_jacobian_drift_finite_horizon`,
  `tendsto_measure_jacobian_drift_global_positive_gap`,
  `tendsto_measure_linearization_error_finite_horizon`,
  `tendsto_measure_linearization_error_global_positive_gap`,
  `tendsto_measure_test_linearization_error_finite_horizon`,
  `tendsto_measure_test_linearization_error_global_positive_gap` : **Phase 12** - Jacobian
  (tangent-feature) freezing, proved directly from the Jacobian Lipschitz bound and not from Gram
  freezing, and convergence in probability of the nonlinear network to its initialization
  linearization (training outputs and any test input), on `[0, T]` without a gap and on `[0, ∞)`
  under a positive limiting gap; all four share one generic outer-measure lemma.

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

/-!
#### Target Theorem 1: Finite-Horizon NTK Training Limit (Phase 0 Target)

**Status.** Proved, with bundled activation hypotheses `SmoothActivation` in place of
`hderiv_lip` alone: conclusion 1 is `tendsto_measure_kernel_drift_finite_horizon`, conclusion 2 is
`tendstoInDistribution_trainingResidual_matrix_exp`, and conclusion 3 is
`tendstoInDistribution_trainingOutputs_matrix_exp`. The commented signature below is kept as the
original target.

**Formal Probability Data**:
For each width `n : ℕ`:
- Parameter probability space: `Ω n := (Fin n → Fin d → ℝ) × (Fin n → ℝ)` with measure
  `μ n := initMeasure n d`.
- Parameter packing: `θ₀ n (p : Ω n) := packParams p.1 p.2`.
- Random trajectory family:
  `θ : ∀ n : ℕ, Ω n → ℝ → EuclideanSpace ℝ (Fin (n * d + n))`
  satisfying:
  - Initial condition and gradient flow ODE: for each `n`, for `initMeasure n d`-almost every `p`,
    `ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)`.
    Here `mseLoss` already contains the `1 / m` normalization, so `ForwardGFTrajectory`
    corresponds to `θ' = -∇ mseLoss`, yielding the intended residual dynamics
    `r'(t) = -(1 / m) K(t) r(t)`.
  - Trajectory measurability: `∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d)`.
    Path continuity in `t` and measurability in `p` reduce the uniform supremum event
    `{p | ∃ t ∈ Set.Icc 0 T, ‖K n t p - K n 0 p‖ > ε}` to a countable dense subset of `[0, T]`,
    ensuring measurability of the supremum event.
- Observable random variables:
  - Residual:
    `r n t p := trainingResidual (netFromParams φ n d)`
      `(fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)`.
  - Predictions:
    `trainingOutputs (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)`.
  - Empirical NTK:
    `K n t p := empiricalNTKMatrix (netFromParams φ n d)`
      `(fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)`.

**Conclusions** (on any compact time horizon `[0, T]` with `T ≥ 0`):
1. **Kernel Stationarity**: The empirical NTK remains asymptotically stationary on `[0, T]`:
   `∀ ε > 0, Filter.Tendsto (fun n => (μ n) {p | ∃ t ∈ Set.Icc 0 T,`
     `‖K n t p - K n 0 p‖ > ε}) Filter.atTop (nhds 0)`.
2. **Fixed-Time Residual Weak Convergence**: For each fixed `t ∈ [0, T]`, the residual vector
   converges in distribution to the linearized infinite-width trajectory:
   `MeasureTheory.TendstoInDistribution (fun n p => r n t p) Filter.atTop`
     `(fun G => WithLp.toLp 2`
     `  ((NormedSpace.exp (- (t / m : ℝ) • limitingFullNTKMatrix φ X)) *ᵥ (G - y).ofLp))`
     `(fun n => initMeasure n d) (multivariateGaussian 0 (limitingCovariance φ scaledX))`.
3. **Fixed-Time Prediction Convergence**: The network predictions converge in distribution:
   `MeasureTheory.TendstoInDistribution (fun n p => trainingOutputs ... (θ n p t)) Filter.atTop`
     `(fun G => y + WithLp.toLp 2`
     `  ((NormedSpace.exp (- (t / m : ℝ) • limitingFullNTKMatrix φ X)) *ᵥ (G - y).ofLp))`
     `(fun n => initMeasure n d) (multivariateGaussian 0 (limitingCovariance φ scaledX))`.

**Mechanism**:
This theorem does not require a positive spectral gap. PSD controls the residual norm, while
finite-horizon displacement and the width-decaying Jacobian Lipschitz estimate imply kernel
stationarity.

**Commented Formal Lean Signature**:
```lean
/-
theorem finite_horizon_ntk_training_limit
    {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hderiv_lip : ∃ L_φ' : ℝ, 0 ≤ L_φ' ∧ LipschitzWith (Real.toNNReal L_φ') (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    (∀ ε > 0, Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc 0 T,
        ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖ > ε})
      Filter.atTop (nhds 0)) ∧
    (∀ t ∈ Set.Icc 0 T,
      MeasureTheory.TendstoInDistribution
        (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
          trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t))
        Filter.atTop
        (fun (G : EuclideanSpace ℝ (Fin m)) =>
          (WithLp.toLp 2 ((NormedSpace.exp (- (t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
        (fun n => initMeasure n d)
        (multivariateGaussian 0
          (limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))) ∧
    (∀ t ∈ Set.Icc 0 T,
      MeasureTheory.TendstoInDistribution
        (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t))
        Filter.atTop
        (fun (G : EuclideanSpace ℝ (Fin m)) =>
          y + (WithLp.toLp 2 ((NormedSpace.exp (- (t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
        (fun n => initMeasure n d)
        (multivariateGaussian 0
          (limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k))))
-/
```
-/


/-! #### Proved consequences of the finite-horizon freeze event

The measurable good event of `exists_measurableSet_finite_horizon_kernel_freeze` yields, for a
family of trajectories that solve the gradient-flow ODE almost everywhere in the initialization,
kernel stationarity in probability on `[0, T]` and, below, convergence of the residual to the
frozen matrix-exponential residual. -/

/-- Any positive `κ : ℝ≥0∞` dominates `ENNReal.ofReal c` for some real `c > 0`. -/
lemma exists_pos_real_ofReal_le {κ : ENNReal} (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c ≤ κ := by
  by_cases h : κ = ⊤
  · exact ⟨1, one_pos, by simp [h]⟩
  · exact ⟨κ.toReal, ENNReal.toReal_pos hκ.ne' h, (ENNReal.ofReal_toReal h).le⟩

/-- `μ S ≤ ofReal c` from the corresponding bound on `μ.real S`, for a finite measure. -/
lemma measure_le_ofReal_of_measureReal_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {S : Set α} {c : ℝ} (h : μ.real S ≤ c) :
    μ S ≤ ENNReal.ofReal c :=
  (ENNReal.ofReal_toReal (measure_ne_top μ S)).symm.le.trans (ENNReal.ofReal_le_ofReal h)

/-- **Generic "supremum of a drift tends to zero in probability", budget depending on the
tolerance.** Let `μ n` be probability measures and `Good n p` a property holding almost surely (in
applications, "the trajectory `θ n p` solves the gradient-flow ODE"). Fix `ε₀ > 0`. Suppose that for
every confidence level `c > 0` and all large `n` there is a measurable event `E` of failure
probability at most `c` on which `D n p t ≤ ε₀` for all `t ∈ S` (whenever `Good n p`). Then the
probability that `D n p t` exceeds `ε₀` at some `t ∈ S` tends to zero. The bad set need not be
measurable, so `μ n` evaluates it as an outer measure. -/
theorem tendsto_measure_exists_gt_of_eventually_good_events {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (S : Set ℝ) (Good : ∀ n, Ω n → Prop) (D : ∀ n, Ω n → ℝ → ℝ)
    (hgood : ∀ n, ∀ᵐ p ∂(μ n), Good n p) {ε₀ : ℝ}
    (hev : ∀ c : ℝ, 0 < c → ∀ᶠ n in Filter.atTop, ∃ E : Set (Ω n), MeasurableSet E ∧
      (μ n).real Eᶜ ≤ c ∧ ∀ p ∈ E, Good n p → ∀ t ∈ S, D n p t ≤ ε₀) :
    Filter.Tendsto (fun n => μ n {p | ∃ t ∈ S, ε₀ < D n p t}) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨c, hc, hcκ⟩ := exists_pos_real_ofReal_le hκ
  filter_upwards [hev c hc] with n hEn
  obtain ⟨E, hEm, hEc, hEp⟩ := hEn
  have hnull : μ n {p | ¬ Good n p} = 0 := ae_iff.1 (hgood n)
  calc μ n {p | ∃ t ∈ S, ε₀ < D n p t} ≤ μ n (Eᶜ ∪ {p | ¬ Good n p}) := by
        refine measure_mono fun p hp => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hcon
        obtain ⟨hpE, hg⟩ := hcon
        obtain ⟨t, ht, hgt⟩ := hp
        have := hEp p hpE hg t ht
        linarith
    _ ≤ μ n Eᶜ + 0 := by rw [← hnull]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal c := by rw [add_zero]; exact measure_le_ofReal_of_measureReal_le _ hEc
    _ ≤ κ := hcκ

/-- **Generic "supremum of a drift tends to zero in probability".** The special case of
`tendsto_measure_exists_gt_of_eventually_good_events` in which, for each confidence level `c`, the
good event forces `D n p t ≤ ρ n` for a fixed sequence `ρ → 0`. This is the shared endgame of the
kernel-, Jacobian- and linearization-drift theorems below. -/
theorem tendsto_measure_exists_gt_of_good_events {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)] (S : Set ℝ)
    (Good : ∀ n, Ω n → Prop) (D : ∀ n, Ω n → ℝ → ℝ)
    (hgood : ∀ n, ∀ᵐ p ∂(μ n), Good n p)
    (hev : ∀ c : ℝ, 0 < c → ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop, ∃ E : Set (Ω n), MeasurableSet E ∧ (μ n).real Eᶜ ≤ c ∧
        ∀ p ∈ E, Good n p → ∀ t ∈ S, D n p t ≤ ρ n)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto (fun n => μ n {p | ∃ t ∈ S, ε₀ < D n p t}) Filter.atTop (nhds 0) :=
  tendsto_measure_exists_gt_of_eventually_good_events μ S Good D hgood fun c hc => by
    obtain ⟨ρ, hρ, hn⟩ := hev c hc
    filter_upwards [hn, hρ.eventually (gt_mem_nhds hε₀)] with n hEn hlt
    obtain ⟨E, hEm, hEc, hEp⟩ := hEn
    exact ⟨E, hEm, hEc, fun p hp hg t ht => (hEp p hp hg t ht).trans hlt.le⟩

/-- **Kernel stationarity in probability on `[0, T]`.** If the trajectories `θ n p` solve the
gradient-flow ODE for `initMeasure n d`-almost every initialization, then for every `ε₀ > 0` the
probability that the empirical NTK drifts by more than `ε₀` somewhere on `[0, T]` tends to zero.
The event is not shown measurable, so `initMeasure n d` evaluates it as an *outer* probability; the
proof bounds it by the complement of the measurable good event of
`exists_measurableSet_finite_horizon_kernel_freeze`. No spectral gap is assumed. -/
theorem tendsto_measure_kernel_drift_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, freezeRate, N, -, hrate, h⟩ := exists_measurableSet_finite_horizon_kernel_freeze hm φ
    hact X y T hT (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity))
    (min_le_left _ _) (by positivity)
  refine ⟨freezeRate, hrate, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := (hEp p hp).2 (θ n p) hflow t ht
    rwa [hflow.init]

/-- **Jacobian stationarity in probability on `[0, T]`.** Under the hypotheses of
`tendsto_measure_kernel_drift_finite_horizon`, for every `ε₀ > 0` the probability that the output
Jacobian `J(θ(t))` moves by more than `ε₀` (in Frobenius norm) from `J(θ(0))` somewhere on `[0, T]`
tends to zero. This is the tangent-feature freezing statement proper: it is not deduced from
`tendsto_measure_kernel_drift_finite_horizon`, since `K = J Jᵀ` can stay put while `J` rotates. It
comes from the same displacement bound and the Jacobian Lipschitz estimate
(`exists_measurableSet_finite_horizon_lazy_training_event`). -/
theorem tendsto_measure_jacobian_drift_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, _, _, _, jacRate, _, N, -, -, hjac, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  refine ⟨jacRate, hjac, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := ((hEp p hp).2.2.2 (θ n p) hflow t ht).2.1
    rwa [hflow.init]

/-- **The trained network stays close to its initialization linearization on `[0, T]`.** Under the
hypotheses of `tendsto_measure_kernel_drift_finite_horizon`, for every `ε₀ > 0` the probability that
`‖f(θ(t)) - f(θ(0)) - J(θ(0)) (θ(t) - θ(0))‖ > ε₀` somewhere on `[0, T]` tends to zero, where `f`
is the vector of training outputs and `J` the output Jacobian. The remainder is bounded
deterministically by `norm_trainingOutputs_sub_linearization_le` (Lipschitz Jacobian on the
displacement ball). Test inputs are handled by
`tendsto_measure_test_linearization_error_finite_horizon`. -/
theorem tendsto_measure_linearization_error_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
              (θ n p t - θ n p 0).ofLp)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
          (θ n p t - θ n p 0).ofLp)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, _, _, _, _, taylorRate, N, -, -, -, htay, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  refine ⟨taylorRate, htay, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := ((hEp p hp).2.2.2 (θ n p) hflow t ht).2.2.1
    rwa [hflow.init]

/-- **Jacobian stationarity in probability on `[0, ∞)` from a positive limiting gap.** If the
limiting kernel satisfies `K_∞ ≥ lambda_inf • 1` with `lambda_inf > 0` and the trajectories `θ n p`
solve the gradient-flow ODE for almost every initialization, then for every `ε₀ > 0` the probability
that the output Jacobian moves by more than `ε₀` from `J(θ(0))` at *some* time `t ≥ 0` tends to
zero, i.e. `P(sup_{t ≥ 0} ‖J(θ(t)) - J(θ(0))‖ > ε₀) → 0`. The displacement bound is uniform in time
because the positive gap makes the residual decay exponentially; the finite-horizon counterpart
needs no gap (`tendsto_measure_jacobian_drift_finite_horizon`). Jacobian freezing is proved directly
from the Jacobian Lipschitz bound, not inferred from kernel freezing. -/
theorem tendsto_measure_jacobian_drift_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Ici 0)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, jacRate, _, N, C, M, R, -, hjac, htay, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  refine ⟨jacRate, hjac, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := (((hEp p hp).2.2.1 (θ n p) hflow).2 t ht).2.2.2.1
    rwa [hflow.init]

/-- **Linearization error in probability on `[0, ∞)` from a positive limiting gap.** Under the
hypotheses of `tendsto_measure_jacobian_drift_global_positive_gap`, for every `ε₀ > 0` the
probability that `‖f(θ(t)) - f(θ(0)) - J(θ(0)) (θ(t) - θ(0))‖ > ε₀` at some `t ≥ 0` tends to zero:
the full nonlinear network stays within `o(1)` of its initialization linearization for all time at
the training inputs. Test inputs are handled by
`tendsto_measure_test_linearization_error_global_positive_gap`. -/
theorem tendsto_measure_linearization_error_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < ‖trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
              (θ n p t - θ n p 0).ofLp)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Ici 0)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
          (θ n p t - θ n p 0).ofLp)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, _, taylorRate, N, C, M, R, -, hjac, htay, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  refine ⟨taylorRate, htay, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := (((hEp p hp).2.2.1 (θ n p) hflow).2 t ht).2.2.2.2
    rwa [hflow.init]

/-- Deterministic test-point linearization bound: at any input `x`, if the readout weights of `θ₀`
are bounded by `R` and `‖θ - θ₀‖ ≤ C`, the network differs from its linearization at `θ₀` by at most
`(K_x(R) / (2 √n)) C²`. Instantiates `abs_netFromParams_sub_linearization_le` for a
`SmoothActivation`. -/
lemma abs_netFromParams_sub_linearization_le_of_disp {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) {n d : ℕ} (hn : 0 < n) (x : Fin d → ℝ)
    {θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n))} {R C : ℝ}
    (hR : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) (hΔ : ‖θ - θ₀‖ ≤ C) :
    |netFromParams φ n d x θ - netFromParams φ n d x θ₀ - ⟪gradParams φ n d x θ₀, θ - θ₀⟫| ≤
      (Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, x j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) / Real.sqrt (n : ℝ)) / 2 * C ^ 2 := by
  obtain ⟨hC₁, hC₂, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  refine (abs_netFromParams_sub_linearization_le φ hact.differentiable n d hn x θ₀ θ C₁ C₂ R hC₁
    hC₂ ((abs_nonneg _).trans (hR ⟨0, hn⟩)) hφ_lip hact.deriv_bdd hact.deriv_lip hR).trans ?_
  gcongr

open Filter Topology in
/-- The test-point remainder rate `(K_x(R₀(n)) / (2 √n)) C²` with `R₀(n) = √(2 log (2 n / δ))`
(the high-probability bound on the readout weights) tends to `0`. -/
lemma tendsto_testLinearizationRate {d : ℕ} (x : Fin d → ℝ) (C₁ C₂ C : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, x j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) /
        Real.sqrt (n : ℝ)) / 2 * C ^ 2) atTop (𝓝 0) := by
  have h := ((tendsto_jacobianLipschitzScale (fun _ : Fin 1 => x) C₁ C₂ hδ 0).div_const 2).mul_const
    (C ^ 2)
  simpa using h

/-- **Linearization error at a test input, in probability on `[0, T]`.** For any test input `x`
(scaled like the training inputs by `1 / √d`), the probability that the network output at `x`
differs from its initialization linearization `f(x; θ(0)) + ⟪∇f(x; θ(0)), θ(t) - θ(0)⟫` by more than
`ε₀` somewhere on `[0, T]` tends to zero. The flow is still trained on the training set; only the
readout weights at initialization and the displacement radius enter the deterministic bound
`abs_netFromParams_sub_linearization_le`. -/
theorem tendsto_measure_test_linearization_error_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (x : Fin d → ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
            netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
          ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0), θ n p t - θ n p 0⟫|})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc (0 : ℝ) T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
        netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
      ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0),
        θ n p t - θ n p 0⟫|) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, C, _, _, _, _, N, -, -, -, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  refine ⟨_, tendsto_testLinearizationRate (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) C₁ C₂ C
    (lt_min one_pos (by positivity : 0 < c / 8)),
    (Filter.eventually_ge_atTop (max N 1)).mono fun n hn' => ?_⟩
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · obtain ⟨-, hp2, -, hall⟩ := hEp p hp
    have hdisp := (hall (θ n p) hflow t ht).2.2.2
    rw [hflow.init]
    exact abs_netFromParams_sub_linearization_le_of_disp hact hn0
      (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j)
      (fun i => by simpa [unpackA_packParams] using hp2 i) hdisp

/-- **Linearization error at a test input, in probability on `[0, ∞)` from a positive gap.**
The test-point counterpart of `tendsto_measure_linearization_error_global_positive_gap`: for every
test input `x` and `ε₀ > 0`,
`P(sup_{t ≥ 0} |f(x; θ(t)) - f(x; θ(0)) - ⟪∇f(x; θ(0)), θ(t) - θ(0)⟫| > ε₀) → 0`. -/
theorem tendsto_measure_test_linearization_error_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (x : Fin d → ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
            netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
          ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0), θ n p t - θ n p 0⟫|})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Ici (0 : ℝ))
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
        netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
      ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0),
        θ n p t - θ n p 0⟫|) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, _, _, N, C, M, R, -, -, -, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  refine ⟨_, tendsto_testLinearizationRate (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) C₁ C₂ C
    (lt_min one_pos (by positivity : 0 < c / 8)),
    (Filter.eventually_ge_atTop (max N 1)).mono fun n hn' => ?_⟩
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · obtain ⟨-, -, hall, hp2⟩ := hEp p hp
    have hdisp := ((hall (θ n p) hflow).2 t ht).1
    rw [hflow.init]
    exact abs_netFromParams_sub_linearization_le_of_disp hact hn0
      (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j)
      (fun i => by simpa [unpackA_packParams] using hp2 i) hdisp

end

end NTK
