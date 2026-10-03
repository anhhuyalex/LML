/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.FiniteHorizon

/-!
# Training limits of the two-layer network: the train-test cross-kernel

train-test cross-kernel: the cross-kernel `J(θ) ∇f(x; θ)` between the training set and a test input
concentrates
at initialization and freezes along gradient flow.

## Main results and proof outline

- `tendsto_initMeasure_crossKernel_ge_eps`, `tendsto_measure_crossKernel_drift_finite_horizon`,
  `tendsto_measure_crossKernel_drift_global_positive_gap`,
  `tendsto_measure_test_prediction_finite_horizon`,
  `tendsto_measure_test_prediction_global_positive_gap`,
  `test_prediction_kernel_interpolation_limit` : The train-test cross-kernel
  `J(θ) ∇f(x; θ)` (a row of the extended-dataset NTK Gram matrix) concentrates at initialization and
  freezes; the trained output at a test input `x` follows the closed-form predictor
  `f₀(x) - a ⬝ᵥ (r₀ - exp(-(t/m) K_∞) r₀)`, `a = K_∞⁻¹ k_∞(x, X)`, at fixed times (no gap) and
  uniformly in time (positive gap), and converges to the ridgeless kernel-regression interpolant
  as `n → ∞` and then `t → ∞`. The deterministic core is
  `abs_inner_displacement_add_frozenPrediction_le(_of_exp_decay)` in `Training.GradientFlow`.

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

/-- Scaling the extended dataset `(X, x)` by `1 / √d` scales both parts. -/
lemma scaled_snoc {m d : ℕ} (X : Fin m → Fin d → ℝ) (x : Fin d → ℝ) :
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
      Fin d → ℝ) α j) =
    Fin.snoc (α := fun _ => Fin d → ℝ) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) := by
  funext α
  refine Fin.lastCases ?_ (fun i => ?_) α <;> simp

/-- Deterministic cross-kernel drift bound. Let `k_θ(x) = J(θ) ∇f(x; θ)` be the train-test
cross-kernel vector (`k_θ(x)_α = ⟪∇f(x; θ), ∇f(X α; θ)⟫`). If the readout weights of `θ₀` are
bounded by `R`, `‖θ - θ₀‖ ≤ Cd`, `‖J(θ₀)‖ ≤ M`, `‖J(θ) - J(θ₀)‖ ≤ jr` and `‖∇f(x; θ₀)‖ ≤ G₀`, then
`‖k_θ(x) - k_{θ₀}(x)‖ ≤ jr G₀ + (M + jr) (K_x / √n) Cd`, where `K_x` is the tangent-feature
Lipschitz scale of `norm_gradParams_sub_le`. -/
private lemma norm_crossKernel_sub_le {φ : ℝ → ℝ} {C₁ C₂ : ℝ} (hact : SmoothActivation φ C₁ C₂)
    {n d m : ℕ} (hn : 0 < n) (Xs : Fin m → Fin d → ℝ) (xs : Fin d → ℝ)
    {θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n))} {R Cd M jr G₀ : ℝ}
    (hR : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) (hΔ : ‖θ - θ₀‖ ≤ Cd)
    (hJ₀ : ‖outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ M)
    (hJ : ‖outputJacobian (netFromParams φ n d) Xs θ -
      outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ jr)
    (hg₀ : ‖gradParams φ n d xs θ₀‖ ≤ G₀) :
    ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ *ᵥ
        (gradParams φ n d xs θ).ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ
        (gradParams φ n d xs θ₀).ofLp)‖ ≤
      jr * G₀ + (M + jr) * ((Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) / Real.sqrt (n : ℝ)) * Cd) := by
  obtain ⟨hC₁, hC₂, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR ⟨0, hn⟩)
  have hg := norm_gradParams_sub_le φ hact.differentiable n d hn xs θ₀ θ C₁ C₂ R hC₁ hC₂ hR0
    hφ_lip hact.deriv_bdd hact.deriv_lip hR
  set Lx : ℝ := Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 +
    3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) / Real.sqrt (n : ℝ) with hLx
  have hLx0 : 0 ≤ Lx := by positivity
  have hjr0 : 0 ≤ jr := (norm_nonneg _).trans hJ
  have hsplit : (WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ *ᵥ
        (gradParams φ n d xs θ).ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ
        (gradParams φ n d xs θ₀).ofLp) =
      WithLp.toLp 2 ((outputJacobian (netFromParams φ n d) Xs θ -
        outputJacobian (netFromParams φ n d) Xs θ₀) *ᵥ (gradParams φ n d xs θ₀).ofLp) +
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ *ᵥ
        (gradParams φ n d xs θ - gradParams φ n d xs θ₀).ofLp) := by
    ext i
    simp [Matrix.sub_mulVec, Matrix.mulVec_sub]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (mulVec_frobenius_norm_le _ _).trans (mul_le_mul hJ hg₀ (norm_nonneg _) hjr0)
  · refine (mulVec_frobenius_norm_le _ _).trans ?_
    have hJθ : ‖outputJacobian (netFromParams φ n d) Xs θ‖ ≤ M + jr := by
      have := norm_sub_le_norm_sub_add_norm_sub (outputJacobian (netFromParams φ n d) Xs θ)
        (outputJacobian (netFromParams φ n d) Xs θ₀) 0
      simp only [sub_zero] at this
      linarith
    exact mul_le_mul hJθ (hg.trans (mul_le_mul_of_nonneg_left hΔ hLx0)) (norm_nonneg _)
      ((norm_nonneg _).trans hJθ)

open Filter Topology in
/-- The tangent-feature Lipschitz scale `K_x(R₀(n)) / √n` at a test input, with the high-probability
readout bound `R₀(n) = √(2 log (2 n / δ))`, tends to `0`. -/
private lemma tendsto_testGradLipschitzRate {d : ℕ} (x : Fin d → ℝ) (C₁ C₂ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, x j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) /
        Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  simpa using tendsto_jacobianLipschitzScale (fun _ : Fin 1 => x) C₁ C₂ hδ 0

/-- **Initialization concentration of the train-test cross-kernel.** For a test input `x`, the
empirical cross-kernel vector `α ↦ ⟪∇f(x; θ₀), ∇f(X α; θ₀)⟫ = (J(θ₀) ∇f(x; θ₀))_α` converges in
probability to `α ↦ limitingFullNTKMatrix φ (X, x) (last, α)`, the train-test entries of the
limiting NTK of the extended dataset. No separate cross-kernel law of large numbers is needed: the
cross-kernel is a row of the empirical NTK Gram matrix of the extended dataset `(X, x)`
(`empiricalNTKMatrix_snoc_last`), whose convergence is
`tendsto_initMeasure_empiricalNTKMatrix_ge_eps`. -/
theorem tendsto_initMeasure_crossKernel_ge_eps
    {d m : ℕ} (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) (X : Fin m → Fin d → ℝ) (x : Fin d → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)) {p | ε ≤
        ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (packParams p.1 p.2)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (fun α : Fin m => limitingFullNTKMatrix φ
            (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ)
              (Fin.last m) (Fin.castSucc α))‖})
      Filter.atTop (nhds 0) := by
  have hφ := hact.differentiable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hφ
  obtain ⟨-, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ hderiv_meas X'
    (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU' (fun n => bot_le)
    (fun n => measure_mono fun p hp => ?_)
  rw [Set.mem_ofPred_eq] at hp ⊢
  refine hp.trans (le_of_eq_of_le ?_ (norm_row_castSucc_le
    (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j)
      (packParams p.1 p.2) - limitingFullNTKMatrix φ X') (Fin.last m)).1)
  congr 1
  ext α
  have hsn : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
      (Fin.snoc (α := fun _ => Fin d → ℝ) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
  simp only [PiLp.sub_apply, Matrix.sub_apply]
  rw [hsn, ← tangentFeature_netFromParams_of_differentiable φ hφ n d,
    outputJacobian_mulVec_tangentFeature, (empiricalNTKMatrix_snoc_last _ _ _ _ α).1]

/-- **Cross-kernel freezing in probability on `[0, T]`.** For a test input `x`, the train-test
cross-kernel vector `k_θ(x) = J(θ) ∇_θ f(x; θ)` (entries `⟪∇f(x; θ), ∇f(X α; θ)⟫`) stays within `ε₀`
of its initial value on `[0, T]` with probability tending to one. No spectral gap is assumed. The
proof splits `k_{θ(t)} - k_{θ(0)} = (J(θ(t)) - J(θ(0))) ∇f(x; θ(0)) + J(θ(t)) (∇f(x; θ(t)) -
∇f(x; θ(0)))` and uses the Jacobian drift of the finite-horizon event, the Lipschitz bound of the
tangent feature at `x` (`norm_gradParams_sub_le`), and concentration of `‖∇f(x; θ(0))‖² = K'(x, x)`
from the extended dataset. -/
theorem tendsto_measure_crossKernel_drift_finite_horizon
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) with hXs
  set xs : Fin d → ℝ := (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  have hφ := hact.differentiable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hφ
  obtain ⟨-, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
  have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ hderiv_meas X'
    (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) one_pos
  refine tendsto_measure_exists_gt_of_good_events (fun n => ((Measure.pi fun _ : Fin n => Measure.pi
      fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t => ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖)
    hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, C, M, _, jacRate, _, N, -, -, hjr, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  set δ : ℝ := min 1 (c / 8) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hLx := tendsto_testGradLipschitzRate xs C₁ C₂ hδpos
  refine ⟨fun n => jacRate n * G₀ + (M + jacRate n) *
    (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
      (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
      Real.sqrt (n : ℝ) * C), ?_, ?_⟩
  · simpa using (hjr.mul_const G₀).add ((hjr.const_add M).mul (hLx.mul_const C))
  filter_upwards [Filter.eventually_ge_atTop (max N 1),
    hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
    with n hn' hUn'
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | 1 ≤
    ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
      Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
  have hUm' : MeasurableSet U' :=
    measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' 1
  have hU'r : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real U' ≤ c / 4 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
        (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
    simp only [hU'def, ← this]
    exact hUn'.le
  refine ⟨E ∩ U'ᶜ, hEm.inter hUm'.compl, ?_, ?_⟩
  · have hEc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ ≤ 2 * δ + c / 4 := by
      rw [probReal_compl_eq_one_sub hEm]
      linarith
    have h2 := measureReal_compl_inter_le ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) E U'ᶜ
    rw [compl_compl] at h2
    have := min_le_right 1 (c / 8)
    have h3 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
    linarith
  · rintro p ⟨hpE, hpU'⟩ hflow t ht
    obtain ⟨-, hp2, hJ0, hall⟩ := hEp p hpE
    have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
        Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < 1 := not_le.1 hpU'
    have hrow := norm_row_castSucc_le
      (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L') (Fin.last m)
    have hg0 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ≤ G₀ := by
      rw [hG₀]
      refine Real.le_sqrt_of_sq_le ?_
      have h1 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ^ 2 = empiricalNTKMatrix
          (netFromParams φ n d)
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ)
          (packParams p.1 p.2) (Fin.last m) (Fin.last m) := by
        rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2,
          tangentFeature_netFromParams_of_differentiable φ hφ, real_inner_self_eq_norm_sq]
      have h2 := hrow.2
      rw [Matrix.sub_apply] at h2
      have h3 := (abs_le.1 (h2.trans hpU2.le)).2
      have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
      rw [h1]
      linarith
    have hreadout : ∀ i : Fin n, |unpackA (packParams p.1 p.2) i| ≤
        Real.sqrt (2 * Real.log (2 * n / δ)) := fun i => by
      simpa [unpackA_packParams] using hp2 i
    have hall' := hall (θ n p) hflow t ht
    have := norm_crossKernel_sub_le hact hn0 Xs xs hreadout hall'.2.2.2 hJ0 hall'.2.1 hg0
    rw [hflow.init]
    exact this

/-- **Cross-kernel freezing in probability on `[0, ∞)` from a positive limiting gap.** The
counterpart of `tendsto_measure_crossKernel_drift_finite_horizon` for all times `t ≥ 0`: if
`K_∞ ≥ lambda_inf • 1` with `lambda_inf > 0`, the train-test cross-kernel vector
`k_θ(x) = J(θ) ∇_θ f(x; θ)` stays within `ε₀` of its initial value for *all* `t ≥ 0` with
probability tending to one. The proof is the same splitting
`k_{θ(t)} - k_{θ(0)} = (J(θ(t)) - J(θ(0))) ∇f(x; θ(0)) + J(θ(t)) (∇f(x; θ(t)) - ∇f(x; θ(0)))`
and uses the Jacobian drift of the finite-horizon event, the Lipschitz bound of the
tangent feature at `x` (`norm_gradParams_sub_le`), and concentration of `‖∇f(x; θ(0))‖² = K'(x, x)`
from the extended dataset. -/
theorem tendsto_measure_crossKernel_drift_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) with hXs
  set xs : Fin d → ℝ := (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  have hφ := hact.differentiable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hφ
  obtain ⟨-, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
  have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ hderiv_meas X'
    (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) one_pos
  refine tendsto_measure_exists_gt_of_good_events (fun n => ((Measure.pi fun _ : Fin n => Measure.pi
      fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          (Set.Ici 0)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t => ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖)
    hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, jacRate, _, N, C, M, R, -, hjr, -, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 8) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  set δ : ℝ := min 1 (c / 8) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hLx := tendsto_testGradLipschitzRate xs C₁ C₂ hδpos
  refine ⟨fun n => jacRate n * G₀ + (M + jacRate n) *
    (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
      (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
      Real.sqrt (n : ℝ) * C), ?_, ?_⟩
  · simpa using (hjr.mul_const G₀).add ((hjr.const_add M).mul (hLx.mul_const C))
  filter_upwards [Filter.eventually_ge_atTop (max N 1),
    hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
    with n hn' hUn'
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | 1 ≤
    ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
      Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
  have hUm' : MeasurableSet U' :=
    measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' 1
  have hU'r : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real U' ≤ c / 4 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
        (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
    simp only [hU'def, ← this]
    exact hUn'.le
  refine ⟨E ∩ U'ᶜ, hEm.inter hUm'.compl, ?_, ?_⟩
  · have hEc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ ≤ 2 * δ + 2 * (c / 8) := by
      rw [probReal_compl_eq_one_sub hEm]
      linarith
    have h2 := measureReal_compl_inter_le ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) E U'ᶜ
    rw [compl_compl] at h2
    have := min_le_right 1 (c / 8)
    have h3 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
    linarith
  · rintro p ⟨hpE, hpU'⟩ hflow t ht
    obtain ⟨-, hJ0, hall, hp2⟩ := hEp p hpE
    have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
        Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < 1 := not_le.1 hpU'
    have hrow := norm_row_castSucc_le
      (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L') (Fin.last m)
    have hg0 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ≤ G₀ := by
      rw [hG₀]
      refine Real.le_sqrt_of_sq_le ?_
      have h1 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ^ 2 = empiricalNTKMatrix
          (netFromParams φ n d)
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ)
          (packParams p.1 p.2) (Fin.last m) (Fin.last m) := by
        rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2,
          tangentFeature_netFromParams_of_differentiable φ hφ, real_inner_self_eq_norm_sq]
      have h2 := hrow.2
      rw [Matrix.sub_apply] at h2
      have h3 := (abs_le.1 (h2.trans hpU2.le)).2
      have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
      rw [h1]
      linarith
    have hreadout : ∀ i : Fin n, |unpackA (packParams p.1 p.2) i| ≤
        Real.sqrt (2 * Real.log (2 * n / δ)) := fun i => by
      simpa [unpackA_packParams] using hp2 i
    have hall' := (hall (θ n p) hflow).2 t ht
    have := norm_crossKernel_sub_le hact hn0 Xs xs hreadout hall'.1 hJ0 hall'.2.2.2.1 hg0
    rw [hflow.init]
    exact this

end

end NTK
