/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.GlobalGap

/-!
# Two-layer network: construction of the gradient-flow family

Forward-time existence, uniqueness and measurable dependence on the initialization of the gradient
flow for every `SmoothActivation` (Phases 10 and 11.1), and the Phase 8 and Phase 9 theorems with
the trajectory hypotheses discharged.

## Main results and proof outline

- `exists_forwardGradientFlow`, `exists_forwardGradientFlow_family`, `forwardGradientFlow_unique`,
  `gradientFlow_finite_horizon_training_limit`,
  `gradientFlow_global_positive_gap_lazy_training_limit` : **Phases 10 and 11.1** - forward-time
  existence, uniqueness and continuous dependence of the gradient flow for every `SmoothActivation`
  (Picard-Lindelöf on a truncated field, an a priori bound from loss monotonicity, the linear growth
  of the Jacobian and Grönwall), a measurable trajectory family for every width, and the Phase 8 and
  Phase 9 theorems with the trajectory hypotheses discharged.

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

/-! ### Construction of the Gradient-Flow Family

For a smooth activation (no bound on the value of `φ`), the negative MSE gradient field of the
two-layer network is locally Lipschitz (`locallyLipschitz_neg_gradient_mseLoss_netFromParams`) and
forward solutions obey an a priori bound: the loss is nonincreasing, so the residual stays bounded,
the Jacobian grows at most linearly in the parameters, and Grönwall's inequality bounds the
parameters on finite horizons (`forward_apriori_bound`). The generic theorem `exists_forward_flow`
therefore yields a forward flow, continuous in the initial parameters, so every initialization has a
`ForwardGFTrajectory` and fixed-time evaluation is continuous, hence measurable, in the
initialization. Backward-time solutions are deliberately not constructed: for an unbounded
activation they can blow up. -/

section GradientFlowConstruction

variable {m d n : ℕ}

/-- Coordinates of the negative MSE gradient of the two-layer network in terms of the hidden and
readout blocks. -/
lemma gradient_mseLoss_netFromParams_apply (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (k : Fin (n * d + n)) :
    gradient (mseLoss (netFromParams φ n d) X y) θ k =
      (m : ℝ)⁻¹ * ∑ α : Fin m, (netFromParams φ n d (X α) θ - y α) *
        gradParams φ n d (X α) θ k := by
  have hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X α) θ') θ :=
    fun α => (hasFDerivAt_netFromParams φ n d (X α) θ fun i => hφ.differentiableAt).differentiableAt
  rw [gradient_mseLoss_apply_j _ X y θ hdiff k]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [outputJacobian, Matrix.of_apply, tangentFeature_netFromParams_of_differentiable φ hφ n d]
  simp [trainingResidual, trainingOutputs]
  ring

private lemma locallyLipschitz_const_mul {α : Type*} [PseudoEMetricSpace α] (c : ℝ) {f : α → ℝ}
    (hf : LocallyLipschitz f) : LocallyLipschitz (fun x => c * f x) :=
  locallyLipschitz_mul_real (LipschitzWith.const c).locallyLipschitz hf

private lemma locallyLipschitz_mul_const {α : Type*} [PseudoEMetricSpace α] (c : ℝ) {f : α → ℝ}
    (hf : LocallyLipschitz f) : LocallyLipschitz (fun x => f x * c) :=
  locallyLipschitz_mul_real hf (LipschitzWith.const c).locallyLipschitz

/-- The negative MSE gradient field of the two-layer network is locally Lipschitz when `φ` and its
derivative are locally Lipschitz. This is the hypothesis behind local existence and uniqueness of
the gradient-flow ODE (Picard-Lindelöf). Proof: every coordinate of the field is a finite sum of
products of locally Lipschitz functions of the packed parameters. -/
theorem locallyLipschitz_neg_gradient_mseLoss_netFromParams (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (hφL : LocallyLipschitz φ) (hdφL : LocallyLipschitz (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    LocallyLipschitz (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      -gradient (mseLoss (netFromParams φ n d) X y) θ) := by
  have hproj : ∀ k : Fin (n * d + n), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => θ k) := fun k =>
    (ContinuousLinearMap.contDiff (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin (n * d + n))
      →L[ℝ] ℝ)).locallyLipschitz
  have hpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => unpackW θ i ⬝ᵥ X α) := fun i α => by
    unfold dotProduct
    exact locallyLipschitz_finset_sum _ fun j _ => locallyLipschitz_mul_const _ (hproj _)
  have hφpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => φ (unpackW θ i ⬝ᵥ X α)) :=
    fun i α => hφL.comp (hpre i α)
  have hdφpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => deriv φ (unpackW θ i ⬝ᵥ X α)) :=
    fun i α => hdφL.comp (hpre i α)
  have hnet : ∀ α : Fin m, LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => netFromParams φ n d (X α) θ) := fun α => by
    simp only [netFromParams_eq_normalized_sum]
    exact locallyLipschitz_const_mul _ (locallyLipschitz_finset_sum _ fun i _ =>
      locallyLipschitz_mul_real (hproj _) (hφpre i α))
  have hres : ∀ α : Fin m, LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => netFromParams φ n d (X α) θ - y α) :=
    fun α => by
      simpa only [sub_eq_add_neg] using (hnet α).add (LipschitzWith.const (-(y α))).locallyLipschitz
  refine locallyLipschitz_euclidean_of_coord fun k => ?_
  obtain ⟨p, rfl⟩ := (paramIndexEquiv n d).surjective k
  have hform : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
      (-gradient (mseLoss (netFromParams φ n d) X y) θ) ((paramIndexEquiv n d) p) =
        -((m : ℝ)⁻¹ * ∑ α : Fin m, (netFromParams φ n d (X α) θ - y α) *
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) p)) := fun θ => by
    rw [PiLp.neg_apply, gradient_mseLoss_netFromParams_apply φ hφ]
  simp only [hform]
  have hg : ∀ α : Fin m, LocallyLipschitz (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      gradParams φ n d (X α) θ ((paramIndexEquiv n d) p)) := fun α => by
    rcases p with ⟨i, j⟩ | i
    · have : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) (Sum.inl (i, j))) =
            (n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ X α) * X α j := fun θ =>
        packParams_apply_idxW _ _ i j
      simp only [this]
      exact locallyLipschitz_mul_const _ (locallyLipschitz_mul_real
        (locallyLipschitz_const_mul _ (hproj (idxA i))) (hdφpre i α))
    · have : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) (Sum.inr i)) =
            (n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⬝ᵥ X α) := fun θ => packParams_apply_idxA _ _ i
      simp only [this]
      exact locallyLipschitz_const_mul _ (hφpre i α)
  exact (locallyLipschitz_const_mul _ (locallyLipschitz_finset_sum _ fun α _ =>
    locallyLipschitz_mul_real (hres α) (hg α))).neg

section APriori
variable {φ : ℝ → ℝ} {C₁ C₂ : ℝ}

private lemma flow_sqrt_inv_nat_mul_nat (hn : 0 < n) :
    ((n : ℝ)⁻¹).sqrt * (n : ℝ) = Real.sqrt (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_inv]
  field_simp
  exact (Real.sq_sqrt hn'.le).symm

/-- **Linear growth of the output Jacobian.** For a smooth activation the Frobenius norm of the
output Jacobian grows at most linearly in the parameter norm: `‖J(θ)‖ ≤ c₀ + c₁ ‖θ‖`, with constants
depending on the data but not on `θ`. Each neuron block satisfies
`‖w_i‖² + a_i² ≤ ‖θ‖²`, and `φ(w ⬝ᵥ x)² ≤ 2 φ(0)² + 2 C₁² ‖w‖² ‖x‖²`. -/
private lemma exists_jacobian_linear_bound (hact : SmoothActivation φ C₁ C₂) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ c₀ + c₁ * ‖θ‖ := by
  obtain ⟨hC₁0, -, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  set S : Fin m → ℝ := fun α => ∑ j : Fin d, X α j ^ 2 with hS
  have hS0 : ∀ α, 0 ≤ S α := fun α => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨Real.sqrt (2 * m * φ 0 ^ 2), Real.sqrt (3 * C₁ ^ 2 * ∑ α : Fin m, S α),
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, fun θ => ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hblock : ∀ i : Fin n, (∑ j : Fin d, θ (idxW i j) ^ 2) + θ (idxA i) ^ 2 ≤ ‖θ‖ ^ 2 :=
    fun i => by
      rw [← norm_sq_restrictCoords_neuronCoords]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_restrictCoords_neuronCoords_le i θ) 2
  -- per-entry bound
  have hentry : ∀ (α : Fin m) (i : Fin n),
      (∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) + gradA φ n d (X α) θ i ^ 2 ≤
        (n : ℝ)⁻¹ * (2 * φ 0 ^ 2 + 3 * C₁ ^ 2 * S α * ‖θ‖ ^ 2) := by
    intro α i
    refine (neuron_block_energy_le φ hact.deriv_bdd hn θ i (X α)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    set u := unpackW θ i ⬝ᵥ X α with hu
    have hφu : φ u ^ 2 ≤ 2 * φ 0 ^ 2 + 2 * (C₁ ^ 2 * u ^ 2) := by
      have h1 : |φ u| ≤ |φ 0| + C₁ * |u| := by
        have := hφ_lip u 0
        rw [sub_zero] at this
        calc |φ u| ≤ |φ 0| + |φ u - φ 0| := by
              have := abs_sub_abs_le_abs_sub (φ u) (φ 0)
              linarith [abs_sub_comm (φ u) (φ 0)]
          _ ≤ _ := by linarith
      have h2 := add_sq_le (a := |φ 0|) (b := C₁ * |u|)
      calc φ u ^ 2 = |φ u| ^ 2 := (sq_abs _).symm
        _ ≤ (|φ 0| + C₁ * |u|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ ≤ 2 * (|φ 0| ^ 2 + (C₁ * |u|) ^ 2) := h2
        _ = _ := by rw [sq_abs, mul_pow, sq_abs]; ring
    have hucs : u ^ 2 ≤ (∑ j : Fin d, θ (idxW i j) ^ 2) * S α := sq_dotProduct_le _ _
    have hw : (∑ j : Fin d, θ (idxW i j) ^ 2) ≤ ‖θ‖ ^ 2 := by
      have := hblock i
      nlinarith [sq_nonneg (θ (idxA i))]
    have ha : θ (idxA i) ^ 2 ≤ ‖θ‖ ^ 2 := by
      have := hblock i
      nlinarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (θ (idxW i j))]
    have hSα := hS0 α
    have hC := sq_nonneg C₁
    have hu2 : u ^ 2 ≤ ‖θ‖ ^ 2 * S α :=
      hucs.trans (mul_le_mul_of_nonneg_right hw hSα)
    have hun : unpackA θ i ^ 2 = θ (idxA i) ^ 2 := rfl
    rw [hun]
    nlinarith [mul_le_mul_of_nonneg_left hu2 hC, mul_le_mul_of_nonneg_left ha
      (mul_nonneg hC hSα)]
  have hsq : ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2 ≤
      2 * m * φ 0 ^ 2 + 3 * C₁ ^ 2 * (∑ α : Fin m, S α) * ‖θ‖ ^ 2 := by
    rw [outputJacobian_netFromParams_frobenius_norm_sq φ n d m X θ
      (fun _ _ => hact.differentiable.differentiableAt)]
    have hreg : (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) +
        ∑ α : Fin m, ∑ i : Fin n, gradA φ n d (X α) θ i ^ 2 =
        ∑ α : Fin m, ∑ i : Fin n, ((∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) +
          gradA φ n d (X α) θ i ^ 2) := by
      simp only [Finset.sum_add_distrib]
    rw [hreg]
    calc _ ≤ ∑ α : Fin m, ∑ i : Fin n, (n : ℝ)⁻¹ * (2 * φ 0 ^ 2 + 3 * C₁ ^ 2 * S α * ‖θ‖ ^ 2) :=
          Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun i _ => hentry α i
      _ = ∑ α : Fin m, (2 * φ 0 ^ 2 + 3 * C₁ ^ 2 * S α * ‖θ‖ ^ 2) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
          ring
  have hnn : 0 ≤ 2 * (m : ℝ) * φ 0 ^ 2 := by positivity
  have hnn' : 0 ≤ 3 * C₁ ^ 2 * (∑ α : Fin m, S α) := by
    have : 0 ≤ ∑ α : Fin m, S α := Finset.sum_nonneg fun α _ => hS0 α
    positivity
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  calc ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2
      ≤ 2 * m * φ 0 ^ 2 + 3 * C₁ ^ 2 * (∑ α : Fin m, S α) * ‖θ‖ ^ 2 := hsq
    _ ≤ (Real.sqrt (2 * m * φ 0 ^ 2) +
          Real.sqrt (3 * C₁ ^ 2 * ∑ α : Fin m, S α) * ‖θ‖) ^ 2 := by
        rw [add_sq, mul_pow, Real.sq_sqrt hnn, Real.sq_sqrt hnn']
        nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg (2 * (m : ℝ) * φ 0 ^ 2))
          (Real.sqrt_nonneg (3 * C₁ ^ 2 * ∑ α : Fin m, S α))) (norm_nonneg θ)]

/-- **The training residual is bounded on bounded parameter sets.** For a smooth activation
(linear growth) and fixed width, `‖r(θ)‖ ≤ B` whenever `‖θ‖ ≤ ρ`. -/
private lemma exists_residual_bound (hact : SmoothActivation φ C₁ C₂) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ‖ ≤ ρ →
      ‖trainingResidual (netFromParams φ n d) X y θ‖ ≤ B := by
  obtain ⟨hC₁0, -, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set ρp : ℝ := max ρ 0 with hρp
  have hρ0 : 0 ≤ ρp := le_max_right _ _
  set b : Fin m → ℝ := fun α => Real.sqrt (n : ℝ) * (ρp * (|φ 0| + C₁ * (ρp *
    Real.sqrt (∑ j : Fin d, X α j ^ 2)))) + |y α| with hb
  refine ⟨∑ α : Fin m, b α, Finset.sum_nonneg fun α _ => by positivity, fun θ hθ => ?_⟩
  have hθ' : ‖θ‖ ≤ ρp := hθ.trans (le_max_left _ _)
  refine (norm_euclidean_le_sum_norm _).trans ?_
  refine Finset.sum_le_sum fun α _ => ?_
  have hresα : trainingResidual (netFromParams φ n d) X y θ α =
      netFromParams φ n d (X α) θ - y α := rfl
  rw [hresα, Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  refine add_le_add ?_ le_rfl
  rw [netFromParams_eq_normalized_sum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hterm : ∀ i : Fin n, |unpackA θ i * φ (unpackW θ i ⬝ᵥ X α)| ≤
      ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2))) := by
    intro i
    have hblock : (∑ j : Fin d, θ (idxW i j) ^ 2) + θ (idxA i) ^ 2 ≤ ‖θ‖ ^ 2 := by
      rw [← norm_sq_restrictCoords_neuronCoords]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_restrictCoords_neuronCoords_le i θ) 2
    have ha : |unpackA θ i| ≤ ρp := by
      have h2 : unpackA θ i ^ 2 ≤ ρp ^ 2 := by
        change θ (idxA i) ^ 2 ≤ ρp ^ 2
        have := hblock
        nlinarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (θ (idxW i j)),
          pow_le_pow_left₀ (norm_nonneg θ) hθ' 2]
      exact (sq_le_sq₀ (abs_nonneg _) hρ0).1 (by rwa [sq_abs])
    have hu : |unpackW θ i ⬝ᵥ X α| ≤ ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2) := by
      have hw : (∑ j : Fin d, θ (idxW i j) ^ 2) ≤ ρp ^ 2 := by
        have := hblock
        nlinarith [sq_nonneg (θ (idxA i)), pow_le_pow_left₀ (norm_nonneg θ) hθ' 2]
      have hu2 : |unpackW θ i ⬝ᵥ X α| ^ 2 ≤
          (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)) ^ 2 := by
        rw [sq_abs, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        exact (sq_dotProduct_le (unpackW θ i) (X α)).trans
          (mul_le_mul_of_nonneg_right hw (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 hu2
    have hφu : |φ (unpackW θ i ⬝ᵥ X α)| ≤
        |φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)) := by
      have := hφ_lip (unpackW θ i ⬝ᵥ X α) 0
      rw [sub_zero] at this
      have h1 : |φ (unpackW θ i ⬝ᵥ X α)| ≤ |φ 0| + |φ (unpackW θ i ⬝ᵥ X α) - φ 0| := by
        have := abs_sub_abs_le_abs_sub (φ (unpackW θ i ⬝ᵥ X α)) (φ 0)
        linarith [abs_sub_comm (φ (unpackW θ i ⬝ᵥ X α)) (φ 0)]
      have h2 : C₁ * |unpackW θ i ⬝ᵥ X α| ≤ C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)) :=
        mul_le_mul_of_nonneg_left hu hC₁0
      linarith
    rw [abs_mul]
    exact mul_le_mul ha hφu (abs_nonneg _) hρ0
  have hsum : |∑ i : Fin n, unpackA θ i * φ (unpackW θ i ⬝ᵥ X α)| ≤
      (n : ℝ) * (ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _i : Fin n, ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2))) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp
  calc ((n : ℝ)⁻¹).sqrt * |∑ i : Fin n, unpackA θ i * φ (unpackW θ i ⬝ᵥ X α)|
      ≤ ((n : ℝ)⁻¹).sqrt * ((n : ℝ) *
          (ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2))))) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = Real.sqrt (n : ℝ) * (ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)))) := by
        rw [← mul_assoc, flow_sqrt_inv_nat_mul_nat hn]

/-- **Forward a priori bound for gradient-flow solutions.** For a smooth activation and fixed width,
any solution of `θ' = -∇L(θ)` on `[0, S]`, `S ≤ T`, that starts in the ball of radius `r` stays in a
ball of radius `ρ(T, r)`. Proof: the loss is nonincreasing, hence the residual stays bounded by its
initial size `B`; then `‖θ'‖ ≤ (1/m) ‖J(θ)‖ B ≤ K ‖θ‖ + ε` by the linear growth of the Jacobian and
Grönwall's inequality applies. Only forward time is used, and no bound on `φ` itself. -/
private theorem forward_apriori_bound (hact : SmoothActivation φ C₁ C₂) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T r : ℝ) :
    ∃ ρ : ℝ, ∀ (θ : ℝ → EuclideanSpace ℝ (Fin (n * d + n))) (S : ℝ), 0 ≤ S → S ≤ T →
      ‖θ 0‖ ≤ r → (∀ t ∈ Set.Icc 0 S,
        HasDerivWithinAt θ (-gradient (mseLoss (netFromParams φ n d) X y) (θ t))
          (Set.Icc 0 S) t) → ‖θ S‖ ≤ ρ := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hJ⟩ := exists_jacobian_linear_bound hact hn X
  obtain ⟨B, hB0, hB⟩ := exists_residual_bound hact hn X y r
  set rp : ℝ := max r 0 with hrp
  set Tp : ℝ := max T 0 with hTp
  have hr0 : 0 ≤ rp := le_max_right _ _
  set K : ℝ := (m : ℝ)⁻¹ * c₁ * B with hK
  set ε : ℝ := (m : ℝ)⁻¹ * c₀ * B with hε
  have hK0 : 0 ≤ K := by positivity
  have hε0 : 0 ≤ ε := by positivity
  refine ⟨(rp + ε * Tp) * Real.exp (K * Tp), fun θ S hS0 hST hθ0 hθ => ?_⟩
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (X β) θ') (θ t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (X β) (θ t)
      fun i => hact.differentiable.differentiableAt).differentiableAt
  have hmono := mseLoss_le_of_hasDerivWithinAt_neg_gradient (netFromParams φ n d) X y
    (θ := θ) (S := S) (fun t _ => hdiff t) hθ
  have hres : ∀ t ∈ Set.Icc (0 : ℝ) S,
      ‖trainingResidual (netFromParams φ n d) X y (θ t)‖ ≤ B := by
    intro t ht
    have h0 : ‖trainingResidual (netFromParams φ n d) X y (θ 0)‖ ≤ B := hB _ hθ0
    have h1 := hmono t ht
    unfold mseLoss at h1
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have : ‖trainingResidual (netFromParams φ n d) X y (θ t)‖ = 0 := by
        rw [EuclideanSpace.norm_eq]; simp
      rw [this]; exact hB0
    · have h2 := le_of_mul_le_mul_left h1 (by positivity : (0 : ℝ) < (2 * (m : ℝ))⁻¹)
      exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2).trans h0
  have hspeed : ∀ t ∈ Set.Icc (0 : ℝ) S,
      ‖-gradient (mseLoss (netFromParams φ n d) X y) (θ t)‖ ≤ K * ‖θ t‖ + ε := by
    intro t ht
    rw [norm_neg]
    refine (gradient_mseLoss_norm_le (netFromParams φ n d) X y (θ t) (hdiff t)).trans ?_
    have h1 := hJ (θ t)
    calc (m : ℝ)⁻¹ * ‖outputJacobian (netFromParams φ n d) X (θ t)‖ *
          ‖trainingResidual (netFromParams φ n d) X y (θ t)‖
        ≤ (m : ℝ)⁻¹ * (c₀ + c₁ * ‖θ t‖) * B := by
          gcongr
          exact hres t ht
      _ = K * ‖θ t‖ + ε := by rw [hK, hε]; ring
  have hcont : ContinuousOn θ (Set.Icc 0 S) := fun t ht => (hθ t ht).continuousWithinAt
  have hright : ∀ x ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt θ (-gradient (mseLoss (netFromParams φ n d) X y) (θ x)) (Set.Ici x) x :=
    fun x hx => (hθ x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Set.Icc_subset_Icc hx.1 le_rfl))
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le hcont hright (δ := rp)
    (le_trans hθ0 (le_max_left _ _)) (fun x hx => hspeed x ⟨hx.1, hx.2.le⟩) S ⟨hS0, le_rfl⟩
  refine hG.trans ((gronwallBound_le_mul_exp hK0 hε0).trans ?_)
  have hST' : S ≤ Tp := hST.trans (le_max_left _ _)
  rw [sub_zero]
  gcongr

private theorem exists_forwardGradientFlow_of_pos (hact : SmoothActivation φ C₁ C₂)
    (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ Φ : EuclideanSpace ℝ (Fin (n * d + n)) → ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ θ₀, ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ (Φ θ₀)) ∧
      Continuous (fun q : EuclideanSpace ℝ (Fin (n * d + n)) × ℝ => Φ q.1 q.2) := by
  obtain ⟨hφL, hdφL⟩ := activation_locallyLipschitz hact
  have hLL := locallyLipschitz_neg_gradient_mseLoss_netFromParams (n := n) φ hact.differentiable
    hφL hdφL X y
  obtain ⟨Φ, hΦ0, hΦd, hΦc⟩ := exists_forward_flow
    (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      -gradient (mseLoss (netFromParams φ n d) X y) θ)
    (lipschitz_on_ball_of_locallyLipschitz hLL)
    (fun T r => forward_apriori_bound hact hn X y T r)
  exact ⟨Φ, fun θ₀ => ⟨hΦ0 θ₀,
    (hΦc.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn,
    fun t ht => by simpa using hΦd θ₀ t ht⟩, hΦc⟩

/-- **Every initialization has a gradient flow, continuous in the initialization.** For a
`SmoothActivation` (no bound on the value of `φ`) and any dataset there is a map `Φ` such that
`Φ θ₀` is a forward-time trajectory of the MSE gradient flow started at `θ₀`, jointly continuous in
the initial parameters and time. Existence uses the Picard-Lindelöf theorem on a truncated field and
the a priori bound `forward_apriori_bound`; nothing is asserted for negative times, where
solutions can blow up. -/
theorem exists_forwardGradientFlow (hact : SmoothActivation φ C₁ C₂) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ Φ : EuclideanSpace ℝ (Fin (n * d + n)) → ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ θ₀, ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ (Φ θ₀)) ∧
      Continuous (fun q : EuclideanSpace ℝ (Fin (n * d + n)) × ℝ => Φ q.1 q.2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no parameters: the parameter space is a point
    have hsub : ∀ u v : EuclideanSpace ℝ (Fin (0 * d + 0)), u = v := fun u v => by
      ext k
      exact absurd k.2 (by simp)
    refine ⟨fun θ₀ _ => θ₀, fun θ₀ => ⟨rfl, continuousOn_const, fun t _ => ?_⟩, continuous_fst⟩
    rw [hsub (-gradient (mseLoss (netFromParams φ 0 d) X y) θ₀) 0]
    exact hasDerivAt_const t θ₀
  · exact exists_forwardGradientFlow_of_pos hact hn X y

/-- **Uniqueness of the gradient flow.** Two forward gradient-flow trajectories of the MSE loss of
the two-layer network from the same initialization agree for all `t ≥ 0` (for a
`SmoothActivation`). -/
theorem forwardGradientFlow_unique (hact : SmoothActivation φ C₁ C₂) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {f g : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hf : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ f)
    (hg : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ g) :
    Set.EqOn f g (Set.Ici 0) := by
  obtain ⟨hφL, hdφL⟩ := activation_locallyLipschitz hact
  have hLL := locallyLipschitz_neg_gradient_mseLoss_netFromParams (n := n) φ hact.differentiable
    hφL hdφL X y
  exact forwardFlow_unique _ (lipschitz_on_ball_of_locallyLipschitz hLL) hf.continuousOn hf.ode
    hg.continuousOn hg.ode (hf.init.trans hg.init.symm)

/-- **A measurable family of gradient-flow trajectories over the initialization laws.** There is a
family `θ n p` such that for *every* width `n` and *every* initialization `p`, `θ n p` is a forward
gradient flow of the MSE loss started at `packParams p.1 p.2`, and each fixed-time evaluation is
continuous, hence measurable, in `p`. This discharges the hypotheses `hθ_flow` (in fact everywhere,
not only almost everywhere) and `hθ_meas` of the finite-horizon and global theorems, under the
source's activation assumptions only. -/
theorem exists_forwardGradientFlow_family (hact : SmoothActivation φ C₁ C₂) (d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2)
        (θ n p)) ∧
      ∀ n t, Continuous (fun p => θ n p t) := by
  choose Φ hΦ hΦc using fun n : ℕ => exists_forwardGradientFlow hact n d m X y
  exact ⟨fun n p => Φ n (packParams p.1 p.2), fun n p => hΦ n _,
    fun n t => (hΦc n).comp (continuous_packParams.prodMk continuous_const)⟩

end APriori

/-- **Finite-horizon training limit for the constructed gradient flow (no spectral gap, no
trajectory hypotheses).** For a `SmoothActivation` (no bound on the value of `φ`), the
constructed family of gradient-flow trajectories `θ n p` (defined for every width and every
initialization, measurable
in `p`) has: kernel stationarity in probability on every `[0, T]`, and, at every fixed time
`t ≥ 0`, the trained residual and predictions converge in distribution to the frozen-kernel laws
`exp(-(t / m) K_∞) (G - y)` and `y + exp(-(t / m) K_∞) (G - y)`, `G ~ 𝒩(0, Φ^{(∞)})`. -/
theorem gradientFlow_finite_horizon_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
      (∀ n t, Measurable (fun p => θ n p t)) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ ε₀ : ℝ, 0 < ε₀ → Filter.Tendsto
        (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin n => gaussianReal 0 1)) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
          ε₀ < ‖empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
            empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
        Filter.atTop (nhds 0)) ∧
      (∀ t : ℝ, 0 ≤ t → TendstoInDistribution
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
          (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))) ∧
      (∀ t : ℝ, 0 ≤ t → TendstoInDistribution
        (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t))
        Filter.atTop
        (fun G : EuclideanSpace ℝ (Fin m) =>
          y + (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
        (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        (multivariateGaussian 0
          (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))) := by
  obtain ⟨θ, hflow, hcont⟩ := exists_forwardGradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0
      1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)), ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, fun n t => (hcont n t).measurable,
    fun T hT ε₀ hε₀ => tendsto_measure_kernel_drift_finite_horizon hm φ hact X y T hT θ hae hε₀,
    fun t ht => tendstoInDistribution_trainingResidual_matrix_exp hm hd φ hact X y t ht θ
      (fun n t => (hcont n t).measurable.aemeasurable) hae,
    fun t ht => tendstoInDistribution_trainingOutputs_matrix_exp hm hd φ hact X y t ht θ
      (fun n t => (hcont n t).measurable.aemeasurable) hae⟩

/-- **Global positive-gap lazy training limit for the constructed gradient flow.** Under a positive
limiting gap, the constructed family of gradient-flow trajectories (defined for every width and
every initialization, measurable in the initialization) satisfies the conclusion of
`global_positive_gap_lazy_training_limit`: with a measurable initialization event of probability at
least `1 - η`, the uniform quarter-gap, `O(√(log n / n))` kernel drift, exponential residual and
loss decay, and `mseLoss → 0`. No trajectory hypothesis remains. -/
theorem gradientFlow_global_positive_gap_lazy_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
      (∀ n t, Measurable (fun p => θ n p t)) ∧
      (
      ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
        (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
        ∀ n ≥ N,
        ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
          ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - η ∧ ∀ᵐ p ∂((Measure.pi
              fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)), p ∈ E →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ n p t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0)) := by
  obtain ⟨θ, hflow, hcont⟩ := exists_forwardGradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0
      1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)), ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, fun n t => (hcont n t).measurable,
    global_positive_gap_lazy_training_limit hm hd φ hact X y lambda_inf
    hlambda_inf hK_gap θ hae hη hη1⟩

/-- **Positive limiting gap from feature independence (SmoothActivation).** If the features
`w ↦ φ(w ⬝ᵥ (X α / √d))` are linearly independent modulo Gaussian-null sets -- no nontrivial
combination vanishes almost everywhere -- then the limiting kernel is positive definite and there is
`lambda_inf > 0` with `(K_∞ - lambda_inf • 1).PosSemidef`, the hypothesis `hK_gap` of the global
lazy-training theorems. The activation enters only through `SmoothActivation`, which supplies
measurability of `φ'` and the `L²` integrability of the features. -/
theorem exists_positive_gap_of_feature_independence {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) {d m : ℕ} (X : Fin m → Fin d → ℝ)
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1),
        ∑ α : Fin m, u α * φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0) :
    ∃ lambda_inf : ℝ, 0 < lambda_inf ∧ (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef := by
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  obtain ⟨hL2, -, hdL2, -⟩ := activation_memLp_two hact (d := d)
  exact exists_pos_sub_smul_one_posSemidef_of_posDef
    (limitingFullNTKMatrix_posDef_of_ae_independent φ X hderiv_meas
      (fun α => hL2 _) (fun α => hdL2 _) hind)

/-- **Constructed global lazy training from feature independence alone.** For a `SmoothActivation`
and a dataset whose scaled features are linearly independent modulo Gaussian-null sets, there is a
positive limiting gap `lambda_inf` (`exists_positive_gap_of_feature_independence`), and for every
confidence `η` the conclusion of `gradientFlow_global_positive_gap_lazy_training_limit` holds for
the constructed gradient flows with that `lambda_inf`; no spectral-gap hypothesis is assumed. -/
theorem gradientFlow_global_lazy_training_limit_of_feature_independence
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1),
        ∑ α : Fin m, u α * φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ lambda_inf : ℝ, 0 < lambda_inf ∧
        ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
            EuclideanSpace ℝ (Fin (n * d + n)),
          (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
          (∀ n t, Measurable (fun p => θ n p t)) ∧
          (
          ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
            (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
            ∀ n ≥ N,
            ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
              ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
                  (Measure.pi fun _ : Fin n => gaussianReal 0
                  1)).real E ≥ 1 - η ∧ ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)), p ∈ E →
                (∀ t : ℝ, 0 ≤ t →
                  (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                    v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
                  ‖empiricalNTKMatrix (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
                    empiricalNTKMatrix (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                    freezeRate n ∧
                  ‖trainingResidual (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
                    ‖trainingResidual (netFromParams φ n d)
                        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                      Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
                  mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                      (θ n p t) ≤
                    mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                        (packParams p.1 p.2) *
                      Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
                Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop
                  (nhds 0)) := by
  obtain ⟨lambda_inf, hlam, hgap⟩ := exists_positive_gap_of_feature_independence hact X hind
  exact ⟨lambda_inf, hlam, gradientFlow_global_positive_gap_lazy_training_limit hm hd φ hact X y
    lambda_inf hlam hgap hη hη1⟩

/-- **Constructed gradient flows with kernel drift `O(n⁻¹ᐟ²)`.** The statement of
`gradientFlow_global_positive_gap_lazy_training_limit` with the sharper drift rate of
`global_positive_gap_lazy_training_limit_inv_sqrt_width`. -/
theorem gradientFlow_global_positive_gap_lazy_training_limit_inv_sqrt_width
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
      (∀ n t, Measurable (fun p => θ n p t)) ∧
      (
      ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
        (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ / Real.sqrt (n : ℝ)) ∧
        ∀ n ≥ N,
        ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
          ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - η ∧ ∀ᵐ p ∂((Measure.pi
              fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)), p ∈ E →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ n p t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0)) := by
  obtain ⟨θ, hflow, hcont⟩ := exists_forwardGradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0
      1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)), ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, fun n t => (hcont n t).measurable,
    global_positive_gap_lazy_training_limit_inv_sqrt_width hm hd φ hact X y lambda_inf
    hlambda_inf hK_gap θ hae hη hη1⟩

end GradientFlowConstruction

end

end NTK
