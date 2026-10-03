/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.KernelFreeze

/-!
# Two-layer network: sharp kernel drift from average neuron moments

Phase 11.2: each neuron's displacement is controlled by its own initial scale, so the kernel
drift is bounded through the degree-four neuron moment averaged over neurons. This gives the
`O(n⁻¹ᐟ²)` rate without a logarithm.

## Main results and proof outline

- `neuron_displacement_le`, `kernel_drift_le_of_neuron_moments`, `exists_neuronMoment_event`,
  `exists_measurableSet_global_lazy_training_event_inv_sqrt_width`,
  `global_positive_gap_lazy_training_limit_inv_sqrt_width`,
  `gradientFlow_global_positive_gap_lazy_training_limit_inv_sqrt_width` : **Phase 11.2** - the
  same global
  theorem with kernel drift `O(n⁻¹ᐟ²)` (no logarithm): each neuron's displacement is controlled by
  its own initial scale, and the resulting degree-four neuron moment is averaged over neurons and
  bounded in probability by Markov's inequality, at the price of one extra failure probability `δ`.

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

/-! ### Sharp kernel drift from average neuron moments

The maximum-readout argument above controls every neuron by the worst readout weight and therefore
loses a `√(log n)`. Here each neuron is controlled by its *own* initial scale. Along a gradient
flow that stays in a ball of radius `C` and whose residual decays like `R e^{-ν t}`, neuron `i`
moves by at most `b_i R / (m ν)` with `b_i² = O(n⁻¹ (Q_i + C² Λ_i²))` (`neuron_displacement_le`),
so the squared Jacobian variation is `n⁻¹ ∑ᵢ Λ_i² ρ_i² = O(n⁻¹)` times an empirical average of
the degree-four neuron moment `neuronMoment` (`kernel_drift_le_of_neuron_moments`). That average is
bounded in probability by Markov's inequality (`exists_neuronMoment_event`), giving kernel drift
`O(n⁻¹ᐟ²)` without a maximum over neurons. -/

section SharpKernelDrift
variable {n d m : ℕ}

/-- Coordinates of neuron `i` in the packed parameter vector: the readout `idxA i` (`none`) and
the hidden weights `idxW i j` (`some j`). -/
def neuronCoords (n d : ℕ) (i : Fin n) : Option (Fin d) → Fin (n * d + n)
  | none => idxA i
  | some j => idxW i j

lemma norm_sq_restrictCoords_neuronCoords (i : Fin n)
    (v : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖restrictCoords (neuronCoords n d i) v‖ ^ 2 =
      (∑ j : Fin d, v (idxW i j) ^ 2) + v (idxA i) ^ 2 := by
  rw [norm_sq_restrictCoords, Fintype.sum_option]
  simp only [neuronCoords]
  ring

private lemma norm_sq_restrictCoords_neuronCoords_sub (i : Fin n)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖restrictCoords (neuronCoords n d i) (θ₁ - θ₂)‖ ^ 2 =
      (∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
        (unpackA θ₁ i - unpackA θ₂ i) ^ 2 := by
  rw [norm_sq_restrictCoords_neuronCoords]
  rfl

lemma norm_restrictCoords_neuronCoords_le (i : Fin n)
    (v : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖restrictCoords (neuronCoords n d i) v‖ ≤ ‖v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  have h := norm_sq_sub_unpack n d v (0 : EuclideanSpace ℝ (Fin (n * d + n)))
  have h0 := norm_sq_restrictCoords_neuronCoords_sub i v (0 : EuclideanSpace ℝ (Fin (n * d + n)))
  rw [sub_zero] at h h0
  rw [h0, h]
  have h1 : (∑ j : Fin d,
      (unpackW v i j - unpackW (0 : EuclideanSpace ℝ (Fin (n * d + n))) i j) ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin d,
        (unpackW v i j - unpackW (0 : EuclideanSpace ℝ (Fin (n * d + n))) i j) ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin n => ∑ j : Fin d,
      (unpackW v i j - unpackW (0 : EuclideanSpace ℝ (Fin (n * d + n))) i j) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : (unpackA v i - unpackA (0 : EuclideanSpace ℝ (Fin (n * d + n))) i) ^ 2 ≤
      ∑ i : Fin n, (unpackA v i - unpackA (0 : EuclideanSpace ℝ (Fin (n * d + n))) i) ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin n =>
      (unpackA v i - unpackA (0 : EuclideanSpace ℝ (Fin (n * d + n))) i) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- Squared per-neuron Jacobian-Lipschitz scale at readout weight `a`: the coefficient of the
neuron's squared displacement in the squared Jacobian-block variation. -/
def neuronLipschitzScaleSq (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ) (a : ℝ) : ℝ :=
  ∑ α : Fin m, (2 * a ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
    3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)

/-- Squared per-neuron activation scale: an upper bound for `n ×` the squared Frobenius norm of the
neuron's Jacobian block (hidden weights `w`, readout weight `a`). -/
noncomputable def neuronJacobianScaleSq (φ : ℝ → ℝ) (C₁ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : ℝ :=
  ∑ α : Fin m, (φ (w ⬝ᵥ X α) ^ 2 + a ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)

/-- The single-neuron observable whose empirical average controls the kernel drift at rate
`n⁻¹ᐟ²`. It is a polynomial of degree four in `(φ (w ⬝ᵥ x), a)`, so it is integrable under Gaussian
initialization as soon as `φ (w ⬝ᵥ x)` is square integrable. -/
noncomputable def neuronMoment (φ : ℝ → ℝ) (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : ℝ :=
  neuronLipschitzScaleSq C₁ C₂ X a *
    (neuronJacobianScaleSq φ C₁ X w a + neuronLipschitzScaleSq C₁ C₂ X a)

lemma neuronLipschitzScaleSq_nonneg (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ) (a : ℝ) :
    0 ≤ neuronLipschitzScaleSq C₁ C₂ X a :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma neuronJacobianScaleSq_nonneg (φ : ℝ → ℝ) (C₁ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : 0 ≤ neuronJacobianScaleSq φ C₁ X w a :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma neuronMoment_nonneg (φ : ℝ → ℝ) (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : 0 ≤ neuronMoment φ C₁ C₂ X w a :=
  mul_nonneg (neuronLipschitzScaleSq_nonneg _ _ _ _)
    (add_nonneg (neuronJacobianScaleSq_nonneg _ _ _ _ _) (neuronLipschitzScaleSq_nonneg _ _ _ _))

/-- The squared norm of neuron `i`'s Jacobian block is its gradient-coordinate energy. -/
private lemma neuron_jacobian_block_sq (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⬝ᵥ X α)) (i : Fin n) :
    ∑ α : Fin m, ∑ o : Option (Fin d),
        outputJacobian (netFromParams φ n d) X θ α (neuronCoords n d i o) ^ 2 =
      ∑ α : Fin m, ((∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) +
        gradA φ n d (X α) θ i ^ 2) := by
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Fintype.sum_option]
  simp only [neuronCoords, outputJacobian_netFromParams_apply_W φ n d m X θ hφ,
    outputJacobian_netFromParams_apply_a φ n d m X θ hφ]
  ring

lemma neuron_block_energy_le (φ : ℝ → ℝ) {C₁ : ℝ} (hC₁ : ∀ z, |deriv φ z| ≤ C₁) (hn : 0 < n)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) (x : Fin d → ℝ) :
    (∑ j : Fin d, gradW φ n d x θ i j ^ 2) + gradA φ n d x θ i ^ 2 ≤
      (n : ℝ)⁻¹ * (φ (unpackW θ i ⬝ᵥ x) ^ 2 + unpackA θ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, x j ^ 2) := by
  have hroot : ((n : ℝ)⁻¹.sqrt) ^ 2 = (n : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hd_sq : deriv φ (unpackW θ i ⬝ᵥ x) ^ 2 ≤ C₁ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hC₁ 0))).2 (hC₁ _)
  have hW : (∑ j : Fin d, gradW φ n d x θ i j ^ 2) =
      (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⬝ᵥ x) ^ 2 * ∑ j : Fin d, x j ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [gradW]
    rw [show (n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x) * x j =
        (n : ℝ)⁻¹.sqrt * (unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x) * x j) by ring, mul_pow, hroot]
    ring
  have hA : gradA φ n d x θ i ^ 2 = (n : ℝ)⁻¹ * φ (unpackW θ i ⬝ᵥ x) ^ 2 := by
    simp only [gradA]; rw [mul_pow, hroot]
  rw [hW, hA]
  have hSx : 0 ≤ ∑ j : Fin d, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : unpackA θ i ^ 2 * deriv φ (unpackW θ i ⬝ᵥ x) ^ 2 * ∑ j : Fin d, x j ^ 2 ≤
      unpackA θ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, x j ^ 2 := by gcongr
  have hn' : 0 ≤ (n : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hn']


/-- The displacement of neuron `i`'s coordinates, in the two forms used in the Jacobian-Lipschitz
estimates. -/
private lemma neuron_displacement_eq (i : Fin n) (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n))) :
    (∑ j : Fin d, (unpackW θ₀ i j - unpackW θ i j) ^ 2) + (unpackA θ₀ i - unpackA θ i) ^ 2 =
      ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 := by
  have hc : ∀ a b : ℝ, (a - b) ^ 2 = (b - a) ^ 2 := fun a b => by ring
  rw [norm_sq_restrictCoords_neuronCoords_sub]
  simp_rw [hc (unpackW θ₀ i _), hc (unpackA θ₀ i)]

/-- `b² ≤ 2 a² + 2 (a - b)²`, i.e. `add_sq_le` for `b = a + (b - a)`. -/
private lemma sq_le_two_mul_sq_add_two_mul_sq_sub (a b : ℝ) :
    b ^ 2 ≤ 2 * a ^ 2 + 2 * (a - b) ^ 2 := by
  have h := add_sq_le (a := a) (b := b - a)
  rw [add_sub_cancel] at h
  nlinarith [h]

/-- **Neuron-block Jacobian energy after a displacement.** -/
private lemma neuron_jacobian_block_energy_le_of_displacement (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    ∑ α : Fin m, ((∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) + gradA φ n d (X α) θ i ^ 2) ≤
      2 * ((n : ℝ)⁻¹ * neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i)) +
      2 * ((n : ℝ)⁻¹ * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
        ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2) := by
  set D := ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 with hD
  have hα : ∀ α : Fin m,
      (∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) + gradA φ n d (X α) θ i ^ 2 ≤
        2 * ((n : ℝ)⁻¹ * (φ (unpackW θ₀ i ⬝ᵥ X α) ^ 2 +
          unpackA θ₀ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)) +
        2 * ((n : ℝ)⁻¹ * (2 * unpackA θ₀ i ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
          3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) * D) := by
    intro α
    have h0 := neuron_block_energy_le φ hC₁ hn θ₀ i (X α)
    have hd := grad_single_neuron_sub_le φ n d (X α) θ₀ θ i C₁ C₂ |unpackA θ₀ i| hC₁0 hC₂0
      (abs_nonneg _) hφ_lip hC₁ hderiv_lip le_rfl
    dsimp only at hd
    rw [neuron_displacement_eq, sq_abs] at hd
    have hW : (∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) ≤
        2 * (∑ j : Fin d, gradW φ n d (X α) θ₀ i j ^ 2) +
        2 * ∑ j : Fin d, (gradW φ n d (X α) θ₀ i j - gradW φ n d (X α) θ i j) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => sq_le_two_mul_sq_add_two_mul_sq_sub _ _
    have hA := sq_le_two_mul_sq_add_two_mul_sq_sub (gradA φ n d (X α) θ₀ i)
      (gradA φ n d (X α) θ i)
    nlinarith
  calc _ ≤ ∑ α : Fin m, (2 * ((n : ℝ)⁻¹ * (φ (unpackW θ₀ i ⬝ᵥ X α) ^ 2 +
          unpackA θ₀ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)) +
        2 * ((n : ℝ)⁻¹ * (2 * unpackA θ₀ i ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
          3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) * D)) := Finset.sum_le_sum fun α _ => hα α
    _ = _ := by
      simp only [neuronJacobianScaleSq, neuronLipschitzScaleSq, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]

/-- **Squared Jacobian variation as a sum over neurons.** -/
lemma outputJacobian_sub_norm_sq_le_neuron_sum (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (X : Fin m → Fin d → ℝ) (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖outputJacobian (netFromParams φ n d) X θ - outputJacobian (netFromParams φ n d) X θ₀‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i : Fin n, neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
        ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 := by
  rw [norm_sub_rev, outputJacobian_sub_frobenius_norm_sq φ n d m X θ₀ θ
    (fun _ _ => hφ.differentiableAt) (fun _ _ => hφ.differentiableAt)]
  simp_rw [← Finset.sum_add_distrib]
  calc _ ≤ ∑ α : Fin m, ∑ i : Fin n, (n : ℝ)⁻¹ * (2 * |unpackA θ₀ i| ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) *
        ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun i _ => ?_
        have hd := grad_single_neuron_sub_le φ n d (X α) θ₀ θ i C₁ C₂ |unpackA θ₀ i| hC₁0 hC₂0
          (abs_nonneg _) hφ_lip hC₁ hderiv_lip le_rfl
        dsimp only at hd
        rwa [neuron_displacement_eq] at hd
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [neuronLipschitzScaleSq, sq_abs, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun α _ => ?_
      ring


/-- **Per-neuron displacement along the flow.** If the flow stays within `C` of `θ₀` and the
residual decays like `R e^{-ν t}`, then neuron `i` moves at most `b_i R / (m ν)` with
`b_i² = 2 n⁻¹ (Q_i + C² Λ_i²)`, where `Q_i, Λ_i²` are the per-neuron scales at initialization. -/
lemma neuron_displacement_le (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hn : 0 < n) (hm : 0 < m)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ_traj)
    {C R ν : ℝ} (hν : 0 < ν)
    (hdisp : ∀ t : ℝ, 0 ≤ t → ‖θ_traj t - θ₀‖ ≤ C)
    (hres : ∀ t : ℝ, 0 ≤ t →
      ‖trainingResidual (netFromParams φ n d) X y (θ_traj t)‖ ≤ R * Real.exp (-ν * t))
    {T : ℝ} (hT : 0 ≤ T) (i : Fin n) :
    ‖restrictCoords (neuronCoords n d i) (θ_traj T - θ₀)‖ ≤
      (m : ℝ)⁻¹ * Real.sqrt (2 * ((n : ℝ)⁻¹ *
        (neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i) +
          C ^ 2 * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i)))) * R / ν := by
  set b := Real.sqrt (2 * ((n : ℝ)⁻¹ *
        (neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i) +
          C ^ 2 * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i)))) with hb
  have hR : 0 ≤ R := by
    have := (norm_nonneg _).trans (hres 0 le_rfl)
    simpa using this
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hspeed : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖restrictCoords (neuronCoords n d i)
        (gradient (mseLoss (netFromParams φ n d) X y) (θ_traj t))‖ ≤
        (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t)) := by
    intro t ht
    have hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ')
        (θ_traj t) := fun β =>
      (hasFDerivAt_netFromParams φ n d (X β) (θ_traj t)
        fun _ => hφ.differentiableAt).differentiableAt
    refine (norm_restrictCoords_gradient_mseLoss_le _ X y (θ_traj t) hdiff
      (neuronCoords n d i)).trans ?_
    rw [neuron_jacobian_block_sq φ X (θ_traj t) (fun _ _ => hφ.differentiableAt) i]
    have hE := neuron_jacobian_block_energy_le_of_displacement φ hC₁0 hC₂0 hφ_lip hC₁ hderiv_lip
      hn X (θ_traj t) θ₀ i
    have hD : ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((norm_restrictCoords_neuronCoords_le i _).trans (hdisp t ht.1)) 2
    have hΛ := neuronLipschitzScaleSq_nonneg C₁ C₂ X (unpackA θ₀ i)
    have hsqrt : Real.sqrt (∑ α : Fin m, ((∑ j : Fin d, gradW φ n d (X α) (θ_traj t) i j ^ 2) +
        gradA φ n d (X α) (θ_traj t) i ^ 2)) ≤ b := by
      refine Real.sqrt_le_sqrt ?_
      have hn' : 0 ≤ (n : ℝ)⁻¹ := by positivity
      have : (n : ℝ)⁻¹ * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
          ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤
          (n : ℝ)⁻¹ * (C ^ 2 * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i)) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hn'
        nlinarith
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hres t ht.1) (by positivity))
  have hBc : Continuous (fun t : ℝ => (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t))) := by
    fun_prop
  have hBi : IntervalIntegrable (fun t : ℝ => (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t)))
      MeasureTheory.volume 0 T := hBc.intervalIntegrable 0 T
  have hmain := norm_map_sub_le_integral_of_forwardGF hflow
    (restrictCoords (neuronCoords n d i)) hT hspeed hBi
  refine hmain.trans ?_
  have hint : (∫ t in (0 : ℝ)..T, (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t))) =
      ((m : ℝ)⁻¹ * b * R) * ∫ t in (0 : ℝ)..T, Real.exp (-ν * t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hint]
  calc ((m : ℝ)⁻¹ * b * R) * ∫ t in (0 : ℝ)..T, Real.exp (-ν * t)
      ≤ ((m : ℝ)⁻¹ * b * R) * ν⁻¹ :=
        mul_le_mul_of_nonneg_left (integral_exp_neg_le ν T hν hT) (by positivity)
    _ = _ := by ring


/-- **Kernel drift at rate `n⁻¹ᐟ²` from an empirical neuron moment.** Let `θ_traj` be a gradient
flow from `θ₀` for the two-layer MSE loss, staying within `C` of `θ₀` with residual decaying like
`R e^{-ν t}` and output Jacobian bounded by `M` along the flow and at `θ₀`. If the empirical average
of the per-neuron observable `neuronMoment` at initialization is at most `τ`, the empirical NTK
stays within `2 M (R / (m ν)) √(2 (1 + C²) τ) / √n` of its initial value for all `t ≥ 0`.

There is no maximum over neurons: each neuron's displacement is controlled by its own scale
(`neuron_displacement_le`) and the averages are controlled in probability by Markov's inequality. -/
theorem kernel_drift_le_of_neuron_moments (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hn : 0 < n) (hm : 0 < m)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ_traj)
    {C R ν M τ : ℝ} (hν : 0 < ν)
    (hdisp : ∀ t : ℝ, 0 ≤ t → ‖θ_traj t - θ₀‖ ≤ C)
    (hres : ∀ t : ℝ, 0 ≤ t →
      ‖trainingResidual (netFromParams φ n d) X y (θ_traj t)‖ ≤ R * Real.exp (-ν * t))
    (hJ : ∀ t : ℝ, 0 ≤ t → ‖outputJacobian (netFromParams φ n d) X (θ_traj t)‖ ≤ M)
    (hJ₀ : ‖outputJacobian (netFromParams φ n d) X θ₀‖ ≤ M)
    (hmom : (n : ℝ)⁻¹ * ∑ i : Fin n,
      neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) ≤ τ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
        empiricalNTKMatrix (netFromParams φ n d) X θ₀‖ ≤
      2 * M * (R / ((m : ℝ) * ν) * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ)) := by
  have hR : 0 ≤ R := by simpa using (norm_nonneg _).trans (hres 0 le_rfl)
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ₀
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hτ : 0 ≤ τ := le_trans (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
    neuronMoment_nonneg φ C₁ C₂ X _ _)) hmom
  set K₁ : ℝ := R / ((m : ℝ) * ν) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  -- per-neuron bound on `Λ_i² ρ_i²`
  have hneuron : ∀ i : Fin n, neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
      ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤
        K₁ ^ 2 * (2 * (n : ℝ)⁻¹ * (1 + C ^ 2)) *
          neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) := by
    intro i
    set Q := neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i) with hQ
    set Λ := neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) with hΛ
    have hQ0 : 0 ≤ Q := neuronJacobianScaleSq_nonneg _ _ _ _ _
    have hΛ0 : 0 ≤ Λ := neuronLipschitzScaleSq_nonneg _ _ _ _
    have hρ := neuron_displacement_le φ hφ hC₁0 hC₂0 hφ_lip hC₁ hderiv_lip hn hm X y hflow hν hdisp
      hres ht i
    set b := Real.sqrt (2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ))) with hb
    have hb2 : b ^ 2 = 2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ)) :=
      Real.sq_sqrt (by positivity)
    have hρ2 : ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤
        K₁ ^ 2 * (2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ))) := by
      calc _ ≤ ((m : ℝ)⁻¹ * b * R / ν) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hρ 2
        _ = K₁ ^ 2 * b ^ 2 := by rw [hK₁]; ring
        _ = _ := by rw [hb2]
    have hmomeq : neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) = Λ * (Q + Λ) := rfl
    rw [hmomeq]
    calc Λ * ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2
        ≤ Λ * (K₁ ^ 2 * (2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ)))) :=
          mul_le_mul_of_nonneg_left hρ2 hΛ0
      _ = K₁ ^ 2 * (2 * (n : ℝ)⁻¹) * (Λ * (Q + C ^ 2 * Λ)) := by ring
      _ ≤ K₁ ^ 2 * (2 * (n : ℝ)⁻¹) * ((1 + C ^ 2) * (Λ * (Q + Λ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [mul_nonneg hΛ0 hQ0, mul_nonneg hΛ0 hΛ0, sq_nonneg C,
            mul_nonneg (mul_nonneg hΛ0 hQ0) (sq_nonneg C),
            mul_nonneg (mul_nonneg hΛ0 hΛ0) (sq_nonneg C)]
      _ = _ := by ring
  have hJsq : ‖outputJacobian (netFromParams φ n d) X (θ_traj t) -
      outputJacobian (netFromParams φ n d) X θ₀‖ ^ 2 ≤
        (K₁ * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ)) ^ 2 := by
    refine (outputJacobian_sub_norm_sq_le_neuron_sum φ hφ hC₁0 hC₂0 hφ_lip hC₁ hderiv_lip X
      (θ_traj t) θ₀).trans ?_
    calc (n : ℝ)⁻¹ * ∑ i : Fin n, neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
          ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2
        ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, K₁ ^ 2 * (2 * (n : ℝ)⁻¹ * (1 + C ^ 2)) *
            neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hneuron i) (by positivity)
      _ = K₁ ^ 2 * (2 * (1 + C ^ 2)) * (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ i : Fin n,
            neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i)) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ K₁ ^ 2 * (2 * (1 + C ^ 2)) * (n : ℝ)⁻¹ * τ :=
          mul_le_mul_of_nonneg_left hmom (by positivity)
      _ = _ := by
          have hrhs : (K₁ * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ)) ^ 2 =
            K₁ ^ 2 * (2 * (1 + C ^ 2) * τ) / n := by
            rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hn'.le]
          rw [hrhs]
          field_simp
  have hJdiff : ‖outputJacobian (netFromParams φ n d) X (θ_traj t) -
      outputJacobian (netFromParams φ n d) X θ₀‖ ≤
        K₁ * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hJsq
  exact (empiricalNTKMatrix_sub_le_of_jacobian_bound _ X _ _ M (hJ t ht) hJ₀).trans
    (mul_le_mul_of_nonneg_left hJdiff (by positivity))


/-- `neuronMoment` is an explicit polynomial in `a` and the activation energy
`∑_α φ (w ⬝ᵥ x_α)²`. -/
private lemma neuronMoment_eq_poly (φ : ℝ → ℝ) (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ) :
    ∃ c₂ c₃ c₄ : ℝ, ∀ (w : Fin d → ℝ) (a : ℝ),
      neuronMoment φ C₁ C₂ X w a = (c₂ * a ^ 2 + c₃) *
        ((∑ α : Fin m, φ (w ⬝ᵥ X α) ^ 2) + c₄ * a ^ 2 + (c₂ * a ^ 2 + c₃)) := by
  refine ⟨∑ α : Fin m, 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2,
    ∑ α : Fin m, 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2,
    ∑ α : Fin m, C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2, fun w a => ?_⟩
  have hΛ : neuronLipschitzScaleSq C₁ C₂ X a =
      (∑ α : Fin m, 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2) * a ^ 2 +
        ∑ α : Fin m, 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2 := by
    simp only [neuronLipschitzScaleSq, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun α _ => by ring
  have hQ : neuronJacobianScaleSq φ C₁ X w a = (∑ α : Fin m, φ (w ⬝ᵥ X α) ^ 2) +
      (∑ α : Fin m, C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) * a ^ 2 := by
    simp only [neuronJacobianScaleSq, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [neuronMoment, hQ, hΛ]

lemma measurable_neuronMoment {φ : ℝ → ℝ} (hφ : Measurable φ) (C₁ C₂ : ℝ)
    (X : Fin m → Fin d → ℝ) :
    Measurable (fun q : (Fin d → ℝ) × ℝ => neuronMoment φ C₁ C₂ X q.1 q.2) := by
  obtain ⟨c₂, c₃, c₄, h⟩ := neuronMoment_eq_poly φ C₁ C₂ X (m := m) (d := d)
  simp_rw [h]
  have hG : Measurable (fun q : (Fin d → ℝ) × ℝ => ∑ α : Fin m, φ (q.1 ⬝ᵥ X α) ^ 2) :=
    Finset.measurable_sum _ fun α _ =>
      (hφ.comp ((measurable_dotProduct_left (X α)).comp measurable_fst)).pow_const 2
  have ha : Measurable (fun q : (Fin d → ℝ) × ℝ => q.2) := measurable_snd
  fun_prop

/-- The single-neuron moment is integrable under the Gaussian single-neuron law. -/
lemma integrable_neuronMoment {φ : ℝ → ℝ} (C₁ C₂ : ℝ)
    (X : Fin m → Fin d → ℝ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d =>
        gaussianReal 0 1)) :
    Integrable (fun q : (Fin d → ℝ) × ℝ => neuronMoment φ C₁ C₂ X q.1 q.2)
      ((Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  obtain ⟨c₂, c₃, c₄, h⟩ := neuronMoment_eq_poly φ C₁ C₂ X (m := m) (d := d)
  have hG : Integrable (fun w : Fin d → ℝ => ∑ α : Fin m, φ (w ⬝ᵥ X α) ^ 2)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := integrable_finsetSum _ fun α _ => (hL2
          α).integrable_sq
  have h2 := integrable_sq_gaussianReal
  have h4 := integrable_pow_four_gaussianReal
  have hu : Integrable (fun a : ℝ => c₂ * a ^ 2 + c₃) (gaussianReal 0 1) :=
    (h2.const_mul c₂).add (integrable_const c₃)
  have hv : Integrable (fun a : ℝ => (c₂ * a ^ 2 + c₃) * ((c₄ + c₂) * a ^ 2 + c₃))
      (gaussianReal 0 1) := by
    have : (fun a : ℝ => (c₂ * a ^ 2 + c₃) * ((c₄ + c₂) * a ^ 2 + c₃)) =
        fun a => c₂ * (c₄ + c₂) * a ^ 4 + (c₂ * c₃ + c₃ * (c₄ + c₂)) * a ^ 2 + c₃ * c₃ := by
      ext a; ring
    rw [this]
    exact ((h4.const_mul _).add (h2.const_mul _)).add (integrable_const _)
  have h1 := hG.mul_prod hu
  have h3 := (integrable_const (1 : ℝ) : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
    (Measure.pi fun _ : Fin d => gaussianReal 0 1)).mul_prod hv
  refine (h1.add h3).congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.add_apply, one_mul, h]
  ring


/-- **The neuron-moment average is bounded with high probability.** For every `δ > 0` there is a
width-independent threshold `τ` such that the empirical average `n⁻¹ ∑ᵢ neuronMoment (Wᵢ, aᵢ)` is at
most `τ` on a measurable initialization event of probability at least `1 - δ`, for every width. -/
theorem exists_neuronMoment_event {φ : ℝ → ℝ} (hφ : Measurable φ) (C₁ C₂ : ℝ)
    (X : Fin m → Fin d → ℝ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d =>
        gaussianReal 0 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ n : ℕ, 0 < n →
      MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ X (p.1 i) (p.2 i) ≤ τ} ∧
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)).real {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ X (p.1 i) (p.2 i) ≤ τ} ≥ 1 - δ := by
  set I : ℝ := ∫ q, neuronMoment φ C₁ C₂ X q.1 q.2 ∂((Measure.pi fun _ : Fin d =>
      gaussianReal 0 1).prod (gaussianReal 0 1))
    with hI
  have hI0 : 0 ≤ I := integral_nonneg fun q => neuronMoment_nonneg _ _ _ _ _ _
  refine ⟨I / δ + 1, by positivity, fun n hn => ⟨?_, ?_⟩⟩
  · exact measurableSet_le (Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      (measurable_neuronMoment hφ C₁ C₂ X).comp
        (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))) _) measurable_const
  · refine measureReal_initMeasure_neuronAverage_le hn (measurable_neuronMoment hφ C₁ C₂ X)
      (integrable_neuronMoment C₁ C₂ X hL2) (fun q => neuronMoment_nonneg _ _ _ _ _ _)
      (by positivity) ?_
    rw [add_mul, div_mul_cancel₀ _ hδ.ne']
    linarith

end SharpKernelDrift

end

end NTK
