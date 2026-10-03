/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.KernelDrift

/-!
# Training limits of the two-layer network: initialization events

Framework for the infinite-width training limits of the two-layer network with trainable input
weights `W` and readout weights `a`. This file contains `SmoothActivation`, the deterministic
feasibility of the bootstrap constants, and the good events at initialization for the finite-horizon
and the global positive-gap theorems (Phases 6.3, 8, 9).

## Main results and proof outline

* `InitializationEvents` : `SmoothActivation`, bootstrap constants, good events (Phases 6.3, 8, 9).
- `SmoothActivation` : bundled activation hypotheses (differentiable, bounded derivative,
  Lipschitz derivative; no bound on the value of `φ`) shared by the paper-facing theorems below.
- `exists_finite_horizon_kernel_freeze_event` : the no-gap counterpart on `[0, T]` with failure
  probability `≤ 2δ + ε`; positive semidefiniteness alone bounds the residual and the
  displacement radius `C = T M R / m` grows linearly in `T`.
- `exists_measurableSet_global_lazy_training_event`, `global_positive_gap_lazy_training_limit` :
  Under a positive limiting gap, uniform Rayleigh gap `λ_∞ / 4`, kernel drift
  `O(√(log n / n))`, exponential residual and loss decay and `mseLoss → 0`, with probability
  `≥ 1 - η`.
- `exists_kernel_freeze_event_of_positive_gap` : Under a positive limiting gap,
  a deterministic sequence `K n → 0` such that, with probability `≥ 1 - 2δ - 2ε` for all large `n`,
  every gradient flow keeps the empirical NTK within `K n` of its initial value for all `t ≥ 0`;
  all bootstrap constants are chosen explicitly.

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

/-! ### Training Limits of Trainable Two-Layer Networks

This section establishes the framework and target specifications for the infinite-width
training limits of the full two-layer neural network with trainable input weights `W` and
trainable readout weights `a`.

Following the roadmap in `docs/NTK_full_formalization_plan.md`:
- `FiniteHorizonLimit`: states the finite-horizon lazy training theorem on `[0, T]` for any
  fixed `T ≥ 0`, establishing kernel stationarity and weak convergence of predictions without
  requiring a strictly positive limiting spectral gap.
- `GlobalPositiveGapLimit`: states the global lazy training theorem under a positive limiting
  spectral gap `λ_min(K_∞) > 0`, establishing uniform-in-time kernel control and exponential
  residual / loss decay with high probability.
-/


section InitializationEvents

/-! #### Deterministic feasibility of the bootstrap constants

The Jacobian-Lipschitz scale `L_J` evaluated at a *fixed* displacement radius `r` is
`sqrt (∑ α, (a α * (√(2 log (2n / δ)) + r) ^ 2 + b α)) / √n`, which vanishes as the width `n → ∞`.
This is what makes the bootstrap feasibility inequalities hold eventually in `n`. -/

open Filter Topology in
private theorem tendsto_sq_sqrt_two_log_add_div_nat {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Tendsto (fun n : ℕ => (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 / n) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => 2 * (n : ℝ) / δ) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < 2 / δ)).congr
      fun n => by ring
  have hlog : Tendsto (fun n : ℕ => Real.log (2 * n / δ) / n) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
    have h2 := h.const_mul (2 / δ)
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Function.comp, pow_one, add_zero, one_mul]
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hbound : Tendsto (fun n : ℕ => 4 * (Real.log (2 * n / δ) / n) + 2 * r ^ 2 * (1 / (n : ℝ)))
      atTop (𝓝 0) := by
    have h1 := hlog.const_mul 4
    have h2 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * r ^ 2)
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hbound
  filter_upwards [eventually_ge_atTop (max 1 ⌈δ / 2⌉₊)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hδn : δ / 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have h1 : 1 ≤ 2 * (n : ℝ) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hlogn : 0 ≤ Real.log (2 * n / δ) := Real.log_nonneg h1
  have hsq : Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 = 2 * Real.log (2 * n / δ) :=
    Real.sq_sqrt (by positivity)
  have key : (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 ≤
      4 * Real.log (2 * n / δ) + 2 * r ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (2 * Real.log (2 * n / δ)) - r)]
  calc (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 / n
      ≤ (4 * Real.log (2 * n / δ) + 2 * r ^ 2) / n := by gcongr
    _ = 4 * (Real.log (2 * n / δ) / n) + 2 * r ^ 2 * (1 / (n : ℝ)) := by field_simp

open Filter Topology in
private theorem tendsto_sqrt_sum_sq_sqrt_two_log_add_div_sqrt_nat {ι : Type*} [Fintype ι]
    (a b : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Tendsto (fun n : ℕ =>
      Real.sqrt (∑ i, (a i * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 + b i))
      / Real.sqrt n) atTop (𝓝 0) := by
  have hu := tendsto_sq_sqrt_two_log_add_div_nat hδ r
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum : Tendsto (fun n : ℕ => ∑ i, (a i * ((Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 / n)
      + b i * (1 / (n : ℝ)))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
      ((hu.const_mul (a i)).add (hinv.const_mul (b i)))
    simpa using this
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsum
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp]
  rw [← Real.sqrt_div' _ hn0.le, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- Regularity consequences of the global derivative bounds on the activation: `C₁, C₂ ≥ 0`, the
first-derivative Lipschitz bound `|φ u - φ v| ≤ C₁ |u - v|`, and measurability of `deriv φ`. -/
lemma activation_regularity_of_bounds (φ : ℝ → ℝ) (C₁ C₂ : ℝ)
    (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hφ : Differentiable ℝ φ) :
    0 ≤ C₁ ∧ 0 ≤ C₂ ∧ (∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) ∧ Measurable (deriv φ) := by
  refine ⟨(abs_nonneg _).trans (hC₁_bdd 0), by simpa using (abs_nonneg _).trans (hderiv_lip 1 0),
    fun u v => ?_, (LipschitzWith.of_dist_le' (K := C₂) fun x y => by
      simpa [Real.dist_eq] using hderiv_lip x y).continuous.measurable⟩
  simpa [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hφ x) (fun x _ => by simpa [Real.norm_eq_abs] using hC₁_bdd x) convex_univ
    (Set.mem_univ v) (Set.mem_univ u)

/-- A bounded measurable function of a Gaussian-row preactivation is in `L²`. -/
private lemma memLp_two_gaussianRow_comp_of_bounded {d : ℕ} (g : ℝ → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (x : Fin d → ℝ) :
    MemLp (fun w => g (w ⬝ᵥ x)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
  MemLp.of_bound (hg.comp (measurable_dotProduct_left x)).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hB _)

/-- A product of two bounded measurable functions of Gaussian-row preactivations is in `L²`. -/
private lemma memLp_two_gaussianRow_mul_comp_of_bounded {d : ℕ} (g : ℝ → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (x x' : Fin d → ℝ) :
    MemLp (fun w => g (w ⬝ᵥ x) * g (w ⬝ᵥ x')) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
  MemLp.of_bound ((hg.comp (measurable_dotProduct_left x)).mul
    (hg.comp (measurable_dotProduct_left x'))).aestronglyMeasurable (B * B)
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB _) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hB 0)))

open Filter Topology in
/-- The Jacobian-Lipschitz scale at a *fixed* displacement radius `r` vanishes as the width
`n → ∞`. This makes the bootstrap feasibility inequalities hold eventually in `n`. -/
lemma tendsto_jacobianLipschitzScale {d m : ℕ} (X : Fin m → Fin d → ℝ) (C₁ C₂ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  refine (tendsto_sqrt_sum_sq_sqrt_two_log_add_div_sqrt_nat
    (fun α => 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2)
    (fun α => 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) hδ r).congr fun n => ?_
  congr 3
  ext α
  ring

open Filter Topology in
/-- The Jacobian-Lipschitz scale at a fixed radius is `O(√(log n / n))`: this is the rate at
which the bootstrap kernel drift vanishes. -/
private lemma jacobianLipschitzScale_le_sqrt_log_div {d m : ℕ} (X : Fin m → Fin d → ℝ)
    (C₁ C₂ : ℝ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤
      A * Real.sqrt (Real.log n / n) := by
  set K1 : ℝ := 4 + 4 * |Real.log (2 / δ)| + 2 * r ^ 2 with hK1
  set B : ℝ := ∑ α : Fin m, (2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 * K1 +
    3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)) with hB
  have hK1_nonneg : 0 ≤ K1 := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlog, eventually_ge_atTop ⌈δ / 2⌉₊, eventually_gt_atTop 0] with n hn hnδ hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hδn : δ / 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
  have h1 : 1 ≤ 2 * (n : ℝ) / δ := by rw [le_div_iff₀ hδ]; linarith
  have hL_nonneg : 0 ≤ Real.log (2 * n / δ) := Real.log_nonneg h1
  have hLsplit : Real.log (2 * n / δ) = Real.log (2 / δ) + Real.log n := by
    rw [show 2 * (n : ℝ) / δ = 2 / δ * n by ring, Real.log_mul (by positivity) hn0'.ne']
  have hsq : Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 = 2 * Real.log (2 * n / δ) :=
    Real.sq_sqrt (by positivity)
  have hkey : (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 ≤ K1 * Real.log n := by
    have h2 : (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 ≤
        4 * Real.log (2 * n / δ) + 2 * r ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (2 * Real.log (2 * n / δ)) - r)]
    have h3 : Real.log (2 / δ) ≤ |Real.log (2 / δ)| * Real.log n :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hn)
    nlinarith [sq_nonneg r]
  have hterm : ∀ α : Fin m, 2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2) ≤
      (2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 * K1 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)) * Real.log n := by
    intro α
    have hb : 0 ≤ 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2) := by positivity
    have hcoef : 0 ≤ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkey hcoef, mul_le_mul_of_nonneg_left hn hb]
  have hS : ∑ α : Fin m, (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)) ≤
      B * Real.log n := by
    rw [hB, Finset.sum_mul]
    exact Finset.sum_le_sum fun α _ => hterm α
  calc Real.sqrt (∑ α : Fin m, (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) /
        Real.sqrt (n : ℝ) ≤ Real.sqrt (B * Real.log n) / Real.sqrt (n : ℝ) := by
        gcongr
    _ = Real.sqrt B * Real.sqrt (Real.log n / n) := by
        rw [Real.sqrt_mul hB_nonneg, Real.sqrt_div' _ hn0'.le, mul_div_assoc]

/-- **Smooth activation.** The bundled activation hypotheses shared by the paper-facing theorems:
`φ` is differentiable with bounded derivative (`C₁`) and `C₂`-Lipschitz derivative. No bound on the
value of `φ` is assumed: a bounded derivative already gives linear growth
`|φ z| ≤ |φ 0| + C₁ |z|` (`activation_growth`), which is all that Gaussian initialization needs.
Every consequence used by the proofs (`C₁, C₂ ≥ 0`, Lipschitzness of `φ`, measurability of
`deriv φ`, `L²` integrability against Gaussians) is derived from these three facts. Lower-level
deterministic lemmas keep taking the unbundled hypotheses they use; the forward gradient-flow
construction (`exists_forwardGradientFlow`) needs nothing beyond this structure. -/
structure SmoothActivation (φ : ℝ → ℝ) (C₁ C₂ : ℝ) : Prop where
  differentiable : Differentiable ℝ φ
  deriv_bdd : ∀ z, |deriv φ z| ≤ C₁
  deriv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|

/-- A bounded derivative gives linear growth of the activation. -/
private lemma activation_growth {φ : ℝ → ℝ} {C₁ C₂ : ℝ} (hact : SmoothActivation φ C₁ C₂) :
    ∀ z, |φ z| ≤ |φ 0| + C₁ * |z| := fun z => by
  obtain ⟨-, -, hφlip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have := hφlip z 0
  rw [sub_zero] at this
  calc |φ z| = |φ z - φ 0 + φ 0| := by ring_nf
    _ ≤ |φ z - φ 0| + |φ 0| := abs_add_le _ _
    _ ≤ |φ 0| + C₁ * |z| := by linarith

/-- Gaussian second moments of the activation and of its derivative along rows, derived from the
bounded derivative alone: `φ` has linear growth and `deriv φ` is bounded. -/
lemma activation_memLp_two {φ : ℝ → ℝ} {C₁ C₂ : ℝ} (hact : SmoothActivation φ C₁ C₂)
    {d : ℕ} :
    (∀ x : Fin d → ℝ, MemLp (fun w => φ (w ⬝ᵥ x)) 2 (Measure.pi fun _ : Fin d =>
        gaussianReal 0 1)) ∧
    (∀ x x' : Fin d → ℝ,
      MemLp (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) ∧
    (∀ x : Fin d → ℝ, MemLp (fun w => deriv φ (w ⬝ᵥ x)) 2 (Measure.pi fun _ : Fin d => gaussianReal
        0 1)) ∧
    (∀ x x' : Fin d → ℝ,
      MemLp (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) 2 (Measure.pi fun _ : Fin d =>
          gaussianReal 0 1)) := by
  obtain ⟨hC₁0, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hmeas : Measurable φ := hact.differentiable.continuous.measurable
  have hA : 0 ≤ |φ 0| := abs_nonneg _
  have h1 : ∀ x : Fin d → ℝ, MemLp (fun w => φ (w ⬝ᵥ x)) 2 (Measure.pi fun _ : Fin d => gaussianReal
      0 1) := fun x => by
    simpa using memLp_gaussianRow_comp_of_linear_growth φ hmeas hA hC₁0
      (activation_growth hact) x 2
  exact ⟨h1, fun x x' => memLp_two_gaussianRow_mul_comp_of_linear_growth φ hmeas hA hC₁0
      (activation_growth hact) x x',
    fun x => memLp_two_gaussianRow_comp_of_bounded (deriv φ) hderiv_meas hact.deriv_bdd x,
    fun x x' => memLp_two_gaussianRow_mul_comp_of_bounded (deriv φ) hderiv_meas hact.deriv_bdd x
      x'⟩

lemma activation_locallyLipschitz {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) :
    LocallyLipschitz φ ∧ LocallyLipschitz (deriv φ) := by
  obtain ⟨hφ, hC₁, hderiv_lip⟩ := hact
  obtain ⟨-, -, hφlip, -⟩ := activation_regularity_of_bounds φ _ _ hC₁ hderiv_lip hφ
  exact ⟨(LipschitzWith.of_dist_le' (K := C₁) fun x y => by
      simpa [Real.dist_eq] using hφlip x y).locallyLipschitz,
    (LipschitzWith.of_dist_le' (K := C₂) fun x y => by
      simpa [Real.dist_eq] using hderiv_lip x y).locallyLipschitz⟩

/-- **Jacobian and readout good events for a smooth activation.** For every `δ ∈ (0, 1]` there is a
constant `M₀` (independent of the width) such that, for every width `n ≥ 1`, there is a measurable
event of `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-probability `≥ 1 - 2 δ` on which the initial output Jacobian has
Frobenius norm at most `M₀` and every readout weight is at most `√(2 log (2 n / δ))`. The Jacobian
bound uses only the bounded derivative
(`outputJacobian_netFromParams_frobenius_norm_concentration_of_L2`), not a bound on `φ`. -/
private lemma exists_jacobian_bound_and_good_events {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) {d m : ℕ} (X : Fin m → Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ n : ℕ, 0 < n →
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)),
        MeasurableSet E ∧ ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
            gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - 2 *
                δ ∧
        ∀ p ∈ E,
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ M₀ ∧
          ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) := by
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hL2 := (activation_memLp_two hact (d := d)).1
  refine ⟨Real.sqrt (2 * ((∑ α : Fin m, ∫ w, φ (w ⬝ᵥ X α) ^ 2 ∂(Measure.pi fun _ : Fin d =>
      gaussianReal 0 1)) + 1 +
      C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ), Real.sqrt_nonneg _, fun n hn => ?_⟩
  exact exists_measurableSet_initial_jacobian_and_readout_bounds φ n d m hn X hact.differentiable
    hact.differentiable.continuous.measurable hderiv_meas hδ hδ1 _
    (outputJacobian_netFromParams_frobenius_norm_concentration_of_L2 φ n d m hn X C₁ hact.deriv_bdd
      hact.differentiable (fun α => hL2 (X α)) hδ hδ1)

/-- **Global lazy-training event with an extra good event and a bootstrap certificate.** This is the
proof of `exists_measurableSet_global_lazy_training_event` with two additions: the good event may be
intersected with any measurable family `Extra n` of probability at least `1 - κ`, and the bootstrap
constants `C` (displacement radius), `M` (Jacobian bound) and `R` (initial residual bound) are
exposed together with the corresponding bounds along every gradient flow. They feed the sharper
average-moment drift estimate `kernel_drift_le_of_neuron_moments`. -/
theorem exists_measurableSet_global_lazy_training_event_with_extra
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (Extra : ∀ n : ℕ, Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)))
    (hExtra_meas : ∀ n, 0 < n → MeasurableSet (Extra n)) {κ : ℝ}
    (hExtra : ∀ n, 0 < n → ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real (Extra n) ≥ 1 -
            κ) :
    ∃ (freezeRate jacRate taylorRate : ℕ → ℝ) (N : ℕ) (C M R : ℝ),
      Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto jacRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto taylorRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
      0 ≤ C ∧ 0 ≤ M ∧ 0 ≤ R ∧ ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
            fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - 2 * δ - 2 * ε - κ ∧ ∀ p ∈ E,
                p ∈ Extra n ∧
          ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤ M ∧
          (∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ((∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ_traj t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)) Filter.atTop (nhds 0)) ∧
            ∀ t : ℝ, 0 ≤ t → ‖θ_traj t - packParams p.1 p.2‖ ≤ C ∧
              ‖outputJacobian (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)‖ ≤ M ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                R * Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              ‖outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                jacRate n ∧
              ‖trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) -
                WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ
                    (θ_traj t - packParams p.1 p.2).ofLp)‖ ≤ taylorRate n) ∧
          ∀ i : Fin n, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) := by
  have hφ := hact.differentiable
  have hC₁_bdd := hact.deriv_bdd
  have hderiv_lip := hact.deriv_lip
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  -- Consequences of the global derivative bounds, so callers need not supply them.
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  -- `L²` integrability of the activation-side observables (from linear growth).
  obtain ⟨hL2, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ Xs α)) 2 (Measure.pi fun _ : Fin d =>
      gaussianReal 0 1) :=
    fun α => hL2 (Xs α)
  have hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⬝ᵥ Xs α) * φ (w ⬝ᵥ Xs β)) 2 (Measure.pi fun _ : Fin d =>
          gaussianReal 0 1) :=
    fun α β => hL2mul (Xs α) (Xs β)
  have hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⬝ᵥ Xs α) * deriv φ (w ⬝ᵥ Xs β)) 2 (Measure.pi fun _ : Fin d =>
          gaussianReal 0 1) :=
    fun α β => hdL2mul (Xs α) (Xs β)
  -- Initial residual radius and initial spectral-gap failure.
  obtain ⟨R, hR_nonneg, hR⟩ := exists_initial_residual_radius φ X y hmeasφ hφ_out_L2
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hU_ev := (tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X
    hφ_L2 hdφ_L2 (half_pos hlambda_inf)).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  -- Deterministic bootstrap constants.
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_jacobian_bound_and_good_events hact Xs hδ hδ1
  set M : ℝ := M₀ + 1 with hM
  set C : ℝ := M * R / (lambda_inf / 2 / 2) with hC
  set r : ℝ := C + 1 with hr
  set ℓ : ℕ → ℝ := fun n => Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, Xs α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, Xs α j ^ 2))) / Real.sqrt (n : ℝ) with hℓ_def
  have hM_pos : 0 < M := by positivity
  have hℓ_nonneg : ∀ n, 0 ≤ ℓ n := fun n => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hℓ : Filter.Tendsto ℓ Filter.atTop (nhds 0) :=
    tendsto_jacobianLipschitzScale Xs C₁ C₂ hδ r
  have hrate : Filter.Tendsto (fun n => 2 * M * ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using (hℓ.const_mul (2 * M)).mul_const C
  have hjac : Filter.Tendsto (fun n => ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using hℓ.mul_const C
  have htay : Filter.Tendsto (fun n => ℓ n * C ^ 2 / 2) Filter.atTop (nhds 0) := by
    simpa using (hℓ.mul_const (C ^ 2)).div_const 2
  have hc : 0 < min 1 (lambda_inf / (8 * M)) := lt_min one_pos (by positivity)
  have hsmall : ∀ᶠ n in Filter.atTop, ℓ n * r < min 1 (lambda_inf / (8 * M)) := by
    exact (hℓ.mul_const r).eventually (gt_mem_nhds (by rw [zero_mul]; exact hc))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_gt_atTop 0).and (hsmall.and hU_ev))
  obtain ⟨A, hA, hAev⟩ := jacobianLipschitzScale_le_sqrt_log_div Xs C₁ C₂ hδ r
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hAev
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨fun n => 2 * M * ℓ n * C, fun n => ℓ n * C, fun n => ℓ n * C ^ 2 / 2, max N N₂, C, M, R,
    hrate, hjac, htay, ⟨2 * M * A * C, by positivity, fun n hn => ?_⟩, hC0, hM_pos.le, hR_nonneg,
    fun n hn => ?_⟩
  · calc 2 * M * ℓ n * C ≤ 2 * M * (A * Real.sqrt (Real.log n / n)) * C := by
          gcongr; exact hN₂ n ((le_max_right _ _).trans hn)
      _ = 2 * M * A * C * Real.sqrt (Real.log n / n) := by ring
  obtain ⟨hn0, hsm, hU⟩ := hN n ((le_max_left _ _).trans hn)
  obtain ⟨E, hEm, hEμ, hEp⟩ := hM₀ n hn0
  set U : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | lambda_inf / 2 ≤
    ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) -
      limitingFullNTKMatrix φ X‖} with hUdef
  set T : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | R <
    ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖} with hTdef
  have hUm : MeasurableSet U :=
    measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas Xs (limitingFullNTKMatrix φ X) _
  have hres_meas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)) := by
    simp_rw [trainingResidual_netFromParams_packParams]
    exact (evalVector_joint_measurable φ hmeasφ Xs).sub_const y
  have hTm : MeasurableSet T := measurableSet_lt measurable_const hres_meas.norm
  have hUr : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)).real U ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le hU.le
  have hTr : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)).real T ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le (hR n)
  have hEc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ ≤ 2 * δ := by
    rw [probReal_compl_eq_one_sub hEm]; linarith
  -- Union bound on the complement of `G = E ∩ Uᶜ ∩ Tᶜ`.
  have hG3c : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real (E ∩ Uᶜ ∩ Tᶜ)ᶜ ≤ 2 * δ + ε + ε :=
    calc ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real (E ∩ Uᶜ ∩ Tᶜ)ᶜ
        ≤ ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real (E ∩ Uᶜ)ᶜ + ((Measure.pi fun _ :
            Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
                gaussianReal 0 1)).real Tᶜᶜ :=
          measureReal_compl_inter_le _ _ _
      _ ≤ (((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ + ((Measure.pi fun _ : Fin n =>
          Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
              gaussianReal 0 1)).real Uᶜᶜ) +
            ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
                (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Tᶜᶜ := by
          gcongr; exact measureReal_compl_inter_le _ _ _
      _ ≤ 2 * δ + ε + ε := by rw [compl_compl, compl_compl]; linarith
  have hXc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real (Extra n)ᶜ ≤ κ := by
    rw [probReal_compl_eq_one_sub (hExtra_meas n hn0)]; linarith [hExtra n hn0]
  have hGc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real ((E ∩ Uᶜ ∩
      Tᶜ) ∩ Extra n)ᶜ ≤ 2 * δ + ε + ε + κ :=
    (measureReal_compl_inter_le _ _ _).trans (add_le_add hG3c hXc)
  refine ⟨(E ∩ Uᶜ ∩ Tᶜ) ∩ Extra n, ((hEm.inter hUm.compl).inter hTm.compl).inter
    (hExtra_meas n hn0),
    by linarith [one_sub_le_measureReal_of_measureReal_compl_le _ hGc], ?_⟩
  rintro p ⟨⟨⟨hpE, hpU⟩, hpT⟩, hpX⟩
  obtain ⟨hp1, hp2⟩ := hEp p hpE
  have hrr : ∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 2) * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) *ᵥ v.ofLp) :=
    fun v => initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le φ X n p lambda_inf
      hK_gap (not_le.1 (show ¬ (lambda_inf / 2 ≤ _) from hpU)).le v
  have hres : ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖ ≤ R :=
    not_lt.1 (show ¬ (R < _) from hpT)
  have hM_ge : M₀ + ℓ n * r ≤ M := by linarith [hsm.le.trans (min_le_left _ _)]
  have hr_nonneg : 0 ≤ r := by positivity
  obtain ⟨hJ_bdd_ball, hJ_lip_ball⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn0 Xs C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ M₀ p hp1 hp2 r (ℓ n) M hr_nonneg
    (hℓ_nonneg n) hM_ge le_rfl
  refine ⟨hpX, hJ_bdd_ball _ (by simpa using hr_nonneg), fun θ_traj hflow => ?_, hp2⟩
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (Xs β) θ') (θ_traj t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (Xs β) (θ_traj t)
      fun i => hφ.differentiableAt).differentiableAt
  have hg := lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds φ n d m hn0 Xs y
    C₁ C₂ hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ (Nat.cast_pos.2 hm) M₀ p hp1 hp2
    θ_traj (lambda_inf / 2) r C M (ℓ n) hflow hdiff (half_pos hlambda_inf) (by positivity)
    (lt_add_one C) hM_pos.le (hℓ_nonneg n) hrr
    hM_ge le_rfl
    (by
      calc 2 * M * ℓ n * r = 2 * M * (ℓ n * r) := by ring
        _ ≤ 2 * M * (lambda_inf / (8 * M)) :=
          mul_le_mul_of_nonneg_left (hsm.le.trans (min_le_right _ _)) (by positivity)
        _ = lambda_inf / 2 / 2 := by field_simp; ring)
    (by
      calc M * ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖ /
            (lambda_inf / 2 / 2) ≤ M * R / (lambda_inf / 2 / 2) := by gcongr
        _ = C := rfl)
  have hloss_decay : ∀ t : ℝ, 0 ≤ t → mseLoss (netFromParams φ n d) Xs y (θ_traj t) ≤
      mseLoss (netFromParams φ n d) Xs y (packParams p.1 p.2) *
        Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t) := fun t ht => by
    have h := (hg t ht).2.2.2.2
    rwa [show -(2 * (lambda_inf / 2 / 2) / (m : ℝ)) * t = -(lambda_inf / (2 * (m : ℝ))) * t by
      ring] at h
  refine ⟨⟨fun t ht => ?_, tendsto_zero_of_le_mul_exp_neg (by positivity)
    (fun t _ => by unfold mseLoss; positivity) hloss_decay⟩, fun t ht => ?_⟩
  · obtain ⟨-, hray, hdrift, hres_d, -⟩ := hg t ht
    refine ⟨fun v => ?_, hdrift, ?_, hloss_decay t ht⟩
    · have := hray v
      rwa [show lambda_inf / 2 / 2 = lambda_inf / 4 by ring] at this
    · rwa [show -(lambda_inf / 2 / 2 / (m : ℝ)) * t = -(lambda_inf / (4 * (m : ℝ))) * t by ring]
        at hres_d
  · obtain ⟨hdisp, -, -, hres_d, -⟩ := hg t ht
    have hball : ‖θ_traj t - packParams p.1 p.2‖ ≤ r := hdisp.trans (lt_add_one C).le
    refine ⟨hdisp, hJ_bdd_ball _ hball, ?_,
      (hJ_lip_ball _ hball).trans (mul_le_mul_of_nonneg_left hdisp (hℓ_nonneg n)),
      (norm_trainingOutputs_sub_linearization_le (netFromParams φ n d) Xs (packParams p.1 p.2) r
        (ℓ n) (fun z _ β => (hasFDerivAt_netFromParams φ n d (Xs β) z
          fun i => hφ.differentiableAt).differentiableAt) hJ_lip_ball hball).trans ?_⟩
    · rw [show -(lambda_inf / (4 * (m : ℝ))) * t = -(lambda_inf / 2 / 2 / (m : ℝ)) * t by ring]
      exact hres_d.trans (mul_le_mul_of_nonneg_right hres (Real.exp_nonneg _))
    · calc ℓ n / 2 * ‖θ_traj t - packParams p.1 p.2‖ ^ 2 ≤ ℓ n / 2 * C ^ 2 := by gcongr
        _ = ℓ n * C ^ 2 / 2 := by ring

/-- **Measurable good event for global positive-gap lazy training, with all bootstrap constants
discharged.** Assume a
`SmoothActivation` (differentiable, bounded derivative, Lipschitz derivative; no bound on the
value of `φ`), and that the limiting kernel satisfies `K_∞ ≥ lambda_inf • 1` with
`lambda_inf > 0`. For every `δ ∈ (0, 1]` and `ε > 0` there are a deterministic sequence
`freezeRate n → 0` and a width `N` such that for every `n ≥ N`,
there is a *measurable* event `E` of `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-probability at least `1 - 2 * δ - 2
* ε`
such that from every initialization in `E`, every gradient flow started at `θ₀ = packParams W a`
satisfies, for all `t ≥ 0`:

* the empirical NTK has Rayleigh quotient at least `lambda_inf / 4`, i.e. a uniform spectral gap
  (the initial half-gap `lambda_inf / 2` is halved once more inside the bootstrap ball);
* the kernel drift is at most `freezeRate n`;
* the residual norm and the MSE loss decay exponentially, at rates `lambda_inf / (4 m)` and
  `lambda_inf / (2 m)`;

and the training loss tends to `0` as `t → ∞`.

No hypothesis is shaped like the conclusion: the four failure probabilities (Jacobian norm,
maximum readout weight, initial spectral gap, initial residual size) are allocated explicitly, the
residual radius comes from output tightness (`exists_initial_residual_radius`), and the
feasibility inequalities of the deterministic bootstrap hold eventually in `n` because the
Jacobian-Lipschitz scale at a fixed radius vanishes with the width. As for the other event
theorems, this is an a priori estimate for any `ForwardGFTrajectory`. -/
theorem exists_measurableSet_global_lazy_training_event
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
            fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - 2 * δ - 2 * ε ∧ ∀ p ∈ E,
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ_traj t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)) Filter.atTop (nhds 0) := by
  obtain ⟨freezeRate, _, _, N, C, M, R, hrate, -, -, hK₀, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap hδ hδ1 hε (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ) (κ := 0)
      (fun n _ => by simp)
  refine ⟨freezeRate, N, hrate, hK₀, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, by linarith, fun p hp θ_traj hflow => ((hEp p hp).2.2.1 θ_traj hflow).1⟩

/-- **Global lazy training with kernel drift `O(n⁻¹ᐟ²)`.** Under the hypotheses of
`exists_measurableSet_global_lazy_training_event`, with the same conclusions, the drift rate obeys
`freezeRate n ≤ K₀ / √n` (no logarithm) on a measurable event of probability at least
`1 - 3 δ - 2 ε`. The extra `δ` pays for the Markov bound on the empirical neuron moment
(`exists_neuronMoment_event`); the deterministic estimate is
`kernel_drift_le_of_neuron_moments`. The logarithmic theorem is kept because its event does not need
the fourth-moment observable. -/
theorem exists_measurableSet_global_lazy_training_event_inv_sqrt_width
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ / Real.sqrt (n : ℝ)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
            fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - 3 * δ - 2 * ε ∧ ∀ p ∈ E,
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ_traj t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)) Filter.atTop (nhds 0) := by
  have hφ := hact.differentiable
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, -⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd hact.deriv_lip hφ
  obtain ⟨hL2, -, -, -⟩ := activation_memLp_two hact (d := d)
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  obtain ⟨τ, hτ, hτev⟩ := exists_neuronMoment_event hφ.continuous.measurable C₁ C₂ Xs
    (fun α => hL2 (Xs α)) hδ
  obtain ⟨freezeRate, _, _, N, C, M, R, hrate, -, -, -, hC, hM, hR, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap hδ hδ1 hε
      (fun n => {p | (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ Xs (p.1 i) (p.2 i) ≤ τ})
      (fun n hn => (hτev n hn).1) (κ := δ) (fun n hn => (hτev n hn).2)
  have hν : 0 < lambda_inf / (4 * (m : ℝ)) := by positivity
  set K : ℝ := 2 * M * (R / ((m : ℝ) * (lambda_inf / (4 * (m : ℝ)))) *
    Real.sqrt (2 * (1 + C ^ 2) * τ)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨fun n => min (freezeRate n) (K / Real.sqrt (n : ℝ)), max N 1, ?_, ⟨K, hK0,
    fun n _ => min_le_right _ _⟩, fun n hn => ?_⟩
  · simpa using hrate.min (tendsto_const_div_sqrt_nat_atTop K)
  obtain ⟨E, hEm, hE, hEp⟩ := h n ((le_max_left _ _).trans hn)
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)
  refine ⟨E, hEm, by linarith, fun p hp θ_traj hflow => ?_⟩
  obtain ⟨hpX, hJ0, hall, -⟩ := hEp p hp
  obtain ⟨⟨horig, htend⟩, hcert⟩ := hall θ_traj hflow
  refine ⟨fun t ht => ?_, htend⟩
  obtain ⟨hray, hdrift, hres, hloss⟩ := horig t ht
  refine ⟨hray, le_min hdrift ?_, hres, hloss⟩
  have hmom : (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ Xs
      (unpackW (packParams p.1 p.2) i) (unpackA (packParams p.1 p.2) i) ≤ τ := by
    simpa [unpackW_packParams, unpackA_packParams] using hpX
  have hsharp := kernel_drift_le_of_neuron_moments φ hφ hC₁_nonneg hC₂_nonneg hφ_lip
    hact.deriv_bdd hact.deriv_lip hn0 hm Xs y hflow hν (fun t ht => (hcert t ht).1)
    (fun t ht => (hcert t ht).2.2.1) (fun t ht => (hcert t ht).2.1) hJ0 hmom ht
  refine hsharp.trans (le_of_eq ?_)
  rw [hK]; ring

/-- **Kernel freeze on `[0, ∞)` from a positive limiting gap.** The kernel-drift component of
`exists_measurableSet_global_lazy_training_event`: with probability at least
`1 - 2 * δ - 2 * ε` every gradient flow keeps the empirical NTK within `freezeRate n → 0` of its
initial value for all `t ≥ 0`. -/
theorem exists_kernel_freeze_event_of_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t : ℝ, 0 ≤ t →
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤ freezeRate n} ≥
        1 - 2 * δ - 2 * ε := by
  obtain ⟨freezeRate, N, hrate, -, h⟩ := exists_measurableSet_global_lazy_training_event hm hd φ
    hact X y lambda_inf hlambda_inf hK_gap hδ hδ1 hε
  refine ⟨freezeRate, N, hrate, fun n hn => ?_⟩
  obtain ⟨E, -, hE, hEp⟩ := h n hn
  exact hE.trans (measureReal_mono fun p hp θ_traj hflow t ht =>
    ((hEp p hp θ_traj hflow).1 t ht).2.1)

/-- **Global positive-gap lazy training limit (paper-facing form).** Let `θ n p` be trajectories
that solve the gradient-flow ODE for `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-almost every initialization, and
assume the
limiting kernel satisfies `K_∞ ≥ lambda_inf • 1`, `lambda_inf > 0`. For every confidence
`η ∈ (0, 1]` there are a drift rate `freezeRate n → 0`, with
`freezeRate n ≤ K₀ √(log n / n)` (the logarithm comes from the maximum readout weight), and a width
`N` such that for `n ≥ N` there is a *measurable* initialization event `E` of probability at least
`1 - η` on which, for almost every initialization, and all `t ≥ 0`: the empirical NTK has Rayleigh
quotient at least `lambda_inf / 4`, it stays within `freezeRate n` of `K_n(0)`, and the residual
norm and MSE loss decay exponentially; moreover the loss tends to `0` as `t → ∞`.

The exact limiting trajectory and the fixed-time weak limits are the separate theorems
`tendstoInDistribution_trainingResidual_matrix_exp` and
`tendstoInDistribution_trainingOutputs_matrix_exp`. -/
theorem global_positive_gap_lazy_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
            fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - η ∧ ∀ᵐ p ∂((Measure.pi fun _ : Fin n =>
                Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
                gaussianReal 0 1)), p ∈ E →
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
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0) := by
  obtain ⟨freezeRate, N, hrate, hK₀, h⟩ := exists_measurableSet_global_lazy_training_event hm hd
    φ hact X y lambda_inf hlambda_inf hK_gap (δ := η / 4) (ε := η / 4) (by positivity)
    (by linarith) (by positivity)
  refine ⟨freezeRate, N, hrate, hK₀, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, le_of_eq_of_le (by ring) hE, (hθ_flow n).mono fun p hflow hpE =>
    hEp p hpE (θ n p) hflow⟩

/-- **Global positive-gap lazy training limit with drift `O(n⁻¹ᐟ²)`.** The statement of
`global_positive_gap_lazy_training_limit` with the drift rate improved from `O(√(log n / n))` to
`freezeRate n ≤ K₀ / √n`, at the same confidence `1 - η`. The improvement replaces the maximum
readout weight by an average of a per-neuron moment
(`exists_measurableSet_global_lazy_training_event_inv_sqrt_width`). -/
theorem global_positive_gap_lazy_training_limit_inv_sqrt_width
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ / Real.sqrt (n : ℝ)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
            fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - η ∧ ∀ᵐ p ∂((Measure.pi fun _ : Fin n =>
                Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
                gaussianReal 0 1)), p ∈ E →
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
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0) := by
  obtain ⟨freezeRate, N, hrate, hK₀, h⟩ :=
    exists_measurableSet_global_lazy_training_event_inv_sqrt_width hm hd φ hact X y lambda_inf
    hlambda_inf hK_gap (δ := η / 5) (ε := η / 5) (by positivity)
    (by linarith) (by positivity)
  refine ⟨freezeRate, N, hrate, hK₀, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, le_of_eq_of_le (by ring) hE, (hθ_flow n).mono fun p hflow hpE =>
    hEp p hpE (θ n p) hflow⟩

/-- **Single-confidence form of `exists_kernel_freeze_event_of_positive_gap`.** For every
confidence level `η ∈ (0, 1]` there are a deterministic drift rate `freezeRate n → 0` and a width
`N` such that for `n ≥ N`, with `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-probability at least `1 - η`, every
gradient flow
from `packParams W a` keeps the empirical NTK within `freezeRate n` of its initial value for all
`t ≥ 0`. This is the main theorem with `δ = ε = η / 4`.

This is an a priori estimate for any `ForwardGFTrajectory`; it does not assert that gradient flows
exist. -/
theorem exists_kernel_freeze_event_of_positive_gap_of_confidence
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t : ℝ, 0 ≤ t →
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n} ≥ 1 - η := by
  obtain ⟨freezeRate, N, hrate, h⟩ := exists_kernel_freeze_event_of_positive_gap hm hd φ hact X y
    lambda_inf hlambda_inf hK_gap (δ := η / 4) (ε := η / 4)
    (by positivity) (by linarith) (by positivity)
  exact ⟨freezeRate, N, hrate, fun n hn => le_of_eq_of_le (by ring) (h n hn)⟩

/-- **Measurable good event for finite-horizon lazy training (no spectral gap).** Assume a
`SmoothActivation` (no bound on the value of `φ`). For every horizon
`T ≥ 0`, `δ ∈ (0, 1]` and `ε > 0` there are a radius `R ≥ 0`, a deterministic sequence
`freezeRate n → 0` and a width `N` such that for `n ≥ N` there is a *measurable* event `E` of
`𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-probability at least `1 - 2 * δ - ε` on which the initial residual has
norm at
most `R` and every gradient flow from `packParams W a`, for all `t ∈ [0, T]`,
keeps the empirical NTK within `freezeRate n` of its initial value, keeps the output Jacobian within
`jacRate n` of its initial value (*Jacobian* freezing, which is strictly stronger than kernel
freezing since `K = J Jᵀ`), and stays within `taylorRate n` of its initialization linearization
`f(θ₀) + J(θ₀) (θ(t) - θ₀)`. All three rates tend to `0`; they come from the single displacement
bound `‖θ(t) - θ₀‖ ≤ C` and the Jacobian Lipschitz scale `ℓ n` (`jacRate n = ℓ n C`,
`taylorRate n = ℓ n C² / 2` by `norm_trainingOutputs_sub_linearization_le`).

Unlike the positive-gap event, no lower bound on the spectrum of the limiting kernel is assumed:
positive semidefiniteness bounds the residual by its initial size
(`finite_horizon_kernel_freeze_bound`), the initial residual is controlled by
`exists_initial_residual_radius`, and the displacement radius `r = C + 1` with `C = T * M * R / m`
depends on `T`. Exposing a measurable event (rather than only its measure) lets later arguments
intersect it with other events and take complements. This is an a priori estimate for any
`GFTrajectory`; it does not assert that gradient flows exist. -/
theorem exists_measurableSet_finite_horizon_lazy_training_event
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (R C M : ℝ) (freezeRate jacRate taylorRate : ℕ → ℝ) (N : ℕ), 0 ≤ R ∧
      Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto jacRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto taylorRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
            fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - 2 * δ - ε ∧
        ∀ p ∈ E,
          ‖trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ ≤ R ∧
          (∀ i : Fin n, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))) ∧
          ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤ M ∧
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                jacRate n ∧
              ‖trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) -
                WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ
                    (θ_traj t - packParams p.1 p.2).ofLp)‖ ≤ taylorRate n ∧
              ‖θ_traj t - packParams p.1 p.2‖ ≤ C := by
  have hφ := hact.differentiable
  have hC₁_bdd := hact.deriv_bdd
  have hderiv_lip := hact.deriv_lip
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ Xs α)) 2 (Measure.pi fun _ : Fin d =>
      gaussianReal 0 1) := fun α =>
    (activation_memLp_two hact (d := d)).1 (Xs α)
  obtain ⟨R, hR_nonneg, hR⟩ := exists_initial_residual_radius φ X y hmeasφ hφ_out_L2
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  -- Deterministic bootstrap constants; the displacement target `C` grows linearly with `T`.
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_jacobian_bound_and_good_events hact Xs hδ hδ1
  set M : ℝ := M₀ + 1 with hM
  set C : ℝ := T * M * R / m with hC
  set r : ℝ := C + 1 with hr
  set ℓ : ℕ → ℝ := fun n => Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, Xs α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, Xs α j ^ 2))) / Real.sqrt (n : ℝ) with hℓ_def
  have hM_pos : 0 < M := by positivity
  have hr_nonneg : 0 ≤ r := by positivity
  have hℓ_nonneg : ∀ n, 0 ≤ ℓ n := fun n => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hℓ : Filter.Tendsto ℓ Filter.atTop (nhds 0) :=
    tendsto_jacobianLipschitzScale Xs C₁ C₂ hδ r
  have hrate : Filter.Tendsto (fun n => 2 * M * ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using (hℓ.const_mul (2 * M)).mul_const C
  have hjac : Filter.Tendsto (fun n => ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using hℓ.mul_const C
  have htay : Filter.Tendsto (fun n => ℓ n * C ^ 2 / 2) Filter.atTop (nhds 0) := by
    simpa using (hℓ.mul_const (C ^ 2)).div_const 2
  have hsmall : ∀ᶠ n in Filter.atTop, ℓ n * r < 1 :=
    (hℓ.mul_const r).eventually (gt_mem_nhds (by rw [zero_mul]; exact one_pos))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.eventually_gt_atTop 0).and hsmall)
  refine ⟨R, C, M, fun n => 2 * M * ℓ n * C, fun n => ℓ n * C, fun n => ℓ n * C ^ 2 / 2, N,
    hR_nonneg, hrate, hjac, htay, fun n hn => ?_⟩
  obtain ⟨hn0, hsm⟩ := hN n hn
  obtain ⟨E, hEm, hEμ, hEp⟩ := hM₀ n hn0
  set Tail : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | R <
    ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖} with hTail
  have hTr : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)).real Tail ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le (hR n)
  have hEc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real Eᶜ ≤ 2 * δ := by
    rw [probReal_compl_eq_one_sub hEm]; linarith
  have hGc : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real (E ∩ Tailᶜ)ᶜ ≤ 2 * δ + ε :=
    (measureReal_compl_inter_le _ _ _).trans (by rw [compl_compl]; linarith)
  have hres_meas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)) := by
    simp_rw [trainingResidual_netFromParams_packParams]
    exact (evalVector_joint_measurable φ hmeasφ Xs).sub_const y
  refine ⟨E ∩ Tailᶜ, hEm.inter (measurableSet_lt measurable_const hres_meas.norm).compl,
    by linarith [one_sub_le_measureReal_of_measureReal_compl_le _ hGc], ?_⟩
  rintro p ⟨hpE, hpT⟩
  obtain ⟨hp1, hp2⟩ := hEp p hpE
  have hres : ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖ ≤ R :=
    not_lt.1 (show ¬ (R < _) from hpT)
  obtain ⟨hJ_bdd, hJ_lip⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn0 Xs C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ M₀ p hp1 hp2 r (ℓ n) M hr_nonneg
    (hℓ_nonneg n) (by linarith) le_rfl
  refine ⟨hres, hp2, hJ_bdd _ (by simpa using hr_nonneg), fun θ_traj hflow t ht => ?_⟩
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (Xs β) θ') (θ_traj t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (Xs β) (θ_traj t)
      fun i => hφ.differentiableAt).differentiableAt
  have hdisp := finite_horizon_displacement_bound (netFromParams φ n d) Xs y hflow hdiff T M r C hT
    hM_pos.le (Nat.cast_pos.2 hm) hr_nonneg (lt_add_one C) (by rw [hC]; gcongr) hJ_bdd t ht
  have hball : ‖θ_traj t - packParams p.1 p.2‖ ≤ r := hdisp.trans (lt_add_one C).le
  refine ⟨finite_horizon_kernel_freeze_bound (netFromParams φ n d) Xs y hflow hdiff T M (ℓ n) r C
    hT hM_pos.le (hℓ_nonneg n) (Nat.cast_pos.2 hm) hr_nonneg (lt_add_one C)
    (by rw [hC]; gcongr) hJ_bdd hJ_lip t ht,
    (hJ_lip _ hball).trans (mul_le_mul_of_nonneg_left hdisp (hℓ_nonneg n)),
    (norm_trainingOutputs_sub_linearization_le (netFromParams φ n d) Xs (packParams p.1 p.2) r
      (ℓ n) (fun z _ β => (hasFDerivAt_netFromParams φ n d (Xs β) z
        fun i => hφ.differentiableAt).differentiableAt) hJ_lip hball).trans ?_, hdisp⟩
  calc ℓ n / 2 * ‖θ_traj t - packParams p.1 p.2‖ ^ 2 ≤ ℓ n / 2 * C ^ 2 := by
        gcongr
    _ = ℓ n * C ^ 2 / 2 := by ring

/-- **Measurable good event for the finite-horizon kernel freeze (no spectral gap).** The kernel
component of `exists_measurableSet_finite_horizon_lazy_training_event`: with probability at least
`1 - 2 * δ - ε` the initial residual has norm at most `R` and every gradient flow keeps the
empirical NTK within `freezeRate n → 0` of its initial value on `[0, T]`. -/
theorem exists_measurableSet_finite_horizon_kernel_freeze
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (R : ℝ) (freezeRate : ℕ → ℝ) (N : ℕ), 0 ≤ R ∧
      Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
            fun _ : Fin n => gaussianReal 0 1)).real E ≥ 1 - 2 * δ - ε ∧
        ∀ p ∈ E,
          ‖trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ ≤ R ∧
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n := by
  obtain ⟨R, _, _, freezeRate, _, _, N, hR, hrate, -, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT hδ hδ1 hε
  refine ⟨R, freezeRate, N, hR, hrate, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, hE, fun p hp => ⟨(hEp p hp).1, fun θ_traj hflow t ht =>
    ((hEp p hp).2.2.2 θ_traj hflow t ht).1⟩⟩

/-- **Finite-horizon kernel freeze with no spectral gap.** Consequence of
`exists_measurableSet_finite_horizon_kernel_freeze`: for every horizon `T ≥ 0`, `δ ∈ (0, 1]` and
`ε > 0` there are a deterministic sequence `freezeRate n → 0` and a width `N` such that for `n ≥ N`,
with `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-probability at least `1 - 2 * δ - ε`, every gradient flow started at
`packParams W a` keeps the empirical NTK within `freezeRate n` of its initial value on `[0, T]`.
No lower bound on the spectrum of the limiting kernel is assumed, in contrast to
`exists_kernel_freeze_event_of_positive_gap`. -/
theorem exists_finite_horizon_kernel_freeze_event
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n} ≥ 1 - 2 * δ - ε := by
  obtain ⟨R, freezeRate, N, -, hrate, h⟩ :=
    exists_measurableSet_finite_horizon_kernel_freeze hm φ hact X y T hT hδ hδ1 hε
  refine ⟨freezeRate, N, hrate, fun n hn => ?_⟩
  obtain ⟨E, -, hE, hEp⟩ := h n hn
  exact hE.trans (measureReal_mono fun p hp => (hEp p hp).2)

/-- **Single-confidence form of `exists_finite_horizon_kernel_freeze_event`** (`δ = ε = η / 3`):
probability at least `1 - η` for `η ∈ (0, 1]`. -/
theorem exists_finite_horizon_kernel_freeze_event_of_confidence
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n} ≥ 1 - η := by
  obtain ⟨freezeRate, N, hrate, h⟩ := exists_finite_horizon_kernel_freeze_event hm φ hact X y T hT
    (δ := η / 3) (ε := η / 3) (by positivity)
    (by linarith) (by positivity)
  exact ⟨freezeRate, N, hrate, fun n hn => le_of_eq_of_le (by ring) (h n hn)⟩

end InitializationEvents

end

end NTK
