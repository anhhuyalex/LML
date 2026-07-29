/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Kernel
import LeanMachineLearning.Optimization.NTK.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Linearization bounds: smooth activations and ReLU

This file proves that the first-order Taylor linearization `f₀` is a good approximation
to the network `f` when the width `m` is large, corresponding to Section 4.2 of the
deep learning theory notes (Telgarsky 2021).

Two regimes are handled separately:

1. **Smooth activations** (Proposition 4.1 / `smoothLinearizationBound`):
   If `σ` is `β`-smooth (i.e. `|σ''| ≤ β`), then
   `|f(x; W) − f₀,V(x; W)| ≤ β/(2√m) · ‖W − V‖_F²`
   for any `x` with Euclidean norm at most `1`.  This does not require any
   probabilistic argument.

2. **ReLU activation** (Lemma 4.1 / `reluLinearizationBound`):
   Because the ReLU is not smooth, we instead exploit Gaussian initialization `W₀`.
   A concentration lemma (`reluSignConcentration`) bounds the number of neurons
   whose sign changes under a bounded perturbation, and Cauchy-Schwarz then gives
   `|f(x; W) − f₀(x; W)| ≤ (2B^{4/3} + B·ln(1/δ)^{1/4}) / m^{1/6}`
   with probability at least `1 − δ`, uniformly over `‖W − W₀‖_F ≤ B`.

## Main results

* `NTK.BetaSmooth` : predicate for `β`-smooth activations.
* `NTK.smoothLinearizationBound` : Proposition 4.1 (smooth case).
* `NTK.reluSignConcentration` : Lemma 4.2 (Gaussian sign-concentration).
* `NTK.reluLinearizationBound` : Lemma 4.1 (ReLU linearization bound).

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory NNReal Filter

set_option linter.style.longLine false

namespace NTK

variable {d m : ℕ}

/-! ### β-smooth activations (Definition 4.4) -/

/-- **Definition 4.4**.
An activation `σ : ℝ → ℝ` is *`β`-smooth* if `σ` is twice differentiable everywhere
and `|σ''(z)| ≤ β` for all `z ∈ ℝ`. -/
structure BetaSmooth (σ : ℝ → ℝ) (β : ℝ) : Prop where
  /-- `σ` is differentiable everywhere. -/
  differentiable : Differentiable ℝ σ
  /-- The derivative `σ'` is also differentiable everywhere. -/
  differentiable' : Differentiable ℝ (deriv σ)
  /-- Second derivative is bounded: `|σ''(z)| ≤ β`. -/
  hessian_bound   : ∀ z : ℝ, |deriv (deriv σ) z| ≤ β

lemma BetaSmooth.β_nonneg {σ : ℝ → ℝ} {β : ℝ} (h : BetaSmooth σ β) : 0 ≤ β :=
  (abs_nonneg (deriv (deriv σ) 0)).trans (h.hessian_bound 0)

/-- Taylor's theorem for `β`-smooth activations:
  `|σ(r) − σ(s) − σ'(s)·(r − s)| ≤ β(r − s)²/2`. -/
lemma BetaSmooth.taylor_bound
    {σ : ℝ → ℝ} {β : ℝ} (hσ : BetaSmooth σ β) (r s : ℝ) :
    |σ r - σ s - deriv σ s * (r - s)| ≤ β * (r - s) ^ 2 / 2 := by
  have hr : r = s ∨ r ≠ s := eq_or_ne r s
  rcases hr with rfl | hr_ne
  · simp
  let C := (σ r - σ s - deriv σ s * (r - s)) / (r - s)^2
  let g := fun t => σ t - σ s - deriv σ s * (t - s) - C * (t - s)^2
  have hg_s : g s = 0 := by simp [g]
  have hg_r : g r = 0 := by
    dsimp [g, C]
    have : (r - s) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hr_ne)
    apply sub_eq_zero.mpr
    exact (div_mul_cancel₀ _ this).symm
  have hσ_cont : Continuous σ := hσ.differentiable.continuous
  have h_cont : ContinuousOn g (Set.Icc (min s r) (max s r)) := by
    apply Continuous.continuousOn
    dsimp [g]
    fun_prop
  have h_diff : ∀ x ∈ Set.Ioo (min s r) (max s r),
      HasDerivAt g (deriv σ x - deriv σ s - 2 * C * (x - s)) x := by
    intro x _hx
    dsimp [g]
    have h1 : HasDerivAt (fun t => σ t) (deriv σ x) x := (hσ.differentiable x).hasDerivAt
    have h2 : HasDerivAt (fun t => σ s) 0 x := hasDerivAt_const x (σ s)
    have h3 : HasDerivAt (fun t => t - s) 1 x := (hasDerivAt_id x).sub_const s
    have h4 : HasDerivAt (fun t => deriv σ s * (t - s)) (deriv σ s * 1) x :=
      h3.const_mul (deriv σ s)
    have h5 : HasDerivAt (fun t => (t - s)^2) (2 * (x - s)^1 * 1) x := h3.pow 2
    have h6 : HasDerivAt (fun t => C * (t - s)^2) (C * (2 * (x - s)^1 * 1)) x := h5.const_mul C
    have h_total := ((h1.sub h2).sub h4).sub h6
    have h_simp :
        deriv σ x - 0 - deriv σ s * 1 - C * (2 * (x - s)^1 * 1) =
          deriv σ x - deriv σ s - 2 * C * (x - s) := by
      ring
    rw [h_simp] at h_total
    exact h_total
  have h_min_lt_max : min s r < max s r := by
    rcases lt_trichotomy s r with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · exfalso; apply hr_ne; exact h.symm
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have h_mean_value : ∃ c ∈ Set.Ioo (min s r) (max s r),
      deriv σ c - deriv σ s - 2 * C * (c - s) =
        (g (max s r) - g (min s r)) / (max s r - min s r) := by
    apply exists_hasDerivAt_eq_slope g _ h_min_lt_max h_cont h_diff
  rcases h_mean_value with ⟨c, hc, hc_eq⟩
  have hg_eval : g (max s r) - g (min s r) = 0 := by
    have h1 : g (max s r) = 0 := by
      rcases max_choice s r with h | h <;> rw [h]
      · exact hg_s
      · exact hg_r
    have h2 : g (min s r) = 0 := by
      rcases min_choice s r with h | h <;> rw [h]
      · exact hg_s
      · exact hg_r
    rw [h1, h2, sub_zero]
  rw [hg_eval, zero_div] at hc_eq
  have hc_simp : deriv σ c - deriv σ s = 2 * C * (c - s) := sub_eq_zero.mp hc_eq
  have h_c_ne_s : c ≠ s := by
    intro h_eq
    have h_in : s ∈ Set.Ioo (min s r) (max s r) := h_eq ▸ hc
    rcases le_total r s with hrs | hsr
    · rw [max_eq_left hrs] at h_in
      exact lt_irrefl _ h_in.2
    · rw [min_eq_left hsr] at h_in
      exact lt_irrefl _ h_in.1
  have h_min_c : min s c < max s c := by
    rcases lt_trichotomy s c with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · exfalso; apply h_c_ne_s; exact h.symm
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have h_mean_value2 : ∃ ξ ∈ Set.Ioo (min s c) (max s c),
      deriv (deriv σ) ξ = (deriv σ (max s c) - deriv σ (min s c)) / (max s c - min s c) := by
    apply exists_hasDerivAt_eq_slope (deriv σ) _ h_min_c
    · apply Continuous.continuousOn
      exact hσ.differentiable'.continuous
    · intro x _hx
      exact (hσ.differentiable' x).hasDerivAt
  rcases h_mean_value2 with ⟨ξ, _hξ, hξ_eq⟩
  have h_deriv_diff : deriv σ (max s c) - deriv σ (min s c) = 2 * C * (max s c - min s c) := by
    rcases le_total s c with hsc | hcs
    · rw [max_eq_right hsc, min_eq_left hsc]
      exact hc_simp
    · rw [max_eq_left hcs, min_eq_right hcs]
      linarith [hc_simp]
  rw [h_deriv_diff] at hξ_eq
  have h_C_eq : C = deriv (deriv σ) ξ / 2 := by
    have h_denom : max s c - min s c ≠ 0 := sub_ne_zero.mpr h_min_c.ne'
    rw [mul_div_cancel_right₀ _ h_denom] at hξ_eq
    linarith [hξ_eq]
  dsimp [C] at h_C_eq
  have h_final : σ r - σ s - deriv σ s * (r - s) = deriv (deriv σ) ξ / 2 * (r - s) ^ 2 := by
    have h_r_s : (r - s)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hr_ne)
    rw [← h_C_eq]
    exact (div_mul_cancel₀ _ h_r_s).symm
  have h_abs_bound :
      |deriv (deriv σ) ξ / 2 * (r - s) ^ 2| =
        |deriv (deriv σ) ξ| / 2 * (r - s) ^ 2 := by
    rw [abs_mul, abs_div, abs_two]
    have h_sq : 0 ≤ (r - s) ^ 2 := sq_nonneg (r - s)
    rw [abs_of_nonneg h_sq]
  rw [h_final, h_abs_bound]
  have h_bound := hσ.hessian_bound ξ
  have h_sq : 0 ≤ (r - s) ^ 2 := sq_nonneg (r - s)
  nlinarith

-- Frobenius norm square equals the double sum of squared coordinate differences
private lemma frobeniusNorm_sq_eq_sum {d m : ℕ} (W V : Fin m → Fin d → ℝ) :
    (frobeniusNorm (fun i j => W i j - V i j))^2 =
      ∑ i : Fin m, ∑ j : Fin d, (W i j - V i j)^2 := by
  unfold frobeniusNorm
  apply Real.sq_sqrt
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

/-! ### Smooth linearization bound (Proposition 4.1) -/

/-- **Proposition 4.1** (Telgarsky 2021).
For a `β`-smooth activation `σ` and outer coefficients `|aⱼ| ≤ 1`,
and for any `x` with Euclidean norm at most `1` and any weight matrices `W, V`:
  `|f(x; W) − f₀,V(x; W)| ≤ β/(2√m) · ‖W − V‖_F²`.

**Proof sketch:** Apply the Taylor bound to each neuron and sum using Cauchy-Schwarz.
No probabilistic argument is needed; the bound holds for any `W, V ∈ ℝ^{m×d}`. -/
theorem smoothLinearizationBound
    {σ : ℝ → ℝ} {β : ℝ}
    (hσ : BetaSmooth σ β)
    (net : ShallowNetwork σ d m)
    (x : Fin d → ℝ)
    (hx : x ⊙ x ≤ 1)
    (W V : Fin m → Fin d → ℝ) :
    |net.eval x W - linearization (σ := σ) (σ' := deriv σ) net.outerCoeffs x V W|
    ≤ β / (2 * Real.sqrt m) * frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
  dsimp [ShallowNetwork.eval, linearization]
  have h_pull :
    (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * σ (∑ k : Fin d, W j k * x k) -
    ((m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * σ (∑ k : Fin d, V j k * x k) +
     (m : ℝ)⁻¹.sqrt * ∑ j : Fin m,
      net.outerCoeffs j * deriv σ (∑ k : Fin d, V j k * x k) *
        ∑ k : Fin d, (W j k - V j k) * x k) =
    (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k) := by
    rw [← mul_add, ← mul_sub]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_pull]
  have h_abs : |(m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| =
    (m : ℝ)⁻¹.sqrt * |∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h_abs]
  have h_sum_le : |∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| ≤
    ∑ j : Fin m, |net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_bound : ∀ j : Fin m,
      |net.outerCoeffs j * (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) -
        deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)| ≤
        β / 2 * (∑ k, (W j k - V j k) * x k)^2 := by
    intro j
    rw [abs_mul]
    have h_taylor := hσ.taylor_bound (∑ k, W j k * x k) (∑ k, V j k * x k)
    have h_sub : ∑ k, W j k * x k - ∑ k, V j k * x k = ∑ k, (W j k - V j k) * x k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_sub] at h_taylor
    have h_rewrite :
        β * (∑ k : Fin d, (W j k - V j k) * x k) ^ 2 / 2 =
          β / 2 * (∑ k : Fin d, (W j k - V j k) * x k) ^ 2 := by
      ring
    rw [h_rewrite] at h_taylor
    have h1 := net.outerCoeffs_bound j
    nlinarith [abs_nonneg (σ (∑ k : Fin d, W j k * x k) -
      σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) *
        ∑ k : Fin d, (W j k - V j k) * x k)]
  have h_sum_bound :
      ∑ j : Fin m, |net.outerCoeffs j *
        (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) -
          deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)| ≤
        ∑ j : Fin m, (β / 2 * (∑ k, (W j k - V j k) * x k)^2) :=
    Finset.sum_le_sum fun j _ => h_bound j
  have h_factor : ∑ j : Fin m, (β / 2 * (∑ k, (W j k - V j k) * x k)^2)
    = β / 2 * ∑ j : Fin m, (∑ k, (W j k - V j k) * x k)^2 := by rw [← Finset.mul_sum]
  have h_cs : ∀ j : Fin m, (∑ k : Fin d, (W j k - V j k) * x k)^2 ≤
    (∑ k : Fin d, (W j k - V j k)^2) * (∑ k : Fin d, (x k)^2) := fun j =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => W j k - V j k) x
  have h_cs_sum : ∑ j : Fin m, (∑ k, (W j k - V j k) * x k)^2 ≤
    ∑ j : Fin m, ((∑ k, (W j k - V j k)^2) * (∑ k, (x k)^2)) := Finset.sum_le_sum fun j _ => h_cs j
  have h_x_bound : ∑ k : Fin d, (x k)^2 = x ⊙ x := (innerProduct_self_eq_sum_sq x).symm
  have h_frob : ∑ j : Fin m, (∑ k, (W j k - V j k)^2) * (x ⊙ x)
    = (∑ j : Fin m, ∑ k, (W j k - V j k)^2) * (x ⊙ x) := by rw [← Finset.sum_mul]
  have h_frob_def :
      ∑ j : Fin m, ∑ k, (W j k - V j k)^2 =
        frobeniusNorm (fun i j => W i j - V i j) ^ 2 := (frobeniusNorm_sq_eq_sum W V).symm
  have h_m_pos : 0 ≤ (m : ℝ)⁻¹.sqrt := Real.sqrt_nonneg _
  have h_final :
      (m : ℝ)⁻¹.sqrt * |∑ j : Fin m, net.outerCoeffs j *
        (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) -
          deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)| ≤
        β / (2 * Real.sqrt m) * frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
    calc
      (m : ℝ)⁻¹.sqrt * |∑ j : Fin m, net.outerCoeffs j *
          (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) -
            deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)| ≤
        (m : ℝ)⁻¹.sqrt *
          ∑ j : Fin m, (β / 2 * (∑ k, (W j k - V j k) * x k)^2) := by
          exact mul_le_mul_of_nonneg_left (h_sum_le.trans h_sum_bound) h_m_pos
      _ = (m : ℝ)⁻¹.sqrt *
          (β / 2 * ∑ j : Fin m, (∑ k, (W j k - V j k) * x k)^2) := by
        rw [h_factor]
      _ ≤ (m : ℝ)⁻¹.sqrt *
          (β / 2 *
            ∑ j : Fin m, ((∑ k, (W j k - V j k)^2) * (∑ k, (x k)^2))) := by
        have h_beta_div : 0 ≤ β / 2 := by
          have h_beta : 0 ≤ β := by
            have : 0 ≤ |deriv (deriv σ) 0| := abs_nonneg _
            exact this.trans (hσ.hessian_bound 0)
          exact div_nonneg h_beta zero_le_two
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_cs_sum h_beta_div)
          h_m_pos
      _ = (m : ℝ)⁻¹.sqrt *
          (β / 2 * ((frobeniusNorm (fun i j => W i j - V i j) ^ 2) * (x ⊙ x))) := by
        congr 2
        rw [h_x_bound, h_frob, h_frob_def]
      _ ≤ (m : ℝ)⁻¹.sqrt *
          (β / 2 * ((frobeniusNorm (fun i j => W i j - V i j) ^ 2) * 1)) := by
        have h_frob_nonneg :
            0 ≤ frobeniusNorm (fun i j => W i j - V i j) ^ 2 :=
          sq_nonneg _
        have h_beta_div : 0 ≤ β / 2 := by
          have h_beta : 0 ≤ β := (abs_nonneg _).trans (hσ.hessian_bound 0)
          exact div_nonneg h_beta zero_le_two
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hx h_frob_nonneg)
            h_beta_div)
          h_m_pos
      _ = β / (2 * Real.sqrt m) * frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
        rw [Real.sqrt_inv]
        ring
  exact h_final

/-! ### Sign concentration under Gaussian initialization (Lemma 4.2) -/

/-- The set of neuron indices whose inner product with `x` is small in absolute value.
  `signAmbiguous τ x W₀ = {j : |wⱼ₀ᵀx| ≤ τ‖x‖}`. -/
noncomputable def signAmbiguous (τ : ℝ) (x : Fin d → ℝ) (W₀ : Fin m → Fin d → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun j =>
    |∑ k : Fin d, W₀ j k * x k| ≤ τ * Real.sqrt (x ⊙ x))

/-- The linear map sending a row vector `w` to the dot product `∑ k, w k * x k`. -/
noncomputable def dotMap {d : ℕ} (x : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ k, w k * x k
  map_add' w₁ w₂ := by simp [Finset.sum_add_distrib, add_mul]
  map_smul' c w := by simp [Finset.mul_sum, mul_assoc]

/-- The continuous linear functional associated to `dotMap x`. -/
noncomputable def dotCLM {d : ℕ} (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (dotMap x)

/-- Informal proof: The measure `gaussianRowMeasure d` is the standard multivariate Gaussian
distribution $\mathcal{N}(0, I_d)$. The map $w \mapsto w^\top x$ is a linear functional.
By standard properties of multivariate Gaussians, the pushforward of a standard Gaussian
under a linear map $w \mapsto w^\top x$ is a 1D Gaussian with mean 0 and variance $\|x\|^2$.
(Source: Vershynin, R. "High-Dimensional Probability", Theorem 3.3.6). -/
lemma map_gaussianRowMeasure_dot {d : ℕ} (x : Fin d → ℝ) :
    Measure.map (fun w => ∑ k, w k * x k) (gaussianRowMeasure d) =
      gaussianReal 0 (Real.toNNReal (x ⊙ x)) := by
  have h_eq : (fun w : Fin d → ℝ => ∑ k, w k * x k) =
      (fun (v : EuclideanSpace ℝ (Fin d)) => innerSL ℝ (WithLp.toLp 2 x) v) ∘ (WithLp.toLp 2) := by
    ext w
    dsimp
    exact (EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 x) (WithLp.toLp 2 w))
  rw [h_eq, ← Measure.map_map]
  · have h_toLp : Measure.map (WithLp.toLp 2) (gaussianRowMeasure d) = stdGaussian (EuclideanSpace ℝ (Fin d)) :=
      map_pi_eq_stdGaussian
    rw [h_toLp]
    have h_map := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) (innerSL ℝ (WithLp.toLp 2 x))
    rw [h_map]
    have h_mean : ∫ (v : EuclideanSpace ℝ (Fin d)), (innerSL ℝ (WithLp.toLp 2 x)) v ∂stdGaussian (EuclideanSpace ℝ (Fin d)) = 0 := by
      rw [(innerSL ℝ (WithLp.toLp 2 x)).integral_comp_id_comm IsGaussian.integrable_id]
      rw [integral_id_stdGaussian]
      exact map_zero (innerSL ℝ (WithLp.toLp 2 x))
    have h_var : Var[innerSL ℝ (WithLp.toLp 2 x); stdGaussian (EuclideanSpace ℝ (Fin d))] = x ⊙ x := by
      rw [variance_dual_stdGaussian]
      rw [innerSL_apply_norm]
      rw [norm_sq_eq_innerProduct (WithLp.toLp 2 x)]
    rw [h_mean, h_var]
  · fun_prop
  · fun_prop

/-- Informal proof: The density of a 1D Gaussian $Z \sim \mathcal{N}(0, v)$ is
$f(z) = \frac{1}{\sqrt{2\pi v}} e^{-z^2/(2v)}$.
Since $e^{-z^2/(2v)} \le 1$ for all $z$, the probability of the interval $[-a, a]$ is bounded by:
$$ P(|Z| \le a) = \int_{-a}^{a} f(z) dz \le \int_{-a}^{a} \frac{1}{\sqrt{2\pi v}} dz = \frac{2a}{\sqrt{2\pi v}} $$
(Source: Rick Durrett, "Probability: Theory and Examples", Gaussian density bounds). -/
-- Pointwise bound on the Gaussian density function by its maximum at 0.
private lemma gaussianPDFReal_le_inv_sqrt (v : ℝ≥0) (z : ℝ) :
    gaussianPDFReal 0 v z ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal]
  simp only [sub_zero]
  have h1 : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h2 : Real.exp (-(z) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [sq_nonneg z]
    · positivity
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(z) ^ 2 / (2 * (v : ℝ)))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 h1
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

-- Integral of a constant function over the symmetric interval [-a, a].
private lemma setIntegral_const_abs_bound (a : ℝ) (_ha : 0 ≤ a) (c : ℝ) :
    ∫ (_z : ℝ) in {z | |z| ≤ a}, c = 2 * a * c := by
  have h_set : {z : ℝ | |z| ≤ a} = Set.Icc (-a) a := by ext z; simp [abs_le]
  rw [h_set, setIntegral_const]
  rw [measureReal_def, Real.volume_Icc]
  simp only [sub_neg_eq_add]
  have h_pos : 0 ≤ a + a := by linarith
  rw [ENNReal.toReal_ofReal h_pos]
  have : a + a = 2 * a := by ring
  rw [this, smul_eq_mul]

lemma gaussianReal_Icc_bound (v : ℝ≥0) (hv : 0 < v) (a : ℝ) (ha : 0 ≤ a) :
    (gaussianReal 0 v).real {z | |z| ≤ a} ≤ 2 * a / Real.sqrt (2 * Real.pi * v) := by
  have hv_ne : v ≠ 0 := ne_of_gt hv
  have h1 : (gaussianReal 0 v).real {z | |z| ≤ a} = ∫ z in {z | |z| ≤ a}, gaussianPDFReal 0 v z := by
    change ((gaussianReal 0 v) {z | |z| ≤ a}).toReal = _
    rw [gaussianReal_apply_eq_integral 0 hv_ne]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun z => gaussianPDFReal_nonneg 0 v z))
  rw [h1]
  have h2 : ∫ z in {z | |z| ≤ a}, gaussianPDFReal 0 v z ≤ ∫ (z : ℝ) in {z | |z| ≤ a}, (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    apply setIntegral_mono
    · exact (integrable_gaussianPDFReal 0 v).integrableOn
    · have h_set : {z : ℝ | |z| ≤ a} = Set.Icc (-a) a := by ext z; simp [abs_le]
      rw [h_set]
      exact continuous_const.integrableOn_Icc
    · exact gaussianPDFReal_le_inv_sqrt v
  have h3 : ∫ (z : ℝ) in {z | |z| ≤ a}, (Real.sqrt (2 * Real.pi * v))⁻¹ = 2 * a / Real.sqrt (2 * Real.pi * v) := by
    rw [setIntegral_const_abs_bound a ha]
    rw [div_eq_mul_inv]
  exact h2.trans_eq h3


lemma prob_signAmbiguous_le_tau {d : ℕ} (x : Fin d → ℝ) (hx : 0 < x ⊙ x) (τ : ℝ) (hτ : 0 < τ) :
    (gaussianRowMeasure d).real {w | |∑ k, w k * x k| ≤ τ * Real.sqrt (x ⊙ x)} ≤ τ := by
  have h_map := map_gaussianRowMeasure_dot x
  have h_prob_eq : (gaussianRowMeasure d).real {w | |∑ k, w k * x k| ≤ τ * Real.sqrt (x ⊙ x)} =
      (gaussianReal 0 (Real.toNNReal (x ⊙ x))).real {z | |z| ≤ τ * Real.sqrt (x ⊙ x)} := by
    have h_set : {z : ℝ | |z| ≤ τ * Real.sqrt (x ⊙ x)} = Set.Icc (- (τ * Real.sqrt (x ⊙ x))) (τ * Real.sqrt (x ⊙ x)) := by ext z; simp [abs_le]
    have h_meas : Measurable (fun w : Fin d → ℝ => ∑ k, w k * x k) := (dotCLM x).continuous.measurable
    have h_preimage : {w : Fin d → ℝ | |∑ k, w k * x k| ≤ τ * Real.sqrt (x ⊙ x)} =
      (fun w : Fin d → ℝ => ∑ k, w k * x k) ⁻¹' (Set.Icc (- (τ * Real.sqrt (x ⊙ x))) (τ * Real.sqrt (x ⊙ x))) := by ext w; simp [abs_le]
    rw [h_preimage]
    have h_map_apply : (Measure.map (fun w => ∑ k, w k * x k) (gaussianRowMeasure d)) (Set.Icc (- (τ * Real.sqrt (x ⊙ x))) (τ * Real.sqrt (x ⊙ x))) =
      (gaussianRowMeasure d) ((fun w : Fin d → ℝ => ∑ k, w k * x k) ⁻¹' (Set.Icc (- (τ * Real.sqrt (x ⊙ x))) (τ * Real.sqrt (x ⊙ x)))) :=
        Measure.map_apply h_meas measurableSet_Icc
    have h_real_eq : ((gaussianRowMeasure d).real ((fun w : Fin d → ℝ => ∑ k, w k * x k) ⁻¹' (Set.Icc (- (τ * Real.sqrt (x ⊙ x))) (τ * Real.sqrt (x ⊙ x))))) =
      (Measure.map (fun w => ∑ k, w k * x k) (gaussianRowMeasure d)).real (Set.Icc (- (τ * Real.sqrt (x ⊙ x))) (τ * Real.sqrt (x ⊙ x))) := by
      exact congr_arg ENNReal.toReal h_map_apply.symm
    rw [h_real_eq, h_map, ← h_set]
  have h_bound := gaussianReal_Icc_bound (Real.toNNReal (x ⊙ x)) (Real.toNNReal_pos.mpr hx)
    (τ * Real.sqrt (x ⊙ x)) (mul_nonneg hτ.le (Real.sqrt_nonneg _))
  have h_simp : 2 * (τ * Real.sqrt (x ⊙ x)) / Real.sqrt (2 * Real.pi * Real.toNNReal (x ⊙ x)) = τ * Real.sqrt (2 / Real.pi) := by
    have h_toNNReal : (Real.toNNReal (x ⊙ x) : ℝ) = x ⊙ x := Real.coe_toNNReal _ hx.le
    rw [h_toNNReal]
    have h_sqrt_mul : Real.sqrt (2 * Real.pi * (x ⊙ x)) = Real.sqrt (2 * Real.pi) * Real.sqrt (x ⊙ x) :=
      Real.sqrt_mul (by positivity) (x ⊙ x)
    rw [h_sqrt_mul]
    have h1 : 2 * (τ * Real.sqrt (x ⊙ x)) / (Real.sqrt (2 * Real.pi) * Real.sqrt (x ⊙ x)) =
              (τ * (2 / Real.sqrt (2 * Real.pi))) * (Real.sqrt (x ⊙ x) / Real.sqrt (x ⊙ x)) := by ring
    rw [h1]
    have h_sqrt_pos : 0 < Real.sqrt (x ⊙ x) := Real.sqrt_pos.mpr hx
    rw [div_self h_sqrt_pos.ne', mul_one]
    have h2 : 2 / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
      have h_two : (2 : ℝ) = Real.sqrt 2 * Real.sqrt 2 := (Real.mul_self_sqrt (by positivity)).symm
      nth_rw 1 [h_two]
      rw [Real.sqrt_mul (by positivity) Real.pi]
      have h_div : (Real.sqrt 2 * Real.sqrt 2) / (Real.sqrt 2 * Real.sqrt Real.pi) = Real.sqrt 2 / Real.sqrt Real.pi := by
        rw [mul_div_mul_left]
        have : (0:ℝ) < 2 := by norm_num
        exact (Real.sqrt_pos.mpr this).ne'
      rw [h_div]
      exact (Real.sqrt_div (by positivity) Real.pi).symm
    rw [h2]
  have h_final : τ * Real.sqrt (2 / Real.pi) ≤ τ := by
    have h_pi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have h_frac : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr h_pi
    have h_sqrt : Real.sqrt (2 / Real.pi) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h_frac
    rw [Real.sqrt_one] at h_sqrt
    have h_mul := mul_le_mul_of_nonneg_left h_sqrt hτ.le
    rw [mul_one] at h_mul
    exact h_mul
  rw [h_prob_eq]
  exact h_bound.trans (le_of_eq h_simp) |> fun h => h.trans h_final

lemma hoeffding_indicators_pi
    (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) [DecidablePred (· ∈ S)] (hS : MeasurableSet S) (p : ℝ) (hp : μ.real S ≤ p)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin m => μ)).real
      {ω : Fin m → Ω | (m : ℝ) * p + t < (Finset.univ.filter (fun j => ω j ∈ S)).card}
      ≤ Real.exp (- 2 * t ^ 2 / m) := by
  let X : Fin m → (Fin m → Ω) → ℝ := fun j ω ↦ if ω j ∈ S then 1 else 0
  have hX_meas : ∀ j, Measurable (X j) := fun j ↦ Measurable.ite (measurable_pi_apply _ hS) measurable_const measurable_const
  have hX_bound : ∀ j, ∀ᵐ ω ∂(Measure.pi (fun _ : Fin m => μ)), X j ω ∈ Set.Icc (0 : ℝ) 1 :=
    fun j ↦ Eventually.of_forall (fun ω ↦ by dsimp [X]; split_ifs <;> simp)
  have Hmap : ∀ j, Measure.map (fun ω : Fin m → Ω ↦ ω j) (Measure.pi (fun _ : Fin m => μ)) = μ := by
    intro j
    rw [Measure.pi_map_eval]
    simp [measure_univ]
  have hX_mean : ∀ j, (Measure.pi (fun _ : Fin m => μ))[X j] ≤ p := by
    intro j
    have h1 : ∫ x, (fun x ↦ if x ∈ S then (1 : ℝ) else 0) (x j) ∂(Measure.pi (fun _ : Fin m => μ)) = ∫ x, if x ∈ S then (1 : ℝ) else 0 ∂(Measure.map (fun ω ↦ ω j) (Measure.pi (fun _ : Fin m => μ))) := by
      have : (fun x : Fin m → Ω ↦ (fun y ↦ if y ∈ S then (1 : ℝ) else 0) (x j)) = (fun x ↦ if x ∈ S then (1 : ℝ) else 0) ∘ (fun ω ↦ ω j) := rfl
      rw [this]
      have h_int_map := integral_map (measurable_pi_apply j).aemeasurable (f := fun y : Ω ↦ if y ∈ S then (1 : ℝ) else 0) (μ := Measure.pi (fun _ : Fin m ↦ μ))
      have h_aestrongly_meas : AEStronglyMeasurable (fun y : Ω ↦ if y ∈ S then (1 : ℝ) else 0) (Measure.map (fun ω : Fin m → Ω ↦ ω j) (Measure.pi (fun _ : Fin m ↦ μ))) := by
        apply Measurable.aestronglyMeasurable
        exact Measurable.ite hS measurable_const measurable_const
      exact (h_int_map h_aestrongly_meas).symm
    rw [h1, Hmap]
    have eq : (fun x ↦ if x ∈ S then (1 : ℝ) else 0) = S.indicator (fun _ ↦ (1 : ℝ)) := by ext x; by_cases hx : x ∈ S <;> simp [hx, Set.indicator]
    rw [eq, integral_indicator hS]
    simp [hp]
  let Y : Fin m → (Fin m → Ω) → ℝ := fun j ω ↦ X j ω - (Measure.pi (fun _ : Fin m => μ))[X j]
  have hY_indep : iIndepFun Y (Measure.pi (fun _ : Fin m => μ)) := by
    have h_aemeas : ∀ i : Fin m, AEMeasurable (fun x : Ω ↦ (if x ∈ S then (1 : ℝ) else 0) - (Measure.pi (fun _ : Fin m => μ))[X i]) μ :=
      fun i ↦ ((Measurable.ite hS measurable_const measurable_const).sub measurable_const).aemeasurable
    exact iIndepFun_pi h_aemeas
  have hY_subG : ∀ j, HasSubgaussianMGF (Y j) ((1 / 4 : ℝ≥0)) (Measure.pi (fun _ : Fin m => μ)) := by
    intro j
    have hm : AEMeasurable (X j) (Measure.pi (fun _ : Fin m => μ)) := (hX_meas j).aemeasurable
    have h_subG := hasSubgaussianMGF_of_mem_Icc hm (hX_bound j)
    have eq : (((‖(1 : ℝ) - 0‖₊) / 2) ^ 2) = (1 / 4 : ℝ≥0) := by
      ext; simp; norm_num
    rw [eq] at h_subG
    exact h_subG
  have h_hoeffding := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY_indep (s := Finset.univ) (fun i _ ↦ hY_subG i) (ε := t) ht
  have eq_bound : Real.exp (-t ^ 2 / (2 * ↑(∑ i : Fin m, (1 / 4 : ℝ≥0)))) = Real.exp (- 2 * t ^ 2 / m) := by
    congr 1
    push_cast
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [eq_bound] at h_hoeffding
  have h_subset : {ω : Fin m → Ω | (m : ℝ) * p + t < (Finset.univ.filter (fun j => ω j ∈ S)).card} ⊆
      {ω | t ≤ ∑ i : Fin m, Y i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h_card : ((Finset.univ.filter (fun j => ω j ∈ S)).card : ℝ) = ∑ j : Fin m, X j ω := by
      dsimp [X]
      rw [Finset.sum_ite]
      simp
    rw [h_card] at hω
    have h_mean_sum : (∑ i : Fin m, (Measure.pi (fun _ : Fin m => μ))[X i]) ≤ m * p := by
      have : (∑ i : Fin m, (Measure.pi (fun _ : Fin m => μ))[X i]) ≤ ∑ i : Fin m, p := Finset.sum_le_sum (fun i _ ↦ hX_mean i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      exact this
    dsimp [Y]
    rw [Finset.sum_sub_distrib]
    linarith
  exact (measureReal_mono h_subset).trans h_hoeffding

-- Bound 1 - δ ≤ (gaussianInit m d).real {W₀ | P W₀} when P holds for all W₀
private lemma measure_ge_one_sub_delta_of_univ
    {m d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {P : (Fin m → Fin d → ℝ) → Prop}
    (hP : ∀ W₀, P W₀) :
    1 - δ ≤ (gaussianInit m d).real {W₀ | P W₀} := by
  have h_univ : {W₀ | P W₀} = Set.univ := Set.ext fun W₀ => iff_true_intro (hP W₀)
  rw [h_univ]
  haveI : IsProbabilityMeasure (gaussianRowMeasure d) := by unfold gaussianRowMeasure; infer_instance
  haveI : IsProbabilityMeasure (gaussianInit m d) := by unfold gaussianInit; infer_instance
  have h_prob_univ : (gaussianInit m d).real Set.univ = 1 := by simp
  rw [h_prob_univ]
  exact sub_le_self 1 (le_of_lt hδ)

/-- **Lemma 4.2** (Telgarsky 2021 / Hoeffding concentration).
Let `x ∈ ℝᵈ` with `‖x‖ > 0` and let `W₀ ~ 𝒩(0, Iᵈ)^{⊗m}`.
For any `τ > 0` and `δ ∈ (0,1)`, with probability at least `1 − δ` over `W₀`,
  `|{j : |wⱼ₀ᵀx| ≤ τ‖x‖₂}| ≤ mτ + √(m/2 · ln(1/δ))`.

**Proof:** Each indicator is Bernoulli with mean `≤ τ` (Gaussian density bound);
apply Hoeffding's inequality to the i.i.d. sum. -/
theorem reluSignConcentration
    (x : Fin d → ℝ) (hx : 0 < x ⊙ x)
    (τ : ℝ) (hτ : 0 < τ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (gaussianInit m d).real {W₀ |
      (m : ℝ) * τ + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) <
        (signAmbiguous τ x W₀).card} ≤ δ := by
  by_cases hm : m = 0
  · subst hm
    have h_empty : {W₀ : Fin 0 → Fin d → ℝ | ((0 : ℕ) : ℝ) * τ +
      Real.sqrt (((0 : ℕ) : ℝ) / 2 * Real.log (1 / δ)) < ↑(signAmbiguous τ x W₀).card} = ∅ := by
      ext W₀
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h_card : (signAmbiguous τ x W₀).card = 0 := Finset.card_eq_zero.mpr (by simp [signAmbiguous])
      rw [h_card, Nat.cast_zero]
      norm_num
    rw [h_empty, measureReal_empty]
    exact hδ.le
  have h_m_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have h_prob := prob_signAmbiguous_le_tau x hx τ hτ
  have h_t_nonneg : 0 ≤ Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) := Real.sqrt_nonneg _
  haveI : IsProbabilityMeasure (gaussianRowMeasure d) := by
    dsimp [gaussianRowMeasure]
    infer_instance
  have hS_meas : MeasurableSet {w : Fin d → ℝ | |∑ k, w k * x k| ≤ τ * Real.sqrt (x ⊙ x)} := by
    apply measurableSet_le
    · exact (Measurable.norm (dotCLM x).continuous.measurable)
    · exact measurable_const
  have h_hoeffding := hoeffding_indicators_pi m (gaussianRowMeasure d)
    {w | |∑ k, w k * x k| ≤ τ * Real.sqrt (x ⊙ x)} hS_meas τ h_prob
    (Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))) h_t_nonneg
  have h_one_lt_div : 1 ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h_one_lt_div
  have h_sq : (Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))) ^ 2 = (m : ℝ) / 2 * Real.log (1 / δ) :=
    Real.sq_sqrt (mul_nonneg (div_nonneg (Nat.cast_nonneg m) zero_le_two) h_log_pos)
  have h_calc : -2 * (Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))) ^ 2 / (m : ℝ) = -Real.log (1 / δ) := by
    rw [h_sq]
    calc
      -2 * ((m : ℝ) / 2 * Real.log (1 / δ)) / (m : ℝ)
      _ = -((2 * ((m : ℝ) / 2)) * Real.log (1 / δ)) / (m : ℝ) := by ring
      _ = -((m : ℝ) * Real.log (1 / δ)) / (m : ℝ) := by
        have : 2 * ((m : ℝ) / 2) = (m : ℝ) := mul_div_cancel₀ (m : ℝ) two_ne_zero
        rw [this]
      _ = -Real.log (1 / δ) * ((m : ℝ) / (m : ℝ)) := by ring
      _ = -Real.log (1 / δ) := by rw [div_self h_m_pos.ne', mul_one]
  have h_exp : Real.exp (- 2 * (Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))) ^ 2 / m) = δ := by
    rw [h_calc, Real.exp_neg, Real.exp_log (zero_lt_one.trans_le h_one_lt_div)]
    rw [one_div, inv_inv]
  unfold gaussianInit signAmbiguous
  exact h_hoeffding.trans (le_of_eq h_exp)

/-! ### Bad index sets for the ReLU proof -/

/-- Neurons whose row perturbation is at least the local cutoff `r`:
  `largePerturb r W W₀ = {j : ‖wⱼ − wⱼ₀‖₂ ≥ r}`. -/
noncomputable def largePerturb (r : ℝ) (W W₀ : Fin m → Fin d → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun j =>
    r ≤ Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2))

/-- The union of the sign-ambiguous and large-perturbation index sets. -/
noncomputable def badSet (τ r : ℝ) (x : Fin d → ℝ) (W W₀ : Fin m → Fin d → ℝ) : Finset (Fin m) :=
  signAmbiguous τ x W₀ ∪ largePerturb r W W₀

/-- For neurons outside `badSet`, the sign of `wⱼᵀx` agrees with `wⱼ₀ᵀx`.
This is the key geometric observation: if `|wⱼ₀ᵀx| > τ‖x‖` and `‖wⱼ − wⱼ₀‖ < τ`,
then the sign cannot have flipped. -/
lemma sign_preserved_outside_badSet
    (τ : ℝ) (_hτ : 0 < τ)
    (x : Fin d → ℝ)
    (W W₀ : Fin m → Fin d → ℝ)
    (j : Fin m) (hj : j ∉ badSet τ τ x W W₀) :
    (0 ≤ ∑ k : Fin d, W j k * x k) ↔
    (0 ≤ ∑ k : Fin d, W₀ j k * x k) := by
  have hj_ambig : j ∉ signAmbiguous τ x W₀ := fun h => hj (Finset.mem_union_left _ h)
  have hj_perturb : j ∉ largePerturb τ W W₀ := fun h => hj (Finset.mem_union_right _ h)
  rw [signAmbiguous, Finset.mem_filter, not_and, not_le] at hj_ambig
  have hA := hj_ambig (Finset.mem_univ j)
  rw [largePerturb, Finset.mem_filter, not_and, not_le] at hj_perturb
  have hB := hj_perturb (Finset.mem_univ j)
  have h_CS_sq : (∑ k : Fin d, (W j k - W₀ j k) * x k) ^ 2 ≤ (∑ k : Fin d, (W j k - W₀ j k) ^ 2) * (x ⊙ x) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => W j k - W₀ j k) x
    have h_dot : ∑ k : Fin d, x k ^ 2 = x ⊙ x := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rwa [h_dot] at this
  have h_CS : |∑ k : Fin d, (W j k - W₀ j k) * x k| ≤ Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2) * Real.sqrt (x ⊙ x) := by
    have h_nonneg_1 : 0 ≤ ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [← Real.sqrt_mul h_nonneg_1]
    have h_sqrt := Real.sqrt_le_sqrt h_CS_sq
    rw [Real.sqrt_sq_eq_abs] at h_sqrt
    exact h_sqrt
  have h_diff_bound : |∑ k : Fin d, W j k * x k - ∑ k : Fin d, W₀ j k * x k| ≤ τ * Real.sqrt (x ⊙ x) := by
    have h_eq : ∑ k : Fin d, W j k * x k - ∑ k : Fin d, W₀ j k * x k = ∑ k : Fin d, (W j k - W₀ j k) * x k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_eq]
    have h_le : Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2) * Real.sqrt (x ⊙ x) ≤ τ * Real.sqrt (x ⊙ x) := by
      exact mul_le_mul_of_nonneg_right hB.le (Real.sqrt_nonneg _)
    exact h_CS.trans h_le
  have h_abs_diff : |∑ k : Fin d, W j k * x k - ∑ k : Fin d, W₀ j k * x k| < |∑ k : Fin d, W₀ j k * x k| :=
    h_diff_bound.trans_lt hA
  constructor
  · intro hW
    by_contra hW₀
    push Not at hW₀
    have h_sub : 0 ≤ ∑ k : Fin d, W j k * x k - ∑ k : Fin d, W₀ j k * x k := sub_nonneg.mpr (hW₀.le.trans hW)
    rw [abs_of_nonneg h_sub, abs_of_neg hW₀] at h_abs_diff
    linarith
  · intro hW₀
    by_contra hW
    push Not at hW
    have h_sub : ∑ k : Fin d, W j k * x k - ∑ k : Fin d, W₀ j k * x k ≤ 0 := sub_nonpos.mpr (hW.le.trans hW₀)
    rw [abs_of_nonpos h_sub, abs_of_nonneg hW₀] at h_abs_diff
    linarith

/-! ### ReLU linearization bound (Lemma 4.1) -/

/-- The ReLU activation. Bundled here for convenience. -/
noncomputable def relu : ℝ → ℝ := fun z => max z 0

/-- The subgradient / derivative of ReLU (a.e. equal to the indicator): `σ'(z) = 1[z ≥ 0]`. -/
noncomputable def reluDeriv : ℝ → ℝ := fun z => if 0 ≤ z then 1 else 0

/-- Scaled shallow network with ReLU activation. -/
abbrev ReLUNetwork (d m : ℕ) := ShallowNetwork relu d m

lemma relu_error_eq_zero_outside_badSet
    {d m : ℕ} (net : ReLUNetwork d m) (x : Fin d → ℝ) (W W₀ : Fin m → Fin d → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (j : Fin m) (hj : j ∉ badSet τ τ x W W₀) :
    net.outerCoeffs j * relu (∑ k, W j k * x k) -
    net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * (∑ k, W j k * x k) = 0 := by
  have h_sign := sign_preserved_outside_badSet τ hτ x W W₀ j hj
  dsimp [relu, reluDeriv]
  rw [mul_assoc, ← mul_sub]
  split_ifs with h_W₀
  · have h_W : 0 ≤ ∑ k, W j k * x k := h_sign.mpr h_W₀
    rw [max_eq_left h_W, one_mul, sub_self, mul_zero]
  · push Not at h_W₀
    have h_W : ¬(0 ≤ ∑ k, W j k * x k) := fun h => by linarith [h_sign.mp h, h_W₀]
    push Not at h_W
    rw [max_eq_right h_W.le, zero_mul, sub_zero, mul_zero]

lemma relu_linearization_error_le (a b : ℝ) :
    |relu a - reluDeriv b * a| ≤ |a - b| := by
  dsimp [relu, reluDeriv]
  split_ifs with hb
  · rw [one_mul]
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [max_eq_right ha, zero_sub, abs_neg, abs_of_nonpos ha]
      have : a ≤ b := ha.trans hb
      rw [abs_of_nonpos (sub_nonpos.mpr this)]
      linarith
  · rw [zero_mul, sub_zero]
    push Not at hb
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha, abs_of_nonneg ha]
      have : b ≤ a := hb.le.trans ha
      rw [abs_of_nonneg (sub_nonneg.mpr this)]
      linarith
    · rw [max_eq_right ha, abs_zero]
      exact abs_nonneg _

lemma relu_eq_reluDeriv_mul (z : ℝ) : relu z = reluDeriv z * z := by
  dsimp [relu, reluDeriv]
  split_ifs with h
  · rw [max_eq_left h, one_mul]
  · push Not at h
    rw [max_eq_right h.le, zero_mul]

lemma relu_eval_sub_linearization_eq
    {d m : ℕ} (net : ReLUNetwork d m) (x : Fin d → ℝ) (W W₀ : Fin m → Fin d → ℝ) :
    net.eval x W - linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W₀ W =
    (m : ℝ)⁻¹.sqrt * ∑ j : Fin m,
      (net.outerCoeffs j * relu (∑ k, W j k * x k) -
       net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k) := by
  dsimp [ShallowNetwork.eval, linearization]
  rw [← mul_add, ← mul_sub]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h_relu : relu (∑ k, W₀ j k * x k) = reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W₀ j k * x k :=
    relu_eq_reluDeriv_mul _
  rw [h_relu]
  have h_dist : ∑ k : Fin d, (W j k - W₀ j k) * x k = ∑ k, W j k * x k - ∑ k, W₀ j k * x k := by
    simp_rw [sub_mul]
    exact (Finset.sum_sub_distrib (f := fun k => W j k * x k) (g := fun k => W₀ j k * x k))
  rw [h_dist]
  ring

lemma sum_eq_sum_badSet
    {d m : ℕ} (net : ReLUNetwork d m) (x : Fin d → ℝ) (W W₀ : Fin m → Fin d → ℝ)
    (τ : ℝ)
    (h_zero : ∀ j : Fin m, j ∉ badSet τ τ x W W₀ →
      net.outerCoeffs j * relu (∑ k, W j k * x k) -
      net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k = 0) :
    ∑ j : Fin m, (net.outerCoeffs j * relu (∑ k, W j k * x k) -
      net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k) =
    ∑ j ∈ badSet τ τ x W W₀, (net.outerCoeffs j * relu (∑ k, W j k * x k) -
      net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k) := by
  symm
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro j _ hj
    exact h_zero j hj

lemma relu_error_sum_le
    {d m : ℕ} (net : ReLUNetwork d m) (x : Fin d → ℝ) (W W₀ : Fin m → Fin d → ℝ)
    (S : Finset (Fin m)) :
    |∑ j ∈ S, (net.outerCoeffs j * relu (∑ k, W j k * x k) -
      net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k)| ≤
    ∑ j ∈ S, |∑ k, (W j k - W₀ j k) * x k| := by
  calc |∑ j ∈ S, (net.outerCoeffs j * relu (∑ k, W j k * x k) -
        net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k)|
    _ ≤ ∑ j ∈ S, |net.outerCoeffs j * relu (∑ k, W j k * x k) -
          net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ S, |∑ k, (W j k - W₀ j k) * x k| := by
      apply Finset.sum_le_sum
      intro j _
      have h1 : net.outerCoeffs j * relu (∑ k, W j k * x k) -
          net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k =
          net.outerCoeffs j * (relu (∑ k, W j k * x k) - reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k) := by ring
      rw [h1, abs_mul]
      have h_bound := relu_linearization_error_le (∑ k, W j k * x k) (∑ k, W₀ j k * x k)
      have h_sub : ∑ k, W j k * x k - ∑ k, W₀ j k * x k = ∑ k, (W j k - W₀ j k) * x k := by
        simp_rw [sub_mul]
        exact (Finset.sum_sub_distrib (f := fun k => W j k * x k) (g := fun k => W₀ j k * x k)).symm
      rw [h_sub] at h_bound
      have h_c := net.outerCoeffs_bound j
      nlinarith [abs_nonneg (relu (∑ k, W j k * x k) - reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k)]

lemma relu_error_cs_bound
    {d m : ℕ} (x : Fin d → ℝ) (hx : x ⊙ x ≤ 1)
    (W W₀ : Fin m → Fin d → ℝ) (B : ℝ)
    (h_frob : frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B)
    (S : Finset (Fin m)) :
    ∑ j ∈ S, |∑ k : Fin d, (W j k - W₀ j k) * x k| ≤ Real.sqrt (S.card : ℝ) * B := by
  have h_cs1 : ∀ j ∈ S, |∑ k : Fin d, (W j k - W₀ j k) * x k| ≤ Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2) := by
    intro j _
    have h_sq : (∑ k : Fin d, (W j k - W₀ j k) * x k) ^ 2 ≤ (∑ k : Fin d, (W j k - W₀ j k) ^ 2) * (x ⊙ x) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => W j k - W₀ j k) x
      have h_dot : ∑ k : Fin d, x k ^ 2 = x ⊙ x := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      rwa [h_dot] at this
    have h_nonneg1 : 0 ≤ ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have h_nonneg2 : 0 ≤ x ⊙ x := Finset.sum_nonneg (fun k _ => mul_self_nonneg (x k))
    have h_sqrt := Real.sqrt_le_sqrt h_sq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul h_nonneg1] at h_sqrt
    have h_x1 : Real.sqrt (x ⊙ x) ≤ 1 := by
      have : Real.sqrt (x ⊙ x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hx
      rwa [Real.sqrt_one] at this
    nlinarith [Real.sqrt_nonneg (∑ k : Fin d, (W j k - W₀ j k) ^ 2), Real.sqrt_nonneg (x ⊙ x)]
  have h_sum_le : ∑ j ∈ S, |∑ k : Fin d, (W j k - W₀ j k) * x k| ≤ ∑ j ∈ S, Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2) :=
    Finset.sum_le_sum h_cs1
  have h_cs2 : (∑ j ∈ S, Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2))^2 ≤ (S.card : ℝ) * (∑ j ∈ S, ∑ k : Fin d, (W j k - W₀ j k) ^ 2) := by
    have h_sum_sq := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun j => Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2))
    simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at h_sum_sq
    have h_sqrt_sq : ∀ j ∈ S, (Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2))^2 = ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := by
      intro j _
      apply Real.sq_sqrt
      exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have h_congr : ∑ j ∈ S, (Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2))^2 = ∑ j ∈ S, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 :=
      Finset.sum_congr rfl h_sqrt_sq
    rwa [h_congr] at h_sum_sq
  have h_sub_frob : ∑ j ∈ S, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 ≤ B^2 := by
    calc ∑ j ∈ S, ∑ k : Fin d, (W j k - W₀ j k) ^ 2
      _ ≤ ∑ j : Fin m, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ _
        · intro i _ _
          exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
      _ = (frobeniusNorm (fun i k => W i k - W₀ i k))^2 := by
        unfold frobeniusNorm
        apply (Real.sq_sqrt _).symm
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
      _ ≤ B^2 := by
        have h_frob_nonneg : 0 ≤ frobeniusNorm (fun i k => W i k - W₀ i k) := frobeniusNorm_nonneg _
        nlinarith
  have h_CS_bound : (∑ j ∈ S, Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2))^2 ≤ (Real.sqrt (S.card : ℝ) * B)^2 := by
    calc (∑ j ∈ S, Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2))^2
      _ ≤ (S.card : ℝ) * (∑ j ∈ S, ∑ k : Fin d, (W j k - W₀ j k) ^ 2) := h_cs2
      _ ≤ (S.card : ℝ) * B^2 := mul_le_mul_of_nonneg_left h_sub_frob (Nat.cast_nonneg _)
      _ = (Real.sqrt (S.card : ℝ) * B)^2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h_nonneg_sum : 0 ≤ ∑ j ∈ S, Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2) :=
    Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
  have h_B_nonneg : 0 ≤ B := by
    have := frobeniusNorm_nonneg (fun i k => W i k - W₀ i k)
    exact this.trans h_frob
  have h_nonneg_RHS : 0 ≤ Real.sqrt (S.card : ℝ) * B := mul_nonneg (Real.sqrt_nonneg _) h_B_nonneg
  have h_sqrt_le : ∑ j ∈ S, Real.sqrt (∑ k : Fin d, (W j k - W₀ j k) ^ 2) ≤ Real.sqrt (S.card : ℝ) * B := by
    nlinarith [h_CS_bound, h_nonneg_sum, h_nonneg_RHS]
  exact h_sum_le.trans h_sqrt_le

lemma card_largePerturb_bound
    {d m : ℕ} (W W₀ : Fin m → Fin d → ℝ) (r B : ℝ) (hr : 0 < r)
    (h_frob : frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B) :
    (largePerturb r W W₀).card ≤ (B / r) ^ 2 := by
  have hr_pos : 0 < r^2 := sq_pos_of_pos hr
  have hr_sq_le : ∀ j ∈ largePerturb r W W₀, r^2 ≤ ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := by
    intro j hj
    have h_r_le := (Finset.mem_filter.mp hj).2
    have h_nonneg : 0 ≤ ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have h_sq := mul_le_mul h_r_le h_r_le hr.le (Real.sqrt_nonneg _)
    rw [← sq, ← sq, Real.sq_sqrt h_nonneg] at h_sq
    exact h_sq
  have h_sum_lower : ((largePerturb r W W₀).card : ℝ) * r^2 ≤ ∑ j ∈ largePerturb r W W₀, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := by
    calc ((largePerturb r W W₀).card : ℝ) * r^2 = ∑ j ∈ largePerturb r W W₀, r^2 := by simp
    _ ≤ ∑ j ∈ largePerturb r W W₀, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := Finset.sum_le_sum hr_sq_le
  have h_sum_upper : ∑ j ∈ largePerturb r W W₀, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 ≤ B^2 := by
    calc ∑ j ∈ largePerturb r W W₀, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 ≤ ∑ j : Fin m, ∑ k : Fin d, (W j k - W₀ j k) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.subset_univ _
          · intro i _ _
            apply Finset.sum_nonneg
            intro k _
            exact sq_nonneg _
    _ = (frobeniusNorm (fun i k => W i k - W₀ i k))^2 := by
      unfold frobeniusNorm
      apply (Real.sq_sqrt _).symm
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro k _
      exact sq_nonneg _
    _ ≤ B^2 := by
      have h_frob_nonneg : 0 ≤ frobeniusNorm (fun i k => W i k - W₀ i k) := by
        unfold frobeniusNorm
        exact Real.sqrt_nonneg _
      nlinarith [h_frob, h_frob_nonneg]
  have h_bound : ((largePerturb r W W₀).card : ℝ) * r^2 ≤ B^2 := h_sum_lower.trans h_sum_upper
  rw [div_pow]
  exact (le_div_iff₀ hr_pos).mpr h_bound

lemma sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  calc x + y ≤ x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
        have : 0 ≤ 2 * (Real.sqrt x * Real.sqrt y) := mul_nonneg zero_le_two (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        linarith
    _ = (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
    _ = (Real.sqrt x + Real.sqrt y) ^ 2 := by ring

lemma m_pow_bound (m : ℕ) (hm : 1 ≤ m) : (m : ℝ) ^ (-1/4 : ℝ) ≤ (m : ℝ) ^ (-1/6 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by norm_num)

lemma sqrt_B_pow (B : ℝ) (hB : 0 ≤ B) : Real.sqrt (B ^ (2/3 : ℝ)) = B ^ (1/3 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hB]
  congr 1
  norm_num

lemma sqrt_m_pow (m : ℕ) (_hm : 1 ≤ m) : Real.sqrt ((m : ℝ) ^ (-1/3 : ℝ)) = (m : ℝ) ^ (-1/6 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 1; norm_num

lemma sqrt_sqrt_m_pow (m : ℕ) (_hm : 1 ≤ m) : Real.sqrt (Real.sqrt (1 / (2 * (m : ℝ)))) = (2 * (m : ℝ)) ^ (-1/4 : ℝ) := by
  have hm_pos : 0 ≤ 2 * (m : ℝ) := by positivity
  have h_inv : 1 / (2 * (m : ℝ)) = (2 * (m : ℝ)) ^ (-1 : ℝ) := by rw [one_div, ← Real.rpow_neg_one]
  rw [h_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hm_pos, ← Real.rpow_mul hm_pos]
  congr 1
  norm_num

-- Bound B * m^(-1/4) * log(1/δ)^(1/4) ≤ B * m^(-1/6) * log(1/δ)^(1/4)
private lemma rpow_m_neg_quarter_bound
    (m : ℕ) (hm : 1 ≤ m) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    B * ((m : ℝ) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) ≤
      B * ((m : ℝ) ^ (-1/6 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) :=
  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (m_pow_bound m hm)
    (Real.rpow_nonneg (Real.log_nonneg (one_le_one_div hδ hδ1.le)) _)) hB

-- Bound √2 * B^(4/3) * m^(-1/6) ≤ 2 * B^(4/3) * m^(-1/6)
private lemma sqrt_two_mul_b_rpow_le
    (m : ℕ) (_hm : 1 ≤ m) (B : ℝ) (_hB : 0 ≤ B) :
    Real.sqrt 2 * B ^ (4/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) ≤
      2 * B ^ (4/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) := by
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)

lemma reluLinearization_algebraic_bound
    (m : ℕ) (hm : 1 ≤ m) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let r := B ^ (2/3 : ℝ) / (m : ℝ) ^ (1/3 : ℝ)
    let S_bound := (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) + (B / r) ^ 2
    B / Real.sqrt m * Real.sqrt S_bound ≤
      (2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) /
        (m : ℝ) ^ (1 / 6 : ℝ) := by
  intro r S_bound
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by linarith : 0 < m)
  have h_r_sq : (B / r) ^ 2 = B ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) := by
    dsimp [r]
    calc (B / (B ^ (2/3 : ℝ) / (m : ℝ) ^ (1/3 : ℝ))) ^ 2
      _ = (B * (m : ℝ) ^ (1/3 : ℝ) / B ^ (2/3 : ℝ)) ^ 2 := by rw [div_div_eq_mul_div]
      _ = (B ^ (1 : ℝ) * (m : ℝ) ^ (1/3 : ℝ) / B ^ (2/3 : ℝ)) ^ 2 := by
        have hB1 : B = B ^ (1 : ℝ) := by rw [Real.rpow_one]
        nth_rw 1 [hB1]
      _ = (B ^ (1 : ℝ) / B ^ (2/3 : ℝ) * (m : ℝ) ^ (1/3 : ℝ)) ^ 2 := by ring
      _ = (B ^ (1 - 2/3 : ℝ) * (m : ℝ) ^ (1/3 : ℝ)) ^ 2 := by
        by_cases hB0 : B = 0
        · subst hB0; norm_num
        · have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
          congr 1
          congr 1
          rw [← Real.rpow_sub hB_pos]
      _ = (B ^ (1/3 : ℝ) * (m : ℝ) ^ (1/3 : ℝ)) ^ 2 := by
        congr 2
        congr 1
        norm_num
      _ = B ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast]
        rw [← Real.rpow_mul hB, ← Real.rpow_mul hm_pos.le]
        congr 1 <;> norm_num
  have h_mr : (m : ℝ) * r = B ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) := by
    dsimp [r]
    have h1 : (m : ℝ) * (B ^ (2/3 : ℝ) / (m : ℝ) ^ (1/3 : ℝ)) = B ^ (2/3 : ℝ) * ((m : ℝ) / (m : ℝ) ^ (1/3 : ℝ)) := by ring
    rw [h1]
    have h2 : (m : ℝ) / (m : ℝ) ^ (1/3 : ℝ) = (m : ℝ) ^ (2/3 : ℝ) := by
      nth_rw 1 [← Real.rpow_one (m : ℝ)]
      rw [← Real.rpow_sub hm_pos]
      congr 1
      norm_num
    rw [h2]
  have h_S_bound : S_bound = 2 * B ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) := by
    dsimp [S_bound]
    rw [h_r_sq, h_mr]
    ring
  have h_S_div : S_bound / (m : ℝ) = 2 * B ^ (2/3 : ℝ) * (m : ℝ) ^ (-1/3 : ℝ) + Real.sqrt (1 / (2 * (m : ℝ)) * Real.log (1 / δ)) := by
    rw [h_S_bound, add_div]
    congr 1
    · have h1 : 2 * B ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) / (m : ℝ) = 2 * B ^ (2/3 : ℝ) * ((m : ℝ) ^ (2/3 : ℝ) / (m : ℝ)) := by ring
      rw [h1]
      have h2 : (m : ℝ) ^ (2/3 : ℝ) / (m : ℝ) = (m : ℝ) ^ (-1/3 : ℝ) := by
        nth_rw 2 [← Real.rpow_one (m : ℝ)]
        rw [← Real.rpow_sub hm_pos]
        congr 1
        norm_num
      rw [h2]
    · have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1.le)
      have h_pos : 0 ≤ (m : ℝ) / 2 * Real.log (1 / δ) := by positivity
      calc Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) / (m : ℝ)
        _ = Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) / Real.sqrt ((m : ℝ) ^ 2) := by
          rw [Real.sqrt_sq hm_pos.le]
        _ = Real.sqrt (((m : ℝ) / 2 * Real.log (1 / δ)) / (m : ℝ) ^ 2) := by rw [← Real.sqrt_div h_pos]
        _ = Real.sqrt (1 / (2 * (m : ℝ)) * Real.log (1 / δ)) := by
          congr 1
          calc (m : ℝ) / 2 * Real.log (1 / δ) / ((m : ℝ) ^ 2)
            _ = ((m : ℝ) / (m : ℝ) ^ 2) / 2 * Real.log (1 / δ) := by ring
            _ = (1 / (m : ℝ)) / 2 * Real.log (1 / δ) := by
              congr 2
              rw [sq, div_mul_eq_div_div, div_self hm_pos.ne', one_div]
            _ = 1 / (2 * (m : ℝ)) * Real.log (1 / δ) := by ring
  have h_LHS : B / Real.sqrt (m : ℝ) * Real.sqrt S_bound = B * Real.sqrt (S_bound / (m : ℝ)) := by
    have h1 : B / Real.sqrt (m : ℝ) * Real.sqrt S_bound = B * (Real.sqrt S_bound / Real.sqrt (m : ℝ)) := by ring
    rw [h1, ← Real.sqrt_div]
    rw [h_S_bound]
    positivity
  have h_sqrt_S_div : Real.sqrt (S_bound / (m : ℝ)) ≤ Real.sqrt (2 * B ^ (2/3 : ℝ) * (m : ℝ) ^ (-1/3 : ℝ)) + Real.sqrt (Real.sqrt (1 / (2 * (m : ℝ)) * Real.log (1 / δ))) := by
    rw [h_S_div]
    apply sqrt_add_le_add_sqrt <;> positivity
  have h_term1 : Real.sqrt (2 * B ^ (2/3 : ℝ) * (m : ℝ) ^ (-1/3 : ℝ)) = Real.sqrt 2 * B ^ (1/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [sqrt_B_pow B hB, sqrt_m_pow m hm]
  have h_term2 : Real.sqrt (Real.sqrt (1 / (2 * (m : ℝ)) * Real.log (1 / δ))) = (2 * (m : ℝ)) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [sqrt_sqrt_m_pow m hm]
    congr 1
    have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1.le)
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h_log_pos]
    congr 1
    norm_num
  have h_B_pow : B * B ^ (1/3 : ℝ) = B ^ (4/3 : ℝ) := by
    by_cases hB0 : B = 0
    · subst hB0; norm_num
    · have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      have h2 : B * B ^ (1/3 : ℝ) = B ^ (1 : ℝ) * B ^ (1/3 : ℝ) := by
        congr 1
        exact (Real.rpow_one B).symm
      rw [h2, ← Real.rpow_add hB_pos]
      congr 1
      norm_num
  have h_bound1 : B * ((2 * (m : ℝ)) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) ≤ B * ((m : ℝ) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) := by
    have h2 : (2 * (m : ℝ)) ^ (-1/4 : ℝ) = (2 : ℝ) ^ (-1/4 : ℝ) * (m : ℝ) ^ (-1/4 : ℝ) := Real.mul_rpow (by positivity) (by positivity)
    rw [h2]
    have h3_0 : (2 : ℝ) ^ (-1/4 : ℝ) ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1/4 : ℝ) ≤ 0)
    have h3 : (2 : ℝ) ^ (-1/4 : ℝ) ≤ (1 : ℝ) := by
      calc (2 : ℝ) ^ (-1/4 : ℝ)
        _ ≤ (2 : ℝ) ^ (0 : ℝ) := h3_0
        _ = (1 : ℝ) := Real.rpow_zero _
    have h4 : (2 : ℝ) ^ (-1/4 : ℝ) * (m : ℝ) ^ (-1/4 : ℝ) ≤ (1 : ℝ) * (m : ℝ) ^ (-1/4 : ℝ) := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hm_pos.le _)
    rw [one_mul] at h4
    have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1.le)
    have h5 : (2 : ℝ) ^ (-1/4 : ℝ) * (m : ℝ) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ) ≤ (m : ℝ) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ) := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg h_log_pos _)
    exact mul_le_mul_of_nonneg_left h5 hB
  have h_bound2 := rpow_m_neg_quarter_bound m hm B δ hB hδ hδ1
  have h_bound3 := sqrt_two_mul_b_rpow_le m hm B hB
  calc B / Real.sqrt (m : ℝ) * Real.sqrt S_bound
    _ = B * Real.sqrt (S_bound / (m : ℝ)) := h_LHS
    _ ≤ B * (Real.sqrt 2 * B ^ (1/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) + (2 * (m : ℝ)) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      calc Real.sqrt (S_bound / (m : ℝ))
        _ ≤ Real.sqrt (2 * B ^ (2/3 : ℝ) * (m : ℝ) ^ (-1/3 : ℝ)) + Real.sqrt (Real.sqrt (1 / (2 * (m : ℝ)) * Real.log (1 / δ))) := h_sqrt_S_div
        _ = Real.sqrt 2 * B ^ (1/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) + (2 * (m : ℝ)) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ) := by rw [h_term1, h_term2]
    _ = Real.sqrt 2 * (B * B ^ (1/3 : ℝ)) * (m : ℝ) ^ (-1/6 : ℝ) + B * ((2 * (m : ℝ)) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) := by ring
    _ = Real.sqrt 2 * B ^ (4/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) + B * ((2 * (m : ℝ)) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) := by rw [h_B_pow]
    _ ≤ 2 * B ^ (4/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) + B * ((2 * (m : ℝ)) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) := add_le_add h_bound3 (le_refl _)
    _ ≤ 2 * B ^ (4/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) + B * ((m : ℝ) ^ (-1/4 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) := add_le_add (le_refl _) h_bound1
    _ ≤ 2 * B ^ (4/3 : ℝ) * (m : ℝ) ^ (-1/6 : ℝ) + B * ((m : ℝ) ^ (-1/6 : ℝ) * Real.log (1 / δ) ^ (1/4 : ℝ)) := add_le_add (le_refl _) h_bound2
    _ = (2 * B ^ (4/3 : ℝ) + B * Real.log (1 / δ) ^ (1/4 : ℝ)) / (m : ℝ) ^ (1/6 : ℝ) := by
      have h1 : (m : ℝ) ^ (-1/6 : ℝ) = 1 / (m : ℝ) ^ (1/6 : ℝ) := by
        calc (m : ℝ) ^ (-1/6 : ℝ)
          _ = (m : ℝ) ^ (-(1/6 : ℝ)) := by congr 1; norm_num
          _ = ((m : ℝ) ^ (1/6 : ℝ))⁻¹ := Real.rpow_neg hm_pos.le _
          _ = 1 / (m : ℝ) ^ (1/6 : ℝ) := (one_div _).symm
      rw [h1]
      ring

lemma innerProduct_eq_zero_iff_eq_zero {d : ℕ} (x : Fin d → ℝ) : x ⊙ x = 0 ↔ x = 0 := by
  rw [← norm_sq_eq_innerProduct (WithLp.toLp 2 x)]; simp

lemma frobeniusNorm_eq_zero {d m : ℕ} (W : Fin m → Fin d → ℝ) :
  frobeniusNorm W = 0 ↔ W = 0 := by
  unfold frobeniusNorm
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg (W i j))))]
  constructor
  · intro h
    ext i j
    have h_i := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))).mp h i (Finset.mem_univ _)
    have h_ij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp h_i j (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp h_ij
  · intro h; subst h; simp

/-- The cardinality of `signAmbiguous r x W₀`, viewed as a real number, is a measurable function
of `W₀`. This is the key measurability fact used in `reluLinearizationBound`.

**Proof:** Write the cardinality as a finite sum of measurable indicator functions using
`Finset.natCast_card_filter`, then apply `Finset.measurable_fun_sum`. Each indicator is measurable
because the inner product `W₀ ↦ ∑ k, W₀ j k * x k` is continuous (via `dotCLM`), absolute value
is continuous, and `measurableSet_le` gives the set measurability. -/
lemma measurable_signAmbiguous_card (r : ℝ) (x : Fin d → ℝ) :
    Measurable (fun W₀ : Fin m → Fin d → ℝ =>
      ((signAmbiguous r x W₀).card : ℝ)) := by
  simp only [signAmbiguous, Finset.natCast_card_filter]
  apply Finset.measurable_fun_sum
  intro j _
  apply Measurable.ite
  · apply measurableSet_le
    · exact continuous_abs.measurable.comp
        ((dotCLM x).continuous.measurable.comp (measurable_pi_apply j))
    · exact measurable_const
  · exact measurable_const
  · exact measurable_const


/-- **Lemma 4.1** (Telgarsky 2021, main ReLU linearization bound).
Let `net` be a ReLU network, `W₀ ~ 𝒩(0, Iᵈ)^{⊗m}`, `B ≥ 0`, and `‖x‖ ≤ 1`.
With probability at least `1 − δ` over `W₀`, for every `W` with `‖W − W₀‖_F ≤ B`:
  `|f(x; W) − f₀(x; W)| ≤ (2B^{4/3} + B·(ln(1/δ))^{1/4}) / m^{1/6}`.

**Proof sketch:**
1. Choose the balancing radius `r = B^{2/3}/m^{1/3}`.
6. Outside `S`, signs are preserved, so the linearization error sums only over `j ∈ S`;
   Cauchy-Schwarz gives the stated bound. -/
theorem reluLinearizationBound
    (net : ReLUNetwork d m)
    (x : Fin d → ℝ) (hx : x ⊙ x ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (gaussianInit m d).real {W₀ |
      ∀ W : Fin m → Fin d → ℝ,
        frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B →
          |net.eval x W -
           linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W₀ W|
          ≤ (2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) /
            (m : ℝ) ^ (1 / 6 : ℝ)} := by
  haveI : IsProbabilityMeasure (gaussianRowMeasure d) := by unfold gaussianRowMeasure; infer_instance
  haveI : IsProbabilityMeasure (gaussianInit m d) := by unfold gaussianInit; infer_instance
  have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_div hδ |>.mpr (le_of_lt hδ1))
  by_cases hx_pos : 0 < x ⊙ x
  swap
  · -- x = 0 case
    have hx_zero_norm : x ⊙ x = 0 := le_antisymm (not_lt.mp hx_pos) (innerProduct_self_nonneg x)
    have hx_zero : x = 0 := (innerProduct_eq_zero_iff_eq_zero x).mp hx_zero_norm
    subst hx_zero
    apply measure_ge_one_sub_delta_of_univ hδ
    intro W₀ W _
    have heval0 : net.eval 0 W = 0 := by simp [ShallowNetwork.eval, relu, Finset.sum_const_zero]
    have hlin0 : linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs 0 W₀ W = 0 := by
      simp [linearization, relu, reluDeriv, Finset.sum_const_zero]
    rw [heval0, hlin0, sub_zero, abs_zero]
    positivity
  by_cases hm : m = 0
  · -- m = 0 case
    subst hm
    apply measure_ge_one_sub_delta_of_univ hδ
    intro W₀ W _
    have heval0 : net.eval x W = 0 := by simp [ShallowNetwork.eval, Real.sqrt_zero]
    have hlin0 : linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W₀ W = 0 := by
      simp [linearization, Real.sqrt_zero]
    rw [heval0, hlin0, sub_zero, abs_zero]
    positivity
  by_cases hB_zero : B = 0
  · -- B = 0 case
    subst hB_zero
    apply measure_ge_one_sub_delta_of_univ hδ
    intro W₀ W hW
    have hW_eq : W = W₀ := by
      have hnorm := frobeniusNorm_nonneg (fun i k => W i k - W₀ i k)
      have hnorm_zero : frobeniusNorm (fun i k => W i k - W₀ i k) = 0 := le_antisymm hW hnorm
      have hdiff := (frobeniusNorm_eq_zero (fun i k => W i k - W₀ i k)).mp hnorm_zero
      ext i k; exact sub_eq_zero.mp (congr_fun (congr_fun hdiff i) k)
    have hlin : linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W₀ W₀ = net.eval x W₀ := by
      simp [linearization, ShallowNetwork.eval, sub_self, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hW_eq, hlin, sub_self, abs_zero]
    positivity
  have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB_zero)
  let r := B ^ (2 / 3 : ℝ) / (m : ℝ) ^ (1 / 3 : ℝ)
  have hr : 0 < r := by
    apply div_pos
    · exact Real.rpow_pos_of_pos hB_pos _
    · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) _
  have h_sign_conc := reluSignConcentration (m := m) x hx_pos r hr δ hδ hδ1
  have h_compl : {W₀ : Fin m → Fin d → ℝ | ((signAmbiguous r x W₀).card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))} =
    {W₀ : Fin m → Fin d → ℝ | (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) < ((signAmbiguous r x W₀).card : ℝ)}ᶜ := by
    ext W₀
    simp only [Set.mem_ofPred, Set.mem_compl_iff]
    exact not_lt.symm
  -- The probability of the complement is ≥ 1 - δ
  apply le_trans (b := (gaussianInit m d).real {W₀ : Fin m → Fin d → ℝ | ((signAmbiguous r x W₀).card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))})
  · rw [h_compl, measureReal_compl]
    · have h_prob_univ : (gaussianInit m d).real Set.univ = 1 := by simp
      rw [h_prob_univ]
      exact sub_le_sub_left h_sign_conc 1
    · exact measurableSet_lt measurable_const (measurable_signAmbiguous_card r x)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro W₀ h_W₀ W h_W
  let S1 := signAmbiguous r x W₀
  let S2 := largePerturb r W W₀
  let S := badSet r r x W W₀
  have h_S1 : (S1.card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) := h_W₀
  have h_S2 : (S2.card : ℝ) ≤ (B / r) ^ 2 := card_largePerturb_bound W W₀ r B hr h_W
  have h_S_card : (S.card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) + (B / r) ^ 2 := by
    have h1 : S.card ≤ S1.card + S2.card := by
      apply le_trans (Finset.card_le_card (by rfl))
      exact Finset.card_union_le S1 S2
    have h2 : (S.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by
      exact_mod_cast h1
    linarith
  have h_diff_S : |net.eval x W - linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W₀ W| ≤ B / Real.sqrt (m : ℝ) * Real.sqrt (S.card : ℝ) := by
    have h_sub_eq := relu_eval_sub_linearization_eq net x W W₀
    rw [h_sub_eq]
    have h_zero : ∀ j : Fin m, j ∉ S →
        net.outerCoeffs j * relu (∑ k, W j k * x k) -
        net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k = 0 :=
      fun j hj => relu_error_eq_zero_outside_badSet net x W W₀ r hr j hj
    have h_sum := sum_eq_sum_badSet net x W W₀ r h_zero
    rw [h_sum]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h_sum_le := relu_error_sum_le net x W W₀ S
    have h_sum_cs := relu_error_cs_bound x hx W W₀ B h_W S
    calc (m : ℝ)⁻¹.sqrt * |∑ j ∈ S, (net.outerCoeffs j * relu (∑ k, W j k * x k) -
          net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * ∑ k, W j k * x k)|
      _ ≤ (m : ℝ)⁻¹.sqrt * ∑ j ∈ S, |∑ k, (W j k - W₀ j k) * x k| :=
        mul_le_mul_of_nonneg_left h_sum_le (Real.sqrt_nonneg _)
      _ ≤ (m : ℝ)⁻¹.sqrt * (Real.sqrt (S.card : ℝ) * B) :=
        mul_le_mul_of_nonneg_left h_sum_cs (Real.sqrt_nonneg _)
      _ = B / Real.sqrt (m : ℝ) * Real.sqrt (S.card : ℝ) := by
        rw [Real.sqrt_inv]
        ring
  have h_alg := reluLinearization_algebraic_bound m (Nat.pos_of_ne_zero hm) B δ hB hδ hδ1
  have h_bound : B / Real.sqrt (m : ℝ) * Real.sqrt (S.card : ℝ) ≤ B / Real.sqrt (m : ℝ) * Real.sqrt ((m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) + (B / r) ^ 2) := by
    apply mul_le_mul_of_nonneg_left
    · apply Real.sqrt_le_sqrt h_S_card
    · positivity
  exact le_trans h_diff_S (le_trans h_bound h_alg)

lemma frob_sub_le {d m : ℕ} (V W W₀ : Fin m → Fin d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hV : frobeniusNorm (fun i k => V i k - W₀ i k) ≤ B)
    (hW : frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B) :
    frobeniusNorm (fun i k => V i k - W i k) ≤ 2 * B := by
  have h_cs : ∀ i k, (V i k - W i k)^2 ≤ 2 * (V i k - W₀ i k)^2 + 2 * (W i k - W₀ i k)^2 := by
    intro i k
    have h1 : 0 ≤ ((V i k - W₀ i k) + (W i k - W₀ i k))^2 := sq_nonneg _
    have h2 : (V i k - W i k)^2 = ((V i k - W₀ i k) - (W i k - W₀ i k))^2 := by ring
    rw [h2]
    linarith [h1]
  have h_sum : ∑ i : Fin m, ∑ k : Fin d, (V i k - W i k)^2 ≤
      2 * (∑ i : Fin m, ∑ k : Fin d, (V i k - W₀ i k)^2) + 2 * (∑ i : Fin m, ∑ k : Fin d, (W i k - W₀ i k)^2) := by
    calc ∑ i : Fin m, ∑ k : Fin d, (V i k - W i k)^2
      _ ≤ ∑ i : Fin m, ∑ k : Fin d, (2 * (V i k - W₀ i k)^2 + 2 * (W i k - W₀ i k)^2) := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro k _; exact h_cs i k
      _ = 2 * (∑ i : Fin m, ∑ k : Fin d, (V i k - W₀ i k)^2) + 2 * (∑ i : Fin m, ∑ k : Fin d, (W i k - W₀ i k)^2) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hV_nonneg : 0 ≤ ∑ i : Fin m, ∑ k : Fin d, (V i k - W₀ i k)^2 := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hV_sq : ∑ i : Fin m, ∑ k : Fin d, (V i k - W₀ i k)^2 ≤ B^2 := by
    have h1 := mul_le_mul hV hV (frobeniusNorm_nonneg _) hB
    rw [← sq] at h1
    unfold frobeniusNorm at h1
    rw [Real.sq_sqrt hV_nonneg] at h1
    rwa [sq]
  have hW_nonneg : 0 ≤ ∑ i : Fin m, ∑ k : Fin d, (W i k - W₀ i k)^2 := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hW_sq : ∑ i : Fin m, ∑ k : Fin d, (W i k - W₀ i k)^2 ≤ B^2 := by
    have h1 := mul_le_mul hW hW (frobeniusNorm_nonneg _) hB
    rw [← sq] at h1
    unfold frobeniusNorm at h1
    rw [Real.sq_sqrt hW_nonneg] at h1
    rwa [sq]
  unfold frobeniusNorm
  have h_bound : ∑ i : Fin m, ∑ k : Fin d, (V i k - W i k)^2 ≤ (2 * B)^2 := by
    calc ∑ i : Fin m, ∑ k : Fin d, (V i k - W i k)^2
      _ ≤ 2 * (∑ i, ∑ k, (V i k - W₀ i k)^2) + 2 * (∑ i, ∑ k, (W i k - W₀ i k)^2) := h_sum
      _ ≤ 2 * B^2 + 2 * B^2 := by nlinarith [hV_sq, hW_sq]
      _ = (2 * B)^2 := by ring
  have h_B_nonneg : 0 ≤ 2 * B := by nlinarith [hB]
  have h_sq_le : Real.sqrt (∑ i, ∑ k, (V i k - W i k)^2) ≤ Real.sqrt ((2 * B)^2) := Real.sqrt_le_sqrt h_bound
  rwa [Real.sqrt_sq h_B_nonneg] at h_sq_le

-- Card bound for 3-way union of Finsets
private lemma card_union3_le {α : Type*} [DecidableEq α] (s1 s2 s3 : Finset α) :
    (s1 ∪ s2 ∪ s3).card ≤ s1.card + s2.card + s3.card := by
  have h1 := Finset.card_union_le (s1 ∪ s2) s3
  have h2 := Finset.card_union_le s1 s2
  omega

-- Constant scaling bound for 2nd order ReLU: 2√2 ≤ 3 and 4√2 ≤ 6
private lemma relu_secondOrder_scaling_bound
    (m : ℕ) (hm : m ≠ 0) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ < 1)
    (S_bound : ℝ)
    (h_alg : B / Real.sqrt (m : ℝ) * Real.sqrt S_bound ≤
      (2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) / (m : ℝ) ^ (1 / 6 : ℝ))
    (S_card : ℝ) (h_S_le : S_card ≤ 2 * S_bound) :
    (2 * B) / Real.sqrt (m : ℝ) * Real.sqrt S_card ≤
      (6 * B ^ (4 / 3 : ℝ) + 3 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) / (m : ℝ) ^ (1 / 6 : ℝ) := by
  have h_sqrt_S : Real.sqrt S_card ≤ Real.sqrt 2 * Real.sqrt S_bound := by
    have h_sqrt := Real.sqrt_le_sqrt h_S_le
    rwa [Real.sqrt_mul (by positivity)] at h_sqrt
  have h_sqrt2_3 : 2 * Real.sqrt 2 ≤ 3 := by
    have h1 : (2 * Real.sqrt 2)^2 = 8 := by ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
    have h2 : (3 : ℝ)^2 = 9 := by norm_num
    have h_sq_le : (2 * Real.sqrt 2)^2 ≤ (3 : ℝ)^2 := by linarith
    have h_pos1 : 0 ≤ 2 * Real.sqrt 2 := by positivity
    have h_pos2 : 0 ≤ (3 : ℝ) := by norm_num
    have h_abs := sq_le_sq.mp h_sq_le
    rwa [abs_of_nonneg h_pos1, abs_of_nonneg h_pos2] at h_abs
  have h_sqrt2_6 : 4 * Real.sqrt 2 ≤ 6 := by
    have h1 : (4 * Real.sqrt 2)^2 = 32 := by ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
    have h_sq_le : (4 * Real.sqrt 2)^2 ≤ (6 : ℝ)^2 := by linarith
    have h_pos1 : 0 ≤ 4 * Real.sqrt 2 := by positivity
    have h_pos2 : 0 ≤ (6 : ℝ) := by norm_num
    have h_abs := sq_le_sq.mp h_sq_le
    rwa [abs_of_nonneg h_pos1, abs_of_nonneg h_pos2] at h_abs
  have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1.le)
  have h_b1 : 0 ≤ B ^ (4 / 3 : ℝ) := Real.rpow_nonneg hB _
  have h_b2 : 0 ≤ B * Real.log (1 / δ) ^ (1 / 4 : ℝ) := mul_nonneg hB (Real.rpow_nonneg h_log_pos _)
  have h_m_pow_pos : 0 ≤ (m : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  calc (2 * B) / Real.sqrt (m : ℝ) * Real.sqrt S_card
    _ ≤ (2 * B) / Real.sqrt (m : ℝ) * (Real.sqrt 2 * Real.sqrt S_bound) := by
      have h_factor : 0 ≤ (2 * B) / Real.sqrt (m : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left h_sqrt_S h_factor
    _ = (2 * Real.sqrt 2) * (B / Real.sqrt (m : ℝ) * Real.sqrt S_bound) := by ring
    _ ≤ (2 * Real.sqrt 2) * ((2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) / (m : ℝ) ^ (1 / 6 : ℝ)) := by
      have h_factor : 0 ≤ 2 * Real.sqrt 2 := by positivity
      exact mul_le_mul_of_nonneg_left h_alg h_factor
    _ = (2 * Real.sqrt 2 * (2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ))) / (m : ℝ) ^ (1 / 6 : ℝ) := by ring
    _ ≤ (6 * B ^ (4 / 3 : ℝ) + 3 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) / (m : ℝ) ^ (1 / 6 : ℝ) := by
      have h_num1 : 2 * Real.sqrt 2 * (2 * B ^ (4 / 3 : ℝ)) ≤ 6 * B ^ (4 / 3 : ℝ) := by
        nlinarith [h_sqrt2_6, h_b1]
      have h_num2 : 2 * Real.sqrt 2 * (B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) ≤ 3 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ) := by
        nlinarith [h_sqrt2_3, h_b2]
      have h_sum_num : 2 * Real.sqrt 2 * (2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) ≤
          6 * B ^ (4 / 3 : ℝ) + 3 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ) := by linarith [h_num1, h_num2]
      exact div_le_div_of_nonneg_right h_sum_num h_m_pow_pos

/- For any additional `V` with `‖V − W₀‖_F ≤ B`:
  `|f(x; V) − (f(x; W) + ⟨∇_W f(x; W), V − W⟩_F)| ≤ (6B^{4/3} + 3B·(ln(1/δ))^{1/4}) / m^{1/6}`. -/
theorem reluLinearizationBound_secondOrder
    (net : ReLUNetwork d m)
    (x : Fin d → ℝ) (hx : x ⊙ x ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (gaussianInit m d).real {W₀ |
      ∀ W V : Fin m → Fin d → ℝ,
        frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B →
        frobeniusNorm (fun i k => V i k - W₀ i k) ≤ B →
          |net.eval x V -
           (net.eval x W +
            linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W V -
            net.eval x W)|
          ≤ (6 * B ^ (4 / 3 : ℝ) + 3 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) /
            (m : ℝ) ^ (1 / 6 : ℝ)} := by
  haveI : IsProbabilityMeasure (gaussianRowMeasure d) := by unfold gaussianRowMeasure; infer_instance
  haveI : IsProbabilityMeasure (gaussianInit m d) := by unfold gaussianInit; infer_instance
  have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_div hδ |>.mpr (le_of_lt hδ1))
  by_cases hx_pos : 0 < x ⊙ x
  swap
  · -- x = 0 case
    have hx_zero_norm : x ⊙ x = 0 := le_antisymm (not_lt.mp hx_pos) (innerProduct_self_nonneg x)
    have hx_zero : x = 0 := (innerProduct_eq_zero_iff_eq_zero x).mp hx_zero_norm
    subst hx_zero
    apply measure_ge_one_sub_delta_of_univ hδ
    intro W₀ W V _ _
    have heval0 : net.eval 0 V = 0 := by simp [ShallowNetwork.eval, relu, Finset.sum_const_zero]
    have hevalW0 : net.eval 0 W = 0 := by simp [ShallowNetwork.eval, relu, Finset.sum_const_zero]
    have hlin0 : linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs 0 W V = 0 := by
      simp [linearization, relu, reluDeriv, Finset.sum_const_zero]
    rw [heval0, hevalW0, hlin0, add_zero, sub_zero, sub_zero, abs_zero]
    positivity
  by_cases hm : m = 0
  · -- m = 0 case
    subst hm
    apply measure_ge_one_sub_delta_of_univ hδ
    intro W₀ W V _ _
    have heval0 : net.eval x V = 0 := by simp [ShallowNetwork.eval, Real.sqrt_zero]
    have hevalW0 : net.eval x W = 0 := by simp [ShallowNetwork.eval, Real.sqrt_zero]
    have hlin0 : linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W V = 0 := by
      simp [linearization, Real.sqrt_zero]
    rw [heval0, hevalW0, hlin0, add_zero, sub_zero, sub_zero, abs_zero]
    positivity
  by_cases hB_zero : B = 0
  · -- B = 0 case
    subst hB_zero
    apply measure_ge_one_sub_delta_of_univ hδ
    intro W₀ W V hW hV
    have hW_eq : W = W₀ := by
      have hnorm := frobeniusNorm_nonneg (fun i k => W i k - W₀ i k)
      have hnorm_zero : frobeniusNorm (fun i k => W i k - W₀ i k) = 0 := le_antisymm hW hnorm
      have hdiff := (frobeniusNorm_eq_zero (fun i k => W i k - W₀ i k)).mp hnorm_zero
      ext i k; exact sub_eq_zero.mp (congr_fun (congr_fun hdiff i) k)
    have hV_eq : V = W₀ := by
      have hnorm := frobeniusNorm_nonneg (fun i k => V i k - W₀ i k)
      have hnorm_zero : frobeniusNorm (fun i k => V i k - W₀ i k) = 0 := le_antisymm hV hnorm
      have hdiff := (frobeniusNorm_eq_zero (fun i k => V i k - W₀ i k)).mp hnorm_zero
      ext i k; exact sub_eq_zero.mp (congr_fun (congr_fun hdiff i) k)
    rw [hW_eq, hV_eq]
    have hlin : linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W₀ W₀ = net.eval x W₀ := by
      simp [linearization, ShallowNetwork.eval, sub_self, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hlin, add_sub_cancel_left, sub_self, abs_zero]
    positivity
  have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB_zero)
  let r := B ^ (2 / 3 : ℝ) / (m : ℝ) ^ (1 / 3 : ℝ)
  have hr : 0 < r := by
    apply div_pos
    · exact Real.rpow_pos_of_pos hB_pos _
    · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) _
  have h_sign_conc := reluSignConcentration (m := m) x hx_pos r hr δ hδ hδ1
  have h_compl : {W₀ : Fin m → Fin d → ℝ | ((signAmbiguous r x W₀).card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))} =
    {W₀ : Fin m → Fin d → ℝ | (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) < ((signAmbiguous r x W₀).card : ℝ)}ᶜ := by
    ext W₀
    simp only [Set.mem_ofPred, Set.mem_compl_iff]
    exact not_lt.symm
  apply le_trans (b := (gaussianInit m d).real {W₀ | ((signAmbiguous r x W₀).card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))})
  · rw [h_compl, measureReal_compl]
    · have h_prob_univ : (gaussianInit m d).real Set.univ = 1 := by simp
      rw [h_prob_univ]
      exact sub_le_sub_left h_sign_conc 1
    · exact measurableSet_lt measurable_const (measurable_signAmbiguous_card r x)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro W₀ h_W₀ W V h_W h_V
  let S1 := signAmbiguous r x W₀
  let S2 := largePerturb r W W₀
  let S3 := largePerturb r V W₀
  let S := S1 ∪ S2 ∪ S3
  have h_S1 : (S1.card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) := h_W₀
  have h_S2 : (S2.card : ℝ) ≤ (B / r) ^ 2 := card_largePerturb_bound W W₀ r B hr h_W
  have h_S3 : (S3.card : ℝ) ≤ (B / r) ^ 2 := card_largePerturb_bound V W₀ r B hr h_V
  have h_S_card : (S.card : ℝ) ≤ (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) + 2 * (B / r) ^ 2 := by
    have h1 : S.card ≤ S1.card + S2.card + S3.card := card_union3_le S1 S2 S3
    have h2 : (S.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by exact_mod_cast h1
    linarith
  have h_frob_VW : frobeniusNorm (fun i k => V i k - W i k) ≤ 2 * B := frob_sub_le V W W₀ B hB h_V h_W
  have h_diff_S : |net.eval x V - (net.eval x W + linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W V - net.eval x W)| ≤ (2 * B) / Real.sqrt (m : ℝ) * Real.sqrt (S.card : ℝ) := by
    have h_ring : net.eval x V - (net.eval x W + linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W V - net.eval x W) =
        net.eval x V - linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W V := by ring
    rw [h_ring]
    have h_sub_eq := relu_eval_sub_linearization_eq net x V W
    rw [h_sub_eq]
    have hj_badW : ∀ j : Fin m, j ∉ S → j ∉ badSet r r x W W₀ := fun j hj h => hj (Finset.mem_union_left S3 h)
    have hj_badV : ∀ j : Fin m, j ∉ S → j ∉ badSet r r x V W₀ := fun j hj h => by
      rcases Finset.mem_union.mp h with h1 | h3
      · exact hj (Finset.mem_union_left S3 (Finset.mem_union_left S2 h1))
      · exact hj (Finset.mem_union_right (S1 ∪ S2) h3)
    have h_zero : ∀ j : Fin m, j ∉ S →
        net.outerCoeffs j * relu (∑ k, V j k * x k) -
        net.outerCoeffs j * reluDeriv (∑ k, W j k * x k) * ∑ k, V j k * x k = 0 := by
      intro j hj
      have h_sign_W := sign_preserved_outside_badSet r hr x W W₀ j (hj_badW j hj)
      have h_sign_V := sign_preserved_outside_badSet r hr x V W₀ j (hj_badV j hj)
      dsimp [relu, reluDeriv]
      rw [mul_assoc, ← mul_sub]
      split_ifs with h_W
      · have h_W₀ : 0 ≤ ∑ k, W₀ j k * x k := h_sign_W.mp h_W
        have h_V : 0 ≤ ∑ k, V j k * x k := h_sign_V.mpr h_W₀
        rw [max_eq_left h_V, one_mul, sub_self, mul_zero]
      · push Not at h_W
        have h_W₀ : ¬(0 ≤ ∑ k, W₀ j k * x k) := fun h => by linarith [h_sign_W.mpr h, h_W]
        have h_V : ¬(0 ≤ ∑ k, V j k * x k) := fun h => by linarith [h_sign_V.mp h, h_W₀]
        push Not at h_V
        rw [max_eq_right h_V.le, zero_mul, sub_zero, mul_zero]
    have h_sum : ∑ j : Fin m, (net.outerCoeffs j * relu (∑ k, V j k * x k) -
        net.outerCoeffs j * reluDeriv (∑ k, W j k * x k) * ∑ k, V j k * x k) =
        ∑ j ∈ S, (net.outerCoeffs j * relu (∑ k, V j k * x k) -
        net.outerCoeffs j * reluDeriv (∑ k, W j k * x k) * ∑ k, V j k * x k) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact h_zero j hj
    rw [h_sum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h_sum_le := relu_error_sum_le net x V W S
    have h_sum_cs := relu_error_cs_bound x hx V W (2 * B) h_frob_VW S
    calc (m : ℝ)⁻¹.sqrt * |∑ j ∈ S, (net.outerCoeffs j * relu (∑ k, V j k * x k) -
          net.outerCoeffs j * reluDeriv (∑ k, W j k * x k) * ∑ k, V j k * x k)|
      _ ≤ (m : ℝ)⁻¹.sqrt * ∑ j ∈ S, |∑ k, (V j k - W j k) * x k| :=
        mul_le_mul_of_nonneg_left h_sum_le (Real.sqrt_nonneg _)
      _ ≤ (m : ℝ)⁻¹.sqrt * (Real.sqrt (S.card : ℝ) * (2 * B)) :=
        mul_le_mul_of_nonneg_left h_sum_cs (Real.sqrt_nonneg _)
      _ = (2 * B) / Real.sqrt (m : ℝ) * Real.sqrt (S.card : ℝ) := by
        rw [Real.sqrt_inv]
        ring
  have h_alg := reluLinearization_algebraic_bound m (Nat.pos_of_ne_zero hm) B δ hB hδ hδ1
  have h_bound : (2 * B) / Real.sqrt (m : ℝ) * Real.sqrt (S.card : ℝ) ≤
      (6 * B ^ (4 / 3 : ℝ) + 3 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) / (m : ℝ) ^ (1 / 6 : ℝ) := by
    let S_bound := (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) + (B / r) ^ 2
    have h_mr : 0 ≤ (m : ℝ) * r := by positivity
    have h_sqrt_pos : 0 ≤ Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) := Real.sqrt_nonneg _
    have h_br : 0 ≤ (B / r) ^ 2 := by positivity
    have h_S_le : (S.card : ℝ) ≤ 2 * S_bound := by
      dsimp [S_bound]
      linarith [h_S_card, h_mr, h_sqrt_pos, h_br]
    exact relu_secondOrder_scaling_bound m hm B δ hB hδ hδ1 S_bound h_alg (S.card : ℝ) h_S_le
  exact h_diff_S.trans h_bound

end NTK

end
