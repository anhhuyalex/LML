/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Kernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Moments.SubGaussian

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

lemma BetaSmooth.β_nonneg {σ : ℝ → ℝ} {β : ℝ} (h : BetaSmooth σ β) : 0 ≤ β := by
  have := h.hessian_bound 0
  linarith [abs_nonneg (deriv (deriv σ) 0)]

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
    have h3 : HasDerivAt (fun t => t - s) 1 x := by
      have : HasDerivAt (fun t => t) 1 x := hasDerivAt_id x
      exact this.sub_const s
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
    (∑ k : Fin d, (W j k - V j k)^2) * (∑ k : Fin d, (x k)^2) := by
    intro j
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => W j k - V j k) x
  have h_cs_sum : ∑ j : Fin m, (∑ k, (W j k - V j k) * x k)^2 ≤
    ∑ j : Fin m, ((∑ k, (W j k - V j k)^2) * (∑ k, (x k)^2)) := Finset.sum_le_sum fun j _ => h_cs j
  have h_x_bound : ∑ k : Fin d, (x k)^2 = x ⊙ x := (innerProduct_self_eq_sum_sq x).symm
  have h_frob : ∑ j : Fin m, (∑ k, (W j k - V j k)^2) * (x ⊙ x)
    = (∑ j : Fin m, ∑ k, (W j k - V j k)^2) * (x ⊙ x) := by rw [← Finset.sum_mul]
  have h_frob_def :
      ∑ j : Fin m, ∑ k, (W j k - V j k)^2 =
        frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
    dsimp [frobeniusNorm]
    have h_nonneg : 0 ≤ ∑ i : Fin m, ∑ j : Fin d, (W i j - V i j) ^ 2 := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact sq_nonneg _
    rw [Real.sq_sqrt h_nonneg]
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

open Classical in
lemma prob_signAmbiguous_le_tau {d : ℕ} (x : Fin d → ℝ) (hx : 0 < x ⊙ x) (τ : ℝ) (hτ : 0 < τ) :
    (gaussianRowMeasure d).real {w | |∑ k, w k * x k| ≤ τ * Real.sqrt (x ⊙ x)} ≤ τ := by
  sorry

open Classical in
lemma hoeffding_indicators_pi
    (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (p : ℝ) (hp : μ.real S ≤ p)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin m => μ)).real
      {ω : Fin m → Ω | (m : ℝ) * p + t < (Finset.univ.filter (fun j => ω j ∈ S)).card}
      ≤ Real.exp (- 2 * t ^ 2 / m) := by
  sorry

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
    have h_empty :
        {W₀ : Fin 0 → Fin d → ℝ |
          ((0 : ℕ) : ℝ) * τ + Real.sqrt (((0 : ℕ) : ℝ) / 2 * Real.log (1 / δ)) <
            ↑(signAmbiguous τ x W₀).card} = ∅ := by
      ext W₀
      have h_card : (signAmbiguous τ x W₀).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty _)
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      rw [h_card]
      simp
    rw [h_empty, measureReal_empty]
    exact hδ.le
  have h_m_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have h_prob := prob_signAmbiguous_le_tau x hx τ hτ
  have h_t_nonneg : 0 ≤ Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) := Real.sqrt_nonneg _
  -- We must provide IsProbabilityMeasure for gaussianRowMeasure
  haveI : IsProbabilityMeasure (gaussianRowMeasure d) := by sorry
  have h_hoeffding := hoeffding_indicators_pi m (gaussianRowMeasure d)
    {w | |∑ k, w k * x k| ≤ τ * Real.sqrt (x ⊙ x)} τ h_prob
    (Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))) h_t_nonneg
  have h_one_lt_div : 1 ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have h_log_pos : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h_one_lt_div
  have h_sq :
      (Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))) ^ 2 =
        (m : ℝ) / 2 * Real.log (1 / δ) :=
    Real.sq_sqrt (mul_nonneg (div_nonneg (Nat.cast_nonneg m) zero_le_two) h_log_pos)
  have h_calc :
      -2 * (Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ))) ^ 2 / (m : ℝ) =
        -Real.log (1 / δ) := by
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
    (τ : ℝ) (hτ : 0 < τ)
    (x : Fin d → ℝ)
    (W W₀ : Fin m → Fin d → ℝ)
    (j : Fin m) (hj : j ∉ badSet τ τ x W W₀) :
    (0 ≤ ∑ k : Fin d, W j k * x k) ↔
    (0 ≤ ∑ k : Fin d, W₀ j k * x k) := by
  sorry

/-! ### ReLU linearization bound (Lemma 4.1) -/

/-- The ReLU activation. Bundled here for convenience. -/
noncomputable def relu : ℝ → ℝ := fun z => max z 0

/-- The subgradient / derivative of ReLU (a.e. equal to the indicator): `σ'(z) = 𝟏[z ≥ 0]`. -/
noncomputable def reluDeriv : ℝ → ℝ := fun z => if 0 ≤ z then 1 else 0

/-- Scaled shallow network with ReLU activation. -/
abbrev ReLUNetwork (d m : ℕ) := ShallowNetwork relu d m

lemma relu_error_eq_zero_outside_badSet
    {d m : ℕ} (net : ReLUNetwork d m) (x : Fin d → ℝ) (W W₀ : Fin m → Fin d → ℝ)
    (r τ : ℝ) (hτ : 0 < τ)
    (j : Fin m) (hj : j ∉ badSet τ r x W W₀) :
    net.outerCoeffs j * relu (∑ k, W j k * x k) -
    net.outerCoeffs j * reluDeriv (∑ k, W₀ j k * x k) * (∑ k, W j k * x k) = 0 := by
  sorry

lemma relu_linearization_error_le (a b : ℝ) :
    |relu a - reluDeriv b * a| ≤ |a - b| := by
  sorry

lemma card_largePerturb_bound
    {d m : ℕ} (W W₀ : Fin m → Fin d → ℝ) (r B : ℝ) (hr : 0 < r)
    (h_frob : frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B) :
    (largePerturb r W W₀).card ≤ (B / r) ^ 2 := by
  sorry

lemma reluLinearization_algebraic_bound
    (m : ℕ) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let r := B ^ (2/3 : ℝ) / (m : ℝ) ^ (1/3 : ℝ)
    let S_bound := (m : ℝ) * r + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) + (B / r) ^ 2
    B / Real.sqrt m * Real.sqrt S_bound ≤
      (2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) /
        (m : ℝ) ^ (1 / 6 : ℝ) := by
  sorry

/-- **Lemma 4.1** (Telgarsky 2021, main ReLU linearization bound).
Let `net` be a ReLU network, `W₀ ~ 𝒩(0, Iᵈ)^{⊗m}`, `B ≥ 0`, and `‖x‖ ≤ 1`.
With probability at least `1 − δ` over `W₀`, for every `W` with `‖W − W₀‖_F ≤ B`:
  `|f(x; W) − f₀(x; W)| ≤ (2B^{4/3} + B·(ln(1/δ))^{1/4}) / m^{1/6}`.

**Proof sketch:**
1. Choose the balancing radius `r = B^{2/3}/m^{1/3}`.
2. Define `S = S₁ ∪ S₂` where `S₁ = signAmbiguous r x W₀` and `S₂ = largePerturb r W W₀`.
3. By `reluSignConcentration`, `|S₁| ≤ rm + √(m ln(1/δ)/2)` w.p. ≥ 1−δ.
4. By Frobenius bound, `|S₂| ≤ B²/r²`.
5. The choice of `r` gives `|S| ≤ m^{2/3}(2B^{2/3} + √(ln(1/δ)))`.
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
  sorry

/-- **Corollary** (second part of Lemma 4.1): second-order Taylor error for ReLU.
For any additional `V` with `‖V − W₀‖_F ≤ B`:
  `|f(x; V) − (f(x; W) + ⟨∇_W f(x; W), V − W⟩_F)| ≤ (6B^{4/3} + 2B·(ln(1/δ))^{1/4}) / m^{1/6}`. -/
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
          ≤ (6 * B ^ (4 / 3 : ℝ) + 2 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) /
            (m : ℝ) ^ (1 / 6 : ℝ)} := by
  sorry

end NTK

end
