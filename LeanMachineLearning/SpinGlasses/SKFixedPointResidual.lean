/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSecondaryContraction

/-!
# The fixed-point residual `|x - Φ(x)|` (Talagrand, proof of Proposition 1.9.5)

Let `Φ(x) = 𝔼 tanh²(β √x z + h)`.  For `h ≠ 0` we show that `x ↦ Φ(x)/x` is strictly decreasing on
`(0, ∞)` (Proposition A.14.1 for `tanh`, from `integral_tanh_core_lt`), and deduce that the fixed
point `q` is the only zero of `x - Φ(x)` on `[0, 1]` and that `|x - Φ(x)| ≥ |x - q|/K` there.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.9.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace SpinGlasses

/-- `x`-derivative of `Φ(x) = 𝔼 tanh²(β √x z + h)` for `x > 0`:
`Φ'(x) = β² 𝔼[(1 - tanh²)(1 - 3 tanh²)]`. -/
theorem hasDerivAt_fixedPointMap_sqrt (β h : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => ∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1))
      (β ^ 2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1)) x := by
  have h1 := hasDerivAt_fixedPointMap_param h (β * Real.sqrt x)
  have h2 : HasDerivAt (fun y : ℝ => β * Real.sqrt y) (β * (1 / (2 * Real.sqrt x))) x :=
    (Real.hasDerivAt_sqrt hx.ne').const_mul β
  have h3 := h1.comp x h2
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have e : ∫ z : ℝ, 2 * (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
      (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) =
      2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [e] at h3
  refine h3.congr_deriv ?_
  generalize (∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
    (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1)) = I
  field_simp

/-- For `h ≠ 0`, `𝔼 tanh²(w z + h) > 0`. -/
theorem fixedPointMap_pos {h : ℝ} (hh : h ≠ 0) (w : ℝ) :
    0 < ∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  refine integral_pos_of_integrable_nonneg_nonzero (x := 0) (continuous_tanh_sq_affine w h)
    (integrable_tanh_sq_affine w h) (fun z => sq_nonneg _) ?_
  have : Real.tanh h ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (fun h0 => hh (Real.sinh_eq_zero.1 h0)) (Real.cosh_pos h).ne'
  simpa using this

/-- **Proposition A.14.1 for `tanh` at every point:** for `x > 0` and `h ≠ 0`,
`x Φ'(x) < Φ(x)`. -/
theorem x_mul_deriv_fixedPointMap_lt {h : ℝ} (hh : h ≠ 0) (β : ℝ) {x : ℝ} (hx : 0 < x) :
    x * (β ^ 2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1)) <
      ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  have hpos := fixedPointMap_pos hh (β * Real.sqrt x)
  by_cases hβ : β = 0
  · subst hβ
    simpa using hpos
  · have hw : β * Real.sqrt x ≠ 0 := mul_ne_zero hβ (Real.sqrt_pos.2 hx).ne'
    have key := integral_tanh_core_lt hw h
    rw [integral_tanh_sq_deriv_mul_id_eq h (β * Real.sqrt x)] at key
    have e : ∫ z : ℝ, 2 * (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) =
        2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
          (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun z => by ring)
    rw [e] at key
    have hsq : (β * Real.sqrt x) * (β * Real.sqrt x) = β ^ 2 * x := by
      rw [← mul_mul_mul_comm, Real.mul_self_sqrt hx.le]; ring
    generalize (∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
      (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1)) = I at key ⊢
    have e2 : (β * Real.sqrt x) * ((β * Real.sqrt x) * (2 * I)) = 2 * (x * (β ^ 2 * I)) := by
      rw [← mul_assoc, hsq]; ring
    linarith only [key, e2]

/-- **`Φ(x)/x` is strictly decreasing on `(0, ∞)`** (`h ≠ 0`; Proposition A.14.1 for `tanh`). -/
theorem strictAntiOn_fixedPointMap_div {h : ℝ} (hh : h ≠ 0) (β : ℝ) :
    StrictAntiOn (fun y : ℝ =>
      (∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)) / y) (Ioi 0) := by
  have hd : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ =>
      (∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)) / y)
      (((β ^ 2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt y * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt y * z + h) ^ 2) ∂(gaussianReal 0 1)) * y -
        (∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)) * 1) / y ^ 2) y :=
    fun y hy => (hasDerivAt_fixedPointMap_sqrt β h hy).div (hasDerivAt_id y) (ne_of_gt hy)
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt) fun y hy => ?_
  rw [interior_Ioi] at hy
  rw [(hd y hy).deriv]
  have := x_mul_deriv_fixedPointMap_lt hh β hy
  have hy2 : 0 < y ^ 2 := by have : (0 : ℝ) < y := hy; positivity
  apply div_neg_of_neg_of_pos _ hy2
  nlinarith only [this]

/-- **Linear lower bound for the fixed-point residual** (`h ≠ 0`; Talagrand, proof of
Proposition 1.9.5): if `q` is a fixed point of `Φ(x) = 𝔼 tanh²(β √x z + h)` and
`q̂ = 𝔼 tanh⁴(β√q z + h)`, there is `K > 0` with `|x - q| ≤ K |x - Φ(x)|` for all `x ∈ [0, 1]`.
The proof: near `q` use `Φ'(q) = β²(1 - 4q + 3q̂) < 1` (Lemma 1.9.3); away from `q` use that
`Φ(x)/x` is strictly decreasing, and near `0` that `Φ(0) = tanh² h > 0`. -/
theorem exists_abs_sub_le_mul_abs_sub_fixedPointMap {β h q qhat : ℝ} (hh : h ≠ 0)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |x - q| ≤ K * |x - ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)| := by
  set Φ : ℝ → ℝ := fun y => ∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)
    with hΦ
  have hq0 : 0 < q := by
    have := fixedPointMap_pos hh (β * Real.sqrt q)
    rwa [hfix] at this
  have hq1 : q ≤ 1 := (fixedPoint_mem_Icc hfix).2
  have hΦq : Φ q = q := hfix
  have hΦpos : ∀ y, 0 < Φ y := fun y => fixedPointMap_pos hh (β * Real.sqrt y)
  set D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qhat) with hD
  have hD0 : 0 < D := by
    have := sk_beta_sq_mul_one_sub_four_add_three_lt_one hq0 hfix hqhat
    linarith
  -- the derivative of `x - Φ x` at `q`
  have hI : ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt q * z + h) ^ 2) *
      (1 - 3 * Real.tanh (β * Real.sqrt q * z + h) ^ 2) ∂(gaussianReal 0 1) =
      1 - 4 * q + 3 * qhat := by
    have h2 := integral_tanh_sq_second_deriv_eq hfix hqhat
    have e : ∫ z : ℝ, 2 * (1 - Real.tanh (β * Real.sqrt q * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt q * z + h) ^ 2) ∂(gaussianReal 0 1) =
        2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt q * z + h) ^ 2) *
          (1 - 3 * Real.tanh (β * Real.sqrt q * z + h) ^ 2) ∂(gaussianReal 0 1) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun z => by ring)
    linarith
  have hdΦ := hasDerivAt_fixedPointMap_sqrt β h hq0
  rw [hI] at hdΦ
  have hr : HasDerivAt (fun y : ℝ => y - Φ y) D q := (hasDerivAt_id' q).sub hdΦ
  have hlo := hr.isLittleO.def (c := D / 2) (by positivity)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hlo
  set ε' : ℝ := min ε (q / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by positivity)
  have hε'q : ε' ≤ q / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  -- monotonicity constants
  have hanti := strictAntiOn_fixedPointMap_div hh β
  have hψq : Φ q / q = 1 := by rw [hΦq]; exact div_self hq0.ne'
  have hc1 : 0 < 1 - Φ (q + ε') / (q + ε') := by
    have : Φ (q + ε') / (q + ε') < Φ q / q :=
      hanti (show q ∈ Ioi (0 : ℝ) from hq0) (show q + ε' ∈ Ioi (0 : ℝ) by
        simp only [mem_Ioi]; linarith) (by linarith)
    rw [hψq] at this
    linarith
  have hc2 : 0 < Φ (q - ε') / (q - ε') - 1 := by
    have : Φ q / q < Φ (q - ε') / (q - ε') :=
      hanti (show q - ε' ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith)
        (show q ∈ Ioi (0 : ℝ) from hq0) (by linarith)
    rw [hψq] at this
    linarith
  set c1 : ℝ := 1 - Φ (q + ε') / (q + ε') with hc1def
  set c2 : ℝ := Φ (q - ε') / (q - ε') - 1 with hc2def
  -- behaviour near `0`
  have hT0 : 0 < Φ 0 := hΦpos 0
  have hcont : ContinuousAt Φ 0 := (continuous_fixedPointMap β h).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.continuousAt_iff.1 hcont (Φ 0 / 2) (by positivity)
  set δ₀ : ℝ := min δ₁ (Φ 0 / 4) with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min hδ₁ (by positivity)
  set K : ℝ := 2 / D + 1 / (q * c1) + 1 / (δ₀ * c2) + 4 / Φ 0 with hK
  have hK1 : 0 ≤ 2 / D := by positivity
  have hK2 : 0 ≤ 1 / (q * c1) := by positivity
  have hK3 : 0 ≤ 1 / (δ₀ * c2) := by positivity
  have hK4 : 0 ≤ 4 / Φ 0 := by positivity
  refine ⟨K, by positivity, fun x hx => ?_⟩
  obtain ⟨hx0, hx1⟩ := hx
  have hxq : |x - q| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have habs : 0 ≤ |x - Φ x| := abs_nonneg _
  change |x - q| ≤ K * |x - Φ x|
  have hcoef : ∀ c : ℝ, 0 ≤ c → c ≤ K → |x - q| ≤ c * |x - Φ x| → |x - q| ≤ K * |x - Φ x| :=
    fun c _ hcK h => h.trans (mul_le_mul_of_nonneg_right hcK habs)
  rcases lt_or_ge |x - q| ε' with h1 | h1
  · -- near `q`
    have h0 := hεb (y := x) (by rw [Real.dist_eq]; exact lt_of_lt_of_le h1 hε'ε)
    have h3 : |x - Φ x - (x - q) * D| ≤ D / 2 * |x - q| := by
      simpa [smul_eq_mul, Real.norm_eq_abs, hΦq] using h0
    have h4 := abs_sub (x - Φ x) (x - Φ x - (x - q) * D)
    rw [sub_sub_cancel, abs_mul, abs_of_pos hD0] at h4
    have h5 : D / 2 * |x - q| ≤ |x - Φ x| := by nlinarith only [h3, h4]
    refine hcoef (2 / D) (by positivity) (by linarith only [hK1, hK2, hK3, hK4, hK]) ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hD0]
    nlinarith only [h5]
  · rcases le_or_gt (q + ε') x with h2 | h2
    · -- to the right of `q`
      have hxpos : 0 < x := by linarith
      have hmono : Φ x / x ≤ Φ (q + ε') / (q + ε') :=
        hanti.antitoneOn (show q + ε' ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith)
          (show x ∈ Ioi (0 : ℝ) from hxpos) h2
      have h6 : Φ x ≤ (1 - c1) * x := by
        rw [div_le_iff₀ hxpos] at hmono
        rw [hc1def]
        linarith only [hmono]
      have h7 : q * c1 ≤ |x - Φ x| := by
        have : x * c1 ≤ x - Φ x := by nlinarith only [h6]
        have h8 : q * c1 ≤ x * c1 := mul_le_mul_of_nonneg_right (by linarith) hc1.le
        exact (le_trans (by linarith only [h8, this]) (le_abs_self _))
      refine hcoef (1 / (q * c1)) (by positivity) (by linarith only [hK1, hK2, hK3, hK4, hK]) ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith only [h7, mul_nonneg (sub_nonneg.2 hxq) (mul_pos hq0 hc1).le]
    · -- to the left of `q`
      have hxl : x ≤ q - ε' := by
        rcases abs_cases (x - q) with ⟨h9, _⟩ | ⟨h9, _⟩
        · linarith only [h9, h1, h2]
        · linarith only [h9, h1]
      rcases lt_or_ge x δ₀ with h10 | h10
      · -- near `0`
        have h11 := hδ₁b (x := x) (by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0]
          exact lt_of_lt_of_le h10 (min_le_left _ _))
        rw [Real.dist_eq] at h11
        have h12 := (abs_lt.1 h11).1
        have h13 : δ₀ ≤ Φ 0 / 4 := min_le_right _ _
        have h14 : Φ 0 / 4 ≤ |x - Φ x| := by
          rw [abs_sub_comm]
          refine le_trans ?_ (le_abs_self _)
          linarith only [h12, h10, h13]
        refine hcoef (4 / Φ 0) (by positivity) (by linarith only [hK1, hK2, hK3, hK4, hK]) ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ hT0]
        nlinarith only [h14, mul_nonneg (sub_nonneg.2 hxq) hT0.le]
      · have hxpos : 0 < x := lt_of_lt_of_le hδ₀0 h10
        have hmono : Φ (q - ε') / (q - ε') ≤ Φ x / x :=
          hanti.antitoneOn (show x ∈ Ioi (0 : ℝ) from hxpos)
            (show q - ε' ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith) hxl
        have h6 : (1 + c2) * x ≤ Φ x := by
          rw [le_div_iff₀ hxpos] at hmono
          rw [hc2def]
          nlinarith only [hmono]
        have h7 : δ₀ * c2 ≤ |x - Φ x| := by
          have : x * c2 ≤ Φ x - x := by nlinarith only [h6]
          have h8 : δ₀ * c2 ≤ x * c2 := mul_le_mul_of_nonneg_right h10 hc2.le
          rw [abs_sub_comm]
          exact le_trans (by linarith only [h8, this]) (le_abs_self _)
        refine hcoef (1 / (δ₀ * c2)) (by positivity) (by linarith only [hK1, hK2, hK3, hK4, hK])
          ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith only [h7, mul_nonneg (sub_nonneg.2 hxq) (mul_pos hδ₀0 hc2).le]

end SpinGlasses
