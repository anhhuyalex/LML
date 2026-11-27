/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Estimates for differences of square roots

* `Real.sqrt_add_le_add_sqrt`: `√(a + b) ≤ √a + √b` for all `a, b`.
* `Real.sq_sqrt_sub_le_abs_sub`: `(√a - √b)² ≤ |a - b|` for all `a, b`.
* `Real.sq_sqrt_sub_le`: `(√q - a)² ≤ (q - a²)² / q` for `q > 0`, `a ≥ 0`.
* `Real.inv_sqrt_mul_self`: `(√n)⁻¹ * (√n)⁻¹ = n⁻¹` for `n ≥ 0`.
* `Real.abs_one_div_two_mul_sqrt_le`: `|1 / (2 √v)| ≤ 1 / (2 √δ)` when `0 < δ ≤ v`.
* `hasDerivAt_sqrt_smul_add_sqrt_one_sub_smul` (real case
  `hasDerivAt_sqrt_mul_add_sqrt_one_sub_mul`): derivative of `s ↦ √s a + √(1 - s) b` at
  `t ∉ {0, 1}`, for `a, b` in a normed space.
* `norm_one_div_two_sqrt_smul_sub_le` (real case `abs_div_two_sqrt_sub_le`): that derivative has
  norm at most `(‖a‖ + ‖b‖) / (2 √δ)` when `δ ≤ t ≤ 1 - δ`.
-/

@[expose] public section

namespace Real

/-- `(√n)⁻¹ * (√n)⁻¹ = n⁻¹` for `n ≥ 0`. -/
theorem inv_sqrt_mul_self (n : ℝ) (hn : 0 ≤ n) :
    (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = n⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hn]

/-- The singular factor `1 / (2 √v)` of a square-root path is bounded away from `0`. -/
theorem abs_one_div_two_mul_sqrt_le {δ v : ℝ} (hδ : 0 < δ) (h : δ ≤ v) :
    |1 / (2 * Real.sqrt v)| ≤ 1 / (2 * Real.sqrt δ) := by
  rw [abs_of_nonneg (by positivity)]
  gcongr

/-- `√(a + b) ≤ √a + √b`: for nonnegative `a, b` because `(√a + √b)² = a + b + 2 √a √b`; a
negative argument has square root `0` and only lowers the left side. -/
theorem sqrt_add_le_add_sqrt (a b : ℝ) : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rcases le_total a 0 with ha | ha
  · rw [Real.sqrt_eq_zero_of_nonpos ha, zero_add]
    exact Real.sqrt_le_sqrt (by linarith)
  rcases le_total b 0 with hb | hb
  · rw [Real.sqrt_eq_zero_of_nonpos hb, add_zero]
    exact Real.sqrt_le_sqrt (by linarith)
  exact Real.sqrt_le_iff.2 ⟨by positivity, by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a)
      (Real.sqrt_nonneg b)]⟩

/-- `(√a - √b)² ≤ |a - b|`, since `|√a - √b| ≤ √|a - b|` by subadditivity of `√`. -/
theorem sq_sqrt_sub_le_abs_sub (a b : ℝ) : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have key : ∀ x y : ℝ, Real.sqrt x - Real.sqrt y ≤ Real.sqrt |x - y| := fun x y => by
    have h := (Real.sqrt_le_sqrt (show x ≤ y + |x - y| by linarith [le_abs_self (x - y)])).trans
      (sqrt_add_le_add_sqrt y |x - y|)
    linarith
  have h : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| :=
    abs_sub_le_iff.2 ⟨key a b, by rw [abs_sub_comm]; exact key b a⟩
  calc (Real.sqrt a - Real.sqrt b) ^ 2 = |Real.sqrt a - Real.sqrt b| ^ 2 := (sq_abs _).symm
    _ ≤ Real.sqrt |a - b| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = |a - b| := Real.sq_sqrt (abs_nonneg _)

/-- `(√q - a)² ≤ (q - a²)² / q` for `q > 0`, `a ≥ 0`, because
`(q - a²)² = (√q - a)² (√q + a)²` and `(√q + a)² ≥ q`. -/
theorem sq_sqrt_sub_le {q a : ℝ} (hq : 0 < q) (ha : 0 ≤ a) :
    (Real.sqrt q - a) ^ 2 ≤ (q - a ^ 2) ^ 2 / q := by
  have key : ∀ s : ℝ, 0 < s → (s - a) ^ 2 ≤ (s ^ 2 - a ^ 2) ^ 2 / s ^ 2 := fun s hs => by
    rw [le_div_iff₀ (by positivity)]
    have hid : (s ^ 2 - a ^ 2) ^ 2 - (s - a) ^ 2 * s ^ 2 = (s - a) ^ 2 * (a * (2 * s + a)) := by
      ring
    have : 0 ≤ (s - a) ^ 2 * (a * (2 * s + a)) := by positivity
    linarith
  have := key (Real.sqrt q) (Real.sqrt_pos.mpr hq)
  rwa [Real.sq_sqrt hq.le] at this

/-- Derivative of `s ↦ √(s / L)` for `0 ≤ L` and `z ≠ 0`. -/
theorem hasDerivAt_sqrt_div_const {L z : ℝ} (hL : 0 ≤ L) (hz : z ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.sqrt (s / L)) (1 / (2 * Real.sqrt z) / Real.sqrt L) z := by
  have e : (fun s : ℝ => Real.sqrt (s / L)) = fun s => Real.sqrt s / Real.sqrt L :=
    funext fun s => Real.sqrt_div' s hL
  rw [e]
  exact (Real.hasDerivAt_sqrt hz).div_const (Real.sqrt L)

end Real

/-- Derivative of `s ↦ √s • a + √(1 - s) • b` at `t ∉ {0, 1}`. -/
theorem hasDerivAt_sqrt_smul_add_sqrt_one_sub_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a b : E) :
    HasDerivAt (fun s : ℝ => Real.sqrt s • a + Real.sqrt (1 - s) • b)
      ((1 / (2 * Real.sqrt t)) • a - (1 / (2 * Real.sqrt (1 - t))) • b) t := by
  have h1 := (Real.hasDerivAt_sqrt ht0).smul_const a
  have h2 := (((hasDerivAt_id t).const_sub 1).sqrt (sub_ne_zero.2 ht1.symm)).smul_const b
  exact (h1.add h2).congr_deriv (by rw [neg_div, neg_smul, ← sub_eq_add_neg]; rfl)

/-- Derivative of `s ↦ √s * a + √(1 - s) * b` at `t ∉ {0, 1}`. -/
theorem hasDerivAt_sqrt_mul_add_sqrt_one_sub_mul {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a b : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sqrt s * a + Real.sqrt (1 - s) * b)
      (a / (2 * Real.sqrt t) - b / (2 * Real.sqrt (1 - t))) t :=
  (hasDerivAt_sqrt_smul_add_sqrt_one_sub_smul ht0 ht1 a b).congr_deriv
    (by simp only [smul_eq_mul, one_div_mul_eq_div])

/-- Uniform inverse-square-root bound on `‖(1 / (2 √t)) • a - (1 / (2 √(1 - t))) • b‖` when
`δ ≤ t` and `δ ≤ 1 - t` (`δ > 0`). -/
theorem norm_one_div_two_sqrt_smul_sub_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {δ t : ℝ} (hδ : 0 < δ) (h1 : δ ≤ t) (h2 : δ ≤ 1 - t) (a b : E) :
    ‖(1 / (2 * Real.sqrt t)) • a - (1 / (2 * Real.sqrt (1 - t))) • b‖ ≤
      (‖a‖ + ‖b‖) / (2 * Real.sqrt δ) := by
  have h : ∀ v, δ ≤ v → ∀ x : E, ‖(1 / (2 * Real.sqrt v)) • x‖ ≤ ‖x‖ / (2 * Real.sqrt δ) :=
    fun v hv x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (Real.abs_one_div_two_mul_sqrt_le hδ hv)
        (norm_nonneg x)).trans_eq (one_div_mul_eq_div _ _)
  rw [add_div]
  exact (norm_sub_le _ _).trans (add_le_add (h t h1 a) (h _ h2 b))

/-- Uniform inverse-square-root bound on `|a / (2 √t) - b / (2 √(1 - t))|` when `δ ≤ t` and
`δ ≤ 1 - t` (`δ > 0`). -/
theorem abs_div_two_sqrt_sub_le {δ t a b : ℝ} (hδ : 0 < δ) (h1 : δ ≤ t) (h2 : δ ≤ 1 - t) :
    |a / (2 * Real.sqrt t) - b / (2 * Real.sqrt (1 - t))| ≤ (|a| + |b|) / (2 * Real.sqrt δ) := by
  simpa only [smul_eq_mul, one_div_mul_eq_div, Real.norm_eq_abs] using
    norm_one_div_two_sqrt_smul_sub_le hδ h1 h2 a b
