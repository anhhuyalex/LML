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

/-!
# Estimates for differences of square roots

* `Real.sqrt_add_le_add_sqrt`: `√(a + b) ≤ √a + √b` for `a, b ≥ 0`.
* `Real.sq_sqrt_sub_le_abs_sub`: `(√a - √b)² ≤ |a - b|` for `a, b ≥ 0`.
* `Real.sq_sqrt_sub_le`: `(√q - a)² ≤ (q - a²)² / q` for `q > 0`, `a ≥ 0`.
* `Real.inv_sqrt_mul_self`: `(√n)⁻¹ * (√n)⁻¹ = n⁻¹` for `n ≥ 0`.
* `Real.abs_one_div_two_mul_sqrt_le`: `|1 / (2 √v)| ≤ 1 / (2 √δ)` when `0 < δ ≤ v`.
* `hasDerivAt_sqrt_mul_add_sqrt_one_sub_mul`: derivative of `s ↦ √s a + √(1 - s) b` on `(0, 1)`.
* `abs_div_two_sqrt_sub_le`: `|a / (2 √t) - b / (2 √(1 - t))| ≤ (|a| + |b|) / (2 √δ)` when
  `δ ≤ t ≤ 1 - δ`.
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

/-- `√(a + b) ≤ √a + √b` for nonnegative `a, b`, since `(√a + √b)² = a + b + 2 √a √b ≥ a + b`. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b :=
  Real.sqrt_le_iff.2 ⟨by positivity, by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a)
      (Real.sqrt_nonneg b)]⟩

/-- `(√a - √b)² ≤ |a - b|` for `a, b ≥ 0`: `|a - b| = |√a - √b| (√a + √b)` and
`|√a - √b| ≤ √a + √b`. -/
theorem sq_sqrt_sub_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hab : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
    rw [abs_le]
    constructor <;> linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have heq : |a - b| = |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
    congr 1
    have := Real.sq_sqrt ha
    have := Real.sq_sqrt hb
    nlinarith
  rw [heq, ← sq_abs, sq]
  exact mul_le_mul_of_nonneg_left hab (abs_nonneg _)

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

/-- Derivative of `s ↦ √s * a + √(1 - s) * b` at an interior point `t ∈ (0, 1)`. -/
theorem hasDerivAt_sqrt_mul_add_sqrt_one_sub_mul {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (a b : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sqrt s * a + Real.sqrt (1 - s) * b)
      (a / (2 * Real.sqrt t) - b / (2 * Real.sqrt (1 - t))) t := by
  have h1 := (Real.hasDerivAt_sqrt ht.1.ne').mul_const a
  have h2 := (((hasDerivAt_id t).const_sub 1).sqrt (sub_pos.2 ht.2).ne').mul_const b
  exact (h1.add h2).congr_deriv (by dsimp only [id_eq]; ring)

/-- Uniform inverse-square-root bound on `|a / (2 √t) - b / (2 √(1 - t))|` when `δ ≤ t` and
`δ ≤ 1 - t` (`δ > 0`). -/
theorem abs_div_two_sqrt_sub_le {δ t a b : ℝ} (hδ : 0 < δ) (h1 : δ ≤ t) (h2 : δ ≤ 1 - t) :
    |a / (2 * Real.sqrt t) - b / (2 * Real.sqrt (1 - t))| ≤ (|a| + |b|) / (2 * Real.sqrt δ) := by
  have ht0 : 0 < t := hδ.trans_le h1
  have ht1 : 0 < 1 - t := hδ.trans_le h2
  have hi1 : 1 / (2 * Real.sqrt t) ≤ 1 / (2 * Real.sqrt δ) :=
    (le_abs_self _).trans (Real.abs_one_div_two_mul_sqrt_le hδ h1)
  have hi2 : 1 / (2 * Real.sqrt (1 - t)) ≤ 1 / (2 * Real.sqrt δ) :=
    (le_abs_self _).trans (Real.abs_one_div_two_mul_sqrt_le hδ h2)
  have hsub := abs_sub (a / (2 * Real.sqrt t)) (b / (2 * Real.sqrt (1 - t)))
  rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt t),
    abs_of_pos (by positivity : 0 < 2 * Real.sqrt (1 - t))] at hsub
  have ha_le : |a| / (2 * Real.sqrt t) ≤ |a| / (2 * Real.sqrt δ) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_left hi1 (abs_nonneg a)
  have hb_le : |b| / (2 * Real.sqrt (1 - t)) ≤ |b| / (2 * Real.sqrt δ) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_left hi2 (abs_nonneg b)
  calc |a / (2 * Real.sqrt t) - b / (2 * Real.sqrt (1 - t))|
      ≤ |a| / (2 * Real.sqrt δ) + |b| / (2 * Real.sqrt δ) := hsub.trans (add_le_add ha_le hb_le)
    _ = (|a| + |b|) / (2 * Real.sqrt δ) := by ring
