/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Endpoint estimates for a derivative bounded by `sin s cos s`

If `φ' ≤ K sin s cos s` on `[0, π/2]`, then `φ (π/2) - φ 0 ≤ K / 2`, since
`φ - (K/2) sin²` is nonincreasing; symmetrically a lower bound `φ' ≥ -K sin s cos s` gives
`-K / 2 ≤ φ (π/2) - φ 0`.  These are the calculus steps behind every interpolation along the
trigonometric path `cos s X + sin s Y` (Guerra's bound, the Aizenman-Lebowitz-Ruelle estimate and
the Gaussian covariance comparison).
-/

@[expose] public section

open Set
open scoped Real

namespace Real

/-- `|sin s cos s| ≤ 1 / 2`. -/
theorem abs_sin_mul_cos_le_half (s : ℝ) : |Real.sin s * Real.cos s| ≤ 1 / 2 := by
  have h : Real.sin s * Real.cos s = Real.sin (2 * s) / 2 := by rw [Real.sin_two_mul]; ring
  rw [h, abs_div, abs_two]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) zero_le_two

/-- Derivative of `sin x ^ 2` is `2 sin s cos s`. -/
theorem hasDerivAt_sin_sq (s : ℝ) :
    HasDerivAt (fun x => sin x ^ 2) (2 * sin s * cos s) s := by
  convert (hasDerivAt_sin s).pow 2 using 1
  ring

/-- Derivative of `cos x ^ 2` is `-(2 sin s cos s)`. -/
theorem hasDerivAt_cos_sq (s : ℝ) :
    HasDerivAt (fun x => cos x ^ 2) (-(2 * sin s * cos s)) s := by
  convert (hasDerivAt_cos s).pow 2 using 1
  ring

/-- A derivative bounded above by `K sin s cos s` on `[a, b]` bounds the increment from `a` to `b`
by `K (sin² b - sin² a) / 2`. -/
theorem sub_le_of_deriv_le_Icc {φ φ' : ℝ → ℝ} (hd : ∀ s, HasDerivAt φ (φ' s) s) {K a b : ℝ}
    (hab : a ≤ b) (hK : ∀ s ∈ Icc a b, φ' s ≤ K * (sin s * cos s)) :
    φ b - φ a ≤ K / 2 * (sin b ^ 2 - sin a ^ 2) := by
  have hF : ∀ s, HasDerivAt (fun x => φ x - K / 2 * sin x ^ 2)
      (φ' s - K * (sin s * cos s)) s := fun s => by
    convert (hd s).sub ((hasDerivAt_sin_sq s).const_mul (K / 2)) using 1
    ring
  have hanti : AntitoneOn (fun x => φ x - K / 2 * sin x ^ 2) (Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun s _ => (hF s).continuousAt.continuousWithinAt)
      (fun s _ => (hF s).differentiableAt.differentiableWithinAt) fun s hs => by
        rw [interior_Icc] at hs
        rw [(hF s).deriv]
        linarith [hK s ⟨hs.1.le, hs.2.le⟩]
  have := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only at this
  linarith

/-- A derivative bounded above by `K sin s cos s` on `[0, π/2]` bounds the increment by `K / 2`. -/
theorem sub_le_half_of_deriv_le {φ φ' : ℝ → ℝ} (hd : ∀ s, HasDerivAt φ (φ' s) s) {K : ℝ}
    (hK : ∀ s ∈ Icc 0 (π / 2), φ' s ≤ K * (sin s * cos s)) : φ (π / 2) - φ 0 ≤ K / 2 := by
  have := sub_le_of_deriv_le_Icc hd (by positivity : (0 : ℝ) ≤ π / 2) hK
  simpa using this

/-- A derivative bounded below by `-K sin s cos s` on `[0, π/2]` bounds the increment below by
`-K / 2`. -/
theorem neg_half_le_sub_of_le_deriv {φ φ' : ℝ → ℝ} (hd : ∀ s, HasDerivAt φ (φ' s) s) {K : ℝ}
    (hK : ∀ s ∈ Icc 0 (π / 2), -(K * (sin s * cos s)) ≤ φ' s) : -(K / 2) ≤ φ (π / 2) - φ 0 := by
  have := sub_le_half_of_deriv_le (φ := fun s => -φ s) (φ' := fun s => -φ' s)
    (fun s => (hd s).neg) (K := K) fun s hs => by linarith [hK s hs]
  linarith

/-- A derivative bounded in absolute value by `K sin s cos s` on `[0, π/2]` bounds the increment
by `K / 2`. -/
theorem abs_sub_le_half_of_abs_deriv_le {φ φ' : ℝ → ℝ} (hd : ∀ s, HasDerivAt φ (φ' s) s) {K : ℝ}
    (hK : ∀ s ∈ Icc 0 (π / 2), |φ' s| ≤ K * (sin s * cos s)) : |φ (π / 2) - φ 0| ≤ K / 2 :=
  abs_le.2 ⟨neg_half_le_sub_of_le_deriv hd fun s hs => (abs_le.1 (hK s hs)).1,
    sub_le_half_of_deriv_le hd fun s hs => (abs_le.1 (hK s hs)).2⟩

/-- Pointwise form: if at every `s` the derivative is `sin s cos s D` with `|D| ≤ K` for
`s ∈ [0, π/2]`, then the increment is at most `K / 2`. The derivative function need not be chosen
by the caller. -/
theorem abs_sub_le_half_of_exists_hasDerivAt {φ : ℝ → ℝ} {K : ℝ}
    (hd : ∀ s, ∃ D, HasDerivAt φ (sin s * cos s * D) s ∧ (s ∈ Icc 0 (π / 2) → |D| ≤ K)) :
    |φ (π / 2) - φ 0| ≤ K / 2 := by
  choose D hDd hDb using hd
  refine abs_sub_le_half_of_abs_deriv_le hDd fun s hs => ?_
  have hsin := sin_nonneg_of_nonneg_of_le_pi hs.1 (hs.2.trans (by linarith [pi_pos]))
  have hcos := cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, pi_pos], hs.2⟩
  rw [abs_mul, abs_of_nonneg (mul_nonneg hsin hcos)]
  have := mul_le_mul_of_nonneg_left (hDb s hs) (mul_nonneg hsin hcos)
  linarith

/-- Interval form of `abs_sub_le_half_of_exists_hasDerivAt`: for `0 ≤ a ≤ b ≤ π/2`,
`|φ b - φ a| ≤ K (sin² b - sin² a) / 2`. -/
theorem abs_sub_le_of_exists_hasDerivAt_Icc {φ : ℝ → ℝ} {K a b : ℝ}
    (hd : ∀ s, ∃ D, HasDerivAt φ (sin s * cos s * D) s ∧ (s ∈ Icc 0 (π / 2) → |D| ≤ K))
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    |φ b - φ a| ≤ K / 2 * (sin b ^ 2 - sin a ^ 2) := by
  choose D hDd hDb using hd
  have hmem : ∀ s ∈ Icc a b, s ∈ Icc 0 (π / 2) := fun s hs =>
    ⟨ha.trans hs.1, hs.2.trans hb⟩
  have hsc : ∀ s ∈ Icc a b, 0 ≤ sin s * cos s := fun s hs => by
    have hs' := hmem s hs
    exact mul_nonneg (sin_nonneg_of_nonneg_of_le_pi hs'.1 (hs'.2.trans (by linarith [pi_pos])))
      (cos_nonneg_of_mem_Icc ⟨by linarith [hs'.1, pi_pos], hs'.2⟩)
  have hup : ∀ s ∈ Icc a b, sin s * cos s * D s ≤ K * (sin s * cos s) := fun s hs => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (hDb s (hmem s hs))).2 (hsc s hs)
    linarith
  have hlo : ∀ s ∈ Icc a b, -(K * (sin s * cos s)) ≤ sin s * cos s * D s := fun s hs => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (hDb s (hmem s hs))).1 (hsc s hs)
    linarith
  refine abs_le.2 ⟨?_, sub_le_of_deriv_le_Icc hDd hab hup⟩
  have := sub_le_of_deriv_le_Icc (φ := fun s => -φ s) (φ' := fun s => -(sin s * cos s * D s))
    (fun s => (hDd s).neg) (K := K) hab fun s hs => by linarith [hlo s hs]
  linarith

/-- If `φ' = sin s cos s D` with `|D - C| ≤ K` on `[0, π/2]`, then
`|φ (π / 2) - φ 0 - C / 2| ≤ K / 2`. -/
theorem abs_sub_sub_half_le_of_exists_hasDerivAt {φ : ℝ → ℝ} {C K : ℝ}
    (hd : ∀ s, ∃ D, HasDerivAt φ (sin s * cos s * D) s ∧ (s ∈ Icc 0 (π / 2) → |D - C| ≤ K)) :
    |φ (π / 2) - φ 0 - C / 2| ≤ K / 2 := by
  have hF : ∀ s, ∃ D', HasDerivAt (fun x => φ x - C / 2 * sin x ^ 2) (sin s * cos s * D') s ∧
      (s ∈ Icc 0 (π / 2) → |D'| ≤ K) := fun s => by
    obtain ⟨D, hD, hDb⟩ := hd s
    refine ⟨D - C, ?_, fun hs => hDb hs⟩
    have hderv : HasDerivAt (fun x => φ x - C / 2 * sin x ^ 2)
        (sin s * cos s * D - C / 2 * (2 * sin s * cos s)) s :=
      hD.sub ((hasDerivAt_sin_sq s).const_mul (C / 2))
    convert hderv using 1
    ring
  have key := abs_sub_le_half_of_exists_hasDerivAt hF
  simp only [sin_zero, sq, mul_zero, sin_pi_div_two, mul_one, sub_zero] at key
  rw [sub_right_comm] at key
  exact key

/-- **Second-order expansion along the trigonometric path.** If `Ψ' = sin s cos s G` and
`G' = sin s cos s D` with `|D| ≤ K` on `[0, π/2]`, then
`|Ψ (π/2) - Ψ 0 - G (π/2) / 2| ≤ K / 4`. -/
theorem abs_sub_sub_half_le_of_second_order {Ψ G : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hΨ : ∀ s, HasDerivAt Ψ (sin s * cos s * G s) s)
    (hG : ∀ s, ∃ D, HasDerivAt G (sin s * cos s * D) s ∧ (s ∈ Icc 0 (π / 2) → |D| ≤ K)) :
    |Ψ (π / 2) - Ψ 0 - G (π / 2) / 2| ≤ K / 4 := by
  have key := abs_sub_sub_half_le_of_exists_hasDerivAt (φ := Ψ) (C := G (π / 2)) (K := K / 2)
    fun s => ⟨G s, hΨ s, fun hs => by
      have h := abs_sub_le_of_exists_hasDerivAt_Icc hG hs.1 hs.2 le_rfl
      rw [abs_sub_comm]
      refine h.trans ?_
      simp only [sin_pi_div_two]
      nlinarith [sq_nonneg (sin s)]⟩
  linarith

/-- Reversed-endpoint form of `abs_sub_sub_half_le_of_exists_hasDerivAt`:
`|φ 0 - φ (π / 2) + C / 2| ≤ K / 2`. -/
theorem abs_sub_add_half_le_of_exists_hasDerivAt {φ : ℝ → ℝ} {C K : ℝ}
    (hd : ∀ s, ∃ D, HasDerivAt φ (sin s * cos s * D) s ∧ (s ∈ Icc 0 (π / 2) → |D - C| ≤ K)) :
    |φ 0 - φ (π / 2) + C / 2| ≤ K / 2 := by
  rw [show φ 0 - φ (π / 2) + C / 2 = -(φ (π / 2) - φ 0 - C / 2) by ring, abs_neg]
  exact abs_sub_sub_half_le_of_exists_hasDerivAt hd

/-- **Grönwall along the trigonometric path.**  If `φ' ≤ K sin s cos s φ` on `[0, π/2]`, then
`φ s ≤ exp (K sin² s / 2) φ 0`, since `φ exp (-K sin² / 2)` is nonincreasing. -/
theorem le_exp_mul_sin_sq_of_exists_hasDerivAt {φ : ℝ → ℝ} {K : ℝ}
    (hd : ∀ s, ∃ d, HasDerivAt φ d s ∧ (s ∈ Icc 0 (π / 2) → d ≤ K * (sin s * cos s) * φ s))
    {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) : φ s ≤ exp (K * sin s ^ 2 / 2) * φ 0 := by
  choose d hd1 hd2 using hd
  set g : ℝ → ℝ := fun x => φ x * exp (-(K * sin x ^ 2 / 2)) with hg
  have hgd : ∀ x, HasDerivAt g (d x * exp (-(K * sin x ^ 2 / 2)) +
      φ x * (exp (-(K * sin x ^ 2 / 2)) * (-(K * (2 * sin x * cos x) / 2)))) x := fun x =>
    (hd1 x).mul (((hasDerivAt_sin_sq x).const_mul K |>.div_const 2).neg.exp)
  have hanti : AntitoneOn g (Icc 0 (π / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 (π / 2))
      (fun x _ => (hgd x).continuousAt.continuousWithinAt)
      (fun x _ => (hgd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hgd x).deriv]
    have h1 := hd2 x ⟨hx.1.le, hx.2.le⟩
    have h2 := exp_pos (-(K * sin x ^ 2 / 2))
    nlinarith [mul_le_mul_of_nonneg_right h1 h2.le]
  have h0 : (0 : ℝ) ∈ Icc 0 (π / 2) := ⟨le_rfl, by positivity⟩
  have key := hanti h0 hs hs.1
  simp only [hg, sin_zero] at key
  have h2 := exp_pos (K * sin s ^ 2 / 2)
  have h3 : exp (-(K * sin s ^ 2 / 2)) * exp (K * sin s ^ 2 / 2) = 1 := by
    rw [← exp_add]; simp
  norm_num at key
  calc φ s = φ s * exp (-(K * sin s ^ 2 / 2)) * exp (K * sin s ^ 2 / 2) := by
        rw [mul_assoc, h3, mul_one]
    _ ≤ φ 0 * exp (K * sin s ^ 2 / 2) := mul_le_mul_of_nonneg_right key h2.le
    _ = exp (K * sin s ^ 2 / 2) * φ 0 := mul_comm _ _

end Real

