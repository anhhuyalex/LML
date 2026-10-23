/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint

/-!
# A chain of functions with `Q_r' = sin s cos s Q_{r+1}`

Along a Gaussian interpolation path `cos s X + sin s Y` the iterated derivatives of an expectation
form a chain `Q_r` with `Q_r' = sin s cos s Q_{r+1}`.  If the first `n` members vanish at `s = 0`
and `Q_n` is bounded by `M` on `[0, π/2]`, then
`|Q_{n-j}(s)| ≤ M (sin² s / 2)^j / j!`, in particular `|Q_0(π/2)| ≤ M / (2^n n!)`.
This is Taylor's formula in the variable `t = sin² s`, proved directly in the angle `s` by the
fencing theorem, so that no change of variable and no one-sided derivatives are needed.
-/

@[expose] public section

open Set
open scoped Real

namespace Real

/-- **Fencing along a trigonometric chain.**  If `Q r` has derivative `sin s cos s Q (r+1) s`,
`Q r 0 = 0` for `r < n` and `|Q n| ≤ M` on `[0, π/2]`, then
`|Q (n - j) s| ≤ M (sin² s / 2)^j / j!` on `[0, π/2]` for `j ≤ n`. -/
theorem abs_chain_le_of_hasDerivAt {Q : ℕ → ℝ → ℝ} {n : ℕ} {M : ℝ}
    (hd : ∀ r s, HasDerivAt (Q r) (sin s * cos s * Q (r + 1) s) s)
    (h0 : ∀ r < n, Q r 0 = 0) (hM : ∀ s ∈ Icc 0 (π / 2), |Q n s| ≤ M) :
    ∀ j ≤ n, ∀ s ∈ Icc 0 (π / 2),
      |Q (n - j) s| ≤ M * ((sin s) ^ 2 / 2) ^ j / (Nat.factorial j : ℝ) := by
  intro j
  induction j with
  | zero => intro _ s hs; simpa using hM s hs
  | succ j ih =>
    intro hj s hs
    have hjn : j ≤ n := Nat.le_of_succ_le hj
    have hr : n - (j + 1) + 1 = n - j := by omega
    set B : ℝ → ℝ := fun x => M * ((sin x) ^ 2 / 2) ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)
      with hB
    have hBd : ∀ x, HasDerivAt B (M * ((sin x) ^ 2 / 2) ^ j / (Nat.factorial j : ℝ) *
        (sin x * cos x)) x := fun x => by
      have h1 : HasDerivAt (fun x => (sin x) ^ 2 / 2) (sin x * cos x) x := by
        have := (hasDerivAt_sin_sq x).div_const 2
        convert this using 1
        ring
      have h2 := ((h1.pow (j + 1)).const_mul M).div_const (Nat.factorial (j + 1) : ℝ)
      convert h2 using 1
      rw [Nat.factorial_succ]
      push_cast
      have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
      field_simp
    have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := Q (n - (j + 1))) (a := 0) (b := π / 2)
      (f' := fun x => sin x * cos x * Q (n - j) x)
      (B := B) (B' := fun x => M * ((sin x) ^ 2 / 2) ^ j / (Nat.factorial j : ℝ) *
        (sin x * cos x))
      (fun x _ => (hd _ x).continuousAt.continuousWithinAt)
      (fun x _ => by
        have := (hd (n - (j + 1)) x).hasDerivWithinAt (s := Set.Ici x)
        rwa [hr] at this)
      (by
        rw [h0 _ (by omega), norm_zero]
        simp [hB])
      hBd
      (fun x hx => by
        have hs0 : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, pi_pos])
        have hc0 : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, pi_pos], hx.2.le⟩
        have hxI : x ∈ Icc 0 (π / 2) := ⟨hx.1, hx.2.le⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hs0 hc0)]
        have := ih hjn x hxI
        calc sin x * cos x * |Q (n - j) x|
            ≤ sin x * cos x * (M * ((sin x) ^ 2 / 2) ^ j / (Nat.factorial j : ℝ)) :=
              mul_le_mul_of_nonneg_left this (mul_nonneg hs0 hc0)
          _ = _ := by ring)
      hs
    simpa [Real.norm_eq_abs, hB] using hmain

/-- **Taylor's formula in the variable `t = sin² s`.**  Under the hypotheses of
`Real.abs_chain_le_of_hasDerivAt`, `|Q 0 (π/2)| ≤ M / (2^n n!)`. -/
theorem abs_chain_zero_le_of_hasDerivAt {Q : ℕ → ℝ → ℝ} {n : ℕ} {M : ℝ}
    (hd : ∀ r s, HasDerivAt (Q r) (sin s * cos s * Q (r + 1) s) s)
    (h0 : ∀ r < n, Q r 0 = 0) (hM : ∀ s ∈ Icc 0 (π / 2), |Q n s| ≤ M) :
    |Q 0 (π / 2)| ≤ M / (2 ^ n * (Nat.factorial n : ℝ)) := by
  have h := abs_chain_le_of_hasDerivAt hd h0 hM n le_rfl (π / 2)
    ⟨by positivity, le_rfl⟩
  simp only [Nat.sub_self, sin_pi_div_two, one_pow] at h
  refine h.trans (le_of_eq ?_)
  rw [div_pow, one_pow]
  field_simp

end Real
