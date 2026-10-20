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

/-- A derivative bounded above by `K sin s cos s` on `[0, π/2]` bounds the increment by `K / 2`. -/
theorem sub_le_half_of_deriv_le {φ φ' : ℝ → ℝ} (hd : ∀ s, HasDerivAt φ (φ' s) s) {K : ℝ}
    (hK : ∀ s ∈ Icc 0 (π / 2), φ' s ≤ K * (sin s * cos s)) : φ (π / 2) - φ 0 ≤ K / 2 := by
  have hF : ∀ s, HasDerivAt (fun x => φ x - K / 2 * sin x ^ 2)
      (φ' s - K * (sin s * cos s)) s := fun s => by
    have hsq : HasDerivAt (fun x => sin x ^ 2) (2 * sin s * cos s) s := by
      convert (hasDerivAt_sin s).pow 2 using 1
      all_goals ring
    convert (hd s).sub (hsq.const_mul (K / 2)) using 1
    ring
  have hanti : AntitoneOn (fun x => φ x - K / 2 * sin x ^ 2) (Icc 0 (π / 2)) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 (π / 2))
      (fun s _ => (hF s).continuousAt.continuousWithinAt)
      (fun s _ => (hF s).differentiableAt.differentiableWithinAt) fun s hs => by
        rw [interior_Icc] at hs
        rw [(hF s).deriv]
        linarith [hK s ⟨hs.1.le, hs.2.le⟩]
  have := hanti ⟨le_rfl, by linarith [pi_pos]⟩ ⟨by linarith [pi_pos], le_rfl⟩
    (by linarith [pi_pos])
  simp only [sin_zero, sin_pi_div_two] at this
  linarith

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

end Real
