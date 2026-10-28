/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring

/-!
# Zero propagation in two-step recurrences

Odd terms of `a (n+2) = c n * a n` vanish when `a 1 = 0`. No condition on the coefficients
is needed beyond multiplication by zero vanishing.
-/

@[expose] public section

namespace Nat

/-- The odd terms of a homogeneous two-step multiplicative recurrence vanish if `a 1 = 0`. -/
theorem eq_zero_of_odd_of_two_step_mul {K : Type*} [MulZeroClass K] {a c : ℕ → K}
    (ha1 : a 1 = 0) (ha : ∀ k, a (k + 2) = c k * a k) {k : ℕ} (hk : Odd k) : a k = 0 := by
  obtain ⟨m, rfl⟩ := hk
  induction m with
  | zero => simpa using ha1
  | succ m ih => rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, ha, ih, mul_zero]

end Nat
