/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# Binomial sums at a vanishing argument

The constant and linear terms are the only contributions to a differentiated binomial sum
at zero. The identity is algebraic over any commutative semiring.
-/

@[expose] public section

namespace Finset

/-- **The binomial sum behind a moving center.**  If `z (t) = 0` and `z' (t) = u`, the derivative
at `t` of `∑ᵢ C(k, i) z(s)^i f_{k-i}(s)` is
`∑ᵢ C(k, i) (i · 0^{i-1} · u · f_{k-i} + 0^i · g_{k-i}) = k u f_{k-1} + g_k`
(only the terms `i = 0, 1` are nonzero). -/
theorem sum_choose_mul_deriv_pow_zero {K : Type*} [CommSemiring K] (k : ℕ) (u : K) (f g : ℕ → K) :
    ∑ i ∈ range (k + 1), (k.choose i : K) *
        ((i : K) * 0 ^ (i - 1) * u * f (k - i) + 0 ^ i * g (k - i)) =
      k * u * f (k - 1) + g k := by
  rcases k with _ | k
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h2 : ∀ i ∈ range k, ((k + 1).choose (i + 1 + 1) : K) *
        (((i + 1 + 1 : ℕ) : K) * 0 ^ (i + 1 + 1 - 1) * u * f (k + 1 - (i + 1 + 1)) +
          0 ^ (i + 1 + 1) * g (k + 1 - (i + 1 + 1))) = 0 := fun i _ => by
      simp
    rw [Finset.sum_eq_zero h2]
    simp [Nat.choose_one_right]
    ring

end Finset
