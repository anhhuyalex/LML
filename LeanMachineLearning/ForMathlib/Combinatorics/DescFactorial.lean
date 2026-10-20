/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.Linarith

/-!
# Counting injective tuples by falling factorials

The number of injective `p`-tuples in `Fin N` is the falling factorial `N.descFactorial p`
(`Fintype.card_embedding_eq`).  Two consequences used to pass from tuples of distinct sites to
all tuples:

* `Nat.pow_le_pow_mul_descFactorial`: `n ^ p ≤ p ^ p * n.descFactorial p` for `p ≤ n`.
* `Fin.descFactorial_mul_le_sum`: a nonnegative function of `p`-tuples that is invariant under
  relabelling `Fin N` satisfies `N.descFactorial p * T u ≤ ∑ T` for an injective tuple `u`.
-/

@[expose] public section

open Finset

namespace Nat

/-- `n^p ≤ p^p · n^{\underline p}` for `p ≤ n`: each factor `n - i` of the falling factorial is at
least `n / p`. -/
theorem pow_le_pow_mul_descFactorial {n p : ℕ} (h : p ≤ n) :
    n ^ p ≤ p ^ p * n.descFactorial p := by
  rw [Nat.descFactorial_eq_prod_range]
  calc n ^ p = ∏ _i ∈ range p, n := by simp
    _ ≤ ∏ i ∈ range p, (p * (n - i)) := Finset.prod_le_prod fun i hi => by
        have hi' := Finset.mem_range.1 hi
        zify [(hi'.le.trans h)]
        have hp : (1 : ℤ) ≤ p := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 (by omega))
        have hpn : (p : ℤ) ≤ n := by exact_mod_cast h
        nlinarith [mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hpn),
          mul_nonneg (Nat.cast_nonneg p : (0 : ℤ) ≤ p)
            (sub_nonneg.2 (show (i : ℤ) ≤ p - 1 by omega))]
    _ = p ^ p * ∏ i ∈ range p, (n - i) := by
        rw [Finset.prod_mul_distrib]; simp

end Nat

namespace Fin

/-- A nonnegative function of `p`-tuples of sites that is invariant under relabelling the sites
satisfies `n^{\underline p} T(u) ≤ ∑ T` for an injective tuple `u`: the falling factorial counts the
injective tuples, and all of them carry the same value. -/
theorem descFactorial_mul_le_sum {N p : ℕ} {T : (Fin p → Fin N) → ℝ} (hT0 : ∀ u, 0 ≤ T u)
    (hT : ∀ (π : Equiv.Perm (Fin N)) u, T (π ∘ u) = T u) {u : Fin p → Fin N}
    (hu : Function.Injective u) : (N.descFactorial p : ℝ) * T u ≤ ∑ u', T u' := by
  have hconst : ∀ e : Fin p ↪ Fin N, T e = T u := fun e => by
    obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair u e hu e.injective
    rw [← hT π u]
    exact congrArg T (funext fun a => (hπ a).symm)
  have h1 : ∑ e : Fin p ↪ Fin N, T e = (N.descFactorial p : ℝ) * T u := by
    rw [Finset.sum_congr rfl fun e _ => hconst e, Finset.sum_const, Finset.card_univ,
      Fintype.card_embedding_eq]
    simp
  rw [← h1]
  calc ∑ e : Fin p ↪ Fin N, T e
      = ∑ u' ∈ Finset.univ.image (fun e : Fin p ↪ Fin N => (e : Fin p → Fin N)), T u' :=
        (Finset.sum_image fun a _ b _ h => DFunLike.coe_injective h).symm
    _ ≤ ∑ u', T u' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u _ _ => hT0 u

end Fin
