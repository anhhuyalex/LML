/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Factorization of Products over the Hypercube `ι → ℤˣ`

This file proves the factorization identity for product functions over the hypercube `ι → ℤˣ`
(Michel Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, 2010, Section 1.2,
Eq. (1.30)):
$$\sum_{\sigma \in \iota \to \mathbb{Z}^\times} \prod_{i \in \iota} a_i(\sigma_i) =
  \prod_{i \in \iota} (a_i(1) + a_i(-1)).$$

The identity holds for an arbitrary finite index type `ι` and an arbitrary commutative semiring `R`.

## Main declarations

* `sum_units_int`: the sum of any function over `ℤˣ = {1, -1}` is `f 1 + f (-1)`.
* `hypercube_sum_prod_eq_prod_add`: the hypercube sum-product factorization.
* `hypercube_sum_prod_erase_eq_prod_add`: singles out a coordinate `j : ι`.

## References

* [M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Springer, 2010], §1.2.
-/

@[expose] public section

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of a function over `ℤˣ = {1, -1}` equals `f 1 + f (-1)`. -/
theorem sum_units_int {M : Type*} [AddCommMonoid M] (f : ℤˣ → M) :
    ∑ s : ℤˣ, f s = f 1 + f (-1) := by
  have h : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext x
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact Int.units_eq_one_or x
  rw [h]
  have hne : (1 : ℤˣ) ≠ -1 := by decide
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]

/-- **Hypercube Factorization Identity (Eq. 1.30):**
The sum over all spin configurations of a product of coordinate functions factors into
the product of coordinate sums. -/
theorem hypercube_sum_prod_eq_prod_add {R : Type*} [CommSemiring R] (a : ι → ℤˣ → R) :
    ∑ σ : ι → ℤˣ, ∏ i, a i (σ i) = ∏ i, (a i 1 + a i (-1)) := by
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  congr 1
  ext i
  exact sum_units_int (a i)

/-- Hypercube sum-product with a singled-out coordinate `j : ι`. -/
theorem hypercube_sum_prod_erase_eq_prod_add {R : Type*} [CommSemiring R]
    (a : ι → ℤˣ → R) (j : ι) :
    ∑ σ : ι → ℤˣ, ∏ i, a i (σ i) =
      (a j 1 + a j (-1)) * ∏ i ∈ Finset.univ.erase j, (a i 1 + a i (-1)) := by
  rw [hypercube_sum_prod_eq_prod_add, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
