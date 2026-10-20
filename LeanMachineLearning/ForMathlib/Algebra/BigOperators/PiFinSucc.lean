/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over `(k + 1)`-tuples with a distinguished first slot

Expanding the product `(∑ⱼ cⱼ) (∑ᵢ eᵢ)^k` over the canonical splitting `Fin (k + 1) → ι` into a
first coordinate and `k` remaining ones gives a sum over `(k + 1)`-tuples
(`sum_piFinSucc_mul_prod`).
-/

@[expose] public section

open Finset

/-- The sum over `(k + 1)`-tuples of a factor `c` in the first slot times a product of `e` over
the other `k` slots factorizes as `(∑ⱼ cⱼ) (∑ᵢ eᵢ)^k`. -/
theorem sum_piFinSucc_mul_prod {ι R : Type*} [Fintype ι] [CommSemiring R] (k : ℕ)
    (c e : ι → R) :
    ∑ u : Fin (k + 1) → ι, c (u 0) * ∏ l : Fin k, e (u l.succ) =
      (∑ j, c j) * (∑ i, e i) ^ k := by
  have h := Fintype.prod_sum (fun (l : Fin (k + 1)) (i : ι) =>
    (Fin.cons c (fun _ => e) : Fin (k + 1) → ι → R) l i)
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h
  exact h.symm
