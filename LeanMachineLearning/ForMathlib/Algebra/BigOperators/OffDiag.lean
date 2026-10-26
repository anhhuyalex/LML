/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Symmetric off-diagonal finite sums

This elementary reindexing is useful whenever a symmetric covariance kernel is
first summed over ordered pairs and then over unordered pairs.
-/

@[expose] public section

open Finset
open scoped BigOperators

/-- A symmetric off-diagonal double sum is twice its strictly ordered half.
The result is stated for every finite linear order, rather than a particular
replica type. -/
theorem sum_sum_offDiag_eq_two_sum_lt {ι : Type*} [Fintype ι] [LinearOrder ι]
    (U : ι → ι → ℝ) (hU : ∀ a b, U a b = U b a) :
    (∑ a, ∑ b, if a = b then 0 else U a b) = 2 * ∑ p : ι × ι with p.1 < p.2, U p.1 p.2 := by
  classical
  rw [← Finset.sum_product' (f := fun a b => if a = b then 0 else U a b), Finset.univ_product_univ]
  have hpt (p : ι × ι) : (if p.1 = p.2 then 0 else U p.1 p.2) =
      (if p.1 < p.2 then U p.1 p.2 else 0) + (if p.2 < p.1 then U p.1 p.2 else 0) := by
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.sum_filter]
  rw [two_mul]
  congr 1
  exact Finset.sum_equiv (Equiv.prodComm ι ι) (by simp) fun p _ => hU _ _

/-- Strictly ordered pairs, as a filtered finite sum or a sum over the subtype. -/
theorem sum_filter_lt_eq_sum_subtype {ι M : Type*} [Fintype ι] [LinearOrder ι] [AddCommMonoid M]
    (f : ι × ι → M) :
    ∑ p : ι × ι with p.1 < p.2, f p = ∑ p : {p : ι × ι // p.1 < p.2}, f p.val :=
  Finset.sum_subtype _ (by simp) f

/-- Strictly ordered pairs are automatically off-diagonal. -/
theorem filter_offDiag_lt {ι : Type*} [Fintype ι] [LinearOrder ι] :
    (Finset.univ : Finset ι).offDiag.filter (fun p : ι × ι => p.1 < p.2) =
      (Finset.univ : Finset (ι × ι)).filter fun p => p.1 < p.2 := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
    and_iff_right_iff_imp]
  exact fun h => h.ne

/-- **Ordered half of a symmetrized double sum.**  The sum over strictly ordered pairs of
`X a b + X b a` is the full double sum of `X` minus its diagonal. -/
theorem sum_filter_lt_add_swap {ι : Type*} [Fintype ι] [LinearOrder ι] (X : ι → ι → ℝ) :
    ∑ p : ι × ι with p.1 < p.2, (X p.1 p.2 + X p.2 p.1) =
      (∑ a, ∑ b, X a b) - ∑ a, X a a := by
  classical
  have h := sum_sum_offDiag_eq_two_sum_lt (fun a b => X a b + X b a) (fun a b => add_comm _ _)
  have e1 : ∀ a, (∑ b, if a = b then 0 else X a b + X b a) =
      (∑ b, X a b) + (∑ b, X b a) - 2 * X a a := fun a => by
    have hs : ∀ b, (X a b + X b a) =
        (if a = b then 0 else X a b + X b a) + (if a = b then X a b + X b a else 0) := fun b => by
      split_ifs <;> simp
    have h1 : (∑ b, (X a b + X b a)) = (∑ b, if a = b then 0 else X a b + X b a) +
        (X a a + X a a) := by
      rw [Finset.sum_congr rfl fun b _ => hs b, Finset.sum_add_distrib,
        Finset.sum_ite_eq]
      simp
    rw [Finset.sum_add_distrib] at h1
    linarith
  have h2 : (∑ a, ∑ b, if a = b then 0 else X a b + X b a) =
      2 * ((∑ a, ∑ b, X a b) - ∑ a, X a a) := by
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_comm (f := fun a b => X b a)]
    ring
  linarith
