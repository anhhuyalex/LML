/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic

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
    (∑ a, ∑ b, if a = b then 0 else U a b) =
      2 * ∑ p ∈ (Finset.univ : Finset ι).offDiag with p.1 < p.2, U p.1 p.2 := by
  classical
  let s : Finset (ι × ι) := (Finset.univ : Finset ι).offDiag
  let sl : Finset (ι × ι) := s.filter fun p => p.1 < p.2
  let sg : Finset (ι × ι) := s.filter fun p => ¬ p.1 < p.2
  have hsplit : (∑ p ∈ s, U p.1 p.2) =
      (∑ p ∈ sl, U p.1 p.2) + ∑ p ∈ sg, U p.1 p.2 := by
    exact (Finset.sum_filter_add_sum_filter_not s (fun p => p.1 < p.2)
      fun p => U p.1 p.2).symm
  have hswap : (∑ p ∈ sg, U p.1 p.2) = ∑ p ∈ sl, U p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_filter.mp (by simpa only [sg] using hp) with ⟨hps, hpnot⟩
      have hpsoff : p ∈ (Finset.univ : Finset ι).offDiag := by
        change p ∈ (Finset.univ : Finset ι).offDiag at hps
        exact hps
      have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hpsoff).2.2
      have hplt : p.2 < p.1 := lt_of_le_of_ne (le_of_not_gt hpnot) (Ne.symm hpne)
      refine Finset.mem_filter.2 ⟨?_, hplt⟩
      change (p.2, p.1) ∈ (Finset.univ : Finset ι).offDiag
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, Ne.symm hpne⟩
    · intro p hp q hq hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
    · intro q hq
      rcases Finset.mem_filter.mp (by simpa only [sl] using hq) with ⟨hqs, hqlt⟩
      refine ⟨(q.2, q.1), ?_, rfl⟩
      refine Finset.mem_filter.2 ⟨?_, not_lt_of_ge (le_of_lt hqlt)⟩
      change (q.2, q.1) ∈ (Finset.univ : Finset ι).offDiag
      have hqsoff : q ∈ (Finset.univ : Finset ι).offDiag := by
        change q ∈ (Finset.univ : Finset ι).offDiag at hqs
        exact hqs
      have hqne : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hqsoff).2.2
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, Ne.symm hqne⟩
    · intro p hp
      exact hU _ _
  calc
    _ = ∑ p ∈ s, U p.1 p.2 := by
      rw [← Finset.sum_product', Finset.univ_product_univ]
      have hterm (p : ι × ι) :
          (if p.1 = p.2 then 0 else U p.1 p.2) =
            if p.1 ≠ p.2 then U p.1 p.2 else 0 := by
        by_cases hp : p.1 = p.2 <;> simp [hp]
      simp_rw [hterm]
      change (∑ p ∈ (Finset.univ : Finset (ι × ι)),
        if p.1 ≠ p.2 then U p.1 p.2 else 0) = _
      rw [← Finset.sum_filter]
      change (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 ≠ p.2),
        U p.1 p.2) = _
      have hs : (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 ≠ p.2) = s := by
        ext p
        simp [s, Finset.mem_offDiag]
      rw [hs]
    _ = 2 * ∑ p ∈ sl, U p.1 p.2 := by rw [hsplit, hswap, two_mul]
    _ = _ := by rfl
