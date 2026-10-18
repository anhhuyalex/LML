/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtomRank

/-!
# Ranked atoms and monotone transformations

The `n`-th largest atom of a counting measure `∑ δ_{u a}` of positive, distinct, summable masses
is carried to the `n`-th largest atom of the transformed counting measure by any strictly
increasing positive map, in particular by a power `x ↦ x ^ e`, `e > 0`, as soon as the transformed
masses are again summable (the ranks do not change).
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- **Ranked atoms commute with powers.** For positive, distinct, summable masses `u a` whose
powers `u a ^ e` (`e > 0`) are summable, the `m`-th largest atom of the powered family is the
`e`-th power of the `m`-th largest atom of the family. -/
theorem nthLargestAtom_sum_dirac_rpow {α : Type*} [Infinite α] (u : α → ℝ)
    (hu : Function.Injective u) (hpos : ∀ a, 0 < u a) (hs : Summable u) {e : ℝ} (he : 0 < e)
    (hs' : Summable fun a => u a ^ e) (m : ℕ) :
    nthLargestAtom m (Measure.sum fun a : α => Measure.dirac (u a ^ e)) =
      nthLargestAtom m (Measure.sum fun a : α => Measure.dirac (u a)) ^ e := by
  have hpos' : ∀ a, 0 < u a ^ e := fun a => Real.rpow_pos_of_pos (hpos a) e
  have hu' : Function.Injective fun a => u a ^ e := fun a b h =>
    hu ((Real.rpow_left_injOn he.ne').eq_iff (hpos a).le (hpos b).le |>.1 h)
  have hfin (a : α) := finite_superlevel_of_summable hs (hpos a)
  obtain ⟨a, ha⟩ := surjective_ncard_superlevel_lt hu hfin m
  have hrank : {b | u a ^ e < u b ^ e}.ncard = m := by
    rw [← ha]
    congr 1
    ext b
    simp only [mem_ofPred_eq]
    exact Real.rpow_lt_rpow_iff (hpos a).le (hpos b).le he
  have h1 := nthLargestAtom_sum_dirac_rank u hpos hs a
  have h2 := nthLargestAtom_sum_dirac_rank (fun a => u a ^ e) hpos' hs' a
  have ha' : {b | u a < u b}.ncard = m := ha
  rw [ha'] at h1
  rw [hrank] at h2
  rw [h1, h2, ENNReal.ofReal_rpow_of_pos (hpos a)]

/-- **Ranked atoms commute with scaling.** For positive, distinct, summable masses `u a` and
`c > 0`, the `m`-th largest atom of the family `c u a` is `c` times that of `u a`. -/
theorem nthLargestAtom_sum_dirac_mul {α : Type*} [Infinite α] (u : α → ℝ)
    (hu : Function.Injective u) (hpos : ∀ a, 0 < u a) (hs : Summable u) {c : ℝ} (hc : 0 < c)
    (m : ℕ) :
    nthLargestAtom m (Measure.sum fun a : α => Measure.dirac (u a * c)) =
      nthLargestAtom m (Measure.sum fun a : α => Measure.dirac (u a)) * ENNReal.ofReal c := by
  have hpos' : ∀ a, 0 < u a * c := fun a => mul_pos (hpos a) hc
  have hs' : Summable fun a => u a * c := hs.mul_right c
  have hfin (a : α) := finite_superlevel_of_summable hs (hpos a)
  obtain ⟨a, ha⟩ := surjective_ncard_superlevel_lt hu hfin m
  have hrank : {b | u a * c < u b * c}.ncard = m := by
    rw [← ha]
    congr 1
    ext b
    simp only [mem_ofPred_eq]
    exact mul_lt_mul_iff_left₀ hc
  have h1 := nthLargestAtom_sum_dirac_rank u hpos hs a
  have h2 := nthLargestAtom_sum_dirac_rank (fun a => u a * c) hpos' hs' a
  have ha' : {b | u a < u b}.ncard = m := ha
  rw [ha'] at h1
  rw [hrank] at h2
  rw [h1, h2, ENNReal.ofReal_mul (hpos a).le]

end MeasureTheory
