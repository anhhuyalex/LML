/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.CDF

/-!
# Existence of a median

Every real random variable has a median: a number `m` with `ℙ (f ≤ m) ≥ 1 / 2` and
`ℙ (m ≤ f) ≥ 1 / 2`.

## Main declarations

* `ProbabilityTheory.exists_median`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

/-- **Every real random variable has a median.** One takes the infimum of the numbers `x` with
`1 / 2 ≤ cdf x`. -/
theorem exists_median {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) :
    ∃ m : ℝ, 1 / 2 ≤ μ.real {ω | f ω ≤ m} ∧ 1 / 2 ≤ μ.real {ω | m ≤ f ω} := by
  set ν : Measure ℝ := μ.map f with hν
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  set S : Set ℝ := {x | 1 / 2 ≤ cdf ν x} with hS
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop ν).eventually
      (eventually_ge_nhds (show (1 / 2 : ℝ) < 1 by norm_num))).exists
    exact ⟨x, hx⟩
  have hbdd : BddBelow S := by
    obtain ⟨x, hx⟩ := eventually_atBot.1 ((tendsto_cdf_atBot ν).eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
    refine ⟨x, fun y hy => ?_⟩
    by_contra h
    exact (hx y (le_of_not_ge h)).not_ge hy
  set m := sInf S with hm
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨m, ?_, ?_⟩
  · -- right continuity of the cumulative distribution function
    have hge : 1 / 2 ≤ cdf ν m := by
      have hlim : Tendsto (fun n : ℕ => cdf ν (m + 1 / (n + 1))) atTop (𝓝 (cdf ν m)) := by
        refine ((cdf ν).right_continuous m).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨by simpa using hseq.const_add m, ?_⟩)
        exact Eventually.of_forall fun n => le_add_of_nonneg_right (by positivity)
      refine ge_of_tendsto' hlim fun n => ?_
      obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hne
        (show sInf S < m + 1 / ((n : ℝ) + 1) from lt_add_of_pos_right _ (by positivity))
      exact hy.trans (monotone_cdf ν hylt.le)
    rwa [cdf_eq_real, hν, map_measureReal_apply hf measurableSet_Iic] at hge
  · have hlt : ν.real (Iio m) ≤ 1 / 2 := by
      have hmono : Monotone fun n : ℕ => Iic (m - 1 / ((n : ℝ) + 1)) := fun a b hab =>
        Iic_subset_Iic.2 (sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hab 1)) m)
      have hU : ⋃ n : ℕ, Iic (m - 1 / ((n : ℝ) + 1)) = Iio m := by
        ext x
        simp only [mem_iUnion, mem_Iic, mem_Iio]
        constructor
        · rintro ⟨n, hn⟩
          exact hn.trans_lt (sub_lt_self _ (by positivity))
        · intro hx
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
          exact ⟨n, by linarith⟩
      have hlim := (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp
        (tendsto_measure_iUnion_atTop (μ := ν) hmono)
      rw [hU] at hlim
      refine le_of_tendsto' hlim fun n => ?_
      change ν.real (Iic (m - 1 / ((n : ℝ) + 1))) ≤ 1 / 2
      rw [← cdf_eq_real]
      by_contra h
      have := csInf_le hbdd (show m - 1 / ((n : ℝ) + 1) ∈ S from (not_le.1 h).le)
      rw [← hm] at this
      exact (sub_lt_self m (by positivity : (0 : ℝ) < 1 / (n + 1))).not_ge this
    have hcompl : {ω | m ≤ f ω} = (f ⁻¹' Iio m)ᶜ := by
      ext ω
      simp
    rw [hν, map_measureReal_apply hf measurableSet_Iio] at hlt
    rw [hcompl, probReal_compl_eq_one_sub (hf measurableSet_Iio)]
    linarith

end ProbabilityTheory
