/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Linearization
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Angular Integrals for the Cho-Saul Kernel

This file identifies the common positive angular sector of two directions separated by
`theta`, then evaluates the ReLU and ReLU-indicator integrals on that sector.
-/

@[expose] public section

open Real MeasureTheory Set

namespace NTK

private lemma cos_nonpos_of_mem_neg_side {x : ℝ}
    (hx_lower : -Real.pi < x) (hx_upper : x ≤ -(Real.pi / 2)) :
    Real.cos x ≤ 0 := by
  rw [← Real.cos_neg x]
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · linarith
  · linarith [Real.pi_pos]

private lemma angular_relu_support (theta : ℝ) (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi) :
    ∫ phi in Set.Ioo (-Real.pi) Real.pi,
      relu (Real.cos phi) * relu (Real.cos (phi - theta)) =
    ∫ phi in Set.Ioc (theta - Real.pi / 2) (Real.pi / 2),
      Real.cos phi * Real.cos (phi - theta) := by
  have ha : -Real.pi < theta - Real.pi / 2 := by linarith [Real.pi_pos]
  have hb : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with phi
  by_cases htarget : phi ∈ Set.Ioo (-Real.pi) Real.pi
  · simp only [Set.indicator_of_mem htarget]
    by_cases hleft : phi ≤ theta - Real.pi / 2
    · have hnot : phi ∉ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) := by
        simp only [Set.mem_Ioc, not_and_or]
        exact Or.inl (not_lt_of_ge hleft)
      rw [Set.indicator_of_notMem hnot]
      by_cases hphi : phi ≤ -(Real.pi / 2)
      · have hc : Real.cos phi ≤ 0 := cos_nonpos_of_mem_neg_side htarget.1 hphi
        simp [relu, max_eq_right hc]
      · have hphi_lower : -(Real.pi / 2) < phi := lt_of_not_ge hphi
        have harg_upper : phi - theta ≤ -(Real.pi / 2) := by linarith
        have harg_lower : -(Real.pi + Real.pi / 2) ≤ phi - theta := by linarith
        have hc : Real.cos (phi - theta) ≤ 0 := by
          rw [← Real.cos_neg (phi - theta)]
          apply Real.cos_nonpos_of_pi_div_two_le_of_le
          · linarith
          · linarith
        simp [relu, max_eq_right hc]
    · have hleft' : theta - Real.pi / 2 < phi := lt_of_not_ge hleft
      by_cases hright : phi ≤ Real.pi / 2
      · have hmem : phi ∈ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) := ⟨hleft', hright⟩
        rw [Set.indicator_of_mem hmem]
        have hc0 : 0 ≤ Real.cos phi :=
          Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hright
        have hc1 : 0 ≤ Real.cos (phi - theta) :=
          Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [relu, max_eq_left hc0, max_eq_left hc1]
      · have hnot : phi ∉ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) := by
          simp only [Set.mem_Ioc, not_and_or]
          exact Or.inr hright
        rw [Set.indicator_of_notMem hnot]
        have hc : Real.cos phi ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_ge hright)
            (by linarith [htarget.2, Real.pi_pos])
        simp [relu, max_eq_right hc]
  · have hnot : phi ∉ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) := by
      intro h
      exact htarget ⟨ha.trans h.1, h.2.trans_lt hb⟩
    simp [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hnot]

lemma angular_relu_integral (theta : ℝ) (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi) :
    ∫ phi in Set.Ioo (-Real.pi) Real.pi,
      relu (Real.cos phi) * relu (Real.cos (phi - theta)) =
      (Real.sin theta + (Real.pi - theta) * Real.cos theta) / 2 := by
  have hab : theta - Real.pi / 2 ≤ Real.pi / 2 := by linarith
  rw [angular_relu_support theta htheta0 hthetapi, ← intervalIntegral.integral_of_le hab]
  simp_rw [Real.cos_sub]
  have hcont1 : IntervalIntegrable (fun phi : ℝ => Real.cos phi ^ 2) volume
      (theta - Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_cos.pow 2).intervalIntegrable _ _
  have hcont2 : IntervalIntegrable (fun phi : ℝ => Real.sin phi * Real.cos phi) volume
      (theta - Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable _ _
  calc
    ∫ phi in theta - Real.pi / 2..Real.pi / 2,
        Real.cos phi * (Real.cos phi * Real.cos theta + Real.sin phi * Real.sin theta)
      = Real.cos theta * (∫ phi in theta - Real.pi / 2..Real.pi / 2, Real.cos phi ^ 2) +
          Real.sin theta * (∫ phi in theta - Real.pi / 2..Real.pi / 2,
            Real.sin phi * Real.cos phi) := by
          rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
          rw [← intervalIntegral.integral_add (hcont1.const_mul _) (hcont2.const_mul _)]
          apply intervalIntegral.integral_congr
          intro _ _
          ring
    _ = Real.cos theta *
          ((Real.cos (Real.pi / 2) * Real.sin (Real.pi / 2) -
              Real.cos (theta - Real.pi / 2) * Real.sin (theta - Real.pi / 2) +
              Real.pi / 2 - (theta - Real.pi / 2)) / 2) +
        Real.sin theta *
          ((Real.sin (Real.pi / 2) ^ 2 - Real.sin (theta - Real.pi / 2) ^ 2) / 2) := by
          rw [integral_cos_sq, integral_sin_mul_cos₁]
    _ = (Real.sin theta + (Real.pi - theta) * Real.cos theta) / 2 := by
          rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
          rw [show Real.cos (theta - Real.pi / 2) = Real.sin theta by
            exact Real.cos_sub_pi_div_two theta]
          rw [show Real.sin (theta - Real.pi / 2) = -Real.cos theta by
            exact Real.sin_sub_pi_div_two theta]
          nlinarith [Real.sin_sq_add_cos_sq theta]

private lemma angular_indicator_support (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hthetapi : theta ≤ Real.pi) :
    ∫ phi in Set.Ioo (-Real.pi) Real.pi,
      reluIndicator (Real.cos phi) * reluIndicator (Real.cos (phi - theta)) =
    ∫ _ in Set.Ioc (theta - Real.pi / 2) (Real.pi / 2), (1 : ℝ) := by
  have ha : -Real.pi < theta - Real.pi / 2 := by linarith [Real.pi_pos]
  have hb : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  have hne_a : ∀ᵐ phi : ℝ, phi ≠ theta - Real.pi / 2 := by simp [ae_iff, measure_singleton]
  have hne_b : ∀ᵐ phi : ℝ, phi ≠ Real.pi / 2 := by simp [ae_iff, measure_singleton]
  have hne_neg_b : ∀ᵐ phi : ℝ, phi ≠ -(Real.pi / 2) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne_a, hne_b, hne_neg_b] with phi hne_a hne_b hne_neg_b
  by_cases htarget : phi ∈ Set.Ioo (-Real.pi) Real.pi
  · simp only [Set.indicator_of_mem htarget]
    by_cases hleft : phi < theta - Real.pi / 2
    · have hnot : phi ∉ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) := by
        simp only [Set.mem_Ioc, not_and_or]
        exact Or.inl (not_lt_of_ge hleft.le)
      rw [Set.indicator_of_notMem hnot]
      by_cases hphi : phi < -(Real.pi / 2)
      · have hc : Real.cos phi < 0 := by
          rw [← Real.cos_neg phi]
          apply Real.cos_neg_of_pi_div_two_lt_of_lt
          · linarith
          · linarith [htarget.1, Real.pi_pos]
        simp [reluIndicator, not_le.mpr hc]
      · have hphi_lower : -(Real.pi / 2) < phi :=
          lt_of_le_of_ne (le_of_not_gt hphi) (Ne.symm hne_neg_b)
        have harg_upper : phi - theta < -(Real.pi / 2) := by linarith
        have harg_lower : -(Real.pi + Real.pi / 2) < phi - theta := by linarith
        have hc : Real.cos (phi - theta) < 0 := by
          rw [← Real.cos_neg (phi - theta)]
          apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> linarith
        simp [reluIndicator, not_le.mpr hc]
    · have hleft' : theta - Real.pi / 2 < phi :=
        lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hne_a)
      by_cases hright : phi < Real.pi / 2
      · have hmem : phi ∈ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) :=
          ⟨hleft', hright.le⟩
        rw [Set.indicator_of_mem hmem]
        have hc0 : 0 ≤ Real.cos phi :=
          Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hright.le
        have hc1 : 0 ≤ Real.cos (phi - theta) :=
          Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [reluIndicator, hc0, hc1]
      · have hright' : Real.pi / 2 < phi :=
          lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hne_b)
        have hnot : phi ∉ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) := by
          simp only [Set.mem_Ioc, not_and_or]
          exact Or.inr (not_le_of_gt hright')
        rw [Set.indicator_of_notMem hnot]
        have hc : Real.cos phi < 0 :=
          Real.cos_neg_of_pi_div_two_lt_of_lt hright' (by linarith [htarget.2, Real.pi_pos])
        simp [reluIndicator, not_le.mpr hc]
  · have hnot : phi ∉ Set.Ioc (theta - Real.pi / 2) (Real.pi / 2) := by
      intro h
      exact htarget ⟨ha.trans h.1, h.2.trans_lt hb⟩
    simp [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hnot]

lemma angular_indicator_integral (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hthetapi : theta ≤ Real.pi) :
    ∫ phi in Set.Ioo (-Real.pi) Real.pi,
      reluIndicator (Real.cos phi) * reluIndicator (Real.cos (phi - theta)) =
      Real.pi - theta := by
  have hab : theta - Real.pi / 2 ≤ Real.pi / 2 := by linarith
  rw [angular_indicator_support theta htheta0 hthetapi]
  rw [MeasureTheory.integral_const]
  simp [hab]
  ring

end NTK
