/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.DeepNNGPTheorems
public import LeanMachineLearning.Optimization.NTK.Initialization.ConditionalConcentration

/-!
# Concentration of Gaussian-Weighted Averages (Readout Layer)

The backward sensitivity at the top hidden layer is `g_{d-1} = W_d ⊙ φ'(h_{d-1})` with an
independent
standard Gaussian readout `W_d`, so its Gram entry is `n⁻¹ ∑ⱼ aⱼ² yⱼ` with
`yⱼ = φ'(h^α_j) φ'(h^β_j)`.
`NTK.tendstoInMeasure_gaussianSq_weighted_average` shows this has the same limit as the unweighted
average, abstractly in the weights `y`.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace NTK

/-- **Gaussian-weighted averages.** Let `a ~ 𝒩(0, I)` be independent of the weights `y n w`. If the
plain average `n⁻¹ ∑ⱼ yⱼ → c₁` and the average of squares `n⁻¹ ∑ⱼ yⱼ² → c₂` converge in measure
(the latter is only used to make the fluctuation tight), then the Gaussian-weighted average
`n⁻¹ ∑ⱼ aⱼ² yⱼ → c₁` in measure.

Proof: `n⁻¹ ∑ⱼ aⱼ² yⱼ - n⁻¹ ∑ⱼ yⱼ = n⁻¹ ∑ⱼ (aⱼ² - 1) yⱼ` has conditional Chebyshev bound
`Var(a₁² - 1) · (n⁻¹ ∑ⱼ yⱼ²) / (n ε²)` (`chebyshev_centeredSquare_weighted`); Fubini and
`tendsto_of_lintegral_section_bound` localize `n⁻¹ ∑ⱼ yⱼ²` near `c₂`. -/
theorem tendstoInMeasure_gaussianSq_weighted_average
    {Ω : Type*} [MeasurableSpace Ω] (νH : Measure Ω) [IsProbabilityMeasure νH]
    (y : ∀ n : ℕ, Ω → Fin n → ℝ) (hy : ∀ n j, Measurable fun w => y n w j) (c₁ c₂ : ℝ)
    (hD : TendstoInMeasure νH (fun (n : ℕ) (w : Ω) => (n : ℝ)⁻¹ * ∑ j : Fin n, y n w j) atTop
      (fun _ => c₁))
    (hM : TendstoInMeasure νH (fun (n : ℕ) (w : Ω) => (n : ℝ)⁻¹ * ∑ j : Fin n, y n w j ^ 2) atTop
      (fun _ => c₂)) :
    TendstoInMeasure (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (q : Ω × (ℕ → ℝ)) => (n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val ^ 2 * y n q.1 j)
      atTop (fun _ => c₁) := by
  have hmp : MeasurePreserving Prod.fst (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      νH := measurePreserving_fst
  have hmeasD : ∀ n : ℕ, Measurable (fun w : Ω => (n : ℝ)⁻¹ * ∑ j : Fin n, y n w j) :=
    fun n => measurable_const.mul (Finset.measurable_sum _ fun j _ => hy n j)
  have hmeasM : ∀ n : ℕ, Measurable (fun w : Ω => (n : ℝ)⁻¹ * ∑ j : Fin n, y n w j ^ 2) :=
    fun n => measurable_const.mul (Finset.measurable_sum _ fun j _ => (hy n j).pow_const 2)
  have hD0 := tendstoInMeasure_comp_measurePreserving hD hmp hmeasD measurable_const
  have hM0 := tendstoInMeasure_comp_measurePreserving hM hmp hmeasM measurable_const
  -- the fluctuation `G - D = n⁻¹ ∑ (aⱼ² - 1) yⱼ` tends to `0` in measure
  have hdev : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
        {q : Ω × (ℕ → ℝ) | ε ≤ dist ((n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val ^ 2 * y n q.1 j)
          ((n : ℝ)⁻¹ * ∑ j : Fin n, y n q.1 j)}) atTop (nhds 0) := by
    intro ε hε
    set S : ℕ → Set (Ω × (ℕ → ℝ)) := fun n =>
      {q | ε ≤ dist ((n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val ^ 2 * y n q.1 j)
        ((n : ℝ)⁻¹ * ∑ j : Fin n, y n q.1 j)} with hS
    have hS_meas : ∀ n, MeasurableSet (S n) := by
      intro n
      have h1 : Measurable (fun q : Ω × (ℕ → ℝ) =>
          (n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val ^ 2 * y n q.1 j) :=
        measurable_const.mul (Finset.measurable_sum _ fun j _ =>
          (((measurable_pi_apply j.val).comp measurable_snd).pow_const 2).mul
            ((hy n j).comp measurable_fst))
      have h2 : Measurable (fun q : Ω × (ℕ → ℝ) => (n : ℝ)⁻¹ * ∑ j : Fin n, y n q.1 j) :=
        measurable_const.mul (Finset.measurable_sum _ fun j _ => (hy n j).comp measurable_fst)
      exact measurableSet_le measurable_const (h1.dist h2)
    have hP : ∀ n, (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) (S n) =
        ∫⁻ w, (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) {v | (w, v) ∈ S n} ∂νH :=
      fun n => Measure.prod_apply (hS_meas n)
    -- localization of the empirical second moment
    set Mn : ℕ → Ω → ℝ := fun n w => (n : ℝ)⁻¹ * ∑ j : Fin n, y n w j ^ 2 with hMn
    set E : ℕ → Set Ω := fun n => {w | c₂ + 1 < Mn n w} with hE_def
    set u : ℕ → ℝ≥0∞ := fun n => (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      {q : Ω × (ℕ → ℝ) | (1 : ℝ≥0∞) ≤ edist (Mn n q.1) c₂} with hu_def
    have hu : Tendsto u atTop (nhds 0) := hM0 1 one_pos
    have hE : ∀ n, νH (E n) ≤ u n := by
      intro n
      have h1 : νH (E n) = (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
          (E n ×ˢ Set.univ) := by
        rw [Measure.prod_prod, measure_univ, mul_one]
      rw [h1]
      refine measure_mono ?_
      rintro ⟨w, v⟩ ⟨hw, -⟩
      simp only [Set.mem_ofPred_eq, edist_dist, Real.dist_eq]
      exact ENNReal.one_le_ofReal.2 (by
        have : c₂ + 1 < Mn n w := hw
        rw [le_abs]; left; linarith)
    set c : ℕ → ℝ≥0∞ := fun n =>
      ENNReal.ofReal ((ProbabilityTheory.variance (fun x : ℝ => x ^ 2 - 1) (gaussianReal 0 1)) * (c₂
          + 1) / ((n : ℝ) * ε ^ 2)) with hc_def
    have hc : Tendsto c atTop (nhds 0) := by
      have h0 : Tendsto (fun n : ℕ => ((ProbabilityTheory.variance (fun x : ℝ => x ^ 2 - 1)
          (gaussianReal 0 1)) * (c₂ + 1) / ε ^ 2) / (n : ℝ))
          atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal
          (((ProbabilityTheory.variance (fun x : ℝ => x ^ 2 - 1) (gaussianReal 0 1)) * (c₂ + 1) / ε
              ^ 2) / (n : ℝ))) atTop (nhds 0) := by
        simpa using ENNReal.tendsto_ofReal h0
      refine h1.congr fun n => ?_
      simp only [hc_def]
      congr 1
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have : (n : ℝ) ≠ 0 := by positivity
        field_simp
    have hσ : ∀ᶠ n in atTop, ∀ w, (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        {v | (w, v) ∈ S n} ≤ (E n).indicator (1 : Ω → ℝ≥0∞) w + c n := by
      filter_upwards [eventually_gt_atTop 0] with n hn w
      by_cases hw : w ∈ E n
      · rw [Set.indicator_of_mem hw]
        exact prob_le_one.trans le_self_add
      · rw [Set.indicator_of_notMem hw, zero_add]
        have hrestr : Measurable (fun v : ℕ → ℝ => fun j : Fin n => v j.val) :=
          measurable_pi_iff.2 fun j => measurable_pi_apply j.val
        have hT : MeasurableSet {a : Fin n → ℝ |
            ε ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, (a j ^ 2 - 1) * y n w j|} := by
          refine measurableSet_le measurable_const (continuous_abs.measurable.comp ?_)
          exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
            (((measurable_pi_apply j).pow_const 2).sub_const 1).mul_const _)
        have hsec : {v | (w, v) ∈ S n} = (fun v : ℕ → ℝ => fun j : Fin n => v j.val) ⁻¹'
            {a : Fin n → ℝ | ε ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, (a j ^ 2 - 1) * y n w j|} := by
          ext v
          simp only [hS, Set.mem_ofPred_eq, Set.mem_preimage, Real.dist_eq]
          have : (n : ℝ)⁻¹ * ∑ j : Fin n, v j.val ^ 2 * y n w j - (n : ℝ)⁻¹ * ∑ j : Fin n, y n w j =
              (n : ℝ)⁻¹ * ∑ j : Fin n, (v j.val ^ 2 - 1) * y n w j := by
            rw [← mul_sub, ← Finset.sum_sub_distrib]
            congr 1
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [this]
        rw [hsec, ← Measure.map_apply hrestr hT, map_infinitePi_real_eq_gaussianReadoutMeasure]
        refine (chebyshev_centeredSquare_weighted n hn (y n w) hε).trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hMw : Mn n w ≤ c₂ + 1 := not_lt.1 hw
        have hsum : ∑ j : Fin n, y n w j ^ 2 = n * Mn n w := by
          simp only [hMn]
          have hn0 : (n : ℝ) ≠ 0 := by positivity
          field_simp
        rw [hsum]
        have hV := gaussianSqCenteredVariance_nonneg
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        calc (ProbabilityTheory.variance (fun x : ℝ => x ^ 2 - 1) (gaussianReal 0 1)) * (n * Mn n
            w) / ((n : ℝ) ^ 2 * ε ^ 2)
            = (ProbabilityTheory.variance (fun x : ℝ => x ^ 2 - 1)
                (gaussianReal 0 1)) * Mn n w / ((n : ℝ) * ε ^ 2) := by
              field_simp
          _ ≤ (ProbabilityTheory.variance (fun x : ℝ => x ^ 2 - 1) (gaussianReal 0 1)) * (c₂ +
              1) / ((n : ℝ) * ε ^ 2) := by
              gcongr
    exact tendsto_of_lintegral_section_bound νH
      (fun n => (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) (S n))
      (fun n w => (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) {v | (w, v) ∈ S n})
      E u c hP hσ hE hu hc
  exact tendstoInMeasure_trans hdev hD0

end NTK

end
