/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Hoeffding's lemma for a two-point law

For `q ∈ [-1, 1]`, a `±1`-valued variable with mean `q` satisfies
`𝔼 exp (u (ε - q)) = (cosh u + q sinh u) exp (-q u) ≤ exp (u² / 2)` (Hoeffding's lemma for a
variable of range length `2`, applied to the explicit two-point law).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- `cosh u + q sinh u ≥ 0` for `|q| ≤ 1`: it is `𝔼 exp (u ε)` for `ε = ±1` with `𝔼 ε = q`. -/
theorem cosh_add_mul_sinh_nonneg (q : ℝ) (hq : |q| ≤ 1) (u : ℝ) :
    0 ≤ Real.cosh u + q * Real.sinh u := by
  obtain ⟨h1, h2⟩ := abs_le.1 hq
  rw [Real.cosh_eq, Real.sinh_eq]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + q) (Real.exp_pos u).le,
    mul_nonneg (by linarith : 0 ≤ 1 - q) (Real.exp_pos (-u)).le]

/-- **Hoeffding for a two-point law:** `(cosh u + q sinh u) e^{-q u} ≤ e^{u² / 2}` for `|q| ≤ 1`.
The left side is `𝔼 exp (u (ε - q))` for `ε = ±1` with `𝔼 ε = q`. -/
theorem cosh_add_mul_sinh_mul_exp_neg_le (q : ℝ) (hq : |q| ≤ 1) (u : ℝ) :
    (Real.cosh u + q * Real.sinh u) * Real.exp (-(q * u)) ≤ Real.exp (u ^ 2 / 2) := by
  have hq1 : -1 ≤ q ∧ q ≤ 1 := abs_le.1 hq
  obtain ⟨ν, hν⟩ : ∃ ν : Measure ℝ, ν = ENNReal.ofReal ((1 + q) / 2) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal ((1 - q) / 2) • Measure.dirac (-1 : ℝ) := ⟨_, rfl⟩
  have hint : ∀ g : ℝ → ℝ, Integrable g ν := fun g => by
    rw [hν]
    refine Integrable.add_measure ?_ ?_
    · exact (integrable_dirac enorm_lt_top).smul_measure (by simp)
    · exact (integrable_dirac enorm_lt_top).smul_measure (by simp)
  have hI : ∀ g : ℝ → ℝ, ∫ x, g x ∂ν = (1 + q) / 2 * g 1 + (1 - q) / 2 * g (-1) := fun g => by
    rw [hν, integral_add_measure ((integrable_dirac enorm_lt_top).smul_measure (by simp))
      ((integrable_dirac enorm_lt_top).smul_measure (by simp)), integral_smul_measure,
      integral_smul_measure, integral_dirac, integral_dirac,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    simp
  have hprob : IsProbabilityMeasure ν := ⟨by
    rw [hν]
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    simp only [ENNReal.ofReal_eq_one]
    ring⟩
  have hmean : ∫ x, x ∂ν = q := by
    rw [hI (fun x => x)]; ring
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hν]
    refine ae_add_measure_iff.2 ⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩
    · exact (ae_dirac_iff (p := fun x : ℝ => x ∈ Set.Icc (-1 : ℝ) 1)
        measurableSet_Icc).2 ⟨by norm_num, by norm_num⟩
    · exact (ae_dirac_iff (p := fun x : ℝ => x ∈ Set.Icc (-1 : ℝ) 1)
        measurableSet_Icc).2 ⟨by norm_num, by norm_num⟩
  have hH := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := fun x : ℝ => x) (a := -1) (b := 1)
    measurable_id.aemeasurable hae
  have h2 := hH.mgf_le u
  simp only [mgf] at h2
  rw [hI, hmean] at h2
  have hc : (((‖(1 : ℝ) - -1‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 := by
    have : ‖(1 : ℝ) - -1‖₊ = 2 := by
      rw [← NNReal.coe_inj]; norm_num
    rw [this]; norm_num
  rw [hc, one_mul] at h2
  have e : (1 + q) / 2 * Real.exp (u * (1 - q)) + (1 - q) / 2 * Real.exp (u * (-1 - q)) =
      (Real.cosh u + q * Real.sinh u) * Real.exp (-(q * u)) := by
    rw [Real.cosh_eq, Real.sinh_eq, show u * (1 - q) = u + -(q * u) by ring,
      show u * (-1 - q) = -u + -(q * u) by ring, Real.exp_add, Real.exp_add]
    ring
  rwa [e] at h2

end ProbabilityTheory
