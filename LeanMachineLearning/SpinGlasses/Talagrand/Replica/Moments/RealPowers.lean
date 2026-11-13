/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.CGFQuotient
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.LogSumExp
public import LeanMachineLearning.SpinGlasses.Talagrand.GaussianFluctuation.SKGaussianFluctuation
public import LeanMachineLearning.SpinGlasses.Basic

/-!
# Finite-system real moments of the SK partition function (Talagrand, Eqs. (1.409)-(1.410))

This file formalizes the `t → 0+` limit of the real moments of the SK partition function
`Z_N = ∑_σ exp (skGibbsEnergy N β h g σ)`.

At fixed finite size `N`, the logarithm `log Z_N` is bounded by a constant plus a linear
combination of absolute Gaussian disorder variables `∑_p |g_p|`. Consequently, `exp (t * log Z_N)`
is integrable against the disorder measure for all `t : ℝ`, so `0` belongs to the interior of the
exponential integrability set.

Applying the general cumulant-generating function derivative quotient theorem yields:
* Eq. (1.409): `(1 / t) * log 𝔼 Z_N^t → 𝔼 log Z_N` as `t → 0+`.
* Eq. (1.410): `(1 / (N * t)) * log 𝔼 Z_N^t → (1 / N) * 𝔼 log Z_N` as `t → 0+` for `N > 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SpinGlasses

/-- The SK partition sum is strictly positive for every disorder realization `g`. -/
theorem skPartition_pos (N : ℕ) (β h : ℝ) (g : FinPairs N → ℝ) :
    0 < ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨fun _ => 1, Finset.mem_univ _⟩

/-- The logarithm of the SK partition function is measurable in the disorder. -/
theorem measurable_log_skPartition (N : ℕ) (β h : ℝ) :
    Measurable fun g : FinPairs N → ℝ =>
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) := by
  refine (Finset.measurable_sum _ fun σ _ => ?_).log
  exact (measurable_skGibbsEnergy N β h σ).exp

/-- The absolute value of the logarithm of the partition function is bounded by
`N * log 2 + |h| * N + (√N)⁻¹ * |β| * ∑_p |g_p|`. -/
lemma abs_log_skPartition_le (N : ℕ) (β h : ℝ) (g : FinPairs N → ℝ) :
    |Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))| ≤
      (N : ℝ) * Real.log 2 + |h| * (N : ℝ) +
        (Real.sqrt N)⁻¹ * |β| * (∑ p : FinPairs N, |g p|) := by
  have hlog : Real.log (Fintype.card (Fin N → ℤˣ) : ℝ) = (N : ℝ) * Real.log 2 := by
    simpa using log_card_spin_configurations (ι := Fin N)
  have h_le := abs_log_sum_exp_le_of_forall
    (skGibbsEnergy N β h g) (abs_skGibbsEnergy_le N β h g)
  rw [hlog] at h_le
  linarith

/-- For every `t : ℝ`, `exp (t * log Z_N)` is integrable against the Gaussian disorder. -/
theorem integrable_exp_mul_log_skPartition (N : ℕ) (β h t : ℝ) :
    Integrable (fun g : FinPairs N → ℝ =>
      Real.exp (t * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  have hm := (measurable_log_skPartition N β h).aemeasurable
    (μ := Measure.pi fun _ => gaussianReal 0 1)
  have hbd (g : FinPairs N → ℝ) :
      |Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))| ≤
        ((N : ℝ) * Real.log 2 + |h| * (N : ℝ)) +
          ∑ p : FinPairs N, ((Real.sqrt N)⁻¹ * |β|) * |g p| := by
    have := abs_log_skPartition_le N β h g
    rw [Finset.mul_sum] at this
    linarith
  exact ProbabilityTheory.integrable_exp_of_linear_bound hm hbd t

/-- `0` belongs to the interior of the exponential integrability set of `log Z_N`. -/
lemma mem_interior_integrableExpSet_log_skPartition (N : ℕ) (β h : ℝ) :
    0 ∈ interior (integrableExpSet
      (fun g : FinPairs N → ℝ =>
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) :=
  mem_interior_integrableExpSet_of_forall (integrable_exp_mul_log_skPartition N β h)

/-- **Talagrand, Eq. (1.409).** For fixed `N`, the real-moment difference quotient
`(1 / t) * log 𝔼 Z_N^t` tends to the quenched free energy `𝔼 log Z_N` as `t → 0+`. -/
theorem tendsto_log_integral_rpow_skPartition_div (N : ℕ) (β h : ℝ) :
    Tendsto (fun t => Real.log (∫ g : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) / t)
      (𝓝[>] 0)
      (𝓝 (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) := by
  have hZ : ∀ᵐ g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1),
      0 < ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ) :=
    Eventually.of_forall (skPartition_pos N β h)
  exact tendsto_log_integral_rpow_div_zero_pos hZ
    (mem_interior_integrableExpSet_log_skPartition N β h)

/-- **Talagrand, Eq. (1.410).** Rescaled by `1 / N`, the real-moment limit satisfies
`(1 / (N * t)) * log 𝔼 Z_N^t → (1 / N) * 𝔼 log Z_N` as `t → 0+` for `0 < N`. -/
theorem tendsto_inv_mul_log_integral_rpow_skPartition_div {N : ℕ} (_hN : 0 < N) (β h : ℝ) :
    Tendsto (fun t => (1 / ((N : ℝ) * t)) * Real.log (∫ g : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)))
      (𝓝[>] 0)
      (𝓝 ((1 / (N : ℝ)) * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) := by
  simpa only [one_div, div_eq_mul_inv, mul_inv_rev,
    mul_assoc, mul_left_comm, mul_comm]
    using (tendsto_log_integral_rpow_skPartition_div N β h).const_mul
      (1 / (N : ℝ))

end SpinGlasses
