/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.CGFQuotient
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
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
  set U : ℝ := (Real.sqrt N)⁻¹ * |β| * (∑ p : FinPairs N, |g p|) + |h| * (N : ℝ)
  have hU_nonneg : 0 ≤ U := by positivity
  have hN_log2_nonneg : 0 ≤ (N : ℝ) * Real.log 2 := by
    refine mul_nonneg (Nat.cast_nonneg N) ?_
    exact Real.log_nonneg (by norm_num)
  have h_term_le (σ : Fin N → ℤˣ) : skGibbsEnergy N β h g σ ≤ U := by
    have := abs_skGibbsEnergy_le N β h g σ
    linarith [le_abs_self (skGibbsEnergy N β h g σ)]
  have h_neg_term_le (σ : Fin N → ℤˣ) : -U ≤ skGibbsEnergy N β h g σ := by
    have := abs_skGibbsEnergy_le N β h g σ
    linarith [neg_le_of_abs_le this]
  have h_exp_le (σ : Fin N → ℤˣ) :
      Real.exp (skGibbsEnergy N β h g σ) ≤ Real.exp U :=
    Real.exp_le_exp.mpr (h_term_le σ)
  have h_sum_le :
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ≤
        (2 : ℝ) ^ N * Real.exp U := by
    calc (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
      _ ≤ ∑ _ : Fin N → ℤˣ, Real.exp U := Finset.sum_le_sum fun σ _ => h_exp_le σ
      _ = (Finset.univ : Finset (Fin N → ℤˣ)).card * Real.exp U := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 : ℝ) ^ N * Real.exp U := by
        rw [Finset.card_univ, card_spin_configurations, Fintype.card_fin]
        norm_cast
  have h_sum_ge :
      Real.exp (-U) ≤ ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ) := by
    have h_mem : (fun _ : Fin N => (1 : ℤˣ)) ∈ (Finset.univ : Finset (Fin N → ℤˣ)) :=
      Finset.mem_univ _
    calc Real.exp (-U)
      _ ≤ Real.exp (skGibbsEnergy N β h g (fun _ => 1)) :=
        Real.exp_le_exp.mpr (h_neg_term_le (fun _ => 1))
      _ ≤ ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ) :=
        Finset.single_le_sum (fun _ _ => (Real.exp_pos _).le) h_mem
  have h_log_le :
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ≤
        (N : ℝ) * Real.log 2 + U := by
    have hpos : 0 < (2 : ℝ) ^ N * Real.exp U := by positivity
    have h_le := (Real.log_le_log_iff (skPartition_pos N β h g) hpos).mpr h_sum_le
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h_le
    linarith
  have h_log_ge :
      -((N : ℝ) * Real.log 2 + U) ≤
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) := by
    have hpos : 0 < Real.exp (-U) := Real.exp_pos _
    have h_ge := (Real.log_le_log_iff hpos (skPartition_pos N β h g)).mpr h_sum_ge
    rw [Real.log_exp] at h_ge
    linarith
  have hU_def : (N : ℝ) * Real.log 2 + U =
      (N : ℝ) * Real.log 2 + |h| * (N : ℝ) +
        (Real.sqrt N)⁻¹ * |β| * (∑ p : FinPairs N, |g p|) := by ring
  rw [abs_le]
  refine ⟨by linarith [h_log_ge], by linarith [h_log_le]⟩

/-- For every `t : ℝ`, `exp (t * log Z_N)` is integrable against the Gaussian disorder. -/
theorem integrable_exp_mul_log_skPartition (N : ℕ) (β h t : ℝ) :
    Integrable (fun g : FinPairs N → ℝ =>
      Real.exp (t * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  set μ := (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  set C := |t| * ((N : ℝ) * Real.log 2 + |h| * (N : ℝ))
  set K := |t| * ((Real.sqrt N)⁻¹ * |β|)
  have hint_bound : Integrable (fun g : FinPairs N → ℝ =>
      Real.exp C * Real.exp (∑ p : FinPairs N, K * |g p|)) μ := by
    have hint_sum := integrable_exp_sum_mul_abs_pi (ι := FinPairs N) (fun _ => K)
    exact hint_sum.const_mul (Real.exp C)
  refine Integrable.mono' hint_bound ?_ (ae_of_all _ fun g => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    exact (measurable_const.mul (measurable_log_skPartition N β h)).exp
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h_abs := abs_log_skPartition_le N β h g
    have ht_le : t * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ≤
        C + ∑ p : FinPairs N, K * |g p| := by
      calc t * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        _ ≤ |t * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))| :=
          le_abs_self _
        _ = |t| * |Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))| :=
          abs_mul _ _
        _ ≤ |t| * ((N : ℝ) * Real.log 2 + |h| * (N : ℝ) +
              (Real.sqrt N)⁻¹ * |β| * (∑ p : FinPairs N, |g p|)) := by
          gcongr
        _ = C + |t| * ((Real.sqrt N)⁻¹ * |β| * (∑ p : FinPairs N, |g p|)) := by ring
        _ = C + K * (∑ p : FinPairs N, |g p|) := by ring
        _ = C + ∑ p : FinPairs N, K * |g p| := by rw [Finset.mul_sum]
    calc Real.exp (t * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)))
      _ ≤ Real.exp (C + ∑ p : FinPairs N, K * |g p|) := Real.exp_le_exp.mpr ht_le
      _ = Real.exp C * Real.exp (∑ p : FinPairs N, K * |g p|) := Real.exp_add _ _

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
theorem tendsto_inv_mul_log_integral_rpow_skPartition_div {N : ℕ} (hN : 0 < N) (β h : ℝ) :
    Tendsto (fun t => (1 / ((N : ℝ) * t)) * Real.log (∫ g : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)))
      (𝓝[>] 0)
      (𝓝 ((1 / (N : ℝ)) * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) := by
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h_lim := (tendsto_log_integral_rpow_skPartition_div N β h).const_mul (1 / (N : ℝ))
  refine h_lim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_ne : t ≠ 0 := ht.ne'
  have h_alg : 1 / ((N : ℝ) * t) * Real.log (∫ g : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      1 / (N : ℝ) * (Real.log (∫ g : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) / t) := by
    ring
  rw [h_alg]

end SpinGlasses
