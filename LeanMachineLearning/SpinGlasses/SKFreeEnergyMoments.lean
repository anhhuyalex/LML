/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianTiltedFreeEnergy
public import LeanMachineLearning.SpinGlasses.SKGaussianFluctuation
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-!
# Moments of the free-energy fluctuation of the SK model (Talagrand, Lemma 1.4.12)

For the SK model with deterministic field `h`, put `A_N = N⁻¹ log Z_N` and
`p_N = 𝔼 A_N`.  The free energy `log Z_N` is a Lipschitz function of the Gaussian disorder, hence
sub-Gaussian (`hasSubgaussianMGF_log_sum_exp`), and this gives Eq. (1.113) of the book for `c = 0`:
`𝔼 |A_N - p_N|^k ≤ K_k / N^{k/2}` with `K_k = 2 k! exp (β² / 2)`, for every `β` and `h`.

## Main declarations

* `SpinGlasses.integral_pow_abs_free_energy_sub_le`: `√N^k 𝔼 |A_N - p_N|^k ≤ 2 k! exp (β² / 2)`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.4.12.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix NNReal

namespace SpinGlasses

/-- **Lemma 1.4.12 (Talagrand, Eq. (1.113) with deterministic field).**  The free energy
`A_N = N⁻¹ log Z_N` of the SK model has moments of every order `k` concentrated at scale
`N^{-1/2}`: `(√N)^k 𝔼 |A_N - 𝔼 A_N|^k ≤ 2 k! exp (β² / 2)` for all `β`, `h` and `N > 0`, and
`|A_N - 𝔼 A_N|^k` is integrable.  The constant does not depend on `h` or `N`. -/
theorem integral_pow_abs_free_energy_sub_le (β h : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    Integrable (fun g : FinPairs N → ℝ => |(N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g σ)) - (N : ℝ)⁻¹ * ∫ g', Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g' σ)) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)|
        ^ k) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
    Real.sqrt N ^ k * ∫ g : FinPairs N → ℝ, |(N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g σ)) - (N : ℝ)⁻¹ * ∫ g', Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g' σ)) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)|
        ^ k ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      2 * Nat.factorial k * Real.exp (β ^ 2 / 2) := by
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  obtain ⟨a, ha, hv⟩ := exists_sk_linear_data N β h
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP
  set F : (FinPairs N → ℝ) → ℝ := fun g => Real.log (∑ σ : Fin N → ℤˣ,
    Real.exp (skGibbsEnergy N β h g σ)) with hF
  have hFe : ∀ g, F g = Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (a σ ⬝ᵥ g + h * ∑ i, ((σ i : ℤ) : ℝ))) := fun g => by
    simp only [hF, ha]
  have hsub : HasSubgaussianMGF (fun g => F g - ∫ g', F g' ∂P)
      (2 * (β ^ 2 * N / 2).toNNReal) P := by
    have := hasSubgaussianMGF_log_sum_exp_tilt a (fun σ => h * ∑ i, ((σ i : ℤ) : ℝ))
      (fun _ => 0) hv 0
    simpa only [hFe, zero_mul, add_zero] using this
  have hF0 : Measurable F := by
    simp only [hF]
    exact Measurable.log (Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_skGibbsEnergy N β h σ))
  have hFm : Measurable fun g => F g - ∫ g', F g' ∂P := hF0.sub_const _
  obtain ⟨hint, hexp⟩ := hsub.integral_exp_abs_mul_le hFm (Real.sqrt N)⁻¹
  -- pointwise comparison with the exponential moment
  have hpt : ∀ g, (Real.sqrt N) ^ k * |(N : ℝ)⁻¹ * F g - (N : ℝ)⁻¹ * ∫ g', F g' ∂P| ^ k ≤
      Nat.factorial k * Real.exp ((Real.sqrt N)⁻¹ * |F g - ∫ g', F g' ∂P|) := fun g => by
    have hN' : (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hN0.le]
    have e : (Real.sqrt N) * |(N : ℝ)⁻¹ * F g - (N : ℝ)⁻¹ * ∫ g', F g' ∂P| =
        (Real.sqrt N)⁻¹ * |F g - ∫ g', F g' ∂P| := by
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hN0), hN']
      field_simp
    rw [← mul_pow, e]
    exact Real.pow_le_factorial_mul_exp (by positivity) k
  have hmeas : Measurable fun g => |(N : ℝ)⁻¹ * F g - (N : ℝ)⁻¹ * ∫ g', F g' ∂P| ^ k :=
    (continuous_abs.measurable.comp ((hF0.const_mul _).sub_const _)).pow_const k
  have hint' : Integrable (fun g => Real.sqrt N ^ k *
      |(N : ℝ)⁻¹ * F g - (N : ℝ)⁻¹ * ∫ g', F g' ∂P| ^ k) P :=
    Integrable.mono' (hint.const_mul (Nat.factorial k : ℝ)) (hmeas.const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt g)
  refine ⟨by simpa [mul_assoc, hs.ne'] using hint'.const_mul ((Real.sqrt N) ^ k)⁻¹, ?_⟩
  rw [← integral_const_mul]
  refine (integral_mono hint' (hint.const_mul (Nat.factorial k : ℝ)) hpt).trans ?_
  rw [integral_const_mul]
  have hc : ((2 * (β ^ 2 * N / 2).toNNReal : ℝ≥0) : ℝ) * ((Real.sqrt N)⁻¹) ^ 2 / 2 =
      β ^ 2 / 2 := by
    push_cast
    rw [Real.coe_toNNReal _ (by positivity), inv_pow, Real.sq_sqrt hN0.le]
    field_simp
  rw [hc] at hexp
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.factorial k)]

end SpinGlasses
