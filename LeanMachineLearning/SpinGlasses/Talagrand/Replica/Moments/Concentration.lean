/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.QuadraticBounds
public import LeanMachineLearning.ForMathlib.Probability.Moments.CGFConvex
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.SpinGlasses.Panchenko.Foundations.Concentration
public import LeanMachineLearning.SpinGlasses.Talagrand.DecoupledSystems.SKFirstMoment
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Moments.RealPowers
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Moments.Convexity
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian concentration and quadratic bounds for real moments of the SK model

This file formalizes the sub-Gaussian concentration of the SK partition function `Z_N` and the
resulting quadratic sandwich for the real-moment pressure `ψ_N(t) = N⁻¹ log 𝔼 Z_N^t`
(Talagrand, Section 1.13).

## Mathematical overview

For every `β, h` and `N ≥ 1`, the SK Hamiltonian decomposed over the hypercube has centered
Gaussian disorder with variance `β² (N - 1) / 2` for every configuration `σ`.
By Panchenko's theorem `hasSubgaussianMGF_log_sum_exp`, the centered free energy
`log Z_N - 𝔼 log Z_N` is sub-Gaussian with parameter `β² (N - 1)`.

Combined with Jensen's inequality and the cumulant-generating function representation, this yields
for every real `t`:
```
t * p_N ≤ ψ_N(t) ≤ t * p_N + β² t² / 2
```
where `p_N = N⁻¹ 𝔼 log Z_N`.

As a consequence, if `p_N → p` and `ψ_N(t) → ψ(t)` pointwise on a neighborhood of `0`, then `ψ`
is differentiable at `0` with derivative `ψ'(0) = p`.  This justifies the interchange of limits
`N → ∞` and `t → 0+` a posteriori whenever the real-moment pressure exists near `0`.

## Main declarations

* `SpinGlasses.hasSubgaussianMGF_log_skPartition`: sub-Gaussian concentration of `log Z_N`.
* `SpinGlasses.inv_mul_log_integral_rpow_skPartition_sandwich`: the quadratic sandwich for
  `ψ_N(t)`.
* `SpinGlasses.hasDerivAt_zero_of_tendsto_inv_mul_log_integral_rpow_skPartition`:
  differentiability `ψ'(0) = p` under convergence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal

namespace SpinGlasses

variable {N : ℕ} (β h : ℝ)

/-- The Gaussian part of the SK Hamiltonian has a Gaussian law on `Fin N → ℤˣ`. -/
theorem skGibbsEnergy_gaussian_part_hasGaussianLaw :
    HasGaussianLaw
      (fun (g : FinPairs N → ℝ) (σ : Fin N → ℤˣ) =>
        (Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  simpa only [dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    hasGaussianLaw_dotProduct_family (fun (σ : Fin N → ℤˣ) (p : FinPairs N) =>
      (Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))

/-- The Gaussian part of the SK Hamiltonian is centered for every configuration `σ`. -/
theorem integral_skGibbsEnergy_gaussian_part_eq_zero (σ : Fin N → ℤˣ) :
    ∫ g : FinPairs N → ℝ,
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) = 0 := by
  simpa only [dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    integral_dotProduct_pi_gaussianReal (fun p : FinPairs N =>
      (Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))

/-- The second moment of the Gaussian part of the SK Hamiltonian equals `β² * (N - 1) / 2`: there
are `N (N - 1) / 2` pairs, each with squared coefficient `β² / N`. -/
theorem integral_skGibbsEnergy_gaussian_part_sq (hN : 0 < N) (σ : Fin N → ℤˣ) :
    ∫ g : FinPairs N → ℝ,
      ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))) ^ 2
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      β ^ 2 * ((N : ℝ) - 1) / 2 := by
  let a : FinPairs N → ℝ := fun p =>
    (Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)
  have hsecond : (∫ g : FinPairs N → ℝ,
      ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))) ^ 2
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = ∑ p, a p ^ 2 := by
    simpa only [a, dotProduct, sq, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      integral_dotProduct_mul_dotProduct_pi_gaussianReal a a
  rw [hsecond]
  have hsum := sum_sk_first_moment_term_sq hN β σ
  change (∑ p : FinPairs N, a p ^ 2 / 2) = _ at hsum
  rw [← Finset.sum_div] at hsum
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hcancel : (N : ℝ) * (β ^ 2 / 4 * (1 - (N : ℝ)⁻¹)) =
      β ^ 2 * ((N : ℝ) - 1) / 4 := by field_simp
  rw [hcancel] at hsum
  linarith

/-- The centered logarithm of the SK partition function has sub-Gaussian MGF with parameter
`2 * v.toNNReal = β² * (N - 1)`. -/
theorem hasSubgaussianMGF_log_skPartition (hN : 0 < N) :
    HasSubgaussianMGF
      (fun g : FinPairs N → ℝ =>
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) -
          ∫ g' : FinPairs N → ℝ,
            Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ))
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
      (2 * (β ^ 2 * ((N : ℝ) - 1) / 2).toNNReal)
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  have hg := skGibbsEnergy_gaussian_part_hasGaussianLaw (N := N) β
  have hm (σ : Fin N → ℤˣ) :
      Measurable (fun (g : FinPairs N → ℝ) =>
        (Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))) := by
    refine measurable_const.mul ?_
    exact Finset.measurable_sum _ fun p _ =>
      ((measurable_pi_apply p).mul_const _).mul_const _
  have h0 (σ : Fin N → ℤˣ) := integral_skGibbsEnergy_gaussian_part_eq_zero (N := N) β σ
  have hv (σ : Fin N → ℤˣ) :
      ∫ g : FinPairs N → ℝ,
        ((Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))) ^ 2
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
        β ^ 2 * ((N : ℝ) - 1) / 2 :=
    le_of_eq (integral_skGibbsEnergy_gaussian_part_sq (N := N) β hN σ)
  let h_bias : (Fin N → ℤˣ) → ℝ := fun σ => h * ∑ i, ((σ i : ℤ) : ℝ)
  have hcore := hasSubgaussianMGF_log_sum_exp
    (hg := hg) (hm := hm) (h0 := h0) (v := β ^ 2 * ((N : ℝ) - 1) / 2) (hv := hv) (h := h_bias)
  have heq (g : FinPairs N → ℝ) (σ : Fin N → ℤˣ) :
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + h_bias σ =
      skGibbsEnergy N β h g σ := (skGibbsEnergy_def N β h g σ).symm
  simp_rw [heq] at hcore
  exact hcore

/-- **Talagrand Section 1.13, quadratic sandwich for the real-moment pressure:**
for every `t : ℝ`, `N ≥ 1`, and every `β, h`:
`t * p_N ≤ ψ_N(t) ≤ t * p_N + β² t² / 2`,
where `p_N = N⁻¹ 𝔼 log Z_N` and `ψ_N(t) = N⁻¹ log 𝔼 Z_N^t`. -/
theorem inv_mul_log_integral_rpow_skPartition_sandwich (hN : 0 < N) (t : ℝ) :
    t * ((N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ≤
      (N : ℝ)⁻¹ * Real.log (∫ g : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ∧
    (N : ℝ)⁻¹ * Real.log (∫ g : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ≤
      t * ((N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) +
        β ^ 2 * t ^ 2 / 2 := by
  set P := (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  set X := fun g : FinPairs N → ℝ =>
    Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
  have hsub := hasSubgaussianMGF_log_skPartition (N := N) β h hN
  have h_sand := cgf_sandwich_of_hasSubgaussianMGF (X := X) (μ := P) hsub t
  have h_rpow : ∫ g : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t ∂P =
      mgf X P t := by
    exact integral_rpow_eq_mgf_log (Filter.Eventually.of_forall (skPartition_pos N β h)) t
  simp only [cgf, ← h_rpow] at h_sand
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.2 hN
  have hN_inv_nonneg : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN_pos.le
  have hv_nonneg : 0 ≤ β ^ 2 * ((N : ℝ) - 1) / 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.2 hN
    positivity
  have hc_eq : ((2 * (β ^ 2 * ((N : ℝ) - 1) / 2).toNNReal : ℝ≥0) : ℝ) =
      β ^ 2 * ((N : ℝ) - 1) := by
    push_cast
    rw [Real.coe_toNNReal _ hv_nonneg]
    ring
  constructor
  · calc t * ((N : ℝ)⁻¹ * ∫ g, X g ∂P) = (N : ℝ)⁻¹ * (t * ∫ g, X g ∂P) := by ring
      _ ≤ (N : ℝ)⁻¹ * Real.log (∫ g, (∑ σ, Real.exp (skGibbsEnergy N β h g σ)) ^ t ∂P) :=
        mul_le_mul_of_nonneg_left h_sand.1 hN_inv_nonneg
  · refine (mul_le_mul_of_nonneg_left h_sand.2 hN_inv_nonneg).trans ?_
    rw [mul_add, ← mul_assoc, hc_eq]
    have h_le : (N : ℝ)⁻¹ * (β ^ 2 * ((N : ℝ) - 1) * t ^ 2 / 2) ≤ β ^ 2 * t ^ 2 / 2 := by
      have : (N : ℝ)⁻¹ * (β ^ 2 * ((N : ℝ) - 1) * t ^ 2 / 2) =
          (((N : ℝ) - 1) / (N : ℝ)) * (β ^ 2 * t ^ 2 / 2) := by ring
      rw [this]
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [div_le_iff₀ hN_pos]
      linarith
    linarith

/-- **Differentiability of the limiting pressure at zero (Talagrand Section 1.13):**
if the quenched free energy converges `N⁻¹ 𝔼 log Z_N → p` and the real-moment pressure
`N⁻¹ log 𝔼 Z_N^t` converges pointwise to `ψ(t)` on a neighborhood of `0`, then `ψ` is
differentiable at `0` with derivative `ψ'(0) = p`.  Both convergence assumptions are hypotheses:
the theorem proves neither, nor a formula for `ψ(t)`. -/
theorem hasDerivAt_zero_of_tendsto_inv_mul_log_integral_rpow_skPartition
    {p : ℝ} {ψ : ℝ → ℝ}
    (ha : Tendsto
      (fun (N : ℕ) => (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
      atTop (𝓝 p))
    (hψ : ∀ᶠ t in 𝓝 0, Tendsto
      (fun (N : ℕ) => (N : ℝ)⁻¹ * Real.log (∫ g : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)))
      atTop (𝓝 (ψ t))) :
    HasDerivAt ψ p 0 := by
  refine hasDerivAt_zero_of_tendsto_quadratic_bounds (C := β ^ 2 / 2) ha hψ
    (Eventually.of_forall fun t => ?_)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [div_mul_eq_mul_div] using
    inv_mul_log_integral_rpow_skPartition_sandwich (N := N) β h hN t

end SpinGlasses
