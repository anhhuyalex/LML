/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Ising
public import
  LeanMachineLearning.SpinGlasses.Talagrand.OverlapConcentration.SKAizenmanLebowitzRuelle

/-!
# Uniform hypercube spins are scalar Ising copies with shared disorder

Transposing sites and components factors both the partition function and the Gibbs law.
This is a fixed-disorder identity at every temperature, before any Gaussian integration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped BigOperators Topology

namespace SpinGlasses

/-- Each hypercube component contributes the scalar zero-field Ising energy. -/
theorem skVectorEnergy_hypercube_eq_sum (N d : ℕ) (β : ℝ) (g : FinPairs N → ℝ)
    (σ : Fin N → Fin d → ℤˣ) :
    skVectorEnergy N β g (fun i u => ((σ i u : ℤ) : ℝ)) =
      ∑ u, skGibbsEnergy N β 0 g (fun i => σ i u) := by
  rw [skVectorEnergy_eq_sum_components]
  simp only [skGibbsEnergy, zero_mul, add_zero]
  simp only [Finset.mul_sum]

/-- The counting partition function is a product over components at fixed disorder. -/
theorem sum_exp_skVectorEnergy_hypercube (N d : ℕ) (β : ℝ) (g : FinPairs N → ℝ) :
    (∑ σ : Fin N → Fin d → ℤˣ,
      Real.exp (skVectorEnergy N β g (fun i u => ((σ i u : ℤ) : ℝ)))) =
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β 0 g σ)) ^ d := by
  simp_rw [skVectorEnergy_hypercube_eq_sum, Real.exp_sum]
  let e := Equiv.piComm (fun _ : Fin N => fun _ : Fin d => ℤˣ)
  have hs := e.sum_comp (fun τ => ∏ u, Real.exp (skGibbsEnergy N β 0 g (τ u)))
  change (∑ σ : Fin N → Fin d → ℤˣ,
    (fun τ : Fin d → Fin N → ℤˣ => ∏ u, Real.exp (skGibbsEnergy N β 0 g (τ u)))
      (e σ)) = _
  rw [hs, ← Fintype.prod_sum (fun (_ : Fin d) (σ : Fin N → ℤˣ) =>
    Real.exp (skGibbsEnergy N β 0 g σ))]
  simp

/-- Normalizing the uniform one-site law contributes `2^N` for each component. -/
theorem integral_exp_skVectorEnergy_hypercube (N d : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) :
    (∫ σ : Fin N → Fin d → ℤˣ,
      Real.exp (skVectorEnergy N β g (fun i u => ((σ i u : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin N =>
        Measure.count.tilted (fun _ : Fin d → ℤˣ => (0 : ℝ)))) =
      ((∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β 0 g σ)) / 2 ^ N) ^ d := by
  rw [integral_exp_pi_count_tilted_eq_div]
  simp only [Finset.sum_const_zero, zero_add, Real.exp_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [sum_exp_skVectorEnergy_hypercube, div_pow]
  congr 1
  norm_num
  ring

/-- Given the couplings, hypercube components have the product of the scalar Gibbs laws.
The disorder `g` is the same in every factor. -/
theorem integral_tilted_skVectorEnergy_hypercube (N d : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) (Ψ : (Fin d → Fin N → ℤˣ) → ℝ) :
    (∫ σ : Fin N → Fin d → ℤˣ, Ψ (fun u i => σ i u)
      ∂((Measure.pi fun _ : Fin N =>
        Measure.count.tilted (fun _ : Fin d → ℤˣ => (0 : ℝ))).tilted
        (fun σ => skVectorEnergy N β g (fun i u => ((σ i u : ℤ) : ℝ))))) =
      ∫ τ : Fin d → Fin N → ℤˣ, Ψ τ
        ∂(Measure.pi fun _ : Fin d => Measure.count.tilted (skGibbsEnergy N β 0 g)) := by
  rw [tilted_pi_count_tilted, pi_tilted_eq_tilted_pi, Measure.pi_count]
  simp only [Finset.sum_const_zero, zero_add]
  simp_rw [skVectorEnergy_hypercube_eq_sum]
  exact (integral_count_tilted_equiv
    (Equiv.piComm fun _ : Fin N => fun _ : Fin d => ℤˣ)
    (fun τ => ∑ u, skGibbsEnergy N β 0 g (τ u)) Ψ).symm

/-- Logarithmic form of the hypercube partition identity. -/
theorem log_integral_exp_skVectorEnergy_hypercube (N d : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) :
    Real.log (∫ σ : Fin N → Fin d → ℤˣ,
      Real.exp (skVectorEnergy N β g (fun i u => ((σ i u : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin N =>
        Measure.count.tilted (fun _ : Fin d → ℤˣ => (0 : ℝ)))) =
      d * (Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β 0 g σ)) -
        N * Real.log 2) := by
  rw [integral_exp_skVectorEnergy_hypercube, Real.log_pow,
    Real.log_div (by positivity) (by positivity), Real.log_pow]

/-- The hypercube pressure is `d` times the zero-field scalar pressure, with the probability
normalization `log 2` subtracted in each component. -/
theorem skVectorFreeEnergy_hypercube (N d : ℕ) (hN : 0 < N) (β : ℝ) :
    skVectorFreeEnergy (Measure.count.tilted (fun _ : Fin d → ℤˣ => (0 : ℝ)))
        (fun ε u => ((ε u : ℤ) : ℝ)) N β =
      d * ((N : ℝ)⁻¹ * (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β 0 g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) - Real.log 2) := by
  have hi : Integrable (fun g : FinPairs N → ℝ =>
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β 0 g σ)))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    simpa only [skGibbsEnergy] using
      integrable_log_partition_sk N ((Real.sqrt N)⁻¹ * β) 0
  simp only [skVectorFreeEnergy, log_integral_exp_skVectorEnergy_hypercube,
    integral_const_mul]
  rw [integral_sub hi (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  field_simp

/-- The uniform hypercube model has limit `d β² / 4` throughout the scalar range `β² < 1/4`.
The temperature bound does not shrink with the number of components. -/
theorem tendsto_skVectorFreeEnergy_hypercube (d : ℕ) (β : ℝ) (hβ : β ^ 2 < 1 / 4) :
    Tendsto (fun N : ℕ =>
      skVectorFreeEnergy (Measure.count.tilted (fun _ : Fin d → ℤˣ => (0 : ℝ)))
        (fun ε u => ((ε u : ℤ) : ℝ)) N β) atTop (𝓝 ((d : ℝ) * (β ^ 2 / 4))) := by
  have hs := tendsto_sk_free_energy_of_lt β 0 0 (by simp) hβ
  simp only [Real.sqrt_zero, mul_zero, zero_mul, add_zero, Real.cosh_zero, Real.log_one,
    integral_zero, sub_zero, one_pow, mul_one] at hs
  have ht := (hs.sub_const (Real.log 2)).const_mul (d : ℝ)
  simp only [add_sub_cancel_left] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [skGibbsEnergy, zero_mul, add_zero] using
    (skVectorFreeEnergy_hypercube N d hN β).symm

end SpinGlasses
