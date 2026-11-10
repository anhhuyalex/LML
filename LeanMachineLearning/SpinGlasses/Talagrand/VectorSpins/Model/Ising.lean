/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.Basic
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityFreeEnergy
public import LeanMachineLearning.SpinGlasses.Gibbs.GibbsMeasureNested
public import LeanMachineLearning.SpinGlasses.Talagrand.GaussianFluctuation.SKGaussianFluctuation

/-!
# One-component vector spins and the scalar Ising model

Talagrand Section 1.12 uses the probability law proportional to `exp (h ε)` at each site.
The scalar Ising partition function instead sums over signs. The Gibbs laws agree, while
their log partition functions differ by `N log (2 cosh h)`. All comparisons are exact for
every inverse temperature and every fixed disorder. Pressure identities use positive sizes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace SpinGlasses

/-- The one-component interaction plus the one-site field is the scalar Ising energy. -/
theorem sum_field_add_skVectorEnergy_eq_skGibbsEnergy (N : ℕ) (β h : ℝ)
    (g : FinPairs N → ℝ) (σ : Fin N → ℤˣ) :
    (∑ i, h * ((σ i : ℤ) : ℝ)) +
        skVectorEnergy N β g (fun i (_ : Fin 1) => ((σ i : ℤ) : ℝ)) =
      skGibbsEnergy N β h g σ := by
  rw [skVectorEnergy_one_component]
  simp only [skGibbsEnergy, ← Finset.mul_sum]
  ring

/-- Moving the field from the one-site probability law into the energy gives exactly the
scalar Ising Gibbs measure. No temperature restriction or disorder averaging is needed. -/
theorem tilted_skVectorEnergy_eq_ising (N : ℕ) (β h : ℝ) (g : FinPairs N → ℝ) :
    (Measure.pi fun _ : Fin N =>
      Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
        (fun σ => skVectorEnergy N β g (fun i (_ : Fin 1) => ((σ i : ℤ) : ℝ))) =
      Measure.count.tilted (skGibbsEnergy N β h g) := by
  rw [tilted_pi_count_tilted]
  congr 1
  funext σ
  exact sum_field_add_skVectorEnergy_eq_skGibbsEnergy N β h g σ

/-- The vector partition function averages the one-site field law, dividing the scalar
counting partition function by `(2 cosh h)^N`, including at size zero. -/
theorem integral_exp_skVectorEnergy_ising (N : ℕ) (β h : ℝ) (g : FinPairs N → ℝ) :
    (∫ σ : Fin N → ℤˣ,
      Real.exp (skVectorEnergy N β g (fun i (_ : Fin 1) => ((σ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin N =>
        Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ)))) =
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) / (2 * Real.cosh h) ^ N := by
  rw [integral_exp_pi_count_tilted_eq_div]
  simp_rw [sum_field_add_skVectorEnergy_eq_skGibbsEnergy]
  rw [show (∑ ε : ℤˣ, Real.exp (h * ((ε : ℤ) : ℝ))) = 2 * Real.cosh h by
    simpa only [mul_comm h] using sum_units_int_exp_mul h]
  simp only [Fintype.card_fin]

/-- Logarithmic normalization for the one-component Ising instance of the vector model. -/
theorem log_integral_exp_skVectorEnergy_ising (N : ℕ) (β h : ℝ) (g : FinPairs N → ℝ) :
    Real.log (∫ σ : Fin N → ℤˣ,
      Real.exp (skVectorEnergy N β g (fun i (_ : Fin 1) => ((σ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin N =>
        Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ)))) =
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) -
        N * Real.log (2 * Real.cosh h) := by
  rw [integral_exp_skVectorEnergy_ising,
    Real.log_div (by positivity) (by positivity), Real.log_pow]

/-- The probability-law vector pressure equals the counting-law scalar pressure minus
`log (2 cosh h)`. Positivity of `N` is needed when cancelling its normalization. -/
theorem skVectorFreeEnergy_ising (N : ℕ) (hN : 0 < N) (β h : ℝ) :
    skVectorFreeEnergy
        (Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ)))
        (fun ε (_ : Fin 1) => ((ε : ℤ) : ℝ)) N β =
      (N : ℝ)⁻¹ * (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
        Real.log (2 * Real.cosh h) := by
  have hi : Integrable (fun g : FinPairs N → ℝ =>
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    simpa only [skGibbsEnergy] using
      integrable_log_partition_sk N ((Real.sqrt N)⁻¹ * β) h
  simp only [skVectorFreeEnergy, log_integral_exp_skVectorEnergy_ising]
  rw [integral_sub hi (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  field_simp

end SpinGlasses
