/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Ising

/-!
# Spins supported on two antipodal points

For equal mass on `±r e_u`, the scalar Ising parameter is `β r²`. In particular `r = sqrt d`
gives the `β d` example of Section 1.12. The identities hold at all temperatures. A coordinate
`u : Fin d` ensures `d > 0`, as required to choose a coordinate axis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace SpinGlasses

/-- A single nonzero spin component multiplies the scalar interaction strength by `r²`. -/
theorem skVectorEnergy_single_component (N d : ℕ) (β r : ℝ) (u₀ : Fin d)
    (g : FinPairs N → ℝ) (σ : Fin N → ℝ) :
    skVectorEnergy N β g (fun i u => if u = u₀ then r * σ i else 0) =
      (Real.sqrt N)⁻¹ * (β * r ^ 2) *
        ∑ p : FinPairs N, g p * σ p.val.1 * σ p.val.2 := by
  have hs (i j : Fin N) :
      (∑ u : Fin d, (if u = u₀ then r * σ i else 0) *
        (if u = u₀ then r * σ j else 0)) = r ^ 2 * (σ i * σ j) := by
    simp only [ite_mul, mul_ite, mul_zero, zero_mul]
    simp
    ring
  simp only [skVectorEnergy, hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The Gibbs law on two equally weighted antipodal points is scalar SK at `β r²`. -/
theorem tilted_skVectorEnergy_two_point (N d : ℕ) (β r : ℝ) (u₀ : Fin d)
    (g : FinPairs N → ℝ) :
    (Measure.pi fun _ : Fin N => Measure.count.tilted (fun _ : ℤˣ => (0 : ℝ))).tilted
        (fun σ => skVectorEnergy N β g
          (fun i u => if u = u₀ then r * ((σ i : ℤ) : ℝ) else 0)) =
      Measure.count.tilted (skGibbsEnergy N (β * r ^ 2) 0 g) := by
  rw [tilted_pi_count_tilted]
  congr 1
  funext σ
  simp only [Finset.sum_const_zero, zero_add, skVectorEnergy_single_component,
    skGibbsEnergy, zero_mul, add_zero]

/-- Equal masses at `±r e_u` give the scalar partition function at `β r²`, divided by `2^N`.
The book's two points `±sqrt d e_u` are the specialization `r = sqrt d`. -/
theorem integral_exp_skVectorEnergy_two_point (N d : ℕ) (β r : ℝ) (u₀ : Fin d)
    (g : FinPairs N → ℝ) :
    (∫ σ : Fin N → ℤˣ, Real.exp (skVectorEnergy N β g
      (fun i u => if u = u₀ then r * ((σ i : ℤ) : ℝ) else 0))
      ∂(Measure.pi fun _ : Fin N => Measure.count.tilted (fun _ : ℤˣ => (0 : ℝ)))) =
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N (β * r ^ 2) 0 g σ)) / 2 ^ N := by
  rw [integral_exp_pi_count_tilted_eq_div]
  simp only [Finset.sum_const_zero, zero_add, Real.exp_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.card_univ, Fintype.card_units_int, Fintype.card_fin, Nat.cast_ofNat,
    skVectorEnergy_single_component, skGibbsEnergy, zero_mul, add_zero]

/-- Logarithmic partition identity for the two-point spin law. -/
theorem log_integral_exp_skVectorEnergy_two_point (N d : ℕ) (β r : ℝ) (u₀ : Fin d)
    (g : FinPairs N → ℝ) :
    Real.log (∫ σ : Fin N → ℤˣ, Real.exp (skVectorEnergy N β g
      (fun i u => if u = u₀ then r * ((σ i : ℤ) : ℝ) else 0))
      ∂(Measure.pi fun _ : Fin N => Measure.count.tilted (fun _ : ℤˣ => (0 : ℝ)))) =
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N (β * r ^ 2) 0 g σ)) -
        N * Real.log 2 := by
  rw [integral_exp_skVectorEnergy_two_point,
    Real.log_div (by positivity) (by positivity), Real.log_pow]

/-- The two-point vector pressure is the scalar pressure at `β r²` minus `log 2`. -/
theorem skVectorFreeEnergy_two_point (N d : ℕ) (hN : 0 < N) (β r : ℝ) (u₀ : Fin d) :
    skVectorFreeEnergy (Measure.count.tilted (fun _ : ℤˣ => (0 : ℝ)))
        (fun ε u => if u = u₀ then r * ((ε : ℤ) : ℝ) else 0) N β =
      (N : ℝ)⁻¹ * (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N (β * r ^ 2) 0 g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) - Real.log 2 := by
  have hi : Integrable (fun g : FinPairs N → ℝ =>
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N (β * r ^ 2) 0 g σ)))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    simpa only [skGibbsEnergy] using
      integrable_log_partition_sk N ((Real.sqrt N)⁻¹ * (β * r ^ 2)) 0
  simp only [skVectorFreeEnergy, log_integral_exp_skVectorEnergy_two_point]
  rw [integral_sub hi (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  field_simp

end SpinGlasses
