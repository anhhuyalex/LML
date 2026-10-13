/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Order.Interval.Finset.Defs
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianMatrix

/-!
# The Sherrington-Kirkpatrick Hamiltonian: covariance and Dean's comfort function

The Hamiltonian of the Sherrington-Kirkpatrick (SK) model [Panchenko, 2013, Eq. (1.1)] with
disorder `G ~ 𝒩(0,1)^{ι×ι}` is
`H_N(σ) = (√N)⁻¹ ∑_{i,j} g_{ij} σ_i σ_j = (√N)⁻¹ * (σ ⬝ᵥ (G *ᵥ σ))`, `N = Fintype.card ι`.

No definition is introduced: the Hamiltonian is the explicit expression above, the disorder is the
function `G : ι → ι → ℝ` read as a matrix by `Matrix.of G` with the law
`Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1`, exactly as for the Gaussian matrix
lemmas of `ForMathlib/Probability/Moments/GaussianMatrix.lean`, and the overlap is
`(Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)` (`SpinGlasses/Basic.lean`).

## Main declarations

* `SpinGlasses.integral_skHamiltonian_mul_skHamiltonian`: the covariance structure
  `E[H_N(σ) H_N(τ)] = N R(σ, τ)²` ([Panchenko, 2013, Eq. (1.3)]), for arbitrary real vectors `σ`,
  `τ`.  It follows from the general bilinear covariance
  `integral_gaussianMatrix_bilinear_mul_bilinear`
  (`E[(u ⬝ᵥ G v)(x ⬝ᵥ G y)] = (u ⬝ᵥ x)(v ⬝ᵥ y)`), which is also what gives the covariance of
  bipartite or `p`-tensor variants of the model.
* `SpinGlasses.sum_lt_mul_units_eq_sub`: Dean's problem [Panchenko, 2013, §1.1]: the comfort
  `∑_{i<j} g_{ij} σ_i σ_j` of a configuration is the total weight of the pairs on which `σ` agrees
  minus that of the pairs on which it disagrees.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace SpinGlasses

variable {ι : Type*} [Fintype ι]

/-- **Covariance of the SK Hamiltonian** ([Panchenko, 2013, Eq. (1.3)]). For the Hamiltonian
`H_N(σ) = (√N)⁻¹ * (σ ⬝ᵥ (G *ᵥ σ))` with standard Gaussian disorder `G`,
`E[H_N(σ) H_N(τ)] = N * R(σ, τ)²` with the overlap `R(σ, τ) = N⁻¹ * (σ ⬝ᵥ τ)`.  The statement is
for arbitrary real vectors, so it covers the hypercube and its relaxations alike. -/
theorem integral_skHamiltonian_mul_skHamiltonian [Nonempty ι] (σ τ : ι → ℝ) :
    ∫ G : ι → ι → ℝ, ((Real.sqrt (Fintype.card ι))⁻¹ * (σ ⬝ᵥ (Matrix.of G *ᵥ σ))) *
        ((Real.sqrt (Fintype.card ι))⁻¹ * (τ ⬝ᵥ (Matrix.of G *ᵥ τ)))
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1) =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ 2 := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc : (Real.sqrt (Fintype.card ι))⁻¹ * (Real.sqrt (Fintype.card ι))⁻¹ =
      (Fintype.card ι : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp_rw [mul_mul_mul_comm, hc]
  rw [integral_const_mul, integral_gaussianMatrix_bilinear_mul_bilinear]
  field_simp

/-- **Dean's comfort function** ([Panchenko, 2013, §1.1]): for a configuration `σ : ι → ℤˣ` and
couplings `g`, `∑_{i<j} g_{ij} σ_i σ_j = ∑_{i<j, σ_i = σ_j} g_{ij} - ∑_{i<j, σ_i ≠ σ_j} g_{ij}`,
since `σ_i σ_j = 1` if `σ_i = σ_j` and `-1` otherwise. -/
theorem sum_lt_mul_units_eq_sub [LinearOrder ι] (g : ι → ι → ℝ) (σ : ι → ℤˣ) :
    ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), g i j * ((σ i : ℤ) : ℝ) * ((σ j : ℤ) : ℝ) =
      (∑ i, ∑ j ∈ Finset.univ.filter fun j => i < j ∧ σ i = σ j, g i j) -
        ∑ i, ∑ j ∈ Finset.univ.filter fun j => i < j ∧ σ i ≠ σ j, g i j := by
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases Int.units_eq_one_or (σ i) with hi | hi <;>
    rcases Int.units_eq_one_or (σ j) with hj | hj <;> by_cases h : i < j <;> simp [hi, hj, h]

end SpinGlasses
