/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Panchenko.Foundations.SKModel
public import LeanMachineLearning.SpinGlasses.Talagrand.GaussianFluctuation.SKGaussianFluctuation
public import
  LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKReplicaSymmetricBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTiltedShift

/-!
# The matrix and the pair Hamiltonian of the SK model

Panchenko's Hamiltonian is `H_N(G, σ) = (√N)⁻¹ ∑_{i,j} G_ij σ_i σ_j` with a Gaussian matrix `G`.
Talagrand's is `(√N)⁻¹ β ∑_{i<j} g_ij σ_i σ_j` with pair disorder `g`. The diagonal terms of the
matrix form do not depend on `σ` (`σ_i² = 1`) and the other terms combine to
`(G_ij + G_ji) σ_i σ_j`. This gives the following statement, which makes the two conventions one.

* `SpinGlasses.map_skHamiltonian_eq_pair`: as a process in `σ`, the matrix Hamiltonian has the
  law of `√2 (√N)⁻¹ ∑_{i<j} g_ij σ_i σ_j + Z`, where `Z` is a standard Gaussian that does not
  depend on `σ` or on `g`.
* `SpinGlasses.integral_gibbs_skHamiltonian_eq_pair`: every disorder-averaged replica Gibbs
  average for the matrix Hamiltonian at inverse temperature `β` equals the one for the pair
  Hamiltonian at inverse temperature `√2 β`, with the same field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace SpinGlasses

variable {N : ℕ}

/-- The covariance of the matrix Hamiltonian is the Gram matrix of the pair Hamiltonian at
`β = √2` plus the covariance `1` of the constant `Z`. -/
theorem skPair_gram (hN : 0 < N) (σ τ : Fin N → ℤˣ) :
    (∑ p : FinPairs N, (Real.sqrt 2 * (Real.sqrt N)⁻¹ * (((σ p.val.1 : ℤ) : ℝ) *
        ((σ p.val.2 : ℤ) : ℝ))) * (Real.sqrt 2 * (Real.sqrt N)⁻¹ * (((τ p.val.1 : ℤ) : ℝ) *
        ((τ p.val.2 : ℤ) : ℝ)))) + 1 =
      (N : ℝ) * ((N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx := sum_finPairs_mul_eq_sub_sum_sq_div_two N
    (fun i => ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ))
  have hsq : ∑ i, (((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) ^ 2 = N := by
    simp [mul_pow, units_cast_sq]
  rw [hsq] at hx
  have e : ∀ p : FinPairs N, (Real.sqrt 2 * (Real.sqrt N)⁻¹ * (((σ p.val.1 : ℤ) : ℝ) *
        ((σ p.val.2 : ℤ) : ℝ))) * (Real.sqrt 2 * (Real.sqrt N)⁻¹ * (((τ p.val.1 : ℤ) : ℝ) *
        ((τ p.val.2 : ℤ) : ℝ))) = 2 / N * (((σ p.val.1 : ℤ) : ℝ) * ((τ p.val.1 : ℤ) : ℝ) *
          (((σ p.val.2 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ))) := by
    intro p
    have : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hNpos.le]
    calc _ = (Real.sqrt 2 * Real.sqrt 2) * ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) *
          (((σ p.val.1 : ℤ) : ℝ) * ((τ p.val.1 : ℤ) : ℝ) *
          (((σ p.val.2 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ))) := by ring
      _ = _ := by
        rw [this, Real.mul_self_sqrt (by norm_num)]
        field_simp
  simp_rw [e, ← Finset.mul_sum]
  rw [hx]
  simp only [dotProduct]
  field_simp
  ring

section Law

variable (H : (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ G σ, H G σ = (Real.sqrt (Fintype.card (Fin N)))⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The matrix Hamiltonian is the pair Hamiltonian at `β = √2` plus a constant Gaussian.**
As a process in `σ`, `(√N)⁻¹ ∑_{i,j} G_ij σ_i σ_j` has the law of
`√2 (√N)⁻¹ ∑_{i<j} g_ij σ_i σ_j + Z`, with `g` and `Z` independent standard Gaussians (`Z` is
indexed by `Unit`). Both sides are centered Gaussian processes with covariance `N R(σ, τ)²`. -/
theorem map_skHamiltonian_eq_pair (hN : 0 < N) :
    (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1).map
        (fun G σ => H G σ) =
      ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Unit => gaussianReal 0 1)).map
        (fun q σ => Real.sqrt 2 * (Real.sqrt N)⁻¹ * ∑ p : FinPairs N,
          q.1 p * (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + q.2 ()) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hcard : Fintype.card (Fin N) = N := Fintype.card_fin N
  have hgram := map_eq_map_dotProduct_prod
    (P := Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (X := fun σ G => H G σ)
    (fun (σ : Fin N → ℤˣ) (p : FinPairs N) => Real.sqrt 2 * (Real.sqrt N)⁻¹ *
      (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)))
    (fun (_ : Fin N → ℤˣ) (_ : Unit) => (1 : ℝ))
    (hasGaussianLaw_skHamiltonian H hH) (integral_skHamiltonian_eq_zero H hH)
    (fun σ τ => by
      rw [integral_skHamiltonian_mul_skHamiltonian_units H hH, hcard]
      have := skPair_gram hN σ τ
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, mul_one] at this ⊢
      linarith)
  rw [hgram]
  congr 1
  funext q σ
  simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

end Law

section Gibbs

variable (H : (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ G σ, H G σ = (Real.sqrt (Fintype.card (Fin N)))⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The Gibbs measures of the two conventions agree.** For every observable `Θ` of `n` replicas,
the disorder average of the replica Gibbs average for the matrix Hamiltonian at inverse
temperature `β` and field `h` equals the disorder average for the pair Hamiltonian
(`skGibbsEnergy`) at inverse temperature `√2 β` and the same field. The diagonal Gaussian cancels
in every Gibbs average. -/
theorem integral_gibbs_skHamiltonian_eq_pair (hN : 0 < N) (n : ℕ) (β h : ℝ)
    (Θ : (Fin n → Fin N → ℤˣ) → ℝ) :
    ∫ G : Fin N → Fin N → ℝ, ∫ σ, Θ σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin N → ℤˣ => β * H G a + h * ∑ i, ((a i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1) =
    ∫ g : FinPairs N → ℝ, ∫ σ, Θ σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (skGibbsEnergy N (Real.sqrt 2 * β) h g))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ((Fin N → ℤˣ) → ℝ) → ℝ, Ψ = fun U => ∫ σ, Θ σ ∂(Measure.pi fun _ :
      Fin n => Measure.count.tilted (fun a : Fin N → ℤˣ => β * U a + h * ∑ i, ((a i : ℤ) : ℝ))) :=
    ⟨_, rfl⟩
  have hΨm : Measurable Ψ := by
    rw [hΨ]
    exact measurable_integral_pi_count_tilted (R := Fin n)
      (g := fun (U : (Fin N → ℤˣ) → ℝ) (a : Fin N → ℤˣ) => β * U a + h * ∑ i, ((a i : ℤ) : ℝ))
      (fun a => by fun_prop) (fun σ => measurable_const)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (FinPairs N → ℝ) → ℝ, Φ = fun g => ∫ σ, Θ σ ∂(Measure.pi fun _ :
      Fin n => Measure.count.tilted (skGibbsEnergy N (Real.sqrt 2 * β) h g)) := ⟨_, rfl⟩
  have hΦm : Measurable Φ := by
    rw [hΦ]
    exact measurable_integral_pi_count_tilted (R := Fin n)
      (g := fun (g : FinPairs N → ℝ) (a : Fin N → ℤˣ) => skGibbsEnergy N (Real.sqrt 2 * β) h g a)
      (fun a => measurable_skGibbsEnergy N _ h a) (fun σ => measurable_const)
  have hHm : Measurable fun (G : Fin N → Fin N → ℝ) (σ : Fin N → ℤˣ) => H G σ := by
    refine measurable_pi_iff.2 fun σ => ?_
    simp only [hH, dotProduct, Matrix.mulVec]
    fun_prop
  have hL : ∀ G : Fin N → Fin N → ℝ, ∫ σ, Θ σ ∂(Measure.pi fun _ : Fin n =>
      Measure.count.tilted (fun a : Fin N → ℤˣ => β * H G a + h * ∑ i, ((a i : ℤ) : ℝ))) =
      Ψ (fun a => H G a) := fun G => by rw [hΨ]
  have hR : ∀ g : FinPairs N → ℝ, ∫ σ, Θ σ ∂(Measure.pi fun _ : Fin n =>
      Measure.count.tilted (skGibbsEnergy N (Real.sqrt 2 * β) h g)) = Φ g := fun g => by
    rw [hΦ]
  simp_rw [hL, hR]
  rw [← integral_map hHm.aemeasurable hΨm.aestronglyMeasurable,
    map_skHamiltonian_eq_pair H hH hN]
  have hUm : Measurable fun (q : (FinPairs N → ℝ) × (Unit → ℝ)) (σ : Fin N → ℤˣ) =>
      Real.sqrt 2 * (Real.sqrt N)⁻¹ * ∑ p : FinPairs N,
        q.1 p * (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + q.2 () := by
    refine measurable_pi_iff.2 fun σ => ?_
    fun_prop
  rw [integral_map hUm.aemeasurable hΨm.aestronglyMeasurable]
  have hpt : ∀ q : (FinPairs N → ℝ) × (Unit → ℝ), Ψ (fun σ => Real.sqrt 2 * (Real.sqrt N)⁻¹ *
      ∑ p : FinPairs N, q.1 p * (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + q.2 ()) =
        Φ q.1 := by
    intro q
    rw [hΨ, hΦ]
    beta_reduce
    have : (fun a : Fin N → ℤˣ => β * (Real.sqrt 2 * (Real.sqrt N)⁻¹ *
        ∑ p : FinPairs N, q.1 p * (((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) + q.2 ()) +
          h * ∑ i, ((a i : ℤ) : ℝ)) =
        fun a => skGibbsEnergy N (Real.sqrt 2 * β) h q.1 a + β * q.2 () := by
      funext a
      simp only [skGibbsEnergy]
      have : ∑ p : FinPairs N, q.1 p * (((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) =
          ∑ p : FinPairs N, q.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ) :=
        Finset.sum_congr rfl fun p _ => by ring
      rw [this]
      ring
    rw [this]
    exact integral_pi_count_tilted_add_const _ _ _
  simp_rw [hpt]
  rw [← integral_map measurable_fst.aemeasurable hΦm.aestronglyMeasurable,
    Measure.map_fst_prod]
  simp

end Gibbs

end SpinGlasses
