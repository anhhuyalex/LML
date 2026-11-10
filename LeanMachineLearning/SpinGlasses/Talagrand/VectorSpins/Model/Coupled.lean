/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Ising
public import LeanMachineLearning.SpinGlasses.Talagrand.BeyondATLine.SKCoupledFreeEnergy
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.Deviation

/-!
# Two-component vector spins and two coupled Ising copies

The one-site law is proportional to `exp (h (ε₁ + ε₂) + λ ε₁ ε₂)` on pairs of signs.
The vector-spin partition integral is the existing coupled partition function divided by
one one-site normalizing sum per site. Both Ising copies use the same disorder.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace SpinGlasses

/-- The vector interaction and one-site pair energy give the two-copy scalar energy. -/
theorem sum_field_add_skVectorEnergy_eq_coupled (N : ℕ) (β h lam : ℝ)
    (g : FinPairs N → ℝ) (σ : Fin N → ℤˣ × ℤˣ) :
    (∑ i : Fin N, (h * ((((σ i).1 : ℤ) : ℝ) + (((σ i).2 : ℤ) : ℝ)) +
      lam * (((σ i).1 : ℤ) : ℝ) * (((σ i).2 : ℤ) : ℝ))) +
        skVectorEnergy N β g (fun i => ![(((σ i).1 : ℤ) : ℝ), (((σ i).2 : ℤ) : ℝ)]) =
      skGibbsEnergy N β h g (fun i => (σ i).1) +
        skGibbsEnergy N β h g (fun i => (σ i).2) +
          lam * ∑ i, (((σ i).1 : ℤ) : ℝ) * (((σ i).2 : ℤ) : ℝ) := by
  simp only [skVectorEnergy, skGibbsEnergy, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Reindexing site pairs as a pair of configurations identifies the counting sum. -/
theorem sum_exp_skVectorEnergy_coupled (N : ℕ) (β h lam : ℝ)
    (g : FinPairs N → ℝ) :
    (∑ σ : Fin N → ℤˣ × ℤˣ, Real.exp ((∑ i : Fin N,
      (h * ((((σ i).1 : ℤ) : ℝ) + (((σ i).2 : ℤ) : ℝ)) +
        lam * (((σ i).1 : ℤ) : ℝ) * (((σ i).2 : ℤ) : ℝ))) +
      skVectorEnergy N β g (fun i => ![(((σ i).1 : ℤ) : ℝ), (((σ i).2 : ℤ) : ℝ)]))) =
      skCoupledPartition N β h lam g := by
  simp_rw [sum_field_add_skVectorEnergy_eq_coupled]
  let e := Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => ℤˣ) (fun _ => ℤˣ)
  have hs := e.sum_comp (fun p => Real.exp (skGibbsEnergy N β h g p.1 +
    skGibbsEnergy N β h g p.2 + lam * ∑ i, ((p.1 i : ℤ) : ℝ) * ((p.2 i : ℤ) : ℝ)))
  simpa only [e, Equiv.arrowProdEquivProdArrow_apply, Fintype.sum_prod_type,
    skCoupledPartition] using hs

/-- The vector-spin Gibbs average agrees with the coupled Ising Gibbs average for every
observable of the two configurations, under the site-pair reindexing. -/
theorem integral_tilted_skVectorEnergy_coupled (N : ℕ) (β h lam : ℝ)
    (g : FinPairs N → ℝ) (Ψ : (Fin N → ℤˣ) × (Fin N → ℤˣ) → ℝ) :
    (∫ σ : Fin N → ℤˣ × ℤˣ, Ψ (fun i => (σ i).1, fun i => (σ i).2)
      ∂((Measure.pi fun _ : Fin N => Measure.count.tilted
        (fun ε : ℤˣ × ℤˣ => h * (((ε.1 : ℤ) : ℝ) + ((ε.2 : ℤ) : ℝ)) +
          lam * ((ε.1 : ℤ) : ℝ) * ((ε.2 : ℤ) : ℝ))).tilted
        (fun σ => skVectorEnergy N β g
          (fun i => ![(((σ i).1 : ℤ) : ℝ), (((σ i).2 : ℤ) : ℝ)])))) =
      ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ), Ψ p
        ∂(Measure.count.tilted (fun p => skGibbsEnergy N β h g p.1 +
          skGibbsEnergy N β h g p.2 +
            lam * ∑ i, ((p.1 i : ℤ) : ℝ) * ((p.2 i : ℤ) : ℝ))) := by
  rw [tilted_pi_count_tilted]
  simp_rw [sum_field_add_skVectorEnergy_eq_coupled]
  exact (integral_count_tilted_equiv
    (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => ℤˣ) (fun _ => ℤˣ))
    (fun p => skGibbsEnergy N β h g p.1 + skGibbsEnergy N β h g p.2 +
      lam * ∑ i, ((p.1 i : ℤ) : ℝ) * ((p.2 i : ℤ) : ℝ)) Ψ).symm

/-- The two-component partition integral is the coupled counting partition function divided
by the `N`-th power of the one-site normalizing sum. -/
theorem integral_exp_skVectorEnergy_coupled (N : ℕ) (β h lam : ℝ)
    (g : FinPairs N → ℝ) :
    (∫ σ : Fin N → ℤˣ × ℤˣ, Real.exp (skVectorEnergy N β g
      (fun i => ![(((σ i).1 : ℤ) : ℝ), (((σ i).2 : ℤ) : ℝ)]))
      ∂(Measure.pi fun _ : Fin N => Measure.count.tilted
        (fun ε : ℤˣ × ℤˣ => h * (((ε.1 : ℤ) : ℝ) + ((ε.2 : ℤ) : ℝ)) +
          lam * ((ε.1 : ℤ) : ℝ) * ((ε.2 : ℤ) : ℝ)))) =
      skCoupledPartition N β h lam g /
        (∑ ε : ℤˣ × ℤˣ, Real.exp (h * (((ε.1 : ℤ) : ℝ) + ((ε.2 : ℤ) : ℝ)) +
          lam * ((ε.1 : ℤ) : ℝ) * ((ε.2 : ℤ) : ℝ))) ^ N := by
  rw [integral_exp_pi_count_tilted_eq_div, sum_exp_skVectorEnergy_coupled, Fintype.card_fin]

/-- Logarithmic form of the two-copy probability-law normalization. -/
theorem log_integral_exp_skVectorEnergy_coupled (N : ℕ) (β h lam : ℝ)
    (g : FinPairs N → ℝ) :
    Real.log (∫ σ : Fin N → ℤˣ × ℤˣ, Real.exp (skVectorEnergy N β g
      (fun i => ![(((σ i).1 : ℤ) : ℝ), (((σ i).2 : ℤ) : ℝ)]))
      ∂(Measure.pi fun _ : Fin N => Measure.count.tilted
        (fun ε : ℤˣ × ℤˣ => h * (((ε.1 : ℤ) : ℝ) + ((ε.2 : ℤ) : ℝ)) +
          lam * ((ε.1 : ℤ) : ℝ) * ((ε.2 : ℤ) : ℝ)))) =
      Real.log (skCoupledPartition N β h lam g) -
        N * Real.log (∑ ε : ℤˣ × ℤˣ,
          Real.exp (h * (((ε.1 : ℤ) : ℝ) + ((ε.2 : ℤ) : ℝ)) +
            lam * ((ε.1 : ℤ) : ℝ) * ((ε.2 : ℤ) : ℝ))) := by
  rw [log_integral_exp_pi_count_tilted, sum_exp_skVectorEnergy_coupled, Fintype.card_fin]

/-- The two-component vector pressure is twice the scalar pressure plus the coupled
free-energy difference, minus the logarithm of the one-site normalizing sum. -/
theorem skVectorFreeEnergy_coupled (N : ℕ) (hN : 0 < N) (β h lam : ℝ) :
    skVectorFreeEnergy
        (Measure.count.tilted (fun ε : ℤˣ × ℤˣ =>
          h * (((ε.1 : ℤ) : ℝ) + ((ε.2 : ℤ) : ℝ)) +
            lam * ((ε.1 : ℤ) : ℝ) * ((ε.2 : ℤ) : ℝ)))
        (fun ε => ![((ε.1 : ℤ) : ℝ), ((ε.2 : ℤ) : ℝ)]) N β =
      2 * ((N : ℝ)⁻¹ * (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) +
        skCoupledFreeEnergy N β h lam -
          Real.log (∑ ε : ℤˣ × ℤˣ,
            Real.exp (h * (((ε.1 : ℤ) : ℝ) + ((ε.2 : ℤ) : ℝ)) +
              lam * ((ε.1 : ℤ) : ℝ) * ((ε.2 : ℤ) : ℝ))) := by
  simp only [skVectorFreeEnergy, log_integral_exp_skVectorEnergy_coupled]
  rw [integral_sub (integrable_log_skCoupledPartition N β h lam) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, skCoupledFreeEnergy,
    skCoupledPartition_zero_coupling, Real.log_pow, integral_const_mul]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  ring

/-- The normalized coupled log-partition ratio fluctuates little with the disorder
(Talagrand, after Eq. (1.365)). This uses the existing concentration theorem twice;
the two log partitions need not be independent. -/
theorem measureReal_abs_log_skCoupledPartition_ratio_sub_freeEnergy_ge_le (N : ℕ)
    (hN : 0 < N) (β h lam : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).real
      {g | y ≤ |(N : ℝ)⁻¹ * (Real.log (skCoupledPartition N β h lam g) -
        Real.log (skCoupledPartition N β h 0 g)) - skCoupledFreeEnergy N β h lam|} ≤
      4 * Real.exp (-((N : ℝ) * y / 2) ^ 2 / (4 * (2 * β ^ 2 * N))) := by
  let P : Measure (FinPairs N → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let A : (FinPairs N → ℝ) → ℝ := fun g => Real.log (skCoupledPartition N β h lam g)
  let B : (FinPairs N → ℝ) → ℝ := fun g => Real.log (skCoupledPartition N β h 0 g)
  let a : ℝ := ∫ g, A g ∂P
  let b : ℝ := ∫ g, B g ∂P
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hhalf : 0 ≤ (N : ℝ) * y / 2 := by positivity
  have hA := measureReal_abs_sub_integral_log_skCoupledPartition_ge_le N β h lam hhalf
  have hB := measureReal_abs_sub_integral_log_skCoupledPartition_ge_le N β h 0 hhalf
  have hset :
      {g | y ≤ |(N : ℝ)⁻¹ * (A g - B g) - (N : ℝ)⁻¹ * (a - b)|} =
        {g | (N : ℝ) * y ≤ |(A g - a) - (B g - b)|} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hNpos)]
    have heq : (A g - B g) - (a - b) = (A g - a) - (B g - b) := by ring
    rw [heq, inv_mul_eq_div, le_div_iff₀ hNpos]
    simp only [mul_comm]
  have htail := measureReal_abs_sub_ge_le P (fun g => A g - a) (fun g => B g - b)
    ((N : ℝ) * y)
  calc
    _ = P.real {g | (N : ℝ) * y ≤ |(A g - a) - (B g - b)|} := by
      change P.real {g | y ≤ |(N : ℝ)⁻¹ * (A g - B g) -
        (N : ℝ)⁻¹ * (a - b)|} = _
      exact congrArg P.real hset
    _ ≤ P.real {g | (N : ℝ) * y / 2 ≤ |A g - a|} +
        P.real {g | (N : ℝ) * y / 2 ≤ |B g - b|} := htail
    _ ≤ _ := by
      change P.real {g | (N : ℝ) * y / 2 ≤ |A g - a|} ≤ _ at hA
      change P.real {g | (N : ℝ) * y / 2 ≤ |B g - b|} ≤ _ at hB
      linarith

end SpinGlasses
