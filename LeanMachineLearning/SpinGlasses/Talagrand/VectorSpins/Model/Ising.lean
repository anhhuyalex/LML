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
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Derivative
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityOuterDerivative

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

/-- The cavity overlap of a one-component Ising configuration with itself is `N / (N + 1)`. -/
theorem skVectorCavityOverlap_ising_diag (N : ℕ) (σ : Fin (N + 1) → ℤˣ) :
    skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N σ σ 0 0 =
      (N : ℝ) / ((N : ℝ) + 1) := by
  simp only [skVectorCavityOverlap]
  have h1 : ∀ i : Fin N, ((σ i.castSucc : ℤ) : ℝ) * ((σ i.castSucc : ℤ) : ℝ) = 1 := fun i => by
    rw [← sq, units_cast_sq]
  simp_rw [h1, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- The diagonal error `R_{σ,σ}^- - 1` is the constant `- (N + 1)⁻¹`. -/
theorem skVectorCavityOverlap_ising_sub_one (N : ℕ) (σ : Fin (N + 1) → ℤˣ) :
    skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N σ σ 0 0 - 1 =
      - ((N : ℝ) + 1)⁻¹ := by
  rw [skVectorCavityOverlap_ising_diag N σ]
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The last-spin product on the diagonal is 1. -/
theorem ising_last_spin_sq (N : ℕ) (σ : Fin (N + 1) → ℤˣ) :
    ((σ (Fin.last N) : ℤ) : ℝ) * ((σ (Fin.last N) : ℤ) : ℝ) = 1 := by
  rw [← sq, units_cast_sq]

/-- Symmetry of the one-component cavity overlap. -/
theorem skVectorCavityOverlap_ising_symm (N : ℕ) (σ τ : Fin (N + 1) → ℤˣ) :
    skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N σ τ 0 0 =
      skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N τ σ 0 0 := by
  simp only [skVectorCavityOverlap]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

local notation "skOverlap₁" => skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ))

/-- **Reduction of the vector cavity derivative to the scalar cavity formula.**
For one-component Ising spins, the diagonal terms `a = b` in the first sum of (1.376)
cancel exactly against the third sum, and the off-diagonal terms double to the strictly
ordered pairs, yielding the three-family replica combination of Eq. (1.151) / (1.152). -/
theorem ising_cavity_rhs_eq_three_family_sum
    (N : ℕ) (β q : ℝ) (R : Type*) [Fintype R] [LinearOrder R]
    (F : (R → Fin (N + 1) → ℤˣ) → ℝ)
    (σ : Option (Option R) → Fin (N + 1) → ℤˣ) :
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * ((a (Fin.last N) : ℤ) : ℝ) * ((b (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N a b 0 0 - q)
    (β ^ 2 / 2 * ∑ a : R, ∑ b : R,
        F (fun c => σ (some (some c))) *
          ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q)) -
      (Fintype.card R : ℝ) * β ^ 2 * ∑ a : R,
        F (fun c => σ (some (some c))) *
          ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some (some a))) (σ (some none)) 0 0 - q) -
      (Fintype.card R : ℝ) * (β ^ 2 / 2) *
        (F (fun c => σ (some (some c))) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some none)) (σ (some none)) 0 0 - 1)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * β ^ 2 *
        (F (fun c => σ (some (some c))) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          ((σ none (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some none)) (σ none) 0 0 - q)) =
    F (fun c => σ (some (some c))) *
      ((∑ p : R × R with p.1 < p.2, K (σ (some (some p.1))) (σ (some (some p.2)))) -
        (Fintype.card R : ℝ) * ∑ a : R, K (σ (some (some a))) (σ (some none)) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * K (σ (some none)) (σ none)) := by
  intro K
  set F0 := F (fun c => σ (some (some c)))
  set U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ :=
    fun x y => ((x (Fin.last N) : ℤ) : ℝ) * ((y (Fin.last N) : ℤ) : ℝ) * (skOverlap₁ N x y 0 0 - q)
  have hu_symm : ∀ x y, U x y = U y x := fun x y => by
    dsimp [U]
    rw [skVectorCavityOverlap_ising_symm N x y]
    ring
  have hu_diag : ∀ x, U x x = (N : ℝ) / ((N : ℝ) + 1) - q := fun x => by
    dsimp [U]
    rw [ising_last_spin_sq, skVectorCavityOverlap_ising_diag]
    ring
  have h_term1 (a b : R) :
      ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
      U (σ (some (some a))) (σ (some (some b))) - if a = b then 1 - q else 0 := by
    split_ifs with hab
    · subst hab
      dsimp [U]
      rw [ising_last_spin_sq]
      ring
    · dsimp [U]
      ring
  have h_sum1 : ∑ a : R, ∑ b : R,
      ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
      (∑ a : R, ∑ b : R, U (σ (some (some a))) (σ (some (some b)))) -
        (Fintype.card R : ℝ) * (1 - q) := by
    simp_rw [h_term1, sum_sub_distrib]
    congr 1
    simp only [sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
  have h_term3 :
      ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N (σ (some none)) (σ (some none)) 0 0 - 1) =
      U (σ (some none)) (σ (some none)) - (1 - q) := by
    dsimp [U]
    rw [ising_last_spin_sq]
    ring
  have hker : ∀ x y, K x y = β ^ 2 * U x y := fun x y => by
    dsimp [K, U]; ring
  have hcomb := replica_covariance_combination_eq_two_sum_lt U
    ((N : ℝ) / ((N : ℝ) + 1) - q) hu_diag hu_symm σ
  have hF_sum1 : (∑ a : R, ∑ b : R,
      F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q)) =
      F0 * ((∑ a : R, ∑ b : R, U (σ (some (some a))) (σ (some (some b)))) -
        (Fintype.card R : ℝ) * (1 - q)) := by
    have : ∀ a b : R,
        F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
        F0 * (((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q)) :=
      fun a b => by ring
    simp_rw [this, ← Finset.mul_sum, h_sum1]
  have hF_sum2 : (∑ a : R,
      F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N (σ (some (some a))) (σ (some none)) 0 0 - q)) =
      F0 * ∑ a : R, U (σ (some (some a))) (σ (some none)) := by
    have : ∀ a : R,
        F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some (some a))) (σ (some none)) 0 0 - q) =
        F0 * U (σ (some (some a))) (σ (some none)) := fun a => by
      dsimp [U]; ring
    simp_rw [this, ← Finset.mul_sum]
  have hF_term3 :
      F0 * ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N (σ (some none)) (σ (some none)) 0 0 - 1) =
      F0 * (U (σ (some none)) (σ (some none)) - (1 - q)) := by
    calc F0 * ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some none)) (σ (some none)) 0 0 - 1)
        = F0 * (((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          (skOverlap₁ N (σ (some none)) (σ (some none)) 0 0 - 1)) := by ring
      _ = F0 * (U (σ (some none)) (σ (some none)) - (1 - q)) := by rw [h_term3]
  have hF_term4 :
      F0 * ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        ((σ none (Fin.last N) : ℤ) : ℝ) *
        (skOverlap₁ N (σ (some none)) (σ none) 0 0 - q) =
      F0 * U (σ (some none)) (σ none) := by
    dsimp [U]; ring
  simp_rw [hker]
  simp_rw [← Finset.mul_sum]
  rw [hF_sum1, hF_sum2, hF_term3, hF_term4]
  linear_combination (F0 * (β ^ 2 / 2)) * hcomb

end SpinGlasses
