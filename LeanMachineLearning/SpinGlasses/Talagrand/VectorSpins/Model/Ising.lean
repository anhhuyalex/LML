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
    obtain (h | h) := Int.units_eq_one_or (σ i.castSucc) <;> simp [h]
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
  obtain (h | h) := Int.units_eq_one_or (σ (Fin.last N)) <;> simp [h]

/-- Symmetry of the one-component cavity overlap. -/
theorem skVectorCavityOverlap_ising_symm (N : ℕ) (σ τ : Fin (N + 1) → ℤˣ) :
    skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N σ τ 0 0 =
      skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N τ σ 0 0 := by
  simp only [skVectorCavityOverlap]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The scalar cavity kernel for one-component Ising spins. -/
noncomputable def skIsingCavityKernel (N : ℕ) (β q : ℝ) (a b : Fin (N + 1) → ℤˣ) : ℝ :=
  β ^ 2 * ((a (Fin.last N) : ℤ) : ℝ) * ((b (Fin.last N) : ℤ) : ℝ) *
    (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N a b 0 0 - q)

/-- The scalar cavity kernel is symmetric. -/
theorem skIsingCavityKernel_comm (N : ℕ) (β q : ℝ) (a b : Fin (N + 1) → ℤˣ) :
    skIsingCavityKernel N β q a b = skIsingCavityKernel N β q b a := by
  simp only [skIsingCavityKernel, skVectorCavityOverlap_ising_symm N a b]
  ring

/-- The scalar cavity kernel matches the SK cavity kernel of Section 1.4. -/
theorem skIsingCavityKernel_eq_skCavityKernel (N : ℕ) (β q : ℝ) (a b : Fin (N + 1) → ℤˣ) :
    skIsingCavityKernel N β q a b =
      β ^ 2 * ((a (Fin.last N) : ℤ) : ℝ) * ((b (Fin.last N) : ℤ) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => ((a i.castSucc : ℤ) : ℝ)) ⬝ᵥ
           fun i : Fin N => ((b i.castSucc : ℤ) : ℝ)) - q) := by
  simp only [skIsingCavityKernel, skVectorCavityOverlap, dotProduct]

/-- The RHS of Proposition 1.12.4 specialized to `d = 1` Ising spins. -/
noncomputable def skVectorCavityIsingRHS (N : ℕ) (β q : ℝ) (R : Type*) [Fintype R] [DecidableEq R]
    (F : (R → Fin (N + 1) → ℤˣ) → ℝ) (σ : Option (Option R) → Fin (N + 1) → ℤˣ) : ℝ :=
  (β ^ 2 / 2 * ∑ a : R, ∑ b : R,
      F (fun c => σ (some (some c))) *
        ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some (some a))) (σ (some (some b))) 0 0 -
          if a = b then 1 else q)) -
    (Fintype.card R : ℝ) * β ^ 2 * ∑ a : R,
      F (fun c => σ (some (some c))) *
        ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some (some a))) (σ (some none)) 0 0 - q) -
    (Fintype.card R : ℝ) * (β ^ 2 / 2) *
      (F (fun c => σ (some (some c))) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some none)) (σ (some none)) 0 0 - 1)) +
    (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * β ^ 2 *
      (F (fun c => σ (some (some c))) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        ((σ none (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some none)) (σ none) 0 0 - q))

/-- The scalar cavity combination of three replica families (Eq. (1.151) / (1.152)). -/
noncomputable def skScalarCavityCombination (N : ℕ) (β q : ℝ) (R : Type*)
    [Fintype R] [LinearOrder R] (F : (R → Fin (N + 1) → ℤˣ) → ℝ)
    (σ : Option (Option R) → Fin (N + 1) → ℤˣ) : ℝ :=
  F (fun c => σ (some (some c))) *
    ((∑ p : R × R with p.1 < p.2,
        skIsingCavityKernel N β q (σ (some (some p.1))) (σ (some (some p.2)))) -
      (Fintype.card R : ℝ) * ∑ a : R,
        skIsingCavityKernel N β q (σ (some (some a))) (σ (some none)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 *
        skIsingCavityKernel N β q (σ (some none)) (σ none))

/-- **Reduction of the vector cavity derivative to the scalar cavity formula.**
For one-component Ising spins, the diagonal terms `a = b` in the first sum of (1.376)
cancel exactly against the third sum, and the off-diagonal terms double to the strictly
ordered pairs, yielding the three-family replica combination of Eq. (1.151) / (1.152). -/
theorem skVectorCavityIsingRHS_eq_skScalarCavityCombination
    (N : ℕ) (β q : ℝ) (R : Type*) [Fintype R] [LinearOrder R]
    (F : (R → Fin (N + 1) → ℤˣ) → ℝ)
    (σ : Option (Option R) → Fin (N + 1) → ℤˣ) :
    skVectorCavityIsingRHS N β q R F σ =
      skScalarCavityCombination N β q R F σ := by
  set F0 := F (fun c => σ (some (some c)))
  set u : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ :=
    fun x y => ((x (Fin.last N) : ℤ) : ℝ) * ((y (Fin.last N) : ℤ) : ℝ) *
      (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N x y 0 0 - q)
  have hu_symm : ∀ x y, u x y = u y x := fun x y => by
    dsimp [u]
    rw [skVectorCavityOverlap_ising_symm N x y]
    ring
  have hdiag_val : ∀ x, ((x (Fin.last N) : ℤ) : ℝ) * ((x (Fin.last N) : ℤ) : ℝ) *
      (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N x x 0 0 - 1) =
      - ((N : ℝ) + 1)⁻¹ := fun x => by
    have h1 := ising_last_spin_sq N x
    have h2 := skVectorCavityOverlap_ising_sub_one N x
    calc ((x (Fin.last N) : ℤ) : ℝ) * ((x (Fin.last N) : ℤ) : ℝ) *
          (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N x x 0 0 - 1)
        = 1 * (- ((N : ℝ) + 1)⁻¹) := by rw [h1, h2]
      _ = - ((N : ℝ) + 1)⁻¹ := one_mul _
  have hsplit (a : R) : ∑ b : R,
      ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
      ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
      (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
        (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
      - ((N : ℝ) + 1)⁻¹ +
      ∑ b : R, if a = b then 0 else u (σ (some (some a))) (σ (some (some b))) := by
    have hh (b : R) :
        ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
        (if a = b then - ((N : ℝ) + 1)⁻¹ else 0) +
        (if a = b then 0 else u (σ (some (some a))) (σ (some (some b)))) := by
      split_ifs with hab
      · subst hab
        simp only [add_zero]
        exact hdiag_val (σ (some (some a)))
      · simp only [zero_add, u]
    rw [Finset.sum_congr rfl fun b _ => hh b, Finset.sum_add_distrib]
    simp only [sum_ite_eq, mem_univ, ite_true]
  have hsum_split : ∑ a : R, ∑ b : R,
      F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
      F0 * ((Fintype.card R : ℝ) * (- ((N : ℝ) + 1)⁻¹)) +
      F0 * (2 * ∑ p : R × R with p.1 < p.2,
        u (σ (some (some p.1))) (σ (some (some p.2)))) := by
    have h1 : ∀ a : R, ∑ b : R,
        F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
          (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
            (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
        F0 * (- ((N : ℝ) + 1)⁻¹ +
          ∑ b : R, if a = b then 0 else u (σ (some (some a))) (σ (some (some b)))) := by
      intro a
      have h2 : ∀ b : R,
          F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
            ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
            (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
              (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q) =
          F0 * (((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
            ((σ (some (some b)) (Fin.last N) : ℤ) : ℝ) *
            (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
              (σ (some (some a))) (σ (some (some b))) 0 0 - if a = b then 1 else q)) :=
        fun b => by ring
      simp_rw [h2, ← Finset.mul_sum, hsplit a]
    simp_rw [h1, ← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    rw [sum_sum_offDiag_eq_two_sum_lt (fun a b => u (σ (some (some a))) (σ (some (some b))))
      fun a b => hu_symm (σ (some (some a))) (σ (some (some b))), mul_add]
  have h2_term : (∑ a : R,
      F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
        ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some (some a))) (σ (some none)) 0 0 - q)) =
      F0 * ∑ a : R, u (σ (some (some a))) (σ (some none)) := by
    have h : ∀ a : R,
        F0 * ((σ (some (some a)) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
            (σ (some (some a))) (σ (some none)) 0 0 - q) =
        F0 * u (σ (some (some a))) (σ (some none)) := fun a => by
      dsimp [u]; ring
    simp_rw [h, ← Finset.mul_sum]
  have h3 : F0 * ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
      ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
      (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
        (σ (some none)) (σ (some none)) 0 0 - 1) =
      F0 * (- ((N : ℝ) + 1)⁻¹) := by
    calc F0 * ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
          (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
            (σ (some none)) (σ (some none)) 0 0 - 1)
        = F0 * (((σ (some none) (Fin.last N) : ℤ) : ℝ) *
            ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
            (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
              (σ (some none)) (σ (some none)) 0 0 - 1)) := by ring
      _ = F0 * (- ((N : ℝ) + 1)⁻¹) := by rw [hdiag_val]
  have h4_term :
      F0 * ((σ (some none) (Fin.last N) : ℤ) : ℝ) *
        ((σ none (Fin.last N) : ℤ) : ℝ) *
        (skVectorCavityOverlap (fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)) N
          (σ (some none)) (σ none) 0 0 - q) =
      F0 * u (σ (some none)) (σ none) := by
    dsimp [u]; ring
  have hker : ∀ x y, skIsingCavityKernel N β q x y = β ^ 2 * u x y := fun x y => by
    dsimp [skIsingCavityKernel, u]; ring
  dsimp [skVectorCavityIsingRHS, skScalarCavityCombination]
  simp_rw [hker]
  rw [hsum_split, h2_term, h3, h4_term]
  simp_rw [← Finset.mul_sum]
  ring

end SpinGlasses
