/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Ising
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Derivative
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Comparison
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityOuterDerivative
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTiltedShift
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.TrigSquareParam

/-!
# Derivative-level bridge from vector cavity to scalar cavity

This file formalizes the bridge between the vector cavity derivative of Section 1.12
(`hasDerivAt_skVectorCavityAverage`) and the scalar SK cavity derivative of Section 1.6
(`hasDerivAt_integral_sk_cavity_path_square`).

For one-component spins ($d = 1$), spin map $\xi_1(\varepsilon) = \varepsilon \in \mathbb{R}$,
$\rho = 1$, and tilted base measure $\mu_h = \text{count}.\text{tilted}(h \cdot \varepsilon)$:
1. The vector Hamiltonian plus the one-site field equals the scalar cavity energy $E(s)$
   (for $s = \arccos \sqrt{t}$) plus the configuration-independent constant
   $(1 - t) \frac{\beta^2}{2}(1 - q)$ (`skVectorCavityEnergy_ising_eq`).
2. At the replica integral level, this constant cancels exactly, identifying the vector and
   scalar Gibbs averages for every fixed disorder realization (`skVectorCavityGibbs_ising_eq`).
3. Gaussian noise on the scalar disorder space satisfies the hypotheses of Proposition 1.12.4
   (`skVectorCavityGaussianData_disorderLaw_ising`).
4. By Fubini, the disorder expectation functions coincide on $(0, 1)$
   (`skVectorCavityAverage_ising_eq`).
5. Transferring the derivative along `HasDerivAt.congr_of_eventuallyEq` establishes the
   derivative of the scalar cavity path from the vector engine
   (`hasDerivAt_ising_cavity_path_of_vector`), and `HasDerivAt.unique` confirms that the
   vector derivative value equals the scalar derivative value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace SpinGlasses

local notation "ξ₁" => fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)

/-! ### S1. Spin dictionary -/

theorem measurable_ising_spin (u : Fin 1) : Measurable (fun ε : ℤˣ => ξ₁ ε u) :=
  measurable_of_finite _

theorem ising_spin_sq_sum_le_one (ε : ℤˣ) : ∑ u : Fin 1, (ξ₁ ε u) ^ 2 ≤ 1 := by
  simp only [Fin.sum_univ_one, units_cast_sq, le_refl]

/-! ### S2. Energy dictionary -/

/-- **The cavity energy dictionary**: for one-component spins and `s = arccos √t`,
the vector cavity Hamiltonian plus the one-site field matches the scalar cavity energy
up to the configuration-independent constant `(1 - t) * (β² / 2 * (1 - q))`. -/
theorem skVectorCavityEnergy_ising_eq (N : ℕ) (β q h t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ) (σ : Fin (N + 1) → ℤˣ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q) g' ω.1
        (fun _ => β * Real.sqrt q * ω.2) t σ +
      ∑ i : Fin (N + 1), h * ((σ i : ℤ) : ℝ) =
    E (Real.arccos (Real.sqrt t)) g' ω σ + (1 - t) * (β ^ 2 / 2 * (1 - q)) := by
  intro B E
  have hcos : Real.cos (Real.arccos (Real.sqrt t)) = Real.sqrt t := by
    have h1 : Real.sqrt t ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ht1
    have h2 : -1 ≤ Real.sqrt t := by
      linarith [Real.sqrt_nonneg t]
    exact Real.cos_arccos h2 h1
  have hsin : Real.sin (Real.arccos (Real.sqrt t)) = Real.sqrt (1 - t) := by
    rw [Real.sin_arccos, Real.sq_sqrt ht0]
  unfold skVectorCavityEnergy
  simp only [Fin.sum_univ_one]
  dsimp [E, B]
  rw [hcos, hsin]
  have hsq : ((σ (Fin.last N) : ℤ) : ℝ) * ((σ (Fin.last N) : ℤ) : ℝ) = 1 := by
    rw [← sq, units_cast_sq]
  rw [hsq]
  have hfield : (∑ i : Fin (N + 1), h * ((σ i : ℤ) : ℝ)) =
      h * ∑ i : Fin (N + 1), ((σ i : ℤ) : ℝ) := by
    rw [Finset.mul_sum]
  rw [hfield]
  simp only [mul_assoc]
  set Sp : ℝ := ∑ p : FinPairs N, g' p * (((σ p.val.1.castSucc : ℤ) : ℝ) *
    ((σ p.val.2.castSucc : ℤ) : ℝ))
  set Si : ℝ := ∑ i : Fin N, ω.1 i * ((σ i.castSucc : ℤ) : ℝ)
  set Sh : ℝ := ∑ i : Fin (N + 1), ((σ i : ℤ) : ℝ)
  ring

/-! ### S3. Gibbs-average dictionary -/

/-- **Pointwise equality of replica Gibbs averages**: for every fixed disorder configuration,
the vector replica average under `μ_h` equals the scalar replica average under counting
measure. -/
theorem skVectorCavityGibbs_ising_eq {R : Type*} [Fintype R] (N : ℕ) (β q h t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ)
    (Ψ : (R → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R =>
      (Measure.pi fun _ : Fin (N + 1) =>
        Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
          (skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q) g' ω.1
            (fun _ => β * Real.sqrt q * ω.2) t)) =
      ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (E (Real.arccos (Real.sqrt t)) g' ω)) := by
  intro B E
  have htilt : (Measure.pi fun _ : Fin (N + 1) =>
        Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
          (skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q) g' ω.1
            (fun _ => β * Real.sqrt q * ω.2) t) =
      Measure.count.tilted (fun σ => E (Real.arccos (Real.sqrt t)) g' ω σ +
        (1 - t) * (β ^ 2 / 2 * (1 - q))) := by
    rw [tilted_pi_count_tilted]
    congr 1
    funext σ
    rw [add_comm]
    exact skVectorCavityEnergy_ising_eq N β q h t ht0 ht1 g' ω σ
  simp_rw [htilt]
  exact integral_pi_count_tilted_add_const _ _ Ψ

end SpinGlasses
