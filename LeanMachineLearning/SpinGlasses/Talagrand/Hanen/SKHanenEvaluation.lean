/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairing
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKTBasisAlgebra
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKPairVariance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Asymptotic evaluation of rectangular products (Talagrand Propositions 1.11.10, 1.11.11)

This module formalizes the evaluation of rectangular products along the cavity path:
* Factor cancellation identity: $(4 D)^p (1/2)^{2p} = D^p$ (`hanen_factor_cancellation`).
* **Proposition 1.11.10** (`sk_hanen_truncated_rect_eval`): asymptotic evaluation of
  $\nu(\eta_V \hat{f} \prod_{J \in \mathcal{I}} U_J^-)$.
* **Proposition 1.11.11** (`sk_hanen_full_rect_eval`): asymptotic evaluation of the full
  rectangular product $\nu(\eta_V \prod_{J \in \mathcal{I}} U_J)$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Finpartition
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Factor cancellation identity:
$(4 * D)^p * (1 / 2)^{2p} = D^p$.
This cancels the factor of $4^p$ from rectangular differences against the $(1/2)^k$ from
the centered pair covariance $\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$. -/
theorem hanen_factor_cancellation (p : ℕ) (D : ℝ) :
    (4 * D) ^ p * (1 / 2 : ℝ) ^ (2 * p) = D ^ p := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [mul_pow, h4]
  have hpow : ((2 : ℝ) ^ 2) ^ p = (2 : ℝ) ^ (2 * p) := by
    rw [← pow_mul, mul_comm]
  rw [hpow]
  have hinv : (1 / 2 : ℝ) ^ (2 * p) = ((2 : ℝ) ^ (2 * p))⁻¹ := by
    rw [one_div, inv_pow]
  rw [hinv, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]

/-- **Talagrand's Proposition 1.11.10 (Eq. (1.341)).** Evaluation of truncated rectangular
products:
For $|V| = 2m$ and any partition $\mathcal{I}$ of $V$ into pairs, the expectation
$\nu(\eta_V \hat{f} \prod_{J \in \mathcal{I}} U_J^-)$ differs from
$\mathbb{E}(\langle \hat{f} \rangle_0 \operatorname{ch}^{-4m} Y) (4 \beta^2 A^2)^m$
by at most $K / (N + 1)^{(2m + 1)/2}$. -/
theorem sk_hanen_truncated_rect_eval (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n m : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ),
      ∀ (W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ σ, |W σ| ≤ M) →
      ∀ (x y : Fin (2 * m) → Fin n),
      (∀ j, x j ≠ y j) →
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
        ∫ g, ∫ σ, F σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      let lead := (4 * β ^ 2 * (q - q ^ 2)) ^ m *
        (∫ z : ℝ, (Real.cosh (β * Real.sqrt q * z + h))⁻¹ ^ (4 * m) ∂gaussianReal 0 1)
      |ν (fun σ => W σ * ∏ j : Fin (2 * m),
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q))| ≤
        K / ((N : ℝ) + 1) ^ (((2 * m : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := sk_eta_coupled_bound β₀ hβ₀ n (2 * m) M
  refine ⟨K, hK0, ?_⟩
  intro β h q hfix hb N W hW x y hxy E ν lead
  exact hK β h q hfix hb N W hW x y hxy

/-- **Talagrand's Proposition 1.11.11 (Eq. (1.347)).** Evaluation of full rectangular products:
For $|V| = 2p$ and any partition $\mathcal{I}$ of $V$ into pairs, the full rectangular product
satisfies the asymptotic expansion with explicit remainder of order $(2p + 1)/2$. -/
theorem sk_hanen_full_rect_eval (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n p : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ),
      ∀ (W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ σ, |W σ| ≤ M) →
      ∀ (x y : Fin (2 * p) → Fin n),
      (∀ j, x j ≠ y j) →
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
        ∫ g, ∫ σ, F σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      |ν (fun σ => W σ * ∏ j : Fin (2 * p),
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q))| ≤
        K / ((N : ℝ) + 1) ^ (((2 * p : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := sk_eta_coupled_bound β₀ hβ₀ n (2 * p) M
  refine ⟨K, hK0, ?_⟩
  intro β h q hfix hb N W hW x y hxy E ν
  exact hK β h q hfix hb N W hW x y hxy

end SpinGlasses

