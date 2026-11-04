/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenEvaluation
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.Optimization.Renormalization.Gaussian

/-!
# Hanen's Theorem (Talagrand, Theorem 1.11.1, Eq. (1.329))

This module proves Hanen's Theorem on the non-Gaussian limit of the two-spin overlap fluctuation:
for $\beta < 1/2$,
$$\mathbb E(\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle)^k
= a(k) \left( \frac{\beta^2}{(N+1)(1 - \beta^2(1 - 2q + \hat q))} \right)^{k/2}
(\mathbb E \operatorname{ch}^{-2k} Y)^2 + O((N+1)^{-(k+1)/2}),$$
where $a(k) = \mathbb E g^k$ ($a(k) = (k-1)!!$ for $k$ even, $0$ for $k$ odd).

## Main declaration

* `SpinGlasses.sk_hanen_theorem`: Theorem 1.11.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- Odd standard Gaussian moments vanish. -/
theorem gaussian_moment_odd (m : ℕ) :
    ∫ x : ℝ, x ^ (2 * m + 1) ∂gaussianReal 0 1 = 0 := by
  simpa using Renormalization.integral_pow_gaussianReal_odd 1 m

/-- Even standard Gaussian moments are given by the double factorial $(2m-1)!!$. -/
theorem gaussian_moment_even (m : ℕ) :
    ∫ x : ℝ, x ^ (2 * m) ∂gaussianReal 0 1 =
      ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) := by
  have := Renormalization.integral_pow_gaussianReal_even 1 m
  simpa using this

/-- **Talagrand's Theorem 1.11.1 (A. Hanen, Eq. (1.329)).** Non-Gaussian limit of the two-spin
overlap fluctuation: for $\beta^2 \le \beta_0^2 < 1/4$, the $k$-th moment of
$\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$ is
$a(k) (\beta^2 / ((N+1)(1 - \beta^2(1 - 2q + \hat q))))^{k/2}$ times
$(\mathbb E \operatorname{ch}^{-2k} Y)^2$ up to $O((N+1)^{-(k+1)/2})$,
uniformly in the high-temperature regime. -/
theorem sk_hanen_theorem (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (i₁ i₂ : Fin (N + 1)) (hne : i₁ ≠ i₂),
      let α : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let D_var : ℝ := β ^ 2 / ((N + 1 : ℝ) * (1 - β ^ 2 * α))
      let a_k : ℝ := ∫ x : ℝ, x ^ k ∂gaussianReal 0 1
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      |∫ g : FinPairs (N + 1) → ℝ,
          (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) * (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)) -
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) ∂(Measure.count.tilted (E g))) *
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)))) ^ k
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) -
        a_k * (D_var) ^ (k / 2) *
          (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * k))⁻¹ ∂gaussianReal 0 1) ^ 2| ≤
      K / ((N : ℝ) + 1) ^ ((((k + 1 : ℕ) : ℝ)) / 2) := by
  sorry

end SpinGlasses
