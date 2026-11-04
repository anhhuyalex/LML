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

This module states Hanen's Theorem on the non-Gaussian limit of the two-spin overlap fluctuation:
for $\beta < 1/2$,
$$\mathbb E(\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle)^k
= a(k) \left( \frac{\beta^2}{(N+1)(1 - \beta^2(1 - 2q + \hat q))} \right)^{k/2}
(\mathbb E \operatorname{ch}^{-2k} Y)^2 + O((N+1)^{-(k+1)/2}),$$
where $a(k) = \mathbb E g^k$ ($a(k) = (k-1)!!$ for $k$ even, $0$ for $k$ odd).
The odd and even estimates are currently placeholders; the parity assembly depends on them.

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

/-- **Talagrand's Theorem 1.11.1 (A. Hanen), odd moments.**
For odd $k = 2m + 1$, the Gaussian moment $a(k)$ vanishes, so the $k$-th moment of
$\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$ is
purely $O((N+1)^{-(m+1)})$. -/
theorem sk_hanen_theorem_odd (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (i₁ i₂ : Fin (N + 1)) (_ : i₁ ≠ i₂),
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      |∫ g : FinPairs (N + 1) → ℝ,
          (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) * (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)) -
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) ∂(Measure.count.tilted (E g))) *
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)))) ^ (2 * m + 1)
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      K / ((N : ℝ) + 1) ^ ((((2 * m + 2 : ℕ) : ℝ)) / 2) := by
  sorry

/-- **Talagrand's Theorem 1.11.1 (A. Hanen), even moments.**
For even $k = 2p$, $a(2p) = (2p-1)!!$, and the $2p$-th moment of
$\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$ is
$a(2p) D_{\mathrm{var}}^p (\mathbb E \operatorname{ch}^{-4p} Y)^2 + O((N+1)^{-(2p+1)/2})$. -/
theorem sk_hanen_theorem_even (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (i₁ i₂ : Fin (N + 1)) (_ : i₁ ≠ i₂),
      let α : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let D_var : ℝ := β ^ 2 / ((N + 1 : ℝ) * (1 - β ^ 2 * α))
      let a_2p : ℝ := ∫ x : ℝ, x ^ (2 * p) ∂gaussianReal 0 1
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      |∫ g : FinPairs (N + 1) → ℝ,
          (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) * (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)) -
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) ∂(Measure.count.tilted (E g))) *
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)))) ^ (2 * p)
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) -
        a_2p * (D_var) ^ p *
          (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1) ^ 2| ≤
      K / ((N : ℝ) + 1) ^ ((((2 * p + 1 : ℕ) : ℝ)) / 2) := by
  sorry

/-- **Talagrand's Theorem 1.11.1 (A. Hanen, Eq. (1.329)).** Non-Gaussian limit of the two-spin
overlap fluctuation: for $\beta^2 \le \beta_0^2 < 1/4$, the $k$-th moment of
$\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$ is
$a(k) (\beta^2 / ((N+1)(1 - \beta^2(1 - 2q + \hat q))))^{k/2}$ times
$(\mathbb E \operatorname{ch}^{-2k} Y)^2$ up to $O((N+1)^{-(k+1)/2})$,
uniformly in the high-temperature regime.

The proof reduces by parity (`Nat.even_or_odd k`) to the odd moment bound
`sk_hanen_theorem_odd` (where $a(k) = 0$ by `gaussian_moment_odd`) and the even moment formula
`sk_hanen_theorem_even` (where $a(2p) = (2p-1)!!$ by `gaussian_moment_even`). -/
theorem sk_hanen_theorem (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (i₁ i₂ : Fin (N + 1)) (_ : i₁ ≠ i₂),
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
  rcases Nat.even_or_odd k with ⟨p, rfl⟩ | ⟨m, rfl⟩
  · have h2p : p + p = 2 * p := by omega
    simp_rw [h2p]
    obtain ⟨K, hKpos, hK⟩ := sk_hanen_theorem_even β₀ hβ₀ p
    refine ⟨K, hKpos, ?_⟩
    intro β h q hfix hβ N i₁ i₂ hne
    have hp : 2 * p / 2 = p := by omega
    have h2k : 2 * (2 * p) = 4 * p := by omega
    rw [hp, h2k]
    exact hK β h q hfix hβ N i₁ i₂ hne
  · obtain ⟨K, hKpos, hK⟩ := sk_hanen_theorem_odd β₀ hβ₀ m
    refine ⟨K, hKpos, ?_⟩
    intro β h q hfix hβ N i₁ i₂ hne α D_var a_k E
    have ha : a_k = 0 := gaussian_moment_odd m
    have hzero : a_k * D_var ^ ((2 * m + 1) / 2) *
        (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * (2 * m + 1)))⁻¹
          ∂gaussianReal 0 1) ^ 2 = 0 := by
      rw [ha, zero_mul, zero_mul]
    rw [hzero, sub_zero]
    have hexp : ((((2 * m + 1 + 1 : ℕ) : ℝ)) / 2) = ((((2 * m + 2 : ℕ) : ℝ)) / 2) := by
      congr 2
    rw [hexp]
    exact hK β h q hfix hβ N i₁ i₂ hne

end SpinGlasses
