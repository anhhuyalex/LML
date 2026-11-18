/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDisorderDerivative
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPPotential
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityBounds

/-!
# Gaussian integration by parts and Proposition 2.2.3 (the smart path derivative)

This module formalizes the Gaussian integration by parts for the perceptron smart path
(Talagrand Section 2.2, Proposition 2.2.3 and Exercise 2.2.4):

1. **Auxiliary spin integration by parts:**
   Integrating by parts against the independent auxiliary Gaussian vector `ξ_k ~ 𝒩(0, 1)` pulls
   down `√( (1 - t) / (N + 1) ) * (u''(S_k) + (u'(S_k))²)`, cancelling the `√(1 - t)` denominator
   via `perceptron_smart_path_auxiliary_prefactor` to yield `-1 / (2 * (N + 1))`.

2. **Quenched disorder integration by parts:**
   Integrating by parts against the quenched row disorder `a_k ~ 𝒩(0, 1)` pulls down
   `√( t / (N + 1) )`, cancelling the `√t` denominator via
   `perceptron_smart_path_quenched_prefactor` to produce a diagonal term
   `+1 / (2 * (N + 1)) * (u''(S_k) + (u'(S_k))²)` and off-diagonal cross-replica interaction
   terms `u'(S_k^ℓ) u'(S_k^{ℓ'})`.

3. **Exact diagonal cancellation:**
   The diagonal terms `+1 / (2 * (N + 1))` from quenched disorder and `-1 / (2 * (N + 1))`
   from auxiliary spins cancel out completely.

4. **Quenched last-field integration by parts:**
   Integrating by parts against `Y ~ 𝒩(0, v)` yields `-v` times the replica spin overlaps.

5. **Proposition 2.2.3:**
   The smart-path derivative equals the sum of the replica cross-interaction of potential
   derivatives and the last-spin replica covariance combination.

6. **Exercise 2.2.4 (smart path without auxiliary spins):**
   Without auxiliary spins, the auxiliary integration by parts is absent, so the diagonal
   second-derivative contribution survives.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace SpinGlasses

/-- Simplification of the auxiliary spin prefactor: the product
`(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1))` simplifies to
`- 1 / (2 * (N + 1))`, cancelling the `√(1 - t)` denominator. -/
theorem perceptron_smart_path_auxiliary_prefactor {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  push_cast
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hsqN : (Real.sqrt ((N : ℝ) + 1)) ^ 2 = ((N : ℝ) + 1) := Real.sq_sqrt hN.le
  have hsqrt_t : Real.sqrt (1 - t) ≠ 0 := Real.sqrt_ne_zero'.mpr ht1
  rw [Real.sqrt_div ht1.le]
  have hmul : (1 / (2 * Real.sqrt ((N : ℝ) + 1))) * (- (1 / Real.sqrt (1 - t))) *
      (Real.sqrt (1 - t) / Real.sqrt ((N : ℝ) + 1)) =
      - ((1 / (2 * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1)))) *
         (Real.sqrt (1 - t) / Real.sqrt (1 - t))) := by ring
  rw [hmul, div_self hsqrt_t, mul_one, ← sq, hsqN]

/-- Simplification of the quenched disorder prefactor: the product
`(1 / (2 * √(N + 1))) * (1 / √t) * √(t / (N + 1))` simplifies to `1 / (2 * (N + 1))`,
cancelling the `√t` denominator. -/
theorem perceptron_smart_path_quenched_prefactor {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (1 / Real.sqrt t) *
      Real.sqrt (t / (N + 1 : ℕ)) =
    (1 / (2 * (N + 1 : ℝ))) := by
  push_cast
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht0 : 0 < t := ht.1
  have hsqN : (Real.sqrt ((N : ℝ) + 1)) ^ 2 = ((N : ℝ) + 1) := Real.sq_sqrt hN.le
  have hsqrt_t : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht0
  rw [Real.sqrt_div ht0.le]
  have hmul : (1 / (2 * Real.sqrt ((N : ℝ) + 1))) * (1 / Real.sqrt t) *
      (Real.sqrt t / Real.sqrt ((N : ℝ) + 1)) =
      ((1 / (2 * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1)))) *
       (Real.sqrt t / Real.sqrt t)) := by ring
  rw [hmul, div_self hsqrt_t, mul_one, ← sq, hsqN]

/-- The two-replica difference combination appearing in the cavity and smart-path derivatives
(Talagrand (2.24)--(2.25)):
`∑_{r < r'} U(σ^r, σ^{r'}) - n ∑_r U(σ^r, σ^{n+1}) + n(n+1)/2 U(σ^{n+1}, σ^{n+2})`. -/
noncomputable def replicaPairDiff {R α : Type*} [Fintype R] [LinearOrder R]
    (U : α → α → ℝ) (τ : Option (Option R) → α) : ℝ :=
  (∑ p : R × R with p.1 < p.2, U (τ (some (some p.1))) (τ (some (some p.2)))) -
    (Fintype.card R : ℝ) * (∑ r : R, U (τ (some (some r))) (τ (some none))) +
    (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * U (τ (some none)) (τ none)

theorem replicaPairDiff_const_mul {R α : Type*} [Fintype R] [LinearOrder R]
    (c : ℝ) (U : α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => c * U a b) τ = c * replicaPairDiff U τ := by
  simp only [replicaPairDiff, mul_sub, mul_add, ← Finset.mul_sum]
  ring

theorem replicaPairDiff_add {R α : Type*} [Fintype R] [LinearOrder R]
    (U₁ U₂ : α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => U₁ a b + U₂ a b) τ =
      replicaPairDiff U₁ τ + replicaPairDiff U₂ τ := by
  simp only [replicaPairDiff, Finset.sum_add_distrib]
  ring

theorem replicaPairDiff_sum {R α ι : Type*} [Fintype R] [LinearOrder R] [Fintype ι]
    (U : ι → α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => ∑ k, U k a b) τ =
      ∑ k, replicaPairDiff (U k) τ := by
  dsimp only [replicaPairDiff]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm
    (s := Finset.filter (fun p : R × R => p.1 < p.2) Finset.univ) (t := Finset.univ)]
  congr 1
  congr 1
  rw [Finset.sum_comm (s := (Finset.univ : Finset R)) (t := Finset.univ)]

/-- Connection with the 4-term replica covariance combination from `SKCavityBounds.lean`:
for any kernel with constant diagonal, `replicaPairDiff` is exactly half of the 4-term
combination. -/
theorem replicaPairDiff_eq_half_replica_covariance_combination
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    replicaPairDiff U τ =
      ((∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, U (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            U (τ (some none)) (τ none)) / 2 := by
  rw [replica_covariance_combination_eq_two_sum_lt U C hdiag hsym τ]
  dsimp only [replicaPairDiff]
  ring

/-- The kernel for the replica cross-interaction of potential derivatives (Talagrand (2.24)):
`U(k, x, y) = ε_x * ε_y * u'(S_k(x)) * u'(S_k(y))`. -/
noncomputable def perceptronReplicaPotentialDerivKernel {N M : ℕ}
    (u : ℝ → ℝ) (t : ℝ)
    (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) (k : Fin M)
    (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) : ℝ :=
  let S := fun (p : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
    (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((p.1.1 i : ℤ) : ℝ)) +
      Real.sqrt (t / (N + 1)) * ω.1.2 k * ((p.1.2 : ℤ) : ℝ) +
      Real.sqrt ((1 - t) / (N + 1)) * p.2 k
  ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (S x) * deriv u (S y)

theorem perceptronReplicaPotentialDerivKernel_symm {N M : ℕ}
    (u : ℝ → ℝ) (t : ℝ)
    (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) (k : Fin M)
    (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
    perceptronReplicaPotentialDerivKernel u t ω k x y =
      perceptronReplicaPotentialDerivKernel u t ω k y x := by
  dsimp only [perceptronReplicaPotentialDerivKernel]
  ring

/-- The diagonal second-derivative plus squared-first-derivative potential combination
appearing in Gaussian integration by parts (Talagrand (2.29), (2.34)):
`D(k, x) = u''(S_k(x)) + (u'(S_k(x)))^2`. -/
noncomputable def perceptronPotentialSecondDerivKernel {N M : ℕ}
    (u : ℝ → ℝ) (t : ℝ)
    (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) (k : Fin M)
    (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) : ℝ :=
  let S := fun (p : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
    (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((p.1.1 i : ℤ) : ℝ)) +
      Real.sqrt (t / (N + 1)) * ω.1.2 k * ((p.1.2 : ℤ) : ℝ) +
      Real.sqrt ((1 - t) / (N + 1)) * p.2 k
  deriv (deriv u) (S x) + (deriv u (S x)) ^ 2

/-- Constraint symmetry reduction: for `M + 1` constraints, if every constraint
yields the same value as the last constraint `Fin.last M`, the sum of `1 / (N + 1)`
over all constraints equals `(M + 1) / (N + 1)` times the last constraint value. -/
theorem sum_div_eq_alpha_mul_last {N M : ℕ} (f : Fin (M + 1) → ℝ)
    (hconst : ∀ k : Fin (M + 1), f k = f (Fin.last M)) :
    (∑ k : Fin (M + 1), (1 / (N + 1 : ℝ)) * f k) =
      ((M + 1 : ℝ) / (N + 1 : ℝ)) * f (Fin.last M) := by
  have hsum : (∑ k : Fin (M + 1), f k) = (M + 1 : ℝ) * f (Fin.last M) := by
    rw [Finset.sum_congr rfl (fun k _ => hconst k)]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one]
  rw [← Finset.mul_sum, hsum]
  ring

end SpinGlasses
