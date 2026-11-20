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
# Algebraic preparations for the Gaussian integration by parts on the smart path

Talagrand Section 2.2, Proposition 2.2.3. The Gaussian integration by parts itself is not
formalized yet; this module contains the algebra it will use.

* `smartPath_sqrt_scaling_prefactor_eq`, `smartPath_auxiliary_prefactor_eq_neg`: the prefactors
  that cancel the `√s` and `√(1 - s)` denominators of the energy derivative (2.27);
* `replicaPairCombination_eq_half_replica_covariance_combination` and
  `replicaPairCombination_lastSpinKernel`: the two-replica combination of (2.24)--(2.25) as half of
  the four-term covariance combination of the cavity method.

The objects of the path (`smartPathEnergy`, `smartPathBase`, ...) are in `SmartPathModel.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

/-- Square-root scaling prefactor of the Gaussian integration by parts on the smart path:
`(1 / (2 * √(N + 1))) * (1 / √s) * √(s / (N + 1)) = 1 / (2 * (N + 1))` for `s > 0`. With `s = t`
this is the quenched-disorder prefactor, with `s = 1 - t` the auxiliary-spin one. -/
theorem smartPath_sqrt_scaling_prefactor_eq {N : ℕ} {s : ℝ} (hs : 0 < s) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (1 / Real.sqrt s) *
      Real.sqrt (s / (N + 1 : ℕ)) =
    1 / (2 * (N + 1 : ℝ)) := by
  push_cast
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [Real.sqrt_div hs.le]
  have h1 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h2 : Real.sqrt ((N : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have h3 := Real.mul_self_sqrt hN.le
  field_simp
  nlinarith [h3]

/-- Simplification of the auxiliary spin prefactor: the product
`(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1))` simplifies to
`- 1 / (2 * (N + 1))`, cancelling the `√(1 - t)` denominator. -/
theorem smartPath_auxiliary_prefactor_eq_neg {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  have := smartPath_sqrt_scaling_prefactor_eq (N := N) (sub_pos.2 ht.2)
  linear_combination -this

/-- Connection with the 4-term replica covariance combination from `SKCavityBounds.lean`:
for any kernel with constant diagonal, `replicaPairCombination` is exactly half of the 4-term
combination. -/
theorem replicaPairCombination_eq_half_replica_covariance_combination
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    replicaPairCombination U τ =
      ((∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, U (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            U (τ (some none)) (τ none)) / 2 := by
  rw [replica_covariance_combination_eq_two_sum_lt U C hdiag hsym τ]
  dsimp only [replicaPairCombination]
  ring

/-- For the last-spin interaction kernel `lastSpinKernel x y = ε_x ε_y` the diagonal is `1`
(`σ_{N+1}² = 1`) and the kernel is symmetric, so `replicaPairCombination` is half of the four-term
replica covariance combination, with no hypothesis on the replicas. Note: `[LinearOrder R]` is
only used to order the pairs `r < r'` without double counting. -/
theorem replicaPairCombination_lastSpinKernel {N M : ℕ} {R : Type*} [Fintype R] [LinearOrder R]
    (τ : Option (Option R) → SmartPathState N M) :
    replicaPairCombination (lastSpinKernel (N := N) (M := M)) τ =
      ((∑ r : R, ∑ r' : R, lastSpinKernel (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, lastSpinKernel (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * lastSpinKernel (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            lastSpinKernel (τ (some none)) (τ none)) / 2 :=
  replicaPairCombination_eq_half_replica_covariance_combination _ 1 lastSpinKernel_self
    lastSpinKernel_comm τ

end SpinGlasses
