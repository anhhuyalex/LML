/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSmartPathProfile

/-!
# Guerra's replica-symmetric upper bound for the SK free energy

This module closes Talagrand's Theorem 1.3.7: for every `q ≥ 0`,
$$p_N(\beta, h) \le \log 2 + \mathbb{E}\log\cosh(\beta z\sqrt{q} + h) +
  \frac{\beta^2}{4}(1 - q)^2.$$
It combines the free energy profile along the smart path
(`exists_sk_smart_path_profile`) with the calculus endpoint estimate
(`le_endpoint_of_trig_square_deriv`).

## Main declaration

* `SpinGlasses.sk_replica_symmetric_upper_bound`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.3.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Guerra's replica-symmetric upper bound (Talagrand, Theorem 1.3.7).** For every `q ≥ 0`,
`p_N(β, h) ≤ log 2 + 𝔼 log cosh (β √q z + h) + β²/4 (1 - q)²`, with `z ~ 𝒩(0, 1)`. -/
theorem sk_replica_symmetric_upper_bound {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q) :
    (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
    Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) +
      β ^ 2 / 4 * (1 - q) ^ 2 := by
  obtain ⟨φ, A, h0, hpi, hderiv, hAnn, -⟩ := exists_sk_smart_path_profile hN β h q hq
  have := le_endpoint_of_trig_square_deriv φ A β q hderiv hAnn
  rw [← h0]
  linarith

end SpinGlasses
