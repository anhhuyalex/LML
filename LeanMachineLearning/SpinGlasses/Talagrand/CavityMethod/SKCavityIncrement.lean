/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKPairPerturbEstimate

/-!
# Talagrand's Proposition 1.6.8: the cavity free-energy increment

Combining the exact increment identity (Eq. 1.176) with the two interpolation estimates
(Eqs. 1.181 and 1.182) proves, for every `N > 0`, `β, h` and `q ∈ [0, 1]`,
`|(N+1) p_{N+1}(β, h) - N p_N(β, h) - A(β, h, q)| ≤ K (1/N + ν(|R_{1,2} - q|))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Talagrand's Proposition 1.6.8 (Eq. 1.170), unconditional.**
For all `N > 0`, `β, h ∈ ℝ` and `q ∈ [0, 1]` (no smallness of `β`, no fixed-point equation),
the expected free energies `E log Z_N(β, h)` of the SK model with `N` and `N + 1` spins satisfy
`|E log Z_{N+1} - E log Z_N - (log 2 + (β²/4)(1-q)² + E log cosh(β z √q + h))| ≤
K (1/N + ν)`, with explicit `K = 2 β² exp(12 β²) cosh(2h) + 1`, where `ν` is the `N`-spin
two-replica Gibbs and disorder average of `|R_{1,2} - q|` at inverse temperature `β`.
Since `(N+1) p_{N+1} - N p_N = E log Z_{N+1} - E log Z_N` this is the book's `(1.170)`. -/
theorem sk_cavity_free_energy_increment (N : ℕ) (β h q : ℝ) (hN : 0 < N)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ g : FinPairs (N + 1) → ℝ,
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ,
          Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (Real.log 2 + β ^ 2 / 4 * (1 - q) ^ 2 +
        ∫ z : ℝ, Real.log (Real.cosh (β * z * Real.sqrt q + h)) ∂gaussianReal 0 1)| ≤
    (2 * β ^ 2 * Real.exp (12 * β ^ 2) * Real.cosh (2 * h) + 1) *
      (1 / (N : ℝ) +
        ∫ g' : FinPairs N → ℝ,
          ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
            |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i : ℝ) * (p.2 i : ℝ) - q|
            ∂((Measure.count.tilted (fun ρ =>
              (Real.sqrt (N : ℝ))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
                h * ∑ i, (ρ i : ℝ))).prod
              (Measure.count.tilted (fun ρ =>
                (Real.sqrt (N : ℝ))⁻¹ * β *
                  (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
                  h * ∑ i, (ρ i : ℝ))))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) :=
  sk_cavity_free_energy_increment_le N β h q hN hq
    (sk_cavity_cosh_estimate N β h q hN hq) (sk_pair_perturb_estimate N hN β h q hq)

end SpinGlasses
