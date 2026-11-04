/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKFixedPointResidual
public import LeanMachineLearning.SpinGlasses.SKGuerraBound

/-!
# Guerra's bound at *the* solution of the self-consistency equation (Talagrand, Section 1.3)

In the book, Theorem 1.3.7 is stated for `SK(β, h) := RS(q)` where `q` is *the* solution of
Eq. (1.74); this is well defined by Proposition 1.3.8.  The statements of `SKGuerraBound.lean` and
`SKFixedPoint.lean` quantify over an arbitrary `q` or an arbitrary solution.  For `h ≠ 0` the
uniqueness theorem `existsUnique_fixedPoint` lets us state the book's version.

## Main declarations

* `SpinGlasses.existsUnique_fixedPoint_replica_symmetric_upper_bound`

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eq. (1.74),
  Theorem 1.3.7 and Proposition 1.3.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace SpinGlasses

/-- **Guerra's bound at the unique solution of Eq. (1.74) (Talagrand, Theorem 1.3.7 with
Proposition 1.3.8), for `h ≠ 0`.**  There is exactly one `q ∈ [0, 1]` such that
`q = 𝔼 tanh²(β √q z + h)` and `p_N(β, h) ≤ log 2 + 𝔼 log cosh (β √q z + h) + β²/4 (1 - q)²`
for all `N ≥ 1`; so `SK(β, h) := RS(q)` is well defined. -/
theorem existsUnique_fixedPoint_replica_symmetric_upper_bound (β : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ∃! q : ℝ, (q ∈ Icc (0 : ℝ) 1 ∧
        ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) ∧
      ∀ N : ℕ, 0 < N →
        (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
          Real.exp ((Real.sqrt N)⁻¹ * β *
            (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
            h * ∑ i, ((σ i : ℤ) : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
        Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) +
          β ^ 2 / 4 * (1 - q) ^ 2 := by
  obtain ⟨q, ⟨hq, hfix⟩, hu⟩ := existsUnique_fixedPoint β hh
  exact ⟨q, ⟨⟨hq, hfix⟩, fun N hN => sk_replica_symmetric_upper_bound hN β h q hq.1⟩,
    fun r hr => hu r hr.1⟩

end SpinGlasses
