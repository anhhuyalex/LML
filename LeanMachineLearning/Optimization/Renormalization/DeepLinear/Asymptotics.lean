/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.GaussianLayer
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Reusable asymptotics for finite-width corrections

The first theorem is deliberately independent of probability and neural networks.  It is the
generic finite-product estimate from which the chapter's fixed-depth expansions follow.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Asymptotics

universe u

/-- First-order expansion of a finite product of `1 + aᵢ/n`.

Informal proof: induct on `s`.  Multiplying the induction hypothesis by `1+a/n` adds `a/n` to the
linear term.  The cross term is a constant multiple of `n⁻²`, while the old remainder remains
`O(n⁻²)` because `1+a/n` is eventually bounded.  This is the elementary finite-product expansion;
see <https://en.wikipedia.org/wiki/Big_O_notation#Properties> for the closure rules.
-/
theorem finset_prod_one_add_inv_sub {ι : Type u} (s : Finset ι) (a : ι → ℝ) :
    (fun n : ℕ =>
      (∏ i ∈ s, (1 + a i / (n : ℝ))) -
        (1 + (∑ i ∈ s, a i) / (n : ℝ))) =O[atTop]
      (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  sorry

end Asymptotics

namespace NeuralNetwork.DeepLinear

/-- The width factor has linear coefficient `m(m-1)`.

Informal proof: apply `Asymptotics.finset_prod_one_add_inv_sub` to `a_s=2s` on `range m` and use
`2 * ∑ s<m s = m(m-1)`.  Source: `docs/Renormalization.md`, expansion following equation
`eq:combinatorial-2m`.
-/
theorem widthMomentFactor_sub_linear_isBigO (m : ℕ) :
    (fun n : ℕ => widthMomentFactor m n -
      (1 + ((m : ℝ) * (m - 1 : ℕ)) / (n : ℝ))) =O[atTop]
      (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  sorry

/-- Fixed-depth expansion of the equal-width correction.

Informal proof: raise the preceding expansion to the fixed natural power `depth`; the finite
binomial expansion has linear term `depth * m(m-1)/n` and every remaining nonconstant term is
`O(n⁻²)`.  Source: `docs/Renormalization.md`, equation `eq:deep-linear-2m-leading`.
-/
theorem equalWidthCorrection_sub_linear_isBigO (m depth : ℕ) :
    (fun n : ℕ => widthMomentFactor m n ^ depth -
      (1 + ((depth : ℝ) * (m : ℝ) * (m - 1 : ℕ)) / (n : ℝ))) =O[atTop]
      (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  sorry

/-- Quadratic remainder for `exp (2r) - 1` at zero.

Informal proof: specialize `Real.exp_sub_sum_range_isBigO_pow` at order two and rescale the
argument by two; the first two Taylor terms are `1+2r`.  Source:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ExpDeriv.html>.
-/
theorem exp_two_sub_linear_isBigO :
    (fun r : ℝ => Real.exp (2 * r) - 1 - 2 * r) =O[nhds 0]
      (fun r : ℝ => r ^ 2) := by
  sorry

/-- Cubic remainder for the connected sixth-order double-scaling coefficient.

Informal proof: expand `exp (6r)` and `exp (2r)` to second order with
`Real.exp_sub_sum_range_isBigO_pow`; constant and linear terms cancel and the quadratic term is
`12r²`.  Closure of `IsBigO` under finite linear combinations absorbs the cubic remainders.
Source:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ExpDeriv.html>.
-/
theorem exp_six_sub_three_exp_two_add_two_isBigO :
    (fun r : ℝ => Real.exp (6 * r) - 3 * Real.exp (2 * r) + 2 - 12 * r ^ 2) =O[nhds 0]
      (fun r : ℝ => r ^ 3) := by
  sorry

end NeuralNetwork.DeepLinear

end

end
