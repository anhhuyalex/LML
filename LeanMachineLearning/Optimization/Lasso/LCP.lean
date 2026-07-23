/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
import LeanMachineLearning.Optimization.Lasso.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear Complementarity Problem (LCP) Formulations for Lasso

This file formalizes the primal-dual LCP formulations of the Lasso regularization path.
-/

namespace Lasso

variable {ι : Type*} [Fintype ι]

/-- The Linear Complementarity Problem (LCP) associated with the positive lasso.
For a given `x`, it requires finding `v` such that `v = q + Mx`, `v ≥ 0`, `x ≥ 0`, and `⟨v, x⟩ = 0`. -/
def isLCP (M : Matrix ι ι ℝ) (q x v : EuclideanSpace ℝ ι) : Prop :=
  v = (WithLp.equiv 2 _).symm (q + M.mulVec x) ∧
  (∀ i, 0 ≤ v i) ∧ (∀ i, 0 ≤ x i) ∧ inner ℝ v x = (0 : ℝ)

/--
Proposition 4.8 from `docs/Lasso.md`: The primal-dual formulation of the positive lasso is a linear complementarity problem.
An informal proof:
The positive lasso objective is a convex quadratic function on the nonnegative orthant.
The Lagrangian is `L(x, v) = (1/2) <x, Mx> + <q, x> - <v, x>` where `q = -r + (\lambda + 1/\mu) \mathbb{1}`.
The KKT conditions are necessary and sufficient:
- Stationarity: `0 = \nabla_x L = q + Mx - v`
- Primal feasibility: `x \ge 0`
- Dual feasibility: `v \ge 0`
- Complementary slackness: `<v, x> = 0`
This exactly matches the LCP formulation.
-/
lemma pos_lasso_is_lcp (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) (x : EuclideanSpace ℝ ι) :
    IsMinOn (lassoObjective M r lambda μ) {x | ∀ i, 0 ≤ x i} x ↔
    ∃ v : EuclideanSpace ℝ ι,
      let q : EuclideanSpace ℝ ι := (WithLp.equiv 2 _).symm (fun i => -r i + lambda + 1 / μ);
      isLCP M q x v := by
  sorry

/-- The parametric LCP (Eq 4.11 in docs/Lasso.md).
Defined for `w(μ) = μ v(μ)` and `z(μ) = μ x(μ)`. -/
def isParametricLCP (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) (z w : EuclideanSpace ℝ ι) : Prop :=
  let q : EuclideanSpace ℝ ι := (WithLp.equiv 2 _).symm (fun i => -μ * r i + 1 + μ * lambda);
  isLCP M q z w

/--
Lemma 4.10 from `docs/Lasso.md`: For small `μ`, the parametric LCP has a unique solution.
An informal proof:
For `0 \le \mu < 1/\max(||r - \lambda \mathbb{1}||_\infty, 1)`, we have `q = (1 + \mu \lambda) \mathbb{1} - \mu r > 0`.
Setting `z = 0` and `w = q` satisfies `w = q + M z`, `w \ge 0`, `z \ge 0`, and `<w, z> = 0`.
Since `q > 0` and `M` is PSD, this is the unique solution because any `z \ge 0` with `z \ne 0` would make `<w, z> > 0`.
-/
lemma parametric_lcp_unique_small_mu (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hμ : 0 ≤ μ) (hμ_small : μ * ‖(WithLp.equiv 2 _).symm (fun i => r i - lambda)‖ < 1) :
    ∃! p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, isParametricLCP M r lambda μ p.1 p.2 := by
  sorry

end Lasso
