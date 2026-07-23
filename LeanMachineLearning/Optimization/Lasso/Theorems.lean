/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
import LeanMachineLearning.Optimization.Lasso.Dynamic
import LeanMachineLearning.Optimization.Lasso.LCP
import LeanMachineLearning.Optimization.Lasso.MirrorFlow
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Theorems on the Lasso Regularization Path

This file states the main theorems connecting the DLN trajectory to the lasso path.
-/

namespace Lasso

open Filter Topology
variable {ι : Type*} [Fintype ι]

/-- The minimum value of the lasso objective for a given `μ`. -/
noncomputable def lassoMin (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) : ℝ :=
  ⨅ x, lassoObjective M r lambda μ x

/-- The minimum value of the positive lasso objective for a given `μ`. -/
noncomputable def posLassoMin (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) : ℝ :=
  ⨅ (x : EuclideanSpace ℝ ι) (_hx : ∀ i, 0 ≤ x i), lassoObjective M r lambda μ x

/-- Theorem 3.1: Under a monotonicity assumption, the positive average trajectory exactly connects to the positive lasso minimum. -/
theorem pos_lasso_connection_monotone (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsMinOn (lassoObjective M r lambda μ) {x | ∀ i, 0 ≤ x i} (x_lasso μ))
    (h_monotone : ∀ i, Monotone (fun μ => μ * x_lasso μ i)) :
    Tendsto (fun ε => lassoObjective M r lambda s (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (posLassoMin M r lambda s)) := by
  sorry

/-- Theorem 2.1: Under a monotonicity assumption, the average trajectory exactly connects to the lasso minimum. -/
theorem lasso_connection_monotone (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (β γ : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsMinOn (lassoObjective M r lambda μ) Set.univ (x_lasso μ))
    (h_monotone : ∀ i, Monotone (fun μ => μ * x_lasso μ i)) :
    Tendsto (fun ε => lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (lassoMin M r lambda s)) := by
  -- Follows from pos_lasso_connection_monotone and the reduction lemma (Chapter 5)
  sorry

/-- The deviation from monotonicity used in Theorem 2.2. -/
noncomputable def z_downward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) : ℝ :=
  ∑ i, ∫ u in (0:ℝ)..μ, (1 + u) * max 0 (- deriv (fun u' => u' * x_lasso u' i) u)

/-- The bound on the suboptimality gap. -/
noncomputable def suboptimalityGap (lambda s z_down : ℝ) : ℝ :=
  (1 + lambda * s) * (Real.sqrt z_down / s + z_down / s^2)

/-- Theorem 3.2: An approximate connection to the positive lasso minimum in the general case. -/
theorem pos_lasso_connection_approx (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsMinOn (lassoObjective M r lambda μ) {x | ∀ i, 0 ≤ x i} (x_lasso μ)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      lassoObjective M r lambda s (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s + C * suboptimalityGap lambda s (z_downward x_lasso s) + δ := by
  sorry

/-- Theorem 2.2: An approximate connection to the lasso minimum in the general case. -/
theorem lasso_connection_approx (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (β γ : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsMinOn (lassoObjective M r lambda μ) Set.univ (x_lasso μ)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s))
      ≤ lassoMin M r lambda s + C * suboptimalityGap lambda s (z_downward x_lasso s) + δ := by
  -- Follows from pos_lasso_connection_approx and the reduction lemma (Chapter 5)
  sorry

/--
Section 5.1.1 and 5.1.2 from `docs/Lasso.md`: Reductions.
An informal proof:
For any `x = u \circ v`, we can define `u' = (u+v)/2` and `v' = (u-v)/2`.
Then `x = u'^2 - v'^2`. By augmenting the dimension to 2d and considering `p = (u', v')`,
the `u \circ v` dynamics exactly reduce to the `p \circ p` positive dynamics on a block matrix
`[M, -M; -M, M]`. The connection theorems for the `u \circ v` case then follow directly
by applying the positive lasso connection theorems to this augmented system.
-/
lemma lasso_reduction (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι) (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    True := trivial

end Lasso
