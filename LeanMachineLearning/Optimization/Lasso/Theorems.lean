/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
import LeanMachineLearning.Optimization.Lasso.Dynamic
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
  sorry

/-- The deviation from monotonicity used in Theorem 2.2. -/
noncomputable def z_downward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) : ℝ :=
  ∑ i, ∫ u in (0:ℝ)..μ, (1 + u) * max 0 (- deriv (fun u' => u' * x_lasso u' i) u)

/-- The bound on the suboptimality gap. -/
noncomputable def suboptimalityGap (lambda s z_down : ℝ) : ℝ :=
  (1 + lambda * s) * (Real.sqrt z_down / s + z_down / s^2)

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
  sorry

end Lasso
