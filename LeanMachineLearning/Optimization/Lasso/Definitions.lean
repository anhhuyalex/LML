/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import LeanMachineLearning.Optimization.Lasso.LCP
public import LeanMachineLearning.Optimization.Lasso.MirrorFlow
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Block

@[expose] public section

namespace Lasso

open Filter Topology
variable {ι : Type*} [Fintype ι]
set_option linter.unusedFintypeInType false

/-! ## Minimum values and path quantities -/

/-- The minimum value of the lasso objective for a given `μ`. -/
noncomputable def lassoMin (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι)
    (lambda μ : ℝ) : ℝ :=
  ⨅ x, lassoObjective M r lambda μ x

/-- The minimum value of the positive lasso objective for a given `μ`. -/
noncomputable def posLassoMin (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι)
    (lambda μ : ℝ) : ℝ :=
  ⨅ (x : EuclideanSpace ℝ ι) (_hx : Nonnegative x), positiveLassoObjective M r lambda μ x

/-- The seminorm squared induced by `M`, written as `<x, Mx>`. -/
noncomputable def matrixSeminormSq (M : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  inner ℝ x (matVec M x)

/-- The `Δε(s)` quantity from Section 4.6. -/
noncomputable def pathDelta
    (M : Matrix ι ι ℝ) (zε z : ℝ → EuclideanSpace ℝ ι) (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * matrixSeminormSq M (zε s - z s)

/-- Positive-lasso path scaling `z(μ) = μ x(μ)`. -/
noncomputable def scaledPrimalPath (x : ℝ → EuclideanSpace ℝ ι) :
    ℝ → EuclideanSpace ℝ ι :=
  fun μ => μ • x μ

/-- The deviation from monotonicity used in the positive-lasso Theorem 3.2. -/
noncomputable def positiveZDownward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) :
    ℝ :=
  ∑ i, ∫ u in (0 : ℝ)..μ, (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)

/-- The upward variation auxiliary quantity used in Eq. (4.15). -/
noncomputable def positiveZUpward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) :
    ℝ :=
  ∑ i, ∫ u in (0 : ℝ)..μ, max 0 (deriv (fun u' => u' * x_lasso u' i) u)

/-- Compatibility alias for the positive-lasso downward variation. -/
noncomputable def zDownward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) : ℝ :=
  positiveZDownward x_lasso μ

/-- The explicit vanishing term from Eq. (4.15). -/
noncomputable def deltaVanishingTerm (ε s z_up : ℝ) : ℝ :=
  (s + z_up) / Real.log (1 / ε)

/-- The full Eq. (4.15) error profile before taking `ε → 0`. -/
noncomputable def deltaFullError (ε s z_up z_down : ℝ) : ℝ :=
  deltaVanishingTerm ε s z_up + z_down

/-- The bound on the final suboptimality gap, Eq. (2.4). -/
noncomputable def suboptimalityGap (lambda s z_down : ℝ) : ℝ :=
  (1 + lambda * s) * (Real.sqrt z_down / s + z_down / s ^ 2)

end Lasso
