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
import Mathlib.Data.Matrix.Block

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
  ⨅ (x : EuclideanSpace ℝ ι) (_hx : Nonnegative x), positiveLassoObjective M r lambda μ x

/-- The seminorm squared induced by `M`, written as `<x, Mx>`. -/
noncomputable def matrixSeminormSq (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ℝ :=
  inner ℝ x (matVec M x)

/-- The `Δε(s)` quantity from Section 4.6. -/
noncomputable def pathDelta
    (M : Matrix ι ι ℝ) (zε z : ℝ → EuclideanSpace ℝ ι) (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * matrixSeminormSq M (zε s - z s)

/-- Positive-lasso path scaling `z(μ) = μ x(μ)`. -/
noncomputable def scaledPrimalPath (x : ℝ → EuclideanSpace ℝ ι) :
    ℝ → EuclideanSpace ℝ ι :=
  fun μ => μ • x μ

/--
Theorem 3.1: under monotonicity, the positive average trajectory exactly
connects to the positive lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 4.7. First use
`monotone_positive_path_regular` to obtain the regularity needed for Theorem
3.2. Under coordinatewise monotonicity, `positiveZDownward` is zero, so the
approximate estimate from `pos_lasso_connection_approx` has no residual error.
-/
theorem pos_lasso_connection_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        positiveLassoObjective M r lambda s
          (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (posLassoMin M r lambda s)) := by
  sorry

/--
Theorem 2.1: under monotonicity, the signed average trajectory exactly connects
to the lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 5.2.1. Reduce the signed
objective and dynamics to the positive problem on the augmented system, then
apply `pos_lasso_connection_monotone`.
-/
theorem lasso_connection_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hdata : ProblemData M r lambda)
    (hβγ : ∀ i, β i ≠ γ i ∧ β i ≠ -γ i)
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (lassoMin M r lambda s)) := by
  -- Proof sketch (Section 5.2.1 from `docs/Lasso.md`):
  -- By `dln_dynamics_reduction`, the signed dynamics map to positive dynamics
  -- on the augmented system.
  -- By `lasso_objective_reduction`, the lasso objective exactly equals the
  -- positive lasso objective on `augmentedMatrix`.
  -- Thus, applying `pos_lasso_connection_monotone` to `u_pos` yields the result.
  sorry

/-- The deviation from monotonicity used in the positive-lasso Theorem 3.2. -/
noncomputable def positiveZDownward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) : ℝ :=
  ∑ i, ∫ u in (0:ℝ)..μ, (1 + u) * max 0 (- deriv (fun u' => u' * x_lasso u' i) u)

/--
The signed-lasso deviation from monotonicity used in Theorem 2.2.
This matches Eq. (2.3): it applies the negative-variation penalty separately to
the positive and negative parts of `z_i(μ) = μ x_i(μ)`.
-/
noncomputable def signedZDownward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) :
    ℝ :=
  ∑ i,
    ∫ u in (0:ℝ)..μ,
      (1 + u) *
        (max 0 (- deriv (fun u' => max (u' * x_lasso u' i) 0) u) +
          max 0 (- deriv (fun u' => max (-(u' * x_lasso u' i)) 0) u))

/-- Backwards-compatible alias for the positive-lasso deviation. -/
noncomputable def z_downward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) : ℝ :=
  positiveZDownward x_lasso μ

/-- The bound on the suboptimality gap. -/
noncomputable def suboptimalityGap (lambda s z_down : ℝ) : ℝ :=
  (1 + lambda * s) * (Real.sqrt z_down / s + z_down / s^2)

/--
Theorem 3.2: an approximate connection to the positive lasso minimum in the
general case.

Informal proof reference: `docs/Lasso.md`, Section 4.6. Use the mirror-flow/LCP
comparison to prove the delta estimate, convert it into the energy estimate, and
take the `limsup` as `ε → 0`.
-/
theorem pos_lasso_connection_approx
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  sorry

/--
Theorem 2.2: an approximate connection to the lasso minimum in the general case.

Informal proof reference: `docs/Lasso.md`, Section 5.2.2. Reduce the signed
problem to positive lasso on the augmented system, apply
`pos_lasso_connection_approx`, and translate the positive-path downward
variation into `signedZDownward`.
-/
theorem lasso_connection_approx
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hdata : ProblemData M r lambda)
    (hβγ : ∀ i, β i ≠ γ i ∧ β i ≠ -γ i)
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s))
      ≤ lassoMin M r lambda s +
        C * suboptimalityGap lambda s (signedZDownward x_lasso s) + δ := by
  -- Proof sketch (Section 5.2.2 from `docs/Lasso.md`):
  -- By `dln_dynamics_reduction`, the signed dynamics map to positive dynamics
  -- on the augmented system.
  -- By `lasso_objective_reduction`, the lasso objective exactly equals the
  -- positive lasso objective on `augmentedMatrix`.
  -- Thus, applying `pos_lasso_connection_approx` to `u_pos` yields the result.
  sorry

/--
Section 4.6, Eq. (4.15): the `M`-seminorm distance between the integrated DLN
trajectory and the parametric positive-lasso path is controlled by the downward
variation of the path, up to terms vanishing with `ε`.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.15).
Differentiate `Δε(s) = 1/2 ‖zε(s)-z(s)‖_M²`, substitute the LCP equation and
the integrated mirror-flow equation, then bound each complementarity defect
using the uniform trajectory bound and the definition of `positiveZDownward`.
-/
theorem positive_path_delta_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      pathDelta M
        (fun τ => posIntegratedTrajectoryRescaled ε (u ε) τ)
        (scaledPrimalPath x_lasso) s
      ≤ C * (positiveZDownward x_lasso s + δ) := by
  sorry

/--
Section 4.6 final estimate: the `Δε` control implies the lasso objective
suboptimality bound of Theorem 3.2.

Informal proof reference: `docs/Lasso.md`, Section 4.6, after Eq. (4.15).
Expand the quadratic objective at a positive-lasso minimizer, write the linear
term with the dual LCP variable, and control the resulting energy `Eε(s)`.
The derivative of the scaled dual path is handled by Lemma 4.11.
-/
theorem positive_path_energy_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  sorry

/--
Lemma 4.12 from `docs/Lasso.md`: under the monotonicity hypothesis of Theorem
3.1, the scaled positive-lasso path has enough compact-interval regularity to
apply Theorem 3.2.

Informal proof reference: Section 4.7, Lemma 4.12. Lemma 4.11 gives local
Lipschitz control of the dual path and hence of the projection of `z(μ)` onto
`Span M`. Complementarity controls the kernel component; monotonicity converts
coordinatewise variation into an `L¹` bound on compact intervals.
-/
theorem monotone_positive_path_regular
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso) := by
  sorry

/--
Section 5.1.1 from `docs/Lasso.md`: Reduction of the lasso to the positive lasso.
An informal proof:
For any `x = x_+ - x_-`, construct `x_pos = [x_+, x_-]`.
Then `x_pos >= 0`, and evaluating the signed lasso objective on `x` is
equivalent to evaluating the positive lasso objective on the augmented system
`[M, -M; -M, M]` and `[r, -r]`.
-/
lemma lasso_objective_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
  ∀ x : EuclideanSpace ℝ ι, ∃ x_pos : EuclideanSpace ℝ (ι ⊕ ι),
    (∀ (i : ι ⊕ ι), 0 ≤ x_pos i) ∧
    lassoObjective M r lambda μ x =
      positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ x_pos := by
  sorry

/--
Section 5.1.2 from `docs/Lasso.md`: Reduction of dynamics in the `u ∘ v` case to the `u ∘ u` case.
An informal proof:
For any `x = u ∘ v`, define `u' = (u+v)/2` and `v' = (u-v)/2`.
After augmenting the dimension to `2d` and taking `p = (u', v')`, the
`u ∘ v` dynamics reduce to the `p ∘ p` positive dynamics on the augmented
system.
-/
lemma dln_dynamics_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
  ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε) →
  ∃ u_pos : ℝ → ℝ → EuclideanSpace ℝ (ι ⊕ ι),
    ∀ ε > 0,
      posDlnGradientFlow (augmentedMatrix M) (augmentedVector r) lambda ε
        ((WithLp.equiv 2 _).symm
          (Sum.elim ((1 / 2 : ℝ) • (β + γ)) ((1 / 2 : ℝ) • (β - γ))))
        (u_pos ε) := by
  sorry

end Lasso
