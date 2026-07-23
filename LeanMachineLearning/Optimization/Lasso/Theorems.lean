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

/-!
# Theorems on the Lasso Regularization Path

This file states the main theorem layer for the lasso regularization path
formalization.  Declarations are ordered by proof dependency:

1. path quantities;
2. Section 4.6 positive-path estimates;
3. positive approximate and monotone theorems;
4. Section 5 signed-to-positive reductions;
5. signed approximate and monotone theorems.

This topological order is intentional.  In particular, signed theorems appear
after `lasso_objective_reduction` and `dln_dynamics_reduction`, because their
informal proofs depend on those reductions.
-/

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

/-- Backwards-compatible alias for the positive-lasso deviation. -/
noncomputable def z_downward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) : ℝ :=
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

/-! ## Section 4.6: positive-path estimate chain -/

/--
Section 4.6, integrated mirror-flow identity in rescaled time.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.13).  Integrate
`d wᵋ / ds = M xᵋ - r + λ 𝟙` from `0` to `s`, using the corrected rescaled
integrated trajectory API.
-/
theorem positive_integrated_mirror_equation
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (β : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε β u) (s : ℝ) :
    posRescaledMirrorVariable ε u s =
      posRescaledMirrorVariable ε u 0 - s • r +
        matVec M (posIntegratedTrajectoryRescaled ε u s) + (s * lambda) • ones := by
  sorry

/--
Section 4.6, differential inequality behind Eq. (4.15).

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.14).  Differentiate
`Δᵋ`, substitute the parametric LCP equation and the integrated mirror equation,
then bound the complementarity-defect terms using the uniform trajectory bound.
-/
theorem positive_delta_differential_inequality
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        deriv
          (fun σ =>
            pathDelta M
              (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ) τ
        ≤ C *
          (1 / Real.log (1 / ε) *
              (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  sorry

/--
Section 4.6, Eq. (4.15), with the full finite-`ε` dependence.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.15).
-/
theorem positive_path_delta_bound_full
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
      ≤ C *
          (deltaFullError ε s
            (positiveZUpward x_lasso s) (positiveZDownward x_lasso s) + δ) := by
  sorry

/--
Coarser version of Eq. (4.15) after absorbing the vanishing finite-`ε` term into
an arbitrary eventual `δ`.

Informal proof reference: `docs/Lasso.md`, Section 4.6.
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
Section 4.6 energy differential inequality for
`Eᵋ(s)=<w(s),zᵋ(s)-z(s)>+Δᵋ(s)`.

Informal proof reference: `docs/Lasso.md`, Section 4.6, after Eq. (4.15).
The derivative of the scaled dual path is controlled by Lemma 4.11.
-/
theorem positive_energy_differential_inequality
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (w z zε : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w) :
    ∀ s : ℝ,
      deriv
        (fun τ =>
          (1 / (1 + τ * lambda)) *
            (inner ℝ (w τ) (zε τ - z τ) + pathDelta M zε z τ)) s
      ≤ pseudoInverseSeminorm Mdagger r * Real.sqrt (2 * pathDelta M zε z s) := by
  sorry

/--
Section 4.6 final estimate: the `Δε` control implies the positive-lasso
objective suboptimality bound of Theorem 3.2.

Informal proof reference: `docs/Lasso.md`, Section 4.6.
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

/-! ## Positive-lasso main theorems -/

/--
Theorem 3.2: an approximate connection to the positive lasso minimum in the
general case.

Informal proof reference: `docs/Lasso.md`, Section 4.6.  This theorem is now
placed after the delta and energy estimates that prove it.
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
Theorem 3.1: under monotonicity, the positive average trajectory exactly
connects to the positive lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 4.7.  Unlike the earlier
skeleton, this statement no longer assumes compact-interval regularity as an
extra hypothesis; that regularity is supplied by `monotone_positive_path_regular`.
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
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        positiveLassoObjective M r lambda s
          (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (posLassoMin M r lambda s)) := by
  sorry

/-! ## Section 5: signed-to-positive reductions -/

/-- Positive part of a coordinate vector. -/
noncomputable def coordinatePositivePart (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => max (x i) 0)

/-- Negative part of a coordinate vector, as a nonnegative vector. -/
noncomputable def coordinateNegativePart (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => max (-(x i)) 0)

/-- Canonical signed-to-positive split `x ↦ (x_+, x_-)`. -/
noncomputable def signedCanonicalSplit (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm
    (Sum.elim (coordinatePositivePart x) (coordinateNegativePart x))

/-- Difference map `(y_pos, y_neg) ↦ y_pos - y_neg`. -/
noncomputable def splitDifference (y : EuclideanSpace ℝ (ι ⊕ ι)) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => y (Sum.inl i) - y (Sum.inr i))

/-- Coordinatewise complementarity of an arbitrary signed split. -/
def SplitComplementary (y : EuclideanSpace ℝ (ι ⊕ ι)) : Prop :=
  ∀ i : ι, y (Sum.inl i) * y (Sum.inr i) = 0

/--
Lemma 5.1(1), inequality part: any nonnegative split gives an augmented positive
objective no smaller than the signed lasso objective of its difference.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(1).
-/
lemma lasso_split_objective_le
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y : EuclideanSpace ℝ (ι ⊕ ι)) (hy : Nonnegative y) :
    lassoObjective M r lambda μ (splitDifference y) ≤
      positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ y := by
  sorry

/--
Lemma 5.1(1), equality criterion: equality holds exactly for complementary
positive and negative parts.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(1).
-/
lemma lasso_split_objective_eq_iff_complementary
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y : EuclideanSpace ℝ (ι ⊕ ι)) (hy : Nonnegative y)
    (hpenalty : 0 < lambda + 1 / μ) :
    lassoObjective M r lambda μ (splitDifference y) =
        positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ y ↔
      SplitComplementary y := by
  sorry

/--
Canonical objective equality for the split `x = x_+ - x_-`.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1.
-/
lemma lasso_objective_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) :
    Nonnegative (signedCanonicalSplit x) ∧
      lassoObjective M r lambda μ x =
        positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ
          (signedCanonicalSplit x) := by
  sorry

/--
Lemma 5.1(2): a signed lasso minimizer gives an augmented positive-lasso
minimizer via the canonical split.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(2).
-/
lemma lasso_minimizer_to_augmented_positive_minimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι)
    (hx : IsLassoMinimizer M r lambda μ x) :
    IsPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ
      (signedCanonicalSplit x) := by
  sorry

/--
Lemma 5.1(3): equality of the signed lasso minimum and the augmented positive
lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(3).
-/
lemma lasso_min_eq_augmented_pos_lasso_min
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    lassoMin M r lambda μ =
      posLassoMin (augmentedMatrix M) (augmentedVector r) lambda μ := by
  sorry

/-- Initial positive weights associated to signed initialization vectors. -/
noncomputable def signedToPositiveInitialization
    (β γ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm
    (Sum.elim ((1 / 2 : ℝ) • (β + γ)) ((1 / 2 : ℝ) • (β - γ)))

/--
The pointwise change of variables
`p_pos=(u+v)/2`, `p_neg=(u-v)/2`.
-/
noncomputable def signedToPositiveWeights
    (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    EuclideanSpace ℝ (ι ⊕ ι) :=
  let uv := WithLp.equiv 2 _ state
  (WithLp.equiv 2 _).symm
    (Sum.elim ((1 / 2 : ℝ) • (uv.1 + uv.2)) ((1 / 2 : ℝ) • (uv.1 - uv.2)))

/--
Algebraic identity behind Section 5.1.2:
`u ∘ v = p_pos^2 - p_neg^2`.

Informal proof reference: `docs/Lasso.md`, Section 5.1.2.
-/
lemma signed_effective_eq_split_positive_effective
    (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    effectiveParameter (fun _ => state) 0 =
      splitDifference (coordinateSquare (signedToPositiveWeights state)) := by
  sorry

/--
Time-averaged version of the signed-to-positive effective-parameter identity.

Informal proof reference: `docs/Lasso.md`, Section 5.2.
-/
lemma signed_average_eq_split_positive_average
    (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (t : ℝ) :
    averageTrajectory w t =
      splitDifference
        (posAverageTrajectory
          (fun τ => signedToPositiveWeights (w (2 * τ))) ((1 / 2 : ℝ) * t)) := by
  sorry

/--
Section 5.1.2: reduction of dynamics in the `u ∘ v` case to the `u ∘ u` case.

Informal proof reference: `docs/Lasso.md`, Section 5.1.2.  The positive
trajectory is explicitly `τ ↦ signedToPositiveWeights (wᵋ(2τ))`.
-/
lemma dln_dynamics_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε) →
      posDlnGradientFlow (augmentedMatrix M) (augmentedVector r) lambda ε
        (signedToPositiveInitialization β γ)
        (fun τ => signedToPositiveWeights ((w ε) (2 * τ))) := by
  sorry

/--
The nondegeneracy condition on signed initialization is exactly nonzero
coordinates for the augmented positive initialization.

Informal proof reference: `docs/Lasso.md`, Section 5.2.
-/
lemma signed_initialization_nondegenerate_iff
    (β γ : EuclideanSpace ℝ ι) :
    NonzeroCoordinates (signedToPositiveInitialization β γ) ↔
      ∀ i, β i ≠ γ i ∧ β i ≠ -γ i := by
  sorry

/--
The signed-lasso deviation from monotonicity used in Theorem 2.2.
This matches Eq. (2.3): it applies the negative-variation penalty separately to
the positive and negative parts of `z_i(μ) = μ x_i(μ)`.
-/
noncomputable def signedZDownward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) :
    ℝ :=
  ∑ i,
    ∫ u in (0 : ℝ)..μ,
      (1 + u) *
        (max 0 (-deriv (fun u' => max (u' * x_lasso u' i) 0) u) +
          max 0 (-deriv (fun u' => max (-(u' * x_lasso u' i)) 0) u))

/-! ## Signed-lasso main theorems -/

/--
Theorem 2.2: an approximate connection to the lasso minimum in the general case.

Informal proof reference: `docs/Lasso.md`, Section 5.2.2.  This declaration now
appears after both `dln_dynamics_reduction` and `lasso_objective_reduction`,
matching the proof sketch.
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
Theorem 2.1: under monotonicity, the signed average trajectory exactly connects
to the lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 5.2.1.  The earlier skeleton
required an extra `h_regular`; this version follows the paper-level theorem
statement and leaves regularity to the positive monotone theorem plus reductions.
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

end Lasso

end
