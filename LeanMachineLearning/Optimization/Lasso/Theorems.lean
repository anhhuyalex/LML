/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import LeanMachineLearning.Optimization.Lasso.LCP
public import LeanMachineLearning.Optimization.Lasso.MirrorFlow
public import LeanMachineLearning.Optimization.Lasso.Definitions
public import LeanMachineLearning.Optimization.Lasso.Bounds.Delta
public import LeanMachineLearning.Optimization.Lasso.Bounds.Energy
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





/--
Section 4.6 final estimate: the `Δε` control implies the positive-lasso
objective suboptimality bound of Theorem 3.2.

Informal proof reference: `docs/Lasso.md`, Section 4.6.

Informal Proof Outline:
1. Use `positiveLassoObjective_eq_energy` to rewrite the objective gap
   `Lasso(xε) - Lasso(x)` as `1/s^2 * E^\varepsilon(s)`.
2. Apply `positive_energy_differential_inequality` to bound the derivative of `E^\varepsilon(\tau)`.
3. Integrate this bound from `τ = 0` to `τ = s`.
4. Use `initial_positive_energy_zero` to show that the integral evaluates
   exactly to `E^\varepsilon(s)`.
5. Substitute the integrated `Δ^\varepsilon(τ)` bound from `positive_path_delta_bound`.
6. Conclude the limit bound for `E^\varepsilon(s) / s^2`, which matches
   `suboptimalityGap` as `ε → 0`.
-/
theorem positive_path_energy_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  -- Obtain the differential inequality bound `C_diff`
  obtain ⟨C_diff, hC_diff_pos, h_diff_bound⟩ := positive_energy_differential_inequality
    M Mdagger r lambda β s hs u hdata hβ hu x_lasso hx_lasso w hdual h_regular
  -- Obtain the delta bound `C_delta`
  obtain ⟨C_delta, hC_delta_pos, h_delta_bound⟩ := positive_path_delta_bound
    M r lambda β s hs u hdata hβ hu x_lasso hx_lasso h_regular
  -- Let C be a combination of C_diff, C_delta, and geometric factors
  let C := C_diff * Real.sqrt (2 * C_delta) + C_diff
  use C
  constructor
  · -- sorry: Need to prove C > 0
    sorry
  · intro δ hδ
    -- sorry: Filter over ε > 0 for both bounds
    -- sorry: Integrate `h_diff_bound` from 0 to s using `bound_of_deriv_bound`
    -- sorry: Use `initial_positive_energy_zero` to remove `E^\varepsilon(0)`
    -- sorry: Substitute `h_delta_bound` into the integrated inequality
    -- sorry: Use `positiveLassoObjective_eq_energy` to connect the energy
    -- `E^\varepsilon(s)` to the objective
    -- sorry: Simplify to match `C * suboptimalityGap + δ`
    sorry

/-! ## Positive-lasso main theorems -/

/--
Theorem 3.2: an approximate connection to the positive lasso minimum in the
general case.

Informal proof reference: `docs/Lasso.md`, Section 4.6.  This theorem is now
placed after the delta and energy estimates that prove it.
-/
theorem pos_lasso_connection_approx
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  -- Proof sketch (Section 4.6 from `docs/Lasso.md`):
  -- By the energy inequality `positiveLassoObjective_eq_energy`, the objective
  -- is bounded by the energy functional. The energy decreases along the gradient
  -- flow trajectory and its limit is bounded by `posLassoMin + C * suboptimalityGap`.
  -- Finally, applying the delta bound `h_delta_bound` gives the desired uniform approximation.
  --
  -- This formalization skeleton relies on `positive_path_energy_bound`, which
  -- integrates the differential inequality. We invoke it directly here.
  exact positive_path_energy_bound M Mdagger r lambda β s hs u hdata hβ hu x_lasso hx_lasso w hdual h_regular

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
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso) := by
  have h_lip_dual := hdual.locally_lipschitz
  have h_lip_span : LocallyLipschitzOnCompacts (fun μ => matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ))) := by
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.7, Lemma 4.12):
    By Lemma 4.11 (`parametric_lcp_dual_regular`), the dual path `w` is locally Lipschitz.
    Using the LCP equation `1/(1+μλ) w(μ) = -μ/(1+μλ) r + 1 + M(1/(1+μλ) z(μ))`,
    the projection of `z(μ)` onto `Span M` is an affine function of `w(μ)` and thus
    also locally Lipschitz.
    -/
    sorry
  have h_lip_ker : LocallyLipschitzOnCompacts (fun μ => scaledPrimalPath x_lasso μ - matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ))) := by
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.7, Lemma 4.12):
    By complementarity, `⟨w(μ), z(μ)⟩ = 0`. Since `1/(1+μλ) w(μ) ∈ 1 + Span M`,
    we can expand this inner product to bound the kernel projection.
    The sum `⟨1, P_ker z(μ)⟩` can be expressed in terms of `w` and `P_span z`,
    which are both locally Lipschitz, making the L1 norm of the kernel projection locally Lipschitz.
    -/
    sorry
  refine ⟨fun a b ha hab => ?_⟩
  rcases h_lip_span.lipschitz_on_Icc a b ha hab with ⟨K1, hK1_nonneg, hK1⟩
  rcases h_lip_ker.lipschitz_on_Icc a b ha hab with ⟨K2, hK2_nonneg, hK2⟩
  use K1 + K2
  constructor
  · exact add_nonneg hK1_nonneg hK2_nonneg
  · intro μ hμ ν hν
    have h_eq1 : scaledPrimalPath x_lasso μ = (matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ))) + (scaledPrimalPath x_lasso μ - matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ))) := by
      abel
    have h_eq2 : scaledPrimalPath x_lasso ν = (matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν))) + (scaledPrimalPath x_lasso ν - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν))) := by
      abel
    rw [h_eq1, h_eq2]
    have h_sub : (matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ)) + (scaledPrimalPath x_lasso μ - matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ)))) - 
                 (matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν)) + (scaledPrimalPath x_lasso ν - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν)))) =
                 (matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ)) - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν))) + 
                 ((scaledPrimalPath x_lasso μ - matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ))) - (scaledPrimalPath x_lasso ν - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν)))) := by
      abel
    rw [h_sub]
    calc
      ‖(matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ)) - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν))) + ((scaledPrimalPath x_lasso μ - matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ))) - (scaledPrimalPath x_lasso ν - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν))))‖
        ≤ ‖matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ)) - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν))‖ + ‖(scaledPrimalPath x_lasso μ - matVec M (matVec Mdagger (scaledPrimalPath x_lasso μ))) - (scaledPrimalPath x_lasso ν - matVec M (matVec Mdagger (scaledPrimalPath x_lasso ν)))‖ := norm_add_le _ _
      _ ≤ K1 * |μ - ν| + K2 * |μ - ν| := add_le_add (hK1 μ hμ ν hν) (hK2 μ hμ ν hν)
      _ = (K1 + K2) * |μ - ν| := by ring

/--
Theorem 3.1: under monotonicity, the positive average trajectory exactly
connects to the positive lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 4.7.  Unlike the earlier
skeleton, this statement no longer assumes compact-interval regularity as an
extra hypothesis; that regularity is supplied by `monotone_positive_path_regular`.
-/
theorem pos_lasso_connection_monotone
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        positiveLassoObjective M r lambda s
          (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (posLassoMin M r lambda s)) := by
  have h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso) :=
    monotone_positive_path_regular M Mdagger r lambda x_lasso w hdata hx_lasso hdual h_monotone
  have h_approx := pos_lasso_connection_approx M Mdagger r lambda β s hs u hdata hβ hu x_lasso hx_lasso w hdual h_regular
  have h_zdown_zero : positiveZDownward x_lasso s = 0 := by
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.7):
    The downward variation `positiveZDownward` is defined as the integral of the negative
    part of the derivative of the scaled path `z(μ)`. Since `z(μ)` is assumed to be monotone
    non-decreasing coordinate-wise, its derivative is almost everywhere non-negative.
    Thus, the negative part is zero, making the integral zero.
    -/
    sorry
  rcases h_approx with ⟨C, hC_pos, h_bound⟩
  have h_sub_zero : suboptimalityGap lambda s (positiveZDownward x_lasso s) = 0 := by
    rw [h_zdown_zero, suboptimalityGap]
    simp
  
  have h_traj_nonneg : ∀ ε > 0, Nonnegative (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)) := by
    /-
    INFORMAL PROOF: The trajectory `u ε` evolves in the positive quadrant,
    so its time-average `posAverageTrajectory` is also non-negative.
    -/
    sorry

  have h_pos_min : ∀ ε > 0, posLassoMin M r lambda s ≤ positiveLassoObjective M r lambda s (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)) := by
    intro ε hε
    have _h1 := h_traj_nonneg ε hε
    /-
    INFORMAL PROOF: `posLassoMin` is the infimum of the objective over all non-negative vectors.
    Since the average trajectory is non-negative, its objective value bounds the infimum from above.
    -/
    sorry

  rw [tendsto_order]
  constructor
  · intro a ha
    have h_eventual : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, a < posLassoMin M r lambda s := by
      filter_upwards [] with ε
      exact ha
    filter_upwards [h_eventual, eventually_mem_nhdsWithin] with ε h_a h_pos
    calc
      a < posLassoMin M r lambda s := h_a
      _ ≤ positiveLassoObjective M r lambda s (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)) := h_pos_min ε h_pos
  · intro b hb
    have h_diff : 0 < (b - posLassoMin M r lambda s) / 2 := half_pos (sub_pos.mpr hb)
    have h_bound_eventual := h_bound ((b - posLassoMin M r lambda s) / 2) h_diff
    filter_upwards [h_bound_eventual] with ε h_le
    calc
      positiveLassoObjective M r lambda s (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
        ≤ posLassoMin M r lambda s + C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + (b - posLassoMin M r lambda s) / 2 := h_le
      _ = posLassoMin M r lambda s + 0 + (b - posLassoMin M r lambda s) / 2 := by rw [h_sub_zero, mul_zero]
      _ = (posLassoMin M r lambda s + b) / 2 := by linarith
      _ < b := by linarith

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
  -- Proof sketch (Section 5.1.1, Lemma 5.1(1)):
  -- The signed lasso objective evaluates the L1 norm |x|. The augmented positive objective
  -- evaluates the sum of the positive and negative components (y_pos + y_neg).
  -- By the triangle inequality, |y_pos - y_neg| <= y_pos + y_neg for any nonnegative components.
  -- This makes the signed objective always less than or equal to the augmented positive objective.
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
  -- Proof sketch (Section 5.1.1, Lemma 5.1(1)):
  -- Equality in the triangle inequality |y_pos - y_neg| <= y_pos + y_neg holds if and only if
  -- y_pos and y_neg have disjoint support. Since they are nonnegative, this is equivalent
  -- to the complementarity condition y_pos * y_neg = 0 for all coordinates.
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
  -- Proof sketch (Section 5.1.1):
  -- The canonical split decomposes x into x_+ and x_-, which are nonnegative by definition.
  -- Since they are defined via max(x, 0) and max(-x, 0), they are complementary (x_+ * x_- = 0).
  -- By `lasso_split_objective_eq_iff_complementary`, the objectives are therefore equal.
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
  -- Proof sketch (Section 5.1.1, Lemma 5.1(2)):
  -- If x minimizes the signed lasso objective, its canonical split minimizes the augmented
  -- positive objective. Any other positive split y can be mapped to a signed vector y_pos - y_neg,
  -- whose signed objective is ≤ the positive objective of y. Since x is the global minimum,
  -- the canonical split of x must achieve the absolute minimum of the augmented problem.
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
  -- Proof sketch (Section 5.1.1, Lemma 5.1(3)):
  -- Follows directly from `lasso_minimizer_to_augmented_positive_minimizer` and
  -- `lasso_objective_reduction`. The minimum values of both problems coincide.
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
  -- Proof sketch (Section 5.1.2):
  -- Algebraic identity: p_pos = (u+v)/2 and p_neg = (u-v)/2.
  -- Therefore, p_pos^2 - p_neg^2 = ((u+v)^2 - (u-v)^2) / 4 = 4uv / 4 = uv.
  -- This exactly matches the effective parameter `u ∘ v`.
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
  -- Proof sketch (Section 5.2):
  -- This follows by integrating the pointwise identity
  -- `signed_effective_eq_split_positive_effective` over time. The time scaling factor of two
  -- accounts for the chain rule in the squared parameterization.
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
  -- Proof sketch (Section 5.1.2):
  -- By differentiating the positive and negative parts of the canonical split, the dynamics
  -- of u and v completely decouple into the standard u ∘ u positive dynamics on the
  -- augmented (doubled) dimension system.
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
  -- Proof sketch (Section 5.2):
  -- The augmented initialization is (u+v)/2 and (u-v)/2.
  -- These components are non-zero if and only if (u+v) ≠ 0 and (u-v) ≠ 0.
  -- This is equivalent to u ≠ -v and u ≠ v.
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
