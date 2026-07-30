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

/-- Regularity bridge used between the public statement of Theorem 3.2 and its
scaled-path energy proof.

On `[a,b] ⊂ (0,∞)`, the product `μ ↦ μ x(μ)` is absolutely continuous because
both factors are. Lemma 4.10 says the positive-Lasso minimizer is zero for all
sufficiently small `μ`, so the scaled path is constant near zero; the two
pieces glue on every `[0,b]`. This is the endpoint argument in Sections
4.5--4.6 of <https://arxiv.org/abs/2509.18766>. Mathlib's supported operations
on absolutely continuous functions are documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.
-/
theorem scaledPrimalPath_regular_of_path_regular
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) := by
  sorry

/-- Construct the auxiliary Moore--Penrose/LCP data from the selected positive
Lasso minimizer path.

The KKT conditions for the constrained convex quadratic give the dual slack
`w(μ)` and show that `(μx(μ),w(μ))` solves the parametric LCP. A symmetric PSD
matrix has a PSD Moore--Penrose inverse by diagonalizing it and inverting the
positive eigenvalues; Lemma 4.11 then supplies the regularity package. See
Sections 4.4--4.5 of <https://arxiv.org/abs/2509.18766>, the KKT development in
Boyd--Vandenberghe <https://web.stanford.edu/~boyd/cvxbook/>, and the spectral
construction of the pseudoinverse in <https://arxiv.org/abs/1110.6882>.
-/
theorem exists_dual_certificate_for_positive_path
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∃ Mdagger : Matrix ι ι ℝ, ∃ w : ℝ → EuclideanSpace ℝ ι,
      ParametricLCPDualRegular M Mdagger r lambda w ∧
        ∀ μ, 0 ≤ μ →
          isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ) := by
  sorry

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
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_regular :
      LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  /-
  INFORMAL PROOF. Integrate the uniform-in-`s` delta and energy differential
  inequalities of Section 4.6, use the zero initial energy, and divide by
  `s²`. The constants in Lemmas 4.1--4.11 depend only on the fixed problem
  data and initialization, so one `C` works for every `s > 0`. This is the
  calculation concluding Theorem 3.2 in <https://arxiv.org/abs/2509.18766>;
  the absolute-continuity/FTC step is supported by Mathlib's interval-integral
  API <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.html>.
  -/
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
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  /-
  INFORMAL PROOF. KKT/LCP duality constructs the auxiliary dual solution from
  the selected minimizer path, so it is not a user-supplied unrelated path.
  Multiplication by `μ` transfers local absolute continuity of `x` to `z` away
  from zero; Lemma 4.10 makes `z=0` near zero. Apply
  `positive_path_energy_bound`. See Sections 4.4--4.6 of
  <https://arxiv.org/abs/2509.18766> and the convex KKT framework in
  Boyd--Vandenberghe <https://web.stanford.edu/~boyd/cvxbook/>.
  -/
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
    LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) := by
  /-
  INFORMAL PROOF. KKT gives the unique dual path attached to `x_lasso`.
  Lemma 4.11 controls the range projection of `z`; complementarity expresses
  the scalar kernel contribution in terms of locally Lipschitz quantities.
  Coordinatewise monotonicity turns its increment into the `ℓ¹` norm of the
  full increment, yielding local Lipschitz continuity of `z`, hence absolute
  continuity. Lemma 4.10 supplies `z=0` near the endpoint. See Lemma 4.12 of
  <https://arxiv.org/abs/2509.18766> and Mathlib's implication
  Lipschitz `⇒` absolutely continuous
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.
  -/
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
  /-
  INFORMAL PROOF. Lemma 4.12 supplies the regularity needed by Theorem 3.2.
  A coordinatewise nondecreasing absolutely continuous `z` has nonnegative
  derivative almost everywhere, so `positiveZDownward x_lasso s = 0`.
  The approximate upper bound therefore has zero error term; feasibility of
  the averaged positive trajectory supplies the matching lower bound. See
  Sections 4.6--4.7 of <https://arxiv.org/abs/2509.18766> and the standard
  a.e.-derivative characterization of absolute continuity
  <https://en.wikipedia.org/wiki/Absolute_continuity>.
  -/
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

/-- Local absolute continuity is preserved by the canonical positive/negative
split used in Section 5.

Coordinatewise `max` is Lipschitz, hence composition with an absolutely
continuous scalar path is absolutely continuous; finite products preserve the
property. This is the regularity step in Section 5.2.2 of
<https://arxiv.org/abs/2509.18766>, cross-checked with Mathlib's absolute
continuity API
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.
-/
theorem signedCanonicalSplit_path_regular
    (x : ℝ → EuclideanSpace ℝ ι)
    (hx : LocallyAbsolutelyContinuousOnPositiveCompacts x) :
    LocallyAbsolutelyContinuousOnPositiveCompacts
      (fun μ => signedCanonicalSplit (x μ)) := by
  sorry

/-- A signed coordinate that is monotone in either direction becomes two
nondecreasing coordinates after the positive/negative split.

If `zᵢ` is nondecreasing then `(zᵢ)₊` is nondecreasing and `(zᵢ)₋` is zero or
nonincreasing in the sign convention represented by the split; if `zᵢ` is
nonincreasing the roles reverse. Applied to `z(μ)=μx(μ)`, both coordinates of
the canonical nonnegative representation have no downward variation in the
appropriate signed-path formula. This is exactly the reduction in Section
5.2.1 of <https://arxiv.org/abs/2509.18766>.
-/
theorem signedCanonicalSplit_scaled_monotonicity
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hmin : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x μ))
    (hx : ∀ i,
      MonotoneOn (fun μ => μ * x μ i) (Set.Ioi 0) ∨
        AntitoneOn (fun μ => μ * x μ i) (Set.Ioi 0)) :
    ∀ j : ι ⊕ ι,
      MonotoneOn (fun μ => μ * signedCanonicalSplit (x μ) j) (Set.Ioi 0) := by
  sorry

/-- Difference map `(y_pos, y_neg) ↦ y_pos - y_neg`. -/
noncomputable def splitDifference (y : EuclideanSpace ℝ (ι ⊕ ι)) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => y (Sum.inl i) - y (Sum.inr i))

/-- Coordinatewise complementarity of an arbitrary signed split. -/
def SplitComplementary (y : EuclideanSpace ℝ (ι ⊕ ι)) : Prop :=
  ∀ i : ι, y (Sum.inl i) * y (Sum.inr i) = 0

/-- The signed-to-positive augmentation preserves the standing problem-data
assumptions.

For `y=(y⁺,y⁻)`, the augmented quadratic form is
`⟨y, M̃y⟩ = ⟨y⁺-y⁻, M(y⁺-y⁻)⟩`, hence is nonnegative. If `r=Mq`, then
`(r,-r)=M̃(q,0)`, and the penalty parameter is unchanged. This is the block
calculation in Section 5.1.1 of <https://arxiv.org/abs/2509.18766>, consistent
with the standard PSD characterization by quadratic forms in
Boyd--Vandenberghe <https://web.stanford.edu/~boyd/cvxbook/>.
-/
theorem augmented_problem_data
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (hdata : ProblemData M r lambda) :
    ProblemData (augmentedMatrix M) (augmentedVector r) lambda := by
  sorry

/--
Lemma 5.1(1), inequality part: any nonnegative split gives an augmented positive
objective no smaller than the signed lasso objective of its difference.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(1).
-/
lemma lasso_split_objective_le
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y : EuclideanSpace ℝ (ι ⊕ ι)) (hy : Nonnegative y)
    (hpenalty : 0 ≤ lambda + 1 / μ) :
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
  constructor
  · -- Nonnegative (signedCanonicalSplit x)
    intro j
    cases j <;>
      simp [signedCanonicalSplit, coordinatePositivePart, coordinateNegativePart, euclideanOf]
  · -- lassoObjective equality
    have h_split : splitDifference (signedCanonicalSplit x) = x := by
      ext i
      change max (x i) 0 - max (-x i) 0 = x i
      rcases le_total 0 (x i) with hpos | hneg
      · rw [max_eq_left hpos, max_eq_right (by linarith)]
        linarith
      · rw [max_eq_right hneg, max_eq_left (by linarith)]
        linarith

    have h_norm : ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖ = ‖(WithLp.equiv 1 (ι ⊕ ι → ℝ)).symm (signedCanonicalSplit x)‖ := by
      rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
      change (∑ i, ‖x i‖) = ∑ j, ‖signedCanonicalSplit x j‖
      have h_sum_rhs : (∑ j : ι ⊕ ι, ‖signedCanonicalSplit x j‖) = (∑ i : ι, ‖signedCanonicalSplit x (Sum.inl i)‖) + (∑ i : ι, ‖signedCanonicalSplit x (Sum.inr i)‖) := by
        exact Fintype.sum_sum_type _
      rw [h_sum_rhs, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change ‖x i‖ = ‖max (x i) 0‖ + ‖max (-x i) 0‖
      simp only [Real.norm_eq_abs]
      rcases le_total 0 (x i) with hpos | hneg
      · have hm1 : max (x i) 0 = x i := max_eq_left hpos
        have hm2 : max (-x i) 0 = 0 := max_eq_right (by linarith)
        rw [hm1, hm2, abs_zero, add_zero]
      · have hm1 : max (x i) 0 = 0 := max_eq_right hneg
        have hm2 : max (-x i) 0 = -x i := max_eq_left (by linarith)
        rw [hm1, hm2, abs_zero, zero_add, abs_neg]

    have h_quad : quadraticLoss M r x =
        quadraticLoss (augmentedMatrix M) (augmentedVector r) (signedCanonicalSplit x) := by
      /-
      Expand the block matrix `[M,-M;-M,M]` and vector `[r;-r]`.
      Both expressions reduce to the quadratic loss at `x₊-x₋=x`.
      This is Lemma 5.1 of <https://arxiv.org/abs/2509.18766>.
      -/
      sorry

    rw [positiveLassoObjective, lassoObjective, lassoObjective, h_norm, h_quad]

/--
Lemma 5.1(2): a signed lasso minimizer gives an augmented positive-lasso
minimizer via the canonical split.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(2).
-/
lemma lasso_minimizer_to_augmented_positive_minimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι)
    (hpenalty : 0 ≤ lambda + 1 / μ)
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
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hpenalty : 0 ≤ lambda + 1 / μ) :
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
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hdata : ProblemData M r lambda)
    (hβγ : ∀ i, β i ≠ γ i ∧ β i ≠ -γ i)
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
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
    (h_monotone : ∀ i,
      MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0) ∨
        AntitoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
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
