# Lasso statement audit and proof API

This note records the statement-level audit of
`LeanMachineLearning/Optimization/Lasso` against `docs/Lasso.md` and
`blueprint/src/chapters/lasso.tex`. It intentionally does not claim that the
remaining `sorry` proofs are complete. Its purpose is to ensure those proof
obligations are the right mathematical propositions.

## Outcome

The public statements now match the source quantifiers and hypotheses:

- Theorems 2.2 and 3.2 choose one constant before quantifying over every
  `s > 0`; the earlier declarations incorrectly allowed a different constant
  for each fixed `s`.
- Their regularity hypothesis is local absolute continuity of `x` on compact
  subsets of `(0,∞)`, not local Lipschitz continuity of `z(μ)=μx(μ)`.
- Theorems 3.1 and 3.2 no longer ask callers for an arbitrary pseudoinverse and
  an unrelated dual path. `exists_dual_certificate_for_positive_path` records
  that these objects must be constructed from the selected minimizer path.
- Signed coordinatewise monotonicity means that each coordinate may be either
  nondecreasing or nonincreasing. The earlier statement forced all coordinates
  to be nondecreasing.
- The inequality and minimizer-transfer parts of Lemma 5.1 now assume
  `0 ≤ λ + 1/μ`. Multiplying the triangle inequality by a negative number
  reverses it, so omitting this hypothesis made the declarations false.
- Lemmas 4.2, 4.7, and 4.10 now have declarations for the consequences actually
  stated in the paper: the uniform tilted-loss bound, the unique nonnegative
  minimum-norm solution and its bound, and the explicit small-`μ` LCP solution
  with the `ℓ∞` threshold and unscaled conclusion.
- Lemma 4.5 now puts its constant outside the quantifier over `α`; only `ε₀`
  may depend on `α`.
- Lemma 4.4 and Proposition 4.1 derive nonvanishing of the effective coordinates
  from the ODE and nonzero initialization rather than exposing it as an extra
  assumption.
- `augmented_problem_data` supplies the missing bridge proving that the signed
  block augmentation preserves the standing PSD/range/nonnegative-penalty
  assumptions.

The source mathematics is the paper *Diagonal Linear Networks and the Lasso
Regularization Path* [arXiv:2509.18766](https://arxiv.org/abs/2509.18766).
Absolute continuity is represented by Mathlib's actual
[`AbsolutelyContinuousOnInterval`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html),
which also confirms that Lipschitz continuity implies absolute continuity but
is a strictly stronger assumption. The KKT/LCP reductions were cross-checked
against [Boyd and Vandenberghe, *Convex
Optimization*](https://web.stanford.edu/~boyd/cvxbook/) and [Cottle, Pang, and
Stone, *The Linear Complementarity
Problem*](https://epubs.siam.org/doi/book/10.1137/1.9780898719000). The
pseudoinverse contract follows the spectral construction summarized in
[Barata and Hussein](https://arxiv.org/abs/1110.6882).

## Informal proof map

1. **Positive approximate theorem.** KKT conditions turn the selected positive
   Lasso minimizer into a parametric LCP solution. Lemma 4.11 controls its dual
   path. Absolute continuity of `x` makes `μx(μ)` absolutely continuous away
   from zero, while Lemma 4.10 makes it identically zero near zero. Integrating
   the delta and energy differential inequalities gives a constant depending
   only on the fixed data, uniformly for every `s`. This is the calculation in
   Sections 4.4--4.6 of the [source
   paper](https://arxiv.org/abs/2509.18766); the formal integration target is
   Mathlib's [absolutely-continuous interval-integral
   API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.html).

2. **Positive monotone theorem.** Lemmas 4.10--4.12 give local absolute
   continuity of the scaled path. A nondecreasing absolutely continuous scalar
   function has nonnegative derivative almost everywhere, so its downward
   variation vanishes. The approximate upper bound becomes exact, while
   feasibility gives the lower bound. See Section 4.7 of the [source
   paper](https://arxiv.org/abs/2509.18766); the a.e.-derivative fact is also
   part of Mathlib's [absolute-continuity
   API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html).

3. **Signed reduction.** The block quadratic form at `(y⁺,y⁻)` equals the
   original form at `y⁺-y⁻`, and nonnegativity gives
   `|y⁺-y⁻| ≤ y⁺+y⁻` coordinatewise. A nonnegative penalty preserves that
   inequality. For the canonical split equality holds. KKT-free comparison of
   arbitrary competitors then transfers minimizers and minimum values. This is
   Lemma 5.1 of the [source paper](https://arxiv.org/abs/2509.18766).

4. **Small-parameter LCP.** The exact `ℓ∞` threshold makes every coordinate of
   `q(μ)=(1+μλ)1-μr` positive. `(z,w)=(0,q(μ))` solves the LCP. For any other
   solution, PSD and complementarity imply `⟨q,z⟩≤0`; strict positivity of `q`
   and `z≥0` force `z=0`, then the affine equation forces `w=q`. Scaling by
   positive `μ` gives the unscaled LCP solution. This is Lemma 4.10 of the
   [source paper](https://arxiv.org/abs/2509.18766), using the standard LCP
   conventions from [Cottle--Pang--Stone](https://epubs.siam.org/doi/book/10.1137/1.9780898719000).

5. **Nonnegative minimum-norm fiber.** Existence follows from coercivity of the
   Euclidean norm on a nonempty closed fiber; strict convexity gives uniqueness.
   Conic Carathéodory reduces a feasible representation to a linearly
   independent active subfamily, whose inverse bound supplies `C‖y‖`; the
   argmin is no larger. This is Lemma 4.7 of the [source
   paper](https://arxiv.org/abs/2509.18766), cross-checked with [Bertsekas' MIT
   convex-analysis slides](https://web.mit.edu/dimitrib/OldFiles/www/Convex_Slides.pdf).

## Ranked reusable results

The ranking reflects likely usefulness when completing the remaining proofs.

1. `ProblemData`, `IsLassoMinimizer`, `IsPositiveLassoMinimizer` —
   `LeanMachineLearning/Optimization/Lasso/Basic.lean`. These are the standing
   assumptions and minimizer predicates; inspect them before unfolding any
   objective.
2. `pos_lasso_is_lcp`, `isParametricLCP`,
   `parametric_lcp_eq_iff_of_small_mu`, `lcp_eq_iff_of_small_mu` —
   `LeanMachineLearning/Optimization/Lasso/LCP.lean`. This is the main
   minimizer-to-complementarity bridge and the exact endpoint API.
3. `LocallyAbsolutelyContinuousOnPositiveCompacts`,
   `LocallyAbsolutelyContinuousOnNonnegativeCompacts`, and
   `LocallyLipschitzOnCompacts.absolutelyContinuous` — `LCP.lean`. Use these
   instead of inventing a Lipschitz assumption in a public theorem.
4. `IsPSDRangeInverse`, `ParametricLCPDualRegular`, and
   `parametric_lcp_dual_regular` — `LCP.lean`. These package the precise laws
   required of the pseudoinverse and the conclusions of Lemma 4.11.
5. `exists_dual_certificate_for_positive_path` and
   `scaledPrimalPath_regular_of_path_regular` — `Theorems.lean`. These isolate
   the two bridges from the paper-level hypotheses to the internal energy API.
6. `posEffectiveParameter_ne_zero`,
   `bregman_projection_characterization`, and
   `pos_trajectory_uniform_bound` — `MirrorFlow.lean`. The positivity invariant
   is derived once and reused rather than repeated at every call site.
7. `nonnegative_solution_norm_bound`,
   `IsNonnegativeMinNormSolution`, and
   `nonnegative_minNorm_solution_norm_bound` — `LCP.lean`. The first is a useful
   feasible-witness bound; the latter two express the faithful argmin theorem.
8. `tiltedLoss_antitone_along_pos_flow` and
   `tiltedLoss_uniform_upper_bound` — `MirrorFlow.lean`. Together they cover
   both clauses of Lemma 4.2.
9. `bregman_projection_fiber_norm_bound` — `MirrorFlow.lean`. Its quantifier
   order enforces `C=C(d,M)` and `ε₀=ε₀(α)`.
10. `augmented_problem_data`, `lasso_objective_reduction`,
    `lasso_split_objective_le`, and
    `signedCanonicalSplit_scaled_monotonicity` — `Theorems.lean`. These are the
    reusable signed-to-positive reduction layer.
11. `LipschitzOnWith.absolutelyContinuousOnInterval` and
    `AbsolutelyContinuousOnInterval.ae_differentiableAt` —
    `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`.
12. `intervalIntegral.integral_deriv_eq_sub` and related FTC results —
    `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`.
13. `PiLp.norm_apply_le`, `PiLp.norm_toLp`, and `WithLp.equiv` —
    `.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`. In particular,
    instantiate `p=∞` for Lemma 4.10 rather than silently using the Euclidean norm.
14. `IsPositiveSemidefinite.get_nonneg`, `matVec_sub`, and the local augmented
    block identities — Mathlib's matrix API plus `Basic.lean`. Prefer these
    checked names over guessed matrix lemmas.

## Lessons-learned diagnosis

The earlier statements violated the following concrete rules in
`docs/lessons_learned.md`:

- **Rule 1 (verify names and signatures)** and the corresponding warnings in
  `docs/hallucinated_mathlib.md`: the formalization described a pseudoinverse
  without a checked Mathlib object or laws and used a home-grown Lipschitz
  surrogate instead of inspecting Mathlib's absolute-continuity API.
- **Rule 3 (search for the exact pattern)**: the `PiLp ∞` norm and
  `AbsolutelyContinuousOnInterval` APIs were already present in `.lake/packages`
  but were not used.
- **Rules 7 and 19 (modularize and extract API)**: nonvanishing, augmented
  `ProblemData`, selected-path duality, and regularity conversion were left as
  repeated informal side conditions rather than named bridges.
- **Rule 18 (never hallucinate mathematical bounds)**: moving `s` before `∃ C`,
  moving `α` before the Lemma 4.5 constant, replacing `ℓ∞` by `ℓ²`, and dropping
  the penalty sign all changed mathematical claims, not merely Lean syntax.
- **The Lasso-specific `IsMinOn` lesson**: `IsMinOn f S x` alone does not prove
  `x ∈ S`. `IsNonnegativeMinNormSolution` explicitly includes fiber membership.

The corrected workflow complies with those lessons by checking every imported
name in the current environment, separating paper-level statements from
internal stronger estimates, adding small named bridges, preserving exact
quantifier order and norm choices, and compiling each dependency before the
next layer. No linter option is weakened.
