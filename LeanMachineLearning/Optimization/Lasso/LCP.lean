/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
import LeanMachineLearning.Optimization.Lasso.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Linear Complementarity Problem (LCP) Formulations for Lasso

This file formalizes the primal-dual LCP formulations of the Lasso regularization path.
-/

namespace Lasso

variable {ι : Type*} [Fintype ι]

/-- The affine term `q = -r + (lambda + 1 / μ) * 1` in the positive-lasso LCP. -/
noncomputable def lcpQ (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => -r i + lambda + 1 / μ)

/-- The affine term `q(μ) = -μ r + (1 + μ lambda) * 1` in the parametric LCP. -/
noncomputable def parametricLcpQ (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => -μ * r i + 1 + μ * lambda)

/--
The Linear Complementarity Problem (LCP) associated with the positive lasso.
For a given `x`, it requires finding `v` such that `v = q + Mx`,
`v ≥ 0`, `x ≥ 0`, and `⟨v, x⟩ = 0`.
-/
def isLCP (M : Matrix ι ι ℝ) (q x v : EuclideanSpace ℝ ι) : Prop :=
  v = q + matVec M x ∧
  Nonnegative v ∧ Nonnegative x ∧ inner ℝ v x = (0 : ℝ)

/-- Coordinatewise derivative of a vector-valued path. -/
noncomputable def coordinateDeriv (f : ℝ → EuclideanSpace ℝ ι) (t : ℝ) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => deriv (fun u => f u i) t)

/-- Local Lipschitz continuity on every compact interval `[a,b]`. -/
structure LocallyLipschitzOnCompacts (f : ℝ → EuclideanSpace ℝ ι) : Prop where
  lipschitz_on_Icc :
    ∀ a b : ℝ, a ≤ b →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ μ ∈ Set.Icc a b, ∀ ν ∈ Set.Icc a b,
          ‖f μ - f ν‖ ≤ K * |μ - ν|

/-- The scaled dual path `w(μ) / (1 + μ lambda)` from Lemma 4.11. -/
noncomputable def scaledDualPath (lambda : ℝ) (w : ℝ → EuclideanSpace ℝ ι) :
    ℝ → EuclideanSpace ℝ ι :=
  fun μ => (1 / (1 + μ * lambda)) • w μ

/--
The seminorm induced by an explicit matrix used as `M†`.

This avoids hallucinating a Mathlib Moore-Penrose pseudoinverse API.  Once the
project has a canonical pseudoinverse object for finite-dimensional matrices,
the parameter `Mdagger` should be instantiated with that matrix.
-/
noncomputable def pseudoInverseSeminorm
    (Mdagger : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.sqrt (max 0 (inner ℝ x (matVec Mdagger x)))

/--
Regularity package for the unique dual solution of the parametric LCP.
This abstracts the three conclusions of Lemma 4.11: absolute continuity
(represented here by local Lipschitz continuity), derivative in `Span M`, and a
uniform derivative bound in the `M†` seminorm used in `docs/Lasso.md`.
-/
structure ParametricLCPDualRegular
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (w : ℝ → EuclideanSpace ℝ ι) : Prop where
  locally_lipschitz : LocallyLipschitzOnCompacts w
  scaled_derivative_in_span :
    ∀ μ : ℝ, InMatrixSpan M (coordinateDeriv (scaledDualPath lambda w) μ)
  scaled_derivative_bound :
    ∀ μ : ℝ,
      pseudoInverseSeminorm Mdagger (coordinateDeriv (scaledDualPath lambda w) μ) ≤
        pseudoInverseSeminorm Mdagger r

/--
The LCP with derivatives from the proof sketch in Section 4.1.  Here `z` is the
integrated primal path, `dz` is its derivative, and `w` is the dual path.
-/
def isLCPWithDerivatives
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda s : ℝ)
    (z dz w : EuclideanSpace ℝ ι) : Prop :=
  w = parametricLcpQ r lambda s + matVec M z ∧
  Nonnegative w ∧ Nonnegative dz ∧ inner ℝ w dz = (0 : ℝ)

/-- A conic combination of a finite family of vectors. -/
def InCone {κ : Type*} [Fintype κ]
    (a : κ → EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι) : Prop :=
  ∃ coeff : κ → ℝ, (∀ i, 0 ≤ coeff i) ∧ (∑ i, coeff i • a i) = y

/--
Proposition 4.8 from `docs/Lasso.md`: the primal-dual formulation of the
positive lasso is a linear complementarity problem.
An informal proof:
The positive lasso objective is a convex quadratic function on the nonnegative orthant.
The Lagrangian is `L(x, v) = (1/2) <x, Mx> + <q, x> - <v, x>`,
where `q = -r + (\lambda + 1/\mu) \mathbb{1}`.
The KKT conditions are necessary and sufficient:
- Stationarity: `0 = \nabla_x L = q + Mx - v`
- Primal feasibility: `x \ge 0`
- Dual feasibility: `v \ge 0`
- Complementary slackness: `<v, x> = 0`
This exactly matches the LCP formulation.
-/
lemma pos_lasso_is_lcp
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) :
    IsPositiveLassoMinimizer M r lambda μ x ↔
    ∃ v : EuclideanSpace ℝ ι, isLCP M (lcpQ r lambda μ) x v := by
  sorry

/-- The parametric LCP (Eq 4.11 in docs/Lasso.md).
Defined for `w(μ) = μ v(μ)` and `z(μ) = μ x(μ)`. -/
def isParametricLCP
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (z w : EuclideanSpace ℝ ι) : Prop :=
  isLCP M (parametricLcpQ r lambda μ) z w

/--
Lemma 4.10 from `docs/Lasso.md`: For small `μ`, the parametric LCP has a unique solution.
An informal proof:
For `0 ≤ μ < 1 / max (‖r - λ𝟙‖∞, 1)`, the affine term
`q = (1 + μλ)𝟙 - μr` is strictly positive.
Setting `z = 0` and `w = q` satisfies the LCP equations.
Since `q > 0` and `M` is PSD, this is the unique solution: any nonzero
`z ≥ 0` would violate complementarity.
-/
lemma parametric_lcp_unique_small_mu
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hμ : 0 ≤ μ)
    (hμ_small : μ * ‖(WithLp.equiv 2 _).symm (fun i => r i - lambda)‖ < 1) :
    ∃! p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      isParametricLCP M r lambda μ p.1 p.2 := by
  sorry

/--
Theorem 4.6 from `docs/Lasso.md` (conic Caratheodory theorem).

Informal proof reference: `docs/Lasso.md`, Section 4.3, Theorem 4.6.
Choose a representation of `y` using a support of minimal cardinality. If the
chosen family is linearly dependent, move along a nontrivial dependence until
one coefficient reaches zero while all coefficients remain nonnegative. This
removes one generator, contradicting minimality. Hence the support is linearly
independent and has cardinality at most the ambient dimension.
-/
theorem conic_caratheodory
    {κ : Type*} [Fintype κ] (a : κ → EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ ι) (hy : InCone a y) :
    ∃ s : Finset κ,
      s.card ≤ Fintype.card ι ∧
      LinearIndependent ℝ (fun i : {i // i ∈ s} => a i) ∧
      InCone (fun i : {i // i ∈ s} => a i) y := by
  sorry

/--
Lemma 4.7 from `docs/Lasso.md`: a feasible nonnegative linear system has a
nonnegative solution with norm controlled by the right-hand side.

Informal proof reference: `docs/Lasso.md`, Section 4.3, Lemma 4.7.
Apply `conic_caratheodory` to express `y` using a linearly independent subfamily
of columns. On that subfamily the matrix has full column rank, so the coefficient
vector is controlled by the operator norm of the pseudo-inverse. Taking the
maximum over finitely many subfamilies gives the constant.
-/
theorem nonnegative_solution_norm_bound
    {κ : Type*} [Fintype κ] (a : κ → EuclideanSpace ℝ ι) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : EuclideanSpace ℝ ι, InCone a y →
        ∃ x : κ → ℝ,
          (∀ i, 0 ≤ x i) ∧ (∑ i, x i • a i) = y ∧
            ‖euclideanOf x‖ ≤ C * ‖y‖ := by
  sorry

/--
Proposition 4.9 from `docs/Lasso.md`: for positive lasso data, the LCP has a
solution and the dual variable is unique.

Informal proof reference: `docs/Lasso.md`, Section 4.4, Proposition 4.9.
Existence follows because the positive-lasso objective is bounded below on the
nonnegative orthant (`ell` is bounded below from `r ∈ Span M`, and the penalty is
nonnegative). The uniqueness of the dual variable is the standard uniqueness
part for positive-semidefinite LCPs, cited there as Cottle--Pang--Stone,
Theorem 3.1.7(d).
-/
theorem lcp_exists_unique_dual
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hdata : ProblemData M r lambda) (hμ : 0 < μ) :
    (∃ x v : EuclideanSpace ℝ ι, isLCP M (lcpQ r lambda μ) x v) ∧
      ∀ ⦃x x' v v' : EuclideanSpace ℝ ι⦄,
        isLCP M (lcpQ r lambda μ) x v →
        isLCP M (lcpQ r lambda μ) x' v' →
        v = v' := by
  sorry

/--
Lemma 4.11 from `docs/Lasso.md`: regularity of the unique dual solution of the
parametric LCP.

Informal proof reference: `docs/Lasso.md`, Section 4.5, Lemma 4.11.
Compare the LCP equations at two parameters `μ` and `μ'` after scaling by
`1 + μ λ`. The difference lies in `Span M`; pairing it with the corresponding
primal difference and using complementarity makes the cross terms nonpositive.
Cauchy--Schwarz gives a Lipschitz estimate, hence absolute continuity, and the
derivative conclusions follow by differentiating the Lipschitz path.
-/
theorem parametric_lcp_dual_regular
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (z w : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hsol : ∀ μ : ℝ, 0 ≤ μ → isParametricLCP M r lambda μ (z μ) (w μ))
    (hdual_unique :
      ∀ ⦃μ : ℝ⦄, 0 ≤ μ →
        ∀ ⦃z₁ z₂ w₁ w₂ : EuclideanSpace ℝ ι⦄,
          isParametricLCP M r lambda μ z₁ w₁ →
          isParametricLCP M r lambda μ z₂ w₂ →
          w₁ = w₂) :
    ParametricLCPDualRegular M Mdagger r lambda w := by
  sorry

end Lasso
