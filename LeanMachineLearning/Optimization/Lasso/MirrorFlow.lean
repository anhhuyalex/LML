/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Mirror Flow Interpretation of Diagonal Linear Networks

This file formalizes the mirror flow interpretation of the DLN dynamics.
-/

@[expose] public section

namespace Lasso

variable {ι : Type*} [Fintype ι]

/-- The gradient of the entropy mirror map, `∇h(x) = 1/4 * log x`, coordinatewise. -/
noncomputable def entropyMirrorGradient (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun i => (1 / 4 : ℝ) * Real.log (x i))

/-- The closed-form positive-DLN vector field in the effective parameter `x = u²`. -/
noncomputable def positiveEffectiveVectorField
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun i => -4 * x i * ((matVec M x) i - r i + lambda))

/-- The mirror-flow ODE `d ∇h(x(t)) / dt = -∇ \widetilde L(x(t))`. -/
def IsEntropyMirrorFlow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : ℝ → EuclideanSpace ℝ ι) : Prop :=
  ∀ t : ℝ,
    HasDerivAt (fun τ => entropyMirrorGradient (x τ))
      (-gradient (tiltedLoss M r lambda) (x t)) t

/--
Equation (3.3) from `docs/Lasso.md`: the effective positive parameter
`x = u²` satisfies a closed ODE.

Informal proof reference: `docs/Lasso.md`, Section 3, Eq. (3.3).
Differentiate `x_i = u_i^2`, use the gradient flow equation for `u_i`, and
apply the chain rule to `ell(u²) + lambda ‖u‖²`.
-/
theorem pos_effective_parameter_hasDerivAt
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) :
    ∀ t : ℝ,
      HasDerivAt (fun τ => posEffectiveParameter u τ)
        (positiveEffectiveVectorField M r lambda (posEffectiveParameter u t)) t := by
  sorry

/--
Section 4.2 from `docs/Lasso.md`: The Mirror Flow interpretation of the positive DLN dynamics.
An informal proof:
The positive DLN dynamics are given by `du/dt = -∇ᵤ L(u)`. By the chain rule,
the effective linear parameter `x = u ∘ u` evolves as
`dx/dt = -4 x ∘ ∇ell(x) - 4 lambda x`.
Using the entropy mirror map `h(x) = (1/4) * Σᵢ (xᵢ log xᵢ - xᵢ)`, we have
`∇h(x) = (1/4) log x`. Thus
`d ∇h(x) / dt = -∇ell(x) - lambda * 𝟙 = -∇L̃(x)`.
Thus the DLN dynamics can be written as a mirror flow in the dual space.
-/
lemma dln_is_mirror_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε β u) :
    ∀ t,
      HasDerivAt
        (fun t =>
          (WithLp.equiv 2 _).symm
            (fun i => (1 / 4 : ℝ) * Real.log (posEffectiveParameter u t i)))
        ((WithLp.equiv 2 _).symm
          (fun i => -((M.mulVec (posEffectiveParameter u t)) i - r i + lambda))) t := by
  sorry

/--
Mirror-flow formulation of the positive-DLN dynamics, packaged with the reusable
predicate `IsEntropyMirrorFlow`.

Informal proof reference: `docs/Lasso.md`, Section 4.2, Eq. (4.1).
This is the same chain-rule computation as `dln_is_mirror_flow`, but stated
using the local API for `entropyMirrorGradient` and `tiltedLoss`.
-/
theorem pos_dln_is_entropy_mirror_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) :
    IsEntropyMirrorFlow M r lambda (fun t => posEffectiveParameter u t) := by
  sorry

/--
Lemma 4.2 from `docs/Lasso.md`: the tilted loss is nonincreasing along the
positive-DLN effective trajectory.

Informal proof reference: Section 4.3, Lemma 4.2. Differentiate
`\widetilde L(x(t))` and use Eq. (3.3) to obtain
`-4 * Σᵢ xᵢ(t) * (∂ᵢ \widetilde L(x(t)))² ≤ 0`.
-/
theorem tiltedLoss_antitone_along_pos_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) :
    Antitone (fun t => tiltedLoss M r lambda (posEffectiveParameter u t)) := by
  sorry

/--
Lemma 4.3 from `docs/Lasso.md`: in the non-coercive case, energy decrease still
controls the image `M xᵋ(t)`.

Informal proof reference: Section 4.3, Lemma 4.3.  Let `x_*` be the minimum-norm
minimizer of `ell`.  Since `r ∈ Span M`, the quadratic loss is bounded below
and `‖M x‖²` is controlled by `‖M^(1/2)(x-x_*)‖²`, hence by the tilted loss
bound from Lemma 4.2.
-/
theorem pos_trajectory_matVec_uniform_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (α : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r 0) (hα : NonzeroCoordinates α)
    (hu : ∀ ε > 0, posDlnGradientFlow M r 0 ε α (u ε)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ,
        ‖matVec M (posEffectiveParameter (u ε) t)‖ ≤ C := by
  sorry

/--
The Bregman divergence associated with the entropy mirror map is nonnegative.

Informal proof reference: `docs/Lasso.md`, Section 4.2 after Eq. (4.2).
It follows from convexity of `h`; in coordinates this is the usual nonnegativity
of relative entropy.
-/
theorem entropyBregman_nonnegative
    (x y : EuclideanSpace ℝ ι) (hx : Positive x) (hy : Positive y) :
    0 ≤ entropyBregman x y := by
  sorry

/--
Lemma 4.4 from `docs/Lasso.md`: the positive-DLN trajectory is the Bregman
projection of its initialization onto the affine fiber with the same `M x`.

Informal proof reference: Section 4.3, Lemma 4.4. The first-order optimality
condition for the constrained Bregman projection is
`∇h(x(t)) - ∇h(x(0)) ∈ Span M`; integrating the mirror-flow equation shows this
condition for the DLN trajectory. Strict convexity gives uniqueness.
-/
theorem bregman_projection_characterization
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) (t : ℝ) :
    IsMinOn
        (fun x => entropyBregman x (posEffectiveParameter u 0))
        {x | Nonnegative x ∧ matVec M x = matVec M (posEffectiveParameter u t)}
        (posEffectiveParameter u t) ∧
      ∀ y : EuclideanSpace ℝ ι,
        IsMinOn
          (fun x => entropyBregman x (posEffectiveParameter u 0))
          {x | Nonnegative x ∧ matVec M x = matVec M (posEffectiveParameter u t)}
          y →
        y = posEffectiveParameter u t := by
  sorry

/--
Lemma 4.5 from `docs/Lasso.md`: Bregman projections on nonnegative affine
fibers have a norm bound polynomial in the fiber value.

Informal proof reference: Section 4.3, Lemma 4.5.  Compare the entropy
Bregman objective at its minimizer with a minimum-norm feasible nonnegative
solution supplied by Lemma 4.7.  The coordinate expression for the Bregman
divergence is sandwiched between a linear lower bound and a quadratic upper
bound in `‖x‖`, uniformly for small `ε`.
-/
theorem bregman_projection_fiber_norm_bound
    (M : Matrix ι ι ℝ) (α : EuclideanSpace ℝ ι) (hα : NonzeroCoordinates α) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ y : EuclideanSpace ℝ ι,
          (∃ u : EuclideanSpace ℝ ι, Nonnegative u ∧ matVec M u = y) →
          ∀ x : EuclideanSpace ℝ ι,
            IsMinOn
              (fun z => entropyBregman z (ε • coordinateSquare α))
              {z | Nonnegative z ∧ matVec M z = y}
              x →
            ‖x‖ ≤ C * (1 + ‖y‖ ^ 2) := by
  sorry

/--
Proposition 4.1 from `docs/Lasso.md`: the positive effective trajectories are
uniformly bounded in time for all sufficiently small initializations.

Informal proof reference: Section 4.3, Proposition 4.1. Lemma 4.2 bounds
`\widetilde L`; Lemma 4.3 bounds `M x(t)` when coercivity is unavailable; Lemma
4.4 turns the trajectory into a Bregman projection; Lemma 4.5 bounds that
projection by a polynomial in `‖M x(t)‖`.
-/
theorem pos_trajectory_uniform_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hα : NonzeroCoordinates α)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε α (u ε)) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ t : ℝ,
        ‖posEffectiveParameter (u ε) t‖ ≤ C := by
  sorry

end Lasso

end
