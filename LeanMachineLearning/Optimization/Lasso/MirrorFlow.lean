/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
import LeanMachineLearning.Optimization.Lasso.Dynamic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Mirror Flow Interpretation of Diagonal Linear Networks

This file formalizes the mirror flow interpretation of the DLN dynamics.
-/

namespace Lasso

variable {ι : Type*} [Fintype ι]

/--
Section 4.2 from `docs/Lasso.md`: The Mirror Flow interpretation of the positive DLN dynamics.
An informal proof:
The positive DLN dynamics are given by `du/dt = - \nabla_u L(u)`. By chain rule, the effective linear parameter
`x = u \circ u` evolves as `dx/dt = -4 x \circ \nabla \ell(x) - 4 \lambda x`.
Using the entropy mirror map `h(x) = (1/4) \sum (x_i \log x_i - x_i)`, we have `\nabla h(x) = (1/4) \log x`.
Then `d \nabla h(x) / dt = (1/4) (1/x) \circ dx/dt = -\nabla \ell(x) - \lambda \mathbb{1} = -\nabla \widetilde{L}(x)`.
Thus the DLN dynamics can be written as a mirror flow in the dual space.
-/
lemma dln_is_mirror_flow (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ) (β : EuclideanSpace ℝ ι)
    (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε β u) :
    ∀ t, HasDerivAt (fun t => (WithLp.equiv 2 _).symm (fun i => (1/4 : ℝ) * Real.log (posEffectiveParameter u t i)))
      ((WithLp.equiv 2 _).symm (fun i => - ((M.mulVec (posEffectiveParameter u t)) i - r i + lambda))) t := by
  sorry

end Lasso
