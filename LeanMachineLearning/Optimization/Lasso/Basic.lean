/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import LeanMachineLearning.Optimization.ConvexOpt.Basic

/-!
# Lasso and Diagonal Linear Network Objectives

This file defines the base objectives for the lasso regularization path analysis.
-/

namespace Lasso

variable {ι : Type*} [Fintype ι]

/-- The quadratic loss function parameterized by a positive semidefinite matrix `M` and vector `r`. -/
noncomputable def quadraticLoss (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ x ((WithLp.equiv 2 (ι → ℝ)).symm (M.mulVec x)) - inner ℝ r x

/-- The lasso objective incorporating implicit regularization parameterized by `μ`. -/
noncomputable def lassoObjective (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  quadraticLoss M r x + (lambda + 1 / μ) * ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖

/-- The diagonal linear network (DLN) objective with explicit weight decay `lambda`. -/
noncomputable def dlnObjective (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (u v : EuclideanSpace ℝ ι) : ℝ :=
  quadraticLoss M r ((WithLp.equiv 2 (ι → ℝ)).symm (fun i => u i * v i)) + (lambda / 2) * (‖u‖^2 + ‖v‖^2)

/-- The positive DLN objective for the `u ∘ u` case with explicit weight decay `lambda`. -/
noncomputable def posDlnObjective (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (u : EuclideanSpace ℝ ι) : ℝ :=
  quadraticLoss M r ((WithLp.equiv 2 (ι → ℝ)).symm (fun i => u i * u i)) + lambda * ‖u‖^2

end Lasso
