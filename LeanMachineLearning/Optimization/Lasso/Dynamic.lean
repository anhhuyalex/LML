/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
import LeanMachineLearning.Optimization.Lasso.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# DLN Gradient Flow Dynamics

This file models the gradient flow dynamics of the diagonal linear network
and defines the time-averaged trajectory.
-/

namespace Lasso

open ConvexOpt
variable {ι : Type*} [Fintype ι]

/-- The vector field for the gradient flow of `u` and `v`. 
The state is `WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)`. -/
noncomputable def dlnVectorField (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) 
    (_t : ℝ) (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  let u := (WithLp.equiv 2 _ state).1
  let v := (WithLp.equiv 2 _ state).2
  (WithLp.equiv 2 _).symm (- gradient (fun u' => dlnObjective M r lambda u' v) u,
   - gradient (fun v' => dlnObjective M r lambda u v') v)

/-- The gradient flow dynamics of the weights `u` and `v` from an initialization. -/
def dlnGradientFlow (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ) (β γ : EuclideanSpace ℝ ι) 
    (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) : Prop :=
  VaryingGFTrajectory (dlnVectorField M r lambda) ((WithLp.equiv 2 _).symm (Real.sqrt ε • β, Real.sqrt ε • γ)) w

/-- The effective linear parameter under gradient flow. -/
noncomputable def effectiveParameter (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (t : ℝ) : EuclideanSpace ℝ ι :=
  let wt := WithLp.equiv 2 _ (w t)
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => wt.1 i * wt.2 i)

/-- The time average of the effective parameter. -/
noncomputable def averageTrajectory (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (t : ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => (1 / t) * ∫ u in (0:ℝ)..t, effectiveParameter w u i)

/-- Rescaled time `s` given time `t` and initialization scale `ε`. -/
noncomputable def rescaledTime (ε t : ℝ) : ℝ :=
  (2 / Real.log (1 / ε)) * t

/-- Time `t` given rescaled time `s` and initialization scale `ε`. -/
noncomputable def timeFromRescaled (ε s : ℝ) : ℝ :=
  (s / 2) * Real.log (1 / ε)

end Lasso
