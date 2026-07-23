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

/-- The vector field for the gradient flow of `u` (the `u ∘ u` case). -/
noncomputable def posDlnVectorField (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) 
    (_t : ℝ) (u : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  - gradient (fun u' => posDlnObjective M r lambda u') u

/-- The gradient flow dynamics of the weight `u` from an initialization for the `u ∘ u` case. -/
def posDlnGradientFlow (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ) (β : EuclideanSpace ℝ ι) 
    (u : ℝ → EuclideanSpace ℝ ι) : Prop :=
  VaryingGFTrajectory (posDlnVectorField M r lambda) (Real.sqrt ε • β) u

/-- The effective linear parameter under gradient flow. -/
noncomputable def effectiveParameter (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (t : ℝ) : EuclideanSpace ℝ ι :=
  let wt := WithLp.equiv 2 _ (w t)
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => wt.1 i * wt.2 i)

/-- The time average of the effective parameter. -/
noncomputable def averageTrajectory (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (t : ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => (1 / t) * ∫ u in (0:ℝ)..t, effectiveParameter w u i)

/-- The effective linear parameter under positive gradient flow (u ∘ u). -/
noncomputable def posEffectiveParameter (u : ℝ → EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  let ut := u t
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => ut i * ut i)

/-- The time average of the positive effective parameter. -/
noncomputable def posAverageTrajectory (u : ℝ → EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => (1 / t) * ∫ v in (0:ℝ)..t, posEffectiveParameter u v i)

/-- Rescaled time `s` given time `t` and initialization scale `ε`. -/
noncomputable def rescaledTime (ε t : ℝ) : ℝ :=
  (2 / Real.log (1 / ε)) * t

/-- Time `t` given rescaled time `s` and initialization scale `ε`. -/
noncomputable def timeFromRescaled (ε s : ℝ) : ℝ :=
  (s / 2) * Real.log (1 / ε)

/-- Rescaled time `s` given time `t` and initialization scale `ε` for the `u ∘ u` case. -/
noncomputable def posRescaledTime (ε t : ℝ) : ℝ :=
  (4 / Real.log (1 / ε)) * t

/-- Time `t` given rescaled time `s` and initialization scale `ε` for the `u ∘ u` case. -/
noncomputable def posTimeFromRescaled (ε s : ℝ) : ℝ :=
  (s / 4) * Real.log (1 / ε)

end Lasso
