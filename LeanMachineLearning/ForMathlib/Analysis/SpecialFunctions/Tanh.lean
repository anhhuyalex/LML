/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Continuity of `Real.tanh`
-/

@[expose] public section

namespace Real

/-- `Real.tanh` is continuous. -/
theorem continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from
    funext Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

end Real
