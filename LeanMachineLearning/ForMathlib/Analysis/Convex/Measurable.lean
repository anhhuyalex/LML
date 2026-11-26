/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of concave functions

## Main statements

* `ConcaveOn.measurable_of_univ`: a concave function on a whole finite-dimensional real normed
  space is measurable.
-/

@[expose] public section

/-- A concave function on a whole finite-dimensional real normed space is measurable. -/
theorem ConcaveOn.measurable_of_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) : Measurable u :=
  (continuousOn_univ.1 (hu.continuousOn isOpen_univ)).measurable
