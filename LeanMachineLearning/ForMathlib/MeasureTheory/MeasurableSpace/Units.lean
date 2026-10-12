/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Singletons of the units of a measurable monoid are measurable

The measurable space on `Mˣ` is the comap of `Units.val` (`Units.instMeasurableSpace`), so
singletons are measurable as soon as they are in `M`.  In particular the spin configurations
`ι → ℤˣ` of `SpinGlasses` form a measurable space with measurable singletons, which is what the
counting measure and `MeasureTheory.Measure.tilted` need.
-/

@[expose] public section

open MeasureTheory

/-- Singletons of `Mˣ` are measurable when singletons of `M` are. -/
instance Units.instMeasurableSingletonClass {M : Type*} [Monoid M] [MeasurableSpace M]
    [MeasurableSingletonClass M] : MeasurableSingletonClass Mˣ where
  measurableSet_singleton u := ⟨{(u : M)}, measurableSet_singleton _, by
    ext v; simp [Units.ext_iff]⟩

end
