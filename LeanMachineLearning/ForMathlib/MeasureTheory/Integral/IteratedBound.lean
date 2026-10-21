/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Pointwise domination of a triple iterated integral

A pointwise bound `|G x y z| ≤ H x y z` passes through three nested integrals
`∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ`, where the innermost measure may depend on the outer
variables, as soon as the dominating function has integrable partial integrals.
-/

@[expose] public section

open MeasureTheory

/-- Domination of a triple iterated integral by the iterated integral of a dominating function. -/
theorem abs_integral_integral_integral_le {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (κ : X → Y → Measure Z)
    {G H : X → Y → Z → ℝ} (hGH : ∀ x y z, |G x y z| ≤ H x y z)
    (h1 : ∀ x y, Integrable (H x y) (κ x y))
    (h2 : ∀ x, Integrable (fun y => ∫ z, H x y z ∂κ x y) ν)
    (h3 : Integrable (fun x => ∫ y, ∫ z, H x y z ∂κ x y ∂ν) μ) :
    |∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ| ≤ ∫ x, ∫ y, ∫ z, H x y z ∂κ x y ∂ν ∂μ := by
  have l1 (x y) : |∫ z, G x y z ∂κ x y| ≤ ∫ z, H x y z ∂κ x y := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le (f := fun z => G x y z) (h1 x y) (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs] using hGH x y z)
  have l2 (x) : |∫ y, ∫ z, G x y z ∂κ x y ∂ν| ≤ ∫ y, ∫ z, H x y z ∂κ x y ∂ν := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le (f := fun y => ∫ z, G x y z ∂κ x y) (h2 x)
        (ae_of_all _ fun y => by
        simpa only [Real.norm_eq_abs] using l1 x y)
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_of_norm_le (f := fun x => ∫ y, ∫ z, G x y z ∂κ x y ∂ν) h3
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using l2 x)
