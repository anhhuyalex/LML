/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expanding the integral of a squared difference

For real functions `f`, `g` with `f²`, `g²` and `f g` integrable,
`∫ (f - g)² = ∫ f² - 2 ∫ f g + ∫ g²`.
-/

@[expose] public section

namespace MeasureTheory

/-- The integral of a squared difference expands as `∫ f² - 2 ∫ f g + ∫ g²`. -/
theorem integral_sq_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable (fun ω => f ω ^ 2) μ) (hg : Integrable (fun ω => g ω ^ 2) μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    ∫ ω, (f ω - g ω) ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ - 2 * ∫ ω, f ω * g ω ∂μ + ∫ ω, g ω ^ 2 ∂μ := by
  have h1 : Integrable (fun ω => f ω ^ 2 - 2 * (f ω * g ω)) μ := hf.sub (hfg.const_mul 2)
  rw [show (fun ω => (f ω - g ω) ^ 2) = fun ω => (f ω ^ 2 - 2 * (f ω * g ω)) + g ω ^ 2 from
    funext fun ω => by ring, integral_add h1 hg, integral_sub hf (hfg.const_mul 2),
    integral_const_mul]

end MeasureTheory
