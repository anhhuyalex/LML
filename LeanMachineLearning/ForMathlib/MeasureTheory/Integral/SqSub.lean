/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

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

/-- The square of a bounded measurable function is integrable for a finite measure. -/
theorem integrable_sq_of_abs_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    Integrable (fun ω => f ω ^ 2) μ := by
  refine Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq' (abs_le.mp (hC ω)).1 (abs_le.mp (hC ω)).2

/-- **Three-term triangle inequality in `L²`:**
`∫ (a + b + c)² ≤ 3 ∫ a² + 3 ∫ b² + 3 ∫ c²` for square-integrable `a, b, c`. -/
theorem integral_sq_add_add_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {a b c : Ω → ℝ} (ha : Integrable (fun ω => a ω ^ 2) μ) (hb : Integrable (fun ω => b ω ^ 2) μ)
    (hc : Integrable (fun ω => c ω ^ 2) μ) :
    ∫ ω, (a ω + b ω + c ω) ^ 2 ∂μ ≤
      3 * ∫ ω, a ω ^ 2 ∂μ + 3 * ∫ ω, b ω ^ 2 ∂μ + 3 * ∫ ω, c ω ^ 2 ∂μ := by
  have hab : Integrable (fun ω => 3 * a ω ^ 2 + 3 * b ω ^ 2) μ :=
    (ha.const_mul 3).add (hb.const_mul 3)
  have hint : Integrable (fun ω => 3 * a ω ^ 2 + 3 * b ω ^ 2 + 3 * c ω ^ 2) μ :=
    hab.add (hc.const_mul 3)
  calc ∫ ω, (a ω + b ω + c ω) ^ 2 ∂μ ≤ ∫ ω, (3 * a ω ^ 2 + 3 * b ω ^ 2 + 3 * c ω ^ 2) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint
          (Filter.Eventually.of_forall fun ω => by
            nlinarith [sq_nonneg (a ω - b ω), sq_nonneg (a ω - c ω), sq_nonneg (b ω - c ω)])
    _ = _ := by
        rw [integral_add hab (hc.const_mul 3), integral_add (ha.const_mul 3) (hb.const_mul 3),
          integral_const_mul, integral_const_mul, integral_const_mul]

end MeasureTheory
