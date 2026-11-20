/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Exponential tilting does not see the scale of the base measure

`(c • μ).tilted f = μ.tilted f` for a finite nonzero constant `c`: the normalizer absorbs the
scale. This lets a finite base measure (such as a counting measure on a finite spin space) be
replaced by a probability measure without changing the Gibbs measure.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- Tilting is invariant under rescaling the base measure by a finite nonzero constant. -/
theorem tilted_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) {c : ENNReal}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) : (c • μ).tilted f = μ.tilted f := by
  unfold Measure.tilted
  rw [withDensity_smul_measure, integral_smul_measure, ← withDensity_smul' c _ hc]
  congr 1
  funext x
  have hct : (c.toReal : ℝ) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc0, hc⟩
  rw [Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  conv_lhs => rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  congr 1
  rw [← mul_div_assoc, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, mul_div_mul_left _ _ hct]

end MeasureTheory
