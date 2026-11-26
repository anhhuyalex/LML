/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of the inner product of two independent vectors

## Main statements

* `MeasureTheory.Integrable.inner_fst_snd`: `(x, y) ↦ ⟪f x, g y⟫` is integrable for the product
  measure when `f` and `g` are integrable.
-/

@[expose] public section

open scoped InnerProductSpace

namespace MeasureTheory

/-- The inner product of integrable functions of two independent variables is integrable. -/
theorem Integrable.inner_fst_snd {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : α → E} {g : β → E} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : α × β => ⟪f z.1, g z.2⟫_ℝ) (μ.prod ν) :=
  hf.op_fst_snd (op := fun x y : E => ⟪x, y⟫_ℝ) continuous_inner
    ⟨1, fun x y => by simpa only [one_mul] using norm_inner_le_norm (𝕜 := ℝ) x y⟩ hg

end MeasureTheory
