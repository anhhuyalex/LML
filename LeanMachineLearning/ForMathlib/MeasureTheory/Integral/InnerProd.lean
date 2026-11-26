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

namespace MeasureTheory

/-- The inner product of integrable functions of two independent variables is integrable. -/
theorem Integrable.inner_fst_snd {α β 𝕜 E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {f : α → E} {g : β → E} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : α × β => inner 𝕜 (f z.1) (g z.2)) (μ.prod ν) :=
  hf.op_fst_snd (op := fun x y : E => inner 𝕜 x y) continuous_inner
    ⟨1, fun x y => by simpa only [one_mul] using norm_inner_le_norm (𝕜 := 𝕜) x y⟩ hg

end MeasureTheory
