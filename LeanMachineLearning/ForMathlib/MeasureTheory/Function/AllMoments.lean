/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# Functions with finite moments of every order

Real functions that belong to `L^p` for every finite `p` are closed under products. Together
with `MemLp.add`, `MemLp.sub` and `memLp_finsetSum` this makes them a class closed under
polynomial operations, which replaces boundedness in algebraic identities between integrals.

## Main statements

* `MeasureTheory.memLp_mul_of_forall_memLp`: a product of two functions with all finite moments
  has all finite moments.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A product of two real functions with finite moments of every order has finite moments of
every order. -/
theorem memLp_mul_of_forall_memLp {f g : α → ℝ} (hf : ∀ p : ℝ≥0, MemLp f p μ)
    (hg : ∀ p : ℝ≥0, MemLp g p μ) (p : ℝ≥0) : MemLp (fun x => f x * g x) p μ := by
  have : ENNReal.HolderTriple ((2 * p : ℝ≥0) : ℝ≥0∞) ((2 * p : ℝ≥0) : ℝ≥0∞) p := ⟨by
    rw [ENNReal.coe_mul, ENNReal.mul_inv (by norm_num) (by norm_num), ← two_mul, ← mul_assoc,
      ENNReal.coe_ofNat, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  exact (hf (2 * p)).fun_mul (hg (2 * p)) (hpqr := this)

end MeasureTheory
