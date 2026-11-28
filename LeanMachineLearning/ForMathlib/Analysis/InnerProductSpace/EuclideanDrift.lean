/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Pairing with a drift vector in Euclidean space

The inner product with the vector `h g + c e_k`, written coordinate-wise.

## Main statement

* `EuclideanSpace.inner_toLp_mul_add_ite`
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace EuclideanSpace

/-- `⟪h g + c e_k, σ⟫ = h ∑ i, g i σ i + σ k c`. -/
theorem inner_toLp_mul_add_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (h c : ℝ) (g : ι → ℝ)
    (k : ι) (σ : EuclideanSpace ℝ ι) :
    ⟪WithLp.toLp 2 (fun i => h * g i + if i = k then c else 0), σ⟫ =
      h * (∑ i, g i * σ i) + σ k * c := by
  have h1 : ⟪WithLp.toLp 2 (fun i => h * g i + if i = k then c else 0), σ⟫ =
      ∑ i, (h * g i + if i = k then c else 0) * σ i := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [h1, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [mul_comm (σ k), Finset.mul_sum]
  exact congrArg (· + _) (Finset.sum_congr rfl fun i _ => mul_assoc _ _ _)

end EuclideanSpace
