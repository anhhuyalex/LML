/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.Weights

/-!
# Extending bounds on monomials to products of linear combinations

A bound for a linear functional on each monomial extends to a product of finite linear
combinations. The loss is the product of the sums of the absolute coefficients. The factor
index and each summand index may be different finite types, including empty types.
-/

@[expose] public section

open scoped BigOperators

namespace LinearMap

/-- A uniform monomial bound extends to products of finite linear combinations. No
independence, positivity of the coefficients, or nonemptiness of the index types is needed. -/
theorem abs_apply_prod_sum_le {Ω J : Type*} [Fintype J]
    {ι : J → Type*} [∀ j, Fintype (ι j)] (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (c : ∀ j, ι j → ℝ) (f : ∀ j, ι j → Ω → ℝ) {E : ℝ}
    (h : ∀ t : ∀ j, ι j, |L (fun ω => ∏ j, f j (t j) ω)| ≤ E) :
    |L (fun ω => ∏ j, ∑ i, c j i * f j i ω)| ≤ (∏ j, ∑ i, |c j i|) * E := by
  classical
  have he : (fun ω => ∏ j, ∑ i, c j i * f j i ω) =
      ∑ t : ∀ j, ι j, (∏ j, c j (t j)) • (fun ω => ∏ j, f j (t j) ω) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.prod_sum,
      Finset.prod_mul_distrib]
  rw [he, map_sum]
  simp only [map_smul, smul_eq_mul]
  refine (Weights.abs_weighted_sum_le (fun t : ∀ j, ι j => ∏ j, c j (t j))
    (fun t : ∀ j, ι j => L (fun ω => ∏ j, f j (t j) ω)) h).trans_eq ?_
  rw [Fintype.prod_sum]
  congr 1
  exact Finset.sum_congr rfl fun t _ => Finset.abs_prod Finset.univ (fun j => c j (t j))

end LinearMap
