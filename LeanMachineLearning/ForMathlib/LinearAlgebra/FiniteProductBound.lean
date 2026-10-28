/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
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

/-- A positive linear functional transfers a uniform square bound to any signed finite
linear combination. The coefficient loss is the square of the total absolute mass. -/
theorem apply_sq_sum_le {Ω I : Type*} [Fintype I] (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g : Ω → ℝ, (∀ ω, f ω ≤ g ω) → L f ≤ L g)
    (c : I → ℝ) (f : I → Ω → ℝ) {E : ℝ}
    (h : ∀ i, L (fun ω => f i ω ^ 2) ≤ E) :
    L (fun ω => (∑ i, c i * f i ω) ^ 2) ≤ (∑ i, |c i|) ^ 2 * E := by
  have hcross (i j : I) : |L (fun ω => f i ω * f j ω)| ≤ E := by
    have hp : 2 * L (fun ω => f i ω * f j ω) ≤
        L (fun ω => f i ω ^ 2) + L (fun ω => f j ω ^ 2) := by
      calc
        _ = L (2 • (fun ω => f i ω * f j ω)) := (L.map_smul 2 _).symm
        _ ≤ L ((fun ω => f i ω ^ 2) + (fun ω => f j ω ^ 2)) :=
          hmono _ _ fun ω => by
            change 2 * (f i ω * f j ω) ≤ f i ω ^ 2 + f j ω ^ 2
            simpa only [mul_assoc] using two_mul_le_add_sq (f i ω) (f j ω)
        _ = _ := L.map_add _ _
    have hn : -2 * L (fun ω => f i ω * f j ω) ≤
        L (fun ω => f i ω ^ 2) + L (fun ω => f j ω ^ 2) := by
      calc
        _ = L ((-2 : ℝ) • (fun ω => f i ω * f j ω)) := (L.map_smul (-2) _).symm
        _ ≤ L ((fun ω => f i ω ^ 2) + (fun ω => f j ω ^ 2)) :=
          hmono _ _ fun ω => by
            change -2 * (f i ω * f j ω) ≤ f i ω ^ 2 + f j ω ^ 2
            simpa only [neg_mul, mul_neg, neg_sq, mul_assoc] using
              two_mul_le_add_sq (-f i ω) (f j ω)
        _ = _ := L.map_add _ _
    exact abs_le.mpr ⟨by linarith [h i, h j], by linarith [h i, h j]⟩
  have he : (fun ω => (∑ i, c i * f i ω) ^ 2) =
      ∑ i, ∑ j, (c i * c j) • (fun ω => f i ω * f j ω) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [he, map_sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  calc
    _ ≤ ∑ i, ∑ j, |c i| * |c j| * E := Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => by
        calc
          _ ≤ |c i * c j * L (fun ω => f i ω * f j ω)| := le_abs_self _
          _ ≤ |c i| * |c j| * E := by
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hcross i j) (by positivity)
    _ = _ := by rw [sq, Finset.sum_mul_sum, Finset.sum_mul]; simp_rw [Finset.sum_mul]

/-- The square-bound extension for a product of finite linear combinations. -/
theorem apply_sq_prod_sum_le {Ω J : Type*} [Fintype J]
    {ι : J → Type*} [∀ j, Fintype (ι j)] (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g : Ω → ℝ, (∀ ω, f ω ≤ g ω) → L f ≤ L g)
    (c : ∀ j, ι j → ℝ) (f : ∀ j, ι j → Ω → ℝ) {E : ℝ}
    (h : ∀ t : ∀ j, ι j, L (fun ω => (∏ j, f j (t j) ω) ^ 2) ≤ E) :
    L (fun ω => (∏ j, ∑ i, c j i * f j i ω) ^ 2) ≤
      (∏ j, ∑ i, |c j i|) ^ 2 * E := by
  classical
  have he (ω : Ω) : (∏ j, ∑ i, c j i * f j i ω) =
      ∑ t : ∀ j, ι j, (∏ j, c j (t j)) * ∏ j, f j (t j) ω := by
    simp only [Fintype.prod_sum, Finset.prod_mul_distrib]
  simp_rw [he]
  refine (L.apply_sq_sum_le hmono (fun t : ∀ j, ι j => ∏ j, c j (t j))
    (fun t ω => ∏ j, f j (t j) ω) h).trans_eq ?_
  rw [Fintype.prod_sum]
  congr 2
  exact Finset.sum_congr rfl fun t _ => Finset.abs_prod Finset.univ (fun j => c j (t j))

end LinearMap
