/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite products and sums under Bochner integration

Generic lemmas for integrating products of finite sums and products of coordinate functions.
Summand types and coordinate spaces may be dependent. No model-specific assumptions are used.
-/

@[expose] public section

open MeasureTheory Finset

namespace MeasureTheory

/-- **Integral of a product of finite sums.** A product of finite linear combinations
integrates as a sum over multi-indices of the weighted products of integrals, provided
the weighted products are integrable. Summand types may depend on the factor. -/
theorem integral_prod_sum {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {M : J → Type*} [∀ j, Fintype (M j)] (μ : Measure Ω)
    (γ : (j : J) → M j → ℝ) (F : (j : J) → M j → Ω → ℝ)
    (h : ∀ t : (j : J) → M j,
      Integrable (fun ω => (∏ j, γ j (t j)) * ∏ j, F j (t j) ω) μ) :
    (∫ ω, ∏ j, ∑ m, γ j m * F j m ω ∂μ) =
      ∑ t : (j : J) → M j, (∏ j, γ j (t j)) * ∫ ω, ∏ j, F j (t j) ω ∂μ := by
  have hexp (ω : Ω) : (∏ j, ∑ m, γ j m * F j m ω) =
      ∑ t : (j : J) → M j, (∏ j, γ j (t j)) * ∏ j, F j (t j) ω := by
    rw [prod_univ_sum (fun _ => univ), Fintype.piFinset_univ]
    exact sum_congr rfl fun _ _ => prod_mul_distrib
  simp_rw [hexp]
  rw [integral_finsetSum _ fun t _ => h t]
  simp_rw [integral_const_mul]

/-- **Integrability of a product of coordinate functions with repeated indices.**
A product of coordinate functions is integrable against a product measure if each coordinate
function raised to its fiber cardinality is integrable. Valid for dependent coordinate spaces
and values in any normed commutative ring. -/
theorem integrable_prod_pi_dep {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J]
    [NormedCommRing K] {X : D → Type*} [∀ d, MeasurableSpace (X d)]
    (μ : (d : D) → Measure (X d)) [∀ d, SigmaFinite (μ d)]
    (d : J → D) (f : (κ : D) → X κ → K)
    (h : ∀ κ, Integrable
      (fun x => f κ x ^ (univ.filter fun j => d j = κ).card) (μ κ)) :
    Integrable (fun z : (κ : D) → X κ => ∏ j, f (d j) (z (d j))) (Measure.pi μ) := by
  have he (z : (κ : D) → X κ) : (∏ j, f (d j) (z (d j))) =
      ∏ κ, f κ (z κ) ^ (univ.filter fun j => d j = κ).card := by
    simpa only [prod_const] using
      (prod_fiberwise' (univ : Finset J) d (fun κ => f κ (z κ))).symm
  simp_rw [he]
  exact Integrable.fintype_prod_dep h

/-- **Integrability of a product of coordinate functions (homogeneous spaces).** -/
theorem integrable_prod_pi {D J K α : Type*} [Fintype D] [DecidableEq D] [Fintype J]
    [NormedCommRing K] [MeasurableSpace α]
    (μ : D → Measure α) [∀ d, SigmaFinite (μ d)]
    (d : J → D) (f : D → α → K)
    (h : ∀ κ, Integrable
      (fun x => f κ x ^ (univ.filter fun j => d j = κ).card) (μ κ)) :
    Integrable (fun z : D → α => ∏ j, f (d j) (z (d j))) (Measure.pi μ) :=
  integrable_prod_pi_dep μ d f h

end MeasureTheory

