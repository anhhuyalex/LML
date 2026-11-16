/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.FiniteExponentialPenalty
public import LeanMachineLearning.SpinGlasses.Basic

/-!
# Exponential penalties for the violated constraints of the binary perceptron

Talagrand, *Spin Glasses* Vol. I, Section 2.1, Eqs. (2.4)-(2.5).  For a fixed disorder
`g : Fin M → Fin N → ℝ`, let `V g σ` be the number of violated constraints of the spin `σ`, i.e.
the cardinality of `{k | ∑ i, g k i * σ i < 0}`.  Then `V g σ = 0` exactly when `σ` is feasible, and
`∑ σ, exp (-β V g σ)` tends to the number of feasible spins as `β → ∞`.  The sizes `N`, `M` and
the disorder are fixed in this limit: nothing is said about exchanging `β → ∞` with `N → ∞`.

## Main declarations

* `SpinGlasses.tendsto_sum_exp_neg_mul_card_violated_constraints`: the limit (2.4).
* `SpinGlasses.sum_exp_neg_mul_card_violated_constraints_sub_card_le`: the explicit error bound
  `0 ≤ ∑ σ, exp (-β V g σ) - C(g) ≤ (2 ^ N - C(g)) exp (-β)` for `β ≥ 0`.
* `SpinGlasses.sum_ite_neg_constraint_field_eq`: for `N ≥ 1` the penalty energy `-β V g σ` is the
  sum over constraints of the potential `x ↦ if x < 0 then -β else 0` at the normalized field.
-/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace SpinGlasses

variable {N M : ℕ}

/-- A spin has no violated constraint exactly when it is feasible. -/
private lemma card_violated_constraints_eq_zero_iff (g : Fin M → Fin N → ℝ) (σ : Fin N → ℤˣ) :
    (univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card = 0 ↔
      ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ) := by
  simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- **Exponential penalties converge to the number of feasible configurations**, Eq. (2.4):
for fixed `N`, `M` and disorder `g`,
`∑ σ, exp (-β V g σ) → #{σ | ∀ k, 0 ≤ ∑ i, g k i * σ i}` as `β → ∞`, where `V g σ` is the number
of constraints with `∑ i, g k i * σ i < 0`.  No restriction on `N`, `M` is needed. -/
theorem tendsto_sum_exp_neg_mul_card_violated_constraints (g : Fin M → Fin N → ℝ) :
    Tendsto (fun β : ℝ => ∑ σ : Fin N → ℤˣ, Real.exp (-β *
        ((univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card : ℝ)))
      atTop (𝓝 ((univ.filter fun σ : Fin N → ℤˣ =>
        ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card : ℝ)) := by
  have h := tendsto_sum_exp_neg_mul_atTop_card_filter_eq_zero
    (fun σ : Fin N → ℤˣ =>
      ((univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card : ℝ))
    fun σ => Nat.cast_nonneg _
  have hset : (univ.filter fun σ : Fin N → ℤˣ =>
      ((univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card : ℝ) = 0) =
      univ.filter fun σ : Fin N → ℤˣ => ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, Nat.cast_eq_zero]
    exact card_violated_constraints_eq_zero_iff g σ
  rwa [hset] at h

/-- **Explicit error of the penalty approximation.**  For `β ≥ 0`,
`0 ≤ ∑ σ, exp (-β V g σ) - C(g) ≤ (2 ^ N - C(g)) exp (-β)`.  The factor `2 ^ N` does not control
normalized logarithms uniformly in `N`, so it cannot justify exchanging the limits in `β`, `N`. -/
theorem sum_exp_neg_mul_card_violated_constraints_sub_card_le (g : Fin M → Fin N → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) :
    0 ≤ ∑ σ : Fin N → ℤˣ, Real.exp (-β *
        ((univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card : ℝ)) -
      (univ.filter fun σ : Fin N → ℤˣ => ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card ∧
    ∑ σ : Fin N → ℤˣ, Real.exp (-β *
        ((univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card : ℝ)) -
      (univ.filter fun σ : Fin N → ℤˣ => ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card ≤
      ((2 : ℝ) ^ N - (univ.filter fun σ : Fin N → ℤˣ =>
        ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card) * Real.exp (-β) := by
  have h := sum_exp_neg_mul_sub_card_filter_le
    (fun σ : Fin N → ℤˣ => (univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card)
    hβ
  have hset : (univ.filter fun σ : Fin N → ℤˣ =>
      (univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card = 0) =
      univ.filter fun σ : Fin N → ℤˣ => ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    exact card_violated_constraints_eq_zero_iff g σ
  rw [hset] at h
  have hcard : (Fintype.card (Fin N → ℤˣ) : ℝ) = 2 ^ N := by
    rw [card_spin_configurations]
    simp
  rwa [hcard] at h

/-- **The penalty as a potential.**  For `N ≥ 1` the exponent `-β V g σ` is
`∑ k, u (S_k)` with `S_k = (√N)⁻¹ ∑ i, g k i * σ i` and `u x = if x < 0 then -β else 0`: the
normalization by `√N` does not change the sign.  The potential is bounded and measurable but
discontinuous at `0` for `β ≠ 0`. -/
theorem sum_ite_neg_constraint_field_eq (hN : 0 < N) (β : ℝ) (g : Fin M → Fin N → ℝ)
    (σ : Fin N → ℤˣ) :
    ∑ k : Fin M, (if (Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0 then -β else 0) =
      -β * ((univ.filter fun k : Fin M => ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0).card : ℝ) := by
  have hsqrt : 0 < (Real.sqrt N)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 hN))
  have hsign : ∀ k, (Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0 ↔
      ∑ i, g k i * ((σ i : ℤ) : ℝ) < 0 := fun k => by
    constructor
    · intro h
      by_contra h'
      exact h.not_ge (mul_nonneg hsqrt.le (not_lt.1 h'))
    · exact fun h => mul_neg_of_pos_of_neg hsqrt h
  simp only [hsign]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

end SpinGlasses
