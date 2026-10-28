/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Moments of a sum of i.i.d. variables: the recurrence in the number of summands

Let `ν` be a probability measure on a measurable space `Ω` and `f : Ω → ℝ` with all powers
`f^j` `ν`-integrable.
For the product measure `ν^{⊗n}` on `Fin n → Ω` put `S_n(y) = ∑ᵢ f (yᵢ)`.
Splitting off the first coordinate (`measurePreserving_piFinSuccAbove`) gives

`𝔼 S_{n+1}^k = ∑_{j ≤ k} C(k, j) (∫ f^j dν) 𝔼 S_n^{k-j}`.

This is the one-step recurrence used for the quantitative central limit theorem for i.i.d. sums
(Talagrand, Spin Glasses, proof of Theorem 1.4.11, Eq. (1.122)).

## Main declarations

* `ProbabilityTheory.integrable_pow_sum_pi`: every power of `S_n` is integrable.
* `ProbabilityTheory.integral_pow_sum_pi_succ`: the recurrence.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, after Eq. (1.122).
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ}

/-- Every power of the i.i.d. sum `S_n` is integrable. -/
theorem integrable_pow_sum_pi (hint : ∀ j, Integrable (fun x => f x ^ j) ν)
    (n k : ℕ) :
    Integrable (fun y : Fin n → Ω => (∑ i, f (y i)) ^ k) (Measure.pi fun _ : Fin n => ν) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hcomp : (fun y : Fin (n + 1) → Ω => (∑ i, f (y i)) ^ k) =
        (fun p : Ω × (Fin n → Ω) => (f p.1 + ∑ i, f (p.2 i)) ^ k) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0) := by
      funext y
      simp [Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply]
      rfl
    rw [hcomp, hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [add_pow]
    exact integrable_finsetSum _ fun j _ =>
      (((hint j).mul_prod (ih (k - j))).mul_const _)

/-- **The recurrence for the moments of an i.i.d. sum:**
`𝔼 S_{n+1}^k = ∑_{j ≤ k} C(k, j) (∫ f^j dν) 𝔼 S_n^{k-j}`. -/
theorem integral_pow_sum_pi_succ (hint : ∀ j, Integrable (fun x => f x ^ j) ν)
    (n k : ℕ) :
    ∫ y : Fin (n + 1) → Ω, (∑ i, f (y i)) ^ k ∂(Measure.pi fun _ : Fin (n + 1) => ν) =
      ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (∫ x, f x ^ j ∂ν) *
        ∫ y : Fin n → Ω, (∑ i, f (y i)) ^ (k - j) ∂(Measure.pi fun _ : Fin n => ν) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
  have hcomp : (fun y : Fin (n + 1) → Ω => (∑ i, f (y i)) ^ k) =
      (fun p : Ω × (Fin n → Ω) => (f p.1 + ∑ i, f (p.2 i)) ^ k) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0) := by
    funext y
    simp [Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  rw [hcomp]
  refine (hmp.integral_comp' (fun p : Ω × (Fin n → Ω) => (f p.1 + ∑ i, f (p.2 i)) ^ k)).trans ?_
  simp_rw [add_pow]
  rw [integral_finsetSum _ fun j _ =>
    (((hint j).mul_prod (integrable_pow_sum_pi hint n (k - j))).mul_const _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_prod_mul (fun x => f x ^ j)
    (fun y : Fin n → Ω => (∑ i, f (y i)) ^ (k - j))]
  ring

end ProbabilityTheory
