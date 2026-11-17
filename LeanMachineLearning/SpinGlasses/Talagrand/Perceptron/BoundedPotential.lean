/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.LogSumExp
public import LeanMachineLearning.SpinGlasses.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Finite-size bounds for the perceptron with a bounded potential

Talagrand, *Spin Glasses* Vol. I, Section 2.1, Eqs. (2.6), (2.10) and (2.11).  For a potential
`u : ℝ → ℝ` the energy of a spin `σ` (the exponent of its Gibbs weight, with counting measure on
the spins) is
`E_u(g, σ) = ∑ k, u ((√N)⁻¹ * ∑ i, g k i * σ i)`, the partition function is
`∑ σ, exp (E_u g σ)` and the pressure is `N⁻¹ 𝔼 log ∑ σ, exp (E_u g σ)`.

If `|u| ≤ D`, then `|E_u| ≤ M D`, and the pressure is within `(M / N) D` of `log 2`, the pressure of
`u = 0`.  Only measurability of `u` and its value bound are used: neither the three derivatives of
the book's hypothesis (2.7) nor a small-load restriction on `M / N` is needed.  These are elementary
finite-size facts; they do not give the replica-symmetric formula of the later sections.
The derivative-product observable of (2.10) is bounded in the same way by `(M / N) D²`.

## Main declarations

* `SpinGlasses.abs_inv_mul_log_sum_exp_potential_sub_log_two_le`: the pointwise bound.
* `SpinGlasses.integrable_log_sum_exp_potential`: the log-partition function is integrable.
* `SpinGlasses.abs_inv_mul_integral_log_sum_exp_potential_sub_log_two_le`: the pressure bound.
* `SpinGlasses.abs_inv_mul_sum_deriv_mul_deriv_le`: the bound for the observable (2.10).
* `SpinGlasses.inv_mul_log_sum_exp_const_potential`: for a constant potential the pressure is
  exactly `log 2 + (M / N) c`, so the constant `(M / N) D` above cannot be improved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

variable {N M : ℕ}

/-- **The energy is bounded by `M D`.**  If `|u| ≤ D` then
`|∑ k, u (S_k)| ≤ M D` for every disorder and spin. -/
theorem abs_sum_potential_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, |u x| ≤ D)
    (g : Fin M → Fin N → ℝ) (σ : Fin N → ℤˣ) :
    |∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ))| ≤ M * D := by
  simpa using Finset.abs_sum_le_card_mul_of_abs_le
    (fun k : Fin M => u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ))) (fun _ => hD _)

/-- The partition sum lies between `2^N exp (-M D)` and `2^N exp (M D)`. These bounds hold
for every disorder, including zero spins or zero constraints, without measurability assumptions. -/
theorem sum_exp_potential_bounds {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, |u x| ≤ D)
    (g : Fin M → Fin N → ℝ) :
    (2 : ℝ) ^ N * Real.exp (-(M * D)) ≤
        ∑ σ : Fin N → ℤˣ,
          Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ))) ∧
      (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) ≤
        (2 : ℝ) ^ N * Real.exp (M * D) := by
  have hcard (c : ℝ) : (∑ _σ : Fin N → ℤˣ, c) = (2 : ℝ) ^ N * c := by
    simp
  constructor
  · rw [← hcard]
    exact Finset.sum_le_sum fun σ _ =>
      Real.exp_le_exp.mpr (neg_le_of_abs_le (abs_sum_potential_le hD g σ))
  · rw [← hcard]
    exact Finset.sum_le_sum fun σ _ =>
      Real.exp_le_exp.mpr (le_of_abs_le (abs_sum_potential_le hD g σ))

/-- **Pointwise pressure bound.**  For `N ≥ 1`, `|u| ≤ D` and every disorder `g`,
`|N⁻¹ log ∑ σ, exp (∑ k, u (S_k)) - log 2| ≤ (M / N) D`. -/
theorem abs_inv_mul_log_sum_exp_potential_sub_log_two_le (hN : 0 < N) {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ x, |u x| ≤ D) (g : Fin M → Fin N → ℝ) :
    |(N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) - Real.log 2| ≤
      M / N * D := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [← inv_mul_log_card_spin_configurations hN, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.2 hN')]
  calc _ ≤ (N : ℝ)⁻¹ * (M * D) :=
        mul_le_mul_of_nonneg_left
          (abs_log_sum_exp_sub_log_card_le _ fun σ => abs_sum_potential_le hD g σ)
          (inv_nonneg.2 hN'.le)
    _ = M / N * D := by ring

/-- **The log-partition function is integrable** for a measurable bounded potential `u`: it is
measurable in the disorder and bounded by `N log 2 + M D`. -/
theorem integrable_log_sum_exp_potential {u : ℝ → ℝ} {D : ℝ} (hu : Measurable u)
    (hD : ∀ x, |u x| ≤ D) :
    Integrable (fun g : Fin M → Fin N → ℝ => Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  exact integrable_log_sum_exp_of_abs_le
    (fun σ => Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop))
    (integrable_const (M * D)) (ae_of_all _ fun g σ => abs_sum_potential_le hD g σ)

/-- **Expected pressure bound** (the normalization behind (2.11)).  For `N ≥ 1`, a measurable
potential with `|u| ≤ D` and counting measure on the spins,
`|N⁻¹ 𝔼 log ∑ σ, exp (∑ k, u (S_k)) - log 2| ≤ (M / N) D`.  There is no small-load assumption on
`M / N`, and `u` needs no derivative. -/
theorem abs_inv_mul_integral_log_sum_exp_potential_sub_log_two_le (hN : 0 < N) {u : ℝ → ℝ}
    {D : ℝ} (hu : Measurable u) (hD : ∀ x, |u x| ≤ D) :
    |(N : ℝ)⁻¹ * ∫ g : Fin M → Fin N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ))))
        ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) -
      Real.log 2| ≤ M / N * D := by
  have h := abs_integral_log_sum_exp_sub_log_card_le_const
    (μ := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (E := fun g σ => ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))
    (fun σ => Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop))
    (fun g σ => abs_sum_potential_le hD g σ)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [← inv_mul_log_card_spin_configurations hN, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.2 hN')]
  calc _ ≤ (N : ℝ)⁻¹ * (M * D) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hN'.le)
        exact h
    _ = M / N * D := by ring

/-- **The derivative-product observable of (2.10) is bounded by `(M / N) D²`.**  If `|u'| ≤ D`, then
for any two fixed spins `σ`, `τ` (the replicas) and every disorder `g`,
`|N⁻¹ ∑ k, u'(S_k σ) u'(S_k τ)| ≤ (M / N) D²`.  The denominator is `N`, not `M`. -/
theorem abs_inv_mul_sum_deriv_mul_deriv_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    (g : Fin M → Fin N → ℝ) (σ τ : Fin N → ℤˣ) :
    |(N : ℝ)⁻¹ * ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)) *
        deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))| ≤ M / N * D ^ 2 := by
  have hsum : |∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)) *
        deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))| ≤ M * D ^ 2 := by
    refine (Finset.abs_sum_le_card_mul_of_abs_le
      (fun k : Fin M => deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)) *
        deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
      (C := D ^ 2) (fun k => ?_)).trans_eq
      (by simp)
    rw [abs_mul, sq]
    exact mul_le_mul (hD _) (hD _) (abs_nonneg _) ((abs_nonneg _).trans (hD 0))
  rw [abs_mul, abs_inv, Nat.abs_cast]
  calc _ ≤ (N : ℝ)⁻¹ * (M * D ^ 2) := by gcongr
    _ = M / N * D ^ 2 := by ring

/-- **The pointwise bound is sharp.**  For a constant potential `u = c` and `N ≥ 1` the pressure is
exactly `N⁻¹ log ∑ σ, exp (∑ k, c) = log 2 + (M / N) c`, so `(M / N) D` cannot be replaced by a
smaller constant in `abs_inv_mul_log_sum_exp_potential_sub_log_two_le`. -/
theorem inv_mul_log_sum_exp_const_potential (hN : 0 < N) (c : ℝ) :
    (N : ℝ)⁻¹ * Real.log (∑ _σ : Fin N → ℤˣ, Real.exp (∑ _k : Fin M, c)) =
      Real.log 2 + M / N * c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, mul_add,
    inv_mul_log_card_spin_configurations hN]
  ring

end SpinGlasses
