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
private lemma abs_sum_potential_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, |u x| ≤ D)
    (g : Fin M → Fin N → ℝ) (σ : Fin N → ℤˣ) :
    |∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ))| ≤ M * D := by
  calc _ ≤ ∑ k : Fin M, |u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin M, D := Finset.sum_le_sum fun k _ => hD _
    _ = M * D := by simp

/-- **Pointwise pressure bound.**  For `N ≥ 1`, `|u| ≤ D` and every disorder `g`,
`|N⁻¹ log ∑ σ, exp (∑ k, u (S_k)) - log 2| ≤ (M / N) D`. -/
theorem abs_inv_mul_log_sum_exp_potential_sub_log_two_le (hN : 0 < N) {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ x, |u x| ≤ D) (g : Fin M → Fin N → ℝ) :
    |(N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) - Real.log 2| ≤
      M / N * D := by
  have h := abs_log_sum_exp_sub_log_card_le
    (fun σ : Fin N → ℤˣ => ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))
    fun σ => abs_sum_potential_le hD g σ
  rw [log_card_spin_configurations, Fintype.card_fin] at h
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have heq : (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) - Real.log 2 =
      (N : ℝ)⁻¹ * (Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) -
          N * Real.log 2) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (inv_pos.2 hN')]
  calc _ ≤ (N : ℝ)⁻¹ * (M * D) := by gcongr
    _ = M / N * D := by ring

/-- **The log-partition function is integrable** for a measurable bounded potential `u`: it is
measurable in the disorder and bounded by `N log 2 + M D`. -/
theorem integrable_log_sum_exp_potential {u : ℝ → ℝ} {D : ℝ} (hu : Measurable u)
    (hD : ∀ x, |u x| ≤ D) :
    Integrable (fun g : Fin M → Fin N → ℝ => Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  refine Integrable.of_bound (C := Real.log (Fintype.card (Fin N → ℤˣ)) + M * D) ?_
    (ae_of_all _ fun g => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    exact Real.measurable_log.comp (Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)))
  · rw [Real.norm_eq_abs]
    exact abs_log_sum_exp_le_of_forall _ fun σ => abs_sum_potential_le hD g σ

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
  set P : Measure (Fin M → Fin N → ℝ) :=
    Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1 with hP
  have hint := integrable_log_sum_exp_potential (N := N) (M := M) hu hD
  have heq : (N : ℝ)⁻¹ * ∫ g, Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) ∂P - Real.log 2 =
      ∫ g, ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) - Real.log 2) ∂P := by
    rw [integral_sub (hint.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp [hP]
  rw [heq]
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun g : Fin M → Fin N → ℝ => (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)))) - Real.log 2)
    (C := M / N * D) (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs]
      exact abs_inv_mul_log_sum_exp_potential_sub_log_two_le hN hD g)
  simpa using this

/-- **The derivative-product observable of (2.10) is bounded by `(M / N) D²`.**  If `|u'| ≤ D`, then
for any two fixed spins `σ`, `τ` (the replicas) and every disorder `g`,
`|N⁻¹ ∑ k, u'(S_k σ) u'(S_k τ)| ≤ (M / N) D²`.  The denominator is `N`, not `M`. -/
theorem abs_inv_mul_sum_deriv_mul_deriv_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    (g : Fin M → Fin N → ℝ) (σ τ : Fin N → ℤˣ) :
    |(N : ℝ)⁻¹ * ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)) *
        deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))| ≤ M / N * D ^ 2 := by
  have hsum : |∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)) *
        deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))| ≤ M * D ^ 2 := by
    calc _ ≤ ∑ k : Fin M, |deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)) *
          deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin M, D ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [abs_mul, sq]
          exact mul_le_mul (hD _) (hD _) (abs_nonneg _) ((abs_nonneg _).trans (hD 0))
      _ = M * D ^ 2 := by simp
  rw [abs_mul, abs_inv, Nat.abs_cast]
  calc _ ≤ (N : ℝ)⁻¹ * (M * D ^ 2) := by gcongr
    _ = M / N * D ^ 2 := by ring

/-- **The pointwise bound is sharp.**  For a constant potential `u = c` and `N ≥ 1` the pressure is
exactly `N⁻¹ log ∑ σ, exp (∑ k, c) = log 2 + (M / N) c`, so `(M / N) D` cannot be replaced by a
smaller constant in `abs_inv_mul_log_sum_exp_potential_sub_log_two_le`. -/
theorem inv_mul_log_sum_exp_const_potential (hN : 0 < N) (c : ℝ) :
    (N : ℝ)⁻¹ * Real.log (∑ _σ : Fin N → ℤˣ, Real.exp (∑ _k : Fin M, c)) =
      Real.log 2 + M / N * c := by
  have hN' : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 hN).ne'
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, card_spin_configurations,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, Real.log_mul (by positivity)
      (Real.exp_pos _).ne', Real.log_exp]
  push_cast
  rw [Real.log_pow]
  field_simp

end SpinGlasses
