/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SpinGlasses.Basic
public import LeanMachineLearning.SpinGlasses.SKModel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Free energy and the smooth approximation of the ground-state energy

The partition function at inverse temperature `β` of an energy function `H : α → ℝ` on a finite
configuration space is `Z(β) = ∑ a, exp (β * H a)`, and the free energy is the normalized expected
log-partition function `N⁻¹ 𝔼 log Z(β)` ([Panchenko, 2013, §1.1]).  The elementary sandwich
`max H ≤ β⁻¹ log Z(β) ≤ β⁻¹ log |α| + max H` ([Panchenko, 2013, Eq. (1.7)]) says that the free
energy at large `β` approximates the ground-state energy.

No definition is introduced: the partition function is the explicit sum, the maximum is
`Function.max` (`ForMathlib/MeasureTheory/Order/MeasurableArg.lean`, with its measurability), and
the expectation is the Bochner integral.  The three layers are kept apart, so that each is reusable
for any finite Gibbs system (Potts, random-field Ising, mixed `p`-spin, ...).

## Main declarations

* **Deterministic** (any finite nonempty `α`, `β > 0`):
  `SpinGlasses.max_le_inv_mul_log_sum_exp`, `SpinGlasses.inv_mul_log_sum_exp_le`,
  `SpinGlasses.abs_inv_mul_log_sum_exp_sub_max_le`.
* **Random energy** `H : Ω → α → ℝ` with measurable, integrable coordinates on a probability
  space: `SpinGlasses.integrable_max`, `SpinGlasses.integrable_log_sum_exp` and the integrated
  sandwich `SpinGlasses.integral_max_le_inv_mul_integral_log_sum_exp`,
  `SpinGlasses.inv_mul_integral_log_sum_exp_le`,
  `SpinGlasses.abs_inv_mul_integral_log_sum_exp_sub_integral_max_le`.
* **Hypercube** `α = ι → ℤˣ`, `|α| = 2 ^ N`, after dividing by `N`:
  `SpinGlasses.card_inv_mul_integral_max_le`, `SpinGlasses.card_inv_mul_integral_log_sum_exp_le`
  and `SpinGlasses.abs_card_inv_mul_integral_log_sum_exp_sub_le` (Eq. (1.7) and the error bound
  `log 2 / β`).
* **SK model**: `SpinGlasses.measurable_skHamiltonian`, `SpinGlasses.integrable_skHamiltonian`
  verify the hypotheses for the Hamiltonian of `SKModel.lean`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Matrix

namespace SpinGlasses

section Deterministic

variable {α : Type*} [Fintype α] [Nonempty α] {β : ℝ}

/-- **Log-sum-exp, lower bound:** `max_a f a ≤ β⁻¹ log ∑ₐ exp (β f a)` for `β > 0`. -/
theorem max_le_inv_mul_log_sum_exp (hβ : 0 < β) (f : α → ℝ) :
    f.max ≤ β⁻¹ * Real.log (∑ a, Real.exp (β * f a)) := by
  obtain ⟨a, ha⟩ := exists_argmax f
  rw [le_inv_mul_iff₀ hβ, ← ha, mul_comm, ← Real.log_exp (f a * β)]
  exact Real.log_le_log (Real.exp_pos _)
    (Finset.single_le_sum (f := fun a => Real.exp (β * f a)) (fun _ _ => (Real.exp_pos _).le)
      (mem_univ a) |>.trans_eq' (by rw [mul_comm]))

/-- **Log-sum-exp, upper bound:** `β⁻¹ log ∑ₐ exp (β f a) ≤ β⁻¹ log |α| + max_a f a` for `β > 0`. -/
theorem inv_mul_log_sum_exp_le (hβ : 0 < β) (f : α → ℝ) :
    β⁻¹ * Real.log (∑ a, Real.exp (β * f a)) ≤ β⁻¹ * Real.log (Fintype.card α) + f.max := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : ∑ a, Real.exp (β * f a) ≤ Fintype.card α * Real.exp (β * f.max) := by
    calc ∑ a, Real.exp (β * f a) ≤ ∑ _a : α, Real.exp (β * f.max) :=
          Finset.sum_le_sum fun a _ =>
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (f.le_max a) hβ.le)
      _ = Fintype.card α * Real.exp (β * f.max) := by simp
  have hpos : 0 < ∑ a, Real.exp (β * f a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  calc β⁻¹ * Real.log (∑ a, Real.exp (β * f a))
      ≤ β⁻¹ * Real.log (Fintype.card α * Real.exp (β * f.max)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hpos hsum) (inv_nonneg.2 hβ.le)
    _ = β⁻¹ * Real.log (Fintype.card α) + f.max := by
        rw [Real.log_mul hcard (Real.exp_pos _).ne', Real.log_exp, mul_add,
          inv_mul_cancel_left₀ hβ.ne']

/-- The smooth approximation error: `|β⁻¹ log ∑ₐ exp (β f a) - max_a f a| ≤ β⁻¹ log |α|`. -/
theorem abs_inv_mul_log_sum_exp_sub_max_le (hβ : 0 < β) (f : α → ℝ) :
    |β⁻¹ * Real.log (∑ a, Real.exp (β * f a)) - f.max| ≤ β⁻¹ * Real.log (Fintype.card α) := by
  have hlog : 0 ≤ β⁻¹ * Real.log (Fintype.card α) :=
    mul_nonneg (inv_nonneg.2 hβ.le) (Real.log_natCast_nonneg _)
  exact abs_le.2 ⟨by linarith [max_le_inv_mul_log_sum_exp hβ f],
    by linarith [inv_mul_log_sum_exp_le hβ f]⟩

end Deterministic

section Random

variable {α : Type*} [Fintype α] [Nonempty α] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {H : Ω → α → ℝ} {β : ℝ}

/-- The maximum of a random energy landscape with integrable coordinates is integrable, since
`|max_a H a| ≤ ∑ₐ |H a|`. -/
theorem integrable_max (hmeas : ∀ a, Measurable fun ω => H ω a)
    (hint : ∀ a, Integrable (fun ω => H ω a) μ) : Integrable (fun ω => (H ω).max) μ := by
  have hm : Measurable fun ω => (H ω).max :=
    measurable_max.comp (measurable_pi_iff.2 hmeas)
  refine Integrable.mono' (g := fun ω => ∑ b, |H ω b|)
    (integrable_finsetSum univ fun a _ => (hint a).abs) hm.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hle : ∀ a, |H ω a| ≤ ∑ b, |H ω b| := fun a =>
    Finset.single_le_sum (f := fun b => |H ω b|) (fun _ _ => abs_nonneg _) (mem_univ a)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [neg_abs_le (H ω a₀), (H ω).le_max a₀, hle a₀],
    Finset.sup'_le _ _ fun a _ => (le_abs_self _).trans (hle a)⟩

/-- The log-partition function of a random energy landscape with integrable coordinates is
integrable for `β > 0`, since `|log Z| ≤ β |max H| + log |α|`. -/
theorem integrable_log_sum_exp [IsFiniteMeasure μ] (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    Integrable (fun ω => Real.log (∑ a, Real.exp (β * H ω a))) μ := by
  have hlog : Measurable fun ω => Real.log (∑ a, Real.exp (β * H ω a)) :=
    (Finset.measurable_sum _ fun a _ => ((hmeas a).const_mul β).exp).log
  refine Integrable.mono' (((integrable_max hmeas hint).abs.const_mul β).add
    (integrable_const (Real.log (Fintype.card α)))) hlog.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h := abs_inv_mul_log_sum_exp_sub_max_le hβ (H ω)
  have hX : |β⁻¹ * Real.log (∑ a, Real.exp (β * H ω a))| ≤ |(H ω).max| +
      β⁻¹ * Real.log (Fintype.card α) := by
    linarith [abs_sub_abs_le_abs_sub (β⁻¹ * Real.log (∑ a, Real.exp (β * H ω a))) (H ω).max]
  rw [Real.norm_eq_abs]
  calc |Real.log (∑ a, Real.exp (β * H ω a))|
      = β * |β⁻¹ * Real.log (∑ a, Real.exp (β * H ω a))| := by
        rw [abs_mul, abs_inv, abs_of_pos hβ, mul_inv_cancel_left₀ hβ.ne']
    _ ≤ β * (|(H ω).max| + β⁻¹ * Real.log (Fintype.card α)) :=
        mul_le_mul_of_nonneg_left hX hβ.le
    _ = β * |(H ω).max| + Real.log (Fintype.card α) := by
        rw [mul_add, mul_inv_cancel_left₀ hβ.ne']

variable [IsProbabilityMeasure μ]

/-- **Smooth approximation, lower bound, in expectation:**
`𝔼 max_a H a ≤ β⁻¹ 𝔼 log ∑ₐ exp (β H a)` for `β > 0`. -/
theorem integral_max_le_inv_mul_integral_log_sum_exp (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    ∫ ω, (H ω).max ∂μ ≤ β⁻¹ * ∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono (integrable_max hmeas hint)
    ((integrable_log_sum_exp hβ hmeas hint).const_mul _)
    fun ω => max_le_inv_mul_log_sum_exp hβ (H ω)

/-- **Smooth approximation, upper bound, in expectation:**
`β⁻¹ 𝔼 log ∑ₐ exp (β H a) ≤ β⁻¹ log |α| + 𝔼 max_a H a` for `β > 0`. -/
theorem inv_mul_integral_log_sum_exp_le (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    β⁻¹ * ∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ ≤
      β⁻¹ * Real.log (Fintype.card α) + ∫ ω, (H ω).max ∂μ := by
  rw [← integral_const_mul]
  calc _ ≤ ∫ ω, (β⁻¹ * Real.log (Fintype.card α) + (H ω).max) ∂μ :=
        integral_mono ((integrable_log_sum_exp hβ hmeas hint).const_mul _)
          ((integrable_const _).add (integrable_max hmeas hint))
          fun ω => inv_mul_log_sum_exp_le hβ (H ω)
    _ = _ := by rw [integral_add (integrable_const _) (integrable_max hmeas hint)]; simp

/-- **Smooth approximation error in expectation:**
`|β⁻¹ 𝔼 log ∑ₐ exp (β H a) - 𝔼 max_a H a| ≤ β⁻¹ log |α|`. -/
theorem abs_inv_mul_integral_log_sum_exp_sub_integral_max_le (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    |β⁻¹ * ∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ - ∫ ω, (H ω).max ∂μ| ≤
      β⁻¹ * Real.log (Fintype.card α) := by
  have hlog : 0 ≤ β⁻¹ * Real.log (Fintype.card α) :=
    mul_nonneg (inv_nonneg.2 hβ.le) (Real.log_natCast_nonneg _)
  exact abs_le.2 ⟨by linarith [integral_max_le_inv_mul_integral_log_sum_exp hβ hmeas hint],
    by linarith [inv_mul_integral_log_sum_exp_le hβ hmeas hint]⟩

end Random

end SpinGlasses
