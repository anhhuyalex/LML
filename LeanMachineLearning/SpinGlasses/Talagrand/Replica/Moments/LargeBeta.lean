/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.RpowTsum
public import LeanMachineLearning.SpinGlasses.Talagrand.DecoupledSystems.SKFirstMoment
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Moments.Concentration

/-!
# An upper bound on the quenched free energy, and failure of the `q = 0` formula at large `β`

Talagrand, end of Section 1.13 and the first paragraph of Section 1.14: the replica-symmetric
formula (1.411) cannot hold at every temperature.  At zero field the fixed-point equation
`q = 𝔼 tanh² (β z √q)` always has the root `q = 0`, for which the right-hand side of (1.411) is
`β² / 4 + log 2`, the annealed value.

## Mathematical overview

For `0 < t ≤ 1`, `x ↦ x ^ t` is subadditive, so `Z_N ^ t ≤ ∑_σ exp (t H(σ))` and, by the exact
Gaussian computation of `integral_sum_exp_mul_sk_energy`,
`𝔼 Z_N ^ t ≤ (2 cosh (t h)) ^ N exp (t² N (β² / 4)(1 - 1 / N))`.
Together with the lower half of the quadratic sandwich of `Moments/Concentration.lean`,
`t p_N ≤ ψ_N(t)`, this gives, for every `N ≥ 1`, all real `β`, `h` and `t ∈ (0, 1]`,

`p_N ≤ t⁻¹ log (2 cosh (t h)) + t β² / 4`,  with `p_N = N⁻¹ 𝔼 log Z_N`.

At `t = 1` this is the annealed bound.  At `h = 0` and `|β| ≥ 2 √(log 2)` the choice
`t = 2 √(log 2) / |β|` gives `p_N ≤ |β| √(log 2)`, which is strictly smaller than
`β² / 4 + log 2` unless `|β| = 2 √(log 2)`, because
`β² / 4 + log 2 - |β| √(log 2) = (|β| / 2 - √(log 2))²`.

## Main declarations

* `SpinGlasses.log_integral_rpow_skPartition_le`: `log 𝔼 Z_N ^ t ≤ N log (2 cosh (t h)) + …`.
* `SpinGlasses.inv_mul_integral_log_skPartition_le`: `p_N ≤ t⁻¹ log (2 cosh (t h)) + t β² / 4`.
* `SpinGlasses.inv_mul_integral_log_skPartition_le_abs_mul_sqrt_log_two`: at `h = 0`,
  `p_N ≤ |β| √(log 2)` for `|β| ≥ 2 √(log 2)`.
* `SpinGlasses.inv_mul_integral_log_skPartition_lt_annealed`: that bound is strictly below the
  `q = 0` value `β² / 4 + log 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SpinGlasses

variable {N : ℕ}

/-- **Upper bound on the real moments of the SK partition function.**  For `0 < t ≤ 1`,
`log 𝔼 Z_N ^ t ≤ N log (2 cosh (t h)) + t² N (β² / 4)(1 - 1 / N)`: the subadditivity of
`x ↦ x ^ t` reduces `𝔼 Z_N ^ t` to the exact Gaussian moments `𝔼 exp (t H(σ))`. -/
theorem log_integral_rpow_skPartition_le (hN : 0 < N) (β h : ℝ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    Real.log (∫ g : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ≤
      (N : ℝ) * Real.log (2 * Real.cosh (t * h)) +
        t ^ 2 * ((N : ℝ) * (β ^ 2 / 4 * (1 - (N : ℝ)⁻¹))) := by
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  have hpt (g : FinPairs N → ℝ) :
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t ≤
        ∑ σ : Fin N → ℤˣ, Real.exp (t * skGibbsEnergy N β h g σ) := by
    refine (Real.rpow_sum_le_sum_rpow Finset.univ _ (fun σ _ => (Real.exp_pos _).le) ht0 ht1).trans
      (le_of_eq (Finset.sum_congr rfl fun σ _ => ?_))
    rw [← Real.exp_mul, mul_comm]
  have hrpow : (fun g : FinPairs N → ℝ =>
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t) = fun g =>
      Real.exp (t * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))) := by
    ext g
    rw [Real.rpow_def_of_pos (skPartition_pos N β h g), mul_comm]
  have hint1 : Integrable (fun g : FinPairs N → ℝ =>
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t) P := by
    rw [hrpow]
    exact integrable_exp_mul_log_skPartition N β h t
  have hint2 : Integrable (fun g : FinPairs N → ℝ =>
      ∑ σ : Fin N → ℤˣ, Real.exp (t * skGibbsEnergy N β h g σ)) P :=
    integrable_finsetSum _ fun σ _ => integrable_exp_mul_sk_energy β h t σ
  have hmono := integral_mono hint1 hint2 hpt
  have hexact := integral_sum_exp_mul_sk_energy hN β h t
  have hpos : 0 < ∫ g : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t ∂P := by
    rw [hrpow]
    exact mgf_pos (X := fun g : FinPairs N → ℝ =>
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)))
      (integrable_exp_mul_log_skPartition N β h t)
  refine (Real.log_le_log hpos (hmono.trans_eq hexact)).trans_eq ?_
  have hc : 0 < 2 * Real.cosh (t * h) := mul_pos two_pos (Real.cosh_pos _)
  rw [Real.log_mul (pow_pos hc N).ne' (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]

/-- **Upper bound on the quenched free energy from the real moments.**  For `N ≥ 1`, all real
`β, h` and `0 < t ≤ 1`,
`N⁻¹ 𝔼 log Z_N ≤ t⁻¹ log (2 cosh (t h)) + t β² / 4`.  At `t = 1` this is the annealed bound. -/
theorem inv_mul_integral_log_skPartition_le (hN : 0 < N) (β h : ℝ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      t⁻¹ * Real.log (2 * Real.cosh (t * h)) + t * β ^ 2 / 4 := by
  have hlow := (inv_mul_log_integral_rpow_skPartition_sandwich (N := N) β h hN t).1
  have hup := log_integral_rpow_skPartition_le hN β h ht0 ht1
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN0.le
  set L := Real.log (2 * Real.cosh (t * h))
  have hscale : (N : ℝ)⁻¹ * ((N : ℝ) * L + t ^ 2 * ((N : ℝ) * (β ^ 2 / 4 * (1 - (N : ℝ)⁻¹)))) =
      L + t ^ 2 * (β ^ 2 / 4) * (1 - (N : ℝ)⁻¹) := by
    field_simp
  have hfac : t ^ 2 * (β ^ 2 / 4) * (1 - (N : ℝ)⁻¹) ≤ t ^ 2 * (β ^ 2 / 4) :=
    mul_le_of_le_one_right (by positivity) (by linarith)
  have h1 : t * ((N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ≤ L + t ^ 2 * (β ^ 2 / 4) :=
    hlow.trans ((mul_le_mul_of_nonneg_left hup hNinv).trans (by rw [hscale]; linarith))
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht0.le)
  rw [← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul, mul_add] at h2
  refine h2.trans_eq ?_
  field_simp

/-- **The annealed bound improves with the exponent (zero field).**  At `h = 0` and
`|β| ≥ 2 √(log 2)` the choice `t = 2 √(log 2) / |β|` in `inv_mul_integral_log_skPartition_le`
gives `N⁻¹ 𝔼 log Z_N ≤ |β| √(log 2)`, for every `N ≥ 1`. -/
theorem inv_mul_integral_log_skPartition_le_abs_mul_sqrt_log_two (hN : 0 < N) {β : ℝ}
    (hβ : 2 * Real.sqrt (Real.log 2) ≤ |β|) :
    (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β 0 g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      |β| * Real.sqrt (Real.log 2) := by
  have hL : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 (Real.log_pos one_lt_two)
  have hβpos : 0 < |β| := lt_of_lt_of_le (by positivity) hβ
  have ht0 : 0 < 2 * Real.sqrt (Real.log 2) / |β| := by positivity
  have ht1 : 2 * Real.sqrt (Real.log 2) / |β| ≤ 1 := (div_le_one hβpos).2 hβ
  refine (inv_mul_integral_log_skPartition_le hN β 0 ht0 ht1).trans_eq ?_
  have hsq : Real.sqrt (Real.log 2) ^ 2 = Real.log 2 := Real.sq_sqrt (Real.log_pos one_lt_two).le
  have hb2 : β ^ 2 = |β| ^ 2 := (sq_abs β).symm
  rw [mul_zero, Real.cosh_zero, mul_one, hb2]
  set s := Real.sqrt (Real.log 2) with hs
  rw [← hsq]
  field_simp
  ring

/-- **Failure of the `q = 0` replica-symmetric value at large `β` (zero field).**  For `h = 0`,
`|β| > 2 √(log 2)` and every `N ≥ 1`, the quenched free energy `N⁻¹ 𝔼 log Z_N` is at most
`|β| √(log 2)`, which is strictly smaller than `β² / 4 + log 2`, the value of the right-hand side
of Eq. (1.411) at the root `q = 0` of `q = 𝔼 tanh² (β z √q)` (equivalently the annealed value,
`integral_sk_partition_function_eq`).  Any limit of `p_N` is therefore strictly below that value.
This concerns the branch `q = 0` only; it does not decide whether (1.411) holds with another
solution `q > 0`. -/
theorem inv_mul_integral_log_skPartition_lt_annealed (hN : 0 < N) {β : ℝ}
    (hβ : 2 * Real.sqrt (Real.log 2) < |β|) :
    (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β 0 g σ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) <
      β ^ 2 / 4 + Real.log 2 := by
  refine lt_of_le_of_lt (inv_mul_integral_log_skPartition_le_abs_mul_sqrt_log_two hN hβ.le) ?_
  have hsq : Real.sqrt (Real.log 2) ^ 2 = Real.log 2 := Real.sq_sqrt (Real.log_pos one_lt_two).le
  have hb2 : β ^ 2 = |β| ^ 2 := (sq_abs β).symm
  have hpos : 0 < (|β| / 2 - Real.sqrt (Real.log 2)) ^ 2 := by
    have : 0 < |β| / 2 - Real.sqrt (Real.log 2) := by linarith
    positivity
  nlinarith [hsq, hb2]

end SpinGlasses
