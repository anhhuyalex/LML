/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathModel
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub
public import LeanMachineLearning.ForMathlib.Analysis.RatioBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Differentiating the perceptron smart-path fields and energy

Talagrand (2.15), (2.22) and (2.27), at fixed disorder and fixed configuration. The full
system size is `N + 1`; there may be no old coordinates or no constraints. Square roots
are differentiated only for `0 < t < 1`. The potential need only be differentiable for
this calculation; no boundedness or second derivative is needed until later analytic steps.

These are pointwise derivatives. Differentiating the normalized replica and disorder
averages also requires integrable bounds, and is a separate statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SpinGlasses

/-- The parameter derivative of a fixed-spin field in (2.15), with full size `N + 1`. -/
theorem hasDerivAt_perceptron_smart_path_field {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (g : Fin N → ℝ) (a : ℝ)
    (σ : Fin N → ℤˣ) (ε : ℤˣ) (ξ : ℝ) :
    HasDerivAt
      (fun s => (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g i * ((σ i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * a * ((ε : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * ξ)
      ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (a * ((ε : ℤ) : ℝ) / Real.sqrt t - ξ / Real.sqrt (1 - t))) t := by
  have hL : (0 : ℝ) ≤ N + 1 := by positivity
  have hp := Real.hasDerivAt_sqrt_div_const hL ht.1.ne'
  have hm := (Real.hasDerivAt_sqrt_div_const hL (sub_pos.mpr ht.2).ne').comp t
    ((hasDerivAt_id t).const_sub 1)
  convert (hp.mul_const a |>.mul_const ((ε : ℤ) : ℝ) |>.const_add
    ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g i * ((σ i : ℤ) : ℝ)))).add
    (hm.mul_const ξ) using 1
  · rfl
  · push_cast; ring

/-- The fixed-state energy derivative (2.27), split into the three pieces `E'_a + E'_ξ + E'_Y`.
Only differentiability of the potential is needed. This statement does not exchange a derivative
with a Gibbs or disorder integral. -/
theorem hasDerivAt_smartPathEnergy {N M : ℕ} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) :
    HasDerivAt (fun s => smartPathEnergy u s ω x)
      (smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
        smartPathEnergyDerivY t ω x) t := by
  have hY := ((hasDerivAt_id t).const_sub 1).sqrt (sub_pos.mpr ht.2).ne'
  have hS (k : Fin M) := hasDerivAt_perceptron_smart_path_field ht (ω.1.1 k) (ω.1.2 k) x.1.1
    x.1.2 (x.2 k)
  have hU (k : Fin M) := (hu (smartPathField t ω x k)).hasDerivAt.comp t (hS k)
  convert ((hY.const_mul ((x.1.2 : ℤ) : ℝ)).mul_const ω.2).add
    (HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) => hU k) using 1
  · rfl
  · simp only [smartPathEnergyDerivA, smartPathEnergyDerivXi, smartPathEnergyDerivY,
      id_eq, ← Finset.sum_add_distrib]
    rw [add_comm]
    push_cast
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring

/-- Pointwise bound on the last-field term of the energy derivative on `δ ≤ 1 - t`. -/
theorem abs_smartPathEnergyDerivY_le {N M : ℕ} {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ 1 - t)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
    |smartPathEnergyDerivY t ω x| ≤ |ω.2| / (2 * Real.sqrt δ) := by
  unfold smartPathEnergyDerivY
  have hx : |-((x.1.2 : ℤ) : ℝ) * ω.2| = |ω.2| := by
    rw [abs_mul, abs_neg, abs_units_cast_eq_one, one_mul]
  have h2 : 0 < 2 * Real.sqrt δ := by have := Real.sqrt_pos.2 hδ; positivity
  refine abs_div_le_div_of_le_abs h2 ?_ hx.le
  rw [abs_of_nonneg (by positivity)]
  have := Real.sqrt_le_sqrt hδt
  linarith

/-- Pointwise bound on the quenched-disorder term of the energy derivative on `δ ≤ t`. -/
theorem abs_smartPathEnergyDerivA_le {N M : ℕ} {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ z, |deriv u z| ≤ D) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
    |smartPathEnergyDerivA u t ω x| ≤
      ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt δ) := by
  unfold smartPathEnergyDerivA
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hterm : |ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t| ≤ |ω.1.2 k| / Real.sqrt δ := by
    simpa only [abs_mul, abs_units_cast_eq_one, mul_one] using
      abs_div_sqrt_le_abs_div_sqrt (ω.1.2 k * ((x.1.2 : ℤ) : ℝ)) t δ hδ hδt
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ))),
    ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hD _) (by positivity)) hterm
    (abs_nonneg _) (mul_nonneg hD0 (by positivity))

/-- Pointwise bound on the auxiliary-spin term of the energy derivative on `δ ≤ 1 - t`. -/
theorem abs_smartPathEnergyDerivXi_le {N M : ℕ} {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ z, |deriv u z| ≤ D) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ 1 - t)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
    |smartPathEnergyDerivXi u t ω x| ≤
      ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|x.2 k| / Real.sqrt δ) := by
  unfold smartPathEnergyDerivXi
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hterm : |- x.2 k / Real.sqrt (1 - t)| ≤ |x.2 k| / Real.sqrt δ := by
    rw [neg_div, abs_neg]
    exact abs_div_sqrt_le_abs_div_sqrt (x.2 k) (1 - t) δ hδ hδt
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ))),
    ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hD _) (by positivity)) hterm
    (abs_nonneg _) (mul_nonneg hD0 (by positivity))

/-- On a closed interval inside `(0, 1)`, the energy derivative grows at most linearly in
the absolute values of the auxiliary coordinates. This is an integrable Gaussian envelope. -/
theorem abs_deriv_perceptron_smart_path_energy_le {N M : ℕ} {t δ : ℝ}
    (hδ : 0 < δ) (ht : t ∈ Set.Icc δ (1 - δ)) {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ z, |deriv u z| ≤ D) (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
    |smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
        smartPathEnergyDerivY t ω x| ≤
      |ω.2| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ) := by
  have hδ1 : δ ≤ 1 - t := by linarith [ht.2]
  have hA := abs_smartPathEnergyDerivA_le hD hδ ht.1 ω x
  have hX := abs_smartPathEnergyDerivXi_le hD hδ hδ1 ω x
  have hY := abs_smartPathEnergyDerivY_le hδ hδ1 ω x
  have h1 : |smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
      smartPathEnergyDerivY t ω x| ≤ |smartPathEnergyDerivA u t ω x| +
      |smartPathEnergyDerivXi u t ω x| + |smartPathEnergyDerivY t ω x| :=
    (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hsum : ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt δ) +
      ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|x.2 k| / Real.sqrt δ) =
      ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

/-- The Gaussian derivative envelope is integrable against counting times Gaussian measure. -/
theorem integrable_perceptron_smart_path_envelope {N M : ℕ} (D δ y : ℝ) (a : Fin M → ℝ) :
    Integrable (fun x : SmartPathState N M =>
      |y| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        ((|a k| + |x.2 k|) / Real.sqrt δ)) (smartPathBase N M) := by
  have h := integrable_add_sum_mul_abs_snd (M := M) (Measure.count : Measure (PerceptronSpin N))
    (|y| / (2 * Real.sqrt δ) +
      ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|a k| / Real.sqrt δ))
    (fun _ => D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [add_div, mul_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The energy is affine in the last field `y = ω.2`: its derivative is
`√(1 - t) ε` (`ε` the last spin), at any `t`. -/
theorem hasDerivAt_smartPathEnergy_lastField {N M : ℕ} (u : ℝ → ℝ) (t : ℝ)
    (ω₀ : (Fin M → Fin N → ℝ) × (Fin M → ℝ)) (x : SmartPathState N M) (y : ℝ) :
    HasDerivAt (fun r => smartPathEnergy u t (ω₀, r) x)
      (Real.sqrt (1 - t) * ((x.1.2 : ℤ) : ℝ)) y := by
  have h := ((hasDerivAt_id y).const_mul (((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t))).add_const
    (∑ k, u (smartPathField t (ω₀, y) x k))
  have hf : (fun r => smartPathEnergy u t (ω₀, r) x) = fun r =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * id r + ∑ k, u (smartPathField t (ω₀, y) x k) := rfl
  rw [hf]
  convert h using 1
  simp [mul_comm]

end SpinGlasses
