/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Basic
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub
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

/-- The fixed-state energy derivative (2.27). Only differentiability of the potential is
needed. This statement does not exchange a derivative with a Gibbs or disorder integral. -/
theorem hasDerivAt_perceptron_smart_path_energy {N M : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (g : Fin M → Fin N → ℝ) (a ξ : Fin M → ℝ)
    (σ : Fin N → ℤˣ) (ε : ℤˣ) (y : ℝ) :
    let S := fun (s : ℝ) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((σ i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * a k * ((ε : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * ξ k
    HasDerivAt (fun s => ((ε : ℤ) : ℝ) * Real.sqrt (1 - s) * y + ∑ k, u (S s k))
      (-((ε : ℤ) : ℝ) * y / (2 * Real.sqrt (1 - t)) +
        ∑ k, deriv u (S t k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
          (a k * ((ε : ℤ) : ℝ) / Real.sqrt t - ξ k / Real.sqrt (1 - t)))) t := by
  intro S
  have hY := ((hasDerivAt_id t).const_sub 1).sqrt (sub_pos.mpr ht.2).ne'
  have hS (k : Fin M) := hasDerivAt_perceptron_smart_path_field ht (g k) (a k) σ ε (ξ k)
  have hU (k : Fin M) := (hu (S t k)).hasDerivAt.comp t (hS k)
  convert ((hY.const_mul ((ε : ℤ) : ℝ)).mul_const y).add
    (HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) => hU k) using 1
  · rfl
  · dsimp only [id_eq]; push_cast; ring

/-- Pointwise bound on the last-field energy derivative term. -/
theorem abs_perceptron_smart_path_E'_Y_le (ε : ℤˣ) (y t δ : ℝ)
    (hδ : 0 < δ) (ht : t ∈ Set.Icc δ (1 - δ)) :
    |-((ε : ℤ) : ℝ) * y / (2 * Real.sqrt (1 - t))| ≤ |y| / (2 * Real.sqrt δ) := by
  have ht1 : 0 < 1 - t := by linarith [ht.2, hδ]
  have hd1 : Real.sqrt δ ≤ Real.sqrt (1 - t) := Real.sqrt_le_sqrt (by linarith [ht.2])
  rw [abs_div, abs_mul, abs_neg, abs_units_cast_eq_one, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sqrt (1 - t))]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left hd1 (by norm_num))

/-- Pointwise bound on one constraint coordinate of the disorder derivative term. -/
theorem abs_perceptron_smart_path_E'_a_term_le {N : ℕ} {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ z, |deriv u z| ≤ D) (S_k a_k : ℝ) (ε : ℤˣ) (t δ : ℝ)
    (hδ : 0 < δ) (ht : t ∈ Set.Icc δ (1 - δ)) :
    |deriv u S_k * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
      (a_k * ((ε : ℤ) : ℝ) / Real.sqrt t))| ≤
      D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|a_k| / Real.sqrt δ) := by
  have ht0 : 0 < t := hδ.trans_le ht.1
  have hdt : Real.sqrt δ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1
  have hc0 := one_div_le_one_div_of_le (Real.sqrt_pos.2 hδ) hdt
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hterm : |a_k * ((ε : ℤ) : ℝ) / Real.sqrt t| ≤ |a_k| / Real.sqrt δ := by
    rw [abs_div, abs_mul, abs_units_cast_eq_one, mul_one,
      abs_of_pos (Real.sqrt_pos.2 ht0)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.2 hδ) hdt
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ))),
    ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hD _) (by positivity)) hterm
    (abs_nonneg _) (mul_nonneg hD0 (by positivity))

/-- Pointwise bound on one constraint coordinate of the auxiliary spin derivative term. -/
theorem abs_perceptron_smart_path_E'_ξ_term_le {N : ℕ} {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ z, |deriv u z| ≤ D) (S_k ξ_k : ℝ) (t δ : ℝ)
    (hδ : 0 < δ) (ht : t ∈ Set.Icc δ (1 - δ)) :
    |deriv u S_k * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
      (- ξ_k / Real.sqrt (1 - t)))| ≤
      D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ξ_k| / Real.sqrt δ) := by
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hd1 : Real.sqrt δ ≤ Real.sqrt (1 - t) := Real.sqrt_le_sqrt (by linarith [ht.2])
  have hc1 := one_div_le_one_div_of_le (Real.sqrt_pos.2 hδ) hd1
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hterm : |- ξ_k / Real.sqrt (1 - t)| ≤ |ξ_k| / Real.sqrt δ := by
    rw [abs_div, abs_neg, abs_of_pos (Real.sqrt_pos.2 ht1)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.2 hδ) hd1
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ))),
    ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hD _) (by positivity)) hterm
    (abs_nonneg _) (mul_nonneg hD0 (by positivity))

/-- On a closed interval inside `(0, 1)`, the energy derivative grows at most linearly in
the absolute values of the auxiliary coordinates. This is an integrable Gaussian envelope. -/
theorem abs_deriv_perceptron_smart_path_energy_le {N M : ℕ} {t δ : ℝ}
    (hδ : 0 < δ) (ht : t ∈ Set.Icc δ (1 - δ))
    {u : ℝ → ℝ} {D : ℝ} (hD : ∀ z, |deriv u z| ≤ D)
    (g : Fin M → Fin N → ℝ) (a ξ : Fin M → ℝ)
    (σ : Fin N → ℤˣ) (ε : ℤˣ) (y : ℝ) :
    let S := fun (s : ℝ) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((σ i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * a k * ((ε : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * ξ k
    |-((ε : ℤ) : ℝ) * y / (2 * Real.sqrt (1 - t)) +
        ∑ k, deriv u (S t k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
          (a k * ((ε : ℤ) : ℝ) / Real.sqrt t - ξ k / Real.sqrt (1 - t)))| ≤
      |y| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        ((|a k| + |ξ k|) / Real.sqrt δ) := by
  intro S
  have ht0 : 0 < t := hδ.trans_le ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hdt : Real.sqrt δ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1
  have hd1 : Real.sqrt δ ≤ Real.sqrt (1 - t) := Real.sqrt_le_sqrt (by linarith [ht.2])
  have hc0 := one_div_le_one_div_of_le (Real.sqrt_pos.2 hδ) hdt
  have hc1 := one_div_le_one_div_of_le (Real.sqrt_pos.2 hδ) hd1
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hY : |-((ε : ℤ) : ℝ) * y / (2 * Real.sqrt (1 - t))| ≤ |y| / (2 * Real.sqrt δ) :=
    abs_perceptron_smart_path_E'_Y_le ε y t δ hδ ht
  have hterm (k : Fin M) :
      |deriv u (S t k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (a k * ((ε : ℤ) : ℝ) / Real.sqrt t - ξ k / Real.sqrt (1 - t)))| ≤
        D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * ((|a k| + |ξ k|) / Real.sqrt δ) := by
    have hsub : |a k * ((ε : ℤ) : ℝ) / Real.sqrt t - ξ k / Real.sqrt (1 - t)| ≤
        (|a k| + |ξ k|) / Real.sqrt δ := by
      calc _ ≤ |a k * ((ε : ℤ) : ℝ) / Real.sqrt t| + |ξ k / Real.sqrt (1 - t)| := abs_sub _ _
        _ = |a k| * (1 / Real.sqrt t) + |ξ k| * (1 / Real.sqrt (1 - t)) := by
          simp only [abs_div, abs_mul, abs_units_cast_eq_one, mul_one,
            abs_of_pos (Real.sqrt_pos.2 ht0), abs_of_pos (Real.sqrt_pos.2 ht1)]
          ring
        _ ≤ |a k| * (1 / Real.sqrt δ) + |ξ k| * (1 / Real.sqrt δ) :=
          add_le_add (mul_le_mul_of_nonneg_left hc0 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _))
        _ = _ := by ring
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ))), ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hD _) (by positivity)) hsub
      (abs_nonneg _) (mul_nonneg hD0 (by positivity))
  exact (abs_add_le _ _).trans (add_le_add hY
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm k)))

/-- The Gaussian derivative envelope is integrable against counting times Gaussian measure. -/
theorem integrable_perceptron_smart_path_envelope {N M : ℕ} (D δ y : ℝ) (a : Fin M → ℝ) :
    Integrable (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
      |y| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        ((|a k| + |x.2 k|) / Real.sqrt δ))
      ((Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
  have h := integrable_add_sum_mul_abs_snd (M := M) (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ))
    (|y| / (2 * Real.sqrt δ) +
      ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|a k| / Real.sqrt δ))
    (fun _ => D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [add_div, mul_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by ring

end SpinGlasses
