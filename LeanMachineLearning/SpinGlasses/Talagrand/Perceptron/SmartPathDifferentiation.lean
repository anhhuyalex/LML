/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Basic
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
  have hL : (0 : ℝ) < N + 1 := by positivity
  have hcoeff {z : ℝ} (hz : 0 < z) :
      (1 / (2 * Real.sqrt (z / (N + 1))) / (N + 1)) =
        (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt z := by
    have hLs : Real.sqrt (N + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
    have hzs : Real.sqrt z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
    rw [Real.sqrt_div hz.le]
    push_cast
    field_simp
    nlinarith [Real.sq_sqrt hL.le]
  have ht0 : t / (N + 1 : ℝ) ≠ 0 := div_ne_zero ht.1.ne' hL.ne'
  have ht1 : (1 - t) / (N + 1 : ℝ) ≠ 0 := div_ne_zero (sub_pos.mpr ht.2).ne' hL.ne'
  have hp := ((hasDerivAt_id t).div_const (N + 1 : ℝ)).sqrt ht0
  have hm := (((hasDerivAt_id t).const_sub 1).div_const (N + 1 : ℝ)).sqrt ht1
  convert (hp.mul_const a |>.mul_const ((ε : ℤ) : ℝ) |>.const_add
    ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g i * ((σ i : ℤ) : ℝ)))).add
    (hm.mul_const ξ) using 1
  · rfl
  · dsimp only [id_eq]
    rw [show 1 / (N + 1 : ℝ) / (2 * Real.sqrt (t / (N + 1))) =
        1 / (2 * Real.sqrt (t / (N + 1))) / (N + 1) by ring,
      show -1 / (N + 1 : ℝ) / (2 * Real.sqrt ((1 - t) / (N + 1))) =
        -(1 / (2 * Real.sqrt ((1 - t) / (N + 1))) / (N + 1)) by ring,
      hcoeff ht.1, hcoeff (sub_pos.mpr ht.2)]
    ring

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
  · dsimp only [id_eq]
    ring

end SpinGlasses
