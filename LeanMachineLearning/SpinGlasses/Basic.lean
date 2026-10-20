/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Spin configurations and the overlap

Spin configurations of the Sherrington-Kirkpatrick model [Panchenko, 2013, §1.1] are the points of
the hypercube `Σ_ι = {-1, +1}^ι`.  This file fixes the conventions used throughout `SpinGlasses`
and proves the elementary properties of the central order parameter, the *overlap*
`R(σ¹, σ²) = |ι|⁻¹ ∑ᵢ σ¹ᵢ σ²ᵢ = (Fintype.card ι : ℝ)⁻¹ * (σ¹ ⬝ᵥ σ²)` ([Panchenko, 2013, Eq. (1.2)]).

* a configuration is a function `σ : ι → ℤˣ` (the units `ℤˣ = {1, -1}`), read as the real vector
  `fun i => (σ i : ℝ)` when sums are formed; the statements below hold for arbitrary real vectors
  `σ : ι → ℝ`, with `∀ i, σ i ^ 2 = 1` (or `|σ i| ≤ 1`) assumed only where it is needed;
* the overlap is the explicit expression `(Fintype.card ι : ℝ)⁻¹ * (σ¹ ⬝ᵥ σ²)`; it is not named,
  since it is a one-line expression in `⬝ᵥ`, and so it is stated for arbitrary real vectors and
  serves the hypercube, its convex hull and the sphere alike;
* its symmetry is `dotProduct_comm`, and its invariance under orthogonal transformations is
  `Matrix.mulVec_dotProduct_mulVec_of_transpose_mul_self` (`ForMathlib/.../MulTranspose.lean`);
* the uniform probability measure on the hypercube is `MeasureTheory.empiricalMeasure id`
  (`ForMathlib/MeasureTheory/Measure/Empirical.lean`), the empirical measure of the family of all
  configurations;
* the index type `ι` is an arbitrary finite type, with `N = Fintype.card ι`.

## Main declarations

* `SpinGlasses.card_inv_mul_dotProduct_self_eq_one`: the self-overlap is `1` on the hypercube.
* `SpinGlasses.abs_card_inv_mul_dotProduct_le_one`: the overlap is at most `1` in absolute value
  when the coordinates lie in `[-1, 1]`.
* `SpinGlasses.card_spin_configurations`: the hypercube has `2 ^ N` points.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.1.
* [D. Sherrington, S. Kirkpatrick, *Solvable model of a spin-glass*, Phys. Rev. Lett. 35, 1975].
-/

@[expose] public section

open Matrix

namespace SpinGlasses

variable {ι : Type*} [Fintype ι]

/-- **The self-overlap of a configuration of the hypercube is `1`:**
`N⁻¹ (σ ⬝ σ) = 1` whenever `σᵢ² = 1` for all `i`. -/
theorem card_inv_mul_dotProduct_self_eq_one [Nonempty ι] (σ : ι → ℝ) (hσ : ∀ i, σ i ^ 2 = 1) :
    (Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ σ) = 1 := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [dotProduct, ← sq, hσ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hN

/-- **The overlap is at most one:** if all coordinates lie in `[-1, 1]` then
`|N⁻¹ (σ ⬝ τ)| ≤ 1`. Each term `|σᵢ τᵢ|` is at most `1`, so no Cauchy-Schwarz is needed. -/
theorem abs_card_inv_mul_dotProduct_le_one [Nonempty ι] (σ τ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 1)
    (hτ : ∀ i, |τ i| ≤ 1) : |(Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)| ≤ 1 := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hsum : |σ ⬝ᵥ τ| ≤ Fintype.card ι :=
    calc |σ ⬝ᵥ τ| ≤ ∑ i, |σ i * τ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact (mul_le_mul (hσ i) (hτ i) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
      _ = Fintype.card ι := by simp
  rw [abs_mul, abs_inv, Nat.abs_cast]
  exact (inv_mul_le_iff₀ hN).2 (by simpa using hsum)

/-- The coordinates of a hypercube configuration have absolute value `1`, hence lie in
`[-1, 1]`. -/
theorem abs_units_cast_le_one (u : ℤˣ) : |((u : ℤ) : ℝ)| ≤ 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- The coordinates of a hypercube configuration have absolute value exactly `1`. -/
theorem abs_units_cast_eq_one (u : ℤˣ) : |((u : ℤ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- The coordinates of a hypercube configuration square to `1`. -/
theorem units_cast_sq (u : ℤˣ) : ((u : ℤ) : ℝ) ^ 2 = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- The hypercube `ι → ℤˣ` of spin configurations has `2 ^ N` points. -/
theorem card_spin_configurations [DecidableEq ι] :
    Fintype.card (ι → ℤˣ) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun, Fintype.card_units_int]

end SpinGlasses
