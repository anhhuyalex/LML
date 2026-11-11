/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.MulTranspose
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Geometry of matrix overlaps for bounded vector spins

These deterministic bounds supply the dimension dependence in Talagrand Section 1.12.
They allow different finite component types, arbitrary configurations, and a normalization
whose total mass is at most one. In particular they cover both full and cavity overlaps.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- The cross-overlap matrix has squared Frobenius norm bounded by the product of the
squared spin radii. The normalization factor `c` scales the bound quadratically. -/
theorem sum_sq_vector_overlap_le {I U V : Type*} [Fintype I] [Fintype U] [Fintype V]
    (σ : I → U → ℝ) (τ : I → V → ℝ) (c A B : ℝ)
    (hA : 0 ≤ A)
    (hσ : ∀ i, ∑ u, σ i u ^ 2 ≤ A) (hτ : ∀ i, ∑ v, τ i v ^ 2 ≤ B) :
    (∑ u, ∑ v, (c * ∑ i, σ i u * τ i v) ^ 2) ≤ (c * Fintype.card I) ^ 2 * (A * B) := by
  have hcross := Matrix.sum_sq_mul_transpose_le_sum_sq_mul_sum_sq
    (fun u i => σ i u) (fun v i => τ i v)
  have hσsum : (∑ u, ∑ i, σ i u ^ 2) ≤ Fintype.card I * A := by
    rw [sum_comm]
    exact (sum_le_sum fun i _ => hσ i).trans_eq (by simp)
  have hτsum : (∑ v, ∑ i, τ i v ^ 2) ≤ Fintype.card I * B := by
    rw [sum_comm]
    exact (sum_le_sum fun i _ => hτ i).trans_eq (by simp)
  calc
    _ = c ^ 2 * ∑ u, ∑ v, (∑ i, σ i u * τ i v) ^ 2 := by
      simp_rw [mul_pow]
      simp only [mul_sum]
    _ ≤ c ^ 2 * ((∑ u, ∑ i, σ i u ^ 2) * ∑ v, ∑ i, τ i v ^ 2) :=
      mul_le_mul_of_nonneg_left hcross (sq_nonneg c)
    _ ≤ c ^ 2 * ((Fintype.card I * A) * (Fintype.card I * B)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hσsum hτsum
          (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA)) (sq_nonneg c)
    _ = (c * Fintype.card I) ^ 2 * (A * B) := by ring

/-- The sharp dimension factor in the pointwise estimate behind Corollary 1.12.5.
No positivity or symmetry assumption on the error matrix is required. -/
theorem sq_vector_overlap_contraction_le {U V : Type*} [Fintype U] [Fintype V]
    (x : U → ℝ) (y : V → ℝ) (D : Matrix U V ℝ) (A B : ℝ)
    (hx : ∑ u, x u ^ 2 ≤ A) (hy : ∑ v, y v ^ 2 ≤ B) :
    (∑ u, ∑ v, x u * y v * D u v) ^ 2 ≤ A * B * ∑ u, ∑ v, D u v ^ 2 := by
  refine (Matrix.sq_sum_mul_mul_le x y D).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hx hy (sum_nonneg fun _ _ => sq_nonneg _)
      ((sum_nonneg fun _ _ => sq_nonneg _).trans hx))
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)

/-- Full overlaps of spins in the radius-`sqrt d` ball satisfy Eq. (1.382).
The statement also covers an empty system, where the normalized overlap is zero. -/
theorem sum_sq_sk_vector_overlap_le (N d : ℕ) (σ τ : Fin N → Fin d → ℝ)
    (hσ : ∀ i, ∑ u, σ i u ^ 2 ≤ d) (hτ : ∀ i, ∑ u, τ i u ^ 2 ≤ d) :
    (∑ u, ∑ v, ((N : ℝ)⁻¹ * ∑ i, σ i u * τ i v) ^ 2) ≤ (d : ℝ) ^ 2 := by
  have hmass : (N : ℝ)⁻¹ * Fintype.card (Fin N) ≤ 1 := by
    simp only [Fintype.card_fin]
    by_cases hN : N = 0
    · simp [hN]
    · rw [inv_mul_cancel₀ (by exact_mod_cast hN)]
  have h := sum_sq_vector_overlap_le σ τ (N : ℝ)⁻¹ d d (Nat.cast_nonneg _) hσ hτ
  refine h.trans ?_
  calc ((N : ℝ)⁻¹ * Fintype.card (Fin N)) ^ 2 * ((d : ℝ) * d)
      ≤ 1 ^ 2 * ((d : ℝ) * d) := by
        have : 0 ≤ (N : ℝ)⁻¹ * Fintype.card (Fin N) := by positivity
        gcongr
    _ = (d : ℝ) ^ 2 := by ring

/-- Cavity overlaps have the same Frobenius bound despite omitting the last spin. -/
theorem sum_sq_sk_vector_trunc_overlap_le (N d : ℕ) (σ τ : Fin N → Fin d → ℝ)
    (hσ : ∀ i, ∑ u, σ i u ^ 2 ≤ d) (hτ : ∀ i, ∑ u, τ i u ^ 2 ≤ d) :
    (∑ u, ∑ v, ((N + 1 : ℝ)⁻¹ * ∑ i, σ i u * τ i v) ^ 2) ≤ (d : ℝ) ^ 2 := by
  have hmass : (N + 1 : ℝ)⁻¹ * Fintype.card (Fin N) ≤ 1 := by
    rw [Fintype.card_fin, inv_mul_eq_div]
    exact (div_le_one (by positivity)).2 (by linarith)
  have h := sum_sq_vector_overlap_le σ τ (N + 1 : ℝ)⁻¹ d d (Nat.cast_nonneg _) hσ hτ
  refine h.trans ?_
  calc ((N + 1 : ℝ)⁻¹ * Fintype.card (Fin N)) ^ 2 * ((d : ℝ) * d)
      ≤ 1 ^ 2 * ((d : ℝ) * d) := by
        have : 0 ≤ (N + 1 : ℝ)⁻¹ * Fintype.card (Fin N) := by positivity
        gcongr
    _ = (d : ℝ) ^ 2 := by ring

/-- **A bilinear form is bounded by the Frobenius norm of its matrix.**  If `∑ Δ² ≤ ε²`,
`∑ x² ≤ a²` and `∑ w² ≤ b²` then `|∑ᵤᵥ Δᵤᵥ xᵤ wᵥ| ≤ ε a b`. -/
theorem abs_sum_bilinear_le {U V : Type*} [Fintype U] [Fintype V]
    (Δ : U → V → ℝ) (x : U → ℝ) (w : V → ℝ) {ε a b : ℝ}
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (hb : 0 ≤ b) (hΔ : ∑ u, ∑ v, Δ u v ^ 2 ≤ ε ^ 2)
    (hx : ∑ u, x u ^ 2 ≤ a ^ 2) (hw : ∑ v, w v ^ 2 ≤ b ^ 2) :
    |∑ u, ∑ v, Δ u v * (x u * w v)| ≤ ε * a * b := by
  have hrew : (∑ u, ∑ v, Δ u v * (x u * w v)) = ∑ u, ∑ v, x u * w v * Δ u v :=
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  rw [hrew]
  have h2 := sq_vector_overlap_contraction_le x w Δ (a ^ 2) (b ^ 2) hx hw
  have hle : (∑ u, ∑ v, x u * w v * Δ u v) ^ 2 ≤ (ε * a * b) ^ 2 := by
    refine h2.trans ?_
    calc a ^ 2 * b ^ 2 * (∑ u, ∑ v, Δ u v ^ 2)
        ≤ a ^ 2 * b ^ 2 * ε ^ 2 := mul_le_mul_of_nonneg_left hΔ (by positivity)
      _ = (ε * a * b) ^ 2 := by ring
  exact abs_le.2 (abs_le_of_sq_le_sq' hle (by positivity))

section SpinBounds

variable {α D : Type*} [Fintype D] {r : ℝ} (ξ : α → D → ℝ) (hr : 0 ≤ r)
  (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r)
include hr hbound

omit hr in
/-- Each coordinate of a spin of squared radius at most `r` is at most `√r` in absolute value. -/
theorem abs_spin_le (a : α) (u : D) : |ξ a u| ≤ Real.sqrt r := by
  refine Real.abs_le_sqrt ?_
  exact (Finset.single_le_sum (f := fun u => ξ a u ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ u)).trans (hbound a)

/-- Products of coordinates of two spins of squared radius at most `r` are at most `r`. -/
theorem abs_spin_mul_le (a b : α) (u v : D) : |ξ a u * ξ b v| ≤ r := by
  rw [abs_mul]
  calc |ξ a u| * |ξ b v| ≤ Real.sqrt r * Real.sqrt r :=
        mul_le_mul (abs_spin_le ξ hbound a u) (abs_spin_le ξ hbound b v) (abs_nonneg _)
          (Real.sqrt_nonneg _)
    _ = r := Real.mul_self_sqrt hr

omit [Fintype D] hr hbound in
/-- The product of two coordinates of a vector spin is measurable. -/
theorem measurable_spin_mul [MeasurableSpace α] (hξ : ∀ u, Measurable (fun a => ξ a u)) (u v : D) :
    Measurable (fun a => ξ a u * ξ a v) :=
  (hξ u).mul (hξ v)

end SpinBounds

end SpinGlasses
