/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Second moments of a square-integrable random vector

For a random vector `x : Ω → p → ℝ` with square-integrable coordinates and second-moment matrix
`Γ j k = E[x_j x_k]`:

* `ProbabilityTheory.integral_dotProduct_mulVec_self`: `E[xᵀ S x] = Tr (S Γ)`;
* `ProbabilityTheory.integral_dotProduct_mul_dotProduct`: `E[(x ⬝ a)(x ⬝ b)] = a ⬝ Γ b`;
* `ProbabilityTheory.integral_mul_le_half_add`: AM-GM, `E[X Y] ≤ (E[X²] + E[Y²]) / 2`.

They reduce every bilinear second-moment computation to the coordinate covariances (used for the
double-descent risk decompositions and for Gaussian matrix forms).
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped Matrix

variable {Ω p : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype p]

/-- Quadratic forms of a square-integrable random vector integrate against its second-moment
matrix. -/
theorem integral_dotProduct_mulVec_self (x : Ω → p → ℝ) (hx : ∀ j, MemLp (fun ω => x ω j) 2 μ)
    (Γ : Matrix p p ℝ) (hΓ : ∀ j k, ∫ ω, x ω j * x ω k ∂μ = Γ j k) (S : Matrix p p ℝ) :
    ∫ ω, x ω ⬝ᵥ (S *ᵥ x ω) ∂μ = Matrix.trace (S * Γ) := by
  have hexp : ∀ ω, x ω ⬝ᵥ (S *ᵥ x ω) = ∑ j, ∑ k, S j k * (x ω j * x ω k) := fun ω => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ j k, Integrable (fun ω => S j k * (x ω j * x ω k)) μ := fun j k =>
    ((hx j).integrable_mul (hx k)).const_mul _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ k, integral_const_mul, hΓ]
  have hsymm : ∀ j k, Γ k j = Γ j k := fun j k => by
    rw [← hΓ, ← hΓ]; exact integral_congr_ae (.of_forall fun ω => mul_comm _ _)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hsymm]


/-- Bilinear second-moment identity: `E[(x ⬝ a)(x ⬝ b)] = a ⬝ Γ b`. -/
theorem integral_dotProduct_mul_dotProduct (x : Ω → p → ℝ) (hx : ∀ j, MemLp (fun ω => x ω j) 2 μ)
    (Γ : Matrix p p ℝ) (hΓ : ∀ j k, ∫ ω, x ω j * x ω k ∂μ = Γ j k) (a b : p → ℝ) :
    ∫ ω, (x ω ⬝ᵥ a) * (x ω ⬝ᵥ b) ∂μ = a ⬝ᵥ (Γ *ᵥ b) := by
  have h := integral_dotProduct_mulVec_self x hx Γ hΓ (Matrix.vecMulVec b a)
  have hpt : ∀ ω, x ω ⬝ᵥ (Matrix.vecMulVec b a *ᵥ x ω) = (x ω ⬝ᵥ a) * (x ω ⬝ᵥ b) := fun ω => by
    rw [Matrix.vecMulVec_mulVec]
    simp [dotProduct_comm]
  simp_rw [hpt] at h
  rw [h, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- AM-GM for square-integrable variables: `E[X Y] ≤ (E[X²] + E[Y²]) / 2`. -/
theorem integral_mul_le_half_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ ω, X ω * Y ω ∂μ ≤ (∫ ω, X ω ^ 2 ∂μ + ∫ ω, Y ω ^ 2 ∂μ) / 2 := by
  have hXi := hX.integrable_sq
  have hYi := hY.integrable_sq
  rw [← integral_add hXi hYi, ← integral_div]
  exact integral_mono (hX.integrable_mul hY) ((hXi.add hYi).div_const 2)
    fun ω => by nlinarith [sq_nonneg (X ω - Y ω)]

end ProbabilityTheory
