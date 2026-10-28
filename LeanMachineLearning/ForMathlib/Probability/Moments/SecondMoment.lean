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
* `ProbabilityTheory.abs_integral_mul_le_weighted_add`: weighted AM-GM,
  `|E[X Y]| ≤ (l E[X²] + l⁻¹ E[Y²]) / 2`;
* `ProbabilityTheory.integral_mul_le_half_add`: AM-GM, `E[X Y] ≤ (E[X²] + E[Y²]) / 2`;
* `ProbabilityTheory.abs_integral_mul_le_of_integral_sq_le`: Cauchy-Schwarz with explicit scales.

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

/-- Weighted AM-GM for square-integrable variables:
`|E[X Y]| ≤ (l E[X²] + l⁻¹ E[Y²]) / 2` for every `l > 0`. -/
theorem abs_integral_mul_le_weighted_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {l : ℝ} (hl : 0 < l) :
    |∫ ω, X ω * Y ω ∂μ| ≤ (l * ∫ ω, X ω ^ 2 ∂μ + l⁻¹ * ∫ ω, Y ω ^ 2 ∂μ) / 2 := by
  have hXi := hX.integrable_sq
  have hYi := hY.integrable_sq
  have hXY := hX.integrable_mul hY
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hXi.const_mul l)
    (hYi.const_mul l⁻¹), ← integral_div]
  refine (abs_integral_le_integral_abs).trans (integral_mono hXY.abs
    (((hXi.const_mul l).add (hYi.const_mul l⁻¹)).div_const 2) fun ω => ?_)
  have h1 : (l * X ω - Y ω) ^ 2 / l = l * X ω ^ 2 + l⁻¹ * Y ω ^ 2 - 2 * (X ω * Y ω) := by
    field_simp
    ring
  have h2 : 0 ≤ (l * X ω - Y ω) ^ 2 / l := by positivity
  have h3 : (l * X ω + Y ω) ^ 2 / l = l * X ω ^ 2 + l⁻¹ * Y ω ^ 2 + 2 * (X ω * Y ω) := by
    field_simp
    ring
  have h4 : 0 ≤ (l * X ω + Y ω) ^ 2 / l := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- AM-GM for square-integrable variables: `E[X Y] ≤ (E[X²] + E[Y²]) / 2`. -/
theorem integral_mul_le_half_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ ω, X ω * Y ω ∂μ ≤ (∫ ω, X ω ^ 2 ∂μ + ∫ ω, Y ω ^ 2 ∂μ) / 2 := by
  simpa using (le_abs_self _).trans (abs_integral_mul_le_weighted_add hX hY one_pos)

/-- **Cauchy-Schwarz with explicit scales:** if `E[X²] ≤ α²` and `E[Y²] ≤ γ²` with `α, γ > 0`,
then `|E[X Y]| ≤ α γ`. -/
theorem abs_integral_mul_le_of_integral_sq_le {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hXb : ∫ ω, X ω ^ 2 ∂μ ≤ α ^ 2)
    (hYb : ∫ ω, Y ω ^ 2 ∂μ ≤ γ ^ 2) : |∫ ω, X ω * Y ω ∂μ| ≤ α * γ := by
  refine (abs_integral_mul_le_weighted_add hX hY (div_pos hγ hα)).trans ?_
  have h1 : γ / α * ∫ ω, X ω ^ 2 ∂μ ≤ γ / α * α ^ 2 :=
    mul_le_mul_of_nonneg_left hXb (div_pos hγ hα).le
  have h2 : (γ / α)⁻¹ * ∫ ω, Y ω ^ 2 ∂μ ≤ (γ / α)⁻¹ * γ ^ 2 :=
    mul_le_mul_of_nonneg_left hYb (inv_pos.2 (div_pos hγ hα)).le
  have h3 : γ / α * α ^ 2 = α * γ := by field_simp
  have h4 : (γ / α)⁻¹ * γ ^ 2 = α * γ := by field_simp
  linarith

end ProbabilityTheory
