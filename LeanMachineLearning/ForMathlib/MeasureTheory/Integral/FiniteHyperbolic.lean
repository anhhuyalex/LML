/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals of hyperbolic functions

For a measure `μ`, the integrals of `sinh (u + h)` and `cosh (u + h)` (with a vector-valued
weight) are linear combinations of the integrals of `exp (±u)`; the integral of `cosh u` is at
least the total mass, and `|∫ sinh u| ≤ ∫ cosh u`. The statements for a probability measure on a
finite space are the special cases where every function is integrable.
-/

@[expose] public section

open MeasureTheory

section General

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Measure α)

/-- The integral of `sinh (u + h) • Ψ` in terms of the integrals of `exp (±u) • Ψ`. -/
theorem integral_sinh_add_smul (Ψ : α → E) (u : α → ℝ) (h : ℝ)
    (hp : Integrable (fun a => Real.exp (u a) • Ψ a) μ)
    (hm : Integrable (fun a => Real.exp (-u a) • Ψ a) μ) :
    ∫ a, Real.sinh (u a + h) • Ψ a ∂μ =
      (2 : ℝ)⁻¹ • (Real.exp h • (∫ a, Real.exp (u a) • Ψ a ∂μ) -
        Real.exp (-h) • ∫ a, Real.exp (-u a) • Ψ a ∂μ) := by
  have heq : (fun a => Real.sinh (u a + h) • Ψ a) = fun a => (2 : ℝ)⁻¹ •
      (Real.exp h • (Real.exp (u a) • Ψ a) - Real.exp (-h) • (Real.exp (-u a) • Ψ a)) := by
    ext a
    rw [Real.sinh_add_eq_exp, smul_smul, smul_smul, ← sub_smul, smul_smul]
    congr 1
    ring
  have h1 : Integrable (fun a => Real.exp h • (Real.exp (u a) • Ψ a)) μ := hp.smul _
  have h2 : Integrable (fun a => Real.exp (-h) • (Real.exp (-u a) • Ψ a)) μ := hm.smul _
  rw [heq, integral_smul, integral_sub h1 h2, integral_smul, integral_smul]

/-- The integral of `cosh (u + h) • Ψ` in terms of the integrals of `exp (±u) • Ψ`. -/
theorem integral_cosh_add_smul (Ψ : α → E) (u : α → ℝ) (h : ℝ)
    (hp : Integrable (fun a => Real.exp (u a) • Ψ a) μ)
    (hm : Integrable (fun a => Real.exp (-u a) • Ψ a) μ) :
    ∫ a, Real.cosh (u a + h) • Ψ a ∂μ =
      (2 : ℝ)⁻¹ • (Real.exp h • (∫ a, Real.exp (u a) • Ψ a ∂μ) +
        Real.exp (-h) • ∫ a, Real.exp (-u a) • Ψ a ∂μ) := by
  have heq : (fun a => Real.cosh (u a + h) • Ψ a) = fun a => (2 : ℝ)⁻¹ •
      (Real.exp h • (Real.exp (u a) • Ψ a) + Real.exp (-h) • (Real.exp (-u a) • Ψ a)) := by
    ext a
    rw [Real.cosh_add_eq_exp, smul_smul, smul_smul, ← add_smul, smul_smul]
    congr 1
    ring
  have h1 : Integrable (fun a => Real.exp h • (Real.exp (u a) • Ψ a)) μ := hp.smul _
  have h2 : Integrable (fun a => Real.exp (-h) • (Real.exp (-u a) • Ψ a)) μ := hm.smul _
  rw [heq, integral_smul, integral_add h1 h2, integral_smul, integral_smul]

/-- The total mass of a finite measure is at most `∫ cosh u`. -/
theorem measureReal_univ_le_integral_cosh [IsFiniteMeasure μ] {u : α → ℝ}
    (hu : Integrable (fun a => Real.cosh (u a)) μ) :
    μ.real Set.univ ≤ ∫ a, Real.cosh (u a) ∂μ := by
  have h1 : μ.real Set.univ = ∫ _ : α, (1 : ℝ) ∂μ := by simp
  rw [h1]
  exact integral_mono (integrable_const 1) hu fun a => Real.one_le_cosh (u a)

/-- `|∫ sinh u| ≤ ∫ cosh u` as soon as `cosh u` is integrable. -/
theorem abs_integral_sinh_le_integral_cosh_of_integrable {u : α → ℝ}
    (hu : Integrable (fun a => Real.cosh (u a)) μ) :
    |∫ a, Real.sinh (u a) ∂μ| ≤ ∫ a, Real.cosh (u a) ∂μ :=
  abs_integral_le_integral_abs.trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    hu (ae_of_all _ fun a => Real.abs_sinh_le_cosh (u a)))

/-- `|∫ φ w| ≤ C ∫ w` for an integrable weight `w ≥ 0` and `|φ| ≤ C`. -/
theorem abs_integral_mul_le_mul_integral_of_integrable {φ w : α → ℝ} (hw : 0 ≤ᵐ[μ] w)
    (hwi : Integrable w μ) {C : ℝ} (hφ : ∀ᵐ a ∂μ, |φ a| ≤ C) :
    |∫ a, φ a * w a ∂μ| ≤ C * ∫ a, w a ∂μ := by
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ => abs_nonneg _) (hwi.const_mul C) ?_)
  filter_upwards [hw, hφ] with a h1 h2
  rw [abs_mul, abs_of_nonneg h1]
  exact mul_le_mul_of_nonneg_right h2 h1

/-- `∫ cosh u > 0` for a nonzero finite measure. -/
theorem integral_cosh_pos [IsFiniteMeasure μ] [NeZero μ] {u : α → ℝ}
    (hu : Integrable (fun a => Real.cosh (u a)) μ) : 0 < ∫ a, Real.cosh (u a) ∂μ :=
  measureReal_univ_pos.trans_le (measureReal_univ_le_integral_cosh μ hu)

/-- `|(∫ sinh u) / ∫ cosh u| ≤ 1` for a nonzero finite measure. -/
theorem abs_integral_sinh_div_integral_cosh_le_of_integrable [IsFiniteMeasure μ] [NeZero μ]
    {u : α → ℝ} (hu : Integrable (fun a => Real.cosh (u a)) μ) :
    |(∫ a, Real.sinh (u a) ∂μ) / ∫ a, Real.cosh (u a) ∂μ| ≤ 1 := by
  have hD := integral_cosh_pos μ hu
  rw [abs_div, abs_of_pos hD, div_le_one hD]
  exact abs_integral_sinh_le_integral_cosh_of_integrable μ hu

/-- `|(∫ φ cosh u) / ∫ cosh u| ≤ C` for a nonzero finite measure and `|φ| ≤ C`. -/
theorem abs_integral_mul_cosh_div_le_of_integrable [IsFiniteMeasure μ] [NeZero μ]
    {φ u : α → ℝ} (hu : Integrable (fun a => Real.cosh (u a)) μ) {C : ℝ}
    (hφ : ∀ᵐ a ∂μ, |φ a| ≤ C) :
    |(∫ a, φ a * Real.cosh (u a) ∂μ) / ∫ a, Real.cosh (u a) ∂μ| ≤ C := by
  have hD := integral_cosh_pos μ hu
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  exact abs_integral_mul_le_mul_integral_of_integrable μ
    (ae_of_all _ fun a => (Real.cosh_pos _).le) hu hφ

end General

section Finite

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [IsProbabilityMeasure μ] [Finite α]

omit [IsProbabilityMeasure μ] in
/-- The integral of `Ψ * sinh (u + h)` against a finite measure on a finite space. -/
theorem integral_mul_sinh_add [IsFiniteMeasure μ] (Ψ u : α → ℝ) (h : ℝ) :
    ∫ a, Ψ a * Real.sinh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Ψ a * Real.exp (u a) ∂μ) -
        Real.exp (-h) * (∫ a, Ψ a * Real.exp (-u a) ∂μ)) / 2 := by
  have h1 := integral_sinh_add_smul μ Ψ u h Integrable.of_finite Integrable.of_finite
  simpa only [smul_eq_mul, mul_comm (Real.sinh _), mul_comm (Real.exp (u _)),
    mul_comm (Real.exp (-u _)), div_eq_inv_mul] using h1

omit [IsProbabilityMeasure μ] in
/-- The integral of `Ψ * cosh (u + h)` against a finite measure on a finite space. -/
theorem integral_mul_cosh_add [IsFiniteMeasure μ] (Ψ u : α → ℝ) (h : ℝ) :
    ∫ a, Ψ a * Real.cosh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Ψ a * Real.exp (u a) ∂μ) +
        Real.exp (-h) * (∫ a, Ψ a * Real.exp (-u a) ∂μ)) / 2 := by
  have h1 := integral_cosh_add_smul μ Ψ u h Integrable.of_finite Integrable.of_finite
  simpa only [smul_eq_mul, mul_comm (Real.cosh _), mul_comm (Real.exp (u _)),
    mul_comm (Real.exp (-u _)), div_eq_inv_mul] using h1

omit [IsProbabilityMeasure μ] in
/-- The integral of `sinh (u + h)` against a finite measure on a finite space. -/
theorem integral_sinh_add [IsFiniteMeasure μ] (u : α → ℝ) (h : ℝ) :
    ∫ a, Real.sinh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Real.exp (u a) ∂μ) -
        Real.exp (-h) * (∫ a, Real.exp (-u a) ∂μ)) / 2 := by
  simpa using integral_mul_sinh_add μ (fun _ => 1) u h

omit [IsProbabilityMeasure μ] in
/-- The integral of `cosh (u + h)` against a finite measure on a finite space. -/
theorem integral_cosh_add [IsFiniteMeasure μ] (u : α → ℝ) (h : ℝ) :
    ∫ a, Real.cosh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Real.exp (u a) ∂μ) +
        Real.exp (-h) * (∫ a, Real.exp (-u a) ∂μ)) / 2 := by
  simpa using integral_mul_cosh_add μ (fun _ => 1) u h

/-- `1 ≤ ∫ cosh u` against a finite probability measure. -/
theorem one_le_integral_cosh (u : α → ℝ) : 1 ≤ ∫ a, Real.cosh (u a) ∂μ := by
  simpa using measureReal_univ_le_integral_cosh μ (u := u) Integrable.of_finite

omit [IsProbabilityMeasure μ] in
/-- `|∫ sinh u| ≤ ∫ cosh u` against a finite measure on a finite space. -/
theorem abs_integral_sinh_le_integral_cosh [IsFiniteMeasure μ] (u : α → ℝ) :
    |∫ a, Real.sinh (u a) ∂μ| ≤ ∫ a, Real.cosh (u a) ∂μ :=
  abs_integral_sinh_le_integral_cosh_of_integrable μ Integrable.of_finite

omit [IsProbabilityMeasure μ] in
/-- `|∫ φ w| ≤ C ∫ w` for a nonnegative weight `w` and `|φ| ≤ C`, finite space. -/
theorem abs_integral_mul_le_mul_integral [IsFiniteMeasure μ]
    (φ w : α → ℝ) (hw : ∀ a, 0 ≤ w a) {C : ℝ} (hφ : ∀ a, |φ a| ≤ C) :
    |∫ a, φ a * w a ∂μ| ≤ C * ∫ a, w a ∂μ :=
  abs_integral_mul_le_mul_integral_of_integrable μ (ae_of_all _ hw) Integrable.of_finite
    (ae_of_all _ hφ)

/-- `|⟨sinh u⟩ / ⟨cosh u⟩| ≤ 1`. -/
theorem abs_integral_sinh_div_integral_cosh_le (u : α → ℝ) :
    |(∫ a, Real.sinh (u a) ∂μ) / ∫ a, Real.cosh (u a) ∂μ| ≤ 1 :=
  abs_integral_sinh_div_integral_cosh_le_of_integrable μ Integrable.of_finite

/-- `|⟨φ cosh u⟩ / ⟨cosh u⟩| ≤ C` when `|φ| ≤ C`. -/
theorem abs_integral_mul_cosh_div_le (φ u : α → ℝ) {C : ℝ} (hφ : ∀ a, |φ a| ≤ C) :
    |(∫ a, φ a * Real.cosh (u a) ∂μ) / ∫ a, Real.cosh (u a) ∂μ| ≤ C :=
  abs_integral_mul_cosh_div_le_of_integrable μ Integrable.of_finite (ae_of_all _ hφ)

end Finite
