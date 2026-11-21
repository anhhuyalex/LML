/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianInterpolationParam
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.BoundedC2

/-!
# Gaussian interpolation with a parameter for functions with bounded derivatives

`hasDerivAt_integral_comp_trig_param` asks for exponential growth bounds on `F` and its first and
second partial derivatives. When `F` is `BoundedC2` all of them hold with exponent `0`.

* `SpinGlasses.hasDerivAt_integral_comp_trig_boundedC2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Real

namespace SpinGlasses

variable {κ Ω T : Type*} [Fintype κ] [DecidableEq κ] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup T] [NormedSpace ℝ T] {X Y : κ → Ω → ℝ}

omit [NormedSpace ℝ T] in
theorem norm_zero_prod_single_le (l : κ) : ‖((0 : T), (Pi.single l 1 : κ → ℝ))‖ ≤ 1 := by
  rw [Prod.norm_def, norm_zero, max_le_iff]
  refine ⟨zero_le_one, (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
  by_cases h : i = l <;> simp [h]

omit [DecidableEq κ] [NormedSpace ℝ T] in
theorem norm_prod_zero_le {τ : T} {A : ℝ} (h : ‖τ‖ ≤ A) : ‖(τ, (0 : κ → ℝ))‖ ≤ A := by
  rw [Prod.norm_def, norm_zero]
  exact max_le h ((norm_nonneg τ).trans h)

/-- The second partial derivative in the spin variables of a function with a bounded second
derivative is bounded by it. -/
theorem abs_fderiv_fderiv_section_le {F : T × (κ → ℝ) → ℝ} (hF : BoundedC2 F) {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C) (c : T) (k l : κ) (y : κ → ℝ) :
    |fderiv ℝ (fun y => fderiv ℝ (fun y => F (c, y)) y (Pi.single l 1)) y (Pi.single k 1)| ≤ C := by
  have hsec : (fun y => fderiv ℝ (fun y => F (c, y)) y (Pi.single l 1)) =
      fun y => fderiv ℝ F (c, y) (0, Pi.single l 1) :=
    funext fun y => fderiv_section_apply hF.differentiable c y _
  have h1 : HasFDerivAt (fun y : κ → ℝ => (c, y))
      ((0 : (κ → ℝ) →L[ℝ] T).prod (ContinuousLinearMap.id ℝ (κ → ℝ))) y :=
    (hasFDerivAt_const c y).prodMk (hasFDerivAt_id y)
  have h2 := (hF.differentiable_fderiv (c, y)).hasFDerivAt.comp y h1
  have h3 := h2.clm_apply (hasFDerivAt_const ((0 : T), (Pi.single l 1 : κ → ℝ)) y)
  have h4 : fderiv ℝ (fun y => fderiv ℝ F (c, y) ((0 : T), (Pi.single l 1 : κ → ℝ))) y = _ :=
    h3.fderiv
  rw [hsec, h4]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
  set A := fderiv ℝ (fderiv ℝ F) (c, y) with hA
  have hC0 : 0 ≤ C := (ContinuousLinearMap.opNorm_nonneg _).trans (hC (c, y))
  have e1 : ‖A ((0 : T), (Pi.single k 1 : κ → ℝ))‖ ≤ C := by
    refine (A.le_opNorm _).trans ?_
    calc ‖A‖ * ‖((0 : T), (Pi.single k 1 : κ → ℝ))‖ ≤ C * 1 :=
          mul_le_mul (hC (c, y)) (norm_zero_prod_single_le k) (norm_nonneg _) hC0
      _ = C := mul_one C
  have e2 := (A ((0 : T), (Pi.single k 1 : κ → ℝ))).le_opNorm ((0 : T), (Pi.single l 1 : κ → ℝ))
  rw [← Real.norm_eq_abs]
  calc _ ≤ ‖A ((0 : T), (Pi.single k 1 : κ → ℝ))‖ * ‖((0 : T), (Pi.single l 1 : κ → ℝ))‖ := e2
    _ ≤ C * 1 := mul_le_mul e1 (norm_zero_prod_single_le l) (norm_nonneg _) hC0
    _ = C := mul_one C

end SpinGlasses
