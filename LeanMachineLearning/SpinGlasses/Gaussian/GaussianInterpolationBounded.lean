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

/-- **Derivative of a Gaussian functional along the trigonometric path, for `F` with bounded
derivatives.** The conclusion is that of `hasDerivAt_integral_comp_trig_param`; the hypotheses
reduce to `F` being `BoundedC2` and the parameter velocity `τ'` being bounded. -/
theorem hasDerivAt_integral_comp_trig_boundedC2
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) {F : T × (κ → ℝ) → ℝ} (hF : BoundedC2 F)
    {τ τ' : ℝ → T} (hτ : ∀ s, HasDerivAt τ (τ' s) s) {A : ℝ} (hA : ∀ s, ‖τ' s‖ ≤ A) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, F (τ s, fun l => Real.cos s * X l ω + Real.sin s * Y l ω) ∂P)
      ((Real.sin t * Real.cos t * ∑ l, ∑ k, ((∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P) *
        ∫ ω, fderiv ℝ (fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single l 1))
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single k 1) ∂P) +
        ∫ ω, fderiv ℝ F (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω)
          (τ' t, 0) ∂P) t := by
  obtain ⟨C, hC0, hC⟩ := hF.exists_bound
  refine hasDerivAt_integral_comp_trig_param hXY hX hY h0 hF.contDiff hτ
    (C₀ := C) (c₀ := 0) (D := fun _ => C) (c₁ := 0) (Cτ := C * A) (cτ := 0)
    (D2 := fun _ _ => C) (c₂ := 0) ?_ ?_ ?_ t ?_
  · intro c y
    simpa using (hC (c, y)).1
  · intro c l y
    have h := (fderiv ℝ F (c, y)).le_opNorm ((0 : T), (Pi.single l 1 : κ → ℝ))
    rw [← Real.norm_eq_abs, zero_mul, Real.exp_zero, mul_one]
    exact h.trans ((mul_le_mul (hC (c, y)).2.1 (norm_zero_prod_single_le l) (norm_nonneg _)
      hC0).trans_eq (mul_one C))
  · intro s y
    have h := (fderiv ℝ F (τ s, y)).le_opNorm (τ' s, (0 : κ → ℝ))
    rw [← Real.norm_eq_abs, zero_mul, Real.exp_zero, mul_one]
    exact h.trans (mul_le_mul (hC (τ s, y)).2.1 (norm_prod_zero_le (hA s)) (norm_nonneg _) hC0)
  · intro k l y
    simpa using abs_fderiv_fderiv_section_le hF (fun x => (hC x).2.2) (τ t) k l y

/-- **Continuity of the second spin derivative.** For `F` that is `C²`, the second partial
derivative in the spin variables is continuous in `y`. -/
theorem continuous_fderiv_fderiv_section {F : T × (κ → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) (c : T)
    (k l : κ) :
    Continuous fun y : κ → ℝ =>
      fderiv ℝ (fun y => fderiv ℝ (fun y => F (c, y)) y (Pi.single l 1)) y (Pi.single k 1) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hsec : (fun y : κ → ℝ => fderiv ℝ (fun y => F (c, y)) y (Pi.single l 1)) =
      fun y => fderiv ℝ F (c, y) (0, Pi.single l 1) :=
    funext fun y => fderiv_section_apply hFd c y _
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fun y : κ → ℝ => fderiv ℝ F (c, y) ((0 : T), (Pi.single l 1 : κ → ℝ))) :=
    (h1.comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  rw [hsec]
  exact (h2.continuous_fderiv one_ne_zero).clm_apply continuous_const

section Integrability

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]

/-- The second spin derivative of a `BoundedC2` functional along a continuous random field is
integrable. -/
theorem integrable_fderiv_fderiv_section {F : T × (κ → ℝ) → ℝ} (hF : BoundedC2 F) (c : T)
    (k l : κ) {Y : Ω → κ → ℝ} (hY : Continuous Y) :
    Integrable (fun ω => fderiv ℝ (fun y => fderiv ℝ (fun y => F (c, y)) y (Pi.single l 1))
      (Y ω) (Pi.single k 1)) P := by
  obtain ⟨C, -, hC⟩ := hF.exists_bound
  exact Integrable.of_bound (C := C)
    (((continuous_fderiv_fderiv_section hF.contDiff c k l).comp hY).aestronglyMeasurable)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_fderiv_fderiv_section_le hF (fun x => (hC x).2.2) c k l _)

omit [DecidableEq κ] in
/-- The parameter derivative of a `BoundedC2` functional along a continuous random field is
integrable. -/
theorem integrable_fderiv_param {F : T × (κ → ℝ) → ℝ} (hF : BoundedC2 F) (c v : T)
    {Y : Ω → κ → ℝ} (hY : Continuous Y) :
    Integrable (fun ω => fderiv ℝ F (c, Y ω) (v, 0)) P := by
  obtain ⟨C, hC0, hC⟩ := hF.exists_bound
  have h1c : ContDiff ℝ 1 (fderiv ℝ F) := hF.contDiff.fderiv_right (by norm_num)
  have h1 : Continuous (fderiv ℝ F) := h1c.continuous
  refine Integrable.of_bound (C := C * ‖(v, (0 : κ → ℝ))‖) ?_ (ae_of_all _ fun ω => ?_)
  · exact ((h1.comp (continuous_const.prodMk hY)).clm_apply continuous_const).aestronglyMeasurable
  · rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact ((fderiv ℝ F (c, Y ω)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC _).2.1 (norm_nonneg _))

end Integrability

end SpinGlasses
