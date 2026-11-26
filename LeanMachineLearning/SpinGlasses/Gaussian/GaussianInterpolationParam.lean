/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianCovarianceInterpolation

/-!
# Gaussian interpolation with an extra smooth parameter

`SpinGlasses.hasDerivAt_integral_comp_trig` differentiates `s ↦ 𝔼 F (cos s X + sin s Y)` for a
functional `F` that does not depend on `s`. In Talagrand's cavity in `M` (Section 2.3) the
normalizer is a Gaussian smoothing whose variance depends on `s`. Here `F` also depends on a
parameter `τ(s)` in a normed space `T`, and the derivative acquires the explicit term
`𝔼 (∂_τ F)(τ s, Z_s) τ'(s)` besides the covariance-difference term.

* `hasDerivAt_integral_comp_trig_param`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Real

namespace SpinGlasses

variable {κ Ω T : Type*} [Fintype κ] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup T] [NormedSpace ℝ T] {X Y : κ → Ω → ℝ}

omit [Fintype κ] in
/-- Partial derivatives of a function of `(τ, y)` in the `y`-direction are those of the section
`y ↦ F (c, y)`. -/
theorem fderiv_section_apply [Finite κ] {F : T × (κ → ℝ) → ℝ} (hF : Differentiable ℝ F) (c : T)
    (y w : κ → ℝ) : fderiv ℝ (fun y => F (c, y)) y w = fderiv ℝ F (c, y) (0, w) := by
  have := Fintype.ofFinite κ
  have h1 : HasFDerivAt (fun y : κ → ℝ => (c, y))
      ((0 : (κ → ℝ) →L[ℝ] T).prod (ContinuousLinearMap.id ℝ (κ → ℝ))) y :=
    (hasFDerivAt_const c y).prodMk (hasFDerivAt_id y)
  have h2 := (hF (c, y)).hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun y => F (c, y)) y = fderiv ℝ F (c, y) ∘L
      (ContinuousLinearMap.prod (0 : (κ → ℝ) →L[ℝ] T) (ContinuousLinearMap.id ℝ (κ → ℝ))) :=
    h2.fderiv
  rw [h3]
  rfl

variable [DecidableEq κ]

/-- **Derivative of a Gaussian functional along the trigonometric path with an extra parameter.**
For independent centered Gaussian vectors `X`, `Y` and a `C²` functional `F (τ, y)` with
exponentially bounded value and partial derivatives (uniformly in the parameter `τ`), and a
differentiable parameter path `τ(s)`, the derivative of `s ↦ 𝔼 F (τ s, cos s X + sin s Y)` at `t`
is the covariance-difference term of `hasDerivAt_integral_comp_trig` for `F (τ t, ·)` plus the
explicit term `𝔼 (∂_τ F)(τ t, Z_t) τ'(t)`. -/
theorem hasDerivAt_integral_comp_trig_param
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) {F : T × (κ → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    {τ τ' : ℝ → T} (hτ : ∀ s, HasDerivAt τ (τ' s) s)
    {C₀ c₀ : ℝ} (hF0 : ∀ c y, |F (c, y)| ≤ C₀ * Real.exp (c₀ * ∑ l, |y l|))
    {D : κ → ℝ} {c₁ : ℝ}
    (hF1 : ∀ c l y, |fderiv ℝ F (c, y) (0, Pi.single l 1)| ≤ D l * Real.exp (c₁ * ∑ l, |y l|))
    {Cτ cτ : ℝ}
    (hFτ : ∀ s y, |fderiv ℝ F (τ s, y) (τ' s, 0)| ≤ Cτ * Real.exp (cτ * ∑ l, |y l|))
    {D2 : κ → κ → ℝ} {c₂ : ℝ} (t : ℝ)
    (hF2 : ∀ k l y, |fderiv ℝ (fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single l 1)) y
      (Pi.single k 1)| ≤ D2 k l * Real.exp (c₂ * ∑ l, |y l|)) :
    HasDerivAt (fun s => ∫ ω, F (τ s, fun l => Real.cos s * X l ω + Real.sin s * Y l ω) ∂P)
      ((Real.sin t * Real.cos t * ∑ l, ∑ k, ((∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P) *
        ∫ ω, fderiv ℝ (fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single l 1))
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single k 1) ∂P) +
        ∫ ω, fderiv ℝ F (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω)
          (τ' t, 0) ∂P) t := by
  have hP := hXY.isProbabilityMeasure
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFc : Continuous F := hFd.continuous
  have hFt2 : ContDiff ℝ 2 (fun y => F (τ t, y)) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hFl : ∀ l, Differentiable ℝ
      (fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single l 1)) := fun l => by
    have h1 : ContDiff ℝ 1 (fderiv ℝ (fun y => F (τ t, y))) := hFt2.fderiv_right (by norm_num)
    exact (h1.clm_apply contDiff_const).differentiable one_ne_zero
  have hsec : ∀ c y w, fderiv ℝ (fun y => F (c, y)) y w = fderiv ℝ F (c, y) (0, w) :=
    fun c y w => fderiv_section_apply hFd c y w
  have hXi : ∀ l, Integrable (X l) P := fun l => (hXY.eval (Sum.inl l)).integrable
  have hYi : ∀ l, Integrable (Y l) P := fun l => (hXY.eval (Sum.inr l)).integrable
  have hmean : ∀ k, ∫ ω, Sum.elim X Y k ω ∂P = 0 := by
    rintro (k | k)
    exacts [hX k, hY k]
  have hD0 : ∀ l, 0 ≤ D l := fun l => by simpa using (abs_nonneg _).trans (hF1 (τ 0) l 0)
  have hC₀ : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hF0 (τ 0) 0)
  have hCτ : 0 ≤ Cτ := by simpa using (abs_nonneg _).trans (hFτ 0 0)
  -- the exponential bound on the integrand of the `y`-derivative
  have hbd : ∀ (s : ℝ) (l : κ) (v : κ ⊕ κ → ℝ),
      |(-Real.sin s * v (Sum.inl l) + Real.cos s * v (Sum.inr l)) *
        fderiv ℝ F (τ s, fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
          (0, Pi.single l 1)| ≤ D l * Real.exp ((|c₁| + 1) * ∑ p, |v p|) := fun s l v => by
    have hS : (0 : ℝ) ≤ ∑ p, |v p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hlr : |v (Sum.inl l)| + |v (Sum.inr l)| ≤ ∑ p, |v p| := by
      rw [Fintype.sum_sum_type]
      exact add_le_add (Finset.single_le_sum (f := fun m => |v (Sum.inl m)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ l)) (Finset.single_le_sum
        (f := fun m => |v (Sum.inr m)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l))
    have hZ := sum_abs_cos_mul_add_sin_mul_le s v
    have hexp : Real.exp (c₁ * ∑ m, |Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m)|) ≤
        Real.exp (|c₁| * ∑ p, |v p|) := Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right
          (le_abs_self c₁) (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hZ (abs_nonneg _)))
    rw [abs_mul]
    calc _ ≤ (∑ p, |v p|) * (D l * Real.exp (|c₁| * ∑ p, |v p|)) :=
          mul_le_mul ((abs_neg_sin_mul_add_cos_mul_le _ _ s).trans hlr)
            ((hF1 _ l _).trans (mul_le_mul_of_nonneg_left hexp (hD0 l))) (abs_nonneg _) hS
      _ = D l * ((∑ p, |v p|) * Real.exp (|c₁| * ∑ p, |v p|)) := by ring
      _ ≤ D l * (Real.exp (∑ p, |v p|) * Real.exp (|c₁| * ∑ p, |v p|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (by linarith [Real.add_one_le_exp (∑ p, |v p|)]) (Real.exp_pos _).le) (hD0 l)
      _ = D l * Real.exp ((|c₁| + 1) * ∑ p, |v p|) := by
          rw [← Real.exp_add]; congr 2; ring
  have hbτ : ∀ (s : ℝ) (v : κ ⊕ κ → ℝ),
      |fderiv ℝ F (τ s, fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
        (τ' s, 0)| ≤ Cτ * Real.exp (|cτ| * ∑ p, |v p|) := fun s v =>
    (hFτ s _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      ((mul_le_mul_of_nonneg_right (le_abs_self cτ)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (sum_abs_cos_mul_add_sin_mul_le s v) (abs_nonneg _)))) hCτ)
  have hFcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hder := hasDerivAt_integral_comp_of_exp_growth (X := Sum.elim X Y) hXY hmean
    (G := fun s v => F (τ s, fun l => Real.cos s * v (Sum.inl l) + Real.sin s * v (Sum.inr l)))
    (G' := fun s v => (∑ l, (-Real.sin s * v (Sum.inl l) + Real.cos s * v (Sum.inr l)) *
      fderiv ℝ F (τ s, fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
        (0, Pi.single l 1)) +
      fderiv ℝ F (τ s, fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
        (τ' s, 0)) t
    (fun s => (hFc.comp (by have := (hτ s).continuousAt; fun_prop)).measurable)
    (Continuous.measurable (by
      have hpt : Continuous fun v : κ ⊕ κ → ℝ => ((τ t, fun m => Real.cos t * v (Sum.inl m) +
          Real.sin t * v (Sum.inr m)) : T × (κ → ℝ)) := continuous_const.prodMk (by fun_prop)
      exact (continuous_finsetSum _ fun l _ => (by fun_prop : Continuous _).mul
        ((hFcont.comp hpt).clm_apply continuous_const)).add
        ((hFcont.comp hpt).clm_apply continuous_const)))
    (fun s v => by
      have hpath : HasDerivAt (fun s => fun l => Real.cos s * v (Sum.inl l) +
          Real.sin s * v (Sum.inr l)) (fun l => -Real.sin s * v (Sum.inl l) +
          Real.cos s * v (Sum.inr l)) s :=
        hasDerivAt_pi.2 fun l => ((Real.hasDerivAt_cos s).mul_const _).add
          ((Real.hasDerivAt_sin s).mul_const _)
      have hp := (hτ s).prodMk hpath
      refine ((hFd _).hasFDerivAt.comp_hasDerivAt s hp).congr_deriv ?_
      have hsplit : ((τ' s, fun l => -Real.sin s * v (Sum.inl l) + Real.cos s * v (Sum.inr l)) :
          T × (κ → ℝ)) = (τ' s, 0) + (0, fun l => -Real.sin s * v (Sum.inl l) +
            Real.cos s * v (Sum.inr l)) := by
        ext <;> simp
      rw [hsplit, map_add, ← hsec]
      rw [fderiv_apply_eq_sum_mul (F := fun y => F (τ s, y))]
      simp only [hsec]
      ring)
    (C := (∑ l, D l) + Cτ) (c := |c₁| + 1 + |cτ|) (fun s v => by
      have hS : (0 : ℝ) ≤ ∑ p, |v p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hA : |∑ l, (-Real.sin s * v (Sum.inl l) + Real.cos s * v (Sum.inr l)) *
          fderiv ℝ F (τ s, fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
            (0, Pi.single l 1)| ≤ (∑ l, D l) * Real.exp ((|c₁| + 1 + |cτ|) * ∑ p, |v p|) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun l _ => (hbd s l v).trans ?_
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
          (show |c₁| + 1 ≤ |c₁| + 1 + |cτ| by linarith [abs_nonneg cτ]) hS)) (hD0 l)
      have hB := (hbτ s v).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right
          (show |cτ| ≤ |c₁| + 1 + |cτ| by linarith [abs_nonneg c₁]) hS)) hCτ)
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add hA hB
        _ = _ := by ring)
    (C₀ := C₀) (c₀ := |c₀|) (fun v => by
      refine (hF0 _ _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₀)
      exact (mul_le_mul_of_nonneg_right (le_abs_self c₀)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (sum_abs_cos_mul_add_sin_mul_le t v) (abs_nonneg _)))
  refine hder.congr_deriv ?_
  -- Gaussian integration by parts for the `y`-derivative part
  have hlin := hasGaussianLaw_sumElim_lincomb hXY (-Real.sin t) (Real.cos t) (Real.cos t)
    (Real.sin t)
  have hWmean : ∀ l, ∫ ω, (-Real.sin t * X l ω + Real.cos t * Y l ω) ∂P = 0 :=
    integral_lincomb_eq_zero hX hY hXi hYi _ _
  have hZmean : ∀ l, ∫ ω, (Real.cos t * X l ω + Real.sin t * Y l ω) ∂P = 0 :=
    integral_lincomb_eq_zero hX hY hXi hYi _ _
  have hstein : ∀ l, ∫ ω, (-Real.sin t * X l ω + Real.cos t * Y l ω) *
      fderiv ℝ F (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (0, Pi.single l 1) ∂P =
      Real.sin t * Real.cos t * ∑ k, ((∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P) *
        ∫ ω, fderiv ℝ (fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single l 1))
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single k 1) ∂P := fun l => by
    have h := integral_mul_comp_eq_sum_integral_mul_of_sum
      (W := fun a ω => -Real.sin t * X a ω + Real.cos t * Y a ω)
      (X := fun a ω => Real.cos t * X a ω + Real.sin t * Y a ω) hlin (i := l) (hWmean l) hZmean
      (F := fun y => fderiv ℝ (fun y => F (τ t, y)) y (Pi.single l 1)) (hFl l) (C := D l)
      (c := c₁) (fun y => by rw [hsec]; exact hF1 _ l y) (D := fun k => D2 k l) (d := fun _ => c₂)
      (fun k y => hF2 k l y)
    have e : ∀ ω, fderiv ℝ F (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω)
        (0, Pi.single l 1) = fderiv ℝ (fun y => F (τ t, y))
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single l 1) :=
      fun ω => (hsec _ _ _).symm
    simp_rw [e]
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_lincomb_mul_lincomb hXY h0 (-Real.sin t) (Real.cos t) (Real.cos t)
      (Real.sin t) l k]
    ring
  have hpt : Continuous fun v : κ ⊕ κ → ℝ => ((τ t, fun m => Real.cos t * v (Sum.inl m) +
      Real.sin t * v (Sum.inr m)) : T × (κ → ℝ)) := continuous_const.prodMk (by fun_prop)
  have hint : ∀ l, Integrable (fun ω => (-Real.sin t * X l ω + Real.cos t * Y l ω) *
      fderiv ℝ F (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (0, Pi.single l 1)) P :=
    fun l => integrable_comp_of_exp_growth (X := Sum.elim X Y) hXY hmean
      (F := fun v => (-Real.sin t * v (Sum.inl l) + Real.cos t * v (Sum.inr l)) *
        fderiv ℝ F (τ t, fun m => Real.cos t * v (Sum.inl m) + Real.sin t * v (Sum.inr m))
          (0, Pi.single l 1))
      (Continuous.measurable ((by fun_prop : Continuous _).mul
        ((hFcont.comp hpt).clm_apply continuous_const)))
      (C := D l) (c := |c₁| + 1) (fun v => hbd t l v)
  have hintτ : Integrable (fun ω => fderiv ℝ F
      (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (τ' t, 0)) P :=
    integrable_comp_of_exp_growth (X := Sum.elim X Y) hXY hmean
      (F := fun v => fderiv ℝ F (τ t, fun m => Real.cos t * v (Sum.inl m) +
        Real.sin t * v (Sum.inr m)) (τ' t, 0))
      (Continuous.measurable ((hFcont.comp hpt).clm_apply continuous_const))
      (C := Cτ) (c := |cτ|) (fun v => by simpa using hbτ t v)
  change ∫ ω, ((∑ l, (-Real.sin t * X l ω + Real.cos t * Y l ω) *
      fderiv ℝ F (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (0, Pi.single l 1)) +
      fderiv ℝ F (τ t, fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (τ' t, 0)) ∂P = _
  rw [integral_add (integrable_finsetSum _ fun l _ => hint l) hintτ,
    integral_finsetSum _ fun l _ => hint l]
  simp_rw [hstein]
  rw [Finset.mul_sum]

end SpinGlasses
