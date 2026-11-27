/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Order.StrictSaddle
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.MillsRatio
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianAffineDerivative
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Shcherbina--Tirozzi model: uniqueness of the replica-symmetric solution

For the hard constraint `exp u = 1_{[τ, ∞)}` with `τ ≥ 0`, the replica-symmetric functional
`F (q, ρ)` (Talagrand, *Spin Glasses*, Vol. I, Eq. (3.121)) has at most one critical point with
`0 < q < ρ` (the uniqueness part of Theorem 3.3.1).

In the variables `x = q / (ρ - q)` and `ρ` the functional becomes `G (x, ρ) = F (x ρ / (1 + x), ρ)`
(Eq. (3.149)). The proof shows that `x ↦ G (x, ρ)` has at most one critical point, which is a
strict minimum, and that `ρ ↦ G (x, ρ)` has at most one, which is a strict maximum.

Throughout, `mills v = p v / ℙ (ξ ≥ v)` is the inverse Mills ratio.

## Main declarations

* `SpinGlasses.shcherbinaTirozziHardFunctional`: the functional `F`.
* `SpinGlasses.hasDerivAt_shcherbinaTirozziHardFunctional_ratio` and
  `SpinGlasses.hasDerivAt_shcherbinaTirozziHardFunctional_self`: Lemma 3.3.13.
* `SpinGlasses.strictMonoOn_shcherbinaTirozziHardFunctional_ratio_deriv` and
  `SpinGlasses.strictAntiOn_shcherbinaTirozziHardFunctional_self_deriv`: Proposition 3.3.11.
* `SpinGlasses.shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero` and
  `SpinGlasses.shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero`: Corollary 3.3.12.
* `SpinGlasses.eq_of_hasDerivAt_shcherbinaTirozziHardFunctional_zero`: Theorem 3.3.1, uniqueness.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SpinGlasses

local notation "mills " v:arg =>
  gaussianPDFReal 0 1 v / Measure.real (gaussianReal 0 1) (Ici v)

/-- **The replica-symmetric functional of the hard constraint** (Talagrand, Eq. (3.121)):
`α 𝔼 log ℙ_ξ (z √q + ξ √(ρ - q) ≥ τ) + q / (2 (ρ - q)) + log (ρ - q) / 2 - κ ρ
  + h² (ρ - q) / 2`. -/
noncomputable def shcherbinaTirozziHardFunctional (α κ h τ q ρ : ℝ) : ℝ :=
  α * ∫ z, Real.log ((gaussianReal 0 1).real
      (Ici ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)))) ∂(gaussianReal 0 1) +
    q / (2 * (ρ - q)) + Real.log (ρ - q) / 2 - κ * ρ + h ^ 2 * (ρ - q) / 2

/-- Eq. (3.149): the functional in the variables `x = q / (ρ - q)` and `ρ`. -/
theorem shcherbinaTirozziHardFunctional_ratio_eq (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 ≤ x)
    (hρ : 0 < ρ) :
    shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) ρ =
      α * ∫ z, Real.log ((gaussianReal 0 1).real
          (Ici (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z))) ∂(gaussianReal 0 1) +
        x / 2 + (Real.log ρ - Real.log (1 + x)) / 2 - κ * ρ + h ^ 2 * ρ / (2 * (1 + x)) := by
  have h1x : 0 < 1 + x := by linarith
  have hs : ρ - x * ρ / (1 + x) = ρ / (1 + x) := by
    field_simp
    ring
  have hW : ∀ z : ℝ, (τ - Real.sqrt (x * ρ / (1 + x)) * z) / Real.sqrt (ρ / (1 + x)) =
      τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z := fun z => by
    rw [Real.sqrt_div' _ h1x.le, Real.sqrt_div' _ h1x.le, Real.sqrt_mul hx]
    have := (Real.sqrt_pos.2 h1x).ne'
    have := (Real.sqrt_pos.2 hρ).ne'
    field_simp
    ring
  unfold shcherbinaTirozziHardFunctional
  simp only [hs, hW]
  rw [Real.log_div hρ.ne' h1x.ne']
  field_simp

/-- **Lemma 3.3.13, Eq. (3.151):** the derivative in `ρ` of
`G (x, ρ) = F (x ρ / (1 + x), ρ)`. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_self (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 ≤ x)
    (hρ : 0 < ρ) :
    HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
      ((α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) *
          (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
            ∂(gaussianReal 0 1)) + ρ⁻¹ - 2 * κ + h ^ 2 / (1 + x)) / 2) ρ := by
  have h1x : 0 < 1 + x := by linarith
  set a : ℝ := τ * Real.sqrt (1 + x) with ha
  set m : ℝ → ℝ := fun r => a / Real.sqrt r with hm
  set m' : ℝ → ℝ := fun r => -(a / (2 * r * Real.sqrt r)) with hm'
  have hmd : ∀ r, 0 < r → HasDerivAt m (m' r) r := fun r hr => by
    have hsr := (Real.sqrt_pos.2 hr).ne'
    have h := (hasDerivAt_const r a).div (Real.hasDerivAt_sqrt hr.ne') hsr
    refine h.congr_deriv ?_
    rw [hm', Real.sq_sqrt hr.le]
    field_simp
    ring
  have hmc : ContinuousAt m' ρ := by
    have hsr := (Real.sqrt_pos.2 hρ).ne'
    refine (continuousAt_const.div (by fun_prop) ?_).neg
    exact mul_ne_zero (mul_ne_zero two_ne_zero hρ.ne') hsr
  have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := fun _ => -Real.sqrt x)
    (m' := m') (σ' := fun _ => 0) (t := ρ)
    ((eventually_gt_nhds hρ).mono fun r hr => hmd r hr)
    (Eventually.of_forall fun r => hasDerivAt_const r _) hmc continuousAt_const
  have hrest : HasDerivAt (fun r => x / 2 + (Real.log r - Real.log (1 + x)) / 2 - κ * r +
      h ^ 2 * r / (2 * (1 + x))) (ρ⁻¹ / 2 - κ + h ^ 2 / (2 * (1 + x))) ρ := by
    have h1 := ((((Real.hasDerivAt_log hρ.ne').sub_const (Real.log (1 + x))).div_const 2
      ).const_add (x / 2)).sub ((hasDerivAt_id ρ).const_mul κ)
    have h2 := ((hasDerivAt_id ρ).const_mul (h ^ 2)).div_const (2 * (1 + x))
    refine (h1.add h2).congr_deriv ?_
    ring
  have hsum := (hE.const_mul α).add hrest
  have heq : (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r) =ᶠ[𝓝 ρ]
      fun r => α * (∫ z, Real.log ((gaussianReal 0 1).real (Ici (m r + -Real.sqrt x * z)))
          ∂(gaussianReal 0 1)) +
        (x / 2 + (Real.log r - Real.log (1 + x)) / 2 - κ * r + h ^ 2 * r / (2 * (1 + x))) := by
    filter_upwards [eventually_gt_nhds hρ] with r hr
    rw [shcherbinaTirozziHardFunctional_ratio_eq α κ h τ hx hr]
    simp only [hm, ha]
    ring
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  have hint : ∫ z, -(mills (m ρ + -Real.sqrt x * z)) * (m' ρ + 0 * z) ∂(gaussianReal 0 1) =
      a / (2 * ρ * Real.sqrt ρ) *
        ∫ z, mills (m ρ + -Real.sqrt x * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hm']
    ring
  rw [hint, show h ^ 2 / (1 + x) = 2 * (h ^ 2 / (2 * (1 + x))) by field_simp]
  simp only [hm, ha]
  ring

/-- The mean `τ √(1 + y) / √ρ` and slope `-√y` of the Gaussian-tail argument in the variable `y`
are differentiable near `x > 0`, with derivatives continuous at `x`. -/
private theorem hasDerivAt_ratio_tail_args (τ : ℝ) {x ρ : ℝ} (hx : 0 < x) (hρ : 0 < ρ) :
    (∀ᶠ y in 𝓝 x, HasDerivAt (fun y => τ * Real.sqrt (1 + y) / Real.sqrt ρ)
        (τ / (2 * Real.sqrt (1 + y) * Real.sqrt ρ)) y) ∧
      (∀ᶠ y in 𝓝 x, HasDerivAt (fun y => -Real.sqrt y) (-(1 / (2 * Real.sqrt y))) y) ∧
      ContinuousAt (fun y => τ / (2 * Real.sqrt (1 + y) * Real.sqrt ρ)) x ∧
      ContinuousAt (fun y => -(1 / (2 * Real.sqrt y))) x := by
  have h1x : 0 < 1 + x := by linarith
  have hsx := (Real.sqrt_pos.2 hx).ne'
  refine ⟨(eventually_gt_nhds hx).mono fun y hy => ?_,
    (eventually_gt_nhds hx).mono fun y hy => (Real.hasDerivAt_sqrt hy.ne').neg,
    continuousAt_const.div (by fun_prop)
      (mul_ne_zero (mul_ne_zero two_ne_zero (Real.sqrt_pos.2 h1x).ne') (Real.sqrt_pos.2 hρ).ne'),
    (continuousAt_const.div (by fun_prop : ContinuousAt (fun y : ℝ => 2 * Real.sqrt y) x)
      (mul_ne_zero two_ne_zero hsx)).neg⟩
  have h1y : (1 : ℝ) + y ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y => Real.sqrt (1 + y)) (1 / (2 * Real.sqrt (1 + y))) y := by
    simpa using ((hasDerivAt_id y).const_add 1).sqrt h1y
  exact ((h1.const_mul τ).div_const (Real.sqrt ρ)).congr_deriv (by ring)

/-- **Lemma 3.3.13, Eq. (3.152):** the derivative in `x` of `G (x, ρ) = F (x ρ / (1 + x), ρ)`
satisfies `2 (1 + x) / x · ∂G/∂x = 1 - α 𝔼 A² / x - h² ρ / (x (1 + x))`. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_ratio (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 < x)
    (hρ : 0 < ρ) :
    HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
      (x / (2 * (1 + x)) *
        (1 - α * (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z) ^ 2
          ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x)))) x := by
  have h1x : 0 < 1 + x := by linarith
  have hsx := (Real.sqrt_pos.2 hx).ne'
  have hs1 := (Real.sqrt_pos.2 h1x).ne'
  have hsρ := (Real.sqrt_pos.2 hρ).ne'
  set m : ℝ → ℝ := fun y => τ * Real.sqrt (1 + y) / Real.sqrt ρ with hm
  set σ : ℝ → ℝ := fun y => -Real.sqrt y with hσ
  set m' : ℝ → ℝ := fun y => τ / (2 * Real.sqrt (1 + y) * Real.sqrt ρ) with hm'
  set σ' : ℝ → ℝ := fun y => -(1 / (2 * Real.sqrt y)) with hσ'
  obtain ⟨hmd, hσd, hmc, hσc⟩ := hasDerivAt_ratio_tail_args τ hx hρ
  have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := σ) (m' := m') (σ' := σ') (t := x)
    hmd hσd hmc hσc
  have hrest : HasDerivAt (fun y => y / 2 + (Real.log ρ - Real.log (1 + y)) / 2 - κ * ρ +
      h ^ 2 * ρ / (2 * (1 + y))) (1 / 2 - (1 + x)⁻¹ / 2 - h ^ 2 * ρ / (2 * (1 + x) ^ 2)) x := by
    have h0 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have h1 := (((hasDerivAt_id x).div_const 2).add
      (((h0.log h1x.ne').const_sub (Real.log ρ)).div_const 2)).sub_const (κ * ρ)
    have h2 := (hasDerivAt_const x (h ^ 2 * ρ)).div (h0.const_mul 2) (by positivity)
    refine (h1.add h2).congr_deriv ?_
    field_simp
    ring
  have hsum := (hE.const_mul α).add hrest
  have heq : (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ) =ᶠ[𝓝 x]
      fun y => α * (∫ z, Real.log ((gaussianReal 0 1).real (Ici (m y + σ y * z)))
          ∂(gaussianReal 0 1)) +
        (y / 2 + (Real.log ρ - Real.log (1 + y)) / 2 - κ * ρ + h ^ 2 * ρ / (2 * (1 + y))) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [shcherbinaTirozziHardFunctional_ratio_eq α κ h τ hy.le hρ]
    simp only [hm, hσ]
    ring
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  -- Gaussian integration by parts
  obtain ⟨hi, hzi, hi2⟩ := integrable_gaussianPDFReal_div_measureReal_Ici_comp (m x) (σ x)
  have hIBP := integral_id_mul_gaussianPDFReal_div_measureReal_Ici_comp (m x) (σ x)
  have hWA : Integrable (fun z => (m x + σ x * z) * mills (m x + σ x * z))
      (gaussianReal 0 1) := by
    refine ((hi.const_mul (m x)).add (hzi.const_mul (σ x))).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have hWAeq : ∫ z, (m x + σ x * z) * mills (m x + σ x * z) ∂(gaussianReal 0 1) =
      m x * (∫ z, mills (m x + σ x * z) ∂(gaussianReal 0 1)) +
        σ x * ∫ z, z * mills (m x + σ x * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi.const_mul _) (hzi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [integral_sub hi2 hWA, hWAeq] at hIBP
  have hder : ∫ z, -(mills (m x + σ x * z)) * (m' x + σ' x * z) ∂(gaussianReal 0 1) =
      -(m' x) * (∫ z, mills (m x + σ x * z) ∂(gaussianReal 0 1)) +
        -(σ' x) * ∫ z, z * mills (m x + σ x * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi.const_mul _) (hzi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [hder]
  change _ = x / (2 * (1 + x)) * (1 - α * (∫ z, mills (m x + σ x * z) ^ 2
    ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x)))
  set I1 := ∫ z, mills (m x + σ x * z) ∂(gaussianReal 0 1) with hI1
  set I2 := ∫ z, mills (m x + σ x * z) ^ 2 ∂(gaussianReal 0 1) with hI2
  set J := ∫ z, z * mills (m x + σ x * z) ∂(gaussianReal 0 1) with hJ
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hs12 : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt h1x.le
  -- solve the integration by parts identity for `J`
  have hJeq : J = -Real.sqrt x * (I2 - m x * I1) / (1 + x) := by
    rw [eq_div_iff h1x.ne']
    simp only [hσ] at hIBP ⊢
    linear_combination hIBP - J * hsx2
  have hmx : m x = τ * Real.sqrt (1 + x) / Real.sqrt ρ := rfl
  rw [hJeq, hmx]
  simp only [hm', hσ']
  set a := Real.sqrt (1 + x) with ha
  set b := Real.sqrt x with hb
  set d := Real.sqrt ρ with hd
  rw [← hs12]
  have hxb : x = b ^ 2 := hsx2.symm
  have hx1 : x = a ^ 2 - 1 := by rw [hs12]; ring
  field_simp
  rw [hs12, hxb]
  ring

/-- A function whose derivative is negative before `a` and positive after `a` increases strictly
away from `a` on `(0, ∞)`: `f y < f x` when `y` lies between `a` and `x ≠ y`. -/
private theorem lt_of_hasDerivAt_neg_of_pos {f f' : ℝ → ℝ} {a x y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hy : a ≤ y ∧ y < x ∨ x < y ∧ y ≤ a) (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hneg : ∀ y, 0 < y → y < a → f' y < 0) (hpos : ∀ y, a < y → 0 < f' y) : f y < f x := by
  rcases hy with ⟨hay, hyx⟩ | ⟨hxy, hya⟩
  · have hy0 : 0 < y := ha.trans_le hay
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := f') (convex_Icc y x)
      (fun w hw => (hf w (hy0.trans_le hw.1)).continuousAt.continuousWithinAt)
      (fun w hw => ?_) (fun w hw => ?_) (left_mem_Icc.2 hyx.le) (right_mem_Icc.2 hyx.le) hyx
    · rw [interior_Icc] at hw
      exact (hf w (hy0.trans hw.1)).hasDerivWithinAt
    · rw [interior_Icc] at hw
      exact hpos w (hay.trans_lt hw.1)
  · refine strictAntiOn_of_hasDerivWithinAt_neg (f' := f') (convex_Icc x y)
      (fun w hw => (hf w (hx.trans_le hw.1)).continuousAt.continuousWithinAt)
      (fun w hw => ?_) (fun w hw => ?_) (left_mem_Icc.2 hxy.le) (right_mem_Icc.2 hxy.le) hxy
    · rw [interior_Icc] at hw
      exact (hf w (hx.trans hw.1)).hasDerivWithinAt
    · rw [interior_Icc] at hw
      exact hneg w (hx.trans hw.1) (hw.2.trans_le hya)

/-- **Proposition 3.3.11, second part:** `x ↦ 1 - α 𝔼 A² / x - h² ρ / (x (1 + x))` is strictly
increasing on `(0, ∞)` unless `α = h = 0`. -/
theorem strictMonoOn_shcherbinaTirozziHardFunctional_ratio_deriv {α h τ ρ : ℝ} (hα : 0 ≤ α)
    (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hαh : α ≠ 0 ∨ h ≠ 0) :
    StrictMonoOn (fun x => 1 - α * (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ +
        -Real.sqrt x * z) ^ 2 ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x))) (Ioi 0) := by
  have hd := fun v => (hasDerivAt_gaussianPDFReal_div_measureReal_Ici v _ fun _ => rfl)
  have hAm : Measurable fun v : ℝ => mills v :=
    monotone_gaussianPDFReal_div_measureReal_Ici.measurable
  have hA0 : ∀ v, 0 ≤ mills v := gaussianPDFReal_div_measureReal_Ici_nonneg
  set A' : ℝ → ℝ := fun v => mills v ^ 2 - v * mills v with hA'
  -- derivative at every `x > 0`
  have key : ∀ x ∈ Ioi (0 : ℝ), ∃ D, 0 < D ∧ HasDerivAt (fun x => 1 - α *
      (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z) ^ 2
        ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x))) D x := by
    intro x (hx : 0 < x)
    have h1x : 0 < 1 + x := by linarith
    have hsx := (Real.sqrt_pos.2 hx).ne'
    have hs1 := (Real.sqrt_pos.2 h1x).ne'
    have hsρ := (Real.sqrt_pos.2 hρ).ne'
    set m : ℝ → ℝ := fun y => τ * Real.sqrt (1 + y) / Real.sqrt ρ with hm
    set σ : ℝ → ℝ := fun y => -Real.sqrt y with hσ
    set m' : ℝ → ℝ := fun y => τ / (2 * Real.sqrt (1 + y) * Real.sqrt ρ) with hm'
    set σ' : ℝ → ℝ := fun y => -(1 / (2 * Real.sqrt y)) with hσ'
    obtain ⟨hmd, hσd, hmc, hσc⟩ := hasDerivAt_ratio_tail_args τ hx hρ
    obtain ⟨hM'i, hM⟩ := hasDerivAt_integral_sq_gaussianPDFReal_div_measureReal_Ici_comp
      (m := m) (σ := σ) (m' := m') (σ' := σ') (t := x)
      hmd hσd hmc hσc
    set M' := ∫ z, 2 * mills (m x + σ x * z) * A' (m x + σ x * z) * (m' x + σ' x * z)
      ∂(gaussianReal 0 1) with hM'
    set M := ∫ z, mills (m x + σ x * z) ^ 2 ∂(gaussianReal 0 1) with hMdef
    have h0 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hfull := (((hM.const_mul α).div (hasDerivAt_id x) hx.ne').const_sub 1).sub
      ((hasDerivAt_const x (h ^ 2 * ρ)).div ((hasDerivAt_id x).mul h0)
        (mul_ne_zero hx.ne' h1x.ne'))
    refine ⟨_, ?_, hfull⟩
    simp only [id_eq, Pi.mul_apply, zero_mul, zero_sub, mul_one, one_mul]
    -- the key positivity: `x M' < M`
    set e : ℝ := τ / (Real.sqrt (1 + x) * Real.sqrt ρ) with he
    have he0 : 0 ≤ e := div_nonneg hτ (by positivity)
    set G : ℝ → ℝ := fun z => mills (m x + σ x * z) ^ 2 -
      x * (2 * mills (m x + σ x * z) * A' (m x + σ x * z) * (m' x + σ' x * z)) with hG
    have hlin : ∀ z, x * (2 * (m' x + σ' x * z)) = (m x + σ x * z) - e := fun z => by
      have h1 : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt h1x.le
      have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
      simp only [hm, hσ, hm', hσ', he]
      set a := Real.sqrt (1 + x)
      set b := Real.sqrt x
      field_simp
      linear_combination (-τ * b) * h1 + (z * Real.sqrt ρ * a) * h2
    have hGpos : ∀ z, 0 < G z := fun z => by
      set v := m x + σ x * z with hv
      have hpos : 0 < mills v := div_pos (gaussianPDFReal_pos _ _ _ one_ne_zero)
        (measureReal_gaussianReal_Ici_pos v)
      have hG' : G z = mills v ^ 2 * (1 - v * mills v + v ^ 2) + e * (mills v * A' v) := by
        have h1 : x * (2 * mills v * A' v * (m' x + σ' x * z)) =
            mills v * A' v * (v - e) := by
          rw [← hlin z]; ring
        have h0 : G z = mills v ^ 2 - x * (2 * mills v * A' v * (m' x + σ' x * z)) := rfl
        rw [h0, h1]
        simp only [hA']
        ring
      have hstrict : v * mills v < 1 + v ^ 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ (measureReal_gaussianReal_Ici_pos v)]
        exact mul_gaussianPDFReal_lt_one_add_sq_mul v
      rw [hG']
      exact add_pos_of_pos_of_nonneg (mul_pos (pow_pos hpos 2) (by linarith))
        (mul_nonneg he0 (mul_nonneg hpos.le (hd v).2))
    have hMi : Integrable (fun z => mills (m x + σ x * z) ^ 2) (gaussianReal 0 1) :=
      (integrable_gaussianPDFReal_div_measureReal_Ici_comp (m x) (σ x)).2.2
    have hGi : Integrable G (gaussianReal 0 1) := hMi.sub (hM'i.const_mul x)
    have hGint : ∫ z, G z ∂(gaussianReal 0 1) = M - x * M' := by
      rw [hMdef, hM', ← integral_const_mul]
      exact integral_sub hMi (hM'i.const_mul x)
    have hGI : 0 < ∫ z, G z ∂(gaussianReal 0 1) := by
      rw [integral_pos_iff_support_of_nonneg (fun z => (hGpos z).le) hGi,
        show Function.support G = univ from eq_univ_of_forall fun z => (hGpos z).ne',
        measure_univ]
      exact one_pos
    have hkey : 0 < M - x * M' := hGint ▸ hGI
    have e1 : -((α * M' * x - α * M) / x ^ 2) -
        -(h ^ 2 * ρ * (1 + x + x)) / (x * (1 + x)) ^ 2 =
        α * (M - x * M') / x ^ 2 + h ^ 2 * ρ * (1 + 2 * x) / (x * (1 + x)) ^ 2 := by ring
    rw [e1]
    have t1 : 0 ≤ α * (M - x * M') / x ^ 2 :=
      div_nonneg (mul_nonneg hα hkey.le) (sq_nonneg _)
    have t2 : 0 ≤ h ^ 2 * ρ * (1 + 2 * x) / (x * (1 + x)) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hρ.le) (by linarith)) (sq_nonneg _)
    rcases hαh with hα' | hh
    · exact add_pos_of_pos_of_nonneg (div_pos (mul_pos (hα.lt_of_ne' hα') hkey) (by positivity))
        t2
    · have hh2 : 0 < h ^ 2 := by positivity
      exact add_pos_of_nonneg_of_pos t1 (div_pos (mul_pos (mul_pos hh2 hρ) (by linarith))
        (by positivity))
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨D, -, hD⟩ := key x hx
    exact hD.continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hx
    obtain ⟨D, hD0, hD⟩ := key x hx
    rwa [hD.deriv]

/-- **Proposition 3.3.11, first part:** `ρ ↦ 2 ∂G/∂ρ` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_shcherbinaTirozziHardFunctional_self_deriv {α τ x : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) :
    StrictAntiOn (fun ρ => α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) *
        (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
          ∂(gaussianReal 0 1)) + ρ⁻¹ - 2 * κ + h ^ 2 / (1 + x)) (Ioi 0) := by
  intro ρ (hρ : 0 < ρ) ρ' (hρ' : 0 < ρ') hlt
  have hA0 : ∀ v, 0 ≤ mills v := gaussianPDFReal_div_measureReal_Ici_nonneg
  have hs : Real.sqrt ρ ≤ Real.sqrt ρ' := Real.sqrt_le_sqrt hlt.le
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hI : ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ' + -Real.sqrt x * z)
        ∂(gaussianReal 0 1) ≤
      ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
        ∂(gaussianReal 0 1) := by
    refine integral_mono (integrable_gaussianPDFReal_div_measureReal_Ici_comp _ _).1
      (integrable_gaussianPDFReal_div_measureReal_Ici_comp _ _).1 fun z =>
      monotone_gaussianPDFReal_div_measureReal_Ici (add_le_add ?_ le_rfl)
    exact div_le_div_of_nonneg_left (mul_nonneg hτ (Real.sqrt_nonneg _)) hsρ hs
  have hc : α * τ * Real.sqrt (1 + x) / (ρ' * Real.sqrt ρ') ≤
      α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) :=
    div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hα hτ) (Real.sqrt_nonneg _))
      (mul_pos hρ hsρ) (mul_le_mul hlt.le hs hsρ.le hρ'.le)
  have hprod := mul_le_mul hc hI (integral_nonneg fun _ => hA0 _)
    (div_nonneg (mul_nonneg (mul_nonneg hα hτ) (Real.sqrt_nonneg _)) (by positivity))
  have hinv : ρ'⁻¹ < ρ⁻¹ := inv_strictAnti₀ hρ hlt
  dsimp only
  linarith

/-- The derivative of `F (q, ·)` at `ρ`, expressed in `x = q / (ρ - q)`. -/
private theorem hasDerivAt_snd (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 ≤ x) (hρ : 0 < ρ) :
    HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) r)
      ((α * (τ * Real.sqrt (1 + x) / Real.sqrt ρ *
            (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
              ∂(gaussianReal 0 1)) +
          x * ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z) ^ 2
              ∂(gaussianReal 0 1)) + (1 - x) * (1 + x)) / (2 * ρ) - κ + h ^ 2 / 2) ρ := by
  have h1x : 0 < 1 + x := by linarith
  set q : ℝ := x * ρ / (1 + x) with hq
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hx hρ.le) h1x.le
  have hs : ρ - q = ρ / (1 + x) := by
    rw [hq]
    field_simp
    ring
  have hs0 : 0 < ρ - q := hs ▸ div_pos hρ h1x
  have hqρ : q < ρ := sub_pos.1 hs0
  set m : ℝ → ℝ := fun r => τ / Real.sqrt (r - q) with hm
  set σ : ℝ → ℝ := fun r => -Real.sqrt q / Real.sqrt (r - q) with hσ
  set m' : ℝ → ℝ := fun r => -(τ / (2 * (r - q) * Real.sqrt (r - q))) with hm'
  set σ' : ℝ → ℝ := fun r => Real.sqrt q / (2 * (r - q) * Real.sqrt (r - q)) with hσ'
  have hquot : ∀ a r : ℝ, q < r → HasDerivAt (fun r => a / Real.sqrt (r - q))
      (-(a / (2 * (r - q) * Real.sqrt (r - q)))) r := fun a r hr => by
    have hr0 : 0 < r - q := sub_pos.2 hr
    have hsr := (Real.sqrt_pos.2 hr0).ne'
    have h1 : HasDerivAt (fun r => Real.sqrt (r - q)) (1 / (2 * Real.sqrt (r - q))) r := by
      simpa using ((hasDerivAt_id r).sub_const q).sqrt hr0.ne'
    refine ((hasDerivAt_const r a).div h1 hsr).congr_deriv ?_
    rw [Real.sq_sqrt hr0.le]
    field_simp
    ring
  have hmd : ∀ r, q < r → HasDerivAt m (m' r) r := fun r hr => hquot τ r hr
  have hσd : ∀ r, q < r → HasDerivAt σ (σ' r) r := fun r hr => by
    refine (hquot (-Real.sqrt q) r hr).congr_deriv ?_
    rw [hσ']
    ring
  have hden : 2 * (ρ - q) * Real.sqrt (ρ - q) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hs0.ne') (Real.sqrt_pos.2 hs0).ne'
  have hdenc : ContinuousAt (fun r : ℝ => 2 * (r - q) * Real.sqrt (r - q)) ρ := by fun_prop
  have hmc : ContinuousAt m' ρ :=
    ContinuousAt.neg (ContinuousAt.div continuousAt_const hdenc hden)
  have hσc : ContinuousAt σ' ρ := ContinuousAt.div continuousAt_const hdenc hden
  have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := σ) (m' := m') (σ' := σ')
    (t := ρ) ((eventually_gt_nhds hqρ).mono fun r hr => hmd r hr)
    ((eventually_gt_nhds hqρ).mono fun r hr => hσd r hr) hmc hσc
  have hrest : HasDerivAt (fun r => q / (2 * (r - q)) + Real.log (r - q) / 2 - κ * r +
      h ^ 2 * (r - q) / 2)
      (-(q / (2 * (ρ - q) ^ 2)) + (ρ - q)⁻¹ / 2 - κ + h ^ 2 / 2) ρ := by
    have h0 : HasDerivAt (fun r : ℝ => r - q) 1 ρ := (hasDerivAt_id ρ).sub_const q
    have h1 := (hasDerivAt_const ρ q).div (h0.const_mul 2) (mul_ne_zero two_ne_zero hs0.ne')
    have h2 := (h0.log hs0.ne').div_const 2
    have h3 := (hasDerivAt_id ρ).const_mul κ
    have h4 := (h0.const_mul (h ^ 2)).div_const 2
    refine (((h1.add h2).sub h3).add h4).congr_deriv ?_
    field_simp
    ring
  have hsum := (hE.const_mul α).add hrest
  have heq : (fun r => shcherbinaTirozziHardFunctional α κ h τ q r) =ᶠ[𝓝 ρ]
      fun r => α * (∫ z, Real.log ((gaussianReal 0 1).real (Ici (m r + σ r * z)))
          ∂(gaussianReal 0 1)) +
        (q / (2 * (r - q)) + Real.log (r - q) / 2 - κ * r + h ^ 2 * (r - q) / 2) := by
    refine Eventually.of_forall fun r => ?_
    have e : ∀ z : ℝ, (τ - Real.sqrt q * z) / Real.sqrt (r - q) = m r + σ r * z := fun z => by
      simp only [hm, hσ]
      ring
    simp only [shcherbinaTirozziHardFunctional, e]
    ring
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  -- evaluate at the point, where `m = τ √(1 + x) / √ρ` and `σ = -√x`
  have hsq : Real.sqrt (ρ - q) = Real.sqrt ρ / Real.sqrt (1 + x) := by
    rw [hs, Real.sqrt_div' _ h1x.le]
  have hsρ := (Real.sqrt_pos.2 hρ).ne'
  have hs1 := (Real.sqrt_pos.2 h1x).ne'
  have hmρ : m ρ = τ * Real.sqrt (1 + x) / Real.sqrt ρ := by
    simp only [hm, hsq]
    field_simp
  have hsqq : Real.sqrt q = Real.sqrt x * (Real.sqrt ρ / Real.sqrt (1 + x)) := by
    rw [hq, Real.sqrt_div' _ h1x.le, Real.sqrt_mul hx, mul_div_assoc]
  have hσρ : σ ρ = -Real.sqrt x := by
    simp only [hσ, hsq, hsqq]
    field_simp
  have hm'ρ : m' ρ = -(m ρ / (2 * (ρ - q))) := by
    change -(τ / (2 * (ρ - q) * Real.sqrt (ρ - q))) =
      -(τ / Real.sqrt (ρ - q) / (2 * (ρ - q)))
    rw [div_div, mul_comm (Real.sqrt (ρ - q))]
  have hσ'ρ : σ' ρ = Real.sqrt x / (2 * (ρ - q)) := by
    have : σ' ρ = -(σ ρ) / (2 * (ρ - q)) := by
      change Real.sqrt q / (2 * (ρ - q) * Real.sqrt (ρ - q)) =
        -(-Real.sqrt q / Real.sqrt (ρ - q)) / (2 * (ρ - q))
      rw [neg_div (Real.sqrt (ρ - q)) (Real.sqrt q), neg_neg, div_div,
        mul_comm (Real.sqrt (ρ - q))]
    rw [this, hσρ, neg_neg]
  obtain ⟨hi, hzi, -⟩ := integrable_gaussianPDFReal_div_measureReal_Ici_comp (m ρ) (σ ρ)
  have hder : ∫ z, -(mills (m ρ + σ ρ * z)) * (m' ρ + σ' ρ * z) ∂(gaussianReal 0 1) =
      -(m' ρ) * (∫ z, mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1)) +
        -(σ' ρ) * ∫ z, z * mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi.const_mul _) (hzi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [hder, ← hmρ, ← hσρ]
  set I1 := ∫ z, mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) with hI1
  set I2 := ∫ z, mills (m ρ + σ ρ * z) ^ 2 ∂(gaussianReal 0 1) with hI2
  set J := ∫ z, z * mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) with hJ
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  -- solve the integration by parts identity for `J`
  have hJeq : J = -Real.sqrt x * (I2 - m ρ * I1) / (1 + x) := by
    rw [eq_div_iff h1x.ne', ← hσρ]
    have h : (1 + σ ρ ^ 2) * J = σ ρ * (I2 - m ρ * I1) :=
      one_add_sq_mul_integral_id_mul_gaussianPDFReal_div_measureReal_Ici (m ρ) (σ ρ)
    have h2 : σ ρ ^ 2 = x := by rw [hσρ, neg_sq, hsx2]
    linear_combination h - J * h2
  have e1 : -(m' ρ) * I1 + -(σ' ρ) * J = (m ρ * I1 + x * I2) / (2 * ρ) := by
    rw [hm'ρ, hσ'ρ, hJeq, hs]
    calc _ = ((1 + x) * (m ρ * I1) + Real.sqrt x ^ 2 * (I2 - m ρ * I1)) / (2 * ρ) := by
          field_simp
      _ = (m ρ * I1 + x * I2) / (2 * ρ) := by
          rw [hsx2]
          ring
  have e2 : -(q / (2 * (ρ - q) ^ 2)) + (ρ - q)⁻¹ / 2 = (1 - x) * (1 + x) / (2 * ρ) := by
    have := hρ.ne'
    have := h1x.ne'
    rw [hs, hq]
    field_simp
    ring
  rw [e1, e2]
  ring

/-- **Corollary 3.3.12:** if `∂G/∂x (x, ρ) = 0`, then `x ↦ G (x, ρ)` increases strictly away from
`x` on `(0, ∞)`: `G (y, ρ) < G (z, ρ)` when `y` lies between `x` and `z ≠ y`. -/
theorem shcherbinaTirozziHardFunctional_ratio_lt_of_between {α τ x ρ y z : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) (hx : 0 < x) (hρ : 0 < ρ) (hz : 0 < z)
    (hyz : x ≤ y ∧ y < z ∨ z < y ∧ y ≤ x)
    (hc : HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
      0 x) :
    shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ <
      shcherbinaTirozziHardFunctional α κ h τ (z * ρ / (1 + z)) ρ := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ, K = fun x => 1 - α * (∫ z, mills (τ * Real.sqrt (1 + x) /
      Real.sqrt ρ + -Real.sqrt x * z) ^ 2 ∂(gaussianReal 0 1)) / x -
      h ^ 2 * ρ / (x * (1 + x)) := ⟨_, rfl⟩
  have hd : ∀ y, 0 < y →
      HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
        (y / (2 * (1 + y)) * K y) y := fun y hy => by
    rw [hK]
    exact hasDerivAt_shcherbinaTirozziHardFunctional_ratio α κ h τ hy hρ
  have hKx : K x = 0 := by
    have h1 := (hd x hx).unique hc
    exact (mul_eq_zero.1 h1).resolve_left (div_pos hx (by linarith)).ne'
  have hαh : α ≠ 0 ∨ h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hK, hcon.1, hcon.2] at hKx
  have hmono : StrictMonoOn K (Ioi 0) := by
    rw [hK]
    exact strictMonoOn_shcherbinaTirozziHardFunctional_ratio_deriv hα hτ hρ hαh
  refine lt_of_hasDerivAt_neg_of_pos
    (f := fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
    (f' := fun y => y / (2 * (1 + y)) * K y) hx hz hyz hd (fun w hw hwx => ?_) fun w hxw => ?_
  · exact mul_neg_of_pos_of_neg (div_pos hw (by linarith))
      ((hmono hw hx hwx).trans_eq hKx)
  · have hw : 0 < w := hx.trans hxw
    exact mul_pos (div_pos hw (by linarith)) (hKx.symm.trans_lt (hmono hx hw hxw))

/-- **Corollary 3.3.12:** a zero of `x ↦ ∂G/∂x (x, ρ)` is a strict minimum of
`x ↦ G (x, ρ)` on `(0, ∞)`. -/
theorem shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero {α τ x ρ y : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) (hx : 0 < x) (hρ : 0 < ρ) (hy : 0 < y) (hyx : y ≠ x)
    (hc : HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
      0 x) :
    shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) ρ <
      shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ :=
  shcherbinaTirozziHardFunctional_ratio_lt_of_between κ h hα hτ hx hρ hy
    (hyx.lt_or_gt.symm.imp (fun h => ⟨le_rfl, h⟩) fun h => ⟨h, le_rfl⟩) hc

/-- A zero of `ρ ↦ ∂G/∂ρ (x, ρ)` is a strict maximum of `ρ ↦ G (x, ρ)` on `(0, ∞)`. -/
theorem shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero {α τ x ρ r : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≠ ρ)
    (hc : HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
      0 ρ) :
    shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r <
      shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) ρ := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, L = fun ρ => α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) *
      (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
        ∂(gaussianReal 0 1)) + ρ⁻¹ - 2 * κ + h ^ 2 / (1 + x) := ⟨_, rfl⟩
  have hd : ∀ r, 0 < r →
      HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
        (L r / 2) r := fun r hr => by
    rw [hL]
    exact hasDerivAt_shcherbinaTirozziHardFunctional_self α κ h τ hx hr
  have hLρ : L ρ = 0 :=
    (div_eq_zero_iff.1 ((hd ρ hρ).unique hc)).resolve_right two_ne_zero
  have hanti : StrictAntiOn L (Ioi 0) := by
    rw [hL]
    exact strictAntiOn_shcherbinaTirozziHardFunctional_self_deriv (x := x) κ h hα hτ
  refine neg_lt_neg_iff.1 (lt_of_hasDerivAt_neg_of_pos
    (f := fun r => -shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
    (f' := fun r => -(L r / 2)) hρ hr
    (hrρ.lt_or_gt.symm.imp (fun h => ⟨le_rfl, h⟩) fun h => ⟨h, le_rfl⟩)
    (fun r hr => (hd r hr).neg)
    (fun w hw hwρ => ?_) fun w hρw => ?_)
  · have h1 : L ρ < L w := hanti hw hρ hwρ
    linarith
  · have h1 : L w < L ρ := hanti hρ (hρ.trans hρw) hρw
    linarith

/-- A critical point `(q, ρ)` of `F` with `0 < q < ρ` gives the critical point
`(x, ρ) = (q / (ρ - q), ρ)` of `G (x, ρ) = F (x ρ / (1 + x), ρ)`. -/
theorem shcherbinaTirozziHardFunctional_ratio_critical (α κ h τ : ℝ) {q ρ : ℝ} (hq : 0 < q)
    (hqρ : q < ρ)
    (hdq : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ) 0 q)
    (hdρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q ρ) 0 ρ) :
    let x : ℝ := q / (ρ - q)
    0 < x ∧ q = x * ρ / (1 + x) ∧
      HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ) 0 x ∧
      HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
        0 ρ := by
  intro x
  have hρ : 0 < ρ := hq.trans hqρ
  have hs : 0 < ρ - q := sub_pos.2 hqρ
  have hx : 0 < x := div_pos hq hs
  have hqx : x * ρ / (1 + x) = q := by
    have := hs.ne'
    have := hρ.ne'
    dsimp only [x]
    field_simp
    ring
  have h1x : 0 < 1 + x := by linarith
  -- the `x`-derivative, by the chain rule
  have hGx : HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
      0 x := by
    have hinner : HasDerivAt (fun y : ℝ => y * ρ / (1 + y)) (ρ / (1 + x) ^ 2) x := by
      refine (((hasDerivAt_id x).mul_const ρ).div ((hasDerivAt_id x).const_add 1)
        h1x.ne').congr_deriv ?_
      simp only [id_eq]
      ring
    have h0 : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ) 0
        (x * ρ / (1 + x)) := by rwa [hqx]
    simpa only [zero_mul, Function.comp_def] using h0.comp x hinner
  -- the `ρ`-derivatives of `F (q, ·)` and `G (x, ·)` agree where `∂G/∂x` vanishes
  refine ⟨hx, hqx.symm, hGx, ?_⟩
  have hK := (hasDerivAt_shcherbinaTirozziHardFunctional_ratio α κ h τ hx hρ).unique hGx
  replace hK := (mul_eq_zero.1 hK).resolve_left (div_pos hx (by linarith)).ne'
  have hF := (hasDerivAt_snd α κ h τ hx.le hρ).unique (by rwa [hqx])
  refine (hasDerivAt_shcherbinaTirozziHardFunctional_self α κ h τ hx.le hρ).congr_deriv ?_
  obtain ⟨I1, hI1⟩ : ∃ I1, I1 = ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ +
      -Real.sqrt x * z) ∂(gaussianReal 0 1) := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I2, I2 = ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ +
      -Real.sqrt x * z) ^ 2 ∂(gaussianReal 0 1) := ⟨_, rfl⟩
  rw [← hI2] at hK
  rw [← hI1, ← hI2] at hF
  rw [← hI1]
  have key : (α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) * I1 + ρ⁻¹ - 2 * κ +
        h ^ 2 / (1 + x)) / 2 =
      ((α * (τ * Real.sqrt (1 + x) / Real.sqrt ρ * I1 + x * I2) + (1 - x) * (1 + x)) /
          (2 * ρ) - κ + h ^ 2 / 2) +
        x ^ 2 / (2 * ρ) * (1 - α * I2 / x - h ^ 2 * ρ / (x * (1 + x))) := by
    have := hx.ne'
    have := hρ.ne'
    have := h1x.ne'
    have := (Real.sqrt_pos.2 hρ).ne'
    field_simp
    ring
  rw [key, hF, hK]
  ring

/-- **Talagrand, Theorem 3.3.1, uniqueness:** for `α ≥ 0` and `τ ≥ 0`, the functional
`F (q, ρ)` has at most one point with `0 < q < ρ` at which both partial derivatives vanish. -/
theorem eq_of_hasDerivAt_shcherbinaTirozziHardFunctional_zero {α τ : ℝ} (κ h : ℝ) (hα : 0 ≤ α)
    (hτ : 0 ≤ τ) {q₁ ρ₁ q₂ ρ₂ : ℝ} (hq₁ : 0 < q₁) (hρ₁ : q₁ < ρ₁) (hq₂ : 0 < q₂)
    (hρ₂ : q₂ < ρ₂)
    (h1q : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ₁) 0 q₁)
    (h1ρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q₁ ρ) 0 ρ₁)
    (h2q : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ₂) 0 q₂)
    (h2ρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q₂ ρ) 0 ρ₂) :
    q₁ = q₂ ∧ ρ₁ = ρ₂ := by
  have hρ₁0 : 0 < ρ₁ := hq₁.trans hρ₁
  have hρ₂0 : 0 < ρ₂ := hq₂.trans hρ₂
  obtain ⟨hx₁, hq₁x, hG1x, hG1ρ⟩ :=
    shcherbinaTirozziHardFunctional_ratio_critical α κ h τ hq₁ hρ₁ h1q h1ρ
  obtain ⟨hx₂, hq₂x, hG2x, hG2ρ⟩ :=
    shcherbinaTirozziHardFunctional_ratio_critical α κ h τ hq₂ hρ₂ h2q h2ρ
  set x₁ : ℝ := q₁ / (ρ₁ - q₁)
  set x₂ : ℝ := q₂ / (ρ₂ - q₂)
  have hx : x₁ = x₂ ∧ ρ₁ = ρ₂ := by
    -- in the variables `(x, ρ)` both critical points are strict saddle points
    obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → ℝ, ∀ x r,
        G x r = shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r :=
      ⟨_, fun _ _ => rfl⟩
    have hmin : ∀ a b : ℝ, 0 < a → 0 < b →
        HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * b / (1 + y)) b) 0 a →
        ∀ c ∈ Set.Ioi (0 : ℝ), c ≠ a → G a b < G c b := fun a b ha hb hd c hc hne => by
      rw [hG, hG]
      exact shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h hα hτ ha hb hc
        hne hd
    have hmax : ∀ a b : ℝ, 0 < a → 0 < b →
        HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (a * r / (1 + a)) r) 0 b →
        ∀ c ∈ Set.Ioi (0 : ℝ), c ≠ b → G a c < G a b := fun a b ha hb hd c hc hne => by
      rw [hG, hG]
      exact shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero κ h hα hτ ha.le hb hc
        hne hd
    exact eq_of_strict_saddle (G := G) (S := Set.Ioi 0) (T := Set.Ioi 0) hx₁ hρ₁0 hx₂ hρ₂0
      (hmin x₁ ρ₁ hx₁ hρ₁0 hG1x) (hmax x₁ ρ₁ hx₁ hρ₁0 hG1ρ) (hmin x₂ ρ₂ hx₂ hρ₂0 hG2x)
      (hmax x₂ ρ₂ hx₂ hρ₂0 hG2ρ)
  refine ⟨?_, hx.2⟩
  rw [hq₁x, hq₂x, hx.1, hx.2]

end SpinGlasses
