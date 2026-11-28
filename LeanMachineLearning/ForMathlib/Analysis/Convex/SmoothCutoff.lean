/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth concave cutoff potentials

This file constructs smooth (`C^∞`) concave nonpositive functions `u : ℝ → ℝ` vanishing on
`[τ, ∞)`, bounded away from `0` at `τ - ε` (`exp (u (τ - ε)) ≤ ε`), and having bounded iterated
derivatives of orders `1 ≤ j ≤ n`. They serve as smooth approximations to the hard indicator
potential `-∞ · 1_{x < τ}` in Talagrand's Shcherbina--Tirozzi model (Section 3.3, Theorem 3.3.1
and Eqs. (3.124)--(3.126)).

It also proves a general linear lower bound from `u τ = 0` and `|u'| ≤ D`.

## Main declarations

* `neg_mul_one_add_abs_le_of_eq_zero_of_abs_deriv_le`: `-(D * (1 + |τ|)) * (1 + |x|) ≤ u x` from
  `u τ = 0` and `|u'| ≤ D`.
* `exists_contDiff_concaveOn_nonpos_eq_zero_of_ge`: existence of a `C^∞` concave nonpositive
  function vanishing on `[τ, ∞)` with `exp (u (τ - ε)) ≤ ε` and bounded iterated derivatives
  of orders `1 ≤ j ≤ n`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

/-- If `u` is differentiable with `u τ = 0` and `|deriv u| ≤ D`, then
`-(D * (1 + |τ|)) * (1 + |x|) ≤ u x` for all `x`. -/
theorem neg_mul_one_add_abs_le_of_eq_zero_of_abs_deriv_le {u : ℝ → ℝ} {τ D : ℝ}
    (hu : Differentiable ℝ u) (huτ : u τ = 0) (hD : ∀ x, |deriv u x| ≤ D) (x : ℝ) :
    -(D * (1 + |τ|)) * (1 + |x|) ≤ u x := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hdiff := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => hu z) (fun z _ => by simpa only [Real.norm_eq_abs] using hD z)
    (mem_univ τ) (mem_univ x)
  rw [huτ, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hdiff
  have h1 : |x - τ| ≤ (1 + |τ|) * (1 + |x|) := by
    have h2 : |x - τ| ≤ |x| + |τ| := abs_sub x τ
    nlinarith [abs_nonneg x, abs_nonneg τ]
  have h3 : |u x| ≤ D * (1 + |τ|) * (1 + |x|) :=
    hdiff.trans ((mul_le_mul_of_nonneg_left h1 hD0).trans_eq (by ring))
  linarith [neg_abs_le (u x)]

/-- Any `C^∞` function on `ℝ` that is locally constant outside `[0, 1]` has all positive-order
iterated derivatives vanishing outside `[0, 1]`, hence bounded on `ℝ`. -/
private lemma iteratedDeriv_eq_zero_of_notMem_Icc {ψ : ℝ → ℝ}
    (hψ0 : ∀ x < (0 : ℝ), ψ x = ψ (-1)) (hψ1 : ∀ x > (1 : ℝ), ψ x = ψ 2)
    (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    iteratedDeriv k ψ x = 0 := by
  have hloc : ∀ y, y ∉ Icc (0 : ℝ) 1 → ∀ᶠ t in 𝓝 y, ψ t = ψ y := fun y hy => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy0 | hy1
    · filter_upwards [Iio_mem_nhds hy0] with t ht
      rw [hψ0 t ht, hψ0 y hy0]
    · filter_upwards [Ioi_mem_nhds hy1] with t ht
      rw [hψ1 t ht, hψ1 y hy1]
  induction k, hk using Nat.le_induction generalizing x with
  | base =>
    rw [iteratedDeriv_one]
    exact (Filter.EventuallyEq.deriv_eq (hloc x hx)).trans (deriv_const x _)
  | succ m hm ih =>
    have hm_loc : iteratedDeriv m ψ =ᶠ[𝓝 x] fun _ => 0 := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx0 | hx1
      · filter_upwards [Iio_mem_nhds hx0] with t ht
        exact ih (fun h => ht.not_ge h.1)
      · filter_upwards [Ioi_mem_nhds hx1] with t ht
        exact ih (fun h => ht.not_ge h.2)
    rw [iteratedDeriv_succ, hm_loc.deriv_eq, deriv_const]

/-- **Existence of smooth concave cutoff potentials** (Talagrand Eqs. (3.124)--(3.126)): for any
`τ : ℝ`, `ε > 0`, and `n : ℕ`, there exists a `C^∞` concave function `u ≤ 0` vanishing on
`[τ, ∞)` with `exp (u (τ - ε)) ≤ ε` and `|iteratedDeriv j u x| ≤ D` for all `1 ≤ j ≤ n` and
all `x : ℝ`. -/
theorem exists_contDiff_concaveOn_nonpos_eq_zero_of_ge
    (τ : ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ (u : ℝ → ℝ) (D : ℝ), (∀ m : ℕ, ContDiff ℝ m u) ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ x, u x ≤ 0) ∧ (∀ x, τ ≤ x → u x = 0) ∧ Real.exp (u (τ - ε)) ≤ ε ∧
      0 ≤ D ∧ ∀ j, 1 ≤ j → j ≤ n → ∀ x, |iteratedDeriv j u x| ≤ D := by
  let ψ₀ : ℝ → ℝ := fun t => 1 - Real.smoothTransition t
  let g₀ : ℝ → ℝ := fun x => ∫ t in (1 : ℝ)..x, ψ₀ t
  have hψc : Continuous ψ₀ := continuous_const.sub Real.smoothTransition.continuous
  have hg₀_deriv : ∀ x, HasDerivAt g₀ (ψ₀ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hψc.intervalIntegrable 1 x)
      hψc.aestronglyMeasurable.stronglyMeasurableAtFilter hψc.continuousAt
  have hder : deriv g₀ = ψ₀ := funext fun x => (hg₀_deriv x).deriv
  have hg₀_contDiff : ∀ m : ℕ, ContDiff ℝ m g₀ := fun m => by
    induction m with
    | zero =>
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x => (hg₀_deriv x).continuousAt
    | succ m _ =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hg₀_deriv x).differentiableAt, by simp, ?_⟩
      rw [hder]
      exact contDiff_const.sub Real.smoothTransition.contDiff
  have hg₀_conc : ConcaveOn ℝ Set.univ g₀ := by
    have hd1 : Differentiable ℝ g₀ := fun x => (hg₀_deriv x).differentiableAt
    have hd2 : Differentiable ℝ (deriv g₀) := by
      rw [hder]
      exact ((Real.smoothTransition.contDiff (n := (1 : ℕ))).differentiable
        one_ne_zero).const_sub 1
    refine concaveOn_univ_of_deriv2_nonpos hd1 hd2 fun x => ?_
    change deriv (deriv g₀) x ≤ 0
    rw [hder]
    have hderiv_sub : deriv ψ₀ x = -deriv Real.smoothTransition x := by
      have hs := ((Real.smoothTransition.contDiff (n := (1 : ℕ))).differentiable
        one_ne_zero x).hasDerivAt
      exact (hs.const_sub 1).deriv
    change deriv ψ₀ x ≤ 0
    rw [hderiv_sub, neg_nonpos]
    exact Real.smoothTransition.monotone.deriv_nonneg
  have hg₀_zero : ∀ x, 1 ≤ x → g₀ x = 0 := fun x hx => by
    dsimp only [g₀]
    have hzero : EqOn ψ₀ 0 (uIcc 1 x) := fun t ht => by
      rw [uIcc_of_le hx] at ht
      simp [ψ₀, Real.smoothTransition.one_of_one_le ht.1]
    rw [intervalIntegral.integral_congr hzero]
    simp
  have hg₀_nonpos : ∀ x, g₀ x ≤ 0 := fun x => by
    rcases le_or_gt 1 x with hx | hx
    · exact (hg₀_zero x hx).le
    · dsimp only [g₀]
      rw [intervalIntegral.integral_symm, neg_nonpos]
      refine intervalIntegral.integral_nonneg hx.le fun t _ => ?_
      dsimp only [ψ₀]; linarith [Real.smoothTransition.le_one t]
  have hg₀_zero_lt : g₀ 0 < 0 := by
    dsimp only [g₀]
    rw [intervalIntegral.integral_symm, neg_lt_zero]
    have hpos_half : 0 < ψ₀ (1 / 2) := by
      dsimp only [ψ₀]
      rw [sub_pos, Real.smoothTransition]
      have h1 : 0 < expNegInvGlue (1 - 1 / 2) := expNegInvGlue.pos_of_pos (by norm_num)
      have h2 : 0 ≤ expNegInvGlue (1 / 2) := expNegInvGlue.nonneg _
      rw [div_lt_one (Real.smoothTransition.pos_denom _)]
      linarith
    have hle : ∀ t ∈ Icc (0 : ℝ) (1 / 2), ψ₀ (1 / 2) ≤ ψ₀ t := fun t ht =>
      sub_le_sub_left (Real.smoothTransition.monotone ht.2) 1
    have h1 : (1 / 2 : ℝ) * ψ₀ (1 / 2) ≤ ∫ t in (0 : ℝ)..(1 / 2), ψ₀ t := by
      have h := intervalIntegral.integral_mono_on (by norm_num)
        (continuousOn_const.intervalIntegrable (μ := volume))
        (hψc.intervalIntegrable (μ := volume) 0 (1 / 2)) hle
      simpa [intervalIntegral.integral_const] using h
    have h2 : 0 ≤ ∫ t in (1 / 2 : ℝ)..1, ψ₀ t :=
      intervalIntegral.integral_nonneg (μ := volume) (by norm_num) fun t _ => by
        dsimp only [ψ₀]; linarith [Real.smoothTransition.le_one t]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hψc.intervalIntegrable (μ := volume) 0 (1 / 2))
      (hψc.intervalIntegrable (μ := volume) (1 / 2) 1)
    linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hpos_half]
  -- Bound `|iteratedDeriv j g₀|` for `1 ≤ j ≤ n`
  have hsingle : ∀ j, 1 ≤ j → ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j g₀ x| ≤ C := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hsucc : ∀ x, iteratedDeriv (k + 1) g₀ x = iteratedDeriv k ψ₀ x := fun x => by
      rw [iteratedDeriv_succ', hder]
    rcases eq_or_ne k 0 with rfl | hk0
    · refine ⟨1, zero_le_one, fun x => ?_⟩
      rw [hsucc x, iteratedDeriv_zero, abs_le]
      dsimp only [ψ₀]
      constructor <;> linarith [Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
      have hc : Continuous (iteratedDeriv k ψ₀) :=
        (contDiff_const.sub
          (Real.smoothTransition.contDiff (n := (k : ℕ)))).continuous_iteratedDeriv (m := k) le_rfl
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        hc.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      rw [hsucc x]
      by_cases hx : x ∈ Icc (0 : ℝ) 1
      · exact (hC x hx).trans (le_max_left _ _)
      · have hzero := iteratedDeriv_eq_zero_of_notMem_Icc
          (fun t ht => show ψ₀ t = ψ₀ (-1) by
            dsimp only [ψ₀]
            rw [Real.smoothTransition.zero_of_nonpos ht.le,
              Real.smoothTransition.zero_of_nonpos (by norm_num)])
          (fun t ht => show ψ₀ t = ψ₀ 2 by
            dsimp only [ψ₀]
            rw [Real.smoothTransition.one_of_one_le ht.le,
              Real.smoothTransition.one_of_one_le (by norm_num)])
          k hk1 hx
        rw [hzero, abs_zero]
        exact le_max_right _ _
  choose C hC0 hCb using fun j (hj : 1 ≤ j) => hsingle j hj
  let C' : ℕ → ℝ := fun j => if hj : 1 ≤ j then C j hj else 0
  have hC'0 : ∀ j, 0 ≤ C' j := fun j => by
    by_cases hj : 1 ≤ j
    · simp only [C', hj, ↓reduceDIte]; exact hC0 j hj
    · simp only [C', hj, ↓reduceDIte, le_rfl]
  set D₀ : ℝ := (Finset.range (n + 1)).sup' ⟨0, by simp⟩ C'
  have hD₀0 : 0 ≤ D₀ := (hC'0 0).trans (Finset.le_sup' C' (by simp))
  have hD₀ : ∀ j, 1 ≤ j → j ≤ n → ∀ x, |iteratedDeriv j g₀ x| ≤ D₀ := fun j hj1 hjn x => by
    have hjmem : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have hle := Finset.le_sup' C' hjmem
    simp only [C', hj1, ↓reduceDIte] at hle
    exact (hCb j hj1 x).trans hle
  -- Rescale and shift `g₀` to `[τ - ε, τ]`
  have hg0_neg : 0 < -g₀ 0 := neg_pos.2 hg₀_zero_lt
  set A : ℝ := max 1 (-Real.log ε / (-g₀ 0)) with hA_def
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let u : ℝ → ℝ := fun x => A * g₀ (ε⁻¹ * x + (1 - τ / ε))
  set D : ℝ := A * (max 1 ε⁻¹) ^ n * D₀ with hD_def
  have hD0 : 0 ≤ D := by positivity
  have harg_ge : ∀ x, τ ≤ x → 1 ≤ ε⁻¹ * x + (1 - τ / ε) := fun x hx => by
    have : 0 ≤ ε⁻¹ * (x - τ) := mul_nonneg (inv_nonneg.2 hε.le) (sub_nonneg.2 hx)
    have hid : ε⁻¹ * x + (1 - τ / ε) = 1 + ε⁻¹ * (x - τ) := by field_simp; ring
    linarith
  have harg_zero : ε⁻¹ * (τ - ε) + (1 - τ / ε) = 0 := by field_simp; ring
  have hcont : ∀ m : ℕ, ContDiff ℝ m u := fun m =>
    contDiff_const.mul ((hg₀_contDiff m).comp
      ((contDiff_const.mul contDiff_id).add contDiff_const))
  refine ⟨u, D, hcont, ?_, ?_, ?_, ?_, hD0, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have haff : ε⁻¹ * (a • x + b • y) + (1 - τ / ε) =
        a • (ε⁻¹ * x + (1 - τ / ε)) + b • (ε⁻¹ * y + (1 - τ / ε)) := by
      simp only [smul_eq_mul]
      calc ε⁻¹ * (a * x + b * y) + (1 - τ / ε)
          = a * (ε⁻¹ * x + (1 - τ / ε)) + b * (ε⁻¹ * y + (1 - τ / ε)) +
              (1 - τ / ε) * (1 - (a + b)) := by ring
        _ = a * (ε⁻¹ * x + (1 - τ / ε)) + b * (ε⁻¹ * y + (1 - τ / ε)) := by
            rw [hab, sub_self, mul_zero, add_zero]
    have hc := hg₀_conc.2 (mem_univ (ε⁻¹ * x + (1 - τ / ε)))
      (mem_univ (ε⁻¹ * y + (1 - τ / ε))) ha hb hab
    dsimp only [u]
    rw [haff]
    simp only [smul_eq_mul] at hc ⊢
    nlinarith [mul_le_mul_of_nonneg_left hc hA0.le]
  · intro x
    exact mul_nonpos_of_nonneg_of_nonpos hA0.le (hg₀_nonpos _)
  · intro x hx
    dsimp only [u]
    rw [hg₀_zero _ (harg_ge x hx), mul_zero]
  · have hu_le : u (τ - ε) ≤ Real.log ε := by
      dsimp only [u]
      rw [harg_zero]
      have h1 : -Real.log ε / (-g₀ 0) ≤ A := le_max_right _ _
      have h2 : -Real.log ε ≤ A * (-g₀ 0) := (div_le_iff₀ hg0_neg).1 h1
      linarith
    exact (Real.exp_le_exp.2 hu_le).trans_eq (Real.exp_log hε)
  · intro j hj1 hjn x
    have hcomp_add : iteratedDeriv j (fun z => g₀ (z + (1 - τ / ε))) =
        fun z => iteratedDeriv j g₀ (z + (1 - τ / ε)) := by
      have heq : (fun z => g₀ (z + (1 - τ / ε))) = fun z => g₀ ((1 - τ / ε) + z) := by
        funext z; rw [add_comm]
      rw [heq, iteratedDeriv_comp_const_add]
      funext z; rw [add_comm]
    have hsmul : iteratedDeriv j (fun x => g₀ (ε⁻¹ * x + (1 - τ / ε))) x =
        ε⁻¹ ^ j * iteratedDeriv j g₀ (ε⁻¹ * x + (1 - τ / ε)) := by
      have h1 := iteratedDeriv_comp_const_smul
        (f := fun z => g₀ (z + (1 - τ / ε)))
        ((hg₀_contDiff j).comp (contDiff_id.add contDiff_const)) ε⁻¹
      have hx1 := congrFun h1 x
      rw [smul_eq_mul, hcomp_add] at hx1
      exact hx1
    have hu_eq : iteratedDeriv j u x =
        A * iteratedDeriv j (fun x => g₀ (ε⁻¹ * x + (1 - τ / ε))) x := by
      have hc : ContDiffAt ℝ j (fun x => g₀ (ε⁻¹ * x + (1 - τ / ε))) x :=
        ((hg₀_contDiff j).comp ((contDiff_const.mul contDiff_id).add contDiff_const)).contDiffAt
      simpa only [u, smul_eq_mul] using iteratedDeriv_fun_const_smul hc A
    rw [hu_eq, hsmul, abs_mul, abs_mul, abs_of_pos hA0, abs_pow, abs_of_pos (inv_pos.2 hε)]
    have hpow : ε⁻¹ ^ j ≤ (max 1 ε⁻¹) ^ n :=
      (pow_le_pow_left₀ (inv_pos.2 hε).le (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hjn)
    have hgbd := hD₀ j hj1 hjn (ε⁻¹ * x + (1 - τ / ε))
    calc A * (ε⁻¹ ^ j * |iteratedDeriv j g₀ (ε⁻¹ * x + (1 - τ / ε))|)
        ≤ A * ((max 1 ε⁻¹) ^ n * D₀) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpow hgbd (abs_nonneg _) (by positivity)) hA0.le
      _ = D := by dsimp only [D]; ring
