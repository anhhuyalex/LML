/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Right-hand limits from linear bounds and derivative of a fixed-point branch

Model-free analysis helpers for parameter-dependent fixed-point equations:

* `tendsto_nhdsGE_zero_of_le`: squeeze `0 ≤ f ≤ g → 0` into `𝓝[≥] 0`.
* `tendsto_nhdsGE_of_le_mul`: if `0 ≤ f a ≤ C * a` for `a ∈ [0, δ)` (`δ > 0`), then `f` tends to
  `0` within `[0, ∞)` as `a → 0⁺`.
* `hasDerivAt_of_fixed_point_contraction`: first-order differentiability of a locally Lipschitz
  fixed-point branch `x b = G (b * R (x b))` when `1 - a * G' * R' ≠ 0`.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- **Squeeze into `[0, ∞)`:** if `0 ≤ f ≤ g` eventually along `l` and `g → 0`, then `f` tends
to `0` within `[0, ∞)`. -/
theorem tendsto_nhdsGE_zero_of_le {α : Type*} {l : Filter α} {f g : α → ℝ}
    (h0 : ∀ᶠ x in l, 0 ≤ f x) (hle : ∀ᶠ x in l, f x ≤ g x) (hg : Tendsto g l (𝓝 0)) :
    Tendsto f l (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨squeeze_zero' h0 hle hg, h0⟩

/-- **Right-hand limit at `0` within `[0, ∞)` from a linear upper bound:** if `0 ≤ f a` and
`f a ≤ C * a` on `[0, δ)` (`δ > 0`), then `f` tends to `0` in `𝓝[≥] 0` as `a → 0⁺`. -/
theorem tendsto_nhdsGE_of_le_mul {f : ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ a ∈ Ico 0 δ, 0 ≤ f a ∧ f a ≤ C * a) :
    Tendsto f (𝓝[≥] 0) (𝓝[≥] 0) := by
  have hc : Continuous fun a : ℝ => max C 0 * a := continuous_const.mul continuous_id
  have h0 : Tendsto (fun a : ℝ => max C 0 * a) (𝓝[≥] 0) (𝓝 0) := by
    have h1 := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ici 0))
    simpa only [mul_zero] using h1
  refine tendsto_nhdsGE_zero_of_le ?_ ?_ h0
  · filter_upwards [Ico_mem_nhdsGE hδ] with a ha
    exact (h a ha).1
  · filter_upwards [Ico_mem_nhdsGE hδ] with a ha
    exact (h a ha).2.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) ha.1)

/-- **First-order differentiability of a locally Lipschitz fixed-point branch:** if
`x b = G (b * R (x b))` and `|x b - x a| ≤ L * |b - a|` on `(a - δ, a + δ)` (`δ > 0`), `G` has
derivative `G'` at `a * R (x a)`, `R` has derivative `R'` at `x a`, and `1 - a * G' * R' ≠ 0`, then
`x` is differentiable at `a` with derivative `(G' * R (x a)) / (1 - a * G' * R')`. -/
theorem hasDerivAt_of_fixed_point_contraction
    {G R x : ℝ → ℝ} {a G' R' δ L : ℝ} (hδ : 0 < δ)
    (hx_fix : ∀ b ∈ Ioo (a - δ) (a + δ), x b = G (b * R (x b)))
    (hx_lip : ∀ b ∈ Ioo (a - δ) (a + δ), |x b - x a| ≤ L * |b - a|)
    (hG : HasDerivAt G G' (a * R (x a)))
    (hR : HasDerivAt R R' (x a))
    (hden : 1 - a * G' * R' ≠ 0) :
    HasDerivAt x ((G' * R (x a)) / (1 - a * G' * R')) a := by
  let L' : ℝ := max L 0 + 1
  have hL' : 0 < L' := by dsimp only [L']; positivity
  have hx_bigO : Asymptotics.IsBigO (𝓝 a) (fun b => x b - x a) (fun b => b - a) := by
    refine Asymptotics.IsBigO.of_bound L' ?_
    filter_upwards [Ioo_mem_nhds (by linarith : a - δ < a) (by linarith : a < a + δ)] with b hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hx_lip b hb).trans (mul_le_mul_of_nonneg_right
      (by dsimp only [L']; linarith [le_max_left L 0]) (abs_nonneg _))
  have hx_cont : ContinuousAt x a := by
    rw [ContinuousAt]
    have h0 : Tendsto (fun b : ℝ => b - a) (𝓝 a) (𝓝 0) := by
      have hc0 : Continuous fun b : ℝ => b - a := continuous_id.sub continuous_const
      simpa only [sub_self] using (hc0.continuousAt (x := a)).tendsto
    simpa only [sub_add_cancel, zero_add] using (hx_bigO.trans_tendsto h0).add_const (x a)
  have hR_o : Asymptotics.IsLittleO (𝓝 a)
      (fun b => R (x b) - R (x a) - (x b - x a) * R') (fun b => b - a) := by
    have h1 : Asymptotics.IsLittleO (𝓝 (x a))
        (fun y => R y - R (x a) - (y - x a) * R') (fun y => y - x a) := by
      simpa only [smul_eq_mul] using hR.isLittleO
    exact (h1.comp_tendsto hx_cont).trans_isBigO hx_bigO
  let u_fn (b : ℝ) : ℝ := b * R (x b)
  have hu_cont : ContinuousAt u_fn a := continuousAt_id.mul (hR.continuousAt.comp hx_cont)
  have hu_bigO : Asymptotics.IsBigO (𝓝 a) (fun b => u_fn b - u_fn a) (fun b => b - a) := by
    have hR_lin : Asymptotics.IsBigO (𝓝 a) (fun b => R' * (x b - x a)) (fun b => b - a) :=
      hx_bigO.const_mul_left R'
    have hR_bigO : Asymptotics.IsBigO (𝓝 a) (fun b => R (x b) - R (x a)) (fun b => b - a) :=
      (hR_o.isBigO.add hR_lin).congr' (Eventually.of_forall fun b => by ring) EventuallyEq.rfl
    have hid_bigO : Asymptotics.IsBigO (𝓝 a) (fun b => b - a) (fun b => b - a) :=
      Asymptotics.isBigO_refl _ _
    have hR_bdd : Asymptotics.IsBigO (𝓝 a) (fun b => R (x b)) (fun _ => (1 : ℝ)) :=
      (hR.continuousAt.comp hx_cont).norm.isBoundedUnder_le.isBigO_const (one_ne_zero' ℝ)
    have hp1 : Asymptotics.IsBigO (𝓝 a) (fun b => (b - a) * R (x b)) (fun b => (b - a) * 1) :=
      hid_bigO.mul hR_bdd
    simp only [mul_one] at hp1
    exact (hp1.add (hR_bigO.const_mul_left a)).congr'
      (Eventually.of_forall fun b => by dsimp only [u_fn]; ring) EventuallyEq.rfl
  have hu_o : Asymptotics.IsLittleO (𝓝 a)
      (fun b => u_fn b - u_fn a - ((b - a) * R (x a) + a * R' * (x b - x a)))
      (fun b => b - a) := by
    have hp1 : Asymptotics.IsLittleO (𝓝 a)
        (fun b => (b - a) * (R (x b) - R (x a))) (fun b => (b - a) * 1) := by
      refine (Asymptotics.isBigO_refl (fun b => b - a) (𝓝 a)).mul_isLittleO ?_
      rw [Asymptotics.isLittleO_one_iff]
      have hc := (hR.continuousAt.comp hx_cont).tendsto
      simpa using hc.sub_const (R (x a))
    simp only [mul_one] at hp1
    exact (hp1.add (hR_o.const_mul_left a)).congr'
      (Eventually.of_forall fun b => by dsimp only [u_fn]; ring) EventuallyEq.rfl
  have hG_o : Asymptotics.IsLittleO (𝓝 a)
      (fun b => G (u_fn b) - G (u_fn a) - (u_fn b - u_fn a) * G') (fun b => b - a) := by
    have h1 : Asymptotics.IsLittleO (𝓝 (u_fn a))
        (fun u => G u - G (u_fn a) - (u - u_fn a) * G') (fun u => u - u_fn a) := by
      simpa only [smul_eq_mul] using hG.isLittleO
    exact (h1.comp_tendsto hu_cont).trans_isBigO hu_bigO
  have hlin_o : Asymptotics.IsLittleO (𝓝 a)
      (fun b => (1 - a * G' * R') * (x b - x a) - (b - a) * (G' * R (x a)))
      (fun b => b - a) := by
    have hsum := hG_o.add (hu_o.const_mul_left G')
    refine hsum.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhds (by linarith : a - δ < a) (by linarith : a < a + δ)] with b hb
    have hxa : x a = G (u_fn a) := hx_fix a ⟨by linarith, by linarith⟩
    have hxb : x b = G (u_fn b) := hx_fix b hb
    rw [← hxa, ← hxb]
    ring
  rw [hasDerivAt_iff_isLittleO]
  have hdiv := hlin_o.const_mul_left (1 - a * G' * R')⁻¹
  refine hdiv.congr' ?_ EventuallyEq.rfl
  refine Eventually.of_forall fun b => ?_
  simp only [smul_eq_mul]
  field_simp
