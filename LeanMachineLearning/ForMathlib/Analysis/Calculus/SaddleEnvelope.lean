/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Envelope derivatives for saddle points

If `(x a, y a)` is a saddle point of `(x, y) ↦ G a x y` for every parameter `a` near `a₀` (minimum
in `x ∈ S`, maximum in `y ∈ T`), `(x a, y a) → (x a₀, y a₀)` as `a → a₀`, and the family of
parameter derivatives `a ↦ ∂_a G a x y` is continuous at `(a₀, x a₀, y a₀)`, then the saddle-value
curve `a ↦ G a (x a) (y a)` is differentiable at `a₀` with derivative `∂_a G a₀ (x a₀) (y a₀)`.
Neither differentiability of `(x, y)` in `a` nor second derivatives of `G` are needed: the saddle
inequalities sandwich each difference quotient between two difference quotients at fixed `(x, y)`,
which are evaluated by the mean value theorem.

## Main statements

* `hasDerivWithinAt_saddle_envelope`: within any convex set `A` containing `a₀` (covers `[0, ∞)` at
  `0` as well as interior points).
* `hasDerivAt_saddle_envelope`: the two-sided interior specialization.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- **Saddle-point envelope theorem on a convex parameter domain:** let `A ⊆ ℝ` be convex with
`a₀ ∈ A`. Suppose that for `a ∈ A` near `a₀`, `(x a, y a) ∈ S × T` is a saddle point of `G a`
(minimizer over `S` in `x`, maximizer over `T` in `y`), `(x, y)` is continuous within `A` at `a₀`,
`b ↦ G b u v` has derivative `G' b u v` for `(b, u, v)` near `(a₀, x a₀, y a₀)`, and `G'` is
continuous at `(a₀, x a₀, y a₀)`. Then `a ↦ G a (x a) (y a)` has derivative `G' a₀ (x a₀) (y a₀)`
within `A` at `a₀`. -/
theorem hasDerivWithinAt_saddle_envelope {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {G G' : ℝ → X → Y → ℝ} {A : Set ℝ} {S : Set X} {T : Set Y} {x : ℝ → X} {y : ℝ → Y} {a₀ : ℝ}
    {U : Set ℝ} {Ux : Set X} {Uy : Set Y}
    (ha₀ : a₀ ∈ A) (hA : Convex ℝ A) (hU : U ∈ 𝓝 a₀) (hUx : Ux ∈ 𝓝 (x a₀)) (hUy : Uy ∈ 𝓝 (y a₀))
    (hmem : ∀ a ∈ A ∩ U, x a ∈ S ∧ y a ∈ T)
    (hmin : ∀ a ∈ A ∩ U, ∀ x' ∈ S, G a (x a) (y a) ≤ G a x' (y a))
    (hmax : ∀ a ∈ A ∩ U, ∀ y' ∈ T, G a (x a) y' ≤ G a (x a) (y a))
    (hx : ContinuousWithinAt x A a₀) (hy : ContinuousWithinAt y A a₀)
    (hd : ∀ b ∈ U, ∀ u ∈ Ux, ∀ v ∈ Uy, HasDerivAt (fun c => G c u v) (G' b u v) b)
    (hcont : ContinuousAt (fun p : ℝ × X × Y => G' p.1 p.2.1 p.2.2) (a₀, x a₀, y a₀)) :
    HasDerivWithinAt (fun a => G a (x a) (y a)) (G' a₀ (x a₀) (y a₀)) A a₀ := by
  set φ : ℝ → ℝ := fun a => G a (x a) (y a)
  set L : ℝ := G' a₀ (x a₀) (y a₀)
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhds]
  intro ε hε
  have hcont' : ∀ᶠ p : ℝ × X × Y in 𝓝 (a₀, x a₀, y a₀), |G' p.1 p.2.1 p.2.2 - L| < ε := by
    simpa [Real.dist_eq] using hcont.eventually (Metric.ball_mem_nhds L hε)
  rw [nhds_prod_eq, nhds_prod_eq, Filter.eventually_prod_iff] at hcont'
  obtain ⟨pa, hpa, pq, hpq, hG'ε⟩ := hcont'
  rw [Filter.eventually_prod_iff] at hpq
  obtain ⟨px, hpx, py, hpy, hpq'⟩ := hpq
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hpa)
  set V : Set ℝ := Metric.ball a₀ δ
  have hVsubU : V ⊆ U := fun b hb => (hball hb).1
  have hVpa : ∀ b ∈ V, pa b := fun b hb => (hball hb).2
  have hVconv : Convex ℝ V := convex_ball a₀ δ
  have ha₀V : a₀ ∈ V := Metric.mem_ball_self hδ0
  have hx0 : x a₀ ∈ Ux ∧ px (x a₀) := mem_of_mem_nhds (Filter.inter_mem hUx hpx)
  have hy0 : y a₀ ∈ Uy ∧ py (y a₀) := mem_of_mem_nhds (Filter.inter_mem hUy hpy)
  have hxmem : ∀ᶠ a in 𝓝[A] a₀, x a ∈ Ux ∧ px (x a) :=
    hx.eventually (Filter.inter_mem hUx hpx)
  have hymem : ∀ᶠ a in 𝓝[A] a₀, y a ∈ Uy ∧ py (y a) :=
    hy.eventually (Filter.inter_mem hUy hpy)
  have hVmemA : ∀ᶠ a in 𝓝[A] a₀, a ∈ V :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds a₀ hδ0)
  have hallA : ∀ᶠ a in 𝓝[A] a₀, a ∈ V ∧ (x a ∈ Ux ∧ px (x a)) ∧ (y a ∈ Uy ∧ py (y a)) :=
    hVmemA.and (hxmem.and hymem)
  have hall : ∀ᶠ a in 𝓝[A \ {a₀}] a₀,
      a ∈ A ∧ a ≠ a₀ ∧ a ∈ V ∧ (x a ∈ Ux ∧ px (x a)) ∧ (y a ∈ Uy ∧ py (y a)) := by
    refine eventually_nhdsWithin_iff.2 ?_
    have h1 := eventually_nhdsWithin_iff.1 hallA
    refine h1.mono fun a ha hmem_diff =>
      ⟨hmem_diff.1, hmem_diff.2, ha hmem_diff.1⟩
  refine hall.mono fun a ⟨haA, hane, haV, ⟨hxaUx, hpxa⟩, ⟨hyaUy, hpya⟩⟩ => ?_
  have haAU : a ∈ A ∩ U := ⟨haA, hVsubU haV⟩
  have ha₀AU : a₀ ∈ A ∩ U := ⟨ha₀, hVsubU ha₀V⟩
  have hmvt : ∀ u v, u ∈ Ux → px u → v ∈ Uy → py v →
      |(G a u v - G a₀ u v) / (a - a₀) - L| < ε := by
    intro u v huUx hpu hvUy hpv
    have hseg : Icc (min a₀ a) (max a₀ a) ⊆ V :=
      hVconv.ordConnected.out (min_rec' (· ∈ V) ha₀V haV) (max_rec' (· ∈ V) ha₀V haV)
    rcases lt_or_gt_of_ne hane with hlt | hgt
    · have hmin_eq : min a₀ a = a := min_eq_right hlt.le
      have hmax_eq : max a₀ a = a₀ := max_eq_left hlt.le
      have hcd : ContinuousOn (fun c => G c u v) (Icc a a₀) := fun c hc =>
        (hd c (hVsubU (hseg (by rwa [hmin_eq, hmax_eq]))) u huUx v hvUy).continuousAt.continuousWithinAt
      have hdd : ∀ c ∈ Ioo a a₀, HasDerivAt (fun c => G c u v) (G' c u v) c :=
        fun c hc => hd c (hVsubU (hseg (by rw [hmin_eq, hmax_eq]; exact Ioo_subset_Icc_self hc)))
          u huUx v hvUy
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun c => G c u v) (fun c => G' c u v)
        hlt hcd hdd
      have hcV : c ∈ V := hseg (by rw [hmin_eq, hmax_eq]; exact Ioo_subset_Icc_self hc)
      have hslope : (G a u v - G a₀ u v) / (a - a₀) = (G a₀ u v - G a u v) / (a₀ - a) := by
        have : a₀ - a ≠ 0 := sub_ne_zero.2 hlt.ne'
        have : a - a₀ ≠ 0 := sub_ne_zero.2 hlt.ne
        field_simp; ring
      rw [hslope, ← hceq]
      exact hG'ε (hVpa c hcV) (hpq' hpu hpv)
    · have hmin_eq : min a₀ a = a₀ := min_eq_left hgt.le
      have hmax_eq : max a₀ a = a := max_eq_right hgt.le
      have hcd : ContinuousOn (fun c => G c u v) (Icc a₀ a) := fun c hc =>
        (hd c (hVsubU (hseg (by rwa [hmin_eq, hmax_eq]))) u huUx v hvUy).continuousAt.continuousWithinAt
      have hdd : ∀ c ∈ Ioo a₀ a, HasDerivAt (fun c => G c u v) (G' c u v) c :=
        fun c hc => hd c (hVsubU (hseg (by rw [hmin_eq, hmax_eq]; exact Ioo_subset_Icc_self hc)))
          u huUx v hvUy
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun c => G c u v) (fun c => G' c u v)
        hgt hcd hdd
      have hcV : c ∈ V := hseg (by rw [hmin_eq, hmax_eq]; exact Ioo_subset_Icc_self hc)
      rw [← hceq]
      exact hG'ε (hVpa c hcV) (hpq' hpu hpv)
  have hb1 := hmvt (x a) (y a₀) hxaUx hpxa hy0.1 hy0.2
  have hb2 := hmvt (x a₀) (y a) hx0.1 hx0.2 hyaUy hpya
  have hlow : G a (x a) (y a₀) - G a₀ (x a) (y a₀) ≤ φ a - φ a₀ := by
    have h1 : G a (x a) (y a₀) ≤ G a (x a) (y a) := hmax a haAU (y a₀) (hmem a₀ ha₀AU).2
    have h2 : G a₀ (x a₀) (y a₀) ≤ G a₀ (x a) (y a₀) := hmin a₀ ha₀AU (x a) (hmem a haAU).1
    dsimp only [φ]; linarith
  have hhigh : φ a - φ a₀ ≤ G a (x a₀) (y a) - G a₀ (x a₀) (y a) := by
    have h1 : G a (x a) (y a) ≤ G a (x a₀) (y a) := hmin a haAU (x a₀) (hmem a₀ ha₀AU).1
    have h2 : G a₀ (x a₀) (y a) ≤ G a₀ (x a₀) (y a₀) := hmax a₀ ha₀AU (y a) (hmem a haAU).2
    dsimp only [φ]; linarith
  rw [slope_def_field, Real.dist_eq, abs_lt]
  rw [abs_lt] at hb1 hb2
  rcases lt_or_gt_of_ne hane with hlt | hgt
  · have hneg : a - a₀ < 0 := sub_neg.2 hlt
    have hd1 : (G a (x a₀) (y a) - G a₀ (x a₀) (y a)) / (a - a₀) ≤ (φ a - φ a₀) / (a - a₀) :=
      div_le_div_of_nonpos_of_le hneg.le hhigh
    have hd2 : (φ a - φ a₀) / (a - a₀) ≤ (G a (x a) (y a₀) - G a₀ (x a) (y a₀)) / (a - a₀) :=
      div_le_div_of_nonpos_of_le hneg.le hlow
    exact ⟨by linarith [hb2.1], by linarith [hb1.2]⟩
  · have hpos : 0 < a - a₀ := sub_pos.2 hgt
    have hd1 : (G a (x a) (y a₀) - G a₀ (x a) (y a₀)) / (a - a₀) ≤ (φ a - φ a₀) / (a - a₀) :=
      div_le_div_of_nonneg_right hlow hpos.le
    have hd2 : (φ a - φ a₀) / (a - a₀) ≤ (G a (x a₀) (y a) - G a₀ (x a₀) (y a)) / (a - a₀) :=
      div_le_div_of_nonneg_right hhigh hpos.le
    exact ⟨by linarith [hb1.1], by linarith [hb2.2]⟩

/-- **Saddle-point envelope theorem (two-sided):** interior specialization of
`hasDerivWithinAt_saddle_envelope`. -/
theorem hasDerivAt_saddle_envelope {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {G G' : ℝ → X → Y → ℝ} {S : Set X} {T : Set Y} {x : ℝ → X} {y : ℝ → Y} {a₀ : ℝ}
    {U : Set ℝ} {Ux : Set X} {Uy : Set Y}
    (hU : U ∈ 𝓝 a₀) (hUx : Ux ∈ 𝓝 (x a₀)) (hUy : Uy ∈ 𝓝 (y a₀))
    (hmem : ∀ a ∈ U, x a ∈ S ∧ y a ∈ T)
    (hmin : ∀ a ∈ U, ∀ x' ∈ S, G a (x a) (y a) ≤ G a x' (y a))
    (hmax : ∀ a ∈ U, ∀ y' ∈ T, G a (x a) y' ≤ G a (x a) (y a))
    (hx : ContinuousAt x a₀) (hy : ContinuousAt y a₀)
    (hd : ∀ b ∈ U, ∀ u ∈ Ux, ∀ v ∈ Uy, HasDerivAt (fun c => G c u v) (G' b u v) b)
    (hcont : ContinuousAt (fun p : ℝ × X × Y => G' p.1 p.2.1 p.2.2) (a₀, x a₀, y a₀)) :
    HasDerivAt (fun a => G a (x a) (y a)) (G' a₀ (x a₀) (y a₀)) a₀ := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_saddle_envelope (mem_univ a₀) convex_univ hU hUx hUy
    (fun a ha => hmem a ha.2) (fun a ha => hmin a ha.2) (fun a ha => hmax a ha.2)
    hx.continuousWithinAt hy.continuousWithinAt hd hcont
