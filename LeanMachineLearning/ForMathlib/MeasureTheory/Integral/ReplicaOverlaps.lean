/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.MeasurePreservingSymmetry

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ReplicaIntegrateOut
public import LeanMachineLearning.ForMathlib.LinearAlgebra.DotProductCentering
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Exact replica integration for the global stage of Theorem 1.10.1

For a fixed disorder the replicas are independent with a common law `μ` and each replica carries
an a.e. bounded vector `v` of a real Hilbert space, with Gibbs mean `b = ∫ v dμ`. If a function
of the replicas does not depend on a coordinate `d`, integrating that replica out is an exact
identity. The statements with the suffix `_inner` are in this generality; those for coordinate
vectors on a finite space are special cases. This file records the three instances used in the
proof of Theorem 1.10.1 (Talagrand, Section 1.10, the computation after Eq. (1.328)):

* a block `R_{x d} - q` with both replicas absent from the rest becomes the global factor
  `N⁻¹ ∑ b² - q`;
* a pendant replica `d` of `R_{x d} - q` is replaced by the mean;
* a factor that is centered in an absent replica integrates to zero.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace MeasureTheory

/-- Injectivity of `Sum.elim ca da` as separate disjointness statements. -/
theorem sum_elim_injective_facts {V R : Type*} {ca da : V → R}
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) :
    (∀ u w, u ≠ w → ca u ≠ ca w) ∧ (∀ u w, u ≠ w → da u ≠ da w) ∧ ∀ u w, ca u ≠ da w :=
  ⟨fun u w h hh => h (Sum.inl_injective (hinj (by simpa using hh))),
    fun u w h hh => h (Sum.inr_injective (hinj (by simpa using hh))),
    fun u w hh => Sum.inl_ne_inr (hinj (a₁ := Sum.inl u) (a₂ := Sum.inr w) (by simpa using hh))⟩

/-- Facts about a block `{x, x'}` of a family of pairwise disjoint blocks. -/
theorem block_facts {V R : Type*} {ca da : V → R}
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) {u0 : V} {x x' : R}
    (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x)) :
    x ≠ x' ∧ ∀ u, u ≠ u0 → ca u ≠ x ∧ ca u ≠ x' ∧ da u ≠ x ∧ da u ≠ x' := by
  obtain ⟨hcc, hdd, hcd⟩ := sum_elim_injective_facts hinj
  rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2
    exact ⟨hcd u0 u0, fun u hu => ⟨hcc u u0 hu, (hcd u u0), (hcd u0 u).symm, hdd u u0 hu⟩⟩
  · subst h1 h2
    exact ⟨(hcd u0 u0).symm, fun u hu => ⟨hcd u u0, hcc u u0 hu, hdd u u0 hu,
      (hcd u0 u).symm⟩⟩

theorem ov_update_of_ne {α R H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : α → H) (c q : ℝ) [DecidableEq R] (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (ρ : R → α) (s : α) {r a a' : R} (h : a ≠ r) (h' : a' ≠ r) :
    ov (Function.update ρ r s) a a' = ov ρ a a' := by
  rw [hov, hov, Function.update_of_ne h, Function.update_of_ne h']

theorem A_update_of_ne {α R H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : α → H) (b : H) (c : ℝ) [DecidableEq R] (A : R → (R → α) → ℝ)
    (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    (ρ : R → α) (s : α) {r a : R} (h : a ≠ r) :
    A a (Function.update ρ r s) = A a ρ := by
  rw [hA, hA, Function.update_of_ne h]

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Replacing a replica by the mean: `R_{x d} - q` against the mean is `T_x + T`. -/
theorem overlap_mean_eq_inner (c q : ℝ) (u b : H) :
    c * inner ℝ u b - q = c * inner ℝ (u - b) b + (c * inner ℝ b b - q) := by
  rw [inner_sub_left]
  ring

/-- **The T-expansion of an overlap (Eq. (1.246)).** -/
theorem overlap_T_expansion_inner (c q : ℝ) (u w b : H) :
    c * inner ℝ u w - q = c * inner ℝ (u - b) (w - b) + c * inner ℝ (u - b) b +
      c * inner ℝ (w - b) b + (c * inner ℝ b b - q) := by
  simp only [inner_sub_left, inner_sub_right, real_inner_comm b w]
  ring

/-- The overlap `c ⟪f, g⟫ - q` of two bounded vector observables is bounded. -/
theorem memLp_top_const_mul_inner_sub {β : Type*} [MeasurableSpace β] {ν : Measure β}
    (c q : ℝ) {f g : β → H} (hf : MemLp f ∞ ν) (hg : MemLp g ∞ ν) [IsFiniteMeasure ν] :
    MemLp (fun z => c * inner ℝ (f z) (g z) - q) ∞ ν :=
  (((innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).memLp_of_bilin ∞ hf hg).const_mul c).sub (memLp_const q)

end Inner

variable {α R H : Type*} [MeasurableSpace α] [Fintype R] [DecidableEq R]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [DecidableEq R] [InnerProductSpace ℝ H] in
/-- A bounded observable of one replica is a bounded observable of the replica family. -/
theorem memLp_top_comp_eval (μ : Measure α) [IsProbabilityMeasure μ] {v : α → H}
    (hv : MemLp v ∞ μ) (x : R) :
    MemLp (fun ρ : R → α => v (ρ x)) ∞ (Measure.pi fun _ : R => μ) :=
  hv.comp_measurePreserving (measurePreserving_eval (fun _ : R => μ) x)

variable [CompleteSpace H]

/-- **A pendant replica is replaced by the Gibbs mean.** If `Z` does not depend on the replica
`d ≠ x`, then `d` can be averaged out of `R_{x d} - q`. -/
theorem integral_pi_overlap_pendant_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ) {x d : R}
    (hxd : x ≠ d) (Z : (R → α) → ℝ) (hZ : ∀ ρ s, Z (Function.update ρ d s) = Z ρ)
    (hZi : Integrable Z (Measure.pi fun _ : R => μ)) :
    ∫ ρ, Z ρ * (c * inner ℝ (v (ρ x)) (v (ρ d)) - q) ∂(Measure.pi fun _ : R => μ) =
      ∫ ρ, Z ρ * (c * inner ℝ (v (ρ x)) b - q) ∂(Measure.pi fun _ : R => μ) := by
  have hvi : Integrable v μ := hv.integrable le_top
  have h := integral_pi_integrate_out_replica_of_integrable μ d
    (fun ρ t => Z ρ * (c * inner ℝ (v (ρ x)) (v t) - q)) (fun ρ s t => by
      simp only [hZ, Function.update_of_ne hxd])
    (hZi.mul_of_top_left (memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv d)))
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_))
  have hi : Integrable (fun t => c * inner ℝ (v (ρ x)) (v t)) μ :=
    (hvi.const_inner (𝕜 := ℝ) (v (ρ x))).const_mul c
  simp only
  rw [integral_const_mul, integral_sub hi (integrable_const _), integral_const_mul,
    integral_inner hvi, hb]
  simp only [integral_const, probReal_univ, one_smul]

/-- **Integrating out a block.** If `Z` depends on neither replica of the block `{x, d}`, then
`R_{x d} - q` integrates to the global factor `c ⟪b, b⟫ - q`. -/
theorem integral_pi_overlap_block_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ) {x d : R}
    (hxd : x ≠ d) (Z : (R → α) → ℝ) (hZx : ∀ ρ s, Z (Function.update ρ x s) = Z ρ)
    (hZd : ∀ ρ s, Z (Function.update ρ d s) = Z ρ)
    (hZi : Integrable Z (Measure.pi fun _ : R => μ)) :
    ∫ ρ, Z ρ * (c * inner ℝ (v (ρ x)) (v (ρ d)) - q) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Z ρ ∂(Measure.pi fun _ : R => μ)) * (c * inner ℝ b b - q) := by
  have hvi : Integrable v μ := hv.integrable le_top
  rw [integral_pi_overlap_pendant_inner μ hv hb c q hxd Z hZd hZi]
  have h := integral_pi_integrate_out_replica_of_integrable μ x
    (fun ρ t => Z ρ * (c * inner ℝ (v t) b - q)) (fun ρ s t => by simp only [hZx])
    (hZi.mul_of_top_left (memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_const b)))
  rw [h, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  have hi : Integrable (fun t => c * inner ℝ (v t) b) μ := by
    simpa only [real_inner_comm b] using
      Integrable.const_mul (hvi.const_inner (𝕜 := ℝ) b) c
  have e : ∫ t, inner ℝ (v t) b ∂μ = inner ℝ b b := by
    simp only [real_inner_comm b]
    rw [integral_inner hvi, hb]
  simp only
  rw [integral_const_mul, integral_sub hi (integrable_const _), integral_const_mul, e]
  simp only [integral_const, probReal_univ, one_smul]

omit [DecidableEq R] in
/-- Independent replicas have mean overlap equal to the squared norm of their mean vector,
assuming only integrability of the vector observable. -/
theorem integral_pi_overlap_eq_mean_sq_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : Integrable v μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c : ℝ) {x y : R}
    (hxy : x ≠ y) :
    (∫ ρ, c * inner ℝ (v (ρ x)) (v (ρ y)) ∂(Measure.pi fun _ : R => μ)) =
      c * inner ℝ b b := by
  have hi : Integrable (fun p : α × α => inner ℝ (v p.1) (v p.2)) (μ.prod μ) :=
    hv.op_fst_snd (by fun_prop) ⟨1, fun x y => by
      simpa only [one_mul, Real.norm_eq_abs] using abs_real_inner_le_norm x y⟩ hv
  calc
    _ = ∫ p : α × α, c * inner ℝ (v p.1) (v p.2) ∂(μ.prod μ) :=
      integral_pi_pair_eq_prod_of_aestronglyMeasurable μ hxy
        (fun a b => c * inner ℝ (v a) (v b)) (hi.const_mul c).aestronglyMeasurable
    _ = c * inner ℝ b b := by
      rw [integral_const_mul, ← hb]
      exact congrArg (c * ·) (integral_prod_bilin (innerSL ℝ) hv hv)

omit [DecidableEq R] in
/-- **Talagrand (1.295).** Subtracting the Gibbs mean overlap leaves the centered pair
and the two single-replica terms, with no global term. This identity is model independent. -/
theorem integral_pi_overlap_centered_decomp_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c : ℝ) {r s : R}
    (hrs : r ≠ s) (x y : R) (ρ : R → α) :
    c * inner ℝ (v (ρ x)) (v (ρ y)) -
        (∫ τ, c * inner ℝ (v (τ r)) (v (τ s)) ∂(Measure.pi fun _ : R => μ)) =
      c * inner ℝ (v (ρ x) - b) (v (ρ y) - b) + c * inner ℝ (v (ρ x) - b) b +
        c * inner ℝ (v (ρ y) - b) b := by
  rw [integral_pi_overlap_eq_mean_sq_inner μ (hv.integrable le_top) hb c hrs]
  have h := overlap_T_expansion_inner c (c * inner ℝ b b) (v (ρ x)) (v (ρ y)) b
  linarith

/-- **A factor centered in an absent replica integrates to zero.** -/
theorem integral_pi_centered_replica_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c : ℝ) (d : R)
    (Z : (R → α) → ℝ) (hZ : ∀ ρ s, Z (Function.update ρ d s) = Z ρ)
    (hZi : Integrable Z (Measure.pi fun _ : R => μ))
    (w : (R → α) → H) (hw : ∀ ρ s, w (Function.update ρ d s) = w ρ)
    (hwm : MemLp w ∞ (Measure.pi fun _ : R => μ)) :
    ∫ ρ, Z ρ * (c * inner ℝ (w ρ) (v (ρ d) - b)) ∂(Measure.pi fun _ : R => μ) = 0 := by
  have hvi : Integrable v μ := hv.integrable le_top
  have hs : MemLp (fun ρ : R → α => v (ρ d) - b) ∞ (Measure.pi fun _ : R => μ) :=
    (memLp_top_comp_eval μ hv d).sub (memLp_const b)
  have hg : MemLp (fun ρ => c * inner ℝ (w ρ) (v (ρ d) - b)) ∞
      (Measure.pi fun _ : R => μ) := by
    have h := memLp_top_const_mul_inner_sub c 0 hwm hs
    simp only [sub_zero] at h
    exact h
  have h := integral_pi_integrate_out_replica_of_integrable μ d
    (fun ρ t => Z ρ * (c * inner ℝ (w ρ) (v t - b))) (fun ρ s t => by
      simp only [hZ, hw]) (hZi.mul_of_top_left hg)
  rw [h]
  have h0 : ∀ ρ : R → α, ∫ t, Z ρ * (c * inner ℝ (w ρ) (v t - b)) ∂μ = 0 := fun ρ => by
    have hs : Integrable (fun t => v t - b) μ := hvi.sub (integrable_const b)
    rw [integral_const_mul, integral_const_mul, integral_inner hs,
      integral_sub hvi (integrable_const b), hb]
    simp
  simp_rw [h0]
  simp only [integral_zero]

/-- **Integrating out a family of untouched blocks.** Let `ov ρ x y = c ⟪v(ρ x), v(ρ y)⟫ - q` and
let the blocks `{ca u, da u}` be pairwise disjoint. If `Z` does not depend on the replicas of the
blocks in `W`, the product of the block overlaps over `W` contributes `Tg ^ card W`. -/
theorem integral_pi_prod_overlap_blocks_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    {V : Type*} (ca da : V → R) (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    (W : Finset V) (Z : (R → α) → ℝ)
    (hZc : ∀ u ∈ W, ∀ ρ s, Z (Function.update ρ (ca u) s) = Z ρ)
    (hZd : ∀ u ∈ W, ∀ ρ s, Z (Function.update ρ (da u) s) = Z ρ)
    (hZi : Integrable Z (Measure.pi fun _ : R => μ)) :
    ∫ ρ, Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Z ρ ∂(Measure.pi fun _ : R => μ)) * Tg ^ W.card := by
  classical
  obtain ⟨hcc, hdd, hcd⟩ := sum_elim_injective_facts hinj
  have hne : ∀ u, ca u ≠ da u := fun u => hcd u u
  have hovm : ∀ x y, MemLp (fun ρ => ov ρ x y) ∞ (Measure.pi fun _ : R => μ) := fun x y => by
    simp only [hov]
    exact memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv y)
  induction W using Finset.induction_on generalizing Z with
  | empty => simp
  | insert w W hw ih =>
    have hind : ∀ (r : R) (s : α) (ρ : R → α), (∀ u ∈ W, r ≠ ca u ∧ r ≠ da u) →
        (∏ u ∈ W, ov (Function.update ρ r s) (ca u) (da u)) =
          ∏ u ∈ W, ov ρ (ca u) (da u) := fun r s ρ h => by
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [hov, hov, Function.update_of_ne (h u hu).1.symm, Function.update_of_ne (h u hu).2.symm]
    have hwu : ∀ u ∈ W, u ≠ w := fun u hu huw => hw (huw ▸ hu)
    have hZ'c : ∀ ρ s, (Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u)) =
        (Z (Function.update ρ (ca w) s) *
          ∏ u ∈ W, ov (Function.update ρ (ca w) s) (ca u) (da u)) := fun ρ s => by
      rw [hZc w (Finset.mem_insert_self w W), hind _ _ _ fun u hu =>
        ⟨(hcc u w (hwu u hu)).symm, (hcd w u)⟩]
    have hZ'd : ∀ ρ s, (Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u)) =
        (Z (Function.update ρ (da w) s) *
          ∏ u ∈ W, ov (Function.update ρ (da w) s) (ca u) (da u)) := fun ρ s => by
      rw [hZd w (Finset.mem_insert_self w W), hind _ _ _ fun u hu =>
        ⟨(hcd u w).symm, (hdd u w (hwu u hu)).symm⟩]
    have hprodm : ∀ T : Finset V, MemLp (fun ρ => ∏ u ∈ T, ov ρ (ca u) (da u)) ∞
        (Measure.pi fun _ : R => μ) := fun T => by
      induction T using Finset.induction_on with
      | empty => simpa using memLp_const (μ := Measure.pi fun _ : R => μ) (p := ∞) (1 : ℝ)
      | insert u T hu ih' =>
        simp only [Finset.prod_insert hu]
        exact (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin ∞ (hovm _ _) ih'
    have h1 := integral_pi_overlap_block_inner μ hv hb c q (hne w)
      (fun ρ => Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u)) (fun ρ s => (hZ'c ρ s).symm)
      (fun ρ s => (hZ'd ρ s).symm) (hZi.mul_of_top_left (hprodm W))
    have h2 := ih Z (fun u hu => hZc u (Finset.mem_insert_of_mem hu))
      (fun u hu => hZd u (Finset.mem_insert_of_mem hu)) hZi
    simp only [Finset.prod_insert hw, Finset.card_insert_of_notMem hw, pow_succ]
    simp only [← hov] at h1
    calc _ = ∫ ρ, (Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u)) * ov ρ (ca w) (da w)
          ∂(Measure.pi fun _ : R => μ) :=
          integral_congr_ae (Filter.Eventually.of_forall fun ρ => by ring)
      _ = _ := by rw [h1, h2, ← hTg]; ring

/-- **No block touches `x, y`:** the blocks contribute `Tg ^ card V`. -/
theorem integral_pi_blocks_untouched_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (hYi : Integrable Y (Measure.pi fun _ : R => μ))
    (hx : ∀ u, x ≠ ca u ∧ x ≠ da u) (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ ∂(Measure.pi fun _ : R => μ)) * Tg ^ Fintype.card V := by
  have h := integral_pi_prod_overlap_blocks_inner μ hv hb c q ov hov Tg hTg ca da hinj
    Finset.univ Y (fun u _ ρ s => hY ρ s _ (hx u).1.symm (hy u).1.symm)
    (fun u _ ρ s => hY ρ s _ (hx u).2.symm (hy u).2.symm) hYi
  simpa only [Finset.card_univ] using h

/-- **One replica of the pair touches a block.** Let `x` belong to the block `u0` with partner `x'`,
while `y` belongs to no block. Then the block `u0` is replaced by `T_x + T`. -/
theorem integral_pi_blocks_one_touched_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (hYi : Integrable Y (Measure.pi fun _ : R => μ))
    (u0 : V) (x' : R) (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ * (A x ρ + Tg) ∂(Measure.pi fun _ : R => μ)) * Tg ^ (Fintype.card V - 1) := by
  classical
  obtain ⟨hxx', hfac⟩ := block_facts hinj hx0
  have hy0 := hy u0
  have hyx' : x' ≠ y := by
    rcases hx0 with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2 ▸ hy0.2.symm
    · exact h1 ▸ hy0.1.symm
  have hsymm : ∀ ρ a a', ov ρ a a' = ov ρ a' a := fun ρ a a' => by
    rw [hov, hov, real_inner_comm]
  have hov0 : ∀ ρ, ov ρ (ca u0) (da u0) = ov ρ x x' := fun ρ => by
    rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hsymm]
  have hprod : ∀ ρ : R → α, Y ρ * ∏ u, ov ρ (ca u) (da u) =
      (Y ρ * ov ρ x x') * ∏ u ∈ Finset.univ.erase u0, ov ρ (ca u) (da u) := fun ρ => by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => ov ρ (ca u) (da u)) (Finset.mem_univ u0),
      hov0]
    ring
  simp_rw [hprod]
  have hovm : MemLp (fun ρ => ov ρ x x') ∞ (Measure.pi fun _ : R => μ) := by
    simp only [hov]
    exact memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv x')
  have h := integral_pi_prod_overlap_blocks_inner μ hv hb c q ov hov Tg hTg ca da hinj
    (Finset.univ.erase u0) (fun ρ => Y ρ * ov ρ x x')
    (fun u hu ρ s => by
      have hu0 := Finset.ne_of_mem_erase hu
      obtain ⟨h1, h2, h3, h4⟩ := hfac u hu0
      rw [hY ρ s _ h1 (hy u).1.symm, ov_update_of_ne v c q ov hov ρ s h1.symm h2.symm])
    (fun u hu ρ s => by
      have hu0 := Finset.ne_of_mem_erase hu
      obtain ⟨h1, h2, h3, h4⟩ := hfac u hu0
      rw [hY ρ s _ h3 (hy u).2.symm, ov_update_of_ne v c q ov hov ρ s h3.symm h4.symm])
    (hYi.mul_of_top_left hovm)
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ]
  congr 1
  simp only [hov]
  rw [integral_pi_overlap_pendant_inner μ hv hb c q hxx' Y
    (fun ρ s => hY ρ s _ hxx'.symm hyx') hYi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  have := overlap_mean_eq_inner c q (v (ρ x)) b
  simp only [hA, hTg, this]

/-- **Both replicas lie in one block.** The block `{x, y}` stays as the overlap `R_{x y} - q`. -/
theorem integral_pi_blocks_same_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (hYi : Integrable Y (Measure.pi fun _ : R => μ))
    (u0 : V) (hx0 : (ca u0 = x ∧ da u0 = y) ∨ (ca u0 = y ∧ da u0 = x)) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ * ov ρ x y ∂(Measure.pi fun _ : R => μ)) * Tg ^ (Fintype.card V - 1) := by
  classical
  obtain ⟨hxx', hfac⟩ := block_facts hinj hx0
  have hsymm : ∀ ρ a a', ov ρ a a' = ov ρ a' a := fun ρ a a' => by
    rw [hov, hov, real_inner_comm]
  have hov0 : ∀ ρ, ov ρ (ca u0) (da u0) = ov ρ x y := fun ρ => by
    rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hsymm]
  have hprod : ∀ ρ : R → α, Y ρ * ∏ u, ov ρ (ca u) (da u) =
      (Y ρ * ov ρ x y) * ∏ u ∈ Finset.univ.erase u0, ov ρ (ca u) (da u) := fun ρ => by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => ov ρ (ca u) (da u)) (Finset.mem_univ u0),
      hov0]
    ring
  simp_rw [hprod]
  have hovm : MemLp (fun ρ => ov ρ x y) ∞ (Measure.pi fun _ : R => μ) := by
    simp only [hov]
    exact memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv y)
  have h := integral_pi_prod_overlap_blocks_inner μ hv hb c q ov hov Tg hTg ca da hinj
    (Finset.univ.erase u0) (fun ρ => Y ρ * ov ρ x y)
    (fun u hu ρ s => by
      obtain ⟨h1, h2, h3, h4⟩ := hfac u (Finset.ne_of_mem_erase hu)
      rw [hY ρ s _ h1 h2, ov_update_of_ne v c q ov hov ρ s h1.symm h2.symm])
    (fun u hu ρ s => by
      obtain ⟨h1, h2, h3, h4⟩ := hfac u (Finset.ne_of_mem_erase hu)
      rw [hY ρ s _ h3 h4, ov_update_of_ne v c q ov hov ρ s h3.symm h4.symm])
    (hYi.mul_of_top_left hovm)
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ]

/-- **The two replicas lie in different blocks.** Both blocks are replaced by the pendant
expressions `T_x + T` and `T_y + T`. -/
theorem integral_pi_blocks_two_touched_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (hYi : Integrable Y (Measure.pi fun _ : R => μ))
    (u0 u1 : V) (hu01 : u0 ≠ u1) (x' y' : R)
    (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy0 : (ca u1 = y ∧ da u1 = y') ∨ (ca u1 = y' ∧ da u1 = y)) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ * ((A x ρ + Tg) * (A y ρ + Tg)) ∂(Measure.pi fun _ : R => μ)) *
        Tg ^ (Fintype.card V - 2) := by
  classical
  obtain ⟨hxx', hfx⟩ := block_facts hinj hx0
  obtain ⟨hyy', hfy⟩ := block_facts hinj hy0
  have hx1 := hfx u1 hu01.symm
  have hy1 := hfy u0 hu01
  -- the replicas of the two blocks are pairwise distinct
  have hxy' : x ≠ y' := by
    rcases hy0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h2]; exact fun h => hx1.2.2.1 h.symm
    · rw [← h1]; exact fun h => hx1.1 h.symm
  have hx'y : x' ≠ y := by
    rcases hy0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1]; exact fun h => hx1.2.1 h.symm
    · rw [← h2]; exact fun h => hx1.2.2.2 h.symm
  have hx'y' : x' ≠ y' := by
    rcases hy0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h2]; exact fun h => hx1.2.2.2 h.symm
    · rw [← h1]; exact fun h => hx1.2.1 h.symm
  have hsymm : ∀ ρ a a', ov ρ a a' = ov ρ a' a := fun ρ a a' => by
    rw [hov, hov, real_inner_comm]
  have hov0 : ∀ ρ, ov ρ (ca u0) (da u0) = ov ρ x x' := fun ρ => by
    rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hsymm]
  have hov1 : ∀ ρ, ov ρ (ca u1) (da u1) = ov ρ y y' := fun ρ => by
    rcases hy0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hsymm]
  have hprod : ∀ ρ : R → α, Y ρ * ∏ u, ov ρ (ca u) (da u) =
      (Y ρ * ov ρ x x' * ov ρ y y') *
        ∏ u ∈ (Finset.univ.erase u0).erase u1, ov ρ (ca u) (da u) := fun ρ => by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => ov ρ (ca u) (da u)) (Finset.mem_univ u0),
      ← Finset.mul_prod_erase (Finset.univ.erase u0) (fun u => ov ρ (ca u) (da u))
        (Finset.mem_erase.mpr ⟨hu01.symm, Finset.mem_univ u1⟩), hov0, hov1]
    ring
  simp_rw [hprod]
  have hrest : ∀ u ∈ (Finset.univ.erase u0).erase u1, u ≠ u0 ∧ u ≠ u1 := fun u hu =>
    ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hu), Finset.ne_of_mem_erase hu⟩
  have hovm : ∀ a a', MemLp (fun ρ => ov ρ a a') ∞ (Measure.pi fun _ : R => μ) := fun a a' => by
    simp only [hov]
    exact memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv a)
      (memLp_top_comp_eval μ hv a')
  have hAm : ∀ z, MemLp (fun ρ => A z ρ + Tg) ∞ (Measure.pi fun _ : R => μ) := fun z => by
    simp only [hA]
    have hs : MemLp (fun ρ : R → α => v (ρ z) - b) ∞ (Measure.pi fun _ : R => μ) :=
      (memLp_top_comp_eval μ hv z).sub (memLp_const b)
    have h := memLp_top_const_mul_inner_sub c (-Tg) hs (memLp_const b)
    simp only [sub_neg_eq_add] at h
    exact h
  have h := integral_pi_prod_overlap_blocks_inner μ hv hb c q ov hov Tg hTg ca da hinj
    ((Finset.univ.erase u0).erase u1) (fun ρ => Y ρ * ov ρ x x' * ov ρ y y')
    (fun u hu ρ s => by
      obtain ⟨hu0, hu1⟩ := hrest u hu
      obtain ⟨h1, h2, h3, h4⟩ := hfx u hu0
      obtain ⟨l1, l2, l3, l4⟩ := hfy u hu1
      rw [hY ρ s _ h1 l1, ov_update_of_ne v c q ov hov ρ s h1.symm h2.symm,
        ov_update_of_ne v c q ov hov ρ s l1.symm l2.symm])
    (fun u hu ρ s => by
      obtain ⟨hu0, hu1⟩ := hrest u hu
      obtain ⟨h1, h2, h3, h4⟩ := hfx u hu0
      obtain ⟨l1, l2, l3, l4⟩ := hfy u hu1
      rw [hY ρ s _ h3 l3, ov_update_of_ne v c q ov hov ρ s h3.symm h4.symm,
        ov_update_of_ne v c q ov hov ρ s l3.symm l4.symm])
    ((hYi.mul_of_top_left (hovm x x')).mul_of_top_left (hovm y y'))
  have hcard : ((Finset.univ.erase u0).erase u1).card = Fintype.card V - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hu01.symm, Finset.mem_univ u1⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ]
    omega
  rw [h, hcard]
  congr 1
  -- first integrate out `x'`, then `y'`
  have e1 := integral_pi_overlap_pendant_inner μ hv hb c q hxx' (fun ρ => Y ρ * ov ρ y y')
    (fun ρ s => by
      rw [hY ρ s _ hxx'.symm hx'y, ov_update_of_ne v c q ov hov ρ s hx'y.symm hx'y'.symm])
    (hYi.mul_of_top_left (hovm y y'))
  have e2 := integral_pi_overlap_pendant_inner μ hv hb c q hyy' (fun ρ => Y ρ * (A x ρ + Tg))
    (fun ρ s => by
      rw [hY ρ s _ hxy'.symm hyy'.symm, A_update_of_ne v b c A hA ρ s hxy'])
    (hYi.mul_of_top_left (hAm x))
  have hmx := fun ρ : R → α => overlap_mean_eq_inner c q (v (ρ x)) b
  have hmy := fun ρ : R → α => overlap_mean_eq_inner c q (v (ρ y)) b
  calc _ = ∫ ρ, (Y ρ * ov ρ y y') * (c * inner ℝ (v (ρ x)) (v (ρ x')) - q)
          ∂(Measure.pi fun _ : R => μ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ρ => by
          beta_reduce
          rw [hov ρ x x']; ring)
    _ = ∫ ρ, (Y ρ * ov ρ y y') * (c * inner ℝ (v (ρ x)) b - q)
          ∂(Measure.pi fun _ : R => μ) := e1
    _ = ∫ ρ, (Y ρ * (A x ρ + Tg)) * (c * inner ℝ (v (ρ y)) (v (ρ y')) - q)
          ∂(Measure.pi fun _ : R => μ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ρ => by
          beta_reduce
          rw [hov ρ y y', hmx ρ, hA, hTg]; ring)
    _ = ∫ ρ, (Y ρ * (A x ρ + Tg)) * (c * inner ℝ (v (ρ y)) b - q)
          ∂(Measure.pi fun _ : R => μ) := e2
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ρ => by
          beta_reduce
          rw [hmy ρ, hA y ρ, hTg]; ring)

omit [DecidableEq R] in
/-- **Orthogonality of the single-replica and pair variables of two distinct replicas.**
Let `A x`, `A y` be the centered single variables and `P x y` the doubly centered pair variable.
Every product in which some replica enters exactly once and centered has mean zero. -/
theorem integral_pi_two_replica_orthogonality_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c : ℝ)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * inner ℝ (v (ρ x) - b) (v (ρ y) - b))
    {x y : R} (hxy : x ≠ y) :
    (∫ ρ, A x ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, P x y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ * P x y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A y ρ * P x y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ * A y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ ^ 2 * A y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ * A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) = 0 := by
  classical
  have hAx : ∀ ρ s r, r ≠ x → A x (Function.update ρ r s) = A x ρ := fun ρ s r h =>
    A_update_of_ne v b c A hA ρ s h.symm
  have hAy : ∀ ρ s r, r ≠ y → A y (Function.update ρ r s) = A y ρ := fun ρ s r h =>
    A_update_of_ne v b c A hA ρ s h.symm
  have hcomm : ∀ (ρ : R → α) (z : R), A z ρ = c * inner ℝ b (v (ρ z) - b) := fun ρ z => by
    rw [hA, real_inner_comm]
  have hcomm' : ∀ (ρ : R → α) (z z' : R), P z z' ρ =
      c * inner ℝ (v (ρ z') - b) (v (ρ z) - b) := fun ρ z z' => by
    rw [hP, real_inner_comm]
  have hw : ∀ z, MemLp (fun ρ : R → α => v (ρ z) - b) ∞ (Measure.pi fun _ : R => μ) :=
    fun z => (memLp_top_comp_eval μ hv z).sub (memLp_const b)
  have hAm : ∀ z, MemLp (A z) ∞ (Measure.pi fun _ : R => μ) := fun z => by
    rw [show A z = fun ρ => c * inner ℝ (v (ρ z) - b) b - 0 from
      funext fun ρ => by rw [hA, sub_zero]]
    exact memLp_top_const_mul_inner_sub c 0 (hw z) (memLp_const b)
  have hAi : ∀ z, Integrable (A z) (Measure.pi fun _ : R => μ) := fun z =>
    (hAm z).integrable le_top
  have hA2 : ∀ z, Integrable (fun ρ => A z ρ ^ 2) (Measure.pi fun _ : R => μ) := fun z => by
    have h : Integrable (fun ρ => A z ρ * A z ρ) (Measure.pi fun _ : R => μ) :=
      (hAi z).mul_of_top_left (hAm z)
    simpa only [pow_two] using h
  have hone : Integrable (fun _ : R → α => (1 : ℝ)) (Measure.pi fun _ : R => μ) :=
    integrable_const 1
  have hbt : MemLp (fun _ : R → α => b) ∞ (Measure.pi fun _ : R => μ) := memLp_const b
  have hwx : ∀ (ρ : R → α) (s : α), v (Function.update ρ y s x) - b = v (ρ x) - b :=
    fun ρ s => by rw [Function.update_of_ne hxy]
  have hwy : ∀ (ρ : R → α) (s : α), v (Function.update ρ x s y) - b = v (ρ y) - b :=
    fun ρ s => by rw [Function.update_of_ne hxy.symm]
  have e1 := integral_pi_centered_replica_inner μ hv hb c x (fun _ => 1) (fun _ _ => rfl) hone
    (fun _ => b) (fun _ _ => rfl) hbt
  have e2 := integral_pi_centered_replica_inner μ hv hb c y (fun _ => 1) (fun _ _ => rfl) hone
    (fun _ => b) (fun _ _ => rfl) hbt
  have e3 := integral_pi_centered_replica_inner μ hv hb c y (fun _ => 1) (fun _ _ => rfl) hone
    (fun ρ => v (ρ x) - b) hwx (hw x)
  have e4 := integral_pi_centered_replica_inner μ hv hb c y (A x)
    (fun ρ s => hAx ρ s y hxy.symm) (hAi x) (fun ρ => v (ρ x) - b) hwx (hw x)
  have e5 := integral_pi_centered_replica_inner μ hv hb c x (A y)
    (fun ρ s => hAy ρ s x hxy) (hAi y) (fun ρ => v (ρ y) - b) hwy (hw y)
  have e6 := integral_pi_centered_replica_inner μ hv hb c y (A x)
    (fun ρ s => hAx ρ s y hxy.symm) (hAi x) (fun _ => b) (fun _ _ => rfl) hbt
  have e7 := integral_pi_centered_replica_inner μ hv hb c y (fun ρ => A x ρ ^ 2)
    (fun ρ s => by rw [hAx ρ s y hxy.symm]) (hA2 x) (fun _ => b) (fun _ _ => rfl) hbt
  have e8 := integral_pi_centered_replica_inner μ hv hb c x (fun ρ => A y ρ ^ 2)
    (fun ρ s => by rw [hAy ρ s x hxy]) (hA2 y) (fun _ => b) (fun _ _ => rfl) hbt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul, ← hcomm] using e1
  · simpa only [one_mul, ← hcomm] using e2
  · simpa only [one_mul, ← hP] using e3
  · simpa only [← hP] using e4
  · simpa only [← hcomm'] using e5
  · simpa only [← hcomm] using e6
  · simpa only [← hcomm, ← mul_assoc, pow_two] using e7
  · simp only [← hcomm] at e8
    rw [← e8]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ρ => mul_comm _ _)

omit [DecidableEq R] in
/-- **The two-replica integrals needed in Theorem 1.10.1.** With `R_{xy} - q = P + A_x + A_y + Tg`,
the integral of `R_{xy} - q` against the pendant expressions of the touching blocks reduces to the
second moments of the centered variables and the third mixed moment `∫ P A_x A_y`. -/
theorem integral_pi_two_replica_overlap_moments_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * inner ℝ (v (ρ x) - b) (v (ρ y) - b))
    {x y : R} (hxy : x ≠ y) :
    (∫ ρ, ov ρ x y ∂(Measure.pi fun _ : R => μ)) = Tg ∧
    (∫ ρ, ov ρ x y * (A x ρ + Tg) ∂(Measure.pi fun _ : R => μ)) =
      (∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2 ∧
    (∫ ρ, ov ρ x y * ov ρ x y ∂(Measure.pi fun _ : R => μ)) =
      (∫ ρ, P x y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2 ∧
    (∫ ρ, ov ρ x y * ((A x ρ + Tg) * (A y ρ + Tg)) ∂(Measure.pi fun _ : R => μ)) =
      Tg ^ 3 + Tg * ((∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ))) +
        ∫ ρ, P x y ρ * A x ρ * A y ρ ∂(Measure.pi fun _ : R => μ) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ :=
    integral_pi_two_replica_orthogonality_inner μ hv hb c A hA P hP hxy
  have hexp : ∀ ρ, ov ρ x y = P x y ρ + A x ρ + A y ρ + Tg := fun ρ => by
    rw [hov, hTg, hP, hA, hA]
    exact overlap_T_expansion_inner c q (v (ρ x)) (v (ρ y)) b
  have hw : ∀ z, MemLp (fun ρ : R → α => v (ρ z) - b) ∞ (Measure.pi fun _ : R => μ) :=
    fun z => (memLp_top_comp_eval μ hv z).sub (memLp_const b)
  have hAm : ∀ z, MemLp (A z) ∞ (Measure.pi fun _ : R => μ) := fun z => by
    rw [show A z = fun ρ => c * inner ℝ (v (ρ z) - b) b - 0 from
      funext fun ρ => by rw [hA, sub_zero]]
    exact memLp_top_const_mul_inner_sub c 0 (hw z) (memLp_const b)
  have hPm : MemLp (P x y) ∞ (Measure.pi fun _ : R => μ) := by
    rw [show P x y = fun ρ => c * inner ℝ (v (ρ x) - b) (v (ρ y) - b) - 0 from
      funext fun ρ => by rw [hP, sub_zero]]
    exact memLp_top_const_mul_inner_sub c 0 (hw x) (hw y)
  -- every polynomial in the bounded variables is integrable
  have hmul : ∀ f g : (R → α) → ℝ, MemLp f ∞ (Measure.pi fun _ : R => μ) →
      MemLp g ∞ (Measure.pi fun _ : R => μ) →
      MemLp (fun ρ => f ρ * g ρ) ∞ (Measure.pi fun _ : R => μ) := fun f g hf hg =>
    (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin ∞ hf hg
  have hint : ∀ f : (R → α) → ℝ, MemLp f ∞ (Measure.pi fun _ : R => μ) →
      Integrable f (Measure.pi fun _ : R => μ) := fun f hf => hf.integrable le_top
  have hc : ∀ k : ℝ, ∫ _ρ : R → α, k ∂(Measure.pi fun _ : R => μ) = k := fun k => by
    simp
  have hsq : ∀ f : (R → α) → ℝ, MemLp f ∞ (Measure.pi fun _ : R => μ) →
      MemLp (fun ρ => f ρ ^ 2) ∞ (Measure.pi fun _ : R => μ) := fun f hf => by
    simpa only [pow_two] using hmul f f hf hf
  have hadd : ∀ f g : (R → α) → ℝ, MemLp f ∞ (Measure.pi fun _ : R => μ) →
      MemLp g ∞ (Measure.pi fun _ : R => μ) →
      MemLp (fun ρ => f ρ + g ρ) ∞ (Measure.pi fun _ : R => μ) := fun f g hf hg =>
    MemLp.add hf hg
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    have hAx := hAm x
    have hAy := hAm y
  · simp_rw [hexp]
    rw [integral_add, integral_add, integral_add, hc, o1, o2, o3]
    · ring
    all_goals
      refine hint _ ?_
      repeat' with_reducible first
        | exact hAx
        | exact hAy
        | exact hPm
        | exact memLp_const _
        | apply hadd
  · have h : ∀ ρ, ov ρ x y * (A x ρ + Tg) = A x ρ * P x y ρ + Tg * P x y ρ + A x ρ ^ 2 +
        2 * Tg * A x ρ + A x ρ * A y ρ + Tg * A y ρ + Tg ^ 2 := fun ρ => by
      rw [hexp]; ring
    simp_rw [h]
    rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
      integral_const_mul, integral_const_mul, integral_const_mul, hc, o1, o2, o3, o4, o6]
    · ring
    all_goals
      refine hint _ ?_
      repeat' with_reducible first
        | exact hAx
        | exact hAy
        | exact hPm
        | exact memLp_const _
        | apply hadd
        | apply hsq
        | apply hmul
  · have h : ∀ ρ, ov ρ x y * ov ρ x y = P x y ρ ^ 2 + A x ρ ^ 2 + A y ρ ^ 2 + Tg ^ 2 +
        2 * (A x ρ * P x y ρ) + 2 * (A y ρ * P x y ρ) + 2 * Tg * P x y ρ +
        2 * (A x ρ * A y ρ) + 2 * Tg * A x ρ + 2 * Tg * A y ρ := fun ρ => by
      rw [hexp]; ring
    simp_rw [h]
    rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
      integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hc,
      o1, o2, o3, o4, o5, o6]
    · ring
    all_goals
      refine hint _ ?_
      repeat' with_reducible first
        | exact hAx
        | exact hAy
        | exact hPm
        | exact memLp_const _
        | apply hadd
        | apply hsq
        | apply hmul
  · have h : ∀ ρ, ov ρ x y * ((A x ρ + Tg) * (A y ρ + Tg)) =
        P x y ρ * A x ρ * A y ρ + Tg * (A x ρ * P x y ρ) + Tg * (A y ρ * P x y ρ) +
        Tg ^ 2 * P x y ρ + A x ρ ^ 2 * A y ρ + Tg * A x ρ ^ 2 + Tg * (A x ρ * A y ρ) +
        Tg ^ 2 * A x ρ + A x ρ * A y ρ ^ 2 + Tg * (A x ρ * A y ρ) + Tg * A y ρ ^ 2 +
        Tg ^ 2 * A y ρ + Tg * (A x ρ * A y ρ) + Tg ^ 2 * A x ρ + Tg ^ 2 * A y ρ + Tg ^ 3 :=
      fun ρ => by rw [hexp]; ring
    simp_rw [h]
    rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
      integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
      integral_add, integral_add, integral_add]
    · simp only [integral_const_mul, hc, o1, o2, o3, o4, o5, o6, o7, o8]
      ring
    all_goals
      refine hint _ ?_
      repeat' with_reducible first
        | exact hAx
        | exact hAy
        | exact hPm
        | exact memLp_const _
        | apply hadd
        | apply hsq
        | apply hmul

omit [DecidableEq R] in
/-- **Case 0: neither `x` nor `y` lies in a block.** -/
theorem integral_pi_overlap_blocks_untouched_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * inner ℝ (v (ρ x) - b) (v (ρ y) - b))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (hx : ∀ u, x ≠ ca u ∧ x ≠ da u) (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      Tg ^ (Fintype.card V + 1) := by
  classical
  have hovi : Integrable (fun ρ => ov ρ x y) (Measure.pi fun _ : R => μ) := by
    simp only [hov]
    exact (memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv y)).integrable le_top
  rw [integral_pi_blocks_untouched_inner μ hv hb c q ov hov Tg hTg ca da hinj
    (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) hovi hx hy,
    (integral_pi_two_replica_overlap_moments_inner μ hv hb c q ov hov Tg hTg A hA P hP hxy).1]
  ring

omit [DecidableEq R] in
/-- **Case 1: `x` lies in a block, `y` does not.** -/
theorem integral_pi_overlap_blocks_one_touched_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * inner ℝ (v (ρ x) - b) (v (ρ y) - b))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 : V) (x' : R) (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      ((∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2) * Tg ^ (Fintype.card V - 1) := by
  classical
  have hovi : Integrable (fun ρ => ov ρ x y) (Measure.pi fun _ : R => μ) := by
    simp only [hov]
    exact (memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv y)).integrable le_top
  rw [integral_pi_blocks_one_touched_inner μ hv hb c q ov hov Tg hTg A hA ca da hinj
    (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) hovi u0 x' hx0 hy,
    (integral_pi_two_replica_overlap_moments_inner μ hv hb c q ov hov Tg hTg A hA P hP hxy).2.1]

omit [DecidableEq R] in
/-- **Case 2: `x` and `y` form one block.** -/
theorem integral_pi_overlap_blocks_same_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * inner ℝ (v (ρ x) - b) (v (ρ y) - b))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 : V) (hx0 : (ca u0 = x ∧ da u0 = y) ∨ (ca u0 = y ∧ da u0 = x)) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      ((∫ ρ, P x y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2) *
        Tg ^ (Fintype.card V - 1) := by
  classical
  have hovi : Integrable (fun ρ => ov ρ x y) (Measure.pi fun _ : R => μ) := by
    simp only [hov]
    exact (memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv y)).integrable le_top
  rw [integral_pi_blocks_same_inner μ hv hb c q ov hov Tg hTg ca da hinj (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) hovi u0 hx0,
    (integral_pi_two_replica_overlap_moments_inner μ hv hb c q ov hov Tg hTg A hA P hP hxy).2.2.1]

omit [DecidableEq R] in
/-- **Case 3: `x` and `y` lie in different blocks.** -/
theorem integral_pi_overlap_blocks_two_touched_inner (μ : Measure α) [IsProbabilityMeasure μ]
    {v : α → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ t, v t ∂μ = b) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = c * inner ℝ (v (ρ x)) (v (ρ y)) - q)
    (Tg : ℝ) (hTg : Tg = c * inner ℝ b b - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * inner ℝ (v (ρ x) - b) b)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * inner ℝ (v (ρ x) - b) (v (ρ y) - b))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 u1 : V) (hu01 : u0 ≠ u1) (x' y' : R)
    (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy0 : (ca u1 = y ∧ da u1 = y') ∨ (ca u1 = y' ∧ da u1 = y)) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (Tg ^ 3 + Tg * ((∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ))) +
        ∫ ρ, P x y ρ * A x ρ * A y ρ ∂(Measure.pi fun _ : R => μ)) *
        Tg ^ (Fintype.card V - 2) := by
  classical
  have hovi : Integrable (fun ρ => ov ρ x y) (Measure.pi fun _ : R => μ) := by
    simp only [hov]
    exact (memLp_top_const_mul_inner_sub c q (memLp_top_comp_eval μ hv x)
      (memLp_top_comp_eval μ hv y)).integrable le_top
  rw [integral_pi_blocks_two_touched_inner μ hv hb c q ov hov Tg hTg A hA ca da hinj
    (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) hovi u0 u1 hu01 x' y'
    hx0 hy0,
    (integral_pi_two_replica_overlap_moments_inner μ hv hb c q ov hov Tg hTg A hA P hP hxy).2.2.2]

/-! ### Coordinates on a finite space -/

section Coordinates

variable {I : Type*} [Fintype I]

/-- The inner product of two coordinate vectors is the sum of the products of coordinates. -/
theorem inner_toLp_two_eq_sum (a c : I → ℝ) :
    inner ℝ (WithLp.toLp 2 a) (WithLp.toLp 2 c) = ∑ i, a i * c i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] [Finite β]

/-- The mean of coordinate vectors on a finite space is computed coordinate by coordinate. -/
theorem integral_toLp_two_eq_of_finite (μ : Measure β) [IsFiniteMeasure μ] (v : β → I → ℝ)
    {b : I → ℝ} (hb : ∀ i, ∫ t, v t i ∂μ = b i) :
    ∫ t, WithLp.toLp 2 (v t) ∂μ = WithLp.toLp 2 b := by
  ext i
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (Integrable.of_finite (μ := μ) (f := fun t => WithLp.toLp 2 (v t)))
  exact h.symm.trans (hb i)

omit [DecidableEq R] in
/-- **Talagrand (1.295)** for coordinate vectors on a finite space. -/
theorem integral_pi_overlap_centered_decomp (μ : Measure β) [IsProbabilityMeasure μ]
    (v : β → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i)
    (c : ℝ) {r s : R} (hrs : r ≠ s) (x y : R) (ρ : R → β) :
    (c * ∑ i, v (ρ x) i * v (ρ y) i) -
        (∫ τ, c * ∑ i, v (τ r) i * v (τ s) i ∂(Measure.pi fun _ : R => μ)) =
      (c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i)) +
        (c * ∑ i, (v (ρ x) i - b i) * b i) +
        (c * ∑ i, (v (ρ y) i - b i) * b i) := by
  have h := integral_pi_overlap_centered_decomp_inner μ
    (v := fun t => WithLp.toLp 2 (v t)) MemLp.of_discrete
    (integral_toLp_two_eq_of_finite μ v hb) c hrs x y ρ
  simpa only [← WithLp.toLp_sub, inner_toLp_two_eq_sum, Pi.sub_apply] using h

/-- **Integrating out a family of untouched blocks**, for coordinate vectors on a finite
space. -/
theorem integral_pi_prod_overlap_blocks (μ : Measure β) [IsProbabilityMeasure μ]
    (v : β → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → β) → R → R → ℝ) (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    {V : Type*} (ca da : V → R) (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    (W : Finset V) (Z : (R → β) → ℝ)
    (hZc : ∀ u ∈ W, ∀ ρ s, Z (Function.update ρ (ca u) s) = Z ρ)
    (hZd : ∀ u ∈ W, ∀ ρ s, Z (Function.update ρ (da u) s) = Z ρ) :
    ∫ ρ, Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Z ρ ∂(Measure.pi fun _ : R => μ)) * Tg ^ W.card :=
  integral_pi_prod_overlap_blocks_inner μ (v := fun t => WithLp.toLp 2 (v t)) MemLp.of_discrete
    (integral_toLp_two_eq_of_finite μ v hb) c q ov
    (fun ρ x y => by rw [hov, inner_toLp_two_eq_sum]) Tg (by rw [hTg, inner_toLp_two_eq_sum])
    ca da hinj W Z hZc hZd Integrable.of_finite

omit [DecidableEq R] in
/-- **Case 0: neither `x` nor `y` lies in a block**, for coordinate vectors. -/
theorem integral_pi_overlap_blocks_untouched (μ : Measure β) [IsProbabilityMeasure μ]
    (v : β → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → β) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → β) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → β) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (hx : ∀ u, x ≠ ca u ∧ x ≠ da u) (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      Tg ^ (Fintype.card V + 1) :=
  integral_pi_overlap_blocks_untouched_inner μ (v := fun t => WithLp.toLp 2 (v t))
    MemLp.of_discrete (integral_toLp_two_eq_of_finite μ v hb) c q ov
    (fun ρ x y => by rw [hov, inner_toLp_two_eq_sum]) Tg (by rw [hTg, inner_toLp_two_eq_sum]) A
    (fun x ρ => by
      rw [hA, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]; simp only [Pi.sub_apply]) P
    (fun x y ρ => by
      rw [hP, ← WithLp.toLp_sub, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]
      simp only [Pi.sub_apply]) ca da hinj hxy hx hy

omit [DecidableEq R] in
/-- **Case 1: `x` lies in a block, `y` does not**, for coordinate vectors. -/
theorem integral_pi_overlap_blocks_one_touched (μ : Measure β) [IsProbabilityMeasure μ]
    (v : β → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → β) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → β) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → β) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 : V) (x' : R) (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      ((∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2) * Tg ^ (Fintype.card V - 1) :=
  integral_pi_overlap_blocks_one_touched_inner μ (v := fun t => WithLp.toLp 2 (v t))
    MemLp.of_discrete (integral_toLp_two_eq_of_finite μ v hb) c q ov
    (fun ρ x y => by rw [hov, inner_toLp_two_eq_sum]) Tg (by rw [hTg, inner_toLp_two_eq_sum]) A
    (fun x ρ => by
      rw [hA, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]; simp only [Pi.sub_apply]) P
    (fun x y ρ => by
      rw [hP, ← WithLp.toLp_sub, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]
      simp only [Pi.sub_apply]) ca da hinj hxy u0 x' hx0 hy

omit [DecidableEq R] in
/-- **Case 2: `x` and `y` form one block**, for coordinate vectors. -/
theorem integral_pi_overlap_blocks_same (μ : Measure β) [IsProbabilityMeasure μ]
    (v : β → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → β) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → β) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → β) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 : V) (hx0 : (ca u0 = x ∧ da u0 = y) ∨ (ca u0 = y ∧ da u0 = x)) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      ((∫ ρ, P x y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2) *
        Tg ^ (Fintype.card V - 1) :=
  integral_pi_overlap_blocks_same_inner μ (v := fun t => WithLp.toLp 2 (v t))
    MemLp.of_discrete (integral_toLp_two_eq_of_finite μ v hb) c q ov
    (fun ρ x y => by rw [hov, inner_toLp_two_eq_sum]) Tg (by rw [hTg, inner_toLp_two_eq_sum]) A
    (fun x ρ => by
      rw [hA, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]; simp only [Pi.sub_apply]) P
    (fun x y ρ => by
      rw [hP, ← WithLp.toLp_sub, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]
      simp only [Pi.sub_apply]) ca da hinj hxy u0 hx0

omit [DecidableEq R] in
/-- **Case 3: `x` and `y` lie in different blocks**, for coordinate vectors. -/
theorem integral_pi_overlap_blocks_two_touched (μ : Measure β) [IsProbabilityMeasure μ]
    (v : β → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → β) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → β) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → β) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 u1 : V) (hu01 : u0 ≠ u1) (x' y' : R)
    (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy0 : (ca u1 = y ∧ da u1 = y') ∨ (ca u1 = y' ∧ da u1 = y)) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (Tg ^ 3 + Tg * ((∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ))) +
        ∫ ρ, P x y ρ * A x ρ * A y ρ ∂(Measure.pi fun _ : R => μ)) *
        Tg ^ (Fintype.card V - 2) :=
  integral_pi_overlap_blocks_two_touched_inner μ (v := fun t => WithLp.toLp 2 (v t))
    MemLp.of_discrete (integral_toLp_two_eq_of_finite μ v hb) c q ov
    (fun ρ x y => by rw [hov, inner_toLp_two_eq_sum]) Tg (by rw [hTg, inner_toLp_two_eq_sum]) A
    (fun x ρ => by
      rw [hA, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]; simp only [Pi.sub_apply]) P
    (fun x y ρ => by
      rw [hP, ← WithLp.toLp_sub, ← WithLp.toLp_sub, inner_toLp_two_eq_sum]
      simp only [Pi.sub_apply]) ca da hinj hxy u0 u1 hu01 x' y' hx0 hy0

end Coordinates

end MeasureTheory
