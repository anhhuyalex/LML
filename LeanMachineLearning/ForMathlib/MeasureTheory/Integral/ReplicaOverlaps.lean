/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ReplicaIntegrateOut
public import LeanMachineLearning.ForMathlib.LinearAlgebra.DotProductCentering

/-!
# Exact replica integration for the global stage of Theorem 1.10.1

For a fixed disorder the replicas are independent with a common law `μ` on a finite space and
the Gibbs mean `b i = ∫ v t i dμ`. If a function of the replicas does not depend on a coordinate
`d`, integrating that replica out is an exact identity. This file records the three instances used
in the proof of Theorem 1.10.1 (Talagrand, Section 1.10, the computation after Eq. (1.328)):

* a block `R_{x d} - q` with both replicas absent from the rest becomes the global factor
  `N⁻¹ ∑ b² - q`;
* a pendant replica `d` of `R_{x d} - q` is replaced by the mean;
* a factor that is centered in an absent replica integrates to zero.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

namespace MeasureTheory

variable {α R I : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
  [Fintype R] [DecidableEq R] [Fintype I]

/-- **A pendant replica is replaced by the Gibbs mean.** If `Z` does not depend on the replica
`d ≠ x`, then `d` can be averaged out of `R_{x d} - q`. -/
theorem integral_pi_overlap_pendant (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ) {x d : R}
    (hxd : x ≠ d) (Z : (R → α) → ℝ) (hZ : ∀ ρ s, Z (Function.update ρ d s) = Z ρ) :
    ∫ ρ, Z ρ * ((c * ∑ i, v (ρ x) i * v (ρ d) i) - q) ∂(Measure.pi fun _ : R => μ) =
      ∫ ρ, Z ρ * ((c * ∑ i, v (ρ x) i * b i) - q) ∂(Measure.pi fun _ : R => μ) := by
  have h := integral_pi_integrate_out_replica μ d
    (fun ρ t => Z ρ * ((c * ∑ i, v (ρ x) i * v t i) - q)) (fun ρ s t => by
      simp only [hZ, Function.update_of_ne hxd])
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_))
  simp only
  rw [integral_const_mul, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [integral_const_mul, hb, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- **Integrating out a block.** If `Z` depends on neither replica of the block `{x, d}`, then
`R_{x d} - q` integrates to the global factor `c ∑ b² - q`. -/
theorem integral_pi_overlap_block (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ) {x d : R}
    (hxd : x ≠ d) (Z : (R → α) → ℝ) (hZx : ∀ ρ s, Z (Function.update ρ x s) = Z ρ)
    (hZd : ∀ ρ s, Z (Function.update ρ d s) = Z ρ) :
    ∫ ρ, Z ρ * ((c * ∑ i, v (ρ x) i * v (ρ d) i) - q) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Z ρ ∂(Measure.pi fun _ : R => μ)) * ((c * ∑ i, b i * b i) - q) := by
  rw [integral_pi_overlap_pendant μ v b hb c q hxd Z hZd]
  have h := integral_pi_integrate_out_replica μ x
    (fun ρ t => Z ρ * ((c * ∑ i, v t i * b i) - q)) (fun ρ s t => by simp only [hZx])
  rw [h, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  simp only
  rw [integral_const_mul, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [integral_mul_const, hb, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- Independent replicas have mean overlap equal to the squared mean vector. -/
theorem integral_pi_overlap_eq_mean_sq (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i)
    (c : ℝ) {x y : R} (hxy : x ≠ y) :
    (∫ ρ, c * ∑ i, v (ρ x) i * v (ρ y) i ∂(Measure.pi fun _ : R => μ)) =
      c * ∑ i, b i * b i := by
  have hm := integral_pi_overlap_block μ v b hb c 0 hxy
    (fun _ => 1) (fun _ _ => rfl) (fun _ _ => rfl)
  simpa only [one_mul, sub_zero, integral_const, probReal_univ, one_smul] using hm

/-- **Talagrand (1.295).** Subtracting the Gibbs mean overlap leaves the centered pair
and the two single-replica terms, with no global term. This identity is model independent. -/
theorem integral_pi_overlap_centered_decomp (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i)
    (c : ℝ) {x y : R} (hxy : x ≠ y) (ρ : R → α) :
    (c * ∑ i, v (ρ x) i * v (ρ y) i) -
        (∫ τ, c * ∑ i, v (τ x) i * v (τ y) i ∂(Measure.pi fun _ : R => μ)) =
      (c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i)) +
        (c * ∑ i, (v (ρ x) i - b i) * b i) +
        (c * ∑ i, (v (ρ y) i - b i) * b i) := by
  rw [integral_pi_overlap_eq_mean_sq μ v b hb c hxy]
  simpa only [dotProduct, Pi.sub_apply] using dotProduct_sub_mean_decomp c (v (ρ x)) (v (ρ y)) b

/-- **A factor centered in an absent replica integrates to zero.** -/
theorem integral_pi_centered_replica (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c : ℝ) (d : R)
    (Z : (R → α) → ℝ) (hZ : ∀ ρ s, Z (Function.update ρ d s) = Z ρ)
    (w : (R → α) → I → ℝ) (hw : ∀ ρ s, w (Function.update ρ d s) = w ρ) :
    ∫ ρ, Z ρ * (c * ∑ i, w ρ i * (v (ρ d) i - b i)) ∂(Measure.pi fun _ : R => μ) = 0 := by
  have h := integral_pi_integrate_out_replica μ d
    (fun ρ t => Z ρ * (c * ∑ i, w ρ i * (v t i - b i))) (fun ρ s t => by
      simp only [hZ, hw])
  rw [h]
  have h0 : ∀ ρ : R → α, ∫ t, Z ρ * (c * ∑ i, w ρ i * (v t i - b i)) ∂μ = 0 := fun ρ => by
    rw [integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp only [integral_const_mul, integral_sub Integrable.of_finite Integrable.of_finite, hb,
      integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, mul_zero,
      Finset.sum_const_zero]
  simp_rw [h0]
  simp only [integral_zero]

/-- **Integrating out a family of untouched blocks.** Let `ov ρ x y = c ∑ v(ρ x) v(ρ y) - q` and
let the blocks `{ca u, da u}` be pairwise disjoint. If `Z` does not depend on the replicas of the
blocks in `W`, the product of the block overlaps over `W` contributes `Tg ^ card W`. -/
theorem integral_pi_prod_overlap_blocks (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ) (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    {V : Type*} (ca da : V → R) (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    (W : Finset V) (Z : (R → α) → ℝ)
    (hZc : ∀ u ∈ W, ∀ ρ s, Z (Function.update ρ (ca u) s) = Z ρ)
    (hZd : ∀ u ∈ W, ∀ ρ s, Z (Function.update ρ (da u) s) = Z ρ) :
    ∫ ρ, Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Z ρ ∂(Measure.pi fun _ : R => μ)) * Tg ^ W.card := by
  have hcc : ∀ u w, u ≠ w → ca u ≠ ca w := fun u w h hh =>
    h (Sum.inl_injective (hinj (by simpa using hh)))
  have hdd : ∀ u w, u ≠ w → da u ≠ da w := fun u w h hh =>
    h (Sum.inr_injective (hinj (by simpa using hh)))
  have hcd : ∀ u w, ca u ≠ da w := fun u w hh => by
    have := hinj (a₁ := Sum.inl u) (a₂ := Sum.inr w) (by simpa using hh)
    exact Sum.inl_ne_inr this
  have hne : ∀ u, ca u ≠ da u := fun u => hcd u u
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
    have h1 := integral_pi_overlap_block μ v b hb c q (hne w)
      (fun ρ => Z ρ * ∏ u ∈ W, ov ρ (ca u) (da u)) (fun ρ s => (hZ'c ρ s).symm)
      (fun ρ s => (hZ'd ρ s).symm)
    have h2 := ih Z (fun u hu => hZc u (Finset.mem_insert_of_mem hu))
      (fun u hu => hZd u (Finset.mem_insert_of_mem hu))
    simp only [Finset.prod_insert hw, Finset.card_insert_of_notMem hw, pow_succ]
    simp only [hov] at h1 h2 ⊢
    calc _ = ∫ ρ, (Z ρ * ∏ u ∈ W, ((c * ∑ i, v (ρ (ca u)) i * v (ρ (da u)) i) - q)) *
          ((c * ∑ i, v (ρ (ca w)) i * v (ρ (da w)) i) - q) ∂(Measure.pi fun _ : R => μ) :=
          integral_congr_ae (Filter.Eventually.of_forall fun ρ => by ring)
      _ = _ := by rw [h1, h2, ← hTg]; ring


/-- Injectivity of `Sum.elim ca da` as separate disjointness statements. -/
theorem sum_elim_injective_facts {V R : Type*} {ca da : V → R}
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) :
    (∀ u w, u ≠ w → ca u ≠ ca w) ∧ (∀ u w, u ≠ w → da u ≠ da w) ∧ ∀ u w, ca u ≠ da w :=
  ⟨fun u w h hh => h (Sum.inl_injective (hinj (by simpa using hh))),
    fun u w h hh => h (Sum.inr_injective (hinj (by simpa using hh))),
    fun u w hh => Sum.inl_ne_inr (hinj (a₁ := Sum.inl u) (a₂ := Sum.inr w) (by simpa using hh))⟩

/-- Replacing a replica by the mean: `R_{x d} - q` against the mean is `T_x + T`. -/
theorem overlap_mean_eq {I : Type*} [Fintype I] (c q : ℝ) (u b : I → ℝ) :
    ((c * ∑ i, u i * b i) - q) =
      (c * ∑ i, (u i - b i) * b i) + ((c * ∑ i, b i * b i) - q) := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- **The T-expansion of an overlap (Eq. (1.246)).** -/
theorem overlap_T_expansion {I : Type*} [Fintype I] (c q : ℝ) (u w b : I → ℝ) :
    ((c * ∑ i, u i * w i) - q) =
      (c * ∑ i, (u i - b i) * (w i - b i)) + (c * ∑ i, (u i - b i) * b i) +
        (c * ∑ i, (w i - b i) * b i) + ((c * ∑ i, b i * b i) - q) := by
  simpa only [dotProduct, Pi.sub_apply] using dotProduct_centering c q u w b

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

theorem ov_update_of_ne {α R I : Type*} (v : α → I → ℝ) (c q : ℝ) [Fintype I] [DecidableEq R]
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (ρ : R → α) (s : α) {r a a' : R} (h : a ≠ r) (h' : a' ≠ r) :
    ov (Function.update ρ r s) a a' = ov ρ a a' := by
  rw [hov, hov, Function.update_of_ne h, Function.update_of_ne h']

theorem A_update_of_ne {α R I : Type*} (v : α → I → ℝ) (b : I → ℝ) (c : ℝ) [Fintype I]
    [DecidableEq R] (A : R → (R → α) → ℝ)
    (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (ρ : R → α) (s : α) {r a : R} (h : a ≠ r) :
    A a (Function.update ρ r s) = A a ρ := by
  rw [hA, hA, Function.update_of_ne h]

/-- **No block touches `x, y`:** the blocks contribute `Tg ^ card V`. -/
theorem integral_pi_blocks_untouched (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (hx : ∀ u, x ≠ ca u ∧ x ≠ da u) (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ ∂(Measure.pi fun _ : R => μ)) * Tg ^ Fintype.card V := by
  have h := integral_pi_prod_overlap_blocks μ v b hb c q ov hov Tg hTg ca da hinj
    Finset.univ Y (fun u _ ρ s => hY ρ s _ (hx u).1.symm (hy u).1.symm)
    (fun u _ ρ s => hY ρ s _ (hx u).2.symm (hy u).2.symm)
  simpa only [Finset.card_univ] using h

/-- **One replica of the pair touches a block.** Let `x` belong to the block `u0` with partner `x'`,
while `y` belongs to no block. Then the block `u0` is replaced by `T_x + T`. -/
theorem integral_pi_blocks_one_touched (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (u0 : V) (x' : R) (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ * (A x ρ + Tg) ∂(Measure.pi fun _ : R => μ)) * Tg ^ (Fintype.card V - 1) := by
  obtain ⟨hxx', hfac⟩ := block_facts hinj hx0
  have hy0 := hy u0
  have hyx' : x' ≠ y := by
    rcases hx0 with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2 ▸ hy0.2.symm
    · exact h1 ▸ hy0.1.symm
  have hov0 : ∀ ρ, ov ρ (ca u0) (da u0) = ov ρ x x' := fun ρ => by
    rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hov, hov]
      simp only [mul_comm (v (ρ x') _)]
  have hprod : ∀ ρ : R → α, Y ρ * ∏ u, ov ρ (ca u) (da u) =
      (Y ρ * ov ρ x x') * ∏ u ∈ Finset.univ.erase u0, ov ρ (ca u) (da u) := fun ρ => by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => ov ρ (ca u) (da u)) (Finset.mem_univ u0),
      hov0]
    ring
  simp_rw [hprod]
  have h := integral_pi_prod_overlap_blocks μ v b hb c q ov hov Tg hTg ca da hinj
    (Finset.univ.erase u0) (fun ρ => Y ρ * ov ρ x x')
    (fun u hu ρ s => by
      have hu0 := Finset.ne_of_mem_erase hu
      obtain ⟨h1, h2, h3, h4⟩ := hfac u hu0
      rw [hY ρ s _ h1 (hy u).1.symm, ov_update_of_ne v c q ov hov ρ s h1.symm h2.symm])
    (fun u hu ρ s => by
      have hu0 := Finset.ne_of_mem_erase hu
      obtain ⟨h1, h2, h3, h4⟩ := hfac u hu0
      rw [hY ρ s _ h3 (hy u).2.symm, ov_update_of_ne v c q ov hov ρ s h3.symm h4.symm])
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ]
  congr 1
  simp only [hov]
  rw [integral_pi_overlap_pendant μ v b hb c q hxx' Y (fun ρ s => hY ρ s _ hxx'.symm hyx')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  have := overlap_mean_eq c q (fun i => v (ρ x) i) b
  simp only [hA, hTg, this]

/-- **Both replicas lie in one block.** The block `{x, y}` stays as the overlap `R_{x y} - q`. -/
theorem integral_pi_blocks_same (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (u0 : V) (hx0 : (ca u0 = x ∧ da u0 = y) ∨ (ca u0 = y ∧ da u0 = x)) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ * ov ρ x y ∂(Measure.pi fun _ : R => μ)) * Tg ^ (Fintype.card V - 1) := by
  obtain ⟨hxx', hfac⟩ := block_facts hinj hx0
  have hov0 : ∀ ρ, ov ρ (ca u0) (da u0) = ov ρ x y := fun ρ => by
    rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hov, hov]
      simp only [mul_comm (v (ρ y) _)]
  have hprod : ∀ ρ : R → α, Y ρ * ∏ u, ov ρ (ca u) (da u) =
      (Y ρ * ov ρ x y) * ∏ u ∈ Finset.univ.erase u0, ov ρ (ca u) (da u) := fun ρ => by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => ov ρ (ca u) (da u)) (Finset.mem_univ u0),
      hov0]
    ring
  simp_rw [hprod]
  have h := integral_pi_prod_overlap_blocks μ v b hb c q ov hov Tg hTg ca da hinj
    (Finset.univ.erase u0) (fun ρ => Y ρ * ov ρ x y)
    (fun u hu ρ s => by
      obtain ⟨h1, h2, h3, h4⟩ := hfac u (Finset.ne_of_mem_erase hu)
      rw [hY ρ s _ h1 h2, ov_update_of_ne v c q ov hov ρ s h1.symm h2.symm])
    (fun u hu ρ s => by
      obtain ⟨h1, h2, h3, h4⟩ := hfac u (Finset.ne_of_mem_erase hu)
      rw [hY ρ s _ h3 h4, ov_update_of_ne v c q ov hov ρ s h3.symm h4.symm])
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ]

/-- **The two replicas lie in different blocks.** Both blocks are replaced by the pendant
expressions `T_x + T` and `T_y + T`. -/
theorem integral_pi_blocks_two_touched (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (Y : (R → α) → ℝ)
    (hY : ∀ ρ s r, r ≠ x → r ≠ y → Y (Function.update ρ r s) = Y ρ)
    (u0 u1 : V) (hu01 : u0 ≠ u1) (x' y' : R)
    (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy0 : (ca u1 = y ∧ da u1 = y') ∨ (ca u1 = y' ∧ da u1 = y)) :
    ∫ ρ, Y ρ * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      (∫ ρ, Y ρ * ((A x ρ + Tg) * (A y ρ + Tg)) ∂(Measure.pi fun _ : R => μ)) *
        Tg ^ (Fintype.card V - 2) := by
  obtain ⟨hxx', hfx⟩ := block_facts hinj hx0
  obtain ⟨hyy', hfy⟩ := block_facts hinj hy0
  obtain ⟨hcc, hdd, hcd⟩ := sum_elim_injective_facts hinj
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
  have hov0 : ∀ ρ, ov ρ (ca u0) (da u0) = ov ρ x x' := fun ρ => by
    rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hov, hov]
      simp only [mul_comm (v (ρ x') _)]
  have hov1 : ∀ ρ, ov ρ (ca u1) (da u1) = ov ρ y y' := fun ρ => by
    rcases hy0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hov, hov]
      simp only [mul_comm (v (ρ y') _)]
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
  have h := integral_pi_prod_overlap_blocks μ v b hb c q ov hov Tg hTg ca da hinj
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
  have hcard : ((Finset.univ.erase u0).erase u1).card = Fintype.card V - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hu01.symm, Finset.mem_univ u1⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ]
    omega
  rw [h, hcard]
  congr 1
  -- first integrate out `x'`, then `y'`
  have e1 := integral_pi_overlap_pendant μ v b hb c q hxx' (fun ρ => Y ρ * ov ρ y y')
    (fun ρ s => by
      rw [hY ρ s _ hxx'.symm hx'y, ov_update_of_ne v c q ov hov ρ s hx'y.symm hx'y'.symm])
  have e2 := integral_pi_overlap_pendant μ v b hb c q hyy' (fun ρ => Y ρ * (A x ρ + Tg))
    (fun ρ s => by
      rw [hY ρ s _ hxy'.symm hyy'.symm.symm.symm, A_update_of_ne v b c A hA ρ s hxy'])
  have hmx := fun ρ : R → α => overlap_mean_eq c q (fun i => v (ρ x) i) b
  have hmy := fun ρ : R → α => overlap_mean_eq c q (fun i => v (ρ y) i) b
  calc _ = ∫ ρ, (Y ρ * ov ρ y y') * ((c * ∑ i, v (ρ x) i * v (ρ x') i) - q)
          ∂(Measure.pi fun _ : R => μ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ρ => by rw [hov ρ x x']; ring)
    _ = ∫ ρ, (Y ρ * ov ρ y y') * ((c * ∑ i, v (ρ x) i * b i) - q)
          ∂(Measure.pi fun _ : R => μ) := e1
    _ = ∫ ρ, (Y ρ * (A x ρ + Tg)) * ((c * ∑ i, v (ρ y) i * v (ρ y') i) - q)
          ∂(Measure.pi fun _ : R => μ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ρ => by
          beta_reduce
          rw [hov ρ y y', hmx ρ, hA, hTg]; ring)
    _ = ∫ ρ, (Y ρ * (A x ρ + Tg)) * ((c * ∑ i, v (ρ y) i * b i) - q)
          ∂(Measure.pi fun _ : R => μ) := e2
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ρ => by
          beta_reduce
          rw [hmy ρ, hA y ρ, hTg]; ring)

omit [DecidableEq R] in
/-- **Orthogonality of the single-replica and pair variables of two distinct replicas.**
Let `A x`, `A y` be the centered single variables and `P x y` the doubly centered pair variable.
Every product in which some replica enters exactly once and centered has mean zero. -/
theorem integral_pi_two_replica_orthogonality (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c : ℝ)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {x y : R} (hxy : x ≠ y) :
    (∫ ρ, A x ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, P x y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ * P x y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A y ρ * P x y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ * A y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ ^ 2 * A y ρ ∂(Measure.pi fun _ : R => μ)) = 0 ∧
    (∫ ρ, A x ρ * A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) = 0 := by
  have hAx : ∀ ρ s r, r ≠ x → A x (Function.update ρ r s) = A x ρ := fun ρ s r h => by
    rw [hA, hA, Function.update_of_ne h.symm]
  have hcomm : ∀ (ρ : R → α) (z : R), A z ρ = c * ∑ i, b i * (v (ρ z) i - b i) := fun ρ z => by
    rw [hA]
    simp only [mul_comm (b _)]
  have hcomm' : ∀ (ρ : R → α) (z z' : R), P z z' ρ =
      c * ∑ i, (v (ρ z') i - b i) * (v (ρ z) i - b i) := fun ρ z z' => by
    rw [hP]
    simp only [mul_comm (v (ρ z) _ - b _)]
  have e1 := integral_pi_centered_replica μ v b hb c x (fun _ => 1) (fun _ _ => rfl)
    (fun _ i => b i) (fun _ _ => rfl)
  have e2 := integral_pi_centered_replica μ v b hb c y (fun _ => 1) (fun _ _ => rfl)
    (fun _ i => b i) (fun _ _ => rfl)
  have e3 := integral_pi_centered_replica μ v b hb c y (fun _ => 1) (fun _ _ => rfl)
    (fun ρ i => v (ρ x) i - b i) (fun ρ s => by
      funext i
      simp only [Function.update_of_ne hxy])
  have e4 := integral_pi_centered_replica μ v b hb c y (fun ρ => A x ρ)
    (fun ρ s => hAx ρ s y hxy.symm) (fun ρ i => v (ρ x) i - b i) (fun ρ s => by
      funext i
      simp only [Function.update_of_ne hxy])
  have e5 := integral_pi_centered_replica μ v b hb c x (fun ρ => A y ρ)
    (fun ρ s => by rw [hA, hA, Function.update_of_ne hxy.symm])
    (fun ρ i => v (ρ y) i - b i) (fun ρ s => by
      funext i
      simp only [Function.update_of_ne hxy.symm])
  have e6 := integral_pi_centered_replica μ v b hb c y (fun ρ => A x ρ)
    (fun ρ s => hAx ρ s y hxy.symm) (fun _ i => b i) (fun _ _ => rfl)
  have e7 := integral_pi_centered_replica μ v b hb c y (fun ρ => A x ρ ^ 2)
    (fun ρ s => by rw [hAx ρ s y hxy.symm]) (fun _ i => b i) (fun _ _ => rfl)
  have e8 := integral_pi_centered_replica μ v b hb c x (fun ρ => A y ρ ^ 2)
    (fun ρ s => by rw [hA, hA, Function.update_of_ne hxy.symm]) (fun _ i => b i) (fun _ _ => rfl)
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
theorem integral_pi_two_replica_overlap_moments (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
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
    integral_pi_two_replica_orthogonality μ v b hb c A hA P hP hxy
  have hexp : ∀ ρ, ov ρ x y = P x y ρ + A x ρ + A y ρ + Tg := fun ρ => by
    rw [hov, hTg, hP, hA, hA]
    exact overlap_T_expansion c q (fun i => v (ρ x) i) (fun i => v (ρ y) i) b
  have hint : ∀ f : (R → α) → ℝ, Integrable f (Measure.pi fun _ : R => μ) :=
    fun f => Integrable.of_finite
  have hc : ∀ k : ℝ, ∫ _ρ : R → α, k ∂(Measure.pi fun _ : R => μ) = k := fun k => by
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [hexp]
    simp only [integral_add (hint _) (hint _), hc, o1, o2, o3]
    ring
  · have h : ∀ ρ, ov ρ x y * (A x ρ + Tg) = A x ρ * P x y ρ + Tg * P x y ρ + A x ρ ^ 2 +
        2 * Tg * A x ρ + A x ρ * A y ρ + Tg * A y ρ + Tg ^ 2 := fun ρ => by
      rw [hexp]; ring
    simp_rw [h]
    simp only [integral_add (hint _) (hint _), integral_const_mul, hc, o1, o2, o3, o4, o6]
    ring
  · have h : ∀ ρ, ov ρ x y * ov ρ x y = P x y ρ ^ 2 + A x ρ ^ 2 + A y ρ ^ 2 + Tg ^ 2 +
        2 * (A x ρ * P x y ρ) + 2 * (A y ρ * P x y ρ) + 2 * Tg * P x y ρ +
        2 * (A x ρ * A y ρ) + 2 * Tg * A x ρ + 2 * Tg * A y ρ := fun ρ => by
      rw [hexp]; ring
    simp_rw [h]
    simp only [integral_add (hint _) (hint _), integral_const_mul, hc, o1, o2, o3, o4, o5, o6]
    ring
  · have h : ∀ ρ, ov ρ x y * ((A x ρ + Tg) * (A y ρ + Tg)) =
        P x y ρ * A x ρ * A y ρ + Tg * (A x ρ * P x y ρ) + Tg * (A y ρ * P x y ρ) +
        Tg ^ 2 * P x y ρ + A x ρ ^ 2 * A y ρ + Tg * A x ρ ^ 2 + Tg * (A x ρ * A y ρ) +
        Tg ^ 2 * A x ρ + A x ρ * A y ρ ^ 2 + Tg * (A x ρ * A y ρ) + Tg * A y ρ ^ 2 +
        Tg ^ 2 * A y ρ + Tg * (A x ρ * A y ρ) + Tg ^ 2 * A x ρ + Tg ^ 2 * A y ρ + Tg ^ 3 :=
      fun ρ => by rw [hexp]; ring
    simp_rw [h]
    simp only [integral_add (hint _) (hint _), integral_const_mul, hc, o1, o2, o3, o4, o5, o6,
      o7, o8]
    ring

omit [DecidableEq R] in
/-- **Case 0: neither `x` nor `y` lies in a block.** -/
theorem integral_pi_overlap_blocks_untouched (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (hx : ∀ u, x ≠ ca u ∧ x ≠ da u) (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      Tg ^ (Fintype.card V + 1) := by
  rw [integral_pi_blocks_untouched μ v b hb c q ov hov Tg hTg ca da hinj (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) hx hy,
    (integral_pi_two_replica_overlap_moments μ v b hb c q ov hov Tg hTg A hA P hP hxy).1]
  ring

omit [DecidableEq R] in
/-- **Case 1: `x` lies in a block, `y` does not.** -/
theorem integral_pi_overlap_blocks_one_touched (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 : V) (x' : R) (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      ((∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2) * Tg ^ (Fintype.card V - 1) := by
  rw [integral_pi_blocks_one_touched μ v b hb c q ov hov Tg hTg A hA ca da hinj (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) u0 x' hx0 hy,
    (integral_pi_two_replica_overlap_moments μ v b hb c q ov hov Tg hTg A hA P hP hxy).2.1]

omit [DecidableEq R] in
/-- **Case 2: `x` and `y` form one block.** -/
theorem integral_pi_overlap_blocks_same (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → α) → ℝ)
    (hP : ∀ x y ρ, P x y ρ = c * ∑ i, (v (ρ x) i - b i) * (v (ρ y) i - b i))
    {V : Type*} [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R))
    {x y : R} (hxy : x ≠ y)
    (u0 : V) (hx0 : (ca u0 = x ∧ da u0 = y) ∨ (ca u0 = y ∧ da u0 = x)) :
    ∫ ρ, ov ρ x y * ∏ u, ov ρ (ca u) (da u) ∂(Measure.pi fun _ : R => μ) =
      ((∫ ρ, P x y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A x ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) +
        (∫ ρ, A y ρ ^ 2 ∂(Measure.pi fun _ : R => μ)) + Tg ^ 2) *
        Tg ^ (Fintype.card V - 1) := by
  rw [integral_pi_blocks_same μ v b hb c q ov hov Tg hTg ca da hinj (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) u0 hx0,
    (integral_pi_two_replica_overlap_moments μ v b hb c q ov hov Tg hTg A hA P hP hxy).2.2.1]

omit [DecidableEq R] in
/-- **Case 3: `x` and `y` lie in different blocks.** -/
theorem integral_pi_overlap_blocks_two_touched (μ : Measure α) [IsProbabilityMeasure μ]
    (v : α → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ t, v t i ∂μ = b i) (c q : ℝ)
    (ov : (R → α) → R → R → ℝ)
    (hov : ∀ ρ x y, ov ρ x y = (c * ∑ i, v (ρ x) i * v (ρ y) i) - q)
    (Tg : ℝ) (hTg : Tg = (c * ∑ i, b i * b i) - q)
    (A : R → (R → α) → ℝ) (hA : ∀ x ρ, A x ρ = c * ∑ i, (v (ρ x) i - b i) * b i)
    (P : R → R → (R → α) → ℝ)
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
        Tg ^ (Fintype.card V - 2) := by
  rw [integral_pi_blocks_two_touched μ v b hb c q ov hov Tg hTg A hA ca da hinj (fun ρ => ov ρ x y)
    (fun ρ s r hx hy => ov_update_of_ne v c q ov hov ρ s hx.symm hy.symm) u0 u1 hu01 x' y' hx0 hy0,
    (integral_pi_two_replica_overlap_moments μ v b hb c q ov hov Tg hTg A hA P hP hxy).2.2.2]

end MeasureTheory
