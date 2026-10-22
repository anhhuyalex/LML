/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianProjectionPath
public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal

/-!
# The general Gibbs fluctuation principle (Talagrand, Theorem 1.7.11): Gibbs-side algebra

This file contains the finite-sum and replica bookkeeping behind Theorem 1.7.11, independent of
any model.  For a Gibbs measure `count.tilted f` on a finite configuration space carrying
`N` bounded observables `ξ_i`, the centered scaled replica data
`u_l i = (ξ_i(σ_l) - ⟨ξ_i⟩) / √N` has Gram entries
`T_{l k} = N⁻¹ ∑_i ξ̇_i(σ_l) ξ̇_i(σ_k) - v² δ_{l k}` (`projGram`).

## Main declarations

* `SpinGlasses.exists_of_pairCount_eq_one`: a replica occurring once in a list of pairs.
* `SpinGlasses.integral_pairProd_centered_eq_zero`: **parity vanishing**: the Gibbs average of
  a product of Gram entries in which some replica occurs exactly once is `0`.
* `SpinGlasses.integral_projSum_centered_zero_eq_zero`: vanishing of the Gibbs average of the
  projection path functional at `s = 0` for `r < m`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

theorem insertNth_eq_update {α : Type*} {n : ℕ} (ℓ : Fin (n + 1)) (a b : α) (σ : Fin n → α) :
    Fin.insertNth (α := fun _ => α) ℓ a σ =
      Function.update (Fin.insertNth (α := fun _ => α) ℓ b σ) ℓ a := by
  funext i
  refine Fin.succAboveCases ℓ ?_ ?_ i
  · simp
  · intro j
    simp

theorem sum_prod_weight_mul_linear_eq_zero {α : Type*} [Fintype α] {n N : ℕ} (w : α → ℝ)
    (ℓ : Fin (n + 1)) (z : Fin N → α → ℝ) (hz : ∀ j, ∑ a, w a * z j a = 0)
    (H : (Fin (n + 1) → α) → ℝ) (c : Fin N → (Fin (n + 1) → α) → ℝ)
    (hH : ∀ σ a, H (Function.update σ ℓ a) = H σ)
    (hc : ∀ j σ a, c j (Function.update σ ℓ a) = c j σ) :
    ∑ σ : Fin (n + 1) → α, (∏ r, w (σ r)) * (H σ * ∑ j, z j (σ ℓ) * c j σ) = 0 := by
  classical
  rw [← (Fin.insertNthEquiv (fun _ => α) ℓ).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_eq_zero fun σ' _ => ?_
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · simp
  have hins : ∀ x, (Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ') =
      Function.update ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) ℓ x := fun x =>
    insertNth_eq_update ℓ x x₀ σ'
  have hH' : ∀ x, H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ')) =
      H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) := fun x => by rw [hins x, hH]
  have hc' : ∀ j x, c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ')) =
      c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) := fun j x => by rw [hins x, hc]
  have hprod : ∀ x, ∏ r, w ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ') r) =
      w x * ∏ j, w (σ' j) := fun x => by
    rw [Fin.prod_univ_succAbove _ ℓ]
    simp
  have hz' : ∀ x, ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ')) ℓ = x := fun x => by simp
  simp only [hH', hc', hprod, hz']
  have : ∀ x, w x * (∏ j, w (σ' j)) * (H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) *
      ∑ j, z j x * c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ'))) =
      (∏ j, w (σ' j)) * H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) *
        ∑ j, (w x * z j x) * c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) := fun x => by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul, hz, zero_mul, Finset.sum_const_zero, mul_zero]


section Parity

variable {m r : ℕ}

/-- If a replica occurs exactly once in a list of pairs, it sits in one pair with a different
replica and in no other pair. -/
theorem exists_of_pairCount_eq_one (p : Fin r → Fin m × Fin m) (ℓ : Fin m)
    (h : pairCount p ℓ = 1) :
    ∃ (i₀ : Fin r) (ℓ' : Fin m), ℓ' ≠ ℓ ∧ (p i₀ = (ℓ, ℓ') ∨ p i₀ = (ℓ', ℓ)) ∧
      ∀ i, i ≠ i₀ → (p i).1 ≠ ℓ ∧ (p i).2 ≠ ℓ := by
  classical
  set t : Fin r → ℕ := fun i => (if (p i).1 = ℓ then 1 else 0) + (if (p i).2 = ℓ then 1 else 0)
    with ht
  have hsum : ∑ i, t i = 1 := h
  obtain ⟨i₀, -, hi₀⟩ : ∃ i₀ ∈ (Finset.univ : Finset (Fin r)), t i₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [Finset.sum_eq_zero fun i hi => hcon i hi] at hsum
  have hle : t i₀ ≤ 1 := hsum ▸ Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i₀)
  have hone : t i₀ = 1 := by omega
  have hrest : ∀ i, i ≠ i₀ → t i = 0 := by
    intro i hi
    have := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r))) t (Finset.mem_univ i₀)
    have h0 : ∑ j ∈ Finset.univ.erase i₀, t j = 0 := by omega
    exact (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
  refine ⟨i₀, ?_⟩
  by_cases h1 : (p i₀).1 = ℓ
  · have h2 : (p i₀).2 ≠ ℓ := by
      intro h2; simp [ht, h1, h2] at hone
    refine ⟨(p i₀).2, h2, Or.inl (Prod.ext h1 rfl), fun i hi => ?_⟩
    have := hrest i hi
    simp only [ht] at this
    constructor <;> intro hh <;> simp [hh] at this
  · have h2 : (p i₀).2 = ℓ := by
      by_contra h2; simp [ht, h1, h2] at hone
    refine ⟨(p i₀).1, h1, Or.inr (Prod.ext rfl h2), fun i hi => ?_⟩
    have := hrest i hi
    simp only [ht] at this
    constructor <;> intro hh <;> simp [hh] at this

end Parity


section CenteredObservable

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ)

theorem sum_weight_mul_centered (f : α → ℝ) (j : Fin N) :
    ∑ a, (Real.exp (f a) / ∑ b, Real.exp (f b)) *
      ((Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f))) = 0 := by
  have hZ : 0 < ∑ b, Real.exp (f b) := Finset.sum_pos (fun _ _ => Real.exp_pos _)
    Finset.univ_nonempty
  have h1 : ∑ a, Real.exp (f a) / ∑ b, Real.exp (f b) = 1 := by
    rw [← Finset.sum_div]; exact div_self hZ.ne'
  have hM : ∫ a, ξ j a ∂(Measure.count.tilted f) =
      ∑ a, (Real.exp (f a) / ∑ b, Real.exp (f b)) * ξ j a := by
    rw [integral_fintype Integrable.of_finite]
    refine Finset.sum_congr rfl fun a _ => by rw [real_count_tilted_singleton, smul_eq_mul]
  set M := ∫ a, ξ j a ∂(Measure.count.tilted f)
  set c : ℝ := (Real.sqrt N)⁻¹
  have hterm : ∀ a, (Real.exp (f a) / ∑ b, Real.exp (f b)) * (c * (ξ j a - M)) =
      c * ((Real.exp (f a) / ∑ b, Real.exp (f b)) * ξ j a) -
        c * M * (Real.exp (f a) / ∑ b, Real.exp (f b)) := fun a => by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hM, h1]
  ring

/-- **Parity vanishing (the replica-centering step of Theorem 1.7.11).**  If a replica occurs
exactly once in a list of pairs, the Gibbs average of the product of the corresponding Gram
entries vanishes, because every entry is linear in the centered replica data and `⟨ξ̇⟩ = 0`. -/
theorem integral_pairProd_centered_eq_zero (f : α → ℝ) (v : ℝ) {m r : ℕ}
    (p : Fin r → Fin m × Fin m) (ℓ : Fin m) (hℓ : pairCount p ℓ = 1) :
    ∫ σ : Fin m → α,
      pairProd (projGram (fun l i => (Real.sqrt N)⁻¹ *
        (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v) p
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos ℓ).ne'
  obtain ⟨i₀, ℓ', hne, hp, hrest⟩ := exists_of_pairCount_eq_one p ℓ hℓ
  rw [integral_pi_count_tilted]
  set w : α → ℝ := fun a => Real.exp (f a) / ∑ b, Real.exp (f b)
  let z : Fin N → α → ℝ := fun j a => (Real.sqrt N)⁻¹ *
    (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f))
  let H : (Fin (n + 1) → α) → ℝ := fun σ =>
    ∏ i ∈ Finset.univ.erase i₀,
      projGram (fun l i => (Real.sqrt N)⁻¹ * (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f)))
        v (p i).1 (p i).2
  let c : Fin N → (Fin (n + 1) → α) → ℝ := fun j σ =>
    (Real.sqrt N)⁻¹ * (ξ j (σ ℓ') - ∫ a, ξ j a ∂(Measure.count.tilted f))
  have hmain : ∀ σ : Fin (n + 1) → α,
      pairProd (projGram (fun l i => (Real.sqrt N)⁻¹ *
        (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v) p =
      H σ * ∑ j, z j (σ ℓ) * c j σ := fun σ => by
    unfold pairProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), mul_comm]
    congr 1
    rcases hp with hp | hp
    · rw [hp]
      simp only [projGram, dotProduct, ite_eq_right (Ne.symm hne), sub_zero, z, c]
    · rw [hp]
      simp only [projGram, dotProduct, ite_eq_right hne, sub_zero, z, c]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hmain]
  refine sum_prod_weight_mul_linear_eq_zero w ℓ z (fun j => sum_weight_mul_centered ξ f j) H c
    (fun σ a => ?_) (fun j σ a => ?_)
  · simp only [H]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := hrest i (Finset.ne_of_mem_erase hi)
    simp only [projGram, dotProduct, Function.update_of_ne hi'.1, Function.update_of_ne hi'.2]
  · simp only [c, Function.update_of_ne hne]

/-- At s = 0, the Gibbs average of the path functional vanishes for any `r < m`, by parity
vanishing and Gaussian vanishing. -/
theorem integral_projSum_centered_zero_eq_zero {m r : ℕ} (V : ℝ → ℝ) (hV : ExpTame V)
    (hm : 0 < m) (hr : r < m) (f : α → ℝ) (v : ℝ)
    (hV0 : ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0) :
    ∫ σ : Fin m → α,
      projSum V (fun l i => (Real.sqrt N)⁻¹ *
        (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v r 0
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) = 0 := by
  rw [integral_pi_count_tilted]
  have hterm : ∀ σ : Fin m → α,
      projSum V (fun l i => (Real.sqrt N)⁻¹ *
        (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v r 0 =
      ∑ p : Fin r → Fin m × Fin m,
        pairProd (projGram (fun l i => (Real.sqrt N)⁻¹ *
          (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v) p *
        ∫ ξ' : Fin m → ℝ, derivProd V (pairCount p) (fun l => v * ξ' l)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun σ => by
    unfold projSum
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_derivProd_projPath_zero]
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨ℓ, h0 | h1⟩ := exists_pairCount_le_one_of_lt p hr
  · have hI : (∫ ξ' : Fin m → ℝ, derivProd V (pairCount p) (fun l => v * ξ' l)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) = 0 := by
      have hz := hV.integral_derivProd_projPath_zero_eq_zero hm
        (fun (_ : Fin m) (_ : Fin N) => (0 : ℝ)) v (pairCount p) ℓ h0 hV0
      rwa [integral_derivProd_projPath_zero] at hz
    simp only [hI, mul_zero, Finset.sum_const_zero]
  · have hG : (∑ x : Fin m → α,
        (∏ r_1 : Fin m, Real.exp (f (x r_1)) / ∑ b : α, Real.exp (f b)) *
          pairProd (projGram (fun l i => (Real.sqrt N)⁻¹ *
            (ξ i (x l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v) p) = 0 := by
      have hz := integral_pairProd_centered_eq_zero ξ f v p ℓ h1
      rwa [integral_pi_count_tilted] at hz
    have heq : (∑ x : Fin m → α,
        (∏ r_1 : Fin m, Real.exp (f (x r_1)) / ∑ b : α, Real.exp (f b)) *
          (pairProd (projGram (fun l i => (Real.sqrt N)⁻¹ *
            (ξ i (x l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v) p *
            ∫ ξ' : Fin m → ℝ, derivProd V (pairCount p) (fun l => v * ξ' l)
              ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1))) =
        (∑ x : Fin m → α,
          (∏ r_1 : Fin m, Real.exp (f (x r_1)) / ∑ b : α, Real.exp (f b)) *
            pairProd (projGram (fun l i => (Real.sqrt N)⁻¹ *
              (ξ i (x l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) v) p) *
          ∫ ξ' : Fin m → ℝ, derivProd V (pairCount p) (fun l => v * ξ' l)
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [heq, hG, zero_mul]

end CenteredObservable


end SpinGlasses
