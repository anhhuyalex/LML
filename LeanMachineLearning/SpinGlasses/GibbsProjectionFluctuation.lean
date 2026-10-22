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
`u_l i = (ξ_i(σ_l) - ⟨ξ_i⟩) / √N` (`gibbsData`) has Gram entries
`T_{l k} = N⁻¹ ∑_i ξ̇_i(σ_l) ξ̇_i(σ_k) - v² δ_{l k}` (`projGram`).

## Main declarations

* `SpinGlasses.exists_of_pairCount_eq_one`: a replica occurring once in a list of pairs.
* `SpinGlasses.integral_pairProd_gibbsData_eq_zero`: **parity vanishing**: the Gibbs average of
  a product of Gram entries in which some replica occurs exactly once is `0`
  (the step "because `⟨σ̇_i⟩ = 0`" of the book's proof).

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


section GibbsData

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ)

/-- The Gibbs average `⟨ξ_i⟩` of the observable `ξ i` for the energy `f`. -/
noncomputable def gibbsMean (f : α → ℝ) (i : Fin N) : ℝ :=
  ∫ a, ξ i a ∂(Measure.count.tilted f)

/-- The centered and scaled replica data `u l i = (ξ_i(σ_l) - ⟨ξ_i⟩) / √N` of a configuration
of `m` replicas. -/
noncomputable def gibbsData (f : α → ℝ) {m : ℕ} (σ : Fin m → α) : Fin m → Fin N → ℝ :=
  fun l i => (Real.sqrt N)⁻¹ * (ξ i (σ l) - gibbsMean ξ f i)

theorem gibbsMean_eq_sum (f : α → ℝ) (i : Fin N) :
    gibbsMean ξ f i = ∑ a, (Real.exp (f a) / ∑ b, Real.exp (f b)) * ξ i a := by
  rw [gibbsMean, integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [real_count_tilted_singleton, smul_eq_mul]



theorem sum_weight_mul_centered (f : α → ℝ) (j : Fin N) :
    ∑ a, (Real.exp (f a) / ∑ b, Real.exp (f b)) *
      ((Real.sqrt N)⁻¹ * (ξ j a - gibbsMean ξ f j)) = 0 := by
  have hZ : 0 < ∑ b, Real.exp (f b) := Finset.sum_pos (fun _ _ => Real.exp_pos _)
    Finset.univ_nonempty
  have h1 : ∑ a, Real.exp (f a) / ∑ b, Real.exp (f b) = 1 := by
    rw [← Finset.sum_div]; exact div_self hZ.ne'
  have hM := gibbsMean_eq_sum ξ f j
  set M := gibbsMean ξ f j with hMdef
  set c : ℝ := (Real.sqrt N)⁻¹ with hc
  have hterm : ∀ a, (Real.exp (f a) / ∑ b, Real.exp (f b)) * (c * (ξ j a - M)) =
      c * ((Real.exp (f a) / ∑ b, Real.exp (f b)) * ξ j a) -
        c * M * (Real.exp (f a) / ∑ b, Real.exp (f b)) := fun a => by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hM, h1]
  ring

theorem gibbsData_update_of_ne (f : α → ℝ) {m : ℕ} (σ : Fin m → α) (ℓ : Fin m) (a : α)
    {l : Fin m} (hl : l ≠ ℓ) :
    gibbsData ξ f (Function.update σ ℓ a) l = gibbsData ξ f σ l := by
  funext i
  simp [gibbsData, Function.update_of_ne hl]



/-- **Parity vanishing (the replica-centering step of Theorem 1.7.11).**  If a replica occurs
exactly once in a list of pairs, the Gibbs average of the product of the corresponding Gram
entries vanishes, because every entry is linear in the centered replica data and `⟨ξ̇⟩ = 0`. -/
theorem integral_pairProd_gibbsData_eq_zero (f : α → ℝ) (v : ℝ) {m r : ℕ}
    (p : Fin r → Fin m × Fin m) (ℓ : Fin m) (hℓ : pairCount p ℓ = 1) :
    ∫ σ : Fin m → α, pairProd (projGram (gibbsData ξ f σ) v) p
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) = 0 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos ℓ).ne'
  obtain ⟨i₀, ℓ', hne, hp, hrest⟩ := exists_of_pairCount_eq_one p ℓ hℓ
  rw [integral_pi_count_tilted]
  set w : α → ℝ := fun a => Real.exp (f a) / ∑ b, Real.exp (f b) with hw
  let z : Fin N → α → ℝ := fun j a => (Real.sqrt N)⁻¹ * (ξ j a - gibbsMean ξ f j)
  let H : (Fin (n + 1) → α) → ℝ := fun σ =>
    ∏ i ∈ Finset.univ.erase i₀, projGram (gibbsData ξ f σ) v (p i).1 (p i).2
  let c : Fin N → (Fin (n + 1) → α) → ℝ := fun j σ => gibbsData ξ f σ ℓ' j
  have hmain : ∀ σ : Fin (n + 1) → α, pairProd (projGram (gibbsData ξ f σ) v) p =
      H σ * ∑ j, z j (σ ℓ) * c j σ := fun σ => by
    unfold pairProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), mul_comm]
    congr 1
    rcases hp with hp | hp
    · rw [hp]
      simp only [projGram, dotProduct, if_neg hne.symm, sub_zero, z, c, gibbsData]
    · rw [hp]
      simp only [projGram, dotProduct, if_neg hne, sub_zero, z, c, gibbsData]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hmain]
  refine sum_prod_weight_mul_linear_eq_zero w ℓ z (fun j => sum_weight_mul_centered ξ f j) H c
    (fun σ a => ?_) (fun j σ a => ?_)
  · simp only [H]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := hrest i (Finset.ne_of_mem_erase hi)
    simp only [projGram, dotProduct, gibbsData_update_of_ne ξ f σ ℓ a hi'.1,
      gibbsData_update_of_ne ξ f σ ℓ a hi'.2]
  · simp only [c, gibbsData_update_of_ne ξ f σ ℓ a hne]

end GibbsData


end SpinGlasses
