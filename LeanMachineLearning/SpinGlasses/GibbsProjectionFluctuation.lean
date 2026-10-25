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
any model.  For a Gibbs measure `count.tilted f` on a finite configuration space, a vector field
`u : α → ℝ^N` (in the application `u a i = (ξ_i(a) - ⟨ξ_i⟩) / √N` for observables `ξ_i`) with Gibbs
mean zero gives replica data `u(σ_l)` whose Gram entries are
`T_{l k} = u(σ_l) ⬝ u(σ_k) - v² δ_{l k}`.

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
  {N : ℕ} (u : α → Fin N → ℝ)

set_option linter.unusedFintypeInType false in
/-- The centered scaled observable `u a j = N^{-1/2} (ξ_j(a) - ⟨ξ_j⟩)` has Gibbs mean zero. -/
theorem integral_centered_eq_zero (ξ : Fin N → α → ℝ) (f : α → ℝ)
    (hu : ∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f)))
    (j : Fin N) : ∫ a, u a j ∂(Measure.count.tilted f) = 0 := by
  simp_rw [hu]
  rw [integral_const_mul, integral_sub Integrable.of_finite (integrable_const _)]
  simp

omit [Nonempty α] in
theorem sum_weight_mul_eq_zero (f : α → ℝ) {j : Fin N}
    (hu : ∫ a, u a j ∂(Measure.count.tilted f) = 0) :
    ∑ a, (Real.exp (f a) / ∑ b, Real.exp (f b)) * u a j = 0 := by
  rw [integral_fintype Integrable.of_finite] at hu
  rw [← hu]
  exact Finset.sum_congr rfl fun a _ => by rw [real_count_tilted_singleton, smul_eq_mul]

omit [Nonempty α] in
set_option linter.unusedFintypeInType false in
/-- **Parity vanishing (the replica-centering step of Theorem 1.7.11).**  If a replica occurs
exactly once in a list of pairs, the Gibbs average of the product of the corresponding Gram
entries vanishes, because every entry is linear in the replica data `u` and `⟨u⟩ = 0`. -/
theorem integral_pairProd_centered_eq_zero (f : α → ℝ)
    (hu : ∀ j, ∫ a, u a j ∂(Measure.count.tilted f) = 0) (v : ℝ) {m r : ℕ}
    (p : Fin r → Fin m × Fin m) (ℓ : Fin m) (hℓ : pairCount p ℓ = 1) :
    ∫ σ : Fin m → α,
      ∏ i, (u (σ (p i).1) ⬝ᵥ u (σ (p i).2) - if (p i).1 = (p i).2 then v ^ 2 else 0)
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos ℓ).ne'
  obtain ⟨i₀, ℓ', hne, hp, hrest⟩ := exists_of_pairCount_eq_one p ℓ hℓ
  rw [integral_pi_count_tilted]
  let H : (Fin (n + 1) → α) → ℝ := fun σ =>
    ∏ i ∈ Finset.univ.erase i₀,
      (u (σ (p i).1) ⬝ᵥ u (σ (p i).2) - if (p i).1 = (p i).2 then v ^ 2 else 0)
  have hmain : ∀ σ : Fin (n + 1) → α,
      (∏ i, (u (σ (p i).1) ⬝ᵥ u (σ (p i).2) - if (p i).1 = (p i).2 then v ^ 2 else 0)) =
      H σ * ∑ j, u (σ ℓ) j * u (σ ℓ') j := fun σ => by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), mul_comm]
    congr 1
    rcases hp with hp | hp
    · rw [hp]
      simp only [dotProduct, ite_eq_right (Ne.symm hne), sub_zero]
    · rw [hp]
      simp only [dotProduct, ite_eq_right hne, sub_zero]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hmain]
  refine sum_prod_weight_mul_linear_eq_zero (fun a => Real.exp (f a) / ∑ b, Real.exp (f b)) ℓ
    (fun j a => u a j) (fun j => sum_weight_mul_eq_zero u f (hu j)) H (fun j σ => u (σ ℓ') j)
    (fun σ a => ?_) (fun j σ a => ?_)
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := hrest i (Finset.ne_of_mem_erase hi)
    simp only [dotProduct, Function.update_of_ne hi'.1, Function.update_of_ne hi'.2]
  · simp only [Function.update_of_ne hne]

omit [Nonempty α] in
set_option linter.unusedFintypeInType false in
/-- At s = 0, the Gibbs average of the path functional vanishes for any `r < m`, by parity
vanishing and Gaussian vanishing. -/
theorem integral_projSum_centered_zero_eq_zero {m r : ℕ} (V : ℝ → ℝ) (hV : ExpTame V)
    (hm : 0 < m) (hr : r < m) (f : α → ℝ)
    (hu : ∀ j, ∫ a, u a j ∂(Measure.count.tilted f) = 0) (v : ℝ)
    (hV0 : ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0) :
    ∫ σ : Fin m → α, projSum V (fun l => u (σ l)) v r 0
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) = 0 := by
  have hterm : ∀ σ : Fin m → α, projSum V (fun l => u (σ l)) v r 0 =
      ∑ p : Fin r → Fin m × Fin m,
        (∏ j, (u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0)) *
        ∫ ξ' : Fin m → ℝ, ∏ ℓ, deriv^[(pairCount p) ℓ] V ((v * ξ' ℓ))
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun σ => by
    unfold projSum
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_derivProd_projPath_zero]
  simp_rw [hterm]
  rw [integral_finsetSum _ fun p _ => Integrable.of_finite]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [integral_mul_const]
  obtain ⟨ℓ, h0 | h1⟩ := exists_pairCount_le_one_of_lt p hr
  · have hz := hV.integral_derivProd_projPath_zero_eq_zero hm
      (fun (_ : Fin m) (_ : Fin N) => (0 : ℝ)) v (pairCount p) ℓ h0 hV0
    rw [integral_derivProd_projPath_zero] at hz
    rw [hz, mul_zero]
  · rw [integral_pairProd_centered_eq_zero u f hu v p ℓ h1, zero_mul]

end CenteredObservable


end SpinGlasses
