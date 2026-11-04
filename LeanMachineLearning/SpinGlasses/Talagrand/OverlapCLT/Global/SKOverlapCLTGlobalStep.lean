/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTComparison
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalClassify

/-!
# The last-site expansion for the global factors (Talagrand, Eq. (1.325))

The `k` blocks `{e (inl u), e (inr u)}` of `2k` replicas carry the global factors
`R_{u} - q = N⁻¹ ∑ σ^{e(inl u)} σ^{e(inr u)} - q`. Splitting off the leading block `p` and applying
the last-site expansion of `SKOverlapCLTStep.lean` with the one-site observable
`ξ = ε^{x} ε^{y} - q` expresses `ν(∏_u (R_u - q))` through the cavity quantity
`ν(ξ ∏_{u ≠ p} U_u⁻)` and the sum of the corrections `ν(ξ e_u ∏_{w ≠ u} U_w⁻)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The last-site expansion of the product of global blocks.** -/
theorem sk_global_step_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (e : V ⊕ V ≃ Fin n) (p : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let νF : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |νF (fun σ => ∏ u : V, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e (.inl u)) v : ℝ) * (σ (e (.inr u)) v : ℝ) - q)) -
      (νF (fun σ => (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
          ∏ u : {u // u ≠ p}, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
            (σ (e (.inl u.1)) v.castSucc : ℝ) * (σ (e (.inr u.1)) v.castSucc : ℝ) - q)) +
        (N + 1 : ℝ)⁻¹ * ∑ u : {u // u ≠ p}, νF (fun σ =>
          (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
            (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
              ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
                (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := sk_overlap_step_expansion β₀ hβ₀ (κ := {u : V // u ≠ p})
    (ι := fun _ => Unit) (fun _ _ => 1) 2
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro Esk νF
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  let a : {u : V // u ≠ p} → Unit → Fin n := fun u _ => e (.inl u.1)
  let b : {u : V // u ≠ p} → Unit → Fin n := fun u _ => e (.inr u.1)
  have hab : ∀ j i, a j i ≠ b j i := fun j i => e.injective.ne (by simp)
  let ξ : (Fin n → ℤˣ) → ℝ := fun ε => (ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ) - q
  have hξ : ∀ ε, |ξ ε| ≤ 2 := fun ε => by
    dsimp only [ξ]
    have h1 : |(ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (abs_units_cast_le_one _) (abs_units_cast_le_one _) (abs_nonneg _)
        zero_le_one).trans (by norm_num)
    have h2 : |q| ≤ 1 := by rw [abs_of_nonneg hq.1]; exact hq.2
    linarith [abs_sub (( ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ)) q]
  have hs := hC β h q hfix hb N n a b hab νF (fun _ => rfl)
    (fun j σ => (N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
      (σ (e (.inl j.1)) v : ℝ) * (σ (e (.inr j.1)) v : ℝ) - q)
    (fun j σ => (N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
      (σ (e (.inl j.1)) v.castSucc : ℝ) * (σ (e (.inr j.1)) v.castSucc : ℝ) - q)
    (fun j σ => (σ (e (.inl j.1)) (Fin.last N) : ℝ) * (σ (e (.inr j.1)) (Fin.last N) : ℝ))
    (fun j σ => by simp [a, b, dotProduct])
    (fun j σ => by simp [a, b, dotProduct])
    (fun j σ => by simp [a, b]) ξ hξ
  beta_reduce at hs
  have hpt : ∀ σ : Fin n → Fin (N + 1) → ℤˣ, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        ξ (fun r => σ r v)) * ∏ j : {u : V // u ≠ p}, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e (.inl j.1)) v : ℝ) * (σ (e (.inr j.1)) v : ℝ) - q) =
      ∏ u : V, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e (.inl u)) v : ℝ) * (σ (e (.inr u)) v : ℝ) - q) := fun σ => by
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun u : V => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e (.inl u)) v : ℝ) * (σ (e (.inr u)) v : ℝ) - q)) p]
    congr 1
    simp only [ξ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub]
    push_cast
    field_simp
  have hcard : Fintype.card {u : V // u ≠ p} + 2 = Fintype.card V + 1 := by
    have h0 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨p⟩
    have : Fintype.card {u : V // u ≠ p} = Fintype.card V - 1 := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ]
    omega
  rw [hcard] at hs
  simp only [hpt] at hs
  exact hs

/-- **The leading cavity term of the global factors** (Lemma 1.10.2 for the block products). -/
theorem sk_global_feedback_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (e : V ⊕ V ≃ Fin n) (p : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q qhat : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 4 ∂gaussianReal 0 1 = qhat) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let ν₂ : ((Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |ν (fun σ => (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
          ∏ u : {u // u ≠ p}, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
            (σ (e (.inl u.1)) v.castSucc : ℝ) * (σ (e (.inr u.1)) v.castSucc : ℝ) - q)) -
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
          ν₂ (fun σ => (∏ u : {u // u ≠ p}, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
                (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (skCavityReplicaPairMap j).1 v.castSucc : ℝ) *
                (σ (skCavityReplicaPairMap j).2 v.castSucc : ℝ) - q)))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := by
  classical
  let κ := {u : V // u ≠ p}
  let f : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hxy : e (.inl p) ≠ e (.inr p) := e.injective.ne (by simp)
  obtain ⟨C, hC0, hC⟩ := sk_cavity_pair_lincomb_expansion_uniform β₀ hβ₀ n (Fintype.card κ) hxy
    (ι := fun _ => Unit) (fun _ _ => (1 : ℝ))
  refine ⟨C, hC0, fun β h q qhat hfix hqhat hb N => ?_⟩
  intro E ν ν₂
  have ht := hC β h q qhat hfix hqhat hb N (fun j _ => e (.inl (f.symm j).1))
    (fun j _ => e (.inr (f.symm j).1)) (fun j _ => e.injective.ne (by simp))
  have hcard : Fintype.card κ + 2 = Fintype.card V + 1 := by
    have h0 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨p⟩
    have : Fintype.card κ = Fintype.card V - 1 := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ]
    omega
  have hF1 : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      (∏ j : Fin (Fintype.card κ), ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (e (.inl (f.symm j).1)) v.castSucc : ℝ) * (σ (e (.inr (f.symm j).1)) v.castSucc : ℝ)
          - q)) = ∏ u : κ, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (e (.inl u.1)) v.castSucc : ℝ) * (σ (e (.inr u.1)) v.castSucc : ℝ) - q) :=
    fun σ => Equiv.prod_comp f.symm (fun u : κ => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (e (.inl u.1)) v.castSucc : ℝ) * (σ (e (.inr u.1)) v.castSucc : ℝ) - q))
  have hF2 : ∀ σ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      (∏ j : Fin (Fintype.card κ), ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (some (some (e (.inl (f.symm j).1)))) v.castSucc : ℝ) *
          (σ (some (some (e (.inr (f.symm j).1)))) v.castSucc : ℝ) - q)) =
      ∏ u : κ, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
          (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q) :=
    fun σ => Equiv.prod_comp f.symm (fun u : κ => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
          (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q))
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, dotProduct, hF1, hF2] at ht
  rw [hcard] at ht
  have hcomm : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      (∏ u : κ, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (e (.inl u.1)) v.castSucc : ℝ) * (σ (e (.inr u.1)) v.castSucc : ℝ) - q)) *
        (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) =
      (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
        ∏ u : κ, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
          (σ (e (.inl u.1)) v.castSucc : ℝ) * (σ (e (.inr u.1)) v.castSucc : ℝ) - q) :=
    fun σ => mul_comm _ _
  simp only [hcomm] at ht
  exact ht

end SpinGlasses
