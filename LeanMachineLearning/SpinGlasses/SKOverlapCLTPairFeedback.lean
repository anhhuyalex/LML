/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrderCorollary
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTTermIMultiplicity
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTComparison

/-!
# The leading pair-factor feedback before Talagrand's Eq. (1.313)

The source's fresh-factor product is transported to `Fin` once, so that Corollary 1.10.3
applies directly. The resulting average is transported back to the original replica type.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The leading rectangular term immediately before Eq. (1.313).** All factors are
explicit fresh-overlap kernels. The positive error constant precedes the site count;
model parameters and original labels are fixed in this version. -/
theorem sk_cavity_fresh_pair_feedback (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q)
    {R J : Type*} [Fintype R] [LinearOrder R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (p : J) (hLp : L p = true) (hSp : S p = true)
    (a b : J → R) (hord : ∀ j, L j = true → S j = true → a j < b j) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let V : J → ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let ep : J → (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun j ε =>
      (if L j then (ε (.inl (a j)) : ℝ) - (ε (.inr (.inl j)) : ℝ)
        else (ε (.inr (.inl j)) : ℝ)) *
      (if S j then (ε (.inl (b j)) : ℝ) - (ε (.inr (.inr j)) : ℝ)
        else (ε (.inr (.inr j)) : ℝ))
    let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |ν (fun σ => (∏ j ∈ Finset.univ.erase p, V j (fun r v => σ r v.castSucc)) *
        ep p (fun r => σ r (Fin.last N))) -
      β ^ 2 * α * ν (fun σ => ∏ j, V j (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let Q := R ⊕ (J ⊕ J)
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let base : Finset J := Finset.univ.erase p
  let f := base.equivFin
  let A : J → Bool × Bool → Q := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let B : J → Bool × Bool → Q := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  let c : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  let qhat := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
  have hqhat : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 4
      ∂gaussianReal 0 1 = qhat := by
    apply integral_congr_ae (ae_of_all _ fun t => ?_)
    congr 2
    ring
  have h13 : e (.inl (a p)) ≠ e (.inl (b p)) :=
    e.injective.ne (Sum.inl_injective.ne (ne_of_lt (hord p hLp hSp)))
  obtain ⟨C, hC0, hC⟩ := sk_cavity_rect_lincomb_expansion β h q hβ hfix qhat hqhat
    (Fintype.card Q) base.card
    (i₁ := e (.inl (a p))) (i₂ := e (.inr (.inl p)))
    (j₁ := e (.inl (b p))) (j₂ := e (.inr (.inr p)))
    (e.injective.ne (by simp)) h13 (e.injective.ne (by simp))
    (e.injective.ne (by simp))
    (e.injective.ne (by intro h; cases h))
    (fun i => c (f.symm i))
  refine ⟨C, hC0, ?_⟩
  intro N Esk V ep ν α
  have hAB (j : J) (i : Bool × Bool) : A j i ≠ B j i :=
    flagged_pair_ne (a j) (b j) j (L j) (S j)
      (fun hL hS => ne_of_lt (hord j hL hS)) i
  have hV (j : J) (ρ : Q → Fin N → ℤˣ) :
      (∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (ρ (A j i) v : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ (B j i) v : ℝ)) - q)) = V j ρ := by
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin N → ℤˣ) (v : Fin N) => (s v : ℝ)) ρ
      (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hp (H : J → ℝ) : (∏ i : Fin base.card, H (f.symm i)) = ∏ j ∈ base, H j := by
    rw [← Finset.prod_coe_sort base H]
    exact Equiv.prod_comp f.symm (fun j : base => H j)
  have hF (ρ : Fin (Fintype.card Q) → Fin N → ℤˣ) :
      (∏ j : Fin base.card, ∑ i : Bool × Bool, c (f.symm j) i *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (e (A (f.symm j) i)) v : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ (e (B (f.symm j) i)) v : ℝ)) - q)) =
        ∏ j ∈ base, V j (fun r => ρ (e r)) := by
    have hv (j : J) := hV j (fun r => ρ (e r))
    simp_rw [hv]
    exact hp (fun j => V j (fun r => ρ (e r)))
  have hrect (ρ : Q → Fin N → ℤˣ) :
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (.inl (a p)) i : ℝ)) ⬝ᵥ
          fun i : Fin N => (ρ (.inl (b p)) i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (.inr (.inl p)) i : ℝ)) ⬝ᵥ
          fun i : Fin N => (ρ (.inl (b p)) i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (.inl (a p)) i : ℝ)) ⬝ᵥ
          fun i : Fin N => (ρ (.inr (.inr p)) i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (.inr (.inl p)) i : ℝ)) ⬝ᵥ
          fun i : Fin N => (ρ (.inr (.inr p)) i : ℝ)) = V p ρ := by
    simp only [V, hLp, hSp, ite_true, Bool.true_or, sub_zero, dotProduct,
      sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have havg (H : (Q → Fin (N + 1) → ℤˣ) → ℝ) : ν H =
      ∫ g, ∫ σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ,
        H (fun r => σ (e r))
        ∂(Measure.pi fun _ : Fin (Fintype.card Q) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    dsimp only [ν]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    exact integral_pi_count_tilted_reindex e (Esk g) H
  have ht := hC N (fun j i => e (A (f.symm j) i))
    (fun j i => e (B (f.symm j) i)) (fun j i => e.injective.ne (hAB _ i))
  dsimp only [] at ht
  have hFfull (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) :=
    hF (fun r v => σ r v.castSucc)
  simp_rw [hFfull] at ht
  have hrectfull (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) :=
    hrect (fun r v => σ (e r) v.castSucc)
  simp_rw [hrectfull] at ht
  have hprod (σ : Q → Fin N → ℤˣ) : (∏ j ∈ base, V j σ) * V p σ = ∏ j, V j σ := by
    simpa only [mul_comm] using
      (Finset.mul_prod_erase (Finset.univ : Finset J) (fun j => V j σ)
        (Finset.mem_univ p))
  have hprod_fun :
      (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ =>
        (∏ j ∈ base, V j (fun r v => σ (e r) v.castSucc)) *
          V p (fun r v => σ (e r) v.castSucc)) =
      (fun σ => ∏ j, V j (fun r v => σ (e r) v.castSucc)) :=
    funext fun σ => hprod (fun r v => σ (e r) v.castSucc)
  rw [hprod_fun] at ht
  have hdegree : base.card + 2 = Fintype.card J + 1 := by
    have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨p⟩
    dsimp only [base]
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    omega
  have hα : 1 - 2 * q + qhat = α := by dsimp only [α, qhat]; ring
  rw [hdegree, hα] at ht
  rw [havg, havg]
  simpa only [ep, hLp, hSp, ite_true] using ht

end SpinGlasses
