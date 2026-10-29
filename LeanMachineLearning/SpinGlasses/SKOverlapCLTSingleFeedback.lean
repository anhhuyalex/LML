/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTPairFeedback
public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrderCorollary

/-!
# The single-factor feedback (1.317)-(1.318) for fresh factors

Apply Corollary 1.10.3, Eq. (1.302), to a leading single factor on the fresh-replica space
`R ⊕ (J ⊕ J)`. The product of the remaining fresh factors does not depend on the last fresh
replica of the leading factor, which is the independence hypothesis of (1.302).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Eq. (1.317)-(1.318) for the actual fresh single factor.** The leading single factor times
the product of the remaining truncated fresh factors equals `β² (1-4q+3q̂)` times the average of
its truncated overlap increment, plus the term II over the other replicas, up to
`C/(N+1)^((card J + 1)/2)`. The constant precedes the temperature, field and site count. -/
theorem sk_cavity_fresh_single_feedback_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (p : J) (hLp : L p = true) (hSp : S p = false)
    (a b : J → R) (hab : ∀ j, L j = true → S j = true → a j ≠ b j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
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
    let ν₂ : ((Option (Option (R ⊕ (J ⊕ J))) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (R ⊕ (J ⊕ J))) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let Jf : Option (Option (R ⊕ (J ⊕ J))) → Option (Option (R ⊕ (J ⊕ J))) → ℝ := fun x y =>
      ν₂ (fun σ => (∏ j ∈ Finset.univ.erase p, V j (fun r v => σ (some (some r)) v.castSucc)) *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ x v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ y v.castSucc : ℝ)) - q))
    |ν (fun σ => (∏ j ∈ Finset.univ.erase p, V j (fun r v => σ r v.castSucc)) *
        ep p (fun r => σ r (Fin.last N))) -
      (β ^ 2 * (1 - 4 * q + 3 * qh) *
        (Jf (some (some (.inl (a p)))) (some (some (.inr (.inr p)))) -
          Jf (some (some (.inr (.inl p)))) (some (some (.inr (.inr p))))) +
      β ^ 2 * (q - qh) *
        ∑ l ∈ Finset.univ.filter (fun l : R ⊕ (J ⊕ J) =>
            l ≠ .inl (a p) ∧ l ≠ .inr (.inl p) ∧ l ≠ .inr (.inr p)),
          (Jf (some (some (.inl (a p)))) (some (some l)) -
            Jf (some (some (.inr (.inl p)))) (some (some l)) -
            (Jf (some (some (.inl (a p)))) (some none) -
              Jf (some (some (.inr (.inl p)))) (some none))))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let Q := R ⊕ (J ⊕ J)
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let ee : Option (Option Q) ≃ Option (Option (Fin (Fintype.card Q))) :=
    e.optionCongr.optionCongr
  let base : Finset J := Finset.univ.erase p
  let f := base.equivFin
  let A : J → Bool × Bool → Q := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let B : J → Bool × Bool → Q := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  let c : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  have h12 : e (.inl (a p)) ≠ e (.inr (.inl p)) := e.injective.ne (by simp)
  have h1r : e (.inl (a p)) ≠ e (.inr (.inr p)) := e.injective.ne (by simp)
  have h2r : e (.inr (.inl p)) ≠ e (.inr (.inr p)) :=
    e.injective.ne (by intro h; cases h)
  obtain ⟨C, hC0, hC⟩ := sk_cavity_sub_third_lincomb_expansion_uniform β₀ hβ₀
    (Fintype.card Q) base.card h12 h1r h2r (fun i => c (f.symm i))
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N Esk V ep ν ν₂ qh Jf
  have hqhat : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 4 ∂gaussianReal 0 1 = qh := by
    apply integral_congr_ae (ae_of_all _ fun t => ?_)
    congr 2
    ring
  have hAB (j : J) (i : Bool × Bool) : A j i ≠ B j i :=
    flagged_pair_ne (a j) (b j) j (L j) (S j) (hab j) i
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
  have hindep : ∀ (ρ : Fin (Fintype.card Q) → Fin N → ℤˣ) z,
      (∏ j : Fin base.card, ∑ i : Bool × Bool, c (f.symm j) i *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N =>
          ((Function.update ρ (e (.inr (.inr p))) z) (e (A (f.symm j) i)) v : ℝ)) ⬝ᵥ
          fun v : Fin N => ((Function.update ρ (e (.inr (.inr p))) z) (e (B (f.symm j) i)) v : ℝ))
          - q)) =
      ∏ j : Fin base.card, ∑ i : Bool × Bool, c (f.symm j) i *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (e (A (f.symm j) i)) v : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ (e (B (f.symm j) i)) v : ℝ)) - q) := by
    intro ρ z
    refine Finset.prod_congr rfl fun jj _ => Finset.sum_congr rfl fun i _ => ?_
    have hjp : (f.symm jj).1 ≠ p := Finset.ne_of_mem_erase (f.symm jj).2
    have hA : e (A (f.symm jj) i) ≠ e (.inr (.inr p)) := by
      refine e.injective.ne ?_
      simp only [A]
      split_ifs
      · simp
      · intro h
        cases h
    have hB : e (B (f.symm jj) i) ≠ e (.inr (.inr p)) := by
      refine e.injective.ne ?_
      simp only [B]
      split_ifs
      · simp
      · intro h
        exact hjp (Sum.inr_injective (Sum.inr_injective h))
    simp only [Function.update_of_ne hA, Function.update_of_ne hB]
  have ht := hC β h q qh hfix hqhat hb N (fun j i => e (A (f.symm j) i))
    (fun j i => e (B (f.symm j) i)) (fun j i => e.injective.ne (hAB _ i)) hindep
  let Ffin : (Fin (Fintype.card Q) → Fin N → ℤˣ) → ℝ := fun ρ =>
    ∏ j : Fin base.card, ∑ i : Bool × Bool, c (f.symm j) i *
      ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (e (A (f.symm j) i)) v : ℝ)) ⬝ᵥ
        fun v : Fin N => (ρ (e (B (f.symm j) i)) v : ℝ)) - q)
  let Jfin : Option (Option (Fin (Fintype.card Q))) → Option (Option (Fin (Fintype.card Q))) →
      ℝ := fun x y =>
    ∫ g, ∫ σ : Option (Option (Fin (Fintype.card Q))) → Fin (N + 1) → ℤˣ,
      Ffin (fun r i => σ (some (some r)) i.castSucc) *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ x v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ y v.castSucc : ℝ)) - q)
      ∂(Measure.pi fun _ : Option (Option (Fin (Fintype.card Q))) =>
        Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have ht' : |(∫ g, ∫ σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ,
        Ffin (fun l i => σ l i.castSucc) *
          ((((σ (e (.inl (a p))) (Fin.last N) : ℤˣ) : ℝ) -
            ((σ (e (.inr (.inl p))) (Fin.last N) : ℤˣ) : ℝ)) *
            ((σ (e (.inr (.inr p))) (Fin.last N) : ℤˣ) : ℝ))
        ∂(Measure.pi fun _ : Fin (Fintype.card Q) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (β ^ 2 * (1 - 4 * q + 3 * qh) *
        (Jfin (some (some (e (.inl (a p))))) (some (some (e (.inr (.inr p))))) -
          Jfin (some (some (e (.inr (.inl p))))) (some (some (e (.inr (.inr p)))))) +
      β ^ 2 * (q - qh) *
        ∑ l ∈ Finset.univ.filter (fun l : Fin (Fintype.card Q) =>
            l ≠ e (.inl (a p)) ∧ l ≠ e (.inr (.inl p)) ∧ l ≠ e (.inr (.inr p))),
          (Jfin (some (some (e (.inl (a p))))) (some (some l)) -
            Jfin (some (some (e (.inr (.inl p))))) (some (some l)) -
            (Jfin (some (some (e (.inl (a p))))) (some none) -
              Jfin (some (some (e (.inr (.inl p))))) (some none))))| ≤
      C / ((N : ℝ) + 1) ^ (((base.card + 2 : ℕ) : ℝ) / 2) := by
    exact ht
  have havg (H : (Q → Fin (N + 1) → ℤˣ) → ℝ) : ν H =
      ∫ g, ∫ σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ,
        H (fun r => σ (e r))
        ∂(Measure.pi fun _ : Fin (Fintype.card Q) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    dsimp only [ν]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    exact integral_pi_count_tilted_reindex e (Esk g) H
  have hJ (x y : Option (Option Q)) : Jf x y = Jfin (ee x) (ee y) := by
    dsimp only [Jf, ν₂, Jfin]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    rw [integral_pi_count_tilted_reindex ee (Esk g)]
    apply integral_congr_ae (ae_of_all _ fun σ => ?_)
    have := hF (fun r i => σ (some (some r)) i.castSucc)
    simp only [Ffin, this]
    rfl
  have hfirst : ν (fun σ => (∏ j ∈ Finset.univ.erase p, V j (fun r v => σ r v.castSucc)) *
        ep p (fun r => σ r (Fin.last N))) =
      ∫ g, ∫ σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ,
        Ffin (fun l i => σ l i.castSucc) *
          ((((σ (e (.inl (a p))) (Fin.last N) : ℤˣ) : ℝ) -
            ((σ (e (.inr (.inl p))) (Fin.last N) : ℤˣ) : ℝ)) *
            ((σ (e (.inr (.inr p))) (Fin.last N) : ℤˣ) : ℝ))
        ∂(Measure.pi fun _ : Fin (Fintype.card Q) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    rw [havg]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    apply integral_congr_ae (ae_of_all _ fun σ => ?_)
    have := hF (fun r i => σ r i.castSucc)
    simp only [Ffin, this, ep, hLp, hSp, ite_true, Bool.false_eq_true, ite_false]
    rfl
  have hdegree : base.card + 2 = Fintype.card J + 1 := by
    have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨p⟩
    dsimp only [base]
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    omega
  rw [hdegree] at ht'
  rw [hfirst]
  convert ht' using 3
  simp only [hJ]
  congr 2
  rw [Finset.sum_filter, Finset.sum_filter, ← e.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [ne_eq, e.apply_eq_iff_eq]
  rfl

end SpinGlasses
