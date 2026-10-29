/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTPairFeedback
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTTermIMultiplicity
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTComparison

/-!
# The pair-factor recurrence of Talagrand, Eq. (1.313)

Combine the last-site expansion, the leading rectangular feedback and the multiplicity
calculation. Both truncated products are replaced by full products with explicit errors.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Eq. (1.313), for the actual enumerated fresh-factor products.** The selected factor
is a pair factor and the multiplicity counts its other ordered-pair matches. Constants
are chosen before the site count; the model parameters and finite factor data are fixed. -/
theorem sk_cavity_fresh_pair_recurrence (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q)
    {R J : Type*} [Fintype R] [LinearOrder R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (p : J) (hLp : L p = true) (hSp : S p = true)
    (a b : J → R) (hord : ∀ j, L j = true → S j = true → a j < b j)
    (u₀ : J)
    (href : ((Finset.univ.filter fun u =>
        L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).erase p).Nonempty →
      u₀ ∈ (Finset.univ.filter fun u =>
        L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).erase p) :
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
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
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
    let cls : Finset J := Finset.univ.filter fun u =>
      L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p
    |(1 - β ^ 2 * α) * ν (fun σ => ∏ j, U j σ) -
      (α / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) *
        ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀, U j σ)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let Q := R ⊕ (J ⊕ J)
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let base : Finset J := Finset.univ.erase p
  let del : Finset J := base.erase u₀
  let cls : Finset J := Finset.univ.filter fun u =>
    L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p
  let c : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  let A : J → Bool × Bool → Q := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let B : J → Bool × Bool → Q := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  let α := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
    ∂gaussianReal 0 1) - 2 * q + 1
  obtain ⟨C₀, hC₀, hstep⟩ := sk_overlap_step_expansion β hβ (fun j : base => c j) 4
  obtain ⟨C₁, hC₁, hfeed⟩ := sk_cavity_fresh_pair_feedback β h q hβ hfix L S p hLp hSp a b hord
  obtain ⟨C₂, hC₂, hterm⟩ := sk_cavity_term_I_multiplicity β hβ
    (R := R) L S p hLp hSp
  obtain ⟨C₃, hC₃, hcomp⟩ := sk_overlap_prod_sub_truncated_le β hβ c 1
  obtain ⟨C₄, hC₄, hdel⟩ :=
    sk_overlap_prod_sub_truncated_le β hβ (fun j : del => c j) 1
  refine ⟨C₀ + C₁ + C₂ + β ^ 2 * |α| * C₃ + |α| * ((cls.card - 1 : ℕ) : ℝ) * C₄,
    by positivity, ?_⟩
  intro N Esk V U ep ν α' cls'
  have hAB (j : J) (i : Bool × Bool) : e (A j i) ≠ e (B j i) :=
    e.injective.ne (flagged_pair_ne (a j) (b j) j (L j) (S j)
      (fun hL hS => ne_of_lt (hord j hL hS)) i)
  let νf : ((Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun H =>
    ∫ g, ∫ σ, H σ
      ∂(Measure.pi fun _ : Fin (Fintype.card Q) => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have havg (H : (Q → Fin (N + 1) → ℤˣ) → ℝ) :
      ν H = νf (fun σ => H (fun r => σ (e r))) := by
    dsimp only [ν, νf]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    exact integral_pi_count_tilted_reindex e (Esk g) H
  obtain ⟨hadd, hsmul, hmono, -⟩ := sk_replica_avg_calculus N (Fintype.card Q)
    β h νf (fun _ => rfl)
  let Λ : ((Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ :=
    ⟨⟨νf, hadd⟩, hsmul⟩
  have hU (j : J) (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) :
      U j (fun r => σ (e r)) = ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v => (σ (e (A j i)) v : ℝ)) ⬝ᵥ
          fun v => (σ (e (B j i)) v : ℝ)) - q) := by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin (N + 1) → ℤˣ) (v : Fin (N + 1)) => (s v : ℝ))
      (fun r => σ (e r)) (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hV (j : J) (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) :
      V j (fun r v => σ (e r) v.castSucc) =
        ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
          ((fun v : Fin N => (σ (e (A j i)) v.castSucc : ℝ)) ⬝ᵥ
            fun v : Fin N => (σ (e (B j i)) v.castSucc : ℝ)) - q) := by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin N → ℤˣ) (v : Fin N) => (s v : ℝ))
      (fun r v => σ (e r) v.castSucc) (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have he (j : J) (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) :
      ep j (fun r => σ (e r) (Fin.last N)) = ∑ i : Bool × Bool, c j i *
        ((σ (e (A j i)) (Fin.last N) : ℝ) * (σ (e (B j i)) (Fin.last N) : ℝ)) := by
    cases hL : L j <;> cases hS : S j <;>
      simp [ep, A, B, c, hL, hS, Fintype.sum_prod_type] <;> ring
  have hp (H : J → ℝ) : (∏ j : base, H j) = ∏ j ∈ base, H j :=
    Finset.prod_coe_sort base H
  have hpe (u : base) (H : J → ℝ) :
      (∏ j ∈ (Finset.univ : Finset base).erase u, H j) = ∏ j ∈ base.erase (u : J), H j := by
    apply Finset.prod_bij (fun j _ => (j : J))
    · intro j hj
      exact Finset.mem_erase.mpr
        ⟨fun heq => (Finset.ne_of_mem_erase hj) (Subtype.ext heq), j.2⟩
    · intro j _ k _ hjk
      exact Subtype.ext hjk
    · intro j hj
      refine ⟨⟨j, (Finset.mem_erase.mp hj).2⟩, ?_, rfl⟩
      simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using
        (show (⟨j, (Finset.mem_erase.mp hj).2⟩ : base) ≠ u from
          fun h => (Finset.ne_of_mem_erase hj) (congrArg Subtype.val h))
    · intro _ _
      rfl
  let Uf : J → (Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) → ℝ :=
    fun j σ => U j (fun r => σ (e r))
  let Um : J → (Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) → ℝ :=
    fun j σ => V j (fun r v => σ (e r) v.castSucc)
  let ee : J → (Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) → ℝ :=
    fun j σ => ep j (fun r => σ (e r) (Fin.last N))
  let ξ : (Fin (Fintype.card Q) → ℤˣ) → ℝ := fun ε => ep p (fun r => ε (e r))
  have hξ (ε) : |ξ ε| ≤ 4 := by
    dsimp only [ξ, ep]
    rw [hLp, hSp]
    simp only [ite_true, abs_mul]
    have h1 := (abs_sub ((ε (e (.inl (a p))) : ℝ))
      (ε (e (.inr (.inl p))) : ℝ)).trans
      (add_le_add (abs_units_cast_le_one _) (abs_units_cast_le_one _))
    have h2 := (abs_sub ((ε (e (.inl (b p))) : ℝ))
      (ε (e (.inr (.inr p))) : ℝ)).trans
      (add_le_add (abs_units_cast_le_one _) (abs_units_cast_le_one _))
    exact (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hs := hstep β h q hfix le_rfl N (Fintype.card Q)
    (fun j : base => fun i => e (A j i)) (fun j : base => fun i => e (B j i))
    (fun j i => hAB j i) νf (fun _ => rfl)
    (fun j : base => Uf j) (fun j : base => Um j) (fun j : base => ee j)
    (fun j σ => hU j σ) (fun j σ => hV j σ) (fun j σ => he j σ) ξ hξ
  have hf := hfeed N
  have ht := hterm β h q hfix le_rfl N a b hord u₀ href
  have hc := hcomp β h q hfix le_rfl N (Fintype.card Q)
    (fun j i => e (A j i)) (fun j i => e (B j i)) hAB νf (fun _ => rfl)
    Uf Um ee hU hV he (fun _ => 1) (fun _ => by norm_num)
  have hd := hdel β h q hfix le_rfl N (Fintype.card Q)
    (fun j : del => fun i => e (A j i)) (fun j : del => fun i => e (B j i))
    (fun j i => hAB j i) νf (fun _ => rfl)
    (fun j : del => Uf j) (fun j : del => Um j) (fun j : del => ee j)
    (fun j σ => hU j σ) (fun j σ => hV j σ) (fun j σ => he j σ)
    (fun _ => 1) (fun _ => by norm_num)

end SpinGlasses
