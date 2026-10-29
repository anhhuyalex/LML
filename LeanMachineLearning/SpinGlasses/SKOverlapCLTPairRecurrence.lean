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
is a pair factor; the multiplicity counts its other ordered-pair matches. The finite
factor data are fixed, while the constant precedes the model parameters throughout the
high-temperature range and precedes the site count. -/
theorem sk_cavity_fresh_pair_recurrence_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [LinearOrder R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (p : J) (hLp : L p = true) (hSp : S p = true)
    (a b : J → R) (hord : ∀ j, L j = true → S j = true → a j < b j)
    (u₀ : J)
    (href : ((Finset.univ.filter fun u =>
        L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).erase p).Nonempty →
      u₀ ∈ (Finset.univ.filter fun u =>
        L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).erase p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
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
  obtain ⟨C₀, hC₀, hstep⟩ := sk_overlap_step_expansion β₀ hβ₀ (fun j : base => c j) 4
  obtain ⟨C₁, hC₁, hfeed⟩ := sk_cavity_fresh_pair_feedback_uniform β₀ hβ₀ L S p hLp hSp a b hord
  obtain ⟨C₂, hC₂, hterm⟩ := sk_cavity_term_I_multiplicity β₀ hβ₀
    (R := R) L S p hLp hSp
  obtain ⟨C₃, hC₃, hcomp⟩ := sk_overlap_prod_sub_truncated_le β₀ hβ₀ c 1
  obtain ⟨C₄, hC₄, hdel⟩ :=
    sk_overlap_prod_sub_truncated_le β₀ hβ₀ (fun j : del => c j) 1
  refine ⟨C₀ + C₁ + C₂ + β₀ ^ 2 * C₃ + ((cls.card - 1 : ℕ) : ℝ) * C₄,
    by positivity, ?_⟩
  intro β h q hfix hb N Esk U ν α' cls'
  let α := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
    ∂gaussianReal 0 1) - 2 * q + 1
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
    apply Finset.prod_bij (fun (j : base) _ => (j : J))
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
  have hs := hstep β h q hfix hb N (Fintype.card Q)
    (fun j : base => fun i => e (A j i)) (fun j : base => fun i => e (B j i))
    (fun j i => hAB j i) νf (fun _ => rfl)
    (fun j : base => Uf j) (fun j : base => Um j) (fun j : base => ee j)
    (fun j σ => hU j σ) (fun j σ => hV j σ) (fun j σ => he j σ) ξ hξ
  have hf := hfeed β h q hfix hb N
  have ht := hterm β h q hfix hb N a b hord u₀ href
  have hc := hcomp β h q hfix hb N (Fintype.card Q)
    (fun j i => e (A j i)) (fun j i => e (B j i)) hAB νf (fun _ => rfl)
    Uf Um ee hU hV he (fun _ => 1) (fun _ => by norm_num)
  have hd := hdel β h q hfix hb N (Fintype.card Q)
    (fun j : del => fun i => e (A j i)) (fun j : del => fun i => e (B j i))
    (fun j i => hAB j i) νf (fun _ => rfl)
    (fun j : del => Uf j) (fun j : del => Um j) (fun j : del => ee j)
    (fun j σ => hU j σ) (fun j σ => hV j σ) (fun j σ => he j σ)
    (fun _ => 1) (fun _ => by norm_num)
  let d : ℝ := ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2)
  let F : ℝ := ν (fun σ => ∏ j, U j σ)
  let Fm : ℝ := ν (fun σ => ∏ j, V j (fun r v => σ r v.castSucc))
  let D : ℝ := ν (fun σ => ∏ j ∈ del, U j σ)
  let Dm : ℝ := ν (fun σ => ∏ j ∈ del, V j (fun r v => σ r v.castSucc))
  let Lead : ℝ := ν (fun σ => (∏ j ∈ base, V j (fun r v => σ r v.castSucc)) *
    ep p (fun r => σ r (Fin.last N)))
  let I : ℝ := (N + 1 : ℝ)⁻¹ * ∑ u ∈ base,
    ν (fun σ => (∏ j ∈ base.erase u, V j (fun r v => σ r v.castSucc)) *
      (ep p (fun r => σ r (Fin.last N)) * ep u (fun r => σ r (Fin.last N))))
  let w : ℝ := (α / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ)
  have hdegree : Fintype.card base + 2 = Fintype.card J + 1 := by
    have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨p⟩
    simp only [Fintype.card_coe, base, Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
    omega
  have hsite (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) :
      (N + 1 : ℝ)⁻¹ * ∑ s : Fin (N + 1), ξ (fun r => σ r s) = Uf p σ := by
    simp only [ξ, ep, Uf, U, hLp, hSp, ite_true, Bool.true_or, sub_zero]
  have hfull_fun :
      (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ =>
        Uf p σ * ∏ j : base, Uf j σ) = (fun σ => ∏ j, Uf j σ) := by
    funext σ
    rw [hp (fun j => Uf j σ)]
    exact Finset.mul_prod_erase Finset.univ (fun j => Uf j σ) (Finset.mem_univ p)
  have hlead_fun :
      (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ =>
        ξ (fun r => σ r (Fin.last N)) * ∏ j : base, Um j σ) =
      (fun σ => (∏ j ∈ base, V j (fun r v => σ (e r) v.castSucc)) *
        ep p (fun r => σ (e r) (Fin.last N))) := by
    funext σ
    rw [hp (fun j => Um j σ)]
    exact mul_comm _ _
  have hpair_fun (u : base) :
      (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ =>
        ξ (fun r => σ r (Fin.last N)) *
          (ee u σ * ∏ j ∈ (Finset.univ : Finset base).erase u, Um j σ)) =
      (fun σ => (∏ j ∈ base.erase (u : J), V j (fun r v => σ (e r) v.castSucc)) *
        (ep p (fun r => σ (e r) (Fin.last N)) *
          ep u (fun r => σ (e r) (Fin.last N)))) := by
    funext σ
    dsimp only [ξ, ee]
    rw [hpe u (fun j => Um j σ)]
    ring
  simp_rw [hsite] at hs
  rw [hfull_fun, hlead_fun, hdegree] at hs
  simp_rw [hpair_fun] at hs
  have hs' : |F - (Lead + I)| ≤ C₀ / d := by
    dsimp only [F, Lead, I, d]
    rw [← Finset.sum_coe_sort base]
    simp_rw [havg]
    exact hs
  have hf' : |Lead - β ^ 2 * α * Fm| ≤ C₁ / d := hf
  have ht' : |I - w * Dm| ≤ C₂ / d := ht
  have hc' : |F - Fm| ≤ C₃ / d := by
    dsimp only [F, Fm]
    rw [havg, havg]
    change |Λ (fun σ => ∏ j, Uf j σ) - Λ (fun σ => ∏ j, Um j σ)| ≤ _
    rw [← map_sub]
    refine (Λ.abs_apply_le_apply_abs hmono _).trans ?_
    simpa only [one_mul, Pi.sub_apply, Λ, LinearMap.coe_mk, AddHom.coe_mk, d] using hc
  have hdfun :
      (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ =>
        ∏ j : del, Uf j σ) = (fun σ => ∏ j ∈ del, U j (fun r => σ (e r))) := by
    funext σ
    exact Finset.prod_coe_sort del (fun j => Uf j σ)
  have hdmfun :
      (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ =>
        ∏ j : del, Um j σ) =
      (fun σ => ∏ j ∈ del, V j (fun r v => σ (e r) v.castSucc)) := by
    funext σ
    exact Finset.prod_coe_sort del (fun j => Um j σ)
  have hd' : |D - Dm| ≤
      C₄ / ((N : ℝ) + 1) ^ (((del.card + 1 : ℕ) : ℝ) / 2) := by
    dsimp only [D, Dm]
    rw [havg, havg, ← hdfun, ← hdmfun]
    change |Λ (fun σ => ∏ j : del, Uf j σ) -
      Λ (fun σ => ∏ j : del, Um j σ)| ≤ _
    rw [← map_sub]
    refine (Λ.abs_apply_le_apply_abs hmono _).trans ?_
    simpa only [one_mul, Pi.sub_apply, Fintype.card_coe, Λ, LinearMap.coe_mk,
      AddHom.coe_mk] using hd
  have hα : |α| ≤ 1 := by
    have hfixz : ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 2
        ∂gaussianReal 0 1 = q := by rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
    have hh := probability_tanh_fourth_sub_two_add_one_mem_Icc
      (P := gaussianReal 0 1) (fun t : ℝ => β * t * Real.sqrt q + h) (by fun_prop)
    rw [hfixz] at hh
    exact abs_le.mpr ⟨by linarith only [hh.1], hh.2⟩
  have hcoef : |β ^ 2 * α * (Fm - F)| ≤ β₀ ^ 2 * C₃ / d := by
    have hβα : β ^ 2 * |α| ≤ β₀ ^ 2 :=
      (mul_le_mul_of_nonneg_left hα (sq_nonneg β)).trans (by simpa only [mul_one] using hb)
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β), abs_sub_comm]
    exact (mul_le_mul hβα hc' (abs_nonneg _) (sq_nonneg β₀)).trans_eq (by ring)
  have hw : |w * (Dm - D)| ≤ |α| * ((cls.card - 1 : ℕ) : ℝ) * C₄ / d := by
    by_cases hz : cls.card - 1 = 0
    · simp only [w, hz, Nat.cast_zero, mul_zero, zero_mul, abs_zero, zero_div, le_refl]
    have hpcls : p ∈ cls := by
      simp only [cls, Finset.mem_filter, Finset.mem_univ, hLp, hSp,
        and_self, eq_self]
    have hcpos : 1 < cls.card := by
      have : 0 < cls.card := Finset.card_pos.mpr ⟨p, hpcls⟩
      omega
    have hne : (cls.erase p).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hpcls]
      omega
    have hu : u₀ ∈ base := by
      exact Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp (href hne)).1, Finset.mem_univ u₀⟩
    have hnat : Fintype.card J = del.card + 2 := by
      have hbcard : base.card = Fintype.card J - 1 := by
        simp only [base, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
      have hdcard : del.card = base.card - 1 := Finset.card_erase_of_mem hu
      have hle := Finset.card_le_univ cls
      omega
    have hdscale : d = (N + 1 : ℝ) *
        ((N : ℝ) + 1) ^ (((del.card + 1 : ℕ) : ℝ) / 2) := by
      dsimp only [d]
      have hexp : ((Fintype.card J + 1 : ℕ) : ℝ) / 2 =
          1 + ((del.card + 1 : ℕ) : ℝ) / 2 := by rw [hnat]; push_cast; ring
      rw [hexp, Real.rpow_add (by positivity), Real.rpow_one]
    have hwp : |w| = |α| * ((cls.card - 1 : ℕ) : ℝ) / (N + 1 : ℝ) := by
      dsimp only [w]
      rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N + 1),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (cls.card - 1))]
      ring
    rw [abs_mul, hwp, abs_sub_comm]
    refine (mul_le_mul_of_nonneg_left hd' (by positivity)).trans_eq ?_
    rw [hdscale, div_mul_div_comm]
  have hwu : |w * (Dm - D)| ≤ ((cls.card - 1 : ℕ) : ℝ) * C₄ / d := by
    refine hw.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have hc0 : 0 ≤ ((cls.card - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα hc0) hC₄.le
  change |(1 - β ^ 2 * α) * F - w * D| ≤ _
  calc
    _ = |(((F - (Lead + I)) + (Lead - β ^ 2 * α * Fm)) + (I - w * Dm) +
        β ^ 2 * α * (Fm - F)) + w * (Dm - D)| := congrArg abs (by ring)
    _ ≤ |F - (Lead + I)| + |Lead - β ^ 2 * α * Fm| + |I - w * Dm| +
        |β ^ 2 * α * (Fm - F)| + |w * (Dm - D)| := by
      have h1 := abs_add_le
        (((F - (Lead + I)) + (Lead - β ^ 2 * α * Fm)) + (I - w * Dm) +
          β ^ 2 * α * (Fm - F)) (w * (Dm - D))
      have h2 := abs_add_le
        (((F - (Lead + I)) + (Lead - β ^ 2 * α * Fm)) + (I - w * Dm))
        (β ^ 2 * α * (Fm - F))
      have h3 := abs_add_le ((F - (Lead + I)) + (Lead - β ^ 2 * α * Fm)) (I - w * Dm)
      have h4 := abs_add_le (F - (Lead + I)) (Lead - β ^ 2 * α * Fm)
      linarith only [h1, h2, h3, h4]
    _ ≤ C₀ / d + C₁ / d + C₂ / d + β₀ ^ 2 * C₃ / d +
        ((cls.card - 1 : ℕ) : ℝ) * C₄ / d :=
      add_le_add (add_le_add (add_le_add (add_le_add hs' hf') ht') hcoef) hwu
    _ = _ := by ring

/-- **Eq. (1.313) with fixed model parameters.** This specializes the uniform
recurrence and keeps the error constant before the site count. -/
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
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
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
  obtain ⟨C, hC0, hC⟩ :=
    sk_cavity_fresh_pair_recurrence_uniform β hβ L S p hLp hSp a b hord u₀ href
  exact ⟨C, hC0, hC β h q hfix le_rfl⟩

end SpinGlasses
