/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTTermI
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTSingleContractions
public import LeanMachineLearning.SpinGlasses.SKTBasisAlgebra
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas

/-!
# Quantitative contractions of a leading single factor (term I of Proposition 1.10.5)

The exact fresh contraction `sk_cavity_decoupled_fresh_single` and the generic comparison
`sk_cavity_prod_contraction_compare` give each summand of Talagrand's Eq. (1.316), with the
same error orders as in the pair case (1.312).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The individual contractions in term I of Eq. (1.316).** A product over `s` truncated
overlap factors contracts with a leading single factor `(ε_x - ε_p) ε_p'` and a flagged fresh
factor up to `C/(N+1)^((card s+1)/2)`. The coefficient is `q - q̂` times the number of matches
of `x` with the flagged slot of a single partner, and zero for pair and global partners. -/
theorem sk_cavity_fresh_single_product_compare (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J κ : Type*} [Fintype R] [Fintype J] [DecidableEq R] [DecidableEq J]
    (s : Finset κ) {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (x z w : R) (p u : J), p ≠ u → ∀ (L S : Bool),
      (L = true → S = true → z ≠ w) →
      ∀ (A B : ∀ j, ι j → R ⊕ (J ⊕ J)), (∀ j ∈ s, ∀ i, A j i ≠ B j i) →
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let G : ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun ρ =>
      ∏ j ∈ s, ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (ρ (A j i) v : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ (B j i) v : ℝ)) - q)
    let e0 : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      ((ε (.inl x) : ℝ) - (ε (.inr (.inl p)) : ℝ)) * (ε (.inr (.inr p)) : ℝ)
    let eu : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      (if L then (ε (.inl z) : ℝ) - (ε (.inr (.inl u)) : ℝ)
        else (ε (.inr (.inl u)) : ℝ)) *
      (if S then (ε (.inl w) : ℝ) - (ε (.inr (.inr u)) : ℝ)
        else (ε (.inr (.inr u)) : ℝ))
    let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let d : ℝ := q - ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let δ : ℝ := (if L && !S then (if x = z then 1 else 0) else 0) +
      (if S && !L then (if x = w then 1 else 0) else 0)
    |ν (fun σ => G (fun r v => σ r v.castSucc) *
        (e0 (fun r => σ r (Fin.last N)) * eu (fun r => σ r (Fin.last N)))) -
      d * δ * ν (fun σ => G (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_cavity_prod_contraction_compare β₀ hβ₀ (R := R ⊕ (J ⊕ J)) s c
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N x z w p u hpu L S hzw A B hAB Esk G e0 eu ν d δ
  have hfixz : ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 2 ∂gaussianReal 0 1 = q := by
    rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
  have hside (b : Bool) (a c : ℤˣ) : |if b then (a : ℝ) - (c : ℝ) else (c : ℝ)| ≤ 2 := by
    cases b
    · norm_num [abs_units_cast_eq_one]
    · exact (abs_sub _ _).trans (by norm_num [abs_units_cast_eq_one])
  have hWl (ε : R ⊕ (J ⊕ J) → ℤˣ) : |e0 ε * eu ε| ≤ 16 := by
    have he0 : |e0 ε| ≤ 4 := by
      dsimp [e0]
      rw [abs_mul]
      exact (mul_le_mul (hside true _ _) (by simp [abs_units_cast_eq_one])
        (abs_nonneg _) (by norm_num)).trans (by norm_num : (2 : ℝ) * 1 ≤ 4)
    have heu : |eu ε| ≤ 4 := by
      dsimp [eu]
      rw [abs_mul]
      exact (mul_le_mul (hside L _ _) (hside S _ _) (abs_nonneg _) (by norm_num)).trans
        (by norm_num : (2 : ℝ) * 2 ≤ 4)
    rw [abs_mul]
    exact (mul_le_mul he0 heu (abs_nonneg _) (by norm_num)).trans (by norm_num : (4 : ℝ) * 4 ≤ 16)
  have hd : |d| ≤ 1 := abs_sub_integral_tanh_fourth_le_one_of_fixedPoint hfix
  have hδ : |δ| ≤ 2 := by
    dsimp [δ]
    split_ifs <;> norm_num
  have hdδ : |d * δ| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hd hδ (abs_nonneg _) zero_le_one).trans (by norm_num : (1 : ℝ) * 2 ≤ 2)
  exact hC β h q hfix hb N A B hAB (fun ε => e0 ε * eu ε) hWl (d * δ) hdδ
    (sk_cavity_decoupled_fresh_single N β q h hfixz x z w p u hpu L S hzw G)

/-- **The finite pairing sum for term I in Eq. (1.316).** The single-type analogue of
`sk_cavity_fresh_term_sum_compare`: after the outer inverse size the error is
`C/(N+1)^((k+3)/2)`, uniformly over the temperature range. -/
theorem sk_cavity_fresh_single_term_sum_compare (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J U κ : Type*} [Fintype R] [Fintype J] [Fintype U] [DecidableEq R] [DecidableEq J]
    (s : U → Finset κ) (k : ℕ) (hcard : ∀ i, (s i).card = k)
    {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (x : R) (z w : U → R) (p : J) (v : U → J),
      (∀ i, p ≠ v i) → ∀ (L S : U → Bool),
      (∀ i, L i = true → S i = true → z i ≠ w i) →
      ∀ (A B : ∀ j, ι j → R ⊕ (J ⊕ J)),
      (∀ i j, j ∈ s i → ∀ a, A j a ≠ B j a) →
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let G : U → ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun i ρ =>
      ∏ j ∈ s i, ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (ρ (A j i) v : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ (B j i) v : ℝ)) - q)
    let e0 : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      ((ε (.inl x) : ℝ) - (ε (.inr (.inl p)) : ℝ)) * (ε (.inr (.inr p)) : ℝ)
    let eu : U → (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun i ε =>
      (if L i then (ε (.inl (z i)) : ℝ) - (ε (.inr (.inl (v i))) : ℝ)
        else (ε (.inr (.inl (v i))) : ℝ)) *
      (if S i then (ε (.inl (w i)) : ℝ) - (ε (.inr (.inr (v i))) : ℝ)
        else (ε (.inr (.inr (v i))) : ℝ))
    let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let d : ℝ := q - ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let δ : U → ℝ := fun i => (if L i && !S i then (if x = z i then 1 else 0) else 0) +
      (if S i && !L i then (if x = w i then 1 else 0) else 0)
    |(N + 1 : ℝ)⁻¹ * (∑ i : U, ν (fun σ => G i (fun r v => σ r v.castSucc) *
        (e0 (fun r => σ r (Fin.last N)) * eu i (fun r => σ r (Fin.last N))))) -
      (d / (N + 1 : ℝ)) * ∑ i : U, δ i * ν (fun σ => G i (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 3 : ℕ) : ℝ) / 2) := by
  choose C hC0 hC using fun i : U => sk_cavity_fresh_single_product_compare β₀ hβ₀
    (R := R) (J := J) (s i) c
  refine ⟨(∑ i : U, C i) + 1, by
    linarith only [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hC0 i).le)], ?_⟩
  intro β h q hfix hb N x z w p v hpv L S hzw A B hAB Esk G e0 eu ν d δ
  have ht (i : U) : |ν (fun σ => G i (fun r v => σ r v.castSucc) *
        (e0 (fun r => σ r (Fin.last N)) * eu i (fun r => σ r (Fin.last N)))) -
      d * δ i * ν (fun σ => G i (fun r v => σ r v.castSucc))| ≤
      C i / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
    simpa only [hcard i] using hC i β h q hfix hb N x (z i) (w i) p (v i) (hpv i) (L i) (S i)
      (hzw i) A B (hAB i)
  have hsum := abs_inv_succ_mul_sum_sub_le _ _ _ k N ht
  have e : (d / (N + 1 : ℝ)) * ∑ i : U, δ i * ν (fun σ => G i (fun r v => σ r v.castSucc)) =
      (N + 1 : ℝ)⁻¹ * ∑ i : U, d * δ i * ν (fun σ => G i (fun r v => σ r v.castSucc)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact hsum.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- **Eq. (1.316), with the actual multiplicity of the leading single label.** The leading factor
`p` is a single factor `(σ^{a p} - b) b`, all factors have flags `(true,true)` (pair),
`(true,false)` (single) or `(false,false)` (global), and `cls` is the class of single factors with
the label of `p`. The reference deleted factor is any member of the class other than `p` when
there is one; otherwise the coefficient vanishes. The coefficient is `q - q̂` over `N + 1` and the
constant is uniform over the temperature range and chosen before every site count and label. -/
theorem sk_cavity_single_term_I_multiplicity (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [Fintype J] [DecidableEq R] [DecidableEq J]
    (L S : J → Bool) (hLS : ∀ j, S j = true → L j = true) (p : J) (hLp : L p = true)
    (hSp : S p = false) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (a b : J → R),
      (∀ j, L j = true → S j = true → a j ≠ b j) →
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
    let G : J → ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun u ρ =>
      ∏ j ∈ (Finset.univ.erase p).erase u, V j ρ
    let e : J → (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun j ε =>
      (if L j then (ε (.inl (a j)) : ℝ) - (ε (.inr (.inl j)) : ℝ)
        else (ε (.inr (.inl j)) : ℝ)) *
      (if S j then (ε (.inl (b j)) : ℝ) - (ε (.inr (.inr j)) : ℝ)
        else (ε (.inr (.inr j)) : ℝ))
    let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let d : ℝ := q - ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let cls : Finset J := Finset.univ.filter fun u =>
      L u = true ∧ S u = false ∧ a u = a p
    ∀ (u₀ : J), ((cls.erase p).Nonempty → u₀ ∈ cls.erase p) →
    |(N + 1 : ℝ)⁻¹ * (∑ u ∈ Finset.univ.erase p,
        ν (fun σ => G u (fun r v => σ r v.castSucc) *
          (e p (fun r => σ r (Fin.last N)) * e u (fun r => σ r (Fin.last N))))) -
      (d / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) *
        ν (fun σ => G u₀ (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let base : Finset J := Finset.univ.erase p
  let c : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  have hcard (u : base) : (base.erase (u : J)).card = Fintype.card J - 2 := by
    rw [Finset.card_erase_of_mem u.2]
    dsimp [base]
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    omega
  obtain ⟨C, hC0, hC⟩ := sk_cavity_fresh_single_term_sum_compare β₀ hβ₀
    (R := R) (J := J) (fun u : base => base.erase (u : J))
    (Fintype.card J - 2) hcard c
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N a b hab Esk V G e ν d cls u₀ href
  let A : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let B : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  have hAB (j : J) (i : Bool × Bool) : A j i ≠ B j i :=
    flagged_pair_ne (a j) (b j) j (L j) (S j) (hab j) i
  have hV (j : J) (ρ : (R ⊕ (J ⊕ J)) → Fin N → ℤˣ) :
      (∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (ρ (A j i) v : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ (B j i) v : ℝ)) - q)) = V j ρ := by
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin N → ℤˣ) (v : Fin N) => (s v : ℝ)) ρ
      (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hVfull (j : J) (σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) :
      (∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (A j i) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (B j i) v.castSucc : ℝ)) - q)) =
        V j (fun r v => σ r v.castSucc) := hV j (fun r v => σ r v.castSucc)
  let δ : J → ℝ := fun u => (if L u && !S u then (if a p = a u then 1 else 0) else 0) +
    (if S u && !L u then (if a p = b u then 1 else 0) else 0)
  have ht := hC β h q hfix hb N (a p) (fun u : base => a u) (fun u : base => b u) p
    (fun u : base => (u : J)) (fun u h => (Finset.ne_of_mem_erase u.2) h.symm)
    (fun u : base => L u) (fun u : base => S u) (fun u hL hS => hab u hL hS) A B
    (fun _ j _ i => hAB j i)
  dsimp only [] at ht
  simp_rw [hVfull] at ht
  have ht' : |(N + 1 : ℝ)⁻¹ * (∑ u ∈ base,
      ν (fun σ => G u (fun r v => σ r v.castSucc) *
        (e p (fun r => σ r (Fin.last N)) * e u (fun r => σ r (Fin.last N))))) -
      (d / (N + 1 : ℝ)) * ∑ u ∈ base,
        δ u * ν (fun σ => G u (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J - 2 + 3 : ℕ) : ℝ) / 2) := by
    rw [← Finset.sum_coe_sort base, ← Finset.sum_coe_sort base]
    simpa only [G, ν, Esk, e, δ, d, base, hLp, hSp, ite_true, Bool.false_eq_true, ite_false,
      mul_assoc] using ht
  let P : J → Prop := fun u => L u = true ∧ S u = false ∧ a u = a p
  let t : Finset J := base.filter P
  have hδ (u : J) : δ u = if P u then 1 else 0 := by
    simp only [δ, P]
    cases hl : L u <;> cases hs : S u
    · simp [hs]
    · exact absurd (hLS u hs) (by simp [hl])
    · simp [hl, hs, eq_comm]
    · simp [hl, hs, eq_comm]
  have htp : t = cls.erase p := by
    ext u
    simp only [t, base, cls, P, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_assoc, and_left_comm, and_comm]
  have hpcls : p ∈ cls := by simp only [cls, Finset.mem_filter, Finset.mem_univ,
    hLp, hSp, and_self, eq_self]
  have htc : t.card = cls.card - 1 := by
    rw [htp, Finset.card_erase_of_mem hpcls]
  let Y : J → ℝ := fun u => ν (fun σ => G u (fun r v => σ r v.castSucc))
  have hY (u : J) (hu : u ∈ t) : Y u = Y u₀ := by
    have hup : u ∈ base ∧ P u := Finset.mem_filter.mp hu
    have hwT : u₀ ∈ t := by
      rw [htp]
      exact href (htp ▸ (show t.Nonempty from ⟨u, hu⟩))
    have hwp : u₀ ∈ base ∧ P u₀ := Finset.mem_filter.mp hwT
    dsimp only [Y, ν, G]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    exact MeasureTheory.integral_fresh_overlap_prod_erase_eq
      (Measure.count.tilted (Esk g))
      (fun (s : Fin (N + 1) → ℤˣ) (v : Fin N) => (s v.castSucc : ℝ))
      (N + 1 : ℝ)⁻¹ q a b L S base hup.1 hwp.1
      (hup.2.1.trans hwp.2.1.symm) (hup.2.2.1.trans hwp.2.2.1.symm)
      (fun _ => hup.2.2.2.trans hwp.2.2.2.symm)
      (fun hs => absurd (hs.symm.trans hup.2.2.1) (by simp))
  have hsum : (∑ u ∈ base, δ u * Y u) = ((cls.card - 1 : ℕ) : ℝ) * Y u₀ := by
    calc
      _ = ∑ u ∈ t, Y u := by
        dsimp only [t]
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun u _ => by rw [hδ]; split_ifs <;> simp
      _ = ∑ _u ∈ t, Y u₀ := Finset.sum_congr rfl fun u hu => hY u hu
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, htc]
  have hgroup : (d / (N + 1 : ℝ)) * ∑ u ∈ base, δ u * Y u =
      (d / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) * Y u₀ := by
    rw [hsum, mul_assoc]
  change |(N + 1 : ℝ)⁻¹ * (∑ u ∈ base,
    ν (fun σ => G u (fun r v => σ r v.castSucc) *
      (e p (fun r => σ r (Fin.last N)) * e u (fun r => σ r (Fin.last N))))) -
    (d / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) * Y u₀| ≤ _
  rw [← hgroup]
  refine ht'.trans ?_
  apply div_le_div_of_nonneg_left hC0.le (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le
    (by linarith only [Nat.cast_nonneg (α := ℝ) N])
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  exact_mod_cast (show Fintype.card J + 1 ≤ Fintype.card J - 2 + 3 by omega)

end SpinGlasses
