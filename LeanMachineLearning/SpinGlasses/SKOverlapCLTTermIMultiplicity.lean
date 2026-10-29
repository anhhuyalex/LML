/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTTermI
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas

/-!
# Multiplicity form of term I (Talagrand, Eq. (1.312))

Represent all three source factor classes by Boolean flags. The finite pairing sum
then groups into one common moment times the number of matching pairs minus one.
Fresh-pair integration identifies the deleted moments, including vanishing factors.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

private theorem flagged_pair_ne {R J : Type*} (a b : R) (j : J) (L S : Bool)
    (hab : L = true → S = true → a ≠ b) (i : Bool × Bool) :
    (if L && i.1 then (Sum.inl a : R ⊕ (J ⊕ J)) else .inr (.inl j)) ≠
      (if S && i.2 then .inl b else .inr (.inr j)) := by
  rcases i with ⟨i, k⟩
  cases L <;> cases S <;> cases i <;> cases k <;> simp_all

private theorem ordered_class_indicator {R : Type*} [LinearOrder R]
    (x y a b : R) (L S : Bool) (hxy : x < y)
    (hab : L = true → S = true → a < b) :
    (if L && S then (if x = a ∧ y = b then (1 : ℝ) else 0) +
      (if x = b ∧ y = a then 1 else 0) else 0) =
      if L = true ∧ S = true ∧ a = x ∧ b = y then 1 else 0 := by
  cases L <;> cases S
  · simp
  · simp
  · simp
  · simp only [Bool.and_self, ↓reduceIte, true_and]
    have hr : ¬(x = b ∧ y = a) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hxy (hab rfl rfl)
    simp only [hr, ↓reduceIte, add_zero]
    simp only [eq_comm]

/-- **Eq. (1.312), with the actual multiplicity of the leading ordered pair.**
The pair, single and global factor classes are encoded by fixed Boolean flags. The
reference deleted factor is chosen from the matching class when that class is nonempty;
if no other matching pair exists the coefficient is zero and the reference is arbitrary.
The constant is uniform over the temperature range and chosen before every site count
and original replica label. -/
theorem sk_cavity_term_I_multiplicity (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [LinearOrder R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (p : J) (hLp : L p = true) (hSp : S p = true) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (a b : J → R),
      (∀ j, L j = true → S j = true → a j < b j) →
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
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    let cls : Finset J := Finset.univ.filter fun u =>
      L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p
    ∀ (u₀ : J), ((cls.erase p).Nonempty → u₀ ∈ cls.erase p) →
    |(N + 1 : ℝ)⁻¹ * (∑ u ∈ Finset.univ.erase p,
        ν (fun σ => G u (fun r v => σ r v.castSucc) *
          (e p (fun r => σ r (Fin.last N)) * e u (fun r => σ r (Fin.last N))))) -
      (α / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) *
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
  obtain ⟨C, hC0, hC⟩ := sk_cavity_fresh_term_sum_compare β₀ hβ₀
    (R := R) (J := J) (fun u : base => base.erase (u : J))
    (Fintype.card J - 2) hcard c
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N a b hord Esk V G e ν α cls u₀ href
  let A : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let B : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  have hAB (j : J) (i : Bool × Bool) : A j i ≠ B j i :=
    flagged_pair_ne (a j) (b j) j (L j) (S j)
      (fun hL hS => ne_of_lt (hord j hL hS)) i
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
  let δ : J → ℝ := fun u => if L u && S u then
    (if a p = a u ∧ b p = b u then 1 else 0) +
    (if a p = b u ∧ b p = a u then 1 else 0) else 0
  have ht := hC β h q hfix hb N (a p) (b p)
    (fun u : base => a u) (fun u : base => b u) (ne_of_lt (hord p hLp hSp))
    p (fun u : base => (u : J)) (fun u h => (Finset.ne_of_mem_erase u.2) h.symm)
    (fun u : base => L u) (fun u : base => S u)
    (fun u hL hS => ne_of_lt (hord u hL hS)) A B (fun _ j _ i => hAB j i)
  dsimp only [] at ht
  simp_rw [hVfull] at ht
  have ht' : |(N + 1 : ℝ)⁻¹ * (∑ u ∈ base,
      ν (fun σ => G u (fun r v => σ r v.castSucc) *
        (e p (fun r => σ r (Fin.last N)) * e u (fun r => σ r (Fin.last N))))) -
      (α / (N + 1 : ℝ)) * ∑ u ∈ base,
        δ u * ν (fun σ => G u (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J - 2 + 3 : ℕ) : ℝ) / 2) := by
    rw [← Finset.sum_coe_sort base, ← Finset.sum_coe_sort base]
    simpa only [G, ν, Esk, e, δ, α, base, hLp, hSp, ite_true,
      mul_assoc] using ht
  let P : J → Prop := fun u => L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p
  let t : Finset J := base.filter P
  have hδ (u : J) : δ u = if P u then 1 else 0 :=
    ordered_class_indicator (a p) (b p) (a u) (b u) (L u) (S u)
      (hord p hLp hSp) (hord u)
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
      (fun _ => hup.2.2.2.1.trans hwp.2.2.2.1.symm)
      (fun _ => hup.2.2.2.2.trans hwp.2.2.2.2.symm)
  have hsum : (∑ u ∈ base, δ u * Y u) = ((cls.card - 1 : ℕ) : ℝ) * Y u₀ := by
    calc
      _ = ∑ u ∈ t, Y u := by
        dsimp only [t]
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun u _ => by rw [hδ]; split_ifs <;> simp
      _ = ∑ _u ∈ t, Y u₀ := Finset.sum_congr rfl fun u hu => hY u hu
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, htc]
  have hgroup : (α / (N + 1 : ℝ)) * ∑ u ∈ base, δ u * Y u =
      (α / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) * Y u₀ := by
    rw [hsum, mul_assoc]
  change |(N + 1 : ℝ)⁻¹ * (∑ u ∈ base,
    ν (fun σ => G u (fun r v => σ r v.castSucc) *
      (e p (fun r => σ r (Fin.last N)) * e u (fun r => σ r (Fin.last N))))) -
    (α / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) * Y u₀| ≤ _
  rw [← hgroup]
  refine ht'.trans ?_
  apply div_le_div_of_nonneg_left hC0.le (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le
    (by linarith only [Nat.cast_nonneg (α := ℝ) N])
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  exact_mod_cast (show Fintype.card J + 1 ≤ Fintype.card J - 2 + 3 by omega)

end SpinGlasses
