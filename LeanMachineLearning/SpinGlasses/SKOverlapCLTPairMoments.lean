/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTPairRecurrence
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTFreshMoments

/-!
# Pair-factor recurrence for the actual Gibbs-mean T-moments

Transport the deterministic fresh-factor recurrence back to the disorder-dependent
T-basis moments. No replica labels or Gibbs means are assumed to be independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **Eq. (1.313) for the mixed T-moments themselves.** The mean in each T-factor
is the actual Gibbs mean at the sampled disorder. The error constant is chosen before
the model parameters throughout the high-temperature range and before the site count. -/
theorem sk_T_pair_recurrence_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
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
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q)
    let νT : Finset J → ℝ := fun s => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    let cls : Finset J := Finset.univ.filter fun u =>
      L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p
    |(1 - β ^ 2 * α) * νT Finset.univ -
      (α / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) *
        νT ((Finset.univ.erase p).erase u₀)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    sk_cavity_fresh_pair_recurrence_uniform β₀ hβ₀ L S p hLp hSp a b hord u₀ href
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N E bmean T νT α cls
  let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    ((N + 1 : ℝ)⁻¹ * ∑ i,
      (if L j then (σ (.inl (a j)) i : ℝ) - (σ (.inr (.inl j)) i : ℝ)
        else (σ (.inr (.inl j)) i : ℝ)) *
      (if S j then (σ (.inl (b j)) i : ℝ) - (σ (.inr (.inr j)) i : ℝ)
        else (σ (.inr (.inr j)) i : ℝ))) - (if L j || S j then 0 else q)
  let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
    ∫ g, ∫ σ, F σ
      ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have havg (s : Finset J) : νT s = ν (fun σ => ∏ j ∈ s, U j σ) :=
    sk_flagged_T_moment_eq_fresh N β h q a b L S s
  rw [havg Finset.univ, havg ((Finset.univ.erase p).erase u₀)]
  exact hC β h q hfix hb N

/-- The uniform pair recurrence on an arbitrary finite factor set. The proof applies
the full-family theorem to the factor subtype; erased products and class multiplicities
are transported by the standard finite-set map API. The ambient factor type may be infinite. -/
theorem sk_T_pair_recurrence_finset_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [LinearOrder R] [DecidableEq J]
    (s : Finset J) (L S : J → Bool) (p : J) (hp : p ∈ s) (hLp : L p = true) (hSp : S p = true)
    (a b : J → R) (hord : ∀ j ∈ s, L j = true → S j = true → a j < b j)
    (u₀ : J) (hu₀ : u₀ ∈ s)
    (href : ((s.filter fun u =>
        L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).erase p).Nonempty →
      u₀ ∈ (s.filter fun u =>
        L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).erase p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q)
    let νT : Finset J → ℝ := fun s => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    let cls : Finset J := s.filter fun u =>
      L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p
    |(1 - β ^ 2 * α) * νT s -
      (α / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) *
        νT ((s.erase p).erase u₀)| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  let p' : s := ⟨p, hp⟩
  let u' : s := ⟨u₀, hu₀⟩
  let P : J → Prop := fun u =>
    L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p
  let cls' : Finset s := Finset.univ.filter fun u => P u.val
  let incl : s ↪ J := Function.Embedding.subtype _
  have hmap : cls'.map incl = s.filter P := by
    calc
      _ = (Finset.univ.map incl).filter P :=
        (Finset.filter_map (f := incl) (s := Finset.univ) (p := P)).symm
      _ = _ := by rw [Finset.univ_eq_attach, Finset.attach_map_val]
  have hmaperase : (cls'.erase p').map incl = (s.filter P).erase p := by
    rw [Finset.map_erase, hmap]
    rfl
  have href' : (cls'.erase p').Nonempty → u' ∈ cls'.erase p' := by
    intro hne
    have hne' : ((s.filter P).erase p).Nonempty := by
      rw [← hmaperase]
      exact Finset.map_nonempty.mpr hne
    have hu := href hne'
    rw [← hmaperase] at hu
    obtain ⟨v, hv, he⟩ := Finset.mem_map.mp hu
    have hvu : v = u' := Subtype.ext he
    exact hvu ▸ hv
  have hcard : cls'.card = (s.filter P).card := by
    rw [← hmap, Finset.card_map]
  obtain ⟨C, hC0, hC⟩ := sk_T_pair_recurrence_uniform β₀ hβ₀
    (fun j : s => L j.val) (fun j : s => S j.val) p' hLp hSp
    (fun j : s => a j.val) (fun j : s => b j.val)
    (fun j => hord j.val j.property) u' href'
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N E bmean T νT α cls
  have hprod (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ) :
      (∏ j : s, T j.val g ρ) = ∏ j ∈ s, T j g ρ :=
    Finset.prod_coe_sort s (fun j => T j g ρ)
  have hprod' (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ) :
      (∏ j ∈ (Finset.univ.erase p').erase u', T j.val g ρ) =
        ∏ j ∈ (s.erase p).erase u₀, T j g ρ := by
    calc
      _ = ∏ j ∈ ((Finset.univ.erase p').erase u').map incl, T j g ρ :=
        (Finset.prod_map _ incl (fun j => T j g ρ)).symm
      _ = _ := by
        rw [Finset.map_erase, Finset.map_erase, Finset.univ_eq_attach,
          Finset.attach_map_val]
        rfl
  have h := hC β h q hfix hb N
  change |(1 - β ^ 2 * α) *
      (∫ g, ∫ ρ, (∏ j : s, T j.val g ρ)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (α / (N + 1 : ℝ)) * ((cls'.card - 1 : ℕ) : ℝ) *
        (∫ g, ∫ ρ, (∏ j ∈ (Finset.univ.erase p').erase u', T j.val g ρ)
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card s + 1 : ℕ) : ℝ) / 2) at h
  simp_rw [hprod, hprod', hcard, Fintype.card_coe] at h
  exact h

end SpinGlasses
