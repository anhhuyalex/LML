/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTSingleII

/-!
# The single-factor recurrence (1.320) and Proposition 1.10.5

The recurrence with the term II explicit and the evaluation (1.319) give Talagrand's Eq. (1.320).
Converted to `T`-moments by (1.305), it is the input of the generic Gaussian class reference
`exists_gaussian_class_moment_error`, which then proves Proposition 1.10.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Combining the recurrence, the evaluation of the term II and the replacement of the truncated
by the full product. -/
theorem single_recurrence_combine (F D' Dm II κ a1 d w m c₂ ε1 ε2 ε3 : ℝ)
    (h1 : |(1 - κ * a1) * F - w * D' - κ * d * II| ≤ ε1) (h2 : |II - m * c₂ * Dm| ≤ ε2)
    (h3 : |D' - Dm| ≤ ε3) :
    |(1 - κ * a1) * F - (w + κ * d * m * c₂) * D'| ≤ ε1 + |κ * d| * ε2 + |κ * d * m * c₂| * ε3 := by
  have e : (1 - κ * a1) * F - (w + κ * d * m * c₂) * D' =
      ((1 - κ * a1) * F - w * D' - κ * d * II) + κ * d * (II - m * c₂ * Dm) +
        κ * d * m * c₂ * (Dm - D') := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 ?_)) ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  · rw [abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)

/-- The numerical estimate for the combined error. -/
theorem single_recurrence_arith (ε1 ε2 ε3 C1 C2 C3 t m c N' Dd κ : ℝ) (ht : |t| ≤ 1)
    (hm : 0 ≤ m) (hc0 : 0 ≤ c) (hc : c ≤ 4 / 3 / N') (hN : 0 < N') (hκ : 0 < κ)
    (hε2 : 0 ≤ ε2) (hε3 : 0 ≤ ε3) (hDdκ : m ≠ 0 → Dd = N' * κ) (h1 : ε1 ≤ C1 / Dd)
    (h2 : ε2 ≤ C2 / Dd) (h3 : ε3 ≤ C3 / κ) :
    ε1 + |t| * ε2 + |t * m * c| * ε3 ≤ (C1 + C2 + 4 / 3 * m * C3) / Dd := by
  have e2 : |t| * ε2 ≤ C2 / Dd := (mul_le_of_le_one_left hε2 ht).trans h2
  have e3 : |t * m * c| * ε3 ≤ 4 / 3 * m * C3 / Dd := by
    have hmc : |t * m * c| ≤ m * c := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm, abs_of_nonneg hc0]
      calc _ ≤ 1 * m * c := by gcongr
        _ = m * c := by ring
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · calc |t * m * c| * ε3 ≤ (m * c) * ε3 := mul_le_mul_of_nonneg_right hmc hε3
        _ ≤ (m * (4 / 3 / N')) * (C3 / κ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hc hm) h3 hε3 (by positivity)
        _ = 4 / 3 * m * C3 / Dd := by
          rw [hDdκ hm0]
          field_simp
  calc ε1 + |t| * ε2 + |t * m * c| * ε3 ≤ C1 / Dd + C2 / Dd + 4 / 3 * m * C3 / Dd :=
        add_le_add (add_le_add h1 e2) e3
    _ = _ := by ring

/-- Removing two distinct elements of a finite type lowers the exponent of `(N+1)` by one. -/
theorem rpow_card_erase_erase {J : Type*} [Fintype J] [DecidableEq J] (p u₀ : J) (hu₀p : u₀ ≠ p)
    (N : ℕ) : ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) =
      ((N : ℝ) + 1) * ((N : ℝ) + 1) ^
        ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2) := by
  have hmem0 : u₀ ∈ (Finset.univ : Finset J).erase p :=
    Finset.mem_erase.mpr ⟨hu₀p, Finset.mem_univ u₀⟩
  have hcardd : (((Finset.univ : Finset J).erase p).erase u₀).card + 3 = Fintype.card J + 1 := by
    rw [Finset.card_erase_of_mem hmem0, Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
    have h2 : 2 ≤ Fintype.card J := by
      have := Finset.card_le_card (show ({p, u₀} : Finset J) ⊆ Finset.univ from
        Finset.subset_univ _)
      rw [Finset.card_pair (Ne.symm hu₀p)] at this
      simpa using this
    omega
  have hexp : ((Fintype.card J + 1 : ℕ) : ℝ) / 2 =
      1 + (((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2 := by
    rw [← hcardd]; push_cast; ring
  rw [hexp, Real.rpow_add (by positivity), Real.rpow_one]

/-- **Eq. (1.320) for the fresh-factor products.** The recurrence of the leading single factor
with the term II evaluated: the leading product is the multiplicity `|cls| - 1` times
`(q - q̂)(1 + β² A²)/(N+1)` times the product with two members of the class deleted, up to
`O(k+1)`; here `A² = α/(1-β²α)`. -/
theorem sk_cavity_fresh_single_recurrence_final_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J) (hLp : L p = true)
    (a b : J → R) (u₀ : J)
    (href : ((Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p).Nonempty →
      u₀ ∈ (Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p) :
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
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let cls : Finset J := Finset.univ.filter fun u =>
      L u = true ∧ S u = false ∧ a u = a p
    |(1 - β ^ 2 * (1 - 4 * q + 3 * qh)) * ν (fun σ => ∏ j, U j σ) -
      ((q - qh) / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) *
        ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀, U j σ)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  have hLS : ∀ j, S j = true → L j = true := fun j hs => by simp [hnp j] at hs
  have hab : ∀ j, L j = true → S j = true → a j ≠ b j := fun j _ hs => by simp [hnp j] at hs
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_cavity_fresh_single_recurrence_uniform β₀ hβ₀ L S hLS p hLp
    (hnp p) a b hab u₀ href
  obtain ⟨C₂, hC₂0, hC₂⟩ := sk_cavity_single_II_eval_uniform β₀ hβ₀ L S hnp p hLp a b u₀ href
  obtain ⟨C₃, hC₃0, hC₃⟩ := sk_fresh_prod_full_trunc_uniform β₀ hβ₀ L S a b hab
    ((Finset.univ.erase p).erase u₀)
  let clsF : Finset J := Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p
  have hCpos : 0 < C₁ + C₂ + 4 / 3 * (((clsF.card - 1 : ℕ) : ℝ)) * C₃ + 1 := by
    have : 0 ≤ 4 / 3 * (((clsF.card - 1 : ℕ) : ℝ)) * C₃ :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hC₃0.le
    linarith
  refine ⟨_, hCpos, fun β h q hfix hb N => ?_⟩
  intro Esk U ν qh α cls
  have h1 := hC₁ β h q hfix hb N
  have h2 := hC₂ β h q hfix hb N
  have h3 := hC₃ β h q hfix hb N
  have key := single_recurrence_combine _ _ _ _ (β ^ 2) (1 - 4 * q + 3 * qh) (q - qh)
    (((q - qh) / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ)) ((cls.card - 1 : ℕ) : ℝ)
    (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) _ _ _ h1 h2 h3
  have hα : 0 ≤ α ∧ α ≤ 1 := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hden : 3 / 4 ≤ 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
    linarith only [h2, hb, hβ₀]
  have hDpos : 0 < 1 - β ^ 2 * α := by linarith only [hden]
  have hc2 : 0 ≤ α / (1 - β ^ 2 * α) / (N + 1 : ℝ) ∧
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) ≤ 4 / 3 / (N + 1 : ℝ) := by
    refine ⟨div_nonneg (div_nonneg hα.1 hDpos.le) (by positivity),
      div_le_div_of_nonneg_right ?_ (by positivity)⟩
    rw [div_le_iff₀ hDpos]
    nlinarith only [hden, hα.2]
  have ht : |β ^ 2 * (q - qh)| ≤ 1 := by
    have hd1 : |q - qh| ≤ 1 := abs_sub_integral_tanh_fourth_le_one_of_fixedPoint hfix
    rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
    calc β ^ 2 * |q - qh| ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hd1 (sq_nonneg _)
      _ ≤ 1 := by linarith only [hb, hβ₀]
  have hDd : 0 < ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by positivity
  have hκ : 0 < ((N : ℝ) + 1) ^
      ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2) := by positivity
  have hDdκ : ((cls.card - 1 : ℕ) : ℝ) ≠ 0 → ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) =
      ((N : ℝ) + 1) * ((N : ℝ) + 1) ^
        ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2) := by
    intro hm
    have hne : (cls.erase p).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (by simp [cls, hLp, hnp p])]
      have : cls.card - 1 ≠ 0 := fun h0 => hm (by rw [h0, Nat.cast_zero])
      omega
    exact rpow_card_erase_erase p u₀ (Finset.ne_of_mem_erase (href hne)) N
  have hfin := single_recurrence_arith
    (C₁ / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2))
    (C₂ / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2))
    (C₃ / ((N : ℝ) + 1) ^
      ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2))
    C₁ C₂ C₃ (β ^ 2 * (q - qh)) ((cls.card - 1 : ℕ) : ℝ)
    (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) ((N : ℝ) + 1)
    (((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2))
    (((N : ℝ) + 1) ^ ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2))
    ht (Nat.cast_nonneg _) hc2.1 hc2.2 (by positivity) hκ
    (by positivity) (by positivity) hDdκ le_rfl le_rfl le_rfl
  have hbound : (C₁ + C₂ + 4 / 3 * ((cls.card - 1 : ℕ) : ℝ) * C₃) /
        ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) ≤
      (C₁ + C₂ + 4 / 3 * (((clsF.card - 1 : ℕ) : ℝ)) * C₃ + 1) /
        ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) :=
    div_le_div_of_nonneg_right (by linarith) hDd.le
  calc _ = |(1 - β ^ 2 * (1 - 4 * q + 3 * qh)) * ν (fun σ => ∏ j, U j σ) -
        (((q - qh) / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) +
          β ^ 2 * (q - qh) * ((cls.card - 1 : ℕ) : ℝ) * (α / (1 - β ^ 2 * α) / (N + 1 : ℝ))) *
        ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀, U j σ)| :=
        congrArg abs (by ring)
    _ ≤ _ := key.trans (hfin.trans hbound)

/-- **Eq. (1.320) for the actual Gibbs-mean `T`-moments.** -/
theorem sk_T_single_recurrence_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J) (hLp : L p = true)
    (a b : J → R) (u₀ : J)
    (href : ((Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p).Nonempty →
      u₀ ∈ (Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p) :
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
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let cls : Finset J := Finset.univ.filter fun u =>
      L u = true ∧ S u = false ∧ a u = a p
    |(1 - β ^ 2 * (1 - 4 * q + 3 * qh)) * νT Finset.univ -
      ((q - qh) / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) *
        νT ((Finset.univ.erase p).erase u₀)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_cavity_fresh_single_recurrence_final_uniform β₀ hβ₀ L S hnp p hLp
    a b u₀ href
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean T νT qh α cls
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

/-- **Eq. (1.320) for `T`-moments on an arbitrary finite set of factors.** -/
theorem sk_T_single_recurrence_finset_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (s : Finset J) (p : J) (hp : p ∈ s)
    (hLp : L p = true) (a b : J → R) (u₀ : J) (hu₀ : u₀ ∈ s)
    (href : ((s.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p).Nonempty →
      u₀ ∈ (s.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p) :
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
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let cls : Finset J := s.filter fun u => L u = true ∧ S u = false ∧ a u = a p
    |(1 - β ^ 2 * (1 - 4 * q + 3 * qh)) * νT s -
      ((q - qh) / (N + 1 : ℝ)) * ((cls.card - 1 : ℕ) : ℝ) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) *
        νT ((s.erase p).erase u₀)| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  let p' : s := ⟨p, hp⟩
  let u' : s := ⟨u₀, hu₀⟩
  let P : J → Prop := fun u => L u = true ∧ S u = false ∧ a u = a p
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
  obtain ⟨C, hC0, hC⟩ := sk_T_single_recurrence_uniform β₀ hβ₀
    (fun j : s => L j.val) (fun j : s => S j.val) (fun j => hnp j.val) p' hLp
    (fun j : s => a j.val) (fun j : s => b j.val) u' href'
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N E bmean T νT qh α cls
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
  have h' := hC β h q hfix hb N
  change |(1 - β ^ 2 * (1 - 4 * q + 3 * qh)) *
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, (∏ j : s, T j.val g ρ)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      ((q - qh) / (N + 1 : ℝ)) * ((cls'.card - 1 : ℕ) : ℝ) *
        (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) *
        (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, (∏ j ∈ (Finset.univ.erase p').erase u', T j.val g ρ)
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card s + 1 : ℕ) : ℝ) / 2) at h'
  simp_rw [hprod, hprod', hcard, Fintype.card_coe] at h'
  exact h'

/-- Dividing a recurrence by a denominator bounded below by `3/4`. -/
theorem div_recurrence_step (X Y D n K : ℝ) (hD : 3 / 4 ≤ D) (h : |D * X - n * Y| ≤ K) :
    |X - n / D * Y| ≤ 4 / 3 * K := by
  have hDpos : 0 < D := by linarith
  have e : X - n / D * Y = (D * X - n * Y) / D := by
    field_simp
  rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  nlinarith [abs_nonneg (D * X - n * Y)]

/-- The coefficients of Eq. (1.320) are bounded: `0 ≤ q - q̂ ≤ 1`, the denominator is at least
`3/4`, `0 ≤ α ≤ 1`, and the variance coefficient `B²` lies in `[0, 2]`. -/
theorem single_coeff_facts (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (β h q : ℝ)
    (hfix : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q)
    (hb : β ^ 2 ≤ β₀ ^ 2) :
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    0 ≤ q - qh ∧ 3 / 4 ≤ 1 - β ^ 2 * (1 - 4 * q + 3 * qh) ∧
      0 ≤ (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) ∧
      (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) ≤ 2 := by
  intro qh α
  have hα : 0 ≤ α ∧ α ≤ 1 := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hβ4 : 4 * β ^ 2 < 1 := by linarith
  have hq : 0 ≤ q := (fixedPoint_mem_Icc hfix).1
  have hqh : qh ≤ q := by
    have := qhat_le_of_fixedPoint β q h _ hfix rfl
    exact (le_of_eq (integral_tanh_pow_mul_z_sqrt_eq β q h 4)).trans this
  have hd : |q - qh| ≤ 1 := abs_sub_integral_tanh_fourth_le_one_of_fixedPoint hfix
  have hden : 3 / 4 ≤ 1 - β ^ 2 * (1 - 4 * q + 3 * qh) :=
    three_quarters_le_one_sub_beta_sq_mul hβ4 hq hqh
  have hDα : 3 / 4 ≤ 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
    linarith
  have hDαpos : 0 < 1 - β ^ 2 * α := by linarith
  have hA : 0 ≤ α / (1 - β ^ 2 * α) ∧ α / (1 - β ^ 2 * α) ≤ 4 / 3 := by
    refine ⟨div_nonneg hα.1 hDαpos.le, ?_⟩
    rw [div_le_iff₀ hDαpos]
    nlinarith
  have hdpos : 0 ≤ q - qh := by linarith
  have hd1 : q - qh ≤ 1 := (le_abs_self _).trans hd
  have hDpos : 0 < 1 - β ^ 2 * (1 - 4 * q + 3 * qh) := by linarith
  have he1 : 1 ≤ 1 + β ^ 2 * (α / (1 - β ^ 2 * α)) ∧ 1 + β ^ 2 * (α / (1 - β ^ 2 * α)) ≤ 4 / 3 := by
    constructor
    · nlinarith [mul_nonneg (sq_nonneg β) hA.1]
    · nlinarith [mul_le_mul_of_nonneg_left hA.2 (sq_nonneg β)]
  refine ⟨hdpos, hden, div_nonneg (mul_nonneg hdpos (by linarith)) hDpos.le, ?_⟩
  rw [div_le_iff₀ hDpos]
  nlinarith [mul_le_mul hd1 he1.2 (by linarith) (by norm_num : (0 : ℝ) ≤ 1)]

/-- **Proposition 1.10.5 (Eq. (1.314)), enumerated form.** Every single factor class contributes
the Gaussian moments of variance `B²/(N+1)` of its size, with
`B² = (q - q̂)(1 + β² A²)/(1 - β²(1 - 4q + 3q̂))`, `A² = α/(1 - β²α)`, times the actual moment of
the non-single factors, up to `O(k+1)`. -/
theorem sk_T_single_gaussian_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (a b : J → R) (s : Finset J) :
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
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    |νT s - (∏ k : R, ∫ x : ℝ,
        (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) * x) ^
          (s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card ∂gaussianReal 0 1) *
      νT (s.filter fun j => ¬(L j = true ∧ S j = false))| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  let P : J → Prop := fun j => L j = true ∧ S j = false
  let valid : ℝ × ℝ × ℝ → Prop := fun θ =>
    (∫ t : ℝ, Real.tanh (θ.1 * Real.sqrt θ.2.2 * t + θ.2.1) ^ 2 ∂gaussianReal 0 1 = θ.2.2) ∧
      θ.1 ^ 2 ≤ β₀ ^ 2
  let qhf : ℝ × ℝ × ℝ → ℝ := fun θ =>
    ∫ t : ℝ, Real.tanh (θ.1 * t * Real.sqrt θ.2.2 + θ.2.1) ^ 4 ∂gaussianReal 0 1
  let cf : ℝ × ℝ × ℝ → ℝ := fun θ =>
    (θ.2.2 - qhf θ) * (1 + θ.1 ^ 2 * ((qhf θ - 2 * θ.2.2 + 1) /
      (1 - θ.1 ^ 2 * (qhf θ - 2 * θ.2.2 + 1)))) /
    (1 - θ.1 ^ 2 * (1 - 4 * θ.2.2 + 3 * qhf θ))
  let F : ℝ × ℝ × ℝ → ℕ → Finset J → ℝ := fun θ N s =>
    ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ j ∈ s,
      (((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted
            (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * θ.1 *
              (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
              θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ)))
          else ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted
            (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * θ.1 *
              (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
              θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ)))) *
        (if S j then (ρ (b j) i : ℝ) - ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted
            (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * θ.1 *
              (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
              θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ)))
          else ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted
            (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * θ.1 *
              (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
              θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ))))) -
        (if L j || S j then 0 else θ.2.2))
      ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * θ.1 *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hF : ∀ (s' : Finset J) (p u : J), p ∈ s' → P p → u ∈ s' →
      (((s'.filter fun j => P j ∧ a j = a p).erase p).Nonempty →
        u ∈ (s'.filter fun j => P j ∧ a j = a p).erase p) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ θ, valid θ → ∀ N : ℕ,
        |F θ N s' - ((((s'.filter fun j => P j ∧ a j = a p).card - 1 : ℕ) : ℝ) * cf θ /
            (N + 1 : ℝ)) * F θ N ((s'.erase p).erase u)| ≤
          K / (N + 1 : ℝ) ^ (((s'.card + 1 : ℕ) : ℝ) / 2) := by
    intro s' p u hps hPp hus href
    have hcls : (s'.filter fun j => P j ∧ a j = a p) =
        (s'.filter fun u => L u = true ∧ S u = false ∧ a u = a p) :=
      Finset.filter_congr fun j _ => by simp [P, and_assoc]
    rw [hcls] at href ⊢
    obtain ⟨C, hC0, hC⟩ := sk_T_single_recurrence_finset_uniform β₀ hβ₀ L S hnp s' p hps hPp.1
      a b u hus href
    refine ⟨4 / 3 * C, by positivity, ?_⟩
    rintro ⟨β, h, q⟩ ⟨hfix, hb⟩ N
    have h1 := hC β h q hfix hb N
    obtain ⟨-, hD, -, -⟩ := single_coeff_facts β₀ hβ₀ β h q hfix hb
    have h2 := div_recurrence_step _ _ _ _ _ hD h1
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_))
    · congr 2
      ring
    · ring
  have hcf : ∀ θ, valid θ → 0 ≤ cf θ ∧ |cf θ| ≤ 2 := by
    rintro ⟨β, h, q⟩ ⟨hfix, hb⟩
    obtain ⟨-, -, h0, h2⟩ := single_coeff_facts β₀ hβ₀ β h q hfix hb
    exact ⟨h0, by rw [abs_of_nonneg h0]; exact h2⟩
  obtain ⟨K, hK0, hK⟩ := exists_gaussian_class_moment_error (J := J) (ι := R) P a valid F cf 2
    (fun θ hθ => (hcf θ hθ).1) (fun θ hθ => (hcf θ hθ).2) hF s
  exact ⟨K, hK0, fun β h q hfix hb N => hK (β, h, q) ⟨hfix, hb⟩ N⟩

end SpinGlasses
