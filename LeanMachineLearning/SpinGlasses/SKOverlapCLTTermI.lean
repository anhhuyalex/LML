/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrderFinite
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTFreshContractions

/-!
# Quantitative fresh-factor contractions for term I

Combine the exact fresh-replica contraction with Eq. (1.298), both for the spin-weighted
product and for the unweighted product. This gives each summand of Talagrand's Eq. (1.312)
with its correct error; its outer factor `1/(N+1)` supplies the final extra inverse power.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The individual contractions in term I of Eq. (1.312).** A product over `s`
truncated overlap factors contracts with two fresh last-site factors up to
`C/(N+1)^((card s+1)/2)`. The coefficient vanishes for the single and global classes,
and is `1-2q+qhat` for a matching pair. The constant precedes all model parameters and
labels, including the temperature and field. -/
theorem sk_cavity_fresh_factor_product_compare (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J κ : Type*} [Fintype R] [Fintype J] [DecidableEq R]
    (s : Finset κ) {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (x y z w : R), x ≠ y →
      ∀ (p u : J), p ≠ u → ∀ (L S : Bool), (L = true → S = true → z ≠ w) →
      ∀ (A B : ∀ j, ι j → R ⊕ (J ⊕ J)),
      (∀ j ∈ s, ∀ i, A j i ≠ B j i) →
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let G : ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun ρ =>
      ∏ j ∈ s, ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (ρ (A j i) v : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ (B j i) v : ℝ)) - q)
    let e0 : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      ((ε (.inl x) : ℝ) - (ε (.inr (.inl p)) : ℝ)) *
        ((ε (.inl y) : ℝ) - (ε (.inr (.inr p)) : ℝ))
    let eu : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      (if L then (ε (.inl z) : ℝ) - (ε (.inr (.inl u)) : ℝ)
        else (ε (.inr (.inl u)) : ℝ)) *
      (if S then (ε (.inl w) : ℝ) - (ε (.inr (.inr u)) : ℝ)
        else (ε (.inr (.inr u)) : ℝ))
    let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    let δ : ℝ := if L && S then (if x = z ∧ y = w then 1 else 0) +
      (if x = w ∧ y = z then 1 else 0) else 0
    |ν (fun σ => G (fun r v => σ r v.castSucc) *
        (e0 (fun r => σ r (Fin.last N)) * eu (fun r => σ r (Fin.last N)))) -
      α * δ * ν (fun σ => G (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨C₀, hC₀0, hC₀⟩ := sk_cavity_lincomb_first_order_finset β₀ hβ₀
    (R := R ⊕ (J ⊕ J)) s 16 c
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_cavity_lincomb_first_order_finset β₀ hβ₀
    (R := R ⊕ (J ⊕ J)) s 1 c
  refine ⟨C₀ + 2 * C₁, by positivity, ?_⟩
  intro β h q hfix hb N x y z w hxy p u hpu L S hzw A B hAB Esk G e0 eu ν α δ
  let B₀ : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
    (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs N,
          g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
  let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
      (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
    Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
      (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
    Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B₀ g' a
  let ν₀ : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ, f σ
      ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  let F : ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ :=
    fun σ => G (fun r v => σ r v.castSucc)
  let W : ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ :=
    fun σ => e0 (fun r => σ r (Fin.last N)) * eu (fun r => σ r (Fin.last N))
  let O : ℝ := ∫ g', ∫ ρ : (R ⊕ (J ⊕ J)) → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hfixz : ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 2 ∂gaussianReal 0 1 = q := by
    rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
  have hside (b : Bool) (a c : ℤˣ) : |if b then (a : ℝ) - (c : ℝ) else (c : ℝ)| ≤ 2 := by
    cases b
    · norm_num [abs_units_cast_eq_one]
    · exact (abs_sub _ _).trans (by norm_num [abs_units_cast_eq_one])
  have hW (σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) : |W σ| ≤ 16 := by
    have he0 : |e0 (fun r => σ r (Fin.last N))| ≤ 4 := by
      dsimp [e0]
      rw [abs_mul]
      exact (mul_le_mul
        (hside true (σ (.inl x) (Fin.last N)) (σ (.inr (.inl p)) (Fin.last N)))
        (hside true (σ (.inl y) (Fin.last N)) (σ (.inr (.inr p)) (Fin.last N)))
        (abs_nonneg _) (by norm_num)).trans (by norm_num : (2 : ℝ) * 2 ≤ 4)
    have heu : |eu (fun r => σ r (Fin.last N))| ≤ 4 := by
      dsimp [eu]
      rw [abs_mul]
      exact (mul_le_mul (hside L _ _) (hside S _ _) (abs_nonneg _) (by norm_num)).trans
        (by norm_num : (2 : ℝ) * 2 ≤ 4)
    simpa only [W, abs_mul] using
      (mul_le_mul he0 heu (abs_nonneg _) (by norm_num)).trans (by norm_num : (4 : ℝ) * 4 ≤ 16)
  have ht₀ : |ν (fun σ => W σ * F σ) - ν₀ (fun σ => W σ * F σ)| ≤
      C₀ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) :=
    hC₀ β h q hfix hb N A B hAB W hW
  have ht₁ : |ν F - ν₀ F| ≤
      C₁ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
    simpa only [one_mul] using hC₁ β h q hfix hb N A B hAB (fun _ => 1)
      (fun _ => by norm_num)
  have hcomm : (fun σ => W σ * F σ) = (fun σ => F σ * W σ) :=
    funext fun _ => mul_comm _ _
  rw [hcomm] at ht₀
  have hz : ν₀ F = O := by
    have hh := sk_cavity_decoupled_endpoint_replicas N β q h
      (∅ : Finset (R ⊕ (J ⊕ J))) G
    simpa only [Finset.prod_empty, Finset.card_empty, pow_zero, integral_const,
      probReal_univ, one_smul, mul_one, one_mul] using hh
  have hc : ν₀ (fun σ => F σ * W σ) = α * δ * O :=
    sk_cavity_decoupled_fresh_factor N β q h hfixz x y z w hxy p u hpu L S hzw G
  rw [hz] at ht₁
  rw [hc] at ht₀
  have ht₁' : |O - ν F| ≤
      C₁ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
    rw [abs_sub_comm]
    exact ht₁
  have hα : |α| ≤ 1 := by
    have hh := probability_tanh_fourth_sub_two_add_one_mem_Icc
      (P := gaussianReal 0 1) (fun t : ℝ => β * t * Real.sqrt q + h) (by fun_prop)
    rw [hfixz] at hh
    exact abs_le.mpr ⟨by linarith only [hh.1], hh.2⟩
  have hδ : |δ| ≤ 2 := by
    dsimp [δ]
    split_ifs <;> norm_num
  have hαδ : |α * δ| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hα hδ (abs_nonneg _) zero_le_one).trans (by norm_num : (1 : ℝ) * 2 ≤ 2)
  change |ν (fun σ => F σ * W σ) - α * δ * ν F| ≤ _
  calc
    _ ≤ |ν (fun σ => F σ * W σ) - α * δ * O| + |α * δ * O - α * δ * ν F| :=
      abs_sub_le _ _ _
    _ = |ν (fun σ => F σ * W σ) - α * δ * O| + |α * δ| * |O - ν F| := by
      rw [← mul_sub, abs_mul]
    _ ≤ C₀ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) +
        2 * (C₁ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2)) :=
      add_le_add ht₀ (mul_le_mul hαδ ht₁'
        (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- **The finite pairing sum for term I in Eq. (1.312).** Each product has `k`
remaining overlap factors. After multiplying by the outer inverse size, the total error
is `C/(N+1)^((k+3)/2)`, uniformly over the temperature range. Specializing to the products
with the leading and contracted factors deleted gives the source error order. -/
theorem sk_cavity_fresh_term_sum_compare (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J U κ : Type*} [Fintype R] [Fintype J] [Fintype U] [DecidableEq R]
    (s : U → Finset κ) (k : ℕ) (hcard : ∀ i, (s i).card = k)
    {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (x y : R) (z w : U → R), x ≠ y →
      ∀ (p : J) (v : U → J), (∀ i, p ≠ v i) → ∀ (L S : U → Bool),
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
      ((ε (.inl x) : ℝ) - (ε (.inr (.inl p)) : ℝ)) *
        ((ε (.inl y) : ℝ) - (ε (.inr (.inr p)) : ℝ))
    let eu : U → (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun i ε =>
      (if L i then (ε (.inl (z i)) : ℝ) - (ε (.inr (.inl (v i))) : ℝ)
        else (ε (.inr (.inl (v i))) : ℝ)) *
      (if S i then (ε (.inl (w i)) : ℝ) - (ε (.inr (.inr (v i))) : ℝ)
        else (ε (.inr (.inr (v i))) : ℝ))
    let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    let δ : U → ℝ := fun i => if L i && S i then
      (if x = z i ∧ y = w i then 1 else 0) +
      (if x = w i ∧ y = z i then 1 else 0) else 0
    |(N + 1 : ℝ)⁻¹ * (∑ i : U, ν (fun σ => G i (fun r v => σ r v.castSucc) *
        (e0 (fun r => σ r (Fin.last N)) * eu i (fun r => σ r (Fin.last N))))) -
      (α / (N + 1 : ℝ)) * ∑ i : U, δ i * ν (fun σ => G i (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 3 : ℕ) : ℝ) / 2) := by
  classical
  choose C hC0 hC using fun i : U => sk_cavity_fresh_factor_product_compare β₀ hβ₀
    (R := R) (J := J) (s i) c
  refine ⟨(∑ i : U, C i) + 1, by
    linarith only [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hC0 i).le)], ?_⟩
  intro β h q hfix hb N x y z w hxy p v hpv L S hzw A B hAB Esk G e0 eu ν α δ
  let X : U → ℝ := fun i => ν (fun σ => G i (fun r v => σ r v.castSucc) *
    (e0 (fun r => σ r (Fin.last N)) * eu i (fun r => σ r (Fin.last N))))
  let Y : U → ℝ := fun i => ν (fun σ => G i (fun r v => σ r v.castSucc))
  have ht (i : U) : |X i - α * δ i * Y i| ≤
      C i / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
    simpa only [hcard i] using hC i β h q hfix hb N x y (z i) (w i) hxy
      p (v i) (hpv i) (L i) (S i) (hzw i) A B (hAB i)
  change |(N + 1 : ℝ)⁻¹ * (∑ i, X i) - (α / (N + 1 : ℝ)) * ∑ i, δ i * Y i| ≤ _
  have he : (N + 1 : ℝ)⁻¹ * (∑ i, X i) - (α / (N + 1 : ℝ)) * ∑ i, δ i * Y i =
      (N + 1 : ℝ)⁻¹ * ∑ i, (X i - α * δ i * Y i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hrpow : ((N : ℝ) + 1) ^ (((k + 3 : ℕ) : ℝ) / 2) =
      ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
    rw [show (((k + 3 : ℕ) : ℝ) / 2) = 1 + (((k + 1 : ℕ) : ℝ) / 2) by push_cast; ring,
      Real.rpow_add (by positivity), Real.rpow_one]
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N + 1 : ℝ)⁻¹)]
  calc
    _ ≤ (N + 1 : ℝ)⁻¹ * ∑ i : U, |X i - α * δ i * Y i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (N + 1 : ℝ)⁻¹ * ∑ i : U,
        C i / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ht i) (by positivity)
    _ = (∑ i : U, C i) / ((N : ℝ) + 1) ^ (((k + 3 : ℕ) : ℝ) / 2) := by
      rw [← Finset.sum_div, hrpow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end SpinGlasses
