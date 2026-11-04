/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTMultiIndex
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import Mathlib.Data.Sum.Order

/-!
# Conditional Gibbs moment fluctuations

Talagrand (1.292)--(1.294) compares a normalized conditional Gibbs moment with a
nonrandom Gaussian moment. Its square uses two disjoint replica families.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real ENNReal Nat

universe u

namespace SpinGlasses

/-- Every conditional pair/single mixed moment belongs to every `L^p` for finite
disorder measures. There is no temperature or fixed-point assumption. -/
theorem sk_T_multiindex_memLp (N : ℕ) (β h : ℝ)
    {R : Type u} [Fintype R] (kP : R × R → ℕ) (kS : R → ℕ)
    (p : ℝ≥0∞) {μ : Measure (FinPairs (N + 1) → ℝ)} [IsFiniteMeasure μ] :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let TP := fun (p : R × R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ p.1 i : ℝ) - bmean g i) *
        ((ρ p.2 i : ℝ) - bmean g i)
    let TS := fun (r : R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ r i : ℝ) - bmean g i) * bmean g i
    let H := fun g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (∏ r, TP r g ρ ^ kP r) * ∏ r, TS r g ρ ^ kS r
    MemLp (fun g => ∫ ρ : R → Fin (N + 1) → ℤˣ, H g ρ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) p μ := by
  intro E bmean TP TS H
  let K := (R × R) ⊕ R
  let m : K → ℕ := Sum.elim kP kS
  let J := Σ κ : K, Fin (m κ)
  let s : J → Bool := fun j => Sum.elim (fun _ => true) (fun _ => false) j.1
  let a : J → R := fun j => Sum.elim Prod.fst id j.1
  let b : J → R := fun j => Sum.elim Prod.snd id j.1
  let T := fun (j : J) g (ρ : R → Fin (N + 1) → ℤˣ) =>
    ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ (a j) i : ℝ) - bmean g i) *
      (if s j then (ρ (b j) i : ℝ) - bmean g i else bmean g i))
  have hprod (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ) :
      (∏ j : J, T j g ρ) = H g ρ := by
    let F : K → ℝ := Sum.elim (fun r => TP r g ρ) (fun r => TS r g ρ)
    have hpow : (∏ j : J, F j.1) = ∏ κ, F κ ^ m κ := by
      rw [Fintype.prod_sigma]
      simp
    have ho (j : J) : T j g ρ = F j.1 := by
      rcases j with ⟨r | r, n⟩ <;> simp [T, F, s, a, b, TP, TS]
    simp_rw [ho]
    rw [hpow, Fintype.prod_sum_type]
    rfl
  have hg := sk_live_T_family_meas_bound N β h 0 (R := R) (K := J) (M := Unit)
    (fun _ _ => true) (fun j _ => s j) (fun j _ => a j) (fun j _ => b j) (fun _ _ => 1)
  have hg' : (∀ ρ : R → Fin (N + 1) → ℤˣ, Measurable fun g => ∏ j : J, T j g ρ) ∧
      ∃ B : ℝ, ∀ g (ρ : R → Fin (N + 1) → ℤˣ), |∏ j : J, T j g ρ| ≤ B := by
    simpa only [Fintype.sum_unique, one_mul, Bool.true_or, ite_true, sub_zero] using hg
  simp_rw [hprod] at hg'
  obtain ⟨hH, B, hB⟩ := hg'
  have hE : ∀ σ, Measurable fun g : FinPairs (N + 1) → ℝ => E g σ := fun σ => by
    dsimp only [E]
    fun_prop
  exact memLp_integral_pi_count_tilted_of_bound p E (fun σ => (hE σ).aemeasurable)
    H (fun ρ => (hH ρ).aemeasurable) B (ae_of_all _ hB)

/-- First two disorder moments of the normalized conditional Gibbs moment, as used
in Talagrand (1.293). The second estimate uses disjoint copies, not doubled powers. -/
theorem sk_T_gibbs_moment_first_two_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type u} [Fintype R] [LinearOrder R] [Nonempty R]
    (kP : R × R → ℕ) (kS : R → ℕ) (hord : ∀ p, 0 < kP p → p.1 < p.2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let TP := fun (p : R × R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ p.1 i : ℝ) - bmean g i) *
        ((ρ p.2 i : ℝ) - bmean g i)
    let TS := fun (r : R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ r i : ℝ) - bmean g i) * bmean g i
    let k : ℕ := (∑ p, kP p) + ∑ r, kS r
    let V := fun g => ((N : ℝ) + 1) ^ ((k : ℝ) / 2) *
      ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (∏ p, TP p g ρ ^ kP p) * (∏ r, TS r g ρ ^ kS r)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let A2 : ℝ := α / (1 - β ^ 2 * α)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * A2) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh))
    let G : ℝ := (∏ p, ∫ x : ℝ, (Real.sqrt A2 * x) ^ kP p ∂gaussianReal 0 1) *
      (∏ r, ∫ x : ℝ, (Real.sqrt B2 * x) ^ kS r ∂gaussianReal 0 1)
    let P := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
    |(∫ g, V g ∂P) - G| ≤ C₁ / Real.sqrt ((N : ℝ) + 1) ∧
      |(∫ g, V g ^ 2 ∂P) - G ^ 2| ≤ C₂ / Real.sqrt ((N : ℝ) + 1) := by
  let blockOrder : LinearOrder (R ⊕ R) :=
    LinearOrder.lift' (toLex : (R ⊕ R) ≃ (R ⊕ₗ R)) toLex.injective
  let kP₂ : (R ⊕ R) × (R ⊕ R) → ℕ := fun p =>
    match p.1, p.2 with
    | .inl r, .inl s => kP (r, s)
    | .inr r, .inr s => kP (r, s)
    | _, _ => 0
  let kS₂ : R ⊕ R → ℕ := Sum.elim kS kS
  have ho₂ : ∀ p, 0 < kP₂ p → @LT.lt (R ⊕ R) blockOrder.toLT p.1 p.2 := by
    rintro ⟨r | r, t | t⟩
    · change 0 < kP (r, t) → toLex (.inl r : R ⊕ R) < toLex (.inl t)
      simpa only [Sum.Lex.inl_lt_inl_iff] using hord (r, t)
    · simp [kP₂]
    · simp [kP₂]
    · change 0 < kP (r, t) → toLex (.inr r : R ⊕ R) < toLex (.inr t)
      simpa only [Sum.Lex.inr_lt_inr_iff] using hord (r, t)
  have hk₂ : (∑ p, kP₂ p) + (∑ r, kS₂ r) =
      2 * ((∑ p, kP p) + ∑ r, kS r) := by
    simp [kP₂, kS₂, Fintype.sum_prod_type, Fintype.sum_sum_type]
    omega
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    sk_T_multiindex_gaussian_moment_normalized_uniform β₀ hβ₀ kP kS 0 hord
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    @sk_T_multiindex_gaussian_moment_normalized_uniform β₀ hβ₀ (R ⊕ R)
      inferInstance blockOrder inferInstance kP₂ kS₂ 0 ho₂
  refine ⟨C₁, hC₁0, C₂, hC₂0, fun β h q hfix hb N => ?_⟩
  intro E bmean TP TS k V qh α A2 B2 G P
  let H := fun g (ρ : R → Fin (N + 1) → ℤˣ) =>
    (∏ p, TP p g ρ ^ kP p) * ∏ r, TS r g ρ ^ kS r
  let TP₂ := fun (p : (R ⊕ R) × (R ⊕ R)) g (ρ : R ⊕ R → Fin (N + 1) → ℤˣ) =>
    (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ p.1 i : ℝ) - bmean g i) *
      ((ρ p.2 i : ℝ) - bmean g i)
  let TS₂ := fun (r : R ⊕ R) g (ρ : R ⊕ R → Fin (N + 1) → ℤˣ) =>
    (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ r i : ℝ) - bmean g i) * bmean g i
  let H₂ := fun g (ρ : R ⊕ R → Fin (N + 1) → ℤˣ) =>
    (∏ p, TP₂ p g ρ ^ kP₂ p) * ∏ r, TS₂ r g ρ ^ kS₂ r
  have hH₂ (g : FinPairs (N + 1) → ℝ) (ρ : R ⊕ R → Fin (N + 1) → ℤˣ) :
      H₂ g ρ = H g (fun r => ρ (.inl r)) * H g (fun r => ρ (.inr r)) := by
    simp [H₂, H, TP₂, TS₂, TP, TS, kP₂, kS₂,
      Fintype.prod_prod_type, Fintype.prod_sum_type]
    ring
  have hsquare (g : FinPairs (N + 1) → ℝ) :
      (∫ ρ : R ⊕ R → Fin (N + 1) → ℤˣ, H₂ g ρ
        ∂(Measure.pi fun _ : R ⊕ R => Measure.count.tilted (E g))) =
        (∫ ρ : R → Fin (N + 1) → ℤˣ, H g ρ
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) ^ 2 := by
    simp_rw [hH₂]
    simpa only [pow_two] using integral_pi_sum_mul (Measure.count.tilted (E g))
      (H g) (H g) Integrable.of_finite.aestronglyMeasurable
      Integrable.of_finite.aestronglyMeasurable
  have hGP (v : ℝ) :
      (∏ p, ∫ x : ℝ, (Real.sqrt v * x) ^ kP₂ p ∂gaussianReal 0 1) =
        (∏ p, ∫ x : ℝ, (Real.sqrt v * x) ^ kP p ∂gaussianReal 0 1) ^ 2 := by
    simp [kP₂, Fintype.prod_prod_type, Fintype.prod_sum_type, pow_two]
  have hGS (v : ℝ) :
      (∏ r, ∫ x : ℝ, (Real.sqrt v * x) ^ kS₂ r ∂gaussianReal 0 1) =
        (∏ r, ∫ x : ℝ, (Real.sqrt v * x) ^ kS r ∂gaussianReal 0 1) ^ 2 := by
    simp [kS₂, Fintype.prod_sum_type, pow_two]
  have h₁ := hC₁ β h q hfix hb N
  simp only [add_zero, pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one] at h₁
  change |((N : ℝ) + 1) ^ ((k : ℝ) / 2) * (∫ g, ∫ ρ, H g ρ
    ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) ∂P) - G| ≤ _ at h₁
  rw [← integral_const_mul] at h₁
  have h₂ := hC₂ β h q hfix hb N
  simp only [add_zero, pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one] at h₂
  change |((N : ℝ) + 1) ^ ((((∑ p, kP₂ p) + ∑ r, kS₂ r : ℕ) : ℝ) / 2) *
    (∫ g, ∫ ρ, H₂ g ρ
      ∂(Measure.pi fun _ : R ⊕ R => Measure.count.tilted (E g)) ∂P) -
    (∏ p, ∫ x : ℝ, (Real.sqrt A2 * x) ^ kP₂ p ∂gaussianReal 0 1) *
    (∏ r, ∫ x : ℝ, (Real.sqrt B2 * x) ^ kS₂ r ∂gaussianReal 0 1)| ≤ _ at h₂
  rw [hk₂, hGP, hGS, ← mul_pow] at h₂
  have hm : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hscale : (((N : ℝ) + 1) ^ ((k : ℝ) / 2)) ^ 2 =
      ((N : ℝ) + 1) ^ (((2 * k : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_mul_natCast hm.le]
    congr 1
    push_cast
    ring
  have hV₂ : (∫ g, V g ^ 2 ∂P) =
      ((N : ℝ) + 1) ^ (((2 * k : ℕ) : ℝ) / 2) *
        ∫ g, ∫ ρ, H₂ g ρ
          ∂(Measure.pi fun _ : R ⊕ R => Measure.count.tilted (E g)) ∂P := by
    simp only [V, mul_pow]
    rw [hscale, integral_const_mul]
    simp_rw [hsquare]
    rfl
  rw [← hV₂] at h₂
  exact ⟨h₁, h₂⟩

/-- **Talagrand (1.293)--(1.294).** A normalized conditional Gibbs pair/single
moment has disorder variance at most `C / sqrt (N+1)`, uniformly in the stated parameters. -/
theorem sk_T_gibbs_moment_variance_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type u} [Fintype R] [LinearOrder R] [Nonempty R]
    (kP : R × R → ℕ) (kS : R → ℕ) (hord : ∀ p, 0 < kP p → p.1 < p.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let TP := fun (p : R × R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ p.1 i : ℝ) - bmean g i) *
        ((ρ p.2 i : ℝ) - bmean g i)
    let TS := fun (r : R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ r i : ℝ) - bmean g i) * bmean g i
    let k : ℕ := (∑ p, kP p) + ∑ r, kS r
    let V := fun g => ((N : ℝ) + 1) ^ ((k : ℝ) / 2) *
      ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (∏ p, TP p g ρ ^ kP p) * (∏ r, TS r g ρ ^ kS r)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let A2 : ℝ := α / (1 - β ^ 2 * α)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * A2) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh))
    let G : ℝ := (∏ p, ∫ x : ℝ, (Real.sqrt A2 * x) ^ kP p ∂gaussianReal 0 1) *
      (∏ r, ∫ x : ℝ, (Real.sqrt B2 * x) ^ kS r ∂gaussianReal 0 1)
    let P := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
    (∫ g, (V g - G) ^ 2 ∂P) ≤ C / Real.sqrt ((N : ℝ) + 1) ∧
      |(∫ g, V g ^ 2 ∂P) - (∫ g, V g ∂P) ^ 2| ≤ C / Real.sqrt ((N : ℝ) + 1) ∧
      (∫ g, (V g - ∫ g', V g' ∂P) ^ 2 ∂P) ≤ C / Real.sqrt ((N : ℝ) + 1) := by
  obtain ⟨C₁, hC₁0, C₂, hC₂0, hCs⟩ :=
    sk_T_gibbs_moment_first_two_uniform β₀ hβ₀ kP kS hord
  let MP : ℝ := (∏ p, ((kP p)! : ℝ)) * Real.sqrt 12 ^ (∑ p, kP p)
  let MS : ℝ := (∏ r, ((kS r)! : ℝ)) * Real.sqrt 12 ^ (∑ r, kS r)
  let M : ℝ := MP * MS
  have hMP : 0 ≤ MP := by positivity
  have hMS : 0 ≤ MS := by positivity
  have hM : 0 ≤ M := mul_nonneg hMP hMS
  refine ⟨C₂ + 2 * M * C₁, by positivity, fun β h q hfix hb N => ?_⟩
  intro E bmean TP TS k V qh α A2 B2 G P
  have hboth : |(∫ g, V g ∂P) - G| ≤ C₁ / Real.sqrt ((N : ℝ) + 1) ∧
      |(∫ g, V g ^ 2 ∂P) - G ^ 2| ≤ C₂ / Real.sqrt ((N : ℝ) + 1) :=
    hCs β h q hfix hb N
  have hα := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hp := one_sub_mul_div_bounds (sq_nonneg β)
    (show β ^ 2 ≤ (1 / 4 : ℝ) by linarith) hα (by norm_num : (1 / 4 : ℝ) < 1)
  have hA12 : A2 ≤ 12 := by norm_num only at hp; linarith [hp.2.2]
  have hB12 : B2 ≤ 12 := by
    have hs := single_coeff_facts β₀ hβ₀ β h q hfix hb
    linarith [hs.2.2.2]
  have hprod {ι : Type u} [Fintype ι] (c : ι → ℕ) (v : ℝ) (hv : v ≤ 12) :
      |∏ i, ∫ x : ℝ, (Real.sqrt v * x) ^ c i ∂gaussianReal 0 1| ≤
        (∏ i, ((c i)! : ℝ)) * Real.sqrt 12 ^ (∑ i, c i) := by
    refine (abs_prod_integral_pow_scaled_gaussianReal_le c (Real.sqrt_nonneg v)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hv) _) (by positivity)
  have hG : |G| ≤ M := by
    dsimp only [G, M]
    rw [abs_mul]
    exact mul_le_mul (hprod kP A2 hA12) (hprod kS B2 hB12) (abs_nonneg _) hMP
  have hV : MemLp V 2 P :=
    (sk_T_multiindex_memLp N β h kP kS 2 (μ := P)).const_mul _
  have hrate : C₂ / Real.sqrt ((N : ℝ) + 1) + 2 * |G| *
      (C₁ / Real.sqrt ((N : ℝ) + 1)) ≤ (C₂ + 2 * M * C₁) / Real.sqrt ((N : ℝ) + 1) := by
    calc C₂ / Real.sqrt ((N : ℝ) + 1) + 2 * |G| *
        (C₁ / Real.sqrt ((N : ℝ) + 1)) ≤
        C₂ / Real.sqrt ((N : ℝ) + 1) + 2 * M *
          (C₁ / Real.sqrt ((N : ℝ) + 1)) := by gcongr
      _ = (C₂ + 2 * M * C₁) / Real.sqrt ((N : ℝ) + 1) := by ring
  have hmse := (integral_sub_const_sq_le_of_moment_errors hV hboth.1 hboth.2).trans hrate
  have hvar := (variance_le_of_moment_errors hV hboth.1 hboth.2).trans hrate
  refine ⟨hmse, ?_, ?_⟩
  · have he : variance V P = (∫ g, V g ^ 2 ∂P) - (∫ g, V g ∂P) ^ 2 :=
      variance_eq_sub hV
    rw [← he, abs_of_nonneg (variance_nonneg V P)]
    exact hvar
  · simpa only [variance_eq_integral hV.aemeasurable] using hvar

end SpinGlasses
