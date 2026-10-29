/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalRecurrence
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianClassRecurrence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Gaussian law of `T` (Talagrand, Theorem 1.10.1, the factors `T`)

The recurrence of `SKOverlapCLTGlobalRecurrence.lean` is the two-factor recurrence of the generic
Gaussian class engine with a single class, so `𝔼 T^k` is the `k`-th moment of a centered Gaussian
of variance `C²/(N+1)` up to `O(k+1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **The variance coefficient `C²` of Theorem 1.10.1** (the end of the proof, relation (1.262)):
the solution of `(1 - β²(1-4q+3q̂)) C² = (q̂-q²) + β²(q̂-q²) A² + 2β²(2q+q²-3q̂) B²` with
`A² = α/(1-β²α)` and `B² = (q-q̂)(1+β²A²)/(1-β²(1-4q+3q̂))`. -/
theorem global_coefficient_facts (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (β h q : ℝ)
    (hfix : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q)
    (hb : β ^ 2 ≤ β₀ ^ 2) :
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qh)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / D
    let E0 : ℝ := (qh - q ^ 2) + β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α)) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2
    3 / 4 ≤ D ∧ |E0 / D| ≤ 12 := by
  intro qh α D B2 E0
  obtain ⟨hdq, hD, hB0, hB2⟩ := single_coeff_facts β₀ hβ₀ β h q hfix hb
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hqh0 : 0 ≤ qh := integral_nonneg fun t => by positivity
  have hα : 0 ≤ α ∧ α ≤ 1 := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hβ4 : β ^ 2 ≤ 1 / 4 := by linarith
  have hDα : 3 / 4 ≤ 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
    linarith
  have hA : 0 ≤ α / (1 - β ^ 2 * α) ∧ α / (1 - β ^ 2 * α) ≤ 4 / 3 := by
    refine ⟨div_nonneg hα.1 (by linarith), ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hqq : |qh - q ^ 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hq.1, hq.2]
  have h3q : |2 * q + q ^ 2 - 3 * qh| ≤ 6 := by
    rw [abs_le]
    constructor <;> nlinarith [hq.1, hq.2]
  have hE0 : |E0| ≤ 9 := by
    have t1 : |β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α))| ≤ 2 / 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β), abs_of_nonneg hA.1]
      have : β ^ 2 * |qh - q ^ 2| ≤ 1 / 4 * 2 :=
        mul_le_mul hβ4 hqq (abs_nonneg _) (by norm_num)
      nlinarith [abs_nonneg (qh - q ^ 2)]
    have t2 : |2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2| ≤ 6 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg (sq_nonneg β)]
      have : 2 * β ^ 2 * |2 * q + q ^ 2 - 3 * qh| ≤ 2 * (1 / 4) * 6 := by
        have := mul_le_mul hβ4 h3q (abs_nonneg _) (by norm_num)
        nlinarith
      nlinarith [abs_nonneg (2 * q + q ^ 2 - 3 * qh)]
    calc |E0| ≤ |qh - q ^ 2| + |β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α))| +
          |2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2| := abs_add_three _ _ _
      _ ≤ 9 := by linarith
  refine ⟨hD, ?_⟩
  rw [abs_div, abs_of_pos (by linarith : 0 < D), div_le_iff₀ (by linarith)]
  linarith [hE0]

/-- **The recurrence in the form used for the Gaussian moments**: the coefficient is
`E0/(N+1)` with `E0` independent of `N`. -/
theorem sk_T_global_recurrence_clean (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {V : Type*} [Fintype V] (p : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (Esk g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qh)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / D
    let E0 : ℝ := (qh - q ^ 2) + β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α)) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |D * ν (Fintype.card V) - ((Fintype.card V - 1 : ℕ) : ℝ) * (E0 / (N + 1 : ℝ)) *
        ν (Fintype.card V - 2)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_T_global_recurrence_uniform β₀ hβ₀ p
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro Esk bmean Tg qh α D B2 E0 ν
  have h1 := hC β h q hfix hb N
  have e : E0 / (N + 1 : ℝ) = (qh - q ^ 2) / (N + 1 : ℝ) +
      β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * (B2 / (N + 1 : ℝ)) := by
    simp only [E0]
    ring
  rw [e]
  exact h1

/-- The global Gaussian variance is nonnegative, including degenerate parameter choices.
The proof uses the degree-two recurrence and positivity of actual second moments. -/
theorem sk_T_global_variance_nonneg (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (β h q : ℝ)
    (hfix : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q)
    (hb : β ^ 2 ≤ β₀ ^ 2) :
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qh)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / D
    let E0 : ℝ := (qh - q ^ 2) + β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α)) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2
    0 ≤ E0 / D := by
  intro qh α D B2 E0
  obtain ⟨C, -, hC⟩ := sk_T_global_recurrence_clean β₀ hβ₀ (V := Fin 2) (0 : Fin 2)
  have hD : 0 < D := by
    have hd := (global_coefficient_facts β₀ hβ₀ β h q hfix hb).1
    linarith
  have hbound : ∀ N : ℕ, -(C / Real.sqrt ((N : ℝ) + 1)) ≤ E0 := by
    intro N
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let b : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      (N + 1 : ℝ)⁻¹ * ∑ i, b g i * b g i - q
    have ht := hC β h q hfix hb N
    change |D * (∫ g, T g ^ 2 ∂(Measure.pi fun _ : FinPairs (N + 1) =>
      gaussianReal 0 1)) - ((2 - 1 : ℕ) : ℝ) * (E0 / (N + 1 : ℝ)) *
        (∫ g, T g ^ (2 - 2) ∂(Measure.pi fun _ : FinPairs (N + 1) =>
          gaussianReal 0 1))| ≤ C / ((N : ℝ) + 1) ^ (((2 + 1 : ℕ) : ℝ) / 2) at ht
    norm_num only [pow_zero, integral_const, probReal_univ, one_smul, mul_one] at ht
    have hpos : 0 ≤ D * (∫ g, T g ^ 2 ∂(Measure.pi fun _ : FinPairs (N + 1) =>
        gaussianReal 0 1)) := mul_nonneg hD.le (integral_nonneg fun _ => sq_nonneg _)
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hrpow : ((N : ℝ) + 1) ^ (3 / 2 : ℝ) =
        ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN,
        Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hrpow] at ht
    have he : -(C / (((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1))) ≤
        E0 / (N + 1 : ℝ) := by linarith [(abs_le.mp ht).2]
    have hh := mul_le_mul_of_nonneg_left he hN.le
    convert hh using 1 <;> field_simp
  have hn : Filter.Tendsto (fun N : ℕ => (N : ℝ) + 1) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hz : Filter.Tendsto (fun N : ℕ => C / Real.sqrt ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp hn).const_div_atTop C
  have hE : -(0 : ℝ) ≤ E0 := le_of_tendsto hz.neg (Filter.Eventually.of_forall hbound)
  exact div_nonneg (by simpa only [neg_zero] using hE) hD.le

/-- **`𝔼 T^k` is a Gaussian moment** (Theorem 1.10.1 for the factors `T` alone). -/
theorem sk_T_global_gaussian_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (Esk g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qh)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / D
    let E0 : ℝ := (qh - q ^ 2) + β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α)) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2
    |(∫ g, Tg g ^ k ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      ∫ x : ℝ, (Real.sqrt (E0 / D / (N + 1 : ℝ)) * x) ^ k ∂gaussianReal 0 1| ≤
      K / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
  classical
  let valid : ℝ × ℝ × ℝ → Prop := fun θ =>
    (∫ t : ℝ, Real.tanh (θ.1 * Real.sqrt θ.2.2 * t + θ.2.1) ^ 2 ∂gaussianReal 0 1 = θ.2.2) ∧
      θ.1 ^ 2 ≤ β₀ ^ 2
  let qhf : ℝ × ℝ × ℝ → ℝ := fun θ =>
    ∫ t : ℝ, Real.tanh (θ.1 * t * Real.sqrt θ.2.2 + θ.2.1) ^ 4 ∂gaussianReal 0 1
  let Dθ : ℝ × ℝ × ℝ → ℝ := fun θ => 1 - θ.1 ^ 2 * (1 - 4 * θ.2.2 + 3 * qhf θ)
  let Enum : ℝ × ℝ × ℝ → ℝ := fun θ =>
    (qhf θ - θ.2.2 ^ 2) + θ.1 ^ 2 * (qhf θ - θ.2.2 ^ 2) *
      ((qhf θ - 2 * θ.2.2 + 1) / (1 - θ.1 ^ 2 * (qhf θ - 2 * θ.2.2 + 1))) +
      2 * θ.1 ^ 2 * (2 * θ.2.2 + θ.2.2 ^ 2 - 3 * qhf θ) *
        ((θ.2.2 - qhf θ) * (1 + θ.1 ^ 2 * ((qhf θ - 2 * θ.2.2 + 1) /
          (1 - θ.1 ^ 2 * (qhf θ - 2 * θ.2.2 + 1)))) / Dθ θ)
  let cf : ℝ × ℝ × ℝ → ℝ := fun θ => Enum θ / Dθ θ
  let Tθ : ℝ × ℝ × ℝ → (N : ℕ) → (FinPairs (N + 1) → ℝ) → ℝ := fun θ N g =>
    ((N + 1 : ℝ)⁻¹ * ∑ i : Fin (N + 1),
      (∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted
        (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * θ.1 *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ)))) *
      (∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted
        (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * θ.1 *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ))))) - θ.2.2
  let Fq : ℝ × ℝ × ℝ → ℕ → Finset ℕ → ℝ := fun θ N s =>
    ∫ g, Tθ θ N g ^ s.card ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hcoef : ∀ θ, valid θ → |cf θ| ≤ 12 := fun θ hθ => by
    have := global_coefficient_facts β₀ hβ₀ θ.1 θ.2.1 θ.2.2 hθ.1 hθ.2
    exact this.2
  have hc0 : ∀ θ, valid θ → 0 ≤ cf θ := fun θ hθ =>
    sk_T_global_variance_nonneg β₀ hβ₀ θ.1 θ.2.1 θ.2.2 hθ.1 hθ.2
  have hF : ∀ (s : Finset ℕ) (p u : ℕ), p ∈ s → True → u ∈ s →
      (((s.filter fun j => True ∧ () = ()).erase p).Nonempty →
        u ∈ (s.filter fun j => True ∧ () = ()).erase p) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ θ, valid θ → ∀ N : ℕ,
        |Fq θ N s - ((((s.filter fun j => True ∧ () = ()).card - 1 : ℕ) : ℝ) *
          cf θ / (N + 1 : ℝ)) * Fq θ N ((s.erase p).erase u)| ≤
          K / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
    intro s p u hps _ hus href
    have hfs : (s.filter fun j => True ∧ () = ()) = s := Finset.filter_true_of_mem fun _ _ =>
      ⟨trivial, rfl⟩
    rw [hfs] at href ⊢
    obtain ⟨C, hC0, hC⟩ := sk_T_global_recurrence_clean β₀ hβ₀ (V := ↥s) ⟨p, hps⟩
    refine ⟨4 / 3 * C, by positivity, fun θ hθ N => ?_⟩
    have h := hC θ.1 θ.2.1 θ.2.2 hθ.1 hθ.2 N
    rw [Fintype.card_coe] at h
    obtain ⟨hD, -⟩ := global_coefficient_facts β₀ hβ₀ θ.1 θ.2.1 θ.2.2 hθ.1 hθ.2
    have hDθ : 3 / 4 ≤ Dθ θ := hD
    have hY : ((s.card - 1 : ℕ) : ℝ) * (Enum θ / (N + 1 : ℝ)) *
        Fq θ N ((s.erase p).erase u) =
        ((s.card - 1 : ℕ) : ℝ) * (Enum θ / (N + 1 : ℝ)) *
          (∫ g, Tθ θ N g ^ (s.card - 2) ∂(Measure.pi fun _ : FinPairs (N + 1) =>
            gaussianReal 0 1)) := by
      by_cases h1 : s.card = 1
      · simp [h1]
      · have hne : ((s.erase p)).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hps]
          have := Finset.card_pos.mpr (⟨p, hps⟩ : s.Nonempty)
          omega
        have hup : u ∈ s.erase p := href (by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hps]
          have := Finset.card_pos.mpr (⟨p, hps⟩ : s.Nonempty)
          omega)
        have hc : ((s.erase p).erase u).card = s.card - 2 := by
          rw [Finset.card_erase_of_mem hup, Finset.card_erase_of_mem hps]
          omega
        simp only [Fq, hc]
    have h' : |Dθ θ * Fq θ N s - ((s.card - 1 : ℕ) : ℝ) * (Enum θ / (N + 1 : ℝ)) *
        Fq θ N ((s.erase p).erase u)| ≤ C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
      rw [hY]
      exact h
    have := div_recurrence_step (Fq θ N s) (Fq θ N ((s.erase p).erase u)) (Dθ θ)
      (((s.card - 1 : ℕ) : ℝ) * (Enum θ / (N + 1 : ℝ))) _ hDθ h'
    have hn : ((s.card - 1 : ℕ) : ℝ) * (Enum θ / (N + 1 : ℝ)) / Dθ θ =
        ((s.card - 1 : ℕ) : ℝ) * cf θ / (N + 1 : ℝ) := by
      simp only [cf]
      have : Dθ θ ≠ 0 := by linarith
      field_simp
    rw [hn] at this
    calc _ ≤ _ := this
      _ = 4 / 3 * C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by ring
  obtain ⟨K, hK0, hK⟩ := ProbabilityTheory.exists_gaussian_class_moment_error (J := ℕ)
    (ι := Unit) (Θ := ℝ × ℝ × ℝ) (fun _ => True) (fun _ => ()) valid Fq cf 12 hc0 hcoef hF
    (Finset.range k)
  refine ⟨K, hK0, fun β h q hfix hb N => ?_⟩
  intro Esk bmean Tg qh α D B2 E0
  have h1 := hK (β, h, q) ⟨hfix, hb⟩ N
  have hfilt1 : (Finset.range k).filter (fun j => ¬True) = ∅ := by simp
  have hF0 : Fq (β, h, q) N ∅ = 1 := by simp [Fq]
  simp only [hfilt1, and_self, Finset.filter_true, Finset.card_range, Finset.univ_unique,
    Finset.prod_singleton, hF0, mul_one] at h1
  have hFk : Fq (β, h, q) N (Finset.range k) =
      ∫ g, Tg g ^ k ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    simp only [Fq, Finset.card_range]
    rfl
  rw [hFk] at h1
  exact h1

end SpinGlasses
