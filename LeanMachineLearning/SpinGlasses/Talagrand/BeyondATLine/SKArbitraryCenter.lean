/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKFixedPointResidual
public import LeanMachineLearning.SpinGlasses.SKBeyondATProposition

/-!
# Overlap bounds around an arbitrary center (Talagrand, Proposition 1.9.5(a))

For `x ∈ [0, 1]` the first-order cavity estimate centered at `x` (the cavity path with `q`
replaced by `x`; no fixed-point property is used) compares `ν(ε₁ε₂)` with its decoupled value
`Φ(x) = 𝔼 tanh²(β √x z + h)` up to `K ν(|R₁₂ - x|)`.  Site symmetry gives `ν(ε₁ε₂) = ν(R₁₂)`,
and Jensen's inequality gives `|ν(R₁₂) - x| ≤ ν(|R₁₂ - x|)`.  With the residual bound
`|x - q| ≤ K |x - Φ(x)|` of `SKFixedPointResidual` this proves `|x - q| ≤ K ν(|R₁₂ - x|)`
(Eq. (1.279)); here the cavity is exact in `ε` so the book's `1/N` correction does not appear.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.9.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Eq. (1.281)/(1.282) for an arbitrary center `x ∈ [0, 1]`.**  For the two-replica average `ν₂`
of the `(N+1)`-spin system,
`|ν₂(R₁₂) - Φ(x)| ≤ 8 β² e^{64 β²} ν₂(|R₁₂ - x|) `, `Φ(x) = 𝔼 tanh²(β √x z + h)`. -/
theorem sk_overlap_mean_sub_fixedPointMap_le (N : ℕ) (β h x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    |ν₂ (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ))) -
        ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)| ≤
      8 * β ^ 2 * Real.exp (64 * β ^ 2) *
        ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|) := by
  have hbd : ∀ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      |((σ 0 (Fin.last N) : ℤˣ) : ℝ) * ((σ 1 (Fin.last N) : ℤˣ) : ℝ)| ≤ 1 := fun σ => by
    rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one]; norm_num
  have T := sk_cavity_nu_sub_nu_zero_le_of_abs_le N 2 β x h hx
    (fun σ : Fin 2 → Fin (N + 1) → ℤˣ => ((σ 0 (Fin.last N) : ℤˣ) : ℝ) *
      ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) (M := 1) hbd
  have P := sk_cavity_decoupled_endpoint_replicas N β x h ({0, 1} : Finset (Fin 2))
    (fun _ => (1 : ℝ))
  have hsym := sk_overlap_mul_eq_last_site_of_perm N 2 β h 0 ν₂ hν₂ 0 1 (fun _ => 1)
    (fun _ _ => rfl)
  simp only [mul_one, sub_zero] at hsym
  simp only [] at T P
  simp only [one_mul, integral_const, probReal_univ, one_smul, mul_one,
    Finset.card_pair (show (0 : Fin 2) ≠ 1 by decide), Finset.prod_pair (show (0 : Fin 2) ≠ 1
      by decide), integral_tanh_pow_mul_z_sqrt_eq] at P
  rw [P] at T
  rw [← hν₂, ← hν₂] at T
  rw [hsym]
  have e : (2 : ℝ) * (2 : ℕ) ^ 2 * β ^ 2 * Real.exp (4 * (((2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) * 1 =
      8 * β ^ 2 * Real.exp (64 * β ^ 2) := by
    norm_num
  rw [e] at T
  exact T

/-- **Jensen:** `|ν₂(R₁₂) - x| ≤ ν₂(|R₁₂ - x|)`. -/
theorem sk_abs_mean_overlap_sub_le (N : ℕ) (β h x : ℝ)
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    |ν₂ (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ))) - x| ≤
      ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|) := by
  obtain ⟨hadd, -, -, hconst⟩ := sk_replica_avg_calculus N 2 β h ν₂ hν₂
  have h1 := sk_nu_abs_le N β h 2 ν₂ hν₂
    (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x)
  have h2 : ν₂ (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x) =
      ν₂ (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ))) - x := by
    have := hadd (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ))) (fun _ => -x)
    rw [hconst] at this
    simp only [← sub_eq_add_neg] at this
    rw [this]
  rwa [h2] at h1

/-- **Proposition 1.9.5(a), Eq. (1.279)** (nonzero field).  Let `h ≠ 0` and let `q` be a fixed
point of `q = 𝔼 tanh²(β √q z + h)`, `q̂ = 𝔼 tanh⁴(β √q z + h)`.  There is `K`, depending only
on `β, h` (not on `N` or `x`), such that for every `N` and every center `x ≥ 0`,
`|x - q| ≤ K ν(|R₁₂ - x|)` for the `(N+1)`-spin SK average. -/
theorem sk_overlap_center_bound (β h q qhat : ℝ) (hh : h ≠ 0)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ)
      (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
      (_ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (x : ℝ), 0 ≤ x →
      |x - q| ≤ K * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|) := by
  obtain ⟨K₀, hK₀, hres⟩ := exists_abs_sub_le_mul_abs_sub_fixedPointMap hh hfix hqhat
  have hC : 0 ≤ 8 * β ^ 2 * Real.exp (64 * β ^ 2) := by positivity
  set K₁ : ℝ := K₀ * (8 * β ^ 2 * Real.exp (64 * β ^ 2) + 1) with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  refine ⟨1 + K₁, by positivity, fun N ν₂ hν₂ x hx => ?_⟩
  obtain ⟨-, -, hmono, hconst⟩ := sk_replica_avg_calculus N 2 β h ν₂ hν₂
  have hD : ∀ y : ℝ, 0 ≤ ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ)) - y|) := fun y =>
    sk_avg_nonneg N β h 2 ν₂ hν₂ _ fun σ => abs_nonneg _
  -- centers in `[0, 1]`
  have h01 : ∀ y ∈ Icc (0 : ℝ) 1, |y - q| ≤ K₁ * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
      ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - y|) :=
    fun y hy => by
    have c1 := sk_overlap_mean_sub_fixedPointMap_le N β h y hy ν₂ hν₂
    have c2 := sk_abs_mean_overlap_sub_le N β h y ν₂ hν₂
    have c3 : |y - ∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)| ≤
        (8 * β ^ 2 * Real.exp (64 * β ^ 2) + 1) * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - y|) := by
      refine (abs_sub_le y (ν₂ (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)))) _).trans ?_
      rw [abs_sub_comm y]
      linarith only [c1, c2]
    calc |y - q| ≤ K₀ * |y - ∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2
          ∂(gaussianReal 0 1)| := hres y hy
      _ ≤ K₀ * ((8 * β ^ 2 * Real.exp (64 * β ^ 2) + 1) * _) :=
          mul_le_mul_of_nonneg_left c3 hK₀.le
      _ = K₁ * _ := by rw [hK₁]; ring
  rcases le_or_gt x 1 with hx1 | hx1
  · exact (h01 x ⟨hx, hx1⟩).trans (mul_le_mul_of_nonneg_right (by linarith)
      (hD x))
  · -- centers beyond `1`
    have hq1 : q ∈ Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
    have hone := h01 1 ⟨zero_le_one, le_rfl⟩
    have hmon : ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - 1|) ≤
        ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|) := by
      refine hmono _ _ fun σ => ?_
      have hR := abs_le.1 (abs_overlap_le_one σ)
      rw [abs_of_nonpos (by linarith [hR.2]), abs_of_nonpos (by linarith [hR.2])]
      linarith
    have hjen := sk_abs_mean_overlap_sub_le N β h x ν₂ hν₂
    have hν1 : ν₂ (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ))) ≤ 1 := by
      have := hmono _ (fun _ => (1 : ℝ)) fun σ => (abs_le.1 (abs_overlap_le_one σ)).2
      rwa [hconst] at this
    have hxm : x - 1 ≤ ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|) := by
      refine le_trans ?_ hjen
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    have h1q : |(1 : ℝ) - q| = |1 - q| := rfl
    calc |x - q| ≤ (x - 1) + |1 - q| := by
          rw [abs_le]; constructor <;> cases abs_cases (1 - q) <;> linarith
      _ ≤ _ + K₁ * _ := add_le_add hxm (hone.trans' le_rfl)
      _ ≤ (1 + K₁) * _ := by nlinarith only [mul_le_mul_of_nonneg_left hmon hK₁0.le]

/-- **Proposition 1.9.5(b), Eq. (1.280)** (nonzero field, beyond the AT line).  Let `h ≠ 0`, `q` a
fixed point, `q̂ = 𝔼 tanh⁴`, and `β² (1 - 2q + q̂) > 1`.  There are `δ' > 0` and `N₀`,
independent of `x`, such that for every `N ≥ N₀` and every center `x ≥ 0`,
`ν(1{|R₁₂ - x| ≥ δ'}) ≥ δ'/(N+1)` for the `(N+1)`-spin SK average. -/
theorem sk_overlap_center_indicator (β h q qhat : ℝ) (hh : h ≠ 0)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hAT : 1 < β ^ 2 * (1 - 2 * q + qhat)) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
      (_ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (x : ℝ), 0 ≤ x →
      δ' / ((N : ℝ) + 1) ≤ ν₂ (fun σ => if δ' ≤ |(N + 1 : ℝ)⁻¹ *
        ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
        then 1 else 0) := by
  have hq : 0 < q := by
    have := fixedPointMap_pos hh (β * Real.sqrt q)
    rwa [hfix] at this
  obtain ⟨δ, hδ, N₁, h192⟩ := sk_proposition_192 β h q qhat hq hfix hqhat hAT
  obtain ⟨K, hK, hcen⟩ := sk_overlap_center_bound β h q qhat hh hfix hqhat
  set c₀ : ℝ := δ / (4 * K) with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set δ' : ℝ := min (δ / 4) (min (c₀ / 2) (min 1 (min (δ ^ 2 / 16) (c₀ / 6)))) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) (lt_min (by positivity)
    (lt_min one_pos (lt_min (by positivity) (by positivity))))
  have l1 : δ' ≤ δ / 4 := min_le_left _ _
  have l2 : δ' ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have l3 : δ' ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have l4 : δ' ≤ δ ^ 2 / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have l5 : δ' ≤ c₀ / 6 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ', hδ'0, N₁, fun N hN ν₂ hν₂ x hx => ?_⟩
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N 2 β h ν₂ hν₂
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hM1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  -- the indicator is monotone in the threshold
  have hind : ∀ t s : ℝ, t ≤ s → ν₂ (fun σ => if s ≤ |(N + 1 : ℝ)⁻¹ *
        ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
        then (1 : ℝ) else 0) ≤
      ν₂ (fun σ => if t ≤ |(N + 1 : ℝ)⁻¹ *
        ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
        then (1 : ℝ) else 0) := fun t s hts => by
    refine hmono _ _ fun σ => ?_
    by_cases h1 : s ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
    · simp [h1, hts.trans h1]
    · simp only [h1, ite_false]
      split_ifs <;> norm_num
  have hdiv : δ' / ((N : ℝ) + 1) ≤ δ' := div_le_self hδ'0.le hM1
  rcases le_or_gt x 2 with hx2 | hx2
  · by_cases hxq : |x - q| ≤ δ / 4
    · -- Case A: the center is close to `q`; use Eq. (1.271)
      obtain ⟨hc, hS⟩ := h192 N hN
      simp only [← hν₂] at hc hS
      have hq1 : |q| ≤ 1 := by
        have := fixedPoint_mem_Icc hfix
        rw [abs_of_nonneg this.1]; exact this.2
      have h271 := sk_indicator_lower_bound_of_cubic N β h q δ hq1 hδ ν₂ hν₂ hc
      have hA1 : δ ^ 2 / (16 * ((N : ℝ) + 1)) ≤ δ / 16 *
          ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) := by
        have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ δ / 16)
        calc δ ^ 2 / (16 * ((N : ℝ) + 1)) = δ / 16 * (δ / ((N : ℝ) + 1)) := by
              field_simp
          _ ≤ _ := this
      have hA2 : ν₂ (fun σ => if δ / 2 ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| then (1 : ℝ) else 0) ≤
          ν₂ (fun σ => if δ / 4 ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x| then (1 : ℝ) else 0) := by
        refine hmono _ _ fun σ => ?_
        by_cases h1 : δ / 2 ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|
        · have h2 : δ / 4 ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x| := by
            have := abs_sub_abs_le_abs_sub ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ))
              ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x)
            have h3 : |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
                fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q - ((N + 1 : ℝ)⁻¹ *
                ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) -
                x)| = |x - q| := by
              rw [show ∀ a b c : ℝ, a - c - (a - b) = b - c from fun a b c => by ring]
            linarith only [this, h3, h1, hxq]
          simp [h1, h2]
        · simp only [h1, ite_false]
          split_ifs <;> norm_num
      have := hind δ' (δ / 4) l1
      calc δ' / ((N : ℝ) + 1) ≤ δ ^ 2 / 16 / ((N : ℝ) + 1) :=
            div_le_div_of_nonneg_right l4 hM0.le
        _ = δ ^ 2 / (16 * ((N : ℝ) + 1)) := by field_simp
        _ ≤ _ := hA1.trans (h271.trans (hA2.trans this))
    · -- Case B: the center is far from `q`; use Eq. (1.279)
      push Not at hxq
      have hDx := hcen N ν₂ hν₂ x hx
      have hDc : c₀ ≤ ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|) := by
        rw [hc₀, div_le_iff₀ (by positivity)]
        nlinarith only [hDx, hxq]
      have hB1 : ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|) ≤
          c₀ / 2 + 3 * ν₂ (fun σ => if c₀ / 2 ≤ |(N + 1 : ℝ)⁻¹ *
            ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
            then (1 : ℝ) else 0) := by
        have key : ν₂ (fun σ => c₀ / 2 + 3 * (if c₀ / 2 ≤ |(N + 1 : ℝ)⁻¹ *
            ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
            then (1 : ℝ) else 0)) = c₀ / 2 + 3 * ν₂ (fun σ => if c₀ / 2 ≤ |(N + 1 : ℝ)⁻¹ *
            ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
            then (1 : ℝ) else 0) := by
          rw [hadd (fun _ => c₀ / 2) (fun σ => 3 * (if c₀ / 2 ≤ |(N + 1 : ℝ)⁻¹ *
            ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
            then (1 : ℝ) else 0)), hconst, hsmul]
        rw [← key]
        refine hmono _ _ fun σ => ?_
        have hR := abs_le.1 (abs_overlap_le_one σ)
        have hb : |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x| ≤ 3 := by
          rw [abs_le]; constructor <;> linarith [hR.1, hR.2]
        by_cases h1 : c₀ / 2 ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
        · simp only [h1, ↓reduceIte]; linarith
        · simp only [h1, ↓reduceIte]; push Not at h1; linarith
      have hB2 : c₀ / 6 ≤ ν₂ (fun σ => if c₀ / 2 ≤ |(N + 1 : ℝ)⁻¹ *
            ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
            then (1 : ℝ) else 0) := by linarith only [hDc, hB1]
      exact (hdiv.trans l5).trans (hB2.trans (hind δ' (c₀ / 2) l2))
  · -- Case C: the center is far from the unit interval
    have hall : ν₂ (fun σ => if δ' ≤ |(N + 1 : ℝ)⁻¹ *
        ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x|
        then (1 : ℝ) else 0) = 1 := by
      refine Eq.trans ?_ (hconst 1)
      congr 1
      funext σ
      have hR := abs_le.1 (abs_overlap_le_one σ)
      have : δ' ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hR.2])]
        linarith [hR.2]
      simp only [this, ↓reduceIte]
    rw [hall]
    exact hdiv.trans l3

end SpinGlasses
