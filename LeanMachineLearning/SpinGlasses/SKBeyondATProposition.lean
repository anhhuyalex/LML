/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKBeyondATCovariance
public import LeanMachineLearning.SpinGlasses.SKBeyondATLowerBound
public import LeanMachineLearning.SpinGlasses.SKSecondaryContraction

/-!
# Proposition 1.9.2 for the SK model (Talagrand, Section 1.9)

Beyond the Almeida--Thouless line, `β² (1 - 2q + q̂) > 1`, the overlap fluctuations are bounded
below: there is `δ > 0`, independent of `N`, with
`ν(|R₁₂ - q|³) ≥ δ ν((R₁₂ - q)²) ≥ δ²/N` for large `N`.

`sk_beyond_at_remainders` assembles Lemma 1.9.4 (`sk_lemma_194`) with Lemma 1.9.3
(`sk_beta_sq_mul_one_sub_four_add_three_lt_one`), which makes the denominator
`1 - β² (1 - 4q + 3q̂)` positive, into the shape required by `exists_cubic_lower_bounds`.
The fixed point is assumed to be positive (Lemma 1.9.3), and for `h = 0` this selects the
non-trivial fixed point.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.9.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Lemma 1.9.4 for the SK model, in the form needed for Proposition 1.9.2.**  Beyond the AT
line there is `K`, depending only on `β` and the fixed point, such that for every `N` the
rectangular second moment and the overlap variance of the `(N+1)`-spin system satisfy
(1.275)--(1.277): with `a = 1 - 2q + q̂`, `ν(rect²) = (4/M) a/(1 - β² a) + 𝓡₁`,
`ν((R₁₂ - q)²) = A + 𝓡₂`, `|A| ≤ K/M`, `|𝓡_i| ≤ K (M^{-3/2} + ν(|R₁₂ - q|³))`, `M = N + 1`. -/
theorem sk_beyond_at_remainders (β h q qhat : ℝ) (hq : 0 < q)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hAT : 1 < β ^ 2 * (1 - 2 * q + qhat)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ)
      (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
      (_ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
      (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
      (_ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)),
      ∃ A : ℝ,
      |ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2) -
        4 / ((N : ℝ) + 1) * ((1 - 2 * q + qhat) / (1 - β ^ 2 * (1 - 2 * q + qhat)))| ≤
        K * ((Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 + ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3)) ∧
      |ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) - A| ≤
        K * ((Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 + ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3)) ∧
      |A| ≤ K / ((N : ℝ) + 1) := by
  have hd := sk_beta_sq_mul_one_sub_four_add_three_lt_one hq hfix hqhat
  have hβ0 : 0 ≤ β ^ 2 := sq_nonneg β
  have hD₁pos : 0 < β ^ 2 * (1 - 2 * q + qhat) - 1 := by linarith
  have hD₂pos : 0 < 1 - β ^ 2 * (1 - 4 * q + 3 * qhat) := by linarith
  set δ : ℝ := min (β ^ 2 * (1 - 2 * q + qhat) - 1) (1 - β ^ 2 * (1 - 4 * q + 3 * qhat)) with hδdef
  have hδ : 0 < δ := lt_min hD₁pos hD₂pos
  have hD₁ : δ ≤ |1 - β ^ 2 * (1 - 2 * q + qhat)| := by
    rw [abs_of_neg (by linarith)]
    linarith [min_le_left (β ^ 2 * (1 - 2 * q + qhat) - 1) (1 - β ^ 2 * (1 - 4 * q + 3 * qhat))]
  have hD₂ : δ ≤ |1 - β ^ 2 * (1 - 4 * q + 3 * qhat)| := by
    rw [abs_of_pos hD₂pos]
    exact min_le_right _ _
  set Kr : ℝ := 2304 * β ^ 4 * Real.exp (256 * β ^ 2) * 32 +
        32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) * 4 + 3) +
        64 * β ^ 2 * Real.exp (144 * β ^ 2) with hKr
  have hKr0 : 0 ≤ Kr := by positivity
  set K : ℝ := 1 + 16 / δ * Kr + (16 / δ + (4 * β ^ 2 / δ + 36 * β ^ 2 / δ + 1) / δ) * Kr +
    (1 / δ + 2 / δ ^ 2 + (1 + β ^ 2 / δ + 6 * β ^ 2 / δ ^ 2) / δ) with hKdef
  have hc1 : 0 ≤ 16 / δ * Kr := by positivity
  have hc2 : 0 ≤ (16 / δ + (4 * β ^ 2 / δ + 36 * β ^ 2 / δ + 1) / δ) * Kr := by positivity
  have hc3 : 0 ≤ 1 / δ + 2 / δ ^ 2 + (1 + β ^ 2 / δ + 6 * β ^ 2 / δ ^ 2) / δ := by positivity
  refine ⟨K, by positivity, fun N ν₂ hν₂ ν₄ hν₄ => ?_⟩
  obtain ⟨ν₃, hν₃⟩ : ∃ ν₃ : ((Fin 3 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ, ∀ Φ, ν₃ Φ =
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := ⟨_, fun _ => rfl⟩
  have key := sk_lemma_194 N β q h qhat δ hfix hqhat hδ hD₁ hD₂ ν₂ hν₂ ν₃ hν₃ ν₄ hν₄
    (Kr * (ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) +
        (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3)) rfl
  obtain ⟨k1, k2, k3⟩ := key
  simp only [← sq] at k2
  have hΔ0 := sk_avg_nonneg N β h 2 ν₂ hν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
    ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3)
    (fun σ => by positivity)
  have hm0 : 0 ≤ (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 := by positivity
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨_, ?_, ?_, k3.trans ?_⟩
  · refine k1.trans ?_
    calc 16 / δ * (Kr * (ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) + (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3)) =
        16 / δ * Kr * ((Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 + ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3))
          := by ring
      _ ≤ K * _ := mul_le_mul_of_nonneg_right (by linarith only [hc2, hc3, hKdef])
          (add_nonneg hm0 hΔ0)
  · refine k2.trans ?_
    calc (16 / δ + (4 * β ^ 2 / δ + 36 * β ^ 2 / δ + 1) / δ) *
        (Kr * (ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) + (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3)) =
        (16 / δ + (4 * β ^ 2 / δ + 36 * β ^ 2 / δ + 1) / δ) * Kr *
          ((Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 + ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3))
          := by ring
      _ ≤ K * _ := mul_le_mul_of_nonneg_right (by linarith only [hc1, hc3, hKdef])
          (add_nonneg hm0 hΔ0)
  · exact div_le_div_of_nonneg_right (by linarith only [hc1, hc2, hKdef]) hM0.le

/-- **Talagrand's Proposition 1.9.2 for the SK model.**  Let `q > 0` be a fixed point of
`q = 𝔼 tanh² (β z √q + h)`, `q̂ = 𝔼 tanh⁴ (β z √q + h)`, and assume `β² (1 - 2q + q̂) > 1`
(Eq. (1.266), beyond the AT line).  Then there are `δ > 0` and `N₀`, independent of `N`, such that
for every `N ≥ N₀` the `(N+1)`-spin system satisfies
`ν(|R₁₂ - q|³) ≥ δ ν((R₁₂ - q)²)` and `ν((R₁₂ - q)²) ≥ δ/(N+1)` (Eq. (1.269)). -/
theorem sk_proposition_192 (β h q qhat : ℝ) (hq : 0 < q)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hAT : 1 < β ^ 2 * (1 - 2 * q + qhat)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      δ * (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤
        (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ∧
      δ / ((N : ℝ) + 1) ≤ (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  obtain ⟨K, hK, hrem⟩ := sk_beyond_at_remainders β h q qhat hq hfix hqhat hAT
  -- the Gibbs averages of `n` replicas, for each `N`
  let ν₂ : (N : ℕ) → ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun N Φ =>
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  let ν₄ : (N : ℕ) → ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun N Φ =>
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  choose A hA using fun N => hrem N (ν₂ N) (fun _ => rfl) (ν₄ N) (fun _ => rfl)
  have hq01 : |q| ≤ 1 := by
    have := fixedPoint_mem_Icc hfix
    rw [abs_of_nonneg this.1]
    exact this.2
  have ha : 0 < 1 - 2 * q + qhat := by
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg β]
  let S2 : ℕ → ℝ := fun N => ν₂ N fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
    fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
  let S3 : ℕ → ℝ := fun N => ν₂ N fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
    fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3
  let T4 : ℕ → ℝ := fun N => ν₄ N fun σ => ((N + 1 : ℝ)⁻¹ *
    ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2
  have key : ∀ N : ℕ, 0 ≤ T4 N ∧ 0 ≤ S3 N ∧ S3 N ≤ 2 * S2 N ∧
      |T4 N - 4 / ((N : ℝ) + 1) * ((1 - 2 * q + qhat) / (1 - β ^ 2 * (1 - 2 * q + qhat)))| ≤
        K * ((Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 + S3 N) ∧
      |S2 N - A N| ≤ K * ((Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 + S3 N) ∧
      |A N| ≤ K / ((N : ℝ) + 1) := fun N => by
    obtain ⟨k1, k2, k3⟩ := hA N
    refine ⟨sk_avg_nonneg N β h 4 (ν₄ N) (fun _ => rfl) _ fun σ => sq_nonneg _,
      sk_avg_nonneg N β h 2 (ν₂ N) (fun _ => rfl) _ fun σ => by positivity, ?_, k1, k2, k3⟩
    have h2 := sk_replica_avg_smul N 2 β h (ν₂ N) (fun _ => rfl) 2
      (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2)
    rw [← h2]
    refine sk_replica_avg_mono N 2 β h (ν₂ N) (fun _ => rfl) _ _ fun σ => ?_
    have hx := abs_overlap_sub_le_two hq01 σ
    set x : ℝ := (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q
    have : |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs x]; ring
    rw [this]
    nlinarith [abs_nonneg x, sq_nonneg x]
  have hMN : ∀ M : ℕ, 1 ≤ M → (M : ℝ) = ((M - 1 : ℕ) : ℝ) + 1 := fun M hM => by
    rw [Nat.cast_sub hM]; ring
  obtain ⟨δ, hδ, M₀, hM₀⟩ := exists_cubic_lower_bounds (β := β) (a := 1 - 2 * q + qhat) (K := K)
    ha hAT hK (fun M => S2 (M - 1)) (fun M => S3 (M - 1)) (fun M => T4 (M - 1))
    (fun M => A (M - 1))
    (fun M => T4 (M - 1) - 4 / (M : ℝ) * ((1 - 2 * q + qhat) / (1 - β ^ 2 * (1 - 2 * q + qhat))))
    (fun M => S2 (M - 1) - A (M - 1))
    (fun M _ => (key (M - 1)).1)
    (fun M _ => by ring)
    (fun M _ => by ring)
    (fun M hM => by
      have := (key (M - 1)).2.2.2.2.2
      rw [hMN M hM]
      exact (le_abs_self _).trans this)
    (fun M hM => by
      have := (key (M - 1)).2.2.2.1
      rw [hMN M hM]
      exact this)
    (fun M hM => by
      have := (key (M - 1)).2.2.2.2.1
      rw [hMN M hM]
      exact this)
    (fun M _ => ⟨(key (M - 1)).2.1, (key (M - 1)).2.2.1⟩)
  refine ⟨δ, hδ, M₀, fun N hN => ?_⟩
  obtain ⟨h1, h2⟩ := hM₀ (N + 1) (by omega)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h1 h2
  exact ⟨h1, h2⟩

end SpinGlasses
