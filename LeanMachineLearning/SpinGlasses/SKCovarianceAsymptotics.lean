/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCovarianceRows
public import LeanMachineLearning.SpinGlasses.SKTBasisAlgebra

/-!
# The overlap covariances to second order (Talagrand, Theorem 1.8.12)

For `β < 1/2` the three overlap covariances `U = ν((R₁₂ - q)²)`, `V = ν((R₁₂ - q)(R₁₃ - q))`,
`W = ν((R₁₂ - q)(R₃₄ - q))` of the `(N+1)`-spin SK system are
`U = A² + 2B² + C²`, `V = B² + C²`, `W = C²` up to `O(M^{-3/2})`, `M = N + 1`, where
`A², B², C²` are the limits of `ν(T₁₂²)`, `ν(T₁²)`, `ν(T²)` (Eqs. (1.248), (1.256), (1.262)).

The proof derives the covariance system (1.231)-(1.233) from the cavity expansion
(`sk_cov_system`) and solves it (`sk_at_scalar_solution`).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.8.12.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The error terms of the covariance system are `O(M^{-3/2})`.** -/
theorem cov_error_arith {β β₀ K₁ K₂ s : ℝ} (hs : 1 ≤ s) (hβ : β ^ 2 ≤ β₀ ^ 2)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
        (Real.sqrt ((8 * K₁ + 8) / s ^ 2) * Real.sqrt (K₂ / (s ^ 2) ^ 2)) +
      32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) *
          (Real.sqrt ((8 * K₂ + 8) / (s ^ 2) ^ 2) * Real.sqrt (K₁ / s ^ 2)) +
        (2 * ((K₁ + 1) / (2 * s)) / s ^ 2 + 1 / (s ^ 2) ^ 2)) +
      (s ^ 2)⁻¹ * (64 * β ^ 2 * Real.exp (144 * β ^ 2) * ((K₁ + 1) / (2 * s))) ≤
    (2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * (Real.sqrt (8 * K₁ + 8) * Real.sqrt K₂) +
      32 * β₀ ^ 2 * (72 * β₀ ^ 2 * Real.exp (256 * β₀ ^ 2) *
          (Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁) + (K₁ + 1) + 1) +
      32 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1)) / s ^ 3 := by
  have hs0 : 0 < s := by linarith
  have hb2 : 0 ≤ β ^ 2 := sq_nonneg _
  have hb4 : β ^ 4 ≤ β₀ ^ 4 := by
    have h1 : β ^ 4 = (β ^ 2) ^ 2 := by ring
    have h2 : β₀ ^ 4 = (β₀ ^ 2) ^ 2 := by ring
    rw [h1, h2]
    exact pow_le_pow_left₀ hb2 hβ 2
  have e1 : Real.exp (256 * β ^ 2) ≤ Real.exp (256 * β₀ ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (144 * β ^ 2) ≤ Real.exp (144 * β₀ ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  have sq1 : Real.sqrt ((8 * K₁ + 8) / s ^ 2) = Real.sqrt (8 * K₁ + 8) / s := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hs0.le]
  have sq2 : Real.sqrt (K₂ / (s ^ 2) ^ 2) = Real.sqrt K₂ / s ^ 2 := by
    rw [Real.sqrt_div hK₂, Real.sqrt_sq (by positivity)]
  have sq3 : Real.sqrt ((8 * K₂ + 8) / (s ^ 2) ^ 2) = Real.sqrt (8 * K₂ + 8) / s ^ 2 := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  have sq4 : Real.sqrt (K₁ / s ^ 2) = Real.sqrt K₁ / s := by
    rw [Real.sqrt_div hK₁, Real.sqrt_sq hs0.le]
  rw [sq1, sq2, sq3, sq4]
  have s3 : 0 < s ^ 3 := by positivity
  have hs3 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have T1 : 2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
      (Real.sqrt (8 * K₁ + 8) / s * (Real.sqrt K₂ / s ^ 2)) ≤
      2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) *
        (Real.sqrt (8 * K₁ + 8) * Real.sqrt K₂) / s ^ 3 := by
    have : Real.sqrt (8 * K₁ + 8) / s * (Real.sqrt K₂ / s ^ 2) =
        Real.sqrt (8 * K₁ + 8) * Real.sqrt K₂ / s ^ 3 := by field_simp
    rw [this, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ s3.le
    have h0 : 0 ≤ Real.sqrt (8 * K₁ + 8) * Real.sqrt K₂ := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hb4 (by norm_num)) e1 (by positivity)
        (by positivity)) h0
  have T2a : 72 * β ^ 2 * Real.exp (256 * β ^ 2) *
      (Real.sqrt (8 * K₂ + 8) / s ^ 2 * (Real.sqrt K₁ / s)) ≤
      72 * β₀ ^ 2 * Real.exp (256 * β₀ ^ 2) *
        (Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁) / s ^ 3 := by
    have : Real.sqrt (8 * K₂ + 8) / s ^ 2 * (Real.sqrt K₁ / s) =
        Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁ / s ^ 3 := by field_simp
    rw [this, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ s3.le
    have h0 : 0 ≤ Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁ := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hβ (by norm_num)) e1 (by positivity)
        (by positivity)) h0
  have T2b : 2 * ((K₁ + 1) / (2 * s)) / s ^ 2 = (K₁ + 1) / s ^ 3 := by
    field_simp
  have T2c : 1 / (s ^ 2) ^ 2 ≤ 1 / s ^ 3 := by
    have : (s ^ 2) ^ 2 = s ^ 4 := by ring
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num) s3 hs3
  have T3 : (s ^ 2)⁻¹ * (64 * β ^ 2 * Real.exp (144 * β ^ 2) * ((K₁ + 1) / (2 * s))) ≤
      32 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1) / s ^ 3 := by
    have : (s ^ 2)⁻¹ * (64 * β ^ 2 * Real.exp (144 * β ^ 2) * ((K₁ + 1) / (2 * s))) =
        32 * β ^ 2 * Real.exp (144 * β ^ 2) * (K₁ + 1) / s ^ 3 := by field_simp; ring
    rw [this]
    refine div_le_div_of_nonneg_right ?_ s3.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hβ (by norm_num)) e2 (by positivity)
        (by positivity)) (by linarith)
  have hβ32 : 32 * β ^ 2 ≤ 32 * β₀ ^ 2 := mul_le_mul_of_nonneg_left hβ (by norm_num)
  have hrhs : (2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * (Real.sqrt (8 * K₁ + 8) * Real.sqrt K₂) +
      32 * β₀ ^ 2 * (72 * β₀ ^ 2 * Real.exp (256 * β₀ ^ 2) *
          (Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁) + (K₁ + 1) + 1) +
      32 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1)) / s ^ 3 =
      2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * (Real.sqrt (8 * K₁ + 8) * Real.sqrt K₂) / s ^ 3 +
      32 * β₀ ^ 2 * (72 * β₀ ^ 2 * Real.exp (256 * β₀ ^ 2) *
          (Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁) / s ^ 3 + (K₁ + 1) / s ^ 3 + 1 / s ^ 3) +
      32 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1) / s ^ 3 := by ring
  rw [hrhs, T2b]
  have inner : 72 * β ^ 2 * Real.exp (256 * β ^ 2) *
      (Real.sqrt (8 * K₂ + 8) / s ^ 2 * (Real.sqrt K₁ / s)) + ((K₁ + 1) / s ^ 3 + 1 / (s ^ 2) ^ 2) ≤
      72 * β₀ ^ 2 * Real.exp (256 * β₀ ^ 2) * (Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁) / s ^ 3 +
        (K₁ + 1) / s ^ 3 + 1 / s ^ 3 := by
    linarith only [T2a, T2c]
  have hnn : 0 ≤ 72 * β ^ 2 * Real.exp (256 * β ^ 2) *
      (Real.sqrt (8 * K₂ + 8) / s ^ 2 * (Real.sqrt K₁ / s)) +
        ((K₁ + 1) / s ^ 3 + 1 / (s ^ 2) ^ 2) := by
    positivity
  have step : 32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) *
      (Real.sqrt (8 * K₂ + 8) / s ^ 2 * (Real.sqrt K₁ / s)) + ((K₁ + 1) / s ^ 3 +
        1 / (s ^ 2) ^ 2)) ≤
      32 * β₀ ^ 2 * (72 * β₀ ^ 2 * Real.exp (256 * β₀ ^ 2) *
        (Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁) / s ^ 3 + (K₁ + 1) / s ^ 3 + 1 / s ^ 3) :=
    mul_le_mul hβ32 inner hnn (by positivity)
  linarith only [T1, step, T3]

/-- **Talagrand's Theorem 1.8.12 (Eq. (1.265)).**  Let `4 β₀² < 1`.  There is `K` such that for
`|β| ≤ β₀`, the fixed point `q`, `q̂ = 𝔼 tanh⁴ (β √q z + h)` and every `N`, with `M = N + 1` and
the averages `ν₂, ν₃, ν₄` of two, three, four replicas of the `(N+1)`-spin system,
`U = ν((R₁₂ - q)²)`, `V = ν((R₁₂ - q)(R₁₃ - q))`, `W = ν((R₁₂ - q)(R₃₄ - q))`:
`U = A² + 2B² + C²`, `V = B² + C²`, `W = C²` up to `K / M^{3/2}`, where `c₂ = 1 - 2q + q̂`,
`d = 1 - 4q + 3q̂`, `D₁ = 1 - β² c₂`, `D₂ = 1 - β² d`, `A² = c₂/(M D₁)`,
`B² = (q - q̂)/(M D₁ D₂)`, `C² = ((q̂ - q²)/M + β²(q̂ - q²) A² + 2β²(2q + q² - 3q̂) B²)/D₂`
(Eqs. (1.248), (1.256), (1.262)). -/
theorem sk_overlap_covariances_nu (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β q qhat : ℝ), |β| ≤ β₀ →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 4 ∂(gaussianReal 0 1) = qhat) →
      ∀ (N : ℕ)
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (_ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₃ : ((Fin 3 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (_ : ∀ Φ, ν₃ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
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
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
      ,
      let c₂ := 1 - 2 * q + qhat
      let d := 1 - 4 * q + 3 * qhat
      let D₁ := 1 - β ^ 2 * c₂
      let D₂ := 1 - β ^ 2 * d
      let A2 := c₂ / (((N : ℝ) + 1) * D₁)
      let B2 := (q - qhat) / (((N : ℝ) + 1) * D₁ * D₂)
      let C2 := ((qhat - q ^ 2) / ((N : ℝ) + 1) + β ^ 2 * (qhat - q ^ 2) * A2 +
        2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2) / D₂
      |ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) - (A2 + 2 * B2 + C2)|
        ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 ∧
      |ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) - (B2 + C2)| ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 ∧
      |ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) - C2| ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
  obtain ⟨K₁, hK₁, hM1⟩ := sk_dev_moment_le β₀ hβ₀ 1
  obtain ⟨K₂, hK₂, hM2⟩ := sk_dev_moment_le β₀ hβ₀ 2
  set CE : ℝ := 2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * (Real.sqrt (8 * K₁ + 8) * Real.sqrt K₂) +
      32 * β₀ ^ 2 * (72 * β₀ ^ 2 * Real.exp (256 * β₀ ^ 2) *
          (Real.sqrt (8 * K₂ + 8) * Real.sqrt K₁) + (K₁ + 1) + 1) +
      32 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1) with hCE
  have hCE0 : 0 ≤ CE := by positivity
  refine ⟨44 * CE + 1, by positivity, fun β q qhat hβ hfix hqhat N ν₂ hν₂ ν₃ hν₃ ν₄ hν₄ => ?_⟩
  intro c₂ d D₁ D₂ A2 B2 C2
  have hβ2 : β ^ 2 ≤ β₀ ^ 2 := by
    rw [← sq_abs β]
    exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
  have hβ4 : 4 * β ^ 2 < 1 := by linarith
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hqh_le : qhat ≤ q := qhat_le_of_fixedPoint β q h qhat hfix hqhat
  have hqh_ge : 0 ≤ qhat := by
    rw [← hqhat]
    exact integral_nonneg fun x => by positivity
  have hqhat01 : qhat ∈ Set.Icc (0 : ℝ) 1 := ⟨hqh_ge, hqh_le.trans hq.2⟩
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hs1 : 1 ≤ Real.sqrt ((N : ℝ) + 1) := by
    rw [Real.one_le_sqrt]
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hs2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt hM0.le
  obtain ⟨ν₆, hν₆⟩ : ∃ ν₆ : ((Fin (4 + 2) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ, ∀ Φ, ν₆ Φ =
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin (4 + 2) → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin (4 + 2) => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨e⟩ : Nonempty (Option (Option (Fin 4)) ≃ Fin (4 + 2)) :=
    ⟨(Fintype.equivFin (Option (Option (Fin 4)))).trans (finCongr (by simp))⟩
  have hD2 := hM1 β h q hfix hβ2 N
  have hD4 := hM2 β h q hfix hβ2 N
  simp only [mul_one, pow_one] at hD2
  have hD2' : ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) ≤ K₁ / ((N : ℝ) + 1) := by
    rw [hν₂]; exact hD2
  have hD4' : ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4) ≤ K₂ / ((N : ℝ) + 1) ^ 2 := by
    rw [hν₂]; exact hD4
  set E : ℝ := 2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
        (Real.sqrt ((8 * K₁ + 8) / ((N : ℝ) + 1)) * Real.sqrt (K₂ / ((N : ℝ) + 1) ^ 2)) +
      32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) *
          (Real.sqrt ((8 * K₂ + 8) / ((N : ℝ) + 1) ^ 2) * Real.sqrt (K₁ / ((N : ℝ) + 1))) +
        (2 * ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))) / ((N : ℝ) + 1) +
          1 / ((N : ℝ) + 1) ^ 2)) +
      (N + 1 : ℝ)⁻¹ * (64 * β ^ 2 * Real.exp (144 * β ^ 2) *
        ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1)))) with hEdef
  obtain ⟨R, hv, hR⟩ := sk_cov_system N β q h hfix qhat hqhat hqhat01 K₁ K₂ hK₁.le hK₂.le e
    ν₂ hν₂ ν₃ hν₃ ν₄ hν₄ ν₆ hν₆ hD2' hD4' E hEdef
  have hEle : E ≤ CE / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
    have := cov_error_arith (s := Real.sqrt ((N : ℝ) + 1)) hs1 hβ2 hK₁.le hK₂.le
    rw [hs2] at this
    exact this
  have bu2 : skCavityBUnscaled q qhat 2 = 1 - q ^ 2 := by simp [skCavityBUnscaled]
  have bu1 : skCavityBUnscaled q qhat 1 = q - q ^ 2 := by simp [skCavityBUnscaled]
  have bu0 : skCavityBUnscaled q qhat 0 = qhat - q ^ 2 := by simp [skCavityBUnscaled]
  have hiff := (sk_at_covariance_equations_iff (skCavityBCoef β q qhat 2)
    (skCavityBCoef β q qhat 1) (skCavityBCoef β q qhat 0) q qhat ((N : ℝ) + 1) _ R).1 hv
  obtain ⟨e0, e1, e2⟩ := hiff
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, skAtRowZero, skAtRowOne, skAtRowTwo, skCavityBCoef, bu2, bu1, bu0] at e0 e1 e2
  set U := ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) with hU
  set V := ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) with hV
  set W := ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) with hW
  have key := sk_at_scalar_solution β q qhat ((N : ℝ) + 1) U V W (R 0) (R 1) (R 2) E hM0 hβ4 hq.1
    hq.2 hqh_ge hqh_le (hR 0) (hR 1) (hR 2) (by linear_combination e0) (by linear_combination e1)
    (by linear_combination e2)
  have hbd : 44 * E ≤ (44 * CE + 1) / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
    have hs3 : 0 < Real.sqrt ((N : ℝ) + 1) ^ 3 := by positivity
    calc 44 * E ≤ 44 * (CE / Real.sqrt ((N : ℝ) + 1) ^ 3) := by gcongr
      _ = 44 * CE / Real.sqrt ((N : ℝ) + 1) ^ 3 := by ring
      _ ≤ (44 * CE + 1) / Real.sqrt ((N : ℝ) + 1) ^ 3 :=
        div_le_div_of_nonneg_right (by linarith) hs3.le
  exact ⟨key.1.trans hbd, key.2.1.trans hbd, key.2.2.trans hbd⟩

/-- **Talagrand's Theorem 1.8.12 (Eq. (1.265)), with the averages written as integrals.**  See
`sk_overlap_covariances_nu` for the notation. -/
theorem sk_overlap_covariances (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β q qhat : ℝ), |β| ≤ β₀ →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 4 ∂(gaussianReal 0 1) = qhat) →
      ∀ N : ℕ,
      let c₂ := 1 - 2 * q + qhat
      let d := 1 - 4 * q + 3 * qhat
      let D₁ := 1 - β ^ 2 * c₂
      let D₂ := 1 - β ^ 2 * d
      let A2 := c₂ / (((N : ℝ) + 1) * D₁)
      let B2 := (q - qhat) / (((N : ℝ) + 1) * D₁ * D₂)
      let C2 := ((qhat - q ^ 2) / ((N : ℝ) + 1) + β ^ 2 * (qhat - q ^ 2) * A2 +
        2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2) / D₂
      |(∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) - (A2 + 2 * B2 + C2)|
        ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 ∧
      |(∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ,
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) - (B2 + C2)|
        ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 ∧
      |(∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) - C2|
        ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
  obtain ⟨K, hK, H⟩ := sk_overlap_covariances_nu β₀ hβ₀ h
  exact ⟨K, hK, fun β q qhat hβ hfix hqhat N =>
    H β q qhat hβ hfix hqhat N
      (fun Φ => ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (fun _ => rfl)
      (fun Φ => ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (fun _ => rfl)
      (fun Φ => ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (fun _ => rfl)⟩

end SpinGlasses
