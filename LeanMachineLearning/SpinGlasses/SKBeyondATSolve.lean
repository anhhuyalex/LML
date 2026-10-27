/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKBeyondATRows

/-!
# Solving the covariance system beyond the Almeida--Thouless line

`sk_at_scalar_solution` divides by `D₁ = 1 - β² (1 - 2q + q̂)` and `D₂ = 1 - β² (1 - 4q + 3q̂)`
using `4β² < 1`, which gives `D_i ≥ 3/4`.  Beyond the AT line `D₁ < 0`, and `D₂ > 0` only by
Lemma 1.9.3, so here the denominators are only assumed to satisfy `δ ≤ |D_i|` and the constants
depend on `δ` and `β` (Talagrand, proof of Lemma 1.9.4: "we are permitted to divide by
`1 - β²(1 - 2q + q̂)` and `1 - β²(1 - 4q + 3q̂)`").

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.9.
-/

@[expose] public section

open scoped BigOperators

namespace SpinGlasses

/-- The error bookkeeping of the covariance system with denominators bounded below in absolute
value by `δ`: with `a = ρ₁/D₁`, `b' = (ρ₁/D₁ - ρ₂/D₂)/2`, `w = (b₀ a + g b' + R₂)/D₂`,
`δ ≤ |D_i|`, `|R_i| ≤ E`, `|b₀| ≤ B`, `|g| ≤ G`, one has `|a| ≤ 4E/δ`, `|b'| ≤ 6E/δ` and
`|w| ≤ (4 B/δ + 6 G/δ + 1) E/δ`. -/
theorem at_error_bound_of_abs {a b' w D₁ D₂ b₀ g R₀ R₁ R₂ E δ B G : ℝ} (hδ : 0 < δ)
    (hD₁ : δ ≤ |D₁|) (hD₂ : δ ≤ |D₂|)
    (hR₀ : |R₀| ≤ E) (hR₁ : |R₁| ≤ E) (hR₂ : |R₂| ≤ E) (hb₀ : |b₀| ≤ B) (hg : |g| ≤ G)
    (ha : a = (R₀ - 2 * R₁ + R₂) / D₁)
    (hb : b' = ((R₀ - 2 * R₁ + R₂) / D₁ - (R₀ - 4 * R₁ + 3 * R₂) / D₂) / 2)
    (hw : w = (b₀ * a + g * b' + R₂) / D₂) :
    |a| ≤ 4 * E / δ ∧ |b'| ≤ 6 * E / δ ∧ |w| ≤ (4 * B / δ + 6 * G / δ + 1) * E / δ := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hR₀
  have hB : 0 ≤ B := (abs_nonneg _).trans hb₀
  have hG : 0 ≤ G := (abs_nonneg _).trans hg
  have hR : ∀ i : Fin 3, |![R₀, R₁, R₂] i| ≤ E := fun i => by fin_cases i <;> assumption
  have hρ1 : |R₀ - 2 * R₁ + R₂| ≤ 4 * E := by
    have h := Weights.abs_weighted_sum_le ![1, -2, 1] _ hR
    simp only [Fin.sum_univ_three] at h
    norm_num at h
    convert h using 2
  have hρ2 : |R₀ - 4 * R₁ + 3 * R₂| ≤ 8 * E := by
    have h := Weights.abs_weighted_sum_le ![1, -4, 3] _ hR
    simp only [Fin.sum_univ_three] at h
    norm_num at h
    convert h using 2
  have q1 := abs_div_le_div_of_le_abs hδ hD₁ hρ1
  have q2 := abs_div_le_div_of_le_abs hδ hD₂ hρ2
  have hα' : |a| ≤ 4 * E / δ := by rw [ha]; exact q1
  have hB' : |b'| ≤ 6 * E / δ := by
    rw [hb]
    have a1 := abs_le.1 q1
    have a2 := abs_le.1 q2
    have e6 : 6 * E / δ = (4 * E / δ + 8 * E / δ) / 2 := by ring
    rw [e6, abs_le]; constructor <;> linarith
  have hnumW : |b₀ * a + g * b' + R₂| ≤ B * (4 * E / δ) + G * (6 * E / δ) + E := by
    have t1 : |b₀ * a| ≤ B * (4 * E / δ) := by
      rw [abs_mul]; exact mul_le_mul hb₀ hα' (abs_nonneg _) hB
    have t2 : |g * b'| ≤ G * (6 * E / δ) := by
      rw [abs_mul]; exact mul_le_mul hg hB' (abs_nonneg _) hG
    have a1 := abs_le.1 t1; have a2 := abs_le.1 t2; have c3 := abs_le.1 hR₂
    rw [abs_le]; constructor <;> linarith
  refine ⟨hα', hB', ?_⟩
  rw [hw]
  refine (abs_div_le_div_of_le_abs hδ hD₂ hnumW).trans (le_of_eq ?_)
  ring

/-- **Solving the covariance system beyond the AT line (the algebra of Lemma 1.9.4).**  With the
hypotheses of `sk_at_scalar_solution`, except that `4 β² < 1` is replaced by `δ ≤ |D₁|`,
`δ ≤ |D₂|`, one has
`|(U - 2V + W) - A²| ≤ 4E/δ` and `|U - (A² + 2B² + C²)| ≤ K(β, δ) E`. -/
theorem sk_at_scalar_solution_of_abs (β q qhat M U V W R₀ R₁ R₂ E δ : ℝ) (hM : 0 < M)
    (hδ : 0 < δ) (hD₁ : δ ≤ |1 - β ^ 2 * (1 - 2 * q + qhat)|)
    (hD₂ : δ ≤ |1 - β ^ 2 * (1 - 4 * q + 3 * qhat)|)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqh0 : 0 ≤ qhat) (hqhq : qhat ≤ q)
    (hR₀ : |R₀| ≤ E) (hR₁ : |R₁| ≤ E) (hR₂ : |R₂| ≤ E)
    (h₀ : U = (1 - q ^ 2) / M + (β ^ 2 * (1 - q ^ 2) * U - 4 * (β ^ 2 * (q - q ^ 2)) * V +
      3 * (β ^ 2 * (qhat - q ^ 2)) * W) + R₀)
    (h₁ : V = (q - q ^ 2) / M + (β ^ 2 * (q - q ^ 2) * U +
      (β ^ 2 * (1 - q ^ 2) - 2 * (β ^ 2 * (q - q ^ 2)) - 3 * (β ^ 2 * (qhat - q ^ 2))) * V +
      (6 * (β ^ 2 * (qhat - q ^ 2)) - 3 * (β ^ 2 * (q - q ^ 2))) * W) + R₁)
    (h₂ : W = (qhat - q ^ 2) / M + (β ^ 2 * (qhat - q ^ 2) * U +
      (4 * (β ^ 2 * (q - q ^ 2)) - 8 * (β ^ 2 * (qhat - q ^ 2))) * V +
      (β ^ 2 * (1 - q ^ 2) - 8 * (β ^ 2 * (q - q ^ 2)) + 10 * (β ^ 2 * (qhat - q ^ 2))) * W) +
      R₂) :
    let c₂ := 1 - 2 * q + qhat
    let d := 1 - 4 * q + 3 * qhat
    let D₁ := 1 - β ^ 2 * c₂
    let D₂ := 1 - β ^ 2 * d
    let A2 := c₂ / (M * D₁)
    let B2 := (q - qhat) / (M * D₁ * D₂)
    let C2 := ((qhat - q ^ 2) / M + β ^ 2 * (qhat - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2) / D₂
    |(U - 2 * V + W) - A2| ≤ 4 * E / δ ∧
      |U - (A2 + 2 * B2 + C2)| ≤ (16 / δ + (4 * β ^ 2 / δ + 36 * β ^ 2 / δ + 1) / δ) * E := by
  intro c₂ d D₁ D₂ A2 B2 C2
  have hE : 0 ≤ E := (abs_nonneg _).trans hR₀
  have hb0 : 0 ≤ β ^ 2 := sq_nonneg β
  have hD₁' : δ ≤ |D₁| := hD₁
  have hD₂' : δ ≤ |D₂| := hD₂
  have hD₁0 : D₁ ≠ 0 := fun h0 => by
    rw [h0, abs_zero] at hD₁'
    linarith
  have hD₂0 : D₂ ≠ 0 := fun h0 => by
    rw [h0, abs_zero] at hD₂'
    linarith
  obtain ⟨hαA, hBB, hWC⟩ := sk_at_exact_errors (β := β) (q := q) (qhat := qhat) (M := M)
    hM.ne' rfl rfl rfl rfl hD₁0 hD₂0 rfl rfl rfl h₀ h₁ h₂
  set α : ℝ := U - 2 * V + W with hα
  set B : ℝ := V - W with hB
  set b0 : ℝ := β ^ 2 * (qhat - q ^ 2) with hb0def
  set g : ℝ := 2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) with hg
  have hb0' : |b0| ≤ β ^ 2 := by
    rw [hb0def, abs_mul, abs_of_nonneg hb0]
    have : |qhat - q ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith only [hq0, hq1, hqh0, hqhq]
    nlinarith only [this, hb0, abs_nonneg (qhat - q ^ 2)]
  have hg' : |g| ≤ 6 * β ^ 2 := by
    rw [hg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hb0]
    have : |2 * q + q ^ 2 - 3 * qhat| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith only [hq0, hq1, hqh0, hqhq]
    nlinarith only [this, hb0, abs_nonneg (2 * q + q ^ 2 - 3 * qhat)]
  obtain ⟨hα', hB', hW'⟩ := at_error_bound_of_abs (a := α - A2) (b' := B - B2) (w := W - C2)
    hδ hD₁' hD₂' hR₀ hR₁ hR₂ hb0' hg' hαA hBB hWC
  refine ⟨hα', ?_⟩
  have hU : U - (A2 + 2 * B2 + C2) = (α - A2) + 2 * (B - B2) + (W - C2) := by
    simp only [hα, hB]; ring
  rw [hU]
  have a1 := abs_le.1 hα'; have a2 := abs_le.1 hB'; have c3 := abs_le.1 hW'
  have hsum : 4 * E / δ + 2 * (6 * E / δ) +
      (4 * β ^ 2 / δ + 6 * (6 * β ^ 2) / δ + 1) * E / δ =
      (16 / δ + (4 * β ^ 2 / δ + 36 * β ^ 2 / δ + 1) / δ) * E := by ring
  rw [abs_le]
  constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, c3.1, c3.2, hsum]

/-- **The leading terms are `O(1/M)`:** with `δ ≤ |D₁|`, `δ ≤ |D₂|`,
`|A² + 2B² + C²| ≤ (1/δ + 2/δ² + (1 + β²/δ + 6β²/δ²)/δ) / M`. -/
theorem abs_at_leading_le (β q qhat M δ : ℝ) (hM : 0 < M) (hδ : 0 < δ)
    (hD₁ : δ ≤ |1 - β ^ 2 * (1 - 2 * q + qhat)|)
    (hD₂ : δ ≤ |1 - β ^ 2 * (1 - 4 * q + 3 * qhat)|)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqh0 : 0 ≤ qhat) (hqhq : qhat ≤ q) :
    let c₂ := 1 - 2 * q + qhat
    let d := 1 - 4 * q + 3 * qhat
    let D₁ := 1 - β ^ 2 * c₂
    let D₂ := 1 - β ^ 2 * d
    let A2 := c₂ / (M * D₁)
    let B2 := (q - qhat) / (M * D₁ * D₂)
    let C2 := ((qhat - q ^ 2) / M + β ^ 2 * (qhat - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2) / D₂
    |A2 + 2 * B2 + C2| ≤
      (1 / δ + 2 / δ ^ 2 + (1 + β ^ 2 / δ + 6 * β ^ 2 / δ ^ 2) / δ) / M := by
  intro c₂ d D₁ D₂ A2 B2 C2
  have hb0 : 0 ≤ β ^ 2 := sq_nonneg β
  have hD₁' : δ ≤ |D₁| := hD₁
  have hD₂' : δ ≤ |D₂| := hD₂
  have hMδ : M * δ ≤ |M * D₁| := by
    rw [abs_mul, abs_of_pos hM]; exact mul_le_mul_of_nonneg_left hD₁' hM.le
  have hMδ2 : M * (δ * δ) ≤ |M * D₁ * D₂| := by
    rw [abs_mul, abs_mul, abs_of_pos hM, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hD₁' hD₂' hδ.le (abs_nonneg _)) hM.le
  have hc₂ : |c₂| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith only [hq0, hq1, hqh0, hqhq]
  have hqq : |q - qhat| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith only [hq0, hq1, hqh0, hqhq]
  have hA : |A2| ≤ 1 / (M * δ) := by
    have := abs_div_le_div_of_le_abs (mul_pos hM hδ) hMδ hc₂
    simpa [A2] using this
  have hB : |B2| ≤ 1 / (M * (δ * δ)) := by
    have := abs_div_le_div_of_le_abs (mul_pos hM (mul_pos hδ hδ)) hMδ2 hqq
    simpa [B2] using this
  have h1 : |qhat - q ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith only [hq0, hq1, hqh0, hqhq]
  have h2 : |2 * q + q ^ 2 - 3 * qhat| ≤ 3 := by
    rw [abs_le]; constructor <;> nlinarith only [hq0, hq1, hqh0, hqhq]
  have hnum : |(qhat - q ^ 2) / M + β ^ 2 * (qhat - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2| ≤
      1 / M + β ^ 2 * (1 / (M * δ)) + 2 * β ^ 2 * 3 * (1 / (M * (δ * δ))) := by
    have t1 : |(qhat - q ^ 2) / M| ≤ 1 / M := by
      rw [abs_div, abs_of_pos hM]; exact div_le_div_of_nonneg_right h1 hM.le
    have t2 : |β ^ 2 * (qhat - q ^ 2) * A2| ≤ β ^ 2 * (1 / (M * δ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb0]
      calc β ^ 2 * |qhat - q ^ 2| * |A2| ≤ β ^ 2 * 1 * (1 / (M * δ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hb0) hA (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have u3 : |2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2| ≤
        2 * β ^ 2 * 3 * (1 / (M * (δ * δ))) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hb0]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) hB (abs_nonneg _)
        (by positivity)
    have a1 := abs_le.1 t1
    have a2 := abs_le.1 t2
    have c3 := abs_le.1 u3
    rw [abs_le]
    constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, c3.1, c3.2]
  have hC : |C2| ≤ (1 / M + β ^ 2 * (1 / (M * δ)) + 2 * β ^ 2 * 3 * (1 / (M * (δ * δ)))) / δ :=
    abs_div_le_div_of_le_abs hδ hD₂' hnum
  have a1 := abs_le.1 hA
  have a2 := abs_le.1 hB
  have c3 := abs_le.1 hC
  have hsum : 1 / (M * δ) + 2 * (1 / (M * (δ * δ))) +
      (1 / M + β ^ 2 * (1 / (M * δ)) + 2 * β ^ 2 * 3 * (1 / (M * (δ * δ)))) / δ =
      (1 / δ + 2 / δ ^ 2 + (1 + β ^ 2 / δ + 6 * β ^ 2 / δ ^ 2) / δ) / M := by
    field_simp
    ring
  rw [← hsum, abs_le]
  constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, c3.1, c3.2]

end SpinGlasses
