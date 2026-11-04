/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKBeyondATSolve
public import LeanMachineLearning.SpinGlasses.SKTBasisAlgebra

/-!
# Lemma 1.9.4 for the SK model

Beyond the Almeida--Thouless line the rectangular second moment and the overlap variance are
obtained from the covariance system (1.231)--(1.233) solved with the cubic remainder of
`sk_cov_row_bound_three`:

* `ν(((σ¹ - σ²)(σ³ - σ⁴)/M)²) = 4 (U - 2V + W)` exactly (`sk_rect_nu_eq`), and the system gives
  `(U - 2V + W) = c₂ / (M D₁) + O(E)`, which is Eq. (1.275);
* `U = ν((R₁₂ - q)²) = A² + 2B² + C² + O(E)`, Eq. (1.276),

where `E = K(β, h) (ν(|R_{1,2} - q|³) + M^{-3/2})` is Eq. (1.277).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.9.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix
open Matrix (atRowZero atRowOne atRowTwo)

namespace SpinGlasses

/-- **The rectangular second moment is `4 (U - 2V + W)`** (exact, for every `β`): with
`U = ν((R₁₂ - q)²)`, `V = ν((R₁₂ - q)(R₁₃ - q))`, `W = ν((R₁₂ - q)(R₃₄ - q))`,
`ν(((σ¹ - σ²)·(σ³ - σ⁴)/M)²) = 4 (U - 2V + W)`, because
`(σ¹ - σ²)·(σ³ - σ⁴)/M = (R₁₃ - q) - (R₁₄ - q) - (R₂₃ - q) + (R₂₄ - q)`. -/
theorem sk_rect_nu_eq (N : ℕ) (β h q : ℝ)
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₃ : ((Fin 3 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₃ : ∀ Φ, ν₃ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₄ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2) =
      4 * (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) -
        2 * ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) +
        ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))) := by
  obtain ⟨hadd, hsmul, -, -⟩ := sk_replica_avg_calculus N 4 β h ν₄ hν₄
  let ov : (Fin 4 → Fin (N + 1) → ℤˣ) → Fin 4 → Fin 4 → ℝ := fun σ i j =>
    (N + 1 : ℝ)⁻¹ * ((fun k : Fin (N + 1) => (σ i k : ℝ)) ⬝ᵥ fun k : Fin (N + 1) => (σ j k : ℝ)) - q
  have cls : ∀ p₁ p₂ r₁ r₂ : Fin 4, p₁ ≠ p₂ → r₁ ≠ r₂ →
      ν₄ (fun σ => ov σ p₁ p₂ * ov σ r₁ r₂) =
        if (p₁ = r₁ ∧ p₂ = r₂) ∨ (p₁ = r₂ ∧ p₂ = r₁) then
          ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q))
        else if p₁ = r₁ ∨ p₁ = r₂ ∨ p₂ = r₁ ∨ p₂ = r₂ then
          ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))
        else
          ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) :=
    fun p₁ p₂ r₁ r₂ hp hr => sk_nu_overlap_class N β h q ν₂ hν₂ ν₃ hν₃ ν₄ hν₄ ν₄ hν₄
      (fun r : Fin 4 => r) (fun _ _ h' => h') hp hr
  have hrect : ∀ σ : Fin 4 → Fin (N + 1) → ℤˣ,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2 =
        ov σ 0 2 * ov σ 0 2 + ov σ 0 3 * ov σ 0 3 + ov σ 1 2 * ov σ 1 2 + ov σ 1 3 * ov σ 1 3 +
          (-2) * (ov σ 0 2 * ov σ 0 3) + (-2) * (ov σ 0 2 * ov σ 1 2) +
          2 * (ov σ 0 2 * ov σ 1 3) + 2 * (ov σ 0 3 * ov σ 1 2) +
          (-2) * (ov σ 0 3 * ov σ 1 3) + (-2) * (ov σ 1 2 * ov σ 1 3) := fun σ => by
    simp only [ov, dotProduct, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have u1 := cls 0 2 0 2 (by decide) (by decide)
  have u2 := cls 0 3 0 3 (by decide) (by decide)
  have u3 := cls 1 2 1 2 (by decide) (by decide)
  have u4 := cls 1 3 1 3 (by decide) (by decide)
  have v1 := cls 0 2 0 3 (by decide) (by decide)
  have v2 := cls 0 2 1 2 (by decide) (by decide)
  have w1 := cls 0 2 1 3 (by decide) (by decide)
  have w2 := cls 0 3 1 2 (by decide) (by decide)
  have v3 := cls 0 3 1 3 (by decide) (by decide)
  have v4 := cls 1 2 1 3 (by decide) (by decide)
  simp only [hrect, hadd, hsmul]
  simp (config := { decide := true }) only [↓reduceIte] at u1 u2 u3 u4 v1 v2 v3 v4 w1 w2
  rw [u1, u2, u3, u4, v1, v2, v3, v4, w1, w2]
  ring

/-- **Talagrand's Lemma 1.9.4 for the SK model, valid for every `β`** (Eqs. (1.275)--(1.277)).
Let `q` be a fixed point, `q̂ = 𝔼 tanh⁴`, and suppose the denominators
`D₁ = 1 - β² (1 - 2q + q̂)` and `D₂ = 1 - β² (1 - 4q + 3q̂)` satisfy `δ ≤ |D_i|`
(beyond the AT line `D₁ < 0`, and `D₂ > 0` by `sk_beta_sq_mul_one_sub_four_add_three_lt_one`).
Put `M = N + 1`, `Δ = ν(|R_{1,2} - q|³)` and `E = K(β) (Δ + M^{-3/2})`.  Then
`ν(((σ¹ - σ²)(σ³ - σ⁴)/M)²) = 4 c₂ / (M D₁) + 𝓡₁` and `ν((R_{1,2} - q)²) = A² + 2B² + C² + 𝓡₂`
with `|𝓡₁| ≤ 16 E/δ`, `|𝓡₂| ≤ K(β, δ) E`, and `|A² + 2B² + C²| ≤ K(β, δ)/M`.  No condition
`4 β² < 1` and no moment bound on `R_{1,2} - q` is used. -/
theorem sk_lemma_194 (N : ℕ) (β q h qhat δ : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hδ : 0 < δ) (hD₁ : δ ≤ |1 - β ^ 2 * (1 - 2 * q + qhat)|)
    (hD₂ : δ ≤ |1 - β ^ 2 * (1 - 4 * q + 3 * qhat)|)
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₃ : ((Fin 3 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₃ : ∀ Φ, ν₃ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₄ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (E : ℝ)
    (hE : E = (2304 * β ^ 4 * Real.exp (256 * β ^ 2) * 32 +
        32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) * 4 + 3) +
        64 * β ^ 2 * Real.exp (144 * β ^ 2)) *
      (ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) +
        (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3)) :
    let c₂ := 1 - 2 * q + qhat
    let d := 1 - 4 * q + 3 * qhat
    let D₁ := 1 - β ^ 2 * c₂
    let D₂ := 1 - β ^ 2 * d
    let A2 := c₂ / (((N : ℝ) + 1) * D₁)
    let B2 := (q - qhat) / (((N : ℝ) + 1) * D₁ * D₂)
    let C2 := ((qhat - q ^ 2) / ((N : ℝ) + 1) + β ^ 2 * (qhat - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2) / D₂
    |ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2) -
        4 / ((N : ℝ) + 1) * (c₂ / D₁)| ≤ 16 / δ * E ∧
      |ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) - (A2 + 2 * B2 + C2)| ≤
        (16 / δ + (4 * β ^ 2 / δ + 36 * β ^ 2 / δ + 1) / δ) * E ∧
      |A2 + 2 * B2 + C2| ≤
        (1 / δ + 2 / δ ^ 2 + (1 + β ^ 2 / δ + 6 * β ^ 2 / δ ^ 2) / δ) / ((N : ℝ) + 1) := by
  intro c₂ d D₁ D₂ A2 B2 C2
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hqh_le : qhat ≤ q := qhat_le_of_fixedPoint β q h qhat hfix hqhat
  have hqh_ge : 0 ≤ qhat := by
    rw [← hqhat]
    exact integral_nonneg fun x => by positivity
  have hqhat01 : qhat ∈ Set.Icc (0 : ℝ) 1 := ⟨hqh_ge, hqh_le.trans hq.2⟩
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨ν₆, hν₆⟩ : ∃ ν₆ : ((Fin (4 + 2) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ, ∀ Φ, ν₆ Φ =
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin (4 + 2) → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin (4 + 2) => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨e⟩ : Nonempty (Option (Option (Fin 4)) ≃ Fin (4 + 2)) :=
    ⟨(Fintype.equivFin (Option (Option (Fin 4)))).trans (finCongr (by simp))⟩
  obtain ⟨R, hv, hR⟩ := sk_cov_system_of_row N β q h qhat e ν₂ hν₂ ν₃ hν₃ ν₄ hν₄ ν₆ hν₆ E
    fun {a c} hac => sk_cov_row_bound_three N β q h hfix qhat hqhat hqhat01 e ν₂ hν₂ ν₄ hν₄
      ν₆ hν₆ hac E hE
  have bu2 : skCavityBUnscaled q qhat 2 = 1 - q ^ 2 := by simp [skCavityBUnscaled]
  have bu1 : skCavityBUnscaled q qhat 1 = q - q ^ 2 := by simp [skCavityBUnscaled]
  have bu0 : skCavityBUnscaled q qhat 0 = qhat - q ^ 2 := by simp [skCavityBUnscaled]
  have hiff := (sk_at_covariance_equations_iff (skCavityBCoef β q qhat 2)
    (skCavityBCoef β q qhat 1) (skCavityBCoef β q qhat 0) q qhat ((N : ℝ) + 1) _ R).1 hv
  obtain ⟨e0, e1, e2⟩ := hiff
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, atRowZero, atRowOne, atRowTwo, skCavityBCoef, bu2, bu1, bu0] at e0 e1 e2
  have key := sk_at_scalar_solution_of_abs β q qhat ((N : ℝ) + 1)
    (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)))
    (ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)))
    (ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)))
    (R 0) (R 1) (R 2) E δ hM0 hδ hD₁ hD₂ hq.1 hq.2 hqh_ge hqh_le (hR 0) (hR 1) (hR 2)
    (by linear_combination e0) (by linear_combination e1) (by linear_combination e2)
  have hA := abs_at_leading_le β q qhat ((N : ℝ) + 1) δ hM0 hδ hD₁ hD₂ hq.1 hq.2 hqh_ge hqh_le
  have hrect := sk_rect_nu_eq N β h q ν₂ hν₂ ν₃ hν₃ ν₄ hν₄
  refine ⟨?_, key.2, hA⟩
  rw [hrect]
  have e4 : 4 / ((N : ℝ) + 1) * (c₂ / D₁) = 4 * A2 := by
    simp only [A2]
    field_simp
  rw [e4]
  have := key.1
  have e5 : 4 * (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) -
      2 * ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) +
      ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))) - 4 * A2 =
      4 * ((ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) -
      2 * ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) +
      ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))) - A2) := by ring
  rw [e5, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hR 0)
  calc 4 * |_| ≤ 4 * (4 * E / δ) := by gcongr
    _ = 16 / δ * E := by ring

end SpinGlasses
