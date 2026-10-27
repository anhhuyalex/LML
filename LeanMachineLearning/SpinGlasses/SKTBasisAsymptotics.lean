/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCovarianceAsymptotics

/-!
# The second moments of `T₁` and `T` (Talagrand, Propositions 1.8.10 and 1.8.11)

With `b = ⟨σ⟩` the Gibbs mean, `T₁ = (σ¹ - b)·b/M` and `T = b·b/M - q`.  Averaged over the
Gibbs measure, `⟨T₁²⟩ = M⁻² ∑_{ij} C_ij b_ib_j = V_G - W_G` and `T² = W_G`, where `V_G`, `W_G` are
the Gibbs averages of `(R₁₂ - q)(R₁₃ - q)` and `(R₁₂ - q)(R₃₄ - q)`
(`GibbsOverlapCovariances.lean`).  Averaging over the disorder, `ν(T₁²) = V - W` and `ν(T²) = W`, so
Propositions 1.8.10 and 1.8.11 are corollaries of Theorem 1.8.12 (`SKCovarianceAsymptotics.lean`).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Propositions 1.8.10, 1.8.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- One replica: the Gibbs average of `((σ¹ - b)·b/M)²` is `M⁻² ∑_{ij} C_ij b_i b_j`. -/
theorem integral_T1_sq {M : ℕ} (A : (Fin M → ℤˣ) → ℝ) (b : Fin M → ℝ)
    (hb : ∀ i, b i = ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) ∂(Measure.count.tilted A))
    (m : Fin M → Fin M → ℝ)
    (hm : ∀ i j, m i j = ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ)
      ∂(Measure.count.tilted A)) :
    ∫ τ : Fin 1 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b i) * b i) ^ 2
        ∂(Measure.pi fun _ : Fin 1 => Measure.count.tilted A) =
      ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m i j - b i * b j) * (b i * b j) := by
  set μ : Measure (Fin M → ℤˣ) := Measure.count.tilted A with hμ
  have hone : ∀ f : (Fin M → ℤˣ) → ℝ,
      ∫ τ : Fin 1 → Fin M → ℤˣ, f (τ 0) ∂(Measure.pi fun _ : Fin 1 => μ) = ∫ x, f x ∂μ :=
    fun f => MeasureTheory.integral_comp_eval (i := (0 : Fin 1))
      Integrable.of_finite.aestronglyMeasurable
  have hexp : ∀ τ : Fin 1 → Fin M → ℤˣ,
      ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b i) * b i) ^ 2 =
        ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (b i * b j) *
          ((((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 0 j : ℤˣ) : ℝ) - b j)) := fun τ => by
    rw [mul_pow, sq (∑ i, _), Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => Integrable.of_finite]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hone (fun x => (b i * b j) * ((((x i : ℤˣ) : ℝ) - b i) * (((x j : ℤˣ) : ℝ) - b j)))
  rw [this, integral_const_mul, integral_dev_mul_dev A b hb i j, ← hm i j]
  ring

/-- The overlap of the `(N+1)`-spin system written with a dot product equals the sum form. -/
theorem overlap_eq_sum (N : ℕ) {n : ℕ} (σ : Fin n → Fin (N + 1) → ℤˣ) (a b : Fin n) :
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ b i : ℝ)) =
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ i, ((σ a i : ℤˣ) : ℝ) * ((σ b i : ℤˣ) : ℝ) := by
  simp [dotProduct]

/-- **Propositions 1.8.10 and 1.8.11 (second moments of `T₁` and `T`).**  For `4 β₀² < 1` there
is `K` such that for `|β| ≤ β₀`, `q` the fixed point, `q̂ = 𝔼 tanh⁴`, every `N` and the Gibbs mean
`b g i = ⟨σ_i⟩` of the `(N+1)`-spin system, with `M = N + 1`,
`ν(T₁²) = B² + O(M^{-3/2})` and `ν(T²) = C² + O(M^{-3/2})`, where
`B² = (q - q̂)/(M D₁ D₂)`, `C² = ((q̂ - q²)/M + β²(q̂ - q²) A² + 2β²(2q + q² - 3q̂) B²)/D₂`,
`T₁ = (σ¹ - b)·b/M`, `T = b·b/M - q`. -/
theorem sk_T_basis_second_moments (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β q qhat : ℝ), |β| ≤ β₀ →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 4 ∂(gaussianReal 0 1) = qhat) →
      ∀ (N : ℕ) (b : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ),
      (∀ g i, b g i = ∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ)
        ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) →
      let c₂ := 1 - 2 * q + qhat
      let d := 1 - 4 * q + 3 * qhat
      let D₁ := 1 - β ^ 2 * c₂
      let D₂ := 1 - β ^ 2 * d
      let A2 := c₂ / (((N : ℝ) + 1) * D₁)
      let B2 := (q - qhat) / (((N : ℝ) + 1) * D₁ * D₂)
      let C2 := ((qhat - q ^ 2) / ((N : ℝ) + 1) + β ^ 2 * (qhat - q ^ 2) * A2 +
        2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2) / D₂
      |(∫ g : FinPairs (N + 1) → ℝ, ∫ τ : Fin 1 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b g i) * b g i) ^ 2
          ∂(Measure.pi fun _ : Fin 1 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) - B2|
        ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 ∧
      |(∫ g : FinPairs (N + 1) → ℝ,
          ((N + 1 : ℝ)⁻¹ * ∑ i, b g i * b g i - q) ^ 2
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) - C2|
        ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
  obtain ⟨K, hK, H⟩ := sk_overlap_covariances β₀ hβ₀ h
  refine ⟨2 * K, by positivity, fun β q qhat hβ hfix hqhat N b hb => ?_⟩
  intro c₂ d D₁ D₂ A2 B2 C2
  obtain ⟨-, hVb, hWb⟩ := H β q qhat hβ hfix hqhat N
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
    (Real.sqrt (N + 1))⁻¹ * β *
      (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
    h * ∑ i : Fin (N + 1), (a i : ℝ)
  let m : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → Fin (N + 1) → ℝ := fun g i j =>
    ∫ y : Fin (N + 1) → ℤˣ, ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ) ∂(Measure.count.tilted (Esk g))
  -- the Gibbs-level identities, pointwise in the disorder
  have gX : ∀ g, ∫ τ : Fin 1 → Fin (N + 1) → ℤˣ,
      ((N + 1 : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b g i) * b g i) ^ 2
        ∂(Measure.pi fun _ : Fin 1 => Measure.count.tilted (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) =
      ((N + 1 : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m g i j - b g i * b g j) * (b g i * b g j) := fun g => by
    have := integral_T1_sq (Esk g) (b g) (hb g) (m g) (fun _ _ => rfl)
    rwa [hcast] at this
  have gV : ∀ g, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i :
    ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) =
      ((N + 1 : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m g i j - b g i * b g j) * (b g i * b g j) +
        ((N + 1 : ℝ)⁻¹ * ∑ i, b g i * b g i - q) ^ 2 := fun g => by
    have := integral_overlap_mul_overlap_eq (Esk g) q (b g) (hb g) (m g) (fun _ _ => rfl)
    simp only [hcast] at this
    simp_rw [overlap_eq_sum N, hcast]
    exact this
  have gW : ∀ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i :
    ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) =
      ((N + 1 : ℝ)⁻¹ * ∑ i, b g i * b g i - q) ^ 2 := fun g => by
    have := integral_overlap_mul_overlap_disjoint_eq (Esk g) q (b g) (hb g)
    simp only [hcast] at this
    simp_rw [overlap_eq_sum N, hcast]
    exact this
  have hXint : (∫ g : FinPairs (N + 1) → ℝ, ∫ τ : Fin 1 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b g i) * b g i) ^ 2
          ∂(Measure.pi fun _ : Fin 1 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
        (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
        (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
    rw [← integral_sub (integrable_integral_sk_replica N 3 β h (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i :
      Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)))
      (integrable_integral_sk_replica N 4 β h (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) =>
        (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)))]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    beta_reduce
    rw [gX g, gV g, gW g]
    ring
  have hTint : (∫ g : FinPairs (N + 1) → ℝ,
          ((N + 1 : ℝ)⁻¹ * ∑ i, b g i * b g i - q) ^ 2
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
        (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    beta_reduce
    rw [gW g]
  rw [hXint, hTint]
  have a1 := abs_le.1 hVb
  have a2 := abs_le.1 hWb
  have hKK : K / Real.sqrt ((N : ℝ) + 1) ^ 3 ≤ 2 * K / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
    gcongr
    linarith
  refine ⟨?_, hWb.trans hKK⟩
  have e2 : 2 * K / Real.sqrt ((N : ℝ) + 1) ^ 3 = 2 * (K / Real.sqrt ((N : ℝ) + 1) ^ 3) := by
    ring
  rw [abs_le, e2]
  constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2]

end SpinGlasses
