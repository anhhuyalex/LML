/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeanTrick
public import LeanMachineLearning.SpinGlasses.SKSecondMoment

/-!
# The second moment of `T_{1,2}` (Talagrand, Proposition 1.8.7)

For the `(N+1)`-spin SK system, `M = N+1`, put `b_i = ⟨σ_i⟩` and
`T_{1,2} = (σ¹ - b)·(σ² - b)/M` (Eq. (1.245)).  Proposition 1.8.7 states
`ν(T_{1,2}²) = A² + O(3)` with `A² = (1 - 2q + q̂)/(M (1 - β²(1 - 2q + q̂)))`.

The book proves it by repeating the proof of Proposition 1.8.5 with six replicas.  Here it is a
corollary of Proposition 1.8.5 itself: the rectangle `(σ¹-σ²)·(σ³-σ⁴)/M` equals
`T_{13} - T_{14} - T_{23} + T_{24}`, and the four squares have the same average while the cross
terms vanish, so `ν(rect²) = 4 ν(T_{1,2}²)` exactly (`integral_rect_sq_eq_four_mul_dev_dot_sq`).
Together with the six-replica form of the Gibbs-mean trick (`GibbsMeanTrick.lean`), which is
the book's route, both give the same value `M⁻² ∑_{ij} C_ij²`.

## Main declaration

* `SpinGlasses.sk_dev_pair_second_moment`: Proposition 1.8.7 with an explicit error
  `K / (N+1)^{3/2}`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.8.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Talagrand's Proposition 1.8.7 (Eq. (1.247)-(1.248)).**  For `|β| ≤ β₀ < 1/2` and `q` the
fixed point, with `b g i = ⟨σ_i⟩` the Gibbs mean of the `(N+1)`-spin system,
`ν(T_{1,2}²) = c₂ / ((N+1) (1 - β² c₂)) + O((N+1)^{-3/2})`, `c₂ = 1 - 2q + q̂`, with an error
`K / (N+1)^{3/2}` where `K` is independent of `N`, `β`, `q`. -/
theorem sk_dev_pair_second_moment (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β q : ℝ), |β| ≤ β₀ →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ (N : ℕ) (b : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ),
      (∀ g i, b g i = ∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ)
        ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) →
      |(∫ g : FinPairs (N + 1) → ℝ, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b g i) * (((τ 1 i : ℤˣ) : ℝ) - b g i)) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        ((∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1) /
          (((N : ℝ) + 1) * (1 - β ^ 2 * ((∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
            ∂(gaussianReal 0 1)) - 2 * q + 1)))| ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
  obtain ⟨K, hK, hmain⟩ := sk_rect_second_moment β₀ hβ₀ h
  refine ⟨K / 4, by positivity, fun β q hβ hfix N b hb => ?_⟩
  have h5 := hmain β q hβ hfix N
  set c₂ : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1
  set Tsq : ℝ := ∫ g : FinPairs (N + 1) → ℝ, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b g i) * (((τ 1 i : ℤˣ) : ℝ) - b g i)) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) with hTsq
  have hrect : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2
          ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = 4 * Tsq := by
    rw [hTsq, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have := integral_rect_sq_eq_four_mul_dev_dot_sq
      (M := N + 1) (fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)) (b g) (hb g)
    simpa [dotProduct, Nat.cast_add, Nat.cast_one] using this
  rw [hrect] at h5
  have hs : 0 < Real.sqrt ((N : ℝ) + 1) ^ 3 := by positivity
  have hrew : Tsq - c₂ / (((N : ℝ) + 1) * (1 - β ^ 2 * c₂)) =
      (4 * Tsq - 4 * c₂ / (((N : ℝ) + 1) * (1 - β ^ 2 * c₂))) / 4 := by ring
  rw [hrew, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc _ ≤ (K / Real.sqrt ((N : ℝ) + 1) ^ 3) / 4 := by gcongr
    _ = _ := by ring

end SpinGlasses
