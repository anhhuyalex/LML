/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenEvaluation
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenReducedSystem

/-!
# Evaluation of full rectangles in the reduced system (Talagrand, Eq. (1.355)-(1.357))

Step E4 of the proof of the even case of Theorem 1.11.1. The reduced `(N+1)`-spin system
`skCavityOldEnergy (N+1) β h g` has coupling `β / √(N+2)`, which equals `βm / √(N+1)` for the
reduced inverse temperature `βm`. Proposition 1.11.11 for `(βm, h, qm)` evaluates the product of
the full rectangles in that system; its overlaps are normalized by `(N+1)⁻¹`, the reduced
system's by `(N+2)⁻¹`, which costs a factor `((N+1)/(N+2))^p` for the `p` rectangles.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- **Proposition 1.11.11 in the reduced system.** For any `(βm, qm)` with the reduced coupling
and a fixed point `qm` of `βm`, the average of `η_V ∏_{J ∈ P} U_J` over the reduced system, with
rectangles normalized by `(N+2)⁻¹`, is `((N+1)/(N+2))^p` times the leading term of
Proposition 1.11.11 for `(βm, h, qm)`, up to `O((N+1)^{-(2p+1)/2})`. -/
theorem sk_hanen_reduced_full_rect_eval (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h βm q qm : ℝ),
      (∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 2 ∂gaussianReal 0 1 = qm) →
      βm ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ),
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * βm = (Real.sqrt ((N : ℝ) + 2))⁻¹ * β →
      ∀ (P : Finpartition.Pairing (univ : Finset (Fin (2 * p))))
      (x y : Fin (2 * p) → Fin n), (∀ j, x j ≠ y j) →
      (∀ u v : Fin (2 * p), u ≠ v →
        x u ≠ x v ∧ x u ≠ y v ∧ y u ≠ x v ∧ y u ≠ y v) →
      let αm := (∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * qm + 1
      let Am := αm / (1 - βm ^ 2 * αm)
      |(∫ g : FinPairs (N + 1) → ℝ, ∫ ρ : Fin n → Fin (N + 1) → ℤˣ,
          (∏ v : Fin (2 * p), ((ρ (x v) (Fin.last N) : ℝ) - (ρ (y v) (Fin.last N) : ℝ))) *
          P.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc (N + 1) n p q (fun j => (x j, y j)) u v ρ)
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy (N + 1) β h g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ p *
          (4 * (((N : ℝ) + 1)⁻¹ + βm ^ 2 * (Am / ((N : ℝ) + 1)))) ^ p *
          ∫ z : ℝ, (Real.cosh (βm * z * Real.sqrt qm + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1| ≤
      K / ((N : ℝ) + 1) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK, hKb⟩ := sk_hanen_full_rect_eval β₀ hβ₀ p n
  refine ⟨K, hK, ?_⟩
  intro β h βm q qm hfixm hβm N hcoef P x y hxy hdisj αm Am
  have key := hKb βm h qm hfixm hβm N P x y hxy hdisj
  dsimp only at key
  rw [skCavityPathMean_one] at key
  have henergy (g : FinPairs (N + 1) → ℝ) :
      (fun a : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * βm *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)) = skCavityOldEnergy (N + 1) β h g := by
    funext a
    rw [hcoef]
    simp only [skCavityOldEnergy, Nat.cast_succ, add_assoc, one_add_one_eq_two]
  simp_rw [henergy] at key
  have hparts : P.val.parts.card = p := P.card_parts_of_card_eq (m := p) (by simp)
  set θ : ℝ := ((N : ℝ) + 1) / ((N : ℝ) + 2) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  set Lead : ℝ := (4 * (((N : ℝ) + 1)⁻¹ + βm ^ 2 * (Am / ((N : ℝ) + 1)))) ^ p *
    ∫ z : ℝ, (Real.cosh (βm * z * Real.sqrt qm + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1 with hLead
  have hrect (ρ : Fin n → Fin (N + 1) → ℤˣ) (u v : Fin (2 * p)) :
      skCavityRectTrunc (N + 1) n p q (fun j => (x j, y j)) u v ρ =
        θ * ((N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (x u) i : ℝ) * (ρ (x v) i : ℝ)) -
          (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (y u) i : ℝ) * (ρ (x v) i : ℝ)) -
          (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (x u) i : ℝ) * (ρ (y v) i : ℝ)) +
          (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (y u) i : ℝ) * (ρ (y v) i : ℝ))) := by
    simp only [skCavityRectTrunc, dotProduct, hθ]
    push_cast
    have h1 : ((N : ℝ) + 1 + 1) = (N : ℝ) + 2 := by ring
    rw [h1]
    field_simp
    ring
  have hobs (ρ : Fin n → Fin (N + 1) → ℤˣ) :
      (∏ v : Fin (2 * p), ((ρ (x v) (Fin.last N) : ℝ) - (ρ (y v) (Fin.last N) : ℝ))) *
        P.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc (N + 1) n p q (fun j => (x j, y j)) u v ρ) =
      θ ^ p * ((∏ v : Fin (2 * p), ((ρ (x v) (Fin.last N) : ℝ) - (ρ (y v) (Fin.last N) : ℝ))) *
        P.blockProduct (Renormalization.pairWeight fun u v =>
          ((N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (x u) i : ℝ) * (ρ (x v) i : ℝ)) -
          (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (y u) i : ℝ) * (ρ (x v) i : ℝ)) -
          (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (x u) i : ℝ) * (ρ (y v) i : ℝ)) +
          (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ (y u) i : ℝ) * (ρ (y v) i : ℝ))))) := by
    simp_rw [hrect, Renormalization.pairWeight_const_mul,
      Renormalization.blockProduct_const_mul, hparts]
    ring
  simp_rw [hobs, integral_const_mul]
  have e2 : (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ p *
      (4 * (((N : ℝ) + 1)⁻¹ + βm ^ 2 * (Am / ((N : ℝ) + 1)))) ^ p *
      ∫ z : ℝ, (Real.cosh (βm * z * Real.sqrt qm + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1 =
      θ ^ p * Lead := by
    simp only [hθ, hLead]
    ring
  rw [e2]
  refine le_trans ?_ key
  rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hθ0 _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hθ0 hθ1)

end SpinGlasses
