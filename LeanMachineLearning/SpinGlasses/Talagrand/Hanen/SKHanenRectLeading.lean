/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangularTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairing

/-!
# Leading Taylor term of the rectangular product (Talagrand, Eq. (1.342) and (1.337))

Step E3b of the proof of Proposition 1.11.10: the Taylor leading term of
`sk_hanen_rect_product_taylor` is evaluated with Theorem 1.11.9
(`sk_hanen_pairing_derivative`) and the Wick sum is split into its pairings.
Everything is expressed through the cavity path mean at `u = 0` of an old-spin function, so no
new definition is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- At `u = 0` the cavity path mean of a function of the old spins only is the decoupled
disorder average of its Gibbs mean (the last spin integrates out because the tilted counting
measures are probability measures). -/
theorem skCavityPathMean_zero_old (N n : ℕ) (β q h : ℝ)
    (G : (Fin n → Fin N → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h 0 (fun σ => G (fun k i => σ k i.castSucc)) =
      ∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  have h1 := skCavityPathMean_zero_mul N n β q h G (fun _ => 1)
  simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using h1


/-- **Steps E3b of Proposition 1.11.10.** For an arbitrary pairing `P₀` the Taylor leading term of
`η_V f̂ ∏_{J ∈ P₀} U_J⁻` is `β^{2m} 𝔼(⟨f̂⟩₀ ch^{-4m}Y) ∑_P ν₀(∏_{P₀} U⁻ ∏_P U⁻)`, where the sum
is over all pairings `P` of the `2m` difference labels and `ν₀` is the cavity-path mean at
`u = 0` (the decoupled average, in which the old spins form the `N`-spin system).
The factor `m!` of Theorem 1.11.9 cancels the `1/m!` of the Taylor term. -/
theorem sk_hanen_rect_leading (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P₀ : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n), (∀ v, (pairMap v).1 ≠ (pairMap v).2) →
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      ∀ (fhat : (Fin n → ℤˣ) → ℝ) (M : ℝ), (∀ ε, |fhat ε| ≤ M) →
      (∀ ε i t, i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
        fhat (Function.update ε i t) = fhat ε) →
      let U := fun (u v : Fin (2 * m)) (ρ : Fin n → Fin N → ℤˣ) =>
        skCavityRectTrunc N n m q pairMap u v ρ
      |skCavityPathMean N n β q h 1 (fun σ =>
          (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
            (σ (pairMap w).2 (Fin.last N) : ℝ))) * fhat (fun r => σ r (Fin.last N)) *
          P₀.blockProduct (Renormalization.pairWeight fun u v =>
            U u v (fun r i => σ r i.castSucc))) -
        β ^ (2 * m) * (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹ ∂gaussianReal 0 1) *
          ∑ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
            skCavityPathMean N n β q h 0 (fun σ =>
              P₀.blockProduct (Renormalization.pairWeight fun u v =>
                U u v (fun r i => σ r i.castSucc)) *
              P.blockProduct (Renormalization.pairWeight fun u v =>
                U u v (fun r i => σ r i.castSucc)))| ≤
      K * M / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK, hKb⟩ := sk_hanen_rect_product_taylor β₀ hβ₀ m n
  refine ⟨K, hK, ?_⟩
  intro β h q hfix hβ N P₀ pairMap hxy hdisj fhat M hM hfhat U
  have hb := hKb β h q hfix hβ N P₀ pairMap hdisj fhat M hM hfhat
  have hder := sk_hanen_pairing_derivative N m n β q h (fixedPoint_mem_Icc hfix) pairMap hxy
    hdisj (fun ρ => P₀.blockProduct (Renormalization.pairWeight fun u v => U u v ρ)) fhat hfhat
  have hfun : (fun σ : Fin n → Fin (N + 1) → ℤˣ =>
      P₀.blockProduct (Renormalization.pairWeight fun u v => U u v (fun k i => σ k i.castSucc)) *
        (∏ w : Fin (2 * m), (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
          ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
        fhat (fun k => σ k (Fin.last N))) =
      fun σ => (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
            (σ (pairMap w).2 (Fin.last N) : ℝ))) * fhat (fun r => σ r (Fin.last N)) *
          P₀.blockProduct (Renormalization.pairWeight fun u v =>
            U u v (fun r i => σ r i.castSucc)) := by
    funext σ
    ring
  simp only [hfun] at hder
  have hsum : ∑ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
      skCavityPathMean N n β q h 0 (fun σ =>
        P₀.blockProduct (Renormalization.pairWeight fun u v =>
          U u v (fun r i => σ r i.castSucc)) *
        P.blockProduct (Renormalization.pairWeight fun u v =>
          U u v (fun r i => σ r i.castSucc))) =
      ∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
        P₀.blockProduct (Renormalization.pairWeight fun u v => U u v ρ) *
          Renormalization.wick (fun u v => U u v ρ) (univ : Finset (Fin (2 * m)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    rw [← skCavityPathMean_zero_old N n β q h (fun ρ =>
      P₀.blockProduct (Renormalization.pairWeight fun u v => U u v ρ) *
        Renormalization.wick (fun u v => U u v ρ) (univ : Finset (Fin (2 * m))))]
    have := skCavityPathMean_finset_sum N n β q h 0
      (univ : Finset (Finpartition.Pairing (univ : Finset (Fin (2 * m))))) (fun _ => 1)
      (fun P σ => P₀.blockProduct (Renormalization.pairWeight fun u v =>
          U u v (fun r i => σ r i.castSucc)) *
        P.blockProduct (Renormalization.pairWeight fun u v =>
          U u v (fun r i => σ r i.castSucc)))
    simp only [one_mul] at this
    rw [← this]
    congr 1
    funext σ
    simp only [Renormalization.wick, Finpartition.pairingSum, Finset.mul_sum]
  rw [hsum]
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hrw : β ^ (2 * m) * (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹ ∂gaussianReal 0 1) *
        (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
          P₀.blockProduct (Renormalization.pairWeight fun u v => U u v ρ) *
            Renormalization.wick (fun u v => U u v ρ) (univ : Finset (Fin (2 * m)))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      (m.factorial : ℝ)⁻¹ * iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t
        (fun σ => (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
            (σ (pairMap w).2 (Fin.last N) : ℝ))) * fhat (fun r => σ r (Fin.last N)) *
          P₀.blockProduct (Renormalization.pairWeight fun u v =>
            U u v (fun r i => σ r i.castSucc)))) (Set.Icc 0 1) 0 := by
    have key : ∀ Z I : ℝ, β ^ (2 * m) * Z * I =
        (m.factorial : ℝ)⁻¹ * ((β ^ 2) ^ m * (m.factorial : ℝ) * Z * I) := by
      intro Z I
      rw [← pow_mul]
      field_simp
    rw [hder]
    exact key _ _
  rw [hrw]
  exact hb

end SpinGlasses
