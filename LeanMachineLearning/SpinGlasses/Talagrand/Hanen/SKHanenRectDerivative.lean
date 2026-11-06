/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairing
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangularTaylor

/-!
# The leading derivative of a product of rectangles (Talagrand, Proposition 1.11.10, step E3b)

Theorem 1.11.9 applied to the observable `η_V f̂ ∏_{J ∈ P₀} U_J⁻` of Eq. (1.342): the `m`-th
cavity derivative at `u = 0` is `β^{2m} m! Z ∑_P ν₀(∏_{J ∈ P₀} U_J⁻ ∏_{J ∈ P} U_J⁻)`, where
every average `ν₀` is the decoupled average of a function of the old spins.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The decoupled cavity average of a function of the old spins is the old-spin average. -/
theorem skCavityPathMean_zero_old (N n : ℕ) (β q h : ℝ) (G : (Fin n → Fin N → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h 0 (fun σ => G (fun k i => σ k i.castSucc)) =
      ∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  simpa using skCavityPathMean_zero_mul N n β q h G (fun _ => 1)

/-- **Step E3b of Proposition 1.11.10.** The `m`-th cavity derivative at `u = 0` of the
observable `η_V f̂ ∏_{J ∈ P₀} U_J⁻` of Eq. (1.342) is
`β^{2m} m! Z ∑_P ν₀(∏_{J ∈ P₀} U_J⁻ ∏_{J ∈ P} U_J⁻)`, the sum running over all pairings `P`
of the `2m` difference labels. The pairing `P₀` is arbitrary. -/
theorem sk_hanen_rect_product_derivative (N m n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (P₀ : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
    (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ (univ : Finset (Fin (2 * m))).biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t (fun σ =>
      (∏ w : Fin (2 * m), (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
        ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
      fhat (fun k => σ k (Fin.last N)) *
      P₀.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun k i => σ k i.castSucc))))
      (Set.Icc 0 1) 0 =
    (β ^ 2) ^ m * (Nat.factorial m : ℝ) *
      (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹
          ∂gaussianReal 0 1) *
      ∑ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
        skCavityPathMean N n β q h 0 (fun σ =>
          P₀.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc N n m q pairMap u v (fun k i => σ k i.castSucc)) *
          P.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc N n m q pairMap u v (fun k i => σ k i.castSucc))) := by
  have hfun : (fun t => skCavityPathMean N n β q h t (fun σ =>
      (∏ w : Fin (2 * m), (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
        ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
      fhat (fun k => σ k (Fin.last N)) *
      P₀.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun k i => σ k i.castSucc)))) =
      fun t => skCavityPathMean N n β q h t (fun σ =>
        (fun ρ : Fin n → Fin N → ℤˣ => P₀.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v ρ)) (fun k i => σ k i.castSucc) *
        (∏ w : Fin (2 * m), (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
          ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
        fhat (fun k => σ k (Fin.last N))) := by
    funext t
    congr 1
    funext σ
    ring
  rw [hfun, sk_hanen_pairing_derivative N m n β q h hq pairMap hxy hdisj
    (fun ρ : Fin n → Fin N → ℤˣ => P₀.blockProduct (Renormalization.pairWeight fun u v =>
      skCavityRectTrunc N n m q pairMap u v ρ)) fhat hfhat]
  congr 1
  have hsum := skCavityPathMean_finset_sum N n β q h 0
    (univ : Finset (Finpartition.Pairing (univ : Finset (Fin (2 * m))))) (fun _ => 1)
    (fun P σ => P₀.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun k i => σ k i.castSucc)) *
      P.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun k i => σ k i.castSucc)))
  simp only [one_mul] at hsum
  rw [← hsum]
  refine Eq.trans ?_ (skCavityPathMean_zero_old N n β q h (fun ρ : Fin n → Fin N → ℤˣ =>
    ∑ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
      P₀.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v ρ) *
      P.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v ρ))).symm
  congr 1
  funext g'
  congr 1
  funext ρ
  simp only [Renormalization.wick, Finpartition.pairingSum, mul_sum]

/-- **Step E3c(i) (Eq. (1.344), first comparison).** For a function `G` of the old spins whose
second moment in the coupled system is at most `C/(N+1)^k`, the coupled average and the decoupled
average differ by at most `D √C/(N+1)^((k+1)/2)`. The constant `D` is chosen before everything
else, and no special form of `G` is needed. -/
theorem skCavityPathMean_one_sub_zero_old_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (G : (Fin n → Fin N → ℤˣ) → ℝ) (C : ℝ), 0 ≤ C →
      skCavityPathMean N n β q h 1 (fun σ => G (fun r i => σ r i.castSucc) ^ 2) ≤
        C / ((N : ℝ) + 1) ^ k →
      |skCavityPathMean N n β q h 1 (fun σ => G (fun r i => σ r i.castSucc)) -
        skCavityPathMean N n β q h 0 (fun σ => G (fun r i => σ r i.castSucc))| ≤
        D * Real.sqrt C / ((N : ℝ) + 1) ^ (((k : ℝ) + 1) / 2) := by
  obtain ⟨D, hD, hDb⟩ := skCavityPathMean_taylor_coefficient_le β₀ hβ₀ 0 k n
  refine ⟨D, hD, ?_⟩
  intro β h q hfix hβ N G C hC hmom
  have hb := hDb β h q hfix hβ N (fun σ => G (fun r i => σ r i.castSucc)) C hC hmom
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  simpa [iteratedDerivWithin_zero] using hb

/-- Square-moment decay for the product of the block products of two arbitrary pairings: there
are `2m` rectangles, so the second moment is of order `(N+1)^{-2m}`. -/
theorem sk_hanen_two_pairing_rect_prod_sq_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ)
      (P P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n),
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      skCavityPathMean N n β q h 1 (fun σ => (P.blockProduct
        (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)) *
        P'.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc))) ^ 2) ≤
        C / ((N : ℝ) + 1) ^ (2 * m) := by
  obtain ⟨C, hC, hCb⟩ := sk_hanen_rect_prod_sq_le β₀ hβ₀ (m + m) 1
  refine ⟨C, hC, ?_⟩
  intro β h q hfix hβ N n P P' pairMap hdisj
  obtain ⟨u, v, huv, hlabels⟩ := Renormalization.exists_labels_prod_pairWeight (m := m) P (by simp)
  obtain ⟨u', v', huv', hlabels'⟩ :=
    Renormalization.exists_labels_prod_pairWeight (m := m) P' (by simp)
  have hprod (ρ : Fin n → Fin N → ℤˣ) :
      (∏ j : Fin (m + m), skCavityRectTrunc N n m q pairMap
        (Fin.append u u' j) (Fin.append v v' j) ρ) =
      P.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v ρ) *
        P'.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v ρ) := by
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hlabels _ fun a b => skCavityRectTrunc_comm N n m q pairMap a b ρ,
      hlabels' _ fun a b => skCavityRectTrunc_comm N n m q pairMap a b ρ]
  have hne : ∀ j, Fin.append u u' j ≠ Fin.append v v' j := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using huv i
    · simpa using huv' i
  have hb := hCb β h q hfix hβ N n m pairMap hdisj (Fin.append u u') (Fin.append v v') hne
    (fun _ => 1) (fun _ => by simp)
  rw [two_mul]
  simpa only [one_mul, hprod] using hb

end SpinGlasses
