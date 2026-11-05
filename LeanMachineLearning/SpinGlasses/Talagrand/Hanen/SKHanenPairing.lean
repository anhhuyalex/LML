/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingBasic
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingTerm
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingSum
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTaylor

/-!
# Combinatorial pairing formula for the cavity derivative (Talagrand Theorem 1.11.9)

For `|V| = 2m`, the `m`-th cavity derivative at `u = 0` evaluates to
`β^{2m} m! ∑_{P} 𝔼(⟨f̂⟩₀ ch^{-4m} Y) ν₀(f⁻ ∏_{J ∈ P} U_J⁻)`,
where the sum ranges over all pairings $P$ of $V$ into 2-element blocks.

## Main declarations

* `SpinGlasses.skCavityRectTrunc`: the truncated rectangular difference $U_J^-$.
* `Renormalization.wick`: the existing finite-partition sum of rectangular block products.
* `SpinGlasses.sk_hanen_pairing_derivative`: Theorem 1.11.9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Talagrand's Theorem 1.11.9 (Eq. (1.337)), base case $m = 0$.**
At $m = 0$, the 0-th cavity derivative at $u = 0$ is the decoupled average, which factors
into the last-spin expectation times the $N$-spin expectation. -/
theorem sk_hanen_pairing_derivative_zero (N n : ℕ) (β q h : ℝ)
    (pairMap : Fin 0 → Fin n × Fin n)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ) :
    iteratedDerivWithin 0 (fun t => skCavityPathMean N n β q h t
      (fun σ => F (fun k i => σ k i.castSucc) *
        (∏ w : Fin 0, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
          ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
        fhat (fun k => σ k (Fin.last N)))) (Set.Icc 0 1) 0 =
    (β ^ 2) ^ 0 * (Nat.factorial 0 : ℝ) *
      (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * 0))⁻¹
          ∂gaussianReal 0 1) *
        (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
            F ρ * Renormalization.wick
              (fun u v => skCavityRectTrunc N n 0 q pairMap u v ρ)
              (univ : Finset (Fin 0))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (skCavityOldEnergy N β h g'))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  rw [iteratedDerivWithin_zero]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_zero,
    inv_one, mul_one, Fin.prod_univ_zero]
  have hw (ρ : Fin n → Fin N → ℤˣ) :
      Renormalization.wick (fun u v => skCavityRectTrunc N n 0 q pairMap u v ρ)
        (univ : Finset (Fin 0)) = 1 := by
    simp only [Finset.univ_eq_empty, Renormalization.wick, Finpartition.pairingSum_empty]
  simp_rw [hw, mul_one]
  exact skCavityPathMean_zero_mul N n β q h F fhat

/-- Assemble the original-pair sum using the class evaluations and the existing ordering
identity. This argument works for every `m`, including zero, without induction. -/
theorem sk_hanen_pairing_derivative_of_old_pairs (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ ε i t,
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    (∑ p : Fin m → FinPairs n, skCavityPathMean N n β q h 0 (fun σ =>
      F (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) *
        (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
          (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N)) *
        ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
          (∑ i : Fin N, (σ (p r).val.1 i.castSucc : ℝ) *
            (σ (p r).val.2 i.castSucc : ℝ)) - q))) =
      (m.factorial : ℝ) *
        (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
          ((Real.cosh (β * z * Real.sqrt q + h))⁻¹) ^ (4 * m) ∂gaussianReal 0 1) *
        (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
          F ρ * Renormalization.wick
            (fun u v => skCavityRectTrunc N n m q pairMap u v ρ) univ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  let oldMean := fun G : (Fin n → Fin N → ℤˣ) → ℝ =>
    ∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ, G ρ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hlin {ι : Type} (s : Finset ι) (G : ι → (Fin n → Fin N → ℤˣ) → ℝ) :
      oldMean (fun ρ => ∑ i ∈ s, G i ρ) = ∑ i ∈ s, oldMean (G i) := by
    simpa only [one_mul] using integral_gibbs_finset_sum
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
      (skCavityOldEnergy N β h) (by intro a; unfold skCavityOldEnergy; fun_prop)
      s (fun _ => 1) G
  let Z := ∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
      ((Real.cosh (β * z * Real.sqrt q + h))⁻¹) ^ (4 * m) ∂gaussianReal 0 1
  let K := fun (ρ : Fin n → Fin N → ℤˣ) (a b : Fin n) =>
    (N + 1 : ℝ)⁻¹ * (∑ j : Fin N, (ρ a j : ℝ) * (ρ b j : ℝ)) - q
  have hK (ρ : Fin n → Fin N → ℤˣ) (a b : Fin n) : K ρ a b = K ρ b a := by
    simp only [K, mul_comm]
  let C := fun (ρ : Fin n → Fin N → ℤˣ) u v =>
    skCavityRectTrunc N n m q pairMap u v ρ
  let w := fun (ρ : Fin n → Fin N → ℤˣ) => Renormalization.pairWeight (C ρ)
  have horder (ρ : Fin n → Fin N → ℤˣ) :
      (∑ Pe : (Σ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
          Fin m ≃ P.val.parts), Pe.1.blockProduct (w ρ)) =
        (m.factorial : ℝ) * Renormalization.wick (C ρ) univ := by
    rw [Fintype.sum_sigma]
    have he (P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
        (e : Fin m ≃ P.val.parts) :
        P.blockProduct (w ρ) = ∏ i : Fin m, w ρ (e i).val := by
      rw [e.prod_comp, prod_coe_sort]
      rfl
    simp_rw [he]
    exact Finpartition.pairingSum_orderings univ m (by simp) (w ρ)
  rw [skCavityPathMean_zero_old_pairs_sum_fibers N m n β q h pairMap hdisj F fhat hfhat]
  have hclass (Pe : Σ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
      Fin m ≃ P.val.parts) :
      (∑ p with (∀ i v, v ∈ (Pe.2 i).val ↔
          (p i).val.1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ∨
          (p i).val.2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n))),
        skCavityPathMean N n β q h 0 (fun σ => F (fun r i => σ r i.castSucc) *
          (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
            (σ (pairMap v).2 (Fin.last N) : ℝ))) *
          (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
            (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N)) *
          ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
            (∑ i : Fin N, (σ (p r).val.1 i.castSucc : ℝ) *
              (σ (p r).val.2 i.castSucc : ℝ)) - q))) =
        Z * oldMean (fun ρ => F ρ * Pe.1.blockProduct (w ρ)) := by
    let s := univ.filter fun p : Fin m → FinPairs n => ∀ i v, v ∈ (Pe.2 i).val ↔
      (p i).val.1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ∨
      (p i).val.2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n))
    let G := fun (p : Fin m → FinPairs n) (ρ : Fin n → Fin N → ℤˣ) =>
      F ρ * ∏ i : Fin m,
        (∏ v ∈ (Pe.2 i).val,
          if (pairMap v).1 ∈ ({(p i).val.1, (p i).val.2} : Finset (Fin n)) then
            (1 : ℝ) else -1) * K ρ (p i).val.1 (p i).val.2
    trans ∑ p ∈ s, Z * oldMean (G p)
    · apply sum_congr rfl
      intro p hp
      exact skCavityPathMean_zero_fiber_term_eval N m n β q h pairMap hxy hdisj
        Pe p (mem_filter.mp hp).2 F fhat hfhat
    rw [← mul_sum, ← hlin]
    congr 1
    congr 1
    funext ρ
    dsimp only [G]
    rw [← mul_sum]
    congr 1
    simpa only [s, w, C, K, skCavityRectTrunc, dotProduct] using
      skCavityPairing_signed_fiber_sum pairMap hxy hdisj Pe (K ρ) (hK ρ)
  simp_rw [hclass]
  rw [← mul_sum, ← hlin]
  have hsum : (fun ρ => ∑ Pe : (Σ P : Finpartition.Pairing
      (univ : Finset (Fin (2 * m))), Fin m ≃ P.val.parts),
      F ρ * Pe.1.blockProduct (w ρ)) =
      fun ρ => (m.factorial : ℝ) * (F ρ * Renormalization.wick (C ρ) univ) := by
    funext ρ
    rw [← mul_sum, horder]
    ring
  rw [hsum]
  simp only [oldMean, integral_const_mul]
  ring

/- Leading-coefficient checks for the combinatorial proof:
At m = 1 there is one pairing. The four choices of endpoints, one from each
spin-difference pair, have signs +,-,-,+ and sum to one rectangle U^-.
At m = 2 there are three pairings of the four spin-difference pairs. Each has
2! derivative orderings and 2^4 endpoint choices: 3 * 2 * 16 = 96 surviving
terms. Regrouping the endpoint choices gives the product of two rectangles;
the two derivative orderings give exactly the factor 2!, without an extra 2^m.
These are hand checks of the coefficient, not a proof of the general identity.
-/

/-- **Talagrand's Theorem 1.11.9 (Eq. (1.337)).** Combinatorial pairing formula for the cavity
derivative: for `|V| = 2m`, the `m`-th cavity derivative at `u = 0` evaluates to
`β^{2m} m! ∑_{P} 𝔼(⟨f̂⟩₀ ch^{-4m} Y) ν₀(f⁻ ∏_{J ∈ P} U_J⁻)`. -/
theorem sk_hanen_pairing_derivative (N m n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ (Finset.univ : Finset (Fin (2 * m))).biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t
      (fun σ => F (fun k i => σ k i.castSucc) *
        (∏ w : Fin (2 * m), (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
          ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
        fhat (fun k => σ k (Fin.last N)))) (Set.Icc 0 1) 0 =
    (β ^ 2) ^ m * (Nat.factorial m : ℝ) *
      (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹
          ∂gaussianReal 0 1) *
        (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
            F ρ * Renormalization.wick
              (fun u v => skCavityRectTrunc N n m q pairMap u v ρ)
              (univ : Finset (Fin (2 * m)))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (skCavityOldEnergy N β h g'))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  rw [iteratedDerivWithin_skCavityPathMean_zero_old_pairs N m n β q h hq
    pairMap hdisj F fhat hfhat,
    sk_hanen_pairing_derivative_of_old_pairs N m n β q h pairMap hxy hdisj F fhat hfhat]
  simp only [inv_pow]
  ring

end SpinGlasses
