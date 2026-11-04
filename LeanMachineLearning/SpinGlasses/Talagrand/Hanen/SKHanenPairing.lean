/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangular
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPathVanishing
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTaylor

/-!
# Combinatorial pairing formula for the cavity derivative (Talagrand Theorem 1.11.9)

For `|V| = 2m`, the `m`-th cavity derivative at `u = 0` evaluates to
`β^{2m} m! ∑_{P} 𝔼(⟨f̂⟩₀ ch^{-4m} Y) ν₀(f⁻ ∏_{J ∈ P} U_J⁻)`,
where the sum ranges over all pairings $P$ of $V$ into 2-element blocks.

## Main declarations

* `SpinGlasses.HanenPairing`: a pairing on `Fin (2 * m)` represented as a fixed-point-free
  involution.
* `SpinGlasses.skCavityRectTrunc`: the truncated rectangular difference $U_J^-$.
* `SpinGlasses.skCavityPairingRectProd`: product of rectangular differences $\prod_{J ∈ P} U_J^-$.
* `SpinGlasses.sk_hanen_pairing_derivative`: Theorem 1.11.9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- A pairing on `Fin (2 * m)` is a fixed-point-free involution. -/
@[ext, nolint docBlame] structure HanenPairing (m : ℕ) where
  /-- The partner involution matching each replica to its paired replica. -/
  partner : Fin (2 * m) → Fin (2 * m)
  /-- The partner map is an involution ($P^2 = \mathrm{id}$). -/
  involutive : ∀ i, partner (partner i) = i
  /-- No replica is paired with itself. -/
  no_fixed_point : ∀ i, partner i ≠ i

attribute [nolint docBlame] HanenPairing.partner

noncomputable instance (m : ℕ) : Fintype (HanenPairing m) := by
  refine Fintype.ofInjective (fun P => P.partner) fun P Q h => ?_
  cases P; cases Q; congr

/-- The unique empty pairing on `Fin 0`. -/
def hanenPairingZero : HanenPairing 0 where
  partner := fun x => x.elim0
  involutive := fun x => x.elim0
  no_fixed_point := fun x => x.elim0

instance : Unique (HanenPairing 0) where
  default := hanenPairingZero
  uniq := fun P => by
    ext x
    exact x.elim0

/-- Truncated rectangular difference $U_J^-$ for two replica pairs. -/
noncomputable def skCavityRectTrunc (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (u v : Fin (2 * m))
    (ρ : Fin n → Fin N → ℤˣ) : ℝ :=
  let x1 := (pairMap u).1
  let x2 := (pairMap u).2
  let y1 := (pairMap v).1
  let y2 := (pairMap v).2
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x1 i : ℝ)) ⬝ᵥ (fun i => (ρ y1 i : ℝ))) - q) -
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x2 i : ℝ)) ⬝ᵥ (fun i => (ρ y1 i : ℝ))) - q) -
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x1 i : ℝ)) ⬝ᵥ (fun i => (ρ y2 i : ℝ))) - q) +
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x2 i : ℝ)) ⬝ᵥ (fun i => (ρ y2 i : ℝ))) - q)

/-- Symmetry of $U_{\{u, v\}}^-$ under swapping $u$ and $v$. -/
theorem skCavityRectTrunc_comm (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (u v : Fin (2 * m))
    (ρ : Fin n → Fin N → ℤˣ) :
    skCavityRectTrunc N n m q pairMap u v ρ = skCavityRectTrunc N n m q pairMap v u ρ := by
  dsimp only [skCavityRectTrunc]
  have hdot (a b : Fin n) :
      ((fun i => (ρ a i : ℝ)) ⬝ᵥ (fun i => (ρ b i : ℝ))) =
      ((fun i => (ρ b i : ℝ)) ⬝ᵥ (fun i => (ρ a i : ℝ))) := dotProduct_comm _ _
  rw [hdot (pairMap u).1 (pairMap v).1, hdot (pairMap u).2 (pairMap v).1,
      hdot (pairMap u).1 (pairMap v).2, hdot (pairMap u).2 (pairMap v).2]
  ring

/-- The product of truncated rectangular differences over the pairs of a pairing $P$. -/
noncomputable def skCavityPairingRectProd (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (P : HanenPairing m)
    (ρ : Fin n → Fin N → ℤˣ) : ℝ :=
  ∏ i ∈ (Finset.univ : Finset (Fin (2 * m))).filter (fun i => i < P.partner i),
    skCavityRectTrunc N n m q pairMap i (P.partner i) ρ

/-- At $m = 0$, the rectangular product is the empty product, which equals 1. -/
@[simp] theorem skCavityPairingRectProd_zero (N n : ℕ) (q : ℝ)
    (pairMap : Fin 0 → Fin n × Fin n) (P : HanenPairing 0)
    (ρ : Fin n → Fin N → ℤˣ) :
    skCavityPairingRectProd N n 0 q pairMap P ρ = 1 := by
  simp [skCavityPairingRectProd]

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
      ∑ P : HanenPairing 0,
        (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * 0))⁻¹
          ∂gaussianReal 0 1) *
        (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
            F ρ * skCavityPairingRectProd N n 0 q pairMap P ρ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (skCavityOldEnergy N β h g'))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  rw [iteratedDerivWithin_zero]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_zero,
    inv_one, mul_one, skCavityPairingRectProd_zero]
  rw [Fintype.sum_unique]
  simp only [Fin.prod_univ_zero, mul_one]
  exact skCavityPathMean_zero_mul N n β q h F fhat

/- Leading-coefficient checks for the remaining combinatorial proof:
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
      ∑ P : HanenPairing m,
        (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹
          ∂gaussianReal 0 1) *
        (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
            F ρ * skCavityPairingRectProd N n m q pairMap P ρ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (skCavityOldEnergy N β h g'))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  induction m generalizing n with
  | zero =>
    exact sk_hanen_pairing_derivative_zero N n β q h pairMap F fhat
  | succ m ih =>
    sorry

end SpinGlasses
