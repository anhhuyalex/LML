/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityDecoupledMonomials
public import LeanMachineLearning.SpinGlasses.SKCavityTaylor
public import LeanMachineLearning.SpinGlasses.SKCavityReplicaPairs
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag
public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.LeftEigenProjection

/-!
# Cavity covariance equations and the AT matrix (Talagrand, Lemma 1.8.2 & Eqs. 1.230–1.236)

This module formalizes:
1. **General Lemma 1.8.2 (Eq. 1.230)**: The cavity path derivative at `t = 0` of
   `(ε_x ε_y - q) f⁻` for an observable `f⁻` on `n` replicas and distinct `x ≠ y ≤ n`:
   `ν₀'((ε_x ε_y - q) f⁻) =
      ∑_{1 ≤ ℓ < ℓ' ≤ n} b(ℓ, ℓ'; x, y) ν₀(f⁻ (R⁻_{ℓ, ℓ'} - q)) -
      n ∑_{ℓ ≤ n} b(ℓ, n+1; x, y) ν₀(f⁻ (R⁻_{ℓ, n+1} - q)) +
      (n(n+1)/2) b(0) ν₀(f⁻ (R⁻_{n+1, n+2} - q))`
   where `b(c) = β² b_unscaled(c)` with `b_unscaled(2) = 1 - q²`, `b_unscaled(1) = q - q²`,
   and `b_unscaled(0) = q̂ - q²`.
2. **The AT Matrix (Eq. 1.234) & Universal Eigenvectors (Eqs. 1.235–1.236)**:
   The `3 × 3` matrix has eigenvectors `(1, -2, 1)` and `(1, -4, 3)` with eigenvalues
   `λ₁ = β² (1 - 2q + q̂)` and `λ₂ = β² (1 - 4q + 3q̂)`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Coincidence count of a replica pair `j` with the pair `{x, y}` of old replicas. -/
def skCavityReplicaPairCoincidences {n : ℕ} (x y : Fin n) (j : SKCavityReplicaPair n) : ℕ :=
  skCavityCoincidences (some (some x)) (some (some y))
    (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2

/-- **Decoupled average of a combination of pair covariance monomials.**  The linear combination
`∑_m c_m (ε_{x m} ε_{y m} - q)` of pair covariances against `ε_a ε_b` and a function `F` of the
old coordinates averages, at the decoupled endpoint, to `∑_m c_m b(coinc_m)` times the average of
`F`, where `coinc_m` counts the coincidences of `{x m, y m}` with `{a, b}`. -/
theorem sk_cavity_decoupled_endpoint_pair_cov_combo (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {R ι : Type*} [Fintype R] [DecidableEq R] [Fintype ι] (c : ι → ℝ) {x y : ι → R}
    (hxy : ∀ m, x m ≠ y m) {a b : R} (hab : a ≠ b)
    (F : (R → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : R → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) *
            ((∑ m, c m * (((σ (x m) (Fin.last N) : ℤˣ) : ℝ) *
                ((σ (y m) (Fin.last N) : ℤˣ) : ℝ) - q)) *
              (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (∑ m, c m * skCavityBUnscaled q qhat (skCavityCoincidences (x m) (y m) a b)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let Gm : ι → (R → Fin (N + 1) → ℤˣ) → ℝ := fun m σ =>
    F (fun r i => σ r i.castSucc) *
      ((((σ (x m) (Fin.last N) : ℤˣ) : ℝ) * ((σ (y m) (Fin.last N) : ℤˣ) : ℝ) - q) *
        (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)))
  have hpt : ∀ σ : R → Fin (N + 1) → ℤˣ,
      F (fun r i => σ r i.castSucc) *
        ((∑ m, c m * (((σ (x m) (Fin.last N) : ℤˣ) : ℝ) *
            ((σ (y m) (Fin.last N) : ℤˣ) : ℝ) - q)) *
          (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) =
        ∑ m ∈ Finset.univ, c m * Gm m σ := fun σ => by
    simp only [Gm, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ c Gm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc]
  congr 1
  exact sk_cavity_decoupled_endpoint_pair_cov N β q h hfix qhat hqhat (hxy m) hab F

/-- **Talagrand, Lemma 1.8.2, Eq. (1.230), for a combination of pair covariances.**
At the decoupled endpoint `t = 0` (`s = π/2`), the cavity path derivative of
`(∑_m c_m (ε_{x m} ε_{y m} - q)) f⁻` on `n` replicas, with `x m ≠ y m`, is the weighted sum over
the three replica families of `(∑_m c_m b(coinc_m)) ν₀(f⁻ (R⁻_{a, b} - q))`, where `coinc_m` is
the number of coincidences of `{x m, y m}` with the family pair `{a, b}`.  Differences of pair
covariances (Lemma 1.8.9) and single pair covariances (Lemma 1.8.2) are special cases. -/
theorem sk_cavity_deriv_zero_pair_combo (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) {x y : ι → Fin n} (hxy : ∀ m, x m ≠ y m)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let so : Fin n → Option (Option (Fin n)) := fun r => some (some r)
    let f : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
      F (fun r i => τ (so r) i.castSucc) *
        ∑ m, c m * ((((τ (so (x m)) (Fin.last N) : ℤˣ) : ℝ) *
          ((τ (so (y m)) (Fin.last N) : ℤˣ) : ℝ)) - q)
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f τ *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (so p.1)) (τ (so p.2))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (so r)) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j *
          ((∑ m, c m * skCavityBCoef β q qhat
              (skCavityReplicaPairCoincidences (x m) (y m) j)) *
            ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              F (fun r => ρ (so r)) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  intro B E so f K
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let Gab : Option (Option (Fin n)) → Option (Option (Fin n)) →
      (Option (Option (Fin n)) → Fin N → ℤˣ) → ℝ := fun a b ρ =>
    F (fun r => ρ (so r)) * (β ^ 2 * ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (ρ a i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ b i : ℝ)) - q))
  have hT : ∀ a b : Option (Option (Fin n)), a ≠ b →
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f τ * K (τ a) (τ b)
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      (∑ m, c m * skCavityBUnscaled q qhat
          (skCavityCoincidences (so (x m)) (so (y m)) a b)) *
        ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ, Gab a b ρ
          ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := fun a b hab => by
    have hpt : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f τ * K (τ a) (τ b) =
          Gab a b (fun r i => τ r i.castSucc) *
            ((∑ m, c m * (((τ (so (x m)) (Fin.last N) : ℤˣ) : ℝ) *
                ((τ (so (y m)) (Fin.last N) : ℤˣ) : ℝ) - q)) *
              (((τ a (Fin.last N) : ℤˣ) : ℝ) * ((τ b (Fin.last N) : ℤˣ) : ℝ))) := fun τ => by
      simp only [f, K, Gab]
      ring
    simp_rw [hpt]
    have hso : ∀ m, so (x m) ≠ so (y m) := fun m h =>
      hxy m (Option.some.inj (Option.some.inj h))
    exact sk_cavity_decoupled_endpoint_pair_cov_combo N β q h hfix qhat hqhat c
      (x := fun m => so (x m)) (y := fun m => so (y m)) hso hab (Gab a b)
  let Gj : SKCavityReplicaPair n → (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun j τ =>
    f τ * K (τ (skCavityReplicaPairMap j).1) (τ (skCavityReplicaPairMap j).2)
  have hS : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      f τ *
          ((∑ p : Fin n × Fin n with p.1 < p.2,
              K (τ (so p.1)) (τ (so p.2))) -
            (n : ℝ) * ∑ r : Fin n, K (τ (so r)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none)) =
        ∑ j, skCavityReplicaPairWeight n j * Gj j τ := fun τ =>
    sk_cavity_signed_pair_mul_sum K τ (f τ)
  simp_rw [hS]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ (skCavityReplicaPairWeight n) Gj]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hne := skCavityReplicaPair_ne j
  have hj := hT (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2 hne
  dsimp [Gj]
  rw [hj]
  have hsum : (∑ m, c m * skCavityBCoef β q qhat
      (skCavityReplicaPairCoincidences (x m) (y m) j)) =
      β ^ 2 * ∑ m, c m * skCavityBUnscaled q qhat
        (skCavityCoincidences (so (x m)) (so (y m))
          (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [skCavityBCoef, skCavityReplicaPairCoincidences, so]
    ring
  rw [hsum]
  simp only [Gab]
  have hint : (∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
        F (fun r => ρ (so r)) *
          (β ^ 2 *
            (((N + 1 : ℝ)⁻¹ *
                ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                  fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      β ^ 2 *
        ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
          F (fun r => ρ (so r)) *
            (((N + 1 : ℝ)⁻¹ *
                ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                  fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q))
          ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have hpt : ∀ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
        F (fun r => ρ (so r)) *
          (β ^ 2 *
            (((N + 1 : ℝ)⁻¹ *
                ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                  fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q))) =
        β ^ 2 *
          (F (fun r => ρ (so r)) *
            (((N + 1 : ℝ)⁻¹ *
                ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                  fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q))) :=
          fun ρ => by ring
    simp_rw [hpt]
    simp_rw [integral_const_mul]
  rw [hint]
  ring

/-- **Talagrand, Lemma 1.8.2, Eq. (1.230): cavity derivative of a pair covariance.**
At the decoupled endpoint `t = 0` (`s = π/2`), the cavity path derivative of
`((ε_x ε_y - q) f⁻)` on `n` replicas for distinct `x ≠ y` is the weighted sum of
`b(c) ν₀(f⁻ (R⁻_{a, b} - q))` over the three replica families, where `c` is the
coincidence count. -/
theorem sk_cavity_deriv_zero_pair (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {x y : Fin n} (hxy : x ≠ y)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let so : Fin n → Option (Option (Fin n)) := fun r => some (some r)
    let f : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
      F (fun r i => τ (so r) i.castSucc) *
        ((((τ (so x) (Fin.last N) : ℤˣ) : ℝ) * ((τ (so y) (Fin.last N) : ℤˣ) : ℝ)) - q)
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f τ *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (so p.1)) (τ (so p.2))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (so r)) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j *
          (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) *
            ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              F (fun r => ρ (so r)) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  intro B E so f K
  have h1 := sk_cavity_deriv_zero_pair_combo N n β q h hfix qhat hqhat (ι := Unit)
    (fun _ => 1) (x := fun _ => x) (y := fun _ => y) (fun _ => hxy) F
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul] at h1
  exact h1

/-- The 3×3 matrix of the cavity covariance system (Talagrand Eq. 1.234):
`[b(2),              -4 b(1),              3 b(0)             ]`
`[b(1),  b(2) - 2 b(1) - 3 b(0),        6 b(0) - 3 b(1)       ]`
`[b(0),        4 b(1) - 8 b(0),   b(2) - 8 b(1) + 10 b(0)     ]` -/
def skAtMatrix (b2 b1 b0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![b2, -4 * b1, 3 * b0],
    ![b1, b2 - 2 * b1 - 3 * b0, 6 * b0 - 3 * b1],
    ![b0, 4 * b1 - 8 * b0, b2 - 8 * b1 + 10 * b0]]

/-- The first eigenvector of the transposed AT matrix: `(1, -2, 1)`. -/
def skAtEigenvectorOne : Fin 3 → ℝ :=
  ![1, -2, 1]

/-- The second eigenvector of the transposed AT matrix: `(1, -4, 3)`. -/
def skAtEigenvectorTwo : Fin 3 → ℝ :=
  ![1, -4, 3]

/-- **Talagrand, Eq. (1.235): universal eigenvector `(1, -2, 1)` of the transposed AT matrix.**
For any coefficients `b(2), b(1), b(0)`, `(1, -2, 1)` is an eigenvector of
`(skAtMatrix b2 b1 b0)ᵀ` with eigenvalue `λ₁ = b(2) - 2 b(1) + b(0)`. -/
theorem sk_at_matrix_transpose_mulVec_one (b2 b1 b0 : ℝ) :
    (skAtMatrix b2 b1 b0)ᵀ *ᵥ skAtEigenvectorOne =
      (b2 - 2 * b1 + b0) • skAtEigenvectorOne := by
  ext i
  fin_cases i
  · change (∑ j : Fin 3, (skAtMatrix b2 b1 b0)ᵀ 0 j * skAtEigenvectorOne j) = _
    rw [Fin.sum_univ_three]
    change b2 * 1 + b1 * (-2) + b0 * 1 = (b2 - 2 * b1 + b0) * 1
    ring
  · change (∑ j : Fin 3, (skAtMatrix b2 b1 b0)ᵀ 1 j * skAtEigenvectorOne j) = _
    rw [Fin.sum_univ_three]
    change (-4 * b1) * 1 + (b2 - 2 * b1 - 3 * b0) * (-2) + (4 * b1 - 8 * b0) * 1 =
        (b2 - 2 * b1 + b0) * (-2)
    ring
  · change (∑ j : Fin 3, (skAtMatrix b2 b1 b0)ᵀ 2 j * skAtEigenvectorOne j) = _
    rw [Fin.sum_univ_three]
    change (3 * b0) * 1 + (6 * b0 - 3 * b1) * (-2) + (b2 - 8 * b1 + 10 * b0) * 1 =
        (b2 - 2 * b1 + b0) * 1
    ring

/-- **Talagrand, Eq. (1.236): universal eigenvector `(1, -4, 3)` of the transposed AT matrix.**
For any coefficients `b(2), b(1), b(0)`, `(1, -4, 3)` is an eigenvector of
`(skAtMatrix b2 b1 b0)ᵀ` with eigenvalue `λ₂ = b(2) - 4 b(1) + 3 b(0)`. -/
theorem sk_at_matrix_transpose_mulVec_two (b2 b1 b0 : ℝ) :
    (skAtMatrix b2 b1 b0)ᵀ *ᵥ skAtEigenvectorTwo =
      (b2 - 4 * b1 + 3 * b0) • skAtEigenvectorTwo := by
  ext i
  fin_cases i
  · change (∑ j : Fin 3, (skAtMatrix b2 b1 b0)ᵀ 0 j * skAtEigenvectorTwo j) = _
    rw [Fin.sum_univ_three]
    change b2 * 1 + b1 * (-4) + b0 * 3 = (b2 - 4 * b1 + 3 * b0) * 1
    ring
  · change (∑ j : Fin 3, (skAtMatrix b2 b1 b0)ᵀ 1 j * skAtEigenvectorTwo j) = _
    rw [Fin.sum_univ_three]
    change (-4 * b1) * 1 + (b2 - 2 * b1 - 3 * b0) * (-4) + (4 * b1 - 8 * b0) * 3 =
        (b2 - 4 * b1 + 3 * b0) * (-4)
    ring
  · change (∑ j : Fin 3, (skAtMatrix b2 b1 b0)ᵀ 2 j * skAtEigenvectorTwo j) = _
    rw [Fin.sum_univ_three]
    change (3 * b0) * 1 + (6 * b0 - 3 * b1) * (-4) + (b2 - 8 * b1 + 10 * b0) * 3 =
        (b2 - 4 * b1 + 3 * b0) * 3
    ring

/-- The first eigenvalue `λ₁ = b(2) - 2 b(1) + b(0)` expressed in terms of `(β, q, q̂)`:
`λ₁ = β² (1 - 2 q + q̂)`. -/
theorem sk_at_eigenvalue_one_eq (β q qhat : ℝ) :
    skCavityBCoef β q qhat 2 - 2 * skCavityBCoef β q qhat 1 +
      skCavityBCoef β q qhat 0 =
    β ^ 2 * (1 - 2 * q + qhat) := by
  dsimp [skCavityBCoef, skCavityBUnscaled]
  ring

/-- The second eigenvalue `λ₂ = b(2) - 4 b(1) + 3 b(0)` expressed in terms of `(β, q, q̂)`:
`λ₂ = β² (1 - 4 q + 3 q̂)`. -/
theorem sk_at_eigenvalue_two_eq (β q qhat : ℝ) :
    skCavityBCoef β q qhat 2 - 4 * skCavityBCoef β q qhat 1 +
      3 * skCavityBCoef β q qhat 0 =
    β ^ 2 * (1 - 4 * q + 3 * qhat) := by
  dsimp [skCavityBCoef, skCavityBUnscaled]
  ring

/-- The first row linear form of the AT matrix system (Eq. 1.231):
`b(2) U - 4 b(1) V + 3 b(0) W`. -/
def skAtRowZero (b2 b1 b0 U V W : ℝ) : ℝ :=
  b2 * U - 4 * b1 * V + 3 * b0 * W

/-- The second row linear form of the AT matrix system (Eq. 1.232):
`b(1) U + (b(2) - 2 b(1) - 3 b(0)) V + (6 b(0) - 3 b(1)) W`. -/
def skAtRowOne (b2 b1 b0 U V W : ℝ) : ℝ :=
  b1 * U + (b2 - 2 * b1 - 3 * b0) * V + (6 * b0 - 3 * b1) * W

/-- The third row linear form of the AT matrix system (Eq. 1.233):
`b(0) U + (4 b(1) - 8 b(0)) V + (b(2) - 8 b(1) + 10 b(0)) W`. -/
def skAtRowTwo (b2 b1 b0 U V W : ℝ) : ℝ :=
  b0 * U + (4 * b1 - 8 * b0) * V + (b2 - 8 * b1 + 10 * b0) * W

theorem sk_at_matrix_mulVec_zero (b2 b1 b0 : ℝ) (v : Fin 3 → ℝ) :
    (skAtMatrix b2 b1 b0 *ᵥ v) 0 = skAtRowZero b2 b1 b0 (v 0) (v 1) (v 2) := by
  change (∑ j : Fin 3, skAtMatrix b2 b1 b0 0 j * v j) = _
  rw [Fin.sum_univ_three]
  change b2 * v 0 + (-4 * b1) * v 1 + (3 * b0) * v 2 = _
  dsimp [skAtRowZero]
  ring

theorem sk_at_matrix_mulVec_one (b2 b1 b0 : ℝ) (v : Fin 3 → ℝ) :
    (skAtMatrix b2 b1 b0 *ᵥ v) 1 = skAtRowOne b2 b1 b0 (v 0) (v 1) (v 2) := by
  change (∑ j : Fin 3, skAtMatrix b2 b1 b0 1 j * v j) = _
  rw [Fin.sum_univ_three]
  rfl

theorem sk_at_matrix_mulVec_two (b2 b1 b0 : ℝ) (v : Fin 3 → ℝ) :
    (skAtMatrix b2 b1 b0 *ᵥ v) 2 = skAtRowTwo b2 b1 b0 (v 0) (v 1) (v 2) := by
  change (∑ j : Fin 3, skAtMatrix b2 b1 b0 2 j * v j) = _
  rw [Fin.sum_univ_three]
  rfl

/-- The rows of `skAtMatrix` applied to `v = ![U, V, W]` match the three linear forms. -/
theorem sk_at_matrix_mulVec_eq (b2 b1 b0 U V W : ℝ) :
    skAtMatrix b2 b1 b0 *ᵥ ![U, V, W] =
      ![skAtRowZero b2 b1 b0 U V W,
        skAtRowOne b2 b1 b0 U V W,
        skAtRowTwo b2 b1 b0 U V W] := by
  ext i
  fin_cases i
  · exact sk_at_matrix_mulVec_zero b2 b1 b0 ![U, V, W]
  · exact sk_at_matrix_mulVec_one b2 b1 b0 ![U, V, W]
  · exact sk_at_matrix_mulVec_two b2 b1 b0 ![U, V, W]

/-- The inhomogeneous source vector of the AT cavity system (Eqs. 1.231–1.233):
`S = (1/M) * (1 - q², q - q², q̂ - q²)ᵀ`. -/
noncomputable def skAtSource (q qhat M : ℝ) : Fin 3 → ℝ :=
  ![ (1 - q ^ 2) / M, (q - q ^ 2) / M, (qhat - q ^ 2) / M ]

/-- The first eigenvector `(1, -2, 1)` projects the source vector to `(1 - 2q + q̂) / M`. -/
theorem sk_at_source_dot_eigenvector_one (q qhat M : ℝ) :
    skAtEigenvectorOne ⬝ᵥ skAtSource q qhat M =
      (1 - 2 * q + qhat) / M := by
  change ∑ i : Fin 3, skAtEigenvectorOne i * skAtSource q qhat M i = _
  rw [Fin.sum_univ_three]
  change 1 * ((1 - q ^ 2) / M) + (-2) * ((q - q ^ 2) / M) + 1 * ((qhat - q ^ 2) / M) = _
  ring

/-- The second eigenvector `(1, -4, 3)` projects the source vector to `(1 - 4q + 3q̂) / M`. -/
theorem sk_at_source_dot_eigenvector_two (q qhat M : ℝ) :
    skAtEigenvectorTwo ⬝ᵥ skAtSource q qhat M =
      (1 - 4 * q + 3 * qhat) / M := by
  change ∑ i : Fin 3, skAtEigenvectorTwo i * skAtSource q qhat M i = _
  rw [Fin.sum_univ_three]
  change 1 * ((1 - q ^ 2) / M) + (-4) * ((q - q ^ 2) / M) + 3 * ((qhat - q ^ 2) / M) = _
  ring

/-- **The Three Cavity Covariance Equations (Talagrand Eqs. 1.231–1.233).**
The component equations for `(U, V, W) = (v 0, v 1, v 2)`:
- `U = (1 - q²) / M + b(2) U - 4 b(1) V + 3 b(0) W + R 0`
- `V = (q - q²) / M + b(1) U + (b(2) - 2 b(1) - 3 b(0)) V + (6 b(0) - 3 b(1)) W + R 1`
- `W = (q̂ - q²) / M + b(0) U + (4 b(1) - 8 b(0)) V + (b(2) - 8 b(1) + 10 b(0)) W + R 2`
are equivalent to the matrix-vector equation `v = S + M *ᵥ v + R`. -/
theorem sk_at_covariance_equations_iff (b2 b1 b0 q qhat M : ℝ)
    (v R : Fin 3 → ℝ) :
    (v = skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R) ↔
      (v 0 = (1 - q ^ 2) / M + skAtRowZero b2 b1 b0 (v 0) (v 1) (v 2) + R 0 ∧
       v 1 = (q - q ^ 2) / M + skAtRowOne b2 b1 b0 (v 0) (v 1) (v 2) + R 1 ∧
       v 2 = (qhat - q ^ 2) / M + skAtRowTwo b2 b1 b0 (v 0) (v 1) (v 2) + R 2) := by
  constructor
  · intro h
    have h0 : v 0 = (skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R) 0 := congr_fun h 0
    have h1 : v 1 = (skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R) 1 := congr_fun h 1
    have h2 : v 2 = (skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R) 2 := congr_fun h 2
    dsimp [skAtSource] at h0 h1 h2
    rw [sk_at_matrix_mulVec_zero] at h0
    rw [sk_at_matrix_mulVec_one] at h1
    rw [sk_at_matrix_mulVec_two] at h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i
    · have hzero := sk_at_matrix_mulVec_zero b2 b1 b0 v
      dsimp [skAtSource]
      linear_combination h0 - hzero
    · have hone := sk_at_matrix_mulVec_one b2 b1 b0 v
      dsimp [skAtSource]
      linear_combination h1 - hone
    · have htwo := sk_at_matrix_mulVec_two b2 b1 b0 v
      dsimp [skAtSource]
      linear_combination h2 - htwo

/-- **Eigenvector decoupling for the first mode `U - 2V + W`:**
Taking the inner product of `v = S + M *ᵥ v + R` with the transposed eigenvector `v₁ = (1, -2, 1)`
yields an uncoupled scalar equation with eigenvalue `λ₁ = b(2) - 2 b(1) + b(0)`. -/
theorem sk_at_system_dot_eigenvector_one (b2 b1 b0 q qhat M : ℝ)
    (v R : Fin 3 → ℝ)
    (hsys : v = skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R) :
    (skAtEigenvectorOne ⬝ᵥ v) =
      (1 - 2 * q + qhat) / M +
        (b2 - 2 * b1 + b0) * (skAtEigenvectorOne ⬝ᵥ v) +
        (skAtEigenvectorOne ⬝ᵥ R) := by
  have h := Matrix.dotProduct_system_of_transpose_eigenvector _ skAtEigenvectorOne v _ R _
    (sk_at_matrix_transpose_mulVec_one b2 b1 b0) hsys
  rw [sk_at_source_dot_eigenvector_one] at h
  exact h

/-- **Eigenvector decoupling for the second mode `U - 4V + 3W`:**
Taking the inner product of `v = S + M *ᵥ v + R` with the transposed eigenvector `v₂ = (1, -4, 3)`
yields an uncoupled scalar equation with eigenvalue `λ₂ = b(2) - 4 b(1) + 3 b(0)`. -/
theorem sk_at_system_dot_eigenvector_two (b2 b1 b0 q qhat M : ℝ)
    (v R : Fin 3 → ℝ)
    (hsys : v = skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R) :
    (skAtEigenvectorTwo ⬝ᵥ v) =
      (1 - 4 * q + 3 * qhat) / M +
        (b2 - 4 * b1 + 3 * b0) * (skAtEigenvectorTwo ⬝ᵥ v) +
        (skAtEigenvectorTwo ⬝ᵥ R) := by
  have h := Matrix.dotProduct_system_of_transpose_eigenvector _ skAtEigenvectorTwo v _ R _
    (sk_at_matrix_transpose_mulVec_two b2 b1 b0) hsys
  rw [sk_at_source_dot_eigenvector_two] at h
  exact h

/-- **Closed-form evaluation of the first decoupled mode `U - 2V + W`:**
When `λ₁ = b(2) - 2 b(1) + b(0) ≠ 1`, the decoupled combination satisfies:
`(U - 2V + W) - (1 - 2q + q̂) / (M * (1 - λ₁)) = (v₁ ⬝ᵥ R) / (1 - λ₁)`. -/
theorem sk_at_system_solve_one (b2 b1 b0 q qhat M : ℝ)
    (v R : Fin 3 → ℝ)
    (hsys : v = skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R)
    (hlam1 : b2 - 2 * b1 + b0 ≠ 1) :
    (skAtEigenvectorOne ⬝ᵥ v) -
      (1 - 2 * q + qhat) / (M * (1 - (b2 - 2 * b1 + b0))) =
        (skAtEigenvectorOne ⬝ᵥ R) / (1 - (b2 - 2 * b1 + b0)) := by
  have hmode := sk_at_system_dot_eigenvector_one b2 b1 b0 q qhat M v R hsys
  have hsub : 1 - (b2 - 2 * b1 + b0) ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam1)
  set Y := skAtEigenvectorOne ⬝ᵥ v
  set S₁ := (1 - 2 * q + qhat) / M
  set R₁ := skAtEigenvectorOne ⬝ᵥ R
  set lam1 := b2 - 2 * b1 + b0
  have heq : (1 - lam1) * Y = S₁ + R₁ := by linarith [hmode]
  have hY : Y = (S₁ + R₁) / (1 - lam1) := by
    rw [← heq, mul_div_cancel_left₀ Y hsub]
  rw [hY, add_div]
  dsimp [S₁]
  rw [div_div]
  ring

/-- **Closed-form evaluation of the second decoupled mode `U - 4V + 3W`:**
When `λ₂ = b(2) - 4 b(1) + 3 b(0) ≠ 1`, the decoupled combination satisfies:
`(U - 4V + 3W) - (1 - 4q + 3q̂) / (M * (1 - λ₂)) = (v₂ ⬝ᵥ R) / (1 - λ₂)`. -/
theorem sk_at_system_solve_two (b2 b1 b0 q qhat M : ℝ)
    (v R : Fin 3 → ℝ)
    (hsys : v = skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ v + R)
    (hlam2 : b2 - 4 * b1 + 3 * b0 ≠ 1) :
    (skAtEigenvectorTwo ⬝ᵥ v) -
      (1 - 4 * q + 3 * qhat) / (M * (1 - (b2 - 4 * b1 + 3 * b0))) =
        (skAtEigenvectorTwo ⬝ᵥ R) / (1 - (b2 - 4 * b1 + 3 * b0)) := by
  have hmode := sk_at_system_dot_eigenvector_two b2 b1 b0 q qhat M v R hsys
  have hsub : 1 - (b2 - 4 * b1 + 3 * b0) ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam2)
  set Y := skAtEigenvectorTwo ⬝ᵥ v
  set S₂ := (1 - 4 * q + 3 * qhat) / M
  set R₂ := skAtEigenvectorTwo ⬝ᵥ R
  set lam2 := b2 - 4 * b1 + 3 * b0
  have heq : (1 - lam2) * Y = S₂ + R₂ := by linarith [hmode]
  have hY : Y = (S₂ + R₂) / (1 - lam2) := by
    rw [← heq, mul_div_cancel_left₀ Y hsub]
  rw [hY, add_div]
  dsimp [S₂]
  rw [div_div]
  ring

/-- The first eigenvalue `b(2) - 2 b(1) + b(0)` in the solution matches `β² (1 - 2q + q̂)`. -/
theorem sk_at_system_solve_one_beta (β q qhat M : ℝ)
    (v R : Fin 3 → ℝ)
    (hsys : v = skAtSource q qhat M +
      skAtMatrix (skCavityBCoef β q qhat 2) (skCavityBCoef β q qhat 1)
        (skCavityBCoef β q qhat 0) *ᵥ v + R)
    (hlam1 : β ^ 2 * (1 - 2 * q + qhat) ≠ 1) :
    4 * (skAtEigenvectorOne ⬝ᵥ v) -
      4 * (1 - 2 * q + qhat) / (M * (1 - β ^ 2 * (1 - 2 * q + qhat))) =
        4 * (skAtEigenvectorOne ⬝ᵥ R) / (1 - β ^ 2 * (1 - 2 * q + qhat)) := by
  have hlam1' : skCavityBCoef β q qhat 2 - 2 * skCavityBCoef β q qhat 1 +
      skCavityBCoef β q qhat 0 ≠ 1 := by
    rw [sk_at_eigenvalue_one_eq]
    exact hlam1
  have hsol := sk_at_system_solve_one (skCavityBCoef β q qhat 2)
    (skCavityBCoef β q qhat 1) (skCavityBCoef β q qhat 0) q qhat M v R hsys hlam1'
  rw [sk_at_eigenvalue_one_eq] at hsol
  linear_combination 4 * hsol

end SpinGlasses
