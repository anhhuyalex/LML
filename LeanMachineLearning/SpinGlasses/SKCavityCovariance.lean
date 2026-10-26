/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityDecoupledMonomials
public import LeanMachineLearning.SpinGlasses.SKCavityTaylor
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag

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

/-- The index type for the three replica families in the cavity path derivative:
1. `Sum.inl s`: distinct pairs `1 ≤ ℓ < ℓ' ≤ n` among old replicas, weight `1`
2. `Sum.inr (Sum.inl s)`: pairs `(ℓ, n+1)` between old and first extra replica, weight `-n`
3. `Sum.inr (Sum.inr _)`: pair `(n+1, n+2)` between the two extra replicas, weight `n(n+1)/2`. -/
abbrev SKCavityReplicaPair (n : ℕ) : Type :=
  FinPairs n ⊕ (Fin n ⊕ Unit)

/-- The pair of lifted replicas `Option (Option (Fin n))` corresponding to an index. -/
def skCavityReplicaPairMap {n : ℕ} (j : SKCavityReplicaPair n) :
    Option (Option (Fin n)) × Option (Option (Fin n)) :=
  match j with
  | Sum.inl s => (some (some s.val.1), some (some s.val.2))
  | Sum.inr (Sum.inl s) => (some (some s), some none)
  | Sum.inr (Sum.inr _) => (some none, none)

/-- The weights of the three replica families in Eq. (1.152). -/
noncomputable def skCavityReplicaPairWeight (n : ℕ) (j : SKCavityReplicaPair n) : ℝ :=
  match j with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => -(n : ℝ)
  | Sum.inr (Sum.inr _) => (n : ℝ) * ((n : ℝ) + 1) / 2

/-- The replicas in every family pair are distinct. -/
theorem skCavityReplicaPair_ne {n : ℕ} (j : SKCavityReplicaPair n) :
    (skCavityReplicaPairMap j).1 ≠ (skCavityReplicaPairMap j).2 := by
  rcases j with s | s | s
  · have h := s.property
    simp only [skCavityReplicaPairMap, ne_eq, Option.some.injEq]
    exact h.ne
  · simp [skCavityReplicaPairMap]
  · simp [skCavityReplicaPairMap]

/-- Coincidence count of a replica pair `j` with the pair `{x, y}` of old replicas. -/
def skCavityReplicaPairCoincidences {n : ℕ} (x y : Fin n) (j : SKCavityReplicaPair n) : ℕ :=
  sk_cavity_coincidences (some (some x)) (some (some y))
    (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2

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
          (sk_cavity_b_coef β q qhat (skCavityReplicaPairCoincidences x y j) *
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
      sk_cavity_b_unscaled q qhat (sk_cavity_coincidences (so x) (so y) a b) *
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
            ((((τ (so x) (Fin.last N) : ℤˣ) : ℝ) * ((τ (so y) (Fin.last N) : ℤˣ) : ℝ) - q) *
              (((τ a (Fin.last N) : ℤˣ) : ℝ) * ((τ b (Fin.last N) : ℤˣ) : ℝ))) := fun τ => by
      simp only [f, K, Gab]
      ring
    simp_rw [hpt]
    have hso : so x ≠ so y := fun h => hxy (Option.some.inj (Option.some.inj h))
    exact sk_cavity_decoupled_endpoint_pair_cov N β q h hfix qhat hqhat hso hab (Gab a b)
  let Gj : SKCavityReplicaPair n → (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun j τ =>
    f τ * K (τ (skCavityReplicaPairMap j).1) (τ (skCavityReplicaPairMap j).2)
  have hS : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      f τ *
          ((∑ p : Fin n × Fin n with p.1 < p.2,
              K (τ (so p.1)) (τ (so p.2))) -
            (n : ℝ) * ∑ r : Fin n, K (τ (so r)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none)) =
        ∑ j, skCavityReplicaPairWeight n j * Gj j τ := fun τ => by
    simp only [SKCavityReplicaPair, Gj, skCavityReplicaPairWeight, skCavityReplicaPairMap, so,
      Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, ← Finset.mul_sum]
    rw [sum_filter_lt_eq_sum_subtype fun s : Fin n × Fin n =>
      K (τ (some (some s.1))) (τ (some (some s.2)))]
    simp only [mul_add, mul_sub]
    ring
  simp_rw [hS]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ (skCavityReplicaPairWeight n) Gj]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hne := skCavityReplicaPair_ne j
  have hj := hT (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2 hne
  dsimp [Gj]
  rw [hj]
  simp only [sk_cavity_b_coef, skCavityReplicaPairCoincidences, Gab]
  have hmul : ∀ (X : ℝ),
      sk_cavity_b_unscaled q qhat (sk_cavity_coincidences (so x) (so y)
        (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2) *
        (β ^ 2 * X) =
      β ^ 2 * sk_cavity_b_unscaled q qhat (sk_cavity_coincidences (so x) (so y)
        (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2) * X := fun X => by ring
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

/-- The 3×3 matrix of the cavity covariance system (Talagrand Eq. 1.234):
`[b(2),              -4 b(1),              3 b(0)             ]`
`[b(1),  b(2) - 2 b(1) - 3 b(0),        6 b(0) - 3 b(1)       ]`
`[b(0),        4 b(1) - 8 b(0),   b(2) - 8 b(1) + 10 b(0)     ]` -/
def sk_at_matrix (b2 b1 b0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![b2, -4 * b1, 3 * b0],
    ![b1, b2 - 2 * b1 - 3 * b0, 6 * b0 - 3 * b1],
    ![b0, 4 * b1 - 8 * b0, b2 - 8 * b1 + 10 * b0]]

/-- The first eigenvector of the transposed AT matrix: `(1, -2, 1)`. -/
def sk_at_eigenvector_one : Fin 3 → ℝ :=
  ![1, -2, 1]

/-- The second eigenvector of the transposed AT matrix: `(1, -4, 3)`. -/
def sk_at_eigenvector_two : Fin 3 → ℝ :=
  ![1, -4, 3]

/-- **Talagrand, Eq. (1.235): universal eigenvector `(1, -2, 1)` of the transposed AT matrix.**
For any coefficients `b(2), b(1), b(0)`, `(1, -2, 1)` is an eigenvector of
`(sk_at_matrix b2 b1 b0)ᵀ` with eigenvalue `λ₁ = b(2) - 2 b(1) + b(0)`. -/
theorem sk_at_matrix_transpose_mulVec_one (b2 b1 b0 : ℝ) :
    (sk_at_matrix b2 b1 b0)ᵀ *ᵥ sk_at_eigenvector_one =
      (b2 - 2 * b1 + b0) • sk_at_eigenvector_one := by
  ext i
  fin_cases i
  · change (∑ j : Fin 3, (sk_at_matrix b2 b1 b0)ᵀ 0 j * sk_at_eigenvector_one j) = _
    rw [Fin.sum_univ_three]
    change b2 * 1 + b1 * (-2) + b0 * 1 = (b2 - 2 * b1 + b0) * 1
    ring
  · change (∑ j : Fin 3, (sk_at_matrix b2 b1 b0)ᵀ 1 j * sk_at_eigenvector_one j) = _
    rw [Fin.sum_univ_three]
    change (-4 * b1) * 1 + (b2 - 2 * b1 - 3 * b0) * (-2) + (4 * b1 - 8 * b0) * 1 =
        (b2 - 2 * b1 + b0) * (-2)
    ring
  · change (∑ j : Fin 3, (sk_at_matrix b2 b1 b0)ᵀ 2 j * sk_at_eigenvector_one j) = _
    rw [Fin.sum_univ_three]
    change (3 * b0) * 1 + (6 * b0 - 3 * b1) * (-2) + (b2 - 8 * b1 + 10 * b0) * 1 =
        (b2 - 2 * b1 + b0) * 1
    ring

/-- **Talagrand, Eq. (1.236): universal eigenvector `(1, -4, 3)` of the transposed AT matrix.**
For any coefficients `b(2), b(1), b(0)`, `(1, -4, 3)` is an eigenvector of
`(sk_at_matrix b2 b1 b0)ᵀ` with eigenvalue `λ₂ = b(2) - 4 b(1) + 3 b(0)`. -/
theorem sk_at_matrix_transpose_mulVec_two (b2 b1 b0 : ℝ) :
    (sk_at_matrix b2 b1 b0)ᵀ *ᵥ sk_at_eigenvector_two =
      (b2 - 4 * b1 + 3 * b0) • sk_at_eigenvector_two := by
  ext i
  fin_cases i
  · change (∑ j : Fin 3, (sk_at_matrix b2 b1 b0)ᵀ 0 j * sk_at_eigenvector_two j) = _
    rw [Fin.sum_univ_three]
    change b2 * 1 + b1 * (-4) + b0 * 3 = (b2 - 4 * b1 + 3 * b0) * 1
    ring
  · change (∑ j : Fin 3, (sk_at_matrix b2 b1 b0)ᵀ 1 j * sk_at_eigenvector_two j) = _
    rw [Fin.sum_univ_three]
    change (-4 * b1) * 1 + (b2 - 2 * b1 - 3 * b0) * (-4) + (4 * b1 - 8 * b0) * 3 =
        (b2 - 4 * b1 + 3 * b0) * (-4)
    ring
  · change (∑ j : Fin 3, (sk_at_matrix b2 b1 b0)ᵀ 2 j * sk_at_eigenvector_two j) = _
    rw [Fin.sum_univ_three]
    change (3 * b0) * 1 + (6 * b0 - 3 * b1) * (-4) + (b2 - 8 * b1 + 10 * b0) * 3 =
        (b2 - 4 * b1 + 3 * b0) * 3
    ring

/-- The first eigenvalue `λ₁ = b(2) - 2 b(1) + b(0)` expressed in terms of `(β, q, q̂)`:
`λ₁ = β² (1 - 2 q + q̂)`. -/
theorem sk_at_eigenvalue_one_eq (β q qhat : ℝ) :
    sk_cavity_b_coef β q qhat 2 - 2 * sk_cavity_b_coef β q qhat 1 +
      sk_cavity_b_coef β q qhat 0 =
    β ^ 2 * (1 - 2 * q + qhat) := by
  dsimp [sk_cavity_b_coef, sk_cavity_b_unscaled]
  ring

/-- The second eigenvalue `λ₂ = b(2) - 4 b(1) + 3 b(0)` expressed in terms of `(β, q, q̂)`:
`λ₂ = β² (1 - 4 q + 3 q̂)`. -/
theorem sk_at_eigenvalue_two_eq (β q qhat : ℝ) :
    sk_cavity_b_coef β q qhat 2 - 4 * sk_cavity_b_coef β q qhat 1 +
      3 * sk_cavity_b_coef β q qhat 0 =
    β ^ 2 * (1 - 4 * q + 3 * qhat) := by
  dsimp [sk_cavity_b_coef, sk_cavity_b_unscaled]
  ring

end SpinGlasses
