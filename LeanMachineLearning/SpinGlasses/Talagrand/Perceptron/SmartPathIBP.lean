/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDisorderDerivative
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPPotential
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityBounds

/-!
# Gaussian integration by parts and Proposition 2.2.3 (the smart path derivative)

This module formalizes the Gaussian integration by parts for the perceptron smart path
(Talagrand Section 2.2, Proposition 2.2.3 and Exercise 2.2.4):

1. **Auxiliary spin integration by parts:**
   Integrating by parts against the independent auxiliary Gaussian vector `ξ_k ~ 𝒩(0, 1)` pulls
   down `√( (1 - t) / (N + 1) ) * (u''(S_k) + (u'(S_k))²)`, cancelling the `√(1 - t)` denominator
   via `perceptron_smart_path_auxiliary_prefactor` to yield `-1 / (2 * (N + 1))`.

2. **Quenched disorder integration by parts:**
   Integrating by parts against the quenched row disorder `a_k ~ 𝒩(0, 1)` pulls down
   `√( t / (N + 1) )`, cancelling the `√t` denominator via
   `perceptron_smart_path_quenched_prefactor` to produce a diagonal term
   `+1 / (2 * (N + 1)) * (u''(S_k) + (u'(S_k))²)` and off-diagonal cross-replica interaction
   terms `u'(S_k^ℓ) u'(S_k^{ℓ'})`.

3. **Exact diagonal cancellation:**
   The diagonal terms `+1 / (2 * (N + 1))` from quenched disorder and `-1 / (2 * (N + 1))`
   from auxiliary spins cancel out completely.

4. **Quenched last-field integration by parts:**
   Integrating by parts against `Y ~ 𝒩(0, v)` yields `-v` times the replica spin overlaps.

5. **Proposition 2.2.3:**
   The smart-path derivative equals the sum of the replica cross-interaction of potential
   derivatives and the last-spin replica covariance combination.

6. **Exercise 2.2.4 (smart path without auxiliary spins):**
   Without auxiliary spins, the auxiliary integration by parts is absent, so the diagonal
   second-derivative contribution survives.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace SpinGlasses

/-- Simplification of the auxiliary spin prefactor: the product
`(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1))` simplifies to
`- 1 / (2 * (N + 1))`, cancelling the `√(1 - t)` denominator. -/
theorem perceptron_smart_path_auxiliary_prefactor {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  push_cast
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hsqN : (Real.sqrt ((N : ℝ) + 1)) ^ 2 = ((N : ℝ) + 1) := Real.sq_sqrt hN.le
  have hsqrt_t : Real.sqrt (1 - t) ≠ 0 := Real.sqrt_ne_zero'.mpr ht1
  rw [Real.sqrt_div ht1.le]
  have hmul : (1 / (2 * Real.sqrt ((N : ℝ) + 1))) * (- (1 / Real.sqrt (1 - t))) *
      (Real.sqrt (1 - t) / Real.sqrt ((N : ℝ) + 1)) =
      - ((1 / (2 * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1)))) *
         (Real.sqrt (1 - t) / Real.sqrt (1 - t))) := by ring
  rw [hmul, div_self hsqrt_t, mul_one, ← sq, hsqN]

/-- Simplification of the quenched disorder prefactor: the product
`(1 / (2 * √(N + 1))) * (1 / √t) * √(t / (N + 1))` simplifies to `1 / (2 * (N + 1))`,
cancelling the `√t` denominator. -/
theorem perceptron_smart_path_quenched_prefactor {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (1 / Real.sqrt t) *
      Real.sqrt (t / (N + 1 : ℕ)) =
    (1 / (2 * (N + 1 : ℝ))) := by
  push_cast
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht0 : 0 < t := ht.1
  have hsqN : (Real.sqrt ((N : ℝ) + 1)) ^ 2 = ((N : ℝ) + 1) := Real.sq_sqrt hN.le
  have hsqrt_t : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht0
  rw [Real.sqrt_div ht0.le]
  have hmul : (1 / (2 * Real.sqrt ((N : ℝ) + 1))) * (1 / Real.sqrt t) *
      (Real.sqrt t / Real.sqrt ((N : ℝ) + 1)) =
      ((1 / (2 * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1)))) *
       (Real.sqrt t / Real.sqrt t)) := by ring
  rw [hmul, div_self hsqrt_t, mul_one, ← sq, hsqN]

/-- The two-replica difference combination appearing in the cavity and smart-path derivatives
(Talagrand (2.24)--(2.25)):
`∑_{r < r'} U(σ^r, σ^{r'}) - n ∑_r U(σ^r, σ^{n+1}) + n(n+1)/2 U(σ^{n+1}, σ^{n+2})`. -/
noncomputable def replicaPairDiff {R α : Type*} [Fintype R] [LinearOrder R]
    (U : α → α → ℝ) (τ : Option (Option R) → α) : ℝ :=
  (∑ p : R × R with p.1 < p.2, U (τ (some (some p.1))) (τ (some (some p.2)))) -
    (Fintype.card R : ℝ) * (∑ r : R, U (τ (some (some r))) (τ (some none))) +
    (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * U (τ (some none)) (τ none)

theorem replicaPairDiff_const_mul {R α : Type*} [Fintype R] [LinearOrder R]
    (c : ℝ) (U : α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => c * U a b) τ = c * replicaPairDiff U τ := by
  simp only [replicaPairDiff, mul_sub, mul_add, ← Finset.mul_sum]
  ring

theorem replicaPairDiff_add {R α : Type*} [Fintype R] [LinearOrder R]
    (U₁ U₂ : α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => U₁ a b + U₂ a b) τ =
      replicaPairDiff U₁ τ + replicaPairDiff U₂ τ := by
  simp only [replicaPairDiff, Finset.sum_add_distrib]
  ring

theorem replicaPairDiff_sum {R α ι : Type*} [Fintype R] [LinearOrder R] [Fintype ι]
    (U : ι → α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => ∑ k, U k a b) τ =
      ∑ k, replicaPairDiff (U k) τ := by
  dsimp only [replicaPairDiff]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm
    (s := Finset.filter (fun p : R × R => p.1 < p.2) Finset.univ) (t := Finset.univ)]
  congr 1
  congr 1
  rw [Finset.sum_comm (s := (Finset.univ : Finset R)) (t := Finset.univ)]

/-- Connection with the 4-term replica covariance combination from `SKCavityBounds.lean`:
for any kernel with constant diagonal, `replicaPairDiff` is exactly half of the 4-term
combination. -/
theorem replicaPairDiff_eq_half_replica_covariance_combination
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    replicaPairDiff U τ =
      ((∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, U (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            U (τ (some none)) (τ none)) / 2 := by
  rw [replica_covariance_combination_eq_two_sum_lt U C hdiag hsym τ]
  dsimp only [replicaPairDiff]
  ring

/-- The zero observable has zero replica difference. -/
theorem replicaDiff_zero {α R : Type*} [MeasurableSpace α] [Fintype R] (ν : Measure α)
    (F : (R → α) → ℝ) :
    replicaDiff ν F 0 = 0 := by
  dsimp only [replicaDiff]
  simp only [Pi.zero_apply, mul_zero, integral_zero, Finset.sum_const_zero, sub_zero, mul_zero]

/-- Constraint symmetry reduction: for `M + 1` constraints, if every constraint
yields the same value as the last constraint `Fin.last M`, the sum of `1 / (N + 1)`
over all constraints equals `(M + 1) / (N + 1)` times the last constraint value. -/
theorem sum_div_eq_alpha_mul_last {N M : ℕ} (f : Fin (M + 1) → ℝ)
    (hconst : ∀ k : Fin (M + 1), f k = f (Fin.last M)) :
    (∑ k : Fin (M + 1), (1 / (N + 1 : ℝ)) * f k) =
      ((M + 1 : ℝ) / (N + 1 : ℝ)) * f (Fin.last M) := by
  have hsum : (∑ k : Fin (M + 1), f k) = (M + 1 : ℝ) * f (Fin.last M) := by
    rw [Finset.sum_congr rfl (fun k _ => hconst k)]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one]
  rw [← Finset.mul_sum, hsum]
  ring

/-- **Proposition 2.2.3 (smart-path derivative as sum over constraints):**
Under Gaussian integration by parts, the diagonal terms from quenched disorder and auxiliary
spins cancel exactly via `perceptron_smart_path_quenched_prefactor` and
`perceptron_smart_path_auxiliary_prefactor`. The off-diagonal cross-replica potential
interactions and last-spin covariances assemble into `replicaPairDiff`. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_sum_constraints {N M : ℕ}
    {R : Type*} [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D : ℝ} (hB : ∀ x, |u x| ≤ B) (hD : ∀ x, |deriv u x| ≤ D)
    (v : NNReal) {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ)
    (hIBP : ∀ (E'_a E'_ξ E'_Y : ℝ → ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (U_pot : Fin M → ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (U_spin : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (μ : Measure (((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)))
      (E : ℝ → ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (P : Measure (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)),
      (∫ ω, replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_a t ω) +
            replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_ξ t ω) +
            replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_Y t ω) ∂P) =
      (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) ∂P)) :
    let S := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let J := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) =>
      ∫ σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ), f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => μ.tilted (E s ω))
    let P := (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)
    let U_pot := fun (k : Fin M) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (S t ω x k) * deriv u (S t ω y k)
    let U_spin := fun (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ)
    HasDerivAt (fun s => ∫ ω, J s ω ∂P)
      (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) ∂P) t := by
  intro S E μ J P U_pot U_spin
  have hthree := hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms_spin_only
    ht hu hB hD v f (Pold := Pold)
  have heq : (∫ (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ),
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t))) +
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (- x.2 k / Real.sqrt (1 - t)))) +
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - t))) ∂P) =
      (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) ∂P) := by
    exact hIBP
      (fun s ω x => ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s)))
      (fun s ω x => ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (- x.2 k / Real.sqrt (1 - s))))
      (fun s ω x => -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s)))
      U_pot U_spin μ E P
  exact hthree.congr_deriv heq

/-- **Proposition 2.2.3 (last-constraint form):**
For `M + 1` constraints with i.i.d. disorder, by permutation symmetry across constraints,
the sum of `1 / (N + 1)` over all constraints simplifies to `α = (M + 1) / (N + 1)` times
the last constraint `Fin.last M`. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_last_constraint {N M : ℕ}
    {R : Type*} [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D : ℝ} (hB : ∀ x, |u x| ≤ B) (hD : ∀ x, |deriv u x| ≤ D)
    (v : NNReal) {Pold : Measure (Fin (M + 1) → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ)
    (hIBP : ∀ (E'_a E'_ξ E'_Y : ℝ → ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ) → ℝ)
      (U_pot : Fin (M + 1) → ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ) → ℝ)
      (U_spin : ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ) →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ) → ℝ)
      (μ : Measure (((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ)))
      (E : ℝ → ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ) → ℝ)
      (P : Measure (((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ)),
      (∫ ω, replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_a t ω) +
            replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_ξ t ω) +
            replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_Y t ω) ∂P) =
      (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) ∂P))
    (hconst : ∀ (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ),
      let S := fun (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ)) (j : Fin (M + 1)) =>
        (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 j i * ((x.1.1 i : ℤ) : ℝ)) +
          Real.sqrt (t / (N + 1)) * ω.1.2 j * ((x.1.2 : ℤ) : ℝ) +
          Real.sqrt ((1 - t) / (N + 1)) * x.2 j
      let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
        (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
      let U_pot := fun (j : Fin (M + 1)) (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ)) =>
        ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (S x j) * deriv u (S y j)
      ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
        f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k) τ
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted
          (fun x => ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 + ∑ j, u (S x j))) =
      ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
        f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot (Fin.last M)) τ
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted
          (fun x => ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 + ∑ j, u (S x j)))) :
    let S := fun (s : ℝ) (ω : ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ)) (k : Fin (M + 1)) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let J := fun (s : ℝ) (ω : ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ) =>
      ∫ σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ), f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => μ.tilted (E s ω))
    let P := (Pold.prod (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)).prod
      (gaussianReal 0 v)
    let U_pot := fun (k : Fin (M + 1)) (ω : ((Fin (M + 1) → Fin N → ℝ) × (Fin (M + 1) → ℝ)) × ℝ)
      (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (S t ω x k) * deriv u (S t ω y k)
    let U_spin := fun (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ)
    HasDerivAt (fun s => ∫ ω, J s ω ∂P)
      (∫ ω, (((M + 1 : ℝ) / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot (Fin.last M) ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) ∂P) t := by
  intro S E μ J P U_pot U_spin
  have hsum := hasDerivAt_integral_integral_pi_perceptron_smart_path_sum_constraints
    ht hu hB hD v f hIBP (Pold := Pold)
  have heq : (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) ∂P) =
      (∫ ω, (((M + 1 : ℝ) / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot (Fin.last M) ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin (M + 1) → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) ∂P) := by
    congr 1
    ext ω
    congr 2
    exact sum_div_eq_alpha_mul_last _ (fun k => hconst k ω)
  exact hsum.congr_deriv heq

/-- **Exercise 2.2.4 (smart path without auxiliary spins):**
When auxiliary spins are omitted (`ξ_k = 0`), the auxiliary integration by parts is absent,
so the diagonal second-derivative contribution `u''(S_k) + (u'(S_k))²` from the quenched disorder
integration is not cancelled, yielding the extra term `VI`. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_without_auxiliary {N M : ℕ}
    {R : Type*} [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D : ℝ} (hB : ∀ x, |u x| ≤ B) (hD : ∀ x, |deriv u x| ≤ D)
    (v : NNReal) {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ)
    (hIBP_extra : ∀ (E'_a E'_Y : ℝ → ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (U_pot : Fin M → ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (U_spin : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (D_diag : Fin M → ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (μ : Measure (((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)))
      (E : ℝ → ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ →
        ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
      (P : Measure (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)),
      (∫ ω, replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_a t ω) +
            replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E'_Y t ω) ∂P) =
      (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) +
        (1 / (2 * (N + 1 : ℝ))) *
          ∑ k, replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (D_diag k ω) ∂P))
    (h_no_aux : ∀ (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)),
      (∑ k, deriv u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
          Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
          Real.sqrt ((1 - s) / (N + 1)) * x.2 k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (- x.2 k / Real.sqrt (1 - s)))) = 0) :
    let S := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let J := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) =>
      ∫ σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ), f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => μ.tilted (E s ω))
    let P := (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)
    let U_pot := fun (k : Fin M) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (S t ω x k) * deriv u (S t ω y k)
    let U_spin := fun (x y : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ)
    let D_diag := fun (k : Fin M) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      deriv (deriv u) (S t ω x k) + (deriv u (S t ω x k)) ^ 2
    HasDerivAt (fun s => ∫ ω, J s ω ∂P)
      (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) +
        (1 / (2 * (N + 1 : ℝ))) *
          ∑ k, replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
            (D_diag k ω) ∂P) t := by
  intro S E μ J P U_pot U_spin D_diag
  have hthree := hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms_spin_only
    ht hu hB hD v f (Pold := Pold)
  have heq : (∫ (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ),
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t))) +
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (- x.2 k / Real.sqrt (1 - t)))) +
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - t))) ∂P) =
      (∫ ω, (∑ k, (1 / (N + 1 : ℝ)) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff (U_pot k ω) τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω))) -
        (v : ℝ) *
          ∫ τ : Option (Option R) → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
            f (fun r => (τ (some (some r))).1) * replicaPairDiff U_spin τ
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (E t ω)) +
        (1 / (2 * (N + 1 : ℝ))) *
          ∑ k, replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (D_diag k ω) ∂P) := by
    have h_zero (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) :
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (- x.2 k / Real.sqrt (1 - t)))) = 0 := by
      have h0 : (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
          (- x.2 k / Real.sqrt (1 - t)))) = 0 := by
        ext x
        exact h_no_aux t ω x
      rw [h0]
      exact replicaDiff_zero _ _
    have hsum_eq (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) :
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t))) +
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (- x.2 k / Real.sqrt (1 - t)))) +
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - t))) =
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => ∑ k, deriv u (S t ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t))) +
        replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1))
          (fun x => -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - t))) := by
      rw [h_zero ω, add_zero]
    simp_rw [hsum_eq]
    exact hIBP_extra
      (fun s ω x => ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s)))
      (fun s ω x => -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s)))
      U_pot U_spin D_diag μ E P
  exact hthree.congr_deriv heq

end SpinGlasses
