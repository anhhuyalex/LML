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

/-!
# The rectangular combination at the decoupled endpoint (Talagrand's Lemma 1.8.4)

At the decoupled endpoint of the cavity path, the derivative of the average of
`(ε₁ - ε₂)(ε₃ - ε₄) f⁻` is `β² (1 - 2 q + q̂) ν₀(f⁻ (R⁻₁₃ - R⁻₁₄ - R⁻₂₃ + R⁻₂₄))` with
`q̂ = 𝔼 tanh⁴ Y`.  The proof is the counting of Lemma 1.8.2 specialised to the rectangular
combination: by the decoupled average of four last spins, the coefficient of the pair `(a, b)` is
`(1 - 2q + q̂) (ϑ_i(a) + ϑ_i(b)) (ϑ_j(a) + ϑ_j(b))` with `ϑ_i(r) = 1_{r = i₁} - 1_{r = i₂}`; it
vanishes except for the four pairs `(i, j)` of the rectangle.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The coefficient of a pair in the rectangular combination.**  Counting the coincidences of
`x₁, x₂, y₁, y₂` with a pair `a ≠ b` turns the alternating sum of the decoupled moments
`m_{4 - 2c}` into `(m₀ - 2 m₂ + m₄)` times the product of the two signed memberships. -/
theorem rect_coeff {R : Type*} [DecidableEq R] {x₁ x₂ y₁ y₂ a b : R} (hab : a ≠ b)
    (M : ℕ → ℝ) :
    M (4 - 2 * ((if x₁ = a then 1 else 0) + (if x₁ = b then 1 else 0) +
        (if y₁ = a then 1 else 0) + (if y₁ = b then 1 else 0))) -
      M (4 - 2 * ((if x₁ = a then 1 else 0) + (if x₁ = b then 1 else 0) +
        (if y₂ = a then 1 else 0) + (if y₂ = b then 1 else 0))) -
      M (4 - 2 * ((if x₂ = a then 1 else 0) + (if x₂ = b then 1 else 0) +
        (if y₁ = a then 1 else 0) + (if y₁ = b then 1 else 0))) +
      M (4 - 2 * ((if x₂ = a then 1 else 0) + (if x₂ = b then 1 else 0) +
        (if y₂ = a then 1 else 0) + (if y₂ = b then 1 else 0))) =
    (M 0 - 2 * M 2 + M 4) *
      ((((if x₁ = a then 1 else 0) + (if x₁ = b then 1 else 0) : ℕ) : ℝ) -
        (((if x₂ = a then 1 else 0) + (if x₂ = b then 1 else 0) : ℕ) : ℝ)) *
      ((((if y₁ = a then 1 else 0) + (if y₁ = b then 1 else 0) : ℕ) : ℝ) -
        (((if y₂ = a then 1 else 0) + (if y₂ = b then 1 else 0) : ℕ) : ℝ)) := by
  have hδ : ∀ x : R, ((if x = a then 1 else 0) + (if x = b then 1 else 0) : ℕ) = 0 ∨
      ((if x = a then 1 else 0) + (if x = b then 1 else 0) : ℕ) = 1 := fun x => by
    by_cases h1 : x = a
    · subst h1
      simp [hab]
    · by_cases h2 : x = b <;> simp [h1, h2, Ne.symm hab]
  have e : ∀ x y : R, ((if x = a then 1 else 0) + (if x = b then 1 else 0) +
        (if y = a then 1 else 0) + (if y = b then 1 else 0) : ℕ) =
      ((if x = a then 1 else 0) + (if x = b then 1 else 0) : ℕ) +
        ((if y = a then 1 else 0) + (if y = b then 1 else 0) : ℕ) := fun x y => by omega
  simp only [e]
  rcases hδ x₁ with h1 | h1 <;> rcases hδ x₂ with h2 | h2 <;> rcases hδ y₁ with h3 | h3 <;>
    rcases hδ y₂ with h4 | h4 <;> simp only [h1, h2, h3, h4] <;> norm_num <;> ring

/-- **Decoupled average of a rectangular sign polynomial times two last spins.**  For distinct
`x₁, x₂` and `y₁, y₂` (distinct from the `x`'s) and a pair `a ≠ b`,
`ν₀(f⁻ (ε_{x₁} - ε_{x₂})(ε_{y₁} - ε_{y₂}) ε_a ε_b)` is
`(1 - 2 q + q̂)` times the signed memberships of `{a, b}` in `{x₁, x₂}` and `{y₁, y₂}` times
the average of `f⁻` at the decoupled endpoint.  Here `q̂ = 𝔼 tanh⁴ Y`. -/
theorem sk_cavity_decoupled_rect_monomial (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q)
    {R : Type*} [Fintype R] [DecidableEq R] {x₁ x₂ y₁ y₂ a b : R} (hab : a ≠ b)
    (hx₁y₁ : x₁ ≠ y₁) (hx₁y₂ : x₁ ≠ y₂) (hx₂y₁ : x₂ ≠ y₁) (hx₂y₂ : x₂ ≠ y₂)
    (G : (R → Fin N → ℤˣ) → ℝ) :
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
          G (fun r i => σ r i.castSucc) *
            ((((σ x₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ x₂ (Fin.last N) : ℤˣ) : ℝ)) *
              (((σ y₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ y₂ (Fin.last N) : ℤˣ) : ℝ)) *
              (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    ((∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1) *
      ((((if x₁ = a then 1 else 0) + (if x₁ = b then 1 else 0) : ℕ) : ℝ) -
        (((if x₂ = a then 1 else 0) + (if x₂ = b then 1 else 0) : ℕ) : ℝ)) *
      ((((if y₁ = a then 1 else 0) + (if y₁ = b then 1 else 0) : ℕ) : ℝ) -
        (((if y₂ = a then 1 else 0) + (if y₂ = b then 1 else 0) : ℕ) : ℝ)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let X : Bool → R := fun u => if u then x₁ else x₂
  let Y : Bool → R := fun v => if v then y₁ else y₂
  let sg : Bool → ℝ := fun u => if u then 1 else -1
  let cw : Bool × Bool → ℝ := fun j => sg j.1 * sg j.2
  let Gj : Bool × Bool → (R → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    G (fun r i => σ r i.castSucc) *
      (((σ (X j.1) (Fin.last N) : ℤˣ) : ℝ) * ((σ (Y j.2) (Fin.last N) : ℤˣ) : ℝ) *
        ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
  have hpt : ∀ σ : R → Fin (N + 1) → ℤˣ,
      G (fun r i => σ r i.castSucc) *
            ((((σ x₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ x₂ (Fin.last N) : ℤˣ) : ℝ)) *
              (((σ y₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ y₂ (Fin.last N) : ℤˣ) : ℝ)) *
              (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) =
        ∑ j, cw j * Gj j σ := fun σ => by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cw, Gj, sg, X, Y, ite_true, ite_false,
      Bool.false_eq_true]
    ring
  simp_rw [hpt]
  have hlin := integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    (Finset.univ : Finset (Bool × Bool)) cw Gj
  refine hlin.trans ?_
  have hend : ∀ (u v : Bool), ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ, Gj (u, v) σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^
        (4 - 2 * ((if X u = a then 1 else 0) + (if X u = b then 1 else 0) +
          (if Y v = a then 1 else 0) + (if Y v = b then 1 else 0))) ∂(gaussianReal 0 1)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    fun u v => sk_cavity_decoupled_endpoint_quartic N β q h
      (x := X u) (y := Y v) (a := a) (b := b)
      (by cases u <;> cases v <;> simp [X, Y, hx₁y₁, hx₁y₂, hx₂y₁, hx₂y₂]) hab G
  set O : ℝ := ∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    with hO
  set m : ℕ → ℝ := fun k => ∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ k ∂(gaussianReal 0 1)
    with hm
  have hm0 : m 0 = 1 := by simp [hm]
  have hm2 : m 2 = q := hfix
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, hend, cw, sg, X, Y, ite_true, ite_false, Bool.false_eq_true]
  have key := rect_coeff (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂) hab m
  rw [hm0, hm2] at key
  calc _ = (m (4 - 2 * ((if x₁ = a then 1 else 0) + (if x₁ = b then 1 else 0) +
        (if y₁ = a then 1 else 0) + (if y₁ = b then 1 else 0))) -
      m (4 - 2 * ((if x₁ = a then 1 else 0) + (if x₁ = b then 1 else 0) +
        (if y₂ = a then 1 else 0) + (if y₂ = b then 1 else 0))) -
      m (4 - 2 * ((if x₂ = a then 1 else 0) + (if x₂ = b then 1 else 0) +
        (if y₁ = a then 1 else 0) + (if y₁ = b then 1 else 0))) +
      m (4 - 2 * ((if x₂ = a then 1 else 0) + (if x₂ = b then 1 else 0) +
        (if y₂ = a then 1 else 0) + (if y₂ = b then 1 else 0)))) * O := by ring
    _ = _ := by rw [key]; ring

/-- **Talagrand's Lemma 1.8.4, Eq. (1.237)** (for the rectangle of replicas `i₁, i₂ | j₁, j₂`).
For an observable `f = f⁻ · (ε_{i₁} - ε_{i₂})(ε_{j₁} - ε_{j₂})` the first derivative at the
decoupled endpoint is `β² (1 - 2 q + q̂)` times the decoupled average of
`f⁻ (R⁻_{i₁ j₁} - R⁻_{i₁ j₂} - R⁻_{i₂ j₁} + R⁻_{i₂ j₂})`, where `q̂ = 𝔼 tanh⁴ Y` and
`R⁻_{ab} = (N+1)⁻¹ ∑_{i<N} σᵃ_i σᵇ_i`. -/
theorem sk_cavity_deriv_zero_rect (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q)
    {i₁ i₂ j₁ j₂ : Fin n} (h13 : i₁ ≠ j₁) (h14 : i₁ ≠ j₂) (h23 : i₂ ≠ j₁) (h24 : i₂ ≠ j₂)
    (F : (Fin n → Fin N → ℤˣ) → ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (hf : ∀ σ, f σ = F (fun r i => σ r i.castSucc) *
      ((((σ i₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ i₂ (Fin.last N) : ℤˣ) : ℝ)) *
        (((σ j₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ j₂ (Fin.last N) : ℤˣ) : ℝ)))) :
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
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    β ^ 2 * ((∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1) *
      ∫ g', ∫ ρ : Fin n → Fin N → ℤˣ, F ρ *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₁ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₁ i : ℝ)) -
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₁ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₂ i : ℝ)) -
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₂ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₁ i : ℝ)) +
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₂ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₂ i : ℝ)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E K
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  set c2 : ℝ := (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1
    with hc2
  let so : Fin n → Option (Option (Fin n)) := fun r => some (some r)
  let Gab : Option (Option (Fin n)) → Option (Option (Fin n)) →
      (Option (Option (Fin n)) → Fin N → ℤˣ) → ℝ := fun a b ρ =>
    F (fun r => ρ (so r)) * (β ^ 2 * ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (ρ a i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ b i : ℝ)) - q))
  have hT : ∀ a b : Option (Option (Fin n)), a ≠ b →
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (so r)) * K (τ a) (τ b)
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      c2 * ((((if so i₁ = a then 1 else 0) + (if so i₁ = b then 1 else 0) : ℕ) : ℝ) -
          (((if so i₂ = a then 1 else 0) + (if so i₂ = b then 1 else 0) : ℕ) : ℝ)) *
        ((((if so j₁ = a then 1 else 0) + (if so j₁ = b then 1 else 0) : ℕ) : ℝ) -
          (((if so j₂ = a then 1 else 0) + (if so j₂ = b then 1 else 0) : ℕ) : ℝ)) *
        ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ, Gab a b ρ
          ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := fun a b hab => by
    have hpt : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (so r)) * K (τ a) (τ b) =
          Gab a b (fun r i => τ r i.castSucc) *
            ((((τ (so i₁) (Fin.last N) : ℤˣ) : ℝ) - ((τ (so i₂) (Fin.last N) : ℤˣ) : ℝ)) *
              (((τ (so j₁) (Fin.last N) : ℤˣ) : ℝ) - ((τ (so j₂) (Fin.last N) : ℤˣ) : ℝ)) *
              (((τ a (Fin.last N) : ℤˣ) : ℝ) * ((τ b (Fin.last N) : ℤˣ) : ℝ))) := fun τ => by
      rw [hf]
      simp only [K, Gab]
      ring
    simp_rw [hpt]
    exact sk_cavity_decoupled_rect_monomial N β q h hfix (x₁ := so i₁) (x₂ := so i₂)
      (y₁ := so j₁) (y₂ := so j₂) hab (by simpa [so] using h13) (by simpa [so] using h14)
      (by simpa [so] using h23) (by simpa [so] using h24) (Gab a b)
  let Gj : SKCavityReplicaPair n → (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun j τ =>
    f (fun r => τ (so r)) * K (τ (skCavityReplicaPairMap j).1) (τ (skCavityReplicaPairMap j).2)
  have hS : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      f (fun r => τ (some (some r))) *
          ((∑ p : Fin n × Fin n with p.1 < p.2,
              K (τ (some (some p.1))) (τ (some (some p.2)))) -
            (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none)) =
        ∑ j, skCavityReplicaPairWeight n j * Gj j τ := fun τ =>
    sk_cavity_signed_pair_mul_sum K τ (f (fun r => τ (so r)))
  simp_rw [hS]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ (skCavityReplicaPairWeight n) Gj]
  let ϑi : Fin n → ℝ := fun r => (if i₁ = r then 1 else 0) - (if i₂ = r then 1 else 0)
  let ϑj : Fin n → ℝ := fun r => (if j₁ = r then 1 else 0) - (if j₂ = r then 1 else 0)
  let W : Fin n → Fin n → ℝ := fun a b => ∫ g', ∫ ρ : Fin n → Fin N → ℤˣ,
      F ρ * (β ^ 2 * ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (ρ a i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ b i : ℝ)) - q))
    ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
      (fun r : Fin N → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
        h * ∑ i : Fin N, (r i : ℝ)))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hW : ∀ a b : Fin n, (∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
      Gab (so a) (so b) ρ
          ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = W a b := fun a b => by
    refine integral_congr_ae (ae_of_all _ fun g' => ?_)
    exact integral_pi_option_option_count_tilted_marginal _
      (fun σ : Fin n → Fin N → ℤˣ => F σ * (β ^ 2 * ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (σ a i : ℝ)) ⬝ᵥ fun i : Fin N => (σ b i : ℝ)) - q)))
  have hWsymm : ∀ a b, W a b = W b a := fun a b => by
    simp only [W, dotProduct_comm]
  have hϑ : ∀ r, ϑi r * ϑj r = 0 := fun r => by
    by_cases ha : i₁ = r
    · subst ha
      simp [ϑi, ϑj, h13.symm, h14.symm]
    · by_cases hb : i₂ = r
      · subst hb
        simp [ϑi, ϑj, h23.symm, h24.symm]
      · simp [ϑi, ha, hb]
  have hDx : ∀ a b : Fin n,
      ((((if so i₁ = so a then 1 else 0) + (if so i₁ = so b then 1 else 0) : ℕ) : ℝ) -
        (((if so i₂ = so a then 1 else 0) + (if so i₂ = so b then 1 else 0) : ℕ) : ℝ)) =
      ϑi a + ϑi b := fun a b => by
    simp only [so, ϑi, Option.some.injEq]
    push_cast
    ring
  have hDy : ∀ a b : Fin n,
      ((((if so j₁ = so a then 1 else 0) + (if so j₁ = so b then 1 else 0) : ℕ) : ℝ) -
        (((if so j₂ = so a then 1 else 0) + (if so j₂ = so b then 1 else 0) : ℕ) : ℝ)) =
      ϑj a + ϑj b := fun a b => by
    simp only [so, ϑj, Option.some.injEq]
    push_cast
    ring
  have hT1 : ∀ p : FinPairs n, (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, Gj (Sum.inl p) τ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      c2 * (ϑi p.1.1 * ϑj p.1.2 + ϑi p.1.2 * ϑj p.1.1) * W p.1.1 p.1.2 := fun p => by
    have := hT (some (some p.1.1)) (some (some p.1.2)) (skCavityReplicaPair_ne (Sum.inl p))
    refine this.trans ?_
    rw [hDx, hDy, hW]
    have h0 := hϑ p.1.1
    have h1 := hϑ p.1.2
    linear_combination (c2 * W p.1.1 p.1.2) * (h0 + h1)
  have hT2 : ∀ r : Fin n, (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, Gj (Sum.inr (Sum.inl r)) τ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = 0 := fun r => by
    have := hT (some (some r)) (some none) (skCavityReplicaPair_ne (Sum.inr (Sum.inl r)))
    refine this.trans ?_
    have hx : ((((if so i₁ = some (some r) then 1 else 0) +
          (if so i₁ = some none then 1 else 0) : ℕ) : ℝ) -
        (((if so i₂ = some (some r) then 1 else 0) +
          (if so i₂ = some none then 1 else 0) : ℕ) : ℝ)) = ϑi r := by
      simp only [so, ϑi, Option.some.injEq, reduceCtorEq, ite_false, add_zero]
      push_cast
      ring
    have hy : ((((if so j₁ = some (some r) then 1 else 0) +
          (if so j₁ = some none then 1 else 0) : ℕ) : ℝ) -
        (((if so j₂ = some (some r) then 1 else 0) +
          (if so j₂ = some none then 1 else 0) : ℕ) : ℝ)) = ϑj r := by
      simp only [so, ϑj, Option.some.injEq, reduceCtorEq, ite_false, add_zero]
      push_cast
      ring
    rw [hx, hy, mul_assoc c2, hϑ r]
    simp
  have hT3 : (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, Gj (Sum.inr (Sum.inr ())) τ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = 0 := by
    have := hT (some none) none (skCavityReplicaPair_ne (Sum.inr (Sum.inr ())))
    refine this.trans ?_
    simp [so]
  simp only [skCavityReplicaPairWeight, Fintype.sum_sum_type, Finset.univ_unique, hT2, hT3,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl fun p _ => by rw [one_mul, hT1 p]]
  -- the four-term combination of the old-system averages
  let Eold : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ := fun g' r =>
    (Real.sqrt (N + 1))⁻¹ * β *
      (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
    h * ∑ i : Fin N, (r i : ℝ)
  have hEold : ∀ r : Fin N → ℤˣ, Measurable (fun g' : FinPairs N → ℝ => Eold g' r) := fun r => by
    dsimp [Eold]
    fun_prop
  let Iu : Bool → Fin n := fun u => if u then i₁ else i₂
  let Jv : Bool → Fin n := fun v => if v then j₁ else j₂
  let sg : Bool → ℝ := fun u => if u then 1 else -1
  let H : Bool × Bool → (Fin n → Fin N → ℤˣ) → ℝ := fun j ρ =>
    F ρ * (β ^ 2 * ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (ρ (Iu j.1) i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ (Jv j.2) i : ℝ)) - q))
  have hlin := integral_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    (R := Fin n) Eold hEold (Finset.univ : Finset (Bool × Bool)) (fun j => sg j.1 * sg j.2) H
  have hcomb : (W i₁ j₁ - W i₁ j₂ - W i₂ j₁ + W i₂ j₂) = β ^ 2 *
      ∫ g', ∫ ρ : Fin n → Fin N → ℤˣ, F ρ *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₁ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₁ i : ℝ)) -
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₁ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₂ i : ℝ)) -
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₂ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₁ i : ℝ)) +
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₂ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₂ i : ℝ)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Eold g'))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have hLHS : (W i₁ j₁ - W i₁ j₂ - W i₂ j₁ + W i₂ j₂) =
        ∑ j : Bool × Bool, (sg j.1 * sg j.2) * ∫ g', ∫ ρ : Fin n → Fin N → ℤˣ, H j ρ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Eold g'))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, sg, Iu, Jv, H, W, Eold, ite_true,
        ite_false, Bool.false_eq_true]
      ring
    rw [hLHS, ← hlin]
    have hpt : ∀ ρ : Fin n → Fin N → ℤˣ, ∑ j : Bool × Bool, (sg j.1 * sg j.2) * H j ρ =
        β ^ 2 * (F ρ *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₁ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₁ i : ℝ)) -
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₁ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₂ i : ℝ)) -
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₂ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₁ i : ℝ)) +
            (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ i₂ i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ j₂ i : ℝ))))
        := fun ρ => by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, sg, Iu, Jv, H, ite_true, ite_false,
        Bool.false_eq_true]
      ring
    simp_rw [hpt, integral_const_mul]
  have hsi : ∀ Φ : Fin n → ℝ, ∑ a, ϑi a * Φ a = Φ i₁ - Φ i₂ := fun Φ => by
    simp [ϑi, sub_mul, Finset.sum_sub_distrib, ite_mul]
  have hsj : ∀ Φ : Fin n → ℝ, ∑ b, ϑj b * Φ b = Φ j₁ - Φ j₂ := fun Φ => by
    simp [ϑj, sub_mul, Finset.sum_sub_distrib, ite_mul]
  have hXX : (∑ a, ∑ b, ϑi a * ϑj b * W a b) = W i₁ j₁ - W i₁ j₂ - W i₂ j₁ + W i₂ j₂ := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => by rw [hsj (fun b => W a b)]]
    rw [hsi (fun a => W a j₁ - W a j₂)]
    ring
  have hdiag : ∑ a, ϑi a * ϑj a * W a a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hϑ a, zero_mul]
  have hswap := sum_filter_lt_add_swap (fun a b => ϑi a * ϑj b * W a b)
  rw [hXX, hdiag, sub_zero] at hswap
  have hsub := sum_filter_lt_eq_sum_subtype
    (fun s : Fin n × Fin n => c2 * (ϑi s.1 * ϑj s.2 + ϑi s.2 * ϑj s.1) * W s.1 s.2)
  rw [show (∑ x : FinPairs n, c2 * (ϑi x.1.1 * ϑj x.1.2 + ϑi x.1.2 * ϑj x.1.1) * W x.1.1 x.1.2) =
      ∑ x : {p : Fin n × Fin n // p.1 < p.2},
        c2 * (ϑi x.1.1 * ϑj x.1.2 + ϑi x.1.2 * ϑj x.1.1) * W x.1.1 x.1.2 from rfl, ← hsub]
  have hpt2 : ∀ s : Fin n × Fin n, c2 * (ϑi s.1 * ϑj s.2 + ϑi s.2 * ϑj s.1) * W s.1 s.2 =
      c2 * (ϑi s.1 * ϑj s.2 * W s.1 s.2 + ϑi s.2 * ϑj s.1 * W s.2 s.1) := fun s => by
    rw [hWsymm s.2 s.1]
    ring
  simp_rw [hpt2, ← Finset.mul_sum]
  rw [hswap, hcomb]
  ring

end SpinGlasses
