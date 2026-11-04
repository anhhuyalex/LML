/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTFreshContractions

/-!
# Decoupled contractions of a leading single factor (Proposition 1.10.5, Eq. (1.316))

For a leading factor of single type `(ε_x₁ - ε_x₂) ε_y` the decoupled average against a spin
pair `ε_a ε_b` with `y ∉ {a, b}` is `(q - q̂)` times the signed membership of `{a, b}` in
`{x₁, x₂}`. This is the single-type analogue of `sk_cavity_decoupled_rect_monomial`, where the
coefficient is `1 - 2q + q̂`. It is built from the same quartic-monomial lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Decoupled average of a single-type sign polynomial times two last spins.** For
`x₁, x₂ ≠ y`, `a ≠ b` and `y ∉ {a, b}`, `ν₀(f⁻ (ε_{x₁} - ε_{x₂}) ε_y ε_a ε_b)` is `q - q̂`
times the signed membership of `{a, b}` in `{x₁, x₂}` times the decoupled average of `f⁻`. -/
theorem sk_cavity_decoupled_single_monomial (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q)
    {R : Type*} [Fintype R] [DecidableEq R] {x₁ x₂ y a b : R} (hab : a ≠ b)
    (hx₁y : x₁ ≠ y) (hx₂y : x₂ ≠ y) (hya : y ≠ a) (hyb : y ≠ b)
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
              ((σ y (Fin.last N) : ℤˣ) : ℝ) *
              (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    ((q - (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1))) *
      ((((if x₁ = a then 1 else 0) + (if x₁ = b then 1 else 0) : ℕ) : ℝ) -
        (((if x₂ = a then 1 else 0) + (if x₂ = b then 1 else 0) : ℕ) : ℝ))) *
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
  let sg : Bool → ℝ := fun u => if u then 1 else -1
  let Gj : Bool → (R → Fin (N + 1) → ℤˣ) → ℝ := fun u σ =>
    G (fun r i => σ r i.castSucc) *
      (((σ (X u) (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) *
        ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
  have hpt : ∀ σ : R → Fin (N + 1) → ℤˣ,
      G (fun r i => σ r i.castSucc) *
            ((((σ x₁ (Fin.last N) : ℤˣ) : ℝ) - ((σ x₂ (Fin.last N) : ℤˣ) : ℝ)) *
              ((σ y (Fin.last N) : ℤˣ) : ℝ) *
              (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) =
        ∑ u, sg u * Gj u σ := fun σ => by
    simp only [Fintype.sum_bool, sg, Gj, X, ite_true, ite_false, Bool.false_eq_true]
    ring
  simp_rw [hpt]
  have hlin := integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    (Finset.univ : Finset Bool) sg Gj
  refine hlin.trans ?_
  have hend : ∀ u : Bool, ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ, Gj u σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^
        (4 - 2 * ((if X u = a then 1 else 0) + (if X u = b then 1 else 0) +
          (if y = a then 1 else 0) + (if y = b then 1 else 0))) ∂(gaussianReal 0 1)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    fun u => sk_cavity_decoupled_endpoint_quartic N β q h (x := X u) (y := y) (a := a) (b := b)
      (by cases u <;> simp [X, hx₁y, hx₂y]) hab G
  set O : ℝ := ∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    with hO
  have hya' : (if y = a then 1 else 0 : ℕ) = 0 := ite_eq_right_iff.mpr (fun h => absurd h hya)
  have hyb' : (if y = b then 1 else 0 : ℕ) = 0 := ite_eq_right_iff.mpr (fun h => absurd h hyb)
  have hδ : ∀ x : R, ((if x = a then 1 else 0) + (if x = b then 1 else 0) : ℕ) = 0 ∨
      ((if x = a then 1 else 0) + (if x = b then 1 else 0) : ℕ) = 1 := fun x => by
    by_cases h1 : x = a
    · subst h1
      simp [hab]
    · by_cases h2 : x = b <;> simp [h1, h2, Ne.symm hab]
  simp only [Fintype.sum_bool, hend, sg, X, ite_true, ite_false, Bool.false_eq_true, hya', hyb',
    add_zero]
  rcases hδ x₁ with h1 | h1 <;> rcases hδ x₂ with h2 | h2 <;>
    simp only [h1, h2, Nat.reduceMul, Nat.reduceSub, Nat.cast_zero, Nat.cast_one, hfix] <;> ring

/-- The single-type leading factor contracted against any finite linear combination of spin
pairs that avoid its last replica `y`. The coefficient is the signed sum of the monomial
coefficients of `sk_cavity_decoupled_single_monomial`. -/
theorem sk_cavity_decoupled_single_lincomb (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q)
    {R : Type*} [Fintype R] [DecidableEq R] {x₁ x₂ y : R}
    {I : Type*} [Fintype I] (c : I → ℝ) (a b : I → R) (hab : ∀ i, a i ≠ b i)
    (hx₁y : x₁ ≠ y) (hx₂y : x₂ ≠ y) (hya : ∀ i, y ≠ a i) (hyb : ∀ i, y ≠ b i)
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
              ((σ y (Fin.last N) : ℤˣ) : ℝ) *
              (∑ i : I, c i * (((σ (a i) (Fin.last N) : ℤˣ) : ℝ) *
                ((σ (b i) (Fin.last N) : ℤˣ) : ℝ))))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (q - (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1))) *
      (∑ i : I, c i * ((((if x₁ = a i then 1 else 0) + (if x₁ = b i then 1 else 0) : ℕ) : ℝ) -
        (((if x₂ = a i then 1 else 0) + (if x₂ = b i then 1 else 0) : ℕ) : ℝ))) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  have hEm (s : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) =>
        E (π / 2) x.1 x.2 s) := by
    dsimp [E, B]
    fun_prop
  let H : I → (R → Fin (N + 1) → ℤˣ) → ℝ := fun i σ =>
    G (fun r v => σ r v.castSucc) *
      (((σ x₁ (Fin.last N) : ℝ) - (σ x₂ (Fin.last N) : ℝ)) * (σ y (Fin.last N) : ℝ) *
        ((σ (a i) (Fin.last N) : ℝ) * (σ (b i) (Fin.last N) : ℝ)))
  have hpoint (σ : R → Fin (N + 1) → ℤˣ) :
      G (fun r v => σ r v.castSucc) *
        (((σ x₁ (Fin.last N) : ℝ) - (σ x₂ (Fin.last N) : ℝ)) * (σ y (Fin.last N) : ℝ) *
          (∑ i : I, c i * ((σ (a i) (Fin.last N) : ℝ) * (σ (b i) (Fin.last N) : ℝ)))) =
        ∑ i : I, c i * H i σ := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by dsimp [H]; ring
  simp_rw [hpoint]
  rw [integral_nested_gibbs_finset_sum
    (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    (E (π / 2)) hEm]
  generalize hO : (∫ g', ∫ ρ : R → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = O
  generalize hA : (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4
    ∂gaussianReal 0 1) = A
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := sk_cavity_decoupled_single_monomial N β q h hfix
    (hab i) hx₁y hx₂y (hya i) (hyb i) G
  change c i * (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ, H i σ
    ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
    ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = _
  dsimp only [H]
  rw [hi, hO, hA]
  ring

/-- The signed incidence of a flagged partner factor with the replicas of a leading single
factor. Only a single partner can be matched: its unflagged slot cancels the other terms. -/
private theorem fresh_single_incidence {R J : Type*} [DecidableEq R] [DecidableEq J]
    (x a b : R) (p u : J) (hpu : p ≠ u) (L S : Bool) :
    let A : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
      if L && i.1 then .inl a else .inr (.inl u)
    let B : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
      if S && i.2 then .inl b else .inr (.inr u)
    let c : Bool × Bool → ℝ := fun i =>
      (if L then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
      (if S then if i.2 then 1 else -1 else if i.2 then 1 else 0)
    (∑ i : Bool × Bool, c i *
      (((((if (Sum.inl x : R ⊕ (J ⊕ J)) = A i then 1 else 0) +
          (if (Sum.inl x : R ⊕ (J ⊕ J)) = B i then 1 else 0) : ℕ) : ℝ) -
        (((if (Sum.inr (.inl p) : R ⊕ (J ⊕ J)) = A i then 1 else 0) +
          (if (Sum.inr (.inl p) : R ⊕ (J ⊕ J)) = B i then 1 else 0) : ℕ) : ℝ)))) =
      (if L && !S then (if x = a then 1 else 0) else 0) +
        (if S && !L then (if x = b then 1 else 0) else 0) := by
  intro A B c
  cases L <;> cases S <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [Fintype.sum_prod_type, A, B, c]

/-- **Decoupled coefficient of a leading single factor against a fresh factor.** The leading
factor is `(ε_x - ε_{p}) ε_{p'}` on fresh replicas of `p`; the partner is any flagged factor of a
fresh index `u ≠ p`. Only a single partner whose unflagged slot is fresh and whose flagged slot
carries the label `x` survives, with coefficient `q - q̂`. -/
theorem sk_cavity_decoupled_fresh_single (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂gaussianReal 0 1 = q)
    {R J : Type*} [Fintype R] [Fintype J] [DecidableEq R] [DecidableEq J]
    (x a b : R) (p u : J) (hpu : p ≠ u) (L S : Bool)
    (hab : L = true → S = true → a ≠ b)
    (G : ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ) :
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
    let e0 : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      ((ε (.inl x) : ℝ) - (ε (.inr (.inl p)) : ℝ)) * (ε (.inr (.inr p)) : ℝ)
    let eu : (R ⊕ (J ⊕ J) → ℤˣ) → ℝ := fun ε =>
      (if L then (ε (.inl a) : ℝ) - (ε (.inr (.inl u)) : ℝ)
        else (ε (.inr (.inl u)) : ℝ)) *
      (if S then (ε (.inl b) : ℝ) - (ε (.inr (.inr u)) : ℝ)
        else (ε (.inr (.inr u)) : ℝ))
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R ⊕ (J ⊕ J) → Fin (N + 1) → ℤˣ,
      G (fun r i => σ r i.castSucc) *
        (e0 (fun r => σ r (Fin.last N)) * eu (fun r => σ r (Fin.last N)))
      ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (q - (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1)) *
      ((if L && !S then (if x = a then 1 else 0) else 0) +
        (if S && !L then (if x = b then 1 else 0) else 0)) *
      ∫ g', ∫ ρ : (R ⊕ (J ⊕ J)) → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E e0 eu
  let A : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
    if L && i.1 then .inl a else .inr (.inl u)
  let bb : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
    if S && i.2 then .inl b else .inr (.inr u)
  let c : Bool × Bool → ℝ := fun i =>
    (if L then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  have hpoint (ε : R ⊕ (J ⊕ J) → ℤˣ) :
      eu ε = ∑ i : Bool × Bool, c i * ((ε (A i) : ℝ) * (ε (bb i) : ℝ)) := by
    cases L <;> cases S <;> simp [Fintype.sum_prod_type, A, bb, c, eu] <;> ring
  have hk := sk_cavity_decoupled_single_lincomb N β q h hfix c A bb
    (fun i => flagged_pair_ne a b u L S hab i)
    (x₁ := Sum.inl x) (x₂ := Sum.inr (Sum.inl p)) (y := Sum.inr (Sum.inr p))
    (by simp) (by simp)
    (fun i => by simp only [A]; split_ifs <;> simp)
    (fun i => by simp only [bb]; split_ifs <;> simp [hpu]) G
  have hc := fresh_single_incidence x a b p u hpu L S
  simp only [hpoint, e0]
  rw [hk, hc]

end SpinGlasses
