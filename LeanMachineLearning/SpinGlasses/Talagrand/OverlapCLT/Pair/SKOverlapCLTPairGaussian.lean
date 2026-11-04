/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTPairMoments
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianClassRecurrence

/-!
# Proposition 1.10.4: peeling the pair factors `T_{ℓℓ'}`

The pair recurrence (1.313), divided by `1 - β²(1 - 2q + q̂) ≥ 3/4`, has the coefficient
`A² = (1 - 2q + q̂) / (1 - β²(1 - 2q + q̂))`, which is bounded by `4/3`. The generic Gaussian
reference `exists_gaussian_class_moment_error` therefore gives Proposition 1.10.4: every mixed
`T`-moment equals the product, over classes of equal ordered replica pairs, of the Gaussian
moments of variance `A² / (N+1)` of the class sizes, times the moment of the factors that are
not pair factors, up to `O(k+1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **Proposition 1.10.4 (Eq. (1.303)), enumerated form.** Each factor `j` of the finite family
is a `T`-basis variable with flags `L j`, `S j` (pair if both are set, single if exactly one,
global if none) built from replicas `a j`, `b j`; pair factors have ordered labels. Then, with
`A² = (1 - 2q + q̂) / (1 - β²(1 - 2q + q̂))`, the mixed moment `νT s` of a factor set `s`
differs from the product over ordered pairs `k` of the Gaussian moments
`𝔼 (A (N+1)^(-1/2) g)^(#pair factors of s labelled k)` times the moment of the non-pair factors
of `s` by at most `C / (N+1)^((card s + 1)/2)`. The constant precedes `β, h, q, N` for
`β² ≤ β₀²`, `4 β₀² < 1`. The Gaussian moments vanish for odd class sizes and satisfy
`a(k) = (k - 1) a(k - 2)`; this is the content of the book's `a(k) A^k`. -/
theorem sk_T_pair_gaussian_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [LinearOrder R] [DecidableEq J]
    (L S : J → Bool) (a b : J → R) (hord : ∀ j, L j = true → S j = true → a j < b j)
    (s : Finset J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q)
    let νT : Finset J → ℝ := fun s => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |νT s - (∏ k : R × R, ∫ x : ℝ,
        (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * x) ^
          (s.filter fun j => (L j = true ∧ S j = true) ∧ (a j, b j) = k).card
          ∂gaussianReal 0 1) *
      νT (s.filter fun j => ¬(L j = true ∧ S j = true))| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  let P : J → Prop := fun j => L j = true ∧ S j = true
  have hcls : ∀ (s : Finset J) (p : J), (s.filter fun j => P j ∧ (a j, b j) = (a p, b p)) =
      s.filter fun u => L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p := fun s p =>
    Finset.filter_congr fun j _ => by simp [P, and_assoc]
  let valid : ℝ × ℝ × ℝ → Prop := fun θ =>
    (∫ t : ℝ, Real.tanh (θ.1 * Real.sqrt θ.2.2 * t + θ.2.1) ^ 2 ∂gaussianReal 0 1 = θ.2.2) ∧
      θ.1 ^ 2 ≤ β₀ ^ 2
  let αf : ℝ × ℝ × ℝ → ℝ := fun θ =>
    (∫ t : ℝ, Real.tanh (θ.1 * t * Real.sqrt θ.2.2 + θ.2.1) ^ 4 ∂gaussianReal 0 1) -
      2 * θ.2.2 + 1
  have hα : ∀ θ, valid θ → αf θ ∈ Set.Icc (0 : ℝ) 1 := fun θ hθ =>
    tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hθ.1
  have hD : ∀ θ, valid θ → 3 / 4 ≤ 1 - θ.1 ^ 2 * αf θ := fun θ hθ => by
    have h1 := hα θ hθ
    have h2 : θ.1 ^ 2 * αf θ ≤ θ.1 ^ 2 * 1 := mul_le_mul_of_nonneg_left h1.2 (sq_nonneg _)
    linarith only [h2, hθ.2, hβ₀]
  let F : ℝ × ℝ × ℝ → ℕ → Finset J → ℝ := fun θ N s =>
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * θ.1 *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      θ.2.1 * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else θ.2.2)
    ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hmain := exists_gaussian_class_moment_error (J := J) (ι := R × R) P
    (fun j => (a j, b j)) valid F (fun θ => αf θ / (1 - θ.1 ^ 2 * αf θ)) (4 / 3)
    (fun θ hθ => div_nonneg (hα θ hθ).1 (by linarith only [hD θ hθ]))
    (fun θ hθ => by
      have hpos : 0 < 1 - θ.1 ^ 2 * αf θ := by linarith only [hD θ hθ]
      rw [abs_div, abs_of_pos hpos, abs_of_nonneg (hα θ hθ).1, div_le_iff₀ hpos]
      nlinarith only [(hα θ hθ).2, hD θ hθ])
    (fun s p u hps hP hus href => by
      rw [hcls] at href ⊢
      obtain ⟨C₀, hC₀, hC⟩ := sk_T_pair_recurrence_finset_uniform β₀ hβ₀ s L S p hps hP.1 hP.2
        a b (fun j _ => hord j) u hus href
      refine ⟨4 / 3 * C₀, by positivity, ?_⟩
      rintro ⟨β, h, q⟩ hθ N
      have hDpos : 0 < 1 - β ^ 2 * αf (β, h, q) := by linarith only [hD (β, h, q) hθ]
      have hX : 0 < ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by positivity
      have h1 : |(1 - β ^ 2 * αf (β, h, q)) * F (β, h, q) N s -
          (αf (β, h, q) / (N + 1 : ℝ)) * (((s.filter fun u =>
            L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).card - 1 : ℕ) : ℝ) *
            F (β, h, q) N ((s.erase p).erase u)| ≤
          C₀ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := hC β h q hθ.1 hθ.2 N
      have e : F (β, h, q) N s - ((((s.filter fun u =>
            L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).card - 1 : ℕ) : ℝ) *
            (αf (β, h, q) / (1 - β ^ 2 * αf (β, h, q))) / (N + 1 : ℝ)) *
            F (β, h, q) N ((s.erase p).erase u) =
          ((1 - β ^ 2 * αf (β, h, q)) * F (β, h, q) N s -
            (αf (β, h, q) / (N + 1 : ℝ)) * (((s.filter fun u =>
            L u = true ∧ S u = true ∧ a u = a p ∧ b u = b p).card - 1 : ℕ) : ℝ) *
            F (β, h, q) N ((s.erase p).erase u)) / (1 - β ^ 2 * αf (β, h, q)) := by
        have hN : (N : ℝ) + 1 ≠ 0 := by positivity
        have key : ∀ A B w α D X : ℝ, D ≠ 0 → X ≠ 0 →
            A - (w * (α / D) / X) * B = (D * A - (α / X) * w * B) / D := by
          intro A B w α D X hD hX
          field_simp
        exact key _ _ _ _ _ _ hDpos.ne' hN
      change |F (β, h, q) N s - _| ≤ _
      rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
      have hy : 0 ≤ C₀ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by positivity
      have e4 : 4 / 3 * C₀ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) =
          4 / 3 * (C₀ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2)) := by ring
      rw [e4]
      nlinarith only [h1, hy, hD (β, h, q) hθ])
  obtain ⟨K, hK, hK'⟩ := hmain s
  exact ⟨K, hK, fun β h q hfix hb N => hK' (β, h, q) ⟨hfix, hb⟩ N⟩

/-- **A T-moment with an odd pair class is of lower order.** If some ordered pair label occurs an
odd number of times among the pair factors of `s`, then `νT s = O(k+1)`: the Gaussian reference of
Proposition 1.10.4 vanishes, because odd Gaussian moments are zero. -/
theorem sk_T_pair_odd_class_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [LinearOrder R] [DecidableEq J]
    (L S : J → Bool) (a b : J → R) (hord : ∀ j, L j = true → S j = true → a j < b j)
    (s : Finset J) (k : R × R)
    (hodd : Odd (s.filter fun j => (L j = true ∧ S j = true) ∧ (a j, b j) = k).card) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q)
    let νT : Finset J → ℝ := fun s => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |νT s| ≤ C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_T_pair_gaussian_moment_uniform β₀ hβ₀ L S a b hord s
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean T νT
  have h1 := hC β h q hfix hb N
  have hz : (∏ k' : R × R, ∫ x : ℝ,
      (Real.sqrt ((∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1 - 2 * q + 1) /
        (1 - β ^ 2 * (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1 -
          2 * q + 1)) / (N + 1 : ℝ)) * x) ^
        (s.filter fun j => (L j = true ∧ S j = true) ∧ (a j, b j) = k').card
        ∂gaussianReal 0 1) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k)
      (integral_pow_scaled_gaussianReal_of_odd _ hodd)
  simp only [hz, zero_mul, sub_zero] at h1
  exact h1


end SpinGlasses
