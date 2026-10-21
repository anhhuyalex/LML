/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityHolder
public import LeanMachineLearning.SpinGlasses.SKCavityDecoupledEndpoint
public import LeanMachineLearning.SpinGlasses.SKCavityFreeEnergy

/-!
# Cavity interpolation bound (Talagrand's Proposition 1.6.5)

`|ν(f) - ν₀(f)|` is bounded by `2 n² β² exp(4 (n+2)² β²)` times a Hölder product of `ν(|f|^p)`
and `ν(|R_{1,2} - q|^r)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Pointwise bound of the angle combination of the cavity derivative by the overlap deviations:
the combination with the covariance kernel `β² ε ε' (q - R⁻)` is at most `2 β²` times the
weighted sum of `|R - q|` over the three replica families. -/
theorem abs_sk_cavity_angle_combination_le (N n : ℕ) (β q : ℝ)
    (τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) :
    let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        (q - (N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)))
    let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (y i : ℝ)) - q|
    |2 * (∑ s : Fin n × Fin n with s.1 < s.2, U (τ (some (some s.1))) (τ (some (some s.2)))) -
        2 * (n : ℝ) * ∑ s : Fin n, U (τ (some (some s))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none)| ≤
      2 * β ^ 2 * ((∑ s : Fin n × Fin n with s.1 < s.2,
            dev (τ (some (some s.1))) (τ (some (some s.2)))) +
          (n : ℝ) * ∑ s : Fin n, dev (τ (some (some s))) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none)) := by
  intro U dev
  have hU : ∀ a b, U a b = -(β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (b i : ℝ)) - q)) + β ^ 2 / (N + 1 : ℝ) := fun a b => by
    rw [sk_cavity_kernel_full_eq]
    simp only [U]
    ring
  have h := abs_two_sum_lt_combination_le n U
    (fun a b => β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (b i : ℝ)) - q)) (β ^ 2 / (N + 1 : ℝ)) hU τ
  simp only [abs_sk_cavity_kernel_full, ← Finset.mul_sum] at h
  refine h.trans (le_of_eq ?_)
  simp only [dev]
  ring

/-- **Talagrand's Proposition 1.6.5 (Eq. (1.156))**, with the constant `exp (4 (n + 2)² β²)`
(the terms of Eq. (1.152) are averages over `n + 2` replicas, to which Lemma 1.6.4 applies with
`n + 2` replicas). -/
theorem sk_cavity_nu_sub_nu_zero_le (N n : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) {p r : ℝ} (hpr : p.HolderConjugate r) :
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
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
    2 * (n : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) *
      ((∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ r
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r)) := by
  intro B E Esk
  let P₀ : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  let P : Measure ((Fin N → ℝ) × ℝ) :=
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
  let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
    |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (y i : ℝ)) - q|
  let Wsum : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    (∑ s : Fin n × Fin n with s.1 < s.2, dev (τ (some (some s.1))) (τ (some (some s.2)))) +
      (n : ℝ) * ∑ s : Fin n, dev (τ (some (some s))) (τ (some none)) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none)
  let X : ℝ :=
    (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
    (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ r
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r)
  let Φ : ℝ → ℝ := fun s =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s g' ω)) ∂P ∂P₀
  have hEm (s : ℝ) (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E s x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  have hd : ∀ s, ∃ D : ℝ, HasDerivAt Φ (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc (0 : ℝ) (π / 2) →
        |D| ≤ 4 * (n : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * X) := by
    intro s
    refine ⟨_, hasDerivAt_integral_sk_cavity_path_angle_offDiag N n β q h hq f s, fun hs => ?_⟩
    have hs' := Real.arccos_sqrt_cos_sq hs.1 hs.2
    have hWnn : ∀ τ, 0 ≤ Wsum τ := fun τ => by
      simp only [Wsum, dev]
      positivity
    have hcard : (Fintype.card (Option (Option (Fin n))) : ℝ) = n + 2 := by
      simp only [Fintype.card_option, Fintype.card_fin]
      push_cast
      ring
    have key := sk_cavity_path_square_le_exp_mul_replicas N β q h hq
      (R := Option (Option (Fin n))) (fun τ => |f fun s => τ (some (some s))| * Wsum τ)
      (fun τ => mul_nonneg (abs_nonneg _) (hWnn τ)) (Real.cos s ^ 2)
      ⟨sq_nonneg _, by nlinarith [Real.cos_sq_le_one s]⟩
    simp only [hs', hcard] at key
    have hW := sk_nested_holder_sum N n β h f hpr q
    refine le_trans (abs_integral_nested_gibbs_le P₀ P (E s) (hEm s)
      (H := fun τ => 2 * β ^ 2 * (|f fun s => τ (some (some s))| * Wsum τ)) ?_) ?_
    · intro τ
      rw [abs_mul]
      have h1 := abs_sk_cavity_angle_combination_le N n β q τ
      calc _ ≤ |f fun s => τ (some (some s))| * (2 * β ^ 2 * Wsum τ) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = _ := by ring
    · simp only [integral_const_mul]
      calc _ ≤ 2 * β ^ 2 * (Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) *
            (2 * (n : ℝ) ^ 2 * X)) := by
            refine mul_le_mul_of_nonneg_left ((key.trans ?_)) (by positivity)
            exact mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
        _ = _ := by ring
  have hmain := Real.abs_sub_le_half_of_exists_hasDerivAt hd
  have hzero : Φ 0 = ∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_sk_cavity_path_zero N n β q h f
  rw [abs_sub_comm, ← hzero]
  refine hmain.trans (le_of_eq ?_)
  simp only [X, dev]
  ring

end SpinGlasses
