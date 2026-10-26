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
# A pointwise bound for the angle derivative of the cavity path

For an observable `f` of `n` replicas and an angle `s ∈ [0, π/2]`, the derivative of the cavity
path average (Eq. (1.151)/(1.152)) is bounded by `2 β² exp (4 (n+2)² β²)` times the coupled
average of `|f| · W`, where `W` is the weighted sum of the overlap deviations `|R_{ab} - q|` over
the replica pairs that occur.  This is the part of Talagrand's Proposition 1.6.5 before Hölder's
inequality; the Hölder step is applied separately for the first order (Proposition 1.8.1,
Eq. (1.215)) and the second order (Eq. (1.216)).
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

/-- **The replica pairs of Eq. (1.152) as a weighted list.**  For every function `D` of two
configurations, the three replica families `∑_{ℓ<ℓ'≤n}`, `n ∑_{ℓ≤n}` and `n(n+1)/2` (one pair of
extra replicas) are a finite sum `∑_j c_j D(τ a_j, τ b_j)` with `c_j ≥ 0`, `a_j ≠ b_j` and
`∑ c_j = 2 n²`. -/
theorem exists_replica_pair_weights (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (pr : ι → Option (Option (Fin n)) × Option (Option (Fin n)))
      (cw : ι → ℝ), (∀ j, (pr j).1 ≠ (pr j).2) ∧ (∀ j, 0 ≤ cw j) ∧
      ∑ j, cw j = 2 * (n : ℝ) ^ 2 ∧
      ∀ {α : Type} (D : α → α → ℝ) (τ : Option (Option (Fin n)) → α),
        (∑ s : Fin n × Fin n with s.1 < s.2, D (τ (some (some s.1))) (τ (some (some s.2)))) +
          (n : ℝ) * ∑ s : Fin n, D (τ (some (some s))) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 * D (τ (some none)) (τ none) =
        ∑ j, cw j * D (τ (pr j).1) (τ (pr j).2) := by
  let ι := FinPairs n ⊕ (Fin n ⊕ Unit)
  let pr : ι → Option (Option (Fin n)) × Option (Option (Fin n)) := fun j =>
    match j with
    | Sum.inl s => (some (some s.val.1), some (some s.val.2))
    | Sum.inr (Sum.inl s) => (some (some s), some none)
    | Sum.inr (Sum.inr _) => (some none, none)
  let cw : ι → ℝ := fun j =>
    match j with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => (n : ℝ)
    | Sum.inr (Sum.inr _) => (n : ℝ) * ((n : ℝ) + 1) / 2
  refine ⟨ι, inferInstance, pr, cw, ?_, ?_, ?_, ?_⟩
  · rintro (s | s | s)
    · have := s.property
      simp only [pr, ne_eq, Option.some.injEq]
      exact this.ne
    · simp [pr]
    · simp [pr]
  · rintro (s | s | s) <;> simp only [cw] <;> positivity
  · simp only [ι, cw, Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ, card_finPairs,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_choose_two,
      Finset.univ_unique, Finset.card_singleton, Nat.cast_one]
    ring
  · intro α D τ
    simp only [ι, cw, pr, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
      one_mul, ← Finset.mul_sum]
    rw [sum_filter_lt_eq_sum_subtype fun s : Fin n × Fin n =>
      D (τ (some (some s.1))) (τ (some (some s.2)))]
    ring

/-- **Pointwise bound for the angle derivative of the cavity path.**  For `s ∈ [0, π/2]` the angle
derivative integrand of Eq. (1.151) (kernel `U = β² ε ε' (q - R⁻)` with weights `2`, `-2 n`,
`n (n+1)`) is at most `2 β² exp (4 (n+2)² β²)` times the coupled average of `|f| · W`, where `W` is
the weighted sum of the deviations `|R - q|` over the replica pairs (the weights of
`exists_replica_pair_weights`). -/
theorem abs_sk_cavity_angle_derivative_le (N n : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (π / 2)) :
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
    let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        (q - (N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)))
    let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (y i : ℝ)) - q|
    |∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            (2 * (∑ p : Fin n × Fin n with p.1 < p.2,
                U (τ (some (some p.1))) (τ (some (some p.2)))) -
              2 * (n : ℝ) * ∑ r : Fin n, U (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E s g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)| ≤
    2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) *
      ∫ g, ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          |f (fun r => τ (some (some r)))| *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                dev (τ (some (some p.1))) (τ (some (some p.2)))) +
              (n : ℝ) * ∑ r : Fin n, dev (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro B E Esk U dev
  let P₀ : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  let P : Measure ((Fin N → ℝ) × ℝ) :=
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
  let Wsum : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    (∑ s : Fin n × Fin n with s.1 < s.2, dev (τ (some (some s.1))) (τ (some (some s.2)))) +
      (n : ℝ) * ∑ s : Fin n, dev (τ (some (some s))) (τ (some none)) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none)
  have hEm : ∀ a : Fin (N + 1) → ℤˣ,
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E s x.1 x.2 a) := fun a => by
    dsimp [E, B]
    fun_prop
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
  refine le_trans (abs_integral_nested_gibbs_le P₀ P (E s) hEm
    (H := fun τ => 2 * β ^ 2 * (|f fun s => τ (some (some s))| * Wsum τ)) ?_) ?_
  · intro τ
    rw [abs_mul]
    have h1 := abs_sk_cavity_angle_combination_le N n β q τ
    calc _ ≤ |f fun s => τ (some (some s))| * (2 * β ^ 2 * Wsum τ) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := by ring
  · simp only [integral_const_mul]
    calc _ ≤ 2 * β ^ 2 * (Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * _) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring

end SpinGlasses
