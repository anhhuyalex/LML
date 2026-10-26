/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityDomination
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedHolder

/-!
# Hölder bound for the SK average of an overlap deviation times an observable

At the coupled endpoint, the average of `|f(σ¹,…,σⁿ)| · |R_{ab} - q|` over `n + 2` replicas is
bounded by `ν(|f|^p)^{1/p} ν(|R_{1,2} - q|^r)^{1/r}` for conjugate exponents `p, r`. The proof is
Hölder's inequality for the iterated average, and marginalization of the replicas that do not
occur: the replicas of `f` (`integral_pi_option_count_tilted_marginal`) and the two replicas of
the overlap (`integral_pi_count_tilted_pair`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Hölder for an arbitrary pair of observables of any set of replicas**, under any random
energy `E g` that is measurable in the disorder `g`. -/
theorem sk_replica_holder (N : ℕ) {R : Type*} [Fintype R]
    (E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ)
    (hEg : ∀ c, Measurable (fun g : FinPairs (N + 1) → ℝ => E g c)) {p r : ℝ}
    (hpr : p.HolderConjugate r) (A B : (R → Fin (N + 1) → ℤˣ) → ℝ) (hA : ∀ τ, 0 ≤ A τ)
    (hB : ∀ τ, 0 ≤ B τ) :
    ∫ g, ∫ τ : R → Fin (N + 1) → ℤˣ, A τ * B τ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    (∫ g, ∫ τ : R → Fin (N + 1) → ℤˣ, A τ ^ p
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
    (∫ g, ∫ τ : R → Fin (N + 1) → ℤˣ, B τ ^ r
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r) :=
  integral_integral_mul_le_Lp_mul_Lq
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (fun g => Measure.pi fun _ : R => Measure.count.tilted (E g)) hpr hA hB
    (measurable_integral_pi_count_tilted (Θ := fun _ τ => A τ ^ p) hEg
      fun _ => measurable_const).aestronglyMeasurable
    (measurable_integral_pi_count_tilted (Θ := fun _ τ => B τ ^ r) hEg
      fun _ => measurable_const).aestronglyMeasurable

/-- **Hölder for one pair of replicas.** -/
theorem sk_nested_holder_pair (N n : ℕ) (β h : ℝ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    {p r : ℝ} (hpr : p.HolderConjugate r) (q : ℝ)
    {a b : Option (Option (Fin n))} (hab : a ≠ b) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∫ g, ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        |f (fun s => τ (some (some s)))| *
          |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ a i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (τ b i : ℝ)) - q|
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
    (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ r
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r) := by
  intro E
  have hEg (c : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ => E g c) := by
    dsimp [E]
    fun_prop
  clear_value E
  set dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
    |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (y i : ℝ)) - q|
    with hdev
  have e1 (g : FinPairs (N + 1) → ℝ) :
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, |f (fun s => τ (some (some s)))| ^ p
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g)) =
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g)) :=
    integral_pi_option_option_count_tilted_marginal (E g) fun σ => |f σ| ^ p
  have e2 (g : FinPairs (N + 1) → ℝ) :
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, dev (τ a) (τ b) ^ r
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g)) =
      ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ r
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) :=
    integral_pi_count_tilted_pair hab (E g) fun x y => dev x y ^ r
  have key := sk_replica_holder N E hEg (R := Option (Option (Fin n))) hpr
    (fun τ => |f (fun s => τ (some (some s)))|) (fun τ => dev (τ a) (τ b))
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  simpa only [e1, e2] using key

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

/-- **Hölder for an observable against a product of two overlap deviations.**  For an observable
`f` of the replicas `ρ r` (`ρ` injective) and two pairs of distinct replicas `(a, b)`, `(c, d)`,
the average of `|f| |R_{ab} - q| |R_{cd} - q|` is at most
`ν(|f|^p)^{1/p} ν(|R_{1,2} - q|^{2r})^{1/r}`: the exponent doubles because two deviations occur
(the second order of Proposition 1.8.1). -/
theorem sk_replica_holder_dev_dev (N n : ℕ) (β h q : ℝ) {R : Type*} [Fintype R] {ρ : Fin n → R}
    (hρ : Function.Injective ρ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) {p r : ℝ}
    (hpr : p.HolderConjugate r) {a b c d : R} (hab : a ≠ b) (hcd : c ≠ d) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (y i : ℝ)) - q|
    ∫ g, ∫ τ : R → Fin (N + 1) → ℤˣ,
        |f (fun s => τ (ρ s))| * (dev (τ a) (τ b) * dev (τ c) (τ d))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
    (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r) := by
  intro E dev
  have hEg (c : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ => E g c) := by
    dsimp [E]
    fun_prop
  clear_value E
  have hr : 0 < r := hpr.symm.pos
  have key := sk_replica_holder N E hEg (R := R) hpr (fun τ => |f (fun s => τ (ρ s))|)
    (fun τ => dev (τ a) (τ b) * dev (τ c) (τ d)) (fun _ => abs_nonneg _)
    (fun τ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  refine key.trans ?_
  have e1 (g : FinPairs (N + 1) → ℝ) :
      ∫ τ : R → Fin (N + 1) → ℤˣ, |f (fun s => τ (ρ s))| ^ p
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) =
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g)) :=
    integral_pi_count_tilted_comp_injective hρ (E g) fun σ => |f σ| ^ p
  have e2 (g : FinPairs (N + 1) → ℝ) (x y : R) (hxy : x ≠ y) :
      ∫ τ : R → Fin (N + 1) → ℤˣ, dev (τ x) (τ y) ^ (2 * r)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) =
      ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) :=
    integral_pi_count_tilted_pair hxy (E g) fun u v => dev u v ^ (2 * r)
  have hdet (x y : R) : Integrable (fun g : FinPairs (N + 1) → ℝ =>
      ∫ τ : R → Fin (N + 1) → ℤˣ, dev (τ x) (τ y) ^ (2 * r)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integrable_integral_pi_count_tilted_det
      (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => E g a)
      (fun a => (hEg a).aemeasurable) fun τ => dev (τ x) (τ y) ^ (2 * r)
  have hpt (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      (u * v) ^ r ≤ (u ^ (2 * r) + v ^ (2 * r)) / 2 := by
    have h2 : ∀ w : ℝ, 0 ≤ w → w ^ (2 * r) = (w ^ r) ^ 2 := fun w hw => by
      rw [mul_comm, Real.rpow_mul hw, Real.rpow_two]
    rw [Real.mul_rpow hu hv, h2 u hu, h2 v hv]
    nlinarith [sq_nonneg (u ^ r - v ^ r)]
  have hmain : ∫ g, ∫ τ : R → Fin (N + 1) → ℤˣ, (dev (τ a) (τ b) * dev (τ c) (τ d)) ^ r
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
      ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    have hin : ∀ g : FinPairs (N + 1) → ℝ,
        ∫ τ : R → Fin (N + 1) → ℤˣ, (dev (τ a) (τ b) * dev (τ c) (τ d)) ^ r
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) ≤
        ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) := fun g => by
      calc _ ≤ ∫ τ : R → Fin (N + 1) → ℤˣ,
            (dev (τ a) (τ b) ^ (2 * r) + dev (τ c) (τ d) ^ (2 * r)) / 2
            ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) :=
            integral_mono Integrable.of_finite Integrable.of_finite fun τ =>
              hpt _ _ (abs_nonneg _) (abs_nonneg _)
        _ = (∫ τ : R → Fin (N + 1) → ℤˣ, dev (τ a) (τ b) ^ (2 * r)
              ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) +
            ∫ τ : R → Fin (N + 1) → ℤˣ, dev (τ c) (τ d) ^ (2 * r)
              ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) / 2 := by
            rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite]
        _ = _ := by rw [e2 g a b hab, e2 g c d hcd]; ring
    calc _ ≤ ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
          integral_mono
            (integrable_integral_pi_count_tilted_det
              (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => E g a)
              (fun a => (hEg a).aemeasurable) fun τ => (dev (τ a) (τ b) * dev (τ c) (τ d)) ^ r)
            (by simp_rw [← e2 _ a b hab]; exact hdet a b) hin
      _ = _ := rfl
  have hnn : 0 ≤ ∫ g, ∫ τ : R → Fin (N + 1) → ℤˣ, (dev (τ a) (τ b) * dev (τ c) (τ d)) ^ r
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_nonneg fun g => integral_nonneg fun τ =>
      Real.rpow_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) _
  simp_rw [e1]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnn hmain (by positivity)) (by positivity)

/-- **Hölder for the three replica families.** The sum of the `2 n²` terms `|f| · |R_{ab} - q|` of
Eq. (1.152), with weights `1`, `n` and `n (n + 1) / 2`, is bounded by `2 n²` times the Hölder
bound of a single pair. -/
theorem sk_nested_holder_sum (N n : ℕ) (β h : ℝ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    {p r : ℝ} (hpr : p.HolderConjugate r) (q : ℝ) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (y i : ℝ)) - q|
    ∫ g, ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        |f (fun s => τ (some (some s)))| *
          ((∑ s : Fin n × Fin n with s.1 < s.2,
              dev (τ (some (some s.1))) (τ (some (some s.2)))) +
            (n : ℝ) * ∑ s : Fin n, dev (τ (some (some s))) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    2 * (n : ℝ) ^ 2 *
      ((∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ r
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r)) := by
  intro E dev
  have hEg (c : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ => E g c) := by
    dsimp [E]
    fun_prop
  obtain ⟨ι, _, pr, cw, hpairs, hc, hcw, hsum'⟩ := exists_replica_pair_weights n
  let G : ι → (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun j τ =>
    |f (fun s => τ (some (some s)))| * dev (τ (pr j).1) (τ (pr j).2)
  have hsum : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      |f (fun s => τ (some (some s)))| *
          ((∑ s : Fin n × Fin n with s.1 < s.2,
              dev (τ (some (some s.1))) (τ (some (some s.2)))) +
            (n : ℝ) * ∑ s : Fin n, dev (τ (some (some s))) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none)) =
        ∑ j : ι, cw j * G j τ := fun τ => by
    rw [hsum' dev τ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [G]; ring
  simp_rw [hsum]
  have key := integral_integral_finset_sum_le
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (fun g => Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
    Finset.univ cw G
    ((∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ r
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r))
    (fun _ _ => Integrable.of_finite)
    (fun j => integrable_integral_pi_count_tilted_det
      (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => E g a)
      (fun a => (hEg a).aemeasurable) (G j))
    (fun j _ => hc j) (fun j _ => sk_nested_holder_pair N n β h f hpr q (hpairs j))
  rw [hcw] at key
  exact key

end SpinGlasses
