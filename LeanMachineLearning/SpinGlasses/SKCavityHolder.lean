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
  have hmA : AEStronglyMeasurable (fun g : FinPairs (N + 1) → ℝ =>
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, |f (fun s => τ (some (some s)))| ^ p
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    rw [funext e1]
    exact (measurable_integral_pi_count_tilted (Θ := fun _ σ => |f σ| ^ p) hEg
      fun _ => measurable_const).aestronglyMeasurable
  have hmB : AEStronglyMeasurable (fun g : FinPairs (N + 1) → ℝ =>
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, dev (τ a) (τ b) ^ r
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    rw [funext e2]
    exact (measurable_integral_pi_count_tilted (Θ := fun _ σ => dev (σ 0) (σ 1) ^ r) hEg
      fun _ => measurable_const).aestronglyMeasurable
  have key := integral_integral_mul_le_Lp_mul_Lq
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (fun g => Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g)) hpr
    (A := fun τ => |f (fun s => τ (some (some s)))|) (B := fun τ => dev (τ a) (τ b))
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hmA hmB
  simpa only [e1, e2] using key

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
  have hpairs : ∀ j : ι, (pr j).1 ≠ (pr j).2 := by
    rintro (s | s | s)
    · have := s.property
      simp only [pr, ne_eq, Option.some.injEq]
      exact this.ne
    · simp [pr]
    · simp [pr]
  let G : ι → (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun j τ =>
    |f (fun s => τ (some (some s)))| * dev (τ (pr j).1) (τ (pr j).2)
  have hsum : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      |f (fun s => τ (some (some s)))| *
          ((∑ s : Fin n × Fin n with s.1 < s.2,
              dev (τ (some (some s.1))) (τ (some (some s.2)))) +
            (n : ℝ) * ∑ s : Fin n, dev (τ (some (some s))) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none)) =
        ∑ j : ι, cw j * G j τ := by
    intro τ
    simp only [ι, cw, G, pr, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
      one_mul, ← mul_assoc, ← Finset.mul_sum]
    rw [sum_filter_lt_eq_sum_subtype fun s : Fin n × Fin n =>
      dev (τ (some (some s.1))) (τ (some (some s.2)))]
    ring
  simp_rw [hsum]
  have hcw : ∑ j : ι, cw j = 2 * (n : ℝ) ^ 2 := by
    simp only [ι, cw, Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ, card_finPairs,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_choose_two,
      Finset.univ_unique, Finset.card_singleton, Nat.cast_one]
    ring
  have hc : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ cw j := by
    rintro (s | s | s) _ <;> simp only [cw] <;> positivity
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
    hc (fun j _ => sk_nested_holder_pair N n β h f hpr q (hpairs j))
  rw [hcw] at key
  exact key

end SpinGlasses
