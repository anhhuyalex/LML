/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityDerivativeBound
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
    have hW := sk_nested_holder_sum N n β h f hpr q
    refine (abs_sk_cavity_angle_derivative_le N n β q h hq f hs).trans ?_
    calc _ ≤ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * (2 * (n : ℝ) ^ 2 * X) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
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

/-- **Talagrand's Proposition 1.8.1, Eq. (1.215), with `τ₁ = ∞`, `τ₂ = 1`.**  For a bounded
observable, `|ν(f) - ν₀(f)| ≤ 2 n² β² exp (4 (n+2)² β²) · sup |f| · ν(|R_{1,2} - q|)`. -/
theorem sk_cavity_nu_sub_nu_zero_le_of_abs_le (N n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) {M : ℝ}
    (hM : ∀ σ, |f σ| ≤ M) :
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
    2 * (n : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * M *
      ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro B E Esk
  let P₀ : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  let P : Measure ((Fin N → ℝ) × ℝ) :=
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
  let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
    |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (y i : ℝ)) - q|
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM fun _ _ => 1)
  have hEg (c : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ => Esk g c) := by
    dsimp [Esk]
    fun_prop
  let A : ℝ := ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1)
    ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
    ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hA0 : 0 ≤ A := integral_nonneg fun g => integral_nonneg fun σ => abs_nonneg _
  let Φ : ℝ → ℝ := fun s =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s g' ω)) ∂P ∂P₀
  have hbound : ∫ g, ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      |f (fun r => τ (some (some r)))| *
        ((∑ p : Fin n × Fin n with p.1 < p.2,
            dev (τ (some (some p.1))) (τ (some (some p.2)))) +
          (n : ℝ) * ∑ r : Fin n, dev (τ (some (some r))) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ 2 * (n : ℝ) ^ 2 * (M * A) := by
    obtain ⟨ι, _, pr, cw, hpairs, hc, hcw, hW⟩ := exists_replica_pair_weights n
    let G : ι → (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun j τ =>
      |f (fun s => τ (some (some s)))| * dev (τ (pr j).1) (τ (pr j).2)
    have hsum : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        |f (fun r => τ (some (some r)))| *
          ((∑ p : Fin n × Fin n with p.1 < p.2,
              dev (τ (some (some p.1))) (τ (some (some p.2)))) +
            (n : ℝ) * ∑ r : Fin n, dev (τ (some (some r))) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 * dev (τ (some none)) (τ none)) =
          ∑ j, cw j * G j τ := fun τ => by
      rw [hW dev τ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [G]; ring
    simp_rw [hsum]
    have key := integral_integral_finset_sum_le
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      (fun g => Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (Esk g))
      Finset.univ cw G (M * A) (fun _ _ => Integrable.of_finite)
      (fun j => integrable_integral_pi_count_tilted_det
        (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => Esk g a)
        (fun a => (hEg a).aemeasurable) (G j))
      (fun j _ => hc j) (fun j _ => by
        have e1 : ∀ g : FinPairs (N + 1) → ℝ,
            ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, G j τ
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (Esk g)) ≤
            M * ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1)
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g)) := fun g => by
          rw [← integral_pi_count_tilted_pair (hpairs j) (Esk g) dev, ← integral_const_mul]
          exact integral_mono Integrable.of_finite Integrable.of_finite fun τ =>
            mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
        calc _ ≤ ∫ g, M * ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1)
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
              ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
              integral_mono (integrable_integral_pi_count_tilted_det
                (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => Esk g a)
                (fun a => (hEg a).aemeasurable) (G j))
                ((integrable_integral_pi_count_tilted_det
                  (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => Esk g a)
                  (fun a => (hEg a).aemeasurable) fun σ : Fin 2 → Fin (N + 1) → ℤˣ =>
                    dev (σ 0) (σ 1)).const_mul M) e1
          _ = M * A := integral_const_mul _ _)
    rw [hcw] at key
    exact key
  have hd : ∀ s, ∃ D : ℝ, HasDerivAt Φ (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc (0 : ℝ) (π / 2) →
        |D| ≤ 4 * (n : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * (M * A)) := by
    intro s
    refine ⟨_, hasDerivAt_integral_sk_cavity_path_angle_offDiag N n β q h hq f s, fun hs => ?_⟩
    refine (abs_sk_cavity_angle_derivative_le N n β q h hq f hs).trans ?_
    calc _ ≤ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * (2 * (n : ℝ) ^ 2 * (M * A)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by ring
  have hmain := Real.abs_sub_le_half_of_exists_hasDerivAt hd
  have hzero : Φ 0 = ∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_sk_cavity_path_zero N n β q h f
  rw [abs_sub_comm, ← hzero]
  refine hmain.trans (le_of_eq ?_)
  simp only [A, dev]
  ring

end SpinGlasses
