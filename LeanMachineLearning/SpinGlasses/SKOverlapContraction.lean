/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityContraction
public import LeanMachineLearning.SpinGlasses.SKCorrelationDecay
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-!
# Contraction of the overlap variance (Talagrand's Proposition 1.6.6)

Site symmetry gives `ν((R - q)²) = ν((ε₁ε₂ - q)(R - q))`, the decoupled endpoint evaluates the
right-hand side at `t = 0` to `(1 - q²)/(N+1)` (Lemma 1.6.2 and the fixed-point equation), and
Proposition 1.6.5 bounds the difference by a small multiple of `ν((R - q)²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Site symmetry of an `R`-replica SK average.** Relabelling the sites of all replicas by a
permutation does not change the disorder average of an observable of the replicas. -/
theorem sk_replica_site_perm (N : ℕ) (β h : ℝ) {R : Type*} [Fintype R]
    (pm : Equiv.Perm (Fin (N + 1))) (Θ : (R → Fin (N + 1) → ℤˣ) → ℝ) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∫ g, ∫ σ : R → Fin (N + 1) → ℤˣ, Θ (fun r i => σ r (pm i))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
    ∫ g, ∫ σ : R → Fin (N + 1) → ℤˣ, Θ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  classical
  intro Esk
  obtain ⟨hw0, hw1, hwm, hsym⟩ := sk_gibbsWeight_siteSymmetric β h Esk (fun g a => by simp [Esk])
  obtain ⟨φ, hφ, hφw⟩ := hsym pm.symm
  let e : (Fin (N + 1) → ℤˣ) ≃ (Fin (N + 1) → ℤˣ) := Equiv.arrowCongr pm (Equiv.refl ℤˣ)
  let w : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
    Real.exp (Esk g σ) / ∑ b, Real.exp (Esk g b)
  have key := integral_comp_weights_equiv
    (P := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) (w := w) hwm e hφ
    (fun g a => by simpa [e] using hφw g a)
    (Ψ := fun v => ∑ τ : R → Fin (N + 1) → ℤˣ, (∏ r, v (τ r)) * Θ τ) (by fun_prop)
  have hre : ∀ g, ∑ τ : R → Fin (N + 1) → ℤˣ, (∏ r, w g (e (τ r))) * Θ τ =
      ∑ τ : R → Fin (N + 1) → ℤˣ, (∏ r, w g (τ r)) * Θ (fun r i => τ r (pm i)) := fun g => by
    rw [← (Equiv.piCongrRight fun _ : R => e).sum_comp fun τ : R → Fin (N + 1) → ℤˣ =>
      (∏ r, w g (τ r)) * Θ (fun r i => τ r (pm i))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : (fun r i => (e (τ r)) (pm i)) = τ := funext fun r => funext fun i => by simp [e]
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, this]
  have hL : ∀ g, ∫ σ : R → Fin (N + 1) → ℤˣ, Θ (fun r i => σ r (pm i))
      ∂(Measure.pi fun _ : R => Measure.count.tilted (Esk g)) =
      ∑ τ : R → Fin (N + 1) → ℤˣ, (∏ r, w g (τ r)) * Θ (fun r i => τ r (pm i)) := fun g =>
    integral_pi_count_tilted (Esk g) _
  have hR : ∀ g, ∫ σ : R → Fin (N + 1) → ℤˣ, Θ σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (Esk g)) =
      ∑ τ : R → Fin (N + 1) → ℤˣ, (∏ r, w g (τ r)) * Θ τ := fun g =>
    integral_pi_count_tilted (Esk g) _
  simp only [hL, hR]
  simp only [hre] at key
  exact key

/-- The `n`-replica SK average of an observable is an integrable function of the disorder. -/
theorem integrable_integral_sk_replica (N n : ℕ) (β h : ℝ)
    (Φ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    Integrable (fun g : FinPairs (N + 1) → ℝ => ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
  integrable_integral_pi_count_tilted_det
    (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ))
    (fun a => (by fun_prop : Measurable fun g : FinPairs (N + 1) → ℝ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)).aemeasurable) Φ

/-- **Monotonicity of the `n`-replica SK average.** -/
theorem integral_integral_sk_replica_mono (N n : ℕ) (β h : ℝ)
    {Φ Ψ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ} (hΦΨ : ∀ σ, Φ σ ≤ Ψ σ) :
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Ψ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
  integral_mono (integrable_integral_sk_replica N n β h Φ)
    (integrable_integral_sk_replica N n β h Ψ)
    fun _ => integral_mono Integrable.of_finite Integrable.of_finite hΦΨ

/-- **Affine behaviour of the `n`-replica SK average.** -/
theorem integral_integral_sk_replica_affine (N n : ℕ) (β h a b : ℝ)
    (Φ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, (a * Φ σ + b)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
    a * ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) + b := by
  have hin (g : FinPairs (N + 1) → ℝ) : ∫ σ : Fin n → Fin (N + 1) → ℤˣ, (a * Φ σ + b)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) =
      a * ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) + b := by
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
    simp
  simp only [hin]
  rw [integral_add ((integrable_integral_sk_replica N n β h Φ).const_mul a) (integrable_const b),
    integral_const_mul]
  simp

/-- **Talagrand's Eq. (1.157), for an arbitrary function of the overlap.** By symmetry between
sites, `ν((R - q) φ(R - q)) = ν((ε₁ε₂ - q) φ(R - q))` for the last site. -/
theorem sk_overlap_mul_eq_last_site (N : ℕ) (β h q : ℝ) (φ : ℝ → ℝ) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
          φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro Esk
  let Rf : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (y i : ℝ))
  let Θ : Fin (N + 1) → (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun i x y =>
    ((x i : ℝ) * (y i : ℝ) - q) * φ (Rf x y - q)
  let ν : ((Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hRperm : ∀ (pm : Equiv.Perm (Fin (N + 1))) x y,
      Rf (fun i => x (pm i)) (fun i => y (pm i)) = Rf x y := fun pm x y => by
    simp only [Rf, dotProduct]
    rw [Equiv.sum_comp pm fun i => (x i : ℝ) * (y i : ℝ)]
  have hsite : ∀ i, ν (Θ i) = ν (Θ (Fin.last N)) := fun i => by
    have h1 := sk_replica_site_perm (R := Fin 2) N β h (Equiv.swap i (Fin.last N))
      (fun σ => Θ (Fin.last N) (σ 0) (σ 1))
    have h2 : ∀ x y, Θ (Fin.last N) (fun j => x (Equiv.swap i (Fin.last N) j))
        (fun j => y (Equiv.swap i (Fin.last N) j)) = Θ i x y := fun x y => by
      simp only [Θ, hRperm, Equiv.swap_apply_right]
    simp only [h2] at h1
    exact h1
  have hint : ∀ i, Integrable (fun g : FinPairs (N + 1) → ℝ => ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      Θ i (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := fun i =>
    integrable_integral_pi_count_tilted_det
      (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => Esk g a)
      (fun a => (by dsimp [Esk]; fun_prop : Measurable fun g : FinPairs (N + 1) → ℝ =>
        Esk g a).aemeasurable) fun σ => Θ i (σ 0) (σ 1)
  have hsum : ν (fun x y => ∑ i, Θ i x y) = ∑ i, ν (Θ i) := by
    simp only [ν]
    have e1 : ∀ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, ∑ i, Θ i (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g)) =
        ∑ i, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ i (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g)) := fun g =>
      integral_finsetSum _ fun i _ => Integrable.of_finite
    simp_rw [e1]
    exact integral_finsetSum _ fun i _ => hint i
  have hpt : ∀ x y, ∑ i, Θ i x y = ((N + 1 : ℕ) : ℝ) * ((Rf x y - q) * φ (Rf x y - q)) :=
    fun x y => by
      simp only [Θ, ← Finset.sum_mul]
      have : ∑ i, ((x i : ℝ) * (y i : ℝ) - q) = ((N + 1 : ℕ) : ℝ) * (Rf x y - q) := by
        simp only [Rf, dotProduct, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp
      rw [this]
      ring
  have hlin : ν (fun x y => ∑ i, Θ i x y) =
      ((N + 1 : ℕ) : ℝ) * ν (fun x y => (Rf x y - q) * φ (Rf x y - q)) := by
    simp only [ν, hpt, integral_const_mul]
  have hfin : ∑ i, ν (Θ i) = ((N + 1 : ℕ) : ℝ) * ν (Θ (Fin.last N)) := by
    simp only [hsite, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by push_cast; exact Nat.cast_add_one_ne_zero N
  have h3 : ((N + 1 : ℕ) : ℝ) * ν (fun x y => (Rf x y - q) * φ (Rf x y - q)) =
      ((N + 1 : ℕ) : ℝ) * ν (Θ (Fin.last N)) := by rw [← hlin, hsum, hfin]
  exact mul_left_cancel₀ hN h3

/-- **Talagrand's Eq. (1.158), for an arbitrary function of the overlap.** At the decoupled
endpoint, with `D = R⁻ - q` the truncated overlap deviation and `x = 1/(N+1)`, the average of
`(ε₁ε₂ - q) φ(R - q)` is `(1 - q²)` times the average of `(φ(D + x) - φ(D - x)) / 2`, by
Lemma 1.6.2 and the fixed-point equation. Only the part of `φ` that is odd about `D` survives. -/
theorem sk_cavity_decoupled_odd_part (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (φ : ℝ → ℝ) :
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
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
          φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
    (1 - q ^ 2) * ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        (φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ 0 i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ 1 i.castSucc : ℝ)) - q + (N + 1 : ℝ)⁻¹) -
          φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ 0 i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ 1 i.castSucc : ℝ)) - q - (N + 1 : ℝ)⁻¹)) / 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let x : ℝ := (N + 1 : ℝ)⁻¹
  let Dt : (Fin 2 → Fin N → ℤˣ) → ℝ := fun ρ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 1 i : ℝ)) - q
  let I : Bool → Finset (Fin 2) := fun u => if u then Finset.univ else ∅
  let Fv : Bool → (Fin 2 → Fin N → ℤˣ) → ℝ := fun v ρ =>
    if v then (φ (Dt ρ + x) + φ (Dt ρ - x)) / 2 else (φ (Dt ρ + x) - φ (Dt ρ - x)) / 2
  let cw : Bool × Bool → ℝ := fun j =>
    match j with
    | (true, true) => 1
    | (false, true) => -q
    | (true, false) => -q
    | (false, false) => 1
  let G : Bool × Bool → (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    Fv j.2 (fun r i => σ r i.castSucc) * ∏ r ∈ I j.1, ((σ r (Fin.last N) : ℤˣ) : ℝ)
  have hf : ∀ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
          φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) = ∑ j, cw j * G j σ := fun σ => by
    have he := units_cast_mul_eq_one_or (σ 0 (Fin.last N)) (σ 1 (Fin.last N))
    rw [sk_overlap_succ_eq_cavity N (σ 0) (σ 1)]
    have hA : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ 0 i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (σ 1 i.castSucc : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q =
        Dt (fun r i => σ r i.castSucc) +
          (σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) * x := by
      simp only [Dt, x]
      ring
    rw [hA]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cw, G, I, Fv, Fin.prod_univ_two,
      Finset.prod_empty, ite_true, ite_false, Bool.false_eq_true]
    rcases he with he | he <;> rw [he] <;> ring_nf
  let Nn : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Ψ =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Ψ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  let O : ((Fin 2 → Fin N → ℤˣ) → ℝ) → ℝ := fun F =>
    ∫ g', ∫ ρ : Fin 2 → Fin N → ℤˣ, F ρ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
        (fun r : Fin N → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
          h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hend : ∀ (I' : Finset (Fin 2)) (F : (Fin 2 → Fin N → ℤˣ) → ℝ),
      Nn (fun σ => F (fun r i => σ r i.castSucc) * ∏ r ∈ I', ((σ r (Fin.last N) : ℤˣ) : ℝ)) =
        (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ I'.card ∂(gaussianReal 0 1)) * O F :=
    fun I' F => sk_cavity_decoupled_endpoint N 2 β q h I' F
  have hlin : Nn (fun σ => ∑ j, cw j * G j σ) = ∑ j, cw j * Nn (G j) :=
    integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
      Finset.univ cw G
  have hfix' : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q := by
    have hz : ∀ z : ℝ, β * z * Real.sqrt q + h = β * Real.sqrt q * z + h := fun z => by ring
    simpa only [hz] using hfix
  have hT : Nn (fun σ => (φ (Dt (fun r i => σ r i.castSucc) + x) -
      φ (Dt (fun r i => σ r i.castSucc) - x)) / 2) = O (Fv false) := by
    have := hend ∅ (Fv false)
    simpa [Fv] using this
  have hmom1 :
      (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ (I true).card ∂(gaussianReal 0 1)) = q := by
    simp [I, hfix']
  have hmom0 :
      (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ (I false).card ∂(gaussianReal 0 1)) = 1 := by
    simp [I]
  change Nn (fun σ => ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
      φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) =
    (1 - q ^ 2) * Nn (fun σ => (φ (Dt (fun r i => σ r i.castSucc) + x) -
      φ (Dt (fun r i => σ r i.castSucc) - x)) / 2)
  rw [hT]
  have h1 : Nn (fun σ => ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
      φ ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) = Nn (fun σ => ∑ j, cw j * G j σ) := by
    simp only [Nn, hf]
  rw [h1, hlin, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, cw]
  rw [hend (I true) (Fv true), hend (I false) (Fv true), hend (I true) (Fv false),
    hend (I false) (Fv false), hmom1, hmom0]
  ring

/-- **Absorption step of Talagrand's Propositions 1.6.6 and 1.6.7.** Site symmetry turns
`ν((R - q)^(2k+2))` into `ν((ε₁ε₂ - q)(R - q)^(2k+1))`; Proposition 1.6.5 with the Hölder pair
`((2k+2)/(2k+1), 2k+2)` compares this with the decoupled average at the price of
`16 β² exp (64 β²) ν((R - q)^(2k+2))`, which the smallness hypothesis absorbs. -/
theorem sk_overlap_pow_le_two_nu_zero (N : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : 16 * β ^ 2 * Real.exp (64 * β ^ 2) ≤ 1 / 2) (k : ℕ) :
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
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    2 * ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * k + 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E Esk
  let Ab : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q
  let f : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) * Ab σ ^ (2 * k + 1)
  let ν : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  let ν₀ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hV0 : 0 ≤ ν (fun σ => Ab σ ^ (2 * k + 2)) :=
    integral_nonneg fun g => integral_nonneg fun σ =>
      Even.pow_nonneg ⟨k + 1, by ring⟩ _
  have hsite : ν (fun σ => Ab σ ^ (2 * k + 2)) = ν f := by
    have h := sk_overlap_mul_eq_last_site N β h q (fun a => a ^ (2 * k + 1))
    dsimp only at h
    simp only [← pow_succ'] at h
    exact h
  set m : ℝ := ((2 * k + 1 : ℕ) : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.le_add_left 1 (2 * k)
  have hm' : (((2 * k + 2 : ℕ)) : ℝ) = m + 1 := by rw [hm]; push_cast; ring
  set p : ℝ := ((2 * k + 2 : ℕ) : ℝ) / m with hp
  set r : ℝ := ((2 * k + 2 : ℕ) : ℝ) with hr
  have hpr : p.HolderConjugate r := by
    rw [hp, hm']
    exact Real.HolderConjugate.succ_div_self (by linarith)
  have hp0 : 0 ≤ p := hpr.nonneg
  have h165 := sk_cavity_nu_sub_nu_zero_le N 2 β q h hq f hpr
  dsimp only at h165
  have hpt1 : ∀ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      |f σ| ^ p ≤ 2 ^ p * Ab σ ^ (2 * k + 2) := fun σ => by
    have hxq := abs_units_cast_mul_sub_le_two (σ 0 (Fin.last N)) (σ 1 (Fin.last N)) hq
    have e1 : (|Ab σ| ^ (2 * k + 1)) ^ p = Ab σ ^ (2 * k + 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      have : ((2 * k + 1 : ℕ) : ℝ) * p = r := by
        rw [← hm, hp, hr]
        field_simp
      rw [this, hr, Real.rpow_natCast]
      exact Even.pow_abs ⟨k + 1, by ring⟩ _
    simp only [f, abs_mul, abs_pow]
    rw [Real.mul_rpow (abs_nonneg _) (pow_nonneg (abs_nonneg _) _), e1]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hxq hp0)
      (Even.pow_nonneg ⟨k + 1, by ring⟩ _)
  have hX1 : ν (fun σ => |f σ| ^ p) ≤ 2 ^ p * ν (fun σ => Ab σ ^ (2 * k + 2)) := by
    have := integral_integral_sk_replica_mono N 2 β h hpt1
    simpa only [ν, integral_const_mul] using this
  have hX2 : ν (fun σ => |Ab σ| ^ r) = ν (fun σ => Ab σ ^ (2 * k + 2)) := by
    have : ∀ σ, |Ab σ| ^ r = Ab σ ^ (2 * k + 2) := fun σ => by
      rw [hr, Real.rpow_natCast]
      exact Even.pow_abs ⟨k + 1, by ring⟩ _
    simp only [ν, this]
  have hX1nn : 0 ≤ ν (fun σ => |f σ| ^ p) :=
    integral_nonneg fun g => integral_nonneg fun σ => Real.rpow_nonneg (abs_nonneg _) _
  have habs : (ν fun σ => |f σ| ^ p) ^ (1 / p) * (ν fun σ => |Ab σ| ^ r) ^ (1 / r) ≤
      2 * ν (fun σ => Ab σ ^ (2 * k + 2)) := by
    rw [hX2]
    exact rpow_mul_rpow_le_mul_of_le_rpow_mul hpr (c := 2) (by norm_num) hV0 hX1nn hX1
  have hC : 2 * (((2 : ℕ) : ℝ)) ^ 2 * β ^ 2 * Real.exp (4 * (((2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) =
      8 * β ^ 2 * Real.exp (64 * β ^ 2) := by norm_num
  have h3 : |ν (fun σ => Ab σ ^ (2 * k + 2)) - ν₀ f| ≤
      16 * β ^ 2 * Real.exp (64 * β ^ 2) * ν (fun σ => Ab σ ^ (2 * k + 2)) := by
    rw [hsite]
    refine h165.trans ?_
    rw [hC]
    calc _ ≤ 8 * β ^ 2 * Real.exp (64 * β ^ 2) * (2 * ν (fun σ => Ab σ ^ (2 * k + 2))) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = _ := by rw [← hsite]; ring
  have h4 : 16 * β ^ 2 * Real.exp (64 * β ^ 2) * ν (fun σ => Ab σ ^ (2 * k + 2)) ≤
      1 / 2 * ν (fun σ => Ab σ ^ (2 * k + 2)) := mul_le_mul_of_nonneg_right hsmall hV0
  have h5 := (abs_le.1 (h3.trans h4)).2
  change ν (fun σ => Ab σ ^ (2 * k + 2)) ≤ 2 * ν₀ f
  linarith

/-- **One induction step for the overlap moments.** Combining the absorption step with the
decoupled endpoint: `ν((R - q)^(2k+2))` is at most `2 (1 - q²)` times the decoupled average of
`((D + x)^(2k+1) - (D - x)^(2k+1)) / 2`, where `D = R⁻ - q` and `x = 1/(N+1)`. -/
theorem sk_overlap_pow_le_two_odd_part (N : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hsmall : 16 * β ^ 2 * Real.exp (64 * β ^ 2) ≤ 1 / 2) (k : ℕ) :
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
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    2 * ((1 - q ^ 2) * ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ 0 i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ 1 i.castSucc : ℝ)) - q + (N + 1 : ℝ)⁻¹) ^ (2 * k + 1) -
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ 0 i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ 1 i.castSucc : ℝ)) - q - (N + 1 : ℝ)⁻¹) ^ (2 * k + 1)) / 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  intro B E Esk
  have h1 := sk_overlap_pow_le_two_nu_zero N β q h hq hsmall k
  have h2 := sk_cavity_decoupled_odd_part N β q h hfix (fun a => a ^ (2 * k + 1))
  dsimp only at h1 h2 ⊢
  rw [h2] at h1
  exact h1

/-- **Talagrand's Proposition 1.6.6** (for the `(N+1)`-spin system). If
`16 β² exp (64 β²) ≤ 1/2` and `q` solves the fixed-point equation, then
`ν((R_{1,2} - q)²) ≤ 2 / (N + 1)`. -/
theorem sk_overlap_sq_le_two_div (N : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hsmall : 16 * β ^ 2 * Real.exp (64 * β ^ 2) ≤ 1 / 2) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ 2 / (N + 1 : ℝ) := by
  intro Esk
  have h1 := sk_overlap_pow_le_two_odd_part N β q h hq hfix hsmall 0
  dsimp only at h1
  have hx : ∀ D x : ℝ, ((D + x) ^ (2 * 0 + 1) - (D - x) ^ (2 * 0 + 1)) / 2 = x := fun D x => by
    ring
  simp only [hx, integral_const, probReal_univ, one_smul] at h1
  have hN : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have h2 : (1 - q ^ 2) * (N + 1 : ℝ)⁻¹ ≤ (N + 1 : ℝ)⁻¹ :=
    mul_le_of_le_one_left (inv_nonneg.2 hN.le) (by nlinarith [sq_nonneg q, hq.1])
  calc _ ≤ _ := h1
    _ ≤ 2 * (N + 1 : ℝ)⁻¹ := by linarith
    _ = 2 / (N + 1 : ℝ) := by rw [div_eq_mul_inv]

end SpinGlasses
