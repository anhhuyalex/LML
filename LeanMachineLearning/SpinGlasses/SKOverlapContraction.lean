/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityContraction
public import LeanMachineLearning.SpinGlasses.SKCorrelationDecay

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

/-- **Site symmetry of a two-replica SK average.** Relabelling the sites of both replicas by a
permutation does not change the disorder average of a two-replica observable. -/
theorem sk_two_replica_site_perm (N : ℕ) (β h : ℝ) (pm : Equiv.Perm (Fin (N + 1)))
    (Θ : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ (fun i => σ 0 (pm i)) (fun i => σ 1 (pm i))
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro Esk
  obtain ⟨E, hE⟩ : ∃ E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ, ∀ g a, E g a =
      (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ) := ⟨Esk, fun g a => by simp [Esk]⟩
  have hEsk : Esk = E := funext fun g => funext fun a => by simp [Esk, hE]
  rw [hEsk]
  obtain ⟨hw0, hw1, hwm, hsym⟩ := sk_gibbsWeight_siteSymmetric β h E hE
  obtain ⟨φ, hφ, hφw⟩ := hsym pm.symm
  let e : (Fin (N + 1) → ℤˣ) ≃ (Fin (N + 1) → ℤˣ) := Equiv.arrowCongr pm (Equiv.refl ℤˣ)
  have key := integral_comp_weights_equiv
    (P := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (w := fun g σ => Real.exp (E g σ) / ∑ b, Real.exp (E g b)) hwm e hφ
    (fun g a => by simpa [e] using hφw g a)
    (Ψ := fun v => ∑ x, ∑ y, v x * v y * Θ x y) (by fun_prop)
  have hre : ∀ g, ∑ x, ∑ y, (Real.exp (E g (e x)) / ∑ b, Real.exp (E g b)) *
        (Real.exp (E g (e y)) / ∑ b, Real.exp (E g b)) * Θ x y =
      ∑ x, ∑ y, (Real.exp (E g x) / ∑ b, Real.exp (E g b)) *
        (Real.exp (E g y) / ∑ b, Real.exp (E g b)) *
        Θ (fun i => x (pm i)) (fun i => y (pm i)) := fun g => by
    rw [← e.sum_comp (fun x => ∑ y, (Real.exp (E g x) / ∑ b, Real.exp (E g b)) *
        (Real.exp (E g y) / ∑ b, Real.exp (E g b)) *
        Θ (fun i => x (pm i)) (fun i => y (pm i)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp (fun y => (Real.exp (E g (e x)) / ∑ b, Real.exp (E g b)) *
        (Real.exp (E g y) / ∑ b, Real.exp (E g b)) *
        Θ (fun i => (e x) (pm i)) (fun i => y (pm i)))]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h1 : (fun i => (e x) (pm i)) = x := funext fun i => by simp [e]
    have h2 : (fun i => (e y) (pm i)) = y := funext fun i => by simp [e]
    simp only [h1, h2]
  have hL : ∀ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ (fun i => σ 0 (pm i)) (fun i => σ 1 (pm i))
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) =
      ∑ x, ∑ y, (Real.exp (E g x) / ∑ b, Real.exp (E g b)) *
        (Real.exp (E g y) / ∑ b, Real.exp (E g b)) *
        Θ (fun i => x (pm i)) (fun i => y (pm i)) := fun g =>
    integral_pi_fin_two_count_tilted (E g)
      (fun x y => Θ (fun i => x (pm i)) (fun i => y (pm i)))
  have hR : ∀ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ (σ 0) (σ 1)
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) =
      ∑ x, ∑ y, (Real.exp (E g x) / ∑ b, Real.exp (E g b)) *
        (Real.exp (E g y) / ∑ b, Real.exp (E g b)) * Θ x y := fun g =>
    integral_pi_fin_two_count_tilted (E g) Θ
  simp only [hL, hR]
  simp only [hre] at key
  exact key

/-- **Talagrand's Eq. (1.157).** By symmetry between sites,
`ν((R - q)²) = ν((ε₁ε₂ - q)(R - q))` for the last site. -/
theorem sk_overlap_sq_eq_last_site (N : ℕ) (β h q : ℝ) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro Esk
  let Rf : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (y i : ℝ))
  let Θ : Fin (N + 1) → (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun i x y =>
    ((x i : ℝ) * (y i : ℝ) - q) * (Rf x y - q)
  let ν : ((Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hRperm : ∀ (pm : Equiv.Perm (Fin (N + 1))) x y,
      Rf (fun i => x (pm i)) (fun i => y (pm i)) = Rf x y := fun pm x y => by
    simp only [Rf, dotProduct]
    rw [Equiv.sum_comp pm fun i => (x i : ℝ) * (y i : ℝ)]
  have hsite : ∀ i, ν (Θ i) = ν (Θ (Fin.last N)) := fun i => by
    have h1 := sk_two_replica_site_perm N β h (Equiv.swap i (Fin.last N)) (Θ (Fin.last N))
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
  have hpt : ∀ x y, ∑ i, Θ i x y = ((N + 1 : ℕ) : ℝ) * (Rf x y - q) ^ 2 := fun x y => by
    simp only [Θ, ← Finset.sum_mul]
    have : ∑ i, ((x i : ℝ) * (y i : ℝ) - q) = ((N + 1 : ℕ) : ℝ) * (Rf x y - q) := by
      simp only [Rf, dotProduct, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
    rw [this]
    ring
  have hlin : ν (fun x y => ∑ i, Θ i x y) =
      ((N + 1 : ℕ) : ℝ) * ν (fun x y => (Rf x y - q) ^ 2) := by
    simp only [ν, hpt, integral_const_mul]
  have hfin : ∑ i, ν (Θ i) = ((N + 1 : ℕ) : ℝ) * ν (Θ (Fin.last N)) := by
    simp only [hsite, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by push_cast; exact Nat.cast_add_one_ne_zero N
  have h3 : ((N + 1 : ℕ) : ℝ) * ν (fun x y => (Rf x y - q) ^ 2) =
      ((N + 1 : ℕ) : ℝ) * ν (Θ (Fin.last N)) := by rw [← hlin, hsum, hfin]
  exact mul_left_cancel₀ hN h3

/-- **Talagrand's Eq. (1.158).** At the decoupled endpoint the observable
`(ε₁ε₂ - q)(R - q)` has average `(1 - q²)/(N + 1)`, by Lemma 1.6.2 and the fixed-point equation. -/
theorem sk_cavity_decoupled_overlap (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
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
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) = (1 - q ^ 2) / (N + 1 : ℝ) := by
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let I : Bool → Finset (Fin 2) := fun u => if u then Finset.univ else ∅
  let Fv : Bool → (Fin 2 → Fin N → ℤˣ) → ℝ := fun v ρ =>
    if v then (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 1 i : ℝ)) - q
    else 1
  let cw : Bool × Bool → ℝ := fun j =>
    match j with
    | (true, true) => 1
    | (false, true) => -q
    | (true, false) => -q / (N + 1)
    | (false, false) => 1 / (N + 1)
  let G : Bool × Bool → (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    Fv j.2 (fun r i => σ r i.castSucc) * ∏ r ∈ I j.1, ((σ r (Fin.last N) : ℤˣ) : ℝ)
  have hf : ∀ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) = ∑ j, cw j * G j σ := fun σ => by
    have h0 := units_cast_sq (σ 0 (Fin.last N))
    have h1 := units_cast_sq (σ 1 (Fin.last N))
    rw [sk_overlap_succ_eq_cavity N (σ 0) (σ 1)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cw, G, I, Fv, Fin.prod_univ_two,
      Finset.prod_empty, ite_true, ite_false, Bool.false_eq_true]
    field_simp
    linear_combination (((σ 1 (Fin.last N) : ℤˣ) : ℝ) ^ 2) * h0 + h1
  simp only [hf]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ cw G]
  have hterm : ∀ j : Bool × Bool, ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      G j σ ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ (I j.1).card ∂(gaussianReal 0 1)) *
        ∫ g', ∫ ρ : Fin 2 → Fin N → ℤˣ, Fv j.2 ρ
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := fun j =>
    sk_cavity_decoupled_endpoint N 2 β q h (I j.1) (Fv j.2)
  simp only [hterm]
  have hfix' : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q := by
    have hz : ∀ z : ℝ, β * z * Real.sqrt q + h = β * Real.sqrt q * z + h := fun z => by ring
    simpa only [hz] using hfix
  have hone : ∫ g' : FinPairs N → ℝ, ∫ ρ : Fin 2 → Fin N → ℤˣ, Fv false ρ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
        (fun r : Fin N → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
          h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) = 1 := by
    simp [Fv]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, cw, I, Fv, ite_true, ite_false, Bool.false_eq_true,
    Finset.card_univ, Fintype.card_fin, Finset.card_empty, pow_zero, integral_const,
    probReal_univ, one_smul]
  rw [hfix']
  ring

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
  let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
    |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (y i : ℝ)) - q|
  let f : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    ((σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q) *
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)
  let V : ℝ := ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hV0 : 0 ≤ V := integral_nonneg fun g => integral_nonneg fun σ => sq_nonneg _
  have hsite : V = ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    sk_overlap_sq_eq_last_site N β h q
  have hdec := sk_cavity_decoupled_overlap N β q h hfix
  have h165 := sk_cavity_nu_sub_nu_zero_le N 2 β q h hq f Real.HolderConjugate.two_two
  dsimp only at h165
  have hEg (c : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ => Esk g c) := by
    dsimp [Esk]
    fun_prop
  have hint2 (Φ : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ) :
      Integrable (fun g : FinPairs (N + 1) → ℝ => ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integrable_integral_pi_count_tilted_det
      (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => Esk g a)
      (fun a => (hEg a).aemeasurable) fun σ => Φ (σ 0) (σ 1)
  -- the Hölder factors
  have hdevV : ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 : ℝ)
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) = V := by
    simp only [V, dev, Real.rpow_two, sq_abs]
  have hfV : ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, |f σ| ^ (2 : ℝ)
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ 4 * V := by
    have hpt : ∀ σ : Fin 2 → Fin (N + 1) → ℤˣ, |f σ| ^ (2 : ℝ) ≤
        4 * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2 := fun σ => by
      have hx : |(σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ)| = 1 := by
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
      have hxq : |(σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q| ≤ 2 :=
        (abs_sub _ _).trans (by rw [hx, abs_of_nonneg hq.1]; linarith [hq.2])
      simp only [f, Real.rpow_two, abs_mul, mul_pow, sq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      calc _ = |(σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) - q| ^ 2 := (sq_abs _).symm
        _ ≤ 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hxq 2
        _ = 4 := by norm_num
    calc _ ≤ ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, 4 * ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
          integral_mono (hint2 fun x y => |f ![x, y]| ^ (2 : ℝ)) (hint2 fun x y => 4 *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (y i : ℝ)) - q) ^ 2)
            fun g => integral_mono Integrable.of_finite Integrable.of_finite hpt
      _ = 4 * V := by simp only [V, integral_const_mul]
  have h2 : |V - (1 - q ^ 2) / (N + 1 : ℝ)| ≤ 2 * (((2 : ℕ) : ℝ)) ^ 2 * β ^ 2 *
      Real.exp (4 * (((2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) *
      ((∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, |f σ| ^ (2 : ℝ)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / (2 : ℝ)) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 : ℝ)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / (2 : ℝ))) := by
    rw [hsite, ← hdec]
    exact h165
  rw [hdevV] at h2
  have hX : (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, |f σ| ^ (2 : ℝ)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / (2 : ℝ)) *
      V ^ (1 / (2 : ℝ)) ≤ 2 * V := by
    have hnn : 0 ≤ ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, |f σ| ^ (2 : ℝ)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
      integral_nonneg fun g => integral_nonneg fun σ => Real.rpow_nonneg (abs_nonneg _) _
    calc _ ≤ (4 * V) ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hnn hfV (by norm_num))
            (Real.rpow_nonneg hV0 _)
      _ = (4 * V * V) ^ (1 / (2 : ℝ)) := (Real.mul_rpow (by positivity) hV0).symm
      _ = 2 * V := by
          rw [show 4 * V * V = (2 * V) ^ 2 by ring, ← Real.rpow_natCast, ← Real.rpow_mul
            (by positivity)]
          norm_num
  have h3 : |V - (1 - q ^ 2) / (N + 1 : ℝ)| ≤ 16 * β ^ 2 * Real.exp (64 * β ^ 2) * V := by
    refine h2.trans ?_
    have hexp : 4 * (((2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2 = 64 * β ^ 2 := by norm_num
    rw [hexp]
    have := mul_le_mul_of_nonneg_left hX (by positivity :
      0 ≤ 2 * (((2 : ℕ) : ℝ)) ^ 2 * β ^ 2 * Real.exp (64 * β ^ 2))
    refine (le_of_eq (by ring)).trans (this.trans (le_of_eq ?_))
    push_cast
    ring
  have h4 : 16 * β ^ 2 * Real.exp (64 * β ^ 2) * V ≤ 1 / 2 * V :=
    mul_le_mul_of_nonneg_right hsmall hV0
  have hN : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have h5 : (1 - q ^ 2) / (N + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg q]) hN.le
  have h6 := (abs_le.1 (h3.trans h4)).2
  have h7 : V ≤ 2 / (N + 1 : ℝ) := by
    have : V / 2 ≤ 1 / (N + 1 : ℝ) := by linarith
    calc V = 2 * (V / 2) := by ring
      _ ≤ 2 * (1 / (N + 1 : ℝ)) := by linarith
      _ = 2 / (N + 1 : ℝ) := by ring
  exact h7

end SpinGlasses

