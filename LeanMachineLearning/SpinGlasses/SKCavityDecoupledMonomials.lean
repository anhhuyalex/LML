/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.QuarticSignProd
public import LeanMachineLearning.SpinGlasses.SKCavityDecoupledEndpoint
public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal
public import LeanMachineLearning.SpinGlasses.SKCavityDomination
public import LeanMachineLearning.SpinGlasses.SKFixedPoint

/-!
# Decoupled endpoint for an arbitrary set of replicas, and sign monomials

Talagrand's Lemma 1.6.2 (`sk_cavity_decoupled_endpoint`) for `Fin n` replicas, restated for any
finite set `R` of replicas, and its consequence for the products of four last spins that occur in
the algebra of Section 1.8: for `x ≠ y` and `a ≠ b`,
`ε_x ε_y ε_a ε_b` has decoupled average `𝔼 tanh^{4 - 2 c} Y`, where `c` counts the coincidences
among `x, y, a, b`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Lemma 1.6.2 for an arbitrary finite set of replicas.** -/
theorem sk_cavity_decoupled_endpoint_replicas (N : ℕ) (β q h : ℝ) {R : Type*} [Fintype R]
    (I : Finset R) (F : (R → Fin N → ℤˣ) → ℝ) :
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
          F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ I.card ∂(gaussianReal 0 1)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  have key := sk_cavity_decoupled_endpoint N (Fintype.card R) β q h (I.map e.toEmbedding)
    (fun ρ => F fun r => ρ (e r))
  simp only [Finset.card_map] at key
  have hL : ∀ (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ),
      ∫ σ : R → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω)) =
        ∫ σ : Fin (Fintype.card R) → Fin (N + 1) → ℤˣ,
          F (fun r i => σ (e r) i.castSucc) *
            ∏ r ∈ I.map e.toEmbedding, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : Fin (Fintype.card R) =>
            Measure.count.tilted (E (π / 2) g' ω)) := fun g' ω => by
    rw [integral_pi_count_tilted_reindex e (E (π / 2) g' ω)]
    simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  have hR : ∀ g' : FinPairs N → ℝ,
      ∫ ρ : R → Fin N → ℤˣ, F ρ ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) =
        ∫ ρ : Fin (Fintype.card R) → Fin N → ℤˣ, F (fun r => ρ (e r))
          ∂(Measure.pi fun _ : Fin (Fintype.card R) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) := fun g' =>
    integral_pi_count_tilted_reindex e _ F
  simp_rw [hL, hR]
  exact key

/-- **Decoupled average of a product of four last spins.**  For distinct `x ≠ y` and `a ≠ b`,
`ε_x ε_y ε_a ε_b` has the decoupled average `𝔼 tanh^{4 - 2 c} Y`, where `c` is the number of
coincidences among `x, y, a, b`, times the average of the old-spin observable. -/
theorem sk_cavity_decoupled_endpoint_quartic (N : ℕ) (β q h : ℝ) {R : Type*} [Fintype R]
    [DecidableEq R] {x y a b : R} (hxy : x ≠ y) (hab : a ≠ b)
    (F : (R → Fin N → ℤˣ) → ℝ) :
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
          F (fun r i => σ r i.castSucc) *
            (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) *
              ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^
        (4 - 2 * ((if x = a then 1 else 0) + (if x = b then 1 else 0) +
          (if y = a then 1 else 0) + (if y = b then 1 else 0))) ∂(gaussianReal 0 1)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  obtain ⟨I, hcard, hprod⟩ := exists_finset_prod_eq_quartic (A := ℝ) hxy hab
  have hpt : ∀ σ : R → Fin (N + 1) → ℤˣ,
      F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) *
          ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)) =
      F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ) := fun σ => by
    rw [hprod (fun r => ((σ r (Fin.last N) : ℤˣ) : ℝ)) fun r => ?_]
    exact units_cast_sq _
  simp_rw [hpt]
  have hI : I.card = 4 - 2 * ((if x = a then 1 else 0) + (if x = b then 1 else 0) +
      (if y = a then 1 else 0) + (if y = b then 1 else 0)) := by omega
  rw [← hI]
  exact sk_cavity_decoupled_endpoint_replicas N β q h I F

/-- Number of coincidences between two replica pairs `{x, y}` and `{a, b}`. -/
def skCavityCoincidences {R : Type*} [DecidableEq R] (x y a b : R) : ℕ :=
  (if x = a then 1 else 0) + (if x = b then 1 else 0) +
    (if y = a then 1 else 0) + (if y = b then 1 else 0)

/-- For distinct pairs `x ≠ y` and `a ≠ b`, there are at most two coincidences. -/
theorem sk_cavity_coincidences_le_two {R : Type*} [DecidableEq R] {x y a b : R}
    (_hxy : x ≠ y) (hab : a ≠ b) :
    skCavityCoincidences x y a b ≤ 2 := by
  dsimp [skCavityCoincidences]
  have hxa : (if x = a then 1 else 0) + (if x = b then 1 else 0) ≤ 1 := by
    by_cases h : x = a <;> by_cases h' : x = b <;> simp [h, h', hab, hab.symm]
  have hya : (if y = a then 1 else 0) + (if y = b then 1 else 0) ≤ 1 := by
    by_cases h : y = a <;> by_cases h' : y = b <;> simp [h, h', hab, hab.symm]
  omega

/-- The unscaled coefficient `b(c)` of Lemma 1.8.2 before multiplying by `β²`.
`1 - q²` for `c = 2`, `q - q²` for `c = 1`, `q̂ - q²` for `c = 0`. -/
def skCavityBUnscaled (q qhat : ℝ) (c : ℕ) : ℝ :=
  if c = 2 then 1 - q ^ 2
  else if c = 1 then q - q ^ 2
  else qhat - q ^ 2

/-- Scaled coefficient `b(c) = β² b_unscaled(c)`. -/
def skCavityBCoef (β q qhat : ℝ) (c : ℕ) : ℝ :=
  β ^ 2 * skCavityBUnscaled q qhat c

/-- The unscaled coefficient `skCavityBUnscaled` matches the difference of decoupled moments
`𝔼 tanh^{4 - 2c} Y - q²` for any `c ≤ 2`. -/
theorem sk_cavity_b_unscaled_eq (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (c : ℕ) (hc : c ≤ 2) :
    (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ (4 - 2 * c) ∂(gaussianReal 0 1)) - q ^ 2 =
      skCavityBUnscaled q qhat c := by
  dsimp [skCavityBUnscaled]
  interval_cases c
  · have h0 : 4 - 2 * 0 = 4 := by norm_num
    rw [h0, integral_tanh_pow_mul_z_sqrt_eq, hqhat]
    simp
  · have h1 : 4 - 2 * 1 = 2 := by norm_num
    rw [h1, integral_tanh_pow_mul_z_sqrt_eq, hfix]
    simp
  · have h2 : 4 - 2 * 2 = 0 := by norm_num
    rw [h2]
    simp only [pow_zero, integral_const, probReal_univ, one_smul]
    simp

/-- **Decoupled average of a pair covariance monomial.**  For distinct `x ≠ y` and `a ≠ b`,
the decoupled average of `f⁻ (ε_x ε_y - q) ε_a ε_b` is `sk_cavity_b_unscaled q q̂ c` times the
average of `f⁻` at the decoupled endpoint, where `c` is the number of coincidences between
`{x, y}` and `{a, b}`. -/
theorem sk_cavity_decoupled_endpoint_pair_cov (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {R : Type*} [Fintype R] [DecidableEq R] {x y a b : R} (hxy : x ≠ y) (hab : a ≠ b)
    (F : (R → Fin N → ℤˣ) → ℝ) :
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
          F (fun r i => σ r i.castSucc) *
            ((((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
              (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    skCavityBUnscaled q qhat (skCavityCoincidences x y a b) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let cw : Bool → ℝ := fun u => if u then 1 else -q
  let Gj : Bool → (R → Fin (N + 1) → ℤˣ) → ℝ := fun u σ =>
    if u then
      F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) *
          ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
    else
      F (fun r i => σ r i.castSucc) *
        (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
  have hpt : ∀ σ : R → Fin (N + 1) → ℤˣ,
      F (fun r i => σ r i.castSucc) *
        ((((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
          (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) =
        ∑ u : Bool, cw u * Gj u σ := fun σ => by
    simp only [cw, Gj, Fintype.sum_bool, ite_true, ite_false, Bool.false_eq_true]
    ring
  simp_rw [hpt]
  have hlin := integral_nested_gibbs_finset_sum
    (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    (E (π / 2)) hEm Finset.univ cw Gj
  refine hlin.trans ?_
  have hT' : (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ, Gj true σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^
        (4 - 2 * skCavityCoincidences x y a b) ∂(gaussianReal 0 1)) *
        ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
          ∂(Measure.pi fun _ : R => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have hgt : ∀ σ : R → Fin (N + 1) → ℤˣ, Gj true σ =
        F (fun r i => σ r i.castSucc) *
          (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) *
            ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)) := fun σ => by
      simp only [Gj, ite_true]
    simp_rw [hgt]
    have key := sk_cavity_decoupled_endpoint_quartic N β q h hxy hab F
    have hco : (4 - 2 * ((if x = a then 1 else 0) + (if x = b then 1 else 0) +
        (if y = a then 1 else 0) + (if y = b then 1 else 0))) =
        4 - 2 * skCavityCoincidences x y a b := rfl
    rw [hco] at key
    exact key
  have hF' : ∀ σ : R → Fin (N + 1) → ℤˣ,
      Gj false σ = F (fun r i => σ r i.castSucc) * ∏ r ∈ ({a, b} : Finset R),
        ((σ r (Fin.last N) : ℤˣ) : ℝ) := fun σ => by
    simp only [Gj, ite_false, Bool.false_eq_true, prod_pair hab, mul_assoc]
  have hF : (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ, Gj false σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) *
        ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
          ∂(Measure.pi fun _ : R => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    simp_rw [hF']
    have key := sk_cavity_decoupled_endpoint_replicas N β q h ({a, b} : Finset R) F
    rw [card_pair hab] at key
    exact key
  have hfix' : (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) = q := by
    rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
  simp only [Fintype.sum_bool, cw, ite_true, ite_false, one_mul, Bool.false_eq_true]
  rw [hT', hF, hfix']
  set O : ℝ := ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hc : skCavityCoincidences x y a b ≤ 2 := sk_cavity_coincidences_le_two hxy hab
  have hdiff := sk_cavity_b_unscaled_eq β q h hfix qhat hqhat (skCavityCoincidences x y a b) hc
  calc (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ (4 - 2 * skCavityCoincidences x y a b)
          ∂(gaussianReal 0 1)) * O + -q * (q * O) =
      ((∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ (4 - 2 * skCavityCoincidences x y a b)
          ∂(gaussianReal 0 1)) - q ^ 2) * O := by ring
    _ = skCavityBUnscaled q qhat (skCavityCoincidences x y a b) * O := by rw [hdiff]

end SpinGlasses
