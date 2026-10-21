/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityDecoupled
public import LeanMachineLearning.SpinGlasses.SKCavityDomination

/-!
# The decoupled endpoint of the cavity path (Talagrand's Lemma 1.6.2)

At `t = 0` (the angle `π / 2`) the last spin is decoupled from the first `N`, so the path
average of `f⁻(σ⁻) ∏_{r ∈ I} ε_r` factors into `𝔼 (tanh Y)^|I|` times the average of `f⁻`
over the `N`-spin system with the old-pair energy.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Talagrand's Lemma 1.6.2 (Eq. (1.150)).** At the decoupled endpoint of the cavity path, with
`Y = β z √q + h`, the average of `f⁻(σ⁻) ∏_{r ∈ I} ε_r` is `𝔼 (tanh Y)^{|I|}` times the average of
`f⁻` under the `N`-spin Gibbs measure of the old-pair energy. -/
theorem sk_cavity_decoupled_endpoint (N n : ℕ) (β q h : ℝ) (I : Finset (Fin n))
    (F : (Fin n → Fin N → ℤˣ) → ℝ) :
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
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ I.card ∂(gaussianReal 0 1)) *
      ∫ g', ∫ ρ : Fin n → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (Equiv.prodComm (Fin N → ℤˣ) ℤˣ).trans (Fin.snocEquiv fun _ => ℤˣ)
  have he (x : (Fin N → ℤˣ) × ℤˣ) : e x = Fin.snoc x.1 x.2 := rfl
  have hpt (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ) :
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω)) =
        Real.tanh (β * ω.2 * Real.sqrt q + h) ^ I.card *
          ∫ ρ : Fin n → Fin N → ℤˣ, F ρ
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              (fun r : Fin N → ℤˣ =>
                (Real.sqrt (N + 1))⁻¹ * β *
                  (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                h * ∑ i : Fin N, (r i : ℝ))) := by
    rw [integral_pi_count_tilted_equiv (R := Fin n) e (E (π / 2) g' ω)]
    have hE : (fun x : (Fin N → ℤˣ) × ℤˣ => E (π / 2) g' ω (e x)) =
        fun x => ((Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (x.1 p.val.1 : ℝ) * (x.1 p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (x.1 i : ℝ)) +
          ((x.2 : ℤˣ) : ℝ) * (β * ω.2 * Real.sqrt q + h) := by
      funext x
      simp only [E, B, he, Real.cos_pi_div_two, Real.sin_pi_div_two, Fin.snoc_castSucc,
        Fin.snoc_last, Fin.sum_univ_castSucc, zero_mul, one_mul, zero_add]
      ring
    rw [hE]
    simp only [he, Fin.snoc_castSucc, Fin.snoc_last]
    exact integral_pi_count_tilted_decoupled_spin
      (fun r : Fin N → ℤˣ => (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
        h * ∑ i : Fin N, (r i : ℝ)) (β * ω.2 * Real.sqrt q + h) F I
  simp_rw [hpt, integral_mul_const]
  have hz : ∫ ω : (Fin N → ℝ) × ℝ, Real.tanh (β * ω.2 * Real.sqrt q + h) ^ I.card
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ I.card ∂(gaussianReal 0 1) := by
    rw [integral_fun_snd (μ := Measure.pi fun _ : Fin N => gaussianReal 0 1)
      (ν := gaussianReal 0 1) (fun z => Real.tanh (β * z * Real.sqrt q + h) ^ I.card)]
    simp
  simp_rw [hz]
  exact integral_const_mul _ _

end SpinGlasses
