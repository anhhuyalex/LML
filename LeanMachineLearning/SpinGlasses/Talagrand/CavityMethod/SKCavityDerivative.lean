/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityEndpoint

/-!
# Conditional Gaussian derivative for the cavity path

The old-pair disorder is fixed in this theorem. Its Hamiltonian is the deterministic
shift in the existing Gaussian replica interpolation theorem; the two independent
interpolated fields involve only the new-edge couplings and the scalar Gaussian.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Conditional, abstract-base form of the cavity replica derivative (Lemma 1.6.3).
The base energy `A` may in particular be the old-pair SK Hamiltonian after its
couplings are fixed. The covariance difference uses the *full* `N+1` normalization. -/
theorem hasDerivAt_integral_cavity_conditional (N n : ℕ) (β q : ℝ)
    (hq : 0 ≤ q) (A : (Fin (N + 1) → ℤˣ) → ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (t : ℝ) :
    HasDerivAt (fun s =>
      ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
                (a (Fin.last N) : ℝ) *
                  ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
              Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)))
      (Real.sin t * Real.cos t *
        ∫ ω : (Fin N → ℝ) × ℝ,
          ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
            f (fun r => τ (some (some r))) *
              ((∑ r : Fin n, ∑ r' : Fin n,
                  β ^ 2 * (τ (some (some r)) (Fin.last N) : ℝ) *
                    (τ (some (some r')) (Fin.last N) : ℝ) *
                    (q - (N + 1 : ℝ)⁻¹ *
                      ((fun i : Fin N => (τ (some (some r)) i.castSucc : ℝ)) ⬝ᵥ
                        fun i : Fin N => (τ (some (some r')) i.castSucc : ℝ)))) -
                2 * (n : ℝ) * ∑ r : Fin n,
                  β ^ 2 * (τ (some (some r)) (Fin.last N) : ℝ) *
                    (τ (some none) (Fin.last N) : ℝ) *
                    (q - (N + 1 : ℝ)⁻¹ *
                      ((fun i : Fin N => (τ (some (some r)) i.castSucc : ℝ)) ⬝ᵥ
                        fun i : Fin N => (τ (some none) i.castSucc : ℝ))) -
                (n : ℝ) * (β ^ 2 * (τ (some none) (Fin.last N) : ℝ) *
                  (τ (some none) (Fin.last N) : ℝ) *
                  (q - (N + 1 : ℝ)⁻¹ *
                    ((fun i : Fin N => (τ (some none) i.castSucc : ℝ)) ⬝ᵥ
                      fun i : Fin N => (τ (some none) i.castSucc : ℝ)))) +
                (n : ℝ) * ((n : ℝ) + 1) *
                  (β ^ 2 * (τ (some none) (Fin.last N) : ℝ) *
                    (τ none (Fin.last N) : ℝ) *
                    (q - (N + 1 : ℝ)⁻¹ *
                      ((fun i : Fin N => (τ (some none) i.castSucc : ℝ)) ⬝ᵥ
                        fun i : Fin N => (τ none i.castSucc : ℝ)))))
            ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
              (fun a : Fin (N + 1) → ℤˣ =>
                Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
                  (a (Fin.last N) : ℝ) *
                    ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
                Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a))
          ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) t := by
  let X : (Fin (N + 1) → ℤˣ) → ((Fin N → ℝ) × ℝ) → ℝ := fun a ω =>
    (Real.sqrt (N + 1))⁻¹ * β * (a (Fin.last N) : ℝ) *
      ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)
  let Y : (Fin (N + 1) → ℤˣ) → ((Fin N → ℝ) × ℝ) → ℝ := fun a ω =>
    β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q
  let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (b i.castSucc : ℝ)))
  have hXm : ∀ a, Measurable (X a) := by
    intro a
    dsimp [X]
    fun_prop
  have hYm : ∀ a, Measurable (Y a) := by
    intro a
    dsimp [Y]
    fun_prop
  have hU : ∀ a b, U a b =
      ∫ ω, Y a ω * Y b ω
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) -
      ∫ ω, X a ω * X b ω
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    fun a b => sk_cavity_covariance_difference N β q hq a b
  have hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    convert hasGaussianLaw_sk_cavity_fields N β q using 1
    funext ω s
    cases s <;> rfl
  have h := hasDerivAt_integral_replica_trig (R := Fin n)
    hXm hYm hXY
    (integral_sk_cavity_edge_field_eq_zero N β)
    (integral_sk_cavity_scalar_field_eq_zero N β q)
    (integral_sk_cavity_edge_mul_scalar_eq_zero N β q)
    U hU A f t
  simpa only [X, Y, U, Fintype.card_fin] using h

end SpinGlasses
