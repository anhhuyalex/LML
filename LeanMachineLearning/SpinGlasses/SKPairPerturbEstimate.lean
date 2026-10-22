/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKPairPerturbGaussian
public import LeanMachineLearning.SpinGlasses.GibbsMeasureNested
public import LeanMachineLearning.SpinGlasses.GaussianInterpolationConditional
public import LeanMachineLearning.SpinGlasses.SKCavityFreeEnergy

/-!
# The pair-perturbation estimate (Talagrand Eq. 1.182)

The path `s ↦ 𝔼 log ⟨exp(cos s u + sin s v)⟩` between the pair-perturbed `(N+1)`-spin system
(`s = 0`) and the decoupled scalar Gaussian (`s = π / 2`) has a derivative within
`β² 𝔼⟨|R_{1,2} - q|⟩_s + 2β² / (N+1)` of `-(β²/2)(1 - q²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Derivative of the pair-perturbation path (Talagrand Eqs. 1.178, 1.182).**  For any
measurable family of base energies `B η` with integrable coordinates, the path
`s ↦ 𝔼 log ∑ₐ exp(cos s u_a + sin s v + B η a)` has derivative `sin t cos t D` at every `t`,
where `D` is within `β² ν_t(|R - q|) + 2β²/(N+1)` of `-(β²/2)(1 - q²)`, `ν_t` the average of the
two-replica tilted measure at time `t`. -/
theorem exists_hasDerivAt_sk_pair_perturb_path
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (N : ℕ) (hN : 0 < N) (β q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (B : Ω₀ → (Fin (N + 1) → ℤˣ) → ℝ) (hB : ∀ a, Measurable fun η => B η a)
    (hBi : ∀ a, Integrable (fun η => B η a) P₀) (t : ℝ) :
    ∃ D : ℝ, HasDerivAt (fun s => ∫ η, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
        Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (Real.cos s *
          (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
            ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          Real.sin s * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a))
        ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂P₀) (Real.sin t * Real.cos t * D) t ∧
      |D - (-(β ^ 2 / 2) * (1 - q ^ 2))| ≤
        β ^ 2 * (∫ η, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
          ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
            |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i.castSucc : ℝ) * (p.2 i.castSucc : ℝ) - q|
            ∂((Measure.count.tilted fun a => Real.cos t *
                (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
                  ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
                Real.sin t * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a).prod
              (Measure.count.tilted fun a => Real.cos t *
                (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
                  ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
                Real.sin t * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a))
          ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1))
          ∂P₀) + 2 * β ^ 2 / ((N : ℝ) + 1) := by
  have _ : Nonempty (Fin (N + 1) → ℤˣ) := ⟨fun _ => 1⟩
  set P : Measure ((FinPairs (N + 1) → ℝ) × ℝ) :=
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1) with hPdef
  set X : (Fin (N + 1) → ℤˣ) → (FinPairs (N + 1) → ℝ) × ℝ → ℝ := fun a ω =>
    β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
      ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ) with hXdef
  set Y : (Fin (N + 1) → ℤˣ) → (FinPairs (N + 1) → ℝ) × ℝ → ℝ := fun _ ω =>
    β * (Real.sqrt 2)⁻¹ * q * ω.2 with hYdef
  have hXm : ∀ a, Measurable (X a) := fun a => by simp only [hXdef]; fun_prop
  have hYm : ∀ a, Measurable (Y a) := fun a => by simp only [hYdef]; fun_prop
  have hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P := by
    convert hasGaussianLaw_sk_pair_perturb_fields N β q using 1
    ext ω (σ | σ) <;> rfl
  have hX : ∀ a, ∫ ω, X a ω ∂P = 0 := fun a => integral_sk_pair_perturb_edge_field_eq_zero N β a
  have hY : ∀ a, ∫ ω, Y a ω ∂P = 0 := fun a =>
    integral_sk_pair_perturb_scalar_field_eq_zero N β q
  have h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0 := fun a b =>
    integral_sk_pair_perturb_edge_mul_scalar_eq_zero N β q a
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  sorry

end SpinGlasses
