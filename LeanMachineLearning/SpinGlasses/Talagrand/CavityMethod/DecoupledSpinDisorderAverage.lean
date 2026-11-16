/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityDecoupled
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Disorder averages of a decoupled last spin

Talagrand, *Spin Glasses* Vol. I, Lemma 1.6.2 and Lemma 2.2.2.  When the energy of the state
`(a, ε) ∈ α × ℤˣ` is `A a + ε Y`, the last spin `ε` is decoupled from `a`.
`integral_pi_count_tilted_decoupled_spin` computes the replica average for fixed `A` and `Y`.
Here the energy of the old state depends on one disorder `ω₀` and the field `Y` on another,
independent, disorder `ω₁`; both are integrated.  The result is the factorization
`𝔼 (tanh Y)^|I| · 𝔼 ⟨f⁻⟩`. The iterated-integral identity needs no assumptions on the
disorder measures. In its probability-law applications the variance of `Y` may be zero.

## Main declaration

* `SpinGlasses.integral_integral_pi_count_tilted_decoupled_spin`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- **Disorder-averaged decoupled last spin.**  Let the old-state energy `A ω₀` depend on a
disorder `ω₀ ∼ μ₀` and the field `Y ω₁` on an independent disorder `ω₁ ∼ μ₁`.  For a function `F`
of the old states of `n` replicas and a set `I` of replicas,
`𝔼 ⟨F(a) ∏_{r ∈ I} ε_r⟩ = 𝔼 (tanh Y)^|I| · 𝔼 ⟨F⟩_A`, with the replica measures the products of the
counting measure tilted by `A ω₀ a + ε Y ω₁`, respectively `A ω₀`. -/
theorem integral_integral_pi_count_tilted_decoupled_spin {Ω₀ Ω₁ α : Type*} [MeasurableSpace Ω₀]
    [MeasurableSpace Ω₁] [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (μ₀ : Measure Ω₀) (μ₁ : Measure Ω₁)
    (A : Ω₀ → α → ℝ) (Y : Ω₁ → ℝ) (F : (Fin n → α) → ℝ) (I : Finset (Fin n)) :
    ∫ ω₀, ∫ ω₁, ∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) * ∏ r ∈ I, (((σ r).2 : ℤˣ) : ℝ)
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun x : α × ℤˣ => A ω₀ x.1 + ((x.2 : ℤˣ) : ℝ) * Y ω₁) ∂μ₁ ∂μ₀ =
      (∫ ω₁, Real.tanh (Y ω₁) ^ I.card ∂μ₁) *
        ∫ ω₀, ∫ ρ, F ρ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (A ω₀)) ∂μ₀ := by
  simp_rw [integral_pi_count_tilted_decoupled_spin _ _ F I, integral_mul_const,
    integral_const_mul]

end SpinGlasses
