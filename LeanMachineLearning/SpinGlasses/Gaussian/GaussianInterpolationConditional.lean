/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianInterpolationReplica

/-!
# Replica derivative averaged over independent base disorder

Talagrand's Lemma 1.4.2 conditionally on a random base energy `B η`: the derivative of the
iterated average `𝔼_η 𝔼_ω ⟨Φ⟩` along the trigonometric path is the average of the conditional
derivative, provided the conditional derivative has a constant bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Function

namespace SpinGlasses

/-- **Lemma 1.4.2 with a random base energy.**  The base energy `B η` is part of the Gibbs
weight and depends on independent disorder `η ∼ P₀`; the Gaussian fields `X, Y` are independent
of it.  The conditional derivative is dominated by a constant `Dm`. -/
theorem hasDerivAt_integral_conditional_replica_trig
    {Ω₀ Ω α R : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α] [Nonempty α] [Fintype R]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] {P : Measure Ω} {X Y : α → Ω → ℝ}
    (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (U : α → α → ℝ)
    (hU : ∀ a b, U a b = ∫ ω, Y a ω * Y b ω ∂P - ∫ ω, X a ω * X b ω ∂P)
    (B : Ω₀ → α → ℝ) (hB : ∀ a, Measurable fun η => B η a)
    (Φ : (R → α) → ℝ) (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M) (t : ℝ) (Dm : ℝ)
    (hbound : ∀ η s, |Real.sin s * Real.cos s * ∫ ω, ∫ τ : Option (Option R) → α,
        Φ (fun r => τ (some (some r))) *
          ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card R * ∑ r, U (τ (some (some r))) (τ (some none)) -
            Fintype.card R * U (τ (some none)) (τ (some none)) +
            Fintype.card R * (Fintype.card R + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option R) =>
          Measure.count.tilted fun a => Real.cos s * X a ω + Real.sin s * Y a ω + B η a)
        ∂P| ≤ Dm) :
    HasDerivAt (fun s => ∫ η, ∫ ω, ∫ σ, Φ σ ∂(Measure.pi fun _ : R =>
        Measure.count.tilted fun a => Real.cos s * X a ω + Real.sin s * Y a ω + B η a) ∂P ∂P₀)
      (∫ η, Real.sin t * Real.cos t * ∫ ω, ∫ τ : Option (Option R) → α,
        Φ (fun r => τ (some (some r))) *
          ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card R * ∑ r, U (τ (some (some r))) (τ (some none)) -
            Fintype.card R * U (τ (some none)) (τ (some none)) +
            Fintype.card R * (Fintype.card R + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option R) =>
          Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + B η a)
        ∂P ∂P₀) t := by
  have := Fintype.ofFinite α
  have hP := hXY.isProbabilityMeasure
  let E : ℝ → Ω₀ → Ω → α → ℝ := fun s η ω a =>
    Real.cos s * X a ω + Real.sin s * Y a ω + B η a
  have hEm (s : ℝ) (a : α) : Measurable (fun x : Ω₀ × Ω => E s x.1 x.2 a) := by
    have h1 : Measurable fun x : Ω₀ × Ω => B x.1 a := (hB a).comp measurable_fst
    have h2 : Measurable fun x : Ω₀ × Ω => X a x.2 := (hXm a).comp measurable_snd
    have h3 : Measurable fun x : Ω₀ × Ω => Y a x.2 := (hYm a).comp measurable_snd
    exact ((h2.const_mul _).add (h3.const_mul _)).add h1
  let F : ℝ → Ω₀ → ℝ := fun s η =>
    ∫ ω, ∫ σ, Φ σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E s η ω)) ∂P
  let D : ℝ → Ω₀ → ℝ := fun s η => Real.sin s * Real.cos s * ∫ ω, ∫ τ : Option (Option R) → α,
    Φ (fun r => τ (some (some r))) *
      ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
        2 * Fintype.card R * ∑ r, U (τ (some (some r))) (τ (some none)) -
        Fintype.card R * U (τ (some none)) (τ (some none)) +
        Fintype.card R * (Fintype.card R + 1) * U (τ (some none)) (τ none))
    ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted (E s η ω)) ∂P
  have hFm : ∀ s, AEStronglyMeasurable (F s) P₀ := by
    intro s
    have hm : Measurable (fun x : Ω₀ × Ω => ∫ σ, Φ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E s x.1 x.2))) :=
      measurable_integral_pi_count_tilted (hEm s) fun _ => measurable_const
    exact hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hDm : AEStronglyMeasurable (D t) P₀ := by
    have hm : Measurable (fun x : Ω₀ × Ω => ∫ τ : Option (Option R) → α,
        Φ (fun r => τ (some (some r))) *
          ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card R * ∑ r, U (τ (some (some r))) (τ (some none)) -
            Fintype.card R * U (τ (some none)) (τ (some none)) +
            Fintype.card R * (Fintype.card R + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted (E t x.1 x.2))) :=
      measurable_integral_pi_count_tilted (hEm t) fun _ => measurable_const
    exact (stronglyMeasurable_const.mul
      hm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hFi : Integrable (F t) P₀ := by
    refine Integrable.of_bound (hFm t) M (ae_of_all _ fun η => ?_)
    rw [Real.norm_eq_abs]
    simpa only [F, Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := P) (f := fun ω =>
        ∫ σ, Φ σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E t η ω)))
      (C := M) (ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs] using abs_integral_pi_count_tilted_le _ hΦ)
  have hderiv : ∀ η s, HasDerivAt (fun u => F u η) (D s η) s := by
    intro η s
    exact hasDerivAt_integral_replica_trig hXm hYm hXY hX hY h0 U hU (B η) Φ s
  exact hasDerivAt_integral_conditional_of_deriv_bound P₀ F D t hFm hDm hFi hderiv Dm hbound

end SpinGlasses
