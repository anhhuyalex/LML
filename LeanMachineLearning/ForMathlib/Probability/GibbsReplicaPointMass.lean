/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ProductTiltedMarginal

/-!
# A point-mass auxiliary coordinate in a Gibbs replica average

For the base law `μ ⊗ δ_{b₀}` the second coordinate is `b₀` almost surely, so every replica
average of an observable that only depends on the first coordinates on `{b = b₀}` is the replica
average against the `μ`-tilted measure with energy `E (·, b₀)`.

* `integral_pi_tilted_prod_dirac`: the transfer of one replica integral;
* `replicaDiff_tilted_prod_dirac`, `replicaPairAverage_tilted_prod_dirac`: the replica difference
  and the two-fresh-replica average (finite first factor).
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass B]
  {μ : Measure A} [SFinite μ] [NeZero μ]

/-- **A point-mass auxiliary coordinate disappears from the replica average.** If the second
coordinate has the point law `δ_{b₀}`, an observable of the replicas that only depends on the
first coordinates there (`G τ = g (τ.1)` whenever all second coordinates equal `b₀`) has the same
average under the replica product of `(μ ⊗ δ_{b₀})`-tilted measures as `g` under the replica
product of the `μ`-tilted measures with energy `E (·, b₀)`. -/
theorem integral_pi_tilted_prod_dirac (b₀ : B) {E : A × B → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod (Measure.dirac b₀)))
    {R : Type*} [Fintype R] {G : (R → A × B) → ℝ} {g : (R → A) → ℝ} (hg : Measurable g)
    (hG : ∀ τ : R → A × B, (∀ r, (τ r).2 = b₀) → G τ = g (fun r => (τ r).1)) :
    ∫ τ, G τ ∂(Measure.pi fun _ : R => (μ.prod (Measure.dirac b₀)).tilted E) =
      ∫ σ, g σ ∂(Measure.pi fun _ : R => μ.tilted fun a => E (a, b₀)) := by
  have hprob : IsProbabilityMeasure ((μ.prod (Measure.dirac b₀)).tilted E) :=
    isProbabilityMeasure_tilted hi
  have hae : ∀ᵐ τ ∂(Measure.pi fun _ : R => (μ.prod (Measure.dirac b₀)).tilted E),
      ∀ r, (τ r).2 = b₀ := by
    rw [ae_all_iff]
    intro r
    have h0 : ∀ᵐ x ∂(μ.prod (Measure.dirac b₀)), x.2 = b₀ :=
      Measure.quasiMeasurePreserving_snd.ae (by simp : ∀ᵐ y ∂(Measure.dirac b₀), y = b₀)
    exact (measurePreserving_eval (fun _ : R => (μ.prod (Measure.dirac b₀)).tilted E)
      r).quasiMeasurePreserving.ae ((tilted_absolutelyContinuous _ _).ae_le h0)
  have h1 : ∫ τ, G τ ∂(Measure.pi fun _ : R => (μ.prod (Measure.dirac b₀)).tilted E) =
      ∫ τ, g (fun r => (τ r).1) ∂(Measure.pi fun _ : R =>
        (μ.prod (Measure.dirac b₀)).tilted E) :=
    integral_congr_ae (hae.mono fun τ hτ => hG τ hτ)
  have he : (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂(Measure.dirac b₀))) =
      fun a => E (a, b₀) := funext fun a => by
    rw [integral_dirac, Real.log_exp]
  rw [h1, integral_pi_tilted_prod_fst hi hg, he]

section Finite

variable [Finite A] [MeasurableSingletonClass A]

/-- The replica difference for the point-mass auxiliary base law. -/
theorem replicaDiff_tilted_prod_dirac (b₀ : B) {E : A × B → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod (Measure.dirac b₀)))
    {R : Type*} [Fintype R] (f : (R → A) → ℝ) (h : A × B → ℝ) :
    replicaDiff ((μ.prod (Measure.dirac b₀)).tilted E)
        (fun σ : R → A × B => f (fun r => (σ r).1)) h =
      replicaDiff (μ.tilted fun a => E (a, b₀)) f (fun a => h (a, b₀)) := by
  have hprob : IsProbabilityMeasure ((μ.prod (Measure.dirac b₀)).tilted E) :=
    isProbabilityMeasure_tilted hi
  have hi' : ∀ i : Option R, ∫ τ : Option R → A × B, f (fun j => (τ (some j)).1) * h (τ i)
      ∂(Measure.pi fun _ : Option R => (μ.prod (Measure.dirac b₀)).tilted E) =
      ∫ σ : Option R → A, f (fun j => σ (some j)) * h (σ i, b₀)
      ∂(Measure.pi fun _ : Option R => μ.tilted fun a => E (a, b₀)) := fun i =>
    integral_pi_tilted_prod_dirac b₀ hi (measurable_of_finite _) (fun τ hτ => by
      have : τ i = ((τ i).1, b₀) := Prod.ext rfl (hτ i)
      exact congrArg (fun p => f (fun j => (τ (some j)).1) * h p) this)
  rw [replicaDiff_eq, replicaDiff_eq]
  simp only [hi']

/-- The two-fresh-replica average for the point-mass auxiliary base law. -/
theorem replicaPairAverage_tilted_prod_dirac (b₀ : B) {E : A × B → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod (Measure.dirac b₀)))
    {R : Type*} [Fintype R] [LinearOrder R] (f : (R → A) → ℝ) (U : A × B → A × B → ℝ) :
    replicaPairAverage ((μ.prod (Measure.dirac b₀)).tilted E)
        (fun σ : R → A × B => f (fun r => (σ r).1)) U =
      replicaPairAverage (μ.tilted fun a => E (a, b₀)) f (fun a b => U (a, b₀) (b, b₀)) := by
  have hprob : IsProbabilityMeasure ((μ.prod (Measure.dirac b₀)).tilted E) :=
    isProbabilityMeasure_tilted hi
  rw [replicaPairAverage_eq, replicaPairAverage_eq]
  refine integral_pi_tilted_prod_dirac b₀ hi (measurable_of_finite _) (fun τ hτ => ?_)
  have hτ' : τ = (fun a => (a, b₀)) ∘ (fun i => (τ i).1) :=
    funext fun i => Prod.ext rfl (hτ i)
  have hc : replicaPairCombination U τ = replicaPairCombination
      (fun a b => U (a, b₀) (b, b₀)) (fun i => (τ i).1) := by
    conv_lhs => rw [hτ']
    rfl
  rw [hc]

end Finite

end MeasureTheory
