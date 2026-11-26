/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.PiFinMul
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Replica averages on a product space factorize

Replicas of a configuration `(a, b) ∈ A × B` split into replicas of `a` and of `b`.

* `integral_pi_prod_mul`: for the product law, the average of `F(first coordinates) G(second
  coordinates)` is the product of the two replica averages;
* `integral_pi_tilted_prod_add_mul`: if the energy is a sum `E₁(a) + E₂(b)`, the Gibbs replica
  average of such a product is the product of the replica averages of the two Gibbs laws
  (the base laws only need to be finite);
* `integral_pi_mul_of_ne`: two distinct replicas of a probability law are independent.

These are the model-free steps behind the factorization (2.39) of Talagrand's Lemma 2.3.1.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

section

variable {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B] [Fintype ι]

/-- **Replicas of a product law.** -/
theorem integral_pi_prod_mul (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (F : (ι → A) → ℝ) (G : (ι → B) → ℝ) :
    ∫ σ : ι → A × B, F (fun i => (σ i).1) * G (fun i => (σ i).2)
        ∂(Measure.pi fun _ : ι => μ.prod ν) =
      (∫ a, F a ∂(Measure.pi fun _ : ι => μ)) * ∫ b, G b ∂(Measure.pi fun _ : ι => ν) := by
  have h := (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => μ)
    (fun _ => ν)).integral_comp' (g := fun p => F p.1 * G p.2)
  rw [integral_prod_mul] at h
  exact h

/-- **Gibbs replicas of an additively split energy.** -/
theorem integral_pi_tilted_prod_add_mul {μ : Measure A} {ν : Measure B} [SigmaFinite μ]
    [SigmaFinite ν] (E₁ : A → ℝ) (E₂ : B → ℝ) (F : (ι → A) → ℝ) (G : (ι → B) → ℝ) :
    ∫ σ : ι → A × B, F (fun i => (σ i).1) * G (fun i => (σ i).2)
        ∂(Measure.pi fun _ : ι => (μ.prod ν).tilted fun p => E₁ p.1 + E₂ p.2) =
      (∫ a, F a ∂(Measure.pi fun _ : ι => μ.tilted E₁)) *
        ∫ b, G b ∂(Measure.pi fun _ : ι => ν.tilted E₂) := by
  rw [integral_pi_tilted_eq_div, integral_pi_tilted_eq_div (μ := μ),
    integral_pi_tilted_eq_div (μ := ν)]
  have key (F' : (ι → A) → ℝ) (G' : (ι → B) → ℝ) :
      ∫ σ : ι → A × B, F' (fun i => (σ i).1) * G' (fun i => (σ i).2) *
        Real.exp (∑ i, (E₁ (σ i).1 + E₂ (σ i).2)) ∂(Measure.pi fun _ : ι => μ.prod ν) =
      (∫ a, F' a * Real.exp (∑ i, E₁ (a i)) ∂(Measure.pi fun _ : ι => μ)) *
        ∫ b, G' b * Real.exp (∑ i, E₂ (b i)) ∂(Measure.pi fun _ : ι => ν) := by
    rw [← integral_pi_prod_mul (ι := ι) μ ν (fun a => F' a * Real.exp (∑ i, E₁ (a i)))
      (fun b => G' b * Real.exp (∑ i, E₂ (b i)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only [Finset.sum_add_distrib, Real.exp_add]
    ring
  have hden := key (fun _ => 1) (fun _ => 1)
  simp only [one_mul] at hden
  rw [key F G, hden, mul_div_mul_comm]

end

/-- **Two distinct replicas are independent.** -/
theorem integral_pi_mul_of_ne {X R : Type*} [MeasurableSpace X] [Fintype R] (ν : Measure X)
    [IsProbabilityMeasure ν] {i j : R} (hij : i ≠ j) {h h' : X → ℝ} (hh : Measurable h)
    (hh' : Measurable h') :
    ∫ τ : R → X, h (τ i) * h' (τ j) ∂(Measure.pi fun _ : R => ν) =
      (∫ x, h x ∂ν) * ∫ x, h' x ∂ν := by
  rw [integral_pi_pair_eq_prod ν hij (fun a b => h a * h' b)
    ((hh.comp measurable_fst).mul (hh'.comp measurable_snd)), integral_prod_mul]

end MeasureTheory
