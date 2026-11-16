/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Marginalizing an exponentially tilted product measure

Integrating an auxiliary variable replaces the joint energy by the logarithm of its
fiberwise exponential integral. The base spaces need not be finite. Explicit Bochner
integrability assumptions justify Fubini; no pointwise positivity assumption on the
fibers is needed because their exponential integrals are positive almost everywhere.

The replica version uses pushforward of finite products, including an empty replica type.
This is the common measure argument behind Talagrand's perceptron Exercise 2.2.1.
-/

@[expose] public section

namespace MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν] [NeZero ν]

/-- A first-coordinate observable under a tilted product measure has the same integral under
the first base measure tilted by the logarithm of the fiber partition function. -/
theorem integral_tilted_prod_fst {E : A × B → ℝ} {f : A → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod ν))
    (hfi : Integrable (fun x : A × B => f x.1 * Real.exp (E x)) (μ.prod ν)) :
    (∫ x, f x.1 ∂((μ.prod ν).tilted E)) =
      ∫ a, f a ∂(μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) := by
  have he : (fun a => Real.exp (Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) =ᵐ[μ]
      (fun a => ∫ b, Real.exp (E (a, b)) ∂ν) := by
    filter_upwards [hi.prod_right_ae] with a ha
    exact Real.exp_log (integral_exp_pos ha)
  rw [integral_tilted_eq_div, integral_tilted_eq_div, integral_prod _ hfi, integral_prod _ hi]
  simp_rw [integral_const_mul]
  rw [integral_congr_ae he]
  congr 1
  exact integral_congr_ae (he.mono fun a ha => congrArg (fun z => f a * z) ha.symm)

/-- The first marginal of a tilted product measure is the tilt by the logarithm of the
fiberwise exponential integral. Only exponential integrability on the product is required. -/
theorem map_fst_tilted_prod {E : A × B → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod ν)) :
    ((μ.prod ν).tilted E).map Prod.fst =
      μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν)) := by
  ext s hs
  apply (measureReal_eq_measureReal_iff).mp
  rw [map_measureReal_apply measurable_fst hs]
  have hfi : Integrable (fun x : A × B => s.indicator (fun _ => (1 : ℝ)) x.1 *
      Real.exp (E x)) (μ.prod ν) := by
    refine hi.bdd_mul (c := 1)
      ((measurable_const.indicator hs).comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    by_cases hx : x.1 ∈ s <;> simp [hx]
  have h := integral_tilted_prod_fst hi hfi
  have heq : (fun x : A × B => s.indicator (fun _ => (1 : ℝ)) x.1) =
      (Prod.fst ⁻¹' s).indicator (fun _ => 1) := by
    funext x
    by_cases hx : x.1 ∈ s <;> simp [hx]
  rw [heq, integral_indicator (hs.preimage measurable_fst), integral_indicator hs] at h
  simpa using h

/-- Marginalization commutes with forming replicas: any measurable observable of the first
coordinates has the same average under the product of the marginal tilted measures. -/
theorem integral_pi_tilted_prod_fst {E : A × B → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod ν))
    {R : Type*} [Fintype R] {f : (R → A) → ℝ} (hf : Measurable f) :
    (∫ x : R → A × B, f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (μ.prod ν).tilted E)) =
      ∫ a, f a ∂(Measure.pi fun _ : R =>
        μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) := by
  have hm := Measure.pi_map_pi (μ := fun _ : R => (μ.prod ν).tilted E)
    (fun _ => measurable_fst.aemeasurable)
  simp_rw [map_fst_tilted_prod hi] at hm
  rw [← hm]
  have hp : Measurable (fun x : R → A × B => fun r => (x r).1) := by fun_prop
  exact (integral_map hp.aemeasurable hf.aestronglyMeasurable).symm


/-- Integrating independent auxiliary coordinates in a finite-state Gibbs law replaces each
coordinate potential by its log exponential integral. The auxiliary laws and potentials may
vary between coordinates; only measurability and upper bounds are required. -/
theorem integral_pi_tilted_count_prod_sum {K : Type*} [Fintype K] [Fintype A]
    [MeasurableSingletonClass A] (νs : K → Measure B) [∀ k, IsProbabilityMeasure (νs k)]
    (D : A → ℝ) (V : A → K → B → ℝ) (hV : ∀ a k, Measurable (V a k))
    (C : K → ℝ) (hC : ∀ a k b, V a k b ≤ C k)
    {R : Type*} [Fintype R] (f : (R → A) → ℝ) :
    (∫ x : R → A × (K → B), f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (Measure.count.prod (Measure.pi νs)).tilted
        (fun p : A × (K → B) => D p.1 + ∑ k, V p.1 k (p.2 k)))) =
      ∫ a, f a ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => D a + ∑ k, Real.log (∫ b, Real.exp (V a k b) ∂νs k))) := by
  have hE : Measurable (fun p : A × (K → B) => D p.1 + ∑ k, V p.1 k (p.2 k)) := by
    refine measurable_from_prod_countable_right fun a => ?_
    change Measurable (fun b : K → B => D a + ∑ k, V a k (b k))
    exact measurable_const.add
      (Finset.measurable_sum Finset.univ fun k _ => (hV a k).comp (measurable_pi_apply k))
  have hb : ∀ p : A × (K → B), D p.1 + ∑ k, V p.1 k (p.2 k) ≤
      (∑ a, |D a|) + ∑ k, C k := fun p =>
    add_le_add ((le_abs_self _).trans
      (Finset.single_le_sum (fun a _ => abs_nonneg (D a)) (Finset.mem_univ p.1)))
      (Finset.sum_le_sum fun k _ => hC p.1 k (p.2 k))
  have hi := integrable_exp_of_ae_le (μ := Measure.count.prod (Measure.pi νs))
    hE.aemeasurable (ae_of_all _ hb)
  have hz (a : A) (k : K) : 0 < ∫ b, Real.exp (V a k b) ∂νs k :=
    integral_exp_pos_of_ae_le (hV a k).aemeasurable (ae_of_all _ fun b => hC a k b)
  have hlog (a : A) :
      Real.log (∫ b : K → B, Real.exp (D a + ∑ k, V a k (b k)) ∂Measure.pi νs) =
        D a + ∑ k, Real.log (∫ b, Real.exp (V a k b) ∂νs k) := by
    simp_rw [Real.exp_add, Real.exp_sum]
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (μ := νs) (fun k b => Real.exp (V a k b)),
      Real.log_mul (Real.exp_pos _).ne' (Finset.prod_pos fun k _ => hz a k).ne', Real.log_exp,
      Real.log_prod (fun k _ => (hz a k).ne')]
  rw [integral_pi_tilted_prod_fst hi (measurable_of_countable f)]
  simp_rw [hlog]

end MeasureTheory
