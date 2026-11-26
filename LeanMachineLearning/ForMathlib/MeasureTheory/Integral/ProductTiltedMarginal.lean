/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity

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

/-- Tilting `μ.prod γ` by `E₀ ∘ Prod.fst` equals `(μ.tilted E₀).prod γ` when `γ` is a probability
measure. -/
theorem tilted_prod_comp_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (γ : Measure β) [IsProbabilityMeasure γ]
    (E₀ : α → ℝ) :
    (μ.prod γ).tilted (fun p => E₀ p.1) = (μ.tilted E₀).prod γ := by
  have hZ : ∫ p : α × β, Real.exp (E₀ p.1) ∂(μ.prod γ) = ∫ a, Real.exp (E₀ a) ∂μ :=
    integral_prod_fun_fst_of_isProbabilityMeasure μ γ fun a => Real.exp (E₀ a)
  -- the density is measurable whether or not the exponential is integrable
  have hg : AEMeasurable (fun a => ENNReal.ofReal
      (Real.exp (E₀ a) / ∫ a, Real.exp (E₀ a) ∂μ)) μ := by
    by_cases hi : Integrable (fun a => Real.exp (E₀ a)) μ
    · exact (hi.aemeasurable.div_const _).ennreal_ofReal
    · simp only [integral_undef hi, div_zero, ENNReal.ofReal_zero]
      exact aemeasurable_const
  simp only [Measure.tilted, hZ]
  exact (prod_withDensity_left₀ (ν := γ) hg).symm

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν] [NeZero ν]

/-- A vector-valued first-coordinate observable under a tilted product measure has the same
integral under the first base measure tilted by the logarithm of the fiber partition function. -/
theorem integral_tilted_prod_fst_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : A × B → ℝ} {f : A → F}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod ν))
    (hfi : Integrable (fun x : A × B => Real.exp (E x) • f x.1) (μ.prod ν)) :
    (∫ x, f x.1 ∂((μ.prod ν).tilted E)) =
      ∫ a, f a ∂(μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) := by
  by_cases hF : CompleteSpace F
  swap
  · simp [integral_of_not_completeSpace hF]
  have he : (fun a => Real.exp (Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) =ᵐ[μ]
      (fun a => ∫ b, Real.exp (E (a, b)) ∂ν) := by
    filter_upwards [hi.prod_right_ae] with a ha
    exact Real.exp_log (integral_exp_pos ha)
  have hZ : ∫ a, Real.exp (Real.log (∫ b, Real.exp (E (a, b)) ∂ν)) ∂μ =
      ∫ x, Real.exp (E x) ∂(μ.prod ν) := by
    rw [integral_congr_ae he, integral_prod _ hi]
  have hsm : ∀ (c : ℝ) (x : A × B), (Real.exp (E x) / c) • f x.1 =
      c⁻¹ • (Real.exp (E x) • f x.1) := fun c x => by rw [smul_smul, div_eq_inv_mul]
  rw [integral_tilted, integral_tilted, hZ]
  simp only [hsm]
  rw [integral_smul, integral_prod _ hfi]
  simp only [integral_smul_const]
  rw [← integral_smul]
  refine integral_congr_ae (he.mono fun a ha => ?_)
  simp only [ha]
  rw [smul_smul, div_eq_inv_mul]

/-- A first-coordinate observable under a tilted product measure has the same integral under
the first base measure tilted by the logarithm of the fiber partition function. -/
theorem integral_tilted_prod_fst {E : A × B → ℝ} {f : A → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod ν))
    (hfi : Integrable (fun x : A × B => f x.1 * Real.exp (E x)) (μ.prod ν)) :
    (∫ x, f x.1 ∂((μ.prod ν).tilted E)) =
      ∫ a, f a ∂(μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) :=
  integral_tilted_prod_fst_smul hi (by simpa only [smul_eq_mul, mul_comm] using hfi)

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

/-- Marginalization commutes with forming replicas, for vector-valued observables of the first
coordinates which are a.e. strongly measurable for the product of the marginal tilted
measures. -/
theorem integral_pi_tilted_prod_fst_of_aestronglyMeasurable {E : A × B → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod ν))
    {R F : Type*} [Fintype R] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (R → A) → F}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : R =>
      μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν)))) :
    (∫ x : R → A × B, f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (μ.prod ν).tilted E)) =
      ∫ a, f a ∂(Measure.pi fun _ : R =>
        μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) := by
  have hm := Measure.pi_map_pi (μ := fun _ : R => (μ.prod ν).tilted E)
    (fun _ => measurable_fst.aemeasurable)
  simp_rw [map_fst_tilted_prod hi] at hm
  rw [← hm] at hf ⊢
  have hp : Measurable (fun x : R → A × B => fun r => (x r).1) := by fun_prop
  exact (integral_map hp.aemeasurable hf).symm

/-- Marginalization commutes with forming replicas: any measurable observable of the first
coordinates has the same average under the product of the marginal tilted measures. -/
theorem integral_pi_tilted_prod_fst {E : A × B → ℝ}
    (hi : Integrable (fun x => Real.exp (E x)) (μ.prod ν))
    {R : Type*} [Fintype R] {f : (R → A) → ℝ} (hf : Measurable f) :
    (∫ x : R → A × B, f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (μ.prod ν).tilted E)) =
      ∫ a, f a ∂(Measure.pi fun _ : R =>
        μ.tilted (fun a => Real.log (∫ b, Real.exp (E (a, b)) ∂ν))) :=
  integral_pi_tilted_prod_fst_of_aestronglyMeasurable hi hf.aestronglyMeasurable

/-- **An unused coordinate does not change the replica average**, for vector-valued observables.
If the energy on `A × B` does not depend on the second coordinate and `ν` is a probability
measure, a first-coordinate replica observable has the same average under the product of the
tilted product measures as under the product of `μ.tilted E₁`. -/
theorem integral_pi_tilted_prod_comp_fst_of_aestronglyMeasurable [IsProbabilityMeasure ν]
    {E₁ : A → ℝ} (hi : Integrable (fun a => Real.exp (E₁ a)) μ)
    {R F : Type*} [Fintype R] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (R → A) → F}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : R => μ.tilted E₁)) :
    (∫ x : R → A × B, f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (μ.prod ν).tilted fun x => E₁ x.1)) =
      ∫ a, f a ∂(Measure.pi fun _ : R => μ.tilted E₁) := by
  have e : (fun a => Real.log (∫ _ : B, Real.exp (E₁ a) ∂ν)) = E₁ := by
    funext a
    simp only [integral_const, probReal_univ, one_smul, Real.log_exp]
  have h := integral_pi_tilted_prod_fst_of_aestronglyMeasurable (μ := μ) (ν := ν)
    (E := fun x => E₁ x.1) (hi.comp_fst ν) (R := R) (f := f) (by simpa only [e] using hf)
  simpa only [e] using h

/-- **An unused coordinate does not change the replica average.** If the energy on `A × B` does
not depend on the second coordinate and `ν` is a probability measure, a first-coordinate replica
observable has the same average under the product of the tilted product measures as under the
product of `μ.tilted E₁`. -/
theorem integral_pi_tilted_prod_comp_fst [IsProbabilityMeasure ν] {E₁ : A → ℝ}
    (hi : Integrable (fun a => Real.exp (E₁ a)) μ)
    {R : Type*} [Fintype R] {f : (R → A) → ℝ} (hf : Measurable f) :
    (∫ x : R → A × B, f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (μ.prod ν).tilted fun x => E₁ x.1)) =
      ∫ a, f a ∂(Measure.pi fun _ : R => μ.tilted E₁) :=
  integral_pi_tilted_prod_comp_fst_of_aestronglyMeasurable hi hf.aestronglyMeasurable

/-- Integrating independent auxiliary coordinates in a Gibbs law replaces each coordinate
potential by its log exponential integral. The base is any finite measure, the energy `D` and
the potentials need only be measurable and bounded above, and the observable may be
vector-valued. -/
theorem integral_pi_tilted_prod_sum {K : Type*} [Fintype K] (μ₀ : Measure A)
    [IsFiniteMeasure μ₀] (νs : K → Measure B) [∀ k, IsProbabilityMeasure (νs k)]
    {D : A → ℝ} (hD : Measurable D) {M : ℝ} (hDM : ∀ a, D a ≤ M)
    {V : A → K → B → ℝ} (hV : ∀ k, Measurable fun p : A × B => V p.1 k p.2)
    {C : K → ℝ} (hC : ∀ a k b, V a k b ≤ C k)
    {R F : Type*} [Fintype R] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (R → A) → F}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : R => μ₀.tilted
      (fun a => D a + ∑ k, Real.log (∫ b, Real.exp (V a k b) ∂νs k)))) :
    (∫ x : R → A × (K → B), f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (μ₀.prod (Measure.pi νs)).tilted
        (fun p : A × (K → B) => D p.1 + ∑ k, V p.1 k (p.2 k)))) =
      ∫ a, f a ∂(Measure.pi fun _ : R => μ₀.tilted
        (fun a => D a + ∑ k, Real.log (∫ b, Real.exp (V a k b) ∂νs k))) := by
  have hE : Measurable (fun p : A × (K → B) => D p.1 + ∑ k, V p.1 k (p.2 k)) :=
    (hD.comp measurable_fst).add <| Finset.measurable_sum Finset.univ fun k _ =>
      (hV k).comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  have hb : ∀ p : A × (K → B), D p.1 + ∑ k, V p.1 k (p.2 k) ≤ M + ∑ k, C k := fun p =>
    add_le_add (hDM _) (Finset.sum_le_sum fun k _ => hC p.1 k (p.2 k))
  have hi := integrable_exp_of_ae_le (μ := μ₀.prod (Measure.pi νs))
    hE.aemeasurable (ae_of_all _ hb)
  have hVa : ∀ a k, Measurable (V a k) := fun a k => (hV k).comp measurable_prodMk_left
  have hz (a : A) (k : K) : 0 < ∫ b, Real.exp (V a k b) ∂νs k :=
    integral_exp_pos_of_ae_le (hVa a k).aemeasurable (ae_of_all _ fun b => hC a k b)
  have hlog (a : A) :
      Real.log (∫ b : K → B, Real.exp (D a + ∑ k, V a k (b k)) ∂Measure.pi νs) =
        D a + ∑ k, Real.log (∫ b, Real.exp (V a k b) ∂νs k) := by
    simp_rw [Real.exp_add, Real.exp_sum]
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (μ := νs) (fun k b => Real.exp (V a k b)),
      Real.log_mul (Real.exp_pos _).ne' (Finset.prod_pos fun k _ => hz a k).ne', Real.log_exp,
      Real.log_prod (fun k _ => (hz a k).ne')]
  have h := integral_pi_tilted_prod_fst_of_aestronglyMeasurable (μ := μ₀)
    (ν := Measure.pi νs) (E := fun p : A × (K → B) => D p.1 + ∑ k, V p.1 k (p.2 k)) hi
    (R := R) (f := f) (by simpa only [hlog] using hf)
  simpa only [hlog] using h

/-- Integrating independent auxiliary coordinates in a finite-state Gibbs law replaces each
coordinate potential by its log exponential integral. The auxiliary laws and potentials may
vary between coordinates; only measurability and upper bounds are required. -/
theorem integral_pi_tilted_count_prod_sum {K : Type*} [Fintype K] [Finite A]
    [MeasurableSingletonClass A] (νs : K → Measure B) [∀ k, IsProbabilityMeasure (νs k)]
    (D : A → ℝ) (V : A → K → B → ℝ) (hV : ∀ a k, Measurable (V a k))
    (C : K → ℝ) (hC : ∀ a k b, V a k b ≤ C k)
    {R : Type*} [Fintype R] (f : (R → A) → ℝ) :
    (∫ x : R → A × (K → B), f (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (Measure.count.prod (Measure.pi νs)).tilted
        (fun p : A × (K → B) => D p.1 + ∑ k, V p.1 k (p.2 k)))) =
      ∫ a, f a ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => D a + ∑ k, Real.log (∫ b, Real.exp (V a k b) ∂νs k))) := by
  have := Fintype.ofFinite A
  exact integral_pi_tilted_prod_sum Measure.count νs (measurable_of_countable D)
    (M := ∑ a, |D a|) (fun a => (le_abs_self _).trans
      (Finset.single_le_sum (fun a _ => abs_nonneg (D a)) (Finset.mem_univ a)))
    (fun k => measurable_from_prod_countable_right fun a => hV a k) hC
    (measurable_of_countable f).aestronglyMeasurable

end MeasureTheory
