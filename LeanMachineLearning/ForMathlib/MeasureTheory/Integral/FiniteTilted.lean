/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exponential tilts of counting measure on a finite space

Finite Gibbs expectations, their product and fiber formulas, and measurability in
an external parameter. The statements concern Mathlib's tilted counting measure;
there is no spin model, Gaussian assumption or separate Gibbs-measure definition.
-/

@[expose] public section

open ProbabilityTheory Finset

namespace MeasureTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The counting measure on a finite type integrates a function to the sum of its values. -/
lemma integral_count_eq_sum (g : α → ℝ) : ∫ a, g a ∂Measure.count = ∑ a, g a := by
  rw [integral_fintype Integrable.of_finite]
  simp [Measure.real]

/-- The partition function is the moment-generating function of the energy for the counting
measure: `Z(β) = ∑ₐ exp (β H a)`. -/
lemma mgf_count (H : α → ℝ) (β : ℝ) :
    mgf H Measure.count β = ∑ a, Real.exp (β * H a) :=
  integral_count_eq_sum _

/-- **The Gibbs average:** the expectation of `g` under the tilt of the counting measure by `f`
is `∑ₐ (exp (f a) / ∑ᵦ exp (f b)) g(a)`.  For `f = β H` this is the Gibbs average at inverse
temperature `β`; for `f = y + h` it is the average under a random field `y` and a deterministic
bias `h`. -/
theorem integral_count_tilted (f g : α → ℝ) :
    ∫ a, g a ∂(Measure.count.tilted f) =
      ∑ a, Real.exp (f a) / (∑ b, Real.exp (f b)) * g a := by
  rw [integral_tilted, integral_count_eq_sum, integral_count_eq_sum]
  simp only [smul_eq_mul]

omit [Fintype α] [MeasurableSingletonClass α] in
/-- **Equivariance of tilted averages:** a measure preserving measurable equivalence transports
both the exponent and the observable. -/
theorem integral_tilted_comp_measurePreserving_equiv {β E : Type*} [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β)
    (he : MeasurePreserving e μ ν) (f : β → ℝ) (g : β → E) :
    ∫ b, g b ∂(ν.tilted f) = ∫ a, g (e a) ∂(μ.tilted fun a => f (e a)) := by
  have hZ : ∫ a, Real.exp (f (e a)) ∂μ = ∫ b, Real.exp (f b) ∂ν :=
    he.integral_comp' (g := fun b => Real.exp (f b))
  rw [integral_tilted, integral_tilted, hZ]
  exact (he.integral_comp' (g := fun b => (Real.exp (f b) / ∫ b, Real.exp (f b) ∂ν) • g b)).symm

omit [Fintype α] in
/-- **Equivariance of finite Gibbs averages.**  Reindexing a finite configuration space along an
equivalence transports both the energy and the observable.  This packages the algebra needed to
move a distinguished coordinate to or from a product type, without introducing a model-specific
Gibbs measure. -/
theorem integral_count_tilted_equiv {β : Type*} [Finite α] [Finite β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (e : α ≃ β) (f g : β → ℝ) :
    ∫ b, g b ∂(Measure.count.tilted f) =
      ∫ a, g (e a) ∂(Measure.count.tilted fun a => f (e a)) := by
  let ψ : α ≃ᵐ β :=
    { toEquiv := e
      measurable_toFun := measurable_of_finite _
      measurable_invFun := measurable_of_finite _ }
  have hψ : MeasurePreserving ψ Measure.count Measure.count := by
    refine ⟨ψ.measurable, Measure.ext fun s _ => ?_⟩
    rw [ψ.map_apply, ← ψ.image_symm]
    exact Measure.count_injective_image ψ.symm.injective s
  exact integral_tilted_comp_measurePreserving_equiv ψ hψ f g

/-- **Disintegrating a finite Gibbs average over a finite fibre.**  If the energy on
`α × ε` is `A a + B a e`, its Gibbs average is the quotient of the corresponding fibrewise
weighted sums.  This is deliberately stated for arbitrary finite types: a last Ising spin is
the specialization `ε = ℤˣ`, while the same identity also applies to Potts spins and finite
latent variables. -/
theorem integral_count_tilted_fiber (A : α → ℝ) {ε : Type*} [Fintype ε]
    [MeasurableSpace ε] [MeasurableSingletonClass ε] (B : α → ε → ℝ)
    (g : α → ε → ℝ) :
    ∫ x : α × ε, g x.1 x.2 ∂(Measure.count.tilted fun x => A x.1 + B x.1 x.2) =
      (∑ a, Real.exp (A a) * ∑ e, Real.exp (B a e) * g a e) /
        (∑ a, Real.exp (A a) * ∑ e, Real.exp (B a e)) := by
  rw [integral_count_tilted]
  simp only [Fintype.sum_prod_type, Real.exp_add]
  have hden :
      (∑ a, ∑ e, Real.exp (A a) * Real.exp (B a e)) =
        ∑ a, Real.exp (A a) * ∑ e, Real.exp (B a e) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
  rw [hden]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = ∑ e, (Real.exp (A a) * (Real.exp (B a e) * g a e)) *
        (∑ a, Real.exp (A a) * ∑ e, Real.exp (B a e))⁻¹ := by
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = (∑ e, Real.exp (A a) * (Real.exp (B a e) * g a e)) *
        (∑ a, Real.exp (A a) * ∑ e, Real.exp (B a e))⁻¹ := by
      rw [Finset.sum_mul]
    _ = _ := by rw [Finset.mul_sum]

/-- **Two replicas of a Gibbs measure as a double sum.**  A function of two independent replicas
integrates against the product of two Gibbs measures to the double sum with the Gibbs weights
`exp (f a) / ∑_b exp (f b)`. -/
theorem integral_pi_fin_two_count_tilted (f : α → ℝ) (Θ : α → α → ℝ) :
    ∫ σ : Fin 2 → α, Θ (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f) =
      ∑ x, ∑ y, Real.exp (f x) / (∑ b, Real.exp (f b)) *
        (Real.exp (f y) / ∑ b, Real.exp (f b)) * Θ x y := by
  rw [integral_pi_fin_two]
  simp_rw [integral_count_tilted, Finset.mul_sum, mul_assoc]

/-- **The Gibbs weight:** the tilt of the counting measure by `f` gives mass
`exp (f a) / ∑ᵦ exp (f b)` to `a`. -/
theorem real_count_tilted_singleton (f : α → ℝ) (a : α) :
    (Measure.count.tilted f).real {a} = Real.exp (f a) / ∑ b, Real.exp (f b) := by
  rw [Measure.real, tilted_apply_eq_ofReal_integral' _ (measurableSet_singleton a),
    ENNReal.toReal_ofReal (by positivity), integral_singleton]
  simp

omit [Fintype α] in
/-- **The Gibbs measure depends measurably on the disorder:** if the energies `f ω a` are
measurable in the parameter `ω` for each state `a`, then so is `ω ↦ Measure.count.tilted (f ω)`
(as a map into `Measure α`). -/
theorem measurable_count_tilted [Finite α] {Ω : Type*} [MeasurableSpace Ω] (f : Ω → α → ℝ)
    (hf : ∀ a, Measurable fun ω => f ω a) :
    Measurable fun ω => (Measure.count : Measure α).tilted (f ω) := by
  have := Fintype.ofFinite α
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [tilted_apply_eq_ofReal_integral' _ hs]
  refine ENNReal.measurable_ofReal.comp ?_
  have h : ∀ ω, ∫ a in s, Real.exp (f ω a) / ∫ x, Real.exp (f ω x) ∂Measure.count ∂Measure.count =
      ∑ a, s.indicator (fun a => Real.exp (f ω a) / ∑ b, Real.exp (f ω b)) a := fun ω => by
    rw [← integral_indicator hs, integral_count_eq_sum]
    simp_rw [integral_count_eq_sum]
  simp_rw [h]
  refine Finset.measurable_sum _ fun a _ => ?_
  by_cases ha : a ∈ s
  · simp only [ha, Set.indicator_of_mem]
    exact (Real.measurable_exp.comp (hf a)).div
      (Finset.measurable_sum _ fun b _ => Real.measurable_exp.comp (hf b))
  · simp [ha]

omit [Fintype α] in
/-- **A Gibbs average over a countable space is measurable in the parameter** if the energies and
the observables are measurable in the parameter for each state. No integrability is needed. -/
theorem measurable_integral_count_tilted_dep_of_countable [Countable α] {Ω : Type*}
    [MeasurableSpace Ω] (f : Ω → α → ℝ) (hf : ∀ a, Measurable fun ω => f ω a) (φ : Ω → α → ℝ)
    (hφ : ∀ a, Measurable fun ω => φ ω a) :
    Measurable fun ω => ∫ a, φ ω a ∂(Measure.count.tilted (f ω)) := by
  have hf' : Measurable fun z : Ω × α => f z.1 z.2 := measurable_from_prod_countable_left hf
  have hφ' : Measurable fun z : Ω × α => φ z.1 z.2 := measurable_from_prod_countable_left hφ
  have hZ : Measurable fun ω => ∫ a, Real.exp (f ω a) ∂(Measure.count : Measure α) :=
    hf'.exp.stronglyMeasurable.integral_prod_right'.measurable
  simp_rw [integral_tilted, smul_eq_mul]
  exact (((hf'.exp.div (hZ.comp measurable_fst)).mul
    hφ').stronglyMeasurable.integral_prod_right').measurable

omit [Fintype α] in
/-- **A Gibbs average of a parameter-dependent observable is measurable in the parameter:** if
the energies `f ω a` and the observables `φ ω a` are measurable in `ω` for each state `a`, so is
`ω ↦ ∫ φ ω d(count.tilted (f ω))`. -/
theorem measurable_integral_count_tilted_dep [Finite α] {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → α → ℝ) (hf : ∀ a, Measurable fun ω => f ω a) (φ : Ω → α → ℝ)
    (hφ : ∀ a, Measurable fun ω => φ ω a) :
    Measurable fun ω => ∫ a, φ ω a ∂(Measure.count.tilted (f ω)) :=
  measurable_integral_count_tilted_dep_of_countable f hf φ hφ

omit [Fintype α] in
/-- **A Gibbs average is measurable in the disorder:** if the energies `f ω a` are measurable in
`ω`, so is `ω ↦ ∫ φ d(count.tilted (f ω))` for every observable `φ`. -/
theorem measurable_integral_count_tilted [Finite α] {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → α → ℝ) (hf : ∀ a, Measurable fun ω => f ω a) (φ : α → ℝ) :
    Measurable fun ω => ∫ a, φ a ∂(Measure.count.tilted (f ω)) :=
  measurable_integral_count_tilted_dep f hf (fun _ => φ) fun _ => measurable_const

omit [Fintype α] in
instance [Finite α] [Nonempty α] (f : α → ℝ) : IsProbabilityMeasure (Measure.count.tilted f) :=
  isProbabilityMeasure_tilted Integrable.of_finite

omit [MeasurableSingletonClass α] in
/-- The average of a vector-valued `g` over a probability measure on a finite space is at most
`∑ₐ ‖g a‖` in norm. -/
theorem norm_integral_le_sum_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → E) :
    ‖∫ a, g a ∂μ‖ ≤ ∑ a, ‖g a‖ := by
  refine (norm_integral_le_of_norm_le_const (C := ∑ a, ‖g a‖) (ae_of_all _ fun a => ?_)).trans ?_
  · exact Finset.single_le_sum (f := fun b => ‖g b‖) (fun _ _ => norm_nonneg _) (mem_univ a)
  · simp

/-- The Gibbs average of `g` is at most `∑ₐ |g a|` in absolute value. -/
theorem norm_integral_count_tilted_le [Nonempty α] (f g : α → ℝ) :
    ‖∫ a, g a ∂(Measure.count.tilted f)‖ ≤ ∑ a, |g a| := by
  simpa only [Real.norm_eq_abs] using norm_integral_le_sum_norm (Measure.count.tilted f) g

end MeasureTheory
