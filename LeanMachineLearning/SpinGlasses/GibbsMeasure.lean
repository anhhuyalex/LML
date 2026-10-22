/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Units
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import LeanMachineLearning.SpinGlasses.FreeEnergy
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Gibbs measure

The Gibbs measure of an energy `H : α → ℝ` on a finite configuration space at inverse temperature
`β` is `G(a) = exp (β H(a)) / Z(β)` with `Z(β) = ∑ₐ exp (β H(a))` ([Panchenko, 2013, Eq. (1.11)]).
It is the exponential tilt of the counting measure,
`MeasureTheory.Measure.count.tilted (fun a => β * H a)`, so no definition is introduced: everything
below is a statement about this Mathlib object, and it inherits the whole tilted-measure and
cumulant-generating-function API.  In particular, the log-partition function is the
cumulant-generating function of `H` for the counting measure,
`log Z(β) = ProbabilityTheory.cgf H count β`, so its derivative in `β` is the Gibbs average of `H`
by `ProbabilityTheory.integral_tilted_mul_self`.

## Main declarations

* `SpinGlasses.integral_count_tilted`, `SpinGlasses.real_count_tilted_singleton`: the Gibbs average
  `⟨g⟩ = ∑ₐ G(a) g(a)` and the Gibbs weight `G(a) = exp (β H a) / Z(β)`.
* `SpinGlasses.hasDerivAt_log_sum_exp`: `(d/dβ) log Z(β) = ⟨H⟩`.
* `SpinGlasses.hasDerivAt_integral_log_sum_exp`: for a random energy with integrable coordinates,
  `(d/dβ) 𝔼 log Z(β) = 𝔼 ⟨H⟩` for `β > 0`, by dominated differentiation under the integral.
* `SpinGlasses.tendsto_real_count_tilted_singleton_of_lt`: at zero temperature, the Gibbs weight of
  every non-ground state tends to `0`.
* `SpinGlasses.tendsto_integral_count_tilted_max`: the Gibbs average of `H` tends to `max H`.
* `SpinGlasses.sk_hasDerivAt_free_energy`: the SK instance, `(d/dβ) F_N(β) = N⁻¹ 𝔼 ⟨H_N⟩`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Matrix Topology

namespace SpinGlasses

section Gibbs

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

omit [Fintype α] in
/-- **Equivariance of finite Gibbs averages.**  Reindexing a finite configuration space along an
equivalence transports both the energy and the observable.  This packages the algebra needed to
move a distinguished coordinate to or from a product type, without introducing a model-specific
Gibbs measure. -/
theorem integral_count_tilted_equiv {β : Type*} [Finite α] [Finite β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (e : α ≃ β) (f g : β → ℝ) :
    ∫ b, g b ∂(Measure.count.tilted f) =
      ∫ a, g (e a) ∂(Measure.count.tilted fun a => f (e a)) := by
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  rw [integral_count_tilted, integral_count_tilted]
  have hZ : (∑ b : β, Real.exp (f b)) = ∑ a : α, Real.exp (f (e a)) :=
    (e.sum_comp fun b => Real.exp (f b)).symm
  rw [hZ]
  exact (e.sum_comp fun b => Real.exp (f b) / (∑ a : α, Real.exp (f (e a))) * g b).symm

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
  classical
  rw [← integral_indicator_one (measurableSet_singleton a), integral_count_tilted]
  simp [Set.indicator_apply]

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
instance [Finite α] [Nonempty α] (f : α → ℝ) : IsProbabilityMeasure (Measure.count.tilted f) :=
  isProbabilityMeasure_tilted Integrable.of_finite

/-- The Gibbs average of `g` is at most `∑ₐ |g a|` in absolute value. -/
theorem norm_integral_count_tilted_le [Nonempty α] (f g : α → ℝ) :
    ‖∫ a, g a ∂(Measure.count.tilted f)‖ ≤ ∑ a, |g a| := by
  refine (norm_integral_le_of_norm_le_const (C := ∑ a, |g a|) (ae_of_all _ fun a => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun b => |g b|) (fun _ _ => abs_nonneg _) (mem_univ a)
  · simp

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A weighted partition sum with positive weights is positive. -/
theorem sum_exp_mul_pos [Nonempty α] (f F : α → ℝ) (hF : ∀ a, 0 < F a) :
    0 < ∑ a, Real.exp (f a) * F a :=
  Finset.sum_pos (fun a _ => mul_pos (Real.exp_pos _) (hF a)) Finset.univ_nonempty

/-- **Logarithm of a Gibbs average:** for a positive observable `F`,
`log ⟨F⟩ = log ∑ₐ exp (f a) F(a) - log ∑ₐ exp (f a)`, i.e. the normalization `Z = ∑ₐ exp (f a)`
splits off.  This is what makes the partition function cancel in differences of log-averages. -/
theorem log_integral_count_tilted [Nonempty α] (f F : α → ℝ) (hF : ∀ a, 0 < F a) :
    Real.log (∫ a, F a ∂(Measure.count.tilted f)) =
      Real.log (∑ a, Real.exp (f a) * F a) - Real.log (∑ a, Real.exp (f a)) := by
  have hZ : 0 < ∑ a, Real.exp (f a) := by
    simpa using sum_exp_mul_pos f (fun _ => 1) fun _ => one_pos
  have hZF := sum_exp_mul_pos f F hF
  rw [integral_count_tilted, ← Real.log_div hZF.ne' hZ.ne', Finset.sum_div]
  simp_rw [div_mul_eq_mul_div]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Model-independent single-spin summation: summing out an Ising sign
`ε ∈ ℤˣ` against an arbitrary base weight `A` and field `L`. -/
theorem sum_exp_prod_units (A L : α → ℝ) :
    (∑ x : α × ℤˣ, Real.exp (A x.1 + (x.2 : ℝ) * L x.1)) =
      2 * ∑ a : α, Real.exp (A a) * Real.cosh (L a) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Real.exp_add, sum_units_int]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [show (fun a : α => Real.exp (A a) * Real.exp (L a) + Real.exp (A a) * Real.exp (-L a)) =
      fun a => 2 * (Real.exp (A a) * Real.cosh (L a)) by
        funext a; rw [Real.cosh_eq]; ring]
  rw [← Finset.mul_sum]

/-- **Model-independent logarithmic single-spin identity.**  Taking the logarithm after
summing an Ising sign separates the base log partition function from the logarithm of the
base Gibbs average of `cosh L`. -/
theorem log_sum_exp_prod_units [Nonempty α] (A L : α → ℝ) :
    Real.log (∑ x : α × ℤˣ, Real.exp (A x.1 + (x.2 : ℝ) * L x.1)) =
      Real.log 2 + Real.log (∑ a : α, Real.exp (A a)) +
        Real.log (∫ a : α, Real.cosh (L a) ∂Measure.count.tilted A) := by
  rw [sum_exp_prod_units, Real.log_mul two_ne_zero
    (sum_exp_mul_pos A _ fun a => Real.cosh_pos (L a)).ne',
    log_integral_count_tilted A _ fun a => Real.cosh_pos (L a)]
  ring

/-- The logarithm of a Gibbs average of `cosh` is a signed log partition function minus the
base log partition function and `log 2`.  This form is suited to direct reuse of Gaussian
log-partition interpolation. -/
theorem log_integral_cosh_count_tilted_eq [Nonempty α] (A L : α → ℝ) :
    Real.log (∫ a : α, Real.cosh (L a) ∂Measure.count.tilted A) =
      Real.log (∑ x : α × ℤˣ, Real.exp (A x.1 + (x.2 : ℝ) * L x.1)) -
        Real.log 2 - Real.log (∑ a : α, Real.exp (A a)) := by
  rw [log_sum_exp_prod_units]
  ring

/-- Summing an Ising sign weighted by `(s : ℝ) * exp (s * x)` yields `2 * sinh x`. -/
theorem sum_units_int_mul_exp (x : ℝ) :
    (∑ s : ℤˣ, (s : ℝ) * Real.exp ((s : ℝ) * x)) = 2 * Real.sinh x := by
  rw [sum_units_int]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [Real.sinh_eq]
  ring

/-- Summing two independent Ising signs against `exp(s * x + t * y) * (s * t)` yields
`4 * sinh x * sinh y`. -/
theorem sum_units_int_prod_mul_exp (x y : ℝ) :
    (∑ s : ℤˣ, ∑ t : ℤˣ, Real.exp ((s : ℝ) * x) * Real.exp ((t : ℝ) * y) *
      ((s : ℝ) * (t : ℝ))) = 4 * Real.sinh x * Real.sinh y := by
  have h1 : (fun s : ℤˣ => ∑ t : ℤˣ, Real.exp ((s : ℝ) * x) * Real.exp ((t : ℝ) * y) *
      ((s : ℝ) * (t : ℝ))) =
      fun s : ℤˣ => ((s : ℝ) * Real.exp ((s : ℝ) * x)) *
        ∑ t : ℤˣ, (t : ℝ) * Real.exp ((t : ℝ) * y) := by
    funext s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [h1, sum_units_int_mul_exp y, ← Finset.sum_mul, sum_units_int_mul_exp x]
  ring

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Summing two replica Ising signs on `α × ℤˣ` factors into a product of `sinh` terms. -/
theorem sum_exp_prod_units_mul_two_replicas (A L : α → ℝ) (g : α → α → ℝ) :
    (∑ x : α × ℤˣ, ∑ y : α × ℤˣ,
      Real.exp (A x.1 + (x.2 : ℝ) * L x.1) * Real.exp (A y.1 + (y.2 : ℝ) * L y.1) *
        ((x.2 : ℝ) * (y.2 : ℝ) * g x.1 y.1)) =
    4 * ∑ a : α, ∑ b : α, Real.exp (A a) * Real.exp (A b) * g a b *
      Real.sinh (L a) * Real.sinh (L b) := by
  simp_rw [Fintype.sum_prod_type]
  have h_comm :
      (∑ a : α, ∑ s : ℤˣ, ∑ b : α, ∑ t : ℤˣ,
        Real.exp (A a + (s : ℝ) * L a) * Real.exp (A b + (t : ℝ) * L b) *
          ((s : ℝ) * (t : ℝ) * g a b)) =
      ∑ a : α, ∑ b : α, ∑ s : ℤˣ, ∑ t : ℤˣ,
        Real.exp (A a + (s : ℝ) * L a) * Real.exp (A b + (t : ℝ) * L b) *
          ((s : ℝ) * (t : ℝ) * g a b) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  rw [h_comm]
  have h_eval (a b : α) :
      (∑ s : ℤˣ, ∑ t : ℤˣ,
        Real.exp (A a + (s : ℝ) * L a) * Real.exp (A b + (t : ℝ) * L b) *
          ((s : ℝ) * (t : ℝ) * g a b)) =
      4 * (Real.exp (A a) * Real.exp (A b) * g a b * Real.sinh (L a) * Real.sinh (L b)) := by
    have he : (∑ s : ℤˣ, ∑ t : ℤˣ,
        Real.exp (A a + (s : ℝ) * L a) * Real.exp (A b + (t : ℝ) * L b) *
          ((s : ℝ) * (t : ℝ) * g a b)) =
        (Real.exp (A a) * Real.exp (A b) * g a b) *
          ∑ s : ℤˣ, ∑ t : ℤˣ, Real.exp ((s : ℝ) * L a) * Real.exp ((t : ℝ) * L b) *
            ((s : ℝ) * (t : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [Real.exp_add]
      ring
    rw [he, sum_units_int_prod_mul_exp]
    ring
  simp_rw [h_eval, ← Finset.mul_sum]

/-- The integral of an observable against the product of two tilted counting measures
equals the double sum weighted by the normalized Gibbs weights. -/
theorem integral_prod_count_tilted (f : α → ℝ) (Θ : α → α → ℝ) :
    ∫ p : α × α, Θ p.1 p.2 ∂((Measure.count.tilted f).prod (Measure.count.tilted f)) =
      ∑ a, ∑ b, Real.exp (f a) / (∑ c, Real.exp (f c)) *
        (Real.exp (f b) / ∑ c, Real.exp (f c)) * Θ a b := by
  have hi : Integrable (fun p : α × α => Θ p.1 p.2)
      ((Measure.count.tilted f).prod (Measure.count.tilted f)) :=
    Integrable.of_finite
  rw [integral_prod _ hi]
  simp_rw [integral_count_tilted, Finset.mul_sum, mul_assoc]

/-- Double sum expansion of the product of two tilted counting measures with explicit partition
prefactor. -/
theorem integral_prod_count_tilted_eq_double_sum (f : α → ℝ) (Θ : α → α → ℝ) :
    ∫ p : α × α, Θ p.1 p.2 ∂((Measure.count.tilted f).prod (Measure.count.tilted f)) =
      (∑ a, Real.exp (f a))⁻¹ ^ 2 *
        ∑ a, ∑ b, Real.exp (f a) * Real.exp (f b) * Θ a b := by
  rw [integral_prod_count_tilted]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Multiplying a tilted counting expectation by the partition function recovers the
unnormalized weighted sum. -/
theorem mul_integral_count_tilted [Nonempty α] (f g : α → ℝ) :
    (∑ c, Real.exp (f c)) * ∫ a, g a ∂(Measure.count.tilted f) =
      ∑ a, Real.exp (f a) * g a := by
  have hZ : 0 < ∑ c, Real.exp (f c) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [integral_count_tilted, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_assoc, mul_div_cancel₀ _ hZ.ne']

omit [Fintype α] in
/-- **Two-replica sign integration for tilted measures (Talagrand Eq. 1.178 for cosh).**
Integrating `ε¹ ε² g(ρ¹, ρ²)` under the product of the signed tilted measures gives the
quotient of the two-replica average of `g sinh sinh` by `⟨cosh L⟩²`. -/
theorem integral_prod_count_tilted_units_mul [Finite α] [Nonempty α] (A L : α → ℝ)
    (g : α → α → ℝ) :
    ∫ p : (α × ℤˣ) × (α × ℤˣ), (p.1.2 : ℝ) * (p.2.2 : ℝ) * g p.1.1 p.2.1
      ∂((Measure.count.tilted fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1).prod
        (Measure.count.tilted fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1)) =
    (∫ p : α × α, g p.1 p.2 * Real.sinh (L p.1) * Real.sinh (L p.2)
      ∂((Measure.count.tilted A).prod (Measure.count.tilted A))) /
      (∫ a, Real.cosh (L a) ∂(Measure.count.tilted A)) ^ 2 := by
  let _ := Fintype.ofFinite α
  let At := fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1
  let ZA := ∑ a : α, Real.exp (A a)
  have hZt : (∑ x : α × ℤˣ, Real.exp (At x)) =
      2 * (ZA * ∫ a, Real.cosh (L a) ∂(Measure.count.tilted A)) := by
    rw [sum_exp_prod_units, mul_integral_count_tilted]
  have h_lhs := integral_prod_count_tilted_eq_double_sum (f := At)
    (Θ := fun x y => (x.2 : ℝ) * (y.2 : ℝ) * g x.1 y.1)
  have h_rhs := integral_prod_count_tilted_eq_double_sum (f := A)
    (Θ := fun a b => g a b * Real.sinh (L a) * Real.sinh (L b))
  have h_num := sum_exp_prod_units_mul_two_replicas A L g
  rw [h_lhs, hZt, h_num, h_rhs]
  have hS : (∑ a, ∑ b, Real.exp (A a) * Real.exp (A b) * g a b * Real.sinh (L a) *
      Real.sinh (L b)) = ∑ a, ∑ b, Real.exp (A a) * Real.exp (A b) *
        (g a b * Real.sinh (L a) * Real.sinh (L b)) := by
    simp_rw [mul_assoc]
  rw [hS, div_eq_mul_inv, inv_pow]
  dsimp only [ZA]
  ring

omit [Fintype α] in
/-- **Pointwise bound on the two-replica signed tilted average.**  Since `⟨cosh L⟩ ≥ 1`, the
denominator in `integral_prod_count_tilted_units_mul` is at least `1`, so the average is
dominated by the numerator alone. -/
theorem abs_integral_prod_count_tilted_units_mul_le [Finite α] [Nonempty α] (A L : α → ℝ)
    (g : α → α → ℝ) :
    |∫ p : (α × ℤˣ) × (α × ℤˣ), (p.1.2 : ℝ) * (p.2.2 : ℝ) * g p.1.1 p.2.1
      ∂((Measure.count.tilted fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1).prod
        (Measure.count.tilted fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1))| ≤
    ∫ p : α × α, |g p.1 p.2| * |Real.sinh (L p.1)| * |Real.sinh (L p.2)|
      ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) := by
  let _ := Fintype.ofFinite α
  rw [integral_prod_count_tilted_units_mul]
  rw [abs_div, abs_pow]
  have hcosh : 1 ≤ ∫ a, Real.cosh (L a) ∂Measure.count.tilted A := by
    have h1 : (1 : ℝ) = ∫ _ : α, (1 : ℝ) ∂Measure.count.tilted A := by
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [h1]
    exact integral_mono (integrable_const _) Integrable.of_finite fun a => Real.one_le_cosh (L a)
  have hden : 1 ≤ |∫ a, Real.cosh (L a) ∂Measure.count.tilted A| ^ 2 := by
    have : 1 ≤ |∫ a, Real.cosh (L a) ∂Measure.count.tilted A| := by
      rwa [abs_of_nonneg (by linarith)]
    nlinarith
  have hnum : |∫ p : α × α, g p.1 p.2 * Real.sinh (L p.1) * Real.sinh (L p.2)
      ∂(Measure.count.tilted A).prod (Measure.count.tilted A)| ≤
      ∫ p : α × α, |g p.1 p.2| * |Real.sinh (L p.1)| * |Real.sinh (L p.2)|
        ∂(Measure.count.tilted A).prod (Measure.count.tilted A) := by
    refine abs_integral_le_integral_abs.trans ?_
    refine integral_mono Integrable.of_finite Integrable.of_finite fun p => ?_
    simp only [abs_mul]
    exact le_rfl
  have hnum_nonneg : 0 ≤ ∫ p : α × α, |g p.1 p.2| * |Real.sinh (L p.1)| * |Real.sinh (L p.2)|
      ∂(Measure.count.tilted A).prod (Measure.count.tilted A) :=
    integral_nonneg fun p => by positivity
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans (div_le_self hnum_nonneg hden)

omit [Fintype α] in
/-- Integrability of a finite two-replica Gibbs average follows coordinatewise.  This is the
finite-measure side condition used before exchanging a disorder integral with the Gibbs sum. -/
theorem integrable_integral_prod_count_tilted {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [Finite α] (A : α → ℝ) (Θ : α → α → Ω → ℝ)
    (h_int : ∀ a b, Integrable (Θ a b) P) :
    Integrable (fun ω => ∫ p : α × α, Θ p.1 p.2 ω
      ∂((Measure.count.tilted A).prod (Measure.count.tilted A))) P := by
  let _ := Fintype.ofFinite α
  have h_exp (ω : Ω) :
      (∫ p : α × α, Θ p.1 p.2 ω ∂((Measure.count.tilted A).prod
        (Measure.count.tilted A))) =
      (∑ a, Real.exp (A a))⁻¹ ^ 2 *
        ∑ a, ∑ b, Real.exp (A a) * Real.exp (A b) * Θ a b ω :=
    integral_prod_count_tilted_eq_double_sum A (fun a b => Θ a b ω)
  simp_rw [h_exp]
  refine (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_).const_mul _
  exact (h_int a b).const_mul _

omit [Fintype α] in
/-- **Exchange of disorder integral with two-replica tilted measure.**  Because the two-replica
tilted measure on a finite type has weights independent of `ω`, integrating an observable
against the two-replica measure and then over `ω` equals integrating over `ω` coordinatewise
and then against the two-replica measure. -/
theorem integral_prod_count_tilted_swap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [Finite α] (A : α → ℝ) (Θ : α → α → Ω → ℝ)
    (h_int : ∀ a b, Integrable (Θ a b) P) :
    (∫ ω, ∫ p : α × α, Θ p.1 p.2 ω
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) ∂P) =
      ∫ p : α × α, (∫ ω, Θ p.1 p.2 ω ∂P)
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) := by
  let _ := Fintype.ofFinite α
  have h_exp (ω : Ω) :
      (∫ p : α × α, Θ p.1 p.2 ω ∂((Measure.count.tilted A).prod (Measure.count.tilted A))) =
      (∑ a, Real.exp (A a))⁻¹ ^ 2 *
        ∑ a, ∑ b, Real.exp (A a) * Real.exp (A b) * Θ a b ω :=
    integral_prod_count_tilted_eq_double_sum A (fun a b => Θ a b ω)
  simp_rw [h_exp]
  rw [integral_const_mul]
  rw [integral_prod_count_tilted_eq_double_sum A (fun a b => ∫ ω, Θ a b ω ∂P)]
  congr 1
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b _
      rw [integral_const_mul]
    · intro b _
      exact (h_int a b).const_mul _
  · intro a _
    refine integrable_finsetSum _ fun b _ => ?_
    exact (h_int a b).const_mul _

omit [Fintype α] in
/-- **Averaged two-replica bound under coordinatewise disorder domination.**  If `F a b ω` has
expectation bounded by `C` for all `a, b`, then the disorder average of `∫ |g| F` under the
two-replica tilted measure is bounded by `C * ∫ |g|`. -/
theorem integral_prod_count_tilted_mul_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [Finite α] (A : α → ℝ) (g : α → α → ℝ) (F : α → α → Ω → ℝ) (C : ℝ)
    (hF_int : ∀ a b, Integrable (F a b) P)
    (hF_le : ∀ a b, (∫ ω, F a b ω ∂P) ≤ C) :
    (∫ ω, ∫ p : α × α, |g p.1 p.2| * F p.1 p.2 ω
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) ∂P) ≤
      C * ∫ p : α × α, |g p.1 p.2|
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) := by
  let _ := Fintype.ofFinite α
  have h_int : ∀ a b, Integrable (fun ω => |g a b| * F a b ω) P := fun a b =>
    (hF_int a b).const_mul (|g a b|)
  rw [integral_prod_count_tilted_swap P A (fun a b ω => |g a b| * F a b ω) h_int]
  simp_rw [integral_const_mul]
  rw [← integral_const_mul]
  refine integral_mono Integrable.of_finite Integrable.of_finite fun p => ?_
  calc |g p.1 p.2| * ∫ ω, F p.1 p.2 ω ∂P
    _ ≤ |g p.1 p.2| * C := mul_le_mul_of_nonneg_left (hF_le p.1 p.2) (abs_nonneg _)
    _ = C * |g p.1 p.2| := mul_comm _ _

omit [Fintype α] in
/-- Measurability of an observable integrated against the product of two tilted measures. -/
theorem measurable_integral_prod_count_tilted {W : Type*} [MeasurableSpace W]
    [Finite α] {g : W → α → ℝ} (hg : ∀ a, Measurable fun w => g w a)
    {Θ : W → α → α → ℝ} (hΘ : ∀ a b, Measurable fun w => Θ w a b) :
    Measurable fun w => ∫ p : α × α, Θ w p.1 p.2
      ∂((Measure.count.tilted (g w)).prod (Measure.count.tilted (g w))) := by
  let _ := Fintype.ofFinite α
  simp_rw [integral_prod_count_tilted]
  refine Finset.measurable_fun_sum _ fun a _ =>
    Finset.measurable_fun_sum _ fun b _ => ?_
  exact (((hg a).exp.div (Finset.measurable_fun_sum _ fun c _ => (hg c).exp)).mul
    ((hg b).exp.div (Finset.measurable_fun_sum _ fun c _ => (hg c).exp))).mul (hΘ a b)

omit [Fintype α] in
/-- Measurability of the signed two-replica average used in cavity `cosh` interpolations. -/
theorem measurable_integral_prod_count_tilted_units_mul [Finite α]
    {W : Type*} [MeasurableSpace W] {A L : W → α → ℝ}
    (hA : ∀ a, Measurable fun w => A w a) (hL : ∀ a, Measurable fun w => L w a)
    (g : α → α → ℝ) :
    Measurable fun w => ∫ p : (α × ℤˣ) × (α × ℤˣ),
      (p.1.2 : ℝ) * (p.2.2 : ℝ) * g p.1.1 p.2.1
      ∂((Measure.count.tilted fun x => A w x.1 + (x.2 : ℝ) * L w x.1).prod
        (Measure.count.tilted fun x => A w x.1 + (x.2 : ℝ) * L w x.1)) := by
  let At : W → α × ℤˣ → ℝ := fun w x => A w x.1 + (x.2 : ℝ) * L w x.1
  let Θ : W → α × ℤˣ → α × ℤˣ → ℝ := fun _ x y =>
    (x.2 : ℝ) * (y.2 : ℝ) * g x.1 y.1
  have hAt : ∀ x, Measurable fun w => At w x := fun x =>
    (hA x.1).add (measurable_const.mul (hL x.1))
  have hΘ : ∀ x y, Measurable fun w => Θ w x y := by
    intro x y
    exact measurable_const
  have hm := measurable_integral_prod_count_tilted (g := At) (Θ := Θ) hAt hΘ
  simpa only [At, Θ] using hm

omit [Fintype α] in
/-- The log Gibbs average of `cosh` of a field is measurable in any parameter on which the base
energy `A` and the field `L` depend measurably. -/
theorem measurable_log_integral_cosh_count_tilted [Finite α] [Nonempty α] {W : Type*}
    [MeasurableSpace W] {A L : W → α → ℝ} (hA : ∀ a, Measurable fun w => A w a)
    (hL : ∀ a, Measurable fun w => L w a) :
    Measurable fun w => Real.log (∫ a, Real.cosh (L w a) ∂Measure.count.tilted (A w)) := by
  have := Fintype.ofFinite α
  simp_rw [log_integral_cosh_count_tilted_eq]
  refine ((Measurable.log (Finset.measurable_sum _ fun x _ =>
    ((hA x.1).add (measurable_const.mul (hL x.1))).exp)).sub measurable_const).sub
    (Measurable.log (Finset.measurable_sum _ fun a _ => (hA a).exp))

/-- **Log-partition perturbation identity.**  Adding an arbitrary finite perturbation `V` to
an energy `f` changes its log partition function by the logarithm of the Gibbs average of
`exp V`.  This is the algebraic form used whenever an independent Gaussian perturbation is
separated from a base Hamiltonian. -/
theorem log_sum_exp_add_eq_log_sum_exp_add_log_integral_exp [Nonempty α]
    (f V : α → ℝ) :
    Real.log (∑ a, Real.exp (f a + V a)) =
      Real.log (∑ a, Real.exp (f a)) +
        Real.log (∫ a, Real.exp (V a) ∂Measure.count.tilted f) := by
  have h := log_integral_count_tilted f (fun a => Real.exp (V a)) fun a => Real.exp_pos _
  simp_rw [Real.exp_add]
  linarith

/-- **Temperature derivative of the log-partition function:**
`(d/dβ) log Z(β) = ⟨H⟩_β`, the Gibbs average of the energy.  This is
`ProbabilityTheory.integral_tilted_mul_self`, since `log Z = cgf H count`. -/
theorem hasDerivAt_log_sum_exp (H : α → ℝ) (β : ℝ) :
    HasDerivAt (fun b => Real.log (∑ a, Real.exp (b * H a)))
      (∫ a, H a ∂(Measure.count.tilted fun a => β * H a)) β := by
  have hβ : β ∈ interior (integrableExpSet H (Measure.count : Measure α)) := by
    rw [show integrableExpSet H (Measure.count : Measure α) = Set.univ from
      Set.eq_univ_of_forall fun t => Integrable.of_finite, interior_univ]
    trivial
  have hcgf : cgf H (Measure.count : Measure α) = fun b => Real.log (∑ a, Real.exp (b * H a)) :=
    funext fun b => by rw [cgf, mgf_count]
  rw [← hcgf, integral_tilted_mul_self hβ]
  exact (analyticAt_cgf hβ).differentiableAt.hasDerivAt

section ZeroTemperature

variable [Nonempty α]

/-- **Zero-temperature concentration:** the Gibbs weight of a configuration which is not a ground
state tends to `0` as `β → ∞`, since it is at most `exp (-β (max H - H a))`. -/
theorem tendsto_real_count_tilted_singleton_of_lt (H : α → ℝ) {a : α} (ha : H a < H.max) :
    Tendsto (fun β => (Measure.count.tilted fun a => β * H a).real {a}) atTop (𝓝 0) := by
  have hd : 0 < H.max - H a := sub_pos.2 ha
  have hlim : Tendsto (fun β : ℝ => Real.exp (-(β * (H.max - H a)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hd)
  obtain ⟨b, hb⟩ := exists_argmax H
  refine squeeze_zero (fun β => ?_) (fun β => ?_) hlim
  · rw [real_count_tilted_singleton]
    exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  · have hZ : 0 < ∑ c, Real.exp (β * H c) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
    have hZb : Real.exp (β * H.max) ≤ ∑ c, Real.exp (β * H c) := by
      rw [← hb]
      exact Finset.single_le_sum (f := fun c => Real.exp (β * H c))
        (fun _ _ => (Real.exp_pos _).le) (mem_univ b)
    rw [real_count_tilted_singleton, div_le_iff₀ hZ]
    calc Real.exp (β * H a) = Real.exp (-(β * (H.max - H a))) * Real.exp (β * H.max) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZb (Real.exp_pos _).le

/-- **The Gibbs average of the energy tends to the ground-state energy** as `β → ∞`, since
`max H - ⟨H⟩_β = ∑ₐ G(a) (max H - H a)` and each non-ground state has vanishing weight. -/
theorem tendsto_integral_count_tilted_max (H : α → ℝ) :
    Tendsto (fun β => ∫ a, H a ∂(Measure.count.tilted fun a => β * H a)) atTop (𝓝 H.max) := by
  have key : ∀ β : ℝ, ∫ a, H a ∂(Measure.count.tilted fun a => β * H a) =
      H.max - ∑ a, (Measure.count.tilted fun a => β * H a).real {a} * (H.max - H a) := by
    intro β
    have hZ : 0 < ∑ c, Real.exp (β * H c) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
    simp only [real_count_tilted_singleton, mul_sub, sum_sub_distrib, ← sum_mul, ← sum_div,
      div_self hZ.ne', one_mul, integral_count_tilted]
    ring
  have hzero : Tendsto (fun β : ℝ => ∑ a, (Measure.count.tilted fun a => β * H a).real {a} *
      (H.max - H a)) atTop (𝓝 0) := by
    have hterm : ∀ a, Tendsto (fun β : ℝ => (Measure.count.tilted fun a => β * H a).real {a} *
        (H.max - H a)) atTop (𝓝 0) := fun a => by
      by_cases h : H a < H.max
      · simpa using (tendsto_real_count_tilted_singleton_of_lt H h).mul_const (H.max - H a)
      · have : H a = H.max := le_antisymm (H.le_max a) (not_lt.1 h)
        simp [this]
    simpa using tendsto_finsetSum univ fun a _ => hterm a
  simpa [key] using tendsto_const_nhds.sub hzero

end ZeroTemperature

end Gibbs

section Path

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Derivative of the log-partition function along a path of energies:** if each `f s a` has
derivative `f' a` at `t`, then `(d/ds) log ∑ₐ exp (f s a) = ⟨f'⟩` at `s = t`, where `⟨·⟩` is the
Gibbs average of the energy `f t`.  The case `f s a = s H a` is `hasDerivAt_log_sum_exp`. -/
theorem hasDerivAt_log_sum_exp_path {f : ℝ → α → ℝ} {f' : α → ℝ} {t : ℝ}
    (hf : ∀ a, HasDerivAt (fun s => f s a) (f' a) t) :
    HasDerivAt (fun s => Real.log (∑ a, Real.exp (f s a)))
      (∫ a, f' a ∂(Measure.count.tilted fun a => f t a)) t := by
  have hS : HasDerivAt (fun s => ∑ a, Real.exp (f s a)) (∑ a, Real.exp (f t a) * f' a) t :=
    HasDerivAt.fun_sum fun a _ => (hf a).exp
  have hpos : 0 < ∑ a, Real.exp (f t a) :=
    Finset.sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
  convert hS.log hpos.ne' using 1
  rw [integral_count_tilted, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ => by ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f f' : ℝ → Ω → α → ℝ} {t : ℝ}
  {S : Set ℝ} {B : Ω → ℝ}

/-- **Derivative of the expected log-partition function along a path of random energies**, by
dominated differentiation under the integral: if the energies `f s ω a` are differentiable in `s`
on a neighbourhood `S` of `t` with derivative `f' s ω a` bounded by an integrable `B ω`, then
`(d/ds) 𝔼 log ∑ₐ exp (f s a) = 𝔼 ⟨f'⟩` at `s = t`.  This is the common core of the temperature
derivative `hasDerivAt_integral_log_sum_exp` and of Gaussian interpolation. -/
theorem hasDerivAt_integral_log_sum_exp_path (hS : S ∈ 𝓝 t)
    (hmeas : ∀ s a, AEMeasurable (fun ω => f s ω a) μ)
    (hmeas' : ∀ a, AEMeasurable (fun ω => f' t ω a) μ)
    (hint : Integrable (fun ω => Real.log (∑ a, Real.exp (f t ω a))) μ)
    (hderiv : ∀ ω, ∀ s ∈ S, ∀ a, HasDerivAt (fun s => f s ω a) (f' s ω a) s)
    (hB : Integrable B μ) (hbound : ∀ ω, ∀ s ∈ S, ∀ a, |f' s ω a| ≤ B ω) :
    HasDerivAt (fun s => ∫ ω, Real.log (∑ a, Real.exp (f s ω a)) ∂μ)
      (∫ ω, ∫ a, f' t ω a ∂(Measure.count.tilted fun a => f t ω a) ∂μ) t := by
  have hF' : AEMeasurable (fun ω => ∫ a, f' t ω a ∂(Measure.count.tilted fun a => f t ω a)) μ := by
    simp_rw [integral_count_tilted]
    exact Finset.aemeasurable_fun_sum _ fun a _ =>
      (((hmeas t a).exp).div (Finset.aemeasurable_fun_sum _ fun c _ => (hmeas t c).exp)).mul
        (hmeas' a)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun s =>
      (Real.measurable_log.comp_aemeasurable
        (Finset.aemeasurable_fun_sum _ fun a _ => (hmeas s a).exp)).aestronglyMeasurable)
    hint (F' := fun s ω => ∫ a, f' s ω a ∂(Measure.count.tilted fun a => f s ω a))
    hF'.aestronglyMeasurable
    (bound := B) (ae_of_all _ fun ω s hs => by
      have := norm_integral_le_of_norm_le_const
        (μ := Measure.count.tilted fun a => f s ω a) (f := fun a => f' s ω a) (C := B ω)
        (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hbound ω s hs a)
      simpa using this)
    hB (ae_of_all _ fun ω s hs => hasDerivAt_log_sum_exp_path (hderiv ω s hs))).2

end Path

section GibbsWeight

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Gibbs weights lie in `[0, 1]`. -/
theorem gibbsWeight_mem_Icc (w h : α → ℝ) (b : α) :
    Real.exp (w b + h b) / ∑ a, Real.exp (w a + h a) ∈ Set.Icc (0 : ℝ) 1 := by
  have hZ : 0 < ∑ a, Real.exp (w a + h a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  refine ⟨(div_pos (Real.exp_pos _) hZ).le, ?_⟩
  rw [div_le_one hZ]
  exact Finset.single_le_sum (f := fun a => Real.exp (w a + h a)) (fun _ _ => (Real.exp_pos _).le)
    (Finset.mem_univ b)

/-- Gibbs weights sum to one. -/
theorem sum_gibbsWeight (w h : α → ℝ) :
    ∑ b, Real.exp (w b + h b) / ∑ a, Real.exp (w a + h a) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-- A Gibbs average of a bounded function over two independent Gibbs measures is bounded:
`∑ₓ ∑ᵧ pₓ qᵧ C(x, y) ≤ a` when `C ≤ a` and `|∑ₓ ∑ᵧ pₓ qᵧ C(x, y)| ≤ ∑ₓ ∑ᵧ |C(x, y)|`. -/
theorem sum_sum_gibbsWeight_mul_le (w v h : α → ℝ) {C : α → α → ℝ} {a : ℝ}
    (ha : ∀ x y, C x y ≤ a) :
    ∑ x, ∑ y, Real.exp (w x + h x) / (∑ c, Real.exp (w c + h c)) *
      (Real.exp (v y + h y) / ∑ c, Real.exp (v c + h c)) * C x y ≤ a := by
  calc _ ≤ ∑ x, ∑ y, Real.exp (w x + h x) / (∑ c, Real.exp (w c + h c)) *
        (Real.exp (v y + h y) / ∑ c, Real.exp (v c + h c)) * a :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (ha x y) (mul_nonneg (gibbsWeight_mem_Icc w h x).1 (gibbsWeight_mem_Icc v h y).1)
    _ = a := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp only [sum_gibbsWeight v h, mul_one, sum_gibbsWeight w h, one_mul]

/-- The `ℓ¹` bound on a Gibbs average over two independent Gibbs measures:
`|∑ₓ ∑ᵧ pₓ qᵧ C(x, y)| ≤ ∑ₓ ∑ᵧ |C(x, y)|`. -/
theorem abs_sum_sum_gibbsWeight_mul_le (w v h : α → ℝ) (C : α → α → ℝ) :
    |∑ x, ∑ y, Real.exp (w x + h x) / (∑ c, Real.exp (w c + h c)) *
      (Real.exp (v y + h y) / ∑ c, Real.exp (v c + h c)) * C x y| ≤ ∑ x, ∑ y, |C x y| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (mul_nonneg (gibbsWeight_mem_Icc w h x).1
    (gibbsWeight_mem_Icc v h y).1)]
  exact mul_le_of_le_one_left (abs_nonneg _) ((mul_le_of_le_one_right
    (gibbsWeight_mem_Icc w h x).1 (gibbsWeight_mem_Icc v h y).2).trans
    (gibbsWeight_mem_Icc w h x).2)

end GibbsWeight

section TrigPath

/-- The trigonometric path `s ↦ cos s x + sin s y + c` has velocity `-sin s x + cos s y`. -/
theorem hasDerivAt_cos_mul_add_sin_mul (x y c s : ℝ) :
    HasDerivAt (fun s => Real.cos s * x + Real.sin s * y + c)
      (-Real.sin s * x + Real.cos s * y) s := by
  convert (((Real.hasDerivAt_cos s).mul_const x).add
    ((Real.hasDerivAt_sin s).mul_const y)).add_const c using 1

/-- The velocity of the trigonometric path is at most `|x| + |y|`, uniformly in `s`. -/
theorem abs_neg_sin_mul_add_cos_mul_le (x y s : ℝ) :
    |-Real.sin s * x + Real.cos s * y| ≤ |x| + |y| := by
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_neg]
  nlinarith [Real.abs_cos_le_one s, Real.abs_sin_le_one s, abs_nonneg x, abs_nonneg y]

/-- The velocity `-sin s x a + cos s y a` of the trigonometric path of a finite family of fields
is at most `∑_b (|x b| + |y b|)`, uniformly in `s` and in the index `a`. -/
theorem abs_neg_sin_mul_add_cos_mul_le_sum {ι : Type*} [Fintype ι] (x y : ι → ℝ) (s : ℝ) (a : ι) :
    |-Real.sin s * x a + Real.cos s * y a| ≤ ∑ b, (|x b| + |y b|) :=
  (abs_neg_sin_mul_add_cos_mul_le (x a) (y a) s).trans
    (Finset.single_le_sum (f := fun b => |x b| + |y b|) (fun _ _ => by positivity)
      (Finset.mem_univ a))

end TrigPath

section Random

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Ω → α → ℝ}

/-- **Temperature derivative of the expected log-partition function:** for a random energy with
integrable coordinates and `β > 0`, `(d/dβ) 𝔼 log Z(β) = 𝔼 ⟨H⟩_β`.  The pointwise derivative is
`hasDerivAt_log_sum_exp`, dominated by the integrable `∑ₐ |H a|`
(`norm_integral_count_tilted_le`). -/
theorem hasDerivAt_integral_log_sum_exp {β : ℝ} (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    HasDerivAt (fun b => ∫ ω, Real.log (∑ a, Real.exp (b * H ω a)) ∂μ)
      (∫ ω, ∫ a, H ω a ∂(Measure.count.tilted fun a => β * H ω a) ∂μ) β :=
  hasDerivAt_integral_log_sum_exp_path (f := fun b ω a => b * H ω a) (f' := fun _ ω a => H ω a)
    (S := Set.Ioi 0) (Ioi_mem_nhds hβ) (fun s a => ((hmeas a).const_mul s).aemeasurable)
    (fun a => (hmeas a).aemeasurable) (integrable_log_sum_exp hβ hmeas hint)
    (fun ω s _ a => (hasDerivAt_id s).mul_const (H ω a) |>.congr_deriv (one_mul _))
    (integrable_finsetSum univ fun a _ => (hint a).abs)
    fun ω _ _ a => Finset.single_le_sum (f := fun b => |H ω b|) (fun _ _ => abs_nonneg _)
      (mem_univ a)

end Random

section SK

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ℝ}

/-- **Temperature derivative of the SK free energy:** for the Hamiltonian
`H G σ = (√N)⁻¹ * (σ ⬝ᵥ (G *ᵥ σ))` with standard Gaussian disorder and `β > 0`,
`(d/dβ) F_N(β) = N⁻¹ 𝔼 ⟨H_N⟩_β` with `F_N(β) = N⁻¹ 𝔼 log Z_N(β)`. -/
theorem sk_hasDerivAt_free_energy (H : (ι → ι → ℝ) → (ι → ℤˣ) → ℝ)
    (hH : ∀ G σ, H G σ = (Real.sqrt (Fintype.card ι))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ)))) (hβ : 0 < β) :
    HasDerivAt (fun b => (Fintype.card ι : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (b * H G σ))
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1))
      ((Fintype.card ι : ℝ)⁻¹ * ∫ G, ∫ σ, H G σ ∂(Measure.count.tilted fun σ => β * H G σ)
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1)) β := by
  obtain rfl : H = fun G σ => (Real.sqrt (Fintype.card ι))⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))) :=
    funext fun G => funext (hH G)
  exact (hasDerivAt_integral_log_sum_exp hβ (fun σ => (sk_measurable_integrable σ).1)
    (fun σ => (sk_measurable_integrable σ).2)).const_mul _

end SK

end SpinGlasses
