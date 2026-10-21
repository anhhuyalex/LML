/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Units
public import LeanMachineLearning.SpinGlasses.FreeEnergy
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted

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

/-- **Logarithm of a Gibbs average:** for a positive observable `F`,
`log ⟨F⟩ = log ∑ₐ exp (f a) F(a) - log ∑ₐ exp (f a)`, i.e. the normalization `Z = ∑ₐ exp (f a)`
splits off.  This is what makes the partition function cancel in differences of log-averages. -/
theorem log_integral_count_tilted [Nonempty α] (f F : α → ℝ) (hF : ∀ a, 0 < F a) :
    Real.log (∫ a, F a ∂(Measure.count.tilted f)) =
      Real.log (∑ a, Real.exp (f a) * F a) - Real.log (∑ a, Real.exp (f a)) := by
  have hZ : 0 < ∑ a, Real.exp (f a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZF : 0 < ∑ a, Real.exp (f a) * F a :=
    Finset.sum_pos (fun a _ => mul_pos (Real.exp_pos _) (hF a)) Finset.univ_nonempty
  rw [integral_count_tilted, ← Real.log_div hZF.ne' hZ.ne', Finset.sum_div]
  simp_rw [div_mul_eq_mul_div]

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
  rw [show (∑ a, Real.exp (f a + V a)) =
      ∑ a, Real.exp (f a) * Real.exp (V a) by simp_rw [Real.exp_add]]
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
