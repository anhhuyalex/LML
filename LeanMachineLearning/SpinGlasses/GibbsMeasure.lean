/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

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

/-- **The Gibbs average:** the expectation of `g` under the tilt of the counting measure by `β H` is
`∑ₐ (exp (β H a) / Z(β)) g(a)`. -/
theorem integral_count_tilted (H g : α → ℝ) (β : ℝ) :
    ∫ a, g a ∂(Measure.count.tilted fun a => β * H a) =
      ∑ a, Real.exp (β * H a) / (∑ b, Real.exp (β * H b)) * g a := by
  rw [integral_tilted_mul_eq_mgf, integral_count_eq_sum, mgf_count]
  simp only [smul_eq_mul]

/-- **The Gibbs weight:** the tilt of the counting measure by `β H` gives mass
`exp (β H a) / Z(β)` to `a`. -/
theorem real_count_tilted_singleton (H : α → ℝ) (β : ℝ) (a : α) :
    (Measure.count.tilted fun a => β * H a).real {a} =
      Real.exp (β * H a) / ∑ b, Real.exp (β * H b) := by
  classical
  rw [← integral_indicator_one (measurableSet_singleton a), integral_count_tilted]
  simp [Set.indicator_apply]

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
      (∫ ω, ∫ a, H ω a ∂(Measure.count.tilted fun a => β * H ω a) ∂μ) β := by
  have hF' : Measurable fun ω => ∫ a, H ω a ∂(Measure.count.tilted fun a => β * H ω a) := by
    simp_rw [integral_count_tilted]
    exact Finset.measurable_sum _ fun a _ => (((hmeas a).const_mul β).exp.div
      (Finset.measurable_sum _ fun c _ => ((hmeas c).const_mul β).exp)).mul (hmeas a)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.Ioi 0) (Ioi_mem_nhds hβ)
    (Eventually.of_forall fun b => (measurable_log_sum_exp hmeas b).aestronglyMeasurable)
    (integrable_log_sum_exp hβ hmeas hint) (F' := fun b ω =>
      ∫ a, H ω a ∂(Measure.count.tilted fun a => b * H ω a)) hF'.aestronglyMeasurable
    (bound := fun ω => ∑ a, |H ω a|)
    (ae_of_all _ fun ω b _ => norm_integral_count_tilted_le _ _)
    (integrable_finsetSum univ fun a _ => (hint a).abs)
    (ae_of_all _ fun ω b _ => hasDerivAt_log_sum_exp (H ω) b)).2

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
