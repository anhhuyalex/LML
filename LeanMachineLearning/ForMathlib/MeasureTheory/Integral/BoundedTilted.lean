/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.ProdBound
public import Mathlib.Probability.Moments.Tilted
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub
public import LeanMachineLearning.ForMathlib.Order.Interval.UnitIoo
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Tactic.Linarith
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.Weights
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ParametrizedL2
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IntegrableOfBound

/-!
# Bounded energies on arbitrary finite measure spaces

These estimates and derivatives use Mathlib's exponential tilt directly. The spin space
need not be finite, and bounds and measurability are only required almost everywhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {C : ℝ}

/-- Bound a vector plus a finite weighted sum of vectors. -/
theorem norm_add_sum_smul_le {K E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset K) (D : E) (z : K → ℝ) (X : K → E) {Eb B : ℝ} (hD : ‖D‖ ≤ Eb)
    (hX : ∀ k ∈ s, ‖X k‖ ≤ B) : ‖D + ∑ k ∈ s, z k • X k‖ ≤ Eb + ∑ k ∈ s, |z k| * B := by
  refine (norm_add_le _ _).trans (add_le_add hD ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k hk => ?_)))
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hX k hk) (abs_nonneg _)

/-- Bound a constant plus a finite weighted sum. This is the energy bound used by
Gaussian cavity paths, with the weights supplied by the path. -/
theorem abs_add_sum_mul_le {K : Type*} [Fintype K] (D : ℝ) (z X : K → ℝ)
    {Eb B : ℝ} (hD : |D| ≤ Eb) (hX : ∀ k, |X k| ≤ B) :
    |D + ∑ k, z k * X k| ≤ Eb + ∑ k, |z k| * B := by
  simpa only [Real.norm_eq_abs, smul_eq_mul] using
    norm_add_sum_smul_le Finset.univ D z X (by simpa only [Real.norm_eq_abs] using hD)
      fun k _ => by simpa only [Real.norm_eq_abs] using hX k

/-- An almost everywhere upper bound on a real energy gives exponential integrability
against any finite measure. A lower bound is unnecessary. -/
theorem integrable_exp_of_ae_le [IsFiniteMeasure μ] (hf : AEMeasurable f μ)
    (hbound : ∀ᵐ a ∂μ, f a ≤ C) : Integrable (fun a => Real.exp (f a)) μ := by
  refine (integrable_const (Real.exp C)).mono' hf.exp.aestronglyMeasurable ?_
  filter_upwards [hbound] with a ha
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ha

/-- A measurable energy bounded above has a positive partition integral on a nonzero finite
base measure. The upper bound supplies the integrability needed by `integral_exp_pos`. -/
theorem integral_exp_pos_of_ae_le [IsFiniteMeasure μ] [NeZero μ] (hf : AEMeasurable f μ)
    (hbound : ∀ᵐ a ∂μ, f a ≤ C) : 0 < ∫ a, Real.exp (f a) ∂μ :=
  integral_exp_pos (integrable_exp_of_ae_le hf hbound)

/-- An almost everywhere upper bound on an energy makes its exponential tilt a
probability measure whenever the base measure is nonzero and finite. -/
theorem isProbabilityMeasure_tilted_of_ae_le [IsFiniteMeasure μ] [NeZero μ]
    (hf : AEMeasurable f μ) (hbound : ∀ᵐ a ∂μ, f a ≤ C) :
    IsProbabilityMeasure (μ.tilted f) :=
  isProbabilityMeasure_tilted (integrable_exp_of_ae_le hf hbound)

/-- The logarithmic partition function of a bounded energy on a probability space is
bounded by the same constant. This applies to continuous and singular base laws alike. -/
theorem abs_log_integral_exp_le_of_ae_abs_le [IsProbabilityMeasure μ]
    (hf : AEMeasurable f μ) (hbound : ∀ᵐ a ∂μ, |f a| ≤ C) :
    |Real.log (∫ a, Real.exp (f a) ∂μ)| ≤ C := by
  have hi := integrable_exp_of_ae_le hf (hbound.mono fun a ha =>
    (le_abs_self (f a)).trans ha)
  have hZ := integral_exp_pos hi
  have hupper : (∫ a, Real.exp (f a) ∂μ) ≤ Real.exp C := by
    calc
      _ ≤ ∫ _a : α, Real.exp C ∂μ := integral_mono_ae hi (integrable_const _)
        (hbound.mono fun a ha => Real.exp_le_exp.mpr ((le_abs_self _).trans ha))
      _ = _ := by simp
  have hlower : Real.exp (-C) ≤ ∫ a, Real.exp (f a) ∂μ := by
    calc
      _ = ∫ _a : α, Real.exp (-C) ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hi (hbound.mono fun a ha =>
        Real.exp_le_exp.mpr ((neg_le_neg ha).trans (neg_abs_le _)))
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hZ).mpr hlower,
    (Real.log_le_iff_le_exp hZ).mpr hupper⟩

end MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℝ} {C : ℝ}

/-- A bounded real variable has exponential moments at every real parameter on a finite
measure space; there is no restriction on the sign of the parameter. -/
theorem integrableExpSet_eq_univ_of_ae_abs_le [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ a ∂μ, |X a| ≤ C) :
    integrableExpSet X μ = univ := by
  apply Set.eq_univ_of_forall
  intro t
  apply integrable_exp_of_ae_le (hX.const_mul t) (C := |t| * C)
  filter_upwards [hbound] with a ha
  apply (le_abs_self _).trans
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ha (abs_nonneg t)

/-- The log-partition derivative for a bounded energy under an arbitrary finite base
measure is its tilted mean. This reuses Mathlib's analytic cumulant-generating function
and tilted-mean identity rather than a finite-configuration differentiation argument. -/
theorem hasDerivAt_log_integral_exp_mul_of_ae_abs_le [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ a ∂μ, |X a| ≤ C) (t : ℝ) :
    HasDerivAt (fun s => Real.log (∫ a, Real.exp (s * X a) ∂μ))
      (∫ a, X a ∂(μ.tilted (fun a => t * X a))) t := by
  have ht : t ∈ interior (integrableExpSet X μ) := by
    simp [integrableExpSet_eq_univ_of_ae_abs_le hX hbound]
  have hcgf : cgf X μ = (fun s => Real.log (∫ a, Real.exp (s * X a) ∂μ)) := rfl
  rw [← hcgf, integral_tilted_mul_self ht]
  exact (analyticAt_cgf ht).differentiableAt.hasDerivAt

end ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {X Y : α → ℝ} {C B : ℝ}

/-- The average of a vector-valued observable under a tilted measure as a quotient of
integrals. -/
theorem integral_tilted_eq_inv_smul {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {μ : Measure α} (e : α → ℝ) (Y : α → V) :
    ∫ a, Y a ∂(μ.tilted e) =
      (∫ a, Real.exp (e a) ∂μ)⁻¹ • ∫ a, Real.exp (e a) • Y a ∂μ := by
  rw [integral_tilted, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [smul_smul, div_eq_inv_mul]

/-- The integral against the tilted probability measure written as a quotient of integrals. -/
theorem integral_tilted_eq_div {α : Type*} [MeasurableSpace α] {μ : Measure α} (e Y : α → ℝ) :
    ∫ a, Y a ∂(μ.tilted e) = (∫ a, Y a * Real.exp (e a) ∂μ) / ∫ a, Real.exp (e a) ∂μ := by
  rw [integral_tilted_eq_inv_smul, smul_eq_mul, inv_mul_eq_div]
  simp only [smul_eq_mul, mul_comm (Real.exp _)]

/-- **Derivative of a moving vector-valued observable under a varying exponential tilt.** For
observables `F r` with values in a normed space and energies `e r` differentiable in `r`, the
derivative of `r ↦ ⟨F r⟩_{e r}` is `⟨∂_r F⟩ + cov(∂_r e, F)`. Integrable bounds on the weighted
derivatives justify differentiating numerator and normalizer. -/
theorem hasDerivAt_integral_tilted_moving_smul {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α} [NeZero μ]
    {e e' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun a => Real.exp (e r a)) μ)
    (hi : Integrable (fun a => Real.exp (e t a)) μ)
    (hdm : AEStronglyMeasurable (fun a => e' t a * Real.exp (e t a)) μ)
    {b : α → ℝ} (hb : Integrable b μ)
    (hdb : ∀ᵐ a ∂μ, ∀ r ∈ s, |e' r a * Real.exp (e r a)| ≤ b a)
    (hd : ∀ᵐ a ∂μ, ∀ r ∈ s, HasDerivAt (fun q => e q a) (e' r a) r)
    {F F' : ℝ → α → V} (hFm : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) μ)
    (hF'm : AEStronglyMeasurable (F' t) μ) {C : ℝ}
    (hFb : ∀ᵐ a ∂μ, ∀ r ∈ s, ‖F r a‖ ≤ C)
    {b₂ : α → ℝ} (hb₂ : Integrable b₂ μ)
    (hdb₂ : ∀ᵐ a ∂μ, ∀ r ∈ s, ‖F' r a‖ * Real.exp (e r a) ≤ b₂ a)
    (hFd : ∀ᵐ a ∂μ, ∀ r ∈ s, HasDerivAt (fun q => F q a) (F' r a) r) :
    HasDerivAt (fun r => ∫ a, F r a ∂μ.tilted (e r))
      ((∫ a, F' t a ∂μ.tilted (e t)) +
        ((∫ a, e' t a • F t a ∂μ.tilted (e t)) -
          (∫ a, e' t a ∂μ.tilted (e t)) • ∫ a, F t a ∂μ.tilted (e t))) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hden := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hi hdm
    (by simpa only [Real.norm_eq_abs] using hdb) hb
    (hd.mono fun a ha r hr => by simpa only [mul_comm] using (ha r hr).exp)
  have hFt : AEStronglyMeasurable (F t) μ := hFm.self_of_nhds
  have hFb' : ∀ᵐ a ∂μ, ‖F t a‖ ≤ C := hFb.mono fun a ha => ha t ht
  have hNi : Integrable (fun a => Real.exp (e t a) • F t a) μ := by
    refine (hi.mul_const |C|).mono' (hmeas.self_of_nhds.smul hFt) (hFb'.mono fun a ha => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (ha.trans (le_abs_self C)) (Real.exp_pos _).le
  have hnum := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun r a => Real.exp (e r a) • F r a)
    (F' := fun r a => Real.exp (e r a) • F' r a + (e' r a * Real.exp (e r a)) • F r a)
    hs (hmeas.and hFm |>.mono fun r hr => hr.1.smul hr.2) hNi
    ((hmeas.self_of_nhds.smul hF'm).add (hdm.smul hFt))
    (bound := fun a => b₂ a + |C| * b a)
    (by
      filter_upwards [hdb, hFb, hdb₂] with a hda hFa hdb2a r hr
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
        exact hdb2a r hr
      · rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul ((hFa r hr).trans (le_abs_self C)) (hda r hr) (abs_nonneg _)
          (abs_nonneg _))
    (hb₂.add (hb.const_mul |C|))
    (by
      filter_upwards [hd, hFd] with a ha hFa r hr
      exact ((ha r hr).exp.smul (hFa r hr)).congr_deriv (by rw [mul_comm (Real.exp _)]))
  have hI1 : Integrable (fun a => Real.exp (e t a) • F' t a) μ :=
    hb₂.mono' (hmeas.self_of_nhds.smul hF'm) (by
      filter_upwards [hdb₂] with a h
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact h t ht)
  have hI2 : Integrable (fun a => (e' t a * Real.exp (e t a)) • F t a) μ :=
    (hb.const_mul |C|).mono' (hdm.smul hFt) (by
      filter_upwards [hdb, hFb] with a hda hFa
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul ((hFa t ht).trans (le_abs_self C)) (hda t ht) (abs_nonneg _)
        (abs_nonneg _))
  have hnum' := hnum.2
  rw [integral_add hI1 hI2] at hnum'
  have hZ := (integral_exp_pos hi).ne'
  simp_rw [integral_tilted_eq_inv_smul]
  refine ((hden.2.inv hZ).smul hnum').congr_deriv ?_
  have e1 : (∫ a, Real.exp (e t a) • e' t a • F t a ∂μ) =
      ∫ a, (e' t a * Real.exp (e t a)) • F t a ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by simp only [smul_smul, mul_comm])
  have e2 : (∫ a, Real.exp (e t a) • e' t a ∂μ) = ∫ a, e' t a * Real.exp (e t a) ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by simp only [smul_eq_mul, mul_comm])
  rw [e1, e2]
  simp only [Pi.inv_apply, smul_add, smul_smul]
  rw [add_assoc]
  congr 1
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  rw [smul_eq_mul]
  field_simp

/-- **Derivative of a moving observable under a varying exponential tilt.** For observables
`F r` and energies `e r` differentiable in `r`, the derivative of `r ↦ ⟨F r⟩_{e r}` is
`⟨∂_r F⟩ + cov(F, ∂_r e)`. Integrable bounds on the weighted derivatives justify differentiating
numerator and normalizer. -/
theorem hasDerivAt_integral_tilted_moving {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [NeZero μ]
    {e e' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun a => Real.exp (e r a)) μ)
    (hi : Integrable (fun a => Real.exp (e t a)) μ)
    (hdm : AEStronglyMeasurable (fun a => e' t a * Real.exp (e t a)) μ)
    {b : α → ℝ} (hb : Integrable b μ)
    (hdb : ∀ᵐ a ∂μ, ∀ r ∈ s, |e' r a * Real.exp (e r a)| ≤ b a)
    (hd : ∀ᵐ a ∂μ, ∀ r ∈ s, HasDerivAt (fun q => e q a) (e' r a) r)
    {F F' : ℝ → α → ℝ} (hFm : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) μ)
    (hF'm : AEStronglyMeasurable (F' t) μ) {C : ℝ}
    (hFb : ∀ᵐ a ∂μ, ∀ r ∈ s, |F r a| ≤ C)
    {b₂ : α → ℝ} (hb₂ : Integrable b₂ μ)
    (hdb₂ : ∀ᵐ a ∂μ, ∀ r ∈ s, |F' r a| * Real.exp (e r a) ≤ b₂ a)
    (hFd : ∀ᵐ a ∂μ, ∀ r ∈ s, HasDerivAt (fun q => F q a) (F' r a) r) :
    HasDerivAt (fun r => ∫ a, F r a ∂μ.tilted (e r))
      ((∫ a, F' t a ∂μ.tilted (e t)) +
        ((∫ a, F t a * e' t a ∂μ.tilted (e t)) -
          (∫ a, F t a ∂μ.tilted (e t)) * ∫ a, e' t a ∂μ.tilted (e t))) t := by
  have h := hasDerivAt_integral_tilted_moving_smul hs hmeas hi hdm hb hdb hd hFm hF'm
    (C := C) (by simpa only [Real.norm_eq_abs] using hFb) hb₂
    (by simpa only [Real.norm_eq_abs] using hdb₂) hFd
  simpa only [smul_eq_mul, mul_comm] using h

/-- **Derivative of the tilted integral of an unbounded observable.** If
`(1 + |F|) (1 + |∂_r e|) exp (e r)` is bounded by an integrable function for all `r` near `t`, then
`r ↦ ⟨F⟩_{e r}` has derivative `⟨F ∂_t e⟩ - ⟨F⟩ ⟨∂_t e⟩` at `t`. The nonzero base measure need
not be finite and the observable need not be bounded. -/
theorem hasDerivAt_integral_tilted_of_envelope {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [NeZero μ] {e e' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (he : ∀ r ∈ s, Measurable (e r)) (he' : Measurable (e' t)) {F : α → ℝ} (hF : Measurable F)
    {b : α → ℝ} (hb : Integrable b μ)
    (hbd : ∀ r ∈ s, ∀ a, (1 + |F a|) * (1 + |e' r a|) * Real.exp (e r a) ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => e q a) (e' r a) r) :
    HasDerivAt (fun r => ∫ a, F a ∂μ.tilted (e r))
      ((∫ a, F a * e' t a ∂μ.tilted (e t)) -
        (∫ a, F a ∂μ.tilted (e t)) * ∫ a, e' t a ∂μ.tilted (e t)) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have key : ∀ r ∈ s, ∀ a (c : ℝ), |c| ≤ (1 + |F a|) * (1 + |e' r a|) →
      |c * Real.exp (e r a)| ≤ b a := fun r hr a c hc => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans (hbd r hr a)
  have h1 : ∀ r a, (1 : ℝ) ≤ (1 + |F a|) * (1 + |e' r a|) := fun r a =>
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_right (abs_nonneg _))
  have hexp : ∀ r ∈ s, AEStronglyMeasurable (fun a => Real.exp (e r a)) μ := fun r hr =>
    (he r hr).exp.aestronglyMeasurable
  have hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun a => Real.exp (e r a)) μ :=
    Filter.mem_of_superset hs hexp
  have hZi : Integrable (fun a => Real.exp (e t a)) μ :=
    hb.mono' (hexp t ht) (ae_of_all _ fun a => by
      simpa only [one_mul, Real.norm_eq_abs] using key t ht a 1 (by rw [abs_one]; exact h1 t a))
  have hden := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun r a => Real.exp (e r a)) (F' := fun r a => e' r a * Real.exp (e r a))
    (bound := b) hs hmeas hZi (he'.mul (he t ht).exp).aestronglyMeasurable
    (ae_of_all _ fun a r hr => by
      rw [Real.norm_eq_abs]
      refine key r hr a _ ?_
      nlinarith [mul_nonneg (abs_nonneg (F a)) (abs_nonneg (e' r a)), abs_nonneg (F a)])
    hb (ae_of_all _ fun a r hr => by
      simpa only [mul_comm] using (hd a r hr).exp)).2
  have hNi : Integrable (fun a => F a * Real.exp (e t a)) μ :=
    hb.mono' (hF.mul (he t ht).exp).aestronglyMeasurable (ae_of_all _ fun a => by
      rw [Real.norm_eq_abs]
      refine key t ht a _ ?_
      nlinarith [mul_nonneg (abs_nonneg (F a)) (abs_nonneg (e' t a)), abs_nonneg (e' t a)])
  have hnum := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun r a => F a * Real.exp (e r a))
    (F' := fun r a => F a * (e' r a * Real.exp (e r a))) (bound := b) hs
    (Filter.mem_of_superset hs fun r hr => (hF.mul (he r hr).exp).aestronglyMeasurable) hNi
    (hF.mul (he'.mul (he t ht).exp)).aestronglyMeasurable
    (ae_of_all _ fun a r hr => by
      rw [Real.norm_eq_abs, ← mul_assoc]
      refine key r hr a _ ?_
      rw [abs_mul]
      nlinarith [abs_nonneg (F a), abs_nonneg (e' r a)])
    hb (ae_of_all _ fun a r hr => by
      simpa only [mul_comm] using ((hd a r hr).exp).const_mul (F a))).2
  simp_rw [integral_tilted_eq_div]
  have hZ := (integral_exp_pos hZi).ne'
  refine (hnum.div hden hZ).congr_deriv ?_
  have e1 : (∫ a, F a * (e' t a * Real.exp (e t a)) ∂μ) =
      ∫ a, F a * e' t a * Real.exp (e t a) ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by ring)
  rw [e1]
  field_simp

/-- Pointwise bound `|x e^y| ≤ c e^B` for `|x| ≤ c` and `y ≤ B`. -/
theorem abs_mul_exp_le {x y c B : ℝ} (hx : |x| ≤ c) (hy : y ≤ B) :
    |x * Real.exp y| ≤ c * Real.exp B := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hx (Real.exp_le_exp.mpr hy) (Real.exp_pos _).le ((abs_nonneg _).trans hx)

/-- **Moving-observable derivative with an integrable derivative envelope.** An upper bound on
the energy, an integrable envelope for the energy derivative, a uniformly bounded observable and an
*integrable envelope* `b₂` for the observable's parameter derivative justify differentiating
`r ↦ ⟨F r⟩_{E r}` on a finite base measure. -/
theorem hasDerivAt_integral_tilted_of_integrable_moving
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {A : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ A)
    {b : α → ℝ} (hb : Integrable b μ)
    (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F F' : ℝ → α → ℝ} (hF : ∀ r ∈ s, Measurable (F r)) (hF' : Measurable (F' t))
    {C : ℝ} (hFb : ∀ r ∈ s, ∀ a, |F r a| ≤ C)
    {b₂ : α → ℝ} (hb₂ : Integrable b₂ μ) (hF'b : ∀ r ∈ s, ∀ a, |F' r a| ≤ b₂ a)
    (hFd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => F q a) (F' r a) r) :
    HasDerivAt (fun r => ∫ a, F r a ∂μ.tilted (E r))
      ((∫ a, F' t a ∂μ.tilted (E t)) +
        ((∫ a, F t a * E' t a ∂μ.tilted (E t)) -
          (∫ a, F t a ∂μ.tilted (E t)) * ∫ a, E' t a ∂μ.tilted (E t))) t := by
  have ht := mem_of_mem_nhds hs
  exact hasDerivAt_integral_tilted_moving (e := E) (e' := E') hs
    (Filter.mem_of_superset hs fun r hr => (hE r hr).exp.aestronglyMeasurable)
    (integrable_exp_of_ae_le (hE t ht).aemeasurable (ae_of_all _ (hEb t ht)))
    (hE'.mul (hE t ht).exp).aestronglyMeasurable (hb.const_mul (Real.exp A))
    (ae_of_all _ fun a r hr =>
      (abs_mul_exp_le (hdb r hr a) (hEb r hr a)).trans_eq (mul_comm _ _))
    (ae_of_all _ hd) (Filter.mem_of_superset hs fun r hr => (hF r hr).aestronglyMeasurable)
    hF'.aestronglyMeasurable (C := C) (ae_of_all _ fun a r hr => hFb r hr a)
    (b₂ := fun a => b₂ a * Real.exp A) (hb₂.mul_const _)
    (ae_of_all _ fun a r hr =>
      mul_le_mul (hF'b r hr a) (Real.exp_le_exp.mpr (hEb r hr a)) (Real.exp_pos _).le
        ((abs_nonneg _).trans (hF'b r hr a)))
    (ae_of_all _ hFd)

/-- **Bounded version of the moving-observable derivative.** Uniform bounds on the observable and
its parameter derivative, and an upper bound on the energy, justify differentiating
`r ↦ ⟨F r⟩_{E r}` on a finite base measure. -/
theorem hasDerivAt_integral_tilted_of_bounded_moving
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {A : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ A)
    {b : α → ℝ} (hb : Integrable b μ)
    (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F F' : ℝ → α → ℝ} (hF : ∀ r ∈ s, Measurable (F r)) (hF' : Measurable (F' t))
    {C C' : ℝ} (hFb : ∀ r ∈ s, ∀ a, |F r a| ≤ C) (hF'b : ∀ r ∈ s, ∀ a, |F' r a| ≤ C')
    (hFd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => F q a) (F' r a) r) :
    HasDerivAt (fun r => ∫ a, F r a ∂μ.tilted (E r))
      ((∫ a, F' t a ∂μ.tilted (E t)) +
        ((∫ a, F t a * E' t a ∂μ.tilted (E t)) -
          (∫ a, F t a ∂μ.tilted (E t)) * ∫ a, E' t a ∂μ.tilted (E t))) t :=
  hasDerivAt_integral_tilted_of_integrable_moving hs hE hE' hEb hb hdb hd hF hF' hFb
    (integrable_const C') hF'b hFd

/-- An upper energy bound converts an unweighted integrable derivative envelope into the
weighted envelope needed to differentiate an exponential tilt on a finite base measure. -/
theorem hasDerivAt_integral_tilted_of_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {A : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ A)
    {b : α → ℝ} (hb : Integrable b μ)
    (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F : α → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ a, |F a| ≤ C) :
    HasDerivAt (fun r => ∫ a, F a ∂μ.tilted (E r))
      ((∫ a, F a * E' t a ∂μ.tilted (E t)) -
        (∫ a, F a ∂μ.tilted (E t)) * ∫ a, E' t a ∂μ.tilted (E t)) t := by
  have := hasDerivAt_integral_tilted_of_bounded_moving hs hE hE' hEb hb hdb hd
    (F := fun _ => F) (F' := fun _ _ => 0) (fun _ _ => hF) measurable_const (C := C) (C' := 0)
    (fun _ _ a => hFb a) (fun _ _ _ => by simp) (fun a r _ => hasDerivAt_const r (F a))
  simpa using this

/-- A bounded log-density controls a possibly unbounded tilted observable by its base first
moment. The denominator bound retains the mass of a nonzero finite base measure. -/
theorem abs_integral_tilted_le_exp_mul_integral_abs {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {e Y : α → ℝ} (he : AEMeasurable e μ) {C : ℝ} (heb : ∀ᵐ a ∂μ, |e a| ≤ C)
    (hY : Integrable Y μ) :
    |∫ a, Y a ∂μ.tilted e| ≤
      Real.exp (2 * C) / μ.real Set.univ * ∫ a, |Y a| ∂μ := by
  have hi := integrable_exp_of_ae_le he (heb.mono fun a ha => le_of_abs_le ha)
  have hZ := integral_exp_pos hi
  have hm : 0 < μ.real Set.univ := ENNReal.toReal_pos (NeZero.ne (μ Set.univ))
    (measure_ne_top μ Set.univ)
  have hl : μ.real Set.univ * Real.exp (-C) ≤ ∫ a, Real.exp (e a) ∂μ := by
    calc _ = ∫ _a, Real.exp (-C) ∂μ := by rw [integral_const, smul_eq_mul]
      _ ≤ _ := integral_mono_ae (integrable_const _) hi
        (heb.mono fun a ha => Real.exp_le_exp.mpr (neg_le_of_abs_le ha))
  have hu : (∫ a, |Y a| * Real.exp (e a) ∂μ) ≤ Real.exp C * ∫ a, |Y a| ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun a => by positivity)
      (hY.abs.const_mul _) ?_
    filter_upwards [heb] with a ha
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (le_of_abs_le ha)) (abs_nonneg _)).trans_eq
      (mul_comm _ _)
  rw [integral_tilted_eq_div, abs_div, abs_of_pos hZ]
  calc _ ≤ (∫ a, |Y a| * Real.exp (e a) ∂μ) / (∫ a, Real.exp (e a) ∂μ) := by
        apply div_le_div_of_nonneg_right _ hZ.le
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
          norm_integral_le_integral_norm (fun a => Y a * Real.exp (e a))
    _ ≤ (Real.exp C * ∫ a, |Y a| ∂μ) / (∫ a, Real.exp (e a) ∂μ) :=
        div_le_div_of_nonneg_right hu hZ.le
    _ ≤ (Real.exp C * ∫ a, |Y a| ∂μ) / (μ.real Set.univ * Real.exp (-C)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hm (Real.exp_pos _)) hl
    _ = _ := by
        rw [Real.exp_neg]
        field_simp
        rw [pow_two, ← Real.exp_add, ← two_mul C]
        exact mul_comm _ _

/-- An upper-bounded energy preserves base integrability under its normalized exponential
 tilt. The base measure is finite and may be zero. -/
theorem integrable_tilted_of_ae_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {e f : α → ℝ} {C : ℝ} (he : AEMeasurable e μ)
    (hC : ∀ᵐ a ∂μ, e a ≤ C) (hf : Integrable f μ) : Integrable f (μ.tilted e) := by
  refine (integrable_tilted_iff (integrable_exp_of_ae_le he hC) f).mpr ?_
  simpa only [smul_eq_mul] using hf.bdd_mul (c := Real.exp C) he.exp.aestronglyMeasurable (by
    filter_upwards [hC] with a ha
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ha)

/-- A bounded derivative or observable bounded pointwise by an integrable envelope is
integrable under an exponential tilt with energy bounded above. -/
theorem integrable_tilted_of_abs_le_envelope {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {e g b : α → ℝ} {A : ℝ} (he : AEMeasurable e μ)
    (hg : AEStronglyMeasurable g μ) (hb : Integrable b μ) (heb : ∀ᵐ a ∂μ, e a ≤ A)
    (hgb : ∀ᵐ a ∂μ, |g a| ≤ b a) : Integrable g (μ.tilted e) :=
  integrable_tilted_of_ae_le he heb
    (hb.mono' hg (hgb.mono fun a ha => by simpa only [Real.norm_eq_abs] using ha))

/-- A jointly measurable observable and random log-density have a measurable tilted integral.
The observable may depend on the same environment as the log-density. -/
theorem measurable_integral_tilted_dep {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {e Y : Ω → α → ℝ}
    (hE : Measurable fun p : Ω × α => e p.1 p.2)
    (hY : Measurable fun p : Ω × α => Y p.1 p.2) :
    Measurable fun ω => ∫ a, Y ω a ∂(μ.tilted (e ω)) := by
  simp_rw [integral_tilted_eq_div]
  exact ((hY.mul hE.exp).integral_prod_right' (ν := μ)).div
    (hE.exp.integral_prod_right' (ν := μ))

/-- The tilted integral of a fixed measurable observable is measurable in a jointly measurable
random log-density. -/
theorem measurable_integral_tilted {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {e : Ω → α → ℝ} (hE : Measurable fun p : Ω × α => e p.1 p.2)
    {Y : α → ℝ} (hY : Measurable Y) : Measurable fun ω => ∫ a, Y a ∂(μ.tilted (e ω)) :=
  measurable_integral_tilted_dep hE (hY.comp measurable_snd)

/-- An integral over two independent copies of a random tilted measure is measurable in the
environment, for a jointly measurable integrable observable. -/
theorem measurable_integral_prod_tilted_dep {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {e : Ω → α → ℝ} (hE : Measurable fun p : Ω × α => e p.1 p.2)
    {F : Ω → α × α → ℝ} (hF : Measurable fun p : Ω × (α × α) => F p.1 p.2)
    (hFi : ∀ ω, Integrable (F ω) ((μ.tilted (e ω)).prod (μ.tilted (e ω)))) :
    Measurable fun ω => ∫ p, F ω p ∂((μ.tilted (e ω)).prod (μ.tilted (e ω))) := by
  have hinner : Measurable fun q : Ω × α => ∫ b, F q.1 (q.2, b) ∂(μ.tilted (e q.1)) :=
    measurable_integral_tilted_dep (e := fun (q : Ω × α) b => e q.1 b)
      (Y := fun (q : Ω × α) b => F q.1 (q.2, b))
      (hE.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (hF.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have h := measurable_integral_tilted_dep (μ := μ) (e := e)
    (Y := fun ω a => ∫ b, F ω (a, b) ∂(μ.tilted (e ω))) hE hinner
  exact (funext fun ω => integral_prod _ (hFi ω)) ▸ h

/-- A tilted integral of an observable bounded by `M` is bounded by `M`. -/
theorem abs_integral_tilted_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [NeZero μ]
    {e Y : α → ℝ} (he : Integrable (fun a => Real.exp (e a)) μ) {M : ℝ}
    (hY : ∀ a, |Y a| ≤ M) : |∫ a, Y a ∂(μ.tilted e)| ≤ M := by
  have : IsProbabilityMeasure (μ.tilted e) := isProbabilityMeasure_tilted he
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ.tilted e) (f := Y) (C := M)
    (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hY a)
  simpa using this

/-- Jensen's inequality for a vector of observables under a tilted probability measure. -/
theorem sum_sq_integral_tilted_le {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} [NeZero μ] {e : α → ℝ}
    (he : Integrable (fun a => Real.exp (e a)) μ)
    (Y : ι → α → ℝ) (hY : ∀ i, Measurable (Y i)) {M : ℝ} (hb : ∀ i a, |Y i a| ≤ M) :
    ∑ i, (∫ a, Y i a ∂(μ.tilted e)) ^ 2 ≤ ∫ a, ∑ i, Y i a ^ 2 ∂(μ.tilted e) := by
  have : IsProbabilityMeasure (μ.tilted e) := isProbabilityMeasure_tilted he
  exact sum_sq_integral_le Y hY hb

/-- A bounded factor controls covariance by twice its bound times the absolute first moment
of the other factor. The inequality itself requires no measurability of the bounded factor. -/
theorem abs_integral_mul_sub_integral_mul_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (F h : α → ℝ) {C : ℝ} (hFb : ∀ᵐ a ∂μ, |F a| ≤ C) (hh : Integrable h μ) :
    |(∫ a, F a * h a ∂μ) - (∫ a, F a ∂μ) * (∫ a, h a ∂μ)| ≤
      2 * |C| * ∫ a, |h a| ∂μ := by
  have hF : |∫ a, F a ∂μ| ≤ |C| := by
    have hx := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := |C|)
      (hFb.mono fun a ha => by simpa only [Real.norm_eq_abs] using ha.trans (le_abs_self C))
    simpa using hx
  have hprod : |∫ a, F a * h a ∂μ| ≤ |C| * ∫ a, |h a| ∂μ := by
    have hx := norm_integral_le_of_norm_le (f := fun a => F a * h a) (hh.abs.const_mul |C|)
      (hFb.mono fun a ha => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (ha.trans (le_abs_self C)) (abs_nonneg _))
    simpa only [Real.norm_eq_abs, integral_const_mul] using hx
  have hhmean : |∫ a, h a ∂μ| ≤ ∫ a, |h a| ∂μ := abs_integral_le_integral_abs
  calc _ ≤ |∫ a, F a * h a ∂μ| + |(∫ a, F a ∂μ) * ∫ a, h a ∂μ| := abs_sub _ _
    _ ≤ |C| * (∫ a, |h a| ∂μ) + |C| * ∫ a, |h a| ∂μ :=
      add_le_add hprod (by
        rw [abs_mul]
        exact mul_le_mul hF hhmean (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

open Filter Topology in
/-- **Derivative of a log-partition function under dominated differentiation.** If the energies
`E r a` have `r`-derivative `E' r a` for `r` in a neighborhood `s` of `t`, with
`|E' r a * exp (E r a)|` dominated by an integrable function, then
`r ↦ log ∫ exp (E r a) ∂μ` has at `t` the derivative `∫ E' t a` against the Gibbs measure
`μ.tilted (E t)`. Both the energy and its derivative may be unbounded and the state space need not
be finite. -/
theorem hasDerivAt_log_integral_exp_of_dominated
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun a => Real.exp (E r a)) μ)
    (hi : Integrable (fun a => Real.exp (E t a)) μ)
    (hdm : AEStronglyMeasurable (fun a => E' t a * Real.exp (E t a)) μ)
    {b : α → ℝ} (hb : Integrable b μ)
    (hdb : ∀ᵐ a ∂μ, ∀ r ∈ s, |E' r a * Real.exp (E r a)| ≤ b a)
    (hd : ∀ᵐ a ∂μ, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r) :
    HasDerivAt (fun r => Real.log (∫ a, Real.exp (E r a) ∂μ))
      (∫ a, E' t a ∂μ.tilted (E t)) t := by
  have hden := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hi hdm
    (by simpa only [Real.norm_eq_abs] using hdb) hb
    (hd.mono fun a ha r hr => by simpa only [mul_comm] using (ha r hr).exp)).2
  exact (hden.log (integral_exp_pos hi).ne').congr_deriv (by
    rw [integral_tilted_eq_div, div_eq_mul_inv, mul_comm])

open Filter Topology in
/-- **Derivative of a square-root interpolation log-partition function.** For a differentiable
potential `u ≤ B` with `|u'| ≤ D₁`, a probability measure `μ` and integrable measurable `A, C`, the
function `s ↦ log ∫ exp (u (√s A + √(1 - s) C)) ∂μ` has at `t ∈ (0, 1)` the derivative
`∫ (A / (2 √t) - C / (2 √(1 - t))) u' (√t A + √(1 - t) C)` against the corresponding Gibbs
measure. -/
theorem hasDerivAt_log_integral_exp_sqrt_path
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {u : ℝ → ℝ} {B D₁ : ℝ} (hu : Differentiable ℝ u) (hB : ∀ x, u x ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D₁) {A C : α → ℝ} (hAm : Measurable A) (hCm : Measurable C)
    (hA : Integrable A μ) (hC : Integrable C μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => Real.log (∫ x, Real.exp (u (√s * A x + √(1 - s) * C x)) ∂μ))
      (∫ x, (A x / (2 * √t) - C x / (2 * √(1 - t))) *
          deriv u (√t * A x + √(1 - t) * C x)
        ∂μ.tilted (fun x => u (√t * A x + √(1 - t) * C x))) t := by
  obtain ⟨δ, hδ, hδ_bd⟩ := exists_Ioo_nhds_bound ht
  have hD₁ : 0 ≤ D₁ := (abs_nonneg _).trans (hD 0)
  have hum : Measurable u := hu.continuous.measurable
  have hmE (s : ℝ) : Measurable fun x => u (√s * A x + √(1 - s) * C x) :=
    hum.comp ((hAm.const_mul _).add (hCm.const_mul _))
  have hmE' (s : ℝ) : Measurable fun x => (A x / (2 * √s) - C x / (2 * √(1 - s))) *
      deriv u (√s * A x + √(1 - s) * C x) :=
    ((hAm.div_const _).sub (hCm.div_const _)).mul
      ((measurable_deriv u).comp ((hAm.const_mul _).add (hCm.const_mul _)))
  refine hasDerivAt_log_integral_exp_of_dominated (μ := μ)
    (E := fun s x => u (√s * A x + √(1 - s) * C x))
    (E' := fun s x => (A x / (2 * √s) - C x / (2 * √(1 - s))) *
      deriv u (√s * A x + √(1 - s) * C x))
    (s := Ioo (t - δ) (t + δ)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (Real.measurable_exp.comp (hmE s)).aestronglyMeasurable)
    (integrable_exp_of_ae_le (hmE t).aemeasurable (ae_of_all _ fun _ => hB _))
    ((hmE' t).mul (Real.measurable_exp.comp (hmE t))).aestronglyMeasurable
    (b := fun x => (D₁ * ((|A x| + |C x|) / (2 * √δ))) * Real.exp B)
    ((((hA.abs.add hC.abs).div_const _).const_mul D₁).mul_const _) ?_ ?_
  · refine ae_of_all _ fun x r hr => abs_mul_exp_le ?_ (hB _)
    obtain ⟨h1, h2⟩ := hδ_bd r hr
    rw [abs_mul, mul_comm]
    exact mul_le_mul (hD _) (abs_div_two_sqrt_sub_le hδ h1 h2) (abs_nonneg _) hD₁
  · refine ae_of_all _ fun x r hr => ?_
    obtain ⟨h1, h2⟩ := hδ_bd r hr
    have hθ := hasDerivAt_sqrt_mul_add_sqrt_one_sub_mul ⟨hδ.trans_le h1, by linarith⟩ (A x) (C x)
    exact ((hu _).hasDerivAt.comp r hθ).congr_deriv (mul_comm _ _)

end MeasureTheory
