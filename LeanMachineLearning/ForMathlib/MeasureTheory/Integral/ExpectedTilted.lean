/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Differentiation of an environment-averaged exponential tilt

A bounded energy controls the normalized Gibbs density from above and below. A separable
bound on its derivative then yields an integrable bound on the covariance derivative.
The outer measure is any finite measure; no Gaussian or finite-state assumption is needed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace MeasureTheory

private theorem abs_integral_mul_sub_integral_mul_tilted_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {e Y b : α → ℝ} {A B C : ℝ} (he : AEMeasurable e μ)
    (heb : ∀ a, |e a| ≤ A) (hb : Integrable b μ) (hYb : ∀ a, |Y a| ≤ B * b a)
    (hiY : Integrable Y μ) (hiTilt : Integrable Y (μ.tilted e))
    (F : α → ℝ) (hFb : ∀ a, |F a| ≤ C) :
    |(∫ a, F a * Y a ∂μ.tilted e) -
      (∫ a, F a ∂μ.tilted e) * (∫ a, Y a ∂μ.tilted e)| ≤
      (2 * |C| / μ.real Set.univ * ∫ a, b a ∂μ) * (Real.exp (2 * A) * B) := by
  have hiExp := integrable_exp_of_ae_le he (ae_of_all _ fun a => le_of_abs_le (heb a))
  have : IsProbabilityMeasure (μ.tilted (e)) := isProbabilityMeasure_tilted
    hiExp
  have hcov := abs_integral_mul_sub_integral_mul_le F (Y) hFb hiTilt
  have htilt := abs_integral_tilted_le_exp_mul_integral_abs he
    (ae_of_all _ heb) hiY.abs
  simp only [abs_abs] at htilt
  have hu : (∫ a, |Y a| ∂μ) ≤ B * ∫ a, b a ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono_ae hiY.abs (hb.const_mul _)
      (ae_of_all _ hYb)
  have hm : 0 < μ.real Set.univ := ENNReal.toReal_pos (NeZero.ne (μ Set.univ))
    (measure_ne_top μ Set.univ)
  calc _ ≤ 2 * |C| * ∫ a, |Y a| ∂μ.tilted (e) := hcov
    _ ≤ 2 * |C| * (Real.exp (2 * A) / μ.real Set.univ *
        (B * ∫ a, b a ∂μ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (le_abs_self _).trans (htilt.trans
        (mul_le_mul_of_nonneg_left hu (by positivity)))
    _ = _ := by ring

/-- Differentiate an average over random exponential tilts. On a common open neighborhood,
`|E r ω a| ≤ A ω` and `|E' r ω a| ≤ B ω * b a`. Integrability of `b` on the finite base and
`exp (2 A) * B` on the finite environment justifies both differentiation steps. The derivative
is the environment average of the covariance with the energy derivative. -/
theorem hasDerivAt_integral_integral_tilted_of_dominated
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} [IsFiniteMeasure P] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → Ω → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : IsOpen s) (ht : t ∈ s)
    (hE : ∀ r ∈ s, Measurable fun p : Ω × α => E r p.1 p.2)
    (hE' : ∀ r ∈ s, Measurable fun p : Ω × α => E' r p.1 p.2)
    {A B : Ω → ℝ} {b : α → ℝ}
    (hEb : ∀ r ∈ s, ∀ ω a, |E r ω a| ≤ A ω)
    (hb : Integrable b μ)
    (hdb : ∀ r ∈ s, ∀ ω a, |E' r ω a| ≤ B ω * b a)
    (houter : Integrable (fun ω => Real.exp (2 * A ω) * B ω) P)
    (hd : ∀ ω a, ∀ r ∈ s, HasDerivAt (fun q => E q ω a) (E' r ω a) r)
    {F : α → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ a, |F a| ≤ C) :
    HasDerivAt (fun r => ∫ ω, ∫ a, F a ∂μ.tilted (E r ω) ∂P)
      (∫ ω, (∫ a, F a * E' t ω a ∂μ.tilted (E t ω)) -
        (∫ a, F a ∂μ.tilted (E t ω)) * (∫ a, E' t ω a ∂μ.tilted (E t ω)) ∂P) t := by
  let D := fun r ω => (∫ a, F a * E' r ω a ∂μ.tilted (E r ω)) -
    (∫ a, F a ∂μ.tilted (E r ω)) * (∫ a, E' r ω a ∂μ.tilted (E r ω))
  have hmE (r : ℝ) (hr : r ∈ s) (ω : Ω) : Measurable (E r ω) := (hE r hr).of_uncurry_left
  have hmE' (r : ℝ) (hr : r ∈ s) (ω : Ω) : Measurable (E' r ω) := (hE' r hr).of_uncurry_left
  have hiExp (r : ℝ) (hr : r ∈ s) (ω : Ω) : Integrable
      (fun a => Real.exp (E r ω a)) μ :=
    integrable_exp_of_ae_le (hmE r hr ω).aemeasurable
      (ae_of_all _ fun a => le_of_abs_le (hEb r hr ω a))
  have hiE' (r : ℝ) (hr : r ∈ s) (ω : Ω) : Integrable (E' r ω) μ :=
    (hb.const_mul (B ω)).mono' (hmE' r hr ω).aestronglyMeasurable
      (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hdb r hr ω a)
  have hiTilt (r : ℝ) (hr : r ∈ s) (ω : Ω) :
      Integrable (E' r ω) (μ.tilted (E r ω)) :=
    integrable_tilted_of_ae_le (hmE r hr ω).aemeasurable
      (ae_of_all _ fun a => le_of_abs_le (hEb r hr ω a)) (hiE' r hr ω)
  have hmD (r : ℝ) (hr : r ∈ s) : Measurable (D r) := by
    exact (measurable_integral_tilted_dep (hE r hr)
      ((hF.comp measurable_snd).mul (hE' r hr))).sub
      ((measurable_integral_tilted_dep (hE r hr) (hF.comp measurable_snd)).mul
        (measurable_integral_tilted_dep (hE r hr) (hE' r hr)))
  have hcalc (ω : Ω) (r : ℝ) (hr : r ∈ s) :
      HasDerivAt (fun q => ∫ a, F a ∂μ.tilted (E q ω)) (D r ω) r :=
    hasDerivAt_integral_tilted_of_bounded (E := fun q => E q ω) (E' := fun q => E' q ω)
      (hs.mem_nhds hr) (fun q hq => hmE q hq ω) (hmE' r hr ω)
      (fun q hq a => le_of_abs_le (hEb q hq ω a)) (hb.const_mul (B ω))
      (fun q hq a => hdb q hq ω a)
      (fun a q hq => hd ω a q hq) hF hFb
  have hbound (ω : Ω) (r : ℝ) (hr : r ∈ s) :
      |D r ω| ≤ (2 * |C| / μ.real Set.univ * ∫ a, b a ∂μ) *
        (Real.exp (2 * A ω) * B ω) :=
    abs_integral_mul_sub_integral_mul_tilted_le (hmE r hr ω).aemeasurable
      (hEb r hr ω) hb (hdb r hr ω) (hiE' r hr ω) (hiTilt r hr ω) F hFb
  have hiF : Integrable (fun ω => ∫ a, F a ∂μ.tilted (E t ω)) P := by
    refine (integrable_const C).mono'
      (measurable_integral_tilted_dep (hE t ht) (hF.comp measurable_snd)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    simpa only [Real.norm_eq_abs] using abs_integral_tilted_le (hiExp t ht ω) hFb
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r ω => ∫ a, F a ∂μ.tilted (E r ω)) (F' := D)
    (bound := fun ω => (2 * |C| / μ.real Set.univ * ∫ a, b a ∂μ) *
      (Real.exp (2 * A ω) * B ω)) (hs.mem_nhds ht)
    (Filter.mem_of_superset (hs.mem_nhds ht) fun r hr =>
      (measurable_integral_tilted_dep (hE r hr) (hF.comp measurable_snd)).aestronglyMeasurable)
    hiF (hmD t ht).aestronglyMeasurable
    (ae_of_all _ fun ω r hr => by simpa only [Real.norm_eq_abs] using hbound ω r hr)
    (houter.const_mul _) (ae_of_all _ hcalc)).2

/-- Replica version of `hasDerivAt_integral_integral_tilted_of_dominated`: only single-replica
envelopes are assumed. -/
theorem hasDerivAt_integral_integral_pi_tilted_of_dominated
    {Ω α R : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype R]
    {P : Measure Ω} [IsFiniteMeasure P] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → Ω → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : IsOpen s) (ht : t ∈ s)
    (hE : ∀ r ∈ s, Measurable fun p : Ω × α => E r p.1 p.2)
    (hE' : ∀ r ∈ s, Measurable fun p : Ω × α => E' r p.1 p.2)
    {A B : Ω → ℝ} {b : α → ℝ}
    (hEb : ∀ r ∈ s, ∀ ω a, |E r ω a| ≤ A ω)
    (hb : Integrable b μ)
    (hdb : ∀ r ∈ s, ∀ ω a, |E' r ω a| ≤ B ω * b a)
    (houter : Integrable (fun ω => Real.exp (2 * ((Fintype.card R : ℝ) * A ω)) * B ω) P)
    (hd : ∀ ω a, ∀ r ∈ s, HasDerivAt (fun q => E q ω a) (E' r ω a) r)
    {F : (R → α) → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    HasDerivAt (fun r => ∫ ω, ∫ σ, F σ ∂(Measure.pi fun _ : R => μ.tilted (E r ω)) ∂P)
      (∫ ω, (∑ i, ∫ σ : Option R → α, F (fun j => σ (some j)) * E' t ω (σ (some i))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω))) -
        (Fintype.card R : ℝ) * ∫ σ : Option R → α,
          F (fun j => σ (some j)) * E' t ω (σ none)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω)) ∂P) t := by
  let J := fun (r : ℝ) (ω : Ω) (σ : R → α) => ∑ i, E r ω (σ i)
  let J' := fun (r : ℝ) (ω : Ω) (σ : R → α) => ∑ i, E' r ω (σ i)
  let b' := fun σ : R → α => ∑ i, b (σ i)
  have : NeZero (Measure.pi fun _ : R => μ) := neZero_measure_pi μ
  have hmJ (r : ℝ) (hr : r ∈ s) : Measurable fun p : Ω × (R → α) => J r p.1 p.2 := by
    refine Finset.measurable_sum _ fun i _ => ?_
    simpa only [Function.comp_def] using (hE r hr).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmJ' (r : ℝ) (hr : r ∈ s) : Measurable fun p : Ω × (R → α) => J' r p.1 p.2 := by
    refine Finset.measurable_sum _ fun i _ => ?_
    simpa only [Function.comp_def] using (hE' r hr).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hb' : Integrable b' (Measure.pi fun _ : R => μ) :=
    integrable_finsetSum _ fun i _ => integrable_comp_eval hb
  have hres := hasDerivAt_integral_integral_tilted_of_dominated (P := P)
    (μ := Measure.pi fun _ : R => μ) (E := J) (E' := J')
    (A := fun ω => (Fintype.card R : ℝ) * A ω)
    (B := B) (b := b') hs ht hmJ hmJ'
    (fun r hr ω σ => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hEb r hr ω (σ i)))
    hb'
    (fun r hr ω σ => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hdb r hr ω (σ i))
    houter (fun ω σ r hr => HasDerivAt.fun_sum fun i _ => hd ω (σ i) r hr) hF hFb
  simp only [J, ← pi_tilted_eq_tilted_pi] at hres
  convert hres using 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hmEω : Measurable (E t ω) := (hE t ht).of_uncurry_left
  have hiE' : Integrable (E' t ω) μ :=
    (hb.const_mul (B ω)).mono' (hE' t ht).of_uncurry_left.aestronglyMeasurable
      (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hdb t ht ω a)
  have hiTilt : Integrable (E' t ω) (μ.tilted (E t ω)) :=
    integrable_tilted_of_ae_le hmEω.aemeasurable
      (ae_of_all _ fun a => le_of_abs_le (hEb t ht ω a)) hiE'
  have hprob : IsProbabilityMeasure (μ.tilted (E t ω)) :=
    isProbabilityMeasure_tilted_of_ae_le hmEω.aemeasurable
      (ae_of_all _ fun a => le_of_abs_le (hEb t ht ω a))
  have := integral_pi_cov_sum_eq_sum_sub_fresh (μ.tilted (E t ω)) F hF.aestronglyMeasurable hFb
    (E' t ω) hiTilt
  simp only [J']
  exact this.symm

end MeasureTheory
