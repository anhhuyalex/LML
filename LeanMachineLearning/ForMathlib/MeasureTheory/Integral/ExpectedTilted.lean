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

/-- Differentiate an average over random exponential tilts of a vector-valued observable. On a
neighbourhood of `t`, `|E r ω a| ≤ A ω` and `|E' r ω a| ≤ B ω * b a` almost everywhere.
Integrability of `b` on the finite base and `exp (2 A) * B` on the finite environment justifies
both differentiation steps. The derivative is the environment average of the covariance with the
energy derivative. -/
theorem hasDerivAt_integral_integral_tilted_smul_of_dominated
    {Ω α V : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {P : Measure Ω} [IsFiniteMeasure P] {μ : Measure α} [IsFiniteMeasure μ]
    [NeZero μ] {E E' : ℝ → Ω → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable fun p : Ω × α => E r p.1 p.2)
    (hE' : ∀ r ∈ s, Measurable fun p : Ω × α => E' r p.1 p.2)
    {A B : Ω → ℝ} {b : α → ℝ}
    (hEb : ∀ᵐ ω ∂P, ∀ᵐ a ∂μ, ∀ r ∈ s, |E r ω a| ≤ A ω)
    (hb : Integrable b μ)
    (hdb : ∀ᵐ ω ∂P, ∀ᵐ a ∂μ, ∀ r ∈ s, |E' r ω a| ≤ B ω * b a)
    (houter : Integrable (fun ω => Real.exp (2 * A ω) * B ω) P)
    (hd : ∀ᵐ ω ∂P, ∀ᵐ a ∂μ, ∀ r ∈ s, HasDerivAt (fun q => E q ω a) (E' r ω a) r)
    {F : α → V} (hF : StronglyMeasurable F) {C : ℝ} (hFb : ∀ᵐ a ∂μ, ‖F a‖ ≤ C) :
    HasDerivAt (fun r => ∫ ω, ∫ a, F a ∂μ.tilted (E r ω) ∂P)
      (∫ ω, (∫ a, E' t ω a • F a ∂μ.tilted (E t ω)) -
        (∫ a, E' t ω a ∂μ.tilted (E t ω)) • (∫ a, F a ∂μ.tilted (E t ω)) ∂P) t := by
  set u := interior s with hu
  have huo : IsOpen u := isOpen_interior
  have htu : t ∈ u := mem_interior_iff_mem_nhds.2 hs
  have hus : u ⊆ s := interior_subset
  set D := fun r ω => (∫ a, E' r ω a • F a ∂μ.tilted (E r ω)) -
    (∫ a, E' r ω a ∂μ.tilted (E r ω)) • (∫ a, F a ∂μ.tilted (E r ω)) with hD
  have hmE (r : ℝ) (hr : r ∈ s) (ω : Ω) : Measurable (E r ω) := (hE r hr).of_uncurry_left
  have hmE' (r : ℝ) (hr : r ∈ s) (ω : Ω) : Measurable (E' r ω) := (hE' r hr).of_uncurry_left
  have hFp : StronglyMeasurable fun p : Ω × α => F p.2 := hF.comp_measurable measurable_snd
  have hmF (r : ℝ) (hr : r ∈ s) :
      StronglyMeasurable fun ω => ∫ a, F a ∂μ.tilted (E r ω) :=
    stronglyMeasurable_integral_tilted_dep (hE r hr) hFp
  have hmD (r : ℝ) (hr : r ∈ s) : StronglyMeasurable (D r) :=
    (stronglyMeasurable_integral_tilted_dep (hE r hr)
      ((hE' r hr).stronglyMeasurable.smul hFp)).sub
      ((stronglyMeasurable_integral_tilted_dep (hE r hr)
        (hE' r hr).stronglyMeasurable).smul (hmF r hr))
  have hm : 0 < μ.real Set.univ := measureReal_univ_pos
  have hae : ∀ᵐ ω ∂P, ∀ r ∈ u,
      HasDerivAt (fun q => ∫ a, F a ∂μ.tilted (E q ω)) (D r ω) r ∧
        ‖D r ω‖ ≤ (2 * |C| / μ.real Set.univ * ∫ a, b a ∂μ) *
          (Real.exp (2 * A ω) * B ω) := by
    filter_upwards [hEb, hdb, hd] with ω h1 h2 h3 r hr
    have hrs := hus hr
    have heb : ∀ᵐ a ∂μ, |E r ω a| ≤ A ω := h1.mono fun a h => h r hrs
    have heub : ∀ᵐ a ∂μ, E r ω a ≤ A ω := heb.mono fun a h => le_of_abs_le h
    have hiE' : Integrable (E' r ω) μ :=
      (hb.const_mul (B ω)).mono' (hmE' r hrs ω).aestronglyMeasurable
        (h2.mono fun a h => by simpa only [Real.norm_eq_abs] using h r hrs)
    refine ⟨hasDerivAt_integral_tilted_of_ae_bounded (E := fun q => E q ω)
      (E' := fun q => E' q ω) (huo.mem_nhds hr)
      (fun q hq => (hmE q (hus hq) ω).aestronglyMeasurable) (hmE' r hrs ω).aestronglyMeasurable
      (h1.mono fun a h q hq => le_of_abs_le (h q (hus hq))) (hb.const_mul (B ω))
      (h2.mono fun a h q hq => h q (hus hq)) (h3.mono fun a h q hq => h q (hus hq))
      hF.aestronglyMeasurable hFb, ?_⟩
    have hiExp := integrable_exp_of_ae_le (hmE r hrs ω).aemeasurable heub
    have : IsProbabilityMeasure (μ.tilted (E r ω)) := isProbabilityMeasure_tilted hiExp
    have hFt : ∀ᵐ a ∂μ.tilted (E r ω), ‖F a‖ ≤ |C| :=
      (tilted_absolutelyContinuous μ _).ae_le (hFb.mono fun a h => h.trans (le_abs_self C))
    have hiYt : Integrable (E' r ω) (μ.tilted (E r ω)) :=
      integrable_tilted_of_ae_le (hmE r hrs ω).aemeasurable heub hiE'
    have h4 : ‖∫ a, E' r ω a • F a ∂μ.tilted (E r ω)‖ ≤
        |C| * ∫ a, |E' r ω a| ∂μ.tilted (E r ω) := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hiYt.abs.const_mul _) (hFt.mono fun a h => ?_)
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    have h5 : ‖(∫ a, E' r ω a ∂μ.tilted (E r ω)) • (∫ a, F a ∂μ.tilted (E r ω))‖ ≤
        |C| * ∫ a, |E' r ω a| ∂μ.tilted (E r ω) := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul (norm_integral_tilted_le_of_ae_norm_le hiExp
        (hFb.mono fun a h => h.trans (le_abs_self C))) abs_integral_le_integral_abs
        (abs_nonneg _) (abs_nonneg _)
    have h6 : ∫ a, |E' r ω a| ∂μ.tilted (E r ω) ≤
        Real.exp (2 * A ω) / μ.real Set.univ * (B ω * ∫ a, b a ∂μ) := by
      have htilt := abs_integral_tilted_le_exp_mul_integral_abs (hmE r hrs ω).aemeasurable
        heb hiE'.abs
      simp only [abs_abs] at htilt
      refine (le_abs_self _).trans (htilt.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
      rw [← integral_const_mul]
      exact integral_mono_ae hiE'.abs (hb.const_mul _) (h2.mono fun a h => h r hrs)
    calc ‖D r ω‖ ≤ |C| * (∫ a, |E' r ω a| ∂μ.tilted (E r ω)) +
          |C| * ∫ a, |E' r ω a| ∂μ.tilted (E r ω) :=
          (norm_sub_le _ _).trans (add_le_add h4 h5)
      _ = 2 * |C| * ∫ a, |E' r ω a| ∂μ.tilted (E r ω) := by ring
      _ ≤ 2 * |C| * (Real.exp (2 * A ω) / μ.real Set.univ * (B ω * ∫ a, b a ∂μ)) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = _ := by ring
  have hiF : Integrable (fun ω => ∫ a, F a ∂μ.tilted (E t ω)) P := by
    refine (integrable_const |C|).mono' (hmF t (hus htu)).aestronglyMeasurable
      (hEb.mono fun ω h => ?_)
    exact norm_integral_tilted_le_of_ae_norm_le
      (integrable_exp_of_ae_le (hmE t (hus htu) ω).aemeasurable
        (h.mono fun a h => le_of_abs_le (h t (hus htu))))
      (hFb.mono fun a h => h.trans (le_abs_self C))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r ω => ∫ a, F a ∂μ.tilted (E r ω)) (F' := D)
    (bound := fun ω => (2 * |C| / μ.real Set.univ * ∫ a, b a ∂μ) *
      (Real.exp (2 * A ω) * B ω)) (huo.mem_nhds htu)
    (Filter.eventually_of_mem (huo.mem_nhds htu) fun r hr =>
      (hmF r (hus hr)).aestronglyMeasurable)
    hiF (hmD t (hus htu)).aestronglyMeasurable
    (hae.mono fun ω h r hr => (h r hr).2)
    (houter.const_mul _) (hae.mono fun ω h r hr => (h r hr).1)).2

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
  have h := hasDerivAt_integral_integral_tilted_smul_of_dominated (P := P) (μ := μ)
    (hs.mem_nhds ht) hE hE'
    (ae_of_all _ fun ω => ae_of_all _ fun a r hr => hEb r hr ω a) hb
    (ae_of_all _ fun ω => ae_of_all _ fun a r hr => hdb r hr ω a) houter
    (ae_of_all _ fun ω => ae_of_all _ (hd ω)) hF.stronglyMeasurable (C := C)
    (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hFb a)
  simpa only [smul_eq_mul, mul_comm] using h

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
  have hiTilt : Integrable (E' t ω) (μ.tilted (E t ω)) :=
    integrable_tilted_of_abs_le_envelope hmEω.aemeasurable
      (hE' t ht).of_uncurry_left.aestronglyMeasurable (hb.const_mul (B ω))
      (ae_of_all _ fun a => le_of_abs_le (hEb t ht ω a)) (ae_of_all _ (hdb t ht ω))
  have hprob : IsProbabilityMeasure (μ.tilted (E t ω)) :=
    isProbabilityMeasure_tilted_of_ae_le hmEω.aemeasurable
      (ae_of_all _ fun a => le_of_abs_le (hEb t ht ω a))
  have := integral_pi_cov_sum_eq_sum_sub_fresh (μ.tilted (E t ω)) F hF.aestronglyMeasurable hFb
    (E' t ω) hiTilt
  simp only [J']
  exact this.symm

end MeasureTheory
