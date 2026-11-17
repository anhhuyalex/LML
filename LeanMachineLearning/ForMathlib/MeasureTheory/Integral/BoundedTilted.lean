/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.ProdBound
public import Mathlib.Probability.Moments.Tilted
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

/-- Bound a constant plus a finite weighted sum. This is the energy bound used by
Gaussian cavity paths, with the weights supplied by the path. -/
theorem abs_add_sum_mul_le {K : Type*} [Fintype K] (D : ℝ) (z X : K → ℝ)
    {Eb B : ℝ} (hD : |D| ≤ Eb) (hX : ∀ k, |X k| ≤ B) :
    |D + ∑ k, z k * X k| ≤ Eb + ∑ k, |z k| * B := by
  calc
    _ ≤ |D| + |∑ k, z k * X k| := abs_add_le _ _
    _ ≤ Eb + (∑ k, |z k|) * B :=
      add_le_add hD (Weights.abs_weighted_sum_le z X hX)
    _ = _ := by rw [Finset.sum_mul]

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

/-- Differentiate a bounded observable's unnormalized exponential moment on an arbitrary
finite measure space. Only almost everywhere bounds and measurability are required. -/
theorem hasDerivAt_integral_mul_exp_mul_of_ae_abs_le
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXbound : ∀ᵐ a ∂μ, |X a| ≤ C) (hYbound : ∀ᵐ a ∂μ, |Y a| ≤ B) (t : ℝ) :
    HasDerivAt (fun s => ∫ a, Y a * Real.exp (s * X a) ∂μ)
      (∫ a, Y a * Real.exp (t * X a) * X a ∂μ) t := by
  have hi (s : ℝ) : Integrable (fun a => Real.exp (s * X a)) μ := by
    have hs : s ∈ integrableExpSet X μ := by
      rw [integrableExpSet_eq_univ_of_ae_abs_le hX hXbound]
      trivial
    exact hs
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s a => Y a * Real.exp (s * X a))
    (F' := fun s a => Y a * Real.exp (s * X a) * X a)
    (s := Ioo (t - 1) (t + 1)) (bound := fun _ =>
      |B| * Real.exp ((|t| + 1) * |C|) * |C|)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (hY.mul (hX.const_mul s).exp).aestronglyMeasurable)
    ((hi t).bdd_mul hY.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hYbound))
    ((hY.mul (hX.const_mul t).exp).mul hX).aestronglyMeasurable ?_
    (integrable_const _) ?_).2
  · filter_upwards [hXbound, hYbound] with a hx hy
    intro s hs
    have hsabs : |s| ≤ |t| + 1 := abs_le.mpr ⟨by
      linarith [neg_abs_le t, hs.1], by linarith [le_abs_self t, hs.2]⟩
    have hexp : Real.exp (s * X a) ≤ Real.exp ((|t| + 1) * |C|) := by
      apply Real.exp_le_exp.mpr
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul hsabs (hx.trans (le_abs_self C)) (abs_nonneg _) (by positivity)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul
      (mul_le_mul (hy.trans (le_abs_self B)) hexp (Real.exp_pos _).le (abs_nonneg _))
      (hx.trans (le_abs_self C)) (abs_nonneg _) (by positivity)
  · exact Eventually.of_forall fun a s _ => by
      simpa only [mul_assoc, id_eq, one_mul] using
        (((hasDerivAt_id s).mul_const (X a)).exp.const_mul (Y a))

/-- Linear response of a bounded observable under exponential tilting: the derivative
is the tilted covariance with the energy. The base measure may be any nonzero finite
measure, and the formula holds at every real parameter. -/
theorem hasDerivAt_integral_tilted_mul_of_ae_abs_le [NeZero μ]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXbound : ∀ᵐ a ∂μ, |X a| ≤ C) (hYbound : ∀ᵐ a ∂μ, |Y a| ≤ B) (t : ℝ) :
    HasDerivAt (fun s => ∫ a, Y a ∂(μ.tilted (fun a => s * X a)))
      ((∫ a, Y a * X a ∂(μ.tilted (fun a => t * X a))) -
        (∫ a, Y a ∂(μ.tilted (fun a => t * X a))) *
          ∫ a, X a ∂(μ.tilted (fun a => t * X a))) t := by
  have ht : t ∈ interior (integrableExpSet X μ) := by
    simp [integrableExpSet_eq_univ_of_ae_abs_le hX hXbound]
  have hZ : mgf X μ t ≠ 0 := (mgf_pos' (NeZero.ne μ) (interior_subset ht)).ne'
  have hmean (s : ℝ) (f : α → ℝ) :
      (∫ a, f a ∂(μ.tilted (fun a => s * X a))) =
        (∫ a, f a * Real.exp (s * X a) ∂μ) / mgf X μ s := by
    rw [integral_tilted_mul_eq_mgf]
    simp only [smul_eq_mul, div_mul_eq_mul_div]
    rw [integral_div]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun a => mul_comm _ _)
  have hnum := hasDerivAt_integral_mul_exp_mul_of_ae_abs_le hX hY hXbound hYbound t
  have hswap : (∫ a, Y a * Real.exp (t * X a) * X a ∂μ) =
      ∫ a, (Y a * X a) * Real.exp (t * X a) ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by ring)
  simp_rw [hmean]
  convert hnum.div (hasDerivAt_mgf ht) hZ using 1
  rw [hswap]
  generalize (∫ a, Y a * X a * Real.exp (t * X a) ∂μ) = A
  generalize (∫ a, Y a * Real.exp (t * X a) ∂μ) = D
  generalize (∫ a, X a * Real.exp (t * X a) ∂μ) = E
  generalize mgf X μ t = Z at hZ ⊢
  field_simp

/-- The integral against the tilted probability measure written as a quotient of integrals. -/
theorem integral_tilted_eq_div {α : Type*} [MeasurableSpace α] {μ : Measure α} (e Y : α → ℝ) :
    ∫ a, Y a ∂(μ.tilted e) = (∫ a, Y a * Real.exp (e a) ∂μ) / ∫ a, Real.exp (e a) ∂μ := by
  rw [integral_tilted, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [smul_eq_mul]
  ring

/-- The derivative of an observable under a varying exponential tilt is its covariance with
the energy derivative. An integrable bound on the weighted derivative justifies differentiating
numerator and normalizer. The observable is bounded and does not vary with the parameter.
The nonzero base measure need not be finite. -/
theorem hasDerivAt_integral_tilted_of_dominated {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [NeZero μ]
    {e e' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun a => Real.exp (e r a)) μ)
    (hi : Integrable (fun a => Real.exp (e t a)) μ)
    (hdm : AEStronglyMeasurable (fun a => e' t a * Real.exp (e t a)) μ)
    {b : α → ℝ} (hb : Integrable b μ)
    (hdb : ∀ᵐ a ∂μ, ∀ r ∈ s, |e' r a * Real.exp (e r a)| ≤ b a)
    (hd : ∀ᵐ a ∂μ, ∀ r ∈ s, HasDerivAt (fun q => e q a) (e' r a) r)
    {F : α → ℝ} (hF : AEStronglyMeasurable F μ) {C : ℝ}
    (hFb : ∀ᵐ a ∂μ, |F a| ≤ C) :
    HasDerivAt (fun r => ∫ a, F a ∂μ.tilted (e r))
      ((∫ a, F a * e' t a ∂μ.tilted (e t)) -
        (∫ a, F a ∂μ.tilted (e t)) * ∫ a, e' t a ∂μ.tilted (e t)) t := by
  have hden := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hi hdm
    (by simpa only [Real.norm_eq_abs] using hdb) hb
    (hd.mono fun a ha r hr => by simpa only [mul_comm] using (ha r hr).exp)
  have hnum := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (hmeas.mono fun r hr => hF.mul hr)
    (hi.bdd_mul hF (by simpa only [Real.norm_eq_abs] using hFb)) (hF.mul hdm)
    (bound := fun a => |C| * b a)
    (by
      filter_upwards [hdb, hFb] with a hda hFa r hr
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFa.trans (le_abs_self C)) (hda r hr) (abs_nonneg _) (abs_nonneg _))
    (hb.const_mul |C|)
    (hd.mono fun a ha r hr => by
      simpa only [Pi.mul_apply, mul_comm] using ((ha r hr).exp.const_mul (F a)))
  simp_rw [integral_tilted_eq_div]
  convert hnum.2.div hden.2 (integral_exp_pos hi).ne' using 1
  have hprod : (∫ a, F a * (e' t a * Real.exp (e t a)) ∂μ) =
      ∫ a, F a * e' t a * Real.exp (e t a) ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ fun a => by ring
  simp only [Pi.mul_apply]
  rw [hprod]
  field_simp [(integral_exp_pos hi).ne']

/-- An upper energy bound converts an unweighted integrable derivative envelope into the
weighted envelope needed to differentiate an exponential tilt on a finite base measure. -/
theorem hasDerivAt_integral_tilted_of_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {A : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ A)
    {b : α → ℝ} (hb : Integrable b μ) (hb0 : ∀ a, 0 ≤ b a)
    (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F : α → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ a, |F a| ≤ C) :
    HasDerivAt (fun r => ∫ a, F a ∂μ.tilted (E r))
      ((∫ a, F a * E' t a ∂μ.tilted (E t)) -
        (∫ a, F a ∂μ.tilted (E t)) * ∫ a, E' t a ∂μ.tilted (E t)) t := by
  have ht := mem_of_mem_nhds hs
  exact hasDerivAt_integral_tilted_of_dominated (e := E) (e' := E') hs
    (Filter.mem_of_superset hs fun r hr => (hE r hr).exp.aestronglyMeasurable)
    (integrable_exp_of_ae_le (hE t ht).aemeasurable (ae_of_all _ (hEb t ht)))
    (hE'.mul (hE t ht).exp).aestronglyMeasurable (hb.const_mul (Real.exp A))
    (ae_of_all _ fun a r hr => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul (hdb r hr a) (Real.exp_le_exp.mpr (hEb r hr a))
        (Real.exp_pos _).le (hb0 a)).trans_eq (mul_comm _ _))
    (ae_of_all _ hd) hF.aestronglyMeasurable (ae_of_all _ hFb)

/-- A bounded log-density controls a possibly unbounded tilted observable by its base first
moment. The denominator bound retains the mass of a nonzero finite base measure. -/
theorem abs_integral_tilted_le_exp_mul_integral_abs {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
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
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (le_of_abs_le ha)) (abs_nonneg _)).trans_eq
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

end MeasureTheory
