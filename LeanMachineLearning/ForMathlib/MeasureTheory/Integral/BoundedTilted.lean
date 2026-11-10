/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Tactic.Linarith

/-!
# Bounded energies on arbitrary finite measure spaces

These estimates and derivatives use Mathlib's exponential tilt directly. The spin space
need not be finite, and bounds and measurability are only required almost everywhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {C : ℝ}

/-- An almost everywhere upper bound on a real energy gives exponential integrability
against any finite measure. A lower bound is unnecessary. -/
theorem integrable_exp_of_ae_le [IsFiniteMeasure μ] (hf : AEMeasurable f μ)
    (hbound : ∀ᵐ a ∂μ, f a ≤ C) : Integrable (fun a => Real.exp (f a)) μ := by
  refine (integrable_const (Real.exp C)).mono' hf.exp.aestronglyMeasurable ?_
  filter_upwards [hbound] with a ha
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ha

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

end MeasureTheory
