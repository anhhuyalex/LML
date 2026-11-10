/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPLinear
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted

/-!
# The log-partition function of a Gibbs measure with a linear Gaussian energy

For bounded measurable data and a finite measure `μ ≠ 0`, `z ↦ log ∫ e^{D + ∑ zₖ Xₖ} dμ` is
Fréchet differentiable with partial derivatives the Gibbs averages `⟨Xₗ⟩`.  This is the
first-order companion of `GibbsIBPLinear.lean` and gives the `β`-derivative of the free energy
used in Eq. (1.393) of Talagrand's book.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators

namespace MeasureTheory

variable {α K : Type*} [MeasurableSpace α] [Fintype K] [DecidableEq K] {μ : Measure α}
  [IsFiniteMeasure μ] {D : α → ℝ} {X : K → α → ℝ} {Eb B : ℝ}

/-- **The log-partition function is smooth** with partial derivatives the Gibbs averages. -/
theorem hasFDerivAt_log_partition_linear [NeZero μ]
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hB : 0 ≤ B)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (z₀ : K → ℝ) :
    ∃ L : (K → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun z : K → ℝ => Real.log (∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)) L z₀ ∧
      ∀ l, L (Pi.single l 1) =
        (∫ a, X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) /
          ∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ := by
  obtain ⟨L₂, h₂, hL₂⟩ := hasFDerivAt_integral_mul_exp_linear (μ := μ) (Y := fun _ => 1) hD hX
    measurable_const hB zero_le_one hDb hXb (fun _ => by simp) z₀
  have hi := integrable_exp_linear (μ := μ) hD hX hDb hXb z₀
  have hpos : (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) ≠ 0 := (integral_exp_pos hi).ne'
  have h2' : HasFDerivAt (fun z : K → ℝ => ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ) L₂ z₀ := by
    simpa only [one_mul] using h₂
  refine ⟨(∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ)⁻¹ • L₂, h2'.log hpos, fun l => ?_⟩
  have e2 : (∫ a, 1 * Real.exp (D a + ∑ k, z₀ k * X k a) * X l a ∂μ) =
      ∫ a, X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by ring)
  rw [smul_apply, hL₂ l, e2, smul_eq_mul, inv_mul_eq_div]

omit [DecidableEq K] in
/-- **A uniform bound for the log-partition function**: `|log ∫ e^{D + ∑ zₖ Xₖ} dμ|` is at most
`|log μ(univ)| + Eb + B ∑ |zₖ|`. -/
theorem abs_log_partition_le [NeZero μ] (hD : Measurable D) (hX : ∀ k, Measurable (X k))
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (z : K → ℝ) :
    |Real.log (∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)| ≤
      |Real.log (μ.real univ)| + (Eb + ∑ k, |z k| * B) := by
  set S : ℝ := Eb + ∑ k, |z k| * B with hS
  have hbd : ∀ a, |D a + ∑ k, z k * X k a| ≤ S :=
    fun a => abs_add_sum_mul_le (D a) z (fun k => X k a) (hDb a) (fun k => hXb k a)
  have hi := integrable_exp_linear (μ := μ) hD hX hDb hXb z
  have hpos : 0 < ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ := integral_exp_pos hi
  have hμ : 0 < μ.real univ := measureReal_univ_pos
  have hup : ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ ≤ Real.exp S * μ.real univ := by
    have := integral_mono hi (integrable_const (Real.exp S)) fun a =>
      Real.exp_le_exp.2 ((le_abs_self _).trans (hbd a))
    simpa [mul_comm] using this
  have hlow : Real.exp (-S) * μ.real univ ≤ ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ := by
    have := integral_mono (integrable_const (Real.exp (-S))) hi fun a =>
      Real.exp_le_exp.2 (by linarith [neg_abs_le (D a + ∑ k, z k * X k a), hbd a])
    simpa [mul_comm] using this
  have h1 : Real.log (∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ) ≤
      S + Real.log (μ.real univ) := by
    calc _ ≤ Real.log (Real.exp S * μ.real univ) := Real.log_le_log hpos hup
      _ = S + Real.log (μ.real univ) := by
        rw [Real.log_mul (Real.exp_pos _).ne' hμ.ne', Real.log_exp]
  have h2 : -S + Real.log (μ.real univ) ≤
      Real.log (∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ) := by
    calc -S + Real.log (μ.real univ) = Real.log (Real.exp (-S) * μ.real univ) := by
          rw [Real.log_mul (Real.exp_pos _).ne' hμ.ne', Real.log_exp]
      _ ≤ _ := Real.log_le_log (mul_pos (Real.exp_pos _) hμ) hlow
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le (Real.log (μ.real univ)), le_abs_self (Real.log (μ.real univ))]

omit [DecidableEq K] in
/-- **Derivative of the expected log-partition function along a random path of parameters.**
If `z s ω` is differentiable in `s` near `t` with derivative `z' s ω` dominated by an integrable
function, and `z t · ` is integrable, then
`s ↦ 𝔼 log ∫ e^{D + ∑ₖ z_k(s) Xₖ} dμ` has derivative `𝔼 ∑ₗ z'ₗ ⟨Xₗ⟩` at `t`. -/
theorem hasDerivAt_integral_log_partition_path [NeZero μ] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hB : 0 ≤ B)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B)
    {z z' : ℝ → Ω → K → ℝ} {t δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ ω, ∀ s ∈ Metric.ball t δ, HasDerivAt (fun r => z r ω) (z' s ω) s)
    (hzm : ∀ s, Measurable (z s)) (hz'm : Measurable (z' t))
    (hzi : ∀ l, Integrable (fun ω => z t ω l) P)
    {g : Ω → ℝ} (hg : Integrable g P)
    (hgb : ∀ ω, ∀ s ∈ Metric.ball t δ, ∀ l, |z' s ω l| ≤ g ω) :
    HasDerivAt (fun s => ∫ ω, Real.log (∫ a, Real.exp (D a + ∑ k, z s ω k * X k a) ∂μ) ∂P)
      (∫ ω, ∑ l, z' t ω l * ((∫ a, X l a * Real.exp (D a + ∑ k, z t ω k * X k a) ∂μ) /
        ∫ a, Real.exp (D a + ∑ k, z t ω k * X k a) ∂μ) ∂P) t := by
  classical
  set Pf : (K → ℝ) → ℝ := fun w => Real.log (∫ a, Real.exp (D a + ∑ k, w k * X k a) ∂μ)
    with hPf
  set Rx : K → (K → ℝ) → ℝ := fun l w => (∫ a, X l a * Real.exp (D a + ∑ k, w k * X k a) ∂μ) /
    ∫ a, Real.exp (D a + ∑ k, w k * X k a) ∂μ with hRx
  have hRxb : ∀ l w, |Rx l w| ≤ B := fun l w => by
    have := abs_gibbs_ratio_le (μ := μ) (Y := X l) hD hX hDb hXb (hXb l) w
    simpa [hRx] using this
  have hPfd : ∀ w₀, ∃ L : (K → ℝ) →L[ℝ] ℝ, HasFDerivAt Pf L w₀ ∧
      ∀ l, L (Pi.single l 1) = Rx l w₀ := fun w₀ =>
    hasFDerivAt_log_partition_linear (μ := μ) hD hX hB hDb hXb w₀
  have hPfc : Continuous Pf := continuous_iff_continuousAt.2 fun w₀ =>
    (hPfd w₀).choose_spec.1.continuousAt
  have hRxc : ∀ l, Continuous (Rx l) := fun l => by
    refine continuous_iff_continuousAt.2 fun w₀ => ?_
    obtain ⟨L, hL, -⟩ := hasFDerivAt_gibbs_ratio_linear (μ := μ) (Y := X l) hD hX (hX l) hB hB
      hDb hXb (hXb l) w₀
    have : Rx l = fun w => (∫ a, X l a * Real.exp (D a + ∑ k, w k * X k a) ∂μ) /
        ∫ a, Real.exp (D a + ∑ k, w k * X k a) ∂μ := rfl
    rw [this]
    exact hL.continuousAt
  have hmeasF : ∀ s, Measurable fun ω => Pf (z s ω) := fun s => hPfc.measurable.comp (hzm s)
  have hmeasF' : Measurable fun ω => ∑ l, z' t ω l * Rx l (z t ω) :=
    Finset.measurable_sum _ fun l _ => ((measurable_pi_apply l).comp hz'm).mul
      ((hRxc l).measurable.comp (hzm t))
  have hFint : Integrable (fun ω => Pf (z t ω)) P := by
    have hdom : Integrable (fun ω => |Real.log (μ.real univ)| + (Eb + ∑ l, |z t ω l| * B)) P :=
      (integrable_const _).add ((integrable_const Eb).add
        (integrable_finsetSum _ fun l _ => (hzi l).abs.mul_const B))
    refine hdom.mono' (hmeasF t).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_log_partition_le hD hX hDb hXb (z t ω)
  have hbound : ∀ ω, ∀ s ∈ Metric.ball t δ, ‖∑ l, z' s ω l * Rx l (z s ω)‖ ≤
      (Fintype.card K * B) * g ω := by
    intro ω s hs
    rw [Real.norm_eq_abs]
    calc |∑ l, z' s ω l * Rx l (z s ω)| ≤ ∑ l, |z' s ω l * Rx l (z s ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : K, g ω * B := Finset.sum_le_sum fun l _ => by
          rw [abs_mul]
          exact mul_le_mul (hgb ω s hs l) (hRxb l _) (abs_nonneg _)
            ((abs_nonneg _).trans (hgb ω s hs l))
      _ = (Fintype.card K * B) * g ω := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => Pf (z s ω)) (F' := fun s ω => ∑ l, z' s ω l * Rx l (z s ω))
    (s := Metric.ball t δ) (x₀ := t) (Metric.ball_mem_nhds t hδ)
    (Eventually.of_forall fun s => (hmeasF s).aestronglyMeasurable) hFint
    hmeasF'.aestronglyMeasurable (ae_of_all _ fun ω s hs => hbound ω s hs)
    (hg.const_mul _) (ae_of_all _ fun ω s hs => ?_)
  · exact this.2
  · obtain ⟨L, hL, hLl⟩ := hPfd (z s ω)
    refine (hL.comp_hasDerivAt s (hz ω s hs)).congr_deriv ?_
    have hz' : z' s ω = ∑ l, z' s ω l • (Pi.single l 1 : K → ℝ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hz', map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, hLl l, smul_eq_mul]

omit [DecidableEq K] in
/-- **Continuity of the expected log-partition function along a random path of parameters.**  If
`s ↦ z s ω` is continuous for every `ω` and the coordinates are dominated by an integrable
function, then `s ↦ 𝔼 log ∫ e^{D + ∑ zₖ(s) Xₖ} dμ` is continuous. -/
theorem continuous_integral_log_partition_path [NeZero μ] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hD : Measurable D) (hX : ∀ k, Measurable (X k))
    (hB : 0 ≤ B) (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B)
    {z : ℝ → Ω → K → ℝ} (hzc : ∀ ω, Continuous fun s => z s ω) (hzm : ∀ s, Measurable (z s))
    {g : Ω → ℝ} (hg : Integrable g P) (hgb : ∀ s ω l, |z s ω l| ≤ g ω) :
    Continuous (fun s => ∫ ω, Real.log (∫ a, Real.exp (D a + ∑ k, z s ω k * X k a) ∂μ) ∂P) := by
  classical
  set Pf : (K → ℝ) → ℝ := fun w => Real.log (∫ a, Real.exp (D a + ∑ k, w k * X k a) ∂μ)
    with hPf
  have hPfc : Continuous Pf := continuous_iff_continuousAt.2 fun w₀ =>
    (hasFDerivAt_log_partition_linear (μ := μ) hD hX hB hDb hXb w₀).choose_spec.1.continuousAt
  refine continuous_of_dominated (bound := fun ω => |Real.log (μ.real univ)| + (Eb + ∑ _k : K, g ω
      * B))
    (fun s => (hPfc.measurable.comp (hzm s)).aestronglyMeasurable) (fun s => ae_of_all _ fun ω =>
        ?_)
    ?_ (ae_of_all _ fun ω => hPfc.comp (continuous_pi_iff.2 fun _ => ?_))
  · rw [Real.norm_eq_abs]
    refine (abs_log_partition_le (μ := μ) hD hX hDb hXb (z s ω)).trans ?_
    refine add_le_add le_rfl (add_le_add le_rfl (Finset.sum_le_sum fun k _ => ?_))
    exact mul_le_mul_of_nonneg_right ((hgb s ω k).trans' (le_of_eq rfl)) hB
  · exact (integrable_const _).add ((integrable_const _).add (integrable_finsetSum _ fun k _ =>
      hg.mul_const B))
  · exact continuous_pi_iff.1 (hzc ω) _

end MeasureTheory
