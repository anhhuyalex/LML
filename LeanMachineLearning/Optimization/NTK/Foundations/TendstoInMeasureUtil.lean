/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Small Calculus for Convergence in Measure of Real Sequences

Elementary closure properties of `TendstoInMeasure` for real-valued sequences, used throughout the
deep backward-concentration argument (`Deep/`):

* `tendstoInMeasure_const`, `tendstoInMeasure_add`, `tendstoInMeasure_sub`;
* `tendstoInMeasure_zero_of_abs_le`: domination by a sequence tending to `0` in measure;
* `tendstoInMeasure_congr_of_measure_ne_tendsto`: changing a sequence on events whose measure tends
  to `0` does not change the limit (used for the "`Φᵀ Φ` is invertible" good event);
* `tendsto_lintegral_min_one_ofReal`, `tendsto_measure_of_le_lintegral_min_one`: if
  `P(Eₙ) ≤ ∫ min 1 (bₙ)` with `bₙ → 0` in measure, then `P(Eₙ) → 0` (the shape of the conditional
  Chebyshev bounds of `Initialization/GaussianConditioning.lean`).
-/

@[expose]
public section

open MeasureTheory Filter
open scoped ENNReal

namespace NTK

section real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A constant sequence converges in measure to its constant. -/
theorem tendstoInMeasure_const (c : ℝ) :
    TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => c) atTop (fun _ => c) :=
  fun ε hε => by simp [edist_self, hε.ne']

/-- Convergence in measure from a pointwise bound by a sum of two distances. -/
theorem tendstoInMeasure_of_dist_le_add {f g h : ℕ → Ω → ℝ} {a b c : ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => a)) (hg : TendstoInMeasure μ g atTop (fun _ => b))
    (hle : ∀ n ω, dist (h n ω) c ≤ dist (f n ω) a + dist (g n ω) b) :
    TendstoInMeasure μ h atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist] at hf hg ⊢
  intro ε hε
  have h2 : 0 < ε / 2 := by linarith
  have hsum := (hf (ε / 2) h2).add (hg (ε / 2) h2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hsum)
    (fun _ => zero_le) fun n => ?_
  refine le_trans (measure_mono fun ω hω => ?_) (measure_union_le _ _)
  by_contra hne
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hne hω
  linarith [hle n ω, hne.1, hne.2]

/-- Sums of sequences converging in measure. -/
theorem tendstoInMeasure_add {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => a)) (hg : TendstoInMeasure μ g atTop (fun _ => b)) :
    TendstoInMeasure μ (fun n ω => f n ω + g n ω) atTop (fun _ => a + b) :=
  tendstoInMeasure_of_dist_le_add hf hg fun _ _ => dist_add_add_le _ _ _ _

/-- Differences of sequences converging in measure. -/
theorem tendstoInMeasure_sub {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => a)) (hg : TendstoInMeasure μ g atTop (fun _ => b)) :
    TendstoInMeasure μ (fun n ω => f n ω - g n ω) atTop (fun _ => a - b) :=
  tendstoInMeasure_of_dist_le_add hf hg fun _ _ => dist_sub_sub_le _ _ _ _

/-- **Domination.** If `|f n ω| ≤ g n ω` and `g n → 0` in measure then `f n → 0` in measure. -/
theorem tendstoInMeasure_zero_of_abs_le {f g : ℕ → Ω → ℝ}
    (hfg : ∀ n ω, |f n ω| ≤ g n ω) (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε)
    (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  exact hω.trans ((hfg n ω).trans (le_abs_self _))

/-- **Domination of the square.** If `(f n ω)² ≤ g n ω` and `g n → 0` in measure then `f n → 0`
in measure. -/
theorem tendstoInMeasure_zero_of_sq_le {f g : ℕ → Ω → ℝ}
    (hfg : ∀ n ω, f n ω ^ 2 ≤ g n ω) (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg (ε ^ 2) (by positivity))
    (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  have h1 : ε ^ 2 ≤ |f n ω| ^ 2 := pow_le_pow_left₀ hε.le hω 2
  rw [sq_abs] at h1
  exact h1.trans ((hfg n ω).trans (le_abs_self _))

/-- A deterministic real sequence converging to `a` converges in measure to `a`. -/
theorem tendstoInMeasure_of_tendsto {c : ℕ → ℝ} {a : ℝ} (h : Tendsto c atTop (nhds a)) :
    TendstoInMeasure μ (fun n (_ : Ω) => c n) atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hev : ∀ᶠ n in atTop, dist (c n) a < ε := (Metric.tendsto_nhds.1 h) ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  have : {ω : Ω | ε ≤ dist (c n) a} = ∅ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]; exact hn
  rw [this, measure_empty]

/-- **Domination of the square on a good event.** If `(f n ω)² ≤ g n ω` whenever `ω ∈ good n`,
`g n → 0` in measure and `μ (good n)ᶜ → 0`, then `f n → 0` in measure. -/
theorem tendstoInMeasure_zero_of_sq_le_on_good {f g : ℕ → Ω → ℝ} {good : ℕ → Set Ω}
    (hfg : ∀ n ω, ω ∈ good n → f n ω ^ 2 ≤ g n ω)
    (hg : TendstoInMeasure μ g atTop (fun _ => 0))
    (hbad : Tendsto (fun n => μ (good n)ᶜ) atTop (nhds 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  have hsum := (hg (ε ^ 2) (by positivity)).add hbad
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hsum)
    (fun _ => zero_le) fun n => ?_
  refine le_trans (measure_mono fun ω hω => ?_) (measure_union_le _ _)
  by_cases h : ω ∈ good n
  · left
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
    have h1 : ε ^ 2 ≤ |f n ω| ^ 2 := pow_le_pow_left₀ hε.le hω 2
    rw [sq_abs] at h1
    exact h1.trans ((hfg n ω h).trans (le_abs_self _))
  · exact Or.inr h

/-- **Changing a sequence on a vanishing event.** If `μ {f n ≠ g n} → 0` and `f n → c` in measure
then `g n → c` in measure. -/
theorem tendstoInMeasure_congr_of_measure_ne_tendsto {f g : ℕ → Ω → ℝ} {c : ℝ}
    (hne : Tendsto (fun n => μ {ω | f n ω ≠ g n ω}) atTop (nhds 0))
    (hf : TendstoInMeasure μ f atTop (fun _ => c)) :
    TendstoInMeasure μ g atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  have hsum := (hf ε hε).add hne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hsum)
    (fun _ => zero_le) fun n => ?_
  refine le_trans (measure_mono fun ω hω => ?_) (measure_union_le _ _)
  by_cases h : f n ω = g n ω
  · exact Or.inl (by simpa [h] using hω)
  · exact Or.inr h

/-- **Changing a sequence on a vanishing event (set form).** If `f n = g n` on `good n`,
`μ (good n)ᶜ → 0` and `f n → c` in measure then `g n → c` in measure. -/
theorem tendstoInMeasure_congr_on_good {f g : ℕ → Ω → ℝ} {c : ℝ} {good : ℕ → Set Ω}
    (hfg : ∀ n ω, ω ∈ good n → f n ω = g n ω)
    (hbad : Tendsto (fun n => μ (good n)ᶜ) atTop (nhds 0))
    (hf : TendstoInMeasure μ f atTop (fun _ => c)) :
    TendstoInMeasure μ g atTop (fun _ => c) :=
  tendstoInMeasure_congr_of_measure_ne_tendsto
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad (fun _ => zero_le)
      fun n => measure_mono fun ω hω => by
        by_contra h
        exact hω (hfg n ω (by simpa using h))) hf

/-- **Reverse transport along `fst`.** If `F n ∘ fst → c` in measure on a product with a probability
measure, then `F n → c` in measure on the first factor. -/
theorem tendstoInMeasure_of_comp_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν] {F : ℕ → α → ℝ} {c : ℝ}
    (hF : ∀ n, Measurable (F n))
    (h : TendstoInMeasure (μ.prod ν) (fun n (q : α × β) => F n q.1) atTop (fun _ => c)) :
    TendstoInMeasure μ F atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  refine (h ε hε).congr fun n => ?_
  have hS : MeasurableSet {a : α | ε ≤ dist (F n a) c} :=
    measurableSet_le measurable_const ((hF n).dist measurable_const)
  have : {q : α × β | ε ≤ dist (F n q.1) c} = {a : α | ε ≤ dist (F n a) c} ×ˢ Set.univ := by
    ext q; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]


end real

section squeeze

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `b n → 0` in measure then `∫ min 1 (b n) → 0` (bounded convergence for the truncation). -/
theorem tendsto_lintegral_min_one_ofReal [IsProbabilityMeasure μ] {b : ℕ → Ω → ℝ}
    (hb : TendstoInMeasure μ b atTop (fun _ => 0)) :
    Tendsto (fun n => ∫⁻ ω, min 1 (ENNReal.ofReal (b n ω)) ∂μ) atTop (nhds 0) := by
  rw [tendstoInMeasure_iff_dist] at hb
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ + ENNReal.ofReal δ ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, by simp [htop]⟩
    · refine ⟨ε.toReal / 2, by have := ENNReal.toReal_pos hε.ne' htop; positivity, ?_⟩
      rw [← ENNReal.ofReal_add (by have := ENNReal.toReal_nonneg (a := ε); positivity)
        (by have := ENNReal.toReal_nonneg (a := ε); positivity)]
      rw [show ε.toReal / 2 + ε.toReal / 2 = ε.toReal by ring, ENNReal.ofReal_toReal htop]
  have hev : ∀ᶠ n in atTop, μ {ω | δ ≤ dist (b n ω) 0} ≤ ENNReal.ofReal δ := by
    have := (hb δ hδ0)
    exact (this.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hδ0)))
  filter_upwards [hev] with n hn
  calc ∫⁻ ω, min 1 (ENNReal.ofReal (b n ω)) ∂μ
      ≤ ∫⁻ ω, ({ω | δ ≤ dist (b n ω) 0}.indicator (1 : Ω → ℝ≥0∞) ω + ENNReal.ofReal δ) ∂μ := by
        refine lintegral_mono fun ω => ?_
        by_cases h : δ ≤ dist (b n ω) 0
        · simp only [Set.indicator_of_mem (show ω ∈ {ω | δ ≤ dist (b n ω) 0} from h),
            Pi.one_apply]
          exact (min_le_left _ _).trans le_self_add
        · have h' : b n ω ≤ δ := by
            simp only [Real.dist_eq, sub_zero, not_le] at h
            exact (le_abs_self _).trans h.le
          simp only [Set.indicator_of_notMem (show ω ∉ {ω | δ ≤ dist (b n ω) 0} from h),
            zero_add]
          exact (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal h')
    _ = ∫⁻ ω, {ω | δ ≤ dist (b n ω) 0}.indicator (1 : Ω → ℝ≥0∞) ω ∂μ + ENNReal.ofReal δ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ μ {ω | δ ≤ dist (b n ω) 0} + ENNReal.ofReal δ := by
        gcongr; exact lintegral_indicator_one_le _
    _ ≤ ε := (add_le_add_left hn _).trans hδ

/-- **Chebyshev squeeze.** If `μ (E n) ≤ ∫ min 1 (b n)` and `b n → 0` in measure then
`μ (E n) → 0`. -/
theorem tendsto_measure_of_le_lintegral_min_one [IsProbabilityMeasure μ] {E : ℕ → Set Ω}
    {b : ℕ → Ω → ℝ} (hE : ∀ᶠ n in atTop, μ (E n) ≤ ∫⁻ ω, min 1 (ENNReal.ofReal (b n ω)) ∂μ)
    (hb : TendstoInMeasure μ b atTop (fun _ => 0)) :
    Tendsto (fun n => μ (E n)) atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_lintegral_min_one_ofReal hb) (Eventually.of_forall fun _ => zero_le) hE

end squeeze

end NTK

end
