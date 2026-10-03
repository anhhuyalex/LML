/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Small Calculus for Convergence in Measure of Real Sequences

Elementary closure properties of `TendstoInMeasure` for real-valued sequences, used throughout the
deep backward-concentration argument (`Deep/`):

* `tendstoInMeasure_const`, `tendstoInMeasure_add`, `tendstoInMeasure_sub`;
* `tendstoInMeasure_zero_of_abs_le`: domination by a sequence tending to `0` in measure;
* `tendstoInMeasure_congr_of_measure_ne_tendsto`: changing a sequence on events whose measure tends
  to `0` does not change the limit (used for the "`Φᵀ Φ` is invertible" good event);
* `tendstoInMeasure_comp_of_continuousAt`, `tendstoInMeasure_comp_of_continuousWithinAt`,
  `tendstoInMeasure_comp_measurePreserving`: continuous mapping and transport along measure
  preserving maps;
* `tendstoInMeasure_trans`, `tendstoInMeasure_pi`, `tendstoInMeasure_sum_mul`,
  `tendstoInMeasure_mul`: two-stage approximation, finite families, sums of products;
* `tendstoInMeasure_matrix_inv`: inversion of convergent matrices over any finite index type;
* `tendsto_integral_of_tendstoInMeasure_of_bounded`: bounded convergence for convergence in measure;
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

section general

/-- `Matrix` inherits its `PseudoEMetricSpace` structure from the underlying Pi type. Mathlib does
not register this instance directly for `Matrix` (to avoid a diamond with other norms such as the
operator or Frobenius norm — `Matrix` is a `def`, not `abbrev`, over `m → n → α`, so instance
search does not unfold it automatically), so it is registered here for all finite index types.
Needed so `tendstoInMeasure_comp_of_continuousAt` applies to `Matrix`-valued sequences. -/
instance instPseudoEMetricSpaceMatrix (ι κ : Type*) [Fintype ι] [Fintype κ] :
    PseudoEMetricSpace (Matrix ι κ ℝ) := by
  unfold Matrix; infer_instance

/-- The matching pseudo-metric instance is needed for the real-valued `dist` tail events used in
convergence-in-measure statements.  As above, it is inherited from the underlying finite Pi type. -/
instance instPseudoMetricSpaceMatrix (ι κ : Type*) [Fintype ι] [Fintype κ] :
    PseudoMetricSpace (Matrix ι κ ℝ) := by
  unfold Matrix; infer_instance

/-- **Continuous mapping theorem for convergence in probability to a constant.** If `f n → y` in
probability and `g` is continuous at `y`, then `g ∘ f n → g y` in probability. Used in the deep NNGP
recursion to turn the inductive hypothesis `Φ_ℓ^{(n)} → Φ_ℓ` into
`𝒞_φ(Φ_ℓ^{(n)}) → 𝒞_φ(Φ_ℓ)`. -/
theorem tendstoInMeasure_comp_of_continuousAt
    {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : ℕ → α → E} {y : E} {g : E → F}
    (hfg : TendstoInMeasure μ f Filter.atTop (fun _ => y)) (hg : ContinuousAt g y) :
    TendstoInMeasure μ (fun n a => g (f n a)) Filter.atTop (fun _ => g y) := by
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := EMetric.continuousAt_iff.mp hg ε hε
  have hmono : ∀ n, μ {a | ε ≤ edist (g (f n a)) (g y)} ≤ μ {a | δ ≤ edist (f n a) y} := by
    intro n
    refine measure_mono fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_contra hlt
    push Not at hlt
    exact absurd (hδg hlt) (not_lt.mpr ha)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg δ hδ)
    (fun _ => zero_le) hmono

/-- **Inverse of a convergent matrix sequence.** If `f n → M` in probability and `M` is invertible,
then `(f n)⁻¹ → M⁻¹` in probability: inversion is `det⁻¹ • adjugate`, continuous where `det ≠ 0`.
With the positive-definite limiting kernels of the deep NTK this yields
`‖Σ̂ₙ⁻¹‖ = O_ℙ(1)` for the empirical activation Gram. -/
theorem tendstoInMeasure_matrix_inv {α ι : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [Fintype ι] [DecidableEq ι] {f : ℕ → α → Matrix ι ι ℝ} {M : Matrix ι ι ℝ}
    (hf : TendstoInMeasure μ f Filter.atTop (fun _ => M)) (hM : IsUnit M.det) :
    TendstoInMeasure μ (fun n a => (f n a)⁻¹) Filter.atTop (fun _ => M⁻¹) := by
  refine tendstoInMeasure_comp_of_continuousAt
    (g := fun A : Matrix ι ι ℝ => A⁻¹) hf ?_
  refine continuousAt_matrix_inv M ?_
  simp only [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hM.ne_zero

/-- Positive-definite version of `tendstoInMeasure_matrix_inv`. -/
theorem tendstoInMeasure_matrix_inv_of_posDef {α ι : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [Fintype ι] [DecidableEq ι] {f : ℕ → α → Matrix ι ι ℝ} {M : Matrix ι ι ℝ}
    (hf : TendstoInMeasure μ f Filter.atTop (fun _ => M)) (hM : M.PosDef) :
    TendstoInMeasure μ (fun n a => (f n a)⁻¹) Filter.atTop (fun _ => M⁻¹) :=
  tendstoInMeasure_matrix_inv hf (isUnit_iff_ne_zero.mpr hM.det_pos.ne')

/-- **Continuous mapping on an invariant set.** If `f n → y` in probability, all values of `f`
lie in `s`, and `g` is continuous at `y` relative to `s`, then `g ∘ f n → g y` in probability.
This is the form needed for covariance matrices: `multivariateGaussian` is naturally continuous in
its covariance only on the positive-semidefinite cone. -/
theorem tendstoInMeasure_comp_of_continuousWithinAt
    {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : ℕ → α → E} {y : E} {g : E → F}
    {s : Set E} (hfg : TendstoInMeasure μ f Filter.atTop (fun _ => y))
    (hf : ∀ n a, f n a ∈ s) (hg : ContinuousWithinAt g s y) :
    TendstoInMeasure μ (fun n a => g (f n a)) Filter.atTop (fun _ => g y) := by
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := EMetric.continuousWithinAt_iff.mp hg ε hε
  have hmono : ∀ n, μ {a | ε ≤ edist (g (f n a)) (g y)} ≤ μ {a | δ ≤ edist (f n a) y} := by
    intro n
    refine measure_mono fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_contra hlt
    push Not at hlt
    exact absurd (hδg (hf n a) hlt) (not_lt.mpr ha)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg δ hδ)
    (fun _ => zero_le) hmono

/-- A two-stage convergence-in-probability argument.  If `f n` is close in probability to a
possibly `n`-dependent intermediate approximation `g n`, and `g n` converges in probability to
`h`, then `f n` converges in probability to `h`.  The deep covariance induction uses this after
separating the fresh-layer empirical fluctuation from the deterministic covariance update. -/
theorem tendstoInMeasure_trans
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoMetricSpace E] {f g : ℕ → α → E} {h : α → E}
    (hfg : ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun n => μ {a | ε ≤ dist (f n a) (g n a)}) Filter.atTop (nhds 0))
    (hgh : TendstoInMeasure μ g Filter.atTop h) :
    TendstoInMeasure μ f Filter.atTop h := by
  rw [tendstoInMeasure_iff_dist] at hgh ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hsum := (hfg (ε / 2) hhalf).add (hgh (ε / 2) hhalf)
  have hmono : ∀ n, μ {a | ε ≤ dist (f n a) (h a)} ≤
      μ {a | ε / 2 ≤ dist (f n a) (g n a)} +
        μ {a | ε / 2 ≤ dist (g n a) (h a)} := by
    intro n
    calc
      μ {a | ε ≤ dist (f n a) (h a)} ≤
          μ ({a | ε / 2 ≤ dist (f n a) (g n a)} ∪
            {a | ε / 2 ≤ dist (g n a) (h a)}) := by
        apply measure_mono
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        by_cases hfg' : ε / 2 ≤ dist (f n a) (g n a)
        · exact Or.inl hfg'
        · right
          by_contra hgh'
          have hfg_lt : dist (f n a) (g n a) < ε / 2 := lt_of_not_ge hfg'
          have hgh_lt : dist (g n a) (h a) < ε / 2 := lt_of_not_ge hgh'
          have hlt : dist (f n a) (h a) < ε := by
            calc
              dist (f n a) (h a) ≤ dist (f n a) (g n a) + dist (g n a) (h a) :=
                dist_triangle _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add hfg_lt hgh_lt
              _ = ε := by ring
          exact (not_lt_of_ge ha) hlt
      _ ≤ μ {a | ε / 2 ≤ dist (f n a) (g n a)} +
          μ {a | ε / 2 ≤ dist (g n a) (h a)} := measure_union_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hsum)
    (fun _ => zero_le) hmono

/-- **Coordinatewise convergence in measure implies joint convergence** for a finite family. -/
theorem tendstoInMeasure_pi {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : ι → Type*} [∀ i, PseudoMetricSpace (E i)] {f : ℕ → Ω → ∀ i, E i} {c : ∀ i, E i}
    (h : ∀ i, TendstoInMeasure μ (fun n a => f n a i) Filter.atTop (fun _ => c i)) :
    TendstoInMeasure μ f Filter.atTop (fun _ => c) := by
  simp_rw [tendstoInMeasure_iff_dist] at h
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsum : Filter.Tendsto (fun n => ∑ i, μ {a | ε ≤ dist (f n a i) (c i)}) Filter.atTop
      (nhds 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ)
      (f := fun i n => μ {a | ε ≤ dist (f n a i) (c i)}) (a := fun _ => 0) fun i _ => h i ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro n
  calc μ {a | ε ≤ dist (f n a) c}
      ≤ μ (⋃ i, {a | ε ≤ dist (f n a i) (c i)}) := by
        apply measure_mono
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha
        by_contra hne
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hne
        push Not at hne
        exact (not_lt_of_ge ha) ((dist_pi_lt_iff hε).2 hne)
    _ ≤ ∑ i, μ {a | ε ≤ dist (f n a i) (c i)} := measure_iUnion_fintype_le _ _

/-- **Sums of products of convergent families.** If `a i n → a∞ i` and `b i n → b∞ i` in measure
for each index `i` of a finite set, then `∑ i, a i n * b i n → ∑ i, a∞ i * b∞ i` in measure. -/
theorem tendstoInMeasure_sum_mul {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {a b : ι → ℕ → Ω → ℝ} {a' b' : ι → ℝ}
    (ha : ∀ i, TendstoInMeasure μ (a i) Filter.atTop (fun _ => a' i))
    (hb : ∀ i, TendstoInMeasure μ (b i) Filter.atTop (fun _ => b' i)) :
    TendstoInMeasure μ (fun n ω => ∑ i, a i n ω * b i n ω) Filter.atTop
      (fun _ => ∑ i, a' i * b' i) := by
  have hpair : TendstoInMeasure μ (fun n ω => (Sum.elim (fun i => a i n ω) (fun i => b i n ω) :
      ι ⊕ ι → ℝ)) Filter.atTop (fun _ => Sum.elim a' b') := by
    refine tendstoInMeasure_pi fun i => ?_
    cases i with
    | inl i => exact ha i
    | inr i => exact hb i
  have hcont : Continuous (fun v : ι ⊕ ι → ℝ => ∑ i, v (Sum.inl i) * v (Sum.inr i)) := by
    fun_prop
  simpa using tendstoInMeasure_comp_of_continuousAt hpair hcont.continuousAt

/-- **Products of convergent sequences.** If `a n → a'` and `b n → b'` in measure then
`a n * b n → a' * b'` in measure (the one-term case of `tendstoInMeasure_sum_mul`). -/
theorem tendstoInMeasure_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {a b : ℕ → Ω → ℝ} {a' b' : ℝ}
    (ha : TendstoInMeasure μ a Filter.atTop (fun _ => a'))
    (hb : TendstoInMeasure μ b Filter.atTop (fun _ => b')) :
    TendstoInMeasure μ (fun n ω => a n ω * b n ω) Filter.atTop (fun _ => a' * b') := by
  simpa using tendstoInMeasure_sum_mul (ι := Unit) (a := fun _ => a) (b := fun _ => b)
    (a' := fun _ => a') (b' := fun _ => b') (fun _ => ha) (fun _ => hb)

/-- Convergence in probability is preserved by precomposition with a measure-preserving map.
The explicit measurability hypotheses make the result applicable to the finite-dimensional
covariance maps used later without relying on an implicit completion of the source measure. -/
theorem tendstoInMeasure_comp_measurePreserving
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {ν : Measure β} [PseudoEMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {T : α → β} {f : ℕ → β → E} {g : β → E}
    (hfg : TendstoInMeasure ν f Filter.atTop g) (hT : MeasurePreserving T μ ν)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) :
    TendstoInMeasure μ (fun n a => f n (T a)) Filter.atTop (fun a => g (T a)) := by
  intro ε hε
  have hset : ∀ n, MeasurableSet {b | ε ≤ edist (f n b) (g b)} := fun n =>
    ((hf n).edist hg) measurableSet_Ici
  have heq : (fun n => μ {a | ε ≤ edist (f n (T a)) (g (T a))}) =
      fun n => ν {b | ε ≤ edist (f n b) (g b)} := by
    funext n
    change μ (T ⁻¹' {b | ε ≤ edist (f n b) (g b)}) = _
    rw [← hT.map_eq, Measure.map_apply hT.measurable (hset n)]
  rw [heq]
  exact hfg ε hε

/-- **Bounded convergence for convergence in probability.** If `f n → g` in probability and the
`f n` are uniformly bounded in norm by a constant, then `∫ f n → ∫ g`. Proof: given any
subsequence, `TendstoInMeasure.exists_seq_tendsto_ae` extracts a further a.e.-convergent
subsequence, along which the ordinary dominated convergence theorem gives convergence of the
integrals; since every subsequence has such a further convergent subsequence,
`tendsto_of_subseq_tendsto` closes the full sequence. Used in the deep NNGP recursion in place of
Theorem 3's dominated convergence step (`tendsto_charFun_outputMeasure_eq_multivariateGaussian`),
since Part 1 only supplies convergence in probability, not the almost-sure convergence Theorem 3
had from Kolmogorov's SLLN. -/
theorem tendsto_integral_of_tendstoInMeasure_of_bounded
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℕ → α → E} {g : α → E}
    (hfg : TendstoInMeasure μ f Filter.atTop g)
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ) (C : ℝ)
    (hf_bound : ∀ n, ∀ᵐ a ∂μ, ‖f n a‖ ≤ C) [IsFiniteMeasure μ] :
    Filter.Tendsto (fun n => ∫ a, f n a ∂μ) Filter.atTop (nhds (∫ a, g a ∂μ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hms_ae⟩ := (hfg.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  simpa using tendsto_integral_of_dominated_convergence (bound := fun _ => C)
    (fun k => hf_meas (ns (ms k))) (integrable_const C)
    (fun k => hf_bound (ns (ms k))) hms_ae

end general

end NTK

end
