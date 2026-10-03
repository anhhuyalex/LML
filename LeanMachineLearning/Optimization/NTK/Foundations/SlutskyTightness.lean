/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Analysis.Matrix.Normed

/-!
# Slutsky, tightness and tail bounds on varying probability spaces

General probability facts with no neural-network content: a Slutsky theorem for random variables
living on width-dependent probability spaces, a uniform norm radius from tightness, and Markov
tail bounds for empirical averages of i.i.d. samples. They are used by `NTK.Initialization`.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

/-! ### Varying-Space Slutsky and Subtraction Theorems

Mathlib's existing Slutsky theorems (`prodMk_of_tendstoInMeasure_const` and
`continuous_comp_prodMk_of_tendstoInMeasure_const`) require a single fixed source
probability measure. In parameter initialization and neural network limits, random
variables live on width-dependent probability spaces `(Ω n, μ n)`.

The theorems below generalize Mathlib's Slutsky API to varying source spaces `(Ω n, μ n)`
under tail convergence in measure to a deterministic constant `c`, with no NTK-specific
assumptions. -/

namespace MeasureTheory

open Filter ProbabilityTheory _root_.BoundedContinuousFunction Topology

variable {ι E E' F Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [SeminormedAddCommGroup E]
  [SecondCountableTopology E] [BorelSpace E]
  {l : Filter ι} [l.IsCountablyGenerated]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X n` converges in distribution to `Z` along `l`, `Y n - X n` converges in measure to 0
under varying spaces `(Ω n, μ n)`, and `Y n` is almost everywhere measurable, then `Y n`
converges in distribution to `Z`. -/
lemma tendstoInDistribution_of_tendsto_measure_norm_sub (X : (i : ι) → Ω i → E)
    (Y : (i : ι) → Ω i → E) (Z : Ω' → E)
    (hXZ : TendstoInDistribution X l Z μ μ')
    (hXY : ∀ ε > 0, Filter.Tendsto (fun i => μ i {ω | ε ≤ ‖Y i ω - X i ω‖}) l (nhds 0))
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution Y l Z μ μ' := by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  have hX : ∀ i, AEMeasurable (X i) (μ i) := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · have := hE; simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂((μ n).map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  -- Needed as a local hypothesis by the `fun_prop` calls below.
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using! tendsto_const_nhds
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂((μ n).map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le n : |∫ ω, F ω ∂((μ n).map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂((μ n).map (Y n))) (∫ ω, F ω ∂((μ n).map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) (μ n) := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) (μ n) := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Y n a) - F (X n a)‖) (μ n) := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂(μ n)‖
      _ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂(μ n) := norm_integral_le_integral_norm _
      _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂(μ n)
          + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂(μ n) := by
        symm
        simp_rw [← not_lt]
        refine integral_add_compl₀ ?_ h_int_sub
        exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
      _ ≤ ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂(μ n)
          + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, M ∂(μ n) := by
        gcongr ?_ + ?_
        · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
          · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
          · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
        · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
          rw [← dist_eq_norm]
          convert! hF_bounded _ _
      _ = L * (ε / 2) * (μ n).real {x | ‖Y n x - X n x‖ < ε / 2}
          + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
          smul_eq_mul]
        ring
      _ ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
        rw [mul_assoc]
        gcongr
        grw [measureReal_le_one, mul_one]
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · have h_toReal := (ENNReal.tendsto_toReal_zero_iff fun n => measure_ne_top (μ n) _).2
        (hXY (ε / 2) (by positivity))
      exact h_toReal
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- **Varying-space Slutsky's theorem**: if `X n` converges in distribution to `Z` along `l`
under `μ n`, and `Y n` converges in measure to a deterministic constant `c` under `μ n`, then
the joint pair `(X n, Y n)` converges in distribution to `(Z, c)`. -/
theorem TendstoInDistribution.prodMk_of_tendsto_measure_norm_sub_const
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E']
    [SecondCountableTopology E'] [BorelSpace E']
    {X : (i : ι) → Ω i → E} {Y : (i : ι) → Ω i → E'} {Z : Ω' → E}
    {c : E'} (hXZ : TendstoInDistribution X l Z μ μ')
    (hY : ∀ ε > 0, Filter.Tendsto (fun i => μ i {ω | ε ≤ ‖Y i ω - c‖}) l (nhds 0))
    (hY_meas : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution (fun n ω => (X n ω, Y n ω)) l (fun ω => (Z ω, c)) μ μ' := by
  have hX : ∀ i, AEMeasurable (X i) (μ i) := hXZ.forall_aemeasurable
  refine tendstoInDistribution_of_tendsto_measure_norm_sub (X := fun n ω => (X n ω, c))
    (fun n ω => (X n ω, Y n ω)) (fun ω => (Z ω, c)) ?_ ?_ (fun i => (hX i).prodMk (hY_meas i))
  · exact hXZ.continuous_comp (g := fun x => (x, c)) (by fun_prop)
  · intro ε hε
    have h_norm : ∀ i ω, ‖(X i ω, Y i ω) - (X i ω, c)‖ = ‖Y i ω - c‖ := by
      intro i ω
      simp only [Prod.sub_def, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    simp_rw [h_norm]
    exact hY ε hε

/-- **Varying-space Slutsky's theorem for continuous functions**: if `X n` converges in
distribution to `Z` under `μ n`, `Y n` converges in measure to a constant `c` under `μ n`,
and `g` is continuous, then `g (X n, Y n)` converges in distribution to `g (Z, c)`. -/
theorem TendstoInDistribution.continuous_comp_prodMk_of_tendsto_measure_norm_sub_const
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E']
    [SecondCountableTopology E'] [BorelSpace E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E × E' → F} (hg : Continuous g)
    {X : (i : ι) → Ω i → E} {Y : (i : ι) → Ω i → E'} (Z : Ω' → E)
    {c : E'} (hXZ : TendstoInDistribution X l Z μ μ')
    (hY : ∀ ε > 0, Filter.Tendsto (fun i => μ i {ω | ε ≤ ‖Y i ω - c‖}) l (nhds 0))
    (hY_meas : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution (fun n ω => g (X n ω, Y n ω)) l (fun ω => g (Z ω, c)) μ μ' :=
  (hXZ.prodMk_of_tendsto_measure_norm_sub_const hY hY_meas).continuous_comp hg

omit [SecondCountableTopology E] [l.IsCountablyGenerated] in
/-- Subtraction of a deterministic constant preserves convergence in distribution. -/
theorem TendstoInDistribution.sub_const
    (X : (i : ι) → Ω i → E) (Z : Ω' → E) (c : E)
    (hXZ : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n ω => X n ω - c) l (fun ω => Z ω - c) μ μ' :=
  hXZ.continuous_comp (continuous_sub_right c)

end MeasureTheory

/-! ### Uniform Norm Radius from Tightness

Generic `L²`-integrability and tightness-to-radius results with no NTK-specific assumptions. -/

namespace MeasureTheory

/-- Under a finite measure, a real function whose self-product lies in `L²` itself lies in `L²`
(the fourth moment controls the second). -/
theorem memLp_two_of_memLp_two_mul_self {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (h : MemLp (fun x => f x * f x) 2 μ) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq hf]
  simpa [sq] using h.integrable one_le_two

/-- **Uniform radius from tightness.** If the laws `(μ i).map (X i)` all lie in a tight set `S`
of measures on a normed space, then for every `ε > 0` a single deterministic radius `R ≥ 0` bounds
the tail probabilities `μ i {‖X i‖ > R}` by `ε`, uniformly in `i`. -/
theorem exists_forall_measure_norm_gt_le_of_isTightMeasureSet_map
    {ι E : Type*} {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)} {mE : MeasurableSpace E}
    [NormedAddCommGroup E] [OpensMeasurableSpace E]
    {μ : (i : ι) → Measure (Ω i)} {X : (i : ι) → Ω i → E} (hX : ∀ i, AEMeasurable (X i) (μ i))
    {S : Set (Measure E)} (hS : IsTightMeasureSet S) (hmem : ∀ i, (μ i).map (X i) ∈ S)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i, μ i {ω | R < ‖X i ω‖} ≤ ε := by
  obtain ⟨R, hR⟩ :=
    ((tendsto_measure_norm_gt_of_isTightMeasureSet hS).eventually (gt_mem_nhds hε)).exists
  refine ⟨max R 0, le_max_right _ _, fun i => ?_⟩
  have hopen : MeasurableSet {x : E | R < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  calc μ i {ω | max R 0 < ‖X i ω‖}
      ≤ μ i {ω | R < ‖X i ω‖} :=
        measure_mono (Set.ofPred_subset_ofPred.2 fun ω hω => lt_of_le_of_lt (le_max_left R 0) hω)
    _ = (μ i).map (X i) {x : E | R < ‖x‖} :=
        (Measure.map_apply_of_aemeasurable (hX i) hopen).symm
    _ ≤ ε := (le_iSup₂ (f := fun ν (_ : ν ∈ S) => ν {x : E | R < ‖x‖}) _ (hmem i)).trans hR.le

/-- Integral of a function composed with a measure-preserving map. Unlike
`MeasurePreserving.integral_comp` this needs no measurable embedding, which coordinate projections
are not. -/
theorem MeasurePreserving.integral_comp_of_aestronglyMeasurable {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → E} (hg : AEStronglyMeasurable g ν) : ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν :=
  calc ∫ x, g (f x) ∂μ = ∫ y, g y ∂(Measure.map f μ) :=
        (integral_map hf.measurable.aemeasurable (by rwa [hf.map_eq])).symm
    _ = ∫ y, g y ∂ν := by rw [hf.map_eq]

/-- **Markov's inequality in high-probability form.** A nonnegative measurable integrable function
whose integral is at most `τ * δ` is at most `τ` with probability at least `1 - δ`. -/
theorem measureReal_fun_le_ge_one_sub_of_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {F : α → ℝ} (hF : Measurable F)
    (hint : Integrable F μ) (hnn : ∀ x, 0 ≤ F x) {τ δ : ℝ} (hτ : 0 < τ)
    (hv : ∫ x, F x ∂μ ≤ τ * δ) : μ.real {x | F x ≤ τ} ≥ 1 - δ := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hnn) hint τ
  have hbad : μ.real {x | τ ≤ F x} ≤ δ := by
    have h1 : τ * μ.real {x | τ ≤ F x} ≤ τ * δ := hmarkov.trans hv
    exact le_of_mul_le_mul_left h1 hτ
  have hbad_meas : MeasurableSet {x | τ ≤ F x} := measurableSet_le measurable_const hF
  have hsub : {x | τ ≤ F x}ᶜ ⊆ {x | F x ≤ τ} := fun x hx => by
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    exact hx.le
  calc μ.real {x | F x ≤ τ} ≥ μ.real {x | τ ≤ F x}ᶜ := measureReal_mono hsub
    _ = 1 - μ.real {x | τ ≤ F x} := probReal_compl_eq_one_sub hbad_meas
    _ ≥ 1 - δ := sub_le_sub_left hbad 1

/-- **Markov bound for an i.i.d. empirical average.** For a nonnegative measurable observable `g`
that is integrable under a probability law `μ`, the empirical average `n⁻¹ ∑ᵢ g (xᵢ)` over `n`
independent samples is at most `τ` with probability at least `1 - δ`, as soon as `E g ≤ τ δ`. The
threshold does not depend on `n`. -/
theorem measureReal_pi_average_le_ge_one_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) {g : α → ℝ} (hg : Measurable g)
    (hint : Integrable g μ) (hnn : ∀ x, 0 ≤ g x) {τ δ : ℝ} (hτ : 0 < τ)
    (hv : ∫ x, g x ∂μ ≤ τ * δ) :
    (Measure.pi fun _ : Fin n => μ).real {x | (n : ℝ)⁻¹ * ∑ i : Fin n, g (x i) ≤ τ} ≥ 1 - δ := by
  have hmp : ∀ i : Fin n, MeasurePreserving (fun x : Fin n → α => x i)
      (Measure.pi fun _ : Fin n => μ) μ := fun i => measurePreserving_eval (fun _ : Fin n => μ) i
  have hterm : ∀ i : Fin n, Integrable (fun x : Fin n → α => g (x i))
      (Measure.pi fun _ : Fin n => μ) := fun i =>
    ((hmp i).integrable_comp hint.aestronglyMeasurable).2 hint
  set F : (Fin n → α) → ℝ := fun x => (n : ℝ)⁻¹ * ∑ i : Fin n, g (x i) with hF
  have hFm : Measurable F := Measurable.const_mul
    (Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)) _
  have hFint : Integrable F (Measure.pi fun _ : Fin n => μ) :=
    Integrable.const_mul (integrable_finsetSum _ fun i _ => hterm i) _
  have hFnn : ∀ x, 0 ≤ F x := fun x => by
    have : 0 ≤ ∑ i : Fin n, g (x i) := Finset.sum_nonneg fun i _ => hnn _
    positivity
  have hFint_eq : ∫ x, F x ∂(Measure.pi fun _ : Fin n => μ) = ∫ x, g x ∂μ := by
    rw [hF, integral_const_mul, integral_finsetSum _ fun i _ => hterm i]
    simp only [(hmp _).integral_comp_of_aestronglyMeasurable hint.aestronglyMeasurable,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  exact measureReal_fun_le_ge_one_sub_of_integral_le _ hFm hFint hFnn hτ (hFint_eq ▸ hv)


end MeasureTheory

end
