/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities
public import LeanMachineLearning.SpinGlasses.PoissonProcessIndepMarks

/-!
# Lemma 2.3 as a statement about Gibbs measures on block indices

Lemma 2.3 of Panchenko compares replica averages for the tilted and the reference marked Poisson
process. Here both averages are written as Gibbs series over replica tuples of the actual block
indices `(n, l)`, `l < Nₙ`, with weights `uₚ exp (t gₚ) / ∑ᵩ u_q exp (t g_q)`. Writing them on one
probability space is what lets the Gaussian marks `g` be integrated by parts while the counts and
masses are held fixed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- A reference block construction whose masses and Gaussian marks have independent
product laws. The split is chosen *before* constructing the blocks, rather than trying
to infer independent marks from an arbitrary decomposition of the product intensity. -/
theorem exists_poissonDirichlet_gaussian_split_blocks (ζ : ℝ) :
    ∃ (ν : ℕ → Measure ℝ) (r : ℕ → ℝ≥0)
      (P : Measure (ℕ → ℕ × (ℕ → ℝ × ℝ))),
      (∀ n, IsProbabilityMeasure (ν n)) ∧ IsProbabilityMeasure P ∧
      (∀ n, Measurable fun ω : ℕ → ℕ × (ℕ → ℝ × ℝ) => ω n) ∧
      iIndepFun (fun n (ω : ℕ → ℕ × (ℕ → ℝ × ℝ)) => ω n) P ∧
      (∀ n, HasLaw (fun ω : ℕ → ℕ × (ℕ → ℝ × ℝ) => ω n)
        (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod (gaussianReal 0 1))) P) ∧
      (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
        Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1) := by
  obtain ⟨ν, r, hν, hμ⟩ := exists_probabilityMeasure_sum_smul_eq_of_sigmaFinite
    (zetaPoissonMeasure ζ)
  let ν' : ℕ → Measure (ℝ × ℝ) := fun n => (ν n).prod (gaussianReal 0 1)
  have _ : ∀ n, IsProbabilityMeasure (ν' n) := fun n => inferInstance
  obtain ⟨P, hP, hBm, hB, hlaw⟩ := exists_poissonBlocks ν' r
  refine ⟨ν, r, P, hν, hP, hBm, hB, hlaw, ?_⟩
  rw [hμ, Measure.prod_sum_left]
  congr 1
  funext n
  rw [Measure.prod_smul_left]

/-- Almost surely every sampled point of the active indices lies in a measurable set `A` that
carries all the mass of the blocks of positive intensity. -/
theorem ae_poissonBlocks_forall_mem {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {A : Set S} (hA : MeasurableSet A) (hν : ∀ n, r n ≠ 0 → ∀ᵐ x ∂ν n, x ∈ A) :
    ∀ᵐ ω ∂P, ∀ n, ∀ l < (B n ω).1, (B n ω).2 l ∈ A := by
  refine ae_all_iff.2 fun n => ?_
  by_cases hn : r n = 0
  · have hN : HasLaw (fun ω => (B n ω).1) Po(0) P := by
      have h := measurePreserving_fst.hasLaw.comp (hlaw n)
      rwa [hn] at h
    filter_upwards [hN.ae_eq_zero_of_poisson_zero] with ω hω l hl
    omega
  · have hsamp : HasLaw (fun ω => (B n ω).2) (Measure.infinitePi fun _ : ℕ => ν n) P :=
      measurePreserving_snd.hasLaw.comp (hlaw n)
    filter_upwards [ae_all_mem_of_hasLaw_infinitePi hsamp hA (hν n hn)] with ω hω l _
    exact hω l


/-- The ζ-Poisson intensity does not charge the nonpositive half-line. -/
theorem zetaPoissonMeasure_Iic_zero (ζ : ℝ) : zetaPoissonMeasure ζ (Set.Iic 0) = 0 := by
  rw [zetaPoissonMeasure, withDensity_apply _ measurableSet_Iic]
  rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0)
    fun x hx => by simp [not_lt.2 (Set.mem_Iic.1 hx)]]
  simp

/-- Almost surely all masses of the Gaussian-marked reference process are positive. -/
theorem ae_poissonDirichlet_gaussian_mass_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ζ : ℝ} (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, ∀ n, ∀ l < (B n ω).1, 0 < ((B n ω).2 l).1 := by
  have hA : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hmem : ∀ n, r n ≠ 0 → ∀ᵐ x ∂ν n, x ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := by
    intro n hn
    rw [ae_iff]
    have hset : {x : ℝ × ℝ | ¬ x ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)} =
        Set.Iic 0 ×ˢ Set.univ := by
      ext x; simp
    rw [hset]
    have hle := Measure.le_iff'.1 (Measure.le_sum (fun n => (r n : ℝ≥0∞) • ν n) n)
      (Set.Iic 0 ×ˢ Set.univ)
    rw [← hμ, Measure.prod_prod, zetaPoissonMeasure_Iic_zero, zero_mul] at hle
    rw [Measure.smul_apply, smul_eq_mul, nonpos_iff_eq_zero, mul_eq_zero] at hle
    exact hle.resolve_left (by simpa using hn)
  filter_upwards [ae_poissonBlocks_forall_mem ν r hlaw hA hmem] with ω h n l hl
  exact (h n l hl).1

/-- A ζ-Poisson marked process has infinitely many strictly positive-mass atoms almost surely.
This supplies an active index for Gaussian integration by parts after fixing the environment. -/
theorem ae_poissonDirichlet_gaussian_active_nonempty
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ)
    (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, Nonempty {p : ℕ × ℕ // p.2 < (B p.1 ω).1} := by
  have hν : ∀ n, IsProbabilityMeasure ((ν n).map Prod.fst) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw measurable_fst
  have hμ0 := eq_sum_map_fst_of_prod_eq ν r hμ
  let M : Ω → Measure ℝ := fun ω => poissonCountingMeasure
    (fun n => (B n ω).1) (fun n l => ((B n ω).2 l).1)
  have hL := (iIndepFun_hasLaw_poissonCountingMeasure_apply (κ := Unit)
    (fun n => (ν n).map Prod.fst) r hCm hCi hClaw hμ0 (fun _ => rfl)
    (A := fun _ => Set.Ioi (0 : ℝ)) (fun _ => measurableSet_Ioi)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)).1 ()
  simp only [zetaPoissonMeasure_Ioi_zero hζ, ↓reduceIte] at hL
  have htop : ∀ᵐ ω ∂P, M ω (Set.Ioi 0) = ∞ := by
    have hd : ∀ᵐ y ∂(P.map fun ω => M ω (Set.Ioi 0)), y = ∞ := by
      rw [hL.map_eq, ae_dirac_eq]
      simp
    exact (ae_map_iff hL.aemeasurable (measurableSet_singleton ∞)).1 hd
  filter_upwards [htop] with ω hω
  by_contra he
  have hempty : ∀ p : ℕ × ℕ, ¬ p.2 < (B p.1 ω).1 := by
    intro p hp
    exact he ⟨⟨p, hp⟩⟩
  have hzero : M ω (Set.Ioi 0) = 0 := by
    rw [show M ω = poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => ((B n ω).2 l).1) by rfl,
      poissonCountingMeasure_apply _ _ measurableSet_Ioi]
    apply ENNReal.tsum_eq_zero.2
    intro n
    apply Finset.sum_eq_zero
    intro l hl
    exact False.elim ((hempty (n, l)) (Finset.mem_range.1 hl))
  exact ENNReal.top_ne_zero (hω.symm.trans hzero)

/-- Almost surely the Gaussian-marked reference process has a summable family of
positive masses on its active block indices. These are the deterministic Gibbs weights
needed after conditioning on the counts and masses. -/
theorem ae_poissonDirichlet_gaussian_summable_masses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, Summable (fun p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
      ((B p.1.1 ω).2 p.1.2).1) := by
  have hν : ∀ n, IsProbabilityMeasure ((ν n).map Prod.fst) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw measurable_fst
  have hμ0 := eq_sum_map_fst_of_prod_eq ν r hμ
  have hfin := ae_lintegral_poisson_lt_top_of_blocks
    (P := P) (M := fun ω => poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => ((B n ω).2 l).1)) (fun n => (ν n).map Prod.fst) r hζ hζ1
    hCm hClaw hμ0 (fun _ => rfl)
  have hpos := ae_poissonDirichlet_gaussian_mass_pos ν r hlaw hμ
  filter_upwards [hfin, hpos] with ω hω hp
  have hsum := lintegral_poissonCountingMeasure_restrict_eq_tsum
    (fun n => (B n ω).1) (fun n l => ((B n ω).2 l).1)
    (A := Set.Ioi (0 : ℝ)) measurableSet_Ioi ENNReal.measurable_ofReal
  simp only [Set.mem_Ioi] at hsum
  rw [hsum] at hω
  have hω' : (∑' q : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      ENNReal.ofReal (((B q.1.1 ω).2 q.1.2).1)) < ∞ := by
    convert hω using 1
    apply tsum_congr
    intro q
    simp [hp q.1.1 q.1.2 q.2]
  exact summable_of_tsum_ofReal_lt_top (fun p => (hp _ _ p.2).le) hω'

/-- The three almost-sure hypotheses needed to apply Gaussian IBP after conditioning on
counts and masses: an active point exists, and its positive masses form a summable family. -/
theorem ae_poissonDirichlet_gaussian_ibp_environment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, Nonempty {p : ℕ × ℕ // p.2 < (B p.1 ω).1} ∧
      (∀ p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1}, 0 < ((B p.1.1 ω).2 p.1.2).1) ∧
      Summable (fun p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
        ((B p.1.1 ω).2 p.1.2).1) := by
  filter_upwards [ae_poissonDirichlet_gaussian_active_nonempty hζ ν r hBm hB hlaw hμ,
    ae_poissonDirichlet_gaussian_mass_pos ν r hlaw hμ,
    ae_poissonDirichlet_gaussian_summable_masses hζ hζ1 ν r hBm hB hlaw hμ]
    with ω hn hp hs
  exact ⟨hn, (fun p => hp p.1.1 p.1.2 p.2), hs⟩

/-- Conditional on positive summable masses, the mass-weighted absolute Gaussian marks
form an integrable series. This is the un-tilted one-replica domination input for
transferring integrability through Lemma 2.3. -/
theorem integrable_gaussian_mass_weighted_abs
    {α : Type*} [Countable α] (u : α → ℝ)
    (hu0 : ∀ a, 0 ≤ u a) (hu : Summable u)
    (iota : α → ℕ × ℕ) :
    (∀ᵐ g ∂(Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1),
      Summable fun a => u a * |g (iota a).1 (iota a).2|) ∧
    Integrable (fun g : ℕ → ℕ → ℝ =>
      ∑' a, u a * |g (iota a).1 (iota a).2|)
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hlaw (a : α) : HasLaw (fun g : ℕ → ℕ → ℝ => g (iota a).1 (iota a).2)
      (gaussianReal 0 1) μ :=
    (hasLaw_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) (iota a).2).comp
      (hasLaw_eval_infinitePi
        (fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) (iota a).1)
  have h := ae_summable_and_integrable_tsum_mul_exp
    (P := μ) (G := u) (X := fun a g => g (iota a).1 (iota a).2)
    (Z := fun _ _ => (0 : ℝ)) hu0 hu
    (fun _ => by
      change HasGaussianLaw (fun _ : ℕ → ℕ → ℝ => (0 : ℝ)) μ
      exact ⟨measurable_const.aemeasurable, by
        rw [Measure.map_const, measure_univ]
        simp only [one_smul]
        infer_instance⟩)
    (fun _ => by simp)
    (fun a => (hlaw a).hasGaussianLaw.memLp_two)
    (a := 1) (v := 0)
    (fun a => (integral_gaussianReal_coordinate_sq hlaw a).le)
    (fun _ => by simp)
  simpa only [Real.exp_zero, mul_one] using h

/-- The expected weighted absolute Gaussian mark is the same for every normalized
summable mass environment. This estimate is uniform even if the active index set and
its masses vary: no independence between coordinates is needed for this first moment. -/
theorem integral_gaussian_weighted_abs_eq
    {α : Type*} [Countable α] (u : α → ℝ)
    (hu0 : ∀ a, 0 ≤ u a) (hu : Summable u)
    (iota : α → ℕ × ℕ) :
    ∫ g : ℕ → ℕ → ℝ, (∑' a, u a * |g (iota a).1 (iota a).2|)
      ∂(Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      (∑' a, u a) * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hlaw (a : α) : HasLaw (fun g : ℕ → ℕ → ℝ => g (iota a).1 (iota a).2)
      (gaussianReal 0 1) μ :=
    (hasLaw_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) (iota a).2).comp
      (hasLaw_eval_infinitePi
        (fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) (iota a).1)
  have hgauss : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
    exact ((memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable
      (by simp)).abs
  have hint (a : α) : Integrable
      (fun g : ℕ → ℕ → ℝ => u a * |g (iota a).1 (iota a).2|) μ := by
    exact ((hlaw a).integrable_comp hgauss).const_mul _
  have heq (a : α) :
      (∫ g : ℕ → ℕ → ℝ, u a * |g (iota a).1 (iota a).2| ∂μ) =
      u a * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
    rw [integral_const_mul]
    exact congrArg (u a * ·) ((hlaw a).integral_comp
      (f := fun x : ℝ => |x|) (by fun_prop))
  have hs : Summable fun a => ∫ g : ℕ → ℕ → ℝ,
      ‖u a * |g (iota a).1 (iota a).2|‖ ∂μ := by
    have h : (fun a => ∫ g : ℕ → ℕ → ℝ,
        ‖u a * |g (iota a).1 (iota a).2|‖ ∂μ) =
        fun a => u a * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
      funext a
      rw [show (fun g : ℕ → ℕ → ℝ =>
        ‖u a * |g (iota a).1 (iota a).2|‖) =
        (fun g => u a * |g (iota a).1 (iota a).2|) from funext fun g => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hu0 a) (abs_nonneg _))]]
      exact heq a
    rw [h]
    exact hu.mul_right _
  rw [← integral_tsum_of_summable_integral_norm hint hs]
  simp_rw [heq]
  exact tsum_mul_right

/-- Conditional on a positive summable mass environment, the un-tilted marked
replica average is integrable under the Gaussian law. The normalized product-weighted
series is dominated by the single-coordinate Gaussian absolute-moment series. -/
theorem integrable_gaussian_gibbs_replica_untilted
    {α J : Type*} [Countable α] [Fintype J]
    (u : α → ℝ) [Nonempty α] (hu0 : ∀ a, 0 < u a) (hu : Summable u)
    (iota : α → ℕ × ℕ) (r₀ : J) (Φ : (J → α) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M) :
    Integrable (fun g : ℕ → ℕ → ℝ =>
      ∑' σ : J → α,
        (∏ j, u (σ j) / ∑' a, u a) *
          (Φ σ * g (iota (σ r₀)).1 (iota (σ r₀)).2))
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hUpos : 0 < ∑' a, u a := by
    apply hu.tsum_pos (fun a => (hu0 a).le)
      (Classical.choice (inferInstance : Nonempty α))
    exact hu0 _
  let w : α → ℝ := fun a => u a / ∑' b, u b
  have hw0 (a : α) : 0 ≤ w a := div_nonneg (hu0 a).le hUpos.le
  have hws : Summable w := hu.div_const _
  have hw : ∑' a, w a = 1 := by
    change (∑' a, u a / ∑' b, u b) = 1
    rw [tsum_div_const, div_self hUpos.ne']
  have hmass := integrable_gaussian_mass_weighted_abs u (fun a => (hu0 a).le) hu iota
  have hmark : ∀ᵐ g ∂μ,
      Summable fun a => w a * |g (iota a).1 (iota a).2| := by
    filter_upwards [hmass.1] with g hg
    simpa only [w, div_mul_eq_mul_div] using hg.div_const (∑' b, u b)
  have hbound : ∀ᵐ g ∂μ,
      |∑' σ : J → α,
        (∏ j, w (σ j)) * (Φ σ * g (iota (σ r₀)).1 (iota (σ r₀)).2)| ≤
        M / (∑' a, u a) *
          ∑' a, u a * |g (iota a).1 (iota a).2| := by
    filter_upwards [hmark] with g hg
    convert abs_tsum_prod_pi_mul_eval_le hw0 hws hw hg hΦ r₀ using 1
    simp only [w, div_mul_eq_mul_div, tsum_div_const]
    ring
  have hmeas : Measurable fun g : ℕ → ℕ → ℝ =>
      ∑' σ : J → α,
        (∏ j, w (σ j)) * (Φ σ * g (iota (σ r₀)).1 (iota (σ r₀)).2) := by
    apply Measurable.tsum
    intro σ
    fun_prop
  have hdom : Integrable (fun g : ℕ → ℕ → ℝ =>
      M / (∑' a, u a) * ∑' a, u a * |g (iota a).1 (iota a).2|) μ :=
    hmass.2.const_mul _
  have hint := hdom.mono' hmeas.aestronglyMeasurable hbound
  simpa only [w] using hint

/-- The un-tilted marked replica average has a first absolute moment bounded
uniformly over all positive summable environments. The normalization cancels the
total mass, so this is suitable for integrating over a random environment. -/
theorem integral_abs_gaussian_gibbs_replica_untilted_le
    {α J : Type*} [Countable α] [Fintype J]
    (u : α → ℝ) [Nonempty α] (hu0 : ∀ a, 0 < u a) (hu : Summable u)
    (iota : α → ℕ × ℕ) (r₀ : J) (Φ : (J → α) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M) :
    ∫ g : ℕ → ℕ → ℝ,
        |∑' σ : J → α,
          (∏ j, u (σ j) / ∑' a, u a) *
            (Φ σ * g (iota (σ r₀)).1 (iota (σ r₀)).2)|
      ∂(Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) ≤
      M * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hUpos : 0 < ∑' a, u a := by
    apply hu.tsum_pos (fun a => (hu0 a).le)
      (Classical.choice (inferInstance : Nonempty α))
    exact hu0 _
  let w : α → ℝ := fun a => u a / ∑' b, u b
  have hw0 (a : α) : 0 ≤ w a := div_nonneg (hu0 a).le hUpos.le
  have hws : Summable w := hu.div_const _
  have hw : ∑' a, w a = 1 := by
    change (∑' a, u a / ∑' b, u b) = 1
    rw [tsum_div_const, div_self hUpos.ne']
  have hmass := integrable_gaussian_mass_weighted_abs u (fun a => (hu0 a).le) hu iota
  have hmark : ∀ᵐ g ∂μ,
      Summable fun a => w a * |g (iota a).1 (iota a).2| := by
    filter_upwards [hmass.1] with g hg
    simpa only [w, div_mul_eq_mul_div] using hg.div_const (∑' b, u b)
  have hbound : ∀ᵐ g ∂μ,
      |∑' σ : J → α,
        (∏ j, w (σ j)) * (Φ σ * g (iota (σ r₀)).1 (iota (σ r₀)).2)| ≤
        M / (∑' a, u a) *
          ∑' a, u a * |g (iota a).1 (iota a).2| := by
    filter_upwards [hmark] with g hg
    convert abs_tsum_prod_pi_mul_eval_le hw0 hws hw hg hΦ r₀ using 1
    simp only [w, div_mul_eq_mul_div, tsum_div_const]
    ring
  have hleft : Integrable (fun g : ℕ → ℕ → ℝ =>
      |∑' σ : J → α, (∏ j, w (σ j)) *
        (Φ σ * g (iota (σ r₀)).1 (iota (σ r₀)).2)|) μ := by
    exact (integrable_gaussian_gibbs_replica_untilted u hu0 hu iota r₀ Φ M hΦ).abs
  have hright : Integrable (fun g : ℕ → ℕ → ℝ =>
      M / (∑' a, u a) * ∑' a, u a * |g (iota a).1 (iota a).2|) μ :=
    hmass.2.const_mul _
  have hle := integral_mono_ae hleft hright hbound
  change (∫ g, |∑' σ : J → α,
      (∏ j, w (σ j)) * (Φ σ * g (iota (σ r₀)).1 (iota (σ r₀)).2)| ∂μ) ≤ _
  calc
    _ ≤ ∫ g : ℕ → ℕ → ℝ,
        M / (∑' a, u a) * ∑' a, u a * |g (iota a).1 (iota a).2| ∂μ := hle
    _ = M * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
      rw [integral_const_mul,
        integral_gaussian_weighted_abs_eq u (fun a => (hu0 a).le) hu iota]
      field_simp

/-- A random active-index replica series can be expressed on the fixed type of block-index
tuples. The guard is determined solely by the block counts; this removes the dependent
index type before applying product-space measurability or Fubini. -/
theorem tsum_poissonBlocks_active_eq_tsum_guard
    {J : Type*} [Fintype J] (N : ℕ → ℕ)
    (f : (J → {p : ℕ × ℕ // p.2 < N p.1}) → ℝ) :
    (∑' σ : J → {p : ℕ × ℕ // p.2 < N p.1}, f σ) =
      ∑' σ : J → ℕ × ℕ,
        if h : ∀ j, (σ j).2 < N (σ j).1 then
          f (fun j => ⟨σ j, h j⟩) else 0 := by
  classical
  exact tsum_pi_subtype_eq_tsum_ite (J := J)
    (s := {p : ℕ × ℕ | p.2 < N p.1}) f

/-- For a fixed environment the guarded series agrees with the replica series over
its active block indices. In particular its denominator is the total active mass.
This statement has no probabilistic assumptions and applies to the extra IBP replica. -/
theorem gaussian_gibbs_replica_guard_eq_active
    {J : Type*} [Fintype J] (z : ℕ → ℕ × (ℕ → ℝ))
    (g : ℕ → ℕ → ℝ) (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ) :
    let α := {p : ℕ × ℕ // p.2 < (z p.1).1}
    (∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (z (σ j).1).1 then
        (∏ j, (z (σ j).1).2 (σ j).2 /
          ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) *
          (Φ σ * g (σ r₀).1 (σ r₀).2)
      else 0) =
    ∑' σ : J → α,
      (∏ j, (z (σ j).1.1).2 (σ j).1.2 /
        ∑' a : α, (z a.1.1).2 a.1.2) *
        (Φ (fun j => (σ j).1) * g (σ r₀).1.1 (σ r₀).1.2) := by
  classical
  let α := {p : ℕ × ℕ // p.2 < (z p.1).1}
  have hden : (∑' a : α, (z a.1.1).2 a.1.2) =
      ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0 := by
    have ht := tsum_subtype {p : ℕ × ℕ | p.2 < (z p.1).1}
      (fun p : ℕ × ℕ => (z p.1).2 p.2)
    change (∑' a : {p : ℕ × ℕ | p.2 < (z p.1).1},
      (z a.1.1).2 a.1.2) = _
    rw [ht]
    apply tsum_congr
    intro p
    by_cases hp : p.2 < (z p.1).1 <;> simp [Set.indicator, hp]
  let f : (J → α) → ℝ := fun σ =>
    (∏ j, (z (σ j).1.1).2 (σ j).1.2 /
      ∑' a : α, (z a.1.1).2 a.1.2) *
      (Φ (fun j => (σ j).1) * g (σ r₀).1.1 (σ r₀).1.2)
  change (∑' σ : J → ℕ × ℕ, if ∀ j, (σ j).2 < (z (σ j).1).1 then
    (∏ j, (z (σ j).1).2 (σ j).2 /
      ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) *
      (Φ σ * g (σ r₀).1 (σ r₀).2) else 0) = ∑' σ : J → α, f σ
  rw [tsum_poissonBlocks_active_eq_tsum_guard (fun n => (z n).1) f]
  apply tsum_congr
  intro σ
  split_ifs with h
  · dsimp only [f]
    rw [hden]
  · rfl

/-- A guarded replica series is measurable jointly in the block environment and the marks.
The weights and observable are arbitrary measurable coordinate functions; this formulation
applies both to Gaussian-marked Gibbs averages and to their bounded overlap terms. -/
theorem measurable_tsum_guarded_replica
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {J : Type*} [Fintype J] (N : S → ℕ → ℕ)
    (hN : ∀ m, Measurable fun z => N z m)
    (w : S × T → ℕ × ℕ → ℝ)
    (hw : ∀ p, Measurable fun zg => w zg p)
    (F : S × T → (J → ℕ × ℕ) → ℝ)
    (hF : ∀ σ, Measurable fun zg => F zg σ) :
    Measurable fun zg : S × T =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < N zg.1 (σ j).1 then
          (∏ j, w zg (σ j) / ∑' p : ℕ × ℕ,
            if p.2 < N zg.1 p.1 then w zg p else 0) * F zg σ
        else 0 := by
  classical
  have hden : Measurable fun zg : S × T =>
      ∑' p : ℕ × ℕ, if p.2 < N zg.1 p.1 then w zg p else 0 := by
    apply Measurable.tsum
    intro p
    exact (hw p).ite (measurableSet_lt measurable_const
      ((hN p.1).comp measurable_fst)) measurable_const
  apply Measurable.tsum
  intro σ
  have hguard : MeasurableSet {zg : S × T | ∀ j, (σ j).2 < N zg.1 (σ j).1} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const
      ((hN (σ j).1).comp measurable_fst)
  have hprod : Measurable fun zg : S × T => ∏ j, w zg (σ j) / (
      ∑' p : ℕ × ℕ, if p.2 < N zg.1 p.1 then w zg p else 0) := by
    exact Finset.measurable_prod _ fun j _ => (hw (σ j)).div hden
  exact (hprod.mul (hF σ)).ite hguard measurable_const

/-- The guarded un-tilted Gaussian-marked replica series is jointly measurable
for an arbitrary bounded index observable. No measurable structure on that
observable is needed because each fixed tuple has a fixed value. -/
theorem measurable_gaussian_gibbs_replica_guard_of_index
    {J : Type*} [Fintype J] (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ) :
    Measurable fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
            (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
        else 0 := by
  classical
  apply measurable_tsum_guarded_replica
    (S := ℕ → ℕ × (ℕ → ℝ)) (T := ℕ → ℕ → ℝ)
    (N := fun z m => (z m).1)
    (w := fun zg p => (zg.1 p.1).2 p.2)
    (F := fun zg σ => Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
  · intro m
    fun_prop
  · intro p
    fun_prop
  · intro σ
    fun_prop

/-- The fixed-index Gaussian-marked Gibbs replica observable is jointly measurable in
block counts, masses and Gaussian marks. The guard avoids dependent active index types. -/
theorem measurable_gaussian_gibbs_replica_guard
    {J : Type*} [Fintype J] [DecidableEq (ℕ × ℕ)]
    (t : ℝ) (r₀ : J) (f : (J → J → ℝ) → ℝ) :
    Measurable fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ,
              if p.2 < (zg.1 p.1).1 then
                (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (f (fun i j => if σ i = σ j then 1 else 0) *
              zg.2 (σ r₀).1 (σ r₀).2)
        else 0 := by
  classical
  apply measurable_tsum_guarded_replica
    (S := ℕ → ℕ × (ℕ → ℝ)) (T := ℕ → ℕ → ℝ)
    (N := fun z m => (z m).1)
    (w := fun zg p => (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2))
    (F := fun zg σ => f (fun i j => if σ i = σ j then 1 else 0) *
      zg.2 (σ r₀).1 (σ r₀).2)
  · intro m
    fun_prop
  · intro p
    fun_prop
  · intro σ
    fun_prop

/-- The hypotheses on the active environment are measurable on the fixed space
of counts and masses. In particular, the dependent active-index summability
predicate is equivalent, under positivity, to convergence of a fixed nonnegative
series, avoiding a dependent measurable index type. -/
theorem measurableSet_gaussian_gibbs_environment :
    MeasurableSet {z : ℕ → ℕ × (ℕ → ℝ) |
      Nonempty {p : ℕ × ℕ // p.2 < (z p.1).1} ∧
      (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
      (∑' p : ℕ × ℕ,
        ENNReal.ofReal (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) < ∞} := by
  classical
  have hN : MeasurableSet {z : ℕ → ℕ × (ℕ → ℝ) |
      Nonempty {p : ℕ × ℕ // p.2 < (z p.1).1}} := by
    have h : MeasurableSet {z : ℕ → ℕ × (ℕ → ℝ) |
        ∃ p : ℕ × ℕ, p.2 < (z p.1).1} := by
      have h' := MeasurableSet.iUnion (f := fun p : ℕ × ℕ =>
        {z : ℕ → ℕ × (ℕ → ℝ) | p.2 < (z p.1).1}) fun p =>
          measurableSet_lt measurable_const (by fun_prop)
      convert h' using 1
      ext z
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    convert h using 1
    ext z
    simp only [nonempty_subtype]
  have hP : MeasurableSet {z : ℕ → ℕ × (ℕ → ℝ) |
      ∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2} := by
    have h' := MeasurableSet.iInter (f := fun p : ℕ × ℕ =>
        {z : ℕ → ℕ × (ℕ → ℝ) |
          p.2 < (z p.1).1 → 0 < (z p.1).2 p.2}) fun p =>
      (by
        have hguard : MeasurableSet
            {z : ℕ → ℕ × (ℕ → ℝ) | p.2 < (z p.1).1} :=
          measurableSet_lt measurable_const (by fun_prop)
        have hpositive : MeasurableSet
            {z : ℕ → ℕ × (ℕ → ℝ) | 0 < (z p.1).2 p.2} :=
          measurableSet_lt measurable_const (by fun_prop)
        convert hguard.compl.union hpositive using 1
        ext z
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
        tauto)
    convert h' using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  have hS : MeasurableSet {z : ℕ → ℕ × (ℕ → ℝ) |
      (∑' p : ℕ × ℕ,
        ENNReal.ofReal (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) < ∞} := by
    have hm : Measurable fun z : ℕ → ℕ × (ℕ → ℝ) =>
        ∑' p : ℕ × ℕ,
          ENNReal.ofReal (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) := by
      apply Measurable.tsum
      intro p
      exact (ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable
        (fun z : ℕ → ℕ × (ℕ → ℝ) => (z p.1).2 p.2)).ite
        (measurableSet_lt measurable_const (by fun_prop)) measurable_const))
    exact measurableSet_lt hm measurable_const
  convert (hN.inter hP).inter hS using 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]

/-- A normalized deterministic mass environment gives an integrable guarded replica
observable under the Gaussian array. The same first-moment bound holds for every
such environment, independently of the number and positions of active atoms. -/
theorem gaussian_gibbs_replica_guard_integrable_and_bound
    {J : Type*} [Fintype J] (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M)
    (z : ℕ → ℕ × (ℕ → ℝ))
    (hn : ∃ p : ℕ × ℕ, p.2 < (z p.1).1)
    (hp : ∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2)
    (hs : Summable (fun p : ℕ × ℕ =>
      if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    let H : (ℕ → ℕ → ℝ) → ℝ := fun g =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (z (σ j).1).1 then
          (∏ j, (z (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) *
            (Φ σ * g (σ r₀).1 (σ r₀).2)
        else 0
    Integrable H μ ∧
      (∫ g, |H g| ∂μ) ≤ M * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
  classical
  let α := {p : ℕ × ℕ // p.2 < (z p.1).1}
  let _ : Nonempty α := by obtain ⟨p, hp'⟩ := hn; exact ⟨⟨p, hp'⟩⟩
  let u : α → ℝ := fun p => (z p.1.1).2 p.1.2
  have hu (p : α) : 0 < u p := hp p.1 p.2
  have hsum : Summable u := by
    apply (summable_subtype_iff_indicator (s :=
      {p : ℕ × ℕ | p.2 < (z p.1).1})
      (f := fun p : ℕ × ℕ => (z p.1).2 p.2)).2
    convert hs using 1
    funext p
    by_cases h : p.2 < (z p.1).1 <;> simp [Set.indicator, h]
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  let H : (ℕ → ℕ → ℝ) → ℝ := fun g =>
    ∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (z (σ j).1).1 then
        (∏ j, (z (σ j).1).2 (σ j).2 /
          ∑' p : ℕ × ℕ,
            if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) *
          (Φ σ * g (σ r₀).1 (σ r₀).2)
      else 0
  have heq (g : ℕ → ℕ → ℝ) : H g =
      ∑' σ : J → α,
        (∏ j, u (σ j) / ∑' a, u a) *
          (Φ (fun j => (σ j).1) * g (σ r₀).1.1 (σ r₀).1.2) :=
    gaussian_gibbs_replica_guard_eq_active z g r₀ Φ
  have hΦα : ∀ σ : J → α, |Φ (fun j => (σ j).1)| ≤ M := fun σ => hΦ _
  constructor
  · have h := integrable_gaussian_gibbs_replica_untilted u hu hsum Subtype.val r₀
      (fun σ => Φ (fun j => (σ j).1)) M hΦα
    simpa only [← heq] using h
  · have h := integral_abs_gaussian_gibbs_replica_untilted_le u hu hsum Subtype.val r₀
      (fun σ => Φ (fun j => (σ j).1)) M hΦα
    simpa only [← heq] using h

/-- Conditional on a positive summable mass environment, an un-tilted Gibbs
observable with one centered Gaussian mark has expectation zero. Unlike the
nonzero-tilt formula, this uses only the zero-covariance case of countable IBP. -/
theorem integral_gaussian_gibbs_replica_guard_untilted_eq_zero
    {J : Type*} [Fintype J] (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M)
    (z : ℕ → ℕ × (ℕ → ℝ))
    (hn : ∃ p : ℕ × ℕ, p.2 < (z p.1).1)
    (hp : ∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2)
    (hs : Summable (fun p : ℕ × ℕ =>
      if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    ∫ g, ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (z (σ j).1).1 then
          (∏ j, (z (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) *
            (Φ σ * g (σ r₀).1 (σ r₀).2)
        else 0 ∂μ = 0 := by
  classical
  let α := {p : ℕ × ℕ // p.2 < (z p.1).1}
  let _ : Nonempty α := by obtain ⟨p, hp'⟩ := hn; exact ⟨⟨p, hp'⟩⟩
  let u : α → ℝ := fun p => (z p.1.1).2 p.1.2
  have hu (p : α) : 0 < u p := hp p.1 p.2
  have hsum : Summable u := by
    apply (summable_subtype_iff_indicator (s :=
      {p : ℕ × ℕ | p.2 < (z p.1).1})
      (f := fun p : ℕ × ℕ => (z p.1).2 p.2)).2
    convert hs using 1
    funext p
    by_cases h : p.2 < (z p.1).1 <;> simp [Set.indicator, h]
  have hΦα : ∀ σ : J → α, |Φ (fun j => (σ j).1)| ≤ M := fun σ => hΦ _
  rw [show (fun g : ℕ → ℕ → ℝ =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (z (σ j).1).1 then
          (∏ j, (z (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) *
            (Φ σ * g (σ r₀).1 (σ r₀).2)
        else 0) = (fun g =>
      ∑' σ : J → α,
        (∏ j, u (σ j) / ∑' a, u a) *
          (Φ (fun j => (σ j).1) * g (σ r₀).1.1 (σ r₀).1.2)) from
    funext fun g => gaussian_gibbs_replica_guard_eq_active z g r₀ Φ]
  have h := integral_gibbs_replica_average_gaussian_active
    Subtype.val Subtype.val_injective u hu hsum 0 r₀
    (fun σ : J → α => Φ (fun j => (σ j).1)) hΦα
  simpa only [zero_mul, Real.exp_zero, mul_one, mul_zero, Finset.sum_const_zero,
    sub_zero, tsum_zero, mul_zero, integral_zero] using h

/-- For almost every split-block environment, the guarded un-tilted Gibbs
observable is conditionally integrable, with a uniform Gaussian first-moment
bound. Its three environment hypotheses are transported through the measurable
law of the counts and masses. -/
theorem ae_gaussian_gibbs_replica_untilted_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    {J : Type*} [Fintype J] (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M) :
    let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
      fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
            (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
        else 0
    ∀ᵐ z ∂P.map Z,
      Integrable (fun g => H (z, g)) μ ∧
      (∫ g, |H (z, g)| ∂μ) ≤ M * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
  have hZm : Measurable Z := measurable_pi_iff.2 fun n => by
    exact (measurable_fst.comp (hBm n)).prodMk
      (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          (measurable_snd.comp (hBm n))))
  have henv := ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
    (fun n => (ν n).prod (gaussianReal 0 1)) r hBm hB hlaw hμ
  have hZenv : ∀ᵐ z ∂P.map Z,
      (∃ p : ℕ × ℕ, p.2 < (z p.1).1) ∧
      (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
      (∑' p : ℕ × ℕ,
        ENNReal.ofReal (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) < ∞ := by
    have hh : ∀ᵐ z ∂P.map Z,
        Nonempty {p : ℕ × ℕ // p.2 < (z p.1).1} ∧
        (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
        (∑' p : ℕ × ℕ,
          ENNReal.ofReal (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) < ∞ :=
      (ae_map_iff hZm.aemeasurable measurableSet_gaussian_gibbs_environment).2 (by
        filter_upwards [henv] with ω ⟨hn, hp, hs⟩
        refine ⟨?_, ?_, ?_⟩
        · exact hn
        · intro p h
          exact hp ⟨p, h⟩
        · have ht : Summable (fun p : ℕ × ℕ =>
              if p.2 < (Z ω p.1).1 then (Z ω p.1).2 p.2 else 0) := by
            have ht' := (summable_subtype_iff_indicator (s :=
              {p : ℕ × ℕ | p.2 < (Z ω p.1).1})
              (f := fun p : ℕ × ℕ => (Z ω p.1).2 p.2)).1 hs
            convert ht' using 1
            funext p
            by_cases h : p.2 < (Z ω p.1).1 <;> simp [Set.indicator, h]
          exact ht.tsum_ofReal_lt_top)
    filter_upwards [hh] with z ⟨hn, hp, hS⟩
    exact ⟨hn.elim fun p => ⟨p.1, p.2⟩, hp, hS⟩
  filter_upwards [hZenv] with z ⟨hn, hp, hS⟩
  have hnonneg (p : ℕ × ℕ) :
      0 ≤ if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0 := by
    split_ifs with h
    · exact (hp p h).le
    · exact le_refl 0
  have hs : Summable (fun p : ℕ × ℕ =>
      if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) :=
    summable_of_tsum_ofReal_lt_top hnonneg hS
  exact gaussian_gibbs_replica_guard_integrable_and_bound r₀ Φ M hΦ z hn hp hs

/-- The un-tilted guarded marked replica observable is jointly integrable under
the product law of the mass environment and the independent Gaussian array.
The pointwise normalized mass cancels in the uniform conditional bound. -/
theorem integrable_gaussian_gibbs_replica_guard_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    {J : Type*} [Fintype J] (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M) :
    let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
      fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
            (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
        else 0
    Integrable H ((P.map Z).prod μ) := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
          ∑' p : ℕ × ℕ,
            if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
          (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
      else 0
  have hmeas : Measurable H := measurable_gaussian_gibbs_replica_guard_of_index r₀ Φ
  have hbound := ae_gaussian_gibbs_replica_untilted_bound hζ hζ1
    ν r hBm hB hlaw hμ r₀ Φ M hΦ
  have hZ : IsProbabilityMeasure (P.map Z) := by
    have hZm : Measurable Z := measurable_pi_iff.2 fun n => by
      exact (measurable_fst.comp (hBm n)).prodMk
        (measurable_pi_iff.2 fun l =>
          measurable_fst.comp ((measurable_pi_apply l).comp
            (measurable_snd.comp (hBm n))))
    exact (Measure.isProbabilityMeasure_map_iff hZm.aemeasurable).2 inferInstance
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).2
  constructor
  · exact hbound.mono fun z hz => hz.1
  · have hconst : Integrable (fun _ : ℕ → ℕ × (ℕ → ℝ) =>
        M * ∫ x : ℝ, |x| ∂gaussianReal 0 1) (P.map Z) := integrable_const _
    have hle : ∀ᵐ z ∂P.map Z,
        ‖∫ g, ‖H (z, g)‖ ∂μ‖ ≤ M * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
      filter_upwards [hbound] with z hz
      have hnonneg : 0 ≤ ∫ g, ‖H (z, g)‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
      change |∫ g, |H (z, g)| ∂μ| ≤ _
      have hnonneg' : 0 ≤ ∫ g, |H (z, g)| ∂μ := by
        simpa only [Real.norm_eq_abs] using hnonneg
      rw [abs_of_nonneg hnonneg']
      exact hz.2
    have houter : AEStronglyMeasurable
        (fun z => ∫ g, ‖H (z, g)‖ ∂μ) (P.map Z) :=
      hmeas.aestronglyMeasurable.norm.integral_prod_right'
    exact hconst.mono' houter hle

/-- Split-block independence transfers the product-space integrability of the
un-tilted guarded Gibbs average to the original probability space. This is the
integrability needed before applying Fubini and comparing with the tilted process. -/
theorem integrable_gaussian_gibbs_replica_guard_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    {J : Type*} [Fintype J] (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M) :
    let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
      fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
    let G : Ω → ℕ → ℕ → ℝ := fun ω n l => ((B n ω).2 l).2
    let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
            (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
        else 0
    Integrable (fun ω => H (Z ω, G ω)) P := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω n l => ((B n ω).2 l).2
  let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
          ∑' p : ℕ × ℕ,
            if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
          (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
      else 0
  have hsplit := indepFun_poissonBlocks_snd_marks ν
    (fun _ => gaussianReal 0 1) r hBm hB hlaw
  have hZm : Measurable Z := measurable_pi_iff.2 fun n => by
    exact (measurable_fst.comp (hBm n)).prodMk
      (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          (measurable_snd.comp (hBm n))))
  have hGm : Measurable G := measurable_pi_iff.2 fun n =>
    measurable_pi_iff.2 fun l =>
      measurable_snd.comp ((measurable_pi_apply l).comp
        (measurable_snd.comp (hBm n)))
  have hmeas : Measurable H := measurable_gaussian_gibbs_replica_guard_of_index r₀ Φ
  have hprod := integrable_gaussian_gibbs_replica_guard_prod hζ hζ1
    ν r hBm hB hlaw hμ r₀ Φ M hΦ
  have hG : P.map G = Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 := hsplit.2.1.map_eq
  rw [← hG] at hprod
  exact (IndepFun.integrable_comp_prod_iff hsplit.1 hZm hGm
    hmeas.aestronglyMeasurable).2 hprod

/-- The un-tilted block Gibbs average with one Gaussian mark has expectation zero.
The count/mass environment is independent of the Gaussian array, and the preceding
conditional zero-tilt IBP identity applies to almost every environment. -/
theorem integral_gaussian_gibbs_replica_guard_blocks_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    {J : Type*} [Fintype J] (r₀ : J) (Φ : (J → ℕ × ℕ) → ℝ)
    (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M) :
    let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
      fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
    let G : Ω → ℕ → ℕ → ℝ := fun ω n l => ((B n ω).2 l).2
    let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
            ∑' p : ℕ × ℕ,
              if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
            (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
        else 0
    ∫ ω, H (Z ω, G ω) ∂P = 0 := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω n l => ((B n ω).2 l).2
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, (zg.1 (σ j).1).2 (σ j).2 /
          ∑' p : ℕ × ℕ,
            if p.2 < (zg.1 p.1).1 then (zg.1 p.1).2 p.2 else 0) *
          (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
      else 0
  have hsplit := indepFun_poissonBlocks_snd_marks ν
    (fun _ => gaussianReal 0 1) r hBm hB hlaw
  have hZm : Measurable Z := measurable_pi_iff.2 fun n => by
    exact (measurable_fst.comp (hBm n)).prodMk
      (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          (measurable_snd.comp (hBm n))))
  have hGm : Measurable G := measurable_pi_iff.2 fun n =>
    measurable_pi_iff.2 fun l =>
      measurable_snd.comp ((measurable_pi_apply l).comp
        (measurable_snd.comp (hBm n)))
  have hprod := integrable_gaussian_gibbs_replica_guard_prod hζ hζ1
    ν r hBm hB hlaw hμ r₀ Φ M hΦ
  have hG : P.map G = μ := hsplit.2.1.map_eq
  change Integrable H ((P.map Z).prod μ) at hprod
  rw [← hG] at hprod
  change (∫ ω, H (Z ω, G ω) ∂P) = 0
  rw [IndepFun.integral_comp_prod hsplit.1 hZm hGm hprod]
  have henv := ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
    (fun n => (ν n).prod (gaussianReal 0 1)) r hBm hB hlaw hμ
  have hcond : ∀ᵐ z ∂P.map Z, ∫ g, H (z, g) ∂(P.map G) = 0 := by
    rw [hG]
    have hh : ∀ᵐ z ∂P.map Z,
        (∃ p : ℕ × ℕ, p.2 < (z p.1).1) ∧
        (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
        (∑' p : ℕ × ℕ,
          ENNReal.ofReal (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) < ∞ := by
      have hset := measurableSet_gaussian_gibbs_environment
      have henv' := (ae_map_iff hZm.aemeasurable hset).2 (by
        filter_upwards [henv] with ω ⟨hn, hp, hs⟩
        refine ⟨hn, (fun p h => hp ⟨p, h⟩), ?_⟩
        have ht := (summable_subtype_iff_indicator (s :=
          {p : ℕ × ℕ | p.2 < (Z ω p.1).1})
          (f := fun p : ℕ × ℕ => (Z ω p.1).2 p.2)).1 hs
        have ht' : Summable (fun p : ℕ × ℕ =>
            if p.2 < (Z ω p.1).1 then (Z ω p.1).2 p.2 else 0) := by
          convert ht using 1
          funext p
          by_cases h : p.2 < (Z ω p.1).1 <;> simp [Set.indicator, h]
        exact ht'.tsum_ofReal_lt_top)
      filter_upwards [henv'] with z ⟨hn, hp, hs⟩
      exact ⟨hn.elim fun p => ⟨p.1, p.2⟩, hp, hs⟩
    filter_upwards [hh] with z ⟨hn, hp, hS⟩
    have hnonneg (p : ℕ × ℕ) :
        0 ≤ if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0 := by
      split_ifs with h
      · exact (hp p h).le
      · exact le_refl 0
    exact integral_gaussian_gibbs_replica_guard_untilted_eq_zero
      r₀ Φ M hΦ z hn hp (summable_of_tsum_ofReal_lt_top hnonneg hS)
  rw [integral_congr_ae hcond, integral_zero]

/-- **Lemma 2.3's replica average as a Gibbs series over block indices.** For a counting measure
whose active atoms `(xₚ, yₚ)` have positive masses and are pairwise distinct, the ratio of
order-free integrals
`∫ (∏ₗ xₗ) f(R) ∏ₗ yₗ^{kₗ} dM^{⊗n} / ∫ ∏ₗ xₗ dM^{⊗n}` against `M` restricted to `{x > 0}` is the
series `∑_σ (∏ₗ x_{σₗ} / ∑ₚ xₚ) f(1{σₗ = σₗ'}) ∏ₗ y_{σₗ}^{kₗ}` over replica tuples of block
indices: the overlap of two atoms is the indicator that their indices coincide. -/
theorem integral_div_pi_poissonCountingMeasure_restrict_pos_eq_tsum
    (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ × ℝ)
    [SigmaFinite ((poissonCountingMeasure N X).restrict (Set.Ioi 0 ×ˢ Set.univ))]
    (hpos : ∀ p : {p : ℕ × ℕ // p.2 < N p.1}, 0 < (X p.1.1 p.1.2).1)
    (hinj : ∀ a b : {p : ℕ × ℕ // p.2 < N p.1}, X a.1.1 a.1.2 = X b.1.1 b.1.2 → a = b)
    (n : ℕ) (k : Fin n → ℕ) (f : (Fin n → Fin n → ℝ) → ℝ) :
    (∫ q, (∏ l, (q l).1) * (f (fun l l' => if q l = q l' then 1 else 0) * ∏ l, (q l).2 ^ k l)
        ∂Measure.pi fun _ : Fin n =>
          (poissonCountingMeasure N X).restrict (Set.Ioi 0 ×ˢ Set.univ)) /
      (∫ q, ∏ l, (q l).1 ∂Measure.pi fun _ : Fin n =>
          (poissonCountingMeasure N X).restrict (Set.Ioi 0 ×ˢ Set.univ)) =
    ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < N p.1},
      (∏ i, (X (σ i).1.1 (σ i).1.2).1 / ∑' p : {p : ℕ × ℕ // p.2 < N p.1},
          (X p.1.1 p.1.2).1) *
        (f (fun i j => if σ i = σ j then 1 else 0) * ∏ i, (X (σ i).1.1 (σ i).1.2).2 ^ k i) := by
  have hA : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  rw [integral_div_pi_poissonCountingMeasure_restrict_eq_tsum N X hA Prod.fst n]
  have hW : ∑' p : {p : ℕ × ℕ // p.2 < N p.1},
      (if X p.1.1 p.1.2 ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) then (X p.1.1 p.1.2).1 else 0) =
      ∑' p : {p : ℕ × ℕ // p.2 < N p.1}, (X p.1.1 p.1.2).1 :=
    tsum_congr fun p => by simp [hpos p]
  rw [hW]
  refine tsum_congr fun σ => ?_
  have hg : ∀ i, X (σ i).1.1 (σ i).1.2 ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := fun i => by
    simpa using hpos (σ i)
  have hR : (fun i j => if X (σ i).1.1 (σ i).1.2 = X (σ j).1.1 (σ j).1.2 then (1 : ℝ) else 0) =
      fun i j => if σ i = σ j then 1 else 0 := by
    funext i j
    exact if_congr ⟨hinj _ _, fun h => by rw [h]⟩ rfl rfl
  simp only [hg, implies_true, ↓reduceIte, hR]

/-- The intensity of the transformed process of Lemma 2.3 is the pushforward of the reference
intensity under `T(u, g) = (u, (exp (t (g - tζ/2)), g - tζ))`, so the transformed process can be
realized on the probability space of the reference blocks by applying `T` to every atom. -/
theorem intensity_tilt_eq_sum_map {ζ : ℝ} (t : ℝ) (ν' : ℕ → Measure (ℝ × ℝ)) (r' : ℕ → ℝ≥0)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n) :
    (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum fun n => (r' n : ℝ≥0∞) •
        (ν' n).map (fun p : ℝ × ℝ => (p.1, (Real.exp (t * (p.2 - t * ζ / 2)), p.2 - t * ζ))) := by
  have hh : Measurable fun g : ℝ => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ) := by fun_prop
  have hT : Measurable fun p : ℝ × ℝ =>
      (p.1, (Real.exp (t * (p.2 - t * ζ / 2)), p.2 - t * ζ)) := by fun_prop
  rw [← poissonIntensity_map ν' r' hT, ← hμ']
  have h := Measure.map_prod_map (zetaPoissonMeasure ζ) (gaussianReal 0 1) measurable_id hh
  rw [Measure.map_id] at h
  exact h


/-- **Distributional Lemma 2.3 in block-index Gibbs form.** For the Gaussian-marked
reference process with atoms `(uₚ, gₚ)`, `p = (n, l)`, `l < Nₙ`, and an overlap observable `f`,
the tilted Gibbs average (weights `uₚ exp (t gₚ)`, marks `gₚ - tζ`) has the same law as
the reference Gibbs average (weights `uₚ`, marks `gₚ`). Overlaps are index coincidences. -/
theorem identDistrib_gibbs_tilt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B' : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' P)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod (Measure.infinitePi fun _ : ℕ => ν' n)) P)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n)
    (n : ℕ) (k : Fin n → ℕ) {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Measurable f) :
    IdentDistrib (fun ω => ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).1 * Real.exp (t * ((B' (σ i).1.1 ω).2 (σ i).1.2).2) /
          ∑' p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
            ((B' p.1.1 ω).2 p.1.2).1 * Real.exp (t * ((B' p.1.1 ω).2 p.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, (((B' (σ i).1.1 ω).2 (σ i).1.2).2 - t * ζ) ^ k i))
      (fun ω => ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).1 /
          ∑' p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1}, ((B' p.1.1 ω).2 p.1.2).1) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).2 ^ k i)) P P := by
  let Tt : ℝ × ℝ → ℝ × (ℝ × ℝ) :=
    fun p => (p.1, (Real.exp (t * (p.2 - t * ζ / 2)), p.2 - t * ζ))
  have hTt : Measurable Tt := by fun_prop
  have hν : ∀ m, IsProbabilityMeasure ((ν' m).map Tt) := fun m => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm' hB' hlaw' hTt
  have hμt := intensity_tilt_eq_sum_map t ν' r' hμ'
  have hid := identDistrib_replica_average_poissonDirichlet_gaussian hζ t
    (fun m => (ν' m).map Tt) r' hCm hCi hClaw hμt ν' r' hBm' hB' hlaw' hμ' n k hf
  have hpos := ae_poissonDirichlet_gaussian_mass_pos ν' r' hlaw' hμ'
  have hnull : ∀ m, r' m ≠ 0 → NullSingletonClass (ν' m) := by
    intro m hm
    have h := nullSingletonClass_map_block ν' r' measurable_id
      (by rw [Measure.map_id, ← hμ']; infer_instance) hm
    rwa [Measure.map_id] at h
  have hdist := ae_poissonBlocks_point_eq_iff_index_eq ν' r' hBm' hB' hlaw' hnull
  have hsf0 := ae_sigmaFinite_poissonDirichlet_gaussian_restrict_pos hζ ν' r' hBm' hB' hlaw' hμ'
  have hshell := ae_forall_measure_Ioi_inv_succ_transform_lt_top hζ t
    (fun m => (ν' m).map Tt) r' hCm hCi hClaw hμt ν' r' hBm' hB' hlaw' hμ'
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => (p.1 * p.2.1, p.2.2) := by fun_prop
  refine (IdentDistrib.of_ae_eq hid.aemeasurable_fst ?_).symm.trans
    (hid.trans (IdentDistrib.of_ae_eq hid.aemeasurable_snd ?_))
  · filter_upwards [hpos, hdist, hshell] with ω h1 h2 h3
    have hmap := poissonCountingMeasure_map (fun j => (B' j ω).1)
      (fun j l => Tt ((B' j ω).2 l)) hm
    have h3' : ∀ k : ℕ, poissonCountingMeasure (fun j => (B' j ω).1)
        (fun j l => (((B' j ω).2 l).1 * Real.exp (t * (((B' j ω).2 l).2 - t * ζ / 2)),
          ((B' j ω).2 l).2 - t * ζ)) (Set.Ioi (1 / ((k : ℝ) + 1)) ×ˢ Set.univ) < ∞ := by
      intro k
      have := h3 k
      rwa [hmap] at this
    have hsf := sigmaFinite_poissonCountingMeasure_restrict_pos_of_shells
      (fun j => (B' j ω).1) (fun j l => (((B' j ω).2 l).1 *
        Real.exp (t * (((B' j ω).2 l).2 - t * ζ / 2)), ((B' j ω).2 l).2 - t * ζ)) h3'
    let _ := hsf
    have hpos' : ∀ p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        0 < ((B' p.1.1 ω).2 p.1.2).1 * Real.exp (t * (((B' p.1.1 ω).2 p.1.2).2 - t * ζ / 2)) :=
      fun p => mul_pos (h1 p.1.1 p.1.2 p.2) (Real.exp_pos _)
    have hinj' : ∀ a b : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (((B' a.1.1 ω).2 a.1.2).1 * Real.exp (t * (((B' a.1.1 ω).2 a.1.2).2 - t * ζ / 2)),
          ((B' a.1.1 ω).2 a.1.2).2 - t * ζ) =
        (((B' b.1.1 ω).2 b.1.2).1 * Real.exp (t * (((B' b.1.1 ω).2 b.1.2).2 - t * ζ / 2)),
          ((B' b.1.1 ω).2 b.1.2).2 - t * ζ) → a = b := by
      intro a b hab
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj hab
      have hg : ((B' a.1.1 ω).2 a.1.2).2 = ((B' b.1.1 ω).2 b.1.2).2 := sub_left_injective h₂
      rw [hg] at h₁
      have hu := mul_right_cancel₀ (Real.exp_pos _).ne' h₁
      exact (h2 a b).1 (Prod.ext hu hg)
    rw [hmap]
    rw [integral_div_pi_poissonCountingMeasure_restrict_pos_eq_tsum _ _ hpos' hinj' n k f]
    have hc0 : Real.exp (-(t * t * ζ / 2)) ≠ 0 := (Real.exp_pos _).ne'
    have hw : ∀ u g : ℝ, u * Real.exp (t * (g - t * ζ / 2)) =
        Real.exp (-(t * t * ζ / 2)) * (u * Real.exp (t * g)) := by
      intro u g
      have : t * (g - t * ζ / 2) = -(t * t * ζ / 2) + t * g := by ring
      rw [this, Real.exp_add]
      ring
    simp only [Tt, hw, tsum_mul_left, mul_div_mul_left _ _ hc0]
  · filter_upwards [hpos, hdist, hsf0] with ω h1 h2 h3
    let _ := h3
    exact (integral_div_pi_poissonCountingMeasure_restrict_pos_eq_tsum (fun j => (B' j ω).1)
      (fun j l => (B' j ω).2 l) (fun p => h1 p.1.1 p.1.2 p.2) (fun a b h => (h2 a b).1 h)
      n k f)


/-- **Lemma 2.3 in block-index Gibbs form, on one probability space.** For the Gaussian-marked
reference process with atoms `(uₚ, gₚ)`, `p = (n, l)`, `l < Nₙ`, and an overlap observable `f`,
the expected tilted Gibbs average (weights `uₚ exp (t gₚ)`, marks `gₚ - tζ`) equals the expected
reference Gibbs average (weights `uₚ`, marks `gₚ`). Overlaps are index coincidences. -/
theorem integral_gibbs_tilt_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B' : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' P)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod (Measure.infinitePi fun _ : ℕ => ν' n)) P)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n)
    (n : ℕ) (k : Fin n → ℕ) {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).1 * Real.exp (t * ((B' (σ i).1.1 ω).2 (σ i).1.2).2) /
          ∑' p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
            ((B' p.1.1 ω).2 p.1.2).1 * Real.exp (t * ((B' p.1.1 ω).2 p.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, (((B' (σ i).1.1 ω).2 (σ i).1.2).2 - t * ζ) ^ k i) ∂P =
      ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).1 /
          ∑' p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1}, ((B' p.1.1 ω).2 p.1.2).1) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).2 ^ k i) ∂P := by
  exact (identDistrib_gibbs_tilt hζ t ν' r' hBm' hB' hlaw' hμ' n k hf).integral_eq
/-- The Gaussian-marked Gibbs series with one centered mark is integrable even
at nonzero tilt. The un-tilted bound comes from the independent split blocks;
Lemma 2.3 transports it to the tilted process as equality in distribution. -/
theorem integrable_gibbs_tilt_centered_mark
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (t : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ) (hf : Measurable f) :
    Integrable (fun ω => ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).1 *
        Real.exp (t * ((B (σ i).1.1 ω).2 (σ i).1.2).2) /
        ∑' p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B p.1.1 ω).2 p.1.2).1 * Real.exp (t * ((B p.1.1 ω).2 p.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          (((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2 - t * ζ))) P := by
  classical
  let ν' : ℕ → Measure (ℝ × ℝ) := fun m => (ν m).prod (gaussianReal 0 1)
  let k : Fin n → ℕ := fun i => if i = r₀ then 1 else 0
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable
    (α := ℕ × ℕ) f
  let Φ : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  have hi : Integrable (fun ω => ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).1 /
        ∑' p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1}, ((B p.1.1 ω).2 p.1.2).1) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2)) P := by
    have h := integrable_gaussian_gibbs_replica_guard_blocks hζ hζ1
      ν r hBm hB hlaw hμ r₀ Φ M hM
    convert h using 1
    funext ω
    simp only [Φ]
    simpa only [Φ, Prod.fst, Prod.snd, Subtype.coe_inj] using
      (gaussian_gibbs_replica_guard_eq_active
        (fun m => ((B m ω).1, fun l => ((B m ω).2 l).1))
        (fun m l => ((B m ω).2 l).2) r₀ Φ).symm
  have hd := identDistrib_gibbs_tilt hζ t ν' r hBm hB hlaw hμ n k hf
  have hi' : Integrable (fun ω => ∑' σ : Fin n →
      {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).1 /
        ∑' p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B p.1.1 ω).2 p.1.2).1) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).2 ^ k i)) P := by
    convert hi using 1
    funext ω
    apply tsum_congr
    intro σ
    congr 1
    simp [k]
  have ht := hd.integrable_iff.mpr hi'
  convert ht using 1
  funext ω
  apply tsum_congr
  intro σ
  congr 1
  simp [k]

end SpinGlasses
