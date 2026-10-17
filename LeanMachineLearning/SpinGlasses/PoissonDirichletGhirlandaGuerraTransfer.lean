/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerra

/-!
# Transferring marked Gaussian integration by parts to Poisson blocks

Separate the integrability of the uncentered Gaussian observable from conditional IBP.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

/-- In a positive summable environment, a bounded observable times a centered mark
is summable if and only if the corresponding uncentered observable is summable.
This is the pointwise series identity needed to add back the deterministic centering. -/
theorem gaussian_gibbs_mark_centering_identity
    {J α : Type*} [Fintype J]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : Summable w)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M)
    (x : (J → α) → ℝ) (c : ℝ)
    (hx : Summable (fun σ : J → α => (∏ j, w (σ j)) * (Φ σ * (x σ - c)))) :
    Summable (fun σ : J → α => (∏ j, w (σ j)) * (Φ σ * x σ)) ∧
    (∑' σ : J → α, (∏ j, w (σ j)) * (Φ σ * x σ)) =
      (∑' σ : J → α, (∏ j, w (σ j)) * (Φ σ * (x σ - c))) +
        c * ∑' σ : J → α, (∏ j, w (σ j)) * Φ σ := by
  classical
  have hbase := summable_prod_pi (J := J) (f := fun _ => w) (fun _ a => hw a)
    (fun _ => hs)
  have hbound : Summable (fun σ : J → α => (∏ j, w (σ j)) * Φ σ) := by
    apply (hbase.mul_right M).of_norm_bounded
    intro σ
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Finset.prod_nonneg
      (fun j _ => hw (σ j)))]
    exact mul_le_mul_of_nonneg_left (hΦ σ) (Finset.prod_nonneg fun j _ => hw (σ j))
  have hadd : (fun σ : J → α => (∏ j, w (σ j)) * (Φ σ * x σ)) =
      (fun σ => (∏ j, w (σ j)) * (Φ σ * (x σ - c))) +
        (fun σ => c * ((∏ j, w (σ j)) * Φ σ)) := by
    funext σ
    simp only [Pi.add_apply]
    ring
  have hlast : Summable (fun σ : J → α => c * ((∏ j, w (σ j)) * Φ σ)) :=
    hbound.mul_left c
  constructor
  · rw [hadd]
    exact hx.add hlast
  · rw [hadd]
    rw [← tsum_mul_left]
    exact hx.tsum_add hlast

/-- The normalized overlap marginal is the extra-replica series with an unused
`none` coordinate removed. This is independent of the origin of the weights. -/
theorem gaussian_gibbs_mark_centering_option_marginal
    {J α : Type*} [Fintype J]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : Summable w)
    (hunit : ∑' a, w a = 1)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    (∑' τ : Option J → α, (∏ o, w (τ o)) * Φ (fun j => τ (some j))) =
      ∑' σ : J → α, (∏ j, w (σ j)) * Φ σ :=
  gaussian_ibp_option_replica_marginal hw hs hunit Φ hΦ

/-- Centering a marked Gibbs series does not affect its convergence, and its
uncentered value is the centered value plus the bounded unmarked average. -/
theorem gaussian_gibbs_mark_centering_identity_of_masses
    {J α : Type*} [Fintype J] [Nonempty α]
    (u : α → ℝ) (hu : ∀ a, 0 < u a) (hs : Summable u)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M)
    (x : (J → α) → ℝ) (c : ℝ)
    (hx : Summable (fun σ : J → α =>
      (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * (x σ - c)))) :
    Summable (fun σ : J → α =>
      (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * x σ)) ∧
    (∑' σ : J → α, (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * x σ)) =
      (∑' σ : J → α,
        (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * (x σ - c))) +
        c * ∑' σ : J → α,
          (∏ j, u (σ j) / ∑' a, u a) * Φ σ := by
  have hpos : 0 < ∑' a, u a :=
    hs.tsum_pos (fun a => (hu a).le) (Classical.choice inferInstance) (hu _)
  exact gaussian_gibbs_mark_centering_identity
    (fun a => u a / ∑' b, u b)
    (fun a => div_nonneg (hu a).le hpos.le) (hs.div_const _) Φ hΦ x c hx

/-- Gaussian exponential weights remain absolutely summable when multiplied by
one Gaussian coordinate (and a fixed centering constant). This holds for any
countable collection of coordinates, without an independence assumption. -/
theorem ae_summable_gaussian_tilted_mark
    {α : Type*} [Countable α] (u : α → ℝ)
    (hu : ∀ a, 0 ≤ u a) (hs : Summable u)
    (iota : α → ℕ × ℕ) (t c : ℝ) :
    ∀ᵐ g ∂(Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1),
      Summable (fun a => u a * Real.exp (t * g (iota a).1 (iota a).2) *
        |g (iota a).1 (iota a).2 - c|) := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hlaw (a : α) : HasLaw (fun g : ℕ → ℕ → ℝ => g (iota a).1 (iota a).2)
      (gaussianReal 0 1) μ :=
    (hasLaw_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) (iota a).2).comp
      (hasLaw_eval_infinitePi
        (fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) (iota a).1)
  have h := ae_summable_and_integrable_tsum_mul_exp (P := μ) (G := u)
    (X := fun a g => g (iota a).1 (iota a).2 - c)
    (Z := fun a g => t * g (iota a).1 (iota a).2) hu hs
    (fun a => by simpa only [smul_eq_mul] using
      (hlaw a).hasGaussianLaw.fun_smul t)
    (fun a => by rw [integral_const_mul, integral_gaussianReal_coordinate hlaw a,
      mul_zero])
    (fun a => ((hlaw a).hasGaussianLaw.memLp_two).sub (memLp_const c))
    (a := 2 + 2 * c ^ 2) (v := t ^ 2)
    (fun a => by
      have hi := ((hlaw a).hasGaussianLaw.memLp_two.sub
        (memLp_const c)).integrable_sq
      have hsq := integral_gaussianReal_coordinate_sq hlaw a
      have hmean := integral_gaussianReal_coordinate hlaw a
      have heq : (fun g : ℕ → ℕ → ℝ =>
        (g (iota a).1 (iota a).2 - c) ^ 2) =
          (fun g => g (iota a).1 (iota a).2 ^ 2 -
            2 * c * g (iota a).1 (iota a).2 + c ^ 2) := by
        funext g
        ring
      have hgi : Integrable (fun g : ℕ → ℕ → ℝ =>
          g (iota a).1 (iota a).2) μ :=
        ((hlaw a).hasGaussianLaw.memLp_two).integrable (by norm_num)
      have hsqint := ((hlaw a).hasGaussianLaw.memLp_two).integrable_sq
      rw [heq]
      have hadd : (∫ g : ℕ → ℕ → ℝ,
          g (iota a).1 (iota a).2 ^ 2 - 2 * c * g (iota a).1 (iota a).2 + c ^ 2 ∂μ) =
          (∫ g : ℕ → ℕ → ℝ,
            g (iota a).1 (iota a).2 ^ 2 - 2 * c * g (iota a).1 (iota a).2 ∂μ) +
            ∫ _ : ℕ → ℕ → ℝ, c ^ 2 ∂μ :=
        integral_add (hsqint.sub (hgi.const_mul _)) (integrable_const _)
      rw [hadd, integral_sub hsqint (hgi.const_mul _), integral_const_mul,
        integral_const, hsq, hmean]
      have hμ : μ.real Set.univ = 1 := by simp [μ]
      rw [hμ]
      simp only [one_smul, mul_zero, sub_zero]
      nlinarith [sq_nonneg c])
    (fun a => by
      simp_rw [mul_pow, integral_const_mul,
        integral_gaussianReal_coordinate_sq hlaw a, mul_one]
      exact le_refl _)
  filter_upwards [h.1] with g hg
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hg

/-- For positive summable masses, Gaussian-tilted replica series with a centered
mark converge absolutely for almost every Gaussian array. Both the tilted mass
sum and its marked variant are needed: one alone does not imply the other. -/
theorem ae_summable_gaussian_gibbs_centered_replica
    {α J : Type*} [Countable α] [Fintype J] [Nonempty α]
    (u : α → ℝ) (hu : ∀ a, 0 < u a) (hs : Summable u)
    (iota : α → ℕ × ℕ) (t c : ℝ) (r₀ : J)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    ∀ᵐ g ∂(Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1),
      Summable (fun σ : J → α =>
        (∏ j, u (σ j) * Real.exp (t * g (iota (σ j)).1 (iota (σ j)).2) /
          ∑' a, u a * Real.exp (t * g (iota a).1 (iota a).2)) *
          (Φ σ * (g (iota (σ r₀)).1 (iota (σ r₀)).2 - c))) := by
  have hm := ae_summable_gaussian_tilted_mark u (fun a => (hu a).le)
    hs iota t c
  have ht := ae_summable_active_gaussian_tilt u (fun a => (hu a).le)
    hs iota t
  filter_upwards [hm, ht] with g hmark htilt
  let v : α → ℝ := fun a =>
    u a * Real.exp (t * g (iota a).1 (iota a).2)
  have hv (a : α) : 0 < v a := mul_pos (hu a) (Real.exp_pos _)
  have hV : 0 < ∑' a, v a :=
    htilt.tsum_pos (fun a => (hv a).le) (Classical.choice inferInstance) (hv _)
  let w : α → ℝ := fun a => v a / ∑' b, v b
  have hw (a : α) : 0 ≤ w a := div_nonneg (hv a).le hV.le
  have hws : Summable w := htilt.div_const _
  have hχ : Summable (fun a => w a *
      |g (iota a).1 (iota a).2 - c|) := by
    have h := hmark.div_const (∑' b, v b)
    convert h using 1
    funext a
    simp only [w, v]
    ring
  have h := summable_prod_pi_mul_abs_eval hw hws hχ r₀ hΦ
  have hnorm : Summable (fun σ : J → α =>
      ‖(∏ j, w (σ j)) *
        (Φ σ * (g (iota (σ r₀)).1 (iota (σ r₀)).2 - c))‖) := by
    convert h using 1
    funext σ
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun j _ => hw (σ j))]
  exact hnorm.of_norm

/-- The marked exponential mass sum is measurable as a fixed-index ENNReal
series. Its finiteness expresses summability of the active marked masses without
placing a measurable structure on the environment-dependent subtype. -/
theorem measurableSet_gaussian_gibbs_tilt_mark_summable (t c : ℝ) :
    MeasurableSet {zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) |
      (∑' p : ℕ × ℕ, ENNReal.ofReal
        (if p.2 < (zg.1 p.1).1 then
          (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
            abs (zg.2 p.1 p.2 - c) else 0)) < ⊤} := by
  have hm : Measurable fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
      ∑' p : ℕ × ℕ, ENNReal.ofReal
        (if p.2 < (zg.1 p.1).1 then
          (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
            abs (zg.2 p.1 p.2 - c) else 0) := by
    apply Measurable.tsum
    intro p
    apply ENNReal.measurable_ofReal.comp
    exact ((by fun_prop : Measurable
      (fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
        (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
          abs (zg.2 p.1 p.2 - c))).ite
      (measurableSet_lt measurable_const (by fun_prop)) measurable_const)
  exact measurableSet_lt hm measurable_const

/-- An a.s. positive and summable mass environment has a.s. summable
Gaussian-tilted masses weighted by an absolute centered mark on the product law. -/
theorem ae_gaussian_gibbs_tilt_mark_summable_prod (t c : ℝ)
    (ρ : Measure (ℕ → ℕ × (ℕ → ℝ)))
    (henv : ∀ᵐ z ∂ρ,
      (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
      Summable (fun p : ℕ × ℕ =>
        if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    ∀ᵐ zg ∂ρ.prod μ,
      (∑' p : ℕ × ℕ, ENNReal.ofReal
        (if p.2 < (zg.1 p.1).1 then
          (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
            abs (zg.2 p.1 p.2 - c) else 0)) < ⊤ := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_gaussian_gibbs_tilt_mark_summable t c)]
  filter_upwards [henv] with z ⟨hp, hs⟩
  let α := {p : ℕ × ℕ // p.2 < (z p.1).1}
  let u : α → ℝ := fun p => (z p.1.1).2 p.1.2
  have hu (p : α) : 0 ≤ u p := (hp p.1 p.2).le
  have hus : Summable u := by
    apply (summable_subtype_iff_indicator (s :=
      {p : ℕ × ℕ | p.2 < (z p.1).1})
      (f := fun p : ℕ × ℕ => (z p.1).2 p.2)).2
    convert hs using 1
    funext p
    by_cases h : p.2 < (z p.1).1 <;> simp [Set.indicator, h]
  filter_upwards [ae_summable_gaussian_tilted_mark u hu hus Subtype.val t c] with g hg
  have ht := (summable_subtype_iff_indicator (s :=
      {p : ℕ × ℕ | p.2 < (z p.1).1})
      (f := fun p : ℕ × ℕ =>
        (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) * |g p.1 p.2 - c|)).1 hg
  have ht' : Summable (fun p : ℕ × ℕ =>
      if p.2 < (z p.1).1 then
        (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) * |g p.1 p.2 - c|
      else 0) := by
    convert ht using 1
    funext p
    by_cases h : p.2 < (z p.1).1 <;> simp [Set.indicator, h]
  exact ht'.tsum_ofReal_lt_top

/-- The centered marked tilted replica series is jointly measurable in the
block environment and the Gaussian array. -/
theorem measurable_gaussian_gibbs_tilt_centered_guard
    {J : Type*} [Fintype J] (t c : ℝ) (r₀ : J)
    (Φ : (J → ℕ × ℕ) → ℝ) :
    Measurable fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
      ∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (Φ σ * (zg.2 (σ r₀).1 (σ r₀).2 - c))
        else 0 := by
  classical
  apply measurable_tsum_guarded_replica
    (N := fun z : ℕ → ℕ × (ℕ → ℝ) => fun m => (z m).1)
    (w := fun (zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ)) p =>
      (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2))
    (F := fun (zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ)) σ =>
      Φ σ * (zg.2 (σ r₀).1 (σ r₀).2 - c))
  · intro m
    fun_prop
  · intro p
    fun_prop
  · intro σ
    fun_prop

/-- Lemma 2.3 supplies integrability of the centered tilted Gibbs series on
Poisson blocks; independent-mark splitting transports it to the product law. -/
theorem integrable_gaussian_gibbs_tilt_centered_guard_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (t : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ) (hf : Measurable f) :
    let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
      fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    Integrable (fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
      ∑' σ : Fin n → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (f (fun i j => if σ i = σ j then 1 else 0) *
              (zg.2 (σ r₀).1 (σ r₀).2 - t * ζ))
        else 0) ((P.map Z).prod μ) := by
  classical
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω m l => ((B m ω).2 l).2
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  let Φ : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : Fin n → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
            Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
          (Φ σ * (zg.2 (σ r₀).1 (σ r₀).2 - t * ζ))
      else 0
  have hsplit := indepFun_poissonBlocks_snd_marks ν
    (fun _ => gaussianReal 0 1) r hBm hB hlaw
  have hZm : Measurable Z := measurable_pi_iff.2 fun m =>
    (measurable_fst.comp (hBm m)).prodMk
      (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          (measurable_snd.comp (hBm m))))
  have hGm : Measurable G := measurable_pi_iff.2 fun m =>
    measurable_pi_iff.2 fun l =>
      measurable_snd.comp ((measurable_pi_apply l).comp
        (measurable_snd.comp (hBm m)))
  have hmeas : Measurable H := by
    simpa only [H] using measurable_gaussian_gibbs_tilt_centered_guard t
      (t * ζ) r₀ Φ
  have hblocks := integrable_gibbs_tilt_centered_mark hζ hζ1 t ν r
    hBm hB hlaw hμ n r₀ f hf
  have hpoint (ω : Ω) : H (Z ω, G ω) =
      ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
            Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            (((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2 - t * ζ)) := by
    simpa only [H, Z, G, Φ, Prod.fst, Prod.snd, Subtype.coe_inj] using
      (gaussian_gibbs_tilt_guard_eq_active t (Z ω) (G ω)
        (fun σ => Φ σ * ((G ω) (σ r₀).1 (σ r₀).2 - t * ζ)))
  have hcomp : Integrable (fun ω => H (Z ω, G ω)) P := by
    convert hblocks using 1
    funext ω
    exact hpoint ω
  have hG : P.map G = μ := hsplit.2.1.map_eq
  have hprod : Integrable H ((P.map Z).prod μ) := by
    rw [← hG]
    exact (IndepFun.integrable_comp_prod_iff hsplit.1 hZm hGm
      (by rw [hG]; exact hmeas.aestronglyMeasurable)).1 hcomp
  exact hprod

end SpinGlasses
