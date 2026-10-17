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
    hasLaw_eval_infinitePi_infinitePi (fun _ _ => gaussianReal 0 1) (iota a).1 (iota a).2
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
      rw [integral_gaussianReal_sub_const_sq (hlaw a) c]
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
  exact measurableSet_tsum_ofReal_guarded_lt_top
    (Ω := (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ)) (fun zg m => (zg.1 m).1)
    (fun m => by fun_prop)
    (fun zg p => (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
      abs (zg.2 p.1 p.2 - c)) (fun p => by fun_prop)

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
    exact (summable_subtype_guard_iff (fun p : ℕ × ℕ => p.2 < (z p.1).1)
      (fun p : ℕ × ℕ => (z p.1).2 p.2)).2 hs
  filter_upwards [ae_summable_gaussian_tilted_mark u hu hus Subtype.val t c] with g hg
  have ht' : Summable (fun p : ℕ × ℕ =>
      if p.2 < (z p.1).1 then
        (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) * |g p.1 p.2 - c|
      else 0) :=
    (summable_subtype_guard_iff (fun p : ℕ × ℕ => p.2 < (z p.1).1)
      (fun p : ℕ × ℕ =>
        (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) * |g p.1 p.2 - c|)).1 hg
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
  have hZm : Measurable Z := measurable_poissonBlocks_counts_fst hBm
  have hGm : Measurable G := measurable_poissonBlocks_snd hBm
  have hmeas : Measurable H := by
    convert measurable_gaussian_gibbs_tilt_centered_guard t
      (t * ζ) r₀ Φ using 1
    funext zg
    apply tsum_congr
    intro σ
    split_ifs <;> rfl
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

/-- For almost every independent environment and Gaussian array, centering can
be removed from a bounded tilted replica observable without changing convergence. -/
theorem ae_gaussian_gibbs_tilt_mark_centering_prod
    {J : Type*} [Fintype J] (t c : ℝ) (r₀ : J)
    (Φ : (J → ℕ × ℕ) → ℝ) (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M)
    (ρ : Measure (ℕ → ℕ × (ℕ → ℝ)))
    (henv : ∀ᵐ z ∂ρ,
      (∃ p : ℕ × ℕ, p.2 < (z p.1).1) ∧
      (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
      Summable (fun p : ℕ × ℕ =>
        if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    ∀ᵐ zg ∂ρ.prod μ,
      (∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
        else 0) =
      (∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (Φ σ * (zg.2 (σ r₀).1 (σ r₀).2 - c))
        else 0) + c *
      (∑' σ : J → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) * Φ σ
        else 0) := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have ht := ae_gaussian_gibbs_tilt_summable_prod t ρ
    (henv.mono fun z hz => ⟨hz.2.1, hz.2.2⟩)
  have hm := ae_gaussian_gibbs_tilt_mark_summable_prod t c ρ
    (henv.mono fun z hz => ⟨hz.2.1, hz.2.2⟩)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae henv, ht, hm]
    with zg ⟨hn, hp, hs⟩ htilt hmark
  let α := {p : ℕ × ℕ // p.2 < (zg.1 p.1).1}
  let _ : Nonempty α := by obtain ⟨p, h⟩ := hn; exact ⟨⟨p, h⟩⟩
  let u : α → ℝ := fun a =>
    (zg.1 a.1.1).2 a.1.2 * Real.exp (t * zg.2 a.1.1 a.1.2)
  have hu (a : α) : 0 < u a := mul_pos (hp a.1 a.2) (Real.exp_pos _)
  have ht0 : Summable (fun p : ℕ × ℕ =>
      if p.2 < (zg.1 p.1).1 then
        (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) := by
    apply summable_of_tsum_ofReal_lt_top (fun p => ?_) htilt
    split_ifs with h
    · exact (mul_pos (hp p h) (Real.exp_pos _)).le
    · exact le_refl 0
  have hus : Summable u := by
    exact (summable_subtype_guard_iff (fun p : ℕ × ℕ => p.2 < (zg.1 p.1).1)
      (fun p : ℕ × ℕ =>
        (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2))).2 ht0
  have hm0 : Summable (fun p : ℕ × ℕ =>
      if p.2 < (zg.1 p.1).1 then
        (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
          |zg.2 p.1 p.2 - c| else 0) := by
    apply summable_of_tsum_ofReal_lt_top (fun p => ?_) hmark
    split_ifs with h
    · exact mul_nonneg (mul_pos (hp p h) (Real.exp_pos _)).le (abs_nonneg _)
    · exact le_refl 0
  have hms : Summable (fun a : α =>
      u a * |zg.2 a.1.1 a.1.2 - c|) := by
    exact (summable_subtype_guard_iff (fun p : ℕ × ℕ => p.2 < (zg.1 p.1).1)
      (fun p : ℕ × ℕ =>
        (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
          |zg.2 p.1 p.2 - c|)).2 hm0
  have hpos : 0 < ∑' a, u a :=
    hus.tsum_pos (fun a => (hu a).le) (Classical.choice inferInstance) (hu _)
  let w : α → ℝ := fun a => u a / ∑' b, u b
  have hw (a : α) : 0 ≤ w a := div_nonneg (hu a).le hpos.le
  have hws : Summable w := hus.div_const _
  have hmarkw : Summable (fun a : α =>
      w a * |zg.2 a.1.1 a.1.2 - c|) := by
    convert hms.div_const (∑' b, u b) using 1
    funext a
    dsimp [w]
    ring
  have hc := summable_prod_pi_mul_abs_eval hw hws hmarkw r₀
    (fun σ : J → α => hΦ (fun j => (σ j).1))
  have hc' : Summable (fun σ : J → α =>
      (∏ j, w (σ j)) *
        (Φ (fun j => (σ j).1) * (zg.2 (σ r₀).1.1 (σ r₀).1.2 - c))) := by
    have hnorm : Summable (fun σ : J → α =>
        ‖(∏ j, w (σ j)) *
          (Φ (fun j => (σ j).1) * (zg.2 (σ r₀).1.1 (σ r₀).1.2 - c))‖) := by
      convert hc using 1
      funext σ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
        (Finset.prod_nonneg fun j _ => hw (σ j))]
    exact hnorm.of_norm
  have heq := (gaussian_gibbs_mark_centering_identity w hw hws
    (fun σ : J → α => Φ (fun j => (σ j).1))
    (fun σ => hΦ (fun j => (σ j).1))
    (fun σ => zg.2 (σ r₀).1.1 (σ r₀).1.2) c hc').2
  have hleft := gaussian_gibbs_tilt_guard_eq_active t zg.1 zg.2
    (fun σ => Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
  have hcenter := gaussian_gibbs_tilt_guard_eq_active t zg.1 zg.2
    (fun σ => Φ σ * (zg.2 (σ r₀).1 (σ r₀).2 - c))
  have hbase := gaussian_gibbs_tilt_guard_eq_active t zg.1 zg.2 Φ
  rw [hleft, hcenter, hbase]
  exact heq

/-- The marked (uncentered) tilted Gaussian replica average is jointly integrable.
The centered part comes from Lemma 2.3; the correction is a bounded Gibbs average. -/
theorem integrable_gaussian_gibbs_tilt_mark_guard_prod
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
              zg.2 (σ r₀).1 (σ r₀).2)
        else 0) ((P.map Z).prod μ) := by
  classical
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  let ρ : Measure (ℕ → ℕ × (ℕ → ℝ)) := P.map Z
  let Φ : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  have hZm : Measurable Z := measurable_poissonBlocks_counts_fst hBm
  have hρ : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff hZm.aemeasurable).2 inferInstance
  have henv := ae_poissonDirichlet_environment_map (P := P) hζ hζ1 ν r hBm hB hlaw hμ
  have hcenter := integrable_gaussian_gibbs_tilt_centered_guard_prod
    hζ hζ1 t ν r hBm hB hlaw hμ n r₀ f hf
  have hbase := integrable_gaussian_gibbs_tilt_bounded_prod t Φ M hM ρ henv
  have hpoint := ae_gaussian_gibbs_tilt_mark_centering_prod t (t * ζ)
    r₀ Φ M hM ρ henv
  have hmeas := measurable_gaussian_gibbs_replica_guard t r₀ f
  let L : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : Fin n → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
            Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
          (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
      else 0
  have hLm : AEStronglyMeasurable L (ρ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    convert hmeas using 1
    funext zg
    apply tsum_congr
    intro σ
    split_ifs <;> rfl
  have hsum := hcenter.add (hbase.const_mul (t * ζ))
  have hpoint' : L =ᵐ[ρ.prod μ] (fun zg =>
      (∑' σ : Fin n → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (Φ σ * (zg.2 (σ r₀).1 (σ r₀).2 - t * ζ))
        else 0) + t * ζ *
      (∑' σ : Fin n → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) * Φ σ
        else 0)) := by
    filter_upwards [hpoint] with zg hz
    have hfirst : L zg =
        ∑' σ : Fin n → ℕ × ℕ,
          if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
            (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
                Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
              ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
                (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
              (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
          else 0 := by
      apply tsum_congr
      intro σ
      split_ifs <;> rfl
    exact hfirst.trans (by
      convert hz using 1
      · apply tsum_congr
        intro σ
        split_ifs <;> rfl
      · apply congrArg₂ (· + ·)
        · apply tsum_congr
          intro σ
          split_ifs <;> rfl
        · congr 1
          apply tsum_congr
          intro σ
          split_ifs <;> rfl)
  have hL : Integrable L (ρ.prod μ) := by
    have hsum' : Integrable (fun zg =>
        (∑' σ : Fin n → ℕ × ℕ,
          if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
            (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
                Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
              ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
                (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
              (Φ σ * (zg.2 (σ r₀).1 (σ r₀).2 - t * ζ))
          else 0) + t * ζ *
        (∑' σ : Fin n → ℕ × ℕ,
          if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
            (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
                Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
              ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
                (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) * Φ σ
          else 0)) (ρ.prod μ) := by
      convert hsum using 1
      funext zg
      apply congrArg₂ (· + ·)
      · apply tsum_congr
        intro σ
        split_ifs <;> rfl
      · congr 1
        apply tsum_congr
        intro σ
        split_ifs <;> rfl
    exact hsum'.congr hpoint'.symm
  exact hL

/-- Expectation-level Gaussian IBP for the Gaussian-marked Poisson-Dirichlet
blocks, expressed on the independent product of count/mass and Gaussian laws. -/
theorem integral_poissonDirichlet_gaussian_tilt_ibp_prod
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
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
      fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
    let ρ : Measure (ℕ → ℕ × (ℕ → ℝ)) := P.map Z
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    (∫ zg, ∑' σ : Fin n → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
            Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            zg.2 (σ r₀).1 (σ r₀).2)
      else 0 ∂ρ.prod μ) =
    ∫ zg, ∑' τ : Option (Fin n) → ℕ × ℕ,
      if ∀ j, (τ j).2 < (zg.1 (τ j).1).1 then
        (∏ j, ((zg.1 (τ j).1).2 (τ j).2 *
            Real.exp (t * zg.2 (τ j).1 (τ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            (∑ j : Fin n, t *
              (if τ (some r₀) = τ (some j) then 1 else 0) -
              n * t * (if τ (some r₀) = τ none then 1 else 0)))
      else 0 ∂ρ.prod μ := by
  classical
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let ρ : Measure (ℕ → ℕ × (ℕ → ℝ)) := P.map Z
  let Φ : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  have hZm : Measurable Z := measurable_poissonBlocks_counts_fst hBm
  have hρ : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff hZm.aemeasurable).2 inferInstance
  have henv := ae_poissonDirichlet_environment_map (P := P) hζ hζ1 ν r hBm hB hlaw hμ
  have hleft := integrable_gaussian_gibbs_tilt_mark_guard_prod
    hζ hζ1 t ν r hBm hB hlaw hμ n r₀ f hf
  let _ : DecidableEq (Fin n) := Classical.decEq _
  have hleft' : Integrable (fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
      ∑' σ : Fin n → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
        else 0) (ρ.prod (Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
    convert hleft using 1
  have hIBP := integral_gaussian_gibbs_replica_guard_tilt_ibp_prod
    t r₀ Φ M hM ρ henv (by
      convert hleft' using 1
      funext zg
      apply tsum_congr
      intro σ
      split_ifs <;> rfl)
  simpa only [Φ, Fintype.card_fin] using hIBP

end SpinGlasses
