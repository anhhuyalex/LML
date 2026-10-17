/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraExpectation

/-!
# Centering overlap observables under Gaussian Poisson--Dirichlet tilts

An algebraic identity for random normalized replica weights, with no
assumptions about the probability space or the provenance of the weights.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- If the marked and plain series converge almost surely, removing a constant
from the mark amounts to adding that constant times the plain expected average.
Unlike `integral_gibbs_centered_mark_add_constant`, this version permits the
index set and the replica observable to depend on the random environment. -/
theorem integral_gibbs_centered_mark_add_constant_dep
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) (α : Ω → Type*)
    (w : (ω : Ω) → α ω → ℝ)
    (Φ : (ω : Ω) → (J → α ω) → ℝ)
    (x : (ω : Ω) → (J → α ω) → ℝ) (c : ℝ)
    (hs : ∀ᵐ ω ∂P, Summable (fun σ : J → α ω =>
      (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c))) ∧
      Summable (fun σ : J → α ω => (∏ j, w ω (σ j)) * Φ ω σ))
    (hcenter : Integrable (fun ω => ∑' σ : J → α ω,
      (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c))) P)
    (hplain : Integrable (fun ω => ∑' σ : J → α ω,
      (∏ j, w ω (σ j)) * Φ ω σ) P) :
    (∫ ω, ∑' σ : J → α ω,
      (∏ j, w ω (σ j)) * (Φ ω σ * x ω σ) ∂P) =
      (∫ ω, ∑' σ : J → α ω,
        (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c)) ∂P) +
        c * ∫ ω, ∑' σ : J → α ω,
          (∏ j, w ω (σ j)) * Φ ω σ ∂P := by
  have hpoint : ∀ᵐ ω ∂P,
      (∑' σ : J → α ω, (∏ j, w ω (σ j)) * (Φ ω σ * x ω σ)) =
        (∑' σ : J → α ω,
          (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c))) +
          c * ∑' σ : J → α ω, (∏ j, w ω (σ j)) * Φ ω σ := by
    filter_upwards [hs] with ω ⟨hmark, hbase⟩
    have hterm (σ : J → α ω) :
        (∏ j, w ω (σ j)) * (Φ ω σ * x ω σ) =
          (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c)) +
            c * ((∏ j, w ω (σ j)) * Φ ω σ) := by ring
    simp_rw [hterm]
    rw [hmark.tsum_add (hbase.mul_left c), tsum_mul_left]
  rw [integral_congr_ae hpoint, integral_add hcenter (hplain.const_mul c),
    integral_const_mul]

/-- Almost surely the centered marked tilted Gibbs series and its bounded
unmarked companion both converge on the random active index type. -/
theorem ae_poissonDirichlet_gaussian_tilt_centering_series
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (t c : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : ProbabilityTheory.iIndepFun B P)
    (hlaw : ∀ n, ProbabilityTheory.HasLaw (B n)
      ((ProbabilityTheory.poissonMeasure (r n)).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (ProbabilityTheory.gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (ProbabilityTheory.gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) •
        (ν n).prod (ProbabilityTheory.gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ) :
    ∀ᵐ ω ∂P,
      Summable (fun σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          (((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2 - c))) ∧
      Summable (fun σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        f (fun i j => if σ i = σ j then 1 else 0)) := by
  classical
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω m l => ((B m ω).2 l).2
  let Φ : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  have hZm : Measurable Z := measurable_poissonBlocks_counts_fst hBm
  have hGm : Measurable G := measurable_poissonBlocks_snd hBm
  have hsplit := indepFun_poissonBlocks_snd_marks ν
    (fun _ => ProbabilityTheory.gaussianReal 0 1) r hBm hB hlaw
  have henv := ae_poissonDirichlet_environment_map hζ hζ1 ν r hBm hB hlaw hμ
  have hprod := ae_gaussian_gibbs_tilt_mark_summable_prod t c (P.map Z)
    (henv.mono fun z hz => ⟨hz.2.1, hz.2.2⟩)
  have hpair : P.map (fun ω => (Z ω, G ω)) =
      (P.map Z).prod (P.map G) :=
    hsplit.1.map_prod_eq_prod_map_map hZm.aemeasurable hGm.aemeasurable
  have hmark : ∀ᵐ ω ∂P,
      (∑' p : ℕ × ℕ, ENNReal.ofReal
        (if p.2 < (Z ω p.1).1 then
          (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2) *
            |G ω p.1 p.2 - c| else 0)) < ⊤ := by
    have hmap : ∀ᵐ zg ∂P.map (fun ω => (Z ω, G ω)),
        (∑' p : ℕ × ℕ, ENNReal.ofReal
          (if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) *
              |zg.2 p.1 p.2 - c| else 0)) < ⊤ := by
      rw [hpair, hsplit.2.1.map_eq]
      exact hprod
    exact (ae_map_iff (hZm.prodMk hGm).aemeasurable
      (measurableSet_gaussian_gibbs_tilt_mark_summable t c)).1 hmap
  have hmass := ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
    (fun m => (ν m).prod (ProbabilityTheory.gaussianReal 0 1))
    r hBm hB hlaw hμ
  have hprodTilt := ae_gaussian_gibbs_tilt_summable_prod t (P.map Z)
    (henv.mono fun z hz => ⟨hz.2.1, hz.2.2⟩)
  have htilt : ∀ᵐ ω ∂P,
      (∑' p : ℕ × ℕ, ENNReal.ofReal
        (if p.2 < (Z ω p.1).1 then
          (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2) else 0)) < ⊤ := by
    have hmap : ∀ᵐ zg ∂P.map (fun ω => (Z ω, G ω)),
        (∑' p : ℕ × ℕ, ENNReal.ofReal
          (if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0)) < ⊤ := by
      rw [hpair, hsplit.2.1.map_eq]
      exact hprodTilt
    exact (ae_map_iff (hZm.prodMk hGm).aemeasurable
      (measurableSet_gaussian_gibbs_tilt_summable t)).1 hmap
  filter_upwards [hmark, htilt, hmass] with ω hm ht ⟨hn, hp, hs⟩
  let α := {p : ℕ × ℕ // p.2 < (B p.1 ω).1}
  let _ : Nonempty α := hn
  let u : α → ℝ := fun a => ((B a.1.1 ω).2 a.1.2).1
  let g : α → ℝ := fun a => ((B a.1.1 ω).2 a.1.2).2
  have hu (a : α) : 0 ≤ u a := (hp a).le
  have hus : Summable u := hs
  have hms0 : Summable (fun p : ℕ × ℕ =>
      if p.2 < (Z ω p.1).1 then
        (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2) *
          |G ω p.1 p.2 - c| else 0) := by
    apply summable_of_tsum_ofReal_lt_top (fun p => ?_) hm
    split_ifs with h
    · exact mul_nonneg (mul_nonneg (hp ⟨p, h⟩).le (Real.exp_pos _).le)
        (abs_nonneg _)
    · exact le_refl 0
  have hms : Summable (fun a : α =>
      u a * Real.exp (t * g a) * |g a - c|) :=
    (summable_subtype_guard_iff (fun p : ℕ × ℕ => p.2 < (Z ω p.1).1)
      (fun p : ℕ × ℕ =>
        (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2) *
          |G ω p.1 p.2 - c|)).2 hms0
  have hts0 : Summable (fun p : ℕ × ℕ =>
      if p.2 < (Z ω p.1).1 then
        (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2) else 0) := by
    apply summable_of_tsum_ofReal_lt_top (fun p => ?_) ht
    split_ifs with h
    · exact mul_nonneg (hp ⟨p, h⟩).le (Real.exp_pos _).le
    · exact le_refl 0
  have hts : Summable (fun a : α => u a * Real.exp (t * g a)) :=
    (summable_subtype_guard_iff (fun p : ℕ × ℕ => p.2 < (Z ω p.1).1)
      (fun p : ℕ × ℕ =>
        (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2))).2 hts0
  let v : α → ℝ := fun a => u a * Real.exp (t * g a)
  have hv (a : α) : 0 < v a := mul_pos (hp a) (Real.exp_pos _)
  have hV : 0 < ∑' a, v a :=
    hts.tsum_pos (fun a => (hv a).le) (Classical.choice inferInstance) (hv _)
  let w : α → ℝ := fun a => v a / ∑' b, v b
  have hw (a : α) : 0 ≤ w a := div_nonneg (hv a).le hV.le
  have hws : Summable w := hts.div_const _
  have hχ : Summable (fun a : α => w a * |g a - c|) := by
    convert hms.div_const (∑' b, v b) using 1
    funext a
    dsimp [w, v]
    ring
  have hΦ (σ : Fin n → α) :
      |f (fun i j => if σ i = σ j then 1 else 0)| ≤ M := by
    simpa only [Subtype.coe_inj] using hM (fun i => (σ i).1)
  have hcenter := summable_prod_pi_mul_abs_eval hw hws hχ r₀ hΦ
  have hcenter' : Summable (fun σ : Fin n → α =>
      (∏ j, w (σ j)) *
        (f (fun i j => if σ i = σ j then 1 else 0) * (g (σ r₀) - c))) := by
    have hh : Summable (fun σ : Fin n → α =>
        ‖(∏ j, w (σ j)) *
          (f (fun i j => if σ i = σ j then 1 else 0) * (g (σ r₀) - c))‖) := by
      convert hcenter using 1
      funext σ
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Finset.prod_nonneg fun j _ => hw (σ j))]
    exact hh.of_norm
  have hbase : Summable (fun σ : Fin n → α =>
      (∏ j, w (σ j)) * f (fun i j => if σ i = σ j then 1 else 0)) := by
    apply (summable_prod_pi (J := Fin n) (f := fun _ => w)
      (fun _ a => hw a) (fun _ => hws)).mul_right M |>.of_norm_bounded
    intro σ
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun j _ => hw (σ j))]
    exact mul_le_mul_of_nonneg_left (hΦ σ)
      (Finset.prod_nonneg fun j _ => hw (σ j))
  exact ⟨hcenter', hbase⟩

/-- The tilted expectation of an uncentered Gaussian mark is the centered
expectation plus the centering constant times the plain overlap expectation. -/
theorem integral_poissonDirichlet_gaussian_tilt_mark_centering
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
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2) ∂P) =
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          (((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2 - t * ζ)) ∂P) +
      t * ζ * ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
            Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P := by
  let α (ω : Ω) := {p : ℕ × ℕ // p.2 < (B p.1 ω).1}
  let w (ω : Ω) (a : α ω) :=
    ((B a.1.1 ω).2 a.1.2).1 * Real.exp (t * ((B a.1.1 ω).2 a.1.2).2) /
      ∑' b : α ω, ((B b.1.1 ω).2 b.1.2).1 *
        Real.exp (t * ((B b.1.1 ω).2 b.1.2).2)
  let Φ (ω : Ω) (σ : Fin n → α ω) :=
    f (fun i j => if σ i = σ j then 1 else 0)
  let x (ω : Ω) (σ : Fin n → α ω) := ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2
  have hs := ae_poissonDirichlet_gaussian_tilt_centering_series
    hζ hζ1 t (t * ζ) ν r hBm hB hlaw hμ n r₀ f
  have hc := integrable_gibbs_tilt_centered_mark
    hζ hζ1 t ν r hBm hB hlaw hμ n r₀ f hf
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω m l => ((B m ω).2 l).2
  let ρ : Measure (ℕ → ℕ × (ℕ → ℝ)) := P.map Z
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hZm : Measurable Z := measurable_poissonBlocks_counts_fst hBm
  have hρ : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff hZm.aemeasurable).2 inferInstance
  have henv := ae_poissonDirichlet_environment_map hζ hζ1 ν r hBm hB hlaw hμ
  let F : (Fin n → ℕ × ℕ) → ℝ :=
    fun σ => f (fun i j => if σ i = σ j then 1 else 0)
  have hp : Integrable (fun zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) =>
      ∑' σ : Fin n → ℕ × ℕ,
        if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
          (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
              Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) * F σ
        else 0) (ρ.prod μ) :=
    by
      convert integrable_gaussian_gibbs_tilt_bounded_prod t F M hM ρ henv using 1
      funext zg
      apply tsum_congr
      intro σ
      split_ifs <;> rfl
  let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : Fin n → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
            Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) * F σ
      else 0
  have hG : P.map G = μ :=
    (indepFun_poissonBlocks_snd_marks ν
      (fun _ => gaussianReal 0 1) r hBm hB hlaw).2.1.map_eq
  have hp' : Integrable (fun ω => H (Z ω, G ω)) P := by
    apply (IndepFun.integrable_comp_prod_iff
      (indepFun_poissonBlocks_snd_marks ν
        (fun _ => gaussianReal 0 1) r hBm hB hlaw).1
      hZm (measurable_poissonBlocks_snd hBm)
      (by rw [hG]; exact hp.aestronglyMeasurable)).2
    rw [hG]
    exact hp
  have hplain : Integrable (fun ω => ∑' σ : Fin n → α ω,
      (∏ j, w ω (σ j)) * Φ ω σ) P := by
    convert hp' using 1
    funext ω
    simpa only [H, Z, G, F, w, Φ, Prod.fst, Prod.snd, Subtype.coe_inj] using
      (gaussian_gibbs_tilt_guard_eq_active t (Z ω) (G ω) F).symm
  exact integral_gibbs_centered_mark_add_constant_dep P α w Φ x (t * ζ)
    hs hc hplain

/-- At unit Gaussian tilt the expected marked overlap is zeta times the
untilted expected overlap. This is the probabilistic input to Theorem 2.7. -/
theorem integral_poissonDirichlet_gaussian_unit_tilt_mark
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
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
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2) ∂P) =
      ζ * ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P := by
  classical
  let k : Fin n → ℕ := fun i => if i = r₀ then 1 else 0
  let ν' : ℕ → Measure (ℝ × ℝ) := fun m => (ν m).prod (gaussianReal 0 1)
  have hzero := integral_gaussian_gibbs_replica_guard_blocks_eq_zero
    hζ hζ1 ν r hBm hB hlaw hμ r₀
    (fun σ : Fin n → ℕ × ℕ => f (fun i j => if σ i = σ j then 1 else 0))
    (Classical.choose (exists_bound_index_overlap_observable (α := ℕ × ℕ) f))
    (Classical.choose_spec (exists_bound_index_overlap_observable (α := ℕ × ℕ) f))
  have hmark : (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2) ∂P) = 0 := by
    calc
      _ = ∫ ω, (∑' σ : Fin n → ℕ × ℕ,
          if ∀ j, (σ j).2 < (B (σ j).1 ω).1 then
            (∏ j, ((B (σ j).1 ω).2 (σ j).2).1 /
              ∑' p : ℕ × ℕ, if p.2 < (B p.1 ω).1 then
                ((B p.1 ω).2 p.2).1 else 0) *
              (f (fun i j => if σ i = σ j then 1 else 0) *
                ((B (σ r₀).1 ω).2 (σ r₀).2).2)
          else 0) ∂P := by
        congr 1
        funext ω
        simpa only [Prod.fst, Prod.snd, Subtype.coe_inj] using
          (gaussian_gibbs_replica_guard_eq_active
            (fun m => ((B m ω).1, fun l => ((B m ω).2 l).1))
            (fun m l => ((B m ω).2 l).2) r₀
            (fun σ : Fin n → ℕ × ℕ =>
              f (fun i j => if σ i = σ j then 1 else 0))).symm
      _ = 0 := by
        convert hzero using 1
        congr 1
        funext ω
        apply tsum_congr
        intro σ
        split_ifs <;> rfl
  have hcenter := integral_gibbs_tilt_eq hζ 1 ν' r hBm hB hlaw hμ n k hf
  have hprod_mark (ω : Ω)
      (σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1}) :
      (∏ i, (((B (σ i).1.1 ω).2 (σ i).1.2).2 - ζ) ^ k i) =
        ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2 - ζ := by
    simp only [k, pow_ite, Finset.prod_ite_eq', Finset.mem_univ,
      ite_true, pow_one, pow_zero]
  have hprod_mark0 (ω : Ω)
      (σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1}) :
      (∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).2 ^ k i) =
        ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2 := by
    simp only [k, pow_ite, Finset.prod_ite_eq', Finset.mem_univ,
      ite_true, pow_one, pow_zero]
  have hcenter' : (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          (((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2 - ζ)) ∂P) = 0 := by
    calc
      _ = ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).1 *
          Real.exp (1 * ((B (σ i).1.1 ω).2 (σ i).1.2).2) /
          ∑' p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B p.1.1 ω).2 p.1.2).1 *
              Real.exp (1 * ((B p.1.1 ω).2 p.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, (((B (σ i).1.1 ω).2 (σ i).1.2).2 - 1 * ζ) ^ k i) ∂P := by
        congr 1
        funext ω
        apply tsum_congr
        intro σ
        simp only [one_mul]
        rw [hprod_mark ω σ]
      _ = ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).1 /
          ∑' p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B p.1.1 ω).2 p.1.2).1) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).2 ^ k i) ∂P := hcenter
      _ = 0 := by
        convert hmark using 1
        congr 1
        funext ω
        apply tsum_congr
        intro σ
        rw [hprod_mark0 ω σ]
  have hplain := integral_gibbs_tilt_eq hζ 1 ν' r hBm hB hlaw hμ n (fun _ => 0) hf
  have hplain' : (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        f (fun i j => if σ i = σ j then 1 else 0) ∂P) =
      ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P := by
    convert hplain using 1
    · congr 1
      funext ω
      apply tsum_congr
      intro σ
      simp only [one_mul, pow_zero, Finset.prod_const_one, mul_one]
    · congr 1
      funext ω
      apply tsum_congr
      intro σ
      simp only [pow_zero, Finset.prod_const_one, mul_one]
  have hc := integral_poissonDirichlet_gaussian_tilt_mark_centering
    hζ hζ1 1 ν r hBm hB hlaw hμ n r₀ f hf
  simpa only [one_mul, hcenter', zero_add, hplain'] using hc


/-- Transfer integrability of a bounded Gaussian-tilted overlap observable
from the independent environment/mark product law to the original blocks. -/
theorem integrable_poissonDirichlet_gaussian_tilt_overlap
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (t : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (F : (J → ℕ × ℕ) → ℝ) (M : ℝ) (hF : ∀ σ, |F σ| ≤ M) :
    Integrable (fun ω => ∑' σ : J → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        F (fun j => (σ j).1)) P := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω m l => ((B m ω).2 l).2
  let ρ : Measure (ℕ → ℕ × (ℕ → ℝ)) := P.map Z
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hZm : Measurable Z := measurable_poissonBlocks_counts_fst hBm
  have hρ : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff hZm.aemeasurable).2 inferInstance
  have henv := ae_poissonDirichlet_environment_map hζ hζ1 ν r hBm hB hlaw hμ
  let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
            Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) * F σ
      else 0
  have hp : Integrable H (ρ.prod μ) :=
    integrable_gaussian_gibbs_tilt_bounded_prod t F M hF ρ henv
  have hG : P.map G = μ :=
    (indepFun_poissonBlocks_snd_marks ν
      (fun _ => gaussianReal 0 1) r hBm hB hlaw).2.1.map_eq
  have hp' : Integrable (fun ω => H (Z ω, G ω)) P := by
    apply (IndepFun.integrable_comp_prod_iff
      (indepFun_poissonBlocks_snd_marks ν
        (fun _ => gaussianReal 0 1) r hBm hB hlaw).1
      hZm (measurable_poissonBlocks_snd hBm)
      (by rw [hG]; exact hp.aestronglyMeasurable)).2
    rw [hG]
    exact hp
  convert hp' using 1
  funext ω
  simpa only [H, Z, G, Prod.fst, Prod.snd, Subtype.coe_inj] using
    (gaussian_gibbs_tilt_guard_eq_active t (Z ω) (G ω) F).symm

end SpinGlasses
