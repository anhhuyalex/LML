/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletIBPAlgebra

/-!
# Gaussian integration by parts after conditioning on the Poisson environment

The fixed count/mass environment has a random active subtype. Guarded sums on the fixed
index space allow integration over the independent environment and Gaussian-mark laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

/-- Reindex a normalized tilted replica average from active block indices to a
fixed ambient tuple type. This applies to arbitrary observables and replica sets,
including the extra `Option J` coordinate of Gaussian integration by parts. -/
theorem gaussian_gibbs_tilt_guard_eq_active
    {J : Type*} [Fintype J] (t : ℝ)
    (z : ℕ → ℕ × (ℕ → ℝ)) (g : ℕ → ℕ → ℝ)
    (F : (J → ℕ × ℕ) → ℝ) :
    (∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (z (σ j).1).1 then
        (∏ j, ((z (σ j).1).2 (σ j).2 * Real.exp (t * g (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then
            (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) else 0) * F σ
      else 0) =
    ∑' σ : J → {p : ℕ × ℕ // p.2 < (z p.1).1},
      (∏ j, (z (σ j).1.1).2 (σ j).1.2 *
          Real.exp (t * g (σ j).1.1 (σ j).1.2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (z p.1).1},
          (z a.1.1).2 a.1.2 * Real.exp (t * g a.1.1 a.1.2)) *
        F (fun j => (σ j).1) := by
  classical
  let α := {p : ℕ × ℕ // p.2 < (z p.1).1}
  have hden : (∑' a : α,
      (z a.1.1).2 a.1.2 * Real.exp (t * g a.1.1 a.1.2)) =
      ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then
        (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) else 0 := by
    have ht := tsum_subtype {p : ℕ × ℕ | p.2 < (z p.1).1}
      (fun p : ℕ × ℕ => (z p.1).2 p.2 * Real.exp (t * g p.1 p.2))
    change (∑' a : {p : ℕ × ℕ | p.2 < (z p.1).1},
      (z a.1.1).2 a.1.2 * Real.exp (t * g a.1.1 a.1.2)) = _
    rw [ht]
    apply tsum_congr
    intro p
    by_cases hh : p.2 < (z p.1).1 <;> simp [Set.indicator, hh]
  rw [tsum_poissonBlocks_active_eq_tsum_guard (fun n => (z n).1)]
  apply tsum_congr
  intro σ
  split_ifs with hh
  · rw [← hden]
  · rfl

/-- Gaussian IBP at nonzero tilt, conditional on one positive summable block environment.
The right hand side includes one extra replica, indexed by `Option J`. -/
theorem integral_gaussian_gibbs_replica_guard_tilt_ibp
    {J : Type*} [Fintype J] (t : ℝ) (r₀ : J)
    (Φ : (J → ℕ × ℕ) → ℝ) (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M)
    (z : ℕ → ℕ × (ℕ → ℝ))
    (hn : ∃ p : ℕ × ℕ, p.2 < (z p.1).1)
    (hp : ∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2)
    (hs : Summable (fun p : ℕ × ℕ =>
      if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    ∫ g, ∑' σ : J → ℕ × ℕ,
      if ∀ j, (σ j).2 < (z (σ j).1).1 then
        (∏ j, ((z (σ j).1).2 (σ j).2 * Real.exp (t * g (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then
            (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) else 0) *
          (Φ σ * g (σ r₀).1 (σ r₀).2)
      else 0 ∂μ =
    ∫ g, ∑' τ : Option J → ℕ × ℕ,
      if ∀ j, (τ j).2 < (z (τ j).1).1 then
        (∏ j, ((z (τ j).1).2 (τ j).2 * Real.exp (t * g (τ j).1 (τ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then
            (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) else 0) *
          (Φ (fun j => τ (some j)) *
            (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
              Fintype.card J * t *
                (if τ (some r₀) = τ none then 1 else 0)))
      else 0 ∂μ := by
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
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have h := integral_gibbs_replica_average_gaussian_active
    Subtype.val Subtype.val_injective u hu hsum t r₀
    (fun σ : J → α => Φ (fun j => (σ j).1)) hΦα
  have hrewrite {K : Type _} [Fintype K] (F : (K → ℕ × ℕ) → ℝ)
      (g : ℕ → ℕ → ℝ) :
      (∑' σ : K → ℕ × ℕ,
        if ∀ j, (σ j).2 < (z (σ j).1).1 then
          (∏ j, ((z (σ j).1).2 (σ j).2 * Real.exp (t * g (σ j).1 (σ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then
              (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) else 0) * F σ
        else 0) =
      ∑' σ : K → α,
        (∏ j, u (σ j) * Real.exp (t * g (σ j).1.1 (σ j).1.2) /
          ∑' a : α, u a * Real.exp (t * g a.1.1 a.1.2)) *
          F (fun j => (σ j).1) :=
    gaussian_gibbs_tilt_guard_eq_active t z g F
  change (∫ g, _ ∂μ) = ∫ g, _ ∂μ
  have hleft (g : ℕ → ℕ → ℝ) :=
    hrewrite (K := J) (fun σ => Φ σ * g (σ r₀).1 (σ r₀).2) g
  have hright (g : ℕ → ℕ → ℝ) :=
    hrewrite (K := Option J) (fun τ =>
      Φ (fun j => τ (some j)) *
        (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
          Fintype.card J * t *
            (if τ (some r₀) = τ none then 1 else 0))) g
  simp only [hleft, hright]
  simpa only [Subtype.coe_inj] using h

/-- A positive summable family of deterministic masses stays summable almost surely
after multiplying by exponentials of the independent Gaussian array. -/
theorem ae_summable_active_gaussian_tilt
    {α : Type*} [Countable α] (u : α → ℝ) (hu : ∀ a, 0 ≤ u a)
    (hs : Summable u) (iota : α → ℕ × ℕ) (t : ℝ) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    ∀ᵐ g ∂μ, Summable fun a => u a * Real.exp (t * g (iota a).1 (iota a).2) := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hlaw (a : α) : HasLaw (fun g : ℕ → ℕ → ℝ => g (iota a).1 (iota a).2)
      (gaussianReal 0 1) μ := by
    have hout := hasLaw_eval_infinitePi
      (fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) (iota a).1
    have hin := hasLaw_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) (iota a).2
    exact hin.comp hout
  have h := ae_summable_and_integrable_tsum_mul_exp (P := μ)
    (X := fun _ _ => (1 : ℝ))
    (Z := fun a g => t * g (iota a).1 (iota a).2) (G := u)
    hu hs (fun a => by simpa only [smul_eq_mul] using
      (hlaw a).hasGaussianLaw.fun_smul t)
    (fun a => by
      rw [integral_const_mul, integral_gaussianReal_coordinate (hlaw) a, mul_zero])
    (fun _ => memLp_const 1) (a := 1) (v := t ^ 2) (by simp)
    (fun a => by
      simp_rw [mul_pow, integral_const_mul,
        integral_gaussianReal_coordinate_sq hlaw a, mul_one]
      exact le_refl _)
  filter_upwards [h.1] with g hg
  simpa only [abs_one, one_mul, mul_assoc] using hg

/-- A covariance correction of finitely many zero-one overlaps is bounded by
`|t|` times the number of original replicas. The observable need only be bounded
on index-coincidence matrices. -/
theorem abs_gaussian_ibp_overlap_correction_le
    {J α : Type*} [Fintype J] [DecidableEq α]
    (t : ℝ) (r₀ : J) (τ : Option J → α)
    {Φ : (J → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    |Φ (fun j => τ (some j)) *
      ((∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0)) -
        (Fintype.card J : ℝ) * t *
          (if τ (some r₀) = τ none then 1 else 0))| ≤
      (Fintype.card J : ℝ) * M * |t| := by
  rw [gaussian_ibp_overlap_correction_factor, abs_mul, abs_mul]
  have hM := hΦ (fun j => τ (some j))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hsum : (∑ j : J,
      if τ (some r₀) = τ (some j) then (1 : ℝ) else 0) ≤ Fintype.card J := by
    simpa using Finset.sum_le_card_nsmul Finset.univ
      (fun j => if τ (some r₀) = τ (some j) then (1 : ℝ) else 0) 1
      (fun j _ => by split_ifs <;> norm_num)
  have hc : |(∑ j : J,
      if τ (some r₀) = τ (some j) then (1 : ℝ) else 0) -
      (Fintype.card J : ℝ) *
        (if τ (some r₀) = τ none then 1 else 0)| ≤ Fintype.card J :=
    abs_sub_le_of_nonneg_of_le
      (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) hsum
      (by positivity) (by split_ifs <;> simp)
  have hb := mul_le_mul hM hc (abs_nonneg _) hM0
  calc
    |Φ (fun j => τ (some j))| * (|t| * |(∑ j : J,
        if τ (some r₀) = τ (some j) then (1 : ℝ) else 0) -
        (Fintype.card J : ℝ) *
          (if τ (some r₀) = τ none then 1 else 0)|)
      = (|Φ (fun j => τ (some j))| * |(∑ j : J,
          if τ (some r₀) = τ (some j) then (1 : ℝ) else 0) -
          (Fintype.card J : ℝ) *
            (if τ (some r₀) = τ none then 1 else 0)|) * |t| := by ring
    _ ≤ (M * Fintype.card J) * |t| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = _ := by ring

end SpinGlasses

namespace SpinGlasses

/-- In a fixed positive summable environment, the extra-replica covariance correction
is integrable under the Gaussian law. Its bound does not depend on the environment. -/
theorem gaussian_gibbs_tilt_correction_integrable_and_bound
    {J : Type*} [Fintype J] (t : ℝ) (r₀ : J)
    (Φ : (J → ℕ × ℕ) → ℝ) (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M)
    (z : ℕ → ℕ × (ℕ → ℝ))
    (hn : ∃ p : ℕ × ℕ, p.2 < (z p.1).1)
    (hp : ∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2)
    (hs : Summable (fun p : ℕ × ℕ =>
      if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    let H : (ℕ → ℕ → ℝ) → ℝ := fun g =>
      ∑' τ : Option J → ℕ × ℕ,
        if ∀ j, (τ j).2 < (z (τ j).1).1 then
          (∏ j, ((z (τ j).1).2 (τ j).2 * Real.exp (t * g (τ j).1 (τ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then
              (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) else 0) *
            (Φ (fun j => τ (some j)) *
              (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
                Fintype.card J * t *
                  (if τ (some r₀) = τ none then 1 else 0)))
        else 0
    Integrable H μ ∧ ∀ᵐ g ∂μ, |H g| ≤ (Fintype.card J : ℝ) * M * |t| := by
  let α := {p : ℕ × ℕ // p.2 < (z p.1).1}
  let _ : Nonempty α := by obtain ⟨p, h⟩ := hn; exact ⟨⟨p, h⟩⟩
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
    ∑' τ : Option J → ℕ × ℕ,
      if ∀ j, (τ j).2 < (z (τ j).1).1 then
        (∏ j, ((z (τ j).1).2 (τ j).2 * Real.exp (t * g (τ j).1 (τ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (z p.1).1 then
            (z p.1).2 p.2 * Real.exp (t * g p.1 p.2) else 0) *
          (Φ (fun j => τ (some j)) *
            (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
              Fintype.card J * t *
                (if τ (some r₀) = τ none then 1 else 0)))
      else 0
  have hUpos : 0 < ∑' a, u a :=
    hsum.tsum_pos (fun a => (hu a).le) (Classical.choice inferInstance) (hu _)
  have hae := ae_summable_active_gaussian_tilt u (fun a => (hu a).le) hsum
    Subtype.val t
  have hmeas : Measurable H := by
    have hm := measurable_tsum_guarded_replica
      (fun z : ℕ → ℕ × (ℕ → ℝ) => fun n => (z n).1)
      (fun n => (measurable_pi_apply n).fst)
      (fun (zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ)) p =>
        (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2))
      (fun p => (by fun_prop))
      (fun _ τ => Φ (fun j => τ (some j)) *
        (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
          (Fintype.card J : ℝ) * t *
            (if τ (some r₀) = τ none then 1 else 0)))
      (fun _ => measurable_const)
    exact hm.comp (measurable_const.prodMk measurable_id)
  have hbound : ∀ᵐ g ∂μ, |H g| ≤ (Fintype.card J : ℝ) * M * |t| := by
    filter_upwards [hae] with g hg
    let v : α → ℝ := fun a => u a * Real.exp (t * g a.1.1 a.1.2)
    have hvpos (a : α) : 0 < v a := mul_pos (hu a) (Real.exp_pos _)
    have hvs : Summable v := hg
    have hVpos : 0 < ∑' a, v a :=
      hvs.tsum_pos (fun a => (hvpos a).le) (Classical.choice inferInstance) (hvpos _)
    let w : α → ℝ := fun a => v a / ∑' b, v b
    have hw0 (a : α) : 0 ≤ w a := div_nonneg (hvpos a).le hVpos.le
    have hws : Summable w := hvs.div_const _
    have hw : ∑' a, w a = 1 := by
      change (∑' a, v a / ∑' b, v b) = 1
      rw [tsum_div_const, div_self hVpos.ne']
    have hΦα : ∀ τ : Option J → α,
        |Φ (fun j => (τ (some j)).1) *
          (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
            Fintype.card J * t *
              (if τ (some r₀) = τ none then 1 else 0))| ≤
          (Fintype.card J : ℝ) * M * |t| :=
      fun τ => abs_gaussian_ibp_overlap_correction_le t r₀ τ
        (fun σ : J → α => hΦ (fun j => (σ j).1))
    have heq := gaussian_gibbs_tilt_guard_eq_active t z g
      (fun τ : Option J → ℕ × ℕ => Φ (fun j => τ (some j)) *
        (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
          Fintype.card J * t *
            (if τ (some r₀) = τ none then 1 else 0)))
    change H g = _ at heq
    rw [heq]
    apply abs_tsum_prod_pi_mul_le_bound hw0 hws hw
    intro τ
    simpa only [Subtype.coe_inj] using hΦα τ
  constructor
  · exact (integrable_const ((Fintype.card J : ℝ) * M * |t|)).mono'
      hmeas.aestronglyMeasurable (by
        filter_upwards [hbound] with g hg
        simpa only [Real.norm_eq_abs] using hg)
  · exact hbound

/-- The extra-replica Gaussian correction is jointly integrable whenever the
count/mass environment is almost surely nonempty, positive, and summable.
Its conditional bound is independent of the environment law. -/
theorem integrable_gaussian_gibbs_tilt_correction_prod
    {J : Type*} [Fintype J] (t : ℝ) (r₀ : J)
    (Φ : (J → ℕ × ℕ) → ℝ) (M : ℝ) (hΦ : ∀ σ, |Φ σ| ≤ M)
    (ρ : Measure (ℕ → ℕ × (ℕ → ℝ))) [IsProbabilityMeasure ρ]
    (henv : ∀ᵐ z ∂ρ,
      (∃ p : ℕ × ℕ, p.2 < (z p.1).1) ∧
      (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
      Summable (fun p : ℕ × ℕ =>
        if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) :
    let μ : Measure (ℕ → ℕ → ℝ) :=
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
    let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
      ∑' τ : Option J → ℕ × ℕ,
        if ∀ j, (τ j).2 < (zg.1 (τ j).1).1 then
          (∏ j, ((zg.1 (τ j).1).2 (τ j).2 *
              Real.exp (t * zg.2 (τ j).1 (τ j).2)) /
            ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
            (Φ (fun j => τ (some j)) *
              (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
                Fintype.card J * t *
                  (if τ (some r₀) = τ none then 1 else 0)))
        else 0
    Integrable H (ρ.prod μ) := by
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  let H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' τ : Option J → ℕ × ℕ,
      if ∀ j, (τ j).2 < (zg.1 (τ j).1).1 then
        (∏ j, ((zg.1 (τ j).1).2 (τ j).2 *
            Real.exp (t * zg.2 (τ j).1 (τ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
          (Φ (fun j => τ (some j)) *
            (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
              Fintype.card J * t *
                (if τ (some r₀) = τ none then 1 else 0)))
      else 0
  have hm : Measurable H := by
    apply measurable_tsum_guarded_replica
      (fun z : ℕ → ℕ × (ℕ → ℝ) => fun n => (z n).1)
      (fun n => (measurable_pi_apply n).fst)
      (fun (zg : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ)) p =>
        (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2))
      (fun p => (by fun_prop))
      (fun _ τ => Φ (fun j => τ (some j)) *
        (∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
          (Fintype.card J : ℝ) * t *
            (if τ (some r₀) = τ none then 1 else 0)))
      (fun _ => measurable_const)
  have hc : ∀ᵐ z ∂ρ,
      Integrable (fun g => H (z, g)) μ ∧
        ∀ᵐ g ∂μ, |H (z, g)| ≤ (Fintype.card J : ℝ) * M * |t| := by
    filter_upwards [henv] with z ⟨hn, hp, hs⟩
    exact gaussian_gibbs_tilt_correction_integrable_and_bound
      t r₀ Φ M hΦ z hn hp hs
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact hc.mono fun z hz => hz.1
  · have hb : ∀ᵐ z ∂ρ,
        ‖∫ g, ‖H (z, g)‖ ∂μ‖ ≤ (Fintype.card J : ℝ) * M * |t| := by
      filter_upwards [hc] with z ⟨hi, hz⟩
      have hnonneg : 0 ≤ ∫ g, |H (z, g)| ∂μ := integral_nonneg fun _ => abs_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by simpa only [Real.norm_eq_abs] using hnonneg)]
      calc
        ∫ g, ‖H (z, g)‖ ∂μ = ∫ g, |H (z, g)| ∂μ := by
          simp only [Real.norm_eq_abs]
        _ ≤ ∫ _ : ℕ → ℕ → ℝ, (Fintype.card J : ℝ) * M * |t| ∂μ :=
          integral_mono_ae hi.abs (integrable_const _) hz
        _ = _ := by simp
    exact (integrable_const ((Fintype.card J : ℝ) * M * |t|)).mono'
      (hm.aestronglyMeasurable.norm.integral_prod_right') hb

end SpinGlasses
