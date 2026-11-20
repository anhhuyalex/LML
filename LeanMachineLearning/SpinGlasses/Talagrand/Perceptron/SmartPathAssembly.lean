/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathIBP

/-!
# Assembling the derivative of the perceptron smart path (Proposition 2.2.3)

Talagrand, Section 2.2. `SmartPathIBP.lean` integrates by parts each of the three terms of (2.28)
at fixed disorder. This module averages over the quenched disorder `smartPathDisorder Pold v` and
combines the terms.

* `integral_coupling_mul_smartPathDisorder`: Stein in one quenched coupling `a_k`, for the disorder
  law (any finite `Pold`, any variance `v`), by Fubini and the coordinatewise Stein identity;
* `replicaDiff_smartPathEnergyDerivA`: linearity of the `E'_a` term over the constraints.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace SpinGlasses

section Joint

variable {N M : ℕ} {u : ℝ → ℝ}

theorem measurable_lastSpin_mul_deriv (t : ℝ) (k : Fin M) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      ((p.2.1.2 : ℤ) : ℝ) * deriv u (smartPathField t p.1 p.2 k) := by
  have := measurable_deriv u
  have hε : Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      ((p.2.1.2 : ℤ) : ℝ) := by fun_prop
  exact hε.mul (this.comp (measurable_smartPathField t k))

theorem measurable_diag_joint (t : ℝ) (k : Fin M) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      deriv (deriv u) (smartPathField t p.1 p.2 k) + deriv u (smartPathField t p.1 p.2 k) ^ 2 :=
  ((measurable_deriv (deriv u)).comp (measurable_smartPathField t k)).add
    (((measurable_deriv u).comp (measurable_smartPathField t k)).pow_const 2)

theorem measurable_potentialKernel_joint (t : ℝ) (k : Fin M) :
    Measurable fun p : SmartPathDisorder N M × (SmartPathState N M × SmartPathState N M) =>
      smartPathPotentialKernel u t p.1 k p.2.1 p.2.2 := by
  have hg := measurable_lastSpin_mul_deriv (N := N) (u := u) t k
  have h1 := hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd) :
    Measurable fun p : SmartPathDisorder N M × (SmartPathState N M × SmartPathState N M) =>
      (p.1, p.2.1))
  have h2 := hg.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd) :
    Measurable fun p : SmartPathDisorder N M × (SmartPathState N M × SmartPathState N M) =>
      (p.1, p.2.2))
  convert h1.mul h2 using 1
  funext p
  unfold smartPathPotentialKernel
  simp only [Pi.mul_apply, Function.comp_apply]
  ring

end Joint

/-- Linearity of the quenched-coupling term over the constraints. -/
theorem replicaDiff_smartPathEnergyDerivA {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] {t : ℝ}
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (ω : SmartPathDisorder N M)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (smartPathEnergyDerivA u t ω) =
      ∑ k : Fin M, ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (ω.1.2 k / Real.sqrt t)) *
        replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
          (fun x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k)) := by
  have hum : Measurable u := hu.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hν : IsProbabilityMeasure (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum (fun x => hu.le x) ω t
  have hfld (k : Fin M) : Measurable fun x : SmartPathState N M => smartPathField t ω x k := by
    unfold smartPathField smartPathFieldNoAux
    fun_prop
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hfun : smartPathEnergyDerivA u t ω = fun x => ∑ k : Fin M,
      ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (ω.1.2 k / Real.sqrt t)) *
        (((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k)) := by
    funext x
    unfold smartPathEnergyDerivA
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint (k : Fin M) : Integrable (fun x : SmartPathState N M =>
      ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (ω.1.2 k / Real.sqrt t)) *
        (((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k)))
      (μ.tilted (smartPathEnergy u t ω)) := by
    refine integrable_of_measurable_bound
      (((hε.mul (hdu.comp (hfld k)))).const_mul _) (M := |(1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k / Real.sqrt t)| * D) fun x => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_mul, abs_units_cast_eq_one, one_mul]
    exact hu.abs_deriv_le _
  rw [hfun, replicaDiff_finset_sum _ _ hF.aestronglyMeasurable hFb Finset.univ _
    (fun k _ => hint k)]
  exact Finset.sum_congr rfl fun k _ => replicaDiff_const_mul _ F _ _

/-- The quenched couplings and the last field are integrable under the disorder law. -/
theorem integrable_coupling_smartPathDisorder {N M : ℕ} {Pold : Measure (Fin M → Fin N → ℝ)}
    [IsFiniteMeasure Pold] (v : ℝ≥0) (k : Fin M) :
    Integrable (fun ω : SmartPathDisorder N M => ω.1.2 k) (smartPathDisorder Pold v) := by
  unfold smartPathDisorder
  have hak : Integrable (fun a : Fin M → ℝ => a k) (Measure.pi fun _ : Fin M => gaussianReal 0 1) :=
    integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k) (f := fun x : ℝ => x)
      IsGaussian.integrable_id
  exact (hak.comp_snd Pold).comp_fst _

/-- **Stein in one quenched coupling, averaged over the disorder.** For `Φ` and `Φ'` with
`ω ↦ a_k Φ(ω)` and `Φ'` integrable, where `Φ'` is the partial derivative of `Φ` in the coordinate
`a_k` (pointwise, along `update`), `𝔼[a_k Φ(ω)] = 𝔼[Φ'(ω)]` for `ω ∼ smartPathDisorder Pold v`
(any finite `Pold`, any variance `v` of the last field). The one-dimensional Stein identity is
applied on the slices of the product, which are integrable by Fubini. -/
theorem integral_coupling_mul_smartPathDisorder {N M : ℕ} {Pold : Measure (Fin M → Fin N → ℝ)}
    [IsFiniteMeasure Pold] (v : ℝ≥0) (k : Fin M) {Φ Φ' : SmartPathDisorder N M → ℝ}
    (hI1 : Integrable (fun ω : SmartPathDisorder N M => ω.1.2 k * Φ ω) (smartPathDisorder Pold v))
    (hI2 : Integrable Φ' (smartPathDisorder Pold v))
    (hder : ∀ (g : Fin M → Fin N → ℝ) (a : Fin M → ℝ) (y : ℝ),
      HasDerivAt (fun τ => Φ ((g, update a k τ), y)) (Φ' ((g, a), y)) (a k)) :
    ∫ ω, ω.1.2 k * Φ ω ∂(smartPathDisorder Pold v) = ∫ ω, Φ' ω ∂(smartPathDisorder Pold v) := by
  classical
  unfold smartPathDisorder at hI1 hI2 ⊢
  rw [integral_prod_symm _ hI1, integral_prod_symm _ hI2]
  refine integral_congr_ae ?_
  filter_upwards [hI1.prod_left_ae, hI2.prod_left_ae] with y hq1 hq2
  change ∫ q, q.2 k * Φ (q, y) ∂(Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)) =
    ∫ q, Φ' (q, y) ∂(Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1))
  rw [integral_prod _ hq1, integral_prod _ hq2]
  refine integral_congr_ae ?_
  filter_upwards [hq1.prod_right_ae, hq2.prod_right_ae] with g ha1 ha2
  have := integral_eval_mul_pi_gaussianReal_eq_of_coord (fun _ : Fin M => (1 : ℝ≥0)) k
    (G := fun a => Φ ((g, a), y)) (G' := fun a => Φ' ((g, a), y)) (fun a => hder g a y)
    ha1 ha2
  simpa using this

/-- Updating the `k`-th coupling by its own value does nothing. -/
theorem smartPathDisorderUpdate_self {N M : ℕ} (ω : SmartPathDisorder N M) (k : Fin M) :
    smartPathDisorderUpdate ω k (ω.1.2 k) = ω := by
  simp [smartPathDisorderUpdate]

/-- **The `k`-th constraint term of Proposition 2.2.3 at fixed disorder:** the replica difference
of the diagonal `u'' + u'^2` at the field `S_k`, plus twice the pair average of the potential
kernel `U_k`. -/
noncomputable def smartPathConstraintTerm {N M : ℕ} {R : Type*} [Fintype R] [LinearOrder R]
    (μ : Measure (SmartPathState N M))
    (u : ℝ → ℝ) (t : ℝ) (k : Fin M) (F : (R → SmartPathState N M) → ℝ)
    (ω : SmartPathDisorder N M) : ℝ :=
  replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
      (fun x => deriv (deriv u) (smartPathField t ω x k) + deriv u (smartPathField t ω x k) ^ 2) +
    2 * replicaPairAverage (μ.tilted (smartPathEnergy u t ω)) F
      (smartPathPotentialKernel u t ω k)

/-- `ω ↦ a_k · replicaDiff (ε u'(S_k))` is integrable under the disorder law. -/
theorem integrable_coupling_mul_replicaDiff {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] {t : ℝ}
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold] (k : Fin M)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    Integrable (fun ω : SmartPathDisorder N M => ω.1.2 k * replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F
      (fun x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k)))
      (smartPathDisorder Pold v) := by
  have hum : Measurable u := hu.measurable
  have hprob (ω : SmartPathDisorder N M) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum (fun x => hu.le x) ω t
  have hE : Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergy u t p.1 p.2 := measurable_smartPathEnergy hum t
  have hhb (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
      |((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k)| ≤ D := by
    rw [abs_mul, abs_units_cast_eq_one, one_mul]
    exact hu.abs_deriv_le _
  have hGm : Measurable fun ω => replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F
      (fun x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k)) :=
    measurable_replicaDiff_tilted (E := fun ω x => smartPathEnergy u t ω x) hE
      (h := fun ω x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k))
      (measurable_lastSpin_mul_deriv t k) hF
  have hGb (ω : SmartPathDisorder N M) : |replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F
      (fun x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k))| ≤
      C * ((Fintype.card R : ℝ) * D + (Fintype.card R : ℝ) * D) := by
    have := hprob ω
    exact abs_replicaDiff_le _ F hF hFb
      (fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k))
      (Measurable.of_uncurry_left (f := fun ω x => ((x.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t ω x k)) (measurable_lastSpin_mul_deriv t k)) (hhb ω)
  have := (integrable_coupling_smartPathDisorder (Pold := Pold) v k).bdd_mul_of_abs_le
    hGm.aestronglyMeasurable (ae_of_all _ hGb)
  simpa only [mul_comm] using this

/-- The replica difference of the diagonal `u'' + u'^2` is integrable in the disorder. -/
theorem integrable_replicaDiff_diag {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] {t : ℝ} {u : ℝ → ℝ}
    {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (F : (R → SmartPathState N M) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) (k : Fin M)
    (P : Measure (SmartPathDisorder N M)) [IsFiniteMeasure P] :
    Integrable (fun ω => replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
      (fun x => deriv (deriv u) (smartPathField t ω x k) +
        deriv u (smartPathField t ω x k) ^ 2)) P := by
  have hum : Measurable u := hu.toSmartPathPotential.measurable
  have hprob (ω : SmartPathDisorder N M) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum
      (fun x => hu.toSmartPathPotential.le x) ω t
  have hE : Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergy u t p.1 p.2 := measurable_smartPathEnergy hum t
  have hm : Measurable fun ω => replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F
      (fun x => deriv (deriv u) (smartPathField t ω x k) +
        deriv u (smartPathField t ω x k) ^ 2) :=
    measurable_replicaDiff_tilted (E := fun ω x => smartPathEnergy u t ω x) hE
      (h := fun ω x => deriv (deriv u) (smartPathField t ω x k) +
        deriv u (smartPathField t ω x k) ^ 2) (measurable_diag_joint t k) hF
  have hb (ω : SmartPathDisorder N M) : |replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F
      (fun x => deriv (deriv u) (smartPathField t ω x k) +
        deriv u (smartPathField t ω x k) ^ 2)| ≤ C * ((Fintype.card R : ℝ) * (D₂ + D ^ 2) +
        (Fintype.card R : ℝ) * (D₂ + D ^ 2)) := by
    have := hprob ω
    exact abs_replicaDiff_le _ F hF hFb
      (fun x : SmartPathState N M => deriv (deriv u) (smartPathField t ω x k) +
        deriv u (smartPathField t ω x k) ^ 2)
      (Measurable.of_uncurry_left (f := fun ω x => deriv (deriv u) (smartPathField t ω x k) +
        deriv u (smartPathField t ω x k) ^ 2) (measurable_diag_joint t k))
      (fun x => abs_deriv₂_add_sq_le hu t ω k x)
  exact integrable_of_measurable_bound hm hb

/-- The pair average of the potential kernel is integrable in the disorder. -/
theorem integrable_replicaPairAverage_kernel {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] [LinearOrder R]
    {t : ℝ} {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    (k : Fin M) (P : Measure (SmartPathDisorder N M)) [IsFiniteMeasure P] :
    Integrable (fun ω => replicaPairAverage (μ.tilted
      (smartPathEnergy u t ω)) F (smartPathPotentialKernel u t ω k)) P := by
  have hum : Measurable u := hu.measurable
  have hprob (ω : SmartPathDisorder N M) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum
      (fun x => hu.le x) ω t
  have hE : Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergy u t p.1 p.2 := measurable_smartPathEnergy hum t
  exact integrable_replicaPairAverage_tilted_of_bound (E := fun ω x => smartPathEnergy u t ω x)
    hE hprob (U := fun ω a b => smartPathPotentialKernel u t ω k a b)
    (measurable_potentialKernel_joint t k)
    (fun ω a b => abs_smartPathPotentialKernel_le hu t ω k a b) hF hFb

/-- **Stein in `a_k`, averaged over the disorder.** -/
theorem integral_coupling_mul_replicaDiff {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] [LinearOrder R]
    {t : ℝ} {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold] (k : Fin M)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ ω, ω.1.2 k * replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (fun x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k))
        ∂(smartPathDisorder Pold v) =
      Real.sqrt (t / (N + 1)) *
        ∫ ω, smartPathConstraintTerm μ u t k F ω ∂(smartPathDisorder Pold v) := by
  rw [← integral_const_mul]
  refine integral_coupling_mul_smartPathDisorder v k
    (integrable_coupling_mul_replicaDiff hu.toSmartPathPotential v k F hF hFb)
    (((integrable_replicaDiff_diag hu F hF hFb k _).add
      ((integrable_replicaPairAverage_kernel hu.toSmartPathPotential F hF hFb k _).const_mul
        2)).const_mul _)
    fun g a y => ?_
  have h := hasDerivAt_replicaDiff_update (μ := μ) (t := t) hu ((g, a), y) k F hF hFb (a k)
  rw [smartPathDisorderUpdate_self] at h
  exact h.congr_deriv (by simp only [smartPathConstraintTerm]; ring)

/-- The last-field term is `-y / (2 √(1 - t))` times the replica difference of the last spin. -/
theorem replicaDiff_smartPathEnergyDerivY_eq {N M : ℕ}
    {μ : Measure (SmartPathState N M)} {R : Type*} [Fintype R] (u : ℝ → ℝ)
    (t : ℝ)
    (ω : SmartPathDisorder N M) (F : (R → SmartPathState N M) → ℝ) :
    replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (smartPathEnergyDerivY t ω) =
      (-(1 / (2 * Real.sqrt (1 - t))) * ω.2) * replicaDiff
        (μ.tilted (smartPathEnergy u t ω)) F
        (fun x => ((x.1.2 : ℤ) : ℝ)) := by
  have hfun : smartPathEnergyDerivY t ω =
      fun x => (-(1 / (2 * Real.sqrt (1 - t))) * ω.2) * ((x.1.2 : ℤ) : ℝ) := by
    funext x
    unfold smartPathEnergyDerivY
    ring
  rw [hfun]
  exact replicaDiff_const_mul _ F _ _

theorem integrable_lastField_smartPathDisorder {N M : ℕ} {Pold : Measure (Fin M → Fin N → ℝ)}
    [IsFiniteMeasure Pold] (v : ℝ≥0) :
    Integrable (fun ω : SmartPathDisorder N M => ω.2) (smartPathDisorder Pold v) := by
  unfold smartPathDisorder
  exact IsGaussian.integrable_id.comp_snd _

/-- The last-field term is integrable under the disorder law. -/
theorem integrable_replicaDiff_smartPathEnergyDerivY {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] {t : ℝ}
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    Integrable (fun ω => replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
      (smartPathEnergyDerivY t ω)) (smartPathDisorder Pold v) := by
  have hum : Measurable u := hu.measurable
  have hprob (ω : SmartPathDisorder N M) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum (fun x => hu.le x) ω t
  have hE : Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergy u t p.1 p.2 := measurable_smartPathEnergy hum t
  have hεj : Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      ((p.2.1.2 : ℤ) : ℝ) := by fun_prop
  have hεb (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
      |((x.1.2 : ℤ) : ℝ)| ≤ 1 := (abs_units_cast_eq_one _).le
  have hGm : Measurable fun ω => replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F (fun x => ((x.1.2 : ℤ) : ℝ)) :=
    measurable_replicaDiff_tilted (E := fun ω x => smartPathEnergy u t ω x) hE
      (h := fun _ x => ((x.1.2 : ℤ) : ℝ)) hεj hF
  have hGb (ω : SmartPathDisorder N M) : |replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F (fun x => ((x.1.2 : ℤ) : ℝ))| ≤
      C * ((Fintype.card R : ℝ) * 1 + (Fintype.card R : ℝ) * 1) := by
    have := hprob ω
    exact abs_replicaDiff_le _ F hF hFb _ (by fun_prop) (hεb ω)
  have hy := integrable_lastField_smartPathDisorder (Pold := Pold) (N := N) v
  simp_rw [replicaDiff_smartPathEnergyDerivY_eq u t]
  have := (hy.const_mul (-(1 / (2 * Real.sqrt (1 - t))))).bdd_mul_of_abs_le
    hGm.aestronglyMeasurable (ae_of_all _ hGb)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using this

/-- **The `E'_a` term, averaged over the disorder.** The quenched couplings are integrated by
parts one constraint at a time (any finite `Pold`, any `v`): the result is
`1/(2(N+1)) ∑_k 𝔼 [diag_k + 2 pair_k]`. -/
theorem integral_replicaDiff_smartPathEnergyDerivA_disorder {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ] {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} {B D D₂ : ℝ}
    (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ ω, replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (smartPathEnergyDerivA u t ω) ∂(smartPathDisorder Pold v) =
      1 / (2 * ((N : ℝ) + 1)) * ∑ k : Fin M,
        ∫ ω, smartPathConstraintTerm μ u t k F ω ∂(smartPathDisorder Pold v) := by
  have hI (k : Fin M) := integrable_coupling_mul_replicaDiff (μ := μ) (t := t)
    hu.toSmartPathPotential v (Pold := Pold) k F hF hFb
  have hpt (ω : SmartPathDisorder N M) : replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F (smartPathEnergyDerivA u t ω) =
      ∑ k : Fin M, ((1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt t) *
        (ω.1.2 k * replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
          (fun x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k))) := by
    rw [replicaDiff_smartPathEnergyDerivA hu.toSmartPathPotential ω F hF hFb]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => (hI k).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_coupling_mul_replicaDiff hu v k F hF hFb, ← mul_assoc]
  have := smartPath_sqrt_scaling_prefactor_eq (N := N) ht.1
  congr 1
  rw [div_eq_mul_one_div _ (Real.sqrt t), mul_assoc]
  push_cast at this ⊢
  linarith [this]

/-- **The `E'_Y` term, averaged over the disorder.** For any finite law `Pold` of the old rows,
any variance `v ≥ 0` of the last field: `𝔼 diff(E'_Y) = -v 𝔼 ⟨F pd(ε_σ ε_τ)⟩`. -/
theorem integral_replicaDiff_smartPathEnergyDerivY_disorder {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ] {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} {B D : ℝ}
    (hu : SmartPathPotential u B D) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ ω, replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (smartPathEnergyDerivY t ω) ∂(smartPathDisorder Pold v) =
      -(v : ℝ) * ∫ ω, replicaPairAverage
        (μ.tilted (smartPathEnergy u t ω)) F lastSpinKernel
        ∂(smartPathDisorder Pold v) := by
  classical
  have hum : Measurable u := hu.measurable
  have hprob (ω : SmartPathDisorder N M) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum (fun x => hu.le x) ω t
  have hE : Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergy u t p.1 p.2 := measurable_smartPathEnergy hum t
  have hKb : ∀ a b : SmartPathState N M, |lastSpinKernel a b| ≤ 1 := fun a b => by
    unfold lastSpinKernel
    rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
  have hLi := integrable_replicaDiff_smartPathEnergyDerivY (μ := μ) (t := t) hu v (Pold := Pold)
    F hF hFb
  have hRi : Integrable (fun ω => replicaPairAverage
      (μ.tilted (smartPathEnergy u t ω)) F lastSpinKernel)
      (smartPathDisorder Pold v) :=
    integrable_replicaPairAverage_tilted_of_bound (E := fun ω x => smartPathEnergy u t ω x)
      hE hprob (U := fun _ a b => lastSpinKernel a b) (by unfold lastSpinKernel; fun_prop)
      (fun _ a b => hKb a b) hF hFb
  unfold smartPathDisorder at hLi hRi ⊢
  rw [integral_prod _ hLi, integral_prod _ hRi, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun q =>
    integral_replicaDiff_smartPathEnergyDerivY ht hum (fun x => hu.le x) v q F hF hFb)


/-- The quenched-coupling term is integrable under the disorder law. -/
theorem integrable_replicaDiff_smartPathEnergyDerivA {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] {t : ℝ}
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    Integrable (fun ω => replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
      (smartPathEnergyDerivA u t ω)) (smartPathDisorder Pold v) := by
  have hpt (ω : SmartPathDisorder N M) : replicaDiff
      (μ.tilted (smartPathEnergy u t ω)) F (smartPathEnergyDerivA u t ω) =
      ∑ k : Fin M, ((1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt t) *
        (ω.1.2 k * replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
          (fun x => ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k))) := by
    rw [replicaDiff_smartPathEnergyDerivA hu ω F hF hFb]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hpt]
  exact integrable_finsetSum _ fun k _ =>
    (integrable_coupling_mul_replicaDiff hu v k F hF hFb).const_mul _

/-- **The `E'_ξ` term, averaged over the disorder** (spin-only observable): minus
`1/(2(N+1))` times the sum over constraints of the expected replica difference of the diagonal. -/
theorem integral_replicaDiff_smartPathEnergyDerivXi_disorder {N M : ℕ} {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} {B D D₂ : ℝ}
    (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → PerceptronSpin N) → ℝ) :
    ∫ ω, replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) (smartPathEnergyDerivXi u t ω)
        ∂(smartPathDisorder Pold v) =
      -(1 / (2 * ((N : ℝ) + 1))) * ∑ k : Fin M, ∫ ω, replicaDiff
        ((smartPathBase N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (fun x => deriv (deriv u) (smartPathField t ω x k) +
          deriv u (smartPathField t ω x k) ^ 2) ∂(smartPathDisorder Pold v) := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  have hFm := measurable_spin_only (N := N) (M := M) f
  have hFb : ∀ σ : R → SmartPathState N M, |f (fun r => (σ r).1)| ≤ C := fun σ => hC _
  simp_rw [replicaDiff_smartPathEnergyDerivXi ht hu _ f]
  rw [integral_const_mul, integral_finsetSum _ fun k _ =>
    integrable_replicaDiff_diag hu _ hFm hFb k _]

/-- The constraint term is the integrable sum of its diagonal and pair parts. -/
theorem integral_smartPathConstraintTerm {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] [LinearOrder R]
    {t : ℝ} {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    (k : Fin M) (P : Measure (SmartPathDisorder N M)) [IsFiniteMeasure P] :
    ∫ ω, smartPathConstraintTerm μ u t k F ω ∂P =
      (∫ ω, replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (fun x => deriv (deriv u) (smartPathField t ω x k) +
          deriv u (smartPathField t ω x k) ^ 2) ∂P) +
      2 * ∫ ω, replicaPairAverage (μ.tilted (smartPathEnergy u t ω)) F
        (smartPathPotentialKernel u t ω k) ∂P := by
  unfold smartPathConstraintTerm
  rw [integral_add (integrable_replicaDiff_diag hu F hF hFb k P)
    ((integrable_replicaPairAverage_kernel hu.toSmartPathPotential F hF hFb k P).const_mul 2),
    integral_const_mul]

/-- **Proposition 2.2.3 (T17.5), sum over the constraints.** For `0 < t < 1`, a potential with
`|u| ≤ B`, `|u'| ≤ D`, `|u''| ≤ D₂`, any finite law `Pold` of the old couplings, any variance
`v ≥ 0` of the last field and any spin-only observable `f` of `n` replicas, the derivative of the
quenched replica average along the smart path is
`(1/(N+1)) ∑_{k<M} 𝔼⟨f pd(U_k)⟩_t − v 𝔼⟨f pd(ε_σ ε_τ)⟩_t`, `pd` the two-replica combination
`replicaPairCombination` and `U_k = ε ε' u'(S_k) u'(S_k)'` the potential kernel. No symmetry of the
rows is assumed (see the exchangeable corollary for the printed last-constraint form). -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_ibp {N M : ℕ} {R : Type*}
    [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ}
    {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (1 / ((N : ℝ) + 1) * ∑ k : Fin M, ∫ ω, replicaPairAverage
          ((smartPathBase N M).tilted (smartPathEnergy u t ω))
          (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
          (smartPathPotentialKernel u t ω k) ∂(smartPathDisorder Pold v) -
        (v : ℝ) * ∫ ω, replicaPairAverage ((smartPathBase N M).tilted (smartPathEnergy u t ω))
          (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) lastSpinKernel
          ∂(smartPathDisorder Pold v)) t := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  have hFm := measurable_spin_only (N := N) (M := M) f
  have hFb : ∀ σ : R → SmartPathState N M, |f (fun r => (σ r).1)| ≤ C := fun σ => hC _
  refine (hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms_spin_only ht
    hu.differentiable hu.abs_le hu.abs_deriv_le v f).congr_deriv ?_
  have hA := integrable_replicaDiff_smartPathEnergyDerivA (μ := smartPathBase N M) (t := t)
    hu.toSmartPathPotential v (Pold := Pold) _ hFm hFb
  have hY := integrable_replicaDiff_smartPathEnergyDerivY (μ := smartPathBase N M) (t := t)
    hu.toSmartPathPotential v
    (Pold := Pold) _ hFm hFb
  have hξ : Integrable (fun ω => replicaDiff
      ((smartPathBase N M).tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) (smartPathEnergyDerivXi u t ω))
      (smartPathDisorder Pold v) := by
    simp_rw [replicaDiff_smartPathEnergyDerivXi ht hu _ f]
    exact (integrable_finsetSum _ fun k _ =>
      integrable_replicaDiff_diag hu _ hFm hFb k _).const_mul _
  have hAξ : Integrable (fun ω => replicaDiff
      ((smartPathBase N M).tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) (smartPathEnergyDerivA u t ω) +
      replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) (smartPathEnergyDerivXi u t ω))
      (smartPathDisorder Pold v) := hA.add hξ
  rw [integral_add hAξ hY, integral_add hA hξ,
    integral_replicaDiff_smartPathEnergyDerivA_disorder ht hu v _ hFm hFb,
    integral_replicaDiff_smartPathEnergyDerivXi_disorder ht hu v f,
    integral_replicaDiff_smartPathEnergyDerivY_disorder ht hu.toSmartPathPotential v _ hFm hFb]
  simp only [integral_smartPathConstraintTerm hu _ hFm hFb, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

end SpinGlasses
