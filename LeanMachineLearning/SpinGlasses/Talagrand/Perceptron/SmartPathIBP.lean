/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDisorderDerivative
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPPotential
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaPairBridge
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaDiffDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityBounds

/-!
# Gaussian integration by parts on the smart path

Talagrand Section 2.2, Proposition 2.2.3. This module contains the algebra and the integration by
parts of the pieces of the derivative (2.28). Proved: the last-field term `E'_Y`
(`integral_replicaDiff_smartPathEnergyDerivY`, Stein in `y ∼ 𝒩(0, v)`, giving `-v` times the
pair average of the last-spin kernel). Not proved yet: the auxiliary-spin term `E'_ξ`, the
quenched-coupling term `E'_a`, and their assembly over the constraints.

* `smartPath_sqrt_scaling_prefactor_eq`, `smartPath_auxiliary_prefactor_eq_neg`: the prefactors
  that cancel the `√s` and `√(1 - s)` denominators of the energy derivative (2.27);
* `replicaPairCombination_lastSpinKernel`: the two-replica combination of the last-spin kernel
  (2.25) as half of the four-term covariance combination of the cavity method;
* `hasDerivAt_replicaDiff_lastSpin_lastField`, `integral_replicaDiff_smartPathEnergyDerivY`: the
  derivative in the last field of the last-spin replica difference and its Gaussian integration
  by parts, from the model-free `replicaDiffWith_replicaDiff_eq_two_mul_replicaPairAverage`
  (`ForMathlib/Probability/GibbsReplicaPairBridge.lean`).

The objects of the path (`smartPathEnergy`, `smartPathBase`, ...) are in `SmartPathModel.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped BigOperators NNReal

namespace SpinGlasses

/-- Square-root scaling prefactor of the Gaussian integration by parts on the smart path:
`(1 / (2 * √(N + 1))) * (1 / √s) * √(s / (N + 1)) = 1 / (2 * (N + 1))` for `s > 0`. With `s = t`
this is the quenched-disorder prefactor, with `s = 1 - t` the auxiliary-spin one. -/
theorem smartPath_sqrt_scaling_prefactor_eq {N : ℕ} {s : ℝ} (hs : 0 < s) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (1 / Real.sqrt s) *
      Real.sqrt (s / (N + 1 : ℕ)) =
    1 / (2 * (N + 1 : ℝ)) := by
  push_cast
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [Real.sqrt_div hs.le]
  have h1 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h2 : Real.sqrt ((N : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have h3 := Real.mul_self_sqrt hN.le
  field_simp
  nlinarith [h3]

/-- Simplification of the auxiliary spin prefactor: the product
`(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1))` simplifies to
`- 1 / (2 * (N + 1))`, cancelling the `√(1 - t)` denominator. -/
theorem smartPath_auxiliary_prefactor_eq_neg {N : ℕ} {t : ℝ} (ht : t < 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  have := smartPath_sqrt_scaling_prefactor_eq (N := N) (sub_pos.2 ht)
  linear_combination -this

/-- For the last-spin interaction kernel `lastSpinKernel x y = ε_x ε_y` the diagonal is `1`
(`σ_{N+1}² = 1`) and the kernel is symmetric, so `replicaPairCombination` is half of the four-term
replica covariance combination, with no hypothesis on the replicas. Note: `[LinearOrder R]` is
only used to order the pairs `r < r'` without double counting. -/
theorem replicaPairCombination_lastSpinKernel {N M : ℕ} {R : Type*} [Fintype R] [LinearOrder R]
    (τ : Option (Option R) → SmartPathState N M) :
    replicaPairCombination (lastSpinKernel (N := N) (M := M)) τ =
      ((∑ r : R, ∑ r' : R, lastSpinKernel (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, lastSpinKernel (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * lastSpinKernel (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            lastSpinKernel (τ (some none)) (τ none)) / 2 :=
  replicaPairCombination_eq_half_replica_covariance_combination _ 1 lastSpinKernel_self
    lastSpinKernel_comm τ


/-- Derivative of the replica difference of the last spin in the last field `y`, in terms of
the two-fresh-replica average (the `E'_Y` Stein step of Proposition 2.2.3 for fixed `y`). -/
theorem hasDerivAt_replicaDiff_lastSpin_lastField {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ] {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (ω₀ : (Fin M → Fin N → ℝ) × (Fin M → ℝ))
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    (y : ℝ) :
    HasDerivAt (fun r => replicaDiff (μ.tilted (smartPathEnergy u t (ω₀, r)))
        F (fun x => ((x.1.2 : ℤ) : ℝ)))
      (2 * Real.sqrt (1 - t) * replicaPairAverage
        (μ.tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel) y := by
  set q := Real.sqrt (1 - t) with hq
  have hν (r : ℝ) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t (ω₀, r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hB (ω₀, r) t
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hεb (x : SmartPathState N M) : |((x.1.2 : ℤ) : ℝ)| ≤ 1 := (abs_units_cast_eq_one _).le
  have hE' : ∀ x : SmartPathState N M, |q * ((x.1.2 : ℤ) : ℝ)| ≤ q := fun x => by
    rw [abs_mul, abs_units_cast_eq_one, mul_one, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hbd := hasDerivAt_replicaDiff_tilted_replicaDiff
    (μ := μ) (E := fun r => smartPathEnergy u t (ω₀, r))
    (E' := fun _ x => q * ((x.1.2 : ℤ) : ℝ)) (t := y) (s := Metric.ball y 1)
    (Metric.ball_mem_nhds y one_pos)
    (fun r _ => measurable_smartPathEnergy_slice hu t (ω₀, r))
    (by fun_prop) (B := M * B + q * (|y| + 1)) (fun r hr x => by
      refine (perceptron_smart_path_energy_le hB t (ω₀, r) x).trans ?_
      have : |r| ≤ |y| + 1 := by
        have := abs_sub_abs_le_abs_sub r y
        have h2 := Metric.mem_ball.1 hr
        rw [Real.dist_eq] at h2
        linarith
      have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg (1 - t))
      linarith)
    (b := fun _ => q) (integrable_const _) (fun r _ x => hE' x)
    (fun x r _ => hasDerivAt_smartPathEnergy_lastField u t ω₀ x r) hF hFb hε hεb
    (integrable_of_measurable_bound (by fun_prop) (M := q) hE')
  have := hν y
  have hbr := replicaDiffWith_replicaDiff_eq_two_mul_replicaPairAverage
    (μ.tilted (smartPathEnergy u t (ω₀, y))) F hF hFb
    (fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ)) hε hεb 1 q
    (fun x => by rw [← sq]; exact units_cast_sq _)
  exact hbr ▸ hbd

/-- **The `E'_Y` term of Proposition 2.2.3 (Stein in the last field).** For the last field
`y ∼ 𝒩(0, v)` (`v = 0` allowed), the `y`-average of the replica difference of the energy
derivative `E'_Y` is `-v` times the `y`-average of the two-fresh-replica average of the last-spin
kernel `ε_x ε_y`, the other disorder `ω₀ = (g, a)` being fixed. -/
theorem integral_replicaDiff_smartPathEnergyDerivY {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ] {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} (ht : t < 1) {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (v : ℝ≥0) (ω₀ : (Fin M → Fin N → ℝ) × (Fin M → ℝ))
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ y, replicaDiff (μ.tilted (smartPathEnergy u t (ω₀, y))) F
        (smartPathEnergyDerivY t (ω₀, y)) ∂(gaussianReal 0 v) =
      -(v : ℝ) * ∫ y, replicaPairAverage
        (μ.tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel
        ∂(gaussianReal 0 v) := by
  set q := Real.sqrt (1 - t) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 (sub_pos.2 ht)
  have hν (r : ℝ) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t (ω₀, r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hB (ω₀, r) t
  set Gf : ℝ → ℝ := fun y => replicaDiff
    (μ.tilted (smartPathEnergy u t (ω₀, y))) F
    (fun x => ((x.1.2 : ℤ) : ℝ)) with hGf
  set PA : ℝ → ℝ := fun y => replicaPairAverage
    (μ.tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel with hPA
  have hderiv (y : ℝ) : HasDerivAt Gf (2 * q * PA y) y :=
    hasDerivAt_replicaDiff_lastSpin_lastField hu hB ω₀ F hF hFb y
  have hGc : Continuous Gf := continuous_iff_continuousAt.2 fun y => (hderiv y).continuousAt
  have hPAm : Measurable fun y => 2 * q * PA y := by
    have : (fun y => 2 * q * PA y) = deriv Gf := funext fun y => (hderiv y).deriv.symm
    rw [this]
    exact measurable_deriv Gf
  -- uniform bounds
  have hεm : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hGb (y : ℝ) : |Gf y| ≤ C * ((Fintype.card R : ℝ) * 1 + (Fintype.card R : ℝ) * 1) := by
    have := hν y
    exact abs_replicaDiff_le _ F hF hFb _ hεm fun x => (abs_units_cast_eq_one _).le
  obtain ⟨K₀, hK₀⟩ := exists_abs_replicaPairCombination_le (R := R)
    (U := lastSpinKernel (N := N) (M := M)) ⟨1, abs_lastSpinKernel_le⟩
  have hPAb : ∃ K, ∀ y, |2 * q * PA y| ≤ K := by
    refine ⟨2 * q * (C * K₀), fun y => ?_⟩
    have := hν y
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_replicaPairAverage_le _ F hFb hK₀) (by positivity)
  obtain ⟨K, hK⟩ := hPAb
  have hxF : Integrable (fun y => y * Gf y) (gaussianReal 0 v) := by
    have := (IsGaussian.integrable_id (μ := gaussianReal 0 v)).bdd_mul_of_abs_le
      (F := Gf) hGc.aestronglyMeasurable (ae_of_all _ hGb)
    simpa only [mul_comm, id] using this
  have hF' : Integrable (fun y => 2 * q * PA y) (gaussianReal 0 v) :=
    integrable_of_measurable_bound hPAm hK
  have hStein := integral_id_mul_gaussianReal_eq v hderiv hxF hF'
  have hpt (y : ℝ) : replicaDiff (μ.tilted (smartPathEnergy u t (ω₀, y))) F
      (smartPathEnergyDerivY t (ω₀, y)) = (-(1 / (2 * q)) * y) * Gf y := by
    have hfun : smartPathEnergyDerivY t (ω₀, y) =
        fun x => (-(1 / (2 * q)) * y) * ((x.1.2 : ℤ) : ℝ) := by
      funext x
      simp only [smartPathEnergyDerivY, hq]
      ring
    rw [hfun]
    exact replicaDiff_const_mul _ F _ _
  simp_rw [hpt]
  have hmul : ∫ y, (-(1 / (2 * q)) * y) * Gf y ∂(gaussianReal 0 v) =
      -(1 / (2 * q)) * ∫ y, y * Gf y ∂(gaussianReal 0 v) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [hmul, hStein, integral_const_mul]
  field_simp

/-- **The `E'_a` term of Proposition 2.2.3, derivative in one coupling.** The replica difference
of `ε u'(S_k)` has derivative, in the `k`-th quenched coupling `a_k`, equal to
`√(t/(N+1)) (replicaDiff (u'' + u'^2)(S_k) + 2 · replicaPairAverage of the potential kernel)`: the
moving observable contributes `u''`, the moving measure contributes the diagonal `u'^2` and the
pair term. Only `u ≤ B`, `|u'| ≤ D`, `|u''| ≤ D₂` are used. -/
theorem hasDerivAt_replicaDiff_update {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] [LinearOrder R]
    {t : ℝ} {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ω : SmartPathDisorder N M) (k : Fin M)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    (z : ℝ) :
    HasDerivAt (fun r => replicaDiff
        (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (fun x => ((x.1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)))
      (Real.sqrt (t / (N + 1)) *
        replicaDiff (μ.tilted
          (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k) +
            deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2) +
        2 * Real.sqrt (t / (N + 1)) * replicaPairAverage
          (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k z) k)) z := by
  have hum : Measurable u := hu.toSmartPathPotential.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hddu : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  have hκ0 : 0 ≤ Real.sqrt (t / (N + 1)) := Real.sqrt_nonneg _
  have hν (r : ℝ) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum
      (fun x => hu.toSmartPathPotential.le x) _ t
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hfm (r : ℝ) : Measurable fun x : SmartPathState N M =>
      smartPathField t (smartPathDisorderUpdate ω k r) x k :=
    measurable_smartPathField_slice t _ k
  have hXm (r : ℝ) : Measurable fun x : SmartPathState N M =>
      ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) :=
    hε.mul (hdu.comp (hfm r))
  have hXb (r : ℝ) (x : SmartPathState N M) :
      |((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)| ≤ D := by
    rw [abs_mul, abs_units_cast_eq_one, one_mul]
    exact hu.abs_deriv_le _
  have hX'b (r : ℝ) (x : SmartPathState N M) :
      |Real.sqrt (t / (N + 1)) *
        deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k)| ≤
        Real.sqrt (t / (N + 1)) * D₂ := by
    rw [abs_mul, abs_of_nonneg hκ0]
    exact mul_le_mul_of_nonneg_left (hu.abs_deriv₂_le _) hκ0
  have hE'b (r : ℝ) (x : SmartPathState N M) :
      |Real.sqrt (t / (N + 1)) *
        (((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k))| ≤
        Real.sqrt (t / (N + 1)) * D := by
    rw [abs_mul, abs_of_nonneg hκ0]
    exact mul_le_mul_of_nonneg_left (hXb r x) hκ0
  have hmov := hasDerivAt_replicaDiff_tilted_moving_replicaDiff
    (μ := μ) (R := R)
    (E := fun r => smartPathEnergy u t (smartPathDisorderUpdate ω k r))
    (E' := fun r x => Real.sqrt (t / (N + 1)) *
      (((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)))
    (t := z) (s := Set.univ) Filter.univ_mem
    (fun r _ => measurable_smartPathEnergy_slice hum t _)
    ((hXm z).const_mul _)
    (B := M * B + Real.sqrt (1 - t) * |ω.2|)
    (fun r _ x => perceptron_smart_path_energy_le (fun x => hu.toSmartPathPotential.le x) t _ x)
    (b := fun _ => Real.sqrt (t / (N + 1)) * D) (integrable_const _)
    (fun r _ x => hE'b r x)
    (fun x r _ => hasDerivAt_smartPathEnergy_update hu.differentiable t ω k x r)
    hF hFb
    (h := fun r x => ((x.1.2 : ℤ) : ℝ) *
      deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k))
    (h' := fun r x => Real.sqrt (t / (N + 1)) *
      deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k))
    (fun r _ => hXm r) ((hddu.comp (hfm z)).const_mul _)
    (H := D) (H' := Real.sqrt (t / (N + 1)) * D₂) (fun r _ x => hXb r x) (fun r _ x => hX'b r x)
    (fun x r _ => hasDerivAt_lastSpin_mul_deriv_update hu.differentiable_deriv t ω k x r)
    (integrable_of_measurable_bound ((hXm z).const_mul _) (hE'b z))
  have := hν z
  have hbr := replicaDiffWith_replicaDiff_eq
    (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F hF hFb
    (fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) *
      deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k)) (hXm z) (hXb z)
    (Real.sqrt (t / (N + 1)))
  have h2 : ∀ x : SmartPathState N M, ((x.1.2 : ℤ) : ℝ) * ((x.1.2 : ℤ) : ℝ) = 1 := fun x => by
    rw [← sq]; exact units_cast_sq _
  have hsq : (fun x : SmartPathState N M => (((x.1.2 : ℤ) : ℝ) *
      deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k)) *
      (((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k))) =
      fun x => deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2 := by
    funext x
    linear_combination (deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2) *
      h2 x
  have hker : (fun a b : SmartPathState N M => (((a.1.2 : ℤ) : ℝ) *
      deriv u (smartPathField t (smartPathDisorderUpdate ω k z) a k)) *
      (((b.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k z) b k))) =
      smartPathPotentialKernel u t (smartPathDisorderUpdate ω k z) k := by
    funext a b
    exact (smartPathPotentialKernel_eq_mul _ _ _ _ a b).symm
  rw [hsq, hker] at hbr
  refine hmov.congr_deriv ?_
  rw [hbr, replicaDiff_const_mul]
  have hI1 : Integrable (fun x : SmartPathState N M =>
      deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k))
      (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) :=
    integrable_of_measurable_bound (hddu.comp (hfm z)) (M := D₂) fun x => hu.abs_deriv₂_le _
  have hI2 : Integrable (fun x : SmartPathState N M =>
      deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2)
      (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) :=
    integrable_of_measurable_bound ((hdu.comp (hfm z)).pow_const 2) (M := D ^ 2) fun x => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hu.abs_deriv_le _) 2
  rw [show (fun x : SmartPathState N M =>
      deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2) =
      fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2 from rfl,
    replicaDiff_add _ F hF.aestronglyMeasurable hFb hI1 hI2]
  ring

/-- The diagonal observable `u''(S_k) + u'(S_k)^2` is bounded by `D₂ + D²`. -/
theorem abs_deriv₂_add_sq_le {N M : ℕ} {u : ℝ → ℝ} {B D D₂ : ℝ}
    (hu : SmartPathPotential₂ u B D D₂) (t : ℝ) (ω : SmartPathDisorder N M) (k : Fin M)
    (x : SmartPathState N M) :
    |deriv (deriv u) (smartPathField t ω x k) + deriv u (smartPathField t ω x k) ^ 2| ≤
      D₂ + D ^ 2 := by
  refine (abs_add_le _ _).trans (add_le_add (hu.abs_deriv₂_le _) ?_)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hu.abs_deriv_le _) 2

/-- The potential kernel `ε ε' u'(S_k) u'(S_k)'` is bounded by `D²`. -/
theorem abs_smartPathPotentialKernel_le {N M : ℕ} {u : ℝ → ℝ} {B D : ℝ}
    (hu : SmartPathPotential u B D) (t : ℝ) (ω : SmartPathDisorder N M) (k : Fin M)
    (a b : SmartPathState N M) : |smartPathPotentialKernel u t ω k a b| ≤ D * D := by
  rw [smartPathPotentialKernel_eq_mul, abs_mul]
  have h (x : SmartPathState N M) :
      |((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k)| ≤ D := by
    rw [abs_mul, abs_units_cast_eq_one, one_mul]
    exact hu.abs_deriv_le _
  exact mul_le_mul (h a) (h b) (abs_nonneg _) ((abs_nonneg _).trans (h a))

/-- **Stein in one quenched coupling `a_k ∼ 𝒩(0, 1)`** (the other disorder fixed). With
`h = ε u'(S_k)`, `∫ z, z · replicaDiff ν_z F h_z` equals
`√(t/(N+1)) ∫ z, [replicaDiff ν_z F (u'' + u'^2)(S_k) + 2 replicaPairAverage ν_z F U_k]`: the
diagonal `u'^2` and the pair term of the potential kernel `U_k`. -/
theorem integral_mul_replicaDiff_update {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] [LinearOrder R]
    {t : ℝ} {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ω : SmartPathDisorder N M) (k : Fin M)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ z, z * replicaDiff
        (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
        (fun x => ((x.1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k)) ∂(gaussianReal 0 1) =
      Real.sqrt (t / (N + 1)) * ∫ z,
        (replicaDiff (μ.tilted
            (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k) +
            deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2) +
        2 * replicaPairAverage
          (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k z) k))
        ∂(gaussianReal 0 1) := by
  have hum : Measurable u := hu.toSmartPathPotential.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hddu : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  have hκ0 : 0 ≤ Real.sqrt (t / (N + 1)) := Real.sqrt_nonneg _
  have hν (r : ℝ) : IsProbabilityMeasure
      (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum
      (fun x => hu.toSmartPathPotential.le x) _ t
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hfm (r : ℝ) : Measurable fun x : SmartPathState N M =>
      smartPathField t (smartPathDisorderUpdate ω k r) x k :=
    measurable_smartPathField_slice t _ k
  have hXm (r : ℝ) : Measurable fun x : SmartPathState N M =>
      ((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) :=
    hε.mul (hdu.comp (hfm r))
  have hXb (r : ℝ) (x : SmartPathState N M) :
      |((x.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)| ≤ D := by
    rw [abs_mul, abs_units_cast_eq_one, one_mul]
    exact hu.abs_deriv_le _
  have hLm (r : ℝ) : Measurable fun x : SmartPathState N M =>
      deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2 :=
    (hddu.comp (hfm r)).add ((hdu.comp (hfm r)).pow_const 2)
  have hLb (r : ℝ) (x : SmartPathState N M) :=
    abs_deriv₂_add_sq_le hu t (smartPathDisorderUpdate ω k r) k x
  -- the derivative of `G`, its bound, and Stein
  have hderiv (r : ℝ) := hasDerivAt_replicaDiff_update (μ := μ) (t := t) hu ω k F hF hFb r
  have hGc : Continuous fun r => replicaDiff (μ.tilted
      (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => ((x.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)) :=
    continuous_iff_continuousAt.2 fun r => (hderiv r).continuousAt
  have hGb (r : ℝ) : |replicaDiff (μ.tilted
      (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => ((x.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k))| ≤
      C * ((Fintype.card R : ℝ) * D + (Fintype.card R : ℝ) * D) := by
    have := hν r
    exact abs_replicaDiff_le _ F hF hFb _ (hXm r) (hXb r)
  have hxF : Integrable (fun r => r * replicaDiff (μ.tilted
      (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => ((x.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k))) (gaussianReal 0 1) := by
    have := (IsGaussian.integrable_id (μ := gaussianReal 0 1)).bdd_mul_of_abs_le
      hGc.aestronglyMeasurable (ae_of_all _ hGb)
    simpa only [mul_comm, id] using this
  have hKb (r : ℝ) (a b : SmartPathState N M) :=
    abs_smartPathPotentialKernel_le hu.toSmartPathPotential t (smartPathDisorderUpdate ω k r) k a b
  have hG'b (r : ℝ) : |Real.sqrt (t / (N + 1)) * replicaDiff (μ.tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2) +
      2 * Real.sqrt (t / (N + 1)) * replicaPairAverage (μ.tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k r) k)| ≤
      Real.sqrt (t / (N + 1)) * (C * ((Fintype.card R : ℝ) * (D₂ + D ^ 2) +
        (Fintype.card R : ℝ) * (D₂ + D ^ 2))) +
      2 * Real.sqrt (t / (N + 1)) * (C * (2 * (Fintype.card R : ℝ) ^ 2 * (D * D))) := by
    have := hν r
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hκ0]
      exact mul_le_mul_of_nonneg_left
        (abs_replicaDiff_le _ F hF hFb _ (hLm r) (hLb r)) hκ0
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (t / (N + 1)))]
      exact mul_le_mul_of_nonneg_left (abs_replicaPairAverage_le _ F hFb
        (abs_replicaPairCombination_le (hKb r))) (by positivity)
  have hG'm : Measurable fun r => Real.sqrt (t / (N + 1)) * replicaDiff
      (μ.tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2) +
      2 * Real.sqrt (t / (N + 1)) * replicaPairAverage (μ.tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k r) k) := by
    have : (fun r => Real.sqrt (t / (N + 1)) * replicaDiff (μ.tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
          deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2) +
        2 * Real.sqrt (t / (N + 1)) * replicaPairAverage (μ.tilted
          (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
          (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k r) k)) =
        deriv fun r => replicaDiff (μ.tilted
          (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
          (fun x => ((x.1.2 : ℤ) : ℝ) *
            deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)) :=
      funext fun r => (hderiv r).deriv.symm
    rw [this]
    exact measurable_deriv _
  have hF' := integrable_of_measurable_bound (m := gaussianReal 0 1) hG'm (hG'b ·)
  have hStein := integral_id_mul_gaussianReal_eq 1 hderiv hxF hF'
  simp only [NNReal.coe_one, one_mul] at hStein
  rw [hStein, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun r => by ring)

/-- **The `E'_ξ` term of Proposition 2.2.3, one replica and one constraint.** For a spin-only
observable `f` of the replicas `some r` and any replica `i`, integrating the auxiliary coordinate
`ξ_k` of replica `i` by parts in the base measure (the normalizer does not depend on `ξ`) gives
`⟨f ξ_k u'(S_k)(σ_i)⟩ = √((1-t)/(N+1)) ⟨f (u'' + u'^2)(S_k)(σ_i)⟩`. -/
theorem integral_pi_xi_mul_deriv {N M : ℕ} {R : Type*} [Fintype R] {t : ℝ} {u : ℝ → ℝ}
    {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (ω : SmartPathDisorder N M) (k : Fin M)
    (f : (R → PerceptronSpin N) → ℝ) (i : Option R) :
    ∫ σ : Option R → SmartPathState N M, f (fun r => (σ (some r)).1) *
        ((σ i).2 k * deriv u (smartPathField t ω (σ i) k))
      ∂(Measure.pi fun _ => (smartPathBase N M).tilted (smartPathEnergy u t ω)) =
      Real.sqrt ((1 - t) / (N + 1)) * ∫ σ : Option R → SmartPathState N M,
        f (fun r => (σ (some r)).1) *
          (deriv (deriv u) (smartPathField t ω (σ i) k) +
            deriv u (smartPathField t ω (σ i) k) ^ 2)
      ∂(Measure.pi fun _ => (smartPathBase N M).tilted (smartPathEnergy u t ω)) := by
  classical
  obtain ⟨C, hfb⟩ := exists_abs_le_of_finite f
  have hf := measurable_of_finite f
  simp only [smartPathBase_tilted_eq]
  rw [integral_pi_tilted_eq_div, integral_pi_tilted_eq_div, ← mul_div_assoc]
  congr 1
  set Eσ : (Option R → SmartPathState N M) → ℝ := fun σ => ∑ j, smartPathEnergy u t ω (σ j)
    with hEσ
  let Φ : (Option R → SmartPathState N M) → ℝ := fun σ =>
    f (fun r => (σ (some r)).1) * deriv u (smartPathField t ω (σ i) k) * Real.exp (Eσ σ)
  let Φ' : (Option R → SmartPathState N M) → ℝ := fun σ =>
    f (fun r => (σ (some r)).1) * (Real.sqrt ((1 - t) / (N + 1)) *
      (deriv (deriv u) (smartPathField t ω (σ i) k) +
        deriv u (smartPathField t ω (σ i) k) ^ 2)) * Real.exp (Eσ σ)
  have hEsum : ∀ (σ : Option R → SmartPathState N M) (y : SmartPathState N M),
      Eσ (update σ i y) = smartPathEnergy u t ω y +
        ∑ j ∈ Finset.univ.erase i, smartPathEnergy u t ω (σ j) := by
    intro σ y
    simp only [Eσ]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  have hΦ : ∀ σ (s : PerceptronSpin N) (ξ : Fin M → ℝ),
      HasDerivAt (fun τ => Φ (update σ i (s, update ξ k τ)))
        (Φ' (update σ i (s, ξ))) (ξ k) := by
    intro σ s ξ
    have hspin : ∀ τ : ℝ, (fun r => ((update σ i (s, update ξ k τ)) (some r)).1) =
        (fun r => ((update σ i (s, ξ)) (some r)).1) := fun τ => funext fun r => by
      by_cases h : some r = i
      · subst h; simp
      · simp [update_of_ne h]
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (f fun r => ((update σ i (s, ξ)) (some r)).1) *
        Real.exp ((((s.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 +
          ∑ k' ∈ Finset.univ.erase k, u (smartPathField t ω (s, ξ) k')) +
          ∑ j ∈ Finset.univ.erase i, smartPathEnergy u t ω (σ j)) := ⟨_, rfl⟩
    have hform : ∀ τ : ℝ, Φ (update σ i (s, update ξ k τ)) =
        A * (deriv u (smartPathField t ω (s, update ξ k 0) k +
          Real.sqrt ((1 - t) / (N + 1)) * τ) *
          Real.exp (u (smartPathField t ω (s, update ξ k 0) k +
            Real.sqrt ((1 - t) / (N + 1)) * τ))) := by
      intro τ
      simp only [Φ]
      rw [hspin τ, hEsum, update_self, smartPathEnergy_xi u t ω k s ξ τ,
        smartPathField_xi_self, hA]
      simp only [Real.exp_add]
      ring
    have hform' : Φ' (update σ i (s, ξ)) =
        A * (Real.sqrt ((1 - t) / (N + 1)) *
          (deriv (deriv u) (smartPathField t ω (s, update ξ k 0) k +
            Real.sqrt ((1 - t) / (N + 1)) * ξ k) +
            deriv u (smartPathField t ω (s, update ξ k 0) k +
              Real.sqrt ((1 - t) / (N + 1)) * ξ k) ^ 2) *
          Real.exp (u (smartPathField t ω (s, update ξ k 0) k +
            Real.sqrt ((1 - t) / (N + 1)) * ξ k))) := by
      have e := smartPathEnergy_xi u t ω k s ξ (ξ k)
      have f2 := smartPathField_xi_self t ω k s ξ (ξ k)
      rw [Function.update_eq_self] at e f2
      simp only [Φ']
      rw [hEsum, update_self, e, f2, hA]
      simp only [Real.exp_add]
      ring
    simp only [hform]
    rw [hform']
    exact (hasDerivAt_deriv_u_mul_exp_affine (u := u) (u' := deriv u) (u'' := deriv (deriv u))
      (fun x => (hu.differentiable x).hasDerivAt)
      (fun x => (hu.differentiable_deriv x).hasDerivAt) _ _ (ξ k)).const_mul A |>.congr_deriv
      (by ring)
  have hum : Measurable u := hu.toSmartPathPotential.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hddu : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  have hfld : Measurable fun x : SmartPathState N M => smartPathField t ω x k :=
    measurable_smartPathField_slice t ω k
  have hfS : Measurable fun σ : Option R → SmartPathState N M =>
      f (fun r => (σ (some r)).1) :=
    hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply (some r)))
  have hfldσ : Measurable fun σ : Option R → SmartPathState N M =>
      smartPathField t ω (σ i) k := hfld.comp (measurable_pi_apply i)
  have hEm : Measurable Eσ :=
    Finset.measurable_sum _ fun j _ =>
      (measurable_smartPathEnergy_slice hum t ω).comp (measurable_pi_apply j)
  have hEb (σ : Option R → SmartPathState N M) :
      Eσ σ ≤ (Fintype.card (Option R) : ℝ) * (M * B + Real.sqrt (1 - t) * |ω.2|) :=
    calc Eσ σ ≤ ∑ _j : Option R, (M * B + Real.sqrt (1 - t) * |ω.2|) :=
          Finset.sum_le_sum fun j _ =>
            perceptron_smart_path_energy_le (fun x => hu.toSmartPathPotential.le x) t ω (σ j)
      _ = _ := by simp; ring
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hfb fun _ => (fun _ => 1, 1))
  have hD₂0 : 0 ≤ D₂ := (abs_nonneg _).trans (hu.abs_deriv₂_le 0)
  have hD0 : 0 ≤ D := hu.toSmartPathPotential.D_nonneg
  have hΦm : Measurable Φ := (hfS.mul (hdu.comp hfldσ)).mul hEm.exp
  have hΦ'm : Measurable Φ' :=
    (hfS.mul (((hddu.comp hfldσ).add ((hdu.comp hfldσ).pow_const 2)).const_mul _)).mul hEm.exp
  have hΦb : ∃ K, ∀ σ, |Φ σ| ≤ K :=
    ⟨C * D * Real.exp ((Fintype.card (Option R) : ℝ) * (M * B + Real.sqrt (1 - t) * |ω.2|)),
      fun σ => abs_mul_exp_le (by
        rw [abs_mul]
        exact mul_le_mul (hfb _) (hu.abs_deriv_le _) (abs_nonneg _) hC0) (hEb σ)⟩
  have hΦ'b : ∃ K, ∀ σ, |Φ' σ| ≤ K :=
    ⟨C * (Real.sqrt ((1 - t) / (N + 1)) * (D₂ + D ^ 2)) *
      Real.exp ((Fintype.card (Option R) : ℝ) * (M * B + Real.sqrt (1 - t) * |ω.2|)),
      fun σ => abs_mul_exp_le (by
        have hc0 : 0 ≤ Real.sqrt ((1 - t) / (N + 1)) := Real.sqrt_nonneg _
        rw [abs_mul, abs_mul, abs_of_nonneg hc0]
        exact mul_le_mul (hfb _) (mul_le_mul_of_nonneg_left (abs_deriv₂_add_sq_le hu t ω k (σ i))
          hc0) (by positivity) hC0) (hEb σ)⟩
  obtain ⟨K₁, hK₁⟩ := hΦb
  obtain ⟨K₂, hK₂⟩ := hΦ'b
  have h1 : Integrable (fun σ : Option R → SmartPathState N M => (σ i).2 k * Φ σ)
      (Measure.pi fun _ : Option R => (smartPathSpinProb N).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
    have hξ : Integrable (fun y : SmartPathState N M => y.2 k)
        ((smartPathSpinProb N).prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)) :=
      (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
        (f := fun x : ℝ => x) (IsGaussian.integrable_id)).comp_snd _
    have := (integrable_comp_eval (μ := fun _ : Option R => (smartPathSpinProb N).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)) (i := i) hξ).bdd_mul_of_abs_le
      hΦm.aestronglyMeasurable (ae_of_all _ hK₁)
    simpa only [mul_comm] using this
  have h2 : Integrable Φ' (Measure.pi fun _ : Option R => (smartPathSpinProb N).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)) :=
    integrable_of_measurable_bound hΦ'm hK₂
  have hstein := integral_apply_snd_mul_pi_prod_stdGaussian_eq (J := Option R)
    (smartPathSpinProb N) i k (Φ := Φ) (Φ' := Φ') hΦ h1 h2
  have hL : (∫ σ : Option R → SmartPathState N M, f (fun r => (σ (some r)).1) *
        ((σ i).2 k * deriv u (smartPathField t ω (σ i) k)) *
        Real.exp (∑ j, smartPathEnergy u t ω (σ j))
      ∂(Measure.pi fun _ : Option R => smartPathBaseProb N M)) =
      ∫ σ : Option R → SmartPathState N M, (σ i).2 k * Φ σ
        ∂(Measure.pi fun _ : Option R => (smartPathSpinProb N).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)) :=
    integral_congr_ae (ae_of_all _ fun σ => by simp only [Φ]; ring)
  rw [hL, hstein, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun σ => by simp only [Φ']; ring)

/-- **The `E'_ξ` term of Proposition 2.2.3.** For a spin-only observable, the replica difference of
the auxiliary-spin part `E'_ξ` of the energy derivative is `-1/(2(N+1))` times the sum over the
constraints of the replica difference of `u'' + u'^2` at the field `S_k`: it is the exact
opposite of the diagonal contribution of the quenched-coupling term
(`integral_mul_replicaDiff_update`). -/
theorem replicaDiff_smartPathEnergyDerivXi {N M : ℕ} {R : Type*} [Fintype R] {t : ℝ}
    (ht : t < 1) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ω : SmartPathDisorder N M) (f : (R → PerceptronSpin N) → ℝ) :
    replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) (smartPathEnergyDerivXi u t ω) =
      -(1 / (2 * ((N : ℝ) + 1))) * ∑ k : Fin M, replicaDiff
        ((smartPathBase N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (fun x => deriv (deriv u) (smartPathField t ω x k) +
          deriv u (smartPathField t ω x k) ^ 2) := by
  classical
  obtain ⟨C, hfb⟩ := exists_abs_le_of_finite f
  have hf := measurable_of_finite f
  have hum : Measurable u := hu.toSmartPathPotential.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hν : IsProbabilityMeasure ((smartPathBase N M).tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum
      (fun x => hu.toSmartPathPotential.le x) ω t
  have hFm : Measurable fun σ : R → SmartPathState N M => f (fun r => (σ r).1) :=
    hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))
  have hFb : ∀ σ : R → SmartPathState N M, |f (fun r => (σ r).1)| ≤ C := fun σ => hfb _
  have hfld (k : Fin M) : Measurable fun x : SmartPathState N M => smartPathField t ω x k :=
    measurable_smartPathField_slice t ω k
  -- integrability of `ξ_k u'(S_k)` under the Gibbs measure
  have hint (k : Fin M) : Integrable (fun x : SmartPathState N M =>
      x.2 k * deriv u (smartPathField t ω x k))
      ((smartPathBase N M).tilted (smartPathEnergy u t ω)) := by
    have hξ : Integrable (fun y : SmartPathState N M => y.2 k) (smartPathBase N M) :=
      (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
        (f := fun x : ℝ => x) (IsGaussian.integrable_id)).comp_snd _
    refine integrable_tilted_of_abs_le_envelope
      (measurable_smartPathEnergy_slice hum t ω).aemeasurable
      ((((measurable_pi_apply k).comp measurable_snd).mul (hdu.comp (hfld k)))).aestronglyMeasurable
      (hξ.norm.const_mul D) (A := M * B + Real.sqrt (1 - t) * |ω.2|)
      (ae_of_all _ fun x => perceptron_smart_path_energy_le
        (fun x => hu.toSmartPathPotential.le x) t ω x) (ae_of_all _ fun x => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hu.abs_deriv_le _ |>.trans le_rfl)
      le_rfl (abs_nonneg _) hu.toSmartPathPotential.D_nonneg
  have hxi := smartPathEnergyDerivXi_eq_sum u t ω
  have hstep (k : Fin M) : replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
      (fun x => x.2 k * deriv u (smartPathField t ω x k)) =
      Real.sqrt ((1 - t) / (N + 1)) * replicaDiff
        ((smartPathBase N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (fun x => deriv (deriv u) (smartPathField t ω x k) +
          deriv u (smartPathField t ω x k) ^ 2) := by
    rw [replicaDiff_eq, replicaDiff_eq]
    simp only [integral_pi_xi_mul_deriv hu ω k f]
    simp only [Finset.mul_sum, ← mul_assoc, mul_sub]
    ring
  rw [hxi, replicaDiff_finset_sum _ _ hFm.aestronglyMeasurable hFb Finset.univ _
    (fun k _ => (hint k).const_mul _)]
  simp only [replicaDiff_const_mul, hstep, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := smartPath_auxiliary_prefactor_eq_neg (N := N) ht
  push_cast at this ⊢
  rw [← mul_assoc, this]

end SpinGlasses
