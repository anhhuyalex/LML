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

open MeasureTheory ProbabilityTheory
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
theorem smartPath_auxiliary_prefactor_eq_neg {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  have := smartPath_sqrt_scaling_prefactor_eq (N := N) (sub_pos.2 ht.2)
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
theorem hasDerivAt_replicaDiff_lastSpin_lastField {N M : ℕ} {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (ω₀ : (Fin M → Fin N → ℝ) × (Fin M → ℝ))
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    (y : ℝ) :
    HasDerivAt (fun r => replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, r)))
        F (fun x => ((x.1.2 : ℤ) : ℝ)))
      (2 * Real.sqrt (1 - t) * replicaPairAverage
        ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel) y := by
  set q := Real.sqrt (1 - t) with hq
  have hν (r : ℝ) : IsProbabilityMeasure
      ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hB (ω₀, r) t
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hεb (x : SmartPathState N M) : |((x.1.2 : ℤ) : ℝ)| ≤ 1 := (abs_units_cast_eq_one _).le
  have hE' : ∀ x : SmartPathState N M, |q * ((x.1.2 : ℤ) : ℝ)| ≤ q := fun x => by
    rw [abs_mul, abs_units_cast_eq_one, mul_one, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hbd := hasDerivAt_replicaDiff_tilted_replicaDiff
    (μ := smartPathBase N M) (E := fun r => smartPathEnergy u t (ω₀, r))
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
    ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F hF hFb
    (fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ)) hε hεb 1 q
    (fun x => by rw [← sq]; exact units_cast_sq _)
  exact hbr ▸ hbd

/-- **The `E'_Y` term of Proposition 2.2.3 (Stein in the last field).** For the last field
`y ∼ 𝒩(0, v)` (`v = 0` allowed), the `y`-average of the replica difference of the energy
derivative `E'_Y` is `-v` times the `y`-average of the two-fresh-replica average of the last-spin
kernel `ε_x ε_y`, the other disorder `ω₀ = (g, a)` being fixed. -/
theorem integral_replicaDiff_smartPathEnergyDerivY {N M : ℕ} {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (v : ℝ≥0) (ω₀ : (Fin M → Fin N → ℝ) × (Fin M → ℝ))
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ y, replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F
        (smartPathEnergyDerivY t (ω₀, y)) ∂(gaussianReal 0 v) =
      -(v : ℝ) * ∫ y, replicaPairAverage
        ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel
        ∂(gaussianReal 0 v) := by
  set q := Real.sqrt (1 - t) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 (sub_pos.2 ht.2)
  have hν (r : ℝ) : IsProbabilityMeasure
      ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hB (ω₀, r) t
  set Gf : ℝ → ℝ := fun y => replicaDiff
    ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F
    (fun x => ((x.1.2 : ℤ) : ℝ)) with hGf
  set PA : ℝ → ℝ := fun y => replicaPairAverage
    ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel with hPA
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
    (U := lastSpinKernel (N := N) (M := M)) ⟨1, fun a b => by
      unfold lastSpinKernel
      rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]⟩
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
  have hpt (y : ℝ) : replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F
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
theorem hasDerivAt_replicaDiff_update {N M : ℕ} {R : Type*} [Fintype R] [LinearOrder R]
    {t : ℝ} {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ω : SmartPathDisorder N M) (k : Fin M)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    (z : ℝ) :
    HasDerivAt (fun r => replicaDiff
        ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (fun x => ((x.1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)))
      (Real.sqrt (t / (N + 1)) *
        replicaDiff ((smartPathBase N M).tilted
          (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k) +
            deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2) +
        2 * Real.sqrt (t / (N + 1)) * replicaPairAverage
          ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k z) k)) z := by
  have hum : Measurable u := hu.toSmartPathPotential.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hddu : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  have hκ0 : 0 ≤ Real.sqrt (t / (N + 1)) := Real.sqrt_nonneg _
  have hν (r : ℝ) : IsProbabilityMeasure
      ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum
      (fun x => hu.toSmartPathPotential.le x) _ t
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hfm (r : ℝ) : Measurable fun x : SmartPathState N M =>
      smartPathField t (smartPathDisorderUpdate ω k r) x k := by
    unfold smartPathField smartPathFieldNoAux
    fun_prop
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
    (μ := smartPathBase N M) (R := R)
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
    ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F hF hFb
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
    unfold smartPathPotentialKernel
    ring
  rw [hsq, hker] at hbr
  refine hmov.congr_deriv ?_
  rw [hbr, replicaDiff_const_mul]
  have hI1 : Integrable (fun x : SmartPathState N M =>
      deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k))
      ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) :=
    integrable_of_measurable_bound (hddu.comp (hfm z)) (M := D₂) fun x => hu.abs_deriv₂_le _
  have hI2 : Integrable (fun x : SmartPathState N M =>
      deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2)
      ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) :=
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

/-- **Stein in one quenched coupling `a_k ∼ 𝒩(0, 1)`** (the other disorder fixed). With
`h = ε u'(S_k)`, `∫ z, z · replicaDiff ν_z F h_z` equals
`√(t/(N+1)) ∫ z, [replicaDiff ν_z F (u'' + u'^2)(S_k) + 2 replicaPairAverage ν_z F U_k]`: the
diagonal `u'^2` and the pair term of the potential kernel `U_k`. -/
theorem integral_mul_replicaDiff_update {N M : ℕ} {R : Type*} [Fintype R] [LinearOrder R]
    {t : ℝ} {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ω : SmartPathDisorder N M) (k : Fin M)
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ z, z * replicaDiff
        ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
        (fun x => ((x.1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k)) ∂(gaussianReal 0 1) =
      Real.sqrt (t / (N + 1)) * ∫ z,
        (replicaDiff ((smartPathBase N M).tilted
            (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k z) x k) +
            deriv u (smartPathField t (smartPathDisorderUpdate ω k z) x k) ^ 2) +
        2 * replicaPairAverage
          ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k z))) F
          (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k z) k))
        ∂(gaussianReal 0 1) := by
  have hum : Measurable u := hu.toSmartPathPotential.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hddu : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  have hκ0 : 0 ≤ Real.sqrt (t / (N + 1)) := Real.sqrt_nonneg _
  have hν (r : ℝ) : IsProbabilityMeasure
      ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hum
      (fun x => hu.toSmartPathPotential.le x) _ t
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hfm (r : ℝ) : Measurable fun x : SmartPathState N M =>
      smartPathField t (smartPathDisorderUpdate ω k r) x k := by
    unfold smartPathField smartPathFieldNoAux
    fun_prop
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
  have hLb (r : ℝ) (x : SmartPathState N M) :
      |deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2| ≤ D₂ + D ^ 2 := by
    refine (abs_add_le _ _).trans (add_le_add (hu.abs_deriv₂_le _) ?_)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hu.abs_deriv_le _) 2
  -- the derivative of `G`, its bound, and Stein
  have hderiv (r : ℝ) := hasDerivAt_replicaDiff_update (t := t) hu ω k F hF hFb r
  have hGc : Continuous fun r => replicaDiff ((smartPathBase N M).tilted
      (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => ((x.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k)) :=
    continuous_iff_continuousAt.2 fun r => (hderiv r).continuousAt
  have hGb (r : ℝ) : |replicaDiff ((smartPathBase N M).tilted
      (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => ((x.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k))| ≤
      C * ((Fintype.card R : ℝ) * D + (Fintype.card R : ℝ) * D) := by
    have := hν r
    exact abs_replicaDiff_le _ F hF hFb _ (hXm r) (hXb r)
  have hxF : Integrable (fun r => r * replicaDiff ((smartPathBase N M).tilted
      (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => ((x.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k))) (gaussianReal 0 1) := by
    have := (IsGaussian.integrable_id (μ := gaussianReal 0 1)).bdd_mul_of_abs_le
      hGc.aestronglyMeasurable (ae_of_all _ hGb)
    simpa only [mul_comm, id] using this
  have hKb (r : ℝ) (a b : SmartPathState N M) :
      |smartPathPotentialKernel u t (smartPathDisorderUpdate ω k r) k a b| ≤ D * D := by
    unfold smartPathPotentialKernel
    rw [show ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) a k) *
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) b k) =
        (((a.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) a k)) *
        (((b.1.2 : ℤ) : ℝ) * deriv u (smartPathField t (smartPathDisorderUpdate ω k r) b k))
        by ring, abs_mul]
    exact mul_le_mul (hXb r a) (hXb r b) (abs_nonneg _) ((abs_nonneg _).trans (hXb r a))
  have hG'b (r : ℝ) : |Real.sqrt (t / (N + 1)) * replicaDiff ((smartPathBase N M).tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2) +
      2 * Real.sqrt (t / (N + 1)) * replicaPairAverage ((smartPathBase N M).tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k r) k)| ≤
      Real.sqrt (t / (N + 1)) * (C * ((Fintype.card R : ℝ) * (D₂ + D ^ 2) +
        (Fintype.card R : ℝ) * (D₂ + D ^ 2))) +
      2 * Real.sqrt (t / (N + 1)) * (C * ((2 * (Fintype.card R : ℝ) ^ 2 +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2) * (D * D))) := by
    have := hν r
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hκ0]
      exact mul_le_mul_of_nonneg_left
        (abs_replicaDiff_le _ F hF hFb _ (hLm r) (hLb r)) hκ0
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (t / (N + 1)))]
      exact mul_le_mul_of_nonneg_left (abs_replicaPairAverage_le _ F hFb
        (abs_replicaPairCombination_le (hKb r))) (by positivity)
  have hG'm : Measurable fun r => Real.sqrt (t / (N + 1)) * replicaDiff
      ((smartPathBase N M).tilted (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
      (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
        deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2) +
      2 * Real.sqrt (t / (N + 1)) * replicaPairAverage ((smartPathBase N M).tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k r) k) := by
    have : (fun r => Real.sqrt (t / (N + 1)) * replicaDiff ((smartPathBase N M).tilted
        (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
        (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderUpdate ω k r) x k) +
          deriv u (smartPathField t (smartPathDisorderUpdate ω k r) x k) ^ 2) +
        2 * Real.sqrt (t / (N + 1)) * replicaPairAverage ((smartPathBase N M).tilted
          (smartPathEnergy u t (smartPathDisorderUpdate ω k r))) F
          (smartPathPotentialKernel u t (smartPathDisorderUpdate ω k r) k)) =
        deriv fun r => replicaDiff ((smartPathBase N M).tilted
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

end SpinGlasses
