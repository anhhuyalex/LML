/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.HardConstraintBoundary
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.ReplicaSymmetricBounds

/-!
# The Shcherbina--Tirozzi model: soft-to-hard stability of RS solutions (Corollary 3.3.4)

Let `0 < κ₀ ≤ κ₁`, `α₀ < 2`, `h₀ ≥ 0`, `τ ≥ 0`. Consider concave smooth potentials `u ≤ 0`
vanishing on `[τ, ∞)` with `exp (u (τ - ε')) ≤ ε'`, and solutions `(q, ρ)` of the soft
replica-symmetric equations (3.69), (3.76), (3.77) for `0 ≤ α ≤ α₀`, `κ₀ ≤ κ ≤ κ₁`, `|h| ≤ h₀`.

This file proves **Talagrand, Corollary 3.3.4** (conditional on the existence of the unique hard
solution `(q₀, ρ₀)` of Theorem 3.3.1): for every `ε > 0`, there is `ε' > 0` such that any soft
solution `(q, ρ)` satisfies `|q - q₀| ≤ ε` and `|ρ - ρ₀| ≤ ε`.

The key analytic ingredient is that as `ε' → 0`, the soft Gaussian-smoothing ratios
`V_n(y) = 𝔼[u_n'(y + c_n ξ) e^{u_n}] / 𝔼[e^{u_n}] = c_n⁻¹ 𝔼[ξ e^{u_n}] / 𝔼[e^{u_n}]` and
`W_n(y) = c_n⁻² 𝔼[(ξ² - 1) e^{u_n}] / 𝔼[e^{u_n}]` converge to the hard inverse Mills ratio
expressions `c⁻¹ mills((τ - y) / c)` and `c⁻² ((τ - y)/c) mills((τ - y)/c)`.

## Main declarations

* `SpinGlasses.hasDerivAt_shcherbinaTirozziHardFunctional_self_fixed`: `∂F/∂ρ` at fixed `q < ρ`.
* `SpinGlasses.isCritical_shcherbinaTirozziHardFunctional_of_tendsto_soft`: along a converging
  sequence of parameters `(α_n, κ_n, h_n, q_n, ρ_n) → (α, κ, h, q, ρ)` with `0 ≤ q < ρ` and
  potentials `u_n` satisfying `exp (u_n (τ - ε_n)) ≤ ε_n → 0`, `(q, ρ)` is a critical point of
  `shcherbinaTirozziHardFunctional α κ h τ`.
* `SpinGlasses.exists_bound_of_shcherbinaTirozziHardFunctional_critical`: uniform a priori bounds
  `q₀, ρ₀, (ρ₀ - q₀)⁻¹ ≤ C` for hard RS critical points.
* `SpinGlasses.exists_soft_rs_close_to_hard`: Talagrand, Corollary 3.3.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SpinGlasses

local notation "mills " v:arg =>
  gaussianPDFReal 0 1 v / Measure.real (gaussianReal 0 1) (Ici v)

/-- Gaussian integration by parts for `V`: for `u ≤ 0` differentiable with `|u'| ≤ D` and `c > 0`,
`∫ u'(y + c ξ) e^{u(y + c ξ)} dγ = c⁻¹ ∫ ξ e^{u(y + c ξ)} dγ`. -/
private theorem integral_deriv_mul_exp_eq_inv_mul_integral_id {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) =
      c⁻¹ * ∫ ξ, ξ * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
  have hum : Measurable u := hu.continuous.measurable
  have hd : ∀ ξ, HasDerivAt (fun ξ => Real.exp (u (y + c * ξ)))
      (c * (deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)))) ξ := fun ξ => by
    have h1 : HasDerivAt (fun ξ => y + c * ξ) c ξ := by
      simpa using ((hasDerivAt_id ξ).const_mul c).const_add y
    refine (((hu _).hasDerivAt.comp ξ h1).exp).congr_deriv ?_
    simp only [Function.comp_apply]; ring
  have hid : Integrable (fun ξ : ℝ => ξ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hwi : Integrable (fun ξ => ξ * Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
    refine hid.abs.mono' (measurable_id.mul
      (hum.comp (by fun_prop : Measurable fun ξ : ℝ => y + c * ξ)).exp).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))
  have hIBP : ∫ ξ, ξ * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) =
      c * ∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
    rw [integral_id_mul_gaussianReal_eq 1 hd hwi
      ((integrable_mul_exp_comp_add_gaussianReal hum hu0 (measurable_deriv u) hD y c).const_mul c),
      NNReal.coe_one, one_mul, integral_const_mul]
  rw [hIBP, inv_mul_cancel_left₀ hc.ne']

/-- Second Gaussian integration by parts for `W`: for `u ≤ 0` twice differentiable with
`|u'| ≤ D`, `|u''| ≤ D₂` and `c > 0`,
`∫ (u'' + u'²)(y + c ξ) e^{u(y + c ξ)} dγ = c⁻² ∫ (ξ² - 1) e^{u(y + c ξ)} dγ`. -/
private theorem integral_deriv_two_add_sq_mul_exp_eq_inv_sq_mul {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u)) (hu0 : ∀ x, u x ≤ 0)
    {D D₂ : ℝ} (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) =
      c⁻¹ ^ 2 * ∫ ξ, (ξ ^ 2 - 1) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
  have hum : Measurable u := hu.continuous.measurable
  have haff : Measurable fun ξ : ℝ => y + c * ξ := by fun_prop
  set g : ℝ → ℝ := fun ξ => deriv u (y + c * ξ) * Real.exp (u (y + c * ξ))
  have hgi : Integrable (fun ξ => ξ * g ξ) (gaussianReal 0 1) := by
    have hid : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := IsGaussian.integrable_id
    have hg : AEStronglyMeasurable g (gaussianReal 0 1) :=
      (((measurable_deriv u).comp haff).mul (hum.comp haff).exp).aestronglyMeasurable
    have hgb : ∀ᵐ ξ ∂gaussianReal 0 1, ‖g ξ‖ ≤ D :=
      ae_of_all _ fun ξ => by
        simpa only [g, Real.norm_eq_abs, Real.exp_zero, mul_one] using
          abs_mul_exp_le (hD (y + c * ξ)) (hu0 (y + c * ξ))
    simpa only [id_eq, mul_comm] using hid.bdd_mul hg hgb
  have hIBP1 : ∫ ξ, ξ * g ξ ∂(gaussianReal 0 1) =
      c * ∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
    simpa only [NNReal.coe_one, one_mul, g] using
      integral_id_mul_deriv_u_mul_exp_affine_gaussianReal 1
        (fun x => (hu x).hasDerivAt) (fun x => (hu2 x).hasDerivAt) hu0 hD hD₂ y c
  -- Also integrate `ξ * (ξ * exp (u (y + c ξ)))` by parts
  have h2_deriv : ∀ ξ, HasDerivAt (fun ξ => ξ * Real.exp (u (y + c * ξ)))
      (Real.exp (u (y + c * ξ)) + c * (ξ * g ξ)) ξ := fun ξ => by
    have h1 : HasDerivAt (fun ξ => y + c * ξ) c ξ := by
      simpa using ((hasDerivAt_id ξ).const_mul c).const_add y
    have hexp' := ((hu _).hasDerivAt.comp ξ h1).exp
    refine ((hasDerivAt_id ξ).mul hexp').congr_deriv ?_
    simp only [Function.comp_apply, id_eq, g]; ring
  have hxi2_int : Integrable (fun ξ => ξ * (ξ * Real.exp (u (y + c * ξ)))) (gaussianReal 0 1) := by
    have hsq : Integrable (fun ξ : ℝ => ξ ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 2).integrable_sq
    refine hsq.mono'
      (measurable_id.mul (measurable_id.mul (hum.comp haff).exp)).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← sq,
      sq_abs]
    exact mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))
  have hexp_int : Integrable (fun ξ => Real.exp (u (y + c * ξ))) (gaussianReal 0 1) :=
    integrable_exp_comp_add_gaussianReal hum hu0 y c
  have hIBP2 : ∫ ξ, ξ * (ξ * Real.exp (u (y + c * ξ))) ∂(gaussianReal 0 1) =
      (∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) +
        c * ∫ ξ, ξ * g ξ ∂(gaussianReal 0 1) := by
    rw [integral_id_mul_gaussianReal_eq 1 h2_deriv hxi2_int (hexp_int.add (hgi.const_mul c)),
      NNReal.coe_one, one_mul, integral_add hexp_int (hgi.const_mul c), integral_const_mul]
  have hsub : ∫ ξ, (ξ ^ 2 - 1) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) =
      (∫ ξ, ξ * (ξ * Real.exp (u (y + c * ξ))) ∂(gaussianReal 0 1)) -
        ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
    rw [← integral_sub hxi2_int hexp_int]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    ring
  rw [hsub, hIBP2, add_sub_cancel_left, hIBP1]
  have hc0 : c ≠ 0 := hc.ne'
  field_simp

/-- The truncated Gaussian moments on `[v, ∞)`:
`∫_{ξ ≥ v} ξ dγ = p(v)` and `∫_{ξ ≥ v} (ξ² - 1) dγ = v p(v)`. -/
private theorem setIntegral_Ici_gaussianReal_moments (v : ℝ) :
    (∫ ξ in Ici v, ξ ∂(gaussianReal 0 1) = gaussianPDFReal 0 1 v) ∧
      (∫ ξ in Ici v, (ξ ^ 2 - 1) ∂(gaussianReal 0 1) = v * gaussianPDFReal 0 1 v) := by
  have h1 : ∫ ξ in Ici v, ξ ∂(gaussianReal 0 1) = gaussianPDFReal 0 1 v := by
    rw [setIntegral_Ici_gaussianReal, integral_Ioi_id_mul_gaussianPDFReal]
  have h2 : ∫ ξ in Ici v, (ξ ^ 2 - 1) ∂(gaussianReal 0 1) = v * gaussianPDFReal 0 1 v := by
    rw [setIntegral_Ici_gaussianReal]
    have hsub : ∀ t : ℝ, (t ^ 2 - 1) * gaussianPDFReal 0 1 t =
        t ^ 2 * gaussianPDFReal 0 1 t - gaussianPDFReal 0 1 t := fun t => by ring
    simp_rw [hsub]
    have hsq_i : Integrable (fun t : ℝ => t ^ 2 * gaussianPDFReal 0 1 t) volume :=
      integrable_mul_gaussianPDFReal_of_integrable ((memLp_id_gaussianReal 2).integrable_sq)
    rw [integral_sub hsq_i.integrableOn (integrable_gaussianPDFReal 0 1).integrableOn,
      integral_Ioi_sq_mul_gaussianPDFReal, ← measureReal_gaussianReal_Ici]
    ring
  exact ⟨h1, h2⟩

/-- Pointwise soft-to-hard convergence of `exp (u_n (y_n + c_n ξ))` to `1_{ξ ≥ (τ - y)/c}` for
every `ξ ≠ (τ - y)/c`, when `u_n ≤ 0` is monotone, vanishes on `[τ, ∞)`, and satisfies
`exp (u_n (τ - ε_n)) ≤ ε_n → 0`. -/
private theorem tendsto_exp_soft_potential {u : ℕ → ℝ → ℝ} {ε y c : ℕ → ℝ} {y₀ c₀ τ : ℝ}
    (hc₀ : 0 < c₀) (hmono : ∀ n, Monotone (u n))
    (huτ : ∀ n x, τ ≤ x → u n x = 0)
    (huε : ∀ n, Real.exp (u n (τ - ε n)) ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 y₀)) (hc : Tendsto c atTop (𝓝 c₀))
    {ξ : ℝ} (hξ : ξ ≠ (τ - y₀) / c₀) :
    Tendsto (fun n => Real.exp (u n (y n + c n * ξ))) atTop
      (𝓝 ((Ici ((τ - y₀) / c₀)).indicator (fun _ => (1 : ℝ)) ξ)) := by
  have harg : Tendsto (fun n => y n + c n * ξ) atTop (𝓝 (y₀ + c₀ * ξ)) :=
    hy.add (hc.mul_const ξ)
  rcases lt_or_gt_of_ne hξ with hlt | hgt
  · -- `ξ < (τ - y₀) / c₀`, i.e., `y₀ + c₀ ξ < τ`
    have hlt' : y₀ + c₀ * ξ < τ := by
      rw [lt_div_iff₀ hc₀] at hlt; linarith
    rw [Set.indicator_of_notMem (by simpa using hlt)]
    have hev : ∀ᶠ n in atTop, y n + c n * ξ ≤ τ - ε n := by
      have hdiff : Tendsto (fun n => (τ - ε n) - (y n + c n * ξ)) atTop
          (𝓝 ((τ - 0) - (y₀ + c₀ * ξ))) := (tendsto_const_nhds.sub hε).sub harg
      filter_upwards [hdiff.eventually (Ioi_mem_nhds (a := 0) (by linarith))] with n hn
      linarith
    refine squeeze_zero' (Eventually.of_forall fun n => (Real.exp_pos _).le) ?_ hε
    filter_upwards [hev] with n hn
    exact (Real.exp_le_exp.2 (hmono n hn)).trans (huε n)
  · -- `ξ > (τ - y₀) / c₀`, i.e., `τ < y₀ + c₀ ξ`
    have hgt' : τ < y₀ + c₀ * ξ := by
      rw [div_lt_iff₀ hc₀] at hgt; linarith
    rw [Set.indicator_of_mem (by simpa using hgt.le)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [harg.eventually (Ioi_mem_nhds hgt')] with n hn
    rw [huτ n _ hn.le, Real.exp_zero]

/-- **Soft-to-hard limit of the Gaussian-smoothing ratios:** along a sequence of monotone potentials
`u_n ≤ 0` vanishing on `[τ, ∞)` with `exp (u_n (τ - ε_n)) ≤ ε_n → 0`, if `y_n → y₀` and
`c_n → c₀ > 0`, then:
* `𝔼[e^{u_n}] → ℙ(ξ ≥ v₀)`,
* `c_n⁻¹ 𝔼[ξ e^{u_n}] / 𝔼[e^{u_n}] → c₀⁻¹ mills v₀`,
* `c_n⁻² 𝔼[(ξ² - 1) e^{u_n}] / 𝔼[e^{u_n}] → c₀⁻² v₀ mills v₀`,
where `v₀ = (τ - y₀) / c₀`. -/
private theorem tendsto_soft_gaussian_ratios {u : ℕ → ℝ → ℝ} {ε y c : ℕ → ℝ} {y₀ c₀ τ : ℝ}
    (hc₀ : 0 < c₀) (hmono : ∀ n, Monotone (u n)) (hu0 : ∀ n x, u n x ≤ 0)
    (huτ : ∀ n x, τ ≤ x → u n x = 0)
    (huε : ∀ n, Real.exp (u n (τ - ε n)) ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 y₀)) (hc : Tendsto c atTop (𝓝 c₀)) :
    let v₀ : ℝ := (τ - y₀) / c₀
    Tendsto (fun n => (c n)⁻¹ * (∫ ξ, ξ * Real.exp (u n (y n + c n * ξ)) ∂(gaussianReal 0 1)) /
        (∫ ξ, Real.exp (u n (y n + c n * ξ)) ∂(gaussianReal 0 1))) atTop
      (𝓝 (c₀⁻¹ * mills v₀)) ∧
    Tendsto (fun n => (c n)⁻¹ ^ 2 *
        (∫ ξ, (ξ ^ 2 - 1) * Real.exp (u n (y n + c n * ξ)) ∂(gaussianReal 0 1)) /
        (∫ ξ, Real.exp (u n (y n + c n * ξ)) ∂(gaussianReal 0 1))) atTop
      (𝓝 (c₀⁻¹ ^ 2 * (v₀ * mills v₀))) := by
  intro v₀
  set γ := gaussianReal 0 1
  have hae : ∀ᵐ ξ ∂γ, ξ ≠ v₀ := by
    have h0 : γ {v₀} = 0 := by
      rw [show γ = gaussianReal 0 1 from rfl, gaussianReal_of_var_ne_zero 0 one_ne_zero,
        withDensity_apply _ (measurableSet_singleton v₀)]
      simp
    rwa [ae_iff, show {ξ | ¬ξ ≠ v₀} = {v₀} by ext; simp]
  have hpt : ∀ᵐ ξ ∂γ, Tendsto (fun n => Real.exp (u n (y n + c n * ξ))) atTop
      (𝓝 ((Ici v₀).indicator (fun _ => (1 : ℝ)) ξ)) :=
    hae.mono fun ξ hξ => tendsto_exp_soft_potential hc₀ hmono huτ huε hε hy hc hξ
  have hZ : Tendsto (fun n => ∫ ξ, Real.exp (u n (y n + c n * ξ)) ∂γ) atTop
      (𝓝 (γ.real (Ici v₀))) := by
    have hlim_eq : ∫ ξ, (Ici v₀).indicator (fun _ => (1 : ℝ)) ξ ∂γ = γ.real (Ici v₀) := by
      rw [integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul, mul_one]
    rw [← hlim_eq]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => ((hmono n).measurable.comp (by fun_prop)).exp.aestronglyMeasurable)
      (integrable_const 1)
      (fun n => ae_of_all _ fun ξ => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.2 (hu0 n _))
      hpt
  obtain ⟨hmom1, hmom2⟩ := setIntegral_Ici_gaussianReal_moments v₀
  have hN1 : Tendsto (fun n => ∫ ξ, ξ * Real.exp (u n (y n + c n * ξ)) ∂γ) atTop
      (𝓝 (gaussianPDFReal 0 1 v₀)) := by
    have hlim_eq : ∫ ξ, ξ * (Ici v₀).indicator (fun _ => (1 : ℝ)) ξ ∂γ =
        gaussianPDFReal 0 1 v₀ := by
      rw [← hmom1, ← integral_indicator measurableSet_Ici]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      by_cases h : ξ ∈ Ici v₀ <;> simp [h]
    rw [← hlim_eq]
    refine tendsto_integral_of_dominated_convergence (fun ξ => |ξ|)
      (fun n => (measurable_id.mul
        ((hmono n).measurable.comp (by fun_prop)).exp).aestronglyMeasurable)
      ((memLp_id_gaussianReal 1).abs.integrable le_rfl)
      (fun n => ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 n _)))
      (hpt.mono fun ξ hξ => hξ.const_mul ξ)
  have hN2 : Tendsto (fun n => ∫ ξ, (ξ ^ 2 - 1) * Real.exp (u n (y n + c n * ξ)) ∂γ) atTop
      (𝓝 (v₀ * gaussianPDFReal 0 1 v₀)) := by
    have hlim_eq : ∫ ξ, (ξ ^ 2 - 1) * (Ici v₀).indicator (fun _ => (1 : ℝ)) ξ ∂γ =
        v₀ * gaussianPDFReal 0 1 v₀ := by
      rw [← hmom2, ← integral_indicator measurableSet_Ici]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      by_cases h : ξ ∈ Ici v₀ <;> simp [h]
    rw [← hlim_eq]
    refine tendsto_integral_of_dominated_convergence (fun ξ => ξ ^ 2 + 1)
      (fun n => (((measurable_id.pow_const 2).sub measurable_const).mul
        ((hmono n).measurable.comp (by fun_prop)).exp).aestronglyMeasurable)
      (((memLp_id_gaussianReal 2).integrable_sq).add (integrable_const 1))
      (fun n => ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        refine (mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 n _))).trans ?_
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _), abs_one]))
      (hpt.mono fun ξ hξ => hξ.const_mul (ξ ^ 2 - 1))
  have hZpos : γ.real (Ici v₀) ≠ 0 := (measureReal_gaussianReal_Ici_pos v₀).ne'
  have hci : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 c₀⁻¹) := hc.inv₀ hc₀.ne'
  constructor
  · have h := hci.mul (hN1.div hZ hZpos)
    exact h.congr fun n => by simp [mul_div_assoc]
  · have h := (hci.pow 2).mul (hN2.div hZ hZpos)
    have hlim : c₀⁻¹ ^ 2 * (v₀ * gaussianPDFReal 0 1 v₀ / γ.real (Ici v₀)) =
        c₀⁻¹ ^ 2 * (v₀ * mills v₀) := by ring
    rw [hlim] at h
    exact h.congr fun n => by simp [mul_div_assoc]

/-- **Pointwise bound on `|W_n|` from `|V_n|` and `W_n ≤ V_n²`:** for concave `u ≤ 0` with bounded
first two derivatives, `W_n(y) ≤ V_n(y)²` and `W_n(y) ≥ -c⁻²` (from `ξ² - 1 ≥ -1`), so
`|W_n(y)| ≤ V_n(y)² + c⁻²`. -/
private theorem abs_W_le_sq_V_add_inv_sq {u : ℝ → ℝ} (huc : ConcaveOn ℝ univ u)
    (hu0 : ∀ x, u x ≤ 0) (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    {D D₂ c : ℝ} (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (hc : 0 < c) (y : ℝ) :
    let Z := ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
    let V := (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z
    let W := (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
      Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z
    |W| ≤ V ^ 2 + c⁻¹ ^ 2 := by
  intro Z V W
  have hum : Measurable u := hu1.continuous.measurable
  have hZ0 : 0 < Z := integral_exp_comp_add_gaussianReal_pos hum hu0 y c
  have hupper : W ≤ V ^ 2 :=
    integral_deriv_two_add_sq_mul_exp_div_le_sq huc hu1 hu2 hD hD₂ y c
  have hlower : -(c⁻¹ ^ 2) ≤ W := by
    dsimp only [W]
    rw [integral_deriv_two_add_sq_mul_exp_eq_inv_sq_mul hu1 hu2 hu0 hD hD₂ hc y, mul_div_assoc]
    have hge : -Z ≤ ∫ ξ, (ξ ^ 2 - 1) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
      have hexp_i : Integrable (fun ξ => Real.exp (u (y + c * ξ))) (gaussianReal 0 1) :=
        integrable_exp_comp_add_gaussianReal hum hu0 y c
      have hnum_i : Integrable (fun ξ => (ξ ^ 2 - 1) * Real.exp (u (y + c * ξ)))
          (gaussianReal 0 1) := by
        have hdom : Integrable (fun ξ : ℝ => ξ ^ 2 + 1) (gaussianReal 0 1) :=
          ((memLp_id_gaussianReal 2).integrable_sq).add (integrable_const 1)
        refine hdom.mono' (((measurable_id.pow_const 2).sub measurable_const).mul
          (hum.comp (by fun_prop)).exp).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        refine (mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))).trans ?_
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _), abs_one])
      rw [← integral_neg]
      refine integral_mono hexp_i.neg hnum_i fun ξ => ?_
      have := Real.exp_pos (u (y + c * ξ))
      nlinarith [sq_nonneg ξ]
    have hdiv : -1 ≤ (∫ ξ, (ξ ^ 2 - 1) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z := by
      rw [le_div_iff₀ hZ0]; linarith
    have := mul_le_mul_of_nonneg_left hdiv (sq_nonneg c⁻¹)
    linarith
  rw [abs_le]
  constructor <;> linarith [sq_nonneg V, sq_nonneg c⁻¹]

/-- **The partial derivative in `ρ` of `F (q, ρ)` at fixed `q < ρ`:**
`2 ∂F/∂ρ = α 𝔼[v mills(v)] / (ρ - q) - q / (ρ - q)² + (ρ - q)⁻¹ - 2 κ + h²`,
where `v(z) = (τ - √q z) / √(ρ - q)`. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_self_fixed (α κ h τ : ℝ) {q ρ : ℝ}
    (hqρ : q < ρ) :
    HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ q ρ')
      ((α * (∫ z, ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)) *
            mills ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)) ∂(gaussianReal 0 1)) / (ρ - q) -
          q / (ρ - q) ^ 2 + (ρ - q)⁻¹ - 2 * κ + h ^ 2) / 2) ρ := by
  have hs₀ : 0 < ρ - q := sub_pos.2 hqρ
  have hc₀ : 0 < Real.sqrt (ρ - q) := Real.sqrt_pos.2 hs₀
  set m : ℝ → ℝ := fun ρ' => τ / Real.sqrt (ρ' - q)
  set σ : ℝ → ℝ := fun ρ' => -Real.sqrt q / Real.sqrt (ρ' - q)
  set m' : ℝ → ℝ := fun ρ' => -(τ / (2 * (ρ' - q) * Real.sqrt (ρ' - q)))
  set σ' : ℝ → ℝ := fun ρ' => Real.sqrt q / (2 * (ρ' - q) * Real.sqrt (ρ' - q))
  have hmd : ∀ᶠ ρ' in 𝓝 ρ, HasDerivAt m (m' ρ') ρ' := by
    filter_upwards [eventually_gt_nhds hqρ] with ρ' hρ'
    have hs' : 0 < ρ' - q := sub_pos.2 hρ'
    have h1 := ((hasDerivAt_id ρ').sub_const q).sqrt hs'.ne'
    have h2 := (hasDerivAt_const ρ' τ).div h1 (Real.sqrt_pos.2 hs').ne'
    refine h2.congr_deriv ?_
    dsimp only [m', id_eq]; rw [Real.sq_sqrt hs'.le]; field_simp; ring
  have hσd : ∀ᶠ ρ' in 𝓝 ρ, HasDerivAt σ (σ' ρ') ρ' := by
    filter_upwards [eventually_gt_nhds hqρ] with ρ' hρ'
    have hs' : 0 < ρ' - q := sub_pos.2 hρ'
    have h1 := ((hasDerivAt_id ρ').sub_const q).sqrt hs'.ne'
    have h2 := (hasDerivAt_const ρ' (-Real.sqrt q)).div h1 (Real.sqrt_pos.2 hs').ne'
    refine h2.congr_deriv ?_
    dsimp only [σ', id_eq]; rw [Real.sq_sqrt hs'.le]; field_simp; ring
  have hmc : ContinuousAt m' ρ := by
    refine (continuousAt_const.div (by fun_prop) ?_).neg
    exact mul_ne_zero (mul_ne_zero two_ne_zero hs₀.ne') hc₀.ne'
  have hσc : ContinuousAt σ' ρ := by
    refine continuousAt_const.div (by fun_prop) ?_
    exact mul_ne_zero (mul_ne_zero two_ne_zero hs₀.ne') hc₀.ne'
  have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := σ) (m' := m') (σ' := σ')
    (t := ρ) hmd hσd hmc hσc
  have hrest : HasDerivAt (fun ρ' => q / (2 * (ρ' - q)) + Real.log (ρ' - q) / 2 - κ * ρ' +
      h ^ 2 * (ρ' - q) / 2)
      (-(q / (2 * (ρ - q) ^ 2)) + (ρ - q)⁻¹ / 2 - κ + h ^ 2 / 2) ρ := by
    have hsub : HasDerivAt (fun ρ' : ℝ => ρ' - q) 1 ρ := (hasDerivAt_id ρ).sub_const q
    have h1 := (hasDerivAt_const ρ q).div (hsub.const_mul 2) (by positivity)
    have h2 := (hsub.log hs₀.ne').div_const 2
    have h3 := (hasDerivAt_id ρ).const_mul κ
    have h4 := (hsub.const_mul (h ^ 2)).div_const 2
    refine (((h1.add h2).sub h3).add h4).congr_deriv ?_
    field_simp; ring
  have hsum := (hE.const_mul α).add hrest
  have heq : (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ q ρ') =ᶠ[𝓝 ρ]
      fun ρ' => α * (∫ z, Real.log ((gaussianReal 0 1).real (Ici (m ρ' + σ ρ' * z)))
          ∂(gaussianReal 0 1)) +
        (q / (2 * (ρ' - q)) + Real.log (ρ' - q) / 2 - κ * ρ' + h ^ 2 * (ρ' - q) / 2) := by
    filter_upwards [eventually_gt_nhds hqρ] with ρ' hρ'
    unfold shcherbinaTirozziHardFunctional
    have harg : ∀ z, (τ - Real.sqrt q * z) / Real.sqrt (ρ' - q) = m ρ' + σ ρ' * z :=
      fun z => by dsimp only [m, σ]; ring
    simp_rw [harg]
    ring
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  have hint_eq : ∫ z, -(mills (m ρ + σ ρ * z)) * (m' ρ + σ' ρ * z) ∂(gaussianReal 0 1) =
      (∫ z, ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)) *
        mills ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)) ∂(gaussianReal 0 1)) /
        (2 * (ρ - q)) := by
    rw [← integral_div]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    have h1 : m ρ + σ ρ * z = (τ - Real.sqrt q * z) / Real.sqrt (ρ - q) := by
      dsimp only [m, σ]; ring
    rw [h1]
    dsimp only [m', σ']
    field_simp [hs₀.ne', hc₀.ne']
    ring
  rw [hint_eq]
  set I := ∫ z, ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)) *
    mills ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)) ∂(gaussianReal 0 1)
  field_simp [hs₀.ne']
  ring

/-- **Soft-to-hard limit of the RS equations:** along a sequence of smooth concave potentials
`u_n ≤ 0` vanishing on `[τ, ∞)` with `exp (u_n (τ - ε_n)) ≤ ε_n → 0`, if
`(α_n, κ_n, h_n, q_n, ρ_n) → (α, κ, h, q, ρ)` with `0 ≤ α`, `0 < κ`, `0 ≤ q < ρ`, and each
`(q_n, ρ_n)` solves the soft RS equations (3.69), (3.76), (3.77) for `u_n`, then `(q, ρ)` is a
critical point of `shcherbinaTirozziHardFunctional α κ h τ` (one-sided in `q` at `q = 0`). -/
theorem isCritical_shcherbinaTirozziHardFunctional_of_tendsto_soft
    {α κ h q ρ r rBar : ℕ → ℝ} {u : ℕ → ℝ → ℝ} {D D₂ ε : ℕ → ℝ}
    {α₀ κ₀ h₀ q₀ ρ₀ τ : ℝ} (hqρ₀ : q₀ < ρ₀)
    (hαn : ∀ n, 0 ≤ α n) (huc : ∀ n, ConcaveOn ℝ univ (u n)) (hu0 : ∀ n x, u n x ≤ 0)
    (huτ : ∀ n x, τ ≤ x → u n x = 0) (hu1 : ∀ n, Differentiable ℝ (u n))
    (hu2 : ∀ n, Differentiable ℝ (deriv (u n))) (hD : ∀ n x, |deriv (u n) x| ≤ D n)
    (hD₂ : ∀ n x, |deriv (deriv (u n)) x| ≤ D₂ n)
    (huε : ∀ n, Real.exp (u n (τ - ε n)) ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (hα_lim : Tendsto α atTop (𝓝 α₀)) (hκ_lim : Tendsto κ atTop (𝓝 κ₀))
    (hh_lim : Tendsto h atTop (𝓝 h₀)) (hq_lim : Tendsto q atTop (𝓝 q₀))
    (hρ_lim : Tendsto ρ atTop (𝓝 ρ₀))
    (hr_eq : ∀ n,
      let Z := fun y => ∫ ξ, Real.exp (u n (y + Real.sqrt (ρ n - q n) * ξ)) ∂(gaussianReal 0 1)
      let V := fun y => (∫ ξ, deriv (u n) (y + Real.sqrt (ρ n - q n) * ξ) *
        Real.exp (u n (y + Real.sqrt (ρ n - q n) * ξ)) ∂(gaussianReal 0 1)) / Z y
      r n = α n * ∫ z, V (Real.sqrt (q n) * z) ^ 2 ∂(gaussianReal 0 1))
    (hrBar_eq : ∀ n,
      let Z := fun y => ∫ ξ, Real.exp (u n (y + Real.sqrt (ρ n - q n) * ξ)) ∂(gaussianReal 0 1)
      let W := fun y => (∫ ξ, (deriv (deriv (u n)) (y + Real.sqrt (ρ n - q n) * ξ) +
        deriv (u n) (y + Real.sqrt (ρ n - q n) * ξ) ^ 2) *
        Real.exp (u n (y + Real.sqrt (ρ n - q n) * ξ)) ∂(gaussianReal 0 1)) / Z y
      rBar n = α n * ∫ z, W (Real.sqrt (q n) * z) ∂(gaussianReal 0 1))
    (hρ_eq : ∀ n, ρ n = (2 * κ n + r n - rBar n)⁻¹ +
      (r n + h n ^ 2) / (2 * κ n + r n - rBar n) ^ 2)
    (hq_eq : ∀ n, q n = (r n + h n ^ 2) / (2 * κ n + r n - rBar n) ^ 2) :
    HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α₀ κ₀ h₀ τ q' ρ₀) 0 (Ici 0) q₀ ∧
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α₀ κ₀ h₀ τ q₀ ρ') 0 ρ₀ := by
  set c₀ : ℝ := Real.sqrt (ρ₀ - q₀)
  have hs₀ : 0 < ρ₀ - q₀ := sub_pos.2 hqρ₀
  have hc₀ : 0 < c₀ := Real.sqrt_pos.2 hs₀
  set c : ℕ → ℝ := fun n => Real.sqrt (ρ n - q n)
  have hc_lim : Tendsto c atTop (𝓝 c₀) := (hρ_lim.sub hq_lim).sqrt
  have hc_pos : ∀ᶠ n in atTop, c₀ / 2 < c n := hc_lim.eventually (Ioi_mem_nhds (half_lt_self hc₀))
  have hq_nn : ∀ n, 0 ≤ q n := fun n => by
    rw [hq_eq n]
    have hr0 : 0 ≤ r n := by
      rw [hr_eq n]; exact mul_nonneg (hαn n) (integral_nonneg fun _ => sq_nonneg _)
    exact div_nonneg (add_nonneg hr0 (sq_nonneg _)) (sq_nonneg _)
  have hq₀ : 0 ≤ q₀ := ge_of_tendsto hq_lim (Eventually.of_forall hq_nn)
  have hsq_lim : Tendsto (fun n => Real.sqrt (q n)) atTop (𝓝 (Real.sqrt q₀)) := hq_lim.sqrt
  have hsq_ub : ∀ᶠ n in atTop, Real.sqrt (q n) ≤ Real.sqrt q₀ + 1 :=
    hsq_lim.eventually (Iic_mem_nhds (by linarith))
  have hmono : ∀ n, Monotone (u n) := fun n =>
    monotone_of_deriv_nonneg (hu1 n) ((huc n).deriv_nonneg_of_forall_ge_eq (hu1 n) (huτ n))
  -- Universal Lemma 3.3.8 bound for dominating `V_n²` and `|W_n|`
  obtain ⟨L, hL0, h338⟩ := exists_sq_mul_integral_deriv_mul_exp_div_le
  set M_c : ℝ := (c₀ / 2)⁻¹
  have hMc0 : 0 < M_c := inv_pos.2 (half_pos hc₀)
  set B_V : ℝ → ℝ := fun z =>
    M_c ^ 2 * ((M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|)) ^ 2 + L)
  set B_dom : ℝ → ℝ := fun z => B_V z + M_c ^ 2
  have hB_int : Integrable B_dom (gaussianReal 0 1) := by
    have hid : MemLp (fun z : ℝ => |z|) 2 (gaussianReal 0 1) := (memLp_id_gaussianReal 2).abs
    have hlin : MemLp (fun z : ℝ => M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|)) 2 (gaussianReal 0 1) :=
      ((memLp_const |τ|).add (hid.const_mul _)).const_mul M_c
    exact ((hlin.integrable_sq.add (integrable_const L)).const_mul (M_c ^ 2)).add
      (integrable_const (M_c ^ 2))
  -- Define the soft `V_n`, `W_n`
  let Z_n (n : ℕ) (y : ℝ) : ℝ :=
    ∫ ξ, Real.exp (u n (y + c n * ξ)) ∂(gaussianReal 0 1)
  let V_n (n : ℕ) (y : ℝ) : ℝ :=
    (∫ ξ, deriv (u n) (y + c n * ξ) * Real.exp (u n (y + c n * ξ)) ∂(gaussianReal 0 1)) / Z_n n y
  let W_n (n : ℕ) (y : ℝ) : ℝ :=
    (∫ ξ, (deriv (deriv (u n)) (y + c n * ξ) + deriv (u n) (y + c n * ξ) ^ 2) *
      Real.exp (u n (y + c n * ξ)) ∂(gaussianReal 0 1)) / Z_n n y
  have hV_dom0 : ∀ᶠ n in atTop, ∀ z : ℝ, V_n n (Real.sqrt (q n) * z) ^ 2 ≤ B_V z := by
    filter_upwards [hc_pos, hsq_ub] with n hcn hqn z
    have hcn0 : 0 < c n := (half_pos hc₀).trans hcn
    have hinv_le : (c n)⁻¹ ≤ M_c := inv_anti₀ (half_pos hc₀) hcn.le
    have h3 := h338 (u n) (hu1 n) (hmono n) (hu0 n) τ (huτ n) (D n) (hD n) (c n) hcn0
      (Real.sqrt (q n) * z)
    rw [mul_div_assoc] at h3
    have hV2 : V_n n (Real.sqrt (q n) * z) ^ 2 ≤
        (c n)⁻¹ ^ 2 * (max ((τ - Real.sqrt (q n) * z) / c n) 0 ^ 2 + L) := by
      have hmul : (c n * V_n n (Real.sqrt (q n) * z)) ^ 2 =
          c n ^ 2 * V_n n (Real.sqrt (q n) * z) ^ 2 := mul_pow _ _ 2
      rw [hmul] at h3
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (c n)⁻¹)
      have hc2 : (c n)⁻¹ ^ 2 * c n ^ 2 = 1 := by field_simp [hcn0.ne']
      linarith [show (c n)⁻¹ ^ 2 * (c n ^ 2 * V_n n (Real.sqrt (q n) * z) ^ 2) =
        V_n n (Real.sqrt (q n) * z) ^ 2 by linear_combination V_n n (Real.sqrt (q n) * z) ^ 2 * hc2]
    have hmax : max ((τ - Real.sqrt (q n) * z) / c n) 0 ≤
        M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|) := by
      refine max_le ?_ (by positivity)
      rw [div_eq_inv_mul]
      have h1 : τ - Real.sqrt (q n) * z ≤ |τ| + (Real.sqrt q₀ + 1) * |z| := by
        have := neg_abs_le (Real.sqrt (q n) * z)
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at this
        nlinarith [abs_nonneg z, le_abs_self τ]
      refine (mul_le_mul_of_nonneg_left h1 (inv_pos.2 hcn0).le).trans ?_
      exact mul_le_mul_of_nonneg_right hinv_le (by positivity)
    have hmax2 : max ((τ - Real.sqrt (q n) * z) / c n) 0 ^ 2 ≤
        (M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|)) ^ 2 :=
      pow_le_pow_left₀ (le_max_right _ _) hmax 2
    have hinv2 : (c n)⁻¹ ^ 2 ≤ M_c ^ 2 := pow_le_pow_left₀ (inv_pos.2 hcn0).le hinv_le 2
    refine hV2.trans ?_
    dsimp only [B_V]
    nlinarith [sq_nonneg (M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|))]
  have hV_dom : ∀ᶠ n in atTop, ∀ z : ℝ, V_n n (Real.sqrt (q n) * z) ^ 2 ≤ B_dom z :=
    hV_dom0.mono fun n hn z => (hn z).trans (le_add_of_nonneg_right (sq_nonneg M_c))
  have hW_dom : ∀ᶠ n in atTop, ∀ z : ℝ, |W_n n (Real.sqrt (q n) * z)| ≤ B_dom z := by
    filter_upwards [hc_pos, hV_dom0] with n hcn hVn z
    have hcn0 : 0 < c n := (half_pos hc₀).trans hcn
    have hinv_le : (c n)⁻¹ ≤ M_c := inv_anti₀ (half_pos hc₀) hcn.le
    have hinv2 : (c n)⁻¹ ^ 2 ≤ M_c ^ 2 := pow_le_pow_left₀ (inv_pos.2 hcn0).le hinv_le 2
    have hW := abs_W_le_sq_V_add_inv_sq (huc n) (hu0 n) (hu1 n) (hu2 n) (hD n) (hD₂ n) hcn0
      (Real.sqrt (q n) * z)
    dsimp only [B_dom]
    linarith [hVn z]
  -- Limits of `r n` and `rBar n` via DCT
  set v_arg : ℝ → ℝ := fun z => (τ - Real.sqrt q₀ * z) / c₀
  have hr_lim : Tendsto r atTop
      (𝓝 (α₀ * ∫ z, (c₀⁻¹ * mills (v_arg z)) ^ 2 ∂(gaussianReal 0 1))) := by
    have hI : Tendsto (fun n => ∫ z, V_n n (Real.sqrt (q n) * z) ^ 2 ∂(gaussianReal 0 1)) atTop
        (𝓝 (∫ z, (c₀⁻¹ * mills (v_arg z)) ^ 2 ∂(gaussianReal 0 1))) := by
      refine tendsto_integral_filter_of_dominated_convergence B_dom
        (Eventually.of_forall fun n =>
          ((measurable_integral_mul_exp_comp_add_div (hu1 n).continuous.measurable
            (measurable_deriv (u n)) (by fun_prop) (c n)).pow_const 2).aestronglyMeasurable)
        (hV_dom.mono fun n hn => ae_of_all _ fun z => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hn z)
        hB_int (ae_of_all _ fun z => ?_)
      have h1 := (tendsto_soft_gaussian_ratios hc₀ hmono hu0 huτ huε hε
        (hsq_lim.mul_const z) hc_lim).1
      refine (h1.pow 2).congr' ?_
      filter_upwards [hc_pos] with n hcn
      have hcn0 : 0 < c n := (half_pos hc₀).trans hcn
      dsimp only [V_n, Z_n]
      rw [integral_deriv_mul_exp_eq_inv_mul_integral_id (hu1 n) (hu0 n) (hD n) hcn0]
    exact (hα_lim.mul hI).congr fun n => (hr_eq n).symm
  have hrBar_lim : Tendsto rBar atTop
      (𝓝 (α₀ * ∫ z, c₀⁻¹ ^ 2 * (v_arg z * mills (v_arg z)) ∂(gaussianReal 0 1))) := by
    have hI : Tendsto (fun n => ∫ z, W_n n (Real.sqrt (q n) * z) ∂(gaussianReal 0 1)) atTop
        (𝓝 (∫ z, c₀⁻¹ ^ 2 * (v_arg z * mills (v_arg z)) ∂(gaussianReal 0 1))) := by
      refine tendsto_integral_filter_of_dominated_convergence B_dom
        (Eventually.of_forall fun n =>
          (measurable_integral_mul_exp_comp_add_div (hu1 n).continuous.measurable
            ((measurable_deriv (deriv (u n))).add ((measurable_deriv (u n)).pow_const 2))
            (by fun_prop) (c n)).aestronglyMeasurable)
        (hW_dom.mono fun n hn => ae_of_all _ fun z => by
          rw [Real.norm_eq_abs]; exact hn z)
        hB_int (ae_of_all _ fun z => ?_)
      have h2 := (tendsto_soft_gaussian_ratios hc₀ hmono hu0 huτ huε hε
        (hsq_lim.mul_const z) hc_lim).2
      refine h2.congr' ?_
      filter_upwards [hc_pos] with n hcn
      have hcn0 : 0 < c n := (half_pos hc₀).trans hcn
      dsimp only [W_n, Z_n]
      rw [integral_deriv_two_add_sq_mul_exp_eq_inv_sq_mul (hu1 n) (hu2 n) (hu0 n) (hD n) (hD₂ n)
        hcn0]
    exact (hα_lim.mul hI).congr fun n => (hrBar_eq n).symm
  -- Pass to the limit in `ρ_n - q_n = d_n⁻¹` and `q_n = (r_n + h_n²) / d_n²`
  set r₀ : ℝ := α₀ * ∫ z, (c₀⁻¹ * mills (v_arg z)) ^ 2 ∂(gaussianReal 0 1)
  set rBar₀ : ℝ := α₀ * ∫ z, c₀⁻¹ ^ 2 * (v_arg z * mills (v_arg z)) ∂(gaussianReal 0 1)
  set d₀ : ℝ := 2 * κ₀ + r₀ - rBar₀
  have hd_lim : Tendsto (fun n => 2 * κ n + r n - rBar n) atTop (𝓝 d₀) :=
    ((hκ_lim.const_mul 2).add hr_lim).sub hrBar_lim
  have hd_eq (n : ℕ) : 2 * κ n + r n - rBar n = (ρ n - q n)⁻¹ := by
    have hgap : ρ n - q n = (2 * κ n + r n - rBar n)⁻¹ := by linarith [hρ_eq n, hq_eq n]
    rw [hgap, inv_inv]
  have hd₀_eq : d₀ = (ρ₀ - q₀)⁻¹ :=
    tendsto_nhds_unique hd_lim
      (((hρ_lim.sub hq_lim).inv₀ hs₀.ne').congr fun n => (hd_eq n).symm)
  have hd₀_pos : 0 < d₀ := by rw [hd₀_eq]; exact inv_pos.2 hs₀
  have hq0_eq : q₀ = (r₀ + h₀ ^ 2) / d₀ ^ 2 := by
    have h2 : Tendsto (fun n => (r n + h n ^ 2) / (2 * κ n + r n - rBar n) ^ 2) atTop
        (𝓝 ((r₀ + h₀ ^ 2) / d₀ ^ 2)) :=
      (hr_lim.add (hh_lim.pow 2)).div (hd_lim.pow 2) (pow_ne_zero 2 hd₀_pos.ne')
    exact tendsto_nhds_unique (hq_lim.congr hq_eq) h2
  -- Simplify `r₀` and `rBar₀` and identify `∂F/∂q = 0` and `∂F/∂ρ = 0`
  have hr₀_eq : r₀ = α₀ * (∫ z, mills (v_arg z) ^ 2 ∂(gaussianReal 0 1)) / (ρ₀ - q₀) := by
    dsimp only [r₀]
    have h1 : ∀ z, (c₀⁻¹ * mills (v_arg z)) ^ 2 = (ρ₀ - q₀)⁻¹ * mills (v_arg z) ^ 2 := fun z => by
      rw [mul_pow, inv_pow, Real.sq_sqrt hs₀.le]
    simp_rw [h1, integral_const_mul]
    ring
  have hrBar₀_eq : rBar₀ = α₀ * (∫ z, v_arg z * mills (v_arg z) ∂(gaussianReal 0 1)) /
      (ρ₀ - q₀) := by
    dsimp only [rBar₀]
    have h1 : ∀ z, c₀⁻¹ ^ 2 * (v_arg z * mills (v_arg z)) =
        (ρ₀ - q₀)⁻¹ * (v_arg z * mills (v_arg z)) := fun z => by
      rw [inv_pow, Real.sq_sqrt hs₀.le]
    simp_rw [h1, integral_const_mul]
    ring
  have hq_stat : q₀ / (ρ₀ - q₀) ^ 2 - r₀ - h₀ ^ 2 = 0 := by
    have h1 : q₀ * d₀ ^ 2 = r₀ + h₀ ^ 2 := by
      rw [hq0_eq, div_mul_cancel₀ _ (pow_ne_zero 2 hd₀_pos.ne')]
    rw [hd₀_eq, inv_pow, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 hs₀.ne')] at h1
    rw [div_eq_mul_inv]
    have : q₀ * ((ρ₀ - q₀) ^ 2)⁻¹ = r₀ + h₀ ^ 2 := by
      rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 hs₀.ne')]; exact h1
    linarith
  have hρ_stat : (ρ₀ - q₀)⁻¹ - 2 * κ₀ - r₀ + rBar₀ = 0 := by
    linarith [hd₀_eq]
  -- Now verify `HasDerivWithinAt (F · ρ₀) 0 (Ici 0) q₀` and `HasDerivAt (F q₀ ·) 0 ρ₀`
  have hv_arg_eq : ∀ z, v_arg z = τ / Real.sqrt (ρ₀ - q₀) +
      -Real.sqrt q₀ / Real.sqrt (ρ₀ - q₀) * z := fun z => by
    dsimp only [v_arg, c₀]; ring
  have hρ₀_pos : 0 < ρ₀ := hq₀.trans_lt hqρ₀
  constructor
  · rcases hq₀.eq_or_lt with rfl | hq_pos
    · -- Boundary `q₀ = 0`: `r₀ + h₀² = 0`
      have hderiv :=
        hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero α₀ κ₀ h₀ τ hρ₀_pos
      refine hderiv.congr_deriv ?_
      have hv0 : ∀ z, v_arg z = τ / Real.sqrt ρ₀ := fun z => by
        dsimp only [v_arg, c₀]; simp
      simp_rw [hv0, integral_const, probReal_univ, one_smul, sub_zero] at hr₀_eq
      rw [zero_div, zero_sub] at hq_stat
      linarith
    · -- Interior `0 < q₀ < ρ₀`
      have hderiv := hasDerivAt_shcherbinaTirozziHardFunctional_overlap α₀ κ₀ h₀ τ hq_pos hqρ₀
      refine hderiv.hasDerivWithinAt.congr_deriv ?_
      simp_rw [← hv_arg_eq]
      rw [← hr₀_eq]
      linarith
  · have hderiv := hasDerivAt_shcherbinaTirozziHardFunctional_self_fixed α₀ κ₀ h₀ τ hqρ₀
    refine hderiv.congr_deriv ?_
    rw [← hrBar₀_eq]
    linarith [hq_stat, hρ_stat]

/-- **Uniform a priori bounds for hard RS critical points:** for `0 < κ₀`, `α₀ < 2`, `τ ≥ 0`,
there is `C` (depending only on `κ₀, κ₁, α₀, h₀, τ`) such that every hard critical point
`0 ≤ q₀ < ρ₀` of `shcherbinaTirozziHardFunctional α κ h τ` with `0 ≤ α ≤ α₀`, `κ₀ ≤ κ ≤ κ₁`,
`|h| ≤ h₀` satisfies `q₀ ≤ C`, `ρ₀ ≤ C`, and `(ρ₀ - q₀)⁻¹ ≤ C`. -/
theorem exists_bound_of_shcherbinaTirozziHardFunctional_critical (κ₀ κ₁ α₀ h₀ τ : ℝ)
    (hκ₀ : 0 < κ₀) (hα₀ : α₀ < 2) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, ∀ (α κ h q₀ ρ₀ : ℝ), 0 ≤ α → α ≤ α₀ → κ₀ ≤ κ → κ ≤ κ₁ → |h| ≤ h₀ →
      0 ≤ q₀ → q₀ < ρ₀ →
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α κ h τ q' ρ₀) 0 (Ici 0) q₀ →
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ q₀ ρ') 0 ρ₀ →
      q₀ ≤ C ∧ ρ₀ ≤ C ∧ (ρ₀ - q₀)⁻¹ ≤ C := by
  set α₁ : ℝ := max α₀ 1
  have hα₁2 : α₁ < 2 := max_lt hα₀ one_lt_two
  have hα₁0 : 0 < α₁ := one_pos.trans_le (le_max_right _ _)
  obtain ⟨a, δ, ha0, haα, hδ0, hδ⟩ := exists_slope_lt_inv_and_threshold hα₁0 hα₁2
  set L_m : ℝ := max 3 ((gaussianPDFReal 0 1 1 / (gaussianReal 0 1).real (Ici 1)) ^ 2 + 1)
  have hLm0 : 0 ≤ L_m := le_trans (by norm_num) (le_max_left _ _)
  have hmills_sq : ∀ v : ℝ, mills v ^ 2 ≤ max v 0 ^ 2 + L_m := fun v => by
    rcases le_total v 1 with hv | hv
    · have hm := monotone_gaussianPDFReal_div_measureReal_Ici hv
      have hsq : mills v ^ 2 ≤ (gaussianPDFReal 0 1 1 / (gaussianReal 0 1).real (Ici 1)) ^ 2 :=
        pow_le_pow_left₀ (gaussianPDFReal_div_measureReal_Ici_nonneg v) hm 2
      have hL : (gaussianPDFReal 0 1 1 / (gaussianReal 0 1).real (Ici 1)) ^ 2 ≤ L_m :=
        (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
      linarith [sq_nonneg (max v 0)]
    · have hv0 : 0 < v := one_pos.trans_le hv
      have h1 : mills v ≤ v + v⁻¹ := by
        rw [div_le_iff₀ (measureReal_gaussianReal_Ici_pos v)]
        refine le_of_mul_le_mul_left ((mul_gaussianPDFReal_le_one_add_sq_mul v).trans_eq ?_) hv0
        field_simp [hv0.ne']; ring
      have h2 : mills v ^ 2 ≤ (v + v⁻¹) ^ 2 :=
        pow_le_pow_left₀ (gaussianPDFReal_div_measureReal_Ici_nonneg v) h1 2
      have h3 : (v + v⁻¹) ^ 2 = v ^ 2 + 2 + v⁻¹ ^ 2 := by field_simp [hv0.ne']; ring
      have h4 : v⁻¹ ^ 2 ≤ 1 := by
        have : v⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hv
        nlinarith [inv_pos.2 hv0]
      have h5 : max v 0 = v := max_eq_left hv0.le
      rw [h5]
      have hL3 : (3 : ℝ) ≤ L_m := le_max_left _ _
      linarith
  set Q : ℝ := max ((τ / δ) ^ 2 + 1)
    ((h₀ ^ 2 / (2 * κ₀) ^ 2 + α₁ * L_m / (2 * κ₀)) / (1 - a * α₁))
  set C₁ : ℝ := 2 * κ₁ / (1 - Real.sqrt (α₁ / 2))
  refine ⟨max (Q + (2 * κ₀)⁻¹) C₁, fun α κ h q₀ ρ₀ hα0 hα hκ hκ1 hh hq₀ hqρ₀ hcq hcρ => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hαα₁ : α ≤ α₁ := hα.trans (le_max_left _ _)
  set s : ℝ := ρ₀ - q₀
  have hs0 : 0 < s := sub_pos.2 hqρ₀
  set c : ℝ := Real.sqrt s
  have hc0 : 0 < c := Real.sqrt_pos.2 hs0
  have hc2 : c ^ 2 = s := Real.sq_sqrt hs0.le
  set v_arg : ℝ → ℝ := fun z => (τ - Real.sqrt q₀ * z) / c
  set r : ℝ := α * (∫ z, mills (v_arg z) ^ 2 ∂(gaussianReal 0 1)) / s
  set rBar : ℝ := α * (∫ z, v_arg z * mills (v_arg z) ∂(gaussianReal 0 1)) / s
  have hq_stat : q₀ / s ^ 2 - r - h ^ 2 = 0 := by
    rcases hq₀.eq_or_lt with rfl | hq_pos
    · have hρ0 : 0 < ρ₀ := hqρ₀
      have h0 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _
        (hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero α κ h τ hρ0) hcq
      have hv0 : ∀ z, v_arg z = τ / Real.sqrt ρ₀ := fun z => by
        dsimp only [v_arg, c, s]; simp
      dsimp only [r, s]
      simp_rw [hv0, integral_const, probReal_univ, one_smul, sub_zero]
      rw [zero_div, zero_sub]
      linarith
    · have h0 := (hcq.hasDerivAt (Ici_mem_nhds hq_pos)).unique
        (hasDerivAt_shcherbinaTirozziHardFunctional_overlap α κ h τ hq_pos hqρ₀)
      have hv_eq : ∀ z, τ / Real.sqrt (ρ₀ - q₀) + -Real.sqrt q₀ / Real.sqrt (ρ₀ - q₀) * z =
          v_arg z := fun z => by dsimp only [v_arg, c, s]; ring
      simp_rw [hv_eq] at h0
      dsimp only [r, s]
      linarith
  have hρ_stat : rBar - q₀ / s ^ 2 + s⁻¹ - 2 * κ + h ^ 2 = 0 := by
    have h0 := hcρ.unique (hasDerivAt_shcherbinaTirozziHardFunctional_self_fixed α κ h τ hqρ₀)
    dsimp only [rBar, v_arg, c, s]
    linarith
  have hs_inv : s⁻¹ = 2 * κ + r - rBar := by linarith
  have hqs : q₀ = (r + h ^ 2) * s ^ 2 := by
    have : q₀ / s ^ 2 = r + h ^ 2 := by linarith
    rw [← this, div_mul_cancel₀ _ (pow_ne_zero 2 hs0.ne')]
  have hr_eq : r = α * ∫ z, (c⁻¹ * mills (v_arg z)) ^ 2 ∂(gaussianReal 0 1) := by
    have h1 : ∀ z, (c⁻¹ * mills (v_arg z)) ^ 2 = s⁻¹ * mills (v_arg z) ^ 2 := fun z => by
      rw [mul_pow, inv_pow, hc2]
    simp_rw [h1, integral_const_mul]
    dsimp only [r]; ring
  have hrr : rBar ≤ r := by
    dsimp only [r, rBar]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hα0) hs0.le
    obtain ⟨hi, hzi, hi2⟩ := integrable_gaussianPDFReal_div_measureReal_Ici_comp
      (τ / c) (-Real.sqrt q₀ / c)
    have hv_eq : ∀ z, τ / c + -Real.sqrt q₀ / c * z = v_arg z := fun z => by
      dsimp only [v_arg]; ring
    simp_rw [hv_eq] at hi hzi hi2
    have hWA : Integrable (fun z => v_arg z * mills (v_arg z)) (gaussianReal 0 1) := by
      refine ((hi.const_mul (τ / c)).add (hzi.const_mul (-Real.sqrt q₀ / c))).congr
        (ae_of_all _ fun z => ?_)
      simp only [Pi.add_apply, v_arg]; ring
    exact integral_mono hWA hi2 fun z =>
      sub_nonneg.1 (hasDerivAt_gaussianPDFReal_div_measureReal_Ici (v_arg z) _ fun _ => rfl).2
  have hsκ : s ≤ (2 * κ₀)⁻¹ := by
    rw [← inv_inv s, hs_inv]
    exact inv_anti₀ (by positivity) (by linarith)
  have hqQ : q₀ ≤ Q := by
    refine q_le_of_replicaSymmetric_equation (V := fun y => c⁻¹ * mills ((τ - y) / c))
      hα0 hαα₁ hα₁0 ha0.le haα hδ0 hδ hτ hLm0 hc0 hc2 hs0 hsκ hh hq₀ hqs (fun y => ?_) hr_eq
    rw [mul_inv_cancel_left₀ hc0.ne']
    exact hmills_sq _
  -- Bound `s⁻¹ = 2 κ + r - rBar` using `r - rBar ≤ √(α / 2) * s⁻¹`
  have hdiff_le : r - rBar ≤ Real.sqrt (α / 2) * s⁻¹ := by
    rcases hα0.eq_or_lt with rfl | hαpos
    · simp [r, rBar]
    rcases hq₀.eq_or_lt with rfl | hq_pos
    · have hv0 : ∀ z, v_arg z = τ / c := fun z => by dsimp only [v_arg]; simp
      have h0 : r + h ^ 2 = 0 := by rw [zero_div] at hq_stat; linarith
      have hr0 : 0 ≤ r := by
        rw [hr_eq]; exact mul_nonneg hαpos.le (integral_nonneg fun _ => sq_nonneg _)
      have hr_zero : r = 0 := by nlinarith [sq_nonneg h]
      dsimp only [r] at hr_zero
      simp_rw [hv0, integral_const, probReal_univ, one_smul] at hr_zero
      have hmills_pos : 0 < mills (τ / c) :=
        div_pos (gaussianPDFReal_pos _ _ _ one_ne_zero) (measureReal_gaussianReal_Ici_pos _)
      have : 0 < α * mills (τ / c) ^ 2 / s := div_pos (mul_pos hαpos (sq_pos_of_pos hmills_pos)) hs0
      linarith
    · -- `q₀ > 0`: use `integral_id_mul_gaussianPDFReal_div_measureReal_Ici_comp`!
      set m_val : ℝ := τ / c
      set σ_val : ℝ := -Real.sqrt q₀ / c
      have hv_eq : ∀ z, m_val + σ_val * z = v_arg z := fun z => by
        dsimp only [m_val, σ_val, v_arg]; ring
      obtain ⟨hi, hzi, hi2⟩ := integrable_gaussianPDFReal_div_measureReal_Ici_comp m_val σ_val
      have hIBP := integral_id_mul_gaussianPDFReal_div_measureReal_Ici_comp m_val σ_val
      simp_rw [hv_eq] at hi hzi hi2 hIBP
      have hWA : Integrable (fun z => v_arg z * mills (v_arg z)) (gaussianReal 0 1) := by
        refine ((hi.const_mul m_val).add (hzi.const_mul σ_val)).congr (ae_of_all _ fun z => ?_)
        simp only [Pi.add_apply, m_val, σ_val, v_arg]; ring
      rw [integral_sub hi2 hWA] at hIBP
      have hdiff_eq : r - rBar = α / (Real.sqrt q₀ * c) *
          (-(∫ z, z * mills (v_arg z) ∂(gaussianReal 0 1))) := by
        have h1 : ∫ z, mills (v_arg z) ^ 2 ∂(gaussianReal 0 1) -
            ∫ z, v_arg z * mills (v_arg z) ∂(gaussianReal 0 1) =
            -(c / Real.sqrt q₀) * ∫ z, z * mills (v_arg z) ∂(gaussianReal 0 1) := by
          have hσ_ne : σ_val ≠ 0 := by
            dsimp only [σ_val]
            exact div_ne_zero (neg_ne_zero.2 (Real.sqrt_pos.2 hq_pos).ne') hc0.ne'
          have : ∫ z, z * mills (v_arg z) ∂(gaussianReal 0 1) =
              σ_val * ((∫ z, mills (v_arg z) ^ 2 ∂(gaussianReal 0 1)) -
                ∫ z, v_arg z * mills (v_arg z) ∂(gaussianReal 0 1)) := hIBP
          dsimp only [σ_val] at this
          have hsq0 : Real.sqrt q₀ ≠ 0 := (Real.sqrt_pos.2 hq_pos).ne'
          field_simp [hsq0, hc0.ne'] at this ⊢
          linarith
        dsimp only [r, rBar]
        rw [← sub_div, ← mul_sub, h1, ← hc2]
        have hsq0 : Real.sqrt q₀ ≠ 0 := (Real.sqrt_pos.2 hq_pos).ne'
        field_simp [hsq0, hc0.ne']
      have hneg : -(∫ z, z * mills (v_arg z) ∂(gaussianReal 0 1)) ≤
          Real.sqrt ((∫ z, mills (v_arg z) ^ 2 ∂(gaussianReal 0 1)) / 2) := by
        have hUL : MemLp (fun z => mills (v_arg z)) 2 (gaussianReal 0 1) :=
          (memLp_two_iff_integrable_sq
            (monotone_gaussianPDFReal_div_measureReal_Ici.measurable.comp
              (by fun_prop)).aestronglyMeasurable).2 hi2
        have hL2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' 2 (by simp)
        refine (neg_integral_id_mul_le_sqrt hL2 hUL fun z =>
          gaussianPDFReal_div_measureReal_Ici_nonneg _).trans_eq ?_
        rw [integral_min_zero_sq_gaussianReal, one_div_mul_eq_div]
      rw [hdiff_eq]
      refine (mul_le_mul_of_nonneg_left hneg (by positivity)).trans ?_
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt hq₀, hc2,
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), inv_pow]
      set I2 : ℝ := ∫ z, mills (v_arg z) ^ 2 ∂(gaussianReal 0 1)
      have hI_eq : α * I2 = r * s := by
        dsimp only [r, I2]; field_simp [hs0.ne']
      have hgoal : α ^ 2 / (q₀ * s) * (I2 / 2) = α / 2 * (r / q₀) := by
        rw [show α ^ 2 / (q₀ * s) * (I2 / 2) = α / (2 * q₀ * s) * (α * I2) by ring_nf, hI_eq]
        field_simp [hq_pos.ne', hs0.ne']
      rw [hgoal]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_iff₀ hq_pos, inv_mul_eq_div, le_div_iff₀ (pow_pos hs0 2)]
      nlinarith [sq_nonneg h, sq_nonneg s, hqs]
  have hs_inv_le : s⁻¹ ≤ C₁ := by
    have hsq2 : Real.sqrt (α₁ / 2) < 1 := by
      rw [Real.sqrt_lt' one_pos, one_pow]; linarith
    have h1 : Real.sqrt (α / 2) * s⁻¹ ≤ Real.sqrt (α₁ / 2) * s⁻¹ :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (inv_nonneg.2 hs0.le)
    rw [le_div_iff₀ (sub_pos.2 hsq2), mul_sub, mul_one, mul_comm s⁻¹]
    linarith
  have hρq : ρ₀ = q₀ + s := by dsimp only [s]; ring
  exact ⟨hqQ.trans ((le_add_of_nonneg_right (by positivity)).trans (le_max_left _ _)),
    hρq ▸ (add_le_add hqQ hsκ).trans (le_max_left _ _),
    hs_inv_le.trans (le_max_right _ _)⟩

/-- **Closedness of the hard RS critical set:** along a converging sequence
`(α_n, κ_n, h_n, q_n, ρ_n) → (α₀, κ₀, h₀, q₀, ρ₀)` with `0 ≤ q₀ < ρ₀`, if each `(q_n, ρ_n)` is a
hard critical point at `(α_n, κ_n, h_n)`, then `(q₀, ρ₀)` is a hard critical point at
`(α₀, κ₀, h₀)`. -/
theorem isCritical_shcherbinaTirozziHardFunctional_of_tendsto_hard
    {α κ h q ρ : ℕ → ℝ} {α₀ κ₀ h₀ q₀ ρ₀ τ : ℝ} (hq₀ : 0 ≤ q₀) (hqρ₀ : q₀ < ρ₀)
    (hqn : ∀ n, 0 ≤ q n) (hqρn : ∀ n, q n < ρ n)
    (hα_lim : Tendsto α atTop (𝓝 α₀)) (hκ_lim : Tendsto κ atTop (𝓝 κ₀))
    (hh_lim : Tendsto h atTop (𝓝 h₀)) (hq_lim : Tendsto q atTop (𝓝 q₀))
    (hρ_lim : Tendsto ρ atTop (𝓝 ρ₀))
    (hcq : ∀ n, HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional (α n) (κ n) (h n) τ q'
      (ρ n)) 0 (Ici 0) (q n))
    (hcρ : ∀ n, HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional (α n) (κ n) (h n) τ (q n)
      ρ') 0 (ρ n)) :
    HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α₀ κ₀ h₀ τ q' ρ₀) 0 (Ici 0) q₀ ∧
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α₀ κ₀ h₀ τ q₀ ρ') 0 ρ₀ := by
  have hs₀ : 0 < ρ₀ - q₀ := sub_pos.2 hqρ₀
  set c₀ : ℝ := Real.sqrt (ρ₀ - q₀)
  have hc₀ : 0 < c₀ := Real.sqrt_pos.2 hs₀
  set c : ℕ → ℝ := fun n => Real.sqrt (ρ n - q n)
  have hc_lim : Tendsto c atTop (𝓝 c₀) := (hρ_lim.sub hq_lim).sqrt
  have hc_pos : ∀ᶠ n in atTop, c₀ / 2 < c n := hc_lim.eventually (Ioi_mem_nhds (half_lt_self hc₀))
  have hsq_lim : Tendsto (fun n => Real.sqrt (q n)) atTop (𝓝 (Real.sqrt q₀)) := hq_lim.sqrt
  have hsq_ub : ∀ᶠ n in atTop, Real.sqrt (q n) ≤ Real.sqrt q₀ + 1 :=
    hsq_lim.eventually (Iic_mem_nhds (by linarith))
  obtain ⟨C_m, hCm0, hCm⟩ := exists_gaussianPDFReal_div_measureReal_Ici_le
  set M_c : ℝ := (c₀ / 2)⁻¹
  have hcm : Continuous fun v : ℝ => mills v :=
    continuous_iff_continuousAt.2 fun v =>
      (hasDerivAt_gaussianPDFReal_div_measureReal_Ici v _ fun _ => rfl).1.continuousAt
  set v_n : ℕ → ℝ → ℝ := fun n z => (τ - Real.sqrt (q n) * z) / c n
  set v₀ : ℝ → ℝ := fun z => (τ - Real.sqrt q₀ * z) / c₀
  have hv_dom : ∀ᶠ n in atTop, ∀ z : ℝ, |v_n n z| ≤ M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|) := by
    filter_upwards [hc_pos, hsq_ub] with n hcn hqn z
    have hcn0 : 0 < c n := (half_pos hc₀).trans hcn
    rw [abs_div, abs_of_pos hcn0, div_eq_inv_mul]
    have h1 : |τ - Real.sqrt (q n) * z| ≤ |τ| + (Real.sqrt q₀ + 1) * |z| := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_right hqn (abs_nonneg z)
    exact mul_le_mul (inv_anti₀ (half_pos hc₀) hcn.le) h1
      (abs_nonneg _) (inv_pos.2 (half_pos hc₀)).le
  set B_dom : ℝ → ℝ := fun z => (C_m + M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|)) ^ 2
  have hB_int : Integrable B_dom (gaussianReal 0 1) := by
    have hid : MemLp (fun z : ℝ => |z|) 2 (gaussianReal 0 1) := (memLp_id_gaussianReal 2).abs
    have hlin : MemLp (fun z : ℝ => C_m + M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|)) 2
        (gaussianReal 0 1) :=
      (memLp_const C_m).add (((memLp_const |τ|).add (hid.const_mul _)).const_mul M_c)
    exact hlin.integrable_sq
  have hI2_lim : Tendsto (fun n => ∫ z, mills (v_n n z) ^ 2 ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ z, mills (v₀ z) ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence B_dom
      (Eventually.of_forall fun n => ((hcm.comp (by fun_prop)).pow 2).aestronglyMeasurable)
      (hv_dom.mono fun n hn => ae_of_all _ fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (gaussianPDFReal_div_measureReal_Ici_nonneg _)
          ((hCm _).trans (add_le_add le_rfl (hn z))) 2)
      hB_int (ae_of_all _ fun z =>
        ((hcm.pow 2).continuousAt.tendsto).comp
          ((tendsto_const_nhds.sub (hsq_lim.mul_const z)).div hc_lim hc₀.ne'))
  have hIv_lim : Tendsto (fun n => ∫ z, v_n n z * mills (v_n n z) ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ z, v₀ z * mills (v₀ z) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence B_dom
      (Eventually.of_forall fun n =>
        (((by fun_prop : Continuous (v_n n)).mul (hcm.comp (by fun_prop))).aestronglyMeasurable))
      (hv_dom.mono fun n hn => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_div_measureReal_Ici_nonneg _)]
        have h1 : |v_n n z| ≤ C_m + M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|) :=
          (hn z).trans (le_add_of_nonneg_left hCm0)
        have h2 : mills (v_n n z) ≤ C_m + M_c * (|τ| + (Real.sqrt q₀ + 1) * |z|) :=
          (hCm _).trans (add_le_add le_rfl (hn z))
        dsimp only [B_dom]
        rw [sq]
        exact mul_le_mul h1 h2 (gaussianPDFReal_div_measureReal_Ici_nonneg _) (by positivity))
      hB_int (ae_of_all _ fun z => by
        have hv : Tendsto (fun n => v_n n z) atTop (𝓝 (v₀ z)) :=
          (tendsto_const_nhds.sub (hsq_lim.mul_const z)).div hc_lim hc₀.ne'
        exact hv.mul (hcm.continuousAt.tendsto.comp hv))
  -- Pass to the limit in `∂F/∂q = 0` and `∂F/∂ρ = 0`
  have hq_stat_n : ∀ n, q n / (ρ n - q n) ^ 2 -
      α n * (∫ z, mills (v_n n z) ^ 2 ∂(gaussianReal 0 1)) / (ρ n - q n) -
      h n ^ 2 = 0 := fun n => by
    rcases (hqn n).eq_or_lt with h0 | hpos
    · have hρn0 : 0 < ρ n := h0 ▸ hqρn n
      have hcq0 : HasDerivWithinAt
          (fun q' => shcherbinaTirozziHardFunctional (α n) (κ n) (h n) τ q' (ρ n))
          0 (Ici 0) 0 := by
        have h := hcq n
        rwa [← h0] at h
      have hd := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _
        (hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero
          (α n) (κ n) (h n) τ hρn0)
        hcq0
      have hv0' : ∀ z, v_n n z = τ / Real.sqrt (ρ n) := fun z => by
        dsimp only [v_n, c]; rw [← h0]; simp
      simp_rw [hv0', integral_const, probReal_univ, one_smul, ← h0, sub_zero, zero_div, zero_sub]
      linarith
    · have hd := ((hcq n).hasDerivAt (Ici_mem_nhds hpos)).unique
        (hasDerivAt_shcherbinaTirozziHardFunctional_overlap (α n) (κ n) (h n) τ hpos (hqρn n))
      have hv_eq : ∀ z, τ / Real.sqrt (ρ n - q n) + -Real.sqrt (q n) / Real.sqrt (ρ n - q n) * z =
          v_n n z := fun z => by dsimp only [v_n, c]; ring
      simp_rw [hv_eq] at hd
      linarith
  have hρ_stat_n : ∀ n, α n * (∫ z, v_n n z * mills (v_n n z) ∂(gaussianReal 0 1)) / (ρ n - q n) -
      q n / (ρ n - q n) ^ 2 + (ρ n - q n)⁻¹ - 2 * κ n + h n ^ 2 = 0 := fun n => by
    have hd := (hcρ n).unique
      (hasDerivAt_shcherbinaTirozziHardFunctional_self_fixed (α n) (κ n) (h n) τ (hqρn n))
    dsimp only [v_n, c]
    linarith
  have hq_stat_0 : q₀ / (ρ₀ - q₀) ^ 2 -
      α₀ * (∫ z, mills (v₀ z) ^ 2 ∂(gaussianReal 0 1)) / (ρ₀ - q₀) - h₀ ^ 2 = 0 := by
    have hlim : Tendsto (fun n => q n / (ρ n - q n) ^ 2 -
        α n * (∫ z, mills (v_n n z) ^ 2 ∂(gaussianReal 0 1)) / (ρ n - q n) - h n ^ 2) atTop
        (𝓝 (q₀ / (ρ₀ - q₀) ^ 2 -
          α₀ * (∫ z, mills (v₀ z) ^ 2 ∂(gaussianReal 0 1)) / (ρ₀ - q₀) - h₀ ^ 2)) :=
      ((hq_lim.div ((hρ_lim.sub hq_lim).pow 2) (pow_ne_zero 2 hs₀.ne')).sub
        ((hα_lim.mul hI2_lim).div (hρ_lim.sub hq_lim) hs₀.ne')).sub (hh_lim.pow 2)
    exact tendsto_nhds_unique (hlim.congr fun n => hq_stat_n n) tendsto_const_nhds
  have hρ_stat_0 : α₀ * (∫ z, v₀ z * mills (v₀ z) ∂(gaussianReal 0 1)) / (ρ₀ - q₀) -
      q₀ / (ρ₀ - q₀) ^ 2 + (ρ₀ - q₀)⁻¹ - 2 * κ₀ + h₀ ^ 2 = 0 := by
    have hlim : Tendsto (fun n => α n * (∫ z, v_n n z * mills (v_n n z) ∂(gaussianReal 0 1)) /
        (ρ n - q n) - q n / (ρ n - q n) ^ 2 + (ρ n - q n)⁻¹ - 2 * κ n + h n ^ 2) atTop
        (𝓝 (α₀ * (∫ z, v₀ z * mills (v₀ z) ∂(gaussianReal 0 1)) / (ρ₀ - q₀) -
          q₀ / (ρ₀ - q₀) ^ 2 + (ρ₀ - q₀)⁻¹ - 2 * κ₀ + h₀ ^ 2)) :=
      (((((hα_lim.mul hIv_lim).div (hρ_lim.sub hq_lim) hs₀.ne').sub
        (hq_lim.div ((hρ_lim.sub hq_lim).pow 2) (pow_ne_zero 2 hs₀.ne'))).add
        ((hρ_lim.sub hq_lim).inv₀ hs₀.ne')).sub (hκ_lim.const_mul 2)).add (hh_lim.pow 2)
    exact tendsto_nhds_unique (hlim.congr fun n => hρ_stat_n n) tendsto_const_nhds
  constructor
  · rcases hq₀.eq_or_lt with rfl | hq_pos
    · have hρ0 : 0 < ρ₀ := hqρ₀
      refine (hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero α₀ κ₀ h₀ τ
        hρ0).congr_deriv ?_
      have hv0' : ∀ z, v₀ z = τ / Real.sqrt ρ₀ := fun z => by dsimp only [v₀, c₀]; simp
      simp_rw [hv0', integral_const, probReal_univ, one_smul, sub_zero, zero_div,
        zero_sub] at hq_stat_0
      linarith
    · refine (hasDerivAt_shcherbinaTirozziHardFunctional_overlap α₀ κ₀ h₀ τ hq_pos
        hqρ₀).hasDerivWithinAt.congr_deriv ?_
      have hv_eq : ∀ z, τ / Real.sqrt (ρ₀ - q₀) + -Real.sqrt q₀ / Real.sqrt (ρ₀ - q₀) * z =
          v₀ z := fun z => by dsimp only [v₀, c₀]; ring
      simp_rw [hv_eq]
      linarith
  · refine (hasDerivAt_shcherbinaTirozziHardFunctional_self_fixed α₀ κ₀ h₀ τ hqρ₀).congr_deriv ?_
    dsimp only [v₀, c₀] at hρ_stat_0
    linarith

/-- **Talagrand, Corollary 3.3.4:** given `0 < κ₀ ≤ κ₁`, `α₀ < 2`, `h₀ ≥ 0`, `τ ≥ 0` and `ε > 0`,
there exists `ε' > 0` such that whenever `u ≤ 0` is smooth and concave, vanishes on `[τ, ∞)` and
satisfies `exp (u (τ - ε')) ≤ ε'`, whenever `0 ≤ α ≤ α₀`, `κ₀ ≤ κ ≤ κ₁`, `|h| ≤ h₀`, and
`(q, ρ)` solves the soft RS equations for `u` while `(q₀, ρ₀)` is a hard RS critical point
(`0 ≤ q₀ < ρ₀`), one has `|q - q₀| ≤ ε` and `|ρ - ρ₀| ≤ ε`. -/
theorem exists_soft_rs_close_to_hard (κ₀ κ₁ α₀ h₀ τ ε : ℝ)
    (hκ₀ : 0 < κ₀) (hα₀ : α₀ < 2) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ∀ (α κ h q ρ r rBar q₀ ρ₀ : ℝ) (u : ℝ → ℝ) (D D₂ : ℝ),
      0 ≤ α → α ≤ α₀ → κ₀ ≤ κ → κ ≤ κ₁ → |h| ≤ h₀ →
      ConcaveOn ℝ univ u → (∀ x, u x ≤ 0) → (∀ x, τ ≤ x → u x = 0) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D₂) →
      Real.exp (u (τ - ε')) ≤ ε' →
      let Z : ℝ → ℝ := fun y =>
        ∫ ξ, Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y => (∫ ξ, deriv u (y + Real.sqrt (ρ - q) * ξ) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ - q) * ξ) +
          deriv u (y + Real.sqrt (ρ - q) * ξ) ^ 2) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      r = α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1) →
      rBar = α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1) →
      ρ = (2 * κ + r - rBar)⁻¹ + (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 →
      q = (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 →
      0 ≤ q₀ → q₀ < ρ₀ →
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α κ h τ q' ρ₀) 0 (Ici 0) q₀ →
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ q₀ ρ') 0 ρ₀ →
      |q - q₀| ≤ ε ∧ |ρ - ρ₀| ≤ ε := by
  by_contra hcon
  push Not at hcon
  -- Choose a sequence of counterexamples with `ε_n = 1 / (n + 1)`
  have hseq : ∀ n : ℕ, ∃ (α κ h q ρ r rBar q₀ ρ₀ : ℝ) (u : ℝ → ℝ) (D D₂ : ℝ),
      0 ≤ α ∧ α ≤ α₀ ∧ κ₀ ≤ κ ∧ κ ≤ κ₁ ∧ |h| ≤ h₀ ∧
      ConcaveOn ℝ univ u ∧ (∀ x, u x ≤ 0) ∧ (∀ x, τ ≤ x → u x = 0) ∧
      Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      (∀ x, |deriv u x| ≤ D) ∧ (∀ x, |deriv (deriv u) x| ≤ D₂) ∧
      Real.exp (u (τ - ((n : ℝ) + 1)⁻¹)) ≤ ((n : ℝ) + 1)⁻¹ ∧
      (let Z := fun y => ∫ ξ, Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)
       let V := fun y => (∫ ξ, deriv u (y + Real.sqrt (ρ - q) * ξ) *
         Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
       let W := fun y => (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ - q) * ξ) +
           deriv u (y + Real.sqrt (ρ - q) * ξ) ^ 2) *
         Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
       r = α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1) ∧
       rBar = α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)) ∧
      ρ = (2 * κ + r - rBar)⁻¹ + (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 ∧
      q = (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 ∧
      0 ≤ q₀ ∧ q₀ < ρ₀ ∧
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α κ h τ q' ρ₀) 0 (Ici 0) q₀ ∧
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ q₀ ρ') 0 ρ₀ ∧
      (ε < |q - q₀| ∨ ε < |ρ - ρ₀|) := fun n => by
    obtain ⟨α, κ, h, q, ρ, r, rBar, q₀, ρ₀, u, D, D₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, hrest⟩ := hcon ((n : ℝ) + 1)⁻¹ (by positivity)
    dsimp only at hrest
    push Not at hrest
    obtain ⟨h14, h15, h16, h17, h18, h19, h20, h21, hbad⟩ := hrest
    exact ⟨α, κ, h, q, ρ, r, rBar, q₀, ρ₀, u, D, D₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, ⟨h14, h15⟩, h16, h17, h18, h19, h20, h21, by
        by_contra hok; push Not at hok; linarith [hbad hok.1]⟩
  choose α κ h q ρ r rBar q₀ ρ₀ u D D₂ hα0 hα1 hκ0 hκ1 hh huc hu0 huτ hu1 hu2 hD hD₂
    huε hr_rBar hρ_eq hq_eq hq₀0 hq₀ρ₀ hcq₀ hcρ₀ hbad using hseq
  -- Apply Proposition 3.3.3 to get uniform bounds on `(q n, ρ n, (ρ n - q n)⁻¹)`
  obtain ⟨C, hC⟩ := exists_bound_of_shcherbinaTirozzi_replicaSymmetric_equations κ₀ κ₁ α₀ h₀ τ
    hκ₀ hα₀ hτ
  have hbd : ∀ n, 0 ≤ q n ∧ q n < ρ n ∧ q n ≤ C ∧ ρ n ≤ C ∧ (ρ n - q n)⁻¹ ≤ C := fun n => by
    obtain ⟨a, b, c, d, e⟩ := hC (α n) (κ n) (h n) (q n) (ρ n) (r n) (rBar n) (u n) (D n) (D₂ n)
      (hα0 n) (hα1 n) (hκ0 n) (hh n) (huc n) (hu0 n) (huτ n) (hu1 n) (hu2 n) (hD n) (hD₂ n)
      (hr_rBar n).1 (hr_rBar n).2 (hρ_eq n) (hq_eq n)
    exact ⟨a, b, c, d, e (hκ1 n)⟩
  -- Uniform bounds for the hard critical points `(q₀ n, ρ₀ n)`
  obtain ⟨C₀, hC₀⟩ := exists_bound_of_shcherbinaTirozziHardFunctional_critical κ₀ κ₁ α₀ h₀ τ
    hκ₀ hα₀ hτ
  have hbd₀ : ∀ n, q₀ n ≤ C₀ ∧ ρ₀ n ≤ C₀ ∧ (ρ₀ n - q₀ n)⁻¹ ≤ C₀ := fun n =>
    hC₀ (α n) (κ n) (h n) (q₀ n) (ρ₀ n) (hα0 n) (hα1 n) (hκ0 n) (hκ1 n) (hh n) (hq₀0 n) (hq₀ρ₀ n)
      (hcq₀ n) (hcρ₀ n)
  -- Extract a converging subsequence in the compact 7-tuple box
  set K_box : Set ((ℝ × ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (Icc 0 α₀ ×ˢ (Icc κ₀ κ₁ ×ˢ Icc (-h₀) h₀)) ×ˢ
      ((Icc 0 C ×ˢ Icc 0 C) ×ˢ (Icc 0 C₀ ×ˢ Icc 0 C₀))
  have hK_comp : IsCompact K_box :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod
      ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc))
  have hmem : ∀ n, ((α n, κ n, h n), ((q n, ρ n), (q₀ n, ρ₀ n))) ∈ K_box := fun n =>
    ⟨⟨⟨hα0 n, hα1 n⟩, ⟨hκ0 n, hκ1 n⟩, abs_le.1 (hh n)⟩,
      ⟨⟨⟨(hbd n).1, (hbd n).2.2.1⟩, ⟨(hbd n).1.trans (hbd n).2.1.le, (hbd n).2.2.2.1⟩⟩,
        ⟨⟨hq₀0 n, (hbd₀ n).1⟩, ⟨(hq₀0 n).trans (hq₀ρ₀ n).le, (hbd₀ n).2.1⟩⟩⟩⟩
  obtain ⟨⟨⟨α_lim, κ_lim, h_lim⟩, ⟨⟨q_lim, ρ_lim⟩, ⟨q₀_lim, ρ₀_lim⟩⟩⟩, hlim_mem, φ, hφ_mono,
      hφ_lim⟩ := hK_comp.tendsto_subseq hmem
  have hα_l : Tendsto (α ∘ φ) atTop (𝓝 α_lim) :=
    (continuous_fst.comp continuous_fst |>.tendsto _).comp hφ_lim
  have hκ_l : Tendsto (κ ∘ φ) atTop (𝓝 κ_lim) :=
    (continuous_fst.comp (continuous_snd.comp continuous_fst) |>.tendsto _).comp hφ_lim
  have hh_l : Tendsto (h ∘ φ) atTop (𝓝 h_lim) :=
    (continuous_snd.comp (continuous_snd.comp continuous_fst) |>.tendsto _).comp hφ_lim
  have hq_l : Tendsto (q ∘ φ) atTop (𝓝 q_lim) :=
    (continuous_fst.comp (continuous_fst.comp continuous_snd) |>.tendsto _).comp hφ_lim
  have hρ_l : Tendsto (ρ ∘ φ) atTop (𝓝 ρ_lim) :=
    (continuous_snd.comp (continuous_fst.comp continuous_snd) |>.tendsto _).comp hφ_lim
  have hq₀_l : Tendsto (q₀ ∘ φ) atTop (𝓝 q₀_lim) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd) |>.tendsto _).comp hφ_lim
  have hρ₀_l : Tendsto (ρ₀ ∘ φ) atTop (𝓝 ρ₀_lim) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd) |>.tendsto _).comp hφ_lim
  -- Strict gaps `q_lim < ρ_lim` and `q₀_lim < ρ₀_lim`
  have hC_pos : 0 < C := lt_of_lt_of_le (inv_pos.2 (sub_pos.2 (hbd 0).2.1)) (hbd 0).2.2.2.2
  have hgap_lim : C⁻¹ ≤ ρ_lim - q_lim := by
    refine ge_of_tendsto (hρ_l.sub hq_l) (Eventually.of_forall fun k => ?_)
    change C⁻¹ ≤ ρ (φ k) - q (φ k)
    have h1 := (hbd (φ k)).2.2.2.2
    have h2 : 0 < ρ (φ k) - q (φ k) := sub_pos.2 (hbd (φ k)).2.1
    rw [← inv_inv (ρ (φ k) - q (φ k))]
    exact inv_anti₀ (inv_pos.2 h2) h1
  have hqρ_lim : q_lim < ρ_lim := by linarith [inv_pos.2 hC_pos]
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le (inv_pos.2 (sub_pos.2 (hq₀ρ₀ 0))) (hbd₀ 0).2.2
  have hgap₀_lim : C₀⁻¹ ≤ ρ₀_lim - q₀_lim := by
    refine ge_of_tendsto (hρ₀_l.sub hq₀_l) (Eventually.of_forall fun k => ?_)
    change C₀⁻¹ ≤ ρ₀ (φ k) - q₀ (φ k)
    have h1 := (hbd₀ (φ k)).2.2
    have h2 : 0 < ρ₀ (φ k) - q₀ (φ k) := sub_pos.2 (hq₀ρ₀ (φ k))
    rw [← inv_inv (ρ₀ (φ k) - q₀ (φ k))]
    exact inv_anti₀ (inv_pos.2 h2) h1
  have hqρ₀_lim : q₀_lim < ρ₀_lim := by linarith [inv_pos.2 hC₀_pos]
  have hε_l : Tendsto (fun k => ((φ k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact h1.comp hφ_mono.tendsto_atTop
  -- Both `(q_lim, ρ_lim)` and `(q₀_lim, ρ₀_lim)` are hard critical points at
  -- `(α_lim, κ_lim, h_lim)`
  have hα_lim0 : 0 ≤ α_lim := hlim_mem.1.1.1
  have hκ_lim0 : 0 < κ_lim := hκ₀.trans_le hlim_mem.1.2.1.1
  have hq_lim0 : 0 ≤ q_lim := hlim_mem.2.1.1.1
  have hq₀_lim0 : 0 ≤ q₀_lim := hlim_mem.2.2.1.1
  obtain ⟨hcq_lim, hcρ_lim⟩ := isCritical_shcherbinaTirozziHardFunctional_of_tendsto_soft
    hqρ_lim
    (fun k => hα0 (φ k)) (fun k => huc (φ k)) (fun k => hu0 (φ k)) (fun k => huτ (φ k))
    (fun k => hu1 (φ k)) (fun k => hu2 (φ k)) (fun k => hD (φ k)) (fun k => hD₂ (φ k))
    (fun k => huε (φ k)) hε_l hα_l hκ_l hh_l hq_l hρ_l
    (fun k => (hr_rBar (φ k)).1) (fun k => (hr_rBar (φ k)).2)
    (fun k => hρ_eq (φ k)) (fun k => hq_eq (φ k))
  obtain ⟨hcq₀_lim, hcρ₀_lim⟩ := isCritical_shcherbinaTirozziHardFunctional_of_tendsto_hard
    hq₀_lim0 hqρ₀_lim (fun k => hq₀0 (φ k)) (fun k => hq₀ρ₀ (φ k))
    hα_l hκ_l hh_l hq₀_l hρ₀_l (fun k => hcq₀ (φ k)) (fun k => hcρ₀ (φ k))
  -- By uniqueness (Theorem 3.3.1), `q_lim = q₀_lim` and `ρ_lim = ρ₀_lim`
  obtain ⟨hq_eq_lim, hρ_eq_lim⟩ := eq_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_zero
    κ_lim h_lim hα_lim0 hτ hq_lim0 hqρ_lim hq₀_lim0 hqρ₀_lim
    hcq_lim hcρ_lim hcq₀_lim hcρ₀_lim
  -- Contradiction with `ε < |q (φ k) - q₀ (φ k)| ∨ ε < |ρ (φ k) - ρ₀ (φ k)|`
  have hq_diff : Tendsto (fun k => |q (φ k) - q₀ (φ k)|) atTop (𝓝 0) := by
    have h := (hq_l.sub hq₀_l).abs
    rwa [hq_eq_lim, sub_self, abs_zero] at h
  have hρ_diff : Tendsto (fun k => |ρ (φ k) - ρ₀ (φ k)|) atTop (𝓝 0) := by
    have h := (hρ_l.sub hρ₀_l).abs
    rwa [hρ_eq_lim, sub_self, abs_zero] at h
  have hev : ∀ᶠ k in atTop, |q (φ k) - q₀ (φ k)| < ε ∧ |ρ (φ k) - ρ₀ (φ k)| < ε :=
    (hq_diff.eventually (Iio_mem_nhds hε)).and (hρ_diff.eventually (Iio_mem_nhds hε))
  obtain ⟨k, hk1, hk2⟩ := hev.exists
  rcases hbad (φ k) with hb | hb <;> linarith

end SpinGlasses
