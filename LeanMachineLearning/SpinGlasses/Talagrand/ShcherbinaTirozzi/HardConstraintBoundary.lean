/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.RSFreeEnergyEnvelope
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The Shcherbina--Tirozzi model: the boundary `q = 0` of the replica-symmetric equations

Talagrand, *Spin Glasses*, Vol. I, Theorem 3.3.1 asserts uniqueness of the solutions of
`∂F/∂q = 0 = ∂F/∂ρ` with `0 ≤ q < ρ`, for the hard-constraint functional `F` of Eq. (3.121).
`HardConstraintUniqueness.lean` treats `0 < q`. This file computes the partial derivative of `F`
in `q`, including the one-sided derivative at `q = 0`, and deduces uniqueness on the whole domain.

Throughout, `mills v = p v / ℙ (ξ ≥ v)` is the inverse Mills ratio.

## Main declarations

* `SpinGlasses.hasDerivAt_shcherbinaTirozziHardFunctional_overlap`: for `0 < q < ρ`,
  `2 ∂F/∂q = q / (ρ - q)² - α 𝔼 mills(…)² / (ρ - q) - h²`.
* `SpinGlasses.hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero`: the right
  derivative at `q = 0` is `-(α mills (τ / √ρ)² / ρ + h²) / 2`.
* `SpinGlasses.eq_zero_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero`: a
  critical point on the boundary `q = 0` forces `α = h = 0`.
* `SpinGlasses.eq_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_zero`: Theorem 3.3.1,
  uniqueness on `0 ≤ q < ρ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SpinGlasses

local notation "mills " v:arg =>
  gaussianPDFReal 0 1 v / Measure.real (gaussianReal 0 1) (Ici v)

/-- **The partial derivative in `q` of the hard replica-symmetric functional** for `0 < q < ρ`:
it is the left side minus the right side of the fixed-point equation for the overlap. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_overlap (α κ h τ : ℝ) {q ρ : ℝ} (hq : 0 < q)
    (hqρ : q < ρ) :
    HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ r ρ)
      ((q / (ρ - q) ^ 2 - α * (∫ z, mills (τ / Real.sqrt (ρ - q) +
          -Real.sqrt q / Real.sqrt (ρ - q) * z) ^ 2 ∂(gaussianReal 0 1)) / (ρ - q) -
        h ^ 2) / 2) q := by
  have hs : 0 < ρ - q := sub_pos.2 hqρ
  have hρ : 0 < ρ := hq.trans hqρ
  have hx : 0 < q / (ρ - q) := div_pos hq hs
  have hinner : HasDerivAt (fun r => r / (ρ - r)) (ρ / (ρ - q) ^ 2) q := by
    refine ((hasDerivAt_id q).div ((hasDerivAt_id q).const_sub ρ) hs.ne').congr_deriv ?_
    simp only [id_eq]; ring
  have hG := (hasDerivAt_shcherbinaTirozziHardFunctional_ratio α κ h τ hx hρ).comp q hinner
  refine (hG.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Iio_mem_nhds hqρ] with r (hr : r < ρ)
    have hsr : ρ - r ≠ 0 := (sub_pos.2 hr).ne'
    have hr' : r / (ρ - r) * ρ / (1 + r / (ρ - r)) = r := by
      have h1 : 1 + r / (ρ - r) = ρ / (ρ - r) := by field_simp; ring
      rw [h1]; have := hρ.ne'; field_simp
    simp only [Function.comp_apply, hr']
  · have h1x : 1 + q / (ρ - q) = ρ / (ρ - q) := by
      have := hs.ne'; field_simp; ring
    have hm : τ * Real.sqrt (1 + q / (ρ - q)) / Real.sqrt ρ = τ / Real.sqrt (ρ - q) := by
      have := (Real.sqrt_pos.2 hρ).ne'; have := (Real.sqrt_pos.2 hs).ne'
      rw [h1x, Real.sqrt_div hρ.le]; field_simp
    have hσ : -Real.sqrt (q / (ρ - q)) = -Real.sqrt q / Real.sqrt (ρ - q) := by
      rw [Real.sqrt_div hq.le, neg_div]
    rw [hm, hσ, h1x]
    have := hs.ne'; have := hρ.ne'; have := hq.ne'
    field_simp

/-- **The right derivative of the hard replica-symmetric functional in `q` at the boundary
`q = 0`.** -/
theorem hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero (α κ h τ : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    HasDerivWithinAt (fun r => shcherbinaTirozziHardFunctional α κ h τ r ρ)
      (-(α * mills (τ / Real.sqrt ρ) ^ 2 / ρ + h ^ 2) / 2) (Ici 0) 0 := by
  set f : ℝ → ℝ := fun r => shcherbinaTirozziHardFunctional α κ h τ r ρ with hf
  have hmem : Ioo (0 : ℝ) ρ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hρ
  have hdiff : DifferentiableOn ℝ f (Ioo 0 ρ) := fun q hq =>
    (hasDerivAt_shcherbinaTirozziHardFunctional_overlap α κ h τ hq.1
      hq.2).differentiableAt.differentiableWithinAt
  -- continuity at `0`, through the variables `x = q / (ρ - q)`
  have hcont : ContinuousWithinAt f (Ioo 0 ρ) 0 := by
    set Φ : ℝ × ℝ → ℝ := fun p => ∫ z, Real.log ((gaussianReal 0 1).real
      (Ici (τ * Real.sqrt (1 + p.1) / Real.sqrt p.2 + -Real.sqrt p.1 * z)))
      ∂(gaussianReal 0 1) with hΦ
    set g : ℝ → ℝ × ℝ := fun q => (q / (ρ - q), ρ) with hg
    set G : ℝ → ℝ := fun q => α * Φ (g q) + q / (2 * (ρ - q)) + Real.log (ρ - q) / 2 -
      κ * ρ + h ^ 2 * (ρ - q) / 2 with hG
    have hfG : ∀ q, 0 ≤ q → q < ρ → f q = G q := fun q hq0 hqρ => by
      have hs : 0 < ρ - q := sub_pos.2 hqρ
      have hx : 1 + q / (ρ - q) = ρ / (ρ - q) := by
        have := hs.ne'
        field_simp
        ring
      have e : ∀ z : ℝ, (τ - Real.sqrt q * z) / Real.sqrt (ρ - q) =
          τ * Real.sqrt (1 + q / (ρ - q)) / Real.sqrt ρ +
            -Real.sqrt (q / (ρ - q)) * z := fun z => by
        rw [hx, Real.sqrt_div' _ hs.le, Real.sqrt_div' _ hs.le]
        have := (Real.sqrt_pos.2 hρ).ne'
        have := (Real.sqrt_pos.2 hs).ne'
        field_simp
        ring
      simp only [hf, hG, hΦ, hg, shcherbinaTirozziHardFunctional, e]
    have hgc : ContinuousWithinAt g (Ioo 0 ρ) 0 := by
      refine ContinuousWithinAt.prodMk ?_ continuousWithinAt_const
      exact (continuousAt_id.div (by fun_prop) (by simpa using hρ.ne')).continuousWithinAt
    have hg0 : g 0 = (0, ρ) := by simp [hg]
    have hΦc : ContinuousWithinAt (fun q => Φ (g q)) (Ioo 0 ρ) 0 := by
      have h0 : ContinuousWithinAt Φ (Ici 0 ×ˢ Ioi 0) (g 0) := by
        rw [hg0]
        exact continuousOn_integral_log_gaussianTail_ratio τ (0, ρ) ⟨self_mem_Ici, hρ⟩
      exact h0.comp hgc fun q hq => ⟨(div_pos hq.1 (sub_pos.2 hq.2)).le, hρ⟩
    have hGc : ContinuousWithinAt G (Ioo 0 ρ) 0 := by
      have h1 : ContinuousAt (fun q : ℝ => q / (2 * (ρ - q))) 0 :=
        continuousAt_id.div (by fun_prop) (by simpa using hρ.ne')
      have h2 : ContinuousAt (fun q : ℝ => Real.log (ρ - q)) 0 :=
        ContinuousAt.log (by fun_prop) (by simpa using hρ.ne')
      have h3 : ContinuousAt (fun q : ℝ => h ^ 2 * (ρ - q) / 2) 0 := by fun_prop
      exact ((((hΦc.const_mul α).add h1.continuousWithinAt).add
        (h2.continuousWithinAt.div_const 2)).sub continuousWithinAt_const).add
          h3.continuousWithinAt
    exact hGc.congr (fun q hq => hfG q hq.1.le hq.2) (hfG 0 le_rfl hρ)
  -- the limit of the derivative
  have hlim : Tendsto (fun q => deriv f q) (𝓝[>] 0)
      (𝓝 (-(α * mills (τ / Real.sqrt ρ) ^ 2 / ρ + h ^ 2) / 2)) := by
    set I : ℝ → ℝ := fun q => ∫ z, mills (τ / Real.sqrt (ρ - q) +
      -Real.sqrt q / Real.sqrt (ρ - q) * z) ^ 2 ∂(gaussianReal 0 1) with hI
    have hsmall : Ioo (0 : ℝ) (ρ / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (half_pos hρ)
    have hcm : Continuous fun v : ℝ => mills v :=
      continuous_iff_continuousAt.2 fun v =>
        (hasDerivAt_gaussianPDFReal_div_measureReal_Ici v _ fun _ => rfl).1.continuousAt
    have hIlim : Tendsto I (𝓝[>] 0) (𝓝 (mills (τ / Real.sqrt ρ) ^ 2)) := by
      obtain ⟨C, hC0, hC⟩ := exists_gaussianPDFReal_div_measureReal_Ici_le
      set B : ℝ := C + |τ| / Real.sqrt (ρ / 2) with hB
      have hB0 : 0 ≤ B := add_nonneg hC0 (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      have hbound : Integrable (fun z : ℝ => (B + |z|) ^ 2) (gaussianReal 0 1) :=
        ((memLp_const B).add (memLp_id_gaussianReal 2).abs).integrable_sq
      have hconst : ∫ _ : ℝ, mills (τ / Real.sqrt ρ) ^ 2 ∂(gaussianReal 0 1) =
          mills (τ / Real.sqrt ρ) ^ 2 := by simp
      rw [← hconst]
      refine tendsto_integral_filter_of_dominated_convergence (fun z => (B + |z|) ^ 2)
        (Eventually.of_forall fun q =>
          ((hcm.comp (by fun_prop : Continuous fun z : ℝ => τ / Real.sqrt (ρ - q) +
            -Real.sqrt q / Real.sqrt (ρ - q) * z)).pow 2).aestronglyMeasurable)
        (eventually_of_mem hsmall fun q hq => ae_of_all _ fun z => ?_) hbound
        (ae_of_all _ fun z => ?_)
      · have hd : ρ / 2 ≤ ρ - q := by linarith [hq.2]
        have hd0 : 0 < ρ - q := (half_pos hρ).trans_le hd
        have hm : |τ / Real.sqrt (ρ - q)| ≤ |τ| / Real.sqrt (ρ / 2) := by
          rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.2 (half_pos hρ))
            (Real.sqrt_le_sqrt hd)
        have hσ : |-Real.sqrt q / Real.sqrt (ρ - q)| ≤ 1 := by
          rw [abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (Real.sqrt_nonneg _), div_le_one (Real.sqrt_pos.2 hd0)]
          exact Real.sqrt_le_sqrt (by linarith [hq.2])
        have hv : |τ / Real.sqrt (ρ - q) + -Real.sqrt q / Real.sqrt (ρ - q) * z| ≤
            |τ| / Real.sqrt (ρ / 2) + |z| := by
          refine (abs_add_le _ _).trans (add_le_add hm ?_)
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) hσ
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        refine pow_le_pow_left₀ (gaussianPDFReal_div_measureReal_Ici_nonneg _) ?_ 2
        refine (hC _).trans ?_
        rw [hB, add_assoc]
        exact add_le_add le_rfl hv
      · have harg : ContinuousAt (fun q : ℝ => τ / Real.sqrt (ρ - q) +
            -Real.sqrt q / Real.sqrt (ρ - q) * z) 0 := by
          have hne : Real.sqrt (ρ - 0) ≠ 0 := by
            rw [sub_zero]
            exact (Real.sqrt_pos.2 hρ).ne'
          have hd : ContinuousAt (fun q : ℝ => Real.sqrt (ρ - q)) 0 := by fun_prop
          have hn : ContinuousAt (fun q : ℝ => -Real.sqrt q) 0 := by fun_prop
          exact (continuousAt_const.div hd hne).add ((hn.div hd hne).mul continuousAt_const)
        have h := ((hcm.pow 2).continuousAt.comp harg).tendsto
        simp only [Function.comp_def, sub_zero, Real.sqrt_zero, neg_zero, zero_div, zero_mul,
          add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
    have hmain : Tendsto (fun q : ℝ => (q / (ρ - q) ^ 2 - α * I q / (ρ - q) - h ^ 2) / 2)
        (𝓝[>] 0) (𝓝 ((0 / (ρ - 0) ^ 2 - α * mills (τ / Real.sqrt ρ) ^ 2 / (ρ - 0) -
          h ^ 2) / 2)) := by
      have hid : Tendsto (fun q : ℝ => q) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      have hsub : Tendsto (fun q : ℝ => ρ - q) (𝓝[>] 0) (𝓝 (ρ - 0)) := hid.const_sub ρ
      have hne : ρ - 0 ≠ 0 := by simpa using hρ.ne'
      exact (((hid.div (hsub.pow 2) (pow_ne_zero 2 hne)).sub
        ((hIlim.const_mul α).div hsub hne)).sub_const (h ^ 2)).div_const 2
    have hval : (0 / (ρ - 0) ^ 2 - α * mills (τ / Real.sqrt ρ) ^ 2 / (ρ - 0) - h ^ 2) / 2 =
        -(α * mills (τ / Real.sqrt ρ) ^ 2 / ρ + h ^ 2) / 2 := by
      rw [zero_div, sub_zero]
      ring
    rw [hval] at hmain
    refine hmain.congr' (eventually_of_mem hmem fun q hq => ?_)
    exact (hasDerivAt_shcherbinaTirozziHardFunctional_overlap α κ h τ hq.1 hq.2).deriv.symm
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont hmem hlim

/-- A critical point of the hard replica-symmetric functional in `q` on the boundary `q = 0`
exists only without constraints and external field: `α = h = 0`. -/
theorem eq_zero_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero (κ τ : ℝ)
    {α h ρ : ℝ} (hα : 0 ≤ α) (hρ : 0 < ρ)
    (hd : HasDerivWithinAt (fun r => shcherbinaTirozziHardFunctional α κ h τ r ρ) 0 (Ici 0) 0) :
    α = 0 ∧ h = 0 := by
  have heq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _
    (hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero α κ h τ hρ) hd
  have hmills : 0 < mills (τ / Real.sqrt ρ) :=
    div_pos (gaussianPDFReal_pos _ _ _ one_ne_zero) (measureReal_gaussianReal_Ici_pos _)
  have h1 : 0 ≤ α * mills (τ / Real.sqrt ρ) ^ 2 / ρ :=
    div_nonneg (mul_nonneg hα (sq_nonneg _)) hρ.le
  have h2 := sq_nonneg h
  have hA : α * mills (τ / Real.sqrt ρ) ^ 2 / ρ = 0 := by linarith
  have hh : h ^ 2 = 0 := by linarith
  refine ⟨?_, pow_eq_zero_iff two_ne_zero |>.1 hh⟩
  rcases (div_eq_zero_iff.1 hA) with h0 | h0
  · exact (mul_eq_zero.1 h0).resolve_right (pow_ne_zero 2 hmills.ne')
  · exact absurd h0 hρ.ne'

/-- **Talagrand, Theorem 3.3.1, uniqueness on `0 ≤ q < ρ`:** for `α ≥ 0` and `τ ≥ 0`, the
equations `∂F/∂q = 0 = ∂F/∂ρ` (the derivative in `q` being one-sided at `q = 0`) have at most one
solution. A solution with `q = 0` exists only if `α = h = 0`, and then `ρ = (2 κ)⁻¹`. -/
theorem eq_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_zero {α τ : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) {q₁ ρ₁ q₂ ρ₂ : ℝ} (hq₁ : 0 ≤ q₁) (hρ₁ : q₁ < ρ₁) (hq₂ : 0 ≤ q₂)
    (hρ₂ : q₂ < ρ₂)
    (h1q : HasDerivWithinAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ₁) 0 (Ici 0) q₁)
    (h1ρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q₁ ρ) 0 ρ₁)
    (h2q : HasDerivWithinAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ₂) 0 (Ici 0) q₂)
    (h2ρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q₂ ρ) 0 ρ₂) :
    q₁ = q₂ ∧ ρ₁ = ρ₂ := by
  -- a solution on the boundary excludes every other overlap
  have key : ∀ {ρ q ρ' : ℝ}, 0 < ρ → 0 ≤ q → q < ρ' →
      HasDerivWithinAt (fun r => shcherbinaTirozziHardFunctional α κ h τ r ρ) 0 (Ici 0) 0 →
      HasDerivWithinAt (fun r => shcherbinaTirozziHardFunctional α κ h τ r ρ') 0 (Ici 0) q →
      α = 0 ∧ h = 0 ∧ q = 0 := fun {ρ q ρ'} hρ hq hqρ hb hd => by
    obtain ⟨hα0, hh0⟩ :=
      eq_zero_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_overlap_zero κ τ hα hρ hb
    refine ⟨hα0, hh0, ?_⟩
    rcases hq.eq_or_lt with h0 | h0
    · exact h0.symm
    have heq := (hd.hasDerivAt (Ici_mem_nhds h0)).unique
      (hasDerivAt_shcherbinaTirozziHardFunctional_overlap α κ h τ h0 hqρ)
    rw [hα0, hh0, zero_mul, zero_div, sub_zero, zero_pow two_ne_zero, sub_zero] at heq
    have hpos : 0 < q / (ρ' - q) ^ 2 := div_pos h0 (pow_pos (sub_pos.2 hqρ) 2)
    linarith
  -- at `q = α = h = 0` the equation in `ρ` determines `ρ`
  have hself : ∀ {ρ : ℝ}, 0 < ρ → α = 0 → h = 0 →
      HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ 0 r) 0 ρ → ρ⁻¹ = 2 * κ :=
    fun {ρ} hρ hα0 hh0 hd => by
      have e : (fun r => shcherbinaTirozziHardFunctional α κ h τ 0 r) =
          fun r => Real.log r / 2 - κ * r := by
        funext r
        simp [shcherbinaTirozziHardFunctional, hα0, hh0]
      rw [e] at hd
      have h' := ((Real.hasDerivAt_log hρ.ne').div_const 2).sub ((hasDerivAt_id ρ).const_mul κ)
      have heq := hd.unique h'
      linarith
  rcases hq₁.eq_or_lt with h10 | h10
  · subst h10
    obtain ⟨hα0, hh0, h20⟩ := key hρ₁ hq₂ hρ₂ h1q h2q
    subst h20
    refine ⟨rfl, inv_injective ?_⟩
    rw [hself hρ₁ hα0 hh0 h1ρ, hself hρ₂ hα0 hh0 h2ρ]
  rcases hq₂.eq_or_lt with h20 | h20
  · subst h20
    obtain ⟨-, -, h10'⟩ := key hρ₂ hq₁ hρ₁ h2q h1q
    exact absurd h10' h10.ne'
  exact eq_of_hasDerivAt_shcherbinaTirozziHardFunctional_zero κ h hα hτ h10 hρ₁ h20 hρ₂
    (h1q.hasDerivAt (Ici_mem_nhds h10)) h1ρ (h2q.hasDerivAt (Ici_mem_nhds h20)) h2ρ

end SpinGlasses
