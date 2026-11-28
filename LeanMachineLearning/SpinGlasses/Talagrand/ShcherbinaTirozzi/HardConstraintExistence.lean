/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.Analysis.Convex.SmoothCutoff

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.HardConstraintBoundary
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.HardConstraintStability
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.RSExistence

/-!
# The Shcherbina--Tirozzi model: existence and stability of hard RS critical points

This module completes **Talagrand, Theorem 3.3.1** (existence and uniqueness of the hard-constraint
replica-symmetric critical point for `0 ≤ α < 2`, `κ > 0`, `τ ≥ 0`, `h : ℝ`) and deduces the
unconditional form of **Corollary 3.3.4** as well as uniform continuity of the hard critical point
in `(α, κ, h)`.

## Main declarations

* `SpinGlasses.exists_shcherbinaTirozziHardFunctional_critical`: existence in Theorem 3.3.1.
* `SpinGlasses.existsUnique_shcherbinaTirozziHardFunctional_critical`: full existence and
  uniqueness in Theorem 3.3.1.
* `SpinGlasses.exists_soft_rs_close_to_hard_unconditional`: unconditional Corollary 3.3.4.
* `SpinGlasses.uniform_close_shcherbinaTirozziHardFunctional_critical`: uniform stability of hard
  critical points under perturbations of `(α, κ, h)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SpinGlasses

/-- **Existence in Talagrand, Theorem 3.3.1:** for `0 ≤ α < 2`, `κ > 0`, `τ ≥ 0`, and `h : ℝ`,
there exists `(q₀, ρ₀)` with `0 ≤ q₀ < ρ₀` that is a critical point of the hard-constraint
replica-symmetric functional `shcherbinaTirozziHardFunctional α κ h τ` (one-sided in `q` at
`q = 0`). -/
theorem exists_shcherbinaTirozziHardFunctional_critical {α κ h τ : ℝ} (hα0 : 0 ≤ α)
    (hα2 : α < 2) (hκ : 0 < κ) (hτ : 0 ≤ τ) :
    ∃ q₀ ρ₀ : ℝ, 0 ≤ q₀ ∧ q₀ < ρ₀ ∧
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α κ h τ q' ρ₀) 0 (Ici 0) q₀ ∧
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ q₀ ρ') 0 ρ₀ := by
  have hα10 : α ≤ 10 := hα2.le.trans (by norm_num)
  have hseq : ∀ n : ℕ, ∃ (u : ℝ → ℝ) (D₀ q ρ : ℝ),
      0 ≤ D₀ ∧ ConcaveOn ℝ univ u ∧ (∀ x, u x ≤ 0) ∧ (∀ x, τ ≤ x → u x = 0) ∧
      Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      Differentiable ℝ (deriv (deriv u)) ∧ Differentiable ℝ (deriv (deriv (deriv u))) ∧
      (∀ x, |deriv u x| ≤ D₀ * (1 + |τ|)) ∧
      (∀ x, |deriv (deriv u) x| ≤ D₀ * (1 + |τ|)) ∧
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D₀ * (1 + |τ|)) ∧
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D₀ * (1 + |τ|)) ∧
      (∀ x, -(D₀ * (1 + |τ|)) * (1 + |x|) ≤ u x) ∧
      Real.exp (u (τ - ((n : ℝ) + 1)⁻¹)) ≤ ((n : ℝ) + 1)⁻¹ ∧
      0 ≤ q ∧ q < ρ ∧
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y => (∫ ξ, deriv u (y + Real.sqrt (ρ - q) * ξ) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ - q) * ξ) +
          deriv u (y + Real.sqrt (ρ - q) * ξ) ^ 2) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      0 < 2 * κ + r - rBar ∧
        ρ = (2 * κ + r - rBar)⁻¹ + (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 ∧
        q = (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 := fun n => by
    obtain ⟨u, D₀, hcd, huc, hu0, huτ, huε, hD₀0, hder⟩ :=
      exists_contDiff_concaveOn_nonpos_eq_zero_of_ge τ (ε := ((n : ℝ) + 1)⁻¹) (by positivity) 4
    have hτ1 : 1 ≤ 1 + |τ| := le_add_of_nonneg_right (abs_nonneg τ)
    have hid_le : ∀ j, 1 ≤ j → j ≤ 4 → ∀ x, |iteratedDeriv j u x| ≤ D₀ * (1 + |τ|) :=
      fun j hj1 hj4 x => (hder j hj1 hj4 x).trans (le_mul_of_one_le_right hD₀0 hτ1)
    have hu1 : Differentiable ℝ u := (hcd 1).differentiable (by simp)
    have hd1 : ContDiff ℝ 3 (deriv u) := (contDiff_succ_iff_deriv.1 (hcd 4)).2.2
    have hu2 : Differentiable ℝ (deriv u) := hd1.differentiable (by simp)
    have hd2 : ContDiff ℝ 2 (deriv (deriv u)) := (contDiff_succ_iff_deriv.1 hd1).2.2
    have hu3 : Differentiable ℝ (deriv (deriv u)) := hd2.differentiable (by simp)
    have hd3 : ContDiff ℝ 1 (deriv (deriv (deriv u))) := (contDiff_succ_iff_deriv.1 hd2).2.2
    have hu4 : Differentiable ℝ (deriv (deriv (deriv u))) := hd3.differentiable (by simp)
    have hD1 : ∀ x, |deriv u x| ≤ D₀ * (1 + |τ|) := fun x => by
      simpa only [iteratedDeriv_one] using hid_le 1 le_rfl (by norm_num) x
    have hD2 : ∀ x, |deriv (deriv u) x| ≤ D₀ * (1 + |τ|) := fun x => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        hid_le 2 (by norm_num) (by norm_num) x
    have hD3 : ∀ x, |deriv (deriv (deriv u)) x| ≤ D₀ * (1 + |τ|) := fun x => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        hid_le 3 (by norm_num) (by norm_num) x
    have hD4 : ∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D₀ * (1 + |τ|) := fun x => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hid_le 4 (by norm_num) le_rfl x
    have hgrow : ∀ x, -(D₀ * (1 + |τ|)) * (1 + |x|) ≤ u x := fun x =>
      neg_mul_one_add_abs_le_of_eq_zero_of_abs_deriv_le hu1 (huτ τ le_rfl)
        (fun y => by simpa only [iteratedDeriv_one] using hder 1 le_rfl (by norm_num) y) x
    obtain ⟨q, ρ, hq0, hqρ, ha, hρ, hq⟩ := exists_shcherbinaTirozzi_rsEquations_solution
      hα0 hα10 hκ huc hu0 hgrow hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4
    exact ⟨u, D₀, q, ρ, hD₀0, huc, hu0, huτ, hu1, hu2, hu3, hu4, hD1, hD2, hD3, hD4, hgrow,
      huε, hq0, hqρ, ha, hρ, hq⟩
  choose u D₀ q ρ hD₀0 huc hu0 huτ hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 hgrow huε hq0 hqρ
    ha hρ_eq hq_eq using hseq
  let r : ℕ → ℝ := fun n =>
    α * ∫ z, ((∫ ξ, deriv (u n) (Real.sqrt (q n) * z + Real.sqrt (ρ n - q n) * ξ) *
      Real.exp (u n (Real.sqrt (q n) * z + Real.sqrt (ρ n - q n) * ξ)) ∂(gaussianReal 0 1)) /
      ∫ ξ, Real.exp (u n (Real.sqrt (q n) * z + Real.sqrt (ρ n - q n) * ξ))
        ∂(gaussianReal 0 1)) ^ 2 ∂(gaussianReal 0 1)
  let rBar : ℕ → ℝ := fun n =>
    α * ∫ z, ((∫ ξ, (deriv (deriv (u n)) (Real.sqrt (q n) * z + Real.sqrt (ρ n - q n) * ξ) +
        deriv (u n) (Real.sqrt (q n) * z + Real.sqrt (ρ n - q n) * ξ) ^ 2) *
      Real.exp (u n (Real.sqrt (q n) * z + Real.sqrt (ρ n - q n) * ξ)) ∂(gaussianReal 0 1)) /
      ∫ ξ, Real.exp (u n (Real.sqrt (q n) * z + Real.sqrt (ρ n - q n) * ξ))
        ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
  -- Uniform bounds independent of `n` from Proposition 3.3.3
  obtain ⟨C, hC⟩ := exists_bound_of_shcherbinaTirozzi_replicaSymmetric_equations
    κ κ α |h| τ hκ hα2 hτ
  have hbd : ∀ n, q n ≤ C ∧ ρ n ≤ C ∧ (ρ n - q n)⁻¹ ≤ C := fun n => by
    obtain ⟨_, _, hqC, hρC, hgapC⟩ := hC α κ h (q n) (ρ n) (r n) (rBar n) (u n)
      (D₀ n * (1 + |τ|)) (D₀ n * (1 + |τ|)) hα0 le_rfl le_rfl le_rfl (huc n) (hu0 n)
      (huτ n) (hu1 n) (hu2 n) (hD1 n) (hD2 n) rfl rfl (hρ_eq n) (hq_eq n)
    exact ⟨hqC, hρC, hgapC le_rfl⟩
  -- Extract a converging subsequence of `(q n, ρ n)` in `[0, C] × [0, C]`
  have hK_comp : IsCompact (Icc (0 : ℝ) C ×ˢ Icc (0 : ℝ) C) := isCompact_Icc.prod isCompact_Icc
  have hmem : ∀ n, (q n, ρ n) ∈ Icc (0 : ℝ) C ×ˢ Icc (0 : ℝ) C := fun n =>
    ⟨⟨hq0 n, (hbd n).1⟩, ⟨(hq0 n).trans (hqρ n).le, (hbd n).2.1⟩⟩
  obtain ⟨⟨q₀, ρ₀⟩, hlim_mem, φ, hφ_mono, hφ_lim⟩ := hK_comp.tendsto_subseq hmem
  have hq_l : Tendsto (q ∘ φ) atTop (𝓝 q₀) := (continuous_fst.tendsto _).comp hφ_lim
  have hρ_l : Tendsto (ρ ∘ φ) atTop (𝓝 ρ₀) := (continuous_snd.tendsto _).comp hφ_lim
  have hC_pos : 0 < C := lt_of_lt_of_le (inv_pos.2 (sub_pos.2 (hqρ 0))) (hbd 0).2.2
  have hgap : C⁻¹ ≤ ρ₀ - q₀ := by
    refine ge_of_tendsto (hρ_l.sub hq_l) (Eventually.of_forall fun k => ?_)
    change C⁻¹ ≤ ρ (φ k) - q (φ k)
    have h1 := (hbd (φ k)).2.2
    have h2 : 0 < ρ (φ k) - q (φ k) := sub_pos.2 (hqρ (φ k))
    rw [← inv_inv (ρ (φ k) - q (φ k))]
    exact inv_anti₀ (inv_pos.2 h2) h1
  have hqρ₀ : q₀ < ρ₀ := by linarith [inv_pos.2 hC_pos]
  have hε_l : Tendsto (fun k => ((φ k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact h1.comp hφ_mono.tendsto_atTop
  obtain ⟨hcq, hcρ⟩ := isCritical_shcherbinaTirozziHardFunctional_of_tendsto_soft
    hqρ₀ (fun _ => hα0) (fun k => huc (φ k)) (fun k => hu0 (φ k)) (fun k => huτ (φ k))
    (fun k => hu1 (φ k)) (fun k => hu2 (φ k)) (fun k => hD1 (φ k)) (fun k => hD2 (φ k))
    (fun k => huε (φ k)) hε_l tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds hq_l hρ_l
    (fun _ => rfl) (fun _ => rfl) (fun k => hρ_eq (φ k)) (fun k => hq_eq (φ k))
  exact ⟨q₀, ρ₀, hlim_mem.1.1, hqρ₀, hcq, hcρ⟩

/-- **Talagrand, Theorem 3.3.1 (full existence and uniqueness):** for `0 ≤ α < 2`, `κ > 0`,
`τ ≥ 0`, and `h : ℝ`, there exists a unique `(q₀, ρ₀)` with `0 ≤ q₀ < ρ₀` at which
`shcherbinaTirozziHardFunctional α κ h τ` is critical (one-sided in `q` at `q = 0`). -/
theorem existsUnique_shcherbinaTirozziHardFunctional_critical {α κ h τ : ℝ} (hα0 : 0 ≤ α)
    (hα2 : α < 2) (hκ : 0 < κ) (hτ : 0 ≤ τ) :
    ∃! p : ℝ × ℝ, 0 ≤ p.1 ∧ p.1 < p.2 ∧
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α κ h τ q' p.2) 0 (Ici 0) p.1 ∧
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ p.1 ρ') 0 p.2 := by
  obtain ⟨q₀, ρ₀, hq₀, hqρ₀, hcq₀, hcρ₀⟩ :=
    exists_shcherbinaTirozziHardFunctional_critical hα0 hα2 hκ hτ
  refine ⟨(q₀, ρ₀), ⟨hq₀, hqρ₀, hcq₀, hcρ₀⟩, ?_⟩
  rintro ⟨q₁, ρ₁⟩ ⟨hq₁, hqρ₁, hcq₁, hcρ₁⟩
  obtain ⟨hq, hρ⟩ := eq_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_zero
    κ h hα0 hτ hq₁ hqρ₁ hq₀ hqρ₀ hcq₁ hcρ₁ hcq₀ hcρ₀
  exact Prod.ext hq hρ

/-- **Talagrand, Corollary 3.3.4 (unconditional):** given `0 < κ₀`, `α₀ < 2`, `h₀`, `τ ≥ 0`,
and `ε > 0`, there exists `ε' > 0` such that whenever `u ≤ 0` is smooth and concave, vanishes on
`[τ, ∞)`, and satisfies `exp (u (τ - ε')) ≤ ε'`, and whenever `0 ≤ α ≤ α₀`, `κ₀ ≤ κ ≤ κ₁`,
`|h| ≤ h₀`, and `(q, ρ)` solves the soft RS equations for `u`, the unique hard critical point
`(q₀, ρ₀)` exists and satisfies `|q - q₀| ≤ ε` and `|ρ - ρ₀| ≤ ε`. -/
theorem exists_soft_rs_close_to_hard_unconditional (κ₀ κ₁ α₀ h₀ τ ε : ℝ)
    (hκ₀ : 0 < κ₀) (hα₀ : α₀ < 2) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ∀ (α κ h q ρ r rBar : ℝ) (u : ℝ → ℝ) (D D₂ : ℝ),
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
      ∃ q₀ ρ₀ : ℝ, 0 ≤ q₀ ∧ q₀ < ρ₀ ∧
        HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α κ h τ q' ρ₀) 0 (Ici 0) q₀ ∧
        HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α κ h τ q₀ ρ') 0 ρ₀ ∧
        |q - q₀| ≤ ε ∧ |ρ - ρ₀| ≤ ε := by
  obtain ⟨ε', hε', hstab⟩ := exists_soft_rs_close_to_hard κ₀ κ₁ α₀ h₀ τ ε hκ₀ hα₀ hτ hε
  refine ⟨ε', hε', fun α κ h q ρ r rBar u D D₂ hα0 hα1 hκ0 hκ1 hh huc hu0 huτ hu1 hu2
      hD hD₂ huε hr hrBar hρ hq => ?_⟩
  obtain ⟨q₀, ρ₀, hq₀, hqρ₀, hcq₀, hcρ₀⟩ := exists_shcherbinaTirozziHardFunctional_critical
    hα0 (hα1.trans_lt hα₀) (hκ₀.trans_le hκ0) hτ
  obtain ⟨hq_close, hρ_close⟩ := hstab α κ h q ρ r rBar q₀ ρ₀ u D D₂ hα0 hα1 hκ0 hκ1 hh
    huc hu0 huτ hu1 hu2 hD hD₂ huε hr hrBar hρ hq hq₀ hqρ₀ hcq₀ hcρ₀
  exact ⟨q₀, ρ₀, hq₀, hqρ₀, hcq₀, hcρ₀, hq_close, hρ_close⟩

/-- **Uniform continuity of the hard RS critical point `(q₀, ρ₀)` in `(α, κ, h)`** on the compact
box `[0, α₀] × [κ₀, κ₁] × [-h₀, h₀]` (`α₀ < 2`, `0 < κ₀`). -/
theorem uniform_close_shcherbinaTirozziHardFunctional_critical
    (κ₀ κ₁ α₀ h₀ τ ε : ℝ) (hκ₀ : 0 < κ₀) (hα₀ : α₀ < 2) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ α₁ α₂ κ₁' κ₂' h₁ h₂ q₁ ρ₁ q₂ ρ₂ : ℝ,
      0 ≤ α₁ → α₁ ≤ α₀ → 0 ≤ α₂ → α₂ ≤ α₀ →
      κ₀ ≤ κ₁' → κ₁' ≤ κ₁ → κ₀ ≤ κ₂' → κ₂' ≤ κ₁ →
      |h₁| ≤ h₀ → |h₂| ≤ h₀ →
      |α₁ - α₂| ≤ δ → |κ₁' - κ₂'| ≤ δ → |h₁ - h₂| ≤ δ →
      0 ≤ q₁ → q₁ < ρ₁ →
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α₁ κ₁' h₁ τ q' ρ₁) 0 (Ici 0) q₁ →
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α₁ κ₁' h₁ τ q₁ ρ') 0 ρ₁ →
      0 ≤ q₂ → q₂ < ρ₂ →
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α₂ κ₂' h₂ τ q' ρ₂) 0 (Ici 0) q₂ →
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α₂ κ₂' h₂ τ q₂ ρ') 0 ρ₂ →
      |q₁ - q₂| ≤ ε ∧ |ρ₁ - ρ₂| ≤ ε := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ α₁ α₂ κ₁' κ₂' h₁ h₂ q₁ ρ₁ q₂ ρ₂ : ℝ,
      0 ≤ α₁ ∧ α₁ ≤ α₀ ∧ 0 ≤ α₂ ∧ α₂ ≤ α₀ ∧
      κ₀ ≤ κ₁' ∧ κ₁' ≤ κ₁ ∧ κ₀ ≤ κ₂' ∧ κ₂' ≤ κ₁ ∧
      |h₁| ≤ h₀ ∧ |h₂| ≤ h₀ ∧
      |α₁ - α₂| ≤ ((n : ℝ) + 1)⁻¹ ∧ |κ₁' - κ₂'| ≤ ((n : ℝ) + 1)⁻¹ ∧
      |h₁ - h₂| ≤ ((n : ℝ) + 1)⁻¹ ∧
      0 ≤ q₁ ∧ q₁ < ρ₁ ∧
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α₁ κ₁' h₁ τ q' ρ₁) 0 (Ici 0) q₁ ∧
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α₁ κ₁' h₁ τ q₁ ρ') 0 ρ₁ ∧
      0 ≤ q₂ ∧ q₂ < ρ₂ ∧
      HasDerivWithinAt (fun q' => shcherbinaTirozziHardFunctional α₂ κ₂' h₂ τ q' ρ₂) 0 (Ici 0) q₂ ∧
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional α₂ κ₂' h₂ τ q₂ ρ') 0 ρ₂ ∧
      (ε < |q₁ - q₂| ∨ ε < |ρ₁ - ρ₂|) := fun n => by
    obtain ⟨α₁, α₂, κ₁', κ₂', h₁, h₂, q₁, ρ₁, q₂, ρ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, hbad⟩ :=
      hcon ((n : ℝ) + 1)⁻¹ (by positivity)
    exact ⟨α₁, α₂, κ₁', κ₂', h₁, h₂, q₁, ρ₁, q₂, ρ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, by
        by_contra hok; push Not at hok; linarith [hbad hok.1]⟩
  choose α₁ α₂ κ₁' κ₂' h₁ h₂ q₁ ρ₁ q₂ ρ₂ hα10 hα11 hα20 hα21 hκ10 hκ11 hκ20 hκ21 hh1 hh2
    hdα hdκ hdh hq10 hq1ρ1 hcq1 hcρ1 hq20 hq2ρ2 hcq2 hcρ2 hbad using hseq
  obtain ⟨C₀, hC₀⟩ := exists_bound_of_shcherbinaTirozziHardFunctional_critical
    κ₀ κ₁ α₀ h₀ τ hκ₀ hα₀ hτ
  have hbd1 : ∀ n, q₁ n ≤ C₀ ∧ ρ₁ n ≤ C₀ ∧ (ρ₁ n - q₁ n)⁻¹ ≤ C₀ := fun n =>
    hC₀ (α₁ n) (κ₁' n) (h₁ n) (q₁ n) (ρ₁ n) (hα10 n) (hα11 n) (hκ10 n) (hκ11 n) (hh1 n)
      (hq10 n) (hq1ρ1 n) (hcq1 n) (hcρ1 n)
  have hbd2 : ∀ n, q₂ n ≤ C₀ ∧ ρ₂ n ≤ C₀ ∧ (ρ₂ n - q₂ n)⁻¹ ≤ C₀ := fun n =>
    hC₀ (α₂ n) (κ₂' n) (h₂ n) (q₂ n) (ρ₂ n) (hα20 n) (hα21 n) (hκ20 n) (hκ21 n) (hh2 n)
      (hq20 n) (hq2ρ2 n) (hcq2 n) (hcρ2 n)
  set K_box : Set ((ℝ × ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (Icc 0 α₀ ×ˢ (Icc κ₀ κ₁ ×ˢ Icc (-h₀) h₀)) ×ˢ
      ((Icc 0 C₀ ×ˢ Icc 0 C₀) ×ˢ (Icc 0 C₀ ×ˢ Icc 0 C₀))
  have hK_comp : IsCompact K_box :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod
      ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc))
  have hmem : ∀ n, ((α₁ n, κ₁' n, h₁ n), ((q₁ n, ρ₁ n), (q₂ n, ρ₂ n))) ∈ K_box := fun n =>
    ⟨⟨⟨hα10 n, hα11 n⟩, ⟨hκ10 n, hκ11 n⟩, abs_le.1 (hh1 n)⟩,
      ⟨⟨⟨hq10 n, (hbd1 n).1⟩, ⟨(hq10 n).trans (hq1ρ1 n).le, (hbd1 n).2.1⟩⟩,
        ⟨⟨hq20 n, (hbd2 n).1⟩, ⟨(hq20 n).trans (hq2ρ2 n).le, (hbd2 n).2.1⟩⟩⟩⟩
  obtain ⟨⟨⟨α_l, κ_l, h_l⟩, ⟨⟨q1_l, ρ1_l⟩, ⟨q2_l, ρ2_l⟩⟩⟩, hlim_mem, φ, hφ_mono, hφ_lim⟩ :=
    hK_comp.tendsto_subseq hmem
  have hα1_l : Tendsto (α₁ ∘ φ) atTop (𝓝 α_l) :=
    (continuous_fst.comp continuous_fst |>.tendsto _).comp hφ_lim
  have hκ1_l : Tendsto (κ₁' ∘ φ) atTop (𝓝 κ_l) :=
    (continuous_fst.comp (continuous_snd.comp continuous_fst) |>.tendsto _).comp hφ_lim
  have hh1_l : Tendsto (h₁ ∘ φ) atTop (𝓝 h_l) :=
    (continuous_snd.comp (continuous_snd.comp continuous_fst) |>.tendsto _).comp hφ_lim
  have hq1_l : Tendsto (q₁ ∘ φ) atTop (𝓝 q1_l) :=
    (continuous_fst.comp (continuous_fst.comp continuous_snd) |>.tendsto _).comp hφ_lim
  have hρ1_l : Tendsto (ρ₁ ∘ φ) atTop (𝓝 ρ1_l) :=
    (continuous_snd.comp (continuous_fst.comp continuous_snd) |>.tendsto _).comp hφ_lim
  have hq2_l : Tendsto (q₂ ∘ φ) atTop (𝓝 q2_l) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd) |>.tendsto _).comp hφ_lim
  have hρ2_l : Tendsto (ρ₂ ∘ φ) atTop (𝓝 ρ2_l) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd) |>.tendsto _).comp hφ_lim
  have hinv_0 : Tendsto (fun k => ((φ k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop.comp
      hφ_mono.tendsto_atTop).atTop_add tendsto_const_nhds)
  have hα2_l : Tendsto (α₂ ∘ φ) atTop (𝓝 α_l) := by
    have hd : Tendsto (fun k => α₂ (φ k) - α₁ (φ k)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k => by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hdα (φ k)) hinv_0
    change Tendsto (fun k => α₂ (φ k)) atTop (𝓝 α_l)
    simpa using hα1_l.add hd
  have hκ2_l : Tendsto (κ₂' ∘ φ) atTop (𝓝 κ_l) := by
    have hd : Tendsto (fun k => κ₂' (φ k) - κ₁' (φ k)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k => by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hdκ (φ k)) hinv_0
    change Tendsto (fun k => κ₂' (φ k)) atTop (𝓝 κ_l)
    simpa using hκ1_l.add hd
  have hh2_l : Tendsto (h₂ ∘ φ) atTop (𝓝 h_l) := by
    have hd : Tendsto (fun k => h₂ (φ k) - h₁ (φ k)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k => by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hdh (φ k)) hinv_0
    change Tendsto (fun k => h₂ (φ k)) atTop (𝓝 h_l)
    simpa using hh1_l.add hd
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le (inv_pos.2 (sub_pos.2 (hq1ρ1 0))) (hbd1 0).2.2
  have hqρ1_l : q1_l < ρ1_l := by
    have hgap : C₀⁻¹ ≤ ρ1_l - q1_l :=
      ge_of_tendsto (hρ1_l.sub hq1_l) (Eventually.of_forall fun k => by
        change C₀⁻¹ ≤ ρ₁ (φ k) - q₁ (φ k)
        have h2 : 0 < ρ₁ (φ k) - q₁ (φ k) := sub_pos.2 (hq1ρ1 (φ k))
        rw [← inv_inv (ρ₁ (φ k) - q₁ (φ k))]
        exact inv_anti₀ (inv_pos.2 h2) (hbd1 (φ k)).2.2)
    linarith [inv_pos.2 hC₀_pos]
  have hqρ2_l : q2_l < ρ2_l := by
    have hgap : C₀⁻¹ ≤ ρ2_l - q2_l :=
      ge_of_tendsto (hρ2_l.sub hq2_l) (Eventually.of_forall fun k => by
        change C₀⁻¹ ≤ ρ₂ (φ k) - q₂ (φ k)
        have h2 : 0 < ρ₂ (φ k) - q₂ (φ k) := sub_pos.2 (hq2ρ2 (φ k))
        rw [← inv_inv (ρ₂ (φ k) - q₂ (φ k))]
        exact inv_anti₀ (inv_pos.2 h2) (hbd2 (φ k)).2.2)
    linarith [inv_pos.2 hC₀_pos]
  obtain ⟨hcq1_l, hcρ1_l⟩ := isCritical_shcherbinaTirozziHardFunctional_of_tendsto_hard
    hlim_mem.2.1.1.1 hqρ1_l (fun k => hq10 (φ k)) (fun k => hq1ρ1 (φ k))
    hα1_l hκ1_l hh1_l hq1_l hρ1_l (fun k => hcq1 (φ k)) (fun k => hcρ1 (φ k))
  obtain ⟨hcq2_l, hcρ2_l⟩ := isCritical_shcherbinaTirozziHardFunctional_of_tendsto_hard
    hlim_mem.2.2.1.1 hqρ2_l (fun k => hq20 (φ k)) (fun k => hq2ρ2 (φ k))
    hα2_l hκ2_l hh2_l hq2_l hρ2_l (fun k => hcq2 (φ k)) (fun k => hcρ2 (φ k))
  obtain ⟨hq_eq, hρ_eq⟩ := eq_of_hasDerivWithinAt_shcherbinaTirozziHardFunctional_zero
    κ_l h_l hlim_mem.1.1.1 hτ hlim_mem.2.1.1.1 hqρ1_l hlim_mem.2.2.1.1 hqρ2_l
    hcq1_l hcρ1_l hcq2_l hcρ2_l
  change q1_l = q2_l at hq_eq
  have hq_diff : Tendsto (fun k => |q₁ (φ k) - q₂ (φ k)|) atTop (𝓝 0) := by
    have t := (hq1_l.sub hq2_l).abs; rwa [hq_eq, sub_self, abs_zero] at t
  have hρ_diff : Tendsto (fun k => |ρ₁ (φ k) - ρ₂ (φ k)|) atTop (𝓝 0) := by
    have t := (hρ1_l.sub hρ2_l).abs; rwa [hρ_eq, sub_self, abs_zero] at t
  obtain ⟨k, hk1, hk2⟩ := ((hq_diff.eventually (Iio_mem_nhds hε)).and
    (hρ_diff.eventually (Iio_mem_nhds hε))).exists
  rcases hbad (φ k) with hb | hb <;> linarith

end SpinGlasses
