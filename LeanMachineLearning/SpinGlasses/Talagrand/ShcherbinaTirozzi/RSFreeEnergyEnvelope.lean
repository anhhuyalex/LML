/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.SaddleEnvelope
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.Convexity
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.HardConstraintUniqueness

/-!
# The Shcherbina--Tirozzi model: envelope derivative and zero-constraint free energy

For the hard-constraint replica-symmetric functional `F (q, ρ)` of Eq. (3.121) (`τ ≥ 0`), this file
formalizes:

* **Zero-load (`α = 0`) evaluation:** at `q₀ = h² / (4 κ²)`, `ρ₀ = (2 κ)⁻¹ + h² / (4 κ²)`, one has
  `0 ≤ q₀ < ρ₀` and `RS₀(0) = log (1 / (2 κ)) / 2 - 1 / 2 + h² / (4 κ)`
  (`shcherbinaTirozziHardFunctional_zero_load`).
* **Talagrand, Lemma 3.3.6 (Eq. (3.130)):** along any continuous curve `(q a, ρ a)` of critical
  points of `F` with `0 < q a < ρ a` (two-sided at `α₀`, or one-sided within a convex set `A`), the
  composite `a ↦ F (a, q a, ρ a)` has derivative `𝔼 log ℙ_ξ (z √(q α₀) + ξ √(ρ α₀ - q α₀) ≥ τ)`
  (`hasDerivAt_shcherbinaTirozziHardFunctional_branch`,
  `hasDerivWithinAt_shcherbinaTirozziHardFunctional_branch`), deduced without assuming
  differentiability of `(q, ρ)` via `hasDerivWithinAt_saddle_envelope` and Corollary 3.3.12.
* **`M = 0` free-energy formula (first step of Theorem 3.3.2, Eq. (3.131)):**
  `N⁻¹ 𝔼 log ∫ exp (-H_{N,0}(σ)) dσ = log (π / κ) / 2 + h² / (4 κ) = RS₀(0) + log (2 e π) / 2`
  (`integral_log_integral_exp_neg_shcherbinaTirozziHamiltonian_zero`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

local notation "mills " v:arg =>
  gaussianPDFReal 0 1 v / Measure.real (gaussianReal 0 1) (Ici v)

/-- Continuity of `(x, ρ) ↦ 𝔼 log ℙ (ξ ≥ τ √(1 + x) / √ρ - √x z)` on `[0, ∞) × (0, ∞)`. -/
theorem continuousOn_integral_log_gaussianTail_ratio (τ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ z, Real.log ((gaussianReal 0 1).real
        (Ici (τ * Real.sqrt (1 + p.1) / Real.sqrt p.2 + -Real.sqrt p.1 * z)))
      ∂(gaussianReal 0 1)) (Ici (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  intro ⟨x₀, ρ₀⟩ ⟨hx₀, hρ₀⟩
  obtain ⟨C, hC0, hC⟩ := exists_abs_log_measureReal_gaussianReal_Ici_le
  set δ : ℝ := min 1 (ρ₀ / 2)
  have hδ0 : 0 < δ := lt_min one_pos (half_pos hρ₀)
  set M : ℝ := |τ| * Real.sqrt (1 + (x₀ + 1)) / Real.sqrt (ρ₀ / 2) + Real.sqrt (x₀ + 1) + 1
  have hM0 : 0 ≤ M := by positivity
  have hdom : Integrable (fun z : ℝ => C * (1 + M * (1 + |z|)) ^ 2) (gaussianReal 0 1) := by
    have hid : MemLp (fun z : ℝ => |z|) 2 (gaussianReal 0 1) := (memLp_id_gaussianReal 2).abs
    have hlin : MemLp (fun z : ℝ => 1 + M * (1 + |z|)) 2 (gaussianReal 0 1) :=
      (memLp_const 1).add (((memLp_const 1).add hid).const_mul M)
    exact (hlin.integrable_sq.const_mul C).congr (ae_of_all _ fun _ => rfl)
  set V : Set (ℝ × ℝ) := (Ici 0 ×ˢ Ioi 0) ∩ Metric.ball (x₀, ρ₀) δ
  have hVmem : V ∈ 𝓝[Ici 0 ×ˢ Ioi 0] (x₀, ρ₀) :=
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hδ0)
  have hbd : ∀ p ∈ V, ∀ z : ℝ,
      |Real.log ((gaussianReal 0 1).real
        (Ici (τ * Real.sqrt (1 + p.1) / Real.sqrt p.2 + -Real.sqrt p.1 * z)))| ≤
        C * (1 + M * (1 + |z|)) ^ 2 := by
    intro ⟨x, ρ⟩ ⟨⟨hx, hρ⟩, hball⟩ z
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hball
    have hx_ub : x ≤ x₀ + 1 := by
      have : |x - x₀| < 1 := hball.1.trans_le (min_le_left _ _)
      linarith [(abs_lt.1 this).2]
    have hρ_lb : ρ₀ / 2 ≤ ρ := by
      have : |ρ - ρ₀| < ρ₀ / 2 := hball.2.trans_le (min_le_right _ _)
      linarith [(abs_lt.1 this).1]
    have hW : |τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z| ≤ M * (1 + |z|) := by
      have h1 : |τ * Real.sqrt (1 + x) / Real.sqrt ρ| ≤
          |τ| * Real.sqrt (1 + (x₀ + 1)) / Real.sqrt (ρ₀ / 2) := by
        rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_pos (Real.sqrt_pos.2 hρ)]
        exact div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (abs_nonneg τ))
          (Real.sqrt_pos.2 (half_pos hρ₀)) (Real.sqrt_le_sqrt hρ_lb)
      have h2 : |-Real.sqrt x * z| ≤ Real.sqrt (x₀ + 1) * |z| := by
        rw [abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx_ub) (abs_nonneg z)
      refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
      have h3 : 0 ≤ |z| := abs_nonneg z
      dsimp only [M]
      nlinarith [Real.sqrt_nonneg (x₀ + 1),
        div_nonneg (mul_nonneg (abs_nonneg τ) (Real.sqrt_nonneg (1 + (x₀ + 1))))
          (Real.sqrt_nonneg (ρ₀ / 2))]
    refine (hC _).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hW) 2) hC0
  have hmeas : ∀ p : ℝ × ℝ, AEStronglyMeasurable (fun z : ℝ =>
      Real.log ((gaussianReal 0 1).real
        (Ici (τ * Real.sqrt (1 + p.1) / Real.sqrt p.2 + -Real.sqrt p.1 * z))))
      (gaussianReal 0 1) := fun p => by
    have hc : Continuous fun v : ℝ => Real.log ((gaussianReal 0 1).real (Ici v)) :=
      continuous_iff_continuousAt.2 fun v =>
        (hasDerivAt_log_measureReal_gaussianReal_Ici v).continuousAt
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  have hpt : ∀ z : ℝ, ContinuousWithinAt (fun p : ℝ × ℝ =>
      Real.log ((gaussianReal 0 1).real
        (Ici (τ * Real.sqrt (1 + p.1) / Real.sqrt p.2 + -Real.sqrt p.1 * z))))
      (Ici 0 ×ˢ Ioi 0) (x₀, ρ₀) := fun z => by
    have hc : Continuous fun v : ℝ => Real.log ((gaussianReal 0 1).real (Ici v)) :=
      continuous_iff_continuousAt.2 fun v =>
        (hasDerivAt_log_measureReal_gaussianReal_Ici v).continuousAt
    have harg : ContinuousAt (fun p : ℝ × ℝ =>
        τ * Real.sqrt (1 + p.1) / Real.sqrt p.2 + -Real.sqrt p.1 * z) (x₀, ρ₀) := by
      refine ContinuousAt.add ?_ (by fun_prop)
      refine ContinuousAt.div (by fun_prop) (by fun_prop) (Real.sqrt_pos.2 hρ₀).ne'
    exact (hc.continuousAt.comp harg).continuousWithinAt
  exact continuousWithinAt_of_dominated (bound := fun z => C * (1 + M * (1 + |z|)) ^ 2)
    (Eventually.of_forall hmeas)
    (eventually_of_mem hVmem fun p hp => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hbd p hp z)
    hdom (ae_of_all _ hpt)

/-- **Talagrand, Lemma 3.3.6 (Eq. (3.130)), along a continuous critical branch on a load set `A`:**
if `A ⊆ [0, ∞)` with `α₀ ∈ A`, `(q a, ρ a)` is continuous within `A` at `α₀` with `0 < q a < ρ a`
and `∂F/∂q (a, q a, ρ a) = 0 = ∂F/∂ρ (a, q a, ρ a)` for `a ∈ A` near `α₀`, then
`a ↦ F (a, q a, ρ a)` has derivative `𝔼 log ℙ_ξ (z √(q α₀) + ξ √(ρ α₀ - q α₀) ≥ τ)` within `A` at
`α₀`. Neither differentiability of `(q, ρ)` nor second derivatives in `ρ` are needed. -/
theorem hasDerivWithinAt_shcherbinaTirozziHardFunctional_branch {A : Set ℝ} {κ h τ α₀ : ℝ}
    (hA0 : ∀ a ∈ A, 0 ≤ a) (hα₀ : α₀ ∈ A) (hτ : 0 ≤ τ)
    {q ρ : ℝ → ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 α₀)
    (hq_pos : ∀ a ∈ A ∩ U, 0 < q a) (hqρ : ∀ a ∈ A ∩ U, q a < ρ a)
    (hcq : ∀ a ∈ A ∩ U, HasDerivAt (fun q' => shcherbinaTirozziHardFunctional a κ h τ q' (ρ a))
      0 (q a))
    (hcρ : ∀ a ∈ A ∩ U, HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional a κ h τ (q a) ρ')
      0 (ρ a))
    (hq_cont : ContinuousWithinAt q A α₀) (hρ_cont : ContinuousWithinAt ρ A α₀) :
    HasDerivWithinAt (fun a => shcherbinaTirozziHardFunctional a κ h τ (q a) (ρ a))
      (∫ z, Real.log ((gaussianReal 0 1).real
          (Ici ((τ - Real.sqrt (q α₀) * z) / Real.sqrt (ρ α₀ - q α₀))))
        ∂(gaussianReal 0 1)) A α₀ := by
  set x : ℝ → ℝ := fun a => q a / (ρ a - q a)
  set G : ℝ → ℝ → ℝ → ℝ := fun a u v =>
    shcherbinaTirozziHardFunctional a κ h τ (u * v / (1 + u)) v
  set G' : ℝ → ℝ → ℝ → ℝ := fun _ u v =>
    ∫ z, Real.log ((gaussianReal 0 1).real
        (Ici (τ * Real.sqrt (1 + u) / Real.sqrt v + -Real.sqrt u * z)))
      ∂(gaussianReal 0 1)
  have ha₀AU : α₀ ∈ A ∩ U := ⟨hα₀, mem_of_mem_nhds hU⟩
  have hq0 : 0 < q α₀ := hq_pos α₀ ha₀AU
  have hqρ0 : q α₀ < ρ α₀ := hqρ α₀ ha₀AU
  have hρ0 : 0 < ρ α₀ := hq0.trans hqρ0
  have hs0 : 0 < ρ α₀ - q α₀ := sub_pos.2 hqρ0
  have hx0 : 0 < x α₀ := div_pos hq0 hs0
  have hqx : ∀ a ∈ A ∩ U, x a * ρ a / (1 + x a) = q a := fun a ha => by
    have hs : (ρ a - q a) ≠ 0 := (sub_pos.2 (hqρ a ha)).ne'
    have h1x : 1 + x a ≠ 0 := (add_pos one_pos (div_pos (hq_pos a ha) (sub_pos.2 (hqρ a ha)))).ne'
    have hρa : ρ a ≠ 0 := ((hq_pos a ha).trans (hqρ a ha)).ne'
    dsimp only [x]; field_simp; ring_nf
    exact mul_inv_cancel_right₀ hρa _
  -- each `(x a, ρ a)` is a saddle point of `G a` on `(0, ∞) × (0, ∞)`
  have hsaddle : ∀ a ∈ A ∩ U, 0 < x a ∧ 0 < ρ a ∧
      (∀ u ∈ Ioi (0 : ℝ), G a (x a) (ρ a) ≤ G a u (ρ a)) ∧
      (∀ v ∈ Ioi (0 : ℝ), G a (x a) v ≤ G a (x a) (ρ a)) := by
    intro a ha
    have hqa := hq_pos a ha
    have hqρa := hqρ a ha
    have hρa : 0 < ρ a := hqa.trans hqρa
    have hsa : 0 < ρ a - q a := sub_pos.2 hqρa
    have hxa : 0 < x a := div_pos hqa hsa
    have h1xa : 0 < 1 + x a := by linarith
    have hGx : HasDerivAt (fun u => G a u (ρ a)) 0 (x a) := by
      have hinner : HasDerivAt (fun u : ℝ => u * ρ a / (1 + u)) (ρ a / (1 + x a) ^ 2) (x a) := by
        refine (((hasDerivAt_id (x a)).mul_const (ρ a)).div ((hasDerivAt_id (x a)).const_add 1)
          h1xa.ne').congr_deriv ?_
        simp only [id_eq]; ring
      have h0 : HasDerivAt (fun q' => shcherbinaTirozziHardFunctional a κ h τ q' (ρ a)) 0
          (x a * ρ a / (1 + x a)) := by rw [hqx a ha]; exact hcq a ha
      simpa only [zero_mul, Function.comp_def] using h0.comp (x a) hinner
    have hGρ : HasDerivAt (fun v => G a (x a) v) 0 (ρ a) := by
      -- relate `∂_ρ F` and `∂_ρ G` at a point where `∂_x G = 0`
      have hK := (hasDerivAt_shcherbinaTirozziHardFunctional_ratio a κ h τ hxa hρa).unique hGx
      replace hK := (mul_eq_zero.1 hK).resolve_left (div_pos hxa (by linarith)).ne'
      -- evaluate `∂_ρ F` directly via `shcherbinaTirozziHardFunctional`
      set m : ℝ → ℝ := fun r => τ / Real.sqrt (r - q a)
      set σ : ℝ → ℝ := fun r => -Real.sqrt (q a) / Real.sqrt (r - q a)
      set m' : ℝ → ℝ := fun r => -(τ / (2 * (r - q a) * Real.sqrt (r - q a)))
      set σ' : ℝ → ℝ := fun r => Real.sqrt (q a) / (2 * (r - q a) * Real.sqrt (r - q a))
      have hquot : ∀ c r : ℝ, q a < r → HasDerivAt (fun r => c / Real.sqrt (r - q a))
          (-(c / (2 * (r - q a) * Real.sqrt (r - q a)))) r := fun c r hr => by
        have hr0 : 0 < r - q a := sub_pos.2 hr
        have hsr := (Real.sqrt_pos.2 hr0).ne'
        have h1 : HasDerivAt (fun r => Real.sqrt (r - q a)) (1 / (2 * Real.sqrt (r - q a))) r := by
          simpa using ((hasDerivAt_id r).sub_const (q a)).sqrt hr0.ne'
        refine ((hasDerivAt_const r c).div h1 hsr).congr_deriv ?_
        rw [Real.sq_sqrt hr0.le]; field_simp; ring
      have hden : 2 * (ρ a - q a) * Real.sqrt (ρ a - q a) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero hsa.ne') (Real.sqrt_pos.2 hsa).ne'
      have hdenc : ContinuousAt (fun r : ℝ => 2 * (r - q a) * Real.sqrt (r - q a)) (ρ a) := by
        fun_prop
      have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := σ) (m' := m') (σ' := σ')
        (t := ρ a) ((eventually_gt_nhds hqρa).mono fun r hr => hquot τ r hr)
        ((eventually_gt_nhds hqρa).mono fun r hr =>
          (hquot (-Real.sqrt (q a)) r hr).congr_deriv (by dsimp only [σ']; ring))
        (ContinuousAt.neg (ContinuousAt.div continuousAt_const hdenc hden))
        (ContinuousAt.div continuousAt_const hdenc hden)
      have hrest : HasDerivAt (fun r => q a / (2 * (r - q a)) + Real.log (r - q a) / 2 - κ * r +
          h ^ 2 * (r - q a) / 2)
          (-(q a / (2 * (ρ a - q a) ^ 2)) + (ρ a - q a)⁻¹ / 2 - κ + h ^ 2 / 2) (ρ a) := by
        have h0 : HasDerivAt (fun r : ℝ => r - q a) 1 (ρ a) := (hasDerivAt_id (ρ a)).sub_const (q a)
        have h1 := (hasDerivAt_const (ρ a) (q a)).div (h0.const_mul 2)
          (mul_ne_zero two_ne_zero hsa.ne')
        have h2 := (h0.log hsa.ne').div_const 2
        have h3 := (hasDerivAt_id (ρ a)).const_mul κ
        have h4 := (h0.const_mul (h ^ 2)).div_const 2
        refine (((h1.add h2).sub h3).add h4).congr_deriv ?_
        field_simp; ring
      have hFd : HasDerivAt (fun r => shcherbinaTirozziHardFunctional a κ h τ (q a) r)
          (a * (∫ z, -(mills (m (ρ a) + σ (ρ a) * z)) * (m' (ρ a) + σ' (ρ a) * z)
              ∂(gaussianReal 0 1)) +
            (-(q a / (2 * (ρ a - q a) ^ 2)) + (ρ a - q a)⁻¹ / 2 - κ + h ^ 2 / 2)) (ρ a) := by
        refine ((hE.const_mul a).add hrest).congr_of_eventuallyEq
          (Eventually.of_forall fun r => ?_)
        have e : ∀ z : ℝ, (τ - Real.sqrt (q a) * z) / Real.sqrt (r - q a) = m r + σ r * z :=
          fun z => by dsimp only [m, σ]; ring
        simp only [shcherbinaTirozziHardFunctional, e, Pi.add_apply]; ring
      have hF0 := hFd.unique (hcρ a ha)
      have hs_eq : ρ a - q a = ρ a / (1 + x a) := by
        have := h1xa.ne'; have := hsa.ne'; dsimp only [x]; field_simp; ring
      have hsq : Real.sqrt (ρ a - q a) = Real.sqrt (ρ a) / Real.sqrt (1 + x a) := by
        rw [hs_eq, Real.sqrt_div' _ h1xa.le]
      have hmρ : m (ρ a) = τ * Real.sqrt (1 + x a) / Real.sqrt (ρ a) := by
        have := (Real.sqrt_pos.2 hρa).ne'; have := (Real.sqrt_pos.2 h1xa).ne'
        dsimp only [m]; rw [hsq]; field_simp
      have hsqq : Real.sqrt (q a) = Real.sqrt (x a) * (Real.sqrt (ρ a) / Real.sqrt (1 + x a)) := by
        rw [← hqx a ha, Real.sqrt_div' _ h1xa.le, Real.sqrt_mul hxa.le, mul_div_assoc]
      have hσρ : σ (ρ a) = -Real.sqrt (x a) := by
        have := (Real.sqrt_pos.2 hρa).ne'; have := (Real.sqrt_pos.2 h1xa).ne'
        dsimp only [σ]; rw [hsq, hsqq]; field_simp
      obtain ⟨hi, hzi, -⟩ :=
        integrable_gaussianPDFReal_div_measureReal_Ici_comp (m (ρ a)) (σ (ρ a))
      have hder : ∫ z, -(mills (m (ρ a) + σ (ρ a) * z)) * (m' (ρ a) + σ' (ρ a) * z)
          ∂(gaussianReal 0 1) =
          -(m' (ρ a)) * (∫ z, mills (m (ρ a) + σ (ρ a) * z) ∂(gaussianReal 0 1)) +
            -(σ' (ρ a)) * ∫ z, z * mills (m (ρ a) + σ (ρ a) * z) ∂(gaussianReal 0 1) := by
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add (hi.const_mul _) (hzi.const_mul _)]
        exact integral_congr_ae (ae_of_all _ fun z => by ring)
      set I1 := ∫ z, mills (m (ρ a) + σ (ρ a) * z) ∂(gaussianReal 0 1)
      set I2 := ∫ z, mills (m (ρ a) + σ (ρ a) * z) ^ 2 ∂(gaussianReal 0 1)
      set J := ∫ z, z * mills (m (ρ a) + σ (ρ a) * z) ∂(gaussianReal 0 1)
      have hsx2 : Real.sqrt (x a) ^ 2 = x a := Real.sq_sqrt hxa.le
      have hJeq : J = -Real.sqrt (x a) * (I2 - m (ρ a) * I1) / (1 + x a) := by
        rw [eq_div_iff h1xa.ne', ← hσρ]
        have h1 := one_add_sq_mul_integral_id_mul_gaussianPDFReal_div_measureReal_Ici
          (m (ρ a)) (σ (ρ a))
        have h2 : σ (ρ a) ^ 2 = x a := by rw [hσρ, neg_sq, hsx2]
        linear_combination h1 - J * h2
      have hm'ρ : m' (ρ a) = -(m (ρ a) / (2 * (ρ a - q a))) := by
        dsimp only [m', m]; rw [div_div, mul_comm (Real.sqrt (ρ a - q a))]
      have hσ'ρ : σ' (ρ a) = Real.sqrt (x a) / (2 * (ρ a - q a)) := by
        have : σ' (ρ a) = -(σ (ρ a)) / (2 * (ρ a - q a)) := by
          dsimp only [σ', σ]
          rw [neg_div (Real.sqrt (ρ a - q a)) (Real.sqrt (q a)), neg_neg, div_div,
            mul_comm (Real.sqrt (ρ a - q a))]
        rw [this, hσρ, neg_neg]
      have e1 : -(m' (ρ a)) * I1 + -(σ' (ρ a)) * J = (m (ρ a) * I1 + x a * I2) / (2 * ρ a) := by
        have := hρa.ne'; have := h1xa.ne'
        rw [hm'ρ, hσ'ρ, hJeq, hs_eq]
        calc _ = ((1 + x a) * (m (ρ a) * I1) + Real.sqrt (x a) ^ 2 * (I2 - m (ρ a) * I1)) /
              (2 * ρ a) := by field_simp
          _ = (m (ρ a) * I1 + x a * I2) / (2 * ρ a) := by rw [hsx2]; ring
      have e2 : -(q a / (2 * (ρ a - q a) ^ 2)) + (ρ a - q a)⁻¹ / 2 =
          (1 - x a) * (1 + x a) / (2 * ρ a) := by
        have := hρa.ne'; have := h1xa.ne'
        rw [hs_eq, ← hqx a ha]; field_simp; ring
      rw [hder, e1, e2] at hF0
      refine (hasDerivAt_shcherbinaTirozziHardFunctional_self a κ h τ hxa.le hρa).congr_deriv ?_
      have hI1' : ∫ z, mills (τ * Real.sqrt (1 + x a) / Real.sqrt (ρ a) + -Real.sqrt (x a) * z)
          ∂(gaussianReal 0 1) = I1 := by rw [← hmρ, ← hσρ]
      have hI2' : ∫ z, mills (τ * Real.sqrt (1 + x a) / Real.sqrt (ρ a) + -Real.sqrt (x a) * z) ^ 2
          ∂(gaussianReal 0 1) = I2 := by rw [← hmρ, ← hσρ]
      rw [hI1']
      rw [hI2'] at hK
      have key : (a * τ * Real.sqrt (1 + x a) / (ρ a * Real.sqrt (ρ a)) * I1 + (ρ a)⁻¹ - 2 * κ +
            h ^ 2 / (1 + x a)) / 2 =
          (a * ((m (ρ a) * I1 + x a * I2) / (2 * ρ a)) +
            ((1 - x a) * (1 + x a) / (2 * ρ a) - κ + h ^ 2 / 2)) +
            x a ^ 2 / (2 * ρ a) * (1 - a * I2 / x a - h ^ 2 * ρ a / (x a * (1 + x a))) := by
        rw [hmρ]
        have := hxa.ne'; have := hρa.ne'; have := h1xa.ne'
        have := (Real.sqrt_pos.2 hρa).ne'
        field_simp; ring
      rw [key, hF0, hK]; ring
    refine ⟨hxa, hρa, fun u hu => ?_, fun v hv => ?_⟩
    · rcases eq_or_ne u (x a) with rfl | hne
      · exact le_rfl
      · exact (shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h
          (hA0 a ha.1) hτ hxa hρa hu hne hGx).le
    · rcases eq_or_ne v (ρ a) with rfl | hne
      · exact le_rfl
      · exact (shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero κ h
          (hA0 a ha.1) hτ hxa.le hρa hv hne hGρ).le
  have hx_cont : ContinuousWithinAt x A α₀ :=
    hq_cont.div (hρ_cont.sub hq_cont) hs0.ne'
  have hd : ∀ b ∈ U, ∀ u ∈ Ioi (0 : ℝ), ∀ v ∈ Ioi (0 : ℝ),
      HasDerivAt (fun c => G c u v) (G' b u v) b := by
    intro b _ u hu v hv
    have heq : (fun c => G c u v) = fun c => c * G' b u v +
        (u / 2 + (Real.log v - Real.log (1 + u)) / 2 - κ * v + h ^ 2 * v / (2 * (1 + u))) := by
      funext c
      dsimp only [G, G']
      rw [shcherbinaTirozziHardFunctional_ratio_eq c κ h τ hu.le hv]
      ring
    rw [heq]
    exact (((hasDerivAt_id b).mul_const (G' b u v)).add_const
      (u / 2 + (Real.log v - Real.log (1 + u)) / 2 - κ * v + h ^ 2 * v / (2 * (1 + u)))).congr_deriv
      (one_mul _)
  have hcont : ContinuousAt (fun p : ℝ × ℝ × ℝ => G' p.1 p.2.1 p.2.2) (α₀, x α₀, ρ α₀) := by
    have hc : ContinuousWithinAt (fun q : ℝ × ℝ => ∫ z, Real.log ((gaussianReal 0 1).real
        (Ici (τ * Real.sqrt (1 + q.1) / Real.sqrt q.2 + -Real.sqrt q.1 * z)))
        ∂(gaussianReal 0 1)) (Ici 0 ×ˢ Ioi 0) (x α₀, ρ α₀) :=
      continuousOn_integral_log_gaussianTail_ratio τ (x α₀, ρ α₀) ⟨hx0.le, hρ0⟩
    have hc_at : ContinuousAt (fun q : ℝ × ℝ => ∫ z, Real.log ((gaussianReal 0 1).real
        (Ici (τ * Real.sqrt (1 + q.1) / Real.sqrt q.2 + -Real.sqrt q.1 * z)))
        ∂(gaussianReal 0 1)) (x α₀, ρ α₀) :=
      hc.continuousAt (prod_mem_nhds (Ici_mem_nhds hx0) (Ioi_mem_nhds hρ0))
    exact ContinuousAt.comp (x := (α₀, x α₀, ρ α₀)) (f := Prod.snd) hc_at continuousAt_snd
  have henv := hasDerivWithinAt_saddle_envelope (S := Ioi 0) (T := Ioi 0)
    hα₀ hU (Ioi_mem_nhds hx0) (Ioi_mem_nhds hρ0)
    (fun a ha => ⟨(hsaddle a ha).1, (hsaddle a ha).2.1⟩)
    (fun a ha => (hsaddle a ha).2.2.1)
    (fun a ha => (hsaddle a ha).2.2.2)
    hx_cont hρ_cont hd hcont
  have hcongr : (fun a => shcherbinaTirozziHardFunctional a κ h τ (q a) (ρ a)) =ᶠ[𝓝[A] α₀]
      fun a => G a (x a) (ρ a) := by
    filter_upwards [inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hU)] with a ha
    dsimp only [G]
    rw [hqx a ⟨ha.1, ha.2⟩]
  have hval : shcherbinaTirozziHardFunctional α₀ κ h τ (q α₀) (ρ α₀) = G α₀ (x α₀) (ρ α₀) := by
    dsimp only [G]; rw [hqx α₀ ha₀AU]
  have hderiv_eq : G' α₀ (x α₀) (ρ α₀) = ∫ z, Real.log ((gaussianReal 0 1).real
      (Ici ((τ - Real.sqrt (q α₀) * z) / Real.sqrt (ρ α₀ - q α₀)))) ∂(gaussianReal 0 1) := by
    dsimp only [G']
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have h1x : 0 < 1 + x α₀ := by linarith
    have hs_eq : ρ α₀ - q α₀ = ρ α₀ / (1 + x α₀) := by
      have := h1x.ne'; have := hs0.ne'; dsimp only [x]; field_simp; ring
    have hW : (τ - Real.sqrt (q α₀) * z) / Real.sqrt (ρ α₀ - q α₀) =
        τ * Real.sqrt (1 + x α₀) / Real.sqrt (ρ α₀) + -Real.sqrt (x α₀) * z := by
      rw [hs_eq, ← hqx α₀ ha₀AU, Real.sqrt_div' _ h1x.le, Real.sqrt_div' _ h1x.le,
        Real.sqrt_mul hx0.le]
      have := (Real.sqrt_pos.2 h1x).ne'; have := (Real.sqrt_pos.2 hρ0).ne'
      field_simp; ring
    simp only [hW]
  rw [← hderiv_eq]
  exact henv.congr_of_eventuallyEq hcongr hval

/-- **Talagrand, Lemma 3.3.6 (Eq. (3.130)), two-sided interior form:** if `0 < α₀`, `(q, ρ)` is
continuous at `α₀`, and for `a` near `α₀` one has `0 < q a < ρ a` and
`∂F/∂q (a, q a, ρ a) = 0 = ∂F/∂ρ (a, q a, ρ a)`, then `a ↦ F (a, q a, ρ a)` has derivative
`𝔼 log ℙ_ξ (z √(q α₀) + ξ √(ρ α₀ - q α₀) ≥ τ)` at `α₀`. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_branch {κ h τ α₀ : ℝ}
    (hα₀ : 0 < α₀) (hτ : 0 ≤ τ) {q ρ : ℝ → ℝ}
    (hq_pos : ∀ᶠ a in 𝓝 α₀, 0 < q a) (hqρ : ∀ᶠ a in 𝓝 α₀, q a < ρ a)
    (hcq : ∀ᶠ a in 𝓝 α₀,
      HasDerivAt (fun q' => shcherbinaTirozziHardFunctional a κ h τ q' (ρ a)) 0 (q a))
    (hcρ : ∀ᶠ a in 𝓝 α₀,
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional a κ h τ (q a) ρ') 0 (ρ a))
    (hq_cont : ContinuousAt q α₀) (hρ_cont : ContinuousAt ρ α₀) :
    HasDerivAt (fun a => shcherbinaTirozziHardFunctional a κ h τ (q a) (ρ a))
      (∫ z, Real.log ((gaussianReal 0 1).real
          (Ici ((τ - Real.sqrt (q α₀) * z) / Real.sqrt (ρ α₀ - q α₀))))
        ∂(gaussianReal 0 1)) α₀ := by
  set U := {a | 0 < q a ∧ q a < ρ a ∧
    HasDerivAt (fun q' => shcherbinaTirozziHardFunctional a κ h τ q' (ρ a)) 0 (q a) ∧
    HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional a κ h τ (q a) ρ') 0 (ρ a)}
  have hUmem : U ∈ 𝓝 α₀ := hq_pos.and (hqρ.and (hcq.and hcρ))
  have hhd := hasDerivWithinAt_shcherbinaTirozziHardFunctional_branch (A := Ici 0)
    (fun _ ha => ha) hα₀.le hτ hUmem
    (fun a ha => ha.2.1) (fun a ha => ha.2.2.1) (fun a ha => ha.2.2.2.1) (fun a ha => ha.2.2.2.2)
    hq_cont.continuousWithinAt hρ_cont.continuousWithinAt
  exact hhd.hasDerivAt (Ici_mem_nhds hα₀)

/-- **Zero-load (`α = 0`) value of the hard replica-symmetric functional** (first display in the
proof of Theorem 3.3.2): at `q₀ = h² / (4 κ²)`, `ρ₀ = (2 κ)⁻¹ + h² / (4 κ²)` (`κ > 0`), one has
`0 ≤ q₀ < ρ₀`, `F (0, q₀, ρ₀) = log ((2 κ)⁻¹) / 2 - 1 / 2 + h² / (4 κ)`, and
`F (0, q₀, ρ₀) + log (2 e π) / 2 = log (π / κ) / 2 + h² / (4 κ)`. -/
theorem shcherbinaTirozziHardFunctional_zero_load {κ : ℝ} (hκ : 0 < κ) (h τ : ℝ) :
    let q₀ : ℝ := h ^ 2 / (4 * κ ^ 2)
    let ρ₀ : ℝ := (2 * κ)⁻¹ + h ^ 2 / (4 * κ ^ 2)
    0 ≤ q₀ ∧ q₀ < ρ₀ ∧
      shcherbinaTirozziHardFunctional 0 κ h τ q₀ ρ₀ =
        Real.log (2 * κ)⁻¹ / 2 - 1 / 2 + h ^ 2 / (4 * κ) ∧
      shcherbinaTirozziHardFunctional 0 κ h τ q₀ ρ₀ + Real.log (2 * Real.exp 1 * π) / 2 =
        Real.log (π / κ) / 2 + h ^ 2 / (4 * κ) := by
  intro q₀ ρ₀
  have hq₀ : 0 ≤ q₀ := by dsimp only [q₀]; positivity
  have hgap : ρ₀ - q₀ = (2 * κ)⁻¹ := by dsimp only [q₀, ρ₀]; ring
  have hqρ : q₀ < ρ₀ := sub_pos.1 (hgap ▸ inv_pos.2 (by positivity))
  have hval : shcherbinaTirozziHardFunctional 0 κ h τ q₀ ρ₀ =
      Real.log (2 * κ)⁻¹ / 2 - 1 / 2 + h ^ 2 / (4 * κ) := by
    unfold shcherbinaTirozziHardFunctional
    rw [zero_mul, zero_add, hgap]
    dsimp only [q₀, ρ₀]
    have := hκ.ne'
    field_simp
    ring
  refine ⟨hq₀, hqρ, hval, ?_⟩
  rw [hval, Real.log_inv, Real.log_mul two_ne_zero hκ.ne',
    Real.log_mul (mul_ne_zero two_ne_zero (Real.exp_pos 1).ne') Real.pi_ne_zero,
    Real.log_mul two_ne_zero (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_div Real.pi_ne_zero hκ.ne']
  ring

/-- **Free energy at `M = 0` constraints** (first step of the proof of Theorem 3.3.2, Eq. (3.131)):
for `κ > 0` and `N ≥ 1`,
`N⁻¹ 𝔼 log ∫ exp (-H_{N,0}(σ)) dσ = log (π / κ) / 2 + h² / (4 κ)`. -/
theorem integral_log_integral_exp_neg_shcherbinaTirozziHamiltonian_zero {N : ℕ} (hN : 1 ≤ N)
    {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (u : ℝ → ℝ) :
    let P : Measure ((Fin 0 → Fin N → ℝ) × (Fin N → ℝ)) :=
      (Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    Integrable (fun d : (Fin 0 → Fin N → ℝ) × (Fin N → ℝ) =>
        Real.log (∫ σ : ℝ^N, Real.exp (-shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ))) P ∧
      (N : ℝ)⁻¹ * (∫ d, Real.log (∫ σ : ℝ^N,
          Real.exp (-shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ)) ∂P) =
        Real.log (π / κ) / 2 + h ^ 2 / (4 * κ) := by
  intro P
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpiκ : 0 < π / κ := div_pos Real.pi_pos hκ
  -- evaluate the partition function explicitly for each disorder `d`
  have hZ : ∀ d : (Fin 0 → Fin N → ℝ) × (Fin N → ℝ),
      Real.log (∫ σ : ℝ^N, Real.exp (-shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ)) =
        (N : ℝ) / 2 * Real.log (π / κ) + h ^ 2 / (4 * κ) * ∑ i : Fin N, d.2 i ^ 2 := by
    intro d
    set a : ℝ^N := WithLp.toLp 2 (fun i : Fin N => h * d.2 i)
    have hH : ∀ σ : ℝ^N, -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ =
        -κ * ‖σ‖ ^ 2 + ⟪a, σ⟫ := fun σ => by
      rw [neg_shcherbinaTirozziHamiltonian_eq, Finset.univ_eq_empty, Finset.sum_empty, zero_sub,
        neg_mul]
    have ha_norm : ‖a‖ ^ 2 = h ^ 2 * ∑ i : Fin N, d.2 i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by change (h * d.2 i) ^ 2 = _; ring
    simp_rw [hH]
    rw [integral_exp_neg_mul_sq_norm_add_inner hκ a, finrank_euclideanSpace_fin,
      Real.log_mul (Real.rpow_pos_of_pos hpiκ _).ne' (Real.exp_pos _).ne',
      Real.log_rpow hpiκ, Real.log_exp, ha_norm]
    ring
  simp_rw [hZ]
  set Pg0 : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1
  have hmp : ∀ i : Fin N, MeasurePreserving
      (fun d : (Fin 0 → Fin N → ℝ) × (Fin N → ℝ) => d.2 i) P (gaussianReal 0 1) := fun i =>
    (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).comp measurePreserving_snd
  have hsq_i : ∀ i : Fin N, Integrable (fun d : (Fin 0 → Fin N → ℝ) × (Fin N → ℝ) => d.2 i ^ 2)
      P := fun i => by
    have h1 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
    exact (hmp i).integrable_comp_of_integrable h1
  have hsum_i : Integrable (fun d : (Fin 0 → Fin N → ℝ) × (Fin N → ℝ) => ∑ i, d.2 i ^ 2) P :=
    integrable_finsetSum _ fun i _ => hsq_i i
  have hint : Integrable (fun d : (Fin 0 → Fin N → ℝ) × (Fin N → ℝ) =>
      (N : ℝ) / 2 * Real.log (π / κ) + h ^ 2 / (4 * κ) * ∑ i, d.2 i ^ 2) P :=
    (integrable_const _).add (hsum_i.const_mul _)
  refine ⟨hint, ?_⟩
  have hsq_val : ∀ i : Fin N, ∫ d, d.2 i ^ 2 ∂P = 1 := fun i => by
    have h2 : ∫ d, d.2 i ^ 2 ∂P = ∫ x, x ^ 2 ∂(gaussianReal 0 1) := by
      rw [← (hmp i).map_eq]
      exact (integral_map (f := fun x : ℝ => x ^ 2) (hmp i).measurable.aemeasurable
        (by fun_prop)).symm
    rw [h2]
    simpa using integral_pow_add_two_gaussianReal 0
  rw [integral_add (integrable_const _) (hsum_i.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ fun i _ => hsq_i i]
  simp only [hsq_val, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

end SpinGlasses
