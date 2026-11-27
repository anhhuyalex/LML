/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.SaddleEnvelope
public import LeanMachineLearning.ForMathlib.Order.StrictSaddle
public import Mathlib.Analysis.Calculus.Darboux
public import Mathlib.Analysis.Convex.Deriv
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.Convexity
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.HardConstraintUniqueness

/-!
# The Shcherbina--Tirozzi model: envelope derivative and zero-constraint free energy

For the hard-constraint replica-symmetric functional `F (q, ρ)` of Eq. (3.121) (`τ ≥ 0`), this file
formalizes:

* **Zero-load (`α = 0`) evaluation:** at `q₀ = h² / (4 κ²)`, `ρ₀ = (2 κ)⁻¹ + h² / (4 κ²)`, one has
  `0 ≤ q₀ < ρ₀` and `RS₀(0) = log (1 / (2 κ)) / 2 - 1 / 2 + h² / (4 κ)`
  (`shcherbinaTirozziHardFunctional_zero_load`).
* **Continuity of the critical branch:** critical points `(q a, ρ a)` of `F` with
  `0 < q a < ρ a` are continuous in the load `a`
  (`continuousWithinAt_shcherbinaTirozziHardFunctional_critical`).
* **Talagrand, Lemma 3.3.6 (Eq. (3.130)):** along any curve `(q a, ρ a)` of critical
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

/-- **Critical points depend continuously on the load:** if `α₀ ∈ A ⊆ [0, ∞)` and, for `a ∈ A`
near `α₀`, `(q a, ρ a)` is a critical point of `F (a, ·, ·)` with `0 < q a < ρ a`, then `q` and `ρ`
are continuous within `A` at `α₀`. No regularity of the branch is assumed: the strict saddle
structure of Corollary 3.3.12 confines the critical points of nearby loads. -/
theorem continuousWithinAt_shcherbinaTirozziHardFunctional_critical {A : Set ℝ} {κ h τ α₀ : ℝ}
    (hA0 : ∀ a ∈ A, 0 ≤ a) (hα₀ : α₀ ∈ A) (hτ : 0 ≤ τ)
    {q ρ : ℝ → ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 α₀)
    (hq_pos : ∀ a ∈ A ∩ U, 0 < q a) (hqρ : ∀ a ∈ A ∩ U, q a < ρ a)
    (hcq : ∀ a ∈ A ∩ U, HasDerivAt (fun q' => shcherbinaTirozziHardFunctional a κ h τ q' (ρ a))
      0 (q a))
    (hcρ : ∀ a ∈ A ∩ U, HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional a κ h τ (q a) ρ')
      0 (ρ a)) :
    ContinuousWithinAt q A α₀ ∧ ContinuousWithinAt ρ A α₀ := by
  -- in the variables `x = q / (ρ - q)` and `ρ` each critical point is a strict saddle point
  set x : ℝ → ℝ := fun a => q a / (ρ a - q a)
  set G : ℝ → ℝ → ℝ → ℝ := fun a u v =>
    shcherbinaTirozziHardFunctional a κ h τ (u * v / (1 + u)) v
  -- the load enters `G` affinely, with coefficient `T`
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ → ℝ, T = fun u v => ∫ z, Real.log ((gaussianReal 0 1).real
      (Ici (τ * Real.sqrt (1 + u) / Real.sqrt v + -Real.sqrt u * z))) ∂(gaussianReal 0 1) :=
    ⟨_, rfl⟩
  have hTc : ContinuousOn (fun p : ℝ × ℝ => T p.1 p.2) (Ici 0 ×ˢ Ioi 0) := by
    rw [hT]; exact continuousOn_integral_log_gaussianTail_ratio τ
  set B : ℝ → ℝ → ℝ := fun u v =>
    u / 2 + (Real.log v - Real.log (1 + u)) / 2 - κ * v + h ^ 2 * v / (2 * (1 + u))
  have hG : ∀ a u v, 0 ≤ u → 0 < v → G a u v = a * T u v + B u v := fun a u v hu hv => by
    dsimp only [G, B]
    rw [hT, shcherbinaTirozziHardFunctional_ratio_eq a κ h τ hu hv]
    ring
  have hcrit : ∀ a ∈ A ∩ U, 0 < x a ∧ q a = x a * ρ a / (1 + x a) ∧
      HasDerivAt (fun u => G a u (ρ a)) 0 (x a) ∧ HasDerivAt (fun v => G a (x a) v) 0 (ρ a) :=
    fun a ha => shcherbinaTirozziHardFunctional_ratio_critical a κ h τ (hq_pos a ha)
      (hqρ a ha) (hcq a ha) (hcρ a ha)
  have ha₀ : α₀ ∈ A ∩ U := ⟨hα₀, mem_of_mem_nhds hU⟩
  obtain ⟨hx0, hqx0, hdx0, hdρ0⟩ := hcrit α₀ ha₀
  have hρ0 : 0 < ρ α₀ := (hq_pos _ ha₀).trans (hqρ _ ha₀)
  have hmem : ∀ᶠ a in 𝓝[A] α₀, a ∈ A ∩ U :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hU)
  have hid : Tendsto (fun a : ℝ => a) (𝓝[A] α₀) (𝓝 α₀) := nhdsWithin_le_nhds
  -- `G a u (r a)` converges when `r a → ρ α₀`
  have hGt : ∀ u, 0 < u → ∀ r : ℝ → ℝ, Tendsto r (𝓝[A] α₀) (𝓝 (ρ α₀)) →
      Tendsto (fun a => G a u (r a)) (𝓝[A] α₀) (𝓝 (G α₀ u (ρ α₀))) := fun u hu r hr => by
    have hT : ContinuousAt (fun p : ℝ × ℝ => T p.1 p.2) (u, ρ α₀) :=
      hTc.continuousAt (prod_mem_nhds (Ici_mem_nhds hu) (Ioi_mem_nhds hρ0))
    have hB : ContinuousAt (B u) (ρ α₀) := by
      dsimp only [B]
      fun_prop (disch := exact hρ0.ne')
    rw [hG α₀ u _ hu.le hρ0]
    refine ((hid.mul (hT.tendsto.comp (tendsto_const_nhds.prodMk_nhds hr))).add
      (hB.tendsto.comp hr)).congr' ?_
    filter_upwards [hr.eventually_const_lt hρ0] with a ha
    exact (hG a u _ hu.le ha).symm
  -- no `r₁ ≠ ρ α₀` lies between `ρ α₀` and `ρ a` for `a` near `α₀`
  have hside : ∀ r₁, 0 < r₁ → r₁ ≠ ρ α₀ → ∀ᶠ a in 𝓝[A] α₀, r₁ ∉ uIcc (ρ α₀) (ρ a) := by
    intro r₁ hr₁ hne
    set K : ℝ → ℝ → ℝ := fun a u => 1 - a * (∫ z, mills (τ * Real.sqrt (1 + u) /
      Real.sqrt (ρ α₀) + -Real.sqrt u * z) ^ 2 ∂(gaussianReal 0 1)) / u -
      h ^ 2 * ρ α₀ / (u * (1 + u))
    have hd : ∀ a u, 0 < u → HasDerivAt (fun u => G a u (ρ α₀)) (u / (2 * (1 + u)) * K a u) u :=
      fun a u hu => hasDerivAt_shcherbinaTirozziHardFunctional_ratio a κ h τ hu hρ0
    have hK0 : K α₀ (x α₀) = 0 :=
      (mul_eq_zero.1 ((hd α₀ _ hx0).unique hdx0)).resolve_left
        (div_pos hx0 (by linarith)).ne'
    have hmono : StrictMonoOn (K α₀) (Ioi 0) := by
      refine strictMonoOn_shcherbinaTirozziHardFunctional_ratio_deriv (hA0 α₀ hα₀) hτ hρ0 ?_
      by_contra hcon
      push Not at hcon
      simp [K, hcon.1, hcon.2] at hK0
    have hKt : ∀ u, Tendsto (fun a => K a u) (𝓝[A] α₀) (𝓝 (K α₀ u)) := fun u =>
      (((hid.mul_const _).div_const u).const_sub 1).sub_const _
    have hl : 0 < x α₀ / 2 := half_pos hx0
    have hlr : x α₀ / 2 ≤ 3 * x α₀ / 2 := by linarith
    have hlo : ∀ᶠ a in 𝓝[A] α₀, K a (x α₀ / 2) < 0 := (hKt _).eventually_lt_const
      ((hmono hl hx0 (half_lt_self hx0)).trans_eq hK0)
    have hhi : ∀ᶠ a in 𝓝[A] α₀, 0 < K a (3 * x α₀ / 2) := (hKt _).eventually_const_lt
      (hK0.symm.trans_lt (hmono hx0 (hl.trans_le hlr) (by linarith)))
    have hTI : ContinuousOn (fun u => T u (ρ α₀)) (Icc (x α₀ / 2) (3 * x α₀ / 2)) :=
      hTc.comp (f := fun u => (u, ρ α₀)) (by fun_prop)
        fun u hu => ⟨(hl.trans_le hu.1).le, hρ0⟩
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hTI
    have hgap : G α₀ (x α₀) r₁ < G α₀ (x α₀) (ρ α₀) :=
      shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero κ h (hA0 α₀ hα₀) hτ hx0.le hρ0
        hr₁ hne hdρ0
    have hnear : ∀ᶠ a in 𝓝[A] α₀,
        G a (x α₀) r₁ + C * |a - α₀| < G α₀ (x α₀) (ρ α₀) := by
      have ht : Tendsto (fun a => a * T (x α₀) r₁ + B (x α₀) r₁ + C * |a - α₀|) (𝓝[A] α₀)
          (𝓝 (α₀ * T (x α₀) r₁ + B (x α₀) r₁ + C * |α₀ - α₀|)) :=
        ((hid.mul_const _).add_const _).add ((hid.sub_const α₀).abs.const_mul C)
      rw [sub_self, abs_zero, mul_zero, add_zero, ← hG α₀ _ _ hx0.le hr₁] at ht
      filter_upwards [ht.eventually_lt_const hgap] with a ha
      rwa [hG a _ _ hx0.le hr₁]
    filter_upwards [hmem, hlo, hhi, hnear] with a ha hlo hhi hnear
    have ha0 : 0 ≤ a := hA0 a ha.1
    -- a critical point of `G a (·, ρ α₀)` near `x α₀`, by Darboux's theorem
    obtain ⟨u, hu, hu0⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt (m := 0) hlr
      (fun u hu => (hd a u (hl.trans_le hu.1)).hasDerivWithinAt)
      (mul_neg_of_pos_of_neg (div_pos hl (by linarith)) hlo)
      (mul_pos (div_pos (hl.trans_le hlr) (by linarith)) hhi)
    have hupos : 0 < u := hl.trans hu.1
    have hmin : ∀ u' ∈ Ioi (0 : ℝ), G a u (ρ α₀) ≤ G a u' (ρ α₀) := fun u' hu' => by
      rcases eq_or_ne u' u with rfl | hne'
      · exact le_rfl
      · exact (shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h ha0 hτ hupos hρ0
          hu' hne' ((hd a u hupos).congr_deriv hu0)).le
    have hlow : G α₀ (x α₀) (ρ α₀) - C * |a - α₀| ≤ G a u (ρ α₀) := by
      have h0 : G α₀ (x α₀) (ρ α₀) ≤ G α₀ u (ρ α₀) := by
        rcases eq_or_ne u (x α₀) with rfl | hne'
        · exact le_rfl
        · exact (shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h (hA0 α₀ hα₀) hτ
            hx0 hρ0 hupos hne' hdx0).le
      have h1 : |(a - α₀) * T u (ρ α₀)| ≤ C * |a - α₀| := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC u (Ioo_subset_Icc_self hu)) (abs_nonneg _)
      have h2 : G a u (ρ α₀) = G α₀ u (ρ α₀) + (a - α₀) * T u (ρ α₀) := by
        rw [hG a u _ hupos.le hρ0, hG α₀ u _ hupos.le hρ0]
        ring
      linarith [(abs_le.1 h1).1]
    obtain ⟨hxa, -, hdxa, hdρa⟩ := hcrit a ha
    have hρa : 0 < ρ a := (hq_pos a ha).trans (hqρ a ha)
    -- `G a (x α₀, ·)` is concave
    have hconc : ConcaveOn ℝ (Ioi 0) fun v => G a (x α₀) v := by
      have hd' := fun v (hv : 0 < v) =>
        hasDerivAt_shcherbinaTirozziHardFunctional_self a κ h τ hx0.le hv
      refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0)
        (fun v hv => (hd' v hv).continuousAt.continuousWithinAt)
        (fun v hv => (hd' v (interior_subset hv)).differentiableAt.differentiableWithinAt) ?_
      rw [interior_Ioi]
      intro v hv w hw hvw
      rw [(hd' v hv).deriv, (hd' w hw).deriv]
      exact div_le_div_of_nonneg_right
        ((strictAntiOn_shcherbinaTirozziHardFunctional_self_deriv (x := x α₀) κ h ha0 hτ
          ).antitoneOn hv hw hvw) zero_le_two
    rw [← segment_eq_uIcc]
    refine notMem_segment_of_saddle (f := G a) (S := Ioi 0) (x := x a) (x₁ := x α₀)
      (m := G a u (ρ α₀)) hxa hx0 hconc.quasiconcaveOn hρa hρ0 (fun u' hu' => ?_) ?_ hmin
      (not_le.2 (by linarith))
    · rcases eq_or_ne u' (x a) with rfl | hne'
      · exact le_rfl
      · exact (shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h ha0 hτ hxa hρa
          hu' hne' hdxa).le
    · rcases eq_or_ne (ρ α₀) (ρ a) with heq | hne'
      · rw [heq]
      · exact (shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero κ h ha0 hτ hxa.le hρa
          hρ0 hne' hdρa).le
  have hρc : Tendsto ρ (𝓝[A] α₀) (𝓝 (ρ α₀)) := by
    refine tendsto_order.2 ⟨fun l hl => ?_, fun r hr => ?_⟩
    · rcases le_or_gt l 0 with h0 | h0
      · filter_upwards [hmem] with a ha
        exact h0.trans_lt ((hq_pos a ha).trans (hqρ a ha))
      · filter_upwards [hside l h0 hl.ne] with a ha
        exact lt_of_not_ge fun hcon => ha (mem_uIcc.2 (Or.inr ⟨hcon, hl.le⟩))
    · filter_upwards [hside r (hρ0.trans hr) hr.ne'] with a ha
      exact lt_of_not_ge fun hcon => ha (mem_uIcc.2 (Or.inl ⟨hr.le, hcon⟩))
  have hxc : Tendsto x (𝓝[A] α₀) (𝓝 (x α₀)) := by
    -- compare the values at `x α₀` and at the test point `l`
    have hcmp : ∀ l, 0 < l → l ≠ x α₀ →
        ∀ᶠ a in 𝓝[A] α₀, a ∈ A ∩ U ∧ G a (x α₀) (ρ a) < G a l (ρ a) := fun l hl hne =>
      hmem.and ((hGt _ hx0 ρ hρc).eventually_lt (hGt l hl ρ hρc)
        (shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h (hA0 α₀ hα₀) hτ hx0 hρ0
          hl hne hdx0))
    have hmon : ∀ a ∈ A ∩ U, ∀ l, 0 < l → (x a ≤ l ∧ l < x α₀ ∨ x α₀ < l ∧ l ≤ x a) →
        G a l (ρ a) < G a (x α₀) (ρ a) := fun a ha l _ hbetween =>
      shcherbinaTirozziHardFunctional_ratio_lt_of_between κ h (hA0 a ha.1) hτ (hcrit a ha).1
        ((hq_pos a ha).trans (hqρ a ha)) hx0 hbetween (hcrit a ha).2.2.1
    refine tendsto_order.2 ⟨fun l hl => ?_, fun r hr => ?_⟩
    · rcases le_or_gt l 0 with h0 | h0
      · filter_upwards [hmem] with a ha
        exact h0.trans_lt (hcrit a ha).1
      · filter_upwards [hcmp l h0 hl.ne] with a ha
        exact lt_of_not_ge fun hcon => lt_asymm ha.2 (hmon a ha.1 l h0 (Or.inl ⟨hcon, hl⟩))
    · filter_upwards [hcmp r (hx0.trans hr) hr.ne'] with a ha
      exact lt_of_not_ge fun hcon =>
        lt_asymm ha.2 (hmon a ha.1 r (hx0.trans hr) (Or.inr ⟨hr, hcon⟩))
  refine ⟨?_, hρc⟩
  have h := (hxc.mul hρc).div (hxc.const_add 1) (by positivity : 1 + x α₀ ≠ 0)
  rw [ContinuousWithinAt, hqx0]
  refine h.congr' ?_
  filter_upwards [hmem] with a ha
  exact (hcrit a ha).2.1.symm

/-- **Talagrand, Lemma 3.3.6 (Eq. (3.130)), along a critical branch on a load set `A`:**
if `A ⊆ [0, ∞)` with `α₀ ∈ A`, and `0 < q a < ρ a` with
`∂F/∂q (a, q a, ρ a) = 0 = ∂F/∂ρ (a, q a, ρ a)` for `a ∈ A` near `α₀`, then
`a ↦ F (a, q a, ρ a)` has derivative `𝔼 log ℙ_ξ (z √(q α₀) + ξ √(ρ α₀ - q α₀) ≥ τ)` within `A` at
`α₀`. Continuity of `(q, ρ)` follows from criticality; neither differentiability of `(q, ρ)` nor
second derivatives in `ρ` are needed. -/
theorem hasDerivWithinAt_shcherbinaTirozziHardFunctional_branch {A : Set ℝ} {κ h τ α₀ : ℝ}
    (hA0 : ∀ a ∈ A, 0 ≤ a) (hα₀ : α₀ ∈ A) (hτ : 0 ≤ τ)
    {q ρ : ℝ → ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 α₀)
    (hq_pos : ∀ a ∈ A ∩ U, 0 < q a) (hqρ : ∀ a ∈ A ∩ U, q a < ρ a)
    (hcq : ∀ a ∈ A ∩ U, HasDerivAt (fun q' => shcherbinaTirozziHardFunctional a κ h τ q' (ρ a))
      0 (q a))
    (hcρ : ∀ a ∈ A ∩ U, HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional a κ h τ (q a) ρ')
      0 (ρ a)) :
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
  have hcrit : ∀ a ∈ A ∩ U, 0 < x a ∧ q a = x a * ρ a / (1 + x a) ∧
      HasDerivAt (fun u => G a u (ρ a)) 0 (x a) ∧ HasDerivAt (fun v => G a (x a) v) 0 (ρ a) :=
    fun a ha => shcherbinaTirozziHardFunctional_ratio_critical a κ h τ (hq_pos a ha)
      (hqρ a ha) (hcq a ha) (hcρ a ha)
  have hqx : ∀ a ∈ A ∩ U, x a * ρ a / (1 + x a) = q a := fun a ha => (hcrit a ha).2.1.symm
  -- each `(x a, ρ a)` is a saddle point of `G a` on `(0, ∞) × (0, ∞)`
  have hsaddle : ∀ a ∈ A ∩ U, 0 < x a ∧ 0 < ρ a ∧
      (∀ u ∈ Ioi (0 : ℝ), G a (x a) (ρ a) ≤ G a u (ρ a)) ∧
      (∀ v ∈ Ioi (0 : ℝ), G a (x a) v ≤ G a (x a) (ρ a)) := by
    intro a ha
    obtain ⟨hxa, -, hGx, hGρ⟩ := hcrit a ha
    have hρa : 0 < ρ a := (hq_pos a ha).trans (hqρ a ha)
    refine ⟨hxa, hρa, fun u hu => ?_, fun v hv => ?_⟩
    · rcases eq_or_ne u (x a) with rfl | hne
      · exact le_rfl
      · exact (shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h
          (hA0 a ha.1) hτ hxa hρa hu hne hGx).le
    · rcases eq_or_ne v (ρ a) with rfl | hne
      · exact le_rfl
      · exact (shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero κ h
          (hA0 a ha.1) hτ hxa.le hρa hv hne hGρ).le
  obtain ⟨hq_cont, hρ_cont⟩ := continuousWithinAt_shcherbinaTirozziHardFunctional_critical
    hA0 hα₀ hτ hU hq_pos hqρ hcq hcρ
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

/-- **Talagrand, Lemma 3.3.6 (Eq. (3.130)), two-sided interior form:** if `0 < α₀` and for `a`
near `α₀` one has `0 < q a < ρ a` and
`∂F/∂q (a, q a, ρ a) = 0 = ∂F/∂ρ (a, q a, ρ a)`, then `a ↦ F (a, q a, ρ a)` has derivative
`𝔼 log ℙ_ξ (z √(q α₀) + ξ √(ρ α₀ - q α₀) ≥ τ)` at `α₀`. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_branch {κ h τ α₀ : ℝ}
    (hα₀ : 0 < α₀) (hτ : 0 ≤ τ) {q ρ : ℝ → ℝ}
    (hq_pos : ∀ᶠ a in 𝓝 α₀, 0 < q a) (hqρ : ∀ᶠ a in 𝓝 α₀, q a < ρ a)
    (hcq : ∀ᶠ a in 𝓝 α₀,
      HasDerivAt (fun q' => shcherbinaTirozziHardFunctional a κ h τ q' (ρ a)) 0 (q a))
    (hcρ : ∀ᶠ a in 𝓝 α₀,
      HasDerivAt (fun ρ' => shcherbinaTirozziHardFunctional a κ h τ (q a) ρ') 0 (ρ a)) :
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
