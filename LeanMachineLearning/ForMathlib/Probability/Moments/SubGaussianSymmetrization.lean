/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian

/-!
# Sub-Gaussian bounds by symmetrization

Two general facts about the sub-Gaussian moment-generating function `HasSubgaussianMGF`.

* `HasSubgaussianMGF.integral_sq_le`: a sub-Gaussian variable with parameter `c` has second moment
  at most `c` (`𝔼 cosh (t X) ≤ exp (c t² / 2)` and `cosh u - 1 ≥ u² / 2`, then `t → 0`).
* `hasSubgaussianMGF_sub_integral_of_integral_exp_sub_le`: **symmetrization.**  To prove that
  `F - 𝔼 F` is sub-Gaussian it suffices to bound the exponential moments of `F(ω) - F(ω')` for
  independent copies `ω, ω'`: by Jensen, `𝔼 exp (t (F - 𝔼 F)) ≤ 𝔼 exp (t F) 𝔼 exp (-t F)`.

Together with Chernoff's bound (`HasSubgaussianMGF.measure_ge_le`, `measure_le_le`) these turn an
exponential-moment bound for a pair of independent copies into a two-sided tail bound and a
variance bound.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

/-- `u² ≤ exp u + exp (-u) - 2`, i.e. `cosh u - 1 ≥ u² / 2`. -/
theorem sq_le_exp_add_exp_neg_sub_two (u : ℝ) : u ^ 2 ≤ Real.exp u + Real.exp (-u) - 2 := by
  have h : Real.cosh u = 1 + 2 * Real.sinh (u / 2) ^ 2 := by
    have := Real.cosh_two_mul (u / 2)
    have h2 := Real.cosh_sq (u / 2)
    rw [show 2 * (u / 2) = u by ring] at this
    nlinarith
  have hs : (u / 2) ^ 2 ≤ Real.sinh (u / 2) ^ 2 := by
    rcases le_total 0 u with hu | hu
    · exact pow_le_pow_left₀ (by linarith) (Real.self_le_sinh_iff.2 (by linarith)) 2
    · have := Real.sinh_le_self_iff.2 (show u / 2 ≤ 0 by linarith)
      nlinarith
  have h3 := Real.cosh_eq u
  nlinarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **A sub-Gaussian variable with parameter `c` has second moment at most `c`.**  Indeed
`t² X² ≤ exp (t X) + exp (-t X) - 2`, so `t² 𝔼 X² ≤ 2 (exp (c t² / 2) - 1) ≤ c t² exp (c t² / 2)`,
and one lets `t → 0`. -/
theorem HasSubgaussianMGF.integral_sq_le {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ^ 2 ∂μ ≤ c := by
  have hsq : Integrable (fun ω => X ω ^ 2) μ := by
    simpa using (h.memLp 2).integrable_sq
  have key : ∀ t : ℝ, 0 < t → ∫ ω, X ω ^ 2 ∂μ ≤ c * Real.exp (c * t ^ 2 / 2) := by
    intro t ht
    have h1 : ∀ ω, t ^ 2 * X ω ^ 2 ≤ Real.exp (t * X ω) + Real.exp (-t * X ω) - 2 := fun ω => by
      have := sq_le_exp_add_exp_neg_sub_two (t * X ω)
      rwa [mul_pow, ← neg_mul] at this
    have h2 : t ^ 2 * ∫ ω, X ω ^ 2 ∂μ ≤ mgf X μ t + mgf X μ (-t) - 2 := by
      rw [← integral_const_mul]
      calc ∫ ω, t ^ 2 * X ω ^ 2 ∂μ
          ≤ ∫ ω, (Real.exp (t * X ω) + Real.exp (-t * X ω) - 2) ∂μ :=
            integral_mono (hsq.const_mul _)
              (((h.integrable_exp_mul t).add (h.integrable_exp_mul (-t))).sub
                (integrable_const 2)) h1
        _ = mgf X μ t + mgf X μ (-t) - 2 := by
            have := integral_sub ((h.integrable_exp_mul t).add (h.integrable_exp_mul (-t)))
              (integrable_const (μ := μ) (2 : ℝ))
            simp only [Pi.add_apply] at this
            rw [this, integral_add (h.integrable_exp_mul t) (h.integrable_exp_mul (-t)),
              integral_const]
            simp [mgf]
    have h3 := h.mgf_le t
    have h4 := h.mgf_le (-t)
    rw [neg_sq] at h4
    set x : ℝ := c * t ^ 2 / 2 with hx
    have hxe : Real.exp x - 1 ≤ x * Real.exp x := by
      have := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
      nlinarith
    have h5 : t ^ 2 * ∫ ω, X ω ^ 2 ∂μ ≤ t ^ 2 * (c * Real.exp x) := by
      calc _ ≤ 2 * (Real.exp x - 1) := by linarith
        _ ≤ 2 * (x * Real.exp x) := by linarith
        _ = t ^ 2 * (c * Real.exp x) := by rw [hx]; ring
    exact le_of_mul_le_mul_left h5 (by positivity)
  have hlim : Tendsto (fun t : ℝ => (c : ℝ) * Real.exp (c * t ^ 2 / 2)) (𝓝[>] 0) (𝓝 c) := by
    have hc : Continuous fun t : ℝ => (c : ℝ) * Real.exp (c * t ^ 2 / 2) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => key t ht)

/-- **Symmetrization.**  Let `F` have exponential moments of all orders under a probability
measure `μ`.  If `𝔼 exp (t (F z₁ - F z₂)) ≤ exp (c t² / 2)` for the independent pair
`z = (z₁, z₂) ∼ μ ⊗ μ` and all `t`, then `F - 𝔼 F` is sub-Gaussian with parameter `c`.
The point is `𝔼 exp (t (F - 𝔼 F)) ≤ 𝔼 exp (t F) 𝔼 exp (-t F) = 𝔼 exp (t (F z₁ - F z₂))`, by
Jensen's inequality `exp (-t 𝔼 F) ≤ 𝔼 exp (-t F)`. -/
theorem hasSubgaussianMGF_sub_integral_of_integral_exp_sub_le {F : Ω → ℝ} (hFm : Measurable F)
    (hint : ∀ t, Integrable (fun ω => Real.exp (t * F ω)) μ) {c : ℝ≥0}
    (h : ∀ t : ℝ, ∫ z, Real.exp (t * (F z.1 - F z.2)) ∂(μ.prod μ) ≤ Real.exp (c * t ^ 2 / 2)) :
    HasSubgaussianMGF (fun ω => F ω - ∫ ω', F ω' ∂μ) c μ := by
  have hFi : Integrable F μ := by
    refine Integrable.mono' ((hint 1).add (hint (-1))) hFm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [one_mul, neg_mul, Pi.add_apply]
    rcases le_total 0 (F ω) with h0 | h0
    · rw [abs_of_nonneg h0]; linarith [Real.exp_pos (-F ω), Real.add_one_le_exp (F ω)]
    · rw [abs_of_nonpos h0]; linarith [Real.exp_pos (F ω), Real.add_one_le_exp (-F ω)]
  set m : ℝ := ∫ ω', F ω' ∂μ with hm
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have := (hint t).const_mul (Real.exp (-(t * m)))
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Real.exp_add]
    congr 1
    ring
  · have hJ : Real.exp (-t * m) ≤ ∫ ω, Real.exp (-t * F ω) ∂μ := by
      have := ConvexOn.map_integral_le convexOn_exp (μ := μ) (f := fun ω => -t * F ω)
        Real.continuous_exp.continuousOn isClosed_univ
        (Eventually.of_forall fun _ => Set.mem_univ _) (hFi.const_mul (-t))
        (by simpa [Function.comp_def] using hint (-t))
      rw [integral_const_mul] at this
      simpa [Function.comp_def, hm] using this
    calc mgf (fun ω => F ω - m) μ t = Real.exp (-t * m) * ∫ ω, Real.exp (t * F ω) ∂μ := by
          rw [mgf, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ (∫ ω, Real.exp (-t * F ω) ∂μ) * ∫ ω, Real.exp (t * F ω) ∂μ :=
          mul_le_mul_of_nonneg_right hJ (integral_nonneg fun _ => (Real.exp_pos _).le)
      _ = ∫ z, Real.exp (t * (F z.1 - F z.2)) ∂(μ.prod μ) := by
          rw [mul_comm]
          have e : ∀ z : Ω × Ω, Real.exp (t * (F z.1 - F z.2)) =
              Real.exp (t * F z.1) * Real.exp (-t * F z.2) := fun z => by
            rw [← Real.exp_add]; congr 1; ring
          simp_rw [e]
          exact (integral_prod_mul (μ := μ) (ν := μ) (fun ω => Real.exp (t * F ω))
            (fun ω => Real.exp (-t * F ω))).symm
      _ ≤ Real.exp (c * t ^ 2 / 2) := h t

end ProbabilityTheory
