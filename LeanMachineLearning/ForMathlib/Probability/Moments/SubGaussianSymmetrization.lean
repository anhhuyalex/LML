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

Two centering bounds go the other way: from a bound around an arbitrary number `m` (for instance a
median) to a bound around the mean.

* `integral_sub_integral_pow_two_mul_le`:
  `𝔼 (f - 𝔼 f) ^ (2 k) ≤ 2 ^ (2 k) 𝔼 (f - m) ^ (2 k)`.
* `integral_exp_mul_sq_sub_integral_le`:
  `𝔼 exp (c (f - 𝔼 f)² / 4) ≤ 𝔼 exp (c (f - m)²)`.
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
theorem hasSubgaussianMGF_sub_integral_of_integral_exp_sub_le {F : Ω → ℝ}
    (hint : ∀ t, Integrable (fun ω => Real.exp (t * F ω)) μ) {c : ℝ≥0}
    (h : ∀ t : ℝ, ∫ z, Real.exp (t * (F z.1 - F z.2)) ∂(μ.prod μ) ≤ Real.exp (c * t ^ 2 / 2)) :
    HasSubgaussianMGF (fun ω => F ω - ∫ ω', F ω' ∂μ) c μ := by
  -- measurability of `F` follows from that of `exp F`
  have hFm : AEStronglyMeasurable F μ := by
    have h1 : AEMeasurable (fun ω => Real.log (Real.exp (1 * F ω))) μ :=
      Real.measurable_log.comp_aemeasurable (hint 1).aemeasurable
    exact (h1.congr (Eventually.of_forall fun ω => by simp)).aestronglyMeasurable
  have hFi : Integrable F μ := by
    refine Integrable.mono' ((hint 1).add (hint (-1))) hFm
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

/-- **Centering at the mean costs a factor `2 ^ (2 k)`** (Talagrand, Eq. (3.22)):
`𝔼 (f - 𝔼 f) ^ (2 k) ≤ 2 ^ (2 k) 𝔼 (f - m) ^ (2 k)` for every number `m`. -/
theorem integral_sub_integral_pow_two_mul_le {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {m : ℝ}
    {k : ℕ} (hint : Integrable (fun ω => (f ω - m) ^ (2 * k)) μ) :
    Integrable (fun ω => (f ω - ∫ ω', f ω' ∂μ) ^ (2 * k)) μ ∧
      ∫ ω, (f ω - ∫ ω', f ω' ∂μ) ^ (2 * k) ∂μ ≤
        2 ^ (2 * k) * ∫ ω, (f ω - m) ^ (2 * k) ∂μ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have heven : Even (2 * k) := even_two_mul k
  set g : Ω → ℝ := fun ω => f ω - m with hg
  have hgm : AEStronglyMeasurable g μ := hf.sub aestronglyMeasurable_const
  have hgi : Integrable g μ := by
    refine Integrable.mono' (hint.add (integrable_const 1)) hgm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, Pi.add_apply, ← heven.pow_abs]
    rcases le_total |g ω| 1 with h | h
    · linarith [pow_nonneg (abs_nonneg (g ω)) (2 * k)]
    · linarith [le_self_pow₀ h (show 2 * k ≠ 0 by omega)]
  have hfi : Integrable f μ :=
    (hgi.add (integrable_const m)).congr (ae_of_all _ fun ω => by simp [hg])
  set e := ∫ ω, g ω ∂μ with he
  have hmean : ∀ ω, f ω - ∫ ω', f ω' ∂μ = g ω - e := fun ω => by
    have : e = (∫ ω', f ω' ∂μ) - m := by
      rw [he, integral_sub hfi (integrable_const m), integral_const, probReal_univ, one_smul]
    simp only [hg, this]
    ring
  have hJ : e ^ (2 * k) ≤ ∫ ω, g ω ^ (2 * k) ∂μ :=
    ConvexOn.map_integral_le (heven.convexOn_pow (𝕜 := ℝ)) (continuous_pow _).continuousOn
      isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hgi hint
  have hpt : ∀ ω, (g ω - e) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (g ω ^ (2 * k) + e ^ (2 * k)) :=
    fun ω => by
      rw [← heven.pow_abs (g ω - e), ← heven.pow_abs (g ω), ← heven.pow_abs e]
      exact (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) _).trans
        (add_pow_le (abs_nonneg _) (abs_nonneg _) _)
  have hdom : Integrable (fun ω => 2 ^ (2 * k - 1) * (g ω ^ (2 * k) + e ^ (2 * k))) μ :=
    (hint.add (integrable_const _)).const_mul _
  have hi : Integrable (fun ω => (g ω - e) ^ (2 * k)) μ := by
    refine Integrable.mono' hdom ((continuous_pow _).comp_aestronglyMeasurable
      (hgm.sub aestronglyMeasurable_const)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (heven.pow_nonneg _)]
    exact hpt ω
  simp only [hmean]
  refine ⟨hi, (integral_mono hi hdom hpt).trans ?_⟩
  rw [integral_const_mul, integral_add hint (integrable_const _), integral_const, probReal_univ,
    one_smul]
  have h2 : (2 : ℝ) ^ (2 * k) = 2 ^ (2 * k - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **Exponential square integrability centered at the mean**: if `exp (c (f - m)²)` is
integrable for some number `m` and `c > 0`, then
`𝔼 exp (c (f - 𝔼 f)² / 4) ≤ 𝔼 exp (c (f - m)²)`. The integrability hypothesis is necessary for
the inequality to carry information. -/
theorem integral_exp_mul_sq_sub_integral_le {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {m c : ℝ} (hc : 0 < c) (hint : Integrable (fun ω => Real.exp (c * (f ω - m) ^ 2)) μ) :
    Integrable (fun ω => Real.exp (c / 4 * (f ω - ∫ ω', f ω' ∂μ) ^ 2)) μ ∧
      ∫ ω, Real.exp (c / 4 * (f ω - ∫ ω', f ω' ∂μ) ^ 2) ∂μ ≤
        ∫ ω, Real.exp (c * (f ω - m) ^ 2) ∂μ := by
  set g : Ω → ℝ := fun ω => f ω - m with hg
  have hgm : AEStronglyMeasurable g μ := hf.sub aestronglyMeasurable_const
  have hg2m : AEStronglyMeasurable (fun ω => g ω ^ 2) μ :=
    (continuous_pow 2).comp_aestronglyMeasurable hgm
  have hg2 : Integrable (fun ω => g ω ^ 2) μ := by
    refine Integrable.mono' (hint.const_mul c⁻¹) hg2m (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), inv_mul_eq_div, le_div_iff₀ hc]
    exact (mul_comm _ _).trans_le ((le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp _))
  have hgL : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).2 hg2
  have hgi : Integrable g μ := hgL.integrable one_le_two
  have hfi : Integrable f μ :=
    (hgi.add (integrable_const m)).congr (ae_of_all _ fun ω => by simp [hg])
  set e := ∫ ω, g ω ∂μ with he
  have hmean : ∀ ω, f ω - ∫ ω', f ω' ∂μ = g ω - e := fun ω => by
    have : e = (∫ ω', f ω' ∂μ) - m := by
      rw [he, integral_sub hfi (integrable_const m), integral_const, probReal_univ, one_smul]
    simp only [hg, this]
    ring
  have hexpm : ∀ {h : Ω → ℝ}, AEStronglyMeasurable h μ →
      AEStronglyMeasurable (fun ω => Real.exp (h ω)) μ := fun hh =>
    Real.continuous_exp.comp_aestronglyMeasurable hh
  have hhalf : Integrable (fun ω => Real.exp (c / 2 * g ω ^ 2)) μ := by
    refine Integrable.mono' hint (hexpm (hg2m.const_mul _)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  -- Jensen twice: `exp (c e² / 2) ≤ 𝔼 exp (c g² / 2)`
  have he2 : e ^ 2 ≤ ∫ ω, g ω ^ 2 ∂μ :=
    ConvexOn.map_integral_le ((even_two).convexOn_pow (𝕜 := ℝ)) (continuous_pow 2).continuousOn
      isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hgi hg2
  have hJ : Real.exp (c / 2 * e ^ 2) ≤ ∫ ω, Real.exp (c / 2 * g ω ^ 2) ∂μ := by
    refine (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left he2 (by linarith))).trans ?_
    rw [← integral_const_mul]
    exact ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) (hg2.const_mul _) hhalf
  have hpt : ∀ ω, Real.exp (c / 4 * (g ω - e) ^ 2) ≤
      Real.exp (c / 2 * e ^ 2) * Real.exp (c / 2 * g ω ^ 2) := fun ω => by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_nonneg hc.le (sq_nonneg (g ω + e))]
  have hi : Integrable (fun ω => Real.exp (c / 4 * (g ω - e) ^ 2)) μ := by
    refine Integrable.mono' (hhalf.const_mul (Real.exp (c / 2 * e ^ 2)))
      (hexpm (((continuous_pow 2).comp_aestronglyMeasurable
        (hgm.sub aestronglyMeasurable_const)).const_mul _)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hpt ω
  simp only [hmean]
  refine ⟨hi, (integral_mono hi (hhalf.const_mul _) hpt).trans ?_⟩
  rw [integral_const_mul]
  -- `(𝔼 exp (c g² / 2))² ≤ 𝔼 exp (c g²)`
  have hsq : ∀ ω, Real.exp (c / 2 * g ω ^ 2) ^ 2 = Real.exp (c * g ω ^ 2) := fun ω => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hJ2 : (∫ ω, Real.exp (c / 2 * g ω ^ 2) ∂μ) ^ 2 ≤ ∫ ω, Real.exp (c * g ω ^ 2) ∂μ := by
    have := ConvexOn.map_integral_le ((even_two).convexOn_pow (𝕜 := ℝ)) (μ := μ)
      (f := fun ω => Real.exp (c / 2 * g ω ^ 2)) (continuous_pow 2).continuousOn
      isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hhalf
      (hint.congr (ae_of_all _ fun ω => (hsq ω).symm))
    simpa only [Function.comp_def, hsq] using this
  refine le_trans ?_ hJ2
  rw [sq (∫ ω, Real.exp (c / 2 * g ω ^ 2) ∂μ)]
  exact mul_le_mul_of_nonneg_right hJ (integral_nonneg fun _ => (Real.exp_pos _).le)

end ProbabilityTheory
