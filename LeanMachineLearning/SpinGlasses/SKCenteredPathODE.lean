/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCenteredPathMoments
public import LeanMachineLearning.SpinGlasses.SKPathOverlapMoments
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment

/-!
# The differential equation of the centered moments (Talagrand, Eq. (1.120))

Along the smart path put `V_s = A_s - SK(s)` and `ψ_m(s) = 𝔼 V_s^m`.  Combining the derivative with a
moving center (`SpinGlasses.exists_sk_smart_path_profile_centered`) with the a priori moments of
`V_s` (Lemma 1.4.12 with Theorem 1.4.10) and the fourth overlap moment (Eq. (1.103)), the
derivative splits as `ψ_m' = sin s cos s ((m (m - 1) / 2) N⁻¹ β² q² ψ_{m-2} + D_m)` with
`|D_m| ≤ K_m N^{-(m+1)/2}`, which is the claim `II = O(m + 1)` of the book.

## Main declarations

* `SpinGlasses.abs_integral_pow_mul_le`: Cauchy-Schwarz for `∫ V^p Q` from moment bounds.
* `SpinGlasses.exists_sk_centered_path_ode`: the differential equation with remainder.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, proof of Theorem 1.4.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Cauchy-Schwarz for a power of a centered variable against a bounded variable.**  If
`𝔼 V^{2p} ≤ K ε^{2p}` and `𝔼 Q² ≤ C ε⁴`, then `|𝔼 V^p Q| ≤ √(K C) ε^{p+2}`. -/
theorem abs_integral_pow_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {V Q : Ω → ℝ} (hV : Measurable V) (hQ : AEStronglyMeasurable Q P)
    {ε K C : ℝ} (hε : 0 < ε) (hK : 0 < K) (hC : 0 < C) {p : ℕ}
    (hVi : Integrable (fun ω => V ω ^ (2 * p)) P) (hVb : ∫ ω, V ω ^ (2 * p) ∂P ≤ K * ε ^ (2 * p))
    {B : ℝ} (hQb : ∀ ω, |Q ω| ≤ B) (hQ2 : ∫ ω, Q ω ^ 2 ∂P ≤ C * ε ^ 4) :
    |∫ ω, V ω ^ p * Q ω ∂P| ≤ Real.sqrt (K * C) * ε ^ (p + 2) := by
  have hX : MemLp (fun ω => V ω ^ p) 2 P := by
    refine (memLp_two_iff_integrable_sq (hV.pow_const p).aestronglyMeasurable).2 ?_
    simpa only [← pow_mul, mul_comm] using hVi
  have hY : MemLp Q 2 P := MemLp.of_bound hQ B (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hQb ω)
  have h := abs_integral_mul_le_of_integral_sq_le hX hY (α := Real.sqrt K * ε ^ p)
    (γ := Real.sqrt C * ε ^ 2) (by positivity) (by positivity)
    (by
      simp only [← pow_mul, mul_comm p 2] at hVb ⊢
      rw [mul_pow, Real.sq_sqrt hK.le, ← pow_mul, mul_comm 2 p]
      simpa only [mul_comm p 2, ← pow_mul] using hVb)
    (by
      rw [mul_pow, Real.sq_sqrt hC.le, ← pow_mul]
      exact hQ2)
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_mul hK.le]
  ring

end SpinGlasses
