/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Continuity of the centered multivariate Gaussian in its covariance matrix

The map `S ↦ multivariateGaussian 0 S` is weakly continuous on the cone of positive semidefinite
matrices (`continuousOn_integral_multivariateGaussian`): if `g` is bounded and continuous, then
`S ↦ ∫ g d(multivariateGaussian 0 S)` is continuous on `{S | S.PosSemidef}`.  The proof is Lévy's
continuity theorem (`ProbabilityMeasure.tendsto_of_tendsto_charFun`), since the characteristic
function `exp (-x ⬝ᵥ S *ᵥ x / 2)` is continuous in `S`.

(Off the cone `multivariateGaussian 0 S` is the Dirac mass at `0`, so no global statement holds.)
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Matrix

namespace ProbabilityTheory

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Weak continuity of `S ↦ multivariateGaussian 0 S` on positive semidefinite matrices.** -/
theorem continuousOn_integral_multivariateGaussian {g : EuclideanSpace ℝ κ → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    ContinuousOn (fun S : Matrix κ κ ℝ => ∫ x, g x ∂(multivariateGaussian 0 S))
      {S | S.PosSemidef} := by
  have : FirstCountableTopology (Matrix κ κ ℝ) :=
    inferInstanceAs (FirstCountableTopology (κ → κ → ℝ))
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro Sn S hSn
  have hSn' : Tendsto (fun n => (Sn n : Matrix κ κ ℝ)) atTop (𝓝 (S : Matrix κ κ ℝ)) :=
    (continuous_subtype_val.tendsto S).comp hSn
  let μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ κ) := fun n =>
    ⟨multivariateGaussian 0 (Sn n : Matrix κ κ ℝ), inferInstance⟩
  let μ₀ : ProbabilityMeasure (EuclideanSpace ℝ κ) :=
    ⟨multivariateGaussian 0 (S : Matrix κ κ ℝ), inferInstance⟩
  have hlevy : Tendsto μ atTop (𝓝 μ₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
    simp only [μ, μ₀, ProbabilityMeasure.coe_mk]
    simp_rw [charFun_multivariateGaussian (Sn _).2, charFun_multivariateGaussian S.2]
    have hq : Tendsto (fun n => t.ofLp ⬝ᵥ (Sn n : Matrix κ κ ℝ) *ᵥ t.ofLp) atTop
        (𝓝 (t.ofLp ⬝ᵥ (S : Matrix κ κ ℝ) *ᵥ t.ofLp)) := by
      have : Continuous fun A : Matrix κ κ ℝ => t.ofLp ⬝ᵥ A *ᵥ t.ofLp := by
        simp only [dotProduct, Matrix.mulVec]
        fun_prop
      exact (this.tendsto _).comp hSn'
    refine (Complex.continuous_exp.tendsto _).comp ?_
    refine tendsto_const_nhds.sub ?_
    exact (Complex.continuous_ofReal.tendsto _).comp hq |>.div_const _
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlevy
    (BoundedContinuousFunction.ofNormedAddCommGroup g hg M hM)
  exact this

end ProbabilityTheory
