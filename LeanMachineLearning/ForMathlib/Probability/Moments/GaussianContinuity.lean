/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Continuity of the centered multivariate Gaussian in its covariance matrix

The map `S ↦ multivariateGaussian 0 S` is weakly continuous on the cone of positive semidefinite
matrices (`continuousOn_integral_multivariateGaussian`): if `g` is bounded and continuous with
values in a real normed space, then `S ↦ ∫ g d(multivariateGaussian 0 S)` is continuous on
`{S | S.PosSemidef}`.  The law is the image of the standard Gaussian under `√S`, the square root
is continuous on the cone, and one applies dominated convergence.

(Off the cone `multivariateGaussian 0 S` is the Dirac mass at `0`, so no global statement holds.)
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction Matrix Matrix.Norms.L2Operator MatrixOrder

namespace ProbabilityTheory

variable {κ E : Type*} [Fintype κ] [DecidableEq κ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Weak continuity of `S ↦ multivariateGaussian 0 S` on positive semidefinite matrices**, for a
bounded continuous test function `g` with values in a normed space.  (See
`continuousOn_integral_multivariateGaussian` for the version with an explicit bound.) -/
theorem continuousOn_integral_multivariateGaussian_of_bcf (g : EuclideanSpace ℝ κ →ᵇ E) :
    ContinuousOn (fun S : Matrix κ κ ℝ => ∫ x, g x ∂(multivariateGaussian 0 S))
      {S | S.PosSemidef} := by
  have hsqrt : ContinuousOn (fun S : Matrix κ κ ℝ => CFC.sqrt S) {S | S.PosSemidef} :=
    CFC.continuousOn_sqrt.mono fun S hS => Matrix.nonneg_iff_posSemidef.2 hS
  have hrep : ∀ S : Matrix κ κ ℝ, ∫ x, g x ∂(multivariateGaussian 0 S) =
      ∫ y, g (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) y)
        ∂(stdGaussian (EuclideanSpace ℝ κ)) := fun S => by
    rw [multivariateGaussian, integral_map (by fun_prop) g.continuous.aestronglyMeasurable]
    simp only [zero_add]
  have happ : ∀ y : EuclideanSpace ℝ κ,
      Continuous fun A : Matrix κ κ ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) A y := fun y => by
    let L : Matrix κ κ ℝ →ₗ[ℝ] EuclideanSpace ℝ κ :=
      { toFun := fun A => Matrix.toEuclideanCLM (𝕜 := ℝ) A y
        map_add' := fun A B => by rw [map_add]; rfl
        map_smul' := fun c A => by rw [map_smul]; rfl }
    exact L.continuous_of_finiteDimensional
  simp_rw [hrep]
  refine continuousOn_of_dominated (bound := fun _ => ‖g‖)
    (fun S _ => (g.continuous.comp
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).continuous).aestronglyMeasurable)
    (fun S _ => ae_of_all _ fun y => g.norm_coe_le_norm _) (integrable_const _)
    (ae_of_all _ fun y => ?_)
  exact g.continuous.comp_continuousOn ((happ y).comp_continuousOn hsqrt)

/-- **Weak continuity of `S ↦ multivariateGaussian 0 S` on positive semidefinite matrices**, for
a continuous function `g` bounded by `M`. -/
theorem continuousOn_integral_multivariateGaussian {g : EuclideanSpace ℝ κ → E}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    ContinuousOn (fun S : Matrix κ κ ℝ => ∫ x, g x ∂(multivariateGaussian 0 S))
      {S | S.PosSemidef} :=
  continuousOn_integral_multivariateGaussian_of_bcf
    (BoundedContinuousFunction.ofNormedAddCommGroup g hg M hM)

end ProbabilityTheory
