/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FixedPoint.Interpolation

/-!
# Gaussian fields with prescribed covariance (Talagrand, Eq. (1.370))

For a positive semidefinite `Q` the centered Gaussian field `Y` with covariance `β² Q` has the
law `skVectorGaussianLaw β Q` on `Fin d → ℝ`.  Two independent fields of covariances `β² Q`, `β² Q'`
form the jointly Gaussian family `Z` used by the interpolation (1.386).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

/-- The law of the centered Gaussian field `Y` with covariance `E Y_u Y_v = β² Q_{u,v}`
(Eq. (1.370)), as a measure on `Fin d → ℝ`. -/
noncomputable def skVectorGaussianLaw {d : ℕ} (β : ℝ) (Q : Fin d → Fin d → ℝ) :
    Measure (Fin d → ℝ) :=
  (multivariateGaussian 0 (β ^ 2 • Matrix.of Q)).map fun z => z.ofLp

section Pair

variable {d : ℕ} (β : ℝ) (Q Q' : Fin d → Fin d → ℝ)

/-- The Gaussian field law is a Gaussian measure. -/
theorem isGaussian_skVectorGaussianLaw :
    IsGaussian (skVectorGaussianLaw β Q) :=
  (hasGaussianLaw_ofLp_multivariateGaussian (β ^ 2 • Matrix.of Q)).isGaussian_map

/-- Two independent Gaussian fields of covariances `β² Q` and `β² Q'`, on the product of two
Euclidean spaces. -/
noncomputable def skVectorGaussianPairLaw : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ
  (Fin d)) :=
  (multivariateGaussian 0 (β ^ 2 • Matrix.of Q)).prod
    (multivariateGaussian 0 (β ^ 2 • Matrix.of Q'))

/-- The coordinates of the pair of fields. -/
def skVectorGaussianPairField (k : Fin d ⊕ Fin d)
    (ω : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  Sum.elim (fun x => ω.1 x) (fun x => ω.2 x) k

instance : IsProbabilityMeasure (skVectorGaussianPairLaw β Q Q') := by
  unfold skVectorGaussianPairLaw; infer_instance

/-- The pair of fields is a Gaussian vector. -/
theorem hasGaussianLaw_skVectorGaussianPairField :
    HasGaussianLaw (fun ω k => skVectorGaussianPairField k ω) (skVectorGaussianPairLaw β Q Q') := by
  have h1 := hasGaussianLaw_ofLp_multivariateGaussian (β ^ 2 • Matrix.of Q)
  have h2 := hasGaussianLaw_ofLp_multivariateGaussian (β ^ 2 • Matrix.of Q')
  exact HasGaussianLaw.sumElim_prod_of_independent h1 h2 (by fun_prop) (by fun_prop)

theorem measurable_skVectorGaussianPairField (k : Fin d ⊕ Fin d) :
    Measurable (skVectorGaussianPairField k) := by
  unfold skVectorGaussianPairField
  rcases k with x | x <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem integral_skVectorGaussianPairField_fst (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ ω, f ω.1 ∂(skVectorGaussianPairLaw β Q Q') =
      ∫ z, f z ∂(multivariateGaussian 0 (β ^ 2 • Matrix.of Q)) := by
  simp [skVectorGaussianPairLaw, integral_fun_fst]

theorem integral_skVectorGaussianPairField_snd (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ ω, f ω.2 ∂(skVectorGaussianPairLaw β Q Q') =
      ∫ z, f z ∂(multivariateGaussian 0 (β ^ 2 • Matrix.of Q')) := by
  simp [skVectorGaussianPairLaw, integral_fun_snd]

/-- The pair of fields is centered. -/
theorem integral_skVectorGaussianPairField (k : Fin d ⊕ Fin d) :
    ∫ ω, skVectorGaussianPairField k ω ∂(skVectorGaussianPairLaw β Q Q') = 0 := by
  rcases k with x | x
  · simpa [skVectorGaussianPairField] using
      (integral_skVectorGaussianPairField_fst β Q Q' (fun z => z x)).trans
        (integral_eval_multivariateGaussian _ x)
  · simpa [skVectorGaussianPairField] using
      (integral_skVectorGaussianPairField_snd β Q Q' (fun z => z x)).trans
        (integral_eval_multivariateGaussian _ x)

/-- Covariance of the first field. -/
theorem integral_skVectorGaussianPairField_inl_mul (hQ : (Matrix.of Q).PosSemidef) (x y : Fin d) :
    ∫ ω, skVectorGaussianPairField (Sum.inl x) ω * skVectorGaussianPairField (Sum.inl y) ω
      ∂(skVectorGaussianPairLaw β Q Q') = β ^ 2 * Q x y := by
  have := (integral_skVectorGaussianPairField_fst β Q Q' (fun z => z x * z y)).trans
    (integral_mul_eval_multivariateGaussian (hQ.smul (sq_nonneg β)) x y)
  simpa [skVectorGaussianPairField] using this

/-- Covariance of the second field. -/
theorem integral_skVectorGaussianPairField_inr_mul (hQ' : (Matrix.of Q').PosSemidef) (x y : Fin d) :
    ∫ ω, skVectorGaussianPairField (Sum.inr x) ω * skVectorGaussianPairField (Sum.inr y) ω
      ∂(skVectorGaussianPairLaw β Q Q') = β ^ 2 * Q' x y := by
  have := (integral_skVectorGaussianPairField_snd β Q Q' (fun z => z x * z y)).trans
    (integral_mul_eval_multivariateGaussian (hQ'.smul (sq_nonneg β)) x y)
  simpa [skVectorGaussianPairField] using this

/-- The two fields are uncorrelated. -/
theorem integral_skVectorGaussianPairField_inl_inr_mul (x y : Fin d) :
    ∫ ω, skVectorGaussianPairField (Sum.inl x) ω * skVectorGaussianPairField (Sum.inr y) ω
      ∂(skVectorGaussianPairLaw β Q Q') = 0 := by
  have := integral_prod_mul (μ := multivariateGaussian 0 (β ^ 2 • Matrix.of Q))
    (ν := multivariateGaussian 0 (β ^ 2 • Matrix.of Q')) (fun z => z x) (fun z => z y)
  rw [integral_eval_multivariateGaussian, zero_mul] at this
  simpa [skVectorGaussianPairLaw, skVectorGaussianPairField] using this

end Pair

end SpinGlasses
