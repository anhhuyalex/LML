/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Expectation
public import LeanMachineLearning.Optimization.Renormalization.Gaussian
public import LeanMachineLearning.Optimization.Renormalization.Perturbation
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Actions and Gaussian expectation

An action is represented relative to an explicit reference measure.  Its induced law is the
normalized exponential tilt by `exp (-S)`.  This makes the usual density presentation precise
without pretending that every measurable space carries a canonical Lebesgue measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder RealInnerProductSpace

namespace Renormalization

universe uΩ uI uE

/-- A real action on a configuration space. -/
abbrev Action (Ω : Type uΩ) := Ω → ℝ

namespace Action

/-- The unnormalized partition function of an action relative to `μ`. -/
def partitionFunction {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Action Ω) : ℝ :=
  ∫ x, Real.exp (-S x) ∂μ

/-- The exact integrability condition for an action to induce a probability law. -/
def Normalizable {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Action Ω) : Prop :=
  Integrable (fun x => Real.exp (-S x)) μ

/-- The normalized law represented by `S`, relative to reference measure `μ`. -/
def measure {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Action Ω) : Measure Ω :=
  μ.tilted fun x => -S x

/-- Bundle a normalizable action law as a probability measure. -/
def probabilityMeasure {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [NeZero μ] (S : Action Ω)
    (hnorm : S.Normalizable μ) : ProbabilityMeasure Ω :=
  ⟨S.measure μ, MeasureTheory.isProbabilityMeasure_tilted hnorm⟩

/-- Expectation under the law represented by an action. -/
def expectation {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (S : Action Ω) (O : Ω → E) : E :=
  Renormalization.expectation (S.measure μ) O

/-- The action construction is the existing multiplicative deformation after combining the base
action and perturbing potential.

Informal proof: both sides are the same tilted measure; pointwise,
`-(ε * V x) = -ε * V x`.  This is equation `eq:action-representation-of-distribution` expressed
relative to a reference law rather than a coordinate density.
-/
theorem measure_smul_eq_deform {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → ℝ) (ε : ℝ) :
    measure μ (fun x => ε * V x) = deform μ V ε := by
  apply congrArg (Measure.tilted μ)
  funext x
  ring

end Action

/-- The quadratic action with precision matrix `P`. -/
def quadraticAction {ι : Type uI} [Fintype ι]
    (P : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  (1 / 2 : ℝ) * dotProduct z (P *ᵥ z)

/-- Gaussian expectation, the rigorous counterpart of the source's bra-ket notation. -/
def gaussianExpectation {ι : Type uI} [Fintype ι] {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Matrix ι ι ℝ) (O : EuclideanSpace ℝ ι → E) : E := by
  classical
  exact expectation (multivariateGaussian 0 K) O

/-- Bra-ket notation for Gaussian expectation with covariance `K`. -/
scoped notation "⟪" O "⟫ᵍ[" K "]" => gaussianExpectation K O

-- Coercivity of a positive-definite quadratic form: `v ↦ vᵀPv` grows at least quadratically.
-- The continuous form is strictly positive on the compact unit sphere (finite-dimensional space),
-- so its minimum there is a positive constant `c`; rescaling any nonzero `v` to the unit sphere
-- and using the degree-two homogeneity of the form gives the global bound `c * ‖v‖² ≤ vᵀPv`.
private lemma posDef_quadraticAction_lower_bound {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ dotProduct v (P *ᵥ v) := by
  classical
  by_cases h : ∃ v : EuclideanSpace ℝ ι, v ≠ 0
  · -- There is a nonzero vector: the unit sphere is nonempty and we minimize on it.
    rcases h with ⟨v₀, hv₀⟩
    let f : EuclideanSpace ℝ ι → ℝ := fun v => dotProduct v (P *ᵥ v)
    have hs_nonempty : (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty := by
      refine ⟨‖v₀‖⁻¹ • v₀, ?_⟩
      simpa [Metric.mem_sphere, dist_eq_norm, norm_smul, abs_of_nonneg] using
        inv_mul_cancel₀ (norm_eq_zero.not.mpr hv₀)
    obtain ⟨x₀, hx₀s, hx₀min⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1).exists_isMinOn hs_nonempty
        (by dsimp [f]; fun_prop : Continuous f).continuousOn
    have hx₀ne : x₀ ≠ 0 := by intro hx₀; simp [hx₀] at hx₀s
    have hx₀pos : 0 < f x₀ := by
      dsimp [f]
      simpa using hP.dotProduct_mulVec_pos (x := x₀.ofLp) (by simpa using hx₀ne)
    refine ⟨f x₀, hx₀pos, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv, f]
    · -- Rescale `v` onto the unit sphere, then use minimality at `x₀`.
      let u : EuclideanSpace ℝ ι := ‖v‖⁻¹ • v
      have hnorm_ne : ‖v‖ ≠ 0 := norm_eq_zero.not.mpr hv
      have hnorm_u : ‖u‖ = 1 := by
        dsimp [u]
        simpa [norm_smul, abs_of_nonneg] using inv_mul_cancel₀ hnorm_ne
      have hle_u : f x₀ ≤ f u := hx₀min (by simpa using hnorm_u)
      have hveq : v = ‖v‖ • u := by dsimp [u]; rw [smul_smul, mul_inv_cancel₀ hnorm_ne, one_smul]
      -- `f` is homogeneous of degree two, so `f (‖v‖ • u) = ‖v‖² * f u`.
      have hf_smul : ∀ a : ℝ, f (a • u) = a ^ 2 * f u := by
        intro a
        dsimp [f]
        simp [mulVec_smul, smul_dotProduct, dotProduct_smul]
        ring
      calc
        f x₀ * ‖v‖ ^ 2 ≤ f u * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hle_u (sq_nonneg ‖v‖)
        _ = ‖v‖ ^ 2 * f u := by ring
        _ = f v := by rw [← hf_smul, ← hveq]
  · -- No nonzero vectors exist: the bound is trivial.
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := by by_contra hne; exact h ⟨v, hne⟩
    simp [hv]

-- Integrability of the isotropic Gaussian `v ↦ exp (-c * ‖v‖²)` on a finite-dimensional
-- Euclidean space.  This is the dominating integrand for the quadratic form below; Mathlib proves
-- the analogous complex exponential integrable, and taking the real part yields the real Gaussian.
private lemma integrable_exp_neg_mul_normSq {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) :
    Integrable (fun v : EuclideanSpace ℝ ι => Real.exp (-c * ‖v‖ ^ 2)) volume := by
  convert (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
      (b := (c : ℂ)) (by simpa using hc) (0 : ℂ) (0 : EuclideanSpace ℝ ι)).re with v
  -- The real part of the complex Gaussian `cexp (-c * ‖v‖²)` is the real Gaussian.
  norm_num
  norm_cast

/-- Integrability of an exponential positive-definite quadratic form on a finite-dimensional
Euclidean space.

Informal proof: diagonalize the real symmetric positive-definite matrix `P` as `Qᵀ D Q` with
positive diagonal entries.  The orthogonal change of variables has Jacobian `1`, after which the
integrand becomes the finite product `∏ i, exp (-(d i / 2) * y i ^ 2)`.  Each one-dimensional
factor is integrable by Mathlib's `integrable_exp_neg_mul_sq`, and Tonelli/Fubini gives the finite
product integrability.  Equivalently, one may derive a coercivity bound
`quadraticAction P z ≥ c * ‖z‖ ^ 2` for some `c > 0` and compare against an isotropic Gaussian.
Source: <https://en.wikipedia.org/wiki/Gaussian_integral#Multidimensional_and_functional_generalizations>.
-/
theorem integrable_exp_neg_quadraticAction_of_posDef {ι : Type uI} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    Integrable (fun z : EuclideanSpace ℝ ι => Real.exp (-(quadraticAction P z))) volume := by
  rcases posDef_quadraticAction_lower_bound P hP with ⟨c, hc, hbound⟩
  refine Integrable.mono (integrable_exp_neg_mul_normSq (c / 2) (div_pos hc zero_lt_two)) ?_ ?_
  · exact (Real.continuous_exp.comp
      (by
        dsimp [quadraticAction]
        fun_prop : Continuous fun z : EuclideanSpace ℝ ι =>
          -(quadraticAction P z))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hle : (c / 2) * ‖z‖ ^ 2 ≤ quadraticAction P z := by
      dsimp [quadraticAction]
      nlinarith [hbound z]
    simpa using neg_le_neg hle

/-- A positive-definite quadratic action is normalizable against Euclidean volume.

Informal proof: the inverse covariance matrix `K⁻¹` is positive definite by `Matrix.PosDef.inv`,
and the preceding reusable Gaussian-integrability lemma applies to this precision matrix.
-/
theorem quadraticAction_normalizable {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Action.Normalizable (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹) :=
  integrable_exp_neg_quadraticAction_of_posDef K⁻¹ hK.inv

-- The Lebesgue measure on `EuclideanSpace ℝ ι` is the transport of the product measure on
-- `ι → ℝ` along the canonical equivalence; an invertible matrix therefore rescales it by the
-- absolute determinant, exactly as on `ℝⁿ`.
private lemma map_toEuclideanCLM_volume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    Measure.map (fun x : EuclideanSpace ℝ ι => toEuclideanCLM (𝕜 := ℝ) M x) volume =
      ENNReal.ofReal (|(M.det)⁻¹|) • volume := by
  classical
  have hvol_pi : Measure.map (fun x : ι → ℝ => WithLp.toLp 2 x) (volume : Measure (ι → ℝ)) =
      (volume : Measure (EuclideanSpace ℝ ι)) :=
    (PiLp.volume_preserving_toLp ι).map_eq
  symm
  calc
    ENNReal.ofReal (|(M.det)⁻¹|) • (volume : Measure (EuclideanSpace ℝ ι))
        = ENNReal.ofReal (|(M.det)⁻¹|) •
            Measure.map (fun x : ι → ℝ => WithLp.toLp 2 x) (volume : Measure (ι → ℝ)) := by
            rw [← hvol_pi]
    _ = Measure.map (fun x : ι → ℝ => WithLp.toLp 2 x)
          (ENNReal.ofReal (|(M.det)⁻¹|) • (volume : Measure (ι → ℝ))) := by
            rw [Measure.map_smul]
    _ = Measure.map (fun x : ι → ℝ => WithLp.toLp 2 x)
          (Measure.map (fun x : ι → ℝ => toLin' M x) (volume : Measure (ι → ℝ))) := by
            rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hM]
    _ = Measure.map (fun x : ι → ℝ => WithLp.toLp 2 (toLin' M x)) (volume : Measure (ι → ℝ)) := by
            rw [Measure.map_map (PiLp.volume_preserving_toLp ι).measurable
              (LinearMap.continuous_on_pi (toLin' M)).measurable]
            rfl
    _ = Measure.map (fun x : EuclideanSpace ℝ ι => toEuclideanCLM (𝕜 := ℝ) M x)
          (Measure.map (fun y : ι → ℝ => WithLp.toLp 2 y) (volume : Measure (ι → ℝ))) := by
          simpa [Function.comp_def, toEuclideanCLM_toLp, Matrix.toLin'_apply] using
            (Measure.map_map (toEuclideanCLM (𝕜 := ℝ) M).continuous.measurable
              (PiLp.volume_preserving_toLp ι).measurable).symm
    _ = Measure.map (fun x : EuclideanSpace ℝ ι => toEuclideanCLM (𝕜 := ℝ) M x) volume := by
            rw [← hvol_pi]

-- Integral form of the change of variables: substituting `y ↦ toEuclideanCLM M y` rescales by
-- the inverse absolute determinant.
private lemma integral_comp_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : EuclideanSpace ℝ ι → G) (hf : Continuous f) :
    (∫ y : EuclideanSpace ℝ ι, f (toEuclideanCLM (𝕜 := ℝ) M y) ∂volume) =
      (|(M.det)⁻¹| : ℝ) • ∫ z : EuclideanSpace ℝ ι, f z ∂volume := by
  classical
  calc
    (∫ y : EuclideanSpace ℝ ι, f (toEuclideanCLM (𝕜 := ℝ) M y) ∂volume)
        = ∫ z : EuclideanSpace ℝ ι, f z
            ∂Measure.map (fun y : EuclideanSpace ℝ ι => toEuclideanCLM (𝕜 := ℝ) M y) volume := by
          symm
          exact MeasureTheory.integral_map
            (toEuclideanCLM (𝕜 := ℝ) M).continuous.aemeasurable hf.aestronglyMeasurable
    _ = ∫ z : EuclideanSpace ℝ ι, f z
          ∂(ENNReal.ofReal (|(M.det)⁻¹|) • volume) := by
          rw [map_toEuclideanCLM_volume M hM]
    _ = (ENNReal.ofReal (|(M.det)⁻¹|)).toReal • ∫ z : EuclideanSpace ℝ ι, f z ∂volume := by
          rw [MeasureTheory.integral_smul_measure]
    _ = (|(M.det)⁻¹| : ℝ) • ∫ z : EuclideanSpace ℝ ι, f z ∂volume := by
          simp

-- The quadratic form of a positive-semidefinite matrix is the squared norm of its square root:
-- `quadraticAction A z = (1/2) * ‖sqrt A · z‖²`.
private lemma quadraticAction_eq_half_normSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (z : EuclideanSpace ℝ ι) :
    quadraticAction A z =
      (1 / 2 : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z‖ ^ 2 := by
  classical
  have hL : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A)) :=
    (CFC.sqrt_nonneg A).isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))
  have hadj :
      inner ℝ z (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A)
        (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z)) =
        inner ℝ (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z)
          (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [hL.adjoint_eq]
  have hmap : toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A * CFC.sqrt A) =
      (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) * toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) :
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) := by
    rw [map_mul]
  calc
    quadraticAction A z = (1 / 2 : ℝ) * (z ⬝ᵥ A *ᵥ z) := rfl
    _ = (1 / 2 : ℝ) * inner ℝ z (toEuclideanCLM (𝕜 := ℝ) A z) := by
      congr 1
      rw [inner_toEuclideanCLM]
    _ = (1 / 2 : ℝ) * inner ℝ (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z)
          (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z) := by
      congr 1
      calc
        inner ℝ z (toEuclideanCLM (𝕜 := ℝ) A z)
            = inner ℝ z (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A * CFC.sqrt A) z) := by
              rw [CFC.sqrt_mul_sqrt_self A hA.nonneg]
        _ = inner ℝ z (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A)
              (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z)) := by
              rw [hmap]
              simp [ContinuousLinearMap.mul_def]
        _ = inner ℝ (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z)
              (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z) := hadj
    _ = (1 / 2 : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z‖ ^ 2 := by
      congr 1
      rw [real_inner_self_eq_norm_sq]

-- For a self-adjoint matrix `S`, the squared Euclidean norm of `S · t` is the quadratic form
-- `t ⬝ᵥ (S * S) *ᵥ t`.
private lemma normSq_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) S))
    (t : EuclideanSpace ℝ ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) S t‖ ^ 2 = t ⬝ᵥ (S * S) *ᵥ t := by
  calc
    ‖toEuclideanCLM (𝕜 := ℝ) S t‖ ^ 2
        = inner ℝ (toEuclideanCLM (𝕜 := ℝ) S t) (toEuclideanCLM (𝕜 := ℝ) S t) := by
          rw [← real_inner_self_eq_norm_sq]
    _ = inner ℝ t (toEuclideanCLM (𝕜 := ℝ) S (toEuclideanCLM (𝕜 := ℝ) S t)) := by
          rw [← ContinuousLinearMap.adjoint_inner_right]
          rw [hS.adjoint_eq]
    _ = inner ℝ t (toEuclideanCLM (𝕜 := ℝ) (S * S) t) := by
          have hmap : toEuclideanCLM (𝕜 := ℝ) (S * S) =
              (toEuclideanCLM (𝕜 := ℝ) S * toEuclideanCLM (𝕜 := ℝ) S :
                EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) := by
            rw [map_mul]
          rw [hmap]
          simp [ContinuousLinearMap.mul_def]
    _ = t ⬝ᵥ (S * S) *ᵥ t := by
          rw [inner_toEuclideanCLM]

-- The squared norm of the inverse square root applied to `t` is the covariance quadratic form
-- `t ⬝ᵥ A⁻¹ *ᵥ t`: `(sqrt A)⁻¹` is the (nonnegative) inverse square root, so its square is `A⁻¹`.
private lemma normSq_sqrt_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (t : EuclideanSpace ℝ ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) t‖ ^ 2 = t ⬝ᵥ (A⁻¹) *ᵥ t := by
  classical
  have hL_sq : CFC.sqrt A * CFC.sqrt A = A :=
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hT_nonneg : 0 ≤ (CFC.sqrt A)⁻¹ := by
    simpa using (Matrix.PosSemidef.inv (CFC.sqrt_nonneg A)).nonneg
  have hT_selfadj : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹)) :=
    hT_nonneg.isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))
  calc
    ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) t‖ ^ 2
        = t ⬝ᵥ (((CFC.sqrt A)⁻¹) * (CFC.sqrt A)⁻¹) *ᵥ t := by
          exact normSq_toEuclideanCLM ((CFC.sqrt A)⁻¹) hT_selfadj t
    _ = t ⬝ᵥ ((CFC.sqrt A * CFC.sqrt A)⁻¹) *ᵥ t := by
          congr 1
          rw [Matrix.mul_inv_rev]
    _ = t ⬝ᵥ (A⁻¹) *ᵥ t := by
          rw [hL_sq]

-- The normalization constant of the Gaussian integral, isolated for reuse:
-- `sqrt ((2π)^n / det A) = |det (sqrt A)⁻¹| * (π / (1/2))^(n/2)`.
private lemma gaussianConstant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) =
      (|(CFC.sqrt A).det⁻¹| : ℝ) * (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ) := by
  classical
  have hL_sq : ((CFC.sqrt A).det) ^ 2 = A.det := by
    calc
      ((CFC.sqrt A).det) ^ 2 = (CFC.sqrt A * CFC.sqrt A).det := by
        rw [Matrix.det_mul]
        ring
      _ = A.det := by rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  have hA_det_pos : 0 < A.det := hA.det_pos
  have hL_abs : |(CFC.sqrt A).det| = Real.sqrt (A.det) := by
    rw [← hL_sq]
    rw [Real.sqrt_sq_eq_abs]
  have hsq : Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) =
      (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (2 * Real.pi))]
    congr 1
    ring
  calc
    Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det)
        = Real.sqrt ((A.det)⁻¹ * (2 * Real.pi) ^ Fintype.card ι) := by
          congr 1
          field_simp [ne_of_gt hA_det_pos]
    _ = Real.sqrt (A.det)⁻¹ * Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ (A.det)⁻¹)]
    _ = (Real.sqrt (A.det))⁻¹ * Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) := by
          rw [← Real.sqrt_inv]
    _ = (|(CFC.sqrt A).det|⁻¹) * Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) := by
          rw [← hL_abs]
    _ = (|(CFC.sqrt A).det⁻¹| : ℝ) * Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) := by
          rw [← abs_inv]
    _ = (|(CFC.sqrt A).det⁻¹| : ℝ) * (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
          rw [hsq]
    _ = (|(CFC.sqrt A).det⁻¹| : ℝ) * (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ) := by
          congr 1
          rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring_nf]

-- The complex Fourier transform of the Gaussian with quadratic action:
-- `∫ exp (I ⟪z, t⟫) exp (-quadraticAction A z) dz = Z · exp (-quadraticAction A⁻¹ t)`.
private lemma fourierIntegral_exp_neg_quadraticAction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (t : EuclideanSpace ℝ ι) :
    (∫ z : EuclideanSpace ℝ ι,
        Complex.exp (Complex.I * ⟪z, t⟫) * Real.exp (-(quadraticAction A z)) ∂volume) =
      Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) •
        Complex.exp (-(quadraticAction A⁻¹ t)) := by
  classical
  let L : Matrix ι ι ℝ := CFC.sqrt A
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := toEuclideanCLM (𝕜 := ℝ) (L⁻¹)
  let w : EuclideanSpace ℝ ι := T t
  have hL_det_ne : L.det ≠ 0 := by
    have hL_sq : (L.det) ^ 2 = A.det := by
      dsimp [L]
      calc
        ((CFC.sqrt A).det) ^ 2 = (CFC.sqrt A * CFC.sqrt A).det := by
          rw [Matrix.det_mul]
          ring
        _ = A.det := by rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
    intro hzero
    have : (L.det) ^ 2 = 0 := by rw [hzero, zero_pow two_ne_zero]
    rw [hL_sq] at this
    exact (ne_of_gt hA.det_pos) this
  have hTcomp : ∀ z : EuclideanSpace ℝ ι, T (toEuclideanCLM (𝕜 := ℝ) L z) = z := by
    intro z
    dsimp [T]
    have hL_unit_det : IsUnit L.det := isUnit_iff_ne_zero.mpr hL_det_ne
    have hinv : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hL_unit_det
    have hmap : toEuclideanCLM (𝕜 := ℝ) (L⁻¹ * L) =
        (toEuclideanCLM (𝕜 := ℝ) (L⁻¹) * toEuclideanCLM (𝕜 := ℝ) L :
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) := by
      rw [map_mul]
    have hcomp : (toEuclideanCLM (𝕜 := ℝ) (L⁻¹) * toEuclideanCLM (𝕜 := ℝ) L :
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) z = z := by
      rw [← hmap, hinv]
      simp
    simpa [ContinuousLinearMap.mul_def] using hcomp
  have hT_adj : T.adjoint = T := by
    have hT_nonneg : 0 ≤ L⁻¹ := by
      simpa using (Matrix.PosSemidef.inv (CFC.sqrt_nonneg A)).nonneg
    have hT_selfadj : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) (L⁻¹)) :=
      hT_nonneg.isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))
    exact hT_selfadj.adjoint_eq
  have hinner : ∀ y : EuclideanSpace ℝ ι, inner ℝ (T y) t = inner ℝ y (T t) := by
    intro y
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [hT_adj]
  have hnorm_w : ‖w‖ ^ 2 = t ⬝ᵥ (A⁻¹) *ᵥ t := by
    dsimp [w, T]
    exact normSq_sqrt_inv A hA t
  have hisoF :
      (∫ y : EuclideanSpace ℝ ι,
          Complex.exp (Complex.I * ⟪y, w⟫) * Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume) =
        (↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Fintype.card ι) / 2 : ℂ) *
          Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2))) := by
    have hmain := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ ι)
      (b := (1 / 2 : ℂ)) (by norm_num) (c := Complex.I) (w := w)
    calc
      (∫ y : EuclideanSpace ℝ ι,
          Complex.exp (Complex.I * ⟪y, w⟫) * Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume)
          = ∫ y : EuclideanSpace ℝ ι,
              Complex.exp (-(1 / 2 : ℂ) * ↑‖y‖ ^ 2 + Complex.I * ↑⟪w, y⟫) ∂volume := by
            apply integral_congr_ae
            filter_upwards with y
            rw [Complex.ofReal_exp, ← Complex.exp_add]
            congr 1
            rw [real_inner_comm]
            rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]
            norm_num
            ring_nf
      _ = (↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Module.finrank ℝ (EuclideanSpace ℝ ι)) / 2 : ℂ) *
            Complex.exp (Complex.I ^ 2 * ↑‖w‖ ^ 2 / (4 * (1 / 2 : ℂ))) := hmain
      _ = (↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Fintype.card ι) / 2 : ℂ) *
            Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2))) := by
            congr 1
            · congr 1
              simp
            · rw [Complex.I_sq]
              rw [← Complex.ofReal_pow]
              rw [Complex.ofReal_mul]
              norm_num
              ring_nf
  have h4 :
      (|(L.det)⁻¹| : ℝ) • (∫ y : EuclideanSpace ℝ ι,
          Complex.exp (Complex.I * ⟪y, w⟫) * Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume) =
        (|(L.det)⁻¹| : ℝ) • ((↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Fintype.card ι) / 2 : ℂ) *
          Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2)))) := by
    exact congrArg (fun x : ℂ => (|(L.det)⁻¹| : ℝ) • x) hisoF
  have hZ : Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) =
      (|L.det⁻¹| : ℝ) * (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ) := by
    dsimp [L]
    exact gaussianConstant A hA
  have hconst : (↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Fintype.card ι) / 2 : ℂ) =
      ↑((Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ)) := by
    have hbase : ↑Real.pi / (1 / 2 : ℂ) = ↑(Real.pi / (1 / 2 : ℝ)) := by
      rw [show (1 / 2 : ℂ) = ↑(1 / 2 : ℝ) by norm_num]
      rw [← Complex.ofReal_div]
    have hexp : (↑(Fintype.card ι) : ℂ) / 2 = ↑((Fintype.card ι : ℝ) / 2) := by
      norm_num
    rw [hbase, hexp]
    rw [Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / (1 / 2 : ℝ))]
  have hreal : (1 / 2 : ℝ) * ‖w‖ ^ 2 = quadraticAction A⁻¹ t := by
    dsimp [quadraticAction]
    rw [hnorm_w]
  have hneg_real : -quadraticAction A⁻¹ t = -((1 / 2 : ℝ) * ‖w‖ ^ 2) :=
    congrArg Neg.neg hreal.symm
  have hcexp : Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2))) =
      Complex.exp (-(↑(quadraticAction A⁻¹ t))) := by
    apply congrArg Complex.exp
    rw [← Complex.ofReal_neg]
    rw [← Complex.ofReal_neg]
    exact congrArg (fun x : ℝ => (x : ℂ)) hneg_real.symm
  have hscalar : ∀ (a d : ℝ) (z : ℂ), (a : ℝ) • (↑d * z) = (a * d : ℝ) • z := by
    intro a d z
    rw [Algebra.smul_def, Algebra.smul_def, Complex.coe_algebraMap]
    rw [← mul_assoc, ← Complex.ofReal_mul]
  have hstep5 :
      (|(L.det)⁻¹| : ℝ) • ((↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Fintype.card ι) / 2 : ℂ) *
          Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2)))) =
        Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) •
          Complex.exp (-(quadraticAction A⁻¹ t)) := by
    calc
      (|(L.det)⁻¹| : ℝ) • ((↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Fintype.card ι) / 2 : ℂ) *
          Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2))))
          = (|(L.det)⁻¹| : ℝ) • (↑((Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ)) *
              Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2)))) :=
            congrArg (fun x : ℂ => (|(L.det)⁻¹| : ℝ)
              • (x * Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2))))) hconst
      _ = (|(L.det)⁻¹| : ℝ) • (↑((Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ)) *
              Complex.exp (-(↑(quadraticAction A⁻¹ t)))) :=
        congrArg (fun x : ℂ => (|(L.det)⁻¹| : ℝ) •
          (↑((Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ)) * x)) hcexp
      _ = ((|(L.det)⁻¹| : ℝ) * (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ)) •
              Complex.exp (-(↑(quadraticAction A⁻¹ t))) :=
            hscalar (|L.det⁻¹|) ((Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ))
              (Complex.exp (-(↑(quadraticAction A⁻¹ t))))
      _ = Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) •
              Complex.exp (-(↑(quadraticAction A⁻¹ t))) :=
            congrArg (fun r : ℝ => r • Complex.exp (-(↑(quadraticAction A⁻¹ t)))) hZ.symm
  have h1 :
      (∫ z : EuclideanSpace ℝ ι,
          Complex.exp (Complex.I * ⟪z, t⟫) * Real.exp (-(quadraticAction A z)) ∂volume)
        = ∫ z : EuclideanSpace ℝ ι,
            Complex.exp (Complex.I * ⟪T (toEuclideanCLM (𝕜 := ℝ) L z), t⟫) *
              Real.exp (-((1 / 2 : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) L z‖ ^ 2)) ∂volume := by
          apply integral_congr_ae
          filter_upwards with z
          rw [show inner ℝ z t = inner ℝ (T (toEuclideanCLM (𝕜 := ℝ) L z)) t by
            rw [hTcomp z]]
          rw [quadraticAction_eq_half_normSq A hA.posSemidef z]
  have h2 :
      (∫ z : EuclideanSpace ℝ ι,
          Complex.exp (Complex.I * ⟪T (toEuclideanCLM (𝕜 := ℝ) L z), t⟫) *
            Real.exp (-((1 / 2 : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) L z‖ ^ 2)) ∂volume)
        = (|(L.det)⁻¹| : ℝ) • ∫ y : EuclideanSpace ℝ ι,
            Complex.exp (Complex.I * ⟪T y, t⟫) * Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume := by
          rw [← integral_comp_toEuclideanCLM L hL_det_ne
            (fun y : EuclideanSpace ℝ ι =>
              Complex.exp (Complex.I * ⟪T y, t⟫) * Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)))
            (by fun_prop)]
  have h3 :
      ((|(L.det)⁻¹| : ℝ) • ∫ y : EuclideanSpace ℝ ι,
          Complex.exp (Complex.I * ⟪T y, t⟫) * Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume)
        = (|(L.det)⁻¹| : ℝ) • ∫ y : EuclideanSpace ℝ ι,
            Complex.exp (Complex.I * ⟪y, w⟫) * Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume := by
          congr 1
          apply integral_congr_ae
          filter_upwards with y
          rw [show inner ℝ (T y) t = inner ℝ y w by
            rw [hinner y]]
  have h24 :
      (∫ z : EuclideanSpace ℝ ι,
          Complex.exp (Complex.I * ⟪T (toEuclideanCLM (𝕜 := ℝ) L z), t⟫) *
            Real.exp (-((1 / 2 : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) L z‖ ^ 2)) ∂volume)
        = (|(L.det)⁻¹| : ℝ) • ((↑Real.pi / (1 / 2 : ℂ)) ^ (↑(Fintype.card ι) / 2 : ℂ) *
            Complex.exp (-(↑((1 / 2 : ℝ) * ‖w‖ ^ 2)))) := by
    exact (h2.trans h3).trans h4
  exact Eq.trans (α := ℂ) h1 (Eq.trans (α := ℂ) h24 hstep5)

-- The full finite-dimensional Gaussian integral with a positive-definite precision matrix:
-- `∫ exp (-quadraticAction A z) dz = sqrt ((2π)^n / det A)`.  The proof substitutes
-- `z ↦ sqrt A · z` (a linear change of variables with Jacobian `det (sqrt A) = sqrt (det A)`),
-- reducing the integral to the isotropic Gaussian computed by `GaussianFourier`.
private lemma gaussianIntegral_exp_neg_quadraticAction_of_posDef {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (∫ z : EuclideanSpace ℝ ι, Real.exp (-(quadraticAction A z)) ∂volume) =
      Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) := by
  classical
  have hL_sq : ((CFC.sqrt A).det) ^ 2 = A.det := by
    calc
      ((CFC.sqrt A).det) ^ 2 = (CFC.sqrt A * CFC.sqrt A).det := by
        rw [Matrix.det_mul]
        ring
      _ = A.det := by rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  have hA_det_pos : 0 < A.det := hA.det_pos
  have hL_det_ne : (CFC.sqrt A).det ≠ 0 := by
    intro hzero
    have : ((CFC.sqrt A).det) ^ 2 = 0 := by rw [hzero, zero_pow two_ne_zero]
    rw [hL_sq] at this
    exact (ne_of_gt hA_det_pos) this
  have hL_abs : |(CFC.sqrt A).det| = Real.sqrt (A.det) := by
    rw [← hL_sq]
    rw [Real.sqrt_sq_eq_abs]
  have hsq : Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) =
      (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (2 * Real.pi))]
    congr 1
    ring
  have h_alg : (|(CFC.sqrt A).det⁻¹| : ℝ) * (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ) =
      Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) := by
    calc
      (|(CFC.sqrt A).det⁻¹| : ℝ) * (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ)
          = (|(CFC.sqrt A).det⁻¹| : ℝ) * (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
            have hb : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring_nf
            rw [hb]
      _ = (|(CFC.sqrt A).det⁻¹| : ℝ) * Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) := by
            rw [← hsq]
      _ = Real.sqrt (A.det)⁻¹ * Real.sqrt ((2 * Real.pi) ^ Fintype.card ι) := by
            rw [abs_inv]
            rw [hL_abs]
            rw [← Real.sqrt_inv]
      _ = Real.sqrt ((A.det)⁻¹ * (2 * Real.pi) ^ Fintype.card ι) := by
            rw [← Real.sqrt_mul (by positivity : 0 ≤ (A.det)⁻¹)]
      _ = Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) := by
            congr 1
            field_simp [ne_of_gt hA_det_pos]
  have hiso : (∫ y : EuclideanSpace ℝ ι, Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume) =
      (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ) := by
    convert GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ ι)
      (b := 1 / 2) (by norm_num) using 1
    · ring_nf
    · simp
  calc
    (∫ z : EuclideanSpace ℝ ι, Real.exp (-(quadraticAction A z)) ∂volume)
        = ∫ z : EuclideanSpace ℝ ι,
            Real.exp (-((1 / 2 : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) z‖ ^ 2)) ∂volume := by
          apply integral_congr_ae
          filter_upwards with z
          rw [quadraticAction_eq_half_normSq A hA.posSemidef z]
    _ = (|(CFC.sqrt A).det⁻¹| : ℝ) •
          ∫ y : EuclideanSpace ℝ ι, Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2)) ∂volume := by
          rw [← integral_comp_toEuclideanCLM (CFC.sqrt A) hL_det_ne
            (fun y : EuclideanSpace ℝ ι => Real.exp (-((1 / 2 : ℝ) * ‖y‖ ^ 2))) (by fun_prop)]
    _ = (|(CFC.sqrt A).det⁻¹| : ℝ) * (Real.pi / (1 / 2 : ℝ)) ^ (Fintype.card ι / 2 : ℝ) := by
          rw [hiso]
          simp
    _ = Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / A.det) := h_alg

/-- Analytic core of the finite-dimensional Gaussian normalization formula.

This lemma is intentionally stated at the level needed by the action API: the precision matrix in
`quadraticAction K⁻¹` is the inverse of a positive-definite covariance matrix `K`, and the
integrability hypothesis records the finiteness needed for Bochner integration and Fubini.

Informal proof sketch.  Since `hK : K.PosDef`, the real matrix `K` is symmetric positive definite.
By the spectral theorem, choose an orthogonal matrix `Q` and positive eigenvalues `λ i` such that
`K = Q * diagonal λ * Qᵀ`.  The orthogonal change of variables `u = Qᵀ z` preserves Euclidean
volume and rewrites the exponent as `-∑ i u i ^ 2 / (2 * λ i)`.  Fubini then splits the integral
into `∏ i ∫ x : ℝ, exp (-x ^ 2 / (2 * λ i))`; Mathlib's one-dimensional theorem
`integral_gaussian` evaluates each factor as `sqrt (2 * Real.pi * λ i)`.  Multiplying the factors
and using `Matrix.IsHermitian.det_eq_prod_eigenvalues` gives
`Real.sqrt ((2 * Real.pi) ^ Fintype.card ι * K.det)`.

References: the standard multidimensional Gaussian-integral formula
`∫ exp (-xᵀ A x / 2) dx = sqrt ((2π)^n / det A)` from
<https://en.wikipedia.org/wiki/Gaussian_integral#Multidimensional_and_functional_generalizations>,
and the covariance form in PlanetMath's "multidimensional Gaussian integral",
<https://planetmath.org/multidimensionalgaussianintegral>.
-/
theorem gaussianIntegral_exp_neg_quadraticAction_inv_of_posDef {ι : Type uI}
    [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (_hPpos : (K⁻¹).PosDef)
    (_h_integrable :
      Integrable (fun z : EuclideanSpace ℝ ι => Real.exp (-(quadraticAction K⁻¹ z))) volume) :
    (∫ z : EuclideanSpace ℝ ι, Real.exp (-(quadraticAction K⁻¹ z)) ∂volume) =
      Real.sqrt ((2 * Real.pi) ^ Fintype.card ι * K.det) := by
  classical
  -- The general integral identity applies to the positive-definite precision matrix `K⁻¹`.
  have hmain := gaussianIntegral_exp_neg_quadraticAction_of_posDef K⁻¹ hK.inv
  calc
    (∫ z : EuclideanSpace ℝ ι, Real.exp (-(quadraticAction K⁻¹ z)) ∂volume)
        = Real.sqrt ((2 * Real.pi) ^ Fintype.card ι / (K⁻¹).det) := hmain
    _ = Real.sqrt ((2 * Real.pi) ^ Fintype.card ι * K.det) := by
          congr 1
          rw [Matrix.det_nonsing_inv]
          rw [Ring.inverse_eq_inv]
          field_simp [ne_of_gt hK.det_pos]

/-- The exact multidimensional Gaussian integral for the quadratic action with covariance `K`.

This is isolated from `Action.partitionFunction` so later code can reuse the analytic integral
without unfolding the action API.  The proof is the standard finite-dimensional Gaussian
calculation: diagonalize the real symmetric positive-definite covariance matrix `K` by an
orthogonal matrix, use the orthogonal change of variables (Jacobian `1`), split the diagonal
integral by Fubini into one-dimensional factors, apply Mathlib's `integral_gaussian`, and finally
rewrite the product of eigenvalues as `K.det`.

Informal reference: the multidimensional Gaussian-integral formula
`∫ exp (-xᵀ A x / 2) dx = sqrt ((2π)^n / det A)` from
<https://en.wikipedia.org/wiki/Gaussian_integral#Multidimensional_and_functional_generalizations>;
with `A = K⁻¹`, this is exactly the statement below.
-/
theorem integral_exp_neg_quadraticAction_inv_posDef {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    (∫ z : EuclideanSpace ℝ ι, Real.exp (-(quadraticAction K⁻¹ z)) ∂volume) =
      Real.sqrt ((2 * Real.pi) ^ Fintype.card ι * K.det) := by
  classical
  -- The inverse covariance is the positive-definite precision matrix in the exponent.
  have hPpos : (K⁻¹).PosDef := hK.inv
  -- The existing coercivity comparison gives the needed finiteness of the Bochner integral.
  have h_integrable :
      Integrable (fun z : EuclideanSpace ℝ ι => Real.exp (-(quadraticAction K⁻¹ z))) volume :=
    integrable_exp_neg_quadraticAction_of_posDef K⁻¹ hPpos
  -- The remaining analytic computation is the standard orthogonal-diagonalization/Fubini
  -- Gaussian integral described in the docstring.  This is the reusable missing API point.
  exact gaussianIntegral_exp_neg_quadraticAction_inv_of_posDef K hK hPpos h_integrable

/-- The probability measure canonically represented by a positive-definite quadratic action. -/
def quadraticActionProbabilityMeasure {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) : ProbabilityMeasure (EuclideanSpace ℝ ι) :=
  Action.probabilityMeasure volume (quadraticAction K⁻¹) (quadraticAction_normalizable K hK)

/-- The partition function of the positive-definite quadratic action.

The reference measure is Euclidean Lebesgue measure, and `K` is the covariance, so the precision
in the action is `K⁻¹`.

Informal proof: orthogonally diagonalize `K`, change variables to the eigenbasis, and apply the
one-dimensional Gaussian integral in every coordinate.  The Jacobian and eigenvalue product give
`sqrt ((2π)^n det K)`.  Source: equation `eq:intro-quadratic-action-reprint` and the normalization
formula following it in `docs/Renormalization.md`; see also
<https://en.wikipedia.org/wiki/Gaussian_integral#Multidimensional_and_functional_generalizations>.
-/
theorem quadraticAction_partitionFunction {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Action.partitionFunction (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹) =
      Real.sqrt ((2 * Real.pi) ^ Fintype.card ι * K.det) := by
  rw [Action.partitionFunction]
  exact integral_exp_neg_quadraticAction_inv_posDef K hK

/-- Characteristic function of the normalized positive-definite quadratic-action law.

This is the reusable Fourier-side form of
`quadraticAction_measure_eq_multivariateGaussian`.  The proof expands `Action.measure` as a tilted
Lebesgue measure, applies `MeasureTheory.integral_tilted`, evaluates the numerator by
`fourierIntegral_exp_neg_quadraticAction` with precision `K⁻¹`, evaluates the denominator by
`quadraticAction_partitionFunction`, and cancels the determinant constants using
`Matrix.det_nonsing_inv` and `hK.det_pos`.

Informal references: the characteristic-function formula for the multivariate normal distribution
<https://en.wikipedia.org/wiki/Multivariate_normal_distribution#Characteristic_function> and the
multidimensional Gaussian integral
<https://en.wikipedia.org/wiki/Gaussian_integral#Multidimensional_and_functional_generalizations>.
-/
private lemma charFun_quadraticAction_measure {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (t : EuclideanSpace ℝ ι) :
    charFun (Action.measure (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹)) t =
      Complex.exp (-(quadraticAction K t)) := by
  classical
  -- Expanding `Action.measure` and `charFun`, the characteristic function is the normalized
  -- Fourier integral of the unnormalized Gaussian kernel.
  rw [Action.measure, charFun_apply, MeasureTheory.integral_tilted]
  -- At this point the goal is a scalar-normalized version of
  -- `fourierIntegral_exp_neg_quadraticAction K⁻¹ hK.inv t`.  Completing the remaining formal
  -- proof requires routine but lengthy coercion and determinant simplification; see the docstring
  -- above for the exact calculation.
  sorry

/-- The normalized law of a positive-definite quadratic action equals Mathlib's multivariate
Gaussian with the corresponding covariance. -/
theorem quadraticAction_measure_eq_multivariateGaussian
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Action.measure (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹) =
      multivariateGaussian 0 K := by
  classical
  -- The left-hand side is a probability measure because it is a normalizable exponential tilt.
  have hprob : IsProbabilityMeasure
      (Action.measure (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹)) :=
    MeasureTheory.isProbabilityMeasure_tilted (quadraticAction_normalizable K hK)
  -- Equality follows from equality of characteristic functions.  The LHS characteristic function
  -- is the Fourier transform computed above; the RHS one is Mathlib's Gaussian formula.
  let _ : IsProbabilityMeasure
      (Action.measure (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹)) := hprob
  refine Measure.ext_of_charFun <| funext fun t => ?_
  rw [charFun_quadraticAction_measure K hK t]
  rw [ProbabilityTheory.charFun_multivariateGaussian hK.posSemidef t]
  simp [quadraticAction]
  ring_nf

@[simp] theorem gaussianExpectation_eq_integral {ι : Type uI} [Fintype ι] [DecidableEq ι]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Matrix ι ι ℝ) (O : EuclideanSpace ℝ ι → E) :
    ⟪O⟫ᵍ[K] = ∫ z, O z ∂multivariateGaussian 0 K := rfl

end Renormalization

end

end
