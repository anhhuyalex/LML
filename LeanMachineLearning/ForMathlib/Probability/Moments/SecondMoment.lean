/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Second moments of a square-integrable random vector

For a random vector `x : Ω → p → ℝ` with square-integrable coordinates and second-moment matrix
`Γ j k = E[x_j x_k]`:

* `ProbabilityTheory.integral_dotProduct_mulVec_self`: `E[xᵀ S x] = Tr (S Γ)`;
* `ProbabilityTheory.integral_dotProduct_mul_dotProduct`: `E[(x ⬝ a)(x ⬝ b)] = a ⬝ Γ b`;
* `ProbabilityTheory.abs_integral_mul_le_weighted_add`: weighted AM-GM,
  `|E[X Y]| ≤ (l E[X²] + l⁻¹ E[Y²]) / 2`;
* `ProbabilityTheory.integral_mul_le_half_add`: AM-GM, `E[X Y] ≤ (E[X²] + E[Y²]) / 2`;
* `ProbabilityTheory.abs_integral_mul_le_of_integral_sq_le`: Cauchy-Schwarz with explicit scales.
* `ProbabilityTheory.norm_setIntegral_le_mul_of_integral_sq_le`: Cauchy-Schwarz on a small set.
* `ProbabilityTheory.variance_le_of_moment_errors`: control of variance from two moment errors.
* `ProbabilityTheory.integral_sub_const_sq_le_of_moment_errors`: the corresponding
  mean-square bound.

* `ProbabilityTheory.integral_add_pow_two_mul_le`: even moments of a sum.
* `ProbabilityTheory.integral_smul_apply_eq_apply_integral_smul_sub_add`: centring a weighted
  integral of a linear image of a square-integrable vector.
* `ProbabilityTheory.norm_integral_smul_sub_le_of_integral_dual_sq_le`: if every continuous
  linear form `φ` of `F - m` has second moment at most `C ‖φ‖²`, then
  `‖∫ f • (F - m)‖ ≤ √(C ∫ f²)`.

They reduce every bilinear second-moment computation to the coordinate covariances (used for the
double-descent risk decompositions and for Gaussian matrix forms).
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped Matrix Topology

/-- The square integral of a weighted finite sum is bounded by the sum of absolute weights
times the weighted sum of square integrals. No probability or independence assumption is needed. -/
theorem integral_sq_weighted_sum_le {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset I) (c : I → ℝ) (X : I → Ω → ℝ) (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    (∫ ω, (∑ i ∈ s, c i * X i ω) ^ 2 ∂μ) ≤
      (∑ i ∈ s, |c i|) * ∑ i ∈ s, |c i| * ∫ ω, X i ω ^ 2 ∂μ := by
  have hs : MemLp (fun ω => ∑ i ∈ s, c i * X i ω) 2 μ :=
    memLp_finsetSum s fun i hi => (hX i hi).const_mul _
  calc
    (∫ ω, (∑ i ∈ s, c i * X i ω) ^ 2 ∂μ) ≤
        ∫ ω, (∑ i ∈ s, |c i|) * ∑ i ∈ s, |c i| * X i ω ^ 2 ∂μ := by
      refine integral_mono hs.integrable_sq
        ((integrable_finsetSum s fun i hi => (hX i hi).integrable_sq.const_mul _).const_mul _)
        (fun ω => ?_)
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (fun i _ => abs_nonneg (c i)) (fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      intro i _
      apply le_of_eq
      rw [mul_pow, ← mul_assoc, ← sq, sq_abs]
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum s fun i hi =>
        (hX i hi).integrable_sq.const_mul _]
      simp_rw [integral_const_mul]

/-- The square integral of a finite sum over a `Finset` is bounded by the number of terms times
the sum of their square integrals. No probability or independence assumption is needed. -/
theorem integral_sq_finset_sum_le {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset I) (X : I → Ω → ℝ) (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ) ≤
      (s.card : ℝ) * ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ := by
  simpa using integral_sq_weighted_sum_le s (fun _ => 1) X hX

/-- The square integral of a finite sum is bounded by the number of terms times
the sum of their square integrals. No probability or independence assumption is needed. -/
theorem integral_sq_fintype_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {X : I → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) :
    (∫ ω, (∑ i, X i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
  simpa using integral_sq_finset_sum_le Finset.univ X (fun i _ => hX i)

/-- If the first two moments approximate those of a constant, the mean-square error is small.
No sign hypotheses on the target or the stated error bounds are needed. -/
theorem integral_sub_const_sq_le_of_moment_errors_of_measureReal_le_one {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : μ.real Set.univ ≤ 1)
    {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {G ε₁ ε₂ : ℝ} (h₁ : |(∫ ω, X ω ∂μ) - G| ≤ ε₁)
    (h₂ : |(∫ ω, X ω ^ 2 ∂μ) - G ^ 2| ≤ ε₂) :
    (∫ ω, (X ω - G) ^ 2 ∂μ) ≤ ε₂ + 2 * |G| * ε₁ := by
  have hc : |2 * G * ((∫ ω, X ω ∂μ) - G)| ≤ 2 * |G| * ε₁ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left h₁ (by positivity)
  have hsecond := (le_abs_self _).trans h₂
  have hcross := (abs_le.mp hc).1
  have he := integral_sq_sub hX.integrable_sq (integrable_const (G ^ 2))
    ((hX.integrable one_le_two).mul_const G)
  simp only [integral_mul_const, integral_const, smul_eq_mul] at he
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hμ (sq_nonneg G)
  nlinarith only [hsecond, hcross, hm]

/-- If the first two moments approximate those of a constant, the mean-square error is small,
on a probability space. -/
theorem integral_sub_const_sq_le_of_moment_errors {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {G ε₁ ε₂ : ℝ} (h₁ : |(∫ ω, X ω ∂μ) - G| ≤ ε₁)
    (h₂ : |(∫ ω, X ω ^ 2 ∂μ) - G ^ 2| ≤ ε₂) :
    (∫ ω, (X ω - G) ^ 2 ∂μ) ≤ ε₂ + 2 * |G| * ε₁ :=
  integral_sub_const_sq_le_of_moment_errors_of_measureReal_le_one (by simp) hX h₁ h₂

/-- The variance of `X` is bounded by the mean-square distance to any constant `G`. -/
theorem variance_le_integral_sub_const_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (G : ℝ) :
    variance X μ ≤ ∫ ω, (X ω - G) ^ 2 ∂μ := by
  calc variance X μ = variance (fun ω => X ω - G) μ :=
        (variance_sub_const hX.aestronglyMeasurable G).symm
    _ ≤ ∫ ω, (X ω - G) ^ 2 ∂μ :=
        variance_le_expectation_sq (hX.sub (memLp_const G)).aestronglyMeasurable

/-- The mean-square distance to the mean is bounded by the mean-square distance to any constant. -/
theorem integral_sub_integral_sq_le_integral_sub_const_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (G : ℝ) :
    ∫ ω, (X ω - ∫ y, X y ∂μ) ^ 2 ∂μ ≤ ∫ ω, (X ω - G) ^ 2 ∂μ := by
  rw [← variance_eq_integral hX.aemeasurable]
  exact variance_le_integral_sub_const_sq hX G

/-- The variance bound follows from the stronger mean-square approximation to a constant. -/
theorem variance_le_of_moment_errors {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {G ε₁ ε₂ : ℝ} (h₁ : |(∫ ω, X ω ∂μ) - G| ≤ ε₁)
    (h₂ : |(∫ ω, X ω ^ 2 ∂μ) - G ^ 2| ≤ ε₂) :
    variance X μ ≤ ε₂ + 2 * |G| * ε₁ :=
  (variance_le_integral_sub_const_sq hX G).trans
    (integral_sub_const_sq_le_of_moment_errors hX h₁ h₂)

/-- **Quadratic forms of a square-integrable random vector integrate against its second-moment
operator,** coordinate free: if `E[⟪a, X⟫ ⟪b, X⟫] = ⟪a, Γ b⟫` then `E[⟪X, S X⟫] = tr (S Γ)`. -/
theorem integral_inner_apply_self_eq_trace {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {X : Ω → E}
    (hX : MemLp X 2 μ) (Γ S : E →ₗ[ℝ] E)
    (hΓ : ∀ a b, ∫ ω, inner ℝ a (X ω) * inner ℝ b (X ω) ∂μ = inner ℝ a (Γ b)) :
    ∫ ω, inner ℝ (X ω) (S (X ω)) ∂μ = LinearMap.trace ℝ E (S ∘ₗ Γ) := by
  set e := stdOrthonormalBasis ℝ E
  have hexp : ∀ ω, inner ℝ (X ω) (S (X ω)) =
      ∑ i, inner ℝ (e i) (X ω) * inner ℝ (S (e i)) (X ω) := fun ω => by
    rw [← LinearMap.adjoint_inner_left, ← e.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.adjoint_inner_left, real_inner_comm (S (e i)), mul_comm]
  have hint : ∀ i, Integrable (fun ω => inner ℝ (e i) (X ω) * inner ℝ (S (e i)) (X ω)) μ :=
    fun i => (hX.const_inner (𝕜 := ℝ) (e i)).integrable_mul (hX.const_inner (𝕜 := ℝ) (S (e i)))
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hint i, LinearMap.trace_comp_comm',
    LinearMap.trace_eq_sum_inner _ e]
  exact Finset.sum_congr rfl fun i _ => by rw [hΓ]; rfl

variable {Ω p : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype p]

/-- Quadratic forms of a square-integrable random vector integrate against its second-moment
matrix. -/
theorem integral_dotProduct_mulVec_self (x : Ω → p → ℝ) (hx : ∀ j, MemLp (fun ω => x ω j) 2 μ)
    (Γ : Matrix p p ℝ) (hΓ : ∀ j k, ∫ ω, x ω j * x ω k ∂μ = Γ j k) (S : Matrix p p ℝ) :
    ∫ ω, x ω ⬝ᵥ (S *ᵥ x ω) ∂μ = Matrix.trace (S * Γ) := by
  classical
  set X : Ω → EuclideanSpace ℝ p := fun ω => WithLp.toLp 2 (x ω)
  have hX : MemLp X 2 μ := memLp_piLp_iff.2 hx
  have hinner : ∀ a b : p → ℝ,
      inner ℝ (WithLp.toLp 2 a) (WithLp.toLp 2 b) = ∑ j, a j * b j := fun a b => by
    simp [PiLp.inner_apply, mul_comm]
  have hquad : ∀ a b : EuclideanSpace ℝ p,
      ∫ ω, inner ℝ a (X ω) * inner ℝ b (X ω) ∂μ =
        inner ℝ a (Matrix.toEuclideanLin Γ b) := fun a b => by
    have hpt : ∀ ω, inner ℝ a (X ω) * inner ℝ b (X ω) =
        ∑ j, ∑ k, (a j * b k) * (x ω j * x ω k) := fun ω => by
      have h1 : inner ℝ a (X ω) = ∑ j, a j * x ω j := hinner a.ofLp (x ω)
      have h2 : inner ℝ b (X ω) = ∑ k, b k * x ω k := hinner b.ofLp (x ω)
      rw [h1, h2, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hint : ∀ j k, Integrable (fun ω => (a j * b k) * (x ω j * x ω k)) μ := fun j k =>
      ((hx j).integrable_mul (hx k)).const_mul _
    have h3 : inner ℝ a (Matrix.toEuclideanLin Γ b) = ∑ j, a j * ∑ k, Γ j k * b k :=
      hinner a.ofLp (Γ *ᵥ b.ofLp)
    simp_rw [hpt]
    rw [h3, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, hΓ]
    ring
  have h := integral_inner_apply_self_eq_trace hX (Matrix.toEuclideanLin Γ)
    (Matrix.toEuclideanLin S) hquad
  have hL : ∀ ω, inner ℝ (X ω) (Matrix.toEuclideanLin S (X ω)) = x ω ⬝ᵥ (S *ᵥ x ω) :=
    fun ω => hinner (x ω) (S *ᵥ x ω)
  simp_rw [hL] at h
  have hcomp : Matrix.toEuclideanLin S ∘ₗ Matrix.toEuclideanLin Γ =
      Matrix.toEuclideanLin (S * Γ) := by
    ext v : 1
    exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec v.ofLp S Γ)
  rw [h, hcomp, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun p ℝ).toBasis,
    LinearMap.toMatrix_toLin]

/-- Bilinear second-moment identity: `E[(x ⬝ a)(x ⬝ b)] = a ⬝ Γ b`. -/
theorem integral_dotProduct_mul_dotProduct (x : Ω → p → ℝ) (hx : ∀ j, MemLp (fun ω => x ω j) 2 μ)
    (Γ : Matrix p p ℝ) (hΓ : ∀ j k, ∫ ω, x ω j * x ω k ∂μ = Γ j k) (a b : p → ℝ) :
    ∫ ω, (x ω ⬝ᵥ a) * (x ω ⬝ᵥ b) ∂μ = a ⬝ᵥ (Γ *ᵥ b) := by
  have h := integral_dotProduct_mulVec_self x hx Γ hΓ (Matrix.vecMulVec b a)
  have hpt : ∀ ω, x ω ⬝ᵥ (Matrix.vecMulVec b a *ᵥ x ω) = (x ω ⬝ᵥ a) * (x ω ⬝ᵥ b) := fun ω => by
    rw [Matrix.vecMulVec_mulVec]
    simp [dotProduct_comm]
  simp_rw [hpt] at h
  rw [h, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- Weighted AM-GM for square-integrable variables:
`|E[X Y]| ≤ (l E[X²] + l⁻¹ E[Y²]) / 2` for every `l > 0`. -/
theorem abs_integral_mul_le_weighted_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {l : ℝ} (hl : 0 < l) :
    |∫ ω, X ω * Y ω ∂μ| ≤ (l * ∫ ω, X ω ^ 2 ∂μ + l⁻¹ * ∫ ω, Y ω ^ 2 ∂μ) / 2 := by
  have hXi := hX.integrable_sq
  have hYi := hY.integrable_sq
  have hXY := hX.integrable_mul hY
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hXi.const_mul l)
    (hYi.const_mul l⁻¹), ← integral_div]
  refine (abs_integral_le_integral_abs).trans (integral_mono hXY.abs
    (((hXi.const_mul l).add (hYi.const_mul l⁻¹)).div_const 2) fun ω => ?_)
  simpa only [abs_mul, sq_abs] using
    (mul_le_half_mul_add_inv_mul (a := |X ω|) (b := |Y ω|) hl)

/-- AM-GM for square-integrable variables: `E[X Y] ≤ (E[X²] + E[Y²]) / 2`. -/
theorem integral_mul_le_half_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ ω, X ω * Y ω ∂μ ≤ (∫ ω, X ω ^ 2 ∂μ + ∫ ω, Y ω ^ 2 ∂μ) / 2 := by
  simpa using (le_abs_self _).trans (abs_integral_mul_le_weighted_add hX hY one_pos)

/-- **Cauchy-Schwarz with explicit scales:** if `E[X²] ≤ α²` and `E[Y²] ≤ γ²` with `α, γ ≥ 0`,
then `|E[X Y]| ≤ α γ`. -/
theorem abs_integral_mul_le_of_integral_sq_le {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hXb : ∫ ω, X ω ^ 2 ∂μ ≤ α ^ 2)
    (hYb : ∫ ω, Y ω ^ 2 ∂μ ≤ γ ^ 2) : |∫ ω, X ω * Y ω ∂μ| ≤ α * γ := by
  -- prove the bound for positive scales, then let the slack tend to zero
  suffices h : ∀ α γ : ℝ, 0 < α → 0 < γ → ∫ ω, X ω ^ 2 ∂μ ≤ α ^ 2 →
      ∫ ω, Y ω ^ 2 ∂μ ≤ γ ^ 2 → |∫ ω, X ω * Y ω ∂μ| ≤ α * γ by
    have hlim : Filter.Tendsto (fun δ : ℝ => (α + δ) * (γ + δ)) (𝓝[>] 0) (𝓝 (α * γ)) := by
      have : Continuous fun δ : ℝ => (α + δ) * (γ + δ) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) => ?_)
    exact h _ _ (add_pos_of_nonneg_of_pos hα hδ) (add_pos_of_nonneg_of_pos hγ hδ)
      (hXb.trans (pow_le_pow_left₀ hα (le_add_of_nonneg_right hδ.le) 2))
      (hYb.trans (pow_le_pow_left₀ hγ (le_add_of_nonneg_right hδ.le) 2))
  clear hα hγ hXb hYb α γ
  intro α γ hα hγ hXb hYb
  refine (abs_integral_mul_le_weighted_add hX hY (div_pos hγ hα)).trans ?_
  have h1 : γ / α * ∫ ω, X ω ^ 2 ∂μ ≤ γ / α * α ^ 2 :=
    mul_le_mul_of_nonneg_left hXb (div_pos hγ hα).le
  have h2 : (γ / α)⁻¹ * ∫ ω, Y ω ^ 2 ∂μ ≤ (γ / α)⁻¹ * γ ^ 2 :=
    mul_le_mul_of_nonneg_left hYb (inv_pos.2 (div_pos hγ hα)).le
  have h3 : γ / α * α ^ 2 = α * γ := by field_simp
  have h4 : (γ / α)⁻¹ * γ ^ 2 = α * γ := by field_simp
  linarith

/-- **Cauchy-Schwarz on a small set:** if `μ S ≤ α²` and `E[‖X‖²] ≤ γ²`, then
`‖∫_S X‖ ≤ α γ`. -/
theorem norm_setIntegral_le_mul_of_integral_sq_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {S : Set Ω} (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤) {X : Ω → V}
    (hX : MemLp X 2 μ) {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hSb : μ.real S ≤ α ^ 2)
    (hXb : ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤ γ ^ 2) : ‖∫ ω in S, X ω ∂μ‖ ≤ α * γ := by
  have h1 : MemLp (S.indicator fun _ => (1 : ℝ)) 2 μ :=
    memLp_indicator_const 2 hS.nullMeasurableSet 1 (Or.inr hSfin)
  have hCS := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := S.indicator fun _ => (1 : ℝ))
    (g := fun ω => ‖X ω‖) Real.HolderConjugate.two_two (by rwa [ENNReal.ofReal_ofNat])
    (by rw [ENNReal.ofReal_ofNat]; exact hX.norm)
  simp only [Real.rpow_two, norm_norm, ← Real.sqrt_eq_rpow] at hCS
  have h2 : ∫ ω, ‖S.indicator (fun _ => (1 : ℝ)) ω‖ ^ 2 ∂μ = μ.real S := by
    rw [← integral_indicator_one hS]
    exact integral_congr_ae (ae_of_all _ fun ω => by by_cases h : ω ∈ S <;> simp [h])
  have h3 : ‖∫ ω in S, X ω ∂μ‖ ≤ ∫ ω, ‖S.indicator (fun _ => (1 : ℝ)) ω‖ * ‖X ω‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    rw [← integral_indicator hS]
    exact integral_congr_ae (ae_of_all _ fun ω => by by_cases h : ω ∈ S <;> simp [h])
  refine h3.trans (hCS.trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) hα))
  · rw [h2]
    exact Real.sqrt_le_iff.2 ⟨hα, hSb⟩
  · exact Real.sqrt_le_iff.2 ⟨hγ, hXb⟩

/-- A mixed-power Cauchy-Schwarz bound on an arbitrary measure: an order-`2p` moment for
`V` and an `L²` bound of order `ε⁴` for `Q` give order `ε^(p+2)` for `∫ V^p Q`. -/
theorem abs_integral_pow_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V Q : Ω → ℝ} (hV : AEStronglyMeasurable V P) (hQ : MemLp Q 2 P)
    {ε K C : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (hC : 0 ≤ C) {p : ℕ}
    (hVi : Integrable (fun ω => V ω ^ (2 * p)) P) (hVb : ∫ ω, V ω ^ (2 * p) ∂P ≤ K * ε ^ (2 * p))
    (hQ2 : ∫ ω, Q ω ^ 2 ∂P ≤ C * ε ^ 4) :
    |∫ ω, V ω ^ p * Q ω ∂P| ≤ Real.sqrt (K * C) * ε ^ (p + 2) := by
  have hX : MemLp (fun ω => V ω ^ p) 2 P := by
    refine (memLp_two_iff_integrable_sq (hV.pow p)).2 ?_
    simpa only [Pi.pow_apply, ← pow_mul, mul_comm] using hVi
  have h := abs_integral_mul_le_of_integral_sq_le hX hQ (α := Real.sqrt K * ε ^ p)
    (γ := Real.sqrt C * ε ^ 2) (by positivity) (by positivity)
    (by
      simp only [← pow_mul, mul_comm p 2] at hVb ⊢
      rw [mul_pow, Real.sq_sqrt hK, ← pow_mul, mul_comm 2 p]
      simpa only [mul_comm p 2, ← pow_mul] using hVb)
    (by
      rw [mul_pow, Real.sq_sqrt hC, ← pow_mul]
      exact hQ2)
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_mul hK]
  ring

/-- **Even moments of a sum:** `∫ (X + Y)^{2k} ≤ 2^{2k-1} (∫ X^{2k} + ∫ Y^{2k})` on an arbitrary
measure space, with integrability of the left-hand side. -/
theorem integral_add_pow_two_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) {k : ℕ}
    (hXi : Integrable (fun ω => X ω ^ (2 * k)) μ) (hYi : Integrable (fun ω => Y ω ^ (2 * k)) μ) :
    Integrable (fun ω => (X ω + Y ω) ^ (2 * k)) μ ∧
      ∫ ω, (X ω + Y ω) ^ (2 * k) ∂μ ≤
        2 ^ (2 * k - 1) * ((∫ ω, X ω ^ (2 * k) ∂μ) + ∫ ω, Y ω ^ (2 * k) ∂μ) := by
  have heven : Even (2 * k) := even_two_mul k
  have hpt : ∀ ω, (X ω + Y ω) ^ (2 * k) ≤
      2 ^ (2 * k - 1) * (X ω ^ (2 * k) + Y ω ^ (2 * k)) := fun ω => by
    rw [← heven.pow_abs (X ω + Y ω), ← heven.pow_abs (X ω), ← heven.pow_abs (Y ω)]
    exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _).trans
      (add_pow_le (abs_nonneg _) (abs_nonneg _) _)
  have hdom := (hXi.add hYi).const_mul (2 ^ (2 * k - 1) : ℝ)
  have hi : Integrable (fun ω => (X ω + Y ω) ^ (2 * k)) μ := by
    refine Integrable.mono' hdom ((continuous_pow _).comp_aestronglyMeasurable (hX.add hY))
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (heven.pow_nonneg _)]
    exact hpt ω
  refine ⟨hi, (integral_mono hi hdom hpt).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add hXi hYi]

/-- **Centring a weighted integral.** For `a, X ∈ L²`, a continuous linear map `ℓ` and any
vector `b`, `∫ a • ℓ X = ℓ (∫ a • (X - b)) + (∫ a) • ℓ b`, with integrability of the left-hand
side. -/
theorem integral_smul_apply_eq_apply_integral_smul_sub_add {Ω V W : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {a : Ω → ℝ}
    (ha : MemLp a 2 μ) {X : Ω → V} (hX : MemLp X 2 μ) (ℓ : V →L[ℝ] W) (b : V) :
    Integrable (fun ω => a ω • ℓ (X ω)) μ ∧
      ∫ ω, a ω • ℓ (X ω) ∂μ = ℓ (∫ ω, a ω • (X ω - b) ∂μ) + (∫ ω, a ω ∂μ) • ℓ b := by
  have haX : Integrable (fun ω => a ω • X ω) μ :=
    memLp_one_iff_integrable.1 (ha.smul hX (p := 2) (q := 2) (r := 1))
  have hab : Integrable (fun ω => a ω • b) μ := (ha.integrable one_le_two).smul_const b
  have e : (fun ω => a ω • ℓ (X ω)) = fun ω => ℓ (a ω • X ω) := by
    funext ω
    rw [map_smul]
  have e' : (fun ω => a ω • (X ω - b)) = fun ω => a ω • X ω - a ω • b := by
    funext ω
    exact smul_sub _ _ _
  refine ⟨e ▸ ℓ.integrable_comp haX, ?_⟩
  rw [e, ℓ.integral_comp_comm haX, e', integral_sub haX hab, integral_smul_const, map_sub,
    map_smul, sub_add_cancel]

/-- **Covariance control in norm.** Let `F` take values in a real Banach space and `m` be a
vector. If `∫ φ (F - m)² ≤ C ‖φ‖²` for every continuous linear form `φ`, then every `f ∈ L²`
satisfies `‖∫ f • (F - m)‖ ≤ √(C ∫ f²)`. No finiteness of the measure is needed. -/
theorem norm_integral_smul_sub_le_of_integral_dual_sq_le {Ω V : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : Ω → V} {m : V} {f : Ω → ℝ} (hf : MemLp f 2 μ) (hF : MemLp (fun ω => F ω - m) 2 μ)
    {C : ℝ} (hC : ∀ φ : StrongDual ℝ V, ∫ ω, φ (F ω - m) ^ 2 ∂μ ≤ C * ‖φ‖ ^ 2) :
    ‖∫ ω, f ω • (F ω - m) ∂μ‖ ≤ Real.sqrt (C * ∫ ω, f ω ^ 2 ∂μ) := by
  have hint : Integrable (fun ω => f ω • (F ω - m)) μ :=
    memLp_one_iff_integrable.1 (hf.smul hF (p := 2) (q := 2) (r := 1))
  refine NormedSpace.norm_le_dual_bound ℝ _ (Real.sqrt_nonneg _) fun φ => ?_
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := fun ω => φ (F ω - m))
    Real.HolderConjugate.two_two (by rwa [ENNReal.ofReal_ofNat])
    (by rw [ENNReal.ofReal_ofNat]; exact φ.comp_memLp' hF)
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow, ← abs_mul] at h
  have e : φ (∫ ω, f ω • (F ω - m) ∂μ) = ∫ ω, f ω * φ (F ω - m) ∂μ := by
    rw [← φ.integral_comp_comm hint]
    simp only [map_smul, smul_eq_mul]
  rw [e, Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs.trans h).trans ?_
  have hf0 : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  refine (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hC φ)) (Real.sqrt_nonneg _)).trans_eq ?_
  rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul' C hf0]
  ring

/-- **Iterated Cauchy-Schwarz for a two-level expectation:** if `U ω, V ω ∈ L²(μ ω)` for every `ω`
and `ω ↦ ∫ U² ∂(μ ω)` and `ω ↦ ∫ V² ∂(μ ω)` are integrable under `P` with expectations `≤ α²`
and `≤ γ²` (`α, γ ≥ 0`), and `ω ↦ ∫ U V ∂(μ ω)` is a.e. strongly measurable, then
`ω ↦ ∫ U V ∂(μ ω)` is integrable and `|∫ ω, ∫ U V ∂(μ ω) ∂P| ≤ α * γ`. -/
theorem abs_integral_integral_mul_le_of_integral_sq_le {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] {P : Measure Ω} {μ : Ω → Measure Γ}
    {U V : Ω → Γ → ℝ} (hU2 : ∀ ω, MemLp (U ω) 2 (μ ω)) (hV2 : ∀ ω, MemLp (V ω) 2 (μ ω))
    (hUVm : AEStronglyMeasurable (fun ω => ∫ x, U ω x * V ω x ∂(μ ω)) P)
    (hUi : Integrable (fun ω => ∫ x, U ω x ^ 2 ∂(μ ω)) P)
    (hVi : Integrable (fun ω => ∫ x, V ω x ^ 2 ∂(μ ω)) P)
    {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hUb : ∫ ω, ∫ x, U ω x ^ 2 ∂(μ ω) ∂P ≤ α ^ 2)
    (hVb : ∫ ω, ∫ x, V ω x ^ 2 ∂(μ ω) ∂P ≤ γ ^ 2) :
    Integrable (fun ω => ∫ x, U ω x * V ω x ∂(μ ω)) P ∧
      |∫ ω, ∫ x, U ω x * V ω x ∂(μ ω) ∂P| ≤ α * γ := by
  set sU : Ω → ℝ := fun ω => Real.sqrt (∫ x, U ω x ^ 2 ∂(μ ω))
  set sV : Ω → ℝ := fun ω => Real.sqrt (∫ x, V ω x ^ 2 ∂(μ ω))
  have hsU2 : MemLp sU 2 P := by
    refine (memLp_two_iff_integrable_sq (Continuous.comp_aestronglyMeasurable Real.continuous_sqrt
      hUi.aestronglyMeasurable)).2 ?_
    exact hUi.congr (ae_of_all _ fun ω =>
      (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).symm)
  have hsV2 : MemLp sV 2 P := by
    refine (memLp_two_iff_integrable_sq (Continuous.comp_aestronglyMeasurable Real.continuous_sqrt
      hVi.aestronglyMeasurable)).2 ?_
    exact hVi.congr (ae_of_all _ fun ω =>
      (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).symm)
  have hpt : ∀ ω, |∫ x, U ω x * V ω x ∂(μ ω)| ≤ sU ω * sV ω := fun ω =>
    abs_integral_mul_le_of_integral_sq_le (hU2 ω) (hV2 ω) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).ge
      (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).ge
  have hdom : Integrable (fun ω => sU ω * sV ω) P := hsU2.integrable_mul hsV2
  have hint : Integrable (fun ω => ∫ x, U ω x * V ω x ∂(μ ω)) P :=
    hdom.mono' hUVm (ae_of_all _ fun ω => (Real.norm_eq_abs _).trans_le (hpt ω))
  refine ⟨hint, (abs_integral_le_integral_abs.trans
    (integral_mono hint.abs hdom hpt)).trans ?_⟩
  refine (le_abs_self _).trans (abs_integral_mul_le_of_integral_sq_le hsU2 hsV2 hα hγ ?_ ?_)
  · refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans_le hUb
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  · refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans_le hVb
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

/-- **Bounded-part and tail split for a two-level expectation** (model-free core of the calculation
before Eq. (3.105) in Talagrand): for `F, X ≥ 0` with `𝔼 ⟨X^4⟩ ≤ C_X`, `𝔼 ⟨1_{K₀ ≤ X}⟩ ≤ δ^4` and
`𝔼 ⟨F^2⟩ ≤ A^2` (`K₀, C_X, δ, A ≥ 0`), one has
`𝔼 ⟨F * X⟩ ≤ K₀ * 𝔼 ⟨F⟩ + √(√C_X) * δ * A`. -/
theorem integral_integral_mul_le_add_indicator_tail {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] {P : Measure Ω} {μ : Ω → Measure Γ} [∀ ω, IsFiniteMeasure (μ ω)]
    {F X : Γ → ℝ} (hF0 : ∀ x, 0 ≤ F x) (hX0 : ∀ x, 0 ≤ X x)
    (hFm : Measurable F) (hXm : Measurable X)
    (hF2 : ∀ ω, MemLp F 2 (μ ω)) (hX4 : ∀ ω, MemLp X 4 (μ ω))
    {K₀ C_X δ A : ℝ} (hK₀ : 0 ≤ K₀) (hCX : 0 ≤ C_X) (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (hint_m : ∀ {Y : Γ → ℝ}, Measurable Y → AEStronglyMeasurable (fun ω => ∫ x, Y x ∂(μ ω)) P)
    (hF1i : Integrable (fun ω => ∫ x, F x ∂(μ ω)) P)
    (hF2i : Integrable (fun ω => ∫ x, F x ^ 2 ∂(μ ω)) P)
    (hF2b : ∫ ω, ∫ x, F x ^ 2 ∂(μ ω) ∂P ≤ A ^ 2)
    (hX4i : Integrable (fun ω => ∫ x, X x ^ 4 ∂(μ ω)) P)
    (hX4b : ∫ ω, ∫ x, X x ^ 4 ∂(μ ω) ∂P ≤ C_X)
    (hSi : Integrable
      (fun ω => ∫ x, ({y | K₀ ≤ X y}.indicator (fun _ => (1 : ℝ)) x) ∂(μ ω)) P)
    (hSb : ∫ ω, ∫ x, ({y | K₀ ≤ X y}.indicator (fun _ => (1 : ℝ)) x) ∂(μ ω) ∂P ≤ δ ^ 4) :
    Integrable (fun ω => ∫ x, F x * X x ∂(μ ω)) P ∧
      ∫ ω, ∫ x, F x * X x ∂(μ ω) ∂P ≤
        K₀ * (∫ ω, ∫ x, F x ∂(μ ω) ∂P) + Real.sqrt (Real.sqrt C_X) * δ * A := by
  set S : Set Γ := {y | K₀ ≤ X y}
  have hSm : MeasurableSet S := measurableSet_le measurable_const hXm
  set Ind : Γ → ℝ := S.indicator fun _ => (1 : ℝ)
  have hInd_m : Measurable Ind := measurable_const.indicator hSm
  have hInd_sq : ∀ x, Ind x ^ 2 = Ind x := fun x => by
    dsimp only [Ind]; by_cases h : x ∈ S <;> simp [h]
  have hInd2 : ∀ ω, MemLp Ind 2 (μ ω) := fun ω =>
    memLp_indicator_const 2 hSm.nullMeasurableSet 1 (Or.inr (measure_ne_top (μ ω) _))
  have hX2_fn_mem : ∀ ω, MemLp (fun x => X x ^ 2) 2 (μ ω) := fun ω => by
    refine (memLp_two_iff_integrable_sq (hXm.pow_const 2).aestronglyMeasurable).2 ?_
    have h4 : Integrable (fun x => ‖X x‖ ^ 4) (μ ω) := (hX4 ω).integrable_norm_pow (by norm_num)
    refine h4.congr (ae_of_all _ fun x => ?_)
    change ‖X x‖ ^ 4 = (X x ^ 2) ^ 2
    rw [Real.norm_of_nonneg (hX0 x)]
    ring
  have hX2_mem : ∀ ω, MemLp X 2 (μ ω) := fun ω => (hX4 ω).mono_exponent (by norm_num)
  have hXInd2 : ∀ ω, MemLp (fun x => X x * Ind x) 2 (μ ω) := fun ω => by
    refine (hX2_mem ω).mono' (hXm.mul hInd_m).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    dsimp only [Ind]
    by_cases h : x ∈ S
    · simp only [Set.indicator_of_mem h, mul_one, Real.norm_of_nonneg (hX0 x), le_rfl]
    · simp only [Set.indicator_of_notMem h, mul_zero, norm_zero]; exact hX0 x
  have hX4_eq : ∀ ω, (∫ x, (X x ^ 2) ^ 2 ∂(μ ω)) = ∫ x, X x ^ 4 ∂(μ ω) := fun ω =>
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have hX2S := abs_integral_integral_mul_le_of_integral_sq_le
    (U := fun _ x => X x ^ 2) (V := fun _ x => Ind x) hX2_fn_mem hInd2
    (hint_m ((hXm.pow_const 2).mul hInd_m))
    (hX4i.congr (ae_of_all _ fun ω => (hX4_eq ω).symm))
    (hSi.congr (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun x => (hInd_sq x).symm)))
    (Real.sqrt_nonneg C_X) (sq_nonneg δ)
    (by
      refine (integral_congr_ae (ae_of_all _ hX4_eq)).trans_le ?_
      rwa [Real.sq_sqrt hCX])
    (by
      refine (integral_congr_ae (ae_of_all _ fun ω =>
        integral_congr_ae (ae_of_all _ fun x => hInd_sq x))).trans_le ?_
      exact hSb.trans_eq (by ring))
  have hXInd_sq : ∀ x, (X x * Ind x) ^ 2 = X x ^ 2 * Ind x := fun x => by
    rw [mul_pow, hInd_sq]
  have hFXS := abs_integral_integral_mul_le_of_integral_sq_le
    (U := fun _ => F) (V := fun _ x => X x * Ind x) hF2 hXInd2
    (hint_m (hFm.mul (hXm.mul hInd_m))) hF2i
    (hX2S.1.congr (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun x => (hXInd_sq x).symm)))
    hA (mul_nonneg (Real.sqrt_nonneg _) hδ) hF2b
    (by
      refine (integral_congr_ae (ae_of_all _ fun ω =>
        integral_congr_ae (ae_of_all _ fun x => hXInd_sq x))).trans_le ?_
      refine ((le_abs_self _).trans hX2S.2).trans_eq ?_
      rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)])
  have hpt_split : ∀ x, F x * X x ≤ K₀ * F x + F x * (X x * Ind x) := fun x => by
    dsimp only [Ind]
    by_cases h : x ∈ S
    · simp only [Set.indicator_of_mem h, mul_one]
      exact le_add_of_nonneg_left (mul_nonneg hK₀ (hF0 x))
    · simp only [Set.indicator_of_notMem h, mul_zero, add_zero, mul_comm K₀]
      exact mul_le_mul_of_nonneg_left (not_le.1 h).le (hF0 x)
  have hpt_ω : ∀ ω, ∫ x, F x * X x ∂(μ ω) ≤
      K₀ * (∫ x, F x ∂(μ ω)) + ∫ x, F x * (X x * Ind x) ∂(μ ω) := fun ω => by
    have hi1 : Integrable (fun x => K₀ * F x) (μ ω) :=
      ((hF2 ω).integrable one_le_two).const_mul K₀
    have hi2 : Integrable (fun x => F x * (X x * Ind x)) (μ ω) :=
      (hF2 ω).integrable_mul (hXInd2 ω)
    have hi_lhs : Integrable (fun x => F x * X x) (μ ω) :=
      (hF2 ω).integrable_mul (hX2_mem ω)
    refine (integral_mono hi_lhs (hi1.add hi2) hpt_split).trans_eq ?_
    rw [integral_add' hi1 hi2, integral_const_mul]
  have hdom_P := (hF1i.const_mul K₀).add hFXS.1
  have hFXi : Integrable (fun ω => ∫ x, F x * X x ∂(μ ω)) P :=
    hdom_P.mono' (hint_m (hFm.mul hXm)) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (integral_nonneg fun x => mul_nonneg (hF0 x) (hX0 x))]
      exact hpt_ω ω)
  refine ⟨hFXi, (integral_mono hFXi hdom_P hpt_ω).trans ?_⟩
  rw [integral_add' (hF1i.const_mul K₀) hFXS.1, integral_const_mul]
  have htail := (le_abs_self _).trans hFXS.2
  linarith

section

open scoped RealInnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Common conditional-centering argument for a scaled inner product of two independent samples. -/
theorem integral_prod_inner_sub_mean_pow_le (μ : Measure E) [IsProbabilityMeasure μ] (s : ℝ)
    {k : ℕ} (hk : k ≠ 0) {A B : ℝ} (hA : 0 ≤ A)
    (hnorm : Integrable (fun x : E => ‖x‖ ^ (2 * k)) μ)
    (hB : ∫ x : E, ‖x‖ ^ (2 * k) ∂μ ≤ B)
    (hproj : let b : E := ∫ x, x ∂μ
      ∀ a : E, Integrable (fun x => (s * ⟪a, x⟫ - s * ⟪a, b⟫) ^ (2 * k)) μ ∧
        ∫ x, (s * ⟪a, x⟫ - s * ⟪a, b⟫) ^ (2 * k) ∂μ ≤ A * ‖a‖ ^ (2 * k)) :
    Integrable (fun p : E × E =>
      (s * ⟪p.1, p.2⟫ - ∫ q : E × E, s * ⟪q.1, q.2⟫ ∂(μ.prod μ)) ^ (2 * k)) (μ.prod μ) ∧
    ∫ p : E × E, (s * ⟪p.1, p.2⟫ - ∫ q : E × E, s * ⟪q.1, q.2⟫ ∂(μ.prod μ)) ^ (2 * k)
      ∂(μ.prod μ) ≤ 4 ^ k * (A * B) := by
  have hn : 1 ≤ 2 * k := by omega
  let p : ℝ≥0∞ := Nat.cast (2 * k)
  have hp1 : 1 ≤ p := by
    dsimp only [p]
    exact_mod_cast hn
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpt : p ≠ ∞ := ENNReal.natCast_ne_top _
  have hpow : p.toReal = ((2 * k : ℕ) : ℝ) := by simp [p]
  have hmem : MemLp (fun x : E => x) p μ :=
    (integrable_norm_rpow_iff aestronglyMeasurable_id hp0 hpt).1
      (by simpa only [id_eq, hpow, Real.rpow_natCast] using hnorm)
  let b : E := ∫ x, x ∂μ
  have hid := hmem.integrable hp1
  have hb : ‖b‖ ^ (2 * k) ≤ B := by
    have hb' := norm_integral_rpow_le_integral_norm_rpow hp1 hpt hmem
    have hj : ‖b‖ ^ (2 * k) ≤ ∫ x : E, ‖x‖ ^ (2 * k) ∂μ := by
      simpa only [b, hpow, Real.rpow_natCast] using hb'
    exact hj.trans hB
  have hmean : ∫ q : E × E, s * ⟪q.1, q.2⟫ ∂(μ.prod μ) = s * ⟪b, b⟫ := by
    rw [integral_const_mul]
    exact congrArg (s * ·) (integral_prod_bilin (innerSL ℝ) hid hid)
  let X : E × E → ℝ := fun p => s * ⟪p.1, p.2⟫ - s * ⟪p.1, b⟫
  let Y : E → ℝ := fun x => s * ⟪b, x⟫ - s * ⟪b, b⟫
  have hXm : Measurable X := by fun_prop
  have hYm : Measurable Y := by fun_prop
  have heven : Even (2 * k) := even_two_mul k
  have hXsec : Integrable (fun x => ∫ y, ‖X (x, y) ^ (2 * k)‖ ∂μ) μ := by
    refine (hnorm.const_mul A).mono'
      (((hXm.pow_const _).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [Real.norm_of_nonneg (heven.pow_nonneg _)]
    exact (hproj x).2
  have hXi : Integrable (fun p => X p ^ (2 * k)) (μ.prod μ) :=
    (integrable_prod_iff (hXm.pow_const _).aestronglyMeasurable).2
      ⟨ae_of_all _ fun x => (hproj x).1, hXsec⟩
  have hXI : ∫ p, X p ^ (2 * k) ∂(μ.prod μ) ≤ A * B := by
    rw [integral_prod _ hXi]
    refine (integral_mono hXi.integral_prod_left (hnorm.const_mul A) fun x => (hproj x).2).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hB hA
  have hYi : Integrable (fun p : E × E => Y p.1 ^ (2 * k)) (μ.prod μ) :=
    (hproj b).1.comp_fst μ
  have hYI : ∫ p : E × E, Y p.1 ^ (2 * k) ∂(μ.prod μ) ≤ A * B := by
    rw [integral_fun_fst (fun x => Y x ^ (2 * k)), probReal_univ, one_smul]
    exact (hproj b).2.trans (mul_le_mul_of_nonneg_left hb hA)
  have hsum := integral_add_pow_two_mul_le (μ := μ.prod μ) (X := X) (Y := fun p => Y p.1)
    hXm.aestronglyMeasurable (hYm.comp measurable_fst).aestronglyMeasurable hXi hYi
  have e (p : E × E) : s * ⟪p.1, p.2⟫ - s * ⟪b, b⟫ = X p + Y p.1 := by
    dsimp [X, Y]
    rw [real_inner_comm p.1 b]
    ring
  simp_rw [hmean, e]
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  refine (mul_le_mul_of_nonneg_left (add_le_add hXI hYI) (by positivity)).trans_eq ?_
  rw [← two_mul, ← mul_assoc, ← pow_succ,
    show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]
  norm_num

end

/-- Combine an even moment around an environment-dependent center with the moment of
the displacement of that center from a fixed target. -/
theorem integral_integral_sub_pow_le_of_center {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {P : Measure Ω} {G : Ω → Measure α}
    [∀ d, IsProbabilityMeasure (G d)] {R : α → ℝ} (hR : Measurable R) {k : ℕ} (hk : k ≠ 0)
    {center : Ω → ℝ}
    (c : ℝ) (hm : Measurable fun d => ∫ σ, (R σ - c) ^ (2 * k) ∂(G d))
    (hfix : ∀ d, Integrable (fun σ => (R σ - center d) ^ (2 * k)) (G d))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1i : Integrable (fun d => ∫ σ, (R σ - center d) ^ (2 * k) ∂(G d)) P)
    (h1 : ∫ d, ∫ σ, (R σ - center d) ^ (2 * k) ∂(G d) ∂P ≤ a ^ k)
    (h2i : Integrable (fun d => (center d - c) ^ (2 * k)) P)
    (h2 : ∫ d, (center d - c) ^ (2 * k) ∂P ≤ b ^ k) :
    Integrable (fun d => ∫ σ, (R σ - c) ^ (2 * k) ∂(G d)) P ∧
      ∫ d, ∫ σ, (R σ - c) ^ (2 * k) ∂(G d) ∂P ≤ (4 * (a + b)) ^ k := by
  have heven : Even (2 * k) := even_two_mul k
  have hpt : ∀ d, ∫ σ, (R σ - c) ^ (2 * k) ∂(G d) ≤ 2 ^ (2 * k - 1) *
      ((∫ σ, (R σ - center d) ^ (2 * k) ∂(G d)) +
        (center d - c) ^ (2 * k)) := fun d => by
    have h := (integral_add_pow_two_mul_le (μ := G d)
      (X := fun σ => R σ - center d) (Y := fun _ => center d - c)
      (hR.sub_const _).aestronglyMeasurable aestronglyMeasurable_const (hfix d)
      (integrable_const _)).2
    simpa only [sub_add_sub_cancel, integral_const, probReal_univ, one_smul] using h
  have hdom := (h1i.add h2i).const_mul (2 ^ (2 * k - 1) : ℝ)
  have hi : Integrable (fun d => ∫ σ, (R σ - c) ^ (2 * k) ∂(G d)) P :=
    Integrable.mono' hdom hm.aestronglyMeasurable (ae_of_all _ fun d => by
      rw [Real.norm_of_nonneg (integral_nonneg fun σ => heven.pow_nonneg _)]
      exact hpt d)
  refine ⟨hi, (integral_mono hi hdom hpt).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add h1i h2i]
  refine (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)).trans ?_
  have h4 : (2 : ℝ) ^ (2 * k - 1) ≤ 4 ^ k := by
    rw [show (4 : ℝ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
    exact pow_le_pow_right₀ one_le_two (by omega)
  rw [mul_pow]
  exact mul_le_mul h4 (pow_add_pow_le ha hb hk) (by positivity) (by positivity)

end ProbabilityTheory
