/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Normed.Module.DoubleDual
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
open scoped Matrix

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
theorem integral_sub_const_sq_le_of_moment_errors {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
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
  simp only [integral_mul_const, integral_const, probReal_univ, smul_eq_mul, one_mul] at he
  rw [he]
  nlinarith only [hsecond, hcross]

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

variable {Ω p : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype p]

/-- Quadratic forms of a square-integrable random vector integrate against its second-moment
matrix. -/
theorem integral_dotProduct_mulVec_self (x : Ω → p → ℝ) (hx : ∀ j, MemLp (fun ω => x ω j) 2 μ)
    (Γ : Matrix p p ℝ) (hΓ : ∀ j k, ∫ ω, x ω j * x ω k ∂μ = Γ j k) (S : Matrix p p ℝ) :
    ∫ ω, x ω ⬝ᵥ (S *ᵥ x ω) ∂μ = Matrix.trace (S * Γ) := by
  have hexp : ∀ ω, x ω ⬝ᵥ (S *ᵥ x ω) = ∑ j, ∑ k, S j k * (x ω j * x ω k) := fun ω => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ j k, Integrable (fun ω => S j k * (x ω j * x ω k)) μ := fun j k =>
    ((hx j).integrable_mul (hx k)).const_mul _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ k, integral_const_mul, hΓ]
  have hsymm : ∀ j k, Γ k j = Γ j k := fun j k => by
    rw [← hΓ, ← hΓ]; exact integral_congr_ae (.of_forall fun ω => mul_comm _ _)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hsymm]


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

/-- **Cauchy-Schwarz with explicit scales:** if `E[X²] ≤ α²` and `E[Y²] ≤ γ²` with `α, γ > 0`,
then `|E[X Y]| ≤ α γ`. -/
theorem abs_integral_mul_le_of_integral_sq_le {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hXb : ∫ ω, X ω ^ 2 ∂μ ≤ α ^ 2)
    (hYb : ∫ ω, Y ω ^ 2 ∂μ ≤ γ ^ 2) : |∫ ω, X ω * Y ω ∂μ| ≤ α * γ := by
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
    {ε K C : ℝ} (hε : 0 < ε) (hK : 0 < K) (hC : 0 < C) {p : ℕ}
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
      rw [mul_pow, Real.sq_sqrt hK.le, ← pow_mul, mul_comm 2 p]
      simpa only [mul_comm p 2, ← pow_mul] using hVb)
    (by
      rw [mul_pow, Real.sq_sqrt hC.le, ← pow_mul]
      exact hQ2)
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_mul hK.le]
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

end ProbabilityTheory
