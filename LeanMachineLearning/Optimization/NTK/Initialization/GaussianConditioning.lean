/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixMeasurability
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianQuadraticVariance

/-!
# Conditional Chebyshev Bounds for the Residual of a Gaussian Weight Matrix

Let `V ~ gaussianInit n p` be a layer's weight matrix and `P` an orthogonal projector built from the
*past* `a ∈ Ω` (e.g. onto the span of the forward features). By Lemma 2.26 the projected part
`V P` and the residual `V Pᗮ` are independent. Quantities such as the backward sensitivities `u`
depend on `V` only through `V P` (and on the *future*, also part of `a`), so, conditionally on
`(a, V P)`, the residual contributes a centred Gaussian quadratic or linear form with explicitly
bounded variance.

* `gaussianInit_measure_le_lintegral_of_section`: the generic transfer. A bound `B x` on the
  `Pᗮ`-section probability, for every value `x` of `V P`, bounds the joint probability by
  `∫ B (V P)`.
* `conditional_quadForm_chebyshev`: for vectors `u = u(V P, a)`, `v = v(V P, a)` and a weight matrix
  `A(a)`,
  `P(|uᵀ (V Pᗮ) A (V Pᗮ)ᵀ v − (u ⬝ᵥ v) tr(Pᗮ A Pᗮ)| ≥ ε) ≤ ∫ min 1 (2 ‖u‖² ‖v‖² ‖A‖_F² / ε²)`
  (the `min 1` makes the bound usable with convergence in measure of the integrand).
* `conditional_linearForm_chebyshev`: `P(|u ⬝ᵥ ((V Pᗮ) b)| ≥ ε) ≤ ∫ min 1 (‖u‖² ‖b‖² / ε²)`.
* `gaussianInit_linearForm_chebyshev`, `integral_linearForm_sq_gaussianInit`: the unconditional
  linear-form analogue of `gaussianInit_quadForm_chebyshev`.

These are the probabilistic core of the decoupling approximation `G_k ≈ G_{k+1} · Φ'_k` and of the
gradient-independence invariant in `Deep/BackwardConcentration.lean`.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace NTK

theorem gaussianInit_measure_le_lintegral_of_section
    (n p : ℕ) (P : Matrix (Fin p) (Fin p) ℝ) (hP : IsStarProjection P)
    (E : Set (Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ)) (hE : MeasurableSet E)
    (B : Matrix (Fin n) (Fin p) ℝ → ℝ≥0∞) (hB : Measurable B)
    (hsec : ∀ x : Matrix (Fin n) (Fin p) ℝ,
      gaussianInit n p {V | (x, Matrix.of V * orthogonalComplement P) ∈ E} ≤ B x) :
    gaussianInit n p {V | (Matrix.of V * P, Matrix.of V * orthogonalComplement P) ∈ E} ≤
      ∫⁻ V, B (Matrix.of V * P) ∂gaussianInit n p := by
  classical
  have hX : Measurable (fun V : Fin n → Fin p → ℝ => Matrix.of V * P) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp (measurable_pi_apply i)).mul_const _
  have hY : Measurable (fun V : Fin n → Fin p → ℝ => Matrix.of V * orthogonalComplement P) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp (measurable_pi_apply i)).mul_const _
  have hind := indepFun_gaussian_orthogonal_projection n p P hP
  have : IsProbabilityMeasure (gaussianInit n p) := by unfold gaussianInit; infer_instance
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable] at hind
  have hpair : Measurable (fun V : Fin n → Fin p → ℝ =>
      (Matrix.of V * P, Matrix.of V * orthogonalComplement P)) := hX.prodMk hY
  have h1 : gaussianInit n p {V | (Matrix.of V * P, Matrix.of V * orthogonalComplement P) ∈ E} =
      ((gaussianInit n p).map (fun V : Fin n → Fin p → ℝ =>
        (Matrix.of V * P, Matrix.of V * orthogonalComplement P))) E := by
    rw [Measure.map_apply hpair hE]; rfl
  rw [h1, hind, Measure.prod_apply hE]
  calc ∫⁻ x, ((gaussianInit n p).map (fun V : Fin n → Fin p → ℝ =>
          Matrix.of V * orthogonalComplement P)) (Prod.mk x ⁻¹' E)
        ∂((gaussianInit n p).map (fun V : Fin n → Fin p → ℝ => Matrix.of V * P))
      ≤ ∫⁻ x, B x ∂((gaussianInit n p).map (fun V : Fin n → Fin p → ℝ => Matrix.of V * P)) := by
        refine lintegral_mono fun x => ?_
        have hsect : MeasurableSet (Prod.mk x ⁻¹' E) := measurable_prodMk_left hE
        rw [Measure.map_apply hY hsect]
        exact hsec x
    _ = ∫⁻ V, B (Matrix.of V * P) ∂gaussianInit n p := lintegral_map hB hX


section linear

/-- Second moment of the bilinear Gaussian linear form: `E[(u ⬝ᵥ W c)²] = ‖u‖² ‖c‖²`. -/
theorem integral_linearForm_sq_gaussianInit (n p : ℕ) (u : Fin n → ℝ) (c : Fin p → ℝ) :
    ∫ W : Fin n → Fin p → ℝ, (u ⬝ᵥ (Matrix.of W *ᵥ c)) ^ 2 ∂(gaussianInit n p) =
      (u ⬝ᵥ u) * (c ⬝ᵥ c) := by
  classical
  have hexp : ∀ W : Fin n → Fin p → ℝ, (u ⬝ᵥ (Matrix.of W *ᵥ c)) ^ 2 =
      ∑ i, ∑ j, ∑ i', ∑ j', (u i * c j * (u i' * c j')) * (W i j * W i' j') := by
    intro W
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  simp_rw [hexp]
  have hint : ∀ i j i' j', Integrable (fun W : Fin n → Fin p → ℝ =>
      (u i * c j * (u i' * c j')) * (W i j * W i' j')) (gaussianInit n p) :=
    fun i j i' j' => (integrable_entry_mul_entry n p i i' j j').const_mul _
  have h1 : ∀ i j i' j', ∫ W : Fin n → Fin p → ℝ,
      (u i * c j * (u i' * c j')) * (W i j * W i' j') ∂(gaussianInit n p) =
      (u i * c j * (u i' * c j')) * (if i = i' ∧ j = j' then 1 else 0) := by
    intro i j i' j'
    rw [integral_const_mul, integral_gaussianInit_entry_mul_entry]
  have hsum : ∫ W : Fin n → Fin p → ℝ,
      ∑ i, ∑ j, ∑ i', ∑ j', (u i * c j * (u i' * c j')) * (W i j * W i' j') ∂(gaussianInit n p) =
      ∑ i, ∑ j, ∑ i', ∑ j', ∫ W : Fin n → Fin p → ℝ,
        (u i * c j * (u i' * c j')) * (W i j * W i' j') ∂(gaussianInit n p) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun i' _ => integrable_finsetSum _ fun j' _ => hint i j i' j']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun i' _ => integrable_finsetSum _ fun j' _ => hint i j i' j']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun i' _ => integrable_finsetSum _ fun j' _ => hint i j i' j']
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [integral_finsetSum _ fun j' _ => hint i j i' j']
  rw [hsum]
  simp_rw [h1]
  simp only [ite_and, mul_ite, mul_one, mul_zero]
  conv_lhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  have hx : ∀ x : Fin n, (∑ y, ∑ x1, ∑ x2, if x = y then (if x1 = x2 then
      u x * c x1 * (u y * c x2) else 0) else 0) = ∑ x1, u x * c x1 * (u x * c x1) := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy.symm]
    · simp
  simp only [hx]
  simp only [dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem memLp_linearForm_gaussianInit (n p : ℕ) (u : Fin n → ℝ) (c : Fin p → ℝ) :
    MemLp (fun W : Fin n → Fin p → ℝ => u ⬝ᵥ (Matrix.of W *ᵥ c)) 2 (gaussianInit n p) := by
  have : (fun W : Fin n → Fin p → ℝ => u ⬝ᵥ (Matrix.of W *ᵥ c)) =
      fun W => ∑ i, ∑ j, (u i * c j) * W i j := by
    funext W
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => (memLp_entry n p i j).const_mul _

theorem integral_linearForm_gaussianInit (n p : ℕ) (u : Fin n → ℝ) (c : Fin p → ℝ) :
    ∫ W : Fin n → Fin p → ℝ, u ⬝ᵥ (Matrix.of W *ᵥ c) ∂(gaussianInit n p) = 0 := by
  have : (fun W : Fin n → Fin p → ℝ => u ⬝ᵥ (Matrix.of W *ᵥ c)) =
      fun W => ∑ i, ∑ j, (u i * c j) * W i j := by
    funext W
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((memLp_entry n p i j).integrable (by norm_num)).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((memLp_entry n p i j).integrable (by norm_num)).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, integral_gaussianInit_entry, mul_zero]

/-- **Chebyshev bound for the Gaussian linear form** `u ⬝ᵥ (W c)`: it is centred with second
moment `‖u‖² ‖c‖²`. -/
theorem gaussianInit_linearForm_chebyshev (n p : ℕ) (u : Fin n → ℝ) (c : Fin p → ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (gaussianInit n p) {W | ε ≤ |u ⬝ᵥ (Matrix.of W *ᵥ c)|} ≤
      ENNReal.ofReal ((u ⬝ᵥ u) * (c ⬝ᵥ c) / ε ^ 2) := by
  classical
  have : IsProbabilityMeasure (gaussianInit n p) := by unfold gaussianInit; infer_instance
  have hmem := memLp_linearForm_gaussianInit n p u c
  have h := meas_ge_le_variance_div_sq hmem hε
  have hmean : (gaussianInit n p)[fun W : Fin n → Fin p → ℝ => u ⬝ᵥ (Matrix.of W *ᵥ c)] = 0 :=
    integral_linearForm_gaussianInit n p u c
  simp only [hmean, sub_zero] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply]
  rw [integral_linearForm_sq_gaussianInit, hmean]
  ring

end linear

section conditional

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Section bound for the quadratic form: for fixed vectors `u₀, v₀` and a projector `Q = Pᗮ`,
the `Pᗮ`-quadratic form concentrates. -/
lemma quadForm_section_le (n p : ℕ) (Q A : Matrix (Fin p) (Fin p) ℝ)
    (hQ : IsStarProjection Q) (u₀ v₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    gaussianInit n p {V | ε ≤ |u₀ ⬝ᵥ (((Matrix.of V * Q) * A * (Matrix.of V * Q)ᵀ) *ᵥ v₀) -
        (u₀ ⬝ᵥ v₀) * (Q * A * Q).trace|} ≤
      ENNReal.ofReal (2 * (u₀ ⬝ᵥ u₀) * (v₀ ⬝ᵥ v₀) * (∑ k, ∑ l, A k l ^ 2) / ε ^ 2) := by
  classical
  have hmat : ∀ V : Fin n → Fin p → ℝ,
      ((Matrix.of V * Q) * A * (Matrix.of V * Q)ᵀ) =
        Matrix.of V * (Q * A * Q) * (Matrix.of V)ᵀ := by
    intro V
    rw [Matrix.transpose_mul, hQ.transpose_eq]
    simp only [Matrix.mul_assoc]
  simp_rw [hmat]
  refine (gaussianInit_quadForm_chebyshev n p u₀ v₀ (Q * A * Q) hε).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  have hu : 0 ≤ u₀ ⬝ᵥ u₀ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hv : 0 ≤ v₀ ⬝ᵥ v₀ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have := frobSq_compress_le Q hQ A
  have h2 : 0 ≤ 2 * (u₀ ⬝ᵥ u₀) * (v₀ ⬝ᵥ v₀) := by positivity
  exact mul_le_mul_of_nonneg_left this h2

theorem conditional_quadForm_chebyshev
    (μ : Measure Ω) (n p : ℕ)
    (P : Ω → Matrix (Fin p) (Fin p) ℝ) (hP : ∀ a, IsStarProjection (P a))
    (hPm : Measurable P) (A : Ω → Matrix (Fin p) (Fin p) ℝ) (hAm : Measurable A)
    (u v : Matrix (Fin n) (Fin p) ℝ × Ω → Fin n → ℝ) (hum : Measurable u) (hvm : Measurable v)
    {ε : ℝ} (hε : 0 < ε) :
    (μ.prod (gaussianInit n p))
      {q | ε ≤ |u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1) * A q.1 *
            (Matrix.of q.2 * orthogonalComplement (P q.1))ᵀ) *ᵥ v (Matrix.of q.2 * P q.1, q.1)) -
        (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
          (orthogonalComplement (P q.1) * A q.1 * orthogonalComplement (P q.1)).trace|} ≤
    ∫⁻ q, min 1 (ENNReal.ofReal
      (2 * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ u (Matrix.of q.2 * P q.1, q.1)) *
      (v (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
      (∑ k, ∑ l, A q.1 k l ^ 2) / ε ^ 2)) ∂(μ.prod (gaussianInit n p)) := by
  classical
  have hγ : IsProbabilityMeasure (gaussianInit n p) := by unfold gaussianInit; infer_instance
  have hOf : Measurable
      (fun q : Ω × (Fin n → Fin p → ℝ) => (Matrix.of q.2 : Matrix (Fin n) (Fin p) ℝ)) :=
    measurable_snd
  have hPq : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => P q.1) := hPm.comp measurable_fst
  have hPc : Measurable (fun a => orthogonalComplement (P a)) := measurable_orthogonalComplement hPm
  have hPcq : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => orthogonalComplement (P q.1)) :=
    hPc.comp measurable_fst
  have hAq : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => A q.1) := hAm.comp measurable_fst
  have hX : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => Matrix.of q.2 * P q.1) :=
    measurable_matrix_mul hOf hPq
  have hY : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) =>
      Matrix.of q.2 * orthogonalComplement (P q.1)) := measurable_matrix_mul hOf hPcq
  have hxa : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => (Matrix.of q.2 * P q.1, q.1)) :=
    hX.prodMk measurable_fst
  have hu' : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => u (Matrix.of q.2 * P q.1, q.1)) :=
    hum.comp hxa
  have hv' : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => v (Matrix.of q.2 * P q.1, q.1)) :=
    hvm.comp hxa
  have hexpr : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) =>
      u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1) * A q.1 *
            (Matrix.of q.2 * orthogonalComplement (P q.1))ᵀ) *ᵥ v (Matrix.of q.2 * P q.1, q.1)) -
        (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
          (orthogonalComplement (P q.1) * A q.1 * orthogonalComplement (P q.1)).trace) := by
    refine (measurable_dotProduct hu' (measurable_mulVec
      (measurable_matrix_mul (measurable_matrix_mul hY hAq) (measurable_matrix_transpose hY))
      hv')).sub ((measurable_dotProduct hu' hv').mul ?_)
    have hM : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) =>
        orthogonalComplement (P q.1) * A q.1 * orthogonalComplement (P q.1)) :=
      measurable_matrix_mul (measurable_matrix_mul hPcq hAq) hPcq
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.measurable_sum _ fun i _ => measurable_matrix_entry hM i i
  have hs : MeasurableSet {q : Ω × (Fin n → Fin p → ℝ) | ε ≤ |u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1) * A q.1 *
            (Matrix.of q.2 * orthogonalComplement (P q.1))ᵀ) *ᵥ v (Matrix.of q.2 * P q.1, q.1)) -
        (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
          (orthogonalComplement (P q.1) * A q.1 * orthogonalComplement (P q.1)).trace|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hexpr)
  refine le_of_eq_of_le (Measure.prod_apply hs) ?_
  have hB : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) =>
      min 1 (ENNReal.ofReal
      (2 * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ u (Matrix.of q.2 * P q.1, q.1)) *
      (v (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
      (∑ k, ∑ l, A q.1 k l ^ 2) / ε ^ 2))) := by
    refine measurable_const.min (ENNReal.measurable_ofReal.comp ?_)
    refine Measurable.div_const (((measurable_const.mul (measurable_dotProduct hu' hu')).mul
      (measurable_dotProduct hv' hv')).mul ?_) _
    exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
      (measurable_matrix_entry hAq k l).pow_const 2
  rw [lintegral_prod _ hB.aemeasurable]
  refine lintegral_mono fun a => ?_
  have hua : Measurable (fun x : Matrix (Fin n) (Fin p) ℝ => u (x, a)) :=
    hum.comp (measurable_id.prodMk measurable_const)
  have hva : Measurable (fun x : Matrix (Fin n) (Fin p) ℝ => v (x, a)) :=
    hvm.comp (measurable_id.prodMk measurable_const)
  have hMa : Measurable (fun z : Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ =>
      z.2 * A a * z.2ᵀ) :=
    measurable_matrix_mul (measurable_matrix_mul measurable_snd measurable_const)
      (measurable_matrix_transpose measurable_snd)
  have hEa : MeasurableSet {z : Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ |
      ε ≤ |u (z.1, a) ⬝ᵥ ((z.2 * A a * z.2ᵀ) *ᵥ v (z.1, a)) -
        (u (z.1, a) ⬝ᵥ v (z.1, a)) *
          (orthogonalComplement (P a) * A a * orthogonalComplement (P a)).trace|} := by
    have h1 : Measurable (fun z : Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ =>
        u (z.1, a)) := hua.comp measurable_fst
    have h2 : Measurable (fun z : Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ =>
        v (z.1, a)) := hva.comp measurable_fst
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp
      ((measurable_dotProduct h1 (measurable_mulVec hMa h2)).sub
        ((measurable_dotProduct h1 h2).mul measurable_const)))
  have hBa : Measurable (fun x : Matrix (Fin n) (Fin p) ℝ =>
      min 1 (ENNReal.ofReal (2 * (u (x, a) ⬝ᵥ u (x, a)) * (v (x, a) ⬝ᵥ v (x, a)) *
        (∑ k, ∑ l, A a k l ^ 2) / ε ^ 2))) := by
    refine measurable_const.min (ENNReal.measurable_ofReal.comp ?_)
    exact Measurable.div_const (((measurable_const.mul (measurable_dotProduct hua hua)).mul
      (measurable_dotProduct hva hva)).mul measurable_const) _
  exact gaussianInit_measure_le_lintegral_of_section n p (P a) (hP a) _ hEa _ hBa
    fun x => le_min prob_le_one (quadForm_section_le n p (orthogonalComplement (P a)) (A a)
      (orthogonalComplement_isOrthogonalProjection _ (hP a)) (u (x, a)) (v (x, a)) hε)


/-- **Normalized conditional quadratic-form bound.** The same statement as
`conditional_quadForm_chebyshev` in the `n⁻²` normalization of the backward Gram matrices: with
`ũ = n⁻¹ ‖u‖²`, `ṽ = n⁻¹ ‖v‖²`, `Ã = n⁻¹ ‖A‖_F²` the right-hand side is
`min 1 (2 ũ ṽ Ã / (n ε²))`, so the `O(1/n)` decay is explicit. -/
theorem conditional_quadForm_chebyshev_normalized
    (μ : Measure Ω) (n p : ℕ) (hn : 0 < n)
    (P : Ω → Matrix (Fin p) (Fin p) ℝ) (hP : ∀ a, IsStarProjection (P a))
    (hPm : Measurable P) (A : Ω → Matrix (Fin p) (Fin p) ℝ) (hAm : Measurable A)
    (u v : Matrix (Fin n) (Fin p) ℝ × Ω → Fin n → ℝ) (hum : Measurable u) (hvm : Measurable v)
    {ε : ℝ} (hε : 0 < ε) :
    (μ.prod (gaussianInit n p))
      {q | ε ≤ |((n : ℝ) ^ 2)⁻¹ * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1) * A q.1 *
            (Matrix.of q.2 * orthogonalComplement (P q.1))ᵀ) *ᵥ v (Matrix.of q.2 * P q.1, q.1))) -
        ((n : ℝ) ^ 2)⁻¹ * ((u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
          (orthogonalComplement (P q.1) * A q.1 * orthogonalComplement (P q.1)).trace)|} ≤
    ∫⁻ q, min 1 (ENNReal.ofReal
      (2 * ((n : ℝ)⁻¹ * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ u (Matrix.of q.2 * P q.1, q.1))) *
      ((n : ℝ)⁻¹ * (v (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1))) *
      ((n : ℝ)⁻¹ * ∑ k, ∑ l, A q.1 k l ^ 2) / ((n : ℝ) * ε ^ 2)))
      ∂(μ.prod (gaussianInit n p)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
  have hε' : 0 < (n : ℝ) ^ 2 * ε := by positivity
  have h := conditional_quadForm_chebyshev μ n p P hP hPm A hAm u v hum hvm hε'
  have hset : ∀ q : Ω × (Fin n → Fin p → ℝ),
      ε ≤ |((n : ℝ) ^ 2)⁻¹ * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1) * A q.1 *
            (Matrix.of q.2 * orthogonalComplement (P q.1))ᵀ) *ᵥ v (Matrix.of q.2 * P q.1, q.1))) -
        ((n : ℝ) ^ 2)⁻¹ * ((u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
          (orthogonalComplement (P q.1) * A q.1 * orthogonalComplement (P q.1)).trace)| ↔
      (n : ℝ) ^ 2 * ε ≤ |u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1) * A q.1 *
            (Matrix.of q.2 * orthogonalComplement (P q.1))ᵀ) *ᵥ v (Matrix.of q.2 * P q.1, q.1)) -
        (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ v (Matrix.of q.2 * P q.1, q.1)) *
          (orthogonalComplement (P q.1) * A q.1 * orthogonalComplement (P q.1)).trace| := by
    intro q
    rw [← mul_sub, abs_mul, abs_of_pos hc, ← div_eq_inv_mul, le_div_iff₀ (by positivity),
      mul_comm]
  simp_rw [hset]
  refine h.trans (le_of_eq (lintegral_congr fun q => ?_))
  congr 2
  field_simp

lemma linearForm_section_le (n p : ℕ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (hQ : IsStarProjection Q) (u₀ : Fin n → ℝ) (b : Fin p → ℝ) {ε : ℝ} (hε : 0 < ε) :
    gaussianInit n p {V | ε ≤ |u₀ ⬝ᵥ ((Matrix.of V * Q) *ᵥ b)|} ≤
      ENNReal.ofReal ((u₀ ⬝ᵥ u₀) * (b ⬝ᵥ b) / ε ^ 2) := by
  classical
  simp_rw [← Matrix.mulVec_mulVec]
  refine (gaussianInit_linearForm_chebyshev n p u₀ (Q *ᵥ b) hε).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  have hu : 0 ≤ u₀ ⬝ᵥ u₀ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  exact mul_le_mul_of_nonneg_left (mulVec_dot_self_le Q hQ b) hu

theorem conditional_linearForm_chebyshev
    (μ : Measure Ω) (n p : ℕ)
    (P : Ω → Matrix (Fin p) (Fin p) ℝ) (hP : ∀ a, IsStarProjection (P a))
    (hPm : Measurable P) (b : Ω → Fin p → ℝ) (hbm : Measurable b)
    (u : Matrix (Fin n) (Fin p) ℝ × Ω → Fin n → ℝ) (hum : Measurable u)
    {ε : ℝ} (hε : 0 < ε) :
    (μ.prod (gaussianInit n p))
      {q | ε ≤ |u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1)) *ᵥ b q.1)|} ≤
    ∫⁻ q, min 1 (ENNReal.ofReal
      ((u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ u (Matrix.of q.2 * P q.1, q.1)) *
      (b q.1 ⬝ᵥ b q.1) / ε ^ 2)) ∂(μ.prod (gaussianInit n p)) := by
  classical
  have hγ : IsProbabilityMeasure (gaussianInit n p) := by unfold gaussianInit; infer_instance
  have hOf : Measurable
      (fun q : Ω × (Fin n → Fin p → ℝ) => (Matrix.of q.2 : Matrix (Fin n) (Fin p) ℝ)) :=
    measurable_snd
  have hPq : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => P q.1) := hPm.comp measurable_fst
  have hPc : Measurable (fun a => orthogonalComplement (P a)) := measurable_orthogonalComplement hPm
  have hPcq : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => orthogonalComplement (P q.1)) :=
    hPc.comp measurable_fst
  have hbq : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => b q.1) := hbm.comp measurable_fst
  have hX : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => Matrix.of q.2 * P q.1) :=
    measurable_matrix_mul hOf hPq
  have hY : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) =>
      Matrix.of q.2 * orthogonalComplement (P q.1)) := measurable_matrix_mul hOf hPcq
  have hxa : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => (Matrix.of q.2 * P q.1, q.1)) :=
    hX.prodMk measurable_fst
  have hu' : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) => u (Matrix.of q.2 * P q.1, q.1)) :=
    hum.comp hxa
  have hs : MeasurableSet {q : Ω × (Fin n → Fin p → ℝ) | ε ≤ |u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1)) *ᵥ b q.1)|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp
      (measurable_dotProduct hu' (measurable_mulVec hY hbq)))
  refine le_of_eq_of_le (Measure.prod_apply hs) ?_
  have hB : Measurable (fun q : Ω × (Fin n → Fin p → ℝ) =>
      min 1 (ENNReal.ofReal ((u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ u (Matrix.of q.2 * P q.1, q.1)) *
      (b q.1 ⬝ᵥ b q.1) / ε ^ 2))) :=
    measurable_const.min (ENNReal.measurable_ofReal.comp (Measurable.div_const
      ((measurable_dotProduct hu' hu').mul (measurable_dotProduct hbq hbq)) _))
  rw [lintegral_prod _ hB.aemeasurable]
  refine lintegral_mono fun a => ?_
  have hua : Measurable (fun x : Matrix (Fin n) (Fin p) ℝ => u (x, a)) :=
    hum.comp (measurable_id.prodMk measurable_const)
  have hEa : MeasurableSet {z : Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ |
      ε ≤ |u (z.1, a) ⬝ᵥ (z.2 *ᵥ b a)|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp
      (measurable_dotProduct (hua.comp measurable_fst)
        (measurable_mulVec measurable_snd measurable_const)))
  have hBa : Measurable (fun x : Matrix (Fin n) (Fin p) ℝ =>
      min 1 (ENNReal.ofReal ((u (x, a) ⬝ᵥ u (x, a)) * (b a ⬝ᵥ b a) / ε ^ 2))) :=
    measurable_const.min (ENNReal.measurable_ofReal.comp (Measurable.div_const
      ((measurable_dotProduct hua hua).mul measurable_const) _))
  exact gaussianInit_measure_le_lintegral_of_section n p (P a) (hP a) _ hEa _ hBa
    fun x => le_min prob_le_one (linearForm_section_le n p (orthogonalComplement (P a))
      (orthogonalComplement_isOrthogonalProjection _ (hP a)) (u (x, a)) (b a) hε)

/-- **Normalized conditional linear-form bound.** With `ũ = n⁻¹ ‖u‖²` and `b̃ = n⁻¹ ‖b‖²`:
`P(|n⁻¹ √(n⁻¹) u ⬝ᵥ ((V Pᗮ) b)| ≥ ε) ≤ ∫ min 1 (ũ b̃ / (n ε²))`. This is the size of
`n⁻¹ ⟨b, y⟩` for the residual `y = n^{-1/2} (V Pᗮ)ᵀ u`. -/
theorem conditional_linearForm_chebyshev_normalized
    (μ : Measure Ω) (n p : ℕ) (hn : 0 < n)
    (P : Ω → Matrix (Fin p) (Fin p) ℝ) (hP : ∀ a, IsStarProjection (P a))
    (hPm : Measurable P) (b : Ω → Fin p → ℝ) (hbm : Measurable b)
    (u : Matrix (Fin n) (Fin p) ℝ × Ω → Fin n → ℝ) (hum : Measurable u)
    {ε : ℝ} (hε : 0 < ε) :
    (μ.prod (gaussianInit n p))
      {q | ε ≤ |((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1)) *ᵥ b q.1))|} ≤
    ∫⁻ q, min 1 (ENNReal.ofReal
      (((n : ℝ)⁻¹ * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ u (Matrix.of q.2 * P q.1, q.1))) *
      ((n : ℝ)⁻¹ * (b q.1 ⬝ᵥ b q.1)) / ((n : ℝ) * ε ^ 2)))
      ∂(μ.prod (gaussianInit n p)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt ((n : ℝ)⁻¹) := Real.sqrt_pos.2 (by positivity)
  have hc : 0 < (n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹) := by positivity
  have hε' : 0 < ε / ((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) := by positivity
  have h := conditional_linearForm_chebyshev μ n p P hP hPm b hbm u hum hε'
  have hset : ∀ q : Ω × (Fin n → Fin p → ℝ),
      ε ≤ |((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) * (u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1)) *ᵥ b q.1))| ↔
      ε / ((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) ≤ |u (Matrix.of q.2 * P q.1, q.1) ⬝ᵥ
          ((Matrix.of q.2 * orthogonalComplement (P q.1)) *ᵥ b q.1)| := by
    intro q
    rw [abs_mul, abs_of_pos hc, div_le_iff₀ hc, mul_comm]
  simp_rw [hset]
  refine h.trans (le_of_eq (lintegral_congr fun q => ?_))
  congr 2
  have hsq : Real.sqrt ((n : ℝ)⁻¹) ^ 2 = (n : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  rw [div_pow, mul_pow, hsq]
  field_simp

end conditional

end NTK

end
