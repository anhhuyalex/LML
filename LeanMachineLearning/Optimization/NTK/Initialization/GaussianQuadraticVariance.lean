/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Quartic
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianMatrixAlgebra

/-!
# Second Moment of Gaussian Quadratic Forms

Variance of the bilinear Gaussian quadratic form `u ⬝ᵥ (W A Wᵀ) v` under `W ~ 𝒩(0,1)^{n×p}`,
which is the fluctuation estimate behind the backward-concentration step of the deep NTK
(`G_k ≈ G_{k+1} · Φ'_k`).

1. **Transport** (`map_gaussianInit_toLp_uncurry`): the entries of `W ~ 𝒩(0,1)^{n×p}`, viewed
   as a vector indexed by `Fin n × Fin p`, are a standard Gaussian vector (`stdGaussian`).
2. **Isserlis for quadratic forms** (`integral_quadForm_sq_stdGaussian`): for `z ~ 𝒩(0, I)` and
   any matrix `C`, `E[(zᵀ C z)²] = (tr C)² + tr(C²) + ‖C‖_F²`. It is proved from the already
   formalized four-coordinate Isserlis formula `integral_coordinateProduct_four`
   (`Renormalization/Quartic.lean`), not from a fresh Wick expansion.
3. **Matrix form** (`integral_quadForm_sq_gaussianInit`): with `C = (u vᵀ) ⊗ A`,
   `E[(u ⬝ᵥ W A Wᵀ v)²] = ((u ⬝ᵥ v) tr A)² + (u ⬝ᵥ v)² tr(A²) + ‖u‖² ‖v‖² ‖A‖_F²`.
4. **Chebyshev** (`gaussianInit_quadForm_chebyshev`):
   `P(|u ⬝ᵥ W A Wᵀ v - (u ⬝ᵥ v) tr A| ≥ ε) ≤ 2 ‖u‖² ‖v‖² ‖A‖_F² / ε²`.
-/

@[expose]
public section

open scoped Matrix ENNReal
open MeasureTheory ProbabilityTheory Matrix

namespace NTK

/-! ### Transport of `𝒩(0,1)^{n×p}` to a standard Gaussian vector -/

/-- The entries of a matrix `W`, viewed as a Euclidean vector indexed by pairs `(i, k)`, are
`WithLp.toLp 2 (Function.uncurry W)`; this map is measurable. -/
lemma measurable_toLp_uncurry (n p : ℕ) :
    Measurable (fun W : Fin n → Fin p → ℝ =>
      (WithLp.toLp 2 (Function.uncurry W) : EuclideanSpace ℝ (Fin n × Fin p))) :=
  (PiLp.continuous_toLp 2 _).measurable.comp measurable_uncurry

/-- Currying the rows of a standard Gaussian matrix into one `Fin n × Fin p`-indexed family pushes
`𝒩(0,1)^{n×p}` forward to the product measure over index pairs. -/
lemma map_gaussianInit_pairIndex (n p : ℕ) :
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1).map (fun W : Fin n →
        Fin p → ℝ => Function.uncurry W) =
      Measure.pi (fun _ : Fin n × Fin p => gaussianReal 0 1) := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hg : Measurable (fun W : Fin n → Fin p → ℝ => Function.uncurry W) := measurable_uncurry
  rw [Measure.map_apply hg (MeasurableSet.univ_pi hs)]
  have hpre : (fun W : Fin n → Fin p → ℝ => Function.uncurry W) ⁻¹'
      (Set.univ.pi s) = Set.univ.pi (fun i : Fin n => Set.univ.pi fun k : Fin p => s (i, k)) := by
    ext W; simp [Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- The entries of `W ~ 𝒩(0,1)^{n×p}` form a standard Gaussian vector on `ℝ^{n × p}`. -/
lemma map_gaussianInit_toLp_uncurry (n p : ℕ) :
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1).map (fun W : Fin n →
        Fin p → ℝ =>
      (WithLp.toLp 2 (Function.uncurry W) : EuclideanSpace ℝ (Fin n × Fin p))) =
      stdGaussian (EuclideanSpace ℝ (Fin n × Fin p)) := by
  rw [← map_pi_eq_stdGaussian, ← map_gaussianInit_pairIndex, Measure.map_map (by fun_prop)
    (by fun_prop)]
  rfl

/-! ### Isserlis for quadratic forms of a standard Gaussian vector -/

section stdGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A single coordinate of a standard Gaussian vector in `EuclideanSpace` has finite moments of
every finite order. -/
lemma memLp_coord_stdGaussian (a : ι) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun z : EuclideanSpace ℝ ι => z a) p (stdGaussian (EuclideanSpace ℝ ι)) :=
  IsGaussian.memLp_dual _ (EuclideanSpace.proj a) p hp

omit [DecidableEq ι] in
/-- A product of two Gaussian coordinates is square integrable. -/
lemma memLp_coord_mul_stdGaussian (a b : ι) :
    MemLp (fun z : EuclideanSpace ℝ ι => z a * z b) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
  have h4 : ∀ x : ι, MemLp (fun z : EuclideanSpace ℝ ι => z x) 4
      (stdGaussian (EuclideanSpace ℝ ι)) := fun x => memLp_coord_stdGaussian x 4 (by simp)
  have := MemLp.mul (r := 2) (h4 b) (h4 a)
  convert this using 1

omit [DecidableEq ι] in
/-- A product of four Gaussian coordinates is integrable. -/
lemma integrable_coord_four (a b c d : ι) :
    Integrable (fun z : EuclideanSpace ℝ ι => z a * z b * z c * z d)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have := (memLp_coord_mul_stdGaussian a b).integrable_mul (memLp_coord_mul_stdGaussian c d)
  convert this using 1
  funext z; simp [mul_assoc]

/-- Fourth moment of four standard Gaussian coordinates (Isserlis with `K = 1`). -/
lemma integral_coord_four (a b c d : ι) :
    ∫ z : EuclideanSpace ℝ ι, z a * z b * z c * z d ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      (if a = b then 1 else 0) * (if c = d then 1 else 0) +
        (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0) := by
  have h := Renormalization.QuarticCoupling.integral_coordinateProduct_four
    (1 : Matrix ι ι ℝ) Matrix.PosSemidef.one ![a, b, c, d]
  rw [multivariateGaussian_zero_one] at h
  simp only [Renormalization.QuarticCoupling.coordinateProduct, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.one_apply] at h
  exact h

omit [DecidableEq ι] in
/-- **Second moment of a Gaussian quadratic form.** For `z ~ 𝒩(0, I)` and any matrix `C`,
`E[(zᵀ C z)²] = (tr C)² + tr(C²) + ∑_{ab} C_{ab}²`, so `Var(zᵀ C z) = tr(C²) + ‖C‖_F²`. -/
theorem integral_quadForm_sq_stdGaussian (C : Matrix ι ι ℝ) :
    ∫ z : EuclideanSpace ℝ ι, (∑ a, ∑ b, C a b * (z a * z b)) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      C.trace ^ 2 + ∑ a, ∑ b, C a b * C b a + ∑ a, ∑ b, C a b ^ 2 := by
  classical
  have hexp : ∀ z : EuclideanSpace ℝ ι, (∑ a, ∑ b, C a b * (z a * z b)) ^ 2 =
      ∑ a, ∑ b, ∑ c, ∑ d, C a b * C c d * (z a * z b * z c * z d) := by
    intro z
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hint : ∀ a b c d : ι, Integrable (fun z : EuclideanSpace ℝ ι =>
      C a b * C c d * (z a * z b * z c * z d)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    fun a b c d => (integrable_coord_four a b c d).const_mul _
  simp_rw [hexp]
  have hsum : ∫ z : EuclideanSpace ℝ ι, ∑ a, ∑ b, ∑ c, ∑ d, C a b * C c d * (z a * z b * z c * z d)
      ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∫ z : EuclideanSpace ℝ ι, C a b * C c d * (z a * z b * z c * z d)
        ∂(stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun d _ => hint a b c d]
  rw [hsum]
  have h1 : ∀ a b c d : ι, ∫ z : EuclideanSpace ℝ ι, C a b * C c d * (z a * z b * z c * z d)
      ∂(stdGaussian (EuclideanSpace ℝ ι)) = C a b * C c d *
        ((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
            (if a = d then 1 else 0) * (if b = c then 1 else 0)) := by
    intro a b c d
    rw [integral_const_mul, integral_coord_four]
  simp_rw [h1, mul_add, Finset.sum_add_distrib]
  rw [add_right_comm]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · simp [Matrix.trace, Matrix.diag, sq, Finset.sum_mul_sum]
  · simp
  · simp [sq]

end stdGaussian

/-! ### The matrix quadratic form `u ⬝ᵥ (W A Wᵀ) v` -/

/-- The bilinear Gaussian quadratic form as a quadratic form in the entries of `W`, with the
Kronecker-type coefficient matrix `C_{(i,k),(j,l)} = u_i v_j A_{kl}`. -/
lemma quadForm_eq_sum_coord (n p : ℕ) (u v : Fin n → ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (W : Fin n → Fin p → ℝ) :
    u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v) =
      ∑ x : Fin n × Fin p, ∑ y : Fin n × Fin p,
        (u x.1 * v y.1 * A x.2 y.2) * (Function.uncurry W x * Function.uncurry W y) := by
  rw [quadForm_mul_mul_transpose]
  simp only [Function.uncurry, Fintype.sum_prod_type, mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.of_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    enter [2, k, 2, l]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Second moment of the bilinear Gaussian quadratic form.**
`E[(u ⬝ᵥ W A Wᵀ v)²] = ((u ⬝ᵥ v) tr A)² + (u ⬝ᵥ v)² tr(A²) + ‖u‖² ‖v‖² ‖A‖_F²`. -/
theorem integral_quadForm_sq_gaussianInit (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ∫ W : Fin n → Fin p → ℝ, (u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v)) ^ 2
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) =
      ((u ⬝ᵥ v) * A.trace) ^ 2 + (u ⬝ᵥ v) ^ 2 * ∑ k, ∑ l, A k l * A l k +
        (u ⬝ᵥ u) * (v ⬝ᵥ v) * ∑ k, ∑ l, A k l ^ 2 := by
  classical
  set C : Matrix (Fin n × Fin p) (Fin n × Fin p) ℝ :=
    Matrix.of fun x y => u x.1 * v y.1 * A x.2 y.2 with hC
  have hq : ∀ W : Fin n → Fin p → ℝ, (u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v)) ^ 2 =
      (fun z : EuclideanSpace ℝ (Fin n × Fin p) => (∑ a, ∑ b, C a b * (z a * z b)) ^ 2)
        (WithLp.toLp 2 (Function.uncurry W) : EuclideanSpace ℝ (Fin n × Fin p)) := by
    intro W
    rw [quadForm_eq_sum_coord]
    simp [hC]
  simp_rw [hq]
  rw [← integral_map (measurable_toLp_uncurry n p).aemeasurable
    (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin n × Fin p) =>
      (∑ a, ∑ b, C a b * (z a * z b)) ^ 2).aestronglyMeasurable,
    map_gaussianInit_toLp_uncurry, integral_quadForm_sq_stdGaussian]
  have htr : C.trace = (u ⬝ᵥ v) * A.trace := by
    simp only [hC, Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type, dotProduct,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hF : ∑ a, ∑ b, C a b ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) * ∑ k, ∑ l, A k l ^ 2 := by
    have h1 := sum_prod_prod_mul (fun i j : Fin n => u i ^ 2 * v j ^ 2)
      (fun k l : Fin p => A k l ^ 2)
    have h2 : ∑ i, ∑ j, u i ^ 2 * v j ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
      simp only [dotProduct, Finset.sum_mul_sum, sq]
    simp only [hC, Matrix.of_apply, mul_pow]
    rw [← h2]
    exact h1
  have hS : ∑ a, ∑ b, C a b * C b a = (u ⬝ᵥ v) ^ 2 * ∑ k, ∑ l, A k l * A l k := by
    have h1 := sum_prod_prod_mul (fun i j : Fin n => (u i * v i) * (u j * v j))
      (fun k l : Fin p => A k l * A l k)
    have h2 : ∑ i, ∑ j, (u i * v i) * (u j * v j) = (u ⬝ᵥ v) ^ 2 := by
      simp only [dotProduct, Finset.sum_mul_sum, sq]
    rw [← h2]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hC, Matrix.of_apply]
    ring
  rw [htr, hF, hS]

/-- The bilinear Gaussian quadratic form is square integrable. -/
theorem memLp_quadForm_gaussianInit (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    MemLp (fun W : Fin n → Fin p → ℝ => u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v)) 2
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) := by
  classical
  have hz : MemLp (fun z : EuclideanSpace ℝ (Fin n × Fin p) =>
      ∑ x : Fin n × Fin p, ∑ y : Fin n × Fin p,
        (u x.1 * v y.1 * A x.2 y.2) * (z x * z y)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin p))) := by
    refine memLp_finsetSum _ fun x _ => memLp_finsetSum _ fun y _ => ?_
    exact (memLp_coord_mul_stdGaussian x y).const_mul _
  rw [← map_gaussianInit_toLp_uncurry] at hz
  have := hz.comp_of_map (measurable_toLp_uncurry n p).aemeasurable
  convert this using 1
  funext W
  exact quadForm_eq_sum_coord n p u v A W

/-- **Chebyshev bound for the bilinear Gaussian quadratic form.** For `W ~ 𝒩(0,1)^{n×p}`,
`P(|u ⬝ᵥ W A Wᵀ v - (u ⬝ᵥ v) tr A| ≥ ε) ≤ 2 ‖u‖² ‖v‖² ‖A‖_F² / ε²`.
With `A = D` diagonal and the normalization `n⁻²`, the right side is `O(n⁻¹)` when `n⁻¹‖u‖²`,
`n⁻¹‖v‖²` and `n⁻¹ ‖D‖_F²` stay bounded. -/
theorem gaussianInit_quadForm_chebyshev (n p : ℕ) (u v : Fin n → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)
      {W | ε ≤ |u ⬝ᵥ (((Matrix.of W) * A * (Matrix.of W)ᵀ) *ᵥ v) - (u ⬝ᵥ v) * A.trace|} ≤
      ENNReal.ofReal (2 * (u ⬝ᵥ u) * (v ⬝ᵥ v) * (∑ k, ∑ l, A k l ^ 2) / ε ^ 2) := by
  classical
  have hmem := memLp_quadForm_gaussianInit n p u v A
  have hmean := integral_gaussianMatrix_quadForm n p u v A
  have h := meas_ge_le_variance_div_sq hmem hε
  simp only [hmean] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply]
  rw [integral_quadForm_sq_gaussianInit, hmean]
  have hF : 0 ≤ ∑ k, ∑ l, A k l ^ 2 :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
  have hS := sum_mul_transpose_le_frobSq A
  have hCS := dotProduct_sq_le_mul_self u v
  nlinarith [mul_le_mul_of_nonneg_right hS (sq_nonneg (u ⬝ᵥ v)),
    mul_le_mul_of_nonneg_right hCS hF, sq_nonneg (u ⬝ᵥ v)]

end NTK

end
