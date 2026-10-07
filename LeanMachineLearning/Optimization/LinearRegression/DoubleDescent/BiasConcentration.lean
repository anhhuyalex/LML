/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.RandomMatrixFoundations

/-!
# Concentration of the bias projector

TODO
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK



/-- **Transposing a Gaussian matrix.** -/
theorem measurePreserving_gaussianMatrix_transpose (p q : ℕ) :
    MeasurePreserving (fun W : Fin p → Fin q → ℝ => fun j i => W i j)
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1)
      (Measure.pi fun _ : Fin q => Measure.pi fun _ : Fin p => gaussianReal 0 1) := by
  have hu : MeasurePreserving (fun W : Fin p → Fin q → ℝ => Function.uncurry W)
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1)
      (Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1) :=
    ⟨measurable_uncurry, NTK.map_gaussianInit_pairIndex p q⟩
  have hu2 : MeasurePreserving (fun W : Fin q → Fin p → ℝ => Function.uncurry W)
      (Measure.pi fun _ : Fin q => Measure.pi fun _ : Fin p => gaussianReal 0 1)
      (Measure.pi fun _ : Fin q × Fin p => gaussianReal 0 1) :=
    ⟨measurable_uncurry, NTK.map_gaussianInit_pairIndex q p⟩
  have hc : MeasurePreserving (fun ψ : Fin q × Fin p → ℝ => Function.curry ψ)
      (Measure.pi fun _ : Fin q × Fin p => gaussianReal 0 1)
      (Measure.pi fun _ : Fin q => Measure.pi fun _ : Fin p => gaussianReal 0 1) :=
    (hu2.symm (MeasurableEquiv.curry (Fin q) (Fin p) ℝ).symm)
  have hmp := MeasureTheory.measurePreserving_piCongrLeft (α := fun _ : Fin q × Fin p => ℝ)
    (fun _ => gaussianReal 0 1) (Equiv.prodComm (Fin p) (Fin q))
  have := hc.comp (hmp.comp hu)
  convert this using 1
  funext W j i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- **Left orthogonal invariance.** -/
theorem measurePreserving_orthogonal_mul_gaussianMatrix {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℝ)
    (hU : U * Uᵀ = 1) :
    MeasurePreserving (fun W : Fin p → Fin q → ℝ => fun i k => (U * Matrix.of W) i k)
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1)
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1) := by
  have hT := measurePreserving_gaussianMatrix_transpose p q
  have hT' := measurePreserving_gaussianMatrix_transpose q p
  have hR : MeasurePreserving (fun W : Fin q → Fin p → ℝ => fun i k => (Matrix.of W * Uᵀ) i k)
      (Measure.pi fun _ : Fin q => Measure.pi fun _ : Fin p => gaussianReal 0 1)
      (Measure.pi fun _ : Fin q => Measure.pi fun _ : Fin p => gaussianReal 0 1) := by
    refine ⟨?_, map_gaussianMatrix_mul_orthonormal Uᵀ (by simpa using hU)⟩
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _
  have := hT'.comp (hR.comp hT)
  convert this using 1
  funext W i k
  simp [Matrix.mul_apply, mul_comm]


/-- Householder rotation: an orthogonal symmetric matrix sending `v` to `v'` when `‖v‖ = ‖v'‖`. -/
theorem exists_orthogonal_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (v v' : ι → ℝ)
    (h : v ⬝ᵥ v = v' ⬝ᵥ v') :
    ∃ U : Matrix ι ι ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ U *ᵥ v = v' := by
  by_cases hw : v - v' = 0
  · exact ⟨1, by simp, by simp, by simpa [sub_eq_zero] using hw⟩
  set w := v - v' with hwdef
  have hww : w ⬝ᵥ w ≠ 0 := fun h0 => hw (dotProduct_self_eq_zero.1 h0)
  have hwv : 2 * (w ⬝ᵥ v) = w ⬝ᵥ w := by
    simp only [hwdef, sub_dotProduct, dotProduct_sub, dotProduct_comm v' v]
    linarith
  set c : ℝ := 2 / (w ⬝ᵥ w) with hc
  have hcw : c * (w ⬝ᵥ w) = 2 := by rw [hc]; field_simp
  have hsymm : (1 - c • Matrix.vecMulVec w w)ᵀ = 1 - c • Matrix.vecMulVec w w := by
    ext i j
    simp [Matrix.vecMulVec, mul_comm, Matrix.one_apply, eq_comm]
  have hsq : (1 - c • Matrix.vecMulVec w w) * (1 - c • Matrix.vecMulVec w w) = 1 := by
    have hww' : Matrix.vecMulVec w w * Matrix.vecMulVec w w = (w ⬝ᵥ w) • Matrix.vecMulVec w w := by
      rw [Matrix.vecMulVec_mul_vecMulVec]
      ext i j
      simp [Matrix.vecMulVec]
      ring
    rw [sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, one_mul, mul_one, smul_smul, hww', smul_smul]
    have : c * c * (w ⬝ᵥ w) = 2 * c := by rw [mul_assoc, hcw]; ring
    rw [this]
    ext i j
    simp [Matrix.vecMulVec]
    ring
  refine ⟨1 - c • Matrix.vecMulVec w w, by rw [hsymm]; exact hsq, by rw [hsymm]; exact hsq, ?_⟩
  have hmv : Matrix.vecMulVec w w *ᵥ v = (w ⬝ᵥ v) • w := by
    ext i
    simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Finset.mul_sum, Finset.sum_mul,
      mul_comm, mul_left_comm]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hmv]
  have : c * (w ⬝ᵥ v) = 1 := by
    rw [← hwv] at hcw; linarith
  rw [smul_smul, this, one_smul, hwdef]
  abel

theorem gramProjector_orthogonal_mul {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
    [DecidableEq n] [DecidableEq m] (U : Matrix k n ℝ) (hU : Uᵀ * U = 1) (Φ : Matrix n m ℝ) :
    gramProjector (U * Φ) = U * gramProjector Φ * Uᵀ := by
  unfold gramProjector
  have : (U * Φ)ᵀ * (U * Φ) = Φᵀ * Φ := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  rw [this, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem measurable_gramProjector {p q : ℕ} :
    Measurable fun W : Fin p → Fin q → ℝ => gramProjector (Matrix.of W) := by
  have hW : Measurable fun W : Fin p → Fin q → ℝ => (Matrix.of W : Matrix (Fin p) (Fin q) ℝ) :=
    Measurable.of_eval_matrix _ fun i k => (measurable_pi_apply k).comp (measurable_pi_apply i)
  exact measurable_matrix_mul (measurable_matrix_mul hW (measurable_matrix_nonsing_inv.comp
    (measurable_matrix_mul (measurable_matrix_transpose hW) hW))) (measurable_matrix_transpose hW)

theorem measurable_residual_dotProduct {p q : ℕ} :
    Measurable fun x : (Fin p → Fin q → ℝ) × (Fin p → ℝ) =>
      ((1 - gramProjector (Matrix.of x.1)) *ᵥ x.2) ⬝ᵥ ((1 - gramProjector (Matrix.of x.1)) *ᵥ x.2) := by
  have hP : Measurable fun x : (Fin p → Fin q → ℝ) × (Fin p → ℝ) =>
      (1 - gramProjector (Matrix.of x.1) : Matrix (Fin p) (Fin p) ℝ) :=
    measurable_orthogonalComplement (measurable_gramProjector.comp measurable_fst)
  have := measurable_mulVec hP measurable_snd
  exact measurable_dotProduct this this

theorem residual_dotProduct_orthogonal_mul {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (U : Matrix n n ℝ) (hU : U * Uᵀ = 1) (hUt : Uᵀ * U = 1)
    (Φ : Matrix n m ℝ) (v : n → ℝ) :
    ((1 - gramProjector (U * Φ)) *ᵥ v) ⬝ᵥ ((1 - gramProjector (U * Φ)) *ᵥ v) =
      ((1 - gramProjector Φ) *ᵥ (Uᵀ *ᵥ v)) ⬝ᵥ ((1 - gramProjector Φ) *ᵥ (Uᵀ *ᵥ v)) := by
  have h1 : (1 : Matrix n n ℝ) - gramProjector (U * Φ) = U * (1 - gramProjector Φ) * Uᵀ := by
    rw [gramProjector_orthogonal_mul U hUt, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
  have hnorm : ∀ x : n → ℝ, (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := fun x => by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hUt,
      Matrix.one_mulVec]
  rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hnorm]

theorem measurable_residual_dotProduct_const {p q : ℕ} (v : Fin p → ℝ) :
    Measurable fun W : Fin p → Fin q → ℝ =>
      ((1 - gramProjector (Matrix.of W)) *ᵥ v) ⬝ᵥ ((1 - gramProjector (Matrix.of W)) *ᵥ v) := by
  have := (measurable_residual_dotProduct (p := p) (q := q)).comp
    (measurable_id.prodMk (measurable_const (a := v)))
  exact this

/-- **Rotation invariance of the residual norm.** -/
theorem map_residual_dotProduct_eq {p q : ℕ} (v v' : Fin p → ℝ) (h : v ⬝ᵥ v = v' ⬝ᵥ v') :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1).map
        (fun W => ((1 - gramProjector (Matrix.of W)) *ᵥ v) ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ v)) =
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1).map
        (fun W => ((1 - gramProjector (Matrix.of W)) *ᵥ v') ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ v')) := by
  obtain ⟨U0, hU0, hU0', hU0v⟩ := exists_orthogonal_mulVec_eq v v' h
  have hU1 : U0ᵀ * (U0ᵀ)ᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hU0'
  have hU2 : (U0ᵀ)ᵀ * U0ᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hU0
  have hmp := measurePreserving_orthogonal_mul_gaussianMatrix (q := q) U0ᵀ hU1
  have hmeas := measurable_residual_dotProduct_const (q := q) v
  calc _ = Measure.map _ (Measure.map (fun W : Fin p → Fin q → ℝ => fun i k =>
          (U0ᵀ * Matrix.of W) i k) (Measure.pi fun _ : Fin p =>
            Measure.pi fun _ : Fin q => gaussianReal 0 1)) := by rw [hmp.map_eq]
    _ = _ := by
      rw [Measure.map_map hmeas hmp.measurable]
      congr 1
      funext W
      have hof : (Matrix.of fun i k => (U0ᵀ * Matrix.of W) i k) = U0ᵀ * Matrix.of W := rfl
      simp only [Function.comp, hof]
      rw [residual_dotProduct_orthogonal_mul U0ᵀ hU1 hU2, Matrix.transpose_transpose, hU0v]

/-- **Ratio estimate.** If `a` is within `t` of `k` and `b` within `t` of `N`, where `0 ≤ k ≤ N`
and `t = η N / 4` with `η ≤ 1`, then `a / b` is within `η` of `k / N`. -/
theorem abs_div_sub_lt_of_close {a b k N η : ℝ} (hN : 0 < N) (hk0 : 0 ≤ k) (hkN : k ≤ N)
    (hη : 0 < η) (hη1 : η ≤ 1) (ha : |a - k| < η * N / 4) (hb : |b - N| < η * N / 4) :
    |a / b - k / N| < η := by
  have hb' : N / 2 < b := by
    have := (abs_lt.1 hb).1
    nlinarith
  have hbpos : 0 < b := by linarith
  rw [div_sub_div _ _ hbpos.ne' hN.ne', abs_div, abs_of_pos (mul_pos hbpos hN),
    div_lt_iff₀ (mul_pos hbpos hN)]
  have e : a * N - b * k = N * (a - k) - k * (b - N) := by ring
  have h1 : |N * (a - k) - k * (b - N)| ≤ N * |a - k| + k * |b - N| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hN, abs_of_nonneg hk0]
  rw [e]
  have h2 : N * |a - k| ≤ N * (η * N / 4) := mul_le_mul_of_nonneg_left ha.le hN.le
  have h3 : k * |b - N| ≤ N * (η * N / 4) := by
    calc k * |b - N| ≤ k * (η * N / 4) := mul_le_mul_of_nonneg_left hb.le hk0
      _ ≤ N * (η * N / 4) := mul_le_mul_of_nonneg_right hkN (by positivity)
  have h4 : η * (b * N) ≥ η * (N / 2 * N) := by
    have := mul_le_mul_of_nonneg_right hb'.le hN.le
    exact mul_le_mul_of_nonneg_left this hη.le
  nlinarith

/-- **Chi-squared tail for a projected Gaussian vector.** If `P` is an orthogonal projection of
trace `r ≥ 1` and `g` has i.i.d. standard normal entries, then `‖P g‖²` deviates from `r` by `t`
with probability at most `(12 r² + 48 r) / t⁴`. -/
theorem measure_projector_dotProduct_deviation_le {ι : Type} [Fintype ι] (P : Matrix ι ι ℝ)
    (hP : IsStarProjection P) (r : ℕ) (hr : (r : ℝ) = P.trace) (hr1 : 1 ≤ r) {t : ℝ}
    (ht : 0 < t) :
    (Measure.pi fun _ : ι => gaussianReal 0 1)
        {g | t ≤ |(P *ᵥ g) ⬝ᵥ (P *ᵥ g) - r|} ≤
      ENNReal.ofReal ((12 * (r : ℝ) ^ 2 + 48 * r) / t ^ 4) := by
  have : NeZero r := ⟨by omega⟩
  have hmap := map_dotProduct_projector_mulVec P hP r hr
  have hmeas : Measurable fun g : ι → ℝ => (P *ᵥ g) ⬝ᵥ (P *ᵥ g) :=
    measurable_dotProduct (measurable_mulVec (measurable_const (a := P)) measurable_id)
      (measurable_mulVec (measurable_const (a := P)) measurable_id)
  have hset : MeasurableSet {y : ℝ | t ≤ |y - r|} :=
    measurableSet_le measurable_const (by fun_prop)
  have h1 : (Measure.pi fun _ : ι => gaussianReal 0 1)
      {g | t ≤ |(P *ᵥ g) ⬝ᵥ (P *ᵥ g) - r|} =
      ((Measure.pi fun _ : ι => gaussianReal 0 1).map
        (fun g => (P *ᵥ g) ⬝ᵥ (P *ᵥ g))) {y : ℝ | t ≤ |y - r|} :=
    (Measure.map_apply hmeas hset).symm
  rw [h1, hmap, Measure.map_apply (by fun_prop) hset]
  have h2 := measureReal_norm_sq_sub_abs_ge_le (E := EuclideanSpace ℝ (Fin r)) ht
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h2
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h2

/-- **Scaling a vector in the residual norm.** For `g ≠ 0`, `‖(1 - P_S) g‖² / ‖g‖²` has the law
of `‖(1 - P_S) u‖²` for any unit vector `u`, under a Gaussian matrix `S`. -/
theorem map_residual_div_dotProduct_eq {p q : ℕ} (g u : Fin p → ℝ) (hg : g ⬝ᵥ g ≠ 0)
    (hu : u ⬝ᵥ u = 1) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1).map
        (fun W => (((1 - gramProjector (Matrix.of W)) *ᵥ g) ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ g)) / (g ⬝ᵥ g)) =
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1).map
        (fun W => ((1 - gramProjector (Matrix.of W)) *ᵥ u) ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ u)) := by
  have hpos : 0 < g ⬝ᵥ g := lt_of_le_of_ne (by
    rw [← star_trivial g]; exact dotProduct_star_self_nonneg g) (Ne.symm hg)
  set s : ℝ := Real.sqrt (g ⬝ᵥ g) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos
  have hss : s * s = g ⬝ᵥ g := Real.mul_self_sqrt hpos.le
  have hugg : (s⁻¹ • g) ⬝ᵥ (s⁻¹ • g) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  rw [← map_residual_dotProduct_eq (s⁻¹ • g) u (hugg.trans hu.symm)]
  congr 1
  funext W
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← hss]
  field_simp

/-- A Gaussian vector in dimension `n₀ ≥ 1` is almost surely nonzero. -/
theorem ae_dotProduct_self_ne_zero_pi_gaussianReal {n0 : ℕ} (hn : 0 < n0) :
    ∀ᵐ g ∂(Measure.pi fun _ : Fin n0 => gaussianReal 0 1), g ⬝ᵥ g ≠ 0 := by
  rw [ae_iff]
  have : {g : Fin n0 → ℝ | ¬ g ⬝ᵥ g ≠ 0} = Set.univ.pi fun _ => {0} := by
    ext g; simp [dotProduct_self_eq_zero, funext_iff]
  rw [this, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n0)) (measure_singleton _)

private theorem chiSq_tail_numeric {r N η : ℝ} (hr : 0 ≤ r) (hrN : r ≤ N) (hN : 1 ≤ N)
    (hη : 0 < η) :
    (12 * r ^ 2 + 48 * r) / (η * N / 4) ^ 4 ≤ 15360 / (η ^ 4 * N ^ 2) := by
  have hN0 : 0 < N := by linarith
  have h4 : 0 < (η * N / 4) ^ 4 := by positivity
  rw [div_le_div_iff₀ h4 (by positivity)]
  have h1 : 12 * r ^ 2 + 48 * r ≤ 60 * N ^ 2 := by nlinarith
  have h2 : (η * N / 4) ^ 4 = η ^ 4 * N ^ 2 * N ^ 2 / 256 := by ring
  rw [h2]
  have h3 : 0 < η ^ 4 * N ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h3.le]

theorem measurable_isUnit_det_gram {p q : ℕ} :
    MeasurableSet {W : Fin p → Fin q → ℝ | IsUnit ((Matrix.of W)ᵀ * Matrix.of W).det} := by
  have hW : Measurable fun W : Fin p → Fin q → ℝ => (Matrix.of W : Matrix (Fin p) (Fin q) ℝ) :=
    Measurable.of_eval_matrix _ fun i k => (measurable_pi_apply k).comp (measurable_pi_apply i)
  have hdet : Measurable fun W : Fin p → Fin q → ℝ => ((Matrix.of W)ᵀ * Matrix.of W).det :=
    (continuous_id.matrix_det).measurable.comp
      (measurable_matrix_mul (measurable_matrix_transpose hW) hW)
  simp_rw [isUnit_iff_ne_zero]
  exact (hdet (measurableSet_singleton 0)).compl

/-- **Tail bound for the bias projector.** Let `S` be an `n₀ × n` Gaussian matrix with `n < n₀`
and `P_S` the orthogonal projection onto its column span. For a unit vector `u`, the squared
distance `‖(1 - P_S) u‖²` of `u` to the column span deviates from `1 - n / n₀` by `η`
with probability at most `30720 / (η⁴ n₀²)`.

The proof compares `u` with an independent Gaussian vector `g`. By rotation invariance of `S`
(`map_residual_dotProduct_eq`) the law of `‖(1 - P_S) u‖²` equals that of `‖(1 - P_S) g‖² / ‖g‖²`
for each fixed `g ≠ 0`, hence under the product measure. There `‖(1 - P_S) g‖² ~ χ²_{n₀-n}` and
`‖g‖² ~ χ²_{n₀}` (`map_dotProduct_projector_mulVec`), and the fourth-moment tail bound applies to
both. -/
theorem measure_residual_dotProduct_deviation_le {n n0 : ℕ} (hn : n < n0) (u : Fin n0 → ℝ)
    (hu : u ⬝ᵥ u = 1) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (Measure.pi fun _ : Fin n0 => Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {W | η ≤ |((1 - gramProjector (Matrix.of W)) *ᵥ u) ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ u) - (1 - (n : ℝ) / n0)|} ≤
      ENNReal.ofReal (30720 / (η ^ 4 * (n0 : ℝ) ^ 2)) := by
  have hN : (0 : ℝ) < n0 := by exact_mod_cast (by omega : 0 < n0)
  have hN1 : (1 : ℝ) ≤ n0 := by exact_mod_cast (by omega : 1 ≤ n0)
  have hnle : (n : ℝ) ≤ n0 := by exact_mod_cast hn.le
  set t : ℝ := η * n0 / 4 with htdef
  have ht : 0 < t := by positivity
  set μS := Measure.pi fun _ : Fin n0 => Measure.pi fun _ : Fin n => gaussianReal 0 1 with hμS
  set μg := Measure.pi fun _ : Fin n0 => gaussianReal 0 1 with hμg
  let a : (Fin n0 → Fin n → ℝ) × (Fin n0 → ℝ) → ℝ := fun x =>
    ((1 - gramProjector (Matrix.of x.1)) *ᵥ x.2) ⬝ᵥ ((1 - gramProjector (Matrix.of x.1)) *ᵥ x.2)
  let b : (Fin n0 → Fin n → ℝ) × (Fin n0 → ℝ) → ℝ := fun x => x.2 ⬝ᵥ x.2
  have ha : Measurable a := measurable_residual_dotProduct
  have hb : Measurable b := measurable_dotProduct measurable_snd measurable_snd
  set E : Set ((Fin n0 → Fin n → ℝ) × (Fin n0 → ℝ)) :=
    {x | η ≤ |a x / b x - (1 - (n : ℝ) / n0)|} with hEdef
  set E1 : Set ((Fin n0 → Fin n → ℝ) × (Fin n0 → ℝ)) :=
    {x | ¬ IsUnit ((Matrix.of x.1)ᵀ * Matrix.of x.1).det ∨ t ≤ |a x - ((n0 : ℝ) - n)|} with hE1
  set E2 : Set ((Fin n0 → Fin n → ℝ) × (Fin n0 → ℝ)) := {x | t ≤ |b x - n0|} with hE2
  have hEm : MeasurableSet E :=
    measurableSet_le measurable_const (by fun_prop)
  have hE1m : MeasurableSet E1 := by
    have h1 : MeasurableSet {x : (Fin n0 → Fin n → ℝ) × (Fin n0 → ℝ) |
        ¬ IsUnit ((Matrix.of x.1)ᵀ * Matrix.of x.1).det} :=
      measurable_fst measurable_isUnit_det_gram.compl
    have h2 : MeasurableSet {x : (Fin n0 → Fin n → ℝ) × (Fin n0 → ℝ) |
        t ≤ |a x - ((n0 : ℝ) - n)|} := measurableSet_le measurable_const (by fun_prop)
    exact h1.union h2
  have hE2m : MeasurableSet E2 := measurableSet_le measurable_const (by fun_prop)
  -- the good event is contained in the union of the two chi-squared tails
  have hsub : E ⊆ E1 ∪ E2 := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, hE1, hE2, Set.mem_ofPred_eq, not_or, not_not, not_le] at hnot
    obtain ⟨⟨hunit, h1⟩, h2⟩ := hnot
    have hlt := abs_div_sub_lt_of_close (a := a x) (b := b x) (k := (n0 : ℝ) - n) hN
      (by linarith) (by linarith) hη hη1 h1 h2
    have e : (1 - (n : ℝ) / n0) = ((n0 : ℝ) - n) / n0 := by field_simp
    rw [hEdef, Set.mem_ofPred_eq, e] at hx
    exact absurd hlt (not_lt.2 hx)
  -- the law of a section: rotation invariance
  set c : ℝ := 1 - (n : ℝ) / n0 with hc
  have hν : μS {W | η ≤ |((1 - gramProjector (Matrix.of W)) *ᵥ u) ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ u) - c|} = (μS.prod μg) E := by
    have hB : MeasurableSet {y : ℝ | η ≤ |y - c|} :=
      measurableSet_le measurable_const (by fun_prop)
    have hsec : ∀ g : Fin n0 → ℝ, g ⬝ᵥ g ≠ 0 →
        μS ((fun S => (S, g)) ⁻¹' E) = μS {W | η ≤ |((1 - gramProjector (Matrix.of W)) *ᵥ u) ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ u) - c|} := by
      intro g hg
      have hmg : Measurable fun W : Fin n0 → Fin n → ℝ =>
          (((1 - gramProjector (Matrix.of W)) *ᵥ g) ⬝ᵥ
            ((1 - gramProjector (Matrix.of W)) *ᵥ g)) / (g ⬝ᵥ g) :=
        (measurable_residual_dotProduct_const g).div_const _
      have := congrArg (fun m => m {y : ℝ | η ≤ |y - c|})
        (map_residual_div_dotProduct_eq (q := n) g u hg hu)
      simp only [Measure.map_apply hmg hB,
        Measure.map_apply (measurable_residual_dotProduct_const u) hB] at this
      exact this
    rw [Measure.prod_apply_symm hEm]
    rw [lintegral_congr_ae ((ae_dotProduct_self_ne_zero_pi_gaussianReal (by omega)).mono
      fun g hg => hsec g hg), lintegral_const, measure_univ, mul_one]
  have hK : ∀ r : ℝ, 0 ≤ r → r ≤ n0 →
      ENNReal.ofReal ((12 * r ^ 2 + 48 * r) / t ^ 4) ≤ ENNReal.ofReal (15360 / (η ^ 4 * (n0 : ℝ) ^ 2)) :=
    fun r h0 h1 => ENNReal.ofReal_le_ofReal (chiSq_tail_numeric h0 h1 hN1 hη)
  -- first tail: the residual `‖(1 - P_S) g‖²`
  have hE1b : (μS.prod μg) E1 ≤ ENNReal.ofReal (15360 / (η ^ 4 * (n0 : ℝ) ^ 2)) := by
    rw [Measure.prod_apply hE1m]
    have hae : ∀ᵐ S ∂μS, IsUnit ((Matrix.of S)ᵀ * Matrix.of S).det :=
      ae_isUnit_det_gram_gaussianMatrix n n0 hn.le
    calc ∫⁻ S, μg (Prod.mk S ⁻¹' E1) ∂μS
        ≤ ∫⁻ _, ENNReal.ofReal (15360 / (η ^ 4 * (n0 : ℝ) ^ 2)) ∂μS := by
          refine lintegral_mono_ae (hae.mono fun S hS => ?_)
          have hP := (isOrthogonalProjection_gramProjector (Matrix.of S) hS).one_sub
          have hr : ((n0 - n : ℕ) : ℝ) = (1 - gramProjector (Matrix.of S)).trace := by
            rw [Matrix.trace_sub, Matrix.trace_one, trace_gramProjector _ hS,
              Fintype.card_fin, Fintype.card_fin, Nat.cast_sub hn.le]
          have h := measure_projector_dotProduct_deviation_le _ hP (n0 - n) hr
            (by omega) ht
          have hset : Prod.mk S ⁻¹' E1 = {g | t ≤ |((1 - gramProjector (Matrix.of S)) *ᵥ g) ⬝ᵥ
              ((1 - gramProjector (Matrix.of S)) *ᵥ g) - ((n0 - n : ℕ) : ℝ)|} := by
            ext g
            simp only [hE1, Set.mem_preimage, Set.mem_ofPred_eq, a, hS, not_true_eq_false,
              false_or, Nat.cast_sub hn.le]
          rw [hset]
          refine h.trans ((hK _ (by positivity) ?_))
          exact_mod_cast Nat.sub_le n0 n
      _ = ENNReal.ofReal (15360 / (η ^ 4 * (n0 : ℝ) ^ 2)) := by
          rw [lintegral_const, measure_univ, mul_one]
  -- second tail: `‖g‖²`
  have hE2b : (μS.prod μg) E2 ≤ ENNReal.ofReal (15360 / (η ^ 4 * (n0 : ℝ) ^ 2)) := by
    have hset : E2 = Set.univ ×ˢ {g : Fin n0 → ℝ | t ≤ |g ⬝ᵥ g - n0|} := by
      ext x; simp [hE2, b]
    have h := measure_projector_dotProduct_deviation_le (1 : Matrix (Fin n0) (Fin n0) ℝ)
      IsStarProjection.one n0 (by simp) (by omega) ht
    simp only [Matrix.one_mulVec] at h
    rw [hset, Measure.prod_prod, measure_univ, one_mul]
    exact h.trans (hK _ (by positivity) le_rfl)
  calc μS {W | η ≤ |((1 - gramProjector (Matrix.of W)) *ᵥ u) ⬝ᵥ
          ((1 - gramProjector (Matrix.of W)) *ᵥ u) - (1 - (n : ℝ) / n0)|}
      = (μS.prod μg) E := hν
    _ ≤ (μS.prod μg) (E1 ∪ E2) := measure_mono hsub
    _ ≤ (μS.prod μg) E1 + (μS.prod μg) E2 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (15360 / (η ^ 4 * (n0 : ℝ) ^ 2)) +
        ENNReal.ofReal (15360 / (η ^ 4 * (n0 : ℝ) ^ 2)) := add_le_add hE1b hE2b
    _ = ENNReal.ofReal (30720 / (η ^ 4 * (n0 : ℝ) ^ 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
end LinearRegression.DoubleDescent

end
