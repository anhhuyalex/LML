/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.OrthogonalDiagonalization
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.RandomMatrixFoundations

/-!
# The trace of the inverse Gram matrix of a Gaussian matrix

Milestone 7d of the double-descent plan ([Bach, 2024]; [Hastie et al., 2022]; [Belkin et al.,
2019]). For `W` a `p × m` matrix with i.i.d. standard normal entries, written
`Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1`, the diagonal entries
of `(Wᵀ W)⁻¹` are exact inverse chi-squared variables (`map_inv_gram_diag_gaussianMatrix`), so:

* `integral_trace_inv_gram_gaussianMatrix`: `E Tr ((Wᵀ W)⁻¹) = m / (p - m - 1)` for `m + 1 < p`
  (Lemma 3.2, Part 1: the inverse-Wishart mean, via `E [1/χ²_ν] = 1/(ν-2)`);
* `measureReal_inv_gram_diag_deviation_le`, `measure_trace_inv_gram_deviation_le`: a
  non-asymptotic tail bound `ℙ (Tr ∉ [m / (ν (1+ε)), m / (ν (1-ε))]) ≤ 60 m / (ε⁴ ν²)`,
  `ν = p - m + 1`, from the fourth-moment Markov bound of `StdGaussianChiSqTails.lean` and a
  union bound over the `m` diagonal entries (no covariance estimate between entries is needed);
  it is the unit-weight case of `measureReal_weighted_diag_inv_gram_deviation_le`;
* `measure_trace_mul_inv_gram_deviation_le`: the same sandwich for `Tr (C (Wᵀ W)⁻¹)` with an
  arbitrary PSD weight `C` (sandwich `Tr C / (ν (1 ± ε))`), by diagonalizing `C` and rotating `W`
  (`Matrix.exists_trace_mul_eq_sum_eigenvalues`, `map_gaussianMatrix_mul_orthonormal`);
* `tendsto_measure_trace_inv_gram_deviation`: **convergence in probability**
  `Tr ((Wᵀ W)⁻¹) → ρ / (1 - ρ)` along `m_k / p_k → ρ < 1` (Lemma 3.2, Part 2), stated for a sequence
  of product measures (no infinite probability space).
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK

private theorem measurable_inv_gram_entry {p q : ℕ} (j k : Fin q) :
    Measurable fun W : Fin p → Fin q → ℝ => ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j k := by
  have hW : Measurable fun W : Fin p → Fin q → ℝ => (Matrix.of W : Matrix (Fin p) (Fin q) ℝ) :=
    Measurable.of_eval_matrix _ fun i k => (measurable_pi_apply k).comp (measurable_pi_apply i)
  exact measurable_matrix_entry (measurable_matrix_nonsing_inv.comp
    (measurable_matrix_mul (measurable_matrix_transpose hW) hW)) j k

/-- **Mean of a diagonal entry of the inverse Gram matrix.** For a `p × (q+1)` Gaussian matrix
with `q + 2 < p`, `E ((Wᵀ W)⁻¹)ⱼⱼ = 1 / (p - q - 2)`, since `((Wᵀ W)⁻¹)ⱼⱼ ~ 1 / χ²_(p-q)` and
`E [1/χ²_ν] = 1/(ν-2)` (`integral_inv_norm_sq_stdGaussian`). -/
theorem integral_inv_gram_diag_gaussianMatrix {p q : ℕ} (hqp : q + 2 < p) (j : Fin (q + 1)) :
    ∫ W, ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j
        ∂(Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1) =
      1 / (((p - q : ℕ) : ℝ) - 2) := by
  have hmeas := measurable_inv_gram_entry (p := p) j j
  have hlaw := map_inv_gram_diag_gaussianMatrix (by omega : q + 1 ≤ p) j
  have hpos : Nontrivial (EuclideanSpace ℝ (Fin (p - q))) := by
    have : NeZero (p - q) := ⟨by omega⟩
    infer_instance
  have h1 : ∫ W, ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j ∂(Measure.pi fun _ : Fin p =>
      Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1) =
      ∫ y, y ∂((Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) =>
        gaussianReal 0 1).map (fun W => ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)) :=
    (integral_map hmeas.aemeasurable aestronglyMeasurable_id).symm
  have h2 : ∫ y, y ∂((stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map
      (fun x => (‖x‖ ^ 2)⁻¹)) = ∫ x, (‖x‖ ^ 2)⁻¹ ∂(stdGaussian (EuclideanSpace ℝ (Fin (p - q)))) :=
    integral_map (by fun_prop) aestronglyMeasurable_id
  rw [h1, hlaw, h2]
  have := integral_inv_norm_sq_stdGaussian (E := EuclideanSpace ℝ (Fin (p - q))) (by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    have : ((p - q : ℕ) : ℝ) = p - q := by rw [Nat.cast_sub (by omega)]
    have h2 : (q + 2 : ℝ) < p := by exact_mod_cast hqp
    linarith)
  simpa [finrank_euclideanSpace] using this


private theorem integrable_inv_gram_diag_gaussianMatrix {p q : ℕ} (hqp : q + 2 < p)
    (j : Fin (q + 1)) :
    Integrable (fun W : Fin p → Fin (q + 1) → ℝ => ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1) := by
  have hmeas := measurable_inv_gram_entry (p := p) j j
  have hlaw := map_inv_gram_diag_gaussianMatrix (by omega : q + 1 ≤ p) j
  have : NeZero (p - q) := ⟨by omega⟩
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin (p - q)) => (‖x‖ ^ 2)⁻¹)
      (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))) := by
    simpa using integrable_inv_norm_sq_pow_stdGaussian (E := EuclideanSpace ℝ (Fin (p - q)))
      (j := 1) (by
        simp only [finrank_euclideanSpace, Fintype.card_fin]
        have : ((p - q : ℕ) : ℝ) = p - q := by rw [Nat.cast_sub (by omega)]
        have h2 : (q + 2 : ℝ) < p := by exact_mod_cast hqp
        push_cast
        linarith)
  have hid : ∀ ν : Measure ℝ, AEStronglyMeasurable (fun y : ℝ => y) ν := fun ν =>
    measurable_id'.aestronglyMeasurable
  have h1 : Integrable (fun y : ℝ => y) ((Measure.pi fun _ : Fin p =>
      Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).map
        (fun W : Fin p → Fin (q + 1) → ℝ => ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)) := by
    rw [hlaw]
    exact (integrable_map_measure (hid _) (by fun_prop)).mpr hint
  exact (integrable_map_measure (hid _) hmeas.aemeasurable).mp h1

/-- **Mean of the trace of the inverse Gram matrix** (the exact inverse-Wishart mean). For a
`p × q` Gaussian matrix with `q + 1 < p`, `E Tr ((Wᵀ W)⁻¹) = q / (p - q - 1)`. -/
theorem integral_trace_inv_gram_gaussianMatrix {p q : ℕ} (hqp : q + 1 < p) :
    ∫ W, ((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace
        ∂(Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1) =
      (q : ℝ) / ((p : ℝ) - q - 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have hsum : ∀ W : Fin p → Fin (q' + 1) → ℝ,
      ((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace = ∑ j, ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j :=
    fun W => rfl
  simp_rw [hsum]
  rw [integral_finsetSum _ fun j _ => integrable_inv_gram_diag_gaussianMatrix hqp j]
  simp_rw [integral_inv_gram_diag_gaussianMatrix hqp]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ((p - q' : ℕ) : ℝ) = p - q' := by rw [Nat.cast_sub (by omega)]
  have h2 : ((p : ℝ) - ((q' + 1 : ℕ) : ℝ) - 1) = ((p - q' : ℕ) : ℝ) - 2 := by
    rw [h1]; push_cast; ring
  rw [h2]
  push_cast
  ring


/-- **Tail bound for one diagonal entry.** For a `p × (q+1)` Gaussian matrix with `q + 1 ≤ p`,
`ν = p - q` and `ε > 0`, the probability that `1 / ((Wᵀ W)⁻¹)ⱼⱼ` deviates from `ν` by at least
`ε ν` is at most `60 / (ε⁴ ν²)` (`measureReal_norm_sq_sub_ge_le`). -/
theorem measureReal_inv_gram_diag_deviation_le {p q : ℕ} (hqp : q + 1 ≤ p) (j : Fin (q + 1))
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).real
        {W | ε * ((p - q : ℕ) : ℝ) ≤
          |(((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)⁻¹ - ((p - q : ℕ) : ℝ)|} ≤
      60 / (ε ^ 4 * ((p - q : ℕ) : ℝ) ^ 2) := by
  have hmeas := measurable_inv_gram_entry (p := p) j j
  have hlaw := map_inv_gram_diag_gaussianMatrix hqp j
  have hlaw' : (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) =>
      gaussianReal 0 1).map (fun W => (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)⁻¹) =
      (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map (fun x => ‖x‖ ^ 2) := by
    have e : (fun W : Fin p → Fin (q + 1) → ℝ => (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)⁻¹) =
        (fun y : ℝ => y⁻¹) ∘ (fun W => ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j) := rfl
    rw [e, ← Measure.map_map (by fun_prop) hmeas, hlaw, Measure.map_map (by fun_prop)
      (by fun_prop)]
    congr 1
    funext x
    simp
  have h := measure_dev_le_of_map_norm_sq (f := fun W : Fin p → Fin (q + 1) → ℝ =>
    (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)⁻¹) hmeas.inv (k := p - q) (by omega) hlaw' hε
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h


/-- **Non-asymptotic concentration of a nonnegatively weighted sum of the diagonal of `(Wᵀ W)⁻¹`.**
For a `p × (q+1)` Gaussian matrix with `q + 1 ≤ p`, `ν = p - q`, weights `wⱼ ≥ 0` and `0 < ε < 1`,
`ℙ (∑ⱼ wⱼ ((Wᵀ W)⁻¹)ⱼⱼ ∉ [∑ w / (ν (1+ε)), ∑ w / (ν (1-ε))]) ≤ 60 (q+1) / (ε⁴ ν²)`.

Proof: every `1 / ((Wᵀ W)⁻¹)ⱼⱼ` is a `χ²_ν` variable (`map_inv_gram_diag_gaussianMatrix`), it lies
in `ν (1 ± ε)` except with probability `60 / (ε⁴ ν²)`
(`measureReal_inv_gram_diag_deviation_le`), and a union bound over the `q+1` columns avoids any
covariance estimate. On the good event every term, hence the weighted sum, is sandwiched. -/
theorem measureReal_weighted_diag_inv_gram_deviation_le {p q : ℕ} (hqp : q + 1 ≤ p)
    (w : Fin (q + 1) → ℝ) (hw : ∀ j, 0 ≤ w j) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).real
        {W | ¬ ((∑ j, w j) / (((p - q : ℕ) : ℝ) * (1 + ε)) ≤
            ∑ j, w j * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j ∧
          ∑ j, w j * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j ≤
            (∑ j, w j) / (((p - q : ℕ) : ℝ) * (1 - ε)))} ≤
      ((q + 1 : ℕ) : ℝ) * (60 / (ε ^ 4 * ((p - q : ℕ) : ℝ) ^ 2)) := by
  set μ := Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1 with hμ
  set ν : ℝ := ((p - q : ℕ) : ℝ) with hνdef
  have hν : 0 < ν := by
    have : 0 < p - q := by omega
    rw [hνdef]; exact_mod_cast this
  set E : Fin (q + 1) → Set (Fin p → Fin (q + 1) → ℝ) := fun j =>
    {W | ε * ν ≤ |(((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j)⁻¹ - ν|} with hE
  have hsub : {W : Fin p → Fin (q + 1) → ℝ | ¬ ((∑ j, w j) / (ν * (1 + ε)) ≤
        ∑ j, w j * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j ∧
      ∑ j, w j * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j ≤ (∑ j, w j) / (ν * (1 - ε)))} ⊆
      ⋃ j, E j := by
    intro W hW
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists, hE, Set.mem_ofPred_eq, not_le] at hnot hW
    apply hW
    set M := (Matrix.of W)ᵀ * Matrix.of W with hM
    have hX : ∀ j, ν * (1 - ε) < (M⁻¹ j j)⁻¹ ∧ (M⁻¹ j j)⁻¹ < ν * (1 + ε) := fun j => by
      have := abs_lt.mp (hnot j)
      constructor <;> nlinarith [this.1, this.2]
    have hpos : ∀ j, 0 < (M⁻¹ j j)⁻¹ := fun j =>
      lt_trans (mul_pos hν (by linarith)) (hX j).1
    have hD : ∀ j, M⁻¹ j j = ((M⁻¹ j j)⁻¹)⁻¹ := fun j => (inv_inv _).symm
    constructor
    · calc (∑ j, w j) / (ν * (1 + ε)) = ∑ j, w j * (1 / (ν * (1 + ε))) := by
            rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ ∑ j, w j * M⁻¹ j j := Finset.sum_le_sum fun j _ => by
            refine mul_le_mul_of_nonneg_left ?_ (hw j)
            rw [hD j, one_div]
            exact inv_anti₀ (hpos j) (hX j).2.le
    · calc ∑ j, w j * M⁻¹ j j ≤ ∑ j, w j * (1 / (ν * (1 - ε))) :=
            Finset.sum_le_sum fun j _ => by
              refine mul_le_mul_of_nonneg_left ?_ (hw j)
              rw [hD j, one_div]
              exact inv_anti₀ (mul_pos hν (by linarith)) (hX j).1.le
        _ = (∑ j, w j) / (ν * (1 - ε)) := by
            rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  calc μ.real {W | _} ≤ μ.real (⋃ j, E j) := measureReal_mono hsub
    _ ≤ ∑ j, μ.real (E j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin (q + 1), 60 / (ε ^ 4 * ν ^ 2) :=
        Finset.sum_le_sum fun j _ => measureReal_inv_gram_diag_deviation_le hqp j hε
    _ = _ := by simp


/-- **Non-asymptotic concentration of `Tr ((Wᵀ W)⁻¹)`.** For a `p × (q+1)` Gaussian matrix with
`q + 1 ≤ p`, `ν = p - q` and `0 < ε < 1`,
`ℙ (Tr ((Wᵀ W)⁻¹) ∉ [(q+1) / (ν (1+ε)), (q+1) / (ν (1-ε))]) ≤ 60 (q+1) / (ε⁴ ν²)`: the case of
unit weights of `measureReal_weighted_diag_inv_gram_deviation_le`. -/
theorem measureReal_trace_inv_gram_deviation_le {p q : ℕ} (hqp : q + 1 ≤ p) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).real
        {W | ¬ (((q + 1 : ℕ) : ℝ) / (((p - q : ℕ) : ℝ) * (1 + ε)) ≤
            ((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace ∧
          ((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace ≤
            ((q + 1 : ℕ) : ℝ) / (((p - q : ℕ) : ℝ) * (1 - ε)))} ≤
      ((q + 1 : ℕ) : ℝ) * (60 / (ε ^ 4 * ((p - q : ℕ) : ℝ) ^ 2)) := by
  simpa [Matrix.trace] using
    measureReal_weighted_diag_inv_gram_deviation_le hqp (fun _ => 1) (fun _ => zero_le_one) hε hε1


/-- **Concentration of `Tr (C (Wᵀ W)⁻¹)` for a PSD weight `C`.** For a `p × (q+1)` Gaussian matrix
with `q + 1 ≤ p`, `ν = p - q` and `0 < ε < 1`, the trace `Tr (C (Wᵀ W)⁻¹)` lies in
`[Tr C / (ν (1+ε)), Tr C / (ν (1-ε))]` except with probability at most `60 (q+1) / (ε⁴ ν²)`,
whatever the PSD matrix `C`. Diagonalize `C = U diag(w) Uᵀ`; orthogonal invariance
(`map_gaussianMatrix_mul_orthonormal`) turns `Uᵀ (Wᵀ W)⁻¹ U` into the inverse Gram matrix of
another Gaussian matrix, and the weighted diagonal bound applies. -/
theorem measure_trace_mul_inv_gram_deviation_le {p q : ℕ} (hqp : q + 1 ≤ p)
    (C : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (hC : C.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)
        {W | ¬ (C.trace / (((p - q : ℕ) : ℝ) * (1 + ε)) ≤
            (C * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹).trace ∧
          (C * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹).trace ≤
            C.trace / (((p - q : ℕ) : ℝ) * (1 - ε)))} ≤
      ENNReal.ofReal (((q + 1 : ℕ) : ℝ) * (60 / (ε ^ 4 * ((p - q : ℕ) : ℝ) ^ 2))) := by
  obtain ⟨U, w, hU, hw, hwsum, htr⟩ := exists_trace_mul_eq_sum_eigenvalues C hC
  set μ := Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1
    with hμ
  set f : (Fin p → Fin (q + 1) → ℝ) → (Fin p → Fin (q + 1) → ℝ) := fun W i k =>
    (Matrix.of W * U) i k with hf
  have hfm : Measurable f := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [hf, Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _
  have hmap : μ.map f = μ := map_gaussianMatrix_mul_orthonormal (ρ := Fin p) U hU
  set E : Set (Fin p → Fin (q + 1) → ℝ) :=
    {W | ¬ ((∑ j, w j) / (((p - q : ℕ) : ℝ) * (1 + ε)) ≤
        ∑ j, w j * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j ∧
      ∑ j, w j * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j ≤
        (∑ j, w j) / (((p - q : ℕ) : ℝ) * (1 - ε)))} with hE
  have hsub : {W : Fin p → Fin (q + 1) → ℝ | ¬ (C.trace / (((p - q : ℕ) : ℝ) * (1 + ε)) ≤
            (C * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹).trace ∧
          (C * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹).trace ≤
            C.trace / (((p - q : ℕ) : ℝ) * (1 - ε)))} ⊆ f ⁻¹' E := by
    intro W hW
    have hfW : (Matrix.of (f W) : Matrix (Fin p) (Fin (q + 1)) ℝ) = Matrix.of W * U := rfl
    have hinv : ((Matrix.of (f W))ᵀ * Matrix.of (f W))⁻¹ =
        Uᵀ * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ * U := by
      have h1 : (Matrix.of W * U)ᵀ * (Matrix.of W * U) =
          Uᵀ * ((Matrix.of W)ᵀ * Matrix.of W) * U := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      rw [hfW, h1]
      exact inv_transpose_mul_mul_orthogonal _ U hU
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq] at hW ⊢
    rw [hinv, hwsum, ← htr]
    exact hW
  have hreal := measureReal_weighted_diag_inv_gram_deviation_le hqp w hw hε hε1
  calc μ _ ≤ μ (f ⁻¹' E) := measure_mono hsub
    _ ≤ (μ.map f) E := Measure.le_map_apply hfm.aemeasurable E
    _ = μ E := by rw [hmap]
    _ ≤ _ := by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal hreal


/-- `measureReal_trace_inv_gram_deviation_le` for `m ≥ 1` columns, with `ν = p - m + 1`. -/
theorem measure_trace_inv_gram_deviation_le {p m : ℕ} (hm : 0 < m) (hmp : m ≤ p) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1)
        {W | ¬ ((m : ℝ) / (((p - m + 1 : ℕ) : ℝ) * (1 + ε)) ≤
            ((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace ∧
          ((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace ≤ (m : ℝ) / (((p - m + 1 : ℕ) : ℝ) * (1 - ε)))} ≤
      ENNReal.ofReal ((m : ℝ) * (60 / (ε ^ 4 * ((p - m + 1 : ℕ) : ℝ) ^ 2))) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h := measureReal_trace_inv_gram_deviation_le (p := p) (q := q) hmp hε hε1
  have e : p - (q + 1) + 1 = p - q := by omega
  rw [e]
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h


private theorem abs_sub_lt_of_trace_bounds {c ck t ε δ : ℝ} (hc : 0 ≤ c) (hck : 0 ≤ ck)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hδε : δ * (c + ε + 1) ≤ ε / 8)
    (hck' : |ck - c| < ε / 4) (ht1 : ck / (1 + δ) ≤ t) (ht2 : t ≤ ck / (1 - δ)) :
    |t - c| < ε := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hck'
  have h1δ : 0 < 1 - δ := by linarith
  have e1 : ck / (1 - δ) ≤ ck * (1 + 2 * δ) := by
    rw [div_le_iff₀ h1δ]
    nlinarith [mul_nonneg hck hδ0.le, mul_nonneg hck (sub_nonneg.2 hδ)]
  have e2 : ck * (1 - δ) ≤ ck / (1 + δ) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hck (sq_nonneg δ)]
  rw [abs_lt]
  constructor
  · nlinarith [mul_nonneg hck hδ0.le]
  · nlinarith [mul_nonneg hck hδ0.le]


open Filter Topology in
/-- **Convergence in probability of `Tr ((Wᵀ W)⁻¹)`** (Lemma 3.2, Part 2 of the notes). Let `W_k`
be `p_k × m_k` Gaussian matrices with `1 ≤ m_k ≤ p_k`, `p_k → ∞` and `m_k / p_k → ρ < 1`. Then for
every `ε > 0`, `ℙ (|Tr ((W_kᵀ W_k)⁻¹) - ρ / (1 - ρ)| ≥ ε) → 0`.

Proof: with `ν_k = p_k - m_k + 1`, `Tr ≈ m_k / ν_k → ρ / (1 - ρ)` on the event of
`measure_trace_inv_gram_deviation_le`, whose complement has probability at most
`60 m_k / (δ⁴ ν_k²) → 0` for a fixed small `δ`. -/
theorem tendsto_measure_trace_inv_gram_deviation {pp mm : ℕ → ℕ} {ρ : ℝ} (hρ1 : ρ < 1)
    (hm : ∀ k, 0 < mm k) (hmp : ∀ k, mm k ≤ pp k) (hp : Tendsto pp atTop atTop)
    (hr : Tendsto (fun k => (mm k : ℝ) / (pp k : ℝ)) atTop (𝓝 ρ)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (Measure.pi fun _ : Fin (pp k) => Measure.pi fun _ : Fin (mm k) =>
        gaussianReal 0 1) {W | ε ≤ |((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace - ρ / (1 - ρ)|})
      atTop (𝓝 0) := by
  have hρ0 : 0 ≤ ρ := ge_of_tendsto' hr fun k => by positivity
  have hpp : ∀ k, (0 : ℝ) < pp k := fun k => by
    have := hm k; have := hmp k; exact_mod_cast (by omega : 0 < pp k)
  set c : ℝ := ρ / (1 - ρ) with hcdef
  have hc0 : 0 ≤ c := div_nonneg hρ0 (by linarith)
  -- ν_k and c_k
  set ν : ℕ → ℝ := fun k => ((pp k - mm k + 1 : ℕ) : ℝ) with hν
  have hνk : ∀ k, ν k = pp k - mm k + 1 := fun k => by
    simp only [hν]; rw [Nat.cast_add, Nat.cast_sub (hmp k)]; simp
  have hνpos : ∀ k, 0 < ν k := fun k => by
    have h1 : (mm k : ℝ) ≤ pp k := by exact_mod_cast hmp k
    rw [hνk]; linarith
  have hinv : Tendsto (fun k => ((pp k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hp)
  have hratio : Tendsto (fun k => ν k / pp k) atTop (𝓝 (1 - ρ)) := by
    have : (fun k => ν k / pp k) = fun k => 1 - (mm k : ℝ) / pp k + ((pp k : ℝ))⁻¹ := by
      funext k; rw [hνk]; field_simp [(hpp k).ne']
    rw [this]
    simpa using (tendsto_const_nhds.sub hr).add hinv
  have hpos1 : 0 < 1 - ρ := by linarith
  have hck : Tendsto (fun k => (mm k : ℝ) / ν k) atTop (𝓝 c) := by
    have : (fun k => (mm k : ℝ) / ν k) = fun k => ((mm k : ℝ) / pp k) / (ν k / pp k) := by
      funext k; field_simp [(hpp k).ne', (hνpos k).ne']
    rw [this]
    exact hr.div hratio hpos1.ne'
  have hνtop : Tendsto ν atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop.comp hp).atTop_mul_pos hpos1 hratio
    refine h.congr fun k => ?_
    simp only [Function.comp]
    field_simp [(hpp k).ne']
  -- choose δ
  set δ : ℝ := min (1 / 2) (ε / (8 * (c + ε + 1))) with hδdef
  have hden : 0 < 8 * (c + ε + 1) := by positivity
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ * (c + ε + 1) ≤ ε / 8 := by
    have h1 : δ ≤ ε / (8 * (c + ε + 1)) := min_le_right _ _
    calc δ * (c + ε + 1) ≤ ε / (8 * (c + ε + 1)) * (c + ε + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ε / 8 := by field_simp
  have hδ1 : δ < 1 := by linarith
  -- bound sequence
  have hbound : Tendsto (fun k => (mm k : ℝ) * (60 / (δ ^ 4 * ν k ^ 2))) atTop (𝓝 0) := by
    have h := tendsto_const_nhds (x := 60 / δ ^ 4) |>.mul
      (hck.mul (tendsto_inv_atTop_zero.comp hνtop))
    have e : (fun k => (mm k : ℝ) * (60 / (δ ^ 4 * ν k ^ 2))) =
        fun k => 60 / δ ^ 4 * ((mm k : ℝ) / ν k * (ν k)⁻¹) := by
      funext k; field_simp [(hνpos k).ne', hδ0.ne']
    rw [e]
    simpa using h
  have hev : ∀ᶠ k in atTop, |(mm k : ℝ) / ν k - c| < ε / 4 :=
    (hck.sub_const c).abs.eventually (gt_mem_nhds (by simpa using (by positivity : 0 < ε / 4)))
  have hbound' : Tendsto (fun k => ENNReal.ofReal ((mm k : ℝ) * (60 / (δ ^ 4 * ν k ^ 2))))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hbound
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound'
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev] with k hk
  refine le_trans (measure_mono ?_) (measure_trace_inv_gram_deviation_le (hm k) (hmp k) hδ0 hδ1)
  intro W hW
  by_contra hgood
  simp only [Set.mem_ofPred_eq, not_not] at hgood
  have hν' : ((pp k - mm k + 1 : ℕ) : ℝ) = ν k := rfl
  have e1 : (mm k : ℝ) / (ν k * (1 + δ)) = ((mm k : ℝ) / ν k) / (1 + δ) := by
    rw [div_div]
  have e2 : (mm k : ℝ) / (ν k * (1 - δ)) = ((mm k : ℝ) / ν k) / (1 - δ) := by
    rw [div_div]
  rw [hν', e1, e2] at hgood
  have hlt := abs_sub_lt_of_trace_bounds hc0 (by have := hνpos k; positivity) hε hδ0 hδ hδε hk
    hgood.1 hgood.2
  exact (not_le.mpr hlt) hW

end LinearRegression.DoubleDescent

end
