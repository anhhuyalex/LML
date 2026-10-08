/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.Householder
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.BiasProjector
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.InverseGramTrace

/-!
# Concentration of the fit error of a Gaussian regression

The quantity `‖(Gᵀ G)⁻¹ Gᵀ ζ‖²` is the fit error of least squares on `n` Gaussian columns `G` when
the response `ζ` is an *independent* Gaussian vector; in random-feature regression it is the cost of
fitting the signal `X θ⊥` omitted by the random features (Milestone 7e/7f of the plan;
[Hastie et al., 2022]; [Belkin et al., 2019]). It concentrates at `n / (m - n + 1)` without any
second moment of the inverse Wishart matrix and without `Tr ((Gᵀ G)⁻²)`:

* `map_quadForm_inv_gram`: for a fixed unit vector `u`, `uᵀ (Wᵀ W)⁻¹ u ~ 1 / χ²_(p-q)`: the
  diagonal law of `RandomMatrixFoundations.lean` rotated by a Householder reflection
  (`Matrix.exists_orthogonal_mulVec_eq`) and `map_gaussianMatrix_mul_orthonormal`;
* `map_dotProduct_div_quadForm_inv_gram`: for an independent Gaussian `z`, `‖z‖² / zᵀ (Wᵀ W)⁻¹ z`
  is exactly `χ²_(p-q)` (`map_prod_eq_of_ae`: Fubini over the fixed direction `z / ‖z‖`);
* `measure_quadForm_inv_gram_deviation_le`: `zᵀ (Wᵀ W)⁻¹ z` is within the sandwich
  `n (1 ∓ η) / (ν (1 ± η))` except with probability `60 / (η⁴ ν²) + 60 / (η⁴ n²)`
  (two `χ²` tails, `measure_dev_le_of_map_norm_sq`);
* `measure_quadForm_inv_gram_fixed_mem_le`: for a *fixed* vector `ξ`, `ξᵀ (Wᵀ W)⁻¹ ξ` lies in
  `‖ξ‖² / (ν (1 ± η))` except with probability `60 / (η⁴ ν²)` (one `χ²` tail);
* `fitError_eq_quadForm`, `measure_fitError_deviation_le`: the same for `‖(Gᵀ G)⁻¹ Gᵀ ζ‖²` with
  `ζ ∈ ℝ^m`, through `G = Q R` and `z = Qᵀ ζ ~ 𝒩(0, I_n)`.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK
open scoped Matrix

/-- **Quadratic form of the inverse Gram matrix in a fixed direction.** For a unit vector `u`,
`uᵀ (Wᵀ W)⁻¹ u` has the law of `((Wᵀ W)⁻¹)₀₀`, namely `1 / χ²_(p-q)`: the matrix `W` may be
rotated so that `u` becomes the first coordinate vector (Householder, then
`map_gaussianMatrix_mul_orthonormal`). -/
theorem map_quadForm_inv_gram {p q : ℕ} (hqp : q + 1 ≤ p) (u : Fin (q + 1) → ℝ)
    (hu : u ⬝ᵥ u = 1) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).map
        (fun W => u ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ u)) =
      (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map (fun x => (‖x‖ ^ 2)⁻¹) := by
  have he : (Pi.single 0 1 : Fin (q + 1) → ℝ) ⬝ᵥ Pi.single 0 1 = u ⬝ᵥ u := by
    rw [hu]; simp
  obtain ⟨U, hU1, hU2, hUe⟩ := Matrix.exists_orthogonal_mulVec_eq _ _ he
  have hmp := map_gaussianMatrix_mul_orthonormal (ρ := Fin p) U hU2
  rw [← map_inv_gram_diag_gaussianMatrix hqp 0]
  have hmeas : Measurable fun W : Fin p → Fin (q + 1) → ℝ =>
      ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ 0 0 := by
    have hW : Measurable fun W : Fin p → Fin (q + 1) → ℝ =>
        (Matrix.of W : Matrix (Fin p) (Fin (q + 1)) ℝ) :=
      Measurable.of_eval_matrix _ fun i k => (measurable_pi_apply k).comp (measurable_pi_apply i)
    exact measurable_matrix_entry (measurable_matrix_nonsing_inv.comp
      (measurable_matrix_mul (measurable_matrix_transpose hW) hW)) 0 0
  have hrot : Measurable fun W : Fin p → Fin (q + 1) → ℝ => fun i k => (Matrix.of W * U) i k := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _
  conv_rhs => rw [← hmp, Measure.map_map hmeas hrot]
  congr 1
  funext W
  simp only [Function.comp]
  have hof : (Matrix.of fun i k => (Matrix.of W * U) i k) = Matrix.of W * U := rfl
  have hUi : U⁻¹ = Uᵀ := Matrix.inv_eq_right_inv hU1
  have hUti : (Uᵀ)⁻¹ = U := Matrix.inv_eq_right_inv hU2
  have key : ((Matrix.of W * U)ᵀ * (Matrix.of W * U))⁻¹ =
      Uᵀ * ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ * U := by
    have : (Matrix.of W * U)ᵀ * (Matrix.of W * U) =
        Uᵀ * ((Matrix.of W)ᵀ * Matrix.of W) * U := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUi, hUti, Matrix.mul_assoc]
  rw [hof, key]
  set M := ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ with hM
  have h1 : (Uᵀ * M * U) 0 0 =
      (Pi.single 0 1 : Fin (q + 1) → ℝ) ⬝ᵥ ((Uᵀ * M * U) *ᵥ Pi.single 0 1) := by simp
  rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUe, Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  have h2 : (Pi.single 0 1 : Fin (q + 1) → ℝ) ⬝ᵥ (Uᵀ *ᵥ (M *ᵥ u)) =
      (U *ᵥ Pi.single 0 1) ⬝ᵥ (M *ᵥ u) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [h2, hUe]

/-- A Gaussian vector in dimension `n ≥ 1` is almost surely nonzero. -/
theorem ae_dotProduct_self_ne_zero_pi_gaussianReal {n : ℕ} (hn : 0 < n) :
    ∀ᵐ g ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1), g ⬝ᵥ g ≠ 0 := by
  rw [ae_iff]
  have : {g : Fin n → ℝ | ¬ g ⬝ᵥ g ≠ 0} = Set.univ.pi fun _ => {0} := by
    ext g; simp [dotProduct_self_eq_zero, funext_iff]
  rw [this, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    ((gaussianReal_absolutelyContinuous 0 one_ne_zero) (by simp))

/-- **The Rayleigh quotient of the Gram matrix against a Gaussian vector is exactly `χ²`.**
For `W` a `p × (q+1)` Gaussian matrix and an independent Gaussian vector `z ∈ ℝ^(q+1)`,
`‖z‖² / (zᵀ (Wᵀ W)⁻¹ z)` has the law of `‖x‖²`, `x ~ stdGaussian (ℝ^(p-q))`, i.e. `χ²_(p-q)`.

For fixed `z ≠ 0` this is `map_quadForm_inv_gram` applied to the unit vector `z / ‖z‖`, and
`map_prod_eq_of_ae` assembles the product law, so no independence or polar decomposition of `z`
is needed. -/
theorem map_dotProduct_div_quadForm_inv_gram {p q : ℕ} (hqp : q + 1 ≤ p) :
    ((Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)).map
        (fun x => (x.2 ⬝ᵥ x.2) / (x.2 ⬝ᵥ (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ *ᵥ x.2))) =
      (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map (fun x => ‖x‖ ^ 2) := by
  have hW : Measurable fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) =>
      (Matrix.of x.1 : Matrix (Fin p) (Fin (q + 1)) ℝ) :=
    Measurable.of_eval_matrix _ fun i k =>
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_fst)
  have hH : Measurable fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) =>
      ((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ :=
    measurable_matrix_nonsing_inv.comp (measurable_matrix_mul (measurable_matrix_transpose hW) hW)
  have hF : Measurable fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) =>
      (x.2 ⬝ᵥ x.2) / (x.2 ⬝ᵥ (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ *ᵥ x.2)) :=
    (measurable_dotProduct measurable_snd measurable_snd).div
      (measurable_dotProduct measurable_snd (measurable_mulVec hH measurable_snd))
  refine map_prod_eq_of_ae _ _ _ hF _ ?_
  filter_upwards [ae_dotProduct_self_ne_zero_pi_gaussianReal (Nat.succ_pos q)] with z hz
  have hpos : 0 < z ⬝ᵥ z := lt_of_le_of_ne (by
    rw [← star_trivial z]; exact dotProduct_star_self_nonneg z) (Ne.symm hz)
  set s : ℝ := Real.sqrt (z ⬝ᵥ z) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos
  have hss : s * s = z ⬝ᵥ z := Real.mul_self_sqrt hpos.le
  have hu : (s⁻¹ • z) ⬝ᵥ (s⁻¹ • z) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  have hlaw := map_quadForm_inv_gram hqp _ hu
  have hmq : Measurable fun W : Fin p → Fin (q + 1) → ℝ =>
      (s⁻¹ • z) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • z)) := by
    have hW' : Measurable fun W : Fin p → Fin (q + 1) → ℝ =>
        (Matrix.of W : Matrix (Fin p) (Fin (q + 1)) ℝ) :=
      Measurable.of_eval_matrix _ fun i k => (measurable_pi_apply k).comp (measurable_pi_apply i)
    exact measurable_dotProduct measurable_const (measurable_mulVec
      (measurable_matrix_nonsing_inv.comp
        (measurable_matrix_mul (measurable_matrix_transpose hW') hW')) measurable_const)
  have e : (fun W : Fin p → Fin (q + 1) → ℝ => (z ⬝ᵥ z) /
      (z ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ z))) =
      (fun y : ℝ => y⁻¹) ∘ (fun W : Fin p → Fin (q + 1) → ℝ =>
        (s⁻¹ • z) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • z))) := by
    funext W
    simp only [Function.comp, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    rw [← hss]
    rw [mul_inv, inv_inv, mul_inv, inv_inv]
    ring
  simp only [e]
  rw [← Measure.map_map (by fun_prop) hmq, hlaw]
  have : NeZero (p - q) := ⟨by omega⟩
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp

/-- **Sandwich bound for the quadratic form of the inverse Gram matrix against a Gaussian
vector.** For `W` a `p × (q+1)` Gaussian matrix and `z` an independent standard Gaussian vector,
`ν = p - q`, `n = q + 1` and `0 < η < 1`, the quadratic form `zᵀ (Wᵀ W)⁻¹ z` lies in
`[n (1 - η) / (ν (1 + η)), n (1 + η) / (ν (1 - η))]` except on an event of probability at most
`60 / (η⁴ ν²) + 60 / (η⁴ n²)`.

Proof: `‖z‖² ~ χ²_n` and `‖z‖² / zᵀ (Wᵀ W)⁻¹ z ~ χ²_ν` (`map_dotProduct_div_quadForm_inv_gram`),
and each tail is bounded by `measure_dev_le_of_map_norm_sq`. -/
theorem measure_quadForm_inv_gram_deviation_le {p q : ℕ} (hqp : q + 1 ≤ p) {η : ℝ} (hη : 0 < η)
    (hη1 : η < 1) :
    ((Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1))
        {x | ¬ (((q + 1 : ℕ) : ℝ) * (1 - η) / (((p - q : ℕ) : ℝ) * (1 + η)) ≤
              x.2 ⬝ᵥ (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ *ᵥ x.2) ∧
            x.2 ⬝ᵥ (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ *ᵥ x.2) ≤
              ((q + 1 : ℕ) : ℝ) * (1 + η) / (((p - q : ℕ) : ℝ) * (1 - η)))} ≤
      ENNReal.ofReal (60 / (η ^ 4 * ((p - q : ℕ) : ℝ) ^ 2)) +
        ENNReal.ofReal (60 / (η ^ 4 * ((q + 1 : ℕ) : ℝ) ^ 2)) := by
  set μW := Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1
    with hμW
  set μz := Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1 with hμz
  set ν : ℝ := ((p - q : ℕ) : ℝ) with hν
  set n : ℝ := ((q + 1 : ℕ) : ℝ) with hn
  have hν0 : 0 < ν := by rw [hν]; exact_mod_cast (by omega : 0 < p - q)
  have hn0 : 0 < n := by rw [hn]; positivity
  set Q : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) → ℝ := fun x =>
    x.2 ⬝ᵥ (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ *ᵥ x.2) with hQ
  have hW : Measurable fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) =>
      (Matrix.of x.1 : Matrix (Fin p) (Fin (q + 1)) ℝ) :=
    Measurable.of_eval_matrix _ fun i k =>
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_fst)
  have hH : Measurable fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) =>
      ((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ :=
    measurable_matrix_nonsing_inv.comp (measurable_matrix_mul (measurable_matrix_transpose hW) hW)
  have hz2 : Measurable fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) => x.2 ⬝ᵥ x.2 :=
    measurable_dotProduct measurable_snd measurable_snd
  have hQm : Measurable Q :=
    measurable_dotProduct measurable_snd (measurable_mulVec hH measurable_snd)
  have hFm : Measurable fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) =>
      (x.2 ⬝ᵥ x.2) / Q x := hz2.div hQm
  have hE1 := measure_dev_le_of_map_norm_sq (μ := μW.prod μz) hFm (k := p - q) (by omega)
    (map_dotProduct_div_quadForm_inv_gram hqp) hη
  have hlawz : (μW.prod μz).map (fun x => x.2 ⬝ᵥ x.2) =
      (stdGaussian (EuclideanSpace ℝ (Fin (q + 1)))).map (fun x => ‖x‖ ^ 2) := by
    have h := map_dotProduct_projector_mulVec (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)
      (IsStarProjection.one _) (q + 1) (by simp)
    simp only [Matrix.one_mulVec] at h
    have e : (fun x : (Fin p → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ) => x.2 ⬝ᵥ x.2) =
        (fun g : Fin (q + 1) → ℝ => g ⬝ᵥ g) ∘ Prod.snd := rfl
    rw [e, ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul, h]
  have hE2 := measure_dev_le_of_map_norm_sq (μ := μW.prod μz) hz2 (k := q + 1) (by omega)
    hlawz hη
  refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans (add_le_add hE1 hE2))
  intro x hx
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
  obtain ⟨h1, h2⟩ := hnot
  apply hx
  have hF1 := abs_lt.1 h1
  have ha1 := abs_lt.1 h2
  set a := x.2 ⬝ᵥ x.2 with ha
  set F := a / Q x with hF
  have hapos : 0 < a := by nlinarith [ha1.1]
  have hFpos : 0 < F := by nlinarith [hF1.1]
  have hQ0 : Q x ≠ 0 := by
    intro h0; rw [hF, h0, div_zero] at hFpos; exact lt_irrefl _ hFpos
  have hQeq : Q x = a / F := by
    rw [hF, div_div_cancel₀ hapos.ne']
  have hlo : n * (1 - η) / (ν * (1 + η)) ≤ Q x := by
    rw [hQeq]
    exact div_le_div₀ hapos.le (by linarith [ha1.1]) hFpos (by linarith [hF1.2])
  have hhi : Q x ≤ n * (1 + η) / (ν * (1 - η)) := by
    rw [hQeq]
    exact div_le_div₀ (by positivity) (by linarith [ha1.2]) (by nlinarith [hF1.1])
      (by linarith [hF1.1])
  exact ⟨hlo, hhi⟩

/-- **Quadratic form of the inverse Gram matrix in a fixed direction, tail bound.** For a
`p × (q+1)` Gaussian matrix with `q + 1 ≤ p`, any fixed vector `ξ`, `ν = p - q` and `0 < η < 1`,
`ξᵀ (Wᵀ W)⁻¹ ξ ∈ [‖ξ‖² / (ν (1+η)), ‖ξ‖² / (ν (1-η))]` except with probability at most
`60 / (η⁴ ν²)`: for a unit direction `ξ / ‖ξ‖` the quadratic form is exactly `1 / χ²_ν`
(`map_quadForm_inv_gram`). -/
theorem measure_quadForm_inv_gram_fixed_mem_le {p q : ℕ} (hqp : q + 1 ≤ p)
    (ξ : Fin (q + 1) → ℝ) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)
        {W | ¬ ((ξ ⬝ᵥ ξ) / (((p - q : ℕ) : ℝ) * (1 + η)) ≤
            ξ ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ ξ) ∧
          ξ ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ ξ) ≤
            (ξ ⬝ᵥ ξ) / (((p - q : ℕ) : ℝ) * (1 - η)))} ≤
      ENNReal.ofReal (60 / (η ^ 4 * ((p - q : ℕ) : ℝ) ^ 2)) := by
  set ν : ℝ := ((p - q : ℕ) : ℝ) with hν
  have hν0 : 0 < ν := by rw [hν]; exact_mod_cast (by omega : 0 < p - q)
  by_cases hξ : ξ ⬝ᵥ ξ = 0
  · have h0 : ξ = 0 := dotProduct_self_eq_zero.1 hξ
    subst h0
    have : {W : Fin p → Fin (q + 1) → ℝ | ¬ (((0 : Fin (q + 1) → ℝ) ⬝ᵥ 0) / (ν * (1 + η)) ≤
        (0 : Fin (q + 1) → ℝ) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ 0) ∧
      (0 : Fin (q + 1) → ℝ) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ 0) ≤
        ((0 : Fin (q + 1) → ℝ) ⬝ᵥ 0) / (ν * (1 - η)))} = ∅ := by
      ext W; simp
    rw [this]; simp
  have hpos : 0 < ξ ⬝ᵥ ξ := lt_of_le_of_ne (by
    rw [← star_trivial ξ]; exact dotProduct_star_self_nonneg ξ) (Ne.symm hξ)
  set s : ℝ := Real.sqrt (ξ ⬝ᵥ ξ) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos
  have hss : s * s = ξ ⬝ᵥ ξ := Real.mul_self_sqrt hpos.le
  have hu : (s⁻¹ • ξ) ⬝ᵥ (s⁻¹ • ξ) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  have hlaw := map_quadForm_inv_gram hqp _ hu
  have hW' : Measurable fun W : Fin p → Fin (q + 1) → ℝ =>
      (Matrix.of W : Matrix (Fin p) (Fin (q + 1)) ℝ) :=
    Measurable.of_eval_matrix _ fun i k => (measurable_pi_apply k).comp (measurable_pi_apply i)
  have hmq : Measurable fun W : Fin p → Fin (q + 1) → ℝ =>
      (s⁻¹ • ξ) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • ξ)) :=
    measurable_dotProduct measurable_const (measurable_mulVec
      (measurable_matrix_nonsing_inv.comp
        (measurable_matrix_mul (measurable_matrix_transpose hW') hW')) measurable_const)
  have hlaw' : (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).map
      (fun W => ((s⁻¹ • ξ) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • ξ)))⁻¹) =
      (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map (fun x => ‖x‖ ^ 2) := by
    have e : (fun W : Fin p → Fin (q + 1) → ℝ =>
        ((s⁻¹ • ξ) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • ξ)))⁻¹) =
        (fun y : ℝ => y⁻¹) ∘ (fun W => (s⁻¹ • ξ) ⬝ᵥ
          (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • ξ))) := rfl
    rw [e, ← Measure.map_map (by fun_prop) hmq, hlaw, Measure.map_map (by fun_prop)
      (by fun_prop)]
    congr 1
    funext x
    simp
  have hdev := measure_dev_le_of_map_norm_sq (f := fun W : Fin p → Fin (q + 1) → ℝ =>
    ((s⁻¹ • ξ) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • ξ)))⁻¹) hmq.inv (k := p - q)
    (by omega) hlaw' hη
  refine le_trans (measure_mono ?_) hdev
  intro W hW
  by_contra hnot
  simp only [Set.mem_ofPred_eq, not_le] at hnot hW
  apply hW
  set a : ℝ := (s⁻¹ • ξ) ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ (s⁻¹ • ξ)) with ha
  have hfq : ξ ⬝ᵥ (((Matrix.of W)ᵀ * Matrix.of W)⁻¹ *ᵥ ξ) = (ξ ⬝ᵥ ξ) * a := by
    rw [ha, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← hss]
    field_simp
  obtain ⟨h1, h2⟩ := abs_lt.1 hnot
  have hfa : 0 < a⁻¹ := by nlinarith [mul_pos hν0 hη]
  have hapos : 0 < a := inv_pos.1 hfa
  rw [hfq]
  have hlo : ν * (1 - η) < a⁻¹ := by nlinarith
  have hhi : a⁻¹ < ν * (1 + η) := by nlinarith
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have : a * (ν * (1 + η)) ≥ 1 := by
      have := mul_lt_mul_of_pos_left hhi hapos
      rw [mul_inv_cancel₀ hapos.ne'] at this
      linarith
    nlinarith [hpos]
  · rw [le_div_iff₀ (by nlinarith)]
    have : a * (ν * (1 - η)) ≤ 1 := by
      have := mul_lt_mul_of_pos_left hlo hapos
      rw [mul_inv_cancel₀ hapos.ne'] at this
      linarith
    nlinarith [hpos]

/-- **The least-squares fit of a Gaussian vector is a quadratic form in the Gram inverse.** If
`G = Q R` with `Qᵀ Q = 1` and `R` symmetric invertible, then for every `ζ`,
`‖(Gᵀ G)⁻¹ Gᵀ ζ‖² = z ᵀ (Gᵀ G)⁻¹ z` with `z = Qᵀ ζ`. -/
theorem fitError_eq_quadForm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (G Q : Matrix m n ℝ) (R : Matrix n n ℝ) (hQ : Qᵀ * Q = 1) (hR : IsUnit R.det) (hRT : Rᵀ = R)
    (hG : G = Q * R) (ζ : m → ℝ) :
    ((((Gᵀ * G)⁻¹ * Gᵀ) *ᵥ ζ) ⬝ᵥ (((Gᵀ * G)⁻¹ * Gᵀ) *ᵥ ζ)) =
      (Qᵀ *ᵥ ζ) ⬝ᵥ ((Gᵀ * G)⁻¹ *ᵥ (Qᵀ *ᵥ ζ)) := by
  have hGG : Gᵀ * G = R * R := by
    rw [hG, Matrix.transpose_mul, hRT, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ,
      Matrix.one_mul]
  have hinv : (Gᵀ * G)⁻¹ = R⁻¹ * R⁻¹ := by rw [hGG, Matrix.mul_inv_rev]
  have hRi : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ hR
  have hRiT : (R⁻¹)ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRT]
  have h1 : ((Gᵀ * G)⁻¹ * Gᵀ) = R⁻¹ * Qᵀ := by
    rw [hinv, hG, Matrix.transpose_mul, hRT]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R⁻¹ R, hRi, Matrix.one_mul]
  rw [h1, hinv, ← Matrix.mulVec_mulVec]
  set z := Qᵀ *ᵥ ζ
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hRiT, ← Matrix.mulVec_mulVec]

/-- Measurability of the sandwich events for the fit error `‖(Gᵀ G)⁻¹ Gᵀ ζ‖²`. -/
theorem measurableSet_not_le_le_fitError {m n : ℕ} (c₁ c₂ : ℝ) :
    MeasurableSet {x : (Fin m → Fin n → ℝ) × (Fin m → ℝ) |
      ¬ (c₁ ≤ ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ∧
        ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ≤ c₂)} := by
  have hW : Measurable fun x : (Fin m → Fin n → ℝ) × (Fin m → ℝ) =>
      (Matrix.of x.1 : Matrix (Fin m) (Fin n) ℝ) :=
    Measurable.of_eval_matrix _ fun i k =>
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_fst)
  have hH : Measurable fun x : (Fin m → Fin n → ℝ) × (Fin m → ℝ) =>
      ((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ :=
    measurable_matrix_nonsing_inv.comp (measurable_matrix_mul (measurable_matrix_transpose hW) hW)
  have hM : Measurable fun x : (Fin m → Fin n → ℝ) × (Fin m → ℝ) =>
      ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) :=
    measurable_mulVec (measurable_matrix_mul hH (measurable_matrix_transpose hW)) measurable_snd
  have hT := measurable_dotProduct hM hM
  exact ((measurableSet_le measurable_const hT).inter (measurableSet_le hT measurable_const)).compl

/-- **Concentration of the fit error `‖(Gᵀ G)⁻¹ Gᵀ ζ‖²` of a Gaussian vector `ζ`.** For `G` an
`m × (q+1)` Gaussian matrix and an independent standard Gaussian `ζ ∈ ℝ^m`, with `ν = m - q`,
`n = q + 1` and `0 < η < 1`, the squared norm `‖(Gᵀ G)⁻¹ Gᵀ ζ‖²` lies in
`[n (1 - η) / (ν (1 + η)), n (1 + η) / (ν (1 - η))]` except on an event of probability at most
`60 / (η⁴ ν²) + 60 / (η⁴ n²)`.

For fixed `G` of full rank, writing `G = Q R` (`exists_orthonormal_factor`), `z = Qᵀ ζ` is again a
standard Gaussian (`map_pi_gaussianReal_mulVec`) and the fit error is the quadratic form
`zᵀ (Gᵀ G)⁻¹ z` (`fitError_eq_quadForm`), so the bound is that of
`measure_quadForm_inv_gram_deviation_le`. -/
theorem measure_fitError_deviation_le {m q : ℕ} (hqm : q + 1 ≤ m) {η : ℝ} (hη : 0 < η)
    (hη1 : η < 1) :
    ((Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin m => gaussianReal 0 1))
        {x | ¬ (((q + 1 : ℕ) : ℝ) * (1 - η) / (((m - q : ℕ) : ℝ) * (1 + η)) ≤
              ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ∧
            ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ≤
              ((q + 1 : ℕ) : ℝ) * (1 + η) / (((m - q : ℕ) : ℝ) * (1 - η)))} ≤
      ENNReal.ofReal (60 / (η ^ 4 * ((m - q : ℕ) : ℝ) ^ 2)) +
        ENNReal.ofReal (60 / (η ^ 4 * ((q + 1 : ℕ) : ℝ) ^ 2)) := by
  set μG := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1
    with hμG
  set μζ := Measure.pi fun _ : Fin m => gaussianReal 0 1 with hμζ
  set μz := Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1 with hμz
  set c1 : ℝ := ((q + 1 : ℕ) : ℝ) * (1 - η) / (((m - q : ℕ) : ℝ) * (1 + η)) with hc1
  set c2 : ℝ := ((q + 1 : ℕ) : ℝ) * (1 + η) / (((m - q : ℕ) : ℝ) * (1 - η)) with hc2
  have hW : ∀ {β : Type} [MeasurableSpace β], Measurable fun x : (Fin m → Fin (q + 1) → ℝ) × β =>
      (Matrix.of x.1 : Matrix (Fin m) (Fin (q + 1)) ℝ) := fun {β} _ =>
    Measurable.of_eval_matrix _ fun i k =>
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_fst)
  have hH : ∀ {β : Type} [MeasurableSpace β], Measurable fun x : (Fin m → Fin (q + 1) → ℝ) × β =>
      ((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ := fun {β} _ =>
    measurable_matrix_nonsing_inv.comp
      (measurable_matrix_mul (measurable_matrix_transpose hW) hW)
  set ET : Set ((Fin m → Fin (q + 1) → ℝ) × (Fin m → ℝ)) :=
    {x | ¬ (c1 ≤ ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ∧
            ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ≤ c2)}
    with hET
  set EQ : Set ((Fin m → Fin (q + 1) → ℝ) × (Fin (q + 1) → ℝ)) :=
    {x | ¬ (c1 ≤ x.2 ⬝ᵥ (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ *ᵥ x.2) ∧
            x.2 ⬝ᵥ (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ *ᵥ x.2) ≤ c2)} with hEQ
  have hETm : MeasurableSet ET := measurableSet_not_le_le_fitError c1 c2
  have hEQm : MeasurableSet EQ := by
    have hQ := measurable_dotProduct (measurable_snd (α := Fin m → Fin (q + 1) → ℝ))
      (measurable_mulVec hH (measurable_snd (α := Fin m → Fin (q + 1) → ℝ)))
    exact ((measurableSet_le measurable_const hQ).inter
      (measurableSet_le hQ measurable_const)).compl
  have hEQb := measure_quadForm_inv_gram_deviation_le hqm hη hη1
  have hae : ∀ᵐ G ∂μG, IsUnit ((Matrix.of G)ᵀ * Matrix.of G).det :=
    ae_isUnit_det_gram_gaussianMatrix (q + 1) m hqm
  refine le_trans (le_of_eq ?_) hEQb
  rw [Measure.prod_apply hETm, Measure.prod_apply hEQm]
  refine lintegral_congr_ae (hae.mono fun G hG => ?_)
  change μζ (Prod.mk G ⁻¹' ET) = μz (Prod.mk G ⁻¹' EQ)
  obtain ⟨Qg, R, hQ, hR, hRT, hGQR⟩ := exists_orthonormal_factor (Matrix.of G) hG
  have hlaw := map_pi_gaussianReal_mulVec Qgᵀ (by simpa using hQ)
  have hsetm : MeasurableSet (Prod.mk G ⁻¹' EQ) := measurable_prodMk_left hEQm
  have hpre : Prod.mk G ⁻¹' ET = (fun ζ : Fin m → ℝ => Qgᵀ *ᵥ ζ) ⁻¹' (Prod.mk G ⁻¹' EQ) := by
    ext ζ
    simp only [hET, hEQ, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [fitError_eq_quadForm (Matrix.of G) Qg R hQ hR hRT hGQR ζ]
  rw [hpre, ← Measure.map_apply (by fun_prop) hsetm, hlaw]

end LinearRegression.DoubleDescent

end
