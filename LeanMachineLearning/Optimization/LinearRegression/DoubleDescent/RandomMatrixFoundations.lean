/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.StdGaussianRadial
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.GaussianMoments
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.GramInverse
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixMeasurability
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianAlgebra
public import LeanMachineLearning.Optimization.NTK.Initialization.ResidualConcentration

/-!
# Gaussian random matrices: invariance, full rank and the inverse Gram diagonal

The probabilistic half of the random-matrix input to double descent (Milestone 7c of the plan;
[Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]). Let `W` be a `p × q` matrix with
i.i.d. standard normal entries, written `Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q =>
gaussianReal 0 1` as in `NTK/Initialization`. We prove:

* `map_gaussianMatrix_mul_orthonormal`: **orthogonal invariance**: if `Qᵀ Q = 1` then `W Q` has
  again i.i.d. standard normal entries (from `NTK.gaussian_map_mulVec`);
* `map_dotProduct_projector_mulVec`: for a Gaussian vector `g` and an orthogonal projection `P`
  of trace `r`, `‖P g‖²` is `χ²_r` (`NTK.exists_orthonormal_rows_of_isStarProjection`);
* `measurePreserving_columnSplit`, `map_prod_eq_of_ae`: column `j` of `W` is independent of the
  remaining columns, and the law under a product measure follows from the conditional law;
* `ae_isUnit_det_gram_gaussianMatrix`: **almost-sure full column rank** for `q ≤ p`;
* `map_inv_gram_diag_gaussianMatrix`: **the diagonal entries of the inverse Gram matrix are exact
  inverse chi-squared variables**, `((Wᵀ W)⁻¹)ⱼⱼ ~ 1 / χ²_(p-q+1)`, from the dual-vector formula of
  `GramInverse.lean` and the radial moments of `StdGaussianRadial.lean`. No Wishart density,
  Bartlett decomposition or Haar measure is used.

Together with `GaussianMoments.lean` these are the inputs for the concentration of
`Tr ((Wᵀ W)⁻¹)` (Milestone 7d).
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK

universe u

/-- **Row-orthonormal maps preserve the product Gaussian.** If `A Aᵀ = 1`, then `A x` is a
standard Gaussian vector for `x` with i.i.d. standard normal coordinates. -/
theorem map_pi_gaussianReal_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ ι ℝ) (hA : A * Aᵀ = 1) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => A *ᵥ x) =
      Measure.pi fun _ : κ => gaussianReal 0 1 := by
  classical
  have h := NTK.gaussian_map_mulVec (0 : EuclideanSpace ℝ ι) 1 Matrix.PosSemidef.one A
  rw [multivariateGaussian_zero_one] at h
  have hm : (fun x : EuclideanSpace ℝ ι => A *ᵥ x.ofLp) =
      (fun y : EuclideanSpace ℝ κ => y.ofLp) ∘ (fun x : EuclideanSpace ℝ ι =>
        (WithLp.toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℝ κ)) := rfl
  rw [pi_gaussianReal_eq_map_stdGaussian (κ := ι), pi_gaussianReal_eq_map_stdGaussian (κ := κ),
    Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map (fun x : EuclideanSpace ℝ ι => A *ᵥ x.ofLp) _ = _
  rw [hm, ← Measure.map_map (by fun_prop) (by fun_prop), h]
  simp [hA, multivariateGaussian_zero_one]

/-- **Orthogonal invariance of a Gaussian matrix.** If `X` has i.i.d. standard normal entries and
`Q` has orthonormal columns (`Qᵀ Q = 1`), then `X Q` again has i.i.d. standard normal entries. -/
theorem map_gaussianMatrix_mul_orthonormal {ρ ι κ : Type*} [Fintype ρ] [Fintype ι]
    [Fintype κ] [DecidableEq κ] (Q : Matrix ι κ ℝ) (hQ : Qᵀ * Q = 1) :
    (Measure.pi fun _ : ρ => Measure.pi fun _ : ι => gaussianReal 0 1).map
        (fun W : ρ → ι → ℝ => fun i k => (Matrix.of W * Q) i k) =
      Measure.pi fun _ : ρ => Measure.pi fun _ : κ => gaussianReal 0 1 := by
  have hrow := map_pi_gaussianReal_mulVec Qᵀ (by simpa using hQ)
  have h := Measure.pi_map_pi (μ := fun _ : ρ => Measure.pi fun _ : ι => gaussianReal 0 1)
    (f := fun _ x => Qᵀ *ᵥ x) (fun _ => by fun_prop)
  simp only [hrow] at h
  rw [← h]
  congr 1
  funext W i k
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- **Projected Gaussian norm is chi-squared.** If `g` has i.i.d. standard normal coordinates and
`P` is an orthogonal projection matrix of trace `r`, then `‖P g‖²` has the law of `‖x‖²` for `x` a
standard Gaussian vector in `ℝ^r`, i.e. `χ²_r`. -/
theorem map_dotProduct_projector_mulVec {ι : Type u} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : IsStarProjection P) (r : ℕ) (hr : (r : ℝ) = P.trace) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun g => (P *ᵥ g) ⬝ᵥ (P *ᵥ g)) =
      (stdGaussian (EuclideanSpace ℝ (Fin r))).map (fun x => ‖x‖ ^ 2) := by
  obtain ⟨κ, _, _, O, hOO, hOtO, hcard⟩ := exists_orthonormal_rows_of_isStarProjection P hP
  have hκ : Fintype.card κ = r := by
    have : (Fintype.card κ : ℝ) = r := hcard.trans hr.symm
    exact_mod_cast this
  have hdot : ∀ (v : κ → ℝ) (x : ι → ℝ), (Oᵀ *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (O *ᵥ x) := fun v x => by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have h1 : ∀ g : ι → ℝ, (P *ᵥ g) ⬝ᵥ (P *ᵥ g) = (O *ᵥ g) ⬝ᵥ (O *ᵥ g) := fun g => by
    have hPg : P *ᵥ g = Oᵀ *ᵥ (O *ᵥ g) := by rw [← hOtO, Matrix.mulVec_mulVec]
    rw [hPg, hdot, Matrix.mulVec_mulVec, hOO, Matrix.one_mulVec]
  have e1 : (fun g : ι → ℝ => (P *ᵥ g) ⬝ᵥ (P *ᵥ g)) =
      (fun y : κ → ℝ => y ⬝ᵥ y) ∘ (fun g : ι → ℝ => O *ᵥ g) := funext h1
  have e2 : (fun y : κ → ℝ => y ⬝ᵥ y) =
      (fun x : EuclideanSpace ℝ κ => ‖x‖ ^ 2) ∘
        (fun y : κ → ℝ => (WithLp.toLp 2 y : EuclideanSpace ℝ κ)) := by
    funext y
    rw [Function.comp_apply, EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  rw [e1, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_gaussianReal_mulVec O hOO, e2,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian]
  let e : κ ≃ Fin r := Fintype.equivFinOfCardEq hκ
  let f : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  rw [← stdGaussian_map f, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [f]

/-- **Column splitting of a Gaussian matrix.** For `W` with i.i.d. standard normal entries, column
`j` and the matrix of the remaining columns are independent: the map
`W ↦ (W · j, W with column j deleted)` is measure preserving into a product measure. -/
theorem measurePreserving_columnSplit {p q : ℕ} (j : Fin (q + 1)) :
    MeasurePreserving
      (fun W : Fin p → Fin (q + 1) → ℝ => (fun i => W i j, fun i k => W i (j.succAbove k)))
      (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin p => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1)) := by
  have hrow : MeasurePreserving (fun x : Fin (q + 1) → ℝ => (x j, fun k => x (j.succAbove k)))
      (Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin q => gaussianReal 0 1)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => gaussianReal 0 1) j
  have h1 := measurePreserving_pi
    (fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)
    (fun _ : Fin p => (gaussianReal 0 1).prod (Measure.pi fun _ : Fin q => gaussianReal 0 1))
    (f := fun _ => fun x : Fin (q + 1) → ℝ => (x j, fun k => x (j.succAbove k))) (fun _ => hrow)
  have h2 := measurePreserving_arrowProdEquivProdArrow ℝ (Fin q → ℝ) (Fin p)
    (fun _ => gaussianReal 0 1) (fun _ => Measure.pi fun _ : Fin q => gaussianReal 0 1)
  exact h2.comp h1

/-- **Law under a product measure from the conditional law.** If `F : α × β → γ` is measurable and,
for `B`-a.e. `b`, the law of `a ↦ F (a, b)` under `A` is a fixed probability measure `λ`, then the
law of `F` under `A ⊗ B` is `λ`. -/
theorem map_prod_eq_of_ae {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (A : Measure α) (B : Measure β) [SFinite A] [IsProbabilityMeasure B]
    (F : α × β → γ) (hF : Measurable F) (lam : Measure γ) [IsProbabilityMeasure lam]
    (h : ∀ᵐ b ∂B, A.map (fun a => F (a, b)) = lam) : (A.prod B).map F = lam := by
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply_symm (hF hs)]
  have : ∀ᵐ b ∂B, A ((fun a => (a, b)) ⁻¹' (F ⁻¹' s)) = lam s := by
    filter_upwards [h] with b hb
    rw [← hb]
    exact (Measure.map_apply (f := fun a => F (a, b))
      (hF.comp (measurable_id.prodMk measurable_const)) hs).symm
  rw [lintegral_congr_ae this]
  simp

/-- **Prepending a column keeps full column rank** if the new column is outside the span of the
others: if `W'` is injective and `g ∉ range W'`, then `[g | W']` is injective. -/
theorem injective_mulVec_cons {p q : ℕ} (W' : Matrix (Fin p) (Fin q) ℝ) (g : Fin p → ℝ)
    (hW' : Function.Injective W'.mulVec) (hg : ∀ v, W' *ᵥ v ≠ g) :
    Function.Injective (Matrix.of fun i => (Fin.cons (g i) (W' i) : Fin (q + 1) → ℝ)).mulVec := by
  intro v w hvw
  set M : Matrix (Fin p) (Fin (q + 1)) ℝ :=
    Matrix.of fun i => (Fin.cons (g i) (W' i) : Fin (q + 1) → ℝ) with hM
  have hd : M *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
  have hexp : ∀ x : Fin (q + 1) → ℝ,
      M *ᵥ x = x 0 • g + W' *ᵥ (fun k : Fin q => x k.succ) := fun x => by
    ext i
    simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
  rw [hexp] at hd
  set d := v - w with hdd
  by_cases h0 : d 0 = 0
  · rw [h0, zero_smul, zero_add] at hd
    have htail : (fun k : Fin q => d k.succ) = 0 := hW' (by rw [hd, Matrix.mulVec_zero])
    have : d = 0 := by
      funext k
      refine Fin.cases h0 (fun k => ?_) k
      exact congrFun htail k
    exact sub_eq_zero.mp this
  · exfalso
    refine hg (-(d 0)⁻¹ • fun k : Fin q => d k.succ) ?_
    rw [Matrix.mulVec_smul]
    have : W' *ᵥ (fun k : Fin q => d k.succ) = -(d 0 • g) := eq_neg_of_add_eq_zero_right hd
    rw [this, smul_neg, neg_smul, smul_smul, inv_mul_cancel₀ h0, one_smul, neg_neg]

private theorem measurable_consColumns {p q : ℕ} :
    Measurable (fun y : (Fin p → ℝ) × (Fin p → Fin q → ℝ) =>
      Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun k => ?_
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [Matrix.of_apply, Fin.cons_zero]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [Matrix.of_apply, Fin.cons_succ]
    exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd)

/-- **A Gaussian matrix with at least as many rows as columns has full column rank almost
surely.** Proved by induction on the number of columns: a new Gaussian column avoids the proper
subspace spanned by the previous ones (`pi_gaussianReal_submodule_eq_zero`). -/
theorem ae_isUnit_det_gram_gaussianMatrix :
    ∀ (q p : ℕ), q ≤ p →
      ∀ᵐ W ∂(Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1),
        IsUnit ((Matrix.of W)ᵀ * Matrix.of W).det := by
  intro q
  induction q with
  | zero => intro p _; exact Filter.Eventually.of_forall fun W => by simp
  | succ q ih =>
    intro p hqp
    set A : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p => gaussianReal 0 1 with hA
    set B : Measure (Fin p → Fin q → ℝ) :=
      Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1 with hB
    have hmp := measurePreserving_columnSplit (p := p) (q := q) 0
    have hN : MeasurableSet {y : (Fin p → ℝ) × (Fin p → Fin q → ℝ) |
        ¬ IsUnit (((Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))ᵀ *
          (Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))).det)} := by
      have hdet : Measurable fun W : Matrix (Fin p) (Fin (q + 1)) ℝ => (Wᵀ * W).det :=
        (continuous_id.matrix_transpose.matrix_mul continuous_id).matrix_det.measurable
      have := (measurableSet_singleton (0 : ℝ)).preimage (hdet.comp measurable_consColumns)
      have e : {y : (Fin p → ℝ) × (Fin p → Fin q → ℝ) |
          ¬ IsUnit (((Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))ᵀ *
            (Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))).det)} =
          ((fun W : Matrix (Fin p) (Fin (q + 1)) ℝ => (Wᵀ * W).det) ∘ fun y =>
            Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ)) ⁻¹' {0} := by
        ext y; simp [isUnit_iff_ne_zero]
      rw [e]; exact this
    have hB' : ∀ᵐ W' ∂B, IsUnit ((Matrix.of W')ᵀ * Matrix.of W').det :=
      ih p (Nat.le_of_succ_le hqp)
    have hnull : (A.prod B) {y : (Fin p → ℝ) × (Fin p → Fin q → ℝ) |
        ¬ IsUnit (((Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))ᵀ *
          (Matrix.of fun i => (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))).det)} = 0 := by
      rw [Measure.prod_apply_symm hN]
      have hin : ∀ᵐ W' ∂B, A ((fun g : Fin p → ℝ => (g, W')) ⁻¹' {y : (Fin p → ℝ) ×
          (Fin p → Fin q → ℝ) | ¬ IsUnit (((Matrix.of fun i =>
            (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))ᵀ * (Matrix.of fun i =>
            (Fin.cons (y.1 i) (y.2 i) : Fin (q + 1) → ℝ))).det)}) = 0 := by
        filter_upwards [hB'] with W' hW'
        have hinj := (isUnit_det_gram_iff_injective (Matrix.of W')).1 hW'
        have hne : LinearMap.range (Matrix.mulVecLin (Matrix.of W')) ≠ ⊤ := by
          intro h
          have h1 := LinearMap.finrank_range_le (Matrix.mulVecLin (Matrix.of W'))
          rw [h, finrank_top] at h1
          simp at h1
          omega
        refine measure_mono_null (t := (LinearMap.range (Matrix.mulVecLin (Matrix.of W')) :
          Set (Fin p → ℝ))) ?_ (pi_gaussianReal_submodule_eq_zero _ hne)
        intro g hg
        by_contra hgr
        refine hg ?_
        rw [isUnit_det_gram_iff_injective]
        exact injective_mulVec_cons (Matrix.of W') g hinj fun v hv =>
          hgr ⟨v, by simpa using hv⟩
      rw [lintegral_congr_ae hin]
      simp
    have hae := hmp.quasiMeasurePreserving.ae (measure_eq_zero_iff_ae_notMem.mp hnull)
    filter_upwards [hae] with W hW
    have e : (fun i => (Fin.cons (W i 0) (fun k : Fin q => W i (Fin.succAbove 0 k)) :
        Fin (q + 1) → ℝ)) = W := by
      funext i
      simp only [Fin.succAbove_zero]
      exact Fin.cons_self_tail (W i)
    have h : IsUnit (((Matrix.of fun i => (Fin.cons (W i 0) (fun k : Fin q =>
        W i (Fin.succAbove 0 k)) : Fin (q + 1) → ℝ))ᵀ * (Matrix.of fun i => (Fin.cons (W i 0)
        (fun k : Fin q => W i (Fin.succAbove 0 k)) : Fin (q + 1) → ℝ))).det) := not_not.mp hW
    rw [e] at h
    exact h

/-- **Dual-vector formula for a `Fin`-indexed Gaussian matrix.** For `W` with `Wᵀ W` invertible,
`((Wᵀ W)⁻¹)ⱼⱼ = ‖(1 - P) wⱼ‖⁻²` with `wⱼ` the `j`-th column and `P` the Gram projector of the
remaining columns, indexed by `Fin q` through `Fin.succAbove`. -/
theorem inv_gram_apply_self_succAbove {p q : ℕ} (W : Fin p → Fin (q + 1) → ℝ)
    (hW : IsUnit ((Matrix.of W)ᵀ * Matrix.of W).det) (j : Fin (q + 1)) :
    ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j =
      (((1 - gramProjector (Matrix.of fun i k => W i (j.succAbove k))) *ᵥ fun i => W i j) ⬝ᵥ
        ((1 - gramProjector (Matrix.of fun i k => W i (j.succAbove k))) *ᵥ fun i => W i j))⁻¹ := by
  have h := inv_gram_apply_self (Matrix.of W) hW j
  have e : (Matrix.of fun i k => W i (j.succAbove k) : Matrix (Fin p) (Fin q) ℝ) =
      ((Matrix.of W).submatrix id (Subtype.val : {k // k ≠ j} → Fin (q + 1))).submatrix id
        (finSuccAboveEquiv j) := by
    ext i k
    rfl
  rw [e, gramProjector_submatrix_equiv]
  exact h

/-- **Law of a diagonal entry of the inverse Gram matrix.** For a `p × (q+1)` matrix `W` with
i.i.d. standard normal entries and `q + 1 ≤ p`, `((Wᵀ W)⁻¹)ⱼⱼ` has the law of `(‖x‖²)⁻¹` for `x` a
standard Gaussian vector in `ℝ^(p-q)`, i.e. of `1 / χ²_(p-q)` with `p - q = p - (q+1) + 1`. -/
theorem map_inv_gram_diag_gaussianMatrix {p q : ℕ} (hqp : q + 1 ≤ p) (j : Fin (q + 1)) :
    (Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).map
        (fun W => ((Matrix.of W)ᵀ * Matrix.of W)⁻¹ j j) =
      (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map (fun x => (‖x‖ ^ 2)⁻¹) := by
  set A : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p => gaussianReal 0 1 with hA
  set B : Measure (Fin p → Fin q → ℝ) :=
    Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin q => gaussianReal 0 1 with hB
  have hmp := measurePreserving_columnSplit (p := p) (q := q) j
  set F : (Fin p → ℝ) × (Fin p → Fin q → ℝ) → ℝ := fun y =>
    (((1 - NTK.gramProjector (Matrix.of y.2)) *ᵥ y.1) ⬝ᵥ
      ((1 - NTK.gramProjector (Matrix.of y.2)) *ᵥ y.1))⁻¹ with hFdef
  have hF : Measurable F := by
    have hP : Measurable fun y : (Fin p → ℝ) × (Fin p → Fin q → ℝ) =>
        NTK.gramProjector (Matrix.of y.2) :=
      NTK.measurable_gramProjector (Φ := fun y : (Fin p → ℝ) × (Fin p → Fin q → ℝ) =>
        (Matrix.of y.2 : Matrix (Fin p) (Fin q) ℝ))
        (Measurable.of_eval fun i => Measurable.of_eval fun k =>
          (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd))
    have hv : Measurable fun y : (Fin p → ℝ) × (Fin p → Fin q → ℝ) =>
        (1 - NTK.gramProjector (Matrix.of y.2)) *ᵥ y.1 :=
      NTK.measurable_mulVec (NTK.measurable_orthogonalComplement hP) measurable_fst
    exact (NTK.measurable_dotProduct hv hv).inv
  have hlam : ∀ᵐ W' ∂B, A.map (fun g => F (g, W')) =
      (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map (fun x => (‖x‖ ^ 2)⁻¹) := by
    filter_upwards [ae_isUnit_det_gram_gaussianMatrix q p (Nat.le_of_succ_le hqp)] with W' hW'
    have hP := NTK.isOrthogonalProjection_gramProjector (Matrix.of W') hW'
    have h1 : IsStarProjection (1 - NTK.gramProjector (Matrix.of W')) := hP.one_sub
    have htr : ((p - q : ℕ) : ℝ) = (1 - NTK.gramProjector (Matrix.of W')).trace := by
      rw [Matrix.trace_sub, Matrix.trace_one, NTK.trace_gramProjector _ hW']
      simp [Nat.cast_sub (Nat.le_of_succ_le hqp)]
    have hlaw := map_dotProduct_projector_mulVec _ h1 (p - q) htr
    have e : (fun g : Fin p → ℝ => F (g, W')) = (fun s : ℝ => s⁻¹) ∘
        (fun g : Fin p → ℝ => ((1 - NTK.gramProjector (Matrix.of W')) *ᵥ g) ⬝ᵥ
          ((1 - NTK.gramProjector (Matrix.of W')) *ᵥ g)) := rfl
    have hm1 : Measurable fun g : Fin p → ℝ => ((1 - NTK.gramProjector (Matrix.of W')) *ᵥ g) ⬝ᵥ
        ((1 - NTK.gramProjector (Matrix.of W')) *ᵥ g) :=
      NTK.measurable_dotProduct (NTK.measurable_mulVec measurable_const measurable_id)
        (NTK.measurable_mulVec measurable_const measurable_id)
    rw [e, ← Measure.map_map measurable_inv hm1, hlaw,
      Measure.map_map measurable_inv (by fun_prop)]
    rfl
  have hlaw : (A.prod B).map F = (stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map
      (fun x => (‖x‖ ^ 2)⁻¹) := by
    have : IsProbabilityMeasure ((stdGaussian (EuclideanSpace ℝ (Fin (p - q)))).map
        (fun x => (‖x‖ ^ 2)⁻¹)) :=
      inferInstance
    exact map_prod_eq_of_ae A B F hF _ hlam
  rw [← hlaw, ← hmp.map_eq, Measure.map_map hF hmp.measurable]
  refine Measure.map_congr ?_
  filter_upwards [ae_isUnit_det_gram_gaussianMatrix (q + 1) p hqp] with W hW
  exact inv_gram_apply_self_succAbove W hW j

end LinearRegression.DoubleDescent

end
