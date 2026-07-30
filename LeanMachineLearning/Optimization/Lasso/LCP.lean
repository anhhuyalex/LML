/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
/-!
# Linear Complementarity Problem (LCP) Formulations for Lasso

This file formalizes the primal-dual LCP formulations of the Lasso regularization path.
-/

@[expose] public section

namespace Lasso

variable {ι : Type*} [Fintype ι]

open scoped ENNReal

/-- The affine term `q = -r + (lambda + 1 / μ) * 1` in the positive-lasso LCP. -/
noncomputable def lcpQ (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => -r i + lambda + 1 / μ)

/-- The affine term `q(μ) = -μ r + (1 + μ lambda) * 1` in the parametric LCP. -/
noncomputable def parametricLcpQ (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => -μ * r i + 1 + μ * lambda)

/--
The Linear Complementarity Problem (LCP) associated with the positive lasso.
For a given `x`, it requires finding `v` such that `v = q + Mx`,
`v ≥ 0`, `x ≥ 0`, and `⟨v, x⟩ = 0`.
-/
def isLCP (M : Matrix ι ι ℝ) (q x v : EuclideanSpace ℝ ι) : Prop :=
  v = q + matVec M x ∧
  Nonnegative v ∧ Nonnegative x ∧ inner ℝ v x = (0 : ℝ)

/-- Coordinatewise derivative of a vector-valued path. -/
noncomputable def coordinateDeriv (f : ℝ → EuclideanSpace ℝ ι) (t : ℝ) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => deriv (fun u => f u i) t)

/-- Local Lipschitz continuity on every compact interval `[a,b]` with `0 ≤ a`. -/
structure LocallyLipschitzOnCompacts (f : ℝ → EuclideanSpace ℝ ι) : Prop where
  lipschitz_on_Icc :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ μ ∈ Set.Icc a b, ∀ ν ∈ Set.Icc a b,
          ‖f μ - f ν‖ ≤ K * |μ - ν|

/-- Absolute continuity on every compact subinterval of `(0, ∞)`.

This is the regularity hypothesis used for the selected Lasso path in
Theorems 2.2 and 3.2.  It deliberately says `0 < a`: the source theorem only
assumes regularity locally away from the singular endpoint `μ = 0`.
-/
structure LocallyAbsolutelyContinuousOnPositiveCompacts
    (f : ℝ → EuclideanSpace ℝ ι) : Prop where
  absolutelyContinuousOn_Icc :
    ∀ a b : ℝ, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval f a b

/-- Absolute continuity on every compact subinterval of `[0, ∞)`.

Lemma 4.12 supplies this stronger endpoint-inclusive property for the scaled
path `z(μ) = μ x(μ)` under coordinatewise monotonicity.
-/
structure LocallyAbsolutelyContinuousOnNonnegativeCompacts
    (f : ℝ → EuclideanSpace ℝ ι) : Prop where
  absolutelyContinuousOn_Icc :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval f a b

/-- A local Lipschitz estimate on `[0, ∞)` implies local absolute continuity.

Mathlib reference:
`LipschitzOnWith.absolutelyContinuousOnInterval` in
`Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`.
-/
lemma LocallyLipschitzOnCompacts.absolutelyContinuous
    {f : ℝ → EuclideanSpace ℝ ι} (hf : LocallyLipschitzOnCompacts f) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts f := by
  constructor
  intro a b ha hab
  obtain ⟨K, hK, hKbound⟩ := hf.lipschitz_on_Icc a b ha hab
  have hlip : LipschitzOnWith K.toNNReal f (Set.Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul (K := K.toNNReal)
    intro μ hμ ν hν
    simpa [dist_eq_norm, Real.dist_eq, Real.toNNReal_of_nonneg hK] using
      hKbound μ hμ ν hν
  have hlip' : LipschitzOnWith K.toNNReal f (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hlip
  exact hlip'.absolutelyContinuousOnInterval

/-- The scaled dual path `w(μ) / (1 + μ lambda)` from Lemma 4.11. -/
noncomputable def scaledDualPath (lambda : ℝ) (w : ℝ → EuclideanSpace ℝ ι) :
    ℝ → EuclideanSpace ℝ ι :=
  fun μ => (1 / (1 + μ * lambda)) • w μ

omit [Fintype ι] in
/--
Algebraic identity relating `w` and its scaled dual path:
`w(t) = (1 + t * lambda) • scaledDualPath lambda w t` when the denominator is nonzero.

This is used to relate the Lipschitz constants of `w` and its scaled version.
-/
lemma scaledDualPath_smul_eq (lambda : ℝ) (w : ℝ → EuclideanSpace ℝ ι) (t : ℝ)
    (h_den_ne_zero : 1 + t * lambda ≠ 0) :
    w t = (1 + t * lambda) • scaledDualPath lambda w t := by
  dsimp [scaledDualPath]
  calc
    w t = (1 : ℝ) • w t := by simp
    _ = ((1 + t * lambda) * (1 / (1 + t * lambda))) • w t := by
      have h : (1 + t * lambda) * (1 / (1 + t * lambda)) = (1 : ℝ) := by
        field_simp [h_den_ne_zero]
      rw [h]
    _ = (1 + t * lambda) • ((1 / (1 + t * lambda)) • w t) := by rw [smul_smul]

/--
Core norm inequality linking `w` and its scaled dual path:
`‖w μ - w ν‖ ≤ |1 + μ·λ|·‖wt μ - wt ν‖ + |λ|·|μ-ν|·‖wt ν‖`
where `wt = scaledDualPath lambda w`.

This follows from the identity `w(t) = (1 + t·λ) • wt(t)` and the triangle inequality.
-/
lemma norm_sub_scaled_le (lambda : ℝ) (w : ℝ → EuclideanSpace ℝ ι) (μ ν : ℝ)
    (h_den_ne_zero_μ : 1 + μ * lambda ≠ 0) (h_den_ne_zero_ν : 1 + ν * lambda ≠ 0) :
    ‖w μ - w ν‖ ≤ |1 + μ * lambda| * ‖scaledDualPath lambda w μ - scaledDualPath lambda w ν‖
      + |lambda| * |μ - ν| * ‖scaledDualPath lambda w ν‖ := by
  have hw_eq_μ : w μ = (1 + μ * lambda) • scaledDualPath lambda w μ :=
    scaledDualPath_smul_eq lambda w μ h_den_ne_zero_μ
  have hw_eq_ν : w ν = (1 + ν * lambda) • scaledDualPath lambda w ν :=
    scaledDualPath_smul_eq lambda w ν h_den_ne_zero_ν
  calc
    ‖w μ - w ν‖ = ‖((1 + μ * lambda) • scaledDualPath lambda w μ) -
      ((1 + ν * lambda) • scaledDualPath lambda w ν)‖ := by rw [hw_eq_μ, hw_eq_ν]
    _ = ‖(((1 + μ * lambda) • scaledDualPath lambda w μ) -
          ((1 + μ * lambda) • scaledDualPath lambda w ν)) +
        (((1 + μ * lambda) • scaledDualPath lambda w ν) -
          ((1 + ν * lambda) • scaledDualPath lambda w ν))‖ := by rw [← sub_add_sub_cancel]
    _ ≤ ‖((1 + μ * lambda) • scaledDualPath lambda w μ) -
          ((1 + μ * lambda) • scaledDualPath lambda w ν)‖ +
        ‖((1 + μ * lambda) • scaledDualPath lambda w ν) -
          ((1 + ν * lambda) • scaledDualPath lambda w ν)‖ := norm_add_le _ _
    _ = ‖(1 + μ * lambda) • (scaledDualPath lambda w μ - scaledDualPath lambda w ν)‖
        + ‖((1 + μ * lambda) - (1 + ν * lambda)) • scaledDualPath lambda w ν‖ := by
      rw [smul_sub, sub_smul]
    _ = ‖(1 + μ * lambda) • (scaledDualPath lambda w μ - scaledDualPath lambda w ν)‖
        + ‖(lambda * (μ - ν)) • scaledDualPath lambda w ν‖ := by ring_nf
    _ = |1 + μ * lambda| * ‖scaledDualPath lambda w μ - scaledDualPath lambda w ν‖
        + |lambda * (μ - ν)| * ‖scaledDualPath lambda w ν‖ := by
      simp [norm_smul, Real.norm_eq_abs]
    _ = |1 + μ * lambda| * ‖scaledDualPath lambda w μ - scaledDualPath lambda w ν‖
        + (|lambda| * |μ - ν|) * ‖scaledDualPath lambda w ν‖ := by rw [abs_mul]

/--
If the scaled dual path `scaledDualPath lambda w` is locally Lipschitz on compacts,
then so is `w` itself. The constant `K'` for `w` on an interval `[a,b]` is constructed
from the constant `K` for the scaled path as `K' = C1 * K + |lambda| * C2` where
`C1 = max |1 + a·λ| |1 + b·λ|` and `C2 = ‖wt a‖ + K*(b-a)`.

Requires `lambda ≥ 0` to ensure denominators `1 + t·λ` stay positive.
-/
lemma locallyLipschitzOnCompacts_of_scaledDual_lipschitz
    (lambda : ℝ) (hlambda_nonneg : 0 ≤ lambda) (w : ℝ → EuclideanSpace ℝ ι)
    (h_scaled_lip : LocallyLipschitzOnCompacts (scaledDualPath lambda w)) :
    LocallyLipschitzOnCompacts w := by
  constructor
  intro a b ha hab
  rcases h_scaled_lip.lipschitz_on_Icc a b ha hab with ⟨K, hK_nonneg, hK_lip⟩
  -- Define bounds for the compact interval
  let C1 := max |1 + a * lambda| |1 + b * lambda|
  let C2 := ‖scaledDualPath lambda w a‖ + K * (b - a)
  let K' := C1 * K + |lambda| * C2
  refine ⟨K', ?_, ?_⟩
  · -- Prove K' is non-negative
    have hC1_nonneg : 0 ≤ C1 := by
      dsimp [C1]
      have h_abs1 : 0 ≤ |1 + a * lambda| := abs_nonneg _
      exact le_trans h_abs1 (le_max_left _ _)
    have hba_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
    have hC2_nonneg : 0 ≤ C2 := by
      dsimp [C2]
      have hnorm : 0 ≤ ‖scaledDualPath lambda w a‖ := norm_nonneg _
      have hmul : 0 ≤ K * (b - a) := mul_nonneg hK_nonneg hba_nonneg
      exact add_nonneg hnorm hmul
    have habs_lambda_nonneg : 0 ≤ |lambda| := abs_nonneg _
    have hprod1 : 0 ≤ C1 * K := mul_nonneg hC1_nonneg hK_nonneg
    have hprod2 : 0 ≤ |lambda| * C2 := mul_nonneg habs_lambda_nonneg hC2_nonneg
    dsimp [K']
    exact add_nonneg hprod1 hprod2
  · -- Prove the Lipschitz bound
    intro μ hμ ν hν
    -- Extract inequalities from interval membership
    have hμ_low : a ≤ μ := hμ.1
    have hμ_high : μ ≤ b := hμ.2
    have hν_low : a ≤ ν := hν.1
    have hν_high : ν ≤ b := hν.2
    have hμ_nonneg : 0 ≤ μ := le_trans ha hμ_low
    have hν_nonneg : 0 ≤ ν := le_trans ha hν_low
    have h_den_ne_zero_μ : 1 + μ * lambda ≠ 0 := by nlinarith
    have h_den_ne_zero_ν : 1 + ν * lambda ≠ 0 := by nlinarith
    -- Define the scaled dual path for convenience
    set wt := scaledDualPath lambda w
    -- Relate w and wt: w(t) = (1 + t*lambda) • wt(t)
    have hw_eq_μ : w μ = (1 + μ * lambda) • wt μ :=
      scaledDualPath_smul_eq lambda w μ h_den_ne_zero_μ
    have hw_eq_ν : w ν = (1 + ν * lambda) • wt ν :=
      scaledDualPath_smul_eq lambda w ν h_den_ne_zero_ν
    -- Bound |1 + μ*lambda| ≤ C1 = max(|1+a*lambda|, |1+b*lambda|)
    -- Since all terms are positive, we can drop absolute values
    have h_abs_bound : |1 + μ * lambda| ≤ C1 := by
      dsimp [C1]
      have h_nonneg_a : 0 ≤ 1 + a * lambda := by nlinarith
      have h_nonneg_μ : 0 ≤ 1 + μ * lambda := by nlinarith
      have h_nonneg_b : 0 ≤ 1 + b * lambda := by nlinarith
      rw [abs_of_nonneg h_nonneg_μ, abs_of_nonneg h_nonneg_a, abs_of_nonneg h_nonneg_b]
      have h_le : 1 + μ * lambda ≤ 1 + b * lambda := by nlinarith
      exact h_le.trans (le_max_right _ _)
    -- C1 is nonnegative (needed for mul_le_mul)
    have hC1_nonneg : 0 ≤ C1 := by
      dsimp [C1]
      have h1 : 0 ≤ |1 + a * lambda| := abs_nonneg _
      exact le_trans h1 (le_max_left _ _)
    -- Bound ‖wt ν‖ ≤ C2 = ‖wt a‖ + K*(b-a)
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    have h_diff_bound_νa : ‖wt ν - wt a‖ ≤ K * |ν - a| := hK_lip ν hν a ha_mem
    have h_diff_bound_μν : ‖wt μ - wt ν‖ ≤ K * |μ - ν| := hK_lip μ hμ ν hν
    have h_wt_norm_bound : ‖wt ν‖ ≤ C2 := by
      dsimp [C2]
      have h_triangle : ‖wt ν‖ ≤ ‖wt a‖ + ‖wt ν - wt a‖ := by
        calc
          ‖wt ν‖ = ‖(wt ν - wt a) + wt a‖ := by simp
          _ ≤ ‖wt ν - wt a‖ + ‖wt a‖ := norm_add_le _ _
          _ = ‖wt a‖ + ‖wt ν - wt a‖ := add_comm _ _
      have h_abs_νa : |ν - a| ≤ b - a := by
        have hνa_nonneg : 0 ≤ ν - a := sub_nonneg.mpr hν_low
        rw [abs_of_nonneg hνa_nonneg]
        nlinarith
      have h_diff_bound' : ‖wt ν - wt a‖ ≤ K * (b - a) := by
        have h_mul : K * |ν - a| ≤ K * (b - a) :=
          mul_le_mul_of_nonneg_left h_abs_νa hK_nonneg
        linarith
      nlinarith
    -- Main inequality: apply the core norm inequality linking w and its scaled dual,
    -- then bound using the Lipschitz property of the scaled path and the norm bound on wt ν.
    have h_norm_le := norm_sub_scaled_le lambda w μ ν h_den_ne_zero_μ h_den_ne_zero_ν
    calc
      ‖w μ - w ν‖ ≤ |1 + μ * lambda| * ‖wt μ - wt ν‖ + |lambda| * |μ - ν| * ‖wt ν‖ := h_norm_le
      _ ≤ C1 * (K * |μ - ν|) + (|lambda| * |μ - ν|) * C2 := by
        have h_mul1 : |1 + μ * lambda| * ‖wt μ - wt ν‖ ≤ C1 * (K * |μ - ν|) := by
          have h1 : |1 + μ * lambda| * ‖wt μ - wt ν‖ ≤ C1 * ‖wt μ - wt ν‖ :=
            mul_le_mul_of_nonneg_right h_abs_bound (norm_nonneg _)
          have h2 : C1 * ‖wt μ - wt ν‖ ≤ C1 * (K * |μ - ν|) :=
            mul_le_mul_of_nonneg_left h_diff_bound_μν hC1_nonneg
          exact le_trans h1 h2
        have h_mul2 : (|lambda| * |μ - ν|) * ‖wt ν‖ ≤ (|lambda| * |μ - ν|) * C2 :=
          mul_le_mul_of_nonneg_left h_wt_norm_bound
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        exact add_le_add h_mul1 h_mul2
      _ = (C1 * K + |lambda| * C2) * |μ - ν| := by ring
      _ = K' * |μ - ν| := rfl

/--
The seminorm induced by an explicit matrix used as `M†`.

This avoids hallucinating a Mathlib Moore-Penrose pseudoinverse API.  Once the
project has a canonical pseudoinverse object for finite-dimensional matrices,
the parameter `Mdagger` should be instantiated with that matrix.
-/
noncomputable def pseudoInverseSeminorm
    (Mdagger : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.sqrt (max 0 (inner ℝ x (matVec Mdagger x)))

/-- The properties of `M†` actually used by the Lasso proof.

Mathlib currently has no canonical Moore--Penrose inverse for these real
matrices. Rather than accepting an unconstrained matrix called `Mdagger`, this
predicate records positivity and the generalized-inverse identity on
`range(M)`. The Moore--Penrose inverse of a symmetric PSD matrix satisfies both
properties (via its spectral decomposition); see Barata--Hussein,
*The Moore--Penrose Pseudoinverse: A Tutorial Review of the Theory*
<https://arxiv.org/abs/1110.6882> and the four Penrose equations summarized at
<https://en.wikipedia.org/wiki/Moore%E2%80%93Penrose_inverse>.
-/
structure IsPSDRangeInverse (M Mdagger : Matrix ι ι ℝ) : Prop where
  psd : IsPositiveSemidefinite Mdagger
  range_inverse :
    ∀ v : EuclideanSpace ℝ ι,
      matVec M (matVec Mdagger (matVec M v)) = matVec M v

/--
Regularity package for the unique dual solution of the parametric LCP.
This abstracts the three conclusions of Lemma 4.11: absolute continuity
(represented here by local Lipschitz continuity), derivative in `Span M`, and a
uniform derivative bound in the `M†` seminorm used in `docs/Lasso.md`.
-/
structure ParametricLCPDualRegular
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (w : ℝ → EuclideanSpace ℝ ι) : Prop where
  inverse_spec : IsPSDRangeInverse M Mdagger
  is_dual_solution :
    ∃ z : ℝ → EuclideanSpace ℝ ι,
      ∀ μ, 0 ≤ μ → isLCP M (parametricLcpQ r lambda μ) (z μ) (w μ)
  locally_lipschitz : LocallyLipschitzOnCompacts w
  absolutely_continuous : LocallyAbsolutelyContinuousOnNonnegativeCompacts w
  scaled_derivative_in_span :
    ∀ μ, 0 ≤ μ → InMatrixSpan M (deriv (scaledDualPath lambda w) μ)
  scaled_derivative_bound :
    ∀ μ, 0 ≤ μ →
      pseudoInverseSeminorm Mdagger (deriv (scaledDualPath lambda w) μ) ≤
        pseudoInverseSeminorm Mdagger r

/--
The LCP with derivatives from the proof sketch in Section 4.1.  Here `z` is the
integrated primal path, `dz` is its derivative, and `w` is the dual path.
-/
def isLCPWithDerivatives
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda s : ℝ)
    (z dz w : EuclideanSpace ℝ ι) : Prop :=
  w = parametricLcpQ r lambda s + matVec M z ∧
  Nonnegative w ∧ Nonnegative dz ∧ inner ℝ w dz = (0 : ℝ)

/-- A conic combination of a finite family of vectors. -/
def InCone {κ : Type*} [Fintype κ]
    (a : κ → EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι) : Prop :=
  ∃ coeff : κ → ℝ, (∀ i, 0 ≤ coeff i) ∧ (∑ i, coeff i • a i) = y

lemma norm_one_eq_inner_ones_of_nonnegative (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) :
    ‖WithLp.toLp 1 (x.ofLp)‖ = inner ℝ ones x := by
  have h1 : ‖WithLp.toLp 1 (x.ofLp)‖ = ∑ i, |x.ofLp i| := by
    rw [PiLp.norm_eq_of_nat 1 (by norm_num)]
    simp
  have h2 : ∑ i, |x.ofLp i| = ∑ i, x.ofLp i :=
    Finset.sum_congr rfl (fun i _ => abs_of_nonneg (hx i))
  have h3 : inner ℝ ones x = ∑ i, x.ofLp i := by
    simp [PiLp.inner_apply, ones, euclideanOf]
  rw [h1, h2, h3]

omit [Fintype ι] in
lemma lcpQ_eq (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    lcpQ r lambda μ = -r + (lambda + 1 / μ) • ones := by
  ext i
  simp [lcpQ, ones, euclideanOf]
  ring

lemma positiveLassoObjective_eq (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) :
    positiveLassoObjective M r lambda μ x =
    (1 / 2 : ℝ) * inner ℝ x (matVec M x) + inner ℝ (lcpQ r lambda μ) x := by
  dsimp [positiveLassoObjective, lassoObjective, quadraticLoss]
  rw [norm_one_eq_inner_ones_of_nonnegative x hx]
  rw [lcpQ_eq]
  rw [inner_add_left, inner_neg_left, real_inner_smul_left]
  ring

lemma quadratic_expansion (M : Matrix ι ι ℝ) (q x y : EuclideanSpace ℝ ι)
    (hM_symm : M.IsSymm) :
    ((1 / 2 : ℝ) * inner ℝ y (matVec M y) + inner ℝ q y) -
    ((1 / 2 : ℝ) * inner ℝ x (matVec M x) + inner ℝ q x) =
    (1 / 2 : ℝ) * inner ℝ (y - x) (matVec M (y - x)) +
    inner ℝ (matVec M x + q) (y - x) := by
  rw [matVec_sub]
  rw [inner_sub_right, inner_sub_right, inner_add_left]
  rw [inner_sub_left, inner_sub_left, inner_add_left]
  rw [inner_matVec_comm_of_isSymm M hM_symm x y]
  have h_cross' : inner ℝ (matVec M x) y = inner ℝ y (matVec M x) := by
    exact real_inner_comm y (matVec M x)
  have h_self : inner ℝ (matVec M x) x = inner ℝ x (matVec M x) := by
    exact real_inner_comm x (matVec M x)
  rw [h_cross', h_self]
  ring

lemma quad_min_implies_grad_nonneg
    (C b : ℝ) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → t * C + b ≥ 0) : b ≥ 0 := by
  by_contra h_neg
  push Not at h_neg
  by_cases hC : C ≤ 0
  · have h1 := h 1 (by norm_num) (by norm_num)
    linarith
  · push Not at hC
    let t := min 1 (-b / (2 * C))
    have ht1 : 0 < t := by
      apply lt_min (by norm_num)
      apply div_pos (neg_pos.mpr h_neg) (mul_pos (by norm_num) hC)
    have ht2 : t ≤ 1 := min_le_left _ _
    have h_eval := h t ht1 ht2
    have ht_le : t ≤ -b / (2 * C) := min_le_right _ _
    have h_eval2 : t * C + b ≤ (-b / (2 * C)) * C + b := by
      have : t * C ≤ (-b / (2 * C)) * C := mul_le_mul_of_nonneg_right ht_le (le_of_lt hC)
      linarith
    have h_cancel : (-b / (2 * C)) * C + b = b / 2 := by
      calc
        (-b / (2 * C)) * C + b = (-b / 2) * (C / C) + b := by ring
        _ = (-b / 2) * 1 + b := by rw [div_self (ne_of_gt hC)]
        _ = b / 2 := by ring
    linarith

lemma quad_min_implies_grad_nonneg'
    (C b : ℝ) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → t^2 * C + t * b ≥ 0) : b ≥ 0 := by
  have h' : ∀ t : ℝ, 0 < t → t ≤ 1 → t * C + b ≥ 0 := by
    intro t ht1 ht2
    have h_eval := h t ht1 ht2
    have : t * (t * C + b) ≥ 0 := by
      calc
        t * (t * C + b) = t^2 * C + t * b := by ring
        _ ≥ 0 := h_eval
    exact nonneg_of_mul_nonneg_right this ht1
  exact quad_min_implies_grad_nonneg C b h'

lemma quad_min_implies_grad_nonpos'
    (C b : ℝ) (h : ∀ t : ℝ, -1 ≤ t → t < 0 → t^2 * C + t * b ≥ 0) : b ≤ 0 := by
  have h_nonneg : -b ≥ 0 := by
    apply quad_min_implies_grad_nonneg' C (-b)
    intro u hu1 hu2
    have h_eval := h (-u) (by linarith) (by linarith)
    have : (-u)^2 * C + (-u) * b = u^2 * C + u * (-b) := by ring
    rw [←this]
    exact h_eval
  linarith

lemma matVec_smul' (M : Matrix ι ι ℝ) (c : ℝ) (x : EuclideanSpace ℝ ι) :
    matVec M (c • x) = c • matVec M x := by
  ext i
  have : c • x = euclideanOf (c • x.ofLp) := rfl
  rw [this]
  dsimp [matVec, PiLp.smul_apply, euclideanOf, Equiv.symm_apply_apply]
  change (M.mulVec (c • x.ofLp)) i = c * (M.mulVec x.ofLp) i
  rw [Matrix.mulVec_smul]
  rfl

lemma inner_single [DecidableEq ι] (v : EuclideanSpace ℝ ι) (i : ι) :
    inner ℝ v (euclideanOf (Pi.single i 1)) = v i := by
  dsimp [PiLp.inner_apply, euclideanOf, Equiv.symm_apply_apply]
  simp only [starRingEnd_apply, star_trivial]
  have h_sum : ∑ j : ι, (Pi.single i 1 : ι → ℝ) j * v.ofLp j =
      ∑ j : ι, if j = i then v.ofLp i else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = i
    · subst h
      rw [Pi.single_eq_same, if_pos rfl]
      ring
    · rw [Pi.single_eq_of_ne h, if_neg h]
      ring
  rw [h_sum]
  simp

lemma quadratic_expansion_eval (M : Matrix ι ι ℝ) (q x d : EuclideanSpace ℝ ι) (t : ℝ)
    (hM_symm : M.IsSymm) :
    ((1 / 2 : ℝ) * inner ℝ (x + t • d) (matVec M (x + t • d)) + inner ℝ q (x + t • d)) -
    ((1 / 2 : ℝ) * inner ℝ x (matVec M x) + inner ℝ q x) =
    t^2 * ((1 / 2 : ℝ) * inner ℝ d (matVec M d)) + t * inner ℝ (matVec M x + q) d := by
  have := quadratic_expansion M q x (x + t • d) hM_symm
  rw [this]
  have h_sub : (x + t • d) - x = t • d := add_sub_cancel_left x (t • d)
  rw [h_sub]
  rw [matVec_smul']
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
  ring

omit [Fintype ι] in
lemma nonnegative_add_t_single [DecidableEq ι] (x : EuclideanSpace ℝ ι) (hx : Nonnegative x)
    (i : ι) (t : ℝ) (ht : 0 ≤ t) :
    Nonnegative (x + t • euclideanOf (Pi.single i 1)) := by
  intro j
  dsimp [PiLp.add_apply, PiLp.smul_apply, euclideanOf, Equiv.symm_apply_apply]
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same]
    have hj := hx j
    linarith
  · rw [Pi.single_eq_of_ne h]
    have hj := hx j
    linarith

omit [Fintype ι] in
lemma nonnegative_add_t_self (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) (t : ℝ) (ht : -1 ≤ t) :
    Nonnegative (x + t • x) := by
  intro j
  dsimp [PiLp.add_apply, PiLp.smul_apply]
  have : x.ofLp j + t * x.ofLp j = (1 + t) * x.ofLp j := by ring
  rw [this]
  apply mul_nonneg (by linarith) (hx j)


/--
Proposition 4.8 from `docs/Lasso.md`: the primal-dual formulation of the
positive lasso is a linear complementarity problem.
An informal proof:
The positive lasso objective is a convex quadratic function on the nonnegative orthant.
The Lagrangian is `L(x, v) = (1/2) <x, Mx> + <q, x> - <v, x>`,
where `q = -r + (\lambda + 1/\mu) \mathbb{1}`.
The KKT conditions are necessary and sufficient:
- Stationarity: `0 = \nabla_x L = q + Mx - v`
- Primal feasibility: `x \ge 0`
- Dual feasibility: `v \ge 0`
- Complementary slackness: `<v, x> = 0`
This exactly matches the LCP formulation.
-/
lemma pos_lasso_is_lcp
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι)
    (hM_symm : M.IsSymm) (hM_psd : IsPositiveSemidefinite M) :
    IsPositiveLassoMinimizer M r lambda μ x ↔
    ∃ v : EuclideanSpace ℝ ι, isLCP M (lcpQ r lambda μ) x v := by
  haveI := Classical.decEq ι
  dsimp [IsPositiveLassoMinimizer, IsMinOn, isLCP]
  let q := lcpQ r lambda μ
  let f := positiveLassoObjective M r lambda μ
  let L := fun y => (1 / 2 : ℝ) * inner ℝ y (matVec M y) + inner ℝ q y
  have h_f_eq_L : ∀ y, Nonnegative y → f y = L y := by
    intro y hy
    exact positiveLassoObjective_eq M r lambda μ y hy
  constructor
  · intro ⟨hx_nonneg, h_min⟩
    let v := matVec M x + q
    use v
    have h_v : v = matVec M x + q := rfl
    have h_eval : ∀ y, Nonnegative y → L y - L x ≥ 0 := by
      intro y hy
      have : f x ≤ f y := h_min hy
      rw [← h_f_eq_L x hx_nonneg, ← h_f_eq_L y hy]
      linarith
    have hv_nonneg : Nonnegative v := by
      intro i
      let d := euclideanOf (Pi.single i 1 : ι → ℝ)
      have h_dir : ∀ t : ℝ, 0 < t → t ≤ 1 →
          t^2 * ((1 / 2 : ℝ) * inner ℝ d (matVec M d)) + t * v i ≥ 0 := by
        intro t ht1 ht2
        have hy_nonneg := nonnegative_add_t_single x hx_nonneg i t (le_of_lt ht1)
        have h_Leval := h_eval (x + t • d) hy_nonneg
        have h_exp := quadratic_expansion_eval M q x d t hM_symm
        have h_inner_d : inner ℝ v d = v i := inner_single v i
        dsimp [L] at h_Leval
        have h_v_eq : matVec M x + q = v := h_v.symm
        rw [h_v_eq] at h_exp
        rw [h_inner_d] at h_exp
        linarith
      exact quad_min_implies_grad_nonneg' ((1 / 2 : ℝ) * inner ℝ d (matVec M d)) (v i) h_dir
    have hvx_nonpos : inner ℝ v x ≤ 0 := by
      have h_dir : ∀ t : ℝ, -1 ≤ t → t < 0 →
          t^2 * ((1 / 2 : ℝ) * inner ℝ x (matVec M x)) + t * inner ℝ v x ≥ 0 := by
        intro t ht1 ht2
        have hy_nonneg := nonnegative_add_t_self x hx_nonneg t ht1
        have h_Leval := h_eval (x + t • x) hy_nonneg
        have h_exp := quadratic_expansion_eval M q x x t hM_symm
        dsimp [L] at h_Leval
        have h_v_eq : matVec M x + q = v := h_v.symm
        rw [h_v_eq] at h_exp
        linarith
      exact quad_min_implies_grad_nonpos' ((1 / 2 : ℝ) * inner ℝ x (matVec M x)) (inner ℝ v x) h_dir
    have hvx_nonneg : inner ℝ v x ≥ 0 := by
      have h_dir : ∀ t : ℝ, 0 < t → t ≤ 1 →
          t^2 * ((1 / 2 : ℝ) * inner ℝ x (matVec M x)) + t * inner ℝ v x ≥ 0 := by
        intro t ht1 ht2
        have hy_nonneg := nonnegative_add_t_self x hx_nonneg t (by linarith)
        have h_Leval := h_eval (x + t • x) hy_nonneg
        have h_exp := quadratic_expansion_eval M q x x t hM_symm
        dsimp [L] at h_Leval
        have h_v_eq : matVec M x + q = v := h_v.symm
        rw [h_v_eq] at h_exp
        linarith
      exact quad_min_implies_grad_nonneg' ((1 / 2 : ℝ) * inner ℝ x (matVec M x)) (inner ℝ v x) h_dir
    have hvx_zero : inner ℝ v x = 0 := by linarith
    have hv_eq_lcp : v = lcpQ r lambda μ + matVec M x := by
      rw [h_v]
      exact add_comm (matVec M x) (lcpQ r lambda μ)
    exact ⟨hv_eq_lcp, hv_nonneg, hx_nonneg, hvx_zero⟩
  · intro ⟨v, hv_eq, hv_nonneg, hx_nonneg, hvx_zero⟩
    refine ⟨hx_nonneg, ?_⟩
    intro y hy
    have h_f_y : f y = L y := positiveLassoObjective_eq M r lambda μ y hy
    have h_f_x : f x = L x := positiveLassoObjective_eq M r lambda μ x hx_nonneg
    change f x ≤ f y
    rw [h_f_x, h_f_y]
    have h_exp := quadratic_expansion M q x y hM_symm
    have h_v_sub : inner ℝ v (y - x) ≥ 0 := by
      have h_sub : inner ℝ v (y - x) = inner ℝ v y - inner ℝ v x := inner_sub_right v y x
      have h_sum : inner ℝ v y = ∑ i : ι, v.ofLp i * y.ofLp i := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Real.inner_apply]
      rw [h_sub, hvx_zero, sub_zero, h_sum]
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (hv_nonneg i) (hy i)
    have h_psd_eval : (1 / 2 : ℝ) * inner ℝ (y - x) (matVec M (y - x)) ≥ 0 := by
      have : inner ℝ (y - x) (matVec M (y - x)) ≥ 0 :=
        IsPositiveSemidefinite.get_nonneg hM_psd (y - x)
      linarith
    have h_L_sub : L y - L x =
        (1 / 2 : ℝ) * inner ℝ (y - x) (matVec M (y - x)) + inner ℝ v (y - x) := by
      dsimp [L]
      have : v = matVec M x + q := by
        rw [hv_eq]
        exact add_comm (lcpQ r lambda μ) (matVec M x)
      rw [this]
      exact h_exp
    linarith

/-- The parametric LCP (Eq 4.11 in docs/Lasso.md).
Defined for `w(μ) = μ v(μ)` and `z(μ) = μ x(μ)`. -/
def isParametricLCP
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (z w : EuclideanSpace ℝ ι) : Prop :=
  isLCP M (parametricLcpQ r lambda μ) z w

/--
Lemma 4.10 from `docs/Lasso.md`: For small `μ`, the parametric LCP has a unique solution.
An informal proof:
For `0 ≤ μ < 1 / max (‖r - λ𝟙‖∞, 1)`, the affine term
`q = (1 + μλ)𝟙 - μr` is strictly positive.
Setting `z = 0` and `w = q` satisfies the LCP equations.
Since `q > 0` and `M` is PSD, this is the unique solution: any nonzero
`z ≥ 0` would violate complementarity.
-/
lemma parametricLcpQ_pos
    (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hμ : 0 ≤ μ)
    (hμ_small : μ * ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ < 1) (i : ι) :
    0 < parametricLcpQ r lambda μ i := by
  have h_bound : |r i - lambda| ≤ ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ := by
    have h := PiLp.norm_apply_le ((WithLp.equiv ∞ _).symm (fun j => r j - lambda)) i
    have h_abs : ‖r i - lambda‖ = |r i - lambda| := Real.norm_eq_abs _
    rw [← h_abs]
    exact h
  have h_bound2 : μ * |r i - lambda| ≤ μ * ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ := by
    exact mul_le_mul_of_nonneg_left h_bound hμ
  have h_bound3 : μ * |r i - lambda| < 1 := by
    linarith [h_bound2, hμ_small]
  have h_le_abs : μ * (r i - lambda) ≤ μ * |r i - lambda| := by
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hμ
  have h_strict : μ * (r i - lambda) < 1 := by
    linarith [h_le_abs, h_bound3]
  have h_q_eq : parametricLcpQ r lambda μ i = -μ * r i + 1 + μ * lambda := rfl
  rw [h_q_eq]
  linarith

lemma parametric_lcp_unique_of_mul_supNorm_lt_one
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hM_psd : IsPositiveSemidefinite M)
    (hμ : 0 ≤ μ)
    (hμ_small : μ * ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ < 1) :
    ∃! p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      isParametricLCP M r lambda μ p.1 p.2 := by
  let q := parametricLcpQ r lambda μ
  have hq_pos : ∀ i, 0 < q i := parametricLcpQ_pos r lambda μ hμ hμ_small
  use (0, q)
  constructor
  · dsimp [isParametricLCP, isLCP]
    constructor
    · ext i
      simp [matVec, euclideanOf, q]
    · constructor
      · intro i
        exact le_of_lt (hq_pos i)
      · constructor
        · intro i
          exact le_refl 0
        · simp [inner_zero_right]
  · rintro ⟨z, w⟩ h_lcp
    dsimp [isParametricLCP, isLCP] at h_lcp
    rcases h_lcp with ⟨h_w, h_w_pos, h_z_pos, h_ortho⟩
    have h_inner_w_z : inner ℝ w z = 0 := h_ortho
    have h_w_eq : w = q + matVec M z := h_w
    have h_inner_sub : inner ℝ (q + matVec M z) z = 0 := by
      rw [←h_w_eq, h_inner_w_z]
    have h_inner_add : inner ℝ q z + inner ℝ (matVec M z) z = 0 := by
      rw [inner_add_left] at h_inner_sub
      exact h_inner_sub
    have hz_Mz_nonneg : 0 ≤ inner ℝ z (matVec M z) := IsPositiveSemidefinite.get_nonneg hM_psd z
    have h_Mz_z_eq : inner ℝ (matVec M z) z = inner ℝ z (matVec M z) := by
      exact real_inner_comm z (matVec M z)
    rw [h_Mz_z_eq] at h_inner_add
    have h_qz_nonpos : inner ℝ q z ≤ 0 := by linarith
    have h_qz_nonneg : 0 ≤ inner ℝ q z := by
      have h_sum : inner ℝ q z = ∑ i : ι, q.ofLp i * z.ofLp i := by
        rw [PiLp.inner_apply]
        simp only [Real.inner_apply]
      rw [h_sum]
      apply Finset.sum_nonneg
      intro i _
      have h1 : 0 ≤ q.ofLp i := le_of_lt (hq_pos i)
      have h2 : 0 ≤ z.ofLp i := h_z_pos i
      exact mul_nonneg (a := q.ofLp i) (b := z.ofLp i) h1 h2
    have h_qz_zero : inner ℝ q z = 0 := le_antisymm h_qz_nonpos h_qz_nonneg
    have h_z_zero : z = 0 := by
      ext i
      have h_sum_zero : ∑ j, q.ofLp j * z.ofLp j = 0 := by
        have h_sum : inner ℝ q z = ∑ j : ι, q.ofLp j * z.ofLp j := by
          rw [PiLp.inner_apply]
          simp only [Real.inner_apply]
        rw [←h_sum]
        exact h_qz_zero
      have h_term_zero : q.ofLp i * z.ofLp i = 0 := by
        have h_nonneg : ∀ j ∈ Finset.univ, 0 ≤ q.ofLp j * z.ofLp j := fun j _ =>
          mul_nonneg (a := q.ofLp j) (b := z.ofLp j) (le_of_lt (hq_pos j)) (h_z_pos j)
        exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_sum_zero i (Finset.mem_univ i)
      cases mul_eq_zero.mp h_term_zero with
      | inl h_q_zero =>
        have h_qi_pos : 0 < q.ofLp i := hq_pos i
        linarith
      | inr h_zi_zero =>
        have h_z_eq : z i = z.ofLp i := rfl
        rw [h_z_eq]
        exact h_zi_zero
    have h_w_eq_q : w = q := by
      rw [h_z_zero] at h_w_eq
      have h_zero : matVec M 0 = 0 := by
        ext j
        simp [matVec, euclideanOf]
      rw [h_zero] at h_w_eq
      simp only [add_zero] at h_w_eq
      exact h_w_eq
    rw [h_z_zero, h_w_eq_q]

omit [Fintype ι] in
/--
If `y` is in the cone of a linearly dependent family, it is in the cone of a strict subfamily.
Informal proof: Suppose `y = ∑_{i ∈ s} t_i a_i` with `t_i ≥ 0` and there exists
a nontrivial relation
`∑_{i ∈ s} c_i a_i = 0`. Without loss of generality, some `c_i > 0`.
Let `θ = \min_{c_i > 0} t_i / c_i`. Then `t_i' = t_i - θ c_i ≥ 0` for all `i`, and for the index
`k` where the minimum is achieved, `t_k' = 0`. Then `y = ∑_{i ∈ s \ {k}} t_i' a_i`, meaning
`y` is in the cone of a strict subfamily.
Source: docs/Lasso.md Section 4.3, Theorem 4.6.
-/
lemma mem_cone_erase {κ : Type*} [DecidableEq κ] (a : κ → EuclideanSpace ℝ ι)
    (s : Finset κ) (h_dep : ¬LinearIndependent ℝ (fun i : {i // i ∈ s} => a i))
    (y : EuclideanSpace ℝ ι) (hy : InCone (fun i : {i // i ∈ s} => a i) y) :
    ∃ k : s, InCone (fun i : {i // i ∈ s.erase k} => a i) y := by
  have h_dep2 := Fintype.not_linearIndependent_iff.mp h_dep
  rcases h_dep2 with ⟨c, hc_sum, ⟨i0, hc_i0_ne_zero⟩⟩
  have h_exists_pos : ∃ c' : {i // i ∈ s} → ℝ, (∑ i, c' i • a i) = 0 ∧ ∃ i0, c' i0 > 0 := by
    rcases lt_trichotomy (c i0) 0 with h | h | h
    · use fun i => - c i
      constructor
      · have : (∑ i, (-c i) • a i) = ∑ i, -(c i • a i) := by
          apply Finset.sum_congr rfl
          intro x _
          exact neg_smul (c x) (a ↑x)
        rw [this, Finset.sum_neg_distrib, hc_sum, neg_zero]
      · use i0
        linarith
    · contradiction
    · use c
      exact ⟨hc_sum, ⟨i0, h⟩⟩
  rcases h_exists_pos with ⟨c', hc'_sum, ⟨i0, hc'_i0_pos⟩⟩
  rcases hy with ⟨t, ht_nonneg, ht_sum⟩
  let S_pos := Finset.univ.filter (fun i : {i // i ∈ s} => c' i > 0)
  have hS_pos_nonempty : S_pos.Nonempty := ⟨i0, by simp [S_pos, hc'_i0_pos]⟩
  let θ_fn := fun i : {i // i ∈ s} => t i / c' i
  obtain ⟨k, hk_in, hk_min⟩ := Finset.exists_min_image S_pos θ_fn hS_pos_nonempty
  use k
  let t' := fun i : {i // i ∈ s} => t i - θ_fn k * c' i
  have ht'_nonneg : ∀ i, 0 ≤ t' i := by
    intro i
    dsimp [t']
    rcases lt_trichotomy (c' i) 0 with hc'_lt | hc'_eq | hc'_gt
    · have : θ_fn k ≥ 0 := by
        dsimp [θ_fn]
        apply div_nonneg (ht_nonneg k)
        rw [Finset.mem_filter] at hk_in
        exact le_of_lt hk_in.2
      have : θ_fn k * c' i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos this (le_of_lt hc'_lt)
      have ht_i_nonneg := ht_nonneg i
      linarith
    · rw [hc'_eq, mul_zero, sub_zero]
      exact ht_nonneg i
    · have hi_in : i ∈ S_pos := by
        simp [S_pos, hc'_gt]
      have h4 : θ_fn k ≤ t i / c' i := hk_min i hi_in
      have h5 : θ_fn k * c' i ≤ t i := (le_div_iff₀ hc'_gt).mp h4
      exact sub_nonneg.mpr h5
  have ht'_k_zero : t' k = 0 := by
    dsimp [t', θ_fn]
    have hk_gt : c' k > 0 := by
      rw [Finset.mem_filter] at hk_in
      exact hk_in.2
    have h_div : (t k / c' k) * c' k = t k := div_mul_cancel₀ (t k) (ne_of_gt hk_gt)
    exact sub_eq_zero.mpr h_div.symm
  let t'' := fun i : {i // i ∈ s.erase (k : κ)} => t' ⟨i.val, Finset.mem_of_mem_erase i.property⟩
  use t''
  constructor
  · intro i
    exact ht'_nonneg _
  · have h_sum_t' : (∑ i : {i // i ∈ s}, t' i • a i.val) = y := by
      have : ∀ i, t' i • a i.val = t i • a i.val - (θ_fn k) • (c' i • a i.val) := by
        intro i
        dsimp [t']
        rw [sub_smul, mul_smul]
      have h1 : (∑ i : {i // i ∈ s}, t' i • a i.val) =
          ∑ i : {i // i ∈ s}, (t i • a i.val - (θ_fn k) • (c' i • a i.val)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact this x
      rw [h1, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [hc'_sum, smul_zero, sub_zero]
      exact ht_sum
    have h_split : (∑ i : {i // i ∈ s}, t' i • a i.val) =
        t' k • a k.val + ∑ i ∈ Finset.univ.erase k, t' i • a i.val := by
      have := Finset.sum_erase_add (Finset.univ : Finset {i // i ∈ s})
        (fun i => t' i • a i.val) (Finset.mem_univ k)
      rw [←this]
      exact add_comm _ _
    have h_split2 : (∑ i : {i // i ∈ s}, t' i • a i.val) =
        ∑ i ∈ Finset.univ.erase k, t' i • a i.val := by
      rw [h_split, ht'_k_zero, zero_smul, zero_add]
    let e : {i // i ∈ s.erase (k : κ)} ≃ ((Finset.univ : Finset {i // i ∈ s}).erase k) := {
      toFun := fun i => ⟨⟨i.val, Finset.mem_of_mem_erase i.property⟩, by
        rw [Finset.mem_erase]
        have h1 := Finset.mem_erase.mp i.property
        refine ⟨?_, Finset.mem_univ _⟩
        intro h_eq
        apply h1.1
        exact Subtype.ext_iff.mp h_eq ⟩
      invFun := fun i => ⟨i.val.val, by
        rw [Finset.mem_erase]
        have h1 := Finset.mem_erase.mp i.property
        have hk_ne : i.val.val ≠ k.val := fun h_eq => h1.1 (Subtype.ext h_eq)
        exact ⟨hk_ne, i.val.property⟩ ⟩
      left_inv := fun i => by rfl
      right_inv := fun i => by rfl
    }
    have h_eq_sum : (∑ i : {i // i ∈ s.erase (k : κ)}, t'' i • a i.val) =
        ∑ i ∈ Finset.univ.erase k, t' i • a i.val := by
      have : (∑ i ∈ Finset.univ.erase k, t' i • a i.val) =
          ∑ i : ((Finset.univ : Finset {i // i ∈ s}).erase k), t' i.val • a i.val.val := by
        exact (Finset.sum_attach ((Finset.univ : Finset {i // i ∈ s}).erase k)
          (fun i => t' i • a i.val)).symm
      rw [this]
      exact Equiv.sum_comp e (fun i => t' i.val • a i.val.val)
    rw [h_eq_sum, ← h_split2]
    exact h_sum_t'

omit [Fintype ι] in
/--
Conic Caratheodory theorem API helper.
Given a point `y` in the cone of `a`, there exists a subset `s` of minimal cardinality such that
`y` is in the cone of `a` restricted to `s`.
Informal proof: The set of subsets `s` such that `y` is in the cone of `a|_s` is finite
and non-empty. Thus it has an element of minimal cardinality.
Source: Standard consequence of finite sets having a minimum size element.
See docs/Lasso.md Section 4.3.
-/
lemma minCardFinsetOfMemCone {κ : Type*} [Fintype κ] (a : κ → EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ ι) (hy : InCone a y) :
    ∃ s : Finset κ, InCone (fun i : {i // i ∈ s} => a i) y ∧
      ∀ s' : Finset κ, InCone (fun i : {i // i ∈ s'} => a i) y → s.card ≤ s'.card := by
  let P := fun s : Finset κ => InCone (fun i : {i // i ∈ s} => a i) y
  haveI : DecidablePred P := fun s => Classical.propDecidable (P s)
  let S := Finset.filter P Finset.univ
  have hS_nonempty : S.Nonempty := by
    use Finset.univ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with ⟨coeff, hcoeff_nonneg, hcoeff_sum⟩
    use fun i => coeff i.val
    constructor
    · intro i
      exact hcoeff_nonneg i.val
    · let e : {i // i ∈ (Finset.univ : Finset κ)} ≃ κ :=
        Equiv.subtypeUnivEquiv fun i => Finset.mem_univ i
      have h_eq : (∑ i : {i // i ∈ (Finset.univ : Finset κ)}, coeff i.val • a i.val) =
          ∑ i : κ, coeff (e.symm i).val • a (e.symm i).val := by
        exact (Equiv.sum_comp e.symm (fun i => coeff i • a i)).symm
      have h_eq2 : (∑ i : κ, coeff (e.symm i).val • a (e.symm i).val) =
          ∑ i : κ, coeff i • a i := by congr
      rw [h_eq, h_eq2]
      exact hcoeff_sum
  obtain ⟨s, hs_in, hs_min⟩ := Finset.exists_min_image S Finset.card hS_nonempty
  use s
  rw [Finset.mem_filter] at hs_in
  refine ⟨hs_in.2, ?_⟩
  intro s' hs'_in
  have hs'_in_S : s' ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ s', hs'_in⟩
  exact hs_min s' hs'_in_S

omit [Fintype ι] in
/--
The support of minimal cardinality for a point in a cone must be linearly independent.
Informal proof: If it were linearly dependent, by `mem_cone_erase`, we could find a
strictly smaller support `s \ {k}` whose cone still contains `y`. This contradicts the
minimality of the support's cardinality.
Source: docs/Lasso.md Section 4.3.
-/
lemma linearIndependent_of_minCardFinsetOfMemCone {κ : Type*}
    (a : κ → EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι) {s : Finset κ}
    (h_in : InCone (fun i : {i // i ∈ s} => a i) y)
    (h_min : ∀ s' : Finset κ, InCone (fun i : {i // i ∈ s'} => a i) y → s.card ≤ s'.card) :
    LinearIndependent ℝ (fun i : {i // i ∈ s} => a i) := by
  haveI : DecidableEq κ := Classical.decEq κ
  by_contra h_dep
  have h_exists := mem_cone_erase a s h_dep y h_in
  rcases h_exists with ⟨k, hk_in⟩
  have h_le := h_min (s.erase k.val) hk_in
  have h_lt : (s.erase k.val).card < s.card := by
    apply Finset.card_erase_lt_of_mem
    exact k.property
  linarith

/--
The dimension of Euclidean space is bounded by the cardinality of its index set.
Informal proof: EuclideanSpace is isomorphic to ℝ^ι, which has dimension |ι|.
Source: Basic linear algebra.
-/
lemma euclideanSpace_finrank_le : Module.finrank ℝ (EuclideanSpace ℝ ι) ≤ Fintype.card ι :=
  le_of_eq finrank_euclideanSpace

/--
Theorem 4.6 from `docs/Lasso.md` (conic Caratheodory theorem).

Informal proof reference: `docs/Lasso.md`, Section 4.3, Theorem 4.6.
Choose a representation of `y` using a support of minimal cardinality. If the
chosen family is linearly dependent, move along a nontrivial dependence until
one coefficient reaches zero while all coefficients remain nonnegative. This
removes one generator, contradicting minimality. Hence the support is linearly
independent and has cardinality at most the ambient dimension.
-/
theorem conic_caratheodory
    {κ : Type*} [Fintype κ] (a : κ → EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ ι) (hy : InCone a y) :
    ∃ s : Finset κ,
      s.card ≤ Fintype.card ι ∧
      LinearIndependent ℝ (fun i : {i // i ∈ s} => a i) ∧
      InCone (fun i : {i // i ∈ s} => a i) y := by
  haveI : DecidableEq κ := Classical.decEq κ
  obtain ⟨s, hs_in, hs_min⟩ := minCardFinsetOfMemCone a y hy
  have h_ind := linearIndependent_of_minCardFinsetOfMemCone a y hs_in hs_min
  use s
  refine ⟨?_, h_ind, hs_in⟩
  rw [← Fintype.card_coe s]
  exact le_trans (LinearIndependent.fintype_card_le_finrank h_ind)
    (euclideanSpace_finrank_le (ι := ι))

/--
For any linearly independent subfamily of columns, there is a constant $C$ bounding the norm of the
coefficients by the norm of the combination.
Informal proof: A linearly independent family of vectors defines an injective linear map. Since it's
between finite-dimensional spaces, it has a bounded left inverse. The norm of this left inverse
serves as the constant $C$.
Source: docs/Lasso.md Section 4.3.
-/
lemma linearIndependent_coefficient_bound {κ : Type*} (a : κ → EuclideanSpace ℝ ι)
    (s : Finset κ) (h_ind : LinearIndependent ℝ (fun i : {i // i ∈ s} => a i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : {i // i ∈ s} → ℝ,
      ‖euclideanOf x‖ ≤ C * ‖∑ i : {i // i ∈ s}, x i • a i‖ := by
  let f : EuclideanSpace ℝ {i // i ∈ s} →ₗ[ℝ] EuclideanSpace ℝ ι :=
    { toFun := fun x => ∑ i : {i // i ∈ s}, x i • a i
      map_add' := by
        intro x y
        ext i
        simp [Finset.sum_add_distrib, add_smul, PiLp.add_apply]
      map_smul' := by
        intro c x
        ext i
        simp [Finset.smul_sum, smul_smul, PiLp.smul_apply] }
  have h_ker : LinearMap.ker f = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y h
    ext i; exact ((Fintype.linearIndependent_iffₛ.mp h_ind) x y (by simpa [f] using h)) i
  have ⟨K, K_pos, hK⟩ := LinearMap.exists_antilipschitzWith f h_ker
  use K
  refine ⟨NNReal.coe_nonneg K, fun x => ?_⟩
  simpa [f, euclideanOf] using ZeroHomClass.bound_of_antilipschitz f hK (euclideanOf x)

/--
The maximum of the constants from `linearIndependent_coefficient_bound` over all linearly
independent subfamilies.
Informal proof: Since `Finset κ` is finite, we can take the maximum over the finite set of
linearly independent subfamilies.
Source: docs/Lasso.md Section 4.3.
-/
lemma max_linearIndependent_coefficient_bound {κ : Type*} [Finite κ] (a : κ → EuclideanSpace ℝ ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Finset κ, LinearIndependent ℝ (fun i : {i // i ∈ s} => a i) →
      ∀ x : {i // i ∈ s} → ℝ, (∀ i, 0 ≤ x i) →
        ‖euclideanOf x‖ ≤ C * ‖∑ i : {i // i ∈ s}, x i • a i‖ := by
  classical
  haveI : Fintype κ := Fintype.ofFinite κ
  -- Collect a constant for each subset s (or 0 if not linearly independent)
  let C_for_s (s : Finset κ) : ℝ :=
    if h : LinearIndependent ℝ (fun i : {i // i ∈ s} => a i) then
      Classical.choose (linearIndependent_coefficient_bound a s h)
    else 0
  have hC_bound (s : Finset κ) (h_ind : LinearIndependent ℝ (fun i : {i // i ∈ s} => a i))
      (x : {i // i ∈ s} → ℝ) : ‖euclideanOf x‖ ≤ C_for_s s * ‖∑ i : {i // i ∈ s}, x i • a i‖ := by
    dsimp [C_for_s]
    rw [dif_pos h_ind]
    exact (Classical.choose_spec (linearIndependent_coefficient_bound a s h_ind)).2 x
  -- Take the maximum of all C_for_s over all subsets (or 0 if empty, but univ is nonempty)
  let C := (Finset.univ : Finset (Finset κ)).fold max 0 C_for_s
  have hC_nonneg' : 0 ≤ C := by
    rw [Finset.le_fold_max]
    left; rfl
  have hC_s_le (s : Finset κ) : C_for_s s ≤ C := by
    rw [Finset.le_fold_max]
    right
    refine ⟨s, Finset.mem_univ _, ?_⟩
    rfl
  refine ⟨C, hC_nonneg', fun s h_ind x _ => ?_⟩
  exact (hC_bound s h_ind x).trans (mul_le_mul_of_nonneg_right (hC_s_le s) (norm_nonneg _))

open Classical in
lemma euclideanOf_norm_extend_by_zero {κ : Type*} [Fintype κ] (s : Finset κ)
    (x_s : {i // i ∈ s} → ℝ) :
    ‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖ = ‖euclideanOf x_s‖ := by
  have h1 : ‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖^2 =
      ∑ i, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (if h : i ∈ s then x_s ⟨i, h⟩ else 0) * (if h : i ∈ s then x_s ⟨i, h⟩ else 0) = _
    ring
  have h2 : (∑ i, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) =
      ∑ i : {x // x ∈ s}, (x_s i)^2 := by
    have h_split : (∑ i, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) =
        (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) +
        (∑ i ∈ sᶜ, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) := (Finset.sum_add_sum_compl s _).symm
    rw [h_split]
    have h_s : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) =
        ∑ i : {x // x ∈ s}, (x_s i)^2 := by
      have h_eq : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) =
          ∑ i : {x // x ∈ s}, (if h : i.val ∈ s then x_s ⟨i.val, h⟩ else 0)^2 :=
            (Finset.sum_attach s _).symm
      rw [h_eq]
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.val ∈ s := i.property
      rw [dif_pos hi]
    have h_sc : (∑ i ∈ sᶜ, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_compl] at hi
      rw [dif_neg hi]
      ring
    rw [h_s, h_sc, add_zero]
  have h3 : ‖euclideanOf x_s‖^2 = ∑ i : {x // x ∈ s}, (x_s i)^2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change x_s i * x_s i = _
    ring
  have h_sq_eq : ‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖^2 =
      ‖euclideanOf x_s‖^2 := by
    rw [h1, h2, ←h3]
  have h_norm_nonneg1 : 0 ≤ ‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖ :=
    norm_nonneg _
  have h_norm_nonneg2 : 0 ≤ ‖euclideanOf x_s‖ := norm_nonneg _
  have h_sqrt : Real.sqrt (‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖^2) =
      Real.sqrt (‖euclideanOf x_s‖^2) := by
    rw [h_sq_eq]
  rw [Real.sqrt_sq h_norm_nonneg1, Real.sqrt_sq h_norm_nonneg2] at h_sqrt
  exact h_sqrt

open Classical in
omit [Fintype ι] in
lemma sum_extend_by_zero {κ : Type*} [Fintype κ] (s : Finset κ)
    (x_s : {i // i ∈ s} → ℝ) (a : κ → EuclideanSpace ℝ ι) :
    (∑ i, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) = ∑ i : {i // i ∈ s}, x_s i • a i.val := by
  have h_split : (∑ i, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) =
      (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) +
      (∑ i ∈ sᶜ, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) := (Finset.sum_add_sum_compl s _).symm
  rw [h_split]
  have h_s : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) =
      ∑ i : {x // x ∈ s}, x_s i • a i.val := by
    have h_eq : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) =
        ∑ i : {x // x ∈ s}, (if h : i.val ∈ s then x_s ⟨i.val, h⟩ else 0) • a i.val :=
          (Finset.sum_attach s _).symm
    rw [h_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val ∈ s := i.property
    rw [dif_pos hi]
  have h_sc : (∑ i ∈ sᶜ, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_compl] at hi
    rw [dif_neg hi]
    exact zero_smul ℝ (a i)
  rw [h_s, h_sc, add_zero]

open Classical in
/--
Lemma 4.7 from `docs/Lasso.md`: a feasible nonnegative linear system has a
nonnegative solution with norm controlled by the right-hand side.

Informal proof reference: `docs/Lasso.md`, Section 4.3, Lemma 4.7.
Apply `conic_caratheodory` to express `y` using a linearly independent subfamily
of columns. On that subfamily the matrix has full column rank, so the coefficient
vector is controlled by the operator norm of the pseudo-inverse. Taking the
maximum over finitely many subfamilies gives the constant.
-/
theorem nonnegative_solution_norm_bound
    {κ : Type*} [Fintype κ] (a : κ → EuclideanSpace ℝ ι) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : EuclideanSpace ℝ ι, InCone a y →
        ∃ x : κ → ℝ,
          (∀ i, 0 ≤ x i) ∧ (∑ i, x i • a i) = y ∧
            ‖euclideanOf x‖ ≤ C * ‖y‖ := by
  have hC := max_linearIndependent_coefficient_bound a
  rcases hC with ⟨C, hC0, hC_bound⟩
  use C
  constructor
  · exact hC0
  · intro y hy
    have h_cara := conic_caratheodory a y hy
    rcases h_cara with ⟨s, _hcard, h_linindep, h_incone⟩
    rcases h_incone with ⟨x_s, hx_s_nonneg, hx_s_sum⟩
    let x : κ → ℝ := fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0
    use x
    have h_nonneg : ∀ i, 0 ≤ x i := by
      intro i
      dsimp [x]
      split_ifs
      · exact hx_s_nonneg _
      · rfl
    have h_sum : (∑ i, x i • a i) = y := by
      have h_sum_ext := sum_extend_by_zero s x_s a
      rw [h_sum_ext]
      exact hx_s_sum
    have h_norm : ‖euclideanOf x‖ ≤ C * ‖y‖ := by
      have h_norm_eq := euclideanOf_norm_extend_by_zero s x_s
      rw [h_norm_eq]
      have h_bound := hC_bound s h_linindep x_s hx_s_nonneg
      rw [hx_s_sum] at h_bound
      exact h_bound
    exact ⟨h_nonneg, h_sum, h_norm⟩

/-- A minimum-Euclidean-norm solution of the nonnegative linear fiber.

The membership conjunct is part of the predicate: `IsMinOn` by itself does not
assert that its proposed minimizer belongs to the set.
-/
def IsNonnegativeMinNormSolution {κ : Type*} [Fintype κ]
    (a : κ → EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι) (x : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i, x i • a i) = y ∧
    IsMinOn (fun z : κ → ℝ => ‖euclideanOf z‖)
      {z | (∀ i, 0 ≤ z i) ∧ (∑ i, z i • a i) = y} x

/-- Faithful argmin form of Lemma 4.7.

For each feasible `y`, the closed convex nonnegative fiber has a unique
minimum-norm point.  Conic Carathéodory gives a linearly independent active
subfamily and therefore one feasible point bounded by `C ‖y‖`; minimality
transfers this bound to the argmin.  Uniqueness follows by minimizing the
strictly convex squared Euclidean norm on a convex set.  This is the proof in
Lemma 4.7 of <https://arxiv.org/abs/2509.18766>, cross-checked against the
conic Carathéodory argument in Bertsekas' MIT convex-analysis slides
<https://web.mit.edu/dimitrib/OldFiles/www/Convex_Slides.pdf>.
-/
-- If two vectors in an inner product space have equal norm and are distinct,
-- then their midpoint has strictly smaller norm (strict convexity of the norm).
private lemma strict_convex_norm_midpoint_lt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {u v : V}
    (h_norm_eq : ‖u‖ = ‖v‖) (h_ne : u ≠ v) : ‖(1/2 : ℝ) • (u + v)‖ < ‖u‖ := by
  have h_sub_pos : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h_ne)
  have h_sub_sq_pos : 0 < ‖u - v‖ ^ 2 := pow_pos h_sub_pos 2
  rw [norm_sub_sq_real, h_norm_eq] at h_sub_sq_pos
  have h_sum_sq_lt : ‖u + v‖ ^ 2 < (2 * ‖u‖) ^ 2 := by
    rw [norm_add_sq_real, h_norm_eq]
    nlinarith
  have h_sum_lt : ‖u + v‖ < 2 * ‖u‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp h_sum_sq_lt
  calc
    ‖(1/2 : ℝ) • (u + v)‖ = (1/2 : ℝ) * ‖u + v‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
    _ < (1/2 : ℝ) * (2 * ‖u‖) := mul_lt_mul_of_pos_left h_sum_lt (by norm_num)
    _ = ‖u‖ := by ring

-- The feasible set of nonnegative solutions to ∑ z_i a_i = y is closed.
private lemma feasible_set_closed {κ : Type*} [Fintype κ]
    {V : Type*} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (a : κ → V) (y : V) :
    IsClosed {z : κ → ℝ | (∀ i, 0 ≤ z i) ∧ (∑ i, z i • a i) = y} := by
  have h_closed_nonneg : IsClosed {z : κ → ℝ | ∀ i, 0 ≤ z i} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_Ici.preimage (continuous_apply i)
  have h_closed_sum : IsClosed {z : κ → ℝ | (∑ i, z i • a i) = y} :=
    (isClosed_singleton).preimage
      (continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).smul continuous_const)
  exact IsClosed.inter h_closed_nonneg h_closed_sum

-- The feasible set of nonnegative solutions to ∑ z_i a_i = y is convex.
private lemma feasible_set_convex {κ : Type*} [Fintype κ]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : κ → V) (y : V) :
    Convex ℝ {z : κ → ℝ | (∀ i, 0 ≤ z i) ∧ (∑ i, z i • a i) = y} := by
  intro z₁ hz₁ z₂ hz₂ s t hs ht hst
  rcases hz₁ with ⟨hz₁_nonneg, hz₁_sum⟩
  rcases hz₂ with ⟨hz₂_nonneg, hz₂_sum⟩
  constructor
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hs, ht, hz₁_nonneg i, hz₂_nonneg i]
  · have hsum : (∑ i : κ, (s • z₁ + t • z₂) i • a i) = y := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ i, (s * z₁ i + t * z₂ i) • a i) = (∑ i, ((s * z₁ i) • a i + (t * z₂ i) • a i)) := by
          simp [add_smul]
        _ = (∑ i, (s * z₁ i) • a i) + (∑ i, (t * z₂ i) • a i) := Finset.sum_add_distrib
        _ = s • (∑ i, z₁ i • a i) + t • (∑ i, z₂ i • a i) := by
          simp [Finset.smul_sum, smul_smul]
        _ = s • y + t • y := by rw [hz₁_sum, hz₂_sum]
        _ = (s + t) • y := by rw [add_smul]
        _ = y := by rw [hst, one_smul]
    exact hsum

theorem nonnegative_minNorm_solution_norm_bound
    {κ : Type*} [Fintype κ] (a : κ → EuclideanSpace ℝ ι) :
    ∃ C : ℝ, 0 < C ∧
      ∀ y : EuclideanSpace ℝ ι, InCone a y →
        ∃ x : κ → ℝ,
          IsNonnegativeMinNormSolution a y x ∧
          (∀ x', IsNonnegativeMinNormSolution a y x' → x' = x) ∧
          ‖euclideanOf x‖ ≤ C * ‖y‖ := by
  rcases nonnegative_solution_norm_bound a with ⟨C₀, _, hC₀⟩
  set C := max C₀ 1 with hC_def
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro y hy
  set S : Set (κ → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ (∑ i, z i • a i) = y} with hS_def
  have hS_nonempty : S.Nonempty := by
    rcases hy with ⟨coeff, hcoeff_nonneg, hcoeff_sum⟩
    exact ⟨coeff, by rw [hS_def]; exact ⟨hcoeff_nonneg, hcoeff_sum⟩⟩
  have hS_closed : IsClosed S := hS_def ▸ feasible_set_closed a y
  have hS_convex : Convex ℝ S := hS_def ▸ feasible_set_convex a y
  set f : (κ → ℝ) → ℝ := fun z => ‖euclideanOf z‖
  have hf_cont : Continuous f := by
    dsimp [f]
    exact Continuous.norm (by
      unfold euclideanOf EuclideanSpace PiLp
      exact PiLp.continuous_toLp (p := 2) (β := fun _ : κ => ℝ))
  -- Existence of a minimizer: use compactness of the sublevel set
  have h_exists : ∃ x ∈ S, IsMinOn f S x := by
    obtain ⟨x₀, hx₀S⟩ := hS_nonempty
    set M : ℝ := f x₀
    let K : Set (κ → ℝ) := {z | z ∈ S ∧ f z ≤ M}
    have hK_closed : IsClosed K :=
      IsClosed.inter hS_closed ((isClosed_Iic (a := M)).preimage hf_cont)
    have hK_compact : IsCompact K := by
      haveI : FiniteDimensional ℝ (EuclideanSpace ℝ κ) :=
        ((EuclideanSpace.equiv κ ℝ).symm.toLinearEquiv).finiteDimensional
      let φ := EuclideanSpace.equiv κ ℝ
      have h_image_compact : IsCompact (φ '' Metric.closedBall (0 : EuclideanSpace ℝ κ) M) :=
        (isCompact_closedBall (0 : EuclideanSpace ℝ κ) M).image φ.continuous
      have h_image_eq : φ '' Metric.closedBall (0 : EuclideanSpace ℝ κ) M =
          {z : κ → ℝ | ‖euclideanOf z‖ ≤ M} := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [Metric.mem_closedBall] at hw
          have h_eq : euclideanOf (φ w) = w := by
            dsimp [euclideanOf, φ, EuclideanSpace, PiLp]; rfl
          simpa [h_eq] using hw
        · intro hz
          refine ⟨euclideanOf z, ?_, rfl⟩
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
          exact hz
      rw [h_image_eq] at h_image_compact
      have hK_sub : K ⊆ {z : κ → ℝ | ‖euclideanOf z‖ ≤ M} := by
        rintro z ⟨_, hzf⟩
        dsimp [f] at hzf
        exact hzf
      exact h_image_compact.of_isClosed_subset hK_closed hK_sub
    have hK_nonempty : K.Nonempty := ⟨x₀, hx₀S, le_refl _⟩
    obtain ⟨x, hxK, hx_min⟩ := hK_compact.exists_isMinOn hK_nonempty hf_cont.continuousOn
    refine ⟨x, hxK.1, ?_⟩
    intro z hzS
    by_cases hzM : f z ≤ f x₀
    · apply hx_min ⟨hzS, hzM⟩
    · exact le_trans hxK.2 (le_of_lt (not_le.mp hzM))
  rcases h_exists with ⟨x, hxS, hx_min⟩
  -- Uniqueness of the minimizer
  have h_unique : ∀ x', IsNonnegativeMinNormSolution a y x' → x' = x := by
    intro x' hx'_sol
    rcases hx'_sol with ⟨hx'_nonneg, hx'_sum, hx'_min⟩
    by_contra h_ne
    have hx'S_set : x' ∈ S := by
      rw [hS_def]
      exact ⟨hx'_nonneg, hx'_sum⟩
    set mid := (1/2 : ℝ) • x + (1/2 : ℝ) • x'
    have h_mid_mem : mid ∈ S :=
      hS_convex hxS hx'S_set (by norm_num) (by norm_num) (by norm_num)
    have h_norm_mid : f mid < f x := by
      dsimp [f, mid]
      have h_norm_eq : ‖euclideanOf x‖ = ‖euclideanOf x'‖ :=
        le_antisymm (by simpa [f] using hx_min hx'S_set) (by simpa [f] using hx'_min hxS)
      have h_uv_ne : euclideanOf x ≠ euclideanOf x' :=
        fun h => h_ne (((WithLp.equiv 2 (κ → ℝ)).symm.injective h).symm)
      rw [show euclideanOf ((1/2 : ℝ) • x + (1/2 : ℝ) • x') =
          (1/2 : ℝ) • (euclideanOf x + euclideanOf x') by simp [euclideanOf]]
      exact strict_convex_norm_midpoint_lt h_norm_eq h_uv_ne
    have h_min_mid : f x ≤ f mid := hx_min h_mid_mem
    linarith
  have h_norm_bound : ‖euclideanOf x‖ ≤ C * ‖y‖ := by
    rcases hC₀ y hy with ⟨x₀, hx₀_nonneg, hx₀_sum, hx₀_norm⟩
    have hfx_le : ‖euclideanOf x‖ ≤ ‖euclideanOf x₀‖ :=
      by simpa [f] using hx_min (by rw [hS_def]; exact ⟨hx₀_nonneg, hx₀_sum⟩)
    have hC_le : C₀ ≤ C := hC_def ▸ le_max_left _ _
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith [hfx_le, hx₀_norm, mul_le_mul_of_nonneg_right hC_le hy_nonneg]
  rcases hxS with ⟨hx_nonneg, hx_sum⟩
  exact ⟨x, ⟨hx_nonneg, hx_sum, hx_min⟩, h_unique, h_norm_bound⟩

/--
The positive lasso objective achieves its minimum on the non-negative orthant.
Informal proof: The positive lasso objective is a convex quadratic function. Since the problem data
$r$ is in the span of $M$, the objective is bounded below. By the Frank-Wolfe theorem for quadratic
programming, a convex quadratic function bounded below on a polyhedron achieves its minimum.
Source: docs/Lasso.md Section 4.4, Proposition 4.9.
-/
-- For nonnegative vectors, ‖x‖₂ ≤ ‖x‖₁ (the standard inequality for Euclidean norms).
private lemma norm_le_sum_of_nonnegative
    (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) : ‖x‖ ≤ ∑ i, x i := by
  have hsq : ‖x‖ ^ 2 ≤ (∑ i, x i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hterm : ∀ i, (x i)^2 ≤ (x i) * ∑ j, x j := by
      intro i
      calc
        (x i)^2 = (x i) * (x i) := sq _
        _ ≤ (x i) * ∑ j, x j := mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)) (hx i)
    calc
      (∑ i, (x i)^2) ≤ ∑ i, (x i) * ∑ j, x j := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (∑ i, x i) * (∑ j, x j) := by rw [← Finset.sum_mul]
      _ = (∑ i, x i) ^ 2 := by ring
  have h_sqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (Finset.sum_nonneg (fun i _ => hx i))] at h_sqrt

-- Key lower bound for the positive lasso objective on the nonnegative orthant.
-- Uses completing the square and PSD property of M.
private lemma positive_lasso_lower_bound
    (M : Matrix ι ι ℝ) (r y : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hM_symm : M.IsSymm) (hy : matVec M y = r) (hM_nonneg : ∀ x, 0 ≤ inner ℝ x (matVec M x))
    (hlambda_nonneg : 0 ≤ lambda) (hμ_pos : 0 < μ)
    (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) :
    (-(1/2) * inner ℝ y (matVec M y)) + (lambda + 1/μ) * ‖x‖ ≤
    positiveLassoObjective M r lambda μ x := by
  set α := lambda + 1/μ with hα_def
  set C := -(1/2) * inner ℝ y (matVec M y) with hC_def
  have h_alpha_nonneg : 0 ≤ α := by
    have h_inv_pos : 0 < 1/μ := div_pos (by linarith) hμ_pos
    dsimp [α, hα_def]
    linarith
  have h_quad : quadraticLoss M r x =
      (1/2) * inner ℝ (x - y) (matVec M (x - y)) - (1/2) * inner ℝ y (matVec M y) := by
    linarith [quadraticLoss_complete_square M r x y hM_symm hy]
  -- Expand the objective: positiveLassoObjective = quadraticLoss + α * ‖x‖₁
  have h_obj : positiveLassoObjective M r lambda μ x =
      quadraticLoss M r x + α * ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖ := by
    dsimp [positiveLassoObjective, lassoObjective, α, hα_def]
  rw [h_obj, h_quad]
  -- Replace the L1 norm with inner ℝ ones x
  have h_norm1 : ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖ = inner ℝ ones x :=
    norm_one_eq_inner_ones_of_nonnegative x hx
  rw [h_norm1]
  -- For nonnegative x, ‖x‖ ≤ inner ones x
  have h_inner_nonneg : ‖x‖ ≤ inner ℝ ones x := by
    simpa [ones, euclideanOf, EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using
      norm_le_sum_of_nonnegative x hx
  -- Goal: C + α*‖x‖ ≤ (1/2)*P - (1/2)*inner_y + α*inner
  -- i.e., C + α*‖x‖ ≤ (1/2)*P + C + α*inner
  -- Cancel C: α*‖x‖ ≤ (1/2)*P + α*inner
  -- Since α ≥ 0, P ≥ 0, and ‖x‖ ≤ inner, the inequality holds.
  nlinarith [h_alpha_nonneg, h_inner_nonneg, hM_nonneg (x - y)]

lemma pos_lasso_achieves_minimum
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hdata : ProblemData M r lambda) (hμ : 0 < μ) :
    ∃ x : EuclideanSpace ℝ ι, IsPositiveLassoMinimizer M r lambda μ x := by
  rcases hdata with ⟨hpsd, hr_span, hlambda_nonneg⟩
  rcases hr_span with ⟨y, hy⟩
  have hM_symm : M.IsSymm := hpsd.symm
  have hM_nonneg : ∀ x, 0 ≤ inner ℝ x (matVec M x) := hpsd.nonneg
  set f := positiveLassoObjective M r lambda μ
  set s := {x : EuclideanSpace ℝ ι | Nonnegative x} with hs_def
  -- f(0) = 0
  have h_f_zero : f 0 = 0 := by
    simp [f, positiveLassoObjective, lassoObjective, quadraticLoss]
  -- The penalty coefficient is strictly positive
  have h_alpha_pos : 0 < lambda + 1/μ := by
    have h_inv_pos : 0 < 1/μ := div_pos (by linarith) hμ
    linarith
  set α := lambda + 1/μ with hα_def
  -- The constant from completing the square: C = -(1/2) yᵀ M y ≤ 0
  set C := -(1/2) * inner ℝ y (matVec M y) with hC_def
  -- Key bound: for nonnegative x, f(x) ≥ C + α * ‖x‖ (extracted as helper)
  have h_bound (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) : C + α * ‖x‖ ≤ f x := by
    dsimp [C, α, f, hC_def, hα_def]
    exact positive_lasso_lower_bound M r y lambda μ hM_symm hy hM_nonneg
      hlambda_nonneg hμ x hx
  -- The nonnegative orthant is closed
  have h_closed : IsClosed s := by
    dsimp [s, hs_def]
    rw [show {x : EuclideanSpace ℝ ι | Nonnegative x} = ⋂ (i : ι), {x | 0 ≤ x i} by
      ext x; simp [Nonnegative]]
    refine isClosed_iInter fun i =>
      (isClosed_Ici (a := (0 : ℝ))).preimage
        (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i)
  -- 0 is in the nonnegative orthant
  have h_zero_mem_s : (0 : EuclideanSpace ℝ ι) ∈ s := by
    simp [hs_def, Nonnegative]
  -- matVec M is linear, hence continuous (finite-dimensional domain)
  have h_cont_matVec : Continuous (matVec M) := by
    let M_lin : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
      { toFun := matVec M
        map_add' := matVec_add M
        map_smul' := matVec_smul_eq M }
    exact M_lin.continuous_of_finiteDimensional
  -- f is continuous everywhere, hence continuous on s
  have h_cont_f : Continuous f := by
    dsimp [f, positiveLassoObjective, lassoObjective, quadraticLoss]
    -- f = (fun x => (1/2) * inner ℝ x (matVec M x) - inner ℝ r x)
    --   + (fun x => α * ‖(L1.equiv).symm x‖)
    refine Continuous.add ?_ ?_
    · -- quadraticLoss part
      refine Continuous.sub ?_ ?_
      · -- (1/2) * inner ℝ x (matVec M x)
        refine Continuous.const_mul ?_ (1/2)
        -- inner ℝ x (matVec M x) is continuous
        exact Continuous.inner continuous_id h_cont_matVec
      · -- inner ℝ r x is continuous
        exact Continuous.inner continuous_const continuous_id
    · -- α * ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖ is continuous
      refine Continuous.const_mul ?_ α
      -- The L1 norm composed with the equivalence is continuous
      refine Continuous.comp ?_ ?_
      · exact continuous_norm
      · continuity
  have h_cont_on : ContinuousOn f s := h_cont_f.continuousOn
  -- Cocontractivity: outside a large enough closed ball, f(x) ≥ f(0) = 0
  set R := (-C) / α + 1 with hR_def
  have h_mem_cocompact :
      ∀ᶠ x in Filter.cocompact (EuclideanSpace ℝ ι) ⊓ Filter.principal s, f 0 ≤ f x := by
    rw [Filter.eventually_inf_principal]
    -- Need: ∀ᶠ x in cocompact, x ∈ s → f 0 ≤ f x
    -- Take K = closedBall 0 R, which is compact
    let K := Metric.closedBall (0 : EuclideanSpace ℝ ι) R
    have hK_compl : Kᶜ ∈ Filter.cocompact (EuclideanSpace ℝ ι) :=
      (isCompact_closedBall _ _).compl_mem_cocompact
    -- For x outside K and in s, we have f 0 ≤ f x
    have h_out : ∀ x, x ∈ s → x ∉ K → f 0 ≤ f x := by
      intro x hx_s hx_not_K
      rw [h_f_zero]
      have hx_norm_gt_R : R < ‖x‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx_not_K
        -- hx_not_K is ¬(‖x‖ ≤ R)
        linarith
      have h_pos : 0 < C + α * ‖x‖ := by
        have h_div_lt : (-C)/α < ‖x‖ := by linarith
        have h_mul : -C < α * ‖x‖ := by
          simpa [mul_comm] using (div_lt_iff₀ h_alpha_pos).mp h_div_lt
        linarith
      linarith [h_bound x hx_s, h_pos]
    -- Use filter_upwards to combine: hK_compl gives "x ∉ K", and we restrict to s
    filter_upwards [hK_compl] with x hx_not_K hx_s
    exact h_out x hx_s hx_not_K
  -- Apply the extreme value theorem: ContinuousOn.exists_isMinOn'
  rcases ContinuousOn.exists_isMinOn' h_cont_on h_closed h_zero_mem_s h_mem_cocompact with
    ⟨x, hx_s, h_min⟩
  exact ⟨x, hx_s, h_min⟩

/-- Inner product of two nonnegative vectors is nonnegative. -/
lemma inner_nonneg_of_nonnegative
    {a b : EuclideanSpace ℝ ι} (ha : Nonnegative a) (hb : Nonnegative b) :
    0 ≤ inner ℝ a b := by
  rw [PiLp.inner_apply]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [Real.inner_apply]
  exact mul_nonneg (ha i) (hb i)

/-- If M is PSD and ⟨d, M d⟩ = 0, then M d = 0.
Proof: For any z, PSD implies 0 ≤ ⟨d + t·z, M(d + t·z)⟩ = 2t·⟨d, M z⟩ + t²·⟨z, M z⟩
(since ⟨d, M d⟩ = 0). This quadratic in t is ≥ 0 for all t, forcing the linear term
coefficient ⟨d, M z⟩ = 0. Taking z = M d and using symmetry gives ‖M d‖² = 0. -/
lemma psd_zero_quadratic_imp_zero
    (M : Matrix ι ι ℝ) (hM_psd : IsPositiveSemidefinite M) (d : EuclideanSpace ℝ ι)
    (h_zero : inner ℝ d (matVec M d) = 0) : matVec M d = 0 := by
  -- Expansion of the quadratic form
  have h_expand (z : EuclideanSpace ℝ ι) (t : ℝ) :
      inner ℝ (d + t • z) (matVec M (d + t • z)) =
      inner ℝ d (matVec M d) + 2 * t * inner ℝ d (matVec M z) + t ^ 2 * inner ℝ z (matVec M z) := by
    rw [matVec_add, matVec_smul_eq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      add_assoc, mul_assoc,
      inner_matVec_comm_of_isSymm M hM_psd.symm d z]
    rw [real_inner_comm z (matVec M d)]
    ring
  -- From PSD, the quadratic form is nonnegative for all choices of z and t
  have h_psd_quad (z : EuclideanSpace ℝ ι) (t : ℝ) : 0 ≤
      inner ℝ d (matVec M d) + 2 * t * inner ℝ d (matVec M z) + t ^ 2 * inner ℝ z (matVec M z) := by
    rw [← h_expand z t]
    exact hM_psd.nonneg (d + t • z)
  -- Simplify using h_zero
  have h_quad_simp (z : EuclideanSpace ℝ ι) (t : ℝ) :
      0 ≤ 2 * t * inner ℝ d (matVec M z) + t ^ 2 * inner ℝ z (matVec M z) := by
    have h := h_psd_quad z t
    rw [h_zero] at h
    simpa [add_zero] using h
  -- Lemma: for any z, inner ℝ d (matVec M z) ≥ 0
  have h_inner_nonneg (z : EuclideanSpace ℝ ι) : 0 ≤ inner ℝ d (matVec M z) := by
    have h_cond : ∀ t : ℝ, 0 < t → t ≤ 1 →
        t ^ 2 * (inner ℝ z (matVec M z)) + t * (2 * inner ℝ d (matVec M z)) ≥ 0 := by
      intro t ht_pos ht_le
      have h := h_quad_simp z t
      simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h
    have hb : 2 * inner ℝ d (matVec M z) ≥ 0 :=
      quad_min_implies_grad_nonneg' (inner ℝ z (matVec M z)) (2 * inner ℝ d (matVec M z)) h_cond
    linarith
  -- Lemma: for any z, inner ℝ d (matVec M z) = 0 (apply nonneg to both z and -z)
  have h_zero_inner (z : EuclideanSpace ℝ ι) : inner ℝ d (matVec M z) = 0 := by
    have h_nonneg := h_inner_nonneg z
    have h_nonpos : inner ℝ d (matVec M z) ≤ 0 := by
      have h_neg := h_inner_nonneg (-z)
      have h_matvec_neg : matVec M (-z) = -(matVec M z) := by
        simpa using (matVec_smul_eq M (-1) z)
      rw [h_matvec_neg] at h_neg
      rw [inner_neg_right] at h_neg
      linarith
    linarith
  -- Take z = matVec M d, use symmetry to get ‖matVec M d‖² = 0
  have h_norm_zero : inner ℝ (matVec M d) (matVec M d) = 0 := by
    rw [← h_zero_inner (matVec M d), inner_matVec_comm_of_isSymm M hM_psd.symm d (matVec M d)]
  rw [inner_self_eq_zero] at h_norm_zero
  exact h_norm_zero

-- For two LCP solutions, complementarity and nonnegativity force
-- ⟨v' - v, x' - x⟩ ≤ 0. This is the key inequality used in uniqueness proofs.
private lemma lcp_inner_diff_nonpos
    (v v' x x' : EuclideanSpace ℝ ι)
    (hv_nonneg : Nonnegative v) (hv'_nonneg : Nonnegative v')
    (hx_nonneg : Nonnegative x) (hx'_nonneg : Nonnegative x')
    (h_comp1 : inner ℝ v x = 0) (h_comp2 : inner ℝ v' x' = 0) :
    inner ℝ (v' - v) (x' - x) ≤ 0 := by
  simp [inner_sub_left, inner_sub_right, h_comp1, h_comp2]
  linarith [inner_nonneg_of_nonnegative hv'_nonneg hx_nonneg,
    inner_nonneg_of_nonnegative hv_nonneg hx'_nonneg]

lemma psd_lcp_unique_dual
    (M : Matrix ι ι ℝ) (hM_psd : IsPositiveSemidefinite M) (q : EuclideanSpace ℝ ι)
    (x x' v v' : EuclideanSpace ℝ ι)
    (h1 : isLCP M q x v) (h2 : isLCP M q x' v') :
    v = v' := by
  rcases h1 with ⟨hv_eq, hv_nonneg, hx_nonneg, h_comp1⟩
  rcases h2 with ⟨hv'_eq, hv'_nonneg, hx'_nonneg, h_comp2⟩
  set d := x' - x
  have h_diff_eq : v' - v = matVec M d := by
    rw [hv_eq, hv'_eq, matVec_sub]; abel_nf
  have h_quad_zero : inner ℝ d (matVec M d) = 0 := by
    have h_nonneg : 0 ≤ inner ℝ d (matVec M d) := hM_psd.nonneg d
    have h_nonpos : inner ℝ d (matVec M d) ≤ 0 := by
      have h := lcp_inner_diff_nonpos v v' x x'
        hv_nonneg hv'_nonneg hx_nonneg hx'_nonneg h_comp1 h_comp2
      simpa [h_diff_eq, real_inner_comm] using h
    linarith
  have h_matvec_zero : matVec M d = 0 :=
    psd_zero_quadratic_imp_zero M hM_psd d h_quad_zero
  have h_zero_diff : v' - v = 0 := by rw [h_diff_eq, h_matvec_zero]
  exact (sub_eq_zero.1 h_zero_diff).symm

/--
Proposition 4.9 from `docs/Lasso.md`: for positive lasso data, the LCP has a
solution and the dual variable is unique.

Informal proof reference: `docs/Lasso.md`, Section 4.4, Proposition 4.9.
Existence follows because the positive-lasso objective is bounded below on the
nonnegative orthant (`ell` is bounded below from `r ∈ Span M`, and the penalty is
nonnegative). The uniqueness of the dual variable is the standard uniqueness
part for positive-semidefinite LCPs, cited there as Cottle--Pang--Stone,
Theorem 3.1.7(d).
-/
theorem lcp_exists_unique_dual
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hdata : ProblemData M r lambda) (hμ : 0 < μ) :
    (∃ x v : EuclideanSpace ℝ ι, isLCP M (lcpQ r lambda μ) x v) ∧
      ∀ ⦃x x' v v' : EuclideanSpace ℝ ι⦄,
        isLCP M (lcpQ r lambda μ) x v →
        isLCP M (lcpQ r lambda μ) x' v' →
        v = v' := by
  have hM_symm : M.IsSymm := hdata.psd.symm
  -- Existence: get a positive lasso minimizer, then convert to LCP solution
  rcases pos_lasso_achieves_minimum M r lambda μ hdata hμ with ⟨x, hx_min⟩
  rcases (pos_lasso_is_lcp M r lambda μ x hM_symm hdata.psd).mp hx_min with ⟨v, hv⟩
  -- Uniqueness: use the PSD LCP uniqueness lemma
  refine ⟨⟨x, v, hv⟩, ?_⟩
  exact psd_lcp_unique_dual M hdata.psd (lcpQ r lambda μ)


-- When ι is nonempty, use the spectral theorem: let C = max eigenvalue of M.
-- Since λ_i² ≤ C·λ_i for each eigenvalue, summing over the eigenbasis gives
-- ‖Mv‖² ≤ C·⟨v, Mv⟩. If all eigenvalues are zero, any C > 0 (e.g. 1) works.
private lemma psd_matrix_norm_sq_bound_nonempty {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hM_psd : IsPositiveSemidefinite M) (h_ne : ¬ IsEmpty ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : EuclideanSpace ℝ ι),
      ‖matVec M v‖ * ‖matVec M v‖ ≤ C * inner ℝ v (matVec M v) := by
  classical
  have h_nonempty : Finset.Nonempty (Finset.univ : Finset ι) := by
    obtain ⟨i₀⟩ := not_isEmpty_iff.mp h_ne
    exact ⟨i₀, Finset.mem_univ i₀⟩
  -- Step 1: `M.IsSymm` implies `M.IsHermitian` over ℝ (which has TrivialStar)
  have hM_herm : M.IsHermitian := by
    simpa using hM_psd.symm
  -- Step 2: eigenbasis and eigenvalues from the spectral theorem for Hermitian matrices
  let b := hM_herm.eigenvectorBasis
  let ev := hM_herm.eigenvalues
  -- Step 3: eigenvector equation for matVec
  have h_eigenvec (i : ι) : matVec M (b i) = (ev i) • (b i) := by
    have h := hM_herm.mulVec_eigenvectorBasis i
    dsimp [matVec, euclideanOf, b, ev]
    simpa using congrArg (WithLp.equiv 2 (ι → ℝ)).symm h
  -- Step 4: eigenvalues are nonnegative (since M is PSD)
  have h_nonneg_ev (i : ι) : 0 ≤ ev i := by
    have hpos := hM_psd.nonneg (b i)
    rw [h_eigenvec i] at hpos
    have h_inner_self : inner ℝ (b i) (b i) = 1 := b.inner_eq_one i
    simpa [h_inner_self, real_inner_smul_right] using hpos
  -- Step 5: repr of matVec under the eigenbasis relates to repr of v
  have h_repr_matVec (v : EuclideanSpace ℝ ι) (i : ι) :
      b.repr (matVec M v) i = (ev i) * b.repr v i := by
    calc
      b.repr (matVec M v) i = inner ℝ (b i) (matVec M v) := by rw [b.repr_apply_apply]
      _ = inner ℝ (matVec M (b i)) v := by
        rw [inner_matVec_comm_of_isSymm M hM_psd.symm (b i) v]
      _ = inner ℝ ((ev i) • (b i)) v := by rw [h_eigenvec i]
      _ = (ev i) * inner ℝ (b i) v := by rw [real_inner_smul_left]
      _ = (ev i) * b.repr v i := by rw [b.repr_apply_apply]
  -- Step 6: expand inner product ⟨v, Mv⟩ in the eigenbasis
  have h_inner_expand (v : EuclideanSpace ℝ ι) :
      inner ℝ v (matVec M v) = ∑ i : ι, (ev i) * (b.repr v i) ^ 2 := by
    calc
      inner ℝ v (matVec M v) = ∑ i : ι, inner ℝ (b i) v * inner ℝ (b i) (matVec M v) := by
        rw [← OrthonormalBasis.sum_inner_mul_inner b v (matVec M v)]
        simp [real_inner_comm]
      _ = ∑ i : ι, (b.repr v i) * (b.repr (matVec M v) i) := by
        simp_rw [b.repr_apply_apply]
      _ = ∑ i : ι, (b.repr v i) * ((ev i) * b.repr v i) := by
        simp_rw [h_repr_matVec v]
      _ = ∑ i : ι, (ev i) * (b.repr v i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
  -- Step 7: expand ‖Mv‖² in the eigenbasis
  have h_norm_sq_expand (v : EuclideanSpace ℝ ι) :
      ‖matVec M v‖ * ‖matVec M v‖ = ∑ i : ι, ((ev i)^2) * (b.repr v i) ^ 2 := by
    rw [show ‖matVec M v‖ * ‖matVec M v‖ = ‖matVec M v‖ ^ 2 by ring,
      ← real_inner_self_eq_norm_sq]
    calc
      inner ℝ (matVec M v) (matVec M v) =
          ∑ i : ι, inner ℝ (b i) (matVec M v) * inner ℝ (b i) (matVec M v) := by
        rw [← OrthonormalBasis.sum_inner_mul_inner b (matVec M v) (matVec M v)]
        simp [real_inner_comm]
      _ = ∑ i : ι, (b.repr (matVec M v) i) * (b.repr (matVec M v) i) := by
        simp_rw [b.repr_apply_apply]
      _ = ∑ i : ι, ((ev i) * b.repr v i) * ((ev i) * b.repr v i) := by
        simp_rw [h_repr_matVec v]
      _ = ∑ i : ι, ((ev i)^2) * (b.repr v i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
  -- Step 8: Let C be the maximum eigenvalue
  let C := Finset.sup' Finset.univ h_nonempty ev
  have hC_max (i : ι) : ev i ≤ C := by
    rw [Finset.le_sup'_iff]
    exact ⟨i, Finset.mem_univ i, le_rfl⟩
  have hC_nonneg : 0 ≤ C := by
    obtain ⟨i, hi⟩ := h_nonempty
    have hi_nonneg := h_nonneg_ev i
    have hi_le_C := hC_max i
    linarith
  -- Step 9: the key inequality λ_i² ≤ C·λ_i
  have h_key (i : ι) : (ev i)^2 ≤ C * (ev i) := by
    have hi_nonneg := h_nonneg_ev i
    have hi_le_C := hC_max i
    nlinarith
  -- Step 10: assemble the bound
  by_cases hC_zero : C = 0
  · -- all eigenvalues are zero, so both sums vanish
    have h_ev_zero (i : ι) : ev i = 0 := by
      have hi_nonneg := h_nonneg_ev i
      have hi_le_C := hC_max i
      linarith
    refine ⟨1, by norm_num, ?_⟩
    intro v
    rw [h_norm_sq_expand v, h_inner_expand v]
    simp [h_ev_zero]
  · -- C > 0
    have hC_pos : 0 < C := lt_of_le_of_ne hC_nonneg (Ne.symm hC_zero)
    refine ⟨C, hC_pos, ?_⟩
    intro v
    rw [h_norm_sq_expand v, h_inner_expand v]
    calc
      ∑ i : ι, ((ev i)^2) * (b.repr v i) ^ 2
          ≤ ∑ i : ι, (C * (ev i)) * (b.repr v i) ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        nlinarith [h_key i, pow_two_nonneg (b.repr v i)]
      _ = C * (∑ i : ι, (ev i) * (b.repr v i) ^ 2) := by
        simp [Finset.mul_sum, mul_assoc]

/-- Helper lemma: PSD matrix norm squared is bounded by its quadratic form.

Proof: By the spectral theorem for real symmetric matrices, `M` has an orthonormal basis
of eigenvectors `b i` with eigenvalues `λ i ≥ 0`. Writing `v = ∑ c_i · b i`, we have:
`⟨v, M v⟩ = ∑ λ_i c_i²` and `‖M v‖² = ∑ λ_i² c_i²`.
Let `C = max_i λ_i` (or `C = 1` if all `λ_i = 0`). Since `λ_i² ≤ C·λ_i` for each `i`,
summing gives `‖M v‖² ≤ C·⟨v, M v⟩`.
-/
lemma psd_matrix_norm_sq_bound {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hM_psd : IsPositiveSemidefinite M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : EuclideanSpace ℝ ι),
      ‖matVec M v‖ * ‖matVec M v‖ ≤ C * inner ℝ v (matVec M v) := by
  classical
  -- Handle the empty ι case: if there are no indices, the space is trivial
  by_cases h_empty : IsEmpty ι
  · -- In a trivial vector space, v = 0, both sides are 0, any C > 0 works
    refine ⟨1, by norm_num, fun v => ?_⟩
    rw [Subsingleton.elim v 0]
    simp [matVec, euclideanOf, norm_zero]
  · -- ι is nonempty: delegate to the spectral-theorem helper
    exact psd_matrix_norm_sq_bound_nonempty M hM_psd h_empty

/-- Helper lemma: Scaled dual path satisfies a parametric LCP. -/
lemma scaled_dual_lcp_eq
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (z w : ℝ → EuclideanSpace ℝ ι)
    (hlambda_nonneg : 0 ≤ lambda)
    (hsol : ∀ μ : ℝ, 0 ≤ μ → isParametricLCP M r lambda μ (z μ) (w μ))
    (μ : ℝ) (hμ : 0 ≤ μ) :
    let wt := scaledDualPath lambda w μ
    let zt := (1 / (1 + μ * lambda)) • z μ
    let s := μ / (1 + μ * lambda)
    wt = -s • r + ones + matVec M zt ∧
    Nonnegative wt ∧ Nonnegative zt ∧ inner ℝ wt zt = 0 := by
  have h_scale : 0 ≤ 1 / (1 + μ * lambda) := div_nonneg (by norm_num) (by nlinarith)
  rcases hsol μ hμ with ⟨hw_eq, hw_nonneg, hz_nonneg, h_comp⟩
  rw [show parametricLcpQ r lambda μ = (-μ) • r + (1 + μ * lambda) • ones from by
    ext i; simp [parametricLcpQ, ones, euclideanOf]; ring] at hw_eq
  have h_wt_eq : scaledDualPath lambda w μ =
      -(μ / (1 + μ * lambda)) • r + ones + matVec M ((1 / (1 + μ * lambda)) • z μ) := by
    dsimp [scaledDualPath]
    rw [hw_eq]
    simp [smul_add, add_assoc, matVec_smul_eq, smul_smul, show 1 + μ * lambda ≠ 0 by nlinarith]
    ring_nf
  have h_wt_nonneg : Nonnegative (scaledDualPath lambda w μ) := by
    intro i
    dsimp [scaledDualPath]
    exact mul_nonneg h_scale (hw_nonneg i)
  have h_zt_nonneg : Nonnegative ((1 / (1 + μ * lambda)) • z μ) := by
    intro i
    exact mul_nonneg h_scale (hz_nonneg i)
  have h_comp_scaled : inner ℝ (scaledDualPath lambda w μ) ((1 / (1 + μ * lambda)) • z μ) = 0 := by
    dsimp [scaledDualPath]
    simp [inner_smul_right, inner_smul_left, h_comp]
  exact ⟨h_wt_eq, h_wt_nonneg, h_zt_nonneg, h_comp_scaled⟩

/-- Helper lemma: The inner product bound for the difference of scaled variables. -/
lemma scaled_dual_lcp_key_ineq
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι)
    (hM_psd : IsPositiveSemidefinite M)
    (wt zt : ℝ → EuclideanSpace ℝ ι) (s : ℝ → ℝ)
    (h_scaled_lcp : ∀ μ : ℝ, 0 ≤ μ →
      wt μ = -(s μ) • r + ones + matVec M (zt μ) ∧
      Nonnegative (wt μ) ∧ Nonnegative (zt μ) ∧ inner ℝ (wt μ) (zt μ) = 0)
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂) :
    inner ℝ (zt μ₁ - zt μ₂) (matVec M (zt μ₁ - zt μ₂)) ≤
      |s μ₁ - s μ₂| * |inner ℝ r (zt μ₁ - zt μ₂)| := by
  rcases h_scaled_lcp μ₁ hμ₁ with ⟨hw_eq₁, hw_nonneg₁, hz_nonneg₁, h_comp₁⟩
  rcases h_scaled_lcp μ₂ hμ₂ with ⟨hw_eq₂, hw_nonneg₂, hz_nonneg₂, h_comp₂⟩
  set d := zt μ₁ - zt μ₂
  set ds := s μ₁ - s μ₂
  have h_diff_eq : wt μ₁ - wt μ₂ = -(ds) • r + matVec M d := by
    rw [hw_eq₁, hw_eq₂]
    simp [d, ds, matVec_sub, sub_smul]
    abel_nf
  have h_inner_nonpos : inner ℝ (wt μ₁ - wt μ₂) d ≤ 0 := by
    have h := lcp_inner_diff_nonpos (wt μ₂) (wt μ₁) (zt μ₂) (zt μ₁)
      hw_nonneg₂ hw_nonneg₁ hz_nonneg₂ hz_nonneg₁ h_comp₂ h_comp₁
    simpa [d] using h
  rw [h_diff_eq] at h_inner_nonpos
  rw [inner_add_left, inner_smul_left] at h_inner_nonpos
  change -(ds) * inner ℝ r d + inner ℝ (matVec M d) d ≤ 0 at h_inner_nonpos
  rw [real_inner_comm d (matVec M d)] at h_inner_nonpos
  have h_quad_le : inner ℝ d (matVec M d) ≤ ds * inner ℝ r d := by linarith
  by_cases h_prod : 0 ≤ ds * inner ℝ r d
  · rw [← abs_of_nonneg h_prod, abs_mul] at h_quad_le
    exact h_quad_le
  · have : ds * inner ℝ r d ≤ 0 := by linarith
    have h_quad_zero : inner ℝ d (matVec M d) = 0 := by
      linarith [h_quad_le, this, hM_psd.nonneg d]
    rw [h_quad_zero]
    nlinarith [abs_nonneg (ds), abs_nonneg (inner ℝ r d)]

/-- Faithful exact-solution form of Lemma 4.10 for the parametric LCP.

The threshold is stated with the finite-dimensional `ℓ∞` norm, exactly as in
`docs/Lasso.md`.  The Lean argument is the paper argument: the threshold makes
every coordinate of `q(μ)` strictly positive; `(z,w)=(0,q(μ))` is feasible;
and PSD plus complementarity forces `z=0`, after which the affine equation
forces `w=q(μ)`.  See Lemma 4.10 of the source paper
<https://arxiv.org/abs/2509.18766> and the standard LCP definition in Cottle,
Pang, and Stone, *The Linear Complementarity Problem*, Chapter 1
<https://epubs.siam.org/doi/book/10.1137/1.9780898719000>.
-/
theorem parametric_lcp_eq_iff_of_small_mu
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hM_psd : IsPositiveSemidefinite M) (hμ : 0 ≤ μ)
    (hμ_small :
      μ < 1 / max ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ 1) :
    ∀ z w : EuclideanSpace ℝ ι,
      isParametricLCP M r lambda μ z w ↔
        z = 0 ∧ w = parametricLcpQ r lambda μ := by
  -- Introduce notation N for the ℓ∞ norm of r - λ·𝟙, and derive μ·N < 1 from hμ_small
  set N := ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ with hN
  have hN_nonneg : 0 ≤ N := by rw [hN]; exact norm_nonneg _
  have hμN_lt_one : μ * N < 1 := by
    by_cases hNle : N ≤ 1
    · -- Case N ≤ 1: max N 1 = 1, so μ < 1/1 = 1, and μ·N ≤ μ·1 < 1
      have hmax_one : max N 1 = 1 := max_eq_right hNle
      rw [hmax_one] at hμ_small
      have hμ_lt_one : μ < 1 := by
        simpa [div_one] using hμ_small
      have hμN_le_μ : μ * N ≤ μ := by
        calc
          μ * N ≤ μ * 1 := mul_le_mul_of_nonneg_left hNle hμ
          _ = μ := by ring
      linarith
    · -- Case N > 1: max N 1 = N, so μ < 1/N, and clearing the denominator gives μ·N < 1
      have h_one_le_N : 1 ≤ N := by linarith
      have hmax_N : max N 1 = N := max_eq_left h_one_le_N
      rw [hmax_N] at hμ_small
      have hpos : 0 < N := by linarith
      exact (lt_div_iff₀ hpos).mp hμ_small
  let q := parametricLcpQ r lambda μ
  have hq_pos : ∀ i, 0 < q i := parametricLcpQ_pos r lambda μ hμ hμN_lt_one
  intro z w
  constructor
  · -- Forward direction: any LCP solution must be (z=0, w=q)
    intro h
    dsimp [isParametricLCP, isLCP] at h
    rcases h with ⟨h_w, h_w_pos, h_z_pos, h_ortho⟩
    -- h_w : w = q + matVec M z, h_ortho : inner ℝ w z = 0
    have h_inner_add : inner ℝ q z + inner ℝ (matVec M z) z = 0 := by
      dsimp [q]
      rw [← inner_add_left, ← h_w, h_ortho]
    have hz_Mz_nonneg : 0 ≤ inner ℝ z (matVec M z) :=
      IsPositiveSemidefinite.get_nonneg hM_psd z
    have h_Mz_z_eq : inner ℝ (matVec M z) z = inner ℝ z (matVec M z) :=
      real_inner_comm z (matVec M z)
    rw [h_Mz_z_eq] at h_inner_add
    have h_qz_nonpos : inner ℝ q z ≤ 0 := by linarith
    have h_qz_nonneg : 0 ≤ inner ℝ q z := by
      -- Expand inner product to sum of coordinate products, all nonnegative
      have h_sum : inner ℝ q z = ∑ i : ι, q.ofLp i * z.ofLp i := by
        rw [PiLp.inner_apply]
        simp only [Real.inner_apply]
      rw [h_sum]
      refine Finset.sum_nonneg (fun i _ => ?_)
      exact mul_nonneg (le_of_lt (hq_pos i)) (h_z_pos i)
    have h_qz_zero : inner ℝ q z = 0 := le_antisymm h_qz_nonpos h_qz_nonneg
    have h_z_zero : z = 0 := by
      ext i
      have h_sum_zero : ∑ j : ι, q.ofLp j * z.ofLp j = 0 := by
        have h_sum : inner ℝ q z = ∑ j : ι, q.ofLp j * z.ofLp j := by
          rw [PiLp.inner_apply]
          simp only [Real.inner_apply]
        rw [← h_sum, h_qz_zero]
      have h_term_zero : q.ofLp i * z.ofLp i = 0 := by
        have h_nonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ q.ofLp j * z.ofLp j :=
          fun j _ => mul_nonneg (le_of_lt (hq_pos j)) (h_z_pos j)
        exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_zero i (Finset.mem_univ i)
      cases mul_eq_zero.mp h_term_zero with
      | inl h_q_zero =>
        have h_qi_pos : 0 < q.ofLp i := hq_pos i
        linarith
      | inr h_zi_zero =>
        simpa using h_zi_zero
    have h_w_eq_q : w = q := by
      rw [h_z_zero] at h_w
      have h_zero : matVec M 0 = 0 := by
        ext j; simp [matVec, euclideanOf]
      rw [h_zero, add_zero] at h_w
      exact h_w
    exact ⟨h_z_zero, h_w_eq_q⟩
  · -- Backward direction: (z=0, w=q) is a solution
    intro ⟨hz, hw⟩
    subst hz; subst hw
    dsimp [isParametricLCP, isLCP]
    constructor
    · ext i; dsimp [q]; simp [matVec, euclideanOf]
    · constructor
      · intro i; exact le_of_lt (hq_pos i)
      · constructor
        · intro i; exact le_refl 0
        · simp [inner_zero_right]

/-- Existential-uniqueness packaging of the faithful Lemma 4.10 threshold.

The more informative theorem `parametric_lcp_eq_iff_of_small_mu` identifies
the solution explicitly; this declaration is retained for clients that only
need `∃!`.
-/
theorem parametric_lcp_unique_small_mu
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hM_psd : IsPositiveSemidefinite M) (hμ : 0 ≤ μ)
    (hμ_small :
      μ < 1 / max ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ 1) :
    ∃! p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      isParametricLCP M r lambda μ p.1 p.2 := by
  sorry

/-- The unscaled positive-Lasso LCP conclusion in the second sentence of
Lemma 4.10.

For `μ > 0`, divide the parametric variables and equations by `μ`.  The exact
parametric solution above becomes `x=0` and
`v=-r+(λ+1/μ)𝟙`.  This is the same scaling calculation as in Lemma 4.10 of
<https://arxiv.org/abs/2509.18766>; the LCP conventions are cross-checked
against Cottle--Pang--Stone
<https://epubs.siam.org/doi/book/10.1137/1.9780898719000>.
-/
theorem lcp_eq_iff_of_small_mu
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hM_psd : IsPositiveSemidefinite M) (hμ : 0 < μ)
    (hμ_small :
      μ < 1 / max ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ 1) :
    ∀ x v : EuclideanSpace ℝ ι,
      isLCP M (lcpQ r lambda μ) x v ↔ x = 0 ∧ v = lcpQ r lambda μ := by
  sorry

/-- Helper lemma: Bound for |s(μ) - s(ν)| -/
lemma scaled_dual_lcp_s_diff_bound (lambda : ℝ) (hlambda_nonneg : 0 ≤ lambda)
    {μ ν : ℝ} (hμ_nonneg : 0 ≤ μ) (hν_nonneg : 0 ≤ ν) :
    let s := fun μ => μ / (1 + μ * lambda)
    |s μ - s ν| ≤ |μ - ν| := by
  intro s
  dsimp [s]
  have h_denom_ge_one : 1 ≤ (1 + μ * lambda) * (1 + ν * lambda) := by
    have h1 : 1 ≤ 1 + μ * lambda := by nlinarith
    have h2 : 1 ≤ 1 + ν * lambda := by nlinarith
    nlinarith
  have h_denom_pos' : 0 < (1 + μ * lambda) * (1 + ν * lambda) := by nlinarith
  rw [show μ / (1 + μ * lambda) - ν / (1 + ν * lambda) =
      (μ - ν) / ((1 + μ * lambda) * (1 + ν * lambda)) by
    rw [div_sub_div _ _ (by nlinarith) (by nlinarith)]
    ring]
  rw [abs_div, abs_of_pos h_denom_pos']
  exact div_le_self (abs_nonneg _) h_denom_ge_one

/--
The difference of scaled dual variables is bounded by the parameter difference.
Informal proof: Using the LCP equations for scaled variables at $\mu_1, \mu_2$, the difference
$  ilde{w}_1 -   ilde{w}_2$ is in the span of $M$ plus a term proportional to $r (\mu_1 - \mu_2)$.
By taking the inner product with $  ilde{z}_1 -   ilde{z}_2$ and using complementarity slackness,
the cross terms are non-positive. Applying Cauchy-Schwarz with the PSD matrix $M$ yields a bound
proportional to $|\mu_1 - \mu_2|$.
Source: docs/Lasso.md Section 4.5, Lemma 4.11.
-/
lemma scaled_dual_lipschitz
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (z w : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hsol : ∀ μ : ℝ, 0 ≤ μ → isParametricLCP M r lambda μ (z μ) (w μ)) :
    LocallyLipschitzOnCompacts (scaledDualPath lambda w) := by
  rcases hdata with ⟨hM_psd, hr_mem_span, hlambda_nonneg⟩
  rcases hr_mem_span with ⟨y, hy⟩
  rcases psd_matrix_norm_sq_bound M hM_psd with ⟨C, hC_pos, hC_bound⟩
  set wt := scaledDualPath lambda w
  set zt : ℝ → EuclideanSpace ℝ ι := fun μ => (1 / (1 + μ * lambda)) • z μ
  set s : ℝ → ℝ := fun μ => μ / (1 + μ * lambda)
  have h_scaled_lcp (μ : ℝ) (hμ : 0 ≤ μ) :
      wt μ = -(s μ) • r + ones + matVec M (zt μ) ∧
      Nonnegative (wt μ) ∧ Nonnegative (zt μ) ∧ inner ℝ (wt μ) (zt μ) = 0 :=
    scaled_dual_lcp_eq M r lambda z w hlambda_nonneg hsol μ hμ
  have h_key_ineq {μ₁ μ₂ : ℝ} (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂) :
      inner ℝ (zt μ₁ - zt μ₂) (matVec M (zt μ₁ - zt μ₂)) ≤
      |s μ₁ - s μ₂| * |inner ℝ r (zt μ₁ - zt μ₂)| :=
    scaled_dual_lcp_key_ineq M r hM_psd wt zt s h_scaled_lcp hμ₁ hμ₂
  refine ⟨?lipschitz_on_Icc⟩
  intro a b ha_nonneg ha_le_b
  set K := ‖r‖ + C * ‖y‖
  have hK_nonneg : 0 ≤ K := by nlinarith [norm_nonneg r, norm_nonneg y, hC_pos]
  refine ⟨K, hK_nonneg, ?_⟩
  intro μ hμ_mem ν hν_mem
  rcases hμ_mem with ⟨hμ_low, hμ_high⟩
  rcases hν_mem with ⟨hν_low, hν_high⟩
  have hμ_nonneg : 0 ≤ μ := le_trans ha_nonneg hμ_low
  have hν_nonneg : 0 ≤ ν := le_trans ha_nonneg hν_low
  set d := zt μ - zt ν
  set ds := s μ - s ν
  have h_diff_eq : wt μ - wt ν = -(ds) • r + matVec M d := by
    rcases h_scaled_lcp μ hμ_nonneg with ⟨hw_eq₁, _, _, _⟩
    rcases h_scaled_lcp ν hν_nonneg with ⟨hw_eq₂, _, _, _⟩
    rw [hw_eq₁, hw_eq₂]
    simp [d, ds, matVec_sub, sub_smul]
    abel_nf
  have h_quad_bound : inner ℝ d (matVec M d) ≤ |ds| * |inner ℝ r d| :=
    h_key_ineq hμ_nonneg hν_nonneg
  have h_abs_r_d_le : |inner ℝ r d| ≤ ‖y‖ * ‖matVec M d‖ := by
    rw [← hy, ← inner_matVec_comm_of_isSymm M hM_psd.symm y d]
    exact abs_real_inner_le_norm _ _
  have h_norm_sq_bound : ‖matVec M d‖ * ‖matVec M d‖ ≤ C * inner ℝ d (matVec M d) := hC_bound d
  have h_Md_norm_le : ‖matVec M d‖ ≤ C * ‖y‖ * |ds| := by
    by_cases h_zero : ‖matVec M d‖ = 0
    · rw [h_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hC_pos) (norm_nonneg y)) (abs_nonneg ds)
    · have h_pos : 0 < ‖matVec M d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
      have h_step2 : C * inner ℝ d (matVec M d) ≤ C * (|ds| * |inner ℝ r d|) :=
        mul_le_mul_of_nonneg_left h_quad_bound (by linarith [hC_pos])
      have h_step3 : C * (|ds| * |inner ℝ r d|) ≤ C * (|ds| * (‖y‖ * ‖matVec M d‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_abs_r_d_le (abs_nonneg _)) (by linarith [hC_pos])
      have h_ineq : ‖matVec M d‖ * ‖matVec M d‖ ≤ C * |ds| * ‖y‖ * ‖matVec M d‖ := by
        calc
          ‖matVec M d‖ * ‖matVec M d‖ ≤ C * inner ℝ d (matVec M d) := h_norm_sq_bound
          _ ≤ C * (|ds| * |inner ℝ r d|) := h_step2
          _ ≤ C * (|ds| * (‖y‖ * ‖matVec M d‖)) := h_step3
          _ = C * |ds| * ‖y‖ * ‖matVec M d‖ := by ring
      nlinarith
  have h_s_diff_bound : |ds| ≤ |μ - ν| :=
    scaled_dual_lcp_s_diff_bound lambda hlambda_nonneg hμ_nonneg hν_nonneg
  calc
    ‖wt μ - wt ν‖ = ‖-(ds) • r + matVec M d‖ := by rw [h_diff_eq]
    _ ≤ ‖-(ds) • r‖ + ‖matVec M d‖ := norm_add_le _ _
    _ = |ds| * ‖r‖ + ‖matVec M d‖ := by
      rw [norm_smul, norm_neg]
      rw [Real.norm_eq_abs]
    _ ≤ |ds| * ‖r‖ + C * ‖y‖ * |ds| := add_le_add (le_refl _) h_Md_norm_le
    _ = (‖r‖ + C * ‖y‖) * |ds| := by ring
    _ ≤ K * |μ - ν| := by
      dsimp [K]
      exact mul_le_mul_of_nonneg_left h_s_diff_bound hK_nonneg

/--
If a path `wt` satisfies `wt(μ) = -(s μ) • r + 1 + M (zt μ)` for all μ ≥ 0,
and `r = M y` for some `y`, then the derivative of `wt` at any μ ≥ 0 lies in
the column space of `M`.
-/
lemma deriv_in_matrix_span_of_scaled_eq
    (M : Matrix ι ι ℝ) (r y : EuclideanSpace ℝ ι) (hy : matVec M y = r)
    (wt zt : ℝ → EuclideanSpace ℝ ι) (s : ℝ → ℝ)
    (h_scaled_eq : ∀ μ, 0 ≤ μ → wt μ = -(s μ) • r + ones + matVec M (zt μ)) :
    ∀ μ, 0 ≤ μ → InMatrixSpan M (deriv wt μ) := by
  intro μ hμ_nonneg
  -- Key idea: difference quotients of wt lie in Span M because
  --   (wt(μ+h)-wt(μ))/h = -((s(μ+h)-s(μ))/h) • r + M ((zt(μ+h)-zt(μ))/h)
  -- and r = M y.  Taking h → 0, the limit (the derivative) stays in Span M
  -- because Span M is a finite-dimensional (hence closed) subspace.
  -- We split into cases: wt differentiable at μ vs not.
  by_cases h_diff : DifferentiableAt ℝ wt μ
  · -- Informal proof:
    -- We have h_scaled_eq: wt(ν) = -(s ν)•r + ones + matVec M (zt ν) for ν ≥ 0.
    -- Since r = M y, the RHS is in the affine subspace 1 + Im(M).
    -- Differentiating, the derivative must lie in the tangent space Im(M).
    -- Formal proof: difference quotients lie in Im(M); Im(M) is a finite-dimensional
    -- subspace, hence closed; the limit (the derivative) stays in Im(M).
    -- Build the subspace S = Im(M) as a linear subspace
    let L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
      { toFun := matVec M
        map_add' := matVec_add M
        map_smul' := matVec_smul_eq M }
    let S : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range L
    -- Show that for all t > 0, the difference quotient is in S
    -- Key: wt ν - ones = matVec M ((-(s ν)) • y + zt ν) for ν ≥ 0
    have h_wt_sub_ones (ν : ℝ) (hν : 0 ≤ ν) : wt ν - ones = matVec M ((-(s ν)) • y + zt ν) := by
      rw [h_scaled_eq ν hν, ← hy]
      calc
        -(s ν) • matVec M y + ones + matVec M (zt ν) - ones
            = (-(s ν)) • matVec M y + matVec M (zt ν) := by abel
        _ = matVec M ((-(s ν)) • y + zt ν) := by
          rw [matVec_add M, matVec_smul_eq M (-(s ν)) y]
    have h_diff_quot_mem :
        ∀ t > 0, t⁻¹ • (wt (μ + t) - wt μ) ∈ (S : Set (EuclideanSpace ℝ ι)) := by
      intro t ht_pos
      have h_wt_diff_eq : wt (μ + t) - wt μ =
          matVec M (((-(s (μ + t))) • y + zt (μ + t)) - ((-(s μ)) • y + zt μ)) := by
        calc
          wt (μ + t) - wt μ = (wt (μ + t) - ones) - (wt μ - ones) := by abel
          _ = matVec M ((-(s (μ + t))) • y + zt (μ + t)) -
              matVec M ((-(s μ)) • y + zt μ) := by
            rw [h_wt_sub_ones (μ + t) (by linarith), h_wt_sub_ones μ hμ_nonneg]
          _ = matVec M (((-(s (μ + t))) • y + zt (μ + t)) -
              ((-(s μ)) • y + zt μ)) := by rw [matVec_sub M]
      rw [h_wt_diff_eq]
      exact ⟨t⁻¹ • (((-(s (μ + t))) • y + zt (μ + t)) -
          ((-(s μ)) • y + zt μ)), by simp [L]⟩
    -- Since S is closed and the limit of difference quotients is deriv wt μ,
    -- we have deriv wt μ ∈ S.
    simpa [S, L, InMatrixSpan] using
      (S.closed_of_finiteDimensional).mem_of_tendsto
        (by
          open scoped Topology in
          simpa using h_diff.hasDerivAt.tendsto_slope_zero_right)
        (by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact h_diff_quot_mem t ht)
  · -- When wt is not differentiable at μ, deriv wt μ is defined to be 0 in Lean.
    rw [deriv_zero_of_not_differentiableAt h_diff]
    exact ⟨0, by simp [matVec, euclideanOf]⟩

/--
Algebraic identity for the scaled difference quotient:
`h⁻¹ • (wt(μ+h) - wt(μ)) = M ((-Δs/h) • y + h⁻¹ • Δzt)`
where `wt(ν) = -(s ν) • r + 1 + M (zt ν)` and `r = M y`.
-/
lemma scaled_diff_quot_eq_matVec
    (M : Matrix ι ι ℝ) (r y : EuclideanSpace ℝ ι) (hy : matVec M y = r)
    (wt zt : ℝ → EuclideanSpace ℝ ι) (s : ℝ → ℝ)
    (h_scaled_eq : ∀ ν, 0 ≤ ν → wt ν = -(s ν) • r + ones + matVec M (zt ν))
    (μ h : ℝ) (hμ_nonneg : 0 ≤ μ) (hpos : 0 < h) :
    h⁻¹ • (wt (μ + h) - wt μ) =
      matVec M ((-((s (μ + h) - s μ) / h)) • y + h⁻¹ • (zt (μ + h) - zt μ)) := by
  set d := zt (μ + h) - zt μ with hd_def
  set ds := s (μ + h) - s μ with hds_def
  have h_sub :
      (-(s (μ + h)) • r + ones + matVec M (zt (μ + h))) -
      (-(s μ) • r + ones + matVec M (zt μ)) = -ds • r + matVec M d := by
    simp [d, ds, matVec_sub, sub_smul]
    abel_nf
  calc
    h⁻¹ • (wt (μ + h) - wt μ)
        = h⁻¹ • (-ds • r + matVec M d) := by
      rw [h_scaled_eq (μ + h) (by linarith), h_scaled_eq μ hμ_nonneg, h_sub]
    _ = h⁻¹ • (-ds • r) + h⁻¹ • (matVec M d) := by rw [smul_add]
    _ = (h⁻¹ • (-ds • r)) + (matVec M (h⁻¹ • d)) := by rw [matVec_smul_eq M h⁻¹ d]
    _ = ((h⁻¹ * (-ds)) • r) + (matVec M (h⁻¹ • d)) := by rw [smul_smul]
    _ = ((-(ds / h)) • r) + (matVec M (h⁻¹ • d)) := by ring_nf
    _ = (-(ds / h)) • (matVec M y) + matVec M (h⁻¹ • d) := by rw [hy]
    _ = matVec M ((-(ds / h)) • y) + matVec M (h⁻¹ • d) := by rw [matVec_smul_eq M (-(ds / h)) y]
    _ = matVec M ((-(ds / h)) • y + h⁻¹ • d) := by rw [matVec_add M]
    _ = matVec M ((-((s (μ + h) - s μ) / h)) • y +
      h⁻¹ • (zt (μ + h) - zt μ)) := by rw [hds_def, hd_def]

/--
Pseudoinverse inner-product identity: `⟨M v, M† (M v)⟩ = ⟨v, M v⟩`.
Follows from symmetry of `M` and the first Penrose condition `M M† M = M`.
-/
lemma pseudoInverse_inner_prop
    (M Mdagger : Matrix ι ι ℝ) (hM_symm : M.IsSymm)
    (h_mp : ∀ v : EuclideanSpace ℝ ι, matVec M (matVec Mdagger (matVec M v)) = matVec M v)
    (v : EuclideanSpace ℝ ι) :
    inner ℝ (matVec M v) (matVec Mdagger (matVec M v)) = inner ℝ v (matVec M v) := by
  rw [← inner_matVec_comm_of_isSymm M hM_symm v (matVec Mdagger (matVec M v)), h_mp v]

/-- Expansion of `⟨(-α)y + u, M((-α)y + u)⟩` for a symmetric matrix `M`.
This identity is used in the proof of the seminorm bound for the derivative
of the scaled dual path (Lemma 4.11). -/
lemma inner_matVec_add_smul_sq_eq
    (M : Matrix ι ι ℝ) (hM_symm : M.IsSymm) (y u : EuclideanSpace ℝ ι) (α : ℝ) :
    inner ℝ ((-α) • y + u) (matVec M ((-α) • y + u)) =
    α ^ 2 * inner ℝ y (matVec M y) + inner ℝ u (matVec M u) -
    2 * α * inner ℝ y (matVec M u) := by
  rw [matVec_add, matVec_smul_eq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_matVec_comm_of_isSymm M hM_symm u y]
  rw [real_inner_comm (matVec M u) y]
  ring

/-- Quadratic inequality: `α²B + A - 2αC ≤ B` given `A ≤ αC`, `0 ≤ α ≤ 1`, `B, C ≥ 0`.
This algebraic inequality is used in the core estimate of Lemma 4.11. -/
lemma quad_ineq (α A B C : ℝ) (hA_le_αC : A ≤ α * C) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : 0 ≤ B) (hC_nonneg : 0 ≤ C) :
    α ^ 2 * B + A - 2 * α * C ≤ B := by
  by_cases h_cases : α * B - C ≤ 0
  · -- then α²B + A - 2αC ≤ α²B + αC - 2αC = α(αB - C) ≤ 0 ≤ B
    nlinarith
  · -- then αB - C > 0, so α(αB - C) ≤ αB - C ≤ αB ≤ B
    nlinarith

/-- Continuity of `pseudoInverseSeminorm Mdagger` on a finite-dimensional `EuclideanSpace`.
Follows from linearity of `matVec Mdagger` and continuity of inner product and `Real.sqrt`. -/
lemma continuous_pseudoInverseSeminorm (Mdagger : Matrix ι ι ℝ) :
    Continuous (pseudoInverseSeminorm Mdagger) := by
  have h_cont_matVec : Continuous (matVec Mdagger) :=
    ({ toFun := matVec Mdagger
       map_add' := matVec_add Mdagger
       map_smul' := matVec_smul_eq Mdagger } : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
      |>.continuous_of_finiteDimensional
  exact ((Continuous.max continuous_const
    (Continuous.inner continuous_id h_cont_matVec)).sqrt : _)

/-- Core estimate for Lemma 4.11: for the scaled dual path, given `h > 0` and the
LCP solution `(z, w)`, there exists `ξ` such that the difference quotient
of `scaledDualPath lambda w` equals `M ξ` and `⟨ξ, M ξ⟩ ≤ ⟨y, M y⟩` (where `r = M y`).

The proof uses the LCP complementarity to get `⟨Δz, M Δz⟩ ≤ Δs · ⟨r, Δz⟩`,
the bound `|Δs|/h ≤ 1`, and an algebraic inequality for PSD matrices. -/
lemma exists_xi_diff_quot_bound
    (M : Matrix ι ι ℝ) (hM_psd : IsPositiveSemidefinite M)
    (r y : EuclideanSpace ℝ ι) (hy : matVec M y = r)
    (lambda : ℝ) (hlambda_nonneg : 0 ≤ lambda)
    (z w : ℝ → EuclideanSpace ℝ ι)
    (hsol : ∀ μ : ℝ, 0 ≤ μ → isParametricLCP M r lambda μ (z μ) (w μ))
    (μ h : ℝ) (hμ_nonneg : 0 ≤ μ) (hpos : 0 < h) :
    ∃ ξ : EuclideanSpace ℝ ι,
      h⁻¹ • ((scaledDualPath lambda w) (μ + h) - (scaledDualPath lambda w) μ) = matVec M ξ ∧
      inner ℝ ξ (matVec M ξ) ≤ inner ℝ y (matVec M y) := by
  -- Define the scaled paths internally to avoid let-binding issues
  set wt := scaledDualPath lambda w
  set zt : ℝ → EuclideanSpace ℝ ι := fun μ => (1 / (1 + μ * lambda)) • z μ
  set s : ℝ → ℝ := fun μ => μ / (1 + μ * lambda)
  -- Get the full scaled LCP conditions
  have h_scaled_full (ν : ℝ) (hν : 0 ≤ ν) :
      wt ν = -(s ν) • r + ones + matVec M (zt ν) ∧
      Nonnegative (wt ν) ∧ Nonnegative (zt ν) ∧ inner ℝ (wt ν) (zt ν) = 0 :=
    scaled_dual_lcp_eq M r lambda z w hlambda_nonneg hsol ν hν
  have h_scaled_eq (ν : ℝ) (hν : 0 ≤ ν) : wt ν = -(s ν) • r + ones + matVec M (zt ν) :=
    (h_scaled_full ν hν).1
  set α := (s (μ + h) - s μ) / h with hα_def
  set u := h⁻¹ • (zt (μ + h) - zt μ) with hu_def
  set ξ := (-α) • y + u with hξ_def
  have h_eq : h⁻¹ • (wt (μ + h) - wt μ) = matVec M ξ := by
    rw [hξ_def]
    simpa [hα_def, hu_def] using
      scaled_diff_quot_eq_matVec M r y hy wt zt s h_scaled_eq μ h hμ_nonneg hpos
  refine ⟨ξ, h_eq, ?_⟩
  · -- Show inner ℝ ξ (matVec M ξ) ≤ inner ℝ y (matVec M y)
    set d := zt (μ + h) - zt μ with hd_def
    set ds := s (μ + h) - s μ with hds_def
    -- ds > 0 (s is strictly increasing when λ ≥ 0, h > 0)
    have hds_pos : 0 < ds := by
      have h_denom1 : 1 + (μ + h) * lambda ≠ 0 := by nlinarith
      have h_denom2 : 1 + μ * lambda ≠ 0 := by nlinarith
      dsimp [s, ds]
      field_simp [h_denom1, h_denom2]
      nlinarith
    -- Key inequality from LCP complementarity: ⟨d, M d⟩ ≤ ds * ⟨r, d⟩
    have h_quad_le : inner ℝ d (matVec M d) ≤ ds * inner ℝ r d := by
      rcases h_scaled_full (μ + h) (by linarith) with
        ⟨hw_eq₁, hw_nonneg₁, hz_nonneg₁, h_comp₁⟩
      rcases h_scaled_full μ hμ_nonneg with
        ⟨hw_eq₂, hw_nonneg₂, hz_nonneg₂, h_comp₂⟩
      have h_diff_eq : wt (μ + h) - wt μ = -(ds) • r + matVec M d := by
        rw [hw_eq₁, hw_eq₂]
        simp [d, ds, matVec_sub, sub_smul]
        abel_nf
      have h_inner_nonpos : inner ℝ (wt (μ + h) - wt μ) d ≤ 0 := by
        have h := lcp_inner_diff_nonpos (wt μ) (wt (μ + h)) (zt μ) (zt (μ + h))
          hw_nonneg₂ hw_nonneg₁ hz_nonneg₂ hz_nonneg₁ h_comp₂ h_comp₁
        simpa [d] using h
      rw [h_diff_eq] at h_inner_nonpos
      rw [inner_add_left, real_inner_smul_left] at h_inner_nonpos
      -- -(ds) * inner ℝ r d + inner ℝ (matVec M d) d ≤ 0
      rw [real_inner_comm d (matVec M d)] at h_inner_nonpos
      linarith
    -- PSD gives ⟨d, M d⟩ ≥ 0, hence ds * ⟨r, d⟩ ≥ 0, and with ds > 0: ⟨r, d⟩ ≥ 0
    have h_quad_nonneg : 0 ≤ inner ℝ d (matVec M d) := hM_psd.nonneg d
    have h_prod_nonneg : 0 ≤ ds * inner ℝ r d := by linarith
    have h_r_d_nonneg : 0 ≤ inner ℝ r d :=
      nonneg_of_mul_nonneg_right h_prod_nonneg hds_pos
    -- Convert to u, α: ⟨u, M u⟩ ≤ α * ⟨y, M u⟩
    have h_u_bound : inner ℝ u (matVec M u) ≤ α * inner ℝ y (matVec M u) := by
      calc
        inner ℝ u (matVec M u) = inner ℝ (h⁻¹ • d) (matVec M (h⁻¹ • d)) := by
          rw [hu_def, hd_def]
        _ = inner ℝ (h⁻¹ • d) (h⁻¹ • matVec M d) := by rw [matVec_smul_eq]
        _ = (h⁻¹) ^ 2 * inner ℝ d (matVec M d) := by
          simp [real_inner_smul_left, real_inner_smul_right]; ring
        _ ≤ (h⁻¹) ^ 2 * (ds * inner ℝ r d) := by nlinarith
        _ = α * inner ℝ r u := by
          rw [hu_def, hα_def, hds_def, inner_smul_right]
          field_simp [hpos.ne.symm]
        _ = α * inner ℝ (matVec M y) u := by rw [hy]
        _ = α * inner ℝ y (matVec M u) := by
          rw [inner_matVec_comm_of_isSymm M hM_psd.symm y u]
    -- C := ⟨y, M u⟩ ≥ 0
    have h_C_nonneg : 0 ≤ inner ℝ y (matVec M u) := by
      rw [hu_def, hd_def, matVec_smul_eq, inner_smul_right]
      rw [inner_matVec_comm_of_isSymm M hM_psd.symm y d, hy]
      exact mul_nonneg (by positivity) h_r_d_nonneg
    -- Bounds on α: 0 ≤ α ≤ 1
    have h_alpha_nonneg : 0 ≤ α := by
      rw [hα_def]
      exact div_nonneg hds_pos.le hpos.le
    have h_alpha_le_one : α ≤ 1 := by
      have h_bound := scaled_dual_lcp_s_diff_bound lambda hlambda_nonneg
        hμ_nonneg (by linarith : 0 ≤ μ + h)
      -- h_bound: let s := ... in |s μ - s (μ+h)| ≤ |μ - (μ+h)|
      have h_temp : |s μ - s (μ + h)| ≤ h := by
        simpa [s, abs_of_pos hpos] using h_bound
      have h_abs_bound : |ds| ≤ h := by
        have h_eq_abs : |s μ - s (μ + h)| = |ds| := by
          rw [show s μ - s (μ + h) = -(s (μ + h) - s μ) by ring, abs_neg]
        rwa [h_eq_abs] at h_temp
      rw [abs_of_pos hds_pos] at h_abs_bound
      rw [hα_def]
      exact (div_le_one hpos).mpr h_abs_bound
    -- Algebraic core: expand ⟨ξ, M ξ⟩ = α²B + A - 2αC and prove ≤ B
    set B := inner ℝ y (matVec M y)
    set A := inner ℝ u (matVec M u)
    set C := inner ℝ y (matVec M u)
    have hB_nonneg : 0 ≤ B := hM_psd.nonneg y
    have hA_le_alphaC : A ≤ α * C := h_u_bound
    have h_expand : inner ℝ ((-α) • y + u) (matVec M ((-α) • y + u)) =
        α ^ 2 * B + A - 2 * α * C := by
      simpa [B, A, C] using
        inner_matVec_add_smul_sq_eq M hM_psd.symm y u α
    rw [hξ_def, h_expand]
    -- Prove α²B + A - 2αC ≤ B using the algebraic inequality lemma
    exact quad_ineq α A B C hA_le_alphaC h_alpha_nonneg h_alpha_le_one
      hB_nonneg h_C_nonneg

/--
Derivative properties of the scaled dual path derived from the LCP structure.

The scaled dual path `wt(μ) := w(μ)/(1 + μ λ)` satisfies the equation
  `wt(μ) = -s(μ) • r + 1 + M (zt(μ))`   (for μ ≥ 0)
where `s(μ) = μ/(1+μλ)` and `zt(μ) = z(μ)/(1+μλ)`.
Differentiating this equation coordinatewise shows that the derivative lies in `Span M`,
and the seminorm bound follows from the key inequality for difference quotients.

Note: This lemma **requires** the LCP structure (`hdata`, `hsol`) because the
Lipschitz condition alone does not link the path to `M` or `r`.
Source: docs/Lasso.md Section 4.5, Lemma 4.11.
-/
lemma derivative_properties_of_lipschitz
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (z w : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hsol : ∀ μ : ℝ, 0 ≤ μ → isParametricLCP M r lambda μ (z μ) (w μ))
    (h_mp : ∀ v : EuclideanSpace ℝ ι, matVec M (matVec Mdagger (matVec M v)) = matVec M v) :
    (∀ μ, 0 ≤ μ → InMatrixSpan M (deriv (scaledDualPath lambda w) μ)) ∧
    (∀ μ, 0 ≤ μ → pseudoInverseSeminorm Mdagger (deriv (scaledDualPath lambda w) μ) ≤
        pseudoInverseSeminorm Mdagger r) := by
  rcases hdata with ⟨hM_psd, hr_mem_span, hlambda_nonneg⟩
  rcases hr_mem_span with ⟨y, hy⟩
  set wt := scaledDualPath lambda w
  set zt : ℝ → EuclideanSpace ℝ ι := fun μ => (1 / (1 + μ * lambda)) • z μ
  set s : ℝ → ℝ := fun μ => μ / (1 + μ * lambda)
  have h_span : ∀ μ, 0 ≤ μ → InMatrixSpan M (deriv wt μ) :=
    deriv_in_matrix_span_of_scaled_eq M r y hy wt zt s
      (fun μ hμ => (scaled_dual_lcp_eq M r lambda z w hlambda_nonneg hsol μ hμ).1)
  -- Part 2: seminorm bound
  have h_bound : ∀ μ, 0 ≤ μ → pseudoInverseSeminorm Mdagger (deriv wt μ) ≤
      pseudoInverseSeminorm Mdagger r := by
    intro μ hμ_nonneg
    -- We split into cases: wt differentiable at μ vs not.
    by_cases h_diff : DifferentiableAt ℝ wt μ
    · -- wt is differentiable at μ.
      refine le_of_tendsto
        ((continuous_pseudoInverseSeminorm Mdagger).continuousAt.tendsto.comp
          (by simpa using h_diff.hasDerivAt.tendsto_slope_zero_right)) ?_
      refine Filter.eventually_of_mem self_mem_nhdsWithin (fun h hpos => ?_)
      rcases exists_xi_diff_quot_bound M hM_psd r y hy lambda hlambda_nonneg z w hsol
        μ h hμ_nonneg hpos with ⟨ξ, hξ_eq, hξ_bound⟩
      dsimp [pseudoInverseSeminorm]
      exact Real.sqrt_le_sqrt (max_le_max (le_refl 0) (by
        rw [hξ_eq, ← hy]
        simpa [pseudoInverse_inner_prop M Mdagger hM_psd.symm h_mp ξ,
          pseudoInverse_inner_prop M Mdagger hM_psd.symm h_mp y] using hξ_bound))
    · -- When not differentiable, the derivative is 0, and the bound holds trivially.
      rw [deriv_zero_of_not_differentiableAt h_diff]
      simp [pseudoInverseSeminorm, Real.sqrt_nonneg]
  exact ⟨h_span, h_bound⟩

/--
Lemma 4.11 from `docs/Lasso.md`: regularity of the unique dual solution of the
parametric LCP.

Informal proof reference: `docs/Lasso.md`, Section 4.5, Lemma 4.11.
Compare the LCP equations at two parameters `μ` and `μ'` after scaling by
`1 + μ λ`. The difference lies in `Span M`; pairing it with the corresponding
primal difference and using complementarity makes the cross terms nonpositive.
Cauchy--Schwarz gives a Lipschitz estimate, hence absolute continuity, and the
derivative conclusions follow by differentiating the Lipschitz path.
-/
theorem parametric_lcp_dual_regular
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (z w : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hsol : ∀ μ : ℝ, 0 ≤ μ → isParametricLCP M r lambda μ (z μ) (w μ))
    (_hdual_unique :
      ∀ ⦃μ : ℝ⦄, 0 ≤ μ →
        ∀ ⦃z₁ z₂ w₁ w₂ : EuclideanSpace ℝ ι⦄,
          isParametricLCP M r lambda μ z₁ w₁ →
          isParametricLCP M r lambda μ z₂ w₂ →
          w₁ = w₂)
    (hinverse : IsPSDRangeInverse M Mdagger) :
    ParametricLCPDualRegular M Mdagger r lambda w := by
  rcases hdata with ⟨hM_psd, hr_mem_span, hlambda_nonneg⟩
  rcases derivative_properties_of_lipschitz M Mdagger r lambda z w
    ⟨hM_psd, hr_mem_span, hlambda_nonneg⟩ hsol hinverse.range_inverse with
      ⟨h_span, h_bound⟩
  have hw_lipschitz : LocallyLipschitzOnCompacts w :=
    locallyLipschitzOnCompacts_of_scaledDual_lipschitz lambda hlambda_nonneg w
      (scaled_dual_lipschitz M r lambda z w ⟨hM_psd, hr_mem_span, hlambda_nonneg⟩ hsol)
  exact
    { inverse_spec := hinverse
      is_dual_solution := ⟨z, hsol⟩
      locally_lipschitz := hw_lipschitz
      absolutely_continuous := hw_lipschitz.absolutelyContinuous
      scaled_derivative_in_span := h_span
      scaled_derivative_bound := h_bound }

end Lasso

end
