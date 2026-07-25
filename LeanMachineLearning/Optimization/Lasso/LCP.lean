/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Linear Complementarity Problem (LCP) Formulations for Lasso

This file formalizes the primal-dual LCP formulations of the Lasso regularization path.
-/

@[expose] public section

namespace Lasso

variable {ι : Type*} [Fintype ι]

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

/-- Local Lipschitz continuity on every compact interval `[a,b]`. -/
structure LocallyLipschitzOnCompacts (f : ℝ → EuclideanSpace ℝ ι) : Prop where
  lipschitz_on_Icc :
    ∀ a b : ℝ, a ≤ b →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ μ ∈ Set.Icc a b, ∀ ν ∈ Set.Icc a b,
          ‖f μ - f ν‖ ≤ K * |μ - ν|

/-- The scaled dual path `w(μ) / (1 + μ lambda)` from Lemma 4.11. -/
noncomputable def scaledDualPath (lambda : ℝ) (w : ℝ → EuclideanSpace ℝ ι) :
    ℝ → EuclideanSpace ℝ ι :=
  fun μ => (1 / (1 + μ * lambda)) • w μ

/--
The seminorm induced by an explicit matrix used as `M†`.

This avoids hallucinating a Mathlib Moore-Penrose pseudoinverse API.  Once the
project has a canonical pseudoinverse object for finite-dimensional matrices,
the parameter `Mdagger` should be instantiated with that matrix.
-/
noncomputable def pseudoInverseSeminorm
    (Mdagger : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.sqrt (max 0 (inner ℝ x (matVec Mdagger x)))

/--
Regularity package for the unique dual solution of the parametric LCP.
This abstracts the three conclusions of Lemma 4.11: absolute continuity
(represented here by local Lipschitz continuity), derivative in `Span M`, and a
uniform derivative bound in the `M†` seminorm used in `docs/Lasso.md`.
-/
structure ParametricLCPDualRegular
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (w : ℝ → EuclideanSpace ℝ ι) : Prop where
  locally_lipschitz : LocallyLipschitzOnCompacts w
  scaled_derivative_in_span :
    ∀ μ : ℝ, InMatrixSpan M (coordinateDeriv (scaledDualPath lambda w) μ)
  scaled_derivative_bound :
    ∀ μ : ℝ,
      pseudoInverseSeminorm Mdagger (coordinateDeriv (scaledDualPath lambda w) μ) ≤
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
  have h2 : ∑ i, |x.ofLp i| = ∑ i, x.ofLp i := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (hx i)
  have h3 : inner ℝ ones x = ∑ i, x.ofLp i := by
    rw [PiLp.inner_apply]
    simp [ones, euclideanOf]
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
      have : inner ℝ (y - x) (matVec M (y - x)) ≥ 0 := IsPositiveSemidefinite.get_nonneg hM_psd (y - x)
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
    (hμ_small : μ * ‖(WithLp.equiv 2 _).symm (fun i => r i - lambda)‖ < 1) (i : ι) :
    0 < parametricLcpQ r lambda μ i := by
  have h_bound : |r i - lambda| ≤ ‖(WithLp.equiv 2 _).symm (fun i => r i - lambda)‖ := by
    have h := PiLp.norm_apply_le ((WithLp.equiv 2 _).symm (fun j => r j - lambda)) i
    have h_abs : ‖r i - lambda‖ = |r i - lambda| := Real.norm_eq_abs _
    rw [← h_abs]
    exact h
  have h_bound2 : μ * |r i - lambda| ≤ μ * ‖(WithLp.equiv 2 _).symm (fun i => r i - lambda)‖ := by
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

lemma parametric_lcp_unique_small_mu
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hM_psd : IsPositiveSemidefinite M)
    (hμ : 0 ≤ μ)
    (hμ_small : μ * ‖(WithLp.equiv 2 _).symm (fun i => r i - lambda)‖ < 1) :
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
Informal proof: Suppose `y = ∑_{i ∈ s} t_i a_i` with `t_i ≥ 0` and there exists a nontrivial relation
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
      have h1 : (∑ i : {i // i ∈ s}, t' i • a i.val) = ∑ i : {i // i ∈ s}, (t i • a i.val - (θ_fn k) • (c' i • a i.val)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact this x
      rw [h1, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [hc'_sum, smul_zero, sub_zero]
      exact ht_sum
    have h_split : (∑ i : {i // i ∈ s}, t' i • a i.val) = t' k • a k.val + ∑ i ∈ Finset.univ.erase k, t' i • a i.val := by
      have := Finset.sum_erase_add (Finset.univ : Finset {i // i ∈ s}) (fun i => t' i • a i.val) (Finset.mem_univ k)
      rw [←this]
      exact add_comm _ _
    have h_split2 : (∑ i : {i // i ∈ s}, t' i • a i.val) = ∑ i ∈ Finset.univ.erase k, t' i • a i.val := by
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
    have h_eq_sum : (∑ i : {i // i ∈ s.erase (k : κ)}, t'' i • a i.val) = ∑ i ∈ Finset.univ.erase k, t' i • a i.val := by
      have : (∑ i ∈ Finset.univ.erase k, t' i • a i.val) = ∑ i : ((Finset.univ : Finset {i // i ∈ s}).erase k), t' i.val • a i.val.val := by
        exact (Finset.sum_attach ((Finset.univ : Finset {i // i ∈ s}).erase k) (fun i => t' i • a i.val)).symm
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
      have h_eq : (∑ i : {i // i ∈ (Finset.univ : Finset κ)}, coeff i.val • a i.val) = ∑ i : κ, coeff (e.symm i).val • a (e.symm i).val := by
        exact (Equiv.sum_comp e.symm (fun i => coeff i • a i)).symm
      have h_eq2 : (∑ i : κ, coeff (e.symm i).val • a (e.symm i).val) = ∑ i : κ, coeff i • a i := by congr
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
lemma euclideanSpace_finrank_le : Module.finrank ℝ (EuclideanSpace ℝ ι) ≤ Fintype.card ι := by
  exact le_of_eq finrank_euclideanSpace

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
  have h_card_le_finrank := LinearIndependent.fintype_card_le_finrank h_ind
  have h_finrank_le_dim := euclideanSpace_finrank_le (ι := ι)
  have h_fintype_card : Fintype.card {i // i ∈ s} = s.card := Fintype.card_coe s
  rw [← h_fintype_card]
  exact le_trans h_card_le_finrank h_finrank_le_dim

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
      map_add' := sorry
      map_smul' := sorry }
  have h_ker : LinearMap.ker f = ⊥ := by sorry
  have ⟨K, K_pos, hK⟩ := LinearMap.exists_antilipschitzWith f h_ker
  use K
  refine ⟨NNReal.coe_nonneg K, fun x => ?_⟩
  have H := ZeroHomClass.bound_of_antilipschitz f hK (euclideanOf x)
  sorry

/--
The maximum of the constants from `linearIndependent_coefficient_bound` over all linearly
independent subfamilies.
Informal proof: Since `Finset κ` is finite, we can take the maximum over the finite set of
linearly independent subfamilies.
Source: docs/Lasso.md Section 4.3.
-/
lemma max_linearIndependent_coefficient_bound {κ : Type*} (a : κ → EuclideanSpace ℝ ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Finset κ, LinearIndependent ℝ (fun i : {i // i ∈ s} => a i) →
      ∀ x : {i // i ∈ s} → ℝ, (∀ i, 0 ≤ x i) →
        ‖euclideanOf x‖ ≤ C * ‖∑ i : {i // i ∈ s}, x i • a i‖ := by
  sorry

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
    have h_s : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) = ∑ i : {x // x ∈ s}, (x_s i)^2 := by
      have h_eq : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0)^2) =
          ∑ i : {x // x ∈ s}, (if h : i.val ∈ s then x_s ⟨i.val, h⟩ else 0)^2 := (Finset.sum_attach s _).symm
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
  have h_sq_eq : ‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖^2 = ‖euclideanOf x_s‖^2 := by
    rw [h1, h2, ←h3]
  have h_norm_nonneg1 : 0 ≤ ‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖ := norm_nonneg _
  have h_norm_nonneg2 : 0 ≤ ‖euclideanOf x_s‖ := norm_nonneg _
  have h_sqrt : Real.sqrt (‖euclideanOf (fun i => if h : i ∈ s then x_s ⟨i, h⟩ else 0)‖^2) = Real.sqrt (‖euclideanOf x_s‖^2) := by
    rw [h_sq_eq]
  rw [Real.sqrt_sq h_norm_nonneg1, Real.sqrt_sq h_norm_nonneg2] at h_sqrt
  exact h_sqrt

open Classical in
lemma sum_extend_by_zero {κ : Type*} [Fintype κ] (s : Finset κ)
    (x_s : {i // i ∈ s} → ℝ) (a : κ → EuclideanSpace ℝ ι) :
    (∑ i, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) = ∑ i : {i // i ∈ s}, x_s i • a i.val := by
  have h_split : (∑ i, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) =
      (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) +
      (∑ i ∈ sᶜ, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) := (Finset.sum_add_sum_compl s _).symm
  rw [h_split]
  have h_s : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) = ∑ i : {x // x ∈ s}, x_s i • a i.val := by
    have h_eq : (∑ i ∈ s, (if h : i ∈ s then x_s ⟨i, h⟩ else 0) • a i) =
        ∑ i : {x // x ∈ s}, (if h : i.val ∈ s then x_s ⟨i.val, h⟩ else 0) • a i.val := (Finset.sum_attach s _).symm
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

/--
The positive lasso objective achieves its minimum on the non-negative orthant.
Informal proof: The positive lasso objective is a convex quadratic function. Since the problem data
$r$ is in the span of $M$, the objective is bounded below. By the Frank-Wolfe theorem for quadratic
programming, a convex quadratic function bounded below on a polyhedron achieves its minimum.
Source: docs/Lasso.md Section 4.4, Proposition 4.9.
-/
lemma pos_lasso_achieves_minimum
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hdata : ProblemData M r lambda) (hμ : 0 < μ) :
    ∃ x : EuclideanSpace ℝ ι, IsPositiveLassoMinimizer M r lambda μ x := by
  sorry

/--
The dual variable of an LCP solution for a PSD matrix is unique.
Informal proof: Let $(x, v)$ and $(x', v')$ be two solutions. By complementarity,
$\langle v, x \rangle = \langle v', x' \rangle = 0$. Since $v, v', x, x' \ge 0$, we have
$\langle v' - v, x' - x \rangle \le 0$. But $v' - v = M(x' - x)$, so
$\langle M(x' - x), x' - x \rangle \le 0$. Since $M$ is PSD, this implies $M(x' - x) = 0$,
so $v = v'$.
Source: Cottle--Pang--Stone, Theorem 3.1.7(d) referenced in docs/Lasso.md Section 4.4.
-/
lemma psd_lcp_unique_dual
    (M : Matrix ι ι ℝ) (hM_psd : IsPositiveSemidefinite M) (q : EuclideanSpace ℝ ι)
    (x x' v v' : EuclideanSpace ℝ ι)
    (h1 : isLCP M q x v) (h2 : isLCP M q x' v') :
    v = v' := by
  sorry

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
  sorry

/--
The difference of scaled dual variables is bounded by the parameter difference.
Informal proof: Using the LCP equations for scaled variables at $\mu_1, \mu_2$, the difference
$\tilde{w}_1 - \tilde{w}_2$ is in the span of $M$ plus a term proportional to $r (\mu_1 - \mu_2)$.
By taking the inner product with $\tilde{z}_1 - \tilde{z}_2$ and using complementarity slackness,
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
  sorry

/--
If a path is locally Lipschitz, it is differentiable almost everywhere and its derivative inherits
properties from the difference quotients.
Informal proof: Absolutely continuous functions are differentiable almost everywhere
(Rademacher's theorem / Lebesgue differentiation theorem). If the difference quotients
$M(\tilde{z}_1 - \tilde{z}_2)$ satisfy a property, the derivative will as well.
Source: docs/Lasso.md Section 4.5, Lemma 4.11.
-/
lemma derivative_properties_of_lipschitz
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (w : ℝ → EuclideanSpace ℝ ι)
    (hlip : LocallyLipschitzOnCompacts (scaledDualPath lambda w)) :
    (∀ μ : ℝ, InMatrixSpan M (coordinateDeriv (scaledDualPath lambda w) μ)) ∧
    (∀ μ : ℝ, pseudoInverseSeminorm Mdagger (coordinateDeriv (scaledDualPath lambda w) μ) ≤
        pseudoInverseSeminorm Mdagger r) := by
  sorry

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
    (hdual_unique :
      ∀ ⦃μ : ℝ⦄, 0 ≤ μ →
        ∀ ⦃z₁ z₂ w₁ w₂ : EuclideanSpace ℝ ι⦄,
          isParametricLCP M r lambda μ z₁ w₁ →
          isParametricLCP M r lambda μ z₂ w₂ →
          w₁ = w₂) :
    ParametricLCPDualRegular M Mdagger r lambda w := by
  sorry

end Lasso

end
