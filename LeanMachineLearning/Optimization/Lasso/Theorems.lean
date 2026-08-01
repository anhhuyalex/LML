/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import LeanMachineLearning.Optimization.Lasso.LCP
public import LeanMachineLearning.Optimization.Lasso.MirrorFlow
public import LeanMachineLearning.Optimization.Lasso.Definitions
public import LeanMachineLearning.Optimization.Lasso.Bounds.Delta
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Theorems on the Lasso Regularization Path

This file states the main theorem layer for the lasso regularization path
formalization.  Declarations are ordered by proof dependency:

1. path quantities;
2. Section 4.6 positive-path estimates;
3. positive approximate and monotone theorems;
4. Section 5 signed-to-positive reductions;
5. signed approximate and monotone theorems.

This topological order is intentional.  In particular, signed theorems appear
after `lasso_objective_reduction` and `dln_dynamics_reduction`, because their
informal proofs depend on those reductions.
-/

@[expose] public section

namespace Lasso

open Filter Topology MeasureTheory
open scoped ENNReal
variable {ι : Type*} [Fintype ι]
set_option linter.unusedFintypeInType false

/-- The value of `positiveLassoObjective` at the origin is `0`: the quadratic loss vanishes
(since both `⟨0, M0⟩` and `⟨r,0⟩` are `0`) and so does the `L¹` penalty. Used to bound the
"junk" branch of `posLassoMin`'s nested infimum by a genuine feasible point. -/
lemma positiveLassoObjective_zero (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    positiveLassoObjective M r lambda μ 0 = 0 := by
  dsimp [positiveLassoObjective, lassoObjective, quadraticLoss]
  simp

omit [Fintype ι] in
/-- The origin is coordinatewise nonnegative. -/
lemma Nonnegative_zero : Nonnegative (0 : EuclideanSpace ℝ ι) := by
  intro i; simp

/--
`lassoMin` is attained at any selected minimizer, i.e. equals the value of the objective there.
This is the standard "an attained infimum equals the minimizer's value" fact
(`ciInf_le`/`le_ciInf`), specialized to `lassoObjective`; reusable for both the signed and
(via `posLassoMin_eq_of_isPositiveLassoMinimizer` below) the positive lasso.
-/
lemma lassoMin_eq_of_isLassoMinimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) (hx : IsLassoMinimizer M r lambda μ x) :
    lassoMin M r lambda μ = lassoObjective M r lambda μ x := by
  have hbdd : BddBelow (Set.range (lassoObjective M r lambda μ)) :=
    ⟨lassoObjective M r lambda μ x, by
      rintro _ ⟨z, rfl⟩; exact isMinOn_iff.mp hx z (Set.mem_univ z)⟩
  exact le_antisymm (ciInf_le hbdd x) (le_ciInf (fun y => isMinOn_iff.mp hx y (Set.mem_univ y)))

/--
`posLassoMin` is attained at any selected positive minimizer, i.e. equals the value of the
objective there.

Informal proof: `posLassoMin M r lambda μ` unfolds to `⨅ y, g y` where `g y = ⨅ (_h :
Nonnegative y), positiveLassoObjective M r lambda μ y`. For nonnegative `y`, `g y` collapses to
`positiveLassoObjective M r lambda μ y` (the index type `Nonnegative y` is a true proposition,
hence a one-point type, so the inner infimum is constant, `ciInf_const`); for non-nonnegative
`y`, the index type is empty, so `g y` is the junk value `Real.iInf_of_isEmpty _ = 0`. The
selected minimizer `y0` is itself a lower bound for `g` on *every* `y`: on nonnegative `y` this
is minimality (`hy0min`), and on non-nonnegative `y` it follows because `positiveLassoObjective
M r lambda μ y0 ≤ positiveLassoObjective M r lambda μ 0 = 0` (`0` is itself a nonnegative
competitor, so `hy0min` applies to it, and the objective vanishes there by
`positiveLassoObjective_zero`). Hence `y0` minimizes `g` over `Set.univ`, and the
`ciInf_le`/`le_ciInf` argument of `lassoMin_eq_of_isLassoMinimizer` applies to `g`.
-/
lemma posLassoMin_eq_of_isPositiveLassoMinimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y0 : EuclideanSpace ℝ ι) (hmin : IsPositiveLassoMinimizer M r lambda μ y0) :
    posLassoMin M r lambda μ = positiveLassoObjective M r lambda μ y0 := by
  obtain ⟨hy0nn, hy0min⟩ := hmin
  set g : EuclideanSpace ℝ ι → ℝ :=
    fun y => ⨅ (_h : Nonnegative y), positiveLassoObjective M r lambda μ y with hg
  have hg_eq_of_nonneg : ∀ y, Nonnegative y → g y = positiveLassoObjective M r lambda μ y := by
    intro y hy
    rw [hg]
    haveI : Nonempty (Nonnegative y) := ⟨hy⟩
    exact ciInf_const
  have hg_eq_of_not_nonneg : ∀ y, ¬ Nonnegative y → g y = 0 := by
    intro y hy
    rw [hg]
    haveI : IsEmpty (Nonnegative y) := ⟨hy⟩
    exact Real.iInf_of_isEmpty _
  have hg_y0 : g y0 = positiveLassoObjective M r lambda μ y0 := hg_eq_of_nonneg y0 hy0nn
  have hy0_le_zero : positiveLassoObjective M r lambda μ y0 ≤ 0 := by
    have h0 := isMinOn_iff.mp hy0min 0 Nonnegative_zero
    rwa [positiveLassoObjective_zero] at h0
  have hmin_g : IsMinOn g Set.univ y0 := by
    rw [isMinOn_iff]
    intro y _
    by_cases hy : Nonnegative y
    · rw [hg_y0, hg_eq_of_nonneg y hy]
      exact isMinOn_iff.mp hy0min y hy
    · rw [hg_y0, hg_eq_of_not_nonneg y hy]
      exact hy0_le_zero
  have hbdd : BddBelow (Set.range g) :=
    ⟨g y0, by rintro _ ⟨z, rfl⟩; exact isMinOn_iff.mp hmin_g z (Set.mem_univ z)⟩
  have hgmin : (⨅ y, g y) = g y0 :=
    le_antisymm (ciInf_le hbdd y0) (le_ciInf (fun y => isMinOn_iff.mp hmin_g y (Set.mem_univ y)))
  rw [show posLassoMin M r lambda μ = ⨅ y, g y from rfl, hgmin, hg_y0]

/--
The product `μ ↦ μ x(μ)` is locally absolutely continuous on positive compacts because
both `x` and `μ ↦ μ` are.

Informal Proof Outline:
For `μ > 0`, `x(μ)` is locally absolutely continuous (by hypothesis), and the identity
function `μ ↦ μ` is Lipschitz, hence locally absolutely continuous. The product of two locally
absolutely continuous functions is locally absolutely continuous.
-/
lemma scaled_path_ac_on_positive
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    LocallyAbsolutelyContinuousOnPositiveCompacts (scaledPrimalPath x_lasso) := by
  -- Goal: ∀ a b, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval (scaledPrimalPath x_lasso) a b
  refine ⟨fun a b ha hle => ?_⟩
  -- Extract AC of x_lasso on [a,b] from the hypothesis
  have hx_ac : AbsolutelyContinuousOnInterval x_lasso a b :=
    h_regular.absolutelyContinuousOn_Icc a b ha hle
  -- The identity function μ ↦ μ is 1-Lipschitz on any compact interval, hence AC
  -- (pattern from Bounds/Delta.lean:3487; Mathlib: LipschitzOnWith.absolutelyContinuousOnInterval)
  have hid_lip : LipschitzOnWith 1 (fun μ : ℝ => μ) (Set.uIcc a b) :=
    fun x _ y _ => by simp
  have hid_ac : AbsolutelyContinuousOnInterval (fun μ : ℝ => μ) a b :=
    hid_lip.absolutelyContinuousOnInterval
  rw [show scaledPrimalPath x_lasso = (fun μ : ℝ => μ) • x_lasso by ext μ; simp [scaledPrimalPath]]
  exact AbsolutelyContinuousOnInterval.smul hid_ac hx_ac

/--
The scaled primal path is identically zero for all sufficiently small `μ ≥ 0`.

Informal Proof Outline:
By Lemma 4.10 (`parametric_lcp_unique_small_mu`), there exists a threshold
`μ_0 > 0` such that for `0 ≤ μ < μ_0`, the unique solution to the parametric
LCP is `(0, q(μ))`.
For `μ > 0`, since `x(μ)` minimizes the positive lasso, it corresponds to a
solution of the LCP (by `pos_lasso_is_lcp`). Thus `z(μ) = μ x(μ)` solves
the parametric LCP. By uniqueness, `z(μ) = 0` for `0 < μ < μ_0`.
At `μ = 0`, `z(0) = 0 * x(0) = 0`.
-/
-- For small μ > 0, any positive lasso minimizer must be zero.
-- This is a consequence of Lemma 4.10: LCP uniqueness forces the solution to (0, lcpQ)
-- when μ is below the threshold 1 / max(‖r-λ·1‖_∞, 1).
private lemma positive_lasso_minimizer_eq_zero_of_small_mu
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hμ_pos : 0 < μ)
    (hμ_small : μ < 1 / max ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ 1)
    (hx_min : IsPositiveLassoMinimizer M r lambda μ x) : x = 0 := by
  rcases (pos_lasso_is_lcp M r lambda μ x hdata.psd.symm hdata.psd).mp hx_min with ⟨v, hv⟩
  exact ((lcp_eq_iff_of_small_mu M r lambda μ hdata.psd hμ_pos hμ_small x v).mp hv).1

lemma scaled_path_zero_near_zero
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∃ μ_0 > 0, ∀ μ ∈ Set.Icc 0 μ_0, scaledPrimalPath x_lasso μ = 0 := by
  -- The denominator in Lemma 4.10 threshold is positive
  set denom := max ‖(WithLp.equiv ∞ _).symm (fun i => r i - lambda)‖ 1 with hdenom
  have h_denom_pos : 0 < denom := by
    rw [hdenom]
    exact lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1)
  -- Half of the threshold: pick μ_0 = (1 / denom) / 2 so that μ < 1/max(...) for all μ ∈ [0, μ_0]
  refine ⟨(1 / denom) / 2, ?_, ?_⟩
  · -- μ_0 > 0 because denominator > 0
    refine half_pos (div_pos (by norm_num) h_denom_pos)
  · intro μ hμ
    rcases hμ with ⟨hμ_low, hμ_high⟩
    by_cases hμ_zero : μ = 0
    · subst hμ_zero; simp [scaledPrimalPath]
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ_low (Ne.symm hμ_zero)
      have hx_min : IsPositiveLassoMinimizer M r lambda μ (x_lasso μ) := hx_lasso μ hμ_pos
      have hpos : 0 < 1 / denom := div_pos (by norm_num) h_denom_pos
      have hμ_small : μ < 1 / denom := by linarith
      have hx_zero := positive_lasso_minimizer_eq_zero_of_small_mu
        M r lambda μ (x_lasso μ) hdata hμ_pos hμ_small hx_min
      -- Therefore scaledPrimalPath x_lasso μ = μ • x_lasso(μ) = μ • 0 = 0
      dsimp [scaledPrimalPath]
      rw [hx_zero, smul_zero]

/--
If a function is identically zero near zero and locally absolutely continuous on positive compacts,
then it is locally absolutely continuous on nonnegative compacts.

Informal Proof Outline:
Let the function be zero on `[0, μ_0]`. Being constant, it is absolutely continuous on `[0, μ_0/2]`.
For any compact interval `[a, b] ⊂ [0, ∞)`, we can split it at `μ_0/2`. The function is absolutely
continuous on `[a, μ_0/2]` and on `[μ_0/2, b]` (since the latter is a positive compact).
Gluing them together gives absolute continuity on `[a, b]`.
-/
-- For an interval collection whose total length is < δ ≤ c (where c = μ₀/2),
-- each interval either has both endpoints ≤ μ₀ or both endpoints ≥ c.
-- This is because an interval straddling the gap (one < c, other > μ₀) would have
-- length > μ₀ - c = c ≥ δ, contradicting the sum bound.
private lemma interval_case_of_sum_lt (I : ℕ → ℝ × ℝ) (n : ℕ) (μ₀ c δ : ℝ)
    (hc_def : c = μ₀ / 2) (hμ₀_pos : 0 < μ₀) (hδ_le_c : δ ≤ c)
    (h_bound : ∀ i ∈ Finset.range n, 0 ≤ (I i).1 ∧ 0 ≤ (I i).2)
    (h_sum_lt : (∑ i ∈ Finset.range n, dist (I i).1 (I i).2) < δ)
    (i : ℕ) (hi : i < n) : ((I i).1 ≤ μ₀ ∧ (I i).2 ≤ μ₀) ∨ (c ≤ (I i).1 ∧ c ≤ (I i).2) := by
  have hi_range : i ∈ Finset.range n := Finset.mem_range.mpr hi
  rcases h_bound i hi_range with ⟨hx0, hy0⟩
  have h_nonneg : ∀ j ∈ Finset.range n, 0 ≤ dist ((I j).1) ((I j).2) :=
    fun j _ => dist_nonneg
  by_cases hx_le_μ₀ : (I i).1 ≤ μ₀
  · by_cases hy_le_μ₀ : (I i).2 ≤ μ₀
    · left; exact ⟨hx_le_μ₀, hy_le_μ₀⟩
    · right
      have hy_gt_μ₀ : μ₀ < (I i).2 := by linarith
      have hx_ge_c : c ≤ (I i).1 := by
        by_contra! hx_lt_c
        have hdist_gt_c : dist ((I i).1) ((I i).2) > c := by
          rw [Real.dist_eq, abs_sub_comm]
          have hpos : 0 < (I i).2 - (I i).1 := by linarith
          rw [abs_of_pos hpos]
          linarith
        linarith [Finset.single_le_sum h_nonneg hi_range, h_sum_lt, hdist_gt_c, hδ_le_c]
      have hy_ge_c : c ≤ (I i).2 := by linarith
      exact ⟨hx_ge_c, hy_ge_c⟩
  · have hx_gt_μ₀ : μ₀ < (I i).1 := by linarith
    by_cases hy_le_μ₀ : (I i).2 ≤ μ₀
    · right
      have hy_ge_c : c ≤ (I i).2 := by
        by_contra! hy_lt_c
        have hdist_gt_c : dist ((I i).1) ((I i).2) > c := by
          rw [Real.dist_eq]
          have hpos : 0 < (I i).1 - (I i).2 := by linarith
          rw [abs_of_pos hpos]
          linarith
        linarith [Finset.single_le_sum h_nonneg hi_range, h_sum_lt, hdist_gt_c, hδ_le_c]
      have hx_ge_c : c ≤ (I i).1 := by linarith
      exact ⟨hx_ge_c, hy_ge_c⟩
    · right
      have hx_ge_c : c ≤ (I i).1 := by linarith
      have hy_ge_c : c ≤ (I i).2 := by linarith
      exact ⟨hx_ge_c, hy_ge_c⟩

lemma locally_ac_on_nonnegative_of_zero_near_zero_and_ac_on_positive
    (f : ℝ → EuclideanSpace ℝ ι)
    (hf_pos : LocallyAbsolutelyContinuousOnPositiveCompacts f)
    (hf_zero : ∃ μ_0 > 0, ∀ μ ∈ Set.Icc 0 μ_0, f μ = 0) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts f := by
  rcases hf_zero with ⟨μ₀, hμ₀_pos, hf_zero_on⟩
  set c := μ₀ / 2 with hc_def
  have hc_pos : 0 < c := by linarith
  have hc_mem : c ∈ Set.Icc (0 : ℝ) μ₀ := ⟨by linarith, by linarith⟩
  have hfc_zero : f c = 0 := hf_zero_on c hc_mem
  open Set in
  constructor
  intro a b ha_nonneg hab
  rcases eq_or_lt_of_le ha_nonneg with (rfl | ha_pos)
  · -- a = 0
    by_cases hb_le : b ≤ μ₀
    · -- b ≤ μ₀, so f = 0 on [0,b]; constant zero is Lipschitz, hence AC
      have hzero : ∀ x ∈ Set.uIcc (0 : ℝ) b, f x = 0 := by
        intro x hx
        rcases Set.mem_uIcc.1 hx with (⟨hx0, hxb⟩ | ⟨hbx, hx0⟩)
        · exact hf_zero_on x ⟨hx0, hxb.trans hb_le⟩
        · -- x ≤ 0 and b ≤ x, so x = 0 = b
          have hx_eq_0 : x = 0 := by linarith
          subst hx_eq_0
          exact hf_zero_on 0 ⟨le_refl 0, hμ₀_pos.le⟩
      have hlip : LipschitzOnWith (0 : NNReal) f (Set.uIcc (0 : ℝ) b) := by
        intro x hx y hy
        simp [hzero x hx, hzero y hy]
      exact hlip.absolutelyContinuousOnInterval
    · -- b > μ₀: use ε-δ with a clever split at c = μ₀/2
      have h_ac_cb : AbsolutelyContinuousOnInterval f c b :=
        hf_pos.absolutelyContinuousOn_Icc c b hc_pos (by linarith)
      rw [absolutelyContinuousOnInterval_iff] at h_ac_cb ⊢
      intro ε hε
      rcases h_ac_cb ε hε with ⟨δ₁, hδ₁_pos, hδ₁_prop⟩
      set δ := min δ₁ c with hδ_def
      have hδ_pos : 0 < δ := lt_min hδ₁_pos hc_pos
      have hδ_le_c : δ ≤ c := min_le_right _ _
      refine ⟨δ, hδ_pos, ?_⟩
      intro E hE h_sum_len
      rcases hE with ⟨hE_mem, hE_disj⟩
      let n := E.1
      let I := E.2
      -- For each interval, convert membership from uIcc 0 b to concrete bounds
      have hE_mem_Icc : ∀ i ∈ Finset.range n,
          0 ≤ (I i).1 ∧ (I i).1 ≤ b ∧ 0 ≤ (I i).2 ∧ (I i).2 ≤ b := by
        intro i hi
        rcases hE_mem i hi with ⟨hx_mem, hy_mem⟩
        have hx := (Set.mem_Icc.1 (by
          rw [← Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ b)]; exact hx_mem))
        have hy := (Set.mem_Icc.1 (by
          rw [← Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ b)]; exact hy_mem))
        exact ⟨hx.1, hx.2, hy.1, hy.2⟩
      -- Key geometric fact: for each interval, either both endpoints ≤ μ₀, or both ≥ c
      have h_bound : ∀ i ∈ Finset.range n, 0 ≤ (I i).1 ∧ 0 ≤ (I i).2 := by
        intro i hi
        rcases hE_mem_Icc i hi with ⟨hx0, _, hy0, _⟩
        exact ⟨hx0, hy0⟩
      have h_key : ∀ i, i < n → ((I i).1 ≤ μ₀ ∧ (I i).2 ≤ μ₀) ∨ (c ≤ (I i).1 ∧ c ≤ (I i).2) :=
        fun i hi => interval_case_of_sum_lt I n μ₀ c δ hc_def hμ₀_pos hδ_le_c h_bound h_sum_len i hi
      -- Define modified I' that replaces "low" intervals with (c, c)
      let I' : ℕ → ℝ × ℝ := fun i =>
        if (I i).1 ≤ μ₀ ∧ (I i).2 ≤ μ₀ then (c, c) else I i
      -- I' intervals are subsets of I intervals (in the uIoc sense)
      have h_subset : ∀ i, uIoc (I' i).1 (I' i).2 ⊆ uIoc (I i).1 (I i).2 := by
        intro i
        dsimp [I']
        by_cases hi_low : (I i).1 ≤ μ₀ ∧ (I i).2 ≤ μ₀
        · rw [if_pos hi_low]; simp
        · rw [if_neg hi_low]
      -- Hence (n, I') ∈ disjWithin c b
      have hI'_mem : (n, I') ∈ AbsolutelyContinuousOnInterval.disjWithin c b := by
        rw [AbsolutelyContinuousOnInterval.disjWithin]
        refine ⟨?_, ?_⟩
        · intro i hi
          dsimp [I']
          by_cases hi_low : (I i).1 ≤ μ₀ ∧ (I i).2 ≤ μ₀
          · rw [if_pos hi_low]
            exact ⟨Set.left_mem_uIcc, Set.left_mem_uIcc⟩
          · rw [if_neg hi_low]
            rcases h_key i (Finset.mem_range.1 hi) with (⟨hx_le, hy_le⟩ | ⟨hx_ge, hy_ge⟩)
            · exfalso; exact hi_low ⟨hx_le, hy_le⟩
            · rcases hE_mem_Icc i hi with ⟨hx0, hxb, hy0, hyb⟩
              have hx_mem' : (I i).1 ∈ Set.uIcc c b := by
                rw [Set.uIcc_of_le (by linarith : c ≤ b)]
                exact ⟨hx_ge, hxb⟩
              have hy_mem' : (I i).2 ∈ Set.uIcc c b := by
                rw [Set.uIcc_of_le (by linarith : c ≤ b)]
                exact ⟨hy_ge, hyb⟩
              exact ⟨hx_mem', hy_mem'⟩
        · intro i hi j hj hij
          exact (hE_disj hi hj hij).mono (h_subset i) (h_subset j)
      -- Total length of I' ≤ total length of I
      have h_len_I'_le : (∑ i ∈ Finset.range n, dist (I' i).1 (I' i).2) ≤
          (∑ i ∈ Finset.range n, dist (I i).1 (I i).2) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        dsimp [I']
        by_cases hi_low : (I i).1 ≤ μ₀ ∧ (I i).2 ≤ μ₀
        · rw [if_pos hi_low]
          simp [dist_nonneg]
        · rw [if_neg hi_low]
      -- Total variation of I' = total variation of I (low intervals contribute 0 on both sides)
      have h_var_eq : (∑ i ∈ Finset.range n, dist (f (I' i).1) (f (I' i).2)) =
          (∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        dsimp [I']
        by_cases hi_low : (I i).1 ≤ μ₀ ∧ (I i).2 ≤ μ₀
        · rw [if_pos hi_low]
          rcases hi_low with ⟨hx_le, hy_le⟩
          rcases hE_mem_Icc i hi with ⟨hx0, hxb, hy0, hyb⟩
          have hfx : f (I i).1 = 0 := hf_zero_on (I i).1 ⟨hx0, hx_le⟩
          have hfy : f (I i).2 = 0 := hf_zero_on (I i).2 ⟨hy0, hy_le⟩
          simp [hfc_zero, hfx, hfy]
        · rw [if_neg hi_low]
      -- Now apply the ε-δ property for AC on [c, b]
      -- Unfold the let definitions n = E.1, I = E.2 for rewriting
      dsimp [n, I] at h_len_I'_le h_var_eq hI'_mem
      have hδ_le_δ₁ : δ ≤ δ₁ := min_le_left _ _
      have h_len_I'_lt_δ₁ : (∑ i ∈ Finset.range E.1, dist (I' i).1 (I' i).2) < δ₁ := by
        linarith
      simpa [h_var_eq] using hδ₁_prop (E.1, I') hI'_mem h_len_I'_lt_δ₁
  · -- a > 0: directly from hf_pos
    exact hf_pos.absolutelyContinuousOn_Icc a b ha_pos hab

/-- Regularity bridge used between the public statement of Theorem 3.2 and its
scaled-path energy proof.

On `[a,b] ⊂ (0,∞)`, the product `μ ↦ μ x(μ)` is absolutely continuous because
both factors are. Lemma 4.10 says the positive-Lasso minimizer is zero for all
sufficiently small `μ`, so the scaled path is constant near zero; the two
pieces glue on every `[0,b]`. This is the endpoint argument in Sections
4.5--4.6 of <https://arxiv.org/abs/2509.18766>. Mathlib's supported operations
on absolutely continuous functions are documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.

Informal Proof Outline:
1. Let `z(μ) = μ x(μ)`. We must show `z` is locally absolutely continuous on `[0, ∞)`.
2. For `μ > 0`, `x(μ)` is locally absolutely continuous (by hypothesis), and `μ ↦ μ`
   is Lipschitz. Thus their product `z(μ)` is locally absolutely continuous on `(0, ∞)`.
3. By Lemma 4.10 (`parametric_lcp_unique_small_mu`), there exists a threshold
   `μ_0 > 0` such that for `0 ≤ μ < μ_0`, the unique solution to the parametric
   LCP is `(0, q(μ))`.
4. For `μ > 0`, since `x(μ)` minimizes the positive lasso, it corresponds to a
   solution of the LCP (by `pos_lasso_is_lcp`). Thus `z(μ) = μ x(μ)` solves
   the parametric LCP.
5. By uniqueness, `z(μ) = 0` for `0 < μ < μ_0`. At `μ = 0`, `z(0) = 0 * x(0) = 0`.
6. Therefore, `z` is identically zero on `[0, μ_0/2]`, making it absolutely
   continuous on that interval.
7. For any compact interval `[a, b] ⊂ [0, ∞)`, we can split it at `μ_0/2`. `z` is
   absolutely continuous on `[a, μ_0/2]` and on `[μ_0/2, b]`, so it is absolutely
   continuous on `[a, b]`.
-/
theorem scaledPrimalPath_regular_of_path_regular
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) := by
  exact locally_ac_on_nonnegative_of_zero_near_zero_and_ac_on_positive
    (scaledPrimalPath x_lasso)
    (scaled_path_ac_on_positive x_lasso h_regular)
    (scaled_path_zero_near_zero M r lambda x_lasso hdata hx_lasso)

-- For μ ≠ 0, scaling lcpQ by μ yields parametricLcpQ
omit [Fintype ι] in
private lemma lcpQ_smul_eq_parametricLcpQ (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) (hμ : μ ≠ 0) :
    μ • lcpQ r lambda μ = parametricLcpQ r lambda μ := by
  ext i
  dsimp [lcpQ, parametricLcpQ, euclideanOf]
  field_simp [hμ]
  ring

/--
For `μ > 0`, if `x` minimizes the positive lasso, there exists a dual solution `w` such that
the scaled primal and dual vectors solve the parametric LCP.

Informal Proof Outline:
For `μ > 0`, `x(μ)` satisfies the KKT conditions for the positive lasso, meaning it solves the
standard LCP (`pos_lasso_is_lcp`). By scaling the standard LCP by `μ`, we obtain a solution
to the `parametricLcpQ` LCP. This corresponds to setting `w = μ v` where `v` is the standard dual.
(Source: docs/Lasso.md Section 4.5).
-/
lemma exists_parametric_lcp_solution_for_positive_lasso
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hμ : 0 < μ)
    (hx_lasso : IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∃ w : EuclideanSpace ℝ ι, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) w := by
  -- Step 1: pos_lasso_is_lcp turns the positive Lasso minimizer into a standard LCP solution
  rcases ((pos_lasso_is_lcp M r lambda μ (x_lasso μ) hdata.psd.get_symm hdata.psd).mp hx_lasso) with
    ⟨v, hv_eq, hv_nonneg, hx_nonneg, hvx_zero⟩
  -- Step 2: scale the dual variable by μ to obtain the parametric LCP witness
  use μ • v
  -- Step 3: unfold the goal and verify the four LCP conditions
  dsimp [isParametricLCP, isLCP, scaledPrimalPath]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Condition 1: stationarity (μ·v = parametricLcpQ + M(μ·x))
    rw [hv_eq, smul_add, lcpQ_smul_eq_parametricLcpQ r lambda μ hμ.ne.symm, matVec_smul_eq]
  · -- Condition 2: dual feasibility (μ·v ≥ 0)
    exact fun i => mul_nonneg hμ.le (hv_nonneg i)
  · -- Condition 3: primal feasibility (μ·x ≥ 0)
    exact fun i => mul_nonneg hμ.le (hx_nonneg i)
  · -- Condition 4: complementarity ⟨μ·v, μ·x⟩ = 0
    simp [inner_smul_right, inner_smul_left, hvx_zero]

/--
At `μ = 0`, the origin and the all-ones vector solve the parametric LCP.

Informal Proof Outline:
At `μ = 0`, `z = 0`. The parametric LCP data is `q(0) = 1 > 0`.
Setting `w = 1` satisfies the LCP since `w ≥ 0`, `z ≥ 0`, and `z^T w = 0`.
(Source: docs/Lasso.md Section 4.5).
-/
lemma exists_parametric_lcp_solution_at_zero
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι) :
    ∃ w : EuclideanSpace ℝ ι, isParametricLCP M r lambda 0 (scaledPrimalPath x_lasso 0) w := by
  use parametricLcpQ r lambda 0
  have hz0 : scaledPrimalPath x_lasso 0 = 0 := by ext i; simp [scaledPrimalPath]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hz0, matVec, euclideanOf]
  · intro i; simp [parametricLcpQ, euclideanOf]
  · rw [hz0]; exact Nonnegative_zero
  · simp [hz0]

/--
Given that `w(μ)` can be constructed piecewise to solve the parametric LCP,
and because the dual solution of an LCP with PSD matrix is unique (`psd_lcp_unique_dual`),
the dual trajectory satisfies the regularity package `ParametricLCPDualRegular`.

(We use `Classical.choose` on the existence lemmas to build `w`).
-/
lemma dual_certificate_regularity
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hinverse : IsPSDRangeInverse M Mdagger)
    (hsol : ∀ μ ≥ 0, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ)) :
    ParametricLCPDualRegular M Mdagger r lambda w :=
  parametric_lcp_dual_regular M Mdagger r lambda _ _ hdata hsol
    (fun μ _ => psd_lcp_unique_dual M hdata.psd (parametricLcpQ r lambda μ))
    hinverse
/-- Construct the auxiliary Moore--Penrose/LCP data from the selected positive
Lasso minimizer path.

The KKT conditions for the constrained convex quadratic give the dual slack
`w(μ)` and show that `(μx(μ),w(μ))` solves the parametric LCP. A symmetric PSD
matrix has a PSD Moore--Penrose inverse by diagonalizing it and inverting the
positive eigenvalues; Lemma 4.11 then supplies the regularity package. See
Sections 4.4--4.5 of <https://arxiv.org/abs/2509.18766>, the KKT development in
Boyd--Vandenberghe <https://web.stanford.edu/~boyd/cvxbook/>, and the spectral
construction of the pseudoinverse in <https://arxiv.org/abs/1110.6882>.

Informal Proof Outline:
1. By `exists_psd_range_inverse`, let `Mdagger` be a matrix satisfying
   `IsPSDRangeInverse M Mdagger`.
2. For each `μ > 0`, `lcp_exists_unique_dual` gives a unique dual slack `v(μ)`
   such that `isLCP M (lcpQ r lambda μ) (x(μ)) (v(μ))` holds. Let `w(μ) = μ v(μ)`.
3. For `μ = 0`, set `w(0) = parametricLcpQ r lambda 0 = 1`.
4. Then for all `μ ≥ 0`, `(z(μ), w(μ))` solves the parametric LCP.
5. Because `w(μ)` is the unique dual solution of the parametric LCP, Lemma 4.11
   (`parametric_lcp_dual_regular`) applies and provides the full regularity
   package `ParametricLCPDualRegular M Mdagger r lambda w`.
6. Thus `Mdagger` and `w` witness the existential quantifiers.
-/
theorem exists_dual_certificate_for_positive_path
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∃ Mdagger : Matrix ι ι ℝ, ∃ w : ℝ → EuclideanSpace ℝ ι,
      ParametricLCPDualRegular M Mdagger r lambda w ∧
        ∀ μ, 0 ≤ μ →
          isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ) := by
  rcases exists_psd_range_inverse M hdata.psd.symm hdata.psd with ⟨Mdagger, hinverse⟩
  use Mdagger
  -- Construct w piecewise using Classical.choose
  have hw_pos : ∀ μ > 0, ∃ w, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) w :=
    fun μ hμ =>
      exists_parametric_lcp_solution_for_positive_lasso
        M r lambda μ x_lasso hdata hμ (hx_lasso μ hμ)
  have hw_zero : ∃ w, isParametricLCP M r lambda 0 (scaledPrimalPath x_lasso 0) w :=
    exists_parametric_lcp_solution_at_zero M r lambda x_lasso
  let w : ℝ → EuclideanSpace ℝ ι := fun μ =>
    if hμ : μ > 0 then Classical.choose (hw_pos μ hμ)
    else if μ = 0 then Classical.choose hw_zero
    else 0 -- arbitrary for negative μ
  use w
  have hsol : ∀ μ ≥ 0, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ) := by
    intro μ hμ
    dsimp [w]
    split_ifs with h_pos h_zero
    · exact Classical.choose_spec (hw_pos μ h_pos)
    · have h_eq : μ = 0 := le_antisymm (not_lt.1 h_pos) hμ
      subst h_eq
      exact Classical.choose_spec hw_zero
    · exfalso
      exact h_zero (le_antisymm (not_lt.1 h_pos) hμ)
  constructor
  · exact dual_certificate_regularity M Mdagger r lambda x_lasso w hdata hinverse hsol
  · exact hsol

/--
Helper lemma: integration of `positive_energy_differential_inequality`.
This uses the FTC and the boundary condition `initial_positive_energy_zero` to conclude
an upper bound on the energy $E^\varepsilon(s)$.

Informal proof: Integrate `positive_energy_differential_inequality` from 0 to $s$.
By FTC and `initial_positive_energy_zero`, the integral evaluates exactly to the energy
at time $s$ scaled by $1 / (1 + s \lambda)$. The right-hand side is bounded by substituting
the uniform bound on $\Delta^\varepsilon(\tau)$ from `positive_path_delta_bound`.

**Status (verified 2026-07-31): genuinely blocked on incomplete upstream infrastructure, not
just unassembled.** `Bounds/Energy.lean` (1012 lines, `lake env lean` succeeds with 0 errors)
contains the two named ingredients:
* `initial_positive_energy_zero` (`Bounds/Energy.lean:968`) — fully proved, no sorry.
* `positive_energy_differential_inequality` (`Bounds/Energy.lean:885`) — its *statement* matches
  this lemma's integrand exactly, but its proof calls `energy_complementarity_bound`
  (`Energy.lean:659`), which in turn calls `energy_deriv_bound_kink_case` (`Energy.lean:425`)
  and `energy_deriv_bound_zero_case` (`Energy.lean:474`), each of which still has `sorry`s
  (`Energy.lean:443,445,449,528,531`, all about non-differentiability of `w` / `φ • w` at kink
  points and at `ε`-independent zero-locus points). So `positive_energy_differential_inequality`
  is *not* actually usable yet, only its statement is trustworthy.
* The Delta-bound half, `positive_path_delta_bound` (`Bounds/Delta.lean:3667`), *is* fully
  proved, no sorry.

Both `positive_energy_differential_inequality` and `positive_path_delta_bound` additionally
require two hypotheses this lemma does not currently take: `h_lipschitz :
LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)` and `h_local_affine :
ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso` (both defined in `Bounds/Delta.lean`).
These would need to be added to this lemma's signature (and threaded through from its callers,
which currently only carry `h_regular`).

**To complete this lemma**: (1) fill the 5 sorries in `Bounds/Energy.lean`'s two kink/zero-case
helper lemmas; (2) add `h_lipschitz`/`h_local_affine` hypotheses here and thread them from
`positive_path_energy_bound`; (3) `public import LeanMachineLearning.Optimization.Lasso.Bounds.
Energy` into `Theorems.lean`; (4) perform the FTC/Gronwall-style integration of the differential
inequality from `0` to `s`, using `initial_positive_energy_zero` as the boundary condition and
`positive_path_delta_bound` to bound the `Δ^ε` term appearing on the differential inequality's
right-hand side — this final integration step is not yet written anywhere in the codebase and
is themselves nontrivial (comparison of a scalar ODE inequality against its bound, standard but
not close to a one-line Mathlib lemma). See Section 4.6 ("Proof of Theorem 3.2") of
<https://arxiv.org/abs/2509.18766> for the informal mathematical argument this formalizes.
-/
lemma positive_energy_integrated_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      inner ℝ (w s) (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s) +
        pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
          (scaledPrimalPath x_lasso) s
      ≤ s^2 * (C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ) := by
  sorry

/--
Algebraic identity rewriting the difference of positive lasso objectives as
an energy inner product.  Extracted from `Bounds/Energy.lean` so that this
file does not depend on that module's currently broken proofs.
-/
lemma positiveLassoObjective_eq_energy
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (s : ℝ) (_hs : 0 < s)
    (z zε : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ ι)
    (hx_nonneg : Nonnegative (s⁻¹ • z)) (hxE_nonneg : Nonnegative (s⁻¹ • zε))
    (hw_eq : matVec M (s⁻¹ • z) + lcpQ r lambda s = s⁻¹ • w)
    (hM_symm : M.IsSymm) :
    positiveLassoObjective M r lambda s (s⁻¹ • zε) - positiveLassoObjective M r lambda s (s⁻¹ • z) =
      s⁻¹ ^ 2 * (inner ℝ w (zε - z) + (1 / 2 : ℝ) * inner ℝ (zε - z) (matVec M (zε - z))) := by
  rw [positiveLassoObjective_eq M r lambda s (s⁻¹ • zε) hxE_nonneg,
    positiveLassoObjective_eq M r lambda s (s⁻¹ • z) hx_nonneg,
    quadratic_expansion M (lcpQ r lambda s) (s⁻¹ • z) (s⁻¹ • zε) hM_symm, hw_eq]
  rw [(smul_sub s⁻¹ zε z).symm, matVec_smul_eq, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right]
  ring

/--
Section 4.6 final estimate: the `Δε` control implies the positive-lasso
objective suboptimality bound of Theorem 3.2.

Informal proof reference: `docs/Lasso.md`, Section 4.6.

Informal Proof Outline:
1. Use `positiveLassoObjective_eq_energy` to rewrite the objective gap
   `Lasso(xε) - Lasso(x)` as `1/s^2 * E^\varepsilon(s)`.
2. Apply `positive_energy_differential_inequality` to bound the derivative of `E^\varepsilon(\tau)`.
3. Integrate this bound from `τ = 0` to `τ = s`.
4. Use `initial_positive_energy_zero` to show that the integral evaluates
   exactly to `E^\varepsilon(s)`.
5. Substitute the integrated `Δ^\varepsilon(τ)` bound from `positive_path_delta_bound`.
6. Conclude the limit bound for `E^\varepsilon(s) / s^2`, which matches
   `suboptimalityGap` as `ε → 0`.
-/
theorem positive_path_energy_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_regular :
      LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  /-
  INFORMAL PROOF. Integrate the uniform-in-`s` delta and energy differential
  inequalities of Section 4.6, use the zero initial energy, and divide by
  `s²`. The constants in Lemmas 4.1--4.11 depend only on the fixed problem
  data and initialization, so one `C` works for every `s > 0`. This is the
  calculation concluding Theorem 3.2 in <https://arxiv.org/abs/2509.18766>;
  the absolute-continuity/FTC step is supported by Mathlib's interval-integral
  API <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.html>.
  -/
  obtain ⟨C, hC_pos, h_energy_bound⟩ :=
    positive_energy_integrated_bound M Mdagger r lambda β u hdata hβ hu
      x_lasso hx_lasso w hdual hdual_selected h_regular
  use C, hC_pos
  intro s hs δ hδ
  have hs_inv_pos : 0 < s⁻¹ := inv_pos.mpr hs
  have hs2_pos : 0 < s^2 := pow_pos hs 2
  have hs_inv2_pos : 0 < s⁻¹ ^ 2 := pow_pos hs_inv_pos 2
  filter_upwards [h_energy_bound s hs δ hδ] with ε hε
  have hw_eq : matVec M (s⁻¹ • scaledPrimalPath x_lasso s) + lcpQ r lambda s = s⁻¹ • w s := by
    -- From hdual_selected s hs, we have isParametricLCP.
    -- The first condition is exactly what we need, after identifying w(s) with the slack.
    have hlcp := hdual_selected s hs.le
    obtain ⟨hw_eq0, -, -, -⟩ := hlcp
    have hscale : parametricLcpQ r lambda s = s • lcpQ r lambda s :=
      (lcpQ_smul_eq_parametricLcpQ r lambda s hs.ne').symm
    rw [hscale] at hw_eq0
    have hgoal :
        s⁻¹ • w s = s⁻¹ • (s • lcpQ r lambda s + matVec M (scaledPrimalPath x_lasso s)) := by
      rw [hw_eq0]
    rw [hgoal, smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, ← matVec_smul_eq]
    abel
  have hx_nonneg : Nonnegative (s⁻¹ • scaledPrimalPath x_lasso s) := by
    obtain ⟨-, -, hz_nonneg, -⟩ := hdual_selected s hs.le
    intro i
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_pos.mpr hs).le (hz_nonneg i)
  have hxE_nonneg : Nonnegative (s⁻¹ • posIntegratedTrajectoryRescaled ε (u ε) s) := by
    -- `t ↦ t⁻¹ • posIntegratedTrajectory u t` is nonnegative for *every* real `t`, not just
    -- `t ≥ 0`: for `t < 0`, `∫₀ᵗ (nonneg) = -∫ₜ⁰ (nonneg) ≤ 0` cancels the sign of `t⁻¹ < 0`.
    have hgen : ∀ t : ℝ, Nonnegative (t⁻¹ • posIntegratedTrajectory (u ε) t) := by
      intro t
      rcases lt_trichotomy t 0 with ht | ht | ht
      · intro i
        simp only [PiLp.smul_apply, smul_eq_mul]
        have hti : (posIntegratedTrajectory (u ε) t) i ≤ 0 := by
          dsimp [posIntegratedTrajectory, euclideanOf]
          rw [intervalIntegral.integral_symm t 0, neg_nonpos]
          exact intervalIntegral.integral_nonneg ht.le
            (fun v _ => posEffectiveParameter_nonnegative (u ε) v i)
        nlinarith [inv_nonpos.mpr ht.le]
      · subst ht; intro i; simp
      · intro i
        simp only [PiLp.smul_apply, smul_eq_mul]
        have hti : 0 ≤ (posIntegratedTrajectory (u ε) t) i := by
          dsimp [posIntegratedTrajectory, euclideanOf]
          exact intervalIntegral.integral_nonneg ht.le
            (fun v _ => posEffectiveParameter_nonnegative (u ε) v i)
        exact mul_nonneg (inv_nonneg.mpr ht.le) hti
    have heq : s⁻¹ • posIntegratedTrajectoryRescaled ε (u ε) s =
        (posTimeFromRescaled ε s)⁻¹ • posIntegratedTrajectory (u ε) (posTimeFromRescaled ε s) := by
      dsimp [posIntegratedTrajectoryRescaled]
      rw [smul_smul]
      congr 1
      rcases eq_or_ne (Real.log (1 / ε)) 0 with hL | hL
      · dsimp [posTimeFromRescaled]; rw [hL]; simp
      · dsimp [posTimeFromRescaled]; field_simp
    rw [heq]
    exact hgen _
  have h_obj_gap := positiveLassoObjective_eq_energy M r lambda s hs
    (scaledPrimalPath x_lasso s) (posIntegratedTrajectoryRescaled ε (u ε) s) (w s)
    hx_nonneg hxE_nonneg hw_eq hdata.psd.symm
  -- The definition of pathDelta is exactly the quadratic term with M
  have h_delta_eq : (1 / 2 : ℝ) *
      inner ℝ (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s)
      (matVec M (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s)) =
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) s := by
    rfl
  rw [h_delta_eq] at h_obj_gap
  have h_average_eq : posAverageTrajectory (u ε) (posTimeFromRescaled ε s) =
      s⁻¹ • posIntegratedTrajectoryRescaled ε (u ε) s := by
    have h1 : posAverageTrajectory (u ε) (posTimeFromRescaled ε s) =
        (posTimeFromRescaled ε s)⁻¹ • posIntegratedTrajectory (u ε) (posTimeFromRescaled ε s) := by
      ext i
      dsimp [posAverageTrajectory, posIntegratedTrajectory, euclideanOf]
      rw [one_div]
    rw [h1]
    dsimp [posIntegratedTrajectoryRescaled]
    rw [smul_smul]
    congr 1
    rcases eq_or_ne (Real.log (1 / ε)) 0 with hL | hL
    · dsimp [posTimeFromRescaled]; rw [hL]; simp
    · dsimp [posTimeFromRescaled]; field_simp
  rw [h_average_eq]
  have h_lasso_min_eq : posLassoMin M r lambda s =
      positiveLassoObjective M r lambda s (s⁻¹ • scaledPrimalPath x_lasso s) := by
    have heq : s⁻¹ • scaledPrimalPath x_lasso s = x_lasso s := by
      dsimp [scaledPrimalPath]
      rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [heq]
    exact posLassoMin_eq_of_isPositiveLassoMinimizer M r lambda s (x_lasso s) (hx_lasso s hs)
  rw [h_lasso_min_eq]
  -- We now have positiveLassoObjective (...) - positiveLassoObjective (...) in h_obj_gap.
  -- Rearranging the inequality:
  -- A - B = s⁻¹ ^ 2 * E
  -- E ≤ s^2 * (C * gap + δ)
  -- So A - B ≤ s⁻¹ ^ 2 * s^2 * (C * gap + δ) = C * gap + δ
  -- So A ≤ B + C * gap + δ
  have h_gap_bound :
      positiveLassoObjective M r lambda s
        (s⁻¹ • posIntegratedTrajectoryRescaled ε (u ε) s) -
      positiveLassoObjective M r lambda s
        (s⁻¹ • scaledPrimalPath x_lasso s)
      ≤ C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
    rw [h_obj_gap]
    calc
      s⁻¹ ^ 2 *
          (inner ℝ (w s)
            (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s) +
          pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
            (scaledPrimalPath x_lasso) s)
        ≤ s⁻¹ ^ 2 *
          (s^2 * (C * suboptimalityGap lambda s
            (positiveZDownward x_lasso s) + δ)) := by
        exact mul_le_mul_of_nonneg_left hε hs_inv2_pos.le
      _ = (s⁻¹ ^ 2 * s^2) *
          (C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ) := by
        rw [mul_assoc]
      _ = C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
        have h_inv : s⁻¹ ^ 2 * s ^ 2 = 1 := by
          rw [← mul_pow]
          rw [inv_mul_cancel₀ hs.ne']
          exact one_pow 2
        rw [h_inv, one_mul]
  linarith [h_gap_bound]

/-! ## Positive-lasso main theorems -/

/--
Theorem 3.2: an approximate connection to the positive lasso minimum in the
general case.

Informal proof reference: `docs/Lasso.md`, Section 4.6.  This theorem is now
placed after the delta and energy estimates that prove it.
-/
theorem pos_lasso_connection_approx
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  obtain ⟨Mdagger, w, hdual, hdual_selected⟩ :=
    exists_dual_certificate_for_positive_path M r lambda x_lasso hdata hx_lasso
  have h_reg_nonneg :
      LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) :=
    scaledPrimalPath_regular_of_path_regular
      M r lambda x_lasso hdata hx_lasso h_regular
  exact positive_path_energy_bound
    M Mdagger r lambda β u hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_reg_nonneg

/--
Lemma 4.12 from `docs/Lasso.md`: under the monotonicity hypothesis of Theorem
3.1, the scaled positive-lasso path has enough compact-interval regularity to
apply Theorem 3.2.

Informal proof reference: Section 4.7, Lemma 4.12. Lemma 4.11 gives local
Lipschitz control of the dual path and hence of the projection of `z(μ)` onto
`Span M`. Complementarity controls the kernel component; monotonicity converts
coordinatewise variation into an `L¹` bound on compact intervals.

**Status (verified 2026-07-31): the generic Lipschitz⟹AC machinery exists and matches, but
one genuinely new hypothesis (LCP-solution uniqueness) is needed and not yet available.**
`Bounds/Delta.lean` already contains a general lemma exactly shaped for this:

```
lemma parametric_lcp_lipschitz
    (M) (r) (lambda) (z : ℝ → EuclideanSpace ℝ ι) (hdata)
    (h_lcp : ∀ μ ≥ 0, isLCP M (parametricLcpQ r lambda μ) (z μ)
      (matVec M (z μ) + parametricLcpQ r lambda μ))
    (h_unique : ∀ μ ≥ 0, ∀ z', isLCP M (parametricLcpQ r lambda μ) z'
      (matVec M z' + parametricLcpQ r lambda μ) → z' = z μ)
    (h_mono : ∀ μ ν, 0 ≤ μ → μ ≤ ν → ∀ i, z μ i ≤ z ν i) :
    LocallyLipschitzOnCompacts z
```
(`Bounds/Delta.lean:2259`), and `LocallyLipschitzOnCompacts.absolutelyContinuous`
(`LCP.lean:90`) turns its conclusion directly into this lemma's goal (applied to `z :=
scaledPrimalPath x_lasso`).

What is missing to invoke it:
* `h_lcp` and the `isLCP`-vs-`isParametricLCP` argument-order match: this is exactly the
  content of `exists_parametric_lcp_solution_for_positive_lasso` (this file, already proved)
  plus `exists_parametric_lcp_solution_at_zero` (already proved), bridged through
  `pos_lasso_is_lcp` (`LCP.lean:633`), giving existence of *a* dual `v(μ)` with `w(μ) =
  matVec M (z μ) + parametricLcpQ r lambda μ` for each `μ ≥ 0`.
* `h_mono` follows directly from `h_monotone` together with `scaledPrimalPath x_lasso μ i = μ *
  x_lasso μ i` — routine.
* `h_unique`, the genuinely missing piece: `parametric_lcp_lipschitz` needs the *selected*
  `z μ = scaledPrimalPath x_lasso μ` to be the **unique** solution of the LCP at every `μ`, not
  merely *a* solution. This is not automatic for a merely-PSD (not positive-definite) `M`: the
  LCP solution set can have multiple primal points differing along `ker M` in general (e.g.
  `M = 0, q = 0` admits every nonnegative `z`). `parametric_lcp_lipschitz`'s own proof sketch
  (comments at `Delta.lean:2323-2334`) explains why uniqueness *does* hold for this specific
  family: the kernel component of `q(μ) = (1 + μλ) • 1` is strictly positive for `λ, μ ≥ 0`,
  which (via complementarity) forces the kernel component of any solution to vanish. Formalizing
  this — i.e. proving `h_unique` as a standalone fact about `IsPositiveLassoMinimizer`-selected
  paths — is not yet done anywhere in the codebase and is a nontrivial piece of linear algebra
  (needs `IsPSDRangeInverse`/pseudoinverse machinery already present for the *dual* uniqueness
  argument `psd_lcp_unique_dual` at `LCP.lean:1634`, adapted to primal uniqueness).

See Lemma 4.12 of <https://arxiv.org/abs/2509.18766> and Mathlib's implication
Lipschitz `⇒` absolutely continuous
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.
-/
theorem monotone_positive_path_regular
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) := by
  sorry

/--
Theorem 3.1: under monotonicity, the positive average trajectory exactly
connects to the positive lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 4.7.  Unlike the earlier
skeleton, this statement no longer assumes compact-interval regularity as an
extra hypothesis; that regularity is supplied by `monotone_positive_path_regular`.
-/
theorem pos_lasso_connection_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        positiveLassoObjective M r lambda s
          (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (posLassoMin M r lambda s)) := by
  /-
  INFORMAL PROOF. Lemma 4.12 supplies the regularity needed by Theorem 3.2.
  A coordinatewise nondecreasing absolutely continuous `z` has nonnegative
  derivative almost everywhere, so `positiveZDownward x_lasso s = 0`.
  The approximate upper bound therefore has zero error term; feasibility of
  the averaged positive trajectory supplies the matching lower bound. See
  Sections 4.6--4.7 of <https://arxiv.org/abs/2509.18766> and the standard
  a.e.-derivative characterization of absolute continuity
  <https://en.wikipedia.org/wiki/Absolute_continuity>.

  Status (verified 2026-07-31): blocked transitively on `monotone_positive_path_regular`
  (still sorry, see its docstring for exactly what's missing) and on
  `pos_lasso_connection_approx`'s upstream `positive_energy_integrated_bound` (also still
  sorry, likewise documented). Given those two, the assembly here should mirror the *already
  proved* signed-case theorem `lasso_connection_monotone` (this file): squeeze via
  `tendsto_of_tendsto_of_tendsto_of_le_of_le'` between the constant `posLassoMin M r lambda s`
  (lower bound, via `posLassoMin_eq_of_isPositiveLassoMinimizer`/`ciInf_le`-style feasibility,
  as in that proof's first bullet) and `pos_lasso_connection_approx`'s upper bound specialized
  to `positiveZDownward x_lasso s = 0`. The extra fact needed for that specialization —
  "coordinatewise nondecreasing + absolutely continuous ⟹ a.e. nonnegative derivative ⟹ the
  `max 0 (-deriv ⋯)` integrand defining `positiveZDownward` vanishes a.e. ⟹ the integral is
  `0`" — is a standard consequence of `MonotoneOn.deriv_nonneg`-type facts (search Mathlib for
  the exact monotone-derivative-sign lemma) combined with `intervalIntegral.integral_eq_zero_iff`
  or a direct a.e.-nonneg-integrand argument; it is not yet stated anywhere in this codebase.
  -/
  sorry

/-! ## Section 5: signed-to-positive reductions -/

/-- Positive part of a coordinate vector. -/
noncomputable def coordinatePositivePart (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => max (x i) 0)

/-- Negative part of a coordinate vector, as a nonnegative vector. -/
noncomputable def coordinateNegativePart (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => max (-(x i)) 0)

/-- Canonical signed-to-positive split `x ↦ (x_+, x_-)`. -/
noncomputable def signedCanonicalSplit (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm
    (Sum.elim (coordinatePositivePart x) (coordinateNegativePart x))

/-- `signedCanonicalSplit` is `2`-Lipschitz (a coarse constant; `√2` is tight): each of the
two block coordinates is `1`-Lipschitz in the ambient coordinate (`abs_max_sub_max_le_abs`), so
`dist (signedCanonicalSplit x) (signedCanonicalSplit y) ^ 2 ≤ 2 * dist x y ^ 2 ≤ (2 * dist x y)^2`
by `EuclideanSpace.dist_sq_eq` on both sides. -/
lemma lipschitzWith_signedCanonicalSplit :
    LipschitzWith 2 (signedCanonicalSplit : EuclideanSpace ℝ ι → EuclideanSpace ℝ (ι ⊕ ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hsq : dist (signedCanonicalSplit x) (signedCanonicalSplit y) ^ 2 ≤
      ((2 : NNReal) * dist x y) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hsplit : (∑ j : ι ⊕ ι, dist (signedCanonicalSplit x j) (signedCanonicalSplit y j) ^ 2) =
        (∑ i : ι, dist (signedCanonicalSplit x (Sum.inl i))
          (signedCanonicalSplit y (Sum.inl i)) ^ 2) +
          ∑ i : ι, dist (signedCanonicalSplit x (Sum.inr i))
            (signedCanonicalSplit y (Sum.inr i)) ^ 2 :=
      Fintype.sum_sum_type _
    rw [hsplit]
    have hterm_inl : ∀ i : ι,
        dist (signedCanonicalSplit x (Sum.inl i)) (signedCanonicalSplit y (Sum.inl i)) ^ 2 ≤
          dist (x i) (y i) ^ 2 := by
      intro i
      change dist (max (x i) 0) (max (y i) 0) ^ 2 ≤ dist (x i) (y i) ^ 2
      simp only [Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_max_sub_max_le_abs (x i) (y i) 0) 2
    have hterm_inr : ∀ i : ι,
        dist (signedCanonicalSplit x (Sum.inr i)) (signedCanonicalSplit y (Sum.inr i)) ^ 2 ≤
          dist (x i) (y i) ^ 2 := by
      intro i
      change dist (max (-(x i)) 0) (max (-(y i)) 0) ^ 2 ≤ dist (x i) (y i) ^ 2
      simp only [Real.dist_eq]
      have h := abs_max_sub_max_le_abs (-(x i)) (-(y i)) 0
      rw [neg_sub_neg, abs_sub_comm (y i) (x i)] at h
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hdxy : (∑ i : ι, dist (x i) (y i) ^ 2) = dist x y ^ 2 :=
      (EuclideanSpace.dist_sq_eq x y).symm
    have hstep :
        (∑ i : ι, dist (signedCanonicalSplit x (Sum.inl i))
            (signedCanonicalSplit y (Sum.inl i)) ^ 2) +
          ∑ i : ι, dist (signedCanonicalSplit x (Sum.inr i))
            (signedCanonicalSplit y (Sum.inr i)) ^ 2
        ≤ (∑ i : ι, dist (x i) (y i) ^ 2) + ∑ i : ι, dist (x i) (y i) ^ 2 :=
      add_le_add (Finset.sum_le_sum fun i _ => hterm_inl i)
        (Finset.sum_le_sum fun i _ => hterm_inr i)
    rw [hdxy] at hstep
    have hK : ((2 : NNReal) * dist x y : ℝ) ^ 2 = 4 * dist x y ^ 2 := by push_cast; ring
    rw [hK]
    nlinarith [sq_nonneg (dist x y)]
  have h2 : (0 : ℝ) ≤ (2 : NNReal) * dist x y := by positivity
  nlinarith [dist_nonneg (x := signedCanonicalSplit x) (y := signedCanonicalSplit y), hsq, h2]

/-- Local absolute continuity is preserved by the canonical positive/negative
split used in Section 5.

Coordinatewise `max` is Lipschitz, hence composition with an absolutely
continuous scalar path is absolutely continuous; finite products preserve the
property. This is the regularity step in Section 5.2.2 of
<https://arxiv.org/abs/2509.18766>, cross-checked with Mathlib's absolute
continuity API
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.
-/
theorem signedCanonicalSplit_path_regular
    (x : ℝ → EuclideanSpace ℝ ι)
    (hx : LocallyAbsolutelyContinuousOnPositiveCompacts x) :
    LocallyAbsolutelyContinuousOnPositiveCompacts
      (fun μ => signedCanonicalSplit (x μ)) := by
  refine ⟨fun a b ha hab => ?_⟩
  -- Note: applying this via dot notation (`lipschitzWith_signedCanonicalSplit.comp_...`)
  -- causes a `whnf` timeout during unification; explicit named arguments avoid it.
  exact LipschitzWith.comp_absolutelyContinuousOnInterval
    (f := x) (g := signedCanonicalSplit) lipschitzWith_signedCanonicalSplit
    (hx.absolutelyContinuousOn_Icc a b ha hab)

/-- Difference map `(y_pos, y_neg) ↦ y_pos - y_neg`. -/
noncomputable def splitDifference (y : EuclideanSpace ℝ (ι ⊕ ι)) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => y (Sum.inl i) - y (Sum.inr i))

/-- Coordinatewise complementarity of an arbitrary signed split. -/
def SplitComplementary (y : EuclideanSpace ℝ (ι ⊕ ι)) : Prop :=
  ∀ i : ι, y (Sum.inl i) * y (Sum.inr i) = 0

/--
The quadratic part of the objective is invariant under the signed/augmented-positive
reduction, for *any* split `y = (y_pos, y_neg)` (not just a complementary one): expanding the
block matrix `[M,-M;-M,M]` and vector `[r;-r]` against `y = (a,b)` and `splitDifference y = a-b`
reduces both sides to the same bilinear expression by `augmentedMatrix_matVec`,
`inner_sumElim`, `inner_augmentedVector_sumElim`. This is the general form of the computation
in Lemma 5.1 of <https://arxiv.org/abs/2509.18766>; `lasso_objective_reduction`'s `h_quad` is
the special case `y = signedCanonicalSplit x`.
-/
lemma quadraticLoss_splitDifference_eq
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (ι ⊕ ι)) :
    quadraticLoss M r (splitDifference y) =
      quadraticLoss (augmentedMatrix M) (augmentedVector r) y := by
  set a : EuclideanSpace ℝ ι := euclideanOf (fun i => y (Sum.inl i)) with ha
  set b : EuclideanSpace ℝ ι := euclideanOf (fun i => y (Sum.inr i)) with hb
  have hy_eq : y = euclideanOf (Sum.elim a b) := by
    ext j
    cases j with
    | inl i => simp [euclideanOf, ha]
    | inr i => simp [euclideanOf, hb]
  have hsplit_eq : splitDifference y = a - b := by
    ext i
    change y (Sum.inl i) - y (Sum.inr i) = _
    simp [euclideanOf, ha, hb]
  rw [hsplit_eq, hy_eq, quadraticLoss, quadraticLoss, augmentedMatrix_matVec, inner_sumElim,
    inner_augmentedVector_sumElim, matVec_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_sub_right, inner_add_right, inner_neg_right]
  ring

/-- The signed-to-positive augmentation preserves the standing problem-data
assumptions.

For `y=(y⁺,y⁻)`, the augmented quadratic form is
`⟨y, M̃y⟩ = ⟨y⁺-y⁻, M(y⁺-y⁻)⟩`, hence is nonnegative. If `r=Mq`, then
`(r,-r)=M̃(q,0)`, and the penalty parameter is unchanged. This is the block
calculation in Section 5.1.1 of <https://arxiv.org/abs/2509.18766>, consistent
with the standard PSD characterization by quadratic forms in
Boyd--Vandenberghe <https://web.stanford.edu/~boyd/cvxbook/>.
-/
theorem augmented_problem_data
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (hdata : ProblemData M r lambda) :
    ProblemData (augmentedMatrix M) (augmentedVector r) lambda := by
  have hM_symm : M.IsSymm := hdata.psd.symm
  refine ⟨⟨augmentedMatrix_isSymm M hM_symm, fun y => ?_⟩, ?_, hdata.lambda_nonneg⟩
  · -- PSD: specializing `quadraticLoss_splitDifference_eq` at `r = 0` isolates the
    -- quadratic-form identity `⟨y, M̃y⟩ = ⟨splitDifference y, M (splitDifference y)⟩`.
    have hquad : inner ℝ y (matVec (augmentedMatrix M) y) =
        inner ℝ (splitDifference y) (matVec M (splitDifference y)) := by
      have h := quadraticLoss_splitDifference_eq M (0 : EuclideanSpace ℝ ι) y
      have haug0 : augmentedVector (0 : EuclideanSpace ℝ ι) = 0 := by
        ext j
        cases j with
        | inl i => simp [augmentedVector]
        | inr i => simp [augmentedVector]
      rw [quadraticLoss, quadraticLoss, haug0, inner_zero_left, inner_zero_left, sub_zero,
        sub_zero] at h
      linarith [h]
    rw [hquad]
    exact hdata.psd.get_nonneg (splitDifference y)
  · -- `r = Mq` lifts to `augmentedVector r = augmentedMatrix M · (q, 0)`.
    obtain ⟨q, hq⟩ := hdata.r_mem_span
    refine ⟨euclideanOf (Sum.elim q 0), ?_⟩
    rw [augmentedMatrix_matVec]
    have h0 : matVec M (0 : EuclideanSpace ℝ ι) = 0 := by ext i; simp [matVec, euclideanOf]
    simp only [show (WithLp.toLp 2 (0 : ι → ℝ) : EuclideanSpace ℝ ι) = 0 from rfl, h0, sub_zero,
      add_zero, hq]
    rfl

/-- Coordinatewise bound behind Lemma 5.1(1): for a nonnegative pair `(y_pos, y_neg)`,
`|y_pos - y_neg| ≤ y_pos + y_neg`, with equality iff one of the two vanishes. Extracted since
both `lasso_split_objective_le` and `lasso_split_objective_eq_iff_complementary` need it. -/
lemma abs_sub_le_add_of_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    |p - q| ≤ p + q :=
  calc |p - q| ≤ |p| + |q| := abs_sub _ _
    _ = p + q := by rw [abs_of_nonneg hp, abs_of_nonneg hq]

/--
Lemma 5.1(1), inequality part: any nonnegative split gives an augmented positive
objective no smaller than the signed lasso objective of its difference.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(1).
-/
lemma lasso_split_objective_le
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y : EuclideanSpace ℝ (ι ⊕ ι)) (hy : Nonnegative y)
    (hpenalty : 0 ≤ lambda + 1 / μ) :
    lassoObjective M r lambda μ (splitDifference y) ≤
      positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ y := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(1)):
  -- The signed lasso objective evaluates the L1 norm |x|. The augmented positive objective
  -- evaluates the sum of the positive and negative components (y_pos + y_neg).
  -- By the triangle inequality, |y_pos - y_neg| <= y_pos + y_neg for any nonnegative components.
  -- This makes the signed objective always less than or equal to the augmented positive objective.
  dsimp only [positiveLassoObjective]
  rw [lassoObjective, lassoObjective, quadraticLoss_splitDifference_eq]
  gcongr
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  change (∑ i, ‖(splitDifference y) i‖) ≤ ∑ j, ‖y j‖
  have h_sum_rhs :
      (∑ j : ι ⊕ ι, ‖y j‖) = (∑ i : ι, ‖y (Sum.inl i)‖) + ∑ i : ι, ‖y (Sum.inr i)‖ :=
    Fintype.sum_sum_type _
  rw [h_sum_rhs, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  change |y (Sum.inl i) - y (Sum.inr i)| ≤ ‖y (Sum.inl i)‖ + ‖y (Sum.inr i)‖
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (hy (Sum.inl i)), abs_of_nonneg (hy (Sum.inr i))]
  exact abs_sub_le_add_of_nonneg (hy (Sum.inl i)) (hy (Sum.inr i))

/--
Lemma 5.1(1), equality criterion: equality holds exactly for complementary
positive and negative parts.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(1).
-/
lemma lasso_split_objective_eq_iff_complementary
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y : EuclideanSpace ℝ (ι ⊕ ι)) (hy : Nonnegative y)
    (hpenalty : 0 < lambda + 1 / μ) :
    lassoObjective M r lambda μ (splitDifference y) =
        positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ y ↔
      SplitComplementary y := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(1)):
  -- Equality in the triangle inequality |y_pos - y_neg| <= y_pos + y_neg holds if and only if
  -- y_pos and y_neg have disjoint support. Since they are nonnegative, this is equivalent
  -- to the complementarity condition y_pos * y_neg = 0 for all coordinates.
  dsimp only [positiveLassoObjective]
  rw [lassoObjective, lassoObjective, quadraticLoss_splitDifference_eq,
    add_right_inj, mul_right_inj' (ne_of_gt hpenalty)]
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  change (∑ i, ‖(splitDifference y) i‖) = (∑ j, ‖y j‖) ↔ _
  have h_sum_rhs :
      (∑ j : ι ⊕ ι, ‖y j‖) = (∑ i : ι, ‖y (Sum.inl i)‖) + ∑ i : ι, ‖y (Sum.inr i)‖ :=
    Fintype.sum_sum_type _
  rw [h_sum_rhs, ← Finset.sum_add_distrib]
  have hterm_le : ∀ i ∈ (Finset.univ : Finset ι),
      ‖(splitDifference y) i‖ ≤ ‖y (Sum.inl i)‖ + ‖y (Sum.inr i)‖ := by
    intro i _
    change |y (Sum.inl i) - y (Sum.inr i)| ≤ ‖y (Sum.inl i)‖ + ‖y (Sum.inr i)‖
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (hy (Sum.inl i)), abs_of_nonneg (hy (Sum.inr i))]
    exact abs_sub_le_add_of_nonneg (hy (Sum.inl i)) (hy (Sum.inr i))
  rw [Finset.sum_eq_sum_iff_of_le hterm_le]
  constructor
  · intro h i
    have hi := h i (Finset.mem_univ i)
    change |y (Sum.inl i) - y (Sum.inr i)| = ‖y (Sum.inl i)‖ + ‖y (Sum.inr i)‖ at hi
    have hai : 0 ≤ y (Sum.inl i) := hy (Sum.inl i)
    have hbi : 0 ≤ y (Sum.inr i) := hy (Sum.inr i)
    simp only [Real.norm_eq_abs, abs_of_nonneg hai, abs_of_nonneg hbi] at hi
    rcases abs_cases (y (Sum.inl i) - y (Sum.inr i)) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq] at hi; nlinarith
    · rw [heq] at hi; nlinarith
  · intro hcomp i _
    have hcompi := hcomp i
    change |y (Sum.inl i) - y (Sum.inr i)| = ‖y (Sum.inl i)‖ + ‖y (Sum.inr i)‖
    have hai : 0 ≤ y (Sum.inl i) := hy (Sum.inl i)
    have hbi : 0 ≤ y (Sum.inr i) := hy (Sum.inr i)
    simp only [Real.norm_eq_abs, abs_of_nonneg hai, abs_of_nonneg hbi]
    rcases mul_eq_zero.mp hcompi with h0 | h0
    · rw [h0, abs_of_nonpos (by linarith)]; ring
    · rw [h0, abs_of_nonneg (by linarith)]; ring

/--
Canonical objective equality for the split `x = x_+ - x_-`.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1.
-/
lemma lasso_objective_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) :
    Nonnegative (signedCanonicalSplit x) ∧
      lassoObjective M r lambda μ x =
        positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ
          (signedCanonicalSplit x) := by
  constructor
  · -- Nonnegative (signedCanonicalSplit x)
    intro j
    cases j <;>
      simp [signedCanonicalSplit, coordinatePositivePart, coordinateNegativePart, euclideanOf]
  · -- lassoObjective equality
    have h_split : splitDifference (signedCanonicalSplit x) = x := by
      ext i
      change max (x i) 0 - max (-x i) 0 = x i
      rcases le_total 0 (x i) with hpos | hneg
      · rw [max_eq_left hpos, max_eq_right (by linarith)]
        linarith
      · rw [max_eq_right hneg, max_eq_left (by linarith)]
        linarith
    have h_norm :
        ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖ =
          ‖(WithLp.equiv 1 (ι ⊕ ι → ℝ)).symm (signedCanonicalSplit x)‖ := by
      rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
      change (∑ i, ‖x i‖) = ∑ j, ‖signedCanonicalSplit x j‖
      have h_sum_rhs :
          (∑ j : ι ⊕ ι, ‖signedCanonicalSplit x j‖) =
            (∑ i : ι, ‖signedCanonicalSplit x (Sum.inl i)‖) +
              ∑ i : ι, ‖signedCanonicalSplit x (Sum.inr i)‖ := by
        exact Fintype.sum_sum_type _
      rw [h_sum_rhs, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change ‖x i‖ = ‖max (x i) 0‖ + ‖max (-x i) 0‖
      simp only [Real.norm_eq_abs]
      rcases le_total 0 (x i) with hpos | hneg
      · have hm1 : max (x i) 0 = x i := max_eq_left hpos
        have hm2 : max (-x i) 0 = 0 := max_eq_right (by linarith)
        rw [hm1, hm2, abs_zero, add_zero]
      · have hm1 : max (x i) 0 = 0 := max_eq_right hneg
        have hm2 : max (-x i) 0 = -x i := max_eq_left (by linarith)
        rw [hm1, hm2, abs_zero, zero_add, abs_neg]
    have h_quad : quadraticLoss M r x =
        quadraticLoss (augmentedMatrix M) (augmentedVector r) (signedCanonicalSplit x) := by
      /-
      Expand the block matrix `[M,-M;-M,M]` and vector `[r;-r]`.
      Both expressions reduce to the quadratic loss at `x₊-x₋=x`.
      This is Lemma 5.1 of <https://arxiv.org/abs/2509.18766>.
      -/
      have h := quadraticLoss_splitDifference_eq M r (signedCanonicalSplit x)
      rwa [h_split] at h
    rw [positiveLassoObjective, lassoObjective, lassoObjective, h_norm, h_quad]

/--
Lemma 5.1(2): a signed lasso minimizer gives an augmented positive-lasso
minimizer via the canonical split.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(2).
-/
lemma lasso_minimizer_to_augmented_positive_minimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι)
    (hpenalty : 0 ≤ lambda + 1 / μ)
    (hx : IsLassoMinimizer M r lambda μ x) :
    IsPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ
      (signedCanonicalSplit x) := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(2)):
  -- If x minimizes the signed lasso objective, its canonical split minimizes the augmented
  -- positive objective. Any other positive split y can be mapped to a signed vector y_pos - y_neg,
  -- whose signed objective is ≤ the positive objective of y. Since x is the global minimum,
  -- the canonical split of x must achieve the absolute minimum of the augmented problem.
  obtain ⟨hnonneg, hobj_eq⟩ := lasso_objective_reduction M r lambda μ x
  refine ⟨hnonneg, isMinOn_iff.mpr (fun y hy => ?_)⟩
  rw [← hobj_eq]
  calc lassoObjective M r lambda μ x
      ≤ lassoObjective M r lambda μ (splitDifference y) :=
        isMinOn_iff.mp hx (splitDifference y) (Set.mem_univ _)
    _ ≤ positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ y :=
        lasso_split_objective_le M r lambda μ y hy hpenalty

/-- A signed coordinate that is monotone in either direction becomes two
nondecreasing coordinates after the positive/negative split.

Lemma 4.10 makes `z(μ)=μx(μ)` zero near the origin. Thus a nondecreasing
coordinate stays nonnegative, so `zᵢ⁺=zᵢ` and `zᵢ⁻=0`; a nonincreasing
coordinate stays nonpositive, so `zᵢ⁺=0` and `zᵢ⁻=-zᵢ`. In either case both
coordinates of the canonical nonnegative representation are nondecreasing.
This is exactly the reduction in Section 5.2.1 of
<https://arxiv.org/abs/2509.18766>.
-/
theorem signedCanonicalSplit_scaled_monotonicity
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hmin : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x μ))
    (hx : ∀ i,
      MonotoneOn (fun μ => μ * x μ i) (Set.Ioi 0) ∨
        AntitoneOn (fun μ => μ * x μ i) (Set.Ioi 0)) :
    ∀ j : ι ⊕ ι,
      MonotoneOn (fun μ => μ * signedCanonicalSplit (x μ) j) (Set.Ioi 0) := by
  have hpenalty : ∀ μ : ℝ, 0 < μ → 0 ≤ lambda + 1 / μ := by
    intro μ hμ
    have h1 := hdata.lambda_nonneg
    have h2 : (0 : ℝ) < 1 / μ := by positivity
    linarith
  have hdata_aug := augmented_problem_data M r lambda hdata
  have hy_pos : ∀ μ > 0,
      IsPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ
        (signedCanonicalSplit (x μ)) :=
    fun μ hμ => lasso_minimizer_to_augmented_positive_minimizer M r lambda μ (x μ)
      (hpenalty μ hμ) (hmin μ hμ)
  -- Lemma 4.10 for the augmented positive system: `z(μ) = μ • signedCanonicalSplit(x μ)`
  -- vanishes for small `μ`, hence (since `μ ≠ 0` there) `signedCanonicalSplit (x μ) = 0`,
  -- hence `x μ = 0` itself (both `max(x μ i, 0)` and `max(-(x μ i), 0)` vanish).
  obtain ⟨μ0, hμ0pos, hzero⟩ :=
    scaled_path_zero_near_zero (augmentedMatrix M) (augmentedVector r) lambda
      (fun μ => signedCanonicalSplit (x μ)) hdata_aug hy_pos
  have hxzero : ∀ μ, 0 < μ → μ ≤ μ0 → x μ = 0 := by
    intro μ hμpos hμle
    have hz := hzero μ ⟨hμpos.le, hμle⟩
    dsimp only [scaledPrimalPath] at hz
    have hsplit0 : signedCanonicalSplit (x μ) = 0 := by
      rcases smul_eq_zero.mp hz with h | h
      · exact absurd h hμpos.ne'
      · exact h
    ext i
    have hinl : signedCanonicalSplit (x μ) (Sum.inl i) =
        (0 : EuclideanSpace ℝ (ι ⊕ ι)) (Sum.inl i) := by rw [hsplit0]
    have hinr : signedCanonicalSplit (x μ) (Sum.inr i) =
        (0 : EuclideanSpace ℝ (ι ⊕ ι)) (Sum.inr i) := by rw [hsplit0]
    change max (x μ i) 0 = 0 at hinl
    change max (-(x μ i)) 0 = 0 at hinr
    change x μ i = 0
    have h1 : x μ i ≤ 0 := by
      have := le_max_left (x μ i) 0; rw [hinl] at this; linarith
    have h2 : 0 ≤ x μ i := by
      have := le_max_left (-x μ i) 0; rw [hinr] at this; linarith
    linarith
  -- An antitone `μ * x μ i` that vanishes on `(0, μ0]` stays `≤ 0` everywhere on `(0,∞)`;
  -- symmetrically a monotone one stays `≥ 0`.
  have hg_le_zero : ∀ i, AntitoneOn (fun μ => μ * x μ i) (Set.Ioi 0) →
      ∀ μ ∈ Set.Ioi (0 : ℝ), μ * x μ i ≤ 0 := by
    intro i hanti μ hμ
    rcases le_total μ μ0 with hle | hge
    · rw [hxzero μ hμ hle]; simp
    · have hμ0mem : μ0 ∈ Set.Ioi (0 : ℝ) := hμ0pos
      have hle' := hanti hμ0mem hμ hge
      dsimp only at hle'
      rw [hxzero μ0 hμ0pos le_rfl] at hle'
      simpa using hle'
  have hg_ge_zero : ∀ i, MonotoneOn (fun μ => μ * x μ i) (Set.Ioi 0) →
      ∀ μ ∈ Set.Ioi (0 : ℝ), 0 ≤ μ * x μ i := by
    intro i hmono μ hμ
    rcases le_total μ μ0 with hle | hge
    · rw [hxzero μ hμ hle]; simp
    · have hμ0mem : μ0 ∈ Set.Ioi (0 : ℝ) := hμ0pos
      have hle' := hmono hμ0mem hμ hge
      dsimp only at hle'
      rw [hxzero μ0 hμ0pos le_rfl] at hle'
      simpa using hle'
  intro j
  cases j with
  | inl i =>
    -- `μ • signedCanonicalSplit(xμ)(inl i) = max(μ x μ i, 0)` on `(0,∞)`: directly monotone
    -- when `μ x μ i` is monotone, and constant `0` (hence monotone) when it is antitone.
    intro a ha b hb hab
    dsimp only
    have hcast : ∀ μ ∈ Set.Ioi (0 : ℝ),
        μ * signedCanonicalSplit (x μ) (Sum.inl i) = max (μ * x μ i) 0 := by
      intro μ hμ
      change μ * max (x μ i) 0 = max (μ * x μ i) 0
      rw [mul_max_of_nonneg _ _ hμ.le, mul_zero]
    rw [hcast a ha, hcast b hb]
    rcases hx i with hg | hg
    · exact max_le_max (hg ha hb hab) le_rfl
    · rw [max_eq_right (hg_le_zero i hg a ha), max_eq_right (hg_le_zero i hg b hb)]
  | inr i =>
    -- Symmetric, with `max(-(μ x μ i), 0)`: monotone when `μ x μ i` is antitone, constant
    -- `0` when it is monotone.
    intro a ha b hb hab
    dsimp only
    have hcast : ∀ μ ∈ Set.Ioi (0 : ℝ),
        μ * signedCanonicalSplit (x μ) (Sum.inr i) = max (-(μ * x μ i)) 0 := by
      intro μ hμ
      change μ * max (-(x μ i)) 0 = max (-(μ * x μ i)) 0
      rw [mul_max_of_nonneg _ _ hμ.le, mul_neg, mul_zero]
    rw [hcast a ha, hcast b hb]
    rcases hx i with hg | hg
    · rw [max_eq_right (by linarith [hg_ge_zero i hg a ha] : -(a * x a i) ≤ 0),
        max_eq_right (by linarith [hg_ge_zero i hg b hb] : -(b * x b i) ≤ 0)]
    · exact max_le_max (neg_le_neg (hg ha hb hab)) le_rfl

/--
Lemma 5.1(3): equality of the signed lasso minimum and the augmented positive
lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(3).

Informal proof: given a selected minimizer `x` of the signed lasso at `μ`,
`lassoMin = lassoObjective x` (`lassoMin_eq_of_isLassoMinimizer`). By Lemma 5.1(2)
(`lasso_minimizer_to_augmented_positive_minimizer`), `signedCanonicalSplit x` minimizes the
augmented positive lasso, so `posLassoMin_aug = positiveLassoObjective_aug (signedCanonicalSplit
x)` (`posLassoMin_eq_of_isPositiveLassoMinimizer`), which equals `lassoObjective x` by Lemma
5.1's objective identity (`lasso_objective_reduction`).
-/
lemma lasso_min_eq_augmented_pos_lasso_min
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hpenalty : 0 ≤ lambda + 1 / μ)
    (x : EuclideanSpace ℝ ι) (hx : IsLassoMinimizer M r lambda μ x) :
    lassoMin M r lambda μ =
      posLassoMin (augmentedMatrix M) (augmentedVector r) lambda μ := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(3)):
  -- Follows directly from `lasso_minimizer_to_augmented_positive_minimizer` and
  -- `lasso_objective_reduction`. The minimum values of both problems coincide.
  rw [lassoMin_eq_of_isLassoMinimizer M r lambda μ x hx]
  have hy := lasso_minimizer_to_augmented_positive_minimizer M r lambda μ x hpenalty hx
  rw [posLassoMin_eq_of_isPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ
      (signedCanonicalSplit x) hy]
  exact (lasso_objective_reduction M r lambda μ x).2

/-- Initial positive weights associated to signed initialization vectors. -/
noncomputable def signedToPositiveInitialization
    (β γ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm
    (Sum.elim ((1 / 2 : ℝ) • (β + γ)) ((1 / 2 : ℝ) • (β - γ)))

/--
The pointwise change of variables
`p_pos=(u+v)/2`, `p_neg=(u-v)/2`.
-/
noncomputable def signedToPositiveWeights
    (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    EuclideanSpace ℝ (ι ⊕ ι) :=
  let uv := WithLp.equiv 2 _ state
  (WithLp.equiv 2 _).symm
    (Sum.elim ((1 / 2 : ℝ) • (uv.1 + uv.2)) ((1 / 2 : ℝ) • (uv.1 - uv.2)))

/-- `signedToPositiveWeights` bundled as a linear map, so that its derivative along a curve
follows from the chain rule for continuous linear maps
(`ContinuousLinearMap.hasFDerivAt.comp_hasDerivAt`), reused in `dln_dynamics_reduction`. -/
noncomputable def signedToPositiveWeightsLM :
    WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →ₗ[ℝ] EuclideanSpace ℝ (ι ⊕ ι) where
  toFun := signedToPositiveWeights
  map_add' := by
    intro s1 s2
    dsimp [signedToPositiveWeights]
    ext j
    cases j with
    | inl i => simp; ring
    | inr i => simp; ring
  map_smul' := by
    intro c s
    dsimp [signedToPositiveWeights]
    ext j
    cases j with
    | inl i => simp [smul_eq_mul]; ring
    | inr i => simp [smul_eq_mul]; ring

/--
Section 5.1.2 of `docs/Lasso.md`: the `u ∘ v` DLN vector field maps, under
`signedToPositiveWeights` and the time-doubling `t ↦ 2t` from the chain rule, to the positive
`u ∘ u` DLN vector field for the augmented system `(augmentedMatrix M, augmentedVector r)`.

Informal proof: write `p_pos = (u+v)/2`, `p_neg = (u-v)/2` for the two `signedToPositiveWeights`
components. By `gradient_posDlnObjective`, `augmentedMatrix_matVec`,
`coordinateSquare_half_add_sub_eq_hadamard`, and the block-vector components
`augmentedVector_apply_inl/inr`, the positive vector field at `signedToPositiveWeights state`
evaluates, coordinatewise in `j = inl i` and `j = inr i`, to
`-(u_i+v_i)(D_i+lambda)` and `(u_i-v_i)(D_i-lambda)` respectively, where
`D = matVec M (hadamard u v) - r`. Comparing with `dlnVectorField_eq`'s explicit formula for
`-(∇_u, ∇_v) dlnObjective` shows these are exactly `2 p_pos`/`2 p_neg` applied to that same pair,
i.e. the two sides agree after scaling by 2 (the chain-rule factor from `t ↦ 2t`).
-/
lemma posDlnVectorField_signedToPositiveWeights_eq
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (t t' : ℝ) (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    (2 : ℝ) • signedToPositiveWeights (dlnVectorField M r lambda t state) =
      posDlnVectorField (augmentedMatrix M) (augmentedVector r) lambda t'
        (signedToPositiveWeights state) := by
  set u := (WithLp.equiv 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) state).1
  set v := (WithLp.equiv 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) state).2
  set ppos := (1 / 2 : ℝ) • (u + v) with hppos
  set pneg := (1 / 2 : ℝ) • (u - v) with hpneg
  have hstw : signedToPositiveWeights state = euclideanOf (Sum.elim ppos pneg) := rfl
  rw [hstw]
  dsimp only [posDlnVectorField]
  rw [(hasGradientAt_posDlnObjective (augmentedMatrix M) (augmentedVector r) lambda
    (augmentedMatrix_isSymm M hM) (euclideanOf (Sum.elim ppos pneg))).gradient]
  rw [coordinateSquare_sumElim, augmentedMatrix_matVec]
  have hdiff : matVec M (coordinateSquare ppos) - matVec M (coordinateSquare pneg) =
      matVec M (hadamard u v) := by
    rw [← matVec_sub, coordinateSquare_half_add_sub_eq_hadamard]
  dsimp only [dlnVectorField]
  rw [(hasGradientAt_dlnObjective_left M r lambda hM u v).gradient,
      (hasGradientAt_dlnObjective_right M r lambda hM u v).gradient]
  ext j
  cases j with
  | inl i =>
    simp [signedToPositiveWeights, euclideanOf, hadamard, augmentedVector_apply_inl]
    have hbridge : (WithLp.toLp 2 fun i : ι => u.ofLp i * v.ofLp i) = hadamard u v := rfl
    rw [hbridge]
    have hd :
        (matVec M (coordinateSquare ppos)).ofLp i - (matVec M (coordinateSquare pneg)).ofLp i =
          (matVec M (hadamard u v)).ofLp i := by
      have h := hdiff
      apply_fun (fun x => x.ofLp i) at h
      simpa using h
    have hppos_val : ppos.ofLp i = 2⁻¹ * u.ofLp i + 2⁻¹ * v.ofLp i := by
      simp [hppos, smul_eq_mul]
    rw [hppos_val]
    linear_combination (u.ofLp i + v.ofLp i) * hd
  | inr i =>
    simp [signedToPositiveWeights, euclideanOf, hadamard, augmentedVector_apply_inr]
    have hbridge : (WithLp.toLp 2 fun i : ι => u.ofLp i * v.ofLp i) = hadamard u v := rfl
    rw [hbridge]
    have hd :
        (matVec M (coordinateSquare ppos)).ofLp i - (matVec M (coordinateSquare pneg)).ofLp i =
          (matVec M (hadamard u v)).ofLp i := by
      have h := hdiff
      apply_fun (fun x => x.ofLp i) at h
      simpa using h
    have hpneg_val : pneg.ofLp i = 2⁻¹ * u.ofLp i - 2⁻¹ * v.ofLp i := by
      simp [hpneg, smul_eq_mul]; ring
    rw [hpneg_val]
    linear_combination (v.ofLp i - u.ofLp i) * hd

omit [Fintype ι] in
/-- Coordinatewise components of the signed-to-positive initialization. -/
lemma signedToPositiveInitialization_apply_inl (β γ : EuclideanSpace ℝ ι) (i : ι) :
    signedToPositiveInitialization β γ (Sum.inl i) = (1 / 2 : ℝ) * (β i + γ i) := by
  simp [signedToPositiveInitialization]; ring

omit [Fintype ι] in
lemma signedToPositiveInitialization_apply_inr (β γ : EuclideanSpace ℝ ι) (i : ι) :
    signedToPositiveInitialization β γ (Sum.inr i) = (1 / 2 : ℝ) * (β i - γ i) := by
  simp [signedToPositiveInitialization]

omit [Fintype ι] in
/--
Algebraic identity behind Section 5.1.2:
`u ∘ v = p_pos^2 - p_neg^2`.

Informal proof reference: `docs/Lasso.md`, Section 5.1.2.
-/
lemma signed_effective_eq_split_positive_effective
    (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    effectiveParameter (fun _ => state) 0 =
      splitDifference (coordinateSquare (signedToPositiveWeights state)) := by
  -- Proof sketch (Section 5.1.2):
  -- Algebraic identity: p_pos = (u+v)/2 and p_neg = (u-v)/2.
  -- Therefore, p_pos^2 - p_neg^2 = ((u+v)^2 - (u-v)^2) / 4 = 4uv / 4 = uv.
  -- This exactly matches the effective parameter `u ∘ v`.
  set uv := WithLp.equiv 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) state with huv
  have hstw : signedToPositiveWeights state =
      euclideanOf (Sum.elim ((1 / 2 : ℝ) • (uv.1 + uv.2)) ((1 / 2 : ℝ) • (uv.1 - uv.2))) := rfl
  rw [hstw, coordinateSquare_sumElim]
  have heff : effectiveParameter (fun _ => state) 0 = hadamard uv.1 uv.2 := rfl
  rw [heff]
  dsimp [hadamard, splitDifference, euclideanOf]
  ext i
  simp [coordinateSquare, euclideanOf, smul_eq_mul]
  ring

/--
`coordinateSquare` is continuous. Reusable version of the pattern proved inline (three times)
in `MirrorFlow.lean` and `Bounds/Delta.lean`.
-/
lemma continuous_coordinateSquare :
    Continuous (coordinateSquare : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
  have h_sq : Continuous (fun (x : EuclideanSpace ℝ ι) (i : ι) => x i * x i) :=
    continuous_pi fun i =>
      Continuous.mul (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i)
        (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i)
  have h_euclideanOf_cont : Continuous (euclideanOf : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    euclideanToPiEquiv.symm.continuous_of_finiteDimensional
  exact h_euclideanOf_cont.comp h_sq

/-- `signedToPositiveWeights` is continuous, being (the coercion of) the bundled linear map
`signedToPositiveWeightsLM`. -/
lemma continuous_signedToPositiveWeights :
    Continuous (signedToPositiveWeights :
      WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) → EuclideanSpace ℝ (ι ⊕ ι)) :=
  signedToPositiveWeightsLM.toContinuousLinearMap.continuous

/--
Time-averaged version of the signed-to-positive effective-parameter identity.

Informal proof reference: `docs/Lasso.md`, Section 5.2.

Informal proof: pointwise (Section 5.1.2's identity, `signed_effective_eq_split_positive_effective`,
applied at each time `u`) `effectiveParameter w u = A(u) - B(u)` where `A(u) = coordinateSquare
(signedToPositiveWeights (w u)) (inl i)` and `B(u)` is its `inr` counterpart. Since `w` is
continuous (`hw_cont`), so are `A` and `B`, hence both are interval integrable on `[0,t]` and
`∫₀ᵗ (A - B) = ∫₀ᵗ A - ∫₀ᵗ B` (`intervalIntegral.integral_sub`). The substitution `u = 2v`
(`intervalIntegral.smul_integral_comp_mul_left`) turns `∫₀ᵗ A` into `2 * ∫₀^{t/2} A(2·)`, and
likewise for `B`; matching this against the definition of `posAverageTrajectory` at `t/2` (whose
two `inl`/`inr` coordinates are literally `(1/(t/2)) * ∫₀^{t/2} A(2·)` and the `B` analogue)
gives the claimed identity after the algebraic simplification `1/(t/2) = 2/t`.
-/
lemma signed_average_eq_split_positive_average
    (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (t : ℝ)
    (hw_cont : Continuous w) :
    averageTrajectory w t =
      splitDifference
        (posAverageTrajectory
          (fun τ => signedToPositiveWeights (w (2 * τ))) ((1 / 2 : ℝ) * t)) := by
  ext i
  set A' : ℝ → ℝ := fun u => coordinateSquare (signedToPositiveWeights (w u)) (Sum.inl i)
    with hA'
  set B' : ℝ → ℝ := fun u => coordinateSquare (signedToPositiveWeights (w u)) (Sum.inr i)
    with hB'
  have hA'_cont : Continuous A' :=
    (continuous_euclidean_apply (Sum.inl i)).comp
      (continuous_coordinateSquare.comp (continuous_signedToPositiveWeights.comp hw_cont))
  have hB'_cont : Continuous B' :=
    (continuous_euclidean_apply (Sum.inr i)).comp
      (continuous_coordinateSquare.comp (continuous_signedToPositiveWeights.comp hw_cont))
  have hpt : ∀ u, effectiveParameter w u i = A' u - B' u := by
    intro u
    have h := signed_effective_eq_split_positive_effective (w u)
    have heff : effectiveParameter (fun _ => w u) 0 = effectiveParameter w u := rfl
    rw [heff] at h
    rw [h]; rfl
  have hLHS : averageTrajectory w t i = (1 / t) * ∫ u in (0 : ℝ)..t, (A' u - B' u) := by
    dsimp [averageTrajectory, euclideanOf]
    congr 1
    exact intervalIntegral.integral_congr (fun u _ => hpt u)
  have hint : (∫ u in (0 : ℝ)..t, (A' u - B' u)) =
      (∫ u in (0 : ℝ)..t, A' u) - ∫ u in (0 : ℝ)..t, B' u :=
    intervalIntegral.integral_sub (hA'_cont.intervalIntegrable 0 t)
      (hB'_cont.intervalIntegrable 0 t)
  have hchgA : (∫ u in (0 : ℝ)..t, A' u) = 2 * ∫ v in (0 : ℝ)..((1 / 2 : ℝ) * t), A' (2 * v) := by
    have h2 := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := (1 / 2 : ℝ) * t)
      A' 2
    simp only [smul_eq_mul, mul_zero] at h2
    rw [show (2 : ℝ) * ((1 / 2 : ℝ) * t) = t by ring] at h2
    linarith [h2]
  have hchgB : (∫ u in (0 : ℝ)..t, B' u) = 2 * ∫ v in (0 : ℝ)..((1 / 2 : ℝ) * t), B' (2 * v) := by
    have h2 := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := (1 / 2 : ℝ) * t)
      B' 2
    simp only [smul_eq_mul, mul_zero] at h2
    rw [show (2 : ℝ) * ((1 / 2 : ℝ) * t) = t by ring] at h2
    linarith [h2]
  have hRHS : splitDifference
      (posAverageTrajectory (fun τ => signedToPositiveWeights (w (2 * τ))) ((1 / 2 : ℝ) * t)) i =
      (1 / ((1 / 2 : ℝ) * t)) * (∫ v in (0 : ℝ)..((1 / 2 : ℝ) * t), A' (2 * v)) -
        (1 / ((1 / 2 : ℝ) * t)) * ∫ v in (0 : ℝ)..((1 / 2 : ℝ) * t), B' (2 * v) := by
    dsimp [splitDifference, euclideanOf, posAverageTrajectory, posEffectiveParameter]
  rw [hLHS, hint, hchgA, hchgB, hRHS]
  have ht2 : (1 : ℝ) / ((1 / 2 : ℝ) * t) = 2 / t := by
    rcases eq_or_ne t 0 with ht0 | ht0
    · simp [ht0]
    · field_simp
  rw [ht2]
  ring

/--
Section 5.1.2: reduction of dynamics in the `u ∘ v` case to the `u ∘ u` case.

Informal proof reference: `docs/Lasso.md`, Section 5.1.2.  The positive
trajectory is explicitly `τ ↦ signedToPositiveWeights (wᵋ(2τ))`.

Informal proof: `dlnGradientFlow` gives `HasDerivAt (w ε) (dlnVectorField M r lambda t ((w ε) t)) t`
for every `t`. Composing `t ↦ 2τ` (chain rule, `HasDerivAt.scomp`) with the linear map
`signedToPositiveWeightsLM` (`ContinuousLinearMap.hasFDerivAt.comp_hasDerivAt`) shows
`τ ↦ signedToPositiveWeights ((w ε)(2τ))` has derivative
`signedToPositiveWeights (2 • dlnVectorField M r lambda (2τ) ((w ε)(2τ)))` at `τ`, and this
equals `posDlnVectorField (augmentedMatrix M) (augmentedVector r) lambda τ
(signedToPositiveWeights ((w ε)(2τ)))` by `posDlnVectorField_signedToPositiveWeights_eq`. The
initial condition and `C¹` regularity transfer along the same chain-rule composition; the
initialization identity is the pointwise algebraic computation `signedToPositiveWeights
((WithLp.equiv 2 _).symm (√ε•β, √ε•γ)) = √ε • signedToPositiveInitialization β γ`.
-/
lemma dln_dynamics_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (hdata : ProblemData M r lambda)
    (β γ : EuclideanSpace ℝ ι)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε) →
      posDlnGradientFlow (augmentedMatrix M) (augmentedVector r) lambda ε
        (signedToPositiveInitialization β γ)
        (fun τ => signedToPositiveWeights ((w ε) (2 * τ))) := by
  have hM : M.IsSymm := hdata.psd.symm
  intro ε _hε hw
  refine ⟨?_, ?_, ?_⟩
  · -- init
    have h0 := hw.init
    simp only [mul_zero]
    rw [h0]
    dsimp [signedToPositiveWeights, signedToPositiveInitialization]
    ext j
    cases j with
    | inl i => simp [smul_eq_mul]; ring
    | inr i => simp [smul_eq_mul]; ring
  · -- cont_diff
    have h1 : ContDiff ℝ 1 (fun τ : ℝ => (w ε) (2 * τ)) :=
      hw.cont_diff.comp (contDiff_const.mul contDiff_id)
    exact signedToPositiveWeightsLM.toContinuousLinearMap.contDiff.comp h1
  · -- ode
    intro τ
    have hg : HasDerivAt (fun τ' : ℝ => 2 * τ') 2 τ := by
      simpa using (hasDerivAt_id τ).const_mul (2 : ℝ)
    have hscaled := (hw.ode (2 * τ)).scomp τ hg
    have hderiv :=
      signedToPositiveWeightsLM.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ hscaled
    have hderiv' : HasDerivAt (fun τ' => signedToPositiveWeights ((w ε) (2 * τ')))
        (signedToPositiveWeights ((2 : ℝ) • dlnVectorField M r lambda (2 * τ) ((w ε) (2 * τ))))
        τ :=
      hderiv
    have heq := posDlnVectorField_signedToPositiveWeights_eq M r lambda hM (2 * τ) τ ((w ε) (2 * τ))
    have hsmul : signedToPositiveWeights
        ((2 : ℝ) • dlnVectorField M r lambda (2 * τ) ((w ε) (2 * τ))) =
        (2 : ℝ) • signedToPositiveWeights (dlnVectorField M r lambda (2 * τ) ((w ε) (2 * τ))) :=
      signedToPositiveWeightsLM.map_smul (2 : ℝ) _
    rw [hsmul, heq] at hderiv'
    exact hderiv'

omit [Fintype ι] in
/--
The nondegeneracy condition on signed initialization is exactly nonzero
coordinates for the augmented positive initialization.

Informal proof reference: `docs/Lasso.md`, Section 5.2.
-/
lemma signed_initialization_nondegenerate_iff
    (β γ : EuclideanSpace ℝ ι) :
    NonzeroCoordinates (signedToPositiveInitialization β γ) ↔
      ∀ i, β i ≠ γ i ∧ β i ≠ -γ i := by
  -- Proof sketch (Section 5.2):
  -- The augmented initialization is (u+v)/2 and (u-v)/2.
  -- These components are non-zero if and only if (u+v) ≠ 0 and (u-v) ≠ 0.
  -- This is equivalent to u ≠ -v and u ≠ v.
  constructor
  · intro h i
    have h1 := h (Sum.inl i)
    have h2 := h (Sum.inr i)
    rw [signedToPositiveInitialization_apply_inl] at h1
    rw [signedToPositiveInitialization_apply_inr] at h2
    constructor
    · intro heq; exact h2 (by rw [heq]; ring)
    · intro heq; exact h1 (by rw [heq]; ring)
  · intro h j
    cases j with
    | inl i =>
      rw [signedToPositiveInitialization_apply_inl]
      intro heq
      exact (h i).2 (by linarith)
    | inr i =>
      rw [signedToPositiveInitialization_apply_inr]
      intro heq
      exact (h i).1 (by linarith)

/--
The signed-lasso deviation from monotonicity used in Theorem 2.2.
This matches Eq. (2.3): it applies the negative-variation penalty separately to
the positive and negative parts of `z_i(μ) = μ x_i(μ)`.
-/
noncomputable def signedZDownward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) :
    ℝ :=
  ∑ i,
    ∫ u in (0 : ℝ)..μ,
      (1 + u) *
        (max 0 (-deriv (fun u' => max (u' * x_lasso u' i) 0) u) +
          max 0 (-deriv (fun u' => max (-(u' * x_lasso u' i)) 0) u))

/--
If `f : ℝ → ℝ` is absolutely continuous on `[a,b]`, then `max 0 (-deriv f)` is interval
integrable on `[a,b]`. General scalar-valued reusable version of the algebraic identity
`max 0 (-x) = (|x| - x)/2` combined with `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`;
deduplicates the argument used privately (and only for `x ↦ u' * x_lasso u' i`) in
`Bounds/Delta.lean`'s `max_zero_neg_deriv_intervalIntegrable`.
-/
lemma intervalIntegrable_max_zero_neg_deriv_of_ac
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (fun u => max 0 (-deriv f u)) volume a b := by
  have h_int_deriv : IntervalIntegrable (deriv f) volume a b :=
    AbsolutelyContinuousOnInterval.intervalIntegrable_deriv hf
  have h_eq : (fun u => max 0 (-deriv f u)) = fun u => (|deriv f u| - deriv f u) / 2 := by
    funext u
    rcases le_total 0 (deriv f u) with hu | hu
    · rw [abs_of_nonneg hu, max_eq_left (neg_nonpos.mpr hu)]; ring
    · rw [abs_of_nonpos hu, max_eq_right (neg_nonneg.mpr hu)]; ring
  rw [h_eq]
  exact (h_int_deriv.abs.sub h_int_deriv).div_const 2

/--
A coordinate projection of an absolutely continuous `EuclideanSpace`-valued curve is
absolutely continuous, since coordinate projection is `1`-Lipschitz. Reusable version of the
coordinate-projection step used (inline, once per coordinate) throughout `Bounds/Delta.lean`,
via the public composition lemma `LipschitzWith.comp_absolutelyContinuousOnInterval`.
-/
lemma absolutelyContinuousOnInterval_apply
    {n : Type*} [Fintype n] {F : ℝ → EuclideanSpace ℝ n} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b) (j : n) :
    AbsolutelyContinuousOnInterval (fun u => F u j) a b := by
  have h_lip : LipschitzWith 1 (fun x : EuclideanSpace ℝ n => x j) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      simpa [dist_eq_norm] using PiLp.norm_apply_le (x - y) j)
  exact h_lip.comp_absolutelyContinuousOnInterval hF

/--
The Eq. (2.3) deviation from monotonicity of the signed path equals the Eq. (3.6)
deviation from monotonicity of its canonical positive/negative split, matching the
identification of `z↓(μ)` used in Section 5.2.2's proof of Theorem 2.2.

Informal proof: write `f(u') = u' x_lasso(u')ᵢ`. For `j = inl i`,
`signedCanonicalSplit (x_lasso u') (inl i) = max(x_lasso(u')ᵢ, 0)`, so
`u' ↦ u' * (signedCanonicalSplit (x_lasso u')) (inl i) = u' ↦ u' * max(x_lasso(u')ᵢ, 0)`.
For `u' ≥ 0`, scalar multiplication by `u'` distributes over `max(·,0)` (`mul_max_of_nonneg`),
so this function equals `u' ↦ max(u' x_lasso(u')ᵢ, 0) = u' ↦ max(f(u'), 0)` on all of
`[0,∞)`; in particular the two functions agree on the open neighbourhood `(0,∞)` of every
`u ∈ (0,μ)`, so they have the same derivative there (`Filter.EventuallyEq.deriv_eq`). The
symmetric computation for `j = inr i` matches `u' ↦ u' * max(-x_lasso(u')ᵢ,0)` with
`u' ↦ max(-f(u'),0)` on `(0,μ)`. Since the two integrands agree pointwise on the open interval
`(0,μ)`, `intervalIntegral.integral_congr_Ioo_of_le` identifies the two `inl`/`inr` integrals
appearing in `positiveZDownward` (after splitting the `ι ⊕ ι` sum via `Fintype.sum_sum_type`)
with the matching `u' ↦ u' * max(±f(u'),0)`-integrals; combining those two integrals for fixed
`i` into the single integral of their sum (matching `signedZDownward`'s shape) uses
`intervalIntegral.integral_add`, which needs interval-integrability of each summand. That
integrability is obtained exactly as in the "positive-path regularity" argument used for
`positiveZDownward_summand_differentiableAt` in `Bounds/Delta.lean` (Lemma 4.9): `h_regular`
gives absolute continuity of the *scaled* split path `scaledPrimalPath (signedCanonicalSplit ∘
x_lasso)` on `[0,μ]` (not just of `x_lasso` on positive compacts — the scaling by `u'` is what
controls behaviour down to `u'=0`, matching how the un-split `positiveZDownward` bounds are
proved from `LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)`
rather than from regularity of `x_lasso` itself); projecting onto coordinates `inl i`/`inr i`
(`absolutelyContinuousOnInterval_apply`) and applying
`intervalIntegrable_max_zero_neg_deriv_of_ac` gives the needed
integrability of `u ↦ max 0 (-deriv (fun u' => u' * max(±x_lasso u' i, 0)) u)`.
See Sec. 5.2.2 ("Note that the quantity `z↓(μ)` ... corresponds to ...") of
<https://arxiv.org/abs/2509.18766>.
-/
lemma positiveZDownward_signedCanonicalSplit_eq
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts
      (scaledPrimalPath (fun ν => signedCanonicalSplit (x_lasso ν))))
    (μ : ℝ) (hμ : 0 ≤ μ) :
    positiveZDownward (fun ν => signedCanonicalSplit (x_lasso ν)) μ =
      signedZDownward x_lasso μ := by
  set y : ℝ → EuclideanSpace ℝ (ι ⊕ ι) := fun ν => signedCanonicalSplit (x_lasso ν) with hy_def
  have hac_y : AbsolutelyContinuousOnInterval (scaledPrimalPath y) 0 μ :=
    h_regular.absolutelyContinuousOn_Icc 0 μ le_rfl hμ
  unfold positiveZDownward
  rw [Fintype.sum_sum_type]
  unfold signedZDownward
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hy_inl :
      (fun u' => u' * (y u').ofLp (Sum.inl i)) = fun u' => u' * max (x_lasso u' i) 0 := by
    funext u'; simp [y, signedCanonicalSplit, coordinatePositivePart, euclideanOf]
  have hy_inr :
      (fun u' => u' * (y u').ofLp (Sum.inr i)) = fun u' => u' * max (-(x_lasso u' i)) 0 := by
    funext u'; simp [y, signedCanonicalSplit, coordinateNegativePart, euclideanOf]
  rw [hy_inl, hy_inr]
  have hac_inl : AbsolutelyContinuousOnInterval (fun u => u * max (x_lasso u i) 0) 0 μ := by
    have h := absolutelyContinuousOnInterval_apply hac_y (Sum.inl i)
    have heq : (fun u => (scaledPrimalPath y u) (Sum.inl i)) =
        fun u => u * max (x_lasso u i) 0 := by
      funext u
      simp [scaledPrimalPath, y, signedCanonicalSplit, coordinatePositivePart, euclideanOf,
        smul_eq_mul]
    rwa [heq] at h
  have hac_inr : AbsolutelyContinuousOnInterval (fun u => u * max (-(x_lasso u i)) 0) 0 μ := by
    have h := absolutelyContinuousOnInterval_apply hac_y (Sum.inr i)
    have heq : (fun u => (scaledPrimalPath y u) (Sum.inr i)) =
        fun u => u * max (-(x_lasso u i)) 0 := by
      funext u
      simp [scaledPrimalPath, y, signedCanonicalSplit, coordinateNegativePart, euclideanOf,
        smul_eq_mul]
    rwa [heq] at h
  have hint_inl : IntervalIntegrable
      (fun u => max 0 (-deriv (fun u' => u' * max (x_lasso u' i) 0) u)) volume 0 μ :=
    intervalIntegrable_max_zero_neg_deriv_of_ac hac_inl
  have hint_inr : IntervalIntegrable
      (fun u => max 0 (-deriv (fun u' => u' * max (-(x_lasso u' i)) 0) u)) volume 0 μ :=
    intervalIntegrable_max_zero_neg_deriv_of_ac hac_inr
  have hint_inl' : IntervalIntegrable
      (fun u => (1 + u) * max 0 (-deriv (fun u' => u' * max (x_lasso u' i) 0) u)) volume 0 μ := by
    have h2 := hint_inl.continuousOn_mul
      (show ContinuousOn (fun u : ℝ => (1 : ℝ) + u) (Set.uIcc 0 μ) by fun_prop)
    simpa [mul_comm] using h2
  have hint_inr' : IntervalIntegrable
      (fun u => (1 + u) * max 0 (-deriv (fun u' => u' * max (-(x_lasso u' i)) 0) u))
      volume 0 μ := by
    have h2 := hint_inr.continuousOn_mul
      (show ContinuousOn (fun u : ℝ => (1 : ℝ) + u) (Set.uIcc 0 μ) by fun_prop)
    simpa [mul_comm] using h2
  rw [← intervalIntegral.integral_add hint_inl' hint_inr']
  apply intervalIntegral.integral_congr_Ioo_of_le hμ
  intro u hu
  dsimp only
  have hu0 : 0 < u := hu.1
  have hderiv_inl : deriv (fun u' => u' * max (x_lasso u' i) 0) u =
      deriv (fun u' => max (u' * x_lasso u' i) 0) u := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hu0] with t ht
    rw [mul_max_of_nonneg _ _ (Set.mem_Ioi.mp ht).le, mul_zero]
  have hderiv_inr : deriv (fun u' => u' * max (-(x_lasso u' i)) 0) u =
      deriv (fun u' => max (-(u' * x_lasso u' i)) 0) u := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hu0] with t ht
    rw [mul_max_of_nonneg _ _ (Set.mem_Ioi.mp ht).le, mul_neg, mul_zero]
  rw [hderiv_inl, hderiv_inr]
  ring

/-! ## Signed-lasso main theorems -/

omit [Fintype ι] in
/--
Coordinatewise nonnegativity of the positive-flow time average, for nonnegative
times.  Since `posEffectiveParameter u v` is nonnegative for every `v`
(`posEffectiveParameter_nonnegative`), its average over `[0, t]` is nonnegative
for `t ≥ 0`, by `intervalIntegral.integral_nonneg`.
-/
private lemma posAverageTrajectory_nonneg
    (u : ℝ → EuclideanSpace ℝ ι) (t : ℝ) (ht : 0 ≤ t) :
    Nonnegative (posAverageTrajectory u t) := by
  intro j
  dsimp [posAverageTrajectory, euclideanOf]
  refine mul_nonneg (div_nonneg zero_le_one ht) ?_
  exact intervalIntegral.integral_nonneg ht
    (fun v _ => posEffectiveParameter_nonnegative u v j)

/--
Theorem 2.2: an approximate connection to the lasso minimum in the general case.

Informal proof reference: `docs/Lasso.md`, Section 5.2.2.  This declaration now
appears after both `dln_dynamics_reduction` and `lasso_objective_reduction`,
matching the proof sketch.

Informal proof (Section 5.2.2): let `y(μ) = signedCanonicalSplit (x_lasso μ)`. By Lemma
5.1(2) (`lasso_minimizer_to_augmented_positive_minimizer`), `y` minimizes the augmented
positive lasso; by `signedCanonicalSplit_path_regular`, `y` inherits local absolute
continuity from `x_lasso`. The signed-to-positive dynamics reduction
(`dln_dynamics_reduction`) exhibits `u_pos ε τ = signedToPositiveWeights (w ε (2τ))` as a
positive DLN flow for the augmented data from `signedToPositiveInitialization β γ`
(nondegenerate via `signed_initialization_nondegenerate_iff` since `hβγ` holds). Applying
Theorem 3.2 (`pos_lasso_connection_approx`) to this augmented system bounds
`positiveLassoObjective_aug(posAverageTrajectory u_pos ...)` above by
`posLassoMin_aug + C·suboptimalityGap(positiveZDownward y s) + δ`, eventually as `ε → 0`.
`posLassoMin_aug = lassoMin` (Lemma 5.1(3), `lasso_min_eq_augmented_pos_lasso_min`) and
`positiveZDownward y s = signedZDownward x_lasso s`
(`positiveZDownward_signedCanonicalSplit_eq`). Finally,
`averageTrajectory (w ε) = splitDifference (posAverageTrajectory u_pos ...)`
(`signed_average_eq_split_positive_average`, with time scalings matched via
`posTimeFromRescaled_eq_half_timeFromRescaled`), and Lemma 5.1(1)
(`lasso_split_objective_le`) bounds the signed objective above by the augmented positive
objective, giving the chain of inequalities in Sec. 5.2.2 of
<https://arxiv.org/abs/2509.18766>.
-/
theorem lasso_connection_approx
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hdata : ProblemData M r lambda)
    (hβγ : ∀ i, β i ≠ γ i ∧ β i ≠ -γ i)
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s))
      ≤ lassoMin M r lambda s +
        C * suboptimalityGap lambda s (signedZDownward x_lasso s) + δ := by
  set y : ℝ → EuclideanSpace ℝ (ι ⊕ ι) := fun μ => signedCanonicalSplit (x_lasso μ) with hy_def
  set u_pos : ℝ → ℝ → EuclideanSpace ℝ (ι ⊕ ι) :=
    fun ε τ => signedToPositiveWeights ((w ε) (2 * τ)) with hu_pos_def
  have hpenalty : ∀ μ : ℝ, 0 < μ → 0 ≤ lambda + 1 / μ := by
    intro μ hμ
    have h1 := hdata.lambda_nonneg
    have h2 : (0 : ℝ) < 1 / μ := by positivity
    linarith
  have hdata_aug : ProblemData (augmentedMatrix M) (augmentedVector r) lambda :=
    augmented_problem_data M r lambda hdata
  have hβ_aug : NonzeroCoordinates (signedToPositiveInitialization β γ) :=
    (signed_initialization_nondegenerate_iff β γ).mpr hβγ
  have hu_aug : ∀ ε > 0, posDlnGradientFlow (augmentedMatrix M) (augmentedVector r) lambda ε
      (signedToPositiveInitialization β γ) (u_pos ε) :=
    fun ε hε => dln_dynamics_reduction M r lambda hdata β γ w ε hε (hw ε hε)
  have hy_pos : ∀ μ > 0,
      IsPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ (y μ) :=
    fun μ hμ => lasso_minimizer_to_augmented_positive_minimizer M r lambda μ (x_lasso μ)
      (hpenalty μ hμ) (hx_lasso μ hμ)
  have h_regular_aug : LocallyAbsolutelyContinuousOnPositiveCompacts y :=
    signedCanonicalSplit_path_regular x_lasso h_regular
  obtain ⟨C, hC_pos, h_pos_bound⟩ :=
    pos_lasso_connection_approx (augmentedMatrix M) (augmentedVector r) lambda
      (signedToPositiveInitialization β γ) u_pos hdata_aug hβ_aug hu_aug y hy_pos h_regular_aug
  refine ⟨C, hC_pos, fun s hs δ hδ => ?_⟩
  have h_reg_scaled_y : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath y) :=
    scaledPrimalPath_regular_of_path_regular (augmentedMatrix M) (augmentedVector r) lambda y
      hdata_aug hy_pos h_regular_aug
  have hZeq : positiveZDownward y s = signedZDownward x_lasso s :=
    positiveZDownward_signedCanonicalSplit_eq x_lasso h_reg_scaled_y s hs.le
  have h_min_eq :
      posLassoMin (augmentedMatrix M) (augmentedVector r) lambda s = lassoMin M r lambda s :=
    (lasso_min_eq_augmented_pos_lasso_min M r lambda s (hpenalty s hs) (x_lasso s)
      (hx_lasso s hs)).symm
  have h_bound := h_pos_bound s hs δ hδ
  rw [hZeq, h_min_eq] at h_bound
  filter_upwards [h_bound, show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, Set.mem_Ioi.mpr one_pos, fun _ hx => hx⟩] with ε hεb hε
  obtain ⟨hε_pos, hε_lt_one⟩ := hε
  have hlog_pos : 0 < Real.log (1 / ε) := Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  have ht_pos : 0 < posTimeFromRescaled ε s := by
    dsimp [posTimeFromRescaled]
    exact mul_pos (div_pos hs (by norm_num)) hlog_pos
  have hy_nonneg : Nonnegative (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) :=
    posAverageTrajectory_nonneg (u_pos ε) (posTimeFromRescaled ε s) ht_pos.le
  have heq : averageTrajectory (w ε) (timeFromRescaled ε s) =
      splitDifference (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) := by
    rw [signed_average_eq_split_positive_average (w ε) (timeFromRescaled ε s)
        (hw ε hε_pos).cont_diff.continuous,
      ← posTimeFromRescaled_eq_half_timeFromRescaled]
  rw [heq]
  refine le_trans ?_ hεb
  exact lasso_split_objective_le M r lambda s
    (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) hy_nonneg (hpenalty s hs)

/--
Theorem 2.1: under monotonicity, the signed average trajectory exactly connects
to the lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 5.2.1.  The earlier skeleton
required an extra `h_regular`; this version follows the paper-level theorem
statement and leaves regularity to the positive monotone theorem plus reductions.

Informal proof (Section 5.2.1): write `x = x_lasso`, `y(μ) = signedCanonicalSplit (x μ)
= (x(μ)₊, x(μ)₋)`.  By Lemma 5.1(2) (`lasso_minimizer_to_augmented_positive_minimizer`),
`y(μ)` minimizes the augmented positive lasso; by the vanishing-near-zero argument for
`z(μ) = μ x(μ)` (`signedCanonicalSplit_scaled_monotonicity`), `μ ↦ μ y(μ)` is
coordinatewise nondecreasing on `(0,∞)`.  The signed-to-positive dynamics reduction
(`dln_dynamics_reduction`) shows `u_pos ε τ = signedToPositiveWeights (w ε (2τ))` is a
positive DLN flow for the augmented data from the augmented initialization
(`signedToPositiveInitialization β γ`, nondegenerate by
`signed_initialization_nondegenerate_iff` since `hβγ` holds).  Applying
`pos_lasso_connection_monotone` to this augmented system gives
`positiveLassoObjective_aug(posAverageTrajectory u_pos ...) → posLassoMin_aug`, and
`posLassoMin_aug = lassoMin` by Lemma 5.1(3) (`lasso_min_eq_augmented_pos_lasso_min`).
Since `averageTrajectory (w ε) = splitDifference (posAverageTrajectory u_pos ...)`
(`signed_average_eq_split_positive_average`, matching the time scalings via
`posTimeFromRescaled_eq_half_timeFromRescaled`), Lemma 5.1(1)
(`lasso_split_objective_le`) bounds the signed objective above by the augmented
positive objective, while `lassoMin ≤` any signed objective value trivially (it is an
infimum).  The signed objective is thus squeezed between the constant `lassoMin` and a
sequence converging to `lassoMin`, giving the result. See Sec. 5.2.1 of
<https://arxiv.org/abs/2509.18766>.
-/
theorem lasso_connection_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hdata : ProblemData M r lambda)
    (hβγ : ∀ i, β i ≠ γ i ∧ β i ≠ -γ i)
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i,
      MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0) ∨
        AntitoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (lassoMin M r lambda s)) := by
  set y : ℝ → EuclideanSpace ℝ (ι ⊕ ι) := fun μ => signedCanonicalSplit (x_lasso μ) with hy_def
  set u_pos : ℝ → ℝ → EuclideanSpace ℝ (ι ⊕ ι) :=
    fun ε τ => signedToPositiveWeights ((w ε) (2 * τ)) with hu_pos_def
  have hpenalty : ∀ μ : ℝ, 0 < μ → 0 ≤ lambda + 1 / μ := by
    intro μ hμ
    have h1 := hdata.lambda_nonneg
    have h2 : (0 : ℝ) < 1 / μ := by positivity
    linarith
  have hdata_aug : ProblemData (augmentedMatrix M) (augmentedVector r) lambda :=
    augmented_problem_data M r lambda hdata
  have hβ_aug : NonzeroCoordinates (signedToPositiveInitialization β γ) :=
    (signed_initialization_nondegenerate_iff β γ).mpr hβγ
  have hu_aug : ∀ ε > 0, posDlnGradientFlow (augmentedMatrix M) (augmentedVector r) lambda ε
      (signedToPositiveInitialization β γ) (u_pos ε) :=
    fun ε hε => dln_dynamics_reduction M r lambda hdata β γ w ε hε (hw ε hε)
  have hy_pos : ∀ μ > 0,
      IsPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ (y μ) :=
    fun μ hμ => lasso_minimizer_to_augmented_positive_minimizer M r lambda μ (x_lasso μ)
      (hpenalty μ hμ) (hx_lasso μ hμ)
  have h_monotone_aug : ∀ j : ι ⊕ ι, MonotoneOn (fun μ => μ * y μ j) (Set.Ioi 0) :=
    signedCanonicalSplit_scaled_monotonicity M r lambda x_lasso hdata hx_lasso h_monotone
  have h_pos_tendsto :=
    pos_lasso_connection_monotone (augmentedMatrix M) (augmentedVector r) lambda
      (signedToPositiveInitialization β γ) s hs u_pos hdata_aug hβ_aug hu_aug y hy_pos
      h_monotone_aug
  have h_min_eq :
      posLassoMin (augmentedMatrix M) (augmentedVector r) lambda s = lassoMin M r lambda s :=
    (lasso_min_eq_augmented_pos_lasso_min M r lambda s (hpenalty s hs) (x_lasso s)
      (hx_lasso s hs)).symm
  rw [h_min_eq] at h_pos_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_pos_tendsto ?_ ?_
  · -- `lassoMin M r lambda s` lower-bounds every value of the signed objective, since
    -- `lassoMin` is the infimum of `lassoObjective` and `x_lasso s` witnesses the
    -- boundedness needed to apply `ciInf_le`.
    refine Filter.Eventually.of_forall (fun ε => ?_)
    have hbdd : BddBelow (Set.range (lassoObjective M r lambda s)) :=
      ⟨lassoObjective M r lambda s (x_lasso s), by
        rintro _ ⟨z, rfl⟩
        exact isMinOn_iff.mp (hx_lasso s hs) z (Set.mem_univ z)⟩
    exact ciInf_le hbdd _
  · -- For `ε` small enough that `log(1/ε) > 0`, the signed average trajectory equals the
    -- difference of the augmented positive trajectory's two halves
    -- (`signed_average_eq_split_positive_average`), and Lemma 5.1(1)
    -- (`lasso_split_objective_le`) bounds its signed objective by the augmented positive
    -- objective.
    filter_upwards [show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      exact ⟨1, Set.mem_Ioi.mpr one_pos, fun _ hx => hx⟩] with ε hε
    obtain ⟨hε_pos, hε_lt_one⟩ := hε
    have hlog_pos : 0 < Real.log (1 / ε) :=
      Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
    have ht_pos : 0 < posTimeFromRescaled ε s := by
      dsimp [posTimeFromRescaled]
      exact mul_pos (div_pos hs (by norm_num)) hlog_pos
    have hy_nonneg : Nonnegative (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) :=
      posAverageTrajectory_nonneg (u_pos ε) (posTimeFromRescaled ε s) ht_pos.le
    have heq : averageTrajectory (w ε) (timeFromRescaled ε s) =
        splitDifference (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) := by
      rw [signed_average_eq_split_positive_average (w ε) (timeFromRescaled ε s)
          (hw ε hε_pos).cont_diff.continuous,
        ← posTimeFromRescaled_eq_half_timeFromRescaled]
    rw [heq]
    exact lasso_split_objective_le M r lambda s
      (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) hy_nonneg (hpenalty s hs)

end Lasso

end
