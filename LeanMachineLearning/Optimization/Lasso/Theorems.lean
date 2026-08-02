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
public import LeanMachineLearning.Optimization.Lasso.Bounds.Energy
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

/-- `sqrt(a + b) ≤ sqrt a + sqrt b` for nonnegative `a, b`. Not in Mathlib under this name;
proved by squaring, since `(sqrt a + sqrt b)^2 = a + b + 2 sqrt a sqrt b ≥ a + b`. -/
private lemma sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have hsa := Real.sq_sqrt ha
    have hsb := Real.sq_sqrt hb
    nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt a + Real.sqrt b :=
      Real.sqrt_sq (by positivity)

/-- The rescaled integrated trajectory `τ ↦ z^ε(τ)` is continuously differentiable.
This extracts the `C¹` argument that is reused in several absolute-continuity proofs
(`pathDelta_ac`, `inner_diff_absolutelyContinuous`, etc.).

Informal proof: `posIntegratedTrajectoryRescaled_hasDerivAt` gives a derivative at every point,
and the derivative is a composition of continuous functions (`coordinateSquare`, the flow `u`,
and the affine time change), hence continuous.

CITATION: `docs/Lasso.md`, Section 4.6. -/
private lemma posIntegratedTrajectoryRescaled_contDiff_one
    (ε : ℝ) (u : ℝ → EuclideanSpace ℝ ι)
    (h_cont_u : Continuous u) (h_log_ne : Real.log (1 / ε) ≠ 0) :
    ContDiff ℝ 1 (fun (τ : ℝ) => posIntegratedTrajectoryRescaled ε u τ) := by
  have h_zε_deriv : ∀ (τ : ℝ), HasDerivAt (fun (ρ : ℝ) => posIntegratedTrajectoryRescaled ε u ρ)
      (posEffectiveParameter u (posTimeFromRescaled ε τ)) τ :=
    fun τ => posIntegratedTrajectoryRescaled_hasDerivAt ε u τ h_cont_u h_log_ne
  have h_deriv_eq : deriv (fun (ρ : ℝ) => posIntegratedTrajectoryRescaled ε u ρ) =
      (fun (τ : ℝ) => posEffectiveParameter u (posTimeFromRescaled ε τ)) :=
    funext (fun τ => (h_zε_deriv τ).deriv)
  have h_cont_time : Continuous (posTimeFromRescaled ε) := by
    unfold posTimeFromRescaled; fun_prop
  have h_cont_coordSquare :
      Continuous (coordinateSquare : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
    by
    let e : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toContinuousLinearEquiv
    have h_proj_cont (i : ι) : Continuous (fun (x : EuclideanSpace ℝ ι) => x i) :=
      (continuous_apply i).comp
        ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous)
    have h_eq : coordinateSquare = e ∘ (fun (x : EuclideanSpace ℝ ι) => fun i => x i * x i) := by
      ext x i; simp [coordinateSquare, euclideanOf, e]
    rw [h_eq]
    exact e.continuous.comp
      (continuous_pi (fun i => Continuous.mul (h_proj_cont i) (h_proj_cont i)))
  have h_cont_deriv :
      Continuous (fun (τ : ℝ) => posEffectiveParameter u (posTimeFromRescaled ε τ)) :=
    by
    dsimp [posEffectiveParameter]
    exact h_cont_coordSquare.comp (h_cont_u.comp h_cont_time)
  exact contDiff_one_iff_deriv.mpr ⟨fun τ => (h_zε_deriv τ).differentiableAt,
    h_deriv_eq ▸ h_cont_deriv⟩

/-- The coordinate projection `x ↦ x i` is `1`-Lipschitz on `EuclideanSpace ℝ ι`. -/
private lemma coordinateProjection_lipschitzWith (i : ι) :
    LipschitzWith 1 (fun (x : EuclideanSpace ℝ ι) => (x i : ℝ)) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simpa [dist_eq_norm] using PiLp.norm_apply_le (x - y) i

/-- The inner product of an absolutely continuous vector path with the difference of a
`C¹` rescaled integrated trajectory and an absolutely continuous path is absolutely continuous.

This is used to show the energy term `E^ε(τ) = ⟨w(τ), z^ε(τ) - z(τ)⟩ + Δ^ε(τ)` is absolutely
continuous on `[0, s]` in `positive_energy_integrated_bound`.

Informal proof: `z^ε` is `C¹` (its derivative exists everywhere and is continuous), and `z` is
absolutely continuous by hypothesis. Hence their difference is absolutely continuous. The inner
product `⟨w, z^ε - z⟩` is a finite sum of products of coordinate projections; each coordinate of
`w` is absolutely continuous (from `hw_ac`), each coordinate of `z^ε - z` is absolutely continuous,
and products of absolutely continuous real functions are absolutely continuous. Summing preserves
absolute continuity.

CITATION: `docs/Lasso.md`, Section 4.6 (energy differential inequality integration). -/
private lemma inner_diff_absolutelyContinuous
    (ε : ℝ) (u : ℝ → EuclideanSpace ℝ ι) (z : ℝ → EuclideanSpace ℝ ι) (w : ℝ → EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 ≤ s)
    (h_cont_u : Continuous u) (h_log_ne : Real.log (1 / ε) ≠ 0)
    (hz_ac : LocallyAbsolutelyContinuousOnNonnegativeCompacts z)
    (hw_ac : LocallyAbsolutelyContinuousOnNonnegativeCompacts w) :
    AbsolutelyContinuousOnInterval
      (fun (τ : ℝ) => inner ℝ (w τ) (posIntegratedTrajectoryRescaled ε u τ - z τ)) 0 s := by
  have hdiff_ac : AbsolutelyContinuousOnInterval
      (fun (τ : ℝ) => posIntegratedTrajectoryRescaled ε u τ - z τ) 0 s :=
    ((posIntegratedTrajectoryRescaled_contDiff_one ε u h_cont_u
      h_log_ne).contDiffOn.absolutelyContinuousOnInterval).sub
      (hz_ac.absolutelyContinuousOn_Icc 0 s le_rfl hs)
  have h_coord_ac : ∀ (i : ι), AbsolutelyContinuousOnInterval
      (fun (τ : ℝ) => (w τ : EuclideanSpace ℝ ι) i *
        (posIntegratedTrajectoryRescaled ε u τ - z τ) i) 0 s := by
    intro i
    have h_lip : LipschitzWith 1 (fun (x : EuclideanSpace ℝ ι) => (x i : ℝ)) :=
      coordinateProjection_lipschitzWith i
    exact (h_lip.comp_absolutelyContinuousOnInterval
      (hw_ac.absolutelyContinuousOn_Icc 0 s le_rfl hs)).mul
      (h_lip.comp_absolutelyContinuousOnInterval hdiff_ac)
  convert absolutelyContinuousOnInterval_sum Finset.univ _ 0 s (fun i _ => h_coord_ac i) with τ
  simp [PiLp.inner_apply, PiLp.sub_apply, RCLike.inner_apply, mul_comm]
/--
Section 4.6, Eq. (4.15) restated as a bound holding **uniformly over `[0, s]`**, not just at the
endpoint `τ = s`. This is the key extra ingredient needed for `positive_energy_integrated_bound`:
integrating the energy differential inequality requires controlling `Δᵋ(τ)` at *every* `τ ≤ s`
(it appears under a square root inside the integrand), not merely its value at `s`.

Informal proof: Apply `positive_delta_complementarity_bound`'s a.e. derivative bound for `Δᵋ` on
`[0, s]`, together with the absolute continuity of `Δᵋ` (`pathDelta_ac`) and of the majorant
`G(τ) = C(1/L·(τ + z↑(τ)) + z↓(τ)) + Cδ/s·τ` (`G_ac`), to conclude via `bound_of_deriv_bound`
that `Δᵋ(τ') ≤ G(τ')` for *every* `τ' ∈ [0, s]` (not just `τ' = s`), by applying that FTC-comparison
lemma with upper endpoint `τ'` instead of `s` (restricting the `[0,s]`-facts to `[0,τ']` via
`AbsolutelyContinuousOnInterval.mono` and the trivial set inclusion `Icc 0 τ' ⊆ Icc 0 s`). Since
`G` is monotone nondecreasing on `[0, s]` (a sum of the identity, `positiveZUpward_monotoneOn`,
and `positiveZDownward_monotoneOn`, each with a nonnegative coefficient), `G(τ') ≤ G(s)` for
`τ' ≤ s`, giving the uniform bound `Δᵋ(τ') ≤ G(s)` for all `τ' ∈ [0, s]`.
-/
private lemma pathDelta_uniform_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (Mdagger : Matrix ι ι ℝ) (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s : ℝ, 0 < s → ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
            (scaledPrimalPath x_lasso) τ
          ≤ C * (1 / Real.log (1 / ε) * (s + positiveZUpward x_lasso s) +
              positiveZDownward x_lasso s) + C * δ := by
  obtain ⟨C, hC_pos, h_diff⟩ := positive_delta_complementarity_bound M r lambda β u hdata hβ hu
    x_lasso hx_lasso Mdagger w hdual hdual_selected h_local_affine h_regular h_lipschitz
  refine ⟨C, hC_pos, fun s hs δ hδ => ?_⟩
  have h_delta_pos : 0 < C * δ / s := div_pos (mul_pos hC_pos hδ) hs
  filter_upwards [h_diff s hs (C * δ / s) h_delta_pos,
      show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε h_deriv_bound hε_mem
  rcases hε_mem with ⟨hε_pos, hε_lt_one⟩
  have hlog_pos : 0 < Real.log (1 / ε) := Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  set F := fun σ => pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    (scaledPrimalPath x_lasso) σ with hF_def
  set G := fun σ => C * (1 / Real.log (1 / ε) * (σ + positiveZUpward x_lasso σ) +
    positiveZDownward x_lasso σ) + C * δ / s * σ with hG_def
  have hF_ac : AbsolutelyContinuousOnInterval F 0 s :=
    pathDelta_ac M ε (u ε) x_lasso s hs.le (hu ε hε_pos).cont_diff.continuous hlog_pos.ne'
      h_regular
  have hG_ac : AbsolutelyContinuousOnInterval G 0 s := G_ac C ε s δ hs x_lasso h_regular
  have hF0 : F 0 = 0 := pathDelta_zero M ε (u ε) x_lasso
  have hG0 : G 0 = 0 := by
    simp only [hG_def]
    rw [(z_upward_downward_zero x_lasso).1, (z_upward_downward_zero x_lasso).2]
    ring
  -- `deriv G τ` matches the RHS of `positive_delta_complementarity_bound`'s bound wherever
  -- `positiveZUpward`/`positiveZDownward` are differentiable, i.e. a.e. (mirroring
  -- `positive_path_delta_bound_full`'s `hG_deriv` computation).
  have h_pos_z_diff := positiveZ_ae_differentiable x_lasso s hs h_local_affine h_regular
  have hderiv_G_eq : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv G τ =
      C * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
        deriv (positiveZDownward x_lasso) τ) + C * δ / s := by
    filter_upwards [h_pos_z_diff] with τ hτ_diff hτ_mem
    obtain ⟨hτ_up_diff, hτ_down_diff⟩ := hτ_diff hτ_mem
    have h_up_hasDeriv : HasDerivAt (positiveZUpward x_lasso)
        (deriv (positiveZUpward x_lasso) τ) τ := hτ_up_diff.hasDerivAt
    have h_down_hasDeriv : HasDerivAt (positiveZDownward x_lasso)
        (deriv (positiveZDownward x_lasso) τ) τ := hτ_down_diff.hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => t + positiveZUpward x_lasso t)
        (1 + deriv (positiveZUpward x_lasso) τ) τ := (hasDerivAt_id' τ).add h_up_hasDeriv
    have h2 : HasDerivAt
        (fun t : ℝ => 1 / Real.log (1 / ε) * (t + positiveZUpward x_lasso t) +
          positiveZDownward x_lasso t)
        (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
          deriv (positiveZDownward x_lasso) τ) τ :=
      (h1.const_mul (1 / Real.log (1 / ε))).add h_down_hasDeriv
    have h3 : HasDerivAt
        (fun t : ℝ => C * (1 / Real.log (1 / ε) * (t + positiveZUpward x_lasso t) +
            positiveZDownward x_lasso t) + C * δ / s * t)
        (C * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + C * δ / s * 1) τ :=
      (h2.const_mul C).add ((hasDerivAt_id' τ).const_mul (C * δ / s))
    rw [hG_def, h3.deriv]
    ring
  have h_deriv_le : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv F τ ≤ deriv G τ := by
    filter_upwards [h_deriv_bound, hderiv_G_eq] with τ hτ1 hτ2 hτ_mem
    rw [hτ2 hτ_mem]
    exact hτ1 hτ_mem
  intro τ' hτ'
  have h_sub : Set.uIcc (0 : ℝ) τ' ⊆ Set.uIcc (0 : ℝ) s := by
    rw [Set.uIcc_of_le hτ'.1, Set.uIcc_of_le hs.le]
    exact Set.Icc_subset_Icc_right hτ'.2
  have hFτ'_le_Gτ' : F τ' ≤ G τ' := by
    apply bound_of_deriv_bound hτ'.1 _ hF0 hG0 (hF_ac.mono h_sub) (hG_ac.mono h_sub)
    filter_upwards [h_deriv_le] with τ hτ_imp hτ_mem
    exact hτ_imp (Set.Icc_subset_Icc_right hτ'.2 hτ_mem)
  have hG_mono : G τ' ≤ G s := by
    have h_up_mono := positiveZUpward_monotoneOn x_lasso h_regular
    have h_down_mono := positiveZDownward_monotoneOn x_lasso h_regular
    have h1 : positiveZUpward x_lasso τ' ≤ positiveZUpward x_lasso s :=
      h_up_mono hτ'.1 hs.le hτ'.2
    have h2 : positiveZDownward x_lasso τ' ≤ positiveZDownward x_lasso s :=
      h_down_mono hτ'.1 hs.le hτ'.2
    have hL_nonneg : 0 ≤ 1 / Real.log (1 / ε) := by positivity
    have hCδs_nonneg : 0 ≤ C * δ / s := by positivity
    simp only [hG_def]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hτ'.2 h1) hC_pos.le,
      mul_le_mul_of_nonneg_left h2 hC_pos.le,
      mul_le_mul_of_nonneg_left hτ'.2 hCδs_nonneg]
  have hGs_eq : G s = C * (1 / Real.log (1 / ε) * (s + positiveZUpward x_lasso s) +
      positiveZDownward x_lasso s) + C * δ := by
    simp only [hG_def]
    field_simp
  calc
    pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ'
        = F τ' := rfl
    _ ≤ G τ' := hFτ'_le_Gτ'
    _ ≤ G s := hG_mono
    _ = _ := hGs_eq

/--
Monotone-case analogue of `pathDelta_uniform_bound`: the same uniform bound on `Δᵋ(τ)` over
`[0,s]`, with `h_local_affine` replaced by coordinatewise monotonicity `h_mono` of
`z = scaledPrimalPath x_lasso`.

Informal proof: identical to `pathDelta_uniform_bound`'s proof, with the single change that
`positive_delta_complementarity_bound` is replaced by
`positive_delta_complementarity_bound_of_monotone` (`Bounds/Delta.lean`) to obtain the a.e.
derivative bound for `Δᵋ`; the FTC-comparison argument via `bound_of_deriv_bound` and the
monotonicity of `G` (`positiveZUpward_monotoneOn`/`positiveZDownward_monotoneOn`, which hold
unconditionally, not just under `h_mono`) are unchanged. Citation: `docs/Lasso.md`, Sec. 4.6,
Eq. (4.15), and Sec. 3.1/4.7 for the monotone specialization.
-/
private lemma pathDelta_uniform_bound_of_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (Mdagger : Matrix ι ι ℝ) (w : ℝ → EuclideanSpace ℝ ι)
    (_hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (_hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s : ℝ, 0 < s → ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
            (scaledPrimalPath x_lasso) τ
          ≤ C * (1 / Real.log (1 / ε) * (s + positiveZUpward x_lasso s) +
              positiveZDownward x_lasso s) + C * δ := by
  -- Identical to `pathDelta_uniform_bound`'s proof: obtain the a.e. derivative bound
  -- from `positive_delta_complementarity_bound_of_monotone`, then use the FTC-comparison
  -- argument via `bound_of_deriv_bound` and monotonicity of the majorant `G`.
  obtain ⟨C, hC_pos, h_diff⟩ := positive_delta_complementarity_bound_of_monotone M r lambda β u
    hdata hβ hu x_lasso hx_lasso h_mono h_regular h_lipschitz
  refine ⟨C, hC_pos, fun s hs δ hδ => ?_⟩
  have h_delta_pos : 0 < C * δ / s := div_pos (mul_pos hC_pos hδ) hs
  filter_upwards [h_diff s hs (C * δ / s) h_delta_pos,
      show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε h_deriv_bound hε_mem
  rcases hε_mem with ⟨hε_pos, hε_lt_one⟩
  have hlog_pos : 0 < Real.log (1 / ε) := Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  set F := fun σ => pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    (scaledPrimalPath x_lasso) σ with hF_def
  set G := fun σ => C * (1 / Real.log (1 / ε) * (σ + positiveZUpward x_lasso σ) +
    positiveZDownward x_lasso σ) + C * δ / s * σ with hG_def
  have hF_ac : AbsolutelyContinuousOnInterval F 0 s :=
    pathDelta_ac M ε (u ε) x_lasso s hs.le (hu ε hε_pos).cont_diff.continuous hlog_pos.ne'
      h_regular
  have hG_ac : AbsolutelyContinuousOnInterval G 0 s := G_ac C ε s δ hs x_lasso h_regular
  have hF0 : F 0 = 0 := pathDelta_zero M ε (u ε) x_lasso
  have hG0 : G 0 = 0 := by
    simp only [hG_def]
    rw [(z_upward_downward_zero x_lasso).1, (z_upward_downward_zero x_lasso).2]
    ring
  -- `deriv G τ` matches the RHS of `positive_delta_complementarity_bound_of_monotone`'s bound
  -- wherever `positiveZUpward`/`positiveZDownward` are differentiable, i.e. a.e.
  -- Use the monotone version `positiveZ_ae_differentiable_of_monotone` instead of
  -- `positiveZ_ae_differentiable`.
  have h_pos_z_diff := positiveZ_ae_differentiable_of_monotone x_lasso s hs h_mono h_regular
  have hderiv_G_eq : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv G τ =
      C * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
        deriv (positiveZDownward x_lasso) τ) + C * δ / s := by
    filter_upwards [h_pos_z_diff] with τ hτ_diff hτ_mem
    obtain ⟨hτ_up_diff, hτ_down_diff⟩ := hτ_diff hτ_mem
    have h_up_hasDeriv : HasDerivAt (positiveZUpward x_lasso)
        (deriv (positiveZUpward x_lasso) τ) τ := hτ_up_diff.hasDerivAt
    have h_down_hasDeriv : HasDerivAt (positiveZDownward x_lasso)
        (deriv (positiveZDownward x_lasso) τ) τ := hτ_down_diff.hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => t + positiveZUpward x_lasso t)
        (1 + deriv (positiveZUpward x_lasso) τ) τ := (hasDerivAt_id' τ).add h_up_hasDeriv
    have h2 : HasDerivAt
        (fun t : ℝ => 1 / Real.log (1 / ε) * (t + positiveZUpward x_lasso t) +
          positiveZDownward x_lasso t)
        (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
          deriv (positiveZDownward x_lasso) τ) τ :=
      (h1.const_mul (1 / Real.log (1 / ε))).add h_down_hasDeriv
    have h3 : HasDerivAt
        (fun t : ℝ => C * (1 / Real.log (1 / ε) * (t + positiveZUpward x_lasso t) +
            positiveZDownward x_lasso t) + C * δ / s * t)
        (C * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + C * δ / s * 1) τ :=
      (h2.const_mul C).add ((hasDerivAt_id' τ).const_mul (C * δ / s))
    rw [hG_def, h3.deriv]
    ring
  have h_deriv_le : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv F τ ≤ deriv G τ := by
    filter_upwards [h_deriv_bound, hderiv_G_eq] with τ hτ1 hτ2 hτ_mem
    rw [hτ2 hτ_mem]
    exact hτ1 hτ_mem
  intro τ' hτ'
  have h_sub : Set.uIcc (0 : ℝ) τ' ⊆ Set.uIcc (0 : ℝ) s := by
    rw [Set.uIcc_of_le hτ'.1, Set.uIcc_of_le hs.le]
    exact Set.Icc_subset_Icc_right hτ'.2
  have hFτ'_le_Gτ' : F τ' ≤ G τ' := by
    apply bound_of_deriv_bound hτ'.1 _ hF0 hG0 (hF_ac.mono h_sub) (hG_ac.mono h_sub)
    filter_upwards [h_deriv_le] with τ hτ_imp hτ_mem
    exact hτ_imp (Set.Icc_subset_Icc_right hτ'.2 hτ_mem)
  have hG_mono : G τ' ≤ G s := by
    have h_up_mono := positiveZUpward_monotoneOn x_lasso h_regular
    have h_down_mono := positiveZDownward_monotoneOn x_lasso h_regular
    have h1 : positiveZUpward x_lasso τ' ≤ positiveZUpward x_lasso s :=
      h_up_mono hτ'.1 hs.le hτ'.2
    have h2 : positiveZDownward x_lasso τ' ≤ positiveZDownward x_lasso s :=
      h_down_mono hτ'.1 hs.le hτ'.2
    have hL_nonneg : 0 ≤ 1 / Real.log (1 / ε) := by positivity
    have hCδs_nonneg : 0 ≤ C * δ / s := by positivity
    simp only [hG_def]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hτ'.2 h1) hC_pos.le,
      mul_le_mul_of_nonneg_left h2 hC_pos.le,
      mul_le_mul_of_nonneg_left hτ'.2 hCδs_nonneg]
  have hGs_eq : G s = C * (1 / Real.log (1 / ε) * (s + positiveZUpward x_lasso s) +
      positiveZDownward x_lasso s) + C * δ := by
    simp only [hG_def]
    field_simp
  calc
    pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ'
        = F τ' := rfl
    _ ≤ G τ' := hFτ'_le_Gτ'
    _ ≤ G s := hG_mono
    _ = _ := hGs_eq

-- The function τ ↦ 1/(1+τ*λ) is absolutely continuous on [0,s] when λ ≥ 0, s ≥ 0.
-- This uses Lipschitz continuity: denominator ≥ 1 implies the function is λ-Lipschitz.
private lemma one_div_one_plus_tau_mul_lambda_ac (lambda s : ℝ)
    (hlambda_nonneg : 0 ≤ lambda) (hs_nonneg : 0 ≤ s) :
    AbsolutelyContinuousOnInterval (fun (τ : ℝ) => 1 / (1 + τ * lambda)) 0 s := by
  set lam_nn : NNReal := ⟨lambda, hlambda_nonneg⟩ with h_lam_nn_def
  have h_lip :
      LipschitzOnWith lam_nn (fun (τ : ℝ) => 1 / (1 + τ * lambda)) (Set.uIcc (0 : ℝ) s) := by
    refine LipschitzOnWith.of_dist_le_mul (fun τ₁ hτ₁ τ₂ hτ₂ => ?_)
    have hτ₁_nonneg : 0 ≤ τ₁ := by
      rcases Set.mem_uIcc.1 hτ₁ with (⟨h, _⟩ | ⟨h₁, h₂⟩)
      · exact h
      · nlinarith
    have hτ₂_nonneg : 0 ≤ τ₂ := by
      rcases Set.mem_uIcc.1 hτ₂ with (⟨h, _⟩ | ⟨h₁, h₂⟩)
      · exact h
      · nlinarith
    have h_denom1_ne : 1 + τ₁ * lambda ≠ 0 := by nlinarith
    have h_denom2_ne : 1 + τ₂ * lambda ≠ 0 := by nlinarith
    have h_denom_nonneg : 0 ≤ (1 + τ₁ * lambda) * (1 + τ₂ * lambda) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    have h_denom_ge_one : 1 ≤ (1 + τ₁ * lambda) * (1 + τ₂ * lambda) := by
      have h1 : 1 ≤ 1 + τ₁ * lambda := by nlinarith
      have h2 : 1 ≤ 1 + τ₂ * lambda := by nlinarith
      nlinarith
    have h_num_nonneg : 0 ≤ lambda * |τ₁ - τ₂| :=
      mul_nonneg hlambda_nonneg (abs_nonneg _)
    -- Rewrite the LHS difference as a single fraction
    have h_left : 1 / (1 + τ₁ * lambda) - 1 / (1 + τ₂ * lambda) =
        (lambda * (τ₂ - τ₁)) / ((1 + τ₁ * lambda) * (1 + τ₂ * lambda)) := by
      field_simp [h_denom1_ne, h_denom2_ne]
      ring
    -- Using |a·b| = |a|·|b|, |λ|=λ, |τ₂-τ₁|=|τ₁-τ₂|, and |D| = D ≥ 0.
    -- Then a/D ≤ a when D ≥ 1 (div_le_self).
    rw [Real.dist_eq, Real.dist_eq, h_left]
    have h_goal : |lambda * (τ₂ - τ₁) / ((1 + τ₁ * lambda) * (1 + τ₂ * lambda))| ≤
        lambda * |τ₁ - τ₂| := by
      rw [abs_div, abs_of_nonneg h_denom_nonneg, abs_mul,
        abs_of_nonneg hlambda_nonneg, ← abs_neg, neg_sub]
      exact div_le_self h_num_nonneg h_denom_ge_one
    have h_lam_eq : (lam_nn : ℝ) = lambda := rfl
    simpa [h_lam_eq] using h_goal
  exact h_lip.absolutelyContinuousOnInterval

/--
Helper lemma: proves that the scaled energy function F(τ) is absolutely continuous.
Informal proof: Derived from the inner product differential continuity and path delta continuity.
(Source: docs/Lasso.md, Section 4.6)
-/
private lemma positive_energy_F_ac
    {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {r : EuclideanSpace ℝ ι} {lambda : ℝ}
    {s ε : ℝ} (u_eps : ℝ → EuclideanSpace ℝ ι) (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (w : ℝ → EuclideanSpace ℝ ι) (hdata : ProblemData M r lambda) (_hε_pos : 0 < ε) (hs : 0 < s)
    (hlog_ne : Real.log (1 / ε) ≠ 0)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (hdual_ac : LocallyAbsolutelyContinuousOnNonnegativeCompacts w)
    (hu_cont_diff : ContDiff ℝ 1 u_eps) :
    AbsolutelyContinuousOnInterval
      (fun (τ : ℝ) => (1 / (1 + τ * lambda)) *
        (inner ℝ (w τ) (posIntegratedTrajectoryRescaled ε u_eps τ - scaledPrimalPath x_lasso τ) +
        pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε u_eps ρ)
          (scaledPrimalPath x_lasso) τ))
      0 s := by
  have hs_nonneg : 0 ≤ s := hs.le
  -- The inner product term ⟨w(τ), zε(τ) - z(τ)⟩ is absolutely continuous on [0,s]
  have h_inner_ac :=
    inner_diff_absolutelyContinuous ε u_eps (scaledPrimalPath x_lasso) w s hs_nonneg
      hu_cont_diff.continuous hlog_ne h_regular hdual_ac
  -- The path-delta term Δε(τ) = ½‖zε(τ) - z(τ)‖_M² is absolutely continuous on [0,s]
  have h_delta_ac :=
    pathDelta_ac M ε u_eps x_lasso s hs_nonneg hu_cont_diff.continuous hlog_ne h_regular
  -- Sum of the two AC functions is AC
  have h_sum_ac := h_inner_ac.add h_delta_ac
  -- Product of two ℝ→ℝ AC functions is AC; the factor 1/(1+τλ) is AC (λ≥0 ensures denominator ≥1>0)
  exact (one_div_one_plus_tau_mul_lambda_ac lambda s hdata.lambda_nonneg hs_nonneg).mul h_sum_ac

/--
Helper lemma: proves that the bounding function G(τ) is absolutely continuous.
Informal proof: G(τ) is a linear combination of identity, and integrals of the positive
z upward and downward paths.
(Source: docs/Lasso.md, Section 4.6)
-/
private lemma positive_energy_G_ac
    {ι : Type*} [Fintype ι] (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (s C_E L K : ℝ) (hs : 0 < s)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    AbsolutelyContinuousOnInterval
      (fun (τ : ℝ) =>
        K * τ + C_E / L * positiveZUpward x_lasso τ + C_E * positiveZDownward x_lasso τ)
      0 s := by
  have h_id_ac : AbsolutelyContinuousOnInterval (fun τ : ℝ => τ) 0 s := by
    have hK : LipschitzOnWith 1 (fun τ : ℝ => τ) (Set.uIcc 0 s) := fun x _ y _ => by simp
    exact hK.absolutelyContinuousOnInterval
  have h_up_ac : AbsolutelyContinuousOnInterval (positiveZUpward x_lasso) 0 s :=
    positiveZUpward_ac x_lasso s hs.le h_regular
  have h_down_ac : AbsolutelyContinuousOnInterval (positiveZDownward x_lasso) 0 s :=
    positiveZDownward_ac x_lasso s hs.le h_regular
  exact ((h_id_ac.const_mul K).add (h_up_ac.const_mul (C_E / L))).add
    (h_down_ac.const_mul C_E)

/--
Helper lemma: algebraic bound for the product-rule derivative in `positive_energy_deriv_bound`.

Informal proof: Isolates the algebraic steps bounding `C_E·(√(2Δ) + 1/L·(1+z_up') + z_down') + δ_E`
by `K + C_E/L·z_up' + C_E·z_down'`, relying on `√(A+B+C) ≤ √A + √B + √C`.
(Source: docs/Lasso.md, Section 4.6)
-/
private lemma positive_energy_deriv_bound_algebraic
    (s C_E C_D L K δ_E δ_D : ℝ) (z_up' z_down' pathDelta z_up_s z_down_s : ℝ)
    (hL_pos : 0 < L)
    (hC_E_pos : 0 < C_E)
    (hC_D_nonneg : 0 ≤ C_D)
    (_hz_up'_nn : 0 ≤ z_up')
    (_hz_down'_nn : 0 ≤ z_down')
    (_hz_up_s_nn : 0 ≤ z_up_s)
    (_hz_down_s_nn : 0 ≤ z_down_s)
    (hK_bound : C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
      C_E * Real.sqrt (2 * C_D) * Real.sqrt (z_down_s) +
      C_E * Real.sqrt (2 * C_D * δ_D) + C_E / L + δ_E ≤ K)
    (h_D_tau : pathDelta ≤ C_D * (1 / L * (s + z_up_s) + z_down_s) + C_D * δ_D) :
    C_E * (Real.sqrt (2 * pathDelta) + 1 / L * (1 + z_up') + z_down') + δ_E ≤
      K + (C_E / L) * z_up' + C_E * z_down' := by
  -- After expanding both sides, the terms (C_E/L)*z_up' + C_E*z_down' cancel,
  -- reducing the goal to: C_E * √(2·pathDelta) + C_E/L + δ_E ≤ K.
  -- From `hK_bound` we have K ≥ C_E * (√(2·C_D/L·(s+z_up_s)) + √(2·C_D)·√(z_down_s)
  --   + √(2·C_D·δ_D)) + C_E/L + δ_E.
  -- So it suffices to prove: √(2·pathDelta) ≤ √(2·C_D/L·(s+z_up_s))
  --   + √(2·C_D)·√(z_down_s) + √(2·C_D·δ_D).
  have h_key : Real.sqrt (2 * pathDelta) ≤
      Real.sqrt (2 * C_D / L * (s + z_up_s)) +
      Real.sqrt (2 * C_D) * Real.sqrt (z_down_s) +
      Real.sqrt (2 * C_D * δ_D) := by
    -- From h_D_tau, multiply by 2 and apply sqrt monotonicity
    have h_mul : 2 * pathDelta ≤ 2 * C_D * (1 / L * (s + z_up_s) + z_down_s) + 2 * C_D * δ_D := by
      nlinarith
    have h_rhs_simp : 2 * C_D * (1 / L * (s + z_up_s) + z_down_s) + 2 * C_D * δ_D =
        2 * C_D / L * (s + z_up_s) + 2 * C_D * z_down_s + 2 * C_D * δ_D := by
      ring
    rw [h_rhs_simp] at h_mul
    have h_sqrt_mul : Real.sqrt (2 * pathDelta) ≤
        Real.sqrt (2 * C_D / L * (s + z_up_s) + 2 * C_D * z_down_s + 2 * C_D * δ_D) :=
      Real.sqrt_le_sqrt h_mul
    -- Now we need the inequality √(A+B+C) ≤ √A + √B + √C
    set A := 2 * C_D / L * (s + z_up_s) with hA
    set B := 2 * C_D * z_down_s with hB
    set C := 2 * C_D * δ_D with hC
    have h_sqrt_add : Real.sqrt (A + B + C) ≤ Real.sqrt A + Real.sqrt B + Real.sqrt C := by
      have h_nonneg_lhs : 0 ≤ Real.sqrt (A + B + C) := Real.sqrt_nonneg _
      have h_nonneg_rhs : 0 ≤ Real.sqrt A + Real.sqrt B + Real.sqrt C := by positivity
      -- Square both sides: a ≤ b (for a,b ≥ 0) is equivalent to a² ≤ b²
      have h_sq_le : (Real.sqrt (A + B + C)) ^ 2 ≤
          (Real.sqrt A + Real.sqrt B + Real.sqrt C) ^ 2 := by
        -- Key identity: (√x)² = max 0 x for all real x
        have h_sq_sqrt_eq_max (x : ℝ) : (Real.sqrt x) ^ 2 = max 0 x := by
          by_cases hx : 0 ≤ x
          · rw [Real.sq_sqrt hx, max_eq_right hx]
          · rw [max_eq_left (by linarith)]
            have hsqrt0 : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
            simp [hsqrt0]
        -- Expand (√A + √B + √C)²
        have h_expand : (Real.sqrt A + Real.sqrt B + Real.sqrt C) ^ 2 =
            (Real.sqrt A) ^ 2 + (Real.sqrt B) ^ 2 + (Real.sqrt C) ^ 2 +
            2 * Real.sqrt A * Real.sqrt B + 2 * Real.sqrt A * Real.sqrt C +
            2 * Real.sqrt B * Real.sqrt C := by
          ring
        rw [h_expand, h_sq_sqrt_eq_max (A + B + C), h_sq_sqrt_eq_max A,
          h_sq_sqrt_eq_max B, h_sq_sqrt_eq_max C]
        -- Goal: max 0 (A+B+C) ≤ max 0 A + max 0 B + max 0 C + (nonnegative cross terms)
        have h_max : max 0 (A + B + C) ≤ max 0 A + max 0 B + max 0 C := by
          by_cases hsum : 0 ≤ A + B + C
          · rw [max_eq_right hsum]
            have hA' : A ≤ max 0 A := by
              by_cases hApos : 0 ≤ A
              · rw [max_eq_right hApos]
              · rw [max_eq_left (by linarith)]; linarith
            have hB' : B ≤ max 0 B := by
              by_cases hBpos : 0 ≤ B
              · rw [max_eq_right hBpos]
              · rw [max_eq_left (by linarith)]; linarith
            have hC' : C ≤ max 0 C := by
              by_cases hCpos : 0 ≤ C
              · rw [max_eq_right hCpos]
              · rw [max_eq_left (by linarith)]; linarith
            linarith
          · rw [max_eq_left (by linarith)]
            have h_nonneg_max : 0 ≤ max 0 A + max 0 B + max 0 C := by positivity
            exact h_nonneg_max
        have h_cross_nonneg : 0 ≤ 2 * Real.sqrt A * Real.sqrt B +
            2 * Real.sqrt A * Real.sqrt C + 2 * Real.sqrt B * Real.sqrt C := by
          positivity
        nlinarith
      -- From a² ≤ b² and a,b ≥ 0, deduce a ≤ b
      exact (sq_le_sq₀ h_nonneg_lhs h_nonneg_rhs).mp h_sq_le
    -- Rewrite √B as √(2·C_D)·√(z_down_s) using √(ab) = √a·√b (since 2·C_D ≥ 0)
    have h_sqrt_B : Real.sqrt B = Real.sqrt (2 * C_D) * Real.sqrt (z_down_s) := by
      rw [hB]
      have h_nonneg_2CD : 0 ≤ 2 * C_D := by nlinarith
      rw [Real.sqrt_mul h_nonneg_2CD (z_down_s)]
    rw [h_sqrt_B] at h_sqrt_add
    -- Now combine: √(2·pathDelta) ≤ √(A+B+C) ≤ √A + √(2·C_D)·√(z_down_s) + √C
    exact le_trans h_sqrt_mul h_sqrt_add
  -- Use h_key and hK_bound to close the goal
  have h_mul : C_E * Real.sqrt (2 * pathDelta) ≤
      C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
      C_E * Real.sqrt (2 * C_D) * Real.sqrt (z_down_s) +
      C_E * Real.sqrt (2 * C_D * δ_D) := by
    -- Multiply h_key by C_E > 0
    have h := mul_le_mul_of_nonneg_left h_key hC_E_pos.le
    -- h: C_E * √(2·pathDelta) ≤ C_E * (√(A) + √(2·C_D)·√(B) + √(C))
    -- Distribute C_E over the sum on the RHS
    have h_distrib : C_E * (Real.sqrt (2 * C_D / L * (s + z_up_s)) +
        Real.sqrt (2 * C_D) * Real.sqrt (z_down_s) +
        Real.sqrt (2 * C_D * δ_D)) =
        C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
        C_E * (Real.sqrt (2 * C_D) * Real.sqrt (z_down_s)) +
        C_E * Real.sqrt (2 * C_D * δ_D) := by ring
    rw [h_distrib] at h
    -- Re-associate the middle term to match hK_bound
    simpa [mul_assoc] using h
  have h_main : C_E * Real.sqrt (2 * pathDelta) + C_E / L + δ_E ≤ K := by
    -- Add C_E/L + δ_E to both sides of h_mul, then chain with hK_bound
    have h_sum : C_E * Real.sqrt (2 * pathDelta) + C_E / L + δ_E ≤
        (C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
         C_E * Real.sqrt (2 * C_D) * Real.sqrt (z_down_s) +
         C_E * Real.sqrt (2 * C_D * δ_D)) + C_E / L + δ_E := by
      linarith
    linarith
  -- Reduce the original goal (which involves z_up', z_down') to h_main
  -- by canceling the common (C_E/L)*z_up' + C_E*z_down' terms
  have h_diff_eq : (C_E * (Real.sqrt (2 * pathDelta) + 1 / L * (1 + z_up') + z_down') + δ_E) -
      (K + (C_E / L) * z_up' + C_E * z_down') =
      (C_E * Real.sqrt (2 * pathDelta) + C_E / L + δ_E) - K := by
    field_simp [hL_pos.ne']
    ring
  have h_nonpos : C_E * (Real.sqrt (2 * pathDelta) + 1 / L * (1 + z_up') + z_down') + δ_E -
      (K + (C_E / L) * z_up' + C_E * z_down') ≤ 0 := by
    rw [h_diff_eq]
    linarith
  linarith

/--
Helper lemma: bound on the derivative of F(τ) by G(τ).

We assume additional nonnegativity hypotheses (λ ≥ 0, E ≥ 0, C_D ≥ 0, L > 0,
z↑' ≥ 0, z↓' ≥ 0) and a lower bound on K that together make the product-rule
estimate go through.  These are available in the calling context
(`positive_energy_integrated_bound`), which has `hdata : ProblemData M r lambda`
(so `lambda_nonneg`, `psd`) and defines `K` via `positive_energy_G_bound`.

Informal proof: F'(τ) = φ'(τ)E(τ) + φ(τ)E'(τ) ≤ 0 + φ(τ)·[C_E·(√(2Δ) + …) + δ_E]
≤ C_E·√(2Δ) + C_E/L + C_E/L·z↑' + C_E·z↓' + δ_E ≤ K + C_E/L·z↑' + C_E·z↓' = G'(τ).
(Source: docs/Lasso.md, Section 4.6)
-/
private lemma positive_energy_deriv_bound
    {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {lambda : ℝ}
    (w zε z : ℝ → EuclideanSpace ℝ ι) (s C_E C_D L K δ_E δ_D : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_lambda_nonneg : 0 ≤ lambda)
    (hL_pos : 0 < L)
    (hC_D_nonneg : 0 ≤ C_D)
    (hE_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) s,
      0 ≤ inner ℝ (w t) (zε t - z t) + pathDelta M zε z t)
    (hK_bound : C_E * Real.sqrt (2 * C_D / L * (s + positiveZUpward x_lasso s)) +
      C_E * Real.sqrt (2 * C_D) * Real.sqrt (positiveZDownward x_lasso s) +
      C_E * Real.sqrt (2 * C_D * δ_D) + C_E / L + δ_E ≤ K)
    (h_z_up_nonneg : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s → 0 ≤ deriv (positiveZUpward x_lasso) t)
    (h_z_down_nonneg : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s → 0 ≤ deriv (positiveZDownward x_lasso) t)
    (hδ_E_nonneg : 0 ≤ δ_E)
    (_hδ_D_nonneg : 0 ≤ δ_D)
    (hE_diff_ae : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s →
      DifferentiableAt ℝ (fun τ => inner ℝ (w τ) (zε τ - z τ) + pathDelta M zε z τ) t)
    (h_E : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s →
      deriv (fun t => inner ℝ (w t) (zε t - z t) + pathDelta M zε z t) t ≤
        C_E * (Real.sqrt (2 * pathDelta M zε z t) +
          1 / L * (1 + deriv (positiveZUpward x_lasso) t) +
          deriv (positiveZDownward x_lasso) t) + δ_E)
    (h_D : ∀ t ∈ Set.Icc 0 s,
      pathDelta M zε z t ≤
        C_D * (1 / L * (s + positiveZUpward x_lasso s) + positiveZDownward x_lasso s) +
        C_D * δ_D)
    (hC_E_pos : 0 < C_E)
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (hs : 0 < s) :
    let E := fun (τ : ℝ) => inner ℝ (w τ) (zε τ - z τ) + pathDelta M zε z τ
    let φ := fun (τ : ℝ) => 1 / (1 + τ * lambda)
    let F := fun (τ : ℝ) => φ τ * E τ
    let G := fun (τ : ℝ) =>
      K * τ + C_E / L * positiveZUpward x_lasso τ + C_E * positiveZDownward x_lasso τ
    ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv F τ ≤ deriv G τ := by
  intro E φ F G
  have h_pos_z_diff := positiveZ_ae_differentiable x_lasso s hs h_local_affine h_regular
  filter_upwards [h_E, hE_diff_ae, h_pos_z_diff, h_z_up_nonneg, h_z_down_nonneg] with
    τ hE_bound hE_diff h_pos_z h_z_up_nn h_z_down_nn
  intro hτ_mem
  have hτ0 : 0 ≤ τ := hτ_mem.1
  have hτs : τ ≤ s := hτ_mem.2
  obtain ⟨hτ_up_diff, hτ_down_diff⟩ := h_pos_z hτ_mem
  set E' := deriv E τ
  set z_up' := deriv (positiveZUpward x_lasso) τ
  set z_down' := deriv (positiveZDownward x_lasso) τ
  -- 1. φ is differentiable at τ
  have h_denom_pos : 0 < 1 + τ * lambda := by nlinarith
  have h_denom_ne_zero : 1 + τ * lambda ≠ 0 := by nlinarith
  have hφ_diff : DifferentiableAt ℝ φ τ := by
    have h_denom_diff : DifferentiableAt ℝ (fun τ' => 1 + τ' * lambda) τ :=
      ((differentiableAt_const (1 : ℝ)).add (differentiableAt_id.mul_const lambda))
    exact (differentiableAt_const (1 : ℝ)).div h_denom_diff h_denom_ne_zero
  have hφ_hasDeriv : HasDerivAt φ (-lambda / ((1 + τ * lambda) ^ 2)) τ := by
    have h_denom_hasDeriv : HasDerivAt (fun τ' => 1 + τ' * lambda) lambda τ := by
      have h_id : HasDerivAt (fun τ' : ℝ => τ') (1 : ℝ) τ := hasDerivAt_id τ
      have h_add : HasDerivAt (fun τ' : ℝ => 1 + τ' * lambda) (0 + 1 * lambda) τ :=
        (hasDerivAt_const τ (1 : ℝ)).add (h_id.mul_const lambda)
      simpa [add_zero] using h_add
    have h_inv : HasDerivAt (fun τ' => (1 + τ' * lambda)⁻¹)
        (-lambda / ((1 + τ * lambda) ^ 2)) τ := by
      exact h_denom_hasDeriv.inv h_denom_ne_zero
    change HasDerivAt (fun τ' => 1 / (1 + τ' * lambda)) (-lambda / ((1 + τ * lambda) ^ 2)) τ
    simpa [one_div] using h_inv
  have hφ'_formula : deriv φ τ = -lambda / ((1 + τ * lambda) ^ 2) := hφ_hasDeriv.deriv
  -- 2. product rule: deriv F = φ'·E + φ·E'
  have h_deriv_F : deriv F τ = deriv φ τ * E τ + φ τ * E' := by
    change deriv (fun τ => φ τ * E τ) τ = deriv φ τ * E τ + φ τ * E'
    exact deriv_mul hφ_diff (hE_diff hτ_mem)
  -- 3. deriv G = K + (C_E/L)·z_up' + C_E·z_down'
  have h_deriv_G : deriv G τ = K + (C_E / L) * z_up' + C_E * z_down' := by
    have h_up_hasDeriv : HasDerivAt (positiveZUpward x_lasso) z_up' τ := hτ_up_diff.hasDerivAt
    have h_down_hasDeriv : HasDerivAt (positiveZDownward x_lasso) z_down' τ :=
      hτ_down_diff.hasDerivAt
    have hG_hasDeriv : HasDerivAt G (K + (C_E / L) * z_up' + C_E * z_down') τ := by
      have h1 : HasDerivAt (fun t => K * t) K τ := by
        simpa using (hasDerivAt_id τ).const_mul K
      have h2 : HasDerivAt (fun t => (C_E / L) * positiveZUpward x_lasso t)
          ((C_E / L) * z_up') τ := h_up_hasDeriv.const_mul (C_E / L)
      have h3 : HasDerivAt (fun t => C_E * positiveZDownward x_lasso t)
          (C_E * z_down') τ := h_down_hasDeriv.const_mul C_E
      exact (h1.add h2).add h3
    exact hG_hasDeriv.deriv
  rw [h_deriv_F, h_deriv_G]
  -- 4. nonnegativity and upper bounds
  have hφ'_nonpos : deriv φ τ ≤ 0 := by
    rw [hφ'_formula]
    have h_num_nonpos : -lambda ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos (by positivity)
  have hφ_nonneg : 0 ≤ φ τ := div_nonneg (by norm_num) (by nlinarith)
  have hφ_le_one : φ τ ≤ 1 := (div_le_one (by nlinarith)).mpr (by nlinarith)
  have h_term1 : deriv φ τ * E τ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hφ'_nonpos (hE_nonneg τ ⟨hτ0, hτs⟩)
  have h_z_up_s_nn : 0 ≤ positiveZUpward x_lasso s := by
    unfold positiveZUpward
    refine Finset.sum_nonneg (fun i _ => ?_)
    refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
    exact le_max_left 0 _
  have h_z_down_s_nn : 0 ≤ positiveZDownward x_lasso s := by
    unfold positiveZDownward
    refine Finset.sum_nonneg (fun i _ => ?_)
    refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
    have hu_nonneg : 0 ≤ u := hu.1
    exact mul_nonneg (by nlinarith) (le_max_left 0 _)
  have h_alg := positive_energy_deriv_bound_algebraic s C_E C_D L K δ_E δ_D
    z_up' z_down' (pathDelta M zε z τ) (positiveZUpward x_lasso s) (positiveZDownward x_lasso s)
    hL_pos hC_E_pos hC_D_nonneg (h_z_up_nn hτ_mem) (h_z_down_nn hτ_mem)
    h_z_up_s_nn h_z_down_s_nn hK_bound (h_D τ hτ_mem)
  have hφE'_bound : φ τ * E' ≤ C_E * (Real.sqrt (2 * pathDelta M zε z τ) +
      1 / L * (1 + z_up') + z_down') + δ_E := by
    have hE_bound_τ := hE_bound hτ_mem
    have h_mul := mul_le_mul_of_nonneg_left hE_bound_τ hφ_nonneg
    -- RHS is nonnegative because C_E>0, L>0, sqrt≥0, z_up'≥0, z_down'≥0, δ_E≥0.
    -- positivity cannot see through the custom `pathDelta` definition, so we prove this manually.
    have hRHS_nonneg : 0 ≤ C_E *
        (Real.sqrt (2 * pathDelta M zε z τ) + 1 / L * (1 + z_up') + z_down') + δ_E := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * pathDelta M zε z τ) := Real.sqrt_nonneg _
      have h_one_div_L_nonneg : 0 ≤ (1 : ℝ) / L :=
        div_nonneg (by norm_num) (by linarith [hL_pos])
      have h_zup_nonneg : 0 ≤ z_up' := h_z_up_nn hτ_mem
      have h_zdn_nonneg : 0 ≤ z_down' := h_z_down_nn hτ_mem
      have h_inner_nonneg : 0 ≤ Real.sqrt (2 * pathDelta M zε z τ) +
          (1 / L) * (1 + z_up') + z_down' := by
        have h1 : 0 ≤ 1 + z_up' := by nlinarith
        have h2 : 0 ≤ (1 / L) * (1 + z_up') := mul_nonneg h_one_div_L_nonneg h1
        nlinarith
      nlinarith
    -- Since 0 ≤ φ τ ≤ 1 and RHS ≥ 0, we have φ τ * RHS ≤ RHS
    have h_φ_mul_RHS : φ τ * (C_E *
          (Real.sqrt (2 * pathDelta M zε z τ) +
            1 / L * (1 + z_up') + z_down') + δ_E) ≤
        C_E * (Real.sqrt (2 * pathDelta M zε z τ) +
          1 / L * (1 + z_up') + z_down') + δ_E :=
      mul_le_of_le_one_left hRHS_nonneg hφ_le_one
    exact le_trans h_mul h_φ_mul_RHS
  -- combine
  have h_total : deriv φ τ * E τ + φ τ * E' ≤ K + (C_E / L) * z_up' + C_E * z_down' := by
    linarith [h_term1, hφE'_bound, h_alg]
  exact h_total

/--
Monotone-case analogue of `positive_energy_deriv_bound`: the same product-rule bound
`deriv F τ ≤ deriv G τ`, with `h_local_affine` replaced by coordinatewise monotonicity
`h_mono` of `z = scaledPrimalPath x_lasso`.

Informal proof: identical to `positive_energy_deriv_bound`'s proof (the product-rule algebra
for `φ`, `F`, `G`, and the `positive_energy_deriv_bound_algebraic` bound are all unaffected by
monotonicity), with the single change that the source of a.e. differentiability of
`positiveZUpward`/`positiveZDownward` is `positiveZ_ae_differentiable_of_monotone`
(`Bounds/Delta.lean`, via `h_mono`) instead of `positiveZ_ae_differentiable` (via
`h_local_affine`). Citation: `docs/Lasso.md`, Section 4.6, and Sec. 3.1/4.7 for the monotone
specialization.
-/
private lemma positive_energy_deriv_bound_of_monotone
    {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {lambda : ℝ}
    (w zε z : ℝ → EuclideanSpace ℝ ι) (s C_E C_D L K δ_E δ_D : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_lambda_nonneg : 0 ≤ lambda)
    (hL_pos : 0 < L)
    (hC_D_nonneg : 0 ≤ C_D)
    (hE_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) s,
      0 ≤ inner ℝ (w t) (zε t - z t) + pathDelta M zε z t)
    (hK_bound : C_E * Real.sqrt (2 * C_D / L * (s + positiveZUpward x_lasso s)) +
      C_E * Real.sqrt (2 * C_D) * Real.sqrt (positiveZDownward x_lasso s) +
      C_E * Real.sqrt (2 * C_D * δ_D) + C_E / L + δ_E ≤ K)
    (h_z_up_nonneg : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s → 0 ≤ deriv (positiveZUpward x_lasso) t)
    (h_z_down_nonneg : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s → 0 ≤ deriv (positiveZDownward x_lasso) t)
    (hδ_E_nonneg : 0 ≤ δ_E)
    (_hδ_D_nonneg : 0 ≤ δ_D)
    (hE_diff_ae : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s →
      DifferentiableAt ℝ (fun τ => inner ℝ (w τ) (zε τ - z τ) + pathDelta M zε z τ) t)
    (h_E : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 s →
      deriv (fun t => inner ℝ (w t) (zε t - z t) + pathDelta M zε z t) t ≤
        C_E * (Real.sqrt (2 * pathDelta M zε z t) +
          1 / L * (1 + deriv (positiveZUpward x_lasso) t) +
          deriv (positiveZDownward x_lasso) t) + δ_E)
    (h_D : ∀ t ∈ Set.Icc 0 s,
      pathDelta M zε z t ≤
        C_D * (1 / L * (s + positiveZUpward x_lasso s) + positiveZDownward x_lasso s) +
        C_D * δ_D)
    (hC_E_pos : 0 < C_E)
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (hs : 0 < s) :
    let E := fun (τ : ℝ) => inner ℝ (w τ) (zε τ - z τ) + pathDelta M zε z τ
    let φ := fun (τ : ℝ) => 1 / (1 + τ * lambda)
    let F := fun (τ : ℝ) => φ τ * E τ
    let G := fun (τ : ℝ) =>
      K * τ + C_E / L * positiveZUpward x_lasso τ + C_E * positiveZDownward x_lasso τ
    ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv F τ ≤ deriv G τ := by
  intro E φ F G
  have h_pos_z_diff := positiveZ_ae_differentiable_of_monotone x_lasso s hs h_mono h_regular
  filter_upwards [h_E, hE_diff_ae, h_pos_z_diff, h_z_up_nonneg, h_z_down_nonneg] with
    τ hE_bound hE_diff h_pos_z h_z_up_nn h_z_down_nn
  intro hτ_mem
  have hτ0 : 0 ≤ τ := hτ_mem.1
  have hτs : τ ≤ s := hτ_mem.2
  obtain ⟨hτ_up_diff, hτ_down_diff⟩ := h_pos_z hτ_mem
  set E' := deriv E τ
  set z_up' := deriv (positiveZUpward x_lasso) τ
  set z_down' := deriv (positiveZDownward x_lasso) τ
  -- 1. φ is differentiable at τ
  have h_denom_pos : 0 < 1 + τ * lambda := by nlinarith
  have h_denom_ne_zero : 1 + τ * lambda ≠ 0 := by nlinarith
  have hφ_diff : DifferentiableAt ℝ φ τ := by
    have h_denom_diff : DifferentiableAt ℝ (fun τ' => 1 + τ' * lambda) τ :=
      ((differentiableAt_const (1 : ℝ)).add (differentiableAt_id.mul_const lambda))
    exact (differentiableAt_const (1 : ℝ)).div h_denom_diff h_denom_ne_zero
  have hφ_hasDeriv : HasDerivAt φ (-lambda / ((1 + τ * lambda) ^ 2)) τ := by
    have h_denom_hasDeriv : HasDerivAt (fun τ' => 1 + τ' * lambda) lambda τ := by
      have h_id : HasDerivAt (fun τ' : ℝ => τ') (1 : ℝ) τ := hasDerivAt_id τ
      have h_add : HasDerivAt (fun τ' : ℝ => 1 + τ' * lambda) (0 + 1 * lambda) τ :=
        (hasDerivAt_const τ (1 : ℝ)).add (h_id.mul_const lambda)
      simpa [add_zero] using h_add
    have h_inv : HasDerivAt (fun τ' => (1 + τ' * lambda)⁻¹)
        (-lambda / ((1 + τ * lambda) ^ 2)) τ := by
      exact h_denom_hasDeriv.inv h_denom_ne_zero
    change HasDerivAt (fun τ' => 1 / (1 + τ' * lambda)) (-lambda / ((1 + τ * lambda) ^ 2)) τ
    simpa [one_div] using h_inv
  have hφ'_formula : deriv φ τ = -lambda / ((1 + τ * lambda) ^ 2) := hφ_hasDeriv.deriv
  -- 2. product rule: deriv F = φ'·E + φ·E'
  have h_deriv_F : deriv F τ = deriv φ τ * E τ + φ τ * E' := by
    change deriv (fun τ => φ τ * E τ) τ = deriv φ τ * E τ + φ τ * E'
    exact deriv_mul hφ_diff (hE_diff hτ_mem)
  -- 3. deriv G = K + (C_E/L)·z_up' + C_E·z_down'
  have h_deriv_G : deriv G τ = K + (C_E / L) * z_up' + C_E * z_down' := by
    have h_up_hasDeriv : HasDerivAt (positiveZUpward x_lasso) z_up' τ := hτ_up_diff.hasDerivAt
    have h_down_hasDeriv : HasDerivAt (positiveZDownward x_lasso) z_down' τ :=
      hτ_down_diff.hasDerivAt
    have hG_hasDeriv : HasDerivAt G (K + (C_E / L) * z_up' + C_E * z_down') τ := by
      have h1 : HasDerivAt (fun t => K * t) K τ := by
        simpa using (hasDerivAt_id τ).const_mul K
      have h2 : HasDerivAt (fun t => (C_E / L) * positiveZUpward x_lasso t)
          ((C_E / L) * z_up') τ := h_up_hasDeriv.const_mul (C_E / L)
      have h3 : HasDerivAt (fun t => C_E * positiveZDownward x_lasso t)
          (C_E * z_down') τ := h_down_hasDeriv.const_mul C_E
      exact (h1.add h2).add h3
    exact hG_hasDeriv.deriv
  rw [h_deriv_F, h_deriv_G]
  -- 4. nonnegativity and upper bounds
  have hφ'_nonpos : deriv φ τ ≤ 0 := by
    rw [hφ'_formula]
    have h_num_nonpos : -lambda ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos (by positivity)
  have hφ_nonneg : 0 ≤ φ τ := div_nonneg (by norm_num) (by nlinarith)
  have hφ_le_one : φ τ ≤ 1 := (div_le_one (by nlinarith)).mpr (by nlinarith)
  have h_term1 : deriv φ τ * E τ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hφ'_nonpos (hE_nonneg τ ⟨hτ0, hτs⟩)
  have h_z_up_s_nn : 0 ≤ positiveZUpward x_lasso s := by
    unfold positiveZUpward
    refine Finset.sum_nonneg (fun i _ => ?_)
    refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
    exact le_max_left 0 _
  have h_z_down_s_nn : 0 ≤ positiveZDownward x_lasso s := by
    unfold positiveZDownward
    refine Finset.sum_nonneg (fun i _ => ?_)
    refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
    have hu_nonneg : 0 ≤ u := hu.1
    exact mul_nonneg (by nlinarith) (le_max_left 0 _)
  have h_alg := positive_energy_deriv_bound_algebraic s C_E C_D L K δ_E δ_D
    z_up' z_down' (pathDelta M zε z τ) (positiveZUpward x_lasso s) (positiveZDownward x_lasso s)
    hL_pos hC_E_pos hC_D_nonneg (h_z_up_nn hτ_mem) (h_z_down_nn hτ_mem)
    h_z_up_s_nn h_z_down_s_nn hK_bound (h_D τ hτ_mem)
  have hφE'_bound : φ τ * E' ≤ C_E * (Real.sqrt (2 * pathDelta M zε z τ) +
      1 / L * (1 + z_up') + z_down') + δ_E := by
    have hE_bound_τ := hE_bound hτ_mem
    have h_mul := mul_le_mul_of_nonneg_left hE_bound_τ hφ_nonneg
    -- RHS is nonnegative because C_E>0, L>0, sqrt≥0, z_up'≥0, z_down'≥0, δ_E≥0.
    have hRHS_nonneg : 0 ≤ C_E *
        (Real.sqrt (2 * pathDelta M zε z τ) + 1 / L * (1 + z_up') + z_down') + δ_E := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * pathDelta M zε z τ) := Real.sqrt_nonneg _
      have h_one_div_L_nonneg : 0 ≤ (1 : ℝ) / L :=
        div_nonneg (by norm_num) (by linarith [hL_pos])
      have h_zup_nonneg : 0 ≤ z_up' := h_z_up_nn hτ_mem
      have h_zdn_nonneg : 0 ≤ z_down' := h_z_down_nn hτ_mem
      have h_inner_nonneg : 0 ≤ Real.sqrt (2 * pathDelta M zε z τ) +
          (1 / L) * (1 + z_up') + z_down' := by
        have h1 : 0 ≤ 1 + z_up' := by nlinarith
        have h2 : 0 ≤ (1 / L) * (1 + z_up') := mul_nonneg h_one_div_L_nonneg h1
        nlinarith
      nlinarith
    -- Since 0 ≤ φ τ ≤ 1 and RHS ≥ 0, we have φ τ * RHS ≤ RHS
    have h_φ_mul_RHS : φ τ * (C_E *
          (Real.sqrt (2 * pathDelta M zε z τ) +
            1 / L * (1 + z_up') + z_down') + δ_E) ≤
        C_E * (Real.sqrt (2 * pathDelta M zε z τ) +
          1 / L * (1 + z_up') + z_down') + δ_E :=
      mul_le_of_le_one_left hRHS_nonneg hφ_le_one
    exact le_trans h_mul h_φ_mul_RHS
  -- combine
  have h_total : deriv φ τ * E τ + φ τ * E' ≤ K + (C_E / L) * z_up' + C_E * z_down' := by
    linarith [h_term1, hφE'_bound, h_alg]
  exact h_total

/--
Helper lemma: algebraic bound on the integrated energy function G(s).
Informal proof: Expands (1+sλ)G(s) and uses asymptotic bounds.
(Source: docs/Lasso.md, Section 4.6)
-/
-- Core inequality for the leading term in positive_energy_G_bound.
-- For z ≥ 0, C_E > 0, C_D > 0, λ ≥ 0, s > 0:
-- (1+sλ)·C_E·(s·√(2C_D)·√z + z) ≤ s²·C·suboptimalityGap(λ,s,z)
-- where C = max(C_E·√(2C_D), C_E).
private lemma leading_term_bound
    (s lambda C_E C_D z : ℝ)
    (hs : 0 < s) (h_lambda_nonneg : 0 ≤ lambda)
    (hz_nonneg : 0 ≤ z) :
    (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D) * Real.sqrt z +
    (1 + s * lambda) * C_E * z ≤
    s^2 * (max (C_E * Real.sqrt (2 * C_D)) C_E * suboptimalityGap lambda s z) := by
  set C := max (C_E * Real.sqrt (2 * C_D)) C_E
  have hC1 : C_E * Real.sqrt (2 * C_D) ≤ C := le_max_left _ _
  have hC2 : C_E ≤ C := le_max_right _ _
  -- core inequality without the (1+sλ) factor:
  -- C_E·(s·√(2C_D)·√z + z) ≤ C·(s·√z + z)
  -- which follows from C_E·√(2C_D) ≤ C (hC1) and C_E ≤ C (hC2)
  have h_core : C_E * (s * Real.sqrt (2 * C_D) * Real.sqrt z + z) ≤
      C * (s * Real.sqrt z + z) := by
    have h_termA : C_E * s * Real.sqrt (2 * C_D) * Real.sqrt z ≤ C * s * Real.sqrt z := by
      calc
        C_E * s * Real.sqrt (2 * C_D) * Real.sqrt z
        = (C_E * Real.sqrt (2 * C_D)) * (s * Real.sqrt z) := by ring
        _ ≤ C * (s * Real.sqrt z) :=
          mul_le_mul_of_nonneg_right hC1 (by positivity)
        _ = C * s * Real.sqrt z := by ring
    nlinarith [h_termA, hC2, hz_nonneg]
  -- rewrite both sides to factor (1+sλ), apply h_core, then rewrite RHS
  have h_lhs_eq : (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D) * Real.sqrt z +
      (1 + s * lambda) * C_E * z =
      (1 + s * lambda) * (C_E * (s * Real.sqrt (2 * C_D) * Real.sqrt z + z)) := by ring
  have h_rhs_eq : s^2 * (C * suboptimalityGap lambda s z) =
      (1 + s * lambda) * (C * (s * Real.sqrt z + z)) := by
    dsimp [suboptimalityGap]
    calc
      s^2 * (C * ((1 + lambda * s) * (Real.sqrt z / s + z / s ^ 2)))
          = C * (1 + lambda * s) * (s^2 * (Real.sqrt z / s + z / s ^ 2)) := by ring
      _ = C * (1 + lambda * s) * (s * Real.sqrt z + z) := by
        field_simp [hs.ne.symm]
      _ = (1 + s * lambda) * (C * (s * Real.sqrt z + z)) := by ring
  rw [h_lhs_eq, h_rhs_eq]
  exact mul_le_mul_of_nonneg_left h_core (by nlinarith)

-- Bounds the δ_D term using the formula for δ_D.
-- The key is that 2*C_D*δ_D is a perfect square, so √(2*C_D*δ_D) simplifies
-- and the remaining expression is an exact equality with s^2*δ/4.
private lemma delta_D_bound
    (s lambda C_E C_D δ δ_D : ℝ)
    (hs : 0 < s) (h_lambda_nonneg : 0 ≤ lambda)
    (hC_E_pos : 0 < C_E) (hC_D_pos : 0 < C_D)
    (hδ_nonneg : 0 ≤ δ)
    (hδ_D : δ_D = (s * δ / (4 * (1 + s * lambda) * C_E)) ^ 2 / (2 * C_D)) :
    (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D * δ_D) ≤ s^2 * δ / 4 := by
  -- From hδ_D, compute 2*C_D*δ_D as a perfect square
  have h_radicand_sq : 2 * C_D * δ_D = ((s * δ) / (4 * (1 + s * lambda) * C_E)) ^ 2 := by
    rw [hδ_D]; field_simp [hC_D_pos.ne.symm]
  rw [h_radicand_sq]
  -- Now we have Real.sqrt (A^2) where A = (s*δ)/(4*(1+s*λ)*C_E) ≥ 0
  rw [Real.sqrt_sq (by positivity : 0 ≤ (s * δ) / (4 * (1 + s * lambda) * C_E))]
  -- Goal: (1+s*λ)*s*C_E * (s*δ/(4*(1+s*λ)*C_E)) ≤ s^2*δ/4
  -- This is an equality, so we prove equality and note it implies ≤
  have h_eq : (1 + s * lambda) * s * C_E * ((s * δ) / (4 * (1 + s * lambda) * C_E)) =
      s^2 * δ / 4 := by
    field_simp [show 1 + s * lambda ≠ 0 by nlinarith, hC_E_pos.ne.symm]
  rw [h_eq]

private lemma positive_energy_G_bound
    {ι : Type*} [Fintype ι] (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (s lambda C_E C_D L K δ δ_E δ_D : ℝ) (h_lambda_nonneg : 0 ≤ lambda)
    (hs : 0 < s) (hC_E_pos : 0 < C_E) (hC_D_pos : 0 < C_D) (hδ_nonneg : 0 ≤ δ)
    (hK : K = C_E * Real.sqrt (2 * C_D / L * (s + positiveZUpward x_lasso s)) +
      C_E * Real.sqrt (2 * C_D) * Real.sqrt (positiveZDownward x_lasso s) +
      C_E * Real.sqrt (2 * C_D * δ_D) + C_E / L + δ_E)
    (hR : (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D / L * (s + positiveZUpward x_lasso s)) +
      (1 + s * lambda) * s * C_E / L +
      (1 + s * lambda) * C_E / L * positiveZUpward x_lasso s ≤ s ^ 2 * δ / 2)
    (hδ_E : δ_E = s * δ / (4 * (1 + s * lambda)))
    (hδ_D : δ_D = (s * δ / (4 * (1 + s * lambda) * C_E)) ^ 2 / (2 * C_D)) :
    let G := fun (τ : ℝ) =>
      K * τ + C_E / L * positiveZUpward x_lasso τ + C_E * positiveZDownward x_lasso τ
    (1 + s * lambda) * G s ≤ s ^ 2 * (max (C_E * Real.sqrt (2 * C_D)) C_E *
        suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ) := by
  change (1 + s * lambda) *
      (K * s + C_E / L * positiveZUpward x_lasso s + C_E * positiveZDownward x_lasso s) ≤ _
  have h_expand : (1 + s * lambda) *
      (K * s + C_E / L * positiveZUpward x_lasso s + C_E * positiveZDownward x_lasso s) =
      (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D / L * (s + positiveZUpward x_lasso s)) +
      (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D) * Real.sqrt (positiveZDownward x_lasso s) +
      (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D * δ_D) +
      (1 + s * lambda) * s * C_E / L +
      (1 + s * lambda) * s * δ_E +
      (1 + s * lambda) * C_E / L * positiveZUpward x_lasso s +
      (1 + s * lambda) * C_E * positiveZDownward x_lasso s := by
    rw [hK]
    ring
  rw [h_expand]
  -- z ≥ 0 because the integrand (1+u)·max(0,…) is nonnegative on [0,s]
  have hz_nonneg : 0 ≤ positiveZDownward x_lasso s := by
    unfold positiveZDownward
    exact Finset.sum_nonneg fun i _ =>
      intervalIntegral.integral_nonneg hs.le fun u hu =>
        mul_nonneg (by nlinarith [hu.1]) (le_max_left 0 _)
  have h_leading := leading_term_bound s lambda C_E C_D (positiveZDownward x_lasso s)
    hs h_lambda_nonneg hz_nonneg
  have h_delta_D := delta_D_bound s lambda C_E C_D δ δ_D
    hs h_lambda_nonneg hC_E_pos hC_D_pos hδ_nonneg hδ_D
  have h_delta_E : (1 + s * lambda) * s * δ_E ≤ s^2 * δ / 4 := by
    rw [hδ_E]
    have h_eq : (1 + s * lambda) * s * (s * δ / (4 * (1 + s * lambda))) = s^2 * δ / 4 := by
      field_simp [show 1 + s * lambda ≠ 0 by nlinarith]
    rw [h_eq]
  nlinarith [h_leading, h_delta_D, h_delta_E, hR]

/--
Helper lemma: integration of `positive_energy_differential_inequality`.
This uses the FTC and the boundary condition `initial_positive_energy_zero` to conclude
an upper bound on the energy $E^\varepsilon(s)$.

Informal proof reference: `docs/Lasso.md`, Section 4.6.

Strategy (Eq. (806)–(816) of `docs/Lasso.md`, formalized without assuming a specific relation
between `C_E` and `C_D`): write `F(τ) = (1/(1+τλ))·Eᵋ(τ)`. `positive_energy_differential_inequality`
gives `deriv F τ ≤ C_E·(√(2Δᵋ(τ)) + 1/L·(1 + z↑'(τ)) + z↓'(τ)) + δ_E` a.e. on `[0,s]`, with a
constant `C_E` uniform in `s` (`Bounds/Energy.lean`'s `energy_complementarity_bound`, redesigned
to hold a.e. rather than pointwise-everywhere — see that file's docstring for why the "kink"
case is discarded for free). `pathDelta_uniform_bound` gives `Δᵋ(τ) ≤ D` uniformly on `[0,s]`,
where `D = C_D·(1/L·(s+z↑(s)) + z↓(s)) + C_D·δ_D`. Bounding `√(2Δᵋ(τ)) ≤ √(2D)` and splitting
`√(2D)` via `sqrt_add_le_add_sqrt` isolates a term `C_E·√(2C_D)·√(z↓(s))` (matching
`suboptimalityGap`'s leading term) from an `ε`-vanishing remainder (→ 0 as `ε → 0` since
`1/log(1/ε) → 0`) and a `δ_E, δ_D`-controllable remainder. Choosing `C := max(C_E·√(2C_D), C_E)`
and `δ_E, δ_D` proportional to the target `δ`/4 absorbs the controllable remainder into `δ`;
the `ε`-vanishing remainder is handled by the `∀ᶠ ε in 𝓝[>] 0` filter.
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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      inner ℝ (w s) (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s) +
        pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
          (scaledPrimalPath x_lasso) s
      ≤ s^2 * (C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ) := by
  -- Step 1: get constants C_E and C_D from the two main lemmas
  obtain ⟨C_E, hC_E_pos, h_deriv_bound⟩ := positive_energy_differential_inequality M Mdagger r
    lambda β u hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_regular h_lipschitz
    h_local_affine
  obtain ⟨C_D, hC_D_pos, h_delta_bound⟩ := pathDelta_uniform_bound M r lambda β u hdata hβ hu
    x_lasso hx_lasso Mdagger w hdual hdual_selected h_local_affine h_regular h_lipschitz
  -- Step 2: define the final constant C = max(C_E·√(2·C_D), C_E)
  set C := max (C_E * Real.sqrt (2 * C_D)) C_E with hC_def
  have hC_pos : 0 < C := by
    refine lt_max_of_lt_left ?_
    positivity
  have hlambda_nonneg : 0 ≤ lambda := hdata.lambda_nonneg
  refine ⟨C, hC_pos, ?_⟩
  intro s hs δ hδ
  have hδ_nonneg : 0 ≤ δ := hδ.le
  -- Step 3: set the slack parameters δ_E, δ_D
  set δ_E := s * δ / (4 * (1 + s * lambda)) with hδ_E_def
  set δ_D := (s * δ / (4 * (1 + s * lambda) * C_E)) ^ 2 / (2 * C_D) with hδ_D_def
  have hδ_E_pos : 0 < δ_E := by
    rw [hδ_E_def]; positivity
  have hδ_D_pos : 0 < δ_D := by
    rw [hδ_D_def]; positivity
  -- Step 4: apply the two bounds with these δ values
  have hE_bound := h_deriv_bound s hs δ_E hδ_E_pos
  have hD_bound := h_delta_bound s hs δ_D hδ_D_pos
  -- Also get that ε ∈ (0,1) for log positivity
  have h_mem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩
  -- Step 5: ε-vanishing remainder → 0 as ε → 0⁺, so it's eventually < s²δ/2
  set z_up_s := positiveZUpward x_lasso s with hz_up_def
  set z_down_s := positiveZDownward x_lasso s with hz_down_def
  have h_tendsto_log_inv : Tendsto (fun (ε : ℝ) => (Real.log (1 / ε))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h_inv_atTop : Tendsto (fun (ε : ℝ) => 1 / ε) (𝓝[>] 0) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    exact (Real.tendsto_log_atTop.comp h_inv_atTop).inv_tendsto_atTop
  -- The remainder: (1+sλ)*s*C_E*√(2*C_D/L*(s+z↑)) + (1+sλ)*C_E/L*(s+z↑)
  -- We prove it → 0 as ε → 0⁺.  Each of the three summands is a constant times
  -- either (log(1/ε))⁻¹ or √((log(1/ε))⁻¹), both of which tend to 0.
  set remainder := fun (ε : ℝ) =>
    (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D / Real.log (1 / ε) * (s + z_up_s)) +
    (1 + s * lambda) * s * C_E / Real.log (1 / ε) +
    (1 + s * lambda) * C_E / Real.log (1 / ε) * z_up_s
    with hrem_def
  have h_tendsto_remainder : Tendsto remainder (𝓝[>] 0) (𝓝 0) := by
    -- Decompose into three terms, each → 0
    set T1 := fun (ε : ℝ) => (1 + s * lambda) * s * C_E *
      Real.sqrt (2 * C_D / Real.log (1 / ε) * (s + z_up_s)) with hT1_def
    set T2 := fun (ε : ℝ) => (1 + s * lambda) * s * C_E / Real.log (1 / ε) with hT2_def
    set T3 := fun (ε : ℝ) => (1 + s * lambda) * C_E / Real.log (1 / ε) * z_up_s with hT3_def
    have h_rem_eq : remainder = fun ε => T1 ε + T2 ε + T3 ε := by
      ext ε; dsimp [remainder, T1, T2, T3]
    -- T2 → 0 and T3 → 0: const * (log(1/ε))⁻¹
    have hT2 : Tendsto T2 (𝓝[>] 0) (𝓝 0) := by
      dsimp [T2]
      have h_eq : (fun ε => (1 + s * lambda) * s * C_E / Real.log (1 / ε)) =
          (fun ε => (1 + s * lambda) * s * C_E * (Real.log (1 / ε))⁻¹) := by
        ext ε; rw [div_eq_mul_inv]
      rw [h_eq]
      have h := h_tendsto_log_inv.const_mul ((1 + s * lambda) * s * C_E)
      have h_lim_eq : (1 + s * lambda) * s * C_E * 0 = 0 := by ring
      rw [h_lim_eq] at h
      exact h
    have hT3 : Tendsto T3 (𝓝[>] 0) (𝓝 0) := by
      dsimp [T3]
      have h_eq : (fun ε => (1 + s * lambda) * C_E / Real.log (1 / ε) * z_up_s) =
          (fun ε => ((1 + s * lambda) * C_E * z_up_s) * (Real.log (1 / ε))⁻¹) := by
        ext ε; rw [div_eq_mul_inv]; ring
      rw [h_eq]
      have h := h_tendsto_log_inv.const_mul ((1 + s * lambda) * C_E * z_up_s)
      have h_lim_eq : (1 + s * lambda) * C_E * z_up_s * 0 = 0 := by ring
      rw [h_lim_eq] at h
      exact h
    -- T1 → 0: const * sqrt(arg) where arg → 0
    have hT1_arg : Tendsto (fun (ε : ℝ) => 2 * C_D / Real.log (1 / ε) * (s + z_up_s))
        (𝓝[>] 0) (𝓝 0) := by
      have h_eq : (fun (ε : ℝ) => 2 * C_D / Real.log (1 / ε) * (s + z_up_s)) =
          (fun (ε : ℝ) => (2 * C_D * (s + z_up_s)) * (Real.log (1 / ε))⁻¹) := by
        ext ε; rw [div_eq_mul_inv]; ring
      rw [h_eq]
      have h := h_tendsto_log_inv.const_mul (2 * C_D * (s + z_up_s))
      have h_lim_eq : 2 * C_D * (s + z_up_s) * 0 = 0 := by ring
      rw [h_lim_eq] at h
      exact h
    have hT1_sqrt : Tendsto (fun (ε : ℝ) =>
        Real.sqrt (2 * C_D / Real.log (1 / ε) * (s + z_up_s))) (𝓝[>] 0) (𝓝 0) := by
      have h_sqzero : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
      have h_comp := Real.continuous_sqrt.continuousAt.tendsto.comp hT1_arg
      rw [h_sqzero] at h_comp
      exact h_comp
    have hT1 : Tendsto T1 (𝓝[>] 0) (𝓝 0) := by
      dsimp [T1]
      have h := hT1_sqrt.const_mul ((1 + s * lambda) * s * C_E)
      have h_lim_eq : (1 + s * lambda) * s * C_E * 0 = 0 := by ring
      rw [h_lim_eq] at h
      exact h
    -- Sum → 0
    rw [h_rem_eq]
    have h_sum := (hT1.add hT2).add hT3
    -- h_sum : Tendsto (T1+T2+T3) (𝓝[>] 0) (𝓝 (0+0+0))
    simpa using h_sum
  have h_target_pos : 0 < s ^ 2 * δ / 2 := by positivity
  have h_eventually_remainder : ∀ᶠ ε in 𝓝[>] 0, remainder ε ≤ s ^ 2 * δ / 2 := by
    have h_target_mem : Set.Ioo (-(s ^ 2 * δ / 2)) (s ^ 2 * δ / 2) ∈ 𝓝 (0 : ℝ) := by
      refine IsOpen.mem_nhds isOpen_Ioo ?_
      constructor <;> linarith
    refine ((h_tendsto_remainder.eventually h_target_mem).mono fun ε hε => ?_)
    rcases hε with ⟨_, hε_high⟩
    exact le_of_lt hε_high
  -- Step 6: intersect all filter conditions
  filter_upwards [hE_bound, hD_bound, h_mem, h_eventually_remainder] with ε hE hD hε_mem h_rem
  rcases hε_mem with ⟨hε_pos, hε_lt_one⟩
  -- Step 7: define L, F, D, G
  set L := Real.log (1 / ε) with hL_def
  have hL_pos : 0 < L := Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  have hL_ne : L ≠ 0 := by linarith
  have h_cont_diff : ContDiff ℝ 1 (u ε) := (hu ε hε_pos).cont_diff
  -- F(τ) = (1/(1+τλ)) * E(τ)
  set F := fun (τ : ℝ) => (1 / (1 + τ * lambda)) *
    (inner ℝ (w τ) (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ) +
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso) τ)
    with hF_def
  -- D = uniform upper bound for Δ(τ)
  set D := C_D * (1 / L * (s + z_up_s) + z_down_s) + C_D * δ_D with hD_def
  -- G(τ) = (C_E·√(2D) + C_E/L + δ_E)·τ + C_E/L·z↑(τ) + C_E·z↓(τ)
  set G := fun (τ : ℝ) => (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) * τ +
    C_E / L * positiveZUpward x_lasso τ + C_E * positiveZDownward x_lasso τ
    with hG_def
  -- Step 8: initial conditions
  have hF0 : F 0 = 0 := by
    rw [hF_def]
    have h0 := initial_positive_energy_zero M ε (u ε) x_lasso w
    simp [h0]
  have hG0 : G 0 = 0 := by
    rw [hG_def]
    have h_up0 : positiveZUpward x_lasso 0 = 0 := (z_upward_downward_zero x_lasso).1
    have h_down0 : positiveZDownward x_lasso 0 = 0 := (z_upward_downward_zero x_lasso).2
    simp [h_up0, h_down0]
  -- Step 9: absolute continuity of F and G on [0,s]
  have hF_ac : AbsolutelyContinuousOnInterval F 0 s :=
    positive_energy_F_ac (u ε) x_lasso w hdata hε_pos hs hL_ne h_regular
      hdual.absolutely_continuous h_cont_diff
  have hG_ac : AbsolutelyContinuousOnInterval G 0 s := by
    have h_id_ac : AbsolutelyContinuousOnInterval (fun τ : ℝ => τ) 0 s := by
      have hK_lip : LipschitzOnWith 1 (fun τ : ℝ => τ) (Set.uIcc 0 s) :=
        fun x _ y _ => by simp
      exact hK_lip.absolutelyContinuousOnInterval
    have h_up_ac : AbsolutelyContinuousOnInterval (positiveZUpward x_lasso) 0 s :=
      positiveZUpward_ac x_lasso s hs.le h_regular
    have h_down_ac : AbsolutelyContinuousOnInterval (positiveZDownward x_lasso) 0 s :=
      positiveZDownward_ac x_lasso s hs.le h_regular
    refine ((h_id_ac.const_mul (C_E * Real.sqrt (2 * D) + C_E / L + δ_E)).add
      (h_up_ac.const_mul (C_E / L))).add (h_down_ac.const_mul C_E)
  -- Step 10: a.e. derivative comparison
  have h_pos_z_diff := positiveZ_ae_differentiable x_lasso s hs h_local_affine h_regular
  -- Compute deriv G at points where z↑, z↓ are differentiable
  have hderiv_G_eq : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv G τ =
      C_E * Real.sqrt (2 * D) + C_E / L * (1 + deriv (positiveZUpward x_lasso) τ) +
      C_E * deriv (positiveZDownward x_lasso) τ + δ_E := by
    filter_upwards [h_pos_z_diff] with τ hτ_diff hτ_mem
    obtain ⟨hτ_up_diff, hτ_down_diff⟩ := hτ_diff hτ_mem
    have h_up_hasDeriv : HasDerivAt (positiveZUpward x_lasso)
        (deriv (positiveZUpward x_lasso) τ) τ := hτ_up_diff.hasDerivAt
    have h_down_hasDeriv : HasDerivAt (positiveZDownward x_lasso)
        (deriv (positiveZDownward x_lasso) τ) τ := hτ_down_diff.hasDerivAt
    have hG_hasDeriv : HasDerivAt G
        (C_E * Real.sqrt (2 * D) + C_E / L + δ_E +
         C_E / L * deriv (positiveZUpward x_lasso) τ +
         C_E * deriv (positiveZDownward x_lasso) τ) τ := by
      dsimp [G]
      have h1 : HasDerivAt (fun t => (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) * t)
          (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) τ := by
        simpa using (hasDerivAt_id τ).const_mul (C_E * Real.sqrt (2 * D) + C_E / L + δ_E)
      have h2 : HasDerivAt (fun t => (C_E / L) * positiveZUpward x_lasso t)
          ((C_E / L) * deriv (positiveZUpward x_lasso) τ) τ :=
        h_up_hasDeriv.const_mul (C_E / L)
      have h3 : HasDerivAt (fun t => C_E * positiveZDownward x_lasso t)
          (C_E * deriv (positiveZDownward x_lasso) τ) τ :=
        h_down_hasDeriv.const_mul C_E
      exact (h1.add h2).add h3
    rw [hG_hasDeriv.deriv]
    ring
  -- The a.e. deriv F ≤ deriv G
  have h_deriv_le : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv F τ ≤ deriv G τ := by
    filter_upwards [hE, hderiv_G_eq] with τ hτE_bound hτGeq
    intro hτ_mem
    rw [hτGeq hτ_mem]
    -- hτE_bound hτ_mem : deriv F τ ≤ C_E*(√(2Δ(τ)) + 1/L*(1+z↑'(τ)) + z↓'(τ)) + δ_E
    -- hD : ∀ τ ∈ Icc 0 s, Δ(τ) ≤ C_D*(1/L*(s+positiveZUpward) + positiveZDownward) + C_D*δ_D
    have hD_τ := hD τ hτ_mem
    have hD_τ' : pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ ≤ D :=
      hD_τ
    have h_sqrt_le : Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ) ≤ Real.sqrt (2 * D) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h_bound := hτE_bound hτ_mem
    -- Expand the RHS of h_bound
    have h_expand : C_E * (Real.sqrt (2 * pathDelta M
        (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso) τ) +
        1 / L * (1 + deriv (positiveZUpward x_lasso) τ) +
        deriv (positiveZDownward x_lasso) τ) + δ_E =
      C_E * Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ) +
      C_E / L * (1 + deriv (positiveZUpward x_lasso) τ) +
      C_E * deriv (positiveZDownward x_lasso) τ + δ_E := by ring
    rw [h_expand] at h_bound
    have h_bound_le : C_E * Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ) ≤ C_E * Real.sqrt (2 * D) :=
      mul_le_mul_of_nonneg_left h_sqrt_le hC_E_pos.le
    linarith
  -- Step 11: apply FTC
  have h_F_le_G : F s ≤ G s :=
    bound_of_deriv_bound hs.le h_deriv_le hF0 hG0 hF_ac hG_ac
  -- Step 12: from F(s) ≤ G(s) to E(s) ≤ (1+sλ)·G(s)
  have h_denom_pos : 0 < 1 + s * lambda := by nlinarith
  have h_denom_ne : 1 + s * lambda ≠ 0 := by nlinarith
  have h_Es_eq : inner ℝ (w s) (posIntegratedTrajectoryRescaled ε (u ε) s -
      scaledPrimalPath x_lasso s) +
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) s = (1 + s * lambda) * F s := by
    dsimp [F]
    field_simp
  rw [h_Es_eq]
  have h_Es_le : (1 + s * lambda) * F s ≤ (1 + s * lambda) * G s :=
    mul_le_mul_of_nonneg_left h_F_le_G h_denom_pos.le
  -- Step 13: bound (1+sλ)·G(s) using the algebraic lemma
  -- Define K as in positive_energy_G_bound
  set K := C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
    C_E * Real.sqrt (2 * C_D) * Real.sqrt z_down_s +
    C_E * Real.sqrt (2 * C_D * δ_D) + C_E / L + δ_E
    with hK_def
  -- Show that C_E*√(2D) + C_E/L + δ_E ≤ K, so G(τ) ≤ G_bound(τ) for τ ≥ 0
  have h_sqrt_D_le : Real.sqrt (2 * D) ≤
      Real.sqrt (2 * C_D / L * (s + z_up_s)) +
      Real.sqrt (2 * C_D) * Real.sqrt z_down_s +
      Real.sqrt (2 * C_D * δ_D) := by
    -- D = C_D*(1/L*(s+z↑) + z↓) + C_D*δ_D
    -- 2D = 2*C_D/L*(s+z↑) + 2*C_D*z↓ + 2*C_D*δ_D
    -- Use the three-term sqrt splitting
    have h_2D_eq : 2 * D = 2 * C_D / L * (s + z_up_s) + 2 * C_D * z_down_s + 2 * C_D * δ_D := by
      dsimp [D]; ring
    rw [h_2D_eq]
    set A := 2 * C_D / L * (s + z_up_s) with hA
    set B := 2 * C_D * z_down_s with hB
    set C_rem := 2 * C_D * δ_D with hC_rem
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      have hzup_nonneg : 0 ≤ z_up_s := by
        rw [hz_up_def]
        unfold positiveZUpward
        refine Finset.sum_nonneg (fun i _ => ?_)
        refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
        exact le_max_left 0 _
      positivity
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      have h_z_down_pos : 0 ≤ z_down_s := by
        rw [hz_down_def]
        unfold positiveZDownward
        refine Finset.sum_nonneg (fun i _ => ?_)
        refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
        have h1u : 0 ≤ u := hu.1
        exact mul_nonneg (by linarith) (le_max_left 0 _)
      positivity
    have hC_nonneg : 0 ≤ C_rem := by
      dsimp [C_rem]; positivity
    have hAB : Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B :=
      sqrt_add_le_add_sqrt hA_nonneg hB_nonneg
    have h_tot : Real.sqrt (A + B + C_rem) ≤ Real.sqrt (A + B) + Real.sqrt C_rem := by
      have hAB_nonneg : 0 ≤ A + B := by positivity
      exact sqrt_add_le_add_sqrt hAB_nonneg hC_nonneg
    have h_sqrt_B : Real.sqrt B = Real.sqrt (2 * C_D) * Real.sqrt z_down_s := by
      dsimp [B]
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2*C_D) z_down_s]
    calc Real.sqrt (A + B + C_rem)
      _ ≤ Real.sqrt (A + B) + Real.sqrt C_rem := h_tot
      _ ≤ Real.sqrt A + Real.sqrt B + Real.sqrt C_rem := by linarith [hAB]
      _ = Real.sqrt A + Real.sqrt (2 * C_D) * Real.sqrt z_down_s + Real.sqrt C_rem := by rw [h_sqrt_B]
  have h_coeff_le : C_E * Real.sqrt (2 * D) + C_E / L + δ_E ≤ K := by
    have h_mul : C_E * Real.sqrt (2 * D) ≤
        C_E * (Real.sqrt (2 * C_D / L * (s + z_up_s)) +
          Real.sqrt (2 * C_D) * Real.sqrt z_down_s +
          Real.sqrt (2 * C_D * δ_D)) :=
      mul_le_mul_of_nonneg_left h_sqrt_D_le hC_E_pos.le
    dsimp [K]
    linarith
  -- Define G_bound as in positive_energy_G_bound
  set G_bound := fun (τ : ℝ) => K * τ + C_E / L * positiveZUpward x_lasso τ +
    C_E * positiveZDownward x_lasso τ
    with hG_bound_def
  have h_G_le_G_bound : G s ≤ G_bound s := by
    dsimp [G, G_bound]
    have hs_nonneg : 0 ≤ s := hs.le
    have h1 : (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) * s ≤ K * s :=
      mul_le_mul_of_nonneg_right h_coeff_le hs_nonneg
    linarith
  -- The ε-vanishing remainder condition for positive_energy_G_bound
  have hR_bound : (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
      (1 + s * lambda) * s * C_E / L +
      (1 + s * lambda) * C_E / L * z_up_s ≤ s ^ 2 * δ / 2 := by
    -- h_rem: remainder ε ≤ s^2*δ/2, and remainder ε expands to exactly the LHS
    dsimp [remainder] at h_rem
    rw [← hL_def] at h_rem
    exact h_rem
  have hG_bound_le := positive_energy_G_bound x_lasso s lambda C_E C_D L K δ δ_E δ_D
    hlambda_nonneg hs hC_E_pos hC_D_pos hδ_nonneg hK_def hR_bound hδ_E_def hδ_D_def
  -- hG_bound_le: (1 + s * lambda) * G_bound s ≤ s^2*(C*suboptimalityGap + δ)
  -- Now chain the inequalities
  calc
    (1 + s * lambda) * F s ≤ (1 + s * lambda) * G s := h_Es_le
    _ ≤ (1 + s * lambda) * G_bound s :=
      mul_le_mul_of_nonneg_left h_G_le_G_bound h_denom_pos.le
    _ ≤ s ^ 2 * (C * suboptimalityGap lambda s z_down_s + δ) := by
      -- hG_bound_le uses z_down_s via positiveZDownward x_lasso s
      rw [hz_down_def, hC_def]
      exact hG_bound_le

/--
Monotone-case analogue of `positive_energy_integrated_bound`: the same integrated energy
bound, with `h_local_affine` replaced by coordinatewise monotonicity `h_mono` of
`z = scaledPrimalPath x_lasso`.

Informal proof: identical to `positive_energy_integrated_bound`'s proof (write `F(τ) =
(1/(1+τλ))·Eᵋ(τ)`, integrate the a.e. derivative bound via FTC, bound `Δᵋ` uniformly, split the
square root, and absorb the controllable remainder), with every ingredient sourced from the
monotone-case chain: `energy_complementarity_bound_of_monotone` (`Bounds/Energy.lean`) for the
derivative bound, `pathDelta_uniform_bound_of_monotone` for the uniform `Δᵋ` bound, and
`positive_energy_deriv_bound_of_monotone`/`positive_energy_G_bound` for the algebraic
assembly (`positive_energy_G_bound` itself needs no `h_local_affine`/`h_mono`, so it is reused
unchanged). Citation: `docs/Lasso.md`, Section 4.6, Eq. (806)–(816), and Sec. 3.1/4.7 for the
monotone specialization.
-/
lemma positive_energy_integrated_bound_of_monotone
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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      inner ℝ (w s) (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s) +
        pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
          (scaledPrimalPath x_lasso) s
      ≤ s^2 * (C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ) := by
  -- Step 1: get constants C_E and C_D from the two main lemmas
  obtain ⟨C_E, hC_E_pos, h_deriv_bound⟩ := positive_energy_differential_inequality_of_monotone M Mdagger r
    lambda β u hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_regular h_lipschitz
    h_mono
  obtain ⟨C_D, hC_D_pos, h_delta_bound⟩ := pathDelta_uniform_bound_of_monotone M r lambda β u hdata hβ hu
    x_lasso hx_lasso Mdagger w hdual hdual_selected h_mono h_regular h_lipschitz
  -- Step 2: define the final constant C = max(C_E·√(2·C_D), C_E)
  set C := max (C_E * Real.sqrt (2 * C_D)) C_E with hC_def
  have hC_pos : 0 < C := by
    refine lt_max_of_lt_left ?_
    positivity
  have hlambda_nonneg : 0 ≤ lambda := hdata.lambda_nonneg
  refine ⟨C, hC_pos, ?_⟩
  intro s hs δ hδ
  have hδ_nonneg : 0 ≤ δ := hδ.le
  -- Step 3: set the slack parameters δ_E, δ_D
  set δ_E := s * δ / (4 * (1 + s * lambda)) with hδ_E_def
  set δ_D := (s * δ / (4 * (1 + s * lambda) * C_E)) ^ 2 / (2 * C_D) with hδ_D_def
  have hδ_E_pos : 0 < δ_E := by
    rw [hδ_E_def]; positivity
  have hδ_D_pos : 0 < δ_D := by
    rw [hδ_D_def]; positivity
  -- Step 4: apply the two bounds with these δ values
  have hE_bound := h_deriv_bound s hs δ_E hδ_E_pos
  have hD_bound := h_delta_bound s hs δ_D hδ_D_pos
  -- Also get that ε ∈ (0,1) for log positivity
  have h_mem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩
  -- Step 5: ε-vanishing remainder → 0 as ε → 0⁺, so it's eventually < s²δ/2
  set z_up_s := positiveZUpward x_lasso s with hz_up_def
  set z_down_s := positiveZDownward x_lasso s with hz_down_def
  have h_tendsto_log_inv : Tendsto (fun (ε : ℝ) => (Real.log (1 / ε))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h_inv_atTop : Tendsto (fun (ε : ℝ) => 1 / ε) (𝓝[>] 0) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    exact (Real.tendsto_log_atTop.comp h_inv_atTop).inv_tendsto_atTop
  -- The remainder: (1+sλ)*s*C_E*√(2*C_D/L*(s+z↑)) + (1+sλ)*C_E/L*(s+z↑)
  -- We prove it → 0 as ε → 0⁺.  Each of the three summands is a constant times
  -- either (log(1/ε))⁻¹ or √((log(1/ε))⁻¹), both of which tend to 0.
  set remainder := fun (ε : ℝ) =>
    (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D / Real.log (1 / ε) * (s + z_up_s)) +
    (1 + s * lambda) * s * C_E / Real.log (1 / ε) +
    (1 + s * lambda) * C_E / Real.log (1 / ε) * z_up_s
    with hrem_def
  have h_tendsto_remainder : Tendsto remainder (𝓝[>] 0) (𝓝 0) := by
    -- Decompose into three terms, each → 0
    set T1 := fun (ε : ℝ) => (1 + s * lambda) * s * C_E *
      Real.sqrt (2 * C_D / Real.log (1 / ε) * (s + z_up_s)) with hT1_def
    set T2 := fun (ε : ℝ) => (1 + s * lambda) * s * C_E / Real.log (1 / ε) with hT2_def
    set T3 := fun (ε : ℝ) => (1 + s * lambda) * C_E / Real.log (1 / ε) * z_up_s with hT3_def
    have h_rem_eq : remainder = fun ε => T1 ε + T2 ε + T3 ε := by
      ext ε; dsimp [remainder, T1, T2, T3]
    -- T2 → 0 and T3 → 0: const * (log(1/ε))⁻¹

    have hT2 : Tendsto T2 (𝓝[>] 0) (𝓝 0) := by
      dsimp [T2]
      have h_eq : (fun ε => (1 + s * lambda) * s * C_E / Real.log (1 / ε)) =
          (fun ε => (1 + s * lambda) * s * C_E * (Real.log (1 / ε))⁻¹) := by
        ext ε; rw [div_eq_mul_inv]
      rw [h_eq]
      have h := h_tendsto_log_inv.const_mul ((1 + s * lambda) * s * C_E)
      simp only [mul_zero] at h
      exact h
    have hT3 : Tendsto T3 (𝓝[>] 0) (𝓝 0) := by
      dsimp [T3]
      have h_eq : (fun ε => (1 + s * lambda) * C_E / Real.log (1 / ε) * z_up_s) =
          (fun ε => ((1 + s * lambda) * C_E * z_up_s) * (Real.log (1 / ε))⁻¹) := by
        ext ε; rw [div_eq_mul_inv]; ring
      rw [h_eq]
      have h := h_tendsto_log_inv.const_mul ((1 + s * lambda) * C_E * z_up_s)
      simp only [mul_zero] at h
      exact h
    -- T1 → 0: const * sqrt(arg) where arg → 0
    have hT1_arg : Tendsto (fun (ε : ℝ) => 2 * C_D / Real.log (1 / ε) * (s + z_up_s))
        (𝓝[>] 0) (𝓝 0) := by
      have h_eq : (fun (ε : ℝ) => 2 * C_D / Real.log (1 / ε) * (s + z_up_s)) =
          (fun (ε : ℝ) => (2 * C_D * (s + z_up_s)) * (Real.log (1 / ε))⁻¹) := by
        ext ε; rw [div_eq_mul_inv]; ring
      rw [h_eq]
      have h := h_tendsto_log_inv.const_mul (2 * C_D * (s + z_up_s))
      simp only [mul_zero] at h
      exact h
    have hT1_sqrt : Tendsto (fun (ε : ℝ) =>
        Real.sqrt (2 * C_D / Real.log (1 / ε) * (s + z_up_s))) (𝓝[>] 0) (𝓝 0) := by
      have h_sqzero : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
      have h_comp := Real.continuous_sqrt.continuousAt.tendsto.comp hT1_arg
      rw [h_sqzero] at h_comp
      exact h_comp
    have hT1 : Tendsto T1 (𝓝[>] 0) (𝓝 0) := by
      dsimp [T1]
      have h := Tendsto.const_mul ((1 + s * lambda) * s * C_E) hT1_sqrt
      simp only [mul_zero] at h
      exact h
    -- Sum → 0
    rw [h_rem_eq]
    have h_sum := (hT1.add hT2).add hT3
    simpa using h_sum
  have h_target_pos : 0 < s ^ 2 * δ / 2 := by positivity
  have h_eventually_remainder : ∀ᶠ ε in 𝓝[>] 0, remainder ε ≤ s ^ 2 * δ / 2 := by
    have h_target_mem : Set.Ioo (-(s ^ 2 * δ / 2)) (s ^ 2 * δ / 2) ∈ 𝓝 (0 : ℝ) := by
      refine IsOpen.mem_nhds isOpen_Ioo ?_
      constructor <;> linarith
    refine ((h_tendsto_remainder.eventually h_target_mem).mono fun ε hε => ?_)
    rcases hε with ⟨_, hε_high⟩
    exact le_of_lt hε_high
  -- Step 6: intersect all filter conditions
  filter_upwards [hE_bound, hD_bound, h_mem, h_eventually_remainder] with ε hE hD hε_mem h_rem
  rcases hε_mem with ⟨hε_pos, hε_lt_one⟩
  -- Step 7: define L, F, D, G
  set L := Real.log (1 / ε) with hL_def
  have hL_pos : 0 < L := Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  have hL_ne : L ≠ 0 := by linarith
  have h_cont_diff : ContDiff ℝ 1 (u ε) := (hu ε hε_pos).cont_diff
  -- F(τ) = (1/(1+τλ)) * E(τ)
  -- F(τ) = (1/(1+τλ)) * E(τ)
  set F := fun (τ : ℝ) => (1 / (1 + τ * lambda)) *
    (inner ℝ (w τ) (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ) +
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso) τ)
    with hF_def
  -- G majorizes F
  set D := C_D * (1 / L * (s + z_up_s) + z_down_s) + C_D * δ_D with hD_def
  set G := fun (τ : ℝ) => (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) * τ +
    (C_E / L) * positiveZUpward x_lasso τ + C_E * positiveZDownward x_lasso τ
    with hG_def
  -- Step 8: initial conditions
  have hF0 : F 0 = 0 := by
    rw [hF_def]
    have h0 := initial_positive_energy_zero M ε (u ε) x_lasso w
    simp [h0]
  have hG0 : G 0 = 0 := by
    rw [hG_def]
    have h_up0 : positiveZUpward x_lasso 0 = 0 := (z_upward_downward_zero x_lasso).1
    have h_down0 : positiveZDownward x_lasso 0 = 0 := (z_upward_downward_zero x_lasso).2
    simp [h_up0, h_down0]
  -- Step 9: absolute continuity of F and G on [0,s]
  have hF_ac : AbsolutelyContinuousOnInterval F 0 s :=
    positive_energy_F_ac (u ε) x_lasso w hdata hε_pos hs hL_ne h_regular
      hdual.absolutely_continuous h_cont_diff
  have hG_ac : AbsolutelyContinuousOnInterval G 0 s := by
    have h_id_ac : AbsolutelyContinuousOnInterval (fun τ : ℝ => τ) 0 s := by
      have hK_lip : LipschitzOnWith 1 (fun τ : ℝ => τ) (Set.uIcc 0 s) :=
        fun x _ y _ => by simp
      exact hK_lip.absolutelyContinuousOnInterval
    have h_up_ac : AbsolutelyContinuousOnInterval (positiveZUpward x_lasso) 0 s :=
      positiveZUpward_ac x_lasso s hs.le h_regular
    have h_down_ac : AbsolutelyContinuousOnInterval (positiveZDownward x_lasso) 0 s :=
      positiveZDownward_ac x_lasso s hs.le h_regular
    refine ((h_id_ac.const_mul (C_E * Real.sqrt (2 * D) + C_E / L + δ_E)).add
      (h_up_ac.const_mul (C_E / L))).add (h_down_ac.const_mul C_E)
  -- Step 10: a.e. derivative comparison
  have h_pos_z_diff := positiveZ_ae_differentiable_of_monotone x_lasso s hs h_mono h_regular
  -- Compute deriv G at points where z↑, z↓ are differentiable
  have hderiv_G_eq : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv G τ =
      C_E * Real.sqrt (2 * D) + C_E / L * (1 + deriv (positiveZUpward x_lasso) τ) +
      C_E * deriv (positiveZDownward x_lasso) τ + δ_E := by
    filter_upwards [h_pos_z_diff] with τ hτ_diff hτ_mem
    obtain ⟨hτ_up_diff, hτ_down_diff⟩ := hτ_diff hτ_mem
    have h_up_hasDeriv : HasDerivAt (positiveZUpward x_lasso)
        (deriv (positiveZUpward x_lasso) τ) τ := hτ_up_diff.hasDerivAt
    have h_down_hasDeriv : HasDerivAt (positiveZDownward x_lasso)
        (deriv (positiveZDownward x_lasso) τ) τ := hτ_down_diff.hasDerivAt
    have hG_hasDeriv : HasDerivAt G
        (C_E * Real.sqrt (2 * D) + C_E / L + δ_E +
         C_E / L * deriv (positiveZUpward x_lasso) τ +
         C_E * deriv (positiveZDownward x_lasso) τ) τ := by
      dsimp [G]
      have h1 : HasDerivAt (fun t => (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) * t)
          (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) τ := by
        simpa using (hasDerivAt_id τ).const_mul (C_E * Real.sqrt (2 * D) + C_E / L + δ_E)
      have h2 : HasDerivAt (fun t => (C_E / L) * positiveZUpward x_lasso t)
          ((C_E / L) * deriv (positiveZUpward x_lasso) τ) τ :=
        h_up_hasDeriv.const_mul (C_E / L)
      have h3 : HasDerivAt (fun t => C_E * positiveZDownward x_lasso t)
          (C_E * deriv (positiveZDownward x_lasso) τ) τ :=
        h_down_hasDeriv.const_mul C_E
      exact (h1.add h2).add h3
    rw [hG_hasDeriv.deriv]
    ring
  -- The a.e. deriv F ≤ deriv G
  have h_deriv_le : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv F τ ≤ deriv G τ := by
    filter_upwards [hE, hderiv_G_eq] with τ hτE_bound hτGeq
    intro hτ_mem
    rw [hτGeq hτ_mem]
    -- hτE_bound hτ_mem : deriv F τ ≤ C_E*(√(2Δ(τ)) + 1/L*(1+z↑'(τ)) + z↓'(τ)) + δ_E
    -- hD : ∀ τ ∈ Icc 0 s, Δ(τ) ≤ C_D*(1/L*(s+positiveZUpward) + positiveZDownward) + C_D*δ_D
    have hD_τ := hD τ hτ_mem
    have hD_τ' : pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ ≤ D :=
      hD_τ
    have h_sqrt_le : Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ) ≤ Real.sqrt (2 * D) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h_bound := hτE_bound hτ_mem
    -- Expand the RHS of h_bound
    have h_expand : C_E * (Real.sqrt (2 * pathDelta M
        (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso) τ) +
        1 / L * (1 + deriv (positiveZUpward x_lasso) τ) +
        deriv (positiveZDownward x_lasso) τ) + δ_E =
      C_E * Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ) +
      C_E / L * (1 + deriv (positiveZUpward x_lasso) τ) +
      C_E * deriv (positiveZDownward x_lasso) τ + δ_E := by ring
    rw [h_expand] at h_bound
    have h_bound_le : C_E * Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) τ) ≤ C_E * Real.sqrt (2 * D) :=
      mul_le_mul_of_nonneg_left h_sqrt_le hC_E_pos.le
    linarith
  -- Step 11: apply FTC
  have h_F_le_G : F s ≤ G s :=
    bound_of_deriv_bound hs.le h_deriv_le hF0 hG0 hF_ac hG_ac
  -- Step 12: from F(s) ≤ G(s) to E(s) ≤ (1+sλ)·G(s)
  have h_denom_pos : 0 < 1 + s * lambda := by nlinarith
  have h_denom_ne : 1 + s * lambda ≠ 0 := by nlinarith
  have h_Es_eq : inner ℝ (w s) (posIntegratedTrajectoryRescaled ε (u ε) s -
      scaledPrimalPath x_lasso s) +
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
        (scaledPrimalPath x_lasso) s = (1 + s * lambda) * F s := by
    dsimp [F]
    field_simp
  rw [h_Es_eq]
  have h_Es_le : (1 + s * lambda) * F s ≤ (1 + s * lambda) * G s :=
    mul_le_mul_of_nonneg_left h_F_le_G h_denom_pos.le
  -- Step 13: bound (1+sλ)·G(s) using the algebraic lemma
  -- Define K as in positive_energy_G_bound
  set K := C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
    C_E * Real.sqrt (2 * C_D) * Real.sqrt z_down_s +
    C_E * Real.sqrt (2 * C_D * δ_D) + C_E / L + δ_E
    with hK_def
  -- Show that C_E*√(2D) + C_E/L + δ_E ≤ K, so G(τ) ≤ G_bound(τ) for τ ≥ 0
  have h_sqrt_D_le : Real.sqrt (2 * D) ≤
      Real.sqrt (2 * C_D / L * (s + z_up_s)) +
      Real.sqrt (2 * C_D) * Real.sqrt z_down_s +
      Real.sqrt (2 * C_D * δ_D) := by
    -- D = C_D*(1/L*(s+z↑) + z↓) + C_D*δ_D
    -- 2D = 2*C_D/L*(s+z↑) + 2*C_D*z↓ + 2*C_D*δ_D
    -- Use the three-term sqrt splitting
    have h_2D_eq : 2 * D = 2 * C_D / L * (s + z_up_s) + 2 * C_D * z_down_s + 2 * C_D * δ_D := by
      dsimp [D]; ring
    rw [h_2D_eq]
    set A := 2 * C_D / L * (s + z_up_s) with hA
    set B := 2 * C_D * z_down_s with hB
    set C_rem := 2 * C_D * δ_D with hC_rem
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      have hzup_nonneg : 0 ≤ z_up_s := by
        rw [hz_up_def]
        unfold positiveZUpward
        refine Finset.sum_nonneg (fun i _ => ?_)
        refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
        exact le_max_left 0 _
      positivity
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      have h_z_down_pos : 0 ≤ z_down_s := by
        rw [hz_down_def]
        unfold positiveZDownward
        refine Finset.sum_nonneg (fun i _ => ?_)
        refine intervalIntegral.integral_nonneg hs.le (fun u hu => ?_)
        have h1u : 0 ≤ u := hu.1
        exact mul_nonneg (by linarith) (le_max_left 0 _)
      positivity
    have hC_nonneg : 0 ≤ C_rem := by
      dsimp [C_rem]; positivity
    have hAB : Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B :=
      sqrt_add_le_add_sqrt hA_nonneg hB_nonneg
    have h_tot : Real.sqrt (A + B + C_rem) ≤ Real.sqrt (A + B) + Real.sqrt C_rem := by
      have hAB_nonneg : 0 ≤ A + B := by positivity
      exact sqrt_add_le_add_sqrt hAB_nonneg hC_nonneg
    have h_sqrt_B : Real.sqrt B = Real.sqrt (2 * C_D) * Real.sqrt z_down_s := by
      dsimp [B]
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2*C_D) z_down_s]
    calc Real.sqrt (A + B + C_rem)
      _ ≤ Real.sqrt (A + B) + Real.sqrt C_rem := h_tot
      _ ≤ Real.sqrt A + Real.sqrt B + Real.sqrt C_rem := by linarith [hAB]
      _ = Real.sqrt A + Real.sqrt (2 * C_D) * Real.sqrt z_down_s + Real.sqrt C_rem := by rw [h_sqrt_B]
  have h_coeff_le : C_E * Real.sqrt (2 * D) + C_E / L + δ_E ≤ K := by
    have h_mul : C_E * Real.sqrt (2 * D) ≤
        C_E * (Real.sqrt (2 * C_D / L * (s + z_up_s)) +
          Real.sqrt (2 * C_D) * Real.sqrt z_down_s +
          Real.sqrt (2 * C_D * δ_D)) :=
      mul_le_mul_of_nonneg_left h_sqrt_D_le hC_E_pos.le
    dsimp [K]
    linarith
  -- Define G_bound as in positive_energy_G_bound
  set G_bound := fun (τ : ℝ) => K * τ + C_E / L * positiveZUpward x_lasso τ +
    C_E * positiveZDownward x_lasso τ
    with hG_bound_def
  have h_G_le_G_bound : G s ≤ G_bound s := by
    dsimp [G, G_bound]
    have hs_nonneg : 0 ≤ s := hs.le
    have h1 : (C_E * Real.sqrt (2 * D) + C_E / L + δ_E) * s ≤ K * s :=
      mul_le_mul_of_nonneg_right h_coeff_le hs_nonneg
    linarith
  -- The ε-vanishing remainder condition for positive_energy_G_bound
  have hR_bound : (1 + s * lambda) * s * C_E * Real.sqrt (2 * C_D / L * (s + z_up_s)) +
      (1 + s * lambda) * s * C_E / L +
      (1 + s * lambda) * C_E / L * z_up_s ≤ s ^ 2 * δ / 2 := by
    -- h_rem: remainder ε ≤ s^2*δ/2, and remainder ε expands to exactly the LHS
    dsimp [remainder] at h_rem
    rw [← hL_def] at h_rem
    exact h_rem
  have hG_bound_le := positive_energy_G_bound x_lasso s lambda C_E C_D L K δ δ_E δ_D
    hlambda_nonneg hs hC_E_pos hC_D_pos hδ_nonneg hK_def hR_bound hδ_E_def hδ_D_def
  -- hG_bound_le: (1 + s * lambda) * G_bound s ≤ s^2*(C*suboptimalityGap + δ)
  -- Now chain the inequalities
  calc
    (1 + s * lambda) * F s ≤ (1 + s * lambda) * G s := h_Es_le
    _ ≤ (1 + s * lambda) * G_bound s :=
      mul_le_mul_of_nonneg_left h_G_le_G_bound h_denom_pos.le
    _ ≤ s ^ 2 * (C * suboptimalityGap lambda s z_down_s + δ) := by
      -- hG_bound_le uses z_down_s via positiveZDownward x_lasso s
      rw [hz_down_def, hC_def]
      exact hG_bound_le

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
      LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso) :
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

  `h_lipschitz`/`h_local_affine` are regularity hypotheses on the *selected* minimizer path
  beyond mere absolute continuity, matching what `Bounds/Delta.lean`'s already-proved
  `positive_path_delta_bound` independently requires for the same path; see
  `docs/Lasso_formalization_report.md` for why this is a deliberate, documented departure from
  `docs/Lasso.md`'s literal (AC-only) hypothesis for Theorem 3.2.
  -/
  obtain ⟨C, hC_pos, h_energy_bound⟩ :=
    positive_energy_integrated_bound M Mdagger r lambda β u hdata hβ hu
      x_lasso hx_lasso w hdual hdual_selected h_regular h_lipschitz h_local_affine
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

/--
Monotone-case analogue of `positive_path_energy_bound`: the same positive-lasso suboptimality
bound, with `h_local_affine` replaced by coordinatewise monotonicity `h_mono` of
`z = scaledPrimalPath x_lasso`.

Informal proof: purely mechanical — identical to `positive_path_energy_bound`'s proof
verbatim (the algebraic identification of the objective gap with `s⁻² · Eᵋ(s)` via
`positiveLassoObjective_eq_energy`, `posLassoMin_eq_of_isPositiveLassoMinimizer`, etc. does not
touch `h_local_affine`/`h_mono` at all), with the single substitution of
`positive_energy_integrated_bound_of_monotone` for `positive_energy_integrated_bound` to obtain
`⟨C, hC_pos, h_energy_bound⟩`. Citation: `docs/Lasso.md`, Section 4.6 (concluding calculation
of Theorem 3.2), and Sec. 3.1/4.7 for the monotone specialization.
-/
theorem positive_path_energy_bound_of_monotone
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
      LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  obtain ⟨C, hC_pos, h_energy_bound⟩ :=
    positive_energy_integrated_bound_of_monotone M Mdagger r lambda β u hdata hβ hu
      x_lasso hx_lasso w hdual hdual_selected h_regular h_lipschitz h_mono
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

**Hypotheses beyond `docs/Lasso.md`:** the paper's Theorem 3.2 states only that
`μ ↦ x(μ)` is absolutely continuous on compact subsets of `(0, ∞)` (`h_regular` here). The two
additional hypotheses `h_lipschitz`/`h_local_affine` on the *selected* scaled path are a
deliberate, documented departure needed to make the differentiate-then-integrate argument of
Section 4.6 rigorous (the paper's own proof writes `d z_i(s)/ds` freely without addressing
differentiability); they match what this codebase's Delta-bound half
(`Bounds/Delta.lean`'s `positive_path_delta_bound`) already independently required. See
`docs/Lasso_formalization_report.md` for the full discussion.
-/
theorem pos_lasso_connection_approx
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso)
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso) :
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
    h_lipschitz h_local_affine

/-- Extends coordinatewise monotonicity of `μ ↦ μ x(μ)` from `(0,∞)` (as given by the
Theorem 3.1/3.2 hypothesis) to all of `[0,∞)`, using that the scaled path vanishes and is
coordinatewise nonnegative at `μ = 0`. Reused by both `monotone_positive_path_lipschitz` and
`pos_lasso_connection_monotone`. -/
private lemma scaledPrimalPath_mono_of_monotoneOn
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    ∀ μ ν, 0 ≤ μ → μ ≤ ν → ∀ i,
      (scaledPrimalPath x_lasso μ) i ≤ (scaledPrimalPath x_lasso ν) i := by
  have hx_nonneg : ∀ μ > 0, ∀ i, 0 ≤ x_lasso μ i := fun μ hμ i => (hx_lasso μ hμ).1 i
  have hz_coord : ∀ μ i, (scaledPrimalPath x_lasso μ) i = μ * x_lasso μ i := by
    intro μ i; simp [scaledPrimalPath, smul_eq_mul]
  have hz_nonneg : ∀ ν, 0 ≤ ν → ∀ i, 0 ≤ (scaledPrimalPath x_lasso ν) i := by
    intro ν hν i
    rcases eq_or_lt_of_le hν with rfl | hν_pos
    · simp [hz_coord]
    · rw [hz_coord]; exact mul_nonneg hν_pos.le (hx_nonneg ν hν_pos i)
  intro μ ν hμ hμν i
  rcases eq_or_lt_of_le hμ with rfl | hμ_pos
  · rw [hz_coord]; simpa using hz_nonneg ν hμν i
  · rw [hz_coord, hz_coord]
    exact h_monotone i (Set.mem_Ioi.mpr hμ_pos)
      (Set.mem_Ioi.mpr (lt_of_lt_of_le hμ_pos hμν)) hμν

/-- Lemma 4.12, strong form: under the monotonicity hypothesis of Theorem 3.1, the scaled
positive-Lasso path `z(μ) = μ x(μ)` is locally *Lipschitz* on `[0,∞)` — not merely absolutely
continuous. `monotone_positive_path_regular` below is the AC corollary; the stronger Lipschitz
fact is exposed separately because `pos_lasso_connection_monotone` needs it directly to invoke
`positive_path_energy_bound_of_monotone`. -/
theorem monotone_positive_path_lipschitz
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso) := by
  set z := scaledPrimalPath x_lasso with hz_def
  -- Lemma 4.11's dual certificate for the scaled path (already proved, this file).
  obtain ⟨Mdagger, w, hdual, hdual_selected⟩ :=
    exists_dual_certificate_for_positive_path M r lambda x_lasso hdata hx_lasso
  -- Reorder `hdual_selected`'s stationarity equation into the `isLCP`-with-swapped-sum shape
  -- required by `locallyLipschitzOnCompacts_of_matVec_lipschitz`.
  have h_lcp : ∀ μ, 0 ≤ μ → isLCP M (parametricLcpQ r lambda μ) (z μ)
      (matVec M (z μ) + parametricLcpQ r lambda μ) := by
    intro μ hμ
    obtain ⟨hweq, hwnn, hznn, hcomp⟩ := hdual_selected μ hμ
    have hv_eq : matVec M (z μ) + parametricLcpQ r lambda μ = w μ := by rw [hweq]; abel
    exact ⟨by abel, hv_eq ▸ hwnn, hznn, hv_eq ▸ hcomp⟩
  -- Monotonicity of `z`, extended from `(0,∞)` to `[0,∞)` via `z 0 = 0 ≤ z ν`.
  have h_mono : ∀ μ ν, 0 ≤ μ → μ ≤ ν → ∀ i, z μ i ≤ z ν i :=
    scaledPrimalPath_mono_of_monotoneOn M r lambda x_lasso hx_lasso h_monotone
  -- `matVec M z` and `matVec M z + q` are both locally Lipschitz on `[0, ∞)`, since they agree
  -- there with the (Lipschitz, by Lemma 4.11) dual path `w` up to the (affine, hence Lipschitz)
  -- term `parametricLcpQ r lambda`.
  have hMz_lip : LocallyLipschitzOnCompacts (fun μ => matVec M (z μ)) := by
    refine ⟨fun a b ha hab => ?_⟩
    obtain ⟨Kw, hKw, hw⟩ := hdual.locally_lipschitz.lipschitz_on_Icc a b ha hab
    obtain ⟨Kq, hKq, hq⟩ :=
      (parametricLcpQ_locallyLipschitzOnCompacts r lambda).lipschitz_on_Icc a b ha hab
    refine ⟨Kw + Kq, add_nonneg hKw hKq, fun μ hμ ν hν => ?_⟩
    have heqμ : matVec M (z μ) = w μ - parametricLcpQ r lambda μ := by
      rw [(hdual_selected μ (le_trans ha hμ.1)).1]; abel
    have heqν : matVec M (z ν) = w ν - parametricLcpQ r lambda ν := by
      rw [(hdual_selected ν (le_trans ha hν.1)).1]; abel
    rw [heqμ, heqν]
    calc ‖(w μ - parametricLcpQ r lambda μ) - (w ν - parametricLcpQ r lambda ν)‖
        = ‖(w μ - w ν) - (parametricLcpQ r lambda μ - parametricLcpQ r lambda ν)‖ := by abel_nf
      _ ≤ ‖w μ - w ν‖ + ‖parametricLcpQ r lambda μ - parametricLcpQ r lambda ν‖ := norm_sub_le _ _
      _ ≤ Kw * |μ - ν| + Kq * |μ - ν| := add_le_add (hw μ hμ ν hν) (hq μ hμ ν hν)
      _ = (Kw + Kq) * |μ - ν| := by ring
  have hw_lip : LocallyLipschitzOnCompacts
      (fun μ => matVec M (z μ) + parametricLcpQ r lambda μ) := by
    refine ⟨fun a b ha hab => ?_⟩
    obtain ⟨K, hK, hKbound⟩ := hdual.locally_lipschitz.lipschitz_on_Icc a b ha hab
    refine ⟨K, hK, fun μ hμ ν hν => ?_⟩
    have heqμ : matVec M (z μ) + parametricLcpQ r lambda μ = w μ := by
      rw [(hdual_selected μ (le_trans ha hμ.1)).1]; abel
    have heqν : matVec M (z ν) + parametricLcpQ r lambda ν = w ν := by
      rw [(hdual_selected ν (le_trans ha hν.1)).1]; abel
    rw [heqμ, heqν]
    exact hKbound μ hμ ν hν
  -- Lemma 4.12: complementarity + monotonicity pin down `z` as locally Lipschitz, no LCP
  -- solution-uniqueness needed (see `locallyLipschitzOnCompacts_of_matVec_lipschitz`).
  exact locallyLipschitzOnCompacts_of_matVec_lipschitz M r lambda z
    hdata.psd hdata.r_mem_span hdata.lambda_nonneg h_lcp hMz_lip hw_lip h_mono

theorem monotone_positive_path_regular
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) := by
  have h_lip := monotone_positive_path_lipschitz M r lambda x_lasso hdata hx_lasso h_monotone
  exact h_lip.absolutelyContinuous

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

  Status (verified 2026-08-01): `monotone_positive_path_regular` is proved (it in fact gives
  the *stronger* `LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)`, not just AC, via a
  direct transcription of Lemma 4.12's complementarity/projection argument — no LCP
  solution-uniqueness hypothesis is needed; see that theorem and
  `locallyLipschitzOnCompacts_of_matVec_lipschitz` in `Bounds/Delta.lean`).

  Route (b) below (Lebesgue's monotone differentiation theorem in place of
  `h_local_affine`) is now fully scoped as a parallel `_of_monotone` chain, matching route (b)
  precisely as sketched here previously, and is aligned with `docs/Lasso.md`: Theorem 3.1's
  *only* hypothesis beyond Theorem 3.2's absolute continuity is monotonicity (Sec. 3.1), so the
  paper never needs anything like piecewise-linearity — that hypothesis is a Lean-specific
  departure of Theorem 3.2's formalization (see `pos_lasso_connection_approx`'s docstring), and
  a monotone-specific route should not need it either. Concretely,
  `positiveZDownward_eq_zero_of_monotone` and `positiveZUpward_eq_sum_of_monotone`
  (`Bounds/Delta.lean`, **already fully proved**) give
  the closed forms `positiveZDownward x_lasso ≡ 0` and `positiveZUpward x_lasso μ = ∑ i, z_i μ`
  on `[0,∞)` directly from monotonicity + Lipschitz (Lebesgue's monotone differentiation
  theorem via `deriv_scaledPrimalPath_coord_nonneg_of_monotone`), which is everything the rest
  of the chain needs in place of `h_local_affine`. The chain has
  an informal proof pointing at the general-case original it mirrors):
  `deriv_pos_z_identities_of_monotone`, `pos_delta_bound_3_of_monotone`,
  `positiveZ_ae_differentiable_of_monotone`, `positive_delta_complementarity_bound_of_monotone`
  (`Bounds/Delta.lean`); `energy_complementarity_bound_of_monotone` (`Bounds/Energy.lean`);
  `pathDelta_uniform_bound_of_monotone`, `positive_energy_deriv_bound_of_monotone`,
  `positive_energy_integrated_bound_of_monotone`, `positive_path_energy_bound_of_monotone`
  (this file). Each differs from its general-case counterpart *only* in sourcing
  differentiability of `positiveZUpward`/`positiveZDownward` from `h_mono` via the closed forms
  instead of from `h_local_affine`; every other ingredient (Cauchy-Schwarz/Lemma 4.11 bounds,
  the uniform trajectory bound, the FTC/integration algebra) is untouched by monotonicity and
  reused verbatim from the general-case proofs.

  Given `positive_path_energy_bound_of_monotone`, the assembly here should mirror the *already
  proved* signed-case theorem `lasso_connection_monotone` (this file): squeeze via
  `tendsto_of_tendsto_of_tendsto_of_le_of_le'` between the constant `posLassoMin M r lambda s`
  (lower bound, via `posLassoMin_eq_of_isPositiveLassoMinimizer`/`ciInf_le`-style feasibility,
  as in that proof's first bullet) and `positive_path_energy_bound_of_monotone`'s upper bound
  specialized to `positiveZDownward x_lasso s = 0` — which, unlike the general case, is not an
  extra fact to prove: it is *exactly* `positiveZDownward_eq_zero_of_monotone`, already proved.
  -/
  have h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i,
      (scaledPrimalPath x_lasso ν) i ≤ (scaledPrimalPath x_lasso ν') i :=
    scaledPrimalPath_mono_of_monotoneOn M r lambda x_lasso hx_lasso h_monotone
  have h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso) :=
    monotone_positive_path_lipschitz M r lambda x_lasso hdata hx_lasso h_monotone
  have h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) :=
    h_lipschitz.absolutelyContinuous
  obtain ⟨Mdagger, w, hdual, hdual_selected⟩ :=
    exists_dual_certificate_for_positive_path M r lambda x_lasso hdata hx_lasso
  obtain ⟨C, hC_pos, h_bound⟩ :=
    positive_path_energy_bound_of_monotone M Mdagger r lambda β u hdata hβ hu x_lasso hx_lasso
      w hdual hdual_selected h_regular h_lipschitz h_mono
  -- Under monotonicity, `positiveZDownward` vanishes identically, so the error term in
  -- `positive_path_energy_bound_of_monotone`'s bound is exactly `δ` (no extra `C * gap` slack).
  have hzdown0 : positiveZDownward x_lasso s = 0 :=
    positiveZDownward_eq_zero_of_monotone x_lasso s hs.le h_regular h_mono
  have hgap0 : suboptimalityGap lambda s (positiveZDownward x_lasso s) = 0 := by
    rw [hzdown0]; simp [suboptimalityGap]
  have h_min_eq : posLassoMin M r lambda s = positiveLassoObjective M r lambda s (x_lasso s) :=
    posLassoMin_eq_of_isPositiveLassoMinimizer M r lambda s (x_lasso s) (hx_lasso s hs)
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  have hδ : 0 < ε' / 2 := by linarith
  filter_upwards [h_bound s hs (ε' / 2) hδ,
      show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
        rw [mem_nhdsGT_iff_exists_Ioo_subset]
        exact ⟨1, Set.mem_Ioi.mpr one_pos, fun _ hx => hx⟩] with ε hub hε_mem
  obtain ⟨hε_pos, hε_lt_one⟩ := hε_mem
  rw [hgap0, mul_zero, add_zero] at hub
  -- Lower bound: `posAverageTrajectory (u ε) (posTimeFromRescaled ε s)` is feasible
  -- (coordinatewise nonnegative), so `x_lasso s`'s minimality gives `posLassoMin ≤` its objective.
  have hlog_pos : 0 < Real.log (1 / ε) := Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  have ht_pos : 0 < posTimeFromRescaled ε s := by
    dsimp [posTimeFromRescaled]
    exact mul_pos (div_pos hs (by norm_num)) hlog_pos
  have hy_nonneg : Nonnegative (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)) := by
    intro j
    dsimp [posAverageTrajectory, euclideanOf]
    refine mul_nonneg (div_nonneg zero_le_one ht_pos.le) ?_
    exact intervalIntegral.integral_nonneg ht_pos.le
      (fun v _ => posEffectiveParameter_nonnegative (u ε) v j)
  have hlb : posLassoMin M r lambda s ≤
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)) := by
    rw [h_min_eq]
    exact isMinOn_iff.mp (hx_lasso s hs).2 _ hy_nonneg
  rw [Real.dist_eq, abs_of_nonneg (by linarith [hlb])]
  linarith [hub]

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
    simp only [signedToPositiveWeights, one_div, hadamard, euclideanOf, WithLp.equiv_symm_apply,
      PiLp.sub_apply, neg_add_rev, WithLp.equiv_apply, WithLp.ofLp_add, WithLp.ofLp_neg,
      WithLp.ofLp_smul, smul_add, smul_neg, PiLp.smul_apply, Sum.elim_inl, Pi.add_apply,
      Pi.neg_apply, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_sub, PiLp.neg_apply, Pi.sub_apply,
      augmentedVector_apply_inl]
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
    simp only [signedToPositiveWeights, one_div, hadamard, euclideanOf, WithLp.equiv_symm_apply,
      PiLp.sub_apply, neg_add_rev, WithLp.equiv_apply, WithLp.ofLp_add, WithLp.ofLp_neg,
      WithLp.ofLp_smul, smul_add, smul_neg, PiLp.smul_apply, Sum.elim_inr, Pi.smul_apply,
      Pi.sub_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_inv_cancel_left₀, WithLp.ofLp_sub, PiLp.neg_apply,
      augmentedVector_apply_inr, sub_neg_eq_add]
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
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso)
    (h_lipschitz : LocallyLipschitzOnCompacts
      (scaledPrimalPath (fun μ => signedCanonicalSplit (x_lasso μ))))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable
      (fun μ => signedCanonicalSplit (x_lasso μ))) :
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
      h_lipschitz h_local_affine
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
