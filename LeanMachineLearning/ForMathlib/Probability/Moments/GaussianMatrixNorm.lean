/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import LeanMachineLearning.ForMathlib.Analysis.Normed.UnitBallNet
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianExp
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianMatrix

/-!
# Tail of the operator norm of a Gaussian matrix

For a matrix `g : κ → ι → ℝ` with i.i.d. standard Gaussian entries, the `ℓ²` operator norm
`‖Matrix.of g‖` is at most of order `√|ι|` outside an event of probability `exp (-|ι|)`, as long as
`|κ| ≤ A |ι|` (Talagrand, *Spin Glasses*, Vol. I, Lemma A.9.1, here for rectangular matrices).

## Main declarations

* `ProbabilityTheory.measureReal_abs_bilinear_gaussian_ge_le`: tail of one bilinear form.
* `ProbabilityTheory.measureReal_l2_opNorm_gaussian_gt_le`: union bound over two nets.
* `ProbabilityTheory.exists_measureReal_l2_opNorm_gaussian_gt_le_exp`: Lemma A.9.1.
-/

@[expose] public section

open MeasureTheory Matrix Module
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace ProbabilityTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A bilinear form `y ⬝ᵥ (G x)` of a standard Gaussian matrix with `y ⬝ᵥ y ≤ 1` and
`x ⬝ᵥ x ≤ 1` exceeds `t` in absolute value with probability at most `2 exp (-t² / 2)`. -/
theorem measureReal_abs_bilinear_gaussian_ge_le {y : κ → ℝ} {x : ι → ℝ} (hy : y ⬝ᵥ y ≤ 1)
    (hx : x ⬝ᵥ x ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : κ => Measure.pi fun _ : ι => gaussianReal 0 1).real
        {g | t ≤ |y ⬝ᵥ (Matrix.of g *ᵥ x)|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  set P := Measure.pi fun _ : κ => Measure.pi fun _ : ι => gaussianReal 0 1 with hP
  set Z : (κ → ι → ℝ) → ℝ := fun g => y ⬝ᵥ (Matrix.of g *ᵥ x) with hZ
  have hZG : HasGaussianLaw Z P :=
    HasGaussianLaw.eval (X := fun (_ : Unit) (g : κ → ι → ℝ) => y ⬝ᵥ (Matrix.of g *ᵥ x))
      (hasGaussianLaw_bilinear_family (A := Unit) (fun _ => y) fun _ => x) ()
  have h0 : ∫ g, Z g ∂P = 0 := integral_linearForm_gaussianInit y x
  have h2 : ∫ g, Z g ^ 2 ∂P ≤ 1 := by
    have := integral_gaussianMatrix_bilinear_mul_bilinear y y x x
    simp only [← sq] at this
    refine this.trans_le ?_
    have hx0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact (mul_le_mul hy hx hx0 zero_le_one).trans_eq (one_mul 1)
  have hsub := hZG.hasSubgaussianMGF_of_integral_sq_le h0 h2
  have hup := hsub.measure_ge_le ht
  have hlo := hsub.neg.measure_ge_le ht
  simp only [Real.toNNReal_one, NNReal.coe_one, mul_one, Pi.neg_apply] at hup hlo
  have hsplit : {g | t ≤ |Z g|} ⊆ {g | t ≤ Z g} ∪ {g | t ≤ -Z g} := fun g (hg : t ≤ |Z g|) =>
    le_abs.1 hg
  calc P.real {g | t ≤ |Z g|} ≤ P.real ({g | t ≤ Z g} ∪ {g | t ≤ -Z g}) :=
        measureReal_mono hsplit (measure_ne_top P _)
    _ ≤ P.real {g | t ≤ Z g} + P.real {g | t ≤ -Z g} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-t ^ 2 / 2) := by linarith

/-- A vector of the Euclidean unit ball has `v ⬝ᵥ v ≤ 1`. -/
private theorem dotProduct_ofLp_self_le_one {n : Type*} [Fintype n] (v : EuclideanSpace ℝ n)
    (hv : ‖v‖ ≤ 1) : v.ofLp ⬝ᵥ v.ofLp ≤ 1 := by
  have h : v.ofLp ⬝ᵥ v.ofLp = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [h]
  exact pow_le_one₀ (norm_nonneg _) hv

variable [DecidableEq ι]

/-- **Union bound over two nets:** the operator norm of a standard Gaussian matrix exceeds `t`
with probability at most `2 · 5 ^ (|ι| + |κ|) · exp (-t² / 32)`. -/
theorem measureReal_l2_opNorm_gaussian_gt_le {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : κ => Measure.pi fun _ : ι => gaussianReal 0 1).real
        {g | t < ‖Matrix.of g‖} ≤
      2 * 5 ^ (Fintype.card ι + Fintype.card κ) * Real.exp (-t ^ 2 / 32) := by
  set P := Measure.pi fun _ : κ => Measure.pi fun _ : ι => gaussianReal 0 1 with hP
  obtain ⟨A, hA1, hAc, hAn⟩ := exists_finset_unitBall_net (EuclideanSpace ℝ ι)
  obtain ⟨B, hB1, hBc, hBn⟩ := exists_finset_unitBall_net (EuclideanSpace ℝ κ)
  rw [finrank_euclideanSpace] at hAc hBc
  have ht4 : 0 ≤ t / 4 := by positivity
  have hsub : {g : κ → ι → ℝ | t < ‖Matrix.of g‖} ⊆
      ⋃ p ∈ A ×ˢ B, {g | t / 4 ≤ |p.2.ofLp ⬝ᵥ (Matrix.of g *ᵥ p.1.ofLp)|} := fun g hg => by
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, not_exists, not_and, not_le,
      Finset.mem_product, and_imp, Prod.forall] at h
    refine (show t < ‖Matrix.of g‖ from hg).not_ge ?_
    rw [Matrix.l2_opNorm_def]
    refine le_trans (ContinuousLinearMap.opNorm_le_four_mul_of_net _ (A := A) (B := B) hAn hBn
      ht4 fun a ha b hb => ?_) (by linarith)
    have e : ⟪b, (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (Matrix.of g) a⟫ =
        b.ofLp ⬝ᵥ (Matrix.of g *ᵥ a.ofLp) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
      rfl
    rw [e]
    exact (h a b ha hb).le
  have hterm : ∀ p ∈ A ×ˢ B,
      P.real {g | t / 4 ≤ |p.2.ofLp ⬝ᵥ (Matrix.of g *ᵥ p.1.ofLp)|} ≤
        2 * Real.exp (-t ^ 2 / 32) := fun p hp => by
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hp
    have h := measureReal_abs_bilinear_gaussian_ge_le (dotProduct_ofLp_self_le_one p.2 (hB1 _ hb))
      (dotProduct_ofLp_self_le_one p.1 (hA1 _ ha)) ht4
    rwa [show -(t / 4) ^ 2 / 2 = -t ^ 2 / 32 by ring] at h
  calc P.real {g | t < ‖Matrix.of g‖}
      ≤ P.real (⋃ p ∈ A ×ˢ B, {g | t / 4 ≤ |p.2.ofLp ⬝ᵥ (Matrix.of g *ᵥ p.1.ofLp)|}) :=
        measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ p ∈ A ×ˢ B,
          P.real {g | t / 4 ≤ |p.2.ofLp ⬝ᵥ (Matrix.of g *ᵥ p.1.ofLp)|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ A ×ˢ B, 2 * Real.exp (-t ^ 2 / 32) := Finset.sum_le_sum hterm
    _ = (A.card * B.card : ℕ) * (2 * Real.exp (-t ^ 2 / 32)) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    _ ≤ (5 ^ (Fintype.card ι + Fintype.card κ) : ℕ) * (2 * Real.exp (-t ^ 2 / 32)) := by
        refine mul_le_mul_of_nonneg_right (Nat.cast_le.2 ?_) (by positivity)
        rw [pow_add]
        exact Nat.mul_le_mul hAc hBc
    _ = 2 * 5 ^ (Fintype.card ι + Fintype.card κ) * Real.exp (-t ^ 2 / 32) := by
        push_cast; ring

/-- **Lemma A.9.1 of Talagrand (Eq. (A.51)), rectangular form.** For every `a ≥ 0` there is
`L > 0`, depending only on `a`, such that a standard Gaussian matrix with `|κ| ≤ a |ι|` satisfies
`ℙ (L √|ι| < ‖G‖) ≤ L exp (-|ι|)`. -/
theorem exists_measureReal_l2_opNorm_gaussian_gt_le_exp (a : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ],
      (Fintype.card κ : ℝ) ≤ a * Fintype.card ι →
      (Measure.pi fun _ : κ => Measure.pi fun _ : ι => gaussianReal 0 1).real
          {g | L * Real.sqrt (Fintype.card ι) < ‖Matrix.of g‖} ≤
        L * Real.exp (-(Fintype.card ι : ℝ)) := by
  set c : ℝ := 32 * (1 + (1 + |a|) * Real.log 5) with hc
  have hlog : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hc0 : 0 ≤ c := by positivity
  refine ⟨max 2 (Real.sqrt c), lt_of_lt_of_le two_pos (le_max_left _ _),
    fun ι κ _ _ _ hκ => ?_⟩
  set L := max 2 (Real.sqrt c) with hL
  have hL0 : 0 ≤ L := le_trans zero_le_two (le_max_left _ _)
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hLc : c ≤ L ^ 2 :=
    (Real.sq_sqrt hc0).symm.le.trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2)
  refine (measureReal_l2_opNorm_gaussian_gt_le (mul_nonneg hL0 (Real.sqrt_nonneg _))).trans ?_
  have h5 : (5 : ℝ) ^ (Fintype.card ι + Fintype.card κ) ≤
      Real.exp ((1 + |a|) * n * Real.log 5) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm (Real.log 5)]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hlog)
    push_cast
    have := mul_le_mul_of_nonneg_right (le_abs_self a) hn0
    rw [← hn]
    linarith
  have hexp : Real.exp (-(L * Real.sqrt n) ^ 2 / 32) ≤
      Real.exp (-n - (1 + |a|) * n * Real.log 5) := by
    rw [Real.exp_le_exp, mul_pow, Real.sq_sqrt hn0]
    have := mul_le_mul_of_nonneg_right hLc hn0
    rw [hc] at this
    linarith
  calc 2 * 5 ^ (Fintype.card ι + Fintype.card κ) * Real.exp (-(L * Real.sqrt n) ^ 2 / 32)
      ≤ 2 * Real.exp ((1 + |a|) * n * Real.log 5) *
          Real.exp (-n - (1 + |a|) * n * Real.log 5) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h5 zero_le_two) hexp (Real.exp_pos _).le
          (by positivity)
    _ = 2 * Real.exp (-n) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ L * Real.exp (-n) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end ProbabilityTheory
