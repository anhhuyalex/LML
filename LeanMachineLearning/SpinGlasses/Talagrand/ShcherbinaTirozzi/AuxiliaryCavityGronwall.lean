/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExpMoment

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.GronwallBackward
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ReplicaExpMomentTail
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.AuxiliaryCavity
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.AuxiliaryCavityDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.AuxiliaryCavityTails

/-!
# The Shcherbina--Tirozzi model: Grönwall comparison along `ν_{t,v}`

This file formalizes Eq. (3.105) and Lemma 3.2.9 (Eq. (3.106)) of Talagrand, *Spin Glasses: A
Challenge for Mathematicians*, Vol. I, Section 3.2.

Along the auxiliary cavity path `ν_{t,v}` (`t, v ∈ [0, 1]`), for any measurable spin observable `f`
of polynomial growth whose second moment satisfies `ν_{t,s}(f²) ≤ A²` for all `s ∈ [0, 1]`:
* Eq. (3.105): `v ↦ ν_{t,v}(f)` is differentiable on `(0, 1)` with
  `|d/dv ν_{t,v}(f)| ≤ K (ν_{t,v}(|f|) + exp (-(N + 1)) A)`.
* Lemma 3.2.9 (Eq. (3.106)): if `f ≥ 0`, then
  `ν_{t,v}(f) ≤ K (ν_t(f) + exp (-(N + 1)) A)` for all `v ∈ [0, 1]`.

## Main declarations

* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le_add_exp`: Eq. (3.105).
* `SpinGlasses.exists_shcherbinaTirozziAuxCavity_le_add_exp`: Lemma 3.2.9 (Eq. (3.106)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- The disorder `((y, (g, g₀)), z)` of the auxiliary cavity system with `M + 1` constraints and
shared Gaussian `z`. -/
local notation "AuxDis[" N ", " M "]" =>
  (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ

/-- The law of `AuxDis` with `y ~ 𝒩(0, r)` and standard Gaussian `g, g₀, z`. -/
local notation "auxLaw[" N ", " M ", " r "]" =>
  Measure.prod
    (Measure.prod (gaussianReal 0 r)
      (Measure.prod
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    (gaussianReal 0 1)

/-- The cavity field `S_{k,t}` on `ℝ^(N+1)`. -/
local notation "cfield[" N ", " t ", " g ", " k ", " σ "]" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

/-- **Contraction of a vector by `√t` on the last coordinate** (`t ∈ [0, 1]`): its inner product
with another contracted vector is `∑_{i < N} x_i y_i + t x_N y_N`, and its squared norm is at most
`‖x‖²`. -/
private lemma truncated_inner_and_norm_sq_le {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let D : ℝ^(N + 1) → ℝ^(N + 1) := fun x =>
      WithLp.toLp 2 fun i => (if i = Fin.last N then Real.sqrt t else 1) * x i
    Measurable D ∧
      (∀ x y : ℝ^(N + 1), ⟪D x, D y⟫ =
        (∑ i : Fin N, x i.castSucc * y i.castSucc) + t * (x (Fin.last N) * y (Fin.last N))) ∧
      (∀ x : ℝ^(N + 1), ‖D x‖ ^ 2 ≤ ‖x‖ ^ 2) := by
  intro D
  have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
    fun i => (Fin.castSucc_lt_last i).ne
  have hDm : Measurable D := by
    have hc : Continuous D := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin (N + 1) => ℝ)).comp
        (continuous_pi fun i => continuous_const.mul
          (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i))
    exact hc.measurable
  have hinner : ∀ x y : ℝ^(N + 1), ⟪D x, D y⟫ =
      (∑ i : Fin N, x i.castSucc * y i.castSucc) + t * (x (Fin.last N) * y (Fin.last N)) := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_castSucc (n := N)]
    simp only [D, hcast, reduceIte, one_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · have ht : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
      linear_combination (x (Fin.last N) * y (Fin.last N)) * ht
  have hnorm : ∀ x : ℝ^(N + 1), ‖D x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    dsimp only [D]
    rw [mul_pow]
    refine mul_le_of_le_one_left (sq_nonneg _) ?_
    split
    · rw [Real.sq_sqrt ht0]; exact ht1
    · norm_num
  exact ⟨hDm, hinner, hnorm⟩

/-- Under a one-replica probability measure `G` with `Integrable (exp (‖p.1‖² / K₁)) G` (`K₁ > 0`),
the truncated overlap deviation `|(N + 1)⁻¹ ⟪D_t (σ a).1, D_t (σ b).1⟫ - m|` is in `L^4` under
`G^{⊗ R_big}`. -/
private lemma memLp_four_truncated_overlap_of_exp_sq_norm {R_big : Type*} [Fintype R_big] {N : ℕ}
    {G : Measure (ℝ^(N + 1) × ℝ)} [IsProbabilityMeasure G] {K₁ t m_val : ℝ} (hK₁ : 0 < K₁)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hexp : Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (‖p.1‖ ^ 2 / K₁)) G)
    (a b : R_big) :
    MemLp (fun σ : R_big → ℝ^(N + 1) × ℝ =>
        |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
          t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_val|) 4
      (Measure.pi fun _ : R_big => G) := by
  obtain ⟨hDm, hinner, hnorm⟩ := truncated_inner_and_norm_sq_le (N := N) ht0 ht1
  set D_t : ℝ^(N + 1) → ℝ^(N + 1) := fun x =>
    WithLp.toLp 2 fun i => (if i = Fin.last N then Real.sqrt t else 1) * x i
  have hXeq : ∀ σ : R_big → ℝ^(N + 1) × ℝ,
      |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
        t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_val| =
      |((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_val| := fun σ => by
    rw [hinner]
  simp_rw [hXeq]
  have hXm : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
      |((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_val| :=
    continuous_abs.measurable.comp
      ((((hDm.comp (measurable_fst.comp (measurable_pi_apply a))).inner
        (hDm.comp (measurable_fst.comp (measurable_pi_apply b)))).const_mul _).sub_const _)
  -- `|((N+1)⁻¹ ⟪D_t x, D_t y⟫ - m)|⁴ ≤ 8 * ((‖x‖² + ‖y‖²)⁴ + |m|⁴)` and `r⁸ ≤ C exp (r² / K₁)`
  have h8 : ∀ x : ℝ^(N + 1),
      (‖x‖ ^ 2) ^ 4 ≤ K₁ ^ 4 * ((4 : ℕ).factorial : ℝ) * Real.exp (‖x‖ ^ 2 / K₁) := fun x => by
    have hts := Real.pow_div_factorial_le_exp (‖x‖ ^ 2 / K₁) (by positivity) 4
    rw [div_pow, div_le_iff₀ (by positivity)] at hts
    have hK4 : 0 < K₁ ^ 4 := by positivity
    calc (‖x‖ ^ 2) ^ 4 = K₁ ^ 4 * ((‖x‖ ^ 2) ^ 4 / K₁ ^ 4) := by field_simp
      _ ≤ K₁ ^ 4 * (Real.exp (‖x‖ ^ 2 / K₁) * ((4 : ℕ).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hts hK4.le
      _ = K₁ ^ 4 * ((4 : ℕ).factorial : ℝ) * Real.exp (‖x‖ ^ 2 / K₁) := by ring
  have hmp_a := measurePreserving_eval (fun _ : R_big => G) a
  have hmp_b := measurePreserving_eval (fun _ : R_big => G) b
  have hdom : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
      8 * |m_val| ^ 4 + 8 * (8 * (K₁ ^ 4 * ((4 : ℕ).factorial : ℝ))) *
        (Real.exp (‖(σ a).1‖ ^ 2 / K₁) + Real.exp (‖(σ b).1‖ ^ 2 / K₁)))
      (Measure.pi fun _ : R_big => G) :=
    (integrable_const _).add (((hmp_a.integrable_comp_of_integrable hexp).add
      (hmp_b.integrable_comp_of_integrable hexp)).const_mul _)
  have hint4 : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
      ‖|((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_val|‖ ^ (4 : ℝ≥0∞).toReal)
      (Measure.pi fun _ : R_big => G) := by
    refine hdom.mono' (hXm.norm.pow_const _).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
    have hrpow : ‖|((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_val|‖ ^ (4 : ℝ≥0∞).toReal =
        |((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_val| ^ 4 := by
      rw [ENNReal.toReal_ofNat, Real.norm_of_nonneg (abs_nonneg _)]
      norm_cast
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hrpow]
    have hinv : ((N : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg N))
    have hinner_le : |((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫| ≤
        ‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine (mul_le_of_le_one_left (abs_nonneg _) hinv).trans ?_
      have hcs := abs_real_inner_le_norm (D_t (σ a).1) (D_t (σ b).1)
      nlinarith [sq_nonneg (‖D_t (σ a).1‖ - ‖D_t (σ b).1‖), hnorm (σ a).1, hnorm (σ b).1]
    have hab : |((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_val| ≤
        (‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2) + |m_val| :=
      (abs_sub _ _).trans (add_le_add hinner_le le_rfl)
    have hp1 : |((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_val| ^ 4 ≤
        8 * ((‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2) ^ 4 + |m_val| ^ 4) :=
      (pow_le_pow_left₀ (abs_nonneg _) hab 4).trans
        ((add_pow_le (by positivity) (abs_nonneg m_val) 4).trans_eq (by norm_num))
    have hp2 : (‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2) ^ 4 ≤
        8 * ((‖(σ a).1‖ ^ 2) ^ 4 + (‖(σ b).1‖ ^ 2) ^ 4) :=
      (add_pow_le (sq_nonneg _) (sq_nonneg _) 4).trans_eq (by norm_num)
    have h8a := h8 (σ a).1
    have h8b := h8 (σ b).1
    nlinarith
  exact (integrable_norm_rpow_iff hXm.aestronglyMeasurable (by norm_num) (by norm_num)).1 hint4

/-- Polynomial growth bound for `|f (σ ∘ some ∘ some)| * |R^t_{a,b} - m_ab|`, used to transfer
each term of Lemma 3.2.8 between the `(d, w)` and `(d_full, z)` disorder representations. -/
private lemma abs_mul_truncated_overlap_le_poly {R_rep : Type*} [Fintype R_rep] {N : ℕ}
    {t m_ab Q C : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htarget : |m_ab| ≤ Q) (hQ : 0 ≤ Q)
    (hC0 : 0 ≤ C) {f : (R_rep → ℝ^(N + 1)) → ℝ} {m : ℕ}
    (hfb : ∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) (a b : Option (Option R_rep))
    (σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ) :
    |(|f (fun l => (σ (some (some l))).1)| *
      |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
          t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|)| ≤
      C * (2 + Q) * ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ (m + 2) := by
  classical
  obtain ⟨-, hinner, hnorm⟩ := truncated_inner_and_norm_sq_le (N := N) ht0 ht1
  set D_t : ℝ^(N + 1) → ℝ^(N + 1) := fun x =>
    WithLp.toLp 2 fun i => (if i = Fin.last N then Real.sqrt t else 1) * x i
  rw [abs_mul, abs_abs, abs_abs]
  have hinv : ((N : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hR_le : |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
      t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab| ≤
      (2 + Q) * ((1 + ‖σ a‖) * (1 + ‖σ b‖)) := by
    rw [← hinner]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hna : ‖D_t (σ a).1‖ ≤ ‖(σ a).1‖ := by
      have hsq := hnorm (σ a).1
      nlinarith [norm_nonneg (D_t (σ a).1), norm_nonneg (σ a).1]
    have hnb : ‖D_t (σ b).1‖ ≤ ‖(σ b).1‖ := by
      have hsq := hnorm (σ b).1
      nlinarith [norm_nonneg (D_t (σ b).1), norm_nonneg (σ b).1]
    have h1 : |⟪D_t (σ a).1, D_t (σ b).1⟫| ≤ ‖(σ a).1‖ * ‖(σ b).1‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hna hnb (norm_nonneg _) (norm_nonneg _))
    have h2 : ((N : ℝ) + 1)⁻¹ * |⟪D_t (σ a).1, D_t (σ b).1⟫| ≤
        (1 + ‖σ a‖) * (1 + ‖σ b‖) := by
      refine (mul_le_of_le_one_left (abs_nonneg _) hinv).trans (h1.trans ?_)
      exact mul_le_mul (by linarith [norm_fst_le (σ a)]) (by linarith [norm_fst_le (σ b)])
        (norm_nonneg _) (by positivity)
    have h3 : (1 : ℝ) ≤ (1 + ‖σ a‖) * (1 + ‖σ b‖) :=
      one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg (σ a)])
        (by linarith [norm_nonneg (σ b)])
    nlinarith [htarget]
  have hf_le : |f (fun l => (σ (some (some l))).1)| ≤
      C * ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ m := by
    refine (hfb _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have hinj : Function.Injective (fun l : R_rep => some (some l)) :=
      (Option.some_injective _).comp (Option.some_injective _)
    calc ∏ l : R_rep, (1 + ‖(σ (some (some l))).1‖) ^ m
        ≤ ∏ l : R_rep, (1 + ‖σ (some (some l))‖) ^ m :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ =>
            pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (norm_fst_le _)) m
      _ = ∏ l ∈ Finset.univ.image (fun l : R_rep => some (some l)), (1 + ‖σ l‖) ^ m :=
          (Finset.prod_image (f := fun l : Option (Option R_rep) => (1 + ‖σ l‖) ^ m)
            fun _ _ _ _ h => hinj h).symm
      _ ≤ ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ m := by
          rw [← Finset.prod_sdiff (Finset.subset_univ
            (Finset.univ.image (fun l : R_rep => some (some l))))]
          exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity)
            (Finset.one_le_prod₀ fun l _ => one_le_pow₀ (by linarith [norm_nonneg (σ l)]))
  have hpair_le : (1 + ‖σ a‖) * (1 + ‖σ b‖) ≤
      ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ 2 := by
    by_cases hab : a = b
    · subst hab
      rw [← sq, ← Finset.prod_singleton (f := fun l => (1 + ‖σ l‖) ^ 2) a,
        ← Finset.prod_sdiff (Finset.subset_univ ({a} : Finset _))]
      exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity)
        (Finset.one_le_prod₀ fun l _ => one_le_pow₀ (by linarith [norm_nonneg (σ l)]))
    · have hsub : ({a, b} : Finset (Option (Option R_rep))) ⊆ Finset.univ := Finset.subset_univ _
      have h1 : (1 + ‖σ a‖) * (1 + ‖σ b‖) ≤ (1 + ‖σ a‖) ^ 2 * (1 + ‖σ b‖) ^ 2 := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact le_self_pow₀ (by linarith [norm_nonneg (σ a)]) (by norm_num)
        · exact le_self_pow₀ (by linarith [norm_nonneg (σ b)]) (by norm_num)
      refine h1.trans ?_
      rw [← Finset.prod_pair (f := fun l => (1 + ‖σ l‖) ^ 2) hab, ← Finset.prod_sdiff hsub]
      exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity)
        (Finset.one_le_prod₀ fun l _ => one_le_pow₀ (by linarith [norm_nonneg (σ l)]))
  calc |f (fun l => (σ (some (some l))).1)| *
        |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
          t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|
      ≤ (C * ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ m) *
          ((2 + Q) * ((1 + ‖σ a‖) * (1 + ‖σ b‖))) :=
        mul_le_mul hf_le hR_le (abs_nonneg _) (by positivity)
    _ ≤ (C * ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ m) *
          ((2 + Q) * ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair_le (by positivity))
          (by positivity)
    _ = C * (2 + Q) * ∏ l : Option (Option R_rep), (1 + ‖σ l‖) ^ (m + 2) := by
        rw [show C * (∏ l, (1 + ‖σ l‖) ^ m) * ((2 + Q) * ∏ l, (1 + ‖σ l‖) ^ 2) =
          C * (2 + Q) * ((∏ l, (1 + ‖σ l‖) ^ m) * (∏ l, (1 + ‖σ l‖) ^ 2)) by ring,
          ← Finset.prod_mul_distrib]
        congr 1; exact Finset.prod_congr rfl fun l _ => (pow_add _ m 2).symm

/-- **Eq. (3.105):** along `ν_{t,v}`, for any measurable spin observable `f` of polynomial growth
with `ν_{t,v₀}(f²) ≤ A²` (`0 ≤ A`), `v ↦ ν_{t,v}(f)` (in the `(d, w)` representation) has a
derivative `D` at `v₀ ∈ (0, 1)` satisfying
`|D| ≤ K * (ν_{t,v₀}(|f|) + exp (-(N + 1)) * A)`,
where `K > 0` depends only on `|R|`, `κ₀`, `h₀`, `D`, `Q`, `R`, `R_diff`.

Note: only `ν_{t,v₀}(f²) ≤ A²` at the point `v₀` is needed (not the supremum over all `v`), and
`D₂ = D` is used so the derivative bound on `u''` enters only via `D`. -/
theorem exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le_add_exp
    {R_rep : Type*} [Fintype R_rep]
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ)
      {f : (R_rep → ℝ^(N + 1)) → ℝ} {C : ℝ} {m : ℕ} {A v₀ : ℝ},
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → (r : ℝ) ≤ R → (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D) → -D ≤ u 0 →
      Measurable f → (∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) →
      0 ≤ A → v₀ ∈ Ioo (0 : ℝ) 1 →
      let P := (gaussianReal 0 r).prod
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
      let γ := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
      let S (v : ℝ) (w : Fin (N + 1) ⊕ Unit → ℝ) (p : ℝ^(N + 1) × ℝ) : ℝ :=
        Real.sqrt v * ((Real.sqrt (N + 1))⁻¹ *
            ((∑ i : Fin N, w (Sum.inl i.castSucc) * p.1 i.castSucc) +
              Real.sqrt t * (w (Sum.inl (Fin.last N)) * p.1 (Fin.last N)))) +
          Real.sqrt (1 - v) * (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (ρ - q) * p.2)
      let G (v : ℝ) (d : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)))
          (w : Fin (N + 1) ⊕ Unit → ℝ) : Measure (ℝ^(N + 1) × ℝ) :=
        ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 p.1 + u (S v w p)
      (∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P ≤ A ^ 2) →
      ∃ D_val : ℝ, HasDerivAt
          (fun v => ∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
            ∂(Measure.pi fun _ : R_rep => G v d w) ∂γ ∂P) D_val v₀ ∧
        |D_val| ≤ K * ((∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
            ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) + Real.exp (-((N : ℝ) + 1)) * A) := by
  classical
  obtain ⟨K₁, L, hK₁_pos, hL_pos, hK₁_ge₀, h3102⟩ :=
    exists_integral_exp_sq_norm_shcherbinaTirozziAuxCavity_le_exp κ₀ h₀ D Q R R_diff
      hκ₀ hQ hR hR_diff
  set n : ℕ := Fintype.card R_rep
  set B_stein : ℝ := ((n : ℝ) + 1) ^ 2 * (1 + 1 + 0 + 0 + |D| + |D|) ^ (n + 2)
  set K_thr : ℝ := K₁ * (L + 5) + Q + 1
  set C_X : ℝ := 1 + 2 ^ 7 * (2 ^ 7 * K₁ ^ 8 * (8 ^ 8 + L ^ 8) + Q ^ 8)
  set K_pair : ℝ := max K_thr (Real.sqrt (Real.sqrt C_X))
  set K : ℝ := B_stein * ((n + 2 : ℝ) ^ 2) * K_pair + 1
  have hK_thr_pos : 0 < K_thr := by dsimp only [K_thr]; positivity
  have hCX_nn : 0 ≤ C_X := by dsimp only [C_X]; positivity
  have hK_pos : 0 < K := by dsimp only [K, B_stein, K_pair]; positivity
  refine ⟨K, hK_pos, fun N M κ h t q ρ rBar r u f C m A v₀ hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR
    hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD hf hfb hA hv₀ => ?_⟩
  intro P γ S G hF2_bound
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hC0 : 0 ≤ C := by
    have h0 := (abs_nonneg (f 0)).trans (hfb 0)
    have hprod : (0 : ℝ) < ∏ _l : R_rep, (1 + ‖(0 : ℝ^(N + 1))‖) ^ m := by simp
    exact nonneg_of_mul_nonneg_left h0 hprod
  -- Step 1: Lemma 3.2.8 with `ψ = 1`
  obtain ⟨D_val, hderiv, hD_le⟩ := exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le
    (R := R_rep) hκ0 r hrr ht0 ht1 hq0 hqρ hu1 hu2 hu0 hD hD₂
    (fun _ _ => (1 : ℝ)) (fun _ => differentiable_const 1)
    (fun _ => by simp)
    (M₀ := 1) (M₁ := 0) (M₂ := 0)
    (fun _ _ => by norm_num) (fun _ _ => by simp) (fun _ _ => by simp)
    hf hfb hv₀
  simp only [Finset.prod_const_one, mul_one, abs_one, abs_zero] at hderiv hD_le
  refine ⟨D_val, hderiv, ?_⟩
  -- Step 2: Set up the `(d_full, z)` representation for `ν_{t,v₀}`
  let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
    -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
      (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
  let S_v₀ : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
    Real.sqrt v₀ * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
      Real.sqrt (1 - v₀) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
  let G_aux : AuxDis[N, M] → Measure (ℝ^(N + 1) × ℝ) := fun w =>
    ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
      fun p => E_old w p.1 + u (S_v₀ w p)
  have ha : K₁⁻¹ < κ := by
    refine inv_lt_of_inv_lt₀ hκ0 (lt_of_lt_of_le ?_
      ((div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ).trans hK₁_ge₀))
    rw [inv_eq_one_div]
    exact div_lt_div_of_pos_right (by norm_num) hκ0
  have hstate_big := shcherbinaTirozziAuxCavity_state_properties
    (R_rep := Option (Option R_rep)) (N := N) (M := M) (h := h)
    hκ0 hrr ht0 ht1 hum hu0 ha (r := r) (v := v₀) (q := q) (ρ := ρ)
  have hprob : ∀ w, IsProbabilityMeasure (G_aux w) := fun w => hstate_big.1 w
  have hsi : ∀ w, Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (‖p.1‖ ^ 2 / K₁)) (G_aux w) :=
    fun w => hstate_big.2.1 w
  have hν_big : ∀ Y : (Option (Option R_rep) → ℝ^(N + 1) × ℝ) → ℝ, Measurable Y →
      Measurable fun w => ∫ σ, Y σ ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux w) :=
    hstate_big.2.2
  -- Exponential moment bound (3.102)
  obtain ⟨hexp_i, hexp_le⟩ := h3102 N M κ h t v₀ q ρ rBar r u D hκ hh ht0 ht1 hv₀.1.le hv₀.2.le
    hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD
  have hEi : Integrable (fun w => ∫ p : ℝ^(N + 1) × ℝ, Real.exp (‖p.1‖ ^ 2 / K₁) ∂(G_aux w))
      auxLaw[N, M, r] := hexp_i
  have hE : ∫ w, ∫ p : ℝ^(N + 1) × ℝ, Real.exp (‖p.1‖ ^ 2 / K₁) ∂(G_aux w) ∂auxLaw[N, M, r] ≤
      Real.exp (L * ((N : ℝ) + 1)) := hexp_le
  -- Transfer `ν_{t,v₀}(|f|)` and `ν_{t,v₀}(f²)` to `(d_full, z)`
  have hnorm_le : ∀ p : ℝ^(N + 1) × ℝ, ‖p.1‖ ≤ ‖p‖ := fun p => norm_fst_le p
  have hF1_shared_int := integrable_shcherbinaTirozziAuxCavity_shared (R := R_rep) (N := N) (M := M)
    (h := h) hκ0 r hrr ht0 ht1 hv₀.1.le hv₀.2.le q ρ hu1 hu0 hD
    (G_obs := fun _ σ => |f (fun l => (σ l).1)|)
    (continuous_abs.measurable.comp
      ((hf.comp (Measurable.of_eval fun l =>
        measurable_fst.comp (measurable_pi_apply l))).comp measurable_snd))
    (C_G := C) (m := m) (fun _ σ => by
      rw [abs_abs]
      refine (hfb _).trans (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ =>
          pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (hnorm_le (σ l))) m) hC0))
  have hF1_eq := integral_shcherbinaTirozziAuxCavity_eq_shared (R := R_rep) (N := N) (M := M)
    (κ := κ) (h := h) r rBar t v₀ q ρ u (fun _ σ => |f (fun l => (σ l).1)|) hF1_shared_int
  have hF2_shared_int := integrable_shcherbinaTirozziAuxCavity_shared (R := R_rep) (N := N) (M := M)
    (h := h) hκ0 r hrr ht0 ht1 hv₀.1.le hv₀.2.le q ρ hu1 hu0 hD
    (G_obs := fun _ σ => f (fun l => (σ l).1) ^ 2)
    (((hf.comp (Measurable.of_eval fun l =>
      measurable_fst.comp (measurable_pi_apply l))).pow_const 2).comp measurable_snd)
    (C_G := C ^ 2) (m := 2 * m) (fun _ σ => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      refine (pow_le_pow_left₀ (abs_nonneg _) (hfb _) 2).trans ?_
      rw [mul_pow, ← Finset.prod_pow]
      refine mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ => ?_) (sq_nonneg C)
      rw [← pow_mul, mul_comm m 2]
      exact pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (hnorm_le (σ l))) _)
  have hF2_eq := integral_shcherbinaTirozziAuxCavity_eq_shared (R := R_rep) (N := N) (M := M)
    (κ := κ) (h := h) r rBar t v₀ q ρ u (fun _ σ => f (fun l => (σ l).1) ^ 2) hF2_shared_int
  have hmp_dis := measurePreserving_auxDisorder_to_shared (N := N) (M := M) r
  have hF1_full_int : Integrable (fun w => ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
      ∂(Measure.pi fun _ : R_rep => G_aux w)) auxLaw[N, M, r] :=
    (hmp_dis.integrable_comp hF1_shared_int.aestronglyMeasurable).2 hF1_shared_int
  have hF2_full_int : Integrable (fun w => ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
      ∂(Measure.pi fun _ : R_rep => G_aux w)) auxLaw[N, M, r] :=
    (hmp_dis.integrable_comp hF2_shared_int.aestronglyMeasurable).2 hF2_shared_int
  -- Also transfer each term `T a b` to `(d_full, z)`
  let T_shared (a b : Option (Option R_rep)) : ℝ :=
    ∫ d, ∫ w, ∫ σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ,
      |f (fun l => (σ (some (some l))).1)| *
        |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
            t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - if a = b then ρ else q|
      ∂(Measure.pi fun _ : Option (Option R_rep) => G v₀ d w) ∂γ ∂P
  have hT_eq : ∀ a b : Option (Option R_rep),
      T_shared a b = ∫ w, ∫ σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ,
        |f (fun l => (σ (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - if a = b then ρ else q|
        ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux w) ∂auxLaw[N, M, r] := by
    intro a b
    have hG_int := integrable_shcherbinaTirozziAuxCavity_shared (R := Option (Option R_rep))
      (N := N) (M := M) (h := h) hκ0 r hrr ht0 ht1 hv₀.1.le hv₀.2.le q ρ hu1 hu0 hD
      (G_obs := fun _ σ =>
        |f (fun l => (σ (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - if a = b then ρ else q|)
      (by
        have hf_m : Measurable fun σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ =>
            |f (fun l => (σ (some (some l))).1)| :=
          continuous_abs.measurable.comp (hf.comp (Measurable.of_eval fun l =>
            measurable_fst.comp (measurable_pi_apply (some (some l)))))
        have hσ_m : ∀ (c : Option (Option R_rep)) (i : Fin (N + 1)),
            Measurable fun σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ => (σ c).1 i := fun c i =>
          ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).comp
            (measurable_fst.comp (measurable_pi_apply c))
        have hR_m : Measurable fun σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ =>
            |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - if a = b then ρ else q| :=
          continuous_abs.measurable.comp
            ((((Finset.measurable_sum _ fun i _ =>
              (hσ_m a i.castSucc).mul (hσ_m b i.castSucc)).add
              (((hσ_m a (Fin.last N)).mul (hσ_m b (Fin.last N))).const_mul t)).const_mul
              _).sub_const _)
        exact (hf_m.mul hR_m).comp measurable_snd)
      (C_G := C * (2 + Q)) (m := m + 2)
      (fun _ σ => abs_mul_truncated_overlap_le_poly (m_ab := if a = b then ρ else q) ht0 ht1
        (by split <;> [rw [abs_of_nonneg (hq0.trans hqρ)]; rw [abs_of_nonneg hq0]] <;> linarith)
        hQ hC0 hfb a b σ)
    exact integral_shcherbinaTirozziAuxCavity_eq_shared (R := Option (Option R_rep))
      (N := N) (M := M) (κ := κ) (h := h) r rBar t v₀ q ρ u _ hG_int
  -- Step 3: Bound each `T_shared a b` with `G_aux` opaque
  have hF1_eq' : (∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
        ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) =
      ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
        ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r] := hF1_eq
  have hF2_full_bound : ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
      ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r] ≤ A ^ 2 := by
    rw [← hF2_eq]; exact hF2_bound
  clear_value G_aux
  obtain ⟨hDm_t, hinner_t, hnorm_t⟩ := truncated_inner_and_norm_sq_le (N := N) ht0 ht1
  set D_t : ℝ^(N + 1) → ℝ^(N + 1) := fun x =>
    WithLp.toLp 2 fun i => (if i = Fin.last N then Real.sqrt t else 1) * x i
  have hinj_some : Function.Injective (fun l : R_rep => some (some l)) :=
    (Option.some_injective _).comp (Option.some_injective _)
  have hF_big_m : Measurable fun σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ =>
      |f (fun l => (σ (some (some l))).1)| :=
    continuous_abs.measurable.comp (hf.comp (Measurable.of_eval fun l =>
      measurable_fst.comp (measurable_pi_apply (some (some l)))))
  have hF_small_m : Measurable fun σ : R_rep → ℝ^(N + 1) × ℝ => |f (fun l => (σ l).1)| :=
    continuous_abs.measurable.comp (hf.comp (Measurable.of_eval fun l =>
      measurable_fst.comp (measurable_pi_apply l)))
  have hF1_marg : ∀ w, (∫ σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ,
        |f (fun l => (σ (some (some l))).1)|
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux w)) =
      ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
        ∂(Measure.pi fun _ : R_rep => G_aux w) := fun w =>
    integral_pi_comp_injective (G_aux w) hinj_some _ hF_small_m.aestronglyMeasurable
  have hF2_marg : ∀ w, (∫ σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ,
        |f (fun l => (σ (some (some l))).1)| ^ 2
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux w)) =
      ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
        ∂(Measure.pi fun _ : R_rep => G_aux w) := fun w => by
    simp_rw [sq_abs]
    exact integral_pi_comp_injective (G_aux w) hinj_some
      (fun σ : R_rep → ℝ^(N + 1) × ℝ => f (fun l => (σ l).1) ^ 2)
      ((hf.comp (Measurable.of_eval fun l =>
        measurable_fst.comp (measurable_pi_apply l))).pow_const 2).aestronglyMeasurable
  have hT_le : ∀ a b : Option (Option R_rep),
      T_shared a b ≤ K_pair * ((∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
          ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r]) +
        Real.exp (-((N : ℝ) + 1)) * A) := by
    intro a b
    rw [hT_eq a b]
    set m_ab : ℝ := if a = b then ρ else q
    have htarget : |m_ab| ≤ Q := by
      dsimp only [m_ab]; split
      · rw [abs_of_nonneg (hq0.trans hqρ)]; exact hρQ
      · rw [abs_of_nonneg hq0]; exact hqρ.trans hρQ
    -- Overlap tail and 4th moment for `D_t`
    obtain ⟨htail, ⟨h4i, h4⟩, -⟩ := integral_integral_pi_overlap_tail_and_pow_le_of_exp_moment
      auxLaw[N, M, r] G_aux hν_big (X := fun p : ℝ^(N + 1) × ℝ => D_t p.1)
      (hDm_t.comp measurable_fst) (s := fun p : ℝ^(N + 1) × ℝ => ‖p.1‖ ^ 2 / K₁) hK₁_pos
      (fun p => by
        rw [mul_div_cancel₀ _ hK₁_pos.ne']
        exact hnorm_t p.1)
      hsi hEi hL_pos.le (le_add_of_nonneg_left (Nat.cast_nonneg N)) hE a b htarget
    have hKthr_gt : K₁ * (L + 5) + Q < K_thr := by dsimp only [K_thr]; linarith
    obtain ⟨hSi, hSb⟩ := htail K_thr hKthr_gt
    set X_ab : (Option (Option R_rep) → ℝ^(N + 1) × ℝ) → ℝ := fun σ =>
      |((N : ℝ) + 1)⁻¹ * ⟪D_t (σ a).1, D_t (σ b).1⟫ - m_ab|
    have hX_eq : ∀ σ, |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
        t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab| = X_ab σ := fun σ => by
      dsimp only [X_ab]; rw [hinner_t]
    simp_rw [hX_eq]
    have hX_m : Measurable X_ab :=
      continuous_abs.measurable.comp
        ((((hDm_t.comp (measurable_fst.comp (measurable_pi_apply a))).inner
          (hDm_t.comp (measurable_fst.comp (measurable_pi_apply b)))).const_mul _).sub_const _)
    have hX4_mem : ∀ w, MemLp X_ab 4 (Measure.pi fun _ : Option (Option R_rep) => G_aux w) :=
      fun w => by
        have h := memLp_four_truncated_overlap_of_exp_sq_norm (R_big := Option (Option R_rep))
          hK₁_pos ht0 ht1 (hsi w) a b (m_val := m_ab)
        exact h.ae_eq (ae_of_all _ fun σ => hX_eq σ)
    have hF2_mem : ∀ w, MemLp (fun σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ =>
        |f (fun l => (σ (some (some l))).1)|) 2
        (Measure.pi fun _ : Option (Option R_rep) => G_aux w) := fun w =>
      memLp_two_pi_comp_injective_of_poly_bound _ hinj_some measurable_fst hf hfb
        (by simpa only [abs_norm] using
          integrable_one_add_abs_pow_of_integrable_exp_sq
            ((measurable_norm.comp measurable_fst).aestronglyMeasurable) hK₁_pos (hsi w) _)
    have hSb' : ∫ w, ∫ σ, ({τ | K_thr ≤ X_ab τ}.indicator (fun _ => (1 : ℝ)) σ)
        ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux w) ∂auxLaw[N, M, r] ≤
        (Real.exp (-((N : ℝ) + 1))) ^ 4 := by
      refine hSb.trans_eq ?_
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsplit := (integral_integral_mul_le_add_indicator_tail
      (P := auxLaw[N, M, r]) (μ := fun w => Measure.pi fun _ : Option (Option R_rep) => G_aux w)
      (F := fun σ => |f (fun l => (σ (some (some l))).1)|) (X := X_ab)
      (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hF_big_m hX_m hF2_mem hX4_mem
      hK_thr_pos.le hCX_nn (Real.exp_pos _).le hA
      (fun hY => (hν_big _ hY).aestronglyMeasurable)
      (hF1_full_int.congr (ae_of_all _ fun w => (hF1_marg w).symm))
      (hF2_full_int.congr (ae_of_all _ fun w => (hF2_marg w).symm))
      (by simpa only [hF2_marg] using hF2_full_bound)
      h4i h4 hSi hSb').2
    simp_rw [hF1_marg] at hsplit
    have hI1_nn : 0 ≤ ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
        ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r] :=
      integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
    have hle1 : K_thr ≤ K_pair := le_max_left _ _
    have hle2 : Real.sqrt (Real.sqrt C_X) ≤ K_pair := le_max_right _ _
    calc ∫ w, ∫ σ, |f (fun l => (σ (some (some l))).1)| * X_ab σ
            ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux w) ∂auxLaw[N, M, r]
        ≤ K_thr * (∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
            ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r]) +
          Real.sqrt (Real.sqrt C_X) * Real.exp (-((N : ℝ) + 1)) * A := hsplit
      _ ≤ K_pair * (∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
            ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r]) +
          K_pair * (Real.exp (-((N : ℝ) + 1)) * A) := by
            rw [mul_assoc]
            exact add_le_add (mul_le_mul_of_nonneg_right hle1 hI1_nn)
              (mul_le_mul_of_nonneg_right hle2 (mul_nonneg (Real.exp_pos _).le hA))
      _ = K_pair * ((∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
            ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r]) +
          Real.exp (-((N : ℝ) + 1)) * A) := by ring
  -- Step 4: Sum over `(a, b) : Option (Option R_rep) × Option (Option R_rep)` and finish
  have hsum_le : ∑ a : Option (Option R_rep), ∑ b : Option (Option R_rep), T_shared a b ≤
      ((n + 2 : ℝ) ^ 2) * (K_pair * ((∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          |f (fun l => (σ l).1)| ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) +
        Real.exp (-((N : ℝ) + 1)) * A)) := by
    have hcard : (Fintype.card (Option (Option R_rep)) : ℝ) = (n : ℝ) + 2 := by
      simp only [Fintype.card_option, n]; push_cast; ring
    calc ∑ a : Option (Option R_rep), ∑ b : Option (Option R_rep), T_shared a b
        ≤ ∑ _a : Option (Option R_rep), ∑ _b : Option (Option R_rep),
            K_pair * ((∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
              ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r]) +
              Real.exp (-((N : ℝ) + 1)) * A) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hT_le a b
      _ = ((n + 2 : ℝ) ^ 2) * (K_pair * ((∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
            |f (fun l => (σ l).1)| ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) +
          Real.exp (-((N : ℝ) + 1)) * A)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← hF1_eq']
          ring
  have hB_nn : 0 ≤ B_stein := by dsimp only [B_stein]; positivity
  have hterm_nn : 0 ≤ (∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
      ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) + Real.exp (-((N : ℝ) + 1)) * A :=
    add_nonneg (integral_nonneg fun _ => integral_nonneg fun _ => integral_nonneg fun _ =>
      abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hA)
  calc |D_val| ≤ B_stein * ∑ a, ∑ b, T_shared a b := hD_le
    _ ≤ B_stein * (((n + 2 : ℝ) ^ 2) * (K_pair * ((∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          |f (fun l => (σ l).1)| ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) +
        Real.exp (-((N : ℝ) + 1)) * A))) :=
        mul_le_mul_of_nonneg_left hsum_le hB_nn
    _ = (B_stein * ((n + 2 : ℝ) ^ 2) * K_pair) * ((∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          |f (fun l => (σ l).1)| ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) +
        Real.exp (-((N : ℝ) + 1)) * A) := by ring
    _ ≤ K * ((∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
          ∂(Measure.pi fun _ : R_rep => G v₀ d w) ∂γ ∂P) + Real.exp (-((N : ℝ) + 1)) * A) := by
        refine mul_le_mul_of_nonneg_right ?_ hterm_nn
        dsimp only [K]; linarith

/-- **Talagrand, Lemma 3.2.9 (Eq. (3.106)):** for any nonnegative measurable spin observable `f` of
polynomial growth with `ν_{t,s}(f²) ≤ A²` for all `s ∈ [0, 1]` (`0 ≤ A`), and every `v ∈ [0, 1]`,
`ν_{t,v}(f) ≤ K * (ν_t(f) + exp (-(N + 1)) * A)`,
where `K > 0` depends only on `|R|`, `κ₀`, `h₀`, `D`, `Q`, `R`, `R_diff`. -/
theorem exists_shcherbinaTirozziAuxCavity_le_add_exp
    {R_rep : Type*} [Fintype R_rep]
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ)
      {f : (R_rep → ℝ^(N + 1)) → ℝ} {C : ℝ} {m : ℕ} {A v : ℝ},
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → (r : ℝ) ≤ R → (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D) → -D ≤ u 0 →
      Measurable f → (∀ σ, 0 ≤ f σ) → (∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) →
      0 ≤ A → v ∈ Icc (0 : ℝ) 1 →
      let P_full := ((gaussianReal 0 r).prod
        ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
      let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let S_v (s : ℝ) : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
        Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
          Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
      let G_aux (s : ℝ) : AuxDis[N, M] → Measure (ℝ^(N + 1) × ℝ) := fun w =>
        ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
          fun p => E_old w p.1 + u (S_v s w p)
      (∀ s ∈ Icc (0 : ℝ) 1,
        ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : R_rep => G_aux s w) ∂auxLaw[N, M, r] ≤ A ^ 2) →
      ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
          ∂(Measure.pi fun _ : R_rep => G_aux v w) ∂auxLaw[N, M, r] ≤
        K * ((∫ d, ∫ a : R_rep → ℝ^(N + 1), f a
            ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
              -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ) ∂P_full) +
          Real.exp (-((N : ℝ) + 1)) * A) := by
  classical
  obtain ⟨K₀, hK₀_pos, h3105⟩ :=
    exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le_add_exp (R_rep := R_rep)
      κ₀ h₀ D Q R R_diff hκ₀ hQ hR hR_diff
  set K : ℝ := Real.exp (K₀ + 1) * max 1 K₀
  have hK_pos : 0 < K := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨K, hK_pos, fun N M κ h t q ρ rBar r u f C m A v hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR
    hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD hf hf0 hfb hA hv => ?_⟩
  intro P_full E_old S_v G_aux hF2_all
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hC0 : 0 ≤ C := by
    have h0 := (abs_nonneg (f 0)).trans (hfb 0)
    have hprod : (0 : ℝ) < ∏ _l : R_rep, (1 + ‖(0 : ℝ^(N + 1))‖) ^ m := by simp
    exact nonneg_of_mul_nonneg_left h0 hprod
  let P := (gaussianReal 0 r).prod
    ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
  let γ := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
  let S_sh (s : ℝ) (w : Fin (N + 1) ⊕ Unit → ℝ) (p : ℝ^(N + 1) × ℝ) : ℝ :=
    Real.sqrt s * ((Real.sqrt (N + 1))⁻¹ *
        ((∑ i : Fin N, w (Sum.inl i.castSucc) * p.1 i.castSucc) +
          Real.sqrt t * (w (Sum.inl (Fin.last N)) * p.1 (Fin.last N)))) +
      Real.sqrt (1 - s) * (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (ρ - q) * p.2)
  let G_sh (s : ℝ) (d : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)))
      (w : Fin (N + 1) ⊕ Unit → ℝ) : Measure (ℝ^(N + 1) × ℝ) :=
    ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 p.1 + u (S_sh s w p)
  let ψ : ℝ → ℝ := fun s =>
    ∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R_rep => G_sh s d w) ∂γ ∂P
  -- Equivalence of `ψ s` and the `(d_full, z)` integral for every `s ∈ [0, 1]`
  have hψ_eq : ∀ s ∈ Icc (0 : ℝ) 1, ψ s =
      ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R_rep => G_aux s w) ∂auxLaw[N, M, r] := fun s hs => by
    have hint := integrable_shcherbinaTirozziAuxCavity_shared (R := R_rep) (N := N) (M := M)
      (h := h) hκ0 r hrr ht0 ht1 hs.1 hs.2 q ρ hu1 hu0 hD
      (G_obs := fun _ σ => f (fun l => (σ l).1))
      ((hf.comp (Measurable.of_eval fun l =>
        measurable_fst.comp (measurable_pi_apply l))).comp measurable_snd)
      (C_G := C) (m := m) (fun _ σ => (hfb _).trans (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ =>
          pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (norm_fst_le (σ l))) m) hC0))
    exact integral_shcherbinaTirozziAuxCavity_eq_shared (R := R_rep) (N := N) (M := M)
      (κ := κ) (h := h) r rBar t s q ρ u (fun _ σ => f (fun l => (σ l).1)) hint
  have hF2_eq : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
        ∂(Measure.pi fun _ : R_rep => G_sh s d w) ∂γ ∂P) =
      ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
        ∂(Measure.pi fun _ : R_rep => G_aux s w) ∂auxLaw[N, M, r] := fun s hs => by
    have hint := integrable_shcherbinaTirozziAuxCavity_shared (R := R_rep) (N := N) (M := M)
      (h := h) hκ0 r hrr ht0 ht1 hs.1 hs.2 q ρ hu1 hu0 hD
      (G_obs := fun _ σ => f (fun l => (σ l).1) ^ 2)
      (((hf.comp (Measurable.of_eval fun l =>
        measurable_fst.comp (measurable_pi_apply l))).pow_const 2).comp measurable_snd)
      (C_G := C ^ 2) (m := 2 * m) (fun _ σ => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        refine (pow_le_pow_left₀ (abs_nonneg _) (hfb _) 2).trans ?_
        rw [mul_pow, ← Finset.prod_pow]
        refine mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ => ?_) (sq_nonneg C)
        rw [← pow_mul, mul_comm m 2]
        exact pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (norm_fst_le (σ l))) _)
    exact integral_shcherbinaTirozziAuxCavity_eq_shared (R := R_rep) (N := N) (M := M)
      (κ := κ) (h := h) r rBar t s q ρ u (fun _ σ => f (fun l => (σ l).1) ^ 2) hint
  -- Continuity on `[0, 1]`
  have hcont : ContinuousOn ψ (Icc 0 1) := by
    have hc := continuousOn_shcherbinaTirozziAuxCavity (R := R_rep) (N := N) (M := M)
      (h := h) hκ0 r hrr ht0 ht1 q ρ hu1 hu0 hD (fun _ _ => (1 : ℝ)) (fun _ => continuous_const)
      (M₀ := 1) (fun _ _ => by norm_num) hf hfb
    simpa only [Finset.prod_const_one, mul_one] using hc
  -- Nonnegativity on `[0, 1]`
  have hψ0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ ψ s := fun s _ =>
    integral_nonneg fun _ => integral_nonneg fun _ => integral_nonneg fun _ => hf0 _
  -- Derivative lower bound on `(0, 1)` from Eq. (3.105)
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt ψ d s ∧
      -(K₀ * ψ s + K₀ * (Real.exp (-((N : ℝ) + 1)) * A)) ≤ d := by
    intro s hs
    have hF2s : ∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1) ^ 2
        ∂(Measure.pi fun _ : R_rep => G_sh s d w) ∂γ ∂P ≤ A ^ 2 := by
      rw [hF2_eq s ⟨hs.1.le, hs.2.le⟩]
      exact hF2_all s ⟨hs.1.le, hs.2.le⟩
    obtain ⟨d, hd, hdb⟩ := h3105 N M κ h t q ρ rBar r u hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR
      hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD hf hfb hA hs hF2s
    have habs_eq : (∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, |f (fun l => (σ l).1)|
        ∂(Measure.pi fun _ : R_rep => G_sh s d w) ∂γ ∂P) = ψ s := by
      simp_rw [abs_of_nonneg (hf0 _)]; rfl
    rw [habs_eq] at hdb
    refine ⟨d, hd, ?_⟩
    have hneg := (abs_le.1 hdb).1
    linarith
  -- Apply backward Grönwall (Lemma A.13.1) and identify `ψ 1 = ν_t(f)`
  have hgron := le_exp_mul_add_endpoint_of_exists_hasDerivAt_Ioo hK₀_pos.le
    (mul_nonneg hK₀_pos.le (mul_nonneg (Real.exp_pos _).le hA)) hcont hψ0 hderiv hv
  rw [← hψ_eq v hv]
  have hψ1 : ψ 1 = ∫ d, ∫ a : R_rep → ℝ^(N + 1), f a
      ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ) ∂P_full := by
    rw [hψ_eq 1 ⟨zero_le_one, le_rfl⟩]
    exact integral_pi_shcherbinaTirozziAuxCavity_one κ h r rBar t q ρ u f
  rw [hψ1] at hgron
  have h1_nn : 0 ≤ ∫ d, ∫ a : R_rep → ℝ^(N + 1), f a
      ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ) ∂P_full :=
    integral_nonneg fun _ => integral_nonneg fun _ => hf0 _
  have h2_nn : 0 ≤ Real.exp (-((N : ℝ) + 1)) * A := mul_nonneg (Real.exp_pos _).le hA
  refine hgron.trans ?_
  dsimp only [K]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left h1_nn (le_max_left 1 K₀))
    (mul_le_mul_of_nonneg_right (le_max_right 1 K₀) h2_nn)

end SpinGlasses
