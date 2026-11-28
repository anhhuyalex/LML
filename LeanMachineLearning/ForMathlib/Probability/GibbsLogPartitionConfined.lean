/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.Order.Interval.UnitIoo
import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.LogSmoothing
import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaConfinedStein

/-!
# Log-partition differentiation along a square-root cavity path under quadratic confinement

Given a confined base energy `E₀ ω x ≤ B₀ ω ‖x‖ - κ ‖x‖²` (`κ > 0`) on a finite-dimensional
normed space `E` with additive Haar measure `μ`, consider the log-partition average
```
φ(v) = ∫ ω, ∫ w, log ∫ p : E × ℝ, exp (u (S_v(w, p))) d((μ.tilted (E₀ ω)) × 𝒩(0, 1)) dγ(w) dP₀(ω)
```
where `S_v(w, (x, ξ)) = √v (X x ⬝ᵥ w) + √(1 - v) (Y ⬝ᵥ w + c_ξ ξ)`, `X x ⬝ᵥ Y = 0`, and
`u ≤ 0` has bounded first two derivatives.

Differentiating `v ↦ log ∫ exp (u ∘ S_v)` inside the disorder expectations via
`hasDerivAt_log_integral_exp_sqrt_path`, justifying dominated differentiation across `(P₀ × γ)`
via the polynomial moment bounds of `GibbsReplicaConfinedStein`, and applying multivariate
Gaussian Stein integration by parts (`stein_pi_tilted_prod_gaussianReal`) with a single replica
yields `ContinuousOn φ [0, 1]` and, for `v ∈ (0, 1)`,
```
φ'(v) = (1 / 2) * (
  𝔼 [ ν_v ( (X(x¹) ⬝ᵥ X(x¹) - (Y ⬝ᵥ Y + c_ξ²)) (u'' + u'²)(S_v(w, p¹)) ) ] -
  𝔼 [ ν_v^⊗2 ( (X(x¹) ⬝ᵥ X(x²) - Y ⬝ᵥ Y) u'(S_v(w, p¹)) u'(S_v(w, p²)) ) ] ).
```
This is the model-free core of Talagrand, *Spin Glasses*, Vol. I, Lemma 3.3.5.

## Main declarations

* `MeasureTheory.continuousOn_integral_log_integral_exp_tilted_prod_gaussianReal_sqrt`:
  continuity of `φ` on `[0, 1]`. It needs neither `X x ⬝ᵥ Y = 0` nor a second derivative of `u`.
* `MeasureTheory.hasDerivAt_and_continuousOn_log_integral_exp_tilted_prod_gaussianReal_sqrt`:
  continuity on `[0, 1]` and derivative-by-parts formula on `(0, 1)` for `φ`.

The disorder measure `P₀` is any s-finite measure; the moment hypothesis makes it finite.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped NNReal Topology BigOperators

namespace MeasureTheory

section LogPartitionConfined

private lemma integrable_one_add_norm_pow_tilted_prod_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {κ B₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2) {v₀ : E × ℝ → ℝ}
    (hv₀m : Measurable v₀) (hv₀ : ∀ p, v₀ p ≤ 0) (m : ℕ) :
    Integrable (fun p : E × ℝ => (1 + ‖p‖) ^ m)
      ((μ.prod (gaussianReal 0 1)).tilted fun p => E₀ p.1 + v₀ p) := by
  rw [tilted_prod_gaussianReal_zero_one μ]
  have hem : Measurable fun p : E × ℝ => E₀ p.1 + v₀ p - p.2 ^ 2 / 2 :=
    ((hE₀m.comp measurable_fst).add hv₀m).sub ((measurable_snd.pow_const 2).div_const 2)
  refine (memLp_of_poly_bound_of_confining (μ := μ.prod volume) (lt_min hκ one_half_pos) hem
    (A := 0) (B := B₀)
    (fun p => by
      simpa only [min_eq_left (hv₀ p)] using prod_gaussian_exponent_confining hκ hB₀ hE₀_conf
        (u := fun x => min x 0) (fun x => min_le_right x 0) v₀ p)
    (f := fun p : E × ℝ => (1 + ‖p‖) ^ m) (by fun_prop) (C := 1) (m := m)
    (fun p => by rw [Real.norm_of_nonneg (by positivity), one_mul]) 1).integrable le_rfl

private lemma half_add_pow_le {B₀ c₀ : ℝ} (hB₀ : 0 ≤ B₀) (hc₀ : 0 ≤ c₀) (m : ℕ) :
    (1 + B₀ + c₀ + 1 / 2) ^ m ≤ (3 / 2 : ℝ) ^ m * (1 + B₀ + c₀) ^ m := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith) m

private lemma abs_linear_field_le {E K : Type*} [NormedAddCommGroup E] [Fintype K]
    {X : E → K → ℝ} {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (Y : K → ℝ) (c_ξ : ℝ) (w : K → ℝ) (p : E × ℝ) :
    |X p.1 ⬝ᵥ w| ≤ (|L_X| * ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) ∧
      |Y ⬝ᵥ w + c_ξ * p.2| ≤ ((∑ k, |Y k|) * ∑ k, |w k| + |c_ξ|) * (1 + ‖p‖) ^ (n_X + 1) := by
  have hw0 : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · have h1 : |X p.1 ⬝ᵥ w| ≤ |L_X| * (1 + ‖p.1‖) ^ n_X * ∑ k, |w k| :=
      abs_dotProduct_le_mul_sum_abs (fun k =>
        (hXb k p.1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))) w
    have h2 : (1 + ‖p.1‖) ^ n_X ≤ (1 + ‖p‖) ^ (n_X + 1) :=
      (pow_le_pow_left₀ (by positivity) (by linarith [norm_fst_le p]) _).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg p]) (Nat.le_succ _))
    calc |X p.1 ⬝ᵥ w| ≤ |L_X| * (1 + ‖p.1‖) ^ n_X * ∑ k, |w k| := h1
      _ = (|L_X| * ∑ k, |w k|) * (1 + ‖p.1‖) ^ n_X := by ring
      _ ≤ (|L_X| * ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) := mul_le_mul_of_nonneg_left h2
          (mul_nonneg (abs_nonneg _) hw0)
  · set s_Y := ∑ k, |Y k|
    have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hdot : |Y ⬝ᵥ w| ≤ s_Y * ∑ k, |w k| :=
      abs_dotProduct_le_mul_sum_abs (fun k => Finset.single_le_sum (f := fun j => |Y j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ k)) w
    have hξ : |p.2| ≤ (1 + ‖p‖) ^ (n_X + 1) :=
      ((Real.norm_eq_abs _).symm.trans_le (norm_snd_le p)).trans
        ((le_add_of_nonneg_left zero_le_one).trans
          (le_self_pow₀ (by linarith [norm_nonneg p]) (Nat.succ_ne_zero _)))
    have h1 : 1 ≤ (1 + ‖p‖) ^ (n_X + 1) := one_le_pow₀ (by linarith [norm_nonneg p])
    have hprod : s_Y * (∑ k, |w k|) * 1 ≤ s_Y * (∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hsY0 hw0)
    calc |Y ⬝ᵥ w + c_ξ * p.2|
        ≤ |Y ⬝ᵥ w| + |c_ξ| * |p.2| := (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ s_Y * (∑ k, |w k|) * 1 + |c_ξ| * (1 + ‖p‖) ^ (n_X + 1) := add_le_add
          (by simpa only [mul_one] using hdot) (mul_le_mul_of_nonneg_left hξ (abs_nonneg _))
      _ ≤ s_Y * (∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) + |c_ξ| * (1 + ‖p‖) ^ (n_X + 1) :=
          add_le_add hprod le_rfl
      _ = (s_Y * ∑ k, |w k| + |c_ξ|) * (1 + ‖p‖) ^ (n_X + 1) := by ring

private lemma abs_linear_field_sum_le {E K : Type*} [NormedAddCommGroup E] [Fintype K]
    {X : E → K → ℝ} {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (Y : K → ℝ) (c_ξ : ℝ) (w : K → ℝ) (p : E × ℝ) :
    |X p.1 ⬝ᵥ w| + |Y ⬝ᵥ w + c_ξ * p.2| ≤
      (|L_X| + ∑ k, |Y k| + |c_ξ|) * (1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) := by
  obtain ⟨hx, hy⟩ := abs_linear_field_le hXb Y c_ξ w p
  have hw0 : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsY0 : 0 ≤ ∑ k : K, |Y k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp0 : 0 ≤ (1 + ‖p‖) ^ (n_X + 1) := by positivity
  refine (add_le_add hx hy).trans ?_
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ hp0
  nlinarith [abs_nonneg L_X, abs_nonneg c_ξ]

private lemma measurable_sqrt_field {E K : Type*} [MeasurableSpace E] [Fintype K]
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    (c_ξ v : ℝ) :
    Measurable fun q : (K → ℝ) × (E × ℝ) =>
      Real.sqrt v * (X q.2.1 ⬝ᵥ q.1) + Real.sqrt (1 - v) * (Y ⬝ᵥ q.1 + c_ξ * q.2.2) := by
  have hXdot : Measurable fun q : (K → ℝ) × (E × ℝ) => X q.2.1 ⬝ᵥ q.1 :=
    Finset.measurable_sum _ fun k _ =>
      ((hXm k).comp (measurable_fst.comp measurable_snd)).mul
        ((measurable_pi_apply k).comp measurable_fst)
  have hYξ : Measurable fun q : (K → ℝ) × (E × ℝ) => Y ⬝ᵥ q.1 + c_ξ * q.2.2 :=
    (Finset.measurable_sum _ fun k _ =>
      measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
      ((measurable_snd.comp measurable_snd).const_mul c_ξ)
  exact (hXdot.const_mul _).add (hYξ.const_mul _)

private lemma abs_log_integral_exp_sqrt_path_le
    {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype K]
    {κ B₀ c₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2) (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁) {C_G : ℝ}
    (hG0_mom : ∫ p : E × ℝ, (1 + ‖p‖) ^ (n_X + 1) ∂((μ.tilted E₀).prod (gaussianReal 0 1)) ≤
      C_G * (1 + B₀ + c₀ + 1 / 2) ^ (n_X + 1))
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (w : K → ℝ) :
    let S (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    |Real.log (∫ p : E × ℝ, Real.exp (u (S p)) ∂((μ.tilted E₀).prod (gaussianReal 0 1)))| ≤
      (|u 0| + D₁ * (|L_X| + ∑ k, |Y k| + |c_ξ|)) * C_G * (3 / 2 : ℝ) ^ (n_X + 1) *
        (1 + ∑ k, |w k|) * (1 + B₀ + c₀) ^ (n_X + 1) := by
  intro S
  have hc₀ : 0 ≤ c₀ := nonneg_of_confining_of_neg_le hE₀_conf hE₀_low
  have hum : Measurable u := hu.continuous.measurable
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0)
  have hEi : Integrable (fun x => Real.exp (E₀ x)) μ :=
    integrable_exp_of_confining (μ := μ) hκ hE₀m (A := 0) (B := B₀) fun x => by
      simpa only [zero_add] using hE₀_conf x
  have : IsProbabilityMeasure (μ.tilted E₀) := isProbabilityMeasure_tilted hEi
  have hpow_int : Integrable (fun p : E × ℝ => (1 + ‖p‖) ^ (n_X + 1))
      ((μ.tilted E₀).prod (gaussianReal 0 1)) := by
    rw [← tilted_prod_comp_fst]
    simpa only [add_zero] using integrable_one_add_norm_pow_tilted_prod_base μ hκ hB₀ hE₀m hE₀_conf
      measurable_const (fun _ => le_rfl) (n_X + 1)
  have hSm : Measurable S :=
    (measurable_sqrt_field X Y hXm c_ξ v).comp measurable_prodMk_left
  have hexp_u_int : Integrable (fun p => Real.exp (u (S p)))
      ((μ.tilted E₀).prod (gaussianReal 0 1)) :=
    Integrable.of_bound (hum.comp hSm).exp.aestronglyMeasurable 1 (ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.2 (hu0 _))
  have hZ_le : ∫ p : E × ℝ, Real.exp (u (S p)) ∂((μ.tilted E₀).prod (gaussianReal 0 1)) ≤ 1 :=
    (integral_mono hexp_u_int (integrable_const 1) fun p =>
      Real.exp_le_one_iff.2 (hu0 _)).trans_eq (by simp)
  have hZ_pos : 0 < ∫ p : E × ℝ, Real.exp (u (S p)) ∂((μ.tilted E₀).prod (gaussianReal 0 1)) :=
    integral_exp_pos_of_ae_le (hum.comp hSm).aemeasurable (ae_of_all _ fun _ => hu0 _)
  have hPhi_le0 : Real.log (∫ p : E × ℝ, Real.exp (u (S p))
      ∂((μ.tilted E₀).prod (gaussianReal 0 1))) ≤ 0 := Real.log_nonpos hZ_pos.le hZ_le
  set L_sum := |L_X| + ∑ k, |Y k| + |c_ξ|
  have hw0 : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS_le : ∀ p, |S p| ≤ L_sum * (1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) := fun p => by
    have hs1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv.2
    have hs2 : Real.sqrt (1 - v) ≤ 1 := Real.sqrt_le_one.2 (by linarith [hv.1])
    calc |S p| ≤ Real.sqrt v * |X p.1 ⬝ᵥ w| + Real.sqrt (1 - v) * |Y ⬝ᵥ w + c_ξ * p.2| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ 1 * |X p.1 ⬝ᵥ w| + 1 * |Y ⬝ᵥ w + c_ξ * p.2| := add_le_add
          (mul_le_mul_of_nonneg_right hs1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hs2 (abs_nonneg _))
      _ ≤ L_sum * (1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) := by
          rw [one_mul, one_mul]; exact abs_linear_field_sum_le hXb Y c_ξ w p
  set c_g := (|u 0| + D₁ * L_sum) * (1 + ∑ k, |w k|)
  have hcg0 : 0 ≤ c_g := by positivity
  let g : E × ℝ → ℝ := fun p => -(c_g * (1 + ‖p‖) ^ (n_X + 1))
  have hgu : ∀ p, g p ≤ u (S p) := fun p => by
    have hlip := neg_le_of_abs_le (norm_le_norm_zero_add_of_norm_deriv_le hu hD₁ (S p))
    simp only [Real.norm_eq_abs] at hlip
    have h11 : 1 ≤ (1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith [norm_nonneg p]))
    have h1 : |u 0| + D₁ * |S p| ≤ c_g * (1 + ‖p‖) ^ (n_X + 1) := by
      calc |u 0| + D₁ * |S p|
          ≤ |u 0| * ((1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1)) +
            D₁ * (L_sum * (1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1)) :=
              add_le_add (le_mul_of_one_le_right (abs_nonneg _) h11)
                (mul_le_mul_of_nonneg_left (hS_le p) hD₁0)
        _ = c_g * (1 + ‖p‖) ^ (n_X + 1) := by dsimp only [c_g]; ring
    dsimp only [g]; linarith
  have hexp_g_int : Integrable (fun p => Real.exp (g p)) ((μ.tilted E₀).prod (gaussianReal 0 1)) :=
    Integrable.of_bound (by fun_prop : Measurable fun p : E × ℝ =>
      Real.exp (g p)).aestronglyMeasurable 1 (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg hcg0 (by positivity))
  have hjensen := convexOn_exp.map_integral_le (μ := (μ.tilted E₀).prod (gaussianReal 0 1))
    Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => mem_univ _)
    ((hpow_int.const_mul c_g).neg) hexp_g_int
  have hlog_ge : ∫ p, g p ∂((μ.tilted E₀).prod (gaussianReal 0 1)) ≤
      Real.log (∫ p : E × ℝ, Real.exp (u (S p)) ∂((μ.tilted E₀).prod (gaussianReal 0 1))) := by
    have hexp_le := hjensen.trans (integral_mono hexp_g_int hexp_u_int fun p =>
      Real.exp_le_exp.2 (hgu p))
    have hlog := Real.log_le_log (Real.exp_pos _) hexp_le
    rwa [Real.log_exp] at hlog
  have hCG0 : 0 ≤ C_G := by
    have hnonneg : 0 ≤ ∫ p : E × ℝ, (1 + ‖p‖) ^ (n_X + 1)
        ∂((μ.tilted E₀).prod (gaussianReal 0 1)) := integral_nonneg fun _ => by positivity
    nlinarith [hnonneg.trans hG0_mom, pow_pos (by linarith : 0 < 1 + B₀ + c₀ + 1 / 2) (n_X + 1)]
  have hint_g_bd : -((|u 0| + D₁ * L_sum) * C_G * (3 / 2 : ℝ) ^ (n_X + 1) *
      (1 + ∑ k, |w k|) * (1 + B₀ + c₀) ^ (n_X + 1)) ≤
      ∫ p, g p ∂((μ.tilted E₀).prod (gaussianReal 0 1)) := by
    dsimp only [g]
    rw [integral_neg, integral_const_mul, neg_le_neg_iff]
    refine (mul_le_mul_of_nonneg_left hG0_mom hcg0).trans ?_
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (half_add_pow_le hB₀ hc₀ (n_X + 1)) hCG0) hcg0).trans_eq ?_
    dsimp only [c_g, L_sum]; ring
  rw [abs_le]
  exact ⟨hint_g_bd.trans hlog_ge, hPhi_le0.trans (by positivity)⟩

private lemma abs_deriv_log_integral_exp_sqrt_path_le
    {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype K]
    {κ B₀ c₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2) (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁) {C_G : ℝ} (hCG0 : 0 ≤ C_G)
    (hCG_le : ∀ (A : E → K → ℝ), (∀ k, Measurable fun x => A x k) →
      ∀ (s_A : ℝ), 0 ≤ s_A → (∀ k x, ‖x‖ ≤ 1 → |A x k| ≤ s_A) →
      ∀ (c_A : ℝ) (w : K → ℝ),
      ∫ p, (1 + ‖p‖) ^ (n_X + 1)
        ∂((μ.prod (gaussianReal 0 1)).tilted fun p => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2)) ≤
        C_G * (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2)) ^
          (n_X + 1))
    {δ v : ℝ} (hδ : 0 < δ) (hv1 : δ ≤ v) (hv2 : δ ≤ 1 - v) (hv₀ : v ∈ Ioo (0 : ℝ) 1)
    (w : K → ℝ) :
    let s_Y := ∑ k, |Y k|
    let L_sum := |L_X| + s_Y + |c_ξ|
    let s_A := |L_X| * 2 ^ n_X + s_Y
    let W_const := 1 + |u 0| + D₁ * |c_ξ| + 1 / 2 + D₁ * s_A
    let S (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν := (μ.prod (gaussianReal 0 1)).tilted fun p => E₀ p.1 + u (S p)
    |∫ p : E × ℝ, ((X p.1 ⬝ᵥ w) / (2 * Real.sqrt v) -
        (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v))) * deriv u (S p) ∂ν| ≤
      ((D₁ / (2 * Real.sqrt δ)) * L_sum * C_G * W_const ^ (n_X + 1) * (3 / 2 : ℝ) ^ (n_X + 1)) *
        (1 + ∑ k, |w k|) ^ (n_X + 2) * (1 + B₀ + c₀) ^ (n_X + 1) := by
  intro s_Y L_sum s_A W_const S ν
  have hc₀ : 0 ≤ c₀ := nonneg_of_confining_of_neg_le hE₀_conf hE₀_low
  have hum : Measurable u := hu.continuous.measurable
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0)
  have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsA0 : 0 ≤ s_A := by positivity
  set A_v : E → K → ℝ := fun x k => Real.sqrt v * X x k + Real.sqrt (1 - v) * Y k
  set c_v : ℝ := Real.sqrt (1 - v) * c_ξ
  have hS_Av : ∀ p : E × ℝ, S p = A_v p.1 ⬝ᵥ w + c_v * p.2 := fun p => by
    dsimp only [S, A_v, c_v, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]; ring
  have hAv_low : ∀ k x, ‖x‖ ≤ 1 → |A_v x k| ≤ s_A := fun k x hx => by
    have hs1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv₀.2.le
    have hs2 : Real.sqrt (1 - v) ≤ 1 := Real.sqrt_le_one.2 (by linarith [hv₀.1])
    have hX1 : |X x k| ≤ |L_X| * 2 ^ n_X := (hXb k x).trans
      (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (by positivity) (abs_nonneg _))
    have hY1 : |Y k| ≤ s_Y := Finset.single_le_sum (f := fun j => |Y j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    calc |A_v x k| ≤ Real.sqrt v * |X x k| + Real.sqrt (1 - v) * |Y k| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ 1 * (|L_X| * 2 ^ n_X) + 1 * s_Y := add_le_add
          (mul_le_mul hs1 hX1 (abs_nonneg _) zero_le_one)
          (mul_le_mul hs2 hY1 (abs_nonneg _) zero_le_one)
      _ = s_A := by dsimp only [s_A]; ring
  have hSm : Measurable S := (measurable_sqrt_field X Y hXm c_ξ v).comp measurable_prodMk_left
  have hν_pow_int : Integrable (fun p : E × ℝ => (1 + ‖p‖) ^ (n_X + 1)) ν :=
    integrable_one_add_norm_pow_tilted_prod_base μ hκ hB₀ hE₀m hE₀_conf (hum.comp hSm)
      (fun _ => hu0 _) _
  have hmom_v : ∫ p : E × ℝ, (1 + ‖p‖) ^ (n_X + 1) ∂ν ≤
      C_G * W_const ^ (n_X + 1) * (1 + ∑ k, |w k|) ^ (n_X + 1) *
        (3 / 2 : ℝ) ^ (n_X + 1) * (1 + B₀ + c₀) ^ (n_X + 1) := by
    have h := hCG_le A_v (fun k => ((hXm k).const_mul _).add measurable_const) s_A hsA0 hAv_low
      c_v w
    have hν_eq : (μ.prod (gaussianReal 0 1)).tilted
        (fun p => E₀ p.1 + u (A_v p.1 ⬝ᵥ w + c_v * p.2)) = ν := by
      dsimp only [ν]; simp_rw [hS_Av]
    rw [hν_eq] at h
    have hw0 : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hcv : |c_v| ≤ |c_ξ| := by
      dsimp only [c_v]; rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.sqrt_le_one.2 (by linarith [hv₀.1]))
    have harg : 1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * ∑ k, |w k| + |c_v|)) + 1 / 2) ≤
        W_const * (1 + ∑ k, |w k|) * (1 + B₀ + c₀ + 1 / 2) := by
      have h1w : 1 ≤ 1 + ∑ k, |w k| := by linarith
      have h2b : 1 ≤ 1 + B₀ + c₀ + 1 / 2 := by linarith
      rw [abs_of_nonneg hD₁0]
      set X_w : ℝ := |u 0| + D₁ * |c_ξ| + D₁ * s_A * ∑ k, |w k| with hX_w
      have hX0 : 0 ≤ X_w := by positivity
      have hW : 1 + X_w ≤ W_const * (1 + ∑ k, |w k|) := by
        have hW1 : 1 + |u 0| + D₁ * |c_ξ| ≤ W_const := by
          dsimp only [W_const]; linarith [mul_nonneg hD₁0 hsA0]
        have hW2 : D₁ * s_A ≤ W_const := by
          dsimp only [W_const]
          linarith [abs_nonneg (u 0), mul_nonneg hD₁0 (abs_nonneg c_ξ)]
        rw [mul_add, mul_one, hX_w]
        linarith [mul_le_mul_of_nonneg_right hW2 hw0]
      calc 1 + B₀ + (c₀ + (|u 0| + D₁ * (s_A * ∑ k, |w k| + |c_v|)) + 1 / 2)
          ≤ (1 + B₀ + c₀ + 1 / 2) + X_w := by
            rw [hX_w, mul_add, ← mul_assoc]
            linarith [mul_le_mul_of_nonneg_left hcv hD₁0]
        _ ≤ (1 + X_w) * (1 + B₀ + c₀ + 1 / 2) := by
            rw [add_mul, one_mul]
            exact add_le_add le_rfl (le_mul_of_one_le_right hX0 h2b)
        _ ≤ W_const * (1 + ∑ k, |w k|) * (1 + B₀ + c₀ + 1 / 2) :=
            mul_le_mul_of_nonneg_right hW (zero_le_one.trans h2b)
    have hpow := pow_le_pow_left₀ (by positivity) harg (n_X + 1)
    refine h.trans ((mul_le_mul_of_nonneg_left hpow hCG0).trans ?_)
    rw [mul_pow, mul_pow]
    calc C_G * (W_const ^ (n_X + 1) * (1 + ∑ k, |w k|) ^ (n_X + 1) *
          (1 + B₀ + c₀ + 1 / 2) ^ (n_X + 1))
        ≤ C_G * (W_const ^ (n_X + 1) * (1 + ∑ k, |w k|) ^ (n_X + 1) *
            ((3 / 2 : ℝ) ^ (n_X + 1) * (1 + B₀ + c₀) ^ (n_X + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (half_add_pow_le hB₀ hc₀ (n_X + 1)) (by positivity)) hCG0
      _ = C_G * W_const ^ (n_X + 1) * (1 + ∑ k, |w k|) ^ (n_X + 1) *
          (3 / 2 : ℝ) ^ (n_X + 1) * (1 + B₀ + c₀) ^ (n_X + 1) := by ring
  have hpt_bd : ∀ p : E × ℝ, |((X p.1 ⬝ᵥ w) / (2 * Real.sqrt v) -
        (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v))) * deriv u (S p)| ≤
      (D₁ / (2 * Real.sqrt δ)) * L_sum * (1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) := fun p => by
    have hs1 : |2 * Real.sqrt v|⁻¹ ≤ (2 * Real.sqrt δ)⁻¹ := by
      have hpos : 0 < 2 * Real.sqrt v := mul_pos zero_lt_two (Real.sqrt_pos.2 hv₀.1)
      have hposδ : 0 < 2 * Real.sqrt δ := mul_pos zero_lt_two (Real.sqrt_pos.2 hδ)
      rw [abs_of_pos hpos]
      exact inv_anti₀ hposδ (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv1) zero_le_two)
    have hs2 : |2 * Real.sqrt (1 - v)|⁻¹ ≤ (2 * Real.sqrt δ)⁻¹ := by
      have hpos : 0 < 2 * Real.sqrt (1 - v) :=
        mul_pos zero_lt_two (Real.sqrt_pos.2 (sub_pos.2 hv₀.2))
      have hposδ : 0 < 2 * Real.sqrt δ := mul_pos zero_lt_two (Real.sqrt_pos.2 hδ)
      rw [abs_of_pos hpos]
      exact inv_anti₀ hposδ (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv2) zero_le_two)
    have hsub : |X p.1 ⬝ᵥ w / (2 * Real.sqrt v) -
        (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v))| ≤
        (2 * Real.sqrt δ)⁻¹ * (L_sum * (1 + ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1)) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_div, div_eq_inv_mul, div_eq_inv_mul]
      refine (add_le_add (mul_le_mul_of_nonneg_right hs1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hs2 (abs_nonneg _))).trans ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_linear_field_sum_le hXb Y c_ξ w p) (by positivity)
    rw [abs_mul]
    refine (mul_le_mul hsub (hD₁ _) (abs_nonneg _) (by positivity)).trans_eq ?_
    rw [div_eq_mul_inv]; ring
  have hXdot_m : Measurable fun p : E × ℝ => X p.1 ⬝ᵥ w :=
    Finset.measurable_sum _ fun k _ => ((hXm k).comp measurable_fst).mul measurable_const
  have hYξ_m : Measurable fun p : E × ℝ => Y ⬝ᵥ w + c_ξ * p.2 :=
    measurable_const.add (measurable_snd.const_mul c_ξ)
  have hint_d : Integrable (fun p : E × ℝ => ((X p.1 ⬝ᵥ w) / (2 * Real.sqrt v) -
      (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v))) * deriv u (S p)) ν :=
    (hν_pow_int.const_mul ((D₁ / (2 * Real.sqrt δ)) * L_sum * (1 + ∑ k, |w k|))).mono'
      (((hXdot_m.div_const _).sub (hYξ_m.div_const _)).mul
        ((measurable_deriv u).comp hSm)).aestronglyMeasurable
      (ae_of_all _ fun p => (Real.norm_eq_abs _).trans_le (hpt_bd p))
  have hint_abs := (norm_integral_le_integral_norm _).trans (integral_mono hint_d.norm
    (hν_pow_int.const_mul ((D₁ / (2 * Real.sqrt δ)) * L_sum * (1 + ∑ k, |w k|)))
    fun p => (Real.norm_eq_abs _).trans_le (hpt_bd p))
  rw [integral_const_mul] at hint_abs
  refine hint_abs.trans ((mul_le_mul_of_nonneg_left hmom_v (by positivity)).trans_eq ?_)
  rw [pow_succ _ (n_X + 1)]; ring

private lemma stein_single_replica_sqrt_log_deriv
    {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype K]
    {κ B₀ c₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2) (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (horth : ∀ x, X x ⬝ᵥ Y = 0) (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hu₂ : Differentiable ℝ (deriv u)) (hu0 : ∀ x, u x ≤ 0) {D₁ D₂ : ℝ}
    (hD₁ : ∀ x, |deriv u x| ≤ D₁) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v₀ * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v₀) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S w p))
    ∫ w, ∫ p : E × ℝ,
        ((X p.1 ⬝ᵥ w) / (2 * Real.sqrt v₀) - (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v₀))) *
          deriv u (S w p) ∂(ν w) ∂γ_sh =
      (1 / 2) * (
        (∫ w, ∫ p : E × ℝ,
          (X p.1 ⬝ᵥ X p.1 - (Y ⬝ᵥ Y + c_ξ ^ 2)) *
            (deriv (deriv u) (S w p) + deriv u (S w p) ^ 2) ∂(ν w) ∂γ_sh) -
        (∫ w, ∫ σ : Fin 2 → E × ℝ,
          (X (σ 0).1 ⬝ᵥ X (σ 1).1 - Y ⬝ᵥ Y) * deriv u (S w (σ 0)) * deriv u (S w (σ 1))
          ∂(Measure.pi fun _ : Fin 2 => ν w) ∂γ_sh)) := by
  intro γ_sh S ν
  set s_Y : ℝ := ∑ k : K, |Y k|
  have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set A_v : E → K → ℝ := fun x k => Real.sqrt v₀ * X x k + Real.sqrt (1 - v₀) * Y k
  set B_v : E → K → ℝ := fun x k =>
    (1 / (2 * Real.sqrt v₀)) * X x k - (1 / (2 * Real.sqrt (1 - v₀))) * Y k
  set c_A : ℝ := Real.sqrt (1 - v₀) * c_ξ
  set c_B : ℝ := -(1 / (2 * Real.sqrt (1 - v₀))) * c_ξ
  have hS : ∀ (w : K → ℝ) (p : E × ℝ), S w p = A_v p.1 ⬝ᵥ w + c_A * p.2 := fun w p => by
    dsimp only [S, A_v, c_A, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]; ring
  have hW : ∀ (w : K → ℝ) (p : E × ℝ), (X p.1 ⬝ᵥ w) / (2 * Real.sqrt v₀) -
      (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v₀)) = B_v p.1 ⬝ᵥ w + c_B * p.2 :=
    fun w p => by
      dsimp only [B_v, c_B, dotProduct]
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]; ring
  have hBA_off : ∀ x y : E, B_v x ⬝ᵥ A_v y = (1 / 2) * (X x ⬝ᵥ X y - Y ⬝ᵥ Y) := fun x y => by
    have hB : B_v x = (1 / (2 * Real.sqrt v₀)) • X x -
        (1 / (2 * Real.sqrt (1 - v₀))) • Y := rfl
    have hA : A_v y = Real.sqrt v₀ • X y + Real.sqrt (1 - v₀) • Y := rfl
    have hYX : Y ⬝ᵥ X y = 0 := by rw [dotProduct_comm]; exact horth y
    have hs1 : Real.sqrt v₀ ≠ 0 := (Real.sqrt_pos.2 hv₀.1).ne'
    have hs2 : Real.sqrt (1 - v₀) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hv₀.2)).ne'
    simp only [hB, hA, sub_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul,
      smul_eq_mul, horth x, hYX, mul_zero]
    field_simp
    ring
  have hBA_diag : ∀ x : E,
      B_v x ⬝ᵥ A_v x + c_B * c_A = (1 / 2) * (X x ⬝ᵥ X x - (Y ⬝ᵥ Y + c_ξ ^ 2)) := fun x => by
    have hs2 : Real.sqrt (1 - v₀) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hv₀.2)).ne'
    have hc : c_B * c_A = -((1 / 2) * c_ξ ^ 2) := by
      dsimp only [c_B, c_A]; field_simp
    rw [hBA_off x x, hc]; ring
  have hAm : ∀ k, Measurable fun x => A_v x k := fun k => ((hXm k).const_mul _).add measurable_const
  have hBm : ∀ k, Measurable fun x => B_v x k := fun k => ((hXm k).const_mul _).sub measurable_const
  set L_A : ℝ := |L_X| + s_Y
  set L_B : ℝ := |L_X| / (2 * Real.sqrt v₀) + s_Y / (2 * Real.sqrt (1 - v₀))
  have hAb : ∀ k x, |A_v x k| ≤ L_A * (1 + ‖x‖) ^ n_X := fun k x => by
    have hs1 : Real.sqrt v₀ ≤ 1 := Real.sqrt_le_one.2 hv₀.2.le
    have hs2 : Real.sqrt (1 - v₀) ≤ 1 := Real.sqrt_le_one.2 (by linarith [hv₀.1])
    have hY1 : |Y k| ≤ s_Y := Finset.single_le_sum (f := fun j => |Y j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have hn1 : 1 ≤ (1 + ‖x‖) ^ n_X := one_le_pow₀ (by linarith [norm_nonneg x])
    calc |A_v x k| ≤ Real.sqrt v₀ * |X x k| + Real.sqrt (1 - v₀) * |Y k| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ 1 * (|L_X| * (1 + ‖x‖) ^ n_X) + 1 * s_Y := add_le_add
          (mul_le_mul hs1 ((hXb k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (by positivity))) (abs_nonneg _) zero_le_one)
          (mul_le_mul hs2 hY1 (abs_nonneg _) zero_le_one)
      _ ≤ |L_X| * (1 + ‖x‖) ^ n_X + s_Y * (1 + ‖x‖) ^ n_X := by
          rw [one_mul, one_mul]; exact add_le_add le_rfl (le_mul_of_one_le_right hsY0 hn1)
      _ = L_A * (1 + ‖x‖) ^ n_X := by dsimp only [L_A]; ring
  have hBb : ∀ k x, |B_v x k| ≤ L_B * (1 + ‖x‖) ^ n_X := fun k x => by
    have hY1 : |Y k| ≤ s_Y := Finset.single_le_sum (f := fun j => |Y j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have hn1 : 1 ≤ (1 + ‖x‖) ^ n_X := one_le_pow₀ (by linarith [norm_nonneg x])
    calc |B_v x k| ≤ (1 / (2 * Real.sqrt v₀)) * |X x k| +
          (1 / (2 * Real.sqrt (1 - v₀))) * |Y k| := by
          refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
            rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 / (2 * Real.sqrt v₀)) * (|L_X| * (1 + ‖x‖) ^ n_X) +
          (1 / (2 * Real.sqrt (1 - v₀))) * s_Y := add_le_add
          (mul_le_mul_of_nonneg_left ((hXb k x).trans (mul_le_mul_of_nonneg_right
            (le_abs_self _) (by positivity))) (by positivity))
          (mul_le_mul_of_nonneg_left hY1 (by positivity))
      _ ≤ (|L_X| / (2 * Real.sqrt v₀)) * (1 + ‖x‖) ^ n_X +
          (s_Y / (2 * Real.sqrt (1 - v₀))) * (1 + ‖x‖) ^ n_X := by
          refine add_le_add (le_of_eq (by ring)) ?_
          rw [one_div_mul_eq_div]
          exact le_mul_of_one_le_right (by positivity) hn1
      _ = L_B * (1 + ‖x‖) ^ n_X := by dsimp only [L_B]; ring
  obtain ⟨_, _, _, hst⟩ := stein_pi_tilted_prod_gaussianReal μ (R := Unit) hκ hB₀
    hE₀m hE₀_conf hE₀_low A_v B_v hAm hBm hAb hBb c_A c_B hu hu0 hD₁
    (fun _ => deriv u) (fun _ => hu₂) (M₀ := D₁) (M₁ := D₂)
    (fun _ => hD₁) (fun _ => hD₂) (f := fun _ => (1 : ℝ)) measurable_const
    (C_f := 1) (m_f := 0) (fun _ => by simp) ()
  have hlhs : ∫ w, ∫ p : E × ℝ,
      ((X p.1 ⬝ᵥ w) / (2 * Real.sqrt v₀) - (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v₀))) *
        deriv u (S w p) ∂(ν w) ∂γ_sh =
      ∫ w, ∫ σ : Unit → E × ℝ, (1 : ℝ) * (B_v (σ ()).1 ⬝ᵥ w + c_B * (σ ()).2) *
        ∏ r : Unit, deriv u (A_v (σ r).1 ⬝ᵥ w + c_A * (σ r).2)
      ∂(Measure.pi fun _ : Unit => (μ.prod (gaussianReal 0 1)).tilted fun p =>
        E₀ p.1 + u (A_v p.1 ⬝ᵥ w + c_A * p.2)) ∂γ_sh := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    have heq_ν : ((μ.prod (gaussianReal 0 1)).tilted fun p =>
        E₀ p.1 + u (A_v p.1 ⬝ᵥ w + c_A * p.2)) = ν w := by dsimp only [ν]; simp_rw [hS]
    have huniq := (measurePreserving_funUnique (ν w) Unit).integral_comp
      (MeasurableEquiv.funUnique Unit (E × ℝ)).measurableEmbedding
      (fun p : E × ℝ => (B_v p.1 ⬝ᵥ w + c_B * p.2) * deriv u (A_v p.1 ⬝ᵥ w + c_A * p.2))
    dsimp only
    rw [heq_ν]; simp_rw [hW, hS]
    convert huniq.symm using 2
    simp only [Fintype.prod_unique, one_mul, MeasurableEquiv.funUnique_apply]
  have hrhs1 : (∑ j : Unit, ∫ w, ∫ σ : Unit → E × ℝ,
        (1 : ℝ) * (B_v (σ ()).1 ⬝ᵥ A_v (σ j).1 + if j = () then c_B * c_A else 0) *
          ((deriv (deriv u) (A_v (σ j).1 ⬝ᵥ w + c_A * (σ j).2) +
              deriv u (A_v (σ j).1 ⬝ᵥ w + c_A * (σ j).2) *
                deriv u (A_v (σ j).1 ⬝ᵥ w + c_A * (σ j).2)) *
            ∏ r ∈ Finset.univ.erase j, deriv u (A_v (σ r).1 ⬝ᵥ w + c_A * (σ r).2))
        ∂(Measure.pi fun _ : Unit => (μ.prod (gaussianReal 0 1)).tilted fun p =>
          E₀ p.1 + u (A_v p.1 ⬝ᵥ w + c_A * p.2)) ∂γ_sh) =
      (1 / 2) * ∫ w, ∫ p : E × ℝ, (X p.1 ⬝ᵥ X p.1 - (Y ⬝ᵥ Y + c_ξ ^ 2)) *
        (deriv (deriv u) (S w p) + deriv u (S w p) ^ 2) ∂(ν w) ∂γ_sh := by
    simp only [Finset.univ_unique, Finset.sum_singleton, ↓reduceIte, Finset.erase_singleton,
      Finset.prod_empty, mul_one, one_mul, ← sq]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    have heq_ν : ((μ.prod (gaussianReal 0 1)).tilted fun p =>
        E₀ p.1 + u (A_v p.1 ⬝ᵥ w + c_A * p.2)) = ν w := by dsimp only [ν]; simp_rw [hS]
    dsimp only
    rw [heq_ν, ← integral_const_mul]
    have huniq := (measurePreserving_funUnique (ν w) Unit).integral_comp
      (MeasurableEquiv.funUnique Unit (E × ℝ)).measurableEmbedding
      (fun p : E × ℝ => (B_v p.1 ⬝ᵥ A_v p.1 + c_B * c_A) *
        (deriv (deriv u) (A_v p.1 ⬝ᵥ w + c_A * p.2) + deriv u (A_v p.1 ⬝ᵥ w + c_A * p.2) ^ 2))
    refine (integral_congr_ae (ae_of_all _ fun σ => ?_)).trans
      (huniq.trans (integral_congr_ae (ae_of_all _ fun p => ?_)))
    · rfl
    · dsimp only
      rw [hBA_diag, hS]; ring
  have hrhs2 : (Fintype.card Unit : ℝ) * ∫ w, ∫ σ : Option Unit → E × ℝ,
        (1 : ℝ) * (B_v (σ (some ())).1 ⬝ᵥ A_v (σ none).1) *
          (∏ r : Unit, deriv u (A_v (σ (some r)).1 ⬝ᵥ w + c_A * (σ (some r)).2)) *
          deriv u (A_v (σ none).1 ⬝ᵥ w + c_A * (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ.prod (gaussianReal 0 1)).tilted fun p =>
          E₀ p.1 + u (A_v p.1 ⬝ᵥ w + c_A * p.2)) ∂γ_sh =
      (1 / 2) * ∫ w, ∫ σ : Fin 2 → E × ℝ,
        (X (σ 0).1 ⬝ᵥ X (σ 1).1 - Y ⬝ᵥ Y) * deriv u (S w (σ 0)) * deriv u (S w (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ν w) ∂γ_sh := by
    simp only [Fintype.card_unit, Nat.cast_one, one_mul, Fintype.prod_unique]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    have heq_ν : ((μ.prod (gaussianReal 0 1)).tilted fun p =>
        E₀ p.1 + u (A_v p.1 ⬝ᵥ w + c_A * p.2)) = ν w := by dsimp only [ν]; simp_rw [hS]
    dsimp only
    rw [heq_ν, ← integral_const_mul]
    -- relabel `some ()` and `none` as the replicas `0` and `1`
    set e : Fin 2 ≃ Option Unit :=
      finSuccEquivLast.trans (Equiv.optionCongr (Equiv.ofUnique (Fin 1) Unit)) with he
    have hmp := measurePreserving_piCongrLeft (fun _ : Option Unit => ν w) e
    refine (hmp.integral_comp' _).symm.trans (integral_congr_ae (ae_of_all _ fun σ => ?_))
    have h0 : MeasurableEquiv.piCongrLeft (fun _ : Option Unit => E × ℝ) e σ (some ()) = σ 0 := by
      rw [show (some () : Option Unit) = e 0 from rfl]
      exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Option Unit => E × ℝ) e σ 0
    have h1 : MeasurableEquiv.piCongrLeft (fun _ : Option Unit => E × ℝ) e σ none = σ 1 := by
      rw [show (none : Option Unit) = e 1 from rfl]
      exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Option Unit => E × ℝ) e σ 1
    simp only [h0, h1, hBA_off, hS]; ring
  rw [← hlhs, hrhs1, hrhs2] at hst
  linarith

private lemma abs_dotProduct_X_le {E K : Type*} [NormedAddCommGroup E] [Fintype K]
    {X : E → K → ℝ} {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (p q : E × ℝ) :
    |X p.1 ⬝ᵥ X q.1| ≤ (Fintype.card K : ℝ) * L_X ^ 2 * ((1 + ‖p‖) ^ n_X * (1 + ‖q‖) ^ n_X) := by
  refine (Finset.abs_sum_le_sum_abs (fun k => X p.1 k * X q.1 k) _).trans
    ((Finset.sum_le_card_nsmul _ _ (L_X ^ 2 * ((1 + ‖p‖) ^ n_X * (1 + ‖q‖) ^ n_X))
      fun k _ => ?_).trans_eq (by rw [Finset.card_univ, nsmul_eq_mul]; ring))
  have hk1 : |X p.1 k| ≤ |L_X| * (1 + ‖p‖) ^ n_X := (hXb k p.1).trans
    (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by positivity)
      (by linarith [norm_fst_le p]) _) (by positivity) (abs_nonneg _))
  have hk2 : |X q.1 k| ≤ |L_X| * (1 + ‖q‖) ^ n_X := (hXb k q.1).trans
    (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by positivity)
      (by linarith [norm_fst_le q]) _) (by positivity) (abs_nonneg _))
  rw [abs_mul]
  refine (mul_le_mul hk1 hk2 (abs_nonneg _) (by positivity)).trans_eq ?_
  rw [← sq_abs L_X]; ring

private lemma integrable_stein_sqrt_log_terms
    {Ω E K : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype K]
    {P₀ : Measure Ω}
    {κ : ℝ} (hκ : 0 < κ) {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω) (hc₀ : ∀ ω, 0 ≤ c₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ D₂ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v₀ * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v₀) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (ω : Ω) (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ ω p.1 + u (S w p))
    Integrable (fun ω => ∫ w, ∫ p : E × ℝ,
        (X p.1 ⬝ᵥ X p.1 - (Y ⬝ᵥ Y + c_ξ ^ 2)) *
          (deriv (deriv u) (S w p) + deriv u (S w p) ^ 2) ∂(ν ω w) ∂γ_sh) P₀ ∧
      Integrable (fun ω => ∫ w, ∫ σ : Fin 2 → E × ℝ,
        (X (σ 0).1 ⬝ᵥ X (σ 1).1 - Y ⬝ᵥ Y) * deriv u (S w (σ 0)) * deriv u (S w (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ν ω w) ∂γ_sh) P₀ := by
  intro γ_sh S ν
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0)
  have hD₂0 : 0 ≤ D₂ := (abs_nonneg _).trans (hD₂ 0)
  have hSm := measurable_sqrt_field X Y hXm c_ξ v₀
  constructor
  · obtain ⟨_, _, hJ⟩ := measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal (E := E)
      (K := K) (ι := Unit) μ P₀ hκ hB₀ hc₀ hmom hE₀m hE₀_conf hE₀_low X Y hXm hXb c_ξ
      hu hu0 hD₁ (2 * n_X)
    let G₁ (w : K → ℝ) (σ : Unit → E × ℝ) : ℝ :=
      (X (σ ()).1 ⬝ᵥ X (σ ()).1 - (Y ⬝ᵥ Y + c_ξ ^ 2)) *
        (deriv (deriv u) (S w (σ ())) + deriv u (S w (σ ())) ^ 2)
    have hGm : Measurable fun q : (K → ℝ) × (Unit → E × ℝ) => G₁ q.1 q.2 := by
      have hX2 : Measurable fun σ : Unit → E × ℝ => X (σ ()).1 ⬝ᵥ X (σ ()).1 :=
        Finset.measurable_sum _ fun k _ =>
          ((hXm k).comp (measurable_fst.comp (measurable_pi_apply ()))).mul
            ((hXm k).comp (measurable_fst.comp (measurable_pi_apply ())))
      have hS' : Measurable fun q : (K → ℝ) × (Unit → E × ℝ) => S q.1 (q.2 ()) :=
        hSm.comp (measurable_fst.prodMk ((measurable_pi_apply ()).comp measurable_snd))
      exact ((hX2.comp measurable_snd).sub measurable_const).mul
        (((measurable_deriv (deriv u)).comp hS').add (((measurable_deriv u).comp hS').pow_const 2))
    set B_d := (∑ k : K, |Y k| ^ 2 + c_ξ ^ 2 + (Fintype.card K : ℝ) * L_X ^ 2) * (D₂ + D₁ ^ 2)
    have hGb : ∀ (w : K → ℝ) (σ : Unit → E × ℝ),
        |G₁ w σ| ≤ B_d * ∏ o : Unit, (1 + ‖σ o‖) ^ (2 * n_X) := fun w σ => by
      have hXX : |X (σ ()).1 ⬝ᵥ X (σ ()).1| ≤
          (Fintype.card K : ℝ) * L_X ^ 2 * (1 + ‖σ ()‖) ^ (2 * n_X) :=
        (abs_dotProduct_X_le hXb (σ ()) (σ ())).trans_eq (by rw [← pow_add, ← two_mul])
      have hYY : |Y ⬝ᵥ Y + c_ξ ^ 2| ≤ ∑ k, |Y k| ^ 2 + c_ξ ^ 2 :=
        (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k _ => by rw [abs_mul, ← sq, sq_abs]))
          (le_of_eq (abs_of_nonneg (sq_nonneg _))))
      have h1p : 1 ≤ (1 + ‖σ ()‖) ^ (2 * n_X) := one_le_pow₀ (by linarith [norm_nonneg (σ ())])
      have hCd : |X (σ ()).1 ⬝ᵥ X (σ ()).1 - (Y ⬝ᵥ Y + c_ξ ^ 2)| ≤
          (∑ k, |Y k| ^ 2 + c_ξ ^ 2 + (Fintype.card K : ℝ) * L_X ^ 2) *
            (1 + ‖σ ()‖) ^ (2 * n_X) := by
        refine (abs_sub _ _).trans ((add_le_add hXX hYY).trans ?_)
        have h0 : 0 ≤ ∑ k, |Y k| ^ 2 + c_ξ ^ 2 :=
          add_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg |Y k|) (sq_nonneg c_ξ)
        nlinarith [mul_le_mul_of_nonneg_left h1p h0]
      rw [abs_mul, Fintype.prod_unique]
      refine (mul_le_mul hCd (abs_deriv_deriv_add_sq_deriv_le hD₁ hD₂ _) (abs_nonneg _)
        (by positivity)).trans_eq ?_; dsimp only [B_d]; ring
    obtain ⟨-, -, hInt⟩ := hJ hv₀.1.le hv₀.2.le hGm (by positivity) hGb
    refine hInt.congr (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun w => ?_))
    exact (measurePreserving_funUnique (ν ω w) Unit).integral_comp
      (MeasurableEquiv.funUnique Unit (E × ℝ)).measurableEmbedding
      (fun p : E × ℝ => (X p.1 ⬝ᵥ X p.1 - (Y ⬝ᵥ Y + c_ξ ^ 2)) *
        (deriv (deriv u) (S w p) + deriv u (S w p) ^ 2))
  · obtain ⟨_, _, hJ⟩ := measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal (E := E)
      (K := K) (ι := Fin 2) μ P₀ hκ hB₀ hc₀ hmom hE₀m hE₀_conf hE₀_low X Y hXm hXb c_ξ
      hu hu0 hD₁ n_X
    let G₂ (w : K → ℝ) (σ : Fin 2 → E × ℝ) : ℝ :=
      (X (σ 0).1 ⬝ᵥ X (σ 1).1 - Y ⬝ᵥ Y) * deriv u (S w (σ 0)) * deriv u (S w (σ 1))
    have hGm : Measurable fun q : (K → ℝ) × (Fin 2 → E × ℝ) => G₂ q.1 q.2 := by
      have hX2 : Measurable fun σ : Fin 2 → E × ℝ => X (σ 0).1 ⬝ᵥ X (σ 1).1 :=
        Finset.measurable_sum _ fun k _ =>
          ((hXm k).comp (measurable_fst.comp (measurable_pi_apply (0 : Fin 2)))).mul
            ((hXm k).comp (measurable_fst.comp (measurable_pi_apply (1 : Fin 2))))
      have hS0 : Measurable fun q : (K → ℝ) × (Fin 2 → E × ℝ) => S q.1 (q.2 0) :=
        hSm.comp (measurable_fst.prodMk ((measurable_pi_apply (0 : Fin 2)).comp measurable_snd))
      have hS1 : Measurable fun q : (K → ℝ) × (Fin 2 → E × ℝ) => S q.1 (q.2 1) :=
        hSm.comp (measurable_fst.prodMk ((measurable_pi_apply (1 : Fin 2)).comp measurable_snd))
      exact (((hX2.comp measurable_snd).sub measurable_const).mul
        ((measurable_deriv u).comp hS0)).mul ((measurable_deriv u).comp hS1)
    set B_o := (∑ k : K, |Y k| ^ 2 + (Fintype.card K : ℝ) * L_X ^ 2) * D₁ ^ 2
    have hGb : ∀ (w : K → ℝ) (σ : Fin 2 → E × ℝ),
        |G₂ w σ| ≤ B_o * ∏ o : Fin 2, (1 + ‖σ o‖) ^ n_X := fun w σ => by
      have hXX := abs_dotProduct_X_le hXb (σ 0) (σ 1)
      have hYY : |Y ⬝ᵥ Y| ≤ ∑ k, |Y k| ^ 2 := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => by rw [abs_mul, ← sq, sq_abs])
      have h1p : 1 ≤ (1 + ‖σ 0‖) ^ n_X * (1 + ‖σ 1‖) ^ n_X :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg (σ 0)]))
          (one_le_pow₀ (by linarith [norm_nonneg (σ 1)]))
      have hCo : |X (σ 0).1 ⬝ᵥ X (σ 1).1 - Y ⬝ᵥ Y| ≤
          (∑ k, |Y k| ^ 2 + (Fintype.card K : ℝ) * L_X ^ 2) *
            ((1 + ‖σ 0‖) ^ n_X * (1 + ‖σ 1‖) ^ n_X) := by
        refine (abs_sub _ _).trans ((add_le_add hXX hYY).trans ?_)
        have h0 : 0 ≤ ∑ k, |Y k| ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg |Y k|
        nlinarith [mul_le_mul_of_nonneg_left h1p h0]
      have hdu : |deriv u (S w (σ 0)) * deriv u (S w (σ 1))| ≤ D₁ ^ 2 := by
        rw [abs_mul]; exact (mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) hD₁0).trans_eq (sq _).symm
      dsimp only [G₂]; rw [mul_assoc, abs_mul, Fin.prod_univ_two]
      refine (mul_le_mul hCo hdu (abs_nonneg _) (by positivity)).trans_eq ?_
      dsimp only [B_o]; ring
    exact (hJ hv₀.1.le hv₀.2.le hGm (by positivity) hGb).2.2

/-- Along the square-root path the log-partition function is measurable in the disorder, and
bounded on `v ∈ [0, 1]` by one integrable function. -/
private lemma exists_integrable_bound_log_integral_exp_sqrt_path
    {Ω E K : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype K]
    {P₀ : Measure Ω}
    {κ : ℝ} (hκ : 0 < κ) {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁) :
    (∀ v : ℝ, Measurable fun q : Ω × (K → ℝ) => Real.log (∫ p : E × ℝ,
        Real.exp (u (Real.sqrt v * (X p.1 ⬝ᵥ q.2) + Real.sqrt (1 - v) * (Y ⬝ᵥ q.2 + c_ξ * p.2)))
        ∂((μ.tilted (E₀ q.1)).prod (gaussianReal 0 1)))) ∧
      ∃ b : Ω × (K → ℝ) → ℝ, Integrable b (P₀.prod (Measure.pi fun _ : K => gaussianReal 0 1)) ∧
        ∀ v ∈ Icc (0 : ℝ) 1, ∀ q : Ω × (K → ℝ), |Real.log (∫ p : E × ℝ,
          Real.exp (u (Real.sqrt v * (X p.1 ⬝ᵥ q.2) +
            Real.sqrt (1 - v) * (Y ⬝ᵥ q.2 + c_ξ * p.2)))
          ∂((μ.tilted (E₀ q.1)).prod (gaussianReal 0 1)))| ≤ b q := by
  set γ_sh := Measure.pi fun _ : K => gaussianReal 0 1 with hγ
  set S : ℝ → (K → ℝ) → E × ℝ → ℝ := fun v w p =>
    Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2) with hSdef
  set G₀ : Ω → Measure E := fun ω => μ.tilted (E₀ ω) with hG₀
  have hum : Measurable u := hu.continuous.measurable
  have huc : Continuous u := hu.continuous
  have hc₀ : ∀ ω, 0 ≤ c₀ ω := fun ω => nonneg_of_confining_of_neg_le (hE₀_conf ω) (hE₀_low ω)
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0)
  have hEω_m : ∀ ω, Measurable (E₀ ω) := fun ω =>
    hE₀m.comp (measurable_const.prodMk measurable_id)
  have hEi : ∀ ω, Integrable (fun x => Real.exp (E₀ ω x)) μ := fun ω =>
    integrable_exp_of_confining (μ := μ) hκ (hEω_m ω) (A := 0) (B := B₀ ω) fun x => by
      simpa only [zero_add] using hE₀_conf ω x
  have hG₀_prob : ∀ ω, IsProbabilityMeasure (G₀ ω) := fun ω => isProbabilityMeasure_tilted (hEi ω)
  have hPhi_m : ∀ v : ℝ, Measurable fun q : Ω × (K → ℝ) =>
      Real.log (∫ p : E × ℝ, Real.exp (u (S v q.2 p)) ∂((G₀ q.1).prod (gaussianReal 0 1))) :=
    fun v => by
      simp only [G₀, ← tilted_prod_comp_fst]
      refine Real.measurable_log.comp (measurable_integral_tilted_dep
        (e := fun (q : Ω × (K → ℝ)) (p : E × ℝ) => E₀ q.1 p.1)
        (Y := fun (q : Ω × (K → ℝ)) (p : E × ℝ) => Real.exp (u (S v q.2 p)))
        (hE₀m.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd)))
        ((hum.comp ((measurable_sqrt_field X Y hXm c_ξ v).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).exp))
  obtain ⟨C_G, hCG0, hCG_le⟩ :=
    exists_integral_one_add_norm_pow_tilted_prod_gaussian_le (K := K) μ hκ (n_X + 1)
  have hG0_mom : ∀ ω, ∫ p : E × ℝ, (1 + ‖p‖) ^ (n_X + 1) ∂((G₀ ω).prod (gaussianReal 0 1)) ≤
      C_G * (1 + B₀ ω + c₀ ω + 1 / 2) ^ (n_X + 1) := fun ω => by
    have h := hCG_le (E₀ ω) (hEω_m ω) (B₀ ω) (c₀ ω) (hB₀ ω) (hE₀_conf ω) (hE₀_low ω)
      (fun _ _ => 0) (fun _ => measurable_const) 0 le_rfl (fun _ _ _ => by simp)
      0 (fun _ => 0) 0 (differentiable_const 0) (fun _ => le_rfl) (fun _ => by simp) 0
    have heq1 : ((μ.prod (gaussianReal 0 1)).tilted fun p : E × ℝ => E₀ ω p.1 + (0 : ℝ)) =
        (G₀ ω).prod (gaussianReal 0 1) := by
      simp only [add_zero]; exact tilted_prod_comp_fst μ (gaussianReal 0 1) (E₀ ω)
    rw [← heq1]; simpa only [abs_zero, zero_mul, add_zero, zero_add, add_assoc] using h
  set s_Y : ℝ := ∑ k : K, |Y k|
  set L_sum : ℝ := |L_X| + s_Y + |c_ξ|
  set C_Phi : ℝ := (|u 0| + D₁ * L_sum) * C_G * (3 / 2 : ℝ) ^ (n_X + 1)
  set b_Phi : Ω × (K → ℝ) → ℝ := fun q =>
    C_Phi * (1 + ∑ k, |q.2 k|) * (1 + B₀ q.1 + c₀ q.1) ^ (n_X + 1)
  have hbPhi_int : Integrable b_Phi (P₀.prod γ_sh) :=
    ((hmom (n_X + 1)).const_mul C_Phi |>.mul_prod
      (integrable_const_add_mul_sum_abs_pow_pi_gaussianReal 1 1 1)).congr
      (ae_of_all _ fun q => by simp only [one_mul, pow_one, b_Phi]; ring)
  let Phi (v : ℝ) (ω : Ω) (w : K → ℝ) : ℝ :=
    Real.log (∫ p : E × ℝ, Real.exp (u (S v w p)) ∂((G₀ ω).prod (gaussianReal 0 1)))
  have hPhi_bd : ∀ v ∈ Icc (0 : ℝ) 1, ∀ ω w, |Phi v ω w| ≤ b_Phi (ω, w) :=
    fun v hv ω w => abs_log_integral_exp_sqrt_path_le μ hκ (hB₀ ω) (hEω_m ω) (hE₀_conf ω)
      (hE₀_low ω) X Y hXm hXb c_ξ hu hu0 hD₁ (hG0_mom ω) hv w
  exact ⟨hPhi_m, b_Phi, hbPhi_int, fun v hv q => hPhi_bd v hv q.1 q.2⟩

/-- **Continuity on `[0, 1]` of the disorder-averaged log-partition function** along a
square-root cavity path under quadratic confinement. No orthogonality between `X` and `Y` and no
second derivative of `u` is needed. -/
theorem continuousOn_integral_log_integral_exp_tilted_prod_gaussianReal_sqrt
    {Ω E K : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype K]
    {P₀ : Measure Ω} [SFinite P₀]
    {κ : ℝ} (hκ : 0 < κ) {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁) :
    ContinuousOn (fun v : ℝ => ∫ ω, ∫ w : K → ℝ, Real.log (∫ p : E × ℝ,
        Real.exp (u (Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)))
        ∂((μ.tilted (E₀ ω)).prod (gaussianReal 0 1)))
        ∂(Measure.pi fun _ : K => gaussianReal 0 1) ∂P₀) (Icc 0 1) := by
  set γ_sh := Measure.pi fun _ : K => gaussianReal 0 1 with hγ
  set S : ℝ → (K → ℝ) → E × ℝ → ℝ := fun v w p =>
    Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2) with hSdef
  set G₀ : Ω → Measure E := fun ω => μ.tilted (E₀ ω) with hG₀
  have hum : Measurable u := hu.continuous.measurable
  have huc : Continuous u := hu.continuous
  have hEi : ∀ ω, Integrable (fun x => Real.exp (E₀ ω x)) μ := fun ω =>
    integrable_exp_of_confining (μ := μ) hκ (hE₀m.comp (measurable_const.prodMk measurable_id))
      (A := 0) (B := B₀ ω) fun x => by simpa only [zero_add] using hE₀_conf ω x
  have hG₀_prob : ∀ ω, IsProbabilityMeasure (G₀ ω) := fun ω => isProbabilityMeasure_tilted (hEi ω)
  obtain ⟨hPhi_m, b_Phi, hbPhi_int, hPhi_bd⟩ :=
    exists_integrable_bound_log_integral_exp_sqrt_path μ hκ hB₀ hmom hE₀m hE₀_conf hE₀_low X Y
      hXm hXb c_ξ hu hu0 hD₁
  let Phi (v : ℝ) (ω : Ω) (w : K → ℝ) : ℝ :=
    Real.log (∫ p : E × ℝ, Real.exp (u (S v w p)) ∂((G₀ ω).prod (gaussianReal 0 1)))
  have hPhi_int : ∀ v ∈ Icc (0 : ℝ) 1,
      Integrable (fun q : Ω × (K → ℝ) => Phi v q.1 q.2) (P₀.prod γ_sh) := fun v hv =>
    hbPhi_int.mono' (hPhi_m v).aestronglyMeasurable (ae_of_all _ fun q =>
      (Real.norm_eq_abs _).trans_le (hPhi_bd v hv q))
  change ContinuousOn (fun v => ∫ ω, ∫ w, Phi v ω w ∂γ_sh ∂P₀) (Icc 0 1)
  have heq : EqOn (fun v => ∫ ω, ∫ w, Phi v ω w ∂γ_sh ∂P₀)
      (fun v => ∫ q : Ω × (K → ℝ), Phi v q.1 q.2 ∂(P₀.prod γ_sh)) (Icc 0 1) :=
    fun v hv => (integral_prod (fun q => Phi v q.1 q.2) (hPhi_int v hv)).symm
  refine (continuousOn_of_dominated (bound := b_Phi)
    (fun v _ => (hPhi_m v).aestronglyMeasurable)
    (fun v hv => ae_of_all _ fun q => (Real.norm_eq_abs _).trans_le (hPhi_bd v hv q))
    hbPhi_int (ae_of_all _ fun q => ?_)).congr heq
  have : IsProbabilityMeasure (G₀ q.1) := hG₀_prob q.1
  refine Continuous.continuousOn (Continuous.log
    (continuous_of_dominated (bound := fun _ => (1 : ℝ))
      (fun v => (hum.comp ((measurable_sqrt_field X Y hXm c_ξ v).comp
        measurable_prodMk_left)).exp.aestronglyMeasurable)
      (fun v => ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.2 (hu0 _))
      (integrable_const 1) (ae_of_all _ fun p => Real.continuous_exp.comp (huc.comp
        ((Real.continuous_sqrt.mul continuous_const).add
          ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).mul
            continuous_const)))))
    (fun v => ne_of_gt (integral_exp_pos_of_ae_le
      (hum.comp ((measurable_sqrt_field X Y hXm c_ξ v).comp
        measurable_prodMk_left)).aemeasurable (ae_of_all _ fun _ => hu0 _))))

/-- **Continuity on `[0, 1]` and derivative-by-parts formula on `(0, 1)` for the disorder-averaged
log-partition function along a square-root cavity path** under quadratic confinement. -/
theorem hasDerivAt_and_continuousOn_log_integral_exp_tilted_prod_gaussianReal_sqrt
    {Ω E K : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype K]
    {P₀ : Measure Ω} [SFinite P₀]
    {κ : ℝ} (hκ : 0 < κ) {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (horth : ∀ x, X x ⬝ᵥ Y = 0)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu₂ : Differentiable ℝ (deriv u))
    (hu0 : ∀ x, u x ≤ 0) {D₁ D₂ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (v : ℝ) (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let G₀ (ω : Ω) : Measure E := μ.tilted (E₀ ω)
    let φ (v : ℝ) : ℝ :=
      ∫ ω, ∫ w, Real.log (∫ p : E × ℝ, Real.exp (u (S v w p))
        ∂((G₀ ω).prod (gaussianReal 0 1))) ∂γ_sh ∂P₀
    let ν (v : ℝ) (ω : Ω) (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ ω p.1 + u (S v w p))
    let C_off (x y : E) : ℝ := X x ⬝ᵥ X y - Y ⬝ᵥ Y
    let C_diag (x : E) : ℝ := X x ⬝ᵥ X x - (Y ⬝ᵥ Y + c_ξ ^ 2)
    ContinuousOn φ (Icc 0 1) ∧
      ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt φ
        ((1 / 2) * (
          (∫ ω, ∫ w, ∫ p : E × ℝ,
            C_diag p.1 * (deriv (deriv u) (S v w p) + deriv u (S v w p) ^ 2)
            ∂(ν v ω w) ∂γ_sh ∂P₀) -
          (∫ ω, ∫ w, ∫ σ : Fin 2 → E × ℝ,
            C_off (σ 0).1 (σ 1).1 * deriv u (S v w (σ 0)) * deriv u (S v w (σ 1))
            ∂(Measure.pi fun _ : Fin 2 => ν v ω w) ∂γ_sh ∂P₀))) v := by
  intro γ_sh S G₀ φ ν C_off C_diag
  have hum : Measurable u := hu.continuous.measurable
  have huc : Continuous u := hu.continuous
  have hc₀ : ∀ ω, 0 ≤ c₀ ω := fun ω => nonneg_of_confining_of_neg_le (hE₀_conf ω) (hE₀_low ω)
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0)
  have hEω_m : ∀ ω, Measurable (E₀ ω) := fun ω =>
    hE₀m.comp (measurable_const.prodMk measurable_id)
  have hEi : ∀ ω, Integrable (fun x => Real.exp (E₀ ω x)) μ := fun ω =>
    integrable_exp_of_confining (μ := μ) hκ (hEω_m ω) (A := 0) (B := B₀ ω) fun x => by
      simpa only [zero_add] using hE₀_conf ω x
  have hG₀_prob : ∀ ω, IsProbabilityMeasure (G₀ ω) := fun ω => isProbabilityMeasure_tilted (hEi ω)
  obtain ⟨C_G, hCG0, hCG_le⟩ :=
    exists_integral_one_add_norm_pow_tilted_prod_gaussian_le (K := K) μ hκ (n_X + 1)
  set s_Y : ℝ := ∑ k : K, |Y k|
  set L_sum : ℝ := |L_X| + s_Y + |c_ξ|
  obtain ⟨hPhi_m, b_Phi, hbPhi_int, hPhi_bd⟩ :=
    exists_integrable_bound_log_integral_exp_sqrt_path μ hκ hB₀ hmom hE₀m hE₀_conf hE₀_low X Y
      hXm hXb c_ξ hu hu0 hD₁
  let Phi (v : ℝ) (ω : Ω) (w : K → ℝ) : ℝ :=
    Real.log (∫ p : E × ℝ, Real.exp (u (S v w p)) ∂((G₀ ω).prod (gaussianReal 0 1)))
  have hPhi_int : ∀ v ∈ Icc (0 : ℝ) 1,
      Integrable (fun q : Ω × (K → ℝ) => Phi v q.1 q.2) (P₀.prod γ_sh) := fun v hv =>
    hbPhi_int.mono' (hPhi_m v).aestronglyMeasurable (ae_of_all _ fun q =>
      (Real.norm_eq_abs _).trans_le (hPhi_bd v hv q))
  have hPhi_cont : ContinuousOn φ (Icc 0 1) :=
    continuousOn_integral_log_integral_exp_tilted_prod_gaussianReal_sqrt μ hκ hB₀ hmom hE₀m
      hE₀_conf hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁
  refine ⟨hPhi_cont, fun v₀ hv₀ => ?_⟩
  obtain ⟨δ, hδ, hδ_bd⟩ := exists_Ioo_nhds_bound hv₀
  let DPhi (v : ℝ) (ω : Ω) (w : K → ℝ) : ℝ :=
    ∫ p : E × ℝ, ((X p.1 ⬝ᵥ w) / (2 * Real.sqrt v) -
      (Y ⬝ᵥ w + c_ξ * p.2) / (2 * Real.sqrt (1 - v))) * deriv u (S v w p) ∂(ν v ω w)
  have hder_pt : ∀ q : Ω × (K → ℝ), ∀ v ∈ Ioo (v₀ - δ) (v₀ + δ),
      HasDerivAt (fun s => Phi s q.1 q.2) (DPhi v q.1 q.2) v := fun q v hv => by
    obtain ⟨h1, h2⟩ := hδ_bd v hv
    have hv_Ioo : v ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le h1, by linarith⟩
    have : IsProbabilityMeasure (G₀ q.1) := hG₀_prob q.1
    have hpow : Integrable (fun p : E × ℝ => (1 + ‖p‖) ^ (n_X + 1))
        ((G₀ q.1).prod (gaussianReal 0 1)) := by
      rw [← tilted_prod_comp_fst]
      simpa only [add_zero] using integrable_one_add_norm_pow_tilted_prod_base μ hκ (hB₀ q.1)
        (hEω_m q.1) (hE₀_conf q.1) measurable_const (fun _ => le_rfl) (n_X + 1)
    have hXdot_m : Measurable fun p : E × ℝ => X p.1 ⬝ᵥ q.2 :=
      Finset.measurable_sum _ fun k _ => ((hXm k).comp measurable_fst).mul measurable_const
    have hYξ_m : Measurable fun p : E × ℝ => Y ⬝ᵥ q.2 + c_ξ * p.2 :=
      measurable_const.add (measurable_snd.const_mul c_ξ)
    have hnu : ((G₀ q.1).prod (gaussianReal 0 1)).tilted (fun p => u (S v q.2 p)) =
        ν v q.1 q.2 := by
      dsimp only [ν, G₀]; rw [← tilted_prod_comp_fst, tilted_tilted ((hEi q.1).comp_fst _)]; rfl
    have h := hasDerivAt_log_integral_exp_sqrt_path (μ := (G₀ q.1).prod (gaussianReal 0 1))
      hu hu0 hD₁ hXdot_m hYξ_m
      ((hpow.const_mul _).mono' hXdot_m.aestronglyMeasurable (ae_of_all _ fun p =>
        (Real.norm_eq_abs _).trans_le (abs_linear_field_le hXb Y c_ξ q.2 p).1))
      ((hpow.const_mul _).mono' hYξ_m.aestronglyMeasurable (ae_of_all _ fun p =>
        (Real.norm_eq_abs _).trans_le (abs_linear_field_le hXb Y c_ξ q.2 p).2)) hv_Ioo
    simpa only [Phi, DPhi, S, hnu] using h
  set s_A : ℝ := |L_X| * 2 ^ n_X + s_Y
  set W_const : ℝ := 1 + |u 0| + D₁ * |c_ξ| + 1 / 2 + D₁ * s_A
  set C_der : ℝ := (D₁ / (2 * Real.sqrt δ)) * L_sum * C_G * W_const ^ (n_X + 1) *
    (3 / 2 : ℝ) ^ (n_X + 1)
  set b_der : Ω × (K → ℝ) → ℝ := fun q =>
    C_der * (1 + ∑ k, |q.2 k|) ^ (n_X + 2) * (1 + B₀ q.1 + c₀ q.1) ^ (n_X + 1)
  have hbder_int : Integrable b_der (P₀.prod γ_sh) :=
    ((hmom (n_X + 1)).const_mul C_der |>.mul_prod
      (integrable_const_add_mul_sum_abs_pow_pi_gaussianReal 1 1 (n_X + 2))).congr
      (ae_of_all _ fun q => by simp only [one_mul, b_der]; ring)
  have hDPhi_m : ∀ v, Measurable fun q : Ω × (K → ℝ) => DPhi v q.1 q.2 := fun v => by
    refine measurable_integral_tilted_dep (μ := μ.prod (gaussianReal 0 1))
      (e := fun (q : Ω × (K → ℝ)) (p : E × ℝ) => E₀ q.1 p.1 + u (S v q.2 p))
      (Y := fun (q : Ω × (K → ℝ)) (p : E × ℝ) =>
        ((X p.1 ⬝ᵥ q.2) / (2 * Real.sqrt v) -
          (Y ⬝ᵥ q.2 + c_ξ * p.2) / (2 * Real.sqrt (1 - v))) * deriv u (S v q.2 p))
      ((hE₀m.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).add (hum.comp
        ((measurable_sqrt_field X Y hXm c_ξ v).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))) ?_
    have hX' : Measurable fun r : (Ω × (K → ℝ)) × (E × ℝ) => X r.2.1 ⬝ᵥ r.1.2 :=
      Finset.measurable_sum _ fun k _ => ((hXm k).comp (measurable_fst.comp measurable_snd)).mul
        ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst))
    have hY' : Measurable fun r : (Ω × (K → ℝ)) × (E × ℝ) => Y ⬝ᵥ r.1.2 + c_ξ * r.2.2 :=
      (Finset.measurable_sum _ fun k _ => measurable_const.mul
        ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst))).add
        ((measurable_snd.comp measurable_snd).const_mul c_ξ)
    have hS' : Measurable fun r : (Ω × (K → ℝ)) × (E × ℝ) => S v r.1.2 r.2 :=
      (measurable_sqrt_field X Y hXm c_ξ v).comp
        (f := fun r : (Ω × (K → ℝ)) × (E × ℝ) => (r.1.2, r.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact ((hX'.div_const _).sub (hY'.div_const _)).mul ((measurable_deriv u).comp hS')
  have hDPhi_bd : ∀ v ∈ Ioo (v₀ - δ) (v₀ + δ), ∀ ω w, |DPhi v ω w| ≤ b_der (ω, w) :=
    fun v hv ω w => by
      obtain ⟨h1, h2⟩ := hδ_bd v hv
      exact abs_deriv_log_integral_exp_sqrt_path_le μ hκ (hB₀ ω) (hEω_m ω) (hE₀_conf ω)
        (hE₀_low ω) X Y hXm hXb c_ξ hu hu0 hD₁ hCG0
        (fun A hAm s_A' hsA' hAl c_A' => hCG_le (E₀ ω) (hEω_m ω) (B₀ ω) (c₀ ω) (hB₀ ω)
          (hE₀_conf ω) (hE₀_low ω) A hAm s_A' hsA' hAl c_A' u D₁ hu hu0 hD₁)
        hδ h1 (by linarith) ⟨hδ.trans_le h1, by linarith⟩ w
  have hd_prod := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P₀.prod γ_sh)
    (F := fun v (q : Ω × (K → ℝ)) => Phi v q.1 q.2)
    (F' := fun v (q : Ω × (K → ℝ)) => DPhi v q.1 q.2)
    (s := Ioo (v₀ - δ) (v₀ + δ)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun v => (hPhi_m v).aestronglyMeasurable)
    (hPhi_int v₀ ⟨hv₀.1.le, hv₀.2.le⟩) (hDPhi_m v₀).aestronglyMeasurable
    (ae_of_all _ fun q v hv => hDPhi_bd v hv q.1 q.2) hbder_int (ae_of_all _ hder_pt)).2
  have hd_φ : HasDerivAt φ (∫ q : Ω × (K → ℝ), DPhi v₀ q.1 q.2 ∂(P₀.prod γ_sh)) v₀ :=
    hd_prod.congr_of_eventuallyEq (eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith))
      fun v hv => (integral_prod (fun q => Phi v q.1 q.2)
        (hPhi_int v ⟨(hδ.trans_le (hδ_bd v hv).1).le, by linarith [(hδ_bd v hv).2]⟩)).symm)
  have hDPhi_int : Integrable (fun q : Ω × (K → ℝ) => DPhi v₀ q.1 q.2) (P₀.prod γ_sh) :=
    hbder_int.mono' (hDPhi_m v₀).aestronglyMeasurable (ae_of_all _ fun q =>
      (Real.norm_eq_abs _).trans_le (hDPhi_bd v₀ ⟨by linarith, by linarith⟩ q.1 q.2))
  refine hd_φ.congr_deriv ?_
  rw [integral_prod _ hDPhi_int]
  dsimp only [DPhi]
  obtain ⟨hJ1, hJ2⟩ := integrable_stein_sqrt_log_terms μ hκ hB₀ hc₀ hmom hE₀m hE₀_conf hE₀_low
    X Y hXm hXb c_ξ hu hu0 hD₁ hD₂ hv₀
  refine (integral_congr_ae (ae_of_all _ fun ω =>
    stein_single_replica_sqrt_log_deriv μ hκ (hB₀ ω) (hEω_m ω) (hE₀_conf ω)
      (hE₀_low ω) X Y hXm hXb horth c_ξ hu hu₂ hu0 hD₁ hD₂ hv₀)).trans ?_
  rw [integral_const_mul, integral_sub hJ1 hJ2]

end LogPartitionConfined

end MeasureTheory
