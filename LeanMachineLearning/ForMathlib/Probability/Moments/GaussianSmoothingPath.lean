/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianAffineDerivative
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Derivative of a Gaussian smoothing along a parameter path

For independent standard Gaussians `η k` and a smooth `f`, the average
`𝔼 f (y + ∑ k, a k s * η k)` along a differentiable path `s ↦ (a k s)` has derivative
`(∑ k, a k a k') 𝔼 f'' (y + ∑ k, a k η k)` (the heat equation). Differentiating under the product
Gaussian integral and applying Stein's lemma in each variable avoids any square root of
`∑ k, a k²`, so the formula holds also where all `a k = 0`.

* `hasDerivAt_integral_gaussian_sum_path`: finitely many Gaussians, vector-valued `f` with `f''`
  of polynomial growth.
* `hasDerivAt_integral_gaussian_pair_path`: two Gaussians and bounded `f''`.

The two-variable case is the explicit term created by the `s`-dependent variance of `ξ*` in
Talagrand's cavity computation (Section 2.3, Eq. (2.49)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ProbabilityTheory

/-- **Heat equation along a path for a finite Gaussian smoothing:** if `f' ` is a derivative of
`f`, `f''` a derivative of `f'` of polynomial growth, and the coefficients `a k` are
differentiable near `s₀` with derivatives continuous at `s₀`, then
`(d/ds) 𝔼 f (y + ∑ k, a k s * η k) = (∑ k, a k s₀ * a' k s₀) • 𝔼 f'' (y + ∑ k, a k s₀ * η k)`. -/
theorem hasDerivAt_integral_gaussian_sum_path {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f' f'' : ℝ → E} {C : ℝ} {n : ℕ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y) (hC : ∀ y, ‖f'' y‖ ≤ C * (1 + |y|) ^ n)
    {a a' : κ → ℝ → ℝ} {s₀ : ℝ} (ha : ∀ k, ∀ᶠ s in 𝓝 s₀, HasDerivAt (a k) (a' k s) s)
    (ha' : ∀ k, ContinuousAt (a' k) s₀) (y : ℝ) :
    HasDerivAt (fun s => ∫ η, f (y + ∑ k, a k s * η k)
        ∂(Measure.pi fun _ : κ => gaussianReal 0 1))
      ((∑ k, a k s₀ * a' k s₀) • ∫ η, f'' (y + ∑ k, a k s₀ * η k)
        ∂(Measure.pi fun _ : κ => gaussianReal 0 1)) s₀ := by
  classical
  set π : Measure (κ → ℝ) := Measure.pi fun _ : κ => gaussianReal 0 1 with hπ
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have hf''m : StronglyMeasurable f'' := stronglyMeasurable_of_forall_hasDerivAt hf'
  have hC1 := norm_le_mul_one_add_abs_pow_of_hasDerivAt hf' hC
  have hC2 := norm_le_mul_one_add_abs_pow_of_hasDerivAt hf hC1
  set C₁ : ℝ := ‖f' 0‖ + C with hC₁
  set C₂ : ℝ := ‖f 0‖ + C₁ with hC₂
  -- every power of `1 + ∑ |η k|` is integrable
  have hpow : ∀ m : ℕ, Integrable (fun η : κ → ℝ => (1 + ∑ k, |η k|) ^ m) π := fun m => by
    have hk : ∀ k, MemLp (fun η : κ → ℝ => ‖η k‖) m π := fun k =>
      ((memLp_id_gaussianReal (μ := 0) (v := 1) m).comp_measurePreserving
        (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)).norm
    have h : MemLp (fun η : κ → ℝ => 1 + ∑ k, ‖η k‖) m π :=
      (memLp_const 1).add (memLp_finsetSum _ fun k _ => hk k)
    refine h.integrable_norm_pow'.congr (ae_of_all _ fun η => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
  have hdom : ∀ g : (κ → ℝ) → E, AEStronglyMeasurable g π → ∀ (D : ℝ) (m : ℕ),
      (∀ η, ‖g η‖ ≤ D * (1 + ∑ k, |η k|) ^ m) → Integrable g π := fun g hg D m h =>
    ((hpow m).const_mul D).mono' hg (ae_of_all _ h)
  -- local bounds for the path
  set B : ℝ := 1 + ∑ k, (|a k s₀| + |a' k s₀|) with hB
  have hB0 : 0 ≤ B := by positivity
  have hnear : ∀ᶠ s in 𝓝 s₀, ∀ k, HasDerivAt (a k) (a' k s) s ∧ |a k s| ≤ B ∧ |a' k s| ≤ B := by
    refine eventually_all.2 fun k => ?_
    have hle : |a k s₀| + |a' k s₀| ≤ ∑ k, (|a k s₀| + |a' k s₀|) :=
      Finset.single_le_sum (f := fun k => |a k s₀| + |a' k s₀|)
        (fun _ _ => by positivity) (Finset.mem_univ k)
    have key : ∀ g : ℝ → ℝ, ContinuousAt g s₀ → |g s₀| + 1 ≤ B → ∀ᶠ s in 𝓝 s₀, |g s| ≤ B :=
      fun g hg h => (hg.abs.eventually_lt_const (lt_add_one _)).mono fun s hs => hs.le.trans h
    have h1 := abs_nonneg (a k s₀)
    have h2 := abs_nonneg (a' k s₀)
    filter_upwards [ha k, key (a k) (ha k).self_of_nhds.continuousAt (by linarith),
      key (a' k) (ha' k) (by linarith)] with s b c d using ⟨b, c, d⟩
  have hlin : ∀ (c : κ → ℝ), (∀ k, |c k| ≤ B) → ∀ η : κ → ℝ,
      |∑ k, c k * η k| ≤ B * ∑ k, |η k| := fun c hc η => by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)
  have harg : ∀ (c : κ → ℝ), (∀ k, |c k| ≤ B) → ∀ (η : κ → ℝ) (D : ℝ), 0 ≤ D → ∀ m : ℕ,
      D * (1 + |y + ∑ k, c k * η k|) ^ m ≤
        D * (1 + |y| + B) ^ m * (1 + ∑ k, |η k|) ^ m := fun c hc η D hD m => by
    rw [mul_assoc, ← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ m) hD
    have h1 := (abs_add_le y (∑ k, c k * η k)).trans (add_le_add le_rfl (hlin c hc η))
    have h2 : (0 : ℝ) ≤ ∑ k, |η k| := by positivity
    nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) h2]
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  have hC₁0 : 0 ≤ C₁ := add_nonneg (norm_nonneg _) hC0
  have hC₂0 : 0 ≤ C₂ := add_nonneg (norm_nonneg _) hC₁0
  have h0 := hnear.self_of_nhds
  have hpm : ∀ s, Continuous fun η : κ → ℝ => y + ∑ k, a k s * η k := fun s => by fun_prop
  -- differentiation under the integral sign
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := π)
    (F := fun s η => f (y + ∑ k, a k s * η k))
    (F' := fun s η => (∑ k, a' k s * η k) • f' (y + ∑ k, a k s * η k))
    (bound := fun η => B * (C₁ * (1 + |y| + B) ^ (n + 1)) * (1 + ∑ k, |η k|) ^ (n + 2))
    hnear (Eventually.of_forall fun s => (hfc.comp (hpm s)).aestronglyMeasurable)
    (hdom _ (hfc.comp (hpm s₀)).aestronglyMeasurable (C₂ * (1 + |y| + B) ^ (n + 1 + 1))
      (n + 1 + 1) fun η => (hC2 _).trans (harg _ (fun k => (h0 k).2.1) η C₂ hC₂0 _))
    (((by fun_prop : Continuous fun η : κ → ℝ => ∑ k, a' k s₀ * η k).smul
      (hf'c.comp (hpm s₀))).aestronglyMeasurable)
    (ae_of_all _ fun η s hs => by
      have h1 : |∑ k, a' k s * η k| ≤ B * (1 + ∑ k, |η k|) :=
        (hlin _ (fun k => (hs k).2.2) η).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hB0)
      rw [norm_smul, Real.norm_eq_abs]
      refine (mul_le_mul h1 ((hC1 _).trans (harg _ (fun k => (hs k).2.1) η C₁ hC₁0 _))
        (norm_nonneg _) (by positivity)).trans_eq ?_
      rw [pow_succ (1 + ∑ k, |η k|) (n + 1)]
      ring)
    ((hpow (n + 2)).const_mul _)
    (ae_of_all _ fun η s hs => by
      have hl : HasDerivAt (fun s => y + ∑ k, a k s * η k) (∑ k, a' k s * η k) s :=
        (HasDerivAt.fun_sum fun k _ => (hs k).1.mul_const (η k)).const_add y
      exact (hf _).scomp s hl)).2
  refine hder.congr_deriv ?_
  -- Stein's lemma in each Gaussian variable
  have hj : ∀ j, Integrable (fun η : κ → ℝ => η j • f' (y + ∑ k, a k s₀ * η k)) π := fun j => by
    refine hdom _ ((continuous_apply j).smul (hf'c.comp (hpm s₀))).aestronglyMeasurable
      (C₁ * (1 + |y| + B) ^ (n + 1)) (n + 2) fun η => ?_
    have h1 : |η j| ≤ 1 + ∑ k, |η k| :=
      (Finset.single_le_sum (f := fun k => |η k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)
    rw [norm_smul, Real.norm_eq_abs]
    refine (mul_le_mul h1 ((hC1 _).trans (harg _ (fun k => (h0 k).2.1) η C₁ hC₁0 _))
      (norm_nonneg _) (by positivity)).trans_eq ?_
    rw [pow_succ (1 + ∑ k, |η k|) (n + 1)]
    ring
  have h2 : Integrable (fun η : κ → ℝ => f'' (y + ∑ k, a k s₀ * η k)) π :=
    hdom _ (hf''m.comp_measurable (hpm s₀).measurable).aestronglyMeasurable
      (C * (1 + |y| + B) ^ n) n fun η =>
        (hC _).trans (harg _ (fun k => (h0 k).2.1) η C hC0 _)
  have hstein : ∀ j, ∫ η, η j • f' (y + ∑ k, a k s₀ * η k) ∂π =
      a j s₀ • ∫ η, f'' (y + ∑ k, a k s₀ * η k) ∂π := fun j => by
    have hd : ∀ η : κ → ℝ, HasDerivAt
        (fun t => f' (y + ∑ k, a k s₀ * Function.update η j t k))
        (a j s₀ • f'' (y + ∑ k, a k s₀ * η k)) (η j) := fun η => by
      have hl : HasDerivAt (fun t => y + ∑ k, a k s₀ * Function.update η j t k) (a j s₀)
          (η j) := by
        refine ((HasDerivAt.fun_sum fun k _ => ((hasDerivAt_pi.1
          (hasDerivAt_update η j (η j))) k).const_mul (a k s₀)).const_add y).congr_deriv ?_
        simp [Pi.single_apply]
      have h := hf' (y + ∑ k, a k s₀ * Function.update η j (η j) k)
      rw [Function.update_eq_self] at h
      refine HasDerivAt.scomp (η j) ?_ hl
      simpa only [Function.update_eq_self] using h
    have hs : Integrable (fun η : κ → ℝ => a j s₀ • f'' (y + ∑ k, a k s₀ * η k)) π :=
      h2.smul (a j s₀)
    have h := integral_eval_smul_pi_gaussianReal_eq_of_coord (fun _ : κ => (1 : ℝ≥0)) j hd
      (hj j) hs
    rwa [NNReal.coe_one, one_smul, integral_smul] at h
  have hsplit : ∀ η : κ → ℝ, (∑ k, a' k s₀ * η k) • f' (y + ∑ k, a k s₀ * η k) =
      ∑ j, a' j s₀ • (η j • f' (y + ∑ k, a k s₀ * η k)) := fun η => by
    simp only [Finset.sum_smul, smul_smul]
  have hi : ∀ j ∈ Finset.univ,
      Integrable (fun η : κ → ℝ => a' j s₀ • (η j • f' (y + ∑ k, a k s₀ * η k))) π :=
    fun j _ => (hj j).smul (a' j s₀)
  simp only [hsplit]
  rw [integral_finsetSum _ hi, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul, hstein, smul_smul, mul_comm]

/-- **Heat equation along a path for a two-Gaussian smoothing** with a bounded second
derivative: the case of two Gaussians of `hasDerivAt_integral_gaussian_sum_path`. -/
theorem hasDerivAt_integral_gaussian_pair_path {f f' f'' : ℝ → ℝ} {C₂ : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hC₂ : ∀ y, |f'' y| ≤ C₂) {a b a' b' : ℝ → ℝ} {s₀ : ℝ}
    (ha : ∀ᶠ s in 𝓝 s₀, HasDerivAt a (a' s) s) (hb : ∀ᶠ s in 𝓝 s₀, HasDerivAt b (b' s) s)
    (ha' : ContinuousAt a' s₀) (hb' : ContinuousAt b' s₀) (y : ℝ) :
    HasDerivAt (fun s => ∫ η, f (y + a s * η.1 + b s * η.2)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      ((a s₀ * a' s₀ + b s₀ * b' s₀) *
        ∫ η, f'' (y + a s₀ * η.1 + b s₀ * η.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      s₀ := by
  have e : ∀ g : ℝ × ℝ → ℝ, ∫ p, g p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ η : Fin 2 → ℝ, g (η 0, η 1) ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := fun g =>
    ((measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' g).symm
  have h := hasDerivAt_integral_gaussian_sum_path (κ := Fin 2) hf hf' (C := C₂) (n := 0)
    (by simpa using hC₂) (a := ![a, b]) (a' := ![a', b']) (s₀ := s₀)
    (Fin.forall_fin_two.2 ⟨ha, hb⟩) (Fin.forall_fin_two.2 ⟨ha', hb'⟩) y
  simpa only [e, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_assoc, smul_eq_mul] using h

end ProbabilityTheory
