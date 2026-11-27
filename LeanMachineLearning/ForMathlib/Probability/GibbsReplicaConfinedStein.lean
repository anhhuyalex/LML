/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IntervalDerivative
public import LeanMachineLearning.ForMathlib.Analysis.Convex.LogConcaveMarginal
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub
public import LeanMachineLearning.ForMathlib.Data.Finset.SumBound
public import LeanMachineLearning.ForMathlib.LinearAlgebra.DotProductBound
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiUpdate
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaConfinedPair
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Gaussian interpolation and integration by parts for confined extended replica Gibbs states

For continuous-spin models on a finite-dimensional normed space `E` with an additive Haar measure
`μ` (such as `ℝ^(N+1)` with Lebesgue measure), consider a confined base energy
`E₀ x ≤ B₀ ‖x‖ - κ ‖x‖²` (`κ > 0`) and an extended state `(x, ξ) ∈ E × ℝ` carrying a standard
Gaussian coordinate `ξ ~ 𝒩(0, 1)` and a shared standard Gaussian vector `w : K → ℝ`.

Given a field `S_v(w, (x, ξ)) = √v (X x ⬝ᵥ w) + √(1 - v) (Y ⬝ᵥ w + c_ξ ξ)` and a nonpositive
potential `u ≤ 0`, tilting `μ × 𝒩(0, 1)` by `E₀ x + u (S_v(w, (x, ξ)))` equals tilting the Haar
product `μ × volume` on `E × ℝ` by `E₀ x + u (S_v(w, (x, ξ))) - ξ² / 2`
(`ProbabilityTheory.tilted_prod_gaussianReal_zero_one`), which is confined with constant
`min κ (1 / 2) > 0`. This allows `GibbsReplicaConfined` to differentiate replica expectations of
unbounded observables of polynomial growth both in individual coordinates `w_k` (justifying
multivariate Gaussian Stein integration by parts) and along `v ∈ (0, 1)`.

## Main statements

* `MeasureTheory.integral_snd_tilted_prod_gaussianReal_one`,
  `MeasureTheory.integral_snd_pi_tilted_prod_gaussianReal`: Gaussian integration by parts in the
  auxiliary coordinate `ξ` of a single replica under `(μ × 𝒩(0, 1)).tilted (E₀ + u ∘ S)`.
* `MeasureTheory.stein_pi_tilted_prod_gaussianReal`: joint Gaussian integration by parts in the
  shared vector `w` and the replica coordinate `ξ^{i₀}` for an `R`-replica expectation of a
  polynomially growing observable.
* `MeasureTheory.hasDerivAt_integral_integral_pi_tilted_prod_gaussianReal_sqrt`: differentiation
  in `v ∈ (0, 1)` and Gaussian integration by parts of the disorder-averaged `R`-replica
  expectation along `S_v`, producing the continuous-spin four-group covariance formula (the
  model-free core of Talagrand's Lemma 3.2.8 and of the second-order cavity step in Theorem 3.2.14).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped NNReal Topology BigOperators

namespace MeasureTheory

/-- **Single-replica Stein identity in the auxiliary Gaussian coordinate** of
`(μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (a p.1 + c * p.2))`, for any s-finite
measure `μ` and `g * exp E₀` integrable. -/
theorem integral_snd_tilted_prod_gaussianReal_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {E₀ a : α → ℝ} (hE₀m : Measurable E₀) (ham : Measurable a)
    {g : α → ℝ} (hgm : Measurable g) (hgi : Integrable (fun x => g x * Real.exp (E₀ x)) μ)
    (c : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    {ψ : ℝ → ℝ} (hψd : Differentiable ℝ ψ) {M₀ M₁ : ℝ}
    (hM₀ : ∀ x, |ψ x| ≤ M₀) (hM₁ : ∀ x, |deriv ψ x| ≤ M₁) :
    let S (p : α × ℝ) : ℝ := a p.1 + c * p.2
    let ν : Measure (α × ℝ) := (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S p))
    ∫ p : α × ℝ, g p.1 * p.2 * ψ (S p) ∂ν =
      c * ∫ p : α × ℝ, g p.1 * (deriv ψ (S p) + ψ (S p) * deriv u (S p)) ∂ν := by
  intro S ν
  set γ : Measure ℝ := gaussianReal 0 1
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hψm : Measurable ψ := hψd.continuous.measurable
  have hdψm : Measurable (deriv ψ) := measurable_deriv ψ
  have hSm : Measurable S := (ham.comp measurable_fst).add (measurable_snd.const_mul c)
  have hx_abs : Integrable (fun x : α => |g x| * Real.exp (E₀ x)) μ :=
    hgi.norm.congr (ae_of_all _ fun x => by
      dsimp only
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le])
  rw [integral_tilted_eq_div, integral_tilted_eq_div, mul_div_assoc']
  congr 1
  rw [← integral_const_mul]
  have h1_int : Integrable (fun p : α × ℝ => (g p.1 * p.2 * ψ (S p)) *
      Real.exp (E₀ p.1 + u (S p))) (μ.prod γ) := by
    have hdom : Integrable (fun p : α × ℝ => (|g p.1| * Real.exp (E₀ p.1)) *
        (|M₀| * |p.2|)) (μ.prod γ) :=
      hx_abs.mul_prod ((integrable_abs_id_gaussianReal (m := 0) (v := 1)).const_mul |M₀|)
    refine hdom.mono' ((((hgm.comp measurable_fst).mul measurable_snd).mul
      (hψm.comp hSm)).mul
      (((hE₀m.comp measurable_fst).add (hum.comp hSm)).exp)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), Real.exp_add]
    have hu1 : Real.exp (u (S p)) ≤ 1 := Real.exp_le_one_iff.2 (hu0 _)
    have hψ1 : |ψ (S p)| ≤ |M₀| := (hM₀ _).trans (le_abs_self _)
    calc |g p.1| * |p.2| * |ψ (S p)| * (Real.exp (E₀ p.1) * Real.exp (u (S p)))
        = (|g p.1| * Real.exp (E₀ p.1)) * (|ψ (S p)| * Real.exp (u (S p)) * |p.2|) := by ring
      _ ≤ (|g p.1| * Real.exp (E₀ p.1)) * (|M₀| * 1 * |p.2|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul hψ1 hu1 (Real.exp_pos _).le (abs_nonneg _)) (abs_nonneg _))
            (by positivity)
      _ = (|g p.1| * Real.exp (E₀ p.1)) * (|M₀| * |p.2|) := by ring
  have h2_int : Integrable (fun p : α × ℝ => c * ((g p.1 *
      (deriv ψ (S p) + ψ (S p) * deriv u (S p))) * Real.exp (E₀ p.1 + u (S p)))) (μ.prod γ) := by
    set B_ψ : ℝ := |c| * (|M₁| + |M₀| * |D₁|)
    have hdom : Integrable (fun p : α × ℝ => (|g p.1| * Real.exp (E₀ p.1)) * B_ψ) (μ.prod γ) :=
      hx_abs.mul_prod (integrable_const B_ψ)
    refine hdom.mono' ((((hgm.comp measurable_fst).mul
      ((hdψm.comp hSm).add ((hψm.comp hSm).mul (hdu.comp hSm)))).mul
      (((hE₀m.comp measurable_fst).add (hum.comp hSm)).exp)).const_mul c).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), Real.exp_add]
    have hu1 : Real.exp (u (S p)) ≤ 1 := Real.exp_le_one_iff.2 (hu0 _)
    have hd1 : |deriv ψ (S p) + ψ (S p) * deriv u (S p)| ≤ |M₁| + |M₀| * |D₁| := by
      refine (abs_add_le _ _).trans (add_le_add ((hM₁ _).trans (le_abs_self _)) ?_)
      rw [abs_mul]
      exact mul_le_mul ((hM₀ _).trans (le_abs_self _)) ((hD₁ _).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
    calc |c| * (|g p.1| * |deriv ψ (S p) + ψ (S p) * deriv u (S p)| *
            (Real.exp (E₀ p.1) * Real.exp (u (S p))))
        = (|g p.1| * Real.exp (E₀ p.1)) *
            (|c| * (|deriv ψ (S p) + ψ (S p) * deriv u (S p)| * Real.exp (u (S p)))) := by ring
      _ ≤ (|g p.1| * Real.exp (E₀ p.1)) * (|c| * ((|M₁| + |M₀| * |D₁|) * 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul hd1 hu1 (Real.exp_pos _).le (by positivity)) (abs_nonneg _))
            (by positivity)
      _ = (|g p.1| * Real.exp (E₀ p.1)) * B_ψ := by dsimp only [B_ψ]; ring
  rw [integral_prod _ h1_int, integral_prod _ h2_int]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  have hpt1 : (fun ξ : ℝ => (g x * ξ * ψ (S (x, ξ))) * Real.exp (E₀ x + u (S (x, ξ)))) =
      fun ξ => (g x * Real.exp (E₀ x)) *
        (ξ * (ψ (a x + c * ξ) * Real.exp (u (a x + c * ξ)))) := by
    funext ξ; dsimp only [S]; rw [Real.exp_add]; ring
  have hpt2 : (fun ξ : ℝ => c * ((g x *
        (deriv ψ (S (x, ξ)) + ψ (S (x, ξ)) * deriv u (S (x, ξ)))) *
        Real.exp (E₀ x + u (S (x, ξ))))) =
      fun ξ => (g x * Real.exp (E₀ x)) * (c * ((deriv ψ (a x + c * ξ) +
        ψ (a x + c * ξ) * deriv u (a x + c * ξ)) * Real.exp (u (a x + c * ξ)))) := by
    funext ξ; dsimp only [S]; rw [Real.exp_add]; ring
  rw [hpt1, hpt2, integral_const_mul, integral_const_mul]
  congr 1
  rw [integral_const_mul]
  set H : ℝ → ℝ := fun ξ => ψ (a x + c * ξ) * Real.exp (u (a x + c * ξ))
  set H' : ℝ → ℝ := fun ξ => c * ((deriv ψ (a x + c * ξ) +
    ψ (a x + c * ξ) * deriv u (a x + c * ξ)) * Real.exp (u (a x + c * ξ)))
  have hHd : ∀ ξ, HasDerivAt H (H' ξ) ξ := fun ξ => by
    have hlin : HasDerivAt (fun t : ℝ => a x + c * t) c ξ := by
      simpa using ((hasDerivAt_id ξ).const_mul c).const_add (a x)
    have h1 := (hψd (a x + c * ξ)).hasDerivAt.comp ξ hlin
    have h2 := ((hu (a x + c * ξ)).hasDerivAt.comp ξ hlin).exp
    exact (h1.mul h2).congr_deriv (by dsimp only [H', Function.comp_def]; ring)
  have hHi1 : Integrable (fun ξ => ξ * H ξ) γ := by
    refine ((integrable_abs_id_gaussianReal (m := 0) (v := 1)).const_mul |M₀|).mono'
      (measurable_id.mul ((hψm.comp (by fun_prop)).mul
        ((hum.comp (by fun_prop)).exp))).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    dsimp only [H]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm |M₀|]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))).trans
        ((hM₀ _).trans (le_abs_self _))) (abs_nonneg _)
  have hHi2 : Integrable H' γ := by
    refine Integrable.of_bound
      ((((hdψm.comp (by fun_prop)).add ((hψm.comp (by fun_prop)).mul (hdu.comp (by fun_prop)))).mul
        ((hum.comp (by fun_prop)).exp)).const_mul c).aestronglyMeasurable
      (|c| * (|M₁| + |M₀| * |D₁|)) (ae_of_all _ fun ξ => ?_)
    dsimp only [H']
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))).trans ?_)
      (abs_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add ((hM₁ _).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    exact mul_le_mul ((hM₀ _).trans (le_abs_self _)) ((hD₁ _).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have hst := integral_id_mul_gaussianReal_eq 1 hHd hHi1 hHi2
  simpa only [NNReal.coe_one, one_mul, H, H', integral_const_mul] using hst

section ConfinedExtended

variable {E K R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_prod_sq_le_add_sq (p : E × ℝ) : ‖p‖ ^ 2 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]; exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (sq_nonneg _)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Adding a nonpositive perturbation and the Gaussian weight of the auxiliary coordinate keeps a
confined energy confined on `E × ℝ`. -/
theorem prod_gaussian_exponent_confining {κ B₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀)
    {E₀ : E → ℝ} (hE₀ : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    {u : ℝ → ℝ} (hu0 : ∀ x, u x ≤ 0) (S : E × ℝ → ℝ) (p : E × ℝ) :
    E₀ p.1 + u (S p) - p.2 ^ 2 / 2 ≤ 0 + B₀ * ‖p‖ - min κ (1 / 2) * ‖p‖ ^ 2 := by
  have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h2 := norm_prod_sq_le_add_sq p
  have hm1 : min κ (1 / 2) ≤ κ := min_le_left _ _
  have hm2 : min κ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hm0 : 0 ≤ min κ (1 / 2) := le_min hκ.le (by positivity)
  nlinarith [hu0 (S p), hE₀ p.1, sq_nonneg ‖p.1‖, sq_nonneg p.2,
    mul_le_mul_of_nonneg_left h1 hB₀, mul_le_mul_of_nonneg_left h2 hm0]

/-- If every `|ψ r|` is at most `M₀`, every sub-product of the `ψ r` is at most
`(1 + |M₀| + |M₁|) ^ |R|`. -/
private theorem abs_prod_le_one_add_pow {R : Type*} [Fintype R] {ψ : R → ℝ → ℝ} {M₀ : ℝ}
    (hM₀ : ∀ r x, |ψ r x| ≤ M₀) (M₁ : ℝ) (s : Finset R) (x : R → ℝ) :
    |∏ r ∈ s, ψ r (x r)| ≤ (1 + |M₀| + |M₁|) ^ Fintype.card R :=
  (s.abs_prod_le_pow_card fun r _ => (hM₀ r _).trans
      ((le_abs_self _).trans (by linarith [abs_nonneg M₁]))).trans
    (pow_le_pow_right₀ (by linarith [abs_nonneg M₀, abs_nonneg M₁]) s.card_le_univ)

/-- Replacing the factor `ψ j` of a product by its derivative keeps the bound
`(1 + |M₀| + |M₁|) ^ |R|`. -/
private theorem abs_deriv_mul_prod_erase_le {R : Type*} [Fintype R] [DecidableEq R]
    {ψ : R → ℝ → ℝ} {M₀ M₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁) (j : R) (x : R → ℝ) :
    |deriv (ψ j) (x j) * ∏ r ∈ Finset.univ.erase j, ψ r (x r)| ≤
      (1 + |M₀| + |M₁|) ^ Fintype.card R := by
  rw [abs_mul, ← Finset.card_univ, ← Finset.card_erase_add_one (Finset.mem_univ j), pow_succ']
  exact mul_le_mul ((hM₁ j _).trans ((le_abs_self _).trans (by linarith [abs_nonneg M₀])))
    ((Finset.univ.erase j).abs_prod_le_pow_card fun r _ => (hM₀ r _).trans
      ((le_abs_self _).trans (by linarith [abs_nonneg M₁])))
    (abs_nonneg _) (by positivity)

/-- The same bound for the derivative of the tilted factor `ψ j * exp u` times the other
factors, with an extra `1 + |D₁|` from `|u'| ≤ D₁`. -/
private theorem abs_tiltedDeriv_mul_prod_erase_le {R : Type*} [Fintype R] [DecidableEq R]
    {ψ : R → ℝ → ℝ} {u : ℝ → ℝ} {M₀ M₁ D₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁) (hD₁ : ∀ x, |deriv u x| ≤ D₁) (j : R) (x : R → ℝ) :
    |(deriv (ψ j) (x j) + ψ j (x j) * deriv u (x j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (x r)| ≤
      (1 + |D₁|) * (1 + |M₀| + |M₁|) ^ Fintype.card R := by
  rw [add_mul, one_add_mul]
  refine (abs_add_le _ _).trans
    (add_le_add (abs_deriv_mul_prod_erase_le hM₀ hM₁ j x) ?_)
  rw [mul_right_comm, Finset.mul_prod_erase _ (fun r => ψ r (x r)) (Finset.mem_univ j), abs_mul]
  exact (mul_le_mul (abs_prod_le_one_add_pow hM₀ M₁ _ x) ((hD₁ _).trans (le_abs_self _))
    (abs_nonneg _) (by positivity)).trans_eq (mul_comm _ _)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A confined energy which is at least `-c₀` on the unit ball forces `0 ≤ c₀`. -/
theorem nonneg_of_confining_of_neg_le {κ B₀ c₀ : ℝ} {E₀ : E → ℝ}
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2) (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x) :
    0 ≤ c₀ := by
  have h1 := hE₀_low 0 (by simp)
  have h2 : E₀ 0 ≤ 0 := by simpa using hE₀_conf 0
  linarith

/-- The one-replica state `(μ × 𝒩(0, 1)).tilted (E₀ x + u (S (x, ξ)))`, with `E₀` confined and
`u ≤ 0`, is a probability measure. -/
theorem isProbabilityMeasure_tilted_prod_gaussianReal_of_confining {κ B₀ : ℝ} (hκ : 0 < κ)
    {E₀ : E → ℝ} (hE₀m : Measurable E₀) (hE₀ : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    {u : ℝ → ℝ} (hum : Measurable u) (hu0 : ∀ x, u x ≤ 0) {S : E × ℝ → ℝ} (hS : Measurable S) :
    IsProbabilityMeasure
      ((μ.prod (gaussianReal 0 1)).tilted fun p => E₀ p.1 + u (S p)) := by
  rw [tilted_prod_gaussianReal_zero_one μ]
  exact isProbabilityMeasure_tilted (integrable_exp_of_confining (μ := μ.prod volume)
    (lt_min hκ one_half_pos)
    (((hE₀m.comp measurable_fst).add (hum.comp hS)).sub
      ((measurable_snd.pow_const 2).div_const 2))
    (prod_gaussian_exponent_confining hκ (abs_nonneg B₀)
      (fun x => (hE₀ x).trans (by gcongr; exact le_abs_self _)) hu0 S))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Away from the endpoints, the derivative in `v` of the field
`√v (X x ⬝ᵥ w) + √(1 - v) (Y ⬝ᵥ w + c_ξ ξ)` grows polynomially in `(x, ξ)`. -/
private theorem abs_sqrt_path_deriv_le [Fintype K] {X : E → K → ℝ} {L_X : ℝ} {n_X : ℕ}
    (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X) (Y w : K → ℝ) (c_ξ : ℝ) {δ v : ℝ}
    (hδ : 0 < δ) (h1 : δ ≤ v) (h2 : δ ≤ 1 - v) (p : E × ℝ) :
    |1 / (2 * Real.sqrt v) * (X p.1 ⬝ᵥ w) -
        1 / (2 * Real.sqrt (1 - v)) * (Y ⬝ᵥ w + c_ξ * p.2)| ≤
      1 / (2 * Real.sqrt δ) * (|L_X| * (∑ k, |w k|) + |Y ⬝ᵥ w| + |c_ξ|) *
        (1 + ‖p‖) ^ (n_X + 1) := by
  have hp : (1 : ℝ) ≤ 1 + ‖p‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hX : |X p.1 ⬝ᵥ w| ≤ |L_X| * (∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) := by
    refine (abs_dotProduct_le_mul_sum_abs (M := |L_X| * (1 + ‖p‖) ^ (n_X + 1))
      (fun k => (hXb k p.1).trans ?_) w).trans_eq (by ring)
    exact mul_le_mul (le_abs_self _)
      ((pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le p) 1) n_X).trans
        (pow_le_pow_right₀ hp (Nat.le_succ n_X))) (by positivity) (abs_nonneg _)
  have hY : |Y ⬝ᵥ w + c_ξ * p.2| ≤ (|Y ⬝ᵥ w| + |c_ξ|) * (1 + ‖p‖) ^ (n_X + 1) := by
    have hp2 : |p.2| ≤ (1 + ‖p‖) ^ (n_X + 1) :=
      ((norm_snd_le p).trans (le_add_of_nonneg_left zero_le_one)).trans
        (le_self_pow₀ hp (Nat.succ_ne_zero _))
    rw [add_mul]
    refine (abs_add_le _ _).trans (add_le_add
      (le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ hp)) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hp2 (abs_nonneg _)
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  refine (add_le_add
    (mul_le_mul (Real.abs_one_div_two_mul_sqrt_le hδ h1) hX (abs_nonneg _) (by positivity))
    (mul_le_mul (Real.abs_one_div_two_mul_sqrt_le hδ h2) hY (abs_nonneg _)
      (by positivity))).trans_eq ?_
  ring

/-- Polynomial moment bound on `E × ℝ` for `(μ.prod (gaussianReal 0 1)).tilted (E₀ + u ∘ S)`,
growing polynomially in `B₀`, `c₀` and `∑ k, |w k|`. -/
theorem exists_integral_one_add_norm_pow_tilted_prod_gaussian_le [Fintype K]
    {κ : ℝ} (hκ : 0 < κ) (m : ℕ) :
    ∃ C_m : ℝ, 0 ≤ C_m ∧ ∀ (E₀ : E → ℝ), Measurable E₀ → ∀ B₀ c₀ : ℝ, 0 ≤ B₀ →
      (∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2) → (∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x) →
      ∀ (A : E → K → ℝ), (∀ k, Measurable fun x => A x k) →
      ∀ (s_A : ℝ), 0 ≤ s_A → (∀ k x, ‖x‖ ≤ 1 → |A x k| ≤ s_A) →
      ∀ (c_A : ℝ) (u : ℝ → ℝ) (D₁ : ℝ), Differentiable ℝ u → (∀ x, u x ≤ 0) →
      (∀ x, |deriv u x| ≤ D₁) → ∀ w : K → ℝ,
      ∫ p, (1 + ‖p‖) ^ m
        ∂((μ.prod (gaussianReal 0 1)).tilted fun p => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2)) ≤
        C_m * (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2)) ^ m := by
  have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
  obtain ⟨C_m, hCm0, hCm⟩ := exists_integral_one_add_norm_pow_tilted_le
    (E := E × ℝ) (μ.prod volume) hκ' m
  refine ⟨C_m, hCm0, fun E₀ hE₀m B₀ c₀ hB₀ hE₀_conf hE₀_low A hAm s_A hs_A hA_low
    c_A u D₁ hu hu0 hD₁ w => ?_⟩
  have hc₀ : 0 ≤ c₀ := nonneg_of_confining_of_neg_le hE₀_conf hE₀_low
  rw [tilted_prod_gaussianReal_zero_one]
  have hum : Measurable u := hu.continuous.measurable
  have hSm : Measurable fun p : E × ℝ => A p.1 ⬝ᵥ w + c_A * p.2 :=
    (Finset.measurable_sum _ fun j _ => ((hAm j).comp measurable_fst).mul_const (w j)).add
      (measurable_snd.const_mul c_A)
  have hem : Measurable fun p : E × ℝ => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2) - p.2 ^ 2 / 2 :=
    ((hE₀m.comp measurable_fst).add (hum.comp hSm)).sub ((measurable_snd.pow_const 2).div_const 2)
  set c_tot : ℝ := c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2
  have hc_tot : 0 ≤ c_tot := by
    have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  refine hCm _ hem B₀ c_tot hB₀ hc_tot
    (fun p => by
      simpa only [zero_add] using prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0
        (fun p => A p.1 ⬝ᵥ w + c_A * p.2) p)
    (fun p hp => ?_)
  have hp1 : ‖p.1‖ ≤ 1 := (norm_fst_le p).trans hp
  have hp2 : |p.2| ≤ 1 := (by simpa using norm_snd_le p : |p.2| ≤ ‖p‖).trans hp
  have hp2_sq : p.2 ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hp2
  have hS_bd : |A p.1 ⬝ᵥ w + c_A * p.2| ≤ s_A * (∑ k, |w k|) + |c_A| := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA_low k p.1 hp1) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hp2
  have hlip : -(|u 0| + |D₁| * |A p.1 ⬝ᵥ w + c_A * p.2|) ≤ u (A p.1 ⬝ᵥ w + c_A * p.2) :=
    neg_le_of_abs_le (norm_le_norm_zero_add_of_norm_deriv_le hu
      (fun z => (hD₁ z).trans (le_abs_self D₁)) _)
  have hD_bd := mul_le_mul_of_nonneg_left hS_bd (abs_nonneg D₁)
  dsimp only [c_tot]
  linarith [hE₀_low p.1 hp1]

/-- **`R`-replica Stein identity in the auxiliary Gaussian coordinate `(σ i₀).2`** for a
polynomially growing observable `f` under a confined base energy `E₀`. -/
theorem integral_snd_pi_tilted_prod_gaussianReal [Fintype R] [DecidableEq R]
    {κ B₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀)
    {E₀ a : E → ℝ} (hE₀m : Measurable E₀) (ham : Measurable a)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (c : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ σ, |f σ| ≤ C_f * ∏ r, (1 + ‖σ r‖) ^ m_f)
    (i₀ : R) :
    let S (p : E × ℝ) : ℝ := a p.1 + c * p.2
    let ν : Measure (E × ℝ) := (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S p))
    ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * (σ i₀).2 * ∏ r, ψ r (S (σ r))
        ∂(Measure.pi fun _ : R => ν) =
      c * ∫ σ : R → E × ℝ, f (fun r => (σ r).1) *
          (deriv (ψ i₀) (S (σ i₀)) + ψ i₀ (S (σ i₀)) * deriv u (S (σ i₀))) *
          ∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r))
        ∂(Measure.pi fun _ : R => ν) := by
  intro S ν
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hSm : Measurable S := (ham.comp measurable_fst).add (measurable_snd.const_mul c)
  have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
  have hconf : ∀ p : E × ℝ, E₀ p.1 + u (S p) - p.2 ^ 2 / 2 ≤
      0 + B₀ * ‖p‖ - min κ (1 / 2) * ‖p‖ ^ 2 :=
    prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 S
  have : IsProbabilityMeasure ν :=
    isProbabilityMeasure_tilted_prod_gaussianReal_of_confining μ hκ hE₀m hE₀_conf hum hu0 hSm
  set C_ψ : ℝ := (1 + |M₀| + |M₁|) ^ Fintype.card R
  have hfb_p : ∀ σ : R → E × ℝ, |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
    abs_comp_le_prod_of_injective hfb norm_fst_le Function.injective_id
  have hLHS_i : Integrable (fun σ : R → E × ℝ =>
      f (fun r => (σ r).1) * (σ i₀).2 * ∏ r, ψ r (S (σ r))) (Measure.pi fun _ : R => ν) := by
    rw [show ν = _ from tilted_prod_gaussianReal_zero_one μ _]
    refine integrable_pi_tilted_of_confining (μ := μ.prod volume) hκ'
      (((hE₀m.comp measurable_fst).add (hum.comp hSm)).sub
        ((measurable_snd.pow_const 2).div_const 2)) hconf
      (((hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
        (measurable_snd.comp (measurable_pi_apply i₀))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp
            (hSm.comp (measurable_pi_apply r)))).aestronglyMeasurable
      (C := |C_f| * (1 * C_ψ)) (m := m_f + 1) fun σ => ?_
    rw [Real.norm_eq_abs, mul_assoc]
    have h2 : |(σ i₀).2 * ∏ r, ψ r (S (σ r))| ≤ (1 * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ 1 := by
      rw [abs_mul, mul_comm (1 : ℝ)]
      have hξ : |(σ i₀).2| ≤ 1 * ∏ r, (1 + ‖σ r‖) ^ 1 := by
        have h0 : |(σ i₀).2| ≤ 1 * (1 + ‖σ i₀‖) ^ 1 := by
          rw [one_mul, pow_one]
          exact ((by simpa using norm_snd_le (σ i₀) : |(σ i₀).2| ≤ ‖σ i₀‖)).trans
            (le_add_of_nonneg_left zero_le_one)
        exact h0.trans (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ 1 i₀) zero_le_one)
      have hpr : |∏ r, ψ r (S (σ r))| ≤ C_ψ :=
        abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S (σ r)
      exact (mul_le_mul hξ hpr (abs_nonneg _) (by positivity)).trans_eq (by ring)
    exact abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) h2
  have hRHS_i : Integrable (fun σ : R → E × ℝ => c * (f (fun r => (σ r).1) *
      (deriv (ψ i₀) (S (σ i₀)) + ψ i₀ (S (σ i₀)) * deriv u (S (σ i₀))) *
      ∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r)))) (Measure.pi fun _ : R => ν) := by
    rw [show ν = _ from tilted_prod_gaussianReal_zero_one μ _]
    refine (integrable_pi_tilted_of_confining (μ := μ.prod volume) hκ'
      (((hE₀m.comp measurable_fst).add (hum.comp hSm)).sub
        ((measurable_snd.pow_const 2).div_const 2)) hconf
      (((hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
        (((measurable_deriv (ψ i₀)).comp (hSm.comp (measurable_pi_apply i₀))).add
          (((hψd i₀).continuous.measurable.comp (hSm.comp (measurable_pi_apply i₀))).mul
            (hdu.comp (hSm.comp (measurable_pi_apply i₀)))))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp
            (hSm.comp (measurable_pi_apply r)))).aestronglyMeasurable
      (C := |C_f| * ((1 + |D₁|) * C_ψ)) (m := m_f + 0) fun σ => ?_).const_mul c
    rw [Real.norm_eq_abs, mul_assoc]
    have h2 : |(deriv (ψ i₀) (S (σ i₀)) + ψ i₀ (S (σ i₀)) * deriv u (S (σ i₀))) *
        ∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r))| ≤
        ((1 + |D₁|) * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ 0 := by
      simp only [pow_zero, Finset.prod_const_one, mul_one]
      exact abs_tiltedDeriv_mul_prod_erase_le hM₀ hM₁ hD₁ i₀ fun r => S (σ r)
    exact abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) h2
  rw [← integral_const_mul, integral_pi_eq_integral_update (fun _ : R => ν) i₀ hLHS_i,
    integral_pi_eq_integral_update (fun _ : R => ν) i₀ hRHS_i]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  dsimp only
  set g_σ : E → ℝ := fun x =>
    f (fun r => (update σ i₀ (x, 0) r).1) * ∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r))
  have hg_m : Measurable g_σ := by
    refine (hf.comp (measurable_pi_iff.2 fun r => ?_)).mul measurable_const
    by_cases hr : r = i₀
    · subst hr; simp only [update_self]; exact measurable_id
    · simp only [update_of_ne hr]; exact measurable_const
  have hg_i : Integrable (fun x => g_σ x * Real.exp (E₀ x)) μ := by
    set K_σ : ℝ := |C_f| * (∏ r ∈ Finset.univ.erase i₀, (1 + ‖(σ r).1‖) ^ m_f) *
      |∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r))|
    have hgb : ∀ x, |g_σ x| ≤ K_σ * (1 + ‖x‖) ^ m_f := fun x => by
      dsimp only [g_σ]
      rw [abs_mul]
      have hf1 : |f (fun r => (update σ i₀ (x, 0) r).1)| ≤
          |C_f| * ((1 + ‖x‖) ^ m_f * ∏ r ∈ Finset.univ.erase i₀, (1 + ‖(σ r).1‖) ^ m_f) := by
        refine (hfb _).trans (mul_le_mul (le_abs_self _) ?_
          (Finset.prod_nonneg fun _ _ => by positivity) (abs_nonneg _))
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
        simp only [update_self]
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => by positivity)
          fun r hr => ?_) (by positivity)
        rw [update_of_ne (Finset.ne_of_mem_erase hr)]
      calc |f (fun r => (update σ i₀ (x, 0) r).1)| * |∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r))|
          ≤ (|C_f| * ((1 + ‖x‖) ^ m_f * ∏ r ∈ Finset.univ.erase i₀, (1 + ‖(σ r).1‖) ^ m_f)) *
              |∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r))| :=
            mul_le_mul_of_nonneg_right hf1 (abs_nonneg _)
        _ = K_σ * (1 + ‖x‖) ^ m_f := by dsimp only [K_σ]; ring
    have hdom : Integrable (fun x => K_σ * ((1 + ‖x‖) ^ m_f *
        Real.exp (B₀ * ‖x‖ - κ * ‖x‖ ^ 2))) μ :=
      (integrable_one_add_norm_pow_mul_exp (μ := μ) hκ B₀ m_f).const_mul K_σ
    refine hdom.mono' (hg_m.mul hE₀m.exp).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul (hgb x) (Real.exp_le_exp.2 (hE₀_conf x)) (Real.exp_pos _).le
      (by positivity)).trans_eq (by ring)
  have hpt_L : ∀ p : E × ℝ,
      f (fun r => (update σ i₀ p r).1) * (update σ i₀ p i₀).2 *
        (∏ r, ψ r (S (update σ i₀ p r))) =
      g_σ p.1 * p.2 * ψ i₀ (S p) := fun p => by
    have hf_eq : (fun r => (update σ i₀ p r).1) = fun r => (update σ i₀ (p.1, 0) r).1 := by
      funext r; by_cases hr : r = i₀ <;> simp [hr]
    rw [hf_eq, update_self, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    simp only [update_self]
    have hpr_eq : (∏ r ∈ Finset.univ.erase i₀, ψ r (S (update σ i₀ p r))) =
        ∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r)) :=
      Finset.prod_congr rfl fun r hr => by rw [update_of_ne (Finset.ne_of_mem_erase hr)]
    rw [hpr_eq]
    dsimp only [g_σ]; ring
  have hpt_R : ∀ p : E × ℝ,
      c * (f (fun r => (update σ i₀ p r).1) *
        (deriv (ψ i₀) (S (update σ i₀ p i₀)) +
          ψ i₀ (S (update σ i₀ p i₀)) * deriv u (S (update σ i₀ p i₀))) *
        ∏ r ∈ Finset.univ.erase i₀, ψ r (S (update σ i₀ p r))) =
      c * (g_σ p.1 * (deriv (ψ i₀) (S p) + ψ i₀ (S p) * deriv u (S p))) := fun p => by
    have hf_eq : (fun r => (update σ i₀ p r).1) = fun r => (update σ i₀ (p.1, 0) r).1 := by
      funext r; by_cases hr : r = i₀ <;> simp [hr]
    have hpr_eq : (∏ r ∈ Finset.univ.erase i₀, ψ r (S (update σ i₀ p r))) =
        ∏ r ∈ Finset.univ.erase i₀, ψ r (S (σ r)) :=
      Finset.prod_congr rfl fun r hr => by rw [update_of_ne (Finset.ne_of_mem_erase hr)]
    rw [hf_eq, update_self, hpr_eq]
    dsimp only [g_σ]; ring
  simp_rw [hpt_L, hpt_R, integral_const_mul]
  exact integral_snd_tilted_prod_gaussianReal_one μ hE₀m ham hg_m hg_i c hu hu0 hD₁
    (hψd i₀) (hM₀ i₀) (hM₁ i₀)

/-- Coordinatewise derivative in `w k` of an `R`-replica expectation under
`(μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2))`. -/
theorem hasDerivAt_coord_tilted_prod_gaussian [Fintype K] [DecidableEq K]
    [Fintype R] [DecidableEq R]
    {κ B₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀)
    {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (A : E → K → ℝ) (hAm : ∀ k, Measurable fun x => A x k)
    {L_A : ℝ} {n_A : ℕ} (hAb : ∀ k x, |A x k| ≤ L_A * (1 + ‖x‖) ^ n_A)
    (c_A : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    (w : K → ℝ) (k : K) :
    let S (w' : K → ℝ) (p : E × ℝ) : ℝ := A p.1 ⬝ᵥ w' + c_A * p.2
    let ν (w' : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S w' p))
    let Φ (w' : K → ℝ) (σ : R → E × ℝ) : ℝ :=
      f (fun r => (σ r).1) * ∏ r, ψ r (S w' (σ r))
    let Φ'_k (σ : R → E × ℝ) : ℝ :=
      f (fun r => (σ r).1) * ∑ j : R, A (σ j).1 k * deriv (ψ j) (S w (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))
    HasDerivAt (fun z => ∫ σ, Φ (update w k z) σ ∂(Measure.pi fun _ : R => ν (update w k z)))
      ((∫ σ, Φ'_k σ ∂(Measure.pi fun _ : R => ν w)) +
        replicaDiff (ν w) (Φ w) (fun p => A p.1 k * deriv u (S w p))) (w k) := by
  intro S ν Φ Φ'_k
  have hν_eq : ∀ w', ν w' = (μ.prod (volume : Measure ℝ)).tilted
      (fun p => E₀ p.1 + u (S w' p) - p.2 ^ 2 / 2) :=
    fun w' => tilted_prod_gaussianReal_zero_one μ _
  simp_rw [hν_eq]
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hSm : ∀ w', Measurable (S w') := fun w' => by
    have hdot : Measurable fun p : E × ℝ => A p.1 ⬝ᵥ w' :=
      Finset.measurable_sum _ fun j _ => ((hAm j).comp measurable_fst).mul_const (w' j)
    exact hdot.add (measurable_snd.const_mul c_A)
  have hem : ∀ z, Measurable (fun p : E × ℝ => E₀ p.1 + u (S (update w k z) p) - p.2 ^ 2 / 2) :=
    fun z => ((hE₀m.comp measurable_fst).add (hum.comp (hSm _))).sub
      ((measurable_snd.pow_const 2).div_const 2)
  have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
  have hconf : ∀ z, ∀ p : E × ℝ,
      E₀ p.1 + u (S (update w k z) p) - p.2 ^ 2 / 2 ≤
        0 + B₀ * ‖p‖ - min κ (1 / 2) * ‖p‖ ^ 2 :=
    fun z => prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 _
  have hS_der : ∀ (p : E × ℝ) (z : ℝ),
      HasDerivAt (fun q => S (update w k q) p) (A p.1 k) z := fun p z => by
    have h1 : ∀ j : K, HasDerivAt (fun q => A p.1 j * update w k q j)
        (if j = k then A p.1 k else 0) z := fun j => by
      by_cases hjk : j = k
      · subst hjk
        simpa [update_self] using ((hasDerivAt_id z).const_mul (A p.1 j))
      · have hup : ∀ q, update w k q j = w j := fun q => update_of_ne hjk q w
        simpa [hjk, hup] using hasDerivAt_const z (A p.1 j * w j)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => h1 j
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
    exact hsum.add_const (c_A * p.2)
  have hed : ∀ (p : E × ℝ) (z : ℝ),
      HasDerivAt (fun q => E₀ p.1 + u (S (update w k q) p) - p.2 ^ 2 / 2)
        (A p.1 k * deriv u (S (update w k z) p)) z := fun p z =>
    ((((hu _).hasDerivAt.comp z (hS_der p z)).const_add (E₀ p.1)).sub_const
      (p.2 ^ 2 / 2)).congr_deriv (mul_comm _ _)
  have he'm : Measurable (fun p : E × ℝ => A p.1 k * deriv u (S (update w k (w k)) p)) := by
    rw [update_eq_self]
    exact ((hAm k).comp measurable_fst).mul (hdu.comp (hSm w))
  have he'b : ∀ z, ∀ p : E × ℝ,
      |A p.1 k * deriv u (S (update w k z) p)| ≤ (|L_A| * |D₁|) * (1 + ‖p‖) ^ n_A := fun z p => by
    rw [abs_mul]
    have h1 : |A p.1 k| ≤ |L_A| * (1 + ‖p‖) ^ n_A :=
      (hAb k p.1).trans (mul_le_mul (le_abs_self _)
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le p) 1) _)
        (by positivity) (abs_nonneg _))
    exact (mul_le_mul h1 ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _)
      (by positivity)).trans_eq (by ring)
  set Ψ' : ℝ → (R → E × ℝ) → ℝ := fun z σ =>
    f (fun r => (σ r).1) * ∑ j : R, A (σ j).1 k * deriv (ψ j) (S (update w k z) (σ j)) *
      ∏ r ∈ Finset.univ.erase j, ψ r (S (update w k z) (σ r))
  have hΦm : ∀ z, Measurable (Φ (update w k z)) := fun z =>
    (hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
      (Finset.measurable_prod _ fun r _ =>
        (hψd r).continuous.measurable.comp ((hSm _).comp (measurable_pi_apply r)))
  have hΦ'm : Measurable (Ψ' (w k)) := by
    dsimp only [Ψ']
    rw [update_eq_self]
    exact (hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
      (Finset.measurable_sum _ fun j _ =>
        ((((hAm k).comp (measurable_fst.comp (measurable_pi_apply j))).mul
          ((measurable_deriv (ψ j)).comp ((hSm w).comp (measurable_pi_apply j)))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp ((hSm w).comp (measurable_pi_apply r)))))
  set C_ψ : ℝ := (1 + |M₀| + |M₁|) ^ Fintype.card R
  have hfb_p : ∀ σ : R → E × ℝ, |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
    abs_comp_le_prod_of_injective hfb norm_fst_le Function.injective_id
  have hΦb : ∀ z, ∀ σ : R → E × ℝ,
      |Φ (update w k z) σ| ≤ (|C_f| * C_ψ * (1 + |L_A| * Fintype.card R)) *
        ∏ r, (1 + ‖σ r‖) ^ (m_f + n_A) := fun z σ => by
    rw [abs_mul]
    have h1 : |∏ r, ψ r (S (update w k z) (σ r))| ≤ C_ψ :=
      abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S (update w k z) (σ r)
    have h2 : ∏ r, (1 + ‖σ r‖) ^ m_f ≤ ∏ r, (1 + ‖σ r‖) ^ (m_f + n_A) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) fun r _ =>
        pow_le_pow_right₀ (by linarith [norm_nonneg (σ r)]) (Nat.le_add_right _ _)
    refine (mul_le_mul (hfb_p σ) h1 (abs_nonneg _) (by positivity)).trans ?_
    calc |C_f| * (∏ r, (1 + ‖σ r‖) ^ m_f) * C_ψ
        ≤ |C_f| * C_ψ * 1 * ∏ r, (1 + ‖σ r‖) ^ (m_f + n_A) := by
          have := mul_le_mul_of_nonneg_left h2
            (mul_nonneg (abs_nonneg C_f) (by positivity : 0 ≤ C_ψ))
          linarith
      _ ≤ (|C_f| * C_ψ * (1 + |L_A| * Fintype.card R)) * ∏ r, (1 + ‖σ r‖) ^ (m_f + n_A) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
            (Finset.prod_nonneg fun _ _ => by positivity)
  have hΦ'b : ∀ z, ∀ σ : R → E × ℝ,
      |Ψ' z σ| ≤ (|C_f| * C_ψ * (1 + |L_A| * Fintype.card R)) *
        ∏ r, (1 + ‖σ r‖) ^ (m_f + n_A) := by
    intro z σ
    have hsum_le : |∑ j : R, A (σ j).1 k * deriv (ψ j) (S (update w k z) (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S (update w k z) (σ r))| ≤
        (C_ψ * (|L_A| * Fintype.card R)) * ∏ r, (1 + ‖σ r‖) ^ n_A := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ j : R, |A (σ j).1 k * deriv (ψ j) (S (update w k z) (σ j)) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S (update w k z) (σ r))| ≤
          (|L_A| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ n_A := fun j => by
        rw [abs_mul, abs_mul]
        have hx : |A (σ j).1 k| ≤ |L_A| * ∏ r, (1 + ‖σ r‖) ^ n_A := by
          have h0 : |A (σ j).1 k| ≤ |L_A| * (1 + ‖σ j‖) ^ n_A :=
            (hAb k (σ j).1).trans (mul_le_mul (le_abs_self _)
              (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ j)) 1) _)
              (by positivity) (abs_nonneg _))
          exact h0.trans (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_A j)
            (abs_nonneg _))
        have hpr : |deriv (ψ j) (S (update w k z) (σ j))| *
            |∏ r ∈ Finset.univ.erase j, ψ r (S (update w k z) (σ r))| ≤ C_ψ :=
          (abs_mul _ _).symm.trans_le
            (abs_deriv_mul_prod_erase_le hM₀ hM₁ j fun r => S (update w k z) (σ r))
        calc |A (σ j).1 k| * |deriv (ψ j) (S (update w k z) (σ j))| *
              |∏ r ∈ Finset.univ.erase j, ψ r (S (update w k z) (σ r))|
            = |A (σ j).1 k| * (|deriv (ψ j) (S (update w k z) (σ j))| *
                |∏ r ∈ Finset.univ.erase j, ψ r (S (update w k z) (σ r))|) := by ring
          _ ≤ (|L_A| * ∏ r, (1 + ‖σ r‖) ^ n_A) * C_ψ :=
                mul_le_mul hx hpr (by positivity) (by positivity)
          _ = (|L_A| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ n_A := by ring
      refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact le_of_eq (by ring)
    refine (abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) hsum_le).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => by positivity)
    have : 0 ≤ |C_f| * C_ψ := by positivity
    nlinarith
  have hΦd : ∀ (σ : R → E × ℝ) (z : ℝ),
      HasDerivAt (fun q => Φ (update w k q) σ) (Ψ' z σ) z := fun σ z => by
    have hprod := HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun r q => ψ r (S (update w k q) (σ r))) fun r _ =>
        ((hψd r _).hasDerivAt.comp z (hS_der (σ r) z))
    refine (hprod.const_mul (f (fun r => (σ r).1))).congr_deriv ?_
    dsimp only [Ψ', smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hmain := hasDerivAt_integral_pi_tilted_of_confining_replicaDiff
    (E := E × ℝ) (μ := μ.prod volume) (R := R) hκ' (s := univ) univ_mem
    (e := fun z p => E₀ p.1 + u (S (update w k z) p) - p.2 ^ 2 / 2)
    (e' := fun z p => A p.1 k * deriv u (S (update w k z) p))
    (Ψ := fun z => Φ (update w k z))
    (Ψ' := Ψ')
    (A := 0) (B := B₀) (L := |L_A| * |D₁|) (n := n_A)
    (C := |C_f| * C_ψ * (1 + |L_A| * Fintype.card R)) (m := m_f + n_A)
    (fun z _ => hem z) he'm
    (fun z _ => hconf z) (fun z _ => he'b z) (fun p z _ => hed p z)
    (fun z _ => hΦm z) hΦ'm
    (fun z _ => hΦb z) (fun z _ => hΦ'b z) (fun σ z _ => hΦd σ z)
  simpa only [Ψ', update_eq_self] using hmain

private theorem add_replicaDiff_prod_eq_sum_sub
    {α : Type*} [MeasurableSpace α] [Fintype R] [DecidableEq R]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (g : (R → α) → ℝ) (hg : Measurable g)
    (a S : α → ℝ) (ha : Measurable a) (hS : Measurable S)
    (u : ℝ → ℝ) (hdu : Measurable (deriv u))
    (ψ : R → ℝ → ℝ) (hψ : ∀ r, Measurable (ψ r))
    (h1 : ∀ j : R, Integrable (fun σ : R → α =>
      g σ * (a (σ j) * deriv (ψ j) (S (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S (σ r)))) (Measure.pi fun _ : R => ν))
    (h2 : ∀ j : R, Integrable (fun σ : R → α =>
      (g σ * ∏ r, ψ r (S (σ r))) * (a (σ j) * deriv u (S (σ j)))) (Measure.pi fun _ : R => ν)) :
    (∫ σ : R → α, g σ * (∑ j : R, a (σ j) * deriv (ψ j) (S (σ j)) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S (σ r))) ∂(Measure.pi fun _ : R => ν)) +
      replicaDiff ν (fun σ => g σ * ∏ r, ψ r (S (σ r))) (fun p => a p * deriv u (S p)) =
    (∑ j : R, ∫ σ : R → α, g σ * a (σ j) *
        ((deriv (ψ j) (S (σ j)) + ψ j (S (σ j)) * deriv u (S (σ j))) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S (σ r))) ∂(Measure.pi fun _ : R => ν)) -
      (Fintype.card R : ℝ) * ∫ σ : Option R → α,
        g (fun r => σ (some r)) * a (σ none) *
          (∏ r, ψ r (S (σ (some r)))) * deriv u (S (σ none))
        ∂(Measure.pi fun _ : Option R => ν) := by
  have hsum1 : (∫ σ : R → α, g σ * (∑ j : R, a (σ j) * deriv (ψ j) (S (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S (σ r))) ∂(Measure.pi fun _ : R => ν)) =
      ∑ j : R, ∫ σ : R → α, g σ * (a (σ j) * deriv (ψ j) (S (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S (σ r))) ∂(Measure.pi fun _ : R => ν) := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ fun j _ => h1 j
  rw [hsum1, replicaDiff_eq]
  have hsome : ∀ j : R,
      (∫ σ : Option R → α,
          (g (fun r => σ (some r)) * ∏ r, ψ r (S (σ (some r)))) *
            (a (σ (some j)) * deriv u (S (σ (some j))))
          ∂(Measure.pi fun _ : Option R => ν)) =
        ∫ σ : R → α,
          (g σ * ∏ r, ψ r (S (σ r))) * (a (σ j) * deriv u (S (σ j)))
          ∂(Measure.pi fun _ : R => ν) := fun j => by
    obtain ⟨G_j, hG_j⟩ : ∃ G_j : (R → α) → ℝ, G_j = fun σ =>
        (g σ * ∏ r, ψ r (S (σ r))) * (a (σ j) * deriv u (S (σ j))) := ⟨_, rfl⟩
    have hm : Measurable G_j := by
      rw [hG_j]
      exact (hg.mul (Finset.measurable_prod _ fun r _ =>
        (hψ r).comp (hS.comp (measurable_pi_apply r)))).mul
        ((ha.comp (measurable_pi_apply j)).mul (hdu.comp (hS.comp (measurable_pi_apply j))))
    have hinj := integral_pi_comp_injective ν (Option.some_injective R) G_j hm.aestronglyMeasurable
    simpa only [hG_j] using hinj
  simp_rw [hsome]
  rw [← add_sub_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_add (h1 j) (h2 j)]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp only
    rw [← Finset.mul_prod_erase Finset.univ (fun r => ψ r (S (σ r))) (Finset.mem_univ j)]
    ring
  · congr 1
    exact integral_congr_ae (ae_of_all _ fun _ => by ring)

/-- A replica average whose observable grows linearly in `w` and polynomially in the replicas is
bounded polynomially in the disorder and is integrable against the Gaussian law of `w`. -/
theorem exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal
    {ι : Type*} [Fintype K] [Fintype ι] {κ : ℝ} (hκ : 0 < κ) (m : ℕ) :
    ∃ A_m : ℝ, 0 ≤ A_m ∧
      ∀ {B₀ c₀ : ℝ}, 0 ≤ B₀ → 0 ≤ c₀ →
        ∀ {E₀ : E → ℝ}, Measurable E₀ →
        (∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2) → (∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x) →
        ∀ (A : E → K → ℝ), (∀ k, Measurable fun x => A x k) →
        ∀ {s_A : ℝ}, 0 ≤ s_A → (∀ k x, ‖x‖ ≤ 1 → |A x k| ≤ s_A) →
        ∀ (c_A : ℝ) {u : ℝ → ℝ}, Differentiable ℝ u → (∀ x, u x ≤ 0) →
        ∀ {D₁ : ℝ}, (∀ x, |deriv u x| ≤ D₁) →
        ∀ {G : (K → ℝ) → (ι → E × ℝ) → ℝ},
        Measurable (fun p : (K → ℝ) × (ι → E × ℝ) => G p.1 p.2) →
        ∀ {C₀ C₁ : ℝ}, 0 ≤ C₀ → 0 ≤ C₁ →
        (∀ w σ, |G w σ| ≤ (C₀ + C₁ * ∑ k, |w k|) * ∏ o, (1 + ‖σ o‖) ^ m) →
        let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
        let ν (w : K → ℝ) :=
          (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2))
        (∀ w, |∫ σ, G w σ ∂(Measure.pi fun _ : ι => ν w)| ≤
          (C₀ + C₁ * ∑ k, |w k|) * A_m ^ Fintype.card ι *
            (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2)) ^
              (m * Fintype.card ι)) ∧
          Integrable (fun w => ∫ σ, G w σ ∂(Measure.pi fun _ : ι => ν w)) γ_sh := by
  obtain ⟨A_m, hAm0, hAm_le⟩ :=
    exists_integral_one_add_norm_pow_tilted_prod_gaussian_le (K := K) μ hκ m
  refine ⟨A_m, hAm0, fun {B₀ c₀} hB₀ hc₀ {E₀} hE₀m hE₀_conf hE₀_low A hAm {s_A} hs_A hA_low
    c_A {u} hu hu0 {D₁} hD₁ {G} hGm {C₀ C₁} hC₀ hC₁ hGb => ?_⟩
  intro γ_sh ν
  have hum : Measurable u := hu.continuous.measurable
  have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
  have hpt : ∀ w, |∫ σ, G w σ ∂(Measure.pi fun _ : ι => ν w)| ≤
      (C₀ + C₁ * ∑ k, |w k|) * A_m ^ Fintype.card ι *
        (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2)) ^
          (m * Fintype.card ι) := fun w => by
    have hν_eq : ν w = (μ.prod (volume : Measure ℝ)).tilted
        (fun p => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2) - p.2 ^ 2 / 2) :=
      tilted_prod_gaussianReal_zero_one μ _
    have hSm : Measurable fun p : E × ℝ => A p.1 ⬝ᵥ w + c_A * p.2 :=
      (Finset.measurable_sum _ fun j _ => ((hAm j).comp measurable_fst).mul_const (w j)).add
        (measurable_snd.const_mul c_A)
    have hem : Measurable fun p : E × ℝ => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2) - p.2 ^ 2 / 2 :=
      ((hE₀m.comp measurable_fst).add (hum.comp hSm)).sub
        ((measurable_snd.pow_const 2).div_const 2)
    have hconf : ∀ p : E × ℝ, E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2) - p.2 ^ 2 / 2 ≤
        0 + B₀ * ‖p‖ - min κ (1 / 2) * ‖p‖ ^ 2 :=
      prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 _
    have h1 : |∫ σ, G w σ ∂(Measure.pi fun _ : ι => ν w)| ≤
        (C₀ + C₁ * ∑ k, |w k|) * (∫ p, (1 + ‖p‖) ^ m ∂(ν w)) ^ Fintype.card ι := by
      simp_rw [hν_eq]
      exact abs_integral_pi_tilted_le_of_confining (μ := μ.prod volume) hκ' hem hconf (hGb w)
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity)
      (hAm_le E₀ hE₀m B₀ c₀ hB₀ hE₀_conf hE₀_low A hAm s_A hs_A hA_low c_A u D₁ hu hu0 hD₁ w)
      (Fintype.card ι)
    have hCw : 0 ≤ C₀ + C₁ * ∑ k, |w k| := by
      have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      positivity
    refine (h1.trans (mul_le_mul_of_nonneg_left h2 hCw)).trans_eq ?_
    rw [mul_pow, ← pow_mul]
    ring
  refine ⟨hpt, ?_⟩
  have hIm : Measurable fun w => ∫ σ, G w σ ∂(Measure.pi fun _ : ι => ν w) := by
    have hν_eq : ∀ w, ν w = (μ.prod (volume : Measure ℝ)).tilted
        (fun p => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2) - p.2 ^ 2 / 2) :=
      fun w => tilted_prod_gaussianReal_zero_one μ _
    simp_rw [hν_eq]
    have he_joint : Measurable fun q : (K → ℝ) × (E × ℝ) =>
        E₀ q.2.1 + u (A q.2.1 ⬝ᵥ q.1 + c_A * q.2.2) - q.2.2 ^ 2 / 2 := by
      have hdot : Measurable fun q : (K → ℝ) × (E × ℝ) => A q.2.1 ⬝ᵥ q.1 :=
        Finset.measurable_sum _ fun k _ =>
          ((hAm k).comp (measurable_fst.comp measurable_snd)).mul
            ((measurable_pi_apply k).comp measurable_fst)
      exact ((hE₀m.comp (measurable_fst.comp measurable_snd)).add
        (hum.comp (hdot.add ((measurable_snd.comp measurable_snd).const_mul c_A)))).sub
        (((measurable_snd.comp measurable_snd).pow_const 2).div_const 2)
    exact measurable_integral_pi_tilted_of_sigmaFinite
      (μ' := μ.prod (volume : Measure ℝ)) he_joint hGm
  set P₀ : ℝ := 1 + C₀ + B₀ + c₀ + |u 0| + |D₁| * |c_A| + 1 / 2
  set P₁ : ℝ := C₁ + |D₁| * s_A
  have hP₀ : 1 ≤ P₀ := by
    dsimp only [P₀]
    linarith [abs_nonneg (u 0), mul_nonneg (abs_nonneg D₁) (abs_nonneg c_A)]
  have hP₁ : 0 ≤ P₁ := by positivity
  set deg : ℕ := m * Fintype.card ι + 1
  have hdom : Integrable (fun w : K → ℝ => A_m ^ Fintype.card ι *
      (P₀ + P₁ * ∑ k, |w k|) ^ deg) γ_sh := by
    have hk : ∀ k : K, MemLp (fun w : K → ℝ => |w k|) deg γ_sh := fun k =>
      ((memLp_id_gaussianReal (μ := 0) (v := 1) deg).comp_measurePreserving
        (measurePreserving_eval (fun _ : K => gaussianReal 0 1) k)).abs
    have hsum : MemLp (fun w : K → ℝ => P₀ + P₁ * ∑ k, |w k|) deg γ_sh :=
      (memLp_const P₀).add ((memLp_finsetSum _ fun k _ => hk k).const_mul P₁)
    refine (hsum.integrable_norm_pow'.congr (ae_of_all _ fun w => ?_)).const_mul _
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  refine hdom.mono' hIm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs]
  refine (hpt w).trans ?_
  have hw0 : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hb1 : C₀ + C₁ * ∑ k, |w k| ≤ P₀ + P₁ * ∑ k, |w k| := by
    dsimp only [P₀, P₁]
    nlinarith [abs_nonneg (u 0), mul_nonneg (abs_nonneg D₁) (abs_nonneg c_A),
      mul_nonneg (mul_nonneg (abs_nonneg D₁) hs_A) hw0]
  have hb2 : 1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2) ≤
      P₀ + P₁ * ∑ k, |w k| := by
    dsimp only [P₀, P₁]
    nlinarith [mul_nonneg hC₁ hw0]
  calc (C₀ + C₁ * ∑ k, |w k|) * A_m ^ Fintype.card ι *
          (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2)) ^
            (m * Fintype.card ι)
      = A_m ^ Fintype.card ι * ((C₀ + C₁ * ∑ k, |w k|) *
          (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_A|)) + 1 / 2)) ^
            (m * Fintype.card ι)) := by ring
    _ ≤ A_m ^ Fintype.card ι * ((P₀ + P₁ * ∑ k, |w k|) *
          (P₀ + P₁ * ∑ k, |w k|) ^ (m * Fintype.card ι)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hb1 (pow_le_pow_left₀ (by positivity) hb2 _) (by positivity) (by positivity))
          (pow_nonneg hAm0 _)
    _ = A_m ^ Fintype.card ι * (P₀ + P₁ * ∑ k, |w k|) ^ deg := by
        dsimp only [deg]; rw [pow_succ']

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem measurable_S_joint {ι : Type*} [Fintype K]
    {A : E → K → ℝ} (hAm : ∀ k, Measurable fun x => A x k) (c_A : ℝ) (i : ι) :
    Measurable fun p : (K → ℝ) × (ι → E × ℝ) => A (p.2 i).1 ⬝ᵥ p.1 + c_A * (p.2 i).2 := by
  have hdot : Measurable fun p : (K → ℝ) × (ι → E × ℝ) => A (p.2 i).1 ⬝ᵥ p.1 :=
    Finset.measurable_sum _ fun j _ =>
      ((hAm j).comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).mul
        ((measurable_pi_apply j).comp measurable_fst)
  exact hdot.add ((measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)).const_mul c_A)

private theorem stein_coord_pi_tilted_prod_gaussianReal [Fintype K]
    [Fintype R] [DecidableEq R]
    {κ B₀ c₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) (hc₀ : 0 ≤ c₀)
    {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x)
    (A : E → K → ℝ) (hAm : ∀ k, Measurable fun x => A x k)
    {L_A : ℝ} {n_A : ℕ} (hAb : ∀ k x, |A x k| ≤ L_A * (1 + ‖x‖) ^ n_A)
    (c_A : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    (k : K) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (w : K → ℝ) (p : E × ℝ) : ℝ := A p.1 ⬝ᵥ w + c_A * p.2
    let ν (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S w p))
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    Integrable (fun w => w k * ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r)) ∂(Measure.pi fun _ : R => ν w)) γ_sh ∧
      (∀ j : R, Integrable (fun w => ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * A (σ j).1 k *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => ν w)) γ_sh) ∧
      Integrable (fun w => ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) * A (σ none).1 k *
            (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => ν w)) γ_sh ∧
      ∫ w, w k * (∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r)) ∂(Measure.pi fun _ : R => ν w)) ∂γ_sh =
        (∑ j : R, ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) * A (σ j).1 k *
              (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
            ∂(Measure.pi fun _ : R => ν w) ∂γ_sh) -
          (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * A (σ none).1 k *
              (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
            ∂(Measure.pi fun _ : Option R => ν w) ∂γ_sh := by
  intro γ_sh S ν ψ_d
  set s_A : ℝ := |L_A| * 2 ^ n_A
  have hs_A : 0 ≤ s_A := by positivity
  have hA_low : ∀ j x, ‖x‖ ≤ 1 → |A x j| ≤ s_A := fun j x hx =>
    (hAb j x).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖x‖ ≤ 2) _)
      (by positivity) (abs_nonneg _))
  set C_ψ : ℝ := (1 + |M₀| + |M₁|) ^ Fintype.card R
  have hfb_p : ∀ σ : R → E × ℝ, |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
    abs_comp_le_prod_of_injective hfb norm_fst_le Function.injective_id
  obtain ⟨_, -, hI1⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal (K := K) (ι := R) μ hκ m_f
  have hLHS_i : Integrable (fun w => w k * ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r)) ∂(Measure.pi fun _ : R => ν w)) γ_sh := by
    have heq : (fun w : K → ℝ => w k * ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r)) ∂(Measure.pi fun _ : R => ν w)) =
      fun w => ∫ σ : R → E × ℝ, w k * (f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => ν w) := funext fun _ => (integral_const_mul _ _).symm
    rw [heq]
    refine (hI1 hB₀ hc₀ hE₀m hE₀_conf hE₀_low A hAm hs_A hA_low c_A hu hu0 hD₁
      (G := fun w σ => w k * (f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r))))
      (((measurable_pi_apply k).comp measurable_fst).mul
        ((hf.comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (measurable_S_joint (ι := R) hAm c_A r))))
      (C₀ := 0) (C₁ := |C_f| * C_ψ) le_rfl (by positivity) fun w σ => ?_).2
    rw [zero_add, abs_mul, abs_mul]
    have hwk : |w k| ≤ ∑ j, |w j| :=
      Finset.single_le_sum (f := fun j => |w j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have hpr : |∏ r, ψ r (S w (σ r))| ≤ C_ψ :=
      abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S w (σ r)
    calc |w k| * (|f (fun r => (σ r).1)| * |∏ r, ψ r (S w (σ r))|)
        ≤ (∑ j, |w j|) * ((|C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f) * C_ψ) :=
          mul_le_mul hwk (mul_le_mul (hfb_p σ) hpr (abs_nonneg _) (by positivity))
            (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ = (|C_f| * C_ψ * ∑ j, |w j|) * ∏ o, (1 + ‖σ o‖) ^ m_f := by ring
  obtain ⟨_, -, hI2⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal
      (K := K) (ι := R) μ hκ (m_f + n_A)
  have hRHS1_i : ∀ j : R, Integrable (fun w => ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * A (σ j).1 k *
        (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
      ∂(Measure.pi fun _ : R => ν w)) γ_sh := fun j => by
    have hj_m := measurable_S_joint (ι := R) hAm c_A j
    refine (hI2 hB₀ hc₀ hE₀m hE₀_conf hE₀_low A hAm hs_A hA_low c_A hu hu0 hD₁
      (G := fun w σ => f (fun r => (σ r).1) * A (σ j).1 k *
        (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))))
      (((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        ((hAm k).comp (measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd)))).mul
        ((((measurable_deriv (ψ j)).comp hj_m).add
          (((hψd j).continuous.measurable.comp hj_m).mul
            ((measurable_deriv u).comp hj_m))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (measurable_S_joint (ι := R) hAm c_A r))))
      (C₀ := |C_f| * (|L_A| * ((1 + |D₁|) * C_ψ))) (C₁ := 0) (by positivity) le_rfl
      fun w σ => ?_).2
    rw [zero_mul, add_zero, mul_assoc]
    have hAj : |A (σ j).1 k * (ψ_d j (S w (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))| ≤
        (|L_A| * ((1 + |D₁|) * C_ψ)) * ∏ r, (1 + ‖σ r‖) ^ n_A := by
      rw [abs_mul]
      have hx : |A (σ j).1 k| ≤ |L_A| * ∏ r, (1 + ‖σ r‖) ^ n_A :=
        ((hAb k (σ j).1).trans (mul_le_mul (le_abs_self _)
          (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ j)) 1) _)
          (by positivity) (abs_nonneg _))).trans
          (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_A j) (abs_nonneg _))
      exact (mul_le_mul hx (abs_tiltedDeriv_mul_prod_erase_le hM₀ hM₁ hD₁ j
        fun r => S w (σ r)) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    exact abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) hAj
  obtain ⟨_, -, hI3⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal
      (K := K) (ι := Option R) μ hκ (m_f + n_A)
  have hRHS2_i : Integrable (fun w => ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * A (σ none).1 k *
        (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
      ∂(Measure.pi fun _ : Option R => ν w)) γ_sh := by
    refine (hI3 hB₀ hc₀ hE₀m hE₀_conf hE₀_low A hAm hs_A hA_low c_A hu hu0 hD₁
      (G := fun w σ => f (fun r => (σ (some r)).1) * A (σ none).1 k *
        (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none)))
      ((((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))).mul
        ((hAm k).comp (measurable_fst.comp ((measurable_pi_apply none).comp measurable_snd)))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp
            (measurable_S_joint (ι := Option R) hAm c_A (some r)))).mul
        ((measurable_deriv u).comp (measurable_S_joint (ι := Option R) hAm c_A none)))
      (C₀ := |C_f| * (|L_A| * (C_ψ * |D₁|))) (C₁ := 0) (by positivity) le_rfl
      fun w σ => ?_).2
    rw [zero_mul, add_zero, mul_assoc, mul_assoc]
    have hf_opt : |f (fun r => (σ (some r)).1)| ≤ |C_f| * ∏ o, (1 + ‖σ o‖) ^ m_f :=
      abs_comp_some_le_prod hfb_p σ
    have hAn : |A (σ none).1 k * ((∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none)))| ≤
        (|L_A| * (C_ψ * |D₁|)) * ∏ o, (1 + ‖σ o‖) ^ n_A := by
      rw [abs_mul, abs_mul]
      have hx : |A (σ none).1 k| ≤ |L_A| * ∏ o, (1 + ‖σ o‖) ^ n_A :=
        ((hAb k (σ none).1).trans (mul_le_mul (le_abs_self _)
          (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ none)) 1) _)
          (by positivity) (abs_nonneg _))).trans
          (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_A none) (abs_nonneg _))
      have hpu : |∏ r, ψ r (S w (σ (some r)))| * |deriv u (S w (σ none))| ≤ C_ψ * |D₁| :=
        mul_le_mul (abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S w (σ (some r)))
          ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
      exact (mul_le_mul hx hpu (by positivity) (by positivity)).trans_eq (by ring)
    exact abs_mul_le_mul_prod_one_add_norm_pow hf_opt hAn
  refine ⟨hLHS_i, hRHS1_i, hRHS2_i, ?_⟩
  classical
  set G_fn : (K → ℝ) → ℝ := fun w =>
    ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r)) ∂(Measure.pi fun _ : R => ν w)
  set G'_fn : (K → ℝ) → ℝ := fun w =>
    (∑ j : R, ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * A (σ j).1 k *
          (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => ν w)) -
      (Fintype.card R : ℝ) * ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * A (σ none).1 k *
          (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
        ∂(Measure.pi fun _ : Option R => ν w)
  have hG_der : ∀ w : K → ℝ, HasDerivAt (fun z => G_fn (update w k z)) (G'_fn w) (w k) := by
    intro w
    refine (hasDerivAt_coord_tilted_prod_gaussian μ hκ hB₀ hE₀m hE₀_conf A hAm hAb c_A
      hu hu0 hD₁ ψ hψd hM₀ hM₁ hf hfb w k).congr_deriv ?_
    have hν_eq : ν w = (μ.prod (volume : Measure ℝ)).tilted
        (fun p => E₀ p.1 + u (S w p) - p.2 ^ 2 / 2) :=
      tilted_prod_gaussianReal_zero_one μ _
    have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
    have hSm : Measurable (S w) :=
      (Finset.measurable_sum _ fun j _ => ((hAm j).comp measurable_fst).mul_const (w j)).add
        (measurable_snd.const_mul c_A)
    have hem : Measurable fun p : E × ℝ => E₀ p.1 + u (S w p) - p.2 ^ 2 / 2 :=
      ((hE₀m.comp measurable_fst).add (hu.continuous.measurable.comp hSm)).sub
        ((measurable_snd.pow_const 2).div_const 2)
    have hconf : ∀ p : E × ℝ, E₀ p.1 + u (S w p) - p.2 ^ 2 / 2 ≤
        0 + B₀ * ‖p‖ - min κ (1 / 2) * ‖p‖ ^ 2 :=
      prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 _
    have : IsProbabilityMeasure (ν w) := by
      rw [hν_eq]; exact isProbabilityMeasure_tilted
        (integrable_exp_of_confining (μ := μ.prod volume) hκ' hem hconf)
    have h1 : ∀ j : R, Integrable (fun σ : R → E × ℝ =>
        f (fun r => (σ r).1) * (A (σ j).1 k * deriv (ψ j) (S w (σ j)) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))) (Measure.pi fun _ : R => ν w) := fun j => by
      rw [hν_eq]
      refine integrable_pi_tilted_of_confining (μ := μ.prod volume) hκ' hem hconf
        ((hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
          ((((hAm k).comp (measurable_fst.comp (measurable_pi_apply j))).mul
            ((measurable_deriv (ψ j)).comp (hSm.comp (measurable_pi_apply j)))).mul
            (Finset.measurable_prod _ fun r _ =>
              (hψd r).continuous.measurable.comp
                (hSm.comp (measurable_pi_apply r))))).aestronglyMeasurable
        (C := |C_f| * (|L_A| * C_ψ)) (m := m_f + n_A) fun σ => ?_
      rw [Real.norm_eq_abs]
      have hx : |A (σ j).1 k| ≤ |L_A| * ∏ r, (1 + ‖σ r‖) ^ n_A :=
        ((hAb k (σ j).1).trans (mul_le_mul (le_abs_self _)
          (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ j)) 1) _)
          (by positivity) (abs_nonneg _))).trans
          (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_A j) (abs_nonneg _))
      have hpr : |deriv (ψ j) (S w (σ j)) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))| ≤ C_ψ :=
        abs_deriv_mul_prod_erase_le hM₀ hM₁ j fun r => S w (σ r)
      have h2' : |A (σ j).1 k * deriv (ψ j) (S w (σ j)) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))| ≤
          (|L_A| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ n_A := by
        rw [mul_assoc, abs_mul]
        exact (mul_le_mul hx hpr (abs_nonneg _) (by positivity)).trans_eq (by ring)
      exact abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) h2'
    have h2 : ∀ j : R, Integrable (fun σ : R → E × ℝ =>
        (f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r))) *
          (A (σ j).1 k * deriv u (S w (σ j)))) (Measure.pi fun _ : R => ν w) := fun j => by
      rw [hν_eq]
      refine integrable_pi_tilted_of_confining (μ := μ.prod volume) hκ' hem hconf
        (((hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hSm.comp (measurable_pi_apply r)))).mul
          (((hAm k).comp (measurable_fst.comp (measurable_pi_apply j))).mul
            ((measurable_deriv u).comp (hSm.comp (measurable_pi_apply j))))).aestronglyMeasurable
        (C := (|C_f| * C_ψ) * (|L_A| * |D₁|)) (m := m_f + n_A) fun σ => ?_
      rw [Real.norm_eq_abs]
      have hp1 : |f (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r))| ≤
          (|C_f| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ m_f := by
        rw [abs_mul]
        have hpr : |∏ r, ψ r (S w (σ r))| ≤ C_ψ :=
          abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S w (σ r)
        exact (mul_le_mul (hfb_p σ) hpr (abs_nonneg _) (by positivity)).trans_eq (by ring)
      have hp2 : |A (σ j).1 k * deriv u (S w (σ j))| ≤
          (|L_A| * |D₁|) * ∏ r, (1 + ‖σ r‖) ^ n_A := by
        rw [abs_mul]
        have hx : |A (σ j).1 k| ≤ |L_A| * ∏ r, (1 + ‖σ r‖) ^ n_A :=
          ((hAb k (σ j).1).trans (mul_le_mul (le_abs_self _)
            (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ j)) 1) _)
            (by positivity) (abs_nonneg _))).trans
            (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_A j) (abs_nonneg _))
        exact (mul_le_mul hx ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _)
          (by positivity)).trans_eq (by ring)
      exact abs_mul_le_mul_prod_one_add_norm_pow hp1 hp2
    exact add_replicaDiff_prod_eq_sum_sub (ν w) (fun σ => f (fun r => (σ r).1))
      (hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r)))
      (fun p => A p.1 k) (S w) ((hAm k).comp measurable_fst) hSm u (measurable_deriv u)
      ψ (fun r => (hψd r).continuous.measurable) h1 h2
  have hG'_int : Integrable G'_fn γ_sh :=
    (integrable_finsetSum _ fun j _ => hRHS1_i j).sub (hRHS2_i.const_mul _)
  have hstein := integral_eval_mul_pi_gaussianReal_eq_of_coord (fun _ : K => (1 : ℝ≥0)) k
    hG_der hLHS_i hG'_int
  rw [NNReal.coe_one, one_mul] at hstein
  refine hstein.trans ?_
  dsimp only [G'_fn]
  rw [integral_sub (integrable_finsetSum _ fun j _ => hRHS1_i j) (hRHS2_i.const_mul _),
    integral_finsetSum _ fun j _ => hRHS1_i j, integral_const_mul]

/-- Replica observables of polynomial growth are integrable for the extended Gibbs state. -/
theorem integrable_pi_tilted_prod_gaussianReal_of_poly [Fintype K] {ι : Type*} [Fintype ι]
    {κ B₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (A : E → K → ℝ) (hAm : ∀ k, Measurable fun x => A x k)
    (c_A : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    (w : K → ℝ) (G : (ι → E × ℝ) → ℝ) (hGm : Measurable G) {C : ℝ} {m : ℕ}
    (hGb : ∀ σ, |G σ| ≤ C * ∏ o, (1 + ‖σ o‖) ^ m) :
    Integrable G (Measure.pi fun _ : ι =>
      ((μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2)))) := by
  rw [tilted_prod_gaussianReal_zero_one μ]
  have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
  have hSm : Measurable fun p : E × ℝ => A p.1 ⬝ᵥ w + c_A * p.2 :=
    (Finset.measurable_sum _ fun j _ => ((hAm j).comp measurable_fst).mul_const (w j)).add
      (measurable_snd.const_mul c_A)
  have hem : Measurable fun p : E × ℝ => E₀ p.1 + u (A p.1 ⬝ᵥ w + c_A * p.2) - p.2 ^ 2 / 2 :=
    ((hE₀m.comp measurable_fst).add (hu.continuous.measurable.comp hSm)).sub
      ((measurable_snd.pow_const 2).div_const 2)
  exact integrable_pi_tilted_of_confining (μ := μ.prod volume) hκ' hem
    (prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 _) hGm.aestronglyMeasurable
    (fun σ => by simpa only [Real.norm_eq_abs] using hGb σ)

/-- **Joint Gaussian integration by parts in `(w, ξ^{i₀})`** for an `R`-replica expectation of a
polynomially growing observable under `(μ.prod (gaussianReal 0 1)).tilted (E₀ + u ∘ S)`. -/
theorem stein_pi_tilted_prod_gaussianReal [Fintype K]
    [Fintype R] [DecidableEq R]
    {κ B₀ c₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀)
    {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x)
    (A B : E → K → ℝ) (hAm : ∀ k, Measurable fun x => A x k)
    (hBm : ∀ k, Measurable fun x => B x k)
    {L_A L_B : ℝ} {n_A n_B : ℕ}
    (hAb : ∀ k x, |A x k| ≤ L_A * (1 + ‖x‖) ^ n_A)
    (hBb : ∀ k x, |B x k| ≤ L_B * (1 + ‖x‖) ^ n_B)
    (c_A c_B : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    (i₀ : R) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (w : K → ℝ) (p : E × ℝ) : ℝ := A p.1 ⬝ᵥ w + c_A * p.2
    let W (w : K → ℝ) (p : E × ℝ) : ℝ := B p.1 ⬝ᵥ w + c_B * p.2
    let ν (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S w p))
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    Integrable (fun w => ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * W w (σ i₀) * ∏ r, ψ r (S w (σ r))
        ∂(Measure.pi fun _ : R => ν w)) γ_sh ∧
      (∀ j : R, Integrable (fun w => ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) *
            (B (σ i₀).1 ⬝ᵥ A (σ j).1 + if j = i₀ then c_B * c_A else 0) *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => ν w)) γ_sh) ∧
      Integrable (fun w => ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) * (B (σ (some i₀)).1 ⬝ᵥ A (σ none).1) *
            (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => ν w)) γ_sh ∧
      ∫ w, ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * W w (σ i₀) * ∏ r, ψ r (S w (σ r))
          ∂(Measure.pi fun _ : R => ν w) ∂γ_sh =
        (∑ j : R, ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) *
              (B (σ i₀).1 ⬝ᵥ A (σ j).1 + if j = i₀ then c_B * c_A else 0) *
              (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
            ∂(Measure.pi fun _ : R => ν w) ∂γ_sh) -
          (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * (B (σ (some i₀)).1 ⬝ᵥ A (σ none).1) *
              (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
            ∂(Measure.pi fun _ : Option R => ν w) ∂γ_sh := by
  intro γ_sh S W ν ψ_d
  have hc₀ : 0 ≤ c₀ := nonneg_of_confining_of_neg_le hE₀_conf hE₀_low
  set s_A : ℝ := |L_A| * 2 ^ n_A
  have hs_A : 0 ≤ s_A := by positivity
  have hA_low : ∀ j x, ‖x‖ ≤ 1 → |A x j| ≤ s_A := fun j x hx =>
    (hAb j x).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖x‖ ≤ 2) _)
      (by positivity) (abs_nonneg _))
  set C_ψ : ℝ := (1 + |M₀| + |M₁|) ^ Fintype.card R
  have hfb_p : ∀ σ : R → E × ℝ, |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
    abs_comp_le_prod_of_injective hfb norm_fst_le Function.injective_id
  have hcoord : ∀ k : K,
      Integrable (fun w => w k * ∫ σ : R → E × ℝ,
          (f (fun r => (σ r).1) * B (σ i₀).1 k) * ∏ r, ψ r (S w (σ r))
          ∂(Measure.pi fun _ : R => ν w)) γ_sh ∧
        (∀ j : R, Integrable (fun w => ∫ σ : R → E × ℝ,
            (f (fun r => (σ r).1) * B (σ i₀).1 k) * A (σ j).1 k *
              (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
            ∂(Measure.pi fun _ : R => ν w)) γ_sh) ∧
        Integrable (fun w => ∫ σ : Option R → E × ℝ,
            (f (fun r => (σ (some r)).1) * B (σ (some i₀)).1 k) * A (σ none).1 k *
              (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
            ∂(Measure.pi fun _ : Option R => ν w)) γ_sh ∧
        ∫ w, w k * (∫ σ : R → E × ℝ,
            (f (fun r => (σ r).1) * B (σ i₀).1 k) * ∏ r, ψ r (S w (σ r))
            ∂(Measure.pi fun _ : R => ν w)) ∂γ_sh =
          (∑ j : R, ∫ w, ∫ σ : R → E × ℝ,
              (f (fun r => (σ r).1) * B (σ i₀).1 k) * A (σ j).1 k *
                (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
              ∂(Measure.pi fun _ : R => ν w) ∂γ_sh) -
            (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → E × ℝ,
              (f (fun r => (σ (some r)).1) * B (σ (some i₀)).1 k) * A (σ none).1 k *
                (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
              ∂(Measure.pi fun _ : Option R => ν w) ∂γ_sh := fun k => by
    have hfk_m : Measurable fun a : R → E => f a * B (a i₀) k :=
      hf.mul ((hBm k).comp (measurable_pi_apply i₀))
    have hfk_b : ∀ a : R → E, |f a * B (a i₀) k| ≤
        (|C_f| * |L_B|) * ∏ r, (1 + ‖a r‖) ^ (m_f + n_B) := fun a => by
      have hfa : |f a| ≤ |C_f| * ∏ r, (1 + ‖a r‖) ^ m_f :=
        (hfb a).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
          (Finset.prod_nonneg fun _ _ => by positivity))
      have hBa : |B (a i₀) k| ≤ |L_B| * ∏ r, (1 + ‖a r‖) ^ n_B :=
        ((hBb k (a i₀)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))).trans
          (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod a n_B i₀) (abs_nonneg _))
      exact abs_mul_le_mul_prod_one_add_norm_pow hfa hBa
    exact stein_coord_pi_tilted_prod_gaussianReal μ hκ hB₀ hc₀ hE₀m hE₀_conf hE₀_low
      A hAm hAb c_A hu hu0 hD₁ ψ hψd hM₀ hM₁ hfk_m hfk_b k
  -- Integrability of the `c_B * (σ i₀).2` piece under `γ_sh`:
  obtain ⟨_, -, hI_ξ⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal
      (K := K) (ι := R) μ hκ (m_f + 1)
  have hξ_LHS_i : Integrable (fun w => ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * (c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r))
      ∂(Measure.pi fun _ : R => ν w)) γ_sh := by
    refine (hI_ξ hB₀ hc₀ hE₀m hE₀_conf hE₀_low A hAm hs_A hA_low c_A hu hu0 hD₁
      (G := fun w σ => f (fun r => (σ r).1) * (c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r)))
      (((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        ((measurable_snd.comp ((measurable_pi_apply i₀).comp measurable_snd)).const_mul c_B)).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp (measurable_S_joint (ι := R) hAm c_A r)))
      (C₀ := |C_f| * (|c_B| * C_ψ)) (C₁ := 0) (by positivity) le_rfl fun w σ => ?_).2
    rw [zero_mul, add_zero, mul_assoc]
    have h2 : |(c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r))| ≤
        (|c_B| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ 1 := by
      rw [abs_mul, abs_mul]
      have hξ : |(σ i₀).2| ≤ ∏ r, (1 + ‖σ r‖) ^ 1 := by
        have h0 : |(σ i₀).2| ≤ (1 + ‖σ i₀‖) ^ 1 := by
          rw [pow_one]
          exact ((by simpa using norm_snd_le (σ i₀) : |(σ i₀).2| ≤ ‖σ i₀‖)).trans
            (le_add_of_nonneg_left zero_le_one)
        exact h0.trans (one_add_norm_pow_le_prod σ 1 i₀)
      have hpr : |∏ r, ψ r (S w (σ r))| ≤ C_ψ :=
        abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S w (σ r)
      calc |c_B| * |(σ i₀).2| * |∏ r, ψ r (S w (σ r))|
          ≤ |c_B| * (∏ r, (1 + ‖σ r‖) ^ 1) * C_ψ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hξ (abs_nonneg _)) hpr (abs_nonneg _)
              (by positivity)
        _ = (|c_B| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ 1 := by ring
    exact abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) h2
  obtain ⟨_, -, hI_ξR⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal (K := K) (ι := R) μ hκ m_f
  have hξ_RHS_i : Integrable (fun w => c_B * c_A * ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * (ψ_d i₀ (S w (σ i₀)) *
        ∏ r ∈ Finset.univ.erase i₀, ψ r (S w (σ r)))
      ∂(Measure.pi fun _ : R => ν w)) γ_sh := by
    have hi₀_m := measurable_S_joint (ι := R) hAm c_A i₀
    refine (hI_ξR hB₀ hc₀ hE₀m hE₀_conf hE₀_low A hAm hs_A hA_low c_A hu hu0 hD₁
      (G := fun w σ => f (fun r => (σ r).1) * (ψ_d i₀ (S w (σ i₀)) *
        ∏ r ∈ Finset.univ.erase i₀, ψ r (S w (σ r))))
      ((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        ((((measurable_deriv (ψ i₀)).comp hi₀_m).add
          (((hψd i₀).continuous.measurable.comp hi₀_m).mul
            ((measurable_deriv u).comp hi₀_m))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (measurable_S_joint (ι := R) hAm c_A r))))
      (C₀ := |C_f| * ((1 + |D₁|) * C_ψ)) (C₁ := 0) (by positivity) le_rfl fun w σ => ?_).2.const_mul
      (c_B * c_A)
    rw [zero_mul, add_zero, abs_mul]
    exact (mul_le_mul (hfb_p σ) (abs_tiltedDeriv_mul_prod_erase_le hM₀ hM₁ hD₁ i₀
      fun r => S w (σ r)) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  -- Pointwise in `w`, combine the `K` coordinates and `(σ i₀).2` inside the replica integrals!
  have hν_prob_int : ∀ w : K → ℝ,
      IsProbabilityMeasure (ν w) ∧
      (∀ k : K, Integrable (fun σ : R → E × ℝ =>
        (f (fun r => (σ r).1) * B (σ i₀).1 k) * ∏ r, ψ r (S w (σ r)))
        (Measure.pi fun _ : R => ν w)) ∧
      Integrable (fun σ : R → E × ℝ =>
        f (fun r => (σ r).1) * (c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r)))
        (Measure.pi fun _ : R => ν w) ∧
      (∀ (j : R) (k : K), Integrable (fun σ : R → E × ℝ =>
        (f (fun r => (σ r).1) * B (σ i₀).1 k) * A (σ j).1 k *
          (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))))
        (Measure.pi fun _ : R => ν w)) ∧
      Integrable (fun σ : R → E × ℝ =>
        f (fun r => (σ r).1) * (ψ_d i₀ (S w (σ i₀)) *
          ∏ r ∈ Finset.univ.erase i₀, ψ r (S w (σ r))))
        (Measure.pi fun _ : R => ν w) ∧
      (∀ k : K, Integrable (fun σ : Option R → E × ℝ =>
        (f (fun r => (σ (some r)).1) * B (σ (some i₀)).1 k) * A (σ none).1 k *
          (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none)))
        (Measure.pi fun _ : Option R => ν w)) := fun w => by
    have hν_eq : ν w = (μ.prod (volume : Measure ℝ)).tilted
        (fun p => E₀ p.1 + u (S w p) - p.2 ^ 2 / 2) :=
      tilted_prod_gaussianReal_zero_one μ _
    have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
    have hSm : Measurable (S w) :=
      (Finset.measurable_sum _ fun j _ => ((hAm j).comp measurable_fst).mul_const (w j)).add
        (measurable_snd.const_mul c_A)
    have hem : Measurable fun p : E × ℝ => E₀ p.1 + u (S w p) - p.2 ^ 2 / 2 :=
      ((hE₀m.comp measurable_fst).add (hu.continuous.measurable.comp hSm)).sub
        ((measurable_snd.pow_const 2).div_const 2)
    have hconf : ∀ p : E × ℝ, E₀ p.1 + u (S w p) - p.2 ^ 2 / 2 ≤
        0 + B₀ * ‖p‖ - min κ (1 / 2) * ‖p‖ ^ 2 :=
      prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 _
    have hprob : IsProbabilityMeasure (ν w) := by
      rw [hν_eq]; exact isProbabilityMeasure_tilted
        (integrable_exp_of_confining (μ := μ.prod volume) hκ' hem hconf)
    have hpr_R_le : ∀ σ : R → E × ℝ, |∏ r, ψ r (S w (σ r))| ≤ C_ψ := fun σ =>
      abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S w (σ r)
    have hpr_O_le : ∀ σ : Option R → E × ℝ, |∏ r, ψ r (S w (σ (some r)))| ≤ C_ψ := fun σ =>
      abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S w (σ (some r))
    have hψd_le : ∀ (j : R) (σ : R → E × ℝ),
        |ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))| ≤
          (1 + |D₁|) * C_ψ := fun j σ =>
      abs_tiltedDeriv_mul_prod_erase_le hM₀ hM₁ hD₁ j fun r => S w (σ r)
    have hf_R : Measurable fun σ : R → E × ℝ => f (fun r => (σ r).1) :=
      hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))
    have hf_O : Measurable fun σ : Option R → E × ℝ => f (fun r => (σ (some r)).1) :=
      hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply (some r)))
    have hpr_R : Measurable fun σ : R → E × ℝ => ∏ r, ψ r (S w (σ r)) :=
      Finset.measurable_prod _ fun r _ =>
        (hψd r).continuous.measurable.comp (hSm.comp (measurable_pi_apply r))
    have hψd_m : ∀ j : R, Measurable fun σ : R → E × ℝ =>
        ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)) := fun j =>
      (((measurable_deriv (ψ j)).comp (hSm.comp (measurable_pi_apply j))).add
        (((hψd j).continuous.measurable.comp (hSm.comp (measurable_pi_apply j))).mul
          ((measurable_deriv u).comp (hSm.comp (measurable_pi_apply j))))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp (hSm.comp (measurable_pi_apply r)))
    have hB_R : ∀ (k : K) (o : R) (σ : R → E × ℝ),
        |B (σ o).1 k| ≤ |L_B| * ∏ o', (1 + ‖σ o'‖) ^ n_B := fun k o σ =>
      ((hBb k (σ o).1).trans (mul_le_mul (le_abs_self _)
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o)) 1) _)
        (by positivity) (abs_nonneg _))).trans
        (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_B o) (abs_nonneg _))
    have hA_R : ∀ (k : K) (o : R) (σ : R → E × ℝ),
        |A (σ o).1 k| ≤ |L_A| * ∏ o', (1 + ‖σ o'‖) ^ n_A := fun k o σ =>
      ((hAb k (σ o).1).trans (mul_le_mul (le_abs_self _)
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o)) 1) _)
        (by positivity) (abs_nonneg _))).trans
        (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_A o) (abs_nonneg _))
    have hB_O : ∀ (k : K) (o : Option R) (σ : Option R → E × ℝ),
        |B (σ o).1 k| ≤ |L_B| * ∏ o', (1 + ‖σ o'‖) ^ n_B := fun k o σ =>
      ((hBb k (σ o).1).trans (mul_le_mul (le_abs_self _)
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o)) 1) _)
        (by positivity) (abs_nonneg _))).trans
        (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_B o) (abs_nonneg _))
    have hA_O : ∀ (k : K) (o : Option R) (σ : Option R → E × ℝ),
        |A (σ o).1 k| ≤ |L_A| * ∏ o', (1 + ‖σ o'‖) ^ n_A := fun k o σ =>
      ((hAb k (σ o).1).trans (mul_le_mul (le_abs_self _)
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o)) 1) _)
        (by positivity) (abs_nonneg _))).trans
        (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n_A o) (abs_nonneg _))
    refine ⟨hprob, fun k => ?_, ?_, fun j k => ?_, ?_, fun k => ?_⟩
    · refine integrable_pi_tilted_prod_gaussianReal_of_poly μ hκ hB₀ hE₀m hE₀_conf A hAm c_A
        hu hu0 w _ ((hf_R.mul ((hBm k).comp (measurable_fst.comp (measurable_pi_apply i₀)))).mul
          hpr_R) (C := (|C_f| * |L_B|) * C_ψ) (m := m_f + n_B) (fun σ : R → E × ℝ => ?_)
      have h1 := abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) (hB_R k i₀ σ)
      rw [abs_mul]
      exact (mul_le_mul h1 (hpr_R_le σ) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    · refine integrable_pi_tilted_prod_gaussianReal_of_poly μ hκ hB₀ hE₀m hE₀_conf A hAm c_A
        hu hu0 w _ ((hf_R.mul ((measurable_snd.comp (measurable_pi_apply i₀)).const_mul c_B)).mul
          hpr_R) (C := |C_f| * (|c_B| * C_ψ)) (m := m_f + 1) (fun σ : R → E × ℝ => ?_)
      have hξ : |c_B * (σ i₀).2| ≤ |c_B| * ∏ r, (1 + ‖σ r‖) ^ 1 := by
        rw [abs_mul]
        have h0 : |(σ i₀).2| ≤ (1 + ‖σ i₀‖) ^ 1 := by
          rw [pow_one]
          have hsnd : |(σ i₀).2| ≤ ‖σ i₀‖ := by
            rw [← Real.norm_eq_abs]; exact norm_snd_le (σ i₀)
          exact hsnd.trans (le_add_of_nonneg_left zero_le_one)
        exact mul_le_mul_of_nonneg_left (h0.trans (one_add_norm_pow_le_prod σ 1 i₀)) (abs_nonneg _)
      have h2 : |(c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r))| ≤
          (|c_B| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ 1 := by
        rw [abs_mul]
        exact (mul_le_mul hξ (hpr_R_le σ) (abs_nonneg _) (by positivity)).trans_eq (by ring)
      have h3 := abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) h2
      simpa only [mul_assoc] using h3
    · refine integrable_pi_tilted_prod_gaussianReal_of_poly μ hκ hB₀ hE₀m hE₀_conf A hAm c_A
        hu hu0 w _ (((hf_R.mul ((hBm k).comp (measurable_fst.comp (measurable_pi_apply i₀)))).mul
          ((hAm k).comp (measurable_fst.comp (measurable_pi_apply j)))).mul (hψd_m j))
        (C := ((|C_f| * |L_B|) * |L_A|) * ((1 + |D₁|) * C_ψ)) (m := (m_f + n_B) + n_A)
        (fun σ : R → E × ℝ => ?_)
      have h12 := abs_mul_le_mul_prod_one_add_norm_pow
        (abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) (hB_R k i₀ σ)) (hA_R k j σ)
      rw [abs_mul]
      exact (mul_le_mul h12 (hψd_le j σ) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    · refine integrable_pi_tilted_prod_gaussianReal_of_poly μ hκ hB₀ hE₀m hE₀_conf A hAm c_A
        hu hu0 w _ (hf_R.mul (hψd_m i₀)) (C := |C_f| * ((1 + |D₁|) * C_ψ)) (m := m_f)
        (fun σ : R → E × ℝ => ?_)
      rw [abs_mul]
      exact (mul_le_mul (hfb_p σ) (hψd_le i₀ σ) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    · refine integrable_pi_tilted_prod_gaussianReal_of_poly μ hκ hB₀ hE₀m hE₀_conf A hAm c_A
        hu hu0 w _ ((((hf_O.mul
          ((hBm k).comp (measurable_fst.comp (measurable_pi_apply (some i₀))))).mul
          ((hAm k).comp (measurable_fst.comp (measurable_pi_apply none)))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hSm.comp (measurable_pi_apply (some r))))).mul
          ((measurable_deriv u).comp (hSm.comp (measurable_pi_apply none))))
        (C := ((|C_f| * |L_B|) * |L_A|) * (C_ψ * |D₁|)) (m := (m_f + n_B) + n_A)
        (fun σ : Option R → E × ℝ => ?_)
      have hf_o : |f (fun r => (σ (some r)).1)| ≤ |C_f| * ∏ o, (1 + ‖σ o‖) ^ m_f :=
        abs_comp_some_le_prod hfb_p σ
      have h12 : |(f fun r => (σ (some r)).1) * B (σ (some i₀)).1 k * A (σ none).1 k| ≤
          (|C_f| * |L_B| * |L_A|) * ∏ o, (1 + ‖σ o‖) ^ ((m_f + n_B) + n_A) :=
        abs_mul_le_mul_prod_one_add_norm_pow
          (abs_mul_le_mul_prod_one_add_norm_pow hf_o (hB_O k (some i₀) σ)) (hA_O k none σ)
      have h34 : |(∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))| ≤ C_ψ * |D₁| := by
        rw [abs_mul]
        exact mul_le_mul (hpr_O_le σ) ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
      rw [mul_assoc (_ * _ * _), abs_mul]
      exact (mul_le_mul h12 h34 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  -- Pointwise decompositions in `w`:
  have hLHS_pt : ∀ w : K → ℝ,
      (∫ σ : R → E × ℝ, f (fun r => (σ r).1) * W w (σ i₀) * ∏ r, ψ r (S w (σ r))
        ∂(Measure.pi fun _ : R => ν w)) =
      (∑ k : K, w k * ∫ σ : R → E × ℝ,
          (f (fun r => (σ r).1) * B (σ i₀).1 k) * ∏ r, ψ r (S w (σ r))
          ∂(Measure.pi fun _ : R => ν w)) +
        ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * (c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r))
          ∂(Measure.pi fun _ : R => ν w) := fun w => by
    obtain ⟨_, hk_i, hξ_i, -, -, -⟩ := hν_prob_int w
    have hpt : ∀ σ : R → E × ℝ,
        f (fun r => (σ r).1) * W w (σ i₀) * ∏ r, ψ r (S w (σ r)) =
        (∑ k : K, w k * ((f (fun r => (σ r).1) * B (σ i₀).1 k) * ∏ r, ψ r (S w (σ r)))) +
          f (fun r => (σ r).1) * (c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r)) := fun σ => by
      dsimp only [W, dotProduct]
      rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1; refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hpt]
    rw [integral_add (integrable_finsetSum _ fun k _ => (hk_i k).const_mul (w k)) hξ_i,
      integral_finsetSum _ fun k _ => (hk_i k).const_mul (w k)]
    congr 1; exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hRHS1_pt : ∀ (j : R) (w : K → ℝ),
      (∫ σ : R → E × ℝ, f (fun r => (σ r).1) *
          (B (σ i₀).1 ⬝ᵥ A (σ j).1 + if j = i₀ then c_B * c_A else 0) *
          (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => ν w)) =
      (∑ k : K, ∫ σ : R → E × ℝ,
          (f (fun r => (σ r).1) * B (σ i₀).1 k) * A (σ j).1 k *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => ν w)) +
        if j = i₀ then c_B * c_A * ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) *
              (ψ_d i₀ (S w (σ i₀)) * ∏ r ∈ Finset.univ.erase i₀, ψ r (S w (σ r)))
            ∂(Measure.pi fun _ : R => ν w)
          else 0 := fun j w => by
    obtain ⟨_, -, -, hjk_i, hξR_i, -⟩ := hν_prob_int w
    by_cases hji : j = i₀
    · subst hji
      simp only [↓reduceIte]
      have hpt : ∀ σ : R → E × ℝ,
          f (fun r => (σ r).1) * (B (σ j).1 ⬝ᵥ A (σ j).1 + c_B * c_A) *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))) =
          (∑ k : K, (f (fun r => (σ r).1) * B (σ j).1 k) * A (σ j).1 k *
              (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))) +
            (c_B * c_A) * (f (fun r => (σ r).1) *
              (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))) := fun σ => by
        dsimp only [dotProduct]
        rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by ring
        · ring
      simp_rw [hpt]
      rw [integral_add (integrable_finsetSum _ fun k _ => hjk_i j k) (hξR_i.const_mul _),
        integral_finsetSum _ fun k _ => hjk_i j k, integral_const_mul]
    · simp only [hji, ↓reduceIte, add_zero]
      have hpt : ∀ σ : R → E × ℝ,
          f (fun r => (σ r).1) * (B (σ i₀).1 ⬝ᵥ A (σ j).1) *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))) =
          ∑ k : K, (f (fun r => (σ r).1) * B (σ i₀).1 k) * A (σ j).1 k *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))) := fun σ => by
        dsimp only [dotProduct]
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp_rw [hpt]
      exact integral_finsetSum _ fun k _ => hjk_i j k
  have hRHS2_pt : ∀ w : K → ℝ,
      (∫ σ : Option R → E × ℝ, f (fun r => (σ (some r)).1) *
          (B (σ (some i₀)).1 ⬝ᵥ A (σ none).1) *
          (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
        ∂(Measure.pi fun _ : Option R => ν w)) =
      ∑ k : K, ∫ σ : Option R → E × ℝ,
        (f (fun r => (σ (some r)).1) * B (σ (some i₀)).1 k) * A (σ none).1 k *
          (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
        ∂(Measure.pi fun _ : Option R => ν w) := fun w => by
    obtain ⟨_, -, -, -, -, hopt_i⟩ := hν_prob_int w
    have hpt : ∀ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * (B (σ (some i₀)).1 ⬝ᵥ A (σ none).1) *
          (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none)) =
        ∑ k : K, (f (fun r => (σ (some r)).1) * B (σ (some i₀)).1 k) * A (σ none).1 k *
          (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none)) := fun σ => by
      dsimp only [dotProduct]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hpt]
    exact integral_finsetSum _ fun k _ => hopt_i k
  -- Assemble all four claims!
  have h1_int : Integrable (fun w => ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * W w (σ i₀) * ∏ r, ψ r (S w (σ r))
      ∂(Measure.pi fun _ : R => ν w)) γ_sh := by
    simp_rw [hLHS_pt]
    exact (integrable_finsetSum _ fun k _ => (hcoord k).1).add hξ_LHS_i
  have h2_int : ∀ j : R, Integrable (fun w => ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) *
        (B (σ i₀).1 ⬝ᵥ A (σ j).1 + if j = i₀ then c_B * c_A else 0) *
        (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
      ∂(Measure.pi fun _ : R => ν w)) γ_sh := fun j => by
    simp_rw [hRHS1_pt j]
    refine (integrable_finsetSum _ fun k _ => (hcoord k).2.1 j).add ?_
    by_cases hji : j = i₀
    · simp only [hji, ↓reduceIte]; exact hξ_RHS_i
    · simp only [hji, ↓reduceIte]; exact integrable_zero _ _ _
  have h3_int : Integrable (fun w => ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * (B (σ (some i₀)).1 ⬝ᵥ A (σ none).1) *
        (∏ r, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
      ∂(Measure.pi fun _ : Option R => ν w)) γ_sh := by
    simp_rw [hRHS2_pt]
    exact integrable_finsetSum _ fun k _ => (hcoord k).2.2.1
  refine ⟨h1_int, h2_int, h3_int, ?_⟩
  -- For the `(σ i₀).2` Stein piece:
  have hξ_eq : ∀ w : K → ℝ,
      (∫ σ : R → E × ℝ, f (fun r => (σ r).1) * (c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r))
        ∂(Measure.pi fun _ : R => ν w)) =
      c_B * c_A * ∫ σ : R → E × ℝ, f (fun r => (σ r).1) *
        (ψ_d i₀ (S w (σ i₀)) * ∏ r ∈ Finset.univ.erase i₀, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => ν w) := fun w => by
    have hcB_pull : (fun σ : R → E × ℝ =>
        f (fun r => (σ r).1) * (c_B * (σ i₀).2) * ∏ r, ψ r (S w (σ r))) =
      fun σ => c_B * (f (fun r => (σ r).1) * (σ i₀).2 * ∏ r, ψ r (S w (σ r))) :=
      funext fun _ => by ring
    have haw : Measurable fun x : E => A x ⬝ᵥ w :=
      Finset.measurable_sum _ fun k _ => (hAm k).mul_const (w k)
    rw [hcB_pull, integral_const_mul,
      integral_snd_pi_tilted_prod_gaussianReal μ hκ hB₀ hE₀m haw
        hE₀_conf c_A hu hu0 hD₁ ψ hψd hM₀ hM₁ hf hfb i₀]
    rw [← mul_assoc]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun _ => by dsimp only [ψ_d]; ring)
  simp_rw [hLHS_pt, hRHS1_pt, hRHS2_pt]
  rw [integral_add (integrable_finsetSum _ fun k _ => (hcoord k).1) hξ_LHS_i,
    integral_finsetSum _ fun k _ => (hcoord k).1]
  simp_rw [hξ_eq]
  have hsum_j : ∀ j : R,
      (∫ w, ((∑ k : K, ∫ σ : R → E × ℝ,
          (f (fun r => (σ r).1) * B (σ i₀).1 k) * A (σ j).1 k *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => ν w)) +
        if j = i₀ then c_B * c_A * ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) *
              (ψ_d i₀ (S w (σ i₀)) * ∏ r ∈ Finset.univ.erase i₀, ψ r (S w (σ r)))
            ∂(Measure.pi fun _ : R => ν w)
          else 0) ∂γ_sh) =
      (∑ k : K, ∫ w, ∫ σ : R → E × ℝ,
          (f (fun r => (σ r).1) * B (σ i₀).1 k) * A (σ j).1 k *
            (ψ_d j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => ν w) ∂γ_sh) +
        if j = i₀ then ∫ w, c_B * c_A * ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) *
              (ψ_d i₀ (S w (σ i₀)) * ∏ r ∈ Finset.univ.erase i₀, ψ r (S w (σ r)))
            ∂(Measure.pi fun _ : R => ν w) ∂γ_sh
          else 0 := fun j => by
    by_cases hji : j = i₀
    · simp only [hji, ↓reduceIte]
      rw [integral_add (integrable_finsetSum _ fun k _ => (hcoord k).2.1 i₀) hξ_RHS_i,
        integral_finsetSum _ fun k _ => (hcoord k).2.1 i₀]
    · simp only [hji, ↓reduceIte, add_zero]
      exact integral_finsetSum _ fun k _ => (hcoord k).2.1 j
  simp_rw [hsum_j, (hcoord _).2.2.2]
  rw [integral_finsetSum _ fun k _ => (hcoord k).2.2.1, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i₀]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_comm]
  ring

/-- Pointwise in `w`, the derivative in `v ∈ (0, 1)` of an `R`-replica expectation along
`S_v(w, (x, ξ)) = √v (X x ⬝ᵥ w) + √(1 - v) (Y ⬝ᵥ w + c_ξ ξ)` under a confined base energy `E₀`. -/
private theorem hasDerivAt_pi_tilted_prod_gaussianReal_sqrt_w [Fintype K] [Fintype R]
    [DecidableEq R] {κ B₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    (w : K → ℝ) {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let S (v : ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let S' (v : ℝ) (p : E × ℝ) : ℝ :=
      (1 / (2 * Real.sqrt v)) * (X p.1 ⬝ᵥ w) - (1 / (2 * Real.sqrt (1 - v))) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (v : ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S v p))
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    HasDerivAt
      (fun v => ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v (σ r))
        ∂(Measure.pi fun _ : R => ν v))
      ((∑ i : R, ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * S' v₀ (σ i) *
            (ψ_d i (S v₀ (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ (σ r)))
          ∂(Measure.pi fun _ : R => ν v₀)) -
        (Fintype.card R : ℝ) * ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) * S' v₀ (σ none) *
            (∏ r, ψ r (S v₀ (σ (some r)))) * deriv u (S v₀ (σ none))
          ∂(Measure.pi fun _ : Option R => ν v₀))
      v₀ := by
  intro S S' ν ψ_d
  set δ : ℝ := min (v₀ / 2) ((1 - v₀) / 2)
  have hδ : 0 < δ := lt_min (half_pos hv₀.1) (half_pos (sub_pos.2 hv₀.2))
  set U_v : Set ℝ := Ioo (v₀ - δ) (v₀ + δ)
  have hUv_nhds : U_v ∈ 𝓝 v₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hδ_le : ∀ v ∈ U_v, δ ≤ v ∧ δ ≤ 1 - v := fun v hv =>
    ⟨by linarith [hv.1, min_le_left (v₀ / 2) ((1 - v₀) / 2)],
     by linarith [hv.2, min_le_right (v₀ / 2) ((1 - v₀) / 2)]⟩
  have hν_eq : ∀ v, ν v = (μ.prod (volume : Measure ℝ)).tilted
      (fun p => E₀ p.1 + u (S v p) - p.2 ^ 2 / 2) :=
    fun v => tilted_prod_gaussianReal_zero_one μ _
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hSm : ∀ v, Measurable (S v) := fun v => by
    have hdot : Measurable fun p : E × ℝ => X p.1 ⬝ᵥ w :=
      Finset.measurable_sum _ fun k _ => ((hXm k).comp measurable_fst).mul_const (w k)
    exact (hdot.const_mul _).add ((measurable_const.add (measurable_snd.const_mul c_ξ)).const_mul _)
  have hS'm : ∀ v, Measurable (S' v) := fun v => by
    have hdot : Measurable fun p : E × ℝ => X p.1 ⬝ᵥ w :=
      Finset.measurable_sum _ fun k _ => ((hXm k).comp measurable_fst).mul_const (w k)
    exact (hdot.const_mul _).sub ((measurable_const.add (measurable_snd.const_mul c_ξ)).const_mul _)
  have hem : ∀ v, Measurable fun p : E × ℝ => E₀ p.1 + u (S v p) - p.2 ^ 2 / 2 := fun v =>
    ((hE₀m.comp measurable_fst).add (hum.comp (hSm v))).sub
      ((measurable_snd.pow_const 2).div_const 2)
  have hκ' : 0 < min κ (1 / 2) := lt_min hκ (by positivity)
  have hconf : ∀ v p, E₀ p.1 + u (S v p) - p.2 ^ 2 / 2 ≤
      0 + B₀ * ‖p‖ - min κ (1 / 2) * ‖p‖ ^ 2 :=
    fun v => prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 (S v)
  have hS_der : ∀ p : E × ℝ, ∀ v ∈ U_v, HasDerivAt (fun s => S s p) (S' v p) v := fun p v hv => by
    obtain ⟨hv1, hv2⟩ := hδ_le v hv
    have h1 := (Real.hasDerivAt_sqrt (hδ.trans_le hv1).ne').mul_const (X p.1 ⬝ᵥ w)
    have h2 := ((Real.hasDerivAt_sqrt (hδ.trans_le hv2).ne').comp v
      ((hasDerivAt_id v).const_sub 1)).mul_const (Y ⬝ᵥ w + c_ξ * p.2)
    refine (h1.add h2).congr_deriv ?_
    dsimp only [S', Function.comp_def]
    ring
  have hed : ∀ p : E × ℝ, ∀ v ∈ U_v,
      HasDerivAt (fun s => E₀ p.1 + u (S s p) - p.2 ^ 2 / 2)
        (S' v p * deriv u (S v p)) v := fun p v hv =>
    ((((hu _).hasDerivAt.comp v (hS_der p v hv)).const_add (E₀ p.1)).sub_const
      (p.2 ^ 2 / 2)).congr_deriv (mul_comm _ _)
  set L_S' : ℝ := (1 / (2 * Real.sqrt δ)) *
    (|L_X| * (∑ k, |w k|) + |Y ⬝ᵥ w| + |c_ξ|)
  have hLS'0 : 0 ≤ L_S' := by
    have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  have hS'b : ∀ v ∈ U_v, ∀ p : E × ℝ, |S' v p| ≤ L_S' * (1 + ‖p‖) ^ (n_X + 1) := fun v hv p =>
    abs_sqrt_path_deriv_le hXb Y w c_ξ hδ (hδ_le v hv).1 (hδ_le v hv).2 p
  have he'b : ∀ v ∈ U_v, ∀ p : E × ℝ,
      |S' v p * deriv u (S v p)| ≤ (L_S' * |D₁|) * (1 + ‖p‖) ^ (n_X + 1) := fun v hv p => by
    rw [abs_mul]
    exact (mul_le_mul (hS'b v hv p) ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _)
      (by positivity)).trans_eq (by ring)
  set Φ : ℝ → (R → E × ℝ) → ℝ := fun v σ => f (fun r => (σ r).1) * ∏ r, ψ r (S v (σ r))
  set Ψ' : ℝ → (R → E × ℝ) → ℝ := fun v σ =>
    f (fun r => (σ r).1) * ∑ j : R, S' v (σ j) * deriv (ψ j) (S v (σ j)) *
      ∏ r ∈ Finset.univ.erase j, ψ r (S v (σ r))
  have hΦm : ∀ v, Measurable (Φ v) := fun v =>
    (hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
      (Finset.measurable_prod _ fun r _ =>
        (hψd r).continuous.measurable.comp ((hSm v).comp (measurable_pi_apply r)))
  have hΨ'm : Measurable (Ψ' v₀) :=
    (hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
      (Finset.measurable_sum _ fun j _ =>
        ((((hS'm v₀).comp (measurable_pi_apply j)).mul
          ((measurable_deriv (ψ j)).comp ((hSm v₀).comp (measurable_pi_apply j)))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp ((hSm v₀).comp (measurable_pi_apply r)))))
  set C_ψ : ℝ := (1 + |M₀| + |M₁|) ^ Fintype.card R
  have hfb_p : ∀ σ : R → E × ℝ, |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
    abs_comp_le_prod_of_injective hfb norm_fst_le Function.injective_id
  have hΦb : ∀ v ∈ U_v, ∀ σ : R → E × ℝ,
      |Φ v σ| ≤ (|C_f| * C_ψ * (1 + L_S' * Fintype.card R)) *
        ∏ r, (1 + ‖σ r‖) ^ (m_f + (n_X + 1)) := fun v _ σ => by
    rw [abs_mul]
    have h1 : |∏ r, ψ r (S v (σ r))| ≤ C_ψ :=
      abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S v (σ r)
    have h2 : ∏ r, (1 + ‖σ r‖) ^ m_f ≤ ∏ r, (1 + ‖σ r‖) ^ (m_f + (n_X + 1)) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) fun r _ =>
        pow_le_pow_right₀ (by linarith [norm_nonneg (σ r)]) (Nat.le_add_right _ _)
    refine (mul_le_mul (hfb_p σ) h1 (abs_nonneg _) (by positivity)).trans ?_
    calc |C_f| * (∏ r, (1 + ‖σ r‖) ^ m_f) * C_ψ
        ≤ |C_f| * C_ψ * 1 * ∏ r, (1 + ‖σ r‖) ^ (m_f + (n_X + 1)) := by
          have := mul_le_mul_of_nonneg_left h2
            (mul_nonneg (abs_nonneg C_f) (by positivity : 0 ≤ C_ψ))
          linarith
      _ ≤ (|C_f| * C_ψ * (1 + L_S' * Fintype.card R)) *
            ∏ r, (1 + ‖σ r‖) ^ (m_f + (n_X + 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
            (Finset.prod_nonneg fun _ _ => by positivity)
  have hΨ'b : ∀ v ∈ U_v, ∀ σ : R → E × ℝ,
      |Ψ' v σ| ≤ (|C_f| * C_ψ * (1 + L_S' * Fintype.card R)) *
        ∏ r, (1 + ‖σ r‖) ^ (m_f + (n_X + 1)) := by
    intro v hv σ
    have hsum_le : |∑ j : R, S' v (σ j) * deriv (ψ j) (S v (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S v (σ r))| ≤
        (C_ψ * (L_S' * Fintype.card R)) * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ j : R, |S' v (σ j) * deriv (ψ j) (S v (σ j)) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S v (σ r))| ≤
          (L_S' * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) := fun j => by
        rw [abs_mul, abs_mul]
        have hx : |S' v (σ j)| ≤ L_S' * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) :=
          (hS'b v hv (σ j)).trans (mul_le_mul_of_nonneg_left
            (one_add_norm_pow_le_prod σ (n_X + 1) j) hLS'0)
        have hpr : |deriv (ψ j) (S v (σ j))| *
            |∏ r ∈ Finset.univ.erase j, ψ r (S v (σ r))| ≤ C_ψ :=
          (abs_mul _ _).symm.trans_le
            (abs_deriv_mul_prod_erase_le hM₀ hM₁ j fun r => S v (σ r))
        calc |S' v (σ j)| * |deriv (ψ j) (S v (σ j))| *
              |∏ r ∈ Finset.univ.erase j, ψ r (S v (σ r))|
            = |S' v (σ j)| * (|deriv (ψ j) (S v (σ j))| *
                |∏ r ∈ Finset.univ.erase j, ψ r (S v (σ r))|) := by ring
          _ ≤ (L_S' * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1)) * C_ψ :=
                mul_le_mul hx hpr (by positivity) (by positivity)
          _ = (L_S' * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) := by ring
      refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact le_of_eq (by ring)
    refine (abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) hsum_le).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => by positivity)
    have : 0 ≤ |C_f| * C_ψ := by positivity
    nlinarith
  have hΦd : ∀ σ : R → E × ℝ, ∀ v ∈ U_v, HasDerivAt (fun s => Φ s σ) (Ψ' v σ) v :=
    fun σ v hv => by
      have hprod := HasDerivAt.fun_finsetProd (u := Finset.univ)
        (f := fun r s => ψ r (S s (σ r))) fun r _ =>
          ((hψd r _).hasDerivAt.comp v (hS_der (σ r) v hv))
      refine (hprod.const_mul (f (fun r => (σ r).1))).congr_deriv ?_
      dsimp only [Ψ', smul_eq_mul]
      congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
  have hmain := hasDerivAt_integral_pi_tilted_of_confining_replicaDiff
    (E := E × ℝ) (μ := μ.prod volume) (R := R) hκ' (s := U_v) hUv_nhds
    (e := fun v p => E₀ p.1 + u (S v p) - p.2 ^ 2 / 2)
    (e' := fun v p => S' v p * deriv u (S v p))
    (Ψ := Φ) (Ψ' := Ψ')
    (A := 0) (B := B₀) (L := L_S' * |D₁|) (n := n_X + 1)
    (C := |C_f| * C_ψ * (1 + L_S' * Fintype.card R)) (m := m_f + (n_X + 1))
    (fun v _ => hem v) ((hS'm v₀).mul (hdu.comp (hSm v₀)))
    (fun v _ => hconf v) he'b hed
    (fun v _ => hΦm v) hΨ'm hΦb hΨ'b hΦd
  simp_rw [hν_eq]
  refine hmain.congr_deriv ?_
  have hv₀_mem : v₀ ∈ U_v := ⟨by linarith, by linarith⟩
  have : IsProbabilityMeasure ((μ.prod volume).tilted
      (fun p => E₀ p.1 + u (S v₀ p) - p.2 ^ 2 / 2)) :=
    isProbabilityMeasure_tilted
      (integrable_exp_of_confining (μ := μ.prod volume) hκ' (hem v₀) (hconf v₀))
  have h1 : ∀ j : R, Integrable (fun σ : R → E × ℝ =>
      f (fun r => (σ r).1) * (S' v₀ (σ j) * deriv (ψ j) (S v₀ (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ (σ r))))
      (Measure.pi fun _ : R => (μ.prod volume).tilted
        (fun p => E₀ p.1 + u (S v₀ p) - p.2 ^ 2 / 2)) := fun j => by
    refine integrable_pi_tilted_of_confining (μ := μ.prod volume) hκ' (hem v₀) (hconf v₀)
      ((hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
        ((((hS'm v₀).comp (measurable_pi_apply j)).mul
          ((measurable_deriv (ψ j)).comp ((hSm v₀).comp (measurable_pi_apply j)))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp
              ((hSm v₀).comp (measurable_pi_apply r))))).aestronglyMeasurable
      (C := |C_f| * (L_S' * C_ψ)) (m := m_f + (n_X + 1)) fun σ => ?_
    rw [Real.norm_eq_abs]
    have hx : |S' v₀ (σ j)| ≤ L_S' * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) :=
      (hS'b v₀ hv₀_mem (σ j)).trans (mul_le_mul_of_nonneg_left
        (one_add_norm_pow_le_prod σ (n_X + 1) j) hLS'0)
    have hpr : |deriv (ψ j) (S v₀ (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ (σ r))| ≤ C_ψ :=
      abs_deriv_mul_prod_erase_le hM₀ hM₁ j fun r => S v₀ (σ r)
    have h2' : |S' v₀ (σ j) * deriv (ψ j) (S v₀ (σ j)) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ (σ r))| ≤
        (L_S' * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) := by
      rw [mul_assoc, abs_mul]
      exact (mul_le_mul hx hpr (abs_nonneg _) (by positivity)).trans_eq (by ring)
    exact abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) h2'
  have h2 : ∀ j : R, Integrable (fun σ : R → E × ℝ =>
      (f (fun r => (σ r).1) * ∏ r, ψ r (S v₀ (σ r))) *
        (S' v₀ (σ j) * deriv u (S v₀ (σ j))))
      (Measure.pi fun _ : R => (μ.prod volume).tilted
        (fun p => E₀ p.1 + u (S v₀ p) - p.2 ^ 2 / 2)) := fun j => by
    refine integrable_pi_tilted_of_confining (μ := μ.prod volume) hκ' (hem v₀) (hconf v₀)
      (((hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp ((hSm v₀).comp (measurable_pi_apply r)))).mul
        (((hS'm v₀).comp (measurable_pi_apply j)).mul
          (hdu.comp ((hSm v₀).comp (measurable_pi_apply j))))).aestronglyMeasurable
      (C := (|C_f| * C_ψ) * (L_S' * |D₁|)) (m := m_f + (n_X + 1)) fun σ => ?_
    rw [Real.norm_eq_abs]
    have hp1 : |f (fun r => (σ r).1) * ∏ r, ψ r (S v₀ (σ r))| ≤
        (|C_f| * C_ψ) * ∏ r, (1 + ‖σ r‖) ^ m_f := by
      rw [abs_mul]
      have hpr : |∏ r, ψ r (S v₀ (σ r))| ≤ C_ψ :=
        abs_prod_le_one_add_pow hM₀ M₁ _ fun r => S v₀ (σ r)
      exact (mul_le_mul (hfb_p σ) hpr (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have hp2 : |S' v₀ (σ j) * deriv u (S v₀ (σ j))| ≤
        (L_S' * |D₁|) * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) :=
      (he'b v₀ hv₀_mem (σ j)).trans (mul_le_mul_of_nonneg_left
        (one_add_norm_pow_le_prod σ (n_X + 1) j) (by positivity))
    exact abs_mul_le_mul_prod_one_add_norm_pow hp1 hp2
  exact add_replicaDiff_prod_eq_sum_sub _ (fun σ => f (fun r => (σ r).1))
    (hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply r)))
    (S' v₀) (S v₀) (hS'm v₀) (hSm v₀) u hdu ψ (fun r => (hψd r).continuous.measurable) h1 h2

/-- Differentiating in `v ∈ (0, 1)` under the shared standard Gaussian `w ~ γ_sh` for a confined
extended replica Gibbs state. -/
private theorem hasDerivAt_integral_w_pi_tilted_prod_gaussianReal_sqrt [Fintype K] [Fintype R]
    [DecidableEq R] {κ B₀ c₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀) (hc₀ : 0 ≤ c₀)
    {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (v : ℝ) (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let S' (v : ℝ) (w : K → ℝ) (p : E × ℝ) : ℝ :=
      (1 / (2 * Real.sqrt v)) * (X p.1 ⬝ᵥ w) - (1 / (2 * Real.sqrt (1 - v))) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (v : ℝ) (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S v w p))
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    HasDerivAt
      (fun v => ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
        ∂(Measure.pi fun _ : R => ν v w) ∂γ_sh)
      ((∑ i : R, ∫ w, ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * S' v₀ w (σ i) *
            (ψ_d i (S v₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
          ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh) -
        (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) * S' v₀ w (σ none) *
            (∏ r, ψ r (S v₀ w (σ (some r)))) * deriv u (S v₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh)
      v₀ := by
  intro γ_sh S S' ν ψ_d
  set δ : ℝ := min (v₀ / 2) ((1 - v₀) / 2)
  have hδ : 0 < δ := lt_min (half_pos hv₀.1) (half_pos (sub_pos.2 hv₀.2))
  set U_v : Set ℝ := Ioo (v₀ - δ) (v₀ + δ)
  have hUv_nhds : U_v ∈ 𝓝 v₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hv₀_mem : v₀ ∈ U_v := ⟨by linarith, by linarith⟩
  have hδ_le : ∀ v ∈ U_v, δ ≤ v ∧ δ ≤ 1 - v := fun v hv =>
    ⟨by linarith [hv.1, min_le_left (v₀ / 2) ((1 - v₀) / 2)],
     by linarith [hv.2, min_le_right (v₀ / 2) ((1 - v₀) / 2)]⟩
  have hv_Icc : ∀ v ∈ U_v, 0 ≤ v ∧ v ≤ 1 := fun v hv =>
    ⟨(hδ.trans_le (hδ_le v hv).1).le, by linarith [(hδ_le v hv).2, hδ]⟩
  set A_v : ℝ → E → K → ℝ := fun v x k => Real.sqrt v * X x k + Real.sqrt (1 - v) * Y k
  set c_v : ℝ → ℝ := fun v => Real.sqrt (1 - v) * c_ξ
  have hS_Av : ∀ v w p, S v w p = A_v v p.1 ⬝ᵥ w + c_v v * p.2 := fun v w p => by
    dsimp only [S, A_v, c_v, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hAvm : ∀ v k, Measurable fun x => A_v v x k := fun v k =>
    ((hXm k).const_mul _).add measurable_const
  set s_Y : ℝ := ∑ k : K, |Y k|
  have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set s_A : ℝ := |L_X| * 2 ^ n_X + s_Y
  have hs_A : 0 ≤ s_A := by positivity
  have hAv_low : ∀ v ∈ U_v, ∀ k x, ‖x‖ ≤ 1 → |A_v v x k| ≤ s_A := fun v hv k x hx => by
    obtain ⟨hv0_le, hv1_le⟩ := hv_Icc v hv
    have hs1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv1_le
    have hs2 : Real.sqrt (1 - v) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hX1 : |X x k| ≤ |L_X| * 2 ^ n_X :=
      (hXb k x).trans (mul_le_mul (le_abs_self _)
        (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖x‖ ≤ 2) _)
        (by positivity) (abs_nonneg _))
    have hY1 : |Y k| ≤ s_Y :=
      Finset.single_le_sum (f := fun j => |Y j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    dsimp only [A_v]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt v * |X x k| + Real.sqrt (1 - v) * |Y k|
        ≤ 1 * (|L_X| * 2 ^ n_X) + 1 * s_Y :=
          add_le_add (mul_le_mul hs1 hX1 (abs_nonneg _) zero_le_one)
            (mul_le_mul hs2 hY1 (abs_nonneg _) zero_le_one)
      _ = s_A := by dsimp only [s_A]; ring
  set C_ψ : ℝ := (1 + |M₀| + |M₁|) ^ Fintype.card R
  have hfb_p : ∀ σ : R → E × ℝ, |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
    abs_comp_le_prod_of_injective hfb norm_fst_le Function.injective_id
  set C_S0 : ℝ := |c_ξ| / (2 * Real.sqrt δ)
  set C_S1 : ℝ := (|L_X| + s_Y + 1) / (2 * Real.sqrt δ)
  have hS'_lin_le : ∀ v ∈ U_v, ∀ (w : K → ℝ) (p : E × ℝ),
      |S' v w p| ≤ (C_S0 + C_S1 * ∑ k, |w k|) * (1 + ‖p‖) ^ (n_X + 1) := by
    intro v hv w p
    refine (abs_sqrt_path_deriv_le hXb Y w c_ξ hδ (hδ_le v hv).1 (hδ_le v hv).2 p).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hYw : |Y ⬝ᵥ w| ≤ s_Y * ∑ k, |w k| := abs_dotProduct_le_mul_sum_abs
      (fun k => Finset.single_le_sum (f := fun j => |Y j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ k)) w
    have hw : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc 1 / (2 * Real.sqrt δ) * (|L_X| * (∑ k, |w k|) + |Y ⬝ᵥ w| + |c_ξ|)
        ≤ 1 / (2 * Real.sqrt δ) * (|c_ξ| + (|L_X| + s_Y + 1) * ∑ k, |w k|) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = C_S0 + C_S1 * ∑ k, |w k| := by dsimp only [C_S0, C_S1]; ring
  -- Bounds and integrability for `F_w`, `D1_w`, `D2_w`:
  set F_w : ℝ → (K → ℝ) → ℝ := fun v w =>
    ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
      ∂(Measure.pi fun _ : R => ν v w)
  set D1_w : R → ℝ → (K → ℝ) → ℝ := fun i v w =>
    ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * S' v w (σ i) *
      (ψ_d i (S v w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ r)))
      ∂(Measure.pi fun _ : R => ν v w)
  set D2_w : ℝ → (K → ℝ) → ℝ := fun v w =>
    ∫ σ : Option R → E × ℝ, f (fun r => (σ (some r)).1) * S' v w (σ none) *
      (∏ r, ψ r (S v w (σ (some r)))) * deriv u (S v w (σ none))
      ∂(Measure.pi fun _ : Option R => ν v w)
  obtain ⟨A_m0, hAm0_nn, hI0⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal (K := K) (ι := R) μ hκ m_f
  obtain ⟨A_m1, hAm1_nn, hI1⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal
      (K := K) (ι := R) μ hκ (m_f + (n_X + 1))
  obtain ⟨A_m2, hAm2_nn, hI2⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal
      (K := K) (ι := Option R) μ hκ (m_f + (n_X + 1))
  have hS'_joint_R : ∀ (v : ℝ) (o : R),
      Measurable fun p : (K → ℝ) × (R → E × ℝ) => S' v p.1 (p.2 o) := fun v o => by
    have hdotX : Measurable fun p : (K → ℝ) × (R → E × ℝ) => X (p.2 o).1 ⬝ᵥ p.1 :=
      Finset.measurable_sum _ fun k _ =>
        ((hXm k).comp (measurable_fst.comp ((measurable_pi_apply o).comp measurable_snd))).mul
          ((measurable_pi_apply k).comp measurable_fst)
    have hdotY : Measurable fun p : (K → ℝ) × (R → E × ℝ) => Y ⬝ᵥ p.1 :=
      Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)
    have h1 : Measurable fun p : (K → ℝ) × (R → E × ℝ) =>
        (1 / (2 * Real.sqrt v)) * (X (p.2 o).1 ⬝ᵥ p.1) :=
      hdotX.const_mul _
    have h2 : Measurable fun p : (K → ℝ) × (R → E × ℝ) =>
        (1 / (2 * Real.sqrt (1 - v))) * (Y ⬝ᵥ p.1 + c_ξ * (p.2 o).2) :=
      (hdotY.add ((measurable_snd.comp ((measurable_pi_apply o).comp measurable_snd)).const_mul
        c_ξ)).const_mul _
    exact h1.sub h2
  have hS'_joint_O : ∀ (v : ℝ) (o : Option R),
      Measurable fun p : (K → ℝ) × (Option R → E × ℝ) => S' v p.1 (p.2 o) := fun v o => by
    have hdotX : Measurable fun p : (K → ℝ) × (Option R → E × ℝ) => X (p.2 o).1 ⬝ᵥ p.1 :=
      Finset.measurable_sum _ fun k _ =>
        ((hXm k).comp (measurable_fst.comp ((measurable_pi_apply o).comp measurable_snd))).mul
          ((measurable_pi_apply k).comp measurable_fst)
    have hdotY : Measurable fun p : (K → ℝ) × (Option R → E × ℝ) => Y ⬝ᵥ p.1 :=
      Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)
    have h1 : Measurable fun p : (K → ℝ) × (Option R → E × ℝ) =>
        (1 / (2 * Real.sqrt v)) * (X (p.2 o).1 ⬝ᵥ p.1) :=
      hdotX.const_mul _
    have h2 : Measurable fun p : (K → ℝ) × (Option R → E × ℝ) =>
        (1 / (2 * Real.sqrt (1 - v))) * (Y ⬝ᵥ p.1 + c_ξ * (p.2 o).2) :=
      (hdotY.add ((measurable_snd.comp ((measurable_pi_apply o).comp measurable_snd)).const_mul
        c_ξ)).const_mul _
    exact h1.sub h2
  have hFw_int : ∀ v ∈ U_v, Integrable (F_w v) γ_sh := fun v hv => by
    have heq : F_w v = fun w => ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * ∏ r, ψ r (A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2)
        ∂(Measure.pi fun _ : R =>
          (μ.prod (gaussianReal 0 1)).tilted
            (fun p => E₀ p.1 + u (A_v v p.1 ⬝ᵥ w + c_v v * p.2))) := by
      funext w; dsimp only [F_w, ν]; simp_rw [hS_Av]
    rw [heq]
    refine (hI0 hB₀ hc₀ hE₀m hE₀_conf hE₀_low (A_v v) (hAvm v) hs_A (hAv_low v hv) (c_v v)
      hu hu0 hD₁
      ((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp
            (measurable_S_joint (ι := R) (hAvm v) (c_v v) r)))
      (C₀ := |C_f| * C_ψ) (C₁ := 0) (by positivity) le_rfl fun w σ => ?_).2
    rw [zero_mul, add_zero, abs_mul]
    have hpr : |∏ r, ψ r (A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2)| ≤ C_ψ :=
      abs_prod_le_one_add_pow hM₀ M₁ _ fun r => A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2
    exact (mul_le_mul (hfb_p σ) hpr (abs_nonneg _) (by positivity)).trans_eq (by ring)
  -- Uniform bound on `|D1_w i v w|` and `|D2_w v w|` over `v ∈ U_v`:
  have hcv_le : ∀ v ∈ U_v, |c_v v| ≤ |c_ξ| := fun v hv => by
    dsimp only [c_v]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.sqrt_le_one.2 (by linarith [(hv_Icc v hv).1]))
  have hD1_pt_int : ∀ (i : R) (v : ℝ), v ∈ U_v →
      (∀ w, |D1_w i v w| ≤
        (|C_f| * ((1 + |D₁|) * C_ψ) * C_S0 +
          |C_f| * ((1 + |D₁|) * C_ψ) * C_S1 * ∑ k, |w k|) * A_m1 ^ Fintype.card R *
          (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_ξ|)) + 1 / 2)) ^
            ((m_f + (n_X + 1)) * Fintype.card R)) ∧
        Integrable (D1_w i v) γ_sh := fun i v hv => by
    have heq : D1_w i v = fun w => ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * S' v w (σ i) *
          (ψ_d i (A_v v (σ i).1 ⬝ᵥ w + c_v v * (σ i).2) *
            ∏ r ∈ Finset.univ.erase i, ψ r (A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2))
        ∂(Measure.pi fun _ : R =>
          (μ.prod (gaussianReal 0 1)).tilted
            (fun p => E₀ p.1 + u (A_v v p.1 ⬝ᵥ w + c_v v * p.2))) := by
      funext w; dsimp only [D1_w, ν]; simp_rw [hS_Av]
    have hi_m := measurable_S_joint (ι := R) (hAvm v) (c_v v) i
    have hres := hI1 hB₀ hc₀ hE₀m hE₀_conf hE₀_low (A_v v) (hAvm v) hs_A (hAv_low v hv) (c_v v)
      hu hu0 hD₁
      (G := fun w σ => f (fun r => (σ r).1) * S' v w (σ i) *
        (ψ_d i (A_v v (σ i).1 ⬝ᵥ w + c_v v * (σ i).2) *
          ∏ r ∈ Finset.univ.erase i, ψ r (A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2)))
      (((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        (hS'_joint_R v i)).mul
        ((((measurable_deriv (ψ i)).comp hi_m).add
          (((hψd i).continuous.measurable.comp hi_m).mul
            ((measurable_deriv u).comp hi_m))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp
              (measurable_S_joint (ι := R) (hAvm v) (c_v v) r))))
      (C₀ := |C_f| * ((1 + |D₁|) * C_ψ) * C_S0)
      (C₁ := |C_f| * ((1 + |D₁|) * C_ψ) * C_S1)
      (by positivity) (by positivity) fun w σ => by
        rw [mul_assoc (f _)]
        have hψd_le : |ψ_d i (A_v v (σ i).1 ⬝ᵥ w + c_v v * (σ i).2) *
            ∏ r ∈ Finset.univ.erase i, ψ r (A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2)| ≤
            (1 + |D₁|) * C_ψ := by
          exact abs_tiltedDeriv_mul_prod_erase_le hM₀ hM₁ hD₁ i fun r =>
            A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2
        have hS1 : |S' v w (σ i) *
            (ψ_d i (A_v v (σ i).1 ⬝ᵥ w + c_v v * (σ i).2) *
              ∏ r ∈ Finset.univ.erase i, ψ r (A_v v (σ r).1 ⬝ᵥ w + c_v v * (σ r).2))| ≤
            (((1 + |D₁|) * C_ψ) * (C_S0 + C_S1 * ∑ k, |w k|)) *
              ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) := by
          rw [abs_mul]
          have hx : |S' v w (σ i)| ≤
              (C_S0 + C_S1 * ∑ k, |w k|) * ∏ r, (1 + ‖σ r‖) ^ (n_X + 1) :=
            (hS'_lin_le v hv w (σ i)).trans (mul_le_mul_of_nonneg_left
              (one_add_norm_pow_le_prod σ (n_X + 1) i) (by
                have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
                positivity))
          exact (mul_le_mul hx hψd_le (abs_nonneg _) (by
            have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
            positivity)).trans_eq (by ring)
        exact (abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) hS1).trans_eq (by ring)
    refine ⟨fun w => ?_, heq.symm ▸ hres.2⟩
    rw [heq]
    refine (hres.1 w).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
      have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      positivity) ?_ _) (by
      have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      positivity)
    linarith [mul_le_mul_of_nonneg_left (hcv_le v hv) (abs_nonneg D₁)]
  have hD2_pt_int : ∀ v ∈ U_v,
      (∀ w, |D2_w v w| ≤
        (|C_f| * (C_ψ * |D₁|) * C_S0 +
          |C_f| * (C_ψ * |D₁|) * C_S1 * ∑ k, |w k|) * A_m2 ^ Fintype.card (Option R) *
          (1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_ξ|)) + 1 / 2)) ^
            ((m_f + (n_X + 1)) * Fintype.card (Option R))) ∧
        Integrable (D2_w v) γ_sh := fun v hv => by
    have heq : D2_w v = fun w => ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * S' v w (σ none) *
          (∏ r, ψ r (A_v v (σ (some r)).1 ⬝ᵥ w + c_v v * (σ (some r)).2)) *
          deriv u (A_v v (σ none).1 ⬝ᵥ w + c_v v * (σ none).2)
        ∂(Measure.pi fun _ : Option R =>
          (μ.prod (gaussianReal 0 1)).tilted
            (fun p => E₀ p.1 + u (A_v v p.1 ⬝ᵥ w + c_v v * p.2))) := by
      funext w; dsimp only [D2_w, ν]; simp_rw [hS_Av]
    have hres := hI2 hB₀ hc₀ hE₀m hE₀_conf hE₀_low (A_v v) (hAvm v) hs_A (hAv_low v hv) (c_v v)
      hu hu0 hD₁
      (G := fun w σ => f (fun r => (σ (some r)).1) * S' v w (σ none) *
        (∏ r, ψ r (A_v v (σ (some r)).1 ⬝ᵥ w + c_v v * (σ (some r)).2)) *
        deriv u (A_v v (σ none).1 ⬝ᵥ w + c_v v * (σ none).2))
      ((((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))).mul
        (hS'_joint_O v none)).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp
            (measurable_S_joint (ι := Option R) (hAvm v) (c_v v) (some r)))).mul
        ((measurable_deriv u).comp
          (measurable_S_joint (ι := Option R) (hAvm v) (c_v v) none)))
      (C₀ := |C_f| * (C_ψ * |D₁|) * C_S0)
      (C₁ := |C_f| * (C_ψ * |D₁|) * C_S1)
      (by positivity) (by positivity) fun w σ => by
        rw [mul_assoc, mul_assoc]
        have hf_o : |f (fun r => (σ (some r)).1)| ≤ |C_f| * ∏ o, (1 + ‖σ o‖) ^ m_f :=
          abs_comp_some_le_prod hfb_p σ
        have hpr : |(∏ r, ψ r (A_v v (σ (some r)).1 ⬝ᵥ w + c_v v * (σ (some r)).2)) *
            deriv u (A_v v (σ none).1 ⬝ᵥ w + c_v v * (σ none).2)| ≤ C_ψ * |D₁| := by
          rw [abs_mul]
          exact mul_le_mul
            (abs_prod_le_one_add_pow hM₀ M₁ _ fun r =>
              A_v v (σ (some r)).1 ⬝ᵥ w + c_v v * (σ (some r)).2)
            ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
        have hS2 : |S' v w (σ none) *
            ((∏ r, ψ r (A_v v (σ (some r)).1 ⬝ᵥ w + c_v v * (σ (some r)).2)) *
              deriv u (A_v v (σ none).1 ⬝ᵥ w + c_v v * (σ none).2))| ≤
            ((C_ψ * |D₁|) * (C_S0 + C_S1 * ∑ k, |w k|)) *
              ∏ o, (1 + ‖σ o‖) ^ (n_X + 1) := by
          rw [abs_mul]
          have hx : |S' v w (σ none)| ≤
              (C_S0 + C_S1 * ∑ k, |w k|) * ∏ o, (1 + ‖σ o‖) ^ (n_X + 1) :=
            (hS'_lin_le v hv w (σ none)).trans (mul_le_mul_of_nonneg_left
              (one_add_norm_pow_le_prod σ (n_X + 1) none) (by
                have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
                positivity))
          exact (mul_le_mul hx hpr (abs_nonneg _) (by
            have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
            positivity)).trans_eq (by ring)
        exact (abs_mul_le_mul_prod_one_add_norm_pow hf_o hS2).trans_eq (by ring)
    refine ⟨fun w => ?_, heq.symm ▸ hres.2⟩
    rw [heq]
    refine (hres.1 w).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
      have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      positivity) ?_ _) (by
      have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      positivity)
    linarith [mul_le_mul_of_nonneg_left (hcv_le v hv) (abs_nonneg D₁)]
  -- Polynomial integrable majorant in `w`:
  set B_base : (K → ℝ) → ℝ := fun w =>
    1 + B₀ + (c₀ + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_ξ|)) + 1 / 2)
  have hBbase_mem : ∀ deg : ℕ, Integrable (fun w => B_base w ^ deg) γ_sh := fun deg => by
    have hk : ∀ k : K, MemLp (fun w : K → ℝ => |w k|) deg γ_sh := fun k =>
      ((memLp_id_gaussianReal (μ := 0) (v := 1) deg).comp_measurePreserving
        (measurePreserving_eval (fun _ : K => gaussianReal 0 1) k)).abs
    have hsum : MemLp B_base deg γ_sh := by
      have h_eq : B_base = fun w =>
          (1 + B₀ + c₀ + |u 0| + |D₁| * |c_ξ| + 1 / 2) + (|D₁| * s_A) * ∑ k, |w k| := by
        funext w; dsimp only [B_base]; ring
      rw [h_eq]
      exact (memLp_const _).add ((memLp_finsetSum _ fun k _ => hk k).const_mul _)
    refine hsum.integrable_norm_pow'.congr (ae_of_all _ fun w => ?_)
    dsimp only [B_base]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  set b1_dom : (K → ℝ) → ℝ := fun w =>
    (|C_f| * ((1 + |D₁|) * C_ψ) * C_S0 +
      |C_f| * ((1 + |D₁|) * C_ψ) * C_S1 * ∑ k, |w k|) * A_m1 ^ Fintype.card R *
      B_base w ^ ((m_f + (n_X + 1)) * Fintype.card R)
  set b2_dom : (K → ℝ) → ℝ := fun w =>
    (|C_f| * (C_ψ * |D₁|) * C_S0 +
      |C_f| * (C_ψ * |D₁|) * C_S1 * ∑ k, |w k|) * A_m2 ^ Fintype.card (Option R) *
      B_base w ^ ((m_f + (n_X + 1)) * Fintype.card (Option R))
  have hpoly_int : ∀ (a₀ a₁ c_m : ℝ) (deg : ℕ), 0 ≤ a₀ → 0 ≤ a₁ → 0 ≤ c_m →
      Integrable (fun w : K → ℝ => (a₀ + a₁ * ∑ k, |w k|) * c_m * B_base w ^ deg) γ_sh := by
    intro a₀ a₁ c_m deg ha₀ ha₁ hcm
    set M_lin : ℝ := 1 + a₀ + a₁
    have hbase1 : ∀ w, 1 ≤ B_base w := fun w => by
      dsimp only [B_base]
      have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith [abs_nonneg (u 0), mul_nonneg (abs_nonneg D₁) (add_nonneg (mul_nonneg hs_A this)
        (abs_nonneg c_ξ))]
    have h_w_mem : MemLp (fun w : K → ℝ => a₀ + a₁ * ∑ k, |w k|) 2 γ_sh :=
      (memLp_const a₀).add ((memLp_finsetSum _ fun k _ =>
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
          (measurePreserving_eval (fun _ : K => gaussianReal 0 1) k)).abs).const_mul a₁)
    have h_B_mem : MemLp (fun w : K → ℝ => c_m * B_base w ^ deg) 2 γ_sh := by
      have hsq : Integrable (fun w => (B_base w ^ deg) ^ 2) γ_sh := by
        simpa only [← pow_mul] using hBbase_mem (deg * 2)
      have hm_B : Measurable (fun w => B_base w ^ deg) := by
        dsimp only [B_base]
        fun_prop
      exact ((memLp_two_iff_integrable_sq hm_B.aestronglyMeasurable).2 hsq).const_mul c_m
    exact (h_w_mem.integrable_mul h_B_mem).congr (ae_of_all _ fun w => by
      change (a₀ + a₁ * ∑ k, |w k|) * (c_m * B_base w ^ deg) =
        (a₀ + a₁ * ∑ k, |w k|) * c_m * B_base w ^ deg
      ring)
  have hb1_i : Integrable b1_dom γ_sh :=
    hpoly_int _ _ _ _ (by positivity) (by positivity) (by positivity)
  have hb2_i : Integrable b2_dom γ_sh :=
    hpoly_int _ _ _ _ (by positivity) (by positivity) (by positivity)
  have hF'v0_m : AEStronglyMeasurable
      (fun w => (∑ i : R, D1_w i v₀ w) - (Fintype.card R : ℝ) * D2_w v₀ w) γ_sh :=
    ((integrable_finsetSum _ fun i _ => (hD1_pt_int i v₀ hv₀_mem).2).sub
      ((hD2_pt_int v₀ hv₀_mem).2.const_mul _)).aestronglyMeasurable
  have hd_w := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ_sh)
    (F := F_w)
    (F' := fun v w => (∑ i : R, D1_w i v w) - (Fintype.card R : ℝ) * D2_w v w)
    (s := U_v) hUv_nhds
    (eventually_of_mem hUv_nhds fun v hv => (hFw_int v hv).aestronglyMeasurable)
    (hFw_int v₀ hv₀_mem) hF'v0_m
    (bound := fun w => (Fintype.card R : ℝ) * b1_dom w + (Fintype.card R : ℝ) * b2_dom w)
    (ae_of_all _ fun w v hv => by
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => (hD1_pt_int i v hv).1 w).trans ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left ((hD2_pt_int v hv).1 w) (Nat.cast_nonneg _))
    ((hb1_i.const_mul _).add (hb2_i.const_mul _))
    (ae_of_all _ fun w v hv =>
      hasDerivAt_pi_tilted_prod_gaussianReal_sqrt_w μ hκ hB₀ hE₀m hE₀_conf X Y hXm hXb c_ξ
        hu hu0 hD₁ ψ hψd hM₀ hM₁ hf hfb w
        ⟨hδ.trans_le (hδ_le v hv).1, by linarith [(hδ_le v hv).2, hδ]⟩)).2
  refine hd_w.congr_deriv ?_
  rw [integral_sub (integrable_finsetSum _ fun i _ => (hD1_pt_int i v₀ hv₀_mem).2)
      ((hD2_pt_int v₀ hv₀_mem).2.const_mul _),
    integral_finsetSum _ fun i _ => (hD1_pt_int i v₀ hv₀_mem).2,
    integral_const_mul]

/-- **Derivative in `v ∈ (0, 1)` and Gaussian integration by parts at fixed confined base energy
`E₀`:** differentiating `v ↦ ∫ w, ⟨f(σ.1) ∏_r ψ_r(S_v(w, σ_r))⟩ ∂γ_sh` at `v₀ ∈ (0, 1)` and
applying `stein_pi_tilted_prod_gaussianReal` to both the `R`-replica sum and the `Option R`
normalizer term produces the five-group continuous-spin covariance formula (diagonal `R` sum,
off-diagonal `R` pair sum, two `Option R` fresh-replica sums, and `Option (Option R)` double-fresh
term). -/
theorem hasDerivAt_integral_pi_tilted_prod_gaussianReal_sqrt [Fintype K] [Fintype R]
    [DecidableEq R] {κ B₀ c₀ : ℝ} (hκ : 0 < κ) (hB₀ : 0 ≤ B₀)
    {E₀ : E → ℝ} (hE₀m : Measurable E₀)
    (hE₀_conf : ∀ x, E₀ x ≤ B₀ * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ x, ‖x‖ ≤ 1 → -c₀ ≤ E₀ x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (horth : ∀ x, X x ⬝ᵥ Y = 0)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu₂ : Differentiable ℝ (deriv u))
    (hu0 : ∀ x, u x ≤ 0) {D₁ D₂ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (v : ℝ) (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (v : ℝ) (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S v w p))
    let C_off (x y : E) : ℝ := X x ⬝ᵥ X y - Y ⬝ᵥ Y
    let C_diag (x : E) : ℝ := X x ⬝ᵥ X x - (Y ⬝ᵥ Y + c_ξ ^ 2)
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    let ψ_dd (r : R) (x : ℝ) : ℝ :=
      deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x +
        ψ r x * deriv (deriv u) x + ψ r x * deriv u x ^ 2
    HasDerivAt
      (fun v => ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
        ∂(Measure.pi fun _ : R => ν v w) ∂γ_sh)
      ((1 / 2) * (
        (∑ i : R, ∫ w, ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * C_diag (σ i).1 *
            (ψ_dd i (S v₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
          ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh) +
        (∑ i : R, ∑ j ∈ Finset.univ.erase i, ∫ w, ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
            (ψ_d i (S v₀ w (σ i)) * ψ_d j (S v₀ w (σ j)) *
              ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v₀ w (σ r)))
          ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh) -
        (Fintype.card R : ℝ) * ∑ i : R, ∫ w, ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
            (ψ_d i (S v₀ w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ (some r)))) *
            deriv u (S v₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh -
        (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
            (∏ r, ψ r (S v₀ w (σ (some r)))) *
            (deriv (deriv u) (S v₀ w (σ none)) + deriv u (S v₀ w (σ none)) ^ 2)
          ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh -
        (Fintype.card R : ℝ) * ∑ j : R, ∫ w, ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
            (ψ_d j (S v₀ w (σ (some j))) *
              ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ w (σ (some r)))) *
            deriv u (S v₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          ∫ w, ∫ σ : Option (Option R) → E × ℝ,
            f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
              (∏ r, ψ r (S v₀ w (σ (some (some r))))) *
              deriv u (S v₀ w (σ none)) * deriv u (S v₀ w (σ (some none)))
            ∂(Measure.pi fun _ : Option (Option R) => ν v₀ w) ∂γ_sh))
      v₀ := by
  intro γ_sh S ν C_off C_diag ψ_d ψ_dd
  have hc₀ : 0 ≤ c₀ := nonneg_of_confining_of_neg_le hE₀_conf hE₀_low
  have hd_w := hasDerivAt_integral_w_pi_tilted_prod_gaussianReal_sqrt μ hκ hB₀ hc₀ hE₀m
    hE₀_conf hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁ ψ hψd hM₀ hM₁ hf hfb hv₀
  refine hd_w.congr_deriv ?_
  have hv₀_pos : 0 < v₀ := hv₀.1
  have h1v₀_pos : 0 < 1 - v₀ := sub_pos.2 hv₀.2
  set A_0 : E → K → ℝ := fun x k => Real.sqrt v₀ * X x k + Real.sqrt (1 - v₀) * Y k
  set B_0 : E → K → ℝ := fun x k =>
    (1 / (2 * Real.sqrt v₀)) * X x k - (1 / (2 * Real.sqrt (1 - v₀))) * Y k
  set c_A0 : ℝ := Real.sqrt (1 - v₀) * c_ξ
  set c_B0 : ℝ := -(1 / (2 * Real.sqrt (1 - v₀))) * c_ξ
  have hA0m : ∀ k, Measurable fun x => A_0 x k := fun k =>
    ((hXm k).const_mul _).add measurable_const
  have hB0m : ∀ k, Measurable fun x => B_0 x k := fun k =>
    ((hXm k).const_mul _).sub measurable_const
  set s_Y : ℝ := ∑ k : K, |Y k|
  have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hA0b : ∀ k x, |A_0 x k| ≤ (|L_X| + s_Y) * (1 + ‖x‖) ^ n_X := fun k x => by
    have hs1 : Real.sqrt v₀ ≤ 1 := Real.sqrt_le_one.2 hv₀.2.le
    have hs2 : Real.sqrt (1 - v₀) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have h1 : (1 : ℝ) ≤ (1 + ‖x‖) ^ n_X := one_le_pow₀ (by linarith [norm_nonneg x])
    have hY1 : |Y k| ≤ s_Y * (1 + ‖x‖) ^ n_X :=
      (Finset.single_le_sum (f := fun j => |Y j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ k)).trans (le_mul_of_one_le_right hsY0 h1)
    dsimp only [A_0]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt v₀ * |X x k| + Real.sqrt (1 - v₀) * |Y k|
        ≤ 1 * (|L_X| * (1 + ‖x‖) ^ n_X) + 1 * (s_Y * (1 + ‖x‖) ^ n_X) :=
          add_le_add
            (mul_le_mul hs1 ((hXb k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
              (by positivity))) (abs_nonneg _) zero_le_one)
            (mul_le_mul hs2 hY1 (abs_nonneg _) zero_le_one)
      _ = (|L_X| + s_Y) * (1 + ‖x‖) ^ n_X := by ring
  set C_B0 : ℝ := |1 / (2 * Real.sqrt v₀)| * |L_X| + |1 / (2 * Real.sqrt (1 - v₀))| * s_Y
  have hB0b : ∀ k x, |B_0 x k| ≤ C_B0 * (1 + ‖x‖) ^ n_X := fun k x => by
    have h1 : (1 : ℝ) ≤ (1 + ‖x‖) ^ n_X := one_le_pow₀ (by linarith [norm_nonneg x])
    have hY1 : |Y k| ≤ s_Y * (1 + ‖x‖) ^ n_X :=
      (Finset.single_le_sum (f := fun j => |Y j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ k)).trans (le_mul_of_one_le_right hsY0 h1)
    dsimp only [B_0]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    calc |1 / (2 * Real.sqrt v₀)| * |X x k| + |1 / (2 * Real.sqrt (1 - v₀))| * |Y k|
        ≤ |1 / (2 * Real.sqrt v₀)| * (|L_X| * (1 + ‖x‖) ^ n_X) +
            |1 / (2 * Real.sqrt (1 - v₀))| * (s_Y * (1 + ‖x‖) ^ n_X) :=
          add_le_add
            (mul_le_mul_of_nonneg_left ((hXb k x).trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hY1 (abs_nonneg _))
      _ = C_B0 * (1 + ‖x‖) ^ n_X := by dsimp only [C_B0]; ring
  have hS_eq : ∀ w p, S v₀ w p = A_0 p.1 ⬝ᵥ w + c_A0 * p.2 := fun w p => by
    dsimp only [S, A_0, c_A0, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hS'_eq : ∀ (w : K → ℝ) (p : E × ℝ),
      (1 / (2 * Real.sqrt v₀)) * (X p.1 ⬝ᵥ w) -
        (1 / (2 * Real.sqrt (1 - v₀))) * (Y ⬝ᵥ w + c_ξ * p.2) =
      B_0 p.1 ⬝ᵥ w + c_B0 * p.2 := fun w p => by
    dsimp only [B_0, c_B0, dotProduct]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  -- Covariance identities:
  have hdot_off : ∀ x y : E, B_0 x ⬝ᵥ A_0 y = (1 / 2) * C_off x y := by
    intro x y
    have hxy := horth x
    have hyx : Y ⬝ᵥ X y = 0 := by rw [dotProduct_comm, horth y]
    have hexp : B_0 x ⬝ᵥ A_0 y =
        ((1 / (2 * Real.sqrt v₀)) * Real.sqrt v₀) * (X x ⬝ᵥ X y) +
        ((1 / (2 * Real.sqrt v₀)) * Real.sqrt (1 - v₀)) * (X x ⬝ᵥ Y) -
        ((1 / (2 * Real.sqrt (1 - v₀))) * Real.sqrt v₀) * (Y ⬝ᵥ X y) -
        ((1 / (2 * Real.sqrt (1 - v₀))) * Real.sqrt (1 - v₀)) * (Y ⬝ᵥ Y) := by
      simp only [B_0, A_0, dotProduct, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hv_ne : Real.sqrt v₀ ≠ 0 := (Real.sqrt_pos.2 hv₀_pos).ne'
    have h1v_ne : Real.sqrt (1 - v₀) ≠ 0 := (Real.sqrt_pos.2 h1v₀_pos).ne'
    rw [hexp, hxy, hyx, mul_zero, mul_zero]
    dsimp only [C_off]
    field_simp
    ring
  have hdot_diag : ∀ x : E, B_0 x ⬝ᵥ A_0 x + c_B0 * c_A0 = (1 / 2) * C_diag x := by
    intro x
    have h1v_ne : Real.sqrt (1 - v₀) ≠ 0 := (Real.sqrt_pos.2 h1v₀_pos).ne'
    have hc : c_B0 * c_A0 = -(1 / 2) * c_ξ ^ 2 := by
      dsimp only [c_B0, c_A0]
      field_simp
    rw [hdot_off x x, hc]
    dsimp only [C_off, C_diag]
    ring
  -- Regularity and bounds of `ψ_d`:
  have hψd_diff : ∀ r, Differentiable ℝ (ψ_d r) := fun r =>
    (hψ₂d r).add ((hψd r).mul hu₂)
  have hψd_deriv : ∀ r x, deriv (ψ_d r) x + ψ_d r x * deriv u x = ψ_dd r x := fun r x => by
    have hd : HasDerivAt (ψ_d r)
        (deriv (deriv (ψ r)) x + (deriv (ψ r) x * deriv u x + ψ r x * deriv (deriv u) x)) x :=
      (hψ₂d r x).hasDerivAt.add (((hψd r x).hasDerivAt).mul (hu₂ x).hasDerivAt)
    rw [hd.deriv]
    dsimp only [ψ_d, ψ_dd]
    ring
  set M_ψ0 : ℝ := |M₀| + |M₁| + |M₀| * |D₁|
  set M_ψ1 : ℝ := |M₁| + |M₂| + 2 * |M₁| * |D₁| + |M₀| * |D₂| + |M₀| * |D₁| ^ 2
  have hψd_b0 : ∀ r x, |ψ_d r x| ≤ M_ψ0 := fun r x => by
    dsimp only [ψ_d, M_ψ0]
    have h1 := (hM₁ r x).trans (le_abs_self _)
    have h2 : |ψ r x * deriv u x| ≤ |M₀| * |D₁| := by
      rw [abs_mul]
      exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
    linarith [abs_add_le (deriv (ψ r) x) (ψ r x * deriv u x), abs_nonneg M₀]
  have hψd_b1 : ∀ r x, |deriv (ψ_d r) x| ≤ M_ψ1 := fun r x => by
    have hd : HasDerivAt (ψ_d r)
        (deriv (deriv (ψ r)) x + (deriv (ψ r) x * deriv u x + ψ r x * deriv (deriv u) x)) x :=
      (hψ₂d r x).hasDerivAt.add (((hψd r x).hasDerivAt).mul (hu₂ x).hasDerivAt)
    rw [hd.deriv]
    dsimp only [M_ψ1]
    have h1 := (hM₂ r x).trans (le_abs_self _)
    have h2 : |deriv (ψ r) x * deriv u x| ≤ |M₁| * |D₁| := by
      rw [abs_mul]
      exact mul_le_mul ((hM₁ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
    have h3 : |ψ r x * deriv (deriv u) x| ≤ |M₀| * |D₂| := by
      rw [abs_mul]
      exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₂ x).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
    linarith [abs_add_le (deriv (deriv (ψ r)) x)
        (deriv (ψ r) x * deriv u x + ψ r x * deriv (deriv u) x),
      abs_add_le (deriv (ψ r) x * deriv u x) (ψ r x * deriv (deriv u) x),
      abs_nonneg M₁, mul_nonneg (abs_nonneg M₁) (abs_nonneg D₁),
      mul_nonneg (abs_nonneg M₀) (sq_nonneg |D₁|)]
  -- 1. Stein IBP on each `i : R` term:
  have h_term1 : ∀ i : R,
      ∫ w, ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) *
            ((1 / (2 * Real.sqrt v₀)) * (X (σ i).1 ⬝ᵥ w) -
              (1 / (2 * Real.sqrt (1 - v₀))) * (Y ⬝ᵥ w + c_ξ * (σ i).2)) *
            (ψ_d i (S v₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
          ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh =
        (1 / 2) * (
          (∫ w, ∫ σ : R → E × ℝ,
              f (fun r => (σ r).1) * C_diag (σ i).1 *
                (ψ_dd i (S v₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
              ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh) +
          (∑ j ∈ Finset.univ.erase i, ∫ w, ∫ σ : R → E × ℝ,
              f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
                (ψ_d i (S v₀ w (σ i)) * ψ_d j (S v₀ w (σ j)) *
                  ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v₀ w (σ r)))
              ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh) -
          (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → E × ℝ,
              f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
                (ψ_d i (S v₀ w (σ (some i))) *
                  ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ (some r)))) *
                deriv u (S v₀ w (σ none))
              ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh) := by
    intro i
    let ψ_i : R → ℝ → ℝ := fun r => if r = i then ψ_d i else ψ r
    have hψi_d : ∀ r, Differentiable ℝ (ψ_i r) := fun r => by
      dsimp only [ψ_i]; split_ifs with h
      · exact hψd_diff i
      · exact hψd r
    have hψi_b0 : ∀ r x, |ψ_i r x| ≤ M_ψ0 := fun r x => by
      dsimp only [ψ_i]; split_ifs with h
      · exact hψd_b0 i x
      · exact (hM₀ r x).trans ((le_abs_self _).trans (by
          dsimp only [M_ψ0]
          linarith [abs_nonneg M₁, mul_nonneg (abs_nonneg M₀) (abs_nonneg D₁)]))
    have hψi_b1 : ∀ r x, |deriv (ψ_i r) x| ≤ M_ψ1 := fun r x => by
      dsimp only [ψ_i]; split_ifs with h
      · exact hψd_b1 i x
      · exact (hM₁ r x).trans ((le_abs_self _).trans (by
          dsimp only [M_ψ1]
          linarith [abs_nonneg M₂, mul_nonneg (abs_nonneg M₁) (abs_nonneg D₁),
            mul_nonneg (abs_nonneg M₀) (abs_nonneg D₂),
            mul_nonneg (abs_nonneg M₀) (sq_nonneg |D₁|)]))
    obtain ⟨_, hst1_j, hst1_opt, hst1_eq⟩ :=
      stein_pi_tilted_prod_gaussianReal μ hκ hB₀ hE₀m hE₀_conf hE₀_low
        A_0 B_0 hA0m hB0m hA0b hB0b c_A0 c_B0 hu hu0 hD₁
        ψ_i hψi_d hψi_b0 hψi_b1 hf hfb i
    have hprod_ψi : ∀ (w : K → ℝ) (τ : R → E × ℝ),
        ∏ r : R, ψ_i r (A_0 (τ r).1 ⬝ᵥ w + c_A0 * (τ r).2) =
          ψ_d i (S v₀ w (τ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (τ r)) := fun w τ => by
      simp_rw [← hS_eq w]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [ψ_i, ↓reduceIte]
      congr 1; exact Finset.prod_congr rfl fun r hr => by simp [Finset.ne_of_mem_erase hr]
    have hLHS_i :
        ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) *
              ((1 / (2 * Real.sqrt v₀)) * (X (σ i).1 ⬝ᵥ w) -
                (1 / (2 * Real.sqrt (1 - v₀))) * (Y ⬝ᵥ w + c_ξ * (σ i).2)) *
              (ψ_d i (S v₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
            ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh =
        ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) * (B_0 (σ i).1 ⬝ᵥ w + c_B0 * (σ i).2) *
              ∏ r, ψ_i r (A_0 (σ r).1 ⬝ᵥ w + c_A0 * (σ r).2)
            ∂(Measure.pi fun _ : R =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      simp_rw [hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      rw [hS'_eq w (σ i), hprod_ψi w σ]
      simp_rw [hS_eq w]
    rw [hLHS_i, hst1_eq, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hdiag_i :
        ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) *
              (B_0 (σ i).1 ⬝ᵥ A_0 (σ i).1 + if i = i then c_B0 * c_A0 else 0) *
              ((deriv (ψ_i i) (A_0 (σ i).1 ⬝ᵥ w + c_A0 * (σ i).2) +
                ψ_i i (A_0 (σ i).1 ⬝ᵥ w + c_A0 * (σ i).2) *
                  deriv u (A_0 (σ i).1 ⬝ᵥ w + c_A0 * (σ i).2)) *
                ∏ r ∈ Finset.univ.erase i, ψ_i r (A_0 (σ r).1 ⬝ᵥ w + c_A0 * (σ r).2))
            ∂(Measure.pi fun _ : R =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh =
        (1 / 2) * ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) * C_diag (σ i).1 *
              (ψ_dd i (S v₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
            ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      rw [← integral_const_mul]
      simp_rw [← hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      simp only [↓reduceIte, hdot_diag, ψ_i, hψd_deriv]
      have hp_rest : ∏ r ∈ Finset.univ.erase i,
          (if r = i then ψ_d i else ψ r) (S v₀ w (σ r)) =
          ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)) :=
        Finset.prod_congr rfl fun r hr => by simp [Finset.ne_of_mem_erase hr]
      rw [hp_rest]; ring
    have hoff_i : ∀ j ∈ Finset.univ.erase i,
        ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) *
              (B_0 (σ i).1 ⬝ᵥ A_0 (σ j).1 + if j = i then c_B0 * c_A0 else 0) *
              ((deriv (ψ_i j) (A_0 (σ j).1 ⬝ᵥ w + c_A0 * (σ j).2) +
                ψ_i j (A_0 (σ j).1 ⬝ᵥ w + c_A0 * (σ j).2) *
                  deriv u (A_0 (σ j).1 ⬝ᵥ w + c_A0 * (σ j).2)) *
                ∏ r ∈ Finset.univ.erase j, ψ_i r (A_0 (σ r).1 ⬝ᵥ w + c_A0 * (σ r).2))
            ∂(Measure.pi fun _ : R =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh =
        (1 / 2) * ∫ w, ∫ σ : R → E × ℝ,
            f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
              (ψ_d i (S v₀ w (σ i)) * ψ_d j (S v₀ w (σ j)) *
                ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v₀ w (σ r)))
            ∂(Measure.pi fun _ : R => ν v₀ w) ∂γ_sh := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hij : i ≠ j := hji.symm
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      rw [← integral_const_mul]
      simp_rw [← hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      simp only [hji, ↓reduceIte, add_zero, hdot_off]
      have hij_mem : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩
      rw [← Finset.mul_prod_erase (Finset.univ.erase j) _ hij_mem, Finset.erase_right_comm]
      simp only [ψ_i, hji, ↓reduceIte]
      have hp_rest : ∏ r ∈ (Finset.univ.erase i).erase j,
          (if r = i then ψ_d i else ψ r) (S v₀ w (σ r)) =
          ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v₀ w (σ r)) :=
        Finset.prod_congr rfl fun r hr => by
          have hri : r ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
          simp [hri]
      rw [hp_rest]
      dsimp only [ψ_d]; ring
    have hfresh_i :
        ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * (B_0 (σ (some i)).1 ⬝ᵥ A_0 (σ none).1) *
              (∏ r, ψ_i r (A_0 (σ (some r)).1 ⬝ᵥ w + c_A0 * (σ (some r)).2)) *
              deriv u (A_0 (σ none).1 ⬝ᵥ w + c_A0 * (σ none).2)
            ∂(Measure.pi fun _ : Option R =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh =
        (1 / 2) * ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
              (ψ_d i (S v₀ w (σ (some i))) *
                ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ (some r)))) *
              deriv u (S v₀ w (σ none))
            ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      rw [← integral_const_mul]
      simp_rw [← hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      have hp_some := hprod_ψi w (fun r => σ (some r))
      simp_rw [← hS_eq w] at hp_some
      rw [hdot_off, hp_some]
      ring
    rw [hdiag_i, Finset.sum_congr rfl hoff_i, hfresh_i, ← Finset.mul_sum]
    ring
  -- 2. Stein IBP on the `Option R` normalizer term at `i₀ = none`:
  have h_term2 :
      ∫ w, ∫ σ : Option R → E × ℝ,
          f (fun r => (σ (some r)).1) *
            ((1 / (2 * Real.sqrt v₀)) * (X (σ none).1 ⬝ᵥ w) -
              (1 / (2 * Real.sqrt (1 - v₀))) * (Y ⬝ᵥ w + c_ξ * (σ none).2)) *
            (∏ r, ψ r (S v₀ w (σ (some r)))) * deriv u (S v₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh =
      (1 / 2) * (
        (∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
              (∏ r, ψ r (S v₀ w (σ (some r)))) *
              (deriv (deriv u) (S v₀ w (σ none)) + deriv u (S v₀ w (σ none)) ^ 2)
            ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh) +
        (∑ j : R, ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
              (ψ_d j (S v₀ w (σ (some j))) *
                ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ w (σ (some r)))) *
              deriv u (S v₀ w (σ none))
            ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh) -
        ((Fintype.card R : ℝ) + 1) * ∫ w, ∫ σ : Option (Option R) → E × ℝ,
            f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
              (∏ r, ψ r (S v₀ w (σ (some (some r))))) *
              deriv u (S v₀ w (σ none)) * deriv u (S v₀ w (σ (some none)))
            ∂(Measure.pi fun _ : Option (Option R) => ν v₀ w) ∂γ_sh) := by
    let ψ_opt : Option R → ℝ → ℝ := fun o => Option.casesOn o (deriv u) ψ
    have hψopt_d : ∀ o, Differentiable ℝ (ψ_opt o) := by
      rintro (_ | r)
      · exact hu₂
      · exact hψd r
    have hψopt_b0 : ∀ o x, |ψ_opt o x| ≤ |M₀| + |D₁| := by
      rintro (_ | r) x
      · exact (hD₁ x).trans ((le_abs_self _).trans (by linarith [abs_nonneg M₀]))
      · exact (hM₀ r x).trans ((le_abs_self _).trans (by linarith [abs_nonneg D₁]))
    have hψopt_b1 : ∀ o x, |deriv (ψ_opt o) x| ≤ |M₁| + |D₂| := by
      rintro (_ | r) x
      · exact (hD₂ x).trans ((le_abs_self _).trans (by linarith [abs_nonneg M₁]))
      · exact (hM₁ r x).trans ((le_abs_self _).trans (by linarith [abs_nonneg D₂]))
    have hf_opt_m : Measurable fun a : Option R → E => f (fun r => a (some r)) :=
      hf.comp (measurable_pi_iff.2 fun r => measurable_pi_apply (some r))
    have hf_opt_b : ∀ a : Option R → E,
        |f (fun r => a (some r))| ≤ |C_f| * ∏ o, (1 + ‖a o‖) ^ m_f :=
      abs_comp_some_le_prod fun b =>
        (hfb b).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
          (Finset.prod_nonneg fun _ _ => by positivity))
    obtain ⟨_, hst2_j, hst2_opt, hst2_eq⟩ :=
      stein_pi_tilted_prod_gaussianReal (R := Option R) μ hκ hB₀ hE₀m hE₀_conf hE₀_low
        A_0 B_0 hA0m hB0m hA0b hB0b c_A0 c_B0 hu hu0 hD₁
        ψ_opt hψopt_d hψopt_b0 hψopt_b1 hf_opt_m hf_opt_b none
    have hprod_opt : ∀ (w : K → ℝ) (τ : Option R → E × ℝ),
        ∏ o : Option R, ψ_opt o (A_0 (τ o).1 ⬝ᵥ w + c_A0 * (τ o).2) =
          (∏ r : R, ψ r (S v₀ w (τ (some r)))) * deriv u (S v₀ w (τ none)) := fun w τ => by
      simp_rw [← hS_eq w]
      rw [Fintype.prod_option]
      simp only [ψ_opt]
      ring
    have hLHS_2 :
        ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) *
              ((1 / (2 * Real.sqrt v₀)) * (X (σ none).1 ⬝ᵥ w) -
                (1 / (2 * Real.sqrt (1 - v₀))) * (Y ⬝ᵥ w + c_ξ * (σ none).2)) *
              (∏ r, ψ r (S v₀ w (σ (some r)))) * deriv u (S v₀ w (σ none))
            ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh =
        ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * (B_0 (σ none).1 ⬝ᵥ w + c_B0 * (σ none).2) *
              ∏ o : Option R, ψ_opt o (A_0 (σ o).1 ⬝ᵥ w + c_A0 * (σ o).2)
            ∂(Measure.pi fun _ : Option R =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      simp_rw [hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      rw [hS'_eq w (σ none), hprod_opt w σ]
      simp_rw [hS_eq w]
      ring
    rw [hLHS_2, hst2_eq, Fintype.sum_option, Fintype.card_option, Nat.cast_add, Nat.cast_one]
    have hnone_term :
        ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) *
              (B_0 (σ none).1 ⬝ᵥ A_0 (σ none).1 +
                if (none : Option R) = none then c_B0 * c_A0 else 0) *
              ((deriv (ψ_opt none) (A_0 (σ none).1 ⬝ᵥ w + c_A0 * (σ none).2) +
                ψ_opt none (A_0 (σ none).1 ⬝ᵥ w + c_A0 * (σ none).2) *
                  deriv u (A_0 (σ none).1 ⬝ᵥ w + c_A0 * (σ none).2)) *
                ∏ o ∈ Finset.univ.erase none, ψ_opt o (A_0 (σ o).1 ⬝ᵥ w + c_A0 * (σ o).2))
            ∂(Measure.pi fun _ : Option R =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh =
        (1 / 2) * ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
              (∏ r, ψ r (S v₀ w (σ (some r)))) *
              (deriv (deriv u) (S v₀ w (σ none)) + deriv u (S v₀ w (σ none)) ^ 2)
            ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      rw [← integral_const_mul]
      simp_rw [← hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      simp only [↓reduceIte, hdot_diag, ψ_opt]
      have herase_none : ∏ o ∈ (Finset.univ : Finset (Option R)).erase none,
          (Option.casesOn o (deriv u) ψ : ℝ → ℝ) (S v₀ w (σ o)) =
          ∏ r : R, ψ r (S v₀ w (σ (some r))) := by
        have h1 := Fintype.prod_option fun o : Option R =>
          if o = none then (1 : ℝ)
          else (Option.casesOn o (deriv u) ψ : ℝ → ℝ) (S v₀ w (σ o))
        simp only [↓reduceIte, one_mul, Option.some_ne_none] at h1
        rw [← h1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (none : Option R))]
        simp only [↓reduceIte, one_mul]
        exact Finset.prod_congr rfl fun o ho => by simp [Finset.ne_of_mem_erase ho]
      rw [herase_none]; ring
    have hsome_term : ∀ j : R,
        ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) *
              (B_0 (σ none).1 ⬝ᵥ A_0 (σ (some j)).1 +
                if (some j : Option R) = none then c_B0 * c_A0 else 0) *
              ((deriv (ψ_opt (some j)) (A_0 (σ (some j)).1 ⬝ᵥ w + c_A0 * (σ (some j)).2) +
                ψ_opt (some j) (A_0 (σ (some j)).1 ⬝ᵥ w + c_A0 * (σ (some j)).2) *
                  deriv u (A_0 (σ (some j)).1 ⬝ᵥ w + c_A0 * (σ (some j)).2)) *
                ∏ o ∈ Finset.univ.erase (some j), ψ_opt o (A_0 (σ o).1 ⬝ᵥ w + c_A0 * (σ o).2))
            ∂(Measure.pi fun _ : Option R =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh =
        (1 / 2) * ∫ w, ∫ σ : Option R → E × ℝ,
            f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
              (ψ_d j (S v₀ w (σ (some j))) *
                ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ w (σ (some r)))) *
              deriv u (S v₀ w (σ none))
            ∂(Measure.pi fun _ : Option R => ν v₀ w) ∂γ_sh := by
      intro j
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      rw [← integral_const_mul]
      simp_rw [← hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      simp only [Option.some_ne_none, ↓reduceIte, add_zero, hdot_off, ψ_opt]
      have hnone_mem : (none : Option R) ∈ (Finset.univ : Finset (Option R)).erase (some j) :=
        Finset.mem_erase.2 ⟨(Option.some_ne_none j).symm, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase (Finset.univ.erase (some j)) _ hnone_mem]
      dsimp only
      have herase_both : ∏ o ∈ ((Finset.univ : Finset (Option R)).erase (some j)).erase none,
          (Option.casesOn o (deriv u) ψ : ℝ → ℝ) (S v₀ w (σ o)) =
          ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ w (σ (some r))) := by
        refine Finset.prod_bij (fun (o : Option R) (ho : o ∈ _) =>
          o.get (Option.isSome_iff_ne_none.2 (Finset.ne_of_mem_erase ho))) ?_ ?_ ?_ ?_
        · intro o ho
          have hne_j : o ≠ some j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ho)
          refine Finset.mem_erase.2 ⟨fun h => hne_j ?_, Finset.mem_univ _⟩
          rw [← h, Option.some_get]
        · intro o₁ ho₁ o₂ ho₂ hget
          have hs1 := Option.some_get (Option.isSome_iff_ne_none.2 (Finset.ne_of_mem_erase ho₁))
          have hs2 := Option.some_get (Option.isSome_iff_ne_none.2 (Finset.ne_of_mem_erase ho₂))
          rw [← hs1, ← hs2, hget]
        · intro r hr
          refine ⟨some r, Finset.mem_erase.2 ⟨Option.some_ne_none r,
            Finset.mem_erase.2 ⟨Option.some_injective R |>.ne (Finset.ne_of_mem_erase hr),
              Finset.mem_univ _⟩⟩, rfl⟩
        · intro o ho
          rcases o with _ | r
          · exact absurd rfl (Finset.ne_of_mem_erase ho)
          · rfl
      rw [herase_both]
      dsimp only [ψ_d]; ring
    have hfresh_2 :
        ∫ w, ∫ σ : Option (Option R) → E × ℝ,
            f (fun r => (σ (some (some r))).1) *
              (B_0 (σ (some none)).1 ⬝ᵥ A_0 (σ none).1) *
              (∏ o : Option R, ψ_opt o (A_0 (σ (some o)).1 ⬝ᵥ w + c_A0 * (σ (some o)).2)) *
              deriv u (A_0 (σ none).1 ⬝ᵥ w + c_A0 * (σ none).2)
            ∂(Measure.pi fun _ : Option (Option R) =>
              (μ.prod (gaussianReal 0 1)).tilted
                (fun p => E₀ p.1 + u (A_0 p.1 ⬝ᵥ w + c_A0 * p.2))) ∂γ_sh =
        (1 / 2) * ∫ w, ∫ σ : Option (Option R) → E × ℝ,
            f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
              (∏ r, ψ r (S v₀ w (σ (some (some r))))) *
              deriv u (S v₀ w (σ none)) * deriv u (S v₀ w (σ (some none)))
            ∂(Measure.pi fun _ : Option (Option R) => ν v₀ w) ∂γ_sh := by
      -- Note: swap `none` and `some none`! Both are fresh replicas outside `some (some r)`.
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [ν]
      rw [← integral_const_mul]
      simp_rw [← hS_eq w]
      have hSm_w : Measurable (S v₀ w) := by
        have heq_Sw : S v₀ w = fun p : E × ℝ => A_0 p.1 ⬝ᵥ w + c_A0 * p.2 :=
          funext (hS_eq w)
        rw [heq_Sw]
        exact (Finset.measurable_sum _ fun k _ => ((hA0m k).comp measurable_fst).mul_const
          (w k)).add (measurable_snd.const_mul c_A0)
      have hprob_w : IsProbabilityMeasure
          ((μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S v₀ w p))) := by
        rw [tilted_prod_gaussianReal_zero_one μ]
        exact isProbabilityMeasure_tilted
          (integrable_exp_of_confining (μ := μ.prod volume) (lt_min hκ (by positivity))
            (((hE₀m.comp measurable_fst).add (hu.continuous.measurable.comp hSm_w)).sub
              ((measurable_snd.pow_const 2).div_const 2))
            (prod_gaussian_exponent_confining hκ hB₀ hE₀_conf hu0 _))
      -- Swap `none` and `some none` via `Equiv.swap`:
      let sw : Equiv.Perm (Option (Option R)) := Equiv.swap none (some none)
      have hmp_sw := measurePreserving_piCongrLeft
        (fun _ : Option (Option R) =>
          (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ p.1 + u (S v₀ w p))) sw
      set G_sw : (Option (Option R) → E × ℝ) → ℝ := fun σ =>
        (1 / 2) * (f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
          (∏ r, ψ r (S v₀ w (σ (some (some r))))) *
          deriv u (S v₀ w (σ none)) * deriv u (S v₀ w (σ (some none))))
      have hGsw_m : Measurable G_sw := by
        have hC_m : Measurable fun σ : Option (Option R) → E × ℝ =>
            C_off (σ none).1 (σ (some none)).1 := by
          dsimp only [C_off, dotProduct]
          exact (Finset.measurable_sum _ fun k _ =>
            ((hXm k).comp (measurable_fst.comp (measurable_pi_apply none))).mul
              ((hXm k).comp (measurable_fst.comp (measurable_pi_apply (some none))))).sub
            measurable_const
        exact (((((hf.comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp (measurable_pi_apply (some (some r))))).mul hC_m).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp
              (hSm_w.comp (measurable_pi_apply (some (some r)))))).mul
          ((measurable_deriv u).comp (hSm_w.comp (measurable_pi_apply none)))).mul
          ((measurable_deriv u).comp (hSm_w.comp (measurable_pi_apply (some none))))).const_mul _
      have hswap_int := hmp_sw.integral_comp_of_aestronglyMeasurable hGsw_m.aestronglyMeasurable
      rw [← hswap_int]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only [G_sw, Function.comp_apply]
      have hp_opt := hprod_opt w (fun o => σ (some o))
      simp_rw [← hS_eq w] at hp_opt
      rw [hdot_off, hp_opt]
      have hsw_ss : ∀ r : R,
          (MeasurableEquiv.piCongrLeft (fun _ => E × ℝ) sw σ) (some (some r)) =
            σ (some (some r)) := fun r => by
        change σ (sw.symm (some (some r))) = σ (some (some r))
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none _)
          (Option.some_injective _ |>.ne (Option.some_ne_none r))]
      have hsw_n : (MeasurableEquiv.piCongrLeft (fun _ => E × ℝ) sw σ) none = σ (some none) := by
        change σ (sw.symm none) = σ (some none)
        rw [Equiv.symm_swap, Equiv.swap_apply_left]
      have hsw_sn : (MeasurableEquiv.piCongrLeft (fun _ => E × ℝ) sw σ) (some none) = σ none := by
        change σ (sw.symm (some none)) = σ none
        rw [Equiv.symm_swap, Equiv.swap_apply_right]
      simp only [hsw_ss, hsw_n, hsw_sn]
      ring
    rw [hnone_term, Finset.sum_congr rfl fun j _ => hsome_term j, hfresh_2, ← Finset.mul_sum]
    ring
  -- Combine `h_term1` and `h_term2`:
  dsimp only
  rw [Finset.sum_congr rfl fun i _ => h_term1 i, h_term2, ← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Along the square-root path, the `w`- and replica-average of an observable of polynomial growth
is measurable, polynomially bounded and integrable in the old disorder. -/
theorem measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal
    {Ω ι : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω) [Fintype K] [Fintype ι]
    {κ : ℝ} (hκ : 0 < κ) {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω) (hc₀ : ∀ ω, 0 ≤ c₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁) (m : ℕ) :
    ∃ C_dom : ℝ, 0 ≤ C_dom ∧
      ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 →
      ∀ {G : (K → ℝ) → (ι → E × ℝ) → ℝ},
      Measurable (fun p : (K → ℝ) × (ι → E × ℝ) => G p.1 p.2) →
      ∀ {C_G : ℝ}, 0 ≤ C_G →
      (∀ w σ, |G w σ| ≤ C_G * ∏ o, (1 + ‖σ o‖) ^ m) →
      let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
      let S (w : K → ℝ) (p : E × ℝ) : ℝ :=
        Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
      let ν (ω : Ω) (w : K → ℝ) : Measure (E × ℝ) :=
        (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ ω p.1 + u (S w p))
      let J (ω : Ω) : ℝ := ∫ w, ∫ σ : ι → E × ℝ, G w σ
        ∂(Measure.pi fun _ : ι => ν ω w) ∂γ_sh
      Measurable J ∧
        (∀ ω, |J ω| ≤ C_G * C_dom * (1 + B₀ ω + c₀ ω) ^ (m * Fintype.card ι)) ∧
        Integrable J P₀ := by
  have hum : Measurable u := hu.continuous.measurable
  set s_Y : ℝ := ∑ k : K, |Y k|
  have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set s_A : ℝ := |L_X| * 2 ^ n_X + s_Y
  have hs_A : 0 ≤ s_A := by positivity
  obtain ⟨A_m, hAm0, hIm⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal (K := K) (ι := ι) μ hκ m
  set γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
  set deg : ℕ := m * Fintype.card ι
  set W_fac : (K → ℝ) → ℝ := fun w =>
    1 + |u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_ξ|) + 1 / 2
  have hWfac_int : Integrable (fun w => W_fac w ^ deg) γ_sh := by
    have hk : ∀ k : K, MemLp (fun w : K → ℝ => |w k|) deg γ_sh := fun k =>
      ((memLp_id_gaussianReal (μ := 0) (v := 1) deg).comp_measurePreserving
        (measurePreserving_eval (fun _ : K => gaussianReal 0 1) k)).abs
    have h_eq : W_fac = fun w =>
        (1 + |u 0| + |D₁| * |c_ξ| + 1 / 2) + (|D₁| * s_A) * ∑ k, |w k| := by
      funext w; dsimp only [W_fac]; ring
    have hmem : MemLp W_fac deg γ_sh := by
      rw [h_eq]
      exact (memLp_const _).add ((memLp_finsetSum _ fun k _ => hk k).const_mul _)
    refine hmem.integrable_norm_pow'.congr (ae_of_all _ fun w => ?_)
    dsimp only [W_fac]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  set I_W : ℝ := ∫ w, W_fac w ^ deg ∂γ_sh
  have hIW0 : 0 ≤ I_W := integral_nonneg fun w => by
    dsimp only [W_fac]
    have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  refine ⟨A_m ^ Fintype.card ι * I_W, by positivity,
    fun {v} hv0 hv1 {G} hGm {C_G} hCG0 hGb => ?_⟩
  intro γ_sh' S ν J
  set A_v : E → K → ℝ := fun x k => Real.sqrt v * X x k + Real.sqrt (1 - v) * Y k
  set c_v : ℝ := Real.sqrt (1 - v) * c_ξ
  have hS_Av : ∀ w p, S w p = A_v p.1 ⬝ᵥ w + c_v * p.2 := fun w p => by
    dsimp only [S, A_v, c_v, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hAvm : ∀ k, Measurable fun x => A_v x k := fun k =>
    ((hXm k).const_mul _).add measurable_const
  have hAv_low : ∀ k x, ‖x‖ ≤ 1 → |A_v x k| ≤ s_A := fun k x hx => by
    have hs1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv1
    have hs2 : Real.sqrt (1 - v) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hX1 : |X x k| ≤ |L_X| * 2 ^ n_X :=
      (hXb k x).trans (mul_le_mul (le_abs_self _)
        (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖x‖ ≤ 2) _)
        (by positivity) (abs_nonneg _))
    have hY1 : |Y k| ≤ s_Y :=
      Finset.single_le_sum (f := fun j => |Y j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    dsimp only [A_v]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt v * |X x k| + Real.sqrt (1 - v) * |Y k|
        ≤ 1 * (|L_X| * 2 ^ n_X) + 1 * s_Y :=
          add_le_add (mul_le_mul hs1 hX1 (abs_nonneg _) zero_le_one)
            (mul_le_mul hs2 hY1 (abs_nonneg _) zero_le_one)
      _ = s_A := by dsimp only [s_A]; ring
  have hcv_le : |c_v| ≤ |c_ξ| := by
    dsimp only [c_v]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.sqrt_le_one.2 (by linarith))
  have hJm : Measurable J := by
    have hν_eq : ∀ ω w, ν ω w = (μ.prod (volume : Measure ℝ)).tilted
        (fun p => E₀ ω p.1 + u (S w p) - p.2 ^ 2 / 2) :=
      fun ω w => tilted_prod_gaussianReal_zero_one μ _
    have he_joint : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) =>
        E₀ q.1.1 q.2.1 + u (S q.1.2 q.2) - q.2.2 ^ 2 / 2 := by
      have hE1 : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) => E₀ q.1.1 q.2.1 :=
        hE₀m.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd))
      have hS1 : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) => S q.1.2 q.2 := by
        simp_rw [hS_Av]
        have hdot : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) => A_v q.2.1 ⬝ᵥ q.1.2 :=
          Finset.measurable_sum _ fun k _ =>
            ((hAvm k).comp (measurable_fst.comp measurable_snd)).mul
              ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst))
        exact hdot.add ((measurable_snd.comp measurable_snd).const_mul c_v)
      exact (hE1.add (hum.comp hS1)).sub
        (((measurable_snd.comp measurable_snd).pow_const 2).div_const 2)
    have hG_joint : Measurable fun q : (Ω × (K → ℝ)) × (ι → E × ℝ) =>
        (fun p : Ω × (K → ℝ) => G p.2) q.1 q.2 :=
      hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h_inner_m := measurable_integral_pi_tilted_of_sigmaFinite
      (μ' := μ.prod (volume : Measure ℝ))
      (e := fun (p : Ω × (K → ℝ)) (x : E × ℝ) => E₀ p.1 x.1 + u (S p.2 x) - x.2 ^ 2 / 2)
      (G := fun p : Ω × (K → ℝ) => G p.2) he_joint hG_joint
    have hJ_eq : J = fun ω => ∫ w,
        (∫ σ : ι → E × ℝ, G w σ ∂(Measure.pi fun _ : ι =>
          (μ.prod (volume : Measure ℝ)).tilted
            (fun p => E₀ ω p.1 + u (S w p) - p.2 ^ 2 / 2))) ∂γ_sh' := by
      funext ω; dsimp only [J]; simp_rw [hν_eq ω]
    rw [hJ_eq]
    exact (h_inner_m.stronglyMeasurable.integral_prod_right' (ν := γ_sh')).measurable
  have hJ_pt : ∀ ω, |J ω| ≤ C_G * (A_m ^ Fintype.card ι * I_W) *
      (1 + B₀ ω + c₀ ω) ^ deg := fun ω => by
    have hEω_m : Measurable (E₀ ω) := hE₀m.comp (measurable_const.prodMk measurable_id)
    have hres := hIm (hB₀ ω) (hc₀ ω) hEω_m (hE₀_conf ω) (hE₀_low ω) A_v hAvm hs_A hAv_low c_v
      hu hu0 hD₁ hGm hCG0 le_rfl (fun w σ => by simpa only [zero_mul, add_zero] using hGb w σ)
    have hν_Av : ∀ w, ν ω w = (μ.prod (gaussianReal 0 1)).tilted
        (fun p => E₀ ω p.1 + u (A_v p.1 ⬝ᵥ w + c_v * p.2)) := by
      intro w; dsimp only [ν]; simp_rw [hS_Av]
    have h_int_w : Integrable (fun w => ∫ σ : ι → E × ℝ, G w σ
        ∂(Measure.pi fun _ : ι => ν ω w)) γ_sh := by
      simp_rw [hν_Av]; exact hres.2
    have h_pt_w : ∀ w, |∫ σ : ι → E × ℝ, G w σ ∂(Measure.pi fun _ : ι => ν ω w)| ≤
        (C_G * A_m ^ Fintype.card ι * (1 + B₀ ω + c₀ ω) ^ deg) * W_fac w ^ deg := fun w => by
      have hw1 := hres.1 w
      simp only [zero_mul, add_zero, ← hν_Av w] at hw1
      refine hw1.trans ?_
      have hbase_prod :
          1 + B₀ ω + (c₀ ω + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_v|)) + 1 / 2) ≤
          (1 + B₀ ω + c₀ ω) * W_fac w := by
        dsimp only [W_fac]
        have hw_nn : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have hBc : 0 ≤ B₀ ω + c₀ ω := add_nonneg (hB₀ ω) (hc₀ ω)
        have hU_nn : 0 ≤ |u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_ξ|) + 1 / 2 := by positivity
        have hcv_d := mul_le_mul_of_nonneg_left hcv_le (abs_nonneg D₁)
        nlinarith [mul_nonneg hBc hU_nn]
      have hpow_le := pow_le_pow_left₀ (by
        have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have := hB₀ ω; have := hc₀ ω; positivity) hbase_prod deg
      rw [mul_pow] at hpow_le
      calc C_G * A_m ^ Fintype.card ι *
              (1 + B₀ ω + (c₀ ω + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_v|)) + 1 / 2)) ^ deg
          ≤ C_G * A_m ^ Fintype.card ι * ((1 + B₀ ω + c₀ ω) ^ deg * W_fac w ^ deg) :=
            mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ = (C_G * A_m ^ Fintype.card ι * (1 + B₀ ω + c₀ ω) ^ deg) * W_fac w ^ deg := by ring
    calc |J ω| ≤ ∫ w, |∫ σ : ι → E × ℝ, G w σ ∂(Measure.pi fun _ : ι => ν ω w)| ∂γ_sh :=
          abs_integral_le_integral_abs
      _ ≤ ∫ w, (C_G * A_m ^ Fintype.card ι * (1 + B₀ ω + c₀ ω) ^ deg) * W_fac w ^ deg ∂γ_sh :=
          integral_mono h_int_w.abs (hWfac_int.const_mul _) h_pt_w
      _ = C_G * (A_m ^ Fintype.card ι * I_W) * (1 + B₀ ω + c₀ ω) ^ deg := by
          rw [integral_const_mul]; dsimp only [I_W]; ring
  have hJ_int : Integrable J P₀ :=
    ((hmom deg).const_mul (C_G * (A_m ^ Fintype.card ι * I_W))).mono'
      hJm.aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hJ_pt ω)
  exact ⟨hJm, hJ_pt, hJ_int⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Centered linear forms with polynomially bounded coefficients have a polynomially bounded
covariance. -/
theorem abs_dotProduct_sub_dotProduct_le_of_abs_le_pow [Fintype K] {X : E → K → ℝ}
    {Y : K → ℝ} {L_X : ℝ} {n_X : ℕ}
    (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X) (c_ξ : ℝ) (x y : E) :
    |X x ⬝ᵥ X y - Y ⬝ᵥ Y| ≤
      ((∑ _k : K, |L_X| ^ 2) + (∑ k : K, Y k ^ 2) + c_ξ ^ 2) *
        (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X := by
  set C_Y : ℝ := ∑ k : K, Y k ^ 2
  set C_cov_bd : ℝ := (∑ _k : K, |L_X| ^ 2) + C_Y + c_ξ ^ 2
  have hdotX : |X x ⬝ᵥ X y| ≤ (∑ _k : K, |L_X| ^ 2) * (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X := by
    calc |X x ⬝ᵥ X y| ≤ ∑ k : K, |X x k| * |X y k| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun k _ => abs_mul _ _
      _ ≤ ∑ _k : K, (|L_X| * (1 + ‖x‖) ^ n_X) * (|L_X| * (1 + ‖y‖) ^ n_X) :=
          Finset.sum_le_sum fun k _ => mul_le_mul
            ((hXb k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
            ((hXb k y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
            (abs_nonneg _) (by positivity)
      _ = (∑ _k : K, |L_X| ^ 2) * (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
  have hdotY : |Y ⬝ᵥ Y| ≤ C_Y * (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X := by
    have hYY : Y ⬝ᵥ Y = C_Y := by
      dsimp only [dotProduct, C_Y]; exact Finset.sum_congr rfl fun _ _ => (sq _).symm
    have hY0 : 0 ≤ C_Y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [hYY, abs_of_nonneg hY0]
    have hx1 : (1 : ℝ) ≤ (1 + ‖x‖) ^ n_X := one_le_pow₀ (by linarith [norm_nonneg x])
    have hy1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ n_X := one_le_pow₀ (by linarith [norm_nonneg y])
    calc C_Y = C_Y * 1 * 1 := by ring
      _ ≤ C_Y * (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx1 hY0) hy1 zero_le_one (by positivity)
  refine (abs_sub _ _).trans ((add_le_add hdotX hdotY).trans ?_)
  have hxy_nn : 0 ≤ (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X := by positivity
  have hsub : (∑ _k : K, |L_X| ^ 2) + C_Y ≤ C_cov_bd := by
    dsimp only [C_cov_bd]; linarith [sq_nonneg c_ξ]
  calc _ = ((∑ _k : K, |L_X| ^ 2) + C_Y) * ((1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X) := by ring
    _ ≤ C_cov_bd * ((1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X) :=
        mul_le_mul_of_nonneg_right hsub hxy_nn
    _ = C_cov_bd * (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X := by ring

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem cdiag_le_of_poly_bound [Fintype K] {X : E → K → ℝ} {Y : K → ℝ} {L_X : ℝ} {n_X : ℕ}
    (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X) (c_ξ : ℝ) (x : E) :
    |X x ⬝ᵥ X x - (Y ⬝ᵥ Y + c_ξ ^ 2)| ≤
      ((∑ _k : K, |L_X| ^ 2) + (∑ k : K, Y k ^ 2) + c_ξ ^ 2) * (1 + ‖x‖) ^ (2 * n_X) := by
  set C_Y : ℝ := ∑ k : K, Y k ^ 2
  have hdotX : |X x ⬝ᵥ X x| ≤ (∑ _k : K, |L_X| ^ 2) * (1 + ‖x‖) ^ (2 * n_X) := by
    calc |X x ⬝ᵥ X x| ≤ ∑ k : K, |X x k| * |X x k| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun k _ => abs_mul _ _
      _ ≤ ∑ _k : K, (|L_X| * (1 + ‖x‖) ^ n_X) * (|L_X| * (1 + ‖x‖) ^ n_X) :=
          Finset.sum_le_sum fun k _ => mul_le_mul
            ((hXb k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
            ((hXb k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
            (abs_nonneg _) (by positivity)
      _ = (∑ _k : K, |L_X| ^ 2) * (1 + ‖x‖) ^ (2 * n_X) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, two_mul, pow_add]
          ring
  have hdotY : |Y ⬝ᵥ Y + c_ξ ^ 2| ≤ (C_Y + c_ξ ^ 2) * (1 + ‖x‖) ^ (2 * n_X) := by
    have hYY : Y ⬝ᵥ Y = C_Y := by
      dsimp only [dotProduct, C_Y]; exact Finset.sum_congr rfl fun _ _ => (sq _).symm
    have hYc0 : 0 ≤ C_Y + c_ξ ^ 2 :=
      add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
    rw [hYY, abs_of_nonneg hYc0]
    exact le_mul_of_one_le_right hYc0 (one_le_pow₀ (by linarith [norm_nonneg x]))
  exact (abs_sub _ _).trans ((add_le_add hdotX hdotY).trans_eq (by ring))

/-- **Disorder-averaged `v ∈ (0, 1)` derivative and Gaussian integration by parts** for a confined
extended replica Gibbs state over an arbitrary old-disorder space `(Ω, P₀)`. Suppose `E₀ ω` is
jointly measurable with confinement `E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖²` and unit-ball lower bound
`-c₀ ω ≤ E₀ ω x`, where `1 + B₀ + c₀ ∈ L^k(P₀)` for every `k : ℕ`. Then the quenched average
`v ↦ ∫ ω, ∫ w, ⟨f(σ.1) ∏_r ψ_r(S_v(w, σ_r))⟩ ∂γ_sh ∂P₀` is differentiable at `v₀ ∈ (0, 1)`, all
six covariance groups are `P₀`-integrable, and its derivative is `(1 / 2)` times their `P₀`-average.
This is the model-free engine for Talagrand's Lemma 3.2.8 and Theorem 3.2.14. -/
theorem hasDerivAt_integral_integral_pi_tilted_prod_gaussianReal_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω)
    [Fintype K] [Fintype R] [DecidableEq R]
    {κ : ℝ} (hκ : 0 < κ)
    {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (horth : ∀ x, X x ⬝ᵥ Y = 0)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu₂ : Differentiable ℝ (deriv u))
    (hu0 : ∀ x, u x ≤ 0) {D₁ D₂ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (v : ℝ) (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (v : ℝ) (ω : Ω) (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ ω p.1 + u (S v w p))
    let C_off (x y : E) : ℝ := X x ⬝ᵥ X y - Y ⬝ᵥ Y
    let C_diag (x : E) : ℝ := X x ⬝ᵥ X x - (Y ⬝ᵥ Y + c_ξ ^ 2)
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    let ψ_dd (r : R) (x : ℝ) : ℝ :=
      deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x +
        ψ r x * deriv (deriv u) x + ψ r x * deriv u x ^ 2
    let I_diag1 (i : R) (ω : Ω) : ℝ :=
      ∫ w, ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * C_diag (σ i).1 *
          (ψ_dd i (S v₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
        ∂(Measure.pi fun _ : R => ν v₀ ω w) ∂γ_sh
    let I_off1 (i j : R) (ω : Ω) : ℝ :=
      ∫ w, ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
          (ψ_d i (S v₀ w (σ i)) * ψ_d j (S v₀ w (σ j)) *
            ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v₀ w (σ r)))
        ∂(Measure.pi fun _ : R => ν v₀ ω w) ∂γ_sh
    let I_off2 (i : R) (ω : Ω) : ℝ :=
      ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
          (ψ_d i (S v₀ w (σ (some i))) *
            ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ (some r)))) *
          deriv u (S v₀ w (σ none))
        ∂(Measure.pi fun _ : Option R => ν v₀ ω w) ∂γ_sh
    let I_diag2 (ω : Ω) : ℝ :=
      ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
          (∏ r, ψ r (S v₀ w (σ (some r)))) *
          (deriv (deriv u) (S v₀ w (σ none)) + deriv u (S v₀ w (σ none)) ^ 2)
        ∂(Measure.pi fun _ : Option R => ν v₀ ω w) ∂γ_sh
    let I_off3 (j : R) (ω : Ω) : ℝ :=
      ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
          (ψ_d j (S v₀ w (σ (some j))) *
            ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ w (σ (some r)))) *
          deriv u (S v₀ w (σ none))
        ∂(Measure.pi fun _ : Option R => ν v₀ ω w) ∂γ_sh
    let I_off4 (ω : Ω) : ℝ :=
      ∫ w, ∫ σ : Option (Option R) → E × ℝ,
        f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
          (∏ r, ψ r (S v₀ w (σ (some (some r))))) *
          deriv u (S v₀ w (σ none)) * deriv u (S v₀ w (σ (some none)))
        ∂(Measure.pi fun _ : Option (Option R) => ν v₀ ω w) ∂γ_sh
    (∀ i : R, Integrable (I_diag1 i) P₀) ∧
      (∀ i : R, ∀ j ∈ Finset.univ.erase i, Integrable (I_off1 i j) P₀) ∧
      (∀ i : R, Integrable (I_off2 i) P₀) ∧
      Integrable I_diag2 P₀ ∧
      (∀ j : R, Integrable (I_off3 j) P₀) ∧
      Integrable I_off4 P₀ ∧
      HasDerivAt
        (fun v => ∫ ω, ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
          ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh ∂P₀)
        ((1 / 2) * (
          (∑ i : R, ∫ ω, I_diag1 i ω ∂P₀) +
          (∑ i : R, ∑ j ∈ Finset.univ.erase i, ∫ ω, I_off1 i j ω ∂P₀) -
          (Fintype.card R : ℝ) * ∑ i : R, ∫ ω, I_off2 i ω ∂P₀ -
          (Fintype.card R : ℝ) * ∫ ω, I_diag2 ω ∂P₀ -
          (Fintype.card R : ℝ) * ∑ j : R, ∫ ω, I_off3 j ω ∂P₀ +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) * ∫ ω, I_off4 ω ∂P₀))
        v₀ := by
  intro γ_sh S ν C_off C_diag ψ_d ψ_dd I_diag1 I_off1 I_off2 I_diag2 I_off3 I_off4
  have hc₀ : ∀ ω, 0 ≤ c₀ ω := fun ω =>
    nonneg_of_confining_of_neg_le (hE₀_conf ω) (hE₀_low ω)
  have : IsFiniteMeasure P₀ :=
    (integrable_const_iff.1 (by simpa using hmom 0 : Integrable (fun _ => (1 : ℝ)) P₀)).resolve_left
      one_ne_zero
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hd2u : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  set C_Y : ℝ := ∑ k : K, Y k ^ 2
  set C_cov_bd : ℝ := (∑ _k : K, |L_X| ^ 2) + C_Y + c_ξ ^ 2
  have hCcov_nn : 0 ≤ C_cov_bd := by
    dsimp only [C_cov_bd, C_Y]
    have : 0 ≤ ∑ k : K, Y k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : 0 ≤ ∑ _k : K, |L_X| ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hCoff_le : ∀ x y : E,
      |C_off x y| ≤ C_cov_bd * (1 + ‖x‖) ^ n_X * (1 + ‖y‖) ^ n_X :=
    abs_dotProduct_sub_dotProduct_le_of_abs_le_pow hXb c_ξ
  have hCdiag_le : ∀ x : E, |C_diag x| ≤ C_cov_bd * (1 + ‖x‖) ^ (2 * n_X) :=
    cdiag_le_of_poly_bound hXb c_ξ
  -- Bounds on `ψ`, `ψ_d`, `ψ_dd`, `u'' + u'^2`:
  obtain ⟨B_ψ, hBψ1, hψ_le_B, hdu_le_B, hψd_le_B, hψdd_le_B, hu2_le_B⟩ :
      ∃ B_ψ : ℝ, 1 ≤ B_ψ ∧
        (∀ r x, |ψ r x| ≤ B_ψ) ∧
        (∀ x, |deriv u x| ≤ B_ψ) ∧
        (∀ r x, |ψ_d r x| ≤ 2 * B_ψ ^ 2) ∧
        (∀ r x, |ψ_dd r x| ≤ 5 * B_ψ ^ 3) ∧
        (∀ x, |deriv (deriv u) x + deriv u x ^ 2| ≤ 2 * B_ψ ^ 2) := by
    let b : ℝ := 1 + |M₀| + |M₁| + |M₂| + |D₁| + |D₂|
    have hb1 : 1 ≤ b := by
      dsimp only [b]
      linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg M₂, abs_nonneg D₁, abs_nonneg D₂]
    have h0 : ∀ r x, |ψ r x| ≤ b := fun r x => (hM₀ r x).trans ((le_abs_self _).trans (by
      dsimp only [b]; linarith [abs_nonneg M₁, abs_nonneg M₂, abs_nonneg D₁, abs_nonneg D₂]))
    have hd1 : ∀ r x, |deriv (ψ r) x| ≤ b := fun r x => (hM₁ r x).trans ((le_abs_self _).trans (by
      dsimp only [b]; linarith [abs_nonneg M₀, abs_nonneg M₂, abs_nonneg D₁, abs_nonneg D₂]))
    have hd2 : ∀ r x, |deriv (deriv (ψ r)) x| ≤ b := fun r x =>
      (hM₂ r x).trans ((le_abs_self _).trans (by
        dsimp only [b]; linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D₁, abs_nonneg D₂]))
    have hdu1 : ∀ x, |deriv u x| ≤ b := fun x => (hD₁ x).trans ((le_abs_self _).trans (by
      dsimp only [b]; linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg M₂, abs_nonneg D₂]))
    have hdu2 : ∀ x, |deriv (deriv u) x| ≤ b := fun x => (hD₂ x).trans ((le_abs_self _).trans (by
      dsimp only [b]; linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg M₂, abs_nonneg D₁]))
    refine ⟨b, hb1, h0, hdu1, fun r x => ?_, fun r x => ?_, fun x => ?_⟩
    · dsimp only [ψ_d]
      have h_1 : |deriv (ψ r) x| ≤ b ^ 2 :=
        (hd1 r x).trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (by omega : 1 ≤ 2))
      have h_2 : |ψ r x * deriv u x| ≤ b ^ 2 := by
        rw [abs_mul, sq]
        exact mul_le_mul (h0 r x) (hdu1 x) (abs_nonneg _) (zero_le_one.trans hb1)
      linarith [abs_add_le (deriv (ψ r) x) (ψ r x * deriv u x)]
    · dsimp only [ψ_dd]
      have h_1 : |deriv (deriv (ψ r)) x| ≤ b ^ 3 :=
        (hd2 r x).trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (by omega : 1 ≤ 3))
      have h_2 : |2 * deriv (ψ r) x * deriv u x| ≤ 2 * b ^ 3 := by
        rw [abs_mul, abs_mul, abs_two, mul_assoc]
        have hp : |deriv (ψ r) x| * |deriv u x| ≤ b ^ 2 := by
          rw [sq]; exact mul_le_mul (hd1 r x) (hdu1 x) (abs_nonneg _) (zero_le_one.trans hb1)
        exact mul_le_mul_of_nonneg_left (hp.trans (pow_le_pow_right₀ hb1 (by omega))) zero_le_two
      have h_3 : |ψ r x * deriv (deriv u) x| ≤ b ^ 3 := by
        rw [abs_mul]
        have hp : |ψ r x| * |deriv (deriv u) x| ≤ b ^ 2 := by
          rw [sq]; exact mul_le_mul (h0 r x) (hdu2 x) (abs_nonneg _) (zero_le_one.trans hb1)
        exact hp.trans (pow_le_pow_right₀ hb1 (by omega))
      have h_4 : |ψ r x * deriv u x ^ 2| ≤ b ^ 3 := by
        rw [abs_mul, abs_pow]
        exact (mul_le_mul (h0 r x) (pow_le_pow_left₀ (abs_nonneg _) (hdu1 x) 2) (by positivity)
          (zero_le_one.trans hb1)).trans_eq (by ring)
      linarith [abs_add_le (deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x +
          ψ r x * deriv (deriv u) x) (ψ r x * deriv u x ^ 2),
        abs_add_le (deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x)
          (ψ r x * deriv (deriv u) x),
        abs_add_le (deriv (deriv (ψ r)) x) (2 * deriv (ψ r) x * deriv u x)]
    · have h_1 : |deriv (deriv u) x| ≤ b ^ 2 :=
        (hdu2 x).trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (by omega : 1 ≤ 2))
      have h_2 : |deriv u x ^ 2| ≤ b ^ 2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hdu1 x) 2
      linarith [abs_add_le (deriv (deriv u) x) (deriv u x ^ 2)]
  -- Measurability of `S v w (p.2 o)` and `C_off`, `C_diag`:
  have hS_joint : ∀ (ι : Type _) (v : ℝ) (o : ι),
      Measurable fun p : (K → ℝ) × (ι → E × ℝ) => S v p.1 (p.2 o) := fun ι v o => by
    have hdotX : Measurable fun p : (K → ℝ) × (ι → E × ℝ) => X (p.2 o).1 ⬝ᵥ p.1 :=
      Finset.measurable_sum _ fun k _ =>
        ((hXm k).comp (measurable_fst.comp ((measurable_pi_apply o).comp measurable_snd))).mul
          ((measurable_pi_apply k).comp measurable_fst)
    have hdotY : Measurable fun p : (K → ℝ) × (ι → E × ℝ) => Y ⬝ᵥ p.1 :=
      Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)
    exact (hdotX.const_mul _).add
      ((hdotY.add ((measurable_snd.comp ((measurable_pi_apply o).comp measurable_snd)).const_mul
        c_ξ)).const_mul _)
  have hS_joint_R := hS_joint R
  have hS_joint_O := hS_joint (Option R)
  have hS_joint_OO := hS_joint (Option (Option R))
  have hCdiag_m : Measurable C_diag := by
    dsimp only [C_diag, dotProduct]
    exact (Finset.measurable_sum _ fun k _ => (hXm k).mul (hXm k)).sub measurable_const
  have hCoff_m : Measurable fun q : E × E => C_off q.1 q.2 := by
    dsimp only [C_off, dotProduct]
    exact (Finset.measurable_sum _ fun k _ =>
      ((hXm k).comp measurable_fst).mul ((hXm k).comp measurable_snd)).sub measurable_const
  have hfb_p : ∀ σ : R → E × ℝ, |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
    abs_comp_le_prod_of_injective hfb norm_fst_le Function.injective_id
  -- Instantiate `measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal` for the 4 shapes:
  obtain ⟨C_d0, hCd0, hctrl0⟩ :=
    measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal (ι := R) μ P₀ hκ hB₀ hc₀ hmom
      hE₀m hE₀_conf hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁ m_f
  obtain ⟨C_dR, hCdR, hctrlR⟩ :=
    measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal (ι := R) μ P₀ hκ hB₀ hc₀ hmom
      hE₀m hE₀_conf hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁ (m_f + 2 * n_X)
  obtain ⟨C_dO, hCdO, hctrlO⟩ :=
    measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal (ι := Option R) μ P₀ hκ hB₀ hc₀
      hmom hE₀m hE₀_conf hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁ (m_f + 2 * n_X)
  obtain ⟨C_dOO, hCdOO, hctrlOO⟩ :=
    measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal (ι := Option (Option R)) μ P₀ hκ
      hB₀ hc₀ hmom hE₀m hE₀_conf hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁ (m_f + 2 * n_X)
  -- Uniform constant `M_mul` bounding all bounded `ψ` products in the 6 covariance groups:
  set M_mul : ℝ := 5 * B_ψ ^ (Fintype.card R + 4)
  have hMmul0 : 0 ≤ M_mul := by positivity
  set C_G_unif : ℝ := |C_f| * C_cov_bd * M_mul
  have hCG_nn : 0 ≤ C_G_unif := by positivity
  have hψd_m : ∀ r, Measurable (ψ_d r) := fun r =>
    (measurable_deriv (ψ r)).add ((hψd r).continuous.measurable.mul hdu)
  have hψdd_m : ∀ r, Measurable (ψ_dd r) := fun r =>
    (((measurable_deriv (deriv (ψ r))).add
      (((measurable_deriv (ψ r)).const_mul 2).mul hdu)).add
      ((hψd r).continuous.measurable.mul hd2u)).add
      ((hψd r).continuous.measurable.mul (hdu.pow_const 2))
  -- `hdu_le_B` already in context
  have hCoff_prod : ∀ (ι : Type _) [Fintype ι] (o₁ o₂ : ι) (σ : ι → E × ℝ),
      |C_off (σ o₁).1 (σ o₂).1| ≤ C_cov_bd * ∏ o, (1 + ‖σ o‖) ^ (2 * n_X) :=
    fun ι _ o₁ o₂ σ => by
      have h1 : (1 + ‖(σ o₁).1‖) ^ n_X ≤ ∏ o, (1 + ‖σ o‖) ^ n_X :=
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o₁)) 1) _).trans
          (one_add_norm_pow_le_prod σ n_X o₁)
      have h2 : (1 + ‖(σ o₂).1‖) ^ n_X ≤ ∏ o, (1 + ‖σ o‖) ^ n_X :=
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o₂)) 1) _).trans
          (one_add_norm_pow_le_prod σ n_X o₂)
      have h12 := mul_le_mul h1 h2 (by positivity) (Finset.prod_nonneg fun _ _ => by positivity)
      rw [← Finset.prod_mul_distrib] at h12
      have h12' : (∏ o, (1 + ‖σ o‖) ^ n_X * (1 + ‖σ o‖) ^ n_X) =
          ∏ o, (1 + ‖σ o‖) ^ (2 * n_X) :=
        Finset.prod_congr rfl fun o _ => by rw [two_mul, pow_add]
      rw [h12'] at h12
      calc |C_off (σ o₁).1 (σ o₂).1|
          ≤ C_cov_bd * ((1 + ‖(σ o₁).1‖) ^ n_X * (1 + ‖(σ o₂).1‖) ^ n_X) := by
            linarith [hCoff_le (σ o₁).1 (σ o₂).1]
        _ ≤ C_cov_bd * ∏ o, (1 + ‖σ o‖) ^ (2 * n_X) :=
            mul_le_mul_of_nonneg_left h12 hCcov_nn
  have hCdiag_prod : ∀ (ι : Type _) [Fintype ι] (o₀ : ι) (σ : ι → E × ℝ),
      |C_diag (σ o₀).1| ≤ C_cov_bd * ∏ o, (1 + ‖σ o‖) ^ (2 * n_X) := fun ι _ o₀ σ =>
    (hCdiag_le (σ o₀).1).trans (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o₀)) 1) _).trans
        (one_add_norm_pow_le_prod σ (2 * n_X) o₀)) hCcov_nn)
  have hg1_all : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 → ∀ i : R,
      let J : Ω → ℝ := fun ω => ∫ w, ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * C_diag (σ i).1 *
          (ψ_dd i (S v w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ r)))
        ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh
      Measurable J ∧
        (∀ ω, |J ω| ≤ C_G_unif * C_dR * (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card R)) ∧
        Integrable J P₀ := fun {v} hv0 hv1 i => by
    refine hctrlR hv0 hv1
      (G := fun w σ => f (fun r => (σ r).1) * C_diag (σ i).1 *
        (ψ_dd i (S v w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ r))))
      (((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        (hCdiag_m.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)))).mul
        (((hψdd_m i).comp (hS_joint_R v i)).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hS_joint_R v r))))
      hCG_nn fun w σ => ?_
    have hfc := abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) (hCdiag_prod R i σ)
    have hm : |ψ_dd i (S v w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ r))| ≤ M_mul := by
      rw [abs_mul, Finset.abs_prod]
      have hp : ∏ r ∈ Finset.univ.erase i, |ψ r (S v w (σ r))| ≤
          ∏ _r ∈ Finset.univ.erase i, B_ψ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le_B r (S v w (σ r))
      have h1 := mul_le_mul (hψdd_le_B i (S v w (σ i))) hp
        (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      refine h1.trans ?_
      rw [Finset.prod_const]
      have hle_card : (Finset.univ.erase i).card ≤ Fintype.card R := Finset.card_le_univ _
      have hpow : B_ψ ^ 3 * B_ψ ^ (Finset.univ.erase i).card ≤ B_ψ ^ (Fintype.card R + 4) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hBψ1 (by omega)
      dsimp only [M_mul]
      linarith [pow_nonneg (zero_le_one.trans hBψ1) (Fintype.card R + 4)]
    rw [abs_mul]
    exact (mul_le_mul hfc hm (abs_nonneg _) (by positivity)).trans_eq (by
      dsimp only [C_G_unif]; ring)
  have hg2_all : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 → ∀ i : R, ∀ j ∈ Finset.univ.erase i,
      let J : Ω → ℝ := fun ω => ∫ w, ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
          (ψ_d i (S v w (σ i)) * ψ_d j (S v w (σ j)) *
            ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v w (σ r)))
        ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh
      Measurable J ∧
        (∀ ω, |J ω| ≤ C_G_unif * C_dR * (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card R)) ∧
        Integrable J P₀ := fun {v} hv0 hv1 i j _ => by
    refine hctrlR hv0 hv1
      (G := fun w σ => f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
        (ψ_d i (S v w (σ i)) * ψ_d j (S v w (σ j)) *
          ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v w (σ r))))
      (((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        (hCoff_m.comp ((measurable_fst.comp ((measurable_pi_apply i).comp
          measurable_snd)).prodMk (measurable_fst.comp ((measurable_pi_apply j).comp
            measurable_snd))))).mul
        ((((hψd_m i).comp (hS_joint_R v i)).mul ((hψd_m j).comp (hS_joint_R v j))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hS_joint_R v r))))
      hCG_nn fun w σ => ?_
    have hfc := abs_mul_le_mul_prod_one_add_norm_pow (hfb_p σ) (hCoff_prod R i j σ)
    have hm : |ψ_d i (S v w (σ i)) * ψ_d j (S v w (σ j)) *
        ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v w (σ r))| ≤ M_mul := by
      rw [abs_mul, abs_mul, Finset.abs_prod]
      have hp : ∏ r ∈ (Finset.univ.erase i).erase j, |ψ r (S v w (σ r))| ≤
          ∏ _r ∈ (Finset.univ.erase i).erase j, B_ψ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le_B r (S v w (σ r))
      have h12 := mul_le_mul (hψd_le_B i (S v w (σ i))) (hψd_le_B j (S v w (σ j)))
        (abs_nonneg _) (by positivity)
      have h1 := mul_le_mul h12 hp (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      refine h1.trans ?_
      rw [Finset.prod_const]
      have hle_card : ((Finset.univ.erase i).erase j).card ≤ Fintype.card R :=
        Finset.card_le_univ _
      have hpow : B_ψ ^ 2 * B_ψ ^ 2 * B_ψ ^ ((Finset.univ.erase i).erase j).card ≤
          B_ψ ^ (Fintype.card R + 4) := by
        rw [← pow_add, ← pow_add]
        exact pow_le_pow_right₀ hBψ1 (by omega)
      calc 2 * B_ψ ^ 2 * (2 * B_ψ ^ 2) * B_ψ ^ ((Finset.univ.erase i).erase j).card
          = 4 * (B_ψ ^ 2 * B_ψ ^ 2 * B_ψ ^ ((Finset.univ.erase i).erase j).card) := by ring
        _ ≤ 4 * B_ψ ^ (Fintype.card R + 4) := mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ ≤ M_mul := by
            dsimp only [M_mul]
            linarith [pow_nonneg (zero_le_one.trans hBψ1) (Fintype.card R + 4)]
    rw [abs_mul]
    exact (mul_le_mul hfc hm (abs_nonneg _) (by positivity)).trans_eq (by
      dsimp only [C_G_unif]; ring)
  have hg3_all : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 → ∀ i : R,
      let J : Ω → ℝ := fun ω => ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
          (ψ_d i (S v w (σ (some i))) *
            ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ (some r)))) *
          deriv u (S v w (σ none))
        ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh
      Measurable J ∧
        (∀ ω, |J ω| ≤ C_G_unif * C_dO *
          (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option R))) ∧
        Integrable J P₀ := fun {v} hv0 hv1 i => by
    refine hctrlO hv0 hv1
      (G := fun w σ => f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
        (ψ_d i (S v w (σ (some i))) *
          ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ (some r)))) *
        deriv u (S v w (σ none)))
      ((((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))).mul
        (hCoff_m.comp ((measurable_fst.comp ((measurable_pi_apply (some i)).comp
          measurable_snd)).prodMk (measurable_fst.comp ((measurable_pi_apply none).comp
            measurable_snd))))).mul
        (((hψd_m i).comp (hS_joint_O v (some i))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hS_joint_O v (some r))))).mul
        (hdu.comp (hS_joint_O v none)))
      hCG_nn fun w σ => ?_
    have hf_o := abs_comp_some_le_prod hfb_p σ
    have hfc := abs_mul_le_mul_prod_one_add_norm_pow hf_o (hCoff_prod (Option R) (some i) none σ)
    have hm : |(ψ_d i (S v w (σ (some i))) *
        ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ (some r)))) *
        deriv u (S v w (σ none))| ≤ M_mul := by
      rw [abs_mul, abs_mul, Finset.abs_prod]
      have hp : ∏ r ∈ Finset.univ.erase i, |ψ r (S v w (σ (some r)))| ≤
          ∏ _r ∈ Finset.univ.erase i, B_ψ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le_B r (S v w (σ (some r)))
      have h12 := mul_le_mul (hψd_le_B i (S v w (σ (some i)))) hp
        (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      have h1 := mul_le_mul h12 (hdu_le_B (S v w (σ none))) (abs_nonneg _) (by positivity)
      refine h1.trans ?_
      rw [Finset.prod_const]
      have hle_card : (Finset.univ.erase i).card ≤ Fintype.card R := Finset.card_le_univ _
      have hpow : B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase i).card * B_ψ ≤
          B_ψ ^ (Fintype.card R + 4) := by
        have : B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase i).card * B_ψ =
            B_ψ ^ (2 + (Finset.univ.erase i).card + 1) := by
          rw [pow_add, pow_add, pow_one]
        rw [this]
        exact pow_le_pow_right₀ hBψ1 (by omega)
      calc 2 * B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase i).card * B_ψ
          = 2 * (B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase i).card * B_ψ) := by ring
        _ ≤ 2 * B_ψ ^ (Fintype.card R + 4) := mul_le_mul_of_nonneg_left hpow zero_le_two
        _ ≤ M_mul := by
            dsimp only [M_mul]
            linarith [pow_nonneg (zero_le_one.trans hBψ1) (Fintype.card R + 4)]
    rw [mul_assoc (_ * _), abs_mul]
    exact (mul_le_mul hfc hm (abs_nonneg _) (by positivity)).trans_eq (by
      dsimp only [C_G_unif]; ring)
  have hg4_all : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 →
      let J : Ω → ℝ := fun ω => ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
          (∏ r, ψ r (S v w (σ (some r)))) *
          (deriv (deriv u) (S v w (σ none)) + deriv u (S v w (σ none)) ^ 2)
        ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh
      Measurable J ∧
        (∀ ω, |J ω| ≤ C_G_unif * C_dO *
          (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option R))) ∧
        Integrable J P₀ := fun {v} hv0 hv1 => by
    refine hctrlO hv0 hv1
      (G := fun w σ => f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
        (∏ r, ψ r (S v w (σ (some r)))) *
        (deriv (deriv u) (S v w (σ none)) + deriv u (S v w (σ none)) ^ 2))
      ((((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))).mul
        (hCdiag_m.comp (measurable_fst.comp ((measurable_pi_apply none).comp
          measurable_snd)))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp (hS_joint_O v (some r)))).mul
        ((hd2u.add (hdu.pow_const 2)).comp (hS_joint_O v none)))
      hCG_nn fun w σ => ?_
    have hf_o := abs_comp_some_le_prod hfb_p σ
    have hfc := abs_mul_le_mul_prod_one_add_norm_pow hf_o (hCdiag_prod (Option R) none σ)
    have hm : |(∏ r, ψ r (S v w (σ (some r)))) *
        (deriv (deriv u) (S v w (σ none)) + deriv u (S v w (σ none)) ^ 2)| ≤ M_mul := by
      rw [abs_mul, Finset.abs_prod]
      have hp : ∏ r : R, |ψ r (S v w (σ (some r)))| ≤ ∏ _r : R, B_ψ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le_B r (S v w (σ (some r)))
      have h1 := mul_le_mul hp (hu2_le_B (S v w (σ none))) (abs_nonneg _) (by positivity)
      refine h1.trans ?_
      rw [Finset.prod_const, Finset.card_univ]
      have hpow : B_ψ ^ Fintype.card R * B_ψ ^ 2 ≤ B_ψ ^ (Fintype.card R + 4) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hBψ1 (by omega)
      calc B_ψ ^ Fintype.card R * (2 * B_ψ ^ 2)
          = 2 * (B_ψ ^ Fintype.card R * B_ψ ^ 2) := by ring
        _ ≤ 2 * B_ψ ^ (Fintype.card R + 4) := mul_le_mul_of_nonneg_left hpow zero_le_two
        _ ≤ M_mul := by
            dsimp only [M_mul]
            linarith [pow_nonneg (zero_le_one.trans hBψ1) (Fintype.card R + 4)]
    rw [mul_assoc (_ * _), abs_mul]
    exact (mul_le_mul hfc hm (abs_nonneg _) (by positivity)).trans_eq (by
      dsimp only [C_G_unif]; ring)
  have hg5_all : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 → ∀ j : R,
      let J : Ω → ℝ := fun ω => ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
          (ψ_d j (S v w (σ (some j))) *
            ∏ r ∈ Finset.univ.erase j, ψ r (S v w (σ (some r)))) *
          deriv u (S v w (σ none))
        ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh
      Measurable J ∧
        (∀ ω, |J ω| ≤ C_G_unif * C_dO *
          (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option R))) ∧
        Integrable J P₀ := fun {v} hv0 hv1 j => by
    refine hctrlO hv0 hv1
      (G := fun w σ => f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
        (ψ_d j (S v w (σ (some j))) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S v w (σ (some r)))) *
        deriv u (S v w (σ none)))
      ((((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))).mul
        (hCoff_m.comp ((measurable_fst.comp ((measurable_pi_apply none).comp
          measurable_snd)).prodMk (measurable_fst.comp ((measurable_pi_apply (some j)).comp
            measurable_snd))))).mul
        (((hψd_m j).comp (hS_joint_O v (some j))).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hS_joint_O v (some r))))).mul
        (hdu.comp (hS_joint_O v none)))
      hCG_nn fun w σ => ?_
    have hf_o := abs_comp_some_le_prod hfb_p σ
    have hfc := abs_mul_le_mul_prod_one_add_norm_pow hf_o (hCoff_prod (Option R) none (some j) σ)
    have hm : |(ψ_d j (S v w (σ (some j))) *
        ∏ r ∈ Finset.univ.erase j, ψ r (S v w (σ (some r)))) *
        deriv u (S v w (σ none))| ≤ M_mul := by
      rw [abs_mul, abs_mul, Finset.abs_prod]
      have hp : ∏ r ∈ Finset.univ.erase j, |ψ r (S v w (σ (some r)))| ≤
          ∏ _r ∈ Finset.univ.erase j, B_ψ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le_B r (S v w (σ (some r)))
      have h12 := mul_le_mul (hψd_le_B j (S v w (σ (some j)))) hp
        (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      have h1 := mul_le_mul h12 (hdu_le_B (S v w (σ none))) (abs_nonneg _) (by positivity)
      refine h1.trans ?_
      rw [Finset.prod_const]
      have hle_card : (Finset.univ.erase j).card ≤ Fintype.card R := Finset.card_le_univ _
      have hpow : B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase j).card * B_ψ ≤
          B_ψ ^ (Fintype.card R + 4) := by
        have : B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase j).card * B_ψ =
            B_ψ ^ (2 + (Finset.univ.erase j).card + 1) := by
          rw [pow_add, pow_add, pow_one]
        rw [this]
        exact pow_le_pow_right₀ hBψ1 (by omega)
      calc 2 * B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase j).card * B_ψ
          = 2 * (B_ψ ^ 2 * B_ψ ^ (Finset.univ.erase j).card * B_ψ) := by ring
        _ ≤ 2 * B_ψ ^ (Fintype.card R + 4) := mul_le_mul_of_nonneg_left hpow zero_le_two
        _ ≤ M_mul := by
            dsimp only [M_mul]
            linarith [pow_nonneg (zero_le_one.trans hBψ1) (Fintype.card R + 4)]
    rw [mul_assoc (_ * _), abs_mul]
    exact (mul_le_mul hfc hm (abs_nonneg _) (by positivity)).trans_eq (by
      dsimp only [C_G_unif]; ring)
  have hg6_all : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 →
      let J : Ω → ℝ := fun ω => ∫ w, ∫ σ : Option (Option R) → E × ℝ,
        f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
          (∏ r, ψ r (S v w (σ (some (some r))))) *
          deriv u (S v w (σ none)) * deriv u (S v w (σ (some none)))
        ∂(Measure.pi fun _ : Option (Option R) => ν v ω w) ∂γ_sh
      Measurable J ∧
        (∀ ω, |J ω| ≤ C_G_unif * C_dOO *
          (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option (Option R)))) ∧
        Integrable J P₀ := fun {v} hv0 hv1 => by
    refine hctrlOO hv0 hv1 ?_ hCG_nn fun w σ => ?_
    · have hm_f : Measurable (fun p : (K → ℝ) × (Option (Option R) → E × ℝ) =>
          f (fun r => (p.2 (some (some r))).1)) :=
        hf.comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply (some (some r))).comp measurable_snd))
      have hm_C : Measurable (fun p : (K → ℝ) × (Option (Option R) → E × ℝ) =>
          C_off (p.2 none).1 (p.2 (some none)).1) :=
        hCoff_m.comp ((measurable_fst.comp ((measurable_pi_apply none).comp
          measurable_snd)).prodMk (measurable_fst.comp ((measurable_pi_apply (some none)).comp
            measurable_snd)))
      have hm_pr : Measurable (fun p : (K → ℝ) × (Option (Option R) → E × ℝ) =>
          ∏ r, ψ r (S v p.1 (p.2 (some (some r))))) :=
        Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp (hS_joint_OO v (some (some r)))
      have hm_du1 : Measurable (fun p : (K → ℝ) × (Option (Option R) → E × ℝ) =>
          deriv u (S v p.1 (p.2 none))) :=
        hdu.comp (hS_joint_OO v none)
      have hm_du2 : Measurable (fun p : (K → ℝ) × (Option (Option R) → E × ℝ) =>
          deriv u (S v p.1 (p.2 (some none)))) :=
        hdu.comp (hS_joint_OO v (some none))
      exact (((hm_f.mul hm_C).mul hm_pr).mul hm_du1).mul hm_du2
    · have hf_oo : |f (fun r => (σ (some (some r))).1)| ≤
          |C_f| * ∏ o, (1 + ‖σ o‖) ^ m_f :=
        abs_comp_some_le_prod (abs_comp_some_le_prod hfb_p) σ
      have hfc := abs_mul_le_mul_prod_one_add_norm_pow hf_oo
        (hCoff_prod (Option (Option R)) none (some none) σ)
      have hm : |(∏ r, ψ r (S v w (σ (some (some r))))) *
          deriv u (S v w (σ none)) * deriv u (S v w (σ (some none)))| ≤ M_mul := by
        rw [abs_mul, abs_mul, Finset.abs_prod]
        have hB0_nn : 0 ≤ B_ψ := zero_le_one.trans hBψ1
        have hp : ∏ r : R, |ψ r (S v w (σ (some (some r))))| ≤ B_ψ ^ Fintype.card R :=
          (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ =>
            hψ_le_B r (S v w (σ (some (some r))))).trans_eq
            (by rw [Finset.prod_const, Finset.card_univ])
        have h12 : (∏ r : R, |ψ r (S v w (σ (some (some r))))|) * |deriv u (S v w (σ none))| ≤
            B_ψ ^ Fintype.card R * B_ψ :=
          mul_le_mul hp (hdu_le_B (S v w (σ none))) (abs_nonneg _) (pow_nonneg hB0_nn _)
        have h1 := mul_le_mul h12 (hdu_le_B (S v w (σ (some none)))) (abs_nonneg _)
          (mul_nonneg (pow_nonneg hB0_nn _) hB0_nn)
        refine h1.trans ?_
        have hpow : B_ψ ^ Fintype.card R * B_ψ * B_ψ ≤ B_ψ ^ (Fintype.card R + 4) := by
          have heq_p : B_ψ ^ Fintype.card R * B_ψ * B_ψ = B_ψ ^ (Fintype.card R + 1 + 1) := by
            rw [pow_succ, pow_succ]
          rw [heq_p]
          exact pow_le_pow_right₀ hBψ1 (by omega)
        have hBn4 : 0 ≤ B_ψ ^ (Fintype.card R + 4) := pow_nonneg hB0_nn _
        calc B_ψ ^ Fintype.card R * B_ψ * B_ψ ≤ 1 * B_ψ ^ (Fintype.card R + 4) := by
              rw [one_mul]; exact hpow
          _ ≤ 5 * B_ψ ^ (Fintype.card R + 4) := mul_le_mul_of_nonneg_right (by norm_num) hBn4
      set P1 : ℝ := (f fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1
      set P2 : ℝ := ∏ r, ψ r (S v w (σ (some (some r))))
      set D_n : ℝ := deriv u (S v w (σ none))
      set D_sn : ℝ := deriv u (S v w (σ (some none)))
      change |P1 * P2 * D_n * D_sn| ≤ C_G_unif * ∏ o, (1 + ‖σ o‖) ^ (m_f + 2 * n_X)
      have hassoc : P1 * P2 * D_n * D_sn = P1 * (P2 * D_n * D_sn) := by ring
      rw [hassoc, abs_mul]
      have hfc_nn : 0 ≤ (|C_f| * C_cov_bd) *
          ∏ o : Option (Option R), (1 + ‖σ o‖) ^ (m_f + 2 * n_X) :=
        mul_nonneg (mul_nonneg (abs_nonneg _) hCcov_nn)
          (Finset.prod_nonneg fun _ _ => pow_nonneg (add_nonneg zero_le_one (norm_nonneg _)) _)
      exact (mul_le_mul hfc hm (abs_nonneg _) hfc_nn).trans_eq (mul_right_comm _ _ _)
  -- Specialize at `v₀` for the 6 integrability outputs:
  have hg1_v0 := hg1_all hv₀.1.le hv₀.2.le
  have hg2_v0 := hg2_all hv₀.1.le hv₀.2.le
  have hg3_v0 := hg3_all hv₀.1.le hv₀.2.le
  have hg4_v0 := hg4_all hv₀.1.le hv₀.2.le
  have hg5_v0 := hg5_all hv₀.1.le hv₀.2.le
  have hg6_v0 := hg6_all hv₀.1.le hv₀.2.le
  refine ⟨fun i => (hg1_v0 i).2.2, fun i j hj => (hg2_v0 i j hj).2.2,
    fun i => (hg3_v0 i).2.2, hg4_v0.2.2, fun j => (hg5_v0 j).2.2, hg6_v0.2.2, ?_⟩
  -- Dominated differentiation in `v` over `(Ω, P₀)`:
  have hIoo_nhds : Ioo (0 : ℝ) 1 ∈ 𝓝 v₀ := Ioo_mem_nhds hv₀.1 hv₀.2
  have hF_ctrl : ∀ v ∈ Ioo (0 : ℝ) 1,
      Integrable (fun ω => ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
        ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh) P₀ := fun v hv => by
    refine (hctrl0 hv.1.le hv.2.le
      ((hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
        (Finset.measurable_prod _ fun r _ =>
          (hψd r).continuous.measurable.comp (hS_joint_R v r)))
      (C_G := |C_f| * B_ψ ^ Fintype.card R) (by positivity) fun w σ => ?_).2.2
    rw [abs_mul]
    have hp : |∏ r, ψ r (S v w (σ r))| ≤ B_ψ ^ Fintype.card R := by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le_B r _).trans_eq
        (by simp)
    exact (mul_le_mul (hfb_p σ) hp (abs_nonneg _) (by positivity)).trans_eq (by ring)
  set D_ω : ℝ → Ω → ℝ := fun v ω =>
    (1 / 2) * (
      (∑ i : R, ∫ w, ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * C_diag (σ i).1 *
          (ψ_dd i (S v w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ r)))
        ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh) +
      (∑ i : R, ∑ j ∈ Finset.univ.erase i, ∫ w, ∫ σ : R → E × ℝ,
        f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
          (ψ_d i (S v w (σ i)) * ψ_d j (S v w (σ j)) *
            ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v w (σ r)))
        ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh) -
      (Fintype.card R : ℝ) * ∑ i : R, ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
          (ψ_d i (S v w (σ (some i))) *
            ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ (some r)))) *
          deriv u (S v w (σ none))
        ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh -
      (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
          (∏ r, ψ r (S v w (σ (some r)))) *
          (deriv (deriv u) (S v w (σ none)) + deriv u (S v w (σ none)) ^ 2)
        ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh -
      (Fintype.card R : ℝ) * ∑ j : R, ∫ w, ∫ σ : Option R → E × ℝ,
        f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
          (ψ_d j (S v w (σ (some j))) *
            ∏ r ∈ Finset.univ.erase j, ψ r (S v w (σ (some r)))) *
          deriv u (S v w (σ none))
        ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
        ∫ w, ∫ σ : Option (Option R) → E × ℝ,
          f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
            (∏ r, ψ r (S v w (σ (some (some r))))) *
            deriv u (S v w (σ none)) * deriv u (S v w (σ (some none)))
          ∂(Measure.pi fun _ : Option (Option R) => ν v ω w) ∂γ_sh)
  set n_R : ℝ := (Fintype.card R : ℝ)
  set b_P₀ : Ω → ℝ := fun ω =>
    n_R * (C_G_unif * C_dR * (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card R)) +
    n_R ^ 2 * (C_G_unif * C_dR * (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card R)) +
    (2 * n_R ^ 2 + n_R) *
      (C_G_unif * C_dO * (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option R))) +
    n_R * (n_R + 1) *
      (C_G_unif * C_dOO *
        (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option (Option R))))
  have hbP₀_int : Integrable b_P₀ P₀ :=
    (((((hmom _).const_mul _).const_mul _).add
      (((hmom _).const_mul _).const_mul _)).add
      (((hmom _).const_mul _).const_mul _)).add
      (((hmom _).const_mul _).const_mul _)
  have hDv0_int : Integrable (D_ω v₀) P₀ := by
    dsimp only [D_ω]
    exact ((((((integrable_finsetSum _ fun i _ => (hg1_v0 i).2.2).add
      (integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j hj => (hg2_v0 i j hj).2.2)).sub
      ((integrable_finsetSum _ fun i _ => (hg3_v0 i).2.2).const_mul _)).sub
      (hg4_v0.2.2.const_mul _)).sub
      ((integrable_finsetSum _ fun j _ => (hg5_v0 j).2.2).const_mul _)).add
      (hg6_v0.2.2.const_mul _)).const_mul _
  have hdom_all : ∀ ω : Ω, ∀ v ∈ Ioo (0 : ℝ) 1, ‖D_ω v ω‖ ≤ b_P₀ ω := by
    intro ω v hv
    rw [Real.norm_eq_abs]
    have hg1 := hg1_all hv.1.le hv.2.le
    have hg2 := hg2_all hv.1.le hv.2.le
    have hg3 := hg3_all hv.1.le hv.2.le
    have hg4 := hg4_all hv.1.le hv.2.le
    have hg5 := hg5_all hv.1.le hv.2.le
    have hg6 := hg6_all hv.1.le hv.2.le
    set G1 : ℝ := ∑ i : R, ∫ w, ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * C_diag (σ i).1 *
        (ψ_dd i (S v w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ r)))
      ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh
    set G2 : ℝ := ∑ i : R, ∑ j ∈ Finset.univ.erase i, ∫ w, ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
        (ψ_d i (S v w (σ i)) * ψ_d j (S v w (σ j)) *
          ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v w (σ r)))
      ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh
    set G3 : ℝ := n_R * ∑ i : R, ∫ w, ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * C_off (σ (some i)).1 (σ none).1 *
        (ψ_d i (S v w (σ (some i))) *
          ∏ r ∈ Finset.univ.erase i, ψ r (S v w (σ (some r)))) *
        deriv u (S v w (σ none))
      ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh
    set G4 : ℝ := n_R * ∫ w, ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * C_diag (σ none).1 *
        (∏ r, ψ r (S v w (σ (some r)))) *
        (deriv (deriv u) (S v w (σ none)) + deriv u (S v w (σ none)) ^ 2)
      ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh
    set G5 : ℝ := n_R * ∑ j : R, ∫ w, ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * C_off (σ none).1 (σ (some j)).1 *
        (ψ_d j (S v w (σ (some j))) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S v w (σ (some r)))) *
        deriv u (S v w (σ none))
      ∂(Measure.pi fun _ : Option R => ν v ω w) ∂γ_sh
    set G6 : ℝ := n_R * (n_R + 1) * ∫ w, ∫ σ : Option (Option R) → E × ℝ,
      f (fun r => (σ (some (some r))).1) * C_off (σ none).1 (σ (some none)).1 *
        (∏ r, ψ r (S v w (σ (some (some r))))) *
        deriv u (S v w (σ none)) * deriv u (S v w (σ (some none)))
      ∂(Measure.pi fun _ : Option (Option R) => ν v ω w) ∂γ_sh
    change |(1 / 2) * (G1 + G2 - G3 - G4 - G5 + G6)| ≤ b_P₀ ω
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2)]
    set X1 := C_G_unif * C_dR * (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card R)
    set X2 := C_G_unif * C_dO * (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option R))
    set X3 := C_G_unif * C_dOO *
      (1 + B₀ ω + c₀ ω) ^ ((m_f + 2 * n_X) * Fintype.card (Option (Option R)))
    have hX1_0 : 0 ≤ X1 := by have := hB₀ ω; have := hc₀ ω; positivity
    have hn0 : 0 ≤ n_R := Nat.cast_nonneg _
    have hs1 : |G1| ≤ n_R * X1 :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun i _ => (hg1 i).2.1 ω).trans_eq (by simp [n_R, X1]))
    have hs2 : |G2| ≤ n_R ^ 2 * X1 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hin : ∀ i : R, |∑ j ∈ Finset.univ.erase i, ∫ w, ∫ σ : R → E × ℝ,
          f (fun r => (σ r).1) * C_off (σ i).1 (σ j).1 *
            (ψ_d i (S v w (σ i)) * ψ_d j (S v w (σ j)) *
              ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v w (σ r)))
          ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh| ≤ n_R * X1 := fun i => by
        refine (Finset.abs_sum_le_sum_abs _ _).trans
          ((Finset.sum_le_sum fun j hj => (hg2 i j hj).2.1 ω).trans ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard_le : ((Finset.univ.erase i).card : ℝ) ≤ n_R := by
          dsimp only [n_R]
          exact_mod_cast Finset.card_le_univ (Finset.univ.erase i)
        exact mul_le_mul_of_nonneg_right hcard_le hX1_0
      refine (Finset.sum_le_sum fun i _ => hin i).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp only [n_R]; ring
    have hs3 : |G3| ≤ n_R ^ 2 * X2 := by
      dsimp only [G3]
      rw [abs_mul, abs_of_nonneg hn0]
      have hin := (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun i _ => (hg3 i).2.1 ω).trans_eq
          (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
      exact (mul_le_mul_of_nonneg_left hin hn0).trans_eq (by dsimp only [n_R]; ring)
    have hs4 : |G4| ≤ n_R * X2 := by
      dsimp only [G4]; rw [abs_mul, abs_of_nonneg hn0]
      exact mul_le_mul_of_nonneg_left (hg4.2.1 ω) hn0
    have hs5 : |G5| ≤ n_R ^ 2 * X2 := by
      dsimp only [G5]
      rw [abs_mul, abs_of_nonneg hn0]
      have hin := (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun j _ => (hg5 j).2.1 ω).trans_eq
          (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
      exact (mul_le_mul_of_nonneg_left hin hn0).trans_eq (by dsimp only [n_R]; ring)
    have hs6 : |G6| ≤ n_R * (n_R + 1) * X3 := by
      dsimp only [G6]; rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hg6.2.1 ω) (by positivity)
    have htot : |G1 + G2 - G3 - G4 - G5 + G6| ≤ b_P₀ ω := by
      dsimp only [b_P₀]
      have ha1 := abs_add_le (G1 + G2 - G3 - G4 - G5) G6
      have ha2 := abs_sub (G1 + G2 - G3 - G4) G5
      have ha3 := abs_sub (G1 + G2 - G3) G4
      have ha4 := abs_sub (G1 + G2) G3
      have ha5 := abs_add_le G1 G2
      linarith
    exact (mul_le_of_le_one_left (abs_nonneg _) (by norm_num)).trans htot
  have hder_all : ∀ ω : Ω, ∀ v ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun v' => ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v' w (σ r))
        ∂(Measure.pi fun _ : R => ν v' ω w) ∂γ_sh) (D_ω v ω) v := fun ω v hv => by
    have hEω_m : Measurable (E₀ ω) := hE₀m.comp (measurable_const.prodMk measurable_id)
    exact hasDerivAt_integral_pi_tilted_prod_gaussianReal_sqrt μ hκ (hB₀ ω) hEω_m
      (hE₀_conf ω) (hE₀_low ω) X Y hXm hXb horth c_ξ hu hu₂ hu0 hD₁ hD₂
      ψ hψd hψ₂d hM₀ hM₁ hM₂ hf hfb hv
  have hd_P₀ := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P₀)
    (F := fun v ω => ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
      ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh)
    (F' := D_ω)
    (s := Ioo 0 1) hIoo_nhds
    (eventually_of_mem hIoo_nhds fun v hv => (hF_ctrl v hv).aestronglyMeasurable)
    (hF_ctrl v₀ hv₀) hDv0_int.aestronglyMeasurable
    (bound := b_P₀) (ae_of_all _ hdom_all) hbP₀_int (ae_of_all _ hder_all)).2
  refine hd_P₀.congr_deriv ?_
  set S_g1 : Ω → ℝ := fun ω => ∑ i : R, I_diag1 i ω
  set S_g2 : Ω → ℝ := fun ω => ∑ i : R, ∑ j ∈ Finset.univ.erase i, I_off1 i j ω
  set S_g3 : Ω → ℝ := fun ω => ∑ i : R, I_off2 i ω
  set S_g5 : Ω → ℝ := fun ω => ∑ j : R, I_off3 j ω
  have hi1 : Integrable S_g1 P₀ := integrable_finsetSum _ fun i _ => (hg1_v0 i).2.2
  have hi2 : Integrable S_g2 P₀ := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j hj => (hg2_v0 i j hj).2.2
  have hi3 : Integrable S_g3 P₀ := integrable_finsetSum _ fun i _ => (hg3_v0 i).2.2
  have hi4 : Integrable I_diag2 P₀ := hg4_v0.2.2
  have hi5 : Integrable S_g5 P₀ := integrable_finsetSum _ fun j _ => (hg5_v0 j).2.2
  have hi6 : Integrable I_off4 P₀ := hg6_v0.2.2
  have hD_v0_eq : D_ω v₀ = fun ω =>
      (1 / 2) * (S_g1 ω + S_g2 ω - n_R * S_g3 ω - n_R * I_diag2 ω - n_R * S_g5 ω +
        n_R * (n_R + 1) * I_off4 ω) := rfl
  rw [hD_v0_eq, integral_const_mul]
  congr 1
  have h_lin : (fun ω => S_g1 ω + S_g2 ω - n_R * S_g3 ω -
      n_R * I_diag2 ω - n_R * S_g5 ω + n_R * (n_R + 1) * I_off4 ω) =
    ((((S_g1 + S_g2) - (fun ω => n_R * S_g3 ω)) -
      (fun ω => n_R * I_diag2 ω)) -
      (fun ω => n_R * S_g5 ω)) +
      (fun ω => n_R * (n_R + 1) * I_off4 ω) := rfl
  rw [h_lin,
    integral_add'
      ((((hi1.add hi2).sub (hi3.const_mul _)).sub (hi4.const_mul _)).sub (hi5.const_mul _))
      (hi6.const_mul _),
    integral_sub' (((hi1.add hi2).sub (hi3.const_mul _)).sub (hi4.const_mul _)) (hi5.const_mul _),
    integral_sub' ((hi1.add hi2).sub (hi3.const_mul _)) (hi4.const_mul _),
    integral_sub' (hi1.add hi2) (hi3.const_mul _),
    integral_add' hi1 hi2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hs1_eq : ∫ ω, S_g1 ω ∂P₀ = ∑ i : R, ∫ ω, I_diag1 i ω ∂P₀ :=
    integral_finsetSum _ fun i _ => (hg1_v0 i).2.2
  have hs2_eq : ∫ ω, S_g2 ω ∂P₀ = ∑ i : R, ∑ j ∈ Finset.univ.erase i, ∫ ω, I_off1 i j ω ∂P₀ := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj => (hg2_v0 i j hj).2.2]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j hj => (hg2_v0 i j hj).2.2
  have hs3_eq : ∫ ω, S_g3 ω ∂P₀ = ∑ i : R, ∫ ω, I_off2 i ω ∂P₀ :=
    integral_finsetSum _ fun i _ => (hg3_v0 i).2.2
  have hs5_eq : ∫ ω, S_g5 ω ∂P₀ = ∑ j : R, ∫ ω, I_off3 j ω ∂P₀ :=
    integral_finsetSum _ fun j _ => (hg5_v0 j).2.2
  rw [hs1_eq, hs2_eq, hs3_eq, hs5_eq]

end ConfinedExtended

end MeasureTheory
