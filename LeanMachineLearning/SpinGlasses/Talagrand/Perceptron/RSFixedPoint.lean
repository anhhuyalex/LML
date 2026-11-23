/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.TrigSquareParam
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPointRS
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityEndpoint
public import
  LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityInterpolationBound
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianTiltedRotationBound

/-!
# Fixed-point analysis of the replica-symmetric system (Talagrand Section 2.4, Theorem 2.4.1)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eq. (2.68) and the
existence/uniqueness half of Theorem 2.4.1.

For a potential `u : ℝ → ℝ` satisfying (2.7) (`∀ j < 3, Differentiable ℝ (iteratedDeriv j u)` and
`∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D`), the replica-symmetric fixed-point system in unknowns
`(q, r)` is
$$q = \mathbb{E}\tanh^2(z\sqrt{r}), \qquad
  r = \alpha \widehat{r}(q) = \alpha \mathbb{E}\left(
    \frac{\mathbb{E}_\xi u'(\theta) e^{u(\theta)}}{\mathbb{E}_\xi e^{u(\theta)}}\right)^2,$$
where $\theta = \sqrt{q}\,z + \sqrt{1 - q}\,\xi$ with $z, \xi \sim \mathcal{N}(0, 1)$ independent.
When $\alpha \ge 0$, every solution $(q, r)$ of (2.68) automatically satisfies $q \in [0, 1]$ and
$r \ge 0$.

## Main declarations

* `abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo`: mean-value Lipschitz bound on `[a, b]` from
  `ContinuousOn` on `[a, b]` and bounded derivative on `(a, b)`.
* `hasDerivAt_integral_tanh_sq_sqrt_and_abs_le`: on `(0, ∞)`, `r ↦ 𝔼 tanh²(z √r)` has derivative
  `𝔼[(1 - tanh²)(1 - 3 tanh²)]` bounded in absolute value by `1`.
* `lipschitzWith_one_integral_tanh_sq_sqrt`: `r ↦ 𝔼 tanh²(z √r)` is `1`-Lipschitz on `ℝ`.
* `SpinGlasses.continuousOn_rhat`: `q ↦ r̂(q)` is continuous on `[0, 1]`.
* `SpinGlasses.exists_hasDerivAt_rhat_abs_le`: under (2.7), `r̂` is differentiable on `(0, 1)` with
  `|r̂'(q)| ≤ K(D)` uniformly in `q ∈ (0, 1)`, proved by reparameterizing `q = cos² s` and applying
  `hasDerivAt_integral_gaussian_tilted_rotation_ibp` on two replicas (`R = Fin 2`).
* `SpinGlasses.exists_lipschitzOnWith_rhat`: `q ↦ r̂(q)` is `K(D)`-Lipschitz on `[0, 1]`.
* `SpinGlasses.exists_unique_rs_fixed_point`: Theorem 2.4.1 (fixed-point part), existence and
  uniqueness of `(q, r) ∈ ℝ × ℝ` solving (2.68) (with `q ∈ [0, 1]` and `r ≥ 0` derived, not
  restricted) when `α ≥ 0` and `α * K(D) ≤ 1`, via Banach's contraction mapping theorem
  (`ContractingWith.exists_fixedPoint'`) on `[0, 1]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

/-! ### Model-free MVT Lipschitz helper and `r ↦ 𝔼 tanh²(z √r)` regularity -/

/-- If `f : ℝ → ℝ` is continuous on `[a, b]` and has derivative bounded by `C` on `(a, b)`,
then `|f y - f x| ≤ C * |y - x|` for all `x, y ∈ [a, b]`. -/
theorem abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo
    {f : ℝ → ℝ} {a b C : ℝ} (hfc : ContinuousOn f (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, ∃ d, HasDerivAt f d x ∧ |d| ≤ C)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f y - f x| ≤ C * |y - x| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm (f y) (f x), abs_sub_comm y x]
    exact this hy hx (le_of_not_ge hxy)
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hsub_oo : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
  choose! f' hf' hfb using hfd
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt (hfc.mono hsub)
    (fun t ht => hf' t (hsub_oo ht))
  have hpos : 0 < y - x := sub_pos.2 hlt
  have heq : f y - f x = f' c * (y - x) := ((eq_div_iff hpos.ne').1 hslope).symm
  rw [heq, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_right (hfb c (hsub_oo hc)) hpos.le

/-- **Uniform derivative bound on `(0, ∞)` for `r ↦ 𝔼 tanh²(z √r)`:** at `r > 0`, the derivative
equals `𝔼[(1 - tanh²(z √r))(1 - 3 tanh²(z √r))]`, whose absolute value is at most `1`. -/
theorem hasDerivAt_integral_tanh_sq_sqrt_and_abs_le {r : ℝ} (hr : 0 < r) :
    let d := ∫ z : ℝ, (1 - Real.tanh (z * Real.sqrt r) ^ 2) *
      (1 - 3 * Real.tanh (z * Real.sqrt r) ^ 2) ∂gaussianReal 0 1
    HasDerivAt (fun x : ℝ => ∫ z : ℝ, Real.tanh (z * Real.sqrt x) ^ 2 ∂gaussianReal 0 1) d r ∧
      |d| ≤ 1 := by
  intro d
  have hfun : (fun x : ℝ => ∫ z : ℝ, Real.tanh (z * Real.sqrt x) ^ 2 ∂gaussianReal 0 1) =
      fun x : ℝ => ∫ z : ℝ, Real.tanh (1 * Real.sqrt x * z + 0) ^ 2 ∂gaussianReal 0 1 := by
    funext x; congr 1; ext z; ring_nf
  have hd0 := SpinGlasses.hasDerivAt_fixedPointMap_sqrt 1 0 hr
  have hd_eq : (1 : ℝ) ^ 2 * ∫ z : ℝ, (1 - Real.tanh (1 * Real.sqrt r * z + 0) ^ 2) *
      (1 - 3 * Real.tanh (1 * Real.sqrt r * z + 0) ^ 2) ∂gaussianReal 0 1 = d := by
    rw [one_pow, one_mul]
    exact integral_congr_ae (ae_of_all _ fun z => by ring_nf)
  rw [hd_eq, ← hfun] at hd0
  refine ⟨hd0, ?_⟩
  have hb := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1) (C := 2)
    (f := fun z : ℝ => 2 * (1 - Real.tanh (z * Real.sqrt r) ^ 2) *
      (1 - 3 * Real.tanh (z * Real.sqrt r) ^ 2))
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact Real.abs_tanh_sq_second_deriv_le _)
  have h2d : ∫ z : ℝ, 2 * (1 - Real.tanh (z * Real.sqrt r) ^ 2) *
      (1 - 3 * Real.tanh (z * Real.sqrt r) ^ 2) ∂gaussianReal 0 1 = 2 * d := by
    dsimp only [d]
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [h2d, probReal_univ, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (zero_lt_two' ℝ)] at hb
  linarith

/-- **`r ↦ 𝔼 tanh²(z √r)` is `1`-Lipschitz on `ℝ`** (for `r ≤ 0`, `√r = 0` makes it `0`, and on
`[0, ∞)` its interior derivative is bounded in absolute value by `1`). -/
theorem lipschitzWith_one_integral_tanh_sq_sqrt :
    LipschitzWith 1 (fun x : ℝ => ∫ z : ℝ, Real.tanh (z * Real.sqrt x) ^ 2 ∂gaussianReal 0 1) := by
  let g : ℝ → ℝ := fun x => ∫ z : ℝ, Real.tanh (z * Real.sqrt x) ^ 2 ∂gaussianReal 0 1
  have hg_eq : g =
      fun x : ℝ => ∫ z : ℝ, Real.tanh (1 * Real.sqrt x * z + 0) ^ 2 ∂gaussianReal 0 1 := by
    funext x; dsimp only [g]; congr 1; ext z; ring_nf
  have hgc : Continuous g := hg_eq ▸ SpinGlasses.continuous_fixedPointMap 1 0
  have hg_nonpos {x : ℝ} (hx : x ≤ 0) : g x = 0 := by
    dsimp only [g]
    simp [Real.sqrt_eq_zero_of_nonpos hx]
  have hIci {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : |g x - g y| ≤ |x - y| := by
    let R : ℝ := max x y + 1
    have hxR : x ∈ Icc 0 R := ⟨hx, by linarith [le_max_left x y]⟩
    have hyR : y ∈ Icc 0 R := ⟨hy, by linarith [le_max_right x y]⟩
    have h := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hgc.continuousOn
      (fun t ht => ⟨_, hasDerivAt_integral_tanh_sq_sqrt_and_abs_le ht.1⟩) hyR hxR
    simpa only [one_mul] using h
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  change dist (g x) (g y) ≤ (1 : ℝ≥0) * dist x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · exact hIci hx hy
  · rw [hg_nonpos hy, ← hg_nonpos (le_refl 0)]
    refine (hIci hx le_rfl).trans ?_
    rw [sub_zero, abs_of_nonneg hx, abs_of_nonneg (by linarith)]
    linarith
  · rw [hg_nonpos hx, ← hg_nonpos (le_refl 0), abs_sub_comm]
    refine (hIci hy le_rfl).trans ?_
    rw [sub_zero, abs_of_nonneg hy, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · rw [hg_nonpos hx, hg_nonpos hy, sub_self, abs_zero]
    exact abs_nonneg _

namespace SpinGlasses

/-- **Continuity of `q ↦ r̂(q)` on `[0, 1]`** when `u` is `C¹` with bounded `|u|` and `|u'|`. -/
theorem continuousOn_rhat {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hdu : Continuous (deriv u))
    {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁) :
    ContinuousOn (perceptronRhat u) (Icc 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  have hum : Measurable u := hu.continuous.measurable
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let N_fn (q z : ℝ) : ℝ :=
    ∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) *
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ
  let Z_fn (q z : ℝ) : ℝ :=
    ∫ ξ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ
  have hZ_pos (q z : ℝ) : 0 < Z_fn q z :=
    integral_exp_pos (integrable_exp_cavityPath_new hum hB_le q z)
  have hN_cont (z : ℝ) : Continuous fun q => N_fn q z := by
    refine continuous_of_dominated (bound := fun _ => |D₁| * Real.exp B)
      (fun q => ?_) (fun q => ae_of_all _ fun ξ => ?_) (integrable_const _)
      (ae_of_all _ fun ξ => ?_)
    · exact ((hdu.comp (by fun_prop)).mul
        (Real.continuous_exp.comp
          (hu.continuous.comp (by fun_prop)))).measurable.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul ((hD₁ _).trans (le_abs_self _)) (Real.exp_le_exp.2 (hB_le _))
        (Real.exp_pos _).le (abs_nonneg _)
    · exact (hdu.comp (by fun_prop)).mul
        (Real.continuous_exp.comp (hu.continuous.comp (by fun_prop)))
  have hZ_cont (z : ℝ) : Continuous fun q => Z_fn q z := by
    refine continuous_of_dominated (bound := fun _ => Real.exp B)
      (fun q => ?_) (fun q => ae_of_all _ fun ξ => ?_) (integrable_const _)
      (ae_of_all _ fun ξ => ?_)
    · exact (Real.continuous_exp.comp
        (hu.continuous.comp (by fun_prop))).measurable.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.2 (hB_le _)
    · exact Real.continuous_exp.comp (hu.continuous.comp (by fun_prop))
  let ρ (q z : ℝ) : ℝ := (N_fn q z / Z_fn q z) ^ 2
  have hρ_cont (z : ℝ) : Continuous fun q => ρ q z :=
    ((hN_cont z).div (hZ_cont z) fun q => (hZ_pos q z).ne').pow 2
  have hρ_meas (q : ℝ) : AEStronglyMeasurable (ρ q) γ := by
    have hNm : Measurable fun z => N_fn q z := by
      have hj : Measurable fun p : ℝ × ℝ =>
          deriv u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2) *
            Real.exp (u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2)) :=
        (hdu.measurable.comp (by fun_prop)).mul (Real.measurable_exp.comp (hum.comp (by fun_prop)))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
    have hZm : Measurable fun z => Z_fn q z := by
      have hj : Measurable fun p : ℝ × ℝ =>
          Real.exp (u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2)) :=
        Real.measurable_exp.comp (hum.comp (by fun_prop))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
    exact ((hNm.div hZm).pow_const 2).aestronglyMeasurable
  have hρ_bd (q z : ℝ) : ‖ρ q z‖ ≤ |D₁| ^ 2 := by
    have hprob := isProbabilityMeasure_tilted (integrable_exp_cavityPath_new hum hB_le q z)
    have h := abs_integral_le_of_forall_abs_le
      (γ.tilted fun ξ : ℝ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))
      (f := fun ξ => deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) (M := |D₁|)
      fun ξ => (hD₁ _).trans (le_abs_self _)
    rw [integral_tilted_eq_div] at h
    dsimp only [ρ, N_fn, Z_fn]
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  exact (continuous_of_dominated (bound := fun _ => |D₁| ^ 2) hρ_meas
    (fun q => ae_of_all _ (hρ_bd q)) (integrable_const _) (ae_of_all _ hρ_cont)).continuousOn

/-- **Angle parametrization of `r̂(cos² s)`:** for `s ∈ [0, π / 2]`, `r̂(cos² s)` equals the
two-replica tilted rotation integral with trivial old state `Unit`, `X_sh = 1`, `Y_aux = 1`, and
`ψ r = deriv u`. -/
private lemma rhat_cos_sq_eq_rotation_integral {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ Real.pi / 2) :
    let γ_sh := Measure.pi fun _ : Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let μ₀ : Measure Unit := Measure.dirac ()
    let S (s' : ℝ) (w : Unit → ℝ) (q : Unit × (Unit → ℝ)) : ℝ :=
      Real.cos s' * ((fun _ : Unit => (1 : ℝ)) ⬝ᵥ w + (0 : Unit → ℝ) ⬝ᵥ q.2) +
        Real.sin s' * ((0 : Unit → ℝ) ⬝ᵥ w + (fun _ : Unit => (1 : ℝ)) ⬝ᵥ q.2)
    perceptronRhat u (Real.cos s ^ 2) =
      ∫ w, ∫ σ : Fin 2 → Unit × (Unit → ℝ),
        (1 : ℝ) * ∏ r : Fin 2, deriv u (S s w (σ r))
        ∂(Measure.pi fun _ : Fin 2 => (μ₀.prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh := by
  intro γ_sh γ_aux μ₀ S
  have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hs1⟩
  have hsin : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 (hs1.trans (by linarith [Real.pi_pos]))
  have hsc1 : Real.sqrt (Real.cos s ^ 2) = Real.cos s := Real.sqrt_sq hcos
  have hsc2 : Real.sqrt (1 - Real.cos s ^ 2) = Real.sin s := by
    rw [← Real.sin_sq s, Real.sqrt_sq hsin]
  rw [perceptronRhat, hsc1, hsc2]
  let e_u : (Unit → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique Unit ℝ
  have hmp_u : MeasurePreserving ⇑e_u γ_sh (gaussianReal 0 1) :=
    measurePreserving_funUnique (gaussianReal 0 1) Unit
  have hS_simp (w : Unit → ℝ) (q : Unit × (Unit → ℝ)) :
      S s w q = Real.cos s * w () + Real.sin s * q.2 () := by
    simp [S, dotProduct]
  let g_z (z : ℝ) : ℝ :=
    ((∫ ξ, deriv u (Real.cos s * z + Real.sin s * ξ) *
        Real.exp (u (Real.cos s * z + Real.sin s * ξ)) ∂gaussianReal 0 1) /
      ∫ ξ, Real.exp (u (Real.cos s * z + Real.sin s * ξ)) ∂gaussianReal 0 1) ^ 2
  have hinner (w : Unit → ℝ) :
      ∫ σ : Fin 2 → Unit × (Unit → ℝ),
        (1 : ℝ) * ∏ r : Fin 2, deriv u (S s w (σ r))
        ∂(Measure.pi fun _ : Fin 2 => (μ₀.prod γ_aux).tilted (fun q => u (S s w q))) =
      g_z (w ()) := by
    have hexp_w : Integrable (fun q : Unit × (Unit → ℝ) => Real.exp (u (S s w q)))
        (μ₀.prod γ_aux) := by
      have hm : Measurable fun q : Unit × (Unit → ℝ) => u (S s w q) := by
        simp_rw [hS_simp]; exact hu.comp (by fun_prop)
      exact integrable_exp_of_ae_le hm.aemeasurable (ae_of_all _ fun _ => hB _)
    have hprob_w : IsProbabilityMeasure ((μ₀.prod γ_aux).tilted (fun q => u (S s w q))) :=
      isProbabilityMeasure_tilted hexp_w
    have hprod2 : ∀ σ : Fin 2 → Unit × (Unit → ℝ),
        (1 : ℝ) * ∏ r : Fin 2, deriv u (S s w (σ r)) =
          deriv u (S s w (σ 0)) * deriv u (S s w (σ 1)) := fun σ => by
      rw [one_mul, Fin.prod_univ_two]
    simp_rw [hprod2]
    have hdu_m : Measurable fun q : Unit × (Unit → ℝ) => deriv u (S s w q) := by
      simp_rw [hS_simp]; exact (measurable_deriv u).comp (by fun_prop)
    rw [integral_pi_mul_of_ne _ (by decide : (0 : Fin 2) ≠ 1) hdu_m hdu_m,
      ← sq, integral_tilted_eq_div]
    dsimp only [g_z]
    congr 1
    have hmp_q : MeasurePreserving (fun q : Unit × (Unit → ℝ) => q.2 ())
        (μ₀.prod γ_aux) (gaussianReal 0 1) :=
      hmp_u.comp measurePreserving_snd
    have hnum_eq : ∫ q : Unit × (Unit → ℝ), deriv u (S s w q) * Real.exp (u (S s w q))
        ∂(μ₀.prod γ_aux) =
      ∫ ξ, deriv u (Real.cos s * w () + Real.sin s * ξ) *
        Real.exp (u (Real.cos s * w () + Real.sin s * ξ)) ∂gaussianReal 0 1 := by
      simp_rw [hS_simp]
      have hm : Measurable fun ξ : ℝ =>
          deriv u (Real.cos s * w () + Real.sin s * ξ) *
            Real.exp (u (Real.cos s * w () + Real.sin s * ξ)) :=
        ((measurable_deriv u).comp (by fun_prop)).mul
          (Real.measurable_exp.comp (hu.comp (by fun_prop)))
      exact hmp_q.integral_comp_of_aestronglyMeasurable hm.aestronglyMeasurable
    have hden_eq : ∫ q : Unit × (Unit → ℝ), Real.exp (u (S s w q)) ∂(μ₀.prod γ_aux) =
      ∫ ξ, Real.exp (u (Real.cos s * w () + Real.sin s * ξ)) ∂gaussianReal 0 1 := by
      simp_rw [hS_simp]
      have hm : Measurable fun ξ : ℝ => Real.exp (u (Real.cos s * w () + Real.sin s * ξ)) :=
        Real.measurable_exp.comp (hu.comp (by fun_prop))
      exact hmp_q.integral_comp_of_aestronglyMeasurable hm.aestronglyMeasurable
    rw [hnum_eq, hden_eq]
  simp_rw [hinner]
  have hgm : Measurable g_z := by
    have hNm : Measurable fun z => ∫ ξ, deriv u (Real.cos s * z + Real.sin s * ξ) *
        Real.exp (u (Real.cos s * z + Real.sin s * ξ)) ∂gaussianReal 0 1 := by
      have hj : Measurable fun p : ℝ × ℝ =>
          deriv u (Real.cos s * p.1 + Real.sin s * p.2) *
            Real.exp (u (Real.cos s * p.1 + Real.sin s * p.2)) :=
        ((measurable_deriv u).comp (by fun_prop)).mul
          (Real.measurable_exp.comp (hu.comp (by fun_prop)))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    have hZm : Measurable fun z =>
        ∫ ξ, Real.exp (u (Real.cos s * z + Real.sin s * ξ)) ∂gaussianReal 0 1 := by
      have hj : Measurable fun p : ℝ × ℝ =>
          Real.exp (u (Real.cos s * p.1 + Real.sin s * p.2)) :=
        Real.measurable_exp.comp (hu.comp (by fun_prop))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    exact (hNm.div hZm).pow_const 2
  exact (hmp_u.integral_comp_of_aestronglyMeasurable hgm.aestronglyMeasurable).symm

/-- **Uniform interior derivative bound on `q ↦ r̂(q)` under (2.7).**
There exists a constant `K(D) ≥ 0` depending only on `D` (`K = 9 (1 + |D| + |D|²)⁴`) such that for
any `u` satisfying (2.7) and every `q ∈ (0, 1)`, `r̂` is differentiable at `q` with
`|r̂'(q)| ≤ K`. -/
theorem exists_hasDerivAt_rhat_abs_le (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {q : ℝ} (_hq : q ∈ Ioo (0 : ℝ) 1),
        ∃ d,
          HasDerivAt
            (fun q' => perceptronRhat u q')
            d q ∧
          |d| ≤ K := by
  let L_w : ℝ := 1 + |D| + |D| ^ 2
  refine ⟨9 * L_w ^ 4, by positivity, ?_⟩
  intro u hd hb q hq
  obtain ⟨hu, hu2, hb3⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hB : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := fun x => (hu.abs_deriv_le x).trans (le_abs_self D)
  have hD₂ : ∀ x, |deriv (deriv u) x| ≤ |D| := fun x => (hu.abs_deriv₂_le x).trans (le_abs_self D)
  have hD₃ : ∀ x, |deriv (deriv (deriv u)) x| ≤ |D| := fun x => (hb3 x).trans (le_abs_self D)
  let γ_sh := Measure.pi fun _ : Unit => gaussianReal 0 1
  let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
  let μ₀ : Measure Unit := Measure.dirac ()
  let X_sh : Unit → Unit → ℝ := fun _ _ => 1
  let Y_sh : Unit → Unit → ℝ := fun _ _ => 0
  let X_aux : Unit → Unit → ℝ := fun _ _ => 0
  let Y_aux : Unit → Unit → ℝ := fun _ _ => 1
  let S (s : ℝ) (w : Unit → ℝ) (x : Unit × (Unit → ℝ)) : ℝ :=
    Real.cos s * (X_sh x.1 ⬝ᵥ w + X_aux x.1 ⬝ᵥ x.2) +
      Real.sin s * (Y_sh x.1 ⬝ᵥ w + Y_aux x.1 ⬝ᵥ x.2)
  let φ (s : ℝ) : ℝ :=
    ∫ w, ∫ σ : Fin 2 → Unit × (Unit → ℝ),
      (1 : ℝ) * ∏ r : Fin 2, deriv u (S s w (σ r))
      ∂(Measure.pi fun _ : Fin 2 => (μ₀.prod γ_aux).tilted (fun x => u (S s w x))) ∂γ_sh
  let s₀ : ℝ := Real.arccos (Real.sqrt q)
  have hrot := hasDerivAt_integral_gaussian_tilted_rotation_ibp (R := Fin 2)
    μ₀ id measurable_id X_sh Y_sh X_aux Y_aux
    (fun _ _ => by simp [X_sh, Y_sh, dotProduct])
    (fun _ _ => by simp [X_aux, Y_aux, dotProduct])
    (fun _ => by simp [X_sh, Y_sh, X_aux, Y_aux, dotProduct])
    hu.differentiable hu.differentiable_deriv hB hD₁ hD₂
    (fun _ => deriv u) (fun _ => hu.differentiable_deriv) (fun _ => hu2)
    (fun _ => hD₁) (fun _ => hD₂) (fun _ => hD₃)
    (f := fun _ => 1) (integrable_const 1) s₀
  dsimp only at hrot
  let C_cov (m m' : Unit) : ℝ := Y_sh m ⬝ᵥ Y_sh m' - X_sh m ⬝ᵥ X_sh m'
  have hC_abs (m m' : Unit) : |C_cov m m'| ≤ 1 := by
    simp [C_cov, X_sh, Y_sh, dotProduct]
  have hLw1 : 1 ≤ L_w := by
    dsimp only [L_w]
    linarith [abs_nonneg D, sq_nonneg |D|]
  have hLw0 : 0 ≤ L_w := zero_le_one.trans hLw1
  have hLw2_le_4 : L_w ^ 2 ≤ L_w ^ 4 := pow_le_pow_right₀ hLw1 (by omega)
  have hLw3_le_4 : L_w ^ 3 ≤ L_w ^ 4 := pow_le_pow_right₀ hLw1 (by omega)
  have hD_Lw (x : ℝ) : |deriv u x| ≤ L_w :=
    (hD₁ x).trans (by dsimp only [L_w]; linarith [sq_nonneg |D|])
  let ψ_d (x : ℝ) : ℝ := deriv (deriv u) x + deriv u x * deriv u x
  have hψd_le (x : ℝ) : |ψ_d x| ≤ L_w := by
    dsimp only [ψ_d, L_w]
    have h1 := hD₂ x
    have h2 : |deriv u x * deriv u x| ≤ |D| ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul (hD₁ x) (hD₁ x) (abs_nonneg _) (abs_nonneg _)
    linarith [abs_add_le (deriv (deriv u) x) (deriv u x * deriv u x)]
  have hSw_m (w : Unit → ℝ) : Measurable fun x : Unit × (Unit → ℝ) => u (S s₀ w x) :=
    hu.measurable.comp (measurable_rotation_field measurable_id X_sh Y_sh X_aux Y_aux s₀ w)
  have hprob_w (w : Unit → ℝ) :
      IsProbabilityMeasure ((μ₀.prod γ_aux).tilted (fun x => u (S s₀ w x))) :=
    isProbabilityMeasure_tilted_of_ae_le (hSw_m w).aemeasurable
      (ae_of_all _ fun _ => le_of_abs_le (hB _))
  obtain ⟨z, hrot', hz_eq⟩ : ∃ z, HasDerivAt φ (Real.sin s₀ * Real.cos s₀ * z) s₀ ∧
      |z| ≤ 18 * L_w ^ 4 := by
    refine ⟨_, hrot, ?_⟩
    have ht1 : ∀ i : Fin 2, ∀ j ∈ Finset.univ.erase i,
        |∫ w, ∫ σ : Fin 2 → Unit × (Unit → ℝ),
          (1 : ℝ) * C_cov (σ i).1 (σ j).1 *
            (ψ_d (S s₀ w (σ i)) * ψ_d (S s₀ w (σ j)) *
              ∏ r ∈ (Finset.univ.erase i).erase j, deriv u (S s₀ w (σ r)))
          ∂(Measure.pi fun _ : Fin 2 =>
            (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh| ≤ L_w ^ 4 := by
      intro i j hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      have her : (Finset.univ.erase i).erase j = ∅ := by
        ext r; fin_cases i <;> fin_cases j <;> fin_cases r <;> simp_all
      refine abs_integral_le_of_forall_abs_le γ_sh fun w =>
        abs_integral_le_of_forall_abs_le _ fun σ => ?_
      rw [her, Finset.prod_empty, mul_one, one_mul, abs_mul, abs_mul]
      calc |C_cov (σ i).1 (σ j).1| * (|ψ_d (S s₀ w (σ i))| * |ψ_d (S s₀ w (σ j))|)
          ≤ 1 * (L_w * L_w) := mul_le_mul (hC_abs (σ i).1 (σ j).1)
            (mul_le_mul (hψd_le _) (hψd_le _) (abs_nonneg _) hLw0) (by positivity) zero_le_one
        _ = L_w ^ 2 := by ring
        _ ≤ L_w ^ 4 := hLw2_le_4
    have ht2 : ∀ (c_fn : Unit → Unit → ℝ), (∀ m m', |c_fn m m'| ≤ 1) → ∀ i : Fin 2,
        |∫ w, ∫ σ : Option (Fin 2) → Unit × (Unit → ℝ),
          (1 : ℝ) * c_fn (σ (some i)).1 (σ none).1 *
            (ψ_d (S s₀ w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, deriv u (S s₀ w (σ (some r)))) *
            deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option (Fin 2) =>
            (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh| ≤ L_w ^ 4 := by
      intro c_fn hc_fn i
      refine abs_integral_le_of_forall_abs_le γ_sh fun w =>
        abs_integral_le_of_forall_abs_le _ fun σ => ?_
      have hprod1 : |∏ r ∈ Finset.univ.erase i, deriv u (S s₀ w (σ (some r)))| ≤ L_w := by
        rw [Finset.abs_prod]
        calc ∏ r ∈ Finset.univ.erase i, |deriv u (S s₀ w (σ (some r)))|
            ≤ ∏ _r ∈ Finset.univ.erase i, L_w :=
              Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun _ _ => hD_Lw _
          _ = L_w := by simp
      rw [one_mul, abs_mul, abs_mul, abs_mul]
      calc |c_fn (σ (some i)).1 (σ none).1| *
            (|ψ_d (S s₀ w (σ (some i)))| *
              |∏ r ∈ Finset.univ.erase i, deriv u (S s₀ w (σ (some r)))|) *
            |deriv u (S s₀ w (σ none))|
          ≤ 1 * (L_w * L_w) * L_w :=
            mul_le_mul (mul_le_mul (hc_fn (σ (some i)).1 (σ none).1)
              (mul_le_mul (hψd_le _) hprod1 (abs_nonneg _) hLw0) (by positivity) zero_le_one)
              (hD_Lw _) (abs_nonneg _) (by positivity)
        _ = L_w ^ 3 := by ring
        _ ≤ L_w ^ 4 := hLw3_le_4
    have ht4 :
        |∫ w, ∫ σ : Option (Option (Fin 2)) → Unit × (Unit → ℝ),
          (1 : ℝ) * C_cov (σ (some none)).1 (σ none).1 *
            (∏ r : Fin 2, deriv u (S s₀ w (σ (some (some r))))) *
            deriv u (S s₀ w (σ (some none))) * deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) =>
            (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh| ≤ L_w ^ 4 := by
      refine abs_integral_le_of_forall_abs_le γ_sh fun w =>
        abs_integral_le_of_forall_abs_le _ fun σ => ?_
      rw [one_mul, Fin.prod_univ_two, abs_mul, abs_mul, abs_mul, abs_mul]
      have h12 : |deriv u (S s₀ w (σ (some (some 0))))| *
          |deriv u (S s₀ w (σ (some (some 1))))| ≤ L_w ^ 2 := by
        rw [sq]; exact mul_le_mul (hD_Lw _) (hD_Lw _) (abs_nonneg _) hLw0
      have h123 : |C_cov (σ (some none)).1 (σ none).1| *
          (|deriv u (S s₀ w (σ (some (some 0))))| *
            |deriv u (S s₀ w (σ (some (some 1))))|) ≤ L_w ^ 2 :=
        (mul_le_mul (hC_abs (σ (some none)).1 (σ none).1) h12
          (by positivity) zero_le_one).trans_eq (one_mul _)
      have h1234 : |C_cov (σ (some none)).1 (σ none).1| *
          (|deriv u (S s₀ w (σ (some (some 0))))| *
            |deriv u (S s₀ w (σ (some (some 1))))|) *
          |deriv u (S s₀ w (σ (some none)))| ≤ L_w ^ 3 := by
        calc _ ≤ L_w ^ 2 * L_w := mul_le_mul h123 (hD_Lw _) (abs_nonneg _) (by positivity)
          _ = L_w ^ 3 := by ring
      calc _ ≤ L_w ^ 3 * L_w := mul_le_mul h1234 (hD_Lw _) (abs_nonneg _) (by positivity)
        _ = L_w ^ 4 := by ring
    have hgrp := Finset.abs_replica_groups_le (R := Fin 2) _ _ _ _ (pow_nonneg hLw0 4)
      (fun i j hij => ht1 i j (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ _⟩))
      (ht2 C_cov hC_abs) (ht2 (fun m m' => C_cov m' m) (fun m m' => hC_abs m' m)) ht4
    simp only [Fintype.card_fin, Nat.cast_ofNat] at hgrp
    exact hgrp.trans_eq (by ring)
  have hcomp := HasDerivAt.comp_arccos_sqrt_of_sin_cos hq.1 hq.2 hrot'
  have hcongr : (fun u' => φ (Real.arccos (Real.sqrt u'))) =ᶠ[𝓝 q]
      fun q' => perceptronRhat u q' := by
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with q' hq'
    dsimp only [φ]
    let s' := Real.arccos (Real.sqrt q')
    have hs'0 : 0 ≤ s' := Real.arccos_nonneg _
    have hs'1 : s' ≤ Real.pi / 2 :=
      Real.arccos_le_pi_div_two.2 (Real.sqrt_nonneg _)
    have hcos_sq : Real.cos s' ^ 2 = q' := by
      have hle1 : Real.sqrt q' ≤ 1 := (Real.sqrt_le_one).2 hq'.2.le
      rw [Real.cos_arccos (by linarith [Real.sqrt_nonneg q']) hle1, Real.sq_sqrt hq'.1.le]
    have heq_rot := rhat_cos_sq_eq_rotation_integral hu.measurable (fun x => hu.le x) hs'0 hs'1
    dsimp only at heq_rot
    rw [hcos_sq] at heq_rot
    exact heq_rot.symm
  refine ⟨-z / 2, hcomp.congr_of_eventuallyEq hcongr.symm, ?_⟩
  rw [abs_div, abs_neg, abs_two]
  linarith

/-- **`q ↦ r̂(q)` is `K(D)`-Lipschitz on `[0, 1]` under (2.7).** -/
theorem exists_lipschitzOnWith_rhat (D : ℝ) :
    ∃ K : ℝ≥0,
      ∀ {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D),
        LipschitzOnWith K (perceptronRhat u) (Icc 0 1) := by
  obtain ⟨K, hK0, hK⟩ := exists_hasDerivAt_rhat_abs_le D
  refine ⟨K.toNNReal, ?_⟩
  intro u hd hb
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hc : ContinuousOn (perceptronRhat u) (Icc 0 1) :=
    continuousOn_rhat hu.differentiable hu.differentiable_deriv.continuous hu.abs_le hu.abs_deriv_le
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.coe_toNNReal K hK0, Real.dist_eq, Real.dist_eq]
  exact abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hc
    (fun q hq => hK hd hb hq) hy hx

/-- **Theorem 2.4.1 (fixed-point part): existence and uniqueness of the replica-symmetric solution
of (2.68).**
Given `D ∈ ℝ`, there exists `K(D) ≥ 0` (chosen before `u` and `α`) such that whenever `u` satisfies
(2.7) and `0 ≤ α` with `α * K(D) ≤ 1`, the system (2.68)
`q = 𝔼 tanh²(z √r)`, `r = α * r̂(q)` has a unique solution `(q, r) ∈ ℝ × ℝ` (with no domain
restriction needed in uniqueness, because `q ∈ [0, 1]` and `r ≥ 0` follow automatically from (2.68)
when `α ≥ 0`). -/
theorem exists_unique_rs_fixed_point (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {α : ℝ} (_hα0 : 0 ≤ α) (_hα : α * K ≤ 1),
        ∃! p : ℝ × ℝ,
          p.1 = (∫ z : ℝ, Real.tanh (z * Real.sqrt p.2) ^ 2 ∂gaussianReal 0 1) ∧
          p.2 = α * perceptronRhat u p.1 := by
  obtain ⟨K_lip, hlip_rhat⟩ := exists_lipschitzOnWith_rhat D
  let K : ℝ := 2 * (K_lip : ℝ)
  refine ⟨K, by positivity, ?_⟩
  intro u hd hb α hα0 hα
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let rhat := perceptronRhat u
  let g_tanh (r : ℝ) : ℝ := ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1
  let ψ (q : ℝ) : ℝ := g_tanh (α * rhat q)
  have hg_mem (r : ℝ) : g_tanh r ∈ Icc (0 : ℝ) 1 := by
    dsimp only [g_tanh]
    have heq : (∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1) =
        ∫ z : ℝ, Real.tanh (1 * Real.sqrt r * z + 0) ^ 2 ∂gaussianReal 0 1 := by
      congr 1; ext z; ring_nf
    rw [heq]
    exact fixedPointMap_mem_Icc 1 0 r
  have hmaps : MapsTo ψ (Icc 0 1) (Icc 0 1) := fun q _ => hg_mem (α * rhat q)
  have hlip_ψ : LipschitzOnWith (1 / 2 : ℝ≥0) ψ (Icc 0 1) := by
    have hlip_g := lipschitzWith_one_integral_tanh_sq_sqrt
    have hlip_r := hlip_rhat hd hb
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h1 : dist (ψ x) (ψ y) ≤ (1 : ℝ≥0) * dist (α * rhat x) (α * rhat y) :=
      hlip_g.dist_le_mul _ _
    have h2 : dist (α * rhat x) (α * rhat y) = |α| * dist (rhat x) (rhat y) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul]
    have h3 : dist (rhat x) (rhat y) ≤ (K_lip : ℝ) * dist x y :=
      hlip_r.dist_le_mul x hx y hy
    have hαK : α * (K_lip : ℝ) ≤ 1 / 2 := by
      dsimp only [K] at hα; linarith
    rw [NNReal.coe_one, one_mul, h2, abs_of_nonneg hα0] at h1
    calc dist (ψ x) (ψ y) ≤ α * ((K_lip : ℝ) * dist x y) :=
          h1.trans (mul_le_mul_of_nonneg_left h3 hα0)
      _ = (α * (K_lip : ℝ)) * dist x y := by ring
      _ ≤ (1 / 2 : ℝ) * dist x y :=
          mul_le_mul_of_nonneg_right hαK dist_nonneg
      _ = ((1 / 2 : ℝ≥0) : ℝ) * dist x y := by norm_num
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict ψ (Icc 0 1) (Icc 0 1)) :=
    ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => hlip_ψ.dist_le_mul x x.2 y y.2⟩
  have hcomp_Icc : IsComplete (Icc (0 : ℝ) 1) := isClosed_Icc.isComplete
  have h0_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨q₀, hq₀_mem, hq₀_fix, -, -⟩ :=
    hcontr.exists_fixedPoint' hcomp_Icc hmaps h0_mem (edist_ne_top 0 (ψ 0))
  refine ⟨(q₀, α * rhat q₀), ⟨hq₀_fix.symm, rfl⟩, ?_⟩
  rintro ⟨q₁, r₁⟩ ⟨hq₁_eq, hr₁_eq⟩
  dsimp only at hq₁_eq hr₁_eq
  have hq₁_mem : q₁ ∈ Icc (0 : ℝ) 1 := by rw [hq₁_eq]; exact hg_mem r₁
  have hq₁_fix : ψ q₁ = q₁ := by
    dsimp only [ψ, g_tanh]
    rw [← hr₁_eq, ← hq₁_eq]
  have hq_subtype : (⟨q₁, hq₁_mem⟩ : Icc (0 : ℝ) 1) = ⟨q₀, hq₀_mem⟩ :=
    hcontr.fixedPoint_unique' (Subtype.ext hq₁_fix) (Subtype.ext hq₀_fix)
  have hq_eq : q₁ = q₀ := congrArg Subtype.val hq_subtype
  subst hq_eq
  exact Prod.ext rfl hr₁_eq

end SpinGlasses
