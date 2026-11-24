/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ReplicaSymmetricFreeEnergy
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.FixedPointDeriv
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IntervalDerivative

/-!
# Variational stationary structure and envelope formula (Talagrand Section 2.4)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.87)--(2.89)
and Lemma 2.4.4.

Consider `perceptronRSFunctional u α r q`:
$$F(\alpha, r, q) = -\frac{1}{2}\,r(1 - q) + \mathbb{E}\log\bigl(2\cosh(z\sqrt{r})\bigr) +
  \alpha\,\mathbb{E}\log\mathbb{E}_\xi \exp u\bigl(\sqrt{q}\,z + \sqrt{1 - q}\,\xi\bigr)$$
as a function of three unrelated real variables `α`, `r`, `q`.

## Main declarations

* `SpinGlasses.integral_log_two_cosh_sqrt_eq`: `𝔼 log(2 cosh(z √r)) = log 2 + 𝔼 log cosh(z √r)`.
* `SpinGlasses.hasDerivAt_integral_log_two_cosh_sqrt`: for `r > 0`,
  `(d/dr) 𝔼 log(2 cosh(z √r)) = (1 / 2)(1 - 𝔼 tanh²(z √r))`.
* `SpinGlasses.hasDerivAt_perceptronRSFunctional_r`: for `r > 0`,
  `∂F / ∂r = (1 / 2)(q - 𝔼 tanh²(z √r))`.
* `SpinGlasses.hasDerivAt_integral_log_integral_exp_q`: for `q ∈ (0, 1)`, under `C²` boundedness of
  `u`, `(d/dq) 𝔼 log 𝔼_ξ exp u(√q z + √(1 - q) ξ) = -(1 / 2) r̂(q)`.
* `SpinGlasses.abs_integral_log_integral_exp_sub_le`: `q ↦ 𝔼 log 𝔼_ξ exp u(θ(q))` is
  `((1 / 2) * D₁²)`-Lipschitz on `[0, 1]` under `SmartPathPotential₂`.
* `SpinGlasses.hasDerivAt_perceptronRSFunctional_q`: for `q ∈ (0, 1)`, under `C²` boundedness of
  `u`, `∂F / ∂q = (1 / 2)(r - α r̂(q))` via Gaussian integration by parts.
* `SpinGlasses.deriv_perceptronRSFunctional_eq_zero_iff`: Lemma 2.4.4, characterizing the critical
  conditions `∂F / ∂r = 0` (`r > 0`) and `∂F / ∂q = 0` (`q ∈ (0, 1)`) as the replica-symmetric
  fixed-point equations (2.87).
* `SpinGlasses.hasDerivAt_perceptronRSFunctional_alpha`: conditional helper for Eq. (2.89) along
  any differentiable critical curve `a ↦ (q a, r a)` with `r α > 0` and `q α ∈ (0, 1)`.
* `SpinGlasses.exists_hasDerivAt_perceptronRSFunctional_small_load`: Eq. (2.89) for the unique
  small-load solution under (2.7) at positive load `α > 0` with `α * K(D) < 1`, handling both the
  affine zero branch `r̂(0) = 0` and the differentiable interior branch `r̂(0) > 0`.
* `SpinGlasses.hasDerivWithinAt_perceptronRSFunctional_zero`: Eq. (2.89) right derivative at zero
  load `α = 0` within `[0, ∞)` for a first-order bounded potential.
* `SpinGlasses.exists_branch_hasDerivAt_perceptronRSFunctional`: Eq. (2.89) for the constructed
  unique solution branch of Theorem 2.4.1.
* `SpinGlasses.exists_branch_taylor_perceptronRSFunctional_le`: Lipschitz bound `D⁴` on `F'(α)` and
  second-order Taylor remainder `|F(b) - F(a) - (b - a) F'(a)| ≤ (D⁴ / 2)(b - a)²` along the
  unique solution branch on `[0, 1 / K(D)]` (the `F''` step of Talagrand's second proof).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

section VariationalCalculus

/-- Splitting `𝔼 log(2 cosh(z √r))` into `log 2 + 𝔼 log cosh(z √r)`. -/
theorem integral_log_two_cosh_sqrt_eq (r : ℝ) :
    ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1 =
      Real.log 2 + ∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1 := by
  have hpt (z : ℝ) :
      Real.log (2 * Real.cosh (z * Real.sqrt r)) =
        Real.log 2 + Real.log (Real.cosh (z * Real.sqrt r)) :=
    Real.log_mul two_ne_zero (Real.cosh_pos _).ne'
  have hint_c : Integrable (fun z : ℝ => Real.log (Real.cosh (z * Real.sqrt r)))
      (gaussianReal 0 1) := by
    have heq : (fun z : ℝ => Real.log (Real.cosh (z * Real.sqrt r))) =
        fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z + 0)) := by funext z; ring_nf
    rw [heq]; exact integrable_log_cosh_affine_gaussianReal (Real.sqrt r) 0
  simp_rw [hpt]
  rw [integral_add (integrable_const (Real.log 2)) hint_c, integral_const, probReal_univ, one_smul]

/-- Derivative of `r' ↦ 𝔼 log(2 cosh(z √r'))` for `r > 0`:
equals `(1 / 2) * (1 - 𝔼 tanh²(z √r))`. -/
theorem hasDerivAt_integral_log_two_cosh_sqrt {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun r' => ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r')) ∂gaussianReal 0 1)
      ((1 / 2) * (1 - ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)) r := by
  have hfun : (fun r' => ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r')) ∂gaussianReal 0 1) =
      fun r' => Real.log 2 +
        ∫ z : ℝ, Real.log (Real.cosh (1 * Real.sqrt r' * z + 0)) ∂gaussianReal 0 1 := by
    funext r'
    rw [integral_log_two_cosh_sqrt_eq]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => by ring_nf)
  have hd_cosh := hasDerivAt_integral_log_cosh_sqrt 1 0 hr
  have hsub : (∫ z : ℝ, (1 - Real.tanh (1 * Real.sqrt r * z + 0) ^ 2) ∂gaussianReal 0 1) =
      1 - ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1 := by
    rw [integral_sub (integrable_const 1) (integrable_tanh_sq_affine (1 * Real.sqrt r) 0),
      integral_const, probReal_univ, one_smul]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => by ring_nf)
  rw [hfun]
  exact (hd_cosh.const_add (Real.log 2)).congr_deriv (by rw [hsub]; ring)

/-- Continuity of `r ↦ 𝔼 log cosh(z √r)` on `[0, 1]`. -/
theorem continuousOn_integral_log_cosh_sqrt :
    ContinuousOn
      (fun r : ℝ => ∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1)
      (Icc 0 1) := by
  refine continuousOn_of_dominated (bound := fun z => |z|)
    (fun r _ => ?_) (fun r hr => ae_of_all _ fun z => ?_)
    IsGaussian.integrable_id.abs (ae_of_all _ fun z => ?_)
  · exact ((Real.continuous_cosh.comp (continuous_id.mul continuous_const)).log
      fun _ => (Real.cosh_pos _).ne').aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_cosh_nonneg _)]
    calc Real.log (Real.cosh (z * Real.sqrt r)) ≤ |z * Real.sqrt r| := Real.log_cosh_le_abs _
      _ = |z| * Real.sqrt r := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ |z| * 1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 hr.2) (abs_nonneg _)
      _ = |z| := mul_one _
  · exact ((Real.continuous_cosh.comp
      (continuous_const.mul Real.continuous_sqrt)).log
      fun _ => (Real.cosh_pos _).ne').continuousOn

/-- **Partial derivative `∂F / ∂r` of `perceptronRSFunctional`:**
for `r > 0`, `r' ↦ F(α, r', q)` has derivative `(1 / 2) * (q - 𝔼 tanh²(z √r))` at `r`. -/
theorem hasDerivAt_perceptronRSFunctional_r (u : ℝ → ℝ) (α : ℝ) {r : ℝ} (hr : 0 < r) (q : ℝ) :
    HasDerivAt (fun r' => perceptronRSFunctional u α r' q)
      ((1 / 2) * (q - ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)) r := by
  unfold perceptronRSFunctional
  have hd_lin : HasDerivAt (fun r' : ℝ => -(1 / 2) * r' * (1 - q)) (-(1 / 2) * (1 - q)) r :=
    (((hasDerivAt_id r).const_mul (-(1 / 2 : ℝ))).mul_const (1 - q)).congr_deriv (by ring)
  exact ((hd_lin.add (hasDerivAt_integral_log_two_cosh_sqrt hr)).add_const _).congr_deriv (by ring)

/-- **Gaussian expectation of `(z / (2 √q) - ξ / (2 √(1 - q))) u'(θ) e^{u(θ)} / 𝔼_ξ e^{u(θ)}`:**
for `q ∈ (0, 1)`, this equals `-(1 / 2) * perceptronRhat u q` (Talagrand's step after Eq. (2.88),
proved via `stein_tilted_unit_replica_deriv` on `Unit` with `α_sh = √q`, `W_sh = 1 / (2 √q)`,
`α_aux = √(1 - q)`, `W_aux = -1 / (2 √(1 - q))`). -/
theorem integral_theta_deriv_tilted_eq_neg_half_rhat
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∫ z : ℝ,
        (∫ ξ : ℝ, (z / (2 * Real.sqrt q) - ξ / (2 * Real.sqrt (1 - q))) *
          deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)
          ∂((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
        ∂gaussianReal 0 1 =
      -(1 / 2) * perceptronRhat u q := by
  let γ_sh := Measure.pi fun _ : Unit => gaussianReal 0 1
  let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
  let μ₀ : Measure Unit := Measure.dirac ()
  let α_sh : Unit → Unit → ℝ := fun _ _ => Real.sqrt q
  let W_sh : Unit → Unit → ℝ := fun _ _ => 1 / (2 * Real.sqrt q)
  let α_aux : Unit → Unit → ℝ := fun _ _ => Real.sqrt (1 - q)
  let W_aux : Unit → Unit → ℝ := fun _ _ => -(1 / (2 * Real.sqrt (1 - q)))
  have hq_ne : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq.1).ne'
  have h1q_ne : Real.sqrt (1 - q) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hq.2)).ne'
  have hcov_sh (τ₁ τ₂ : Unit) : W_sh τ₁ ⬝ᵥ α_sh τ₂ = (1 / 2) * 1 := by
    simp only [W_sh, α_sh, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    field_simp
  have hcov_diag (τ : Unit) : W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0 := by
    rw [hcov_sh τ τ]
    have h2 : W_aux τ ⬝ᵥ α_aux τ = -(1 / 2) := by
      simp only [W_aux, α_aux, dotProduct, Finset.univ_unique, Finset.sum_singleton]
      field_simp
    rw [h2]; ring
  have hst := stein_tilted_unit_replica_deriv μ₀ (id : Unit → Unit) measurable_id
    α_sh W_sh α_aux W_aux hu (fun _ _ => 1) hcov_sh hcov_diag
  dsimp only [id_eq] at hst
  let e_u : (Unit → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique Unit ℝ
  have hmp_sh : MeasurePreserving ⇑e_u γ_sh (gaussianReal 0 1) :=
    measurePreserving_funUnique (gaussianReal 0 1) Unit
  let e_q : Unit × (Unit → ℝ) ≃ᵐ ℝ :=
    (MeasurableEquiv.uniqueProd Unit (Unit → ℝ)).trans e_u
  have he_q_apply (y : Unit × (Unit → ℝ)) : e_q y = y.2 () := rfl
  have hmp_q : MeasurePreserving ⇑e_q (μ₀.prod γ_aux) (gaussianReal 0 1) :=
    hmp_sh.comp (measurePreserving_snd (μ := μ₀) (ν := γ_aux))
  have htilted_w (w : Unit → ℝ) :
      ((μ₀.prod γ_aux).tilted
        (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))).map e_q =
      (gaussianReal 0 1).tilted (fun ξ => u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ)) := by
    have hVm : Measurable fun y : Unit × (Unit → ℝ) => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2) := by
      simp only [α_sh, α_aux, dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact hu.measurable.comp
        (measurable_const.add (measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)))
    rw [map_tilted_measurableEquiv e_q hmp_q hVm]
    congr 1; funext ξ
    obtain ⟨y, rfl⟩ := e_q.surjective ξ
    dsimp only [Function.comp_apply]
    rw [MeasurableEquiv.symm_apply_apply, he_q_apply]
    simp [α_sh, α_aux, dotProduct]
  let L_1d (z : ℝ) : ℝ :=
    ∫ ξ : ℝ, (z / (2 * Real.sqrt q) - ξ / (2 * Real.sqrt (1 - q))) *
      deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)
      ∂((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))
  have hL_m : Measurable L_1d :=
    measurable_integral_tilted_dep (hu.measurable.comp (by fun_prop))
      (((measurable_fst.div_const _).sub (measurable_snd.div_const _)).mul
        ((measurable_deriv u).comp (by fun_prop)))
  have hlhs_w (w : Unit → ℝ) :
      (∫ σ : Unit → Unit × (Unit → ℝ),
        1 * (W_sh (σ ()).1 ⬝ᵥ w + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ w + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2)))) =
      L_1d (w ()) := by
    let ν_w := (μ₀.prod γ_aux).tilted (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))
    have hVm : Measurable fun y : Unit × (Unit → ℝ) => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2) := by
      simp only [α_sh, α_aux, dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact hu.measurable.comp
        (measurable_const.add (measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)))
    have hprob_w : IsProbabilityMeasure ν_w :=
      isProbabilityMeasure_tilted_of_ae_le hVm.aemeasurable (ae_of_all _ fun _ => hu.le _)
    let g_ξ (ξ : ℝ) : ℝ :=
      (w () / (2 * Real.sqrt q) - ξ / (2 * Real.sqrt (1 - q))) *
        deriv u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ)
    have hg_m : Measurable g_ξ :=
      (measurable_const.sub (measurable_id.div_const _)).mul
        ((measurable_deriv u).comp (by fun_prop))
    have h1 := (integral_pi_map_equiv ν_w e_q (fun f_u : Unit → ℝ => g_ξ (f_u ()))).symm
    rw [htilted_w w] at h1
    have hprob_t := isProbabilityMeasure_tilted_cavityPath_new hu.measurable hu.le q (w ())
    have h2 : (∫ f_u : Unit → ℝ, g_ξ (f_u ())
        ∂(Measure.pi fun _ : Unit =>
          (gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ))) =
        L_1d (w ()) :=
      (measurePreserving_funUnique _ Unit).integral_comp_of_aestronglyMeasurable
        (g := g_ξ) hg_m.aestronglyMeasurable
    refine (integral_congr_ae (ae_of_all _ fun σ => ?_)).trans (h1.trans h2)
    dsimp only [g_ξ]
    rw [he_q_apply]
    simp only [show (Finset.univ : Finset Unit) = {()} from rfl,
      Finset.prod_singleton, one_mul, W_sh, W_aux, α_sh, α_aux,
      dotProduct, Finset.sum_singleton]
    ring
  have hlhs_eq :
      (∫ w, ∫ σ : Unit → Unit × (Unit → ℝ),
        1 * (W_sh (σ ()).1 ⬝ᵥ w + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ w + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))) ∂γ_sh) =
      ∫ z, L_1d z ∂gaussianReal 0 1 := by
    simp_rw [hlhs_w]
    exact hmp_sh.integral_comp_of_aestronglyMeasurable (g := L_1d) hL_m.aestronglyMeasurable
  let R_1d (z : ℝ) : ℝ :=
    (∫ ξ : ℝ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)
      ∂((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ^ 2
  have hR_m : Measurable R_1d :=
    (measurable_integral_tilted_dep (hu.measurable.comp (by fun_prop))
      ((measurable_deriv u).comp (by fun_prop))).pow_const 2
  have hrhs_w (w : Unit → ℝ) :
      (∫ σ : Option Unit → Unit × (Unit → ℝ),
        1 * deriv u (α_sh (σ (some ())).1 ⬝ᵥ w + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (σ none).1 ⬝ᵥ w + α_aux (σ none).1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2)))) =
      R_1d (w ()) := by
    let ν_w := (μ₀.prod γ_aux).tilted (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))
    have hVm : Measurable fun y : Unit × (Unit → ℝ) => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2) := by
      simp only [α_sh, α_aux, dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact hu.measurable.comp
        (measurable_const.add (measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)))
    have hprob_w : IsProbabilityMeasure ν_w :=
      isProbabilityMeasure_tilted_of_ae_le hVm.aemeasurable (ae_of_all _ fun _ => hu.le _)
    have hprob_t := isProbabilityMeasure_tilted_cavityPath_new hu.measurable hu.le q (w ())
    let h_ξ (ξ : ℝ) : ℝ := deriv u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ)
    have hh_m : Measurable h_ξ := (measurable_deriv u).comp (by fun_prop)
    have h1 := (integral_pi_map_equiv ν_w e_q
      (fun τ : Option Unit → ℝ => h_ξ (τ (some ())) * h_ξ (τ none))).symm
    rw [htilted_w w] at h1
    have h2 : (∫ τ : Option Unit → ℝ, h_ξ (τ (some ())) * h_ξ (τ none)
        ∂(Measure.pi fun _ : Option Unit =>
          (gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ))) =
        R_1d (w ()) := by
      rw [integral_pi_mul_of_ne _ (by decide : (some () : Option Unit) ≠ none) hh_m hh_m, ← sq]
    refine (integral_congr_ae (ae_of_all _ fun σ => ?_)).trans (h1.trans h2)
    dsimp only [h_ξ]
    rw [he_q_apply, he_q_apply]
    simp only [show (Finset.univ : Finset Unit) = {()} from rfl, one_mul, α_sh, α_aux,
      dotProduct, Finset.sum_singleton]
  have hrhs_eq :
      -(1 / 2) * (∫ w, ∫ σ : Option Unit → Unit × (Unit → ℝ),
        1 * deriv u (α_sh (σ (some ())).1 ⬝ᵥ w + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (σ none).1 ⬝ᵥ w + α_aux (σ none).1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))) ∂γ_sh) =
      -(1 / 2) * perceptronRhat u q := by
    simp_rw [hrhs_w]
    have hcomp_R : (∫ w : Unit → ℝ, R_1d (w ()) ∂γ_sh) = ∫ z, R_1d z ∂gaussianReal 0 1 :=
      hmp_sh.integral_comp_of_aestronglyMeasurable (g := R_1d) hR_m.aestronglyMeasurable
    rw [hcomp_R, perceptronRhat_eq_integral_sq_integral_tilted]
  rw [hlhs_eq, hrhs_eq] at hst
  exact hst

/-- **`q`-derivative of the nested Gaussian log-partition integral**
`q' ↦ 𝔼_z log 𝔼_ξ exp u(√q' z + √(1 - q') ξ)` on `q ∈ (0, 1)`: under `SmartPathPotential₂`, its
derivative at `q` equals `-(1 / 2) * perceptronRhat u q`. -/
theorem hasDerivAt_integral_log_integral_exp_q
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun q' => ∫ z : ℝ, Real.log (∫ ξ : ℝ,
        Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1)
      (-(1 / 2) * perceptronRhat u q) q := by
  let γ : Measure ℝ := gaussianReal 0 1
  obtain ⟨δ, hδ, hδ_bd⟩ := exists_Ioo_nhds_bound hq
  let U_nbhd : Set ℝ := Ioo (q - δ) (q + δ)
  have hU_nhds : U_nbhd ∈ 𝓝 q := Ioo_mem_nhds (by linarith) (by linarith)
  have hpt_bd (z ξ : ℝ) {t : ℝ} (ht : t ∈ U_nbhd) :
      |(z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
        deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)| ≤
      |D₁| * ((|z| + |ξ|) / (2 * Real.sqrt δ)) := by
    obtain ⟨hd_t, hd_1t⟩ := hδ_bd t ht
    rw [abs_mul, mul_comm _ |deriv u _|]
    exact mul_le_mul (hu.abs_deriv_le_abs _) (abs_div_two_sqrt_sub_le hδ hd_t hd_1t)
      (abs_nonneg _) (abs_nonneg D₁)
  let Z_q (q' z : ℝ) : ℝ :=
    ∫ ξ : ℝ, Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂γ
  let L_q (q' z : ℝ) : ℝ :=
    ∫ ξ : ℝ, (z / (2 * Real.sqrt q') - ξ / (2 * Real.sqrt (1 - q'))) *
      deriv u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)
      ∂(γ.tilted fun ξ => u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ))
  have hZq_deriv (z : ℝ) {q' : ℝ} (hq' : q' ∈ U_nbhd) :
      HasDerivAt (fun t => Real.log (Z_q t z)) (L_q q' z) q' := by
    obtain ⟨hd_t, hd_1t⟩ := hδ_bd q' hq'
    exact hasDerivAt_log_integral_exp_sqrt_path (μ := γ) hu.differentiable hu.le
      hu.abs_deriv_le (A := fun _ => z) (C := id) measurable_const measurable_id
      (integrable_const z) IsGaussian.integrable_id ⟨hδ.trans_le hd_t, by linarith⟩
  let dom_z (z : ℝ) : ℝ :=
    |D₁| * (|z| / (2 * Real.sqrt δ) +
      Real.exp (2 * |B|) * ((∫ ξ : ℝ, |ξ| ∂γ) / (2 * Real.sqrt δ)))
  have hdom_z_i : Integrable dom_z γ :=
    ((IsGaussian.integrable_id.abs.div_const _).add (integrable_const _)).const_mul |D₁|
  have hLq_bd (z : ℝ) {t : ℝ} (ht : t ∈ U_nbhd) : |L_q t z| ≤ dom_z z := by
    have hpos : 0 < 2 * Real.sqrt δ := by positivity
    let V_t (ξ : ℝ) : ℝ := u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)
    have hVt_m : Measurable V_t := hu.measurable.comp (by fun_prop)
    have hprob_t := isProbabilityMeasure_tilted_cavityPath_new hu.measurable hu.le t z
    have hξ_tilted : Integrable (fun ξ : ℝ => |ξ|) (γ.tilted V_t) :=
      integrable_tilted_of_ae_le hVt_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
        IsGaussian.integrable_id.abs
    have hpt_L (ξ : ℝ) :
        |(z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
          deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)| ≤
        |D₁| * (|z| / (2 * Real.sqrt δ) + |ξ| / (2 * Real.sqrt δ)) :=
      (hpt_bd z ξ ht).trans_eq (by ring)
    have hint_L : Integrable
        (fun ξ => (z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
          deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)) (γ.tilted V_t) := by
      have hm : Measurable fun ξ : ℝ =>
          (z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
            deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ) :=
        (measurable_const.sub (measurable_id.div_const _)).mul
          ((measurable_deriv u).comp (by fun_prop))
      exact integrable_tilted_of_abs_le_envelope hVt_m.aemeasurable hm.aestronglyMeasurable
        (((integrable_const _).add (IsGaussian.integrable_id.abs.div_const _)).const_mul |D₁|)
        (ae_of_all _ fun _ => hu.le _) (ae_of_all _ hpt_L)
    have h1 : |L_q t z| ≤
        ∫ ξ : ℝ, |D₁| * (|z| / (2 * Real.sqrt δ) + |ξ| / (2 * Real.sqrt δ)) ∂(γ.tilted V_t) :=
      (abs_integral_le_integral_abs).trans
        (integral_mono hint_L.abs
          (((integrable_const _).add (hξ_tilted.div_const _)).const_mul |D₁|) hpt_L)
    have h2 : (∫ ξ : ℝ, |D₁| * (|z| / (2 * Real.sqrt δ) + |ξ| / (2 * Real.sqrt δ))
        ∂(γ.tilted V_t)) =
        |D₁| * (|z| / (2 * Real.sqrt δ) + (∫ ξ, |ξ| ∂(γ.tilted V_t)) / (2 * Real.sqrt δ)) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hξ_tilted.div_const _),
        integral_const, probReal_univ, one_smul, integral_div]
    rw [h2] at h1
    have hdom_t : ∫ ξ, |ξ| ∂(γ.tilted V_t) ≤ Real.exp (2 * |B|) * ∫ ξ, |ξ| ∂γ := by
      have hbound := abs_integral_tilted_le_exp_mul_integral_abs (Y := fun ξ => |ξ|)
        hVt_m.aemeasurable
        (ae_of_all _ fun ξ => (hu.abs_le _).trans (le_abs_self B))
        (IsGaussian.integrable_id (μ := γ)).abs
      simpa only [probReal_univ, div_one, abs_abs] using (le_abs_self _).trans hbound
    refine h1.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (abs_nonneg D₁))
    calc (∫ ξ, |ξ| ∂(γ.tilted V_t)) / (2 * Real.sqrt δ)
        ≤ (Real.exp (2 * |B|) * ∫ ξ, |ξ| ∂γ) / (2 * Real.sqrt δ) :=
          div_le_div_of_nonneg_right hdom_t hpos.le
      _ = Real.exp (2 * |B|) * ((∫ ξ, |ξ| ∂γ) / (2 * Real.sqrt δ)) := by ring
  have hlogZ_int (t : ℝ) : Integrable (fun z => Real.log (Z_q t z)) γ :=
    integrable_log_integral_exp_cavityPath hu.measurable hu.abs_le t
  have hLq_m : AEStronglyMeasurable (L_q q) γ :=
    (measurable_integral_tilted_dep (hu.measurable.comp (by fun_prop))
      (((measurable_fst.div_const _).sub (measurable_snd.div_const _)).mul
        ((measurable_deriv u).comp (by fun_prop)))).aestronglyMeasurable
  have hd_pot : HasDerivAt (fun q' => ∫ z, Real.log (Z_q q' z) ∂γ) (∫ z, L_q q z ∂γ) q :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ)
      (F := fun t z => Real.log (Z_q t z)) (F' := L_q) (s := U_nbhd) (bound := dom_z)
      hU_nhds (Eventually.of_forall fun t => (hlogZ_int t).aestronglyMeasurable)
      (hlogZ_int q) hLq_m
      (ae_of_all _ fun z t ht => by rw [Real.norm_eq_abs]; exact hLq_bd z ht)
      hdom_z_i (ae_of_all _ fun z t ht => hZq_deriv z ht)).2
  exact hd_pot.congr_deriv (integral_theta_deriv_tilted_eq_neg_half_rhat hu hq)

/-- **Partial derivative `∂F / ∂q` of `perceptronRSFunctional` (Eq. (2.88) + Gaussian IBP):**
for `q ∈ (0, 1)` and `u` satisfying `SmartPathPotential₂`, `q' ↦ F(α, r, q')` has derivative
`(1 / 2) * (r - α * perceptronRhat u q)` at `q`. -/
theorem hasDerivAt_perceptronRSFunctional_q
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (α r : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q' => perceptronRSFunctional u α r q')
      ((1 / 2) * (r - α * perceptronRhat u q)) q := by
  have hd_pot := hasDerivAt_integral_log_integral_exp_q hu hq
  unfold perceptronRSFunctional
  have hd_lin : HasDerivAt (fun q' : ℝ => -(1 / 2) * r * (1 - q')) ((1 / 2) * r) q := by
    have hsub : HasDerivAt (fun q' : ℝ => 1 - q') (-1) q := by
      simpa using (hasDerivAt_id q).const_sub 1
    exact (hsub.const_mul (-(1 / 2) * r)).congr_deriv (by ring)
  exact ((hd_lin.add_const _).add (hd_pot.const_mul α)).congr_deriv (by ring)

/-- **Talagrand Section 2.4, Lemma 2.4.4 (critical point characterization of (2.87)):**
For `r > 0` and `q ∈ (0, 1)`, under `SmartPathPotential₂`, the partial derivatives of
`F(α, r, q) = perceptronRSFunctional u α r q` vanish if and only if `(q, r)` solves the
replica-symmetric system (2.87):
* `∂F / ∂r = 0 ↔ q = 𝔼 tanh²(z √r)`
* `∂F / ∂q = 0 ↔ r = α * perceptronRhat u q`. -/
theorem deriv_perceptronRSFunctional_eq_zero_iff
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (α : ℝ) {r : ℝ} (hr : 0 < r) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    (deriv (fun r' => perceptronRSFunctional u α r' q) r = 0 ↔
        q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1) ∧
      (deriv (fun q' => perceptronRSFunctional u α r q') q = 0 ↔
        r = α * perceptronRhat u q) := by
  rw [(hasDerivAt_perceptronRSFunctional_r u α hr q).deriv,
    (hasDerivAt_perceptronRSFunctional_q hu α r hq).deriv]
  constructor
  · rw [mul_eq_zero, or_iff_right (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_eq_zero]
  · rw [mul_eq_zero, or_iff_right (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_eq_zero]

/-- **Conditional envelope step of Eq. (2.89) (envelope theorem along the critical curve).**
This is a helper: it assumes interiority (`r α > 0`, `q α ∈ (0, 1)`) and differentiability of the
branch, which the book obtains from Theorem 2.4.1 and which
`exists_hasDerivAt_perceptronRSFunctional_small_load` derives. Cite that theorem, not this one, as
the statement of (2.89).
If `q, r : ℝ → ℝ` are differentiable at `α` with `r α > 0`, `q α ∈ (0, 1)`, and `(q α, r α)`
satisfies the critical-point system (2.87) at `α`, then `a ↦ F(a, r a, q a)` has derivative
`𝔼 log 𝔼_ξ exp u(√(q α) z + √(1 - q α) ξ)` at `α`. -/
theorem hasDerivAt_perceptronRSFunctional_alpha
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {α : ℝ} {q r : ℝ → ℝ}
    (hr_pos : 0 < r α) (hq_mem : q α ∈ Ioo (0 : ℝ) 1)
    (hq_crit : q α = ∫ z : ℝ, Real.tanh (z * Real.sqrt (r α)) ^ 2 ∂gaussianReal 0 1)
    (hr_crit : r α = α * perceptronRhat u (q α))
    (hr_diff : DifferentiableAt ℝ r α) (hq_diff : DifferentiableAt ℝ q α) :
    HasDerivAt (fun a => perceptronRSFunctional u a (r a) (q a))
      (∫ z : ℝ, Real.log (∫ ξ : ℝ,
        Real.exp (u (Real.sqrt (q α) * z + Real.sqrt (1 - q α) * ξ)) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1) α := by
  let ψ (q' : ℝ) : ℝ :=
    ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1
  have hd_ψ : HasDerivAt ψ (-(1 / 2) * perceptronRhat u (q α)) (q α) :=
    hasDerivAt_integral_log_integral_exp_q hu hq_mem
  have hd_term1 : HasDerivAt (fun a => -(1 / 2) * r a * (1 - q a))
      ((-(1 / 2) * deriv r α) * (1 - q α) + (-(1 / 2) * r α) * (-deriv q α)) α := by
    have h1q_a : HasDerivAt (fun a => 1 - q a) (-deriv q α) α := by
      simpa using hq_diff.hasDerivAt.const_sub 1
    exact (hr_diff.hasDerivAt.const_mul (-(1 / 2 : ℝ))).mul h1q_a
  have hd_term2 := (hasDerivAt_integral_log_two_cosh_sqrt hr_pos).comp α hr_diff.hasDerivAt
  have hd_term3 : HasDerivAt (fun a => a * ψ (q a))
      (1 * ψ (q α) + α * ((-(1 / 2) * perceptronRhat u (q α)) * deriv q α)) α :=
    (hasDerivAt_id α).mul (hd_ψ.comp α hq_diff.hasDerivAt)
  refine ((hd_term1.add hd_term2).add hd_term3).congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl) |>.congr_deriv ?_
  rw [← hq_crit, hr_crit]
  dsimp only [ψ]
  ring

/-- Right derivative of `r ↦ 𝔼 log(2 cosh(z √r))` at `0` within `[0, ∞)`: equals `1 / 2`. -/
private lemma hasDerivWithinAt_integral_log_two_cosh_sqrt_zero :
    HasDerivWithinAt
      (fun r : ℝ => ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1)
      (1 / 2) (Ici 0) 0 := by
  let F (r : ℝ) : ℝ := ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1
  let G (r : ℝ) : ℝ := (1 / 2) * (1 - ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
  have hF_cont : ContinuousOn F (Icc 0 1) :=
    ((continuousOn_const (s := Icc 0 1) (c := Real.log 2)).add
      continuousOn_integral_log_cosh_sqrt).congr fun r _ => integral_log_two_cosh_sqrt_eq r
  have hG_cont : Continuous G :=
    continuous_const.mul (continuous_const.sub lipschitzWith_one_integral_tanh_sq_sqrt.continuous)
  have hd_oo : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt F (G r) r :=
    fun _ hr => hasDerivAt_integral_log_two_cosh_sqrt hr.1
  have hdiff : DifferentiableOn ℝ F (Ioo 0 1) :=
    fun r hr => (hd_oo r hr).differentiableAt.differentiableWithinAt
  have heq : deriv F =ᶠ[𝓝[>] (0 : ℝ)] G := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact (hd_oo t ht).deriv
  have hG0 : G 0 = 1 / 2 := by simp [G]
  have hlim : Tendsto (deriv F) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
    rw [← hG0]
    exact (hG_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  have hc0 : ContinuousWithinAt F (Ioo 0 1) 0 :=
    (hF_cont 0 ⟨le_rfl, zero_le_one⟩).mono Ioo_subset_Icc_self
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hc0 (Ioo_mem_nhdsGT zero_lt_one) hlim

/-- Continuity of `q ↦ 𝔼_z log 𝔼_ξ exp u(√q z + √(1 - q) ξ)` on `[0, 1]` for bounded continuous
`u`. -/
theorem continuousOn_integral_log_integral_exp {u : ℝ → ℝ} (hu : Continuous u)
    {B : ℝ} (hB : ∀ x, |u x| ≤ B) :
    ContinuousOn
      (fun q : ℝ => ∫ z : ℝ, Real.log (∫ ξ : ℝ,
        Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1)
      (Icc 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  have hum : Measurable u := hu.measurable
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let Z_fn (q z : ℝ) : ℝ :=
    ∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ
  have hZ_cont (z : ℝ) : Continuous fun q => Z_fn q z :=
    continuous_of_dominated (bound := fun _ => Real.exp B)
      (fun q => (Real.continuous_exp.comp (hu.comp (by fun_prop))).measurable.aestronglyMeasurable)
      (fun q => ae_of_all _ fun _ => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.2 (hB_le _))
      (integrable_const _)
      (ae_of_all _ fun _ => Real.continuous_exp.comp (hu.comp (by fun_prop)))
  have hlog_cont (z : ℝ) : Continuous fun q => Real.log (Z_fn q z) :=
    (hZ_cont z).log fun q => (integral_exp_cavityPath_pos hum hB_le q z).ne'
  have hlog_meas (q : ℝ) : AEStronglyMeasurable (fun z => Real.log (Z_fn q z)) γ :=
    (integrable_log_integral_exp_cavityPath hum hB q).aestronglyMeasurable
  have hlog_bd (q z : ℝ) : ‖Real.log (Z_fn q z)‖ ≤ |B| := by
    rw [Real.norm_eq_abs]
    exact (abs_log_integral_exp_cavityPath_le hum hB q z).trans (le_abs_self B)
  exact (continuous_of_dominated (bound := fun _ => |B|) hlog_meas
    (fun q => ae_of_all _ (hlog_bd q)) (integrable_const _) (ae_of_all _ hlog_cont)).continuousOn

/-- **`q ↦ 𝔼 log 𝔼_ξ exp u(√q z + √(1 - q) ξ)` is `((1 / 2) * D₁²)`-Lipschitz on `[0, 1]`** under
`SmartPathPotential₂ u B D₁ D₂`: its derivative on `(0, 1)` is `-(1 / 2) * r̂(q)` and
`0 ≤ r̂(q) ≤ D₁²`. -/
theorem abs_integral_log_integral_exp_sub_le
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q₁ q₂ : ℝ} (hq₁ : q₁ ∈ Icc (0 : ℝ) 1) (hq₂ : q₂ ∈ Icc (0 : ℝ) 1) :
    |(∫ z : ℝ, Real.log (∫ ξ : ℝ,
          Real.exp (u (Real.sqrt q₁ * z + Real.sqrt (1 - q₁) * ξ)) ∂gaussianReal 0 1)
          ∂gaussianReal 0 1) -
      (∫ z : ℝ, Real.log (∫ ξ : ℝ,
          Real.exp (u (Real.sqrt q₂ * z + Real.sqrt (1 - q₂) * ξ)) ∂gaussianReal 0 1)
          ∂gaussianReal 0 1)| ≤
      (1 / 2) * D₁ ^ 2 * |q₁ - q₂| := by
  refine abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo
    (continuousOn_integral_log_integral_exp hu.continuous hu.abs_le)
    (fun q hq => ⟨-(1 / 2) * perceptronRhat u q,
      hasDerivAt_integral_log_integral_exp_q hu hq, ?_⟩) hq₂ hq₁
  have hm := rhat_mem_Icc hu.abs_deriv_le q
    (fun z => integrable_exp_cavityPath_new hu.measurable hu.le q z)
  rw [neg_mul, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hm.1]
  exact mul_le_mul_of_nonneg_left hm.2 (by positivity)

/-- **Talagrand Section 2.4, Eq. (2.89) for the small-load solution at positive load:**
Given `D ∈ ℝ`, there exists `K(D) > 0` (chosen before `u, q, r, α`) such that whenever `u` satisfies
(2.7), `0 < α` with `α * K(D) < 1`, and `(q a, r a)` solves (2.68) for all `a` near `α` (the unique
small-load branch of Theorem 2.4.1 is such a family), the composite functional
`a ↦ F(a, r a, q a)` is differentiable at `α` with derivative
`𝔼 log 𝔼_ξ exp u(√(q α) z + √(1 - q α) ξ)`. This unconditionally covers both the
zero branch `perceptronRhat u 0 = 0` (where `(q, r) = (0, 0)` and `F` is affine in `α`) and the
interior branch `perceptronRhat u 0 > 0` (where `r α > 0`, `q α ∈ (0, 1)`, and `(q, r)` are
differentiable at `α`). -/
theorem exists_hasDerivAt_perceptronRSFunctional_small_load (D : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {q r : ℝ → ℝ} {α : ℝ} (_hα_pos : 0 < α) (_hα : α * K < 1)
        (_hfix : ∀ᶠ a in 𝓝 α,
          q a = (∫ z : ℝ, Real.tanh (z * Real.sqrt (r a)) ^ 2 ∂gaussianReal 0 1) ∧
            r a = a * perceptronRhat u (q a)),
        HasDerivAt (fun a => perceptronRSFunctional u a (r a) (q a))
          (∫ z : ℝ, Real.log (∫ ξ : ℝ,
            Real.exp (u (Real.sqrt (q α) * z + Real.sqrt (1 - q α) * ξ)) ∂gaussianReal 0 1)
            ∂gaussianReal 0 1) α := by
  obtain ⟨K_der, hKder0, h_rhat_der⟩ := exists_hasDerivAt_rhat_abs_le D
  obtain ⟨K_sub, hKsub0, h_sub_lip⟩ := exists_abs_rs_fixed_point_sub_le D
  let K : ℝ := max (2 * K_der) K_sub + 1
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, ?_⟩
  intro u hd hb q r α hα_pos hα hfix
  obtain ⟨ε, hε, hεfix⟩ := Metric.eventually_nhds_iff.1 hfix
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hα_lt : α < 1 / K := (lt_div_iff₀ hK_pos).2 hα
  let δ : ℝ := min (min (α / 2) ((1 / K - α) / 2)) ε
  have hδ : 0 < δ :=
    lt_min (lt_min (half_pos hα_pos) (half_pos (sub_pos.2 hα_lt))) hε
  have hδε : δ ≤ ε := min_le_right _ _
  have hb_in {b : ℝ} (hb_mem : b ∈ Ioo (α - δ) (α + δ)) : 0 ≤ b ∧ b * K ≤ 1 := by
    have hd1 : δ ≤ α / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hd2 : δ ≤ (1 / K - α) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hb0 : 0 ≤ b := by linarith [hb_mem.1]
    have hb_ub : b ≤ 1 / K := by linarith [hb_mem.2]
    exact ⟨hb0, (le_div_iff₀ hK_pos).1 hb_ub⟩
  have hfix_in {b : ℝ} (hb_mem : b ∈ Ioo (α - δ) (α + δ)) :
      q b = (∫ z : ℝ, Real.tanh (z * Real.sqrt (r b)) ^ 2 ∂gaussianReal 0 1) ∧
        r b = b * perceptronRhat u (q b) :=
    hεfix (by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hb_mem.1], by linarith [hb_mem.2]⟩)
  have hK_ge_sub : K_sub ≤ K := (le_max_right _ _).trans (by dsimp only [K]; linarith)
  have hK_ge_2der : 2 * K_der ≤ K := (le_max_left _ _).trans (by dsimp only [K]; linarith)
  have hq_lip : ∀ a ∈ Ioo (α - δ) (α + δ), ∀ b ∈ Ioo (α - δ) (α + δ),
      |q a - q b| ≤ 2 * D ^ 2 * |a - b| := by
    intro a ha_m b hb_m
    obtain ⟨ha0, haK⟩ := hb_in ha_m
    have ha_sub : a * K_sub ≤ 1 := (mul_le_mul_of_nonneg_left hK_ge_sub ha0).trans haK
    exact h_sub_lip hd hb ha0 ha_sub (hfix_in ha_m).1 (hfix_in ha_m).2
      (hfix_in hb_m).1 (hfix_in hb_m).2
  rcases (perceptronRhat_nonneg u 0).eq_or_lt with hrhat0_zero | hrhat0_pos
  · have hzero_branch : ∀ b ∈ Ioo (α - δ) (α + δ), q b = 0 ∧ r b = 0 := by
      intro b hb_m
      obtain ⟨hb0, hbK⟩ := hb_in hb_m
      have hb_sub : b * K_sub ≤ 1 := (mul_le_mul_of_nonneg_left hK_ge_sub hb0).trans hbK
      have h0_q : (0 : ℝ) = ∫ z : ℝ, Real.tanh (z * Real.sqrt 0) ^ 2 ∂gaussianReal 0 1 := by simp
      have h0_r : (0 : ℝ) = b * perceptronRhat u 0 := by rw [← hrhat0_zero, mul_zero]
      have hdiff := h_sub_lip hd hb hb0 hb_sub (hfix_in hb_m).1 (hfix_in hb_m).2 h0_q h0_r
      rw [sub_self, abs_zero, mul_zero, sub_zero] at hdiff
      have hqb0 : q b = 0 := abs_nonpos_iff.1 hdiff
      refine ⟨hqb0, ?_⟩
      rw [(hfix_in hb_m).2, hqb0, ← hrhat0_zero, mul_zero]
    have hα_mem : α ∈ Ioo (α - δ) (α + δ) := ⟨by linarith, by linarith⟩
    obtain ⟨hqα0, _⟩ := hzero_branch α hα_mem
    let c₀ : ℝ := ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt 0 * z + Real.sqrt (1 - 0) * ξ)) ∂gaussianReal 0 1) ∂gaussianReal 0 1
    let c_cosh : ℝ := ∫ z : ℝ, Real.log (2 * Real.cosh 0) ∂gaussianReal 0 1
    have hcongr : (fun a => perceptronRSFunctional u a (r a) (q a)) =ᶠ[𝓝 α]
        fun a => c_cosh + a * c₀ := by
      filter_upwards [Ioo_mem_nhds (by linarith : α - δ < α) (by linarith : α < α + δ)] with b hb_m
      obtain ⟨hqb0, hrb0⟩ := hzero_branch b hb_m
      unfold perceptronRSFunctional
      rw [hqb0, hrb0]
      simp [c_cosh, c₀]
    have hd_aff : HasDerivAt (fun a : ℝ => c_cosh + a * c₀) c₀ α := by
      simpa using ((hasDerivAt_id α).mul_const c₀).const_add c_cosh
    rw [hqα0]
    exact hd_aff.congr_of_eventuallyEq hcongr
  · have hα_mem : α ∈ Ioo (α - δ) (α + δ) := ⟨by linarith, by linarith⟩
    obtain ⟨hα0, hαK⟩ := hb_in hα_mem
    have hqα := (hfix_in hα_mem).1
    have hrα := (hfix_in hα_mem).2
    have hrα_pos : 0 < r α := by
      have hrα_nn : 0 ≤ r α := by
        rw [hrα]; exact mul_nonneg hα0 (perceptronRhat_nonneg u (q α))
      rcases hrα_nn.eq_or_lt with hr0_eq | hpos
      · exfalso
        have hq0_eq : q α = 0 := by rw [hqα, ← hr0_eq]; simp
        have hr_pos' : 0 < r α := by rw [hrα, hq0_eq]; exact mul_pos hα_pos hrhat0_pos
        linarith
      · exact hpos
    have hqα_mem : q α ∈ Ioo (0 : ℝ) 1 := by
      rw [hqα]; exact integral_tanh_sq_sqrt_mem_Ioo hrα_pos
    let G (r' : ℝ) : ℝ := ∫ z : ℝ, Real.tanh (z * Real.sqrt r') ^ 2 ∂gaussianReal 0 1
    let R := perceptronRhat u
    obtain ⟨hG_der, hG_bd⟩ := hasDerivAt_integral_tanh_sq_sqrt_and_abs_le hrα_pos
    obtain ⟨R', hR_der, hR_bd⟩ := h_rhat_der hd hb hqα_mem
    let G' : ℝ := ∫ z : ℝ, (1 - Real.tanh (z * Real.sqrt (r α)) ^ 2) *
      (1 - 3 * Real.tanh (z * Real.sqrt (r α)) ^ 2) ∂gaussianReal 0 1
    have hden_pos : 1 / 2 ≤ 1 - α * G' * R' := by
      have hprod : |α * G' * R'| ≤ α * K_der := by
        rw [abs_mul, abs_mul, abs_of_pos hα_pos]
        calc α * |G'| * |R'| ≤ α * 1 * K_der :=
              mul_le_mul (mul_le_mul_of_nonneg_left hG_bd hα_pos.le) hR_bd
                (abs_nonneg _) (mul_nonneg hα_pos.le zero_le_one)
          _ = α * K_der := by ring
      have haK_half : α * K_der ≤ 1 / 2 := by
        have h2 : α * (2 * K_der) ≤ 1 := (mul_le_mul_of_nonneg_left hK_ge_2der hα0).trans hαK
        linarith
      have hle : α * G' * R' ≤ 1 / 2 := (le_abs_self _).trans (hprod.trans haK_half)
      linarith
    have hG_at : HasDerivAt G G' (α * R (q α)) := by rwa [← hrα]
    have hq_fix_loc : ∀ b ∈ Ioo (α - δ) (α + δ), q b = G (b * R (q b)) := by
      intro b hb_m
      change q b = ∫ z : ℝ, Real.tanh (z * Real.sqrt (b * perceptronRhat u (q b))) ^ 2
        ∂gaussianReal 0 1
      rw [← (hfix_in hb_m).2]
      exact (hfix_in hb_m).1
    have hq_diff : DifferentiableAt ℝ q α :=
      (hasDerivAt_of_fixed_point_contraction hδ hq_fix_loc
        (fun b hb_m => hq_lip b hb_m α hα_mem) hG_at hR_der (by linarith)).differentiableAt
    have hr_diff : DifferentiableAt ℝ r α := by
      have hr_congr : r =ᶠ[𝓝 α] fun b => b * R (q b) := by
        filter_upwards [Ioo_mem_nhds (by linarith : α - δ < α) (by linarith : α < α + δ)]
          with b hb_m
        exact (hfix_in hb_m).2
      exact (differentiableAt_id.mul (hR_der.differentiableAt.comp α hq_diff)).congr_of_eventuallyEq
        hr_congr
    exact hasDerivAt_perceptronRSFunctional_alpha hu hrα_pos hqα_mem hqα hrα hr_diff hq_diff

/-- **Talagrand Section 2.4, Eq. (2.89) right derivative at zero load `α = 0`:**
For a first-order bounded potential (`u` differentiable, `|u| ≤ B`, `|u'| ≤ D`; no second or third
derivative is needed), if `(q a, r a)` solves (2.68) for `a ∈ [0, δ)` (`δ > 0`), then
`(q 0, r 0) = (0, 0)` and `a ↦ F(a, r a, q a)` has right derivative
`𝔼 log 𝔼_ξ exp u(√(q 0) z + √(1 - q 0) ξ)` (`= log 𝔼_ξ exp u(ξ)`) at `0` within `[0, ∞)`. -/
theorem hasDerivWithinAt_perceptronRSFunctional_zero
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    {q r : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hq_fix : ∀ a ∈ Ico 0 δ,
      q a = ∫ z : ℝ, Real.tanh (z * Real.sqrt (r a)) ^ 2 ∂gaussianReal 0 1)
    (hr_fix : ∀ a ∈ Ico 0 δ, r a = a * perceptronRhat u (q a)) :
    HasDerivWithinAt (fun a => perceptronRSFunctional u a (r a) (q a))
      (∫ z : ℝ, Real.log (∫ ξ : ℝ,
        Real.exp (u (Real.sqrt (q 0) * z + Real.sqrt (1 - q 0) * ξ)) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1)
      (Ici 0) 0 := by
  have hr0 : r 0 = 0 := by rw [hr_fix 0 ⟨le_rfl, hδ⟩, zero_mul]
  have hq0 : q 0 = 0 := by rw [hq_fix 0 ⟨le_rfl, hδ⟩, hr0]; simp
  let ψ (q' : ℝ) : ℝ :=
    ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1
  let C (r' : ℝ) : ℝ := ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r')) ∂gaussianReal 0 1
  have hr_mem {a : ℝ} (ha : a ∈ Ico 0 δ) : 0 ≤ r a ∧ r a ≤ D ^ 2 * a := by
    rw [hr_fix a ha, mul_comm (D ^ 2) a]
    have hm := rhat_mem_Icc hu.abs_deriv_le (q a)
      (fun z => integrable_exp_cavityPath_new hu.measurable hu.le (q a) z)
    exact ⟨mul_nonneg ha.1 hm.1, mul_le_mul_of_nonneg_left hm.2 ha.1⟩
  have hq_mem {a : ℝ} (ha : a ∈ Ico 0 δ) : 0 ≤ q a ∧ q a ≤ r a ∧ q a ≤ 1 := by
    have hmem : q a ∈ Icc (0 : ℝ) 1 := by
      rw [hq_fix a ha]; exact integral_tanh_sq_sqrt_mem_Icc _
    have hle_r : q a ≤ r a := by
      rw [hq_fix a ha]; exact integral_tanh_sq_sqrt_le (hr_mem ha).1
    exact ⟨hmem.1, hle_r, hmem.2⟩
  have hr_tendsto : Tendsto r (𝓝[≥] 0) (𝓝[≥] 0) :=
    tendsto_nhdsGE_of_le_mul hδ fun _ ha => hr_mem ha
  have hr_bigO : Asymptotics.IsBigO (𝓝[≥] 0) (fun a => r a - 0) (fun a => a - 0) := by
    refine Asymptotics.IsBigO.of_bound (D ^ 2) ?_
    filter_upwards [Ico_mem_nhdsGE hδ] with a ha
    rw [sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hr_mem ha).1, abs_of_nonneg ha.1]
    exact (hr_mem ha).2
  have hC_o : Asymptotics.IsLittleO (𝓝[≥] 0)
      (fun a => C (r a) - C 0 - (1 / 2) * r a) (fun a => a - 0) := by
    have h1 := hasDerivWithinAt_integral_log_two_cosh_sqrt_zero.isLittleO
    refine ((h1.comp_tendsto hr_tendsto).trans_isBigO hr_bigO).congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun a => ?_
    dsimp only [C, Function.comp_apply]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hrq_o : Asymptotics.IsLittleO (𝓝[≥] 0)
      (fun a => (1 / 2) * r a * q a) (fun a => a - 0) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Ico_mem_nhdsGE (lt_min hδ (show 0 < c / (D ^ 4 + 1) by positivity))] with a ha
    have ha_δ : a ∈ Ico 0 δ := ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩
    obtain ⟨hr_nn, hr_ub⟩ := hr_mem ha_δ
    obtain ⟨hq_nn, hq_ub, -⟩ := hq_mem ha_δ
    rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg ha.1]
    have hq_d : q a ≤ D ^ 2 * a := hq_ub.trans hr_ub
    have hprod : (1 / 2) * r a * q a ≤ a * (a * D ^ 4) := by
      have ha_d2 : 0 ≤ 1 * (D ^ 2 * a) := mul_nonneg zero_le_one (mul_nonneg (sq_nonneg D) ha.1)
      calc (1 / 2) * r a * q a ≤ 1 * (D ^ 2 * a) * (D ^ 2 * a) :=
            mul_le_mul (mul_le_mul (by norm_num) hr_ub hr_nn zero_le_one) hq_d hq_nn ha_d2
        _ = a * (a * D ^ 4) := by ring
    have ha_c : a * (D ^ 4 + 1) ≤ c :=
      (le_div_iff₀ (by positivity)).1 (ha.2.trans_le (min_le_right _ _)).le
    have had4 : a * D ^ 4 ≤ c :=
      (mul_le_mul_of_nonneg_left (by linarith) ha.1).trans ha_c
    exact hprod.trans (by rw [mul_comm c a]; exact mul_le_mul_of_nonneg_left had4 ha.1)
  have hψ_cont : ContinuousOn ψ (Icc 0 1) :=
    continuousOn_integral_log_integral_exp hu.continuous hu.abs_le
  have hq_tendsto : Tendsto q (𝓝[≥] 0) (nhdsWithin (q 0) (Icc 0 1)) := by
    have hq_ge : Tendsto q (𝓝[≥] 0) (𝓝[≥] 0) :=
      tendsto_nhdsGE_of_le_mul hδ fun a ha => ⟨(hq_mem ha).1, (hq_mem ha).2.1.trans (hr_mem ha).2⟩
    rw [tendsto_nhdsWithin_iff, hq0]
    refine ⟨tendsto_nhds_of_tendsto_nhdsWithin hq_ge, ?_⟩
    filter_upwards [Ico_mem_nhdsGE hδ] with a ha
    exact ⟨(hq_mem ha).1, (hq_mem ha).2.2⟩
  have hψ_o : Asymptotics.IsLittleO (𝓝[≥] 0)
      (fun a => a * (ψ (q a) - ψ (q 0))) (fun a => a - 0) := by
    have h1 : Asymptotics.IsLittleO (𝓝[≥] 0)
        (fun a => (a - 0) * (ψ (q a) - ψ (q 0))) (fun a => (a - 0) * 1) := by
      refine (Asymptotics.isBigO_refl (fun a => a - 0) (𝓝[≥] 0)).mul_isLittleO ?_
      rw [Asymptotics.isLittleO_one_iff]
      have hq0_mem : q 0 ∈ Icc (0 : ℝ) 1 := by rw [hq0]; exact ⟨le_rfl, zero_le_one⟩
      have hc := (hψ_cont (q 0) hq0_mem).tendsto.comp hq_tendsto
      simpa using hc.sub_const (ψ (q 0))
    simpa only [sub_zero, mul_one] using h1
  rw [hasDerivWithinAt_iff_isLittleO]
  refine ((hC_o.add hrq_o).add hψ_o).congr' ?_ EventuallyEq.rfl
  refine Eventually.of_forall fun a => ?_
  unfold perceptronRSFunctional
  dsimp only [C, ψ]
  rw [hr0]
  simp only [sub_zero, smul_eq_mul, neg_mul, zero_mul]
  ring

/-- **Talagrand Section 2.4, Eq. (2.89) for the solution branch of Theorem 2.4.1.**
Given `D`, there is `K(D) > 0` such that for every `u` satisfying (2.7) there are functions
`q, r : ℝ → ℝ` with `(q a, r a)` solving (2.68) for every load `a ≥ 0` with `a * K(D) ≤ 1` (the
unique solution of Theorem 2.4.1), and the composite functional `a ↦ F(a, r a, q a)` has derivative
`𝔼 log 𝔼_ξ exp u(√(q α) z + √(1 - q α) ξ)` at every `α ∈ (0, 1 / K(D))`, and the corresponding right
derivative at `0` within `[0, ∞)`. No solution family is assumed. -/
theorem exists_branch_hasDerivAt_perceptronRSFunctional (D : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D),
        ∃ q r : ℝ → ℝ,
          (∀ a, 0 ≤ a → a * K ≤ 1 →
            q a = (∫ z : ℝ, Real.tanh (z * Real.sqrt (r a)) ^ 2 ∂gaussianReal 0 1) ∧
              r a = a * perceptronRhat u (q a)) ∧
          (∀ α, 0 < α → α * K < 1 →
            HasDerivAt (fun a => perceptronRSFunctional u a (r a) (q a))
              (∫ z : ℝ, Real.log (∫ ξ : ℝ,
                Real.exp (u (Real.sqrt (q α) * z + Real.sqrt (1 - q α) * ξ)) ∂gaussianReal 0 1)
                ∂gaussianReal 0 1) α) ∧
          HasDerivWithinAt (fun a => perceptronRSFunctional u a (r a) (q a))
            (∫ z : ℝ, Real.log (∫ ξ : ℝ,
              Real.exp (u (Real.sqrt (q 0) * z + Real.sqrt (1 - q 0) * ξ)) ∂gaussianReal 0 1)
              ∂gaussianReal 0 1) (Ici 0) 0 := by
  obtain ⟨K₁, hK₁, h_small⟩ := exists_hasDerivAt_perceptronRSFunctional_small_load D
  obtain ⟨K₂, hK₂, h_uniq⟩ := exists_unique_rs_fixed_point D
  let K : ℝ := max K₁ K₂
  have hK_pos : 0 < K := lt_of_lt_of_le hK₁ (le_max_left _ _)
  refine ⟨K, hK_pos, ?_⟩
  intro u hd hb
  classical
  have hex : ∀ a : ℝ, 0 ≤ a → a * K ≤ 1 → ∃ p : ℝ × ℝ,
      p.1 = (∫ z : ℝ, Real.tanh (z * Real.sqrt p.2) ^ 2 ∂gaussianReal 0 1) ∧
        p.2 = a * perceptronRhat u p.1 := fun a ha0 haK =>
    (h_uniq hd hb ha0
      ((mul_le_mul_of_nonneg_left (le_max_right _ _) ha0).trans haK)).exists
  let P : ℝ → ℝ × ℝ := fun a =>
    if h : 0 ≤ a ∧ a * K ≤ 1 then Classical.choose (hex a h.1 h.2) else (0, 0)
  have hspec : ∀ a, 0 ≤ a → a * K ≤ 1 →
      (P a).1 = (∫ z : ℝ, Real.tanh (z * Real.sqrt (P a).2) ^ 2 ∂gaussianReal 0 1) ∧
        (P a).2 = a * perceptronRhat u (P a).1 := by
    intro a ha0 haK
    have h : 0 ≤ a ∧ a * K ≤ 1 := ⟨ha0, haK⟩
    simp only [P, h]
    exact Classical.choose_spec (hex a ha0 haK)
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  refine ⟨fun a => (P a).1, fun a => (P a).2, hspec, ?_, ?_⟩
  · intro α hα_pos hαK
    have hαK₁ : α * K₁ < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_left _ _) hα_pos.le) hαK
    refine h_small hd hb hα_pos hαK₁ ?_
    have hev : ∀ᶠ a in 𝓝 α, 0 < a ∧ a * K < 1 :=
      (eventually_gt_nhds hα_pos).and
        ((continuous_id.mul continuous_const).continuousAt.eventually_lt
          continuousAt_const hαK)
    filter_upwards [hev] with a ha
    exact hspec a ha.1.le ha.2.le
  · refine hasDerivWithinAt_perceptronRSFunctional_zero hu.toSmartPathPotential
      (δ := 1 / K) (by positivity) (fun a ha => (hspec a ha.1 ?_).1)
      (fun a ha => (hspec a ha.1 ?_).2)
    all_goals exact ((lt_div_iff₀ hK_pos).1 ha.2).le

/-- **Second-order increment bound along the replica-symmetric solution branch (the `F''` step of
Talagrand's second proof of Theorem 2.4.2).**
Given `D ∈ ℝ`, there exists `K(D) > 0` such that for every `u` satisfying (2.7) there are functions
`q, r : ℝ → ℝ` solving (2.68) for every load `a ≥ 0` with `a * K(D) ≤ 1` (the unique branch of
Theorem 2.4.1), for which `F'(a) = 𝔼 log 𝔼_ξ exp u(√(q a) z + √(1 - q a) ξ)` is `D⁴`-Lipschitz on
`[0, 1 / K(D)]` and every `a, b ∈ [0, 1 / K(D)]` satisfies
$$|F(b) - F(a) - (b - a)\,F'(a)| \le \frac{D^4}{2}\,(b - a)^2,$$
so `|F((M + 1) / (N + 1)) - F(M / (N + 1)) - (N + 1)⁻¹ F'(M / (N + 1))| ≤ D⁴ / (2 (N + 1)²)`. -/
theorem exists_branch_taylor_perceptronRSFunctional_le (D : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D),
        ∃ q r : ℝ → ℝ,
          (∀ a, 0 ≤ a → a * K ≤ 1 →
            q a = (∫ z : ℝ, Real.tanh (z * Real.sqrt (r a)) ^ 2 ∂gaussianReal 0 1) ∧
              r a = a * perceptronRhat u (q a)) ∧
          (∀ a b, 0 ≤ a → a * K ≤ 1 → 0 ≤ b → b * K ≤ 1 →
            |(∫ z : ℝ, Real.log (∫ ξ : ℝ,
                  Real.exp (u (Real.sqrt (q a) * z + Real.sqrt (1 - q a) * ξ)) ∂gaussianReal 0 1)
                  ∂gaussianReal 0 1) -
              (∫ z : ℝ, Real.log (∫ ξ : ℝ,
                  Real.exp (u (Real.sqrt (q b) * z + Real.sqrt (1 - q b) * ξ)) ∂gaussianReal 0 1)
                  ∂gaussianReal 0 1)| ≤
              D ^ 4 * |a - b|) ∧
          (∀ a b, 0 ≤ a → a * K ≤ 1 → 0 ≤ b → b * K ≤ 1 →
            |perceptronRSFunctional u b (r b) (q b) - perceptronRSFunctional u a (r a) (q a) -
                (b - a) * ∫ z : ℝ, Real.log (∫ ξ : ℝ,
                  Real.exp (u (Real.sqrt (q a) * z + Real.sqrt (1 - q a) * ξ)) ∂gaussianReal 0 1)
                  ∂gaussianReal 0 1| ≤
              (D ^ 4 / 2) * (b - a) ^ 2) := by
  obtain ⟨K₁, hK₁, h_branch⟩ := exists_branch_hasDerivAt_perceptronRSFunctional D
  obtain ⟨K₂, hK₂, h_sub⟩ := exists_abs_rs_fixed_point_sub_le D
  let K : ℝ := 2 * max K₁ K₂
  have hK_pos : 0 < K := by dsimp only [K]; linarith [lt_of_lt_of_le hK₁ (le_max_left K₁ K₂)]
  refine ⟨K, hK_pos, ?_⟩
  intro u hd hb
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨q, r, hspec₁, hder_pos, hder_zero⟩ := h_branch hd hb
  have hmax_pos : 0 < max K₁ K₂ := lt_of_lt_of_le hK₁ (le_max_left K₁ K₂)
  have hK_le₁ : K₁ ≤ K := (le_max_left K₁ K₂).trans (by dsimp only [K]; linarith)
  have hK_lt₁ : ∀ a, 0 ≤ a → a * K ≤ 1 → a * K₁ < 1 := by
    intro a ha0 haK
    have h2 : a * (2 * K₁) ≤ 1 :=
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_max_left K₁ K₂) zero_le_two) ha0).trans haK
    nlinarith [hK₁]
  have hK_le₂ : K₂ ≤ K := (le_max_right K₁ K₂).trans (by dsimp only [K]; linarith)
  have hspec : ∀ a, 0 ≤ a → a <= 2 / K →
      q a = (∫ z : ℝ, Real.tanh (z * Real.sqrt (r a)) ^ 2 ∂gaussianReal 0 1) ∧
        r a = a * perceptronRhat u (q a) := by
    intro a ha0 ha_ub
    have haK₁ : a * K₁ ≤ 1 := by
      have h1 : a * K ≤ 2 := (le_div_iff₀ hK_pos).1 ha_ub
      have h2 : a * (2 * K₁) ≤ 2 :=
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_max_left K₁ K₂) zero_le_two) ha0).trans h1
      linarith
    exact hspec₁ a ha0 haK₁
  let ψ (q' : ℝ) : ℝ :=
    ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1
  let F_br (a : ℝ) : ℝ := perceptronRSFunctional u a (r a) (q a)
  let F'_br (a : ℝ) : ℝ := ψ (q a)
  have hq_mem_all : ∀ a, 0 ≤ a → a ≤ 2 / K → q a ∈ Icc (0 : ℝ) 1 := fun a ha0 ha_ub => by
    rw [(hspec a ha0 ha_ub).1]; exact integral_tanh_sq_sqrt_mem_Icc _
  have hF'_lip : ∀ a b, 0 ≤ a → a * K ≤ 1 → 0 ≤ b → b ≤ 2 / K →
      |F'_br a - F'_br b| ≤ D ^ 4 * |a - b| := by
    intro a b ha0 haK hb0 hb_ub
    have ha_ub : a ≤ 2 / K := (le_div_iff₀ hK_pos).2 (haK.trans (by norm_num))
    have haK₂ : a * K₂ ≤ 1 := (mul_le_mul_of_nonneg_left hK_le₂ ha0).trans haK
    have hq_sub := h_sub hd hb ha0 haK₂ (hspec a ha0 ha_ub).1 (hspec a ha0 ha_ub).2
      (hspec b hb0 hb_ub).1 (hspec b hb0 hb_ub).2
    have hψ_sub := abs_integral_log_integral_exp_sub_le hu
      (hq_mem_all a ha0 ha_ub) (hq_mem_all b hb0 hb_ub)
    calc |F'_br a - F'_br b|
        ≤ (1 / 2) * D ^ 2 * |q a - q b| := hψ_sub
      _ ≤ (1 / 2) * D ^ 2 * (2 * D ^ 2 * |a - b|) :=
          mul_le_mul_of_nonneg_left hq_sub (by positivity)
      _ = D ^ 4 * |a - b| := by ring
  refine ⟨q, r, fun a ha0 haK =>
      hspec a ha0 ((le_div_iff₀ hK_pos).2 (haK.trans (by norm_num))),
    fun a b ha0 haK hb0 hbK =>
      hF'_lip a b ha0 haK hb0 ((le_div_iff₀ hK_pos).2 (hbK.trans (by norm_num))),
    ?_⟩
  intro a b ha0 haK hb0 hbK
  have ha_le : a ≤ 1 / K := (le_div_iff₀ hK_pos).2 haK
  have hb_le : b ≤ 1 / K := (le_div_iff₀ hK_pos).2 hbK
  -- Apply `image_norm_le_of_norm_deriv_right_le_deriv_boundary` on `[0, 1]`.
  rcases eq_or_ne a b with rfl | hab_ne
  · simp
  let Δ : ℝ := b - a
  let g (s : ℝ) : ℝ := F_br (a + s * Δ) - F_br a - s * (Δ * F'_br a)
  have hseg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ a + s * Δ ∧ (a + s * Δ) * K ≤ 1 := by
    have hconv1 : (1 - s) * a + s * b = a + s * Δ := by dsimp only [Δ]; ring
    rw [← hconv1]
    have h1s : 0 ≤ 1 - s := sub_nonneg.2 hs.2
    refine ⟨add_nonneg (mul_nonneg h1s ha0) (mul_nonneg hs.1 hb0), ?_⟩
    calc ((1 - s) * a + s * b) * K
        = (1 - s) * (a * K) + s * (b * K) := by ring
      _ ≤ (1 - s) * 1 + s * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left haK h1s) (mul_le_mul_of_nonneg_left hbK hs.1)
      _ = 1 := by ring
  have hg_cont : ContinuousOn g (Icc 0 1) := by
    have hF_diff_within : ∀ x ∈ Icc (0 : ℝ) (1 / K),
        HasDerivWithinAt F_br (F'_br x) (Ici 0) x := by
      intro x hx
      rcases hx.1.eq_or_lt with rfl | hx_pos
      · exact hder_zero
      · have hxK : x * K ≤ 1 := (le_div_iff₀ hK_pos).1 hx.2
        exact (hder_pos x hx_pos (hK_lt₁ x hx_pos.le hxK)).hasDerivWithinAt
    have hF_cont : ContinuousOn F_br (Icc 0 (1 / K)) := fun x hx =>
      (hF_diff_within x hx).continuousWithinAt.mono Icc_subset_Ici_self
    have hline_cont : ContinuousOn (fun s : ℝ => a + s * Δ) (Icc 0 1) :=
      continuousOn_const.add (continuousOn_id.mul continuousOn_const)
    have hmaps : MapsTo (fun s : ℝ => a + s * Δ) (Icc 0 1) (Icc 0 (1 / K)) := fun s hs =>
      ⟨(hseg hs).1, (le_div_iff₀ hK_pos).2 (hseg hs).2⟩
    exact ((hF_cont.comp hline_cont hmaps).sub continuousOn_const).sub
      (continuousOn_id.mul continuousOn_const)
  have hg_der : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt g (Δ * (F'_br (a + s * Δ) - F'_br a)) (Ici s) s := by
    intro s hs
    have hs_cc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    obtain ⟨hx0, hxK⟩ := hseg hs_cc
    have hline : HasDerivWithinAt (fun t : ℝ => a + t * Δ) Δ (Ici s) s := by
      have h := (((hasDerivAt_id s).mul_const Δ).const_add a).hasDerivWithinAt (s := Ici s)
      exact h.congr_deriv (by ring)
    have hF_s : HasDerivWithinAt (fun t => F_br (a + t * Δ)) (F'_br (a + s * Δ) * Δ) (Ici s) s := by
      rcases hx0.eq_or_lt with hx_eq0 | hx_pos
      · -- At `a + s * Δ = 0`: since `a, b ≥ 0` and `a ≠ b`, if `s = 0` then `a = 0` and `b > 0`,
        -- so `a + t * Δ ≥ 0` for `t ≥ 0`! If `s > 0`, `hx_eq0` is impossible because `s < 1` and
        -- `(1 - s) a + s b = 0` forces `a = b = 0`, contradicting `hab_ne`.
        have hmaps_ge : MapsTo (fun t : ℝ => a + t * Δ) (Ici s) (Ici 0) := by
          rcases hs.1.eq_or_lt with rfl | hs_pos
          · simp only [zero_mul, add_zero] at hx_eq0
            subst hx_eq0
            have hb_pos : 0 < b := lt_of_le_of_ne hb0 hab_ne
            intro t ht
            change 0 ≤ 0 + t * (b - 0)
            exact add_nonneg le_rfl (mul_nonneg ht (sub_nonneg.2 hb_pos.le))
          · exfalso
            have hconv : (1 - s) * a + s * b = 0 := by
              calc (1 - s) * a + s * b = a + s * Δ := by dsimp only [Δ]; ring
                _ = 0 := hx_eq0.symm
            have h1s_pos : 0 < 1 - s := sub_pos.2 hs.2
            have ha_z : a = 0 := by nlinarith
            have hb_z : b = 0 := by nlinarith
            exact hab_ne (ha_z.trans hb_z.symm)
        have h0_at : HasDerivWithinAt F_br (F'_br (a + s * Δ)) (Ici 0) (a + s * Δ) := by
          rw [← hx_eq0]; exact hder_zero
        exact h0_at.comp s hline hmaps_ge
      · exact (hder_pos (a + s * Δ) hx_pos (hK_lt₁ _ hx_pos.le hxK)).comp_hasDerivWithinAt s hline
    have hsub1 := hF_s.sub_const (F_br a)
    have hsub2 := hsub1.sub (((hasDerivAt_id s).mul_const (Δ * F'_br a)).hasDerivWithinAt)
    exact hsub2.congr_deriv (by ring)
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (a := 0) (b := 1)
    (B := fun s => D ^ 4 * Δ ^ 2 * s ^ 2 / 2)
    (B' := fun s => D ^ 4 * Δ ^ 2 * s)
    hg_cont hg_der
    (by simp [g])
    (fun s => by
      have h := ((hasDerivAt_pow 2 s).const_mul (D ^ 4 * Δ ^ 2)).div_const 2
      exact h.congr_deriv (by push_cast; ring))
    (fun s hs => by
      have hs_cc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      obtain ⟨hx0, hxK⟩ := hseg hs_cc
      have hx_ub : a + s * Δ ≤ 2 / K := (le_div_iff₀ hK_pos).2 (hxK.trans (by norm_num))
      rw [Real.norm_eq_abs, abs_mul, abs_sub_comm (F'_br (a + s * Δ))]
      calc |Δ| * |F'_br a - F'_br (a + s * Δ)|
          ≤ |Δ| * (D ^ 4 * |a - (a + s * Δ)|) :=
            mul_le_mul_of_nonneg_left (hF'_lip a (a + s * Δ) ha0 haK hx0 hx_ub) (abs_nonneg Δ)
        _ = D ^ 4 * Δ ^ 2 * s := by
            have hdiff : a - (a + s * Δ) = -(s * Δ) := by ring
            rw [hdiff, abs_neg, abs_mul, abs_of_nonneg hs.1]
            have hsq : |Δ| * |Δ| = Δ ^ 2 := by rw [← sq, sq_abs]
            linear_combination D ^ 4 * s * hsq)
    (x := 1) ⟨zero_le_one, le_rfl⟩
  have heval : a + 1 * Δ = b := by dsimp only [Δ]; ring
  rw [Real.norm_eq_abs] at hbound
  dsimp only [g] at hbound
  rw [heval, one_mul] at hbound
  exact hbound.trans_eq (by dsimp only [Δ]; ring)

end VariationalCalculus

end SpinGlasses
