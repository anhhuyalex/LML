/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ReplicaSymmetricFreeEnergy

/-!
# Variational stationary structure and discrete cavity increment (Talagrand Section 2.4)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.87)--(2.92)
and Lemma 2.4.4.

Consider `perceptronRSFunctional u α r q`:
$$F(\alpha, r, q) = -\frac{1}{2}\,r(1 - q) + \mathbb{E}\log\bigl(2\cosh(z\sqrt{r})\bigr) +
  \alpha\,\mathbb{E}\log\mathbb{E}_\xi \exp u\bigl(\sqrt{q}\,z + \sqrt{1 - q}\,\xi\bigr)$$
as a function of three unrelated real variables `α`, `r`, `q`.

## Main declarations

* `SpinGlasses.hasDerivAt_perceptronRSFunctional_r`: for `r > 0`,
  `∂F / ∂r = (1 / 2)(q - 𝔼 tanh²(z √r))`.
* `SpinGlasses.hasDerivAt_perceptronRSFunctional_q`: for `q ∈ (0, 1)`, under `C²` boundedness of
  `u`, `∂F / ∂q = (1 / 2)(r - α r̂(q))` via Gaussian integration by parts.
* `SpinGlasses.deriv_perceptronRSFunctional_eq_zero_iff`: Lemma 2.4.4, characterizing the critical
  conditions `∂F / ∂r = 0` (`r > 0`) and `∂F / ∂q = 0` (`q ∈ (0, 1)`, `α ≠ 0` or general form) as
  the replica-symmetric fixed-point equations (2.87).
* `SpinGlasses.hasDerivAt_perceptronRSFunctional_alpha`: Eq. (2.89), envelope theorem along any
  differentiable critical curve `a ↦ (q a, r a)` with `r α > 0` and `q α ∈ (0, 1)`.
* `SpinGlasses.perceptron_pressure_succ_sub_eq`: Eq. (2.90), exact discrete cavity increment
  `p_{N+1, M+1}(u) - p_{N+1, M}(u) = (N + 1)⁻¹ 𝔼 log ⟨exp u(S_M)⟩`.
* `SpinGlasses.hasDerivAt_second_proof_interpolation`: Eq. (2.91), exact derivative and Gaussian IBP
  identity for `φ(v) = 𝔼 log 𝔼_ξ ⟨exp u(√v S_M + √(1 - v) θ)⟩` on `v ∈ (0, 1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

section VariationalCalculus

/-- **Partial derivative `∂F / ∂r` of `perceptronRSFunctional`:**
for `r > 0`, `r' ↦ F(α, r', q)` has derivative `(1 / 2) * (q - 𝔼 tanh²(z √r))` at `r`. -/
theorem hasDerivAt_perceptronRSFunctional_r (u : ℝ → ℝ) (α : ℝ) {r : ℝ} (hr : 0 < r) (q : ℝ) :
    HasDerivAt (fun r' => perceptronRSFunctional u α r' q)
      ((1 / 2) * (q - ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)) r := by
  have hfun : (fun r' => perceptronRSFunctional u α r' q) =
      fun r' => -(1 / 2) * r' * (1 - q) + Real.log 2 +
        (∫ z : ℝ, Real.log (Real.cosh (1 * Real.sqrt r' * z + 0)) ∂gaussianReal 0 1) +
        α * ∫ z : ℝ, Real.log (∫ ξ : ℝ,
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
          ∂gaussianReal 0 1 := by
    funext r'
    rw [perceptronRSFunctional_eq_log_two_add]
    congr 2
    exact integral_congr_ae (ae_of_all _ fun z => by ring_nf)
  rw [hfun]
  have hd_lin : HasDerivAt (fun r' : ℝ => -(1 / 2) * r' * (1 - q)) (-(1 / 2) * (1 - q)) r := by
    have h1 := ((hasDerivAt_id r).const_mul (-(1 / 2 : ℝ))).mul_const (1 - q)
    exact h1.congr_deriv (by ring)
  have hd_cosh := hasDerivAt_integral_log_cosh_sqrt 1 0 hr
  have hsub : (∫ z : ℝ, (1 - Real.tanh (1 * Real.sqrt r * z + 0) ^ 2) ∂gaussianReal 0 1) =
      1 - ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1 := by
    rw [integral_sub (integrable_const 1) (integrable_tanh_sq_affine (1 * Real.sqrt r) 0),
      integral_const, probReal_univ, one_smul]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => by ring_nf)
  have hd_tot := ((hd_lin.add_const (Real.log 2)).add hd_cosh).add_const
    (α * ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1)
  refine hd_tot.congr_deriv ?_
  rw [hsub]
  ring

/-- **Gaussian expectation of `(z / (2 √q) - ξ / (2 √(1 - q))) u'(θ) e^{u(θ)} / 𝔼_ξ e^{u(θ)}`:**
for `q ∈ (0, 1)`, this equals `-(1 / 2) * perceptronRhat u q` (Talagrand's step after Eq. (2.88),
proved via `stein_tilted_replica_ratio` on `Unit` with `α_sh = √q`, `W_sh = 1 / (2 √q)`,
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
  have hcov_sh : W_sh () ⬝ᵥ α_sh () = 1 / 2 := by
    simp only [W_sh, α_sh, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    field_simp
  have hcov_diag : W_sh () ⬝ᵥ α_sh () + W_aux () ⬝ᵥ α_aux () = 0 := by
    rw [hcov_sh]
    have h2 : W_aux () ⬝ᵥ α_aux () = -(1 / 2) := by
      simp only [W_aux, α_aux, dotProduct, Finset.univ_unique, Finset.sum_singleton]
      field_simp
    rw [h2]; ring
  have hψ_deriv (x : ℝ) :
      HasDerivAt (fun t => deriv u t * Real.exp (u t))
        ((deriv (deriv u) x + deriv u x * deriv u x) * Real.exp (u x)) x := by
    have h1 : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
      (hu.differentiable_deriv x).hasDerivAt
    have h2 : HasDerivAt (fun t => Real.exp (u t)) (Real.exp (u x) * deriv u x) x :=
      (hu.differentiable x).hasDerivAt.exp
    exact (h1.mul h2).congr_deriv (by ring)
  have hst := stein_tilted_replica_ratio (R := Unit) (μ₀ := μ₀)
    (π := (id : Unit → Unit)) measurable_id α_sh W_sh α_aux W_aux
    hu.differentiable hu.abs_le hu.abs_deriv_le
    (fun _ => deriv u)
    (fun _ x => (hψ_deriv x).differentiableAt)
    (M₀ := fun _ => |D₁|) (M' := fun _ => (|D₂| + |D₁| ^ 2) * Real.exp |B|)
    (fun _ x => (hu.abs_deriv_le x).trans (le_abs_self D₁))
    (fun _ x => by
      rw [(hψ_deriv x).deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul ?_ (Real.exp_le_exp.2 ((hu.le x).trans (le_abs_self B)))
        (Real.exp_pos _).le (by positivity)
      refine (abs_add_le _ _).trans (add_le_add
        ((hu.abs_deriv₂_le x).trans (le_abs_self D₂)) ?_)
      rw [abs_mul, sq]
      exact mul_le_mul ((hu.abs_deriv_le x).trans (le_abs_self D₁))
        ((hu.abs_deriv_le x).trans (le_abs_self D₁)) (abs_nonneg _) (abs_nonneg _))
    (fun _ x => deriv (deriv u) x + deriv u x * deriv u x)
    (fun _ x => (hψ_deriv x).deriv)
    () (f := fun _ => (1 : ℝ)) (integrable_const 1)
  dsimp only [id_eq] at hst
  -- Diagonal sum vanishes!
  have hdiag_zero :
      (∑ j : Unit, ∫ w, ∫ σ : Unit → Unit × (Unit → ℝ),
        1 * (W_sh (σ ()).1 ⬝ᵥ α_sh (σ j).1 +
            if () = j then W_aux (σ ()).1 ⬝ᵥ α_aux (σ j).1 else 0) *
          ((deriv (deriv u) (α_sh (σ j).1 ⬝ᵥ w + α_aux (σ j).1 ⬝ᵥ (σ j).2) +
              deriv u (α_sh (σ j).1 ⬝ᵥ w + α_aux (σ j).1 ⬝ᵥ (σ j).2) *
                deriv u (α_sh (σ j).1 ⬝ᵥ w + α_aux (σ j).1 ⬝ᵥ (σ j).2)) *
            ∏ r_u ∈ Finset.univ.erase j,
              deriv u (α_sh (σ r_u).1 ⬝ᵥ w + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
          (fun q_1 => u (α_sh q_1.1 ⬝ᵥ w + α_aux q_1.1 ⬝ᵥ q_1.2))) ∂γ_sh) = 0 := by
    rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
    refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun w => ?_)).trans
      (integral_zero _ ℝ)
    refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun σ => ?_)).trans
      (integral_zero _ ℝ)
    dsimp only
    simp only [↓reduceIte, hcov_diag]
    ring
  rw [hdiag_zero, zero_sub, Fintype.card_unique, Nat.cast_one, one_mul] at hst
  -- Align LHS of `hst` with the desired 1D integral, and RHS with `-(1 / 2) * perceptronRhat u q`!
  let e_u : (Unit → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique Unit ℝ
  have hmp_sh : MeasurePreserving ⇑e_u γ_sh (gaussianReal 0 1) :=
    measurePreserving_funUnique (gaussianReal 0 1) Unit
  let e_q : Unit × (Unit → ℝ) ≃ᵐ ℝ :=
    (MeasurableEquiv.uniqueProd Unit (Unit → ℝ)).trans e_u
  have he_q_apply (y : Unit × (Unit → ℝ)) : e_q y = y.2 () := rfl
  have hmp_q : MeasurePreserving ⇑e_q (μ₀.prod γ_aux) (gaussianReal 0 1) := by
    have h1 : MeasurePreserving (Prod.snd : Unit × (Unit → ℝ) → (Unit → ℝ)) (μ₀.prod γ_aux) γ_aux :=
      measurePreserving_snd
    exact hmp_sh.comp h1
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
  -- Align LHS of `hst`:
  let L_1d (z : ℝ) : ℝ :=
    ∫ ξ : ℝ, (z / (2 * Real.sqrt q) - ξ / (2 * Real.sqrt (1 - q))) *
      deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)
      ∂((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))
  have hL_m : Measurable L_1d := by
    apply measurable_integral_tilted_dep
    · exact hu.measurable.comp (by fun_prop)
    · exact ((measurable_fst.div_const _).sub (measurable_snd.div_const _)).mul
        ((measurable_deriv u).comp (by fun_prop))
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
      ((measurable_const.sub (measurable_id.div_const _)).mul
        ((measurable_deriv u).comp (by fun_prop)))
    have h1 := (integral_pi_map_equiv ν_w e_q (fun f_u : Unit → ℝ => g_ξ (f_u ()))).symm
    rw [htilted_w w] at h1
    have hprob_t : IsProbabilityMeasure
        ((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ)) :=
      isProbabilityMeasure_tilted
        (integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q (w ()))
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
  -- Align RHS of `hst`:
  let R_1d (z : ℝ) : ℝ :=
    (∫ ξ : ℝ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)
      ∂((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ^ 2
  have hR_m : Measurable R_1d := by
    apply Measurable.pow_const
    apply measurable_integral_tilted_dep
    · exact hu.measurable.comp (by fun_prop)
    · exact (measurable_deriv u).comp (by fun_prop)
  have hrhs_w (w : Unit → ℝ) :
      (∫ σ : Option Unit → Unit × (Unit → ℝ),
        (1 * W_sh (σ (some ())).1 ⬝ᵥ α_sh (σ none).1 *
            ∏ r_u : Unit,
              deriv u (α_sh (σ (some r_u)).1 ⬝ᵥ w + α_aux (σ (some r_u)).1 ⬝ᵥ (σ (some r_u)).2)) *
          deriv u (α_sh (σ none).1 ⬝ᵥ w + α_aux (σ none).1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2)))) =
      (1 / 2) * R_1d (w ()) := by
    let ν_w := (μ₀.prod γ_aux).tilted (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))
    have hVm : Measurable fun y : Unit × (Unit → ℝ) => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2) := by
      simp only [α_sh, α_aux, dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact hu.measurable.comp
        (measurable_const.add (measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)))
    have hprob_w : IsProbabilityMeasure ν_w :=
      isProbabilityMeasure_tilted_of_ae_le hVm.aemeasurable (ae_of_all _ fun _ => hu.le _)
    have hprob_t : IsProbabilityMeasure
        ((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ)) :=
      isProbabilityMeasure_tilted
        (integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q (w ()))
    let h_ξ (ξ : ℝ) : ℝ := deriv u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ)
    have hh_m : Measurable h_ξ := (measurable_deriv u).comp (by fun_prop)
    have h1 := (integral_pi_map_equiv ν_w e_q
      (fun τ : Option Unit → ℝ => (1 / 2) * (h_ξ (τ (some ())) * h_ξ (τ none)))).symm
    rw [htilted_w w] at h1
    have h2 : (∫ τ : Option Unit → ℝ, (1 / 2) * (h_ξ (τ (some ())) * h_ξ (τ none))
        ∂(Measure.pi fun _ : Option Unit =>
          (gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * w () + Real.sqrt (1 - q) * ξ))) =
        (1 / 2) * R_1d (w ()) := by
      rw [integral_const_mul,
        integral_pi_mul_of_ne _ (by decide : (some () : Option Unit) ≠ none) hh_m hh_m, ← sq]
    refine (integral_congr_ae (ae_of_all _ fun σ => ?_)).trans (h1.trans h2)
    dsimp only [h_ξ]
    rw [he_q_apply, he_q_apply]
    simp only [show (Finset.univ : Finset Unit) = {()} from rfl,
      Finset.prod_singleton, W_sh, α_sh, α_aux, dotProduct, Finset.sum_singleton]
    field_simp
  have hrhs_eq :
      -(∫ w, ∫ σ : Option Unit → Unit × (Unit → ℝ),
        (1 * W_sh (σ (some ())).1 ⬝ᵥ α_sh (σ none).1 *
            ∏ r_u : Unit,
              deriv u (α_sh (σ (some r_u)).1 ⬝ᵥ w + α_aux (σ (some r_u)).1 ⬝ᵥ (σ (some r_u)).2)) *
          deriv u (α_sh (σ none).1 ⬝ᵥ w + α_aux (σ none).1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))) ∂γ_sh) =
      -(1 / 2) * perceptronRhat u q := by
    simp_rw [hrhs_w]
    have hcomp_R : (∫ w : Unit → ℝ, R_1d (w ()) ∂γ_sh) = ∫ z, R_1d z ∂gaussianReal 0 1 :=
      hmp_sh.integral_comp_of_aestronglyMeasurable (g := R_1d) hR_m.aestronglyMeasurable
    rw [integral_const_mul, hcomp_R, perceptronRhat_eq_integral_sq_integral_tilted]
    dsimp only [R_1d]
    ring
  rw [hlhs_eq, hrhs_eq] at hst
  exact hst

/-- **Partial derivative `∂F / ∂q` of `perceptronRSFunctional` (Eq. (2.88) + Gaussian IBP):**
for `q ∈ (0, 1)` and `u` satisfying `SmartPathPotential₂`, `q' ↦ F(α, r, q')` has derivative
`(1 / 2) * (r - α * perceptronRhat u q)` at `q`. -/
theorem hasDerivAt_perceptronRSFunctional_q
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (α r : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q' => perceptronRSFunctional u α r q')
      ((1 / 2) * (r - α * perceptronRhat u q)) q := by
  let γ : Measure ℝ := gaussianReal 0 1
  let δ : ℝ := min (q / 2) ((1 - q) / 2)
  have hδ : 0 < δ := lt_min (half_pos hq.1) (half_pos (sub_pos.2 hq.2))
  let U_nbhd : Set ℝ := Ioo (q - δ) (q + δ)
  have hU_nhds : U_nbhd ∈ 𝓝 q := Ioo_mem_nhds (by linarith) (by linarith)
  have hq'_b {q' : ℝ} (hq' : q' ∈ U_nbhd) : δ ≤ q' ∧ δ ≤ 1 - q' ∧ 0 < q' ∧ q' < 1 := by
    have h1 : δ ≤ q / 2 := min_le_left _ _
    have h2 : δ ≤ (1 - q) / 2 := min_le_right _ _
    refine ⟨by linarith [hq'.1], by linarith [hq'.2], by linarith [hq'.1], by linarith [hq'.2]⟩
  -- Differentiate `q' ↦ log (∫ ξ, exp (u (√q' z + √(1 - q') ξ)) ∂γ)` at fixed `z`, then integrate!
  let Z_q (q' z : ℝ) : ℝ :=
    ∫ ξ : ℝ, Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂γ
  let L_q (q' z : ℝ) : ℝ :=
    ∫ ξ : ℝ, (z / (2 * Real.sqrt q') - ξ / (2 * Real.sqrt (1 - q'))) *
      deriv u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)
      ∂(γ.tilted fun ξ => u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ))
  have hZq_deriv (z : ℝ) {q' : ℝ} (hq' : q' ∈ U_nbhd) :
      HasDerivAt (fun t => Real.log (Z_q t z)) (L_q q' z) q' := by
    have hpt_ξ (ξ : ℝ) {t : ℝ} (ht : t ∈ U_nbhd) :
        HasDerivAt (fun s => Real.exp (u (Real.sqrt s * z + Real.sqrt (1 - s) * ξ)))
          (((z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
            deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)) *
            Real.exp (u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ))) t := by
      obtain ⟨-, -, ht0, ht1⟩ := hq'_b ht
      have h1 : HasDerivAt (fun s => Real.sqrt s * z) ((1 / (2 * Real.sqrt t)) * z) t :=
        (Real.hasDerivAt_sqrt ht0.ne').mul_const z
      have h2 : HasDerivAt (fun s => Real.sqrt (1 - s) * ξ)
          ((-(1 / (2 * Real.sqrt (1 - t)))) * ξ) t := by
        have hsub : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub 1
        have hsq := (Real.hasDerivAt_sqrt (sub_pos.2 ht1).ne').comp t hsub
        exact (hsq.mul_const ξ).congr_deriv (by ring)
      have hθ : HasDerivAt (fun s => Real.sqrt s * z + Real.sqrt (1 - s) * ξ)
          (z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) t :=
        (h1.add h2).congr_deriv (by ring)
      have hu_d := ((hu.differentiable _).hasDerivAt.comp t hθ).exp
      exact hu_d.congr_deriv (by dsimp only [Function.comp_apply]; ring)
    have hinv_bd {t : ℝ} (ht : t ∈ U_nbhd) :
        1 / (2 * Real.sqrt t) ≤ 1 / (2 * Real.sqrt δ) ∧
          1 / (2 * Real.sqrt (1 - t)) ≤ 1 / (2 * Real.sqrt δ) := by
      obtain ⟨hd_t, hd_1t, -, -⟩ := hq'_b ht
      have hpos : 0 < 2 * Real.sqrt δ := by positivity
      exact ⟨one_div_le_one_div_of_le hpos
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd_t) zero_le_two),
        one_div_le_one_div_of_le hpos
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd_1t) zero_le_two)⟩
    let dom_ξ (ξ : ℝ) : ℝ :=
      (|D₁| * ((|z| + |ξ|) / (2 * Real.sqrt δ))) * Real.exp |B|
    have hdom_ξ_i : Integrable dom_ξ γ :=
      ((((integrable_const |z|).add IsGaussian.integrable_id.abs).div_const _).const_mul
        |D₁|).mul_const _
    have hm_ev : ∀ᶠ t in 𝓝 q',
        AEStronglyMeasurable (fun ξ => Real.exp (u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ))) γ :=
      Eventually.of_forall fun t =>
        (Real.measurable_exp.comp (hu.measurable.comp (by fun_prop))).aestronglyMeasurable
    have hi_q' : Integrable (fun ξ => Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ))) γ :=
      integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q' z
    have hdm_q' : AEStronglyMeasurable
        (fun ξ => ((z / (2 * Real.sqrt q') - ξ / (2 * Real.sqrt (1 - q'))) *
          deriv u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) *
          Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ))) γ :=
      ((((measurable_const.sub (measurable_id.div_const _)).mul
        ((measurable_deriv u).comp (by fun_prop))).mul
        (Real.measurable_exp.comp (hu.measurable.comp (by fun_prop))))).aestronglyMeasurable
    have hZd : HasDerivAt (fun t => Z_q t z)
        (∫ ξ, ((z / (2 * Real.sqrt q') - ξ / (2 * Real.sqrt (1 - q'))) *
          deriv u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) *
          Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂γ) q' :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ)
        (F := fun t ξ => Real.exp (u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)))
        (F' := fun t ξ => ((z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
          deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)) *
          Real.exp (u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)))
        (s := U_nbhd) (bound := dom_ξ)
        (IsOpen.mem_nhds isOpen_Ioo hq') hm_ev hi_q' hdm_q'
        (ae_of_all _ fun ξ t ht => by
          obtain ⟨hi1, hi2⟩ := hinv_bd ht
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
            mul_comm _ |deriv u _|]
          refine mul_le_mul ?_ (Real.exp_le_exp.2 ((hu.le _).trans (le_abs_self B)))
            (Real.exp_pos _).le (by positivity)
          refine mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self D₁)) ?_
            (abs_nonneg _) (abs_nonneg D₁)
          have hsub_le := (abs_sub (z / (2 * Real.sqrt t)) (ξ / (2 * Real.sqrt (1 - t))))
          obtain ⟨-, -, ht0, ht1⟩ := hq'_b ht
          rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt t),
            abs_of_pos (by positivity : 0 < 2 * Real.sqrt (1 - t))] at hsub_le
          have hz_le : |z| / (2 * Real.sqrt t) ≤ |z| / (2 * Real.sqrt δ) := by
            simpa only [div_eq_mul_inv, one_div, one_mul] using
              mul_le_mul_of_nonneg_left hi1 (abs_nonneg z)
          have hξ_le : |ξ| / (2 * Real.sqrt (1 - t)) ≤ |ξ| / (2 * Real.sqrt δ) := by
            simpa only [div_eq_mul_inv, one_div, one_mul] using
              mul_le_mul_of_nonneg_left hi2 (abs_nonneg ξ)
          calc |z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))|
              ≤ |z| / (2 * Real.sqrt δ) + |ξ| / (2 * Real.sqrt δ) :=
                hsub_le.trans (add_le_add hz_le hξ_le)
            _ = (|z| + |ξ|) / (2 * Real.sqrt δ) := by ring)
        hdom_ξ_i
        (ae_of_all _ fun ξ t ht => hpt_ξ ξ ht)).2
    have hZ_pos : 0 < Z_q q' z := integral_exp_pos hi_q'
    exact (hZd.log hZ_pos.ne').congr_deriv
      (by dsimp only [L_q, Z_q]; rw [integral_tilted_eq_div, div_eq_mul_inv, mul_comm])
  -- Bound `|L_q t z|` uniformly on `t ∈ U_nbhd` by an integrable function of `z`!
  let dom_z (z : ℝ) : ℝ :=
    |D₁| * (|z| / (2 * Real.sqrt δ) +
      Real.exp (2 * |B|) * ((∫ ξ : ℝ, |ξ| ∂γ) / (2 * Real.sqrt δ)))
  have hdom_z_i : Integrable dom_z γ :=
    ((IsGaussian.integrable_id.abs.div_const _).add (integrable_const _)).const_mul |D₁|
  have hLq_bd (z : ℝ) {t : ℝ} (ht : t ∈ U_nbhd) : |L_q t z| ≤ dom_z z := by
    obtain ⟨hd_t, hd_1t, ht0, ht1⟩ := hq'_b ht
    have hpos : 0 < 2 * Real.sqrt δ := by positivity
    have hi1 : 1 / (2 * Real.sqrt t) ≤ 1 / (2 * Real.sqrt δ) :=
      one_div_le_one_div_of_le hpos (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd_t) zero_le_two)
    have hi2 : 1 / (2 * Real.sqrt (1 - t)) ≤ 1 / (2 * Real.sqrt δ) :=
      one_div_le_one_div_of_le hpos
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd_1t) zero_le_two)
    let V_t (ξ : ℝ) : ℝ := u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)
    have hVt_m : Measurable V_t := hu.measurable.comp (by fun_prop)
    have hprob_t : IsProbabilityMeasure (γ.tilted V_t) :=
      isProbabilityMeasure_tilted
        (integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) t z)
    have hξ_tilted : Integrable (fun ξ : ℝ => |ξ|) (γ.tilted V_t) :=
      integrable_tilted_of_ae_le hVt_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
        IsGaussian.integrable_id.abs
    have hpt_L (ξ : ℝ) :
        |(z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
          deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)| ≤
        |D₁| * (|z| / (2 * Real.sqrt δ) + |ξ| / (2 * Real.sqrt δ)) := by
      rw [abs_mul, mul_comm _ |deriv u _|]
      refine mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self D₁)) ?_
        (abs_nonneg _) (abs_nonneg D₁)
      have hsub_le := abs_sub (z / (2 * Real.sqrt t)) (ξ / (2 * Real.sqrt (1 - t)))
      rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt t),
        abs_of_pos (by positivity : 0 < 2 * Real.sqrt (1 - t))] at hsub_le
      have hz_le : |z| / (2 * Real.sqrt t) ≤ |z| / (2 * Real.sqrt δ) := by
        simpa only [div_eq_mul_inv, one_div, one_mul] using
          mul_le_mul_of_nonneg_left hi1 (abs_nonneg z)
      have hξ_le : |ξ| / (2 * Real.sqrt (1 - t)) ≤ |ξ| / (2 * Real.sqrt δ) := by
        simpa only [div_eq_mul_inv, one_div, one_mul] using
          mul_le_mul_of_nonneg_left hi2 (abs_nonneg ξ)
      exact hsub_le.trans (add_le_add hz_le hξ_le)
    have hint_L : Integrable
        (fun ξ => (z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
          deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ)) (γ.tilted V_t) := by
      have hm : Measurable fun ξ : ℝ =>
          (z / (2 * Real.sqrt t) - ξ / (2 * Real.sqrt (1 - t))) *
            deriv u (Real.sqrt t * z + Real.sqrt (1 - t) * ξ) :=
        (measurable_const.sub (measurable_id.div_const _)).mul
          ((measurable_deriv u).comp (by fun_prop))
      exact (((integrable_const _).add (hξ_tilted.div_const _)).const_mul |D₁|).mono'
        hm.aestronglyMeasurable (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs]; exact hpt_L ξ)
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
    -- Bound `∫ ξ, |ξ| ∂(γ.tilted V_t) ≤ exp(2 |B|) * ∫ ξ, |ξ| ∂γ`!
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
  -- Differentiate `q' ↦ ∫ z, log (Z_q q' z) ∂γ` at `q`!
  have hlogZ_int (t : ℝ) : Integrable (fun z => Real.log (Z_q t z)) γ := by
    have hm : Measurable fun z => Real.log (Z_q t z) := by
      refine Real.measurable_log.comp ?_
      have hj : Measurable fun p : ℝ × ℝ =>
          Real.exp (u (Real.sqrt t * p.1 + Real.sqrt (1 - t) * p.2)) :=
        Real.measurable_exp.comp (hu.measurable.comp (by fun_prop))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
    exact Integrable.of_bound hm.aestronglyMeasurable |B| (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact (abs_log_integral_exp_le_of_ae_abs_le (hu.measurable.comp (by fun_prop)).aemeasurable
        (ae_of_all _ fun _ => hu.abs_le _)).trans (le_abs_self B))
  have hLq_m : AEStronglyMeasurable (L_q q) γ := by
    apply Measurable.aestronglyMeasurable
    apply measurable_integral_tilted_dep
    · exact hu.measurable.comp (by fun_prop)
    · exact ((measurable_fst.div_const _).sub (measurable_snd.div_const _)).mul
        ((measurable_deriv u).comp (by fun_prop))
  have hd_pot : HasDerivAt (fun q' => ∫ z, Real.log (Z_q q' z) ∂γ) (∫ z, L_q q z ∂γ) q :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ)
      (F := fun t z => Real.log (Z_q t z)) (F' := L_q) (s := U_nbhd) (bound := dom_z)
      hU_nhds (Eventually.of_forall fun t => (hlogZ_int t).aestronglyMeasurable)
      (hlogZ_int q) hLq_m
      (ae_of_all _ fun z t ht => by rw [Real.norm_eq_abs]; exact hLq_bd z ht)
      hdom_z_i (ae_of_all _ fun z t ht => hZq_deriv z ht)).2
  have hibp := integral_theta_deriv_tilted_eq_neg_half_rhat hu hq
  change ∫ z, L_q q z ∂γ = -(1 / 2) * perceptronRhat u q at hibp
  rw [hibp] at hd_pot
  -- Combine with `-(1 / 2) * r * (1 - q') + const`!
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

/-- **Talagrand Section 2.4, Eq. (2.89) (envelope theorem along the critical curve):**
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
  -- Decompose `perceptronRSFunctional u a (r a) (q a)` into:
  -- `g₁(a) = -(1 / 2) * r a * (1 - q a) + ∫ z, log(2 cosh(z √(r a)))`
  -- `g₂(a) = a * ψ(q a)` where `ψ(q') = ∫ z, log ∫ ξ, exp u(√q' z + √(1 - q') ξ)`!
  let ψ (q' : ℝ) : ℝ :=
    ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q' * z + Real.sqrt (1 - q') * ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1
  -- Extract `HasDerivAt ψ (-(1 / 2) * perceptronRhat u (q α)) (q α)` from `α = 1, r = 0`!
  have hd_F1 := hasDerivAt_perceptronRSFunctional_q hu 1 0 hq_mem
  have hψ_eq : (fun q' => perceptronRSFunctional u 1 0 q') =
      fun q' => (∫ z : ℝ, Real.log (2 * Real.cosh 0) ∂gaussianReal 0 1) + ψ q' := by
    funext q'
    unfold perceptronRSFunctional
    simp [ψ]
  rw [hψ_eq] at hd_F1
  have hd_ψ : HasDerivAt ψ (-(1 / 2) * perceptronRhat u (q α)) (q α) := by
    have h1 := (hd_F1.sub_const (∫ z : ℝ, Real.log (2 * Real.cosh 0) ∂gaussianReal 0 1))
    have hfun : (fun x => (∫ z : ℝ, Real.log (2 * Real.cosh 0) ∂gaussianReal 0 1) + ψ x -
        ∫ z : ℝ, Real.log (2 * Real.cosh 0) ∂gaussianReal 0 1) = ψ := by
      funext x; ring
    rw [hfun] at h1
    exact h1.congr_deriv (by ring)
  -- Extract `HasDerivAt (fun r' => ∫ z, log(2 cosh(z √r'))) ... (r α)` from `α = 0, q = 1`!
  have hd_Fr := hasDerivAt_perceptronRSFunctional_r u 0 hr_pos 1
  have hcosh_eq : (fun r' => perceptronRSFunctional u 0 r' 1) =
      fun r' => ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r')) ∂gaussianReal 0 1 := by
    funext r'
    unfold perceptronRSFunctional
    simp
  rw [hcosh_eq] at hd_Fr
  -- Chain rule on `a ↦ F(a, r a, q a)`:
  have hd_term1 : HasDerivAt (fun a => -(1 / 2) * r a * (1 - q a))
      ((-(1 / 2) * deriv r α) * (1 - q α) + (-(1 / 2) * r α) * (-deriv q α)) α := by
    have hr_a := hr_diff.hasDerivAt
    have h1q_a : HasDerivAt (fun a => 1 - q a) (-deriv q α) α := by
      simpa using hq_diff.hasDerivAt.const_sub 1
    exact (hr_a.const_mul (-(1 / 2 : ℝ))).mul h1q_a
  have hd_term2 : HasDerivAt
      (fun a => ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt (r a))) ∂gaussianReal 0 1)
      (((1 / 2) * (1 - ∫ z : ℝ, Real.tanh (z * Real.sqrt (r α)) ^ 2 ∂gaussianReal 0 1)) *
        deriv r α) α :=
    hd_Fr.comp α hr_diff.hasDerivAt
  have hd_term3 : HasDerivAt (fun a => a * ψ (q a))
      (1 * ψ (q α) + α * ((-(1 / 2) * perceptronRhat u (q α)) * deriv q α)) α :=
    (hasDerivAt_id α).mul (hd_ψ.comp α hq_diff.hasDerivAt)
  have hd_all := (hd_term1.add hd_term2).add hd_term3
  have hF_fun : (fun a => perceptronRSFunctional u a (r a) (q a)) =
      fun a => -(1 / 2) * r a * (1 - q a) +
        (∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt (r a))) ∂gaussianReal 0 1) +
        a * ψ (q a) := by
    funext a; rfl
  have hF_fun' : (((fun a => -(1 / 2) * r a * (1 - q a)) +
      fun a => ∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt (r a))) ∂gaussianReal 0 1) +
      fun a => a * ψ (q a)) = fun a => perceptronRSFunctional u a (r a) (q a) := by
    funext a; rfl
  rw [hF_fun'] at hd_all
  refine hd_all.congr_deriv ?_
  rw [← hq_crit, hr_crit]
  dsimp only [ψ]
  ring

end VariationalCalculus

section SecondProofIncrement

/-- **Talagrand Section 2.4, Eq. (2.90) (discrete cavity increment of the perceptron pressure):**
`p_{N+1, M+1}(u) - p_{N+1, M}(u) = (N + 1)⁻¹ 𝔼 log ⟨exp u(S_M)⟩`, where `⟨·⟩` is the `M`-constraint
quenched Gibbs measure on `Fin (N + 1) → ℤˣ` and `S_M(τ) = (√(N + 1))⁻¹ ∑ᵢ g_{M, i} τᵢ` is the
fresh constraint field. -/
theorem perceptron_pressure_succ_sub_eq
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) (hi : Integrable u (gaussianReal 0 1)) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let P_M1 := Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ
    let γ_row := Measure.pi fun _ : Fin (N + 1) => γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let p_M1 : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g : Fin (M + 1) → Fin (N + 1) → ℝ,
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin (M + 1),
          u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ∂P_M1
    let p_M : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g₀ : Fin M → Fin (N + 1) → ℝ,
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin M,
          u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))) ∂P_M
    p_M1 - p_M =
      ((N : ℝ) + 1)⁻¹ * ∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ),
        Real.log (∫ τ : Fin (N + 1) → ℤˣ,
          Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))
          ∂(μ_M p.1)) ∂(P_M.prod γ_row) := by
  intro γ P_M P_M1 γ_row μ_M p_M1 p_M
  let Z_M (g₀ : Fin M → Fin (N + 1) → ℝ) : ℝ :=
    ∑ τ : Fin (N + 1) → ℤˣ,
      Real.exp (∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
  let R_inc (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ τ : Fin (N + 1) → ℤˣ,
      Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ))) ∂(μ_M p.1)
  have hZM_pos (g₀ : Fin M → Fin (N + 1) → ℝ) : 0 < Z_M g₀ :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hR_eq (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :
      R_inc p =
        (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp ((∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1 k i * ((τ i : ℤ) : ℝ))) +
            u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))) / Z_M p.1 := by
    dsimp only [R_inc, μ_M, Z_M]
    rw [integral_tilted_eq_div, integral_fintype Integrable.of_finite,
      integral_fintype Integrable.of_finite]
    simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Real.exp_add, mul_comm]
  have hR_pos (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) : 0 < R_inc p := by
    rw [hR_eq p]
    exact div_pos (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty) (hZM_pos p.1)
  have hmp := measurePreserving_finSuccProd γ_row M
  let F_M1 (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) : ℝ :=
    Real.log (Z_M p.1) + Real.log (R_inc p)
  have hZM_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (Z_M p.1) := by
    refine Real.measurable_log.comp (Finset.measurable_sum _ fun τ _ => Real.measurable_exp.comp ?_)
    refine Finset.measurable_sum _ fun k _ => hu.comp ?_
    refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
    exact ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_fst)).mul_const _
  have hR_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (R_inc p) := by
    have heq : (fun p => Real.log (R_inc p)) = fun p =>
        Real.log ((∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp ((∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1 k i * ((τ i : ℤ) : ℝ))) +
            u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))) / Z_M p.1) :=
      funext fun p => congrArg Real.log (hR_eq p)
    rw [heq]
    refine Real.measurable_log.comp (Measurable.div ?_ ?_)
    · refine Finset.measurable_sum _ fun τ _ => Real.measurable_exp.comp (Measurable.add ?_ ?_)
      · refine Finset.measurable_sum _ fun k _ => hu.comp ?_
        refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
        exact ((measurable_pi_apply i).comp
          ((measurable_pi_apply k).comp measurable_fst)).mul_const _
      · refine hu.comp ((Finset.measurable_sum _ fun i _ => ?_).const_mul _)
        exact ((measurable_pi_apply i).comp measurable_snd).mul_const _
    · refine Finset.measurable_sum _ fun τ _ => Real.measurable_exp.comp ?_
      refine Finset.measurable_sum _ fun k _ => hu.comp ?_
      refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
      exact ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_fst)).mul_const _
  have hp_M1_eq :
      (∫ g : Fin (M + 1) → Fin (N + 1) → ℝ,
        Real.log (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ k : Fin (M + 1),
            u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ∂P_M1) =
      ∫ p, F_M1 p ∂(P_M.prod γ_row) := by
    have hcomp := hmp.integral_comp_of_aestronglyMeasurable (g := F_M1)
      (hZM_m.add hR_m).aestronglyMeasurable
    refine (integral_congr_ae (ae_of_all _ fun g => ?_)).trans hcomp
    dsimp only [F_M1, Function.comp_apply]
    rw [← Real.log_mul (hZM_pos _).ne' (hR_pos _).ne', hR_eq,
      mul_div_cancel₀ _ (hZM_pos _).ne']
    congr 1
    refine Finset.sum_congr rfl fun τ _ => congrArg Real.exp ?_
    rw [Fin.sum_univ_castSucc]
    simp [MeasurableEquiv.finSuccProd_apply]
  let H (g : Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g i * ((τ i : ℤ) : ℝ)
  have hH_m (τ : Fin (N + 1) → ℤˣ) : Measurable fun g => H g τ := by
    dsimp only [H]
    fun_prop
  have hH_i (τ : Fin (N + 1) → ℤˣ) : Integrable (fun g => u (H g τ)) γ_row := by
    have hm : Measure.map (fun g => H g τ) γ_row = gaussianReal 0 1 :=
      map_normalized_constraint_field_eq_gaussianReal (Nat.succ_pos N) τ
    have hm_i : Integrable u (Measure.map (fun g => H g τ) γ_row) := by
      rw [hm]
      exact hi
    exact hm_i.comp_measurable (hH_m τ)
  let pEnergy (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))
      (τ : Fin (N + 1) → ℤˣ) : ℝ := ∑ k : Fin M, u (H (p.1 k) τ)
  have hE_m (τ : Fin (N + 1) → ℤˣ) : Measurable fun p => pEnergy p τ :=
    Finset.measurable_sum _ fun k _ => ((hu.comp (hH_m τ)).comp
      ((measurable_pi_apply k).comp measurable_fst))
  have hE_i (τ : Fin (N + 1) → ℤˣ) :
      Integrable (fun p => pEnergy p τ) (P_M.prod γ_row) :=
    integrable_finsetSum _ fun k _ =>
      (integrable_comp_eval (μ := fun _ : Fin M => γ_row) (i := k) (hH_i τ)).comp_fst γ_row
  have hZM_int : Integrable (fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (Z_M p.1)) (P_M.prod γ_row) := by
    simpa only [one_mul] using
      integrable_log_sum_exp (μ := P_M.prod γ_row) (H := pEnergy)
        (β := 1) one_pos hE_m hE_i
  have hR_int : Integrable (fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (R_inc p)) (P_M.prod γ_row) := by
    have hNew := integrable_log_sum_exp (μ := P_M.prod γ_row)
      (H := fun p τ => pEnergy p τ + u (H p.2 τ)) (β := 1) one_pos
      (fun τ => (hE_m τ).add ((hu.comp (hH_m τ)).comp measurable_snd))
      (fun τ => (hE_i τ).add ((hH_i τ).comp_snd P_M))
    simp only [one_mul] at hNew
    refine (hNew.sub hZM_int).congr (ae_of_all _ fun p => ?_)
    change Real.log (∑ τ, Real.exp (pEnergy p τ + u (H p.2 τ))) -
      Real.log (Z_M p.1) = Real.log (R_inc p)
    rw [hR_eq p, Real.log_div _ (hZM_pos p.1).ne']
    exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  have hZM_fst :
      (∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ), Real.log (Z_M p.1)
        ∂(P_M.prod γ_row)) =
      ∫ g₀ : Fin M → Fin (N + 1) → ℝ, Real.log (Z_M g₀) ∂P_M :=
    integral_prod_fun_fst_of_isProbabilityMeasure P_M γ_row (fun g₀ => Real.log (Z_M g₀))
  dsimp only [p_M1, p_M]
  rw [hp_M1_eq, integral_add hZM_int hR_int, hZM_fst]
  dsimp only [Z_M, R_inc]
  ring

/-- **Talagrand Section 2.4, Eq. (2.91) (first derivative and Gaussian IBP of the second proof's
cavity interpolation `φ(v)`):**
For `v ∈ (0, 1)`, `q ∈ [0, 1]`, and `u` satisfying `SmartPathPotential₂`, define
`φ(v) = 𝔼 log ∫_ξ ⟨exp u(√v S_M(τ) + √(1 - v)(√q z + √(1 - q) ξ))⟩ dγ(ξ)`, where the outer
expectation is over `(g₀, g_M, z)` and `⟨·⟩` is the `M`-constraint quenched Gibbs measure `μ_M g₀`.
Then `φ` is differentiable at `v` with derivative
$$-\frac{1}{2}\,\mathbb{E}\left[
  \int_{(\Sigma_{N+1} \times \mathbb{R})^2}
    (R_{1, 2} - q)\,u'(S_v^1)\,u'(S_v^2)\,
    \mathrm{d}\bigl((\mu_M(g_0) \otimes \gamma).\mathrm{tilted}(u \circ S_v)\bigr)^{\otimes 2}
\right].$$ -/
theorem hasDerivAt_second_proof_interpolation
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let P_ext := (P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ)).prod γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let S_v (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      Real.sqrt v' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - v') * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    HasDerivAt
      (fun v' => ∫ ω, Real.log (∫ x, Real.exp (u (S_v v' ω x)) ∂((μ_M ω.1.1).prod γ)) ∂P_ext)
      (-(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
        ∂P_ext) v := by
  -- Express `φ(v')` via `(N + 1) * (p_{N+1, 1, v'}(u) at r = 0)` on the conditional base `μ_M g₀`!
  -- Better yet: differentiate directly on `U_nbhd ⊆ Ioo 0 1` and apply `stein_tilted_replica_ratio`
  -- at fixed `g₀`!
  intro γ P_M P_ext μ_M S_v
  let S'_v (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
    (1 / (2 * Real.sqrt v')) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) -
      (1 / (2 * Real.sqrt (1 - v'))) * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
  let δ : ℝ := min (v / 2) ((1 - v) / 2)
  have hδ : 0 < δ := lt_min (half_pos hv.1) (half_pos (sub_pos.2 hv.2))
  let U_nbhd : Set ℝ := Ioo (v - δ) (v + δ)
  have hU_nhds : U_nbhd ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  have hv'_b {v' : ℝ} (hv' : v' ∈ U_nbhd) : δ ≤ v' ∧ δ ≤ 1 - v' ∧ 0 < v' ∧ v' < 1 := by
    have h1 : δ ≤ v / 2 := min_le_left _ _
    have h2 : δ ≤ (1 - v) / 2 := min_le_right _ _
    refine ⟨by linarith [hv'.1], by linarith [hv'.2], by linarith [hv'.1], by linarith [hv'.2]⟩
  have hμM_prob (g₀ : Fin M → Fin (N + 1) → ℝ) : IsProbabilityMeasure (μ_M g₀) :=
    isProbabilityMeasure_tilted Integrable.of_finite
  -- Step 1: Differentiate `v' ↦ ∫ ω, log ∫ x, exp (u (S_v v' ω x))` at `v`!
  let Z_fn (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
    ∫ x, Real.exp (u (S_v v' ω x)) ∂((μ_M ω.1.1).prod γ)
  let F'_fn (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
    ∫ x, (S'_v v' ω x * deriv u (S_v v' ω x))
      ∂(((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v' ω x)))
  have hSv_m (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S_v v' ω x := by
    have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
        ∑ i : Fin (N + 1), ω.1.2 i * ((x.1 i : ℤ) : ℝ) :=
      Finset.measurable_sum _ fun i _ =>
        measurable_const.mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))
    exact ((h1.const_mul _).const_mul _).add
      ((measurable_const.add (measurable_snd.const_mul _)).const_mul _)
  have hS'v_m (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S'_v v' ω x := by
    have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
        ∑ i : Fin (N + 1), ω.1.2 i * ((x.1 i : ℤ) : ℝ) :=
      Finset.measurable_sum _ fun i _ =>
        measurable_const.mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))
    exact ((h1.const_mul _).const_mul _).sub
      ((measurable_const.add (measurable_snd.const_mul _)).const_mul _)
  let b_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
    |D₁| * ((1 / (2 * Real.sqrt δ)) *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.2 i|) + Real.sqrt q * |ω.2|))
  let c_ξ : ℝ := |D₁| * ((1 / (2 * Real.sqrt δ)) * Real.sqrt (1 - q))
  have hb_ω0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : 0 ≤ b_ω ω := by
    dsimp only [b_ω]; positivity
  have hc_ξ0 : 0 ≤ c_ξ := by dsimp only [c_ξ]; positivity
  have hpt_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (x : (Fin (N + 1) → ℤˣ) × ℝ) {t : ℝ} (ht : t ∈ U_nbhd) :
      |S'_v t ω x * deriv u (S_v t ω x)| ≤ b_ω ω + c_ξ * |x.2| := by
    obtain ⟨hd_t, hd_1t, ht0, ht1⟩ := hv'_b ht
    have hpos : 0 < 2 * Real.sqrt δ := by positivity
    have hi1 : 1 / (2 * Real.sqrt t) ≤ 1 / (2 * Real.sqrt δ) :=
      one_div_le_one_div_of_le hpos (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd_t) zero_le_two)
    have hi2 : 1 / (2 * Real.sqrt (1 - t)) ≤ 1 / (2 * Real.sqrt δ) :=
      one_div_le_one_div_of_le hpos
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd_1t) zero_le_two)
    rw [abs_mul, mul_comm _ |deriv u _|]
    have hS'_le : |S'_v t ω x| ≤
        (1 / (2 * Real.sqrt δ)) *
          (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.2 i|) +
            Real.sqrt q * |ω.2|) + Real.sqrt (1 - q) * |x.2|) := by
      dsimp only [S'_v]
      refine (abs_sub _ _).trans ?_
      have hs1 : |(1 / (2 * Real.sqrt t)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ))| ≤
          (1 / (2 * Real.sqrt δ)) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, |ω.1.2 i|) := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt t)),
          abs_mul, abs_of_pos (by positivity : 0 < (Real.sqrt (N + 1 : ℕ))⁻¹)]
        refine mul_le_mul hi1 (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity) (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_units_cast_eq_one, mul_one])
      have hs2 : |(1 / (2 * Real.sqrt (1 - t))) * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)| ≤
          (1 / (2 * Real.sqrt δ)) * (Real.sqrt q * |ω.2| + Real.sqrt (1 - q) * |x.2|) := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt (1 - t)))]
        refine mul_le_mul hi2 ((abs_add_le _ _).trans (add_le_add ?_ ?_))
          (abs_nonneg _) (by positivity)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ (1 / (2 * Real.sqrt δ)) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, |ω.1.2 i|) +
            (1 / (2 * Real.sqrt δ)) * (Real.sqrt q * |ω.2| + Real.sqrt (1 - q) * |x.2|) :=
          add_le_add hs1 hs2
        _ = _ := by ring
    calc |deriv u (S_v t ω x)| * |S'_v t ω x|
        ≤ |D₁| * ((1 / (2 * Real.sqrt δ)) *
            (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.2 i|) +
              Real.sqrt q * |ω.2|) + Real.sqrt (1 - q) * |x.2|)) :=
          mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self D₁)) hS'_le
            (abs_nonneg _) (abs_nonneg D₁)
      _ = b_ω ω + c_ξ * |x.2| := by dsimp only [b_ω, c_ξ]; ring
  have hZ_deriv (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      {t : ℝ} (ht : t ∈ U_nbhd) :
      HasDerivAt (fun v' => Real.log (Z_fn v' ω)) (F'_fn t ω) t := by
    have hpt_x (x : (Fin (N + 1) → ℤˣ) × ℝ) {s' : ℝ} (hs' : s' ∈ U_nbhd) :
        HasDerivAt (fun v' => Real.exp (u (S_v v' ω x)))
          ((S'_v s' ω x * deriv u (S_v s' ω x)) * Real.exp (u (S_v s' ω x))) s' := by
      obtain ⟨-, -, hs'0, hs'1⟩ := hv'_b hs'
      have h1 : HasDerivAt
          (fun v' => Real.sqrt v' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)))
          ((1 / (2 * Real.sqrt s')) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ))) s' :=
        (Real.hasDerivAt_sqrt hs'0.ne').mul_const _
      have h2 : HasDerivAt
          (fun v' => Real.sqrt (1 - v') * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2))
          ((-(1 / (2 * Real.sqrt (1 - s')))) *
            (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)) s' := by
        have hsub : HasDerivAt (fun v' : ℝ => 1 - v') (-1) s' := by
          simpa using (hasDerivAt_id s').const_sub 1
        have hsq := (Real.hasDerivAt_sqrt (sub_pos.2 hs'1).ne').comp s' hsub
        exact (hsq.mul_const _).congr_deriv (by ring)
      have hS_d : HasDerivAt (fun v' => S_v v' ω x) (S'_v s' ω x) s' :=
        (h1.add h2).congr_deriv (by dsimp only [S'_v]; ring)
      exact (((hu.differentiable _).hasDerivAt.comp s' hS_d).exp).congr_deriv
        (by dsimp only [Function.comp_apply]; ring)
    let dom_x (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ := (b_ω ω + c_ξ * |x.2|) * Real.exp |B|
    have hdom_xi : Integrable dom_x ((μ_M ω.1.1).prod γ) :=
      ((integrable_const (b_ω ω)).add
        ((IsGaussian.integrable_id.abs.const_mul c_ξ).comp_snd _)).mul_const _
    have hi_t : Integrable (fun x => Real.exp (u (S_v t ω x))) ((μ_M ω.1.1).prod γ) :=
      integrable_exp_of_ae_le (hu.measurable.comp (hSv_m t ω)).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    have hZd : HasDerivAt (fun v' => Z_fn v' ω)
        (∫ x, (S'_v t ω x * deriv u (S_v t ω x)) * Real.exp (u (S_v t ω x))
          ∂((μ_M ω.1.1).prod γ)) t :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ_M ω.1.1).prod γ)
        (F := fun s' x => Real.exp (u (S_v s' ω x)))
        (F' := fun s' x => (S'_v s' ω x * deriv u (S_v s' ω x)) * Real.exp (u (S_v s' ω x)))
        (s := U_nbhd) (bound := dom_x)
        (IsOpen.mem_nhds isOpen_Ioo ht)
        (Eventually.of_forall fun s' =>
          (Real.measurable_exp.comp (hu.measurable.comp (hSv_m s' ω))).aestronglyMeasurable)
        hi_t
        (((hS'v_m t ω).mul ((measurable_deriv u).comp (hSv_m t ω))).mul
          (Real.measurable_exp.comp (hu.measurable.comp (hSv_m t ω)))).aestronglyMeasurable
        (ae_of_all _ fun x s' hs' => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul (hpt_bd ω x hs')
            (Real.exp_le_exp.2 ((hu.le _).trans (le_abs_self B)))
            (Real.exp_pos _).le (by positivity))
        hdom_xi (ae_of_all _ fun x s' hs' => hpt_x x hs')).2
    have hZ_pos : 0 < Z_fn t ω := integral_exp_pos hi_t
    exact (hZd.log hZ_pos.ne').congr_deriv
      (by dsimp only [F'_fn, Z_fn]; rw [integral_tilted_eq_div, div_eq_mul_inv, mul_comm])
  -- Bound `|F'_fn t ω|` by `b_ω ω + exp(2 |B|) * c_ξ * ∫ |ξ| ∂γ`!
  have hF'_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      {t : ℝ} (ht : t ∈ U_nbhd) :
      |F'_fn t ω| ≤ b_ω ω + Real.exp (2 * |B|) * (c_ξ * ∫ ξ, |ξ| ∂γ) := by
    let V_t (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ := u (S_v t ω x)
    have hVt_m : Measurable V_t := hu.measurable.comp (hSv_m t ω)
    have hprob_t : IsProbabilityMeasure (((μ_M ω.1.1).prod γ).tilted V_t) :=
      isProbabilityMeasure_tilted_of_ae_le hVt_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
    have hξ_int : Integrable (fun x : (Fin (N + 1) → ℤˣ) × ℝ => |x.2|) ((μ_M ω.1.1).prod γ) :=
      IsGaussian.integrable_id.abs.comp_snd _
    have hξ_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × ℝ => |x.2|)
        (((μ_M ω.1.1).prod γ).tilted V_t) :=
      integrable_tilted_of_ae_le hVt_m.aemeasurable (ae_of_all _ fun _ => hu.le _) hξ_int
    have hint_F : Integrable (fun x => S'_v t ω x * deriv u (S_v t ω x))
        (((μ_M ω.1.1).prod γ).tilted V_t) :=
      ((integrable_const (b_ω ω)).add (hξ_t.const_mul c_ξ)).mono'
        ((hS'v_m t ω).mul ((measurable_deriv u).comp (hSv_m t ω))).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hpt_bd ω x ht)
    have h1 : |F'_fn t ω| ≤
        ∫ x, (b_ω ω + c_ξ * |x.2|) ∂(((μ_M ω.1.1).prod γ).tilted V_t) :=
      (abs_integral_le_integral_abs).trans
        (integral_mono hint_F.abs ((integrable_const (b_ω ω)).add (hξ_t.const_mul c_ξ))
          fun x => hpt_bd ω x ht)
    have h1_add : (∫ x, (b_ω ω + c_ξ * |x.2|) ∂(((μ_M ω.1.1).prod γ).tilted V_t)) =
        (∫ _x, b_ω ω ∂(((μ_M ω.1.1).prod γ).tilted V_t)) +
        ∫ x, c_ξ * |x.2| ∂(((μ_M ω.1.1).prod γ).tilted V_t) :=
      integral_add (integrable_const (b_ω ω)) (hξ_t.const_mul c_ξ)
    rw [h1_add, integral_const, probReal_univ, one_smul, integral_const_mul] at h1
    refine h1.trans (add_le_add le_rfl ?_)
    have hbound := abs_integral_tilted_le_exp_mul_integral_abs hVt_m.aemeasurable
      (ae_of_all _ fun x => (hu.abs_le _).trans (le_abs_self B)) hξ_int
    have hsnd := integral_prod_fun_snd_of_isProbabilityMeasure (μ := μ_M ω.1.1) (ν := γ)
      (fun ξ : ℝ => |ξ|)
    have hd0 := (le_abs_self _).trans hbound
    simp only [probReal_univ, div_one, abs_abs, hsnd] at hd0
    calc c_ξ * ∫ x, |x.2| ∂(((μ_M ω.1.1).prod γ).tilted V_t)
        ≤ c_ξ * (Real.exp (2 * |B|) * ∫ ξ, |ξ| ∂γ) :=
          mul_le_mul_of_nonneg_left hd0 hc_ξ0
      _ = Real.exp (2 * |B|) * (c_ξ * ∫ ξ, |ξ| ∂γ) := by ring
  -- Measurability of `Z_fn t` and `F'_fn v` on `P_ext`!
  let E_M (g₀ : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
  have hEM_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
      E_M p.1 p.2 := by
    refine Finset.measurable_sum _ fun k _ => hu.measurable.comp ?_
    refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
    have h1 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
        p.1 k i := (measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_fst)
    have h2 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
        ((p.2 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_snd)
    exact h1.mul h2
  have hEM_i (g₀ : Fin M → Fin (N + 1) → ℝ) :
      Integrable (fun τ => Real.exp (E_M g₀ τ)) Measure.count := Integrable.of_finite
  have hSv_joint (s' : ℝ) : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
      S_v s' p.1 p.2 := by
    have h1 : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
        ∑ i : Fin (N + 1), p.1.1.2 i * ((p.2.1 i : ℤ) : ℝ) :=
      Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp
          (measurable_snd.comp (measurable_fst.comp measurable_fst))).mul
        (measurable_units_cast.comp
          ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    exact ((h1.const_mul _).const_mul _).add
      ((((measurable_snd.comp measurable_fst).const_mul _).add
        ((measurable_snd.comp measurable_snd).const_mul _)).const_mul _)
  have hS'v_joint : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
      S'_v v p.1 p.2 := by
    have h1 : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
        ∑ i : Fin (N + 1), p.1.1.2 i * ((p.2.1 i : ℤ) : ℝ) :=
      Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp
          (measurable_snd.comp (measurable_fst.comp measurable_fst))).mul
        (measurable_units_cast.comp
          ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    exact ((h1.const_mul _).const_mul _).sub
      ((((measurable_snd.comp measurable_fst).const_mul _).add
        ((measurable_snd.comp measurable_snd).const_mul _)).const_mul _)
  have hZ_m (s' : ℝ) : Measurable (Z_fn s') := by
    have heq : Z_fn s' = fun ω =>
        (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v s' ω (τ, ξ))) ∂γ) /
        ∑ τ : Fin (N + 1) → ℤˣ, Real.exp (E_M ω.1.1 τ) := by
      funext ω
      dsimp only [Z_fn, μ_M]
      have hi : Integrable (fun x => Real.exp (u (S_v s' ω x)))
          (((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E_M ω.1.1)).prod γ) :=
        integrable_exp_of_ae_le (hu.measurable.comp (hSv_m s' ω)).aemeasurable
          (ae_of_all _ fun _ => hu.le _)
      rw [integral_prod _ hi, integral_tilted_eq_div,
        integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
      simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
      congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [heq]
    refine Measurable.div (Finset.measurable_sum _ fun τ _ => Measurable.mul ?_ ?_)
      (Finset.measurable_sum _ fun τ _ => ?_)
    · have hτ : Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
          E_M ω.1.1 τ :=
        Finset.measurable_sum _ fun k _ => hu.measurable.comp
          ((Finset.measurable_sum _ fun i _ =>
            ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp
              (measurable_fst.comp measurable_fst))).mul_const _).const_mul _)
      exact Real.measurable_exp.comp hτ
    · have hj : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
          Real.exp (u (S_v s' p.1 (τ, p.2))) := by
        have h1 : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
            ∑ i : Fin (N + 1), p.1.1.2 i * ((τ i : ℤ) : ℝ) :=
          Finset.measurable_sum _ fun i _ =>
            ((measurable_pi_apply i).comp
              (measurable_snd.comp (measurable_fst.comp measurable_fst))).mul_const _
        exact Real.measurable_exp.comp (hu.measurable.comp
          (((h1.const_mul _).const_mul _).add
            ((((measurable_snd.comp measurable_fst).const_mul _).add
              (measurable_snd.const_mul _)).const_mul _)))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
    · have hτ : Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
          E_M ω.1.1 τ :=
        Finset.measurable_sum _ fun k _ => hu.measurable.comp
          ((Finset.measurable_sum _ fun i _ =>
            ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp
              (measurable_fst.comp measurable_fst))).mul_const _).const_mul _)
      exact Real.measurable_exp.comp hτ
  have hlogZ_int (s' : ℝ) : Integrable (fun ω => Real.log (Z_fn s' ω)) P_ext :=
    Integrable.of_bound (Real.measurable_log.comp (hZ_m s')).aestronglyMeasurable |B|
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact (abs_log_integral_exp_le_of_ae_abs_le
          (hu.measurable.comp (hSv_m s' ω)).aemeasurable
          (ae_of_all _ fun _ => hu.abs_le _)).trans (le_abs_self B))
  -- Measurability of `F'_fn v` via `measurable_integral_pi_tilted_prod_tilted` on `Prod.assoc`:
  let e_ass : (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) ≃ᵐ
      (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ) :=
    MeasurableEquiv.prodAssoc
  have hF'_m : Measurable (F'_fn v) := by
    let V_a (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ))
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ := u (S_v v (e_ass.symm p) x)
    let G_a (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ))
        (σ : Unit → (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      S'_v v (e_ass.symm p) (σ ()) * deriv u (S_v v (e_ass.symm p) (σ ()))
    have hVa_m : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
        V_a q_p.1 q_p.2 := by
      have h1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
          ∑ i : Fin (N + 1), q_p.1.2.1 i * ((q_p.2.1 i : ℤ) : ℝ) :=
        Finset.measurable_sum _ fun i _ =>
          ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_snd.comp measurable_fst))).mul
          (measurable_units_cast.comp
            ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
      exact hu.measurable.comp (((h1.const_mul _).const_mul _).add
        ((((measurable_snd.comp (measurable_snd.comp measurable_fst)).const_mul _).add
          ((measurable_snd.comp measurable_snd).const_mul _)).const_mul _))
    have hGa_m : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
          (Unit → (Fin (N + 1) → ℤˣ) × ℝ) => G_a q_p.1 q_p.2 := by
      have h_ev : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × ℝ) => q_p.2 () :=
        (measurable_pi_apply ()).comp measurable_snd
      have h1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × ℝ) =>
          ∑ i : Fin (N + 1), q_p.1.2.1 i * ((((q_p.2 ()).1 i : ℤ) : ℝ)) :=
        Finset.measurable_sum _ fun i _ =>
          ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_snd.comp measurable_fst))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp (measurable_fst.comp h_ev)))
      have hz_a : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × ℝ) =>
          Real.sqrt q * q_p.1.2.2 + Real.sqrt (1 - q) * (q_p.2 ()).2 :=
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).const_mul _).add
          ((measurable_snd.comp h_ev).const_mul _)
      exact (((h1.const_mul _).const_mul _).sub (hz_a.const_mul _)).mul
        ((measurable_deriv u).comp (((h1.const_mul _).const_mul _).add (hz_a.const_mul _)))
    have hm_u := measurable_integral_pi_tilted_prod_tilted (R := Unit)
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)) γ hEM_m hEM_i hVa_m hGa_m
    have heq : F'_fn v = fun ω =>
        (∫ σ : Unit → (Fin (N + 1) → ℤˣ) × ℝ, G_a (e_ass ω) σ
          ∂(Measure.pi fun _ : Unit => ((μ_M (e_ass ω).1).prod γ).tilted (V_a (e_ass ω)))) := by
      funext ω
      have hV_ω : V_a (e_ass ω) = fun x => u (S_v v ω x) := by
        funext x; dsimp only [V_a]; rw [MeasurableEquiv.symm_apply_apply]
      have hprob_ω : IsProbabilityMeasure
          (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))) :=
        isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
          (ae_of_all _ fun _ => hu.le _)
      have he_fst : (e_ass ω).1 = ω.1.1 := rfl
      rw [he_fst, hV_ω]
      symm
      refine (integral_congr_ae (ae_of_all _ fun σ => ?_)).trans
        ((measurePreserving_funUnique (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
          Unit).integral_comp_of_aestronglyMeasurable
          (g := fun x => S'_v v ω x * deriv u (S_v v ω x))
          ((hS'v_m v ω).mul ((measurable_deriv u).comp (hSv_m v ω))).aestronglyMeasurable)
      dsimp only [G_a, Function.comp_apply]
      rw [MeasurableEquiv.symm_apply_apply]
      rfl
    rw [heq]
    exact hm_u.comp e_ass.measurable
  have hb_ω_int : Integrable b_ω P_ext := by
    dsimp only [b_ω]
    refine Integrable.const_mul (Integrable.const_mul (Integrable.add ?_ ?_) _) |D₁|
    · refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
      have hi1 : Integrable (fun gM : Fin (N + 1) → ℝ => |gM i|)
          (Measure.pi fun _ : Fin (N + 1) => γ) :=
        integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ) (i := i) IsGaussian.integrable_id.abs
      exact (hi1.comp_snd P_M).comp_fst γ
    · have hz1 : Integrable (fun z : ℝ => Real.sqrt q * |z|) γ :=
        IsGaussian.integrable_id.abs.const_mul (Real.sqrt q)
      exact hz1.comp_snd (P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ))
  have hd_raw : HasDerivAt (fun v' => ∫ ω, Real.log (Z_fn v' ω) ∂P_ext)
      (∫ ω, F'_fn v ω ∂P_ext) v :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P_ext)
      (F := fun t ω => Real.log (Z_fn t ω)) (F' := F'_fn) (s := U_nbhd)
      (bound := fun ω => b_ω ω + Real.exp (2 * |B|) * (c_ξ * ∫ ξ, |ξ| ∂γ))
      hU_nhds (Eventually.of_forall fun t => (hlogZ_int t).aestronglyMeasurable)
      (hlogZ_int v) hF'_m.aestronglyMeasurable
      (ae_of_all _ fun ω t ht => by rw [Real.norm_eq_abs]; exact hF'_bd ω ht)
      (hb_ω_int.add (integrable_const _))
      (ae_of_all _ fun ω t ht => hZ_deriv ω ht)).2
  -- Step 2: Apply `stein_tilted_replica_ratio` at fixed `g₀` to evaluate `∫ ω, F'_fn v ω ∂P_ext`!
  refine hd_raw.congr_deriv ?_
  let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ
  let γ_aux := Measure.pi fun _ : Unit => γ
  let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => Real.sqrt (1 - v) * Real.sqrt q)
  let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt q)
  let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - v) * Real.sqrt (1 - q)
  let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
    fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - q)
  have hcov_sh (τ₁ τ₂ : Fin (N + 1) → ℤˣ) :
      W_sh τ₁ ⬝ᵥ α_sh τ₂ =
        (1 / 2) * ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) - q) := by
    dsimp only [W_sh, α_sh]
    rw [sumElim_dotProduct_sumElim]
    have hv_ne : Real.sqrt v ≠ 0 := (Real.sqrt_pos.2 hv.1).ne'
    have h1v_ne : Real.sqrt (1 - v) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hv.2)).ne'
    have hsq_L : (Real.sqrt (N + 1 : ℕ))⁻¹ * (Real.sqrt (N + 1 : ℕ))⁻¹ = ((N : ℝ) + 1)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    have hsq_q : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.1
    have h1 : (fun i : Fin (N + 1) =>
        (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₁ i : ℤ) : ℝ)) ⬝ᵥ
      (fun i : Fin (N + 1) =>
        Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₂ i : ℤ) : ℝ)) =
      (1 / 2) * (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) := by
      simp only [dotProduct]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc : (1 / (2 * Real.sqrt v)) * Real.sqrt v = 1 / 2 := by field_simp
      calc (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₁ i : ℤ) : ℝ) *
            (Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₂ i : ℤ) : ℝ))
          = ((1 / (2 * Real.sqrt v)) * Real.sqrt v) *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * (Real.sqrt (N + 1 : ℕ))⁻¹) *
              (((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) := by ring
        _ = (1 / 2) * (((N : ℝ) + 1)⁻¹ * (((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ))) := by
            rw [hc, hsq_L]; ring
    have h2 : (fun _ : Unit => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt q) ⬝ᵥ
        (fun _ : Unit => Real.sqrt (1 - v) * Real.sqrt q) = -(1 / 2) * q := by
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      have hc : (1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - v) = 1 / 2 := by field_simp
      calc -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt q * (Real.sqrt (1 - v) * Real.sqrt q)
          = -((1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - v)) * (Real.sqrt q * Real.sqrt q) := by
            ring
        _ = -(1 / 2) * q := by rw [hc, hsq_q]
    rw [h1, h2]; ring
  have hcov_diag (τ : Fin (N + 1) → ℤˣ) :
      W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0 := by
    rw [hcov_sh τ τ]
    have hself : (((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) = 1 := by
      simpa only [dotProduct, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        card_inv_mul_dotProduct_self_eq_one (fun i : Fin (N + 1) => ((τ i : ℤ) : ℝ))
          (fun i => units_cast_sq (τ i))
    have haux_dot : W_aux τ ⬝ᵥ α_aux τ = -(1 / 2) * (1 - q) := by
      dsimp only [W_aux, α_aux]
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      have h1v_ne : Real.sqrt (1 - v) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hv.2)).ne'
      have hc : (1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - v) = 1 / 2 := by field_simp
      have hsq_1q : Real.sqrt (1 - q) * Real.sqrt (1 - q) = 1 - q :=
        Real.mul_self_sqrt (sub_nonneg.2 hq.2)
      calc -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - q) *
            (Real.sqrt (1 - v) * Real.sqrt (1 - q))
          = -((1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - v)) *
              (Real.sqrt (1 - q) * Real.sqrt (1 - q)) := by ring
        _ = -(1 / 2) * (1 - q) := by rw [hc, hsq_1q]
    rw [hself, haux_dot]; ring
  have hstein_g₀ (g₀ : Fin M → Fin (N + 1) → ℝ) :
      ∫ w, ∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
          1 * (W_sh (σ ()).1 ⬝ᵥ w + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
            (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ w + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
          ∂(Measure.pi fun _ : Unit => ((μ_M g₀).prod γ_aux).tilted
            (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))) ∂γ_sh =
      -(1 / 2) * ∫ w, ∫ σ : Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i,
              (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q) *
            deriv u (α_sh (σ (some ())).1 ⬝ᵥ w + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
            deriv u (α_sh (σ none).1 ⬝ᵥ w + α_aux (σ none).1 ⬝ᵥ (σ none).2)
          ∂(Measure.pi fun _ : Option Unit => ((μ_M g₀).prod γ_aux).tilted
            (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))) ∂γ_sh := by
    have hψ_deriv (x : ℝ) :
        HasDerivAt (fun t => deriv u t * Real.exp (u t))
          ((deriv (deriv u) x + deriv u x * deriv u x) * Real.exp (u x)) x := by
      have h1 : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        (hu.differentiable_deriv x).hasDerivAt
      have h2 : HasDerivAt (fun t => Real.exp (u t)) (Real.exp (u x) * deriv u x) x :=
        (hu.differentiable x).hasDerivAt.exp
      exact (h1.mul h2).congr_deriv (by ring)
    have hst := stein_tilted_replica_ratio (R := Unit) (μ₀ := μ_M g₀)
      (π := id) measurable_id α_sh W_sh α_aux W_aux
      hu.differentiable hu.abs_le hu.abs_deriv_le
      (fun _ => deriv u)
      (fun _ x => (hψ_deriv x).differentiableAt)
      (M₀ := fun _ => |D₁|) (M' := fun _ => (|D₂| + |D₁| ^ 2) * Real.exp |B|)
      (fun _ x => (hu.abs_deriv_le x).trans (le_abs_self D₁))
      (fun _ x => by
        rw [(hψ_deriv x).deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
        refine mul_le_mul ?_ (Real.exp_le_exp.2 ((hu.le x).trans (le_abs_self B)))
          (Real.exp_pos _).le (by positivity)
        refine (abs_add_le _ _).trans (add_le_add
          ((hu.abs_deriv₂_le x).trans (le_abs_self D₂)) ?_)
        rw [abs_mul, sq]
        exact mul_le_mul ((hu.abs_deriv_le x).trans (le_abs_self D₁))
          ((hu.abs_deriv_le x).trans (le_abs_self D₁)) (abs_nonneg _) (abs_nonneg _))
      (fun _ x => deriv (deriv u) x + deriv u x * deriv u x)
      (fun _ x => (hψ_deriv x).deriv)
      () (f := fun _ => (1 : ℝ)) (integrable_const 1)
    dsimp only [id_eq] at hst
    exact (hst.trans (by
      have hdiag_zero :
          (∑ j : Unit, ∫ w, ∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
            1 * (W_sh (σ ()).1 ⬝ᵥ α_sh (σ j).1 +
                if () = j then W_aux (σ ()).1 ⬝ᵥ α_aux (σ j).1 else 0) *
              ((deriv (deriv u) (α_sh (σ j).1 ⬝ᵥ w + α_aux (σ j).1 ⬝ᵥ (σ j).2) +
                  deriv u (α_sh (σ j).1 ⬝ᵥ w + α_aux (σ j).1 ⬝ᵥ (σ j).2) *
                    deriv u (α_sh (σ j).1 ⬝ᵥ w + α_aux (σ j).1 ⬝ᵥ (σ j).2)) *
                ∏ r_u ∈ Finset.univ.erase j,
                  deriv u (α_sh (σ r_u).1 ⬝ᵥ w + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
            ∂(Measure.pi fun _ : Unit => ((μ_M g₀).prod γ_aux).tilted
              (fun q_1 => u (α_sh q_1.1 ⬝ᵥ w + α_aux q_1.1 ⬝ᵥ q_1.2))) ∂γ_sh) = 0 := by
        rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
        refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun w => ?_)).trans
          (integral_zero _ ℝ)
        refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun σ => ?_)).trans
          (integral_zero _ ℝ)
        dsimp only
        simp only [↓reduceIte, hcov_diag (σ ()).1]
        ring
      rw [hdiag_zero, zero_sub, Fintype.card_unique, Nat.cast_one, one_mul]
      symm
      rw [neg_mul, ← integral_const_mul, neg_inj]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      simp only [Finset.univ_unique, Finset.prod_singleton, hcov_sh]
      ring))
  -- Transport `P_ext` to `P_M.prod γ_sh` and `(Fin (N + 1) → ℤˣ) × ℝ` to `... × (Unit → ℝ)`.
  let split_ext (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ) :=
    (ω.1.1, Sum.elim ω.1.2 (fun _ : Unit => ω.2))
  have hmp_ext : MeasurePreserving split_ext P_ext (P_M.prod γ_sh) := by
    have h1 := measurePreserving_prodAssoc P_M (Measure.pi fun _ : Fin (N + 1) => γ) γ
    have hunit := (measurePreserving_funUnique γ Unit).symm
    have hsum := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin (N + 1) ⊕ Unit => ℝ)
      (fun _ => γ)).comp ((MeasurePreserving.id (Measure.pi fun _ : Fin (N + 1) => γ)).prod hunit)
    have full := ((MeasurePreserving.id P_M).prod hsum).comp h1
    convert full using 1
    ext ω : 1
    refine Prod.ext rfl ?_
    ext idx
    rcases idx with i | _ <;>
      simp [split_ext, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]
  let e_st : ((Fin (N + 1) → ℤˣ) × ℝ) ≃ᵐ ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.funUnique Unit ℝ).symm
  have he_st_apply (x : (Fin (N + 1) → ℤˣ) × ℝ) : e_st x = (x.1, fun _ => x.2) := rfl
  have hmp_st (g₀ : Fin M → Fin (N + 1) → ℝ) :
      MeasurePreserving ⇑e_st ((μ_M g₀).prod γ) ((μ_M g₀).prod γ_aux) :=
    (MeasurePreserving.id (μ_M g₀)).prod (measurePreserving_funUnique γ Unit).symm
  have hS_eq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (x : (Fin (N + 1) → ℤˣ) × ℝ) :
      α_sh (e_st x).1 ⬝ᵥ (split_ext ω).2 + α_aux (e_st x).1 ⬝ᵥ (e_st x).2 = S_v v ω x := by
    rw [he_st_apply]
    dsimp only [α_sh, α_aux, split_ext, S_v]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h1 : (∑ i : Fin (N + 1),
        Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) * ω.1.2 i) =
      Real.sqrt v *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), ω.1.2 i * ((x.1 i : ℤ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
  have hS'_eq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (x : (Fin (N + 1) → ℤˣ) × ℝ) :
      W_sh (e_st x).1 ⬝ᵥ (split_ext ω).2 + W_aux (e_st x).1 ⬝ᵥ (e_st x).2 = S'_v v ω x := by
    rw [he_st_apply]
    dsimp only [W_sh, W_aux, split_ext, S'_v]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h1 : (∑ i : Fin (N + 1),
        (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) * ω.1.2 i) =
      (1 / (2 * Real.sqrt v)) *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), ω.1.2 i * ((x.1 i : ℤ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
  have htilted_st (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))).map e_st =
      ((μ_M (split_ext ω).1).prod γ_aux).tilted
        (fun y => u (α_sh y.1 ⬝ᵥ (split_ext ω).2 + α_aux y.1 ⬝ᵥ y.2)) := by
    have hVm : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => u (S_v v ω x) :=
      hu.measurable.comp (hSv_m v ω)
    rw [map_tilted_measurableEquiv e_st (hmp_st ω.1.1) hVm]
    congr 1; funext y
    obtain ⟨x, rfl⟩ := e_st.surjective y
    dsimp only [Function.comp_apply]
    rw [MeasurableEquiv.symm_apply_apply, hS_eq ω x]
  let I_L (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
      1 * (W_sh (σ ()).1 ⬝ᵥ p.2 + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ p.2 + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
      ∂(Measure.pi fun _ : Unit => ((μ_M p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)))
  let I_R (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q) *
        deriv u (α_sh (σ (some ())).1 ⬝ᵥ p.2 + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1 ⬝ᵥ p.2 + α_aux (σ none).1 ⬝ᵥ (σ none).2)
      ∂(Measure.pi fun _ : Option Unit => ((μ_M p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)))
  let V_sp (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ))
      (y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
    u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)
  have hVsp_m : Measurable fun q_p :
      ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => V_sp q_p.1 q_p.2 := by
    have hd1 : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_sh q_p.2.1 ⬝ᵥ q_p.1.2 := by
      simp only [dotProduct]
      refine Finset.measurable_sum _ fun idx _ => ?_
      have ha : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_sh q_p.2.1 idx :=
        (measurable_of_finite fun τ => α_sh τ idx).comp (measurable_fst.comp measurable_snd)
      exact ha.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
    have hd2 : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_aux q_p.2.1 ⬝ᵥ q_p.2.2 := by
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact measurable_const.mul
        ((measurable_pi_apply ()).comp (measurable_snd.comp measurable_snd))
    exact hu.measurable.comp (hd1.add hd2)
  have hIL_m : Measurable I_L := by
    let F_L (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ))
        (σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      1 * (W_sh (σ ()).1 ⬝ᵥ p.2 + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ p.2 + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
    have hFL_m : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => F_L q_p.1 q_p.2 := by
      dsimp only [F_L]
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      have h_ev : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => q_p.2 () :=
        (measurable_pi_apply ()).comp measurable_snd
      have hw1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => W_sh (q_p.2 ()).1 ⬝ᵥ q_p.1.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => W_sh τ idx).comp (measurable_fst.comp h_ev)).mul
            ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have hw2 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => W_aux (q_p.2 ()).1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      have ha1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_sh (q_p.2 ()).1 ⬝ᵥ q_p.1.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp (measurable_fst.comp h_ev)).mul
            ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_aux (q_p.2 ()).1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      exact (hw1.add hw2).mul ((measurable_deriv u).comp (ha1.add ha2))
    exact measurable_integral_pi_tilted_prod_tilted
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)) γ_aux hEM_m hEM_i hVsp_m hFL_m
  have hIR_m : Measurable I_R := by
    have hfl_o (o : Option Unit) : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
        deriv u (α_sh (q_p.2 o).1 ⬝ᵥ q_p.1.2 + α_aux (q_p.2 o).1 ⬝ᵥ (q_p.2 o).2) := by
      have h_ev : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => q_p.2 o :=
        (measurable_pi_apply o).comp measurable_snd
      have ha1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_sh (q_p.2 o).1 ⬝ᵥ q_p.1.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp (measurable_fst.comp h_ev)).mul
            ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
          α_aux (q_p.2 o).1 ⬝ᵥ (q_p.2 o).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      exact (measurable_deriv u).comp (ha1.add ha2)
    have hR_o : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
          ((((q_p.2 (some ())).1 i : ℤ) : ℝ) * (((q_p.2 none).1 i : ℤ) : ℝ))) - q) := by
      refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
      exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp ((measurable_pi_apply (some ())).comp measurable_snd)))).mul
        (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp ((measurable_pi_apply none).comp measurable_snd))))
    exact measurable_integral_pi_tilted_prod_tilted
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)) γ_aux hEM_m hEM_i hVsp_m
      ((hR_o.mul (hfl_o (some ()))).mul (hfl_o none))
  -- Pointwise split alignment:
  have hIL_split (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      I_L (split_ext ω) = F'_fn v ω := by
    let ν_ω := ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))
    have hprob_ω : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    let F_sL (σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      1 * (W_sh (σ ()).1 ⬝ᵥ (split_ext ω).2 + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit,
          deriv u (α_sh (σ r_u).1 ⬝ᵥ (split_ext ω).2 + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
    have ht1 : I_L (split_ext ω) =
        ∫ f_u : Unit → (Fin (N + 1) → ℤˣ) × ℝ,
          F_sL (fun r_u => e_st (f_u r_u)) ∂(Measure.pi fun _ : Unit => ν_ω) := by
      dsimp only [I_L, F_sL, ν_ω]
      rw [← htilted_st ω]
      exact integral_pi_map_equiv ν_ω e_st F_sL
    have ht2 (f_u : Unit → (Fin (N + 1) → ℤˣ) × ℝ) :
        F_sL (fun r_u => e_st (f_u r_u)) =
          S'_v v ω (f_u ()) * deriv u (S_v v ω (f_u ())) := by
      dsimp only [F_sL]
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      rw [hS_eq ω (f_u ()), hS'_eq ω (f_u ())]
    rw [ht1]
    exact (integral_congr_ae (ae_of_all _ ht2)).trans
      ((measurePreserving_funUnique ν_ω Unit).integral_comp_of_aestronglyMeasurable
        (g := fun x => S'_v v ω x * deriv u (S_v v ω x))
        ((hS'v_m v ω).mul ((measurable_deriv u).comp (hSv_m v ω))).aestronglyMeasurable)
  let e_opt2 : Option Unit ≃ Fin 2 :=
    { toFun := fun o => match o with | some () => 0 | none => 1
      invFun := fun i => if i = 0 then some () else none
      left_inv := fun o => by cases o <;> simp
      right_inv := fun i => by fin_cases i <;> simp }
  have hIR_split (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      I_R (split_ext ω) =
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
          ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))) := by
    let ν_ω := ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))
    have hprob_ω : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    let G₂ (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
    have hG2_m : Measurable G₂ := by
      have hR_2 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ =>
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 0)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 1))))
      exact (hR_2.mul ((measurable_deriv u).comp ((hSv_m v ω).comp (measurable_pi_apply 0)))).mul
        ((measurable_deriv u).comp ((hSv_m v ω).comp (measurable_pi_apply 1)))
    let F_sR (σ : Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q) *
        deriv u
          (α_sh (σ (some ())).1 ⬝ᵥ (split_ext ω).2 + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1 ⬝ᵥ (split_ext ω).2 + α_aux (σ none).1 ⬝ᵥ (σ none).2)
    have ht1 : I_R (split_ext ω) =
        ∫ τ_o : Option Unit → (Fin (N + 1) → ℤˣ) × ℝ,
          F_sR (fun o => e_st (τ_o o)) ∂(Measure.pi fun _ : Option Unit => ν_ω) := by
      dsimp only [I_R, F_sR, ν_ω]
      rw [← htilted_st ω]
      exact integral_pi_map_equiv ν_ω e_st F_sR
    let e_pi := MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × ℝ) e_opt2
    have hmp_opt2 : MeasurePreserving ⇑e_pi
        (Measure.pi fun _ : Option Unit => ν_ω) (Measure.pi fun _ : Fin 2 => ν_ω) :=
      measurePreserving_piCongrLeft (fun _ : Fin 2 => ν_ω) e_opt2
    have h_opt := hmp_opt2.integral_comp_of_aestronglyMeasurable hG2_m.aestronglyMeasurable
    have ht2 (τ_o : Option Unit → (Fin (N + 1) → ℤˣ) × ℝ) :
        F_sR (fun o => e_st (τ_o o)) = (G₂ ∘ ⇑e_pi) τ_o := by
      have h0 : e_pi τ_o 0 = τ_o (some ()) := by
        change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × ℝ) e_opt2 τ_o) 0 = _
        rw [Equiv.piCongrLeft_apply]; rfl
      have h1 : e_pi τ_o 1 = τ_o none := by
        change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × ℝ) e_opt2 τ_o) 1 = _
        rw [Equiv.piCongrLeft_apply]; rfl
      dsimp only [F_sR, G₂, Function.comp_apply]
      rw [h0, h1, hS_eq ω (τ_o (some ())), hS_eq ω (τ_o none),
        he_st_apply (τ_o (some ())), he_st_apply (τ_o none)]
    rw [ht1]
    exact (integral_congr_ae (ae_of_all _ ht2)).trans h_opt
  -- Integrability of `I_L` and `I_R` on `P_M.prod γ_sh` via pulling back from `P_ext`!
  have hF'_int : Integrable (F'_fn v) P_ext := by
    have hv_mem : v ∈ U_nbhd := ⟨by linarith, by linarith⟩
    exact (hb_ω_int.add (integrable_const _)).mono' hF'_m.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hF'_bd ω hv_mem)
  have hIL_int : Integrable I_L (P_M.prod γ_sh) :=
    (hmp_ext.integrable_comp hIL_m.aestronglyMeasurable).1
      (hF'_int.congr (ae_of_all _ fun ω => (hIL_split ω).symm))
  have hIR_int : Integrable I_R (P_M.prod γ_sh) := by
    refine Integrable.of_bound hIR_m.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun p => ?_)
    have hVp_m : Measurable (V_sp p) := by
      have ha1 : Measurable fun y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ) => α_sh y.1 ⬝ᵥ p.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp measurable_fst).mul_const _
      have ha2 : Measurable fun y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ) => α_aux y.1 ⬝ᵥ y.2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
      exact hu.measurable.comp (ha1.add ha2)
    have hprob_p : IsProbabilityMeasure (((μ_M p.1).prod γ_aux).tilted (V_sp p)) :=
      isProbabilityMeasure_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun σ => by
      rw [abs_mul, abs_mul, sq]
      have hd_ov : |(((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q| ≤ 2 := by
        have h1 : |((N : ℝ) + 1)⁻¹ * ∑ i,
            (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)| ≤ 1 := by
          rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
          have hs_b : |∑ i : Fin (N + 1),
              (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)| ≤ (N : ℝ) + 1 :=
            ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := 1) fun i => by
              rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]).trans_eq
              (by simp))
          exact (inv_mul_le_iff₀ (by positivity)).2 (by linarith)
        have h2 := abs_sub (((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) q
        rw [abs_of_nonneg hq.1] at h2; linarith [hq.2]
      calc _ ≤ 2 * |D₁| * |D₁| :=
            mul_le_mul (mul_le_mul hd_ov ((hu.abs_deriv_le _).trans (le_abs_self D₁))
              (abs_nonneg _) zero_le_two) ((hu.abs_deriv_le _).trans (le_abs_self D₁))
              (abs_nonneg _) (by positivity)
        _ = 2 * (|D₁| * |D₁|) := by ring
  have hlhs_eq : (∫ ω, F'_fn v ω ∂P_ext) = ∫ p, I_L p ∂(P_M.prod γ_sh) :=
    (integral_congr_ae (ae_of_all _ fun ω => (hIL_split ω).symm)).trans
      (hmp_ext.integral_comp_of_aestronglyMeasurable hIL_m.aestronglyMeasurable)
  have hrhs_eq :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
        ∂P_ext) =
      ∫ p, I_R p ∂(P_M.prod γ_sh) :=
    (integral_congr_ae (ae_of_all _ fun ω => (hIR_split ω).symm)).trans
      (hmp_ext.integral_comp_of_aestronglyMeasurable hIR_m.aestronglyMeasurable)
  rw [hlhs_eq, hrhs_eq, integral_prod I_L hIL_int, integral_prod I_R hIR_int,
    ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun g₀ => hstein_g₀ g₀)

end SecondProofIncrement

end SpinGlasses
