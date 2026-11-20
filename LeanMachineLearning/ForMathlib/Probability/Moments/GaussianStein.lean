/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiUpdate
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stein's lemma (Gaussian integration by parts)

For a centered Gaussian `g ~ 𝒩(0, v)` and a differentiable `F`,
`𝔼[g F(g)] = v 𝔼[F'(g)]` (`integral_id_mul_gaussianReal_eq`, Panchenko Eq. (1.19)).  It is
Mathlib's improper integration by parts (`integral_mul_deriv_eq_deriv_mul_of_integrable`) applied
to `F` and the Gaussian density, whose derivative is `-(x / v) p(x)`.

The coordinatewise version for a vector of independent centered Gaussians follows by resampling
one coordinate (`MeasureTheory.integral_pi_eq_integral_update`) and applying the one-dimensional
identity to the slices (`integral_eval_mul_pi_gaussianReal_eq`).
-/

@[expose] public section

open MeasureTheory Filter Topology Function Matrix
open scoped NNReal

namespace ProbabilityTheory

/-- A continuous function `F` with `x * F x` integrable against a finite measure is integrable. -/
theorem integrable_of_integrable_id_mul {μ : Measure ℝ} [IsFiniteMeasure μ] {F : ℝ → ℝ}
    (hF : Continuous F) (h : Integrable (fun x => x * F x) μ) : Integrable F μ := by
  have h1 : IntegrableOn F (Set.Icc (-1) 1) μ :=
    hF.continuousOn.integrableOn_Icc
  have h2 : IntegrableOn F (Set.Icc (-1 : ℝ) 1)ᶜ μ := by
    refine Integrable.mono' h.norm.integrableOn (hF.aestronglyMeasurable.restrict) ?_
    refine (ae_restrict_iff' measurableSet_Icc.compl).2 (Eventually.of_forall fun x hx => ?_)
    have hx1 : 1 ≤ |x| := by
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [norm_mul, Real.norm_eq_abs]
    exact le_mul_of_one_le_left (abs_nonneg _) hx1
  have := h1.union h2
  rwa [Set.union_compl_self, integrableOn_univ] at this

/-- The derivative of the centered Gaussian density: `p'(x) = -(x / v) p(x)`. -/
theorem hasDerivAt_gaussianPDFReal_zero {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / v) * gaussianPDFReal 0 v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / (2 * v)) (-(2 * x) / (2 * v)) x := by
    simpa using ((hasDerivAt_pow 2 x).neg.div_const (2 * (v : ℝ)))
  have h2 := (h1.exp).const_mul (√(2 * Real.pi * v))⁻¹
  have e : gaussianPDFReal 0 v =
      fun y => (√(2 * Real.pi * v))⁻¹ * Real.exp (-(y ^ 2) / (2 * v)) := by
    ext y; simp [gaussianPDFReal]
  rw [e]
  convert h2 using 1
  field_simp

/-- Integrability against a nondegenerate Gaussian is integrability of the density-weighted
function against Lebesgue measure. -/
theorem integrable_gaussianReal_iff_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) {f : ℝ → E} :
    Integrable f (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x • f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [toReal_gaussianPDF]

/-- Polynomials are integrable against a real Gaussian. -/
theorem integrable_pow_gaussianReal (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal m v) := by
  have h := (memLp_id_gaussianReal (μ := m) (v := v) k).integrable_norm_pow'
  refine Integrable.mono' (by simpa using h) (by fun_prop) (Eventually.of_forall fun x => ?_)
  simp

/-- **Stein's lemma (Panchenko Eq. (1.19)):** for `g ~ 𝒩(0, v)` and `F` differentiable with
`g F(g)` and `F'(g)` integrable, `𝔼[g F(g)] = v 𝔼[F'(g)]`.  The case `v = 0` is trivial, and for
`v ≠ 0` it is integration by parts against the Gaussian density, whose boundary terms vanish
because `F` is integrable against the density (a consequence of the integrability of `g F(g)`). -/
theorem integral_id_mul_gaussianReal_eq (v : ℝ≥0) {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hxF : Integrable (fun x => x * F x) (gaussianReal 0 v))
    (hF' : Integrable F' (gaussianReal 0 v)) :
    ∫ x, x * F x ∂gaussianReal 0 v = v * ∫ x, F' x ∂gaussianReal 0 v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hFi : Integrable F (gaussianReal 0 v) := integrable_of_integrable_id_mul hFc hxF
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hpd := hasDerivAt_gaussianPDFReal_zero hv
  rw [integrable_gaussianReal_iff_smul hv] at hxF hF' hFi
  simp only [smul_eq_mul] at hxF hF' hFi
  have h1 : Integrable (fun x => F x * (-(x / v) * gaussianPDFReal 0 v x)) := by
    have := hxF.const_mul (-(v : ℝ)⁻¹)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only; field_simp
  have h2 : Integrable (fun x => F' x * gaussianPDFReal 0 v x) := by
    simpa only [mul_comm] using hF'
  have h3 : Integrable (fun x => F x * gaussianPDFReal 0 v x) := by
    simpa only [mul_comm] using hFi
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := F) (v := gaussianPDFReal 0 v)
    (u' := F') (v' := fun x => -(x / v) * gaussianPDFReal 0 v x)
    (fun x _ => hF x) (fun x _ => hpd x) h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have e1 : ∫ x, gaussianPDFReal 0 v x * (x * F x) =
      -(v : ℝ) * ∫ x, F x * (-(x / v) * gaussianPDFReal 0 v x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only; field_simp
  rw [e1, key]
  simp only [mul_comm]
  ring_nf

/-- **Gaussian integration by parts for an affine composition:**
`𝔼 [z F(S₀ + c z)] = v c 𝔼 [F'(S₀ + c z)]` for `z ~ 𝒩(0, v)`. -/
theorem integral_id_mul_comp_affine_gaussianReal (v : ℝ≥0) {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (S₀ c : ℝ)
    (h1 : Integrable (fun z => z * F (S₀ + c * z)) (gaussianReal 0 v))
    (h2 : Integrable (fun z => F' (S₀ + c * z)) (gaussianReal 0 v)) :
    ∫ z, z * F (S₀ + c * z) ∂gaussianReal 0 v =
      (v : ℝ) * c * ∫ z, F' (S₀ + c * z) ∂gaussianReal 0 v := by
  have hd : ∀ z, HasDerivAt (fun t => F (S₀ + c * t)) (c * F' (S₀ + c * z)) z := fun z => by
    have hl : HasDerivAt (fun t : ℝ => S₀ + c * t) c z := by
      simpa using ((hasDerivAt_id z).const_mul c).const_add S₀
    exact ((hF _).comp z hl).congr_deriv (mul_comm _ _)
  have h := integral_id_mul_gaussianReal_eq v hd h1 (h2.const_mul c)
  rw [h, integral_const_mul]
  ring

/-- **The moment recurrence of the standard Gaussian:** `𝔼 g^{k+2} = (k + 1) 𝔼 g^k`, from
Stein's lemma with `F (x) = x^{k+1}`. -/
theorem integral_pow_add_two_gaussianReal (k : ℕ) :
    ∫ x : ℝ, x ^ (k + 2) ∂(gaussianReal 0 1) =
      (k + 1 : ℝ) * ∫ x : ℝ, x ^ k ∂(gaussianReal 0 1) := by
  have h := integral_id_mul_gaussianReal_eq 1 (F := fun x : ℝ => x ^ (k + 1))
    (F' := fun x => (k + 1 : ℝ) * x ^ k) (fun x => by simpa using hasDerivAt_pow (k + 1) x)
    (by simpa [pow_succ'] using integrable_pow_gaussianReal 0 1 (k + 2))
    ((integrable_pow_gaussianReal 0 1 k).const_mul _)
  simp only [NNReal.coe_one, one_mul, integral_const_mul] at h
  simpa [pow_succ'] using h

section Growth

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- `exp (w |t|)` is integrable against any real Gaussian law, including zero variance. -/
theorem integrable_exp_mul_abs_gaussianReal {m : ℝ} {v : ℝ≥0} (w : ℝ) :
    Integrable (fun t : ℝ => Real.exp (w * |t|)) (gaussianReal m v) := by
  refine Integrable.mono' ((integrable_exp_mul_gaussianReal (μ := m) (v := v) w).add
    (integrable_exp_mul_gaussianReal (μ := m) (v := v) (-w))) (by fun_prop) ?_
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact le_add_of_le_of_nonneg le_rfl (Real.exp_pos _).le
  · rw [abs_of_nonpos ht]
    refine le_add_of_nonneg_of_le (Real.exp_pos _).le (le_of_eq ?_)
    ring_nf

/-- `|id|` is integrable against any real Gaussian law. -/
theorem integrable_abs_id_gaussianReal {m : ℝ} {v : ℝ≥0} :
    Integrable (fun t : ℝ => |t|) (gaussianReal m v) := by
  refine (integrable_exp_mul_abs_gaussianReal (m := m) (v := v) 1).mono' (by fun_prop) ?_
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_abs, one_mul]
  exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |t|)

/-- An affine combination of absolute coordinates is integrable against a product of
a finite measure and standard Gaussian coordinates. -/
theorem integrable_add_sum_mul_abs_snd {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsFiniteMeasure ν] {M : ℕ} (c : ℝ) (w : Fin M → ℝ) :
    Integrable (fun x : A × (Fin M → ℝ) => c + ∑ k, w k * |x.2 k|)
      (ν.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
  have hξ (k : Fin M) : Integrable (fun x : A × (Fin M → ℝ) => |x.2 k|)
      (ν.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)) :=
    (integrable_comp_eval (integrable_abs_id_gaussianReal (m := 0) (v := 1))).comp_snd ν
  exact (integrable_const c).add (integrable_finsetSum Finset.univ fun k _ =>
    (hξ k).const_mul (w k))

omit [DecidableEq ι] in
/-- `exp (∑ k, w k |ξ k|)` is integrable against i.i.d. standard Gaussians. -/
theorem integrable_exp_sum_mul_abs_pi (w : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => Real.exp (∑ k, w k * |ξ k|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h := Integrable.fintype_prod (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun k (t : ℝ) => Real.exp (w k * |t|)) fun k => integrable_exp_mul_abs_gaussianReal (w k)
  simpa [Real.exp_sum] using h

omit [DecidableEq ι] in
/-- Any measurable functional `F` bounded by `C + ∑ k, w k |x k|` satisfies
`exp (t * F x)` is integrable against standard Gaussian disorder for every `t : ℝ`. -/
theorem integrable_exp_of_linear_bound {F : (ι → ℝ) → ℝ}
    (hFm : AEMeasurable F (Measure.pi fun _ : ι => gaussianReal 0 1))
    {C : ℝ} {w : ι → ℝ} (hF : ∀ x, |F x| ≤ C + ∑ k, w k * |x k|) (t : ℝ) :
    Integrable (fun x => Real.exp (t * F x)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hbound (x : ι → ℝ) : t * F x ≤ |t| * C + ∑ k, (|t| * |w k|) * |x k| := by
    have h1 : t * F x ≤ |t * F x| := le_abs_self _
    have h2 : |t * F x| = |t| * |F x| := abs_mul _ _
    have h3 : |t| * |F x| ≤ |t| * (C + ∑ k, w k * |x k|) :=
      mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    have h4 : |t| * (C + ∑ k, w k * |x k|) = |t| * C + ∑ k, (|t| * w k) * |x k| := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    have h5 : ∑ k, (|t| * w k) * |x k| ≤ ∑ k, (|t| * |w k|) * |x k| := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)) (abs_nonneg _)
    linarith
  have hint : Integrable (fun x : ι → ℝ => Real.exp (|t| * C + ∑ k, (|t| * |w k|) * |x k|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    simp_rw [add_comm (|t| * C), Real.exp_add]
    exact (integrable_exp_sum_mul_abs_pi (fun k => |t| * |w k|)).mul_const _
  refine hint.mono' (hFm.const_mul t).exp.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (hbound x)

end Growth


section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Coordinatewise Stein identity, derivative in the coordinate only.** If `ξ` has independent
coordinates `ξ i ~ 𝒩(0, v i)` and `G` is differentiable along coordinate `j` with derivative
`G' x`, i.e. `HasDerivAt (fun t => G (update x j t)) (G' x) (x j)`, then
`𝔼[ξ j G(ξ)] = v j 𝔼[G'(ξ)]`. Nothing is assumed about the other coordinates. -/
theorem integral_eval_mul_pi_gaussianReal_eq_of_coord (v : ι → ℝ≥0) (j : ι)
    {G G' : (ι → ℝ) → ℝ}
    (hG : ∀ x, HasDerivAt (fun t => G (update x j t)) (G' x) (x j))
    (hxG : Integrable (fun x => x j * G x) (Measure.pi fun i => gaussianReal 0 (v i)))
    (hG' : Integrable G' (Measure.pi fun i => gaussianReal 0 (v i))) :
    ∫ x, x j * G x ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      v j * ∫ x, G' x ∂(Measure.pi fun i => gaussianReal 0 (v i)) := by
  set π := Measure.pi fun i => gaussianReal 0 (v i) with hπ
  have h1 := integrable_update_pi (fun i => gaussianReal 0 (v i)) j hxG
  have h2 := integrable_update_pi (fun i => gaussianReal 0 (v i)) j hG'
  have e1 := integral_pi_eq_integral_update (fun i => gaussianReal 0 (v i)) j hxG
  have e2 := integral_pi_eq_integral_update (fun i => gaussianReal 0 (v i)) j hG'
  rw [e1, e2, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae, h2.prod_right_ae] with x hx1 hx2
  simp only [update_self] at hx1 ⊢
  refine integral_id_mul_gaussianReal_eq (v j) (F := fun t => G (update x j t))
    (F' := fun t => G' (update x j t)) (fun t => ?_) hx1 hx2
  simpa using hG (update x j t)

/-- **Coordinatewise Stein identity for independent centered Gaussians:**
if `ξ` has independent coordinates `ξ i ~ 𝒩(0, v i)`, and `G` has partial derivatives `G' i`, then
`𝔼[ξ j G(ξ)] = v j 𝔼[∂ⱼ G(ξ)]`.  The partial derivatives are expressed through
`HasDerivAt (fun t => G (update x i t)) (G' i x) (x i)`, so that no joint differentiability of
`G` is needed. -/
theorem integral_eval_mul_pi_gaussianReal_eq (v : ι → ℝ≥0) (j : ι)
    {G : (ι → ℝ) → ℝ} {G' : ι → (ι → ℝ) → ℝ}
    (hG : ∀ (x : ι → ℝ) (i : ι), HasDerivAt (fun t => G (update x i t)) (G' i x) (x i))
    (hxG : Integrable (fun x => x j * G x) (Measure.pi fun i => gaussianReal 0 (v i)))
    (hG' : Integrable (G' j) (Measure.pi fun i => gaussianReal 0 (v i))) :
    ∫ x, x j * G x ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      v j * ∫ x, G' j x ∂(Measure.pi fun i => gaussianReal 0 (v i)) :=
  integral_eval_mul_pi_gaussianReal_eq_of_coord v j (fun x => hG x j) hxG hG'


/-- **Stein in one Gaussian coordinate with a spectator.** On `A × (K → ℝ)` with the product of an
`s`-finite measure `μ` on `A` and independent standard Gaussians, `𝔼[ξ_k φ] = 𝔼[∂_k φ]`. -/
theorem integral_snd_apply_mul_prod_pi_gaussianReal_eq {A K : Type*} [MeasurableSpace A]
    [Fintype K] [DecidableEq K] (μ : Measure A) [SFinite μ] (k : K)
    {φ φ' : A × (K → ℝ) → ℝ}
    (hφ : ∀ s ξ, HasDerivAt (fun τ => φ (s, update ξ k τ)) (φ' (s, ξ)) (ξ k))
    (h1 : Integrable (fun y => y.2 k * φ y) (μ.prod (Measure.pi fun _ : K => gaussianReal 0 1)))
    (h2 : Integrable φ' (μ.prod (Measure.pi fun _ : K => gaussianReal 0 1))) :
    ∫ y, y.2 k * φ y ∂(μ.prod (Measure.pi fun _ : K => gaussianReal 0 1)) =
      ∫ y, φ' y ∂(μ.prod (Measure.pi fun _ : K => gaussianReal 0 1)) := by
  rw [integral_prod _ h1, integral_prod _ h2]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae, h2.prod_right_ae] with s hs1 hs2
  have := integral_eval_mul_pi_gaussianReal_eq_of_coord (fun _ : K => (1 : ℝ≥0)) k
    (G := fun ξ => φ (s, ξ)) (G' := fun ξ => φ' (s, ξ)) (fun ξ => hφ s ξ) hs1 hs2
  simpa using this

/-- **Stein in one Gaussian coordinate of one replica.** For independent replicas drawn from
`μ ⊗ (standard Gaussians)^K`, the coordinate `(σ i).2 k` is integrated by parts against a
function that is differentiable along that coordinate (the other coordinates and replicas are
spectators): `𝔼[(σ i).2 k · Φ(σ)] = 𝔼[Φ'(σ)]`. -/
theorem integral_apply_snd_mul_pi_prod_eq {J A K : Type*} [MeasurableSpace A] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] (μ : Measure A) [IsProbabilityMeasure μ]
    (i : J) (k : K) {Φ Φ' : (J → A × (K → ℝ)) → ℝ}
    (hΦ : ∀ σ s ξ, HasDerivAt (fun τ => Φ (update σ i (s, update ξ k τ)))
      (Φ' (update σ i (s, ξ))) (ξ k))
    (h1 : Integrable (fun σ => (σ i).2 k * Φ σ)
      (Measure.pi fun _ : J => μ.prod (Measure.pi fun _ : K => gaussianReal 0 1)))
    (h2 : Integrable Φ'
      (Measure.pi fun _ : J => μ.prod (Measure.pi fun _ : K => gaussianReal 0 1))) :
    ∫ σ, (σ i).2 k * Φ σ ∂(Measure.pi fun _ : J => μ.prod (Measure.pi fun _ : K =>
        gaussianReal 0 1)) =
      ∫ σ, Φ' σ ∂(Measure.pi fun _ : J => μ.prod (Measure.pi fun _ : K => gaussianReal 0 1)) := by
  set base := μ.prod (Measure.pi fun _ : K => gaussianReal 0 1) with hbase
  rw [integral_pi_eq_integral_update (fun _ : J => base) i h1,
    integral_pi_eq_integral_update (fun _ : J => base) i h2]
  refine integral_congr_ae ?_
  filter_upwards [(integrable_update_pi (fun _ : J => base) i h1).prod_right_ae,
    (integrable_update_pi (fun _ : J => base) i h2).prod_right_ae] with σ hσ1 hσ2
  simp only [update_self] at hσ1 ⊢
  exact integral_snd_apply_mul_prod_pi_gaussianReal_eq μ k (φ := fun y => Φ (update σ i y))
    (φ' := fun y => Φ' (update σ i y)) (fun s ξ => hΦ σ s ξ) hσ1 hσ2

end Pi


section Linear

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
/-- The `ℓ¹` norm of `A ξ` is bounded by the weighted `ℓ¹` norm of `ξ`. -/
theorem sum_abs_mulVec_le (A : Matrix κ ι ℝ) (ξ : ι → ℝ) :
    ∑ l, |(A *ᵥ ξ) l| ≤ ∑ k, (∑ l, |A l k|) * |ξ k| := by
  calc ∑ l, |(A *ᵥ ξ) l| ≤ ∑ l, ∑ k, |A l k| * |ξ k| := by
        refine Finset.sum_le_sum fun l _ => ?_
        simp only [mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ = ∑ k, (∑ l, |A l k|) * |ξ k| := by
        rw [Finset.sum_comm]; simp [Finset.sum_mul]

omit [Fintype κ] in
theorem hasDerivAt_mulVec_update [Finite κ] (A : Matrix κ ι ℝ) (x : ι → ℝ) (j : ι) :
    HasDerivAt (fun t => A *ᵥ update x j t) (fun l => A l j) (x j) := by
  have := Fintype.ofFinite κ
  have h : ∀ t, A *ᵥ update x j t = A *ᵥ x + (t - x j) • (fun l => A l j) := by
    intro t
    have hu : update x j t = x + (t - x j) • Pi.single j (1 : ℝ) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [hu, mulVec_add, mulVec_smul, mulVec_single_one]
    rfl
  simp only [h]
  simpa using
    (((hasDerivAt_id (x j)).sub_const (x j)).smul_const (fun l => A l j)).const_add (A *ᵥ x)


omit [DecidableEq ι] in
/-- A measurable function of exponential growth in `‖y‖₁`, composed with a linear map, is
integrable against i.i.d. standard Gaussians. -/
theorem integrable_comp_mulVec_of_exp_growth (A : Matrix κ ι ℝ) {F : (κ → ℝ) → ℝ}
    (hFm : Measurable F) {C c : ℝ} (hF : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) :
    Integrable (fun ξ => F (A *ᵥ ξ)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_exp_sum_mul_abs_pi
    fun k => |c| * ∑ l, |A l k|).const_mul |C|) (hFm.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  refine (hF _).trans ?_
  have hC : 0 ≤ C := by
    have := (abs_nonneg (F 0)).trans (hF 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  rw [abs_of_nonneg hC]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
  calc c * ∑ l, |(A *ᵥ ξ) l| ≤ |c| * ∑ l, |(A *ᵥ ξ) l| :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ ≤ |c| * ∑ k, (∑ l, |A l k|) * |ξ k| :=
        mul_le_mul_of_nonneg_left (sum_abs_mulVec_le A ξ) (abs_nonneg c)
    _ = ∑ k, |c| * (∑ l, |A l k|) * |ξ k| := by
        rw [Finset.mul_sum]; simp [mul_assoc]

omit [DecidableEq ι] in
/-- As `integrable_comp_mulVec_of_exp_growth`, with an extra coordinate factor `ξ j`. -/
theorem integrable_eval_mul_comp_mulVec_of_exp_growth (A : Matrix κ ι ℝ) (j : ι)
    {F : (κ → ℝ) → ℝ} (hFm : Measurable F) {C c : ℝ}
    (hF : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) :
    Integrable (fun ξ : ι → ℝ => ξ j * F (A *ᵥ ξ)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  have hC : 0 ≤ C := by
    have := (abs_nonneg (F 0)).trans (hF 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  refine Integrable.mono' ((integrable_exp_sum_mul_abs_pi
    fun k => |c| * (∑ l, |A l k|) + (if k = j then (1 : ℝ) else 0)).const_mul C)
    ((measurable_pi_apply j).mul (hFm.comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |F (A *ᵥ ξ)| ≤ C * Real.exp (∑ k, |c| * (∑ l, |A l k|) * |ξ k|) := by
    refine (hF _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
    calc c * ∑ l, |(A *ᵥ ξ) l| ≤ |c| * ∑ l, |(A *ᵥ ξ) l| :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ ≤ |c| * ∑ k, (∑ l, |A l k|) * |ξ k| :=
          mul_le_mul_of_nonneg_left (sum_abs_mulVec_le A ξ) (abs_nonneg c)
      _ = ∑ k, |c| * (∑ l, |A l k|) * |ξ k| := by
          rw [Finset.mul_sum]; simp [mul_assoc]
  have h2 : |ξ j| ≤ Real.exp (∑ k, (if k = j then (1 : ℝ) else 0) * |ξ k|) := by
    have : ∑ k, ((if k = j then (1 : ℝ) else 0)) * |ξ k| = |ξ j| := by
      simp
    rw [this]
    linarith [Real.add_one_le_exp (|ξ j|)]
  calc |ξ j| * |F (A *ᵥ ξ)| ≤ Real.exp (∑ k, (if k = j then (1 : ℝ) else 0) * |ξ k|) *
        (C * Real.exp (∑ k, |c| * (∑ l, |A l k|) * |ξ k|)) :=
        mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (∑ k, (|c| * (∑ l, |A l k|) + (if k = j then (1 : ℝ) else 0)) * |ξ k|) := by
        simp only [add_mul, Finset.sum_add_distrib, Real.exp_add]
        ring


omit [DecidableEq ι] in
/-- **Stein's identity for a linear image of i.i.d. standard Gaussians.**  For `g = A ξ` with
`ξ` i.i.d. `𝒩(0, 1)` and `F` differentiable with exponentially bounded value and partial
derivatives, `𝔼[g i F(g)] = ∑ l, (A Aᵀ) i l 𝔼[∂ₗ F(g)]`; `A Aᵀ` is the covariance of `g`. -/
theorem integral_mulVec_mul_comp_mulVec_eq_sum [DecidableEq κ] (A : Matrix κ ι ℝ) (i : κ)
    {F : (κ → ℝ) → ℝ}
    (hF : Differentiable ℝ F) {C c : ℝ} (hFg : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|))
    {D d : κ → ℝ} (hFg' : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤
      D l * Real.exp (d l * ∑ l, |y l|)) :
    ∫ ξ, (A *ᵥ ξ) i * F (A *ᵥ ξ) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∑ l, (A * Aᵀ) i l * ∫ ξ, fderiv ℝ F (A *ᵥ ξ) (Pi.single l 1)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  set π := Measure.pi fun _ : ι => gaussianReal 0 1 with hπ
  have hFm : Measurable F := hF.continuous.measurable
  have hdm : ∀ l, Measurable fun y => fderiv ℝ F y (Pi.single l 1) := fun l =>
    measurable_fderiv_apply_const ℝ F _
  have hint' : ∀ l, Integrable (fun ξ => fderiv ℝ F (A *ᵥ ξ) (Pi.single l 1)) π := fun l =>
    integrable_comp_mulVec_of_exp_growth A (hdm l) (hFg' l)
  have hstein : ∀ j, ∫ ξ, ξ j * F (A *ᵥ ξ) ∂π =
      ∑ l, A l j * ∫ ξ, fderiv ℝ F (A *ᵥ ξ) (Pi.single l 1) ∂π := by
    intro j
    have h := integral_eval_mul_pi_gaussianReal_eq (fun _ : ι => (1 : ℝ≥0)) j
      (G := fun ξ => F (A *ᵥ ξ)) (G' := fun j ξ => ∑ l, A l j * fderiv ℝ F (A *ᵥ ξ) (Pi.single l 1))
      (fun x i => ?_) (integrable_eval_mul_comp_mulVec_of_exp_growth A j hFm hFg)
      (integrable_finsetSum _ fun l _ => (hint' l).const_mul _)
    · simp only [NNReal.coe_one, one_mul] at h
      rw [h, integral_finsetSum _ fun l _ => (hint' l).const_mul _]
      simp only [integral_const_mul]
    · have hl := (hF.differentiableAt (x := A *ᵥ update x i (x i))).hasFDerivAt.comp_hasDerivAt
        (x i) (hasDerivAt_mulVec_update A x i)
      simp only [update_eq_self] at hl
      refine hl.congr_deriv ?_
      have : (fun l => A l i) = ∑ l, A l i • (Pi.single l (1 : ℝ) : κ → ℝ) := by
        ext m; simp [Pi.single_apply]
      rw [this, map_sum]
      simp
  have hexp : ∀ ξ : ι → ℝ, (A *ᵥ ξ) i * F (A *ᵥ ξ) = ∑ j, A i j * (ξ j * F (A *ᵥ ξ)) := by
    intro ξ
    simp only [mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ =>
    (integrable_eval_mul_comp_mulVec_of_exp_growth A j hFm hFg).const_mul _]
  simp only [integral_const_mul]
  rw [Finset.sum_congr rfl fun j _ => by rw [hstein j]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]

end Linear

end ProbabilityTheory
