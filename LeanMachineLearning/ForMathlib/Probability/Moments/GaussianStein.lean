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
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Stein's lemma (Gaussian integration by parts)

For a centered Gaussian `g ~ 𝒩(0, v)` and a differentiable `F`,
`𝔼[g F(g)] = v 𝔼[F'(g)]` (`integral_id_mul_gaussianReal_eq`, Panchenko Eq. (1.19)).  It is
Mathlib's improper integration by parts (`integral_mul_deriv_eq_deriv_mul_of_integrable`) applied
to `F` and the Gaussian density, whose derivative is `-(x / v) p(x)`.

The coordinatewise version for a vector of independent centered Gaussians follows by resampling
one coordinate (`MeasureTheory.integral_pi_eq_integral_update`) and applying the one-dimensional
identity to the slices (`integral_eval_mul_pi_gaussianReal_eq`).

The identities are proved for functions with values in a real normed space
(`integral_id_smul_gaussianReal_eq`, `integral_eval_smul_pi_gaussianReal_eq_of_coord`,
`integral_dotProduct_smul_pi_gaussianReal_eq`); the real-valued statements are their special cases.
-/

@[expose] public section

open MeasureTheory Filter Topology Function Matrix
open scoped NNReal

namespace ProbabilityTheory

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `x • F x` is integrable against a locally finite measure on `ℝ` and `F` is bounded on
`[-1, 1]`, then `F` is integrable. -/
theorem integrable_of_integrable_id_smul {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {F : ℝ → E}
    (hFm : AEStronglyMeasurable F μ) {C : ℝ} (hC : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖F x‖ ≤ C)
    (h : Integrable (fun x => x • F x) μ) : Integrable F μ := by
  have h1 : IntegrableOn F (Set.Icc (-1) 1) μ :=
    IntegrableOn.of_bound measure_Icc_lt_top hFm.restrict C
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hC))
  have h2 : IntegrableOn F (Set.Icc (-1 : ℝ) 1)ᶜ μ := by
    refine Integrable.mono' h.norm.integrableOn hFm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Icc.compl).2 (Eventually.of_forall fun x hx => ?_)
    have hx1 : 1 ≤ |x| := by
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [norm_smul, Real.norm_eq_abs]
    exact le_mul_of_one_le_left (norm_nonneg _) hx1
  have := h1.union h2
  rwa [Set.union_compl_self, integrableOn_univ] at this

end Vector

/-- A continuous function `F` with `x * F x` integrable against a locally finite measure is
integrable. -/
theorem integrable_of_integrable_id_mul {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {F : ℝ → ℝ}
    (hF : Continuous F) (h : Integrable (fun x => x * F x) μ) : Integrable F μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF.continuousOn
  exact integrable_of_integrable_id_smul hF.aestronglyMeasurable hC h

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

/-- **Stein's lemma for vector-valued functions:** for `g ~ 𝒩(0, v)` and `F` with values in a
real normed space, differentiable with `g • F(g)` and `F'(g)` integrable,
`𝔼[g • F(g)] = v • 𝔼[F'(g)]`.  The case `v = 0` is trivial, and for `v ≠ 0` it is integration by
parts against the Gaussian density, whose boundary terms vanish because `F` is integrable against
the density (a consequence of the integrability of `g • F(g)`). -/
theorem integral_id_smul_gaussianReal_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ≥0) {F F' : ℝ → E} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hxF : Integrable (fun x => x • F x) (gaussianReal 0 v))
    (hF' : Integrable F' (gaussianReal 0 v)) :
    ∫ x, x • F x ∂gaussianReal 0 v = (v : ℝ) • ∫ x, F' x ∂gaussianReal 0 v := by
  rcases eq_or_ne v 0 with rfl | hv
  · by_cases hE : CompleteSpace E
    · simp [gaussianReal_zero_var, integral_dirac]
    · simp [integral_of_not_completeSpace hE]
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hFi : Integrable F (gaussianReal 0 v) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hFc.continuousOn
    exact integrable_of_integrable_id_smul hFc.aestronglyMeasurable hC hxF
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hpd := hasDerivAt_gaussianPDFReal_zero hv
  rw [integrable_gaussianReal_iff_smul hv] at hxF hF' hFi
  have h1 : Integrable (fun x => (-(x / v) * gaussianPDFReal 0 v x) • F x) := by
    refine (hxF.smul (-(v : ℝ)⁻¹)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.smul_apply, smul_smul]
    congr 1
    field_simp
  have key : ∫ x, gaussianPDFReal 0 v x • F' x =
      -∫ x, (-(x / v) * gaussianPDFReal 0 v x) • F x :=
    integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (u := gaussianPDFReal 0 v)
      (u' := fun x => -(x / v) * gaussianPDFReal 0 v x) (v := F) (v' := F')
      (fun x _ => hpd x) (fun x _ => hF x) hF' h1 hFi
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv, key,
    ← integral_neg, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [← neg_smul, smul_smul]
  congr 1
  field_simp

/-- **Stein's lemma (Panchenko Eq. (1.19)):** for `g ~ 𝒩(0, v)` and `F` differentiable with
`g F(g)` and `F'(g)` integrable, `𝔼[g F(g)] = v 𝔼[F'(g)]`. -/
theorem integral_id_mul_gaussianReal_eq (v : ℝ≥0) {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hxF : Integrable (fun x => x * F x) (gaussianReal 0 v))
    (hF' : Integrable F' (gaussianReal 0 v)) :
    ∫ x, x * F x ∂gaussianReal 0 v = v * ∫ x, F' x ∂gaussianReal 0 v :=
  integral_id_smul_gaussianReal_eq v hF hxF hF'

/-- **Gaussian integration by parts for an affine composition**, vector-valued:
`𝔼 [z • F(S₀ + c z)] = (v c) • 𝔼 [F'(S₀ + c z)]` for `z ~ 𝒩(0, v)`. -/
theorem integral_id_smul_comp_affine_gaussianReal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ℝ≥0) {F F' : ℝ → E} (hF : ∀ x, HasDerivAt F (F' x) x) (S₀ c : ℝ)
    (h1 : Integrable (fun z => z • F (S₀ + c * z)) (gaussianReal 0 v))
    (h2 : Integrable (fun z => F' (S₀ + c * z)) (gaussianReal 0 v)) :
    ∫ z, z • F (S₀ + c * z) ∂gaussianReal 0 v =
      ((v : ℝ) * c) • ∫ z, F' (S₀ + c * z) ∂gaussianReal 0 v := by
  have hd : ∀ z, HasDerivAt (fun t => F (S₀ + c * t)) (c • F' (S₀ + c * z)) z := fun z => by
    have hl : HasDerivAt (fun t : ℝ => S₀ + c * t) c z := by
      simpa using ((hasDerivAt_id z).const_mul c).const_add S₀
    exact (hF _).scomp z hl
  have h2' : Integrable (fun z => c • F' (S₀ + c * z)) (gaussianReal 0 v) := h2.smul c
  rw [integral_id_smul_gaussianReal_eq v hd h1 h2', integral_smul, smul_smul]

/-- **Gaussian integration by parts for an affine composition:**
`𝔼 [z F(S₀ + c z)] = v c 𝔼 [F'(S₀ + c z)]` for `z ~ 𝒩(0, v)`. -/
theorem integral_id_mul_comp_affine_gaussianReal (v : ℝ≥0) {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (S₀ c : ℝ)
    (h1 : Integrable (fun z => z * F (S₀ + c * z)) (gaussianReal 0 v))
    (h2 : Integrable (fun z => F' (S₀ + c * z)) (gaussianReal 0 v)) :
    ∫ z, z * F (S₀ + c * z) ∂gaussianReal 0 v =
      (v : ℝ) * c * ∫ z, F' (S₀ + c * z) ∂gaussianReal 0 v :=
  integral_id_smul_comp_affine_gaussianReal v hF S₀ c h1 h2

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
a finite measure and independent Gaussian coordinates. -/
theorem integrable_add_sum_mul_abs_snd {A K : Type*} [MeasurableSpace A] [Fintype K]
    (ν : Measure A) [IsFiniteMeasure ν] {m : K → ℝ} {v : K → ℝ≥0} (c : ℝ) (w : K → ℝ) :
    Integrable (fun x : A × (K → ℝ) => c + ∑ k, w k * |x.2 k|)
      (ν.prod (Measure.pi fun k => gaussianReal (m k) (v k))) := by
  have hξ (k : K) : Integrable (fun x : A × (K → ℝ) => |x.2 k|)
      (ν.prod (Measure.pi fun k => gaussianReal (m k) (v k))) :=
    (integrable_comp_eval (μ := fun k => gaussianReal (m k) (v k)) (i := k)
      (integrable_abs_id_gaussianReal (m := m k) (v := v k))).comp_snd ν
  exact (integrable_const c).add (integrable_finsetSum Finset.univ fun k _ =>
    (hξ k).const_mul (w k))

omit [DecidableEq ι] in
/-- `exp (∑ k, w k |ξ k|)` is integrable against independent real Gaussians. -/
theorem integrable_exp_sum_mul_abs_pi_gaussianReal (m : ι → ℝ) (v : ι → ℝ≥0) (w : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => Real.exp (∑ k, w k * |ξ k|))
      (Measure.pi fun k => gaussianReal (m k) (v k)) := by
  have h := Integrable.fintype_prod (μ := fun k => gaussianReal (m k) (v k))
    (f := fun k (t : ℝ) => Real.exp (w k * |t|)) fun k => integrable_exp_mul_abs_gaussianReal (w k)
  simpa [Real.exp_sum] using h

omit [DecidableEq ι] in
/-- `exp (∑ k, w k |ξ k|)` is integrable against i.i.d. standard Gaussians. -/
theorem integrable_exp_sum_mul_abs_pi (w : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => Real.exp (∑ k, w k * |ξ k|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  integrable_exp_sum_mul_abs_pi_gaussianReal (fun _ => 0) (fun _ => 1) w

omit [DecidableEq ι] in
/-- Any measurable functional `F` bounded by `C + ∑ k, w k |x k|` satisfies
`exp (t * F x)` is integrable against independent real Gaussians for every `t : ℝ`. -/
theorem integrable_exp_of_linear_bound {m : ι → ℝ} {v : ι → ℝ≥0} {F : (ι → ℝ) → ℝ}
    (hFm : AEMeasurable F (Measure.pi fun k => gaussianReal (m k) (v k)))
    {C : ℝ} {w : ι → ℝ} (hF : ∀ x, |F x| ≤ C + ∑ k, w k * |x k|) (t : ℝ) :
    Integrable (fun x => Real.exp (t * F x))
      (Measure.pi fun k => gaussianReal (m k) (v k)) := by
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
      (Measure.pi fun k => gaussianReal (m k) (v k)) := by
    simp_rw [add_comm (|t| * C), Real.exp_add]
    exact (integrable_exp_sum_mul_abs_pi_gaussianReal m v (fun k => |t| * |w k|)).mul_const _
  refine hint.mono' (hFm.const_mul t).exp.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (hbound x)

end Growth


section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Coordinatewise Stein identity, derivative in the coordinate only**, vector-valued. If `ξ`
has independent coordinates `ξ i ~ 𝒩(0, v i)` and `G` is differentiable along coordinate `j` with
derivative `G' x`, i.e. `HasDerivAt (fun t => G (update x j t)) (G' x) (x j)`, then
`𝔼[ξ j • G(ξ)] = v j • 𝔼[G'(ξ)]`. Nothing is assumed about the other coordinates. -/
theorem integral_eval_smul_pi_gaussianReal_eq_of_coord {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ι → ℝ≥0) (j : ι) {G G' : (ι → ℝ) → E}
    (hG : ∀ x, HasDerivAt (fun t => G (update x j t)) (G' x) (x j))
    (hxG : Integrable (fun x => x j • G x) (Measure.pi fun i => gaussianReal 0 (v i)))
    (hG' : Integrable G' (Measure.pi fun i => gaussianReal 0 (v i))) :
    ∫ x, x j • G x ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      (v j : ℝ) • ∫ x, G' x ∂(Measure.pi fun i => gaussianReal 0 (v i)) := by
  have h1 := integrable_update_pi (fun i => gaussianReal 0 (v i)) j hxG
  have h2 := integrable_update_pi (fun i => gaussianReal 0 (v i)) j hG'
  have e1 := integral_pi_eq_integral_update (fun i => gaussianReal 0 (v i)) j hxG
  have e2 := integral_pi_eq_integral_update (fun i => gaussianReal 0 (v i)) j hG'
  rw [e1, e2, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae, h2.prod_right_ae] with x hx1 hx2
  simp only [update_self] at hx1 ⊢
  refine integral_id_smul_gaussianReal_eq (v j) (F := fun t => G (update x j t))
    (F' := fun t => G' (update x j t)) (fun t => ?_) hx1 hx2
  simpa using hG (update x j t)

/-- **Coordinatewise Stein identity, derivative in the coordinate only.** If `ξ` has independent
coordinates `ξ i ~ 𝒩(0, v i)` and `G` is differentiable along coordinate `j` with derivative
`G' x`, then `𝔼[ξ j G(ξ)] = v j 𝔼[G'(ξ)]`. -/
theorem integral_eval_mul_pi_gaussianReal_eq_of_coord (v : ι → ℝ≥0) (j : ι)
    {G G' : (ι → ℝ) → ℝ}
    (hG : ∀ x, HasDerivAt (fun t => G (update x j t)) (G' x) (x j))
    (hxG : Integrable (fun x => x j * G x) (Measure.pi fun i => gaussianReal 0 (v i)))
    (hG' : Integrable G' (Measure.pi fun i => gaussianReal 0 (v i))) :
    ∫ x, x j * G x ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      v j * ∫ x, G' x ∂(Measure.pi fun i => gaussianReal 0 (v i)) :=
  integral_eval_smul_pi_gaussianReal_eq_of_coord v j hG hxG hG'

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


/-- **Stein in one Gaussian coordinate with a spectator**, vector-valued. On `A × (K → ℝ)` with
the product of an `s`-finite measure `μ` on `A` and independent Gaussians `ξ k ~ 𝒩(0, v k)`,
`𝔼[ξ k • φ] = v k • 𝔼[∂ₖ φ]`. -/
theorem integral_snd_apply_smul_prod_pi_gaussianReal_eq {E A K : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace A] [Fintype K] [DecidableEq K] (μ : Measure A) [SFinite μ]
    (v : K → ℝ≥0) (k : K) {φ φ' : A × (K → ℝ) → E}
    (hφ : ∀ s ξ, HasDerivAt (fun τ => φ (s, update ξ k τ)) (φ' (s, ξ)) (ξ k))
    (h1 : Integrable (fun y => y.2 k • φ y)
      (μ.prod (Measure.pi fun k => gaussianReal 0 (v k))))
    (h2 : Integrable φ' (μ.prod (Measure.pi fun k => gaussianReal 0 (v k)))) :
    ∫ y, y.2 k • φ y ∂(μ.prod (Measure.pi fun k => gaussianReal 0 (v k))) =
      (v k : ℝ) • ∫ y, φ' y ∂(μ.prod (Measure.pi fun k => gaussianReal 0 (v k))) := by
  rw [integral_prod _ h1, integral_prod _ h2, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae, h2.prod_right_ae] with s hs1 hs2
  exact integral_eval_smul_pi_gaussianReal_eq_of_coord v k
    (G := fun ξ => φ (s, ξ)) (G' := fun ξ => φ' (s, ξ)) (fun ξ => hφ s ξ) hs1 hs2

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
  simpa using integral_snd_apply_smul_prod_pi_gaussianReal_eq μ (fun _ => 1) k hφ h1 h2

/-- **Stein in one Gaussian coordinate of one replica**, vector-valued. For independent replicas
drawn from `μ ⊗ (Gaussians 𝒩(0, v k))`, with `μ` σ-finite, the coordinate `(σ i).2 k` is
integrated by parts against a function that is differentiable along that coordinate (the other
coordinates and replicas are spectators): `𝔼[(σ i).2 k • Φ(σ)] = v k • 𝔼[Φ'(σ)]`. -/
theorem integral_apply_snd_smul_pi_prod_eq {E J A K : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace A] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (μ : Measure A) [SigmaFinite μ] (v : K → ℝ≥0) (i : J) (k : K)
    {Φ Φ' : (J → A × (K → ℝ)) → E}
    (hΦ : ∀ σ s ξ, HasDerivAt (fun τ => Φ (update σ i (s, update ξ k τ)))
      (Φ' (update σ i (s, ξ))) (ξ k))
    (h1 : Integrable (fun σ => (σ i).2 k • Φ σ)
      (Measure.pi fun _ : J => μ.prod (Measure.pi fun k => gaussianReal 0 (v k))))
    (h2 : Integrable Φ'
      (Measure.pi fun _ : J => μ.prod (Measure.pi fun k => gaussianReal 0 (v k)))) :
    ∫ σ, (σ i).2 k • Φ σ
        ∂(Measure.pi fun _ : J => μ.prod (Measure.pi fun k => gaussianReal 0 (v k))) =
      (v k : ℝ) • ∫ σ, Φ' σ
        ∂(Measure.pi fun _ : J => μ.prod (Measure.pi fun k => gaussianReal 0 (v k))) := by
  set γ : Measure (K → ℝ) := Measure.pi fun k => gaussianReal 0 (v k) with hγ
  set base := μ.prod γ with hbase
  have : Unique {j // j = i} := ⟨⟨⟨i, rfl⟩⟩, fun x => Subtype.ext x.2⟩
  -- split off the replica `i`, and then its Gaussian coordinates
  set T : (({j // ¬j = i} → A × (K → ℝ)) × A) × (K → ℝ) ≃ᵐ (J → A × (K → ℝ)) :=
    MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodComm.trans
      (((MeasurableEquiv.piUnique fun _ : {j // j = i} => A × (K → ℝ)).symm.prodCongr
        (MeasurableEquiv.refl _)).trans
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => A × (K → ℝ)) fun j => j = i).symm))
    with hT
  set ν : Measure ({j // ¬j = i} → A × (K → ℝ)) := Measure.pi fun _ => base with hν
  have hmp : MeasurePreserving T ((ν.prod μ).prod γ) (Measure.pi fun _ : J => base) := by
    have h1 : MeasurePreserving MeasurableEquiv.prodAssoc ((ν.prod μ).prod γ) (ν.prod base) :=
      measurePreserving_prodAssoc ν μ γ
    have h2 : MeasurePreserving MeasurableEquiv.prodComm (ν.prod base) (base.prod ν) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving
        ((MeasurableEquiv.piUnique fun _ : {j // j = i} => A × (K → ℝ)).symm.prodCongr
          (MeasurableEquiv.refl ({j // ¬j = i} → A × (K → ℝ))))
        (base.prod ν) ((Measure.pi fun _ : {j // j = i} => base).prod ν) :=
      ((measurePreserving_piUnique fun _ : {j // j = i} => base).symm _).prod
        (MeasurePreserving.id ν)
    have h4 : MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => A × (K → ℝ)) fun j => j = i).symm
        ((Measure.pi fun _ : {j // j = i} => base).prod ν) (Measure.pi fun _ : J => base) := by
      convert (measurePreserving_piEquivPiSubtypeProd (fun _ : J => base) fun j => j = i).symm _
    exact h1.trans (h2.trans (h3.trans h4))
  have hTi : ∀ y, T y i = (y.1.2, y.2) := fun y => by
    simp [hT, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      MeasurableEquiv.piUnique, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
      MeasurableEquiv.prodCongr]
  have hTne : ∀ y y' : (({j // ¬j = i} → A × (K → ℝ)) × A) × (K → ℝ), y.1.1 = y'.1.1 →
      ∀ j, j ≠ i → T y j = T y' j := fun y y' h j hj => by
    simp [hT, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr, hj, h]
  have hupd : ∀ r a ξ ξ', T ((r, a), ξ') = update (T ((r, a), ξ)) i (a, ξ') := by
    intro r a ξ ξ'
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [update_self, hTi]
    · rw [update_of_ne hj]
      exact hTne ((r, a), ξ') ((r, a), ξ) rfl j hj
  have e : ∀ f : (J → A × (K → ℝ)) → E, ∫ σ, f σ ∂(Measure.pi fun _ : J => base) =
      ∫ y, f (T y) ∂((ν.prod μ).prod γ) := fun f =>
    (hmp.integral_comp T.measurableEmbedding f).symm
  have hcoord : ∀ y, (T y i).2 k = y.2 k := fun y => by rw [hTi]
  have h1' := (hmp.integrable_comp_emb T.measurableEmbedding).2 h1
  have h2' := (hmp.integrable_comp_emb T.measurableEmbedding).2 h2
  simp only [Function.comp_def, hcoord] at h1' h2'
  rw [e, e]
  simp only [hcoord]
  refine integral_snd_apply_smul_prod_pi_gaussianReal_eq _ v k (φ := fun y => Φ (T y))
    (φ' := fun y => Φ' (T y)) (fun s ξ => ?_) h1' h2'
  obtain ⟨r, a⟩ := s
  have h := hΦ (T ((r, a), ξ)) a ξ
  rw [← hupd r a ξ ξ] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun τ => by
    exact congrArg Φ (hupd r a ξ (update ξ k τ)))

/-- **Stein in one Gaussian coordinate of one replica.** For independent replicas drawn from
`μ ⊗ (standard Gaussians)^K`, with `μ` σ-finite, `𝔼[(σ i).2 k · Φ(σ)] = 𝔼[Φ'(σ)]`. -/
theorem integral_apply_snd_mul_pi_prod_eq {J A K : Type*} [MeasurableSpace A] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] (μ : Measure A) [SigmaFinite μ]
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
  simpa using integral_apply_snd_smul_pi_prod_eq μ (fun _ => 1) i k hΦ h1 h2

end Pi


section Linear

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
/-- The weighted `ℓ¹` norm of `A ξ` is bounded by a weighted `ℓ¹` norm of `ξ`. -/
theorem sum_mul_abs_mulVec_le (A : Matrix κ ι ℝ) {w : κ → ℝ} (hw : ∀ l, 0 ≤ w l) (ξ : ι → ℝ) :
    ∑ l, w l * |(A *ᵥ ξ) l| ≤ ∑ k, (∑ l, w l * |A l k|) * |ξ k| := by
  calc ∑ l, w l * |(A *ᵥ ξ) l| ≤ ∑ l, ∑ k, w l * (|A l k| * |ξ k|) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hw l)
        simp only [mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ = ∑ k, (∑ l, w l * |A l k|) * |ξ k| := by
        rw [Finset.sum_comm]; simp [Finset.sum_mul, mul_assoc]

omit [DecidableEq ι] in
/-- The `ℓ¹` norm of `A ξ` is bounded by the weighted `ℓ¹` norm of `ξ`. -/
theorem sum_abs_mulVec_le (A : Matrix κ ι ℝ) (ξ : ι → ℝ) :
    ∑ l, |(A *ᵥ ξ) l| ≤ ∑ k, (∑ l, |A l k|) * |ξ k| := by
  simpa only [one_mul] using sum_mul_abs_mulVec_le A (w := fun _ => 1) (fun _ => zero_le_one) ξ

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
/-- `exp (∑ l, c l |(A ξ) l|)` is at most `exp` of a weighted `ℓ¹` norm of `ξ`. -/
theorem exp_sum_mul_abs_mulVec_le (A : Matrix κ ι ℝ) (c : κ → ℝ) (ξ : ι → ℝ) :
    Real.exp (∑ l, c l * |(A *ᵥ ξ) l|) ≤
      Real.exp (∑ k, (∑ l, |c l| * |A l k|) * |ξ k|) :=
  Real.exp_le_exp.2 <| (Finset.sum_le_sum fun l _ =>
    mul_le_mul_of_nonneg_right (le_abs_self (c l)) (abs_nonneg _)).trans
      (sum_mul_abs_mulVec_le A (fun l => abs_nonneg (c l)) ξ)

omit [DecidableEq ι] in
/-- A function with `|F y| ≤ C exp (∑ l, c l |y l|)`, composed with a linear map, is integrable
against i.i.d. standard Gaussians. -/
theorem integrable_comp_mulVec_of_exp_sum_growth (A : Matrix κ ι ℝ) {F : (κ → ℝ) → ℝ}
    (hFm : AEStronglyMeasurable (fun ξ => F (A *ᵥ ξ))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    {C : ℝ} {c : κ → ℝ} (hF : ∀ y, |F y| ≤ C * Real.exp (∑ l, c l * |y l|)) :
    Integrable (fun ξ => F (A *ᵥ ξ)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg (F 0)).trans (hF 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  refine Integrable.mono' ((integrable_exp_sum_mul_abs_pi
    fun k => ∑ l, |c l| * |A l k|).const_mul C) hFm (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  exact (hF _).trans (mul_le_mul_of_nonneg_left (exp_sum_mul_abs_mulVec_le A c ξ) hC)

omit [DecidableEq ι] in
/-- A measurable function of exponential growth in `‖y‖₁`, composed with a linear map, is
integrable against i.i.d. standard Gaussians. -/
theorem integrable_comp_mulVec_of_exp_growth (A : Matrix κ ι ℝ) {F : (κ → ℝ) → ℝ}
    (hFm : Measurable F) {C c : ℝ} (hF : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) :
    Integrable (fun ξ => F (A *ᵥ ξ)) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  integrable_comp_mulVec_of_exp_sum_growth A (c := fun _ => c)
    (hFm.comp (by fun_prop)).aestronglyMeasurable
    fun y => by simpa only [Finset.mul_sum] using hF y

omit [DecidableEq ι] in
/-- As `integrable_comp_mulVec_of_exp_sum_growth`, with an extra coordinate factor `ξ j`. -/
theorem integrable_eval_mul_comp_mulVec_of_exp_sum_growth (A : Matrix κ ι ℝ) (j : ι)
    {F : (κ → ℝ) → ℝ}
    (hFm : AEStronglyMeasurable (fun ξ => F (A *ᵥ ξ))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    {C : ℝ} {c : κ → ℝ} (hF : ∀ y, |F y| ≤ C * Real.exp (∑ l, c l * |y l|)) :
    Integrable (fun ξ : ι → ℝ => ξ j * F (A *ᵥ ξ)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  have hC : 0 ≤ C := by
    have := (abs_nonneg (F 0)).trans (hF 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  refine Integrable.mono' ((integrable_exp_sum_mul_abs_pi
    fun k => (∑ l, |c l| * |A l k|) + (if k = j then (1 : ℝ) else 0)).const_mul C)
    ((measurable_pi_apply j).aestronglyMeasurable.mul hFm) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |F (A *ᵥ ξ)| ≤ C * Real.exp (∑ k, (∑ l, |c l| * |A l k|) * |ξ k|) :=
    (hF _).trans (mul_le_mul_of_nonneg_left (exp_sum_mul_abs_mulVec_le A c ξ) hC)
  have h2 : |ξ j| ≤ Real.exp (∑ k, (if k = j then (1 : ℝ) else 0) * |ξ k|) := by
    have : ∑ k, ((if k = j then (1 : ℝ) else 0)) * |ξ k| = |ξ j| := by
      simp
    rw [this]
    linarith [Real.add_one_le_exp (|ξ j|)]
  calc |ξ j| * |F (A *ᵥ ξ)| ≤ Real.exp (∑ k, (if k = j then (1 : ℝ) else 0) * |ξ k|) *
        (C * Real.exp (∑ k, (∑ l, |c l| * |A l k|) * |ξ k|)) :=
        mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (∑ k, ((∑ l, |c l| * |A l k|) + (if k = j then (1 : ℝ) else 0)) * |ξ k|) := by
        simp only [add_mul, Finset.sum_add_distrib, Real.exp_add]
        ring

omit [DecidableEq ι] in
/-- As `integrable_comp_mulVec_of_exp_growth`, with an extra coordinate factor `ξ j`. -/
theorem integrable_eval_mul_comp_mulVec_of_exp_growth (A : Matrix κ ι ℝ) (j : ι)
    {F : (κ → ℝ) → ℝ} (hFm : Measurable F) {C c : ℝ}
    (hF : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) :
    Integrable (fun ξ : ι → ℝ => ξ j * F (A *ᵥ ξ)) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  integrable_eval_mul_comp_mulVec_of_exp_sum_growth A j (c := fun _ => c)
    (hFm.comp (by fun_prop)).aestronglyMeasurable
    fun y => by simpa only [Finset.mul_sum] using hF y

/-- **Stein's identity along a direction.** For `ξ` with independent coordinates
`ξ j ~ 𝒩(0, v j)` and a differentiable vector-valued `G`,
`𝔼[(a ⬝ᵥ ξ) • G(ξ)] = 𝔼[DG(ξ) (v * a)]`. -/
theorem integral_dotProduct_smul_pi_gaussianReal_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ι → ℝ≥0) (a : ι → ℝ) {G : (ι → ℝ) → E} (hG : Differentiable ℝ G)
    (hxG : ∀ j, Integrable (fun x => x j • G x) (Measure.pi fun i => gaussianReal 0 (v i)))
    (hG' : ∀ j, Integrable (fun x => fderiv ℝ G x (Pi.single j 1))
      (Measure.pi fun i => gaussianReal 0 (v i))) :
    ∫ x, (a ⬝ᵥ x) • G x ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      ∫ x, fderiv ℝ G x (fun j => v j * a j) ∂(Measure.pi fun i => gaussianReal 0 (v i)) := by
  set π := Measure.pi fun i => gaussianReal 0 (v i) with hπ
  have hstein : ∀ j, ∫ x, x j • G x ∂π = (v j : ℝ) • ∫ x, fderiv ℝ G x (Pi.single j 1) ∂π := by
    refine fun j => integral_eval_smul_pi_gaussianReal_eq_of_coord v j (fun x => ?_) (hxG j) (hG' j)
    have h := (hG (update x j (x j))).hasFDerivAt.comp_hasDerivAt (x j)
      (hasDerivAt_update x j (x j))
    rwa [update_eq_self] at h
  have hl : ∀ x : ι → ℝ, (a ⬝ᵥ x) • G x = ∑ j, a j • (x j • G x) := fun x => by
    simp only [dotProduct, Finset.sum_smul, smul_smul]
  have hr : ∀ x : ι → ℝ, fderiv ℝ G x (fun j => v j * a j) =
      ∑ j, (v j * a j : ℝ) • fderiv ℝ G x (Pi.single j 1) := fun x => by
    have : (fun j => (v j : ℝ) * a j) = ∑ j, (v j * a j : ℝ) • Pi.single j (1 : ℝ) := by
      ext m; simp [Pi.single_apply]
    rw [this, map_sum]
    simp only [map_smul]
  simp only [hl, hr]
  have hi1 : ∀ j ∈ Finset.univ, Integrable (fun x => a j • (x j • G x)) π := fun j _ =>
    (hxG j).smul (a j)
  have hi2 : ∀ j ∈ Finset.univ,
      Integrable (fun x => (v j * a j : ℝ) • fderiv ℝ G x (Pi.single j 1)) π := fun j _ =>
    (hG' j).smul (v j * a j : ℝ)
  rw [integral_finsetSum _ hi1, integral_finsetSum _ hi2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul, integral_smul, hstein, smul_smul, mul_comm]

omit [DecidableEq ι] in
/-- **Stein's identity for a linear image of i.i.d. standard Gaussians**, with coordinatewise
exponential growth.  For `g = A ξ` with `ξ` i.i.d. `𝒩(0, 1)` and `F` differentiable with
exponentially bounded value and partial derivatives,
`𝔼[g i F(g)] = ∑ l, (A Aᵀ) i l 𝔼[∂ₗ F(g)]`; `A Aᵀ` is the covariance of `g`. -/
theorem integral_mulVec_mul_comp_mulVec_eq_sum_of_exp_sum_growth (A : Matrix κ ι ℝ)
    (i : κ) [DecidableEq κ] {F : (κ → ℝ) → ℝ} (hF : Differentiable ℝ F) {C : ℝ} {c : κ → ℝ}
    (hFg : ∀ y, |F y| ≤ C * Real.exp (∑ l, c l * |y l|)) {D : κ → ℝ} {d : κ → κ → ℝ}
    (hFg' : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l * Real.exp (∑ m, d l m * |y m|)) :
    ∫ ξ, (A *ᵥ ξ) i * F (A *ᵥ ξ) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∑ l, (A * Aᵀ) i l * ∫ ξ, fderiv ℝ F (A *ᵥ ξ) (Pi.single l 1)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  set π := Measure.pi fun _ : ι => gaussianReal 0 1 with hπ
  set L : (ι → ℝ) →L[ℝ] (κ → ℝ) := LinearMap.toContinuousLinearMap A.mulVecLin with hL
  have hLa : ∀ x, L x = A *ᵥ x := fun x => rfl
  have hFm : AEStronglyMeasurable (fun ξ => F (A *ᵥ ξ)) π :=
    (hF.continuous.comp L.continuous).aestronglyMeasurable
  have hint' : ∀ l, Integrable (fun ξ => fderiv ℝ F (A *ᵥ ξ) (Pi.single l 1)) π := fun l =>
    integrable_comp_mulVec_of_exp_sum_growth A
      ((measurable_fderiv_apply_const ℝ F _).comp L.continuous.measurable).aestronglyMeasurable
      (hFg' l)
  have hsum : ∀ (w : κ → ℝ) (y : κ → ℝ),
      fderiv ℝ F y w = ∑ l, w l * fderiv ℝ F y (Pi.single l 1) := fun w y => by
    have : w = ∑ l, w l • (Pi.single l (1 : ℝ) : κ → ℝ) := by
      ext m; simp [Pi.single_apply]
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hcomp : ∀ x w, fderiv ℝ (fun ξ => F (A *ᵥ ξ)) x w =
      ∑ l, (A *ᵥ w) l * fderiv ℝ F (A *ᵥ x) (Pi.single l 1) := fun x w => by
    have h := ((hF (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
    rw [show (fun ξ => F (A *ᵥ ξ)) = F ∘ L from rfl, h, ContinuousLinearMap.comp_apply,
      hsum]
    rfl
  have h := integral_dotProduct_smul_pi_gaussianReal_eq (fun _ : ι => (1 : ℝ≥0)) (A i)
    (G := fun ξ => F (A *ᵥ ξ)) (hF.comp L.differentiable)
    (fun j => integrable_eval_mul_comp_mulVec_of_exp_sum_growth A j hFm hFg)
    (fun j => by
      simp only [hcomp]
      exact integrable_finsetSum _ fun l _ => (hint' l).const_mul _)
  simp only [NNReal.coe_one, one_mul, smul_eq_mul, hcomp] at h
  have hcov : ∀ l, (A *ᵥ A i) l = (A * Aᵀ) i l := fun l => by
    simp only [mulVec, dotProduct, Matrix.mul_apply, transpose_apply, mul_comm]
  simp only [hcov] at h
  refine h.trans ?_
  rw [integral_finsetSum _ fun l _ => (hint' l).const_mul _]
  simp only [integral_const_mul]

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
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
  integral_mulVec_mul_comp_mulVec_eq_sum_of_exp_sum_growth A i hF (c := fun _ => c)
    (fun y => by simpa only [Finset.mul_sum] using hFg y) (d := fun l _ => d l)
    fun l y => by simpa only [Finset.mul_sum] using hFg' l y

end Linear

/-- **Stein identity for one entry of a Gaussian matrix**, vector-valued: if the entries
`x i j ~ 𝒩(0, v i j)` are independent and `G` is differentiable along the entry `(i, j)`, then
`𝔼 [x i j • G x] = v i j • 𝔼 [∂ G x]`. -/
theorem integral_apply_apply_smul_pi_pi_gaussianReal_eq {E ι κ : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (v : ι → κ → ℝ≥0)
    (i : ι) (j : κ) {G G' : (ι → κ → ℝ) → E}
    (hG : ∀ x, HasDerivAt (fun t => G (update x i (update (x i) j t))) (G' x) (x i j))
    (hxG : Integrable (fun x => x i j • G x)
      (Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j)))
    (hG' : Integrable G' (Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j))) :
    ∫ x, x i j • G x ∂(Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j)) =
      (v i j : ℝ) •
        ∫ x, G' x ∂(Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j)) := by
  set γ : ι → Measure (κ → ℝ) := fun i => Measure.pi fun j => gaussianReal 0 (v i j) with hγ
  have h1 := integrable_update_pi γ i hxG
  have h2 := integrable_update_pi γ i hG'
  rw [integral_pi_eq_integral_update γ i hxG, integral_pi_eq_integral_update γ i hG',
    ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae, h2.prod_right_ae] with x hx1 hx2
  simp only [update_self] at hx1 ⊢
  exact integral_eval_smul_pi_gaussianReal_eq_of_coord (v i) j
    (G := fun y => G (update x i y)) (G' := fun y => G' (update x i y)) (fun y => by
      have := hG (update x i y)
      simpa only [update_self, update_idem] using this) hx1 hx2

/-- **Stein identity for one entry of a Gaussian matrix**: if the entries `x i j ~ 𝒩(0, v i j)`
are independent and `G` is differentiable along the entry `(i, j)`, then
`𝔼 [x i j G x] = v i j 𝔼 [∂ G x]`. -/
theorem integral_apply_apply_mul_pi_pi_gaussianReal_eq {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (v : ι → κ → ℝ≥0) (i : ι) (j : κ)
    {G G' : (ι → κ → ℝ) → ℝ}
    (hG : ∀ x, HasDerivAt (fun t => G (update x i (update (x i) j t))) (G' x) (x i j))
    (hxG : Integrable (fun x => x i j * G x)
      (Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j)))
    (hG' : Integrable G' (Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j))) :
    ∫ x, x i j * G x ∂(Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j)) =
      v i j * ∫ x, G' x ∂(Measure.pi fun i => Measure.pi fun j => gaussianReal 0 (v i j)) :=
  integral_apply_apply_smul_pi_pi_gaussianReal_eq v i j hG hxG hG'

end ProbabilityTheory
