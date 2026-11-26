/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IntervalDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.OverlapConcentration

/-!
# The Shcherbina--Tirozzi model: the overlaps as functions of the disorder

The Gibbs averages `⟨R_{1,1}⟩` and `⟨R_{1,2}⟩` are Lipschitz functions of the disorder with
Lipschitz constant of order `1 / √N` on a large convex set (Talagrand, Section 3.1,
Lemmas 3.1.13--3.1.15 and Proposition 3.1.16). The gradient bound is stated for the derivative
along an arbitrary line `t ↦ (g + t Δ, g₀ + t Δ₀)` in the disorder space.

## Main declarations

* `SpinGlasses.norm_integral_smul_sub_mean_shcherbinaTirozziGibbs_le`: Lemma 3.1.13.
* `SpinGlasses.abs_sum_deriv_field_mul_sub_le`: Lemma 3.1.14.
* `SpinGlasses.norm_integral_smul_deriv_field_sub_mean_le`: Lemma 3.1.15.
* `SpinGlasses.hasDerivAt_integral_shcherbinaTirozziGibbs_line`: differentiation of a Gibbs
  average along a line of the disorder.
* `SpinGlasses.abs_integral_mul_disorderDerivative_le`: the covariance bound behind
  Proposition 3.1.16.
* `SpinGlasses.exists_hasDerivAt_integral_shcherbinaTirozzi_selfOverlap_line` and
  `SpinGlasses.exists_hasDerivAt_integral_shcherbinaTirozzi_overlap_line`: Proposition 3.1.16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Module Matrix
open scoped RealInnerProductSpace Real Matrix.Norms.L2Operator Topology

namespace SpinGlasses

variable {N M : ℕ}

/-- Under the Gibbs measure the configuration is square integrable (by Lemma 3.1.5). -/
theorem memLp_id_shcherbinaTirozziGibbs {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ} (hu : Measurable u)
    (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ) :
    MemLp (fun σ : EuclideanSpace ℝ (Fin N) => σ) 2
      (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) := by
  have hexp := (integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le (h := h) hκ hu hu0 g g₀).1
  refine (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2 ?_
  refine Integrable.mono' (hexp.const_mul (2 / κ))
    (continuous_norm.pow 2).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 := Real.add_one_le_exp (κ / 2 * ‖σ‖ ^ 2)
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  simp only [id_eq]
  nlinarith

/-- Maurey's inequality for the second moment of a linear image: if the projections `⟪F σ, y⟫`
are `A ‖y‖`-Lipschitz, then `⟨⟪F - ⟨F⟩, y⟫²⟩ ≤ 32 A² ‖y‖² / κ`. -/
private theorem integral_inner_sub_mean_sq_le {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ)
    (g₀ : Fin N → ℝ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : EuclideanSpace ℝ (Fin N) → H} (hFm : ∀ y : H, Measurable fun σ => ⟪F σ, y⟫)
    (hF : Integrable F (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ))
    {A : ℝ} (hA : 0 ≤ A) (hlip : ∀ (y : H) σ τ, |⟪F σ, y⟫ - ⟪F τ, y⟫| ≤ A * ‖y‖ * ‖σ - τ‖)
    (y : H) :
    ∫ σ, ⟪F σ - ∫ τ, F τ
          ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ), y⟫ ^ 2
        ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ≤
      32 * A ^ 2 / κ * ‖y‖ ^ 2 := by
  have key := (integral_sub_integral_pow_shcherbinaTirozziGibbs_le (h := h) hκ hu hu0 g g₀
    (hFm y) (mul_nonneg hA (norm_nonneg y)) (hlip y) 1).2
  have hmean : ∫ τ, ⟪F τ, y⟫ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
      = ⟪∫ τ, F τ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ), y⟫ := by
    simp_rw [real_inner_comm y]
    exact integral_inner hF y
  simp_rw [hmean, ← inner_sub_left] at key
  simp only [mul_one, pow_one, Nat.cast_one] at key
  exact key.trans_eq (by ring)

/-- **Lemma 3.1.13:** for `f ∈ L²(G)`, `‖⟨(σ - ⟨σ⟩) f⟩‖ ≤ √(32 ⟨f²⟩ / κ)`. -/
theorem norm_integral_smul_sub_mean_shcherbinaTirozziGibbs_le {κ h : ℝ} (hκ : 0 < κ)
    {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ)
    (g₀ : Fin N → ℝ) (G : Measure (EuclideanSpace ℝ (Fin N)))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
    {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : MemLp f 2 G) :
    ‖∫ σ, f σ • (σ - ∫ τ, τ ∂G) ∂G‖ ≤ Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) := by
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]; exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  have hid : MemLp (fun σ : EuclideanSpace ℝ (Fin N) => σ) 2 G := by
    rw [hG]; exact memLp_id_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  refine norm_integral_smul_sub_le_of_integral_inner_sq_le hf (hid.sub (memLp_const _))
    fun y => ?_
  have key := integral_inner_sub_mean_sq_le (h := h) hκ hu hu0 g g₀
    (F := fun σ : EuclideanSpace ℝ (Fin N) => σ) (fun y => by fun_prop)
    (hG ▸ hid.integrable one_le_two) (A := 1) zero_le_one (fun y σ τ => by
      rw [← inner_sub_left, one_mul, mul_comm]
      exact abs_real_inner_le_norm _ _) y
  rw [← hG] at key
  simpa using key

/-- The difference of the constraint fields of two configurations is the image of their
difference under the disorder matrix. -/
private theorem sum_sq_field_le (g : Fin M → Fin N → ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    ∑ k, ((Real.sqrt N)⁻¹ * ∑ i, g k i * v i) ^ 2 ≤
      ((Real.sqrt N)⁻¹ * (‖Matrix.of g‖ * ‖v‖)) ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec (Matrix.of g) v
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [EuclideanSpace.real_norm_sq_eq] at h2
  rw [mul_pow]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun k _ => le_of_eq ?_).trans
    (h2.trans_eq (mul_pow _ _ _))) (sq_nonneg _)
  rfl

/-- A function whose derivative is bounded by `D` is `D`-Lipschitz. -/
private theorem abs_sub_le_of_abs_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {D : ℝ}
    (h : ∀ x, |deriv f x| ≤ D) (a b : ℝ) : |f a - f b| ≤ D * |a - b| := by
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hf x)
    (fun x _ => by simpa only [Real.norm_eq_abs] using h x) (Set.mem_univ b) (Set.mem_univ a)
  simpa only [Real.norm_eq_abs] using this

/-- **Lemma 3.1.14:** if `|u''| ≤ D`, then `σ ↦ ∑_k u'(S_k σ) y_k` is Lipschitz with constant
`D ‖g‖ ‖y‖ / √N`, where `‖g‖` is the operator norm of the disorder matrix. -/
theorem abs_sum_deriv_field_mul_sub_le {u : ℝ → ℝ} (hu' : Differentiable ℝ (deriv u)) {D : ℝ}
    (hD : ∀ x, |deriv (deriv u) x| ≤ D) (g : Fin M → Fin N → ℝ) (y : Fin M → ℝ)
    (σ τ : EuclideanSpace ℝ (Fin N)) :
    |(∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) * y k) -
        ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * τ i) * y k| ≤
      D * ((Real.sqrt N)⁻¹ * ‖Matrix.of g‖) * Real.sqrt (∑ k, y k ^ 2) * ‖σ - τ‖ := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  set d : Fin M → ℝ := fun k => (Real.sqrt N)⁻¹ * ∑ i, g k i * (σ - τ) i with hd
  have hdiff : ∀ k, (Real.sqrt N)⁻¹ * ∑ i, g k i * σ i -
      (Real.sqrt N)⁻¹ * ∑ i, g k i * τ i = d k := fun k => by
    rw [hd, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
  have h1 : |(∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) * y k) -
      ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * τ i) * y k| ≤
        D * ∑ k, |d k| * |y k| := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [← sub_mul, abs_mul, ← mul_assoc, ← hdiff]
    exact mul_le_mul_of_nonneg_right (abs_sub_le_of_abs_deriv_le hu' hD _ _) (abs_nonneg _)
  have h2 : ∑ k, |d k| * |y k| ≤
      Real.sqrt (∑ k, d k ^ 2) * Real.sqrt (∑ k, y k ^ 2) := by
    simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun k => |d k|) fun k => |y k|
  have h3 : Real.sqrt (∑ k, d k ^ 2) ≤ (Real.sqrt N)⁻¹ * (‖Matrix.of g‖ * ‖σ - τ‖) := by
    refine (Real.sqrt_le_sqrt (sum_sq_field_le g (σ - τ))).trans_eq (Real.sqrt_sq ?_)
    positivity
  refine h1.trans ((mul_le_mul_of_nonneg_left (h2.trans
    (mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _))) hD0).trans_eq ?_)
  ring

/-- **Lemma 3.1.15:** with `U σ = (u'(S_k σ))_k` and `|u''| ≤ D`, every `f ∈ L²(G)` satisfies
`‖⟨(U - ⟨U⟩) f⟩‖ ≤ (D ‖g‖ / √N) √(32 ⟨f²⟩ / κ)`. -/
theorem norm_integral_smul_deriv_field_sub_mean_le {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (hu' : Differentiable ℝ (deriv u))
    {D : ℝ} (hD : ∀ x, |deriv (deriv u) x| ≤ D) (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ)
    (G : Measure (EuclideanSpace ℝ (Fin N)))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
    {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : MemLp f 2 G)
    (U : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin M))
    (hU : ∀ σ, U σ = WithLp.toLp 2 fun k => deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i)) :
    ‖∫ σ, f σ • (U σ - ∫ τ, U τ ∂G) ∂G‖ ≤
      D * ((Real.sqrt N)⁻¹ * ‖Matrix.of g‖) * Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) := by
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]; exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  have hid : MemLp (fun σ : EuclideanSpace ℝ (Fin N) => σ) 2 G := by
    rw [hG]; exact memLp_id_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  set L : ℝ := D * ((Real.sqrt N)⁻¹ * ‖Matrix.of g‖) with hL
  have hL0 : 0 ≤ L := by positivity
  have hinner : ∀ (y : EuclideanSpace ℝ (Fin M)) σ,
      ⟪U σ, y⟫ = ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) * y k := fun y σ => by
    rw [hU, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hlip : ∀ (y : EuclideanSpace ℝ (Fin M)) σ τ,
      |⟪U σ, y⟫ - ⟪U τ, y⟫| ≤ L * ‖y‖ * ‖σ - τ‖ := fun y σ τ => by
    rw [hinner, hinner, EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    exact abs_sum_deriv_field_mul_sub_le hu' hD g y σ τ
  have hfield : ∀ k : Fin M, Measurable fun σ : EuclideanSpace ℝ (Fin N) =>
      deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) := fun k =>
    hu'.continuous.measurable.comp ((Finset.measurable_sum _ fun i _ =>
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).const_mul _).const_mul _)
  have hUm : Measurable U := by
    have hm : Measurable fun σ : EuclideanSpace ℝ (Fin N) =>
        fun k => deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) :=
      Measurable.of_eval fun k => hfield k
    rw [funext hU]
    exact (WithLp.measurable_toLp 2 (Fin M → ℝ)).comp hm
  have hUnorm : ∀ σ τ, ‖U σ - U τ‖ ≤ L * ‖σ - τ‖ := fun σ τ => by
    rcases eq_or_lt_of_le (norm_nonneg (U σ - U τ)) with h0 | h0
    · rw [← h0]; positivity
    have h1 := hlip (U σ - U τ) σ τ
    rw [← inner_sub_left, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _), sq,
      mul_right_comm] at h1
    exact le_of_mul_le_mul_right h1 h0
  have hUL : MemLp U 2 G := by
    have h1 : MemLp (fun σ : EuclideanSpace ℝ (Fin N) => ‖U 0‖ + L * ‖σ‖) 2 G :=
      (memLp_const _).add (hid.norm.const_mul L)
    refine h1.mono' hUm.aestronglyMeasurable (ae_of_all _ fun σ => ?_)
    have h2 := hUnorm σ 0
    rw [sub_zero] at h2
    exact (norm_le_norm_add_norm_sub' (U σ) (U 0)).trans (add_le_add le_rfl h2)
  have key : ‖∫ σ, f σ • (U σ - ∫ τ, U τ ∂G) ∂G‖ ≤
      Real.sqrt (32 * L ^ 2 / κ * ∫ σ, f σ ^ 2 ∂G) := by
    refine norm_integral_smul_sub_le_of_integral_inner_sq_le hf (hUL.sub (memLp_const _))
      fun y => ?_
    have h := integral_inner_sub_mean_sq_le (h := h) hκ hu hu0 g g₀ (F := U)
      (fun y => by
        simp_rw [hinner y]
        exact Finset.measurable_sum _ fun k _ => (hfield k).mul_const _)
      (hG ▸ hUL.integrable one_le_two) hL0 hlip y
    rwa [← hG] at h
  refine key.trans_eq ?_
  rw [show 32 * L ^ 2 / κ * ∫ σ, f σ ^ 2 ∂G = L ^ 2 * (32 / κ * ∫ σ, f σ ^ 2 ∂G) by ring,
    Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0]

/-- **Differentiation along a line of the disorder.** For an observable of at most quadratic
growth, `t ↦ ⟨Φ⟩_{g + t Δ, g₀ + t Δ₀}` has derivative `⟨Φ X⟩ - ⟨Φ⟩ ⟨X⟩` at `t`, where
`X σ = ∑_k u'(S_k σ) S_k^Δ σ + h ∑_i Δ₀_i σ_i` is the derivative of `-H`. -/
theorem hasDerivAt_integral_shcherbinaTirozziGibbs_line {κ h : ℝ} (hκ : 0 < κ) (hh : 0 ≤ h)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (g Δ : Fin M → Fin N → ℝ) (g₀ Δ₀ : Fin N → ℝ)
    {Φ : EuclideanSpace ℝ (Fin N) → ℝ} (hΦ : Measurable Φ) {c : ℝ}
    (hΦb : ∀ σ, |Φ σ| ≤ c * (1 + ‖σ‖ ^ 2)) (t : ℝ) :
    ∀ X : EuclideanSpace ℝ (Fin N) → ℝ,
      (∀ σ, X σ = (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, (g k i + t * Δ k i) * σ i) *
        ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i) →
      HasDerivAt (fun r => ∫ σ, Φ σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
          (fun k i => g k i + r * Δ k i) (fun i => g₀ i + r * Δ₀ i) σ))
        ((∫ σ, Φ σ * X σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
            (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ)) -
          (∫ σ, Φ σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
              (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ)) *
            ∫ σ, X σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
              (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ)) t := by
  intro X hX
  obtain rfl := funext hX
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hc : 0 ≤ c := by
    have := (abs_nonneg _).trans (hΦb 0)
    simpa using this
  set E := EuclideanSpace ℝ (Fin N)
  set Y : ℝ → E → ℝ := fun r σ =>
    (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, (g k i + r * Δ k i) * σ i) *
      ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i with hY
  set v : Fin M → E := fun k => WithLp.toLp 2 (fun i => (Real.sqrt N)⁻¹ * Δ k i) with hv
  set w : E := WithLp.toLp 2 Δ₀ with hw
  set a₀ : E := WithLp.toLp 2 g₀ with ha₀
  set L : ℝ := D * (∑ k, ‖v k‖) + h * ‖w‖ with hL
  set R : ℝ := h * (‖a₀‖ + (|t| + 1) * ‖w‖) with hR
  have hL0 : 0 ≤ L := by
    have : 0 ≤ ∑ k, ‖v k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity
  have hvS : ∀ (k : Fin M) (σ : E), (Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i = ⟪v k, σ⟫ :=
    fun k σ => (inner_toLp_inv_sqrt_mul_eq _ _ _).symm
  have hwS : ∀ σ : E, ∑ i, Δ₀ i * σ i = ⟪w, σ⟫ := fun σ => by
    have := inner_toLp_inv_sqrt_mul_eq 1 Δ₀ σ
    simpa only [one_mul] using this.symm
  have hYb : ∀ r σ, |Y r σ| ≤ L * ‖σ‖ := fun r σ => by
    have h1 : |∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, (g k i + r * Δ k i) * σ i) *
        ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)| ≤ D * (∑ k, ‖v k‖) * ‖σ‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, hvS, mul_assoc]
      exact mul_le_mul (hD _) (abs_real_inner_le_norm _ _) (abs_nonneg _) hD0
    have h2 : |h * ∑ i, Δ₀ i * σ i| ≤ h * ‖w‖ * ‖σ‖ := by
      rw [abs_mul, abs_of_nonneg hh, hwS, mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hh
    rw [hY, hL, add_mul]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hconf : ∀ r ∈ Metric.ball t 1, ∀ σ : E,
      -shcherbinaTirozziHamiltonian κ h u (fun k i => g k i + r * Δ k i)
        (fun i => g₀ i + r * Δ₀ i) σ ≤ R * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun r hr σ => by
    have hr' : |r| ≤ |t| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hr
      have := abs_sub_abs_le_abs_sub r t
      linarith
    rw [neg_shcherbinaTirozziHamiltonian_eq]
    have h1 : ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, (g k i + r * Δ k i) * σ i) ≤ 0 :=
      Finset.sum_nonpos fun k _ => hu0 _
    have h2 : ⟪(WithLp.toLp 2 (fun i => h * (g₀ i + r * Δ₀ i)) : E), σ⟫ ≤ R * ‖σ‖ := by
      have e : (WithLp.toLp 2 (fun i => h * (g₀ i + r * Δ₀ i)) : E) = h • (a₀ + r • w) := rfl
      refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [e, norm_smul, Real.norm_of_nonneg hh, hR]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) hh
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hr' (norm_nonneg _)
    linarith
  set b : E → ℝ := fun σ => (1 + c) * Real.exp ((R + L + 2) ^ 2 / (2 * κ)) *
    Real.exp (-(κ / 2) * ‖σ‖ ^ 2) with hb
  have hbi : Integrable b := by
    have := integrable_exp_neg_mul_sq_norm_add_inner (E := E) (half_pos hκ) 0
    simp only [inner_zero_left, add_zero] at this
    exact this.const_mul _
  have hder : ∀ (σ : E) (r : ℝ), HasDerivAt (fun q => -shcherbinaTirozziHamiltonian κ h u
      (fun k i => g k i + q * Δ k i) (fun i => g₀ i + q * Δ₀ i) σ) (Y r σ) r := fun σ r => by
    have hlin : ∀ a d : Fin N → ℝ, HasDerivAt (fun q => ∑ i, (a i + q * d i) * σ i)
        (∑ i, d i * σ i) r := fun a d => by
      refine HasDerivAt.fun_sum fun i _ => ?_
      simpa using (((hasDerivAt_id r).mul_const (d i)).const_add (a i)).mul_const (σ i)
    have hsum : HasDerivAt (fun q => ∑ k, u ((Real.sqrt N)⁻¹ *
          ∑ i, (g k i + q * Δ k i) * σ i))
        (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, (g k i + r * Δ k i) * σ i) *
          ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) r :=
      HasDerivAt.fun_sum fun k _ =>
        (hu _).hasDerivAt.comp r ((hlin (g k) (Δ k)).const_mul _)
    have hext := (hlin g₀ Δ₀).const_mul h
    have htot := (hsum.sub_const (κ * ‖σ‖ ^ 2)).add hext
    refine htot.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    simp only [shcherbinaTirozziHamiltonian, Pi.add_apply]
    ring
  have hum : Measurable u := hu.continuous.measurable
  refine hasDerivAt_integral_tilted_of_envelope (μ := volume) (s := Metric.ball t 1)
    (e' := Y) (Metric.ball_mem_nhds t one_pos)
    (fun r _ => (measurable_shcherbinaTirozziHamiltonian_apply κ h hum _ _).neg) ?_ hΦ hbi
    (fun r hr σ => ?_) (fun σ r _ => hder σ r)
  · have hdm : Measurable (deriv u) := measurable_deriv u
    have hσ : ∀ i : Fin N, Measurable fun σ : E => σ i := fun i =>
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable
    refine (Finset.measurable_sum _ fun k _ => (hdm.comp
      ((Finset.measurable_sum _ fun i _ => (hσ i).const_mul _).const_mul _)).mul
        ((Finset.measurable_sum _ fun i _ => (hσ i).const_mul _).const_mul _)).add
      ((Finset.measurable_sum _ fun i _ => (hσ i).const_mul _).const_mul _)
  · obtain ⟨s, hs⟩ : ∃ s : ℝ, ‖σ‖ = s := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := hs ▸ norm_nonneg _
    have h1 : 1 + |Φ σ| ≤ (1 + c) * Real.exp (2 * s) := by
      have h2 : 1 + s ^ 2 ≤ Real.exp (2 * s) := by
        have := Real.quadratic_le_exp_of_nonneg (mul_nonneg zero_le_two hs0)
        nlinarith
      have h3 : 1 + |Φ σ| ≤ (1 + c) * (1 + s ^ 2) := by
        have := hΦb σ
        rw [hs] at this
        nlinarith [sq_nonneg s]
      exact h3.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have h4 : 1 + |Y r σ| ≤ Real.exp (L * s) :=
      hs ▸ (add_le_add le_rfl (hYb r σ)).trans ((add_comm _ _).trans_le (Real.add_one_le_exp _))
    have h5 : -shcherbinaTirozziHamiltonian κ h u (fun k i => g k i + r * Δ k i)
        (fun i => g₀ i + r * Δ₀ i) σ ≤ R * s - κ * s ^ 2 := hs ▸ hconf r hr σ
    refine (mul_le_mul (mul_le_mul h1 h4 (by positivity) (by positivity))
      (Real.exp_le_exp.2 h5) (Real.exp_pos _).le (by positivity)).trans ?_
    rw [hb]
    simp only
    rw [hs, mul_assoc (1 + c), mul_assoc (1 + c), mul_assoc (1 + c), ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith)
    have hsq : (R + L + 2) * s ≤ (R + L + 2) ^ 2 / (2 * κ) + κ / 2 * s ^ 2 := by
      have h0 : 0 ≤ (κ * s - (R + L + 2)) ^ 2 / (2 * κ) :=
        div_nonneg (sq_nonneg _) (by positivity)
      have e : (κ * s - (R + L + 2)) ^ 2 / (2 * κ) =
          (R + L + 2) ^ 2 / (2 * κ) + κ / 2 * s ^ 2 - (R + L + 2) * s := by
        field_simp
        ring
      linarith
    nlinarith

end SpinGlasses
