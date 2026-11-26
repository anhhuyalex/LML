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

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {N M : ℕ}

/-- The covariance bound for a Lipschitz vector function of the configuration under the Gibbs
measure: `‖⟨f (F - ⟨F⟩)⟩‖ ≤ A √(32 ⟨f²⟩ / κ)`. -/
private theorem norm_integral_smul_sub_mean_le_of_lipschitz {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ)
    (g₀ : Fin N → ℝ) (G : Measure (ℝ^N))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : ℝ^N → V} (hFm : StronglyMeasurable F) (hF : MemLp F 2 G) {A : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ σ τ, ‖F σ - F τ‖ ≤ A * ‖σ - τ‖) {f : ℝ^N → ℝ} (hf : MemLp f 2 G) :
    ‖∫ σ, f σ • (F σ - ∫ τ, F τ ∂G) ∂G‖ ≤ A * Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) := by
  have hum := hu.measurable_of_univ
  have key := norm_integral_smul_sub_integral_le_of_lipschitz (μ₀ := volume) (C := Set.univ)
    (H := shcherbinaTirozziHamiltonian κ h u g g₀) convex_univ MeasurableSet.univ
    (NeZero.ne _) (measurable_shcherbinaTirozziHamiltonian_apply κ h hum g g₀)
    (integrableOn_univ.2 (integrable_exp_neg_shcherbinaTirozziHamiltonian hκ hum hu0 g g₀))
    (fun x _ y _ => shcherbinaTirozziHamiltonian_midpoint_gap κ h hu g g₀ x y) hκ hFm
    (A := A) (f := f)
  simp only [Measure.restrict_univ, ← hG] at key
  exact key hF hA (fun x _ y _ => hlip x y) hf

/-- **Lemma 3.1.13:** for `f ∈ L²(G)`, `‖⟨(σ - ⟨σ⟩) f⟩‖ ≤ √(32 ⟨f²⟩ / κ)`. -/
theorem norm_integral_smul_sub_mean_shcherbinaTirozziGibbs_le {κ h : ℝ} (hκ : 0 < κ)
    {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ)
    (g₀ : Fin N → ℝ) (G : Measure (ℝ^N))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
    {f : ℝ^N → ℝ} (hf : MemLp f 2 G) :
    ‖∫ σ, f σ • (σ - ∫ τ, τ ∂G) ∂G‖ ≤ Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) := by
  have hid : MemLp (fun σ : ℝ^N => σ) 2 G := by
    rw [hG]; exact memLp_id_shcherbinaTirozziGibbs hκ hu.measurable_of_univ hu0 g g₀
  have key := norm_integral_smul_sub_mean_le_of_lipschitz (h := h) hκ hu hu0 g g₀ G hG
    (F := fun σ : ℝ^N => σ) stronglyMeasurable_id hid zero_le_one
    (fun σ τ => (one_mul _).ge) hf
  rwa [one_mul] at key

/-- The difference of the constraint fields of two configurations is the image of their
difference under the disorder matrix. -/
private theorem sum_sq_field_le (g : Fin M → Fin N → ℝ) (v : ℝ^N) :
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
    (σ τ : ℝ^N) :
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
    (G : Measure (ℝ^N))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
    {f : ℝ^N → ℝ} (hf : MemLp f 2 G)
    (U : ℝ^N → ℝ^M)
    (hU : ∀ σ, U σ = WithLp.toLp 2 fun k => deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i)) :
    ‖∫ σ, f σ • (U σ - ∫ τ, U τ ∂G) ∂G‖ ≤
      D * ((Real.sqrt N)⁻¹ * ‖Matrix.of g‖) * Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) := by
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]; exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  have hid : MemLp (fun σ : ℝ^N => σ) 2 G := by
    rw [hG]; exact memLp_id_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  set L : ℝ := D * ((Real.sqrt N)⁻¹ * ‖Matrix.of g‖) with hL
  have hL0 : 0 ≤ L := by positivity
  have hinner : ∀ (y : ℝ^M) σ,
      ⟪U σ, y⟫ = ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) * y k := fun y σ => by
    rw [hU, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hlip : ∀ (y : ℝ^M) σ τ,
      |⟪U σ, y⟫ - ⟪U τ, y⟫| ≤ L * ‖y‖ * ‖σ - τ‖ := fun y σ τ => by
    rw [hinner, hinner, EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    exact abs_sum_deriv_field_mul_sub_le hu' hD g y σ τ
  have hfield : ∀ k : Fin M, Measurable fun σ : ℝ^N =>
      deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) := fun k =>
    hu'.continuous.measurable.comp ((Finset.measurable_sum _ fun i _ =>
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).const_mul _).const_mul _)
  have hUm : Measurable U := by
    have hm : Measurable fun σ : ℝ^N =>
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
    have h1 : MemLp (fun σ : ℝ^N => ‖U 0‖ + L * ‖σ‖) 2 G :=
      (memLp_const _).add (hid.norm.const_mul L)
    refine h1.mono' hUm.aestronglyMeasurable (ae_of_all _ fun σ => ?_)
    have h2 := hUnorm σ 0
    rw [sub_zero] at h2
    exact (norm_le_norm_add_norm_sub' (U σ) (U 0)).trans (add_le_add le_rfl h2)
  exact norm_integral_smul_sub_mean_le_of_lipschitz (h := h) hκ hu hu0 g g₀ G hG
    hUm.stronglyMeasurable hUL hL0 hUnorm hf

/-- **Differentiation along a line of the disorder.** For an observable of at most quadratic
growth, `t ↦ ⟨F⟩_{g + t Δ, g₀ + t Δ₀}` has derivative `⟨F X⟩ - ⟨F⟩ ⟨X⟩` at `t`, where
`X σ = ∑_k u'(S_k σ) S_k^Δ σ + h ∑_i Δ₀_i σ_i` is the derivative of `-H`. -/
theorem hasDerivAt_integral_shcherbinaTirozziGibbs_line {κ h : ℝ} (hκ : 0 < κ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (g Δ : Fin M → Fin N → ℝ) (g₀ Δ₀ : Fin N → ℝ)
    {F : ℝ^N → ℝ} (hF : Measurable F) {c : ℝ}
    (hFb : ∀ σ, |F σ| ≤ c * (1 + ‖σ‖ ^ 2)) (t : ℝ) :
    ∀ X : ℝ^N → ℝ,
      (∀ σ, X σ = (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, (g k i + t * Δ k i) * σ i) *
        ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i) →
      HasDerivAt (fun r => ∫ σ, F σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
          (fun k i => g k i + r * Δ k i) (fun i => g₀ i + r * Δ₀ i) σ))
        ((∫ σ, F σ * X σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
            (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ)) -
          (∫ σ, F σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
              (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ)) *
            ∫ σ, X σ ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
              (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ)) t := by
  intro X hX
  -- the model is the case `v k = g k / √N`, `a = h g₀` of the general ridge potential
  set v : Fin M → ℝ^N := fun k => WithLp.toLp 2 (fun i => (Real.sqrt N)⁻¹ * g k i) with hv
  set w : Fin M → ℝ^N := fun k => WithLp.toLp 2 (fun i => (Real.sqrt N)⁻¹ * Δ k i) with hw
  set a : ℝ^N := WithLp.toLp 2 (fun i => h * g₀ i) with ha
  set c' : ℝ^N := WithLp.toLp 2 (fun i => h * Δ₀ i) with hc'
  have hline : ∀ (r : ℝ) (k : Fin M) (σ : ℝ^N), ⟪v k + r • w k, σ⟫ =
      (Real.sqrt N)⁻¹ * ∑ i, (g k i + r * Δ k i) * σ i := fun r k σ => by
    rw [← inner_toLp_inv_sqrt_mul_eq]
    congr 1
    ext i
    change (Real.sqrt N)⁻¹ * g k i + r * ((Real.sqrt N)⁻¹ * Δ k i) =
      (Real.sqrt N)⁻¹ * (g k i + r * Δ k i)
    ring
  have hH : ∀ r : ℝ, (fun σ : ℝ^N => -shcherbinaTirozziHamiltonian κ h u
        (fun k i => g k i + r * Δ k i) (fun i => g₀ i + r * Δ₀ i) σ) =
      fun σ => (∑ k, u ⟪v k + r • w k, σ⟫) - κ * ‖σ‖ ^ 2 + ⟪a + r • c', σ⟫ := fun r => by
    funext σ
    have e : a + r • c' = WithLp.toLp 2 (fun i => h * (g₀ i + r * Δ₀ i)) := by
      ext i
      change h * g₀ i + r * (h * Δ₀ i) = h * (g₀ i + r * Δ₀ i)
      ring
    rw [neg_shcherbinaTirozziHamiltonian_eq, e]
    simp only [hline]
  have hXe : X = fun σ => (∑ k, deriv u ⟪v k + t • w k, σ⟫ * ⟪w k, σ⟫) + ⟪c', σ⟫ := by
    funext σ
    have h1 : ∀ k, ⟪w k, σ⟫ = (Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i := fun k =>
      inner_toLp_inv_sqrt_mul_eq _ _ _
    have h2 : ⟪c', σ⟫ = h * ∑ i, Δ₀ i * σ i := inner_toLp_inv_sqrt_mul_eq _ _ _
    rw [hX]
    simp only [hline, h1, h2]
  simp only [hH]
  rw [hXe]
  exact hasDerivAt_integral_tilted_sum_comp_inner_line hκ hu hu0 hD v w a c' hF hFb t

/-- **The covariance bound behind Proposition 3.1.16.** For a centered `f ∈ L²(G)` and the
derivative `X` of `-H` in the disorder direction `(Δ, Δ₀)`,
`|⟨f X⟩| ≤ √(32 ⟨f²⟩ / κ) (4 D + h + D ‖g‖ ‖⟨σ⟩‖ / N) √(∑ Δ² + ∑ Δ₀²)`. -/
theorem abs_integral_mul_disorderDerivative_le {κ h : ℝ} (hκ : 0 < κ) (hh : 0 ≤ h) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (hu' : Differentiable ℝ (deriv u))
    {D : ℝ} (hD1 : ∀ x, |deriv u x| ≤ D) (hD2 : ∀ x, |deriv (deriv u) x| ≤ D) (hN : 1 ≤ N)
    (hM : M ≤ 10 * N) (g Δ : Fin M → Fin N → ℝ) (g₀ Δ₀ : Fin N → ℝ)
    (G : Measure (ℝ^N))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
    {f : ℝ^N → ℝ} (hf : MemLp f 2 G) (hf0 : ∫ σ, f σ ∂G = 0)
    (X : ℝ^N → ℝ)
    (hX : ∀ σ, X σ = (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) *
        ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i) :
    |∫ σ, f σ * X σ ∂G| ≤ Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) *
      (4 * D + h + D * ‖Matrix.of g‖ * ‖∫ σ, σ ∂G‖ / N) *
        Real.sqrt ((∑ k, ∑ i, Δ k i ^ 2) + ∑ i, Δ₀ i ^ 2) := by
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]; exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  have hid : MemLp (fun σ : ℝ^N => σ) 2 G := by
    rw [hG]; exact memLp_id_shcherbinaTirozziGibbs hκ hum hu0 g g₀
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set b : ℝ^N := ∫ σ, σ ∂G with hb
  set Φ : ℝ := Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) with hΦ
  have hΦ0 : 0 ≤ Φ := Real.sqrt_nonneg _
  set A : ℝ := ∑ k, ∑ i, Δ k i ^ 2 with hA
  set A₀ : ℝ := ∑ i, Δ₀ i ^ 2 with hA₀
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA00 : 0 ≤ A₀ := Finset.sum_nonneg fun i _ => sq_nonneg _
  set δ : ℝ := Real.sqrt (A + A₀) with hδ
  have hfield : ∀ k : Fin M, Measurable fun σ : ℝ^N =>
      deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) := fun k =>
    hu'.continuous.measurable.comp ((Finset.measurable_sum _ fun i _ =>
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).const_mul _).const_mul _)
  set φ : Fin M → ℝ^N → ℝ := fun k σ =>
    f σ * deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) with hφ
  have hφb : ∀ k σ, ‖φ k σ‖ ≤ D * ‖f σ‖ := fun k σ => by
    rw [hφ, norm_mul, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hD1 _) (norm_nonneg _)
  have hφL : ∀ k, MemLp (φ k) 2 G := fun k =>
    hf.of_le_mul (hf.aestronglyMeasurable.mul (hfield k).aestronglyMeasurable) (ae_of_all _ (hφb k))
  set v : Fin M → ℝ^N :=
    fun k => WithLp.toLp 2 (fun i => (Real.sqrt N)⁻¹ * Δ k i) with hv
  set d₀ : ℝ^N := WithLp.toLp 2 Δ₀ with hd₀
  -- Lemma 3.1.13 applied to `f u'(S_k)` and to `f`
  set w : Fin M → ℝ^N := fun k => ∫ σ, φ k σ • (σ - b) ∂G with hw
  have hwn : ∀ k, ‖w k‖ ≤ D * Φ := fun k => by
    refine (norm_integral_smul_sub_mean_shcherbinaTirozziGibbs_le hκ hu hu0 g g₀ G hG
      (hφL k)).trans ?_
    have h1 : ∫ σ, φ k σ ^ 2 ∂G ≤ D ^ 2 * ∫ σ, f σ ^ 2 ∂G := by
      rw [← integral_const_mul]
      refine integral_mono (hφL k).integrable_sq (hf.integrable_sq.const_mul _) fun σ => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hφb k σ) 2
      simpa only [mul_pow, Real.norm_eq_abs, sq_abs] using this
    refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1 (by positivity))).trans_eq ?_
    rw [hΦ, show 32 / κ * (D ^ 2 * ∫ σ, f σ ^ 2 ∂G) =
      D ^ 2 * (32 / κ * ∫ σ, f σ ^ 2 ∂G) by ring, Real.sqrt_mul (sq_nonneg D),
      Real.sqrt_sq hD0]
  set z : ℝ^N := ∫ σ, f σ • (σ - b) ∂G with hz
  have hzn : ‖z‖ ≤ Φ :=
    norm_integral_smul_sub_mean_shcherbinaTirozziGibbs_le hκ hu hu0 g g₀ G hG hf
  -- Lemma 3.1.15
  set U : ℝ^N → ℝ^M := fun σ =>
    WithLp.toLp 2 fun k => deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) with hU
  set V : ℝ^M := ∫ σ, f σ • (U σ - ∫ τ, U τ ∂G) ∂G with hV
  have hVn : ‖V‖ ≤ D * ((Real.sqrt N)⁻¹ * ‖Matrix.of g‖) * Φ :=
    norm_integral_smul_deriv_field_sub_mean_le hκ hu hu0 hu' hD2 g g₀ G hG hf U fun _ => rfl
  have hUm : Measurable U := (WithLp.measurable_toLp 2 (Fin M → ℝ)).comp
    (Measurable.of_eval fun k => hfield k)
  have hUL : MemLp U 2 G := by
    refine MemLp.of_bound hUm.aestronglyMeasurable (Real.sqrt (M * D ^ 2))
      (ae_of_all _ fun σ => ?_)
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ((Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (show ‖U σ k‖ ≤ D from hD1 _) 2).trans_eq ?_)
    simp
  have hVk : ∀ k, V k = ∫ σ, φ k σ ∂G := fun k => by
    have h := (integral_smul_apply_eq_apply_integral_smul_sub_add hf hUL
      (EuclideanSpace.proj (𝕜 := ℝ) k) (∫ τ, U τ ∂G)).2
    rw [hf0, zero_smul, add_zero] at h
    exact h.symm
  -- expand `⟨f X⟩`
  have hterm : ∀ k, Integrable (fun σ => φ k σ * ⟪v k, σ⟫) G ∧
      ∫ σ, φ k σ * ⟪v k, σ⟫ ∂G = ⟪v k, w k⟫ + V k * ⟪v k, b⟫ := fun k => by
    rw [hVk]
    exact integral_smul_apply_eq_apply_integral_smul_sub_add (hφL k) hid (innerSL ℝ (v k)) b
  have hlast : Integrable (fun σ => f σ * ⟪d₀, σ⟫) G ∧ ∫ σ, f σ * ⟪d₀, σ⟫ ∂G = ⟪d₀, z⟫ := by
    have h := integral_smul_apply_eq_apply_integral_smul_sub_add hf hid (innerSL ℝ d₀) b
    rw [hf0, zero_smul, add_zero] at h
    exact h
  have hfX : ∫ σ, f σ * X σ ∂G =
      (∑ k, (⟪v k, w k⟫ + V k * ⟪v k, b⟫)) + h * ⟪d₀, z⟫ := by
    have e : (fun σ => f σ * X σ) = fun σ =>
        (∑ k, φ k σ * ⟪v k, σ⟫) + h * (f σ * ⟪d₀, σ⟫) := by
      funext σ
      have h1 : ∀ k, (Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i = ⟪v k, σ⟫ :=
        fun k => (inner_toLp_inv_sqrt_mul_eq _ _ _).symm
      have h2 : ∑ i, Δ₀ i * σ i = ⟪d₀, σ⟫ := by
        have := inner_toLp_inv_sqrt_mul_eq 1 Δ₀ σ
        simpa only [one_mul] using this.symm
      simp only [hX, h1, h2, hφ]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
      · ring
    have hsum : Integrable (fun σ => ∑ k, φ k σ * ⟪v k, σ⟫) G :=
      integrable_finsetSum _ fun k _ => (hterm k).1
    rw [e, integral_add hsum (hlast.1.const_mul h), integral_finsetSum _ fun k _ => (hterm k).1,
      integral_const_mul, hlast.2]
    exact congrArg₂ _ (Finset.sum_congr rfl fun k _ => (hterm k).2) rfl
  -- norms of the direction
  have hvn : ∑ k, ‖v k‖ ^ 2 = (N : ℝ)⁻¹ * A := by
    rw [hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      change ((Real.sqrt N)⁻¹ * Δ k i) ^ 2 = _
      rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hsA : Real.sqrt A ≤ δ := Real.sqrt_le_sqrt (le_add_of_nonneg_right hA00)
  have hsumv : ∑ k, ‖v k‖ ≤ 4 * δ := by
    have h1 : (∑ k, ‖v k‖) ^ 2 ≤ 16 * A := by
      have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      rw [Finset.card_univ, Fintype.card_fin, hvn] at h2
      have hMN : (M : ℝ) * (N : ℝ)⁻¹ ≤ 16 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hN0]
        have h10 : (M : ℝ) ≤ 10 * N := by exact_mod_cast hM
        linarith
      refine h2.trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hMN hA0
    have h3 : ∑ k, ‖v k‖ ≤ 4 * Real.sqrt A := by
      refine (Real.le_sqrt_of_sq_le h1).trans_eq ?_
      rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    exact h3.trans (mul_le_mul_of_nonneg_left hsA (by norm_num))
  have hsumV : ∑ k, ‖v k‖ * |V k| ≤ D * ‖Matrix.of g‖ * Φ / N * δ := by
    have h1 : ∑ k, ‖v k‖ * |V k| ≤ Real.sqrt (∑ k, ‖v k‖ ^ 2) * ‖V‖ := by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs]
      exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => ‖v k‖) fun k => |V k|
    have h2 : Real.sqrt (∑ k, ‖v k‖ ^ 2) ≤ (Real.sqrt N)⁻¹ * δ := by
      rw [hvn, Real.sqrt_mul (inv_nonneg.2 hN0.le), Real.sqrt_inv]
      exact mul_le_mul_of_nonneg_left hsA (inv_nonneg.2 (Real.sqrt_nonneg _))
    refine h1.trans ((mul_le_mul h2 hVn (norm_nonneg _)
      (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).trans_eq ?_)
    have hsq : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hN0.le]
    rw [div_eq_mul_inv, ← hsq]
    ring
  have hd₀n : ‖d₀‖ ≤ δ := by
    have e : ‖d₀‖ = Real.sqrt A₀ := by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rfl
    rw [e]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left hA0)
  have h1 : |∑ k, (⟪v k, w k⟫ + V k * ⟪v k, b⟫)| ≤
      D * Φ * ∑ k, ‖v k‖ + ‖b‖ * ∑ k, ‖v k‖ * |V k| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_real_inner_le_norm _ _).trans ?_
      rw [mul_comm (D * Φ)]
      exact mul_le_mul_of_nonneg_left (hwn k) (norm_nonneg _)
    · rw [abs_mul]
      refine (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)).trans_eq ?_
      ring
  have h2 : |h * ⟪d₀, z⟫| ≤ h * (δ * Φ) := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul hd₀n hzn (norm_nonneg _) (Real.sqrt_nonneg _))) hh
  rw [hfX]
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have h3 := mul_le_mul_of_nonneg_left hsumv (mul_nonneg hD0 hΦ0)
  have h4 := mul_le_mul_of_nonneg_left hsumV (norm_nonneg b)
  refine (add_le_add (add_le_add h3 h4) le_rfl).trans_eq ?_
  ring

/-- The square of the covariance bound for an observable whose centered version has second
moment of order `B / N²`. -/
private theorem sq_integral_mul_disorderDerivative_le {κ₀ κ h h₀ D c K₉ B : ℝ} (hκ₀ : 0 < κ₀)
    (hκ : κ₀ ≤ κ) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u)
    (hu0 : ∀ x, u x ≤ 0) (hu' : Differentiable ℝ (deriv u)) (hD1 : ∀ x, |deriv u x| ≤ D)
    (hD2 : ∀ x, |deriv (deriv u) x| ≤ D) (hN : 1 ≤ N) (hM : M ≤ 10 * N)
    (g Δ : Fin M → Fin N → ℝ) (g₀ Δ₀ : Fin N → ℝ) (G : Measure (ℝ^N))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)
    {f : ℝ^N → ℝ} (hf : MemLp f 2 G) (hf0 : ∫ σ, f σ ∂G = 0)
    (hc : 0 ≤ c) (hK₉ : 0 ≤ K₉) (hB : 0 ≤ B) (hf2 : ∫ σ, f σ ^ 2 ∂G ≤ c * B / (N : ℝ) ^ 2)
    (hb : ‖∫ σ, σ ∂G‖ ^ 2 ≤ K₉ * B) (X : ℝ^N → ℝ)
    (hX : ∀ σ, X σ = (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) *
        ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i) :
    (∫ σ, f σ * X σ ∂G) ^ 2 ≤
      64 * c / κ₀ * ((4 * D + h₀) ^ 2 + D ^ 2 * K₉) *
        (B / (N : ℝ) ^ 2 + B ^ 2 * ‖Matrix.of g‖ ^ 2 / (N : ℝ) ^ 4) *
          ((∑ k, ∑ i, Δ k i ^ 2) + ∑ i, Δ₀ i ^ 2) := by
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key := abs_integral_mul_disorderDerivative_le hκ0 hh hu hu0 hu' hD1 hD2 hN hM g Δ g₀ Δ₀
    G hG hf hf0 X hX
  set δ2 : ℝ := (∑ k, ∑ i, Δ k i ^ 2) + ∑ i, Δ₀ i ^ 2 with hδ2
  have hδ20 : 0 ≤ δ2 := add_nonneg
    (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
  set n : ℝ := ‖Matrix.of g‖ with hn
  set β : ℝ := ‖∫ σ, σ ∂G‖ with hβ
  have hf20 : 0 ≤ ∫ σ, f σ ^ 2 ∂G := integral_nonneg fun _ => sq_nonneg _
  have h1 := pow_le_pow_left₀ (abs_nonneg _) key 2
  rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (by positivity) hf20),
    Real.sq_sqrt hδ20] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hδ20)
  have h2 : 32 / κ * ∫ σ, f σ ^ 2 ∂G ≤ 32 / κ₀ * (c * B / (N : ℝ) ^ 2) :=
    mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ) hf2 hf20 (by positivity)
  have h3 : (4 * D + h + D * n * β / N) ^ 2 ≤
      2 * (4 * D + h₀) ^ 2 + 2 * (D ^ 2 * n ^ 2 * (K₉ * B) / (N : ℝ) ^ 2) := by
    refine (add_sq_le).trans ?_
    rw [mul_add]
    refine add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (by linarith) 2) zero_le_two) (mul_le_mul_of_nonneg_left ?_ zero_le_two)
    rw [div_pow, mul_pow, mul_pow]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
  refine (mul_le_mul h2 h3 (sq_nonneg _) (by positivity)).trans ?_
  have hexp : 32 / κ₀ * (c * B / (N : ℝ) ^ 2) *
        (2 * (4 * D + h₀) ^ 2 + 2 * (D ^ 2 * n ^ 2 * (K₉ * B) / (N : ℝ) ^ 2)) =
      64 * c / κ₀ * ((4 * D + h₀) ^ 2 * (B / (N : ℝ) ^ 2) +
        D ^ 2 * K₉ * (B ^ 2 * n ^ 2 / (N : ℝ) ^ 4)) := by ring
  rw [hexp, mul_assoc (64 * c / κ₀)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hP : 0 ≤ B / (N : ℝ) ^ 2 := by positivity
  have hQ : 0 ≤ B ^ 2 * n ^ 2 / (N : ℝ) ^ 4 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (4 * D + h₀)) hQ,
    mul_nonneg (mul_nonneg (sq_nonneg D) hK₉) hP]

/-- The derivative of `-H` in a direction of the disorder is square integrable under any
probability measure with a square integrable configuration. -/
private theorem memLp_disorderDerivative {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (g Δ : Fin M → Fin N → ℝ)
    (Δ₀ : Fin N → ℝ) (h : ℝ) (G : Measure (ℝ^N))
    (hid : MemLp (fun σ : ℝ^N => σ) 2 G)
    (X : ℝ^N → ℝ)
    (hX : ∀ σ, X σ = (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) *
        ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i) :
    MemLp X 2 G := by
  have hlin : ∀ a : Fin N → ℝ, ∀ c : ℝ,
      MemLp (fun σ : ℝ^N => c * ∑ i, a i * σ i) 2 G := fun a c => by
    have h1 := hid.const_inner (𝕜 := ℝ)
      (WithLp.toLp 2 (fun i => c * a i) : ℝ^N)
    simpa only [inner_toLp_inv_sqrt_mul_eq] using h1
  have hfield : ∀ k : Fin M, Measurable fun σ : ℝ^N =>
      deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) := fun k =>
    (measurable_deriv u).comp ((Finset.measurable_sum _ fun i _ =>
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).const_mul _).const_mul _)
  have hsum : MemLp (fun σ : ℝ^N =>
      ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) *
        ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) 2 G := by
    refine memLp_finsetSum _ fun k _ => (hlin (Δ k) (Real.sqrt N)⁻¹).of_le_mul (c := D)
      ((hfield k).aestronglyMeasurable.mul
        (hlin (Δ k) (Real.sqrt N)⁻¹).aestronglyMeasurable)
      (ae_of_all _ fun σ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)
  have e : X = fun σ => (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) *
      ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i := funext hX
  rw [e]
  exact hsum.add (hlin Δ₀ h)

/-- **Proposition 3.1.16 for `R_{1,1}`:** along every line of the disorder, the derivative `d` of
`⟨R_{1,1}⟩` satisfies `d² ≤ K (B^* / N² + B^{*2} ‖g‖² / N⁴) ‖(Δ, Δ₀)‖²`. -/
theorem exists_hasDerivAt_integral_shcherbinaTirozzi_selfOverlap_line (κ₀ h₀ D : ℝ)
    (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M : ℕ) (κ h : ℝ) (u : ℝ → ℝ) (g Δ : Fin M → Fin N → ℝ)
      (g₀ Δ₀ : Fin N → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ → M ≤ 10 * N → 1 ≤ N →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D) →
      ∃ d : ℝ, HasDerivAt (fun t => ∫ σ, (N : ℝ)⁻¹ * ‖σ‖ ^ 2
            ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
              (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ)) d 0 ∧
        d ^ 2 ≤ K * ((N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2) / (N : ℝ) ^ 2 +
            (N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2) ^ 2 * ‖Matrix.of g‖ ^ 2 /
              (N : ℝ) ^ 4) * ((∑ k, ∑ i, Δ k i ^ 2) + ∑ i, Δ₀ i ^ 2) := by
  obtain ⟨K₁₁, hK₁₁, h335⟩ :=
    exists_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le κ₀ h₀ D hκ₀
  obtain ⟨K₉, hK₉, h319⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ₀ h₀ D hκ₀
  refine ⟨64 * K₁₁ / κ₀ * ((4 * D + h₀) ^ 2 + D ^ 2 * K₉), by positivity,
    fun N M κ h u g Δ g₀ Δ₀ hκ hh0 hh hM hN hu hu0 hD hud hu' hD1 hD2 => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set G := volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ with hG
  have : IsProbabilityMeasure G :=
    isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 g g₀
  have hid : MemLp (fun σ : ℝ^N => σ) 2 G :=
    memLp_id_shcherbinaTirozziGibbs hκ0 hum hu0 g g₀
  set B : ℝ := N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  set F : ℝ^N → ℝ := fun σ => (N : ℝ)⁻¹ * ‖σ‖ ^ 2 with hF
  have hFm : Measurable F := by fun_prop
  have hFb : ∀ σ, |F σ| ≤ 1 * (1 + ‖σ‖ ^ 2) := fun σ => by
    rw [hF, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hN0.le) (sq_nonneg _)), one_mul]
    exact (mul_le_of_le_one_left (sq_nonneg _) (inv_le_one_of_one_le₀ hN1)).trans
      (le_add_of_nonneg_left zero_le_one)
  set X : ℝ^N → ℝ := fun σ =>
    (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) *
      ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i with hX
  have hder := hasDerivAt_integral_shcherbinaTirozziGibbs_line (h := h) hκ0 hud hu0 hD1 g Δ g₀ Δ₀
    hFm hFb 0 X fun σ => by simp [hX]
  simp only [zero_mul, add_zero, ← hG] at hder
  refine ⟨_, hder, ?_⟩
  have hFL : MemLp F 2 G := by
    refine (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 ?_
    have h4 := (h319 N M 2 κ h u g g₀ hκ hh0 hh hM (by omega) hum hu0 hD).1
    rw [← hG] at h4
    have e : (fun σ => F σ ^ 2) = fun σ => ((N : ℝ)⁻¹) ^ 2 * ‖σ‖ ^ (2 * 2) := by
      funext σ; rw [hF]; ring
    rw [e]
    exact h4.const_mul _
  have hXL := memLp_disorderDerivative hD1 g Δ Δ₀ h G hid X fun σ => rfl
  set f : ℝ^N → ℝ := fun σ => F σ - ∫ τ, F τ ∂G with hf
  have hfL : MemLp f 2 G := hFL.sub (memLp_const _)
  have hf0 : ∫ σ, f σ ∂G = 0 := by
    rw [hf, integral_sub (hFL.integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  have hcov : (∫ σ, F σ * X σ ∂G) - (∫ σ, F σ ∂G) * ∫ σ, X σ ∂G = ∫ σ, f σ * X σ ∂G := by
    have e : (fun σ => f σ * X σ) = fun σ => F σ * X σ - (∫ τ, F τ ∂G) * X σ := by
      funext σ; rw [hf]; ring
    have h1 : Integrable (fun σ => F σ * X σ) G := hFL.integrable_mul hXL
    rw [e, integral_sub h1 ((hXL.integrable one_le_two).const_mul _),
      integral_const_mul (∫ τ, F τ ∂G) X]
  have hf2 : ∫ σ, f σ ^ 2 ∂G ≤ K₁₁ * B / (N : ℝ) ^ 2 := by
    have h1 := (h335 N M 1 κ h u g g₀ hκ hh0 hh hM hN hN hu hu0 hD G hG).2
    simpa only [mul_one, pow_one, Nat.cast_one] using h1
  have hbary : ‖∫ σ, σ ∂G‖ ^ 2 ≤ K₉ * B := by
    refine (sq_norm_integral_le_integral_sq_norm hid).trans ?_
    have h1 := (h319 N M 1 κ h u g g₀ hκ hh0 hh hM (by omega) hum hu0 hD).2
    rw [← hG] at h1
    simpa only [mul_one, pow_one] using h1
  rw [hcov]
  exact sq_integral_mul_disorderDerivative_le hκ₀ hκ hh0 hh hu hu0 hu' hD1 hD2 hN hM g Δ g₀ Δ₀
    G hG hfL hf0 hK₁₁ hK₉ hB0 hf2 hbary X fun σ => rfl

/-- **Proposition 3.1.16 for `R_{1,2}`:** along every line of the disorder, the derivative `d` of
`⟨R_{1,2}⟩` satisfies `d² ≤ K (B^* / N² + B^{*2} ‖g‖² / N⁴) ‖(Δ, Δ₀)‖²`. -/
theorem exists_hasDerivAt_integral_shcherbinaTirozzi_overlap_line (κ₀ h₀ D : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M : ℕ) (κ h : ℝ) (u : ℝ → ℝ) (g Δ : Fin M → Fin N → ℝ)
      (g₀ Δ₀ : Fin N → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ → M ≤ 10 * N → 1 ≤ N →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D) →
      ∀ G : ℝ → Measure (ℝ^N),
      (∀ t, G t = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u
        (fun k i => g k i + t * Δ k i) (fun i => g₀ i + t * Δ₀ i) σ) →
      ∃ d : ℝ, HasDerivAt (fun t => ∫ p, (N : ℝ)⁻¹ * ⟪p.1, p.2⟫ ∂((G t).prod (G t))) d 0 ∧
        d ^ 2 ≤ K * ((N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2) / (N : ℝ) ^ 2 +
            (N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2) ^ 2 * ‖Matrix.of g‖ ^ 2 /
              (N : ℝ) ^ 4) * ((∑ k, ∑ i, Δ k i ^ 2) + ∑ i, Δ₀ i ^ 2) := by
  obtain ⟨K₉, hK₉, h319⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ₀ h₀ D hκ₀
  refine ⟨64 * (128 * K₉ / κ₀) / κ₀ * ((4 * D + h₀) ^ 2 + D ^ 2 * K₉), by positivity,
    fun N M κ h u g Δ g₀ Δ₀ hκ hh0 hh hM hN hu hu0 hD hud hu' hD1 hD2 G hGt => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hG : G 0 = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ := by
    rw [hGt 0]
    simp
  have hprob : ∀ t, IsProbabilityMeasure (G t) := fun t => by
    rw [hGt t]; exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 _ _
  have hidt : ∀ t, MemLp (fun σ : ℝ^N => σ) 2 (G t) := fun t => by
    rw [hGt t]; exact memLp_id_shcherbinaTirozziGibbs hκ0 hum hu0 _ _
  have := hprob 0
  have hid := hidt 0
  set B : ℝ := N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  set b : ℝ^N := ∫ σ, σ ∂(G 0) with hb
  set X : ℝ^N → ℝ := fun σ =>
    (∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) *
      ((Real.sqrt N)⁻¹ * ∑ i, Δ k i * σ i)) + h * ∑ i, Δ₀ i * σ i with hX
  have hXL := memLp_disorderDerivative hD1 g Δ Δ₀ h (G 0) hid X fun σ => rfl
  -- the barycenter and its coordinates
  have hcoordL : ∀ i : Fin N, MemLp (fun σ : ℝ^N => σ i) 2 (G 0) :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hid
  have hbi : ∀ t i, (∫ σ, σ ∂(G t)) i = ∫ σ, σ i ∂(G t) := fun t i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      ((hidt t).integrable one_le_two)).symm
  have hcoord : ∀ i : Fin N, HasDerivAt (fun t => ∫ σ, σ i ∂(G t))
      ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0)) 0 := fun i => by
    have hm : Measurable fun σ : ℝ^N => σ i :=
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable
    have hbound : ∀ σ : ℝ^N, |σ i| ≤ 1 * (1 + ‖σ‖ ^ 2) := fun σ => by
      have h1 : |σ i| ≤ ‖σ‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le σ i
      rw [one_mul]
      nlinarith [sq_nonneg (‖σ‖ - 1), norm_nonneg σ]
    have h := hasDerivAt_integral_shcherbinaTirozziGibbs_line (h := h) hκ0 hud hu0 hD1 g Δ g₀ Δ₀
      hm hbound 0 X fun σ => by simp [hX]
    simp only [← hGt] at h
    rw [hb, hbi]
    exact h
  have hsq : HasDerivAt (fun t => (N : ℝ)⁻¹ * ∑ i, (∫ σ, σ i ∂(G t)) ^ 2)
      ((N : ℝ)⁻¹ * ∑ i, 2 * b i * ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0))) 0 := by
    refine (HasDerivAt.fun_sum fun i _ => ?_).const_mul _
    refine ((hcoord i).pow 2).congr_deriv ?_
    rw [hb, hbi]
    ring
  have hfun : (fun t => ∫ p, (N : ℝ)⁻¹ * ⟪p.1, p.2⟫ ∂((G t).prod (G t))) =
      fun t => (N : ℝ)⁻¹ * ∑ i, (∫ σ, σ i ∂(G t)) ^ 2 := by
    funext t
    have := hprob t
    have h1 := (hidt t).integrable one_le_two
    rw [integral_const_mul]
    have h2 : ∫ p, ⟪p.1, p.2⟫ ∂((G t).prod (G t)) = ‖∫ σ, σ ∂(G t)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      exact integral_prod_bilin (innerSL ℝ) h1 h1
    rw [h2, EuclideanSpace.real_norm_sq_eq]
    simp_rw [hbi]
  rw [hfun]
  refine ⟨_, hsq, ?_⟩
  set f : ℝ^N → ℝ := fun σ => 2 * (N : ℝ)⁻¹ * (⟪b, σ⟫ - ⟪b, b⟫) with hf
  have hbL : MemLp (fun σ => ⟪b, σ⟫) 2 (G 0) := hid.const_inner b
  have hfL : MemLp f 2 (G 0) := (hbL.sub (memLp_const _)).const_mul _
  have hinner : ∫ σ, ⟪b, σ⟫ ∂(G 0) = ⟪b, b⟫ := integral_inner (hid.integrable one_le_two) b
  have hf0 : ∫ σ, f σ ∂(G 0) = 0 := by
    rw [hf, integral_const_mul, integral_sub (hbL.integrable one_le_two) (integrable_const _),
      hinner, integral_const, probReal_univ, one_smul, sub_self, mul_zero]
  have hcov : (N : ℝ)⁻¹ * ∑ i, 2 * b i * ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0)) =
      ∫ σ, f σ * X σ ∂(G 0) := by
    have h1 : ∀ i : Fin N, Integrable (fun σ => σ i * X σ) (G 0) := fun i =>
      (hcoordL i).integrable_mul hXL
    have h2 : Integrable (fun σ => ⟪b, σ⟫ * X σ) (G 0) := hbL.integrable_mul hXL
    have h3 : ∑ i, b i * ∫ σ, σ i * X σ ∂(G 0) = ∫ σ, ⟪b, σ⟫ * X σ ∂(G 0) := by
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun i _ => (h1 i).const_mul _]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      simp only [PiLp.inner_apply, Finset.sum_mul, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h4 : ∑ i, b i * b i = ⟪b, b⟫ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    have e : (fun σ => f σ * X σ) = fun σ =>
        2 * (N : ℝ)⁻¹ * (⟪b, σ⟫ * X σ) - 2 * (N : ℝ)⁻¹ * ⟪b, b⟫ * X σ := by
      funext σ; rw [hf]; ring
    rw [e, integral_sub (h2.const_mul _) ((hXL.integrable one_le_two).const_mul _),
      integral_const_mul, integral_const_mul, ← h3, ← h4]
    have h5 : ∑ i, 2 * b i * ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0)) =
        2 * (∑ i, b i * ∫ σ, σ i * X σ ∂(G 0)) -
          2 * (∑ i, b i * b i) * ∫ σ, X σ ∂(G 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h5]
    ring
  have hbary : ‖b‖ ^ 2 ≤ K₉ * B := by
    refine (sq_norm_integral_le_integral_sq_norm hid).trans ?_
    have h1 := (h319 N M 1 κ h u g g₀ hκ hh0 hh hM (by omega) hum hu0 hD).2
    rw [← hG] at h1
    simpa only [mul_one, pow_one] using h1
  have hf2 : ∫ σ, f σ ^ 2 ∂(G 0) ≤ 128 * K₉ / κ₀ * B / (N : ℝ) ^ 2 := by
    have hlip : ∀ x y : ℝ^N, |⟪b, x⟫ - ⟪b, y⟫| ≤ ‖b‖ * ‖x - y‖ :=
      fun x y => by
        rw [← inner_sub_right]
        exact abs_real_inner_le_norm _ _
    have h1 := (integral_sub_integral_pow_shcherbinaTirozziGibbs_le (h := h) hκ0 hu hu0 g g₀
      (f := fun σ => ⟪b, σ⟫) (by fun_prop) (norm_nonneg b) hlip 1).2
    rw [← hG, hinner] at h1
    simp only [mul_one, pow_one, Nat.cast_one] at h1
    have e : (fun σ => f σ ^ 2) = fun σ => 4 * ((N : ℝ)⁻¹) ^ 2 * (⟪b, σ⟫ - ⟪b, b⟫) ^ 2 := by
      funext σ; rw [hf]; ring
    rw [e, integral_const_mul]
    refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
    have h2 : 4 * (8 * ‖b‖ ^ 2 / κ) ≤ 32 * (K₉ * B) / κ₀ := by
      rw [show 4 * (8 * ‖b‖ ^ 2 / κ) = 32 * ‖b‖ ^ 2 / κ by ring]
      exact div_le_div₀ (mul_nonneg (by norm_num) (mul_nonneg hK₉ hB0))
        (mul_le_mul_of_nonneg_left hbary (by norm_num)) hκ₀ hκ
    refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq ?_
    ring
  rw [hcov]
  exact sq_integral_mul_disorderDerivative_le hκ₀ hκ hh0 hh hu hu0 hu' hD1 hD2 hN hM g Δ g₀ Δ₀
    (G 0) hG hfL hf0 (by positivity) hK₉ hB0 hf2 hbary X fun σ => rfl

end SpinGlasses
