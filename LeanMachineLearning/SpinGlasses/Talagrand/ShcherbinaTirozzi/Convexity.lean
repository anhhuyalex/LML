/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Integral
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.QuadraticTilt
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianExp

/-!
# The Shcherbina--Tirozzi model: convexity and normalization (Talagrand Section 3.1)

The configuration space is `ℝ^N` and, for a potential `u`, disorder `g : Fin M → Fin N → ℝ`
(constraint vectors) and `g₀ : Fin N → ℝ` (external field), the Hamiltonian is Eq. (3.1),
`-H σ = ∑_k u ((√N)⁻¹ ∑_i g k i σ_i) + h ∑_i g₀ i σ_i - κ ‖σ‖²`.
The Gibbs measure (3.5) is `volume.tilted (fun σ => -H σ)`.

## Main declarations

* `SpinGlasses.shcherbinaTirozziHamiltonian`: Eq. (3.1).
* `SpinGlasses.shcherbinaTirozziHamiltonian_midpoint_gap`: Eq. (3.4), from the concavity of `u`.
* `SpinGlasses.integrable_exp_neg_shcherbinaTirozziHamiltonian`: the partition function is finite.
* `SpinGlasses.integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le`: Lemma 3.1.5 for the model.
* `SpinGlasses.inv_integral_exp_neg_shcherbinaTirozziHamiltonian_le`: Lemma 3.1.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {N M : ℕ}

/-- The Hamiltonian (3.1) of the Shcherbina--Tirozzi model on `ℝ^N`. -/
noncomputable def shcherbinaTirozziHamiltonian (κ h : ℝ) (u : ℝ → ℝ) (g : Fin M → Fin N → ℝ)
    (g₀ : Fin N → ℝ) (σ : ℝ^N) : ℝ :=
  κ * ‖σ‖ ^ 2 - ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) - h * ∑ i, g₀ i * σ i

/-- The constraint field `S_k` as the inner product with the normalized disorder vector. -/
theorem inner_toLp_inv_sqrt_mul_eq (c : ℝ) (a : Fin N → ℝ) (σ : ℝ^N) :
    ⟪WithLp.toLp 2 (fun i => c * a i), σ⟫ = c * ∑ i, a i * σ i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Finset.mul_sum, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    change σ i * (c * a i) = c * (a i * σ i)
    ring

/-- The opposite of the Hamiltonian is a perturbation `∑_k u (S_k)` of the quadratic confinement
`-κ ‖σ‖²` plus a linear term. -/
theorem neg_shcherbinaTirozziHamiltonian_eq (κ h : ℝ) (u : ℝ → ℝ) (g : Fin M → Fin N → ℝ)
    (g₀ : Fin N → ℝ) (σ : ℝ^N) :
    -shcherbinaTirozziHamiltonian κ h u g g₀ σ =
      (∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i)) - κ * ‖σ‖ ^ 2 +
        ⟪WithLp.toLp 2 (fun i => h * g₀ i), σ⟫ := by
  rw [inner_toLp_inv_sqrt_mul_eq, shcherbinaTirozziHamiltonian]
  ring

/-- The Hamiltonian is jointly measurable in the disorder and the configuration. -/
theorem measurable_shcherbinaTirozziHamiltonian (κ h : ℝ) {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) × ℝ^N =>
      shcherbinaTirozziHamiltonian κ h u p.1.1 p.1.2 p.2 := by
  have hσ : ∀ i : Fin N, Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => p.2 i := fun i =>
    ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).comp measurable_snd
  have hg : ∀ (k : Fin M) (i : Fin N), Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => p.1.1 k i := fun k i =>
    (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
      (measurable_fst.comp measurable_fst))
  have hg₀ : ∀ i : Fin N, Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => p.1.2 i := fun i =>
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hfield : ∀ k : Fin M, Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => u ((Real.sqrt N)⁻¹ * ∑ i, p.1.1 k i * p.2 i) := fun k =>
    hu.comp ((Finset.measurable_sum _ fun i _ => (hg k i).mul (hσ i)).const_mul _)
  have hsum := Finset.measurable_sum Finset.univ fun k _ => hfield k
  have hlin := (Finset.measurable_sum Finset.univ fun i _ => (hg₀ i).mul (hσ i)).const_mul h
  have hq : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) × ℝ^N =>
      κ * ‖p.2‖ ^ 2 := (measurable_snd.norm.pow_const 2).const_mul κ
  simp only [shcherbinaTirozziHamiltonian]
  exact (hq.sub hsum).sub hlin

/-- The Hamiltonian is measurable in the configuration. -/
theorem measurable_shcherbinaTirozziHamiltonian_apply (κ h : ℝ) {u : ℝ → ℝ} (hu : Measurable u)
    (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ) :
    Measurable (shcherbinaTirozziHamiltonian κ h u g g₀) := by
  have hσ : ∀ i : Fin N, Measurable fun σ : ℝ^N => σ i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable
  have hfield : ∀ k : Fin M, Measurable fun σ : ℝ^N =>
      u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) := fun k =>
    hu.comp ((Finset.measurable_sum _ fun i _ => (hσ i).const_mul _).const_mul _)
  have hsum := Finset.measurable_sum Finset.univ fun k _ => hfield k
  have hlin := (Finset.measurable_sum Finset.univ fun i _ => (hσ i).const_mul (g₀ i)).const_mul h
  have hq : Measurable fun σ : ℝ^N => κ * ‖σ‖ ^ 2 :=
    (measurable_norm.pow_const 2).const_mul κ
  exact (hq.sub hsum).sub hlin

/-- **Eq. (3.4):** for concave `u`, the Hamiltonian is uniformly midpoint convex with constant
`κ`. -/
theorem shcherbinaTirozziHamiltonian_midpoint_gap (κ h : ℝ) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ)
    (x y : ℝ^N) :
    κ * ‖(1 / 2 : ℝ) • (x - y)‖ ^ 2 ≤
      (shcherbinaTirozziHamiltonian κ h u g g₀ x + shcherbinaTirozziHamiltonian κ h u g g₀ y) / 2 -
        shcherbinaTirozziHamiltonian κ h u g g₀ ((1 / 2 : ℝ) • (x + y)) := by
  have hfield : ∀ a : Fin N → ℝ, ∀ c : ℝ,
      c * ∑ i, a i * ((1 / 2 : ℝ) • (x + y)) i =
        (1 / 2) * (c * ∑ i, a i * x i) + (1 / 2) * (c * ∑ i, a i * y i) := fun a c => by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      change c * (a i * ((1 / 2) * (x i + y i))) = _
      ring
  have hconc : ∀ k : Fin M,
      (u ((Real.sqrt N)⁻¹ * ∑ i, g k i * x i) + u ((Real.sqrt N)⁻¹ * ∑ i, g k i * y i)) / 2 ≤
        u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((1 / 2 : ℝ) • (x + y)) i) := fun k => by
    rw [hfield]
    have := hu.2 (Set.mem_univ ((Real.sqrt N)⁻¹ * ∑ i, g k i * x i))
      (Set.mem_univ ((Real.sqrt N)⁻¹ * ∑ i, g k i * y i)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    linarith
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hconc k
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hsum
  have hlin := hfield g₀ 1
  simp only [one_mul] at hlin
  have hpar : ‖(1 / 2 : ℝ) • (x - y)‖ ^ 2 =
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 - ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 := by
    have := parallelogram_law_with_norm ℝ x y
    simp only [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_pow]
    nlinarith
  simp only [shcherbinaTirozziHamiltonian]
  rw [hlin, hpar]
  linarith

/-- For `u ≤ 0` and `κ > 0`, the Boltzmann weight is integrable: the partition function of (3.5)
is finite. -/
theorem integrable_exp_neg_shcherbinaTirozziHamiltonian {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ) :
    Integrable fun σ => Real.exp (-shcherbinaTirozziHamiltonian κ h u g g₀ σ) := by
  simp_rw [neg_shcherbinaTirozziHamiltonian_eq]
  refine integrable_exp_add_neg_mul_sq_norm_add_inner ?_
    (fun σ => Finset.sum_nonpos fun k _ => hu0 _) hκ _
  exact Finset.measurable_sum _ fun k _ => hu.comp
    ((Finset.measurable_sum _ fun i _ =>
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).const_mul _).const_mul _)

/-- The Gibbs measure (3.5) is a probability measure. -/
theorem isProbabilityMeasure_shcherbinaTirozziGibbs {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ) :
    IsProbabilityMeasure
      (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) :=
  isProbabilityMeasure_tilted (integrable_exp_neg_shcherbinaTirozziHamiltonian hκ hu hu0 g g₀)

/-- **Lemma 3.1.5 for the model:** under the Gibbs measure,
`⟨exp (κ ‖σ‖² / 2)⟩ ≤ Z⁻¹ (2 π / κ) ^ (N / 2) exp (h² ∑_i g_i² / (2 κ))`. -/
theorem integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ) :
    Integrable (fun σ : ℝ^N => Real.exp (κ / 2 * ‖σ‖ ^ 2))
        (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ∧
      ∫ σ, Real.exp (κ / 2 * ‖σ‖ ^ 2)
          ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ≤
        (∫ σ, Real.exp (-shcherbinaTirozziHamiltonian κ h u g g₀ σ))⁻¹ *
          ((2 * π / κ) ^ ((N : ℝ) / 2) * Real.exp (h ^ 2 * (∑ i, g₀ i ^ 2) / (2 * κ))) := by
  have hU : Measurable fun σ : ℝ^N =>
      ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * σ i) :=
    Finset.measurable_sum _ fun k _ => hu.comp
      ((Finset.measurable_sum _ fun i _ =>
        ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).const_mul _).const_mul _)
  have key := integral_exp_half_sq_norm_tilted_le hU
    (fun σ => Finset.sum_nonpos fun k _ => hu0 _) hκ
    (WithLp.toLp 2 (fun i => h * g₀ i) : ℝ^N)
  simp_rw [← neg_shcherbinaTirozziHamiltonian_eq, finrank_euclideanSpace_fin] at key
  have hnorm : ‖(WithLp.toLp 2 (fun i => h * g₀ i) : ℝ^N)‖ ^ 2 =
      h ^ 2 * ∑ i, g₀ i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      change (h * g₀ i) ^ 2 = _
      ring
  rwa [hnorm] at key

/-- **Lemma 3.1.6:** if `-D (1 + |x|) ≤ u x ≤ 0`, then
`1 / Z ≤ (κ / π) ^ (N / 2) exp (D (M + √(M / (κ N) ∑_{k,i} g_{k,i}²)))`. -/
theorem inv_integral_exp_neg_shcherbinaTirozziHamiltonian_le {κ h D : ℝ} (hκ : 0 < κ)
    {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (hD : ∀ x, -D * (1 + |x|) ≤ u x)
    (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ) :
    (∫ σ, Real.exp (-shcherbinaTirozziHamiltonian κ h u g g₀ σ))⁻¹ ≤
      (κ / π) ^ ((N : ℝ) / 2) *
        Real.exp (D * (M + Real.sqrt (M / (κ * N) * ∑ k, ∑ i, g k i ^ 2))) := by
  have hD0 : 0 ≤ D := by
    have h1 := (hD 0).trans (hu0 0)
    simp only [abs_zero, add_zero, mul_one] at h1
    linarith
  set E := ℝ^N
  set c : ℝ := (Real.sqrt (2 * κ))⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  have hcκ : c ≤ (Real.sqrt κ)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hκ) (Real.sqrt_le_sqrt (by linarith))
  set v : Fin M → E := fun k => WithLp.toLp 2 (fun i => (Real.sqrt N)⁻¹ * g k i) with hv
  set a : E := WithLp.toLp 2 (fun i => h * g₀ i) with ha
  have hS : ∀ (k : Fin M) (σ : E), (Real.sqrt N)⁻¹ * ∑ i, g k i * σ i = ⟪v k, σ⟫ :=
    fun k σ => (inner_toLp_inv_sqrt_mul_eq _ _ _).symm
  -- the exponent as a function of a standard Gaussian vector
  set Y : E → ℝ := fun z => (∑ k, u ⟪v k, c • z⟫) + ⟪a, c • z⟫ with hY
  have hZ : ∫ σ, Real.exp (-shcherbinaTirozziHamiltonian κ h u g g₀ σ) =
      (π / κ) ^ ((N : ℝ) / 2) * ∫ z, Real.exp (Y z) ∂stdGaussian E := by
    have e : ∀ σ : E, Real.exp (-shcherbinaTirozziHamiltonian κ h u g g₀ σ) =
        Real.exp ((∑ k, u ⟪v k, σ⟫) + ⟪a, σ⟫) * Real.exp (-κ * ‖σ‖ ^ 2) := fun σ => by
      rw [neg_shcherbinaTirozziHamiltonian_eq, ← Real.exp_add]
      simp only [hS]
      rw [← ha]
      congr 1
      ring
    simp_rw [e]
    rw [integral_mul_exp_neg_mul_sq_norm hκ
      (fun σ : E => Real.exp ((∑ k, u ⟪v k, σ⟫) + ⟪a, σ⟫)), finrank_euclideanSpace_fin]
  have hlin : ∀ b : E, Integrable (fun z => ⟪b, z⟫) (stdGaussian E) := fun b =>
    (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ b) 1 (by norm_num)).integrable le_rfl
  have hlin0 : ∫ z, ⟪a, c • z⟫ ∂stdGaussian E = 0 := by
    have h0 : ∫ z, ⟪a, z⟫ ∂stdGaussian E = 0 := integral_strongDual_stdGaussian (innerSL ℝ a)
    simp_rw [real_inner_smul_right]
    rw [integral_const_mul, h0, mul_zero]
  have hai : Integrable (fun z => ⟪a, c • z⟫) (stdGaussian E) := by
    simp_rw [real_inner_smul_right]
    exact (hlin a).const_mul c
  have hum : ∀ k, Measurable fun z : E => u ⟪v k, c • z⟫ := fun k =>
    hu.comp (by fun_prop : Measurable fun z : E => ⟪v k, c • z⟫)
  have hbound : ∀ (k : Fin M) (z : E), -D * (1 + c * |⟪v k, z⟫|) ≤ u ⟪v k, c • z⟫ :=
    fun k z => by
      refine le_trans (le_of_eq ?_) (hD _)
      rw [real_inner_smul_right, abs_mul, abs_of_pos hc0]
  have hdomk : ∀ k, Integrable (fun z => D * (1 + c * |⟪v k, z⟫|)) (stdGaussian E) :=
    fun k => ((integrable_const 1).add ((hlin (v k)).abs.const_mul c)).const_mul D
  have hui : ∀ k, Integrable (fun z => u ⟪v k, c • z⟫) (stdGaussian E) := fun k => by
    refine Integrable.mono' (hdomk k) (hum k).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonpos (hu0 _)]
    have := hbound k z
    linarith
  have hYi : Integrable Y (stdGaussian E) :=
    (integrable_finsetSum _ fun k _ => hui k).add hai
  have hexpi : Integrable (fun z => Real.exp (Y z)) (stdGaussian E) := by
    have hG : HasGaussianLaw (fun z : E => ⟪a, c • z⟫) (stdGaussian E) := by
      have := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
        (innerSL ℝ (c • a))
      refine this.congr (ae_of_all _ fun z => ?_)
      change ⟪c • a, z⟫ = ⟪a, c • z⟫
      rw [real_inner_smul_left, real_inner_smul_right]
    have h1 := integrable_exp_mul_of_hasGaussianLaw hG 1
    simp only [one_mul] at h1
    have hYm : Measurable Y := (Finset.measurable_sum _ fun k _ => hum k).add
      (by fun_prop : Measurable fun z : E => ⟪a, c • z⟫)
    refine Integrable.mono' h1 (Real.measurable_exp.comp hYm).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp, hY]
    exact add_le_of_nonpos_left (Finset.sum_nonpos fun k _ => hu0 _)
  -- Jensen's inequality
  have hJ : Real.exp (∫ z, Y z ∂stdGaussian E) ≤ ∫ z, Real.exp (Y z) ∂stdGaussian E :=
    ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hYi hexpi
  have hlow : -(D * (M + Real.sqrt (M / (κ * N) * ∑ k, ∑ i, g k i ^ 2))) ≤
      ∫ z, Y z ∂stdGaussian E := by
    have hk : ∀ k, -D * (1 + c * ‖v k‖) ≤ ∫ z, u ⟪v k, c • z⟫ ∂stdGaussian E := fun k => by
      have h1 := integral_mono (hdomk k).neg (hui k) fun z => by
        simpa only [Pi.neg_apply, neg_mul] using hbound k z
      simp only [Pi.neg_apply] at h1
      rw [integral_neg, integral_const_mul,
        integral_add (integrable_const 1) ((hlin (v k)).abs.const_mul c), integral_const_mul]
        at h1
      simp only [integral_const, probReal_univ, one_smul] at h1
      have h2 := mul_le_mul_of_nonneg_left (integral_abs_inner_stdGaussian_le (v k))
        (mul_nonneg hD0 hc0.le)
      linarith
    have hnorm : ∀ k, ‖v k‖ ^ 2 = (N : ℝ)⁻¹ * ∑ i, g k i ^ 2 := fun k => by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        change ((Real.sqrt N)⁻¹ * g k i) ^ 2 = _
        rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    have hCS : ∑ k, ‖v k‖ ≤ Real.sqrt (M / N * ∑ k, ∑ i, g k i ^ 2) := by
      refine Real.le_sqrt_of_sq_le ?_
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      simp only [Finset.card_univ, Fintype.card_fin, hnorm, ← Finset.mul_sum] at this
      refine this.trans_eq ?_
      ring
    have hsqrt : c * Real.sqrt (M / N * ∑ k, ∑ i, g k i ^ 2) ≤
        Real.sqrt (M / (κ * N) * ∑ k, ∑ i, g k i ^ 2) := by
      refine (mul_le_mul_of_nonneg_right hcκ (Real.sqrt_nonneg _)).trans_eq ?_
      rw [← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.2 hκ.le)]
      congr 1
      rw [div_mul_eq_div_div_swap]
      ring
    rw [hY]
    simp only
    rw [integral_add (integrable_finsetSum _ fun k _ => hui k) hai, hlin0, add_zero,
      integral_finsetSum _ fun k _ => hui k]
    refine le_trans ?_ (Finset.sum_le_sum fun k _ => hk k)
    have hsum : ∑ k : Fin M, -D * (1 + c * ‖v k‖) = -(D * (M + c * ∑ k, ‖v k‖)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    rw [hsum, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((mul_le_mul_of_nonneg_left hCS hc0.le).trans hsqrt)) hD0
  have hZlow : (π / κ) ^ ((N : ℝ) / 2) *
      Real.exp (-(D * (M + Real.sqrt (M / (κ * N) * ∑ k, ∑ i, g k i ^ 2)))) ≤
        ∫ σ, Real.exp (-shcherbinaTirozziHamiltonian κ h u g g₀ σ) := by
    rw [hZ]
    exact mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 hlow).trans hJ)
      (Real.rpow_nonneg (by positivity) _)
  have hpos : 0 < (π / κ) ^ ((N : ℝ) / 2) *
      Real.exp (-(D * (M + Real.sqrt (M / (κ * N) * ∑ k, ∑ i, g k i ^ 2)))) :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  refine (inv_anti₀ hpos hZlow).trans_eq ?_
  rw [mul_inv, Real.exp_neg, inv_inv, ← Real.inv_rpow (by positivity), inv_div]

end SpinGlasses
