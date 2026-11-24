/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Gaussian integration by parts for a Gibbs measure with a linear Gaussian energy

Let `μ` be a finite measure on a measurable space `α` (the base law of the spins), and let the
energy be `D a + ∑ₖ zₖ Xₖ a` with bounded measurable `D`, `Xₖ` and a Gaussian parameter vector
`z`. The Gibbs average `⟨Y⟩_z = ∫ Y e^{E_z} dμ / ∫ e^{E_z} dμ` is a smooth function of `z`, with
`∂ₗ ⟨Y⟩ = ⟨Y Xₗ⟩ - ⟨Y⟩⟨Xₗ⟩`, and Gaussian integration by parts gives
`𝔼 Zₖ ⟨Y⟩_Z = ∑ₗ 𝔼[Zₖ Zₗ] 𝔼[⟨Y Xₗ⟩_Z - ⟨Y⟩_Z ⟨Xₗ⟩_Z]`.
The base law is arbitrary: finite or continuous.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped BigOperators

namespace MeasureTheory

variable {α K : Type*} [MeasurableSpace α] [Fintype K] [DecidableEq K] {μ : Measure α}
  [IsFiniteMeasure μ]
  {D : α → ℝ} {X : K → α → ℝ} {Y : α → ℝ} {Eb B M : ℝ}

/-- The Laplace-type integral `z ↦ ∫ Y e^{D + ∑ zₖ Xₖ} dμ` of bounded measurable functions is
Fréchet differentiable, with partial derivatives `∫ Y Xₗ e^{D + ∑ zₖ Xₖ} dμ`. -/
theorem hasFDerivAt_integral_mul_exp_linear
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hYb : ∀ a, |Y a| ≤ M) (z₀ : K → ℝ) :
    ∃ L : (K → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun z : K → ℝ => ∫ a, Y a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) L z₀ ∧
      ∀ l, L (Pi.single l 1) = ∫ a, Y a * Real.exp (D a + ∑ k, z₀ k * X k a) * X l a ∂μ := by
  -- the linear form `z ↦ ∑ₖ Xₖ a zₖ`
  let Lx : α → (K → ℝ) →L[ℝ] ℝ := fun a => ∑ k, X k a • ContinuousLinearMap.proj k
  have hLx : ∀ a z, Lx a z = ∑ k, z k * X k a := by
    intro a z
    simp only [Lx, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    exact sum_congr rfl fun k _ => mul_comm _ _
  have hLxn : ∀ a, ‖Lx a‖ ≤ Fintype.card K * B := by
    intro a
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hLx, Real.norm_eq_abs]
    calc |∑ k, v k * X k a| ≤ ∑ k, |v k * X k a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : K, ‖v‖ * B := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul (by simpa using norm_le_pi_norm v k) (hXb k a) (abs_nonneg _)
            (norm_nonneg _)
      _ = Fintype.card K * B * ‖v‖ := by simp; ring
  -- the integrand and its derivative
  set S : ℝ := ∑ k, (|z₀ k| + 1) * B with hS
  have hS0 : 0 ≤ S := by positivity
  have hexp : ∀ a, ∀ z ∈ Metric.ball z₀ 1, D a + ∑ k, z k * X k a ≤ Eb + S := by
    intro a z hz
    have hzk : ∀ k, |z k| ≤ |z₀ k| + 1 := fun k => by
      have : |z k - z₀ k| < 1 := (dist_le_pi_dist z z₀ k).trans_lt hz
      calc |z k| = |(z k - z₀ k) + z₀ k| := by ring_nf
        _ ≤ |z k - z₀ k| + |z₀ k| := abs_add_le _ _
        _ ≤ 1 + |z₀ k| := by linarith
        _ = |z₀ k| + 1 := by ring
    have hbd := abs_add_sum_mul_le (D a) z (fun k => X k a) (hDb a) (fun k => hXb k a)
    have hsum : ∑ k, |z k| * B ≤ S := sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hzk k) hB
    linarith [le_abs_self (D a + ∑ k, z k * X k a)]
  have hmeasE : ∀ z : K → ℝ, Measurable fun a => D a + ∑ k, z k * X k a := by
    intro z
    exact hD.add (Finset.measurable_sum _ fun k _ => (hX k).const_mul _)
  have hbd : ∀ a, ∀ z ∈ Metric.ball z₀ 1,
      |Y a * Real.exp (D a + ∑ k, z k * X k a)| ≤ M * Real.exp (Eb + S) := by
    intro a z hz
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hYb a) (Real.exp_le_exp.2 (hexp a z hz)) (Real.exp_pos _).le hM
  have hLxm : Measurable fun a => Lx a := by
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (hX k).smul_const _
  have hF'meas : Measurable fun a => (Y a * Real.exp (D a + ∑ k, z₀ k * X k a)) • Lx a :=
    (hY.mul (hmeasE z₀).exp).smul hLxm
  have hF'bd : ∀ a, ‖(Y a * Real.exp (D a + ∑ k, z₀ k * X k a)) • Lx a‖ ≤
      M * Real.exp (Eb + S) * (Fintype.card K * B) := by
    intro a
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hbd a z₀ (Metric.mem_ball_self one_pos)) (hLxn a) (norm_nonneg _)
      (by positivity)
  have hF'int : Integrable (fun a => (Y a * Real.exp (D a + ∑ k, z₀ k * X k a)) • Lx a) μ :=
    (integrable_const (M * Real.exp (Eb + S) * (Fintype.card K * B))).mono'
      hF'meas.aestronglyMeasurable (ae_of_all _ hF'bd)
  refine ⟨∫ a, (Y a * Real.exp (D a + ∑ k, z₀ k * X k a)) • Lx a ∂μ, ?_, fun l => ?_⟩
  · refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun z a => Y a * Real.exp (D a + ∑ k, z k * X k a))
      (F' := fun z a => (Y a * Real.exp (D a + ∑ k, z k * X k a)) • Lx a)
      (bound := fun _ => M * Real.exp (Eb + S) * (Fintype.card K * B)) (s := Metric.ball z₀ 1)
      (Metric.ball_mem_nhds z₀ one_pos)
      (Eventually.of_forall fun z => (hY.mul (hmeasE z).exp).aestronglyMeasurable)
      ((integrable_const (M * Real.exp (Eb + S))).mono'
        (hY.mul (hmeasE z₀).exp).aestronglyMeasurable
        (ae_of_all _ fun a => by
          rw [Real.norm_eq_abs]; exact hbd a z₀ (Metric.mem_ball_self one_pos)))
      hF'meas.aestronglyMeasurable
      (ae_of_all _ fun a z hz => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hbd a z hz) (hLxn a) (norm_nonneg _) (by positivity))
      (integrable_const _) (ae_of_all _ fun a z _ => ?_)
    have hfun : (fun z : K → ℝ => Y a * Real.exp (D a + ∑ k, z k * X k a)) =
        fun z => Y a * Real.exp (D a + Lx a z) := by
      funext z; rw [hLx]
    rw [hfun]
    have := (((Lx a).hasFDerivAt (x := z)).const_add (D a)).exp.const_mul (Y a)
    refine this.congr_fderiv ?_
    rw [hLx]
    ext v
    simp only [smul_apply, smul_eq_mul]
    ring
  · rw [ContinuousLinearMap.integral_apply hF'int]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    have hsingle : Lx a (Pi.single l 1) = X l a := by
      rw [hLx, sum_eq_single l (fun k _ hk => by simp [hk]) (by simp)]
      simp
    simp only [smul_apply, smul_eq_mul, hsingle]

omit [DecidableEq K] in
/-- The exponential of the bounded linear energy is integrable. -/
theorem integrable_exp_linear (hD : Measurable D) (hX : ∀ k, Measurable (X k))
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (z : K → ℝ) :
    Integrable (fun a => Real.exp (D a + ∑ k, z k * X k a)) μ :=
  integrable_exp_of_ae_le
    (hD.add (Finset.measurable_sum _ fun k _ => (hX k).const_mul _)).aemeasurable
    (Filter.Eventually.of_forall fun a => (le_abs_self _).trans
      (abs_add_sum_mul_le (D a) z (fun k => X k a) (hDb a) (fun k => hXb k a)))

/-- **The Gibbs average as a smooth function of the Gaussian parameters.** For `μ ≠ 0` and
bounded measurable data, `z ↦ ∫ Y e^{E_z} / ∫ e^{E_z}` is Fréchet differentiable and its partial
derivative in the direction `l` is `⟨Y Xₗ⟩ - ⟨Y⟩⟨Xₗ⟩` (the covariance of `Y` with the feature). -/
theorem hasFDerivAt_gibbs_ratio_linear [NeZero μ]
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hYb : ∀ a, |Y a| ≤ M) (z₀ : K → ℝ) :
    ∃ L : (K → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun z : K → ℝ => (∫ a, Y a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
        ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ) L z₀ ∧
      ∀ l, L (Pi.single l 1) =
        (∫ a, Y a * X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) /
          (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) -
        ((∫ a, Y a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) /
          (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ)) *
          ((∫ a, X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) /
          (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ)) := by
  obtain ⟨L₁, h₁, hL₁⟩ := hasFDerivAt_integral_mul_exp_linear (μ := μ) hD hX hY hB hM hDb hXb hYb z₀
  obtain ⟨L₂, h₂, hL₂⟩ := hasFDerivAt_integral_mul_exp_linear (μ := μ) (Y := fun _ => 1) hD hX
    measurable_const hB zero_le_one hDb hXb (fun _ => by simp) z₀
  have hi := integrable_exp_linear (μ := μ) hD hX hDb hXb z₀
  have hpos : (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) ≠ 0 := (integral_exp_pos hi).ne'
  have h2' : HasFDerivAt (fun z : K → ℝ => ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ) L₂ z₀ := by
    simpa only [one_mul] using h₂
  have hinv := (hasDerivAt_inv hpos).comp_hasFDerivAt z₀ h2'
  have hmul := h₁.mul hinv
  refine ⟨(∫ a, Y a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) •
      ((-((∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) ^ 2)⁻¹) • L₂) +
      (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ)⁻¹ • L₁, ?_, fun l => ?_⟩
  · convert hmul using 1
    · funext z
      simp [div_eq_mul_inv]
    · simp only [Function.comp]
  have e1 : (∫ a, Y a * Real.exp (D a + ∑ k, z₀ k * X k a) * X l a ∂μ) =
      ∫ a, Y a * X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by ring)
  have e2 : (∫ a, 1 * Real.exp (D a + ∑ k, z₀ k * X k a) * X l a ∂μ) =
      ∫ a, X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by ring)
  rw [add_apply, smul_apply, smul_apply, smul_apply, hL₁ l, hL₂ l, e1, e2]
  simp only [smul_eq_mul]
  field_simp
  ring

omit [DecidableEq K] in
/-- The Gibbs average of a function bounded by `M` is bounded by `M`. -/
theorem abs_gibbs_ratio_le [NeZero μ] (hD : Measurable D) (hX : ∀ k, Measurable (X k))
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B)
    (hYb : ∀ a, |Y a| ≤ M) (z : K → ℝ) :
    |(∫ a, Y a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ| ≤ M := by
  rw [← integral_tilted_eq_div]
  exact abs_integral_tilted_le (integrable_exp_linear hD hX hDb hXb z) hYb

omit [DecidableEq K] in
/-- **Gaussian integration by parts for a Gibbs average with a linear Gaussian energy.**
Let `R Y z` be the Gibbs average `∫ Y e^{D + ∑ zₖ Xₖ} / ∫ e^{D + ∑ zₖ Xₖ}` (the base law `μ` is an
arbitrary finite measure; `D`, `Xₖ`, `Y` are bounded and measurable). For a centered Gaussian
vector `Z`, `𝔼 [Zᵢ R Y (Z)] = ∑ₗ 𝔼[Zᵢ Zₗ] 𝔼[R (Y Xₗ) (Z) - R Y (Z) R Xₗ (Z)]`. -/
theorem integral_mul_gibbs_ratio_eq_sum [NeZero μ] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : K → Ω → ℝ}
    (R : (α → ℝ) → (K → ℝ) → ℝ)
    (hR : ∀ Y z, R Y z = (∫ a, Y a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)
    (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0) (i : K)
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hYb : ∀ a, |Y a| ≤ M) :
    ∫ ω, Z i ω * R Y (fun k => Z k ω) ∂P = ∑ l, (∫ ω, Z i ω * Z l ω ∂P) *
      ∫ ω, (R (fun a => Y a * X l a) (fun k => Z k ω) -
        R Y (fun k => Z k ω) * R (X l) (fun k => Z k ω)) ∂P := by
  classical
  have hRfun : ∀ Y', R Y' = fun z => (∫ a, Y' a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ := fun Y' => funext (hR Y')
  have hder : ∀ z₀ : K → ℝ, ∃ L : (K → ℝ) →L[ℝ] ℝ, HasFDerivAt (R Y) L z₀ ∧ ∀ l,
      L (Pi.single l 1) = R (fun a => Y a * X l a) z₀ - R Y z₀ * R (X l) z₀ := by
    intro z₀
    obtain ⟨L, hL, hLl⟩ := hasFDerivAt_gibbs_ratio_linear (μ := μ) hD hX hY hB hM hDb hXb hYb z₀
    refine ⟨L, by rw [hRfun]; exact hL, fun l => ?_⟩
    rw [hLl l, hR, hR, hR]
  have hdiff : Differentiable ℝ (R Y) := fun z₀ => by
    obtain ⟨L, hL, -⟩ := hder z₀
    exact hL.differentiableAt
  have hbound1 : ∀ y, |R Y y| ≤ M * Real.exp (0 * ∑ l, |y l|) := fun y => by
    rw [zero_mul, Real.exp_zero, mul_one, hR]
    exact abs_gibbs_ratio_le hD hX hDb hXb hYb y
  have hbound2 : ∀ l y, |fderiv ℝ (R Y) y (Pi.single l 1)| ≤
      (2 * M * B) * Real.exp ((0 : ℝ) * ∑ l, |y l|) := by
    intro l y
    obtain ⟨L, hL, hLl⟩ := hder y
    rw [hL.fderiv, hLl l, zero_mul, Real.exp_zero, mul_one]
    have h1 : |R (fun a => Y a * X l a) y| ≤ M * B := by
      rw [hR]
      exact abs_gibbs_ratio_le hD hX hDb hXb (fun a => by
        rw [abs_mul]; exact mul_le_mul (hYb a) (hXb l a) (abs_nonneg _) hM) y
    have h2 : |R Y y| ≤ M := by rw [hR]; exact abs_gibbs_ratio_le hD hX hDb hXb hYb y
    have h3 : |R (X l) y| ≤ B := by
      rw [hR]; exact abs_gibbs_ratio_le hD hX hDb hXb (hXb l) y
    calc |R (fun a => Y a * X l a) y - R Y y * R (X l) y|
        ≤ |R (fun a => Y a * X l a) y| + |R Y y| * |R (X l) y| :=
          (abs_sub _ _).trans (by rw [abs_mul])
      _ ≤ M * B + M * B := add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) hM)
      _ = 2 * M * B := by ring
  have := integral_mul_comp_eq_sum_integral_mul hZ hmean i hdiff (C := M) (c := 0)
    hbound1 (D := fun _ => 2 * M * B) (d := fun _ => 0) hbound2
  rw [this]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  obtain ⟨L, hL, hLl⟩ := hder (fun k => Z k ω)
  beta_reduce
  rw [hL.fderiv, hLl l]

omit [DecidableEq K] in
/-- **Gaussian integration by parts for a Gibbs average multiplied by `G(log Z(z))`.**
Let `Z_part z = ∫ exp(D + ∑_k z_k X_k) dμ` and `R Y z = (∫ Y exp(D + ∑_k z_k X_k) dμ) / Z_part z`
for a nonzero finite base measure `μ` and bounded measurable `D, X_k, Y`. If `G : ℝ → ℝ` is
differentiable with value and derivative of exponential growth `|G t| ≤ CG * exp(cG * |t|)` and
`|G' t| ≤ CG' * exp(cG' * |t|)`, then for a centered Gaussian vector `Z`:
`𝔼[Z_i R Y (Z) G(log Z_part(Z))] =
  ∑_l 𝔼[Z_i Z_l] 𝔼[(R(Y X_l)(Z) - R Y (Z) R(X_l)(Z)) G(log Z_part(Z))
    + R Y (Z) R(X_l)(Z) G'(log Z_part(Z))]`. -/
theorem integral_mul_gibbs_ratio_mul_comp_log_eq_sum [NeZero μ] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : K → Ω → ℝ}
    (R : (α → ℝ) → (K → ℝ) → ℝ)
    (hR : ∀ Y' z, R Y' z = (∫ a, Y' a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)
    (Z_part : (K → ℝ) → ℝ)
    (hZ_part : ∀ z, Z_part z = ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)
    (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0) (i : K)
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hYb : ∀ a, |Y a| ≤ M)
    {G : ℝ → ℝ} (hG : Differentiable ℝ G) {CG cG CG' cG' : ℝ}
    (hGb : ∀ t, |G t| ≤ CG * Real.exp (cG * |t|))
    (hGd : ∀ t, |deriv G t| ≤ CG' * Real.exp (cG' * |t|)) :
    ∫ ω, Z i ω * (R Y (fun k => Z k ω) * G (Real.log (Z_part (fun k => Z k ω)))) ∂P =
      ∑ l, (∫ ω, Z i ω * Z l ω ∂P) *
        ∫ ω, ((R (fun a => Y a * X l a) (fun k => Z k ω) -
              R Y (fun k => Z k ω) * R (X l) (fun k => Z k ω)) *
            G (Real.log (Z_part (fun k => Z k ω))) +
          R Y (fun k => Z k ω) * R (X l) (fun k => Z k ω) *
            deriv G (Real.log (Z_part (fun k => Z k ω)))) ∂P := by
  classical
  have hμ_pos : 0 < μ.real Set.univ := measureReal_univ_pos
  obtain ⟨a₀⟩ := Measure.nonempty_of_neZero μ
  have hEb : 0 ≤ Eb := (abs_nonneg _).trans (hDb a₀)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hYb a₀)
  let B' : ℝ := max B 0
  have hB' : 0 ≤ B' := le_max_right B 0
  have hXb' : ∀ k a, |X k a| ≤ B' := fun k a => (hXb k a).trans (le_max_left B 0)
  have hCG0 : 0 ≤ CG := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hGb 0)) (Real.exp_pos _)
  have hCG'0 : 0 ≤ CG' := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hGd 0)) (Real.exp_pos _)
  have hZ_pos : ∀ z : K → ℝ, 0 < Z_part z := fun z => by
    rw [hZ_part]; exact integral_exp_pos (integrable_exp_linear hD hX hDb hXb' z)
  have hlog_Z_bd : ∀ z : K → ℝ, |Real.log (Z_part z)| ≤
      (|Real.log (μ.real Set.univ)| + Eb) + B' * ∑ k, |z k| := by
    intro z
    let C_z : ℝ := Eb + ∑ k, |z k| * B'
    have hexp_i := integrable_exp_linear (μ := μ) hD hX hDb hXb' z
    have hE_abs : ∀ a, |D a + ∑ k, z k * X k a| ≤ C_z := fun a =>
      abs_add_sum_mul_le (D a) z (fun k => X k a) (hDb a) (fun k => hXb' k a)
    have hup : Z_part z ≤ μ.real Set.univ * Real.exp C_z := by
      rw [hZ_part]
      calc (∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)
          ≤ ∫ _a, Real.exp C_z ∂μ := integral_mono hexp_i (integrable_const _) fun a =>
              Real.exp_le_exp.2 ((le_abs_self _).trans (hE_abs a))
        _ = μ.real Set.univ * Real.exp C_z := by simp [smul_eq_mul]
    have hlow : μ.real Set.univ * Real.exp (-C_z) ≤ Z_part z := by
      rw [hZ_part]
      calc μ.real Set.univ * Real.exp (-C_z)
          = ∫ _a, Real.exp (-C_z) ∂μ := by simp [smul_eq_mul]
        _ ≤ ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ :=
            integral_mono (integrable_const _) hexp_i fun a =>
              Real.exp_le_exp.2 (neg_le_of_abs_le (hE_abs a))
    have hl1 : Real.log (μ.real Set.univ) - C_z ≤ Real.log (Z_part z) := by
      have := Real.log_le_log (mul_pos hμ_pos (Real.exp_pos _)) hlow
      rwa [Real.log_mul hμ_pos.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
    have hl2 : Real.log (Z_part z) ≤ Real.log (μ.real Set.univ) + C_z := by
      have := Real.log_le_log (hZ_pos z) hup
      rwa [Real.log_mul hμ_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    have habs : |Real.log (Z_part z)| ≤ |Real.log (μ.real Set.univ)| + C_z := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le (Real.log (μ.real Set.univ))],
        by linarith [le_abs_self (Real.log (μ.real Set.univ))]⟩
    refine habs.trans_eq ?_
    dsimp only [C_z]; rw [← Finset.sum_mul]; ring
  have hRfun : ∀ Y', R Y' = fun z => (∫ a, Y' a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ := fun Y' => funext (hR Y')
  let Φ (z : K → ℝ) : ℝ := R Y z * G (Real.log (Z_part z))
  have hder : ∀ z₀ : K → ℝ, ∃ L : (K → ℝ) →L[ℝ] ℝ, HasFDerivAt Φ L z₀ ∧ ∀ l,
      L (Pi.single l 1) =
        (R (fun a => Y a * X l a) z₀ - R Y z₀ * R (X l) z₀) * G (Real.log (Z_part z₀)) +
          R Y z₀ * R (X l) z₀ * deriv G (Real.log (Z_part z₀)) := by
    intro z₀
    obtain ⟨L_R, hLR, hLR_l⟩ :=
      hasFDerivAt_gibbs_ratio_linear (μ := μ) hD hX hY hB' hM hDb hXb' hYb z₀
    rw [← hRfun Y] at hLR
    obtain ⟨L_Z, hLZ, hLZ_l⟩ := hasFDerivAt_integral_mul_exp_linear (μ := μ) (Y := fun _ => 1)
      hD hX measurable_const hB' zero_le_one hDb hXb' (fun _ => by simp) z₀
    have hZfun : Z_part = fun z => ∫ a, 1 * Real.exp (D a + ∑ k, z k * X k a) ∂μ := by
      funext z; rw [hZ_part]; simp
    rw [← hZfun] at hLZ
    have hlogZ : HasFDerivAt (fun z => Real.log (Z_part z)) ((Z_part z₀)⁻¹ • L_Z) z₀ :=
      hLZ.log (hZ_pos z₀).ne'
    have hG_logZ : HasFDerivAt (fun z => G (Real.log (Z_part z)))
        (deriv G (Real.log (Z_part z₀)) • ((Z_part z₀)⁻¹ • L_Z)) z₀ :=
      (hG (Real.log (Z_part z₀))).hasDerivAt.comp_hasFDerivAt z₀ hlogZ
    have hprod := hLR.mul hG_logZ
    refine ⟨_, hprod, fun l => ?_⟩
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hLR_l l, hLZ_l l]
    have he1 : (∫ a, Y a * X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) /
        (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) = R (fun a => Y a * X l a) z₀ :=
      (hR _ z₀).symm
    have he2 : (∫ a, Y a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) /
        (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) = R Y z₀ :=
      (hR _ z₀).symm
    have he3 : (∫ a, X l a * Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) /
        (∫ a, Real.exp (D a + ∑ k, z₀ k * X k a) ∂μ) = R (X l) z₀ :=
      (hR _ z₀).symm
    have he4 : (Z_part z₀)⁻¹ * ∫ a, 1 * Real.exp (D a + ∑ k, z₀ k * X k a) * X l a ∂μ =
        R (X l) z₀ := by
      rw [hR (X l) z₀, hZ_part z₀, div_eq_inv_mul]
      congr 1; exact integral_congr_ae (ae_of_all _ fun a => by ring)
    rw [he1, he2, he3, he4]
    ring
  have hdiff : Differentiable ℝ Φ := fun z₀ => (hder z₀).choose_spec.1.differentiableAt
  let A₀ : ℝ := |Real.log (μ.real Set.univ)| + Eb
  have hG_z_bd : ∀ z : K → ℝ, |G (Real.log (Z_part z))| ≤
      (CG * Real.exp (|cG| * A₀)) * Real.exp ((|cG| * B') * ∑ k, |z k|) := fun z => by
    calc |G (Real.log (Z_part z))|
        ≤ CG * Real.exp (cG * |Real.log (Z_part z)|) := hGb _
      _ ≤ CG * Real.exp (|cG| * |Real.log (Z_part z)|) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self cG) (abs_nonneg _))) hCG0
      _ ≤ CG * Real.exp (|cG| * (A₀ + B' * ∑ k, |z k|)) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hlog_Z_bd z) (abs_nonneg cG))) hCG0
      _ = (CG * Real.exp (|cG| * A₀)) * Real.exp ((|cG| * B') * ∑ k, |z k|) := by
          rw [mul_add, Real.exp_add, mul_assoc (|cG|) B', ← mul_assoc CG]
  have hG'_z_bd : ∀ z : K → ℝ, |deriv G (Real.log (Z_part z))| ≤
      (CG' * Real.exp (|cG'| * A₀)) * Real.exp ((|cG'| * B') * ∑ k, |z k|) := fun z => by
    calc |deriv G (Real.log (Z_part z))|
        ≤ CG' * Real.exp (cG' * |Real.log (Z_part z)|) := hGd _
      _ ≤ CG' * Real.exp (|cG'| * |Real.log (Z_part z)|) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self cG') (abs_nonneg _))) hCG'0
      _ ≤ CG' * Real.exp (|cG'| * (A₀ + B' * ∑ k, |z k|)) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hlog_Z_bd z) (abs_nonneg cG'))) hCG'0
      _ = (CG' * Real.exp (|cG'| * A₀)) * Real.exp ((|cG'| * B') * ∑ k, |z k|) := by
          rw [mul_add, Real.exp_add, mul_assoc (|cG'|) B', ← mul_assoc CG']
  have hbound1 : ∀ z : K → ℝ, |Φ z| ≤
      (M * (CG * Real.exp (|cG| * A₀))) * Real.exp ((|cG| * B') * ∑ k, |z k|) := fun z => by
    dsimp only [Φ]
    rw [abs_mul]
    have hRY : |R Y z| ≤ M := by rw [hR]; exact abs_gibbs_ratio_le hD hX hDb hXb' hYb z
    calc |R Y z| * |G (Real.log (Z_part z))|
        ≤ M * ((CG * Real.exp (|cG| * A₀)) * Real.exp ((|cG| * B') * ∑ k, |z k|)) :=
          mul_le_mul hRY (hG_z_bd z) (abs_nonneg _) hM
      _ = _ := by ring
  let c_max : ℝ := max (|cG| * B') (|cG'| * B')
  have hbound2 : ∀ (l : K) (z : K → ℝ), |fderiv ℝ Φ z (Pi.single l 1)| ≤
      (2 * M * B' * (CG * Real.exp (|cG| * A₀)) +
        M * B' * (CG' * Real.exp (|cG'| * A₀))) * Real.exp (c_max * ∑ k, |z k|) := by
    intro l z
    obtain ⟨L, hL, hLl⟩ := hder z
    rw [hL.fderiv, hLl l]
    have h1 : |R (fun a => Y a * X l a) z| ≤ M * B' := by
      rw [hR]; exact abs_gibbs_ratio_le hD hX hDb hXb' (fun a => by
        rw [abs_mul]; exact mul_le_mul (hYb a) (hXb' l a) (abs_nonneg _) hM) z
    have h2 : |R Y z| ≤ M := by rw [hR]; exact abs_gibbs_ratio_le hD hX hDb hXb' hYb z
    have h3 : |R (X l) z| ≤ B' := by rw [hR]; exact abs_gibbs_ratio_le hD hX hDb hXb' (hXb' l) z
    have hcov_bd : |R (fun a => Y a * X l a) z - R Y z * R (X l) z| ≤ 2 * M * B' := by
      calc |R (fun a => Y a * X l a) z - R Y z * R (X l) z|
          ≤ |R (fun a => Y a * X l a) z| + |R Y z| * |R (X l) z| :=
            (abs_sub _ _).trans (by rw [abs_mul])
        _ ≤ M * B' + M * B' := add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) hM)
        _ = 2 * M * B' := by ring
    have hprod_bd : |R Y z * R (X l) z| ≤ M * B' := by
      rw [abs_mul]; exact mul_le_mul h2 h3 (abs_nonneg _) hM
    have hsum_nn : 0 ≤ ∑ k, |z k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hexp1 : Real.exp ((|cG| * B') * ∑ k, |z k|) ≤ Real.exp (c_max * ∑ k, |z k|) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hsum_nn)
    have hexp2 : Real.exp ((|cG'| * B') * ∑ k, |z k|) ≤ Real.exp (c_max * ∑ k, |z k|) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hsum_nn)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have ht1 : |R (fun a => Y a * X l a) z - R Y z * R (X l) z| * |G (Real.log (Z_part z))| ≤
        2 * M * B' * (CG * Real.exp (|cG| * A₀)) * Real.exp (c_max * ∑ k, |z k|) := by
      calc _ ≤ (2 * M * B') * ((CG * Real.exp (|cG| * A₀)) *
              Real.exp ((|cG| * B') * ∑ k, |z k|)) :=
            mul_le_mul hcov_bd (hG_z_bd z) (abs_nonneg _) (by positivity)
        _ ≤ (2 * M * B') * ((CG * Real.exp (|cG| * A₀)) * Real.exp (c_max * ∑ k, |z k|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp1 (by positivity)) (by positivity)
        _ = _ := by ring
    have ht2 : |R Y z * R (X l) z| * |deriv G (Real.log (Z_part z))| ≤
        M * B' * (CG' * Real.exp (|cG'| * A₀)) * Real.exp (c_max * ∑ k, |z k|) := by
      calc _ ≤ (M * B') * ((CG' * Real.exp (|cG'| * A₀)) *
              Real.exp ((|cG'| * B') * ∑ k, |z k|)) :=
            mul_le_mul hprod_bd (hG'_z_bd z) (abs_nonneg _) (by positivity)
        _ ≤ (M * B') * ((CG' * Real.exp (|cG'| * A₀)) * Real.exp (c_max * ∑ k, |z k|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp2 (by positivity)) (by positivity)
        _ = _ := by ring
    calc _ ≤ 2 * M * B' * (CG * Real.exp (|cG| * A₀)) * Real.exp (c_max * ∑ k, |z k|) +
            M * B' * (CG' * Real.exp (|cG'| * A₀)) * Real.exp (c_max * ∑ k, |z k|) :=
          add_le_add ht1 ht2
      _ = _ := by ring
  have h := integral_mul_comp_eq_sum_integral_mul hZ hmean i hdiff
    (C := M * (CG * Real.exp (|cG| * A₀))) (c := |cG| * B') hbound1
    (D := fun _ => 2 * M * B' * (CG * Real.exp (|cG| * A₀)) +
      M * B' * (CG' * Real.exp (|cG'| * A₀)))
    (d := fun _ => c_max) hbound2
  dsimp only [Φ] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  obtain ⟨L, hL, hLl⟩ := hder (fun k => Z k ω)
  beta_reduce
  rw [hL.fderiv, hLl l]

omit [DecidableEq K] in
/-- The Gibbs average is continuous in the parameters. -/
theorem continuous_gibbs_ratio_linear [NeZero μ] (R : (α → ℝ) → (K → ℝ) → ℝ)
    (hR : ∀ Y z, R Y z = (∫ a, Y a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hYb : ∀ a, |Y a| ≤ M) :
    Continuous (R Y) := by
  classical
  rw [funext (hR Y)]
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨L, hL, -⟩ := hasFDerivAt_gibbs_ratio_linear (μ := μ) hD hX hY hB hM hDb hXb hYb z₀
  exact hL.continuousAt

omit [DecidableEq K] in
/-- **Derivative of a Gibbs average along a path of parameters.** If `t ↦ z t` has derivative
`z'` at `t`, then `t ↦ ⟨Y⟩_{z t}` has derivative `∑ₗ z'ₗ (⟨Y Xₗ⟩ - ⟨Y⟩⟨Xₗ⟩)` at `t`. -/
theorem hasDerivAt_gibbs_ratio_path [NeZero μ] (R : (α → ℝ) → (K → ℝ) → ℝ)
    (hR : ∀ Y z, R Y z = (∫ a, Y a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hYb : ∀ a, |Y a| ≤ M)
    {z : ℝ → K → ℝ} {z' : K → ℝ} {t : ℝ} (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => R Y (z s))
      (∑ l, z' l * (R (fun a => Y a * X l a) (z t) - R Y (z t) * R (X l) (z t))) t := by
  classical
  obtain ⟨L, hL, hLl⟩ := hasFDerivAt_gibbs_ratio_linear (μ := μ) hD hX hY hB hM hDb hXb hYb (z t)
  rw [← funext (hR Y)] at hL
  refine (hL.comp_hasDerivAt t hz).congr_deriv ?_
  have hz' : z' = ∑ l, z' l • (Pi.single l 1 : K → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz', map_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_smul, hLl l, hR, hR, hR]
  simp [smul_eq_mul]

omit [DecidableEq K] in
/-- **Derivative of an expected Gibbs average along a random parameter path.** Let `z s ω` be a
random path of parameters, differentiable in `s` near `t` with derivative `z' s ω`, and dominated
near `t`
by an integrable function. Then `s ↦ 𝔼 ⟨Y⟩_{z s}` is differentiable at `t`, and its derivative is
`𝔼 ∑ₗ z'ₗ (⟨Y Xₗ⟩ - ⟨Y⟩⟨Xₗ⟩)`. The Gaussian parameters may be unbounded. -/
theorem hasDerivAt_integral_gibbs_ratio_path [NeZero μ] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (R : (α → ℝ) → (K → ℝ) → ℝ)
    (hR : ∀ Y z, R Y z = (∫ a, Y a * Real.exp (D a + ∑ k, z k * X k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * X k a) ∂μ)
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hYb : ∀ a, |Y a| ≤ M)
    {z z' : ℝ → Ω → K → ℝ} {t δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ ω, ∀ s ∈ Metric.ball t δ, HasDerivAt (fun r => z r ω) (z' s ω) s)
    (hzm : ∀ s, Measurable (z s)) (hz'm : Measurable (z' t))
    {g : Ω → ℝ} (hg : Integrable g P)
    (hgb : ∀ ω, ∀ s ∈ Metric.ball t δ, ∀ l, |z' s ω l| ≤ g ω) :
    HasDerivAt (fun s => ∫ ω, R Y (z s ω) ∂P)
      (∫ ω, ∑ l, z' t ω l * (R (fun a => Y a * X l a) (z t ω) -
        R Y (z t ω) * R (X l) (z t ω)) ∂P) t := by
  classical
  have hcont : ∀ (Y' : α → ℝ) (M' : ℝ), 0 ≤ M' → Measurable Y' → (∀ a, |Y' a| ≤ M') →
      Continuous (R Y') := fun _ _ hM' hY' hY'b =>
    continuous_gibbs_ratio_linear R hR hD hX hY' hB hM' hDb hXb hY'b
  have hYX : ∀ l, Measurable (fun a => Y a * X l a) := fun l => hY.mul (hX l)
  have hYXb : ∀ l a, |Y a * X l a| ≤ M * B := fun l a => by
    rw [abs_mul]; exact mul_le_mul (hYb a) (hXb l a) (abs_nonneg _) hM
  have hMB : 0 ≤ M * B := mul_nonneg hM hB
  have hmeasR : ∀ (Y' : α → ℝ) (M' : ℝ) (hM' : 0 ≤ M') (hY' : Measurable Y')
      (hY'b : ∀ a, |Y' a| ≤ M') (s : ℝ), Measurable fun ω => R Y' (z s ω) :=
    fun Y' M' hM' hY' hY'b s => (hcont Y' M' hM' hY' hY'b).measurable.comp (hzm s)
  have hRb : ∀ (Y' : α → ℝ) (M' : ℝ), (∀ a, |Y' a| ≤ M') → ∀ z, |R Y' z| ≤ M' := by
    intro Y' M' hY'b z0
    rw [hR]
    exact abs_gibbs_ratio_le hD hX hDb hXb hY'b z0
  -- the integrand and its derivative
  have hF'b : ∀ ω, ∀ s ∈ Metric.ball t δ, ‖∑ l, z' s ω l * (R (fun a => Y a * X l a) (z s ω) -
        R Y (z s ω) * R (X l) (z s ω))‖ ≤ (Fintype.card K * (2 * M * B)) * g ω := by
    intro ω s hs
    rw [Real.norm_eq_abs]
    calc |∑ l, z' s ω l * (R (fun a => Y a * X l a) (z s ω) - R Y (z s ω) * R (X l) (z s ω))|
        ≤ ∑ l, |z' s ω l * (R (fun a => Y a * X l a) (z s ω) -
            R Y (z s ω) * R (X l) (z s ω))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : K, g ω * (2 * M * B) := Finset.sum_le_sum fun l _ => by
          rw [abs_mul]
          refine mul_le_mul (hgb ω s hs l) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hgb ω s hs l))
          calc |R (fun a => Y a * X l a) (z s ω) - R Y (z s ω) * R (X l) (z s ω)|
              ≤ |R (fun a => Y a * X l a) (z s ω)| + |R Y (z s ω)| * |R (X l) (z s ω)| :=
                (abs_sub _ _).trans (by rw [abs_mul])
            _ ≤ M * B + M * B := add_le_add (hRb _ _ (hYXb l) _)
                (mul_le_mul (hRb Y M hYb _) (hRb (X l) B (hXb l) _) (abs_nonneg _) hM)
            _ = 2 * M * B := by ring
      _ = (Fintype.card K * (2 * M * B)) * g ω := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hmeasF' : Measurable fun ω => ∑ l, z' t ω l * (R (fun a => Y a * X l a) (z t ω) -
      R Y (z t ω) * R (X l) (z t ω)) := by
    refine Finset.measurable_sum _ fun l _ => ?_
    refine ((measurable_pi_apply l).comp hz'm).mul ?_
    exact (hmeasR _ _ hMB (hYX l) (hYXb l) t).sub
      ((hmeasR Y M hM hY hYb t).mul (hmeasR (X l) B hB (hX l) (hXb l) t))
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => R Y (z s ω)) (F' := fun s ω => ∑ l, z' s ω l *
      (R (fun a => Y a * X l a) (z s ω) - R Y (z s ω) * R (X l) (z s ω)))
    (s := Metric.ball t δ) (x₀ := t) (Metric.ball_mem_nhds t hδ)
    (Eventually.of_forall fun s => (hmeasR Y M hM hY hYb s).aestronglyMeasurable)
    ((integrable_const M).mono' (hmeasR Y M hM hY hYb t).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hRb Y M hYb _))
    hmeasF'.aestronglyMeasurable
    (ae_of_all _ fun ω s hs => hF'b ω s hs) (hg.const_mul _)
    (ae_of_all _ fun ω s hs => hasDerivAt_gibbs_ratio_path R hR hD hX hY hB hM hDb hXb hYb
      (hz ω s hs))
  exact this.2

end MeasureTheory
