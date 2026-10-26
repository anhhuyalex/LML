/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.SpinGlasses.SKDecoupled

/-!
# The replica-symmetric fixed-point equation of the SK model

For `β, h ∈ ℝ`, the replica-symmetric overlap `q` solves (Talagrand, Eq. (1.74))
$$q = \mathbb{E}\tanh^2(\beta z\sqrt{q} + h), \qquad z \sim \mathcal{N}(0, 1).$$
This module shows that the map `ψ(x) = 𝔼 tanh²(β z √x + h)` is continuous and takes values in
`[0, 1]`, so that the equation has a solution `q ∈ [0, 1]` (intermediate value theorem).

It also establishes the stability of the fixed point under perturbation of inverse temperature
(Talagrand, Lemma 1.7.5): when changing $\beta$ to $\beta_- = \beta \sqrt{1 - 1/N}$, the fixed point
satisfies $|q - q_-| \le 1/N$ for all $4\beta^2 < 1$.

## Main declarations

* `SpinGlasses.continuous_fixedPointMap`: continuity of `ψ`.
* `SpinGlasses.exists_fixedPoint`: the existence of a fixed point `q ∈ [0, 1]`.
* `SpinGlasses.abs_fixedPointMap_sub_le`: Lipschitz bound $|H(w_1) - H(w_2)| \le 2 |w_1^2 - w_2^2|$.
* `SpinGlasses.sk_fixed_point_shift_le`: Lemma 1.7.5, $|q - q_-| \le 1/N$.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.3, Eq. (1.74).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace SpinGlasses

/-- `ψ(x) = 𝔼 tanh²(β z √x + h)` is continuous in `x`. -/
theorem continuous_fixedPointMap (β h : ℝ) :
    Continuous fun x : ℝ =>
      ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun x => ?_) (fun x => ?_)
    (integrable_const _) (ae_of_all _ fun z => ?_)
  · exact ((Real.continuous_tanh.comp (by fun_prop : Continuous fun z : ℝ =>
      β * Real.sqrt x * z + h)).pow 2).aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (Real.tanh_sq_lt_one _).le
  · exact (Real.continuous_tanh.comp (by fun_prop : Continuous fun x : ℝ =>
      β * Real.sqrt x * z + h)).pow 2

/-- `0 ≤ ψ(x) ≤ 1`. -/
theorem fixedPointMap_mem_Icc (β h x : ℝ) :
    ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun z => sq_nonneg _, ?_⟩
  calc ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)
      ≤ ∫ z : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) := by
        exact integral_mono (integrable_tanh_sq _ (by fun_prop)) (integrable_const _)
          fun z => (Real.tanh_sq_lt_one _).le
    _ = 1 := by simp

/-- A fixed point `q = ψ(q)` lies in `[0, 1]`. -/
theorem fixedPoint_mem_Icc {β h q : ℝ}
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    q ∈ Icc (0 : ℝ) 1 :=
  hfix ▸ fixedPointMap_mem_Icc β h q

/-- A fixed point `q = ψ(q)` satisfies `|q| ≤ 1`. -/
theorem abs_fixedPoint_le_one {β h q : ℝ}
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    |q| ≤ 1 :=
  abs_le.2 ⟨by linarith [(fixedPoint_mem_Icc hfix).1], (fixedPoint_mem_Icc hfix).2⟩

/-- **Existence of the replica-symmetric overlap (Eq. 1.74):** there is `q ∈ [0, 1]` with
`q = 𝔼 tanh²(β z √q + h)`. -/
theorem exists_fixedPoint (β h : ℝ) :
    ∃ q ∈ Icc (0 : ℝ) 1,
      q = ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  set ψ : ℝ → ℝ := fun x => ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)
  have hcont : ContinuousOn (fun x => ψ x - x) (Icc 0 1) :=
    ((continuous_fixedPointMap β h).sub continuous_id).continuousOn
  have h0 : 0 ≤ ψ 0 - 0 := by rw [sub_zero]; exact (fixedPointMap_mem_Icc β h 0).1
  have h1 : ψ 1 - 1 ≤ 0 := by linarith [(fixedPointMap_mem_Icc β h 1).2]
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont ⟨h1, h0⟩
  exact ⟨q, hq, by simp only [ψ] at hq0; linarith⟩

section Stability

open Filter

/-- `|z|` is integrable against the standard Gaussian measure. -/
theorem integrable_abs_id_gaussianReal : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
  refine (integrable_exp_mul_abs_gaussianReal 1).mono' (by fun_prop)
    (Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_abs, one_mul]
  exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (|z|))

/-- Affine map `z ↦ w * z + h` is continuous. -/
theorem continuous_affine (w h : ℝ) : Continuous fun z : ℝ => w * z + h :=
  (continuous_id'.const_mul w).add continuous_const

/-- `z ↦ tanh (w * z + h)` is continuous. -/
theorem continuous_tanh_affine (w h : ℝ) : Continuous fun z : ℝ => Real.tanh (w * z + h) :=
  Real.continuous_tanh.comp (continuous_affine w h)

/-- `z ↦ tanh²(w * z + h)` is continuous. -/
theorem continuous_tanh_sq_affine (w h : ℝ) :
    Continuous fun z : ℝ => Real.tanh (w * z + h) ^ 2 :=
  (continuous_tanh_affine w h).pow 2

/-- `z ↦ tanh²(w * z + h)` is integrable against the standard Gaussian. -/
theorem integrable_tanh_sq_affine (w h : ℝ) :
    Integrable (fun z : ℝ => Real.tanh (w * z + h) ^ 2) (gaussianReal 0 1) :=
  MeasureTheory.integrable_tanh_sq' (fun z => w * z + h) (by fun_prop)

/-- Permutation symmetry of powers of `tanh (β z √q + h)` vs `tanh (β √q z + h)`. -/
@[simp] theorem integral_tanh_pow_mul_z_sqrt_eq (β q h : ℝ) (k : ℕ) :
    (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ k ∂(gaussianReal 0 1)) =
      ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ k ∂(gaussianReal 0 1) := by
  congr 1; ext z; congr 2; ring

/-- Permutation symmetry of `log (cosh (β z √q + h))` vs `log (cosh (β √q z + h))`. -/
@[simp] theorem integral_log_cosh_mul_z_sqrt_eq (β q h : ℝ) :
    (∫ z : ℝ, Real.log (Real.cosh (β * z * Real.sqrt q + h)) ∂(gaussianReal 0 1)) =
      ∫ z : ℝ, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1) := by
  congr 1; ext z; congr 2; ring

/-- The first derivative of the integrand `z ↦ 2 tanh(w z + h) (1 - tanh²(w z + h))` is
continuous. -/
theorem continuous_tanh_deriv_affine (w h : ℝ) :
    Continuous fun z : ℝ => 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) :=
  ((continuous_tanh_affine w h).const_mul 2).mul
    (continuous_const.sub (continuous_tanh_sq_affine w h))

/-- The second derivative of the integrand `z ↦ 2 (1 - tanh²)(1 - 3 tanh²)` is continuous. -/
theorem continuous_tanh_second_deriv_affine (w h : ℝ) :
    Continuous fun z : ℝ => 2 * (1 - Real.tanh (w * z + h) ^ 2) *
      (1 - 3 * Real.tanh (w * z + h) ^ 2) :=
  ((continuous_const.sub (continuous_tanh_sq_affine w h)).const_mul 2).mul
    (continuous_const.sub ((continuous_tanh_sq_affine w h).const_mul 3))

/-- **Parameter derivative of the fixed-point map via Stein's lemma:**
$$\frac{d}{dw} \mathbb{E}\tanh^2(w z + h) = w \mathbb{E}[f''(w z + h)],$$
where $f(x) = \tanh^2 x$ and $f''(x) = 2 (1 - \tanh^2 x)(1 - 3 \tanh^2 x)$. -/
theorem hasDerivAt_fixedPointMap_param (h : ℝ) (w : ℝ) :
    HasDerivAt (fun v => ∫ z : ℝ, Real.tanh (v * z + h) ^ 2 ∂(gaussianReal 0 1))
      (w * ∫ z : ℝ, 2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2)
        ∂(gaussianReal 0 1)) w := by
  have h_diff : HasDerivAt (fun v => ∫ z : ℝ, Real.tanh (v * z + h) ^ 2 ∂(gaussianReal 0 1))
      (∫ z : ℝ, 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z
        ∂(gaussianReal 0 1)) w := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
      (F := fun v z => Real.tanh (v * z + h) ^ 2)
      (F' := fun v z => 2 * Real.tanh (v * z + h) * (1 - Real.tanh (v * z + h) ^ 2) * z)
      univ_mem
      (Eventually.of_forall fun v => (continuous_tanh_sq_affine v h).aestronglyMeasurable)
      (integrable_tanh_sq_affine w h)
      ((continuous_tanh_deriv_affine w h |>.mul continuous_id').aestronglyMeasurable)
      (bound := fun z => 2 * |z|)
      (ae_of_all _ fun z v _ => ?_)
      (integrable_abs_id_gaussianReal.const_mul 2)
      (ae_of_all _ fun z v _ => ?_)).2
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (Real.abs_deriv_tanh_sq_le _) (abs_nonneg _)
    · have h_lin : HasDerivAt (fun v => v * z + h) z v := by
        simpa using ((hasDerivAt_id' v).mul_const z).add_const h
      exact (Real.hasDerivAt_tanh_sq (v * z + h)).comp v h_lin
  have h_stein : ∫ z : ℝ, 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z
        ∂(gaussianReal 0 1) =
      w * ∫ z : ℝ, 2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2)
        ∂(gaussianReal 0 1) := by
    have hF_deriv : ∀ z : ℝ, HasDerivAt (fun y => 2 * Real.tanh (w * y + h) *
        (1 - Real.tanh (w * y + h) ^ 2))
        (w * (2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2))) z := by
      intro z
      have h_lin : HasDerivAt (fun y => w * y + h) w z := by
        simpa using ((hasDerivAt_id' z).const_mul w).add_const h
      have h_comp := (Real.hasDerivAt_tanh_sq_deriv (w * z + h)).comp z h_lin
      convert h_comp using 1
      · rfl
      · ring
    have hxF : Integrable (fun z : ℝ => z * (2 * Real.tanh (w * z + h) *
        (1 - Real.tanh (w * z + h) ^ 2))) (gaussianReal 0 1) := by
      refine (integrable_abs_id_gaussianReal.const_mul 2).mono' ?_ ?_
      · exact (continuous_id'.mul (continuous_tanh_deriv_affine w h)).aestronglyMeasurable
      · refine Eventually.of_forall fun z => ?_
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.abs_deriv_tanh_sq_le _) (abs_nonneg _)
    have hF' : Integrable (fun z : ℝ => w * (2 * (1 - Real.tanh (w * z + h) ^ 2) *
        (1 - 3 * Real.tanh (w * z + h) ^ 2))) (gaussianReal 0 1) := by
      refine (integrable_const (2 * |w|)).mono' ?_ ?_
      · exact (continuous_const.mul (continuous_tanh_second_deriv_affine w h)).aestronglyMeasurable
      · refine Eventually.of_forall fun z => ?_
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.abs_tanh_sq_second_deriv_le _) (abs_nonneg _)
    have h_ibp := integral_id_mul_gaussianReal_eq (v := 1) hF_deriv hxF hF'
    simp only [NNReal.coe_one, one_mul] at h_ibp
    have h_comm : (fun z => 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z) =
        fun z => z * (2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2)) := by
      ext z; ring
    rw [h_comm, h_ibp, ← integral_const_mul]
  rwa [h_stein] at h_diff

/-- The parameter derivative $|H'(w)|$ is bounded by $2 |w|$. -/
theorem abs_deriv_fixedPointMap_param_le (h : ℝ) (w : ℝ) :
    |w * ∫ z : ℝ, 2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2)
      ∂(gaussianReal 0 1)| ≤ 2 * |w| := by
  rw [abs_mul, mul_comm]
  have h_int_le : |∫ z : ℝ, 2 * (1 - Real.tanh (w * z + h) ^ 2) *
      (1 - 3 * Real.tanh (w * z + h) ^ 2) ∂(gaussianReal 0 1)| ≤ 2 := by
    calc |∫ z : ℝ, 2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2)
        ∂(gaussianReal 0 1)|
      _ ≤ ∫ z : ℝ, |2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2)|
        ∂(gaussianReal 0 1) := abs_integral_le_integral_abs
      _ ≤ ∫ z : ℝ, (2 : ℝ) ∂(gaussianReal 0 1) := by
          refine integral_mono ?_ (integrable_const 2) (fun z => Real.abs_tanh_sq_second_deriv_le _)
          refine (integrable_const (2 : ℝ)).mono'
            (continuous_tanh_second_deriv_affine w h).norm.aestronglyMeasurable ?_
          refine ae_of_all _ fun z => ?_
          simpa using Real.abs_tanh_sq_second_deriv_le _
      _ = 2 := by simp
  exact mul_le_mul_of_nonneg_right h_int_le (abs_nonneg w)

/-- **Lipschitz bound on the fixed-point map:**
$$|H(w_1) - H(w_2)| \le 2 |w_1^2 - w_2^2|.$$ -/
theorem abs_fixedPointMap_sub_le (h : ℝ) {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    |(∫ z : ℝ, Real.tanh (w₁ * z + h) ^ 2 ∂(gaussianReal 0 1)) -
      (∫ z : ℝ, Real.tanh (w₂ * z + h) ^ 2 ∂(gaussianReal 0 1))| ≤ 2 * |w₁ ^ 2 - w₂ ^ 2| := by
  set F := fun w => ∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1)
  set g := fun t => F ((1 - t) * w₁ + t * w₂)
  have h_lin : ∀ t, HasDerivAt (fun s => (1 - s) * w₁ + s * w₂) (w₂ - w₁) t := by
    intro t
    have h1 : HasDerivAt (fun s => (1 - s) * w₁) (-w₁) t := by
      simpa using ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id' t)).mul_const w₁
    have h2 : HasDerivAt (fun s => s * w₂) w₂ t := by
      simpa using (hasDerivAt_id' t).mul_const w₂
    have hsum := h1.add h2
    have heq : -w₁ + w₂ = w₂ - w₁ := by ring
    exact heq ▸ hsum
  have hg_deriv : ∀ t, HasDerivAt g (deriv F ((1 - t) * w₁ + t * w₂) * (w₂ - w₁)) t := by
    intro t
    have hF_deriv := hasDerivAt_fixedPointMap_param h ((1 - t) * w₁ + t * w₂)
    have h_comp := hF_deriv.comp t (h_lin t)
    rw [hF_deriv.deriv]
    convert h_comp using 1
    rfl
  have hg_bdd : ∀ t ∈ Icc (0 : ℝ) 1, |deriv g t| ≤ 2 * |w₁ ^ 2 - w₂ ^ 2| := by
    rintro t ⟨ht0, ht1⟩
    have h_dg := (hg_deriv t).deriv
    rw [h_dg, abs_mul]
    have hF_deriv := hasDerivAt_fixedPointMap_param h ((1 - t) * w₁ + t * w₂)
    rw [hF_deriv.deriv]
    have h_dF_le := abs_deriv_fixedPointMap_param_le h ((1 - t) * w₁ + t * w₂)
    have h_wt_nonneg : 0 ≤ (1 - t) * w₁ + t * w₂ := by
      have : 0 ≤ 1 - t := by linarith
      nlinarith
    rw [abs_of_nonneg h_wt_nonneg] at h_dF_le
    have h_wt_le : (1 - t) * w₁ + t * w₂ ≤ w₁ + w₂ := by
      calc (1 - t) * w₁ + t * w₂ = w₁ + t * (w₂ - w₁) := by ring
        _ ≤ w₁ + 1 * w₂ := by nlinarith
        _ = w₁ + w₂ := by ring
    have h_step1 : |((1 - t) * w₁ + t * w₂) * ∫ z, 2 *
        (1 - Real.tanh (((1 - t) * w₁ + t * w₂) * z + h) ^ 2) *
        (1 - 3 * Real.tanh (((1 - t) * w₁ + t * w₂) * z + h) ^ 2) ∂(gaussianReal 0 1)| * |w₂ - w₁|
      ≤ (2 * ((1 - t) * w₁ + t * w₂)) * |w₂ - w₁| :=
        mul_le_mul_of_nonneg_right h_dF_le (abs_nonneg _)
    have h_step2 : (2 * ((1 - t) * w₁ + t * w₂)) * |w₂ - w₁| ≤ (2 * (w₁ + w₂)) * |w₂ - w₁| := by
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      nlinarith
    have h_step3 : (2 * (w₁ + w₂)) * |w₂ - w₁| = 2 * |w₁ ^ 2 - w₂ ^ 2| := by
      have : (w₁ + w₂) * |w₂ - w₁| = |w₁ ^ 2 - w₂ ^ 2| := by
        rw [← abs_of_nonneg (by linarith : 0 ≤ w₁ + w₂), ← abs_mul]
        have heq : (w₁ + w₂) * (w₂ - w₁) = -(w₁ ^ 2 - w₂ ^ 2) := by ring
        rw [heq, abs_neg]
      linarith
    linarith
  have hg_diff : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ g t :=
    fun t _ => (hg_deriv t).differentiableAt
  have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le hg_diff
    (fun t ht => by simpa [Real.norm_eq_abs] using hg_bdd t ht)
    (convex_Icc (0 : ℝ) 1) (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simp only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h_mvt
  have hg0 : g 0 = F w₁ := by
    change F ((1 - 0) * w₁ + 0 * w₂) = F w₁
    have : (1 - 0 : ℝ) * w₁ + 0 * w₂ = w₁ := by ring
    rw [this]
  have hg1 : g 1 = F w₂ := by
    change F ((1 - 1) * w₁ + 1 * w₂) = F w₂
    have : (1 - 1 : ℝ) * w₁ + 1 * w₂ = w₂ := by ring
    rw [this]
  rw [hg0, hg1] at h_mvt
  rw [abs_sub_comm]
  exact h_mvt

/-- **Fixed-point shift under small parameter change (Talagrand Lemma 1.7.5):**
For $\beta < 1/2$, changing $\beta$ to $\beta_- = \beta \sqrt{1 - 1/N}$ shifts the fixed point
$q = \mathbb{E}\tanh^2(\beta z \sqrt{q} + h)$ by at most $1/N$:
$$|q - q_-| \le \frac{1}{N}.$$ -/
theorem sk_fixed_point_shift_le {N : ℕ} (hN : 0 < N) (β h q q_minus : ℝ)
    (hβ_pos : 0 ≤ β) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hfix_minus : ∫ z : ℝ, Real.tanh (β * Real.sqrt (1 - (N : ℝ)⁻¹) * Real.sqrt q_minus * z + h) ^ 2
      ∂(gaussianReal 0 1) = q_minus) :
    |q - q_minus| ≤ 1 / (N : ℝ) := by
  have hq_mem := fixedPoint_mem_Icc hfix
  have hqm_mem := fixedPoint_mem_Icc hfix_minus
  have hq0 : 0 ≤ q := hq_mem.1
  have hq1 : q ≤ 1 := hq_mem.2
  have hqm0 : 0 ≤ q_minus := hqm_mem.1
  have hN_ge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN_inv_le : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN_ge
  have h1N : 0 ≤ 1 - (N : ℝ)⁻¹ := by linarith
  set β_minus := β * Real.sqrt (1 - (N : ℝ)⁻¹)
  have hβm_pos : 0 ≤ β_minus := mul_nonneg hβ_pos (Real.sqrt_nonneg _)
  have hw1 : 0 ≤ β * Real.sqrt q := mul_nonneg hβ_pos (Real.sqrt_nonneg _)
  have hw2 : 0 ≤ β_minus * Real.sqrt q_minus := mul_nonneg hβm_pos (Real.sqrt_nonneg _)
  have h_bound := abs_fixedPointMap_sub_le h hw1 hw2
  rw [hfix, hfix_minus] at h_bound
  have hw1_sq : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, Real.sq_sqrt hq0]
  have hw2_sq : (β_minus * Real.sqrt q_minus) ^ 2 = β_minus ^ 2 * q_minus := by
    rw [mul_pow, Real.sq_sqrt hqm0]
  rw [hw1_sq, hw2_sq] at h_bound
  have hβm_sq : β_minus ^ 2 = β ^ 2 * (1 - (N : ℝ)⁻¹) := by
    dsimp [β_minus]
    rw [mul_pow, Real.sq_sqrt h1N]
  have h_sub_id : β ^ 2 * q - β_minus ^ 2 * q_minus =
      (β ^ 2 - β_minus ^ 2) * q + β_minus ^ 2 * (q - q_minus) := by ring
  rw [h_sub_id] at h_bound
  have h_diff_sq : β ^ 2 - β_minus ^ 2 = β ^ 2 / (N : ℝ) := by
    rw [hβm_sq]
    ring
  have h_tri : |(β ^ 2 - β_minus ^ 2) * q + β_minus ^ 2 * (q - q_minus)| ≤
      (β ^ 2 - β_minus ^ 2) * q + β_minus ^ 2 * |q - q_minus| := by
    refine (abs_add_le _ _).trans ?_
    have h1 : 0 ≤ (β ^ 2 - β_minus ^ 2) * q := by
      rw [h_diff_sq]
      exact mul_nonneg (div_nonneg (sq_nonneg _) hN_pos.le) hq0
    have h2 : 0 ≤ β_minus ^ 2 := sq_nonneg _
    rw [abs_of_nonneg h1, abs_mul, abs_of_nonneg h2]
  have h_le1 : 2 * |(β ^ 2 - β_minus ^ 2) * q + β_minus ^ 2 * (q - q_minus)| ≤
      2 * ((β ^ 2 / (N : ℝ)) * 1 + β ^ 2 * |q - q_minus|) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 2)
    refine h_tri.trans ?_
    rw [h_diff_sq]
    have hqm_le : β_minus ^ 2 ≤ β ^ 2 := by
      rw [hβm_sq]
      have : 0 ≤ β ^ 2 * (N : ℝ)⁻¹ := mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hN_pos.le)
      linarith
    have hq_le : (β ^ 2 / (N : ℝ)) * q ≤ (β ^ 2 / (N : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hq1 (div_nonneg (sq_nonneg _) hN_pos.le)
    have h_sec : β_minus ^ 2 * |q - q_minus| ≤ β ^ 2 * |q - q_minus| :=
      mul_le_mul_of_nonneg_right hqm_le (abs_nonneg _)
    linarith
  have h_comb : |q - q_minus| ≤ 2 * (β ^ 2 / (N : ℝ)) + 2 * β ^ 2 * |q - q_minus| := by
    have h_mul : 2 * ((β ^ 2 / (N : ℝ)) * 1 + β ^ 2 * |q - q_minus|) =
        2 * (β ^ 2 / (N : ℝ)) + 2 * β ^ 2 * |q - q_minus| := by ring
    linarith [h_bound, h_le1]
  have h_rearr : (1 - 2 * β ^ 2) * |q - q_minus| ≤ 2 * (β ^ 2 / (N : ℝ)) := by
    calc (1 - 2 * β ^ 2) * |q - q_minus| = |q - q_minus| - 2 * β ^ 2 * |q - q_minus| := by ring
      _ ≤ 2 * (β ^ 2 / (N : ℝ)) := by linarith [h_comb]
  have h_denom : 1 / 2 < 1 - 2 * β ^ 2 := by linarith
  have h_denom_pos : 0 < 1 - 2 * β ^ 2 := by linarith
  have h_num : 2 * β ^ 2 < 1 / 2 := by linarith
  have h_ratio : 2 * β ^ 2 / (1 - 2 * β ^ 2) ≤ 1 := by
    rw [div_le_one₀ h_denom_pos]
    linarith
  have h_final : |q - q_minus| ≤ (2 * β ^ 2 / (1 - 2 * β ^ 2)) * (1 / (N : ℝ)) := by
    rw [mul_comm] at h_rearr
    have h_div : |q - q_minus| ≤ (2 * (β ^ 2 / (N : ℝ))) / (1 - 2 * β ^ 2) := by
      rwa [le_div_iff₀ h_denom_pos]
    calc |q - q_minus| ≤ (2 * (β ^ 2 / (N : ℝ))) / (1 - 2 * β ^ 2) := h_div
      _ = (2 * β ^ 2 / (1 - 2 * β ^ 2)) * (1 / (N : ℝ)) := by ring
  calc |q - q_minus| ≤ (2 * β ^ 2 / (1 - 2 * β ^ 2)) * (1 / (N : ℝ)) := h_final
    _ ≤ 1 * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right h_ratio (by positivity)
    _ = 1 / (N : ℝ) := one_mul _

end Stability

end SpinGlasses
