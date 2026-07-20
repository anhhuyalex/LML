import LeanMachineLearning.Optimization.NTK.Kernel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open Real MeasureTheory ProbabilityTheory NNReal Filter

namespace NTK

structure BetaSmooth (σ : ℝ → ℝ) (β : ℝ) : Prop where
  differentiable : Differentiable ℝ σ
  differentiable' : Differentiable ℝ (deriv σ)
  hessian_bound   : ∀ z : ℝ, |deriv (deriv σ) z| ≤ β

lemma BetaSmooth.taylor_bound
    {σ : ℝ → ℝ} {β : ℝ} (hσ : BetaSmooth σ β) (r s : ℝ) :
    |σ r - σ s - deriv σ s * (r - s)| ≤ β * (r - s) ^ 2 / 2 := by
  have hr : r = s ∨ r ≠ s := eq_or_ne r s
  rcases hr with rfl | hr_ne
  · simp
  let C := (σ r - σ s - deriv σ s * (r - s)) / (r - s)^2
  let g := fun t => σ t - σ s - deriv σ s * (t - s) - C * (t - s)^2
  have hg_s : g s = 0 := by simp [g]
  have hg_r : g r = 0 := by
    dsimp [g, C]
    have : (r - s) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hr_ne)
    apply sub_eq_zero.mpr
    exact (div_mul_cancel₀ _ this).symm
  have hσ_cont : Continuous σ := hσ.differentiable.continuous
  have h_cont : ContinuousOn g (Set.uIcc s r) := by
    apply Continuous.continuousOn
    dsimp [g]
    fun_prop
  have h_diff : ∀ x ∈ Set.uIoo s r, HasDerivAt g (deriv σ x - deriv σ s - 2 * C * (x - s)) x := by
    intro x _hx
    dsimp [g]
    have h1 : HasDerivAt (fun t => σ t) (deriv σ x) x := (hσ.differentiable x).hasDerivAt
    have h2 : HasDerivAt (fun t => σ s) 0 x := hasDerivAt_const x (σ s)
    have h3 : HasDerivAt (fun t => t - s) 1 x := by
      have : HasDerivAt (fun t => t) 1 x := hasDerivAt_id x
      exact this.sub_const s
    have h4 : HasDerivAt (fun t => deriv σ s * (t - s)) (deriv σ s * 1) x := h3.const_mul (deriv σ s)
    have h5 : HasDerivAt (fun t => (t - s)^2) (2 * (x - s)^1 * 1) x := h3.pow 2
    have h6 : HasDerivAt (fun t => C * (t - s)^2) (C * (2 * (x - s)^1 * 1)) x := h5.const_mul C
    have h_total := ((h1.sub h2).sub h4).sub h6
    have h_simp : deriv σ x - 0 - deriv σ s * 1 - C * (2 * (x - s)^1 * 1) = deriv σ x - deriv σ s - 2 * C * (x - s) := by ring
    rw [h_simp] at h_total
    exact h_total
  have h_min_lt_max : min s r < max s r := by
    rcases lt_trichotomy s r with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · exfalso; apply hr_ne; exact h.symm
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have h_mean_value : ∃ c ∈ Set.Ioo (min s r) (max s r),
      deriv σ c - deriv σ s - 2 * C * (c - s) =
        (g (max s r) - g (min s r)) / (max s r - min s r) := by
    apply exists_hasDerivAt_eq_slope g _ h_min_lt_max h_cont h_diff
  rcases h_mean_value with ⟨c, hc, hc_eq⟩
  have hg_eval : g (max s r) - g (min s r) = 0 := by
    have h1 : g (max s r) = 0 := by
      rcases max_choice s r with h | h <;> rw [h]
      · exact hg_s
      · exact hg_r
    have h2 : g (min s r) = 0 := by
      rcases min_choice s r with h | h <;> rw [h]
      · exact hg_s
      · exact hg_r
    rw [h1, h2, sub_zero]
  rw [hg_eval, zero_div] at hc_eq
  have hc_simp : deriv σ c - deriv σ s = 2 * C * (c - s) := sub_eq_zero.mp hc_eq
  have h_c_ne_s : c ≠ s := by
    rintro rfl
    have h_in : s ∈ Set.Ioo (min s r) (max s r) := hc
    rcases le_total r s with hrs | hsr
    · rw [max_eq_left hrs] at h_in
      exact lt_irrefl _ h_in.2
    · rw [min_eq_left hsr] at h_in
      exact lt_irrefl _ h_in.1
  have h_min_c : min s c < max s c := by
    rcases lt_trichotomy s c with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · exfalso; apply h_c_ne_s; exact h.symm
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have h_mean_value2 : ∃ ξ ∈ Set.Ioo (min s c) (max s c),
      deriv (deriv σ) ξ = (deriv σ (max s c) - deriv σ (min s c)) / (max s c - min s c) := by
    apply exists_hasDerivAt_eq_slope (deriv σ) _ h_min_c
    · apply Continuous.continuousOn
      exact hσ.differentiable'.continuous
    · intro x _hx
      exact (hσ.differentiable' x).hasDerivAt
  rcases h_mean_value2 with ⟨ξ, _hξ, hξ_eq⟩
  have h_deriv_diff : deriv σ (max s c) - deriv σ (min s c) = 2 * C * (max s c - min s c) := by
    rcases le_total s c with hsc | hcs
    · rw [max_eq_right hsc, min_eq_left hsc]
      exact hc_simp
    · rw [max_eq_left hcs, min_eq_right hcs]
      linarith [hc_simp]
  rw [h_deriv_diff] at hξ_eq
  have h_C_eq : C = deriv (deriv σ) ξ / 2 := by
    have h_denom : max s c - min s c ≠ 0 := sub_ne_zero.mpr h_min_c.ne'
    rw [mul_div_cancel_right₀ _ h_denom] at hξ_eq
    linarith [hξ_eq]
  dsimp [C] at h_C_eq
  have h_final : σ r - σ s - deriv σ s * (r - s) = deriv (deriv σ) ξ / 2 * (r - s) ^ 2 := by
    have h_r_s : (r - s)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hr_ne)
    rw [← h_C_eq]
    exact div_mul_cancel₀ _ h_r_s
  have h_abs_bound : |deriv (deriv σ) ξ / 2 * (r - s) ^ 2| = |deriv (deriv σ) ξ| / 2 * (r - s) ^ 2 := by
    rw [abs_mul, abs_div, abs_two]
    have h_sq : 0 ≤ (r - s) ^ 2 := sq_nonneg (r - s)
    rw [abs_of_nonneg h_sq]
  rw [h_final, h_abs_bound]
  have h_bound := hσ.hessian_bound ξ
  have h_sq : 0 ≤ (r - s) ^ 2 := sq_nonneg (r - s)
  nlinarith

theorem smoothLinearizationBound
    {d m : ℕ} {σ : ℝ → ℝ} {β : ℝ}
    (hσ : BetaSmooth σ β)
    (net : ShallowNetwork σ d m)
    (x : Fin d → ℝ)
    (hx : x ⊙ x ≤ 1)
    (W V : Fin m → Fin d → ℝ) :
    |net.eval x W - linearization (σ := σ) (σ' := deriv σ) net.outerCoeffs x V W|
    ≤ β / (2 * Real.sqrt m) * frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
  dsimp [ShallowNetwork.eval, linearization]
  -- Pull out the 1/√m factor
  have h_pull :
    (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * σ (∑ k : Fin d, W j k * x k) -
    ((m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * σ (∑ k : Fin d, V j k * x k) +
     (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k) =
    (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k) := by
    rw [← mul_add]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_pull]
  have h_abs : |(m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| =
    (m : ℝ)⁻¹.sqrt * |∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h_abs]
  have h_sum_le : |∑ j : Fin m, net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| ≤
    ∑ j : Fin m, |net.outerCoeffs j * (
      σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) -
      deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_bound : ∀ j : Fin m,
    |net.outerCoeffs j * (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) - deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)|
    ≤ β / 2 * (∑ k, (W j k - V j k) * x k)^2 := by
    intro j
    rw [abs_mul]
    have h_taylor := hσ.taylor_bound (∑ k, W j k * x k) (∑ k, V j k * x k)
    have h_sub : ∑ k, W j k * x k - ∑ k, V j k * x k = ∑ k, (W j k - V j k) * x k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_sub] at h_taylor
    have h_rewrite : β * (∑ k : Fin d, (W j k - V j k) * x k) ^ 2 / 2 = β / 2 * (∑ k : Fin d, (W j k - V j k) * x k) ^ 2 := by ring
    rw [h_rewrite] at h_taylor
    have h1 := net.outerCoeffs_bound j
    nlinarith [abs_nonneg (σ (∑ k : Fin d, W j k * x k) - σ (∑ k : Fin d, V j k * x k) - deriv σ (∑ k : Fin d, V j k * x k) * ∑ k : Fin d, (W j k - V j k) * x k)]
  have h_sum_bound : ∑ j : Fin m, |net.outerCoeffs j * (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) - deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)|
    ≤ ∑ j : Fin m, (β / 2 * (∑ k, (W j k - V j k) * x k)^2) := Finset.sum_le_sum fun j _ => h_bound j
  have h_factor : ∑ j : Fin m, (β / 2 * (∑ k, (W j k - V j k) * x k)^2)
    = β / 2 * ∑ j : Fin m, (∑ k, (W j k - V j k) * x k)^2 := by rw [← Finset.mul_sum]
  have h_cs : ∀ j : Fin m, (∑ k : Fin d, (W j k - V j k) * x k)^2 ≤
    (∑ k : Fin d, (W j k - V j k)^2) * (∑ k : Fin d, (x k)^2) := by
    intro j
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => W j k - V j k) x
  have h_cs_sum : ∑ j : Fin m, (∑ k, (W j k - V j k) * x k)^2 ≤
    ∑ j : Fin m, ((∑ k, (W j k - V j k)^2) * (∑ k, (x k)^2)) := Finset.sum_le_sum fun j _ => h_cs j
  have h_x_bound : ∑ k : Fin d, (x k)^2 = x ⊙ x := (innerProduct_self_eq_sum_sq x).symm
  have h_frob : ∑ j : Fin m, (∑ k, (W j k - V j k)^2) * (x ⊙ x)
    = (∑ j : Fin m, ∑ k, (W j k - V j k)^2) * (x ⊙ x) := by rw [← Finset.sum_mul]
  have h_frob_def : ∑ j : Fin m, ∑ k, (W j k - V j k)^2 = frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
    dsimp [frobeniusNorm]
    have h_nonneg : 0 ≤ ∑ i : Fin m, ∑ j : Fin d, (W i j - V i j) ^ 2 := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact sq_nonneg _
    rw [Real.sq_sqrt h_nonneg]
  have h_m_pos : 0 ≤ (m : ℝ)⁻¹.sqrt := Real.sqrt_nonneg _
  have h_final : (m : ℝ)⁻¹.sqrt * |∑ j : Fin m, net.outerCoeffs j * (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) - deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)|
    ≤ β / (2 * Real.sqrt m) * frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
    calc
      (m : ℝ)⁻¹.sqrt * |∑ j : Fin m, net.outerCoeffs j * (σ (∑ k, W j k * x k) - σ (∑ k, V j k * x k) - deriv σ (∑ k, V j k * x k) * ∑ k, (W j k - V j k) * x k)|
        ≤ (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, (β / 2 * (∑ k, (W j k - V j k) * x k)^2) := mul_le_mul_of_nonneg_left (h_sum_le.trans h_sum_bound) h_m_pos
      _ = (m : ℝ)⁻¹.sqrt * (β / 2 * ∑ j : Fin m, (∑ k, (W j k - V j k) * x k)^2) := by rw [h_factor]
      _ ≤ (m : ℝ)⁻¹.sqrt * (β / 2 * ∑ j : Fin m, ((∑ k, (W j k - V j k)^2) * (∑ k, (x k)^2))) := by
        apply mul_le_mul_of_nonneg_left
        apply mul_le_mul_of_nonneg_left h_cs_sum
        · have h_beta : 0 ≤ β := by
            -- wait, beta >= 0 since it bounds absolute value, we can just assume it or use nlinarith
            -- actually we can just apply hσ.hessian_bound to see β >= 0.
            have : 0 ≤ |deriv (deriv σ) 0| := abs_nonneg _
            exact this.trans (hσ.hessian_bound 0)
          exact div_nonneg h_beta zero_le_two
        · exact h_m_pos
      _ = (m : ℝ)⁻¹.sqrt * (β / 2 * ((frobeniusNorm (fun i j => W i j - V i j) ^ 2) * (x ⊙ x))) := by
        congr 2
        rw [h_x_bound, h_frob, h_frob_def]
      _ ≤ (m : ℝ)⁻¹.sqrt * (β / 2 * ((frobeniusNorm (fun i j => W i j - V i j) ^ 2) * 1)) := by
        apply mul_le_mul_of_nonneg_left
        apply mul_le_mul_of_nonneg_left
        apply mul_le_mul_of_nonneg_left hx
        · have h_frob_nonneg : 0 ≤ frobeniusNorm (fun i j => W i j - V i j) ^ 2 := sq_nonneg _
          exact h_frob_nonneg
        · have h_beta : 0 ≤ β := (abs_nonneg _).trans (hσ.hessian_bound 0)
          exact div_nonneg h_beta zero_le_two
        · exact h_m_pos
      _ = β / (2 * Real.sqrt m) * frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
        rw [Real.sqrt_inv]
        ring
  exact h_final
end NTK
