/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IntervalDerivative
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.LogSmoothing

/-!
# The Shcherbina--Tirozzi model: a priori bounds on the replica-symmetric equations

For a concave potential `u ≤ 0` which vanishes on `[τ, ∞)`, every solution `0 ≤ q < ρ` of the
replica-symmetric equations (3.69), (3.76), (3.77) satisfies `q, ρ, (ρ - q)⁻¹ ≤ C`, with `C`
depending only on `κ₀, κ₁, α₀ < 2, h₀, τ` and not on `u` (Talagrand, *Spin Glasses*, Vol. I,
Proposition 3.3.3). Here `r = Ψ(q, ρ)` and `r̄ = Ψ̄(q, ρ)` are written out with
`θ = √q z + √(ρ - q) ξ`.

The printed statement assumes only `κ ≥ κ₀`. The upper bound `κ ≤ κ₁` is necessary: for `u = 0`
one has `r = r̄ = 0` and `(ρ - q)⁻¹ = 2 κ`.

## Main declarations

* `SpinGlasses.exists_bound_of_shcherbinaTirozzi_replicaSymmetric_equations`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace SpinGlasses

/-- The estimate behind (3.146): let `V ≥ 0` be bounded with `V' = W - V²`, where `W` is bounded
and measurable, and let `r = α 𝔼 V (√q z)²`, `r̄ = α 𝔼 W (√q z)`. If `r s² ≤ q` then
`r - r̄ ≤ √(α / 2) / s`. -/
private theorem sub_le_sqrt_div_two_mul_inv {V W : ℝ → ℝ} {D B α q s r rBar : ℝ}
    (hV0 : ∀ y, 0 ≤ V y) (hVD : ∀ y, |V y| ≤ D) (hWm : Measurable W) (hWB : ∀ y, |W y| ≤ B)
    (hVd : ∀ y, HasDerivAt V (W y - V y ^ 2) y) (hα : 0 ≤ α) (hq : 0 ≤ q) (hs : 0 < s)
    (hr : r = α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1))
    (hrBar : rBar = α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1))
    (hrq : r * s ^ 2 ≤ q) : r - rBar ≤ Real.sqrt (α / 2) * s⁻¹ := by
  rcases hα.eq_or_lt with rfl | hαpos
  · simp [hr, hrBar]
  have hr0 : 0 ≤ r := hr ▸ mul_nonneg hα (integral_nonneg fun _ => sq_nonneg _)
  rcases hq.eq_or_lt with rfl | hqpos
  · -- `q = 0`: `V` is minimal at `0`, so `W 0 = V' 0 = 0`
    have hr00 : r = 0 := le_antisymm (nonpos_of_mul_nonpos_left hrq (pow_pos hs 2)) hr0
    have hV00 : V 0 = 0 := by
      rw [hr00] at hr
      simp only [Real.sqrt_zero, zero_mul, integral_const, probReal_univ, one_smul] at hr
      exact (pow_eq_zero_iff two_ne_zero).1 ((mul_eq_zero.1 hr.symm).resolve_left hαpos.ne')
    have hW0 : W 0 = 0 := by
      have hle : ∀ y, V 0 ≤ V y := fun y => hV00.trans_le (hV0 y)
      have hmin : IsLocalMin V 0 := Filter.Eventually.of_forall hle
      simpa [hV00] using hmin.hasDerivAt_eq_zero (hVd 0)
    have hrB0 : rBar = 0 := by simp [hrBar, hW0]
    rw [hr00, hrB0, sub_zero]
    positivity
  -- `q > 0`: integrate by parts in `z`
  set γ := gaussianReal 0 1 with hγ
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hVm : Measurable V :=
    (continuous_iff_continuousAt.2 fun y => (hVd y).continuousAt).measurable
  have hshift : Measurable fun z : ℝ => Real.sqrt q * z := by fun_prop
  set U : ℝ → ℝ := fun z => V (Real.sqrt q * z) with hU
  have hUm : Measurable U := hVm.comp hshift
  have hUd : ∀ z, HasDerivAt U
      (Real.sqrt q * (W (Real.sqrt q * z) - U z ^ 2)) z := fun z => by
    have h1 : HasDerivAt (fun z => Real.sqrt q * z) (Real.sqrt q) z := by
      simpa using (hasDerivAt_id z).const_mul (Real.sqrt q)
    exact ((hVd (Real.sqrt q * z)).comp z h1).congr_deriv (mul_comm _ _)
  have hUb : ∀ z, ‖U z‖ ≤ D := fun z => (Real.norm_eq_abs _).trans_le (hVD _)
  have hUL : MemLp U 2 γ := MemLp.of_bound hUm.aestronglyMeasurable D (ae_of_all _ hUb)
  have hUi : Integrable U γ := hUL.integrable one_le_two
  have hL2 : MemLp (id : ℝ → ℝ) 2 γ := memLp_id_gaussianReal' 2 (by simp)
  have hzU : Integrable (fun z => z * U z) γ := hL2.integrable_mul hUL
  have hWi : Integrable (fun z => W (Real.sqrt q * z)) γ :=
    Integrable.of_bound (hWm.comp hshift).aestronglyMeasurable B
      (ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hWB _))
  have hU2i : Integrable (fun z => U z ^ 2) γ := hUL.integrable_sq
  have hstein : ∫ z, z * U z ∂γ =
      Real.sqrt q * ∫ z, (W (Real.sqrt q * z) - U z ^ 2) ∂γ := by
    have hdi : Integrable (fun z => W (Real.sqrt q * z) - U z ^ 2) γ := hWi.sub hU2i
    rw [integral_id_mul_gaussianReal_eq 1 hUd hzU (hdi.const_mul _), NNReal.coe_one,
      one_mul, integral_const_mul]
  set I := ∫ z, U z ^ 2 ∂γ with hI
  have hrI : r = α * I := hr
  have hdiff : r - rBar = α / Real.sqrt q * -(∫ z, z * U z ∂γ) := by
    rw [hstein, integral_sub hWi hU2i, hrI, hrBar]
    field_simp
    ring
  have hneg : -(∫ z, z * U z ∂γ) ≤ Real.sqrt (I / 2) := by
    refine (neg_integral_id_mul_le_sqrt hL2 hUL fun z => hV0 _).trans_eq ?_
    rw [integral_min_zero_sq_gaussianReal, one_div_mul_eq_div]
  refine hdiff.trans_le ((mul_le_mul_of_nonneg_left hneg
    (div_nonneg hα hsq0.le)).trans ?_)
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), inv_pow,
    show α ^ 2 / q * (I / 2) = α / 2 * (α * I / q) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ hqpos, inv_mul_eq_div, le_div_iff₀ (pow_pos hs 2), ← hrI]
  exact hrq

/-- The estimate behind (3.147): if `(c V y)² ≤ (max ((τ - y) / c) 0)² + L`,
`r = α 𝔼 V (√q z)²` and `𝔼 (min (z - τ / √q) 0)² ≤ a`, then `r (c²)² ≤ α (q a + L c²)`. -/
private theorem mul_sq_le_of_sq_mul_le {V : ℝ → ℝ} {α q c r τ L a : ℝ} (hα : 0 ≤ α)
    (hq : 0 < q) (hc : 0 < c)
    (hV : ∀ y, (c * V y) ^ 2 ≤ max ((τ - y) / c) 0 ^ 2 + L)
    (hr : r = α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1))
    (hmin : ∫ z, min (z - τ / Real.sqrt q) 0 ^ 2 ∂(gaussianReal 0 1) ≤ a) :
    r * (c ^ 2) ^ 2 ≤ α * (q * a + L * c ^ 2) := by
  set γ := gaussianReal 0 1 with hγ
  set b : ℝ := τ / Real.sqrt q with hb
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hpt : ∀ z, (c ^ 2) ^ 2 * V (Real.sqrt q * z) ^ 2 ≤
      q * min (z - b) 0 ^ 2 + L * c ^ 2 := fun z => by
    have h1 : (τ - Real.sqrt q * z) / c = Real.sqrt q / c * (b - z) := by
      rw [hb]
      field_simp
    have h2 : max (b - z) 0 = -min (z - b) 0 := by
      rw [← max_neg_neg, neg_sub, neg_zero]
    have h3 : max ((τ - Real.sqrt q * z) / c) 0 ^ 2 = q / c ^ 2 * min (z - b) 0 ^ 2 := by
      have h4 : max (Real.sqrt q / c * (b - z)) 0 = Real.sqrt q / c * max (b - z) 0 := by
        rw [mul_max_of_nonneg _ _ (div_nonneg hsq0.le hc.le), mul_zero]
      rw [h1, h4, h2, mul_pow, div_pow, Real.sq_sqrt hq.le, neg_sq]
    calc (c ^ 2) ^ 2 * V (Real.sqrt q * z) ^ 2
        = c ^ 2 * (c * V (Real.sqrt q * z)) ^ 2 := by ring
      _ ≤ c ^ 2 * (q / c ^ 2 * min (z - b) 0 ^ 2 + L) :=
          mul_le_mul_of_nonneg_left (h3 ▸ hV _) (sq_nonneg _)
      _ = q * min (z - b) 0 ^ 2 + L * c ^ 2 := by
          field_simp
  have hmini : Integrable (fun z => min (z - b) 0 ^ 2) γ := by
    have hL2 : MemLp (id : ℝ → ℝ) 2 γ := memLp_id_gaussianReal' 2 (by simp)
    refine ((hL2.sub (memLp_const b)).integrable_sq).mono'
      (by fun_prop : Measurable fun z : ℝ => min (z - b) 0 ^ 2).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_pow, Real.norm_eq_abs, Pi.sub_apply, id_eq, ← sq_abs (z - b)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rcases le_total (z - b) 0 with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, abs_zero]; exact abs_nonneg _
  have hdom : Integrable (fun z => q * min (z - b) 0 ^ 2 + L * c ^ 2) γ :=
    (hmini.const_mul _).add (integrable_const _)
  have hint : (c ^ 2) ^ 2 * ∫ z, V (Real.sqrt q * z) ^ 2 ∂γ ≤ q * a + L * c ^ 2 := by
    rw [← integral_const_mul]
    refine (integral_mono_of_nonneg
      (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hdom
      (ae_of_all _ hpt)).trans ?_
    rw [integral_add (hmini.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    exact add_le_add (mul_le_mul_of_nonneg_left hmin hq.le) le_rfl
  rw [hr, mul_assoc, mul_comm (∫ z, V (Real.sqrt q * z) ^ 2 ∂γ)]
  exact mul_le_mul_of_nonneg_left hint hα

/-- For `α₁ ∈ (0, 2)` there are a slope `a < 1 / α₁` and a neighbourhood of `0` on which
`𝔼 (min (z - b) 0)² < a`: the choice of constants behind (3.147). -/
private theorem exists_slope_lt_inv_and_threshold {α₁ : ℝ} (hα₁0 : 0 < α₁) (hα₁2 : α₁ < 2) :
    ∃ a δ : ℝ, 0 < a ∧ a * α₁ < 1 ∧ 0 < δ ∧
      ∀ b, |b| < δ → ∫ z, min (z - b) 0 ^ 2 ∂(gaussianReal 0 1) < a := by
  set a : ℝ := (1 / 2 + α₁⁻¹) / 2 with ha
  have hinv : 1 / 2 < α₁⁻¹ := by
    rw [one_div]
    exact inv_strictAnti₀ hα₁0 hα₁2
  have haα : a * α₁ < 1 := by
    have : a < α₁⁻¹ := by rw [ha]; linarith
    calc a * α₁ < α₁⁻¹ * α₁ := mul_lt_mul_of_pos_right this hα₁0
      _ = 1 := inv_mul_cancel₀ hα₁0.ne'
  have hc := (continuous_integral_min_sub_zero_sq (μ := gaussianReal 0 1)
    (memLp_id_gaussianReal' 2 (by simp))).continuousAt (x := 0)
  have h0 : ∫ z, min (z - 0) 0 ^ 2 ∂(gaussianReal 0 1) < a := by
    simp only [sub_zero, integral_min_zero_sq_gaussianReal]
    rw [ha]; linarith
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 (hc.eventually_lt_const h0)
  exact ⟨a, δ, by rw [ha]; linarith [inv_pos.2 hα₁0], haα, hδ0,
    fun b hb => hδ (by rwa [Real.dist_eq, sub_zero])⟩

/-- The bound (3.147) on `q`: from `q = (r + h²) s²`, `r = α 𝔼 V (√q z)²`, the estimate of
Lemma 3.3.8 on `V` with `c² = s ≤ (2 κ₀)⁻¹`, and the constants of
`exists_slope_lt_inv_and_threshold`. -/
private theorem q_le_of_replicaSymmetric_equation {V : ℝ → ℝ}
    {α α₁ a δ τ L c s q r h h₀ κ₀ : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ α₁) (hα₁0 : 0 < α₁) (ha0 : 0 ≤ a)
    (haα : a * α₁ < 1) (hδ0 : 0 < δ)
    (hδ : ∀ b, |b| < δ → ∫ z, min (z - b) 0 ^ 2 ∂(gaussianReal 0 1) < a) (hτ : 0 ≤ τ)
    (hL0 : 0 ≤ L) (hc0 : 0 < c) (hc2 : c ^ 2 = s) (hs0 : 0 < s) (hsκ : s ≤ (2 * κ₀)⁻¹)
    (hh : |h| ≤ h₀) (hq : 0 ≤ q) (hqs : q = (r + h ^ 2) * s ^ 2)
    (hV : ∀ y, (c * V y) ^ 2 ≤ max ((τ - y) / c) 0 ^ 2 + L)
    (hr : r = α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)) :
    q ≤ max ((τ / δ) ^ 2 + 1)
      ((h₀ ^ 2 / (2 * κ₀) ^ 2 + α₁ * L / (2 * κ₀)) / (1 - a * α₁)) := by
  by_contra hcon
  push Not at hcon
  have hqτ : (τ / δ) ^ 2 + 1 < q := (le_max_left _ _).trans_lt hcon
  have hqpos : 0 < q := lt_of_le_of_lt (by positivity) hqτ
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hbδ : |τ / Real.sqrt q| < δ := by
    rw [abs_of_nonneg (div_nonneg hτ hsq0.le), div_lt_iff₀ hsq0]
    have h1 : τ / δ < Real.sqrt q := by
      rw [Real.lt_sqrt (div_nonneg hτ hδ0.le)]
      linarith
    rw [div_lt_iff₀ hδ0] at h1
    linarith
  have hrs := mul_sq_le_of_sq_mul_le hα0 hqpos hc0 hV hr (hδ _ hbδ).le
  rw [hc2] at hrs
  have hhs : h ^ 2 * s ^ 2 ≤ h₀ ^ 2 / (2 * κ₀) ^ 2 := by
    have h1 : h ^ 2 ≤ h₀ ^ 2 := by
      rw [← sq_abs h]
      exact pow_le_pow_left₀ (abs_nonneg _) hh 2
    have h2 := pow_le_pow_left₀ hs0.le hsκ 2
    rw [inv_pow] at h2
    rw [div_eq_mul_inv]
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
  have hLs : α * (L * s) ≤ α₁ * L / (2 * κ₀) := by
    rw [div_eq_mul_inv, mul_assoc α₁]
    exact mul_le_mul hα (mul_le_mul_of_nonneg_left hsκ hL0) (mul_nonneg hL0 hs0.le) hα₁0.le
  have haq : α * (q * a) ≤ a * α₁ * q := by
    refine (mul_le_mul_of_nonneg_right hα (mul_nonneg hq ha0)).trans_eq ?_
    ring
  have hfin : (1 - a * α₁) * q ≤ h₀ ^ 2 / (2 * κ₀) ^ 2 + α₁ * L / (2 * κ₀) := by
    have h1 : q = r * s ^ 2 + h ^ 2 * s ^ 2 := by rw [← add_mul]; exact hqs
    rw [mul_add] at hrs
    linarith
  have h1 : q ≤ (h₀ ^ 2 / (2 * κ₀) ^ 2 + α₁ * L / (2 * κ₀)) / (1 - a * α₁) := by
    rw [le_div_iff₀ (sub_pos.2 haα), mul_comm]
    exact hfin
  exact (h1.trans (le_max_right _ _)).not_gt hcon

/-- **Proposition 3.3.3:** every solution of the replica-symmetric equations satisfies
`0 ≤ q < ρ`, `q ≤ C` and `ρ ≤ C`, and `(ρ - q)⁻¹ ≤ C` under the necessary upper bound
`κ ≤ κ₁`,
uniformly over the concave potentials `u ≤ 0` vanishing on `[τ, ∞)`. The inequalities
`0 ≤ q < ρ` follow from the equations and need not be assumed. -/
theorem exists_bound_of_shcherbinaTirozzi_replicaSymmetric_equations (κ₀ κ₁ α₀ h₀ τ : ℝ)
    (hκ₀ : 0 < κ₀) (hα₀ : α₀ < 2) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, ∀ (α κ h q ρ r rBar : ℝ) (u : ℝ → ℝ) (D D₂ : ℝ), 0 ≤ α → α ≤ α₀ → κ₀ ≤ κ →
      |h| ≤ h₀ → ConcaveOn ℝ univ u → (∀ x, u x ≤ 0) →
      (∀ x, τ ≤ x → u x = 0) → Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D₂) →
      let Z : ℝ → ℝ := fun y =>
        ∫ ξ, Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y => (∫ ξ, deriv u (y + Real.sqrt (ρ - q) * ξ) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ - q) * ξ) +
          deriv u (y + Real.sqrt (ρ - q) * ξ) ^ 2) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      r = α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1) →
      rBar = α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1) →
      ρ = (2 * κ + r - rBar)⁻¹ + (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 →
      q = (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 →
      0 ≤ q ∧ q < ρ ∧ q ≤ C ∧ ρ ≤ C ∧ (κ ≤ κ₁ → (ρ - q)⁻¹ ≤ C) := by
  obtain ⟨L, hL0, h338⟩ := exists_sq_mul_integral_deriv_mul_exp_div_le
  -- a slope strictly between `1/2` and `1/α₁`, and the corresponding threshold of Lemma 3.3.9
  set α₁ : ℝ := max α₀ 1 with hα₁
  have hα₁2 : α₁ < 2 := max_lt hα₀ one_lt_two
  have hα₁0 : 0 < α₁ := one_pos.trans_le (le_max_right _ _)
  obtain ⟨a, δ, ha0, haα, hδ0, hδ⟩ := exists_slope_lt_inv_and_threshold hα₁0 hα₁2
  set Q : ℝ := max ((τ / δ) ^ 2 + 1)
    ((h₀ ^ 2 / (2 * κ₀) ^ 2 + α₁ * L / (2 * κ₀)) / (1 - a * α₁)) with hQ
  set C₁ : ℝ := 2 * κ₁ / (1 - Real.sqrt (α₁ / 2)) with hC₁
  refine ⟨max (Q + (2 * κ₀)⁻¹) C₁, fun α κ h q ρ r rBar u D D₂ hα0 hα hκ hh huc hu0
    huτ hu1 hu2 hD hD₂ => ?_⟩
  intro Z V W hr hrBar hρ hqe
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hαα₁ : α ≤ α₁ := hα.trans (le_max_left _ _)
  -- `r̄ ≤ r`, so the denominator is at least `2 κ`; the equations then give `0 ≤ q < ρ`
  have hrr : rBar ≤ r := by
    rw [hr, hrBar]
    exact mul_le_mul_of_nonneg_left (integral_deriv_two_add_sq_div_le_integral_sq_div
      (μ := gaussianReal 0 1) huc hu1 hu2 hD hD₂ (a := fun z => Real.sqrt q * z)
      (by fun_prop) (Real.sqrt (ρ - q))) hα0
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact mul_nonneg hα0 (integral_nonneg fun _ => sq_nonneg _)
  set d : ℝ := 2 * κ + r - rBar with hd
  have hd2 : 2 * κ ≤ d := by rw [hd]; linarith
  have hq : 0 ≤ q := by
    rw [hqe]
    exact div_nonneg (add_nonneg hr0 (sq_nonneg h)) (sq_nonneg d)
  have hgap : ρ - q = d⁻¹ := by linarith
  have hqρ : q < ρ := sub_pos.1 (hgap ▸ inv_pos.2 (lt_of_lt_of_le (by linarith) hd2))
  set s : ℝ := ρ - q with hs
  have hs0 : 0 < s := sub_pos.2 hqρ
  set c : ℝ := Real.sqrt s with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hs0
  have hc2 : c ^ 2 = s := Real.sq_sqrt hs0.le
  -- the smoothing of `u`, with `V = (log Z)'` and `V' = W - V²`
  have hum : Measurable u := hu1.continuous.measurable
  have hu'0 : ∀ x, 0 ≤ deriv u x := huc.deriv_nonneg_of_forall_ge_eq hu1 huτ
  have hVd : ∀ y, HasDerivAt V (W y - V y ^ 2) y := fun y =>
    (hasDerivAt_log_integral_exp_comp_add_gaussianReal hu1 hu2 hu0 hD hD₂ c y).2.2
  have hV0 : ∀ y, 0 ≤ V y := fun y => div_nonneg
    (integral_nonneg fun ξ => mul_nonneg (hu'0 _) (Real.exp_pos _).le)
    (integral_nonneg fun _ => (Real.exp_pos _).le)
  have hVD : ∀ y, |V y| ≤ D := fun y => abs_integral_mul_exp_comp_add_div_le hD
    (integrable_exp_comp_add_gaussianReal hum hu0 y c)
  have hWB : ∀ y, |W y| ≤ D₂ + D ^ 2 := fun y =>
    abs_integral_mul_exp_comp_add_div_le
      (f := fun x => deriv (deriv u) x + deriv u x ^ 2)
      (abs_deriv_deriv_add_sq_deriv_le hD hD₂) (integrable_exp_comp_add_gaussianReal hum hu0 y c)
  have hWm : Measurable W := measurable_integral_mul_exp_comp_add_div hum
    (f := fun x => deriv (deriv u) x + deriv u x ^ 2)
    ((measurable_deriv (deriv u)).add ((measurable_deriv u).pow_const 2)) measurable_id c
  have hrV : r = α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1) := hr
  have hrW : rBar = α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1) := hrBar
  have hsd : s = d⁻¹ := hgap
  have hs_inv : s⁻¹ = d := by rw [hsd, inv_inv]
  have hsκ : s ≤ (2 * κ₀)⁻¹ := by
    rw [hsd]
    exact inv_anti₀ (by positivity) ((by linarith : 2 * κ₀ ≤ 2 * κ).trans hd2)
  have hqs : q = (r + h ^ 2) * s ^ 2 := by
    rw [hsd, inv_pow, ← div_eq_mul_inv]; exact hqe
  have hrq : r * s ^ 2 ≤ q := by
    rw [hqs]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg h)) (sq_nonneg s)
  -- first bound: `(ρ - q)⁻¹`
  have hfirst : κ ≤ κ₁ → s⁻¹ ≤ C₁ := fun hκ1 => by
    have hsq2 : Real.sqrt (α₁ / 2) < 1 := by
      rw [Real.sqrt_lt' one_pos, one_pow]; linarith
    have hdiff := sub_le_sqrt_div_two_mul_inv hV0 hVD hWm hWB hVd hα0 hq hs0 hrV hrW hrq
    have h1 : Real.sqrt (α / 2) * s⁻¹ ≤ Real.sqrt (α₁ / 2) * s⁻¹ :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (inv_nonneg.2 hs0.le)
    have h2 : s⁻¹ = 2 * κ + (r - rBar) := by rw [hs_inv, hd]; ring
    rw [hC₁, le_div_iff₀ (sub_pos.2 hsq2), mul_sub, mul_one, mul_comm s⁻¹]
    linarith
  -- second bound: `q`
  have hqQ : q ≤ Q := by
    have humono : Monotone u := monotone_of_deriv_nonneg hu1 hu'0
    refine q_le_of_replicaSymmetric_equation hα0 hαα₁ hα₁0 ha0.le haα hδ0 hδ hτ hL0 hc0 hc2
      hs0 hsκ hh hq hqs (fun y => ?_) hrV
    have := h338 u hu1 humono hu0 τ huτ D hD c hc0 y
    rwa [mul_div_assoc] at this
  have hρq : ρ = q + s := by rw [hs]; ring
  refine ⟨hq, hqρ,
    hqQ.trans ((le_add_of_nonneg_right (by positivity)).trans (le_max_left _ _)), ?_,
    fun hκ1 => (hfirst hκ1).trans (le_max_right _ _)⟩
  rw [hρq]
  exact (add_le_add hqQ hsκ).trans (le_max_left _ _)

end SpinGlasses
