/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKSecondMoment
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh

/-!
# Lipschitz estimates for the Gaussian averages in Hanen's leading term

Step E5 of the proof of the even case of Theorem 1.11.1 (the book's "very simple matter").
The leading term of Proposition 1.11.11 for the reduced system differs from the one for the
full system by `O((N+2)^{-1/2})` in the bracket. The bracket is a Gaussian average of a bounded
Lipschitz function of `r z + h` with `r = β √q`; this module collects the Lipschitz bounds in `r`
and the comparison `|r - rm| ≲ (N+2)^{-1/2}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real
namespace SpinGlasses

/-- The first absolute moment of the standard Gaussian is at most one. -/
theorem integral_abs_gaussianReal_le_one : ∫ z : ℝ, |z| ∂gaussianReal 0 1 ≤ 1 := by
  have hm : MemLp id 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := hm.integrable_sq
  have habs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (hm.integrable (by norm_num)).abs
  have hvar : ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1 = 1 := by
    have h0 : ∫ z : ℝ, id z ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
    have := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := id) aemeasurable_id h0
    rw [variance_id_gaussianReal] at this
    simpa using this.symm
  calc ∫ z : ℝ, |z| ∂gaussianReal 0 1 ≤ ∫ z : ℝ, (1 + z ^ 2) / 2 ∂gaussianReal 0 1 :=
        integral_mono habs ((integrable_const (1 : ℝ)).add hsq |>.div_const 2) fun z => by
          nlinarith [sq_abs z, sq_nonneg (|z| - 1)]
    _ = 1 := by
        rw [integral_div, integral_add (integrable_const _) hsq, hvar]
        simp

/-- **Integral form of a Lipschitz bound.** If `f` is bounded, continuous and `L`-Lipschitz, then
the Gaussian average of `f (r z + h)` is `L`-Lipschitz in `r`. -/
theorem abs_integral_gaussianReal_comp_sub_le (f : ℝ → ℝ) (L B : ℝ) (hL : 0 ≤ L)
    (hcont : Continuous f) (hf : ∀ u v, |f u - f v| ≤ L * |u - v|) (hB : ∀ u, |f u| ≤ B)
    (r r' h : ℝ) :
    |(∫ z : ℝ, f (r * z + h) ∂gaussianReal 0 1) - ∫ z : ℝ, f (r' * z + h) ∂gaussianReal 0 1| ≤
      L * |r - r'| := by
  have hint (c : ℝ) : Integrable (fun z : ℝ => f (c * z + h)) (gaussianReal 0 1) :=
    Integrable.of_bound (hcont.comp (by fun_prop)).aestronglyMeasurable B
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hB _)
  have habs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 2).integrable (by norm_num)).abs
  rw [← integral_sub (hint r) (hint r')]
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ z : ℝ, |f (r * z + h) - f (r' * z + h)| ∂gaussianReal 0 1
      ≤ ∫ z : ℝ, L * |r - r'| * |z| ∂gaussianReal 0 1 := by
        refine integral_mono ((hint r).sub (hint r')).abs (habs.const_mul _) fun z => ?_
        have := hf (r * z + h) (r' * z + h)
        calc _ ≤ L * |r * z + h - (r' * z + h)| := this
          _ = L * |r - r'| * |z| := by
              rw [show r * z + h - (r' * z + h) = (r - r') * z by ring, abs_mul]
              ring
    _ = L * |r - r'| * ∫ z : ℝ, |z| ∂gaussianReal 0 1 := integral_const_mul _ _
    _ ≤ L * |r - r'| * 1 :=
        mul_le_mul_of_nonneg_left integral_abs_gaussianReal_le_one (by positivity)
    _ = _ := mul_one _

/-- `x ↦ x^n` is `n`-Lipschitz on `[0, 1]`. -/
theorem abs_pow_sub_pow_le_of_mem_Icc (n : ℕ) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : |a ^ n - b ^ n| ≤ n * |a - b| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : b ^ n ∈ Set.Icc (0 : ℝ) 1 := ⟨pow_nonneg hb.1 n, pow_le_one₀ hb.1 hb.2⟩
    have h1 : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [h1]
    calc _ ≤ |a * (a ^ n - b ^ n)| + |(a - b) * b ^ n| := abs_add_le _ _
      _ = a * |a ^ n - b ^ n| + |a - b| * b ^ n := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha.1, abs_of_nonneg hbn.1]
      _ ≤ 1 * (n * |a - b|) + |a - b| * 1 := by
          gcongr
          · exact ha.2
          · exact hbn.2
      _ = _ := by push_cast; ring

/-- The hyperbolic secant is 1-Lipschitz. -/
theorem abs_inv_cosh_sub_le (u v : ℝ) : |(Real.cosh u)⁻¹ - (Real.cosh v)⁻¹| ≤ |u - v| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u => (Real.cosh u)⁻¹)
      (-(Real.sinh x) / (Real.cosh x) ^ 2) x := by
    intro x
    exact (Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne'
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (fun u => (Real.cosh u)⁻¹) x‖ ≤ 1 := by
    intro x _
    rw [(hd x).deriv, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ Real.cosh x ^ 2)]
    have hc := Real.one_le_cosh x
    have hs := Real.abs_sinh_le_cosh x
    rw [div_le_one (by positivity)]
    nlinarith
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u => (Real.cosh u)⁻¹)
    (fun x _ => (hd x).differentiableAt) hb convex_univ (Set.mem_univ v) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using this

/-- `u ↦ (cosh u ^ n)⁻¹` is `n`-Lipschitz. -/
theorem abs_inv_cosh_pow_sub_le (n : ℕ) (u v : ℝ) :
    |(Real.cosh u ^ n)⁻¹ - (Real.cosh v ^ n)⁻¹| ≤ n * |u - v| := by
  have hm (x : ℝ) : (Real.cosh x)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, inv_le_one_of_one_le₀ (Real.one_le_cosh x)⟩
  rw [← inv_pow, ← inv_pow]
  exact (abs_pow_sub_pow_le_of_mem_Icc n (hm u) (hm v)).trans
    (mul_le_mul_of_nonneg_left (abs_inv_cosh_sub_le u v) (Nat.cast_nonneg n))

/-- `tanh ^ 4` is 4-Lipschitz. -/
theorem abs_tanh_pow_four_sub_le (u v : ℝ) :
    |Real.tanh u ^ 4 - Real.tanh v ^ 4| ≤ 4 * |u - v| := by
  have ha := Real.abs_tanh_lt_one u
  have hb := Real.abs_tanh_lt_one v
  have h1 : Real.tanh u ^ 4 - Real.tanh v ^ 4 = (Real.tanh u - Real.tanh v) *
      ((Real.tanh u + Real.tanh v) * (Real.tanh u ^ 2 + Real.tanh v ^ 2)) := by ring
  rw [h1, abs_mul]
  have h2 : |(Real.tanh u + Real.tanh v) * (Real.tanh u ^ 2 + Real.tanh v ^ 2)| ≤ 4 := by
    rw [abs_mul]
    have hs : |Real.tanh u + Real.tanh v| ≤ 2 := by
      have := abs_add_le (Real.tanh u) (Real.tanh v); linarith
    have hq : |Real.tanh u ^ 2 + Real.tanh v ^ 2| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [abs_nonneg (Real.tanh u), abs_nonneg (Real.tanh v), sq_abs (Real.tanh u),
        sq_abs (Real.tanh v)]
    nlinarith [abs_nonneg (Real.tanh u + Real.tanh v),
      abs_nonneg (Real.tanh u ^ 2 + Real.tanh v ^ 2)]
  calc _ ≤ |u - v| * 4 := by
        refine mul_le_mul (Real.abs_tanh_sub_tanh_le u v) h2 (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

/-- The Gaussian average of `(cosh (r z + h) ^ (4p))⁻¹` is `4p`-Lipschitz in `r`. -/
theorem abs_integral_inv_cosh_pow_sub_le (p : ℕ) (r r' h : ℝ) :
    |(∫ z : ℝ, (Real.cosh (r * z + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1) -
      ∫ z : ℝ, (Real.cosh (r' * z + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1| ≤
      ((4 * p : ℕ) : ℝ) * |r - r'| :=
  abs_integral_gaussianReal_comp_sub_le (fun u => (Real.cosh u ^ (4 * p))⁻¹) ((4 * p : ℕ) : ℝ) 1
    (Nat.cast_nonneg _) (by fun_prop (disch := intro; positivity))
    (fun u v => abs_inv_cosh_pow_sub_le (4 * p) u v) (fun u => by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (Real.one_le_cosh u))) r r' h

/-- The Gaussian average of `tanh (r z + h) ^ 4` is 4-Lipschitz in `r`. -/
theorem abs_integral_tanh_pow_four_sub_le (r r' h : ℝ) :
    |(∫ z : ℝ, Real.tanh (r * z + h) ^ 4 ∂gaussianReal 0 1) -
      ∫ z : ℝ, Real.tanh (r' * z + h) ^ 4 ∂gaussianReal 0 1| ≤ 4 * |r - r'| :=
  abs_integral_gaussianReal_comp_sub_le (fun u => Real.tanh u ^ 4) 4 1 (by norm_num)
    (by fun_prop) abs_tanh_pow_four_sub_le (fun u => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one u).le) r r' h

/-- `|√a - √b| ≤ √|a - b|` for nonnegative `a`, `b`. -/
theorem abs_sqrt_sub_sqrt_le_sqrt_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith [Real.sqrt_le_sqrt h]), abs_of_nonneg (by linarith)]
    apply Real.le_sqrt_of_sq_le
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have h3 : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt h
    nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg a]
  · rw [abs_of_nonpos (by linarith [Real.sqrt_le_sqrt h]), abs_of_nonpos (by linarith)]
    apply Real.le_sqrt_of_sq_le
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have h3 : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt h
    nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg a]

/-- **Parameter gap.** The effective field strengths `r = β √q` of the full system and
`rm = βm √qm` of the reduced system (`βm = β √((N+1)/(N+2))`, `|q - qm| ≤ 1/(N+2)`) differ by at
most `1/√(N+2)`. -/
theorem hanen_param_gap (β q qm : ℝ) (N : ℕ) (hβ : 4 * β ^ 2 < 1) (hq0 : 0 ≤ q)
    (hqm0 : 0 ≤ qm) (hqm1 : qm ≤ 1) (hqq : |q - qm| ≤ 1 / ((N : ℝ) + 2)) :
    |β * Real.sqrt q - β * Real.sqrt (((N : ℝ) + 1) / ((N : ℝ) + 2)) * Real.sqrt qm| ≤
      1 / Real.sqrt ((N : ℝ) + 2) := by
  set t : ℝ := (N : ℝ) + 2 with ht
  have ht0 : 0 < t := by positivity
  set θ : ℝ := ((N : ℝ) + 1) / t with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : 1 - θ = 1 / t := by rw [hθ, ht]; field_simp; ring
  have hβabs : |β| ≤ 1 / 2 := by
    have : β ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq' this (by norm_num) |>.2 |> fun h => by
      rw [abs_le]; constructor <;> nlinarith [abs_le_of_sq_le_sq' this (by norm_num)]
  have h1 : β * Real.sqrt q - β * Real.sqrt θ * Real.sqrt qm =
      β * (Real.sqrt q - Real.sqrt (θ * qm)) := by
    rw [Real.sqrt_mul hθ0]; ring
  have h2 : |q - θ * qm| ≤ 2 / t := by
    have : q - θ * qm = (q - qm) + (1 - θ) * qm := by ring
    rw [this]
    calc _ ≤ |q - qm| + |(1 - θ) * qm| := abs_add_le _ _
      _ ≤ 1 / t + 1 / t := by
          refine add_le_add hqq ?_
          rw [abs_mul, hθ1, abs_of_nonneg (by positivity), abs_of_nonneg hqm0]
          calc 1 / t * qm ≤ 1 / t * 1 := mul_le_mul_of_nonneg_left hqm1 (by positivity)
            _ = 1 / t := mul_one _
      _ = 2 / t := by ring
  rw [h1, abs_mul]
  have h3 := abs_sqrt_sub_sqrt_le_sqrt_abs_sub hq0 (mul_nonneg hθ0 hqm0)
  have h4 : Real.sqrt |q - θ * qm| ≤ Real.sqrt (2 / t) := Real.sqrt_le_sqrt h2
  have h5 : Real.sqrt (2 / t) ≤ 2 / Real.sqrt t := by
    rw [Real.sqrt_div (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact div_le_div_of_nonneg_right this (Real.sqrt_nonneg _)
  calc |β| * |Real.sqrt q - Real.sqrt (θ * qm)| ≤ (1 / 2) * (2 / Real.sqrt t) :=
        mul_le_mul hβabs (h3.trans (h4.trans h5)) (abs_nonneg _) (by norm_num)
    _ = 1 / Real.sqrt t := by ring

/-- `|x^n - y^n| ≤ n M^(n-1) |x - y|` for `x, y ∈ [0, M]`, stated without a subtraction in the
exponent. -/
theorem mul_abs_pow_sub_pow_le {x y M : ℝ} (hM : 0 < M) (hx : x ∈ Set.Icc (0 : ℝ) M)
    (hy : y ∈ Set.Icc (0 : ℝ) M) (n : ℕ) : M * |x ^ n - y ^ n| ≤ n * M ^ n * |x - y| := by
  have hx' : x / M ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hx.1 hM.le, (div_le_one hM).2 hx.2⟩
  have hy' : y / M ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hy.1 hM.le, (div_le_one hM).2 hy.2⟩
  have h := abs_pow_sub_pow_le_of_mem_Icc n hx' hy'
  rw [div_pow, div_pow, ← sub_div, abs_div, abs_of_pos (pow_pos hM n), div_le_iff₀ (pow_pos hM n),
    ← sub_div, abs_div, abs_of_pos hM] at h
  have h2 : |x ^ n - y ^ n| ≤ n * (|x - y| / M) * M ^ n := h
  calc M * |x ^ n - y ^ n| ≤ M * (n * (|x - y| / M) * M ^ n) :=
        mul_le_mul_of_nonneg_left h2 hM.le
    _ = n * M ^ n * |x - y| := by field_simp

/-- **Gap of the variance parameter.** For `α, αm ∈ [0, 1]` and `0 ≤ bm ≤ b ≤ 1/4`,
`|α/(1 - bα) - αm/(1 - bm αm)| ≤ (16/9) (|α - αm| + |b - bm|)`. -/
theorem abs_div_sub_div_le_of_mem_Icc {α αm b bm : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hαm : αm ∈ Set.Icc (0 : ℝ) 1) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 4) (hbm0 : 0 ≤ bm)
    (hbm : bm ≤ b) :
    |α / (1 - b * α) - αm / (1 - bm * αm)| ≤ 16 / 9 * (|α - αm| + |b - bm|) := by
  have hD : 3 / 4 ≤ 1 - b * α := by nlinarith [hα.1, hα.2]
  have hDm : 3 / 4 ≤ 1 - bm * αm := by nlinarith [hαm.1, hαm.2]
  have hD0 : 0 < 1 - b * α := by linarith
  have hDm0 : 0 < 1 - bm * αm := by linarith
  rw [div_sub_div _ _ hD0.ne' hDm0.ne', abs_div, abs_of_pos (mul_pos hD0 hDm0),
    div_le_iff₀ (mul_pos hD0 hDm0)]
  have hnum : α * (1 - bm * αm) - (1 - b * α) * αm = (α - αm) + α * αm * (b - bm) := by ring
  rw [hnum]
  have h1 : |α * αm * (b - bm)| ≤ |b - bm| := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hα.1 hαm.1)]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (by nlinarith [hα.1, hα.2, hαm.1, hαm.2])
  have h2 : (9 / 16 : ℝ) ≤ (1 - b * α) * (1 - bm * αm) := by nlinarith
  calc |(α - αm) + α * αm * (b - bm)| ≤ |α - αm| + |b - bm| :=
        (abs_add_le _ _).trans (add_le_add le_rfl h1)
    _ ≤ 16 / 9 * (|α - αm| + |b - bm|) * ((1 - b * α) * (1 - bm * αm)) := by
        have := add_nonneg (abs_nonneg (α - αm)) (abs_nonneg (b - bm))
        nlinarith

/-- A Gaussian average of a function bounded by one is bounded by one. -/
theorem abs_integral_gaussianReal_le_one (f : ℝ → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |∫ z : ℝ, f z ∂gaussianReal 0 1| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1) (C := 1)
    (f := f) (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hf z)
  simpa [Real.norm_eq_abs] using this

/-- The reduced-system bracket, rescaled by `θ = (N+1)/(N+2)`, is the full-system bracket with
`A` replaced by `θ A`. Pure algebra, kept apart so that no Gaussian average is unfolded. -/
theorem hanen_lead_bracket_eq (N : ℝ) (hN : 0 < N + 1) (b A : ℝ) :
    ((N + 1) / (N + 2)) * (4 * ((N + 1)⁻¹ + (b * ((N + 1) / (N + 2))) * (A / (N + 1)))) =
      4 * ((N + 2)⁻¹ + b * (((N + 1) / (N + 2)) * A / (N + 2))) := by
  have h2 : N + 2 ≠ 0 := by linarith
  field_simp

/-- **Algebraic core of the leading-term shift.** If the two brackets' parameters `A`, `Am`
(with `θ A_m` against `A`) and the two cosh averages `Jm`, `J` are `ε = 1/√t` close, then the two
leading terms are `O(t^{-(2p+1)/2})` close. All hypotheses are about plain real numbers. -/
theorem hanen_shift_core (p : ℕ) (t θ b A Am Jm J ε : ℝ) (ht : 2 ≤ t) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 4) (hε : ε = 1 / Real.sqrt t)
    (hA : A ∈ Set.Icc (0 : ℝ) (4 / 3)) (hAm : Am ∈ Set.Icc (0 : ℝ) (4 / 3))
    (hδ : |θ * Am - A| ≤ 13 * ε) (hJ1 : |Jm| ≤ 1) (hJ : |Jm - J| ≤ 4 * p * ε) :
    |(4 * (t⁻¹ + b * (θ * Am / t))) ^ p * Jm - (4 * (t⁻¹ + b * (A / t))) ^ p * J| ≤
      (7 * p * 6 ^ p + 1) / t ^ (((2 * p + 1 : ℕ) : ℝ) / 2) := by
  have ht0 : 0 < t := by linarith
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hε0 : 0 < ε := by rw [hε]; positivity
  set a : ℝ := 4 * (t⁻¹ + b * (A / t)) with ha
  set am : ℝ := 4 * (t⁻¹ + b * (θ * Am / t)) with ham
  have ha0 : 0 ≤ a := by rw [ha]; have := hA.1; positivity
  have ham0 : 0 ≤ am := by rw [ham]; have := hAm.1; positivity
  have ha6 : a ≤ 6 / t := by
    have : a = 4 / t * (1 + b * A) := by rw [ha]; ring
    rw [this, div_mul_eq_mul_div, div_le_div_iff_of_pos_right ht0]
    nlinarith [hA.2, hA.1]
  have ham6 : am ≤ 6 / t := by
    have : am = 4 / t * (1 + b * (θ * Am)) := by rw [ham]; ring
    rw [this, div_mul_eq_mul_div, div_le_div_iff_of_pos_right ht0]
    have h1 : θ * Am ≤ 4 / 3 := by nlinarith [hAm.2, hAm.1]
    nlinarith [hAm.1]
  have hdiffa : |am - a| ≤ 13 * ε / t := by
    have e : am - a = 4 * b * (θ * Am - A) / t := by rw [ham, ha]; ring
    rw [e, abs_div, abs_of_pos ht0, abs_mul, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ ht0.le
    calc 4 * b * |θ * Am - A| ≤ 1 * (13 * ε) := by
          apply mul_le_mul (by linarith) hδ (abs_nonneg _) (by norm_num)
      _ = 13 * ε := one_mul _
  set M : ℝ := 6 / t with hM
  have hM0 : 0 < M := by positivity
  have hpow := mul_abs_pow_sub_pow_le hM0 ⟨ham0, ham6⟩ ⟨ha0, ha6⟩ p
  have hsplit : am ^ p * Jm - a ^ p * J = (am ^ p - a ^ p) * Jm + a ^ p * (Jm - J) := by ring
  have hap : a ^ p ≤ M ^ p := pow_le_pow_left₀ ha0 ha6 p
  have hMt : M * t = 6 := by rw [hM]; field_simp
  have hkey : |am ^ p * Jm - a ^ p * J| ≤ 7 * p * M ^ p * ε := by
    rw [hsplit]
    have hd1 : |am ^ p - a ^ p| ≤ p * M ^ p * (13 / 6) * ε := by
      have h1 : M * |am ^ p - a ^ p| ≤ p * M ^ p * (13 * ε / t) :=
        hpow.trans (mul_le_mul_of_nonneg_left hdiffa (by positivity))
      have h2 : p * M ^ p * (13 * ε / t) = M * (p * M ^ p * (13 / 6) * ε) := by
        field_simp
        nlinarith [hMt]
      rw [h2] at h1
      exact le_of_mul_le_mul_left h1 hM0
    have hd2 : |a ^ p * (Jm - J)| ≤ M ^ p * (4 * p * ε) := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 p)]
      exact mul_le_mul hap hJ (abs_nonneg _) (by positivity)
    calc _ ≤ |(am ^ p - a ^ p) * Jm| + |a ^ p * (Jm - J)| := abs_add_le _ _
      _ ≤ p * M ^ p * (13 / 6) * ε + M ^ p * (4 * p * ε) := by
          refine add_le_add ?_ hd2
          rw [abs_mul]
          calc |am ^ p - a ^ p| * |Jm| ≤ |am ^ p - a ^ p| * 1 :=
                mul_le_mul_of_nonneg_left hJ1 (abs_nonneg _)
            _ ≤ _ := by rw [mul_one]; exact hd1
      _ ≤ 7 * p * M ^ p * ε := by
          have : (0 : ℝ) ≤ p * M ^ p * ε := by positivity
          nlinarith
  have hrate : 7 * p * M ^ p * ε = 7 * p * 6 ^ p / t ^ (((2 * p + 1 : ℕ) : ℝ) / 2) := by
    have hsq : t ^ (((2 * p + 1 : ℕ) : ℝ) / 2) = t ^ p * Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add ht0]
      congr 1
      push_cast
      ring
    rw [hsq, hM, hε, div_pow]
    field_simp
  rw [hrate] at hkey
  refine hkey.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- **E5: the leading term of the reduced system is the leading term of the full system, up to
`O((N+2)^{-(2p+1)/2})`** (Talagrand: "a very simple matter"). The reduced system has inverse
temperature `βm = β √((N+1)/(N+2))` and a fixed point `qm` with `|q - qm| ≤ 1/(N+2)`. The bracket
differs by `O((N+2)^{-1/2})` (Lipschitz estimates in `r = β √q`), while its prefactor is
`O((N+2)^{-p})`. -/
theorem sk_hanen_leading_term_shift (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q qm : ℝ) (N : ℕ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      (∫ z : ℝ, Real.tanh ((β * Real.sqrt (((N : ℝ) + 1) / ((N : ℝ) + 2))) * Real.sqrt qm * z
        + h) ^ 2 ∂gaussianReal 0 1 = qm) →
      β ^ 2 ≤ β₀ ^ 2 → |q - qm| ≤ 1 / ((N : ℝ) + 2) →
      let βm := β * Real.sqrt (((N : ℝ) + 1) / ((N : ℝ) + 2))
      let α := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1) - 2 * q + 1
      let A := α / (1 - β ^ 2 * α)
      let αm := (∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 4 ∂gaussianReal 0 1) -
        2 * qm + 1
      let Am := αm / (1 - βm ^ 2 * αm)
      |(((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ p *
          (4 * (((N : ℝ) + 1)⁻¹ + βm ^ 2 * (Am / ((N : ℝ) + 1)))) ^ p *
          (∫ z : ℝ, (Real.cosh (βm * z * Real.sqrt qm + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1) -
        (4 * (((N : ℝ) + 2)⁻¹ + β ^ 2 * (A / ((N : ℝ) + 2)))) ^ p *
          (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1)| ≤
        K / ((N : ℝ) + 2) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) := by
  refine ⟨7 * p * 6 ^ p + 1, by positivity, ?_⟩
  intro β h q qm N hfix hfixm hβ hqq βm α A αm Am
  set t : ℝ := (N : ℝ) + 2 with ht
  have ht2 : 2 ≤ t := by rw [ht]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have ht0 : 0 < t := by linarith
  set θ : ℝ := ((N : ℝ) + 1) / t with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : 1 - θ = 1 / t := by rw [hθ, ht]; field_simp; ring
  have hθle : θ ≤ 1 := by rw [← sub_nonneg, hθ1]; positivity
  have hβ4 : 4 * β ^ 2 < 1 := lt_of_le_of_lt (by nlinarith) hβ₀
  have hβ2 : β ^ 2 ≤ 1 / 4 := by linarith
  have hq := fixedPoint_mem_Icc hfix
  have hqm := fixedPoint_mem_Icc hfixm
  have hβmsq : βm ^ 2 = β ^ 2 * θ := by
    rw [show βm = β * Real.sqrt θ from rfl, mul_pow, Real.sq_sqrt hθ0]
  -- the parameter gap
  have hgap : |β * Real.sqrt q - βm * Real.sqrt qm| ≤ 1 / Real.sqrt t :=
    hanen_param_gap β q qm N hβ4 hq.1 hqm.1 hqm.2 hqq
  set ε : ℝ := 1 / Real.sqrt t with hε
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hε0 : 0 < ε := by positivity
  have h1t : 1 / t ≤ ε := by
    rw [hε]
    apply one_div_le_one_div_of_le hsqt
    rw [Real.sqrt_le_left ht0.le]
    nlinarith
  -- the cosh averages
  have hJ : |(∫ z : ℝ, (Real.cosh (βm * z * Real.sqrt qm + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1) -
      ∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1| ≤
      4 * p * ε := by
    have e1 : ∀ (b c : ℝ), (fun z : ℝ => (Real.cosh (b * z * c + h) ^ (4 * p))⁻¹) =
        fun z => (Real.cosh ((b * c) * z + h) ^ (4 * p))⁻¹ := by
      intro b c; funext z; rw [mul_right_comm]
    rw [e1, e1]
    have := abs_integral_inv_cosh_pow_sub_le p (βm * Real.sqrt qm) (β * Real.sqrt q) h
    push_cast at this
    refine this.trans ?_
    rw [abs_sub_comm] at hgap
    calc 4 * (p : ℝ) * |βm * Real.sqrt qm - β * Real.sqrt q| ≤ 4 * p * ε :=
          mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = _ := rfl
  -- the tanh^4 averages and alpha
  have hE : |(∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 4 ∂gaussianReal 0 1) -
      ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1| ≤ 4 * ε := by
    have := abs_integral_tanh_pow_four_sub_le (βm * Real.sqrt qm) (β * Real.sqrt q) h
    refine this.trans ?_
    rw [abs_sub_comm] at hgap
    exact mul_le_mul_of_nonneg_left hgap (by norm_num)
  have hα := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hαm := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfixm
  simp only [integral_tanh_pow_mul_z_sqrt_eq] at hα hαm
  have hαdiff : |α - αm| ≤ 4 * ε + 2 / t := by
    have e : α - αm = -((∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 4 ∂gaussianReal 0 1) -
        ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1) +
        2 * (qm - q) := by simp only [α, αm]; ring
    rw [e]
    calc _ ≤ |-((∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 4 ∂gaussianReal 0 1) -
        ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1)| + |2 * (qm - q)| :=
          abs_add_le _ _
      _ ≤ 4 * ε + 2 / t := by
          rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm qm q]
          have : 2 * |q - qm| ≤ 2 / t := by
            have := hqq
            calc 2 * |q - qm| ≤ 2 * (1 / t) := by gcongr
              _ = 2 / t := by ring
          linarith
  have hbdiff : |β ^ 2 - βm ^ 2| ≤ 1 / (4 * t) := by
    have e : β ^ 2 - βm ^ 2 = β ^ 2 * (1 / t) := by rw [hβmsq, ← hθ1]; ring
    rw [e, abs_of_nonneg (by positivity)]
    calc β ^ 2 * (1 / t) ≤ 1 / 4 * (1 / t) := by gcongr
      _ = 1 / (4 * t) := by field_simp
  have hAgap := abs_div_sub_div_le_of_mem_Icc hα hαm (sq_nonneg β) hβ2 (sq_nonneg βm)
    (by rw [hβmsq]; nlinarith [sq_nonneg β])
  have hArange (αx bx : ℝ) (hαx : αx ∈ Set.Icc (0 : ℝ) 1) (hb0 : 0 ≤ bx) (hb : bx ≤ 1 / 4) :
      αx / (1 - bx * αx) ∈ Set.Icc (0 : ℝ) (4 / 3) := by
    have hD : 3 / 4 ≤ 1 - bx * αx := by nlinarith [hαx.1, hαx.2]
    refine ⟨div_nonneg hαx.1 (by linarith), ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hαx.1, hαx.2]
  have hAr := hArange α (β ^ 2) hα (sq_nonneg β) hβ2
  have hAmr := hArange αm (βm ^ 2) hαm (sq_nonneg βm)
    (by rw [hβmsq]; nlinarith [sq_nonneg β])
  have hδ : |θ * Am - A| ≤ 13 * ε := by
    have e : θ * Am - A = (θ - 1) * Am + (Am - A) := by ring
    rw [e]
    have h2 : |Am - A| ≤ 16 / 9 * (|α - αm| + |β ^ 2 - βm ^ 2|) := by
      rw [abs_sub_comm]; exact hAgap
    calc _ ≤ |(θ - 1) * Am| + |Am - A| := abs_add_le _ _
      _ ≤ (1 / t) * (4 / 3) + 16 / 9 * ((4 * ε + 2 / t) + 1 / (4 * t)) := by
          refine add_le_add ?_ (h2.trans (by gcongr))
          rw [abs_mul, abs_of_nonpos (by linarith), abs_of_nonneg hAmr.1, neg_sub, hθ1]
          exact mul_le_mul_of_nonneg_left hAmr.2 (by positivity)
      _ ≤ 13 * ε := by
          have h3 : 1 / (4 * t) ≤ ε / 4 := by
            have : 1 / (4 * t) = (1 / t) / 4 := by field_simp
            rw [this]; linarith
          have h4 : 2 / t ≤ 2 * ε := by
            have : 2 / t = 2 * (1 / t) := by ring
            rw [this]; linarith
          nlinarith
  -- reduce to the abstract algebra
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hβm0 : 0 ≤ βm ^ 2 := sq_nonneg βm
  have hAbd : A ∈ Set.Icc (0 : ℝ) (4 / 3) := hAr
  have hAmbd : Am ∈ Set.Icc (0 : ℝ) (4 / 3) := hAmr
  have hlead := hanen_lead_bracket_eq (N : ℝ) hN (β ^ 2) Am
  rw [← ht, ← hθ] at hlead
  rw [← mul_pow, hβmsq, hlead]
  exact (hanen_shift_core p t θ (β ^ 2) A Am _ _ ε ht2 hθ0 hθle (sq_nonneg β) hβ2 hε hAbd
    hAmbd hδ (abs_integral_gaussianReal_le_one _ fun z => by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (Real.one_le_cosh _))) hJ).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

end SpinGlasses
