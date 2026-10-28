/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKFixedPointResidual
public import LeanMachineLearning.SpinGlasses.SKSmartPathProfile

/-!
# The replica-symmetric functional and its critical points (Talagrand, Proposition 1.3.8)

Guerra's bound (Theorem 1.3.7) is `p_N(β, h) ≤ RS(q)` for every `q ≥ 0`, where
`RS(y) = log 2 + 𝔼 log cosh (β √y z + h) + β² (1 - y)² / 4`.  Talagrand explains that the best
choice of `q` solves the self-consistency equation (1.74), by computing `RS'` from the Gaussian
integration by parts formula (1.75).  This file formalizes that explanation:

* `SpinGlasses.hasDerivAt_integral_log_cosh_sqrt`: Eq. (1.75) for `f = log cosh`;
* `SpinGlasses.hasDerivAt_rsFunctional`: `RS'(x) = (β² / 2) (x - Φ(x))` for `x > 0`;
* `SpinGlasses.fixedPoint_of_isMinOn_rsFunctional`: for `β ≠ 0` a minimizer of `RS` on `[0, ∞)`
  is a fixed point (a minimizer at `0` forces `h = 0`);
* `SpinGlasses.exists_fixedPoint_isMinOn_rsFunctional`: a minimizing fixed point exists;
* `SpinGlasses.fixedPoint_unique_of_abs_lt_one`: for `|β| < 1` the fixed point is unique for every
  `h`, including `h = 0` (the short argument of the book, `Φ' ≤ β²`).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eqs. (1.74)-(1.76) and
  Proposition 1.3.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SpinGlasses

/-- **Guerra's replica-symmetric functional** (Talagrand, Eq. (1.76) and Theorem 1.3.7):
`RS(y) = log 2 + 𝔼 log cosh (β √y z + h) + β² (1 - y)² / 4`.  It is a definition because it is the
object that is differentiated, minimized and bounded in this file and in Guerra's bound. -/
noncomputable def rsFunctional (β h y : ℝ) : ℝ :=
  Real.log 2 + ∫ z : ℝ, Real.log (Real.cosh (β * Real.sqrt y * z + h)) ∂(gaussianReal 0 1) +
    β ^ 2 / 4 * (1 - y) ^ 2

/-- **Eq. (1.75) for `f = log cosh`:** for `x > 0`,
`(d/dx) 𝔼 log cosh (β √x z + h) = (β² / 2) 𝔼 (1 - tanh² (β √x z + h))`. -/
theorem hasDerivAt_integral_log_cosh_sqrt (β h : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ∫ z : ℝ, Real.log (Real.cosh (β * Real.sqrt y * z + h))
        ∂(gaussianReal 0 1))
      (β ^ 2 / 2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1))
      x := by
  exact hasDerivAt_comp_mul_sqrt hx (hasDerivAt_integral_comp_affine_gaussianReal
    (f := fun y => Real.log (Real.cosh y)) (f' := Real.tanh)
    (f'' := fun y => 1 - Real.tanh y ^ 2) Real.hasDerivAt_log_cosh
    Real.hasDerivAt_tanh (by have := Real.continuous_tanh; fun_prop)
    (fun y => (Real.abs_tanh_lt_one y).le) Real.abs_one_sub_tanh_sq_le h (β * Real.sqrt x)
    (integrable_log_cosh_affine_gaussianReal _ _))

/-- **The derivative of the replica-symmetric functional:** for `x > 0`,
`RS'(x) = (β² / 2) (x - 𝔼 tanh² (β √x z + h))` (Talagrand, after Eq. (1.75)). -/
theorem hasDerivAt_rsFunctional (β h : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rsFunctional β h)
      (β ^ 2 / 2 * (x - ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)))
      x := by
  have h1 := ((hasDerivAt_integral_log_cosh_sqrt β h hx).const_add (Real.log 2)).add
    ((((hasDerivAt_id x).const_sub 1).pow 2).const_mul (β ^ 2 / 4))
  have hI : ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) =
      1 - ∫ z : ℝ, Real.tanh (β * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) := by
    rw [integral_sub (integrable_const _) (integrable_tanh_sq_affine _ _)]
    simp
  refine h1.congr_deriv ?_
  rw [hI]
  simp only [id]
  ring

/-- `RS` is continuous on every compact interval `[0, R]`. -/
theorem continuousOn_rsFunctional (β h R : ℝ) : ContinuousOn (rsFunctional β h) (Icc 0 R) := by
  have hint : ContinuousOn (fun y : ℝ => ∫ z : ℝ,
      Real.log (Real.cosh (β * Real.sqrt y * z + h)) ∂(gaussianReal 0 1)) (Icc 0 R) := by
    refine continuousOn_of_dominated (bound := fun z => |β| * Real.sqrt R * |z| + |h|)
      (fun y _ => ?_) (fun y hy => ae_of_all _ fun z => ?_)
      ((integrable_abs_id_gaussianReal.const_mul _).add (integrable_const _))
      (ae_of_all _ fun z => ?_)
    · exact (Real.continuous_cosh.comp (by fun_prop : Continuous fun z : ℝ =>
        β * Real.sqrt y * z + h)).log (fun x => (Real.cosh_pos _).ne') |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_cosh_nonneg _)]
      refine (Real.log_cosh_le_abs _).trans ?_
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg y)]
      gcongr
      exact hy.2
    · exact (Real.continuous_cosh.comp (by fun_prop : Continuous fun y : ℝ =>
        β * Real.sqrt y * z + h)).log (fun x => (Real.cosh_pos _).ne') |>.continuousOn
  unfold rsFunctional
  exact ((continuousOn_const.add hint).add (by fun_prop))

/-- `RS(y) ≥ log 2 + β² (1 - y)² / 4`, since `log cosh ≥ 0`. -/
theorem log_two_add_le_rsFunctional (β h y : ℝ) :
    Real.log 2 + β ^ 2 / 4 * (1 - y) ^ 2 ≤ rsFunctional β h y := by
  unfold rsFunctional
  have : 0 ≤ ∫ z : ℝ, Real.log (Real.cosh (β * Real.sqrt y * z + h)) ∂(gaussianReal 0 1) :=
    integral_nonneg fun z => Real.log_cosh_nonneg _
  linarith

/-- **A minimizer of `RS` is a solution of (1.74)** (Talagrand, after Eq. (1.75)): if `β ≠ 0`
and `q ≥ 0` minimizes `RS` on `[0, ∞)` then `q = 𝔼 tanh² (β √q z + h)`.  For `q > 0` the
derivative vanishes at the interior minimum; at `q = 0` the derivative of `RS` at `0+` is
`-(β² / 2) tanh² h`, which would make `RS` strictly decrease from `0` unless `h = 0`, in which case
`0` is itself a solution.  (For `β = 0`, `RS` is constant and every `q` minimizes it.) -/
theorem fixedPoint_of_isMinOn_rsFunctional {β h q : ℝ} (hβ : β ≠ 0) (hq : 0 ≤ q)
    (hmin : IsMinOn (rsFunctional β h) (Ici 0) q) :
    ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q := by
  have hβ2 : 0 < β ^ 2 / 2 := by positivity
  rcases hq.eq_or_lt with rfl | hqpos
  · by_cases hh : h = 0
    · simp [hh]
    exfalso
    set Φ : ℝ → ℝ := fun y => ∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)
      with hΦ
    have hΦ0 : Φ 0 = Real.tanh h ^ 2 := by simp [hΦ]
    have hc : 0 < Real.tanh h ^ 2 := by simpa using fixedPointMap_pos hh (0 : ℝ)
    have hev : ∀ᶠ y in 𝓝 (0 : ℝ), Real.tanh h ^ 2 / 2 < Φ y :=
      (continuous_fixedPointMap β h).continuousAt.eventually
        (lt_mem_nhds (a := Real.tanh h ^ 2 / 2) (b := Φ 0) (by rw [hΦ0]; linarith))
    obtain ⟨ε, hε, hεy⟩ := Metric.eventually_nhds_iff.1 hev
    set δ := min (ε / 2) (Real.tanh h ^ 2 / 4) with hδ
    have hδpos : 0 < δ := lt_min (half_pos hε) (by linarith)
    have hanti : StrictAntiOn (rsFunctional β h) (Icc 0 δ) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc 0 δ) (continuousOn_rsFunctional β h δ) ?_
      intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hx.1
      rw [(hasDerivAt_rsFunctional β h hx0).deriv]
      have h1 : Real.tanh h ^ 2 / 2 < Φ x := by
        refine hεy ?_
        rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
        linarith [hx.2, min_le_left (ε / 2) (Real.tanh h ^ 2 / 4)]
      have h2 : x < Real.tanh h ^ 2 / 4 := lt_of_lt_of_le hx.2 (min_le_right _ _)
      exact mul_neg_of_pos_of_neg hβ2 (by linarith)
    have := hanti (left_mem_Icc.2 hδpos.le) (right_mem_Icc.2 hδpos.le) hδpos
    exact absurd (hmin (show δ ∈ Ici (0 : ℝ) from hδpos.le)) (not_le.2 this)
  · have hloc : IsLocalMin (rsFunctional β h) q := hmin.isLocalMin (Ici_mem_nhds hqpos)
    have hd := hloc.hasDerivAt_eq_zero (hasDerivAt_rsFunctional β h hqpos)
    have := (mul_eq_zero.1 hd).resolve_left hβ2.ne'
    linarith

/-- **Existence of a minimizing solution of (1.74):** for every `β` and `h` there is `q ≥ 0` which
solves `q = 𝔼 tanh² (β √q z + h)` and minimizes `RS` on `[0, ∞)`.  With Guerra's bound
(Theorem 1.3.7, valid for every `y ≥ 0`) this shows that the best bound of this form is attained
at a solution of (1.74). -/
theorem exists_fixedPoint_isMinOn_rsFunctional (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ IsMinOn (rsFunctional β h) (Ici 0) q ∧
      ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q := by
  by_cases hβ : β = 0
  · obtain ⟨q, hq, hqe⟩ := exists_fixedPoint β h
    refine ⟨q, hq.1, fun y _ => ?_, hqe.symm⟩
    simp [rsFunctional, hβ]
  have hβ2 : 0 < β ^ 2 := by positivity
  set D := rsFunctional β h 1 - Real.log 2 with hD
  have hD0 : 0 ≤ D := by
    have := log_two_add_le_rsFunctional β h 1
    simp at this
    linarith
  set R : ℝ := 1 + Real.sqrt (4 * D / β ^ 2) with hR
  have hR1 : 1 ≤ R := by linarith [Real.sqrt_nonneg (4 * D / β ^ 2)]
  obtain ⟨q, hqmem, hqmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_isMinOn
    ⟨0, left_mem_Icc.2 (by linarith)⟩ (continuousOn_rsFunctional β h R)
  have hq0 : 0 ≤ q := hqmem.1
  have hglob : IsMinOn (rsFunctional β h) (Ici 0) q := by
    intro y hy
    change rsFunctional β h q ≤ rsFunctional β h y
    by_cases hyR : y ≤ R
    · exact hqmin (show y ∈ Icc 0 R from ⟨hy, hyR⟩)
    · push Not at hyR
      have h1 : rsFunctional β h q ≤ rsFunctional β h 1 :=
        hqmin (show (1 : ℝ) ∈ Icc 0 R from ⟨zero_le_one, hR1⟩)
      have h2 := log_two_add_le_rsFunctional β h y
      have h3 : 4 * D / β ^ 2 ≤ (y - 1) ^ 2 := by
        have : Real.sqrt (4 * D / β ^ 2) ≤ y - 1 := by linarith
        calc 4 * D / β ^ 2 = Real.sqrt (4 * D / β ^ 2) ^ 2 :=
              (Real.sq_sqrt (by positivity)).symm
          _ ≤ (y - 1) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
      have h4 : D ≤ β ^ 2 / 4 * (1 - y) ^ 2 := by
        rw [div_le_iff₀ hβ2] at h3
        nlinarith
      linarith
  exact ⟨q, hq0, hglob, fixedPoint_of_isMinOn_rsFunctional hβ hq0 hglob⟩

/-- **`Φ' ≤ β²`** (the short argument of the book for `β < 1`): for `x > 0`,
`Φ'(x) = β² 𝔼 [(1 - tanh²)(1 - 3 tanh²)] ≤ β²`, since `(1 - t)(1 - 3t) = 1 - 4t + 3t² ≤ 1` for
`t = tanh² ∈ [0, 1]`. -/
theorem deriv_fixedPointMap_sqrt_le (β h x : ℝ) :
    β ^ 2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) ≤ β ^ 2 := by
  have hle : ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
      (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) ≤ 1 := by
    have hint : Integrable (fun z : ℝ => (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2)) (gaussianReal 0 1) := by
      refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun z => ?_)
      · exact ((continuous_const.sub (continuous_tanh_sq_affine _ h)).mul
          (continuous_const.sub ((continuous_tanh_sq_affine _ h).const_mul 3))).aestronglyMeasurable
      · have h0 : 0 ≤ Real.tanh (β * Real.sqrt x * z + h) ^ 2 := sq_nonneg _
        have h1 := Real.tanh_sq_lt_one (β * Real.sqrt x * z + h)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith
    calc _ ≤ ∫ z : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) := by
          refine integral_mono hint (integrable_const _) fun z => ?_
          have h0 : 0 ≤ Real.tanh (β * Real.sqrt x * z + h) ^ 2 := sq_nonneg _
          have h1 := Real.tanh_sq_lt_one (β * Real.sqrt x * z + h)
          nlinarith
      _ = 1 := by simp
  nlinarith [sq_nonneg β]

/-- **Uniqueness of the fixed point for `|β| < 1`, every `h`** (Talagrand, Proposition 1.3.8, the
short argument): since `Φ' ≤ β² < 1`, `Φ(x) - x` is strictly decreasing on `[0, ∞)`, so (1.74) has
at most one solution `q ≥ 0`; this includes `h = 0`, where the solution is `0`. -/
theorem fixedPoint_unique_of_abs_lt_one {β h q r : ℝ} (hβ : |β| < 1) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hqe : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hre : ∫ z : ℝ, Real.tanh (β * Real.sqrt r * z + h) ^ 2 ∂(gaussianReal 0 1) = r) :
    q = r := by
  have hβ2 : β ^ 2 < 1 := by
    have := sq_abs β
    nlinarith [abs_nonneg β]
  set g : ℝ → ℝ := fun y =>
    (∫ z : ℝ, Real.tanh (β * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)) - y with hg
  have hanti : StrictAntiOn g (Ici 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici 0)
      (((continuous_fixedPointMap β h).sub continuous_id).continuousOn) ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    have hd := (hasDerivAt_fixedPointMap_sqrt β h hx0).sub (hasDerivAt_id x)
    have e : deriv g x = β ^ 2 * ∫ z : ℝ, (1 - Real.tanh (β * Real.sqrt x * z + h) ^ 2) *
        (1 - 3 * Real.tanh (β * Real.sqrt x * z + h) ^ 2) ∂(gaussianReal 0 1) - 1 := hd.deriv
    rw [e]
    linarith [deriv_fixedPointMap_sqrt_le β h x]
  refine hanti.injOn hq hr ?_
  simp only [hg, hqe, hre, sub_self]

end SpinGlasses
