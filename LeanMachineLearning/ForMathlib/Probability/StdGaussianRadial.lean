/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Radial moments of the standard Gaussian

For the standard Gaussian measure `stdGaussian E` on a finite-dimensional real inner product space
`E` of dimension `k > 0` (Muirhead, 1982; Vershynin, 2018, §3.3), this file proves

* `stdGaussian_eq_withDensity`: `stdGaussian E` has Lebesgue density `(2π)^(-k/2) exp (-‖x‖²/2)`
  (by matching characteristic functions with Mathlib's Gaussian Fourier integral);
* `integral_comp_norm_stdGaussian`: polar-coordinate reduction
  `∫ f ‖x‖ = K ∫₀^∞ r^(k-1) f r e^(-r²/2)` with a constant `K` that never needs to be evaluated;
* `integral_norm_rpow_stdGaussian`: the radial moment formula
  `E ‖x‖^a = 2^(a/2) Γ ((k + a)/2) / Γ (k/2)` for every real `a > -k`, together with integrability;
* `integral_norm_sq_pow_stdGaussian`: the `χ²_k` moments `E (‖x‖²)^j = ∏_{i<j} (k + 2 i)`;
* `integral_sumSq_pow_pi_gaussianReal`: the same moments for `∑ g_i²` under
  `Measure.pi fun _ => gaussianReal 0 1`;
* `stdGaussian_submodule_eq_zero`, `pi_gaussianReal_submodule_eq_zero`: proper subspaces are
  null (an almost-sure statement, e.g. a Gaussian vector avoids the span of finitely many others).

Since `‖x‖²` under `stdGaussian E` is a `χ²_k` variable, these are the chi-squared moments,
including the inverse moments (`a < 0`) that the Wishart and inverse-Wishart calculations of
random matrix theory need. The unit-ball volume appearing in the polar formula cancels against the
normalization `∫ 1 = 1`, so no spherical measure is ever computed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private lemma integrable_exp_neg_half_sq_norm :
    Integrable (fun x : E => Real.exp (-‖x‖ ^ 2 / 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E)
    (b := ((1 / 2 : ℝ) : ℂ)) (by simp) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]
  ring

/-- **Density of the standard Gaussian.** On a `k`-dimensional real inner product space,
`stdGaussian E` has Lebesgue density `x ↦ (2π)^(-k/2) exp (-‖x‖²/2)`.

Proof: both sides are finite measures, so it suffices to compare characteristic functions
(`Measure.ext_of_charFun`); the left one is `exp (-‖t‖²/2)` (`charFun_stdGaussian`), and the right
one is Mathlib's Gaussian Fourier integral
`GaussianFourier.integral_cexp_neg_mul_sq_norm_add` with `b = 1/2`. -/
theorem stdGaussian_eq_withDensity :
    stdGaussian E = (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal ((2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-‖x‖ ^ 2 / 2))) := by
  set c : ℝ := (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hc
  have hc0 : 0 < c := by positivity
  have hnn : ∀ x : E, 0 ≤ c * Real.exp (-‖x‖ ^ 2 / 2) := fun x => by positivity
  have hmeas : Measurable (fun x : E => ENNReal.ofReal (c * Real.exp (-‖x‖ ^ 2 / 2))) := by
    fun_prop
  have hfin : IsFiniteMeasure ((volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (c * Real.exp (-‖x‖ ^ 2 / 2)))) :=
    isFiniteMeasure_withDensity_ofReal
      (integrable_exp_neg_half_sq_norm.const_mul c).hasFiniteIntegral
  refine (Measure.ext_of_charFun (funext fun t => ?_)).symm
  rw [charFun_stdGaussian, charFun_apply, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hnn _)]
  have key : ∀ x : E, (c * Real.exp (-‖x‖ ^ 2 / 2)) • Complex.exp (↑⟪x, t⟫_ℝ * Complex.I) =
      (c : ℂ) * Complex.exp (-((1 / 2 : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 + Complex.I * ↑⟪t, x⟫_ℝ) := by
    intro x
    rw [Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    rw [real_inner_comm]
    push_cast
    ring_nf
  simp_rw [key]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (b := ((1 / 2 : ℝ) : ℂ)) (by simp) Complex.I t]
  have h2 : (c : ℂ) * ((π : ℂ) / ((1 / 2 : ℝ) : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2) = 1 := by
    have e1 : (π : ℂ) / ((1 / 2 : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((Module.finrank ℝ E : ℂ) / 2) = (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e1, e2, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul, hc,
      ← Real.rpow_add (by positivity), neg_div, neg_add_cancel, Real.rpow_zero]
    simp
  rw [← mul_assoc, h2, one_mul, Complex.I_sq]
  congr 1
  push_cast
  ring

/-- **Polar-coordinate reduction.** For `x ~ stdGaussian E` with `E` nontrivial of dimension `k`,
`E f ‖x‖ = K ∫₀^∞ r^(k-1) (f r e^(-r²/2)) dr` with the explicit constant
`K = (2π)^(-k/2) · k · vol (B(0,1))`. The constant is never evaluated: it is eliminated by the
normalization `E 1 = 1` (see `integral_norm_rpow_stdGaussian`).

Proof: `stdGaussian_eq_withDensity` followed by Mathlib's `integral_fun_norm_addHaar`. -/
theorem integral_comp_norm_stdGaussian [Nontrivial E] (f : ℝ → ℝ) :
    ∫ x, f ‖x‖ ∂stdGaussian E =
      ((2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          (Module.finrank ℝ E * (volume : Measure E).real (Metric.ball 0 1))) *
        ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) * (f y * Real.exp (-y ^ 2 / 2)) := by
  set c : ℝ := (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hc
  have hnn : ∀ x : E, 0 ≤ c * Real.exp (-‖x‖ ^ 2 / 2) := fun x => by positivity
  have hmeas : Measurable (fun x : E => ENNReal.ofReal (c * Real.exp (-‖x‖ ^ 2 / 2))) := by
    fun_prop
  rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hnn _), smul_eq_mul]
  have := integral_fun_norm_addHaar (volume : Measure E)
    (fun y => c * Real.exp (-y ^ 2 / 2) * f y)
  simp only [nsmul_eq_mul, smul_eq_mul] at this
  rw [this]
  have e : ∀ y : ℝ, y ^ (Module.finrank ℝ E - 1) * (c * Real.exp (-y ^ 2 / 2) * f y) =
      c * (y ^ (Module.finrank ℝ E - 1) * (f y * Real.exp (-y ^ 2 / 2))) := fun y => by ring
  simp_rw [e, integral_const_mul]
  ring

/-- **Radial Gaussian integral.** For `k > 0` and real `a > -k`,
`∫₀^∞ r^(k-1) (r^a e^(-r²/2)) dr = 2^((k+a)/2 - 1) Γ ((k+a)/2)`.

With `a = 0` and `k = 2, 4` this recovers `NTK.integral_radial_gaussian_one` and
`NTK.integral_radial_gaussian_three`. Proof: Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`
with `p = 2`, `b = 1/2`. -/
theorem integral_radial_gaussian {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : -(k : ℝ) < a) :
    ∫ y in Ioi (0 : ℝ), y ^ (k - 1) * (y ^ a * Real.exp (-y ^ 2 / 2)) =
      2 ^ (((k : ℝ) + a) / 2 - 1) * Real.Gamma (((k : ℝ) + a) / 2) := by
  have hq : (-1 : ℝ) < (k : ℝ) - 1 + a := by linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (k : ℝ) - 1 + a) (b := 1 / 2)
    (by norm_num) hq (by norm_num)
  have e : ∀ y ∈ Ioi (0 : ℝ), y ^ (k - 1) * (y ^ a * Real.exp (-y ^ 2 / 2)) =
      y ^ ((k : ℝ) - 1 + a) * Real.exp (-(1 / 2) * y ^ (2 : ℝ)) := by
    intro y hy
    have hy : 0 < y := hy
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hy, this, Real.rpow_two]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, h]
  have hs : (k : ℝ) - 1 + a + 1 = k + a := by ring
  rw [hs, one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_div, neg_neg,
    Real.rpow_sub_one (by norm_num)]
  ring

/-- **Radial moments of the standard Gaussian.** On a nontrivial finite-dimensional real inner
product space of dimension `k`, for every real `a > -k`,
`E ‖x‖^a = 2^(a/2) Γ ((k + a)/2) / Γ (k/2)`.

In particular `‖x‖²` is a `χ²_k` variable and `a = -2, -4` give its inverse moments (for
`k > 2, 4`).
Proof: `integral_comp_norm_stdGaussian` with `f r = r^a` and `f r = r^0`; the common constant `K`
cancels because `E 1 = 1`, leaving a ratio of two `integral_radial_gaussian` values. -/
theorem integral_norm_rpow_stdGaussian [Nontrivial E] {a : ℝ}
    (ha : -(Module.finrank ℝ E : ℝ) < a) :
    ∫ x, ‖x‖ ^ a ∂stdGaussian E =
      2 ^ (a / 2) * Real.Gamma (((Module.finrank ℝ E : ℝ) + a) / 2) /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) := by
  have hk : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hkr : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hk
  have h0 := integral_comp_norm_stdGaussian (E := E) (fun y => y ^ (0 : ℝ))
  have h1 := integral_comp_norm_stdGaussian (E := E) (fun y => y ^ a)
  have J0 := integral_radial_gaussian hk (a := 0) (by linarith)
  have J1 := integral_radial_gaussian hk (a := a) ha
  simp only [Real.rpow_zero, integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
  simp only [Real.rpow_zero, one_mul, add_zero] at J0 h0
  rw [J0] at h0
  set K : ℝ := (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    (Module.finrank ℝ E * (volume : Measure E).real (Metric.ball 0 1)) with hK
  rw [h1, J1]
  have hG : 0 < Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hK2 : K * 2 ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) =
      1 / Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) := by
    rw [eq_div_iff hG.ne']
    calc K * 2 ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) * Real.Gamma ((Module.finrank ℝ E : ℝ) / 2)
        = K * (2 ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) *
            Real.Gamma ((Module.finrank ℝ E : ℝ) / 2)) := by ring
      _ = 1 := h0.symm
  have hs : ((Module.finrank ℝ E : ℝ) + a) / 2 - 1 =
      a / 2 + ((Module.finrank ℝ E : ℝ) / 2 - 1) := by ring
  rw [hs, Real.rpow_add (by norm_num)]
  calc K * (2 ^ (a / 2) * 2 ^ ((Module.finrank ℝ E : ℝ) / 2 - 1) *
        Real.Gamma (((Module.finrank ℝ E : ℝ) + a) / 2))
      = 2 ^ (a / 2) * Real.Gamma (((Module.finrank ℝ E : ℝ) + a) / 2) *
        (K * 2 ^ ((Module.finrank ℝ E : ℝ) / 2 - 1)) := by ring
    _ = _ := by rw [hK2]; ring

/-- `‖x‖^a` is integrable under `stdGaussian E` exactly in the range `a > -k` where the moment
formula `integral_norm_rpow_stdGaussian` holds. Proof: if it were not integrable, the Bochner
integral would be `0`, contradicting the strictly positive value of that formula. -/
theorem integrable_norm_rpow_stdGaussian [Nontrivial E] {a : ℝ}
    (ha : -(Module.finrank ℝ E : ℝ) < a) :
    Integrable (fun x : E => ‖x‖ ^ a) (stdGaussian E) := by
  by_contra h
  have h0 := integral_norm_rpow_stdGaussian (E := E) ha
  rw [integral_undef h] at h0
  have hk : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have hpos : 0 < 2 ^ (a / 2) * Real.Gamma (((Module.finrank ℝ E : ℝ) + a) / 2) /
      Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) := by
    have := Real.Gamma_pos_of_pos (show 0 < ((Module.finrank ℝ E : ℝ) + a) / 2 by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < (Module.finrank ℝ E : ℝ) / 2 by positivity)
    positivity
  linarith

private lemma rpow_two_mul_natCast {r : ℝ} (hr : 0 ≤ r) (j : ℕ) :
    r ^ (2 * (j : ℝ)) = (r ^ 2) ^ j := by
  rw [Real.rpow_mul hr, Real.rpow_two, Real.rpow_natCast]

private lemma Gamma_add_natCast_eq_prod (s : ℝ) (hs : 0 < s) (j : ℕ) :
    Real.Gamma (s + j) = (∏ i ∈ Finset.range j, (s + i)) * Real.Gamma s := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity),
      ih]
    ring

/-- Every power `(‖x‖²)^j` is integrable under `stdGaussian E` (the `χ²_k` variable has all
moments). -/
theorem integrable_norm_sq_pow_stdGaussian [Nontrivial E] (j : ℕ) :
    Integrable (fun x : E => (‖x‖ ^ 2) ^ j) (stdGaussian E) := by
  have hk : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have hj : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
  have := integrable_norm_rpow_stdGaussian (E := E) (a := 2 * (j : ℝ)) (by linarith)
  simpa only [rpow_two_mul_natCast (norm_nonneg _)] using this

/-- **`χ²_k` moments.** For `x ~ stdGaussian E` with `dim E = k`,
`E (‖x‖²)^j = ∏_{i<j} (k + 2 i)`.

Proof: `integral_norm_rpow_stdGaussian` with `a = 2j` and `Γ (k/2 + j) = ∏_{i<j} (k/2 + i) Γ (k/2)`.
It is the engine of `NeuralNetwork.DeepLinear.integral_sumSq_pow_stdGaussian`, which replaced a
Stein-recursion proof of the same formula. -/
theorem integral_norm_sq_pow_stdGaussian [Nontrivial E] (j : ℕ) :
    ∫ x, (‖x‖ ^ 2) ^ j ∂stdGaussian E =
      ∏ i ∈ Finset.range j, ((Module.finrank ℝ E : ℝ) + 2 * i) := by
  have hk : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have h := integral_norm_rpow_stdGaussian (E := E) (a := 2 * (j : ℝ))
    (by have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
        linarith)
  simp only [rpow_two_mul_natCast (norm_nonneg _)] at h
  rw [h]
  have e1 : (2 : ℝ) ^ (2 * (j : ℝ) / 2) = 2 ^ j := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]
  have e2 : ((Module.finrank ℝ E : ℝ) + 2 * (j : ℝ)) / 2 = (Module.finrank ℝ E : ℝ) / 2 + j := by
    ring
  have hG : 0 < Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [e1, e2, Gamma_add_natCast_eq_prod _ (by positivity), mul_div_assoc,
    mul_comm _ (Real.Gamma _), mul_div_cancel_left₀ _ hG.ne']
  have e3 : ∏ i ∈ Finset.range j, ((Module.finrank ℝ E : ℝ) + 2 * (i : ℝ)) =
      ∏ i ∈ Finset.range j, (2 * ((Module.finrank ℝ E : ℝ) / 2 + (i : ℝ))) :=
    Finset.prod_congr rfl fun i _ => by ring
  rw [e3, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- **`χ²` moments in coordinates.** For `g` with i.i.d. standard normal coordinates indexed by a
nonempty finite type `ι`, `E (∑ᵢ gᵢ²)^j = ∏_{i<j} (|ι| + 2 i)`.

This is `integral_norm_sq_pow_stdGaussian` transported along `map_pi_eq_stdGaussian`. -/
theorem integral_sumSq_pow_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι] (j : ℕ) :
    ∫ g : ι → ℝ, (∑ i, g i ^ 2) ^ j ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∏ i ∈ Finset.range j, ((Fintype.card ι : ℝ) + 2 * i) := by
  have h := integral_norm_sq_pow_stdGaussian (E := EuclideanSpace ℝ ι) j
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)] at h
  simpa [EuclideanSpace.norm_sq_eq] using h

/-- **Inverse `χ²` moment.** For `dim E = k > 2`, `E (‖x‖²)⁻¹ = 1 / (k - 2)`, i.e. `E [1 / χ²_k] =
1/(k-2)`. This is the scalar fact behind `E Tr (GᵀG)⁻¹ = q/(p-q-1)` for an `p × q` Gaussian matrix.

Proof: `integral_norm_rpow_stdGaussian` with `a = -2` and `Γ (k/2) = (k/2 - 1) Γ (k/2 - 1)`. -/
theorem integral_inv_norm_sq_stdGaussian [Nontrivial E] (hk : 2 < (Module.finrank ℝ E : ℝ)) :
    ∫ x, (‖x‖ ^ 2)⁻¹ ∂stdGaussian E = 1 / ((Module.finrank ℝ E : ℝ) - 2) := by
  have h := integral_norm_rpow_stdGaussian (E := E) (a := -2) (by linarith)
  have hL : ∀ x : E, ‖x‖ ^ (-2 : ℝ) = (‖x‖ ^ 2)⁻¹ := fun x => by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]
  simp_rw [hL] at h
  rw [h]
  have e : ((Module.finrank ℝ E : ℝ) / 2) = ((Module.finrank ℝ E : ℝ) + -2) / 2 + 1 := by ring
  have hs : 0 < ((Module.finrank ℝ E : ℝ) + -2) / 2 := by linarith
  rw [e, Real.Gamma_add_one hs.ne', show (-2 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hk2 : (Module.finrank ℝ E : ℝ) - 2 = 2 * (((Module.finrank ℝ E : ℝ) + -2) / 2) := by ring
  rw [hk2]
  have hG := Real.Gamma_pos_of_pos hs
  generalize ((Module.finrank ℝ E : ℝ) + -2) / 2 = s at hs hG ⊢
  field_simp

/-- **Second inverse `χ²` moment.** For `dim E = k > 4`,
`E ((‖x‖²)⁻¹)² = 1 / ((k - 2) (k - 4))`, i.e. `E [1/χ⁴_k]`. -/
theorem integral_inv_norm_sq_sq_stdGaussian [Nontrivial E]
    (hk : 4 < (Module.finrank ℝ E : ℝ)) :
    ∫ x, ((‖x‖ ^ 2)⁻¹) ^ 2 ∂stdGaussian E =
      1 / (((Module.finrank ℝ E : ℝ) - 2) * ((Module.finrank ℝ E : ℝ) - 4)) := by
  have h := integral_norm_rpow_stdGaussian (E := E) (a := -4) (by linarith)
  have hL : ∀ x : E, ‖x‖ ^ (-4 : ℝ) = ((‖x‖ ^ 2)⁻¹) ^ 2 := fun x => by
    have : ‖x‖ ^ (-(2 * ((2 : ℕ) : ℝ))) = ((‖x‖ ^ 2)⁻¹) ^ 2 := by
      rw [Real.rpow_neg (norm_nonneg _), rpow_two_mul_natCast (norm_nonneg _), inv_pow]
    rw [← this]; norm_num
  simp_rw [hL] at h
  rw [h]
  have e : ((Module.finrank ℝ E : ℝ) / 2) = ((Module.finrank ℝ E : ℝ) + -4) / 2 + 1 + 1 := by ring
  have hs : 0 < ((Module.finrank ℝ E : ℝ) + -4) / 2 := by linarith
  rw [e, Real.Gamma_add_one (by positivity), Real.Gamma_add_one hs.ne',
    show (-4 / 2 : ℝ) = -2 by norm_num, Real.rpow_neg (by norm_num)]
  have hk2 : (Module.finrank ℝ E : ℝ) - 2 = 2 * (((Module.finrank ℝ E : ℝ) + -4) / 2 + 1) := by
    ring
  have hk4 : (Module.finrank ℝ E : ℝ) - 4 = 2 * (((Module.finrank ℝ E : ℝ) + -4) / 2) := by ring
  rw [hk2, hk4]
  have hG := Real.Gamma_pos_of_pos hs
  generalize ((Module.finrank ℝ E : ℝ) + -4) / 2 = s at hs hG ⊢
  have hs1 : s + 1 ≠ 0 := by positivity
  field_simp
  norm_num

/-- `((‖x‖²)⁻¹)^j` is integrable under `stdGaussian E` as soon as `2 j < dim E`. -/
theorem integrable_inv_norm_sq_pow_stdGaussian [Nontrivial E] {j : ℕ}
    (hj : 2 * (j : ℝ) < Module.finrank ℝ E) :
    Integrable (fun x : E => ((‖x‖ ^ 2)⁻¹) ^ j) (stdGaussian E) := by
  have := integrable_norm_rpow_stdGaussian (E := E) (a := -(2 * (j : ℝ))) (by linarith)
  simpa only [Real.rpow_neg (norm_nonneg _), rpow_two_mul_natCast (norm_nonneg _), inv_pow]
    using this

/-- The product of i.i.d. standard normals is `stdGaussian` pushed to coordinates: the
`ofLp`-version of `map_pi_eq_stdGaussian`. -/
theorem pi_gaussianReal_eq_map_stdGaussian {κ : Type*} [Fintype κ] :
    (Measure.pi fun _ : κ => gaussianReal 0 1) =
      (stdGaussian (EuclideanSpace ℝ κ)).map (fun x => x.ofLp) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- **A proper subspace is `stdGaussian`-null.** The standard Gaussian has a Lebesgue density
(`stdGaussian_eq_withDensity`) and proper subspaces are Lebesgue-null
(`MeasureTheory.Measure.addHaar_submodule`). -/
theorem stdGaussian_submodule_eq_zero (K : Submodule ℝ E) (hK : K ≠ ⊤) :
    stdGaussian E K = 0 := by
  rw [stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _ (Measure.addHaar_submodule _ K hK)

/-- A proper subspace of `ι → ℝ` is null for the product of standard normals. -/
theorem pi_gaussianReal_submodule_eq_zero {ι : Type*} [Fintype ι] (K : Submodule ℝ (ι → ℝ))
    (hK : K ≠ ⊤) : (Measure.pi fun _ : ι => gaussianReal 0 1) K = 0 := by
  have hKc : IsClosed (K : Set (ι → ℝ)) := K.closed_of_finiteDimensional
  rw [pi_gaussianReal_eq_map_stdGaussian, Measure.map_apply (by fun_prop) hKc.measurableSet]
  refine stdGaussian_submodule_eq_zero (K.comap (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap) ?_
  intro h
  apply hK
  rw [eq_top_iff]
  intro x _
  have : (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm x ∈
      K.comap (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap := by rw [h]; trivial
  simpa using this

end ProbabilityTheory

end
