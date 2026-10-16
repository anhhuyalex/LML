/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import LeanMachineLearning.ForMathlib.Analysis.RpowTsum
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtom
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.RestrictPartition
public import LeanMachineLearning.SpinGlasses.PoissonProcessEquivalence
public import LeanMachineLearning.SpinGlasses.PoissonProcessPartition

/-!
# The Poisson–Dirichlet intensity

The intensity of the Poisson point process used to construct `PD(ζ)` is
`ζ x ^ (-1 - ζ) dx` on the positive half-line. The counting measure itself is represented by
the existing `SpinGlasses.poissonCountingMeasure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

/-- The intensity `ζ x ^ (-1 - ζ) dx` on the positive half-line. -/
noncomputable def zetaPoissonMeasure (ζ : ℝ) : Measure ℝ :=
  volume.withDensity fun x =>
    if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0

instance nullSingletonClass_zetaPoissonMeasure (ζ : ℝ) :
    NullSingletonClass (zetaPoissonMeasure ζ) := by
  unfold zetaPoissonMeasure
  infer_instance

instance sigmaFinite_zetaPoissonMeasure (ζ : ℝ) :
    SigmaFinite (zetaPoissonMeasure ζ) := by
  unfold zetaPoissonMeasure
  exact SigmaFinite.withDensity_of_ne_top' (fun x => by
    split_ifs <;> simp)

/-- The `a`-th moment of the power-law density above one,
`∫_{(1,∞)} ζ x ^ (a - 1 - ζ) dx = ζ / (ζ - a)` for `a < ζ`. -/
theorem integral_Ioi_zeta_rpow_add {ζ a : ℝ} (hζ : 0 < ζ) (haζ : a < ζ) :
    ∫ x in Ioi (1 : ℝ), ζ * x ^ (a - 1 - ζ) = ζ / (ζ - a) := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : a - 1 - ζ < -1)
    (by norm_num : (0 : ℝ) < 1)]
  have h2 : ζ - a ≠ 0 := by linarith
  have h3 : a - ζ ≠ 0 := by linarith
  rw [show a - 1 - ζ + 1 = a - ζ by ring, Real.one_rpow]
  field_simp
  ring

/-- The power-law density has unit mass above one. -/
theorem integral_Ioi_zeta_rpow {ζ : ℝ} (hζ : 0 < ζ) :
    ∫ x in Ioi (1 : ℝ), ζ * x ^ (-1 - ζ) = 1 := by
  simpa [zero_sub, div_self hζ.ne'] using integral_Ioi_zeta_rpow_add hζ (a := 0) hζ

/-- The first moment of points below one, evaluated at the intensity measure. -/
theorem integral_Ioo_zeta_rpow {ζ : ℝ} (hζ1 : ζ < 1) :
    ∫ x in Ioo (0 : ℝ) 1, ζ * x ^ (-ζ) = ζ / (1 - ζ) := by
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by linarith : -1 < -ζ))]
  simp only [Real.one_rpow, Real.zero_rpow (by linarith : -ζ + 1 ≠ 0)]
  ring

/-- The mass of the intensity above `s > 0` is `s ^ (-ζ)`. -/
theorem zetaPoissonMeasure_Ioi {ζ s : ℝ} (hζ : 0 < ζ) (hs : 0 < s) :
    zetaPoissonMeasure ζ (Ioi s) = ENNReal.ofReal (s ^ (-ζ)) := by
  rw [zetaPoissonMeasure, withDensity_apply _ measurableSet_Ioi]
  have heq : (∫⁻ x in Ioi s,
      if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0) =
      ∫⁻ x in Ioi s, ENNReal.ofReal (ζ * x ^ (-1 - ζ)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [lt_trans hs (mem_Ioi.mp hx)]
  rw [heq]
  have hf : IntegrableOn (fun x : ℝ => ζ * x ^ (-1 - ζ)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - ζ < -1) hs).const_mul ζ
  rw [← ofReal_integral_eq_lintegral_ofReal hf]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -1 - ζ < -1) hs,
      show -1 - ζ + 1 = -ζ by ring]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hζ.le (Real.rpow_nonneg (le_of_lt (lt_trans hs (mem_Ioi.mp hx))) _)

/-- The mass of the intensity above one is exactly one. -/
theorem zetaPoissonMeasure_Ioi_one {ζ : ℝ} (hζ : 0 < ζ) :
    zetaPoissonMeasure ζ (Ioi 1) = 1 := by
  simp [zetaPoissonMeasure_Ioi hζ zero_lt_one]

/-- The `ζ`-intensity as an integral against Lebesgue measure on the positive half-line. -/
theorem lintegral_zetaPoissonMeasure (ζ : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂zetaPoissonMeasure ζ =
      ∫⁻ x in Ioi 0, ENNReal.ofReal (ζ * x ^ (-1 - ζ)) * f x := by
  have hd : Measurable (fun x : ℝ => if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).ite measurableSet_Ioi measurable_const
  rw [zetaPoissonMeasure, lintegral_withDensity_eq_lintegral_mul _ hd hf,
    ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun x => ?_
  by_cases hx : 0 < x <;> simp [hx, indicator]

/-- The `b`-th moment of the intensity over a set `A` of positive reals,
`∫_A x ^ b ζ x ^ (-1 - ζ) dx`, written with the exponents combined. -/
theorem lintegral_zetaPoissonMeasure_indicator_rpow {ζ b : ℝ} (hζ : 0 ≤ ζ) (hb : 0 ≤ b)
    {A : Set ℝ} (hA : MeasurableSet A) (hA0 : A ⊆ Ioi 0) :
    ∫⁻ x, A.indicator (fun x => ENNReal.ofReal x ^ b) x ∂zetaPoissonMeasure ζ =
      ∫⁻ x in A, ENNReal.ofReal (ζ * x ^ (b - 1 - ζ)) := by
  have hm : Measurable (A.indicator fun x => ENNReal.ofReal x ^ b) :=
    (ENNReal.measurable_ofReal.pow_const b).indicator hA
  rw [lintegral_zetaPoissonMeasure ζ hm]
  have h1 : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal (ζ * x ^ (-1 - ζ)) *
      A.indicator (fun x => ENNReal.ofReal x ^ b) x =
      A.indicator (fun x => ENNReal.ofReal (ζ * x ^ (b - 1 - ζ))) x := by
    intro x hx
    by_cases h : x ∈ A
    · have hx0 : 0 < x := hx
      simp only [indicator_of_mem h]
      rw [ENNReal.ofReal_rpow_of_nonneg hx.le hb, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_assoc, ← Real.rpow_add hx]
      ring_nf
    · simp [indicator_of_notMem h]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator hA,
    Measure.restrict_restrict hA, inter_eq_left.2 hA0]

/-- The mass of the intensity of the points above one, raised to the power `a`:
`∫_{[1,∞)} x ^ a ζ x ^ (-1-ζ) dx = ζ / (ζ - a)` for `0 ≤ a < ζ`. -/
theorem lintegral_zetaPoissonMeasure_Ici_rpow {ζ a : ℝ} (hζ : 0 < ζ) (ha : 0 ≤ a)
    (haζ : a < ζ) :
    ∫⁻ x, (Ici (1 : ℝ)).indicator (fun x => ENNReal.ofReal x ^ a) x ∂zetaPoissonMeasure ζ =
      ENNReal.ofReal (ζ / (ζ - a)) := by
  rw [lintegral_zetaPoissonMeasure_indicator_rpow hζ.le ha measurableSet_Ici
      fun x (hx : 1 ≤ x) => lt_of_lt_of_le zero_lt_one hx,
    ← setLIntegral_congr (Ioi_ae_eq_Ici (a := (1 : ℝ)))]
  have hint : IntegrableOn (fun x : ℝ => ζ * x ^ (a - 1 - ζ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - 1 - ζ < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul ζ
  rw [← ofReal_integral_eq_lintegral_ofReal hint, integral_Ioi_zeta_rpow_add hζ haζ]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg hζ.le (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)

/-- Expected small-point mass from Campbell's identity. The result assumes only Campbell's
formula, so it applies to any construction of the Poisson counting measure. -/
theorem expected_poisson_sum_lt_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {M : Ω → Measure ℝ}
    (hCamp : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ)) :
    ∫⁻ ω, ∫⁻ x in Ioo 0 1, ENNReal.ofReal x ∂(M ω) ∂P =
      ENNReal.ofReal (ζ / (1 - ζ)) := by
  have hf : Measurable ((Ioo (0 : ℝ) 1).indicator fun x => ENNReal.ofReal x ^ (1 : ℝ)) :=
    (ENNReal.measurable_ofReal.pow_const 1).indicator measurableSet_Ioo
  have hc := hCamp _ hf
  rw [lintegral_zetaPoissonMeasure_indicator_rpow hζ0.le zero_le_one measurableSet_Ioo
    Ioo_subset_Ioi_self] at hc
  simp only [ENNReal.rpow_one, lintegral_indicator measurableSet_Ioo] at hc
  rw [hc, show (1 : ℝ) - 1 - ζ = -ζ by ring]
  have hi : IntegrableOn (fun x : ℝ => ζ * x ^ (-ζ)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2
      (by linarith : -1 < -ζ)).const_mul ζ
  rw [← ofReal_integral_eq_lintegral_ofReal hi, integral_Ioo_zeta_rpow hζ1]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact mul_nonneg hζ0.le (Real.rpow_nonneg hx.1.le _)

/-- **Lemma 2.1, quantitative form (Panchenko, Eq. (2.15)).** For `0 < a < ζ < 1`, the `a`-th moment
of the total mass `∑_{x ∈ Π} x` of the `ζ`-Poisson process is at most
`1 + ζ / (1 - ζ) + ζ / (ζ - a)`. It is stated in `ℝ≥0∞`, so it also shows that the total mass is
finite almost surely (see `ae_lintegral_poisson_lt_top`), unlike a real-valued statement, which
would be vacuous on the event `∑ x = ∞` where `ENNReal.toReal ∞ = 0`.

The process enters only through Campbell's formula and through the fact that each `M ω` is a
counting measure `poissonCountingMeasure N X` (the subadditivity `(∑ xᵢ) ^ a ≤ ∑ xᵢ ^ a` is an
atomic statement and fails for diffuse measures). -/
theorem lintegral_poisson_sum_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ζ a : ℝ} (ha0 : 0 < a) (haζ : a < ζ) (hζ1 : ζ < 1)
    {M : Ω → Measure ℝ} (hMm : Measurable M)
    (hatom : ∀ ω, ∃ (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ), M ω = poissonCountingMeasure N X)
    (hCamp : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ)) :
    ∫⁻ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a ∂P ≤
      1 + ENNReal.ofReal (ζ / (1 - ζ)) + ENNReal.ofReal (ζ / (ζ - a)) := by
  have hζ0 : 0 < ζ := ha0.trans haζ
  have ha1 : a ≤ 1 := by linarith
  set g₂ : ℝ → ℝ≥0∞ := (Ici (1 : ℝ)).indicator fun x => ENNReal.ofReal x ^ a with hg₂
  have hg₂m : Measurable g₂ := (ENNReal.measurable_ofReal.pow_const a).indicator measurableSet_Ici
  have hA : Measurable fun ω => ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal x ∂(M ω) :=
    (Measure.measurable_lintegral_restrict measurableSet_Ioo ENNReal.measurable_ofReal).comp hMm
  have hB : Measurable fun ω => ∫⁻ x, g₂ x ∂(M ω) := (Measure.measurable_lintegral hg₂m).comp hMm
  -- pointwise: split at `1`, use `x ^ a ≤ 1 + x` below and atomic subadditivity above
  have hpt : ∀ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a ≤
      1 + ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal x ∂(M ω) + ∫⁻ x, g₂ x ∂(M ω) := by
    intro ω
    rw [← Ioo_union_Ici_eq_Ioi zero_lt_one, lintegral_union measurableSet_Ici
      ((Iio_disjoint_Ici le_rfl).mono_left Ioo_subset_Iio_self)]
    refine (ENNReal.rpow_add_le_add_rpow _ _ ha0.le ha1).trans ?_
    refine add_le_add (ENNReal.rpow_le_one_add ha0.le ha1) ?_
    obtain ⟨N, X, hω⟩ := hatom ω
    rw [hω, ← lintegral_indicator measurableSet_Ici,
      lintegral_poissonCountingMeasure_eq_tsum N X
        (ENNReal.measurable_ofReal.indicator measurableSet_Ici),
      lintegral_poissonCountingMeasure_eq_tsum N X hg₂m]
    refine (ENNReal.rpow_tsum_le_tsum_rpow _ ha0 ha1).trans (le_of_eq (tsum_congr fun q => ?_))
    by_cases h : X q.1.1 q.1.2 ∈ Ici (1 : ℝ)
    · simp [hg₂, indicator_of_mem h]
    · simp [hg₂, indicator_of_notMem h, ENNReal.zero_rpow_of_pos ha0]
  calc ∫⁻ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a ∂P
      ≤ ∫⁻ ω, (1 + ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal x ∂(M ω) + ∫⁻ x, g₂ x ∂(M ω)) ∂P :=
        lintegral_mono hpt
    _ = 1 + ENNReal.ofReal (ζ / (1 - ζ)) + ENNReal.ofReal (ζ / (ζ - a)) := by
        rw [lintegral_add_right _ hB, lintegral_add_right _ hA, lintegral_const, measure_univ,
          mul_one, expected_poisson_sum_lt_one hζ0 hζ1 hCamp, hCamp g₂ hg₂m,
          lintegral_zetaPoissonMeasure_Ici_rpow hζ0 ha0.le haζ]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ζ : ℝ}
  {M : Ω → Measure ℝ}

/-- The `a`-th power of the total mass `∑_{x ∈ Π} x` is measurable in the sample point. -/
theorem measurable_lintegral_poisson_sum_rpow (hMm : Measurable M) (a : ℝ) :
    Measurable fun ω => (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a :=
  ((Measure.measurable_lintegral_restrict measurableSet_Ioi ENNReal.measurable_ofReal).comp
    hMm).pow_const a

/-- **The total mass `∑_{x ∈ Π} x` of the `ζ`-Poisson process is finite almost surely.** This is a
consequence of Lemma 2.1 (any `a ∈ (0, ζ)` works): the `a`-th moment of the total mass is finite,
so the total mass is. -/
theorem ae_lintegral_poisson_lt_top (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hMm : Measurable M)
    (hatom : ∀ ω, ∃ (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ), M ω = poissonCountingMeasure N X)
    (hCamp : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ)) :
    ∀ᵐ ω ∂P, ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω) < ∞ := by
  have ha0 : 0 < ζ / 2 := by positivity
  have hbound := lintegral_poisson_sum_rpow_le ha0 (by linarith : ζ / 2 < ζ) hζ1 hMm hatom hCamp
  have hm := measurable_lintegral_poisson_sum_rpow hMm (ζ / 2)
  have hfin : ∫⁻ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ (ζ / 2) ∂P ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) hbound
  filter_upwards [ae_lt_top hm hfin] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos ha0).1 hω

/-- **Lemma 2.1, real form.** `𝔼 (∑_{x ∈ Π} x) ^ a < ∞` for `0 < a < ζ < 1`: the total mass has an
integrable `a`-th power. Finiteness of the mass itself is `ae_lintegral_poisson_lt_top`. -/
theorem integrable_poisson_sum_rpow {a : ℝ} (ha0 : 0 < a) (haζ : a < ζ) (hζ1 : ζ < 1)
    (hMm : Measurable M)
    (hatom : ∀ ω, ∃ (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ), M ω = poissonCountingMeasure N X)
    (hCamp : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ)) :
    Integrable (fun ω => (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)).toReal ^ a) P := by
  have hbound := lintegral_poisson_sum_rpow_le ha0 haζ hζ1 hMm hatom hCamp
  have hm := measurable_lintegral_poisson_sum_rpow hMm a
  have := integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (ne_top_of_le_ne_top (by simp) hbound)
  simpa only [ENNReal.toReal_rpow] using this

/-- **Lemma 2.1 (Panchenko, Eq. (2.15)).** For `0 < a < ζ < 1`,
`𝔼 (∑_{x ∈ Π} x) ^ a ≤ 1 + ζ / (1 - ζ) + ζ / (ζ - a)`. -/
theorem integral_poisson_sum_rpow_le {a : ℝ} (ha0 : 0 < a) (haζ : a < ζ) (hζ1 : ζ < 1)
    (hMm : Measurable M)
    (hatom : ∀ ω, ∃ (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ), M ω = poissonCountingMeasure N X)
    (hCamp : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ)) :
    ∫ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)).toReal ^ a ∂P ≤
      1 + ζ / (1 - ζ) + ζ / (ζ - a) := by
  have hζ0 : 0 < ζ := ha0.trans haζ
  have hbound := lintegral_poisson_sum_rpow_le ha0 haζ hζ1 hMm hatom hCamp
  have hm := measurable_lintegral_poisson_sum_rpow hMm a
  have hfin : ∫⁻ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a ∂P ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) hbound
  have hae : ∀ᵐ ω ∂P, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a < ∞ := ae_lt_top hm hfin
  simp_rw [ENNReal.toReal_rpow]
  rw [integral_toReal hm.aemeasurable hae]
  have h1 : 0 ≤ ζ / (1 - ζ) := div_nonneg hζ0.le (by linarith)
  have h2 : 0 ≤ ζ / (ζ - a) := div_nonneg hζ0.le (by linarith)
  calc (∫⁻ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a ∂P).toReal
      ≤ (1 + ENNReal.ofReal (ζ / (1 - ζ)) + ENNReal.ofReal (ζ / (ζ - a))).toReal :=
        ENNReal.toReal_mono (by simp) hbound
    _ = 1 + ζ / (1 - ζ) + ζ / (ζ - a) := by
        rw [ENNReal.toReal_add (by simp) ENNReal.ofReal_ne_top,
          ENNReal.toReal_add ENNReal.one_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_one,
          ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]

/-- **The `PD(ζ)` weights.** If `u₀ ≥ u₁ ≥ …` is the decreasing enumeration of the atoms of `M`
(`MeasureTheory.nthLargestAtom`), then `vₙ = uₙ / ∑ₗ uₗ`. For a ζ-Poisson counting measure these are
almost surely positive, decreasing, and sum to one (`ae_poissonDirichletWeight`): their law is
`PD(ζ)`. -/
noncomputable def poissonDirichletWeight (n : ℕ) (M : Measure ℝ) : ℝ :=
  (nthLargestAtom n M / ∑' l, nthLargestAtom l M).toReal

/-- `M ↦ vₙ(M)` is measurable for the Giry σ-algebra. -/
theorem measurable_poissonDirichletWeight (n : ℕ) : Measurable (poissonDirichletWeight n) :=
  ((measurable_nthLargestAtom n).div
    (Measurable.tsum measurable_nthLargestAtom)).ennreal_toReal

/-- The weights are nonincreasing: `v₀ ≥ v₁ ≥ …`. -/
theorem antitone_poissonDirichletWeight (M : Measure ℝ) :
    Antitone fun n => poissonDirichletWeight n M := by
  intro m n hmn
  have hle : nthLargestAtom m M ≤ ∑' l, nthLargestAtom l M :=
    ENNReal.le_tsum (f := fun l => nthLargestAtom l M) m
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    ((ENNReal.div_le_div_right hle _).trans ENNReal.div_self_le_one)) ?_
  exact ENNReal.div_le_div_right (antitone_nthLargestAtom M hmn) _

/-- If the total mass `∑ₗ uₗ` is positive and finite, the weights sum to `1`. -/
theorem hasSum_poissonDirichletWeight {M : Measure ℝ} (h0 : 0 < ∑' l, nthLargestAtom l M)
    (hT : ∑' l, nthLargestAtom l M < ∞) : HasSum (fun n => poissonDirichletWeight n M) 1 := by
  set T := ∑' l, nthLargestAtom l M with hTdef
  have h1 : ∑' n, nthLargestAtom n M / T = 1 := by
    simp_rw [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel h0.ne' hT.ne
  have hne : ∀ n, nthLargestAtom n M / T ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (h1 ▸ ENNReal.le_tsum (f := fun n => nthLargestAtom n M / T) n)
  have hsum := ENNReal.summable_toReal (f := fun n => nthLargestAtom n M / T)
    (h1 ▸ ENNReal.one_ne_top)
  have := hsum.hasSum
  rwa [← ENNReal.tsum_toReal_eq hne, h1, ENNReal.toReal_one] at this

/-- The intensity `ζ x ^ (-1 - ζ) dx` has infinite mass near `0`: the process has infinitely many
points. -/
theorem zetaPoissonMeasure_Ioi_zero {ζ : ℝ} (hζ : 0 < ζ) :
    zetaPoissonMeasure ζ (Ioi 0) = ∞ := by
  by_contra hne
  have h1 : zetaPoissonMeasure ζ (Ioi 0) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (ζ * x ^ (-1 - ζ)) := by
    rw [zetaPoissonMeasure, withDensity_apply _ measurableSet_Ioi]
    exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => by simp [mem_Ioi.1 hx]
  rw [h1] at hne
  have hm : AEStronglyMeasurable (fun x : ℝ => ζ * x ^ (-1 - ζ)) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Measurable fun x : ℝ => ζ * x ^ (-1 - ζ)).aestronglyMeasurable
  have hint : Integrable (fun x : ℝ => ζ * x ^ (-1 - ζ)) (volume.restrict (Ioi 0)) :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg hζ.le (Real.rpow_nonneg (le_of_lt hx) _)))).1 hne
  have hIoo : IntegrableOn (fun x : ℝ => x ^ (-1 - ζ)) (Ioo 0 1) := by
    have h2 : IntegrableOn (fun x : ℝ => ζ * x ^ (-1 - ζ)) (Ioo 0 1) :=
      hint.mono_measure (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)
    have h3 := h2.const_mul ζ⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hζ.ne', one_mul] at h3
    exact h3
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).1 hIoo
  linarith

section BlockModel

/-! ### The `ζ`-Poisson process built from independent blocks

Below, `M ω = poissonCountingMeasure (Nₙ ω) (Xₙₗ ω)` is the counting measure of independent blocks
`Bₙ = (Nₙ, (Xₙₗ)ₗ) ~ Po(rₙ) ⊗ νₙ^{⊗ℕ}` whose intensity `∑ₙ rₙ νₙ` is `zetaPoissonMeasure ζ`. -/

variable (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
  {B : ℕ → Ω → ℕ × (ℕ → ℝ)}

omit [IsProbabilityMeasure P] in
/-- The counting measure of measurable blocks is a measurable random measure. -/
theorem measurable_poissonCountingMeasure_of_blocks (hBm : ∀ n, Measurable (B n))
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)) :
    Measurable M := by
  have : M = fun ω => poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l) :=
    funext hM
  exact this ▸ measurable_poissonCountingMeasure_comp hBm

omit [IsProbabilityMeasure P] in
/-- Campbell's formula for the ζ-Poisson counting measure. -/
theorem lintegral_lintegral_zeta_of_blocks
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l))
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ) := by
  simp_rw [hM]
  rw [lintegral_poissonCountingMeasure ν r hlaw hf, ← hμ]

/-- **Lemma 2.1 for the block construction** (Panchenko, Eq. (2.15)). -/
theorem integral_poisson_sum_rpow_le_of_blocks {a : ℝ} (ha0 : 0 < a) (haζ : a < ζ) (hζ1 : ζ < 1)
    (hBm : ∀ n, Measurable (B n))
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)) :
    Integrable (fun ω => (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)).toReal ^ a) P ∧
      ∫ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)).toReal ^ a ∂P ≤
        1 + ζ / (1 - ζ) + ζ / (ζ - a) := by
  have hMm := measurable_poissonCountingMeasure_of_blocks hBm hM
  have hatom : ∀ ω, ∃ (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ), M ω = poissonCountingMeasure N X :=
    fun ω => ⟨_, _, hM ω⟩
  have hCamp := fun f (hf : Measurable f) => lintegral_lintegral_zeta_of_blocks ν r hlaw hμ hM hf
  exact ⟨integrable_poisson_sum_rpow ha0 haζ hζ1 hMm hatom hCamp,
    integral_poisson_sum_rpow_le ha0 haζ hζ1 hMm hatom hCamp⟩

/-- The total mass `∑_{x ∈ Π} x` of the block construction is finite almost surely. -/
theorem ae_lintegral_poisson_lt_top_of_blocks (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hBm : ∀ n, Measurable (B n))
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)) :
    ∀ᵐ ω ∂P, ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω) < ∞ :=
  ae_lintegral_poisson_lt_top hζ0 hζ1 (measurable_poissonCountingMeasure_of_blocks hBm hM)
    (fun ω => ⟨_, _, hM ω⟩) fun _ hf => lintegral_lintegral_zeta_of_blocks ν r hlaw hμ hM hf

/-- **`PD(ζ)` is well defined.** Almost surely, the atoms `u₀ > 0, u₁ > 0, …` of the ζ-Poisson
process are all positive, their sum `∑ₙ uₙ = ∑_{x ∈ Π} x` is finite, and so the weights
`vₙ = uₙ / ∑ₗ uₗ` are positive, nonincreasing and sum to one. -/
theorem ae_poissonDirichletWeight (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)) :
    ∀ᵐ ω ∂P, (∀ n, 0 < nthLargestAtom n (M ω)) ∧ ∑' n, nthLargestAtom n (M ω) < ∞ ∧
      HasSum (fun n => poissonDirichletWeight n (M ω)) 1 ∧
      (∀ n, 0 < poissonDirichletWeight n (M ω)) ∧
      Antitone fun n => poissonDirichletWeight n (M ω) := by
  -- the process has infinitely many points
  have hinf : ∀ᵐ ω ∂P, M ω (Ioi 0) = ∞ := by
    have hL := (iIndepFun_hasLaw_poissonCountingMeasure_apply (κ := Unit) ν r hBm hB hlaw hμ hM
      (A := fun _ => Ioi (0 : ℝ)) (fun _ => measurableSet_Ioi)
      (fun i j hij => absurd (Subsingleton.elim i j) hij)).1 ()
    simp only [zetaPoissonMeasure_Ioi_zero hζ0, ↓reduceIte] at hL
    have : ∀ᵐ y ∂(P.map fun ω => M ω (Ioi 0)), y = ∞ := by
      rw [hL.map_eq, ae_dirac_eq]; simp
    exact (ae_map_iff hL.aemeasurable (measurableSet_singleton ∞)).1 this
  filter_upwards [hinf, ae_lintegral_poisson_lt_top_of_blocks ν r hζ0 hζ1 hBm hlaw hμ hM]
    with ω hω hfin
  obtain ⟨N, X, hNX⟩ : ∃ (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ), M ω = poissonCountingMeasure N X :=
    ⟨_, _, hM ω⟩
  have hint : ∀ s : ℝ, 0 < s → M ω (Ioi s) = ⊤ ∨ ∃ m : ℕ, M ω (Ioi s) = m := fun s _ => by
    rw [hNX]; exact poissonCountingMeasure_apply_eq_top_or_natCast N X measurableSet_Ioi
  have hpos : ∀ n, 0 < nthLargestAtom n (M ω) := fun n => by
    have := (ofReal_lt_nthLargestAtom_iff (M := M ω) n le_rfl hint).2 (by rw [hω]; exact le_top)
    simpa using this
  have hsum := tsum_nthLargestAtom hint
  have hT0 : 0 < ∑' n, nthLargestAtom n (M ω) :=
    (hpos 0).trans_le (ENNReal.le_tsum (f := fun n => nthLargestAtom n (M ω)) 0)
  have hT : ∑' n, nthLargestAtom n (M ω) < ∞ := hsum ▸ hfin
  refine ⟨hpos, hT, hasSum_poissonDirichletWeight hT0 hT, fun n => ?_,
    antitone_poissonDirichletWeight (M ω)⟩
  refine ENNReal.toReal_pos ?_ ?_
  · exact (ENNReal.div_pos_iff.2 ⟨(hpos n).ne', hT.ne⟩).ne'
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((ENNReal.div_le_div_right
        (ENNReal.le_tsum (f := fun l => nthLargestAtom l (M ω)) n) _).trans
        ENNReal.div_self_le_one)

end BlockModel

/-- **Existence of `PD(ζ)`.** For `0 < ζ < 1` there is a probability space carrying independent
Poisson blocks whose counting measure is a Poisson process with intensity `ζ x ^ (-1 - ζ) dx`, and
almost surely the normalized decreasing atoms `vₙ` of that process are positive, nonincreasing and
sum to one. The law of `(vₙ)ₙ` on the simplex is `PD(ζ)`. -/
theorem exists_poissonDirichletWeight {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ P : Measure (ℕ → ℕ × (ℕ → ℝ)), IsProbabilityMeasure P ∧
      ∀ᵐ ω ∂P, HasSum (fun n => poissonDirichletWeight n
          (poissonCountingMeasure (fun k => (ω k).1) (fun k l => (ω k).2 l))) 1 ∧
        (∀ n, 0 < poissonDirichletWeight n
          (poissonCountingMeasure (fun k => (ω k).1) (fun k l => (ω k).2 l))) ∧
        Antitone fun n => poissonDirichletWeight n
          (poissonCountingMeasure (fun k => (ω k).1) (fun k l => (ω k).2 l)) := by
  obtain ⟨ν, r, hν, hμ⟩ :=
    exists_probabilityMeasure_sum_smul_eq_of_sigmaFinite (zetaPoissonMeasure ζ)
  obtain ⟨P, hP, hBm, hB, hlaw⟩ := exists_poissonBlocks ν r
  refine ⟨P, hP, ?_⟩
  filter_upwards [ae_poissonDirichletWeight (P := P) (B := fun n ω => ω n) ν r hζ0 hζ1 hBm hB
    hlaw hμ (M := fun ω => poissonCountingMeasure (fun k => (ω k).1) (fun k l => (ω k).2 l))
    (fun _ => rfl)] with ω h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end SpinGlasses
