/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.Symmetry
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.GaussianFields

/-!
# The first moment of the number of feasible configurations of the binary perceptron

Talagrand, *Spin Glasses* Vol. I, Section 2.1, Eqs. (2.1)-(2.2) and the paragraph after (2.2).
The disorder is `g : Fin M → Fin N → ℝ` with independent standard Gaussian entries, a spin
`σ : Fin N → ℤˣ` is *feasible* when `0 ≤ ∑ i, g k i * σ i` for every `k < M`, and
`C(g)` is the number of feasible spins, written as the cardinality of a `Finset.filter`.

For `N ≥ 1` a fixed spin is feasible with probability `(1 / 2) ^ M`, so
`𝔼 C = 2 ^ N / 2 ^ M`; Markov's inequality gives `ℙ(C ≥ 1) ≤ 2 ^ N / 2 ^ M`, which tends to zero
whenever `M(N) / N → α > 1`.  The powers are real powers of natural numbers, so the quotient is
right also for `M > N`.  For `N = 0` every field vanishes and the unique empty spin satisfies all
constraints, so the half-probability computation needs `N ≥ 1`.

This is the book's short first-moment argument; it does not locate the sharp threshold of
Research Problem 2.1.1.

## Main declarations

* `SpinGlasses.measureReal_feasible_configuration_eq`: `ℙ(σ feasible) = (1 / 2) ^ M`.
* `SpinGlasses.integral_card_feasible_configurations_eq`: `𝔼 C = 2 ^ N / 2 ^ M`.
* `SpinGlasses.measureReal_exists_feasible_configuration_le`: `ℙ(C ≥ 1) ≤ 2 ^ N / 2 ^ M`.
* `SpinGlasses.tendsto_measureReal_exists_feasible_configuration_zero`: the probability of a
  feasible configuration tends to zero when `M(N) / N → α > 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace SpinGlasses

variable {N M : ℕ}

/-- The event that a fixed spin satisfies every constraint is measurable. -/
theorem measurableSet_feasible_configuration (σ : Fin N → ℤˣ) :
    MeasurableSet {g : Fin M → Fin N → ℝ | ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun k => measurableSet_le measurable_const (by fun_prop)

/-- The number of feasible configurations is the sum over spins of the feasibility indicators. -/
theorem card_feasible_configurations_eq_sum_indicator (g : Fin M → Fin N → ℝ) :
    ((Finset.univ.filter fun σ : Fin N → ℤˣ => ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card : ℝ) =
      ∑ σ : Fin N → ℤˣ, Set.indicator
        {g : Fin M → Fin N → ℝ | ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)} (fun _ => (1 : ℝ)) g := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ) <;> simp [Set.indicator, h]

/-- The number of feasible configurations is measurable. -/
theorem measurable_card_feasible_configurations :
    Measurable fun g : Fin M → Fin N → ℝ =>
      ((Finset.univ.filter fun σ : Fin N → ℤˣ =>
        ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card : ℝ) := by
  simp only [card_feasible_configurations_eq_sum_indicator]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.indicator (measurableSet_feasible_configuration σ)

/-- **A fixed spin is feasible with probability `(1 / 2) ^ M`.**  The `M` fields of a fixed spin
are i.i.d. standard normal, each nonnegative with probability `1 / 2`.  Requires `N ≥ 1`. -/
theorem measureReal_feasible_configuration_eq (hN : 0 < N) (σ : Fin N → ℤˣ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).real
        {g | ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)} = (1 / 2) ^ M := by
  have hsqrt : 0 < (Real.sqrt N)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 hN))
  have hmeas : Measurable fun (g : Fin M → Fin N → ℝ) (k : Fin M) =>
      (Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ) := by fun_prop
  have hset : {g : Fin M → Fin N → ℝ | ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)} =
      (fun (g : Fin M → Fin N → ℝ) (k : Fin M) =>
        (Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ i : ℤ) : ℝ)) ⁻¹' Set.univ.pi fun _ => Set.Ici 0 := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ici]
    exact forall_congr' fun k => (mul_nonneg_iff_of_pos_left hsqrt).symm
  rw [measureReal_def, hset, ← Measure.map_apply hmeas (MeasurableSet.univ_pi fun _ =>
    measurableSet_Ici), map_normalized_constraint_fields_eq_pi_gaussianReal hN (fun _ => σ),
    Measure.pi_pi]
  simp only [gaussianReal_Ici_zero one_ne_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.toReal_pow, one_div, ENNReal.toReal_inv]
  simp

/-- **Expected number of feasible configurations**, Eq. (2.2): `𝔼 C = 2 ^ N / 2 ^ M`, with real
powers of natural exponents (so that the quotient is correct for `M > N` too).  Requires
`N ≥ 1`; `M = 0` is allowed. -/
theorem integral_card_feasible_configurations_eq (hN : 0 < N) :
    ∫ g : Fin M → Fin N → ℝ,
        ((Finset.univ.filter fun σ : Fin N → ℤˣ =>
          ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card : ℝ)
        ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (2 : ℝ) ^ N / (2 : ℝ) ^ M := by
  simp only [card_feasible_configurations_eq_sum_indicator]
  rw [integral_finset_sum _ fun σ _ => (integrable_const (1 : ℝ)).indicator
    (measurableSet_feasible_configuration σ)]
  have h : ∀ σ : Fin N → ℤˣ, ∫ g : Fin M → Fin N → ℝ, Set.indicator
      {g : Fin M → Fin N → ℝ | ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)} (fun _ => (1 : ℝ)) g
      ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (1 / 2) ^ M := fun σ => by
    rw [integral_indicator_const _ (measurableSet_feasible_configuration σ), smul_eq_mul,
      mul_one]
    exact measureReal_feasible_configuration_eq hN σ
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_fun, Fintype.card_units_int, Fintype.card_fin]
  push_cast
  rw [one_div, inv_pow, div_eq_mul_inv]

/-- **Markov bound for the existence of a feasible configuration:**
`ℙ(∃ σ feasible) ≤ 2 ^ N / 2 ^ M`.  Requires `N ≥ 1`. -/
theorem measureReal_exists_feasible_configuration_le (hN : 0 < N) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).real
        {g | ∃ σ : Fin N → ℤˣ, ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)} ≤
      (2 : ℝ) ^ N / (2 : ℝ) ^ M := by
  have hint : Integrable (fun g : Fin M → Fin N → ℝ =>
      ((Finset.univ.filter fun σ : Fin N → ℤˣ =>
        ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)).card : ℝ))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
    simp only [card_feasible_configurations_eq_sum_indicator]
    exact integrable_finset_sum _ fun σ _ => (integrable_const (1 : ℝ)).indicator
      (measurableSet_feasible_configuration σ)
  have h := hint.measure_le_integral (ae_of_all _ fun g => Nat.cast_nonneg _)
    (s := {g | ∃ σ : Fin N → ℤˣ, ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)}) (by
      rintro g ⟨σ, hσ⟩
      exact Nat.one_le_cast.2 (Finset.card_pos.2 ⟨σ, by simpa using hσ⟩))
  rw [integral_card_feasible_configurations_eq hN] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- **No feasible configuration above the first-moment threshold** (the paragraph after (2.2)):
if `M(N) / N → α > 1`, the probability that some spin satisfies all `M(N)` constraints tends to
zero.  Each probability is taken under its own finite-dimensional disorder law. -/
theorem tendsto_measureReal_exists_feasible_configuration_zero {M : ℕ → ℕ} {α : ℝ} (hα : 1 < α)
    (hM : Tendsto (fun N => (M N : ℝ) / N) atTop (𝓝 α)) :
    Tendsto (fun N => (Measure.pi fun _ : Fin (M N) =>
        Measure.pi fun _ : Fin N => gaussianReal 0 1).real
        {g | ∃ σ : Fin N → ℤˣ, ∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)}) atTop (𝓝 0) := by
  set θ : ℝ := (α - 1) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have h2θ : 1 < (2 : ℝ) ^ θ := Real.one_lt_rpow one_lt_two hθ0
  have hr : ((2 : ℝ) ^ θ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2θ
  have hr0 : 0 ≤ ((2 : ℝ) ^ θ)⁻¹ := by positivity
  have hev : ∀ᶠ N : ℕ in atTop, 0 < N ∧ (1 + θ) * N ≤ M N := by
    filter_upwards [eventually_gt_atTop 0, hM.eventually (lt_mem_nhds (a := 1 + θ)
      (by rw [hθ]; linarith))] with N hN hlt
    refine ⟨hN, ?_⟩
    have := (lt_div_iff₀ (Nat.cast_pos.2 hN)).1 hlt
    exact this.le
  refine squeeze_zero' (Eventually.of_forall fun N => measureReal_nonneg) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr)
  filter_upwards [hev] with N ⟨hN, hMN⟩
  refine (measureReal_exists_feasible_configuration_le hN).trans ?_
  have h1 : (2 : ℝ) ^ ((1 + θ) * N) ≤ (2 : ℝ) ^ (M N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two hMN
  have h2 : (2 : ℝ) ^ ((1 + θ) * N) = (2 : ℝ) ^ N * ((2 : ℝ) ^ θ) ^ N := by
    rw [add_mul, one_mul, Real.rpow_add two_pos, Real.rpow_natCast,
      mul_comm θ, Real.rpow_mul two_pos.le, Real.rpow_natCast]
  rw [Real.rpow_natCast] at h1
  rw [h2] at h1
  rw [inv_pow, div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  have : (0 : ℝ) < (2 : ℝ) ^ N * ((2 : ℝ) ^ θ) ^ N := by positivity
  calc (2 : ℝ) ^ N = (2 : ℝ) ^ N * ((2 : ℝ) ^ θ) ^ N * (((2 : ℝ) ^ θ) ^ N)⁻¹ := by
        field_simp
    _ ≤ _ := by gcongr

end SpinGlasses
