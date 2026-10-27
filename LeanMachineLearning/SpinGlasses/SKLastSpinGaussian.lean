/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Function.UnitVectorField
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.MapProdFiberLaw
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.SpinGlasses.SKFixedPointPositive
public import LeanMachineLearning.SpinGlasses.SKLastSpinApprox
public import LeanMachineLearning.SpinGlasses.SKOldSpinCavity

/-!
# The last spin is a function of an independent standard Gaussian (Talagrand, Lemma 1.7.6)

For `0 ≤ β ≤ β₀`, `4 β₀² < 1` and the fixed point `q = 𝔼 tanh²(β √q z + h)` there is a standard
Gaussian `z`, a measurable function of the couplings of the `(N+1)`-spin system and independent
of the couplings of the first `N` spins, with
`𝔼 (⟨σ_{N+1}⟩ - tanh(β √q z + h))² ≤ K / (N+1)` (`SpinGlasses.sk_last_spin_gaussian_approx`).

The Gaussian is the renormalized cavity field `z = A⁻¹ ∑ y_i ⟨σ_i⟩_-`, `A² = ∑ ⟨σ_i⟩_-²`.  The
model-independent part (`exists_independent_gaussian_projection`) is stated for any measurable
vector `m` of the old couplings and any measure preserving split of the disorder.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.7.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace SpinGlasses

section Projection

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {N : ℕ}

/-- **A standard Gaussian independent of the old couplings.**  Let the disorder of `Ω` split
measure-preservingly (`e`) into old couplings `ω'` and an independent standard Gaussian vector
`y ∈ ℝ^N`, and let `m` be a measurable vector of the old couplings.  Then
`Z (ω', y) = u(ω') ⬝ᵥ y` with the unit direction `u = m / ‖m‖` is, for every `ω'`, a standard
Gaussian in `y`, so `Z ∘ e` is a standard Gaussian independent of the old couplings; and for all
`c, t` the `y`-average `𝔼_y (c m ⬝ᵥ y - t Z)² = (c ‖m‖ - t)²` (the first step of Talagrand's
Eq. (1.188)). -/
theorem exists_independent_gaussian_projection (hN : 0 < N)
    {e : Ω → Ω' × (Fin N → ℝ)}
    (he : MeasurePreserving e P (P'.prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)))
    {m : Ω' → Fin N → ℝ} (hm : ∀ i, Measurable fun ω' => m ω' i) :
    ∃ Z : Ω' × (Fin N → ℝ) → ℝ, Measurable Z ∧
      IndepFun (fun ω => Z (e ω)) (fun ω => (e ω).1) P ∧
      P.map (fun ω => Z (e ω)) = gaussianReal 0 1 ∧
      (∀ (c t : ℝ) (ω' : Ω'),
        Integrable (fun y : Fin N → ℝ => (c * (m ω' ⬝ᵥ y) - t * Z (ω', y)) ^ 2)
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
      ∀ (c t : ℝ) (ω' : Ω'), ∫ y : Fin N → ℝ, (c * (m ω' ⬝ᵥ y) - t * Z (ω', y)) ^ 2
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
          (c * Real.sqrt (m ω' ⬝ᵥ m ω') - t) ^ 2 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨u, hu, hu1, hmu⟩ := exists_measurable_unit_field hm
  have hZ : Measurable fun w : Ω' × (Fin N → ℝ) => u w.1 ⬝ᵥ w.2 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ =>
      ((hu i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)
  have hfib : ∀ ω' : Ω', (Measure.pi fun _ : Fin N => gaussianReal 0 1).map
      (fun y => u ω' ⬝ᵥ y) = gaussianReal 0 1 := fun ω' =>
    map_dotProduct_pi_gaussianReal_of_dotProduct_self (hu1 ω')
  obtain ⟨hind, hlaw⟩ := indepFun_fst_comp_of_measurePreserving he hZ (ae_of_all _ hfib)
  have hlin : ∀ (c t : ℝ) (ω' : Ω') (y : Fin N → ℝ),
      c * (m ω' ⬝ᵥ y) - t * (u ω' ⬝ᵥ y) =
        (c * Real.sqrt (m ω' ⬝ᵥ m ω') - t) * (u ω' ⬝ᵥ y) := fun c t ω' y => by
    conv_lhs => rw [hmu ω']
    simp only [smul_dotProduct, smul_eq_mul]
    ring
  refine ⟨fun w => u w.1 ⬝ᵥ w.2, hZ, hind.symm, hlaw, fun c t ω' => ?_, fun c t ω' => ?_⟩
  · simp_rw [hlin]
    exact ((memLp_dotProduct_pi_gaussianReal (u ω')).integrable_sq.const_mul
      ((c * Real.sqrt (m ω' ⬝ᵥ m ω') - t) ^ 2)).congr
      (Filter.Eventually.of_forall fun y => by simp [mul_pow])
  · simp_rw [hlin, mul_pow, sq (u ω' ⬝ᵥ _)]
    rw [integral_const_mul, integral_dotProduct_mul_dotProduct_pi_gaussianReal, hu1, mul_one]

end Projection

section Algebra

/-- **Recentering the overlap** with the fixed-point shift: if `|q - q_-| ≤ ε ≤ 1`, `q ∈ [0, 1]`
then `(q - (1 - ε) R)² ≤ 4 (R - q_-)² + 6 ε²`. -/
theorem sq_sub_mul_le {q qm R ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hqm : |q - qm| ≤ ε) : (q - (1 - ε) * R) ^ 2 ≤ 4 * (R - qm) ^ 2 + 6 * ε ^ 2 := by
  have hd : (q - qm) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hqm 2
  have h1 : (q - R) ^ 2 ≤ 2 * (R - qm) ^ 2 + 2 * ε ^ 2 := by
    nlinarith [sq_nonneg ((qm - R) - (q - qm))]
  have h2 : ((1 - ε) * (q - R)) ^ 2 ≤ (q - R) ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (by linarith) (by linarith))
  have h3 : (ε * q) ^ 2 ≤ ε ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hq.1 hq.2)
  have h4 : q - (1 - ε) * R = (1 - ε) * (q - R) + ε * q := by ring
  rw [h4]
  nlinarith [sq_nonneg ((1 - ε) * (q - R) - ε * q)]

end Algebra

/-- With no external field, a spin has Gibbs mean zero (the Hamiltonian is even). -/
theorem integral_spin_eq_zero_of_field_zero (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ) (i : Fin N) :
    ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β 0 g)) = 0 := by
  have hE : ∀ σ : Fin N → ℤˣ, skGibbsEnergy N β 0 g (-σ) = skGibbsEnergy N β 0 g σ :=
    fun σ => by simp [skGibbsEnergy]
  have h := integral_count_tilted_equiv (Equiv.neg (Fin N → ℤˣ)) (skGibbsEnergy N β 0 g)
    (fun σ => ((σ i : ℤ) : ℝ))
  have hf : (fun a : Fin N → ℤˣ => skGibbsEnergy N β 0 g (Equiv.neg (Fin N → ℤˣ) a)) =
      skGibbsEnergy N β 0 g := funext fun a => hE a
  rw [hf] at h
  simp only [Equiv.neg_apply, Pi.neg_apply, Units.val_neg, Int.cast_neg, integral_neg] at h
  linarith

/-- **The fixed point of the cavity system** (Lemma 1.7.5 in the `(N+1)`-spin indexing).  For
`0 ≤ β`, `4 β² < 1` and a fixed point `q` at `β`, the `N`-spin system at
`β_- = β √(N/(N+1))` has a fixed point `q_-` with `|q - q_-| ≤ 1/(N+1)`. -/
theorem exists_fixedPoint_cavity {β : ℝ} (h q : ℝ) (hβ0 : 0 ≤ β) (hβ4 : 4 * β ^ 2 < 1)
    (hq : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    {N : ℕ} :
    ∃ qm : ℝ, qm ∈ Set.Icc (0 : ℝ) 1 ∧
      ∫ x : ℝ, Real.tanh (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm * x + h) ^ 2
        ∂(gaussianReal 0 1) = qm ∧ |q - qm| ≤ 1 / ((N : ℝ) + 1) := by
  obtain ⟨qm, hqmI, hqm⟩ := exists_fixedPoint (β * Real.sqrt ((N : ℝ) / (N + 1))) h
  refine ⟨qm, hqmI, hqm.symm, ?_⟩
  have := sk_fixed_point_shift_le (N := N + 1) (Nat.succ_pos N) β h q qm hβ0 hβ4 hq (by
    rw [one_sub_inv_succ_eq_div]; exact hqm.symm)
  simpa using this

/-- A Gibbs mean of a spin of the SK system is measurable in the couplings. -/
theorem measurable_integral_spin_skGibbsEnergy (N : ℕ) (β h : ℝ) (i : Fin N) :
    Measurable fun g : FinPairs N → ℝ =>
      ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)) :=
  measurable_integral_count_tilted (fun g a => skGibbsEnergy N β h g a)
    (measurable_skGibbsEnergy N β h) _

/-- **The renormalization defect of the old magnetizations** (Eq. (1.189)).  With
`R̄ = N⁻¹ ∑_i ⟨σ_i⟩_-²` the mean overlap of the `N`-spin system at `β_- = β √(N/(N+1))`, the
quantity `q - (N/(N+1)) R̄` has a dominating integrable function `B` of the old couplings with
`∫ B ≤ K / (N+1)`; `q` is the fixed point at `β` and `K` depends on `β₀` only. -/
theorem sk_old_overlap_dev_bound (β₀ : ℝ) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ N : ℕ, 0 < N → ∃ B : (FinPairs N → ℝ) → ℝ,
        Integrable B (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
        ∫ g, B g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / ((N : ℝ) + 1) ∧
        ∀ g : FinPairs N → ℝ, (q - (N : ℝ) / ((N : ℝ) + 1) * ((N : ℝ)⁻¹ * ∑ i : Fin N,
          (∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted
            (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g))) ^ 2)) ^ 2 ≤ B g := by
  obtain ⟨K', hK'0, hK'⟩ := sk_overlap_moment_le_of_exp_unif β₀ hβ₀' 1
  refine ⟨8 * K' + 6, by positivity, fun β hβ0 hββ₀ q hq N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hβ2 : β ^ 2 ≤ β₀ ^ 2 := pow_le_pow_left₀ hβ0 hββ₀ 2
  have hβ4 : 4 * β ^ 2 < 1 := by linarith
  have hs : Real.sqrt ((N : ℝ) / (N + 1)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one (by positivity)).mpr (by linarith))
  have hbm2 : (β * Real.sqrt ((N : ℝ) / (N + 1))) ^ 2 ≤ β₀ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc β ^ 2 * ((N : ℝ) / (N + 1)) ≤ β ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr (by linarith)) (sq_nonneg _)
      _ ≤ β₀ ^ 2 := by rw [mul_one]; exact hβ2
  obtain ⟨qm, hqmI, hqm, hshift⟩ := exists_fixedPoint_cavity (N := N) h q hβ0 hβ4 hq
  have hOM : ∫ g, overlapMoment (fun (j : Fin N) (a : Fin N → ℤˣ) => ((a j : ℤ) : ℝ))
      (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g) qm 1
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K' / N := by
    have := hK' _ h qm hqm hbm2 N hN
    rw [pow_one] at this
    exact this
  have hint := integrable_overlapMoment_skGibbsEnergy N
    (β * Real.sqrt ((N : ℝ) / (N + 1))) h qm 1
  refine ⟨fun g => 4 * overlapMoment (fun (j : Fin N) (a : Fin N → ℤˣ) => ((a j : ℤ) : ℝ))
    (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g) qm 1 +
      6 * (1 / ((N : ℝ) + 1)) ^ 2, (hint.const_mul 4).add (integrable_const _), ?_, fun g => ?_⟩
  · rw [integral_add (hint.const_mul 4) (integrable_const _), integral_const_mul,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have h1 : K' / N ≤ 2 * K' / ((N : ℝ) + 1) := by
      rw [div_le_div_iff₀ hN0 (by positivity)]
      nlinarith
    have h2 : 6 * (1 / ((N : ℝ) + 1)) ^ 2 ≤ 6 / ((N : ℝ) + 1) := by
      have hp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) hp]
      nlinarith
    calc 4 * ∫ g, overlapMoment (fun (j : Fin N) (a : Fin N → ℤˣ) => ((a j : ℤ) : ℝ))
          (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g) qm 1
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) +
          6 * (1 / ((N : ℝ) + 1)) ^ 2
        ≤ 4 * (K' / N) + 6 / ((N : ℝ) + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left hOM (by norm_num)) h2
      _ ≤ 4 * (2 * K' / ((N : ℝ) + 1)) + 6 / ((N : ℝ) + 1) := by gcongr
      _ = (8 * K' + 6) / ((N : ℝ) + 1) := by ring
  · have hJ := sq_meanOverlap_sub_le_overlapMoment
      (fun (j : Fin N) (a : Fin N → ℤˣ) => ((a j : ℤ) : ℝ))
      (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g) qm
    have hε : (N : ℝ) / ((N : ℝ) + 1) = 1 - 1 / ((N : ℝ) + 1) := by
      field_simp; ring
    have hε1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have := sq_sub_mul_le (by positivity) hε1 (fixedPoint_mem_Icc hq) hshift
      (R := (N : ℝ)⁻¹ * ∑ i : Fin N, (∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted
        (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g))) ^ 2)
    rw [← hε] at this
    beta_reduce
    linarith

/-- The square of a difference of two measurable functions bounded by `1` is integrable. -/
theorem integrable_sq_sub_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    (ha1 : ∀ ω, |a ω| ≤ 1) (hb1 : ∀ ω, |b ω| ≤ 1) :
    Integrable (fun ω => (a ω - b ω) ^ 2) μ :=
  integrable_sq_of_abs_le (ha.sub hb) (C := 2) fun ω =>
    (abs_sub _ _).trans (by linarith [ha1 ω, hb1 ω])

/-- **The cavity field against the renormalized Gaussian** (Eq. (1.188) and what follows).
For `h ≠ 0`, if `m` is the vector of old magnetizations `⟨σ_i⟩_-` and `Z` is a projection with
`𝔼_y (c m ⬝ᵥ y - t Z)² = (c ‖m‖ - t)²`, then
`𝔼 (tanh(β (N+1)^{-1/2} m ⬝ᵥ y + h) - tanh(β √q Z + h))² ≤ K / (N+1)`, with `K` depending on
`β₀` and `h` only. -/
theorem sk_cavity_tanh_gaussian_sub_le (β₀ : ℝ) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ) (hh : h ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ N : ℕ, 0 < N → ∀ (Z : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ)
        (m : (FinPairs N → ℝ) → Fin N → ℝ),
      (∀ g i, m g i = ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted
        (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g))) →
      (∀ (c t : ℝ) (g : FinPairs N → ℝ), Integrable
        (fun y : Fin N → ℝ => (c * (m g ⬝ᵥ y) - t * Z (g, y)) ^ 2)
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) →
      (∀ (c t : ℝ) (g : FinPairs N → ℝ), ∫ y : Fin N → ℝ, (c * (m g ⬝ᵥ y) - t * Z (g, y)) ^ 2
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
          (c * Real.sqrt (m g ⬝ᵥ m g) - t) ^ 2) →
      ∫ g : FinPairs (N + 1) → ℝ, (Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
          ∑ i : Fin N, (skCavityDisorderEquiv N g).2 i * m (skCavityDisorderEquiv N g).1 i + h) -
        Real.tanh (β * Real.sqrt q * Z (skCavityDisorderEquiv N g) + h)) ^ 2
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ K / ((N : ℝ) + 1) := by
  obtain ⟨K₂, hK₂0, hK₂⟩ := sk_old_overlap_dev_bound β₀ hβ₀' h
  set qmin : ℝ := (Real.sinh (2 * |h|) / (Real.cosh (2 * h) + Real.exp (1 / 2))) ^ 2 with hqmin
  have hqminpos : 0 < qmin := by
    have h1 : 0 < Real.sinh (2 * |h|) :=
      Real.sinh_pos_iff.mpr (by have := abs_pos.mpr hh; linarith)
    have h2 := Real.cosh_pos (2 * h)
    have h3 := Real.exp_pos (1 / 2)
    positivity
  refine ⟨β₀ ^ 2 / qmin * K₂ + 1, by positivity, fun β hβ0 hββ₀ q hq N hN Z m hm hZi hZ => ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨B, hBint, hBle, hBpt⟩ := hK₂ β hβ0 hββ₀ q hq N hN
  have hβ2 : β ^ 2 ≤ β₀ ^ 2 := pow_le_pow_left₀ hβ0 hββ₀ 2
  have hβ4 : 4 * β ^ 2 < 1 := by linarith
  have hqle : qmin ≤ q := fixedPoint_lower_bound hβ4 hq hh
  have hqpos : 0 < q := lt_of_lt_of_le hqminpos hqle
  set c : ℝ := (Real.sqrt ((N : ℝ) + 1))⁻¹ with hc
  have hc2 : c ^ 2 = 1 / ((N : ℝ) + 1) := by
    rw [hc, inv_pow, Real.sq_sqrt (by positivity)]; ring
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨F2, hF2⟩ : ∃ F2 : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ, ∀ w, F2 w =
      (Real.tanh (c * β * ∑ i : Fin N, w.2 i * m w.1 i + h) -
        Real.tanh (β * Real.sqrt q * Z w + h)) ^ 2 := ⟨_, fun _ => rfl⟩
  have hpt : ∀ g : FinPairs N → ℝ, ∫ y, F2 (g, y) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
      ≤ β₀ ^ 2 / qmin * B g := fun g => by
    have hLip : ∀ y : Fin N → ℝ, F2 (g, y) ≤
        β ^ 2 * (c * (m g ⬝ᵥ y) - Real.sqrt q * Z (g, y)) ^ 2 := fun y => by
      rw [hF2]
      have hdot : ∑ i : Fin N, y i * m g i = m g ⬝ᵥ y := by simp [dotProduct, mul_comm]
      have h1 := Real.abs_tanh_sub_tanh_le (c * β * ∑ i : Fin N, y i * m g i + h)
        (β * Real.sqrt q * Z (g, y) + h)
      have h2 : (c * β * ∑ i : Fin N, y i * m g i + h) - (β * Real.sqrt q * Z (g, y) + h) =
          β * (c * (m g ⬝ᵥ y) - Real.sqrt q * Z (g, y)) := by rw [hdot]; ring
      rw [h2] at h1
      calc _ ≤ (β * (c * (m g ⬝ᵥ y) - Real.sqrt q * Z (g, y))) ^ 2 :=
            sq_le_sq.mpr (by simpa using h1)
        _ = _ := by ring
    have hS : m g ⬝ᵥ m g = ∑ i : Fin N, (∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted
        (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g))) ^ 2 := by
      simp [dotProduct, hm, sq]
    have hA : (c * Real.sqrt (m g ⬝ᵥ m g)) ^ 2 = (N : ℝ) / ((N : ℝ) + 1) * ((N : ℝ)⁻¹ * ∑ i : Fin N,
        (∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted
          (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g))) ^ 2) := by
      rw [mul_pow, hc2, Real.sq_sqrt (by rw [hS]; exact Finset.sum_nonneg fun i _ => sq_nonneg _),
        hS]
      field_simp
    have hB' : (q - (c * Real.sqrt (m g ⬝ᵥ m g)) ^ 2) ^ 2 ≤ B g := by rw [hA]; exact hBpt g
    have hB0 : 0 ≤ B g := le_trans (sq_nonneg _) hB'
    have ha0 : 0 ≤ c * Real.sqrt (m g ⬝ᵥ m g) := mul_nonneg hc0 (Real.sqrt_nonneg _)
    calc ∫ y, F2 (g, y) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ≤ ∫ y, β ^ 2 * (c * (m g ⬝ᵥ y) - Real.sqrt q * Z (g, y)) ^ 2
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
          integral_mono_of_nonneg (ae_of_all _ fun y => by
              change 0 ≤ F2 (g, y)
              rw [hF2]; exact sq_nonneg _)
            ((hZi c (Real.sqrt q) g).const_mul _) (ae_of_all _ hLip)
      _ = β ^ 2 * (c * Real.sqrt (m g ⬝ᵥ m g) - Real.sqrt q) ^ 2 := by
          rw [integral_const_mul, hZ]
      _ ≤ β ^ 2 * ((q - (c * Real.sqrt (m g ⬝ᵥ m g)) ^ 2) ^ 2 / q) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          rw [← neg_sub, neg_sq]
          exact Real.sq_sqrt_sub_le hqpos ha0
      _ ≤ β₀ ^ 2 * (B g / qmin) :=
          mul_le_mul hβ2 (div_le_div₀ hB0 hB' hqminpos hqle) (by positivity) (sq_nonneg _)
      _ = β₀ ^ 2 / qmin * B g := by ring
  calc _ = ∫ w, F2 w ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
        rw [← (measurePreserving_skCavityDisorderEquiv N).integral_comp' F2]
        simp only [hF2, hc]
    _ ≤ ∫ g, ∫ y, F2 (g, y) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
        integral_prod_le_integral_integral_of_nonneg fun w => by rw [hF2]; exact sq_nonneg _
    _ ≤ ∫ g, β₀ ^ 2 / qmin * B g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
        integral_mono_of_nonneg
          (ae_of_all _ fun g => integral_nonneg fun y => by rw [hF2]; exact sq_nonneg _)
          (hBint.const_mul _) (ae_of_all _ hpt)
    _ = β₀ ^ 2 / qmin * ∫ g, B g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
        integral_const_mul _ _
    _ ≤ β₀ ^ 2 / qmin * (K₂ / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hBle (by positivity)
    _ ≤ (β₀ ^ 2 / qmin * K₂ + 1) / ((N : ℝ) + 1) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **The renormalized cavity Gaussian of the `(N+1)`-spin system** (Talagrand's
`z = A⁻¹ ∑_i g_i ⟨σ_i⟩_-`): with `m g' i = ⟨σ_i⟩_-` the old magnetizations at
`β_- = β √(N/(N+1))`, there is a projection `Z` of (old couplings, new edges) such that `Z ∘ e` is
a standard Gaussian independent of the old couplings, with the `y`-average of Eq. (1.188). -/
theorem exists_sk_cavity_gaussian (β h : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ (m : (FinPairs N → ℝ) → Fin N → ℝ) (Z : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ),
      (∀ g i, m g i = ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted
        (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g))) ∧
      (∀ i, Measurable fun g => m g i) ∧ Measurable Z ∧
      IndepFun (fun g => Z (skCavityDisorderEquiv N g)) (fun g => (skCavityDisorderEquiv N g).1)
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ∧
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).map
        (fun g => Z (skCavityDisorderEquiv N g)) = gaussianReal 0 1 ∧
      (∀ (c t : ℝ) (g : FinPairs N → ℝ), Integrable
        (fun y : Fin N → ℝ => (c * (m g ⬝ᵥ y) - t * Z (g, y)) ^ 2)
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
      (∀ (c t : ℝ) (g : FinPairs N → ℝ), ∫ y : Fin N → ℝ, (c * (m g ⬝ᵥ y) - t * Z (g, y)) ^ 2
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
          (c * Real.sqrt (m g ⬝ᵥ m g) - t) ^ 2) := by
  obtain ⟨m, hm⟩ : ∃ m : (FinPairs N → ℝ) → Fin N → ℝ, ∀ g i, m g i = ∫ b, ((b i : ℤ) : ℝ)
      ∂(Measure.count.tilted (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g)) :=
    ⟨fun g i => _, fun _ _ => rfl⟩
  have hmeas : ∀ i, Measurable fun g => m g i := fun i => by
    simp_rw [hm]
    exact measurable_integral_spin_skGibbsEnergy N _ h i
  obtain ⟨Z, hZ, hind, hlaw, hZi, hZint⟩ := exists_independent_gaussian_projection hN
    (measurePreserving_skCavityDisorderEquiv N) hmeas
  exact ⟨m, Z, hm, hmeas, hZ, hind, hlaw, hZi, hZint⟩

/-- `∫ x² dγ = 1` for the standard Gaussian. -/
theorem integral_sq_gaussianReal_zero_one : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h2 := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral (X := id) measurable_id'.aemeasurable] at h2
  simpa [id] using h2

/-- With no external field the fixed point vanishes. -/
theorem fixedPoint_eq_zero_of_field_zero {β q : ℝ} (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + 0) ^ 2 ∂(gaussianReal 0 1) = q) :
    q = 0 := by
  have hq := fixedPoint_mem_Icc hfix
  have hint : Integrable (fun x : ℝ => (β * Real.sqrt q * x) ^ 2) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 2).integrable_sq.const_mul ((β * Real.sqrt q) ^ 2)).congr
      (Filter.Eventually.of_forall fun x => by simp [mul_pow])
  have h1 : q ≤ β ^ 2 * q := by
    calc q = ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + 0) ^ 2 ∂(gaussianReal 0 1) := hfix.symm
      _ ≤ ∫ x : ℝ, (β * Real.sqrt q * x) ^ 2 ∂(gaussianReal 0 1) :=
          integral_mono (integrable_tanh_sq_affine _ _) hint fun x => by
            rw [add_zero]
            exact sq_le_sq.mpr (by simpa using Real.abs_tanh_le_abs (β * Real.sqrt q * x))
      _ = β ^ 2 * q := by
          simp_rw [mul_pow]
          rw [integral_const_mul, integral_sq_gaussianReal_zero_one, mul_one, Real.sq_sqrt hq.1]
  nlinarith [hq.1, sq_nonneg β]

/-- **Lemma 1.7.6 (Talagrand).**  Let `0 ≤ β ≤ β₀`, `4 β₀² < 1` and let `q` solve the fixed-point
equation (1.74).  For the `(N+1)`-spin SK system there is a standard Gaussian `z`, a measurable
function of all couplings that is independent of the couplings among the first `N` spins, with
`𝔼 (⟨σ_{N+1}⟩ - tanh(β z √q + h))² ≤ K / (N+1)`.  The constant `K` depends on `β₀` and `h` only
(it degenerates as `h → 0`, as the book remarks); for `h = 0` one has `q = 0` and the bound is
trivial.  Here `⟨σ_{N+1}⟩` is the Gibbs mean of the last spin. -/
theorem sk_last_spin_gaussian_approx (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ N : ℕ, 0 < N → ∃ z : (FinPairs (N + 1) → ℝ) → ℝ, Measurable z ∧
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).map z = gaussianReal 0 1 ∧
        IndepFun z (fun g => (skCavityDisorderEquiv N g).1)
          (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ∧
        ∫ g : FinPairs (N + 1) → ℝ,
          (∫ σ, ((σ (Fin.last N) : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) -
            Real.tanh (β * Real.sqrt q * z g + h)) ^ 2
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ K / ((N : ℝ) + 1) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := sk_last_spin_tanh_approx β₀ hβ₀ hβ₀' h
  by_cases hh : h = 0
  · refine ⟨1, one_pos, fun β hβ0 hββ₀ q hq N hN => ?_⟩
    subst hh
    obtain ⟨m, Z, -, -, hZ, hind, hlaw, -, -⟩ := exists_sk_cavity_gaussian β 0 hN
    have hβ4 : 4 * β ^ 2 < 1 := by nlinarith [pow_le_pow_left₀ hβ0 hββ₀ 2]
    have hq0 := fixedPoint_eq_zero_of_field_zero hβ4 hq
    refine ⟨fun g => Z (skCavityDisorderEquiv N g), hZ.comp (skCavityDisorderEquiv N).measurable,
      hlaw, hind, ?_⟩
    simp only [hq0, integral_spin_eq_zero_of_field_zero, Real.sqrt_zero, mul_zero, zero_mul,
      add_zero, Real.tanh_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, integral_zero]
    positivity
  obtain ⟨K₃, hK₃0, hK₃⟩ := sk_cavity_tanh_gaussian_sub_le β₀ hβ₀' h hh
  refine ⟨2 * K₁ + 2 * K₃, by positivity, fun β hβ0 hββ₀ q hq N hN => ?_⟩
  obtain ⟨m, Z, hm, hmm, hZ, hind, hlaw, hZi, hZint⟩ := exists_sk_cavity_gaussian β h hN
  have hem := (skCavityDisorderEquiv N).measurable
  refine ⟨fun g => Z (skCavityDisorderEquiv N g), hZ.comp hem, hlaw, hind, ?_⟩
  have h2 := hK₃ β hβ0 hββ₀ q hq N hN Z m hm hZi hZint
  have h1 := hK₁ β (by rw [abs_of_nonneg hβ0]; exact hββ₀) N hN
  obtain ⟨X, hX⟩ : ∃ X : (FinPairs (N + 1) → ℝ) → ℝ, ∀ g, X g =
      ∫ σ, ((σ (Fin.last N) : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) :=
    ⟨fun g => _, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (FinPairs (N + 1) → ℝ) → ℝ, ∀ g, T g =
      Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
        ∑ i : Fin N, (skCavityDisorderEquiv N g).2 i * m (skCavityDisorderEquiv N g).1 i + h) :=
    ⟨fun g => _, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : (FinPairs (N + 1) → ℝ) → ℝ, ∀ g, W g =
      Real.tanh (β * Real.sqrt q * Z (skCavityDisorderEquiv N g) + h) :=
    ⟨fun g => _, fun _ => rfl⟩
  have h1' : ∫ g, (X g - T g) ^ 2 ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
      K₁ / ((N : ℝ) + 1) := by
    simpa only [hX, hT, hm] using h1
  have h2' : ∫ g, (T g - W g) ^ 2 ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
      K₃ / ((N : ℝ) + 1) := by
    simpa only [hT, hW] using h2
  have hXm : Measurable X := by
    rw [show X = fun g => ∫ σ, ((σ (Fin.last N) : ℤ) : ℝ)
      ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) from funext hX]
    exact measurable_integral_spin_skGibbsEnergy (N + 1) β h (Fin.last N)
  have hTm : Measurable T := by
    rw [show T = fun g => Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
        ∑ i : Fin N, (skCavityDisorderEquiv N g).2 i * m (skCavityDisorderEquiv N g).1 i + h)
      from funext hT]
    refine Real.continuous_tanh.measurable.comp ((Measurable.const_mul ?_ _).add_const h)
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (measurable_snd.comp hem)).mul
        ((hmm i).comp (measurable_fst.comp hem))
  have hWm : Measurable W := by
    rw [show W = fun g => Real.tanh (β * Real.sqrt q * Z (skCavityDisorderEquiv N g) + h)
      from funext hW]
    exact Real.continuous_tanh.measurable.comp (((hZ.comp hem).const_mul _).add_const h)
  have hX1 : ∀ g, |X g| ≤ 1 := fun g => by rw [hX]; exact abs_integral_spin_le_one _ _
  have hT1 : ∀ g, |T g| ≤ 1 := fun g => by rw [hT]; exact (Real.abs_tanh_lt_one _).le
  have hW1 : ∀ g, |W g| ≤ 1 := fun g => by rw [hW]; exact (Real.abs_tanh_lt_one _).le
  have hi1 := integrable_sq_sub_of_abs_le
    (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) hXm hTm hX1 hT1
  have hi2 := integrable_sq_sub_of_abs_le
    (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) hTm hWm hT1 hW1
  have hgoal : ∫ g, (X g - W g) ^ 2 ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
      ∫ g, (2 * (X g - T g) ^ 2 + 2 * (T g - W g) ^ 2)
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_mono_of_nonneg (ae_of_all _ fun g => sq_nonneg _)
      ((hi1.const_mul 2).add (hi2.const_mul 2)) (ae_of_all _ fun g => by
        nlinarith [sq_nonneg ((X g - T g) - (T g - W g))])
  rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
    integral_const_mul] at hgoal
  simp only [hX, hW] at hgoal
  calc _ ≤ _ := hgoal
    _ ≤ 2 * (K₁ / ((N : ℝ) + 1)) + 2 * (K₃ / ((N : ℝ) + 1)) := by
        have := h1'; have := h2'
        simp only [hX, hT] at *
        nlinarith
    _ = (2 * K₁ + 2 * K₃) / ((N : ℝ) + 1) := by ring

end SpinGlasses
