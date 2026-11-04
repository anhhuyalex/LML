/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsFluctuationMoment
public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration
public import LeanMachineLearning.SpinGlasses.SKFirstMoment
public import LeanMachineLearning.SpinGlasses.SKFixedPoint

/-!
# The general Gaussian fluctuation principle for the SK model (Talagrand, Theorem 1.7.11)

For `4 β² < 1`, `q = 𝔼 tanh²(β √q z + h)`, an exponentially tame `U` and `k ≥ 1`,
`𝔼 (⟨U(N^{-1/2} ∑ y_i (σ_i - ⟨σ_i⟩))⟩ - 𝔼_ξ U(ξ √(1-q)))^{2k} ≤ K / N^k`
(`SpinGlasses.sk_general_gaussian_fluctuation`).  For every fixed disorder `g` the model-independent
bound `exists_gibbs_fluctuation_pow_le` controls the left-hand side by a multiple of the overlap
moment; the SK model enters only through the moment bound `sk_overlap_moment_le_of_exp` for the
overlap, which is then integrated over `g`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

/-- The Gibbs energy of the SK model with the pair disorder `g`. -/
noncomputable def skGibbsEnergy (N : ℕ) (β h : ℝ) (g : FinPairs N → ℝ) (a : Fin N → ℤˣ) : ℝ :=
  (Real.sqrt N)⁻¹ * β * (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
    h * ∑ i, ((a i : ℤ) : ℝ)

/-- The SK energy of a fixed configuration is measurable in the disorder. -/
theorem measurable_skGibbsEnergy (N : ℕ) (β h : ℝ) (a : Fin N → ℤˣ) :
    Measurable fun g : FinPairs N → ℝ => skGibbsEnergy N β h g a := by
  unfold skGibbsEnergy
  fun_prop

/-- **The SK energy is a linear form of the disorder.**  There are coefficient vectors `a σ` with
`skGibbsEnergy N β h g σ = a σ ⬝ᵥ g + h ∑ᵢ σᵢ` and `a σ ⬝ᵥ a σ ≤ β² N / 2` (the exact value is
`β² (N - 1) / 2`: the variance of the pair field of a fixed configuration). -/
theorem exists_sk_linear_data (N : ℕ) (β h : ℝ) :
    ∃ a : (Fin N → ℤˣ) → FinPairs N → ℝ,
      (∀ σ g, skGibbsEnergy N β h g σ = a σ ⬝ᵥ g + h * ∑ i, ((σ i : ℤ) : ℝ)) ∧
      ∀ σ, a σ ⬝ᵥ a σ ≤ β ^ 2 * N / 2 := by
  refine ⟨fun σ p => (Real.sqrt N)⁻¹ * β * (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)),
    fun σ g => ?_, fun σ => ?_⟩
  · simp only [skGibbsEnergy, dotProduct, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [dotProduct]
    have hc : ((Real.sqrt N)⁻¹ * β) ^ 2 = β ^ 2 / N := by
      rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
      ring
    have hterm : ∀ p : FinPairs N, ((Real.sqrt N)⁻¹ * β * (((σ p.val.1 : ℤ) : ℝ) *
        ((σ p.val.2 : ℤ) : ℝ))) * ((Real.sqrt N)⁻¹ * β * (((σ p.val.1 : ℤ) : ℝ) *
        ((σ p.val.2 : ℤ) : ℝ))) = β ^ 2 / N := fun p => by
      have h1 : (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
          (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) = 1 := by
        have := units_cast_sq (σ p.val.1)
        have := units_cast_sq (σ p.val.2)
        nlinarith [units_cast_sq (σ p.val.1), units_cast_sq (σ p.val.2)]
      calc _ = ((Real.sqrt N)⁻¹ * β) ^ 2 * ((((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
            (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))) := by ring
        _ = β ^ 2 / N := by rw [h1, hc, mul_one]
    simp only [dotProduct, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [cast_card_finPairs]
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
    rw [show (N : ℝ) * ((N : ℝ) - 1) / 2 * (β ^ 2 / N) = β ^ 2 * ((N : ℝ) - 1) / 2 by
      field_simp]
    nlinarith [sq_nonneg β]

/-- The overlap moment of the SK Gibbs measure is integrable in the disorder. -/
theorem integrable_overlapMoment_skGibbsEnergy (N : ℕ) (β h q : ℝ) (k : ℕ) :
    Integrable (fun g : FinPairs N → ℝ =>
      overlapMoment (fun (i : Fin N) (a : Fin N → ℤˣ) => ((a i : ℤ) : ℝ))
        (skGibbsEnergy N β h g) q k) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  refine integrable_integral_pi_count_tilted_det (R := Fin 2)
    (g := fun a g => skGibbsEnergy N β h g a)
    (fun a => (measurable_skGibbsEnergy N β h a).aemeasurable)
    (fun τ => ((N : ℝ)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ) - q) ^ (2 * k))

/-- **The general Gaussian fluctuation principle (Talagrand, Theorem 1.7.11).**  Let
`4 β² < 1`, let `q = 𝔼 tanh²(β √q z + h)` and let `U` be exponentially tame.  Then for every `k ≥ 1`
there is `K` such that for every `N ≥ 1`
`𝔼 (⟨U(N^{-1/2} ∑ y_i σ̇_i)⟩ - 𝔼_ξ U(ξ √(1-q)))^{2k} ≤ K / N^k`, where `σ̇_i = σ_i - ⟨σ_i⟩`, `y` is
a standard Gaussian vector independent of the disorder `g`, and `𝔼` is over `g` and `y`. -/
theorem sk_general_gaussian_fluctuation (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) {U : ℝ → ℝ} (hU : ExpTame U) {k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
        ((∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
          ∫ t, U (Real.sqrt (1 - q) * t) ∂(gaussianReal 0 1)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / (N : ℝ) ^ k := by
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q) with hvdef
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  set c₀ : ℝ := ∫ s, U (v * s) ∂(gaussianReal 0 1) with hc₀
  have hV : ExpTame (fun x => U x - c₀) := hU.sub_const c₀
  have hV0 : ∫ t, (fun x => U x - c₀) (v * t) ∂(gaussianReal 0 1) = 0 :=
    hU.integral_sub_const_mul_gaussianReal v
  obtain ⟨Cb, c, hCb, hc, hbd⟩ := hV.exists_bound_upTo (2 * (2 * k))
  obtain ⟨C, hC0, hC⟩ := exists_gibbs_fluctuation_pow_le hk (fun j _ => hCb j) hc
  obtain ⟨K', hK'0, hK'⟩ := sk_overlap_moment_le_of_exp β h q hfix hβ k
  refine ⟨C * K' + 1, by positivity, fun N hN => ?_⟩
  have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  set ξ : Fin N → (Fin N → ℤˣ) → ℝ := fun i a => ((a i : ℤ) : ℝ) with hξ
  have hξ_sq : ∀ i a, ξ i a ^ 2 = 1 := fun i a => units_cast_sq (a i)
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP
  set J : (FinPairs N → ℝ) → ℝ := fun g => overlapMoment ξ (skGibbsEnergy N β h g) q k with hJ
  have hJint : Integrable J P := integrable_overlapMoment_skGibbsEnergy N β h q k
  have hJmom : ∫ g, J g ∂P ≤ K' / (N : ℝ) ^ k := hK' N hN
  -- for each disorder the Gibbs-side bound
  have hpt : ∀ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
      ((∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
            ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) - c₀) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤ C * J g := fun g => by
    simp_rw [sub_integral_count_tilted_eq]
    exact hC (fun x => U x - c₀) hV hbd q v hq.1 hv hV0 N hN (Fin N → ℤˣ) ξ hξ_sq
      (skGibbsEnergy N β h g) _ fun a j => rfl
  have hnonneg : ∀ g : FinPairs N → ℝ, 0 ≤ ∫ y : Fin N → ℝ,
      ((∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
            ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) - c₀) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun g =>
    integral_nonneg fun y => Even.pow_nonneg ⟨k, by ring⟩ _
  calc _ ≤ ∫ g, C * J g ∂P :=
        integral_mono_of_nonneg (ae_of_all _ hnonneg) (hJint.const_mul C) (ae_of_all _ hpt)
    _ = C * ∫ g, J g ∂P := integral_const_mul _ _
    _ ≤ C * (K' / (N : ℝ) ^ k) := mul_le_mul_of_nonneg_left hJmom hC0
    _ ≤ (C * K' + 1) / (N : ℝ) ^ k := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) hNk.le

end SpinGlasses
