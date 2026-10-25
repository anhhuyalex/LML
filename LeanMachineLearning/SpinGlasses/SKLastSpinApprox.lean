/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKGaussianCorollaries
public import LeanMachineLearning.SpinGlasses.SKCavityFreeEnergy
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound

/-!
# The last spin is a tanh of the cavity field (Talagrand, Lemma 1.7.4, Eq. (1.185))

For the `(N+1)`-spin SK system at inverse temperature `β` the cavity formula writes the Gibbs
mean of the last spin as `⟨sinh L⟩_- / ⟨cosh L⟩_-`, where `⟨·⟩_-` is the Gibbs measure of the old
`N`-spin system at `β_- = β √(N/(N+1))` and the field `L` is linear in the new couplings `y`.
Corollary 1.7.15, Eq. (1.209), compares this ratio with `tanh` of the mean field, and the
disorder of the `(N+1)`-spin system is the product of the old disorder and `y`.  This gives
`𝔼 (⟨σ_{N+1}⟩ - tanh (β (N+1)^{-1/2} ∑ g_i ⟨σ_i⟩_- + h))² ≤ K / (N+1)`
(`SpinGlasses.sk_last_spin_tanh_approx`).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.7.4, Eq. (1.185).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- The old system at `β_- = β √(N/(N+1))` has the interaction coefficient `β / √(N+1)` of the
`(N+1)`-spin system. -/
theorem sk_beta_minus_coefficient (N : ℕ) (β : ℝ) (hN : 0 < N) :
    (Real.sqrt (N : ℝ))⁻¹ * (β * Real.sqrt ((N : ℝ) / (N + 1))) =
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * β := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [Real.sqrt_div hN0.le]
  have h1 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have h2 : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- The cavity field of the old system at `β_-` in dot-product form: the linear form in the new
couplings `y` with coefficient `(√N)⁻¹ β_-` is `β/√(N+1)` times `∑ y_i a_i`. -/
theorem dotProduct_sk_beta_minus (N : ℕ) (β : ℝ) (hN : 0 < N) (y a : Fin N → ℝ) :
    ((fun i => (Real.sqrt (N : ℝ))⁻¹ * (β * Real.sqrt ((N : ℝ) / (N + 1)) * a i)) ⬝ᵥ y) =
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ i, y i * a i := by
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (y i * a i) * sk_beta_minus_coefficient N β hN

/-- **Cavity splitting of the SK energy.**  The energy of the `(N+1)`-spin system is the energy of
the old `N`-spin system at `β_- = β √(N/(N+1))` (with the old couplings) plus the last spin times
the cavity field, which is linear in the new couplings `y`. -/
theorem skGibbsEnergy_succ_cavity {N : ℕ} (hN : 0 < N) (β h : ℝ) (g : FinPairs (N + 1) → ℝ)
    (σ : Fin (N + 1) → ℤˣ) :
    skGibbsEnergy (N + 1) β h g σ =
      skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h
          (fun p : FinPairs N => g ⟨(p.val.1.castSucc, p.val.2.castSucc),
            Fin.castSucc_lt_castSucc_iff.mpr p.property⟩) (fun i => σ i.castSucc) +
        ((σ (Fin.last N) : ℤ) : ℝ) *
          (((fun i => (Real.sqrt (N : ℝ))⁻¹ *
              (β * Real.sqrt ((N : ℝ) / (N + 1)) * ((σ i.castSucc : ℤ) : ℝ))) ⬝ᵥ
            fun i : Fin N => g ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩) + h) := by
  rw [dotProduct_sk_beta_minus N β hN]
  have hc := sk_cavity_energy_snoc N ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β) h g σ
  unfold skGibbsEnergy
  rw [Nat.cast_succ, sk_beta_minus_coefficient N β hN]
  simp only [mul_add]
  convert hc using 2
  ring

/-- **Cavity formula for the last spin.**  The Gibbs mean of the last spin of the `(N+1)`-spin
system is the ratio `⟨sinh L⟩_- / ⟨cosh L⟩_-` over the old Gibbs measure at `β_-`, with
`L ρ = (√N)⁻¹ β_- ∑ y_i ρ_i + h` and `y` the couplings of the last spin. -/
theorem integral_last_spin_eq_sinh_div_cosh {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (g : FinPairs (N + 1) → ℝ) :
    ∫ σ, ((σ (Fin.last N) : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) =
      (∫ a, Real.sinh (((fun i => (Real.sqrt (N : ℝ))⁻¹ *
            (β * Real.sqrt ((N : ℝ) / (N + 1)) * ((a i : ℤ) : ℝ))) ⬝ᵥ
          fun i : Fin N => g ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h
          (fun p : FinPairs N => g ⟨(p.val.1.castSucc, p.val.2.castSucc),
            Fin.castSucc_lt_castSucc_iff.mpr p.property⟩)))) /
      (∫ a, Real.cosh (((fun i => (Real.sqrt (N : ℝ))⁻¹ *
            (β * Real.sqrt ((N : ℝ) / (N + 1)) * ((a i : ℤ) : ℝ))) ⬝ᵥ
          fun i : Fin N => g ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h
          (fun p : FinPairs N => g ⟨(p.val.1.castSucc, p.val.2.castSucc),
            Fin.castSucc_lt_castSucc_iff.mpr p.property⟩)))) := by
  set A : (Fin N → ℤˣ) → ℝ := skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h
    (fun p : FinPairs N => g ⟨(p.val.1.castSucc, p.val.2.castSucc),
      Fin.castSucc_lt_castSucc_iff.mpr p.property⟩) with hA
  set L : (Fin N → ℤˣ) → ℝ := fun ρ => ((fun i => (Real.sqrt (N : ℝ))⁻¹ *
      (β * Real.sqrt ((N : ℝ) / (N + 1)) * ((ρ i : ℤ) : ℝ))) ⬝ᵥ
    fun i : Fin N => g ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩) + h with hL
  have hE : skGibbsEnergy (N + 1) β h g = fun σ : Fin (N + 1) → ℤˣ =>
      A (fun i => σ i.castSucc) + ((σ (Fin.last N) : ℤ) : ℝ) * L (fun i => σ i.castSucc) :=
    funext (skGibbsEnergy_succ_cavity hN β h g)
  rw [hE, integral_count_tilted_fin_snoc_cavity_units N A L]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ρ => ?_)
  simp only [Fin.snoc_last, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul,
    neg_one_mul, ← sub_eq_add_neg, Real.sinh_eq, hL]

/-- **Talagrand, Lemma 1.7.4, Eq. (1.185).**  For `4 β₀² < 1` and `h` there is `K` such that for
all `|β| ≤ β₀` and `N ≥ 1`,
`𝔼 (⟨σ_{N+1}⟩ - tanh (β (N+1)^{-1/2} ∑_{i ≤ N} g_{i,N+1} ⟨σ_i⟩_- + h))² ≤ K / (N+1)`,
where `⟨·⟩_-` is the Gibbs measure of the first `N` spins with the old couplings at
`β_- = β √(N/(N+1))`. -/
theorem sk_last_spin_tanh_approx (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, |β| ≤ β₀ → ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs (N + 1) → ℝ,
        (∫ σ, ((σ (Fin.last N) : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) -
          Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
            ∑ i : Fin N, g ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩ *
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted
                (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h
                  (fun p : FinPairs N => g ⟨(p.val.1.castSucc, p.val.2.castSucc),
                    Fin.castSucc_lt_castSucc_iff.mpr p.property⟩))) + h)) ^ 2
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ K / ((N : ℝ) + 1) := by
  obtain ⟨K, hK0, hK⟩ := sk_cavity_field_tanh_approx β₀ hβ₀ hβ₀' h (k := 1) le_rfl
  refine ⟨2 * K, by positivity, fun β hβ N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : Real.sqrt ((N : ℝ) / (N + 1)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one (by positivity)).mpr (by linarith))
  have hβm : |β * Real.sqrt ((N : ℝ) / (N + 1))| ≤ β₀ := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc _ ≤ |β| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ ≤ β₀ := by rw [mul_one]; exact hβ
  obtain ⟨q, -, hq⟩ := exists_fixedPoint (β * Real.sqrt ((N : ℝ) / (N + 1))) h
  have hKN := hK _ q hq.symm hβm N hN
  set P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  set Q := Measure.pi fun _ : Fin N => gaussianReal 0 1
  let F : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun w =>
    (((∫ a, Real.sinh (((fun i => (Real.sqrt (N : ℝ))⁻¹ *
          (β * Real.sqrt ((N : ℝ) / (N + 1)) * ((a i : ℤ) : ℝ))) ⬝ᵥ w.2) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h w.1))) /
      (∫ a, Real.cosh (((fun i => (Real.sqrt (N : ℝ))⁻¹ *
          (β * Real.sqrt ((N : ℝ) / (N + 1)) * ((a i : ℤ) : ℝ))) ⬝ᵥ w.2) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h w.1)))) -
      Real.tanh (((fun i => (Real.sqrt (N : ℝ))⁻¹ *
          (β * Real.sqrt ((N : ℝ) / (N + 1)) *
            ∫ b, ((b i : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h
                w.1)))) ⬝ᵥ w.2) + h)) ^ (2 * 1)
  have hF0 : ∀ w, 0 ≤ F w := fun w => Even.pow_nonneg ⟨1, by ring⟩ _
  calc _ = ∫ g : FinPairs (N + 1) → ℝ,
        F (fun p : FinPairs N => g ⟨(p.val.1.castSucc, p.val.2.castSucc),
            Fin.castSucc_lt_castSucc_iff.mpr p.property⟩,
          fun i : Fin N => g ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩)
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
        refine integral_congr_ae (ae_of_all _ fun g => ?_)
        simp only [F, mul_one, integral_last_spin_eq_sinh_div_cosh hN β h g,
          dotProduct_sk_beta_minus N β hN]
    _ = ∫ w, F w ∂(P.prod Q) := integral_comp_sk_cavity_disorder N F
    _ ≤ ∫ x, ∫ y, F (x, y) ∂Q ∂P := integral_prod_le_integral_integral_of_nonneg hF0
    _ ≤ K / (N : ℝ) ^ 1 := by simpa only [F] using hKN
    _ ≤ 2 * K / ((N : ℝ) + 1) := by
        rw [pow_one, div_le_div_iff₀ hN0 (by positivity)]
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith

end SpinGlasses
