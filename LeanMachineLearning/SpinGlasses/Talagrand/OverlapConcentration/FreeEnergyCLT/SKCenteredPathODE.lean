/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCenteredPathMoments
public import LeanMachineLearning.SpinGlasses.SKPathOverlapMoments
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment

/-!
# The differential equation of the centered moments (Talagrand, Eq. (1.120))

Along the smart path put `V_s = A_s - SK(s)` and `ψ_m(s) = 𝔼 V_s^m`.  Combining the derivative
with a moving center (`SpinGlasses.exists_sk_smart_path_profile_centered`) with the a priori
moments of `V_s` (Lemma 1.4.12 with Theorem 1.4.10) and the fourth overlap moment (Eq. (1.103)),
the derivative splits as `ψ_m' = sin s cos s ((m (m - 1) / 2) N⁻¹ β² q² ψ_{m-2} + D_m)` with
`|D_m| ≤ K_m N^{-(m+1)/2}`, which is the claim `II = O(m + 1)` of the book.

## Main declarations

* `ProbabilityTheory.abs_integral_pow_mul_le`: Cauchy-Schwarz for `∫ V^p Q` from moment bounds.
* `SpinGlasses.exists_sk_centered_path_ode`: the differential equation with remainder.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, proof of Theorem 1.4.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The squared overlap deviation `(R_{1,2} - q)²` of two replicas is at most `4`, so its mean
under any probability measure on pairs of configurations is at most `4` in modulus. -/
theorem abs_integral_overlap_sq_le_four {N : ℕ} (hN : 0 < N) (q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (ν : Measure (Fin 2 → (Fin N → ℤˣ))) [IsProbabilityMeasure ν] :
    |∫ σ : Fin 2 → (Fin N → ℤˣ),
      (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
      ∂ν| ≤ 4 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hf0 : ∀ σ : Fin 2 → (Fin N → ℤˣ), |(((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ
      fun i => ((σ 1 i : ℤ) : ℝ))) - q)| ≤ 2 := fun σ => by
    simpa only [Fintype.card_fin] using abs_card_inv_mul_dotProduct_sub_le_two
      (fun i : Fin N => ((σ 0 i : ℤ) : ℝ)) (fun i : Fin N => ((σ 1 i : ℤ) : ℝ))
      (fun i => abs_units_cast_le_one _) (fun i => abs_units_cast_le_one _) q hq
  have key : ∀ R : (Fin 2 → (Fin N → ℤˣ)) → ℝ, (∀ σ, |R σ| ≤ 2) → |∫ σ, R σ ^ 2 ∂ν| ≤ 4 :=
    fun R hR => by
      simpa [probReal_univ] using norm_integral_le_of_norm_le_const (μ := ν) (C := 4)
        (f := fun σ => R σ ^ 2) (ae_of_all _ fun σ => by
          rw [Real.norm_eq_abs, abs_pow]
          nlinarith [hR σ, abs_nonneg (R σ)])
  exact key _ hf0

/-- **Jensen for a Gibbs average of the squared overlap deviation:**
`⟨(R_{1,2} - q)²⟩² ≤ ⟨(R_{1,2} - q)⁴⟩` for a probability measure on pairs of configurations. -/
theorem sq_integral_overlap_sq_le {N : ℕ} (q : ℝ)
    (ν : Measure (Fin 2 → (Fin N → ℤˣ))) [IsProbabilityMeasure ν] :
    (∫ σ : Fin 2 → (Fin N → ℤˣ),
      (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
      ∂ν) ^ 2 ≤ ∫ σ : Fin 2 → (Fin N → ℤˣ),
      (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ (2 * 2)
      ∂ν := by
  convert sq_integral_le_integral_sq (μX := ν)
      (g := fun σ : Fin 2 → (Fin N → ℤˣ) => (((N : ℝ)⁻¹ *
        ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
      (measurable_of_finite _) Integrable.of_finite using 1
  congr 1
  funext σ
  ring

/-- The Gibbs average `⟨(R_{1,2} - q)²⟩_s` along the smart path is a measurable function of the
disorder, for any family of energies `E a` that are measurable in the disorder. -/
theorem aemeasurable_gibbs_overlap_sq {N : ℕ} (q : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {E : (Fin N → ℤˣ) → Ω → ℝ} (hE : ∀ a, Measurable (E a)) :
    AEMeasurable (fun ω => ∫ σ : Fin 2 → (Fin N → ℤˣ),
      (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b => E b ω)) P :=
  aemeasurable_integral_pi_count_tilted (R := Fin 2) (g := fun ω a => E a ω)
    (fun a => (hE a).aemeasurable) fun _ => aemeasurable_const

/-- Jensen for the squared overlap deviation, averaged over arbitrary finite disorder.
No system-size or fixed-point range assumption is needed for this finite-state inequality. -/
theorem integral_gibbs_overlap_sq_sq_le {N : ℕ} (q : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {E : (Fin N → ℤˣ) → Ω → ℝ}
    (hE : ∀ a, AEMeasurable (E a) P) :
    ∫ ω, (∫ σ : Fin 2 → (Fin N → ℤˣ),
      (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b => E b ω)) ^ 2 ∂P ≤
    ∫ ω, ∫ σ : Fin 2 → (Fin N → ℤˣ),
      (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ (2 * 2)
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b => E b ω) ∂P := by
  convert integral_sq_integral_pi_count_tilted_le (R := Fin 2) hE
    (fun σ : Fin 2 → (Fin N → ℤˣ) =>
      (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2) using 1
  congr 1
  funext ω
  congr 1
  funext σ
  ring

/-- **Bookkeeping of the three remainder terms** (Talagrand, `II = O(k + 1)`): with `0 < ε ≤ 1`,
`|T₁| ≤ c₁ ε^{m+1}` and, for `m ≥ 2`, `|T₂| ≤ c₂ ε^m` and `|T₃| ≤ c₃ ε^{m-2}`, the combination
`b (m T₁ - ε² m (m-1) T₂ + ε⁴ m (m-1) T₃)` has modulus at most
`|b| (m c₁ + m (m-1) c₂ + m (m-1) c₃) ε^{m+1}`. -/
theorem abs_remainder_combination_le {ε b T₁ T₂ T₃ c₁ c₂ c₃ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (h₁ : |T₁| ≤ c₁ * ε ^ (m + 1)) (h₂ : 2 ≤ m → |T₂| ≤ c₂ * ε ^ m)
    (h₃ : 2 ≤ m → |T₃| ≤ c₃ * ε ^ (m - 2)) :
    |b * ((m : ℝ) * T₁ - ε ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) * T₂ +
        ε ^ 4 * ((m : ℝ) * ((m : ℝ) - 1)) * T₃)| ≤
      |b| * ((m : ℝ) * c₁ + (m : ℝ) * ((m : ℝ) - 1) * c₂ + (m : ℝ) * ((m : ℝ) - 1) * c₃) *
        ε ^ (m + 1) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hc₁ : 0 ≤ c₁ := by
    have := (abs_nonneg T₁).trans h₁
    exact nonneg_of_mul_nonneg_left this (by positivity)
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · obtain rfl : m = 1 := by omega
    simp only [Nat.cast_one, sub_self, mul_zero, zero_mul, sub_zero, add_zero, one_mul] at h₁ ⊢
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg b)
  · have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hge
      linarith
    have hP : ε ^ (m + 2) ≤ ε ^ (m + 1) := pow_le_pow_of_le_one hε.le hε1 (by omega)
    have e2 : ε ^ 2 * ε ^ m = ε ^ (m + 2) := by rw [← pow_add]; ring_nf
    have e4 : ε ^ 4 * ε ^ (m - 2) = ε ^ (m + 2) := by rw [← pow_add]; congr 1; omega
    have t2 : ε ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) * |T₂| ≤
        (m : ℝ) * ((m : ℝ) - 1) * c₂ * ε ^ (m + 1) := by
      calc _ ≤ ε ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) * (c₂ * ε ^ m) :=
            mul_le_mul_of_nonneg_left (h₂ hge) (by positivity)
        _ = (m : ℝ) * ((m : ℝ) - 1) * c₂ * ε ^ (m + 2) := by rw [← e2]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
    have t3 : ε ^ 4 * ((m : ℝ) * ((m : ℝ) - 1)) * |T₃| ≤
        (m : ℝ) * ((m : ℝ) - 1) * c₃ * ε ^ (m + 1) := by
      calc _ ≤ ε ^ 4 * ((m : ℝ) * ((m : ℝ) - 1)) * (c₃ * ε ^ (m - 2)) :=
            mul_le_mul_of_nonneg_left (h₃ hge) (by positivity)
        _ = (m : ℝ) * ((m : ℝ) - 1) * c₃ * ε ^ (m + 2) := by rw [← e4]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
    have t1 : (m : ℝ) * |T₁| ≤ (m : ℝ) * c₁ * ε ^ (m + 1) := by
      calc _ ≤ (m : ℝ) * (c₁ * ε ^ (m + 1)) := mul_le_mul_of_nonneg_left h₁ hm0.le
        _ = _ := by ring
    rw [abs_mul]
    have hsum : |(m : ℝ) * T₁ - ε ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) * T₂ +
        ε ^ 4 * ((m : ℝ) * ((m : ℝ) - 1)) * T₃| ≤ (m : ℝ) * c₁ * ε ^ (m + 1) +
        (m : ℝ) * ((m : ℝ) - 1) * c₂ * ε ^ (m + 1) +
        (m : ℝ) * ((m : ℝ) - 1) * c₃ * ε ^ (m + 1) := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
      · rwa [abs_mul, abs_of_pos hm0]
      · rwa [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 2),
          abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * ((m : ℝ) - 1))]
      · rwa [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 4),
          abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * ((m : ℝ) - 1))]
    calc |b| * _ ≤ |b| * ((m : ℝ) * c₁ * ε ^ (m + 1) +
        (m : ℝ) * ((m : ℝ) - 1) * c₂ * ε ^ (m + 1) + (m : ℝ) * ((m : ℝ) - 1) * c₃ * ε ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg b)
      _ = _ := by ring

/-- **The differential equation of the centered moments along the smart path** (Talagrand,
Eq. (1.120)).  Let `β² < 1/4`, `q` a fixed point, `ψ_k(s) = 𝔼 (A_N(s) - SK(s))^k`.  There are
constants `K_m` depending only on `β` such that for every `N > 0`: `ψ_0 = 1`; `ψ_k(0)` is the `k`-th
moment about `rsFunctional β h q` of the SK free energy and `ψ_k(π/2)` that of the average of the
i.i.d. centered variables `log cosh (β √q zᵢ + h) - 𝔼 log cosh (β √q z + h)`; and for every
`m ≥ 1` and `s`, `ψ_m'(s) = sin s cos s ((m (m-1) / 2) N⁻¹ β² q² ψ_{m-2}(s) + D)` with
`|D| ≤ K_m N^{-(m+1)/2}` for `s ∈ [0, π/2]`. -/
theorem exists_sk_centered_path_ode (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) :
    ∃ K : ℕ → ℝ, ∀ {N : ℕ}, 0 < N → ∃ ψ : ℕ → ℝ → ℝ,
      (∀ s, ψ 0 s = 1) ∧
      (∀ k, ψ k 0 = ∫ g : FinPairs N → ℝ, ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
          Real.exp (skGibbsEnergy N β h g σ)) - rsFunctional β h q) ^ k
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ∧
      (∀ k, ψ k (Real.pi / 2) = ∫ z : Fin N → ℝ, ((N : ℝ)⁻¹ * ∑ i, (Real.log (Real.cosh
          (β * Real.sqrt q * z i + h)) - ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h))
            ∂(gaussianReal 0 1))) ^ k ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
      ∀ m, 1 ≤ m → ∀ s, ∃ D, HasDerivAt (ψ m) (Real.sin s * Real.cos s *
        ((m : ℝ) * (m - 1) / 2 * ((Real.sqrt N)⁻¹) ^ 2 * (β ^ 2 * q ^ 2) * ψ (m - 2) s + D)) s ∧
        (s ∈ Set.Icc 0 (Real.pi / 2) → |D| ≤ K m * ((Real.sqrt N)⁻¹) ^ (m + 1)) := by
  have hq1 := fixedPoint_mem_Icc hfix
  have hq : 0 ≤ q := hq1.1
  have hb : 0 < 1 / 4 - β ^ 2 := by linarith
  have hs2 : 0 < 1 / 2 - 2 * β ^ 2 := by linarith
  have hsq : 0 < Real.sqrt (1 / 2 - 2 * β ^ 2) := Real.sqrt_pos.2 hs2
  set K1 : ℝ := (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ / (1 / 4 - β ^ 2) with hK1_def
  have hK1 : 0 < K1 := by positivity
  set Kv : ℕ → ℝ := fun j => 2 ^ (j - 1) * (2 * (Nat.factorial j : ℝ) * Real.exp (3 / 2 * β ^ 2) +
    (β ^ 2 / 4 * K1) ^ j) with hKv_def
  have hKv : ∀ j, 0 < Kv j := fun j => mul_pos (by positivity)
    (add_pos_of_pos_of_nonneg (by positivity) (pow_nonneg (by positivity) _))
  set C4 : ℝ := (Nat.factorial 2 : ℝ) * (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ / (1 / 4 - β ^ 2) ^ 2
    with hC4_def
  have hC4 : 0 < C4 := by positivity
  refine ⟨fun m => β ^ 2 / 2 * ((m : ℝ) * Real.sqrt (Kv (2 * (m - 1)) * C4) +
    (m : ℝ) * ((m : ℝ) - 1) * Real.sqrt (Kv (2 * (m - 2)) * C4) +
    (m : ℝ) * ((m : ℝ) - 1) * Kv (m - 2)), fun {N} hN => ?_⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  obtain ⟨F, G, A, Q, hF, hG, hA, hQ, hcen⟩ :=
    exists_sk_smart_path_profile_centered hN β h q hq hq1.2
  set P := (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  refine ⟨fun m s => ∫ ω, (A s ω - skPathRS β h q s) ^ m ∂P, fun s => by simp, ?_, ?_, ?_⟩
  · intro k
    have e : ∀ g σ, skGibbsEnergy N β h g σ = F g σ + h * ∑ i, ((σ i : ℤ) : ℝ) := fun g σ => by
      simp only [skGibbsEnergy, hF]
    simp only [e]
    simpa only [skPathRS_zero] using (hcen k).1
  · intro k
    refine ((hcen k).2.1).trans (integral_congr_ae (ae_of_all _ fun z => ?_))
    dsimp only
    rw [skPathRS_pi_div_two, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    field_simp
    ring
  · obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = (Real.sqrt N)⁻¹ := ⟨_, rfl⟩
    have hε : 0 < ε := by rw [hε_def]; exact inv_pos.2 (Real.sqrt_pos.2 hNpos)
    have hε1 : ε ≤ 1 := by
      rw [hε_def]; exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (Nat.one_le_cast.2 hN))
    have hε2 : ε ^ 2 = (N : ℝ)⁻¹ := by rw [hε_def, inv_pow, Real.sq_sqrt hNpos.le]
    have hε4 : ε ^ 4 = ((N : ℝ)⁻¹) ^ 2 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hε2]
    simp only [← hε_def]
    intro m hm s
    have hint : ∀ (a : ℝ) (j : ℕ), Integrable (fun ω => (A s ω - a) ^ j) P := fun a j =>
      integrable_smart_path_free_energy_sub_pow hN β h q hq hq1.2 hF hG hA s a j
    have hAm : Measurable (A s) := measurable_smart_path_free_energy β h q hF hG hA s
    have hEm : ∀ a : Fin N → ℤˣ, Measurable (fun ω : (FinPairs N → ℝ) × (Fin N → ℝ) =>
        Real.cos s * F ω.1 a + Real.sin s * G ω.2 a + h * ∑ i, ((a i : ℤ) : ℝ)) := fun a => by
      simp only [hF, hG]
      fun_prop
    have hQm : AEMeasurable (Q s) P := by
      have e : Q s = fun ω => ∫ σ : Fin 2 → (Fin N → ℤˣ),
          (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b =>
            Real.cos s * F ω.1 b + Real.sin s * G ω.2 b + h * ∑ i, ((b i : ℤ) : ℝ)) :=
        funext (hQ s)
      rw [e]
      exact aemeasurable_gibbs_overlap_sq q hEm
    have hQb : ∀ ω, |Q s ω| ≤ 4 := fun ω => by
      rw [hQ]
      exact abs_integral_overlap_sq_le_four hN q hq1 _
    have hQL2 : MemLp (Q s) 2 P := MemLp.of_bound hQm.aestronglyMeasurable 4
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQb ω)
    -- the integrals of the three terms
    set V : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun ω => A s ω - skPathRS β h q s with hV_def
    have hVm : Measurable V := hAm.sub_const _
    have hQV : ∀ j, Integrable (fun ω => V ω ^ j * Q s ω) P := fun j => by
      have := Integrable.bdd_mul (c := 4) (hint (skPathRS β h q s) j) hQm.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQb ω)
      simpa only [mul_comm] using this
    set T0 := ∫ ω, V ω ^ (m - 1) ∂P with hT0
    set T1 := ∫ ω, V ω ^ (m - 1) * Q s ω ∂P with hT1
    set T2 := ∫ ω, V ω ^ (m - 2) * Q s ω ∂P with hT2
    set T3 := ∫ ω, V ω ^ (m - 2) ∂P with hT3
    set D : ℝ := β ^ 2 / 2 * ((m : ℝ) * T1 - ε ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) * T2 +
      ε ^ 4 * ((m : ℝ) * ((m : ℝ) - 1)) * T3) with hD_def
    refine ⟨D, ?_, fun hs => ?_⟩
    · have hder := (hcen m).2.2 s
      refine hder.congr_deriv ?_
      have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub hm, Nat.cast_one]
      have hI : ∫ ω, (((m : ℝ) * (A s ω - skPathRS β h q s) ^ (m - 1)) * (Q s ω - (1 - q) ^ 2) -
          (N : ℝ)⁻¹ * ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * (A s ω - skPathRS β h q s) ^ (m - 1 - 1)) *
            (Q s ω - q ^ 2 - (N : ℝ)⁻¹)) ∂P =
          (m : ℝ) * T1 - (m : ℝ) * (1 - q) ^ 2 * T0 -
            (N : ℝ)⁻¹ * ((m : ℝ) * ((m : ℝ) - 1)) * T2 +
            (N : ℝ)⁻¹ * ((m : ℝ) * ((m : ℝ) - 1)) * (q ^ 2 + (N : ℝ)⁻¹) * T3 := by
        have e : ∀ ω, ((m : ℝ) * (A s ω - skPathRS β h q s) ^ (m - 1)) * (Q s ω - (1 - q) ^ 2) -
            (N : ℝ)⁻¹ * ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * (A s ω - skPathRS β h q s) ^ (m - 1 - 1)) *
              (Q s ω - q ^ 2 - (N : ℝ)⁻¹) =
            (m : ℝ) * (V ω ^ (m - 1) * Q s ω) - (m : ℝ) * (1 - q) ^ 2 * V ω ^ (m - 1) -
              (N : ℝ)⁻¹ * ((m : ℝ) * ((m : ℝ) - 1)) * (V ω ^ (m - 2) * Q s ω) +
              (N : ℝ)⁻¹ * ((m : ℝ) * ((m : ℝ) - 1)) * (q ^ 2 + (N : ℝ)⁻¹) * V ω ^ (m - 2) :=
          fun ω => by
            rw [hm1, show m - 1 - 1 = m - 2 by omega]
            simp only [hV_def]
            ring
        simp_rw [e]
        have i1 := (hQV (m - 1)).const_mul (m : ℝ)
        have i2 := (hint (skPathRS β h q s) (m - 1)).const_mul ((m : ℝ) * (1 - q) ^ 2)
        have i3 := (hQV (m - 2)).const_mul ((N : ℝ)⁻¹ * ((m : ℝ) * ((m : ℝ) - 1)))
        have i4 := (hint (skPathRS β h q s) (m - 2)).const_mul
          ((N : ℝ)⁻¹ * ((m : ℝ) * ((m : ℝ) - 1)) * (q ^ 2 + (N : ℝ)⁻¹))
        rw [integral_add (f := fun ω => (m : ℝ) * (V ω ^ (m - 1) * Q s ω) -
            (m : ℝ) * (1 - q) ^ 2 * V ω ^ (m - 1) -
            (N : ℝ)⁻¹ * ((m : ℝ) * ((m : ℝ) - 1)) * (V ω ^ (m - 2) * Q s ω))
            ((i1.sub i2).sub i3) i4,
          integral_sub (f := fun ω => (m : ℝ) * (V ω ^ (m - 1) * Q s ω) -
            (m : ℝ) * (1 - q) ^ 2 * V ω ^ (m - 1)) (i1.sub i2) i3,
          integral_sub i1 i2]
        simp only [integral_const_mul, hT0, hT1, hT2, hT3, hV_def]
      rw [hI]
      have e0 : ∫ ω, (A s ω - skPathRS β h q s) ^ (m - 1) ∂P = T0 := rfl
      have e3 : ∫ ω, (A s ω - skPathRS β h q s) ^ (m - 2) ∂P = T3 := rfl
      rw [e0]
      change _ = Real.sin s * Real.cos s * ((m : ℝ) * ((m : ℝ) - 1) / 2 * ε ^ 2 * (β ^ 2 * q ^ 2) *
        (∫ ω, (A s ω - skPathRS β h q s) ^ (m - 2) ∂P) + D)
      rw [e3, hD_def, ← hε2]
      have : ε ^ 4 = ε ^ 2 * ε ^ 2 := by ring
      rw [this]
      ring
    · -- the a priori bounds and the Cauchy-Schwarz estimates
      have hVb : ∀ j, ∫ ω, |V ω| ^ j ∂P ≤ Kv j * ε ^ j := fun j => by
        obtain ⟨-, h1⟩ := integral_pow_abs_smart_path_V_le hN β h q hfix hβ hs j
        have h2 : Real.sqrt N ^ j * ∫ ω, |V ω| ^ j ∂P ≤ Kv j := by
          simpa only [hV_def, hA, hF, hG, hK1_def, hKv_def] using h1
        have hp : 0 < Real.sqrt N ^ j := pow_pos (Real.sqrt_pos.2 hNpos) j
        rw [hε_def, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp]
        linarith [h2]
      have hVsq : ∀ p, ∫ ω, V ω ^ (2 * p) ∂P ≤ Kv (2 * p) * ε ^ (2 * p) := fun p => by
        simpa only [(even_two_mul p).pow_abs] using hVb (2 * p)
      have hQ2 : ∫ ω, Q s ω ^ 2 ∂P ≤ C4 * ε ^ 4 := by
        have e : ∫ ω, Q s ω ^ 2 ∂P = ∫ ω, (∫ σ : Fin 2 → (Fin N → ℤˣ),
            (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b =>
              Real.cos s * F ω.1 b + Real.sin s * G ω.2 b + h * ∑ i, ((b i : ℤ) : ℝ))) ^ 2
            ∂P := by simp only [hQ]
        rw [e]
        refine (integral_gibbs_overlap_sq_sq_le q (P := P) (E := fun b ω =>
          Real.cos s * F ω.1 b + Real.sin s * G ω.2 b + h * ∑ i, ((b i : ℤ) : ℝ))
          (fun a => (hEm a).aemeasurable)).trans ?_
        have hpo := sk_path_expected_pow_overlap_le hN β h q hfix hβ 2 hs
        simp only [hF, hG]
        refine hpo.trans (le_of_eq ?_)
        rw [hC4_def, hε4]
        field_simp
      have hT1 : |T1| ≤ Real.sqrt (Kv (2 * (m - 1)) * C4) * ε ^ (m + 1) := by
        have := abs_integral_pow_mul_le hVm.aestronglyMeasurable hQL2 hε (hKv (2 * (m - 1))) hC4
          (p := m - 1) (hint _ _) (hVsq (m - 1)) hQ2
        rwa [show m - 1 + 2 = m + 1 by omega] at this
      have hT2 : 2 ≤ m → |T2| ≤ Real.sqrt (Kv (2 * (m - 2)) * C4) * ε ^ m := fun hm2 => by
        have := abs_integral_pow_mul_le hVm.aestronglyMeasurable hQL2 hε (hKv (2 * (m - 2))) hC4
          (p := m - 2) (hint _ _) (hVsq (m - 2)) hQ2
        rwa [show m - 2 + 2 = m by omega] at this
      have hT3 : 2 ≤ m → |T3| ≤ Kv (m - 2) * ε ^ (m - 2) := fun _ => by
        calc |T3| ≤ ∫ ω, |V ω ^ (m - 2)| ∂P := abs_integral_le_integral_abs
          _ = ∫ ω, |V ω| ^ (m - 2) ∂P := by simp only [abs_pow]
          _ ≤ _ := hVb _
      have := abs_remainder_combination_le (b := β ^ 2 / 2) hm hε hε1 (Real.sqrt_nonneg _)
        (hKv (m - 2)).le hT1 hT2 hT3
      rw [abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)] at this
      exact this

end SpinGlasses
