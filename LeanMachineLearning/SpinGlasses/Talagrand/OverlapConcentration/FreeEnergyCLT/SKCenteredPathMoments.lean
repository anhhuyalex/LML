/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.Binomial
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import LeanMachineLearning.SpinGlasses.SKFreeEnergyMoments
public import LeanMachineLearning.SpinGlasses.SKSmartPathProfileComp

/-!
# Centered moments of the free energy along the smart path (Talagrand, proof of Theorem 1.4.11)

Put `V(s) = A_N(s) - SK(s)`, where `A_N(s) = N⁻¹ log Z_N(s)` is the free energy along the smart
path and `SK(s) = skPathRS β h q s` the replica-symmetric value along it.  Eq. (1.125)
differentiates `𝔼 (A_N(s) - a)^k` for a *fixed* center `a`; the book then writes
`(d/dt) φ(t, SK(t)) = ∂_t φ(t, SK(t)) + SK'(t) ∂_a φ(t, SK(t))`.  Here the chain rule is proved by
expanding `(A - SK(s))^k` in powers of `SK(t) - SK(s)`: only the terms of order `0` and `1`
survive in the derivative at `s = t`.

## Main declarations

* `Finset.sum_choose_mul_deriv_pow_zero`: the evaluation of the resulting binomial sum.
* `SpinGlasses.exists_sk_smart_path_profile_centered`: the derivative of
  `s ↦ 𝔼 V(s)^k` along the path, with both endpoints.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eqs. (1.124)-(1.126).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The free energy `A_s` of the smart path is a measurable function of the disorder. -/
theorem measurable_smart_path_free_energy {N : ℕ} (β h q : ℝ)
    {F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ} {G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ}
    {A : ℝ → (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ}
    (hF : ∀ g σ, F g σ = (Real.sqrt N)⁻¹ * β *
      ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))
    (hG : ∀ z σ, G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ))
    (hA : ∀ t ω, A t ω = (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (Real.cos t * F ω.1 σ + Real.sin t * G ω.2 σ + h * ∑ i, ((σ i : ℤ) : ℝ))))
    (s : ℝ) : Measurable (A s) := by
  have e : A s = fun ω => (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp
      (Real.cos s * ((Real.sqrt N)⁻¹ * β * ∑ p : FinPairs N, ω.1 p * ((σ p.val.1 : ℤ) : ℝ) *
        ((σ p.val.2 : ℤ) : ℝ)) + Real.sin s * (β * Real.sqrt q * ∑ i, ω.2 i * ((σ i : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))) := by
    funext ω; rw [hA]; simp only [hF, hG]
  rw [e]
  refine Measurable.const_mul (Measurable.log (Finset.measurable_sum _ fun σ _ =>
    Real.measurable_exp.comp ?_)) _
  fun_prop

/-- Every power of `A_s - a` is integrable for the disorder measure, for every `s` and `a`
(Lemma 1.4.12 along the path). -/
theorem integrable_smart_path_free_energy_sub_pow {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q)
    (hq1 : q ≤ 1)
    {F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ} {G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ}
    {A : ℝ → (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ}
    (hF : ∀ g σ, F g σ = (Real.sqrt N)⁻¹ * β *
      ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))
    (hG : ∀ z σ, G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ))
    (hA : ∀ t ω, A t ω = (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (Real.cos t * F ω.1 σ + Real.sin t * G ω.2 σ + h * ∑ i, ((σ i : ℤ) : ℝ))))
    (s a : ℝ) (m : ℕ) :
    Integrable (fun ω => (A s ω - a) ^ m)
      ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  have h1 := (integral_pow_abs_smart_path_free_energy_sub_le hN β h q hq hq1 s m).1
  refine integrable_sub_pow_of_integrable_abs_pow
    (measurable_smart_path_free_energy β h q hF hG hA s)
    (c := ∫ ω', A s ω' ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1))) ?_ a
  convert h1 using 3
  all_goals simp only [hA, hF, hG]

/-- **Eq. (1.124)-(1.126) with the moving center `SK(s)`** (Talagrand, proof of Theorem 1.4.11).
With the smart-path free energy `A_s`, the overlap average `Q_s = ⟨(R_{1,2} - q)²⟩_s` and
`V_s = A_s - SK(s)`, the function `s ↦ 𝔼 V_s^k` has the derivative
`(β²/2) sin t cos t (𝔼 [k V^{k-1} (Q - (1-q)²) - N⁻¹ k (k-1) V^{k-2} (Q - q² - N⁻¹)] +
  k (1-q)² 𝔼 V^{k-1})`
at `t`, where the last term is `SK'(t) ∂_a φ` of the book.  Its value at `s = 0` is the `k`-th
moment about the replica-symmetric value in the SK model, and at `s = π/2` that of the decoupled
system. -/
theorem exists_sk_smart_path_profile_centered {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q)
    (hq1 : q ≤ 1) :
    ∃ (F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ) (G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
      (A Q : ℝ → (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ),
      (∀ g σ, F g σ = (Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ∧
      (∀ z σ, G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ)) ∧
      (∀ t ω, A t ω = (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (Real.cos t * F ω.1 σ + Real.sin t * G ω.2 σ + h * ∑ i, ((σ i : ℤ) : ℝ)))) ∧
      (∀ t ω, Q t ω = ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b =>
          Real.cos t * F ω.1 b + Real.sin t * G ω.2 b + h * ∑ i, ((b i : ℤ) : ℝ))) ∧
      ∀ k : ℕ,
      (∫ ω, (A 0 ω - rsFunctional β h q) ^ k
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) =
        ∫ g : FinPairs N → ℝ, ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
          Real.exp (F g σ + h * ∑ i, ((σ i : ℤ) : ℝ))) - rsFunctional β h q) ^ k
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ∧
      (∫ ω, (A (Real.pi / 2) ω - skPathRS β h q (Real.pi / 2)) ^ k
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) =
        ∫ z : Fin N → ℝ, (Real.log 2 + (N : ℝ)⁻¹ * ∑ i,
          Real.log (Real.cosh (β * Real.sqrt q * z i + h)) - skPathRS β h q (Real.pi / 2)) ^ k
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
      ∀ t, HasDerivAt (fun s => ∫ ω, (A s ω - skPathRS β h q s) ^ k
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)))
        (β ^ 2 / 2 * Real.sin t * Real.cos t *
          ((∫ ω, (((k : ℝ) * (A t ω - skPathRS β h q t) ^ (k - 1)) * (Q t ω - (1 - q) ^ 2) -
            (N : ℝ)⁻¹ * ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * (A t ω - skPathRS β h q t) ^ (k - 1 - 1)) *
              (Q t ω - q ^ 2 - (N : ℝ)⁻¹))
            ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin N => gaussianReal 0 1))) +
          (k : ℝ) * (1 - q) ^ 2 * ∫ ω, (A t ω - skPathRS β h q t) ^ (k - 1)
            ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin N => gaussianReal 0 1)))) t := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  obtain ⟨F, G, A, Q, hF, hG, hA, hQ, hpow⟩ := exists_sk_smart_path_profile_pow hN β h q hq
  refine ⟨F, G, A, Q, hF, hG, hA, hQ, fun k => ⟨?_, ?_, fun t => ?_⟩⟩
  · simpa only [skPathRS_zero] using (hpow (rsFunctional β h q) k).1
  · exact (hpow (skPathRS β h q (Real.pi / 2)) k).2.1
  set P := (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hint : ∀ s (a : ℝ) (m : ℕ), Integrable (fun ω => (A s ω - a) ^ m) P := fun s a m =>
    integrable_smart_path_free_energy_sub_pow hN β h q hq hq1 hF hG hA s a m
  set a0 := skPathRS β h q t with ha0
  set φ : ℕ → ℝ → ℝ := fun m s => ∫ ω, (A s ω - a0) ^ m ∂P with hφ
  set z : ℝ → ℝ := fun s => a0 - skPathRS β h q s with hz
  set D : ℕ → ℝ := fun m => β ^ 2 / 2 * Real.sin t * Real.cos t *
    ∫ ω, (((m : ℝ) * (A t ω - a0) ^ (m - 1)) * (Q t ω - (1 - q) ^ 2) -
      (N : ℝ)⁻¹ * ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * (A t ω - a0) ^ (m - 1 - 1)) *
        (Q t ω - q ^ 2 - (N : ℝ)⁻¹)) ∂P with hD_def
  have hD : ∀ m, HasDerivAt (φ m) (D m) t := fun m => (hpow a0 m).2.2 t
  have hz' : HasDerivAt z (β ^ 2 / 2 * (1 - q) ^ 2 * Real.sin t * Real.cos t) t := by
    refine ((hasDerivAt_skPathRS β h q t).const_sub a0).congr_deriv ?_
    ring
  have hzt : z t = 0 := by simp [hz, ha0]
  have hsum : ∀ s, ∫ ω, (A s ω - skPathRS β h q s) ^ k ∂P =
      ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (z s ^ i * φ (k - i) s) := fun s => by
    have e : ∀ ω, (A s ω - skPathRS β h q s) ^ k =
        ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (z s ^ i * (A s ω - a0) ^ (k - i)) := fun ω => by
      have : A s ω - skPathRS β h q s = z s + (A s ω - a0) := by simp only [hz]; ring
      rw [this, add_pow]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ => ((hint s a0 (k - i)).const_mul (z s ^ i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_const_mul]
  have hder : HasDerivAt (fun s => ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (z s ^ i * φ (k - i) s))
      (∑ i ∈ range (k + 1), (k.choose i : ℝ) * (((i : ℝ) * z t ^ (i - 1) *
        (β ^ 2 / 2 * (1 - q) ^ 2 * Real.sin t * Real.cos t)) * φ (k - i) t +
          z t ^ i * D (k - i))) t :=
    HasDerivAt.fun_sum fun i _ => ((hz'.pow i).mul (hD (k - i))).const_mul _
  rw [show (fun s => ∫ ω, (A s ω - skPathRS β h q s) ^ k ∂P) = fun s => ∑ i ∈ range (k + 1),
    (k.choose i : ℝ) * (z s ^ i * φ (k - i) s) from funext hsum]
  refine hder.congr_deriv ?_
  simp only [hzt]
  rw [sum_choose_mul_deriv_pow_zero k (β ^ 2 / 2 * (1 - q) ^ 2 * Real.sin t * Real.cos t)
    (fun m => φ m t) D]
  simp only [hD_def, hφ]
  ring

end SpinGlasses
