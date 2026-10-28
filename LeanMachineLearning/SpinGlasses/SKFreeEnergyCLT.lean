/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCenteredPathODE
public import LeanMachineLearning.SpinGlasses.SKSmartPathCLT
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumExpansion
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# The central limit theorem for the free energy (Talagrand, Theorem 1.4.11)

For `β² < 1/4`, a deterministic field `h`, and `q` the fixed point of the replica-symmetric
equation, the normalized free energy `A_N = N⁻¹ log Z_N(β, h)` of the SK model satisfies, for each
`k`, with `a(k)` the `k`-th moment of a standard Gaussian,
`𝔼 (A_N - SK(β, h))^k = N^{-k/2} a(k) b^{⌊k/2⌋} + O(N^{-(k+1)/2})`,
where `b = 𝔼 (log cosh Y)² - (𝔼 log cosh Y)² - β² q² / 2` and `Y = β √q z + h`.

The proof assembles: the differential equation of the centered moments along the smart path with
remainder `O(N^{-(m+1)/2})` (`exists_sk_centered_path_ode`, which uses Lemma 1.4.12, Theorem 1.4.10
along the path and the fourth overlap moment); the quantitative moment expansion of an i.i.d.
centered sum at the decoupled endpoint (`abs_integral_pow_avg_sub_le`, Eq. (1.122)); and the
induction on the degree (`clt_induction`).

**Scope.** The field `h` is deterministic (the case `c = 0` of the book's Gaussian field
`h_i = c y_i + d`); the centering is the replica-symmetric value `SK(β, h) = rsFunctional β h q`,
as in the book.

## Main declarations

* `SpinGlasses.sk_free_energy_clt`: Theorem 1.4.11, Eq. (1.109).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.4.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Every power of `log cosh (a x + b)` is integrable against the standard Gaussian. -/
theorem integrable_pow_log_cosh_affine_gaussianReal (a b : ℝ) (j : ℕ) :
    Integrable (fun x : ℝ => Real.log (Real.cosh (a * x + b)) ^ j) (gaussianReal 0 1) := by
  have hx : Integrable (fun x : ℝ => |x| ^ j) (gaussianReal 0 1) := by
    simpa only [abs_pow] using (integrable_pow_gaussianReal 0 1 j).abs
  have hcont : Continuous fun x : ℝ => Real.log (Real.cosh (a * x + b)) :=
    (Real.continuous_cosh.comp (by fun_prop : Continuous fun x : ℝ => a * x + b)).log
      fun x => (Real.cosh_pos _).ne'
  refine Integrable.mono' (((hx.const_mul (|a| ^ j)).add (integrable_const (|b| ^ j))).const_mul
    (2 ^ (j - 1))) (hcont.pow j).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have h0 := Real.log_cosh_nonneg (a * x + b)
  have h1 := Real.log_cosh_le_abs (a * x + b)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 j)]
  refine (pow_le_pow_left₀ h0 h1 j).trans ?_
  have := abs_add_pow_le (a * x) b j
  simpa only [Pi.add_apply, abs_mul, mul_pow] using this

/-- **Theorem 1.4.11 of Talagrand (Spin Glasses, Vol. I), Eq. (1.109): the central limit theorem
for the free energy** of the SK model with deterministic field.  For `β² < 1/4` and `q` with
`q = 𝔼 tanh² (β √q z + h)`, every `k` has a constant `C` such that for all `N > 0`,
`|𝔼 (N⁻¹ log Z_N - SK(β, h))^k - N^{-k/2} a(k) b^{⌊k/2⌋}| ≤ C N^{-(k+1)/2}`,
with `a(k) = 𝔼 g^k` the Gaussian moments, `SK(β, h) = rsFunctional β h q` and
`b = 𝔼 (log cosh Y)² - (𝔼 log cosh Y)² - β² q² / 2`, `Y = β √q z + h`. -/
theorem sk_free_energy_clt (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      |∫ g : FinPairs N → ℝ, ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
          Real.exp (skGibbsEnergy N β h g σ)) - rsFunctional β h q) ^ k
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) -
        ((Real.sqrt N)⁻¹) ^ k * (∫ x : ℝ, x ^ k ∂(gaussianReal 0 1)) *
          ((∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ^ 2 ∂(gaussianReal 0 1) -
            (∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1)) ^ 2) -
            β ^ 2 * q ^ 2 / 2) ^ (k / 2)| ≤ C * ((Real.sqrt N)⁻¹) ^ (k + 1) := by
  set L : ℝ → ℝ := fun x => Real.log (Real.cosh (β * Real.sqrt q * x + h)) with hL
  have hLi : ∀ j, Integrable (fun x => L x ^ j) (gaussianReal 0 1) := fun j =>
    integrable_pow_log_cosh_affine_gaussianReal _ _ j
  have hLm : Measurable L := (Real.continuous_cosh.comp
    (by fun_prop : Continuous fun x : ℝ => β * Real.sqrt q * x + h)).log
      (fun x => (Real.cosh_pos _).ne') |>.measurable
  set c0 : ℝ := ∫ x, L x ∂(gaussianReal 0 1) with hc0
  set V0 : ℝ := ∫ x, L x ^ 2 ∂(gaussianReal 0 1) - c0 ^ 2 with hV0
  set a : ℕ → ℝ := fun k => ∫ x : ℝ, x ^ k ∂(gaussianReal 0 1) with ha_def
  have ha0 : a 0 = 1 := by simp [ha_def]
  have ha1 : a 1 = 0 := by simp [ha_def, integral_id_gaussianReal]
  have ha : ∀ k, a (k + 2) = (k + 1) * a k := fun k => integral_pow_add_two_gaussianReal k
  -- the centered variable
  have hint : ∀ j, Integrable (fun x => (L x - c0) ^ j) (gaussianReal 0 1) := fun j => by
    refine Integrable.mono' (((hLi j).add (integrable_const (|c0| ^ j))).const_mul (2 ^ (j - 1)))
      ((hLm.sub_const c0).pow_const j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ L x := Real.log_cosh_nonneg _
    rw [Real.norm_eq_abs, ← abs_pow]
    have := abs_add_pow_le (L x) (-c0) j
    rw [← sub_eq_add_neg, abs_neg, abs_of_nonneg h0] at this
    simpa only [Pi.add_apply, abs_pow, abs_of_nonneg h0] using this
  have h1 : Integrable L (gaussianReal 0 1) := by simpa using hLi 1
  have h0 : ∫ x, (L x - c0) ∂(gaussianReal 0 1) = 0 := by
    rw [integral_sub h1 (integrable_const c0), integral_const, probReal_univ, one_smul, ← hc0,
      sub_self]
  have hσ : ∫ x, (L x - c0) ^ 2 ∂(gaussianReal 0 1) = V0 := by
    have e : ∀ x, (L x - c0) ^ 2 = L x ^ 2 - 2 * c0 * L x + c0 ^ 2 := fun x => by ring
    have i1 : Integrable (fun x => L x ^ 2 - 2 * c0 * L x) (gaussianReal 0 1) :=
      (hLi 2).sub (h1.const_mul _)
    simp_rw [e]
    rw [integral_add (f := fun x => L x ^ 2 - 2 * c0 * L x) (g := fun _ => c0 ^ 2) i1
      (integrable_const _), integral_sub (hLi 2) (h1.const_mul _), integral_const_mul,
      integral_const, probReal_univ, one_smul, ← hc0, hV0]
    ring
  obtain ⟨K, hK⟩ := exists_sk_centered_path_ode β h q hfix hβ
  have hex : ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      |∫ y : Fin N → ℝ, ((N : ℝ)⁻¹ * ∑ i, (L (y i) - c0)) ^ m
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) -
        ((Real.sqrt N)⁻¹) ^ m * a m * (∫ x, (L x - c0) ^ 2 ∂(gaussianReal 0 1)) ^ (m / 2)| ≤
      C * ((Real.sqrt N)⁻¹) ^ (m + 1) := fun m hm =>
    abs_integral_pow_avg_sub_le (f := fun x => L x - c0) hint h0 ha0 ha1 ha hm
  choose! Cd hCd0 hCd using hex
  obtain ⟨C, hC0, hC⟩ := exists_clt_const (β ^ 2 * q ^ 2) K Cd
  refine ⟨max (C k) 0, le_max_right _ _, fun N hN => ?_⟩
  obtain ⟨ψ, hψ0, hψ_0, hψ_π, hψ_ode⟩ := hK hN
  have hε : 0 < (Real.sqrt N)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 hN))
  set b : ℝ → ℝ := fun s => V0 + (-(β ^ 2 * q ^ 2 / 2)) * Real.cos s ^ 2 with hb_def
  have hb : ∀ s, HasDerivAt b (β ^ 2 * q ^ 2 * Real.sin s * Real.cos s) s := fun s =>
    (((Real.hasDerivAt_cos_sq s).const_mul (-(β ^ 2 * q ^ 2 / 2))).const_add V0).congr_deriv
      (by ring)
  have hdec : ∀ m, 1 ≤ m → |ψ m (Real.pi / 2) -
      ((Real.sqrt N)⁻¹) ^ m * a m * b (Real.pi / 2) ^ (m / 2)| ≤
        Cd m * ((Real.sqrt N)⁻¹) ^ (m + 1) := fun m hm => by
    have hbpi : b (Real.pi / 2) = ∫ x, (L x - c0) ^ 2 ∂(gaussianReal 0 1) := by
      simp [hb_def, hσ]
    rw [hbpi, hψ_π m]
    exact hCd m hm N hN
  have key := clt_induction (ε := (Real.sqrt N)⁻¹) (B := β ^ 2 * q ^ 2) hε ha0 ha1 ha hb hψ0
    (C_rem := K) (C_dec := Cd) (C := C) (by rw [hC0]) (fun m hm => hψ_ode m hm) hdec hC k
    (s := 0) ⟨le_rfl, by positivity⟩
  rw [hψ_0 k] at key
  have hb0 : b 0 = (∫ x, L x ^ 2 ∂(gaussianReal 0 1) - c0 ^ 2) - β ^ 2 * q ^ 2 / 2 := by
    simp [hb_def, hV0]
    ring
  rw [hb0] at key
  exact key.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end SpinGlasses
