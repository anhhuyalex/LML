/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenEvaluation
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenOddProduct
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenReducedEval
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenLeadingShift
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenProductTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.SpinDecorrelation.SKCovarianceSiteSymmetry
public import LeanMachineLearning.SpinGlasses.Panchenko.AldousHoover.DeFinetti
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.Optimization.Renormalization.Gaussian

/-!
# Hanen's Theorem (Talagrand, Theorem 1.11.1, Eq. (1.329))

This module states Hanen's Theorem on the non-Gaussian limit of the two-spin overlap fluctuation:
for $\beta < 1/2$,
$$\mathbb E(\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle)^k
= a(k) \left( \frac{\beta^2}{(N+1)(1 - \beta^2(1 - 2q + \hat q))} \right)^{k/2}
(\mathbb E \operatorname{ch}^{-2k} Y)^2 + O((N+1)^{-(k+1)/2}),$$
where $a(k) = \mathbb E g^k$ ($a(k) = (k-1)!!$ for $k$ even, $0$ for $k$ odd).
Both parities are proved (`sk_hanen_theorem_odd`, `sk_hanen_theorem_even`), and the theorem is
their assembly.

## Main declaration

* `SpinGlasses.sk_hanen_theorem`: Theorem 1.11.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- Odd standard Gaussian moments vanish. -/
theorem gaussian_moment_odd (m : ℕ) :
    ∫ x : ℝ, x ^ (2 * m + 1) ∂gaussianReal 0 1 = 0 := by
  simpa using Renormalization.integral_pow_gaussianReal_odd 1 m

/-- Even standard Gaussian moments are given by the double factorial $(2m-1)!!$. -/
theorem gaussian_moment_even (m : ℕ) :
    ∫ x : ℝ, x ^ (2 * m) ∂gaussianReal 0 1 =
      ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) := by
  have := Renormalization.integral_pow_gaussianReal_even 1 m
  simpa using this

/-- **Talagrand's Theorem 1.11.1 (A. Hanen), odd moments.**
For odd $k = 2m + 1$, the Gaussian moment $a(k)$ vanishes, so the $k$-th moment of
$\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$ is
purely $O((N+1)^{-(m+1)})$. -/
theorem sk_hanen_theorem_odd (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (i₁ i₂ : Fin (N + 1)) (_ : i₁ ≠ i₂),
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      |∫ g : FinPairs (N + 1) → ℝ,
          (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) * (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)) -
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) ∂(Measure.count.tilted (E g))) *
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)))) ^ (2 * m + 1)
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      K / ((N : ℝ) + 1) ^ ((((2 * m + 2 : ℕ) : ℝ)) / 2) := by
  obtain ⟨K, hK, hbound⟩ := sk_hanen_odd_spin_product_bound β₀ hβ₀ (2 * (2 * m + 1)) m
  refine ⟨K, hK, ?_⟩
  intro β h q hfix hβ N i₁ i₂ hij
  cases N with
  | zero => exact False.elim (hij (Fin.ext (by omega)))
  | succ N =>
    intro E
    let i0 : Fin (N + 2) := (Fin.last N).castSucc
    let j0 : Fin (N + 2) := Fin.last (N + 1)
    let a : Fin 2 → Fin (N + 2) := ![i0, j0]
    let b : Fin 2 → Fin (N + 2) := ![i₁, i₂]
    have ha : Function.Injective a := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · have hv := congrArg Fin.val hxy
        change N = N + 1 at hv
        omega
      · have hv := congrArg Fin.val hxy
        change N + 1 = N at hv
        omega
      · rfl
    have hb : Function.Injective b := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact False.elim (hij hxy)
      · exact False.elim (hij hxy.symm)
      · rfl
    obtain ⟨perm, hperm⟩ := exists_equiv_comp_eq ha hb
    have hpermi : perm i0 = i₁ := hperm 0
    have hpermj : perm j0 = i₂ := hperm 1
    have hsym := sk_covariance_pow_site_perm (N + 1) (2 * m + 1) β h perm i0 j0
    simp only [hpermi, hpermj] at hsym
    rw [hsym]
    simp_rw [cov_pow_eq_two_inv_pow_mul_integral, integral_const_mul, Finset.prod_mul_distrib]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (2 * m + 1))]
    let pm : Fin (2 * m + 1) → Fin (2 * (2 * m + 1)) × Fin (2 * (2 * m + 1)) :=
      fun w => (finPair0 w, finPair1 w)
    have hdisj : ∀ u v : Fin (2 * m + 1), u ≠ v →
        (pm u).1 ≠ (pm v).1 ∧ (pm u).1 ≠ (pm v).2 ∧
        (pm u).2 ≠ (pm v).1 ∧ (pm u).2 ≠ (pm v).2 := by
      intro u v huv
      exact ⟨finPair0_injective.ne huv, finPair0_ne_finPair1_of_ne u v,
        Ne.symm (finPair0_ne_finPair1_of_ne v u), finPair1_injective.ne huv⟩
    have hprod := hbound β h q hfix hβ N pm hdisj
    rw [skCavityPathMean_one] at hprod
    have he : (((2 * m + 2 : ℕ) : ℝ) / 2) = (m + 1 : ℕ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
    calc
      _ ≤ _ := mul_le_of_le_one_left (abs_nonneg _)
        (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num))
      _ ≤ _ := by
        simpa only [pm, finPair0, finPair1, i0, j0, Nat.cast_succ,
          add_assoc, one_add_one_eq_two] using hprod


/-- **Talagrand's Theorem 1.11.1 (A. Hanen), even moments.**
For even $k = 2p$, $a(2p) = (2p-1)!!$, and the $2p$-th moment of
$\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$ is
$a(2p) D_{\mathrm{var}}^p (\mathbb E \operatorname{ch}^{-4p} Y)^2 + O((N+1)^{-(2p+1)/2})$. -/
theorem sk_hanen_theorem_even (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (i₁ i₂ : Fin (N + 1)) (_ : i₁ ≠ i₂),
      let α : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let D_var : ℝ := β ^ 2 / ((N + 1 : ℝ) * (1 - β ^ 2 * α))
      let a_2p : ℝ := ∫ x : ℝ, x ^ (2 * p) ∂gaussianReal 0 1
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      |∫ g : FinPairs (N + 1) → ℝ,
          (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) * (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)) -
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) ∂(Measure.count.tilted (E g))) *
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)))) ^ (2 * p)
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) -
        a_2p * (D_var) ^ p *
          (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1) ^ 2| ≤
      K / ((N : ℝ) + 1) ^ ((((2 * p + 1 : ℕ) : ℝ)) / 2) := by
  obtain ⟨K1, hK1, hb1⟩ := sk_hanen_spin_product_taylor β₀ hβ₀ (2 * (2 * p)) (2 * p)
  obtain ⟨K4, hK4, hb4⟩ := sk_hanen_reduced_full_rect_eval β₀ hβ₀ p (2 * (2 * p))
  obtain ⟨K5, hK5, hb5⟩ := sk_hanen_leading_term_shift β₀ hβ₀ p
  refine ⟨K1 + (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * p)))) : ℝ) *
    (2 ^ (((2 * p + 1 : ℕ) : ℝ) / 2) * K4 + K5) + 1, by positivity, ?_⟩
  intro β h q hfix hβ N i₁ i₂ hij
  cases N with
  | zero => exact False.elim (hij (Fin.ext (by omega)))
  | succ N =>
    intro α D_var a_2p E
    let i0 : Fin (N + 2) := (Fin.last N).castSucc
    let j0 : Fin (N + 2) := Fin.last (N + 1)
    let a : Fin 2 → Fin (N + 2) := ![i0, j0]
    let b : Fin 2 → Fin (N + 2) := ![i₁, i₂]
    have ha : Function.Injective a := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · have hv := congrArg Fin.val hxy
        change N = N + 1 at hv
        omega
      · have hv := congrArg Fin.val hxy
        change N + 1 = N at hv
        omega
      · rfl
    have hb : Function.Injective b := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact False.elim (hij hxy)
      · exact False.elim (hij hxy.symm)
      · rfl
    obtain ⟨perm, hperm⟩ := exists_equiv_comp_eq ha hb
    have hpermi : perm i0 = i₁ := hperm 0
    have hpermj : perm j0 = i₂ := hperm 1
    have hsym := sk_covariance_pow_site_perm (N + 1) (2 * p) β h perm i0 j0
    simp only [hpermi, hpermj] at hsym
    rw [hsym]
    simp_rw [cov_pow_eq_two_inv_pow_mul_integral, integral_const_mul, Finset.prod_mul_distrib]
    -- the replica pairs
    let pm : Fin (2 * p) → Fin (2 * (2 * p)) × Fin (2 * (2 * p)) :=
      fun w => (finPair0 w, finPair1 w)
    have hxy : ∀ w, (pm w).1 ≠ (pm w).2 := fun w => finPair0_ne_finPair1 w
    have hdisj : ∀ u v : Fin (2 * p), u ≠ v →
        (pm u).1 ≠ (pm v).1 ∧ (pm u).1 ≠ (pm v).2 ∧
        (pm u).2 ≠ (pm v).1 ∧ (pm u).2 ≠ (pm v).2 := by
      intro u v huv
      exact ⟨finPair0_injective.ne huv, finPair0_ne_finPair1_of_ne u v,
        Ne.symm (finPair0_ne_finPair1_of_ne v u), finPair1_injective.ne huv⟩
    -- the Taylor step
    have hT := hb1 β h q hfix hβ N pm hdisj
    dsimp only at hT
    have hp : (2 * p + 1) / 2 = p := by omega
    rw [hp] at hT
    -- the derivative of order `p` at the decoupled endpoint (Theorem 1.11.9)
    have hq := fixedPoint_mem_Icc hfix
    have hder := sk_hanen_pairing_derivative (N + 1) p (2 * (2 * p)) β q h hq pm hxy hdisj
      (fun ρ => ∏ w : Fin (2 * p), ((ρ (pm w).1 (Fin.last N) : ℝ) -
        (ρ (pm w).2 (Fin.last N) : ℝ))) (fun _ => 1) (fun _ _ _ _ => rfl)
    simp only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] at hder
    -- the Wick sum splits into the pairings
    have hW : (∫ g' : FinPairs (N + 1) → ℝ, ∫ ρ : Fin (2 * (2 * p)) → Fin (N + 1) → ℤˣ,
        (∏ w, ((ρ (pm w).1 (Fin.last N) : ℝ) - (ρ (pm w).2 (Fin.last N) : ℝ))) *
          Renormalization.wick (fun u v => skCavityRectTrunc (N + 1) (2 * (2 * p)) p q pm u v ρ)
            (univ : Finset (Fin (2 * p)))
        ∂(Measure.pi fun _ : Fin (2 * (2 * p)) =>
          Measure.count.tilted (skCavityOldEnergy (N + 1) β h g'))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * p))),
        ∫ g' : FinPairs (N + 1) → ℝ, ∫ ρ : Fin (2 * (2 * p)) → Fin (N + 1) → ℤˣ,
          (∏ w, ((ρ (pm w).1 (Fin.last N) : ℝ) - (ρ (pm w).2 (Fin.last N) : ℝ))) *
            P'.blockProduct (Renormalization.pairWeight fun u v =>
              skCavityRectTrunc (N + 1) (2 * (2 * p)) p q pm u v ρ)
          ∂(Measure.pi fun _ : Fin (2 * (2 * p)) =>
            Measure.count.tilted (skCavityOldEnergy (N + 1) β h g'))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
      rw [← skCavityPathMean_zero_old (N + 1) (2 * (2 * p)) β q h (fun ρ =>
        (∏ w, ((ρ (pm w).1 (Fin.last N) : ℝ) - (ρ (pm w).2 (Fin.last N) : ℝ))) *
          Renormalization.wick (fun u v => skCavityRectTrunc (N + 1) (2 * (2 * p)) p q pm u v ρ)
            (univ : Finset (Fin (2 * p))))]
      have hsum := skCavityPathMean_finset_sum (N + 1) (2 * (2 * p)) β q h 0
        (univ : Finset (Finpartition.Pairing (univ : Finset (Fin (2 * p))))) (fun _ => 1)
        (fun P' σ => (∏ w, ((σ (pm w).1 (Fin.last N).castSucc : ℝ) -
          (σ (pm w).2 (Fin.last N).castSucc : ℝ))) *
            P'.blockProduct (Renormalization.pairWeight fun u v =>
              skCavityRectTrunc (N + 1) (2 * (2 * p)) p q pm u v (fun r i => σ r i.castSucc)))
      simp only [one_mul] at hsum
      have hpt : (fun σ : Fin (2 * (2 * p)) → Fin (N + 1 + 1) → ℤˣ =>
          (∏ w, ((σ (pm w).1 (Fin.last N).castSucc : ℝ) - (σ (pm w).2 (Fin.last N).castSucc : ℝ))) *
            Renormalization.wick (fun u v => skCavityRectTrunc (N + 1) (2 * (2 * p)) p q pm u v
              (fun r i => σ r i.castSucc)) (univ : Finset (Fin (2 * p)))) =
          fun σ => ∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * p))),
            (∏ w, ((σ (pm w).1 (Fin.last N).castSucc : ℝ) -
              (σ (pm w).2 (Fin.last N).castSucc : ℝ))) *
            P'.blockProduct (Renormalization.pairWeight fun u v =>
              skCavityRectTrunc (N + 1) (2 * (2 * p)) p q pm u v (fun r i => σ r i.castSucc)) := by
        funext σ
        simp only [Renormalization.wick, Finpartition.pairingSum, Finset.mul_sum]
      rw [hpt, hsum]
      refine Finset.sum_congr rfl fun P' _ => ?_
      exact skCavityPathMean_zero_old (N + 1) (2 * (2 * p)) β q h (fun ρ =>
        (∏ w, ((ρ (pm w).1 (Fin.last N) : ℝ) - (ρ (pm w).2 (Fin.last N) : ℝ))) *
          P'.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc (N + 1) (2 * (2 * p)) p q pm u v ρ))
    rw [hW] at hder
    -- the reduced system
    have hβ4 : 4 * β ^ 2 < 1 := lt_of_le_of_lt (by nlinarith) hβ₀
    obtain ⟨qm, hqm, hfixm, hshift⟩ := exists_fixedPoint_cavity_of_sq_lt β h q hβ4 hfix (N + 1)
    set θ : ℝ := ((N : ℝ) + 1) / ((N : ℝ) + 2) with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    set βm : ℝ := β * Real.sqrt θ with hβm
    have hfixm' : ∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 2 ∂gaussianReal 0 1 = qm := by
      simpa only [βm, θ, Nat.cast_succ, add_assoc, one_add_one_eq_two] using hfixm
    have hβm2 : βm ^ 2 ≤ β₀ ^ 2 := by
      rw [hβm, mul_pow, Real.sq_sqrt hθ0]
      exact (mul_le_mul_of_nonneg_left hθ1 (sq_nonneg β)).trans (by simpa using hβ)
    have hcoef : (Real.sqrt ((N : ℝ) + 1))⁻¹ * βm = (Real.sqrt ((N : ℝ) + 2))⁻¹ * β := by
      have hc := sk_beta_minus_coefficient (N + 1) β (by omega)
      simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two, βm, θ] using hc
    have hqq : |q - qm| ≤ 1 / ((N : ℝ) + 2) := by
      simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using hshift
    have hE5 := hb5 β h q qm N hfix hfixm' hβ hqq
    dsimp only at hE5
    have hE4 := fun P' : Finpartition.Pairing (univ : Finset (Fin (2 * p))) =>
      hb4 β h βm q qm hfixm' hβm2 N hcoef P' (fun w => (pm w).1) (fun w => (pm w).2)
        (fun w => hxy w) (fun u v huv => hdisj u v huv)
    set Jz : ℝ := ∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1
      with hJz
    have hJ : |Jz| ≤ 1 := abs_integral_gaussianReal_le_one _ fun z => by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (Real.one_le_cosh _))
    have hcardR : (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * p)))) : ℝ) =
        a_2p := by
      have h1 := Finpartition.Pairing.card_mul_two_pow_mul_factorial p
        (univ : Finset (Fin (2 * p))) (by simp)
      have h2 : (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * p)))) : ℝ) *
          2 ^ p * (p.factorial : ℝ) = ((2 * p).factorial : ℝ) := by
        rw [mul_assoc]; exact_mod_cast h1
      have h3 := gaussian_moment_even p
      change _ = ∫ x : ℝ, x ^ (2 * p) ∂gaussianReal 0 1
      rw [h3, eq_div_iff (by positivity)]
      linarith
    have hα' := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
    simp only [integral_tanh_pow_mul_z_sqrt_eq] at hα'
    have hD : 1 - β ^ 2 * α ≠ 0 := by
      have := hα'.2
      have := hα'.1
      nlinarith [sq_nonneg β]
    have hc1 : ((2 : ℝ)⁻¹) ^ (2 * p) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have ht0 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hexp : (((2 * p : ℕ) : ℝ) + 1) / 2 = (((2 * p + 1 : ℕ) : ℝ) / 2) := by
      push_cast; ring
    rw [hexp] at hT
    have hscale : K4 / ((N : ℝ) + 1) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) ≤
        2 ^ (((2 * p + 1 : ℕ) : ℝ) / 2) * K4 / ((N : ℝ) + 2) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) := by
      have he0 : (0 : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) / 2 := by positivity
      have hs : ((N : ℝ) + 2) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) ≤
          2 ^ (((2 * p + 1 : ℕ) : ℝ) / 2) * ((N : ℝ) + 1) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) := by
        rw [← Real.mul_rpow (by norm_num) hN1.le]
        exact Real.rpow_le_rpow ht0.le (by linarith [Nat.cast_nonneg (α := ℝ) N]) he0
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hN1 _) (Real.rpow_pos_of_pos ht0 _)]
      calc K4 * ((N : ℝ) + 2) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) ≤
          K4 * (2 ^ (((2 * p + 1 : ℕ) : ℝ) / 2) * ((N : ℝ) + 1) ^ (((2 * p + 1 : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hs hK4.le
        _ = _ := by ring
    have hkey := hanen_even_assemble (p := p) (b := β ^ 2) (J := Jz)
      (c := (2 : ℝ)⁻¹ ^ (2 * p))
      (card := (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * p)))) : ℝ))
      (e2 := (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * p)))) : ℝ) *
        (2 ^ (((2 * p + 1 : ℕ) : ℝ) / 2) * K4 / ((N : ℝ) + 2) ^ (((2 * p + 1 : ℕ) : ℝ) / 2)))
      (hb := sq_nonneg β) (hb4 := by nlinarith) (hJ := hJ) (hc := by positivity) (hc1 := hc1)
      (hcard := Nat.cast_nonneg _) (h1 := hT) (h2 := hder) (h4 := hE5)
      (h3 := abs_sum_sub_card_mul_le _ _ _ fun P' => (hE4 P').trans hscale)
    have hTeq : a_2p * D_var ^ p * Jz ^ 2 = (2 : ℝ)⁻¹ ^ (2 * p) *
        ((β ^ 2) ^ p * Jz * ((Fintype.card (Finpartition.Pairing
          (univ : Finset (Fin (2 * p)))) : ℝ) *
          ((4 * (((N : ℝ) + 2)⁻¹ + β ^ 2 * ((α / (1 - β ^ 2 * α)) / ((N : ℝ) + 2)))) ^ p *
            Jz))) := by
      have hid := hanen_even_identity p ((N : ℝ) + 2) (β ^ 2) α (α / (1 - β ^ 2 * α)) Jz
        (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * p)))) : ℝ) a_2p ht0 hD rfl
        hcardR
      rw [← hid]
      have hDv : D_var = β ^ 2 / (((N : ℝ) + 2) * (1 - β ^ 2 * α)) := by
        simp only [D_var]; push_cast; ring_nf
      rw [hDv]
    rw [hTeq]
    have ht : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 2 := by push_cast; ring
    refine le_trans (le_of_eq ?_) (hkey.trans ?_)
    · rw [skCavityPathMean_one]
      rfl
    · rw [ht]
      exact hanen_even_final K1 K4 K5 _ _ _ (Real.rpow_pos_of_pos ht0 _)

/-- **Talagrand's Theorem 1.11.1 (A. Hanen, Eq. (1.329)).** Non-Gaussian limit of the two-spin
overlap fluctuation: for $\beta^2 \le \beta_0^2 < 1/4$, the $k$-th moment of
$\langle \sigma_1 \sigma_2 \rangle - \langle \sigma_1 \rangle \langle \sigma_2 \rangle$ is
$a(k) (\beta^2 / ((N+1)(1 - \beta^2(1 - 2q + \hat q))))^{k/2}$ times
$(\mathbb E \operatorname{ch}^{-2k} Y)^2$ up to $O((N+1)^{-(k+1)/2})$,
uniformly in the high-temperature regime.

The proof reduces by parity (`Nat.even_or_odd k`) to the odd moment bound
`sk_hanen_theorem_odd` (where $a(k) = 0$ by `gaussian_moment_odd`) and the even moment formula
`sk_hanen_theorem_even` (where $a(2p) = (2p-1)!!$ by `gaussian_moment_even`). -/
theorem sk_hanen_theorem (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (i₁ i₂ : Fin (N + 1)) (_ : i₁ ≠ i₂),
      let α : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let D_var : ℝ := β ^ 2 / ((N + 1 : ℝ) * (1 - β ^ 2 * α))
      let a_k : ℝ := ∫ x : ℝ, x ^ k ∂gaussianReal 0 1
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      |∫ g : FinPairs (N + 1) → ℝ,
          (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) * (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)) -
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₁ : ℝ) ∂(Measure.count.tilted (E g))) *
            (∫ σ : Fin (N + 1) → ℤˣ, (σ i₂ : ℝ) ∂(Measure.count.tilted (E g)))) ^ k
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) -
        a_k * (D_var) ^ (k / 2) *
          (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * k))⁻¹ ∂gaussianReal 0 1) ^ 2| ≤
      K / ((N : ℝ) + 1) ^ ((((k + 1 : ℕ) : ℝ)) / 2) := by
  rcases Nat.even_or_odd k with ⟨p, rfl⟩ | ⟨m, rfl⟩
  · have h2p : p + p = 2 * p := by omega
    simp_rw [h2p]
    obtain ⟨K, hKpos, hK⟩ := sk_hanen_theorem_even β₀ hβ₀ p
    refine ⟨K, hKpos, ?_⟩
    intro β h q hfix hβ N i₁ i₂ hne
    have hp : 2 * p / 2 = p := by omega
    have h2k : 2 * (2 * p) = 4 * p := by omega
    rw [hp, h2k]
    exact hK β h q hfix hβ N i₁ i₂ hne
  · obtain ⟨K, hKpos, hK⟩ := sk_hanen_theorem_odd β₀ hβ₀ m
    refine ⟨K, hKpos, ?_⟩
    intro β h q hfix hβ N i₁ i₂ hne α D_var a_k E
    have ha : a_k = 0 := gaussian_moment_odd m
    have hzero : a_k * D_var ^ ((2 * m + 1) / 2) *
        (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * (2 * m + 1)))⁻¹
          ∂gaussianReal 0 1) ^ 2 = 0 := by
      rw [ha, zero_mul, zero_mul]
    rw [hzero, sub_zero]
    have hexp : ((((2 * m + 1 + 1 : ℕ) : ℝ)) / 2) = ((((2 * m + 2 : ℕ) : ℝ)) / 2) := by
      congr 2
    rw [hexp]
    exact hK β h q hfix hβ N i₁ i₂ hne

end SpinGlasses
