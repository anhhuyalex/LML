/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.SpinDecorrelation.SpinDecorrelation
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.OverlapConcentration
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.EmpiricalVarianceHighMoments
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTilted
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianInterpolationReplica

/-!
# Spin correlation decay, overlap variances, and empirical-variance concentration for the perceptron

Chapter 2 analogues of the Section 1.14 correlation and variance estimates (Eqs. (1.412)--(1.414)),
together with the variance of the empirical derivative product of Section 2.5. These consequences
are **not printed in Talagrand Section 2.6**; they parallel `SKCorrelationDecay.lean` line by line,
instantiating the model-independent Proposition 1.4.14 (`integral_sq_prod_sub_prod_le_finset` in
`SpinDecorrelation.lean`), the perceptron overlap bound `integral_perceptron_overlap_sub_sq_le`
(Theorem 2.4.1), and the `k = 1` case of `integral_perceptron_empirical_variance_pow_le`
(Theorem 2.5.2).

## Main declarations

* `SpinGlasses.perceptron_gibbsWeight_siteSymmetric`: the perceptron Gibbs weights satisfy the
  nonnegativity, normalization, measurability, and site-permutation symmetry hypotheses of
  Proposition 1.4.14 under any row-wise sigma-finite disorder law.
* `SpinGlasses.perceptron_correlation_decay_le`: truncated multi-site spin correlation bound
  `𝔼 (⟨∏_{i ∈ S} σᵢ⟩ - ∏_{i ∈ S} ⟨σᵢ⟩)² ≤ spinDecorrConst S.card * L / (N + 1)`.
* `SpinGlasses.perceptron_gibbs_pair_covariance_sq_le`: pairwise spin covariance decay
  `𝔼 (⟨σᵢ σⱼ⟩ - ⟨σᵢ⟩⟨σⱼ⟩)² ≤ L' / (N + 1)` for `i ≠ j` (with `L' = spinDecorrConst 2 * L`).
* `SpinGlasses.perceptron_expected_gibbs_overlap_sub_sq_le`,
  `SpinGlasses.perceptron_var_gibbs_overlap_le`,
  `SpinGlasses.perceptron_expected_gibbs_var_overlap_le`: mean-square deviation from `q`, disorder
  variance `Var_g(⟨R₁,₂⟩_g) ≤ L / (N + 1)`, and expected Gibbs variance
  `𝔼 ⟨(R₁,₂ - ⟨R₁,₂⟩_g)²⟩_g ≤ L / (N + 1)`.
* `SpinGlasses.perceptron_expected_gibbs_empirical_variance_sub_sq_le`,
  `SpinGlasses.perceptron_var_gibbs_empirical_variance_le`,
  `SpinGlasses.perceptron_expected_gibbs_var_empirical_variance_le`: mean-square deviation from `r`,
  disorder variance `Var_g(⟨C⟩_g) ≤ α L / (N + 1)`, and expected Gibbs variance
  `𝔼 ⟨(C - ⟨C⟩_g)²⟩_g ≤ α L / (N + 1)` for `C(g, σ¹, σ²) = (N + 1)⁻¹ ∑_{k < M} u'(S_k¹) u'(S_k²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped BigOperators NNReal ENNReal Matrix

namespace SpinGlasses

/-! ### Measurability helpers for the perceptron constraint field and energy -/

private lemma measurable_perceptron_field {L M : ℕ} (τ : Fin L → ℤˣ) (k : Fin M) :
    Measurable fun g : Fin M → Fin L → ℝ =>
      (Real.sqrt (L : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ) := by
  have hk : Measurable fun g : Fin M → Fin L → ℝ => g k := measurable_pi_apply k
  have hsum : Measurable fun g : Fin M → Fin L → ℝ => ∑ i : Fin L, g k i * ((τ i : ℤ) : ℝ) :=
    Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hk).mul measurable_const
  exact hsum.const_mul _

private lemma measurable_perceptron_energy {L M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (τ : Fin L → ℤˣ) :
    Measurable fun g : Fin M → Fin L → ℝ =>
      ∑ k : Fin M, u ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)) :=
  Finset.measurable_sum _ fun k _ => hu.comp (measurable_perceptron_field τ k)

/-! ### Site symmetry of the perceptron Gibbs weights and correlation decay -/

/-- **The perceptron Gibbs weights as a site-symmetric random state.** For any measurable potential
`u : ℝ → ℝ` and any row-wise sigma-finite coordinate laws `μ : Fin M → Measure ℝ`, the Gibbs weights
`exp (E g σ) / ∑_b exp (E g b)` of `E g τ = ∑_k u ((√L)⁻¹ ∑_i g_{k,i} τ_i)` are nonnegative, sum to
one, depend measurably on `g`, and their law under `⨂_k ⨂_i μ_k` is invariant under every site
permutation `π : Equiv.Perm (Fin L)`. -/
theorem perceptron_gibbsWeight_siteSymmetric {L M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (μ : Fin M → Measure ℝ) [∀ k, SigmaFinite (μ k)]
    (E : (Fin M → Fin L → ℝ) → (Fin L → ℤˣ) → ℝ)
    (hE : ∀ g τ, E g τ = ∑ k, u ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))) :
    (∀ g σ, 0 ≤ Real.exp (E g σ) / ∑ b, Real.exp (E g b)) ∧
      (∀ g, ∑ σ, Real.exp (E g σ) / ∑ b, Real.exp (E g b) = 1) ∧
      (∀ σ, Measurable fun g => Real.exp (E g σ) / ∑ b, Real.exp (E g b)) ∧
      ∀ π : Equiv.Perm (Fin L), ∃ φ : (Fin M → Fin L → ℝ) → (Fin M → Fin L → ℝ),
        MeasurePreserving φ (Measure.pi fun k : Fin M => Measure.pi fun _ : Fin L => μ k)
          (Measure.pi fun k : Fin M => Measure.pi fun _ : Fin L => μ k) ∧
        ∀ g σ, Real.exp (E (φ g) σ) / ∑ b, Real.exp (E (φ g) b) =
          Real.exp (E g (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) σ)) / ∑ b, Real.exp (E g b) := by
  have hZ : ∀ g, 0 < ∑ b, Real.exp (E g b) := fun g =>
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hEm : ∀ τ, Measurable fun g => E g τ := fun τ => by
    simp only [hE]
    exact measurable_perceptron_energy hu τ
  refine ⟨fun g σ => div_nonneg (Real.exp_pos _).le (hZ g).le,
    fun g => by rw [← Finset.sum_div, div_self (hZ g).ne'],
    fun σ => (Real.measurable_exp.comp (hEm σ)).div
      (Finset.measurable_sum _ fun b _ => Real.measurable_exp.comp (hEm b)),
    fun π => ⟨fun g k i => g k (π.symm i), measurePreserving_pi_pi_comp_perm μ π.symm,
      fun g σ => ?_⟩⟩
  have hEc : ∀ τ : Fin L → ℤˣ,
      E (fun k i => g k (π.symm i)) τ = E g (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) τ) :=
    fun τ => by
      rw [hE, hE]
      refine Finset.sum_congr rfl fun k _ => congrArg u (congrArg _ ?_)
      have hsum := Equiv.sum_comp π.symm
        (fun j => g k j * (((Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) τ) j : ℤ) : ℝ))
      refine Eq.trans ?_ hsum
      exact Finset.sum_congr rfl fun i _ => by simp [Equiv.arrowCongr_apply]
  rw [hEc σ]
  congr 1
  simp_rw [hEc]
  exact Equiv.sum_comp (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ)) fun b => Real.exp (E g b)

/-- **Truncated spin correlation decay for the perceptron (analogue of Eq. (1.132)).**
Given `D ∈ ℝ`, there exist constants `K ≥ 0` and `L ≥ 0` (independent of `N, M, u, q, r, S`) such
that under (2.7), `(M / (N + 1)) * K ≤ 1`, and `(q, r)` solving (2.68), every finite set `S` of
sites in `Fin (N + 1)` satisfies
`𝔼 (⟨∏_{i ∈ S} σᵢ⟩ - ∏_{i ∈ S} ⟨σᵢ⟩)² ≤ spinDecorrConst S.card * (L / (N + 1))`. -/
theorem perceptron_correlation_decay_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        (S : Finset (Fin (N + 1))),
        ∫ g : Fin M → Fin (N + 1) → ℝ,
            (∫ σ : Fin (N + 1) → ℤˣ, ∏ i ∈ S, ((σ i : ℤ) : ℝ)
                ∂((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))) -
              ∏ i ∈ S, ∫ σ : Fin (N + 1) → ℤˣ, ((σ i : ℤ) : ℝ)
                ∂((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ^ 2
            ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
          spinDecorrConst S.card * (L / ((N : ℝ) + 1)) := by
  obtain ⟨K, L, hK0, hL0, hov⟩ := integral_perceptron_overlap_sub_sq_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr S
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := hq ▸ integral_tanh_sq_sqrt_mem_Icc r
  have hq_abs : |q| ≤ 1 := abs_le.2 ⟨by linarith [hq_mem.1], hq_mem.2⟩
  obtain ⟨E, hE⟩ : ∃ E : (Fin M → Fin (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ,
      ∀ g τ, E g τ = ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  simp only [← hE]
  obtain ⟨hw0, hw1, hwm, hsym⟩ := perceptron_gibbsWeight_siteSymmetric hu.measurable
    (fun _ : Fin M => gaussianReal 0 1) E hE
  have habs : ∀ (i : Fin (N + 1)) (σ : Fin (N + 1) → ℤˣ), |((σ i : ℤ) : ℝ)| ≤ 1 :=
    fun _ _ => abs_units_cast_le_one _
  have hint := integral_sq_prod_sub_prod_le_finset
    (P := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
    (ξ := fun (i : Fin (N + 1)) (σ : Fin (N + 1) → ℤˣ) => ((σ i : ℤ) : ℝ))
    (w := fun g σ => Real.exp (E g σ) / ∑ b, Real.exp (E g b))
    (Nat.succ_pos N) habs hw0 hw1 hwm
    (fun π => Equiv.arrowCongr π.symm (Equiv.refl ℤˣ)) (fun π i σ => by simp) hsym hq_abs S
  have hov_step := hov N M hd hb hα hq hr
  simp only [← hE] at hov_step
  have hov_weights :
      ∫ g : Fin M → Fin (N + 1) → ℝ, ∑ x, ∑ y, Real.exp (E g x) / (∑ b, Real.exp (E g b)) *
          (Real.exp (E g y) / ∑ b, Real.exp (E g b)) *
          (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q) ^ 2
          ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
        L / ((N : ℝ) + 1) := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun g => ?_))) hov_step
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    simp_rw [hcast]
    exact (integral_pi_fin_two_count_tilted (E g) fun x y =>
      (((N : ℝ) + 1)⁻¹ * ∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q) ^ 2).symm
  simp only [integral_count_tilted]
  exact hint.trans (mul_le_mul_of_nonneg_left hov_weights (spinDecorrConst_nonneg _))

/-- **Pairwise spin covariance decay for the perceptron (analogue of Eq. (1.412)).**
Given `D ∈ ℝ`, there exist constants `K ≥ 0` and `L' ≥ 0` (chosen before `N, M, u, q, r, i, j`,
namely `L' = spinDecorrConst 2 * L` where `L` is the overlap constant of Theorem 2.4.1) such that
whenever `u` satisfies (2.7), `(M / (N + 1)) * K ≤ 1`, `(q, r)` solves (2.68), and `i ≠ j` in
`Fin (N + 1)`,
`𝔼 (⟨σᵢ σⱼ⟩_g - ⟨σᵢ⟩_g ⟨σⱼ⟩_g)² ≤ L' / (N + 1)`. -/
theorem perceptron_gibbs_pair_covariance_sq_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        {i j : Fin (N + 1)} (_hij : i ≠ j),
        ∫ g : Fin M → Fin (N + 1) → ℝ,
            (∫ σ : Fin (N + 1) → ℤˣ, ((σ i : ℤ) : ℝ) * ((σ j : ℤ) : ℝ)
                ∂((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ l, g k l * ((τ l : ℤ) : ℝ))) -
              (∫ σ : Fin (N + 1) → ℤˣ, ((σ i : ℤ) : ℝ)
                ∂((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ l, g k l * ((τ l : ℤ) : ℝ)))) *
              (∫ σ : Fin (N + 1) → ℤˣ, ((σ j : ℤ) : ℝ)
                ∂((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ l, g k l * ((τ l : ℤ) : ℝ))))) ^ 2
            ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
          L / ((N : ℝ) + 1) := by
  obtain ⟨K, L, hK0, hL0, hcorr⟩ := perceptron_correlation_decay_le D
  refine ⟨K, spinDecorrConst 2 * L, hK0, mul_nonneg (spinDecorrConst_nonneg 2) hL0, ?_⟩
  intro N M u hd hb hα q r hq hr i j hij
  have h := hcorr N M hd hb hα hq hr {i, j}
  rw [card_pair hij, mul_div_assoc'] at h
  simpa only [prod_pair hij] using h

/-! ### Overlap deviation and variances (analogues of Eqs. (1.413)--(1.414)) -/

/-- **Expected squared Gibbs overlap deviation for the perceptron (analogue of Eq. (1.413)).**
Under the standing hypotheses of Theorem 2.4.1, `𝔼 (⟨R₁,₂⟩_g - q)² ≤ L / (N + 1)`. -/
theorem perceptron_expected_gibbs_overlap_sub_sq_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        ∫ g : Fin M → Fin (N + 1) → ℝ,
            (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
                ((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ)
                ∂(Measure.pi fun _ : Fin 2 =>
                  (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                    ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))) - q) ^ 2
            ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
          L / ((N : ℝ) + 1) := by
  obtain ⟨K, L, hK0, hL0, hov⟩ := integral_perceptron_overlap_sub_sq_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨E, hE⟩ : ∃ E : (Fin M → Fin (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ,
      ∀ g τ, E g τ = ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  simp only [← hE]
  set Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    ((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ)
  have h_int_sub (g : Fin M → Fin (N + 1) → ℝ) :
      (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
          ∂(Measure.pi fun _ : Fin 2 =>
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) - q =
        ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (Φ σ - q)
          ∂(Measure.pi fun _ : Fin 2 =>
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) := by
    simp only [integral_sub Integrable.of_finite (integrable_const q), integral_const,
      probReal_univ, one_smul]
  have hE_ae (a : Fin (N + 1) → ℤˣ) :
      AEMeasurable (fun g => E g a)
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
    simp only [hE]
    exact (measurable_perceptron_energy hu.measurable a).aemeasurable
  have hjensen := integral_sq_integral_pi_count_tilted_le (R := Fin 2)
    (P := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
    (E := fun a g => E g a) hE_ae (fun σ => Φ σ - q)
  have hov_step := hov N M hd hb hα hq hr
  simp only [← hE] at hov_step
  simp_rw [h_int_sub]
  exact hjensen.trans hov_step

/-- **Variance of the quenched Gibbs overlap under the disorder (analogue of Eq. (1.413)).**
Under the standing hypotheses of Theorem 2.4.1, `Var_g(⟨R₁,₂⟩_g) ≤ L / (N + 1)`. -/
theorem perceptron_var_gibbs_overlap_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        variance
          (fun g : Fin M → Fin (N + 1) → ℝ =>
            ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ)
              ∂(Measure.pi fun _ : Fin 2 =>
                (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))))
          (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
          L / ((N : ℝ) + 1) := by
  obtain ⟨K, L, hK0, hL0, hov⟩ := perceptron_expected_gibbs_overlap_sub_sq_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨E, hE⟩ : ∃ E : (Fin M → Fin (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ,
      ∀ g τ, E g τ = ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ, ∀ σ,
      Φ σ = ((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hE, ← hΦ]
  have hE_ae (a : Fin (N + 1) → ℤˣ) :
      AEMeasurable (fun g => E g a)
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
    simp only [hE]
    exact (measurable_perceptron_energy hu.measurable a).aemeasurable
  have hΦ_bound (σ : Fin 2 → Fin (N + 1) → ℤˣ) : |Φ σ| ≤ 1 := by
    rw [hΦ]
    have hcast : (N : ℝ) + 1 = (Fintype.card (Fin (N + 1)) : ℝ) := by simp
    rw [hcast]
    simpa only [dotProduct] using abs_card_inv_mul_dotProduct_le_one
      (fun i => ((σ 0 i : ℤ) : ℝ)) (fun i => ((σ 1 i : ℤ) : ℝ))
      (fun i => (abs_units_cast_eq_one (σ 0 i)).le)
      (fun i => (abs_units_cast_eq_one (σ 1 i)).le)
  have hY_mem : MemLp (fun g : Fin M → Fin (N + 1) → ℝ =>
      ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) 2
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) :=
    memLp_integral_pi_count_tilted_of_bound 2 (fun g a => E g a) hE_ae
      (fun _ σ => Φ σ) (fun _ => aemeasurable_const) 1 (ae_of_all _ fun _ σ => hΦ_bound σ)
  have hvar := variance_le_integral_sub_const_sq hY_mem q
  have hov_step := hov N M hd hb hα hq hr
  simp only [← hE, ← hΦ] at hov_step
  exact hvar.trans hov_step

/-- **Expected Gibbs overlap variance for the perceptron (analogue of Eq. (1.414)).**
Under the standing hypotheses of Theorem 2.4.1, `𝔼 ⟨(R₁,₂ - ⟨R₁,₂⟩_g)²⟩_g ≤ L / (N + 1)`. -/
theorem perceptron_expected_gibbs_var_overlap_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        ∫ g : Fin M → Fin (N + 1) → ℝ,
          ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) -
              ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
                ((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)
                ∂(Measure.pi fun _ : Fin 2 =>
                  (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun a =>
                    ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((a i : ℤ) : ℝ)))) ^ 2
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun a =>
                ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((a i : ℤ) : ℝ)))
          ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
          L / ((N : ℝ) + 1) := by
  obtain ⟨K, L, hK0, hL0, hov⟩ := integral_perceptron_overlap_sub_sq_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨E, hE⟩ : ∃ E : (Fin M → Fin (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ,
      ∀ g τ, E g τ = ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  simp only [← hE]
  set Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    ((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ)
  have hE_ae (a : Fin (N + 1) → ℤˣ) :
      AEMeasurable (fun g => E g a)
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
    simp only [hE]
    exact (measurable_perceptron_energy hu.measurable a).aemeasurable
  have hov_step := hov N M hd hb hα hq hr
  simp only [← hE] at hov_step
  exact (integral_integral_sub_integral_sq_pi_count_tilted_le (E := fun a g => E g a) hE_ae Φ
    q).trans hov_step

/-! ### Variances of the empirical constraint-derivative product `C(g, σ¹, σ²)` -/

/-- **Expected squared deviation of the quenched empirical derivative product `⟨C⟩_g` from `r`:**
with `C(g, σ¹, σ²) = (N + 1)⁻¹ ∑_{k < M} u'(S_k¹) u'(S_k²)` and `α = M / (N + 1)`, taking `k = 1`
in Theorem 2.5.2 and Jensen's inequality gives `𝔼 (⟨C⟩_g - r)² ≤ α L / (N + 1)`. -/
theorem perceptron_expected_gibbs_empirical_variance_sub_sq_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let S_perc (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) (j : Fin M) : ℝ :=
          (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)
        ∫ g,
          (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                deriv u (S_perc g (σ 0) j) * deriv u (S_perc g (σ 1) j)
              ∂(Measure.pi fun _ : Fin 2 =>
                (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                  fun τ => ∑ j, u (S_perc g τ j)) - r) ^ 2
          ∂P_g ≤
          ((M : ℝ) / ((N : ℝ) + 1)) * L / ((N : ℝ) + 1) := by
  obtain ⟨K, L, hK0, hL0, hemp⟩ := integral_perceptron_empirical_variance_pow_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr P_g S_perc
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := hu.abs_deriv_le_abs
  let E (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ j : Fin M, u (S_perc g τ j)
  let C_obs (g : Fin M → Fin (N + 1) → ℝ) (σ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, deriv u (S_perc g (σ 0) j) * deriv u (S_perc g (σ 1) j)
  have hSm (τ : Fin (N + 1) → ℤˣ) (j : Fin M) : Measurable fun g => S_perc g τ j :=
    measurable_perceptron_field τ j
  have hEm (τ : Fin (N + 1) → ℤˣ) : Measurable fun g => E g τ :=
    measurable_perceptron_energy hu.measurable τ
  have hCm (σ : Fin 2 → Fin (N + 1) → ℤˣ) : Measurable fun g => C_obs g σ :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_deriv u).comp (hSm (σ 0) j)).mul
        ((measurable_deriv u).comp (hSm (σ 1) j))).const_mul _
  have hC_b (g : Fin M → Fin (N + 1) → ℝ) (σ : Fin 2 → Fin (N + 1) → ℤˣ) :
      |C_obs g σ - r| ^ 2 ≤ ((M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2 + |r|) ^ 2 := by
    have hcb : |C_obs g σ| ≤ (M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2 := by
      dsimp only [C_obs]
      have hpos : 0 < (N : ℝ) + 1 := by positivity
      rw [abs_mul, abs_of_pos (inv_pos.2 hpos)]
      calc ((N : ℝ) + 1)⁻¹ * |∑ j : Fin M, _|
          ≤ ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, |deriv u (S_perc g (σ 0) j) *
              deriv u (S_perc g (σ 1) j)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hpos).le
        _ ≤ ((N : ℝ) + 1)⁻¹ * ∑ _j : Fin M, |D| ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => by
              rw [abs_mul, sq]
              exact mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D))
              (inv_pos.2 hpos).le
        _ = (M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add hcb le_rfl)) 2
  have hi_rhs : Integrable (fun g => ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (C_obs g σ - r) ^ 2
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) P_g :=
    integrable_integral_pi_count_tilted_of_bound E hEm (fun g σ => (C_obs g σ - r) ^ 2)
      (fun σ => ((hCm σ).sub_const r).pow_const 2)
      (((M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2 + |r|) ^ 2)
      (fun g σ => by rw [abs_pow]; exact hC_b g σ)
  have hm_lhs : Measurable (fun g =>
      (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, C_obs g σ ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) - r) ^ 2) :=
    ((measurable_integral_pi_count_tilted hEm hCm).sub_const r).pow_const 2
  have hpt (g : Fin M → Fin (N + 1) → ℝ) :
      (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, C_obs g σ ∂(Measure.pi fun _ : Fin 2 =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) - r) ^ 2 ≤
        ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (C_obs g σ - r) ^ 2
          ∂(Measure.pi fun _ : Fin 2 =>
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) := by
    have hsub : (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, C_obs g σ ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) - r =
        ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (C_obs g σ - r) ∂(Measure.pi fun _ : Fin 2 =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) := by
      simp only [integral_sub Integrable.of_finite (integrable_const r), integral_const,
        probReal_univ, one_smul]
    rw [hsub]
    exact sq_integral_le_integral_sq (measurable_of_finite _) Integrable.of_finite
  have hjensen :
      ∫ g, (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, C_obs g σ ∂(Measure.pi fun _ : Fin 2 =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) - r) ^ 2 ∂P_g ≤
        ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (C_obs g σ - r) ^ 2
          ∂(Measure.pi fun _ : Fin 2 =>
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) ∂P_g :=
    integral_mono_ae (hi_rhs.mono' hm_lhs.aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs, abs_sq] using hpt g))
      hi_rhs (ae_of_all _ hpt)
  have h1 := hemp N M hd hb hα hq hr 1
  dsimp only at h1
  simpa only [Nat.cast_one, Nat.mul_one, pow_one, one_mul, mul_one] using hjensen.trans h1

/-- **Disorder variance of the quenched empirical derivative product `⟨C⟩_g`:**
with `C(g, σ¹, σ²) = (N + 1)⁻¹ ∑_{k < M} u'(S_k¹) u'(S_k²)` and `α = M / (N + 1)`, under the
standing hypotheses of Theorem 2.5.2, `Var_g(⟨C⟩_g) ≤ α L / (N + 1)`. -/
theorem perceptron_var_gibbs_empirical_variance_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let S_perc (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) (j : Fin M) : ℝ :=
          (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)
        variance
          (fun g =>
            ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                deriv u (S_perc g (σ 0) j) * deriv u (S_perc g (σ 1) j)
              ∂(Measure.pi fun _ : Fin 2 =>
                (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                  fun τ => ∑ j, u (S_perc g τ j)))
          P_g ≤
          ((M : ℝ) / ((N : ℝ) + 1)) * L / ((N : ℝ) + 1) := by
  obtain ⟨K, L, hK0, hL0, hemp⟩ := perceptron_expected_gibbs_empirical_variance_sub_sq_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr P_g S_perc
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := hu.abs_deriv_le_abs
  let E (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ j : Fin M, u (S_perc g τ j)
  let C_obs (g : Fin M → Fin (N + 1) → ℝ) (σ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, deriv u (S_perc g (σ 0) j) * deriv u (S_perc g (σ 1) j)
  have hSm (τ : Fin (N + 1) → ℤˣ) (j : Fin M) : Measurable fun g => S_perc g τ j :=
    measurable_perceptron_field τ j
  have hE_ae (τ : Fin (N + 1) → ℤˣ) : AEMeasurable (fun g => E g τ) P_g :=
    (measurable_perceptron_energy hu.measurable τ).aemeasurable
  have hC_ae (σ : Fin 2 → Fin (N + 1) → ℤˣ) : AEMeasurable (fun g => C_obs g σ) P_g :=
    ((Finset.measurable_sum _ fun j _ =>
      ((measurable_deriv u).comp (hSm (σ 0) j)).mul
        ((measurable_deriv u).comp (hSm (σ 1) j))).const_mul _).aemeasurable
  have hC_b (g : Fin M → Fin (N + 1) → ℝ) (σ : Fin 2 → Fin (N + 1) → ℤˣ) :
      |C_obs g σ| ≤ (M : ℝ) / ((N + 1) : ℝ) * |D| ^ 2 := by
    dsimp only [C_obs]
    have hpos : 0 < (N : ℝ) + 1 := by positivity
    rw [abs_mul, abs_of_pos (inv_pos.2 hpos)]
    calc ((N : ℝ) + 1)⁻¹ * |∑ j : Fin M, _|
        ≤ ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, |deriv u (S_perc g (σ 0) j) *
            deriv u (S_perc g (σ 1) j)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hpos).le
      _ ≤ ((N : ℝ) + 1)⁻¹ * ∑ _j : Fin M, |D| ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => by
            rw [abs_mul, sq]
            exact mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D))
            (inv_pos.2 hpos).le
      _ = (M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hP_prob : IsProbabilityMeasure P_g := by dsimp only [P_g]; infer_instance
  have hY_mem : MemLp (fun g =>
      ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, C_obs g σ ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) 2 P_g :=
    memLp_integral_pi_count_tilted_of_bound 2 E hE_ae C_obs hC_ae
      ((M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2) (ae_of_all _ hC_b)
  have hvar := variance_le_integral_sub_const_sq hY_mem r
  exact hvar.trans (hemp N M hd hb hα hq hr)

/-- **Expected Gibbs variance of the empirical derivative product `C(g, σ¹, σ²)`:**
under the standing hypotheses of Theorem 2.5.2, `𝔼 ⟨(C - ⟨C⟩_g)²⟩_g ≤ α L / (N + 1)`. -/
theorem perceptron_expected_gibbs_var_empirical_variance_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let S_perc (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) (j : Fin M) : ℝ :=
          (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)
        ∫ g,
          ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            (((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                deriv u (S_perc g (σ 0) j) * deriv u (S_perc g (σ 1) j) -
              ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
                ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                  deriv u (S_perc g (τ 0) j) * deriv u (S_perc g (τ 1) j)
                ∂(Measure.pi fun _ : Fin 2 =>
                  (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                    fun a => ∑ j, u (S_perc g a j))) ^ 2
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                fun a => ∑ j, u (S_perc g a j))
          ∂P_g ≤
          ((M : ℝ) / ((N : ℝ) + 1)) * L / ((N : ℝ) + 1) := by
  obtain ⟨K, L, hK0, hL0, hemp⟩ := integral_perceptron_empirical_variance_pow_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr P_g S_perc
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := hu.abs_deriv_le_abs
  let E (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ j : Fin M, u (S_perc g τ j)
  let C_obs (g : Fin M → Fin (N + 1) → ℝ) (σ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, deriv u (S_perc g (σ 0) j) * deriv u (S_perc g (σ 1) j)
  have hSm (τ : Fin (N + 1) → ℤˣ) (j : Fin M) : Measurable fun g => S_perc g τ j :=
    measurable_perceptron_field τ j
  have hEm (τ : Fin (N + 1) → ℤˣ) : Measurable fun g => E g τ :=
    measurable_perceptron_energy hu.measurable τ
  have hCm (σ : Fin 2 → Fin (N + 1) → ℤˣ) : Measurable fun g => C_obs g σ :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_deriv u).comp (hSm (σ 0) j)).mul
        ((measurable_deriv u).comp (hSm (σ 1) j))).const_mul _
  have hC_b (g : Fin M → Fin (N + 1) → ℝ) (σ : Fin 2 → Fin (N + 1) → ℤˣ) :
      |C_obs g σ - r| ^ 2 ≤ ((M : ℝ) / ((N + 1 : ℕ) : ℝ) * |D| ^ 2 + |r|) ^ 2 := by
    have hcb : |C_obs g σ| ≤ (M : ℝ) / ((N + 1 : ℕ) : ℝ) * |D| ^ 2 := by
      dsimp only [C_obs]
      have hpos : 0 < (N : ℝ) + 1 := by positivity
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast, abs_mul, abs_of_pos (inv_pos.2 hpos)]
      calc ((N : ℝ) + 1)⁻¹ * |∑ j : Fin M, _|
          ≤ ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, |deriv u (S_perc g (σ 0) j) *
              deriv u (S_perc g (σ 1) j)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hpos).le
        _ ≤ ((N : ℝ) + 1)⁻¹ * ∑ _j : Fin M, |D| ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => by
              rw [abs_mul, sq]
              exact mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D))
              (inv_pos.2 hpos).le
        _ = (M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add hcb le_rfl)) 2
  have hP_fin : IsFiniteMeasure P_g := by dsimp only [P_g]; infer_instance
  have hi_rhs : Integrable (fun g => ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (C_obs g σ - r) ^ 2
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) P_g :=
    integrable_integral_pi_count_tilted_of_bound E hEm (fun g σ => (C_obs g σ - r) ^ 2)
      (fun σ => ((hCm σ).sub_const r).pow_const 2)
      (((M : ℝ) / ((N + 1 : ℕ) : ℝ) * |D| ^ 2 + |r|) ^ 2)
      (fun g σ => by rw [abs_pow]; exact hC_b g σ)
  have hpt (g : Fin M → Fin (N + 1) → ℝ) :
      ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          (C_obs g σ - ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, C_obs g τ
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) ^ 2
        ∂(Measure.pi fun _ : Fin 2 =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) ≤
      ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (C_obs g σ - r) ^ 2
        ∂(Measure.pi fun _ : Fin 2 =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) :=
    integral_sub_integral_sq_le_integral_sub_const_sq
      ((memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).2
        Integrable.of_finite) r
  have hgibbs :
      ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          (C_obs g σ - ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, C_obs g τ
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))) ^ 2
          ∂(Measure.pi fun _ : Fin 2 =>
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) ∂P_g ≤
        ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, (C_obs g σ - r) ^ 2
          ∂(Measure.pi fun _ : Fin 2 =>
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) ∂P_g :=
    integral_mono_of_nonneg (ae_of_all _ fun _ => integral_nonneg fun _ => sq_nonneg _)
      hi_rhs (ae_of_all _ hpt)
  have h1 := hemp N M hd hb hα hq hr 1
  dsimp only at h1
  simpa only [Nat.cast_one, Nat.mul_one, pow_one, one_mul, mul_one] using hgibbs.trans h1

end SpinGlasses
