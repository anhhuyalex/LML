/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityComparison
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathExchangeable
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathEndpoints
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.GronwallBackward
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.PiSnoc

/-!
# Smart-path derivative bounds and endpoint domination (Proposition 2.3.6 and Lemma 2.3.7)

Talagrand Section 2.3, Eqs. (2.66)--(2.67). Setting the variance of the last field `Y` to
`r = α * r̂`, where `α = (M + 1) / (N + 1)` is the constraint-to-spin load ratio and `r̂` is the
endpoint square ratio of (2.36), the Gaussian-row smart-path derivative (Proposition 2.2.3,
`hasDerivAt_integral_integral_pi_perceptron_smart_path_gaussian_rows` at `Fin.last M`) writes
`ν'_t(f)` as `α` times the `replicaPairAverage` difference between `smartPathPotentialKernel` and
`r̂ • lastSpinKernel`. Applying Proposition 2.3.5 (Eq. (2.62), `ConstraintCavityComparison.lean`)
to each of the off-diagonal pair terms over `Option (Option R)` bounds `|ν'_t(f)|` by `α K(D, n)`
times the Hölder pair moment plus the `1 / (N + 1)` first-moment error (Eq. (2.66)).

For nonnegative `f` on `R` replicas (in particular `R = Fin 2` as in Lemma 2.3.7), the `(1, ∞)`
case gives `|ν'_t(f)| ≤ α K₁(D) ν_t(f)` on `(0, 1)`. Together with continuity of `t ↦ ν_t(f)` on
`[0, 1]` (`continuousOn_integral_integral_pi_perceptron_smart_path`) and backward Grönwall
(`le_exp_mul_endpoint_of_exists_hasDerivAt`), this yields `ν_t(f) ≤ exp (α K₁ (1 - t)) ν_1(f)`,
and under the small-load condition `α K(D) ≤ 1` (`K(D) = K₁(D) / log 2`), `ν_t(f) ≤ 2 ν(f)`
(Eq. (2.67)).

The expansion and `2 |R|²` bound for averaged `replicaPairAverage` expressions are in
`ForMathlib/Probability/GibbsReplicaProduct.lean`.

## Main declarations

* `SpinGlasses.exists_hasDerivAt_smartPath_abs_le_holder`,
  `SpinGlasses.exists_hasDerivAt_smartPath_abs_le_first_moment`,
  `SpinGlasses.exists_hasDerivAt_smartPath_abs_le_of_ae_abs_le`: Proposition 2.3.6, Eq. (2.66),
  for interior conjugate exponents and both `(1, ∞)` and `(∞, 1)` endpoints.
* `SpinGlasses.continuousOn_integral_integral_pi_perceptron_smart_path`: continuity of `t ↦ ν_t(f)`
  on `[0, 1]`.
* `SpinGlasses.integral_integral_pi_perceptron_smart_path_one_eq`: quenched equality `ν_1 = ν`
  with the Section 2.1 perceptron Gibbs average.
* `SpinGlasses.integral_smartPath_le_two_mul_endpoint`,
  `SpinGlasses.integral_smartPath_fin_two_le_two_mul_perceptron`: Lemma 2.3.7, Eq. (2.67).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

universe uR

/-- **Abstract master bound behind Proposition 2.3.6, Eq. (2.66).** If each off-diagonal pair
difference on `Option (Option R)` is bounded by `K_pair * B_err`, then `ν'_t(f)` at variance
`r = α * r̂` (`(α * rhat).toNNReal`) is bounded in absolute value by
`α * (2 |R|² K_pair) * B_err`. -/
theorem exists_hasDerivAt_smartPath_abs_le_of_pair_bound
    {N M : ℕ} {R : Type uR} [Fintype R] [LinearOrder R]
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (q : ℝ)
    {u : ℝ → ℝ} {D : ℝ}
    (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
    (f : (R → PerceptronSpin N) → ℝ)
    {B_err K_pair : ℝ} :
    let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
    let rhat := perceptronRhat u q
    let variance : ℝ≥0 := (α * rhat).toNNReal
    let P := smartPathDisorder
      (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ (ω : SmartPathDisorder N (M + 1)) :=
      (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
    (∀ i j : Option (Option R), i ≠ j →
      |(∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          (f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)) *
          (deriv u (smartPathField t ω (τ i) (Fin.last M)) *
            deriv u (smartPathField t ω (τ j) (Fin.last M)))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P) -
      rhat * (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P)| ≤ K_pair * B_err) →
    ∃ d',
      HasDerivAt
        (fun s => ∫ ω, ∫ σ : R → SmartPathState N (M + 1), f (fun r => (σ r).1)
          ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u s ω))
          ∂P)
        d' t ∧
      |d'| ≤ α * (2 * (Fintype.card R : ℝ) ^ 2 * K_pair) * B_err := by
  intro α rhat variance P μ hterm
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hrhat_b := rhat_mem_Icc (u := u) (D' := |D|)
    (fun x => (hu.abs_deriv_le x).trans (le_abs_self D)) q
    (fun z => integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q z)
  have hvar_eq : (variance : ℝ) = α * rhat :=
    Real.coe_toNNReal _ (mul_nonneg hα0 hrhat_b.1)
  have hderiv := hasDerivAt_integral_integral_pi_perceptron_smart_path_gaussian_rows
    (N := N) (M := M + 1) (R := R) ht hu variance (Fin.last M) f
  have hα_cast : ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) = α := by push_cast; rfl
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  let F : (R → SmartPathState N (M + 1)) → ℝ := fun σ => f (fun r => (σ r).1)
  have hP_prob : IsProbabilityMeasure P := by dsimp [P]; rw [smartPathDisorder_eq]; infer_instance
  have hμ_prob (ω : SmartPathDisorder N (M + 1)) : IsProbabilityMeasure (μ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  have h1_m (i j : Option (Option R)) :
      Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) =>
        F (fun r => p.2 (some (some r))) *
          smartPathPotentialKernel u t p.1 (Fin.last M) (p.2 i) (p.2 j) := by
    have hf2 : Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) =>
        F (fun r => p.2 (some (some r))) :=
      (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some (some r))).comp measurable_snd))
    have hpU : Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) => (p.1, (p.2 i, p.2 j)) :=
      measurable_fst.prodMk
        (((measurable_pi_apply i).comp measurable_snd).prodMk
          ((measurable_pi_apply j).comp measurable_snd))
    have hUm := (measurable_potentialKernel_joint (N := N) (M := M + 1) (u := u) t
      (Fin.last M)).comp hpU
    exact hf2.mul hUm
  have h1_b (i j : Option (Option R)) (ω : SmartPathDisorder N (M + 1))
      (τ : Option (Option R) → SmartPathState N (M + 1)) :
      |F (fun r => τ (some (some r))) *
        smartPathPotentialKernel u t ω (Fin.last M) (τ i) (τ j)| ≤ |C_f| * |D| ^ 2 := by
    dsimp only [F]
    rw [smartPathPotentialKernel_eq, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_units_cast_eq_one, abs_units_cast_eq_one, one_mul, one_mul, sq]
    exact mul_le_mul ((hCf _).trans (le_abs_self _))
      (mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self _))
        ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have h2_m (i j : Option (Option R)) :
      Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) =>
        F (fun r => p.2 (some (some r))) * lastSpinKernel (p.2 i) (p.2 j) := by
    have hf2 : Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) =>
        F (fun r => p.2 (some (some r))) :=
      (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some (some r))).comp measurable_snd))
    have hpU : Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) => (p.2 i, p.2 j) :=
      ((measurable_pi_apply i).comp measurable_snd).prodMk
        ((measurable_pi_apply j).comp measurable_snd)
    exact hf2.mul (measurable_lastSpinKernel.comp hpU)
  have h2_b (i j : Option (Option R)) (_ω : SmartPathDisorder N (M + 1))
      (τ : Option (Option R) → SmartPathState N (M + 1)) :
      |F (fun r => τ (some (some r))) * lastSpinKernel (τ i) (τ j)| ≤ |C_f| := by
    dsimp only [F]
    rw [abs_mul, lastSpinKernel_eq, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one,
      mul_one, mul_one]
    exact (hCf _).trans (le_abs_self _)
  have hexp1 := integral_replicaPairAverage_eq_combination P μ F
    (fun ω => smartPathPotentialKernel u t ω (Fin.last M))
    (fun i j ω => Integrable.of_bound
      ((h1_m i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (|C_f| * |D| ^ 2) (ae_of_all _ fun τ => by simpa using h1_b i j ω τ))
    (fun i j => integrable_integral_pi_perceptron_smart_path hu.measurable (fun x => hu.le x) t
      (h1_m i j) (h1_b i j))
  have hexp2 := integral_replicaPairAverage_eq_combination P μ F
    (fun _ => lastSpinKernel)
    (fun i j ω => Integrable.of_bound
      ((h2_m i j).comp (measurable_const (a := ω).prodMk measurable_id)).aestronglyMeasurable
      |C_f| (ae_of_all _ fun τ => by simpa using h2_b i j ω τ))
    (fun i j => integrable_integral_pi_perceptron_smart_path hu.measurable (fun x => hu.le x) t
      (h2_m i j) (h2_b i j))
  dsimp only at hexp1 hexp2
  refine ⟨_, hderiv, ?_⟩
  rw [hα_cast, hvar_eq]
  let I_pot := ∫ ω, replicaPairAverage (μ ω) F (smartPathPotentialKernel u t ω (Fin.last M)) ∂P
  let I_ls := ∫ ω, replicaPairAverage (μ ω) F lastSpinKernel ∂P
  change |α * I_pot - α * rhat * I_ls| ≤ _
  have hfactor : α * I_pot - α * rhat * I_ls = α * (I_pot - rhat * I_ls) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hα0]
  let T (i j : Option (Option R)) : ℝ :=
    (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
        (f (fun r => (τ (some (some r))).1) *
          (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)) *
        (deriv u (smartPathField t ω (τ i) (Fin.last M)) *
          deriv u (smartPathField t ω (τ j) (Fin.last M)))
      ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P) -
    rhat * (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
        f (fun r => (τ (some (some r))).1) *
          (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)
      ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P)
  have hdiff : I_pot - rhat * I_ls =
      (∑ p : R × R with p.1 < p.2, T (some (some p.1)) (some (some p.2))) -
        (Fintype.card R : ℝ) * (∑ r : R, T (some (some r)) (some none)) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * T (some none) none := by
    have h1_rw (i j : Option (Option R)) :
        (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          F (fun r => τ (some (some r))) *
            smartPathPotentialKernel u t ω (Fin.last M) (τ i) (τ j)
          ∂(Measure.pi fun _ => μ ω) ∂P) =
        ∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          (f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)) *
          (deriv u (smartPathField t ω (τ i) (Fin.last M)) *
            deriv u (smartPathField t ω (τ j) (Fin.last M)))
          ∂(Measure.pi fun _ => μ ω) ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun τ => by
        dsimp only [F]; rw [smartPathPotentialKernel_eq]; ring))
    have h2_rw (i j : Option (Option R)) :
        (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          F (fun r => τ (some (some r))) * lastSpinKernel (τ i) (τ j)
          ∂(Measure.pi fun _ => μ ω) ∂P) =
        ∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)
          ∂(Measure.pi fun _ => μ ω) ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun τ => by
        dsimp only [F]; rw [lastSpinKernel_eq]; ring))
    dsimp only [I_pot, I_ls]
    rw [hexp1, hexp2]
    simp_rw [h1_rw, h2_rw]
    let S₁ : ℝ := ∑ p : R × R with p.1 < p.2,
      ∫ ω, ∫ τ, (f (fun r => (τ (some (some r))).1) *
        (((τ (some (some p.1))).1.2 : ℤ) : ℝ) * (((τ (some (some p.2))).1.2 : ℤ) : ℝ)) *
        (deriv u (smartPathField t ω (τ (some (some p.1))) (Fin.last M)) *
          deriv u (smartPathField t ω (τ (some (some p.2))) (Fin.last M)))
      ∂(Measure.pi fun _ => μ ω) ∂P
    let S₂ : ℝ := ∑ p : R × R with p.1 < p.2,
      ∫ ω, ∫ τ, f (fun r => (τ (some (some r))).1) *
        (((τ (some (some p.1))).1.2 : ℤ) : ℝ) * (((τ (some (some p.2))).1.2 : ℤ) : ℝ)
      ∂(Measure.pi fun _ => μ ω) ∂P
    let R₁ : ℝ := ∑ r : R,
      ∫ ω, ∫ τ, (f (fun r' => (τ (some (some r'))).1) *
        (((τ (some (some r))).1.2 : ℤ) : ℝ) * (((τ (some none)).1.2 : ℤ) : ℝ)) *
        (deriv u (smartPathField t ω (τ (some (some r))) (Fin.last M)) *
          deriv u (smartPathField t ω (τ (some none)) (Fin.last M)))
      ∂(Measure.pi fun _ => μ ω) ∂P
    let R₂ : ℝ := ∑ r : R,
      ∫ ω, ∫ τ, f (fun r' => (τ (some (some r'))).1) *
        (((τ (some (some r))).1.2 : ℤ) : ℝ) * (((τ (some none)).1.2 : ℤ) : ℝ)
      ∂(Measure.pi fun _ => μ ω) ∂P
    let U₁ : ℝ := ∫ ω, ∫ τ, (f (fun r => (τ (some (some r))).1) *
        (((τ (some none)).1.2 : ℤ) : ℝ) * (((τ none).1.2 : ℤ) : ℝ)) *
        (deriv u (smartPathField t ω (τ (some none)) (Fin.last M)) *
          deriv u (smartPathField t ω (τ none) (Fin.last M)))
      ∂(Measure.pi fun _ => μ ω) ∂P
    let U₂ : ℝ := ∫ ω, ∫ τ, f (fun r => (τ (some (some r))).1) *
        (((τ (some none)).1.2 : ℤ) : ℝ) * (((τ none).1.2 : ℤ) : ℝ)
      ∂(Measure.pi fun _ => μ ω) ∂P
    have hS : (∑ p : R × R with p.1 < p.2, T (some (some p.1)) (some (some p.2))) =
        S₁ - rhat * S₂ := by
      dsimp only [T, S₁, S₂]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    have hR : (∑ r : R, T (some (some r)) (some none)) = R₁ - rhat * R₂ := by
      dsimp only [T, R₁, R₂]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    have hU : T (some none) none = U₁ - rhat * U₂ := rfl
    rw [hS, hR, hU]
    change (S₁ - (Fintype.card R : ℝ) * R₁ +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * U₁) -
      rhat * (S₂ - (Fintype.card R : ℝ) * R₂ +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * U₂) = _
    ring
  rw [hdiff]
  have hcomb := abs_replicaPairCombination_scalar_le T hterm
  refine (mul_le_mul_of_nonneg_left hcomb hα0).trans_eq ?_
  ring

/-- **Proposition 2.3.6, Eq. (2.66), `(1, ∞)` endpoint.**
Under (2.7) and `r = α * r̂`, there exists `K ≥ 0` depending only on `|R|` and `D` such that for
every `N, M`, `t ∈ (0, 1)`, `q ∈ [0, 1]` and spin-only observable `f` on `R` replicas,
`|ν'_t(f)| ≤ α K ((2 + 1 / (N + 1)) ν_t(|f|))`. -/
theorem exists_hasDerivAt_smartPath_abs_le_first_moment
    (R : Type uR) [Fintype R] [LinearOrder R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q : ℝ} (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (f : (R → PerceptronSpin N) → ℝ),
        let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
        let rhat := perceptronRhat u q
        let variance : ℝ≥0 := (α * rhat).toNNReal
        let P := smartPathDisorder
          (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ (ω : SmartPathDisorder N (M + 1)) :=
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
        ∃ d',
          HasDerivAt
            (fun s => ∫ ω, ∫ σ : R → SmartPathState N (M + 1), f (fun r => (σ r).1)
              ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u s ω))
              ∂P)
            d' t ∧
          |d'| ≤ α * K * ((2 + 1 / (N + 1)) *
            ∫ ω, ∫ σ : R → SmartPathState N (M + 1), |f (fun r => (σ r).1)|
              ∂(Measure.pi fun _ : R => μ ω) ∂P) := by
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    abs_integral_smartPath_deriv_mul_sub_rhat_le_first_moment (Option (Option R)) D
  refine ⟨2 * (Fintype.card R : ℝ) ^ 2 * K₂, by positivity, ?_⟩
  intro N M t q ht hq u hd hb f α rhat variance P μ
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
    Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
  let μ₀ (ω : SmartPathDisorder N M) := (smartPathBase N M).tilted (smartPathEnergy u t ω)
  have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  have hμ₀ (ω : SmartPathDisorder N M) : IsProbabilityMeasure (μ₀ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  have hμ (ω : SmartPathDisorder N (M + 1)) : IsProbabilityMeasure (μ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  let e₂ : R → Option (Option R) := fun r => some (some r)
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp (Option.some_injective _)
  let I₁ : ℝ := ∫ ω, ∫ σ : R → SmartPathState N (M + 1), |f (fun r => (σ r).1)|
    ∂(Measure.pi fun _ : R => μ ω) ∂P
  let B_err : ℝ := (2 + 1 / (N + 1)) * I₁
  have hterm (i j : Option (Option R)) (hij : i ≠ j) :
      |(∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          (f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)) *
          (deriv u (smartPathField t ω (τ i) (Fin.last M)) *
            deriv u (smartPathField t ω (τ j) (Fin.last M)))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P) -
      rhat * (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P)| ≤ K₂ * B_err := by
    let g_ij (_ : SmartPathDisorder N M) (a : Option (Option R) → SmartPathState N M) : ℝ :=
      f (fun r => (a (some (some r))).1) * (((a i).1.2 : ℤ) : ℝ) * (((a j).1.2 : ℤ) : ℝ)
    have hg_m : Measurable fun p : SmartPathDisorder N M ×
        (Option (Option R) → SmartPathState N M) => g_ij p.1 p.2 := by
      have hf2 : Measurable fun p : SmartPathDisorder N M ×
          (Option (Option R) → SmartPathState N M) =>
          f (fun r => (p.2 (some (some r))).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply (some (some r))).comp measurable_snd))
      have hε (k : Option (Option R)) :
          Measurable fun p : SmartPathDisorder N M × (Option (Option R) → SmartPathState N M) =>
            (((p.2 k).1.2 : ℤ) : ℝ) :=
        measurable_units_cast.comp
          (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)))
      exact ((hf2.mul (hε i)).mul (hε j) : _)
    have hg_b (ω : SmartPathDisorder N M) (a : Option (Option R) → SmartPathState N M) :
        |g_ij ω a| ≤ |C_f| := by
      dsimp only [g_ij]
      rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
      exact (hCf _).trans (le_abs_self _)
    have hgi : ∀ᵐ ω ∂P₀, Integrable (g_ij ω) (Measure.pi fun _ => μ₀ ω) :=
      ae_of_all _ fun ω => Integrable.of_bound
        (hg_m.comp (measurable_const (a := ω).prodMk measurable_id)).aestronglyMeasurable
        |C_f| (ae_of_all _ fun a => by simpa using hg_b ω a)
    have hg_m1 := measurable_integral_pi_tilted (μ := smartPathBase N M)
      (E := fun ω => smartPathEnergy u t ω) (G := fun ω a => |g_ij ω a|)
      (measurable_smartPathEnergy hu.measurable t)
      (by simpa only [Real.norm_eq_abs] using hg_m.norm)
    have hgi₁ : Integrable (fun ω => ∫ a, |g_ij ω a| ∂(Measure.pi fun _ => μ₀ ω)) P₀ :=
      Integrable.of_bound hg_m1.aestronglyMeasurable |C_f| (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_forall_abs_le _ fun a => by
          rw [abs_abs]; exact hg_b ω a)
    have hb262 := hK₂ N M hij ⟨ht.1.le, ht.2.le⟩ hq variance hd hb hg_m hgi hgi₁
    dsimp only [g_ij] at hb262
    have hm1_eq : (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
        |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)|
        ∂(Measure.pi fun _ => μ ω) ∂P) = I₁ := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      have hpt (τ : Option (Option R) → SmartPathState N (M + 1)) :
          |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)| =
          |f (fun r => (τ (e₂ r)).1)| := by
        rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
      simp_rw [hpt]
      have hfm : Measurable fun σ : R → SmartPathState N (M + 1) => |f (fun r => (σ r).1)| :=
        (measurable_spin_only f).norm
      exact integral_pi_comp_injective (μ ω) he₂
        (fun σ => |f (fun r => (σ r).1)|) hfm.aestronglyMeasurable
    rw [hm1_eq] at hb262
    exact hb262
  obtain ⟨d', hd', hbd⟩ :=
    exists_hasDerivAt_smartPath_abs_le_of_pair_bound ht q hd hb f hterm
  exact ⟨d', hd', hbd.trans_eq (by ring)⟩

/-- **Proposition 2.3.6, Eq. (2.66), interior Hölder exponents.**
Under (2.7) and `r = α * r̂`, there exists `K ≥ 0` depending only on `|R|` and `D` (chosen before
`N, M, t, q, u, f, p₁, p₂`) such that for every `t ∈ (0, 1)`, `q ∈ [0, 1]`, conjugate `p₁, p₂` and
spin-only observable `f` on `R` replicas,
`|ν'_t(f)| ≤ α K (ν_t(|f|^{p₁})^{1/p₁} ν_t(|R_{1,2} - q|^{p₂})^{1/p₂} + 1/(N+1) ν_t(|f|))`. -/
theorem exists_hasDerivAt_smartPath_abs_le_holder
    (R : Type uR) [Fintype R] [LinearOrder R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q : ℝ} (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (f : (R → PerceptronSpin N) → ℝ)
        {p₁ p₂ : ℝ} (_hp : p₁.HolderConjugate p₂),
        let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        let rhat := perceptronRhat u q
        let variance : ℝ≥0 := (α * rhat).toNNReal
        let P := smartPathDisorder
          (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ (ω : SmartPathDisorder N (M + 1)) :=
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
        ∃ d',
          HasDerivAt
            (fun s => ∫ ω, ∫ σ : R → SmartPathState N (M + 1), f (fun r => (σ r).1)
              ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u s ω))
              ∂P)
            d' t ∧
          |d'| ≤ α * K *
            ((∫ ω, ∫ σ : R → SmartPathState N (M + 1),
                |f (fun r => (σ r).1)| ^ p₁ ∂(Measure.pi fun _ : R => μ ω) ∂P) ^ (1 / p₁) *
              (∫ ω, ∫ a : Fin 2 → SmartPathState N (M + 1),
                d_spin (a 0).1 (a 1).1 ^ p₂ ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P) ^ (1 / p₂) +
              1 / (N + 1) *
                ∫ ω, ∫ σ : R → SmartPathState N (M + 1),
                  |f (fun r => (σ r).1)| ∂(Measure.pi fun _ : R => μ ω) ∂P) := by
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    abs_integral_smartPath_deriv_mul_sub_rhat_le_holder (Option (Option R)) D
  refine ⟨2 * (Fintype.card R : ℝ) ^ 2 * K₂, by positivity, ?_⟩
  intro N M t q ht hq u hd hb f p₁ p₂ hp α d_spin rhat variance P μ
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
    Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
  let μ₀ (ω : SmartPathDisorder N M) := (smartPathBase N M).tilted (smartPathEnergy u t ω)
  have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  have hμ₀ (ω : SmartPathDisorder N M) : IsProbabilityMeasure (μ₀ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  have hμ (ω : SmartPathDisorder N (M + 1)) : IsProbabilityMeasure (μ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  let e₂ : R → Option (Option R) := fun r => some (some r)
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp (Option.some_injective _)
  let A₀ : ℝ := ∫ ω, ∫ σ : R → SmartPathState N (M + 1),
    |f (fun r => (σ r).1)| ^ p₁ ∂(Measure.pi fun _ : R => μ ω) ∂P
  let B₀ : ℝ := ∫ ω, ∫ a : Fin 2 → SmartPathState N (M + 1),
    d_spin (a 0).1 (a 1).1 ^ p₂ ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P
  let I₁ : ℝ := ∫ ω, ∫ σ : R → SmartPathState N (M + 1),
    |f (fun r => (σ r).1)| ∂(Measure.pi fun _ : R => μ ω) ∂P
  let B_err : ℝ := A₀ ^ (1 / p₁) * B₀ ^ (1 / p₂) + 1 / (N + 1) * I₁
  have hterm (i j : Option (Option R)) (hij : i ≠ j) :
      |(∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          (f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)) *
          (deriv u (smartPathField t ω (τ i) (Fin.last M)) *
            deriv u (smartPathField t ω (τ j) (Fin.last M)))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P) -
      rhat * (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P)| ≤ K₂ * B_err := by
    let g_ij (_ : SmartPathDisorder N M) (a : Option (Option R) → SmartPathState N M) : ℝ :=
      f (fun r => (a (some (some r))).1) * (((a i).1.2 : ℤ) : ℝ) * (((a j).1.2 : ℤ) : ℝ)
    have hg_m : Measurable fun p : SmartPathDisorder N M ×
        (Option (Option R) → SmartPathState N M) => g_ij p.1 p.2 := by
      have hf2 : Measurable fun p : SmartPathDisorder N M ×
          (Option (Option R) → SmartPathState N M) =>
          f (fun r => (p.2 (some (some r))).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply (some (some r))).comp measurable_snd))
      have hε (k : Option (Option R)) :
          Measurable fun p : SmartPathDisorder N M × (Option (Option R) → SmartPathState N M) =>
            (((p.2 k).1.2 : ℤ) : ℝ) :=
        measurable_units_cast.comp
          (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)))
      exact ((hf2.mul (hε i)).mul (hε j) : _)
    have hg_b (ω : SmartPathDisorder N M) (a : Option (Option R) → SmartPathState N M) :
        |g_ij ω a| ≤ |C_f| := by
      dsimp only [g_ij]
      rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
      exact (hCf _).trans (le_abs_self _)
    have hg_pb (ω : SmartPathDisorder N M) (a : Option (Option R) → SmartPathState N M) :
        |(|g_ij ω a| ^ p₁)| ≤ |C_f| ^ p₁ := by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hg_b ω a) hp.pos.le
    have hg_pm : Measurable fun p : SmartPathDisorder N M ×
        (Option (Option R) → SmartPathState N M) => |g_ij p.1 p.2| ^ p₁ :=
      (by simpa only [Real.norm_eq_abs] using hg_m.norm : Measurable _).pow_const p₁
    have hgp : ∀ᵐ ω ∂P₀, Integrable (fun a => |g_ij ω a| ^ p₁) (Measure.pi fun _ => μ₀ ω) :=
      ae_of_all _ fun ω => Integrable.of_bound
        (hg_pm.comp (measurable_const (a := ω).prodMk measurable_id)).aestronglyMeasurable
        (|C_f| ^ p₁) (ae_of_all _ fun a => by simpa using hg_pb ω a)
    have hg_pm1 := measurable_integral_pi_tilted (μ := smartPathBase N M)
      (E := fun ω => smartPathEnergy u t ω) (G := fun ω a => |g_ij ω a| ^ p₁)
      (measurable_smartPathEnergy hu.measurable t) hg_pm
    have hgp₁ : Integrable (fun ω => ∫ a, |g_ij ω a| ^ p₁ ∂(Measure.pi fun _ => μ₀ ω)) P₀ :=
      Integrable.of_bound hg_pm1.aestronglyMeasurable (|C_f| ^ p₁) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_forall_abs_le _ fun a => hg_pb ω a)
    have hb262 := hK₂ N M hij ⟨ht.1.le, ht.2.le⟩ hq variance hd hb hg_m hp hgp hgp₁
    dsimp only [g_ij] at hb262
    have hm1_eq : (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
        |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)|
        ∂(Measure.pi fun _ => μ ω) ∂P) = I₁ := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      have hpt (τ : Option (Option R) → SmartPathState N (M + 1)) :
          |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)| =
          |f (fun r => (τ (e₂ r)).1)| := by
        rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
      simp_rw [hpt]
      have hfm : Measurable fun σ : R → SmartPathState N (M + 1) => |f (fun r => (σ r).1)| :=
        (measurable_spin_only f).norm
      exact integral_pi_comp_injective (μ ω) he₂
        (fun σ => |f (fun r => (σ r).1)|) hfm.aestronglyMeasurable
    have hmp_eq : (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
        |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)| ^ p₁
        ∂(Measure.pi fun _ => μ ω) ∂P) = A₀ := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      have hpt (τ : Option (Option R) → SmartPathState N (M + 1)) :
          |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) *
            (((τ j).1.2 : ℤ) : ℝ)| ^ p₁ =
          |f (fun r => (τ (e₂ r)).1)| ^ p₁ := by
        rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
      simp_rw [hpt]
      have hfm : Measurable fun σ : R → SmartPathState N (M + 1) =>
          |f (fun r => (σ r).1)| ^ p₁ :=
        ((measurable_spin_only f).norm).pow_const p₁
      exact integral_pi_comp_injective (μ ω) he₂
        (fun σ => |f (fun r => (σ r).1)| ^ p₁) hfm.aestronglyMeasurable
    rw [hm1_eq, hmp_eq] at hb262
    exact hb262
  obtain ⟨d', hd', hbd⟩ :=
    exists_hasDerivAt_smartPath_abs_le_of_pair_bound ht q hd hb f hterm
  exact ⟨d', hd', hbd.trans_eq (by ring)⟩

/-- **Proposition 2.3.6, Eq. (2.66), `(∞, 1)` endpoint.**
Under (2.7) and `r = α * r̂`, there exists `K ≥ 0` depending only on `|R|` and `D` such that if
`|f σ| ≤ M_f` for all `σ`, then
`|ν'_t(f)| ≤ α K (M_f ν_t(|R_{1,2} - q|) + 1/(N+1) ν_t(|f|))`. -/
theorem exists_hasDerivAt_smartPath_abs_le_of_ae_abs_le
    (R : Type uR) [Fintype R] [LinearOrder R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q : ℝ} (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (f : (R → PerceptronSpin N) → ℝ) {M_f : ℝ} (_hMf : 0 ≤ M_f)
        (_hfb : ∀ σ, |f σ| ≤ M_f),
        let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        let rhat := perceptronRhat u q
        let variance : ℝ≥0 := (α * rhat).toNNReal
        let P := smartPathDisorder
          (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ (ω : SmartPathDisorder N (M + 1)) :=
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
        ∃ d',
          HasDerivAt
            (fun s => ∫ ω, ∫ σ : R → SmartPathState N (M + 1), f (fun r => (σ r).1)
              ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u s ω))
              ∂P)
            d' t ∧
          |d'| ≤ α * K *
            (M_f * (∫ ω, ∫ a : Fin 2 → SmartPathState N (M + 1),
                d_spin (a 0).1 (a 1).1 ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P) +
              1 / (N + 1) *
                ∫ ω, ∫ σ : R → SmartPathState N (M + 1),
                  |f (fun r => (σ r).1)| ∂(Measure.pi fun _ : R => μ ω) ∂P) := by
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    abs_integral_smartPath_deriv_mul_sub_rhat_le_of_ae_abs_le (Option (Option R)) D
  refine ⟨2 * (Fintype.card R : ℝ) ^ 2 * K₂, by positivity, ?_⟩
  intro N M t q ht hq u hd hb f M_f hMf hfb α d_spin rhat variance P μ
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
    Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
  let μ₀ (ω : SmartPathDisorder N M) := (smartPathBase N M).tilted (smartPathEnergy u t ω)
  have hμ (ω : SmartPathDisorder N (M + 1)) : IsProbabilityMeasure (μ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  let e₂ : R → Option (Option R) := fun r => some (some r)
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp (Option.some_injective _)
  let J₀ : ℝ := ∫ ω, ∫ a : Fin 2 → SmartPathState N (M + 1),
    d_spin (a 0).1 (a 1).1 ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P
  let I₁ : ℝ := ∫ ω, ∫ σ : R → SmartPathState N (M + 1),
    |f (fun r => (σ r).1)| ∂(Measure.pi fun _ : R => μ ω) ∂P
  let B_err : ℝ := M_f * J₀ + 1 / (N + 1) * I₁
  have hterm (i j : Option (Option R)) (hij : i ≠ j) :
      |(∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          (f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)) *
          (deriv u (smartPathField t ω (τ i) (Fin.last M)) *
            deriv u (smartPathField t ω (τ j) (Fin.last M)))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P) -
      rhat * (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
          f (fun r => (τ (some (some r))).1) *
            (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P)| ≤ K₂ * B_err := by
    let g_ij (_ : SmartPathDisorder N M) (a : Option (Option R) → SmartPathState N M) : ℝ :=
      f (fun r => (a (some (some r))).1) * (((a i).1.2 : ℤ) : ℝ) * (((a j).1.2 : ℤ) : ℝ)
    have hg_m : Measurable fun p : SmartPathDisorder N M ×
        (Option (Option R) → SmartPathState N M) => g_ij p.1 p.2 := by
      have hf2 : Measurable fun p : SmartPathDisorder N M ×
          (Option (Option R) → SmartPathState N M) =>
          f (fun r => (p.2 (some (some r))).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply (some (some r))).comp measurable_snd))
      have hε (k : Option (Option R)) :
          Measurable fun p : SmartPathDisorder N M × (Option (Option R) → SmartPathState N M) =>
            (((p.2 k).1.2 : ℤ) : ℝ) :=
        measurable_units_cast.comp
          (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)))
      exact ((hf2.mul (hε i)).mul (hε j) : _)
    have hOld : ∀ᵐ ω ∂P₀, ∀ᵐ a ∂(Measure.pi fun _ => μ₀ ω), |g_ij ω a| ≤ M_f :=
      ae_of_all _ fun _ => ae_of_all _ fun a => by
        dsimp only [g_ij]
        rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
        exact hfb _
    have hb262 := hK₂ N M hij ⟨ht.1.le, ht.2.le⟩ hq variance hd hb hg_m hMf hOld
    dsimp only [g_ij] at hb262
    have hm1_eq : (∫ ω, ∫ τ : Option (Option R) → SmartPathState N (M + 1),
        |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)|
        ∂(Measure.pi fun _ => μ ω) ∂P) = I₁ := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      have hpt (τ : Option (Option R) → SmartPathState N (M + 1)) :
          |f (fun r => (τ (some (some r))).1) * (((τ i).1.2 : ℤ) : ℝ) * (((τ j).1.2 : ℤ) : ℝ)| =
          |f (fun r => (τ (e₂ r)).1)| := by
        rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
      simp_rw [hpt]
      have hfm : Measurable fun σ : R → SmartPathState N (M + 1) => |f (fun r => (σ r).1)| :=
        (measurable_spin_only f).norm
      exact integral_pi_comp_injective (μ ω) he₂
        (fun σ => |f (fun r => (σ r).1)|) hfm.aestronglyMeasurable
    rw [hm1_eq] at hb262
    exact hb262
  obtain ⟨d', hd', hbd⟩ :=
    exists_hasDerivAt_smartPath_abs_le_of_pair_bound ht q hd hb f hterm
  exact ⟨d', hd', hbd.trans_eq (by ring)⟩

/-! ### Continuity on `[0, 1]`, endpoint identity `ν_1 = ν`, and Lemma 2.3.7, Eq. (2.67) -/

/-- **Continuity of the disorder-averaged smart-path Gibbs expectation on `[0, 1]`.**
Integrating out the auxiliary coordinates via Exercise 2.2.1
(`integral_pi_perceptron_smart_path_auxiliary`) writes the fixed-disorder replica average as a
finite rational expression in Gaussian integrals of `exp ∘ u`, continuous at both endpoints `t = 0`
and `t = 1` where `√t` and `√(1 - t)` are continuous; dominated convergence over the finite
disorder measure gives continuity of `t ↦ ν_t(f)`. -/
theorem continuousOn_integral_integral_pi_perceptron_smart_path
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Continuous u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (v : ℝ≥0) (f : (R → PerceptronSpin N) → ℝ) :
    ContinuousOn
      (fun t => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω))
        ∂smartPathDisorder Pold v)
      (Set.Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  let P := smartPathDisorder Pold v
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let Φ (t : ℝ) (ω : SmartPathDisorder N M) : ℝ :=
    ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
      ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω))
  have hΦm (t : ℝ) : AEStronglyMeasurable (Φ t) P :=
    (measurable_integral_pi_tilted (measurable_smartPathEnergy hu.measurable t)
      ((measurable_spin_only f).comp measurable_snd)).aestronglyMeasurable
  have hΦb (t : ℝ) (ω : SmartPathDisorder N M) : ‖Φ t ω‖ ≤ |C_f| := by
    have : IsProbabilityMeasure ((smartPathBase N M).tilted (smartPathEnergy u t ω)) :=
      isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable hB_le ω t
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun σ => (hCf _).trans (le_abs_self _)
  have hΦ_cont (ω : SmartPathDisorder N M) : Continuous (fun t => Φ t ω) := by
    let γ : Measure ℝ := gaussianReal 0 1
    let g_pot (t : ℝ) (a : PerceptronSpin N) (k : Fin M) : ℝ :=
      ∫ z, Real.exp (u (smartPathFieldNoAux t ω (a, 0) k +
        Real.sqrt ((1 - t) / (N + 1)) * z)) ∂γ
    have hg_pos (t : ℝ) (a : PerceptronSpin N) (k : Fin M) : 0 < g_pot t a k := by
      have hm : Measurable fun z : ℝ =>
          u (smartPathFieldNoAux t ω (a, 0) k + Real.sqrt ((1 - t) / (N + 1)) * z) :=
        hu.measurable.comp (by fun_prop)
      exact integral_exp_pos_of_ae_le hm.aemeasurable (ae_of_all _ fun _ => hB_le _)
    have hg_cont (a : PerceptronSpin N) (k : Fin M) : Continuous (fun t => g_pot t a k) := by
      refine continuous_of_dominated (bound := fun _ => Real.exp B)
        (fun t => ?_) (fun t => ae_of_all _ fun z => ?_) (integrable_const _)
        (ae_of_all _ fun z => ?_)
      · exact (Real.continuous_exp.comp (hu.comp (by fun_prop))).measurable.aestronglyMeasurable
      · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.2 (hB_le _)
      · simp only [smartPathFieldNoAux_eq]
        fun_prop
    let w_spin (t : ℝ) (a : PerceptronSpin N) : ℝ :=
      Real.exp (((a.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2)
    have hw_cont (a : PerceptronSpin N) : Continuous (fun t => w_spin t a) := by
      dsimp only [w_spin]; fun_prop
    let ψ_spin (t : ℝ) (a : PerceptronSpin N) : ℝ := ∏ k : Fin M, g_pot t a k
    have hψ_cont (a : PerceptronSpin N) : Continuous (fun t => ψ_spin t a) := by
      dsimp only [ψ_spin]; fun_prop
    have hw_pos (t : ℝ) (a : PerceptronSpin N) : 0 < w_spin t a := Real.exp_pos _
    have hψ_pos (t : ℝ) (a : PerceptronSpin N) : 0 < ψ_spin t a :=
      Finset.prod_pos fun k _ => hg_pos t a k
    have hden_ne (t : ℝ) : (∑ a : PerceptronSpin N, w_spin t a * ψ_spin t a) ^ Fintype.card R ≠ 0 :=
      pow_ne_zero _ (Finset.sum_pos (fun a _ => mul_pos (hw_pos t a) (hψ_pos t a))
        Finset.univ_nonempty).ne'
    have hΦ_eq (t : ℝ) : Φ t ω =
        (∑ σ : R → PerceptronSpin N, f σ * ∏ r, (w_spin t (σ r) * ψ_spin t (σ r))) /
          (∑ a : PerceptronSpin N, w_spin t a * ψ_spin t a) ^ Fintype.card R := by
      dsimp only [Φ]
      rw [integral_pi_perceptron_smart_path_auxiliary hu.measurable hB_le ω t f]
      refine integral_pi_count_tilted_eq_sum_div (fun a => ?_) f
      rw [Real.exp_add]
      congr 1
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun k _ => Real.exp_log (hg_pos t a k)
    simp_rw [hΦ_eq]
    have hnum_cont : Continuous (fun t =>
        ∑ σ : R → PerceptronSpin N, f σ * ∏ r, (w_spin t (σ r) * ψ_spin t (σ r))) := by fun_prop
    have hden_cont : Continuous (fun t =>
        (∑ a : PerceptronSpin N, w_spin t a * ψ_spin t a) ^ Fintype.card R) := by fun_prop
    exact hnum_cont.div hden_cont hden_ne
  exact (continuous_of_dominated (bound := fun _ => |C_f|) hΦm
    (fun t => ae_of_all _ (hΦb t)) (integrable_const _) (ae_of_all _ hΦ_cont)).continuousOn

/-- **Disorder-averaged terminal identity `ν_1(F) = ν(F)`.** At `t = 1` the last field `y` and
auxiliary spins drop out (`integral_pi_perceptron_smart_path_one`), and
`MeasurableEquiv.finSuccProd` merges the old couplings `g` and last couplings `a` into the full
`M × (N + 1)` Gaussian matrix of Section 2.1. No hypothesis on `u` or `F` is required. -/
theorem integral_integral_pi_perceptron_smart_path_one_eq
    {N M : ℕ} {R : Type uR} [Fintype R]
    (u : ℝ → ℝ) (v : ℝ≥0) (F : (R → Fin (N + 1) → ℤˣ) → ℝ) :
    let P := smartPathDisorder
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    ∫ ω, ∫ x : R → SmartPathState N M,
        F (fun r => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x r).1.1 (x r).1.2)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u 1 ω)) ∂P =
      ∫ g : Fin M → Fin (N + 1) → ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ, F σ
        ∂(Measure.pi fun _ : R =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
            fun τ : Fin (N + 1) → ℤˣ =>
              ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
  intro P
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let e_row : (Fin (N + 1) → ℝ) ≃ᵐ (Fin N → ℝ) × ℝ := MeasurableEquiv.finSuccProd ℝ N
  let e_rows : (Fin M → Fin (N + 1) → ℝ) ≃ᵐ (Fin M → (Fin N → ℝ) × ℝ) :=
    MeasurableEquiv.piCongrRight fun _ => e_row
  let e_split : (Fin M → Fin (N + 1) → ℝ) ≃ᵐ (Fin M → Fin N → ℝ) × (Fin M → ℝ) :=
    e_rows.trans (MeasurableEquiv.arrowProdEquivProdArrow _ _ _)
  have hmp_split : MeasurePreserving ⇑e_split
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ₁)
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ₁).prod
        (Measure.pi fun _ : Fin M => γ₁)) :=
    measurePreserving_pi_finSuccProd (fun _ : Fin M => γ₁) N
  let Ψ : (Fin M → Fin N → ℝ) × (Fin M → ℝ) → ℝ := fun ga =>
    ∫ x : R → SmartPathState N M,
      F (fun r => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x r).1.1 (x r).1.2)
      ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u 1 (ga, 0)))
  have hpt_y (ω : SmartPathDisorder N M) :
      (∫ x : R → SmartPathState N M,
        F (fun r => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x r).1.1 (x r).1.2)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u 1 ω))) =
      Ψ ω.1 := by
    dsimp only [Ψ]
    have hEn : smartPathEnergy u 1 ω = smartPathEnergy u 1 (ω.1, 0) := by
      funext x
      simp [smartPathEnergy_eq, smartPathField_eq, smartPathFieldNoAux_eq]
    rw [hEn]
  simp_rw [hpt_y]
  dsimp only [P]
  rw [smartPathDisorder_eq, integral_prod_fun_fst_of_isProbabilityMeasure]
  have hmap_eq : ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ₁).prod
      (Measure.pi fun _ : Fin M => γ₁)) =
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ₁).map e_split :=
    hmp_split.map_eq.symm
  rw [hmap_eq, integral_map_equiv e_split]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  dsimp only [Ψ]
  have he_g : e_split g = (fun k i => g k i.castSucc, fun k => g k (Fin.last N)) := by
    refine Prod.ext (funext fun k => funext fun i => ?_) (funext fun k => ?_)
    · change (MeasurableEquiv.finSuccProd ℝ N (g k)).1 i = g k i.castSucc
      rw [MeasurableEquiv.finSuccProd_apply]
    · change (MeasurableEquiv.finSuccProd ℝ N (g k)).2 = g k (Fin.last N)
      rw [MeasurableEquiv.finSuccProd_apply]
  rw [he_g]
  exact integral_pi_perceptron_smart_path_one u g 0 F

/-- **Lemma 2.3.7, Eq. (2.67), general finite replica type `R`.**
There exists a constant `K(n, D) ≥ 0` (chosen before `N, M, t, q, u, f`) such that under (2.7) and
`r = α * r̂`, whenever `((M + 1) / (N + 1)) * K ≤ 1` and `f ≥ 0` is a spin-only observable on `R`
replicas, `ν_t(f) ≤ 2 ν_1(f)` for every `t ∈ [0, 1]` and `q ∈ [0, 1]`. -/
theorem integral_smartPath_le_two_mul_endpoint
    (R : Type uR) [Fintype R] [LinearOrder R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : ((M : ℝ) + 1) / ((N : ℝ) + 1) * K ≤ 1)
        (f : (R → PerceptronSpin N) → ℝ) (_hf0 : ∀ σ, 0 ≤ f σ),
        let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
        let rhat := perceptronRhat u q
        let variance : ℝ≥0 := (α * rhat).toNNReal
        let P := smartPathDisorder
          (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        (∫ ω, ∫ σ : R → SmartPathState N (M + 1), f (fun r => (σ r).1)
            ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω))
            ∂P) ≤
          2 * ∫ ω, ∫ σ : R → SmartPathState N (M + 1), f (fun r => (σ r).1)
            ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u 1 ω))
            ∂P := by
  obtain ⟨K₀, hK₀, hderiv⟩ := exists_hasDerivAt_smartPath_abs_le_first_moment R D
  let K₁ : ℝ := 3 * K₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let K : ℝ := K₁ / Real.log 2
  refine ⟨K, div_nonneg (by positivity) hlog2.le, ?_⟩
  intro N M t q ht hq u hd hb hα f hf0 α rhat variance P
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  let g (s : ℝ) : ℝ := ∫ ω, ∫ σ : R → SmartPathState N (M + 1), f (fun r => (σ r).1)
    ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u s ω)) ∂P
  have hg_nonneg (s : ℝ) : 0 ≤ g s :=
    integral_nonneg fun _ => integral_nonneg fun _ => hf0 _
  have hc : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_integral_pi_perceptron_smart_path hu.continuous hu.abs_le variance f
  have hd_gron (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
      ∃ d, HasDerivAt g d s ∧ -(α * K₁ * g s) ≤ d := by
    obtain ⟨d, hd_s, hbd⟩ := hderiv N M hs hq hd hb f
    refine ⟨d, hd_s, ?_⟩
    have habs_f : (∫ ω, ∫ σ : R → SmartPathState N (M + 1), |f (fun r => (σ r).1)|
        ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u s ω)) ∂P) =
        g s := by
      refine integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun σ => ?_))
      exact abs_of_nonneg (hf0 _)
    rw [habs_f] at hbd
    have h1N : 1 / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h3 : (2 + 1 / ((N : ℝ) + 1)) * g s ≤ 3 * g s :=
      mul_le_mul_of_nonneg_right (by linarith) (hg_nonneg s)
    have hbd' : |d| ≤ α * K₁ * g s := by
      calc |d| ≤ α * K₀ * ((2 + 1 / (N + 1)) * g s) := hbd
        _ ≤ α * K₀ * (3 * g s) := mul_le_mul_of_nonneg_left h3 (mul_nonneg hα0 hK₀)
        _ = α * K₁ * g s := by dsimp only [K₁]; ring
    exact neg_le_of_abs_le hbd'
  have hgron := le_exp_mul_endpoint_of_exists_hasDerivAt hc hd_gron ht
  have h1t : 1 - t ≤ 1 := by linarith [ht.1]
  have hαK₁ : α * K₁ ≤ Real.log 2 := by
    have h1 : α * (K₁ / Real.log 2) ≤ 1 := hα
    have h2 := mul_le_mul_of_nonneg_right h1 hlog2.le
    rwa [one_mul, mul_div_assoc', div_mul_cancel₀ _ hlog2.ne'] at h2
  have hexp_le : Real.exp (α * K₁ * (1 - t)) ≤ 2 := by
    have hprod : α * K₁ * (1 - t) ≤ Real.log 2 := by
      calc α * K₁ * (1 - t) ≤ α * K₁ * 1 :=
            mul_le_mul_of_nonneg_left h1t (mul_nonneg hα0 (by positivity))
        _ = α * K₁ := mul_one _
        _ ≤ Real.log 2 := hαK₁
    calc Real.exp (α * K₁ * (1 - t)) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hprod
      _ = 2 := Real.exp_log zero_lt_two
  exact hgron.trans (mul_le_mul_of_nonneg_right hexp_le (hg_nonneg 1))

/-- **Lemma 2.3.7, Eq. (2.67), in the book's two-replica perceptron form `ν_t(f) ≤ 2 ν(f)`.**
Specializes `integral_smartPath_le_two_mul_endpoint` to `R = Fin 2` and identifies the right-hand
side `ν_1(f)` with the Section 2.1 `(N + 1)`-spin, `(M + 1)`-constraint perceptron Gibbs average
`ν(f)` via `integral_integral_pi_perceptron_smart_path_one_eq`. -/
theorem integral_smartPath_fin_two_le_two_mul_perceptron (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : ((M : ℝ) + 1) / ((N : ℝ) + 1) * K ≤ 1)
        (F : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) (_hF0 : ∀ σ, 0 ≤ F σ),
        let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
        let rhat := perceptronRhat u q
        let variance : ℝ≥0 := (α * rhat).toNNReal
        let P := smartPathDisorder
          (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        (∫ ω, ∫ σ : Fin 2 → SmartPathState N (M + 1),
            F (fun r => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (σ r).1.1 (σ r).1.2)
            ∂(Measure.pi fun _ : Fin 2 =>
              (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P) ≤
          2 * ∫ g : Fin (M + 1) → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, F σ
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                fun τ : Fin (N + 1) → ℤˣ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
            ∂(Measure.pi fun _ : Fin (M + 1) =>
              Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
  obtain ⟨K, hK0, hmain⟩ := integral_smartPath_le_two_mul_endpoint (Fin 2) D
  refine ⟨K, hK0, ?_⟩
  intro N M t q ht hq u hd hb hα F hF0 α rhat variance P
  let f : (Fin 2 → PerceptronSpin N) → ℝ :=
    fun a => F (fun r => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (a r).1 (a r).2)
  have hf0 : ∀ a, 0 ≤ f a := fun _ => hF0 _
  have h1 := hmain N M ht hq hd hb hα f hf0
  have hend := integral_integral_pi_perceptron_smart_path_one_eq (N := N) (M := M + 1)
    u variance F
  dsimp only [f] at h1
  rwa [hend] at h1

end SpinGlasses
