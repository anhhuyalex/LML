/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.DeepRecursion
public import LeanMachineLearning.Optimization.NTK.Foundations.IIDAverage

/-!
# Conditional Chebyshev Concentration with a Random Conditioning Covariance

The successor step of the deep NNGP recursion conditions on the preceding layers: given them, the
next layer is i.i.d. `𝒩(0, K)` where the covariance `K` is itself random (the empirical covariance
of the previous layer). This file proves the architecture-free probabilistic step.

* `NTK.chebyshev_activationProduct_pi`: for a *fixed* covariance `K`, the empirical activated
  covariance entry of an i.i.d. `𝒩(0, K)` layer deviates from `∫ φ φ d𝒩(0, K)` by `≥ δ` with
  probability at most `M(K) / (n δ²)`, where `M(K)` is the single-neuron second moment.
* `NTK.continuousOn_covarianceEntry`, `NTK.measurable_comp_of_continuousOn_psd`: the entry map is
  continuous on the positive-semidefinite cone, hence measurable along measurable PSD-valued maps.
* `NTK.tendsto_measure_conditional_activationProduct`: with `q = (a, b)` (fresh layer `a`, past
  `b`), a covariance `K n` that does not depend on `a` and converges in measure to a PSD limit, the
  deviation probability tends to `0`. The proof is Fubini over `a`, the fixed-`K` Chebyshev bound,
  and localization of `M(K n)` near `M(K∞)` by `continuousWithinAt_activationProductSq`.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ENNReal

namespace NTK

/-- **Chebyshev for one fixed Gaussian layer, bounded by the second moment.** -/
theorem chebyshev_activationProduct_pi
    (n m : ℕ) (hn : 0 < n) (K : Matrix (Fin m) (Fin m) ℝ)
    (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (α β : Fin m) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)
      {Z | δ ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, φ ((Z j).ofLp α) * φ ((Z j).ofLp β) -
        ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂multivariateGaussian 0 K|} ≤
      ENNReal.ofReal ((∫ z : EuclideanSpace ℝ (Fin m),
        (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K) / ((n : ℝ) * δ ^ 2)) :=
  chebyshev_average_pi_le_second_moment (multivariateGaussian 0 K) hn
    (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α) * φ (z.ofLp β))
    (memLp_activation_product_of_polynomial_growth m K φ hφ_cont.measurable C hC p hp
      hφ_growth α β) hδ

/-- Entry of the Gaussian covariance-update map is continuous on the positive-semidefinite cone. -/
lemma continuousOn_covarianceEntry (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p)) (m : ℕ) (α β : Fin m) :
    ContinuousOn (fun K : Matrix (Fin m) (Fin m) ℝ =>
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂multivariateGaussian 0 K)
      {K | K.PosSemidef} := fun K0 hK0 =>
  continuousWithinAt_pi.1
    (continuousWithinAt_pi.1
      (continuousWithinAt_covarianceMap φ hφ_cont C hC p hp hφ_growth m K0 hK0) α) β

/-- A function continuous on the PSD cone, composed with a measurable PSD-valued map, is
measurable. -/
lemma measurable_comp_of_continuousOn_psd {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (F : Matrix (Fin m) (Fin m) ℝ → ℝ) (hF : ContinuousOn F {K | K.PosSemidef})
    {S : Ω → Matrix (Fin m) (Fin m) ℝ} (hS : Measurable S) (hpsd : ∀ ω, (S ω).PosSemidef) :
    Measurable (fun ω => F (S ω)) := by
  have h : (fun ω => F (S ω)) =
      (Set.domRestrict {K : Matrix (Fin m) (Fin m) ℝ | K.PosSemidef} F) ∘
        (fun ω => (⟨S ω, hpsd ω⟩ : {K : Matrix (Fin m) (Fin m) ℝ | K.PosSemidef})) := rfl
  rw [h]
  exact hF.domRestrict.measurable.comp (hS.subtype_mk)

/-- **Conditional Chebyshev concentration with a random conditioning covariance.**
Let `q = (a, b) ∈ Ω₂ × Ω₁` and let `Z n q` be an `n`-vector of `ℝ^m`-valued variables which, for
each fixed past `b`, is (in the fresh coordinate `a ~ ν`) i.i.d. `𝒩(0, K n (a, b))`, where the
random covariance `K n` does not depend on `a` and converges in measure to a deterministic PSD
`Klim`. Then the
empirical activated covariance entry concentrates around its conditional mean
`∫ φ φ d𝒩(0, K n q)`.

Proof: Fubini over `a`, Chebyshev (`chebyshev_activationProduct_pi`) for each fixed `b` with the
conditional second moment `M(K n q)`, and localization of `M(K n q)` near `M(Klim)` using
`continuousWithinAt_activationProductSq` together with the convergence in measure of `K n`. -/
theorem tendsto_measure_conditional_activationProduct
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) (ν : Measure Ω₂) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν]
    (m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (K : ℕ → Ω₂ × Ω₁ → Matrix (Fin m) (Fin m) ℝ) (Klim : Matrix (Fin m) (Fin m) ℝ)
    (hKlim : Klim.PosSemidef)
    (hK_meas : ∀ n, Measurable (K n)) (hK_psd : ∀ n q, (K n q).PosSemidef)
    (hK_const : ∀ n a a' b, K n (a, b) = K n (a', b))
    (hK_tendsto : TendstoInMeasure (ν.prod μ₁) K Filter.atTop (fun _ => Klim))
    (Z : ∀ n : ℕ, Ω₂ × Ω₁ → (Fin n → EuclideanSpace ℝ (Fin m)))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hZ_law : ∀ n a b, Measure.map (fun a' => Z n (a', b)) ν =
      Measure.pi fun _ : Fin n => multivariateGaussian 0 (K n (a, b)))
    (α β : Fin m) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun n : ℕ => (ν.prod μ₁)
      {q | δ ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, φ ((Z n q j).ofLp α) * φ ((Z n q j).ofLp β) -
        ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β)
          ∂multivariateGaussian 0 (K n q)|})
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨a0⟩ := nonempty_of_isProbabilityMeasure ν
  let Gf : Matrix (Fin m) (Fin m) ℝ → ℝ := fun K' =>
    ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂multivariateGaussian 0 K'
  let Mf : Matrix (Fin m) (Fin m) ℝ → ℝ := fun K' =>
    ∫ z : EuclideanSpace ℝ (Fin m), (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K'
  let Y : ∀ n : ℕ, (Fin n → EuclideanSpace ℝ (Fin m)) → ℝ := fun n Z' =>
    (n : ℝ)⁻¹ * ∑ j : Fin n, φ ((Z' j).ofLp α) * φ ((Z' j).ofLp β)
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact (hφ_cont.measurable.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable.comp
          (measurable_pi_apply j))).mul
      (hφ_cont.measurable.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable.comp
          (measurable_pi_apply j)))
  have hG_meas : ∀ n, Measurable (fun q => Gf (K n q)) := fun n =>
    measurable_comp_of_continuousOn_psd Gf
      (continuousOn_covarianceEntry φ hφ_cont C hC p hp hφ_growth m α β) (hK_meas n) (hK_psd n)
  let S : ℕ → Set (Ω₂ × Ω₁) := fun n => {q | δ ≤ |Y n (Z n q) - Gf (K n q)|}
  have hS_meas : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le measurable_const
      (continuous_abs.measurable.comp (((hY_meas n).comp (hZ_meas n)).sub (hG_meas n)))
  -- the bad set where the conditional second moment is not localized
  let Esec : ℕ → Set Ω₁ := fun n => {b | Mf Klim + 1 < Mf (K n (a0, b))}
  -- pointwise bound on the conditional probability of a section
  have hsec : ∀ n, 0 < n → ∀ b : Ω₁,
      ν ((fun a => (a, b)) ⁻¹' S n) ≤
        (Esec n).indicator (1 : Ω₁ → ENNReal) b +
          ENNReal.ofReal ((Mf Klim + 1) / ((n : ℝ) * δ ^ 2)) := by
    intro n hn b
    by_cases hb : b ∈ Esec n
    · simp only [Set.indicator_of_mem hb]
      exact (prob_le_one).trans le_self_add
    · simp only [Set.indicator_of_notMem hb, zero_add]
      have hsec_eq : (fun a => (a, b)) ⁻¹' S n =
          (fun a => Z n (a, b)) ⁻¹'
            {z | δ ≤ |Y n z - Gf (K n (a0, b))|} := by
        ext a
        simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, hK_const n a a0 b]
      have hT_meas : MeasurableSet {z : Fin n → EuclideanSpace ℝ (Fin m) |
          δ ≤ |Y n z - Gf (K n (a0, b))|} :=
        measurableSet_le measurable_const
          (continuous_abs.measurable.comp ((hY_meas n).sub measurable_const))
      have hZb_meas : Measurable (fun a => Z n (a, b)) :=
        (hZ_meas n).comp measurable_prodMk_right
      rw [hsec_eq, ← Measure.map_apply hZb_meas hT_meas, hZ_law n a0 b]
      refine (chebyshev_activationProduct_pi n m hn (K n (a0, b)) φ hφ_cont C hC p hp
        hφ_growth α β hδ).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have hn' : (0 : ℝ) < (n : ℝ) * δ ^ 2 := by positivity
      exact div_le_div_of_nonneg_right (not_lt.1 hb |>.trans le_rfl) hn'.le
  -- Fubini over the fresh coordinate
  have hprod : ∀ n, (ν.prod μ₁) (S n) = ∫⁻ b, ν ((fun a => (a, b)) ⁻¹' S n) ∂μ₁ :=
    fun n => Measure.prod_apply_symm (hS_meas n)
  -- localization of the conditional second moment
  let Mmat : Matrix (Fin m) (Fin m) ℝ → Fin m → Fin m → ℝ := fun K' α' β' =>
    ∫ z : EuclideanSpace ℝ (Fin m),
      (φ (z.ofLp α') * φ (z.ofLp β')) ^ 2 ∂multivariateGaussian 0 K'
  have hMmat : TendstoInMeasure (ν.prod μ₁) (fun n q => Mmat (K n q)) Filter.atTop
      (fun _ => Mmat Klim) :=
    tendstoInMeasure_comp_of_continuousWithinAt hK_tendsto (fun n q => hK_psd n q)
      (continuousWithinAt_activationProductSq φ hφ_cont C hC p hp hφ_growth m Klim hKlim)
  let u : ℕ → ENNReal := fun n => (ν.prod μ₁)
    {q | (1 : ENNReal) ≤ edist (Mmat (K n q)) (Mmat Klim)}
  have hu : Filter.Tendsto u Filter.atTop (nhds 0) := hMmat 1 one_pos
  have hE : ∀ n, μ₁ (Esec n) ≤ u n := by
    intro n
    have h1 : μ₁ (Esec n) = (ν.prod μ₁) (Set.univ ×ˢ Esec n) := by
      rw [Measure.prod_prod, measure_univ, one_mul]
    rw [h1]
    refine measure_mono ?_
    rintro ⟨a, b⟩ ⟨-, hb⟩
    have hb' : Mf Klim + 1 < Mf (K n (a, b)) := by
      rw [hK_const n a a0 b]; exact hb
    have hcoord : edist (Mmat (K n (a, b)) α β) (Mmat Klim α β) ≤
        edist (Mmat (K n (a, b))) (Mmat Klim) :=
      (edist_le_pi_edist (Mmat (K n (a, b)) α) (Mmat Klim α) β).trans
        (edist_le_pi_edist (Mmat (K n (a, b))) (Mmat Klim) α)
    refine le_trans ?_ hcoord
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.one_le_ofReal.2 (by
      have : Mf Klim + 1 < Mf (K n (a, b)) := hb'
      rw [le_abs]; left; linarith)
  -- the deterministic `O(1/n)` term
  let c : ℕ → ENNReal := fun n => ENNReal.ofReal ((Mf Klim + 1) / ((n : ℝ) * δ ^ 2))
  have hc : Filter.Tendsto c Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((Mf Klim + 1) / δ ^ 2) / (n : ℝ))
        Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h1 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (((Mf Klim + 1) / δ ^ 2) / (n : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal h0
    refine h1.congr fun n => ?_
    simp only [c]
    congr 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n : ℝ) ≠ 0 := by positivity
      field_simp
  -- assemble
  have hsum : Filter.Tendsto (fun n => u n + c n) Filter.atTop (nhds 0) := by
    simpa using hu.add hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [hprod n]
  calc ∫⁻ b, ν ((fun a => (a, b)) ⁻¹' S n) ∂μ₁
      ≤ ∫⁻ b, ((Esec n).indicator (1 : Ω₁ → ENNReal) b + c n) ∂μ₁ :=
        lintegral_mono fun b => hsec n hn b
    _ = ∫⁻ b, (Esec n).indicator (1 : Ω₁ → ENNReal) b ∂μ₁ + c n := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ μ₁ (Esec n) + c n := by
        gcongr
        exact lintegral_indicator_one_le _
    _ ≤ u n + c n := by gcongr; exact hE n

end NTK

end
