/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingHamiltonian

/-!
# Empirical variance of `u'` along the `s`-interpolating path (Talagrand Section 2.4, Lemma 2.4.3)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.84)--(2.86)
and Lemma 2.4.3.

For `N + 1` spins and `M` constraints at load `α = M / (N + 1)`, write
$$f(\sigma^1, \sigma^2) =
  \frac{1}{N + 1} \sum_{k < M} u'(S_{k, s}^1)\,u'(S_{k, s}^2) - r,$$
and for `M + 1` constraints write `f^-` for the corresponding quantity with the last row omitted:
$$f^-(\sigma^1, \sigma^2) =
  \frac{1}{N + 1} \sum_{k < M} u'(S_{k, s}^1)\,u'(S_{k, s}^2) - r.$$

## Main declarations

* `SpinGlasses.abs_deriv_interpolating_pressure_add_le_cauchy_schwarz`: Eq. (2.84), Cauchy-Schwarz
  bound separating the pressure derivative error into the overlap second moment and the empirical
  variance of `u'`.
* `SpinGlasses.integral_empirical_variance_split_le`: Eq. (2.86), using constraint exchangeability
  and splitting off the last constraint to bound `ν_s(f²)` by
  `ν_s((α u'(S_M^1) u'(S_M^2) - r) f^-) + α D⁴ / (N + 1)`.
* `SpinGlasses.integral_interpolating_deriv_empirical_variance_le`: Lemma 2.4.3 (Eq. (2.85)),
  uniform `O(1 / (N + 1))` bound on `ν_s(f²)` for `s ∈ [0, 1]` when `(q, r)` solves (2.68) and
  `α * K(D) ≤ 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

section CauchySchwarz

/-- **Eq. (2.84): Cauchy-Schwarz bound on the regrouped `s`-interpolating pressure derivative.**
If `p'(s)` satisfies `hasDerivAt_interpolating_pressure_regrouped` (so `s ∈ (0, 1)`, `q ∈ [0, 1]`,
`r ≥ 0`), then by `integral_integral_pair_holder_prob` with conjugate exponents `2` and `2`,
`|p'(s) + (r / 2)(1 - q)| ≤ (1 / 2) * ν_s((R_{1,2} - q)²)^{1/2} * ν_s(f²)^{1/2}`. -/
theorem abs_deriv_interpolating_pressure_add_le_cauchy_schwarz
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr0 : 0 ≤ r) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      Real.sqrt s' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s') * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let E_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (S_fn s' ω x k)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
    let ν_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
      μ_s.tilted (E_s s ω)
    let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
    let f (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (((N : ℝ) + 1)⁻¹ * ∑ k : Fin M, deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r
    ∃ d,
      HasDerivAt
        (fun s' => ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s) ∂P) d s ∧
      |d + (r / 2) * (1 - q)| ≤
        (1 / 2) *
          (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              (R_obs σ - q) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) ^ (1 / (2 : ℝ)) *
          (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) ^ (1 / (2 : ℝ)) := by
  intro P_g P_z P_z' P μ_s S_fn E_s ν_s R_obs f
  have hd := hasDerivAt_interpolating_pressure_regrouped (N := N) (M := M) hu hq hr0 hs
  refine ⟨_, hd, ?_⟩
  have hEm_joint : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E_s s p.1 p.2 := by
    refine (Finset.measurable_sum _ fun k _ => hu.measurable.comp ?_).add ?_
    · have hg_sum : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
          ∑ i : Fin (N + 1), p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hgi : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.1.1 k i :=
          (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
            (measurable_fst.comp (measurable_fst.comp measurable_fst)))
        have hσi : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp measurable_snd))
        exact hgi.mul hσi
      have hzk : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.1.2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
      have hξk : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.2.2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
      exact ((hg_sum.const_mul _).const_mul _).add
        (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
    · refine Finset.measurable_sum _ fun i _ => ?_
      have hσi : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))
      have hz'i : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.2 i :=
        (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
      exact ((hσi.mul_const _).mul hz'i).mul_const _
  have hEb_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      E_s s ω x ≤ M * B + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hu.le _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν_prob (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (ν_s ω) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable (ae_of_all _ (hEb_ω ω))
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  let d_pair (a b : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    |(((N : ℝ) + 1)⁻¹ * ∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)) - q|
  have hd_pair_m : Measurable fun p : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) ×
      ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => d_pair p.1 p.2 := by
    have hsum_m : Measurable fun p : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
        ∑ i : Fin (N + 1), ((p.1.1 i : ℤ) : ℝ) * ((p.2.1 i : ℤ) : ℝ) :=
      Finset.measurable_sum _ fun i _ =>
        (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_fst))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp measurable_snd)))
    simpa only [d_pair, Real.norm_eq_abs] using ((hsum_m.const_mul _).sub_const q).norm
  have hd_pair_b (a b : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : d_pair a b ≤ 2 := by
    dsimp only [d_pair]
    have h1 : |((N : ℝ) + 1)⁻¹ * ∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)| ≤ 1 := by
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      have hs_b : |∑ i : Fin (N + 1), ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)| ≤ (N : ℝ) + 1 :=
        ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := 1) fun i => by
          rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]).trans_eq (by simp))
      exact (inv_mul_le_iff₀ (by positivity)).2 (by linarith)
    have h2 := abs_sub (((N : ℝ) + 1)⁻¹ * ∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)) q
    rw [abs_of_nonneg hq.1] at h2
    linarith [hq.2]
  let M_f : ℝ := ((M : ℝ) / ((N : ℝ) + 1)) * |D₁| ^ 2 + |r|
  have hf_b (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |f ω σ| ≤ M_f := by
    dsimp only [f, M_f]
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hsum : |∑ k : Fin M, deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)| ≤
        (M : ℝ) * |D₁| ^ 2 := by
      refine ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := |D₁| ^ 2) fun k => ?_).trans_eq
        (by simp))
      rw [abs_mul, sq]
      exact mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self D₁))
        ((hu.abs_deriv_le _).trans (le_abs_self D₁)) (abs_nonneg _) (abs_nonneg D₁)
    calc ((N : ℝ) + 1)⁻¹ * |∑ k : Fin M, deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)|
        ≤ ((N : ℝ) + 1)⁻¹ * ((M : ℝ) * |D₁| ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((M : ℝ) / ((N : ℝ) + 1)) * |D₁| ^ 2 := by ring
  have hf_joint_m : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => f p.1 p.2 := by
    have hS_l (l : Fin 2) (k : Fin M) : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => S_fn s p.1 (p.2 l) k := by
      have hg_sum : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
          ∑ i : Fin (N + 1), p.1.1.1 k i * ((((p.2 l).1 i : ℤ) : ℝ)) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hgi : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.1.1 k i :=
          (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
            (measurable_fst.comp (measurable_fst.comp measurable_fst)))
        have hσi : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => (((p.2 l).1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd)))
        exact hgi.mul hσi
      have hzk : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.1.2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
      have hξk : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => (p.2 l).2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp
          ((measurable_pi_apply l).comp measurable_snd))
      exact ((hg_sum.const_mul _).const_mul _).add
        (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
    refine ((Finset.measurable_sum _ fun k _ => ?_).const_mul _).sub_const r
    exact ((measurable_deriv u).comp (hS_l 0 k)).mul ((measurable_deriv u).comp (hS_l 1 k))
  have hp22 : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hf_m (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (f ω) := by
    have hS_l (l : Fin 2) (k : Fin M) :
        Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S_fn s ω (σ l) k := by
      dsimp only [S_fn]; fun_prop
    refine ((Finset.measurable_sum _ fun k _ => ?_).const_mul _).sub_const r
    exact ((measurable_deriv u).comp (hS_l 0 k)).mul ((measurable_deriv u).comp (hS_l 1 k))
  have hfp_mem : ∀ᵐ ω ∂P,
      MemLp (f ω) (ENNReal.ofReal 2) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
    ae_of_all _ fun ω => MemLp.of_bound (hf_m ω).aestronglyMeasurable M_f
      (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hf_b ω σ)
  have hm_R_sub : Measurable fun τ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => R_obs τ - q := by
    refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
    exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_pi_apply 0)))).mul
      (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 1))))
  have hm_d_tau : Measurable fun τ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
      d_pair (τ 0) (τ 1) := by
    simpa only [d_pair, R_obs, Real.norm_eq_abs] using hm_R_sub.norm
  have hdq_mem : ∀ᵐ ω ∂P,
      MemLp (fun τ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => d_pair (τ 0) (τ 1))
        (ENNReal.ofReal 2) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
    ae_of_all _ fun _ => MemLp.of_bound hm_d_tau.aestronglyMeasurable 2
      (ae_of_all _ fun τ => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hd_pair_b (τ 0) (τ 1))
  have hμ_fin : IsFiniteMeasure μ_s := inferInstance
  have hfp_int : Integrable
      (fun ω => ∫ a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        |f ω a| ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P := by
    let F_sq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := |f ω a| ^ (2 : ℝ)
    have hFsq_m : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => F_sq p.1 p.2 := by
      have habs : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => |f p.1 p.2| := by
        simpa only [Real.norm_eq_abs] using hf_joint_m.norm
      exact habs.pow_const (2 : ℝ)
    have hm := @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint F_sq hFsq_m
    exact Integrable.of_bound hm.aestronglyMeasurable (M_f ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)]
      exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun a => by
        rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf_b ω a) 2))
  have hdq_int : Integrable
      (fun ω => ∫ τ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        d_pair (τ 0) (τ 1) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P := by
    let D_sq (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (τ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := d_pair (τ 0) (τ 1) ^ (2 : ℝ)
    have hDsq_m : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => D_sq p.1 p.2 :=
      (hm_d_tau.pow_const (2 : ℝ)).comp measurable_snd
    have hm := @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint D_sq hDsq_m
    exact Integrable.of_bound hm.aestronglyMeasurable 4 (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)]
      exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun τ => by
        rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _), show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact pow_le_pow_left₀ (abs_nonneg _) (hd_pair_b (τ 0) (τ 1)) 2))
  have hcs := integral_integral_pair_holder_prob P ν_s
    (e := (id : Fin 2 → Fin 2)) Function.injective_id (by decide : (0 : Fin 2) ≠ 1)
    (f := f) (d := d_pair) (fun _ _ => abs_nonneg _) hp22 hfp_mem hfp_int hdq_mem hdq_int
  have hprod_int : Integrable
      (fun ω => ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        |f ω σ| * d_pair (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P := by
    let G_prod (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      |f ω σ| * d_pair (σ 0) (σ 1)
    have hGp_m : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => G_prod p.1 p.2 := by
      have habs : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => |f p.1 p.2| := by
        simpa only [Real.norm_eq_abs] using hf_joint_m.norm
      exact habs.mul (hm_d_tau.comp measurable_snd)
    have hm := @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint
      G_prod hGp_m
    exact Integrable.of_bound hm.aestronglyMeasurable (|M_f| * 2) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun σ => by
        rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        exact mul_le_mul ((hf_b ω σ).trans (le_abs_self _)) (hd_pair_b (σ 0) (σ 1))
          (abs_nonneg _) (abs_nonneg _)))
  have hraw_int (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        (R_obs σ - q) * f ω σ) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
    Integrable.of_bound (hm_R_sub.mul (hf_m ω)).aestronglyMeasurable (2 * |M_f|)
      (ae_of_all _ fun σ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hd_pair_b (σ 0) (σ 1)) ((hf_b ω σ).trans (le_abs_self _))
          (abs_nonneg _) zero_le_two)
  have hprod_pt_int (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        |f ω σ| * d_pair (σ 0) (σ 1)) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
    Integrable.of_bound ((hf_m ω).norm.mul hm_d_tau).aestronglyMeasurable (|M_f| * 2)
      (ae_of_all _ fun τ => by
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        exact mul_le_mul ((hf_b ω τ).trans (le_abs_self _)) (hd_pair_b (τ 0) (τ 1))
          (abs_nonneg _) (abs_nonneg _))
  have hraw_P_int : Integrable
      (fun ω => ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (R_obs σ - q) * f ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P := by
    let G_raw (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := (R_obs σ - q) * f ω σ
    have hGr_m : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => G_raw p.1 p.2 := by
      have hm_R : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => R_obs p.2 - q := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))))
      exact hm_R.mul hf_joint_m
    have hm := @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint
      G_raw hGr_m
    exact hprod_int.mono hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,
        Real.norm_of_nonneg (integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      refine (abs_integral_le_integral_abs).trans
        (integral_mono (hraw_int ω).abs (hprod_pt_int ω) fun σ => ?_)
      dsimp only [d_pair, R_obs]
      rw [abs_mul, mul_comm])
  have habs_le :
      |∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (R_obs σ - q) * f ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P| ≤
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          |f ω σ| * d_pair (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
    refine (abs_integral_le_integral_abs).trans (integral_mono hraw_P_int.abs hprod_int fun ω => ?_)
    refine (abs_integral_le_integral_abs).trans
      (integral_mono (hraw_int ω).abs (hprod_pt_int ω) fun σ => ?_)
    dsimp only [d_pair, R_obs]
    rw [abs_mul, mul_comm]
  have heq_f2 : (∫ ω, ∫ a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        |f ω a| ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P :=
    integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun _ => by
      dsimp only; rw [Real.rpow_two, sq_abs]))
  have heq_R2 : (∫ ω, ∫ τ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        d_pair (τ 0) (τ 1) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (R_obs σ - q) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P :=
    integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun _ => by
      dsimp only [d_pair, R_obs]; rw [Real.rpow_two, sq_abs]))
  rw [heq_f2, heq_R2] at hcs
  have halg : (-(r / 2) * (1 - q) -
      (1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (R_obs σ - q) * f ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) + (r / 2) * (1 - q) =
      -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (R_obs σ - q) * f ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by ring
  rw [halg, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h_tot := habs_le.trans hcs
  calc (1 / 2) * |∫ ω, ∫ σ, (R_obs σ - q) * f ω σ ∂(Measure.pi fun _ => ν_s ω) ∂P|
      ≤ (1 / 2) * ((∫ ω, ∫ σ, (f ω σ) ^ 2 ∂(Measure.pi fun _ => ν_s ω) ∂P) ^ (1 / (2 : ℝ)) *
          (∫ ω, ∫ σ, (R_obs σ - q) ^ 2 ∂(Measure.pi fun _ => ν_s ω) ∂P) ^ (1 / (2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h_tot (by positivity)
    _ = (1 / 2) *
          (∫ ω, ∫ σ, (R_obs σ - q) ^ 2 ∂(Measure.pi fun _ => ν_s ω) ∂P) ^ (1 / (2 : ℝ)) *
          (∫ ω, ∫ σ, (f ω σ) ^ 2 ∂(Measure.pi fun _ => ν_s ω) ∂P) ^ (1 / (2 : ℝ)) := by ring

end CauchySchwarz

section EmpiricalVariance

/-- **Eq. (2.86): constraint exchangeability and splitting off the last constraint.**
For `N + 1` spins and `M + 1` constraints with load `α = (M + 1) / (N + 1)`, write
`f = (N + 1)⁻¹ ∑_{k : Fin (M + 1)} u'(S_{k,s}^1) u'(S_{k,s}^2) - r` and
`f⁻ = (N + 1)⁻¹ ∑_{k : Fin M} u'(S_{k,s}^1) u'(S_{k,s}^2) - r`.
By row-swap invariance under `interpConstraintDisorderSwap` and `interpConstraintStateSwap`,
`ν_s(f²) = ν_s((α u'(S_{M,s}^1) u'(S_{M,s}^2) - r) f) ≤ ν_s((α u'(S_{M,s}^1) u'(S_{M,s}^2) - r) f⁻) + (α |D₁|² + |r|) |D₁|² / (N + 1)`. -/
theorem integral_empirical_variance_split_le
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B D₁ : ℝ}
    (hB : ∀ x, u x ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁) (s q r : ℝ) :
    let α : ℝ := ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (k : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ k : Fin (M + 1), u (S_fn ω x k)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let ν_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
      μ_s.tilted (E_s ω)
    let f (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (((N : ℝ) + 1)⁻¹ *
        ∑ k : Fin (M + 1), deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)) - r
    let fMinus (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (((N : ℝ) + 1)⁻¹ *
        ∑ k : Fin M, deriv u (S_fn ω (σ 0) k.castSucc) * deriv u (S_fn ω (σ 1) k.castSucc)) - r
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P ≤
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        (α * (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))) - r) *
          fMinus ω σ
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) +
      (α * |D₁| ^ 2 + |r|) * |D₁| ^ 2 / ((N : ℝ) + 1) := by
  intro α P_g P_z P_z' P μ_s S_fn E_s ν_s f fMinus
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hμ_fin : IsFiniteMeasure μ_s := inferInstance
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  let Ω := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
  let St := (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)
  have hS_joint (k : Fin (M + 1)) : Measurable fun p : Ω × St => S_fn p.1 p.2 k := by
    have hg_sum : Measurable fun p : Ω × St =>
        ∑ i : Fin (N + 1), p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ) := by
      refine Finset.measurable_sum _ fun i _ => ?_
      have hgi : Measurable fun p : Ω × St => p.1.1.1 k i :=
        (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
          (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      have hσi : Measurable fun p : Ω × St => ((p.2.1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))
      exact hgi.mul hσi
    have hzk : Measurable fun p : Ω × St => p.1.1.2 k :=
      (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
    have hξk : Measurable fun p : Ω × St => p.2.2 k :=
      (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
    exact ((hg_sum.const_mul _).const_mul _).add
      (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
  have hEm_joint : Measurable fun p : Ω × St => E_s p.1 p.2 := by
    refine (Finset.measurable_sum _ fun k _ => hu.comp (hS_joint k)).add ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    have hσi : Measurable fun p : Ω × St => ((p.2.1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd))
    have hz'i : Measurable fun p : Ω × St => p.1.2 i :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
    exact ((hσi.mul_const _).mul hz'i).mul_const _
  have hEb_ω (ω : Ω) (x : St) :
      E_s ω x ≤ (M + 1 : ℕ) * B + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν_prob (ω : Ω) : IsProbabilityMeasure (ν_s ω) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable (ae_of_all _ (hEb_ω ω))
  let U_k (k : Fin (M + 1)) (ω : Ω) (σ : Fin 2 → St) : ℝ :=
    deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)
  have hUk_b (k : Fin (M + 1)) (ω : Ω) (σ : Fin 2 → St) : |U_k k ω σ| ≤ |D₁| ^ 2 := by
    dsimp only [U_k]
    rw [abs_mul, sq]
    exact mul_le_mul ((hD₁ _).trans (le_abs_self D₁)) ((hD₁ _).trans (le_abs_self D₁))
      (abs_nonneg _) (abs_nonneg D₁)
  have hUk_joint (k : Fin (M + 1)) : Measurable fun p : Ω × (Fin 2 → St) => U_k k p.1 p.2 := by
    have hl (l : Fin 2) : Measurable fun p : Ω × (Fin 2 → St) => S_fn p.1 (p.2 l) k := by
      have hp : Measurable fun p : Ω × (Fin 2 → St) => (p.1, p.2 l) :=
        measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd)
      exact (hS_joint k).comp hp
    exact ((measurable_deriv u).comp (hl 0)).mul ((measurable_deriv u).comp (hl 1))
  have hf_joint : Measurable fun p : Ω × (Fin 2 → St) => f p.1 p.2 :=
    ((Finset.measurable_sum _ fun k _ => hUk_joint k).const_mul _).sub_const r
  have hfMinus_joint : Measurable fun p : Ω × (Fin 2 → St) => fMinus p.1 p.2 :=
    ((Finset.measurable_sum _ fun k _ => hUk_joint k.castSucc).const_mul _).sub_const r
  let C_g : ℝ := α * |D₁| ^ 2 + |r|
  have hCg0 : 0 ≤ C_g := by dsimp only [C_g]; positivity
  let g_k (k : Fin (M + 1)) (ω : Ω) (σ : Fin 2 → St) : ℝ :=
    (α * U_k k ω σ - r) * f ω σ
  have hgk_b (k : Fin (M + 1)) (ω : Ω) (σ : Fin 2 → St) : |g_k k ω σ| ≤ C_g ^ 2 := by
    have h1 : |α * U_k k ω σ - r| ≤ C_g := by
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_of_nonneg hα0]
      exact mul_le_mul_of_nonneg_left (hUk_b k ω σ) hα0
    have h2 : |f ω σ| ≤ C_g := by
      dsimp only [f, C_g, α]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      have hs_b : |∑ k' : Fin (M + 1), U_k k' ω σ| ≤ ((M + 1 : ℕ) : ℝ) * |D₁| ^ 2 :=
        ((Finset.abs_sum_le_card_mul_of_abs_le _ fun k' => hUk_b k' ω σ).trans_eq (by simp))
      calc ((N : ℝ) + 1)⁻¹ * |∑ k' : Fin (M + 1), U_k k' ω σ|
          ≤ ((N : ℝ) + 1)⁻¹ * (((M + 1 : ℕ) : ℝ) * |D₁| ^ 2) :=
            mul_le_mul_of_nonneg_left hs_b (by positivity)
        _ = ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) * |D₁| ^ 2 := by ring
    dsimp only [g_k]
    rw [abs_mul, sq]
    exact mul_le_mul h1 h2 (abs_nonneg _) hCg0
  have hgk_joint (k : Fin (M + 1)) : Measurable fun p : Ω × (Fin 2 → St) => g_k k p.1 p.2 :=
    ((((hUk_joint k).const_mul α).sub_const r).mul hf_joint)
  have hUk_slice (k : Fin (M + 1)) (ω : Ω) : Measurable (U_k k ω) := by
    have hl (l : Fin 2) :
        Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) => S_fn ω (σ l) k := by
      dsimp only [S_fn]; fun_prop
    exact ((measurable_deriv u).comp (hl 0)).mul ((measurable_deriv u).comp (hl 1))
  have hf_slice (ω : Ω) : Measurable (f ω) :=
    ((Finset.measurable_sum _ fun k _ => hUk_slice k ω).const_mul _).sub_const r
  have hfMinus_slice (ω : Ω) : Measurable (fMinus ω) :=
    ((Finset.measurable_sum _ fun k _ => hUk_slice k.castSucc ω).const_mul _).sub_const r
  have hgk_in (k : Fin (M + 1)) (ω : Ω) :
      Integrable (g_k k ω) (Measure.pi fun _ : Fin 2 => ν_s ω) := by
    have hm : Measurable (g_k k ω) := (((hUk_slice k ω).const_mul α).sub_const r).mul (hf_slice ω)
    exact Integrable.of_bound hm.aestronglyMeasurable (C_g ^ 2)
      (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hgk_b k ω σ)
  have hgk_out (k : Fin (M + 1)) :
      Integrable (fun ω => ∫ σ, g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P := by
    have hm := @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ E_s hEm_joint
      (g_k k) (hgk_joint k)
    exact Integrable.of_bound hm.aestronglyMeasurable (C_g ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_forall_abs_le _ (hgk_b k ω))
  -- Swap invariance of `g_k k` with `g_k (Fin.last M)`!
  have htilted_swap (k : Fin (M + 1)) (ω : Ω) :
      ν_s (interpConstraintDisorderSwap k (Fin.last M) ω) =
        (ν_s ω).map (interpConstraintStateSwap k (Fin.last M)) := by
    dsimp only [ν_s]
    rw [map_tilted_measurableEquiv (interpConstraintStateSwap k (Fin.last M))
      (measurePreserving_interpConstraintStateSwap k (Fin.last M))
      (Measurable.of_uncurry_left hEm_joint)]
    congr 1; funext x
    dsimp only [Function.comp_apply]
    rw [interpConstraintStateSwap_symm_apply]
    dsimp only [E_s, S_fn, interpConstraintDisorderSwap]
    congr 1
    rw [← Equiv.sum_comp (Equiv.swap k (Fin.last M))]
    refine Finset.sum_congr rfl fun k' _ => ?_
    simp
  have hsym (k : Fin (M + 1)) :
      (∫ ω, ∫ σ, g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
        ∫ ω, ∫ σ, g_k (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
    let Ψ_l (k' : Fin (M + 1)) (ω : Ω) : ℝ :=
      ∫ σ, g_k k' ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)
    have hΨ_m : Measurable (Ψ_l (Fin.last M)) :=
      @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ E_s hEm_joint
        (g_k (Fin.last M)) (hgk_joint (Fin.last M))
    have hpt_sw (ω : Ω) :
        Ψ_l (Fin.last M) (interpConstraintDisorderSwap k (Fin.last M) ω) = Ψ_l k ω := by
      dsimp only [Ψ_l]
      rw [htilted_swap k ω, integral_pi_map_equiv (ν_s ω) (interpConstraintStateSwap k (Fin.last M))]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      have hU_sw (k' : Fin (M + 1)) :
          U_k k' (interpConstraintDisorderSwap k (Fin.last M) ω)
            (fun l => interpConstraintStateSwap k (Fin.last M) (σ l)) =
          U_k (Equiv.swap k (Fin.last M) k') ω σ := by
        dsimp only [U_k, S_fn, interpConstraintDisorderSwap]
        simp [interpConstraintStateSwap_apply]
      have hf_sw :
          f (interpConstraintDisorderSwap k (Fin.last M) ω)
            (fun l => interpConstraintStateSwap k (Fin.last M) (σ l)) = f ω σ := by
        dsimp only [f]
        congr 2
        have hsum_eq :
            (∑ k' : Fin (M + 1),
              U_k k' (interpConstraintDisorderSwap k (Fin.last M) ω)
                (fun l => interpConstraintStateSwap k (Fin.last M) (σ l))) =
            ∑ k' : Fin (M + 1), U_k k' ω σ := by
          simp_rw [hU_sw]
          exact Equiv.sum_comp (Equiv.swap k (Fin.last M)) (fun k' => U_k k' ω σ)
        exact hsum_eq
      dsimp only [g_k]
      rw [hU_sw (Fin.last M), Equiv.swap_apply_right, hf_sw]
    have hmp := measurePreserving_interpConstraintDisorderSwap (L := N + 1) k (Fin.last M)
    have heq := hmp.integral_comp_of_aestronglyMeasurable hΨ_m.aestronglyMeasurable
    exact (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans heq
  -- Sum over `k : Fin (M + 1)` gives `(M + 1) * f²`!
  have hsum_pt (ω : Ω) (σ : Fin 2 → St) :
      ∑ k : Fin (M + 1), g_k k ω σ = ((M + 1 : ℕ) : ℝ) * (f ω σ) ^ 2 := by
    dsimp only [g_k]
    rw [← Finset.sum_mul]
    have hsum_sub : (∑ k : Fin (M + 1), (α * U_k k ω σ - r)) =
        ((M + 1 : ℕ) : ℝ) * f ω σ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      dsimp only [α, f, U_k]
      have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hsum_sub, sq]
    ring
  have hsum_int := integral_integral_finset_sum_dep P
    (fun ω => Measure.pi fun _ : Fin 2 => ν_s ω) Finset.univ g_k
    (fun k _ ω => hgk_in k ω) (fun k _ => hgk_out k)
  have hlhs_eq :
      ((M + 1 : ℕ) : ℝ) *
        (∫ ω, ∫ σ, (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
      ((M + 1 : ℕ) : ℝ) *
        ∫ ω, ∫ σ, g_k (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
    have h1 : (∫ ω, ∫ σ, ∑ k : Fin (M + 1), g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
        ((M + 1 : ℕ) : ℝ) * ∫ ω, ∫ σ, (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
      simp_rw [hsum_pt, integral_const_mul]
    have h2 : (∑ k : Fin (M + 1),
        ∫ ω, ∫ σ, g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
        ((M + 1 : ℕ) : ℝ) *
          ∫ ω, ∫ σ, g_k (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
      simp_rw [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact h1.symm.trans (hsum_int.trans h2)
  have hf2_eq_gk :
      (∫ ω, ∫ σ, (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
      ∫ ω, ∫ σ, g_k (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P :=
    mul_left_cancel₀ (by positivity : ((M + 1 : ℕ) : ℝ) ≠ 0) hlhs_eq
  -- Now bound `g_k (Fin.last M) ω σ ≤ (α U_M - r) fMinus + (α |D₁|² + |r|) |D₁|² / (N + 1)`!
  let g_minus (ω : Ω) (σ : Fin 2 → St) : ℝ :=
    (α * U_k (Fin.last M) ω σ - r) * fMinus ω σ
  have hgminus_joint : Measurable fun p : Ω × (Fin 2 → St) => g_minus p.1 p.2 :=
    ((((hUk_joint (Fin.last M)).const_mul α).sub_const r).mul hfMinus_joint)
  have hgminus_b (ω : Ω) (σ : Fin 2 → St) : |g_minus ω σ| ≤ C_g ^ 2 := by
    have h1 : |α * U_k (Fin.last M) ω σ - r| ≤ C_g := by
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_of_nonneg hα0]
      exact mul_le_mul_of_nonneg_left (hUk_b (Fin.last M) ω σ) hα0
    have h2 : |fMinus ω σ| ≤ C_g := by
      dsimp only [fMinus, C_g, α]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      have hs_b : |∑ k' : Fin M, deriv u (S_fn ω (σ 0) k'.castSucc) *
            deriv u (S_fn ω (σ 1) k'.castSucc)| ≤ (M : ℝ) * |D₁| ^ 2 := by
        refine ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := |D₁| ^ 2) fun k' => ?_).trans_eq
          (by simp))
        exact hUk_b k'.castSucc ω σ
      have hM_le : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
      calc ((N : ℝ) + 1)⁻¹ * |∑ k' : Fin M, deriv u (S_fn ω (σ 0) k'.castSucc) *
            deriv u (S_fn ω (σ 1) k'.castSucc)|
          ≤ ((N : ℝ) + 1)⁻¹ * (((M + 1 : ℕ) : ℝ) * |D₁| ^ 2) :=
            mul_le_mul_of_nonneg_left
              (hs_b.trans (mul_le_mul_of_nonneg_right hM_le (sq_nonneg _))) (by positivity)
        _ = ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) * |D₁| ^ 2 := by ring
    dsimp only [g_minus]
    rw [abs_mul, sq]
    exact mul_le_mul h1 h2 (abs_nonneg _) hCg0
  have hgminus_in (ω : Ω) :
      Integrable (g_minus ω) (Measure.pi fun _ : Fin 2 => ν_s ω) := by
    have hm : Measurable (g_minus ω) :=
      (((hUk_slice (Fin.last M) ω).const_mul α).sub_const r).mul (hfMinus_slice ω)
    exact Integrable.of_bound hm.aestronglyMeasurable (C_g ^ 2)
      (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hgminus_b ω σ)
  have hgminus_out :
      Integrable (fun ω => ∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P := by
    have hm := @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ E_s hEm_joint
      g_minus hgminus_joint
    exact Integrable.of_bound hm.aestronglyMeasurable (C_g ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_forall_abs_le _ (hgminus_b ω))
  let err_c : ℝ := C_g * |D₁| ^ 2 / ((N : ℝ) + 1)
  have hpt_le (ω : Ω) (σ : Fin 2 → St) :
      g_k (Fin.last M) ω σ ≤ g_minus ω σ + err_c := by
    have hf_diff : f ω σ - fMinus ω σ = ((N : ℝ) + 1)⁻¹ * U_k (Fin.last M) ω σ := by
      dsimp only [f, fMinus, U_k]
      rw [Fin.sum_univ_castSucc]
      ring
    have hdiff_eq : g_k (Fin.last M) ω σ - g_minus ω σ =
        (α * U_k (Fin.last M) ω σ - r) * (((N : ℝ) + 1)⁻¹ * U_k (Fin.last M) ω σ) := by
      dsimp only [g_k, g_minus]
      rw [← mul_sub, hf_diff]
    have hdiff_le : |g_k (Fin.last M) ω σ - g_minus ω σ| ≤ err_c := by
      rw [hdiff_eq, abs_mul, abs_mul, abs_inv,
        abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      have h1 : |α * U_k (Fin.last M) ω σ - r| ≤ C_g := by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_nonneg hα0]
        exact mul_le_mul_of_nonneg_left (hUk_b (Fin.last M) ω σ) hα0
      calc |α * U_k (Fin.last M) ω σ - r| * (((N : ℝ) + 1)⁻¹ * |U_k (Fin.last M) ω σ|)
          ≤ C_g * (((N : ℝ) + 1)⁻¹ * |D₁| ^ 2) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left (hUk_b (Fin.last M) ω σ) (by positivity))
              (by positivity) hCg0
        _ = err_c := by dsimp only [err_c]; ring
    have h_le : g_k (Fin.last M) ω σ - g_minus ω σ ≤ err_c :=
      (le_abs_self _).trans hdiff_le
    exact sub_le_iff_le_add'.1 h_le
  rw [hf2_eq_gk]
  have hmono_P :
      (∫ ω, ∫ σ, g_k (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) ≤
        ∫ ω, ((∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) + err_c) ∂P := by
    refine integral_mono (hgk_out (Fin.last M)) (hgminus_out.add (integrable_const err_c))
      fun ω => ?_
    have h1 := integral_mono (hgk_in (Fin.last M) ω) ((hgminus_in ω).add (integrable_const err_c))
      (hpt_le ω)
    have h_add_pt : (∫ σ, (g_minus ω σ + err_c) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) =
        (∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) +
        ∫ _σ, err_c ∂(Measure.pi fun _ : Fin 2 => ν_s ω) :=
      integral_add (hgminus_in ω) (integrable_const err_c)
    have h2 : (∫ σ, (g_minus ω σ + err_c) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) =
        (∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) + err_c := by
      rw [h_add_pt, integral_const, probReal_univ, one_smul]
    exact h1.trans_eq h2
  have h_add_P :
      (∫ ω, ((∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) + err_c) ∂P) =
        (∫ ω, ∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) + ∫ _ω, err_c ∂P :=
    integral_add hgminus_out (integrable_const err_c)
  have hP_add :
      (∫ ω, ((∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) + err_c) ∂P) =
        (∫ ω, ∫ σ, g_minus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) + err_c := by
    rw [h_add_P, integral_const, probReal_univ, one_smul]
  exact hmono_P.trans_eq hP_add

end EmpiricalVariance

end SpinGlasses
