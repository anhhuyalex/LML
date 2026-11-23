/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingHamiltonian
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingSmartPath
import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaSecondMoment

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

/-- The overlap of two states, normalised by `N + 1`, lies in `[-1, 1]`, so its distance to
`q ∈ [0, 1]` is at most `2`. -/
private lemma abs_overlap_sub_le_two {N M : ℕ} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (a b : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
    |((N : ℝ) + 1)⁻¹ * ∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ) - q| ≤ 2 := by
  have h1 : |((N : ℝ) + 1)⁻¹ * ∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hs_b : |∑ i : Fin (N + 1), ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)| ≤ (N : ℝ) + 1 :=
      ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := 1) fun i => by
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]).trans_eq (by simp))
    exact (inv_mul_le_iff₀ (by positivity)).2 (by linarith)
  have h2 := abs_sub (((N : ℝ) + 1)⁻¹ * ∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)) q
  rw [abs_of_nonneg hq.1] at h2
  linarith [hq.2]

/-- The observable `(N + 1)⁻¹ ∑_k u'(a_k) u'(b_k) - r` is bounded when `|u'| ≤ D₁`. -/
private lemma abs_empVar_obs_le {N M : ℕ} {u : ℝ → ℝ} {D₁ : ℝ} (hD : ∀ x, |deriv u x| ≤ D₁)
    (r : ℝ) (a b : Fin M → ℝ) :
    |((N : ℝ) + 1)⁻¹ * ∑ k : Fin M, deriv u (a k) * deriv u (b k) - r| ≤
      ((M : ℝ) / ((N : ℝ) + 1)) * |D₁| ^ 2 + |r| := by
  refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
  have hsum : |∑ k : Fin M, deriv u (a k) * deriv u (b k)| ≤ (M : ℝ) * |D₁| ^ 2 := by
    refine ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := |D₁| ^ 2) fun k => ?_).trans_eq
      (by simp))
    rw [abs_mul, sq]
    exact mul_le_mul ((hD _).trans (le_abs_self D₁)) ((hD _).trans (le_abs_self D₁))
      (abs_nonneg _) (abs_nonneg D₁)
  calc ((N : ℝ) + 1)⁻¹ * |∑ k : Fin M, deriv u (a k) * deriv u (b k)|
      ≤ ((N : ℝ) + 1)⁻¹ * ((M : ℝ) * |D₁| ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((M : ℝ) / ((N : ℝ) + 1)) * |D₁| ^ 2 := by ring

/-- Joint measurability of the two-replica observable `c * ∑_k u'(S_k(x⁰)) u'(S_k(x¹)) - r`
from joint measurability of each field `S_k`. -/
private lemma measurable_empVar_obs_joint {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {M : ℕ} (u : ℝ → ℝ) (c r : ℝ) {S : Ω → X → Fin M → ℝ}
    (hS : ∀ k, Measurable fun p : Ω × X => S p.1 p.2 k) :
    Measurable fun p : Ω × (Fin 2 → X) =>
      c * ∑ k : Fin M, deriv u (S p.1 (p.2 0) k) * deriv u (S p.1 (p.2 1) k) - r := by
  have hS_l (l : Fin 2) (k : Fin M) :
      Measurable fun p : Ω × (Fin 2 → X) => S p.1 (p.2 l) k :=
    (hS k).comp (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
  refine ((Finset.measurable_sum _ fun k _ => ?_).const_mul _).sub_const r
  exact ((measurable_deriv u).comp (hS_l 0 k)).mul ((measurable_deriv u).comp (hS_l 1 k))

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
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E_s s p.1 p.2 :=
    measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
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
  have hd_pair_b (a b : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : d_pair a b ≤ 2 :=
    abs_overlap_sub_le_two hq a b
  let M_f : ℝ := ((M : ℝ) / ((N : ℝ) + 1)) * |D₁| ^ 2 + |r|
  have hf_b (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |f ω σ| ≤ M_f :=
    abs_empVar_obs_le (N := N) hu.abs_deriv_le r (S_fn s ω (σ 0)) (S_fn s ω (σ 1))
  have hf_joint_m : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => f p.1 p.2 :=
    measurable_empVar_obs_joint u ((N : ℝ) + 1)⁻¹ r (S := S_fn s)
      fun k => measurable_interpField_joint (L := N + 1) (M := M) s q k
  have hp22 : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hf_m (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (f ω) := Measurable.of_uncurry_left hf_joint_m
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
  have hf_abs_joint : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => |f p.1 p.2| := by
    simpa only [Real.norm_eq_abs] using hf_joint_m.norm
  have hfp_int : Integrable
      (fun ω => ∫ a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        |f ω a| ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P :=
    integrable_integral_pi_tilted (μ := μ_s) hEm_joint hν_prob
      (G := fun ω a => |f ω a| ^ (2 : ℝ))
      (hf_abs_joint.pow_const (2 : ℝ)) (M := M_f ^ 2) fun ω a => by
        rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf_b ω a) 2
  have hdq_int : Integrable
      (fun ω => ∫ τ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        d_pair (τ 0) (τ 1) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P :=
    integrable_integral_pi_tilted (μ := μ_s) hEm_joint hν_prob
      (G := fun _ τ => d_pair (τ 0) (τ 1) ^ (2 : ℝ))
      ((hm_d_tau.pow_const (2 : ℝ)).comp measurable_snd) (M := 4) fun _ τ => by
        rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _), show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact pow_le_pow_left₀ (abs_nonneg _) (hd_pair_b (τ 0) (τ 1)) 2
  have hcs := integral_integral_pair_holder_prob P ν_s
    (e := (id : Fin 2 → Fin 2)) Function.injective_id (by decide : (0 : Fin 2) ≠ 1)
    (f := f) (d := d_pair) (fun _ _ => abs_nonneg _) hp22 hfp_mem hfp_int hdq_mem hdq_int
  have hprod_int : Integrable
      (fun ω => ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        |f ω σ| * d_pair (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P :=
    integrable_integral_pi_tilted (μ := μ_s) hEm_joint hν_prob
      (G := fun ω σ => |f ω σ| * d_pair (σ 0) (σ 1))
      (hf_abs_joint.mul (hm_d_tau.comp measurable_snd)) (M := |M_f| * 2) fun ω σ => by
        rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        exact mul_le_mul ((hf_b ω σ).trans (le_abs_self _)) (hd_pair_b (σ 0) (σ 1))
          (abs_nonneg _) (abs_nonneg _)
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
        (R_obs σ - q) * f ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P :=
    integrable_integral_pi_tilted (μ := μ_s) hEm_joint hν_prob
      (G := fun ω σ => (R_obs σ - q) * f ω σ)
      ((hm_R_sub.comp measurable_snd).mul hf_joint_m) (M := 2 * |M_f|) fun ω σ => by
        rw [abs_mul]
        exact mul_le_mul (hd_pair_b (σ 0) (σ 1)) ((hf_b ω σ).trans (le_abs_self _))
          (abs_nonneg _) zero_le_two
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
`ν_s(f²) = ν_s((α u'(S_{M,s}^1) u'(S_{M,s}^2) - r) f)`
`≤ ν_s((α u'(S_{M,s}^1) u'(S_{M,s}^2) - r) f⁻) + (α |D₁|² + |r|) |D₁|² / (N + 1)`. -/
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
  have hS_joint (k : Fin (M + 1)) :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        S_fn p.1 p.2 k := by
    have hg_sum :
        Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
            (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          ∑ i : Fin (N + 1), p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ) := by
      refine Finset.measurable_sum _ fun i _ => ?_
      have hgi :
          Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
              (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.1.1 k i :=
        (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
          (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      have hσi :
          Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
              (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
            ((p.2.1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))
      exact hgi.mul hσi
    have hzk :
        Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
            (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.1.2 k :=
      (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
    have hξk :
        Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
            (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.2.2 k :=
      (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
    exact ((hg_sum.const_mul _).const_mul _).add
      (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
  have hEm_joint :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => E_s p.1 p.2 := by
    refine (Finset.measurable_sum _ fun k _ => hu.comp (hS_joint k)).add ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    have hσi :
        Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
            (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          ((p.2.1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd))
    have hz'i :
        Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
            (Fin (N + 1) → ℝ)) × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.2 i :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
    exact ((hσi.mul_const _).mul hz'i).mul_const _
  have hEb_ω (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * B + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hS_slice (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (k : Fin (M + 1)) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) => S_fn ω x k := by
    have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
        ∑ i : Fin (N + 1), ω.1.1 k i * ((x.1 i : ℤ) : ℝ) :=
      Finset.measurable_sum _ fun i _ =>
        measurable_const.mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))
    have h2 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) => x.2 k :=
      (measurable_pi_apply k).comp measurable_snd
    exact ((h1.const_mul _).const_mul _).add
      ((measurable_const.add (h2.const_mul _)).const_mul _)
  have hEm_slice (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (E_s ω) := by
    refine (Finset.measurable_sum _ fun k _ => hu.comp (hS_slice ω k)).add ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((measurable_units_cast.comp
      ((measurable_pi_apply i).comp measurable_fst)).mul_const _).mul_const _).mul_const _
  have hν_prob (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (ν_s ω) :=
    isProbabilityMeasure_tilted_of_ae_le (hEm_slice ω).aemeasurable (ae_of_all _ (hEb_ω ω))
  let U_k (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)
  have hUk_b (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : |U_k k ω σ| ≤ |D₁| ^ 2 := by
    dsimp only [U_k]
    rw [abs_mul, sq]
    exact mul_le_mul ((hD₁ _).trans (le_abs_self D₁)) ((hD₁ _).trans (le_abs_self D₁))
      (abs_nonneg _) (abs_nonneg D₁)
  have hUk_joint (k : Fin (M + 1)) :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        U_k k p.1 p.2 := by
    have hl (l : Fin 2) :
        Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
            (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          S_fn p.1 (p.2 l) k := by
      have hg_sum :
          Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
              (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
            ∑ i : Fin (N + 1), p.1.1.1 k i * ((((p.2 l).1 i : ℤ) : ℝ)) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hgi :
            Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
                (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
              p.1.1.1 k i :=
          (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
            (measurable_fst.comp (measurable_fst.comp measurable_fst)))
        have hσi :
            Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
                (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
              (((p.2 l).1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd)))
        exact hgi.mul hσi
      have hzk :
          Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
              (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
            p.1.1.2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
      have hξk :
          Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
              (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
            (p.2 l).2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp
          ((measurable_pi_apply l).comp measurable_snd))
      exact ((hg_sum.const_mul _).const_mul _).add
        (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
    exact ((measurable_deriv u).comp (hl 0)).mul ((measurable_deriv u).comp (hl 1))
  have hf_joint :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => f p.1 p.2 :=
    ((Finset.measurable_sum _ fun k _ => hUk_joint k).const_mul _).sub_const r
  have hfMinus_joint :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        fMinus p.1 p.2 :=
    ((Finset.measurable_sum _ fun k _ => hUk_joint k.castSucc).const_mul _).sub_const r
  let C_g : ℝ := α * |D₁| ^ 2 + |r|
  have hCg0 : 0 ≤ C_g := by dsimp only [C_g]; positivity
  let g_k (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    (α * U_k k ω σ - r) * f ω σ
  have hgk_b (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : |g_k k ω σ| ≤ C_g ^ 2 := by
    have h1 : |α * U_k k ω σ - r| ≤ C_g := by
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_of_nonneg hα0]
      exact mul_le_mul_of_nonneg_left (hUk_b k ω σ) hα0
    have h2 : |f ω σ| ≤ C_g := by
      dsimp only [f, C_g, α]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      have hs_b : |∑ k' : Fin (M + 1), deriv u (S_fn ω (σ 0) k') * deriv u (S_fn ω (σ 1) k')| ≤
          ((M + 1 : ℕ) : ℝ) * |D₁| ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun k' _ => hUk_b k' ω σ).trans_eq ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc ((N : ℝ) + 1)⁻¹ * |∑ k' : Fin (M + 1),
            deriv u (S_fn ω (σ 0) k') * deriv u (S_fn ω (σ 1) k')|
          ≤ ((N : ℝ) + 1)⁻¹ * (((M + 1 : ℕ) : ℝ) * |D₁| ^ 2) :=
            mul_le_mul_of_nonneg_left hs_b (by positivity)
        _ = ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) * |D₁| ^ 2 := by ring
    dsimp only [g_k]
    rw [abs_mul, sq]
    exact mul_le_mul h1 h2 (abs_nonneg _) hCg0
  have hgk_joint (k : Fin (M + 1)) :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        g_k k p.1 p.2 :=
    ((((hUk_joint k).const_mul α).sub_const r).mul hf_joint)
  have hUk_slice (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (U_k k ω) :=
    ((measurable_deriv u).comp ((hS_slice ω k).comp (measurable_pi_apply 0))).mul
      ((measurable_deriv u).comp ((hS_slice ω k).comp (measurable_pi_apply 1)))
  have hf_slice (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (f ω) :=
    ((Finset.measurable_sum _ fun k _ => hUk_slice k ω).const_mul _).sub_const r
  have hfMinus_slice
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (fMinus ω) :=
    ((Finset.measurable_sum _ fun k _ => hUk_slice k.castSucc ω).const_mul _).sub_const r
  have hgk_in (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
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
        exact abs_integral_le_of_forall_abs_le (Measure.pi fun _ : Fin 2 => ν_s ω) (hgk_b k ω))
  -- Swap invariance of `g_k k` with `g_k (Fin.last M)`!
  have htilted_swap (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      ν_s (interpConstraintDisorderSwap k (Fin.last M) ω) =
        (ν_s ω).map (interpConstraintStateSwap k (Fin.last M)) := by
    dsimp only [ν_s]
    rw [map_tilted_measurableEquiv (interpConstraintStateSwap k (Fin.last M))
      (measurePreserving_interpConstraintStateSwap k (Fin.last M)) (hEm_slice ω)]
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
    let Ψ_last
        (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ σ, g_k (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)
    have hΨ_m : Measurable Ψ_last :=
      @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ E_s hEm_joint
        (g_k (Fin.last M)) (hgk_joint (Fin.last M))
    have hpt_sw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        Ψ_last (interpConstraintDisorderSwap k (Fin.last M) ω) =
          ∫ σ, g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) := by
      dsimp only [Ψ_last]
      rw [htilted_swap k ω,
        integral_pi_map_equiv (ν_s ω) (interpConstraintStateSwap k (Fin.last M))]
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
        change (((N : ℝ) + 1)⁻¹ *
            ∑ k' : Fin (M + 1), U_k k' (interpConstraintDisorderSwap k (Fin.last M) ω)
              (fun l => interpConstraintStateSwap k (Fin.last M) (σ l))) - r =
          (((N : ℝ) + 1)⁻¹ * ∑ k' : Fin (M + 1), U_k k' ω σ) - r
        congr 2
        simp_rw [hU_sw]
        exact Equiv.sum_comp (Equiv.swap k (Fin.last M)) (fun k' => U_k k' ω σ)
      dsimp only [g_k]
      rw [hU_sw (Fin.last M), Equiv.swap_apply_right, hf_sw]
    have hmp := measurePreserving_interpConstraintDisorderSwap (L := N + 1) k (Fin.last M)
    have heq : (∫ ω, Ψ_last (interpConstraintDisorderSwap k (Fin.last M) ω) ∂P) =
        ∫ ω, Ψ_last ω ∂P :=
      hmp.integral_comp_of_aestronglyMeasurable (g := Ψ_last) hΨ_m.aestronglyMeasurable
    have hcongr : (∫ ω, ∫ σ, g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
        ∫ ω, Ψ_last (interpConstraintDisorderSwap k (Fin.last M) ω) ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)
    exact hcongr.trans heq
  -- Sum over `k : Fin (M + 1)` gives `(M + 1) * f²`!
  have hsum_pt (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
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
  have hM1_ne : ((M + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero M)
  have hf2_eq_gk :
      (∫ ω, ∫ σ, (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
      ∫ ω, ∫ σ, g_k (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P :=
    mul_left_cancel₀ hM1_ne hlhs_eq
  -- Now bound `g_k (Fin.last M) ω σ ≤ (α U_M - r) fMinus + (α |D₁|² + |r|) |D₁|² / (N + 1)`!
  let g_minus (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    (α * U_k (Fin.last M) ω σ - r) * fMinus ω σ
  have hgminus_joint :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        g_minus p.1 p.2 :=
    ((((hUk_joint (Fin.last M)).const_mul α).sub_const r).mul hfMinus_joint)
  have hgminus_b (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : |g_minus ω σ| ≤ C_g ^ 2 := by
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
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun k' _ => hUk_b k'.castSucc ω σ).trans_eq ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
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
  have hgminus_in
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
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
        exact abs_integral_le_of_forall_abs_le (Measure.pi fun _ : Fin 2 => ν_s ω) (hgminus_b ω))
  let err_c : ℝ := C_g * |D₁| ^ 2 / ((N : ℝ) + 1)
  have hpt_le (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
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
  exact hmono_P.trans (le_of_eq hP_add)

/-- Disorder split for `(M + 1)` constraints in the `s`-interpolating system, grouping the last
constraint's `(g_M, z_M)` into `((Fin N ⊕ Unit) ⊕ Unit) → ℝ` to match `InterpolatingCavityBound`. -/
private lemma measurePreserving_interpVarDisorder_lastSplit (N M : ℕ) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P₀ := ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ).prod
      (Measure.pi fun _ : Fin M => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
    let P₁ := ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ).prod
      (Measure.pi fun _ : Fin (M + 1) => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
    MeasurePreserving
      (fun ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ) =>
        (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
          (Sum.elim (Sum.elim (Fin.init (ω.1.1 (Fin.last M)))
              (fun _ : Unit => ω.1.1 (Fin.last M) (Fin.last N)))
            (fun _ : Unit => ω.1.2 (Fin.last M)) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)))
      P₁ (P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ)) := by
  intro γ P₀ P₁
  let G₀ := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
  let gM1 := Measure.pi fun _ : Fin (N + 1) => γ
  let gM0 := Measure.pi fun _ : Fin N => γ
  let Z₀ := Measure.pi fun _ : Fin M => γ
  let Zp := Measure.pi fun _ : Fin (N + 1) => γ
  have hg := measurePreserving_finSuccProd gM1 M
  have hg_col := measurePreserving_finSuccProd γ N
  have hz := measurePreserving_finSuccProd γ M
  have hunit := (measurePreserving_funUnique γ Unit).symm
  have hsum1 := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin N ⊕ Unit => ℝ)
    (fun _ => γ)).comp (((MeasurePreserving.id gM0).prod hunit).comp hg_col)
  have hsum2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : (Fin N ⊕ Unit) ⊕ Unit => ℝ) (fun _ => γ)).comp (hsum1.prod hunit)
  have step1 : MeasurePreserving
      (Prod.map (Prod.map (MeasurableEquiv.finSuccProd (Fin (N + 1) → ℝ) M)
        (MeasurableEquiv.finSuccProd ℝ M)) id)
      P₁ (((G₀.prod gM1).prod (Z₀.prod γ)).prod Zp) :=
    (hg.prod hz).prod (MeasurePreserving.id Zp)
  have step2 := (measurePreserving_prodProdProdComm G₀ gM1 Z₀ γ).prod (MeasurePreserving.id Zp)
  have step3 := measurePreserving_prodAssoc (G₀.prod Z₀) (gM1.prod γ) Zp
  have step4 := (MeasurePreserving.id (G₀.prod Z₀)).prod
    (Measure.measurePreserving_swap (μ := gM1.prod γ) (ν := Zp))
  have step5 := (measurePreserving_prodAssoc (G₀.prod Z₀) Zp (gM1.prod γ)).symm
  have step6 := (MeasurePreserving.id P₀).prod hsum2
  have full := step6.comp (step5.comp (step4.comp (step3.comp (step2.comp step1))))
  convert full using 1
  ext ω : 1
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.prodAssoc, Fin.init_def]
  · ext idx
    rcases idx with (i | _) | _ <;>
      simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply, Fin.init_def]

/-- Transport a replica average on `((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))` at
smart-path `t = 1` (where coordinate `0` of `y.2 : Fin 2 → ℝ` has coefficient `0`) to the full
`(M + 1)`-constraint `s`-interpolating Gibbs measure `ν_s ω`. -/
private lemma integral_pi_interpVar_last_split_eq.{uR}
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ)
    {H : ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) →
      (R → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) → ℝ}
    (hHm : Measurable fun p :
      (((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (R → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ)) => H p.1 p.2) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P₀ := ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ).prod
      (Measure.pi fun _ : Fin M => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
    let P₁ := ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ).prod
      (Measure.pi fun _ : Fin (M + 1) => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
    let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ
    let γ₂ := Measure.pi fun _ : Fin 2 => γ
    let μ_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => γ)
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => γ)
    let π_sp (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : PerceptronSpin N :=
      (Fin.init x₀.1, x₀.1 (Fin.last N))
    let E₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * ((x₀.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * x₀.2 k))) +
      ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ k : Fin (M + 1), u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let μ₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
      μ_base.tilted (E₀ ω₀)
    let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)
        (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ)) : ℝ :=
      Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp y.1))
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ y.2
    let splitΩ (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) :=
      (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
        Sum.elim (Sum.elim (Fin.init (ω.1.1 (Fin.last M)))
            (fun _ : Unit => ω.1.1 (Fin.last M) (Fin.last N)))
          (fun _ : Unit => ω.1.2 (Fin.last M)))
    ∫ p, ∫ a : R → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        H p (fun l => ((a l).1, (a l).2 1))
        ∂(Measure.pi fun _ : R => ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y)))
        ∂(P₀.prod γ₁) =
      ∫ ω, ∫ σ : R → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        H (splitΩ ω) (fun l => interpStateLastSplit (N + 1) M (σ l))
        ∂(Measure.pi fun _ : R => μ_s.tilted (E_s ω)) ∂P₁ := by
  intro γ P₀ P₁ γ₁ γ₂ μ_base μ_s π_sp E₀ E_s μ₀ X_fn splitΩ
  -- Step 1: Simplify `X_fn` since `1 - 1 = 0`, so `X_fn w₁ y` depends only on `(y.1, y.2 1)`!
  let X₁ (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)
      (z : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp z.1))
      (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      Real.sqrt (1 - s) * Real.sqrt (1 - q) * z.2
  have hX_eq (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)
      (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ)) :
      X_fn w₁ y = X₁ w₁ (y.1, y.2 1) := by
    dsimp only [X_fn, X₁]
    simp [dotProduct, Fin.sum_univ_two]
  -- Step 2: Integrate out `y.2 0` using `finSuccProd ℝ 1` (or `Fin 2 ≃ᵐ Unit × ℝ`)!
  let e_2 : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ :=
    { toFun := fun v => (v 0, v 1)
      invFun := fun p => ![p.1, p.2]
      left_inv := fun v => by ext i; fin_cases i <;> rfl
      right_inv := fun _ => rfl
      measurable_toFun := (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
      measurable_invFun := measurable_pi_iff.2 fun i => by
        fin_cases i
        · exact measurable_fst
        · exact measurable_snd }
  have hmp_2 : MeasurePreserving ⇑e_2 γ₂ (γ.prod γ) := by
    have hfp := measurePreserving_finSuccProd γ 1
    let e_1 : (Fin 1 → ℝ) × ℝ ≃ᵐ ℝ × ℝ :=
      MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique (Fin 1) ℝ) (MeasurableEquiv.refl ℝ)
    have hmp_1 : MeasurePreserving ⇑e_1 ((Measure.pi fun _ : Fin 1 => γ).prod γ) (γ.prod γ) :=
      (measurePreserving_funUnique γ (Fin 1)).prod (MeasurePreserving.id γ)
    convert hmp_1.comp hfp using 1
    ext v : 1
    refine Prod.ext ?_ ?_ <;> rfl
  let e_aux : (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ)) ≃ᵐ
      (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) × ℝ :=
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (e_2.trans MeasurableEquiv.prodComm)).trans MeasurableEquiv.prodAssoc.symm)
  have he_aux_apply (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ)) :
      e_aux y = ((y.1, y.2 1), y.2 0) := rfl
  have hmp_aux (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      MeasurePreserving ⇑e_aux ((μ₀ ω₀).prod γ₂) (((μ₀ ω₀).prod γ).prod γ) := by
    have h1 := (MeasurePreserving.id (μ₀ ω₀)).prod hmp_2
    have h2 := (MeasurePreserving.id (μ₀ ω₀)).prod
      (Measure.measurePreserving_swap (μ := γ) (ν := γ))
    have h3 := (measurePreserving_prodAssoc (μ₀ ω₀) γ γ).symm
    convert h3.comp (h2.comp h1) using 1
    ext y : 1; rfl
  have hE₀_m : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E₀ p.1 p.2 := by
    refine (Finset.measurable_sum _ fun k _ => hu.comp ?_).add ?_
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
  have hE₀_i (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x₀ => Real.exp (E₀ ω₀ x₀)) μ_base := by
    have hm : Measurable (E₀ ω₀) := by
      refine (Finset.measurable_sum _ fun k _ => hu.comp ?_).add ?_
      · refine (((Finset.measurable_sum _ fun i _ =>
          measurable_const.mul (measurable_units_cast.comp
            ((measurable_pi_apply i).comp measurable_fst))).const_mul _).const_mul _).add
          ((measurable_const.add
            (((measurable_pi_apply k).comp measurable_snd).const_mul _)).const_mul _)
      · exact Finset.measurable_sum _ fun i _ =>
          (((measurable_units_cast.comp
            ((measurable_pi_apply i).comp measurable_fst)).mul_const _).mul_const _).mul_const _
    have hbd_0 (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E₀ ω₀ x₀ ≤ M * B + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r| := by
      refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
        (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
    exact integrable_exp_of_ae_le hm.aemeasurable (ae_of_all _ hbd_0)
  have hcoef_m (idx : (Fin N ⊕ Unit) ⊕ Unit) :
      Measurable fun τ : Fin (N + 1) → ℤˣ =>
        (Sum.elim (Real.sqrt s • cavityCoef N 1 (Fin.init τ, τ (Fin.last N)))
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) idx := by
    rcases idx with (i | _) | _
    · dsimp only [cavityCoef, Sum.elim_inl, Pi.smul_apply, smul_eq_mul, Fin.init_def]
      exact measurable_const.mul
        (measurable_const.mul (measurable_units_cast.comp (measurable_pi_apply i.castSucc)))
    · dsimp only [cavityCoef, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
      exact measurable_const.mul
        (measurable_const.mul (measurable_units_cast.comp (measurable_pi_apply (Fin.last N))))
    · dsimp only [Sum.elim_inr]
      exact measurable_const
  have hinner_p (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) :
      ∫ a : R → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        H p (fun l => ((a l).1, (a l).2 1))
        ∂(Measure.pi fun _ : R => ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))) =
      ∫ z : R → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ, H p z
        ∂(Measure.pi fun _ : R => ((μ₀ p.1).prod γ).tilted (fun z => u (X₁ p.2 z))) := by
    have hμ₀_prob : IsProbabilityMeasure (μ₀ p.1) := isProbabilityMeasure_tilted (hE₀_i p.1)
    have hV_m : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ) =>
        u (X_fn p.2 y) := by
      simp_rw [hX_eq]
      have hd1 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ) =>
          Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp y.1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((hcoef_m idx).comp (measurable_fst.comp measurable_fst)).mul_const _
      have hd2 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ) =>
          Real.sqrt (1 - s) * Real.sqrt (1 - q) * y.2 1 :=
        measurable_const.mul ((measurable_pi_apply 1).comp measurable_snd)
      exact hu.comp (hd1.add hd2)
    have hprob_src : IsProbabilityMeasure
        (((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))) :=
      isProbabilityMeasure_tilted_of_ae_le hV_m.aemeasurable (ae_of_all _ fun _ => hB _)
    have hmap_tilt : (((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))).map e_aux =
        ((((μ₀ p.1).prod γ).prod γ).tilted
          (fun q_z => u (X₁ p.2 q_z.1) + (0 : ℝ → ℝ) q_z.2)) := by
      rw [map_tilted_measurableEquiv e_aux (hmp_aux p.1) hV_m]
      congr 1; ext q_z
      obtain ⟨y, rfl⟩ := e_aux.surjective q_z
      dsimp only [Function.comp_apply]
      rw [MeasurableEquiv.symm_apply_apply, hX_eq, he_aux_apply]
      simp
    have htrans := (integral_pi_map_equiv
      (((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))) e_aux
      (fun τ => H p (fun l => (τ l).1))).symm
    rw [hmap_tilt] at htrans
    have hprod := integral_pi_tilted_prod_add_mul (μ := (μ₀ p.1).prod γ) (ν := γ) (ι := R)
      (fun z => u (X₁ p.2 z)) (0 : ℝ → ℝ) (H p) (fun _ => 1)
    simp only [MeasureTheory.tilted_zero, integral_const, probReal_univ, one_smul, mul_one] at hprod
    exact htrans.trans hprod
  simp_rw [hinner_p]
  -- Step 3: Transport the `X₁`-tilted split integral to `P₁` and `μ_s.tilted (E_s ω)`.
  let V₁ (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ := u (X₁ p.2 z)
  have hV₁_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => V₁ q_p.1 q_p.2 := by
    have hd1 : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
        Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp q_p.2.1))
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ q_p.1.2 := by
      simp only [dotProduct]
      refine Finset.measurable_sum _ fun idx _ => ?_
      have ha : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
          (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp q_p.2.1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) idx :=
        (hcoef_m idx).comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
      exact ha.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
    have hd2 : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
        Real.sqrt (1 - s) * Real.sqrt (1 - q) * q_p.2.2 :=
      measurable_const.mul (measurable_snd.comp measurable_snd)
    exact hu.comp (hd1.add hd2)
  let I_fn (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ z : R → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ, H p z
      ∂(Measure.pi fun _ : R => ((μ₀ p.1).prod γ).tilted (V₁ p))
  have hIm : Measurable I_fn :=
    measurable_integral_pi_tilted_prod_tilted μ_base γ hE₀_m hE₀_i hV₁_m hHm
  have hmp_dis := measurePreserving_interpVarDisorder_lastSplit N M
  rw [← hmp_dis.integral_comp_of_aestronglyMeasurable hIm.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only [I_fn, Function.comp_apply]
  have hEs_slice : Measurable (E_s ω) := by
    refine (Finset.measurable_sum _ fun k _ => hu.comp ?_).add ?_
    · refine (((Finset.measurable_sum _ fun i _ =>
        measurable_const.mul (measurable_units_cast.comp
          ((measurable_pi_apply i).comp measurable_fst))).const_mul _).const_mul _).add
        ((measurable_const.add
          (((measurable_pi_apply k).comp measurable_snd).const_mul _)).const_mul _)
    · exact Finset.measurable_sum _ fun i _ =>
        (((measurable_units_cast.comp
          ((measurable_pi_apply i).comp measurable_fst)).mul_const _).mul_const _).mul_const _
  have hEs_bd (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * B + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hprob_ω : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_of_ae_le hEs_slice.aemeasurable (ae_of_all _ hEs_bd)
  have hX₁_eq (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      X₁ (splitΩ ω).2 (interpStateLastSplit (N + 1) M x) =
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) *
          (Real.sqrt q * ω.1.2 (Fin.last M) + Real.sqrt (1 - q) * x.2 (Fin.last M)) := by
    rw [interpStateLastSplit_apply]
    dsimp only [X₁, splitΩ, π_sp, cavityCoef]
    rw [sumElim_dotProduct_sumElim, smul_dotProduct, smul_eq_mul, sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h_sqrt1 : Real.sqrt (1 / ((N : ℝ) + 1)) = (Real.sqrt (N + 1 : ℕ))⁻¹ := by
      rw [one_div, Real.sqrt_inv]
      push_cast; rfl
    rw [h_sqrt1, Fin.sum_univ_castSucc]
    simp only [Fin.init_def]
    have hsum_i :
        (∑ i : Fin N, (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i.castSucc : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i.castSucc) =
        (Real.sqrt (N + 1 : ℕ))⁻¹ *
          ∑ i : Fin N, ω.1.1 (Fin.last M) i.castSucc * ((x.1 i.castSucc : ℤ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum_i]
    ring
  have htilted_st :
      (μ_s.tilted (E_s ω)).map (interpStateLastSplit (N + 1) M) =
      ((μ₀ (splitΩ ω).1).prod γ).tilted (V₁ (splitΩ ω)) := by
    rw [map_tilted_measurableEquiv (interpStateLastSplit (N + 1) M)
      (measurePreserving_interpStateLastSplit (N + 1) M) hEs_slice]
    have hcomb : ((μ₀ (splitΩ ω).1).prod γ).tilted (V₁ (splitΩ ω)) =
        (μ_base.prod γ).tilted (fun z => E₀ (splitΩ ω).1 z.1 + V₁ (splitΩ ω) z) := by
      rw [← tilted_prod_comp_fst, tilted_tilted ((hE₀_i (splitΩ ω).1).comp_fst γ)]
      rfl
    rw [hcomb]
    congr 1; funext z
    obtain ⟨x, rfl⟩ := (interpStateLastSplit (N + 1) M).surjective z
    dsimp only [Function.comp_apply, V₁]
    rw [MeasurableEquiv.symm_apply_apply, hX₁_eq x, interpStateLastSplit_apply]
    dsimp only [E_s, E₀, splitΩ]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.init_def]
    ring
  rw [← htilted_st]
  exact integral_pi_map_equiv (μ_s.tilted (E_s ω)) (interpStateLastSplit (N + 1) M)
    (H (splitΩ ω))

/-- **Talagrand Section 2.4, Lemma 2.4.3 (Eq. (2.85)): empirical variance bound on `u'` along the
`s`-interpolating path.**
Given `D ∈ ℝ`, there exist constants `K(D) ≥ 0` and `L_var ≥ 0` (chosen before `N, M, s, u, q, r`)
such that whenever `u` satisfies (2.7), `α = M / (N + 1)` satisfies `α * K(D) ≤ 1`, `(q, r)` solves
the replica-symmetric system (2.68) for load `α`, and `s ∈ [0, 1]`, the centered empirical average
`f = (N + 1)⁻¹ ∑_{k : Fin M} u'(S_{k,s}^1) u'(S_{k,s}^2) - r` satisfies
`ν_s(f²) ≤ L_var / (N + 1)` for every `N, M : ℕ` (including `M = 0` and `N = 0`). -/
theorem integral_interpolating_deriv_empirical_variance_le (D : ℝ) :
    ∃ K L_var : ℝ, 0 ≤ K ∧ 0 ≤ L_var ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_s := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ k : Fin M, u (S_fn ω x k)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let f (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (((N : ℝ) + 1)⁻¹ *
            ∑ k : Fin M, deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)) - r
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
          L_var / ((N : ℝ) + 1) := by
  obtain ⟨K_ov, L_ov, hKov0, hLov0, h_ov⟩ := integral_interpolating_overlap_sub_sq_le D
  obtain ⟨K_cav, hKcav0, h_cav⟩ := abs_integral_interp_deriv_mul_sub_rhat_le_l2 (Fin 2) D
  let K : ℝ := max (max K_ov K_cav) 1
  let L_var : ℝ := L_ov + 9 * |D| ^ 4 + 4 * |D| ^ 2
  refine ⟨K, L_var, le_max_of_le_right zero_le_one, by positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_le : ∀ x, u x ≤ |D| := fun x => (hu.le x).trans (le_abs_self D)
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := fun x => (hu.abs_deriv_le x).trans (le_abs_self D)
  -- Case `M = 0`: both the sum and `r` vanish!
  rcases M with _ | M
  · have hr0 : r = 0 := by simp [hr]
    intro P_g P_z P_z' P_s μ_s S_fn E_s f
    have hf0 (ω : ((Fin 0 → Fin (N + 1) → ℝ) × (Fin 0 → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ)) : f ω σ = 0 := by
      simp [f, hr0]
    simp only [hf0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    exact div_nonneg (by dsimp only [L_var]; positivity) (by positivity)
  -- Case `M + 1`:
  dsimp only
  let α : ℝ := ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα_ov : α * K_ov ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_left K_ov K_cav).trans (le_max_left _ 1)) hα0).trans hα
  have hα_cav : α * K_cav ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_right K_ov K_cav).trans (le_max_left _ 1)) hα0).trans hα
  have hα_le1 : α ≤ 1 := by
    have h := (mul_le_mul_of_nonneg_left (le_max_right (max K_ov K_cav) 1) hα0).trans hα
    simpa only [mul_one] using h
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
    rw [hq]
    have heq : (∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1) =
        ∫ z : ℝ, Real.tanh (1 * Real.sqrt r * z + 0) ^ 2 ∂gaussianReal 0 1 := by
      congr 1; ext z; ring_nf
    rw [heq]
    exact fixedPointMap_mem_Icc 1 0 r
  have hrhat_mem := rhat_mem_Icc hD₁ q
    (fun z => integrable_exp_cavityPath_new hu.measurable hD_le q z)
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hα0 hrhat_mem.1
  have hr_le : r ≤ α * |D| ^ 2 := by
    rw [hr]; exact mul_le_mul_of_nonneg_left hrhat_mem.2 hα0
  have hr_abs : |r| ≤ α * |D| ^ 2 := by rwa [abs_of_nonneg hr0]
  -- Local abbreviations for `(M + 1)` constraints and `M` old constraints!
  let γ : Measure ℝ := gaussianReal 0 1
  let P₀ := ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ).prod
    (Measure.pi fun _ : Fin M => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
  let P₁ := ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ).prod
    (Measure.pi fun _ : Fin (M + 1) => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
  let μ_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod (Measure.pi fun _ : Fin M => γ)
  let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
    (Measure.pi fun _ : Fin (M + 1) => γ)
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
  let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
  let V_f : ℝ := ∫ ω, ∫ σ, (f ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  let V_minus : ℝ := ∫ ω, ∫ σ, (fMinus ω σ) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  let Q_ov : ℝ := ∫ ω, ∫ σ, (R_obs σ - q) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  have hVf0 : 0 ≤ V_f := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hVminus0 : 0 ≤ V_minus := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hQov0 : 0 ≤ Q_ov := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  -- Overlap bound Eq. (2.80): `Q_ov ≤ L_ov / (N + 1)`!
  have hQov_le : Q_ov ≤ L_ov / ((N : ℝ) + 1) :=
    h_ov N (M + 1) hs hd hb hα_ov hq hr
  -- Step 1: Eq. (2.86) split bound!
  have hsplit := integral_empirical_variance_split_le (N := N) (M := M)
    hu.measurable hD_le hD₁ s q r
  dsimp only at hsplit
  -- Step 2: Apply `abs_integral_interp_deriv_mul_sub_rhat_le_l2` in old coordinates at `t = 1`!
  let E₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (∑ k : Fin M, u (Real.sqrt s *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * ((x₀.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * x₀.2 k))) +
    ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r
  let π_sp (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : PerceptronSpin N :=
    (Fin.init x₀.1, x₀.1 (Fin.last N))
  have hπ_m : Measurable π_sp := by
    refine (measurable_pi_iff.2 fun i => ?_).prodMk
      ((measurable_pi_apply (Fin.last N)).comp measurable_fst)
    exact (measurable_pi_apply i.castSucc).comp measurable_fst
  have hE₀_m : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E₀ p.1 p.2 := by
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
  have hE₀_i (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x₀ => Real.exp (E₀ ω₀ x₀)) μ_base := by
    have hm : Measurable (E₀ ω₀) := by
      refine (Finset.measurable_sum _ fun k _ => hu.measurable.comp ?_).add ?_
      · refine (((Finset.measurable_sum _ fun i _ =>
          measurable_const.mul (measurable_units_cast.comp
            ((measurable_pi_apply i).comp measurable_fst))).const_mul _).const_mul _).add
          ((measurable_const.add
            (((measurable_pi_apply k).comp measurable_snd).const_mul _)).const_mul _)
      · exact Finset.measurable_sum _ fun i _ =>
          (((measurable_units_cast.comp
            ((measurable_pi_apply i).comp measurable_fst)).mul_const _).mul_const _).mul_const _
    have hbd_0 (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E₀ ω₀ x₀ ≤ M * |D| + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r| := by
      refine add_le_add ((Finset.sum_le_sum fun _ _ => hD_le _).trans_eq (by simp))
        (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
    exact integrable_exp_of_ae_le hm.aemeasurable (ae_of_all _ hbd_0)
  let f₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (((N : ℝ) + 1)⁻¹ *
      ∑ k : Fin M,
        deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * (((a 0).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * (a 0).2 k)) *
        deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * (((a 1).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * (a 1).2 k))) - r
  have hf₀_m : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => f₀ p.1 p.2 := by
    have hl (l : Fin 2) (k : Fin M) : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
        Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((((p.2 l).1 i : ℤ) : ℝ))) +
          Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * (p.2 l).2 k) := by
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
    exact ((measurable_deriv u).comp (hl 0 k)).mul ((measurable_deriv u).comp (hl 1 k))
  -- Bound `|f₀ ω₀ a| ≤ 2 * α * |D|²`!
  have hf₀_b (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |f₀ ω₀ a| ≤ 2 * α * |D| ^ 2 := by
    dsimp only [f₀]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hs_b : |∑ k : Fin M,
        deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * (((a 0).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * (a 0).2 k)) *
        deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * (((a 1).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * (a 1).2 k))| ≤
        (M : ℝ) * |D| ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => ?_).trans_eq
        (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
      rw [abs_mul, sq]
      exact mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D)
    have hM_le : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : ((N : ℝ) + 1)⁻¹ * |∑ k : Fin M,
        deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * (((a 0).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * (a 0).2 k)) *
        deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k i * (((a 1).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * (a 1).2 k))| ≤
        α * |D| ^ 2 := by
      calc _ ≤ ((N : ℝ) + 1)⁻¹ * (((M + 1 : ℕ) : ℝ) * |D| ^ 2) :=
            mul_le_mul_of_nonneg_left
              (hs_b.trans (mul_le_mul_of_nonneg_right hM_le (sq_nonneg _))) (by positivity)
        _ = α * |D| ^ 2 := by dsimp only [α]; ring
    linarith [hr_abs]
  have hP₀_prob : IsProbabilityMeasure P₀ := by dsimp only [P₀, γ]; infer_instance
  have hμb_fin : IsFiniteMeasure μ_base := inferInstance
  have hμb_ne : NeZero μ_base := inferInstance
  have hcav_raw := h_cav N P₀ μ_base hE₀_m hE₀_i π_sp hπ_m (by decide : (0 : Fin 2) ≠ 1)
    hs ⟨zero_le_one, le_rfl⟩ hq_mem hd hb hf₀_m hf₀_b
  dsimp only at hcav_raw
  -- Transport each of the 5 averages in `hcav_raw` to `P₁` and `ν_s ω`!
  let X₁ (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)
      (z : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp z.1))
      (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      Real.sqrt (1 - s) * Real.sqrt (1 - q) * z.2
  have hcoef_idx (idx : (Fin N ⊕ Unit) ⊕ Unit) :
      Measurable fun τ : Fin (N + 1) → ℤˣ =>
        (Sum.elim (Real.sqrt s • cavityCoef N 1 (Fin.init τ, τ (Fin.last N)))
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) idx := by
    rcases idx with (i | _) | _
    · dsimp only [cavityCoef, Sum.elim_inl, Pi.smul_apply, smul_eq_mul, Fin.init_def]
      exact measurable_const.mul
        (measurable_const.mul (measurable_units_cast.comp (measurable_pi_apply i.castSucc)))
    · dsimp only [cavityCoef, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
      exact measurable_const.mul
        (measurable_const.mul (measurable_units_cast.comp (measurable_pi_apply (Fin.last N))))
    · exact measurable_const
  have hf₀_lift_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
      f₀ q_p.1.1 (fun l => (q_p.2 l).1) := by
    have hl (l : Fin 2) (k : Fin M) : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
        Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, q_p.1.1.1.1 k i * ((((q_p.2 l).1.1 i : ℤ) : ℝ))) +
          Real.sqrt (1 - s) *
            (Real.sqrt q * q_p.1.1.1.2 k + Real.sqrt (1 - q) * (q_p.2 l).1.2 k) := by
      have hg_sum : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
          ∑ i : Fin (N + 1), q_p.1.1.1.1 k i * ((((q_p.2 l).1.1 i : ℤ) : ℝ)) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hgi : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
            (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => q_p.1.1.1.1 k i :=
          (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
            (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))))
        have hσi : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
            (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => (((q_p.2 l).1.1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp
              (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd))))
        exact hgi.mul hσi
      have hzk : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => q_p.1.1.1.2 k :=
        (measurable_pi_apply k).comp
          (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      have hξk : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => (q_p.2 l).1.2 k :=
        (measurable_pi_apply k).comp
          (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd)))
      exact ((hg_sum.const_mul _).const_mul _).add
        (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
    refine ((Finset.measurable_sum _ fun k _ => ?_).const_mul _).sub_const r
    exact ((measurable_deriv u).comp (hl 0 k)).mul ((measurable_deriv u).comp (hl 1 k))
  let splitΩ (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) :=
    (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
      Sum.elim (Sum.elim (Fin.init (ω.1.1 (Fin.last M)))
          (fun _ : Unit => ω.1.1 (Fin.last M) (Fin.last N)))
        (fun _ : Unit => ω.1.2 (Fin.last M)))
  have hX₁_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      X₁ (splitΩ ω).2 (interpStateLastSplit (N + 1) M x) = S_fn ω x (Fin.last M) := by
    rw [interpStateLastSplit_apply]
    dsimp only [X₁, splitΩ, π_sp, cavityCoef, S_fn]
    rw [sumElim_dotProduct_sumElim, smul_dotProduct, smul_eq_mul, sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h_sqrt1 : Real.sqrt (1 / ((N : ℝ) + 1)) = (Real.sqrt (N + 1 : ℕ))⁻¹ := by
      rw [one_div, Real.sqrt_inv]; push_cast; rfl
    rw [h_sqrt1, Fin.sum_univ_castSucc]
    simp only [Fin.init_def]
    have hsum_i :
        (∑ i : Fin N, (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i.castSucc : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i.castSucc) =
        (Real.sqrt (N + 1 : ℕ))⁻¹ *
          ∑ i : Fin N, ω.1.1 (Fin.last M) i.castSucc * ((x.1 i.castSucc : ℤ) : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum_i]; ring
  have hf₀_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      f₀ (splitΩ ω).1 (fun l => (interpStateLastSplit (N + 1) M (σ l)).1) = fMinus ω σ := by
    simp only [interpStateLastSplit_apply, f₀, fMinus, splitΩ, S_fn, Fin.init_def]
  have hX_fn_eq (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)
      (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ)) :
      Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp y.1))
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ y.2 = X₁ w₁ (y.1, y.2 1) := by
    dsimp only [X₁]; simp [dotProduct, Fin.sum_univ_two]
  -- 1. Weighted average transport:
  let H_w (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    f₀ p.1 (fun l => (z l).1) * (deriv u (X₁ p.2 (z 0)) * deriv u (X₁ p.2 (z 1)))
  have hHw_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => H_w q_p.1 q_p.2 := by
    have hzl (l : Fin 2) : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => deriv u (X₁ q_p.1.2 (q_p.2 l)) := by
      have hd1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
          Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (q_p.2 l).1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have ha : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
            (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
            (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (q_p.2 l).1))
              (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) idx :=
          (hcoef_idx idx).comp (measurable_fst.comp
            (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd)))
        exact ha.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have hd2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
          Real.sqrt (1 - s) * Real.sqrt (1 - q) * (q_p.2 l).2 :=
        measurable_const.mul (measurable_snd.comp ((measurable_pi_apply l).comp measurable_snd))
      exact (measurable_deriv u).comp (hd1.add hd2)
    exact hf₀_lift_m.mul ((hzl 0).mul (hzl 1))
  have htr_w := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_w) hHw_m
  -- 2. Unweighted average transport:
  let H_u (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    f₀ p.1 (fun l => (z l).1)
  have htr_u := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_u) hf₀_lift_m
  -- 3. First moment transport:
  let H_1 (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    |f₀ p.1 (fun l => (z l).1)|
  have hH1_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => H_1 q_p.1 q_p.2 := by
    simpa only [H_1, Real.norm_eq_abs] using hf₀_lift_m.norm
  have htr_1 := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_1) hH1_m
  -- 4. Second moment transport (`V_minus`):
  let H_2 (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    (f₀ p.1 (fun l => (z l).1)) ^ 2
  have htr_2 := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_2) (hf₀_lift_m.pow_const 2)
  -- 5. Overlap second moment transport (`Q_ov`):
  let d_spin (σ τ : PerceptronSpin N) : ℝ :=
    |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
      ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
  let H_ov (_p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    (d_spin (π_sp (z 0).1) (π_sp (z 1).1)) ^ 2
  have hHov_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => H_ov q_p.1 q_p.2 := by
    have hsum_sp : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
        ((∑ i : Fin N,
            ((((z 0).1.1 i.castSucc : ℤ) : ℝ) * (((z 1).1.1 i.castSucc : ℤ) : ℝ))) +
          ((((z 0).1.1 (Fin.last N) : ℤ) : ℝ) * (((z 1).1.1 (Fin.last N) : ℤ) : ℝ))) /
          (N + 1) - q := by
      have hs1 : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
          ∑ i : Fin N, ((((z 0).1.1 i.castSucc : ℤ) : ℝ) * (((z 1).1.1 i.castSucc : ℤ) : ℝ)) :=
        Finset.measurable_sum _ fun i _ =>
          (measurable_units_cast.comp ((measurable_pi_apply i.castSucc).comp
            (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 0))))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i.castSucc).comp
            (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 1)))))
      have hs2 : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
          ((((z 0).1.1 (Fin.last N) : ℤ) : ℝ) * (((z 1).1.1 (Fin.last N) : ℤ) : ℝ)) :=
        (measurable_units_cast.comp ((measurable_pi_apply (Fin.last N)).comp
          (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 0))))).mul
        (measurable_units_cast.comp ((measurable_pi_apply (Fin.last N)).comp
          (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 1)))))
      exact ((hs1.add hs2).div_const _).sub_const q
    have hsq_z : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
        (d_spin (π_sp (z 0).1) (π_sp (z 1).1)) ^ 2 := by
      have habs := hsum_sp.norm
      simpa only [d_spin, π_sp, Fin.init_def, Real.norm_eq_abs] using habs.pow_const 2
    exact hsq_z.comp measurable_snd
  have htr_ov := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_ov) hHov_m
  dsimp only at htr_w htr_u htr_1 htr_2 htr_ov
  -- Align `hcav_raw` with the full-system integrals!
  have hw_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        f₀ p.1 (fun l => (a l).1) *
          (deriv u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (a 0).1))
              (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
            ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
              Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ (a 0).2) *
          deriv u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (a 1).1))
              (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
            ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
              Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ (a 1).2))
        ∂(Measure.pi fun _ : Fin 2 =>
          ((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted
            (fun x => u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        fMinus ω σ * (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
    refine (integral_congr_ae (ae_of_all _ fun p =>
        integral_congr_ae (ae_of_all _ fun a => ?_))).trans
      (htr_w.trans (integral_congr_ae (ae_of_all _ fun ω =>
        integral_congr_ae (ae_of_all _ fun σ => ?_))))
    · dsimp only [H_w]; rw [hX_fn_eq p.2 (a 0), hX_fn_eq p.2 (a 1)]
    · dsimp only [H_w]
      rw [hf₀_split ω σ, hX₁_split ω (σ 0), hX₁_split ω (σ 1)]
  have hu_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        f₀ p.1 (fun l => (a l).1)
        ∂(Measure.pi fun _ : Fin 2 =>
          ((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted
            (fun x => u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        fMinus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ :=
    htr_u.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => hf₀_split ω σ)))
  have h1_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        |f₀ p.1 (fun l => (a l).1)|
        ∂(Measure.pi fun _ : Fin 2 =>
          ((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted
            (fun x => u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ :=
    htr_1.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => by dsimp only [H_1]; rw [hf₀_split ω σ])))
  have h2_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        (f₀ p.1 (fun l => (a l).1)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 =>
          ((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted
            (fun x => u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) = V_minus :=
    htr_2.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => by dsimp only [H_2]; rw [hf₀_split ω σ])))
  have hov_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        (d_spin (π_sp (a 0).1) (π_sp (a 1).1)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 =>
          ((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted
            (fun x => u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) = Q_ov := by
    refine htr_ov.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => ?_)))
    dsimp only [H_ov, d_spin, π_sp, R_obs]
    rw [sq_abs, interpStateLastSplit_apply, interpStateLastSplit_apply]
    simp only [Fin.init_def]
    congr 1
    rw [Fin.sum_univ_castSucc]
    ring
  rw [hw_eq, hu_eq, h1_eq, h2_eq, hov_eq] at hcav_raw
  -- Multiply `hcav_raw` by `α` and identify `α * (weighted - rhat * unweighted)` with
  -- `∫ ω, ∫ σ, (α * U_M - r) * fMinus`!
  have hP₁_prob : IsProbabilityMeasure P₁ := by dsimp only [P₁, γ]; infer_instance
  have hEs_slice (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (E_s ω) := by
    refine (Finset.measurable_sum _ fun k _ => hu.measurable.comp ?_).add ?_
    · refine (((Finset.measurable_sum _ fun i _ =>
        measurable_const.mul (measurable_units_cast.comp
          ((measurable_pi_apply i).comp measurable_fst))).const_mul _).const_mul _).add
        ((measurable_const.add
          (((measurable_pi_apply k).comp measurable_snd).const_mul _)).const_mul _)
    · exact Finset.measurable_sum _ fun i _ =>
        (((measurable_units_cast.comp
          ((measurable_pi_apply i).comp measurable_fst)).mul_const _).mul_const _).mul_const _
  have hν_prob (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (ν_s ω) := by
    have hbd (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        E_s ω x ≤ (M + 1 : ℕ) * |D| +
          ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
      refine add_le_add ((Finset.sum_le_sum fun _ _ => hD_le _).trans_eq (by simp))
        (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
    exact isProbabilityMeasure_tilted_of_ae_le (hEs_slice ω).aemeasurable (ae_of_all _ hbd)
  have hfMinus_b (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      |fMinus ω σ| ≤ 2 * α * |D| ^ 2 := by
    have h0 := hf₀_b (splitΩ ω).1 (fun l => (interpStateLastSplit (N + 1) M (σ l)).1)
    rwa [hf₀_split ω σ] at h0
  have hI1_minus_le :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤ 2 * α * |D| ^ 2 := by
    have h1 := abs_integral_le_of_forall_abs_le P₁
      (f := fun ω => ∫ σ, |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) fun ω =>
      abs_integral_le_of_forall_abs_le (Measure.pi fun _ : Fin 2 => ν_s ω)
        (f := fun σ => |fMinus ω σ|) fun σ => by
          rw [abs_abs]; exact hfMinus_b ω σ
    exact (le_abs_self _).trans h1
  -- Linearity of `α * weighted - r * unweighted`:
  have hEs_joint : Measurable fun p :
      (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => E_s p.1 p.2 := by
    refine (Finset.measurable_sum _ fun k _ => hu.measurable.comp ?_).add ?_
    · have hg_sum : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          ∑ i : Fin (N + 1), p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hgi : Measurable fun p :
            (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.1.1 k i :=
          (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
            (measurable_fst.comp (measurable_fst.comp measurable_fst)))
        have hσi : Measurable fun p :
            (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp measurable_snd))
        exact hgi.mul hσi
      have hzk : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.1.2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
      have hξk : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.2.2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
      exact ((hg_sum.const_mul _).const_mul _).add
        (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
    · refine Finset.measurable_sum _ fun i _ => ?_
      have hσi : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))
      have hz'i : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.2 i :=
        (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
      exact ((hσi.mul_const _).mul hz'i).mul_const _
  have hUk_joint (k : Fin (M + 1)) :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        deriv u (S_fn p.1 (p.2 0) k) * deriv u (S_fn p.1 (p.2 1) k) := by
    have hl (l : Fin 2) : Measurable fun p :
        (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => S_fn p.1 (p.2 l) k := by
      have hg_sum : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          ∑ i : Fin (N + 1), p.1.1.1 k i * ((((p.2 l).1 i : ℤ) : ℝ)) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hgi : Measurable fun p :
            (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.1.1 k i :=
          (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
            (measurable_fst.comp (measurable_fst.comp measurable_fst)))
        have hσi : Measurable fun p :
            (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => (((p.2 l).1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd)))
        exact hgi.mul hσi
      have hzk : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => p.1.1.2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
      have hξk : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => (p.2 l).2 k :=
        (measurable_pi_apply k).comp (measurable_snd.comp
          ((measurable_pi_apply l).comp measurable_snd))
      exact ((hg_sum.const_mul _).const_mul _).add
        (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)
    exact ((measurable_deriv u).comp (hl 0)).mul ((measurable_deriv u).comp (hl 1))
  have hfMinus_joint :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        fMinus p.1 p.2 :=
    ((Finset.measurable_sum _ fun k _ => hUk_joint k.castSucc).const_mul _).sub_const r
  have hf_joint :
      Measurable fun p : (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) ×
          (Fin (N + 1) → ℝ)) × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        f p.1 p.2 :=
    ((Finset.measurable_sum _ fun k _ => hUk_joint k).const_mul _).sub_const r
  have hS_slice (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (k : Fin (M + 1)) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) => S_fn ω x k := by
    have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
        ∑ i : Fin (N + 1), ω.1.1 k i * ((x.1 i : ℤ) : ℝ) :=
      Finset.measurable_sum _ fun i _ =>
        measurable_const.mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))
    have h2 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) => x.2 k :=
      (measurable_pi_apply k).comp measurable_snd
    exact ((h1.const_mul _).const_mul _).add
      ((measurable_const.add (h2.const_mul _)).const_mul _)
  have hUk_slice (k : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
        deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k) :=
    ((measurable_deriv u).comp ((hS_slice ω k).comp (measurable_pi_apply 0))).mul
      ((measurable_deriv u).comp ((hS_slice ω k).comp (measurable_pi_apply 1)))
  have hfMinus_slice
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (fMinus ω) :=
    ((Finset.measurable_sum _ fun k _ => hUk_slice k.castSucc ω).const_mul _).sub_const r
  have hf_slice
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (f ω) :=
    ((Finset.measurable_sum _ fun k _ => hUk_slice k ω).const_mul _).sub_const r
  let Gw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    fMinus ω σ * (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))
  have hGw_bound (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : |Gw ω σ| ≤ 2 * α * |D| ^ 4 := by
    dsimp only [Gw]
    rw [abs_mul, abs_mul]
    calc |fMinus ω σ| * (|deriv u (S_fn ω (σ 0) (Fin.last M))| *
          |deriv u (S_fn ω (σ 1) (Fin.last M))|)
        ≤ (2 * α * |D| ^ 2) * (|D| * |D|) :=
          mul_le_mul (hfMinus_b ω σ)
            (mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D))
            (by positivity) (by positivity)
      _ = 2 * α * |D| ^ 4 := by ring
  have hw_pt_int (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (Gw ω) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
    Integrable.of_bound ((hfMinus_slice ω).mul (hUk_slice (Fin.last M) ω)).aestronglyMeasurable
      (2 * α * |D| ^ 4) (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hGw_bound ω σ)
  have hu_pt_int (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fMinus ω) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
    Integrable.of_bound (hfMinus_slice ω).aestronglyMeasurable (2 * α * |D| ^ 2)
      (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hfMinus_b ω σ)
  have hw_out_int : Integrable (fun ω => ∫ σ, Gw ω σ
      ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P₁ :=
    integrable_integral_pi_tilted (μ := μ_s) hEs_joint hν_prob
      (G := Gw) (hfMinus_joint.mul (hUk_joint (Fin.last M))) hGw_bound
  have hu_out_int : Integrable (fun ω => ∫ σ, fMinus ω σ
      ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P₁ :=
    integrable_integral_pi_tilted (μ := μ_s) hEs_joint hν_prob hfMinus_joint hfMinus_b
  have hgminus_eq :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        (α * (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))) - r) *
          fMinus ω σ
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) =
      α * ((∫ ω, ∫ σ, fMinus ω σ *
          (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) -
        perceptronRhat u q * ∫ ω, ∫ σ, fMinus ω σ
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) := by
    have hpt (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        (∫ σ, (α * (deriv u (S_fn ω (σ 0) (Fin.last M)) *
            deriv u (S_fn ω (σ 1) (Fin.last M))) - r) * fMinus ω σ
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) =
        α * (∫ σ, fMinus ω σ *
            (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))
            ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) -
          r * ∫ σ, fMinus ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) := by
      have halg (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
          (α * (deriv u (S_fn ω (σ 0) (Fin.last M)) *
              deriv u (S_fn ω (σ 1) (Fin.last M))) - r) * fMinus ω σ =
          α * (fMinus ω σ * (deriv u (S_fn ω (σ 0) (Fin.last M)) *
              deriv u (S_fn ω (σ 1) (Fin.last M)))) - r * fMinus ω σ := by ring
      simp_rw [halg]
      have hsub := integral_sub ((hw_pt_int ω).const_mul α) ((hu_pt_int ω).const_mul r)
      rw [hsub, integral_const_mul, integral_const_mul]
    simp_rw [hpt]
    have hsub_P := integral_sub (hw_out_int.const_mul α) (hu_out_int.const_mul r)
    rw [hsub_P, integral_const_mul, integral_const_mul, hr]
    dsimp only [α]
    ring
  -- Combine `hgminus_eq` and `hcav_raw`!
  have hgminus_bd :
      (∫ ω, ∫ σ, (α * (deriv u (S_fn ω (σ 0) (Fin.last M)) *
          deriv u (S_fn ω (σ 1) (Fin.last M))) - r) * fMinus ω σ
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤
      (1 / 2) * Q_ov + (1 / 2) * V_minus + 2 * α * |D| ^ 2 / ((N : ℝ) + 1) := by
    rw [hgminus_eq]
    have h1 : α * ((∫ ω, ∫ σ, fMinus ω σ *
          (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) -
        perceptronRhat u q * ∫ ω, ∫ σ, fMinus ω σ
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤
        α * (K_cav * (V_minus ^ (1 / (2 : ℝ)) * Q_ov ^ (1 / (2 : ℝ)) +
          1 / ((N : ℝ) + 1) *
            ∫ ω, ∫ σ, |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁)) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_of_nonneg hα0]
      exact mul_le_mul_of_nonneg_left hcav_raw hα0
    have hprod_amgm : V_minus ^ (1 / (2 : ℝ)) * Q_ov ^ (1 / (2 : ℝ)) ≤
        (1 / 2) * Q_ov + (1 / 2) * V_minus := by
      have hs1 : V_minus ^ (1 / (2 : ℝ)) = Real.sqrt V_minus := (Real.sqrt_eq_rpow V_minus).symm
      have hs2 : Q_ov ^ (1 / (2 : ℝ)) = Real.sqrt Q_ov := (Real.sqrt_eq_rpow Q_ov).symm
      rw [hs1, hs2]
      have h_alg : (1 / 2) * (Real.sqrt Q_ov ^ 2 + Real.sqrt V_minus ^ 2) -
          Real.sqrt V_minus * Real.sqrt Q_ov =
          (1 / 2) * (Real.sqrt Q_ov - Real.sqrt V_minus) ^ 2 := by ring
      have h_nn : 0 ≤ (1 / 2) * (Real.sqrt Q_ov - Real.sqrt V_minus) ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      rw [← h_alg, Real.sq_sqrt hQov0, Real.sq_sqrt hVminus0] at h_nn
      have h_distr : (1 / 2) * (Q_ov + V_minus) = (1 / 2) * Q_ov + (1 / 2) * V_minus := by ring
      rw [h_distr] at h_nn
      exact sub_nonneg.1 h_nn
    have hI1_div : 1 / ((N : ℝ) + 1) *
        (∫ ω, ∫ σ, |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤
        2 * α * |D| ^ 2 / ((N : ℝ) + 1) := by
      calc 1 / ((N : ℝ) + 1) * _ ≤ 1 / ((N : ℝ) + 1) * (2 * α * |D| ^ 2) :=
            mul_le_mul_of_nonneg_left hI1_minus_le (by positivity)
        _ = 2 * α * |D| ^ 2 / ((N : ℝ) + 1) := by ring
    have hinner_nonneg : 0 ≤ V_minus ^ (1 / (2 : ℝ)) * Q_ov ^ (1 / (2 : ℝ)) +
        1 / ((N : ℝ) + 1) *
          ∫ ω, ∫ σ, |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ :=
      add_nonneg (by positivity) (mul_nonneg (by positivity)
        (integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _))
    calc α * (_ - _)
        ≤ α * (K_cav * (V_minus ^ (1 / (2 : ℝ)) * Q_ov ^ (1 / (2 : ℝ)) +
            1 / ((N : ℝ) + 1) *
              ∫ ω, ∫ σ, |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁)) := h1
      _ = (α * K_cav) * (V_minus ^ (1 / (2 : ℝ)) * Q_ov ^ (1 / (2 : ℝ)) +
            1 / ((N : ℝ) + 1) *
              ∫ ω, ∫ σ, |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) := by ring
      _ ≤ 1 * (V_minus ^ (1 / (2 : ℝ)) * Q_ov ^ (1 / (2 : ℝ)) +
            1 / ((N : ℝ) + 1) *
              ∫ ω, ∫ σ, |fMinus ω σ| ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) :=
          mul_le_mul_of_nonneg_right hα_cav hinner_nonneg
      _ ≤ ((1 / 2) * Q_ov + (1 / 2) * V_minus) + 2 * α * |D| ^ 2 / ((N : ℝ) + 1) := by
          rw [one_mul]; exact add_le_add hprod_amgm hI1_div
      _ = (1 / 2) * Q_ov + (1 / 2) * V_minus + 2 * α * |D| ^ 2 / ((N : ℝ) + 1) := by ring
  -- Step 3: Bound `V_minus ≤ V_f + 5 * |D| ^ 4 / (N + 1)`!
  have hVminus_le : V_minus ≤ V_f + 5 * |D| ^ 4 / ((N : ℝ) + 1) := by
    let err_v : ℝ := 5 * |D| ^ 4 / ((N : ℝ) + 1)
    have hf_b (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : |f ω σ| ≤ 2 * α * |D| ^ 2 := by
      dsimp only [f]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      have hs_b : |∑ k : Fin (M + 1), deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)| ≤
          ((M + 1 : ℕ) : ℝ) * |D| ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun k _ => ?_).trans_eq
          (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
        rw [abs_mul, sq]
        exact mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D)
      have h1 : ((N : ℝ) + 1)⁻¹ *
          |∑ k : Fin (M + 1), deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)| ≤
          α * |D| ^ 2 := by
        calc _ ≤ ((N : ℝ) + 1)⁻¹ * (((M + 1 : ℕ) : ℝ) * |D| ^ 2) :=
              mul_le_mul_of_nonneg_left hs_b (by positivity)
          _ = α * |D| ^ 2 := by dsimp only [α]; ring
      linarith [hr_abs]
    have hpt_sq (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        (fMinus ω σ) ^ 2 ≤ (f ω σ) ^ 2 + err_v := by
      have hdiff : fMinus ω σ - f ω σ =
          -(((N : ℝ) + 1)⁻¹ *
            (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))) := by
        dsimp only [f, fMinus]
        rw [Fin.sum_univ_castSucc]
        ring
      have hdiff_abs : |fMinus ω σ - f ω σ| ≤ |D| ^ 2 / ((N : ℝ) + 1) := by
        rw [hdiff, abs_neg, abs_mul, abs_inv,
          abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1), abs_mul, sq]
        calc ((N : ℝ) + 1)⁻¹ * (|deriv u (S_fn ω (σ 0) (Fin.last M))| *
              |deriv u (S_fn ω (σ 1) (Fin.last M))|)
            ≤ ((N : ℝ) + 1)⁻¹ * (|D| * |D|) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D)) (by positivity)
          _ = (|D| * |D|) / ((N : ℝ) + 1) := by ring
      have hsum_abs : |fMinus ω σ + f ω σ| ≤ 4 * |D| ^ 2 := by
        have h1 := (abs_add_le (fMinus ω σ) (f ω σ)).trans
          (add_le_add (hfMinus_b ω σ) (hf_b ω σ))
        have h2 : 4 * α * |D| ^ 2 ≤ 4 * 1 * |D| ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hα_le1 (by norm_num)) (sq_nonneg _)
        linarith
      have hsq_sub : |(fMinus ω σ) ^ 2 - (f ω σ) ^ 2| ≤ 4 * |D| ^ 4 / ((N : ℝ) + 1) := by
        rw [sq_sub_sq, mul_comm (fMinus ω σ + f ω σ), abs_mul]
        calc |fMinus ω σ - f ω σ| * |fMinus ω σ + f ω σ|
            ≤ (|D| ^ 2 / ((N : ℝ) + 1)) * (4 * |D| ^ 2) :=
              mul_le_mul hdiff_abs hsum_abs (abs_nonneg _) (by positivity)
          _ = 4 * |D| ^ 4 / ((N : ℝ) + 1) := by ring
      have h45 : 4 * |D| ^ 4 / ((N : ℝ) + 1) ≤ err_v := by
        dsimp only [err_v]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (abs_nonneg D) 4)) (by positivity)
      have hle := ((le_abs_self _).trans hsq_sub).trans h45
      exact sub_le_iff_le_add'.1 hle
    exact integral_integral_pi_tilted_sq_le_add (μ := μ_s) hEs_joint hν_prob hfMinus_joint
      hf_joint (fun ω σ => hfMinus_b ω σ) hf_b hpt_sq
  -- Step 4: Assemble and absorb `(1 / 2) * V_f`!
  have herr_split : (α * |(|D|)| ^ 2 + |r|) * |(|D|)| ^ 2 / ((N : ℝ) + 1) ≤
      2 * |D| ^ 4 / ((N : ℝ) + 1) := by
    rw [abs_abs]
    have h1 : α * |D| ^ 2 + |r| ≤ 2 * |D| ^ 2 := by
      have ha1 : α * |D| ^ 2 ≤ 1 * |D| ^ 2 :=
        mul_le_mul_of_nonneg_right hα_le1 (sq_nonneg _)
      linarith [hr_abs]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc (α * |D| ^ 2 + |r|) * |D| ^ 2 ≤ (2 * |D| ^ 2) * |D| ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 2 * |D| ^ 4 := by ring
  have herr_cav : 2 * α * |D| ^ 2 / ((N : ℝ) + 1) ≤ 2 * |D| ^ 2 / ((N : ℝ) + 1) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc 2 * α * |D| ^ 2 ≤ 2 * 1 * |D| ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα_le1 zero_le_two) (sq_nonneg _)
      _ = 2 * |D| ^ 2 := by ring
  have hVf_step1 : V_f ≤
      ((1 / 2) * Q_ov + (1 / 2) * V_minus + 2 * |D| ^ 2 / ((N : ℝ) + 1)) +
      2 * |D| ^ 4 / ((N : ℝ) + 1) := by
    refine hsplit.trans (add_le_add ?_ herr_split)
    exact hgminus_bd.trans (add_le_add le_rfl herr_cav)
  have hVf_step2 : V_f ≤
      (1 / 2) * Q_ov + (1 / 2) * (V_f + 5 * |D| ^ 4 / ((N : ℝ) + 1)) +
      2 * |D| ^ 2 / ((N : ℝ) + 1) + 2 * |D| ^ 4 / ((N : ℝ) + 1) := by
    have hvm : (1 / 2) * V_minus ≤ (1 / 2) * (V_f + 5 * |D| ^ 4 / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hVminus_le (by positivity)
    linarith [hVf_step1]
  have hhalf_Vf : (1 / 2) * V_f ≤
      (1 / 2) * (L_ov / ((N : ℝ) + 1)) + (9 / 2) * (|D| ^ 4 / ((N : ℝ) + 1)) +
      2 * (|D| ^ 2 / ((N : ℝ) + 1)) := by
    have hq_half : (1 / 2) * Q_ov ≤ (1 / 2) * (L_ov / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hQov_le (by positivity)
    have hd4_rew : ∀ c : ℝ, c * |D| ^ 4 / ((N : ℝ) + 1) = c * (|D| ^ 4 / ((N : ℝ) + 1)) :=
      fun _ => by ring
    have hd2_rew : 2 * |D| ^ 2 / ((N : ℝ) + 1) = 2 * (|D| ^ 2 / ((N : ℝ) + 1)) := by ring
    rw [hd4_rew 5, hd4_rew 2, hd2_rew] at hVf_step2
    linarith
  have hVf_final : V_f ≤ (L_ov + 9 * |D| ^ 4 + 4 * |D| ^ 2) / ((N : ℝ) + 1) := by
    have h2 := mul_le_mul_of_nonneg_left hhalf_Vf zero_le_two
    calc V_f = 2 * ((1 / 2) * V_f) := by ring
      _ ≤ 2 * ((1 / 2) * (L_ov / ((N : ℝ) + 1)) + (9 / 2) * (|D| ^ 4 / ((N : ℝ) + 1)) +
            2 * (|D| ^ 2 / ((N : ℝ) + 1))) := h2
      _ = (L_ov + 9 * |D| ^ 4 + 4 * |D| ^ 2) / ((N : ℝ) + 1) := by ring
  exact hVf_final

end EmpiricalVariance

end SpinGlasses
