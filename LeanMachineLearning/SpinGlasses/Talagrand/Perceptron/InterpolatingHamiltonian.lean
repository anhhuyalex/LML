/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingOverlap
public import LeanMachineLearning.SpinGlasses.Gibbs.GibbsMeasure
public import LeanMachineLearning.SpinGlasses.Talagrand.DecoupledSystems.SKDecoupled
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPLinear

/-!
# The `s`-interpolating free energy and derivative identity (Talagrand Section 2.4, Eqs. (2.76)--(2.83))

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.76),
(2.81)--(2.83) and endpoint evaluations at `s = 0` and `s = 1`.

For `N + 1` spins and `M` constraints, the `s`-interpolating Hamiltonian (`s ∈ [0, 1]`) is
$$-H_{M, N+1, s}(\sigma, \xi) =
  \sum_{k < M} u\!\left(\sqrt{s}\,S_k(\sigma) +
    \sqrt{1 - s}\,(\sqrt{q}\,z_k + \sqrt{1 - q}\,\xi_k)\right) +
  \sum_{i < N + 1} \sigma_i \sqrt{1 - s}\,z'_i \sqrt{r},$$
with normalized expected log-partition function (pressure)
$$p_{N+1, M, s}(u) = \frac{1}{N + 1}\,\mathbb{E}\log\int_{\mathbb{R}^M}\sum_\sigma
  \exp(-H_{M, N+1, s}(\sigma, \xi))\,\mathrm{d}\gamma(\xi).$$

## Main declarations

* `SpinGlasses.continuousOn_interpolating_pressure`: continuity of `s ↦ p_{N+1, M, s}(u)` on `[0, 1]`.
* `SpinGlasses.interpolating_pressure_one_eq`: at `s = 1`, `p_{N+1, M, 1}(u)` equals the Section 2.1
  perceptron pressure `p_{N+1, M}(u)`.
* `SpinGlasses.interpolating_pressure_zero_eq`: at `s = 0` (when `r ≥ 0`), `p_{N+1, M, 0}(u)` equals
  `log 2 + 𝔼 log cosh(z √r) + (M / (N + 1)) 𝔼 log 𝔼_ξ exp u(√q z + √(1 - q) ξ)`.
* `SpinGlasses.hasDerivAt_interpolating_pressure_regrouped`: Eq. (2.83), on `s ∈ (0, 1)`,
  $$\frac{\mathrm{d}}{\mathrm{d}s} p_{N+1, M, s}(u) = -\frac{r}{2}(1 - q) -
    \frac{1}{2}\,\nu_s\!\left((R_{1,2} - q)\left(\frac{1}{N + 1}
      \sum_{k < M} u'(S_{k, s}^1) u'(S_{k, s}^2) - r\right)\right).$$
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

section PressureAndEndpoints

/-- Marginalization of the auxiliary Gaussian vector `ξ : Fin M → ℝ` inside the partition function:
`∫ ξ, ∑ σ, exp (E_s ω (σ, ξ)) dγ_M = ∑ σ, exp (E_eff ω σ)`. -/
private lemma integral_sum_exp_interpolating_eq
    {L M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) :
    let γ_M := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let μ_s := (Measure.count : Measure (Fin L → ℤˣ)).prod γ_M
    let E_s (x : (Fin L → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin L, ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ∫ x, Real.exp (E_s x) ∂μ_s =
      ∑ τ : Fin L → ℤˣ, Real.exp
        ((∑ i : Fin L, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
          ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
              ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
            ∂gaussianReal 0 1)) := by
  intro γ_M μ_s E_s
  have hEm : Measurable E_s := by
    refine (Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)).add ?_
    fun_prop
  have hEb (x : (Fin L → ℤˣ) × (Fin M → ℝ)) :
      E_s x ≤ M * B + ∑ i : Fin L, |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    dsimp only [E_s]
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hi : Integrable (fun x => Real.exp (E_s x)) μ_s :=
    integrable_exp_of_ae_le hEm.aemeasurable (ae_of_all _ hEb)
  dsimp only [μ_s]
  rw [integral_prod _ hi, integral_fintype Integrable.of_finite]
  simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hsplit (ξ : Fin M → ℝ) :
      Real.exp (E_s (τ, ξ)) =
        Real.exp (∑ i : Fin L, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) *
          ∏ k : Fin M, Real.exp (u (Real.sqrt s *
              ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ k))) := by
    dsimp only [E_s]
    rw [add_comm, Real.exp_add]
    congr 1
    exact Real.exp_sum _ _
  simp_rw [hsplit]
  rw [integral_const_mul,
    integral_fintype_prod_eq_prod (μ := fun _ : Fin M => gaussianReal 0 1)
      (fun k ξ => Real.exp (u (Real.sqrt s *
          ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ))))]
  rw [Real.exp_add]
  congr 1
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun k _ => (Real.exp_log ?_).symm
  exact integral_exp_pos_of_ae_le (hu.comp (by fun_prop)).aemeasurable
    (ae_of_all _ fun _ => hB _)

/-- **Continuity of the `s`-interpolating pressure `p_{N+1, M, s}(u)` on `[0, 1]`.** -/
theorem continuousOn_interpolating_pressure
    {N M : ℕ} {u : ℝ → ℝ} (hu : Continuous u) {B : ℝ} (hB : ∀ x, |u x| ≤ B) (q r : ℝ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (s : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ContinuousOn
      (fun s => ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_s s ω x) ∂μ_s) ∂P)
      (Icc (0 : ℝ) 1) := by
  intro P_g P_z P_z' P μ_s E_s
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let Φ (s : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    Real.log (∫ x, Real.exp (E_s s ω x) ∂μ_s)
  let E_eff (s : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
      ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
        ∂gaussianReal 0 1)
  have hΦ_eq (s : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Φ s ω = Real.log (∑ τ, Real.exp (E_eff s ω τ)) := by
    dsimp only [Φ, E_eff]
    rw [integral_sum_exp_interpolating_eq hu.measurable hB_le s q r ω]
  have hE_eff_m (s : ℝ) (τ : Fin (N + 1) → ℤˣ) : Measurable fun ω => E_eff s ω τ := by
    refine (Finset.measurable_sum _ fun i _ => by fun_prop).add ?_
    refine Finset.measurable_sum _ fun k _ => Real.measurable_log.comp ?_
    have hj : Measurable fun p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) × ℝ =>
        Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2))) :=
      Real.measurable_exp.comp (hu.measurable.comp (by fun_prop))
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hΦm (s : ℝ) : AEStronglyMeasurable (Φ s) P := by
    have heq : Φ s = fun ω => Real.log (∑ τ, Real.exp (E_eff s ω τ)) := funext (hΦ_eq s)
    rw [heq]
    exact (Real.measurable_log.comp
      (Finset.measurable_sum _ fun τ _ => Real.measurable_exp.comp (hE_eff_m s τ))).aestronglyMeasurable
  let dom (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1) * Real.log 2 + M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
  have hdom_int : Integrable dom P := by
    refine ((integrable_const _).add (integrable_const _)).add ?_
    refine integrable_finsetSum _ fun i _ => ?_
    have hi : Integrable (fun z' : Fin (N + 1) → ℝ => |z' i| * Real.sqrt r) P_z' :=
      (integrable_comp_eval (μ := fun _ : Fin (N + 1) => gaussianReal 0 1) (i := i)
        IsGaussian.integrable_id.abs).mul_const _
    exact hi.comp_snd _
  have hΦb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      ‖Φ s ω‖ ≤ dom ω := by
    rw [hΦ_eq s, Real.norm_eq_abs]
    have hsqrt1 : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.2 (by linarith [hs.1])
    have hEb_τ (τ : Fin (N + 1) → ℤˣ) :
        |E_eff s ω τ| ≤ M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
      dsimp only [E_eff]
      refine (abs_add_le _ _).trans ?_
      rw [add_comm ((M : ℝ) * B)]
      refine add_le_add ?_ ?_
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (1 - s) * |ω.2 i| * Real.sqrt r
            ≤ 1 * |ω.2 i| * Real.sqrt r :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsqrt1 (abs_nonneg _))
                (Real.sqrt_nonneg _)
          _ = |ω.2 i| * Real.sqrt r := by ring
      · refine ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := B) fun k => ?_).trans_eq (by simp))
        exact abs_log_integral_exp_le_of_ae_abs_le (hu.measurable.comp (by fun_prop)).aemeasurable
          (ae_of_all _ fun _ => hB _)
    have hsub := abs_log_sum_exp_sub_log_card_le (E_eff s ω) hEb_τ
    have hcard : Real.log (Fintype.card (Fin (N + 1) → ℤˣ) : ℝ) = ((N : ℝ) + 1) * Real.log 2 := by
      rw [card_spin_configurations, Fintype.card_fin]
      push_cast; rw [Real.log_pow]; push_cast; ring
    rw [hcard] at hsub
    have htri := (abs_add_le (Real.log (∑ τ, Real.exp (E_eff s ω τ)) - ((N : ℝ) + 1) * Real.log 2)
      (((N : ℝ) + 1) * Real.log 2))
    rw [sub_add_cancel, abs_of_nonneg (mul_nonneg (by positivity) (Real.log_nonneg one_le_two))]
      at htri
    dsimp only [dom]
    linarith
  have hΦ_cont (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Continuous (fun s => Φ s ω) := by
    have heq_s : (fun s => Φ s ω) = fun s => Real.log (∑ τ, Real.exp (E_eff s ω τ)) :=
      funext fun s => hΦ_eq s ω
    rw [heq_s]
    have hg_cont (τ : Fin (N + 1) → ℤˣ) (k : Fin M) :
        Continuous fun s : ℝ => ∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1 := by
      refine continuous_of_dominated (bound := fun _ => Real.exp B)
        (fun s => (Real.continuous_exp.comp (hu.comp (by fun_prop))).measurable.aestronglyMeasurable)
        (fun s => ae_of_all _ fun _ => by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.2 (hB_le _))
        (integrable_const _)
        (ae_of_all _ fun _ => Real.continuous_exp.comp (hu.comp (by fun_prop)))
    have hg_pos (s : ℝ) (τ : Fin (N + 1) → ℤˣ) (k : Fin M) :
        0 < ∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1 :=
      integral_exp_pos_of_ae_le (hu.measurable.comp (by fun_prop)).aemeasurable
        (ae_of_all _ fun _ => hB_le _)
    have hE_cont (τ : Fin (N + 1) → ℤˣ) : Continuous fun s => E_eff s ω τ := by
      have h1 : Continuous fun s : ℝ =>
          ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r := by
        fun_prop
      have h2_each (k : Fin M) : Continuous fun s : ℝ =>
          Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
            ∂gaussianReal 0 1) :=
        (hg_cont τ k).log fun s => (hg_pos s τ k).ne'
      have h2 : Continuous fun s : ℝ =>
          ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
            ∂gaussianReal 0 1) := by
        fun_prop
      exact h1.add h2
    have hsum_cont : Continuous fun s : ℝ => ∑ τ, Real.exp (E_eff s ω τ) := by
      fun_prop
    exact hsum_cont.log fun s => (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  refine continuousOn_const.mul ?_
  exact continuousOn_of_dominated (fun s _ => hΦm s) (fun s hs => ae_of_all _ (hΦb s hs))
    hdom_int (ae_of_all _ fun ω => (hΦ_cont ω).continuousOn)

/-- **Endpoint `s = 1`:** `p_{N+1, M, 1}(u)` equals the Section 2.1 perceptron pressure
`p_{N+1, M}(u)`. -/
theorem interpolating_pressure_one_eq
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B) (q r : ℝ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_1 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt 1 *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 1) * ω.2 i * Real.sqrt r
    ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_1 ω x) ∂μ_s) ∂P =
      ((N : ℝ) + 1)⁻¹ * ∫ g : Fin M → Fin (N + 1) → ℝ,
        Real.log (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))))
        ∂P_g := by
  intro P_g P_z P_z' P μ_s E_1
  congr 1
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Real.log (∫ x, Real.exp (E_1 ω x) ∂μ_s) =
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)))) := by
    rw [integral_sum_exp_interpolating_eq hu hB_le 1 q r ω]
    congr 1; refine Finset.sum_congr rfl fun τ _ => congrArg Real.exp ?_
    simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, one_mul, mul_zero, zero_mul, add_zero,
      Finset.sum_const_zero, zero_add, integral_const, probReal_univ, one_smul, Real.log_exp]
  simp_rw [hpt]
  have h1 := integral_prod_fun_fst_of_isProbabilityMeasure (μ := P_g.prod P_z) (ν := P_z')
    (fun gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ) =>
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, gz.1 k i * ((τ i : ℤ) : ℝ)))))
  have h2 := integral_prod_fun_fst_of_isProbabilityMeasure (μ := P_g) (ν := P_z)
    (fun g : Fin M → Fin (N + 1) → ℝ =>
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))))
  exact h1.trans h2

/-- **Endpoint `s = 0`:** the spins decouple into i.i.d. local fields `z'_i √r` and the
constraints decouple into `M` i.i.d. copies of `log 𝔼_ξ exp u(√q z + √(1 - q) ξ)`, giving
`p_{N+1, M, 0}(u) = log 2 + 𝔼 log cosh(z √r) + (M / (N + 1)) 𝔼 log 𝔼_ξ exp u(θ)`. -/
theorem interpolating_pressure_zero_eq
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q r : ℝ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt 0 *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - 0) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 0) * ω.2 i * Real.sqrt r
    ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_0 ω x) ∂μ_s) ∂P =
      Real.log 2 + (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1) +
        ((M : ℝ) / ((N : ℝ) + 1)) *
          ∫ z : ℝ, Real.log (∫ ξ : ℝ,
            Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
          ∂gaussianReal 0 1 := by
  intro P_g P_z P_z' P μ_s E_0
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let ψ_z (z : ℝ) : ℝ :=
    Real.log (∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ₁)
  have hψ_m : Measurable ψ_z := by
    refine Real.measurable_log.comp ?_
    have hj : Measurable fun p : ℝ × ℝ =>
        Real.exp (u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2)) :=
      Real.measurable_exp.comp (hu.comp (by fun_prop))
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ₁)).measurable
  have hψ_b (z : ℝ) : |ψ_z z| ≤ |B| :=
    (abs_log_integral_exp_le_of_ae_abs_le (hu.comp (by fun_prop)).aemeasurable
      (ae_of_all _ fun _ => hB _)).trans (le_abs_self B)
  have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Real.log (∫ x, Real.exp (E_0 ω x) ∂μ_s) =
      (((N : ℝ) + 1) * Real.log 2 + ∑ i : Fin (N + 1), Real.log (Real.cosh (ω.2 i * Real.sqrt r))) +
        ∑ k : Fin M, ψ_z (ω.1.2 k) := by
    rw [integral_sum_exp_interpolating_eq hu hB_le 0 q r ω]
    have hsimp (τ : Fin (N + 1) → ℤˣ) :
        Real.exp ((∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - 0) * ω.2 i * Real.sqrt r) +
          ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt 0 *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - 0) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ))) ∂γ₁)) =
        Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * (ω.2 i * Real.sqrt r)) *
          Real.exp (∑ k : Fin M, ψ_z (ω.1.2 k)) := by
      rw [← Real.exp_add]
      congr 1
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
        (Finset.sum_congr rfl fun k _ => ?_)
      · rw [sub_zero, Real.sqrt_one]; ring
      · dsimp only [ψ_z, γ₁]
        congr 1; refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
        dsimp only
        rw [Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul]
    rw [Finset.sum_congr rfl fun τ _ => hsimp τ, ← Finset.sum_mul]
    have hsum_pos : 0 < ∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * (ω.2 i * Real.sqrt r)) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    rw [Real.log_mul hsum_pos.ne' (Real.exp_pos _).ne', Real.log_exp,
      log_decoupled_partition_function_eq (fun i : Fin (N + 1) => ω.2 i * Real.sqrt r),
      Fintype.card_fin]
    push_cast; rfl
  simp_rw [hpt]
  have hlc_m : Measurable (fun x : ℝ => Real.log (Real.cosh (x * Real.sqrt r))) :=
    (Real.continuous_cosh.comp (by fun_prop)).log (fun _ => (Real.cosh_pos _).ne') |>.measurable
  have hlc_int1 : Integrable (fun z : ℝ => Real.log (Real.cosh (z * Real.sqrt r))) γ₁ := by
    have h1 := integrable_log_cosh_affine_gaussianReal (Real.sqrt r) 0
    refine h1.congr (ae_of_all _ fun z => ?_)
    change Real.log (Real.cosh (Real.sqrt r * z + 0)) = Real.log (Real.cosh (z * Real.sqrt r))
    congr 2; ring
  have hA_int : Integrable
      (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
        ((N : ℝ) + 1) * Real.log 2 +
          ∑ i : Fin (N + 1), Real.log (Real.cosh (ω.2 i * Real.sqrt r))) P := by
    refine (integrable_const _).add (integrable_finsetSum _ fun i _ => ?_)
    have hi : Integrable (fun z' : Fin (N + 1) → ℝ => Real.log (Real.cosh (z' i * Real.sqrt r)))
        P_z' :=
      integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i) hlc_int1
    exact hi.comp_snd _
  have hB_int : Integrable
      (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
        ∑ k : Fin M, ψ_z (ω.1.2 k)) P := by
    refine integrable_finsetSum _ fun k _ => ?_
    have hk1 : Integrable ψ_z γ₁ :=
      Integrable.of_bound hψ_m.aestronglyMeasurable |B|
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hψ_b z)
    have hk2 : Integrable (fun z : Fin M → ℝ => ψ_z (z k)) P_z :=
      integrable_comp_eval (μ := fun _ : Fin M => γ₁) (i := k) hk1
    exact (hk2.comp_snd _).comp_fst _
  rw [integral_add hA_int hB_int]
  have hI_A : (∫ ω, (((N : ℝ) + 1) * Real.log 2 +
        ∑ i : Fin (N + 1), Real.log (Real.cosh (ω.2 i * Real.sqrt r))) ∂P) =
      ((N : ℝ) + 1) * (Real.log 2 + ∫ z, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ₁) := by
    have hsnd := integral_prod_fun_snd_of_isProbabilityMeasure (μ := P_g.prod P_z) (ν := P_z')
      (fun z' : Fin (N + 1) → ℝ =>
        ((N : ℝ) + 1) * Real.log 2 + ∑ i : Fin (N + 1), Real.log (Real.cosh (z' i * Real.sqrt r)))
    dsimp only [P]
    rw [hsnd,
      integral_add (integrable_const _) (integrable_finsetSum _ fun i _ =>
        integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i) hlc_int1),
      integral_const, probReal_univ, one_smul,
      integral_finsetSum _ fun i _ =>
        integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i) hlc_int1]
    have heach (i : Fin (N + 1)) :
        (∫ z' : Fin (N + 1) → ℝ, Real.log (Real.cosh (z' i * Real.sqrt r)) ∂P_z') =
        ∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ₁ := by
      have h := (measurePreserving_eval (fun _ : Fin (N + 1) => γ₁) i).integral_comp_of_aestronglyMeasurable
        hlc_m.aestronglyMeasurable
      exact h
    rw [Finset.sum_congr rfl fun i _ => heach i,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hI_B : (∫ ω, (∑ k : Fin M, ψ_z (ω.1.2 k)) ∂P) = (M : ℝ) * ∫ z, ψ_z z ∂γ₁ := by
    have hfst := integral_prod_fun_fst_of_isProbabilityMeasure (μ := P_g.prod P_z) (ν := P_z')
      (fun gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ) => ∑ k : Fin M, ψ_z (gz.2 k))
    have hsnd := integral_prod_fun_snd_of_isProbabilityMeasure (μ := P_g) (ν := P_z)
      (fun z : Fin M → ℝ => ∑ k : Fin M, ψ_z (z k))
    dsimp only [P]
    rw [hfst, hsnd]
    have hk1 : Integrable ψ_z γ₁ :=
      Integrable.of_bound hψ_m.aestronglyMeasurable |B|
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hψ_b z)
    rw [integral_finsetSum _ fun k _ =>
      integrable_comp_eval (μ := fun _ : Fin M => γ₁) (i := k) hk1]
    have heach (k : Fin M) : (∫ z : Fin M → ℝ, ψ_z (z k) ∂P_z) = ∫ z, ψ_z z ∂γ₁ := by
      have h := (measurePreserving_eval (fun _ : Fin M => γ₁) k).integral_comp_of_aestronglyMeasurable
        hψ_m.aestronglyMeasurable
      exact h
    rw [Finset.sum_congr rfl fun k _ => heach k,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hI_A, hI_B]
  dsimp only [γ₁, ψ_z]
  have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
  generalize (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1) = I_cosh
  generalize (∫ z : ℝ, Real.log (∫ ξ : ℝ,
    Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
    ∂gaussianReal 0 1) = I_pot
  field_simp

end PressureAndEndpoints

section DerivativeAndIBP

/-- **Differentiation of the `s`-interpolating pressure (Eq. (2.81)):**
for `s ∈ (0, 1)`, `d/ds p_{N+1, M, s}(u) = (N + 1)⁻¹ * ν_s(∂_s(-H_{M, N+1, s}))`. -/
theorem hasDerivAt_interpolating_pressure
    {N M : ℕ} {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (q r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
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
    let S'_fn (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      (1 / (2 * Real.sqrt s')) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s'))) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let E_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (S_fn s' ω x k)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
    HasDerivAt
      (fun s' => ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s) ∂P)
      (((N : ℝ) + 1)⁻¹ * ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn s ω x k * deriv u (S_fn s ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s s ω)) ∂P) s := by
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s
  have hum : Measurable u := hu.continuous.measurable
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hD₁0 : 0 ≤ |D₁| := abs_nonneg D₁
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let γ_M := Measure.pi fun _ : Fin M => γ₁
  let E'_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (∑ k : Fin M, S'_fn s' ω x k * deriv u (S_fn s' ω x k)) -
      (1 / (2 * Real.sqrt (1 - s'))) *
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r
  let δ : ℝ := min (s / 2) ((1 - s) / 2)
  have hδ : 0 < δ := lt_min (half_pos hs.1) (half_pos (sub_pos.2 hs.2))
  let U_nbhd : Set ℝ := Ioo (s - δ) (s + δ)
  have hU_nhds : U_nbhd ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hs'_b {s' : ℝ} (hs' : s' ∈ U_nbhd) : δ ≤ s' ∧ δ ≤ 1 - s' ∧ 0 < s' ∧ s' < 1 := by
    have h1 : δ ≤ s / 2 := min_le_left _ _
    have h2 : δ ≤ (1 - s) / 2 := min_le_right _ _
    refine ⟨by linarith [hs'.1], by linarith [hs'.2], by linarith [hs'.1], by linarith [hs'.2]⟩
  -- Pointwise derivative of `E_s s' ω x` on `U_nbhd`!
  have hd_E (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) {s' : ℝ} (hs' : s' ∈ U_nbhd) :
      HasDerivAt (fun t => E_s t ω x) (E'_s s' ω x) s' := by
    obtain ⟨-, -, hs'0, hs'1⟩ := hs'_b hs'
    have hsq1 := Real.hasDerivAt_sqrt hs'0.ne'
    have hsq2 := ((hasDerivAt_id s').const_sub 1).sqrt (sub_pos.2 hs'1).ne'
    have hsq2' : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t)) (-1 / (2 * Real.sqrt (1 - s'))) s' :=
      hsq2
    have hS_k (k : Fin M) : HasDerivAt (fun t => S_fn t ω x k) (S'_fn s' ω x k) s' := by
      have h := (hsq1.mul_const ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ))).add
        (hsq2'.mul_const (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))
      exact h.congr_deriv (by dsimp only [S'_fn]; ring)
    have hU_k (k : Fin M) : HasDerivAt (fun t => u (S_fn t ω x k))
        (S'_fn s' ω x k * deriv u (S_fn s' ω x k)) s' := by
      have h := (hu (S_fn s' ω x k)).hasDerivAt.comp s' (hS_k k)
      exact h.congr_deriv (mul_comm _ _)
    have h_ext (i : Fin (N + 1)) :
        HasDerivAt (fun t => ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 i * Real.sqrt r)
          (-(1 / (2 * Real.sqrt (1 - s'))) * (((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)) s' := by
      have h := ((hsq2'.const_mul ((x.1 i : ℤ) : ℝ)).mul_const (ω.2 i)).mul_const (Real.sqrt r)
      exact h.congr_deriv (by ring)
    have htot := (HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) => hU_k k).add
      (HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => h_ext i)
    exact htot.congr_deriv (by dsimp only [E'_s]; rw [← Finset.mul_sum]; ring)
  -- Bound on `|E'_s s' ω x|` for `s' ∈ U_nbhd`: `≤ b_ω ω + b_ξ x.2`!
  let b_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    |D₁| * (1 / (2 * Real.sqrt δ)) *
      (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
        Real.sqrt q * |ω.1.2 k|)) +
      (1 / (2 * Real.sqrt δ)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
  let b_ξ (ξ : Fin M → ℝ) : ℝ :=
    |D₁| * (1 / (2 * Real.sqrt δ)) * ∑ k : Fin M, Real.sqrt (1 - q) * |ξ k|
  have hb_ω0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : 0 ≤ b_ω ω := by
    dsimp only [b_ω]; positivity
  have hb_ξ0 (ξ : Fin M → ℝ) : 0 ≤ b_ξ ξ := by dsimp only [b_ξ]; positivity
  have hb_ξ_int : Integrable b_ξ γ_M := by
    refine (integrable_finsetSum _ fun k _ => ?_).const_mul _
    exact (integrable_comp_eval (μ := fun _ : Fin M => γ₁) (i := k)
      IsGaussian.integrable_id.abs).const_mul _
  have hb_ω_int : Integrable b_ω P := by
    refine Integrable.add ?_ ?_
    · refine (integrable_finsetSum _ fun k _ => Integrable.add ?_ ?_).const_mul _
      · refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
        have hi1 : Integrable (fun g : Fin M → Fin (N + 1) → ℝ => |g k i|) P_g := by
          have hc := integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i)
            IsGaussian.integrable_id.abs
          exact integrable_comp_eval (μ := fun _ : Fin M => Measure.pi fun _ => γ₁) (i := k) hc
        exact (hi1.comp_fst _).comp_fst _
      · have hk1 : Integrable (fun z : Fin M → ℝ => Real.sqrt q * |z k|) P_z :=
          (integrable_comp_eval (μ := fun _ : Fin M => γ₁) (i := k)
            IsGaussian.integrable_id.abs).const_mul _
        exact (hk1.comp_snd _).comp_fst _
    · refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
      have hi1 : Integrable (fun z' : Fin (N + 1) → ℝ => |z' i| * Real.sqrt r) P_z' :=
        (integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i)
          IsGaussian.integrable_id.abs).mul_const _
      exact hi1.comp_snd _
  have hE'_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) {s' : ℝ} (hs' : s' ∈ U_nbhd) :
      |E'_s s' ω x| ≤ b_ω ω + b_ξ x.2 := by
    obtain ⟨hδs, hδ1s, -, -⟩ := hs'_b hs'
    have hinv_s : 1 / (2 * Real.sqrt s') ≤ 1 / (2 * Real.sqrt δ) :=
      one_div_le_one_div_of_le (mul_pos zero_lt_two (Real.sqrt_pos.2 hδ))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδs) zero_le_two)
    have hinv_1s : 1 / (2 * Real.sqrt (1 - s')) ≤ 1 / (2 * Real.sqrt δ) :=
      one_div_le_one_div_of_le (mul_pos zero_lt_two (Real.sqrt_pos.2 hδ))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδ1s) zero_le_two)
    dsimp only [E'_s]
    refine (abs_sub _ _).trans ?_
    have hterm1 : |∑ k : Fin M, S'_fn s' ω x k * deriv u (S_fn s' ω x k)| ≤
        |D₁| * (1 / (2 * Real.sqrt δ)) *
          (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
            Real.sqrt q * |ω.1.2 k|)) + b_ξ x.2 := by
      have hk_bd (k : Fin M) : |S'_fn s' ω x k * deriv u (S_fn s' ω x k)| ≤
          |D₁| * (1 / (2 * Real.sqrt δ)) *
            (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
              Real.sqrt q * |ω.1.2 k|) + Real.sqrt (1 - q) * |x.2 k|) := by
        rw [abs_mul, mul_comm _ |deriv u (S_fn s' ω x k)|]
        have hd_le : |deriv u (S_fn s' ω x k)| ≤ |D₁| := (hD₁ _).trans (le_abs_self D₁)
        have hS'_le : |S'_fn s' ω x k| ≤ (1 / (2 * Real.sqrt δ)) *
            (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
              Real.sqrt q * |ω.1.2 k|) + Real.sqrt (1 - q) * |x.2 k|) := by
          dsimp only [S'_fn]
          refine (abs_sub _ _).trans ?_
          rw [abs_mul (1 / (2 * Real.sqrt s')),
            abs_mul (1 / (2 * Real.sqrt (1 - s'))),
            abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt s')),
            abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (1 - s'))),
            abs_mul ((Real.sqrt (N + 1 : ℕ))⁻¹),
            abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (N + 1 : ℕ))⁻¹)]
          have hsum_g : |∑ i : Fin (N + 1), ω.1.1 k i * ((x.1 i : ℤ) : ℝ)| ≤
              ∑ i : Fin (N + 1), |ω.1.1 k i| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_units_cast_eq_one, mul_one])
          have hθ : |Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k| ≤
              Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
            · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hp1 : (1 / (2 * Real.sqrt s')) *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * |∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)|) ≤
              (1 / (2 * Real.sqrt δ)) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, |ω.1.1 k i|) :=
            mul_le_mul hinv_s (mul_le_mul_of_nonneg_left hsum_g (by positivity))
              (by positivity) (by positivity)
          have hp2 : (1 / (2 * Real.sqrt (1 - s'))) *
              |Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k| ≤
              (1 / (2 * Real.sqrt δ)) *
                (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|) :=
            mul_le_mul hinv_1s hθ (abs_nonneg _) (by positivity)
          linarith
        calc |deriv u (S_fn s' ω x k)| * |S'_fn s' ω x k|
            ≤ |D₁| * ((1 / (2 * Real.sqrt δ)) *
                (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
                  Real.sqrt q * |ω.1.2 k|) + Real.sqrt (1 - q) * |x.2 k|)) :=
              mul_le_mul hd_le hS'_le (abs_nonneg _) hD₁0
          _ = _ := by ring
      refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hk_bd k)).trans_eq ?_
      dsimp only [b_ξ]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    have hterm2 : |(1 / (2 * Real.sqrt (1 - s'))) *
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r| ≤
        (1 / (2 * Real.sqrt δ)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (1 - s')))]
      refine mul_le_mul hinv_1s ?_ (abs_nonneg _) (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    dsimp only [b_ω]
    linarith
  -- Differentiate `s' ↦ log (∫ x, exp (E_s s' ω x) ∂μ_s)` at fixed `ω`!
  let Z_fn (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ x, Real.exp (E_s s' ω x) ∂μ_s
  have hEm (s' : ℝ) : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E_s s' p.1 p.2 := by
    refine (Finset.measurable_sum _ fun k _ => hum.comp (by fun_prop)).add ?_
    fun_prop
  have hE'm (s' : ℝ) : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E'_s s' p.1 p.2 := by
    refine (Finset.measurable_sum _ fun k _ => ?_).sub ?_
    · refine (by fun_prop : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => S'_fn s' p.1 p.2 k).mul ?_
      exact (measurable_deriv u).comp (by fun_prop)
    · fun_prop
  have hE_abs_bd {s' : ℝ} (hs' : s' ∈ U_nbhd)
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      |E_s s' ω x| ≤ M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
    obtain ⟨-, -, hs'0, _⟩ := hs'_b hs'
    have hsq1 : Real.sqrt (1 - s') ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    dsimp only [E_s]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ => hB _).trans_eq (by simp)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
        abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (1 - s') * |ω.2 i| * Real.sqrt r
          ≤ 1 * |ω.2 i| * Real.sqrt r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq1 (abs_nonneg _))
              (Real.sqrt_nonneg _)
        _ = |ω.2 i| * Real.sqrt r := by ring
  have hZ_deriv (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      {s' : ℝ} (hs' : s' ∈ U_nbhd) :
      HasDerivAt (fun t => Real.log (Z_fn t ω))
        (∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))) s' := by
    let C_E : ℝ := M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
    have hZ_d : HasDerivAt (fun t => Z_fn t ω)
        (∫ x, E'_s s' ω x * Real.exp (E_s s' ω x) ∂μ_s) s' := by
      have hm_ev : ∀ᶠ t in 𝓝 s', AEStronglyMeasurable (fun x => Real.exp (E_s t ω x)) μ_s :=
        Eventually.of_forall fun t =>
          (Real.measurable_exp.comp ((hEm t).comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
      have hi_s' : Integrable (fun x => Real.exp (E_s s' ω x)) μ_s :=
        integrable_exp_of_ae_le ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
          (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs' ω x))
      have hdm : AEStronglyMeasurable (fun x => E'_s s' ω x * Real.exp (E_s s' ω x)) μ_s :=
        (((hE'm s').comp (measurable_const.prodMk measurable_id)).mul
          (Real.measurable_exp.comp ((hEm s').comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
      let dom_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
        (b_ω ω + b_ξ x.2) * Real.exp C_E
      have hdom_x_i : Integrable dom_x μ_s :=
        ((integrable_const (b_ω ω)).add (hb_ξ_int.comp_snd _)).mul_const (Real.exp C_E)
      exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ_s)
        (F := fun t x => Real.exp (E_s t ω x))
        (F' := fun t x => E'_s t ω x * Real.exp (E_s t ω x))
        (s := U_nbhd) (bound := dom_x)
        (IsOpen.mem_nhds isOpen_Ioo hs') hm_ev hi_s' hdm
        (ae_of_all _ fun x t ht => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul (hE'_bd ω x ht)
            (Real.exp_le_exp.2 (le_of_abs_le (hE_abs_bd ht ω x)))
            (Real.exp_pos _).le (add_nonneg (hb_ω0 ω) (hb_ξ0 x.2)))
        hdom_x_i
        (ae_of_all _ fun x t ht => ((hd_E ω x ht).exp).congr_deriv (mul_comm _ _))).2
    have hi_s' : Integrable (fun x => Real.exp (E_s s' ω x)) μ_s :=
      integrable_exp_of_ae_le ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs' ω x))
    have hZ_pos : 0 < Z_fn s' ω := integral_exp_pos hi_s'
    exact (hZ_d.log hZ_pos.ne').congr_deriv
      (by rw [integral_tilted_eq_div, div_eq_mul_inv, mul_comm])
  -- Bound on `|∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))|` for `s' ∈ U_nbhd`:
  -- using `integral_tilted_le_exp_mul` or bounding `exp(E_s) / Z`?
  -- Wait! Notice `|E_s s' ω x - ∑_i x_i √(1-s') ω.2_i √r| ≤ M * B`!
  -- Even simpler: `Z_fn s' ω ≥ 2^(N+1) * exp(-C_E)`? No, `C_E` has `∑ |ω.2 i| √r`, and `exp(2 C_E) * ∫ b_ξ` is integrable over Gaussian `ω.2` (`Fernique` / `integrable_exp_mul_abs`)!
  -- Wait: EVEN SIMPLER! On `x = (τ, ξ)`, for fixed `τ`, the spin part `∑_i τ_i √(1-s') ω.2_i √r` cancels if we bound `∫_ξ |b_ξ ξ| exp(u_sum) / ∫_ξ exp(u_sum) ≤ exp(2 M B) * ∫_ξ b_ξ ξ`!
  have htilted_ξ_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      {s' : ℝ} (hs' : s' ∈ U_nbhd) :
      |∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))| ≤
        b_ω ω + Real.exp (2 * M * B) * ∫ ξ, b_ξ ξ ∂γ_M := by
    have hs'_mem := hs'
    obtain ⟨-, -, hs'0, _⟩ := hs'_b hs'
    let C_E : ℝ := M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
    have hi_s' : Integrable (fun x => Real.exp (E_s s' ω x)) μ_s :=
      integrable_exp_of_ae_le ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs' ω x))
    have hprob_t : IsProbabilityMeasure (μ_s.tilted (E_s s' ω)) :=
      isProbabilityMeasure_tilted hi_s'
    have hE'i : Integrable (E'_s s' ω) (μ_s.tilted (E_s s' ω)) := by
      have hb_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ω ω + b_ξ x.2)
          (μ_s.tilted (E_s s' ω)) :=
        integrable_tilted_of_ae_le
          ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
          (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs' ω x))
          ((integrable_const (b_ω ω)).add (hb_ξ_int.comp_snd _))
      exact hb_t.mono'
        ((hE'm s').comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hE'_bd ω x hs')
    have hb_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ω ω + b_ξ x.2)
        (μ_s.tilted (E_s s' ω)) :=
      integrable_tilted_of_ae_le
        ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs' ω x))
        ((integrable_const (b_ω ω)).add (hb_ξ_int.comp_snd _))
    have h1 : |∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))| ≤
        b_ω ω + ∫ x, b_ξ x.2 ∂(μ_s.tilted (E_s s' ω)) := by
      refine (abs_integral_le_integral_abs).trans ?_
      refine (integral_mono hE'i.abs hb_t fun x => hE'_bd ω x hs').trans_eq ?_
      have hb_ξ_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ξ x.2)
          (μ_s.tilted (E_s s' ω)) :=
        integrable_tilted_of_ae_le
          ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
          (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs' ω x))
          (hb_ξ_int.comp_snd _)
      rw [integral_add (integrable_const (b_ω ω)) hb_ξ_t, integral_const, probReal_univ, one_smul]
    refine h1.trans (add_le_add le_rfl ?_)
    -- Bound `∫ x, b_ξ x.2 ∂(μ_s.tilted (E_s s' ω)) ≤ exp(2 M B) * ∫ ξ, b_ξ ξ ∂γ_M`!
    let E_0_spin (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
    have hE0_m : Measurable E_0_spin := by dsimp only [E_0_spin]; fun_prop
    have hE0_b (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E_0_spin x ≤ ∑ i : Fin (N + 1), |Real.sqrt (1 - s') * ω.2 i * Real.sqrt r| :=
      Finset.sum_le_sum fun i _ => (le_abs_self _).trans (by
        rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul])
    have hi0 : Integrable (fun x => Real.exp (E_0_spin x)) μ_s :=
      integrable_exp_of_ae_le hE0_m.aemeasurable (ae_of_all _ hE0_b)
    have hdiff_E (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        |E_s s' ω x - E_0_spin x| ≤ M * B := by
      have heq_sub : E_s s' ω x - E_0_spin x = ∑ k : Fin M, u (S_fn s' ω x k) := by
        dsimp only [E_s, E_0_spin]; ring
      rw [heq_sub]
      exact (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ => hB _).trans_eq (by simp)
    have hdom_1 := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := Unit) (μ := μ_s)
      (E₀ := E_0_spin) (E₁ := E_s s' ω) hi0
      (((hEm s').comp (measurable_const.prodMk measurable_id)).sub hE0_m)
      (C := M * B) hdiff_E
      (Y := fun f : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ξ (f ()).2)
      (fun f => hb_ξ0 (f ()).2)
      (by
        have : IsProbabilityMeasure (μ_s.tilted E_0_spin) := isProbabilityMeasure_tilted hi0
        exact integrable_comp_eval (μ := fun _ : Unit => μ_s.tilted E_0_spin) (i := ())
          (integrable_tilted_of_ae_le hE0_m.aemeasurable (ae_of_all _ hE0_b)
            (hb_ξ_int.comp_snd _)))
    have h_unit (ν : Measure ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ))) [SigmaFinite ν] :
        (∫ f : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), b_ξ (f ()).2
          ∂(Measure.pi fun _ : Unit => ν)) =
        ∫ x, b_ξ x.2 ∂ν := by
      have hm : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ξ x.2 := by
        dsimp only [b_ξ]; fun_prop
      exact (measurePreserving_funUnique ν Unit).integral_comp_of_aestronglyMeasurable
        hm.aestronglyMeasurable
    have : SigmaFinite (μ_s.tilted (E_s s' ω)) := inferInstance
    have : IsProbabilityMeasure (μ_s.tilted E_0_spin) := isProbabilityMeasure_tilted hi0
    rw [h_unit (μ_s.tilted (E_s s' ω)), h_unit (μ_s.tilted E_0_spin)] at hdom_1
    simp only [Fintype.card_unique, Nat.cast_one, mul_one] at hdom_1
    -- Finally, under `μ_s.tilted E_0_spin`, `x.2` is independent of `x.1` and has law `γ_M`!
    have hE0_indep : ∫ x, b_ξ x.2 ∂(μ_s.tilted E_0_spin) = ∫ ξ, b_ξ ξ ∂γ_M := by
      rw [integral_tilted_eq_div]
      have hnum : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          b_ξ x.2 * Real.exp (E_0_spin x) ∂μ_s) =
          (∫ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)
            ∂Measure.count) * (∫ ξ, b_ξ ξ ∂γ_M) := by
        dsimp only [μ_s, E_0_spin]
        have hp := integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ))) (ν := γ_M)
          (fun τ => Real.exp (∑ i : Fin (N + 1),
            ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)) b_ξ
        exact (integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)).trans hp
      have hden : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Real.exp (E_0_spin x) ∂μ_s) =
          ∫ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)
            ∂Measure.count := by
        dsimp only [μ_s, E_0_spin]
        have hp := integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ))) (ν := γ_M)
          (fun τ => Real.exp (∑ i : Fin (N + 1),
            ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)) (fun _ => (1 : ℝ))
        simpa using hp
      have hden_pos : 0 < ∫ x, Real.exp (E_0_spin x) ∂μ_s := integral_exp_pos hi0
      rw [hden] at hden_pos
      rw [hnum, hden, mul_div_cancel_left₀ _ hden_pos.ne']
    rw [hE0_indep, ← mul_assoc] at hdom_1
    exact hdom_1
  -- Differentiate under `∫ ω ... ∂P`!
  have hlogZ_int (s' : ℝ) (hs' : s' ∈ U_nbhd) :
      Integrable (fun ω => Real.log (Z_fn s' ω)) P := by
    let E_eff (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (τ : Fin (N + 1) → ℤˣ) : ℝ :=
      (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r) +
        ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s' *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s') * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ))) ∂γ₁)
    have hZ_eq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        Real.log (Z_fn s' ω) = Real.log (∑ τ, Real.exp (E_eff ω τ)) := by
      dsimp only [Z_fn, E_eff, E_s, S_fn, γ₁]
      rw [integral_sum_exp_interpolating_eq hum hB_le s' q r ω]
    have hEm_τ (τ : Fin (N + 1) → ℤˣ) : Measurable fun ω => E_eff ω τ := by
      refine (Finset.measurable_sum _ fun i _ => by fun_prop).add ?_
      refine Finset.measurable_sum _ fun k _ => Real.measurable_log.comp ?_
      have hj : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) × ℝ =>
          Real.exp (u (Real.sqrt s' *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s') * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2))) :=
        Real.measurable_exp.comp (hum.comp (by fun_prop))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ₁)).measurable
    have hm_log : Measurable fun ω => Real.log (Z_fn s' ω) := by
      have heq := funext hZ_eq
      rw [heq]
      exact Real.measurable_log.comp (Finset.measurable_sum _ fun τ _ =>
        Real.measurable_exp.comp (hEm_τ τ))
    let dom_Z (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1) * Real.log 2 + M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
    have hdom_Z_i : Integrable dom_Z P := by
      refine ((integrable_const _).add (integrable_const _)).add (integrable_finsetSum _ fun i _ => ?_)
      exact ((integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i)
        IsGaussian.integrable_id.abs).mul_const _).comp_snd _
    refine hdom_Z_i.mono' hm_log.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, hZ_eq ω]
    obtain ⟨-, -, hs'0, _⟩ := hs'_b hs'
    have hsq1 : Real.sqrt (1 - s') ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hEb_τ (τ : Fin (N + 1) → ℤˣ) :
        |E_eff ω τ| ≤ M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
      dsimp only [E_eff]
      refine (abs_add_le _ _).trans ?_
      rw [add_comm ((M : ℝ) * B)]
      refine add_le_add ?_ ?_
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (1 - s') * |ω.2 i| * Real.sqrt r
            ≤ 1 * |ω.2 i| * Real.sqrt r :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq1 (abs_nonneg _))
                (Real.sqrt_nonneg _)
          _ = |ω.2 i| * Real.sqrt r := by ring
      · refine ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := B) fun k => ?_).trans_eq (by simp))
        exact abs_log_integral_exp_le_of_ae_abs_le (hum.comp (by fun_prop)).aemeasurable
          (ae_of_all _ fun _ => hB _)
    have hsub := abs_log_sum_exp_sub_log_card_le (E_eff ω) hEb_τ
    have hcard : Real.log (Fintype.card (Fin (N + 1) → ℤˣ) : ℝ) = ((N : ℝ) + 1) * Real.log 2 := by
      rw [card_spin_configurations, Fintype.card_fin]
      push_cast; rw [Real.log_pow]; push_cast; ring
    rw [hcard] at hsub
    have htri := abs_add_le (Real.log (∑ τ, Real.exp (E_eff ω τ)) - ((N : ℝ) + 1) * Real.log 2)
      (((N : ℝ) + 1) * Real.log 2)
    rw [sub_add_cancel, abs_of_nonneg (mul_nonneg (by positivity) (Real.log_nonneg one_le_two))]
      at htri
    dsimp only [dom_Z]; linarith
  have hF'_m : AEStronglyMeasurable (fun ω => ∫ x, E'_s s ω x ∂(μ_s.tilted (E_s s ω))) P := by
    let num_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ x, E'_s s ω x * Real.exp (E_s s ω x) ∂μ_s
    let den_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ x, Real.exp (E_s s ω x) ∂μ_s
    have hnum_m : Measurable num_fn :=
      (((hE'm s).mul (Real.measurable_exp.comp (hEm s))).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    have hden_m : Measurable den_fn :=
      ((Real.measurable_exp.comp (hEm s)).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    have heq : (fun ω => ∫ x, E'_s s ω x ∂(μ_s.tilted (E_s s ω))) =
        fun ω => num_fn ω / den_fn ω :=
      funext fun ω => integral_tilted_eq_div _ _
    rw [heq]
    exact (hnum_m.div hden_m).aestronglyMeasurable
  have hP_deriv : HasDerivAt (fun s' => ∫ ω, Real.log (Z_fn s' ω) ∂P)
      (∫ ω, ∫ x, E'_s s ω x ∂(μ_s.tilted (E_s s ω)) ∂P) s := by
    have hs_mem : s ∈ U_nbhd := ⟨by linarith, by linarith⟩
    have hm_ev : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (fun ω => Real.log (Z_fn t ω)) P :=
      Filter.eventually_of_mem hU_nhds fun t ht => (hlogZ_int t ht).aestronglyMeasurable
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
      (F := fun t ω => Real.log (Z_fn t ω))
      (F' := fun t ω => ∫ x, E'_s t ω x ∂(μ_s.tilted (E_s t ω)))
      (s := U_nbhd)
      (bound := fun ω => b_ω ω + Real.exp (2 * M * B) * ∫ ξ, b_ξ ξ ∂γ_M)
      hU_nhds hm_ev (hlogZ_int s hs_mem) hF'_m
      (ae_of_all _ fun ω t ht => by
        rw [Real.norm_eq_abs]; exact htilted_ξ_bd ω ht)
      (hb_ω_int.add (integrable_const _))
      (ae_of_all _ fun ω t ht => hZ_deriv ω ht)).2
  exact hP_deriv.const_mul (((N : ℝ) + 1)⁻¹)

/-- **Gaussian IBP on the external field `z'_i` (`r ≥ 0`, `s < 1`):**
`(N + 1)⁻¹ ν_s((2 √(1 - s))⁻¹ ∑ᵢ σᵢ z'ᵢ √r) = (r / 2)(1 - ν_s(R_{1,2}))`. -/
theorem integral_interpolating_external_field_ibp
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q : ℝ) {r : ℝ} (hr0 : 0 ≤ r) {s : ℝ} (hs1 : s < 1) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ((N : ℝ) + 1)⁻¹ *
        ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (1 / (2 * Real.sqrt (1 - s))) *
            (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s ω)) ∂P =
      (r / 2) * (1 - ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P) := by
  intro P_g P_z P_z' P μ_s E_s
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hB0 : 0 ≤ |B| := abs_nonneg B
  let c : ℝ := Real.sqrt (1 - s) * Real.sqrt r
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  -- Fix `gz = (g, z)` and apply `integral_mul_gibbs_ratio_eq_sum` over `z' ~ P_z'`!
  let D_gz (gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ∑ k : Fin M, u (Real.sqrt s *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, gz.1 k i * ((x.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * gz.2 k + Real.sqrt (1 - q) * x.2 k))
  let X_i (i : Fin (N + 1)) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    c * ((x.1 i : ℤ) : ℝ)
  have hDm (gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) : Measurable (D_gz gz) :=
    Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)
  have hDb (gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |D_gz gz x| ≤ M * |B| :=
    (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ => (hB _).trans (le_abs_self B)).trans_eq
      (by simp)
  have hXm (i : Fin (N + 1)) : Measurable (X_i i) := by dsimp only [X_i]; fun_prop
  have hXb (i : Fin (N + 1)) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |X_i i x| ≤ c := by
    dsimp only [X_i]; rw [abs_mul, abs_of_nonneg hc0, abs_units_cast_eq_one, mul_one]
  have hE_eq (gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) (z' : Fin (N + 1) → ℝ)
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      E_s (gz, z') x = D_gz gz x + ∑ i : Fin (N + 1), z' i * X_i i x := by
    dsimp only [E_s, D_gz, X_i, c]
    congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  have hZ_gauss : HasGaussianLaw (fun (z' : Fin (N + 1) → ℝ) (i : Fin (N + 1)) => z' i) P_z' := by
    let cId : Fin (N + 1) → Fin (N + 1) → ℝ := fun i j => if j = i then 1 else 0
    convert hasGaussianLaw_dotProduct_family cId using 1
    ext z' i
    simp [cId, dotProduct]
  have hZ_mean (i : Fin (N + 1)) : ∫ z' : Fin (N + 1) → ℝ, z' i ∂P_z' = 0 := by
    have heq := integral_dotProduct_pi_gaussianReal (Pi.single i (1 : ℝ))
    refine (integral_congr_ae (ae_of_all _ fun z' => ?_)).trans heq
    simp [dotProduct, Pi.single_apply]
  have hZ_cov (i l : Fin (N + 1)) :
      ∫ z' : Fin (N + 1) → ℝ, z' i * z' l ∂P_z' = if i = l then 1 else 0 := by
    let ei : Fin (N + 1) → ℝ := Pi.single i 1
    let el : Fin (N + 1) → ℝ := Pi.single l 1
    have hpt (z' : Fin (N + 1) → ℝ) : z' i * z' l = (ei ⬝ᵥ z') * (el ⬝ᵥ z') := by
      simp [ei, el, dotProduct, Pi.single_apply]
    simp_rw [hpt]
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    simp [ei, el, dotProduct, Pi.single_apply, eq_comm]
  -- Pointwise in `gz`, IBP for coordinate `i`!
  have hibp_gz (gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) (i : Fin (N + 1)) :
      ∫ z', z' i * (∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s (gz, z')))) ∂P_z' =
      c * ∫ z', (1 - (∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s (gz, z')))) ^ 2) ∂P_z' := by
    let R_gz (Y : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) → ℝ) (z' : Fin (N + 1) → ℝ) : ℝ :=
      (∫ x, Y x * Real.exp (D_gz gz x + ∑ k, z' k * X_i k x) ∂μ_s) /
        ∫ x, Real.exp (D_gz gz x + ∑ k, z' k * X_i k x) ∂μ_s
    have hR_tilted (Y : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) → ℝ) (z' : Fin (N + 1) → ℝ) :
        R_gz Y z' = ∫ x, Y x ∂(μ_s.tilted (E_s (gz, z'))) := by
      rw [integral_tilted_eq_div]
      simp_rw [hE_eq gz z']
      rfl
    have hstein := integral_mul_gibbs_ratio_eq_sum (μ := μ_s) (P := P_z')
      R_gz (fun _ _ => rfl) hZ_gauss hZ_mean i (hDm gz) hXm
      (Y := fun x => ((x.1 i : ℤ) : ℝ)) (by fun_prop) hc0 zero_le_one
      (hDb gz) hXb (fun _ => (abs_units_cast_eq_one _).le)
    simp only [hZ_cov i, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, hR_tilted] at hstein
    rw [hstein]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z' => ?_)
    dsimp only
    have hprob : IsProbabilityMeasure (μ_s.tilted (E_s (gz, z'))) := by
      have hmE : Measurable (E_s (gz, z')) := by
        rw [show E_s (gz, z') = fun x => D_gz gz x + ∑ k, z' k * X_i k x from funext (hE_eq gz z')]
        exact (hDm gz).add (Finset.measurable_sum _ fun k _ => (hXm k).const_mul (z' k))
      exact isProbabilityMeasure_tilted_of_ae_le hmE.aemeasurable
        (ae_of_all _ fun x => by
          rw [hE_eq gz z']
          exact le_of_abs_le (abs_add_sum_mul_le _ _ _ (hDb gz x) (fun k => hXb k x)))
    have hsq_x : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((x.1 i : ℤ) : ℝ) * X_i i x ∂(μ_s.tilted (E_s (gz, z')))) = c := by
      have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
          ((x.1 i : ℤ) : ℝ) * X_i i x = c := by
        dsimp only [X_i]
        have h1 : ((x.1 i : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
        linear_combination c * h1
      simp_rw [hpt_x]
      simp
    have hlin_x : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        X_i i x ∂(μ_s.tilted (E_s (gz, z')))) =
        c * ∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s (gz, z'))) := by
      dsimp only [X_i]; exact integral_const_mul c _
    rw [hsq_x, hlin_x]
    ring
  -- Also express `(∫ x, σ_i ∂ν)²` as two-replica average `∫ σ : Fin 2 → ..., σ_0 i * σ_1 i`!
  have htwo_rep (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (i : Fin (N + 1)) :
      (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))) ^ 2 =
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
    let ν_ω := μ_s.tilted (E_s ω)
    have hEm_ω : Measurable (E_s ω) := by
      refine (Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)).add ?_
      fun_prop
    have hEb_ω (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E_s ω x ≤ M * B + ∑ j : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 j * Real.sqrt r| :=
      add_le_add ((Finset.sum_le_sum fun _ _ => hB_le _).trans_eq (by simp))
        (Finset.sum_le_sum fun j _ => (le_abs_self _).trans (by
          rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]))
    have : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le hEm_ω.aemeasurable (ae_of_all _ hEb_ω)
    let sp_i : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) → ℝ := fun x => ((x.1 i : ℤ) : ℝ)
    have hprod := integral_pi_fin_two_mul_fun ν_ω sp_i sp_i
    rw [sq]
    exact hprod.symm
  -- Now pull the sum over `i : Fin (N + 1)` outside `∫ ω` and `∫ x` on both sides!
  have hEm_joint : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E_s p.1 p.2 := by
    have h1_sum : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
        ∑ k : Fin M, u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, p.1.1.1 k j * ((p.2.1 j : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2.2 k)) := by
      refine Finset.measurable_sum _ fun k _ => hu.comp ?_
      have hg_sum : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
          ∑ j : Fin (N + 1), p.1.1.1 k j * ((p.2.1 j : ℤ) : ℝ) := by
        refine Finset.measurable_sum _ fun j _ => ?_
        have hgj : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.1.1 k j :=
          (measurable_pi_apply j).comp ((measurable_pi_apply k).comp
            (measurable_fst.comp (measurable_fst.comp measurable_fst)))
        have hσj : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 j : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply j).comp
            (measurable_fst.comp measurable_snd))
        exact hgj.mul hσj
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
    have h2_sum : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
        ∑ j : Fin (N + 1), ((p.2.1 j : ℤ) : ℝ) * Real.sqrt (1 - s) * p.1.2 j * Real.sqrt r := by
      refine Finset.measurable_sum _ fun j _ => ?_
      have hσj : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 j : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply j).comp
          (measurable_fst.comp measurable_snd))
      have hz'j : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.2 j :=
        (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
      exact ((hσj.mul_const _).mul hz'j).mul_const _
    exact h1_sum.add h2_sum
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s ω)) := by
    have hEm_ω : Measurable (E_s ω) := Measurable.of_uncurry_left hEm_joint
    have hEb_ω (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E_s ω x ≤ M * B + ∑ j : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 j * Real.sqrt r| :=
      add_le_add ((Finset.sum_le_sum fun _ _ => hB_le _).trans_eq (by simp))
        (Finset.sum_le_sum fun j _ => (le_abs_self _).trans (by
          rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]))
    exact isProbabilityMeasure_tilted_of_ae_le hEm_ω.aemeasurable (ae_of_all _ hEb_ω)
  let L_i (i : Fin (N + 1))
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ω.2 i * ∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))
  have hLi_int (i : Fin (N + 1)) : Integrable (L_i i) P := by
    let num_i (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ x, ((x.1 i : ℤ) : ℝ) * Real.exp (E_s ω x) ∂μ_s
    let den_i (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ x, Real.exp (E_s ω x) ∂μ_s
    have hspin_p : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd))
    have hnum_m : Measurable num_i :=
      ((hspin_p.mul (Real.measurable_exp.comp hEm_joint)).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    have hden_m : Measurable den_i :=
      ((Real.measurable_exp.comp hEm_joint).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    have hLm : Measurable (L_i i) := by
      have heq : L_i i = fun ω => ω.2 i * (num_i ω / den_i ω) :=
        funext fun ω => by dsimp only [L_i]; rw [integral_tilted_eq_div]
      rw [heq]
      exact (by fun_prop : Measurable fun ω :
        ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) => ω.2 i).mul
        (hnum_m.div hden_m)
    have hdom_i : Integrable
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) => |ω.2 i|) P :=
      (integrable_comp_eval (μ := fun _ : Fin (N + 1) => gaussianReal 0 1) (i := i)
        IsGaussian.integrable_id.abs).comp_snd _
    refine hdom_i.mono' hLm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := hprob_ω ω
    rw [Real.norm_eq_abs, abs_mul]
    have hb1 : |∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))| ≤ 1 :=
      abs_integral_le_of_forall_abs_le _ fun _ => (abs_units_cast_eq_one _).le
    calc |ω.2 i| * |∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))|
        ≤ |ω.2 i| * 1 := mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
      _ = |ω.2 i| := mul_one _
  let Q_i (i : Fin (N + 1))
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))
  have hQi_int (i : Fin (N + 1)) : Integrable (Q_i i) P := by
    let G_i (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
    have hGm : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => G_i p.1 p.2 := by
      have h0 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
          (((σ 0).1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 0)))
      have h1 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
          (((σ 1).1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 1)))
      exact (h0.mul h1).comp measurable_snd
    have hQm := measurable_integral_pi_tilted (μ := μ_s) hEm_joint hGm
    exact Integrable.of_bound hQm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      have := hprob_ω ω
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun _ => by
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one])
  have hibp_full (i : Fin (N + 1)) :
      ∫ ω, L_i i ω ∂P = c * (1 - ∫ ω, Q_i i ω ∂P) := by
    have hR_int : Integrable (fun ω => 1 - Q_i i ω) P := (integrable_const 1).sub (hQi_int i)
    dsimp only [P]
    rw [integral_prod _ (hLi_int i)]
    have heq_fub : ∀ᵐ gz ∂(P_g.prod P_z),
        ∫ z', L_i i (gz, z') ∂P_z' = c * ∫ z', (1 - Q_i i (gz, z')) ∂P_z' :=
      ae_of_all _ fun gz => by
        dsimp only [L_i]
        rw [hibp_gz gz i]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun z' => ?_)
        dsimp only [Q_i]
        rw [htwo_rep (gz, z') i]
    rw [integral_congr_ae heq_fub, integral_const_mul,
      ← integral_prod (fun ω => 1 - Q_i i ω) hR_int,
      integral_sub (integrable_const 1) (hQi_int i), integral_const, probReal_univ, one_smul]
  -- Rewrite LHS in terms of `∑ i, ∫ ω, L_i i ω ∂P`!
  have hlhs_rw :
      (∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω)) ∂P) =
      (Real.sqrt r / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), ∫ ω, L_i i ω ∂P := by
    have hpt_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (1 / (2 * Real.sqrt (1 - s))) *
            (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s ω))) =
        (Real.sqrt r / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), L_i i ω := by
      have := hprob_ω ω
      rw [integral_const_mul]
      have h_in (i : Fin (N + 1)) :
          Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
            ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r) (μ_s.tilted (E_s ω)) :=
        Integrable.of_bound (by fun_prop) (|ω.2 i| * Real.sqrt r) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
            abs_of_nonneg (Real.sqrt_nonneg _)])
      rw [integral_finsetSum _ fun i _ => h_in i]
      have h_term (i : Fin (N + 1)) :
          (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r ∂(μ_s.tilted (E_s ω))) =
          Real.sqrt r * L_i i ω := by
        have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
            ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r =
            (Real.sqrt r * ω.2 i) * ((x.1 i : ℤ) : ℝ) := by ring
        simp_rw [hpt_x]
        rw [integral_const_mul]
        dsimp only [L_i]; ring
      simp_rw [h_term, ← Finset.mul_sum]
      ring
    simp_rw [hpt_ω]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hLi_int i]
  have hrhs_rw :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P) =
      ((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), ∫ ω, Q_i i ω ∂P := by
    have hpt_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) =
        ((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), Q_i i ω := by
      have := hprob_ω ω
      have hin_i (i : Fin (N + 1)) :
          Integrable (fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
            (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
            (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
        have hm : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
            (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) :=
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 0)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 1))))
        exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one])
      rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ => hin_i i]
    simp_rw [hpt_ω]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hQi_int i]
  rw [hlhs_rw, hrhs_rw]
  simp_rw [hibp_full, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp only [c]
  have h1s_ne : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hs1)).ne'
  have hsr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0
  have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  generalize (∑ x : Fin (N + 1), ∫ ω, Q_i x ω ∂P) = S_Q
  field_simp
  linear_combination ((N : ℝ) + 1 - S_Q) * hsr

/-- **Constraint-swap invariance for the `s`-interpolating disorder and Gibbs law.** -/
def interpConstraintStateSwap {L M : ℕ} (k₁ k₂ : Fin M) :
    ((Fin L → ℤˣ) × (Fin M → ℝ)) ≃ᵐ ((Fin L → ℤˣ) × (Fin M → ℝ)) where
  toFun x := (x.1, fun k => x.2 (Equiv.swap k₁ k₂ k))
  invFun x := (x.1, fun k => x.2 (Equiv.swap k₁ k₂ k))
  left_inv x := Prod.ext rfl (funext fun k => by simp)
  right_inv x := Prod.ext rfl (funext fun k => by simp)
  measurable_toFun := measurable_fst.prodMk (measurable_pi_iff.2 fun k =>
    (measurable_pi_apply (Equiv.swap k₁ k₂ k)).comp measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_pi_iff.2 fun k =>
    (measurable_pi_apply (Equiv.swap k₁ k₂ k)).comp measurable_snd)

def interpConstraintDisorderSwap {L M : ℕ} (k₁ k₂ : Fin M)
    (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) :
    ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ) :=
  ((fun k => ω.1.1 (Equiv.swap k₁ k₂ k), fun k => ω.1.2 (Equiv.swap k₁ k₂ k)), ω.2)

lemma measurePreserving_interpConstraintDisorderSwap {L M : ℕ} (k₁ k₂ : Fin M) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin L => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin L => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    MeasurePreserving (interpConstraintDisorderSwap (L := L) k₁ k₂) P P := by
  intro P_g P_z P_z' P
  have hg : MeasurePreserving
      (fun g : Fin M → Fin L → ℝ => fun k => g (Equiv.swap k₁ k₂ k)) P_g P_g :=
    measurePreserving_pi_comp_injective _ (Equiv.injective _)
  have hz : MeasurePreserving
      (fun z : Fin M → ℝ => fun k => z (Equiv.swap k₁ k₂ k)) P_z P_z :=
    measurePreserving_pi_comp_injective _ (Equiv.injective _)
  exact (hg.prod hz).prod (MeasurePreserving.id P_z')

lemma measurePreserving_interpConstraintStateSwap {L M : ℕ} (k₁ k₂ : Fin M) :
    let μ_s := (Measure.count : Measure (Fin L → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    MeasurePreserving ⇑(interpConstraintStateSwap (L := L) k₁ k₂) μ_s μ_s := by
  intro μ_s
  have h : MeasurePreserving (fun ξ : Fin M → ℝ => fun k => ξ (Equiv.swap k₁ k₂ k))
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
      (Measure.pi fun _ : Fin M => gaussianReal 0 1) :=
    measurePreserving_pi_comp_injective _ (Equiv.injective _)
  exact (MeasurePreserving.id _).prod h

@[simp]
lemma interpConstraintStateSwap_apply {L M : ℕ} (k₁ k₂ : Fin M)
    (x : (Fin L → ℤˣ) × (Fin M → ℝ)) :
    interpConstraintStateSwap k₁ k₂ x = (x.1, fun k => x.2 (Equiv.swap k₁ k₂ k)) := rfl

@[simp]
lemma interpConstraintStateSwap_symm_apply {L M : ℕ} (k₁ k₂ : Fin M)
    (x : (Fin L → ℤˣ) × (Fin M → ℝ)) :
    (interpConstraintStateSwap k₁ k₂).symm x = (x.1, fun k => x.2 (Equiv.swap k₁ k₂ k)) := rfl

private lemma measurable_interpField_joint {L M : ℕ} (s q : ℝ) (k : Fin M) :
    Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) =>
      Real.sqrt s * ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2.2 k) := by
  have hg_sum : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => ∑ i : Fin L, p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hgi : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) => p.1.1.1 k i :=
      (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst)))
    have hσi : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd))
    exact hgi.mul hσi
  have hzk : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => p.1.1.2 k :=
    (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hξk : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => p.2.2 k :=
    (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
  exact ((hg_sum.const_mul _).const_mul _).add
    (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)

private lemma measurable_interpFieldDeriv_joint {L M : ℕ} (s q : ℝ) (k : Fin M) :
    Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) =>
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2.2 k) := by
  have hg_sum : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => ∑ i : Fin L, p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hgi : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) => p.1.1.1 k i :=
      (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst)))
    have hσi : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd))
    exact hgi.mul hσi
  have hzk : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => p.1.1.2 k :=
    (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hξk : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => p.2.2 k :=
    (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
  exact ((hg_sum.const_mul _).const_mul _).sub
    (((hzk.const_mul _).add (hξk.const_mul _)).const_mul _)

private lemma measurable_interpEnergy_joint {L M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (s q r : ℝ) :
    Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) =>
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2.2 k))) +
      ∑ i : Fin L, ((p.2.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * p.1.2 i * Real.sqrt r := by
  refine (Finset.measurable_sum _ fun k _ => hu.comp (measurable_interpField_joint s q k)).add ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  have hσi : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
    measurable_units_cast.comp ((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_snd))
  have hz'i : Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
      ((Fin L → ℤˣ) × (Fin M → ℝ)) => p.1.2 i :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  exact ((hσi.mul_const _).mul hz'i).mul_const _

private lemma interpEnergy_le {L M : ℕ} {u : ℝ → ℝ} {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ)
    (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ))
    (x : (Fin L → ℤˣ) × (Fin M → ℝ)) :
    (∑ k : Fin M, u (Real.sqrt s *
        ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
    (∑ i : Fin L, ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) ≤
    M * B + ∑ i : Fin L, |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
  refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
    (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]

/-- **Splitting the `(M + 1)`-constraint `s`-interpolating disorder into the `M`-constraint
disorder and the last constraint's shared Gaussian vector `(g_M, z_M) : (Fin L ⊕ Unit) → ℝ`.** -/
private lemma measurePreserving_interpConstraintDisorder_lastSplit (L M : ℕ) :
    let γ := gaussianReal (0 : ℝ) 1
    let P_M := ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin L => γ).prod
      (Measure.pi fun _ : Fin M => γ)).prod (Measure.pi fun _ : Fin L => γ)
    let P_M1 := ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin L => γ).prod
      (Measure.pi fun _ : Fin (M + 1) => γ)).prod (Measure.pi fun _ : Fin L => γ)
    MeasurePreserving
      (fun ω : ((Fin (M + 1) → Fin L → ℝ) × (Fin (M + 1) → ℝ)) × (Fin L → ℝ) =>
        (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
          (Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) :
            (Fin L ⊕ Unit) → ℝ)))
      P_M1 (P_M.prod (Measure.pi fun _ : Fin L ⊕ Unit => γ)) := by
  intro γ P_M P_M1
  let G₀ := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin L => γ
  let gM := Measure.pi fun _ : Fin L => γ
  let Z₀ := Measure.pi fun _ : Fin M => γ
  let Zp := Measure.pi fun _ : Fin L => γ
  have hg := measurePreserving_finSuccProd gM M
  have hz := measurePreserving_finSuccProd γ M
  have hunit := (measurePreserving_funUnique γ Unit).symm
  have hsum := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin L ⊕ Unit => ℝ)
    (fun _ => γ)).comp ((MeasurePreserving.id gM).prod hunit)
  have step1 : MeasurePreserving
      (Prod.map (Prod.map (MeasurableEquiv.finSuccProd (Fin L → ℝ) M)
        (MeasurableEquiv.finSuccProd ℝ M)) id)
      P_M1 (((G₀.prod gM).prod (Z₀.prod γ)).prod Zp) :=
    (hg.prod hz).prod (MeasurePreserving.id Zp)
  have step2 := (measurePreserving_prodProdProdComm G₀ gM Z₀ γ).prod (MeasurePreserving.id Zp)
  have step3 := measurePreserving_prodAssoc (G₀.prod Z₀) (gM.prod γ) Zp
  have step4 := (MeasurePreserving.id (G₀.prod Z₀)).prod
    (Measure.measurePreserving_swap (μ := gM.prod γ) (ν := Zp))
  have step5 := (measurePreserving_prodAssoc (G₀.prod Z₀) Zp (gM.prod γ)).symm
  have step6 := (MeasurePreserving.id P_M).prod hsum
  have full := step6.comp (step5.comp (step4.comp (step3.comp (step2.comp step1))))
  convert full using 1
  ext ω : 1
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.prodAssoc, Fin.init_def]
  · ext idx
    rcases idx with i | _ <;>
      simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]

/-- State split for `(M + 1)` constraints in the `s`-interpolating system. -/
private def interpStateLastSplit (L M : ℕ) :
    ((Fin L → ℤˣ) × (Fin (M + 1) → ℝ)) ≃ᵐ (((Fin L → ℤˣ) × (Fin M → ℝ)) × ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.finSuccProd ℝ M)).trans
    MeasurableEquiv.prodAssoc.symm

private lemma interpStateLastSplit_apply {L M : ℕ} (x : (Fin L → ℤˣ) × (Fin (M + 1) → ℝ)) :
    interpStateLastSplit L M x = ((x.1, Fin.init x.2), x.2 (Fin.last M)) := by
  simp [interpStateLastSplit, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_prodCongr,
    MeasurableEquiv.coe_refl, Fin.init_def]

private lemma measurePreserving_interpStateLastSplit (L M : ℕ) :
    MeasurePreserving ⇑(interpStateLastSplit L M)
      ((Measure.count : Measure (Fin L → ℤˣ)).prod
        (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1))
      (((Measure.count : Measure (Fin L → ℤˣ)).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 1)) :=
  (measurePreserving_prodAssoc _ _ _).symm.comp
    ((MeasurePreserving.id _).prod (measurePreserving_finSuccProd _ M))

/-- **Gaussian IBP on a single `s`-interpolating constraint field (Eq. (2.82)):**
for `s ∈ (0, 1)`, `q ∈ [0, 1]`, and any constraint `k : Fin M`,
`ν_s(S'_{k, s} u'(S_{k, s})) = - (1 / 2) ν_s((R_{1,2} - q) u'(S^1_{k, s}) u'(S^2_{k, s}))`. -/
theorem integral_interpolating_field_deriv_ibp
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (k : Fin M) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k' : Fin M) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let S'_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k' : Fin M) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (S_fn ω x k')) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω)) ∂P =
      -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P := by
  rcases M with _ | M
  · exact Fin.elim0 k
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s
  -- Step 1: Reduce `k` to `Fin.last M` by `interpConstraintDisorderSwap k (Fin.last M)`!
  -- First prove the identity at `Fin.last M`, then transport via `k ↔ Fin.last M`!
  have hEm_joint {M' : ℕ} : Measurable fun p :
      (((Fin M' → Fin (N + 1) → ℝ) × (Fin M' → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M' → ℝ)) =>
      (∑ k' : Fin M', u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 k' i * ((p.2.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k' + Real.sqrt (1 - q) * p.2.2 k'))) +
      ∑ i : Fin (N + 1), ((p.2.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * p.1.2 i * Real.sqrt r :=
    measurable_interpEnergy_joint (L := N + 1) (M := M') hu.measurable s q r
  -- Swap invariance for LHS and RHS!
  have htilted_swap (k₁ k₂ : Fin (M + 1))
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      μ_s.tilted (E_s (interpConstraintDisorderSwap k₁ k₂ ω)) =
      (μ_s.tilted (E_s ω)).map (interpConstraintStateSwap k₁ k₂) := by
    rw [map_tilted_measurableEquiv (interpConstraintStateSwap k₁ k₂)
      (measurePreserving_interpConstraintStateSwap k₁ k₂)
      (Measurable.of_uncurry_left hEm_joint)]
    congr 1; funext x
    dsimp only [Function.comp_apply]
    rw [interpConstraintStateSwap_symm_apply]
    dsimp only [E_s, S_fn, interpConstraintDisorderSwap]
    congr 1
    rw [← Equiv.sum_comp (Equiv.swap k₁ k₂)]
    refine Finset.sum_congr rfl fun k' _ => ?_
    simp
  have hlhs_swap :
      ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω)) ∂P =
      ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)) ∂(μ_s.tilted (E_s ω)) ∂P := by
    let Φ_l (k' : Fin (M + 1))
        (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ x, S'_fn ω x k' * deriv u (S_fn ω x k') ∂(μ_s.tilted (E_s ω))
    have hΦ_m (k' : Fin (M + 1)) : Measurable (Φ_l k') := by
      have hS_m := measurable_interpField_joint (L := N + 1) (M := M + 1) s q k'
      have hS'_m := measurable_interpFieldDeriv_joint (L := N + 1) (M := M + 1) s q k'
      let num_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
        ∫ x, (S'_fn ω x k' * deriv u (S_fn ω x k')) * Real.exp (E_s ω x) ∂μ_s
      let den_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
        ∫ x, Real.exp (E_s ω x) ∂μ_s
      have hnum_m : Measurable num_fn :=
        (((hS'_m.mul ((measurable_deriv u).comp hS_m)).mul
          (Real.measurable_exp.comp hEm_joint)).stronglyMeasurable.integral_prod_right'
          (ν := μ_s)).measurable
      have hden_m : Measurable den_fn :=
        ((Real.measurable_exp.comp hEm_joint).stronglyMeasurable.integral_prod_right'
          (ν := μ_s)).measurable
      have heq : Φ_l k' = fun ω => num_fn ω / den_fn ω :=
        funext fun _ => integral_tilted_eq_div _ _
      rw [heq]
      exact hnum_m.div hden_m
    have hpt_sw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        Φ_l (Fin.last M) (interpConstraintDisorderSwap k (Fin.last M) ω) = Φ_l k ω := by
      dsimp only [Φ_l]
      rw [htilted_swap k (Fin.last M) ω, integral_map_equiv]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only [Function.comp_apply, S_fn, S'_fn, interpConstraintDisorderSwap]
      simp [interpConstraintStateSwap_apply]
    have hmp := measurePreserving_interpConstraintDisorderSwap (L := N + 1) k (Fin.last M)
    have heq := hmp.integral_comp_of_aestronglyMeasurable (hΦ_m (Fin.last M)).aestronglyMeasurable
    have heq' : ∫ ω, Φ_l k ω ∂P = ∫ ω, Φ_l (Fin.last M) ω ∂P := by
      refine (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans ?_
      exact heq
    exact heq'
  have hrhs_swap :
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P := by
    let Ψ_r (k' : Fin (M + 1))
        (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) k') * deriv u (S_fn ω (σ 1) k')
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))
    have hΨ_m (k' : Fin (M + 1)) : Measurable (Ψ_r k') := by
      have hS_l (l : Fin 2) : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => S_fn p.1 (p.2 l) k' := by
        have hp_l : Measurable fun p :
            (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => (p.1, p.2 l) :=
          measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd)
        have hcomp := (measurable_interpField_joint (L := N + 1) (M := M + 1) s q k').comp hp_l
        exact hcomp
      have hR_m : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          (((N : ℝ) + 1)⁻¹ * ∑ i, ((((p.2 0).1 i : ℤ) : ℝ) * (((p.2 1).1 i : ℤ) : ℝ))) - q := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const _
        have h0 : Measurable fun p :
            (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => (((p.2 0).1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)))
        have h1 : Measurable fun p :
            (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => (((p.2 1).1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd)))
        exact h0.mul h1
      have hμ_fin : IsFiniteMeasure μ_s := inferInstance
      exact @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ E_s hEm_joint _
        ((hR_m.mul ((measurable_deriv u).comp (hS_l 0))).mul
          ((measurable_deriv u).comp (hS_l 1)))
    have hpt_sw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        Ψ_r (Fin.last M) (interpConstraintDisorderSwap k (Fin.last M) ω) = Ψ_r k ω := by
      have hprob : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
        isProbabilityMeasure_tilted_of_ae_le
          (Measurable.of_uncurry_left hEm_joint).aemeasurable
          (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
      dsimp only [Ψ_r]
      rw [htilted_swap k (Fin.last M) ω,
        integral_pi_map_equiv (μ_s.tilted (E_s ω)) (interpConstraintStateSwap k (Fin.last M))]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only [S_fn, interpConstraintDisorderSwap]
      simp [interpConstraintStateSwap_apply]
    have hmp := measurePreserving_interpConstraintDisorderSwap (L := N + 1) k (Fin.last M)
    have heq := hmp.integral_comp_of_aestronglyMeasurable (hΨ_m (Fin.last M)).aestronglyMeasurable
    have heq' : ∫ ω, Ψ_r k ω ∂P = ∫ ω, Ψ_r (Fin.last M) ω ∂P := by
      refine (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans ?_
      exact heq
    exact heq'
  rw [hlhs_swap, hrhs_swap]
  -- Step 2: Now prove the identity at `Fin.last M` by splitting into `P_0 × γ_sh` and applying
  -- `stein_tilted_replica_ratio` (`R = Unit`, `ψ = deriv u`)!
  let P₀ := (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
    (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
  let μ₀_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)
  let E₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (∑ k' : Fin M, u (Real.sqrt s *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k' i * ((x₀.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k' + Real.sqrt (1 - q) * x₀.2 k'))) +
    ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r
  let μ₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
    μ₀_base.tilted (E₀ ω₀)
  let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
  let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
  let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
  let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q)
  let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - s) * Real.sqrt (1 - q)
  let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
    fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)
  have hcov_sh (τ₁ τ₂ : Fin (N + 1) → ℤˣ) :
      W_sh τ₁ ⬝ᵥ α_sh τ₂ =
        (1 / 2) * ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) - q) := by
    dsimp only [W_sh, α_sh]
    rw [sumElim_dotProduct_sumElim]
    have hs_ne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs.1).ne'
    have h1s_ne : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hs.2)).ne'
    have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hsq_L : (Real.sqrt (N + 1 : ℕ))⁻¹ * (Real.sqrt (N + 1 : ℕ))⁻¹ = ((N : ℝ) + 1)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    have hsq_q : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.1
    have h1 : (fun i : Fin (N + 1) =>
        (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₁ i : ℤ) : ℝ)) ⬝ᵥ
      (fun i : Fin (N + 1) =>
        Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₂ i : ℤ) : ℝ)) =
      (1 / 2) * (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) := by
      simp only [dotProduct]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc : (1 / (2 * Real.sqrt s)) * Real.sqrt s = 1 / 2 := by field_simp
      calc (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₁ i : ℤ) : ℝ) *
            (Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₂ i : ℤ) : ℝ))
          = ((1 / (2 * Real.sqrt s)) * Real.sqrt s) *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * (Real.sqrt (N + 1 : ℕ))⁻¹) *
              (((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) := by ring
        _ = (1 / 2) * (((N : ℝ) + 1)⁻¹ * (((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ))) := by
            rw [hc, hsq_L]; ring
    have h2 : (fun _ : Unit => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q) ⬝ᵥ
        (fun _ : Unit => Real.sqrt (1 - s) * Real.sqrt q) = -(1 / 2) * q := by
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      have hc : (1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - s) = 1 / 2 := by field_simp
      calc -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q * (Real.sqrt (1 - s) * Real.sqrt q)
          = -((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - s)) * (Real.sqrt q * Real.sqrt q) := by
            ring
        _ = -(1 / 2) * q := by rw [hc, hsq_q]
    rw [h1, h2]; ring
  have hcov_diag (τ : Fin (N + 1) → ℤˣ) :
      W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0 := by
    rw [hcov_sh τ τ]
    have hself : (((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) = 1 := by
      have h1 (i : Fin (N + 1)) : ((τ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ) = 1 := by
        rw [← sq]; exact units_cast_sq _
      simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
      push_cast; exact inv_mul_cancel₀ hL
    have haux_dot : W_aux τ ⬝ᵥ α_aux τ = -(1 / 2) * (1 - q) := by
      dsimp only [W_aux, α_aux]
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      have h1s_ne : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hs.2)).ne'
      have hc : (1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - s) = 1 / 2 := by field_simp
      have hsq_1q : Real.sqrt (1 - q) * Real.sqrt (1 - q) = 1 - q :=
        Real.mul_self_sqrt (sub_nonneg.2 hq.2)
      calc -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q) *
            (Real.sqrt (1 - s) * Real.sqrt (1 - q))
          = -((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - s)) *
              (Real.sqrt (1 - q) * Real.sqrt (1 - q)) := by ring
        _ = -(1 / 2) * (1 - q) := by rw [hc, hsq_1q]
    rw [hself, haux_dot]; ring
  -- Pointwise Stein identity at fixed `ω₀`!
  have hstein_ω₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      ∫ w, ∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
          1 * (W_sh (σ ()).1.1 ⬝ᵥ w + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
            (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ w + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
          ∂(Measure.pi fun _ : Unit => ((μ₀ ω₀).prod γ_aux).tilted
            (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2))) ∂γ_sh =
      -(1 / 2) * ∫ w, ∫ σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i,
              (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
            deriv u (α_sh (σ (some ())).1.1 ⬝ᵥ w + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
            deriv u (α_sh (σ none).1.1 ⬝ᵥ w + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
          ∂(Measure.pi fun _ : Option Unit => ((μ₀ ω₀).prod γ_aux).tilted
            (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2))) ∂γ_sh := by
    have hμ₀_prob : IsProbabilityMeasure (μ₀ ω₀) :=
      isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω₀))
    have hψ_deriv (x : ℝ) :
        HasDerivAt (fun t => deriv u t * Real.exp (u t))
          ((deriv (deriv u) x + deriv u x * deriv u x) * Real.exp (u x)) x := by
      have h1 : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        (hu.differentiable_deriv x).hasDerivAt
      have h2 : HasDerivAt (fun t => Real.exp (u t)) (Real.exp (u x) * deriv u x) x :=
        (hu.differentiable x).hasDerivAt.exp
      exact (h1.mul h2).congr_deriv (by ring)
    have hst := stein_tilted_replica_ratio (R := Unit) (μ₀ := μ₀ ω₀)
      (π := Prod.fst) measurable_fst α_sh W_sh α_aux W_aux
      hu.differentiable hu.abs_le hu.abs_deriv_le
      (fun _ => deriv u)
      (fun _ x => (hψ_deriv x).differentiableAt)
      (M₀ := fun _ => |D₁|) (M' := fun _ => (|D₂| + |D₁| ^ 2) * Real.exp |B|)
      (fun _ x => (hu.abs_deriv_le x).trans (le_abs_self D₁))
      (fun _ x => by
        rw [(hψ_deriv x).deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
        refine mul_le_mul ?_ (Real.exp_le_exp.2 ((hu.le x).trans (le_abs_self B)))
          (Real.exp_pos _).le (by positivity)
        refine (abs_add_le _ _).trans (add_le_add
          ((hu.abs_deriv₂_le x).trans (le_abs_self D₂)) ?_)
        rw [abs_mul, sq]
        exact mul_le_mul ((hu.abs_deriv_le x).trans (le_abs_self D₁))
          ((hu.abs_deriv_le x).trans (le_abs_self D₁)) (abs_nonneg _) (abs_nonneg _))
      (fun _ x => deriv (deriv u) x + deriv u x * deriv u x)
      (fun _ x => (hψ_deriv x).deriv)
      () (f := fun _ => (1 : ℝ)) (integrable_const 1)
    dsimp only at hst
    rw [hst]
    have hdiag_zero :
        (∑ j : Unit, ∫ w, ∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
          1 * (W_sh (σ ()).1.1 ⬝ᵥ α_sh (σ j).1.1 +
              if () = j then W_aux (σ ()).1.1 ⬝ᵥ α_aux (σ j).1.1 else 0) *
            ((deriv (deriv u) (α_sh (σ j).1.1 ⬝ᵥ w + α_aux (σ j).1.1 ⬝ᵥ (σ j).2) +
                deriv u (α_sh (σ j).1.1 ⬝ᵥ w + α_aux (σ j).1.1 ⬝ᵥ (σ j).2) *
                  deriv u (α_sh (σ j).1.1 ⬝ᵥ w + α_aux (σ j).1.1 ⬝ᵥ (σ j).2)) *
              ∏ r_u ∈ Finset.univ.erase j,
                deriv u (α_sh (σ r_u).1.1 ⬝ᵥ w + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
          ∂(Measure.pi fun _ : Unit => ((μ₀ ω₀).prod γ_aux).tilted
            (fun q_1 => u (α_sh q_1.1.1 ⬝ᵥ w + α_aux q_1.1.1 ⬝ᵥ q_1.2))) ∂γ_sh) = 0 := by
      simp only [Finset.univ_unique, Finset.sum_singleton, ↓reduceIte]
      refine (integral_congr_ae (ae_of_all _ fun w =>
        integral_congr_ae (ae_of_all _ fun σ => ?_))).trans (by simp)
      rw [hcov_diag (σ ()).1.1]
      ring
    rw [hdiag_zero, zero_sub, Fintype.card_unique, Nat.cast_one, one_mul, ← neg_mul,
      ← integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w =>
      integral_congr_ae (ae_of_all _ fun σ => ?_))
    simp only [Finset.univ_unique, Finset.prod_singleton, hcov_sh]
    ring
  -- Step 3: Transport both sides of `hstein_ω₀` integrated over `ω₀ ~ P₀` to `P`!
  -- First build the equivalence between `Option Unit` and `Fin 2`:
  let e_opt2 : Option Unit ≃ Fin 2 :=
    { toFun := fun o => match o with | some () => 0 | none => 1
      invFun := fun i => if i = 0 then some () else none
      left_inv := fun o => by cases o <;> simp
      right_inv := fun i => by fin_cases i <;> simp }
  -- Transport `((μ₀ ω₀).prod γ_aux).tilted (...)` to `μ_s.tilted (E_s ω)` via `e_st_u`!
  let e_u : ℝ ≃ᵐ (Unit → ℝ) := (MeasurableEquiv.funUnique Unit ℝ).symm
  have hmp_u : MeasurePreserving ⇑e_u (gaussianReal 0 1) γ_aux :=
    (measurePreserving_funUnique (gaussianReal 0 1) Unit).symm
  let e_st : ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) ≃ᵐ
      ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) :=
    (interpStateLastSplit (N + 1) M).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u)
  have hmp_st : MeasurePreserving ⇑e_st μ_s (μ₀_base.prod γ_aux) :=
    ((MeasurePreserving.id μ₀_base).prod hmp_u).comp
      (measurePreserving_interpStateLastSplit (N + 1) M)
  have he_st_apply (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      e_st x = ((x.1, Fin.init x.2), fun _ => x.2 (Fin.last M)) := by
    change (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u
      (interpStateLastSplit (N + 1) M x)) = _
    rw [interpStateLastSplit_apply]
    rfl
  let splitΩ (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ) :=
    (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
      Sum.elim (ω.1.1 (Fin.last M)) (fun _ => ω.1.2 (Fin.last M)))
  have hmp_dis := measurePreserving_interpConstraintDisorder_lastSplit (N + 1) M
  have hS_last_eq (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      α_sh (e_st x).1.1 ⬝ᵥ (splitΩ ω).2 + α_aux (e_st x).1.1 ⬝ᵥ (e_st x).2 =
      S_fn ω x (Fin.last M) := by
    rw [he_st_apply]
    dsimp only [α_sh, α_aux, splitΩ, S_fn]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring) (by ring)
  have hS'_last_eq (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      W_sh (e_st x).1.1 ⬝ᵥ (splitΩ ω).2 + W_aux (e_st x).1.1 ⬝ᵥ (e_st x).2 =
      S'_fn ω x (Fin.last M) := by
    rw [he_st_apply]
    dsimp only [W_sh, W_aux, splitΩ, S'_fn]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
    have h1 : (∑ i : Fin (N + 1),
        (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i) =
      ∑ i : Fin (N + 1),
        (1 / (2 * Real.sqrt s)) * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          (ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ))) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
  have htilted_st (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      (μ_s.tilted (E_s ω)).map e_st =
      ((μ₀ (splitΩ ω).1).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ (splitΩ ω).2 + α_aux y.1.1 ⬝ᵥ y.2)) := by
    rw [map_tilted_measurableEquiv e_st hmp_st (Measurable.of_uncurry_left hEm_joint)]
    have hE₀_int : Integrable (fun x₀ => Real.exp (E₀ (splitΩ ω).1 x₀)) μ₀_base :=
      integrable_exp_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r (splitΩ ω).1))
    have hcomb : ((μ₀ (splitΩ ω).1).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ (splitΩ ω).2 + α_aux y.1.1 ⬝ᵥ y.2)) =
        (μ₀_base.prod γ_aux).tilted
          (fun y => E₀ (splitΩ ω).1 y.1 + u (α_sh y.1.1 ⬝ᵥ (splitΩ ω).2 + α_aux y.1.1 ⬝ᵥ y.2)) := by
      rw [← tilted_prod_comp_fst, tilted_tilted (hE₀_int.comp_fst γ_aux)]
      rfl
    rw [hcomb]
    congr 1; funext y
    obtain ⟨x, rfl⟩ := e_st.surjective y
    rw [MeasurableEquiv.symm_apply_apply, hS_last_eq ω x, he_st_apply]
    dsimp only [E_s, E₀, splitΩ, S_fn]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.init_def]
    ring
  -- Now define `I_L (ω₀, w)` and `I_R (ω₀, w)` on `P₀.prod γ_sh`, prove their integrability on
  -- `P₀.prod γ_sh` by pulling back from `P` via `hmp_dis` (or bounding directly on `P₀.prod γ_sh`),
  -- and use Fubini (`integral_prod`)!
  let I_L (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
      1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
      ∂(Measure.pi fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)))
  let I_R (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
        deriv u (α_sh (σ (some ())).1.1 ⬝ᵥ p.2 + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1.1 ⬝ᵥ p.2 + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
      ∂(Measure.pi fun _ : Option Unit => ((μ₀ p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)))
  have hH_comb_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
      (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
      E₀ q_p.1.1 q_p.2.1 + u (α_sh q_p.2.1.1 ⬝ᵥ q_p.1.2 + α_aux q_p.2.1.1 ⬝ᵥ q_p.2.2) := by
    have hp0 : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) => (q_p.1.1, q_p.2.1) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    have hE0_m := hEm_joint.comp hp0
    have hd1 : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
        α_sh q_p.2.1.1 ⬝ᵥ q_p.1.2 := by
      simp only [dotProduct]
      refine Finset.measurable_sum _ fun idx _ => ?_
      have ha : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) => α_sh q_p.2.1.1 idx :=
        (measurable_of_finite fun τ => α_sh τ idx).comp
          (measurable_fst.comp (measurable_fst.comp measurable_snd))
      exact ha.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
    have hd2 : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
        α_aux q_p.2.1.1 ⬝ᵥ q_p.2.2 := by
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp measurable_snd))
    exact hE0_m.add (hu.measurable.comp (hd1.add hd2))
  have hν_comb (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) :
      ((μ₀ p.1).prod γ_aux).tilted (fun y => u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)) =
      (μ₀_base.prod γ_aux).tilted
        (fun y => E₀ p.1 y.1 + u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)) := by
    have hE₀_i : Integrable (fun x₀ => Real.exp (E₀ p.1 x₀)) μ₀_base :=
      integrable_exp_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r p.1))
    rw [← tilted_prod_comp_fst, tilted_tilted (hE₀_i.comp_fst γ_aux)]
    rfl
  have hIL_m : Measurable I_L := by
    have heq : I_L = fun p => ∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀_base.prod γ_aux).tilted
          (fun y => E₀ p.1 y.1 + u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2))) :=
      funext fun p => by dsimp only [I_L]; simp_rw [hν_comb p]
    rw [heq]
    have hG_m : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
        1 * (W_sh (q_p.2 ()).1.1 ⬝ᵥ q_p.1.2 + W_aux (q_p.2 ()).1.1 ⬝ᵥ (q_p.2 ()).2) *
          (∏ r_u : Unit,
            deriv u (α_sh (q_p.2 r_u).1.1 ⬝ᵥ q_p.1.2 + α_aux (q_p.2 r_u).1.1 ⬝ᵥ (q_p.2 r_u).2)) := by
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      have hw1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          W_sh (q_p.2 ()).1.1 ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have hw_idx : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
            W_sh (q_p.2 ()).1.1 idx :=
          (measurable_of_finite fun τ => W_sh τ idx).comp
            (measurable_fst.comp (measurable_fst.comp ((measurable_pi_apply ()).comp measurable_snd)))
        exact hw_idx.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have hw2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          W_aux (q_p.2 ()).1.1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp
          (measurable_snd.comp ((measurable_pi_apply ()).comp measurable_snd)))
      have ha1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_sh (q_p.2 ()).1.1 ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have ha_idx : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
            α_sh (q_p.2 ()).1.1 idx :=
          (measurable_of_finite fun τ => α_sh τ idx).comp
            (measurable_fst.comp (measurable_fst.comp ((measurable_pi_apply ()).comp measurable_snd)))
        exact ha_idx.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_aux (q_p.2 ()).1.1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp
          (measurable_snd.comp ((measurable_pi_apply ()).comp measurable_snd)))
      exact (hw1.add hw2).mul ((measurable_deriv u).comp (ha1.add ha2))
    have hμ_fin : IsFiniteMeasure (μ₀_base.prod γ_aux) := inferInstance
    exact @measurable_integral_pi_tilted _ _ _ _ (μ₀_base.prod γ_aux) hμ_fin _ _ _ hH_comb_m _ hG_m
  have hIR_m : Measurable I_R := by
    have heq : I_R = fun p => ∫ σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
            (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
          deriv u (α_sh (σ (some ())).1.1 ⬝ᵥ p.2 + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (σ none).1.1 ⬝ᵥ p.2 + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀_base.prod γ_aux).tilted
          (fun y => E₀ p.1 y.1 + u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2))) :=
      funext fun p => by dsimp only [I_R]; simp_rw [hν_comb p]
    rw [heq]
    have hfl_o (o : Option Unit) : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
        deriv u (α_sh (q_p.2 o).1.1 ⬝ᵥ q_p.1.2 + α_aux (q_p.2 o).1.1 ⬝ᵥ (q_p.2 o).2) := by
      have ha1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_sh (q_p.2 o).1.1 ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have ha_idx : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
            α_sh (q_p.2 o).1.1 idx :=
          (measurable_of_finite fun τ => α_sh τ idx).comp
            (measurable_fst.comp (measurable_fst.comp ((measurable_pi_apply o).comp measurable_snd)))
        exact ha_idx.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_aux (q_p.2 o).1.1 ⬝ᵥ (q_p.2 o).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp
          (measurable_snd.comp ((measurable_pi_apply o).comp measurable_snd)))
      exact (measurable_deriv u).comp (ha1.add ha2)
    have hR_o : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
          ((((q_p.2 (some ())).1.1 i : ℤ) : ℝ) * (((q_p.2 none).1.1 i : ℤ) : ℝ))) - q) := by
      refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const _
      exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp ((measurable_pi_apply (some ())).comp measurable_snd)))).mul
        (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp ((measurable_pi_apply none).comp measurable_snd))))
    have hμ_fin : IsFiniteMeasure (μ₀_base.prod γ_aux) := inferInstance
    exact @measurable_integral_pi_tilted _ _ _ _ (μ₀_base.prod γ_aux) hμ_fin _ _ _ hH_comb_m _
      ((hR_o.mul (hfl_o (some ()))).mul (hfl_o none))
  -- Pointwise correspondence `I_L (splitΩ ω) = LHS(ω)` and `I_R (splitΩ ω) = RHS(ω)`!
  have hIL_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      I_L (splitΩ ω) =
        ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)) ∂(μ_s.tilted (E_s ω)) := by
    have hprob_ω : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
      isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
    dsimp only [I_L]
    rw [← htilted_st ω, integral_pi_map_equiv (μ_s.tilted (E_s ω)) e_st]
    have h_u := (measurePreserving_funUnique (μ_s.tilted (E_s ω)) Unit).integral_comp_of_aestronglyMeasurable
      (g := fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
        S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)))
      (by
        have hS_x : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
            S_fn ω x (Fin.last M) := by dsimp only [S_fn]; fun_prop
        have hS'_x : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
            S'_fn ω x (Fin.last M) := by dsimp only [S'_fn]; fun_prop
        exact (hS'_x.mul ((measurable_deriv u).comp hS_x)).aestronglyMeasurable)
    refine (integral_congr_ae (ae_of_all _ fun f_u => ?_)).trans h_u
    simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
    rw [hS_last_eq ω (f_u ()), hS'_last_eq ω (f_u ())]
    rfl
  have hIR_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      I_R (splitΩ ω) =
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
    have hprob_ω : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
      isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
    dsimp only [I_R]
    rw [← htilted_st ω, integral_pi_map_equiv (μ_s.tilted (E_s ω)) e_st]
    have hmp_opt2 : MeasurePreserving
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ))
          e_opt2)
        (Measure.pi fun _ : Option Unit => μ_s.tilted (E_s ω))
        (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) :=
      measurePreserving_piCongrLeft _ e_opt2
    have hG2_m : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) := by
      have hS_l (l : Fin 2) : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          S_fn ω (σ l) (Fin.last M) := by dsimp only [S_fn]; fun_prop
      have hR_2 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const _
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 0)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 1))))
      exact (hR_2.mul ((measurable_deriv u).comp (hS_l 0))).mul
        ((measurable_deriv u).comp (hS_l 1))
    have h_opt := hmp_opt2.integral_comp_of_aestronglyMeasurable hG2_m.aestronglyMeasurable
    refine (integral_congr_ae (ae_of_all _ fun τ_o => ?_)).trans h_opt
    have h0 : (MeasurableEquiv.piCongrLeft
        (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) e_opt2 τ_o) 0 =
        τ_o (some ()) := by
      change (Equiv.piCongrLeft _ e_opt2 τ_o) 0 = _
      rw [Equiv.piCongrLeft_apply]; rfl
    have h1 : (MeasurableEquiv.piCongrLeft
        (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) e_opt2 τ_o) 1 =
        τ_o none := by
      change (Equiv.piCongrLeft _ e_opt2 τ_o) 1 = _
      rw [Equiv.piCongrLeft_apply]; rfl
    dsimp only [Function.comp_apply]
    rw [h0, h1, hS_last_eq ω (τ_o (some ())), hS_last_eq ω (τ_o none),
      he_st_apply (τ_o (some ())), he_st_apply (τ_o none)]
  -- Integrability of `I_L` and `I_R` on `P₀.prod γ_sh`!
  have hIR_int : Integrable I_R (P₀.prod γ_sh) := by
    refine Integrable.of_bound hIR_m.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun p => ?_)
    have hprob_p : IsProbabilityMeasure
        (((μ₀ p.1).prod γ_aux).tilted (fun y => u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2))) := by
      rw [hν_comb p]
      exact isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hH_comb_m).aemeasurable
        (ae_of_all _ fun y => add_le_add (interpEnergy_le (fun x => hu.le x) s q r p.1 y.1)
          (hu.le _))
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun σ => by
      rw [abs_mul, abs_mul, sq]
      have hd_ov : |(((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q| ≤ 2 := by
        have h1 : |((N : ℝ) + 1)⁻¹ * ∑ i,
            (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)| ≤ 1 := by
          rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
          have hs_b : |∑ i : Fin (N + 1),
              (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)| ≤ (N : ℝ) + 1 := by
            refine ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := 1) fun i => ?_).trans_eq ?_)
            · rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
            · simp
          exact (inv_mul_le_iff₀ (by positivity)).2 (by linarith)
        have h2 := abs_sub (((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) q
        rw [abs_of_nonneg hq.1] at h2
        linarith [hq.2]
      calc _ ≤ 2 * |D₁| * |D₁| :=
            mul_le_mul (mul_le_mul hd_ov ((hu.abs_deriv_le _).trans (le_abs_self D₁))
              (abs_nonneg _) zero_le_two) ((hu.abs_deriv_le _).trans (le_abs_self D₁))
              (abs_nonneg _) (by positivity)
        _ = 2 * (|D₁| * |D₁|) := by ring
  have hIL_int : Integrable I_L (P₀.prod γ_sh) := by
    -- Bound `|I_L p|` by `|D₁| * (c_w * ∑ |p.2| + c_η * exp(2|B|) * ∫ |η|)`!
    let c_sh : ℝ := max ((1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹)
      ((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q)
    let c_aux : ℝ := (1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)
    have hc_sh0 : 0 ≤ c_sh := le_max_of_le_left (by positivity)
    have hc_aux0 : 0 ≤ c_aux := by dsimp only [c_aux]; positivity
    let dom_p (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
      |D₁| * (c_sh * (∑ idx : Fin (N + 1) ⊕ Unit, |p.2 idx|) +
        Real.exp (2 * |B|) * (c_aux * ∫ η : Unit → ℝ, |η ()| ∂γ_aux))
    have hdom_i : Integrable dom_p (P₀.prod γ_sh) := by
      refine (Integrable.add ?_ (integrable_const _)).const_mul |D₁|
      refine (integrable_finsetSum _ fun idx _ => ?_).const_mul c_sh
      exact (integrable_comp_eval (μ := fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1) (i := idx)
        IsGaussian.integrable_id.abs).comp_snd _
    refine hdom_i.mono' hIL_m.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    dsimp only [I_L]
    have hμ₀_p : IsProbabilityMeasure (μ₀ p.1) :=
      isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r p.1))
    let V_p (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
      u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)
    have hVp_m : Measurable V_p := by
      have ha1 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          α_sh y.1.1 ⬝ᵥ p.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp
            (measurable_fst.comp measurable_fst)).mul_const _
      have ha2 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          α_aux y.1.1 ⬝ᵥ y.2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
      exact hu.measurable.comp (ha1.add ha2)
    have hprob_ν : IsProbabilityMeasure (((μ₀ p.1).prod γ_aux).tilted V_p) :=
      isProbabilityMeasure_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
    have hpt_bd (σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) :
        |1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))| ≤
        |D₁| * (c_sh * (∑ idx, |p.2 idx|) + c_aux * |(σ ()).2 ()|) := by
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      rw [abs_mul, mul_comm _ |deriv u _|]
      refine mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self D₁)) ?_
        (abs_nonneg _) (abs_nonneg D₁)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun idx _ => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rcases idx with i | _
        · dsimp only [W_sh]
          rw [Sum.elim_inl, abs_mul, abs_units_cast_eq_one, mul_one,
            abs_of_nonneg (by positivity)]
          exact le_max_left _ _
        · dsimp only [W_sh]
          rw [Sum.elim_inr, neg_mul, abs_neg, abs_of_nonneg (by positivity)]
          exact le_max_right _ _
      · dsimp only [W_aux, c_aux]
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        rw [neg_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    have hη_int : Integrable (fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
        |y.2 ()|) ((μ₀ p.1).prod γ_aux) :=
      (integrable_comp_eval (μ := fun _ : Unit => gaussianReal 0 1) (i := ())
        IsGaussian.integrable_id.abs).comp_snd _
    have hη_tilted : Integrable
        (fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          |D₁| * (c_sh * (∑ idx, |p.2 idx|) + c_aux * |(σ ()).2 ()|))
        (Measure.pi fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted V_p) := by
      have hy_t := integrable_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
        hη_int
      have hu_t := integrable_comp_eval
        (μ := fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted V_p) (i := ()) hy_t
      exact ((integrable_const _).add (hu_t.const_mul c_aux)).const_mul |D₁|
    have hint_lhs : Integrable
        (fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
            (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2)))
        (Measure.pi fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted V_p) := by
      have hm_σ : Measurable fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
            (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2)) := by
        simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
        have hw1 : Measurable fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
            W_sh (σ ()).1.1 ⬝ᵥ p.2 :=
          Finset.measurable_sum _ fun idx _ =>
            ((measurable_of_finite fun τ => W_sh τ idx).comp
              (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply ())))).mul_const _
        have hw2 : Measurable fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
            W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2 := by
          simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
          exact measurable_const.mul ((measurable_pi_apply ()).comp
            (measurable_snd.comp (measurable_pi_apply ())))
        have hv1 := hVp_m.comp (measurable_pi_apply ())
        have ha1 : Measurable fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
            α_sh (σ ()).1.1 ⬝ᵥ p.2 + α_aux (σ ()).1.1 ⬝ᵥ (σ ()).2 := by
          have ha_sh : Measurable fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
              α_sh (σ ()).1.1 ⬝ᵥ p.2 :=
            Finset.measurable_sum _ fun idx _ =>
              ((measurable_of_finite fun τ => α_sh τ idx).comp
                (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply ())))).mul_const _
          have ha_aux : Measurable fun σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
              α_aux (σ ()).1.1 ⬝ᵥ (σ ()).2 := by
            simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
            exact measurable_const.mul ((measurable_pi_apply ()).comp
              (measurable_snd.comp (measurable_pi_apply ())))
          exact ha_sh.add ha_aux
        exact (hw1.add hw2).mul ((measurable_deriv u).comp ha1)
      exact hη_tilted.mono' hm_σ.aestronglyMeasurable
        (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hpt_bd σ)
    have h1 := (abs_integral_le_integral_abs).trans (integral_mono hint_lhs.abs hη_tilted hpt_bd)
    have hy_t := integrable_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
      hη_int
    have hu_t := integrable_comp_eval
      (μ := fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted V_p) (i := ()) hy_t
    have h2 : (∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        |D₁| * (c_sh * (∑ idx, |p.2 idx|) + c_aux * |(σ ()).2 ()|)
        ∂(Measure.pi fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted V_p)) =
        |D₁| * (c_sh * (∑ idx, |p.2 idx|) +
          c_aux * ∫ y, |y.2 ()| ∂(((μ₀ p.1).prod γ_aux).tilted V_p)) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hu_t.const_mul c_aux),
        integral_const, probReal_univ, one_smul, integral_const_mul]
      congr 3
      exact (measurePreserving_funUnique (((μ₀ p.1).prod γ_aux).tilted V_p)
        Unit).integral_comp_of_aestronglyMeasurable
        ((measurable_pi_apply ()).comp measurable_snd).norm.aestronglyMeasurable
    -- Domination `∫ y, |y.2 ()| ∂(((μ₀ p.1).prod γ_aux).tilted V_p) ≤ exp(2|B|) * ∫ η, |η ()| ∂γ_aux`!
    have hdom_y : ∫ y, |y.2 ()| ∂(((μ₀ p.1).prod γ_aux).tilted V_p) ≤
        Real.exp (2 * |B|) * ∫ η : Unit → ℝ, |η ()| ∂γ_aux := by
      have hd0 := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := Unit)
        (μ := (μ₀ p.1).prod γ_aux) (E₀ := 0) (E₁ := V_p)
        (by simp : Integrable (fun _ => Real.exp 0) ((μ₀ p.1).prod γ_aux))
        (hVp_m.sub measurable_const) (C := |B|)
        (fun y => by simp only [Pi.zero_apply, sub_zero]; exact (hu.abs_le _).trans (le_abs_self B))
        (Y := fun f_u : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) => |(f_u ()).2 ()|)
        (fun _ => abs_nonneg _)
        (by
          rw [tilted_zero_of_isProbabilityMeasure]
          exact integrable_comp_eval (μ := fun _ : Unit => (μ₀ p.1).prod γ_aux) (i := ()) hη_int)
      rw [tilted_zero_of_isProbabilityMeasure] at hd0
      simp only [Fintype.card_unique, Nat.cast_one, mul_one] at hd0
      have hu1 := (measurePreserving_funUnique (((μ₀ p.1).prod γ_aux).tilted V_p)
        Unit).integral_comp_of_aestronglyMeasurable
        (g := fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) => |y.2 ()|)
        ((measurable_pi_apply ()).comp measurable_snd).norm.aestronglyMeasurable
      have hu2 := (measurePreserving_funUnique ((μ₀ p.1).prod γ_aux)
        Unit).integral_comp_of_aestronglyMeasurable
        (g := fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) => |y.2 ()|)
        ((measurable_pi_apply ()).comp measurable_snd).norm.aestronglyMeasurable
      rw [hu1, hu2, integral_prod_fun_snd_of_isProbabilityMeasure] at hd0
      exact hd0
    rw [h2] at h1
    refine h1.trans ?_
    dsimp only [dom_p]
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (abs_nonneg D₁)
    calc c_aux * ∫ y, |y.2 ()| ∂(((μ₀ p.1).prod γ_aux).tilted V_p)
        ≤ c_aux * (Real.exp (2 * |B|) * ∫ η, |η ()| ∂γ_aux) :=
          mul_le_mul_of_nonneg_left hdom_y hc_aux0
      _ = Real.exp (2 * |B|) * (c_aux * ∫ η, |η ()| ∂γ_aux) := by ring
  -- Assemble via `hmp_dis` and Fubini (`integral_prod`)!
  have hlhs_eq : (∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)) ∂(μ_s.tilted (E_s ω)) ∂P) =
      ∫ p, I_L p ∂(P₀.prod γ_sh) := by
    have h1 := hmp_dis.integral_comp_of_aestronglyMeasurable hIL_m.aestronglyMeasurable
    refine (integral_congr_ae (ae_of_all _ fun ω => (hIL_split ω).symm)).trans ?_
    exact h1
  have hrhs_eq : (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P) =
      ∫ p, I_R p ∂(P₀.prod γ_sh) := by
    have h1 := hmp_dis.integral_comp_of_aestronglyMeasurable hIR_m.aestronglyMeasurable
    refine (integral_congr_ae (ae_of_all _ fun ω => (hIR_split ω).symm)).trans ?_
    exact h1
  rw [hlhs_eq, hrhs_eq, integral_prod I_L hIL_int, integral_prod I_R hIR_int,
    ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun ω₀ => hstein_ω₀ ω₀)

/-- **Regrouped derivative formula for the `s`-interpolating pressure (Eq. (2.83)):**
for `s ∈ (0, 1)`, `q ∈ [0, 1]`, `r ≥ 0`, and `u` satisfying `SmartPathPotential₂`,
`d/ds p_{N+1, M, s}(u) = -(r / 2)(1 - q) - (1 / 2) ν_s((R_{1,2} - q)((N + 1)⁻¹ ∑ₖ u'(S¹_{k,s}) u'(S²_{k,s}) - r))`. -/
theorem hasDerivAt_interpolating_pressure_regrouped
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
    HasDerivAt
      (fun s' => ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s) ∂P)
      (-(r / 2) * (1 - q) -
        (1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
              deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) s := by
  intro P_g P_z P_z' P μ_s S_fn E_s
  have hd_raw := hasDerivAt_interpolating_pressure (N := N) (M := M)
    hu.differentiable hu.abs_le hu.abs_deriv_le q r hs
  refine hd_raw.congr_deriv ?_
  let S'_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
    (1 / (2 * Real.sqrt s)) *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) -
      (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
  have hEm_joint : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E_s s p.1 p.2 :=
    measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s s ω)) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
  -- Split the LHS derivative into `(N+1)⁻¹ ∑_k ν_s(S'_k u'(S_k)) - (N+1)⁻¹ ν_s(ext)`!
  have hS'_in_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (k : Fin M) :
      Integrable (fun x => S'_fn ω x k * deriv u (S_fn s ω x k)) (μ_s.tilted (E_s s ω)) := by
    have hm : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        S'_fn ω x k * deriv u (S_fn s ω x k) := by
      have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S'_fn ω x k := by
        dsimp only [S'_fn]; fun_prop
      have h2 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S_fn s ω x k := by
        dsimp only [S_fn]; fun_prop
      exact h1.mul ((measurable_deriv u).comp h2)
    have hξ_k : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|) μ_s :=
      (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
        IsGaussian.integrable_id.abs).comp_snd _
    have hξ_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|)
        (μ_s.tilted (E_s s ω)) :=
      integrable_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω)) hξ_k
    let c0 : ℝ := |D₁| * ((1 / (2 * Real.sqrt s)) *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
      (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|))
    let c1 : ℝ := |D₁| * ((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q))
    refine ((integrable_const c0).add (hξ_t.const_mul c1)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm _ |deriv u _|]
    have hd_b : |deriv u (S_fn s ω x k)| ≤ |D₁| := (hu.abs_deriv_le _).trans (le_abs_self D₁)
    have hS'_b : |S'_fn ω x k| ≤
        (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|) := by
      dsimp only [S'_fn]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul (1 / (2 * Real.sqrt s)), abs_of_nonneg (by positivity),
          abs_mul ((Real.sqrt (N + 1 : ℕ))⁻¹), abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_units_cast_eq_one, mul_one])
      · rw [abs_mul (1 / (2 * Real.sqrt (1 - s))), abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |deriv u (S_fn s ω x k)| * |S'_fn ω x k|
        ≤ |D₁| * ((1 / (2 * Real.sqrt s)) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
          (1 / (2 * Real.sqrt (1 - s))) *
            (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|)) :=
          mul_le_mul hd_b hS'_b (abs_nonneg _) (abs_nonneg D₁)
      _ = c0 + c1 * |x.2 k| := by dsimp only [c0, c1]; ring
  have hext_in_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        (1 / (2 * Real.sqrt (1 - s))) *
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        (μ_s.tilted (E_s s ω)) := by
    have := hprob_ω ω
    exact Integrable.of_bound (by fun_prop)
      ((1 / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul (1 / (2 * Real.sqrt (1 - s))),
          abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]))
  -- Outer integrability of each constraint piece and external piece!
  have hS'_in_P (k : Fin M) :
      Integrable (fun ω => ∫ x, S'_fn ω x k * deriv u (S_fn s ω x k) ∂(μ_s.tilted (E_s s ω))) P := by
    let num_k (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
      ∫ x, (S'_fn ω x k * deriv u (S_fn s ω x k)) * Real.exp (E_s s ω x) ∂μ_s
    let den_k (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
      ∫ x, Real.exp (E_s s ω x) ∂μ_s
    have hS_m := measurable_interpField_joint (L := N + 1) (M := M) s q k
    have hS'_m := measurable_interpFieldDeriv_joint (L := N + 1) (M := M) s q k
    have hnum_m : Measurable num_k :=
      (((hS'_m.mul ((measurable_deriv u).comp hS_m)).mul
        (Real.measurable_exp.comp hEm_joint)).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    have hden_m : Measurable den_k :=
      ((Real.measurable_exp.comp hEm_joint).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    have hm_k : Measurable fun ω => ∫ x, S'_fn ω x k * deriv u (S_fn s ω x k)
        ∂(μ_s.tilted (E_s s ω)) := by
      have heq : (fun ω => ∫ x, S'_fn ω x k * deriv u (S_fn s ω x k) ∂(μ_s.tilted (E_s s ω))) =
          fun ω => num_k ω / den_k ω := funext fun _ => integral_tilted_eq_div _ _
      rw [heq]; exact hnum_m.div hden_m
    -- Domination on `P`:
    let c1 : ℝ := |D₁| * ((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q))
    let dom_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      |D₁| * ((1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|)) +
      Real.exp (2 * M * |B|) * (c1 * ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1))
    have hdom_i : Integrable dom_ω P := by
      refine Integrable.add (Integrable.const_mul ?_ |D₁|) (integrable_const _)
      refine Integrable.add ?_ ?_
      · refine (Integrable.const_mul (integrable_finsetSum _ fun i _ => ?_) _).const_mul _
        have hi1 : Integrable (fun g : Fin M → Fin (N + 1) → ℝ => |g k i|) P_g :=
          integrable_comp_eval (μ := fun _ : Fin M => Measure.pi fun _ => gaussianReal 0 1) (i := k)
            (integrable_comp_eval (μ := fun _ : Fin (N + 1) => gaussianReal 0 1) (i := i)
              IsGaussian.integrable_id.abs)
        exact (hi1.comp_fst _).comp_fst _
      · have hk1 : Integrable (fun z : Fin M → ℝ => Real.sqrt q * |z k|) P_z :=
          (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
            IsGaussian.integrable_id.abs).const_mul _
        exact ((hk1.comp_snd _).comp_fst _).const_mul _
    refine hdom_i.mono' hm_k.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := hprob_ω ω
    rw [Real.norm_eq_abs]
    let c0_ω : ℝ := |D₁| * ((1 / (2 * Real.sqrt s)) *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
      (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|))
    have hξ_k : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|) μ_s :=
      (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
        IsGaussian.integrable_id.abs).comp_snd _
    have hξ_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|)
        (μ_s.tilted (E_s s ω)) :=
      integrable_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω)) hξ_k
    have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        |S'_fn ω x k * deriv u (S_fn s ω x k)| ≤ c0_ω + c1 * |x.2 k| := by
      rw [abs_mul, mul_comm _ |deriv u _|]
      have hd_b : |deriv u (S_fn s ω x k)| ≤ |D₁| := (hu.abs_deriv_le _).trans (le_abs_self D₁)
      have hS'_b : |S'_fn ω x k| ≤
          (1 / (2 * Real.sqrt s)) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
          (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|) := by
        dsimp only [S'_fn]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul (1 / (2 * Real.sqrt s)), abs_of_nonneg (by positivity),
            abs_mul ((Real.sqrt (N + 1 : ℕ))⁻¹), abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_units_cast_eq_one, mul_one])) (by positivity)) (by positivity)
        · rw [abs_mul (1 / (2 * Real.sqrt (1 - s))), abs_of_nonneg (by positivity)]
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
          · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc |deriv u (S_fn s ω x k)| * |S'_fn ω x k|
          ≤ |D₁| * ((1 / (2 * Real.sqrt s)) *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
            (1 / (2 * Real.sqrt (1 - s))) *
              (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|)) :=
            mul_le_mul hd_b hS'_b (abs_nonneg _) (abs_nonneg D₁)
        _ = c0_ω + c1 * |x.2 k| := by dsimp only [c0_ω, c1]; ring
    have h1 := (abs_integral_le_integral_abs).trans
      (integral_mono (hS'_in_pt ω k).abs
        (f := fun x => |S'_fn ω x k * deriv u (S_fn s ω x k)|)
        (g := fun x => c0_ω + c1 * |x.2 k|)
        ((integrable_const c0_ω).add (hξ_t.const_mul c1)) hpt_x)
    rw [integral_add (integrable_const c0_ω) (hξ_t.const_mul c1), integral_const, probReal_univ,
      one_smul, integral_const_mul] at h1
    refine h1.trans (add_le_add le_rfl ?_)
    -- Bound `∫ x, |x.2 k| ∂(μ_s.tilted (E_s s ω)) ≤ exp(2 M |B|) * ∫ ξ, |ξ k| ∂γ_M`!
    let E0_sp (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    have hE0_m : Measurable E0_sp := by dsimp only [E0_sp]; fun_prop
    have hE0_b (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E0_sp x ≤ ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| :=
      Finset.sum_le_sum fun i _ => (le_abs_self _).trans (by
        rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul])
    have hi0 : Integrable (fun x => Real.exp (E0_sp x)) μ_s :=
      integrable_exp_of_ae_le hE0_m.aemeasurable (ae_of_all _ hE0_b)
    have : IsProbabilityMeasure (μ_s.tilted E0_sp) := isProbabilityMeasure_tilted hi0
    have hd_e := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := Unit) (μ := μ_s)
      (E₀ := E0_sp) (E₁ := E_s s ω) hi0
      ((Measurable.of_uncurry_left hEm_joint).sub hE0_m) (C := M * |B|)
      (fun x => by
        have heq_s : E_s s ω x - E0_sp x = ∑ k', u (S_fn s ω x k') := by
          dsimp only [E_s, E0_sp]; ring
        rw [heq_s]
        exact (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ =>
          (hu.abs_le _).trans (le_abs_self B)).trans_eq (by simp))
      (Y := fun f_u : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |(f_u ()).2 k|)
      (fun _ => abs_nonneg _)
      (integrable_comp_eval (μ := fun _ : Unit => μ_s.tilted E0_sp) (i := ())
        (integrable_tilted_of_ae_le hE0_m.aemeasurable (ae_of_all _ hE0_b) hξ_k))
    simp only [Fintype.card_unique, Nat.cast_one, mul_one] at hd_e
    have hu1 : (∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), |(σ ()).2 k|
        ∂(Measure.pi fun _ : Unit => μ_s.tilted (E_s s ω))) =
        ∫ y, |y.2 k| ∂(μ_s.tilted (E_s s ω)) :=
      (measurePreserving_funUnique (μ_s.tilted (E_s s ω))
        Unit).integral_comp_of_aestronglyMeasurable
        (g := fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|)
        ((measurable_pi_apply k).comp measurable_snd).norm.aestronglyMeasurable
    have hu2 : (∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), |(σ ()).2 k|
        ∂(Measure.pi fun _ : Unit => μ_s.tilted E0_sp)) =
        ∫ y, |y.2 k| ∂(μ_s.tilted E0_sp) :=
      (measurePreserving_funUnique (μ_s.tilted E0_sp)
        Unit).integral_comp_of_aestronglyMeasurable
        (g := fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|)
        ((measurable_pi_apply k).comp measurable_snd).norm.aestronglyMeasurable
    rw [hu1, hu2] at hd_e
    have hE0_ind : ∫ x, |x.2 k| ∂(μ_s.tilted E0_sp) =
        ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1) := by
      rw [integral_tilted_eq_div]
      have hnum : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          |x.2 k| * Real.exp (E0_sp x) ∂μ_s) =
          (∫ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
            ∂Measure.count) *
            ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1) := by
        dsimp only [μ_s, E0_sp]
        have hp := integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ)))
          (ν := Measure.pi fun _ : Fin M => gaussianReal 0 1)
          (fun τ => Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r))
          (fun ξ => |ξ k|)
        exact (integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)).trans hp
      have hden : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Real.exp (E0_sp x) ∂μ_s) =
          ∫ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
            ∂Measure.count := by
        dsimp only [μ_s, E0_sp]
        have hp := integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ)))
          (ν := Measure.pi fun _ : Fin M => gaussianReal 0 1)
          (fun τ => Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r))
          (fun _ => (1 : ℝ))
        simpa using hp
      have hden_pos : 0 < ∫ x, Real.exp (E0_sp x) ∂μ_s := integral_exp_pos hi0
      rw [hden] at hden_pos
      rw [hnum, hden, mul_div_cancel_left₀ _ hden_pos.ne']
    rw [hE0_ind, ← mul_assoc] at hd_e
    have hc1_0 : 0 ≤ c1 := by dsimp only [c1]; positivity
    calc c1 * ∫ x, |x.2 k| ∂(μ_s.tilted (E_s s ω))
        ≤ c1 * (Real.exp (2 * M * |B|) *
            ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1)) :=
          mul_le_mul_of_nonneg_left hd_e hc1_0
      _ = Real.exp (2 * M * |B|) *
            (c1 * ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1)) := by ring
  have hext_in_P :
      Integrable (fun ω => ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r) ∂(μ_s.tilted (E_s s ω))) P := by
    let num_e (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
      ∫ x, ((1 / (2 * Real.sqrt (1 - s))) *
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r) * Real.exp (E_s s ω x) ∂μ_s
    let den_e (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
      ∫ x, Real.exp (E_s s ω x) ∂μ_s
    have hg_e : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
        (1 / (2 * Real.sqrt (1 - s))) *
          ∑ i : Fin (N + 1), ((p.2.1 i : ℤ) : ℝ) * p.1.2 i * Real.sqrt r := by
      refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
      have h1 : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))
      have h2 : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => p.1.2 i :=
        (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
      exact (h1.mul h2).mul_const _
    have hm_e : Measurable fun ω => ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r) ∂(μ_s.tilted (E_s s ω)) := by
      have heq : (fun ω => ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s s ω))) = fun ω => num_e ω / den_e ω :=
        funext fun _ => integral_tilted_eq_div _ _
      rw [heq]
      exact (((hg_e.mul (Real.measurable_exp.comp hEm_joint)).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable).div
        (((Real.measurable_exp.comp hEm_joint).stronglyMeasurable.integral_prod_right'
          (ν := μ_s)).measurable)
    have hdom_e : Integrable
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          (1 / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) P :=
      (integrable_finsetSum _ fun i _ =>
        ((integrable_comp_eval (μ := fun _ : Fin (N + 1) => gaussianReal 0 1) (i := i)
          IsGaussian.integrable_id.abs).mul_const _).comp_snd _).const_mul _
    refine hdom_e.mono' hm_e.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := hprob_ω ω
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun x => by
      rw [abs_mul (1 / (2 * Real.sqrt (1 - s))), abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]))
        (by positivity)
  -- Split LHS integral!
  have hlhs_split :
      ((N : ℝ) + 1)⁻¹ * (∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn s ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s s ω)) ∂P) =
      ((N : ℝ) + 1)⁻¹ * (∑ k : Fin M,
        ∫ ω, ∫ x, S'_fn ω x k * deriv u (S_fn s ω x k) ∂(μ_s.tilted (E_s s ω)) ∂P) -
      ((N : ℝ) + 1)⁻¹ *
        ∫ ω, ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s s ω)) ∂P := by
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn s ω x k)) -
            (1 / (2 * Real.sqrt (1 - s))) *
              ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s s ω))) =
        (∑ k : Fin M, ∫ x, S'_fn ω x k * deriv u (S_fn s ω x k) ∂(μ_s.tilted (E_s s ω))) -
          ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
            (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
            ∂(μ_s.tilted (E_s s ω)) := by
      rw [integral_sub (integrable_finsetSum _ fun k _ => hS'_in_pt ω k) (hext_in_pt ω),
        integral_finsetSum _ fun k _ => hS'_in_pt ω k]
    simp_rw [hpt]
    rw [integral_sub (integrable_finsetSum _ fun k _ => hS'_in_P k) hext_in_P,
      integral_finsetSum _ fun k _ => hS'_in_P k, mul_sub]
  have hext_ibp :=
    integral_interpolating_external_field_ibp (N := N) (M := M) hu.measurable hu.abs_le q hr0 hs.2
  dsimp only at hext_ibp
  have hfield_ibp (k : Fin M) :=
    integral_interpolating_field_deriv_ibp (N := N) (M := M) hu hq r hs k
  dsimp only at hfield_ibp
  have hlhs_ibp :
      ((N : ℝ) + 1)⁻¹ * (∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn s ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s s ω)) ∂P) =
      ((N : ℝ) + 1)⁻¹ *
        (∑ k : Fin M, -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) -
      (r / 2) * (1 - ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) := by
    rw [hlhs_split, hext_ibp, Finset.sum_congr rfl fun k _ => hfield_ibp k]
  -- Combine the sum over `k` and the `(r / 2)(1 - ν_s(R_{1,2}))` term into the regrouped RHS!
  let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
  have hR_obs_m : Measurable R_obs := by
    refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
    have h0 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => (((σ 0).1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 0)))
    have h1 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => (((σ 1).1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 1)))
    exact h0.mul h1
  have hR_obs_b (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |R_obs σ| ≤ 1 := by
    dsimp only [R_obs]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hs_b : |∑ i : Fin (N + 1), (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)| ≤
        (N : ℝ) + 1 :=
      ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := 1) fun i => by
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]).trans_eq (by simp))
    exact (inv_mul_le_iff₀ (by positivity)).2 (by linarith)
  have hUk_int_P (k : Fin M) :
      Integrable (fun ω => ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) P := by
    let G_U (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)
    have hS_l (l : Fin 2) : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => S_fn s p.1 (p.2 l) k := by
      have hp_l : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => (p.1, p.2 l) :=
        measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd)
      have hcomp := (measurable_interpField_joint (L := N + 1) (M := M) s q k).comp hp_l
      exact hcomp
    have hG_m : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => G_U p.1 p.2 := by
      have hr_p : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => R_obs p.2 - q :=
        (hR_obs_m.comp measurable_snd).sub_const q
      exact (hr_p.mul ((measurable_deriv u).comp (hS_l 0))).mul
        ((measurable_deriv u).comp (hS_l 1))
    have hμ_fin : IsFiniteMeasure μ_s := inferInstance
    have hm : Measurable fun ω => ∫ σ, G_U ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) :=
      @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint G_U hG_m
    exact Integrable.of_bound hm.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun ω => by
      have := hprob_ω ω
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun σ => by
        dsimp only [G_U]
        rw [abs_mul, abs_mul, sq]
        have hd2 : |R_obs σ - q| ≤ 2 := by
          have h := abs_sub (R_obs σ) q
          rw [abs_of_nonneg hq.1] at h
          linarith [hR_obs_b σ, hq.2]
        calc _ ≤ 2 * |D₁| * |D₁| :=
              mul_le_mul (mul_le_mul hd2 ((hu.abs_deriv_le _).trans (le_abs_self D₁))
                (abs_nonneg _) zero_le_two) ((hu.abs_deriv_le _).trans (le_abs_self D₁))
                (abs_nonneg _) (by positivity)
          _ = 2 * (|D₁| * |D₁|) := by ring)
  have hR_int_P :
      Integrable (fun ω => ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        R_obs σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) P := by
    have hμ_fin : IsFiniteMeasure μ_s := inferInstance
    let G_R (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := R_obs σ
    have hm : Measurable fun ω => ∫ σ, G_R ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) :=
      @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint G_R
        (hR_obs_m.comp measurable_snd)
    exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      have := hprob_ω ω
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ hR_obs_b)
  have hUk_int_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (k : Fin M) :
      Integrable (fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        (R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k))
        (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) := by
    have := hprob_ω ω
    have hS_l (l : Fin 2) : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        S_fn s ω (σ l) k := by dsimp only [S_fn]; fun_prop
    have hm := ((hR_obs_m.sub_const q).mul ((measurable_deriv u).comp (hS_l 0))).mul
      ((measurable_deriv u).comp (hS_l 1))
    exact Integrable.of_bound hm.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, sq]
      have hd2 : |R_obs σ - q| ≤ 2 := by
        have h := abs_sub (R_obs σ) q
        rw [abs_of_nonneg hq.1] at h; linarith [hR_obs_b σ, hq.2]
      calc _ ≤ 2 * |D₁| * |D₁| :=
            mul_le_mul (mul_le_mul hd2 ((hu.abs_deriv_le _).trans (le_abs_self D₁))
              (abs_nonneg _) zero_le_two) ((hu.abs_deriv_le _).trans (le_abs_self D₁))
              (abs_nonneg _) (by positivity)
        _ = 2 * (|D₁| * |D₁|) := by ring)
  have hR_int_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable R_obs (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) := by
    have := hprob_ω ω
    exact Integrable.of_bound hR_obs_m.aestronglyMeasurable 1 (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs]; exact hR_obs_b σ)
  -- Expand RHS integral into the sum of `k` terms minus `r * (ν_s(R_obs) - q)`!
  have hrhs_expand :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (R_obs σ - q) *
          ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
            deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) =
      ((N : ℝ) + 1)⁻¹ * (∑ k : Fin M, ∫ ω, ∫ σ,
        (R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) -
      r * ((∫ ω, ∫ σ, R_obs σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) - q) := by
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (R_obs σ - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
              deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) =
        ((N : ℝ) + 1)⁻¹ * (∑ k : Fin M, ∫ σ,
          (R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) -
        r * ((∫ σ, R_obs σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) - q) := by
      have := hprob_ω ω
      have h_alg (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
          (R_obs σ - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
              deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r) =
          ((N : ℝ) + 1)⁻¹ * (∑ k : Fin M,
            (R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) -
          r * (R_obs σ - q) := by
        rw [mul_sub, ← mul_assoc, mul_comm (R_obs σ - q) (((N : ℝ) + 1)⁻¹), mul_assoc,
          Finset.mul_sum]
        congr 1
        · congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
        · ring
      simp_rw [h_alg]
      rw [integral_sub ((integrable_finsetSum _ fun k _ => hUk_int_pt ω k).const_mul _)
        (((hR_int_pt ω).sub (integrable_const q)).const_mul r),
        integral_const_mul, integral_finsetSum _ fun k _ => hUk_int_pt ω k,
        integral_const_mul, integral_sub (hR_int_pt ω) (integrable_const q),
        integral_const, probReal_univ, one_smul]
    simp_rw [hpt]
    rw [integral_sub ((integrable_finsetSum _ fun k _ => hUk_int_P k).const_mul _)
      ((hR_int_P.sub (integrable_const q)).const_mul r),
      integral_const_mul, integral_finsetSum _ fun k _ => hUk_int_P k,
      integral_const_mul, integral_sub hR_int_P (integrable_const q),
      integral_const, probReal_univ, one_smul]
  dsimp only [R_obs] at hrhs_expand
  refine hlhs_ibp.trans ?_
  rw [hrhs_expand, ← Finset.mul_sum]
  ring

end DerivativeAndIBP

end SpinGlasses
