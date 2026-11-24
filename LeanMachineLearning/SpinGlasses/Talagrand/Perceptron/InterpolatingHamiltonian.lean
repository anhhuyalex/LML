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
# The `s`-interpolating free energy and derivative identity (Talagrand Section 2.4)

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

* `SpinGlasses.continuousOn_interpolating_pressure`: continuity of `s ↦ p_{N+1, M, s}(u)` on
  `[0, 1]`.
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
lemma integral_sum_exp_interpolating_eq
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
    have hj : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) × ℝ =>
        Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2))) :=
      Real.measurable_exp.comp (hu.measurable.comp (by fun_prop))
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hΦm (s : ℝ) : AEStronglyMeasurable (Φ s) P := by
    have heq : Φ s = fun ω => Real.log (∑ τ, Real.exp (E_eff s ω τ)) := funext (hΦ_eq s)
    rw [heq]
    exact (Real.measurable_log.comp
      (Finset.measurable_sum _ fun τ _ =>
        Real.measurable_exp.comp (hE_eff_m s τ))).aestronglyMeasurable
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
        (fun s =>
          (Real.continuous_exp.comp (hu.comp (by fun_prop))).measurable.aestronglyMeasurable)
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
    exact hsum_cont.log fun s =>
      (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
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
        Real.exp (∑ k : Fin M,
          u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)))) := by
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
      have h := (measurePreserving_eval (fun _ : Fin (N + 1) => γ₁)
        i).integral_comp_of_aestronglyMeasurable hlc_m.aestronglyMeasurable
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
      have h := (measurePreserving_eval (fun _ : Fin M => γ₁)
        k).integral_comp_of_aestronglyMeasurable hψ_m.aestronglyMeasurable
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

/-- Measurability and disorder-envelope bound for the `s`-interpolating log-partition function
`log ∫ exp (E_s s ω x) dμ_s` when `0 ≤ s`. -/
lemma measurable_and_abs_log_interpPartition_le
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q r : ℝ) {s : ℝ} (hs0 : 0 ≤ s) :
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    (Measurable fun ω => Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)) ∧
    ∀ ω, |Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)| ≤
      ((N : ℝ) + 1) * Real.log 2 + M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
  intro μ_s E_s
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let E_eff (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
      ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ))) ∂γ₁)
  have hZ_eq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s) = Real.log (∑ τ, Real.exp (E_eff ω τ)) := by
    dsimp only [E_eff, E_s, γ₁]
    rw [integral_sum_exp_interpolating_eq hu hB_le s q r ω]
  have hEm_τ (τ : Fin (N + 1) → ℤˣ) : Measurable fun ω => E_eff ω τ := by
    refine (Finset.measurable_sum _ fun i _ => by fun_prop).add ?_
    refine Finset.measurable_sum _ fun k _ => Real.measurable_log.comp ?_
    have hj : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) × ℝ =>
        Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2))) :=
      Real.measurable_exp.comp (hu.comp (by fun_prop))
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ₁)).measurable
  refine ⟨?_, fun ω => ?_⟩
  · rw [funext hZ_eq]
    exact Real.measurable_log.comp (Finset.measurable_sum _ fun τ _ =>
      Real.measurable_exp.comp (hEm_τ τ))
  · rw [hZ_eq ω]
    have hsq1 : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hEb_τ (τ : Fin (N + 1) → ℤˣ) :
        |E_eff ω τ| ≤ M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
      dsimp only [E_eff]
      refine (abs_add_le _ _).trans ?_
      rw [add_comm ((M : ℝ) * B)]
      refine add_le_add ?_ ?_
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (1 - s) * |ω.2 i| * Real.sqrt r
            ≤ 1 * |ω.2 i| * Real.sqrt r :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq1 (abs_nonneg _))
                (Real.sqrt_nonneg _)
          _ = |ω.2 i| * Real.sqrt r := by ring
      · refine ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := B) fun k => ?_).trans_eq (by simp))
        exact abs_log_integral_exp_le_of_ae_abs_le (hu.comp (by fun_prop)).aemeasurable
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
    linarith

/-- **Pointwise `s`-derivative and disorder-envelope bound for `log ∫ exp (E_s s' ω x) dμ_s`** on
any subinterval `[δ, 1 - δ]` (`δ > 0`). Reusable for `hasDerivAt_interpolating_pressure` and for
higher centered moments (`hasDerivAt_interpolating_centered_moment_pow`). -/
lemma hasDerivAt_and_abs_le_log_interpPartition
    {N M : ℕ} {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (q r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    let γ₁ : Measure ℝ := gaussianReal 0 1
    let γ_M := Measure.pi fun _ : Fin M => γ₁
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod γ_M
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
    let E'_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, S'_fn s' ω x k * deriv u (S_fn s' ω x k)) -
        (1 / (2 * Real.sqrt (1 - s'))) *
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r
    let b_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      |D₁| * (1 / (2 * Real.sqrt δ)) *
        (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
          Real.sqrt q * |ω.1.2 k|)) +
        (1 / (2 * Real.sqrt δ)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
    let b_ξ (ξ : Fin M → ℝ) : ℝ :=
      |D₁| * (1 / (2 * Real.sqrt δ)) * ∑ k : Fin M, Real.sqrt (1 - q) * |ξ k|
    (∀ s', Measurable fun ω => ∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))) ∧
    (∀ ω {s'}, δ ≤ s' → δ ≤ 1 - s' →
      HasDerivAt (fun t => Real.log (∫ x, Real.exp (E_s t ω x) ∂μ_s))
        (∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))) s' ∧
      |∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))| ≤
        b_ω ω + Real.exp (2 * M * B) * ∫ ξ, b_ξ ξ ∂γ_M) := by
  intro γ₁ γ_M μ_s S_fn S'_fn E_s E'_s b_ω b_ξ
  have hum : Measurable u := hu.continuous.measurable
  have hD₁0 : 0 ≤ |D₁| := abs_nonneg D₁
  have hb_ω0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : 0 ≤ b_ω ω := by
    dsimp only [b_ω]; positivity
  have hb_ξ0 (ξ : Fin M → ℝ) : 0 ≤ b_ξ ξ := by dsimp only [b_ξ]; positivity
  have hb_ξ_int : Integrable b_ξ γ_M := by
    refine (integrable_finsetSum _ fun k _ => ?_).const_mul _
    exact (integrable_comp_eval (μ := fun _ : Fin M => γ₁) (i := k)
      IsGaussian.integrable_id.abs).const_mul _
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
  have hF'_m (s' : ℝ) : Measurable fun ω => ∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω)) := by
    let num_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ x, E'_s s' ω x * Real.exp (E_s s' ω x) ∂μ_s
    let den_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ∫ x, Real.exp (E_s s' ω x) ∂μ_s
    have hnum_m : Measurable num_fn :=
      (((hE'm s').mul (Real.measurable_exp.comp (hEm s'))).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    have hden_m : Measurable den_fn :=
      ((Real.measurable_exp.comp (hEm s')).stronglyMeasurable.integral_prod_right'
        (ν := μ_s)).measurable
    rw [show (fun ω => ∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))) =
      fun ω => num_fn ω / den_fn ω from funext fun _ => integral_tilted_eq_div _ _]
    exact hnum_m.div hden_m
  have hd_E (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
      HasDerivAt (fun τ => E_s τ ω x) (E'_s t ω x) t := by
    have hsq2' : HasDerivAt (fun τ : ℝ => Real.sqrt (1 - τ)) (-1 / (2 * Real.sqrt (1 - t))) t :=
      ((hasDerivAt_id t).const_sub 1).sqrt (sub_pos.2 ht1).ne'
    have hS_k (k : Fin M) : HasDerivAt (fun τ => S_fn τ ω x k) (S'_fn t ω x k) t :=
      (hasDerivAt_sqrt_mul_add_sqrt_one_sub_mul ⟨ht0, ht1⟩ _ _).congr_deriv
        (by dsimp only [S'_fn]; ring)
    have hU_k (k : Fin M) : HasDerivAt (fun τ => u (S_fn τ ω x k))
        (S'_fn t ω x k * deriv u (S_fn t ω x k)) t :=
      ((hu (S_fn t ω x k)).hasDerivAt.comp t (hS_k k)).congr_deriv (mul_comm _ _)
    have h_ext (i : Fin (N + 1)) :
        HasDerivAt (fun τ => ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - τ) * ω.2 i * Real.sqrt r)
          (-(1 / (2 * Real.sqrt (1 - t))) * (((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)) t :=
      (((hsq2'.const_mul ((x.1 i : ℤ) : ℝ)).mul_const (ω.2 i)).mul_const (Real.sqrt r)).congr_deriv
        (by ring)
    exact ((HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) => hU_k k).add
      (HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => h_ext i)).congr_deriv
      (by dsimp only [E'_s]; rw [← Finset.mul_sum]; ring)
  have hE'_bd_δ (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) {δ₀ t : ℝ} (hδ₀ : 0 < δ₀)
      (ht_l : δ₀ ≤ t) (ht_r : δ₀ ≤ 1 - t) :
      |E'_s t ω x| ≤
        (|D₁| * (1 / (2 * Real.sqrt δ₀)) *
          (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
            Real.sqrt q * |ω.1.2 k|)) +
          (1 / (2 * Real.sqrt δ₀)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) +
        (|D₁| * (1 / (2 * Real.sqrt δ₀)) * ∑ k : Fin M, Real.sqrt (1 - q) * |x.2 k|) := by
    have hinv_s : 1 / (2 * Real.sqrt t) ≤ 1 / (2 * Real.sqrt δ₀) :=
      one_div_le_one_div_of_le (mul_pos zero_lt_two (Real.sqrt_pos.2 hδ₀))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht_l) zero_le_two)
    have hinv_1s : 1 / (2 * Real.sqrt (1 - t)) ≤ 1 / (2 * Real.sqrt δ₀) :=
      one_div_le_one_div_of_le (mul_pos zero_lt_two (Real.sqrt_pos.2 hδ₀))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht_r) zero_le_two)
    dsimp only [E'_s]
    refine (abs_sub _ _).trans ?_
    have hterm1 : |∑ k : Fin M, S'_fn t ω x k * deriv u (S_fn t ω x k)| ≤
        |D₁| * (1 / (2 * Real.sqrt δ₀)) *
          (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
            Real.sqrt q * |ω.1.2 k|)) +
        (|D₁| * (1 / (2 * Real.sqrt δ₀)) * ∑ k : Fin M, Real.sqrt (1 - q) * |x.2 k|) := by
      have hk_bd (k : Fin M) : |S'_fn t ω x k * deriv u (S_fn t ω x k)| ≤
          |D₁| * (1 / (2 * Real.sqrt δ₀)) *
            (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
              Real.sqrt q * |ω.1.2 k|) + Real.sqrt (1 - q) * |x.2 k|) := by
        rw [abs_mul, mul_comm _ |deriv u (S_fn t ω x k)|]
        have hd_le : |deriv u (S_fn t ω x k)| ≤ |D₁| := (hD₁ _).trans (le_abs_self D₁)
        have hS'_le : |S'_fn t ω x k| ≤ (1 / (2 * Real.sqrt δ₀)) *
            (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
              Real.sqrt q * |ω.1.2 k|) + Real.sqrt (1 - q) * |x.2 k|) := by
          dsimp only [S'_fn]
          refine (abs_sub _ _).trans ?_
          have ht0 : 0 < t := hδ₀.trans_le ht_l
          have ht1 : 0 < 1 - t := hδ₀.trans_le ht_r
          rw [abs_mul (1 / (2 * Real.sqrt t)),
            abs_mul (1 / (2 * Real.sqrt (1 - t))),
            abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt t)),
            abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (1 - t))),
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
          have hp1 : (1 / (2 * Real.sqrt t)) *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * |∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)|) ≤
              (1 / (2 * Real.sqrt δ₀)) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, |ω.1.1 k i|) :=
            mul_le_mul hinv_s (mul_le_mul_of_nonneg_left hsum_g (by positivity))
              (by positivity) (by positivity)
          have hp2 : (1 / (2 * Real.sqrt (1 - t))) *
              |Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k| ≤
              (1 / (2 * Real.sqrt δ₀)) *
                (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|) :=
            mul_le_mul hinv_1s hθ (abs_nonneg _) (by positivity)
          linarith
        calc |deriv u (S_fn t ω x k)| * |S'_fn t ω x k|
            ≤ |D₁| * ((1 / (2 * Real.sqrt δ₀)) *
                (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
                  Real.sqrt q * |ω.1.2 k|) + Real.sqrt (1 - q) * |x.2 k|)) :=
              mul_le_mul hd_le hS'_le (abs_nonneg _) hD₁0
          _ = _ := by ring
      refine ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => hk_bd k)).trans_eq ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    have hterm2 : |(1 / (2 * Real.sqrt (1 - t))) *
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r| ≤
        (1 / (2 * Real.sqrt δ₀)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
      have ht1 : 0 < 1 - t := hδ₀.trans_le ht_r
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (1 - t)))]
      refine mul_le_mul hinv_1s ?_ (abs_nonneg _) (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    linarith
  have hE_abs_bd {t : ℝ} (ht0 : 0 ≤ t)
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      |E_s t ω x| ≤ M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r := by
    have hsq1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    dsimp only [E_s]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ => hB _).trans_eq (by simp)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
        abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (1 - t) * |ω.2 i| * Real.sqrt r
          ≤ 1 * |ω.2 i| * Real.sqrt r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq1 (abs_nonneg _))
              (Real.sqrt_nonneg _)
        _ = |ω.2 i| * Real.sqrt r := by ring
  refine ⟨hF'_m, fun ω {s'} hs'l hs'r => ⟨?_, ?_⟩⟩
  · have hs'_Ioo : s' ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le hs'l, by linarith⟩
    obtain ⟨δ', hδ', hδ'_bd⟩ := exists_Ioo_nhds_bound hs'_Ioo
    let C_E : ℝ := M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
    let b_ω' : ℝ := |D₁| * (1 / (2 * Real.sqrt δ')) *
        (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
          Real.sqrt q * |ω.1.2 k|)) +
        (1 / (2 * Real.sqrt δ')) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
    let b_ξ' (ξ : Fin M → ℝ) : ℝ :=
      |D₁| * (1 / (2 * Real.sqrt δ')) * ∑ k : Fin M, Real.sqrt (1 - q) * |ξ k|
    have hb_ξ'_int : Integrable b_ξ' γ_M := by
      refine (integrable_finsetSum _ fun k _ => ?_).const_mul _
      exact (integrable_comp_eval (μ := fun _ : Fin M => γ₁) (i := k)
        IsGaussian.integrable_id.abs).const_mul _
    have hm_ev : ∀ᶠ t in 𝓝 s', AEStronglyMeasurable (fun x => Real.exp (E_s t ω x)) μ_s :=
      Eventually.of_forall fun t => (Real.measurable_exp.comp
        ((hEm t).comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    have hi_s' : Integrable (fun x => Real.exp (E_s s' ω x)) μ_s :=
      integrable_exp_of_ae_le ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs'_Ioo.1.le ω x))
    have hdm : AEStronglyMeasurable (fun x => E'_s s' ω x * Real.exp (E_s s' ω x)) μ_s :=
      (((hE'm s').comp (measurable_const.prodMk measurable_id)).mul
        (Real.measurable_exp.comp
          ((hEm s').comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
    exact hasDerivAt_log_integral_exp_of_dominated (μ := μ_s) (E := fun t x => E_s t ω x)
      (E' := fun t x => E'_s t ω x) (s := Ioo (s' - δ') (s' + δ'))
      (Ioo_mem_nhds (by linarith) (by linarith)) hm_ev hi_s' hdm
      (b := fun x => (b_ω' + b_ξ' x.2) * Real.exp C_E)
      (((integrable_const b_ω').add (hb_ξ'_int.comp_snd _)).mul_const (Real.exp C_E))
      (ae_of_all _ fun x t ht => by
        obtain ⟨h1, h2⟩ := hδ'_bd t ht
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hE'_bd_δ ω x hδ' h1 h2)
          (Real.exp_le_exp.2 (le_of_abs_le (hE_abs_bd (hδ'.trans_le h1).le ω x)))
          (Real.exp_pos _).le (by dsimp only [b_ω', b_ξ']; positivity))
      (ae_of_all _ fun x t ht => by
        obtain ⟨h1, h2⟩ := hδ'_bd t ht
        exact hd_E ω x (hδ'.trans_le h1) (by linarith))
  · have hs'0 : 0 ≤ s' := (hδ.trans_le hs'l).le
    have hi_s' : Integrable (fun x => Real.exp (E_s s' ω x)) μ_s :=
      integrable_exp_of_ae_le ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs'0 ω x))
    have hprob_t : IsProbabilityMeasure (μ_s.tilted (E_s s' ω)) :=
      isProbabilityMeasure_tilted hi_s'
    have hb_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ω ω + b_ξ x.2)
        (μ_s.tilted (E_s s' ω)) :=
      integrable_tilted_of_ae_le
        ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs'0 ω x))
        ((integrable_const (b_ω ω)).add (hb_ξ_int.comp_snd _))
    have hE'i : Integrable (E'_s s' ω) (μ_s.tilted (E_s s' ω)) :=
      hb_t.mono' ((hE'm s').comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hE'_bd_δ ω x hδ hs'l hs'r)
    have h1 : |∫ x, E'_s s' ω x ∂(μ_s.tilted (E_s s' ω))| ≤
        b_ω ω + ∫ x, b_ξ x.2 ∂(μ_s.tilted (E_s s' ω)) := by
      refine (abs_integral_le_integral_abs).trans ?_
      refine (integral_mono hE'i.abs hb_t fun x => hE'_bd_δ ω x hδ hs'l hs'r).trans_eq ?_
      have hb_ξ_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ξ x.2)
          (μ_s.tilted (E_s s' ω)) :=
        integrable_tilted_of_ae_le
          ((hEm s').comp (measurable_const.prodMk measurable_id)).aemeasurable
          (ae_of_all _ fun x => le_of_abs_le (hE_abs_bd hs'0 ω x))
          (hb_ξ_int.comp_snd _)
      rw [integral_add (integrable_const (b_ω ω)) hb_ξ_t, integral_const, probReal_univ, one_smul]
    refine h1.trans (add_le_add le_rfl ?_)
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
      rw [show E_s s' ω x - E_0_spin x = ∑ k : Fin M, u (S_fn s' ω x k) by
        dsimp only [E_s, E_0_spin]; ring]
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
        ∫ x, b_ξ x.2 ∂ν :=
      (measurePreserving_funUnique ν Unit).integral_comp_of_aestronglyMeasurable
        (by dsimp only [b_ξ]; fun_prop :
          Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => b_ξ x.2).aestronglyMeasurable
    have : SigmaFinite (μ_s.tilted (E_s s' ω)) := inferInstance
    have : IsProbabilityMeasure (μ_s.tilted E_0_spin) := isProbabilityMeasure_tilted hi0
    rw [h_unit (μ_s.tilted (E_s s' ω)), h_unit (μ_s.tilted E_0_spin)] at hdom_1
    simp only [Fintype.card_unique, Nat.cast_one, mul_one] at hdom_1
    have hE0_indep : ∫ x, b_ξ x.2 ∂(μ_s.tilted E_0_spin) = ∫ ξ, b_ξ ξ ∂γ_M := by
      rw [integral_tilted_eq_div]
      have hnum : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          b_ξ x.2 * Real.exp (E_0_spin x) ∂μ_s) =
          (∫ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)
            ∂Measure.count) * (∫ ξ, b_ξ ξ ∂γ_M) := by
        dsimp only [μ_s, E_0_spin]
        exact (integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)).trans
          (integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ))) (ν := γ_M)
            (fun τ => Real.exp (∑ i : Fin (N + 1),
              ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)) b_ξ)
      have hden : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Real.exp (E_0_spin x) ∂μ_s) =
          ∫ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)
            ∂Measure.count := by
        dsimp only [μ_s, E_0_spin]
        simpa using integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ))) (ν := γ_M)
          (fun τ => Real.exp (∑ i : Fin (N + 1),
            ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r)) (fun _ => (1 : ℝ))
      have hden_pos : 0 < ∫ x, Real.exp (E_0_spin x) ∂μ_s := integral_exp_pos hi0
      rw [hden] at hden_pos
      rw [hnum, hden, mul_div_cancel_left₀ _ hden_pos.ne']
    rw [hE0_indep, ← mul_assoc] at hdom_1
    exact hdom_1

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
  obtain ⟨δ, hδ, hδ_bd⟩ := exists_Ioo_nhds_bound hs
  let U_nbhd : Set ℝ := Ioo (s - δ) (s + δ)
  have hU_nhds : U_nbhd ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨hF'_m, hpt_δ⟩ := hasDerivAt_and_abs_le_log_interpPartition (N := N) (M := M)
    hu hB hD₁ q r hδ
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let b_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    |D₁| * (1 / (2 * Real.sqrt δ)) *
      (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
        Real.sqrt q * |ω.1.2 k|)) +
      (1 / (2 * Real.sqrt δ)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
  let b_ξ (ξ : Fin M → ℝ) : ℝ :=
    |D₁| * (1 / (2 * Real.sqrt δ)) * ∑ k : Fin M, Real.sqrt (1 - q) * |ξ k|
  have hb_ω_int : Integrable b_ω P := by
    refine Integrable.add ?_ ?_
    · refine (integrable_finsetSum _ fun k _ => Integrable.add ?_ ?_).const_mul _
      · refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
        exact ((integrable_comp_eval (μ := fun _ : Fin M => Measure.pi fun _ => γ₁) (i := k)
          (integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i)
            IsGaussian.integrable_id.abs)).comp_fst _).comp_fst _
      · exact (((integrable_comp_eval (μ := fun _ : Fin M => γ₁) (i := k)
          IsGaussian.integrable_id.abs).const_mul _).comp_snd _).comp_fst _
    · refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
      exact ((integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i)
        IsGaussian.integrable_id.abs).mul_const _).comp_snd _
  have hlogZ_int {s' : ℝ} (hs' : s' ∈ U_nbhd) :
      Integrable (fun ω => Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s)) P := by
    have hs'0 : 0 ≤ s' := (hδ.trans_le (hδ_bd s' hs').1).le
    obtain ⟨hm_log, hbd_log⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
      hu.continuous.measurable hB q r hs'0
    have hdom : Integrable
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          ((N : ℝ) + 1) * Real.log 2 + M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) P :=
      ((integrable_const _).add (integrable_const _)).add
        (integrable_finsetSum _ fun i _ =>
          ((integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ₁) (i := i)
            IsGaussian.integrable_id.abs).mul_const _).comp_snd _)
    exact hdom.mono' hm_log.aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).trans_le (hbd_log ω))
  have hs_mem : s ∈ U_nbhd := ⟨by linarith, by linarith⟩
  have hP_deriv : HasDerivAt (fun s' => ∫ ω, Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s) ∂P)
      (∫ ω, ∫ x,
        ((∑ k : Fin M, S'_fn s ω x k * deriv u (S_fn s ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s s ω)) ∂P) s :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
      (F := fun t ω => Real.log (∫ x, Real.exp (E_s t ω x) ∂μ_s))
      (F' := fun t ω => ∫ x,
        ((∑ k : Fin M, S'_fn t ω x k * deriv u (S_fn t ω x k)) -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s t ω)))
      (s := U_nbhd)
      (bound := fun ω => b_ω ω + Real.exp (2 * M * B) *
        ∫ ξ, b_ξ ξ ∂(Measure.pi fun _ : Fin M => γ₁))
      hU_nhds
      (Filter.eventually_of_mem hU_nhds fun _ ht => (hlogZ_int ht).aestronglyMeasurable)
      (hlogZ_int hs_mem) (hF'_m s).aestronglyMeasurable
      (ae_of_all _ fun ω t ht => by
        rw [Real.norm_eq_abs]; exact (hpt_δ ω (hδ_bd t ht).1 (hδ_bd t ht).2).2)
      (hb_ω_int.add (integrable_const _))
      (ae_of_all _ fun ω t ht => (hpt_δ ω (hδ_bd t ht).1 (hδ_bd t ht).2).1)).2
  exact hP_deriv.const_mul (((N : ℝ) + 1)⁻¹)

/-- The `k`-th interpolating field is jointly measurable in the disorder and the state. -/
lemma measurable_interpField_joint {L M : ℕ} (s q : ℝ) (k : Fin M) :
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

lemma measurable_interpFieldDeriv_joint {L M : ℕ} (s q : ℝ) (k : Fin M) :
    Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        ((Fin L → ℤˣ) × (Fin M → ℝ)) =>
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((p.2.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) *
          (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2.2 k) := by
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

/-- For a fixed disorder `ω`, the `k`-th interpolating field is measurable in the state. -/
lemma measurable_interpField_slice {L M : ℕ} (s q : ℝ) (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) ×
    (Fin L → ℝ)) (k : Fin M) :
    Measurable fun x : (Fin L → ℤˣ) × (Fin M → ℝ) =>
      Real.sqrt s * ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k) :=
  (measurable_interpField_joint (L := L) (M := M) s q k).comp
    (measurable_const (a := ω) |>.prodMk measurable_id)

/-- The `k`-th interpolating field of replica `l` is jointly measurable in the disorder and the
replica tuple. -/
lemma measurable_interpField_replica_joint {L M : ℕ} (s q : ℝ) (k : Fin M) (l : Fin 2) :
    Measurable fun p : (((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) ×
        (Fin 2 → (Fin L → ℤˣ) × (Fin M → ℝ)) =>
      Real.sqrt s * ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * (((p.2 l).1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * (p.2 l).2 k) :=
  (measurable_interpField_joint s q k).comp
    (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))

/-- The interpolating energy is jointly measurable in the disorder and the state. -/
lemma measurable_interpEnergy_joint {L M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
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

/-- For a fixed disorder `ω`, the interpolating energy is measurable in the state. -/
lemma measurable_interpEnergy_slice {L M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) (s q r : ℝ)
    (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) :
    Measurable fun x : (Fin L → ℤˣ) × (Fin M → ℝ) =>
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin L, ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r :=
  (Finset.measurable_sum _ fun k _ => hu.comp (measurable_interpField_slice s q ω k)).add
    (Finset.measurable_sum _ fun i _ =>
      (((measurable_units_cast.comp
        ((measurable_pi_apply i).comp measurable_fst)).mul_const _).mul_const _).mul_const _)

/-- Upper bound on the `s`-interpolating energy: `(M · B + ∑ᵢ |√(1 - s) z'ᵢ √r|)` when `u ≤ B`. -/
lemma interpEnergy_le {L M : ℕ} {u : ℝ → ℝ} {B : ℝ} (hB : ∀ x, u x ≤ B)
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

/-- The Gibbs measure of the `s`-interpolating energy is a probability measure when `u` is
measurable and bounded above. -/
lemma isProbabilityMeasure_tilted_interpEnergy {L M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ}
    (hB : ∀ x, u x ≤ B) (s q r : ℝ) (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) :
    IsProbabilityMeasure (((Measure.count : Measure (Fin L → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)).tilted
      fun x : (Fin L → ℤˣ) × (Fin M → ℝ) =>
        (∑ k : Fin M, u (Real.sqrt s *
            ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
        ∑ i : Fin L, ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) :=
  isProbabilityMeasure_tilted_of_ae_le
    (measurable_interpEnergy_slice hu s q r ω).aemeasurable
    (ae_of_all _ fun x => interpEnergy_le hB s q r ω x)

/-- Pointwise Gaussian IBP on coordinate `i` of `z'` at fixed `(g, z)` for the `s`-interpolating
Gibbs measure (`r ≥ 0`). -/
private lemma interp_external_field_ibp_coord
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q r s : ℝ)
    (gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) (i : Fin (N + 1)) :
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (z' : Fin (N + 1) → ℝ) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, gz.1 k j * ((x.1 j : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * gz.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ j : Fin (N + 1), ((x.1 j : ℤ) : ℝ) * Real.sqrt (1 - s) * z' j * Real.sqrt r
    ∫ z', z' i * (∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s z'))) ∂P_z' =
      (Real.sqrt (1 - s) * Real.sqrt r) *
        ∫ z', (1 - ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s z'))) ∂P_z' := by
  intro P_z' μ_s E_s
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let c : ℝ := Real.sqrt (1 - s) * Real.sqrt r
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  let D_gz (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ∑ k : Fin M, u (Real.sqrt s *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, gz.1 k j * ((x.1 j : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * gz.2 k + Real.sqrt (1 - q) * x.2 k))
  let X_i (j : Fin (N + 1)) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    c * ((x.1 j : ℤ) : ℝ)
  have hDm : Measurable D_gz := Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)
  have hDb (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |D_gz x| ≤ M * |B| :=
    (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ => (hB _).trans (le_abs_self B)).trans_eq
      (by simp)
  have hXm (j : Fin (N + 1)) : Measurable (X_i j) := by dsimp only [X_i]; fun_prop
  have hXb (j : Fin (N + 1)) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |X_i j x| ≤ c := by
    dsimp only [X_i]; rw [abs_mul, abs_of_nonneg hc0, abs_units_cast_eq_one, mul_one]
  have hE_eq (z' : Fin (N + 1) → ℝ) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      E_s z' x = D_gz x + ∑ j : Fin (N + 1), z' j * X_i j x := by
    dsimp only [E_s, D_gz, X_i, c]
    congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
  have hZ_gauss : HasGaussianLaw (fun (z' : Fin (N + 1) → ℝ) (j : Fin (N + 1)) => z' j) P_z' := by
    let cId : Fin (N + 1) → Fin (N + 1) → ℝ := fun j l => if l = j then 1 else 0
    convert hasGaussianLaw_dotProduct_family cId using 1
    ext z' j; simp [cId, dotProduct]
  have hZ_mean (j : Fin (N + 1)) : ∫ z' : Fin (N + 1) → ℝ, z' j ∂P_z' = 0 := by
    refine (integral_congr_ae (ae_of_all _ fun z' => ?_)).trans
      (integral_dotProduct_pi_gaussianReal (Pi.single j (1 : ℝ)))
    simp [dotProduct, Pi.single_apply]
  have hZ_cov (j l : Fin (N + 1)) :
      ∫ z' : Fin (N + 1) → ℝ, z' j * z' l ∂P_z' = if j = l then 1 else 0 := by
    let ej : Fin (N + 1) → ℝ := Pi.single j 1
    let el : Fin (N + 1) → ℝ := Pi.single l 1
    have hpt (z' : Fin (N + 1) → ℝ) : z' j * z' l = (ej ⬝ᵥ z') * (el ⬝ᵥ z') := by
      simp [ej, el, dotProduct, Pi.single_apply]
    simp_rw [hpt]
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    simp [ej, el, dotProduct, Pi.single_apply, eq_comm]
  let R_gz (Y : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) → ℝ) (z' : Fin (N + 1) → ℝ) : ℝ :=
    (∫ x, Y x * Real.exp (D_gz x + ∑ k, z' k * X_i k x) ∂μ_s) /
      ∫ x, Real.exp (D_gz x + ∑ k, z' k * X_i k x) ∂μ_s
  have hR_tilted (Y : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) → ℝ) (z' : Fin (N + 1) → ℝ) :
      R_gz Y z' = ∫ x, Y x ∂(μ_s.tilted (E_s z')) := by
    rw [integral_tilted_eq_div]; simp_rw [hE_eq z']; rfl
  have hstein := integral_mul_gibbs_ratio_eq_sum (μ := μ_s) (P := P_z')
    R_gz (fun _ _ => rfl) hZ_gauss hZ_mean i hDm hXm
    (Y := fun x => ((x.1 i : ℤ) : ℝ)) (by fun_prop) hc0 zero_le_one
    hDb hXb (fun _ => (abs_units_cast_eq_one _).le)
  simp only [hZ_cov i, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, hR_tilted] at hstein
  rw [hstein, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z' => ?_)
  dsimp only
  have hprob : IsProbabilityMeasure (μ_s.tilted (E_s z')) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu hB_le s q r (gz, z')
  have hsq_x : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      ((x.1 i : ℤ) : ℝ) * X_i i x ∂(μ_s.tilted (E_s z'))) = c := by
    have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        ((x.1 i : ℤ) : ℝ) * X_i i x = c := by
      dsimp only [X_i]
      have h1 : ((x.1 i : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
      linear_combination c * h1
    simp_rw [hpt_x]; simp
  have hlin_x : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      X_i i x ∂(μ_s.tilted (E_s z'))) =
      c * ∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s z')) :=
    integral_const_mul c _
  have htwo_rep :
      (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s z'))) ^ 2 =
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s z')) := by
    rw [sq]
    exact (integral_pi_fin_two_mul_fun (μ_s.tilted (E_s z'))
      (fun x => ((x.1 i : ℤ) : ℝ)) (fun x => ((x.1 i : ℤ) : ℝ))).symm
  rw [hsq_x, hlin_x, ← htwo_rep]
  dsimp only [c]; ring

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
  let c : ℝ := Real.sqrt (1 - s) * Real.sqrt r
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu s q r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu hB_le s q r ω
  let L_i (i : Fin (N + 1))
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ω.2 i * ∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))
  have hLi_int (i : Fin (N + 1)) : Integrable (L_i i) P := by
    have hspin_p : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd))
    have hLm : Measurable (L_i i) :=
      ((measurable_pi_apply i).comp measurable_snd).mul
        (measurable_integral_tilted_dep hEm_joint hspin_p)
    have hdom_i : Integrable
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) => |ω.2 i|) P :=
      (integrable_comp_eval (μ := fun _ : Fin (N + 1) => gaussianReal 0 1) (i := i)
        IsGaussian.integrable_id.abs).comp_snd _
    refine hdom_i.mono' hLm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := hprob_ω ω
    rw [Real.norm_eq_abs, abs_mul]
    calc |ω.2 i| * |∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))|
        ≤ |ω.2 i| * 1 := mul_le_mul_of_nonneg_left
          (abs_integral_le_of_forall_abs_le _ fun _ => (abs_units_cast_eq_one _).le)
          (abs_nonneg _)
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
    exact Integrable.of_bound
      (measurable_integral_pi_tilted (μ := μ_s) hEm_joint hGm).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
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
      ae_of_all _ fun gz => interp_external_field_ibp_coord hu hB q r s gz i
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

/-- Swapping the constraints `k₁` and `k₂` in a state `(σ, ξ)` of the interpolating system:
the spins are unchanged and the auxiliary coordinates `ξ_{k₁}`, `ξ_{k₂}` are exchanged. -/
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

/-- Swapping the constraints `k₁` and `k₂` in the disorder `((g, z), z')` of the interpolating
system. The disorder of constraint `k` is its row `g k` and its shared Gaussian `z k`, and both
are exchanged between `k₁` and `k₂`; the external field `z'` is unchanged. -/
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

/-- **Splitting the `(M + 1)`-constraint `s`-interpolating disorder into the `M`-constraint
disorder and the last constraint's shared Gaussian vector `(g_M, z_M) : (Fin L ⊕ Unit) → ℝ`.** -/
lemma measurePreserving_interpConstraintDisorder_lastSplit (L M : ℕ) :
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
      P_M1 (P_M.prod (Measure.pi fun _ : Fin L ⊕ Unit => γ)) :=
  measurePreserving_lastRow_sumPi_split (ι := Fin L) (gaussianReal 0 1)
    (Measure.pi fun _ : Fin L => gaussianReal 0 1) M

/-- Splitting the `(M + 1)`-constraint state `(σ, ξ)` of the `s`-interpolating system into the
`M`-constraint state `(σ, Fin.init ξ)` and the last auxiliary coordinate `ξ_M`. -/
def interpStateLastSplit (L M : ℕ) :
    ((Fin L → ℤˣ) × (Fin (M + 1) → ℝ)) ≃ᵐ (((Fin L → ℤˣ) × (Fin M → ℝ)) × ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.finSuccProd ℝ M)).trans
    MeasurableEquiv.prodAssoc.symm

@[simp]
lemma interpStateLastSplit_apply {L M : ℕ} (x : (Fin L → ℤˣ) × (Fin (M + 1) → ℝ)) :
    interpStateLastSplit L M x = ((x.1, Fin.init x.2), x.2 (Fin.last M)) := by
  simp [interpStateLastSplit, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_prodCongr,
    MeasurableEquiv.coe_refl, Fin.init_def]

lemma measurePreserving_interpStateLastSplit (L M : ℕ) :
    MeasurePreserving ⇑(interpStateLastSplit L M)
      ((Measure.count : Measure (Fin L → ℤˣ)).prod
        (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1))
      (((Measure.count : Measure (Fin L → ℤˣ)).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 1)) :=
  (measurePreserving_prodAssoc _ _ _).symm.comp
    ((MeasurePreserving.id _).prod (measurePreserving_finSuccProd _ M))

/-- **Covariance of the shared Gaussian block in the Stein step** (Talagrand (2.82), (2.91)):
for the coefficient vectors of `S_s'` and `S_s` over the shared Gaussians `(g, z)`, the covariance
of the derivative of the field of `τ₁` with the field of `τ₂` is `(R(τ₁, τ₂) - q) / 2`. -/
theorem interp_stein_cov_shared {N : ℕ} {s q : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hq : 0 ≤ q)
    (τ₁ τ₂ : Fin (N + 1) → ℤˣ) :
    Sum.elim (fun i : Fin (N + 1) =>
        (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₁ i : ℤ) : ℝ))
      (fun _ : Unit => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q) ⬝ᵥ
    Sum.elim (fun i : Fin (N + 1) =>
        Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ₂ i : ℤ) : ℝ))
      (fun _ : Unit => Real.sqrt (1 - s) * Real.sqrt q) =
      (1 / 2) * ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) - q) := by
    rw [sumElim_dotProduct_sumElim]
    have hs_ne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs.1).ne'
    have h1s_ne : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hs.2)).ne'
    have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hsq_L : (Real.sqrt (N + 1 : ℕ))⁻¹ * (Real.sqrt (N + 1 : ℕ))⁻¹ = ((N : ℝ) + 1)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    have hsq_q : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
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

/-- **The diagonal covariance vanishes in the Stein step:** the shared and the auxiliary Gaussian
contributions to `⟨S_s', S_s⟩` of one spin configuration cancel, which kills the diagonal term. -/
theorem interp_stein_cov_diag {N : ℕ} {s q : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (τ : Fin (N + 1) → ℤˣ) :
    Sum.elim (fun i : Fin (N + 1) =>
        (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ : Unit => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q) ⬝ᵥ
    Sum.elim (fun i : Fin (N + 1) =>
        Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ : Unit => Real.sqrt (1 - s) * Real.sqrt q) +
    (fun _ : Unit => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)) ⬝ᵥ
      (fun _ : Unit => Real.sqrt (1 - s) * Real.sqrt (1 - q)) = 0 := by
    rw [interp_stein_cov_shared hs hq.1 τ τ]
    have hself : (((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) = 1 := by
      simpa only [dotProduct, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        card_inv_mul_dotProduct_self_eq_one (fun i : Fin (N + 1) => ((τ i : ℤ) : ℝ))
          (fun i => units_cast_sq (τ i))
    have haux_dot : (fun _ : Unit => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)) ⬝ᵥ
        (fun _ : Unit => Real.sqrt (1 - s) * Real.sqrt (1 - q)) = -(1 / 2) * (1 - q) := by
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

/-- **Single-replica Gaussian integration by parts with factor `deriv u` and zero diagonal
covariance.** For `R = Unit` and observable `1`, when `W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0`
and `W_sh τ₁ ⬝ᵥ α_sh τ₂ = (1 / 2) * c τ₁ τ₂`, `stein_tilted_replica_ratio` kills the diagonal term
and leaves `-(1 / 2)` times the `Option Unit` two-replica expectation of `c * u' * u'`. -/
theorem stein_tilted_unit_replica_deriv
    {α L K_sh K_aux : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (π : α → L) (hπ : Measurable π)
    (α_sh W_sh : L → K_sh → ℝ) (α_aux W_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (c : L → L → ℝ)
    (hcov_sh : ∀ τ₁ τ₂, W_sh τ₁ ⬝ᵥ α_sh τ₂ = (1 / 2) * c τ₁ τ₂)
    (hcov_diag : ∀ τ, W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    ∫ w, ∫ σ : Unit → α × (K_aux → ℝ),
        1 * (W_sh (π (σ ()).1) ⬝ᵥ w + W_aux (π (σ ()).1) ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (π (σ r_u).1) ⬝ᵥ w + α_aux (π (σ r_u).1) ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh (π y.1) ⬝ᵥ w + α_aux (π y.1) ⬝ᵥ y.2))) ∂γ_sh =
      -(1 / 2) * ∫ w, ∫ σ : Option Unit → α × (K_aux → ℝ),
        c (π (σ (some ())).1) (π (σ none).1) *
          deriv u (α_sh (π (σ (some ())).1) ⬝ᵥ w + α_aux (π (σ (some ())).1) ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (π (σ none).1) ⬝ᵥ w + α_aux (π (σ none).1) ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh (π y.1) ⬝ᵥ w + α_aux (π y.1) ⬝ᵥ y.2))) ∂γ_sh := by
  intro γ_sh γ_aux
  have hψ_deriv := hu.hasDerivAt_deriv_mul_exp
  have hst := stein_tilted_replica_ratio (R := Unit) (μ₀ := μ₀)
    (π := π) hπ α_sh W_sh α_aux W_aux
    hu.differentiable hu.abs_le hu.abs_deriv_le
    (fun _ => deriv u)
    (fun _ x => (hψ_deriv x).differentiableAt)
    (M₀ := fun _ => |D₁|) (M' := fun _ => (|D₂| + |D₁| ^ 2) * Real.exp |B|)
    (fun _ x => hu.abs_deriv_le_abs x)
    (fun _ x => by
      rw [(hψ_deriv x).deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul ?_ (Real.exp_le_exp.2 (hu.le_abs x)) (Real.exp_pos _).le (by positivity)
      refine (abs_add_le _ _).trans (add_le_add
        ((hu.abs_deriv₂_le x).trans (le_abs_self D₂)) ?_)
      rw [abs_mul, sq]
      exact mul_le_mul (hu.abs_deriv_le_abs x) (hu.abs_deriv_le_abs x)
        (abs_nonneg _) (abs_nonneg _))
    (fun _ x => deriv (deriv u) x + deriv u x * deriv u x)
    (fun _ x => (hψ_deriv x).deriv)
    () (f := fun _ => (1 : ℝ)) (integrable_const 1)
  dsimp only at hst
  rw [hst]
  have hdiag_zero :
      (∑ j : Unit, ∫ w, ∫ σ : Unit → α × (K_aux → ℝ),
        1 * (W_sh (π (σ ()).1) ⬝ᵥ α_sh (π (σ j).1) +
            if () = j then W_aux (π (σ ()).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
          ((deriv (deriv u) (α_sh (π (σ j).1) ⬝ᵥ w + α_aux (π (σ j).1) ⬝ᵥ (σ j).2) +
              deriv u (α_sh (π (σ j).1) ⬝ᵥ w + α_aux (π (σ j).1) ⬝ᵥ (σ j).2) *
                deriv u (α_sh (π (σ j).1) ⬝ᵥ w + α_aux (π (σ j).1) ⬝ᵥ (σ j).2)) *
            ∏ r_u ∈ Finset.univ.erase j,
              deriv u (α_sh (π (σ r_u).1) ⬝ᵥ w + α_aux (π (σ r_u).1) ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
          (fun q_1 => u (α_sh (π q_1.1) ⬝ᵥ w + α_aux (π q_1.1) ⬝ᵥ q_1.2))) ∂γ_sh) = 0 := by
    rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
    refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun w => ?_)).trans
      (integral_zero _ ℝ)
    refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun σ => ?_)).trans
      (integral_zero _ ℝ)
    dsimp only
    simp only [↓reduceIte, hcov_diag (π (σ ()).1)]
    ring
  rw [hdiag_zero, zero_sub, Fintype.card_unique, Nat.cast_one, one_mul]
  symm
  rw [neg_mul, ← integral_const_mul, neg_inj]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  dsimp only
  simp only [Finset.univ_unique, Finset.prod_singleton, hcov_sh]
  ring

/-- **Stein identity at fixed old disorder for the last constraint of (2.82).** For a fixed
`M`-constraint disorder `ω₀`, Gaussian integration by parts over the last constraint's shared
Gaussian `(g_M, z_M)` and auxiliary Gaussian `ξ_M` turns the single-replica derivative term into
`-(1 / 2)` times the overlap-weighted two-replica term; the diagonal covariance vanishes. -/
private theorem interp_field_deriv_stein_fixed_disorder
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
    let μ₀_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E₀ (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k' i * ((x₀.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k' + Real.sqrt (1 - q) * x₀.2 k'))) +
      ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r
    let μ₀ := μ₀_base.tilted E₀
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
    ∫ w, ∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        1 * (W_sh (σ ()).1.1 ⬝ᵥ w + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ w + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2))) ∂γ_sh =
      -(1 / 2) * ∫ w, ∫ σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
            (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
          deriv u (α_sh (σ (some ())).1.1 ⬝ᵥ w + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (σ none).1.1 ⬝ᵥ w + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2))) ∂γ_sh := by
  intro μ₀_base E₀ μ₀ γ_sh γ_aux α_sh W_sh α_aux W_aux
  have hE₀_m : Measurable E₀ := by
    refine (Finset.measurable_sum _ fun k' _ => hu.measurable.comp ?_).add ?_
    · refine (((Finset.measurable_sum _ fun i _ =>
        measurable_const.mul (measurable_units_cast.comp
          ((measurable_pi_apply i).comp measurable_fst))).const_mul _).const_mul _).add
        ((measurable_const.add
          (((measurable_pi_apply k').comp measurable_snd).const_mul _)).const_mul _)
    · exact Finset.measurable_sum _ fun i _ =>
        (((measurable_units_cast.comp
          ((measurable_pi_apply i).comp measurable_fst)).mul_const _).mul_const _).mul_const _
  have hμ₀_prob : IsProbabilityMeasure μ₀ :=
    isProbabilityMeasure_tilted_of_ae_le hE₀_m.aemeasurable
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω₀))
  exact stein_tilted_unit_replica_deriv μ₀ Prod.fst measurable_fst α_sh W_sh α_aux W_aux hu
    (fun τ₁ τ₂ => (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) - q)
    (interp_stein_cov_shared hs hq.1) (interp_stein_cov_diag hs hq)

/-- **Measurability of the split Stein integrands for (2.82).** -/
lemma measurable_interp_stein_split
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (q r s : ℝ) :
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
    Measurable I_L ∧ Measurable I_R := by
  intro μ₀_base E₀ μ₀ γ_aux α_sh W_sh α_aux W_aux I_L I_R
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu s q r
  have hE₀i_all (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x₀ => Real.exp (E₀ ω₀ x₀)) μ₀_base :=
    integrable_exp_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable
      (ae_of_all _ (interpEnergy_le hB s q r ω₀))
  let V_split (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ))
      (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
    u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)
  have hV_split_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
      (((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) => V_split q_p.1 q_p.2 := by
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
      exact measurable_const.mul
        ((measurable_pi_apply ()).comp (measurable_snd.comp measurable_snd))
    exact hu.comp (hd1.add hd2)
  refine ⟨?_, ?_⟩
  · let F_L (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ))
        (σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
      1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
    have hG_m : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) => F_L q_p.1 q_p.2 := by
      dsimp only [F_L]
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      have h_ev : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) => q_p.2 () :=
        (measurable_pi_apply ()).comp measurable_snd
      have hw1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          W_sh (q_p.2 ()).1.1 ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have hw_idx := (measurable_of_finite fun τ => W_sh τ idx).comp
          (measurable_fst.comp (measurable_fst.comp h_ev))
        exact hw_idx.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have hw2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          W_aux (q_p.2 ()).1.1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      have ha1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_sh (q_p.2 ()).1.1 ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have ha_idx := (measurable_of_finite fun τ => α_sh τ idx).comp
          (measurable_fst.comp (measurable_fst.comp h_ev))
        exact ha_idx.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_aux (q_p.2 ()).1.1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      exact (hw1.add hw2).mul ((measurable_deriv u).comp (ha1.add ha2))
    exact measurable_integral_pi_tilted_prod_tilted μ₀_base γ_aux hEm_joint hE₀i_all hV_split_m hG_m
  · have hfl_o (o : Option Unit) : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
        deriv u (α_sh (q_p.2 o).1.1 ⬝ᵥ q_p.1.2 + α_aux (q_p.2 o).1.1 ⬝ᵥ (q_p.2 o).2) := by
      have h_ev : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) => q_p.2 o :=
        (measurable_pi_apply o).comp measurable_snd
      have ha1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_sh (q_p.2 o).1.1 ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have ha_idx := (measurable_of_finite fun τ => α_sh τ idx).comp
          (measurable_fst.comp (measurable_fst.comp h_ev))
        exact ha_idx.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          α_aux (q_p.2 o).1.1 ⬝ᵥ (q_p.2 o).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      exact (measurable_deriv u).comp (ha1.add ha2)
    have hR_o : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
          ((((q_p.2 (some ())).1.1 i : ℤ) : ℝ) * (((q_p.2 none).1.1 i : ℤ) : ℝ))) - q) := by
      have h_some : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          (q_p.2 (some ())).1.1 :=
        measurable_fst.comp (measurable_fst.comp
          ((measurable_pi_apply (some ())).comp measurable_snd))
      have h_none : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) =>
          (q_p.2 none).1.1 :=
        measurable_fst.comp (measurable_fst.comp
          ((measurable_pi_apply none).comp measurable_snd))
      refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const _
      exact (measurable_units_cast.comp ((measurable_pi_apply i).comp h_some)).mul
        (measurable_units_cast.comp ((measurable_pi_apply i).comp h_none))
    exact measurable_integral_pi_tilted_prod_tilted μ₀_base γ_aux hEm_joint hE₀i_all hV_split_m
      ((hR_o.mul (hfl_o (some ()))).mul (hfl_o none))

/-- **Measurability and product-disorder integrability of the split Stein integrands for
(2.82).** -/
private lemma measurable_and_integrable_interp_stein_split
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r s : ℝ) :
    let P₀ :=
      (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
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
    Measurable I_L ∧ Measurable I_R ∧ Integrable I_L (P₀.prod γ_sh) ∧
      Integrable I_R (P₀.prod γ_sh) := by
  intro P₀ μ₀_base E₀ μ₀ γ_sh γ_aux α_sh W_sh α_aux W_aux I_L I_R
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hE₀i_all (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x₀ => Real.exp (E₀ ω₀ x₀)) μ₀_base :=
    integrable_exp_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω₀))
  let V_split (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ))
      (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
    u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)
  obtain ⟨hIL_m, hIR_m⟩ :=
    measurable_interp_stein_split (N := N) (M := M) hu.measurable (fun x => hu.le x) q r s
  have hVp_m_all (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) :
      Measurable (V_split p) := by
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
  have hIR_int : Integrable I_R (P₀.prod γ_sh) := by
    refine Integrable.of_bound hIR_m.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun p => ?_)
    have hμ₀_p : IsProbabilityMeasure (μ₀ p.1) := isProbabilityMeasure_tilted (hE₀i_all p.1)
    have hprob_p : IsProbabilityMeasure (((μ₀ p.1).prod γ_aux).tilted (V_split p)) :=
      isProbabilityMeasure_tilted_of_ae_le (hVp_m_all p).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun σ => by
      rw [abs_mul, abs_mul, sq]
      have hd_ov := abs_spin_overlap_sub_le_two hq (σ (some ())).1.1 (σ none).1.1
      calc _ ≤ 2 * |D₁| * |D₁| :=
            mul_le_mul (mul_le_mul hd_ov (hu.abs_deriv_le_abs _)
              (abs_nonneg _) zero_le_two) (hu.abs_deriv_le_abs _)
              (abs_nonneg _) (by positivity)
        _ = 2 * (|D₁| * |D₁|) := by ring
  have hIL_int : Integrable I_L (P₀.prod γ_sh) := by
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
    have hμ₀_p : IsProbabilityMeasure (μ₀ p.1) := isProbabilityMeasure_tilted (hE₀i_all p.1)
    let V_p := V_split p
    have hVp_m : Measurable V_p := hVp_m_all p
    have hprob_ν : IsProbabilityMeasure (((μ₀ p.1).prod γ_aux).tilted V_p) :=
      isProbabilityMeasure_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
    have hpt_bd (σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) :
        |1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))| ≤
        |D₁| * (c_sh * (∑ idx, |p.2 idx|) + c_aux * |(σ ()).2 ()|) := by
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      rw [abs_mul, mul_comm _ |deriv u _|]
      refine mul_le_mul (hu.abs_deriv_le_abs _) ?_ (abs_nonneg _) (abs_nonneg D₁)
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
          rw [MeasureTheory.tilted_zero]
          exact integrable_comp_eval (μ := fun _ : Unit => (μ₀ p.1).prod γ_aux) (i := ()) hη_int)
      rw [MeasureTheory.tilted_zero] at hd0
      simp only [Fintype.card_unique, Nat.cast_one, mul_one] at hd0
      have hu1 : (∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ), |(σ ()).2 ()|
          ∂(Measure.pi fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted V_p)) =
          ∫ y, |y.2 ()| ∂(((μ₀ p.1).prod γ_aux).tilted V_p) :=
        (measurePreserving_funUnique (((μ₀ p.1).prod γ_aux).tilted V_p)
          Unit).integral_comp_of_aestronglyMeasurable
          (g := fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) => |y.2 ()|)
          ((measurable_pi_apply ()).comp measurable_snd).norm.aestronglyMeasurable
      have hu2 : (∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ), |(σ ()).2 ()|
          ∂(Measure.pi fun _ : Unit => (μ₀ p.1).prod γ_aux)) =
          ∫ y, |y.2 ()| ∂((μ₀ p.1).prod γ_aux) :=
        (measurePreserving_funUnique ((μ₀ p.1).prod γ_aux)
          Unit).integral_comp_of_aestronglyMeasurable
          (g := fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) => |y.2 ()|)
          ((measurable_pi_apply ()).comp measurable_snd).norm.aestronglyMeasurable
      have h_snd := integral_prod_fun_snd_of_isProbabilityMeasure (μ := μ₀ p.1) (ν := γ_aux)
        (fun η : Unit → ℝ => |η ()|)
      rw [hu1, hu2, h_snd] at hd0
      exact hd0
    rw [h2] at h1
    refine h1.trans ?_
    dsimp only [dom_p]
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (abs_nonneg D₁)
    calc c_aux * ∫ y, |y.2 ()| ∂(((μ₀ p.1).prod γ_aux).tilted V_p)
        ≤ c_aux * (Real.exp (2 * |B|) * ∫ η, |η ()| ∂γ_aux) :=
          mul_le_mul_of_nonneg_left hdom_y hc_aux0
      _ = Real.exp (2 * |B|) * (c_aux * ∫ η, |η ()| ∂γ_aux) := by ring
  exact ⟨hIL_m, hIR_m, hIL_int, hIR_int⟩

/-- **Last-constraint Gaussian IBP and measure transport for (2.82).** Splitting `(M + 1)`
constraints into the `M` old constraints and `Fin.last M`, transporting the disorder and state,
and applying `interp_field_deriv_stein_fixed_disorder` yields Eq. (2.82) at `Fin.last M`. -/
private theorem integral_interpolating_field_deriv_ibp_last
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (k' : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let S'_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (k' : Fin (M + 1)) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ k' : Fin (M + 1), u (S_fn ω x k')) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)) ∂(μ_s.tilted (E_s ω)) ∂P =
      -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P := by
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s
  have hEm_joint {M' : ℕ} :=
    measurable_interpEnergy_joint (L := N + 1) (M := M') hu.measurable s q r
  let P₀ :=
    (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
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
  obtain ⟨hIL_m, hIR_m, hIL_int, hIR_int⟩ :=
    measurable_and_integrable_interp_stein_split (N := N) (M := M) hu hq r s
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
  let e_opt2 : Option Unit ≃ Fin 2 :=
    { toFun := fun o => match o with | some () => 0 | none => 1
      invFun := fun i => if i = 0 then some () else none
      left_inv := fun o => by cases o <;> simp
      right_inv := fun i => by fin_cases i <;> simp }
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
    rw [interpStateLastSplit_apply]; rfl
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
    have h1 : (∑ i : Fin (N + 1),
        Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i) =
      ∑ i : Fin (N + 1),
        Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          (ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ))) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
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
    dsimp only [Function.comp_apply]
    rw [MeasurableEquiv.symm_apply_apply, hS_last_eq ω x, he_st_apply]
    dsimp only [E_s, E₀, splitΩ, S_fn]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.init_def]
    ring
  have hIL_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      I_L (splitΩ ω) =
        ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)) ∂(μ_s.tilted (E_s ω)) := by
    let ν_ω := μ_s.tilted (E_s ω)
    have hprob_ω : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
    let g_L (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M))
    have hg_Lm : Measurable g_L := by
      have hS_x : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          S_fn ω x (Fin.last M) := by dsimp only [S_fn]; fun_prop
      have hS'_x : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          S'_fn ω x (Fin.last M) := by dsimp only [S'_fn]; fun_prop
      exact hS'_x.mul ((measurable_deriv u).comp hS_x)
    let F_split_L (σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
      1 * (W_sh (σ ()).1.1 ⬝ᵥ (splitΩ ω).2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit,
          deriv u (α_sh (σ r_u).1.1 ⬝ᵥ (splitΩ ω).2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
    have ht1 : I_L (splitΩ ω) =
        ∫ f_u : Unit → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          F_split_L (fun r_u => e_st (f_u r_u)) ∂(Measure.pi fun _ : Unit => ν_ω) := by
      dsimp only [I_L, F_split_L, ν_ω]
      rw [← htilted_st ω]
      exact integral_pi_map_equiv (μ_s.tilted (E_s ω)) e_st F_split_L
    have ht2 : ∀ f_u : Unit → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        F_split_L (fun r_u => e_st (f_u r_u)) = g_L (f_u ()) := fun f_u => by
      dsimp only [F_split_L, g_L]
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      rw [hS_last_eq ω (f_u ()), hS'_last_eq ω (f_u ())]
    have h_u := (measurePreserving_funUnique ν_ω Unit).integral_comp_of_aestronglyMeasurable
      (g := g_L) hg_Lm.aestronglyMeasurable
    rw [ht1]
    exact (integral_congr_ae (ae_of_all _ ht2)).trans h_u
  have hIR_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      I_R (splitΩ ω) =
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
    let ν_ω := μ_s.tilted (E_s ω)
    have hprob_ω : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
    let G₂ (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
    have hG2_m : Measurable G₂ := by
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
    let F_split_R (σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
        deriv u
          (α_sh (σ (some ())).1.1 ⬝ᵥ (splitΩ ω).2 + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1.1 ⬝ᵥ (splitΩ ω).2 + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
    have ht1 : I_R (splitΩ ω) =
        ∫ τ_o : Option Unit → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          F_split_R (fun o => e_st (τ_o o)) ∂(Measure.pi fun _ : Option Unit => ν_ω) := by
      dsimp only [I_R, F_split_R, ν_ω]
      rw [← htilted_st ω]
      exact integral_pi_map_equiv (μ_s.tilted (E_s ω)) e_st F_split_R
    let e_pi := MeasurableEquiv.piCongrLeft
      (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) e_opt2
    have hmp_opt2 : MeasurePreserving ⇑e_pi
        (Measure.pi fun _ : Option Unit => ν_ω) (Measure.pi fun _ : Fin 2 => ν_ω) :=
      measurePreserving_piCongrLeft (fun _ : Fin 2 => ν_ω) e_opt2
    have h_opt := hmp_opt2.integral_comp_of_aestronglyMeasurable hG2_m.aestronglyMeasurable
    have ht2 : ∀ τ_o : Option Unit → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        F_split_R (fun o => e_st (τ_o o)) = (G₂ ∘ ⇑e_pi) τ_o := fun τ_o => by
      have h0 : e_pi τ_o 0 = τ_o (some ()) := by
        change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ))
          e_opt2 τ_o) 0 = _
        rw [Equiv.piCongrLeft_apply]; rfl
      have h1 : e_pi τ_o 1 = τ_o none := by
        change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ))
          e_opt2 τ_o) 1 = _
        rw [Equiv.piCongrLeft_apply]; rfl
      dsimp only [F_split_R, G₂, Function.comp_apply]
      rw [h0, h1, hS_last_eq ω (τ_o (some ())), hS_last_eq ω (τ_o none),
        he_st_apply (τ_o (some ())), he_st_apply (τ_o none)]
    rw [ht1]
    exact (integral_congr_ae (ae_of_all _ ht2)).trans h_opt
  have hlhs_eq : (∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)) ∂(μ_s.tilted (E_s ω)) ∂P) =
      ∫ p, I_L p ∂(P₀.prod γ_sh) :=
    (integral_congr_ae (ae_of_all _ fun ω => (hIL_split ω).symm)).trans
      (hmp_dis.integral_comp_of_aestronglyMeasurable hIL_m.aestronglyMeasurable)
  have hrhs_eq : (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P) =
      ∫ p, I_R p ∂(P₀.prod γ_sh) :=
    (integral_congr_ae (ae_of_all _ fun ω => (hIR_split ω).symm)).trans
      (hmp_dis.integral_comp_of_aestronglyMeasurable hIR_m.aestronglyMeasurable)
  rw [hlhs_eq, hrhs_eq, integral_prod I_L hIL_int, integral_prod I_R hIR_int,
    ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun ω₀ =>
    interp_field_deriv_stein_fixed_disorder (N := N) (M := M) hu hq r hs ω₀)

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
  have hEm_joint : Measurable fun p :
      (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => E_s p.1 p.2 :=
    measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu.measurable s q r
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
    have hΦ_m (k' : Fin (M + 1)) : Measurable (Φ_l k') :=
      measurable_integral_tilted_dep hEm_joint
        ((measurable_interpFieldDeriv_joint (L := N + 1) (M := M + 1) s q k').mul
          ((measurable_deriv u).comp
            (measurable_interpField_joint (L := N + 1) (M := M + 1) s q k')))
    have hpt_sw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        Φ_l (Fin.last M) (interpConstraintDisorderSwap k (Fin.last M) ω) = Φ_l k ω := by
      dsimp only [Φ_l]
      rw [htilted_swap k (Fin.last M) ω, integral_map_equiv]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only [Function.comp_apply, S_fn, S'_fn, interpConstraintDisorderSwap]
      simp [interpConstraintStateSwap_apply]
    have hmp := measurePreserving_interpConstraintDisorderSwap (L := N + 1) k (Fin.last M)
    exact (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans
      (hmp.integral_comp_of_aestronglyMeasurable (hΦ_m (Fin.last M)).aestronglyMeasurable)
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
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => S_fn p.1 (p.2 l) k' :=
        (measurable_interpField_joint (L := N + 1) (M := M + 1) s q k').comp
          (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
      have hR_m : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          (((N : ℝ) + 1)⁻¹ * ∑ i, ((((p.2 0).1 i : ℤ) : ℝ) * (((p.2 1).1 i : ℤ) : ℝ))) - q := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const _
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))))
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
    exact (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans
      (hmp.integral_comp_of_aestronglyMeasurable (hΨ_m (Fin.last M)).aestronglyMeasurable)
  rw [hlhs_swap, hrhs_swap]
  exact integral_interpolating_field_deriv_ibp_last hu hq r hs

/-- **Linearity split of the raw `s`-interpolating pressure derivative (2.81)** into the sum over
constraints `k` of `ν_s(S'_{k, s} u'(S_{k, s}))` minus the external-field expectation. -/
private theorem integral_interpolating_pressure_deriv_split
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (q r s : ℝ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let S'_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (S_fn ω x k)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ((N : ℝ) + 1)⁻¹ * (∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω)) ∂P) =
      ((N : ℝ) + 1)⁻¹ * (∑ k : Fin M,
        ∫ ω, ∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω)) ∂P) -
      ((N : ℝ) + 1)⁻¹ *
        ∫ ω, ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s ω)) ∂P := by
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s
  have hEm_joint : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E_s p.1 p.2 :=
    measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
  have hpt_x (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (k : Fin M) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      |S'_fn ω x k * deriv u (S_fn ω x k)| ≤
        |D₁| * ((1 / (2 * Real.sqrt s)) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
          (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|)) +
        |D₁| * ((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)) * |x.2 k| := by
    rw [abs_mul, mul_comm _ |deriv u _|]
    have hd_b : |deriv u (S_fn ω x k)| ≤ |D₁| := (hu.abs_deriv_le _).trans (le_abs_self D₁)
    have hS'_b : |S'_fn ω x k| ≤
        (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
        (1 / (2 * Real.sqrt (1 - s))) *
          (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|) := by
      dsimp only [S'_fn]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul (1 / (2 * Real.sqrt s)), abs_of_nonneg (by positivity),
          abs_mul ((Real.sqrt (N + 1 : ℕ))⁻¹), abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_units_cast_eq_one, mul_one])) (by positivity)) (by positivity)
      · rw [abs_mul (1 / (2 * Real.sqrt (1 - s))), abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left
          ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |deriv u (S_fn ω x k)| * |S'_fn ω x k|
        ≤ |D₁| * ((1 / (2 * Real.sqrt s)) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
          (1 / (2 * Real.sqrt (1 - s))) *
            (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|)) :=
          mul_le_mul hd_b hS'_b (abs_nonneg _) (abs_nonneg D₁)
      _ = _ := by ring
  have hS'_in_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (k : Fin M) :
      Integrable (fun x => S'_fn ω x k * deriv u (S_fn ω x k)) (μ_s.tilted (E_s ω)) := by
    have hm : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        S'_fn ω x k * deriv u (S_fn ω x k) := by
      have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S'_fn ω x k := by
        dsimp only [S'_fn]; fun_prop
      have h2 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S_fn ω x k := by
        dsimp only [S_fn]; fun_prop
      exact h1.mul ((measurable_deriv u).comp h2)
    have hξ_k : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|) μ_s :=
      (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
        IsGaussian.integrable_id.abs).comp_snd _
    exact integrable_tilted_of_abs_le_envelope
      (Measurable.of_uncurry_left hEm_joint).aemeasurable hm.aestronglyMeasurable
      ((integrable_const _).add (hξ_k.const_mul _))
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
      (ae_of_all _ (hpt_x ω k))
  have hS'_in_P (k : Fin M) :
      Integrable (fun ω =>
        ∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) P := by
    have hm_k : Measurable fun ω => ∫ x, S'_fn ω x k * deriv u (S_fn ω x k)
        ∂(μ_s.tilted (E_s ω)) :=
      measurable_integral_tilted_dep hEm_joint
        ((measurable_interpFieldDeriv_joint (L := N + 1) (M := M) s q k).mul
          ((measurable_deriv u).comp (measurable_interpField_joint (L := N + 1) (M := M) s q k)))
    let c1 : ℝ := |D₁| * ((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q))
    let dom_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      |D₁| * ((1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|)) +
      Real.exp (2 * M * |B|) *
        (c1 * ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1))
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
        (μ_s.tilted (E_s ω)) :=
      integrable_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm_joint).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω)) hξ_k
    have h1 := (abs_integral_le_integral_abs).trans
      (integral_mono (hS'_in_pt ω k).abs
        (f := fun x => |S'_fn ω x k * deriv u (S_fn ω x k)|)
        (g := fun x => c0_ω + c1 * |x.2 k|)
        ((integrable_const c0_ω).add (hξ_t.const_mul c1)) (hpt_x ω k))
    rw [integral_add (integrable_const c0_ω) (hξ_t.const_mul c1), integral_const, probReal_univ,
      one_smul, integral_const_mul] at h1
    refine h1.trans (add_le_add le_rfl ?_)
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
      (E₀ := E0_sp) (E₁ := E_s ω) hi0
      ((Measurable.of_uncurry_left hEm_joint).sub hE0_m) (C := M * |B|)
      (fun x => by
        have heq_s : E_s ω x - E0_sp x = ∑ k', u (S_fn ω x k') := by
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
        ∂(Measure.pi fun _ : Unit => μ_s.tilted (E_s ω))) =
        ∫ y, |y.2 k| ∂(μ_s.tilted (E_s ω)) :=
      (measurePreserving_funUnique (μ_s.tilted (E_s ω))
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
    calc c1 * ∫ x, |x.2 k| ∂(μ_s.tilted (E_s ω))
        ≤ c1 * (Real.exp (2 * M * |B|) *
            ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1)) :=
          mul_le_mul_of_nonneg_left hd_e hc1_0
      _ = Real.exp (2 * M * |B|) *
            (c1 * ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1)) := by ring
  have hext_in_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        (1 / (2 * Real.sqrt (1 - s))) *
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        (μ_s.tilted (E_s ω)) := by
    have := hprob_ω ω
    exact Integrable.of_bound (by fun_prop)
      ((1 / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul (1 / (2 * Real.sqrt (1 - s))),
          abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
            abs_of_nonneg (Real.sqrt_nonneg _)]))
  have hext_in_P :
      Integrable (fun ω => ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) P := by
    have hg_e : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
        (1 / (2 * Real.sqrt (1 - s))) *
          ∑ i : Fin (N + 1), ((p.2.1 i : ℤ) : ℝ) * p.1.2 i * Real.sqrt r := by
      refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
      exact ((measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))).mul
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))).mul_const _
    have hm_e : Measurable fun ω => ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r) ∂(μ_s.tilted (E_s ω)) :=
      measurable_integral_tilted_dep hEm_joint hg_e
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
          rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
            abs_of_nonneg (Real.sqrt_nonneg _)]))
        (by positivity)
  have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) =
      (∑ k : Fin M, ∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) -
        ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s ω)) := by
    rw [integral_sub (integrable_finsetSum _ fun k _ => hS'_in_pt ω k) (hext_in_pt ω),
      integral_finsetSum _ fun k _ => hS'_in_pt ω k]
  simp_rw [hpt]
  rw [integral_sub (integrable_finsetSum _ fun k _ => hS'_in_P k) hext_in_P,
    integral_finsetSum _ fun k _ => hS'_in_P k, mul_sub]

/-- **Regrouped derivative formula for the `s`-interpolating pressure (Eq. (2.83)):**
for `s ∈ (0, 1)`, `q ∈ [0, 1]`, `r ≥ 0`, and `u` satisfying `SmartPathPotential₂`,
`d/ds p_{N+1, M, s}(u) = -(r / 2)(1 - q)`
`- (1 / 2) ν_s((R_{1,2} - q)((N + 1)⁻¹ ∑ₖ u'(S¹_{k,s}) u'(S²_{k,s}) - r))`. -/
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
  have hlhs_split := integral_interpolating_pressure_deriv_split (N := N) (M := M) hu q r s
  have hext_ibp :=
    integral_interpolating_external_field_ibp (N := N) (M := M) hu.measurable hu.abs_le q hr0 hs.2
  have hfield_ibp (k : Fin M) :=
    integral_interpolating_field_deriv_ibp (N := N) (M := M) hu hq r hs k
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
    have h1 : ((N : ℝ) + 1)⁻¹ * (∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn s ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s s ω)) ∂P) =
      ((N : ℝ) + 1)⁻¹ * (∑ k : Fin M,
        ∫ ω, ∫ x, S'_fn ω x k * deriv u (S_fn s ω x k) ∂(μ_s.tilted (E_s s ω)) ∂P) -
      ((N : ℝ) + 1)⁻¹ *
        ∫ ω, ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s s ω)) ∂P := hlhs_split
    have h2 : ((N : ℝ) + 1)⁻¹ *
        ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (1 / (2 * Real.sqrt (1 - s))) *
            (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s s ω)) ∂P =
      (r / 2) * (1 - ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) := hext_ibp
    have h3 (k : Fin M) :
        ∫ ω, ∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          S'_fn ω x k * deriv u (S_fn s ω x k) ∂(μ_s.tilted (E_s s ω)) ∂P =
        -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P := hfield_ibp k
    rw [h1, h2, Finset.sum_congr rfl fun k _ => h3 k]
  -- Combine the sum over `k` and the `(r / 2)(1 - ν_s(R_{1,2}))` term into the regrouped RHS!
  let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
  have hR_obs_m : Measurable R_obs := by
    refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
    have h0 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        (((σ 0).1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 0)))
    have h1 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        (((σ 1).1 i : ℤ) : ℝ) :=
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
  have hd2_bd (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |R_obs σ - q| ≤ 2 := by
    have h := abs_sub (R_obs σ) q
    rw [abs_of_nonneg hq.1] at h; linarith [hR_obs_b σ, hq.2]
  let g_k (k : Fin M) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ *
      ((R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k))
  have hgk_bd (k : Fin M) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      |g_k k ω σ| ≤ ((N : ℝ) + 1)⁻¹ * (2 * |D₁| ^ 2) := by
    dsimp only [g_k]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_mul, abs_mul, sq]
    calc _ ≤ 2 * |D₁| * |D₁| :=
          mul_le_mul (mul_le_mul (hd2_bd σ) ((hu.abs_deriv_le _).trans (le_abs_self D₁))
            (abs_nonneg _) zero_le_two) ((hu.abs_deriv_le _).trans (le_abs_self D₁))
            (abs_nonneg _) (by positivity)
      _ = 2 * (|D₁| * |D₁|) := by ring
  have hgk_in (k : Fin M) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (g_k k ω) (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) := by
    have := hprob_ω ω
    have hS_l (l : Fin 2) : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        S_fn s ω (σ l) k := by dsimp only [S_fn]; fun_prop
    have hm_gk : Measurable (g_k k ω) :=
      measurable_const.mul ((((hR_obs_m.sub_const q).mul ((measurable_deriv u).comp (hS_l 0))).mul
        ((measurable_deriv u).comp (hS_l 1))))
    exact Integrable.of_bound hm_gk.aestronglyMeasurable
      (((N : ℝ) + 1)⁻¹ * (2 * |D₁| ^ 2))
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hgk_bd k ω σ)
  have hμ_fin : IsFiniteMeasure μ_s := inferInstance
  have hgk_out (k : Fin M) : Integrable
      (fun ω => ∫ σ, g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) P := by
    have hS_l (l : Fin 2) : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => S_fn s p.1 (p.2 l) k :=
      measurable_interpField_replica_joint (L := N + 1) (M := M) s q k l
    have hgk_joint : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => g_k k p.1 p.2 :=
      measurable_const.mul ((((hR_obs_m.comp measurable_snd).sub_const q).mul
        ((measurable_deriv u).comp (hS_l 0))).mul ((measurable_deriv u).comp (hS_l 1)))
    have hm : Measurable fun ω =>
        ∫ σ, g_k k ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) :=
      @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint (g_k k) hgk_joint
    exact Integrable.of_bound hm.aestronglyMeasurable (((N : ℝ) + 1)⁻¹ * (2 * |D₁| ^ 2))
      (ae_of_all _ fun ω => by
        have := hprob_ω ω
        rw [Real.norm_eq_abs]; exact abs_integral_le_of_forall_abs_le _ (hgk_bd k ω))
  let g_sum (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := ∑ k : Fin M, g_k k ω σ
  let g_r (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := r * (R_obs σ - q)
  have hgr_in (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable g_r (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) := by
    have := hprob_ω ω
    exact Integrable.of_bound (measurable_const.mul (hR_obs_m.sub_const q)).aestronglyMeasurable
      (|r| * 2) (ae_of_all _ fun σ => by
        dsimp only [g_r]; rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hd2_bd σ) (abs_nonneg r))
  have hgr_out :
      Integrable (fun ω => ∫ σ, g_r σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) P := by
    let G_r (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := g_r σ
    have hm : Measurable fun ω =>
        ∫ σ, G_r ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) :=
      @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint G_r
        (measurable_const.mul ((hR_obs_m.comp measurable_snd).sub_const q))
    exact Integrable.of_bound hm.aestronglyMeasurable (|r| * 2) (ae_of_all _ fun ω => by
      have := hprob_ω ω
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun σ => by
        dsimp only [G_r, g_r]; rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hd2_bd σ) (abs_nonneg r))
  have hsum_eq := integral_integral_finset_sum_dep P
    (fun ω => Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) Finset.univ g_k
    (fun k _ ω => hgk_in k ω) (fun k _ => hgk_out k)
  have hrhs_expand :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (R_obs σ - q) *
          ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
            deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) =
      (∑ k : Fin M, ((N : ℝ) + 1)⁻¹ * ∫ ω, ∫ σ,
        (R_obs σ - q) * deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) -
      r * ((∫ ω, ∫ σ, R_obs σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P) - q) := by
    have hpt_sub (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (∫ σ, (R_obs σ - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
              deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) =
        (∫ σ, g_sum ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) -
          ∫ σ, g_r σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) := by
      have halg (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
          (R_obs σ - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
              deriv u (S_fn s ω (σ 0) k) * deriv u (S_fn s ω (σ 1) k)) - r) =
          g_sum ω σ - g_r σ := by
        dsimp only [g_sum, g_k, g_r]
        rw [mul_sub, ← mul_assoc, mul_comm (R_obs σ - q) (((N : ℝ) + 1)⁻¹), mul_assoc,
          Finset.mul_sum, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun _ _ => by ring
        · ring
      simp_rw [halg]
      exact integral_sub (integrable_finsetSum _ fun k _ => hgk_in k ω) (hgr_in ω)
    simp_rw [hpt_sub]
    have hgsum_out : Integrable
        (fun ω => ∫ σ, g_sum ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) P :=
      (integrable_finsetSum Finset.univ fun k _ => hgk_out k).congr
        (ae_of_all _ fun ω => (integral_finsetSum Finset.univ fun k _ => hgk_in k ω).symm)
    rw [integral_sub hgsum_out hgr_out]
    dsimp only [g_sum]
    rw [hsum_eq]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [g_k]
      simp_rw [integral_const_mul]
    · have hR_in_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
          Integrable R_obs (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) := by
        have := hprob_ω ω
        exact Integrable.of_bound hR_obs_m.aestronglyMeasurable 1
          (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hR_obs_b σ)
      have hR_out_P : Integrable
          (fun ω => ∫ σ, R_obs σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) P := by
        let G_R (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := R_obs σ
        have hm : Measurable fun ω =>
            ∫ σ, G_R ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) :=
          @measurable_integral_pi_tilted _ _ _ _ μ_s hμ_fin _ _ (E_s s) hEm_joint G_R
            (hR_obs_m.comp measurable_snd)
        exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          have := hprob_ω ω
          rw [Real.norm_eq_abs]; exact abs_integral_le_of_forall_abs_le _ hR_obs_b)
      have hgr_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
          (∫ σ, g_r σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) =
          r * ((∫ σ, R_obs σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) - q) := by
        have := hprob_ω ω
        dsimp only [g_r]
        rw [integral_const_mul, integral_sub (hR_in_ω ω) (integrable_const q),
          integral_const, probReal_univ, one_smul]
      simp_rw [hgr_pt]
      rw [integral_const_mul, integral_sub hR_out_P (integrable_const q),
        integral_const, probReal_univ, one_smul]
  dsimp only [R_obs] at hrhs_expand
  refine hlhs_ibp.trans ?_
  rw [hrhs_expand, Finset.mul_sum]
  have hsum_neg :
      (∑ x : Fin M, ((N : ℝ) + 1)⁻¹ * (-(1 / 2) * ∫ ω, ∫ σ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn s ω (σ 0) x) * deriv u (S_fn s ω (σ 1) x)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P)) =
      -(1 / 2) * ∑ x : Fin M, ((N : ℝ) + 1)⁻¹ * ∫ ω, ∫ σ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn s ω (σ 0) x) * deriv u (S_fn s ω (σ 1) x)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsum_neg]
  ring

end DerivativeAndIBP

end SpinGlasses
