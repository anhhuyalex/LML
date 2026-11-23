/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.EmpiricalVariance
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.RSFixedPoint

/-!
# Convergence of the perceptron free energy to the replica-symmetric solution (Theorem 2.4.2)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.74)--(2.75)
and the first proof of Theorem 2.4.2 (via the `s`-interpolating Hamiltonian).

For `N + 1` spins and `M` constraints with load `α = M / (N + 1)`, the replica-symmetric functional
(Eq. (2.74) and the three-variable functional `F(α, r, q)` before Lemma 2.4.4) is
$$F(\alpha, r, q) = -\frac{1}{2}\,r(1 - q) + \mathbb{E}\log\bigl(2\cosh(z\sqrt{r})\bigr) +
  \alpha\,\mathbb{E}\log\mathbb{E}_\xi \exp u\bigl(\sqrt{q}\,z + \sqrt{1 - q}\,\xi\bigr).$$

## Main declarations

* `SpinGlasses.perceptronRSFunctional`: the three-variable replica-symmetric functional `F(α, r, q)`
  of Eq. (2.74) and Lemma 2.4.4.
* `SpinGlasses.abs_deriv_interpolating_pressure_add_le`: uniform `O(1 / (N + 1))` bound on
  `|p'_{N+1, M, s}(u) + (r / 2)(1 - q)|` on `s ∈ (0, 1)` by combining Eq. (2.84), Eq. (2.80), and
  Lemma 2.4.3 (Eq. (2.85)).
* `SpinGlasses.abs_perceptron_pressure_sub_rs_free_energy_le`: Theorem 2.4.2 for any solution
  `(q, r)` of the fixed-point system (2.68).
* `SpinGlasses.exists_unique_rs_fixed_point_and_abs_pressure_sub_le`: unconditional source-facing
  Theorem 2.4.2 combined with Theorem 2.4.1 under a single small-load condition `α * K(D) ≤ 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

/-- **The replica-symmetric functional `F(α, r, q)` for the Gaussian binary perceptron**
(Talagrand, Eq. (2.74) and Lemma 2.4.4):
`F(α, r, q) = -(1 / 2) r (1 - q) + 𝔼 log(2 cosh(z √r)) + α 𝔼 log 𝔼_ξ exp u(√q z + √(1 - q) ξ)`.
This is a definition because it is the object evaluated in Theorem 2.4.2 and differentiated with
respect to `r`, `q`, and `α` in Lemma 2.4.4 and Eq. (2.89). -/
noncomputable def perceptronRSFunctional (u : ℝ → ℝ) (α r q : ℝ) : ℝ :=
  -(1 / 2) * r * (1 - q) +
    (∫ z : ℝ, Real.log (2 * Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1) +
    α * ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1

/-- Rewriting `𝔼 log(2 cosh(z √r))` as `log 2 + 𝔼 log cosh(z √r)`. -/
theorem perceptronRSFunctional_eq_log_two_add (u : ℝ → ℝ) (α r q : ℝ) :
    perceptronRSFunctional u α r q =
      -(1 / 2) * r * (1 - q) + Real.log 2 +
        (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1) +
        α * ∫ z : ℝ, Real.log (∫ ξ : ℝ,
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
          ∂gaussianReal 0 1 := by
  unfold perceptronRSFunctional
  have hpt (z : ℝ) :
      Real.log (2 * Real.cosh (z * Real.sqrt r)) =
        Real.log 2 + Real.log (Real.cosh (z * Real.sqrt r)) :=
    Real.log_mul two_ne_zero (Real.cosh_pos _).ne'
  have hint_cosh : Integrable (fun z : ℝ => Real.log (Real.cosh (z * Real.sqrt r)))
      (gaussianReal 0 1) := by
    have heq : (fun z : ℝ => Real.log (Real.cosh (z * Real.sqrt r))) =
        fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z + 0)) := by
      funext z; ring_nf
    rw [heq]
    exact integrable_log_cosh_affine_gaussianReal (Real.sqrt r) 0
  simp_rw [hpt]
  rw [integral_add (integrable_const (Real.log 2)) hint_cosh, integral_const, probReal_univ,
    one_smul]
  ring

/-- **Uniform `O(1 / (N + 1))` bound on `|p'_{N+1, M, s}(u) + (r / 2)(1 - q)|` along `s ∈ (0, 1)`.**
Combines Cauchy-Schwarz Eq. (2.84) (`abs_deriv_interpolating_pressure_add_le_cauchy_schwarz`),
overlap concentration Eq. (2.80) (`integral_interpolating_overlap_sub_sq_le`), and Lemma 2.4.3
Eq. (2.85) (`integral_interpolating_deriv_empirical_variance_le`). -/
theorem abs_deriv_interpolating_pressure_add_le (D : ℝ) :
    ∃ K L_der : ℝ, 0 ≤ K ∧ 0 ≤ L_der ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Ioo (0 : ℝ) 1)
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
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let E_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ k : Fin M, u (Real.sqrt s' *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s') * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
        ∃ d,
          HasDerivAt
            (fun s' => ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s) ∂P) d s ∧
          |d + (r / 2) * (1 - q)| ≤ L_der / ((N : ℝ) + 1) := by
  obtain ⟨K_ov, L_ov, hKov0, hLov0, h_ov⟩ := integral_interpolating_overlap_sub_sq_le D
  obtain ⟨K_var, L_var, hKvar0, hLvar0, h_var⟩ :=
    integral_interpolating_deriv_empirical_variance_le D
  let K : ℝ := max K_ov K_var
  let L_der : ℝ := (1 / 2) * (Real.sqrt L_ov * Real.sqrt L_var)
  refine ⟨K, L_der, le_max_of_le_left hKov0, by positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr P_g P_z P_z' P μ_s E_s
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hα0 : 0 ≤ (M : ℝ) / ((N : ℝ) + 1) := by positivity
  have hα_ov : (M : ℝ) / ((N : ℝ) + 1) * K_ov ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_max_left K_ov K_var) hα0).trans hα
  have hα_var : (M : ℝ) / ((N : ℝ) + 1) * K_var ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_max_right K_ov K_var) hα0).trans hα
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
    rw [hq]
    have heq : (∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1) =
        ∫ z : ℝ, Real.tanh (1 * Real.sqrt r * z + 0) ^ 2 ∂gaussianReal 0 1 := by
      congr 1; ext z; ring_nf
    rw [heq]
    exact fixedPointMap_mem_Icc 1 0 r
  have hrhat0 : 0 ≤ perceptronRhat u q := perceptronRhat_nonneg u q
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hα0 hrhat0
  have hs_cc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  obtain ⟨d, hd_p, hcs⟩ :=
    abs_deriv_interpolating_pressure_add_le_cauchy_schwarz (N := N) (M := M) hu hq_mem hr0 hs
  refine ⟨d, hd_p, ?_⟩
  have hb_ov := h_ov N M hs_cc hd hb hα_ov hq hr
  have hb_var := h_var N M hs_cc hd hb hα_var hq hr
  dsimp only at hb_ov hb_var
  let A_ov := ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
    (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q) ^ 2
    ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P
  let B_var := ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
    ((((N : ℝ) + 1)⁻¹ * ∑ k : Fin M,
      deriv u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((((σ 0).1 i : ℤ) : ℝ))) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * (σ 0).2 k)) *
      deriv u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((((σ 1).1 i : ℤ) : ℝ))) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * (σ 1).2 k))) - r) ^ 2
    ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω)) ∂P
  have hA0 : 0 ≤ A_ov := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hB0 : 0 ≤ B_var := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hrpow_A : A_ov ^ (1 / (2 : ℝ)) ≤ Real.sqrt L_ov / Real.sqrt ((N : ℝ) + 1) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_div hLov0]
    exact Real.sqrt_le_sqrt hb_ov
  have hrpow_B : B_var ^ (1 / (2 : ℝ)) ≤ Real.sqrt L_var / Real.sqrt ((N : ℝ) + 1) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_div hLvar0]
    exact Real.sqrt_le_sqrt hb_var
  have hprod_le : A_ov ^ (1 / (2 : ℝ)) * B_var ^ (1 / (2 : ℝ)) ≤
      (Real.sqrt L_ov * Real.sqrt L_var) / ((N : ℝ) + 1) := by
    have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hsq_L : Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) = (N : ℝ) + 1 :=
      Real.mul_self_sqrt hL_pos.le
    calc A_ov ^ (1 / (2 : ℝ)) * B_var ^ (1 / (2 : ℝ))
        ≤ (Real.sqrt L_ov / Real.sqrt ((N : ℝ) + 1)) *
            (Real.sqrt L_var / Real.sqrt ((N : ℝ) + 1)) :=
          mul_le_mul hrpow_A hrpow_B (Real.rpow_nonneg hB0 _) (by positivity)
      _ = (Real.sqrt L_ov * Real.sqrt L_var) /
            (Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1)) := by ring
      _ = (Real.sqrt L_ov * Real.sqrt L_var) / ((N : ℝ) + 1) := by rw [hsq_L]
  refine hcs.trans ?_
  calc (1 / 2) * A_ov ^ (1 / (2 : ℝ)) * B_var ^ (1 / (2 : ℝ))
      = (1 / 2) * (A_ov ^ (1 / (2 : ℝ)) * B_var ^ (1 / (2 : ℝ))) := by ring
    _ ≤ (1 / 2) * ((Real.sqrt L_ov * Real.sqrt L_var) / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hprod_le (by positivity)
    _ = L_der / ((N : ℝ) + 1) := by dsimp only [L_der]; ring

/-- **Talagrand Theorem 2.4.2 (for any solution `(q, r)` of (2.68)):**
Given `D ∈ ℝ`, there exist constants `K(D) ≥ 0` and `C(D) ≥ 0` (chosen before `N, M, u, q, r`) such
that whenever `u` satisfies (2.7), `α = M / (N + 1)` satisfies `α * K(D) ≤ 1`, and `(q, r)` solves
(2.68), the finite-size perceptron pressure `p_{N+1, M}(u)` satisfies
`|p_{N+1, M}(u) - F(α, r, q)| ≤ C(D) / (N + 1)` for every `N, M : ℕ`. -/
theorem abs_perceptron_pressure_sub_rs_free_energy_le (D : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D),
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        α * K ≤ 1 →
        ∀ {q r : ℝ}
          (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
          (_hr : r = α * perceptronRhat u q),
          let P_g := Measure.pi fun _ : Fin M =>
            Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
          let p_NM : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g : Fin M → Fin (N + 1) → ℝ,
            Real.log (∑ τ : Fin (N + 1) → ℤˣ,
              Real.exp (∑ k : Fin M,
                u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ∂P_g
          |p_NM - perceptronRSFunctional u α r q| ≤ C / ((N : ℝ) + 1) := by
  obtain ⟨K, C, hK0, hC0, h_der⟩ := abs_deriv_interpolating_pressure_add_le D
  refine ⟨K, C, hK0, hC0, ?_⟩
  intro N M u hd hb α hα q r hq hr P_g p_NM
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
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
  let p_path (s : ℝ) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∫ ω, Real.log (∫ x, Real.exp (E_s s ω x) ∂μ_s) ∂P
  let φ (s : ℝ) : ℝ := p_path s + s * ((r / 2) * (1 - q))
  have hp_cont : ContinuousOn p_path (Icc 0 1) :=
    continuousOn_interpolating_pressure hu.continuous hu.abs_le q r
  have hφ_cont : ContinuousOn φ (Icc 0 1) :=
    hp_cont.add (continuousOn_id.mul continuousOn_const)
  have hφ_deriv : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d', HasDerivAt φ d' s ∧ |d'| ≤ C / ((N : ℝ) + 1) := by
    intro s hs
    obtain ⟨d, hd_p, hbd⟩ := h_der N M hs hd hb hα hq hr
    refine ⟨d + (r / 2) * (1 - q), ?_, hbd⟩
    have hd_lin := ((hasDerivAt_id s).mul_const ((r / 2) * (1 - q))).congr_deriv
      (one_mul ((r / 2) * (1 - q)))
    exact hd_p.add hd_lin
  -- Apply `exists_hasDerivAt_eq_slope` on `[0, 1]`!
  choose! φ' hφ' hφ'_bd using hφ_deriv
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope φ φ' zero_lt_one hφ_cont hφ'
  have hinc : |φ 1 - φ 0| ≤ C / ((N : ℝ) + 1) := by
    have heq : φ 1 - φ 0 = φ' c := by
      rw [sub_zero, div_one] at hslope
      exact hslope.symm
    rw [heq]
    exact hφ'_bd c hc
  have hp1 : p_path 1 = p_NM :=
    interpolating_pressure_one_eq hu.measurable hu.abs_le q r
  have hp0 : p_path 0 =
      Real.log 2 + (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂gaussianReal 0 1) +
        α * ∫ z : ℝ, Real.log (∫ ξ : ℝ,
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
          ∂gaussianReal 0 1 :=
    interpolating_pressure_zero_eq hu.measurable hu.abs_le q r
  have hdiff_eq : φ 1 - φ 0 = p_NM - perceptronRSFunctional u α r q := by
    dsimp only [φ]
    rw [hp1, hp0, perceptronRSFunctional_eq_log_two_add]
    ring
  rwa [hdiff_eq] at hinc

/-- **Talagrand Theorem 2.4.2 combined with Theorem 2.4.1 (unconditional source-facing theorem):**
Given `D ∈ ℝ`, there exist constants `K(D) ≥ 0` and `C(D) ≥ 0` (chosen before `N, M, u`) such that
whenever `u` satisfies (2.7) and `α = M / (N + 1)` satisfies `α * K(D) ≤ 1`, the replica-symmetric
system (2.68) has a unique solution `(q, r) ∈ ℝ × ℝ` and the finite-size perceptron pressure
satisfies `|p_{N+1, M}(u) - p(u)| ≤ C(D) / (N + 1)`. -/
theorem exists_unique_rs_fixed_point_and_abs_pressure_sub_le (D : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D),
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        α * K ≤ 1 →
        let P_g := Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let p_NM : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g : Fin M → Fin (N + 1) → ℝ,
          Real.log (∑ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ k : Fin M,
              u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ∂P_g
        let S (p : ℝ × ℝ) : Prop :=
          p.1 = (∫ z : ℝ, Real.tanh (z * Real.sqrt p.2) ^ 2 ∂gaussianReal 0 1) ∧
          p.2 = α * perceptronRhat u p.1
        (∃! p, S p) ∧
          ∀ p, S p → |p_NM - perceptronRSFunctional u α p.2 p.1| ≤ C / ((N : ℝ) + 1) := by
  obtain ⟨K₁, _, hK₁0, _, h_thm1⟩ := exists_unique_rs_fixed_point_and_overlap_sub_sq_le D
  obtain ⟨K₂, C, hK₂0, hC0, h_thm2⟩ := abs_perceptron_pressure_sub_rs_free_energy_le D
  refine ⟨max K₁ K₂, C, le_max_of_le_left hK₁0, hC0, ?_⟩
  intro N M u hd hb α hα P_g p_NM S
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα₁ : α * K₁ ≤ 1 := (mul_le_mul_of_nonneg_left (le_max_left K₁ K₂) hα0).trans hα
  have hα₂ : α * K₂ ≤ 1 := (mul_le_mul_of_nonneg_left (le_max_right K₁ K₂) hα0).trans hα
  obtain ⟨hex, -⟩ := h_thm1 N M hd hb hα₁
  refine ⟨hex, fun p hp => h_thm2 N M hd hb hα₂ hp.1 hp.2⟩

end SpinGlasses
