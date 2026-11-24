/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingHamiltonian

/-!
# Discrete cavity increment and second-proof interpolation (Talagrand Section 2.4)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.90)--(2.91)
from the second proof of Theorem 2.4.2.

For `N + 1` spins and `M` constraints, write `μ_M(g₀)` for the `M`-constraint quenched Gibbs measure
on `Fin (N + 1) → ℤˣ` and `S_M(τ) = (√(N + 1))⁻¹ ∑ᵢ g_{M, i} τᵢ` for the fresh constraint field.

## Main declarations

* `SpinGlasses.perceptron_pressure_succ_sub_eq`: Eq. (2.90), exact discrete cavity increment
  `p_{N+1, M+1}(u) - p_{N+1, M}(u) = (N + 1)⁻¹ 𝔼 log ⟨exp u(S_M)⟩`.
* `SpinGlasses.hasDerivAt_second_proof_interpolation`: Eq. (2.91), exact derivative and Gaussian IBP
  identity for `φ(v) = 𝔼 log 𝔼_ξ ⟨exp u(√v S_M + √(1 - v) θ)⟩` on `v ∈ (0, 1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

section SecondProofIncrement

/-- **Talagrand Section 2.4, Eq. (2.90) (discrete cavity increment of the perceptron pressure):**
`p_{N+1, M+1}(u) - p_{N+1, M}(u) = (N + 1)⁻¹ 𝔼 log ⟨exp u(S_M)⟩`, where `⟨·⟩` is the `M`-constraint
quenched Gibbs measure on `Fin (N + 1) → ℤˣ` and `S_M(τ) = (√(N + 1))⁻¹ ∑ᵢ g_{M, i} τᵢ` is the
fresh constraint field. -/
theorem perceptron_pressure_succ_sub_eq
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) (hi : Integrable u (gaussianReal 0 1)) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let P_M1 := Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ
    let γ_row := Measure.pi fun _ : Fin (N + 1) => γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let p_M1 : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g : Fin (M + 1) → Fin (N + 1) → ℝ,
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin (M + 1),
          u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ∂P_M1
    let p_M : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g₀ : Fin M → Fin (N + 1) → ℝ,
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin M,
          u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))) ∂P_M
    p_M1 - p_M =
      ((N : ℝ) + 1)⁻¹ * ∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ),
        Real.log (∫ τ : Fin (N + 1) → ℤˣ,
          Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))
          ∂(μ_M p.1)) ∂(P_M.prod γ_row) := by
  intro γ P_M P_M1 γ_row μ_M p_M1 p_M
  let H (g : Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g i * ((τ i : ℤ) : ℝ)
  have hH_m (τ : Fin (N + 1) → ℤˣ) : Measurable fun g => H g τ := by dsimp only [H]; fun_prop
  have hH_i (τ : Fin (N + 1) → ℤˣ) : Integrable (fun g => u (H g τ)) γ_row := by
    have hm : Measure.map (fun g => H g τ) γ_row = gaussianReal 0 1 :=
      map_normalized_constraint_field_eq_gaussianReal (Nat.succ_pos N) τ
    have hm_i : Integrable u (Measure.map (fun g => H g τ) γ_row) := by rwa [hm]
    exact hm_i.comp_measurable (hH_m τ)
  let pEnergy (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))
      (τ : Fin (N + 1) → ℤˣ) : ℝ := ∑ k : Fin M, u (H (p.1 k) τ)
  let Z_M (g₀ : Fin M → Fin (N + 1) → ℝ) : ℝ :=
    ∑ τ : Fin (N + 1) → ℤˣ, Real.exp (∑ k : Fin M, u (H (g₀ k) τ))
  let R_inc (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ τ : Fin (N + 1) → ℤˣ, Real.exp (u (H p.2 τ)) ∂(μ_M p.1)
  have hlog_add (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :
      Real.log (∑ τ : Fin (N + 1) → ℤˣ, Real.exp (pEnergy p τ + u (H p.2 τ))) =
        Real.log (Z_M p.1) + Real.log (R_inc p) :=
    log_sum_exp_add_eq_log_sum_exp_add_log_integral_exp (pEnergy p) (fun τ => u (H p.2 τ))
  have hE_m (τ : Fin (N + 1) → ℤˣ) : Measurable fun p => pEnergy p τ :=
    Finset.measurable_sum _ fun k _ => ((hu.comp (hH_m τ)).comp
      ((measurable_pi_apply k).comp measurable_fst))
  have hE1_m (τ : Fin (N + 1) → ℤˣ) :
      Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
        pEnergy p τ + u (H p.2 τ) :=
    (hE_m τ).add ((hu.comp (hH_m τ)).comp measurable_snd)
  have hZM_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (Z_M p.1) := by
    simpa only [one_mul] using measurable_log_sum_exp hE_m 1
  have hFM1_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (∑ τ, Real.exp (pEnergy p τ + u (H p.2 τ))) := by
    simpa only [one_mul] using measurable_log_sum_exp hE1_m 1
  have hp_M1_eq :
      (∫ g : Fin (M + 1) → Fin (N + 1) → ℝ,
        Real.log (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ k : Fin (M + 1), u (H (g k) τ))) ∂P_M1) =
      ∫ p, (Real.log (Z_M p.1) + Real.log (R_inc p)) ∂(P_M.prod γ_row) := by
    have hmp := measurePreserving_finSuccProd γ_row M
    have hcomp := hmp.integral_comp_of_aestronglyMeasurable
      (g := fun p => Real.log (∑ τ, Real.exp (pEnergy p τ + u (H p.2 τ))))
      hFM1_m.aestronglyMeasurable
    refine (integral_congr_ae (ae_of_all _ fun g => ?_)).trans
      (hcomp.trans (integral_congr_ae (ae_of_all _ hlog_add)))
    dsimp only [Function.comp_apply, pEnergy]
    congr 1; refine Finset.sum_congr rfl fun τ _ => congrArg Real.exp ?_
    rw [Fin.sum_univ_castSucc]
    simp [MeasurableEquiv.finSuccProd_apply]
  have hE_i (τ : Fin (N + 1) → ℤˣ) :
      Integrable (fun p => pEnergy p τ) (P_M.prod γ_row) :=
    integrable_finsetSum _ fun k _ =>
      (integrable_comp_eval (μ := fun _ : Fin M => γ_row) (i := k) (hH_i τ)).comp_fst γ_row
  have hZM_int : Integrable (fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (Z_M p.1)) (P_M.prod γ_row) := by
    simpa only [one_mul] using
      integrable_log_sum_exp (μ := P_M.prod γ_row) (H := pEnergy) (β := 1) one_pos hE_m hE_i
  have hR_int : Integrable (fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
      Real.log (R_inc p)) (P_M.prod γ_row) := by
    have hNew := integrable_log_sum_exp (μ := P_M.prod γ_row)
      (H := fun p τ => pEnergy p τ + u (H p.2 τ)) (β := 1) one_pos hE1_m
      (fun τ => (hE_i τ).add ((hH_i τ).comp_snd P_M))
    simp only [one_mul] at hNew
    exact (hNew.sub hZM_int).congr (ae_of_all _ fun p => by
      simp only [Pi.sub_apply]; linarith [hlog_add p])
  have hZM_fst :
      (∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ), Real.log (Z_M p.1)
        ∂(P_M.prod γ_row)) =
      ∫ g₀ : Fin M → Fin (N + 1) → ℝ, Real.log (Z_M g₀) ∂P_M :=
    integral_prod_fun_fst_of_isProbabilityMeasure P_M γ_row (fun g₀ => Real.log (Z_M g₀))
  dsimp only [p_M1, p_M]
  change ((N : ℝ) + 1)⁻¹ * (∫ g : Fin (M + 1) → Fin (N + 1) → ℝ,
        Real.log (∑ τ, Real.exp (∑ k, u (H (g k) τ))) ∂P_M1) -
      ((N : ℝ) + 1)⁻¹ * (∫ g₀ : Fin M → Fin (N + 1) → ℝ, Real.log (Z_M g₀) ∂P_M) =
    ((N : ℝ) + 1)⁻¹ * ∫ p, Real.log (R_inc p) ∂(P_M.prod γ_row)
  rw [hp_M1_eq, integral_add hZM_int hR_int, hZM_fst]
  ring

/-- The second-proof field `√v' (√(N+1))⁻¹ ∑ᵢ g'ᵢ εᵢ + √(1-v') (√q z + √(1-q) ξ)` is measurable in
the state `(ε, ξ)` for a fixed disorder. -/
private lemma measurable_secondProof_field {N M : ℕ} (q v' : ℝ)
    (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
    Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
      Real.sqrt v' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - v') * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2) :=
  (((Finset.measurable_sum _ fun i _ => measurable_const.mul
    (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))).const_mul _
    ).const_mul _).add ((measurable_const.add (measurable_snd.const_mul _)).const_mul _)

/-- The `v'`-derivative of the second-proof field is measurable in the state. -/
private lemma measurable_secondProof_field_deriv {N M : ℕ} (q v' : ℝ)
    (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
    Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
      (1 / (2 * Real.sqrt v')) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - v'))) * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2) :=
  (((Finset.measurable_sum _ fun i _ => measurable_const.mul
    (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))).const_mul _
    ).const_mul _).sub ((measurable_const.add (measurable_snd.const_mul _)).const_mul _)

/-- **Dominated differentiation step of (2.91).** The function
`v' ↦ 𝔼 log ∫ exp u(S_{v'})` is differentiable at `v ∈ (0, 1)` with derivative the
integral of `⟨S'_v u'(S_v)⟩` over the disorder, and this derivative is integrable. -/
private theorem hasDerivAt_secondProof_logPartition
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let P_ext := (P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ)).prod γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let S_v (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      Real.sqrt v' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - v') * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    let S'_v (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      (1 / (2 * Real.sqrt v')) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - v'))) * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    let F'_stmt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
      ∫ x, (S'_v v ω x * deriv u (S_v v ω x))
        ∂(((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
    HasDerivAt
      (fun v' => ∫ ω, Real.log (∫ x, Real.exp (u (S_v v' ω x)) ∂((μ_M ω.1.1).prod γ)) ∂P_ext)
      (∫ ω, F'_stmt ω ∂P_ext) v ∧ Integrable F'_stmt P_ext := by
  intro γ P_M P_ext μ_M S_v S'_v F'_stmt
  obtain ⟨δ, hδ, hδ_bd⟩ := exists_Ioo_nhds_bound hv
  let U_nbhd : Set ℝ := Ioo (v - δ) (v + δ)
  have hU_nhds : U_nbhd ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  have hμM_prob (g₀ : Fin M → Fin (N + 1) → ℝ) : IsProbabilityMeasure (μ_M g₀) :=
    isProbabilityMeasure_tilted Integrable.of_finite
  let Z_fn (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
    ∫ x, Real.exp (u (S_v v' ω x)) ∂((μ_M ω.1.1).prod γ)
  let F'_fn (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
    ∫ x, (S'_v v' ω x * deriv u (S_v v' ω x))
      ∂(((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v' ω x)))
  have hSv_m (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S_v v' ω x :=
    measurable_secondProof_field q v' ω
  have hS'v_m (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S'_v v' ω x :=
    measurable_secondProof_field_deriv q v' ω
  let b_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
    |D₁| * ((1 / (2 * Real.sqrt δ)) *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.2 i|) + Real.sqrt q * |ω.2|))
  let c_ξ : ℝ := |D₁| * ((1 / (2 * Real.sqrt δ)) * Real.sqrt (1 - q))
  have hc_ξ0 : 0 ≤ c_ξ := by dsimp only [c_ξ]; positivity
  have hpt_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (x : (Fin (N + 1) → ℤˣ) × ℝ) {t : ℝ} (ht : t ∈ U_nbhd) :
      |S'_v t ω x * deriv u (S_v t ω x)| ≤ b_ω ω + c_ξ * |x.2| := by
    obtain ⟨hd_t, hd_1t⟩ := hδ_bd t ht
    rw [abs_mul, mul_comm _ |deriv u _|]
    have hS'_le : |S'_v t ω x| ≤
        (1 / (2 * Real.sqrt δ)) *
          (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.2 i|) +
            Real.sqrt q * |ω.2|) + Real.sqrt (1 - q) * |x.2|) := by
      have hdiv := abs_div_two_sqrt_sub_le hδ hd_t hd_1t
        (a := (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ))
        (b := Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
      have heq : S'_v t ω x =
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) / (2 * Real.sqrt t) -
            (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2) / (2 * Real.sqrt (1 - t)) := by
        dsimp only [S'_v]; ring
      rw [heq]
      refine hdiv.trans ?_
      have hs1 : |(Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)| ≤
          (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, |ω.1.2 i| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < (Real.sqrt (N + 1 : ℕ))⁻¹)]
        exact mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_units_cast_eq_one, mul_one])) (by positivity)
      have hs2 : |Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2| ≤
          Real.sqrt q * |ω.2| + Real.sqrt (1 - q) * |x.2| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ (((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, |ω.1.2 i|) +
            (Real.sqrt q * |ω.2| + Real.sqrt (1 - q) * |x.2|)) / (2 * Real.sqrt δ) :=
          div_le_div_of_nonneg_right (add_le_add hs1 hs2) (by positivity)
        _ = _ := by ring
    calc |deriv u (S_v t ω x)| * |S'_v t ω x|
        ≤ |D₁| * ((1 / (2 * Real.sqrt δ)) *
            (((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.2 i|) +
              Real.sqrt q * |ω.2|) + Real.sqrt (1 - q) * |x.2|)) :=
          mul_le_mul (hu.abs_deriv_le_abs _) hS'_le (abs_nonneg _) (abs_nonneg D₁)
      _ = b_ω ω + c_ξ * |x.2| := by dsimp only [b_ω, c_ξ]; ring
  have hZ_deriv (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      {t : ℝ} (ht : t ∈ U_nbhd) :
      HasDerivAt (fun v' => Real.log (Z_fn v' ω)) (F'_fn t ω) t := by
    obtain ⟨hd_t, hd_1t⟩ := hδ_bd t ht
    have hA_m : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
        (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ) :=
      (Finset.measurable_sum _ fun i _ => measurable_const.mul
        (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))).const_mul _
    have hC_m : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
        Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2 :=
      measurable_const.add (measurable_snd.const_mul _)
    have hA_i : Integrable (fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
        (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) ((μ_M ω.1.1).prod γ) :=
      Integrable.of_bound hA_m.aestronglyMeasurable
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, |ω.1.2 i|) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
          exact mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_units_cast_eq_one, mul_one])) (by positivity))
    have hC_i : Integrable (fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
        Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2) ((μ_M ω.1.1).prod γ) :=
      (integrable_const _).add (IsGaussian.integrable_id.comp_snd _ |>.const_mul _)
    exact (hasDerivAt_log_integral_exp_sqrt_path (μ := (μ_M ω.1.1).prod γ) hu.differentiable
      hu.le hu.abs_deriv_le hA_m hC_m hA_i hC_i ⟨hδ.trans_le hd_t, by linarith⟩).congr_deriv
      (integral_congr_ae (ae_of_all _ fun x => by dsimp only [S'_v, S_v]; ring))
  have hF'_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      {t : ℝ} (ht : t ∈ U_nbhd) :
      |F'_fn t ω| ≤ b_ω ω + Real.exp (2 * |B|) * (c_ξ * ∫ ξ, |ξ| ∂γ) := by
    let V_t (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ := u (S_v t ω x)
    have hVt_m : Measurable V_t := hu.measurable.comp (hSv_m t ω)
    have hprob_t : IsProbabilityMeasure (((μ_M ω.1.1).prod γ).tilted V_t) :=
      isProbabilityMeasure_tilted_of_ae_le hVt_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
    have hξ_int : Integrable (fun x : (Fin (N + 1) → ℤˣ) × ℝ => |x.2|) ((μ_M ω.1.1).prod γ) :=
      IsGaussian.integrable_id.abs.comp_snd _
    have hξ_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × ℝ => |x.2|)
        (((μ_M ω.1.1).prod γ).tilted V_t) :=
      integrable_tilted_of_ae_le hVt_m.aemeasurable (ae_of_all _ fun _ => hu.le _) hξ_int
    have hint_F : Integrable (fun x => S'_v t ω x * deriv u (S_v t ω x))
        (((μ_M ω.1.1).prod γ).tilted V_t) :=
      ((integrable_const (b_ω ω)).add (hξ_t.const_mul c_ξ)).mono'
        ((hS'v_m t ω).mul ((measurable_deriv u).comp (hSv_m t ω))).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hpt_bd ω x ht)
    have h1 : |F'_fn t ω| ≤
        ∫ x, (b_ω ω + c_ξ * |x.2|) ∂(((μ_M ω.1.1).prod γ).tilted V_t) :=
      (abs_integral_le_integral_abs).trans
        (integral_mono hint_F.abs ((integrable_const (b_ω ω)).add (hξ_t.const_mul c_ξ))
          fun x => hpt_bd ω x ht)
    have h1_add : (∫ x, (b_ω ω + c_ξ * |x.2|) ∂(((μ_M ω.1.1).prod γ).tilted V_t)) =
        (∫ _x, b_ω ω ∂(((μ_M ω.1.1).prod γ).tilted V_t)) +
        ∫ x, c_ξ * |x.2| ∂(((μ_M ω.1.1).prod γ).tilted V_t) :=
      integral_add (integrable_const (b_ω ω)) (hξ_t.const_mul c_ξ)
    rw [h1_add, integral_const, probReal_univ, one_smul, integral_const_mul] at h1
    refine h1.trans (add_le_add le_rfl ?_)
    have hbound := abs_integral_tilted_le_exp_mul_integral_abs hVt_m.aemeasurable
      (ae_of_all _ fun x => (hu.abs_le _).trans (le_abs_self B)) hξ_int
    have hsnd := integral_prod_fun_snd_of_isProbabilityMeasure (μ := μ_M ω.1.1) (ν := γ)
      (fun ξ : ℝ => |ξ|)
    have hd0 := (le_abs_self _).trans hbound
    simp only [probReal_univ, div_one, abs_abs, hsnd] at hd0
    calc c_ξ * ∫ x, |x.2| ∂(((μ_M ω.1.1).prod γ).tilted V_t)
        ≤ c_ξ * (Real.exp (2 * |B|) * ∫ ξ, |ξ| ∂γ) :=
          mul_le_mul_of_nonneg_left hd0 hc_ξ0
      _ = Real.exp (2 * |B|) * (c_ξ * ∫ ξ, |ξ| ∂γ) := by ring
  let E_M (g₀ : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
  have hEM_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
      E_M p.1 p.2 := by
    refine Finset.measurable_sum _ fun k _ => hu.measurable.comp ?_
    refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
    have h1 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
        p.1 k i := (measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_fst)
    have h2 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
        ((p.2 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_snd)
    exact h1.mul h2
  have hEM_i (g₀ : Fin M → Fin (N + 1) → ℝ) :
      Integrable (fun τ => Real.exp (E_M g₀ τ)) Measure.count := Integrable.of_finite
  have hZ_m (s' : ℝ) : Measurable (Z_fn s') := by
    have heq : Z_fn s' = fun ω =>
        (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v s' ω (τ, ξ))) ∂γ) /
        ∑ τ : Fin (N + 1) → ℤˣ, Real.exp (E_M ω.1.1 τ) := by
      funext ω
      dsimp only [Z_fn, μ_M]
      have hi : Integrable (fun x => Real.exp (u (S_v s' ω x)))
          (((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E_M ω.1.1)).prod γ) :=
        integrable_exp_of_ae_le (hu.measurable.comp (hSv_m s' ω)).aemeasurable
          (ae_of_all _ fun _ => hu.le _)
      rw [integral_prod _ hi, integral_tilted_eq_div,
        integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
      simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
      congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [heq]
    refine Measurable.div (Finset.measurable_sum _ fun τ _ => Measurable.mul ?_ ?_)
      (Finset.measurable_sum _ fun τ _ => ?_)
    · have hτ : Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
          E_M ω.1.1 τ :=
        Finset.measurable_sum _ fun k _ => hu.measurable.comp
          ((Finset.measurable_sum _ fun i _ =>
            ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp
              (measurable_fst.comp measurable_fst))).mul_const _).const_mul _)
      exact Real.measurable_exp.comp hτ
    · have hj : Measurable fun p :
          (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
          Real.exp (u (S_v s' p.1 (τ, p.2))) := by
        have h1 : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
            ∑ i : Fin (N + 1), p.1.1.2 i * ((τ i : ℤ) : ℝ) :=
          Finset.measurable_sum _ fun i _ =>
            ((measurable_pi_apply i).comp
              (measurable_snd.comp (measurable_fst.comp measurable_fst))).mul_const _
        exact Real.measurable_exp.comp (hu.measurable.comp
          (((h1.const_mul _).const_mul _).add
            ((((measurable_snd.comp measurable_fst).const_mul _).add
              (measurable_snd.const_mul _)).const_mul _)))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
    · have hτ : Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
          E_M ω.1.1 τ :=
        Finset.measurable_sum _ fun k _ => hu.measurable.comp
          ((Finset.measurable_sum _ fun i _ =>
            ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp
              (measurable_fst.comp measurable_fst))).mul_const _).const_mul _)
      exact Real.measurable_exp.comp hτ
  have hlogZ_int (s' : ℝ) : Integrable (fun ω => Real.log (Z_fn s' ω)) P_ext :=
    Integrable.of_bound (Real.measurable_log.comp (hZ_m s')).aestronglyMeasurable |B|
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact (abs_log_integral_exp_le_of_ae_abs_le
          (hu.measurable.comp (hSv_m s' ω)).aemeasurable
          (ae_of_all _ fun _ => hu.abs_le _)).trans (le_abs_self B))
  let e_ass : (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) ≃ᵐ
      (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ) :=
    MeasurableEquiv.prodAssoc
  have hF'_m : Measurable (F'_fn v) := by
    let V_a (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ))
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ := u (S_v v (e_ass.symm p) x)
    let G_a (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ))
        (σ : Unit → (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      S'_v v (e_ass.symm p) (σ ()) * deriv u (S_v v (e_ass.symm p) (σ ()))
    have hVa_m : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
        V_a q_p.1 q_p.2 := by
      have h1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
          ∑ i : Fin (N + 1), q_p.1.2.1 i * ((q_p.2.1 i : ℤ) : ℝ) :=
        Finset.measurable_sum _ fun i _ =>
          ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_snd.comp measurable_fst))).mul
          (measurable_units_cast.comp
            ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
      exact hu.measurable.comp (((h1.const_mul _).const_mul _).add
        ((((measurable_snd.comp (measurable_snd.comp measurable_fst)).const_mul _).add
          ((measurable_snd.comp measurable_snd).const_mul _)).const_mul _))
    have hGa_m : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
          (Unit → (Fin (N + 1) → ℤˣ) × ℝ) => G_a q_p.1 q_p.2 := by
      have h_ev : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × ℝ) => q_p.2 () :=
        (measurable_pi_apply ()).comp measurable_snd
      have h1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × ℝ) =>
          ∑ i : Fin (N + 1), q_p.1.2.1 i * ((((q_p.2 ()).1 i : ℤ) : ℝ)) :=
        Finset.measurable_sum _ fun i _ =>
          ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_snd.comp measurable_fst))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp (measurable_fst.comp h_ev)))
      have hz_a : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) → ℝ) × ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × ℝ) =>
          Real.sqrt q * q_p.1.2.2 + Real.sqrt (1 - q) * (q_p.2 ()).2 :=
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).const_mul _).add
          ((measurable_snd.comp h_ev).const_mul _)
      exact (((h1.const_mul _).const_mul _).sub (hz_a.const_mul _)).mul
        ((measurable_deriv u).comp (((h1.const_mul _).const_mul _).add (hz_a.const_mul _)))
    have hm_u := measurable_integral_pi_tilted_prod_tilted (R := Unit)
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)) γ hEM_m hEM_i hVa_m hGa_m
    have heq : F'_fn v = fun ω =>
        (∫ σ : Unit → (Fin (N + 1) → ℤˣ) × ℝ, G_a (e_ass ω) σ
          ∂(Measure.pi fun _ : Unit => ((μ_M (e_ass ω).1).prod γ).tilted (V_a (e_ass ω)))) := by
      funext ω
      have hV_ω : V_a (e_ass ω) = fun x => u (S_v v ω x) := by
        funext x; dsimp only [V_a]; rw [MeasurableEquiv.symm_apply_apply]
      have hprob_ω : IsProbabilityMeasure
          (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))) :=
        isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
          (ae_of_all _ fun _ => hu.le _)
      have he_fst : (e_ass ω).1 = ω.1.1 := rfl
      rw [he_fst, hV_ω]
      symm
      refine (integral_congr_ae (ae_of_all _ fun σ => ?_)).trans
        ((measurePreserving_funUnique (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
          Unit).integral_comp_of_aestronglyMeasurable
          (g := fun x => S'_v v ω x * deriv u (S_v v ω x))
          ((hS'v_m v ω).mul ((measurable_deriv u).comp (hSv_m v ω))).aestronglyMeasurable)
      dsimp only [G_a, Function.comp_apply]
      rw [MeasurableEquiv.symm_apply_apply]
      rfl
    rw [heq]
    exact hm_u.comp e_ass.measurable
  have hb_ω_int : Integrable b_ω P_ext := by
    dsimp only [b_ω]
    refine Integrable.const_mul (Integrable.const_mul (Integrable.add ?_ ?_) _) |D₁|
    · refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
      have hi1 : Integrable (fun gM : Fin (N + 1) → ℝ => |gM i|)
          (Measure.pi fun _ : Fin (N + 1) => γ) :=
        integrable_comp_eval (μ := fun _ : Fin (N + 1) => γ) (i := i) IsGaussian.integrable_id.abs
      exact (hi1.comp_snd P_M).comp_fst γ
    · have hz1 : Integrable (fun z : ℝ => Real.sqrt q * |z|) γ :=
        IsGaussian.integrable_id.abs.const_mul (Real.sqrt q)
      exact hz1.comp_snd (P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ))
  have hd_raw : HasDerivAt (fun v' => ∫ ω, Real.log (Z_fn v' ω) ∂P_ext)
      (∫ ω, F'_fn v ω ∂P_ext) v :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P_ext)
      (F := fun t ω => Real.log (Z_fn t ω)) (F' := F'_fn) (s := U_nbhd)
      (bound := fun ω => b_ω ω + Real.exp (2 * |B|) * (c_ξ * ∫ ξ, |ξ| ∂γ))
      hU_nhds (Eventually.of_forall fun t => (hlogZ_int t).aestronglyMeasurable)
      (hlogZ_int v) hF'_m.aestronglyMeasurable
      (ae_of_all _ fun ω t ht => by rw [Real.norm_eq_abs]; exact hF'_bd ω ht)
      (hb_ω_int.add (integrable_const _))
      (ae_of_all _ fun ω t ht => hZ_deriv ω ht)).2
  have hF'_int : Integrable (F'_fn v) P_ext := by
    have hv_mem : v ∈ U_nbhd := ⟨by linarith, by linarith⟩
    exact (hb_ω_int.add (integrable_const _)).mono' hF'_m.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hF'_bd ω hv_mem)
  exact ⟨hd_raw, hF'_int⟩

/-- **Stein identity at fixed old disorder in (2.91).** For a fixed old disorder `g₀`, Gaussian
integration by parts over the shared Gaussian `(g_M, z)` with the auxiliary Gaussian `ξ` turns the
one-replica derivative term into `-(1/2)` times the overlap-weighted two-replica term; the
diagonal covariance vanishes, so only the fresh-replica term remains. -/
private theorem secondProof_stein_fixed_disorder
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (g₀ : Fin M → Fin (N + 1) → ℝ) :
    let γ : Measure ℝ := gaussianReal 0 1
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ
    let γ_aux := Measure.pi fun _ : Unit => γ
    let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => Real.sqrt (1 - v) * Real.sqrt q)
    let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt q)
    let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - v) * Real.sqrt (1 - q)
    let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
      fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - q)
    ∫ w, ∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
        1 * (W_sh (σ ()).1 ⬝ᵥ w + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ w + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => ((μ_M g₀).prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))) ∂γ_sh =
      -(1 / 2) * ∫ w, ∫ σ : Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i,
              (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q) *
            deriv u (α_sh (σ (some ())).1 ⬝ᵥ w + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
            deriv u (α_sh (σ none).1 ⬝ᵥ w + α_aux (σ none).1 ⬝ᵥ (σ none).2)
          ∂(Measure.pi fun _ : Option Unit => ((μ_M g₀).prod γ_aux).tilted
            (fun y => u (α_sh y.1 ⬝ᵥ w + α_aux y.1 ⬝ᵥ y.2))) ∂γ_sh := by
  intro γ μ_M γ_sh γ_aux α_sh W_sh α_aux W_aux
  have hprob : IsProbabilityMeasure (μ_M g₀) := isProbabilityMeasure_tilted Integrable.of_finite
  exact stein_tilted_unit_replica_deriv (μ_M g₀) id measurable_id α_sh W_sh α_aux W_aux hu
    (fun τ₁ τ₂ => (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) - q)
    (interp_stein_cov_shared hv hq.1) (interp_stein_cov_diag hv hq)

/-- **Measurability of the split one-replica and two-replica Stein integrands for (2.91).** -/
private lemma measurable_secondProof_stein_split
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) (q v : ℝ) :
    let γ : Measure ℝ := gaussianReal 0 1
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let γ_aux := Measure.pi fun _ : Unit => γ
    let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => Real.sqrt (1 - v) * Real.sqrt q)
    let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt q)
    let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - v) * Real.sqrt (1 - q)
    let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
      fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - q)
    let I_L (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
      ∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
        1 * (W_sh (σ ()).1 ⬝ᵥ p.2 + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ p.2 + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => ((μ_M p.1).prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)))
    let I_R (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
      ∫ σ : Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
            (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q) *
          deriv u (α_sh (σ (some ())).1 ⬝ᵥ p.2 + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (σ none).1 ⬝ᵥ p.2 + α_aux (σ none).1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => ((μ_M p.1).prod γ_aux).tilted
          (fun y => u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)))
    Measurable I_L ∧ Measurable I_R := by
  intro γ μ_M γ_aux α_sh W_sh α_aux W_aux I_L I_R
  let E_M (g₀ : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
  have hEM_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
      E_M p.1 p.2 := by
    refine Finset.measurable_sum _ fun k _ => hu.comp ?_
    refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
    have h1 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
        p.1 k i := (measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_fst)
    have h2 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
        ((p.2 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_snd)
    exact h1.mul h2
  have hEM_i (g₀ : Fin M → Fin (N + 1) → ℝ) :
      Integrable (fun τ => Real.exp (E_M g₀ τ)) Measure.count := Integrable.of_finite
  let V_sp (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ))
      (y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
    u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)
  have hVsp_m : Measurable fun q_p :
      ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
        ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => V_sp q_p.1 q_p.2 := by
    have hd1 : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_sh q_p.2.1 ⬝ᵥ q_p.1.2 := by
      simp only [dotProduct]
      refine Finset.measurable_sum _ fun idx _ => ?_
      exact ((measurable_of_finite fun τ => α_sh τ idx).comp
        (measurable_fst.comp measurable_snd)).mul
        ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
    have hd2 : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_aux q_p.2.1 ⬝ᵥ q_p.2.2 := by
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact measurable_const.mul
        ((measurable_pi_apply ()).comp (measurable_snd.comp measurable_snd))
    exact hu.comp (hd1.add hd2)
  have hIL_m : Measurable I_L := by
    let F_L (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ))
        (σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      1 * (W_sh (σ ()).1 ⬝ᵥ p.2 + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ p.2 + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
    have hFL_m : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => F_L q_p.1 q_p.2 := by
      dsimp only [F_L]
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      have h_ev : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => q_p.2 () :=
        (measurable_pi_apply ()).comp measurable_snd
      have hw1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => W_sh (q_p.2 ()).1 ⬝ᵥ q_p.1.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => W_sh τ idx).comp (measurable_fst.comp h_ev)).mul
            ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have hw2 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => W_aux (q_p.2 ()).1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      have ha1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_sh (q_p.2 ()).1 ⬝ᵥ q_p.1.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp (measurable_fst.comp h_ev)).mul
            ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_aux (q_p.2 ()).1 ⬝ᵥ (q_p.2 ()).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      exact (hw1.add hw2).mul ((measurable_deriv u).comp (ha1.add ha2))
    exact measurable_integral_pi_tilted_prod_tilted
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)) γ_aux hEM_m hEM_i hVsp_m hFL_m
  have hIR_m : Measurable I_R := by
    have hfl_o (o : Option Unit) : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
        deriv u (α_sh (q_p.2 o).1 ⬝ᵥ q_p.1.2 + α_aux (q_p.2 o).1 ⬝ᵥ (q_p.2 o).2) := by
      have h_ev : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => q_p.2 o :=
        (measurable_pi_apply o).comp measurable_snd
      have ha1 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) => α_sh (q_p.2 o).1 ⬝ᵥ q_p.1.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp (measurable_fst.comp h_ev)).mul
            ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have ha2 : Measurable fun q_p :
          ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
            (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
          α_aux (q_p.2 o).1 ⬝ᵥ (q_p.2 o).2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp (measurable_snd.comp h_ev))
      exact (measurable_deriv u).comp (ha1.add ha2)
    have hR_o : Measurable fun q_p :
        ((Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) ×
          (Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
          ((((q_p.2 (some ())).1 i : ℤ) : ℝ) * (((q_p.2 none).1 i : ℤ) : ℝ))) - q) := by
      refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
      exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp ((measurable_pi_apply (some ())).comp measurable_snd)))).mul
        (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp ((measurable_pi_apply none).comp measurable_snd))))
    exact measurable_integral_pi_tilted_prod_tilted
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)) γ_aux hEM_m hEM_i hVsp_m
      ((hR_o.mul (hfl_o (some ()))).mul (hfl_o none))
  exact ⟨hIL_m, hIR_m⟩

/-- **Gaussian integration by parts step of (2.91).** The integral over the disorder of
`⟨S'_v u'(S_v)⟩` equals `-(1/2)` times the overlap-weighted two-replica term. The
integrability hypothesis is the output of the dominated differentiation step. -/
private theorem integral_secondProof_stein
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let P_ext := (P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ)).prod γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let S_v (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      Real.sqrt v' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - v') * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    let S'_v (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      (1 / (2 * Real.sqrt v')) * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - v'))) * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    let F'_stmt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) : ℝ :=
      ∫ x, (S'_v v ω x * deriv u (S_v v ω x))
        ∂(((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
    Integrable F'_stmt P_ext →
    ∫ ω, F'_stmt ω ∂P_ext =
        -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
        ∂P_ext := by
  intro γ P_M P_ext μ_M S_v S'_v F'_stmt hF'_int
  have hμM_prob (g₀ : Fin M → Fin (N + 1) → ℝ) : IsProbabilityMeasure (μ_M g₀) :=
    isProbabilityMeasure_tilted Integrable.of_finite
  have hSv_m (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S_v v' ω x :=
    measurable_secondProof_field q v' ω
  have hS'v_m (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S'_v v' ω x :=
    measurable_secondProof_field_deriv q v' ω
  let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ
  let γ_aux := Measure.pi fun _ : Unit => γ
  let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => Real.sqrt (1 - v) * Real.sqrt q)
  let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt q)
  let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - v) * Real.sqrt (1 - q)
  let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
    fun _ => -(1 / (2 * Real.sqrt (1 - v))) * Real.sqrt (1 - q)
  obtain ⟨hIL_m, hIR_m⟩ := measurable_secondProof_stein_split (N := N) (M := M) hu.measurable q v
  let split_ext (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ) :=
    (ω.1.1, Sum.elim ω.1.2 (fun _ : Unit => ω.2))
  have hmp_ext : MeasurePreserving split_ext P_ext (P_M.prod γ_sh) := by
    have h1 := measurePreserving_prodAssoc P_M (Measure.pi fun _ : Fin (N + 1) => γ) γ
    have hunit := (measurePreserving_funUnique γ Unit).symm
    have hsum := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin (N + 1) ⊕ Unit => ℝ)
      (fun _ => γ)).comp ((MeasurePreserving.id (Measure.pi fun _ : Fin (N + 1) => γ)).prod hunit)
    have full := ((MeasurePreserving.id P_M).prod hsum).comp h1
    convert full using 1
    ext ω : 1
    refine Prod.ext rfl ?_
    ext idx
    rcases idx with i | _ <;>
      simp [split_ext, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]
  let e_st : ((Fin (N + 1) → ℤˣ) × ℝ) ≃ᵐ ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.funUnique Unit ℝ).symm
  have he_st_apply (x : (Fin (N + 1) → ℤˣ) × ℝ) : e_st x = (x.1, fun _ => x.2) := rfl
  have hmp_st (g₀ : Fin M → Fin (N + 1) → ℝ) :
      MeasurePreserving ⇑e_st ((μ_M g₀).prod γ) ((μ_M g₀).prod γ_aux) :=
    (MeasurePreserving.id (μ_M g₀)).prod (measurePreserving_funUnique γ Unit).symm
  have hS_eq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (x : (Fin (N + 1) → ℤˣ) × ℝ) :
      α_sh (e_st x).1 ⬝ᵥ (split_ext ω).2 + α_aux (e_st x).1 ⬝ᵥ (e_st x).2 = S_v v ω x := by
    rw [he_st_apply]
    dsimp only [α_sh, α_aux, split_ext, S_v]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h1 : (∑ i : Fin (N + 1),
        Real.sqrt v * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) * ω.1.2 i) =
      Real.sqrt v *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), ω.1.2 i * ((x.1 i : ℤ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
  have hS'_eq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (x : (Fin (N + 1) → ℤˣ) × ℝ) :
      W_sh (e_st x).1 ⬝ᵥ (split_ext ω).2 + W_aux (e_st x).1 ⬝ᵥ (e_st x).2 = S'_v v ω x := by
    rw [he_st_apply]
    dsimp only [W_sh, W_aux, split_ext, S'_v]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h1 : (∑ i : Fin (N + 1),
        (1 / (2 * Real.sqrt v)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) * ω.1.2 i) =
      (1 / (2 * Real.sqrt v)) *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), ω.1.2 i * ((x.1 i : ℤ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
  have htilted_st (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))).map e_st =
      ((μ_M (split_ext ω).1).prod γ_aux).tilted
        (fun y => u (α_sh y.1 ⬝ᵥ (split_ext ω).2 + α_aux y.1 ⬝ᵥ y.2)) := by
    have hVm : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => u (S_v v ω x) :=
      hu.measurable.comp (hSv_m v ω)
    rw [map_tilted_measurableEquiv e_st (hmp_st ω.1.1) hVm]
    congr 1; funext y
    obtain ⟨x, rfl⟩ := e_st.surjective y
    dsimp only [Function.comp_apply]
    rw [MeasurableEquiv.symm_apply_apply, hS_eq ω x]
  let I_L (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
      1 * (W_sh (σ ()).1 ⬝ᵥ p.2 + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit, deriv u (α_sh (σ r_u).1 ⬝ᵥ p.2 + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
      ∂(Measure.pi fun _ : Unit => ((μ_M p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)))
  let I_R (p : (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q) *
        deriv u (α_sh (σ (some ())).1 ⬝ᵥ p.2 + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1 ⬝ᵥ p.2 + α_aux (σ none).1 ⬝ᵥ (σ none).2)
      ∂(Measure.pi fun _ : Option Unit => ((μ_M p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)))
  have hIL_split (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      I_L (split_ext ω) = F'_stmt ω := by
    let ν_ω := ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))
    have hprob_ω : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    let F_sL (σ : Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      1 * (W_sh (σ ()).1 ⬝ᵥ (split_ext ω).2 + W_aux (σ ()).1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit,
          deriv u (α_sh (σ r_u).1 ⬝ᵥ (split_ext ω).2 + α_aux (σ r_u).1 ⬝ᵥ (σ r_u).2))
    have ht1 : I_L (split_ext ω) =
        ∫ f_u : Unit → (Fin (N + 1) → ℤˣ) × ℝ,
          F_sL (fun r_u => e_st (f_u r_u)) ∂(Measure.pi fun _ : Unit => ν_ω) := by
      dsimp only [I_L, F_sL, ν_ω]
      rw [← htilted_st ω]
      exact integral_pi_map_equiv ν_ω e_st F_sL
    have ht2 (f_u : Unit → (Fin (N + 1) → ℤˣ) × ℝ) :
        F_sL (fun r_u => e_st (f_u r_u)) =
          S'_v v ω (f_u ()) * deriv u (S_v v ω (f_u ())) := by
      dsimp only [F_sL]
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      rw [hS_eq ω (f_u ()), hS'_eq ω (f_u ())]
    rw [ht1]
    exact (integral_congr_ae (ae_of_all _ ht2)).trans
      ((measurePreserving_funUnique ν_ω Unit).integral_comp_of_aestronglyMeasurable
        (g := fun x => S'_v v ω x * deriv u (S_v v ω x))
        ((hS'v_m v ω).mul ((measurable_deriv u).comp (hSv_m v ω))).aestronglyMeasurable)
  let e_opt2 : Option Unit ≃ Fin 2 :=
    { toFun := fun o => match o with | some () => 0 | none => 1
      invFun := fun i => if i = 0 then some () else none
      left_inv := fun o => by cases o <;> simp
      right_inv := fun i => by fin_cases i <;> simp }
  have hIR_split (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      I_R (split_ext ω) =
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
          ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))) := by
    let ν_ω := ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))
    have hprob_ω : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    let G₂ (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
    have hG2_m : Measurable G₂ := by
      have hR_2 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ =>
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 0)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 1))))
      exact (hR_2.mul ((measurable_deriv u).comp ((hSv_m v ω).comp (measurable_pi_apply 0)))).mul
        ((measurable_deriv u).comp ((hSv_m v ω).comp (measurable_pi_apply 1)))
    let F_sR (σ : Option Unit → (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1 i : ℤ) : ℝ) * (((σ none).1 i : ℤ) : ℝ)) - q) *
        deriv u
          (α_sh (σ (some ())).1 ⬝ᵥ (split_ext ω).2 + α_aux (σ (some ())).1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1 ⬝ᵥ (split_ext ω).2 + α_aux (σ none).1 ⬝ᵥ (σ none).2)
    have ht1 : I_R (split_ext ω) =
        ∫ τ_o : Option Unit → (Fin (N + 1) → ℤˣ) × ℝ,
          F_sR (fun o => e_st (τ_o o)) ∂(Measure.pi fun _ : Option Unit => ν_ω) := by
      dsimp only [I_R, F_sR, ν_ω]
      rw [← htilted_st ω]
      exact integral_pi_map_equiv ν_ω e_st F_sR
    let e_pi := MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × ℝ) e_opt2
    have hmp_opt2 : MeasurePreserving ⇑e_pi
        (Measure.pi fun _ : Option Unit => ν_ω) (Measure.pi fun _ : Fin 2 => ν_ω) :=
      measurePreserving_piCongrLeft (fun _ : Fin 2 => ν_ω) e_opt2
    have h_opt := hmp_opt2.integral_comp_of_aestronglyMeasurable hG2_m.aestronglyMeasurable
    have ht2 (τ_o : Option Unit → (Fin (N + 1) → ℤˣ) × ℝ) :
        F_sR (fun o => e_st (τ_o o)) = (G₂ ∘ ⇑e_pi) τ_o := by
      have h0 : e_pi τ_o 0 = τ_o (some ()) := by
        change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × ℝ) e_opt2 τ_o) 0 = _
        rw [Equiv.piCongrLeft_apply]; rfl
      have h1 : e_pi τ_o 1 = τ_o none := by
        change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × ℝ) e_opt2 τ_o) 1 = _
        rw [Equiv.piCongrLeft_apply]; rfl
      dsimp only [F_sR, G₂, Function.comp_apply]
      rw [h0, h1, hS_eq ω (τ_o (some ())), hS_eq ω (τ_o none),
        he_st_apply (τ_o (some ())), he_st_apply (τ_o none)]
    rw [ht1]
    exact (integral_congr_ae (ae_of_all _ ht2)).trans h_opt
  have hIL_int : Integrable I_L (P_M.prod γ_sh) :=
    (hmp_ext.integrable_comp hIL_m.aestronglyMeasurable).1
      (hF'_int.congr (ae_of_all _ fun ω => (hIL_split ω).symm))
  have hIR_int : Integrable I_R (P_M.prod γ_sh) := by
    refine Integrable.of_bound hIR_m.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun p => ?_)
    have hVp_m : Measurable fun y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ) =>
        u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2) := by
      have ha1 : Measurable fun y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ) => α_sh y.1 ⬝ᵥ p.2 :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp measurable_fst).mul_const _
      have ha2 : Measurable fun y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ) => α_aux y.1 ⬝ᵥ y.2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
      exact hu.measurable.comp (ha1.add ha2)
    have hprob_p : IsProbabilityMeasure
        (((μ_M p.1).prod γ_aux).tilted fun y => u (α_sh y.1 ⬝ᵥ p.2 + α_aux y.1 ⬝ᵥ y.2)) :=
      isProbabilityMeasure_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun σ => by
      rw [abs_mul, abs_mul, sq]
      have hd_ov := abs_spin_overlap_sub_le_two hq (σ (some ())).1 (σ none).1
      calc _ ≤ 2 * |D₁| * |D₁| :=
            mul_le_mul (mul_le_mul hd_ov (hu.abs_deriv_le_abs _)
              (abs_nonneg _) zero_le_two) (hu.abs_deriv_le_abs _)
              (abs_nonneg _) (by positivity)
        _ = 2 * (|D₁| * |D₁|) := by ring
  have hlhs_eq : (∫ ω, F'_stmt ω ∂P_ext) = ∫ p, I_L p ∂(P_M.prod γ_sh) :=
    (integral_congr_ae (ae_of_all _ fun ω => (hIL_split ω).symm)).trans
      (hmp_ext.integral_comp_of_aestronglyMeasurable hIL_m.aestronglyMeasurable)
  have hrhs_eq :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
        ∂P_ext) =
      ∫ p, I_R p ∂(P_M.prod γ_sh) :=
    (integral_congr_ae (ae_of_all _ fun ω => (hIR_split ω).symm)).trans
      (hmp_ext.integral_comp_of_aestronglyMeasurable hIR_m.aestronglyMeasurable)
  rw [hlhs_eq, hrhs_eq, integral_prod I_L hIL_int, integral_prod I_R hIR_int,
    ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun g₀ =>
    secondProof_stein_fixed_disorder (N := N) (M := M) hu hq hv g₀)

/-- **Talagrand Section 2.4, Eq. (2.91) (first derivative and Gaussian IBP of the second proof's
cavity interpolation `φ(v)`):**
For `v ∈ (0, 1)`, `q ∈ [0, 1]`, and `u` satisfying `SmartPathPotential₂`, define
`φ(v) = 𝔼 log ∫_ξ ⟨exp u(√v S_M(τ) + √(1 - v)(√q z + √(1 - q) ξ))⟩ dγ(ξ)`, where the outer
expectation is over `(g₀, g_M, z)` and `⟨·⟩` is the `M`-constraint quenched Gibbs measure `μ_M g₀`.
Then `φ` is differentiable at `v` with derivative
$$-\frac{1}{2}\,\mathbb{E}\left[
  \int_{(\Sigma_{N+1} \times \mathbb{R})^2}
    (R_{1, 2} - q)\,u'(S_v^1)\,u'(S_v^2)\,
    \mathrm{d}\bigl((\mu_M(g_0) \otimes \gamma).\mathrm{tilted}(u \circ S_v)\bigr)^{\otimes 2}
\right].$$ -/
theorem hasDerivAt_second_proof_interpolation
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let P_ext := (P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ)).prod γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let S_v (v' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      Real.sqrt v' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - v') * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    HasDerivAt
      (fun v' => ∫ ω, Real.log (∫ x, Real.exp (u (S_v v' ω x)) ∂((μ_M ω.1.1).prod γ)) ∂P_ext)
      (-(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
        ∂P_ext) v := by
  intro γ P_M P_ext μ_M S_v
  obtain ⟨hd, hint⟩ := hasDerivAt_secondProof_logPartition (N := N) (M := M) (q := q) hu hv
  exact hd.congr_deriv (integral_secondProof_stein (N := N) (M := M) hu hq hv hint)

end SecondProofIncrement

end SpinGlasses
