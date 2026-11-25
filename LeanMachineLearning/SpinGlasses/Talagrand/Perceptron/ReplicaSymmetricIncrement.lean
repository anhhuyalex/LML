/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingHamiltonian
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ReplicaSymmetricVariational
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.OverlapConcentration
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianTiltedRotationBound
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaPairBound
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.TrigSquareParam
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IteratedDerivBounds
public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Units

/-!
# Discrete cavity increment and second-proof interpolation (Talagrand Section 2.4)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.90)--(2.93)
and the summation step of the second proof of Theorem 2.4.2.

For `N + 1` spins and `M` constraints, write `μ_M(g₀)` for the `M`-constraint quenched Gibbs measure
on `Fin (N + 1) → ℤˣ` and `S_M(τ) = (√(N + 1))⁻¹ ∑ᵢ g_{M, i} τᵢ` for the fresh constraint field.

## Main declarations

* `SpinGlasses.perceptron_pressure_succ_sub_eq`: Eq. (2.90), exact discrete cavity increment
  `p_{N+1, M+1}(u) - p_{N+1, M}(u) = (N + 1)⁻¹ 𝔼 log ⟨exp u(S_M)⟩`.
* `SpinGlasses.hasDerivAt_second_proof_interpolation`: Eq. (2.91), exact derivative and Gaussian IBP
  identity for `φ(v) = 𝔼 log 𝔼_ξ ⟨exp u(√v S_M + √(1 - v) θ)⟩` on `v ∈ (0, 1)`.
* `SpinGlasses.exists_hasDerivAt_second_proof_deriv_abs_le`: unconditional second-derivative bound
  `|φ''(v)| ≤ K_sec(D) * ν((R_{1, 2} - q)²)` on `v ∈ (0, 1)` under (2.7) and `q ∈ [0, 1]`.
* `SpinGlasses.exists_abs_perceptron_pressure_succ_sub_add_le`: unconditional discrete increment
  Taylor bound combining (2.90)--(2.92) without the Chapter 9 centered-overlap input.
* `SpinGlasses.abs_perceptron_pressure_succ_sub_le_of_centered_overlap`: conditional Eq. (2.93)
  under the explicit Chapter 9 centered-overlap hypothesis `|ν(R_{1, 2} - q)| ≤ K_bias / (N + 1)`.
* `SpinGlasses.abs_perceptron_pressure_sub_rs_le_of_centered_overlap`: conditional summation step
  completing the second proof of Theorem 2.4.2 at rate `(α / (N + 1)) * (C + (D² / 2) * K_bias)`
  under the explicit Chapter 9 centered-overlap hypothesis.
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

/-- Joint measurability of the `M`-constraint perceptron energy in `(g₀, τ)`. -/
private lemma measurable_perceptronEnergy_joint {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
      ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1 k i * ((p.2 i : ℤ) : ℝ)) := by
  refine Finset.measurable_sum _ fun k _ => hu.comp ?_
  refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
  have h1 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) => p.1 k i :=
    (measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_fst)
  have h2 : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
      ((p.2 i : ℤ) : ℝ) :=
    measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_snd)
  exact h1.mul h2

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
      E_M p.1 p.2 := measurable_perceptronEnergy_joint hu.measurable
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

/-- **Measurability and `I_R`-integrability of the split Stein integrands for (2.91).** -/
private lemma measurable_and_integrable_secondProof_stein_split
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (v : ℝ) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
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
    Measurable I_L ∧ Measurable I_R ∧ Integrable I_R (P_M.prod γ_sh) := by
  intro γ P_M μ_M γ_sh γ_aux α_sh W_sh α_aux W_aux I_L I_R
  let E_M (g₀ : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
  have hEM_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
      E_M p.1 p.2 := measurable_perceptronEnergy_joint hu.measurable
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
    exact hu.measurable.comp (hd1.add hd2)
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
  have hIR_int : Integrable I_R (P_M.prod γ_sh) := by
    refine Integrable.of_bound hIR_m.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun p => ?_)
    have hμM_prob : IsProbabilityMeasure (μ_M p.1) := isProbabilityMeasure_tilted (hEM_i p.1)
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
  exact ⟨hIL_m, hIR_m, hIR_int⟩

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
  obtain ⟨hIL_m, hIR_m, hIR_int⟩ :=
    measurable_and_integrable_secondProof_stein_split (N := N) (M := M) hu hq v
  let split_ext (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      (Fin M → Fin (N + 1) → ℝ) × ((Fin (N + 1) ⊕ Unit) → ℝ) :=
    (ω.1.1, Sum.elim ω.1.2 (fun _ : Unit => ω.2))
  have hmp_ext : MeasurePreserving split_ext P_ext (P_M.prod γ_sh) := by
    have hunit := (measurePreserving_funUnique γ Unit).symm
    have hsum := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin (N + 1) ⊕ Unit => ℝ)
      (fun _ => γ)).comp ((MeasurePreserving.id (Measure.pi fun _ : Fin (N + 1) => γ)).prod hunit)
    convert (((MeasurePreserving.id P_M).prod hsum).comp
      (measurePreserving_prodAssoc P_M (Measure.pi fun _ : Fin (N + 1) => γ) γ)) using 1
    ext ω : 1
    refine Prod.ext rfl (funext fun idx => ?_)
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

/-- Orthogonality and variance dot-product identities for the second-proof cavity rotation:
`X_sh τ = Sum.elim (i ↦ (√(N+1))⁻¹ τ_i) 0`, `Y_sh = Sum.elim 0 √q`, `X_aux = 0`,
`Y_aux = fun _ => √(1 - q)`. -/
private lemma secondProof_rotation_dotProducts {N : ℕ} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    let X_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ)) 0
    let Y_sh : (Fin (N + 1) ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let X_aux : Unit → ℝ := 0
    let Y_aux : Unit → ℝ := fun _ => Real.sqrt (1 - q)
    (∀ τ : Fin (N + 1) → ℤˣ, X_sh τ ⬝ᵥ Y_sh = 0) ∧
    (X_aux ⬝ᵥ Y_aux = 0) ∧
    (∀ τ : Fin (N + 1) → ℤˣ, X_sh τ ⬝ᵥ X_sh τ + X_aux ⬝ᵥ X_aux = 1) ∧
    (Y_sh ⬝ᵥ Y_sh + Y_aux ⬝ᵥ Y_aux = 1) ∧
    (∀ τ₁ τ₂ : Fin (N + 1) → ℤˣ,
      Y_sh ⬝ᵥ Y_sh - X_sh τ₁ ⬝ᵥ X_sh τ₂ =
        q - ((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) := by
  intro X_sh Y_sh X_aux Y_aux
  have h1q : 0 ≤ 1 - q := sub_nonneg.2 hq.2
  have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsq_inv : ((Real.sqrt (N + 1 : ℕ))⁻¹) ^ 2 = ((N : ℝ) + 1)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ; simp [X_sh, Y_sh, dotProduct]
  · simp [X_aux, Y_aux, dotProduct]
  · intro τ
    simp only [X_sh, X_aux, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    have hsum : (∑ i : Fin (N + 1),
        (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))) =
        ((Real.sqrt (N + 1 : ℕ))⁻¹) ^ 2 * ((N : ℝ) + 1) := by
      have hterm (i : Fin (N + 1)) :
          (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ)) =
          ((Real.sqrt (N + 1 : ℕ))⁻¹) ^ 2 := by
        have hsq : (((τ i : ℤ) : ℝ)) ^ 2 = 1 := units_cast_sq _
        linear_combination (((Real.sqrt (N + 1 : ℕ))⁻¹) ^ 2) * hsq
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [hsum, hsq_inv, inv_mul_cancel₀ hL_pos.ne']
  · have hy : Y_sh ⬝ᵥ Y_sh = q := by
      simp [Y_sh, dotProduct, ← sq, Real.sq_sqrt hq.1]
    have hya : Y_aux ⬝ᵥ Y_aux = 1 - q := by
      simp [Y_aux, dotProduct, ← sq, Real.sq_sqrt h1q]
    rw [hy, hya]; ring
  · intro τ₁ τ₂
    have hy : Y_sh ⬝ᵥ Y_sh = q := by
      simp [Y_sh, dotProduct, ← sq, Real.sq_sqrt hq.1]
    have hx : X_sh τ₁ ⬝ᵥ X_sh τ₂ =
        ((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ) := by
      simp only [X_sh, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← hsq_inv, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hy, hx]

/-- Let-free joint measurability of the second-proof angle field in `(w, (τ, η))`. -/
private lemma measurable_secondProof_angle_field {N : ℕ} (q s : ℝ) :
    Measurable fun p : ((Fin (N + 1) ⊕ Unit) → ℝ) × ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
      Real.cos s *
        ((Sum.elim (fun i : Fin (N + 1) => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((p.2.1 i : ℤ) : ℝ))
          (0 : Unit → ℝ)) ⬝ᵥ p.1 + (0 : Unit → ℝ) ⬝ᵥ p.2.2) +
      Real.sin s *
        ((Sum.elim (0 : Fin (N + 1) → ℝ) (fun _ : Unit => Real.sqrt q)) ⬝ᵥ p.1 +
          (fun _ : Unit => Real.sqrt (1 - q)) ⬝ᵥ p.2.2) := by
  have hX (idx : Fin (N + 1) ⊕ Unit) :
      Measurable fun p : ((Fin (N + 1) ⊕ Unit) → ℝ) × ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
        (Sum.elim (fun i : Fin (N + 1) => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((p.2.1 i : ℤ) : ℝ))
          (0 : Unit → ℝ)) idx :=
    (measurable_of_finite fun (τ : Fin (N + 1) → ℤˣ) =>
      (Sum.elim (fun i : Fin (N + 1) => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (0 : Unit → ℝ)) idx).comp (measurable_fst.comp measurable_snd)
  have hdotX : Measurable fun p :
      ((Fin (N + 1) ⊕ Unit) → ℝ) × ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
      (Sum.elim (fun i : Fin (N + 1) => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((p.2.1 i : ℤ) : ℝ))
        (0 : Unit → ℝ)) ⬝ᵥ p.1 :=
    Finset.measurable_sum _ fun idx _ =>
      (hX idx).mul ((measurable_pi_apply idx).comp measurable_fst)
  have hdotY : Measurable fun p :
      ((Fin (N + 1) ⊕ Unit) → ℝ) × ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
      (Sum.elim (0 : Fin (N + 1) → ℝ) (fun _ : Unit => Real.sqrt q)) ⬝ᵥ p.1 :=
    Finset.measurable_sum _ fun idx _ =>
      measurable_const.mul ((measurable_pi_apply idx).comp measurable_fst)
  have hdotXa : Measurable fun p :
      ((Fin (N + 1) ⊕ Unit) → ℝ) × ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
      (0 : Unit → ℝ) ⬝ᵥ p.2.2 := by
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    exact measurable_const
  have hdotYa : Measurable fun p :
      ((Fin (N + 1) ⊕ Unit) → ℝ) × ((Fin (N + 1) → ℤˣ) × (Unit → ℝ)) =>
      (fun _ : Unit => Real.sqrt (1 - q)) ⬝ᵥ p.2.2 :=
    Finset.measurable_sum _ fun idx _ =>
      measurable_const.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_snd))
  exact ((hdotX.add hdotXa).const_mul _).add ((hdotY.add hdotYa).const_mul _)

/-- Let-free slice measurability of the second-proof angle field in `(τ, η)` at fixed `w`. -/
private lemma measurable_secondProof_angle_field_slice {N : ℕ} (q s : ℝ)
    (w : (Fin (N + 1) ⊕ Unit) → ℝ) :
    Measurable fun y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ) =>
      Real.cos s *
        ((Sum.elim (fun i : Fin (N + 1) => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((y.1 i : ℤ) : ℝ))
          (0 : Unit → ℝ)) ⬝ᵥ w + (0 : Unit → ℝ) ⬝ᵥ y.2) +
      Real.sin s *
        ((Sum.elim (0 : Fin (N + 1) → ℝ) (fun _ : Unit => Real.sqrt q)) ⬝ᵥ w +
          (fun _ : Unit => Real.sqrt (1 - q)) ⬝ᵥ y.2) :=
  measurable_rotation_field measurable_id
    (fun τ : Fin (N + 1) → ℤˣ =>
      Sum.elim (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ)) 0)
    (fun _ => Sum.elim 0 (fun _ => Real.sqrt q))
    (fun _ => 0)
    (fun _ => fun _ => Real.sqrt (1 - q)) s w

/-- Transport between `(P_ext, (μ_M g₀).prod γ)` in `(cos s, sin s)` coordinates and
`(P_M.prod γ_sh, (μ_M g₀).prod γ_aux)` in angle `s` coordinates for the two-replica integrand of
`φ'(v)`. -/
private lemma integral_secondProof_deriv_eq_angle
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B D₁ : ℝ}
    (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (s : ℝ) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let P_ext := (P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ)).prod γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ
    let γ_aux := Measure.pi fun _ : Unit => γ
    let X_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ)) 0
    let Y_sh : (Fin (N + 1) ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let X_aux : Unit → ℝ := 0
    let Y_aux : Unit → ℝ := fun _ => Real.sqrt (1 - q)
    let S_ang (w : (Fin (N + 1) ⊕ Unit) → ℝ) (y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      Real.cos s * (X_sh y.1 ⬝ᵥ w + X_aux ⬝ᵥ y.2) +
        Real.sin s * (Y_sh ⬝ᵥ w + Y_aux ⬝ᵥ y.2)
    let S_cs (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      Real.cos s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
        Real.sin s * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_cs ω (σ 0)) * deriv u (S_cs ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_cs ω x)))
        ∂P_ext =
      ∫ g₀, ∫ w, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          ∏ r : Fin 2, deriv u (S_ang w (σ r))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M g₀).prod γ_aux).tilted (fun y => u (S_ang w y)))
        ∂γ_sh ∂P_M := by
  intro γ P_M P_ext μ_M γ_sh γ_aux X_sh Y_sh X_aux Y_aux S_ang S_cs
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hμM_prob (g₀ : Fin M → Fin (N + 1) → ℝ) : IsProbabilityMeasure (μ_M g₀) :=
    isProbabilityMeasure_tilted Integrable.of_finite
  let Ω₀ := Fin M → Fin (N + 1) → ℝ
  let W := (Fin (N + 1) ⊕ Unit) → ℝ
  let T := (Fin (N + 1) → ℤˣ) × (Unit → ℝ)
  let split_ext (ω : (Ω₀ × (Fin (N + 1) → ℝ)) × ℝ) : Ω₀ × W :=
    (ω.1.1, Sum.elim ω.1.2 (fun _ : Unit => ω.2))
  have hmp_ext : MeasurePreserving split_ext P_ext (P_M.prod γ_sh) := by
    have hunit := (measurePreserving_funUnique γ Unit).symm
    have hsum := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin (N + 1) ⊕ Unit => ℝ)
      (fun _ => γ)).comp ((MeasurePreserving.id (Measure.pi fun _ : Fin (N + 1) => γ)).prod hunit)
    convert (((MeasurePreserving.id P_M).prod hsum).comp
      (measurePreserving_prodAssoc P_M (Measure.pi fun _ : Fin (N + 1) => γ) γ)) using 1
    ext ω : 1
    refine Prod.ext rfl (funext fun idx => ?_)
    rcases idx with i | _ <;>
      simp [split_ext, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]
  let e_st : ((Fin (N + 1) → ℤˣ) × ℝ) ≃ᵐ T :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.funUnique Unit ℝ).symm
  have he_st_apply (x : (Fin (N + 1) → ℤˣ) × ℝ) : e_st x = (x.1, fun _ => x.2) := rfl
  have hmp_st (g₀ : Ω₀) : MeasurePreserving ⇑e_st ((μ_M g₀).prod γ) ((μ_M g₀).prod γ_aux) :=
    (MeasurePreserving.id (μ_M g₀)).prod (measurePreserving_funUnique γ Unit).symm
  have hS_eq (ω : (Ω₀ × (Fin (N + 1) → ℝ)) × ℝ) (x : (Fin (N + 1) → ℤˣ) × ℝ) :
      S_ang (split_ext ω).2 (e_st x) = S_cs ω x := by
    rw [he_st_apply]
    dsimp only [S_ang, S_cs, X_sh, Y_sh, X_aux, Y_aux, split_ext]
    rw [sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add]
    congr 1
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hScs_m (ω : (Ω₀ × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S_cs ω x :=
    (((Finset.measurable_sum _ fun i _ => measurable_const.mul
      (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))).const_mul _
      ).const_mul _).add ((measurable_const.add (measurable_snd.const_mul _)).const_mul _)
  have htilted_st (ω : (Ω₀ × (Fin (N + 1) → ℝ)) × ℝ) :
      (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_cs ω x))).map e_st =
      ((μ_M (split_ext ω).1).prod γ_aux).tilted (fun y => u (S_ang (split_ext ω).2 y)) := by
    have hVm : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => u (S_cs ω x) :=
      hu.comp (hScs_m ω)
    rw [map_tilted_measurableEquiv e_st (hmp_st ω.1.1) hVm]
    congr 1; funext y
    obtain ⟨x, rfl⟩ := e_st.surjective y
    dsimp only [Function.comp_apply]
    rw [MeasurableEquiv.symm_apply_apply, hS_eq ω x]
  obtain ⟨I_ang, hI_ang⟩ : ∃ I_ang : Ω₀ × W → ℝ, ∀ p, I_ang p =
      ∫ σ : Fin 2 → T,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          ∏ r : Fin 2, deriv u (S_ang p.2 (σ r))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M p.1).prod γ_aux).tilted (fun y => u (S_ang p.2 y))) :=
    ⟨_, fun _ => rfl⟩
  have hIang_m : Measurable I_ang := by
    rw [show I_ang = _ from funext hI_ang]
    let V_obs (p : Ω₀ × W) (y : T) : ℝ := u (S_ang p.2 y)
    let F_obs (p : Ω₀ × W) (σ : Fin 2 → T) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        ∏ r : Fin 2, deriv u (S_ang p.2 (σ r))
    have hSang_m : Measurable fun p : W × T => S_ang p.1 p.2 :=
      measurable_secondProof_angle_field q s
    have hpV : Measurable fun q_p : (Ω₀ × W) × T => (q_p.1.2, q_p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hsV := hSang_m.comp hpV
    have hVm : Measurable fun q_p : (Ω₀ × W) × T => V_obs q_p.1 q_p.2 := hu.comp hsV
    have hFm : Measurable fun q_p : (Ω₀ × W) × (Fin 2 → T) => F_obs q_p.1 q_p.2 := by
      have hov : Measurable fun q_p : (Ω₀ × W) × (Fin 2 → T) =>
          ((((N : ℝ) + 1)⁻¹ * ∑ i,
            ((((q_p.2 0).1 i : ℤ) : ℝ) * (((q_p.2 1).1 i : ℤ) : ℝ))) - q) := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))))
      have hpr : Measurable fun q_p : (Ω₀ × W) × (Fin 2 → T) =>
          ∏ r : Fin 2, deriv u (S_ang q_p.1.2 (q_p.2 r)) := by
        refine Finset.measurable_prod _ fun r _ => ?_
        have hpr_r : Measurable fun q_p : (Ω₀ × W) × (Fin 2 → T) => (q_p.1.2, q_p.2 r) :=
          (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)
        have hsr := hSang_m.comp hpr_r
        exact (measurable_deriv u).comp hsr
      exact hov.mul hpr
    let E_M (g₀ : Ω₀) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
      ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
    have hEM_m : Measurable fun p : Ω₀ × (Fin (N + 1) → ℤˣ) => E_M p.1 p.2 :=
      measurable_perceptronEnergy_joint hu
    have hEM_i (g₀ : Ω₀) : Integrable (fun τ => Real.exp (E_M g₀ τ)) Measure.count :=
      Integrable.of_finite
    exact measurable_integral_pi_tilted_prod_tilted
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)) γ_aux hEM_m hEM_i hVm hFm
  have hpt (ω : (Ω₀ × (Fin (N + 1) → ℝ)) × ℝ) :
      I_ang (split_ext ω) =
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_cs ω (σ 0)) * deriv u (S_cs ω (σ 1))
          ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_cs ω x))) := by
    rw [hI_ang]
    let ν_ω := ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_cs ω x))
    have hprob_ω : IsProbabilityMeasure ν_ω :=
      isProbabilityMeasure_tilted_of_ae_le (hu.comp (hScs_m ω)).aemeasurable
        (ae_of_all _ fun _ => hB_le _)
    let F_ang (σ : Fin 2 → T) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        ∏ r : Fin 2, deriv u (S_ang (split_ext ω).2 (σ r))
    have ht1 : (∫ σ : Fin 2 → T, F_ang σ
        ∂(Measure.pi fun _ : Fin 2 =>
          ((μ_M (split_ext ω).1).prod γ_aux).tilted (fun y => u (S_ang (split_ext ω).2 y)))) =
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
          F_ang (fun r => e_st (σ r)) ∂(Measure.pi fun _ : Fin 2 => ν_ω) := by
      dsimp only [F_ang, ν_ω]
      rw [← htilted_st ω]
      exact integral_pi_map_equiv ν_ω e_st F_ang
    rw [ht1]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp only [F_ang]
    rw [Fin.prod_univ_two, hS_eq ω (σ 0), hS_eq ω (σ 1), he_st_apply (σ 0), he_st_apply (σ 1),
      ← mul_assoc]
  have hIang_int : Integrable I_ang (P_M.prod γ_sh) := by
    refine Integrable.of_bound hIang_m.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun p => ?_)
    rw [hI_ang]
    have hVp_m : Measurable fun y : T => u (S_ang p.2 y) :=
      hu.comp (measurable_secondProof_angle_field_slice (N := N) q s p.2)
    have hprob_p : IsProbabilityMeasure (((μ_M p.1).prod γ_aux).tilted fun y => u (S_ang p.2 y)) :=
      isProbabilityMeasure_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hB_le _)
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun σ => by
      rw [abs_mul, Fin.prod_univ_two, abs_mul, sq]
      have hd_ov := abs_spin_overlap_sub_le_two hq (σ 0).1 (σ 1).1
      exact mul_le_mul hd_ov (mul_le_mul ((hD₁ _).trans (le_abs_self _))
        ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
        (by positivity) zero_le_two
  refine (integral_congr_ae (ae_of_all _ fun ω => (hpt ω).symm)).trans ?_
  rw [hmp_ext.integral_comp_of_aestronglyMeasurable hIang_m.aestronglyMeasurable,
    integral_prod I_ang hIang_int]
  exact integral_congr_ae (ae_of_all _ fun g₀ => integral_congr_ae (ae_of_all _ fun w =>
    hI_ang (g₀, w)))

/-- **Angle-derivative bound for the second-proof cavity interpolation:**
differentiating `s ↦ ∫ g₀, ∫ w, ⟨(R_{1,2} - q) u'(S_s^1) u'(S_s^2)⟩ ∂γ_sh ∂P_M` brings down a
second factor of `R_{ℓ, ℓ'} - q` across the four replica groups, bounded via Cauchy-Schwarz and
boundedness of the cavity tilt (`exp (8 |D|)`) by `K(D) * ν((R_{1, 2} - q)²)`. -/
private lemma exists_hasDerivAt_secondProof_angle_abs_le
    {N M : ℕ} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    {u : ℝ → ℝ} {D : ℝ}
    (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
    (s₀ : ℝ) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ
    let γ_aux := Measure.pi fun _ : Unit => γ
    let X_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ)) 0
    let Y_sh : (Fin (N + 1) ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let X_aux : Unit → ℝ := 0
    let Y_aux : Unit → ℝ := fun _ => Real.sqrt (1 - q)
    let S_ang (s : ℝ) (w : (Fin (N + 1) ⊕ Unit) → ℝ) (y : (Fin (N + 1) → ℤˣ) × (Unit → ℝ)) : ℝ :=
      Real.cos s * (X_sh y.1 ⬝ᵥ w + X_aux ⬝ᵥ y.2) +
        Real.sin s * (Y_sh ⬝ᵥ w + Y_aux ⬝ᵥ y.2)
    let L : ℝ := 1 + 3 * |D| + |D| ^ 2
    ∃ z,
      HasDerivAt
        (fun s => ∫ g₀, ∫ w, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              ∏ r : Fin 2, deriv u (S_ang s w (σ r))
            ∂(Measure.pi fun _ : Fin 2 => ((μ_M g₀).prod γ_aux).tilted (fun y => u (S_ang s w y)))
            ∂γ_sh ∂P_M)
        (Real.sin s₀ * Real.cos s₀ * z) s₀ ∧
      |z| ≤ 18 * L ^ 4 * Real.exp (8 * |D|) *
        ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M := by
  intro γ P_M μ_M γ_sh γ_aux X_sh Y_sh X_aux Y_aux S_ang L
  obtain ⟨hu, h2d, hb3⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hB_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  have hB_le : ∀ x, u x ≤ |D| := fun x => le_of_abs_le (hB_abs x)
  let Ω₀ := Fin M → Fin (N + 1) → ℝ
  let α := Fin (N + 1) → ℤˣ
  let W := (Fin (N + 1) ⊕ Unit) → ℝ
  let T := α × (Unit → ℝ)
  have hμM_prob (g₀ : Ω₀) : IsProbabilityMeasure (μ_M g₀) :=
    isProbabilityMeasure_tilted Integrable.of_finite
  let E_M (g₀ : Ω₀) (τ : α) : ℝ :=
    ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
  have hEM_m : Measurable fun p : Ω₀ × α => E_M p.1 p.2 :=
    measurable_perceptronEnergy_joint hu.measurable
  have hEM_i (g₀ : Ω₀) : Integrable (fun τ => Real.exp (E_M g₀ τ)) Measure.count :=
    Integrable.of_finite
  let f_ov (a : Fin 2 → α) : ℝ :=
    (((N : ℝ) + 1)⁻¹ * ∑ i, ((a 0 i : ℤ) : ℝ) * ((a 1 i : ℤ) : ℝ)) - q
  let d_ov (τ₁ τ₂ : α) : ℝ := |(((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) - q|
  have hd_le2 (τ₁ τ₂ : α) : d_ov τ₁ τ₂ ≤ 2 := abs_spin_overlap_sub_le_two hq τ₁ τ₂
  have hf_le2 (a : Fin 2 → α) : |f_ov a| ≤ 2 := hd_le2 (a 0) (a 1)
  have hSang_m (s : ℝ) : Measurable fun p : W × T => S_ang s p.1 p.2 :=
    measurable_secondProof_angle_field q s
  have hV_slice (s : ℝ) (w : W) : Measurable fun y : T => u (S_ang s w y) :=
    hu.measurable.comp (measurable_secondProof_angle_field_slice (N := N) q s w)
  let ν (p : Ω₀ × W) : Measure T := ((μ_M p.1).prod γ_aux).tilted fun y => u (S_ang s₀ p.2 y)
  have hν_prob (p : Ω₀ × W) : IsProbabilityMeasure (ν p) :=
    isProbabilityMeasure_tilted_of_ae_le (hV_slice s₀ p.2).aemeasurable
      (ae_of_all _ fun _ => hB_le _)
  have hmν {ι : Type} [Fintype ι] {G : Ω₀ × W → (ι → T) → ℝ}
      (hG : Measurable fun p : (Ω₀ × W) × (ι → T) => G p.1 p.2) :
      Measurable fun p => ∫ a, G p a ∂(Measure.pi fun _ : ι => ν p) := by
    let V_obs (p : Ω₀ × W) (y : T) : ℝ := u (S_ang s₀ p.2 y)
    have hpV : Measurable fun p : (Ω₀ × W) × T => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hsV := (hSang_m s₀).comp hpV
    have hVm : Measurable fun p : (Ω₀ × W) × T => V_obs p.1 p.2 := hu.measurable.comp hsV
    exact measurable_integral_pi_tilted_prod_tilted
      (Measure.count : Measure α) γ_aux hEM_m hEM_i hVm hG
  -- Bound the mixed pair moment on `ν` by `exp (8 |D|) * Q_val`!
  let Q_val : ℝ := ∫ g₀, ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M
  have hQ0 : 0 ≤ Q_val := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hQ_m : Measurable fun g₀ : Ω₀ =>
      ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) :=
    measurable_integral_pi_tilted (μ := (Measure.count : Measure α)) hEM_m
      ((measurable_of_finite fun τ : Fin 2 → α => f_ov τ ^ 2).comp measurable_snd)
  have hQ_int : Integrable (fun g₀ : Ω₀ =>
      ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀)) P_M :=
    Integrable.of_bound hQ_m.aestronglyMeasurable 4 (ae_of_all _ fun g₀ => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun τ => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf_le2 τ) 2 |>.trans (by norm_num))
  obtain ⟨horth_sh, horth_aux, hvar_X, hvar_Y, hcov⟩ := secondProof_rotation_dotProducts (N := N) hq
  let C_cov (τ₁ τ₂ : α) : ℝ := Y_sh ⬝ᵥ Y_sh - X_sh τ₁ ⬝ᵥ X_sh τ₂
  have hc_abs (τ₁ τ₂ : α) : |C_cov τ₁ τ₂| = d_ov τ₁ τ₂ := by
    change |Y_sh ⬝ᵥ Y_sh - X_sh τ₁ ⬝ᵥ X_sh τ₂| = d_ov τ₁ τ₂
    rw [hcov τ₁ τ₂]
    dsimp only [d_ov]
    exact abs_sub_comm _ _
  let K : ℝ := L ^ 4
  have hL1 : 1 ≤ L := by dsimp only [L]; nlinarith [abs_nonneg D]
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  let m_pair : ℝ := Real.exp (8 * |D|) * Q_val
  have hm0 : 0 ≤ m_pair := mul_nonneg (Real.exp_pos _).le hQ0
  have hTerm {ι : Type} [Fintype ι] (hcard : Fintype.card ι ≤ 4)
      (e : Fin 2 → ι) (he : Function.Injective e) (i j : ι) (hij : i ≠ j)
      (H : Ω₀ × W → (ι → T) → ℝ)
      (hHm : Measurable fun x : (Ω₀ × W) × (ι → T) => H x.1 x.2)
      (hHb : ∀ p a, |H p a| ≤ K) :
      let J (g₀ : Ω₀) := ∫ w, ∫ a : ι → T,
        f_ov (fun r => (a (e r)).1) * C_cov (a i).1 (a j).1 * H (g₀, w) a
        ∂(Measure.pi fun _ : ι => ν (g₀, w)) ∂γ_sh
      Integrable J P_M ∧ |∫ g₀, J g₀ ∂P_M| ≤ K * m_pair := by
    intro J
    let T_obs (p : Ω₀ × W) (a : ι → T) : ℝ :=
      f_ov (fun r => (a (e r)).1) * C_cov (a i).1 (a j).1 * H p a
    have hTm : Measurable fun x : (Ω₀ × W) × (ι → T) => T_obs x.1 x.2 := by
      have h_spin (k : ι) ( idx : Fin (N + 1)) :
          Measurable fun x : (Ω₀ × W) × (ι → T) => (((x.2 k).1 idx : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply idx).comp
          (measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)))
      have h1 : Measurable fun x : (Ω₀ × W) × (ι → T) => f_ov (fun r => (x.2 (e r)).1) :=
        ((Finset.measurable_sum _ fun idx _ =>
          (h_spin (e 0) idx).mul (h_spin (e 1) idx)).const_mul _).sub_const q
      have h2 : Measurable fun x : (Ω₀ × W) × (ι → T) => C_cov (x.2 i).1 (x.2 j).1 := by
        have hc_eq : (fun x : (Ω₀ × W) × (ι → T) => C_cov (x.2 i).1 (x.2 j).1) =
            fun x => q - ((N : ℝ) + 1)⁻¹ *
              ∑ idx, (((x.2 i).1 idx : ℤ) : ℝ) * (((x.2 j).1 idx : ℤ) : ℝ) :=
          funext fun x => hcov (x.2 i).1 (x.2 j).1
        rw [hc_eq]
        exact measurable_const.sub ((Finset.measurable_sum _ fun idx _ =>
          (h_spin i idx).mul (h_spin j idx)).const_mul _)
      exact (h1.mul h2).mul hHm
    have hT_int_m : Measurable fun p : Ω₀ × W =>
        ∫ a : ι → T, T_obs p a ∂(Measure.pi fun _ : ι => ν p) := hmν hTm
    have hJm : Measurable J := by
      dsimp only [J, γ_sh]
      exact (hT_int_m.stronglyMeasurable.integral_prod_right'
        (ν := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ)).measurable
    let Φ (b : ι → α) : ℝ := (1 / 2) * (f_ov (b ∘ e) ^ 2 + f_ov (fun r => b (![i, j] r)) ^ 2)
    have hΦ0 (b : ι → α) : 0 ≤ Φ b := by dsimp only [Φ]; positivity
    have hprod_le_Φ (b : ι → α) : |f_ov (b ∘ e)| * |C_cov (b i) (b j)| ≤ Φ b := by
      rw [hc_abs]
      have hd_eq : d_ov (b i) (b j) = |f_ov (fun r => b (![i, j] r))| := by
        dsimp only [d_ov, f_ov]; rfl
      rw [hd_eq]
      have hsq1 : |f_ov (b ∘ e)| ^ 2 = f_ov (b ∘ e) ^ 2 := sq_abs _
      have hsq2 : |f_ov (fun r => b (![i, j] r))| ^ 2 = f_ov (fun r => b (![i, j] r)) ^ 2 :=
        sq_abs _
      dsimp only [Φ]
      nlinarith [sq_nonneg (|f_ov (b ∘ e)| - |f_ov (fun r => b (![i, j] r))|)]
    have hΦ_avg (g₀ : Ω₀) :
        ∫ b : ι → α, Φ b ∂(Measure.pi fun _ : ι => μ_M g₀) =
          ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) := by
      have hij_inj : Function.Injective (![i, j] : Fin 2 → ι) := by
        intro r₁ r₂ hr
        fin_cases r₁ <;> fin_cases r₂ <;> simp_all [Ne.symm hij]
      have h1 : ∫ b : ι → α, f_ov (b ∘ e) ^ 2 ∂(Measure.pi fun _ : ι => μ_M g₀) =
          ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) :=
        integral_pi_comp_injective (μ_M g₀) he (fun τ => f_ov τ ^ 2)
          Integrable.of_finite.aestronglyMeasurable
      have h2 : ∫ b : ι → α, f_ov (fun r => b (![i, j] r)) ^ 2
          ∂(Measure.pi fun _ : ι => μ_M g₀) =
          ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) :=
        integral_pi_comp_injective (μ_M g₀) hij_inj (fun τ => f_ov τ ^ 2)
          Integrable.of_finite.aestronglyMeasurable
      dsimp only [Φ]
      rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite, h1, h2]
      ring
    have hJ_pt (g₀ : Ω₀) :
        |J g₀| ≤ K * Real.exp (8 * |D|) *
          ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) := by
      dsimp only [J]
      refine abs_integral_le_of_forall_abs_le γ_sh fun w => ?_
      obtain ⟨hΦ_tilt, hΦ_comp⟩ := integrable_pi_tilted_prod_fst_abs_and_le
        (ι := ι) (R := ι) (μ_M g₀) γ_aux (hV_slice s₀ w) (fun _ => hB_abs _)
        Function.injective_id (f := Φ) Integrable.of_finite
      have hexp_le : Real.exp (2 * (Fintype.card ι : ℝ) * |D|) ≤ Real.exp (8 * |D|) := by
        refine Real.exp_le_exp.2 ?_
        have hc4 : (Fintype.card ι : ℝ) ≤ 4 := by exact_mod_cast hcard
        nlinarith [abs_nonneg D]
      have hΦ_abs_eq : (∫ b : ι → α, |Φ b| ∂(Measure.pi fun _ : ι => μ_M g₀)) =
          ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) := by
        rw [integral_congr_ae (ae_of_all _ fun b => abs_of_nonneg (hΦ0 b)), hΦ_avg g₀]
      calc |∫ a : ι → T, f_ov (fun r => (a (e r)).1) * C_cov (a i).1 (a j).1 * H (g₀, w) a
              ∂(Measure.pi fun _ : ι => ν (g₀, w))|
          ≤ ∫ a : ι → T, |f_ov (fun r => (a (e r)).1) * C_cov (a i).1 (a j).1 * H (g₀, w) a|
              ∂(Measure.pi fun _ : ι => ν (g₀, w)) := abs_integral_le_integral_abs
        _ ≤ ∫ a : ι → T, K * |Φ (fun r => (a r).1)| ∂(Measure.pi fun _ : ι => ν (g₀, w)) := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
              (hΦ_tilt.const_mul K) (ae_of_all _ fun a => ?_)
            dsimp only
            rw [abs_mul, abs_mul, abs_of_nonneg (hΦ0 _), mul_comm K]
            exact mul_le_mul (hprod_le_Φ (fun r => (a r).1)) (hHb (g₀, w) a)
              (abs_nonneg _) (hΦ0 _)
        _ = K * ∫ a : ι → T, |Φ (fun r => (a r).1)| ∂(Measure.pi fun _ : ι => ν (g₀, w)) :=
            integral_const_mul _ _
        _ ≤ K * (Real.exp (2 * (Fintype.card ι : ℝ) * |D|) *
              ∫ b : ι → α, |Φ b| ∂(Measure.pi fun _ : ι => μ_M g₀)) :=
            mul_le_mul_of_nonneg_left hΦ_comp hK0
        _ = K * Real.exp (2 * (Fintype.card ι : ℝ) * |D|) *
              ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) := by
            rw [hΦ_abs_eq]; ring
        _ ≤ K * Real.exp (8 * |D|) *
              ∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le hK0)
              (integral_nonneg fun _ => sq_nonneg _)
    have hJ_int : Integrable J P_M :=
      (hQ_int.const_mul (K * Real.exp (8 * |D|))).mono' hJm.aestronglyMeasurable
        (ae_of_all _ fun g₀ => by rw [Real.norm_eq_abs]; exact hJ_pt g₀)
    refine ⟨hJ_int, ?_⟩
    calc |∫ g₀, J g₀ ∂P_M|
        ≤ ∫ g₀, |J g₀| ∂P_M := abs_integral_le_integral_abs
      _ ≤ ∫ g₀, K * Real.exp (8 * |D|) *
            (∫ τ : Fin 2 → α, f_ov τ ^ 2 ∂(Measure.pi fun _ : Fin 2 => μ_M g₀)) ∂P_M :=
          integral_mono hJ_int.abs (hQ_int.const_mul _) hJ_pt
      _ = K * m_pair := by rw [integral_const_mul]; dsimp only [m_pair, Q_val]; ring
  let ψ_d (x : ℝ) : ℝ := deriv (deriv u) x + deriv u x * deriv u x
  have hψm : Measurable (deriv u) := measurable_deriv u
  have hψdm : Measurable ψ_d := (measurable_deriv _).add (hψm.mul hψm)
  have hDu_L (x : ℝ) : |deriv u x| ≤ L :=
    (hu.abs_deriv_le_abs x).trans (by dsimp only [L]; nlinarith [abs_nonneg D])
  have hψd_L (x : ℝ) : |ψ_d x| ≤ L := by
    dsimp only [ψ_d]
    have h1 := (hu.abs_deriv₂_le x).trans (le_abs_self D)
    have h2 : |deriv u x * deriv u x| ≤ |D| ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul (hu.abs_deriv_le_abs x) (hu.abs_deriv_le_abs x)
        (abs_nonneg _) (abs_nonneg _)
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans (by
      dsimp only [L]; linarith [abs_nonneg D]))
  have hfield {ι : Type} (i : ι) :
      Measurable fun x : (Ω₀ × W) × (ι → T) => S_ang s₀ x.1.2 (x.2 i) := by
    have hp : Measurable fun x : (Ω₀ × W) × (ι → T) => (x.1.2, x.2 i) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
    have hs := (hSang_m s₀).comp hp
    exact hs
  have hprod {ι : Type} (e : Fin 2 → ι) (U : Finset (Fin 2)) (p : Ω₀ × W) (a : ι → T) :
      |∏ r ∈ U, deriv u (S_ang s₀ p.2 (a (e r)))| ≤ L ^ 2 := by
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _r ∈ U, L := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun _ _ => hDu_L _
      _ = L ^ U.card := Finset.prod_const _
      _ ≤ L ^ 2 := pow_le_pow_right₀ hL1 ((Finset.card_le_univ U).trans_eq (Fintype.card_fin 2))
  have hprod_m {ι : Type} (e : Fin 2 → ι) (U : Finset (Fin 2)) :
      Measurable fun x : (Ω₀ × W) × (ι → T) => ∏ r ∈ U, deriv u (S_ang s₀ x.1.2 (x.2 (e r))) := by
    refine Finset.measurable_prod _ fun r _ => ?_
    have hf_r := hfield (e r)
    exact hψm.comp hf_r
  have hthree (a b g : ℝ) (ha : |a| ≤ L) (hb_a : |b| ≤ L) (hg : |g| ≤ L ^ 2) :
      |a * b * g| ≤ K := by
    rw [abs_mul, abs_mul]
    calc _ ≤ L * L * L ^ 2 :=
          mul_le_mul (mul_le_mul ha hb_a (abs_nonneg _) (zero_le_one.trans hL1)) hg
            (abs_nonneg _) (by positivity)
      _ = K := by dsimp only [K]; ring
  let e₁ : Fin 2 → Option (Fin 2) := some
  let e₂ : Fin 2 → Option (Option (Fin 2)) := fun r => some (some r)
  have he₁ : Function.Injective e₁ := Option.some_injective _
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp he₁
  let G₀ (i j : Fin 2) (p : Ω₀ × W) (a : Fin 2 → T) : ℝ :=
    ψ_d (S_ang s₀ p.2 (a i)) * ψ_d (S_ang s₀ p.2 (a j)) *
      ∏ r ∈ (Finset.univ.erase i).erase j, deriv u (S_ang s₀ p.2 (a r))
  let G₁ (i : Fin 2) (p : Ω₀ × W) (a : Option (Fin 2) → T) : ℝ :=
    (ψ_d (S_ang s₀ p.2 (a (some i))) *
      ∏ r ∈ Finset.univ.erase i, deriv u (S_ang s₀ p.2 (a (some r)))) *
      deriv u (S_ang s₀ p.2 (a none))
  let G₂ (p : Ω₀ × W) (a : Option (Option (Fin 2)) → T) : ℝ :=
    (∏ r : Fin 2, deriv u (S_ang s₀ p.2 (a (some (some r))))) *
      deriv u (S_ang s₀ p.2 (a (some none))) * deriv u (S_ang s₀ p.2 (a none))
  have hm₀ (i j : Fin 2) : Measurable fun x : (Ω₀ × W) × (Fin 2 → T) => G₀ i j x.1 x.2 :=
    ((hψdm.comp (hfield i)).mul (hψdm.comp (hfield j))).mul (hprod_m id _)
  have hm₁ (i : Fin 2) : Measurable fun x : (Ω₀ × W) × (Option (Fin 2) → T) => G₁ i x.1 x.2 :=
    ((hψdm.comp (hfield (some i))).mul (hprod_m e₁ _)).mul (hψm.comp (hfield none))
  have hm₂ : Measurable fun x : (Ω₀ × W) × (Option (Option (Fin 2)) → T) => G₂ x.1 x.2 :=
    ((hprod_m e₂ Finset.univ).mul (hψm.comp (hfield (some none)))).mul (hψm.comp (hfield none))
  have hb₀ (i j : Fin 2) (p : Ω₀ × W) (a : Fin 2 → T) : |G₀ i j p a| ≤ K :=
    hthree _ _ _ (hψd_L _) (hψd_L _) (hprod id _ p a)
  have hb₁ (i : Fin 2) (p : Ω₀ × W) (a : Option (Fin 2) → T) : |G₁ i p a| ≤ K := by
    dsimp only [G₁]; rw [mul_right_comm]
    exact hthree _ _ _ (hψd_L _) (hDu_L _) (hprod e₁ _ p a)
  have hb₂ (p : Ω₀ × W) (a : Option (Option (Fin 2)) → T) : |G₂ p a| ≤ K := by
    dsimp only [G₂]
    rw [show (∏ r : Fin 2, deriv u (S_ang s₀ p.2 (a (some (some r))))) *
      deriv u (S_ang s₀ p.2 (a (some none))) * deriv u (S_ang s₀ p.2 (a none)) =
      deriv u (S_ang s₀ p.2 (a (some none))) * deriv u (S_ang s₀ p.2 (a none)) *
        (∏ r : Fin 2, deriv u (S_ang s₀ p.2 (a (some (some r))))) by ring]
    exact hthree _ _ _ (hDu_L _) (hDu_L _) (hprod e₂ Finset.univ p a)
  let J₀ (i j : Fin 2) (g₀ : Ω₀) : ℝ :=
    ∫ w, ∫ a : Fin 2 → T, f_ov (fun r => (a r).1) * C_cov (a i).1 (a j).1 * G₀ i j (g₀, w) a
      ∂(Measure.pi fun _ : Fin 2 => ν (g₀, w)) ∂γ_sh
  let J₁ (i : Fin 2) (g₀ : Ω₀) : ℝ :=
    ∫ w, ∫ a : Option (Fin 2) → T,
      f_ov (fun r => (a (some r)).1) * C_cov (a (some i)).1 (a none).1 * G₁ i (g₀, w) a
      ∂(Measure.pi fun _ : Option (Fin 2) => ν (g₀, w)) ∂γ_sh
  let J₁' (i : Fin 2) (g₀ : Ω₀) : ℝ :=
    ∫ w, ∫ a : Option (Fin 2) → T,
      f_ov (fun r => (a (some r)).1) * C_cov (a none).1 (a (some i)).1 * G₁ i (g₀, w) a
      ∂(Measure.pi fun _ : Option (Fin 2) => ν (g₀, w)) ∂γ_sh
  let J₂ (g₀ : Ω₀) : ℝ :=
    ∫ w, ∫ a : Option (Option (Fin 2)) → T,
      f_ov (fun r => (a (some (some r))).1) * C_cov (a (some none)).1 (a none).1 * G₂ (g₀, w) a
      ∂(Measure.pi fun _ : Option (Option (Fin 2)) => ν (g₀, w)) ∂γ_sh
  have hj₀ (i j : Fin 2) (h : i ≠ j) :
      Integrable (J₀ i j) P_M ∧ |∫ g₀, J₀ i j g₀ ∂P_M| ≤ K * m_pair :=
    hTerm (by decide) id Function.injective_id i j h (G₀ i j) (hm₀ i j) (hb₀ i j)
  have hj₁ (i : Fin 2) :
      Integrable (J₁ i) P_M ∧ |∫ g₀, J₁ i g₀ ∂P_M| ≤ K * m_pair :=
    hTerm (by decide) e₁ he₁ (some i) none (by simp) (G₁ i) (hm₁ i) (hb₁ i)
  have hj₁' (i : Fin 2) :
      Integrable (J₁' i) P_M ∧ |∫ g₀, J₁' i g₀ ∂P_M| ≤ K * m_pair :=
    hTerm (by decide) e₁ he₁ none (some i) (by simp) (G₁ i) (hm₁ i) (hb₁ i)
  have hj₂ : Integrable J₂ P_M ∧ |∫ g₀, J₂ g₀ ∂P_M| ≤ K * m_pair :=
    hTerm (by decide) e₂ he₂ (some none) none (by simp) G₂ hm₂ hb₂
  have hcomb := abs_integral_replica_groups_le P_M J₀ J₁ J₁' J₂
    (fun i j h => (hj₀ i j h).1) (fun i => (hj₁ i).1) (fun i => (hj₁' i).1) hj₂.1
    (mul_nonneg hK0 hm0)
    (fun i j h => (hj₀ i j h).2) (fun i => (hj₁ i).2) (fun i => (hj₁' i).2) hj₂.2
  have hGm (s' : ℝ) : AEStronglyMeasurable
      (fun g₀ : Ω₀ => ∫ w, ∫ σ : Fin 2 → T,
        f_ov (fun r => (σ r).1) * ∏ r : Fin 2, deriv u (S_ang s' w (σ r))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M g₀).prod γ_aux).tilted (fun y => u (S_ang s' w y)))
        ∂γ_sh) P_M := by
    let V_obs (p : Ω₀ × W) (y : T) : ℝ := u (S_ang s' p.2 y)
    let F_obs (p : Ω₀ × W) (σ : Fin 2 → T) : ℝ :=
      f_ov (fun r => (σ r).1) * ∏ r : Fin 2, deriv u (S_ang s' p.2 (σ r))
    have hpV : Measurable fun p : (Ω₀ × W) × T => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hsV := (hSang_m s').comp hpV
    have hVm : Measurable fun p : (Ω₀ × W) × T => V_obs p.1 p.2 := hu.measurable.comp hsV
    have hpr : Measurable fun p : (Ω₀ × W) × (Fin 2 → T) =>
        ∏ r : Fin 2, deriv u (S_ang s' p.1.2 (p.2 r)) := by
      refine Finset.measurable_prod _ fun r _ => ?_
      have hpr_r : Measurable fun p : (Ω₀ × W) × (Fin 2 → T) => (p.1.2, p.2 r) :=
        (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)
      have hsr := (hSang_m s').comp hpr_r
      exact hψm.comp hsr
    have hfm_id : Measurable fun p : (Ω₀ × W) × (Fin 2 → T) =>
        f_ov (fun r => (p.2 r).1) := by
      refine ((Finset.measurable_sum _ fun idx _ => ?_).const_mul _).sub_const q
      exact (measurable_units_cast.comp ((measurable_pi_apply idx).comp
        (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)))).mul
        (measurable_units_cast.comp ((measurable_pi_apply idx).comp
          (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))))
    have hFm : Measurable fun p : (Ω₀ × W) × (Fin 2 → T) => F_obs p.1 p.2 := hfm_id.mul hpr
    have hm_int := measurable_integral_pi_tilted_prod_tilted
      (Measure.count : Measure α) γ_aux hEM_m hEM_i hVm hFm
    exact (hm_int.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ)).aestronglyMeasurable
  have hf_int : Integrable (fun g₀ : Ω₀ => ∫ a, |f_ov a| ∂(Measure.pi fun _ : Fin 2 => μ_M g₀))
      P_M := by
    have hf_abs_m : Measurable fun p : Ω₀ × (Fin 2 → α) => |f_ov p.2| := by
      have hov_m : Measurable fun p : Ω₀ × (Fin 2 → α) => f_ov p.2 := by
        refine ((Finset.measurable_sum _ fun idx _ => ?_).const_mul _).sub_const q
        exact (measurable_units_cast.comp ((measurable_pi_apply idx).comp
          ((measurable_pi_apply 0).comp measurable_snd))).mul
          (measurable_units_cast.comp ((measurable_pi_apply idx).comp
            ((measurable_pi_apply 1).comp measurable_snd)))
      exact hov_m.norm
    have hm1 := measurable_integral_pi_tilted (μ := (Measure.count : Measure α))
      (G := fun _ a => |f_ov a|) hEM_m hf_abs_m
    exact Integrable.of_bound hm1.aestronglyMeasurable 2 (ae_of_all _ fun g₀ => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun a => by rw [abs_abs]; exact hf_le2 a)
  have hdRot := hasDerivAt_integral_integral_gaussian_tilted_rotation_ibp
    (Ω₀ := Ω₀) (α := α) (L := α) (K_sh := Fin (N + 1) ⊕ Unit) (K_aux := Unit) (R := Fin 2)
    P_M μ_M id measurable_id X_sh (fun _ => Y_sh) (fun _ => X_aux) (fun _ => Y_aux)
    (fun m _ => horth_sh m) (fun _ _ => horth_aux)
    (fun m => (hvar_X m).trans hvar_Y.symm)
    hu.differentiable hu.differentiable_deriv hB_abs hu.abs_deriv_le_abs
    (fun x => (hu.abs_deriv₂_le x).trans (le_abs_self D))
    (fun _ => deriv u) (fun _ => hu.differentiable_deriv) (fun _ => h2d)
    (M₀ := fun _ => |D|) (M₁ := fun _ => |D|) (M₂ := fun _ => |D|)
    (fun _ x => hu.abs_deriv_le_abs x)
    (fun _ x => (hu.abs_deriv₂_le x).trans (le_abs_self D))
    (fun _ x => (hb3 x).trans (le_abs_self D))
    (f := fun _ => f_ov) (ae_of_all _ fun _ => Integrable.of_finite) hf_int hGm s₀
  dsimp only at hdRot
  refine ⟨_, hdRot, ?_⟩
  have hbound : |∫ ω, ((∑ i : Fin 2, ∑ j ∈ Finset.univ.erase i, J₀ i j ω) -
        (Fintype.card (Fin 2) : ℝ) * ∑ i : Fin 2, J₁ i ω -
        (Fintype.card (Fin 2) : ℝ) * ∑ i : Fin 2, J₁' i ω +
        (Fintype.card (Fin 2) : ℝ) * ((Fintype.card (Fin 2) : ℝ) + 1) * J₂ ω) ∂P_M| ≤
      18 * L ^ 4 * Real.exp (8 * |D|) * Q_val :=
    hcomb.trans_eq (by
      have hcard2 : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
      rw [hcard2]
      dsimp only [K, m_pair]
      ring)
  have hJ₁_eq (i : Fin 2) (g₀ : Ω₀) :
      (∫ w, ∫ σ : Option (Fin 2) → T,
          (f_ov fun r => (σ (some r)).1) * C_cov (σ (some i)).1 (σ none).1 *
            (ψ_d (S_ang s₀ w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, deriv u (S_ang s₀ w (σ (some r)))) *
            deriv u (S_ang s₀ w (σ none))
          ∂(Measure.pi fun _ : Option (Fin 2) => ν (g₀, w)) ∂γ_sh) = J₁ i g₀ :=
    integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => by
      dsimp only [G₁]; ring))
  have hJ₁'_eq (j : Fin 2) (g₀ : Ω₀) :
      (∫ w, ∫ σ : Option (Fin 2) → T,
          (f_ov fun r => (σ (some r)).1) * C_cov (σ none).1 (σ (some j)).1 *
            (ψ_d (S_ang s₀ w (σ (some j))) *
              ∏ r ∈ Finset.univ.erase j, deriv u (S_ang s₀ w (σ (some r)))) *
            deriv u (S_ang s₀ w (σ none))
          ∂(Measure.pi fun _ : Option (Fin 2) => ν (g₀, w)) ∂γ_sh) = J₁' j g₀ :=
    integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => by
      dsimp only [G₁]; ring))
  have hJ₂_eq (g₀ : Ω₀) :
      (∫ w, ∫ σ : Option (Option (Fin 2)) → T,
          (f_ov fun r => (σ (some (some r))).1) * C_cov (σ (some none)).1 (σ none).1 *
            (∏ r : Fin 2, deriv u (S_ang s₀ w (σ (some (some r))))) *
            deriv u (S_ang s₀ w (σ (some none))) * deriv u (S_ang s₀ w (σ none))
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) => ν (g₀, w)) ∂γ_sh) = J₂ g₀ :=
    integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => by
      dsimp only [G₂]; ring))
  refine le_of_eq_of_le (congrArg abs (integral_congr_ae (ae_of_all _ fun g₀ => ?_))) hbound
  exact congrArg₂ (· + ·)
    (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) rfl
        (congrArg _ (Finset.sum_congr rfl fun i _ => hJ₁_eq i g₀)))
      (congrArg _ (Finset.sum_congr rfl fun j _ => hJ₁'_eq j g₀)))
    (congrArg _ (hJ₂_eq g₀))

/-- **Second-derivative bound for `φ(v)` on `(0, 1)` in the second proof of Theorem 2.4.2:**
Under (2.7) and `q ∈ [0, 1]`, the derivative `φ'(v)` of `hasDerivAt_second_proof_interpolation`
(Eq. (2.91)) is differentiable at every `v ∈ (0, 1)` with
`|φ''(v)| ≤ K(D) * ν((R_{1, 2} - q)²)`, where `K(D) ≥ 0` depends only on `D`. -/
theorem exists_hasDerivAt_second_proof_deriv_abs_le (D : ℝ) :
    ∃ K_sec : ℝ, 0 ≤ K_sec ∧
      ∀ (N M : ℕ) {q v : ℝ} (_hq : q ∈ Icc (0 : ℝ) 1) (_hv : v ∈ Ioo (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D),
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
        ∃ d₂,
          HasDerivAt
            (fun v' => -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
              ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
                deriv u (S_v v' ω (σ 0)) * deriv u (S_v v' ω (σ 1))
              ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v' ω x)))
              ∂P_ext)
            d₂ v ∧
          |d₂| ≤ K_sec *
            ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M := by
  let L : ℝ := 1 + 3 * |D| + |D| ^ 2
  let K_sec : ℝ := (9 / 2) * L ^ 4 * Real.exp (8 * |D|)
  refine ⟨K_sec, by positivity, ?_⟩
  intro N M q v hq hv u hd hb γ P_M P_ext μ_M S_v
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hB_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  let s₀ : ℝ := Real.arccos (Real.sqrt v)
  obtain ⟨z, hz_ang, hz_bd⟩ :=
    exists_hasDerivAt_secondProof_angle_abs_le (N := N) (M := M) hq hd hb s₀
  have hcomp := HasDerivAt.comp_arccos_sqrt_of_sin_cos hv.1 hv.2 hz_ang
  have hcomp_half := hcomp.const_mul (-(1 / 2 : ℝ))
  have hev : (fun v' => -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v' ω (σ 0)) * deriv u (S_v v' ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v' ω x)))
        ∂P_ext) =ᶠ[𝓝 v]
      fun v' => -(1 / 2) * ∫ g₀, ∫ w, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Unit → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          ∏ r : Fin 2, deriv u
            (Real.cos (Real.arccos (Real.sqrt v')) *
              ((Sum.elim (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * (((σ r).1 i : ℤ) : ℝ)) 0) ⬝ᵥ w +
                (0 : Unit → ℝ) ⬝ᵥ (σ r).2) +
              Real.sin (Real.arccos (Real.sqrt v')) *
                ((Sum.elim 0 (fun _ => Real.sqrt q)) ⬝ᵥ w +
                  (fun _ : Unit => Real.sqrt (1 - q)) ⬝ᵥ (σ r).2))
        ∂(Measure.pi fun _ : Fin 2 =>
          ((μ_M g₀).prod (Measure.pi fun _ : Unit => γ)).tilted fun y =>
            u (Real.cos (Real.arccos (Real.sqrt v')) *
                ((Sum.elim (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((y.1 i : ℤ) : ℝ)) 0) ⬝ᵥ w +
                  (0 : Unit → ℝ) ⬝ᵥ y.2) +
                Real.sin (Real.arccos (Real.sqrt v')) *
                  ((Sum.elim 0 (fun _ => Real.sqrt q)) ⬝ᵥ w +
                    (fun _ : Unit => Real.sqrt (1 - q)) ⬝ᵥ y.2)))
        ∂(Measure.pi fun _ : Fin (N + 1) ⊕ Unit => γ) ∂P_M := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with v' hv'
    congr 1
    have hcos : Real.cos (Real.arccos (Real.sqrt v')) = Real.sqrt v' :=
      Real.cos_arccos (by linarith [Real.sqrt_nonneg v']) (Real.sqrt_le_one.2 hv'.2.le)
    have hsin : Real.sin (Real.arccos (Real.sqrt v')) = Real.sqrt (1 - v') := by
      rw [Real.sin_arccos, Real.sq_sqrt hv'.1.le]
    have htr := integral_secondProof_deriv_eq_angle (N := N) (M := M) hu.measurable hB_abs
      hu.abs_deriv_le_abs hq (Real.arccos (Real.sqrt v'))
    dsimp only at htr
    rw [← htr]
    exact integral_congr_ae (ae_of_all _ fun ω => by
      have hSv (x : (Fin (N + 1) → ℤˣ) × ℝ) :
          S_v v' ω x = Real.cos (Real.arccos (Real.sqrt v')) *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
            Real.sin (Real.arccos (Real.sqrt v')) *
              (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2) := by
        dsimp only [S_v]; rw [hcos, hsin]
      simp_rw [hSv]
      rfl)
  refine ⟨-(1 / 2) * (-z / 2), hcomp_half.congr_of_eventuallyEq hev, ?_⟩
  have h1 : |-(1 / 2) * (-z / 2)| = (1 / 4) * |z| := by
    rw [show -(1 / 2 : ℝ) * (-z / 2) = (1 / 4) * z by ring, abs_mul, abs_of_pos (by norm_num)]
  rw [h1]
  calc (1 / 4) * |z|
      ≤ (1 / 4) * (18 * L ^ 4 * Real.exp (8 * |D|) *
          ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
            ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M) :=
        mul_le_mul_of_nonneg_left hz_bd (by norm_num)
    _ = K_sec * _ := by dsimp only [K_sec]; ring

/-- **Continuity and endpoint values of `φ(v)` and `φ'(v)` on `[0, 1]`:**
Under `u` continuous with `|u| ≤ B`, `u'` continuous with `|u'| ≤ D₁`, and `q ∈ [0, 1]`,
1. `φ` is continuous on `[0, 1]`;
2. `φ'` is continuous on `[0, 1]`;
3. `φ(1) = ∫ p, log ∫ τ, exp u(S_M(τ)) d(μ_M p.1) d(P_M × γ_row)`
   (`= (N + 1) (p_{N+1, M+1} - p_{N+1, M})`);
4. `φ(0) = 𝔼_z log 𝔼_ξ exp u(√q z + √(1 - q) ξ)`;
5. `φ'(0) = -(1 / 2) * perceptronRhat u q * ν(R_{1, 2} - q)`. -/
lemma secondProof_continuity_and_endpoints
    {N M : ℕ} {u : ℝ → ℝ} (hu : Continuous u) (hu' : Continuous (deriv u))
    {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    let γ : Measure ℝ := gaussianReal 0 1
    let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
    let γ_row := Measure.pi fun _ : Fin (N + 1) => γ
    let P_ext := (P_M.prod γ_row).prod γ
    let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
    let S_v (v : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
        (x : (Fin (N + 1) → ℤˣ) × ℝ) : ℝ :=
      Real.sqrt v * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - v) * (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)
    let φ (v : ℝ) : ℝ :=
      ∫ ω, Real.log (∫ x, Real.exp (u (S_v v ω x)) ∂((μ_M ω.1.1).prod γ)) ∂P_ext
    let φ' (v : ℝ) : ℝ :=
      -(1 / 2) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x)))
        ∂P_ext
    ContinuousOn φ (Icc 0 1) ∧
    ContinuousOn φ' (Icc 0 1) ∧
    φ 1 = (∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ),
      Real.log (∫ τ : Fin (N + 1) → ℤˣ,
        Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))
        ∂(μ_M p.1)) ∂(P_M.prod γ_row)) ∧
    φ 0 = (∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ∂γ) ∧
    φ' 0 = -(1 / 2) * perceptronRhat u q *
      ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M := by
  intro γ P_M γ_row P_ext μ_M S_v φ φ'
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hγ_prob : IsProbabilityMeasure γ := by dsimp only [γ]; infer_instance
  have hPM_prob : IsProbabilityMeasure P_M := by dsimp only [P_M, γ]; infer_instance
  have hPext_prob : IsProbabilityMeasure P_ext := by
    dsimp only [P_ext, P_M, γ_row, γ]; infer_instance
  have hμM_prob (g₀ : Fin M → Fin (N + 1) → ℝ) : IsProbabilityMeasure (μ_M g₀) :=
    isProbabilityMeasure_tilted Integrable.of_finite
  have hSv_m (v : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ => S_v v ω x :=
    (((Finset.measurable_sum _ fun i _ => measurable_const.mul
      (measurable_units_cast.comp ((measurable_pi_apply i).comp measurable_fst))).const_mul _
      ).const_mul _).add ((measurable_const.add (measurable_snd.const_mul _)).const_mul _)
  let E_M (g₀ : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
  have hEM_m : Measurable fun p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℤˣ) =>
      E_M p.1 p.2 := measurable_perceptronEnergy_joint hu.measurable
  -- Helper: continuity in `v` of `∫ ξ, h (S_v v ω (τ, ξ)) ∂γ` for bounded continuous `h`.
  have hint_ξ_cont {h : ℝ → ℝ} (hh : Continuous h) {M_h : ℝ} (hh_bd : ∀ x, |h x| ≤ M_h)
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) (τ : Fin (N + 1) → ℤˣ) :
      Continuous fun v : ℝ => ∫ ξ : ℝ, h (S_v v ω (τ, ξ)) ∂γ :=
    continuous_of_dominated (bound := fun _ => |M_h|)
      (fun _ => (hh.comp (by dsimp only [S_v]; fun_prop)).measurable.aestronglyMeasurable)
      (fun _ => ae_of_all _ fun _ => by
        rw [Real.norm_eq_abs]; exact (hh_bd _).trans (le_abs_self _))
      (integrable_const _)
      (ae_of_all _ fun _ => hh.comp (by dsimp only [S_v]; fun_prop))
  have hexp_pos (v : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (τ : Fin (N + 1) → ℤˣ) :
      0 < ∫ ξ : ℝ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ :=
    integral_exp_pos_of_ae_le (hu.measurable.comp (by dsimp only [S_v]; fun_prop)).aemeasurable
      (ae_of_all _ fun _ => hB_le _)
  have hexp_cont (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ)
      (τ : Fin (N + 1) → ℤˣ) :
      Continuous fun v : ℝ => ∫ ξ : ℝ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ :=
    hint_ξ_cont (h := fun x => Real.exp (u x)) (Real.continuous_exp.comp hu)
      (M_h := Real.exp B) (fun x => by
        rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hB_le x)) ω τ
  have hZ_eq (v : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      ∫ x, Real.exp (u (S_v v ω x)) ∂((μ_M ω.1.1).prod γ) =
        (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ) /
        ∑ τ : Fin (N + 1) → ℤˣ, Real.exp (E_M ω.1.1 τ) := by
    have hi : Integrable (fun x => Real.exp (u (S_v v ω x))) ((μ_M ω.1.1).prod γ) :=
      integrable_exp_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
        (ae_of_all _ fun _ => hB_le _)
    dsimp only [μ_M]
    rw [integral_prod _ hi, integral_tilted_eq_div,
      integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
    simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hZ_m (v : ℝ) :
      Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
        ∫ x, Real.exp (u (S_v v ω x)) ∂((μ_M ω.1.1).prod γ) := by
    rw [funext (hZ_eq v)]
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
          Real.exp (u (S_v v p.1 (τ, p.2))) := by
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
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    · have hτ : Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
          E_M ω.1.1 τ :=
        Finset.measurable_sum _ fun k _ => hu.measurable.comp
          ((Finset.measurable_sum _ fun i _ =>
            ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp
              (measurable_fst.comp measurable_fst))).mul_const _).const_mul _)
      exact Real.measurable_exp.comp hτ
  have hφ_cont : ContinuousOn φ (Icc 0 1) := by
    refine continuousOn_of_dominated
      (fun v _ => (Real.measurable_log.comp (hZ_m v)).aestronglyMeasurable)
      (fun v _ => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact (abs_log_integral_exp_le_of_ae_abs_le
          (hu.measurable.comp (hSv_m v ω)).aemeasurable
          (ae_of_all _ fun _ => hB _)).trans (le_abs_self B))
      (integrable_const |B|)
      (ae_of_all _ fun ω => Continuous.continuousOn ?_)
    rw [funext fun v => congrArg Real.log (hZ_eq v ω)]
    have hnum_cont : Continuous fun v : ℝ =>
        ∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ := by
      have := hexp_cont ω
      fun_prop
    have hdiv_cont : Continuous fun v : ℝ =>
        (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ) /
        ∑ τ : Fin (N + 1) → ℤˣ, Real.exp (E_M ω.1.1 τ) :=
      hnum_cont.div_const _
    exact hdiv_cont.log fun v => (div_pos
      (Finset.sum_pos (fun τ _ => mul_pos (Real.exp_pos _) (hexp_pos v ω τ))
        Finset.univ_nonempty)
      (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)).ne'
  -- For `φ'`, factor each replica's `ξ`-integral!
  have hφ'_inner_eq (v : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))) =
      ((∑ τ₀ : Fin (N + 1) → ℤˣ, ∑ τ₁ : Fin (N + 1) → ℤˣ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₀ i : ℤ) : ℝ) * ((τ₁ i : ℤ) : ℝ)) - q) *
          (Real.exp (E_M ω.1.1 τ₀) *
            ∫ ξ, deriv u (S_v v ω (τ₀, ξ)) * Real.exp (u (S_v v ω (τ₀, ξ))) ∂γ) *
          (Real.exp (E_M ω.1.1 τ₁) *
            ∫ ξ, deriv u (S_v v ω (τ₁, ξ)) * Real.exp (u (S_v v ω (τ₁, ξ))) ∂γ)) /
        (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ) ^ 2) := by
    let ν₁ := ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))
    have hν₁_prob : IsProbabilityMeasure ν₁ :=
      isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
        (ae_of_all _ fun _ => hB_le _)
    -- Let's rewrite `Measure.pi (fun _ : Fin 2 => ν₁)` via `measurePreserving_piFinTwo`!
    let G₂ (p : ((Fin (N + 1) → ℤˣ) × ℝ) × ((Fin (N + 1) → ℤˣ) × ℝ)) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i, ((p.1.1 i : ℤ) : ℝ) * ((p.2.1 i : ℤ) : ℝ)) - q) *
        deriv u (S_v v ω p.1) * deriv u (S_v v ω p.2)
    have hG₂_m : Measurable G₂ := by
      have hov : Measurable fun p : ((Fin (N + 1) → ℤˣ) × ℝ) × ((Fin (N + 1) → ℤˣ) × ℝ) =>
          ((((N : ℝ) + 1)⁻¹ * ∑ i, ((p.1.1 i : ℤ) : ℝ) * ((p.2.1 i : ℤ) : ℝ)) - q) := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_fst))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp measurable_snd)))
      exact (hov.mul ((hu'.measurable.comp ((hSv_m v ω).comp measurable_fst)))).mul
        (hu'.measurable.comp ((hSv_m v ω).comp measurable_snd))
    have hpi2 : (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ν₁)) =
      ∫ y : ((Fin (N + 1) → ℤˣ) × ℝ) × ((Fin (N + 1) → ℤˣ) × ℝ), G₂ y ∂(ν₁.prod ν₁) :=
      (measurePreserving_piFinTwo fun _ => ν₁).integral_comp_of_aestronglyMeasurable
        hG₂_m.aestronglyMeasurable
    have hG₂_int : Integrable G₂ (ν₁.prod ν₁) :=
      Integrable.of_bound hG₂_m.aestronglyMeasurable (2 * |D₁| ^ 2) (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs]
        dsimp only [G₂]
        rw [abs_mul, abs_mul]
        calc _ ≤ (2 * |D₁|) * |D₁| :=
              mul_le_mul (mul_le_mul (abs_spin_overlap_sub_le_two hq p.1.1 p.2.1)
                ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) zero_le_two)
                ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
          _ = 2 * |D₁| ^ 2 := by ring)
    have h1_tilted (H : (Fin (N + 1) → ℤˣ) → ℝ) :
        ∫ x : (Fin (N + 1) → ℤˣ) × ℝ, H x.1 * deriv u (S_v v ω x) ∂ν₁ =
          (∑ τ, H τ * (Real.exp (E_M ω.1.1 τ) *
            ∫ ξ, deriv u (S_v v ω (τ, ξ)) * Real.exp (u (S_v v ω (τ, ξ))) ∂γ)) /
          (∑ τ, Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ) := by
      dsimp only [ν₁]
      rw [integral_tilted_eq_div, hZ_eq v ω]
      have hHm : Measurable fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
          H x.1 * deriv u (S_v v ω x) * Real.exp (u (S_v v ω x)) :=
        (((measurable_of_finite H).comp measurable_fst).mul
          (hu'.measurable.comp (hSv_m v ω))).mul
          (Real.measurable_exp.comp (hu.measurable.comp (hSv_m v ω)))
      obtain ⟨CH, hCH⟩ := exists_abs_le_of_finite H
      have hHi : Integrable (fun x : (Fin (N + 1) → ℤˣ) × ℝ =>
          H x.1 * deriv u (S_v v ω x) * Real.exp (u (S_v v ω x))) ((μ_M ω.1.1).prod γ) :=
        Integrable.of_bound hHm.aestronglyMeasurable (|CH| * |D₁| * Real.exp B)
          (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul (mul_le_mul ((hCH x.1).trans (le_abs_self _))
              ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
              (Real.exp_le_exp.2 (hB_le _)) (Real.exp_pos _).le (by positivity))
      dsimp only [μ_M]
      rw [integral_prod _ hHi, integral_tilted_eq_div,
        integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
      simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
      change ((∑ τ : Fin (N + 1) → ℤˣ,
          (∫ y, H τ * deriv u (S_v v ω (τ, y)) * Real.exp (u (S_v v ω (τ, y))) ∂γ) *
            Real.exp (E_M ω.1.1 τ)) / ∑ τ, Real.exp (E_M ω.1.1 τ)) /
        ((∑ τ, Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ) /
          ∑ τ, Real.exp (E_M ω.1.1 τ)) = _
      have hZ_M_pos : 0 < ∑ τ, Real.exp (E_M ω.1.1 τ) :=
        Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
      have hB_pos : 0 < ∑ τ, Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ :=
        Finset.sum_pos (fun τ _ => mul_pos (Real.exp_pos _) (hexp_pos v ω τ))
          Finset.univ_nonempty
      have hnum_eq : (∑ τ : Fin (N + 1) → ℤˣ,
          (∫ y, H τ * deriv u (S_v v ω (τ, y)) * Real.exp (u (S_v v ω (τ, y))) ∂γ) *
            Real.exp (E_M ω.1.1 τ)) =
          ∑ τ : Fin (N + 1) → ℤˣ,
            H τ * (Real.exp (E_M ω.1.1 τ) *
              ∫ ξ, deriv u (S_v v ω (τ, ξ)) * Real.exp (u (S_v v ω (τ, ξ))) ∂γ) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        have hin : (∫ y, H τ * deriv u (S_v v ω (τ, y)) * Real.exp (u (S_v v ω (τ, y))) ∂γ) =
            H τ * ∫ ξ, deriv u (S_v v ω (τ, ξ)) * Real.exp (u (S_v v ω (τ, ξ))) ∂γ := by
          simp_rw [mul_assoc (H τ)]
          exact integral_const_mul _ _
        rw [hin]; ring
      rw [hnum_eq, div_div_div_cancel_right₀ hZ_M_pos.ne']
    change (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => ν₁)) = _
    rw [hpi2, integral_prod _ hG₂_int]
    have hinner_x (x : (Fin (N + 1) → ℤˣ) × ℝ) :
        ∫ y : (Fin (N + 1) → ℤˣ) × ℝ, G₂ (x, y) ∂ν₁ =
        deriv u (S_v v ω x) *
          ((∑ τ₁, ((((N : ℝ) + 1)⁻¹ * ∑ i, ((x.1 i : ℤ) : ℝ) * ((τ₁ i : ℤ) : ℝ)) - q) *
            (Real.exp (E_M ω.1.1 τ₁) *
              ∫ ξ, deriv u (S_v v ω (τ₁, ξ)) * Real.exp (u (S_v v ω (τ₁, ξ))) ∂γ)) /
          (∑ τ, Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ)) := by
      let Hx (τ₁ : Fin (N + 1) → ℤˣ) : ℝ :=
        ((((N : ℝ) + 1)⁻¹ * ∑ i, ((x.1 i : ℤ) : ℝ) * ((τ₁ i : ℤ) : ℝ)) - q)
      have heq_y (y : (Fin (N + 1) → ℤˣ) × ℝ) :
          G₂ (x, y) = deriv u (S_v v ω x) * (Hx y.1 * deriv u (S_v v ω y)) := by
        dsimp only [G₂, Hx]; ring
      simp_rw [heq_y, integral_const_mul]
      rw [h1_tilted Hx]
    simp_rw [hinner_x]
    let C_y (τ₀ : Fin (N + 1) → ℤˣ) : ℝ :=
      (∑ τ₁, ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₀ i : ℤ) : ℝ) * ((τ₁ i : ℤ) : ℝ)) - q) *
        (Real.exp (E_M ω.1.1 τ₁) *
          ∫ ξ, deriv u (S_v v ω (τ₁, ξ)) * Real.exp (u (S_v v ω (τ₁, ξ))) ∂γ)) /
      (∑ τ, Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ)
    have houter : (∫ x : (Fin (N + 1) → ℤˣ) × ℝ, deriv u (S_v v ω x) * C_y x.1 ∂ν₁) =
        ∫ x : (Fin (N + 1) → ℤˣ) × ℝ, C_y x.1 * deriv u (S_v v ω x) ∂ν₁ :=
      integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
    rw [houter, h1_tilted C_y]
    dsimp only [C_y]
    have hB_pos : 0 < ∑ τ, Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ :=
      Finset.sum_pos (fun τ _ => mul_pos (Real.exp_pos _) (hexp_pos v ω τ)) Finset.univ_nonempty
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, div_div, ← sq]
    congr 1
    refine Finset.sum_congr rfl fun τ₀ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun τ₁ _ => by ring
  have hφ'_cont : ContinuousOn φ' (Icc 0 1) := by
    dsimp only [φ']
    refine continuousOn_const.mul ?_
    have hI_m (v : ℝ) : Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_v v ω (σ 0)) * deriv u (S_v v ω (σ 1))
          ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))) := by
      rw [funext (hφ'_inner_eq v)]
      have hEm (τ : Fin (N + 1) → ℤˣ) :
          Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
            Real.exp (E_M ω.1.1 τ) :=
        Real.measurable_exp.comp
          (Finset.measurable_sum _ fun k _ => hu.measurable.comp
            ((Finset.measurable_sum _ fun i _ =>
              ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp
                (measurable_fst.comp measurable_fst))).mul_const _).const_mul _))
      have hIm_exp (τ : Fin (N + 1) → ℤˣ) :
          Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
            ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ := by
        have hj : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
            Real.exp (u (S_v v p.1 (τ, p.2))) := by
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
        exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
      have hIm_du (τ : Fin (N + 1) → ℤˣ) :
          Measurable fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ =>
            ∫ ξ, deriv u (S_v v ω (τ, ξ)) * Real.exp (u (S_v v ω (τ, ξ))) ∂γ := by
        have hj : Measurable fun p :
            (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
            deriv u (S_v v p.1 (τ, p.2)) * Real.exp (u (S_v v p.1 (τ, p.2))) := by
          have h1 : Measurable fun p :
              (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
              S_v v p.1 (τ, p.2) := by
            have hs : Measurable fun p :
                (((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) × ℝ =>
                ∑ i : Fin (N + 1), p.1.1.2 i * ((τ i : ℤ) : ℝ) :=
              Finset.measurable_sum _ fun i _ =>
                ((measurable_pi_apply i).comp
                  (measurable_snd.comp (measurable_fst.comp measurable_fst))).mul_const _
            exact ((hs.const_mul _).const_mul _).add
              ((((measurable_snd.comp measurable_fst).const_mul _).add
                (measurable_snd.const_mul _)).const_mul _)
          exact (hu'.measurable.comp h1).mul (Real.measurable_exp.comp (hu.measurable.comp h1))
        exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
      refine Measurable.div
        (Finset.measurable_sum _ fun τ₀ _ => Finset.measurable_sum _ fun τ₁ _ =>
          ((measurable_const.mul ((hEm τ₀).mul (hIm_du τ₀))).mul ((hEm τ₁).mul (hIm_du τ₁))))
        ((Finset.measurable_sum _ fun τ _ => (hEm τ).mul (hIm_exp τ)).pow_const 2)
    refine continuousOn_of_dominated
      (fun v _ => (hI_m v).aestronglyMeasurable)
      (fun v _ => ae_of_all _ fun ω => by
        have hprob_ω : IsProbabilityMeasure
            (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v v ω x))) :=
          isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp (hSv_m v ω)).aemeasurable
            (ae_of_all _ fun _ => hB_le _)
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_forall_abs_le _ fun σ => by
          rw [abs_mul, abs_mul]
          calc _ ≤ (2 * |D₁|) * |D₁| :=
                mul_le_mul (mul_le_mul (abs_spin_overlap_sub_le_two hq (σ 0).1 (σ 1).1)
                  ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) zero_le_two)
                  ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
            _ = 2 * |D₁| ^ 2 := by ring)
      (integrable_const (2 * |D₁| ^ 2))
      (ae_of_all _ fun ω => Continuous.continuousOn ?_)
    rw [funext fun v => hφ'_inner_eq v ω]
    have hdu_cont (τ : Fin (N + 1) → ℤˣ) :
        Continuous fun v : ℝ =>
          ∫ ξ, deriv u (S_v v ω (τ, ξ)) * Real.exp (u (S_v v ω (τ, ξ))) ∂γ :=
      hint_ξ_cont (h := fun x => deriv u x * Real.exp (u x))
        (hu'.mul (Real.continuous_exp.comp hu))
        (M_h := |D₁| * Real.exp B)
        (fun x => by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul ((hD₁ x).trans (le_abs_self _)) (Real.exp_le_exp.2 (hB_le x))
            (Real.exp_pos _).le (abs_nonneg _)) ω τ
    have hnum_c : Continuous fun v : ℝ =>
        ∑ τ₀ : Fin (N + 1) → ℤˣ, ∑ τ₁ : Fin (N + 1) → ℤˣ,
          ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₀ i : ℤ) : ℝ) * ((τ₁ i : ℤ) : ℝ)) - q) *
            (Real.exp (E_M ω.1.1 τ₀) *
              ∫ ξ, deriv u (S_v v ω (τ₀, ξ)) * Real.exp (u (S_v v ω (τ₀, ξ))) ∂γ) *
            (Real.exp (E_M ω.1.1 τ₁) *
              ∫ ξ, deriv u (S_v v ω (τ₁, ξ)) * Real.exp (u (S_v v ω (τ₁, ξ))) ∂γ) := by
      fun_prop
    have hden_c : Continuous fun v : ℝ =>
        (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (E_M ω.1.1 τ) * ∫ ξ, Real.exp (u (S_v v ω (τ, ξ))) ∂γ) ^ 2 := by
      have := hexp_cont ω
      fun_prop
    exact hnum_c.div hden_c fun v => pow_ne_zero 2
      (Finset.sum_pos (fun τ _ => mul_pos (Real.exp_pos _) (hexp_pos v ω τ))
        Finset.univ_nonempty).ne'
  -- Endpoint `φ 1`:
  have hφ1 : φ 1 = ∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ),
      Real.log (∫ τ : Fin (N + 1) → ℤˣ,
        Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))
        ∂(μ_M p.1)) ∂(P_M.prod γ_row) := by
    dsimp only [φ]
    let f1 (p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) : ℝ :=
      Real.log (∫ τ : Fin (N + 1) → ℤˣ,
        Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))
        ∂(μ_M p.1))
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
        Real.log (∫ x, Real.exp (u (S_v 1 ω x)) ∂((μ_M ω.1.1).prod γ)) = f1 ω.1 := by
      dsimp only [f1]
      congr 1
      let g1 (τ : Fin (N + 1) → ℤˣ) : ℝ :=
        Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.2 i * ((τ i : ℤ) : ℝ)))
      have hs1 (x : (Fin (N + 1) → ℤˣ) × ℝ) : Real.exp (u (S_v 1 ω x)) = g1 x.1 := by
        dsimp only [S_v, g1]
        rw [Real.sqrt_one, one_mul, sub_self, Real.sqrt_zero, zero_mul, add_zero]
      simp_rw [hs1]
      exact integral_prod_fun_fst_of_isProbabilityMeasure (μ_M ω.1.1) γ g1
    simp_rw [hpt]
    exact integral_prod_fun_fst_of_isProbabilityMeasure (P_M.prod γ_row) γ f1
  -- Endpoint `φ 0`:
  have hφ0 : φ 0 = ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ∂γ := by
    dsimp only [φ]
    let f0 (z : ℝ) : ℝ :=
      Real.log (∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ)
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
        Real.log (∫ x, Real.exp (u (S_v 0 ω x)) ∂((μ_M ω.1.1).prod γ)) = f0 ω.2 := by
      dsimp only [f0]
      congr 1
      let g0 (ξ : ℝ) : ℝ := Real.exp (u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * ξ))
      have hs0 (x : (Fin (N + 1) → ℤˣ) × ℝ) : Real.exp (u (S_v 0 ω x)) = g0 x.2 := by
        dsimp only [S_v, g0]
        rw [Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul]
      simp_rw [hs0]
      exact integral_prod_fun_snd_of_isProbabilityMeasure (μ_M ω.1.1) γ g0
    simp_rw [hpt]
    exact integral_prod_fun_snd_of_isProbabilityMeasure (P_M.prod γ_row) γ f0
  -- Endpoint `φ' 0`:
  have hφ'0 : φ' 0 = -(1 / 2) * perceptronRhat u q *
      ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M := by
    dsimp only [φ']
    let ov_g (g₀ : Fin M → Fin (N + 1) → ℝ) : ℝ :=
      ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin 2 => μ_M g₀)
    let ρ_z (z : ℝ) : ℝ :=
      ((∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) *
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) /
        ∫ ξ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ^ 2
    have hpt0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × ℝ) :
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_v 0 ω (σ 0)) * deriv u (S_v 0 ω (σ 1))
          ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v 0 ω x)))) =
        ov_g ω.1.1 * ρ_z ω.2 := by
      have hs0 (x : (Fin (N + 1) → ℤˣ) × ℝ) :
          S_v 0 ω x = Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2 := by
        dsimp only [S_v]
        rw [Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul]
      have htilted0 : (((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v 0 ω x))) =
          ((μ_M ω.1.1).prod γ).tilted (fun x => (0 : (Fin (N + 1) → ℤˣ) → ℝ) x.1 +
            u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2)) := by
        congr 1; funext x; rw [hs0 x]; simp
      have hint_prod := integral_pi_tilted_prod_add_mul (μ := μ_M ω.1.1) (ν := γ) (ι := Fin 2)
        (0 : (Fin (N + 1) → ℤˣ) → ℝ)
        (fun ξ => u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * ξ))
        (fun τ => ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q))
        (fun η => deriv u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * η 0) *
          deriv u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * η 1))
      simp only [tilted_zero] at hint_prod
      have h_eq_integrand :
          (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              deriv u (S_v 0 ω (σ 0)) * deriv u (S_v 0 ω (σ 1))
            ∂(Measure.pi fun _ : Fin 2 => ((μ_M ω.1.1).prod γ).tilted (fun x => u (S_v 0 ω x)))) =
          ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × ℝ,
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              (deriv u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * (σ 0).2) *
                deriv u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * (σ 1).2))
            ∂(Measure.pi fun _ : Fin 2 =>
              ((μ_M ω.1.1).prod γ).tilted (fun x => (0 : (Fin (N + 1) → ℤˣ) → ℝ) x.1 +
                u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * x.2))) := by
        rw [htilted0]
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        dsimp only
        rw [hs0 (σ 0), hs0 (σ 1), mul_assoc]
      rw [h_eq_integrand, hint_prod]
      congr 1
      have hprob_z : IsProbabilityMeasure
          (γ.tilted fun ξ => u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * ξ)) :=
        isProbabilityMeasure_tilted (integrable_exp_cavityPath_new hu.measurable hB_le q ω.2)
      have hθ : Measurable fun ξ : ℝ => deriv u (Real.sqrt q * ω.2 + Real.sqrt (1 - q) * ξ) :=
        hu'.measurable.comp (by fun_prop)
      rw [integral_pi_mul_of_ne _ (by decide : (0 : Fin 2) ≠ 1) hθ hθ, integral_tilted_eq_div,
        ← sq]
    simp_rw [hpt0]
    dsimp only [P_ext]
    rw [integral_prod_mul (μ := P_M.prod γ_row) (ν := γ) (fun p => ov_g p.1) ρ_z,
      integral_prod_fun_fst_of_isProbabilityMeasure P_M γ_row ov_g]
    dsimp only [perceptronRhat, ρ_z, ov_g, γ]
    ring
  exact ⟨hφ_cont, hφ'_cont, hφ1, hφ0, hφ'0⟩

/-- **Unconditional discrete pressure increment bound (combining Eqs. (2.90)–(2.92) without the
Chapter 9 centered-overlap input):**
Under (2.7) and `q ∈ [0, 1]`,
$$\left|p_{N+1, M+1}(u) - p_{N+1, M}(u) -
    \frac{1}{N + 1}\,\mathbb{E}\log\mathbb{E}_\xi \exp u(\sqrt{q}\,z + \sqrt{1 - q}\,\xi) +
    \frac{\widehat{r}(q)}{2 (N + 1)}\,\nu(R_{1, 2} - q)\right|
  \le \frac{K_{\mathrm{sec}}(D)}{2 (N + 1)}\,\nu\bigl((R_{1, 2} - q)^2\bigr).$$
Neither the fixed-point equations (2.68) nor the Chapter 9 centered-overlap estimate is assumed. -/
theorem exists_abs_perceptron_pressure_succ_sub_add_le (D : ℝ) :
    ∃ K_sec : ℝ, 0 ≤ K_sec ∧
      ∀ (N M : ℕ) {q : ℝ} (_hq : q ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D),
        let γ : Measure ℝ := gaussianReal 0 1
        let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let P_M1 := Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ
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
        |p_M1 - p_M -
            ((N : ℝ) + 1)⁻¹ * (∫ z : ℝ, Real.log (∫ ξ : ℝ,
              Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ∂γ) +
            (perceptronRhat u q / (2 * ((N : ℝ) + 1))) *
              ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
                ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
                ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M| ≤
          (K_sec / (2 * ((N : ℝ) + 1))) *
            ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M := by
  obtain ⟨K_sec, hKsec0, h_sec⟩ := exists_hasDerivAt_second_proof_deriv_abs_le D
  refine ⟨K_sec, hKsec0, ?_⟩
  intro N M q hq u hd hb γ P_M P_M1 μ_M p_M1 p_M
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hui : Integrable u γ :=
    Integrable.of_bound hu.measurable.aestronglyMeasurable |D|
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (hu.abs_le x).trans (le_abs_self D))
  have h290 := perceptron_pressure_succ_sub_eq (N := N) (M := M) hu.measurable hui
  dsimp only at h290
  obtain ⟨hφ_c, hφ'_c, hφ1, hφ0, hφ'0⟩ :=
    secondProof_continuity_and_endpoints (N := N) (M := M)
      hu.differentiable.continuous hu.differentiable_deriv.continuous
      hu.abs_le hu.abs_deriv_le hq
  dsimp only at hφ1 hφ0 hφ'0
  have htay := abs_sub_sub_deriv_zero_le_half_of_Ioo hφ_c hφ'_c
    (fun v hv => hasDerivAt_second_proof_interpolation (N := N) (M := M) hu hq hv)
    (fun v hv => h_sec N M hq hv hd hb)
  rw [hφ1, hφ0, hφ'0] at htay
  have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left htay (inv_nonneg.2 hL_pos.le)
  have hlhs_eq :
      ((N : ℝ) + 1)⁻¹ *
        |(∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ),
            Real.log (∫ τ : Fin (N + 1) → ℤˣ,
              Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))
              ∂(μ_M p.1)) ∂(P_M.prod (Measure.pi fun _ : Fin (N + 1) => γ))) -
          (∫ z : ℝ, Real.log (∫ ξ : ℝ,
            Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ∂γ) -
          (-(1 / 2) * perceptronRhat u q *
            ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
              ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M)| =
      |p_M1 - p_M -
          ((N : ℝ) + 1)⁻¹ * (∫ z : ℝ, Real.log (∫ ξ : ℝ,
            Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ∂γ) +
          (perceptronRhat u q / (2 * ((N : ℝ) + 1))) *
            ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
              ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M| := by
    have hmul_abs (x : ℝ) : ((N : ℝ) + 1)⁻¹ * |x| = |((N : ℝ) + 1)⁻¹ * x| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hL_pos)]
    rw [hmul_abs]
    congr 1
    dsimp only [p_M1, p_M, P_M1, P_M, μ_M, γ] at h290 ⊢
    generalize (∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1) = I_θ
    generalize (∫ g₀ : Fin M → Fin (N + 1) → ℝ, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
          (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))))
      ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) = B_ov
    generalize (∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ),
      Real.log (∫ τ : Fin (N + 1) → ℤˣ,
        Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.2 i * ((τ i : ℤ) : ℝ)))
        ∂Measure.count.tilted fun τ =>
          ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1 k i * ((τ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) = J_inc at h290 ⊢
    generalize (((N : ℝ) + 1)⁻¹ * ∫ g : Fin (M + 1) → Fin (N + 1) → ℝ,
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin (M + 1),
          u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))))
      ∂Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) =
      p1_val at h290 ⊢
    generalize (((N : ℝ) + 1)⁻¹ * ∫ g₀ : Fin M → Fin (N + 1) → ℝ,
      Real.log (∑ τ : Fin (N + 1) → ℤˣ,
        Real.exp (∑ k : Fin M,
          u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))))
      ∂Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) =
      p0_val at h290 ⊢
    have hJ : ((N : ℝ) + 1)⁻¹ * J_inc = p1_val - p0_val := h290.symm
    have hdist : ((N : ℝ) + 1)⁻¹ * (J_inc - I_θ - -(1 / 2) * perceptronRhat u q * B_ov) =
        ((N : ℝ) + 1)⁻¹ * J_inc - ((N : ℝ) + 1)⁻¹ * I_θ +
          (perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov := by
      field_simp; ring
    rw [hdist, hJ]
  rw [hlhs_eq] at hmul
  refine hmul.trans_eq ?_
  dsimp only [μ_M, P_M, γ]
  generalize (∫ g₀ : Fin M → Fin (N + 1) → ℝ, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
    ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q) ^ 2
    ∂(Measure.pi fun _ : Fin 2 =>
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
        (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))))
    ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) = Q_val
  field_simp

/-- **Conditional Eq. (2.93) (discrete increment rate `O((N + 1)⁻²)` under the Chapter 9
centered-overlap hypothesis):**
Given `D`, there exist `K, C ≥ 0` such that under (2.7), `(M / (N + 1)) * K ≤ 1`, `(q, r)` solving
(2.68) at load `M / (N + 1)`, and the explicit Chapter 9 centered-overlap hypothesis
`|ν(R_{1, 2} - q)| ≤ K_bias / (N + 1)` (`K_bias ≥ 0`),
$$\left|p_{N+1, M+1}(u) - p_{N+1, M}(u) -
    \frac{1}{N + 1}\,\mathbb{E}\log\mathbb{E}_\xi \exp u(\sqrt{q}\,z + \sqrt{1 - q}\,\xi)\right|
  \le \frac{C + (D^2 / 2)\,K_{\mathrm{bias}}}{(N + 1)^2}.$$
Note: the centered-overlap bound `|ν(R_{1, 2} - q)| ≤ K_bias / (N + 1)` is deferred by Talagrand to
Chapter 9 and is therefore taken as an explicit hypothesis of Eq. (2.93) alone. -/
theorem abs_perceptron_pressure_succ_sub_le_of_centered_overlap (D : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        {K_bias : ℝ}
        (_hbias :
          let γ : Measure ℝ := gaussianReal 0 1
          let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
          let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
              (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
          |∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
              ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M| ≤
            K_bias / ((N : ℝ) + 1)),
        let γ : Measure ℝ := gaussianReal 0 1
        let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let P_M1 := Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ
        let p_M1 : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g : Fin (M + 1) → Fin (N + 1) → ℝ,
          Real.log (∑ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ k : Fin (M + 1),
              u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ∂P_M1
        let p_M : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g₀ : Fin M → Fin (N + 1) → ℝ,
          Real.log (∑ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ k : Fin M,
              u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))) ∂P_M
        |p_M1 - p_M -
            ((N : ℝ) + 1)⁻¹ * (∫ z : ℝ, Real.log (∫ ξ : ℝ,
              Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ∂γ)| ≤
          (C + (D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 := by
  obtain ⟨K_sec, hKsec0, h_inc⟩ := exists_abs_perceptron_pressure_succ_sub_add_le D
  obtain ⟨K_ov, L_ov, hKov0, hLov0, h_ov⟩ := integral_perceptron_overlap_sub_sq_le D
  refine ⟨K_ov, (K_sec / 2) * L_ov, hKov0, by positivity, ?_⟩
  intro N M u hd hb hα q r hq hr K_bias hbias γ P_M P_M1 p_M1 p_M
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  have hrhat_mem : perceptronRhat u q ∈ Icc (0 : ℝ) (|D| ^ 2) :=
    rhat_mem_Icc hu.abs_deriv_le_abs q
      (fun z => integrable_exp_cavityPath_new hu.measurable hu.le_abs q z)
  have hrhat_le : perceptronRhat u q ≤ D ^ 2 := by simpa only [sq_abs] using hrhat_mem.2
  have h1 := h_inc N M hq_mem hd hb
  have h2 := h_ov N M hd hb hα hq hr
  dsimp only at h1 h2 hbias
  let μ_M (g₀ : Fin M → Fin (N + 1) → ℝ) :=
    (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
      (fun τ => ∑ k : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ)))
  let B_ov : ℝ := ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
    ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q)
    ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M
  let Q_ov : ℝ := ∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
    ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - q) ^ 2
    ∂(Measure.pi fun _ : Fin 2 => μ_M g₀) ∂P_M
  let Δ : ℝ := p_M1 - p_M -
    ((N : ℝ) + 1)⁻¹ * (∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ) ∂γ)
  have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hKbias0 : 0 ≤ K_bias := by
    have h0 : 0 ≤ K_bias / ((N : ℝ) + 1) := (abs_nonneg B_ov).trans hbias
    exact ((div_nonneg_iff.1 h0).resolve_right (fun h => by linarith [h.2])).1
  have h_tri : |Δ| ≤ |Δ + (perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov| +
      |(perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov| := by
    simpa only [add_sub_cancel_right] using
      abs_sub (Δ + (perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov)
        ((perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov)
  have h_part1 : |Δ + (perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov| ≤
      ((K_sec / 2) * L_ov) / ((N : ℝ) + 1) ^ 2 := by
    calc |Δ + (perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov|
        ≤ (K_sec / (2 * ((N : ℝ) + 1))) * Q_ov := h1
      _ ≤ (K_sec / (2 * ((N : ℝ) + 1))) * (L_ov / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((K_sec / 2) * L_ov) / ((N : ℝ) + 1) ^ 2 := by field_simp
  have h_part2 : |(perceptronRhat u q / (2 * ((N : ℝ) + 1))) * B_ov| ≤
      ((D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg hrhat_mem.1, abs_of_pos (by positivity)]
    calc (perceptronRhat u q / (2 * ((N : ℝ) + 1))) * |B_ov|
        ≤ (D ^ 2 / (2 * ((N : ℝ) + 1))) * (K_bias / ((N : ℝ) + 1)) :=
          mul_le_mul (div_le_div_of_nonneg_right hrhat_le (by positivity)) hbias
            (abs_nonneg _) (by positivity)
      _ = ((D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 := by field_simp
  calc |Δ| ≤ ((K_sec / 2) * L_ov) / ((N : ℝ) + 1) ^ 2 +
          ((D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 :=
        h_tri.trans (add_le_add h_part1 h_part2)
    _ = ((K_sec / 2) * L_ov + (D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 :=
        (add_div _ _ _).symm

/-- **Summation step completing the second proof of Theorem 2.4.2 (conditional on the Chapter 9
centered-overlap hypothesis):**
Combining Eq. (2.93) (`abs_perceptron_pressure_succ_sub_le_of_centered_overlap`) with the `F''`
Taylor bound (`exists_branch_taylor_perceptronRSFunctional_le`) and summing over `m < M` via
`p_{N+1, 0}(u) = log 2 = F(0, 0, 0)` yields the sharper `O(α / (N + 1))` rate claimed at the end
of Talagrand's second proof:
$$|p_{N+1, M}(u) - F(\alpha, r, q)| \le
  \frac{M}{(N + 1)^2}\,\bigl(C + \tfrac{1}{2}\,D^4 + \tfrac{1}{2}\,D^2 K_{\mathrm{bias}}\bigr)
  = \frac{\alpha}{N + 1}\,\bigl(C + \tfrac{1}{2}\,D^4 + \tfrac{1}{2}\,D^2 K_{\mathrm{bias}}\bigr).$$
Notice that the unconditional Theorem 2.4.2 (`abs_perceptron_pressure_sub_rs_free_energy_le`) does
not need `hbias`; this conditional theorem formalizes the final deduction of the second proof from
the Chapter 9 input `hbias`. -/
theorem abs_perceptron_pressure_sub_rs_le_of_centered_overlap (D : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        {K_bias : ℝ} (_hKbias0 : 0 ≤ K_bias)
        (_hbias : ∀ (m : ℕ), m < M →
          ∀ {qm rm : ℝ},
            qm = (∫ z : ℝ, Real.tanh (z * Real.sqrt rm) ^ 2 ∂gaussianReal 0 1) →
            rm = ((m : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u qm →
            let γ : Measure ℝ := gaussianReal 0 1
            let P_m := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (N + 1) => γ
            let μ_m (g₀ : Fin m → Fin (N + 1) → ℝ) :=
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted fun τ =>
                ∑ k : Fin m, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g₀ k i * ((τ i : ℤ) : ℝ))
            |∫ g₀, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ,
                ((((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ)) - qm)
                ∂(Measure.pi fun _ : Fin 2 => μ_m g₀) ∂P_m| ≤
              K_bias / ((N : ℝ) + 1)),
        let γ : Measure ℝ := gaussianReal 0 1
        let P_M := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        let p_M : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g : Fin M → Fin (N + 1) → ℝ,
          Real.log (∑ τ : Fin (N + 1) → ℤˣ,
            Real.exp (∑ k : Fin M,
              u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) ∂P_M
        |p_M - perceptronRSFunctional u α r q| ≤
          (α / ((N : ℝ) + 1)) * (C + (D ^ 2 / 2) * K_bias) := by
  obtain ⟨K_inc, C_inc, hKinc0, hCinc0, h_inc⟩ :=
    abs_perceptron_pressure_succ_sub_le_of_centered_overlap D
  obtain ⟨K_br, hKbr_pos, h_br⟩ := exists_branch_taylor_perceptronRSFunctional_le D
  obtain ⟨K_uniq, hKuniq0, h_uniq⟩ := exists_unique_rs_fixed_point D
  let K : ℝ := max (max K_inc K_br) (max K_uniq 1)
  let C : ℝ := C_inc + D ^ 4 / 2
  refine ⟨K, C, by positivity, by positivity, ?_⟩
  intro N M u hd hb hα q r hq hr K_bias hKbias0 hbias γ P_M α p_M
  obtain ⟨q_br, r_br, hspec_br, -, htay_br⟩ := h_br hd hb
  have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hK_ge_br : K_br ≤ K := (le_max_right K_inc K_br).trans (le_max_left _ _)
  have hK_ge_inc : K_inc ≤ K := (le_max_left K_inc K_br).trans (le_max_left _ _)
  have hK_ge_uniq : K_uniq ≤ K := (le_max_left K_uniq 1).trans (le_max_right _ _)
  let p_seq (m : ℕ) : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ g : Fin m → Fin (N + 1) → ℝ,
    Real.log (∑ τ : Fin (N + 1) → ℤˣ,
      Real.exp (∑ k : Fin m,
        u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))))
    ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (N + 1) => γ)
  let F_seq (m : ℕ) : ℝ :=
    perceptronRSFunctional u ((m : ℝ) / ((N : ℝ) + 1))
      (r_br ((m : ℝ) / ((N : ℝ) + 1))) (q_br ((m : ℝ) / ((N : ℝ) + 1)))
  -- Base case `m = 0`: `p_seq 0 = log 2` and `F_seq 0 = log 2`.
  have hp0_eq : p_seq 0 = Real.log 2 := by
    dsimp only [p_seq]
    have hP0_prob : IsProbabilityMeasure
        (Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin (N + 1) => γ) := by
      dsimp only [γ]; infer_instance
    have hsum_0 (g : Fin 0 → Fin (N + 1) → ℝ) :
        Real.log (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ k : Fin 0,
            u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) =
        ((N : ℝ) + 1) * Real.log 2 := by
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.exp_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_units_int, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      rw [Nat.cast_pow, Nat.cast_two, Real.log_pow]
      push_cast; ring
    simp_rw [hsum_0]
    rw [integral_const, probReal_univ, one_smul]
    field_simp
  have hF0_eq : F_seq 0 = Real.log 2 := by
    dsimp only [F_seq]
    rw [Nat.cast_zero, zero_div]
    have hspec0 := hspec_br 0 le_rfl (by simp)
    have hr0 : r_br 0 = 0 := by rw [hspec0.2, zero_mul]
    have hq0 : q_br 0 = 0 := by rw [hspec0.1, hr0, Real.sqrt_zero]; simp
    rw [hr0, hq0, perceptronRSFunctional_eq_log_two_add]
    simp [Real.sqrt_zero]
  -- Uniqueness at `m = M` identifies `(q, r)` with `(q_br α, r_br α)`:
  have huniq_M := h_uniq hd hb hα0 ((mul_le_mul_of_nonneg_left hK_ge_uniq hα0).trans hα)
  have hqr_eq : (q, r) = (q_br α, r_br α) := by
    obtain ⟨p₀, hp₀, huniq⟩ := huniq_M
    have h1 : (q, r) = p₀ := huniq (q, r) ⟨hq, hr⟩
    have h2 : (q_br α, r_br α) = p₀ :=
      huniq (q_br α, r_br α) (hspec_br α hα0 ((mul_le_mul_of_nonneg_left hK_ge_br hα0).trans hα))
    exact h1.trans h2.symm
  have hFM_eq : F_seq M = perceptronRSFunctional u α r q := by
    have hq_eq : q = q_br α := congrArg Prod.fst hqr_eq
    have hr_eq : r = r_br α := congrArg Prod.snd hqr_eq
    dsimp only [F_seq, α] at hq_eq hr_eq ⊢
    rw [← hq_eq, ← hr_eq]
  -- Step bound for each `m < M`:
  have hstep (m : ℕ) (hm : m < M) :
      |(p_seq (m + 1) - F_seq (m + 1)) - (p_seq m - F_seq m)| ≤
        (C + (D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 := by
    let am : ℝ := (m : ℝ) / ((N : ℝ) + 1)
    let bm : ℝ := ((m + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)
    have ham0 : 0 ≤ am := by dsimp only [am]; positivity
    have hbm0 : 0 ≤ bm := by dsimp only [bm]; positivity
    have hbm_le_α : bm ≤ α := by
      dsimp only [bm, α]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hm) hL_pos.le
    have ham_le_α : am ≤ α := by
      dsimp only [am, α]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hm.le) hL_pos.le
    have hamK_br : am * K_br ≤ 1 :=
      (mul_le_mul ham_le_α hK_ge_br (by positivity) hα0).trans hα
    have hbmK_br : bm * K_br ≤ 1 :=
      (mul_le_mul hbm_le_α hK_ge_br (by positivity) hα0).trans hα
    have hamK_inc : am * K_inc ≤ 1 :=
      (mul_le_mul ham_le_α hK_ge_inc (by positivity) hα0).trans hα
    obtain ⟨hqm, hrm⟩ := hspec_br am ham0 hamK_br
    have hbias_m := hbias m hm hqm hrm
    have hp_step := h_inc N m hd hb hamK_inc hqm hrm hbias_m
    have hF_step := htay_br am bm ham0 hamK_br hbm0 hbmK_br
    have hbm_sub_am : bm - am = ((N : ℝ) + 1)⁻¹ := by
      dsimp only [bm, am]; push_cast; field_simp; ring
    rw [hbm_sub_am] at hF_step
    let I_m : ℝ := ((N : ℝ) + 1)⁻¹ * ∫ z : ℝ, Real.log (∫ ξ : ℝ,
      Real.exp (u (Real.sqrt (q_br am) * z + Real.sqrt (1 - q_br am) * ξ)) ∂γ) ∂γ
    have hrew : (p_seq (m + 1) - F_seq (m + 1)) - (p_seq m - F_seq m) =
        (p_seq (m + 1) - p_seq m - I_m) - (F_seq (m + 1) - F_seq m - I_m) := by ring
    rw [hrew]
    refine (abs_sub _ _).trans ?_
    calc |p_seq (m + 1) - p_seq m - I_m| + |F_seq (m + 1) - F_seq m - I_m|
        ≤ (C_inc + (D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 +
            (D ^ 4 / 2) * (((N : ℝ) + 1)⁻¹) ^ 2 :=
          add_le_add hp_step hF_step
      _ = (C + (D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 := by
          dsimp only [C]; rw [inv_pow]; field_simp; ring
  -- Telescope over `m ∈ Finset.range M`:
  let δ (m : ℕ) : ℝ := p_seq m - F_seq m
  have hδ0 : δ 0 = 0 := by dsimp only [δ]; rw [hp0_eq, hF0_eq, sub_self]
  have htel : δ M - δ 0 = ∑ m ∈ Finset.range M, (δ (m + 1) - δ m) :=
    (Finset.sum_range_sub δ M).symm
  rw [hδ0, sub_zero] at htel
  have hδM : δ M = p_M - perceptronRSFunctional u α r q := by
    dsimp only [δ, p_seq, p_M, P_M]; rw [hFM_eq]
  rw [← hδM, htel]
  calc |∑ m ∈ Finset.range M, (δ (m + 1) - δ m)|
      ≤ ∑ m ∈ Finset.range M, |δ (m + 1) - δ m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.range M, (C + (D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2 :=
        Finset.sum_le_sum fun m hm => hstep m (Finset.mem_range.1 hm)
    _ = (M : ℝ) * ((C + (D ^ 2 / 2) * K_bias) / ((N : ℝ) + 1) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (α / ((N : ℝ) + 1)) * (C + (D ^ 2 / 2) * K_bias) := by
        dsimp only [α]; field_simp

end SecondProofIncrement

end SpinGlasses
