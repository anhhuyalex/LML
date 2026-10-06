/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.Concentration

/-!
# Two-layer network: joint law of the initial residual and the empirical NTK

Measurability of the empirical NTK matrix on packed parameters and the joint weak convergence
`(r_n(0), K_n(0)) ⟹ (G - y, K_∞)` of the initial training residual and empirical NTK.

## Main results and proof outline

- `measurable_empiricalNTKMatrix_netFromParams_packParams` : measurability of the empirical NTK
  matrix on packed parameters under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`.
- `tendstoInDistribution_initial_trainingResidual` : canonical initial training residual weak limit
  `r_n(0) ⟹ G - y` on the scaled dataset `(1 / √d) * X`.
- `tendstoInDistribution_joint_initial_residual_empiricalNTK` : joint weak convergence of initial
  training residual and empirical NTK matrix `(r_n(0), K_n(0)) ⟹ (G - y, K_∞)`.
- `exists_initial_residual_radius` : a single deterministic radius `R`, uniform in the width `n`,
  bounding the tail probability of the initial training residual norm by any `ε > 0`.

See `LeanMachineLearning.Optimization.NTK.Training.TwoLayer` for the overview of the whole
development.
-/

namespace NTK

open ConvexOpt MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

@[expose] public section

section JointOutputKernelInitialization

/-- Second countability of `Matrix (Fin m) (Fin m) ℝ` for the topology derived from the Frobenius
norm, which is what lemmas quantified over `[SeminormedAddCommGroup E']` see once
`Matrix.frobeniusNormedAddCommGroup` is a local instance. Mathlib's default (product) topology on
`Matrix` is a different term, defeq to this one only at default transparency, so typeclass search
does not accept an instance stated for the default topology; we therefore pin the topology
explicitly. -/
local instance (priority := 2000) instSecondCountableTopologyMatrixFrobenius (m : ℕ) :
    @SecondCountableTopology (Matrix (Fin m) (Fin m) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            Matrix.frobeniusNormedAddCommGroup)))) := by
  let : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) := Matrix.frobeniusNormedAddCommGroup
  let : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) := Matrix.frobeniusNormedSpace
  exact @secondCountable_of_proper _ NormedAddCommGroup.toSeminormedAddCommGroup.toPseudoMetricSpace
    (FiniteDimensional.proper_real (Matrix (Fin m) (Fin m) ℝ))

/-- `BorelSpace` for the Frobenius-derived topology on `Matrix (Fin m) (Fin m) ℝ`; see
`instSecondCountableTopologyMatrixFrobenius`. -/
local instance (priority := 2000) instBorelSpaceMatrixFrobenius (m : ℕ) :
    @BorelSpace (Matrix (Fin m) (Fin m) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _ Matrix.frobeniusNormedAddCommGroup))))
      Matrix.instMeasurableSpace := by
  exact (inferInstance : BorelSpace (Matrix (Fin m) (Fin m) ℝ))

/-- Measurability of the empirical NTK matrix evaluated on packed parameters
`packParams p.1 p.2` on an arbitrary dataset `X`. -/
lemma measurable_empiricalNTKMatrix_netFromParams_packParams
    {m d n : ℕ} (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ) :
    Measurable (fun (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
      empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) := by
  change Measurable (fun (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) (α β : Fin m) =>
    empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2) α β)
  rw [measurable_pi_iff]
  intro α
  rw [measurable_pi_iff]
  intro β
  have h_eq : (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2) α β) =
      fun p => (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ (p.1 i ⬝ᵥ X α) * φ (p.1 i ⬝ᵥ X β) +
         p.2 i ^ 2 * deriv φ (p.1 i ⬝ᵥ X α) * deriv φ (p.1 i ⬝ᵥ X β) * (X α ⬝ᵥ X β)) := by
    ext p
    have h := empiricalNTKMatrix_netFromParams_eq_neuron_sum φ n d m X
      (packParams p.1 p.2) (fun _ _ => hφ_diff.differentiableAt) α β
    simp_rw [packParams_weight_row, packParams_readout] at h
    exact h
  rw [h_eq]
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  have h_w : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have h_a : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have h_wx (k : Fin m) : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      p.1 i ⬝ᵥ X k) :=
    (measurable_dotProduct_left (X k)).comp h_w
  have h_φ (k : Fin m) : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      φ (p.1 i ⬝ᵥ X k)) :=
    hφ_diff.continuous.measurable.comp (h_wx k)
  have h_dφ (k : Fin m) : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      deriv φ (p.1 i ⬝ᵥ X k)) :=
    hdφ_meas.comp (h_wx k)
  have h_a2 : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2 i ^ 2) :=
    (continuous_pow 2).measurable.comp h_a
  exact (h_φ α).mul (h_φ β) |>.add <|
    ((h_a2.mul (h_dφ α)).mul (h_dφ β)).mul_const _

/-- Initial training residual weak limit on the paper's scaled dataset `(1 / √d) * X`:
the residual under initialization converges in distribution to `G - y`,
where `G ~ 𝒩(0, Φ^{(∞)}(X / √d))`. -/
theorem tendstoInDistribution_initial_trainingResidual
    {d m : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        trainingResidual (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2))
      Filter.atTop
      (fun G => G - y)
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  simp_rw [trainingResidual_netFromParams_packParams]
  exact tendstoInDistribution_initialResidual_evalVector φ X y hφ_meas hφ_L2

/-- **Theorem (Joint Output and NTK Weak Convergence at Initialization)**:
As width `n → ∞`, the joint law of the initial training residual
`r_n(0) = trainingResidual (netFromParams φ n d) X_scaled y θ_0`
and the full empirical NTK matrix
`K_n(0) = empiricalNTKMatrix (netFromParams φ n d) X_scaled θ_0`
converges in distribution to the joint pair `(G - y, limitingFullNTKMatrix φ X)`
under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`, where `G ~ 𝒩(0, Φ^{(∞)})` and `K_∞` is deterministic. -/
theorem tendstoInDistribution_joint_initial_residual_empiricalNTK
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β
            k))) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β
            k))) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        (trainingResidual (netFromParams φ n d)
           (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2),
         empiricalNTKMatrix (netFromParams φ n d)
           (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)))
      Filter.atTop
      (fun G => (G - y, limitingFullNTKMatrix φ X))
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  have hX := tendstoInDistribution_initial_trainingResidual φ X y
    hφ_diff.continuous.measurable fun α => memLp_two_of_memLp_two_mul_self
      ((hφ_diff.continuous.measurable.comp
        (measurable_dotProduct_left _)).aestronglyMeasurable) (hφ_L2 α α)
  have hY : ∀ ε > 0, Filter.Tendsto
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1))
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) -
            limitingFullNTKMatrix φ X‖})
      Filter.atTop (nhds 0) :=
    fun ε hε => tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ_diff hdφ_meas X
      hφ_L2 hdφ_L2 hε
  have hY_meas : ∀ n, AEMeasurable (fun p => empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)) ((Measure.pi fun _ : Fin n =>
          Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
              gaussianReal 0 1)) :=
    fun n => (measurable_empiricalNTKMatrix_netFromParams_packParams φ hφ_diff hdφ_meas
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)).aemeasurable
  exact hX.prodMk_of_tendsto_measure_norm_sub_const hY hY_meas

/-- **Uniform residual radius at initialization.** For every failure level `ε > 0` there is a
single deterministic radius `R ≥ 0`, valid for all widths `n`, such that the initial training
residual on the scaled dataset exceeds `R` in norm with `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`-probability at
most `ε`.
This is output-law tightness (from the characteristic-function limit) translated by `-y`. -/
theorem exists_initial_residual_radius
    {d m : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n, ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | R <
        ‖trainingResidual (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖} ≤ ε := by
  have hmeas : ∀ n, Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) := fun n =>
    evalVector_joint_measurable φ hφ_meas _
  have htight := (isTightMeasureSet_range_outputMeasure_scaled_dataset φ X hφ_meas hφ_L2).map
    (continuous_sub_right y)
  simp_rw [trainingResidual_netFromParams_packParams]
  refine exists_forall_measure_norm_gt_le_of_isTightMeasureSet_map
    (μ := fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    (X := fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
      evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) - y)
    (fun n => ((hmeas n).sub_const y).aemeasurable) htight
    (fun n => ⟨outputMeasure n d φ _, Set.mem_range_self n, ?_⟩) hε
  rw [outputMeasure_eq_map, Measure.map_map (measurable_sub_const y) (hmeas n)]
  rfl

/-- The event that the initial empirical NTK on an arbitrary dataset is at least `ε` away, in
Frobenius norm, from a fixed matrix is measurable. The Frobenius topology instances are local to
this section, so this measurability fact is proved here for use by later event constructions. -/
lemma measurableSet_empiricalNTKMatrix_dist_ge
    {m d n : ℕ} (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ) (K_inf : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) :
    MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ε ≤ ‖empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2) - K_inf‖} :=
  measurableSet_le measurable_const
    ((measurable_empiricalNTKMatrix_netFromParams_packParams φ hφ_diff hdφ_meas X).sub_const
      K_inf).norm

end JointOutputKernelInitialization

end

end NTK
