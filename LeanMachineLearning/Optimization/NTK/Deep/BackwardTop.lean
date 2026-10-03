/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.BackwardDecoupling
public import LeanMachineLearning.Optimization.NTK.Initialization.ReadoutLinearConcentration

/-!
# The Top Hidden Layer: Base Cases of the Backward Induction

At `ℓ = d - 1` the sensitivity is `g_{d-1} = W_d ⊙ φ'(h_{d-1})` with an independent Gaussian readout
`W_d`. This file proves, on `DeepSpace d`, the two base cases of the joint downward induction:

* `gradIndep_top_tendsto`: `I(d-1)`, i.e. `n⁻¹ ⟨h_{d-1}^b, g_{d-1}^a⟩ → 0` (a centred Gaussian
  linear form in the readout);
* `sensitivityGram_top_tendsto`: `G_{d-1}^{ab} → ∫ φ'φ' d𝒩(0, Σ^{d-1})` (the weighted Gaussian
  average of `Deep/BackwardConcentration.lean`, transported to `DeepSpace`).
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix

namespace NTK

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

/-- The forward pass does not read the readout `Wd`: it depends on `ω` only through `ω.1`. -/
lemma preactivation_deepParams_readout (n : ℕ) (ω : DeepSpace d) (v : ℕ → ℝ) (ℓ : Fin d) :
    deepMLPPreactivation d n0 n m φ X (deepParams d n0 n (ω.1, v)) ℓ =
      deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ℓ :=
  deepMLPPreactivation_congr_prefix φ X _ _ ℓ rfl fun _ _ => rfl

lemma netDeriv_deepParams_readout (n : ℕ) (ω : DeepSpace d) (v : ℕ → ℝ) (ℓ : Fin d) (a : Fin m) :
    netDeriv φ φ' X (deepParams d n0 n (ω.1, v)) ℓ a =
      netDeriv φ φ' X (deepParams d n0 n ω) ℓ a := by
  funext j
  simp only [netDeriv]
  rw [preactivation_deepParams_readout (φ := φ) X n ω v ℓ]

include A in
/-- **`I(d-1)`: gradient independence at the top hidden layer.** -/
theorem gradIndep_top_tendsto (hd : 0 < d) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        gradIndep φ φ' X (deepParams d n0 n ω) ⟨d - 1, by omega⟩ a b) atTop (fun _ => 0) := by
  have hφm : Measurable φ := A.cont.measurable
  have hφ'm : Measurable φ' := A.cont'.measurable
  set π : Measure (Fin d → ℕ → ℕ → ℝ) := Measure.pi fun _ : Fin d =>
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hπ
  have : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  let yv : ∀ n : ℕ, (Fin d → ℕ → ℕ → ℝ) → Fin n → ℝ := fun n w j =>
    deepMLPPreactivation d n0 n m φ X (deepParams d n0 n (w, fun _ => 0)) ⟨d - 1, by omega⟩ b j *
      netDeriv φ φ' X (deepParams d n0 n (w, fun _ => 0)) ⟨d - 1, by omega⟩ a j
  have hmeas0 : ∀ n : ℕ, Measurable (fun w : Fin d → ℕ → ℕ → ℝ => ((w, fun _ => (0 : ℝ)) :
      DeepSpace d)) := fun n => measurable_id.prodMk measurable_const
  have hy : ∀ n j, Measurable fun w => yv n w j := by
    intro n j
    exact ((measurable_netPre hφm X n ⟨d - 1, by omega⟩ b j).comp (hmeas0 n)).mul
      (hφ'm.comp ((measurable_netPre hφm X n ⟨d - 1, by omega⟩ a j).comp (hmeas0 n)))
  have hF4 : ∀ (F : ∀ n : ℕ, DeepSpace d → ℝ) (c : ℝ),
      (∀ n, Measurable (fun w : Fin d → ℕ → ℕ → ℝ => F n (w, fun _ => 0))) →
      (∀ n (ω : DeepSpace d), F n ω = F n (ω.1, fun _ => 0)) →
      TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) (fun (n : ℕ) (ω : DeepSpace d) => F n ω) atTop
        (fun _ => c) →
      TendstoInMeasure π (fun (n : ℕ) (w : Fin d → ℕ → ℕ → ℝ) => F n (w, fun _ => 0)) atTop
        (fun _ => c) := by
    intro F c hFm hFeq hF
    refine tendstoInMeasure_of_comp_fst (ν := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      hFm ?_
    refine (hF.congr_left fun n => Eventually.of_forall fun ω => ?_)
    exact hFeq n ω
  have hb : BddByConv π (fun (n : ℕ) (w : Fin d → ℕ → ℕ → ℝ) =>
      (n : ℝ)⁻¹ * ∑ j : Fin n, yv n w j ^ 2) := by
    obtain ⟨c1, hc1⟩ := preFour_cvg (d := d) (n0 := n0) A X (d - 1) (by omega) b
    obtain ⟨c2, hc2⟩ := avg4_deriv_cvg (d := d) (n0 := n0) A X (d - 1) (by omega) a
    have hc1' := hF4 (fun n ω => avg4 (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω)
      ⟨d - 1, by omega⟩ b)) c1 (fun n => measurable_avg4 fun j =>
        (measurable_netPre hφm X n ⟨d - 1, by omega⟩ b j).comp (hmeas0 n)) (fun n ω => by
        simp only [preactivation_deepParams_readout]) hc1
    have hc2' := hF4 (fun n ω => avg4 (netDeriv φ φ' X (deepParams d n0 n ω) ⟨d - 1, by omega⟩ a))
      c2 (fun n => measurable_avg4 fun j =>
        hφ'm.comp ((measurable_netPre hφm X n ⟨d - 1, by omega⟩ a j).comp (hmeas0 n)))
      (fun n ω => (congrArg avg4 (netDeriv_deepParams_readout (φ := φ) (φ' := φ') X n ω
        (fun _ => 0) ⟨d - 1, by omega⟩ a)).symm) hc2
    refine ⟨fun n w => (avg4 (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n (w, fun _ => 0))
        ⟨d - 1, by omega⟩ b) + avg4 (netDeriv φ φ' X (deepParams d n0 n (w, fun _ => 0))
          ⟨d - 1, by omega⟩ a)) / 2, (c1 + c2) / 2, fun n w => ?_,
      tendstoInMeasure_half_sum hc1' hc2'⟩
    have := avg_sq_mul_le_avg4
      (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n (w, fun _ => 0))
        ⟨d - 1, by omega⟩ b) (netDeriv φ φ' X (deepParams d n0 n (w, fun _ => 0))
          ⟨d - 1, by omega⟩ a)
    simpa [yv, dotProduct, sq] using this
  have hmain := tendstoInMeasure_gaussianLinear_average π yv hy hb
  refine hmain.congr_left fun n => Eventually.of_forall fun ω => ?_
  simp only [gradIndep, yv]
  have hg : backwardSensitivity d n0 n m φ φ' X (deepParams d n0 n ω) ⟨d - 1, by omega⟩ a =
      fun j => (deepParams d n0 n ω).Wd j * φ' (deepMLPPreactivation d n0 n m φ X
        (deepParams d n0 n ω) ⟨d - 1, by omega⟩ a j) :=
    funext fun j => backwardSensitivity_top d n0 n m φ φ' X _ hd a j
  rw [hg]
  simp only [dotProduct, preactivation_deepParams_readout, netDeriv]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [deepParams, DeepMLPParams.ofTensor]
  ring

include A in
/-- **`C(d-1)`: the top-layer sensitivity Gram converges** on `DeepSpace`:
`G_{d-1}^{ab} → ∫ φ'φ' d𝒩(0, Σ^{d-1})`. -/
theorem sensitivityGram_top_tendsto (hd : 0 < d) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨d - 1, by omega⟩ a b)
      atTop
      (fun _ => ∫ z : EuclideanSpace ℝ (Fin m), φ' (z.ofLp a) * φ' (z.ofLp b)
        ∂multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (d - 1))) := by
  have hφm : Measurable φ := A.cont.measurable
  have hφ'm : Measurable φ' := A.cont'.measurable
  have hd1 : d - 1 < d := by omega
  have hν := deepEmpiricalFeatureCovariance_tendstoInMeasure n0 m d φ φ' A.cont A.cont' A.C A.hC
    A.p A.hp A.growth A.C A.hC A.p A.hp A.growth' X (d - 1) hd1
  have hD0 := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Fin m → Fin m → ℝ => M a b) hν
    (by exact ((continuous_apply b).comp (continuous_apply a)).continuousAt)
  have hν2 := deepEmpiricalFeatureCovariance_tendstoInMeasure n0 m d φ (fun x => φ' x ^ 2)
    A.cont (A.cont'.pow 2) A.C A.hC A.p A.hp A.growth (2 * A.C ^ 2) (by have := A.hC; positivity)
    (2 * A.p) (by have := A.hp; omega) (polynomial_growth_sq φ' A.C A.p A.growth') X (d - 1) hd1
  have hM0 := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Fin m → Fin m → ℝ => M a b) hν2
    (by exact ((continuous_apply b).comp (continuous_apply a)).continuousAt)
  have hy_meas : ∀ (n : ℕ) (j : Fin n), Measurable (fun w : Fin d → ℕ → ℕ → ℝ =>
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) a j) *
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) b j)) :=
    fun n j => (hφ'm.comp (measurable_deepPreactivation n0 m n d φ hφm X (d - 1) a j)).mul
      (hφ'm.comp (measurable_deepPreactivation n0 m n d φ hφm X (d - 1) b j))
  have hW := tendstoInMeasure_gaussianSq_weighted_average
    (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
    (fun (n : ℕ) (w : Fin d → ℕ → ℕ → ℝ) (j : Fin n) =>
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) a j) *
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) b j))
    hy_meas _ _ hD0
    (by
      refine hM0.congr' (Eventually.of_forall fun n => ae_of_all _ fun w => ?_) EventuallyEq.rfl
      simp only [mul_pow])
  refine hW.congr_left fun n => Eventually.of_forall fun ω => ?_
  beta_reduce
  rw [deepSensitivityGram_hidden d n0 n m φ φ' X _ (d - 1) hd1, Matrix.of_apply]
  simp only [dotProduct, backwardSensitivity_top d n0 n m φ φ' X _ hd,
    deepParams, deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X _ _ (d - 1) hd1]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [DeepMLPParams.ofTensor]
  ring

end NTK

end
