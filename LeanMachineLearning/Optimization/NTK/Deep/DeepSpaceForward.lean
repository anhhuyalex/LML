/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.GaussianDecoupling
public import LeanMachineLearning.Optimization.NTK.Deep.BackwardStructure

/-!
# Forward Concentration on `population/readout product`

The forward results of `Initialization/DeepNNGPTheorems.lean` are stated on the product of the
first `d` Gaussian weight populations. The backward induction additionally carries an
independent Gaussian readout. This file transports
the forward results there (`Prod.fst` is measure preserving):

* `tendstoInMeasure_deepSpace_of_prefix`: the transport lemma;
* `deepSpace_featureCov_tendsto`: `n⁻¹ ∑ⱼ ψ(h_ℓ^a,ⱼ) ψ(h_ℓ^b,ⱼ) → ∫ ψ ψ d𝒩(0, Σ^ℓ)` for an
  arbitrary polynomially bounded continuous `ψ`;
* `deepSpace_activationGram_tendsto`: the same for `ψ = φ` with the limit `Σ^{ℓ+1}`.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix

namespace NTK

/-- Transport of convergence in measure from the `Fin d`-indexed weight populations to
`((Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ))` for families that ignore the readout. -/
theorem tendstoInMeasure_deepSpace_of_prefix (d : ℕ)
    (F : ℕ → (Fin d → ℕ → ℕ → ℝ) → ℝ) (c : ℝ) (hF : ∀ n, Measurable (F n))
    (h : TendstoInMeasure
      (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      F atTop (fun _ => c)) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1)) (fun n (ω : ((Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ))) => F n ω.1) atTop
      (fun _ => c) :=
  tendstoInMeasure_comp_measurePreserving h measurePreserving_fst hF measurable_const

variable {d n0 m : ℕ}

/-- **Feature-covariance convergence on `population/readout product`.** -/
theorem deepSpace_featureCov_tendsto (φ ψ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (Cψ : ℝ) (hCψ : 0 ≤ Cψ) (pψ : ℕ) (hpψ : 0 < pψ)
    (hψ_growth : ∀ x : ℝ, |ψ x| ≤ Cψ * (1 + |x| ^ pψ))
    (X : Fin m → Fin n0 → ℝ) (ℓ : ℕ) (hℓ : ℓ < d) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : ((Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ))) => (n : ℝ)⁻¹ * ∑ j : Fin n,
        ψ (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a j) *
        ψ (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ b j))
      atTop
      (fun _ => ∫ z : EuclideanSpace ℝ (Fin m), ψ (z.ofLp a) * ψ (z.ofLp b)
        ∂multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ℓ)) := by
  have hν := deepEmpiricalFeatureCovariance_tendstoInMeasure n0 m d φ ψ hφ_cont hψ_cont C hC p hp
    hφ_growth Cψ hCψ pψ hpψ hψ_growth X ℓ hℓ
  have hentry := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Fin m → Fin m → ℝ => M a b)
    hν (by exact ((continuous_apply b).comp (continuous_apply a)).continuousAt)
  have hmeas := fun n : ℕ => measurable_deepFeatureAverage n0 m n d φ ψ hφ_cont.measurable
    hψ_cont.measurable X ℓ a b
  have hcomp := tendstoInMeasure_deepSpace_of_prefix d _ _ hmeas hentry
  convert hcomp using 3
  · rename_i n ω
    rw [deepParams]
    simp only [deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X _ _ ℓ hℓ]
  · rfl

/-- **Activation-Gram convergence on `population/readout product`:**
`n⁻¹ ⟨φ(h_ℓ^a), φ(h_ℓ^b)⟩ → Σ^{ℓ+1}_{ab}`. -/
theorem deepSpace_activationGram_tendsto (φ : ℝ → ℝ) (hφ_cont : Continuous φ) (C : ℝ)
    (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (ℓ : ℕ) (hℓ : ℓ < d) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : ((Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ))) => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a j) *
        φ (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ b j))
      atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (ℓ + 1) a b) := by
  have hν := deepEmpiricalCovariance_tendstoInMeasure n0 m d φ hφ_cont C hC p hp hφ_growth X ℓ hℓ
  have hentry := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Matrix (Fin m) (Fin m) ℝ => M a b)
    hν (by exact ((continuous_apply b).comp (continuous_apply a)).continuousAt)
  have hmeas := fun n : ℕ => measurable_deepFeatureAverage n0 m n d φ φ hφ_cont.measurable
    hφ_cont.measurable X ℓ a b
  have hcomp := tendstoInMeasure_deepSpace_of_prefix d _ _ hmeas hentry
  convert hcomp using 3
  · rename_i n ω
    rw [deepParams]
    simp only [deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X _ _ ℓ hℓ]
  · rfl

end NTK

end
