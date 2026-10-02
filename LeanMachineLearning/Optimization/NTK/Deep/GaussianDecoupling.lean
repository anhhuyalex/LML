/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import LeanMachineLearning.Optimization.NTK.Deep.Architecture
public import LeanMachineLearning.Optimization.NTK.Deep.LayerwiseNTK
public import LeanMachineLearning.Optimization.NTK.Deep.LimitingNTK
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Foundations.Concentration
public import LeanMachineLearning.Optimization.NTK.Initialization.Setup
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianAlgebra
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianMatrixAlgebra
public import LeanMachineLearning.Optimization.NTK.Initialization.CovariancePropagation
public import LeanMachineLearning.Optimization.NTK.Initialization.DeepNNGPTheorems

/-!
# Deep NTK Convergence: Backward Decoupling and Theorem 2.27

This module bridges the finite-width forward/backward Gram matrices to the deterministic limiting
NTK. The architecture-free Gaussian matrix facts it relies on (coordinate moments, the quadratic
form `E[u ⬝ᵥ (W A Wᵀ) v] = (u ⬝ᵥ v) tr A`, joint Gaussianity, and the one-sided conditioning
Lemma 2.26 `W P ⟂ W Pᗮ`) live in `Initialization/GaussianMatrixAlgebra.lean`.

1. **Deterministic assembly** (`deepEmpiricalNTK_entry_tendstoInMeasure_of_layerwise`): if every
   layerwise activation Gram `Φ_{k+1}^{(n)}` and sensitivity Gram `G_k^{(n)}` converges in measure
   to its limit, so does the empirical NTK entry (Proposition 2.25 plus
   `tendstoInMeasure_sum_mul`).
2. **Forward transport** (`deepActivationGram_entry_tendstoInMeasure`): moves
   `deepEmpiricalCovariance_tendstoInMeasure` to the `(W, w_out)` product measure used by
   `DeepMLPParams.ofTensor`.
3. **Backward concentration** (`deepSensitivityGram_entry_tendstoInMeasure`, in
   `Deep/BackwardConcentration.lean`; assumes positive-definite limiting kernels `hnd`):
   applied to `u = g_{ℓ+1}^α`, `v = g_{ℓ+1}^β` and `A = diag(φ'(h^α) φ'(h^β))`, the quadratic form
   yields the transition factor `G_{ℓ+1}^{(n), αβ} · Φ'^{(n)}_{ℓ, αβ}`.
4. **Theorem 2.27** (`deepEmpiricalNTK_tendstoInMeasure_deepLimitingNTK`, also in
   `Deep/BackwardConcentration.lean`): convergence in measure of `deepEmpiricalNTK` to
   `deepLimitingNTK`, from 1–3, under the same nondegeneracy assumption.
-/

@[expose]
public section

open scoped Matrix Real BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix

namespace NTK

/-! ### Theorem 2.27 Global Limiting Convergence -/

/-- **Deterministic assembly for Theorem 2.27.** Fix an entry `(α, β)`. If every non-trivial
layerwise
forward covariance `Φ_{k+1}^{(n)}` and backward covariance `G_k^{(n)}` converges in measure to its
deterministic limit `Σ^{k+1}` resp. `Π^k`, then the empirical NTK entry converges in measure to the
limiting NTK entry.

The two end layers need no hypothesis: `Φ_0^{(n)} = Σ^0` is the deterministic input Gram matrix and
`G_{d+1}^{(n)} = Π^d = 1` is the terminal condition. The proof is the exact layerwise decomposition
(Proposition 2.25) plus `tendstoInMeasure_sum_mul`, so it holds over an arbitrary measure and an
arbitrary random-parameter family `θ n : Ω → DeepMLPParams d n0 n`. -/
theorem deepEmpiricalNTK_entry_tendstoInMeasure_of_layerwise
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (d n0 m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : ∀ n : ℕ, Ω → DeepMLPParams d n0 n) (α β : Fin m)
    (hΦ : ∀ (k : ℕ) (hk : k < d),
      TendstoInMeasure μ
        (fun n ω => deepActivationGram d n0 n m φ X (θ n ω) ⟨k + 1, by omega⟩ α β)
        Filter.atTop
        (fun _ => layerCovarianceSeq 1 0 φ m
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1) α β))
    (hG : ∀ (k : ℕ) (hk : k < d),
      TendstoInMeasure μ
        (fun n ω => deepSensitivityGram d n0 n m φ φ' X (θ n ω) ⟨k, by omega⟩ α β)
        Filter.atTop
        (fun _ => deepLimitingSensitivityKernel d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ α β)) :
    TendstoInMeasure μ
      (fun n ω => deepEmpiricalNTK d n0 n m φ φ' X (θ n ω) α β) Filter.atTop
      (fun _ => deepLimitingNTK d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) α β) := by
  set Φ0 : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j) with hΦ0
  have hconst : ∀ c : ℝ, TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => c) Filter.atTop (fun _ => c) :=
    fun c ε hε => by simp [edist_self, hε.ne']
  have hG' : ∀ ℓ : Fin (d + 1), TendstoInMeasure μ
      (fun n ω => deepSensitivityGram d n0 n m φ φ' X (θ n ω) ℓ α β) Filter.atTop
      (fun _ => deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ α β) := by
    rintro ⟨l, hl⟩
    by_cases hld : l = d
    · subst hld
      simp only [deepSensitivityGram_terminal, deepLimitingSensitivityKernel_terminal,
        Matrix.of_apply]
      exact hconst 1
    · exact hG l (by omega)
  have hΦ' : ∀ ℓ : Fin (d + 1), TendstoInMeasure μ
      (fun n ω => deepActivationGram d n0 n m φ X (θ n ω) ℓ α β) Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m Φ0 ℓ.val α β) := by
    rintro ⟨l, hl⟩
    cases l with
    | zero =>
      simp only [deepActivationGram_zero, layerCovarianceSeq]
      exact hconst _
    | succ k => exact hΦ k (by omega)
  have := tendstoInMeasure_sum_mul (μ := μ)
    (a := fun (ℓ : Fin (d + 1)) (n : ℕ) (ω : Ω) =>
      deepSensitivityGram d n0 n m φ φ' X (θ n ω) ℓ α β)
    (b := fun (ℓ : Fin (d + 1)) (n : ℕ) (ω : Ω) =>
      deepActivationGram d n0 n m φ X (θ n ω) ℓ α β)
    hG' hΦ'
  simpa [deepEmpiricalNTK, deepLimitingNTK, Matrix.sum_apply, Matrix.hadamard_apply] using this


/-- **Transport from the `Fin d`-indexed weight population to the `(W, w_out)` product measure,
readout kept.** The map `(W, w_out) ↦ ((W 0, …, W (d - 1)), w_out)` is measure preserving, so
convergence in measure of a measurable scalar family of the first `d` weight populations and the
readout transfers to the product measure used by `DeepMLPParams.ofTensor`. -/
theorem tendstoInMeasure_prod_of_prefix_prod (d : ℕ)
    (F : ℕ → (Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ) → ℝ) (c : ℝ) (hF : ∀ n, Measurable (F n))
    (h : TendstoInMeasure
      ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      F Filter.atTop (fun _ => c)) :
    TendstoInMeasure
      ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) => F n (fun i : Fin d => q.1 i.val, q.2))
      Filter.atTop (fun _ => c) :=
  tendstoInMeasure_comp_measurePreserving h
    ((measurePreserving_prefixMap (Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) d).prod (MeasurePreserving.id _))
    hF measurable_const

/-- Special case of `tendstoInMeasure_prod_of_prefix_prod` for families that ignore the readout. -/
theorem tendstoInMeasure_prod_of_prefix (d : ℕ) (F : ℕ → (Fin d → ℕ → ℕ → ℝ) → ℝ) (c : ℝ)
    (hF : ∀ n, Measurable (F n))
    (h : TendstoInMeasure
      (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      F Filter.atTop (fun _ => c)) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) => F n (fun i : Fin d => q.1 i.val))
      Filter.atTop (fun _ => c) :=
  tendstoInMeasure_prod_of_prefix_prod d (fun n w => F n w.1) c
    (fun n => (hF n).comp measurable_fst)
    (tendstoInMeasure_comp_measurePreserving h measurePreserving_fst hF measurable_const)

/-- **Forward covariance concentration for the finite-parameter network (entrywise).** Transport of
`deepEmpiricalCovariance_tendstoInMeasure` (stated over the `Fin d`-indexed weight population and
for `deepPreactivation`) to the product measure on `(W, w_out)` used for `DeepMLPParams.ofTensor`
(`tendstoInMeasure_prod_of_prefix`): preactivations up to layer `k` only read `W 0, …, W k`
(`deepPreactivation_congr_of_eqOn`). -/
theorem deepActivationGram_entry_tendstoInMeasure
    (d n0 m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (k : ℕ) (hk : k < d) (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepActivationGram d n0 n m φ X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k + 1, by omega⟩ α β)
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1) α β) := by
  have hν := deepEmpiricalCovariance_tendstoInMeasure n0 m d φ hφ_cont C hC p hp hφ_growth X k hk
  have hentry := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Matrix (Fin m) (Fin m) ℝ => M α β)
    hν (by exact ((continuous_apply β).comp (continuous_apply α)).continuousAt)
  have hmeas := fun n : ℕ => measurable_deepFeatureAverage n0 m n d φ φ hφ_cont.measurable
    hφ_cont.measurable X k α β
  have hcomp := tendstoInMeasure_prod_of_prefix d _ _ hmeas hentry
  convert hcomp using 3
  · rename_i n q
    have hcongr := deepPreactivation_eq_prefix n0 m n d φ X q.1 k (by omega)
    rw [deepActivationGram_succ d n0 n m φ X _ k hk, Matrix.of_apply]
    simp only [dotProduct]
    rw [deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X q.1 q.2 k hk, hcongr]
  · rfl

/-- **Derivative Gram concentration (sub-lemma 1.1 of the backward step).** For `k < d` the
empirical
derivative Gram entry `Φ'^{(n), αβ}_k = n⁻¹ ∑_j φ'(h_{k,j}^α) φ'(h_{k,j}^β)` converges in measure to
`∫ φ' φ' d𝒩(0, Σ^k)` with `Σ^k = layerCovarianceSeq 1 0 φ m Φ0 k`, i.e. the factor `Σ̇^k` appearing
in
`deepLimitingSensitivityKernel`. Note that the covariance is built from `φ` while the averaged
feature is
`φ'`; this is `deepEmpiricalFeatureCovariance_tendstoInMeasure` with `ψ = φ'`. -/
theorem deepDerivativeGram_entry_tendstoInMeasure
    (d n0 m : ℕ) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (C' : ℝ) (hC' : 0 ≤ C') (p' : ℕ) (hp' : 0 < p')
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C' * (1 + |x| ^ p'))
    (X : Fin m → Fin n0 → ℝ) (k : ℕ) (hk : k < d) (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepDerivativeGram d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k, hk⟩ α β)
      Filter.atTop
      (fun _ => ∫ z : EuclideanSpace ℝ (Fin m), φ' (z.ofLp α) * φ' (z.ofLp β)
        ∂multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) k)) := by
  have hν := deepEmpiricalFeatureCovariance_tendstoInMeasure n0 m d φ φ' hφ_cont hφ'_cont C hC p hp
    hφ_growth C' hC' p' hp' hφ'_growth X k hk
  have hentry := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Fin m → Fin m → ℝ => M α β)
    hν (by exact ((continuous_apply β).comp (continuous_apply α)).continuousAt)
  have hmeas := fun n : ℕ => measurable_deepFeatureAverage n0 m n d φ φ' hφ_cont.measurable
    hφ'_cont.measurable X k α β
  have hcomp := tendstoInMeasure_prod_of_prefix d _ _ hmeas hentry
  convert hcomp using 3
  · rename_i n q
    have hcongr := deepPreactivation_eq_prefix n0 m n d φ X q.1 k (by omega)
    simp only [deepDerivativeGram, Matrix.of_apply, dotProduct]
    rw [deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X q.1 q.2 k hk, hcongr]
  · rfl

end NTK

end
