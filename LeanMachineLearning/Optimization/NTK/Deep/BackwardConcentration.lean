/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.BackwardInduction

/-!
# Backward Sensitivity Concentration and Theorem 2.27

Convergence in measure of the backward sensitivity Gram matrices `deepSensitivityGram` to the
limiting kernels `deepLimitingSensitivityKernel`, by downward induction on the layer, and the
resulting convergence of the deep empirical NTK (Theorem 2.27).

The hard core, the decoupling approximation `G_k - G_{k+1} · Φ'_k → 0` (`decoupling_tendsto`; its
proof by Gaussian conditioning on the projected part, an Isserlis variance bound and the
gradient-independence invariant lives on `population/readout product`, in `Deep/BackwardDecoupling.lean` and
`Deep/BackwardInduction.lean`), and the top hidden layer (`sensitivityGram_top_tendsto`,
`Deep/BackwardTop.lean`) are proved on `population/readout product` and not transported separately to the
`(W, w_out)` product space.

* `NTK.deepSensitivityGram_entry_tendstoInMeasure`: the downward induction
  (`deepSpace_sensitivity_induction`) transported to the product space.
* `NTK.deepEmpiricalNTK_tendstoInMeasure_deepLimitingNTK`: Theorem 2.27.

**Standing extra hypothesis.** The decoupling approximation, hence the induction and Theorem 2.27,
assume the hypothesis `hnd` (positive-definite limiting forward kernels `Σ^ℓ`,
`1 ≤ ℓ < d`). This is stronger than the informal theorem and is documented at each statement.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix ENNReal

namespace NTK

/-- **Backward covariance concentration (the core of Theorem 2.27).** For `k < d` the empirical
backward Gram entry `G_k^{(n), αβ} = n⁻¹ ⟨g_k^α, g_k^β⟩` (`deepSensitivityGram`) converges in
measure to the limiting backward covariance `Π^k_{αβ}` (`deepLimitingSensitivityKernel`).

Downward induction on `k`, carried out jointly with the gradient-independence invariant
`I(k): n⁻¹ ⟨h_k^b, g_k^a⟩ → 0` on `population/readout product` (`deepSpace_sensitivity_induction`). The top hidden
layer is `sensitivityGram_top_tendsto` (limit `Σ̇^{d-1} = Π^{d-1}`, as `Π^d = 1`). For `k + 1 < d`,
`G_k ≈ G_{k+1} · Φ'_k` (`decoupling_tendsto`), the induction hypothesis gives `G_{k+1} → Π^{k+1}`,
the derivative Gram converges to `Σ̇^k` (`derivGram_tendsto`), and `tendstoInMeasure_mul` combines
them into `Σ̇^k · Π^{k+1} = Π^k`.

**Extra hypothesis `hnd`** (positive-definite `Σ^ℓ`, `1 ≤ ℓ < d`; see
`decoupling_tendsto`), because the induction step uses the decoupling
approximation (the readout base case `k = d - 1` does not). -/
theorem deepSensitivityGram_entry_tendstoInMeasure
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (hnd : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < d →
      (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ℓ).PosDef)
    (k : ℕ) (hk : k < d) (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepSensitivityGram d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k, by omega⟩ α β)
      Filter.atTop
      (fun _ => deepLimitingSensitivityKernel d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ α β) := by
  have hd : 0 < d := by omega
  let A : ActivationData φ φ' := ⟨hφ_cont, hφ'_cont, C, hC, p, hp, hφ_growth, hφ'_growth⟩
  have h := (deepSpace_sensitivity_induction A X hd hnd k hk).1 α β
  have hT := tendstoInMeasure_prod_of_prefix_prod d _ _
    (fun n => measurable_sensitivityGram_entry (n0 := n0) X hφ_cont.measurable
      hφ'_cont.measurable n k hk α β) h
  refine hT.congr_left fun n => Eventually.of_forall fun q => ?_
  simp only [deepParams_prefix hd]

/-- **Theorem 2.27 (Infinite-Width Convergence of the Deep Empirical NTK to the Limiting NTK)**:
For any depth `d ≥ 1`, input dimension `n0`, sample size `m`, continuous activation `φ` and its
derivative `φ'` with bounded polynomial growth, and input dataset `X`, the empirical Neural Tangent
Kernel Gram matrix `deepEmpiricalNTK` converges entrywise in probability / in measure to the
deterministic recursive limiting NTK `deepLimitingNTK` as network width `n → ∞`.

**Extra hypothesis (not in the informal statement):** `hnd`, i.e. the limiting forward kernels
`Σ^ℓ`, `1 ≤ ℓ < d`, are positive definite. It is needed only by
the decoupling approximation `decoupling_tendsto` (control of the
pseudo-inverse of the empirical activation Gram). It fails e.g. for linear `φ` with `m > n0`, or for
repeated inputs; removing it (reducing to a linearly independent subfamily of inputs) is future
work. -/
theorem deepEmpiricalNTK_tendstoInMeasure_deepLimitingNTK
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (hnd : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < d →
      (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ℓ).PosDef)
    (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepEmpiricalNTK d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2) α β)
      Filter.atTop
      (fun _ =>
        deepLimitingNTK d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) α β) := by
  exact deepEmpiricalNTK_entry_tendstoInMeasure_of_layerwise d n0 m φ φ' X
    (fun n (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) => DeepMLPParams.ofTensor d n0 n q.1 q.2) α β
    (fun k hk => deepActivationGram_entry_tendstoInMeasure d n0 m φ hφ_cont C hC p hp
      hφ_growth X k hk α β)
    (fun k hk => deepSensitivityGram_entry_tendstoInMeasure d n0 m hd φ φ' hφ_cont hφ'_cont
      C hC p hp hφ_growth hφ'_growth X hnd k hk α β)

end NTK

end
