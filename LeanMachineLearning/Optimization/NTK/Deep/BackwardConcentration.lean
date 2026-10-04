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
limiting
kernels `deepLimitingSensitivityKernel`, by downward induction on the layer, and the resulting
convergence of the deep empirical NTK (Theorem 2.27).

* `NTK.deepSensitivityGram_readout_entry_tendstoInMeasure` (top hidden layer,
  `g_{d-1} = W_d ⊙ φ'(h_{d-1})`): the transport to the product space of
  `sensitivityGram_top_tendsto` (`Deep/BackwardTop.lean`), with separate growth constants.
* `NTK.deepSensitivityGram_sub_mul_tendstoInMeasure` (decoupling approximation
  `G_k - G_{k+1} · Φ'_k → 0`): the hard core. Its proof (Gaussian conditioning on the projected
  part, Isserlis variance bound, gradient-independence invariant) lives on `DeepSpace`
  (`Deep/BackwardDecoupling.lean`, `Deep/BackwardInduction.lean`); here it is its transport to the
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

/-- **Readout-layer backward concentration (sub-lemma 1.2).** At the top hidden layer
`g_{d-1}^α = W_d ⊙ φ'(h_{d-1}^α)`, so `G_{d-1}^{αβ} = n⁻¹ ∑ⱼ W_{d,j}² φ'(h^α_j) φ'(h^β_j)`. The
readout is an independent standard Gaussian, so this has the same limit as the derivative Gram
matrix,
`∫ φ' φ' d𝒩(0, Σ^{d-1})`. Separate growth constants for `φ` and `φ'` are accepted and merged
(`polynomial_growth_mono`) to feed the `DeepSpace` statement `sensitivityGram_top_tendsto`. -/
theorem deepSensitivityGram_readout_entry_tendstoInMeasure
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (C' : ℝ) (hC' : 0 ≤ C') (p' : ℕ)
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C' * (1 + |x| ^ p'))
    (X : Fin m → Fin n0 → ℝ) (α β : Fin m) :
    TendstoInMeasure
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun n : ℕ => fun (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) =>
        deepSensitivityGram d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨d - 1, by omega⟩ α β)
      Filter.atTop
      (fun _ => ∫ z : EuclideanSpace ℝ (Fin m), φ' (z.ofLp α) * φ' (z.ofLp β)
        ∂multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (d - 1))) := by
  have hC₀ : 0 ≤ 2 * max C C' := by positivity
  have hp₀ : 0 < max p p' := lt_max_of_lt_left hp
  let A : ActivationData φ φ' :=
    ⟨hφ_cont, hφ'_cont, 2 * max C C', hC₀, max p p', hp₀,
      polynomial_growth_mono φ hC (by linarith [le_max_left C C']) (le_max_left p p') hφ_growth,
      polynomial_growth_mono φ' hC' (by linarith [le_max_right C C']) (le_max_right p p')
        hφ'_growth⟩
  have h := sensitivityGram_top_tendsto A X hd α β
  have hT := tendstoInMeasure_prod_of_prefix_prod d _ _
    (fun n => measurable_sensitivityGram_entry (n0 := n0) X hφ_cont.measurable
      hφ'_cont.measurable n (d - 1) (by omega) α β) h
  refine hT.congr_left fun n => Eventually.of_forall fun q => ?_
  simp only [deepParams_prefix hd]

/-- **Decoupling approximation (sub-lemma 1.3, the hard core of the backward induction).** For a
hidden layer `k` with `k + 1 < d`, the backward Gram entry at layer `k` is asymptotically the
product of the backward Gram entry at layer `k + 1` and the derivative Gram entry at layer `k`:
`G_k^{(n),αβ} - G_{k+1}^{(n),αβ} · Φ'^{(n),αβ}_k → 0` in measure.

**Extra hypothesis `hnd`:** the limiting forward kernel `Σ^ℓ = layerCovarianceSeq 1 0 φ m Φ0 ℓ`
(the limit of the activation Gram `n⁻¹ ⟨φ(h_{ℓ-1}^α), φ(h_{ℓ-1}^β)⟩`, `Φ0 = X Xᵀ / n0`) is
**positive definite** for every `1 ≤ ℓ < d` (the input layer `ℓ = 0` is not constrained). The
orthogonal projector onto the span of the `m` forward features is controlled through the inverse
`Σ̂⁻¹` of the empirical Gram, which is only uniformly bounded when the limiting Gram is invertible.
The hypothesis is expected to hold for generic inputs and a non-polynomial activation (not proved
here), but it fails for linear `φ` once `m > n0`, and for repeated or collinear inputs. It is *not*
needed for the forward results, and is the only reason the backward induction and Theorem 2.27
below carry it.

**Proof.** With `D = diag(φ'(h_k^α) φ'(h_k^β))` and `u^γ = g_{k+1}^γ`,
`G_k^{αβ} = n⁻² (u^α)ᵀ W_{k+1} D W_{k+1}ᵀ u^β`. Let `Φ = [φ(h_k^1) … φ(h_k^m)]` and `P` the
orthogonal projector onto its span, so `n^{-1/2} W_{k+1}ᵀ u = x + y` with the projected part
`x = Φ (Σ̂⁻¹ ζ)`, `ζ = n⁻¹ ⟨h_{k+1}, u⟩`, and the residual `y = n^{-1/2} (W_{k+1} Pᗮ)ᵀ u`
(`backwardSensitivity_hidden_decomp`). The forward pass, hence `u`, sees `W_{k+1}` only through
`W_{k+1} P` (`backwardSensitivity_updateWh_congr`), while the residual `W_{k+1} Pᗮ` is independent
of `(W_{k+1} P, later layers)` (Lemma 2.26, `measurePreserving_layerSplit`).

* *Residual part* (`gperp_sub_tendsto`): conditionally on `(W_{k+1} P, past, future)` the
  quadratic form `n⁻² uᵀ (W Pᗮ) D (W Pᗮ)ᵀ v` has mean `G_{k+1} Φ'_k − G_{k+1} n⁻¹ tr(D P)` and
  variance `O(n⁻¹)` (`tendsto_residualQuadForm`, from Isserlis), and `n⁻¹ tr(D P) → 0`
  (`tendstoInMeasure_inv_nat_mul_trace`).
* *Projected part* (`wsq_projPart_tendsto`): vanishes thanks to the **gradient-independence
  invariant** `I(ℓ): n⁻¹ ⟨h_ℓ^b, g_ℓ^a⟩ → 0` (`ζ → 0`), with `Σ̂⁻¹ → (Σ^{k+1})⁻¹` bounded.
* *Assembly* (`decoupling_tendsto`): Cauchy–Schwarz `|G_k − G_⊥|² ≤ 3 [N_f(x) N_g(x') + N_f(x)
  N_g(y') + N_f(y) N_g(x')]` (`wcov_sub_sq_le`).

The invariant `I` and the decoupling are proved in one joint downward induction on `DeepSpace`
(`deepSpace_sensitivity_induction`, `Deep/BackwardInduction.lean`); this statement is its
`ℓ = k` instance transported to the `(W, w_out)` product space. -/
theorem deepSensitivityGram_sub_mul_tendstoInMeasure
    (d n0 m : ℕ) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (hnd : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < d →
      (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ℓ).PosDef)
    (k : ℕ) (hk : k + 1 < d) (α β : Fin m) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ =>
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      {q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ) | ε ≤ dist
        (deepSensitivityGram d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k, by omega⟩ α β)
        (deepSensitivityGram d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k + 1, by omega⟩ α β *
         deepDerivativeGram d n0 n m φ φ' X (DeepMLPParams.ofTensor d n0 n q.1 q.2)
          ⟨k, by omega⟩ α β)})
      Filter.atTop (nhds 0) := by
  have hd : 0 < d := by omega
  let A : ActivationData φ φ' := ⟨hφ_cont, hφ'_cont, C, hC, p, hp, hφ_growth, hφ'_growth⟩
  obtain ⟨hC1, hI1⟩ := deepSpace_sensitivity_induction A X hd hnd (k + 1) hk
  have hG : ∀ c c' : Fin m, ∃ c0 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d =>
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
          (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c')
      atTop (fun _ => c0) := fun c c' => ⟨_, hC1 c c'⟩
  have hdec := decoupling_tendsto A X k hk (hnd (k + 1) (by omega) hk) hG hI1 α β
  have hF : ∀ n : ℕ, Measurable (fun ω : DeepSpace d =>
      deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ α β -
      deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ α β *
        deepDerivativeGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ α β) :=
    fun n => (measurable_sensitivityGram_entry (n0 := n0) X hφ_cont.measurable hφ'_cont.measurable
        n k (by omega) α β).sub
      ((measurable_sensitivityGram_entry (n0 := n0) X hφ_cont.measurable hφ'_cont.measurable
        n (k + 1) hk α β).mul
        (measurable_derivativeGram_entry (n0 := n0) X hφ_cont.measurable hφ'_cont.measurable
          n k (by omega) α β))
  have hT := tendstoInMeasure_prod_of_prefix_prod d _ _ hF hdec
  rw [tendstoInMeasure_iff_dist] at hT
  refine (hT ε hε).congr fun n => ?_
  congr 1
  ext q
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, deepParams_prefix hd]

/-- **Backward covariance concentration (the core of Theorem 2.27).** For `k < d` the empirical
backward Gram entry `G_k^{(n), αβ} = n⁻¹ ⟨g_k^α, g_k^β⟩` (`deepSensitivityGram`) converges in
measure to the limiting backward covariance `Π^k_{αβ}` (`deepLimitingSensitivityKernel`).

Downward induction on `k`, carried out jointly with the gradient-independence invariant
`I(k): n⁻¹ ⟨h_k^b, g_k^a⟩ → 0` on `DeepSpace` (`deepSpace_sensitivity_induction`). The top hidden
layer is `sensitivityGram_top_tendsto` (limit `Σ̇^{d-1} = Π^{d-1}`, as `Π^d = 1`). For `k + 1 < d`,
`G_k ≈ G_{k+1} · Φ'_k` (`decoupling_tendsto`), the induction hypothesis gives `G_{k+1} → Π^{k+1}`,
the derivative Gram converges to `Σ̇^k` (`derivGram_tendsto`), and `tendstoInMeasure_mul` combines
them into `Σ̇^k · Π^{k+1} = Π^k`.

**Extra hypothesis `hnd`** (positive-definite `Σ^ℓ`, `1 ≤ ℓ < d`; see
`deepSensitivityGram_sub_mul_tendstoInMeasure`), because the induction step uses the decoupling
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
the decoupling approximation `deepSensitivityGram_sub_mul_tendstoInMeasure` (control of the
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
