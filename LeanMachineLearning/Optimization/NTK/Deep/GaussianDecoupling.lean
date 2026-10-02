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
3. **Backward concentration** (`deepSensitivityGram_entry_tendstoInMeasure`, currently `sorry`):
   applied to `u = g_{ℓ+1}^α`, `v = g_{ℓ+1}^β` and `A = diag(φ'(h^α) φ'(h^β))`, the quadratic form
   yields the transition factor `G_{ℓ+1}^{(n), αβ} · Φ'^{(n)}_{ℓ, αβ}`.
4. **Theorem 2.27** (`deepEmpiricalNTK_tendstoInMeasure_deepLimitingNTK`): convergence in measure of
   `deepEmpiricalNTK` to `deepLimitingNTK`, from 1–3.
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


/-- **Forward covariance concentration for the finite-parameter network (entrywise).** Transport of
`deepEmpiricalCovariance_tendstoInMeasure` (stated over the `Fin d`-indexed weight population and
for `deepPreactivation`) to the product measure on `(W, w_out)` used for `DeepMLPParams.ofTensor`:
the restriction `W ↦ (W 0, …, W (d - 1))` is measure preserving, and preactivations up to layer `k`
only read `W 0, …, W k` (`deepPreactivation_congr_of_eqOn`). -/
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
  -- project to the `(α, β)` entry
  have hentry := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Matrix (Fin m) (Fin m) ℝ => M α β)
    hν (by exact ((continuous_apply β).comp (continuous_apply α)).continuousAt)
  have hT : MeasurePreserving
      (fun q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ) => fun i : Fin d => q.1 i.val)
      (Measure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) :=
    (measurePreserving_prefixMap (Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) d).comp measurePreserving_fst
  have hmeas : ∀ n : ℕ, Measurable (fun w : Fin d → ℕ → ℕ → ℝ =>
      (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) k α j) *
        φ (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) k β j)) := by
    intro n
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact (hφ_cont.measurable.comp
      (measurable_deepPreactivation n0 m n d φ hφ_cont.measurable X k α j)).mul
      (hφ_cont.measurable.comp (measurable_deepPreactivation n0 m n d φ hφ_cont.measurable X k β j))
  have hcomp := tendstoInMeasure_comp_measurePreserving hentry hT hmeas measurable_const
  convert hcomp using 3
  · rename_i n q
    have hcongr : deepPreactivation n0 m n φ X q.1 k =
        deepPreactivation n0 m n φ X (fun k' => if h : k' < d then q.1 k' else 0) k :=
      deepPreactivation_congr_of_eqOn n0 m n φ X _ _ k fun r hr => by
        simp [show r < d by omega]
    rw [deepActivationGram_succ d n0 n m φ X _ k hk, Matrix.of_apply]
    simp only [dotProduct]
    rw [deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X q.1 q.2 k hk, hcongr]
  · rfl

/-- **Backward covariance concentration (the core of Theorem 2.27).** For `k < d` the empirical
backward Gram entry `G_k^{(n), αβ} = n⁻¹ ⟨g_k^α, g_k^β⟩` (`deepSensitivityGram`) converges in
measure to the limiting backward covariance `Π^k_{αβ}` (`deepLimitingSensitivityKernel`).

Informal proof (downward induction on `k`; source: the Deep NTK source text, "Layerwise Structural
Decomposition", and Lemma 2.26 of the plan):
* `k = d - 1`: `g_{d-1}^α = W_d ⊙ φ'(h_{d-1}^α)`, so
  `G_{d-1}^{αβ} = n⁻¹ ∑_j W_{d,j}² φ'(h^α_j) φ'(h^β_j)`.
  The readout `W_d` is independent of the hidden layers and standard Gaussian, so conditionally on
  the hidden layers this is an i.i.d. average whose mean is `Φ'^{(n)}_{d-1,αβ}` (the empirical
  derivative Gram `deepDerivativeGram`), with conditional variance `O(1/n)`. By the forward
  concentration of `h_{d-1}` and continuity of the derivative-kernel map this tends to
  `Σ̇^{d-1}_{αβ} = Π^{d-1}_{αβ}`.
* `k < d - 1`: `G_k^{αβ} = n⁻² (g_{k+1}^α)ᵀ W_k D^αD^β W_kᵀ g_{k+1}^β` with `D^αD^β =
  diag(φ'(h_k^α) φ'(h_k^β))`. Decompose `W_k = W_k P + W_k Pᗮ` where `P` projects onto the span
  of the `m` forward features `φ(h_k^α)` (`orthogonalDecomposition`). The forward pass uses only
  `W_k P` (`orthogonalDecomposition_mul`), while `W_k Pᗮ` is independent of it
  (`indepFun_conditioned_weight_history`). Replacing `W_k` by an independent copy in the residual
  part costs `O(m/n)` since `rank P ≤ m`. For the independent part the quadratic form has mean
  `(u ⬝ᵥ v) tr A` (`integral_gaussianMatrix_quadForm`, normalized in
  `backward_empirical_quadForm_asymptotic_limit`) and `O(1/n)` variance, giving the product
  `G_{k+1}^{αβ} · Φ'^{(n)}_{k,αβ}`. The induction hypothesis (`G_{k+1}^{(n)} → Π^{k+1}`), the
  forward concentration (`Φ'^{(n)}_k → Σ̇^k`) and `tendstoInMeasure_sum_mul` then yield
  `G_k^{αβ} → Σ̇^k_{αβ} Π^{k+1}_{αβ} = Π^k_{αβ}`. -/
theorem deepSensitivityGram_entry_tendstoInMeasure
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (k : ℕ) (hk : k < d) (α β : Fin m) :
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
  sorry

/-- **Theorem 2.27 (Infinite-Width Convergence of the Deep Empirical NTK to the Limiting NTK)**:
For any depth `d ≥ 1`, input dimension `n0`, sample size `m`, continuous activation `φ` and its
derivative `φ'` with bounded polynomial growth, and input dataset `X`, the empirical Neural Tangent
Kernel Gram matrix `deepEmpiricalNTK` converges entrywise in probability / in measure to the
deterministic recursive limiting NTK `deepLimitingNTK` as network width `n → ∞`. -/
theorem deepEmpiricalNTK_tendstoInMeasure_deepLimitingNTK
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (α β : Fin m) :
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
      C hC p hp hφ_growth hφ'_growth X k hk α β)

end NTK

end
