/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.GaussianDecoupling
public import LeanMachineLearning.Optimization.NTK.Initialization.ReadoutConcentration

/-!
# Backward Sensitivity Concentration and Theorem 2.27

Convergence in measure of the backward sensitivity Gram matrices `deepSensitivityGram` to the
limiting
kernels `deepLimitingSensitivityKernel`, by downward induction on the layer, and the resulting
convergence of the deep empirical NTK (Theorem 2.27).

* `NTK.deepSensitivityGram_readout_entry_tendstoInMeasure` (top hidden layer,
  `g_{d-1} = W_d ⊙ φ'(h_{d-1})`):
  fully proved from the derivative-Gram concentration and the Gaussian-weighted average lemma
  `tendstoInMeasure_gaussianSq_weighted_average`.
* `NTK.deepSensitivityGram_sub_mul_tendstoInMeasure` (decoupling approximation
  `G_k - G_{k+1} · Φ'_k → 0`): the one remaining `sorry`, with an informal proof.
* `NTK.deepSensitivityGram_entry_tendstoInMeasure`: the downward induction, proved from the two
  above.
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
`∫ φ' φ' d𝒩(0, Σ^{d-1})`. -/
theorem deepSensitivityGram_readout_entry_tendstoInMeasure
    (d n0 m : ℕ) (hd : 0 < d) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (C' : ℝ) (hC' : 0 ≤ C') (p' : ℕ) (hp' : 0 < p')
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
  have hd1 : d - 1 < d := by omega
  -- convergence of the derivative Gram and of the average of its squares, on the prefix space
  have hν := deepEmpiricalFeatureCovariance_tendstoInMeasure n0 m d φ φ' hφ_cont hφ'_cont C hC p hp
    hφ_growth C' hC' p' hp' hφ'_growth X (d - 1) hd1
  have hD0 := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Fin m → Fin m → ℝ => M α β) hν
    (by exact ((continuous_apply β).comp (continuous_apply α)).continuousAt)
  have hν2 := deepEmpiricalFeatureCovariance_tendstoInMeasure n0 m d φ (fun x => φ' x ^ 2)
    hφ_cont (hφ'_cont.pow 2) C hC p hp hφ_growth (2 * C' ^ 2) (by positivity) (2 * p') (by omega)
    (polynomial_growth_sq φ' C' p' hφ'_growth) X (d - 1) hd1
  have hM0 := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Fin m → Fin m → ℝ => M α β) hν2
    (by exact ((continuous_apply β).comp (continuous_apply α)).continuousAt)
  have hy_meas : ∀ (n : ℕ) (j : Fin n), Measurable (fun w : Fin d → ℕ → ℕ → ℝ =>
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) α j) *
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) β j)) :=
    fun n j => (hφ'_cont.measurable.comp
        (measurable_deepPreactivation n0 m n d φ hφ_cont.measurable X (d - 1) α j)).mul
      (hφ'_cont.measurable.comp (measurable_deepPreactivation n0 m n d φ hφ_cont.measurable X
        (d - 1) β j))
  have hW := tendstoInMeasure_gaussianSq_weighted_average
    (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
    (fun (n : ℕ) (w : Fin d → ℕ → ℕ → ℝ) (j : Fin n) =>
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) α j) *
      φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then w ⟨k, h⟩ else 0) (d - 1) β j))
    hy_meas _ _ hD0
    (by
      refine hM0.congr' (Eventually.of_forall fun n => ae_of_all _ fun w => ?_) EventuallyEq.rfl
      simp only [mul_pow])
  have hF_meas : ∀ n : ℕ, Measurable (fun q : (Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ) =>
      (n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val ^ 2 *
        (φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then q.1 ⟨k, h⟩ else 0)
          (d - 1) α j) *
        φ' (deepPreactivation n0 m n φ X (fun k => if h : k < d then q.1 ⟨k, h⟩ else 0)
          (d - 1) β j))) := by
    intro n
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact (((measurable_pi_apply j.val).comp measurable_snd).pow_const 2).mul
      ((hy_meas n j).comp measurable_fst)
  have hT := tendstoInMeasure_prod_of_prefix_prod d _ _ hF_meas hW
  convert hT using 3
  · rename_i n q
    have hcongr := deepPreactivation_eq_prefix n0 m n d φ X q.1 (d - 1) (by omega)
    rw [deepSensitivityGram_hidden d n0 n m φ φ' X _ (d - 1) hd1, Matrix.of_apply]
    simp only [dotProduct, backwardSensitivity_top d n0 n m φ φ' X _ hd,
      deepMLPPreactivation_ofTensor_eq_deepPreactivation d n0 n m φ X q.1 q.2 (d - 1) hd1, hcongr]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [DeepMLPParams.ofTensor]
    ring
  · rfl

/-- **Decoupling approximation (sub-lemma 1.3, the hard core of the backward induction).** For a
hidden layer `k` with `k + 1 < d`, the backward Gram entry at layer `k` is asymptotically the
product of
the backward Gram entry at layer `k + 1` and the derivative Gram entry at layer `k`:
`G_k^{(n),αβ} - G_{k+1}^{(n),αβ} · Φ'^{(n),αβ}_k → 0` in measure.

**Extra hypothesis `hnd`:** the limiting forward kernel `Σ^ℓ = layerCovarianceSeq 1 0 φ m Φ0 ℓ`
(the limit of the activation Gram `n⁻¹ ⟨φ(h_{ℓ-1}^α), φ(h_{ℓ-1}^β)⟩`, `Φ0 = X Xᵀ / n0`) is
**positive definite** for every `1 ≤ ℓ < d` (the input layer `ℓ = 0` is not constrained). The
orthogonal projector onto the span of the `m` forward features is controlled through the
pseudo-inverse `Σ̂⁺` of the empirical Gram, which is only uniformly bounded when the limiting
Gram is invertible. The hypothesis is expected to hold for generic inputs and a non-polynomial
activation (not proved here), but it fails for linear `φ` once `m > n0`, and for repeated or
collinear inputs. It is *not* needed for the forward results, and is the only reason the
backward induction and Theorem 2.27 below carry it.

Informal proof (corrected; the naive "rank-`m` part is `O(m/n)`" bound is **false** here). With
`D = diag(φ'(h_k^α) φ'(h_k^β))` (it depends only on layers `≤ k`) and `u^γ = g_{k+1}^γ`,
`G_k^{αβ} = n⁻² (u^α)ᵀ W_{k+1} D W_{k+1}ᵀ u^β`. Let `Φ = [φ(h_k^1) … φ(h_k^m)]` and `P` the
orthogonal projector onto its span; `W_{k+1} = W_{k+1} P + W_{k+1} Pᗮ`
(`orthogonalDecomposition`). The forward pass, hence `u`, sees `W_{k+1}` only through `W_{k+1} P`
(`orthogonalDecomposition_mul`), while `W_{k+1} Pᗮ` is independent of `(W_{k+1} P, later layers)`
(`indepFun_conditioned_weight_history`). So `n^{-1/2} W_{k+1}ᵀ u = Pᗮ-part + P-part`:

* **Pᗮ-part** `n^{-1/2} Pᗮ W̃ᵀ u` (`W̃` an independent Gaussian copy): conditionally on the
  sigma-algebra `F` generated by everything else, the quadratic form has mean
  `n⁻² (u^α ⬝ u^β) tr(D Pᗮ) = G_{k+1}^{αβ} Φ'^{αβ}_k - O(m/n)`
  (`integral_gaussianMatrix_quadForm`, `backward_empirical_quadForm_asymptotic_limit`) and variance
  `O(n⁻¹)` (Gaussian fourth moments), so Chebyshev closes it
  (`tendsto_of_lintegral_section_bound`).
* **P-part** `n^{-1/2} P W_{k+1}ᵀ u = Φ c` with `c = Σ̂⁺ (z^a ⬝ u^γ)/n`, `Σ̂ = n⁻¹ΦᵀΦ`,
  `z = h_{k+1}`. This is *not* negligible by rank alone: `u` depends on `W_{k+1} P` through `z`, so
  its size is exactly `(z ⬝ u / n)ᵀ Σ̂⁺ (z ⬝ u / n)`. It vanishes only thanks to the
  **gradient-independence invariant** `I(ℓ)`: `n⁻¹ ⟨h_ℓ^a, g_ℓ^γ⟩ → 0` in measure.
  `I(d-1)` is a plain Chebyshev bound (`g_{d-1} = w_out ⊙ φ'(h_{d-1})` with `w_out` an independent
  centred Gaussian), and
  `I(ℓ)` follows from `I(ℓ+1)` and the same `Pᗮ`/`P` split. The decoupling lemma and `I` therefore
  have to be proved in one joint downward induction on `ℓ`.

Available tools (all sorry-free): the exact decomposition `Vᵀ u = Φ c + (V Pᗮ)ᵀ u`
(`transpose_mulVec_eq_gramProjector_add`, `Foundations/GramProjector.lean`); the conditioning on
the projected part and the future, `conditional_quadForm_chebyshev` and
`conditional_linearForm_chebyshev` (`Initialization/GaussianConditioning.lean`, built on Lemma 2.26
and `gaussianInit_quadForm_chebyshev`), applied with `A = D`, whose bound is
`2 ‖u‖² ‖v‖² ‖D‖_F² / ε²` since `‖Pᗮ D Pᗮ‖_F ≤ ‖D‖_F` (`frobSq_compress_le`); the rank bound
`trace_orthogonalProjectionOfGram` (`tr P = m`); and, under `hnd`,
`tendstoInMeasure_matrix_inv_of_posDef`, giving `Σ̂⁻¹ → (Σ^{k+1})⁻¹`, so `Σ̂⁺ = Σ̂⁻¹` is `O_ℙ(1)`.

Remaining plan (deterministic part first, all quantities normalised by `n`): with `f = φ'(h^α)`,
`g = φ'(h^β)`, `s = n^{-1/2} Vᵀ u^α = x + y` (`x = Φ (Σ̂⁻¹ ζ)`, `ζ = n⁻¹ ⟨h_{k+1}, u^α⟩`) and
`N_f(a) = n⁻¹ ∑ⱼ fⱼ² aⱼ²`, Cauchy–Schwarz gives
`|G_k − G_⊥|² ≤ 3 [N_f(x) N_g(x') + N_f(x) N_g(y') + N_f(y) N_g(x')]`, where `G_⊥` is the `Pᗮ`
quadratic form. Then: (1) `G_⊥ − G_{k+1} Φ'_k → 0` by `conditional_quadForm_chebyshev`, the squeeze
`tendsto_of_lintegral_section_bound`, and `tr(D P) = tr(Σ̂⁻¹ M̂) = O_ℙ(1)`; (2) `N_f(x) → 0` from
`ζ → 0` (`I(k+1)`), `Σ̂⁻¹ → (Σ^{k+1})⁻¹` and tightness of `M̂` (dominated by pairwise averages of
`φ²`, `φ'²` already covered by `deepEmpiricalFeatureCovariance_tendstoInMeasure`); (3) `N_f(y)`
is tight by the same conditional Chebyshev; (4) `I(ℓ)` by its own downward induction using
`conditional_linearForm_chebyshev`. Network-side prerequisites: `g_{k+1}` depends on `V = W_{k+1}`
only through `V Φ` (a congruence lemma like `deepPreactivation_congr_of_eqOn` for the backward
pass), and a measure-preserving splitting of the layer `W_{k+1}` from the other layers and the
readout (`measurePreserving_piFinSuccAbove`). -/
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
  sorry

/-- **Backward covariance concentration (the core of Theorem 2.27).** For `k < d` the empirical
backward Gram entry `G_k^{(n), αβ} = n⁻¹ ⟨g_k^α, g_k^β⟩` (`deepSensitivityGram`) converges in
measure to the limiting backward covariance `Π^k_{αβ}` (`deepLimitingSensitivityKernel`).

Downward induction on `k`. The top hidden layer is
`deepSensitivityGram_readout_entry_tendstoInMeasure`
(limit `Σ̇^{d-1} = Π^{d-1}`, as `Π^d = 1`). For `k + 1 < d`, `G_k ≈ G_{k+1} · Φ'_k`
(`deepSensitivityGram_sub_mul_tendstoInMeasure`), the induction hypothesis gives
`G_{k+1} → Π^{k+1}`,
the derivative Gram converges to `Σ̇^k` (`deepDerivativeGram_entry_tendstoInMeasure`), and
`tendstoInMeasure_sum_mul` combines them into `Σ̇^k · Π^{k+1} = Π^k`.

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
  have key : ∀ j : ℕ, ∀ k : ℕ, ∀ hk : k < d, k + j = d - 1 →
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
    intro j
    induction j with
    | zero =>
      intro k hk hkj
      obtain rfl : k = d - 1 := by omega
      have h := deepSensitivityGram_readout_entry_tendstoInMeasure d n0 m hd φ φ' hφ_cont hφ'_cont
        C hC p hp hφ_growth C hC p hp hφ'_growth X α β
      have hterm : deepLimitingSensitivityKernel d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨d - 1 + 1, by omega⟩ =
          Matrix.of fun _ _ => 1 := by
        have : (⟨d - 1 + 1, by omega⟩ : Fin (d + 1)) = ⟨d, by omega⟩ :=
          Fin.ext (Nat.sub_add_cancel (by omega))
        rw [this]
        exact deepLimitingSensitivityKernel_terminal d m φ φ' _
      have hlim := congrFun (congrFun
        (deepLimitingSensitivityKernel_step d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨d - 1, by omega⟩
          (by simp; omega)) α) β
      simp only [Matrix.hadamard_apply, hterm, Matrix.of_apply, mul_one] at hlim
      rw [hlim]
      exact h
    | succ j ih =>
      intro k hk hkj
      have hk1 : k + 1 < d := by omega
      have hG := ih (k + 1) hk1 (by omega)
      have hD := deepDerivativeGram_entry_tendstoInMeasure d n0 m φ φ' hφ_cont hφ'_cont C hC p hp
        hφ_growth C hC p hp hφ'_growth X k hk α β
      have hprod := tendstoInMeasure_mul hG hD
      have hlim := congrFun (congrFun
        (deepLimitingSensitivityKernel_step d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ hk) α) β
      simp only [Matrix.hadamard_apply, Matrix.of_apply] at hlim
      rw [hlim, mul_comm]
      exact tendstoInMeasure_trans
        (fun ε hε => deepSensitivityGram_sub_mul_tendstoInMeasure d n0 m φ φ' hφ_cont hφ'_cont C hC
          p hp hφ_growth hφ'_growth X hnd k hk1 α β hε) hprod
  exact key (d - 1 - k) k hk (by omega)

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
