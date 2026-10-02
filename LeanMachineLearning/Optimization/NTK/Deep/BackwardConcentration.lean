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
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix ENNReal

namespace NTK

/-- Transport with the readout kept: `(W, w_out) ↦ ((W 0, …, W (d-1)), w_out)`. -/
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
    have hcongr : deepPreactivation n0 m n φ X q.1 (d - 1) =
        deepPreactivation n0 m n φ X (fun k' => if h : k' < d then q.1 k' else 0) (d - 1) :=
      deepPreactivation_congr_of_eqOn n0 m n φ X _ _ (d - 1) fun r hr => by
        simp [show r < d by omega]
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

Informal proof: with `D = diag(φ'(h_k^α) φ'(h_k^β))` (it depends only on layers `≤ k`),
`G_k^{αβ} = n⁻² (g_{k+1}^α)ᵀ W_k D Wₖᵀ g_{k+1}^β`. Let `P` be the orthogonal projector onto the
span of
the `m` forward features `φ(h_k^α)`. Then `W_k = W_k P + W_k Pᗮ` (`orthogonalDecomposition`). The
forward pass, hence `g_{k+1}`, sees `W_k` only through `W_k P` (`orthogonalDecomposition_mul`),
while
`W_k Pᗮ` is independent of `(W_k P, later layers)` (`indepFun_conditioned_weight_history`). The
terms
containing `W_k P` have rank `≤ m ≪ n` and are `O(m/n)`. For the `W_k Pᗮ`–`W_k Pᗮ` term the
quadratic form
has conditional mean `n⁻² (g_{k+1}^α ⬝ g_{k+1}^β) tr(D Pᗮ) = G_{k+1}^{αβ} · Φ'^{αβ}_k - O(m/n)`
(`integral_gaussianMatrix_quadForm`, `backward_empirical_quadForm_asymptotic_limit`) and conditional
variance `O(n⁻¹)` (a fourth-moment computation for the Gaussian quadratic form), so Chebyshev
closes the
estimate. -/
theorem deepSensitivityGram_sub_mul_tendstoInMeasure
    (d n0 m : ℕ) (φ φ' : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (hφ'_growth : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin n0 → ℝ) (k : ℕ) (hk : k + 1 < d) (α β : Fin m) {ε : ℝ} (hε : 0 < ε) :
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
`tendstoInMeasure_sum_mul` combines them into `Σ̇^k · Π^{k+1} = Π^k`. -/
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
          Fin.ext (by show d - 1 + 1 = d; omega)
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
          p hp hφ_growth hφ'_growth X k hk1 α β hε) hprod
  exact key (d - 1 - k) k hk (by omega)

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
