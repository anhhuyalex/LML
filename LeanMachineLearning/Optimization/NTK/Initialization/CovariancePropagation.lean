/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.MultilayerNNGP

/-!
# Layer-by-layer conditional Gaussian structure and covariance propagation

Independence across depth, the recursive limiting kernel `Φ_ℓ`, and the asymptotic propagation of
the empirical covariance matrix.

## Main results and proof outline

* The depth-$d$ recursive network notation ($h_1^\alpha, h_{\ell+1}^\alpha$, the limiting
  recursion $\boldsymbol{\Phi}_\ell$ via the covariance operator $\mathcal{C}_\varphi$, and
  independence across the per-layer weight matrices $\mathbf{W}_0, \dots, \mathbf{W}_d$ in place
  of an explicit filtration $\mathcal{F}_\ell$) is formalized in
  `section LayerByLayerConditionalGaussian`: see `layerCovarianceSeq`,
  `indepFun_layer_history`, and `exact_conditional_normality_layer` below.
* The recursively-defined deterministic limiting forward covariance kernel
  $\boldsymbol{\Phi}_0, \boldsymbol{\Phi}_{\ell+1} := \mathcal{C}_\varphi(\boldsymbol{\Phi}_\ell)$
  is formalized by `NTK.layerCovarianceSeq`, with positive semidefiniteness at every layer
  `NTK.layerCovarianceSeq_posSemidef` (reusing `NTK.limitingRecurrence_posSemidef_multivariate`
  at each step).
  * The Kronecker concatenation of $n'$ i.i.d. Gaussian vectors into one Gaussian vector with
    covariance $\boldsymbol{\Phi}_\ell^{(n)} \otimes \mathbf{I}_{n'}$
    (`NTK.multivariateGaussian_pi_eq_kronecker`).
* `NTK.conditional_preactivations_eq_pi` makes the coordinate-decoupling consequence explicit:
  conditionally on a fixed preceding layer, new-neuron preactivation vectors have a product law
  of identical centered multivariate Gaussians with the activated empirical covariance.
* For continuous activations of polynomial growth,
  `NTK.conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq` proves that the
  activated empirical covariance of this conditional i.i.d. Gaussian layer converges in
  probability to the next deterministic forward kernel.  The reusable fixed-covariance form is
  `NTK.conditional_empiricalCovariance_tendstoInMeasure_of_polynomial_growth`.
* `NTK.multivariateGaussian_pi_eq_kronecker` : Kronecker-product concatenation of `n` i.i.d.
  Gaussian vectors (built on the `Fin m`-family Propositions 2.9'-2.10' above).
* `NTK.layerCovarianceSeq`, `NTK.layerCovarianceSeq_posSemidef` : the recursive limiting kernel
  $\Phi_\ell$ and its positive semidefiniteness at every layer.
* `NTK.exact_conditional_normality_layer` : Theorem (Conditional Pre-Activation Distribution),
  $\mathbf{H}_{\ell+1} \mid \mathbf{H} \sim \mathcal{N}(\mathbf{0}, \boldsymbol{\Phi}_\ell^{(n)}
    \otimes \mathbf{I}_{n'})$.
* `NTK.conditional_preactivations_eq_pi` : conditional i.i.d. neuron-vector product law.
* `NTK.memLp_activation_coordinate_of_polynomial_growth` : polynomial growth implies the
  coordinatewise Gaussian $L^2$ condition.
* `NTK.conditional_empiricalCovariance_tendstoInMeasure` : conditional empirical covariance
  convergence in probability under a direct $L^2$ hypothesis.

See
`LeanMachineLearning.Optimization.NTK.Initialization`
for the overview of the whole development.
-/

@[expose] public section

set_option linter.style.longLine false

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section LayerByLayerConditionalGaussian

/-! ## Layer-by-Layer Conditional Gaussian Structure -/

/-! ### Recursive Limiting Kernel `Φ_ℓ` -/

/-- The recursively-defined deterministic limiting forward covariance kernel `Φ_ℓ ∈ ℝ^{m × m}`,
built from a base kernel `Φ0` by repeatedly applying the covariance operator
`𝒞_φ(K) := fun α β => σb ^ 2 + σw ^ 2 * ∫ z, φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)`
(the same map that already appears throughout `MultilayerSequentialNNGP`, e.g. in
`limitingRecurrence_posSemidef_multivariate`): `Φ_0 := Φ0`, `Φ_{ℓ+1} := 𝒞_φ(Φ_ℓ)`. -/
noncomputable def layerCovarianceSeq (σw σb : ℝ) (φ : ℝ → ℝ) (m : ℕ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => Φ0
  | ℓ + 1 => fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
      φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 (layerCovarianceSeq σw σb φ m Φ0 ℓ))

/-- The recursive kernel `Φ_ℓ` is positive semidefinite at every layer, provided the base kernel
`Φ0` is and `φ` is square-integrable against `Φ_ℓ` at every layer `ℓ`. Each step reuses the
already-proven `limitingRecurrence_posSemidef_multivariate` (the `MultilayerSequentialNNGP`
single-transition PSD fact) rather than re-deriving positive semidefiniteness from scratch. -/
theorem layerCovarianceSeq_posSemidef (σw σb : ℝ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (m : ℕ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) (hΦ0 : Φ0.PosSemidef)
    (hφ_L2 : ∀ ℓ : ℕ, ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 (layerCovarianceSeq σw σb φ m Φ0 ℓ))) :
    ∀ ℓ : ℕ, (layerCovarianceSeq σw σb φ m Φ0 ℓ).PosSemidef := by
  intro ℓ
  induction ℓ with
  | zero => exact hΦ0
  | succ ℓ _ih =>
    exact limitingRecurrence_posSemidef_multivariate σw σb m φ hφ_meas
      (layerCovarianceSeq σw σb φ m Φ0 ℓ) (hφ_L2 ℓ)

/-! ### Kronecker Concatenation of i.i.d. Gaussian Vectors -/

-- The quadratic form of `Φ ⊗ₖ I` is the sum of `Φ`'s quadratic forms on each block.
private lemma sum_quadraticForm_eq_kronecker_one_quadraticForm
    (Φ : Matrix (Fin m) (Fin m) ℝ) (x : Fin m × Fin n → ℝ) :
    ∑ j : Fin n, (fun α : Fin m => x (α, j)) ⬝ᵥ Φ *ᵥ (fun α : Fin m => x (α, j)) =
      x ⬝ᵥ (Φ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x := by
  have h_lhs : ∀ j : Fin n, (fun α : Fin m => x (α, j)) ⬝ᵥ Φ *ᵥ
      (fun α : Fin m => x (α, j)) =
      ∑ α : Fin m, ∑ β : Fin m, x (α, j) * Φ α β * x (β, j) := by
    intro j
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  have h_collapse : ∀ (α β : Fin m) (j : Fin n),
      ∑ j' : Fin n, Φ α β * (1 : Matrix (Fin n) (Fin n) ℝ) j j' * x (β, j') =
        Φ α β * x (β, j) := by
    intro α β j
    simp [Matrix.one_apply, mul_ite, mul_zero]
  have h_rhs : x ⬝ᵥ (Φ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x =
      ∑ α : Fin m, ∑ j : Fin n, ∑ β : Fin m, x (α, j) * Φ α β * x (β, j) := by
    simp only [dotProduct, mulVec, Fintype.sum_prod_type, kronecker_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [← Finset.mul_sum, h_collapse]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  rw [h_rhs]
  simp_rw [h_lhs]
  rw [Finset.sum_comm]

/-- Concatenating `n` i.i.d. copies of the `m`-variate Gaussian `𝒩(0, Φ)` (indexed `(α, j)` with
`α` the coordinate within a copy and `j` the copy index, matching the paper's stacking
`H = [(h^1)ᵀ, …, (h^m)ᵀ]ᵀ`) is again Gaussian, with Kronecker-product covariance `Φ ⊗ₖ I_n`. -/
theorem multivariateGaussian_pi_eq_kronecker (n m : ℕ) (Φ : Matrix (Fin m) (Fin m) ℝ)
    (hΦ : Φ.PosSemidef) :
    Measure.map (fun Y : Fin n → EuclideanSpace ℝ (Fin m) =>
        WithLp.toLp 2 (fun p : Fin m × Fin n => (Y p.2).ofLp p.1))
      (Measure.pi (fun _ : Fin n => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) Φ)) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m × Fin n))
        (Φ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  set F := fun Y : Fin n → EuclideanSpace ℝ (Fin m) =>
    WithLp.toLp 2 (fun p : Fin m × Fin n => (Y p.2).ofLp p.1) with hF_def
  have hF_meas : Measurable F := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m × Fin n => ℝ)).measurable.comp
    refine measurable_pi_iff.2 fun p => ?_
    exact ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) p.1).measurable).comp
      (measurable_pi_apply p.2)
  have hΦ1 : (Φ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := hΦ.kronecker Matrix.PosSemidef.one
  apply Measure.ext_of_charFun
  ext t
  set tb : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun α => t.ofLp (α, j))
    with htb_def
  have h_inner (Y : Fin n → EuclideanSpace ℝ (Fin m)) :
      ⟪F Y, t⟫ = ∑ j : Fin n, ⟪Y j, tb j⟫ := by
    simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial, hF_def, htb_def]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h_exp : ∀ Y : Fin n → EuclideanSpace ℝ (Fin m),
      Complex.exp ((⟪F Y, t⟫ : ℝ) * Complex.I) =
        ∏ j : Fin n, Complex.exp ((⟪Y j, tb j⟫ : ℝ) * Complex.I) := by
    intro Y
    rw [h_inner Y]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  rw [charFun_apply, integral_map hF_meas.aemeasurable (by fun_prop)]
  simp_rw [h_exp]
  rw [MeasureTheory.integral_fintype_prod_eq_prod (fun j (y : EuclideanSpace ℝ (Fin m)) =>
    Complex.exp ((⟪y, tb j⟫ : ℝ) * Complex.I))]
  simp_rw [← charFun_apply, charFun_multivariateGaussian hΦ]
  rw [charFun_multivariateGaussian hΦ1]
  simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub]
  have h_quadratic : ∑ j : Fin n, (tb j).ofLp ⬝ᵥ Φ *ᵥ (tb j).ofLp =
      t.ofLp ⬝ᵥ (Φ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ t.ofLp := by
    simpa only [htb_def, WithLp.ofLp_toLp] using
      sum_quadraticForm_eq_kronecker_one_quadraticForm Φ t.ofLp
  have h_real : ∑ j : Fin n, -((tb j).ofLp ⬝ᵥ Φ *ᵥ (tb j).ofLp / 2) =
      -(t.ofLp ⬝ᵥ (Φ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ t.ofLp / 2) := by
    rw [← h_quadratic, Finset.sum_div]
    simp
  have h_arg : (∑ j : Fin n, -((((tb j).ofLp ⬝ᵥ Φ *ᵥ (tb j).ofLp : ℝ) : ℂ) / 2)) =
      -((((t.ofLp ⬝ᵥ (Φ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ t.ofLp : ℝ) : ℂ)) / 2) := by
    exact_mod_cast h_real
  rw [← Complex.exp_sum, h_arg]

/-! ### Main Theorem: Conditional Pre-Activation Distribution -/


end LayerByLayerConditionalGaussian

section LayerByLayerConditionalGaussian

/-- **Theorem (Conditional Pre-Activation Distribution)**: conditioned on the `Fin n`-wide
previous-layer post-activations `H` (i.e. on `𝓕_ℓ`; as throughout this file, e.g.
`exact_conditional_normality_general_multivariate`, conditioning is represented by taking `H` as a
plain given argument rather than through `condDistrib`/`Kernel` machinery), the full width-`n'`
next-layer preactivation vector `H_{ℓ+1} ∈ ℝ^{m n'}` — stacked `(α, i)` with `α` the input index and
`i` the neuron index, matching `[(h^1)ᵀ, …, (h^m)ᵀ]ᵀ` — is exactly Gaussian with covariance
`Φ_ℓ^{(n)} ⊗ I_{n'}`, where `Φ_ℓ^{(n)} α β := n⁻¹ ∑ k, H k α * H k β` is the finite-width empirical
covariance of `H` (the `σw = 1, σb = 0` case of `empirical_layer_covariance_posSemidef_multivariate`).
This is the depth generalization of Theorem 1 (`exact_conditional_normality`) combining the
`Fin m`-family Gaussian vector algebra (`gaussianMatrix_mulVec_family`) with the Kronecker
concatenation of the resulting `n'` i.i.d. neuron preactivations
(`multivariateGaussian_pi_eq_kronecker`). -/
theorem exact_conditional_normality_layer (n n' m : ℕ) (H : Fin n → Fin m → ℝ) :
    Measure.map (fun W : Fin n' → Fin n → ℝ =>
        WithLp.toLp 2 (fun p : Fin m × Fin n' =>
          (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W p.2 k * H k p.1))
      (gaussianInit n' n) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m × Fin n'))
        ((show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ k : Fin n, H k α * H k β) ⊗ₖ
          (1 : Matrix (Fin n') (Fin n') ℝ)) := by
  set u : Fin m → Fin n → ℝ := fun α k => (n : ℝ)⁻¹.sqrt * H k α with hu_def
  have hΦ_eq : (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β) =
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ k : Fin n, H k α * H k β) := by
    have hroot : (n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt = (n : ℝ)⁻¹ := Real.mul_self_sqrt (by positivity)
    ext α β
    simp only [Matrix.of_apply, dotProduct, hu_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [show (n : ℝ)⁻¹.sqrt * H k α * ((n : ℝ)⁻¹.sqrt * H k β) =
          ((n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt) * (H k α * H k β) from by ring, hroot]
  have hΦ_pos : (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β).PosSemidef := by
    rw [hΦ_eq]
    simpa using empirical_layer_covariance_posSemidef_multivariate 1 0 n m H
  set F1 : (Fin n' → Fin n → ℝ) → (Fin n' → EuclideanSpace ℝ (Fin m)) :=
    fun W i => WithLp.toLp 2 (fun α : Fin m => W i ⬝ᵥ u α) with hF1_def
  set F2 : (Fin n' → EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m × Fin n') :=
    fun Y => WithLp.toLp 2 (fun p : Fin m × Fin n' => (Y p.2).ofLp p.1) with hF2_def
  have hF1_meas : Measurable F1 := by
    rw [hF1_def]
    refine measurable_pi_iff.2 fun i => ?_
    refine (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp ?_
    refine measurable_pi_iff.2 fun α => ?_
    simp only [dotProduct]
    refine Finset.measurable_sum _ fun k _ => ?_
    have hik : Measurable (fun W : Fin n' → Fin n → ℝ => W i k) :=
      (measurable_pi_apply k).comp (measurable_pi_apply i)
    exact hik.mul_const (u α k)
  have hF2_meas : Measurable F2 := by
    rw [hF2_def]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m × Fin n' => ℝ)).measurable.comp
    refine measurable_pi_iff.2 fun p => ?_
    exact ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) p.1).measurable).comp
      (measurable_pi_apply p.2)
  have hmap_eq : (fun W : Fin n' → Fin n → ℝ =>
      WithLp.toLp 2 (fun p : Fin m × Fin n' => (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W p.2 k * H k p.1)) =
      F2 ∘ F1 := by
    funext W
    rw [hF2_def, hF1_def]
    congr 1
    funext p
    simp only [dotProduct, hu_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hmap_eq, ← Measure.map_map hF2_meas hF1_meas, hF1_def, gaussianMatrix_mulVec_family,
    multivariateGaussian_pi_eq_kronecker n' m _ hΦ_pos, hΦ_eq]

end LayerByLayerConditionalGaussian

section AsymptoticEmpiricalCovariancePropagation

/-! ## Asymptotic Propagation of the Empirical Covariance Matrix

For a fixed realization of the preceding layer, the next-layer weight matrix is independent of
that realization.  `conditional_preactivations_eq_pi` records the resulting conditional product
law: its neuron-indexed preactivation vectors are i.i.d. centered multivariate Gaussians whose
covariance is the empirical activated covariance of the preceding layer.  The theorems below then
apply the existing multivariate SLLN on this conditional product space.  In particular,
`TendstoInMeasure` is convergence in probability.

The polynomial-growth theorem assumes continuity as well as the growth bound.  Continuity is
needed for the subsequent deterministic covariance recursion at singular covariance matrices;
the SLLN itself only needs the resulting `L²` hypothesis.
-/

/-- **Coordinate decoupling for a conditional layer.**  After the preceding preactivations `H`
are fixed, the vectors indexed by the new neurons are independent, identically distributed
centered Gaussians.  Their common covariance is the activated empirical covariance of `H`.

This is the product-law form of the Kronecker statement in
`exact_conditional_normality_layer`; it is obtained directly from
`gaussianMatrix_mulVec_family`. -/
theorem conditional_preactivations_eq_pi (n n' m : ℕ) (φ : ℝ → ℝ)
    (H : Fin n → EuclideanSpace ℝ (Fin m)) :
    Measure.map
      (fun W : Fin n' → Fin n → ℝ =>
        fun j : Fin n' => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j k * φ ((H k).ofLp α))
      (gaussianInit n' n) =
      Measure.pi (fun _ : Fin n' =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β : Fin m =>
            (n : ℝ)⁻¹ * ∑ k : Fin n,
              φ ((H k).ofLp α) * φ ((H k).ofLp β))) := by
  let u : Fin m → Fin n → ℝ := fun α k =>
    (n : ℝ)⁻¹.sqrt * φ ((H k).ofLp α)
  have h_map :
      (fun W : Fin n' → Fin n → ℝ =>
        fun j : Fin n' => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j k * φ ((H k).ofLp α)) =
      (fun W : Fin n' → Fin n → ℝ =>
        fun j : Fin n' => WithLp.toLp 2 fun α : Fin m => W j ⬝ᵥ u α) := by
    funext W j
    congr 1
    funext α
    simp only [dotProduct, u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h_map, gaussianMatrix_mulVec_family]
  congr 1
  funext j
  congr 1
  ext α β
  simp only [Matrix.of_apply, dotProduct, u, Finset.mul_sum]
  have hroot : (n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt = (n : ℝ)⁻¹ :=
    Real.mul_self_sqrt (by positivity)
  exact Finset.sum_congr rfl fun k _ => by
    rw [show (n : ℝ)⁻¹.sqrt * φ ((H k).ofLp α) *
        ((n : ℝ)⁻¹.sqrt * φ ((H k).ofLp β)) =
        ((n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt) *
          (φ ((H k).ofLp α) * φ ((H k).ofLp β)) by ring, hroot]

/-- The activated empirical covariance appearing in `conditional_preactivations_eq_pi` is
positive semidefinite. -/
lemma conditional_preactivation_covariance_posSemidef (n m : ℕ) (φ : ℝ → ℝ)
    (H : Fin n → EuclideanSpace ℝ (Fin m)) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β : Fin m =>
      (n : ℝ)⁻¹ * ∑ k : Fin n,
        φ ((H k).ofLp α) * φ ((H k).ofLp β)).PosSemidef := by
  simpa using empirical_layer_covariance_posSemidef_multivariate 1 0 n m
    (fun k α => φ ((H k).ofLp α))

/-- Polynomial growth gives the coordinatewise `L²` hypothesis required by the conditional
covariance SLLN.  Gaussian measures have moments of every finite order, so no boundedness
assumption on the activation is needed. -/
lemma memLp_activation_coordinate_of_polynomial_growth
    (m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (α : Fin m) :
    MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K) := by
  let μ : Measure (EuclideanSpace ℝ (Fin m)) := multivariateGaussian 0 K
  have h_id : MemLp id (↑(2 * p) : ℝ≥0∞) μ :=
    IsGaussian.memLp_id μ (↑(2 * p) : ℝ≥0∞)
      (ENNReal.natCast_ne_top (2 * p))
  have hnorm : MemLp (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖ ^ p) 2 μ := by
    have h := (memLp_norm_rpow_iff (f := id) (q := (p : ℝ≥0∞))
      (by fun_prop) (by exact_mod_cast hp.ne') (by simp)).mpr h_id
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
    have hquot : (↑(2 * p) : ℝ≥0∞) / (p : ℝ≥0∞) = 2 := by
      rw [Nat.cast_mul, ENNReal.mul_div_cancel_right hp0 (by simp)]
      norm_num
    rw [hquot] at h
    simpa using h
  have hbase : MemLp (fun z : EuclideanSpace ℝ (Fin m) => C * (1 + ‖z‖ ^ p)) 2 μ := by
    simpa using ((memLp_const (μ := μ) (1 : ℝ)).add hnorm).const_mul C
  refine hbase.mono ?_ ?_
  · exact (hφ_meas.comp
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs]
  calc
    |φ (z.ofLp α)| ≤ C * (1 + |z.ofLp α| ^ p) := hφ_growth _
    _ ≤ C * (1 + ‖z‖ ^ p) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add_right
      simpa only [Real.norm_eq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (PiLp.norm_apply_le z α) p
    _ ≤ |C * (1 + ‖z‖ ^ p)| := le_abs_self _

/-- The polynomial-growth activation bound at any finite natural `Lq` exponent.  The `L²`
specialization above is the SLLN interface; this slightly more general companion is used for the
fourth moments which control the conditional empirical-covariance fluctuation. -/
lemma memLp_activation_coordinate_of_polynomial_growth_of_nat
    (m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (p q : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (α : Fin m) :
    MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) q
      (multivariateGaussian 0 K) := by
  let μ : Measure (EuclideanSpace ℝ (Fin m)) := multivariateGaussian 0 K
  have h_id : MemLp id (↑(q * p) : ℝ≥0∞) μ :=
    IsGaussian.memLp_id μ (↑(q * p) : ℝ≥0∞)
      (ENNReal.natCast_ne_top (q * p))
  have hnorm : MemLp (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖ ^ p) q μ := by
    have h := (memLp_norm_rpow_iff (f := id) (q := (p : ℝ≥0∞))
      (by fun_prop) (by exact_mod_cast hp.ne') (by simp)).mpr h_id
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
    have hquot : (↑(q * p) : ℝ≥0∞) / (p : ℝ≥0∞) = q := by
      rw [Nat.cast_mul, ENNReal.mul_div_cancel_right hp0 (by simp)]
    rw [hquot] at h
    simpa using h
  have hbase : MemLp (fun z : EuclideanSpace ℝ (Fin m) => C * (1 + ‖z‖ ^ p)) q μ := by
    simpa using ((memLp_const (μ := μ) (1 : ℝ)).add hnorm).const_mul C
  refine hbase.mono ?_ ?_
  · exact (hφ_meas.comp
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs]
  calc
    |φ (z.ofLp α)| ≤ C * (1 + |z.ofLp α| ^ p) := hφ_growth _
    _ ≤ C * (1 + ‖z‖ ^ p) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add_right
      simpa only [Real.norm_eq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (PiLp.norm_apply_le z α) p
    _ ≤ |C * (1 + ‖z‖ ^ p)| := le_abs_self _

/-- Products of two activated Gaussian coordinates are square-integrable.  This is the exact
moment hypothesis for Chebyshev's inequality applied to a covariance entry. -/
lemma memLp_activation_product_of_polynomial_growth
    (m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (α β : Fin m) :
    MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α) * φ (z.ofLp β)) 2
      (multivariateGaussian 0 K) := by
  have hα : MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) (4 : ENNReal)
      (multivariateGaussian 0 K) :=
    memLp_activation_coordinate_of_polynomial_growth_of_nat m K φ hφ_meas C hC p 4 hp
      hφ_growth α
  have hβ : MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp β)) (4 : ENNReal)
      (multivariateGaussian 0 K) :=
    memLp_activation_coordinate_of_polynomial_growth_of_nat m K φ hφ_meas C hC p 4 hp
      hφ_growth β
  let _ : ENNReal.HolderTriple (4 : ENNReal) 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_inv]⟩
  change MemLp ((fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) *
    fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp β)) 2 (multivariateGaussian 0 K)
  exact hβ.mul (r := (2 : ℝ≥0∞)) hα

/-- The same square-integrability statement after selecting one coordinate from a finite i.i.d.
Gaussian layer.  This is the form consumed by `variance_sum_pi`. -/
lemma memLp_activation_product_pi_of_polynomial_growth
    (n m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (j : Fin n) (α β : Fin m) :
    MemLp (fun Z : Fin n → EuclideanSpace ℝ (Fin m) =>
      φ ((Z j).ofLp α) * φ ((Z j).ofLp β)) 2
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 K) :=
  (memLp_activation_product_of_polynomial_growth m K φ hφ_meas C hC p hp hφ_growth α β).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => multivariateGaussian 0 K) j)

/-- Entrywise Chebyshev estimate for a finite i.i.d. Gaussian layer.  The variance is deliberately
left explicit: in the deep induction it is controlled after conditioning on the previous random
layer and localizing its empirical covariance near the deterministic limit. -/
lemma empiricalCovariance_entry_chebyshev_of_polynomial_growth
    (n m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ)
    (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (α β : Fin m) {ε : ℝ} (hε : 0 < ε) :
    let μ : Measure (Fin n → EuclideanSpace ℝ (Fin m)) :=
      Measure.pi fun _ : Fin n => multivariateGaussian 0 K
    μ {Z | ε ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n,
        φ ((Z j).ofLp α) * φ ((Z j).ofLp β) -
          ∫ z : Fin n → EuclideanSpace ℝ (Fin m),
            (n : ℝ)⁻¹ * ∑ j : Fin n,
              φ ((z j).ofLp α) * φ ((z j).ofLp β) ∂μ|} ≤
      ENNReal.ofReal
        (variance (fun Z : Fin n → EuclideanSpace ℝ (Fin m) => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ ((Z j).ofLp α) * φ ((Z j).ofLp β)) μ / ε ^ 2) := by
  dsimp
  apply meas_ge_le_variance_div_sq
  · exact (memLp_finsetSum Finset.univ fun j _ =>
      memLp_activation_product_pi_of_polynomial_growth n m K φ hφ_cont.measurable C hC p hp
        hφ_growth j α β).const_mul _
  · exact hε

/-- The variance in the entrywise Chebyshev estimate is `O(n⁻¹)`.  The right-hand side is the
single-neuron second moment; it will be locally bounded when the random empirical covariance of
the preceding layer converges to its deterministic limit. -/
lemma variance_empiricalCovariance_entry_le_of_polynomial_growth
    (n m : ℕ) (hn : 0 < n) (K : Matrix (Fin m) (Fin m) ℝ)
    (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (α β : Fin m) :
    let μ : Measure (Fin n → EuclideanSpace ℝ (Fin m)) :=
      Measure.pi fun _ : Fin n => multivariateGaussian 0 K
    variance (fun Z : Fin n → EuclideanSpace ℝ (Fin m) => (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ ((Z j).ofLp α) * φ ((Z j).ofLp β)) μ ≤
      (n : ℝ)⁻¹ * ∫ z : EuclideanSpace ℝ (Fin m),
        (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K := by
  dsimp
  let Y : Fin n → EuclideanSpace ℝ (Fin m) → ℝ :=
    fun j z => φ (z.ofLp α) * φ (z.ofLp β)
  have hY : ∀ j : Fin n, MemLp (Y j) 2 (multivariateGaussian 0 K) := fun j =>
    memLp_activation_product_of_polynomial_growth m K φ hφ_cont.measurable C hC p hp
      hφ_growth α β
  have hsum : MemLp (fun Z : Fin n → EuclideanSpace ℝ (Fin m) => ∑ j : Fin n, Y j (Z j)) 2
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 K) :=
    memLp_finsetSum Finset.univ fun j _ => hY j |>.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => multivariateGaussian 0 K) j)
  have hvar_sum : variance (fun Z : Fin n → EuclideanSpace ℝ (Fin m) => ∑ j : Fin n, Y j (Z j))
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 K) =
      ∑ j : Fin n, variance (Y j) (multivariateGaussian 0 K) := by
    have hsum_eq : (fun Z : Fin n → EuclideanSpace ℝ (Fin m) => ∑ j : Fin n, Y j (Z j)) =
        ∑ j : Fin n, fun Z => Y j (Z j) := by
      funext Z
      simp
    rw [hsum_eq]
    exact variance_sum_pi (μ := fun _ : Fin n => multivariateGaussian 0 K) hY
  have hvar_le : ∀ j : Fin n, variance (Y j) (multivariateGaussian 0 K) ≤
      ∫ z : EuclideanSpace ℝ (Fin m), (Y j z) ^ 2 ∂multivariateGaussian 0 K := fun j =>
    variance_le_expectation_sq (hY j).aestronglyMeasurable
  have hsecond_nonneg : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin m),
      (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K :=
    integral_nonneg fun _ => sq_nonneg _
  have hsum_le : ∑ j : Fin n, variance (Y j) (multivariateGaussian 0 K) ≤
      ∑ j : Fin n, ∫ z : EuclideanSpace ℝ (Fin m), (Y j z) ^ 2 ∂multivariateGaussian 0 K := by
    exact Finset.sum_le_sum fun j _ => hvar_le j
  have hsum_second : ∑ j : Fin n, ∫ z : EuclideanSpace ℝ (Fin m), (Y j z) ^ 2 ∂
      multivariateGaussian 0 K = (n : ℝ) * ∫ z : EuclideanSpace ℝ (Fin m),
        (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K := by
    simp only [Y]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (fun Z : Fin n → EuclideanSpace ℝ (Fin m) => (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ ((Z j).ofLp α) * φ ((Z j).ofLp β)) =
      fun Z => (n : ℝ)⁻¹ * ∑ j : Fin n, Y j (Z j) by rfl, variance_const_mul, hvar_sum]
  calc
    (n : ℝ)⁻¹ ^ 2 * ∑ j : Fin n, variance (Y j) (multivariateGaussian 0 K) ≤
        (n : ℝ)⁻¹ ^ 2 * ∑ j : Fin n, ∫ z : EuclideanSpace ℝ (Fin m),
          (Y j z) ^ 2 ∂multivariateGaussian 0 K := by
      gcongr
    _ = (n : ℝ)⁻¹ * ∫ z : EuclideanSpace ℝ (Fin m),
        (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K := by
      rw [hsum_second]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp

/-- **Conditional empirical covariance propagation.**  For an i.i.d. sequence of conditional
preactivation vectors with law `𝒩(0, K)`, the empirical activated covariance converges in
probability to the Gaussian covariance update of `K`.

The `TendstoInMeasure` conclusion is the formal convergence-in-probability statement.  The
almost-sure SLLN used in the proof is stronger than the conditional Chebyshev conclusion for a
fixed conditioning realization. -/
theorem conditional_empiricalCovariance_tendstoInMeasure
    (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (hφ_L2 : ∀ α : Fin m,
      MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
        (multivariateGaussian 0 K)) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K)
      (fun n : ℕ => fun (Z : ℕ → EuclideanSpace ℝ (Fin m)) => fun α β : Fin m =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β))
      Filter.atTop
      (fun _ => fun α β : Fin m =>
        ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    refine (measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_).aestronglyMeasurable
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact
      (hφ_meas.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable.comp
          (measurable_pi_apply j.val))).mul
      (hφ_meas.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable.comp
          (measurable_pi_apply j.val)))
  simpa using
    (empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate
      1 0 m φ hφ_meas K hφ_L2)

/-- The conditional covariance propagation theorem under the stated polynomial-growth condition.
Continuity supplies measurability, while
`memLp_activation_coordinate_of_polynomial_growth` supplies the SLLN integrability hypothesis. -/
theorem conditional_empiricalCovariance_tendstoInMeasure_of_polynomial_growth
    (m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (K : Matrix (Fin m) (Fin m) ℝ) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K)
      (fun n : ℕ => fun (Z : ℕ → EuclideanSpace ℝ (Fin m)) => fun α β : Fin m =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β))
      Filter.atTop
      (fun _ => fun α β : Fin m =>
        ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) :=
  conditional_empiricalCovariance_tendstoInMeasure m φ hφ_cont.measurable K
    (fun α => memLp_activation_coordinate_of_polynomial_growth
      m K φ hφ_cont.measurable C hC p hp hφ_growth α)


end AsymptoticEmpiricalCovariancePropagation

end NTK

end
