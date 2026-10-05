/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.NNGPLimit

/-!
# Multilayer sequential NNGP

Conditional normality and recurrence convergence for sequentially built multilayer networks.

## Main results and proof outline

* Exact Conditional Normality across layers
  (`NTK.exact_conditional_normality_general_multivariate`):
  Conditional on previous layer activations $\mathbf{H} \in \mathbb{R}^{n \times m}$, the
  preactivations vector is exact centered multivariate Gaussian:
  $$h^{(\ell+1)} \mid \mathbf{H} \sim
    \mathcal{N}\left(\mathbf{0}, \boldsymbol{\Sigma}^{(\ell+1), (n)}\right)$$
  with empirical layer covariance matrix:
  $$\Sigma^{(\ell+1), (n)}_{\alpha \beta} :=
    \sigma_b^2 + \frac{\sigma_w^2}{n} \sum_{j=1}^n
      \varphi(h_{j,\alpha}^{(\ell)}) \varphi(h_{j,\beta}^{(\ell)})$$
  which is symmetric positive semidefinite
  (`NTK.empirical_layer_covariance_posSemidef_multivariate`).
* Strong Law of Large Numbers for the Covariance Recurrence
  (`NTK.empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate`):
  When previous-layer preactivation draws are i.i.d. from $\mathcal{N}(\mathbf{0}, \mathbf{K})$,
  the empirical layer covariance converges entrywise almost surely:
  $$\Sigma^{(\ell+1), (n)}_{\alpha \beta} \xrightarrow{\text{a.s.}}
    \Sigma^{(\ell+1)}_{\alpha \beta} := \sigma_b^2 + \sigma_w^2
      \int \varphi(z_\alpha) \varphi(z_\beta) d\mathcal{N}(\mathbf{0}, \mathbf{K})$$
  and the limiting recurrence matrix is symmetric positive semidefinite
  (`NTK.limitingRecurrence_posSemidef_multivariate`).
* Pointwise characteristic function convergence via Dominated Convergence:
  `NTK.tendsto_charFun_sequential_preactivation_multivariate`.
* Master Theorem (Multivariate Sequential Convergence in Distribution):
  Preactivations converge in distribution to
  $\mathcal{N}(\mathbf{0}, \boldsymbol{\Sigma}^{(\ell+1)})$ for arbitrary $m$:
  `NTK.tendstoInDistribution_sequential_preactivation`.

See
`LeanMachineLearning.Optimization.NTK.Initialization`
for the overview of the whole development.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section MultilayerSequentialNNGP


/-! ## Multilayer Sequential NNGP: Conditional Normality & Recurrence Convergence -/

/-! ### Multivariate sequential preactivation convergence -/

/-- The projection identity used by the conditional Gaussian calculation, for any finite
collection of evaluation points. -/
lemma projection_layer_eq_multivariate (σw σb : ℝ) (n m : ℕ) (H : Fin n → Fin m → ℝ)
    (w : Fin n → ℝ) (b : ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    ⟪t, WithLp.toLp 2 (fun α => σb * b + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j : Fin n, w j * H j α)⟫ =
      (σb * ∑ α : Fin m, t.ofLp α) * b +
        ∑ j : Fin n, w j * ((σw * (n : ℝ)⁻¹.sqrt) * ∑ α : Fin m, t.ofLp α * H j α) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  · calc
      ∑ α : Fin m, t.ofLp α * (σb * b) = (∑ α : Fin m, t.ofLp α) * (σb * b) :=
        (Finset.sum_mul _ _ _).symm
      _ = ∑ α : Fin m, t.ofLp α * (σb * b) := Finset.sum_mul _ _ _
      _ = ∑ α : Fin m, (σb * t.ofLp α) * b :=
        Finset.sum_congr rfl fun α _ => by ring
      _ = (∑ α : Fin m, σb * t.ofLp α) * b := (Finset.sum_mul _ _ _).symm
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => by ring

/-- The empirical covariance quadratic form is the sum of the squared Gaussian coefficients. -/
lemma projection_layer_variance_eq_multivariate (σw σb : ℝ) (n m : ℕ) (H : Fin n → Fin m → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    (σb * ∑ α : Fin m, t.ofLp α) ^ 2 +
      ∑ j : Fin n, ((σw * (n : ℝ)⁻¹.sqrt) * ∑ α : Fin m, t.ofLp α * H j α) ^ 2 =
      t.ofLp ⬝ᵥ (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n, H j α * H j
          β) *ᵥ t.ofLp := by
  have h_square (f : Fin m → ℝ) :
      (∑ α : Fin m, f α) ^ 2 = ∑ α : Fin m, ∑ β : Fin m, f α * f β := by
    rw [pow_two, Fintype.sum_mul_sum]
  have hroot : (σw * (n : ℝ)⁻¹.sqrt) ^ 2 = σw ^ 2 * (n : ℝ)⁻¹ := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [show (σb * ∑ α : Fin m, t.ofLp α) ^ 2 =
      σb ^ 2 * (∑ α : Fin m, t.ofLp α) ^ 2 by ring]
  rw [h_square]
  simp_rw [show ((σw * (n : ℝ)⁻¹.sqrt) * ∑ α : Fin m, t.ofLp α * H _ α) ^ 2 =
      (σw * (n : ℝ)⁻¹.sqrt) ^ 2 * (∑ α : Fin m, t.ofLp α * H _ α) ^ 2 by ring]
  simp_rw [hroot, h_square]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  ring_nf
  have h_reorder :
      (∑ j : Fin n, ∑ α : Fin m, ∑ β : Fin m,
        σw ^ 2 * (n : ℝ)⁻¹ * t.ofLp α * H j α * t.ofLp β * H j β) =
      ∑ α : Fin m, ∑ β : Fin m, ∑ j : Fin n,
        σw ^ 2 * (n : ℝ)⁻¹ * t.ofLp α * H j α * t.ofLp β * H j β := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => by rw [Finset.sum_comm]
  rw [h_reorder]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun j _ => by ring

/-- The empirical layer covariance defines a nonnegative quadratic form: `0 ≤ t ⬝ᵥ Σ⁽ⁿ⁾ *ᵥ t`. -/
lemma empirical_layer_covariance_nonneg_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    0 ≤ t.ofLp ⬝ᵥ (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
      ∑ j : Fin n, H j α * H j β) *ᵥ t.ofLp := by
  rw [← projection_layer_variance_eq_multivariate]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The empirical layer covariance `σb² + σw² n⁻¹ ∑ⱼ Hⱼα Hⱼβ` is Hermitian. -/
lemma empirical_layer_covariance_isHermitian_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) :
    Matrix.IsHermitian (show Matrix (Fin m) (Fin m) ℝ from fun α β =>
      σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n, H j α * H j β) := by
  ext α β
  rw [conjTranspose_apply]
  simp only [star_trivial]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The empirical layer covariance `σb² + σw² n⁻¹ ∑ⱼ Hⱼα Hⱼβ` is positive semidefinite. -/
lemma empirical_layer_covariance_posSemidef_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
      ∑ j : Fin n, H j α * H j β).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (empirical_layer_covariance_isHermitian_multivariate σw σb n m H) ?_
  intro c
  simpa using empirical_layer_covariance_nonneg_multivariate σw σb n m H (WithLp.toLp 2 c)

/-- Strong law for scalar observables of i.i.d. multivariate Gaussian draws. -/
lemma multivariateGaussian_average_tendsto_integral_multivariate
    (m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (hg_meas : Measurable g)
    (hg_int : Integrable g (multivariateGaussian 0 K)) :
    ∀ᵐ seq : ℕ → EuclideanSpace ℝ (Fin m)
      ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K),
      Filter.Tendsto
        (fun width : ℕ => (width : ℝ)⁻¹ * ∑ j : Fin width, g (seq j))
        Filter.atTop (nhds (∫ z, g z ∂(multivariateGaussian 0 K))) :=
  iid_average_tendsto_integral (multivariateGaussian 0 K) g hg_meas hg_int

/-- Almost-sure convergence of every entry of the empirical covariance recurrence. -/
theorem empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) :
    ∀ᵐ Z : ℕ → EuclideanSpace ℝ (Fin m) ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K),
      Filter.Tendsto
        (fun n : ℕ => fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
          ∑ j : Fin n, φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β))
        Filter.atTop
        (nhds (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) := by
  have h_entry : ∀ α β : Fin m,
      ∀ᵐ Z : ℕ → EuclideanSpace ℝ (Fin m) ∂(Measure.infinitePi
          fun _ : ℕ => multivariateGaussian 0 K),
        Filter.Tendsto
          (fun n : ℕ => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
            ∑ j : Fin n, φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β))
          Filter.atTop
          (nhds (σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
            φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) := by
    intro α β
    set g := fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α) * φ (z.ofLp β)
    have hg_meas : Measurable g :=
      (hφ_meas.comp (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable).mul
      (hφ_meas.comp (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable)
    have hg_int : Integrable g (multivariateGaussian 0 K) :=
      (hφ_L2 α).integrable_mul (hφ_L2 β)
    have hslln := multivariateGaussian_average_tendsto_integral_multivariate m K g hg_meas hg_int
    filter_upwards [hslln] with Z hZ
    have h_scale := hZ.const_mul (σw ^ 2)
    simp_rw [← mul_assoc] at h_scale
    exact h_scale.const_add (σb ^ 2)
  exact ae_tendsto_matrix_of_forall_entry h_entry

-- Measurability of the per-layer preactivation map used to build the conditional Gaussian.
private lemma measurable_conditional_preactivation (σw σb : ℝ) (n m : ℕ) (H : Fin n → Fin m → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
      σb * p.2 + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j, p.1 j * H j α) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun α => ?_
  refine (measurable_const.mul measurable_snd).add ?_
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  exact ((measurable_pi_apply j).comp measurable_fst).mul_const _

-- The characteristic-function integral of a centered real Gaussian, evaluated at `1`.
private lemma integral_exp_mul_I_gaussianReal (v : ℝ) (hv : 0 ≤ v) :
    (∫ y : ℝ, Complex.exp (y * Complex.I) ∂gaussianReal 0 (Real.toNNReal v)) =
      Complex.exp (- Complex.ofReal v / 2) := by
  have h_cf : (∫ y : ℝ, Complex.exp (y * Complex.I) ∂gaussianReal 0 (Real.toNNReal v)) =
      charFun (gaussianReal 0 (Real.toNNReal v)) 1 := by
    rw [charFun_apply_real]
    simp
  rw [h_cf, charFun_gaussianReal]
  simp only [ofReal_zero, mul_zero, zero_mul, ofReal_one, mul_one, one_pow, zero_sub]
  rw [Real.coe_toNNReal _ hv]
  congr 1
  rw [neg_div]

-- The characteristic function of a linear form in the Gaussian readout weights.
private lemma integral_exp_sum_mul_I_gaussianReadout (c : Fin n → ℝ) :
    (∫ w : Fin n → ℝ, Complex.exp ((∑ j : Fin n, w j * c j : ℝ) * Complex.I)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) =
      Complex.exp (- Complex.ofReal (∑ j : Fin n, (c j) ^ 2) / 2) := by
  have h_map := map_gaussianReadoutMeasure_inner c
  have h_meas_dot : Measurable (fun w : Fin n → ℝ => ∑ j : Fin n, w j * c j) := by
    refine Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  have h_int : (∫ w : Fin n → ℝ, Complex.exp ((∑ j : Fin n, w j * c j : ℝ) * Complex.I)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) = ∫ y : ℝ, Complex.exp (y * Complex.I)
        ∂Measure.map (fun w => ∑ j : Fin n, w j * c j) (Measure.pi fun _ : Fin n =>
            gaussianReal 0 1) := by
    rw [integral_map h_meas_dot.aemeasurable (by fun_prop)]
  rw [h_int, h_map]
  exact integral_exp_mul_I_gaussianReal _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)

-- The characteristic function of a scalar standard Gaussian at a real frequency.
private lemma integral_exp_mul_I_standardGaussian (c : ℝ) :
    (∫ b : ℝ, Complex.exp ((c * b : ℝ) * Complex.I) ∂gaussianReal 0 1) =
      Complex.exp (- Complex.ofReal (c ^ 2) / 2) := by
  have h_cf : (∫ b : ℝ, Complex.exp ((c * b : ℝ) * Complex.I) ∂gaussianReal 0 1) =
      charFun (gaussianReal 0 1) c := by
    rw [charFun_apply_real]
    congr 1 with b
    push_cast
    ring
  rw [h_cf, charFun_gaussianReal]
  congr 1
  push_cast
  ring

-- The covariance is written as a plain lambda `fun α β => …`, so its type is `Fin m → Fin m → ℝ`
-- rather than `Matrix (Fin m) (Fin m) ℝ`; finding `IsProbabilityMeasure (multivariateGaussian …)`
-- then needs `Matrix` to be unfolded.
set_option backward.isDefEq.respectTransparency.types false in
/-- Conditional on deterministic previous-layer activations, the full `m`-vector of
preactivations is exactly Gaussian. -/
lemma exact_conditional_normality_general_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) :
    Measure.map
      (fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
        σb * p.2 + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j, p.1 j * H j α)
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1)) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
          ∑ j : Fin n, H j α * H j β) := by
  have hPos : (show Matrix (Fin m) (Fin m) ℝ from fun α β : Fin m => σb ^ 2 +
      (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n, H j α * H j β).PosSemidef :=
    empirical_layer_covariance_posSemidef_multivariate σw σb n m H
  apply Measure.ext_of_charFun
  ext t
  set F := fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
    σb * p.2 + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j, p.1 j * H j α
  have hF_meas : Measurable F := measurable_conditional_preactivation σw σb n m H
  rw [charFun_apply, integral_map hF_meas.aemeasurable (by fun_prop)]
  have h_inner (p : (Fin n → ℝ) × ℝ) : ⟪F p, t⟫ = ⟪t, F p⟫ := real_inner_comm _ _
  simp_rw [h_inner]
  have h_proj (p : (Fin n → ℝ) × ℝ) :
      ⟪t, F p⟫ = (σb * ∑ α : Fin m, t.ofLp α) * p.2 +
        ∑ j : Fin n, p.1 j * ((σw * (n : ℝ)⁻¹.sqrt) * ∑ α : Fin m, t.ofLp α * H j α) :=
    projection_layer_eq_multivariate σw σb n m H p.1 p.2 t
  simp_rw [h_proj]
  -- The weights and bias are independent, so split the characteristic integrand.
  have h_split (p : (Fin n → ℝ) × ℝ) :
      Complex.exp ((((σb * ∑ α : Fin m, t.ofLp α) * p.2 +
        ∑ j : Fin n, p.1 j * ((σw * (n : ℝ)⁻¹.sqrt) * ∑ α : Fin m, t.ofLp α * H j
            α)) : ℝ) * Complex.I) =
      Complex.exp ((∑ j : Fin n, p.1 j * ((σw * (n : ℝ)⁻¹.sqrt) *
        ∑ α : Fin m, t.ofLp α * H j α) : ℝ) * Complex.I) *
      Complex.exp (((σb * ∑ α : Fin m, t.ofLp α) * p.2 : ℝ) * Complex.I) := by
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [h_split]
  set cw := fun j : Fin n => (σw * (n : ℝ)⁻¹.sqrt) * ∑ α : Fin m, t.ofLp α * H j α
  set cb := σb * ∑ α : Fin m, t.ofLp α
  have h_prod : (∫ p : (Fin n → ℝ) × ℝ,
      Complex.exp ((∑ j : Fin n, p.1 j * cw j : ℝ) * Complex.I) *
        Complex.exp ((cb * p.2 : ℝ) * Complex.I)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1)) =
    (∫ w : Fin n → ℝ, Complex.exp ((∑ j : Fin n, w j * cw j : ℝ) * Complex.I)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) *
      (∫ b : ℝ, Complex.exp ((cb * b : ℝ) * Complex.I) ∂gaussianReal 0 1) :=
    integral_prod_mul (fun w : Fin n → ℝ => Complex.exp ((∑ j : Fin n, w j * cw j : ℝ) * Complex.I))
      (fun b : ℝ => Complex.exp ((cb * b : ℝ) * Complex.I))
  rw [h_prod]
  -- Evaluate the independent Gaussian weight and bias factors.
  rw [integral_exp_sum_mul_I_gaussianReadout, integral_exp_mul_I_standardGaussian,
    ← Complex.exp_add]
  -- The two scalar variances combine into the covariance quadratic form.
  have h_var := projection_layer_variance_eq_multivariate σw σb n m H t
  have h_alg : - Complex.ofReal (∑ j : Fin n, (cw j) ^ 2) / 2 + - Complex.ofReal (cb ^ 2) / 2 =
      - Complex.ofReal (cb ^ 2 + ∑ j : Fin n, (cw j) ^ 2) / 2 := by
    push_cast
    ring
  rw [h_alg, h_var]
  rw [charFun_multivariateGaussian hPos]
  simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub, neg_div]

/-- Characteristic function of the conditional preactivation: integrating out the readout weights
and bias gives `exp (-(t ⬝ᵥ Σ⁽ⁿ⁾ *ᵥ t) / 2)`. -/
lemma charFun_conditional_preactivation_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    charFun
      (Measure.map (fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
        σb * p.2 + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j, p.1 j * H j α)
        ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1))) t =
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
        (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
          ∑ j : Fin n, H j α * H j β) *ᵥ t.ofLp) / 2) := by
  rw [exact_conditional_normality_general_multivariate]
  rw [charFun_multivariateGaussian
    (empirical_layer_covariance_posSemidef_multivariate σw σb n m H)]
  simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub, neg_div]

/-- The limiting recurrence matrix `σb² + σw² 𝔼[φ(zα) φ(zβ)]`, `z ~ 𝒩(0, K)`, is Hermitian. -/
lemma limitingRecurrence_isHermitian_multivariate (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ)
    (K : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.IsHermitian (show Matrix (Fin m) (Fin m) ℝ from fun α β => σb ^ 2 + σw ^ 2 *
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) := by
  ext α β
  rw [conjTranspose_apply]
  simp only [star_trivial]
  congr 2
  congr 1 with z
  ring

/-- The limiting recurrence matrix defines a nonnegative quadratic form (for `L²` activations). -/
lemma limitingRecurrence_nonneg_multivariate (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ)
    (hφ_meas : Measurable φ) (K : Matrix (Fin m) (Fin m) ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) (c : Fin m → ℝ) :
    0 ≤ c ⬝ᵥ (fun α β => σb ^ 2 + σw ^ 2 *
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0
          K)) *ᵥ c := by
  have hslln := empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate σw σb m φ hφ_meas K
      hφ_L2
  rcases hslln.exists with ⟨Z, hZ⟩
  have h_quad : Filter.Tendsto
      (fun n : ℕ => c ⬝ᵥ (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
        ∑ j : Fin n, φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ c)
      Filter.atTop
      (nhds (c ⬝ᵥ (fun α β => σb ^ 2 + σw ^ 2 *
        ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0
            K)) *ᵥ c)) :=
    (continuous_matrix_quadratic c).continuousAt.tendsto.comp hZ
  refine ge_of_tendsto h_quad (Filter.Eventually.of_forall fun n => ?_)
  exact empirical_layer_covariance_nonneg_multivariate σw σb n m
    (fun j α => φ ((Z j).ofLp α)) (WithLp.toLp 2 c)

/-- The limiting recurrence matrix `σb² + σw² 𝔼[φ(zα) φ(zβ)]`, `z ~ 𝒩(0, K)`, is positive
semidefinite. -/
lemma limitingRecurrence_posSemidef_multivariate (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ)
    (hφ_meas : Measurable φ) (K : Matrix (Fin m) (Fin m) ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β => σb ^ 2 + σw ^ 2 *
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0
          K)).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (limitingRecurrence_isHermitian_multivariate σw σb m φ K)
    fun x => by simpa using limitingRecurrence_nonneg_multivariate σw σb m φ hφ_meas K hφ_L2 x

-- Measurability of the characteristic integrand for the per-layer empirical recurrence.
private lemma measurable_exp_quadratic_layerRecurrence_multivariate
    (σw σb : ℝ) (n m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (t : EuclideanSpace ℝ (Fin m)) :
    Measurable (fun Z : ℕ → EuclideanSpace ℝ (Fin m) =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
        (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
          φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)) := by
  have h_quad : Measurable (fun Z : ℕ → EuclideanSpace ℝ (Fin m) =>
      t.ofLp ⬝ᵥ (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
        φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) := by
    simp only [dotProduct, mulVec]
    refine Finset.measurable_sum _ fun α _ => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun β _ => ?_)
    refine (measurable_const.add (measurable_const.mul (Finset.measurable_sum _
        fun j _ => ?_))).mul_const _
    refine (hφ_meas.comp ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable.comp
      (measurable_pi_apply j.val))).mul ?_
    exact hφ_meas.comp ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable.comp
      (measurable_pi_apply j.val))
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp h_quad).neg.div_const 2)

/-- Dominated convergence for the conditional characteristic functions: `∫ exp (-(t ⬝ᵥ Σ⁽ⁿ⁾(Z) *ᵥ t)
/ 2)` over i.i.d. `𝒩(0, K)` draws converges to `exp (-(t ⬝ᵥ Σ *ᵥ t) / 2)`, where `Σ` is the
limiting recurrence matrix. -/
lemma tendsto_charFun_preactivation_dct_multivariate
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ => ∫ Z : ℕ → EuclideanSpace ℝ (Fin m),
        Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
          (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
            φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)
        ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K))
      Filter.atTop
      (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
        (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) *ᵥ t.ofLp) / 2))) := by
  have hslln := empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate σw σb m φ hφ_meas K
      hφ_L2
  have h_cont : Continuous (fun M : Matrix (Fin m) (Fin m) ℝ =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ M *ᵥ t.ofLp) / 2)) :=
    continuous_charFun_integrand t
  have h_ae : ∀ᵐ Z : ℕ → EuclideanSpace ℝ (Fin m) ∂(Measure.infinitePi
      fun _ : ℕ => multivariateGaussian 0 K),
      Filter.Tendsto
        (fun n : ℕ => Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
          (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
            φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2))
        Filter.atTop
        (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
          (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
            φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) *ᵥ t.ofLp) / 2))) := by
    filter_upwards [hslln] with Z hZ
    exact (h_cont.tendsto _).comp hZ
  have h_bound : ∀ n : ℕ, ∀ᵐ Z : ℕ → EuclideanSpace ℝ (Fin m)
      ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K),
      ‖Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
        (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
          φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)‖ ≤ (1 : ℝ) := by
    intro n
    refine ae_of_all _ fun Z => norm_exp_neg_ofReal_div_two_le_one ?_
    exact empirical_layer_covariance_nonneg_multivariate σw σb n m
      (fun j α => φ ((Z j).ofLp α)) t
  have h_meas (n : ℕ) : Measurable (fun Z : ℕ → EuclideanSpace ℝ (Fin m) =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
        (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
          φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)) :=
    measurable_exp_quadratic_layerRecurrence_multivariate σw σb n m φ hφ_meas t
  have h_lim := tendsto_integral_of_dominated_convergence (bound := fun _ => (1 : ℝ))
    (fun n => (h_meas n).aestronglyMeasurable) (integrable_const 1) h_bound h_ae
  simpa only [integral_const, probReal_univ, one_smul] using h_lim

-- Measurability of the sequential (input-and-readout) preactivation map.
/-- The sequential preactivation `(Z, (w, b)) ↦ σb b + σw n^{-1/2} ∑ⱼ wⱼ φ(Zⱼ)` is measurable. -/
lemma measurable_sequential_preactivation (σw σb : ℝ) (n m : ℕ) (φ : ℝ → ℝ)
    (hφ_meas : Measurable φ) :
    Measurable (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
      WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
        ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
  refine measurable_pi_iff.2 fun α => ?_
  refine (measurable_const.mul (measurable_snd.comp measurable_snd)).add ?_
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  refine ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)).mul ?_
  exact hφ_meas.comp ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable.comp
    ((measurable_pi_apply j.val).comp measurable_fst))

/-- The characteristic function of the sequential preactivation equals the expectation of `exp (-(t
⬝ᵥ Σ⁽ⁿ⁾(Z) *ᵥ t) / 2)` over the previous layer `Z ~ 𝒩(0, K)^{⊗ℕ}`. -/
lemma charFun_map_sequential_preactivation_multivariate
    (σw σb : ℝ) (n m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun (Measure.map
      (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
          ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
      ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1)))) t =
      ∫ Z : ℕ → EuclideanSpace ℝ (Fin m),
        Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
          (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
            φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)
        ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K) := by
  set F := fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
    WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
      ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α)
  set μZ := Measure.infinitePi fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K
  set μP := (Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1)
  have hF_meas : Measurable F := measurable_sequential_preactivation σw σb n m φ hφ_meas
  rw [charFun_apply, integral_map hF_meas.aemeasurable (by fun_prop)]
  have h_inner (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) :
      ⟪F p, t⟫ = ⟪t, F p⟫ := real_inner_comm _ _
  simp_rw [h_inner]
  have h_exp_meas : AEStronglyMeasurable
      (fun p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ) =>
        Complex.exp (⟪t, F p⟫ * Complex.I)) (μZ.prod μP) := by
    have h_inner_meas : Measurable (fun p => ⟪t, F p⟫) :=
      (continuous_const.inner continuous_id).measurable.comp hF_meas
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp h_inner_meas).mul_const Complex.I)).aestronglyMeasurable
  have h_prod := integral_prod (fun p => Complex.exp (⟪t, F p⟫ * Complex.I))
    (Integrable.of_bound h_exp_meas 1 (ae_of_all _ fun p => (Complex.norm_exp_ofReal_mul_I _).le))
  rw [h_prod]
  congr 1 with Z
  set FZ := fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
    σb * p.2 + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j : Fin n, p.1 j * φ ((Z j.val).ofLp α)
  have h_FZ_eq (p : (Fin n → ℝ) × ℝ) : F (Z, p) = FZ p := by rfl
  simp_rw [h_FZ_eq]
  have h_FZ_meas : Measurable FZ :=
    measurable_conditional_preactivation σw σb n m (fun j α => φ ((Z j.val).ofLp α))
  have h_cf : (∫ p : (Fin n → ℝ) × ℝ, Complex.exp (⟪t, FZ p⟫ * Complex.I) ∂μP) =
      charFun (Measure.map FZ μP) t := by
    rw [charFun_apply, integral_map h_FZ_meas.aemeasurable (by fun_prop)]
    congr 1 with p
    rw [real_inner_comm]
  rw [h_cf]
  exact charFun_conditional_preactivation_multivariate σw σb n m
    (fun j α => φ ((Z j.val).ofLp α)) t

/-- The characteristic functions of the sequential preactivations converge pointwise to that of
`𝒩(0, σb² + σw² 𝔼[φ φ])` (strong law plus dominated convergence). -/
lemma tendsto_charFun_sequential_preactivation_multivariate
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ => charFun (Measure.map
        (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
          WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
            ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
        ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
          ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1)))) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) t)) := by
  have hPos : (show Matrix (Fin m) (Fin m) ℝ from fun α β => σb ^ 2 + σw ^ 2 *
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0
          K)).PosSemidef :=
    limitingRecurrence_posSemidef_multivariate σw σb m φ hφ_meas K hφ_L2
  have h_cf : charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
      (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
        φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) t =
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
        (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) *ᵥ t.ofLp) / 2) := by
    rw [charFun_multivariateGaussian hPos]
    simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub, neg_div]
  rw [h_cf]
  have h_eq (n : ℕ) : charFun (Measure.map
      (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
          ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
      ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1)))) t =
      ∫ Z : ℕ → EuclideanSpace ℝ (Fin m),
        Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
          (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
            φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)
        ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K) :=
    charFun_map_sequential_preactivation_multivariate σw σb n m φ hφ_meas K t
  simp_rw [h_eq]
  exact tendsto_charFun_preactivation_dct_multivariate σw σb m φ hφ_meas K hφ_L2 t


-- The covariance is written as a plain lambda `fun α β => …`, so its type is `Fin m → Fin m → ℝ`
-- rather than `Matrix (Fin m) (Fin m) ℝ`; finding `IsProbabilityMeasure (multivariateGaussian …)`
-- then needs `Matrix` to be unfolded.
set_option backward.isDefEq.respectTransparency.types false in
/-- **Sequential Multilayer NNGP Limit.** For a measurable activation `φ` with `φ(zα) ∈ L²(𝒩(0,
K))`, the next-layer preactivation vector built from i.i.d. `𝒩(0, K)` previous-layer draws
converges in distribution to the centered Gaussian with covariance `σb² + σw² 𝔼[φ(zα) φ(zβ)]`. -/
theorem tendstoInDistribution_sequential_preactivation
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) :
    TendstoInDistribution
      (fun n (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
          ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
      Filter.atTop id
      (fun n => (Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) where
  forall_aemeasurable n :=
    (measurable_sequential_preactivation σw σb n m φ hφ_meas).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    have h_meas (n : ℕ) : AEMeasurable
        (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
          WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
            ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
        ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
          ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1))) :=
      (measurable_sequential_preactivation σw σb n m φ hφ_meas).aemeasurable
    have h_weak : Filter.Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
        (fun n : ℕ => ⟨Measure.map
          (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
            WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
              ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
          ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
            ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1))),
          (Measure.isProbabilityMeasure_map_iff (h_meas n)).mpr inferInstance⟩)
        Filter.atTop
        (nhds ⟨multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
            φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)), inferInstance⟩) := by
      apply ProbabilityMeasure.tendsto_of_tendsto_charFun
      intro t
      exact tendsto_charFun_sequential_preactivation_multivariate σw σb m φ hφ_meas K hφ_L2 t
    convert! h_weak
    exact Subtype.ext Measure.map_id

end MultilayerSequentialNNGP

end NTK

end
