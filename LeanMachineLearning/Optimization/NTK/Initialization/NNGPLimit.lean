/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.ConditionalNormality

/-!
# Theorems 2 and 3: kernel convergence and the NNGP limit

Strong-law convergence of the empirical covariance (Theorem 2) and convergence in distribution
of the output to the NNGP at initialization (Theorem 3).

## Main results and proof outline

* Limiting NNGP covariance matrix $\boldsymbol{\Phi} \in \mathbb{R}^{m \times m}$:
  $\Phi^{\alpha \beta} :=
    \int \varphi(\mathbf{w}^\top \mathbf{x}^\alpha) \varphi(\mathbf{w}^\top \mathbf{x}^\beta)
    d\mathcal{N}(\mathbf{0}, \mathbf{I}_{n_0})$
  (`limitingCovariance φ X`).
* As width $n \to \infty$, the empirical covariance matrix converges almost surely to the
  deterministic NNGP Gram matrix:
  $$\Phi^{(n), \alpha \beta} \xrightarrow{\text{a.s.}}
    \int \varphi(\mathbf{w}^\top \mathbf{x}^\alpha) \varphi(\mathbf{w}^\top \mathbf{x}^\beta)
    d\mathcal{N}(\mathbf{0}, \mathbf{I}_{n_0})$$
  formalized entrywise by `NTK.empiricalCovariance_tendsto_integral`.
* Full matrix convergence in $\mathbb{R}^{m \times m}$ almost surely:
  $\boldsymbol{\Phi}^{(n)} \xrightarrow{\text{a.s.}} \boldsymbol{\Phi}$
  formalized by `NTK.empiricalCovariance_tendsto_matrix_integral`.
* The limiting Gram matrix $\boldsymbol{\Phi}$ is symmetric positive semidefinite:
  `NTK.limitingCovariance_posSemidef` via `NTK.sum_sum_mul_limitingCovariance_eq_integral_sq`
  and `NTK.sum_sum_mul_limitingCovariance_nonneg`.
* Step 1: For fixed inputs $\mathbf{x}^\alpha, \mathbf{x}^\beta$,
  define the scalar random variables
  $$Y_i := \varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)
    \varphi(\mathbf{w}_i^\top \mathbf{x}^\beta)$$
  for $i \in \{1, \dots, n\}$ (`NTK.measurable_cov_summand`).
* Step 3: Under square-integrability of $\varphi$, the expectation exists and is finite by
  Cauchy-Schwarz:
  $$\mathbb{E}_{\mathbf{w}_i}\left[ |Y_i| \right] \le
    \sqrt{\mathbb{E}_{\mathbf{w}_i}[\varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)^2]
    \mathbb{E}_{\mathbf{w}_i}[\varphi(\mathbf{w}_i^\top \mathbf{x}^\beta)^2]} < \infty$$
  (`NTK.integrable_cov_summand_of_memLp`).
* As width $n \to \infty$, the output vector $\mathbf{f}_m$ converges in distribution under the
  joint initialization measure `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)` to the centered multivariate Gaussian
  distribution with covariance $\boldsymbol{\Phi}$:
  $$\mathbf{f}_m \xrightarrow{d} \mathcal{N}\left(\mathbf{0}, \boldsymbol{\Phi}\right)
    \quad \text{in } \mathbb{R}^m$$
  formalized by `NTK.tendstoInDistribution_evalVector`.
* The unconditional pushforward measures
  $\mu_{\mathbf{f}_m}^{(n)} = \text{outputMeasure } n\ d\ \varphi\ X$
  converge weakly (narrowly) to the multivariate Gaussian measure:
  $$\mu_{\mathbf{f}_m}^{(n)} \rightharpoonup
    \mathcal{N}\left(\mathbf{0}, \boldsymbol{\Phi}\right)$$
  formalized by `NTK.outputMeasure_tendsto_multivariateGaussian`.
* Step 1: Conditioning on input weights $\mathbf{W}$ and integrating out readout weights $a$
  yields the unconditional characteristic function via iterated expectation:
  $$\psi_n(\mathbf{t}) =
    \mathbb{E}_{\mathbf{W}, a}\left[\exp(i \langle \mathbf{t}, \mathbf{f}_m \rangle)\right] =$$
  $$\mathbb{E}_{\mathbf{W}}\left[\exp\left(-\frac{1}{2}
    \mathbf{t}^\top \boldsymbol{\Phi}^{(n)} \mathbf{t}\right)\right]$$
  (`NTK.charFun_outputMeasure`).
* Step 2: By Theorem 2 (almost sure matrix convergence), the quadratic form converges
  almost surely:
  $\mathbf{t}^\top \boldsymbol{\Phi}^{(n)} \mathbf{t} \xrightarrow{\text{a.s.}}
    \mathbf{t}^\top \boldsymbol{\Phi} \mathbf{t}$,
  hence the characteristic integrand converges almost surely:
  $\exp(-\frac{1}{2} \mathbf{t}^\top \boldsymbol{\Phi}^{(n)} \mathbf{t}) \xrightarrow{\text{a.s.}}
    \exp(-\frac{1}{2} \mathbf{t}^\top \boldsymbol{\Phi} \mathbf{t})$
  (`NTK.charFun_integrand_tendsto_ae`).
* Step 3: By positive semidefiniteness of $\boldsymbol{\Phi}^{(n)}$, the exponent is nonpositive,
  so the integrand is uniformly bounded by $1$ (`NTK.norm_exp_neg_ofReal_div_two_le_one`).
* Step 4: Applying Lebesgue's Dominated Convergence Theorem passes the limit under expectation:
  $$\lim_{n \to \infty} \psi_n(\mathbf{t}) =
    \exp\left(-\frac{1}{2} \mathbf{t}^\top \boldsymbol{\Phi} \mathbf{t}\right)$$
  which matches the characteristic function of $\mathcal{N}(\mathbf{0}, \boldsymbol{\Phi})$
  (`NTK.tendsto_charFun_outputMeasure_eq_multivariateGaussian`).
* Step 5: By Lévy's Continuity Theorem in Euclidean space
  (`ProbabilityMeasure.tendsto_of_tendsto_charFun`), pointwise convergence of characteristic
  functions implies weak convergence of measures
  (`NTK.outputMeasure_tendsto_multivariateGaussian`) and convergence in distribution
  (`NTK.tendstoInDistribution_evalVector`).
* For every fixed projection vector $\mathbf{u} \in \mathbb{R}^m$, the scalar linear combination
  converges in distribution to a zero-mean univariate normal random variable:
  $$S_n(\mathbf{u}) = \sum_{\alpha=1}^m u_\alpha f(\mathbf{x}^\alpha; \boldsymbol{\theta})
    \xrightarrow{d} \mathcal{N}\left( 0, \mathbf{u}^\top \boldsymbol{\Phi} \mathbf{u} \right)$$
  formalized by `NTK.map_projection_tendsto_gaussianReal` and
  `NTK.tendstoInDistribution_projection`.
* Step 3: Almost sure convergence of conditional variance:
  $\mathbf{u}^\top \boldsymbol{\Phi}^{(n)} \mathbf{u} \xrightarrow{\text{a.s.}}
    \mathbf{u}^\top \boldsymbol{\Phi} \mathbf{u}$
  (`NTK.conditionalVariance_tendsto_limitingVariance_ae`).
* Step 4: Unconditional characteristic function:
  $\psi_n(t) =
    \mathbb{E}_{\mathbf{W}}[\exp(-\frac{t^2}{2}
      \mathbf{u}^\top \boldsymbol{\Phi}^{(n)} \mathbf{u})]$
  (`NTK.charFun_map_projection`).
* Step 5: Passing the limit via Dominated Convergence Theorem:
  $\lim_{n \to \infty} \psi_n(t) =
    \exp(-\frac{t^2}{2} \mathbf{u}^\top \boldsymbol{\Phi} \mathbf{u})$
  (`NTK.tendsto_charFun_map_projection`, `NTK.tendsto_charFun_map_projection_eq_gaussianReal`).
* `NTK.limitingCovariance` : deterministic limiting covariance matrix
  $\boldsymbol{\Phi} \in \mathbb{R}^{m \times m}$.
* `NTK.empiricalCovariance_tendsto_integral` : Theorem 2 entrywise almost sure convergence
  $\Phi^{(n), \alpha \beta} \xrightarrow{\text{a.s.}} \Phi^{\alpha \beta}$.
* `NTK.empiricalCovariance_tendsto_matrix_integral` : Theorem 2 full matrix almost sure
  convergence $\boldsymbol{\Phi}^{(n)} \xrightarrow{\text{a.s.}} \boldsymbol{\Phi}$.
* `NTK.sum_sum_mul_limitingCovariance_eq_integral_sq` : expectation-of-square identity for the
  limiting quadratic form.
* `NTK.sum_sum_mul_limitingCovariance_nonneg` : nonnegativity of the limiting kernel
  quadratic form.
* `NTK.limitingCovariance_posSemidef` : positive semidefiniteness of the limiting covariance
  matrix $\boldsymbol{\Phi}$.
* `NTK.outputMeasure`, `NTK.outputMeasure_eq_map` : unconditional output law and its
  pushforward API.
* `NTK.charFun_outputMeasure` : total-expectation formula for the unconditional characteristic
  function.
* `NTK.outputMeasure_tendsto_multivariateGaussian` : Theorem 3 multivariate weak convergence of
  output laws
  $\mu_{\mathbf{f}_m}^{(n)} \rightharpoonup \mathcal{N}(\mathbf{0}, \boldsymbol{\Phi})$.
* `NTK.tendstoInDistribution_evalVector` : Theorem 2.3 / Theorem 3 convergence in distribution
  $\mathbf{f}_m \xrightarrow{d} \mathcal{N}(\mathbf{0}, \boldsymbol{\Phi})$.
* `NTK.conditionalVariance_tendsto_limitingVariance_ae` : Step 3 almost sure convergence of
  conditional variance
  $\mathbf{u}^\top \boldsymbol{\Phi}^{(n)} \mathbf{u} \xrightarrow{\text{a.s.}}
    \mathbf{u}^\top \boldsymbol{\Phi} \mathbf{u}$.
* `NTK.charFun_map_projection` : Step 4 unconditional characteristic function of 1D projections.
* `NTK.tendsto_charFun_map_projection` : Step 5 DCT limit of projection characteristic function.
* `NTK.map_projection_tendsto_gaussianReal` : Step 6 weak convergence of linear combinations.
* `NTK.tendstoInDistribution_projection` : Theorem (Gaussianity of Linear Combinations
  $S_n(\mathbf{u}) \xrightarrow{d} \mathcal{N}(0, \mathbf{u}^\top \boldsymbol{\Phi} \mathbf{u})$).

See
`LeanMachineLearning.Optimization.NTK.Initialization`
for the overview of the whole development.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section Theorem2

/-! ## Theorem 2: Asymptotic Kernel Convergence and the NNGP Limit -/

/-! ### Step 1: Summand Measurability -/

/-- Step 1 (Measurability): For measurable `φ`, the product `w ↦ φ(w ⬝ᵥ x) * φ(w ⬝ᵥ x')` is
measurable. -/
lemma measurable_cov_summand (φ : ℝ → ℝ) (hφ : Measurable φ) (x x' : Fin d → ℝ) :
    Measurable (fun w : Fin d → ℝ => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) :=
  (hφ.comp (measurable_dotProduct_left x)).mul (hφ.comp (measurable_dotProduct_left x'))

/-! ### Step 3: Integrability via Cauchy-Schwarz -/

/-- Step 3 (Integrability via Cauchy-Schwarz): If `φ(· ⬝ᵥ x)` and `φ(· ⬝ᵥ x')` are square-integrable
under the Gaussian row measure, their product is integrable. -/
lemma integrable_cov_summand_of_memLp
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hx : MemLp (fun w => φ (w ⬝ᵥ x)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (hx' : MemLp (fun w => φ (w ⬝ᵥ x')) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
  hx.integrable_mul hx'

/-! ### Step 2 & Step 4: SLLN Convergence (Entrywise and Full Matrix) -/

/-- **Theorem 2 (Entrywise SLLN for the Covariance Tensor)**:
As width `n → ∞`, each entry of the empirical covariance matrix converges almost surely to the
deterministic limiting NNGP expectation:
  `Φ^{(n), α β} →_as 𝔼_{w ~ 𝒩(0, I_d)}[φ(w ⬝ᵥ X α) φ(w ⬝ᵥ X β)]`.

**Proof (4 Steps)**:
* Step 1: For fixed inputs `X α, X β`, define the summands
`Y_i(rows) := φ(rows i ⬝ᵥ X α) φ(rows i ⬝ᵥ X β)`.
* Step 2: Because `rows` are i.i.d. under the infinite product measure `μ`, `{Y_i}` is i.i.d.
* Step 3: By square-integrability of `φ` and Cauchy-Schwarz (`MemLp.integrable_mul`), `Y_0` is
integrable.
* Step 4: By Kolmogorov/Etemadi's SLLN (`strong_law_ae`), `(1/n) ∑_{i=1}^n Y_i →_as 𝔼[Y_0]`. -/
theorem empiricalCovariance_tendsto_integral
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (α β : Fin m) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => (Measure.pi fun _ : Fin d => gaussianReal
        0 1)),
      Filter.Tendsto
        (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X α β)
      Filter.atTop
      (nhds (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(Measure.pi fun _ : Fin d =>
          gaussianReal 0 1))) := by
  set g := fun w : Fin d → ℝ => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)
  have hg_meas : Measurable g := measurable_cov_summand φ hφ_meas (X α) (X β)
  have hg_int : Integrable g (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
    integrable_cov_summand_of_memLp φ (X α) (X β) (hφ_L2 α) (hφ_L2 β)
  simpa only [empiricalCovariance, g] using
    gaussianRow_average_tendsto_integral g hg_meas hg_int


/-- **Theorem 2 (Full Matrix Strong Law of Large Numbers for the Covariance Tensor)**:
As width `n → ∞`, the empirical covariance matrix converges almost surely to the deterministic
limiting NNGP Gram matrix in `Matrix (Fin m) (Fin m) ℝ`:
  `Φ^{(n)} →_as (fun α β => 𝔼_{w ~ 𝒩(0, I_d)}[φ(w ⬝ᵥ X α) φ(w ⬝ᵥ X β)])`. -/
theorem empiricalCovariance_tendsto_matrix_integral
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => (Measure.pi fun _ : Fin d => gaussianReal
        0 1)),
      Filter.Tendsto
        (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X)
        Filter.atTop
        (nhds ((fun α β => ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(Measure.pi fun _ : Fin d =>
            gaussianReal 0 1)) : Matrix (Fin m) (Fin m) ℝ)) := by
  exact ae_tendsto_matrix_of_forall_entry fun α β =>
    empiricalCovariance_tendsto_integral φ X hφ_meas hφ_L2 α β

end Theorem2

section Theorem3

/-! ## Theorem 3: Asymptotic Convergence in Distribution to NNGP -/

/-! ### Limiting NNGP Covariance Matrix and Output Distribution -/

/-- The limiting NNGP covariance matrix `Φ^{(∞)} ∈ ℝ^{m × m}`:
  `Φ^{(∞), α β} = ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(𝒩(0, I_d))`. -/
noncomputable def limitingCovariance
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun α β => ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)

/-- Equation lemma for `limitingCovariance`. -/
lemma limitingCovariance_apply
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (α β : Fin m) :
    limitingCovariance φ X α β =
      ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := rfl

/-- The limiting NNGP covariance matrix is symmetric (Hermitian). -/
lemma limitingCovariance_isHermitian
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    (limitingCovariance φ X).IsHermitian := by
  ext α β
  simp only [limitingCovariance_apply, conjTranspose_apply, star_trivial]
  congr 1 with w
  ring

/-- Full matrix almost sure convergence from Theorem 2 packaged with `limitingCovariance`. -/
lemma empiricalCovariance_tendsto_limitingCovariance
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => (Measure.pi fun _ : Fin d => gaussianReal
        0 1)),
      Filter.Tendsto
        (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X)
        Filter.atTop
        (nhds (limitingCovariance φ X)) :=
  empiricalCovariance_tendsto_matrix_integral φ X hφ_meas hφ_L2

/-- The quadratic form with a matrix `M ↦ c ⬝ᵥ M *ᵥ c` is continuous. -/
lemma continuous_matrix_quadratic (c : Fin m → ℝ) :
    Continuous (fun M : Matrix (Fin m) (Fin m) ℝ => c ⬝ᵥ M *ᵥ c) := by
  have h_eq : (fun M : Matrix (Fin m) (Fin m) ℝ => c ⬝ᵥ M *ᵥ c) =
      fun M => ∑ α : Fin m, ∑ β : Fin m, c α * M α β * c β := by
    funext M
    rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  rw [h_eq]
  have h_entry (α β : Fin m) : Continuous (fun M : Matrix (Fin m) (Fin m) ℝ => M α β) :=
    (continuous_apply β).comp (continuous_apply α)
  exact continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
    (continuous_const.mul (h_entry α β)).mul continuous_const

/-- **Theorem 2.3 Step 4 (Expectation-of-Square Identity for Limiting Kernel)**:
The quadratic form with the limiting covariance kernel equals the expectation of the
squared projected activation:
  `∑ α, ∑ β, u α * u β * Φ(X α, X β) = 𝔼_w [(∑ α, u α * φ(w ⬝ᵥ X α))²]`.
This directly verifies condition (i) of Definition 2.2, confirming `Φ` is positive semidefinite. -/
lemma sum_sum_mul_limitingCovariance_eq_integral_sq
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal
        0 1))
    (u : Fin m → ℝ) :
    (∑ α : Fin m, ∑ β : Fin m, u α * u β * limitingCovariance φ X α β) =
      ∫ w, (∑ α : Fin m, u α * φ (w ⬝ᵥ X α)) ^ 2 ∂(Measure.pi fun _ : Fin d =>
          gaussianReal 0 1) := by
  have hint (α β : Fin m) :
      Integrable (fun w => (u α * u β) * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β))) (Measure.pi fun _ : Fin d =>
          gaussianReal 0 1) :=
    (integrable_cov_summand_of_memLp φ (X α) (X β) (hφ_L2 α) (hφ_L2 β)).const_mul (u α * u β)
  simp_rw [limitingCovariance_apply]
  have h1 (α : Fin m) :
      (∑ β : Fin m, u α * u β * ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(Measure.pi fun _ : Fin d =>
          gaussianReal 0 1)) =
      ∫ w, ∑ β : Fin m, u α * u β * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) ∂(Measure.pi fun _ : Fin d =>
          gaussianReal 0 1) := by
    have h_in (β : Fin m) :
        u α * u β * ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(Measure.pi fun _ : Fin d =>
            gaussianReal 0 1) =
        ∫ w, (u α * u β) * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) ∂(Measure.pi fun _ : Fin d => gaussianReal
            0 1) :=
      (integral_const_mul (u α * u β) (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β))).symm
    simp_rw [h_in]
    exact (integral_finsetSum _ fun β _ => hint α β).symm
  simp_rw [h1]
  have hint_sum (α : Fin m) :
      Integrable (fun w => ∑ β : Fin m, u α * u β * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β))) (Measure.pi fun _
          : Fin d => gaussianReal 0 1) :=
    integrable_finsetSum _ fun β _ => hint α β
  rw [← integral_finsetSum _ fun α _ => hint_sum α]
  congr 1 with w
  simp only [pow_two]
  have h_alg : (∑ α : Fin m, ∑ β : Fin m, u α * u β * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β))) =
      (∑ α : Fin m, u α * φ (w ⬝ᵥ X α)) * (∑ β : Fin m, u β * φ (w ⬝ᵥ X β)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  exact h_alg

/-- The quadratic form with the limiting covariance kernel is nonnegative by the
expectation-of-square identity. -/
lemma sum_sum_mul_limitingCovariance_nonneg
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal
        0 1))
    (u : Fin m → ℝ) :
    0 ≤ ∑ α : Fin m, ∑ β : Fin m, u α * u β * limitingCovariance φ X α β := by
  rw [sum_sum_mul_limitingCovariance_eq_integral_sq φ X hφ_L2 u]
  exact integral_nonneg fun w => sq_nonneg _

/-- The quadratic form with the limiting NNGP covariance matrix `c ⬝ᵥ Φ^{(∞)} *ᵥ c` is nonnegative.
-/
lemma limitingCovariance_nonneg
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (c : Fin m → ℝ) :
    0 ≤ c ⬝ᵥ (limitingCovariance φ X) *ᵥ c := by
  have h_ae := empiricalCovariance_tendsto_limitingCovariance φ X hφ_meas hφ_L2
  obtain ⟨rows, hrows⟩ := h_ae.exists
  have h_tend : Filter.Tendsto
      (fun n : ℕ => c ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ c)
      Filter.atTop
      (nhds (c ⬝ᵥ (limitingCovariance φ X) *ᵥ c)) :=
    ((continuous_matrix_quadratic c).tendsto (limitingCovariance φ X)).comp hrows
  refine ge_of_tendsto h_tend ?_
  filter_upwards with n
  exact empiricalCovariance_nonneg n φ (fun i => rows i.val) X c

/-- The limiting NNGP covariance matrix `Φ^{(∞)}` is positive semidefinite (`PosSemidef`). -/
theorem limitingCovariance_posSemidef
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    (limitingCovariance φ X).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (limitingCovariance_isHermitian φ X)
    fun x => by simpa using limitingCovariance_nonneg φ X hφ_meas hφ_L2 x

lemma evalSingle_joint_measurable
    (φ : ℝ → ℝ) (hφ : Measurable φ) (x : Fin d → ℝ) :
    Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => evalSingle φ p.1 p.2 x) := by
  simp_rw [evalSingle_eq_normalized_sum]
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun i _ => ?_
  have h_ai : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have h_Wi : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => φ (p.1 i ⬝ᵥ x)) :=
    hφ.comp ((measurable_dotProduct_left x).comp ((measurable_pi_apply i).comp measurable_fst))
  exact h_ai.mul h_Wi

lemma evalVector_joint_measurable
    (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ) :
    Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => evalVector φ p.1 p.2 X) := by
  change Measurable ((WithLp.toLp 2) ∘
    (fun (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) α => evalSingle φ p.1 p.2 (X α)))
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.2 fun α => evalSingle_joint_measurable φ hφ (X α))

/-- Joint distribution of network outputs across evaluation points `X` at width `n`:
  `outputMeasure n d φ X = (𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)).map (fun (W, a) => evalVector φ W a X)`. -/
noncomputable def outputMeasure (n d : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.map (fun p => evalVector φ p.1 p.2 X) ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin
      d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))

/-- The output law as the pushforward of the joint initialization measure. This is the public
equation lemma for `outputMeasure`, so downstream proofs need not unfold its implementation. -/
lemma outputMeasure_eq_map
    (n d : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    outputMeasure n d φ X =
      Measure.map (fun p => evalVector φ p.1 p.2 X) ((Measure.pi fun _ : Fin n => Measure.pi fun _ :
          Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := rfl

/-- `outputMeasure n d φ X` is a probability measure when `φ` is measurable. -/
lemma isProbabilityMeasure_outputMeasure
    (n d : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ) :
    IsProbabilityMeasure (outputMeasure n d φ X) := by
  rw [outputMeasure_eq_map]
  exact (Measure.isProbabilityMeasure_map_iff (evalVector_joint_measurable φ hφ
      X).aemeasurable).mpr inferInstance

/-- Transport: The pushforward of the infinite Gaussian row product measure under restriction to the
first `n` hidden units is exactly the finite-width input weight measure `𝒩(0,1)^{n×d}`. -/
lemma map_infinitePi_rows_eq_gaussianInit (n d : ℕ) :
    Measure.map (fun (rows : ℕ → Fin d → ℝ) (i : Fin n) => rows i.val)
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0 1)) = (Measure.pi
          fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  exact (measurePreserving_prefixMap (Measure.pi fun _ : Fin d => gaussianReal 0 1) n).map_eq

/-! ### Step 1 & Step 2: Unconditional Characteristic Function -/

/-- Step 1 & 2 helper: Integrating out the readout weights under `𝒩(0, I_n)` gives the
conditional characteristic function `exp(- (1/2) t ⬝ᵥ Φ^{(n)} *ᵥ t)`. -/
lemma integral_exp_inner_evalVector
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    (∫ a, Complex.exp (⟪evalVector φ W a X, t⟫ * Complex.I) ∂(Measure.pi fun _ : Fin n =>
        gaussianReal 0 1)) =
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2) := by
  have h_meas : Measurable (fun a => evalVector φ W a X) := evalVector_measurable φ W X
  calc
    (∫ a, Complex.exp (⟪evalVector φ W a X, t⟫ * Complex.I)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) =
        charFun (Measure.map (fun a => evalVector φ W a X) (Measure.pi fun _ : Fin n => gaussianReal
            0 1)) t := by
      rw [charFun_apply, integral_map h_meas.aemeasurable (by fun_prop)]
    _ = Complex.exp
        (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2) :=
      charFun_readout_evalVector φ W X t

/-- **Step 2 (Law of Total Expectation for the Characteristic Function)**:
The unconditional characteristic function of the network output vector under `𝒩(0,1)^{n×d} ⊗ 𝒩(0,
I_n)` is the
expectation over input weights `W` of the conditional characteristic function:
  `charFun (outputMeasure n d φ X) t = 𝔼_W [exp(- (1/2) t ⬝ᵥ Φ^{(n)}(W) *ᵥ t)]`. -/
lemma charFun_outputMeasure
    (n : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun (outputMeasure n d φ X) t =
      ∫ W, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  have h_meas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => evalVector φ p.1 p.2 X) :=
    evalVector_joint_measurable φ hφ X
  calc
    charFun (outputMeasure n d φ X) t =
        ∫ p, Complex.exp (⟪evalVector φ p.1 p.2 X, t⟫ * Complex.I) ∂((Measure.pi fun _ : Fin n =>
            Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
                gaussianReal 0 1)) := by
      rw [outputMeasure_eq_map, charFun_apply,
        integral_map h_meas.aemeasurable (by fun_prop)]
    _ = ∫ W, (∫ a, Complex.exp (⟪evalVector φ W a X, t⟫ * Complex.I)
          ∂(Measure.pi fun _ : Fin n =>
              gaussianReal 0 1)) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
                  gaussianReal 0 1) := by
      change (∫ p, Complex.exp (⟪evalVector φ p.1 p.2 X, t⟫ * Complex.I)
          ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin n => gaussianReal 0 1))) = _
      have h_inner : Measurable
          (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
            ⟪evalVector φ p.1 p.2 X, t⟫) :=
        (continuous_id.inner continuous_const).measurable.comp h_meas
      have h_exp_meas : AEStronglyMeasurable
          (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
            Complex.exp (⟪evalVector φ p.1 p.2 X, t⟫ * Complex.I))
          ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
        (Complex.continuous_exp.measurable.comp
          ((Complex.measurable_ofReal.comp h_inner).mul_const Complex.I)).aestronglyMeasurable
      exact integral_prod _ (Integrable.of_bound h_exp_meas 1
        (ae_of_all _ fun p => (Complex.norm_exp_ofReal_mul_I _).le))
    _ = ∫ W, Complex.exp
        (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)
          ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
      congr 1 with W
      exact integral_exp_inner_evalVector φ W X t

/-- Measurability of the characteristic integrand on input weight matrices. -/
lemma measurable_exp_quadratic_empiricalCovariance
    (n : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Measurable (fun W : Fin n → Fin d → ℝ =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)) := by
  have h_quad : Measurable (fun W : Fin n → Fin d → ℝ =>
      t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) := by
    have h_eq : (fun W : Fin n → Fin d → ℝ => t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) =
        fun W => ∑ α : Fin m, ∑ β : Fin m, t.ofLp α * (empiricalCovariance n φ W X α
            β) * t.ofLp β := by
      funext W
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    rw [h_eq]
    refine Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun β _ => ?_
    have h_cov : Measurable (fun W : Fin n → Fin d → ℝ => empiricalCovariance n φ W X α β) := by
      simp only [empiricalCovariance]
      refine Measurable.const_mul ?_ _
      refine Finset.measurable_sum _ fun i _ => ?_
      have h_summand : Measurable (fun w : Fin d → ℝ => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) :=
        measurable_cov_summand φ hφ (X α) (X β)
      exact h_summand.comp (measurable_pi_apply i)
    exact (measurable_const.mul h_cov).mul measurable_const
  exact Complex.measurable_exp.comp
    (((Complex.measurable_ofReal.comp h_quad).neg).div_const 2)

/-- The characteristic integrand `M ↦ exp(- (1/2) t ⬝ᵥ M *ᵥ t)` is continuous. -/
lemma continuous_charFun_integrand (t : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun M : Matrix (Fin m) (Fin m) ℝ =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ M *ᵥ t.ofLp) / 2)) := by
  exact Complex.continuous_exp.comp
    (((Complex.continuous_ofReal.comp (continuous_matrix_quadratic t.ofLp)).neg).div_const 2)

/-- Expressing the expectation under `𝒩(0,1)^{n×d}` as an expectation under `infinitePi`. -/
lemma integral_charFun_gaussianInit_eq_infinitePi
    (n : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    (∫ W, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)
      ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1)) =
    ∫ rows, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ
        (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)
      ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0 1)) := by
  rw [← map_infinitePi_rows_eq_gaussianInit n d]
  have h_map : Measurable (fun (rows : ℕ → Fin d → ℝ) (i : Fin n) => rows i.val) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply i.val
  have h_f : Measurable (fun W : Fin n → Fin d → ℝ =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)) :=
    measurable_exp_quadratic_empiricalCovariance n φ hφ X t
  rw [integral_map h_map.aemeasurable h_f.aestronglyMeasurable]

/-! ### Step 3 & Step 4: Dominated Convergence of the Characteristic Function -/

/-- **Step 3 (Almost sure convergence of characteristic integrand)**:
By Theorem 2, `Φ^{(n)} →_as Φ^{(∞)}`. By continuity of `M ↦ exp(- (1/2) t ⬝ᵥ M *ᵥ t)`, the
characteristic integrand converges almost surely. -/
lemma charFun_integrand_tendsto_ae
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (t : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => (Measure.pi fun _ : Fin d => gaussianReal
        0 1)),
      Filter.Tendsto
        (fun n : ℕ => Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ
            (fun i => rows i.val) X) *ᵥ t.ofLp) / 2))
        Filter.atTop
        (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ t.ofLp) /
            2))) := by
  have h_mat := empiricalCovariance_tendsto_limitingCovariance φ X hφ_meas hφ_L2
  filter_upwards [h_mat] with rows hrows
  exact ((continuous_charFun_integrand t).tendsto (limitingCovariance φ X)).comp hrows

/-- Auxiliary: `‖exp(- s / 2)‖ ≤ 1` for nonnegative real `s`. -/
lemma norm_exp_neg_ofReal_div_two_le_one {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp (- Complex.ofReal s / 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, show (- Complex.ofReal s / 2).re = - s / 2 by simp, ← Real.exp_zero]
  exact Real.exp_le_exp_of_le (by linarith)

/-- Step 4 uniform bound: The characteristic integrand is bounded by `1` uniformly in `n` and `W`.
-/
lemma norm_charFun_readout_le_one
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    ‖Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)‖ ≤ 1 :=
  norm_exp_neg_ofReal_div_two_le_one (empiricalCovariance_nonneg n φ W X t.ofLp)

/-- Step 4 (DCT under infinite product): The infinite-product integral of the characteristic
integrand
converges to `exp(- (1/2) t ⬝ᵥ Φ^{(∞)} *ᵥ t)`. -/
lemma tendsto_integral_charFun_infinitePi
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ rows, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ
            (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)
          ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0 1)))
      Filter.atTop
      (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ t.ofLp) / 2))) :=
          by
  have h_ae := charFun_integrand_tendsto_ae φ X hφ_meas hφ_L2 t
  have h_bound : ∀ n : ℕ, ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun
      _ : Fin d => gaussianReal 0 1)),
      ‖Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ
          (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)‖ ≤ (1 : ℝ) :=
    fun n => ae_of_all _ fun rows => norm_charFun_readout_le_one n φ _ X t
  have h_meas (n : ℕ) : Measurable (fun rows : ℕ → Fin d → ℝ =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ
          (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)) := by
    have h_map : Measurable (fun (rows : ℕ → Fin d → ℝ) (i : Fin n) => rows i.val) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply i.val
    exact (measurable_exp_quadratic_empiricalCovariance n φ hφ_meas X t).comp h_map
  have h_lim := tendsto_integral_of_dominated_convergence (bound := fun _ => (1 : ℝ))
    (fun n => (h_meas n).aestronglyMeasurable)
    (integrable_const 1)
    h_bound
    h_ae
  simpa only [integral_const, probReal_univ, one_smul] using h_lim

/-- **Step 4 (Dominated Convergence Theorem for Characteristic Functions)**:
The unconditional characteristic function of the network output converges to the Gaussian
characteristic
function:
  `lim_{n → ∞} charFun (outputMeasure n d φ X) t = exp(- (1/2) t ⬝ᵥ Φ^{(∞)} *ᵥ t)`. -/
lemma tendsto_charFun_outputMeasure
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ => charFun (outputMeasure n d φ X) t)
      Filter.atTop
      (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ t.ofLp) / 2))) :=
          by
  have h_eq (n : ℕ) : charFun (outputMeasure n d φ X) t =
      ∫ rows, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ
          (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin d => gaussianReal 0 1)) := by
    rw [charFun_outputMeasure n φ hφ_meas X t,
      integral_charFun_gaussianInit_eq_infinitePi n φ hφ_meas X t]
  simp_rw [h_eq]
  exact tendsto_integral_charFun_infinitePi φ X hφ_meas hφ_L2 t

/-! ### Step 5: Lévy Continuity Theorem and Theorem 3 Statements -/

/-- Pointwise convergence of characteristic functions to the characteristic function of the
multivariate Gaussian `𝒩(0, Φ^{(∞)})`. -/
lemma tendsto_charFun_outputMeasure_eq_multivariateGaussian
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ => charFun (outputMeasure n d φ X) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (limitingCovariance φ X)) t)) := by
  have hPos : (limitingCovariance φ X).PosSemidef :=
    limitingCovariance_posSemidef φ X hφ_meas hφ_L2
  have h_cf : charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
      (limitingCovariance φ X)) t =
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ t.ofLp) / 2) := by
    rw [charFun_multivariateGaussian hPos]
    congr 1
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]
  rw [h_cf]
  exact tendsto_charFun_outputMeasure φ X hφ_meas hφ_L2 t



/-! ### Gaussianity of Linear Combinations (Scalar NNGP Limit) -/

/-- Homogeneity of matrix quadratic forms under scalar multiplication. -/
lemma dot_mulVec_smul (t : ℝ) (M : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) :
    (t • u) ⬝ᵥ M *ᵥ (t • u) = t ^ 2 * (u ⬝ᵥ M *ᵥ u) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- The scalar projection is measurable as a joint function of `(W, a)`. -/
lemma projection_joint_measurable
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (X : Fin m → Fin d → ℝ) (u : Fin m → ℝ) :
    Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) := by
  exact Finset.measurable_sum _ fun α _ =>
    measurable_const.mul (evalSingle_joint_measurable φ hφ_meas (X α))

/-- Expressing the inner product with `WithLp.toLp 2 (t • u)` as a scaled projection sum. -/
lemma inner_smul_evalVector (t : ℝ) (u : Fin m → ℝ)
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (X : Fin m → Fin d → ℝ) :
    ⟪evalVector φ W a X, WithLp.toLp 2 (t • u)⟫ =
      t * ∑ α : Fin m, u α * evalSingle φ W a (X α) := by
  rw [real_inner_comm, evalVector_inner]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- **Step 3 (Almost sure convergence of conditional variance)**:
By Theorem 2 and continuity of matrix quadratic forms, the conditional variance
converges almost surely:
  `u ⬝ᵥ Φ^{(n)} *ᵥ u →_as u ⬝ᵥ Φ^{(∞)} *ᵥ u`. -/
lemma conditionalVariance_tendsto_limitingVariance_ae
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (u : Fin m → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => (Measure.pi fun _ : Fin d => gaussianReal
        0 1)),
      Filter.Tendsto
        (fun n : ℕ => u ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ u)
        Filter.atTop
        (nhds (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u)) := by
  have h_mat := empiricalCovariance_tendsto_limitingCovariance φ X hφ_meas hφ_L2
  filter_upwards [h_mat] with rows hrows
  exact ((continuous_matrix_quadratic u).tendsto (limitingCovariance φ X)).comp hrows

/-- Characteristic function of the projection expressed as evaluation of
`charFun (outputMeasure n)`. -/
lemma charFun_map_projection_eq_outputMeasure
    (n : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (X : Fin m → Fin d → ℝ)
    (u : Fin m → ℝ) (t : ℝ) :
    charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) ((Measure.pi fun _ : Fin n => Measure.pi fun _
          : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) t =
      charFun (outputMeasure n d φ X) (WithLp.toLp 2 (t • u)) := by
  have h_proj_meas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) :=
    projection_joint_measurable φ hφ_meas X u
  rw [charFun_apply_real, integral_map h_proj_meas.aemeasurable (by fun_prop)]
  rw [charFun_apply, outputMeasure_eq_map,
    integral_map (evalVector_joint_measurable φ hφ_meas X).aemeasurable (by fun_prop)]
  congr 1 with p
  congr 1
  rw [inner_smul_evalVector]
  push_cast
  ring

/-- **Step 4 (Law of Total Expectation for Scalar Characteristic Function)**:
The unconditional characteristic function of the linear projection is obtained by
evaluating `charFun (outputMeasure n)` at the projection direction `WithLp.toLp 2 (t • u)`:
  `ψ_n(t) = 𝔼_W [exp(- (t²/2) u ⬝ᵥ Φ^{(n)} *ᵥ u)]`. -/
lemma charFun_map_projection
    (n : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (X : Fin m → Fin d → ℝ)
    (u : Fin m → ℝ) (t : ℝ) :
    charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) ((Measure.pi fun _ : Fin n => Measure.pi fun _
          : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) t =
      ∫ W, Complex.exp (- Complex.ofReal (t ^ 2 * (u ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ u)) / 2)
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  rw [charFun_map_projection_eq_outputMeasure n φ hφ_meas X u t,
    charFun_outputMeasure n φ hφ_meas X (WithLp.toLp 2 (t • u))]
  congr 1 with W
  congr 2
  rw [WithLp.ofLp_toLp, dot_mulVec_smul]

/-- **Step 5 (Passing the Limit via Dominated Convergence)**:
Specializing `tendsto_charFun_outputMeasure` at `WithLp.toLp 2 (t • u)` directly yields
the limit of the scalar characteristic function without repeating the DCT proof:
  `lim_{n → ∞} ψ_n(t) = exp(- (t²/2) u ⬝ᵥ Φ^{(∞)} *ᵥ u)`. -/
lemma tendsto_charFun_map_projection
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (u : Fin m → ℝ) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) ((Measure.pi fun _ : Fin n => Measure.pi fun
            _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) t)
      Filter.atTop
      (nhds (Complex.exp (- Complex.ofReal (t ^ 2 * (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u)) / 2))) :=
          by
  have h_eq (n : ℕ) :
      charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) ((Measure.pi fun _ : Fin n => Measure.pi fun
            _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) t =
      charFun (outputMeasure n d φ X) (WithLp.toLp 2 (t • u)) :=
    charFun_map_projection_eq_outputMeasure n φ hφ_meas X u t
  simp_rw [h_eq]
  have h_lim := tendsto_charFun_outputMeasure φ X hφ_meas hφ_L2 (WithLp.toLp 2 (t • u))
  have h_quad : (WithLp.toLp 2 (t • u)).ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ (WithLp.toLp 2
      (t • u)).ofLp =
      t ^ 2 * (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u) := by
    rw [WithLp.ofLp_toLp, dot_mulVec_smul]
  rwa [h_quad] at h_lim

/-- Pointwise convergence of scalar characteristic functions to the characteristic function
of the univariate Gaussian `𝒩(0, u ⬝ᵥ Φ^{(∞)} *ᵥ u)`. -/
lemma tendsto_charFun_map_projection_eq_gaussianReal
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (u : Fin m → ℝ) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) ((Measure.pi fun _ : Fin n => Measure.pi fun
            _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) t)
      Filter.atTop
      (nhds (charFun (gaussianReal 0 (Real.toNNReal (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u))) t)) := by
  have h_nonneg : 0 ≤ u ⬝ᵥ (limitingCovariance φ X) *ᵥ u :=
    limitingCovariance_nonneg φ X hφ_meas hφ_L2 u
  have h_cf : charFun (gaussianReal 0 (Real.toNNReal (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u))) t =
      Complex.exp (- Complex.ofReal (t ^ 2 * (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u)) / 2) := by
    rw [charFun_gaussianReal]
    simp only [mul_zero, zero_mul, ofReal_zero, zero_sub, neg_div]
    rw [Real.coe_toNNReal _ h_nonneg]
    congr 1
    push_cast
    ring
  rw [h_cf]
  exact tendsto_charFun_map_projection φ X hφ_meas hφ_L2 u t

/-- `Measure.map` of the projection is a probability measure when `φ` is measurable. -/
lemma isProbabilityMeasure_map_projection
    (n d : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (X : Fin m → Fin d → ℝ) (u : Fin m → ℝ) :
    IsProbabilityMeasure (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) ((Measure.pi fun _ : Fin n => Measure.pi fun _
          : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) :=
  (Measure.isProbabilityMeasure_map_iff (projection_joint_measurable φ hφ_meas X
      u).aemeasurable).mpr inferInstance



/-- **Theorem 3 (Weak Convergence of Output Measure to NNGP Limit)**:
As width `n → ∞`, the joint distribution of network outputs across evaluation points
converges weakly to the multivariate Gaussian distribution `𝒩(0, Φ^{(∞)})`:
  `outputMeasure n d φ X →_w 𝒩(0, Φ^{(∞)})`. -/
theorem outputMeasure_tendsto_multivariateGaussian
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    Filter.Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
      (fun n : ℕ => ⟨outputMeasure n d φ X,
        isProbabilityMeasure_outputMeasure n d φ hφ_meas X⟩)
      Filter.atTop
      (nhds ⟨multivariateGaussian 0 (limitingCovariance φ X), inferInstance⟩) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  exact tendsto_charFun_outputMeasure_eq_multivariateGaussian φ X hφ_meas hφ_L2 t

set_option backward.isDefEq.respectTransparency.types false in
/-- **Theorem 3 (Asymptotic Convergence in Distribution to NNGP)**:
As width `n → ∞`, the output vector `f_m(W, a)` under the parameter initialization
measure converges in distribution to the centered multivariate Gaussian `𝒩(0, Φ^{(∞)})`:
  `(f(x^1; θ), …, f(x^m; θ))ᵀ →_d 𝒩(0, Φ^{(∞)})`.

**Proof (5 Steps)**:
* Step 1: By `charFun_readout_evalVector`, the conditional characteristic function given input
weights
  `W` (the σ-algebra `ℱ`) is `exp(- (1/2) t ⬝ᵥ Φ^{(n)} *ᵥ t)`.
* Step 2: By Fubini (`charFun_outputMeasure`), the unconditional characteristic function is the
  expectation `𝔼_W [exp(- (1/2) t ⬝ᵥ Φ^{(n)} *ᵥ t)]`.
* Step 3: By Theorem 2 (`empiricalCovariance_tendsto_limitingCovariance`), `Φ^{(n)} →_as Φ^{(∞)}`,
  so the characteristic integrand converges almost surely (`charFun_integrand_tendsto_ae`).
* Step 4: Since `Φ^{(n)}` is positive semidefinite, `‖exp(- (1/2) t ⬝ᵥ Φ^{(n)} *ᵥ t)‖ ≤ 1`.
  By the Dominated Convergence Theorem (`tendsto_charFun_outputMeasure`),
  `charFun (outputMeasure n) t → exp(- (1/2) t ⬝ᵥ Φ^{(∞)} *ᵥ t)`.
* Step 5: By Lévy's Continuity Theorem (`ProbabilityMeasure.tendsto_of_tendsto_charFun`), pointwise
  characteristic function convergence implies weak convergence and convergence in distribution. -/
theorem tendstoInDistribution_evalVector
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) => evalVector φ p.1 p.2 X)
      Filter.atTop
      id
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (multivariateGaussian 0 (limitingCovariance φ X)) where
  forall_aemeasurable n := (evalVector_joint_measurable φ hφ_meas X).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    convert! outputMeasure_tendsto_multivariateGaussian φ X hφ_meas hφ_L2
    exact Subtype.ext Measure.map_id

/-- Convergence in distribution of the neural network output vector evaluated on the
paper's scaled dataset `(1 / √d) * X` to the limiting Gaussian distribution
`𝒩(0, Φ^{(∞)}(X / √d))`. -/
theorem tendstoInDistribution_evalVector_scaled_dataset
    {d m : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))
      Filter.atTop
      id
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) :=
  tendstoInDistribution_evalVector φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) hφ_meas hφ_L2

/-- Initial residual weak limit on the scaled dataset `(1 / √d) * X`:
subtracting the target vector `y` preserves convergence in distribution,
yielding `r_n(0) ⟹ G - y` where `G ~ 𝒩(0, Φ^{(∞)})`. -/
theorem tendstoInDistribution_initialResidual_evalVector
    {d m : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) - y)
      Filter.atTop
      (fun G => G - y)
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  have h := tendstoInDistribution_evalVector_scaled_dataset φ X hφ_meas hφ_L2
  exact TendstoInDistribution.sub_const _ _ y h

/-- Tightness of the sequence of output laws `outputMeasure n d φ X` as `n` varies:
follows from pointwise convergence of characteristic functions to the multivariate Gaussian
via Lévy continuity (`MeasureTheory.isTightMeasureSet_of_tendsto_charFun`). -/
theorem isTightMeasureSet_range_outputMeasure
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    IsTightMeasureSet (Set.range (outputMeasure · d φ X)) := by
  have : ∀ n, IsProbabilityMeasure (outputMeasure n d φ X) :=
    fun n => isProbabilityMeasure_outputMeasure n d φ hφ_meas X
  have hCont : ContinuousAt
      (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (limitingCovariance φ X))) 0 :=
    continuous_charFun.continuousAt
  exact isTightMeasureSet_of_tendsto_charFun hCont
    (fun t => tendsto_charFun_outputMeasure_eq_multivariateGaussian φ X hφ_meas hφ_L2 t)

/-- Tightness of the sequence of output laws on the scaled dataset `(1 / √d) * X`. -/
theorem isTightMeasureSet_range_outputMeasure_scaled_dataset
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    IsTightMeasureSet
      (Set.range (outputMeasure · d φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) :=
  isTightMeasureSet_range_outputMeasure φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
    hφ_meas hφ_L2

/-- **Theorem (Weak Convergence of Linear Combinations)**:
As width `n → ∞`, the pushforward law of the scalar linear combination converges weakly
to the centered univariate Gaussian `𝒩(0, u ⬝ᵥ Φ^{(∞)} *ᵥ u)`. -/
theorem map_projection_tendsto_gaussianReal
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (u : Fin m → ℝ) :
    Filter.Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ => ⟨Measure.map (fun p => ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α))
          ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)),
        isProbabilityMeasure_map_projection n d φ hφ_meas X u⟩)
      Filter.atTop
      (nhds ⟨gaussianReal 0 (Real.toNNReal (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u)), inferInstance⟩) :=
          by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  exact tendsto_charFun_map_projection_eq_gaussianReal φ X hφ_meas hφ_L2 u t

set_option backward.isDefEq.respectTransparency.types false in
/-- **Theorem (Gaussianity of Linear Combinations / Asymptotic Univariate NNGP)**:
As width `n → ∞`, the scalar linear combination `S_n(u) = ∑ α, u α * f(X α; θ)` under
parameter initialization converges in distribution to the centered univariate normal
distribution `𝒩(0, u ⬝ᵥ Φ^{(∞)} *ᵥ u)`:
  `∑ α, u α * f(X α; θ) →_d 𝒩(0, u ⬝ᵥ Φ^{(∞)} *ᵥ u)`.

**Proof (6 Steps)**:
* Step 1: `projection_eq_sum_projectionCoeff` reformulates the projection
  as `∑ i, a_i * projectionCoeff`.
* Step 2: `map_readout_projection_eq_gaussianReal` shows that conditional on input weights,
  the projection is distributed as `𝒩(0, u ⬝ᵥ Φ^{(n)} *ᵥ u)`.
* Step 3: `conditionalVariance_tendsto_limitingVariance_ae` proves
`u ⬝ᵥ Φ^{(n)} *ᵥ u →_as u ⬝ᵥ Φ^{(∞)} *ᵥ u`.
* Step 4: `charFun_map_projection` evaluates the unconditional characteristic function as
  `𝔼_W [exp(- (t²/2) u ⬝ᵥ Φ^{(n)} *ᵥ u)]`.
* Step 5: `tendsto_charFun_map_projection` uses Dominated Convergence to show that the
characteristic
  function converges to `exp(- (t²/2) u ⬝ᵥ Φ^{(∞)} *ᵥ u)`.
* Step 6: `tendstoInDistribution_projection` concludes convergence in distribution by Lévy's
  Continuity Theorem (`ProbabilityMeasure.tendsto_of_tendsto_charFun`). -/
theorem tendstoInDistribution_projection
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (u : Fin m → ℝ) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) => ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X
          α))
      Filter.atTop
      id
      (fun n => ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (gaussianReal 0 (Real.toNNReal (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u))) where
  forall_aemeasurable n := (projection_joint_measurable φ hφ_meas X u).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    convert! map_projection_tendsto_gaussianReal φ X hφ_meas hφ_L2 u
    exact Subtype.ext Measure.map_id

end Theorem3

end NTK

end
