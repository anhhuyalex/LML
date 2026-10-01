/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.Setup
public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianAlgebra
public import LeanMachineLearning.Optimization.NTK.Initialization.ConditionalNormality
public import LeanMachineLearning.Optimization.NTK.Initialization.NNGPLimit
public import LeanMachineLearning.Optimization.NTK.Initialization.MultilayerNNGP
public import LeanMachineLearning.Optimization.NTK.Initialization.CovariancePropagation
public import LeanMachineLearning.Optimization.NTK.Initialization.DeepRecursion
public import LeanMachineLearning.Optimization.NTK.Initialization.DeepNNGPTheorems
public import LeanMachineLearning.Optimization.NTK.Initialization.FullNTK

/-!
# NTK Initialization, Gaussian Processes, and Finite-Dimensional NNGP Limit

This file formalizes the parameter initialization probability space, mutual independence
structure, Definition 2.2 (Gaussian Processes), Theorem 1 / Step 1 (Exact Conditional Normality),
Theorem 2 / Step 2 (Strong Law of Large Numbers for the Covariance Tensor), Theorem 2.3 /
Theorem 3 (Finite-Dimensional NNGP Limit at Initialization), Multilayer Sequential NNGP
recurrence convergence, the Layer-by-Layer Conditional Gaussian Structure (independence across
depth and the depth-$d$ recursive kernel $\Phi_\ell$).  Proposition 2.5 (Cho-Saul / Arc-Cosine
Kernel for ReLU) is in `LeanMachineLearning.Optimization.NTK.ReLU.ArcCosine`, which this module
imports.

Peripheral API and optional corollaries are in
`LeanMachineLearning.Optimization.NTK.Initialization.Peripheral`; this module keeps the definitions,
core arguments, main theorem statements, proofs, and their proof narratives.

The overview below describes the full initialization development.  In particular,
`integral_conditional_output_eq_zero`, `cov_conditional_output_eq_covariance`,
`indepFun_layer_history`, and the two arc-cosine representation corollaries are peripheral
results in `Initialization.Peripheral`; all other named definitions and main results described here
are declared in this module.

## Structure

The development is a chain of modules in `Initialization/`, each importing the previous one; this
file re-exports all of them.

* `Setup` : network evaluation, the initialization probability space, readout-weight concentration.
* `GaussianAlgebra` : Gaussian vector algebra (Propositions 2.8-2.10).
* `ConditionalNormality` : Theorem 1.
* `NNGPLimit` : Theorems 2 and 3.
* `MultilayerNNGP` : multilayer sequential NNGP.
* `CovariancePropagation` : layer-by-layer Gaussian structure, covariance propagation.
* `DeepRecursion`, `DeepNNGPTheorems` : Theorem 2.13, construction and main theorems.
* `FullNTK` : full two-layer NTK initialization and infinite-width limit.

## Mathematical Formulation

* **Variable Declarations and Type Signatures**:
  * Input dimension $n_0 \in \mathbb{N}$ (represented by `d : ℕ`).
  * Hidden layer width $n \in \mathbb{N}$.
  * Number of evaluation points $m, r \in \mathbb{N}$.
  * Evaluation points $\mathbf{x}^1, \dots, \mathbf{x}^m \in \mathbb{R}^{n_0}$
    (`X : Fin m → Fin d → ℝ`).
  * Readout weights: $a_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1) \quad \forall i$
    (`gaussianReadoutMeasure n`).
  * Input weights:
    $\mathbf{w}_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(\mathbf{0}, \mathbf{I}_{n_0})$
    (`gaussianInit n d`).
  * Parameter space $\boldsymbol{\theta} = \{(a_i, \mathbf{w}_i)\}_{i=1}^n$ with joint measure
    `initMeasure n d`.
  * Mutual Independence: $\{a_i\}_{i=1}^n$ is mutually independent of $\{\mathbf{w}_i\}_{i=1}^n$
    (`indepFun_input_readout`).
  * Scalar network output:
    $f(\mathbf{x}; \boldsymbol{\theta}) =
      \frac{1}{\sqrt{n}} \sum_{i=1}^n a_i \varphi(\mathbf{w}_i^\top \mathbf{x})$
    (`evalSingle φ W a x`).
  * Output vector $\mathbf{f}_m = (f(\mathbf{x}^1), \dots, f(\mathbf{x}^m))^\top$
    (`evalVector φ W a X`).
  * Empirical covariance matrix $\boldsymbol{\Phi}^{(n)} \in \mathbb{R}^{m \times m}$:
    $\Phi^{(n), \alpha \beta} :=
      \frac{1}{n} \sum_{i=1}^n \varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)
      \varphi(\mathbf{w}_i^\top \mathbf{x}^\beta)$
    (`empiricalCovariance n φ W X`).
  * Limiting NNGP covariance matrix $\boldsymbol{\Phi} \in \mathbb{R}^{m \times m}$:
    $\Phi^{\alpha \beta} :=
      \int \varphi(\mathbf{w}^\top \mathbf{x}^\alpha) \varphi(\mathbf{w}^\top \mathbf{x}^\beta)
      d\mathcal{N}(\mathbf{0}, \mathbf{I}_{n_0})$
    (`limitingCovariance φ X`).
  * Layer hyperparameters and intermediate representations:
    weight scaling $\sigma_w \in \mathbb{R}$, bias scaling $\sigma_b \in \mathbb{R}$,
    layer width $n$, activations $\mathbf{H} \in \mathbb{R}^{n \times m}$,
    bias $b \sim \mathcal{N}(0, 1)$.
  * Projection vector $\mathbf{u} \in \mathbb{R}^m$ (`u : Fin m → ℝ`).
  * Compact subset $K \subset \mathbb{R}^{n_0}$ and Banach space
    $C(K) = \{g: K \to \mathbb{R} \mid g \text{ continuous}\}$ equipped with supremum norm
    (Mathlib's `C(K, ℝ)` via `ContinuousMap.Compact`).
  * The depth-$d$ recursive network notation ($h_1^\alpha, h_{\ell+1}^\alpha$, the limiting
    recursion $\boldsymbol{\Phi}_\ell$ via the covariance operator $\mathcal{C}_\varphi$, and
    independence across the per-layer weight matrices $\mathbf{W}_0, \dots, \mathbf{W}_d$ in place
    of an explicit filtration $\mathcal{F}_\ell$) is formalized in
    `section LayerByLayerConditionalGaussian`: see `layerCovarianceSeq`,
    `indepFun_layer_history`, and `exact_conditional_normality_layer` below.

* **Definition 2.2 (Gaussian Process)**:
  A random function $f : \mathbb{R}^{n_0} \to \mathbb{R}$ on $(\Omega, \Sigma, \mathbb{P})$
  is a Gaussian process with mean function $\mu$ and covariance kernel $\Phi$, denoted
  $f \sim \operatorname{GP}(\mu, \Phi)$, iff:
  * (i) Positive Semidefiniteness: For every $r \in \mathbb{N}$ and points
    $\mathbf{x}^1, \dots, \mathbf{x}^r$, the Gram matrix
    $[\Phi(\mathbf{x}^\alpha, \mathbf{x}^\beta)]_{\alpha,\beta=1}^r$ is symmetric positive
    semidefinite (`PosSemidef`), satisfying:
    $$\sum_{\alpha,\beta} u_\alpha u_\beta \Phi(\mathbf{x}^\alpha, \mathbf{x}^\beta) \ge 0.$$
    Formalized in Lean by `empiricalCovariance_posSemidef` for the empirical covariance
    $\boldsymbol{\Phi}^{(n)}$ and `limitingCovariance_posSemidef` for the limiting NNGP Gram
    matrix $\boldsymbol{\Phi}$.
  * (ii) Gaussian Finite-Dimensional Distributions: For every collection of inputs,
    the evaluation vector $(f(\mathbf{x}^1), \dots, f(\mathbf{x}^r))^\top$ has distribution
    $\mathcal{N}(\mu(\mathbf{x}^\cdot), [\Phi(\mathbf{x}^\alpha, \mathbf{x}^\beta)])$.
  * In Lean, the conditional network output $x \mapsto \text{evalSingle } \varphi\ W\ a\ x$
    under `gaussianReadoutMeasure n` is formalized as an exact Gaussian process in Mathlib:
    `isGaussianProcess_exact_conditional_output`, with finite-dimensional distributions
    `exact_conditional_normality`, conditional mean zero `integral_conditional_output_eq_zero`,
    and conditional covariance `cov_conditional_output_eq_covariance`.

* **Theorem 2.3 / Theorem 1 (Exact Finite-Width Conditional Normality / Step 1)**:
  * Conditional on the sub-$\sigma$-algebra $\mathcal{F}$ generated by input weights $\mathbf{W}$,
    the output vector
    $\mathbf{f}_m := (f(\mathbf{x}^1; \boldsymbol{\theta}), \dots,$
      $f(\mathbf{x}^m; \boldsymbol{\theta}))^\top$
    is an exact centered multivariate Gaussian vector:
    $$\mathbf{f}_m \mid \mathcal{F} \sim
      \mathcal{N}\left(\mathbf{0}, \boldsymbol{\Phi}^{(n)}\right)$$
    formalized by `NTK.exact_conditional_normality`.
  * The empirical covariance matrix $\boldsymbol{\Phi}^{(n)}$ is symmetric positive semidefinite
    for any width $n$ (`NTK.empiricalCovariance_posSemidef`).

* **Proof Steps for Theorem 1**:
  * Step 1: For any projection vector $\mathbf{c} \in \mathbb{R}^m$, the scalar projection is
    $$\sum_{\alpha=1}^m c_\alpha f(\mathbf{x}^\alpha; \boldsymbol{\theta}) =
      \sum_{i=1}^n a_i \psi_i$$
    where $\psi_i := \frac{1}{\sqrt{n}} \sum_{\alpha=1}^m c_\alpha \varphi(h_i(\mathbf{x}^\alpha))$
    (`NTK.projection_eq_sum_projectionCoeff`).
  * Step 2: $\psi_i$ is $\mathcal{F}$-measurable, so conditional on $\mathcal{F}$ the coefficients
    $\psi_i$ are deterministic constants (`NTK.projectionCoeff_measurable`).
  * Step 3: $\{a_i\}_{i=1}^n$ are independent of $\mathcal{F}$ and i.i.d. standard Gaussian; thus
    $\sum_{i=1}^n a_i \psi_i$ is a linear combination of independent zero-mean Gaussians.
  * Step 4: The variance of the linear combination is
    $$\sum_{i=1}^n \psi_i^2 = \mathbf{c}^\top \boldsymbol{\Phi}^{(n)} \mathbf{c}$$
    (`NTK.sum_projectionCoeff_sq_eq_bilin`),
    and the 1D pushforward distribution along $\mathbf{c}$ is
    $\mathcal{N}(0, \mathbf{c}^\top \boldsymbol{\Phi}^{(n)} \mathbf{c})$
    (`NTK.map_readout_projection_eq_gaussianReal`).
  * Step 5: By the Cramér-Wold device / characteristic function uniqueness for multivariate
    distributions (`Measure.ext_of_charFun`), the conditional joint distribution of $\mathbf{f}_m$
    is $\mathcal{N}(\mathbf{0}, \boldsymbol{\Phi}^{(n)})$ (`NTK.exact_conditional_normality`).

* **Theorem 2 (Strong Law of Large Numbers for the Covariance Tensor / Asymptotic NNGP Limit)**:
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

* **Proof Steps for Theorem 2**:
  * Step 1: For fixed inputs $\mathbf{x}^\alpha, \mathbf{x}^\beta$,
    define the scalar random variables
    $$Y_i := \varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)
      \varphi(\mathbf{w}_i^\top \mathbf{x}^\beta)$$
    for $i \in \{1, \dots, n\}$ (`NTK.measurable_cov_summand`).
  * Step 2: Because $\{\mathbf{w}_i\}_{i=1}^n$ are i.i.d. across hidden units, the sequence
    $\{Y_i\}_{i=1}^n$ is independent and identically distributed.
  * Step 3: Under square-integrability of $\varphi$, the expectation exists and is finite by
    Cauchy-Schwarz:
    $$\mathbb{E}_{\mathbf{w}_i}\left[ |Y_i| \right] \le
      \sqrt{\mathbb{E}_{\mathbf{w}_i}[\varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)^2]
      \mathbb{E}_{\mathbf{w}_i}[\varphi(\mathbf{w}_i^\top \mathbf{x}^\beta)^2]} < \infty$$
    (`NTK.integrable_cov_summand_of_memLp`).
  * Step 4: By Kolmogorov's Strong Law of Large Numbers (SLLN):
    $$\Phi^{(n), \alpha \beta} = \frac{1}{n} \sum_{i=1}^n Y_i
      \xrightarrow{\text{a.s.}} \mathbb{E}_{\mathbf{w}}[Y_1] = \Phi^{\alpha \beta}.$$

* **Theorem 2.3 / Theorem 3 (Finite-Dimensional NNGP Limit / Multivariate Convergence)**:
  * As width $n \to \infty$, the output vector $\mathbf{f}_m$ converges in distribution under the
    joint initialization measure `initMeasure n d` to the centered multivariate Gaussian
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

* **Proof Steps for Theorem 3**:
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

* **Theorem (Gaussianity of Linear Combinations / Scalar NNGP Limit)**:
  * For every fixed projection vector $\mathbf{u} \in \mathbb{R}^m$, the scalar linear combination
    converges in distribution to a zero-mean univariate normal random variable:
    $$S_n(\mathbf{u}) = \sum_{\alpha=1}^m u_\alpha f(\mathbf{x}^\alpha; \boldsymbol{\theta})
      \xrightarrow{d} \mathcal{N}\left( 0, \mathbf{u}^\top \boldsymbol{\Phi} \mathbf{u} \right)$$
    formalized by `NTK.map_projection_tendsto_gaussianReal` and
    `NTK.tendstoInDistribution_projection`.
  * Step 1: Linear combination of readout weights:
    $S_n(\mathbf{u}) = \sum_{i=1}^n a_i \psi_i(\mathbf{u})$.
  * Step 2: Exact conditional distribution:
    $S_n(\mathbf{u}) \mid \mathcal{F} \sim
      \mathcal{N}(0, \mathbf{u}^\top \boldsymbol{\Phi}^{(n)} \mathbf{u})$.
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
  * Step 6: Weak convergence conclusion via 1D Lévy Continuity Theorem:
    $S_n(\mathbf{u}) \xrightarrow{d} \mathcal{N}(0, \mathbf{u}^\top \boldsymbol{\Phi} \mathbf{u})$.

* **Theorem (Multilayer Sequential NNGP: Conditional Normality, SLLN Recurrence, and Limit)**:
  * In deep networks, the layer-to-layer preactivation vector evaluated at $m$ inputs satisfies:
    $$h_\alpha^{(\ell+1)} =
      \sigma_b b + \frac{\sigma_w}{\sqrt{n}} \sum_{j=1}^n w_j \varphi(h_{j,\alpha}^{(\ell)})$$
    with weight vector $\mathbf{w} \sim \mathcal{N}(\mathbf{0}, \mathbf{I}_n)$ and bias
    $b \sim \mathcal{N}(0, 1)$.
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
  * Public Bivariate Corollary ($m = 2$):
    `NTK.tendstoInDistribution_sequential_bivariate`.

* **Layer-by-Layer Conditional Gaussian Structure**:
  * **Independence Across Depth**: mutual independence of the per-layer weight matrices
    $\mathbf{W}_0, \dots, \mathbf{W}_{L-1}$ implies each $\mathbf{W}_\ell$ is independent of the
    history $(\mathbf{W}_i)_{i < \ell}$, formalized for a common per-layer shape by
    `NTK.indepFun_layer_history`.
  * The recursively-defined deterministic limiting forward covariance kernel
    $\boldsymbol{\Phi}_0, \boldsymbol{\Phi}_{\ell+1} := \mathcal{C}_\varphi(\boldsymbol{\Phi}_\ell)$
    is formalized by `NTK.layerCovarianceSeq`, with positive semidefiniteness at every layer
    `NTK.layerCovarianceSeq_posSemidef` (reusing `NTK.limitingRecurrence_posSemidef_multivariate`
    at each step).
  * **Theorem (Conditional Pre-Activation Distribution)**: conditioned on the width-$n$
    previous-layer post-activations $\mathbf{H}$ (representing conditioning on $\mathcal{F}_\ell$,
    as throughout this file), the full width-$n'$ next-layer preactivation vector
    $\mathbf{H}_{\ell+1} \in \mathbb{R}^{m n'}$ (stacked
    $[(\mathbf{h}_{\ell+1}^1)^\top, \dots, (\mathbf{h}_{\ell+1}^m)^\top]^\top$) is exactly Gaussian
    with covariance $\boldsymbol{\Phi}_\ell^{(n)} \otimes \mathbf{I}_{n'}$:
    $$\mathbf{H}_{\ell+1} \mid \mathbf{H} \sim
      \mathcal{N}\left(\mathbf{0}, \boldsymbol{\Phi}_\ell^{(n)} \otimes \mathbf{I}_{n'}\right)$$
    formalized by `NTK.exact_conditional_normality_layer`, via two Gaussian-vector-algebra
    ingredients:
    * The `Fin m`-family generalizations of Propositions 2.9-2.10 from a fixed pair of vectors to
      a fixed family (`NTK.stdGaussian_inner_family`, `NTK.gaussianMatrix_mulVec_family`), giving
      the row-indexed (neuron-indexed) family of $n'$ i.i.d. copies of the single-neuron
      $m$-variate Gaussian $\mathcal{N}(\mathbf{0}, \boldsymbol{\Phi}_\ell^{(n)})$.
    * The Kronecker concatenation of $n'$ i.i.d. Gaussian vectors into one Gaussian vector with
      covariance $\boldsymbol{\Phi}_\ell^{(n)} \otimes \mathbf{I}_{n'}$
      (`NTK.multivariateGaussian_pi_eq_kronecker`).

* **Asymptotic Propagation of the Empirical Covariance Matrix**:
  * `NTK.conditional_preactivations_eq_pi` makes the coordinate-decoupling consequence explicit:
    conditionally on a fixed preceding layer, new-neuron preactivation vectors have a product law
    of identical centered multivariate Gaussians with the activated empirical covariance.
  * For continuous activations of polynomial growth,
    `NTK.conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq` proves that the
    activated empirical covariance of this conditional i.i.d. Gaussian layer converges in
    probability to the next deterministic forward kernel.  The reusable fixed-covariance form is
    `NTK.conditional_empiricalCovariance_tendstoInMeasure_of_polynomial_growth`.

* **Proposition 2.5 (Cho-Saul / Arc-Cosine Kernel for ReLU)**:
  Under the joint Gaussian distribution
  $(h^\alpha, h^\beta) \sim \mathcal{N}(\mathbf{0}, \boldsymbol{\Sigma})$ with
  $\Phi^{\alpha \alpha}, \Phi^{\beta \beta} > 0$ and Pearson correlation
  $\rho = \frac{\Phi^{\alpha \beta}}{\sqrt{\Phi^{\alpha \alpha} \Phi^{\beta \beta}}} \in [-1, 1]$
  (`NTK.pearsonRho_mem_Icc`, `NTK.corrMatrix2x2_posSemidef`):
  * The expected product of ReLU derivatives (the 1-st order / derivative kernel) is:
    $$\mathbb{E}_{(h^\alpha, h^\beta)}\left[ \varphi'(h^\alpha) \varphi'(h^\beta) \right] =
      \mathbb{P}\left( h^\alpha > 0, h^\beta > 0 \right) =
      \frac{1}{4} + \frac{1}{2\pi} \arcsin(\rho)$$
    formalized by `NTK.expected_reluIndicator_mul_reluIndicator_bivariate` and
    `NTK.expected_reluDeriv_mul_reluDeriv_bivariate`.
  * The expected product of ReLU activations (the 0-th order / NNGP kernel) is:
    $$\mathbb{E}_{(h^\alpha, h^\beta)}\left[ \varphi(h^\alpha) \varphi(h^\beta) \right] =
      \frac{\sqrt{\Phi^{\alpha \alpha} \Phi^{\beta \beta}}}{2\pi}
      \left( \sqrt{1 - \rho^2} + \rho \left( \frac{\pi}{2} + \arcsin(\rho) \right) \right)$$
    formalized by `NTK.expected_relu_mul_relu_bivariate`.
  * Closed-form evaluation of the bivariate limiting recurrence entry for ReLU:
    $$\sigma_b^2 + \sigma_w^2 \mathbb{E}_{(h^\alpha, h^\beta)}
      \left[ \varphi(h^\alpha) \varphi(h^\beta) \right] =$$
    $$\sigma_b^2 + \sigma_w^2 \frac{\sqrt{\Phi^{\alpha \alpha} \Phi^{\beta \beta}}}{2\pi}
      \left( \sqrt{1 - \rho^2} + \rho \left( \frac{\pi}{2} + \arcsin(\rho) \right) \right)$$
    formalized by `NTK.limitingRecurrence_relu_bivariate`.
  * Step 1: Reduction to standardized variables via positive homogeneity
    (`NTK.relu_pos_mul`, `NTK.expected_relu_mul_relu_eq_scale_mul_standardized`).
  * Step 2: Cholesky decomposition of the $2 \times 2$ correlation matrix into two independent
    standard Gaussians (`NTK.cholesky2x2_mul_transpose`, `NTK.map_cholesky2x2_stdGaussian`).
  * Step 3: Polar-coordinate evaluation of angular sectors for ReLU and its derivative
    (`NTK.expected_reluIndicator_mul_reluIndicator_standardized`,
    `NTK.expected_relu_mul_relu_standardized`, `NTK.div_two_pi_pi_sub_arccos_eq_arcsin`).
  * Step 4: Final scaling assembly.

* **Connection to Arc-Cosine Kernel Geometry (Cho & Saul)**:
  With $\theta := \arccos(\rho) \in [0, \pi]$, Proposition 2.5's two kernels rewrite exactly as
  half of the order-0 and order-1 arc-cosine kernels:
  $$J_0(\theta) := \frac{1}{\pi}(\pi - \theta), \qquad
    J_1(\theta) := \frac{1}{\pi}\left(\sin\theta + (\pi - \theta)\cos\theta\right)$$
  $$\mathbb{E}[\varphi'(h^\alpha)\varphi'(h^\beta)] = \frac{1}{2}J_0(\theta)
    \quad\text{(`NTK.expected_reluDeriv_mul_reluDeriv_bivariate_eq_arcCosineJ0`)}$$
  $$\mathbb{E}[\varphi(h^\alpha)\varphi(h^\beta)] =
    \frac{\sqrt{\Phi^{\alpha\alpha}\Phi^{\beta\beta}}}{2}J_1(\theta)
    \quad\text{(`NTK.expected_relu_mul_relu_bivariate_eq_arcCosineJ1`)}$$
  Both are proved as trigonometric rewrites of the already-established $\rho$-form of
  Proposition 2.5, with no new probabilistic content.

* **Propositions 2.8-2.10 (Gaussian Vector Algebra)**:
  General, non-NTK-specific facts about Gaussian vectors under linear maps, underlying the
  conditional-normality arguments used throughout Theorem 1 and `MultilayerSequentialNNGP`:
  * Proposition 2.8: a linear image `A g` of a Gaussian vector `g ~ 𝒩(μ, S)` is again Gaussian,
    `A g ~ 𝒩(A μ, A S Aᵀ)` (`NTK.gaussian_map_mulVec`).
  * Proposition 2.9: for `g ~ 𝒩(0, I_n)` and fixed `u, v : Fin n → ℝ`, the joint law of
    `(⟪g,u⟫, ⟪g,v⟫)` is the bivariate Gaussian with covariance
    `!![u⬝ᵥu, u⬝ᵥv; u⬝ᵥv, v⬝ᵥv]` (`NTK.stdGaussian_inner_pair`), proved as a corollary of
    Proposition 2.8.
  * Proposition 2.10: for a matrix `W` with i.i.d. standard Gaussian entries, the row-indexed
    family `i ↦ (W i ⬝ᵥ u, W i ⬝ᵥ v)` consists of `n` i.i.d. copies of Proposition 2.9's
    bivariate Gaussian (`NTK.gaussianMatrix_mulVec_pair`), proved by pushing the row-product
    measure `gaussianInit n n` forward row-by-row via `Measure.pi_map_pi`.
  * Propositions 2.9' and 2.10': the direct `Fin m`-indexed generalizations of Propositions 2.9
    and 2.10 from a fixed pair of vectors to a fixed family `u : Fin m → Fin n → ℝ`
    (`NTK.stdGaussian_inner_family`, `NTK.gaussianMatrix_mulVec_family`), proved by the same
    techniques; used by the Layer-by-Layer Conditional Gaussian Structure below.

## Main definitions and theorems

* **Preliminaries and Initialization Probability Space**:
  * `NTK.evalSingle` : scalar network output
    $f(\mathbf{x}; \mathbf{W}, a) =
      \frac{1}{\sqrt{n}} \sum_{i=1}^n a_i \varphi(\mathbf{w}_i^\top \mathbf{x})$.
  * `NTK.evalSingle_eq_normalized_sum` : equation lemma for scalar network evaluation.
  * `NTK.evalVector` : output vector $\mathbf{f}_m(\mathbf{W}, a) \in \mathbb{R}^m$.
  * `NTK.empiricalCovariance` : empirical covariance matrix
    $\boldsymbol{\Phi}^{(n)} \in \mathbb{R}^{m \times m}$.
  * `NTK.gaussianReadoutMeasure` : transparent product measure
    $\bigotimes_{i=1}^n \mathcal{N}(0, 1)$.
  * `NTK.initMeasure` : joint parameter initialization measure
    $(\bigotimes_{i=1}^n \mathcal{N}(\mathbf{0}, \mathbf{I}_{n_0})) \otimes
      (\bigotimes_{i=1}^n \mathcal{N}(0, 1))$.
  * `NTK.indepFun_input_readout` : mutual independence of input weights $\mathbf{W}$ and
    readout weights $a$.

* **Gaussian Vector Algebra (Propositions 2.8-2.10)**:
  * `NTK.inner_eq_dotProduct_ofLp` : the real `EuclideanSpace` inner product is the `dotProduct`
    of the underlying coordinate functions.
  * `NTK.gaussian_map_mulVec` : Proposition 2.8, `A g ~ 𝒩(A μ, A S Aᵀ)` for a linear image of a
    Gaussian vector.
  * `NTK.stdGaussian_inner_pair` : Proposition 2.9, the joint law of `(⟪g,u⟫, ⟪g,v⟫)` for
    `g ~ 𝒩(0, I_n)`.
  * `NTK.gaussianMatrix_mulVec_pair` : Proposition 2.10, the row-indexed joint law of
    `(W ⬝ᵥ u, W ⬝ᵥ v)` for an i.i.d. Gaussian matrix `W`.
  * `NTK.stdGaussian_inner_family`, `NTK.gaussianMatrix_mulVec_family` : the `Fin m`-family
    generalizations of Propositions 2.9-2.10.

* **Theorem 1: Exact Finite-Width Conditional Normality**:
  * `NTK.projectionCoeff` : projection coefficients
    $\psi_i = \frac{1}{\sqrt{n}} \sum_\alpha c_\alpha \varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)$.
  * `NTK.projectionCoeff_eq_normalized_sum`, `NTK.projectionCoeff_sq`,
    `NTK.projectionCoeff_measurable` : equation, square-expansion,
    and $\mathcal{F}$-measurability API for `projectionCoeff`.
  * `NTK.projection_eq_sum_projectionCoeff` : Step 1 algebraic identity
    $\sum_\alpha c_\alpha f(\mathbf{x}^\alpha) = \sum_i a_i \psi_i$.
  * `NTK.sum_projectionCoeff_sq_eq_bilin` : Step 4 variance identity
    $\sum_i \psi_i^2 = \mathbf{c}^\top \boldsymbol{\Phi}^{(n)} \mathbf{c}$.
  * `NTK.empiricalCovariance_posSemidef` : positive semidefiniteness of $\boldsymbol{\Phi}^{(n)}$.
  * `NTK.map_readout_projection_eq_gaussianReal` : Step 4 1D conditional normality.
  * `NTK.exact_conditional_normality` : Theorem 1 exact multivariate conditional normality
    $\mathbf{f}_m \mid \mathbf{W} \sim \mathcal{N}(\mathbf{0}, \boldsymbol{\Phi}^{(n)})$.
  * `NTK.isGaussianProcess_exact_conditional_output` : Definition 2.2 exact conditional Gaussian
    process.
  * `NTK.integral_conditional_output_eq_zero`, `NTK.cov_conditional_output_eq_covariance` :
    zero conditional mean and conditional covariance matching $\boldsymbol{\Phi}^{(n)}$.

* **Theorem 2: Strong Law of Large Numbers for the Covariance Tensor**:
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

* **Theorem 3: Multivariate Asymptotic NNGP Limit and Linear Combinations**:
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

* **Multilayer Sequential NNGP**:
  * `NTK.empirical_layer_covariance_posSemidef_multivariate` : positive semidefiniteness of the
    empirical layer covariance matrix.
  * `NTK.exact_conditional_normality_general_multivariate` : exact multivariate conditional
    normality across layers.
  * `NTK.empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate` : entrywise SLLN
    convergence of the sequential empirical covariance recurrence.
  * `NTK.limitingRecurrence_posSemidef_multivariate` : positive semidefiniteness of the limiting
    recurrence matrix.
  * `NTK.tendsto_charFun_sequential_preactivation_multivariate` : pointwise DCT convergence of the
    multivariate preactivation characteristic functions.
  * `NTK.tendstoInDistribution_sequential_preactivation` : master theorem for arbitrary `Fin m`.
  * `NTK.tendstoInDistribution_sequential_bivariate` : public `m = 2` bivariate corollary.

* **Layer-by-Layer Conditional Gaussian Structure**:
  * `NTK.multivariateGaussian_pi_eq_kronecker` : Kronecker-product concatenation of `n` i.i.d.
    Gaussian vectors (built on the `Fin m`-family Propositions 2.9'-2.10' above).
  * `NTK.indepFun_layer_history` : Independence Across Depth, `W_ℓ` independent of the history
    `(W_i)_{i < ℓ}`.
  * `NTK.layerCovarianceSeq`, `NTK.layerCovarianceSeq_posSemidef` : the recursive limiting kernel
    $\Phi_\ell$ and its positive semidefiniteness at every layer.
  * `NTK.exact_conditional_normality_layer` : Theorem (Conditional Pre-Activation Distribution),
    $\mathbf{H}_{\ell+1} \mid \mathbf{H} \sim \mathcal{N}(\mathbf{0}, \boldsymbol{\Phi}_\ell^{(n)}
      \otimes \mathbf{I}_{n'})$.

* **Asymptotic Empirical Covariance Propagation**:
  * `NTK.conditional_preactivations_eq_pi` : conditional i.i.d. neuron-vector product law.
  * `NTK.memLp_activation_coordinate_of_polynomial_growth` : polynomial growth implies the
    coordinatewise Gaussian $L^2$ condition.
  * `NTK.conditional_empiricalCovariance_tendstoInMeasure` : conditional empirical covariance
    convergence in probability under a direct $L^2$ hypothesis.
  * `NTK.conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq` : the corresponding
    recursive forward-kernel statement for continuous polynomial-growth activations.

* **Theorem 2.13 (Deep NNGP Recursion)**: assembles the single-layer machinery above into an
  actual depth-`L` network with real chained weight matrices.
  * `NTK.deepPreactivation` : the recursive pre-activation family $h_1, \dots, h_L$ of a depth-$L$
    MLP, built from a single infinite population of i.i.d. standard Gaussian weights.
  * `NTK.indepFun_deepLayer_history` : Independence Across Depth for this population (the
    infinite-population analogue of `NTK.indepFun_layer_history`).
  * `NTK.instPseudoEMetricSpaceMatrix` : the missing `PseudoEMetricSpace (Matrix (Fin m) (Fin m) ℝ)`
    glue instance (Mathlib deliberately does not register one directly, to avoid a diamond with
    other matrix norms), needed for the lemma below.
  * `NTK.tendstoInMeasure_comp_of_continuousAt`,
    `NTK.tendsto_integral_of_tendstoInMeasure_of_bounded` : general-purpose
    convergence-in-probability lemmas (continuous mapping to a constant limit; bounded convergence)
    missing from Mathlib's `ConvergenceInMeasure` API, needed by the theorems below.
  * `NTK.continuousWithinAt_covarianceMap` : continuity of the covariance-update map
    $\mathcal{C}_\varphi$ on the positive-semidefinite cone, including its singular boundary.
  * `NTK.deepEmpiricalCovariance_tendstoInMeasure` : Part 1, layerwise covariance convergence in
    probability $\Phi_\ell^{(n)} \xrightarrow{\mathbb{P}} \Phi_\ell$. **Currently `sorry`d** — see
    its docstring for the remaining random-conditional-layer fluctuation argument.
  * `NTK.measurable_deepEval`, `NTK.deepEval_covariance_posSemidef`,
    `NTK.map_deepEval_snd_eq_multivariateGaussian`, `NTK.charFun_map_deepEval`,
    `NTK.norm_charFun_deepEval_le_one`, `NTK.aestronglyMeasurable_charFun_deepEval`,
    `NTK.tendsto_charFun_map_deepEval` : supporting measurability, positive-semidefiniteness, exact
    conditional normality, and characteristic-function lemmas for the depth-$L$ network's output,
    assembled into Part 2 below.
  * `NTK.tendstoInDistribution_deepEval` : Part 2, output convergence in distribution
    $\mathbf{f}_m(\boldsymbol{\theta}) \xrightarrow{d} \mathcal{N}(\mathbf{0}, \Phi_L)$. Fully
    proved (reuses `NTK.exact_conditional_normality_general_multivariate` verbatim for the exact
    conditional normality step; depends on Part 1's statement, which is still `sorry`d above).

* **Cho-Saul / Arc-Cosine Kernel for ReLU (Proposition 2.5)**:
  * `NTK.relu` : Rectified Linear Unit activation function $\varphi(u) = \max\{u, 0\}$.
  * `NTK.reluDeriv` : weak derivative alias to `Kernel.reluIndicator`.
  * `NTK.pearsonRho_mem_Icc` : Pearson correlation $\rho \in [-1, 1]$.
  * `NTK.corrMatrix2x2_posSemidef` : positive semidefiniteness of the $2 \times 2$ correlation
    matrix for $\rho \in [-1, 1]$.
  * `NTK.div_two_pi_pi_sub_arccos_eq_arcsin` : trigonometric conversion between arccosine and
    arcsine forms.
  * `NTK.expected_reluIndicator_mul_reluIndicator_bivariate` : Proposition 2.5 derivative kernel
    $\frac{1}{4} + \frac{1}{2\pi}\arcsin(\rho)$.
  * `NTK.expected_reluDeriv_mul_reluDeriv_bivariate` : derivative kernel stated with weak-derivative
    notation `reluDeriv`.
  * `NTK.expected_relu_mul_relu_bivariate` : Proposition 2.5 0-th order / NNGP kernel
    $\frac{\sqrt{\Phi^{\alpha\alpha}\Phi^{\beta\beta}}}{2\pi}(\sqrt{1-\rho^2} +
      \rho(\frac{\pi}{2}+\arcsin(\rho)))$.
  * `NTK.limitingRecurrence_relu_bivariate` : closed-form evaluation of the bivariate limiting
    recurrence for ReLU.
  * `NTK.expected_reluDeriv_mul_reluDeriv_bivariate_eq_arcCosineJ0` : the derivative kernel as
    `(1/2) J₀(arccos ρ)`, the order-0 arc-cosine kernel of Cho & Saul.
  * `NTK.expected_relu_mul_relu_bivariate_eq_arcCosineJ1` : the activation kernel as
    `(√(Φαα Φββ)/2) J₁(arccos ρ)`, the order-1 arc-cosine kernel of Cho & Saul.
* **Full Two-Layer NTK Initialization, Concentration, and Strong Law**:
  * `NTK.singleNeuronMeasure` : product probability measure for a single hidden neuron `(w, a)`.
  * `NTK.measurePreserving_arrowProd_singleNeuronMeasure` : measure preservation of the finite
    array rearrangement between `(Fin n → singleNeuronMeasure d)` and `initMeasure n d`.
  * `NTK.measurePreserving_infiniteSeq_to_init` : measure preservation of the infinite sequence
    prefix truncation to `initMeasure n d`.
  * `NTK.fullNTKSummandSecondMoment` : uncentered second moment of the full NTK summand.
  * `NTK.measurable_fullNTK_summand` : measurability of full activation-derivative summand.
  * `NTK.integrable_fullNTK_summand` : integrability under product Gaussian measure.
  * `NTK.memLp_two_fullNTK_summand` : square-integrability (`MemLp 2`) of full summand.
  * `NTK.integrable_sq_fullNTK_summand` : second-moment bound for quantitative concentration.
  * `NTK.integral_fullNTK_summand` : expectation identity decomposing into NNGP plus
    derivative kernel.
  * `NTK.fullNTKSummand_tendsto_integral` : entrywise almost-sure convergence of empirical sums.
  * `NTK.fullNTKMatrix_tendsto_integral` : almost-sure matrix convergence on dataset `X`.
  * `NTK.fullNTKMatrix_norm_sub_tendsto_zero` : matrix norm almost-sure convergence.
  * `NTK.fullNTKMatrix_tendstoInMeasure` : matrix convergence in probability (`TendstoInMeasure`).
  * `NTK.fullNTKMatrix_scaled_dataset_tendsto_integral` : almost-sure matrix convergence on
    the paper's scaled dataset `(1 / √d) * X`.
  * `NTK.fullNTKMatrix_scaled_dataset_tendstoInMeasure` : convergence in probability on the
    paper's scaled dataset `(1 / √d) * X`.
-/
