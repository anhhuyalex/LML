/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.Shallow.Kernel
public import LeanMachineLearning.Optimization.NTK.Shallow.Linearization
public import LeanMachineLearning.Optimization.NTK.ReLU.ArcCosine
public import LeanMachineLearning.Optimization.NTK.Foundations.SlutskyTightness
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Analysis.Matrix.Normed

/-!
# NTK Initialization, Gaussian Processes, and Finite-Dimensional NNGP Limit

This file formalizes the parameter initialization probability space, mutual independence
structure, Definition 2.2 (Gaussian Processes), Theorem 1 / Step 1 (Exact Conditional Normality),
Theorem 2 / Step 2 (Strong Law of Large Numbers for the Covariance Tensor), Theorem 2.3 /
Theorem 3 (Finite-Dimensional NNGP Limit at Initialization), Multilayer Sequential NNGP
recurrence convergence, the Layer-by-Layer Conditional Gaussian Structure (independence across
depth and the depth-$d$ recursive kernel $\Phi_\ell$).  Proposition 2.5 (Cho-Saul / Arc-Cosine
Kernel for ReLU) is in `LeanMachineLearning.Optimization.NTK.ReLU.ArcCosine`, which this module imports.

Peripheral API and optional corollaries are in
`LeanMachineLearning.Optimization.NTK.Initialization.Peripheral`; this module keeps the definitions,
core arguments, main theorem statements, proofs, and their proof narratives.

The overview below describes the full initialization development.  In particular,
`integral_conditional_output_eq_zero`, `cov_conditional_output_eq_covariance`,
`indepFun_layer_history`, and the two arc-cosine representation corollaries are peripheral
results in `Initialization.Peripheral`; all other named definitions and main results described here
are declared in this module.

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

@[expose] public section

set_option linter.style.longLine false

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section Preliminaries

/-! ## Network Setup and Initialization Probability Space -/

/-! ### Network Evaluation and Empirical Covariance -/

/-- Single-output evaluation of a two-layer neural network with width `n`, activation `φ`,
input weights `W`, and readout weights `a`:
  `f(x; W, a) = (1/√n) ∑ i, a i * φ (W i ⬝ᵥ x)`. -/
noncomputable def evalSingle
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, a i * φ (W i ⬝ᵥ x)

/-- The normalized-sum formula for a scalar network evaluation. This is the public
equation lemma for `evalSingle`, so proofs need not unfold its implementation. -/
lemma evalSingle_eq_normalized_sum
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (x : Fin d → ℝ) :
    evalSingle φ W a x = (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, a i * φ (W i ⬝ᵥ x) := rfl

/-- The output vector `f_m(W, a) ∈ ℝᵐ` evaluated at `m` input points `X 0, …, X (m - 1)`:
  `f_m(W, a)_α = f(X α; W, a)`. -/
noncomputable def evalVector
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (X : Fin m → Fin d → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun α => evalSingle φ W a (X α))

/-- The empirical covariance matrix `Φ^{(n)} ∈ ℝ^{m × m}`:
  `Φ^{(n), α β} = (1/n) ∑ i, φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β)`. -/
noncomputable def empiricalCovariance
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun α β => (n : ℝ)⁻¹ * ∑ i : Fin n, φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β)

/-! ### API for Network Evaluation -/

@[simp] lemma evalVector_ofLp
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (X : Fin m → Fin d → ℝ) (α : Fin m) :
    (evalVector φ W a X).ofLp α = evalSingle φ W a (X α) := rfl

lemma evalVector_inner
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (a : Fin n → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    ⟪t, evalVector φ W a X⟫ = ∑ α : Fin m, t.ofLp α * evalSingle φ W a (X α) := by
  simp only [evalVector, PiLp.inner_apply, RCLike.inner_apply', conj_trivial]

lemma evalVector_continuous
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Continuous (fun a => evalVector φ W a X) := by
  change Continuous ((WithLp.toLp 2) ∘ (fun a α => evalSingle φ W a (X α)))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => ?_)
  simp only [evalSingle_eq_normalized_sum]
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul continuous_const)

lemma evalVector_measurable
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Measurable (fun a => evalVector φ W a X) :=
  (evalVector_continuous φ W X).measurable

lemma inner_evalVector_continuous
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun a => ⟪t, evalVector φ W a X⟫) :=
  (innerSL ℝ t).continuous.comp (evalVector_continuous φ W X)

lemma inner_evalVector_measurable
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Measurable (fun a => ⟪t, evalVector φ W a X⟫) :=
  (inner_evalVector_continuous φ W X t).measurable

/-! ### Initialization Probability Space and Independence Structure -/

/-- Transparent readout weight product measure on `Fin n → ℝ` with i.i.d. coordinates $\mathcal{N}(0, 1)$. -/
noncomputable abbrev gaussianReadoutMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- Instance: `gaussianInit n d` from `Basic.lean` is a probability measure. -/
instance instIsProbabilityMeasureGaussianInit (n d : ℕ) :
    IsProbabilityMeasure (gaussianInit n d) := by
  dsimp [gaussianInit]
  infer_instance

/-- Transparent joint initialization measure on `(Fin n → Fin d → ℝ) × (Fin n → ℝ)`
using the existing `NTK.gaussianInit` from `Basic.lean`. -/
noncomputable abbrev initMeasure (n d : ℕ) : Measure ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) :=
  (gaussianInit n d).prod (gaussianReadoutMeasure n)

/-- Readout weight coordinates `a_i` have marginal standard normal distribution
$\mathcal{N}(0, 1)$. -/
lemma map_gaussianReadoutMeasure_coord (i : Fin n) :
    Measure.map (fun a : Fin n → ℝ => a i) (gaussianReadoutMeasure n) = gaussianReal 0 1 :=
  (MeasureTheory.measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq

/-- The square function is integrable with respect to the standard real Gaussian measure. -/
lemma integrable_sq_gaussianReal : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq
    (memLp_id_gaussianReal (2 : NNReal)).aestronglyMeasurable).1
  exact memLp_id_gaussianReal (2 : NNReal)

/-- The second moment of the standard real Gaussian measure is 1. -/
lemma integral_sq_gaussianReal : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral (X := id) measurable_id'.aemeasurable] at h
  simpa [id] using h

/-- The fourth power is integrable with respect to the standard real Gaussian measure. -/
lemma integrable_pow_four_gaussianReal :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have h := memLp_id_gaussianReal (4 : NNReal) (μ := 0) (v := 1)
  have hint := h.integrable_norm_rpow (by norm_num) (by norm_num)
  have heq : (fun x : ℝ => ‖id x‖ ^ (4 : ℝ)) = (fun x : ℝ => x ^ 4) := by
    ext x
    simp only [id, Real.norm_eq_abs]
    have h1 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h1, Real.rpow_natCast]
    have h2 : |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    have h3 : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [h2, sq_abs, ← h3]
  have h_exp : ((4 : NNReal) : ENNReal).toReal = 4 := by rfl
  rw [h_exp] at hint
  rw [heq] at hint
  exact hint

/-- The square function is square-integrable (in `MemLp 2`) with respect to the standard
real Gaussian measure. -/
lemma memLp_sq_gaussianReal_two :
    MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have heq : (fun x : ℝ => (x ^ 2) ^ 2) = (fun x : ℝ => x ^ 4) := by
    ext x; ring
  rw [heq]
  exact integrable_pow_four_gaussianReal

/-- The normalized squared Euclidean norm of a readout vector. -/
noncomputable def gaussianReadoutEnergy (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2

/-- Markov tail bound for the normalized squared readout energy. -/
lemma prob_gaussianReadout_sum_sq_le
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussianReadoutMeasure n).real {a | (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2 ≤ δ⁻¹} ≥
      1 - δ :=
  measureReal_pi_average_le_ge_one_sub (μ := gaussianReal 0 1) hn (g := fun a : ℝ => a ^ 2)
    (by fun_prop) integrable_sq_gaussianReal (fun _ => sq_nonneg _) (inv_pos.2 hδ)
    (by rw [integral_sq_gaussianReal, inv_mul_cancel₀ hδ.ne'])

/-- **Empirical activation energy concentration.** If `φ(w ⬝ᵥ x_α)` is square integrable under the
Gaussian row law and `∑_α E φ(w ⬝ᵥ x_α)² ≤ τ δ`, then the width-normalized activation energy
`n⁻¹ ∑_i ∑_α φ(W_i ⬝ᵥ x_α)²` of the hidden weights is at most `τ` with probability `≥ 1 - δ`. -/
lemma measureReal_gaussianInit_activationEnergy_le {n d m : ℕ} (hn : 0 < n) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    {τ δ : ℝ} (hτ : 0 < τ)
    (hv : ∑ α : Fin m, ∫ w, φ (w ⬝ᵥ X α) ^ 2 ∂(gaussianRowMeasure d) ≤ τ * δ) :
    (gaussianInit n d).real {W | (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m,
      φ (W i ⬝ᵥ X α) ^ 2 ≤ τ} ≥ 1 - δ :=
  measureReal_pi_average_le_ge_one_sub (μ := gaussianRowMeasure d) hn
    (g := fun w => ∑ α : Fin m, φ (w ⬝ᵥ X α) ^ 2)
    (Finset.measurable_sum _ fun α _ =>
      (hφ.comp (measurable_dotProduct_left (X α))).pow_const 2)
    (integrable_finsetSum _ fun α _ => (hL2 α).integrable_sq) (fun w => by positivity) hτ
    (by rwa [integral_finsetSum _ fun α _ => (hL2 α).integrable_sq])

/-- A measurable activation with at most linear growth has all Gaussian moments along a row. -/
lemma memLp_gaussianRow_comp_of_linear_growth (φ : ℝ → ℝ) (hφ : Measurable φ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrow : ∀ z, |φ z| ≤ A + B * |z|) (x : Fin d → ℝ) (p : NNReal) :
    MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ x)) p (gaussianRowMeasure d) := by
  have hlin : Measurable (fun w : Fin d → ℝ => w ⬝ᵥ x) := measurable_dotProduct_left x
  change MemLp (φ ∘ fun w : Fin d → ℝ => w ⬝ᵥ x) p (gaussianRowMeasure d)
  rw [← memLp_map_measure_iff (hφ.aestronglyMeasurable) hlin.aemeasurable,
    map_gaussianRowMeasure_dotProduct]
  have hid := memLp_id_gaussianReal (μ := 0) (v := Real.toNNReal (x ⬝ᵥ x)) p
  refine MemLp.of_le (g := fun z => A + B * ‖z‖) ?_ hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  · exact (memLp_const A).add (hid.norm.const_mul B)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ A + B * ‖z‖)]
    simpa [Real.norm_eq_abs] using hgrow z

/-- Product of two such activations along rows is square integrable (Hölder with exponents
`4, 4 → 2`). -/
lemma memLp_two_gaussianRow_mul_comp_of_linear_growth (φ : ℝ → ℝ) (hφ : Measurable φ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrow : ∀ z, |φ z| ≤ A + B * |z|) (x x' : Fin d → ℝ) :
    MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d) := by
  have h4 : ∀ y : Fin d → ℝ, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ y)) (4 : ENNReal)
      (gaussianRowMeasure d) := fun y => by
    simpa using memLp_gaussianRow_comp_of_linear_growth φ hφ hA hB hgrow y (d := d) 4
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul]
    have : (4 : ENNReal) = 2 * 2 := by norm_num
    rw [this, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]⟩
  exact MemLp.mul (r := 2) (h4 x') (h4 x)
/-! ### Entrywise (max) concentration for readout weights

`prob_gaussianReadout_sum_sq_le` above bounds the readout *energy* `n⁻¹ ∑ᵢ aᵢ²` (an average),
via Markov's inequality, giving a tail bound whose natural scale is `O(√(n/δ))`. Gap 4
(`NetworkParam.lean`'s `outputJacobian_netFromParams_frobenius_sub_le`) instead needs a uniform
bound on every *individual* `|aᵢ|`. Bounding this the same crude way (Markov on each `aᵢ²`
plus a union bound) would give `R = O(√(n/δ))` too - and since Gap 4's `L_J` is linear in `R`,
an `R` that grows like `√n` would make `L_J = Θ(1)`, silently breaking the "kernel freezes as
`n → ∞`" conclusion the whole plan is aimed at (see `docs/NTK_lazy_training_gap_closure_plan.md`
§3.1). The fix is to use the actual Gaussian tail (Chernoff/sub-Gaussian) instead of Markov,
which gives the much better `R = O(√(log(n/δ)))` - logarithmic, not polynomial, in the width. -/

/-- The standard Gaussian has a sub-Gaussian moment-generating function with parameter `1`. -/
lemma hasSubgaussianMGF_id_gaussianReal_zero_one :
    ProbabilityTheory.HasSubgaussianMGF id (1 : NNReal) (gaussianReal 0 1) where
  integrable_exp_mul := integrable_exp_mul_gaussianReal
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

/-- Negating a standard Gaussian is still sub-Gaussian with the same parameter (used for the
two-sided/absolute-value tail bound below). -/
lemma hasSubgaussianMGF_neg_id_gaussianReal_zero_one :
    ProbabilityTheory.HasSubgaussianMGF (fun x => -x) (1 : NNReal) (gaussianReal 0 1) where
  integrable_exp_mul t := by
    have := integrable_exp_mul_gaussianReal (μ := (0:ℝ)) (v := (1:NNReal)) (-t)
    simpa [mul_comm, mul_neg] using this
  mgf_le t := by
    have h := hasSubgaussianMGF_id_gaussianReal_zero_one.mgf_le (-t)
    unfold mgf at *
    simp only [id] at h ⊢
    convert h using 2
    · ext x; ring_nf
    · ring

/-- Two-sided Chernoff tail bound for a standard Gaussian: `P(|X| ≥ ε) ≤ 2 exp(-ε²/2)`. -/
lemma prob_abs_gaussianReal_ge_le (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1).real {x : ℝ | ε ≤ |x|} ≤ 2 * Real.exp (-ε ^ 2 / 2) := by
  have hset : {x : ℝ | ε ≤ |x|} = {x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  have h1 := hasSubgaussianMGF_id_gaussianReal_zero_one.measure_ge_le hε
  have h2 := hasSubgaussianMGF_neg_id_gaussianReal_zero_one.measure_ge_le hε
  simp only [id] at h1
  have hle := measureReal_union_le (μ := gaussianReal 0 1) {x : ℝ | ε ≤ x} {x : ℝ | ε ≤ -x}
  have hcalc : Real.exp (-ε ^ 2 / (2 * (1:NNReal))) = Real.exp (-ε ^ 2 / 2) := by norm_num
  rw [hcalc] at h1 h2
  calc
    (gaussianReal 0 1).real ({x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x}) ≤
        (gaussianReal 0 1).real {x : ℝ | ε ≤ x} + (gaussianReal 0 1).real {x : ℝ | ε ≤ -x} := hle
    _ ≤ Real.exp (-ε ^ 2 / 2) + Real.exp (-ε ^ 2 / 2) := add_le_add h1 h2
    _ = 2 * Real.exp (-ε ^ 2 / 2) := by ring

/-- Transport the two-sided tail bound to a single readout coordinate `a i`. -/
lemma prob_abs_gaussianReadout_coord_ge_le (n : ℕ) (i : Fin n) (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ε ≤ |a i|} ≤ 2 * Real.exp (-ε ^ 2 / 2) := by
  have hmap : Measure.map (fun a : Fin n → ℝ => a i) (gaussianReadoutMeasure n) =
      gaussianReal 0 1 := map_gaussianReadoutMeasure_coord i
  have hpre : {a : Fin n → ℝ | ε ≤ |a i|} =
      (fun a : Fin n → ℝ => a i) ⁻¹' {x : ℝ | ε ≤ |x|} := rfl
  have hms : MeasurableSet {x : ℝ | ε ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hkey : (gaussianReadoutMeasure n).real
      ((fun a : Fin n → ℝ => a i) ⁻¹' {x : ℝ | ε ≤ |x|}) =
      (gaussianReal 0 1).real {x : ℝ | ε ≤ |x|} := by
    unfold MeasureTheory.Measure.real
    rw [← Measure.map_apply (measurable_pi_apply i) hms, hmap]
  rw [hpre, hkey]
  exact prob_abs_gaussianReal_ge_le ε hε

/-- Union bound over all `n` readout coordinates: the probability that *some* coordinate exceeds
`ε` in absolute value is at most `2n` times the single-coordinate tail bound. -/
theorem prob_max_abs_gaussianReadout_ge_le (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} ≤
      2 * (n : ℝ) * Real.exp (-ε ^ 2 / 2) := by
  have heq : {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} = ⋃ i : Fin n, {a : Fin n → ℝ | ε ≤ |a i|} := by
    ext a; simp
  rw [heq]
  calc
    (gaussianReadoutMeasure n).real (⋃ i : Fin n, {a : Fin n → ℝ | ε ≤ |a i|}) ≤
        ∑ i : Fin n, (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ε ≤ |a i|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2 * Real.exp (-ε ^ 2 / 2) :=
      Finset.sum_le_sum (fun i _ => prob_abs_gaussianReadout_coord_ge_le n i ε hε)
    _ = 2 * (n : ℝ) * Real.exp (-ε ^ 2 / 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- **Gap 4b deliverable.** With probability `≥ 1 - δ`, every readout weight `a i` has
`|a i| ≤ √(2 log(2n/δ))` - a bound that grows only **logarithmically** in the width `n`. -/
theorem prob_forall_abs_gaussianReadout_le (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (gaussianReadoutMeasure n).real
      {a : Fin n → ℝ | ∀ i, |a i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} ≥ 1 - δ := by
  set ε : ℝ := Real.sqrt (2 * Real.log (2 * n / δ)) with hε_def
  have hnδ_pos : 0 < 2 * (n : ℝ) / δ := by positivity
  have hε_nonneg : 0 ≤ ε := Real.sqrt_nonneg _
  have hbad := prob_max_abs_gaussianReadout_ge_le n ε hε_nonneg
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hlog_nonneg : 0 ≤ Real.log (2 * (n:ℝ) / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    nlinarith
  have hε_sq : ε ^ 2 = 2 * Real.log (2 * (n:ℝ) / δ) := by
    rw [hε_def, Real.sq_sqrt (by positivity)]
  have hexp : Real.exp (-ε ^ 2 / 2) = δ / (2 * n) := by
    rw [hε_sq]
    rw [show -(2 * Real.log (2 * (n:ℝ) / δ)) / 2 = -Real.log (2 * (n:ℝ) / δ) by ring]
    rw [Real.exp_neg, Real.exp_log hnδ_pos]
    rw [inv_div]
  rw [hexp] at hbad
  have hrhs : 2 * (n:ℝ) * (δ / (2 * (n:ℝ))) = δ := by field_simp
  rw [hrhs] at hbad
  have hcompl : {a : Fin n → ℝ | ∀ i, |a i| ≤ ε} = {a : Fin n → ℝ | ∃ i, ε < |a i|} ᶜ := by
    ext a
    simp [not_exists, not_lt]
  rw [hcompl]
  have hsub : {a : Fin n → ℝ | ∃ i, ε < |a i|} ⊆ {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} :=
    fun a ⟨i, hi⟩ => ⟨i, hi.le⟩
  have hle := measureReal_mono (μ := gaussianReadoutMeasure n) hsub
  have hbad' : (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ∃ i, ε < |a i|} ≤ δ :=
    hle.trans hbad
  have hcompl_ge : (gaussianReadoutMeasure n).real ({a : Fin n → ℝ | ∃ i, ε < |a i|} ᶜ) ≥
      1 - δ := by
    have hUn : {a : Fin n → ℝ | ∃ i, ε < |a i|} = ⋃ i : Fin n, {a : Fin n → ℝ | ε < |a i|} := by
      ext a; simp
    have hmeas : MeasurableSet {a : Fin n → ℝ | ∃ i, ε < |a i|} := by
      rw [hUn]
      exact MeasurableSet.iUnion (fun i => measurableSet_lt measurable_const
        (continuous_abs.measurable.comp (measurable_pi_apply i)))
    have := probReal_compl_eq_one_sub (μ := gaussianReadoutMeasure n)
      (s := {a : Fin n → ℝ | ∃ i, ε < |a i|}) hmeas
    rw [ge_iff_le, this]
    linarith
  exact hcompl_ge

/-- **Generic, reusable union-bound-for-complements.** Two events each of probability `≥ 1 - δ`
on the same probability measure intersect in an event of probability `≥ 1 - δ₁ - δ₂`. Used by
Phase 6 (`NetworkParam.lean`) to combine Gap 3's Jacobian-norm event with Gap 4b's
entrywise-readout event, but stated with no reference to the NTK setup so it can be reused for
any future combination of independent high-probability events. -/
theorem measureReal_inter_ge_of_ge {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {δ₁ δ₂ : ℝ} (hA' : μ.real A ≥ 1 - δ₁) (hB' : μ.real B ≥ 1 - δ₂) :
    μ.real (A ∩ B) ≥ 1 - δ₁ - δ₂ := by
  have hcompl : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := Set.compl_inter A B
  have h1 : μ.real ((A ∩ B)ᶜ) = 1 - μ.real (A ∩ B) := probReal_compl_eq_one_sub (hA.inter hB)
  have h2 : μ.real (Aᶜ ∪ Bᶜ) ≤ μ.real Aᶜ + μ.real Bᶜ := measureReal_union_le Aᶜ Bᶜ
  have h3 : μ.real Aᶜ = 1 - μ.real A := probReal_compl_eq_one_sub hA
  have h4 : μ.real Bᶜ = 1 - μ.real B := probReal_compl_eq_one_sub hB
  rw [hcompl] at h1
  linarith [h1, h2, h3, h4]

/-- The complement of an intersection has measure at most the sum of the complements' measures.
No measurability is needed. -/
theorem measureReal_compl_inter_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) :
    μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
  rw [Set.compl_inter]
  exact measureReal_union_le _ _

/-- On a probability measure, `1 - μ Sᶜ ≤ μ S` for an arbitrary (possibly non-measurable) `S`. -/
theorem one_sub_le_measureReal_of_measureReal_compl_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {S : Set α} {c : ℝ} (h : μ.real Sᶜ ≤ c) :
    1 - c ≤ μ.real S := by
  have h1 := measureReal_union_le (μ := μ) S Sᶜ
  rw [Set.union_compl_self] at h1
  have h2 : μ.real Set.univ = 1 := by simp
  linarith

/-- Lift Gap 4b's readout-only event to the full initialization product measure
`initMeasure n d = (gaussianInit n d).prod (gaussianReadoutMeasure n)`. -/
lemma initMeasure_forall_abs_readout_ge (n d : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (initMeasure n d).real
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} ≥ 1 - δ := by
  have hset : {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} =
      Set.univ ×ˢ {a : Fin n → ℝ | ∀ i, |a i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} := by
    ext p; simp
  rw [hset, initMeasure, MeasureTheory.measureReal_prod_prod]
  simpa using prob_forall_abs_gaussianReadout_le n hn hδ hδ1

/-- Readout weights `a_i` are mutually independent across hidden units `i ∈ Fin n`. -/
lemma iIndepFun_readoutWeights (n : ℕ) :
    iIndepFun (fun i : Fin n => fun a : Fin n → ℝ => a i) (gaussianReadoutMeasure n) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Input weight rows `W_i` have marginal standard Gaussian row distribution `𝒩(0, Iᵈ)`. -/
lemma map_gaussianInit_row (i : Fin n) :
    Measure.map (fun W : Fin n → Fin d → ℝ => W i) (gaussianInit n d) = gaussianRowMeasure d :=
  (MeasureTheory.measurePreserving_eval (fun _ : Fin n => gaussianRowMeasure d) i).map_eq

/-- Input weight rows `W_i` are mutually independent across hidden unit indices `i ∈ Fin n`. -/
lemma iIndepFun_inputWeights (n d : ℕ) :
    iIndepFun (fun i : Fin n => fun W : Fin n → Fin d → ℝ => W i) (gaussianInit n d) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Mutual Independence: the family of input weights `W` is independent of readout weights `a`. -/
lemma indepFun_input_readout (n d : ℕ) :
    IndepFun (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1)
      (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2)
      (initMeasure n d) :=
  indepFun_prod measurable_id measurable_id

end Preliminaries

section GaussianVectorAlgebra

/-! ## Gaussian Vector Algebra (Propositions 2.8-2.10) -/

/-- The real inner product on any finite-dimensional `EuclideanSpace` is the `dotProduct` of the
underlying coordinate functions. -/
lemma inner_eq_dotProduct_ofLp {γ : Type*} [Fintype γ] (a b : EuclideanSpace ℝ γ) :
    ⟪a, b⟫ = a.ofLp ⬝ᵥ b.ofLp := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial, dotProduct]

/-- **Proposition 2.8 (Linear Transformations of Gaussian Vectors)**:
If `g ~ 𝒩(μ, S)` on `EuclideanSpace ℝ ι` and `A` is a deterministic `κ × ι` matrix, then the
linear image `A g` is again Gaussian: `A g ~ 𝒩(A μ, A S Aᵀ)`. -/
theorem gaussian_map_mulVec {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (A : Matrix κ ι ℝ) :
    Measure.map (fun x : EuclideanSpace ℝ ι => WithLp.toLp 2 (A *ᵥ x.ofLp))
        (multivariateGaussian μ S) =
      multivariateGaussian (WithLp.toLp 2 (A *ᵥ μ.ofLp)) (A * S * Aᵀ) := by
  have hAST : (A * S * Aᵀ).PosSemidef := by simpa using hS.mul_mul_conjTranspose_same A
  set F := fun x : EuclideanSpace ℝ ι => WithLp.toLp 2 (A *ᵥ x.ofLp) with hF_def
  have hF_cont : Continuous F :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (PiLp.continuous_apply 2 _ j))
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map hF_cont.measurable.aemeasurable (by fun_prop)]
  have h_inner : ∀ x : EuclideanSpace ℝ ι, ⟪F x, t⟫ = x.ofLp ⬝ᵥ (Aᵀ *ᵥ t.ofLp) := by
    intro x
    rw [real_inner_comm, inner_eq_dotProduct_ofLp]
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  simp_rw [h_inner]
  have h_as_charFun : (∫ x : EuclideanSpace ℝ ι,
      Complex.exp ((x.ofLp ⬝ᵥ (Aᵀ *ᵥ t.ofLp) : ℝ) * Complex.I) ∂(multivariateGaussian μ S)) =
      charFun (multivariateGaussian μ S) (WithLp.toLp 2 (Aᵀ *ᵥ t.ofLp)) := by
    rw [charFun_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [inner_eq_dotProduct_ofLp]
  rw [h_as_charFun, charFun_multivariateGaussian hS, charFun_multivariateGaussian hAST]
  have h_mean : ⟪(WithLp.toLp 2 (Aᵀ *ᵥ t.ofLp) : EuclideanSpace ℝ ι), μ⟫ =
      ⟪t, (WithLp.toLp 2 (A *ᵥ μ.ofLp) : EuclideanSpace ℝ κ)⟫ := by
    rw [inner_eq_dotProduct_ofLp, inner_eq_dotProduct_ofLp]
    conv_rhs => rw [dotProduct_mulVec, ← mulVec_transpose]
  have h_quad : (Aᵀ *ᵥ t.ofLp) ⬝ᵥ S *ᵥ (Aᵀ *ᵥ t.ofLp) = t.ofLp ⬝ᵥ (A * S * Aᵀ) *ᵥ t.ofLp := by
    conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [h_mean, h_quad]

/-- **Proposition 2.9 (Inner Products with a Standard Gaussian Vector)**:
For `g ~ 𝒩(0, I_n)` (`gaussianReadoutMeasure n`) and fixed deterministic vectors `u v : Fin n → ℝ`,
the joint law of the pair of projections `(⟪g,u⟫, ⟪g,v⟫) = (g ⬝ᵥ u, g ⬝ᵥ v)` is the bivariate
Gaussian with covariance matrix `!![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v]`. -/
theorem stdGaussian_inner_pair (n : ℕ) (u v : Fin n → ℝ) :
    Measure.map (fun a : Fin n → ℝ => WithLp.toLp 2 (![a ⬝ᵥ u, a ⬝ᵥ v] : Fin 2 → ℝ))
        (gaussianReadoutMeasure n) =
      multivariateGaussian 0 !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] := by
  set A : Matrix (Fin 2) (Fin n) ℝ := Matrix.of ![u, v] with hA_def
  have hA_mulVec : ∀ a : Fin n → ℝ, A *ᵥ a = ![a ⬝ᵥ u, a ⬝ᵥ v] := by
    intro a
    ext i
    fin_cases i <;> simp [A, mulVec, dotProduct, mul_comm]
  have hF_eq : (fun a : Fin n → ℝ => WithLp.toLp 2 (![a ⬝ᵥ u, a ⬝ᵥ v] : Fin 2 → ℝ)) =
      (fun x : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (A *ᵥ x.ofLp)) ∘ (WithLp.toLp 2) := by
    ext a
    simp [hA_mulVec]
  have hSpos : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h_map := gaussian_map_mulVec (0 : EuclideanSpace ℝ (Fin n)) 1 hSpos A
  rw [hF_eq, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h_toLp : Measure.map (WithLp.toLp 2) (gaussianReadoutMeasure n) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [map_pi_eq_stdGaussian, multivariateGaussian_zero_one]
  rw [h_toLp, h_map]
  have h_mean0 : A *ᵥ (0 : EuclideanSpace ℝ (Fin n)).ofLp = (0 : Fin 2 → ℝ) := by simp
  have h_cov : A * (1 : Matrix (Fin n) (Fin n) ℝ) * Aᵀ =
      !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] := by
    rw [Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mul_comm]
  rw [h_mean0, h_cov]
  simp

/-- **Proposition 2.10 (Matrix-Vector Multiplication by a Gaussian Matrix)**:
For `W : Fin n → Fin n → ℝ` with i.i.d. standard Gaussian entries (`gaussianInit n n`) and fixed
deterministic vectors `u v : Fin n → ℝ`, the joint law of the row-indexed pairs
`i ↦ (W i ⬝ᵥ u, W i ⬝ᵥ v) = i ↦ ((W *ᵥ u) i, (W *ᵥ v) i)` consists of `n` i.i.d. copies of the
bivariate Gaussian from Proposition 2.9, i.e. the block/Kronecker-structured covariance
`!![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] ⊗ Iₙ`. -/
theorem gaussianMatrix_mulVec_pair (n : ℕ) (u v : Fin n → ℝ) :
    Measure.map
      (fun W : Fin n → Fin n → ℝ =>
        fun i : Fin n => WithLp.toLp 2 (![W i ⬝ᵥ u, W i ⬝ᵥ v] : Fin 2 → ℝ))
      (gaussianInit n n) =
      Measure.pi (fun _ : Fin n => multivariateGaussian 0 !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v]) := by
  have h_init_eq : gaussianInit n n = Measure.pi (fun _ : Fin n => gaussianReadoutMeasure n) := rfl
  set f := fun a : Fin n → ℝ => WithLp.toLp 2 (![a ⬝ᵥ u, a ⬝ᵥ v] : Fin 2 → ℝ) with hf_def
  have hf_cont : Continuous f := by
    apply (PiLp.continuous_toLp 2 _).comp
    refine continuous_pi fun k => ?_
    fin_cases k <;> fun_prop
  have hf_meas : Measurable f := hf_cont.measurable
  have hσ : ∀ i : Fin n, SigmaFinite ((gaussianReadoutMeasure n).map f) := fun i => by
    rw [hf_def, stdGaussian_inner_pair]; infer_instance
  rw [h_init_eq, Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReadoutMeasure n)
    (f := fun _ : Fin n => f) (fun _ => hf_meas.aemeasurable)]
  congr 1
  funext i
  exact stdGaussian_inner_pair n u v

/-- **Proposition 2.9' (Inner Products with a Standard Gaussian Vector, `Fin m`-Family)**:
The `Fin m`-indexed generalization of Proposition 2.9 (`stdGaussian_inner_pair`) from a fixed pair
of vectors to a fixed family `u : Fin m → Fin n → ℝ`. For `g ~ 𝒩(0, I_n)` and fixed deterministic
vectors `u α`, the joint law of the projections `α ↦ ⟪g, u α⟫ = g ⬝ᵥ u α` is the `m`-variate
Gaussian with covariance matrix `(α, β) ↦ u α ⬝ᵥ u β`. -/
theorem stdGaussian_inner_family (n m : ℕ) (u : Fin m → Fin n → ℝ) :
    Measure.map (fun a : Fin n → ℝ => WithLp.toLp 2 (fun α : Fin m => a ⬝ᵥ u α))
        (gaussianReadoutMeasure n) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β) := by
  set A : Matrix (Fin m) (Fin n) ℝ := Matrix.of u with hA_def
  have hA_mulVec : ∀ a : Fin n → ℝ, A *ᵥ a = fun α => a ⬝ᵥ u α := by
    intro a
    ext α
    simp [A, mulVec, dotProduct, mul_comm]
  have hF_eq : (fun a : Fin n → ℝ => WithLp.toLp 2 (fun α : Fin m => a ⬝ᵥ u α)) =
      (fun x : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (A *ᵥ x.ofLp)) ∘ (WithLp.toLp 2) := by
    ext a
    simp [hA_mulVec]
  have hSpos : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h_map := gaussian_map_mulVec (0 : EuclideanSpace ℝ (Fin n)) 1 hSpos A
  rw [hF_eq, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h_toLp : Measure.map (WithLp.toLp 2) (gaussianReadoutMeasure n) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [map_pi_eq_stdGaussian, multivariateGaussian_zero_one]
  rw [h_toLp, h_map]
  have h_mean0 : A *ᵥ (0 : EuclideanSpace ℝ (Fin n)).ofLp = (0 : Fin m → ℝ) := by simp
  have h_cov : A * (1 : Matrix (Fin n) (Fin n) ℝ) * Aᵀ =
      (Matrix.of fun α β => u α ⬝ᵥ u β) := by
    rw [Matrix.mul_one]
    ext α β
    simp [A, Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  rw [h_mean0, h_cov]
  simp

/-- **Proposition 2.10' (Matrix-Vector Multiplication by a Gaussian Matrix, `Fin m`-Family)**:
The `Fin m`-indexed generalization of Proposition 2.10 (`gaussianMatrix_mulVec_pair`) from a fixed
pair of vectors to a fixed family `u : Fin m → Fin n → ℝ`. For `W : Fin r → Fin n → ℝ` with i.i.d.
standard Gaussian rows (`gaussianInit r n`), the row-indexed family
`i ↦ (α ↦ W i ⬝ᵥ u α) : Fin r → EuclideanSpace ℝ (Fin m)` consists of `r` i.i.d. copies of
Proposition 2.9''s `m`-variate Gaussian with covariance `(α, β) ↦ u α ⬝ᵥ u β`. -/
theorem gaussianMatrix_mulVec_family (n r m : ℕ) (u : Fin m → Fin n → ℝ) :
    Measure.map
      (fun W : Fin r → Fin n → ℝ =>
        fun i : Fin r => WithLp.toLp 2 (fun α : Fin m => W i ⬝ᵥ u α))
      (gaussianInit r n) =
      Measure.pi (fun _ : Fin r =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β)) := by
  have h_init_eq : gaussianInit r n = Measure.pi (fun _ : Fin r => gaussianReadoutMeasure n) := rfl
  set f := fun a : Fin n → ℝ => WithLp.toLp 2 (fun α : Fin m => a ⬝ᵥ u α) with hf_def
  have hf_cont : Continuous f :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => by fun_prop)
  have hf_meas : Measurable f := hf_cont.measurable
  have hσ : ∀ i : Fin r, SigmaFinite ((gaussianReadoutMeasure n).map f) := fun i => by
    rw [hf_def, stdGaussian_inner_family]; infer_instance
  rw [h_init_eq, Measure.pi_map_pi (μ := fun _ : Fin r => gaussianReadoutMeasure n)
    (f := fun _ : Fin r => f) (fun _ => hf_meas.aemeasurable)]
  congr 1
  funext i
  exact stdGaussian_inner_family n m u

end GaussianVectorAlgebra

section Theorem1

/-! ## Theorem 1: Exact Finite-Width Conditional Normality -/

/-! ### Step 1 & Step 2: Linear Projections and Projection Coefficients -/

/-- The $\mathcal{F}$-measurable projection coefficients `projectionCoeff` (mathematically `ψ_i`)
for each hidden unit `i`:
  `projectionCoeff n φ W X c i = (1/√n) ∑_α c_α φ(W i ⬝ᵥ X α)`. -/
noncomputable def projectionCoeff
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (c : Fin m → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹.sqrt * ∑ α : Fin m, c α * φ (W i ⬝ᵥ X α)

/-- The normalized-sum formula for a projection coefficient. This is the public
equation lemma for `projectionCoeff`, so proofs need not unfold its implementation. -/
lemma projectionCoeff_eq_normalized_sum
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (c : Fin m → ℝ) (i : Fin n) :
    projectionCoeff n φ W X c i = (n : ℝ)⁻¹.sqrt * ∑ α : Fin m, c α * φ (W i ⬝ᵥ X α) := rfl

/-- For measurable `φ`, each projection coefficient is measurable as a function of the input
weight matrix. This formalizes the `ℱ`-measurability assertion in Step 2. -/
lemma projectionCoeff_measurable
    (n : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (c : Fin m → ℝ) (i : Fin n) :
    Measurable (fun W : Fin n → Fin d → ℝ => projectionCoeff n φ W X c i) := by
  simp_rw [projectionCoeff_eq_normalized_sum]
  refine Measurable.const_mul (Finset.measurable_sum _ fun α _ => ?_) _
  exact measurable_const.mul
    (hφ.comp ((measurable_dotProduct_left (X α)).comp (measurable_pi_apply i)))

/-- **Step 1 (Linear projection identity)**:
For any linear combination vector `c : Fin m → ℝ`, the scalar linear projection of
the network output satisfies:
  `∑ α, c α * f(X α; W, a) = ∑ i, a i * projectionCoeff n φ W X c i`. -/
lemma projection_eq_sum_projectionCoeff
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (X : Fin m → Fin d → ℝ) (c : Fin m → ℝ) :
    (∑ α : Fin m, c α * evalSingle φ W a (X α)) =
      ∑ i : Fin n, a i * projectionCoeff n φ W X c i :=
  calc
    (∑ α : Fin m, c α * evalSingle φ W a (X α)) =
        ∑ α : Fin m, c α * ((n : ℝ)⁻¹.sqrt *
          ∑ i : Fin n, a i * φ (W i ⬝ᵥ X α)) := by
      simp_rw [evalSingle_eq_normalized_sum]
    _ = ∑ i : Fin n, a i * ((n : ℝ)⁻¹.sqrt *
          ∑ α : Fin m, c α * φ (W i ⬝ᵥ X α)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring
    _ = ∑ i : Fin n, a i * projectionCoeff n φ W X c i := by
      simp_rw [projectionCoeff_eq_normalized_sum]

/-! ### Step 4: Variance and Positive Semidefiniteness -/

/-- The square of a projection coefficient expanded as a double sum. -/
lemma projectionCoeff_sq (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ)
    (X : Fin m → Fin d → ℝ) (c : Fin m → ℝ) (i : Fin n) :
    (projectionCoeff n φ W X c i) ^ 2 =
      (n : ℝ)⁻¹ * ∑ α : Fin m, ∑ β : Fin m,
        c α * c β * (φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β)) :=
  calc
    (projectionCoeff n φ W X c i) ^ 2 =
        ((n : ℝ)⁻¹.sqrt * ∑ α : Fin m, c α * φ (W i ⬝ᵥ X α)) ^ 2 := by
      rw [projectionCoeff_eq_normalized_sum]
    _ = (n : ℝ)⁻¹ * (∑ α : Fin m, c α * φ (W i ⬝ᵥ X α)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    _ = (n : ℝ)⁻¹ * ∑ α : Fin m, ∑ β : Fin m,
        c α * c β * (φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β)) := by
      congr 1
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

/-- **Step 4 (Variance identity)**:
The sum of squared coefficients `∑ i, (projectionCoeff ... i)^2` equals the quadratic form
`c ⬝ᵥ Φ^{(n)} *ᵥ c`:
  `∑ i, (projectionCoeff n φ W X c i)^2 = c ⬝ᵥ Φ^{(n)} *ᵥ c`. -/
lemma sum_projectionCoeff_sq_eq_bilin
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (c : Fin m → ℝ) :
    ∑ i : Fin n, (projectionCoeff n φ W X c i) ^ 2 =
      c ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ c := by
  simp_rw [projectionCoeff_sq]
  simp only [dotProduct, mulVec, empiricalCovariance]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  calc
    (∑ i : Fin n, (n : ℝ)⁻¹ *
        (c α * c β * (φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β)))) =
        ∑ i : Fin n, c α * ((n : ℝ)⁻¹ * (φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β))) * c β :=
      Finset.sum_congr rfl fun i _ => by ring
    _ = c α * ((∑ i : Fin n, (n : ℝ)⁻¹ *
        (φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β))) * c β) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- The empirical covariance matrix `Φ^{(n)}` is symmetric (Hermitian). -/
lemma empiricalCovariance_isHermitian
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    (empiricalCovariance n φ W X).IsHermitian := by
  ext α β
  simp only [empiricalCovariance, conjTranspose_apply, star_trivial]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The quadratic form with `Φ^{(n)}` is always nonnegative. -/
lemma empiricalCovariance_nonneg
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (c : Fin m → ℝ) :
    0 ≤ c ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ c := by
  rw [← sum_projectionCoeff_sq_eq_bilin]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (projectionCoeff n φ W X c i))

/-- The empirical covariance matrix `Φ^{(n)}` is positive semidefinite (`PosSemidef`). -/
theorem empiricalCovariance_posSemidef
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    (empiricalCovariance n φ W X).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (empiricalCovariance_isHermitian n φ W X)
    fun x => by simpa using empiricalCovariance_nonneg n φ W X x

/-! ### Step 3, 4 & 5: Conditional Distribution and Theorem 1 -/

/-- Pushforward of the readout measure under standard inner product with a vector `v : Fin n → ℝ`
is a 1D Gaussian with mean 0 and variance `∑ i, v i ^ 2`. -/
lemma map_gaussianReadoutMeasure_inner (v : Fin n → ℝ) :
    Measure.map (fun a : Fin n → ℝ => ∑ i : Fin n, a i * v i) (gaussianReadoutMeasure n) =
      gaussianReal 0 (Real.toNNReal (∑ i : Fin n, v i ^ 2)) := by
  have h_eq : (fun a : Fin n → ℝ => ∑ i : Fin n, a i * v i) =
      (fun (u : EuclideanSpace ℝ (Fin n)) => innerSL ℝ (WithLp.toLp 2 v) u) ∘ (WithLp.toLp 2) := by
    ext a
    dsimp [innerSL_apply_apply]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  rw [h_eq, ← Measure.map_map]
  · have h_toLp : Measure.map (WithLp.toLp 2) (gaussianReadoutMeasure n) =
        stdGaussian (EuclideanSpace ℝ (Fin n)) := map_pi_eq_stdGaussian
    rw [h_toLp]
    have h_map := IsGaussian.map_eq_gaussianReal
      (μ := stdGaussian (EuclideanSpace ℝ (Fin n))) (innerSL ℝ (WithLp.toLp 2 v))
    rw [h_map]
    have h_mean : ∫ (u : EuclideanSpace ℝ (Fin n)),
        (innerSL ℝ (WithLp.toLp 2 v)) u ∂stdGaussian (EuclideanSpace ℝ (Fin n)) = 0 := by
      rw [(innerSL ℝ (WithLp.toLp 2 v)).integral_comp_id_comm IsGaussian.integrable_id,
        integral_id_stdGaussian]
      exact map_zero (innerSL ℝ (WithLp.toLp 2 v))
    have h_var : Var[innerSL ℝ (WithLp.toLp 2 v); stdGaussian (EuclideanSpace ℝ (Fin n))] =
        ∑ i : Fin n, v i ^ 2 := by
      rw [variance_dual_stdGaussian, innerSL_apply_norm]
      simp only [EuclideanSpace.real_norm_sq_eq]
    rw [h_mean, h_var]
  all_goals fun_prop

/-- **Step 4 (Exact 1D Conditional Normality)**:
Conditional on `W`, every scalar linear projection `∑ α, c α * f(X α; W, a)` is distributed
as a univariate centered Gaussian with variance `c ⬝ᵥ Φ^{(n)} *ᵥ c`. -/
theorem map_readout_projection_eq_gaussianReal
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) (c : Fin m → ℝ) :
    Measure.map (fun a => ∑ α : Fin m, c α * evalSingle φ W a (X α)) (gaussianReadoutMeasure n) =
      gaussianReal 0 (Real.toNNReal (c ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ c)) := by
  calc
    Measure.map (fun a => ∑ α : Fin m, c α * evalSingle φ W a (X α))
        (gaussianReadoutMeasure n) =
        Measure.map (fun a => ∑ i : Fin n, a i * projectionCoeff n φ W X c i)
          (gaussianReadoutMeasure n) := by
      congr 1
      funext a
      exact projection_eq_sum_projectionCoeff φ W a X c
    _ = gaussianReal 0 (Real.toNNReal (∑ i : Fin n, (projectionCoeff n φ W X c i) ^ 2)) :=
      map_gaussianReadoutMeasure_inner (projectionCoeff n φ W X c)
    _ = gaussianReal 0 (Real.toNNReal (c ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ c)) := by
      rw [sum_projectionCoeff_sq_eq_bilin]

/-- Pushforward under inner product with `t` yields a 1D Gaussian with variance
`t.ofLp ⬝ᵥ Φ^{(n)} *ᵥ t.ofLp`. -/
lemma map_readout_inner_evalVector
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Measure.map (fun a => ⟪t, evalVector φ W a X⟫) (gaussianReadoutMeasure n) =
      gaussianReal 0 (Real.toNNReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp)) := by
  calc
    Measure.map (fun a => ⟪t, evalVector φ W a X⟫) (gaussianReadoutMeasure n) =
        Measure.map (fun a => ∑ α : Fin m, t.ofLp α * evalSingle φ W a (X α))
          (gaussianReadoutMeasure n) := by
      congr 1
      funext a
      exact evalVector_inner φ W X a t
    _ = gaussianReal 0
        (Real.toNNReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp)) :=
      map_readout_projection_eq_gaussianReal φ W X t.ofLp

/-- The characteristic function of `evalVector` under `gaussianReadoutMeasure n`. -/
lemma charFun_readout_evalVector
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun (Measure.map (fun a => evalVector φ W a X) (gaussianReadoutMeasure n)) t =
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2) := by
  set μ := Measure.map (fun a => evalVector φ W a X) (gaussianReadoutMeasure n)
  rw [charFun_apply]
  rw [integral_map (evalVector_measurable φ W X).aemeasurable (by fun_prop)]
  have h_exp : (fun a => Complex.exp (⟪evalVector φ W a X, t⟫ * Complex.I)) =
      (fun a => Complex.exp (⟪t, evalVector φ W a X⟫ * Complex.I)) := by
    ext a
    congr 1
    rw [real_inner_comm]
  rw [h_exp]
  have h_meas_inner : Measurable (fun a => ⟪t, evalVector φ W a X⟫) :=
    inner_evalVector_measurable φ W X t
  have h_int_map : (∫ a, Complex.exp (⟪t, evalVector φ W a X⟫ * Complex.I) ∂gaussianReadoutMeasure n) =
      ∫ y : ℝ, Complex.exp (y * Complex.I) ∂Measure.map (fun a => ⟪t, evalVector φ W a X⟫) (gaussianReadoutMeasure n) := by
    rw [integral_map h_meas_inner.aemeasurable (by fun_prop)]
  rw [h_int_map, map_readout_inner_evalVector φ W X t]
  have h_cf_1 : (∫ y : ℝ, Complex.exp (y * Complex.I) ∂(gaussianReal 0 (Real.toNNReal (t.ofLp ⬝ᵥ empiricalCovariance n φ W X *ᵥ t.ofLp)))) =
      charFun (gaussianReal 0 (Real.toNNReal (t.ofLp ⬝ᵥ empiricalCovariance n φ W X *ᵥ t.ofLp))) 1 := by
    rw [charFun_apply_real]
    simp
  rw [h_cf_1, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.ofReal_one, mul_one, one_pow, zero_sub]
  have h_nonneg : 0 ≤ t.ofLp ⬝ᵥ empiricalCovariance n φ W X *ᵥ t.ofLp :=
    empiricalCovariance_nonneg n φ W X t.ofLp
  rw [Real.coe_toNNReal _ h_nonneg]
  congr 1
  rw [neg_div]



end Theorem1

section Theorem2

/-! ## Theorem 2: Asymptotic Kernel Convergence and the NNGP Limit -/

/-! ### Step 1: Summand Measurability -/

/-- Step 1 (Measurability): For measurable `φ`, the product `w ↦ φ(w ⬝ᵥ x) * φ(w ⬝ᵥ x')` is measurable. -/
lemma measurable_cov_summand (φ : ℝ → ℝ) (hφ : Measurable φ) (x x' : Fin d → ℝ) :
    Measurable (fun w : Fin d → ℝ => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) :=
  (hφ.comp (measurable_dotProduct_left x)).mul (hφ.comp (measurable_dotProduct_left x'))

/-! ### Step 3: Integrability via Cauchy-Schwarz -/

/-- Step 3 (Integrability via Cauchy-Schwarz): If `φ(· ⬝ᵥ x)` and `φ(· ⬝ᵥ x')` are square-integrable
under the Gaussian row measure, their product is integrable. -/
lemma integrable_cov_summand_of_memLp
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hx : MemLp (fun w => φ (w ⬝ᵥ x)) 2 (gaussianRowMeasure d))
    (hx' : MemLp (fun w => φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d)) :
    Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (gaussianRowMeasure d) :=
  hx.integrable_mul hx'

/-! ### Step 2 & Step 4: SLLN Convergence (Entrywise and Full Matrix) -/

/-- **Theorem 2 (Entrywise SLLN for the Covariance Tensor)**:
As width `n → ∞`, each entry of the empirical covariance matrix converges almost surely to the
deterministic limiting NNGP expectation:
  `Φ^{(n), α β} →_as 𝔼_{w ~ 𝒩(0, I_d)}[φ(w ⬝ᵥ X α) φ(w ⬝ᵥ X β)]`.

**Proof (4 Steps)**:
* Step 1: For fixed inputs `X α, X β`, define the summands `Y_i(rows) := φ(rows i ⬝ᵥ X α) φ(rows i ⬝ᵥ X β)`.
* Step 2: Because `rows` are i.i.d. under the infinite product measure `μ`, `{Y_i}` is i.i.d.
* Step 3: By square-integrability of `φ` and Cauchy-Schwarz (`MemLp.integrable_mul`), `Y_0` is integrable.
* Step 4: By Kolmogorov/Etemadi's SLLN (`strong_law_ae`), `(1/n) ∑_{i=1}^n Y_i →_as 𝔼[Y_0]`. -/
theorem empiricalCovariance_tendsto_integral
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (α β : Fin m) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
      Filter.Tendsto
        (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X α β)
      Filter.atTop
      (nhds (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d))) := by
  set g := fun w : Fin d → ℝ => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)
  have hg_meas : Measurable g := measurable_cov_summand φ hφ_meas (X α) (X β)
  have hg_int : Integrable g (gaussianRowMeasure d) :=
    integrable_cov_summand_of_memLp φ (X α) (X β) (hφ_L2 α) (hφ_L2 β)
  simpa only [empiricalCovariance, g] using
    gaussianRow_average_tendsto_integral g hg_meas hg_int


end Theorem2

section Theorem3

/-! ## Theorem 3: Asymptotic Convergence in Distribution to NNGP -/

/-! ### Limiting NNGP Covariance Matrix and Output Distribution -/

/-- The limiting NNGP covariance matrix `Φ^{(∞)} ∈ ℝ^{m × m}`:
  `Φ^{(∞), α β} = ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)`. -/
noncomputable def limitingCovariance
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun α β => ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)

/-- Equation lemma for `limitingCovariance`. -/
lemma limitingCovariance_apply
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (α β : Fin m) :
    limitingCovariance φ X α β =
      ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d) := rfl

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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
      Filter.Tendsto
        (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X)
        Filter.atTop
        (nhds (limitingCovariance φ X)) :=
by
  have h_entry : ∀ α β : Fin m,
      ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
        Filter.Tendsto
          (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X α β)
          Filter.atTop
          (nhds (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d))) :=
    fun α β => empiricalCovariance_tendsto_integral φ X hφ_meas hφ_L2 α β
  have h_all :
      ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
        ∀ α β : Fin m,
          Filter.Tendsto
            (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X α β)
            Filter.atTop
            (nhds (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d))) := by
    simp_rw [ae_all_iff]
    exact h_entry
  filter_upwards [h_all] with rows hrows
  change Filter.Tendsto
    (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X)
    Filter.atTop
    (nhds ((fun α β => ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)
      ∂(gaussianRowMeasure d)) : Matrix (Fin m) (Fin m) ℝ))
  exact tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => hrows α β

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
    (hφ_L2 : ∀ α : Fin m, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (u : Fin m → ℝ) :
    (∑ α : Fin m, ∑ β : Fin m, u α * u β * limitingCovariance φ X α β) =
      ∫ w, (∑ α : Fin m, u α * φ (w ⬝ᵥ X α)) ^ 2 ∂(gaussianRowMeasure d) := by
  have hint (α β : Fin m) :
      Integrable (fun w => (u α * u β) * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β))) (gaussianRowMeasure d) :=
    (integrable_cov_summand_of_memLp φ (X α) (X β) (hφ_L2 α) (hφ_L2 β)).const_mul (u α * u β)
  simp_rw [limitingCovariance_apply]
  have h1 (α : Fin m) :
      (∑ β : Fin m, u α * u β * ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) =
      ∫ w, ∑ β : Fin m, u α * u β * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) ∂(gaussianRowMeasure d) := by
    have h_in (β : Fin m) :
        u α * u β * ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d) =
        ∫ w, (u α * u β) * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) ∂(gaussianRowMeasure d) :=
      (integral_const_mul (u α * u β) (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β))).symm
    simp_rw [h_in]
    exact (integral_finsetSum _ fun β _ => hint α β).symm
  simp_rw [h1]
  have hint_sum (α : Fin m) :
      Integrable (fun w => ∑ β : Fin m, u α * u β * (φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β))) (gaussianRowMeasure d) :=
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
    (hφ_L2 : ∀ α : Fin m, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (u : Fin m → ℝ) :
    0 ≤ ∑ α : Fin m, ∑ β : Fin m, u α * u β * limitingCovariance φ X α β := by
  rw [sum_sum_mul_limitingCovariance_eq_integral_sq φ X hφ_L2 u]
  exact integral_nonneg fun w => sq_nonneg _

/-- The quadratic form with the limiting NNGP covariance matrix `c ⬝ᵥ Φ^{(∞)} *ᵥ c` is nonnegative. -/
lemma limitingCovariance_nonneg
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d)) :
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
  `outputMeasure n d φ X = (initMeasure n d).map (fun (W, a) => evalVector φ W a X)`. -/
noncomputable def outputMeasure (n d : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.map (fun p => evalVector φ p.1 p.2 X) (initMeasure n d)

/-- The output law as the pushforward of the joint initialization measure. This is the public
equation lemma for `outputMeasure`, so downstream proofs need not unfold its implementation. -/
lemma outputMeasure_eq_map
    (n d : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    outputMeasure n d φ X =
      Measure.map (fun p => evalVector φ p.1 p.2 X) (initMeasure n d) := rfl

/-- `outputMeasure n d φ X` is a probability measure when `φ` is measurable. -/
lemma isProbabilityMeasure_outputMeasure
    (n d : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ) :
    IsProbabilityMeasure (outputMeasure n d φ X) := by
  rw [outputMeasure_eq_map]
  exact (Measure.isProbabilityMeasure_map_iff (evalVector_joint_measurable φ hφ X).aemeasurable).mpr inferInstance

/-- Transport: The pushforward of the infinite Gaussian row product measure under restriction to the
first `n` hidden units is exactly the finite-width input weight measure `gaussianInit n d`. -/
lemma map_infinitePi_rows_eq_gaussianInit (n d : ℕ) :
    Measure.map (fun (rows : ℕ → Fin d → ℝ) (i : Fin n) => rows i.val)
      (Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d) = gaussianInit n d := by
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  rfl

/-! ### Step 1 & Step 2: Unconditional Characteristic Function -/

/-- Step 1 & 2 helper: Integrating out the readout weights under `gaussianReadoutMeasure n` gives the
conditional characteristic function `exp(- (1/2) t ⬝ᵥ Φ^{(n)} *ᵥ t)`. -/
lemma integral_exp_inner_evalVector
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    (∫ a, Complex.exp (⟪evalVector φ W a X, t⟫ * Complex.I) ∂(gaussianReadoutMeasure n)) =
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2) := by
  have h_meas : Measurable (fun a => evalVector φ W a X) := evalVector_measurable φ W X
  calc
    (∫ a, Complex.exp (⟪evalVector φ W a X, t⟫ * Complex.I)
        ∂(gaussianReadoutMeasure n)) =
        charFun (Measure.map (fun a => evalVector φ W a X) (gaussianReadoutMeasure n)) t := by
      rw [charFun_apply, integral_map h_meas.aemeasurable (by fun_prop)]
    _ = Complex.exp
        (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2) :=
      charFun_readout_evalVector φ W X t

/-- **Step 2 (Law of Total Expectation for the Characteristic Function)**:
The unconditional characteristic function of the network output vector under `initMeasure n d` is the
expectation over input weights `W` of the conditional characteristic function:
  `charFun (outputMeasure n d φ X) t = 𝔼_W [exp(- (1/2) t ⬝ᵥ Φ^{(n)}(W) *ᵥ t)]`. -/
lemma charFun_outputMeasure
    (n : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun (outputMeasure n d φ X) t =
      ∫ W, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)
        ∂(gaussianInit n d) := by
  have h_meas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => evalVector φ p.1 p.2 X) :=
    evalVector_joint_measurable φ hφ X
  calc
    charFun (outputMeasure n d φ X) t =
        ∫ p, Complex.exp (⟪evalVector φ p.1 p.2 X, t⟫ * Complex.I) ∂(initMeasure n d) := by
      rw [outputMeasure_eq_map, charFun_apply,
        integral_map h_meas.aemeasurable (by fun_prop)]
    _ = ∫ W, (∫ a, Complex.exp (⟪evalVector φ W a X, t⟫ * Complex.I)
          ∂(gaussianReadoutMeasure n)) ∂(gaussianInit n d) := by
      change (∫ p, Complex.exp (⟪evalVector φ p.1 p.2 X, t⟫ * Complex.I)
          ∂((gaussianInit n d).prod (gaussianReadoutMeasure n))) = _
      have h_inner : Measurable
          (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
            ⟪evalVector φ p.1 p.2 X, t⟫) :=
        (continuous_id.inner continuous_const).measurable.comp h_meas
      have h_exp_meas : AEStronglyMeasurable
          (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
            Complex.exp (⟪evalVector φ p.1 p.2 X, t⟫ * Complex.I))
          ((gaussianInit n d).prod (gaussianReadoutMeasure n)) :=
        (Complex.continuous_exp.measurable.comp
          ((Complex.measurable_ofReal.comp h_inner).mul_const Complex.I)).aestronglyMeasurable
      exact integral_prod _ (Integrable.of_bound h_exp_meas 1
        (ae_of_all _ fun p => (Complex.norm_exp_ofReal_mul_I _).le))
    _ = ∫ W, Complex.exp
        (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)
          ∂(gaussianInit n d) := by
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
        fun W => ∑ α : Fin m, ∑ β : Fin m, t.ofLp α * (empiricalCovariance n φ W X α β) * t.ofLp β := by
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

/-- Expressing the expectation under `gaussianInit n d` as an expectation under `infinitePi`. -/
lemma integral_charFun_gaussianInit_eq_infinitePi
    (n : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    (∫ W, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)
      ∂(gaussianInit n d)) =
    ∫ rows, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)
      ∂(Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d) := by
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (t : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
      Filter.Tendsto
        (fun n : ℕ => Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ t.ofLp) / 2))
        Filter.atTop
        (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ t.ofLp) / 2))) := by
  have h_mat := empiricalCovariance_tendsto_limitingCovariance φ X hφ_meas hφ_L2
  filter_upwards [h_mat] with rows hrows
  exact ((continuous_charFun_integrand t).tendsto (limitingCovariance φ X)).comp hrows

/-- Auxiliary: `‖exp(- s / 2)‖ ≤ 1` for nonnegative real `s`. -/
lemma norm_exp_neg_ofReal_div_two_le_one {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp (- Complex.ofReal s / 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, show (- Complex.ofReal s / 2).re = - s / 2 by simp, ← Real.exp_zero]
  exact Real.exp_le_exp_of_le (by linarith)

/-- Step 4 uniform bound: The characteristic integrand is bounded by `1` uniformly in `n` and `W`. -/
lemma norm_charFun_readout_le_one
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    ‖Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ t.ofLp) / 2)‖ ≤ 1 :=
  norm_exp_neg_ofReal_div_two_le_one (empiricalCovariance_nonneg n φ W X t.ofLp)

/-- Step 4 (DCT under infinite product): The infinite-product integral of the characteristic integrand
converges to `exp(- (1/2) t ⬝ᵥ Φ^{(∞)} *ᵥ t)`. -/
lemma tendsto_integral_charFun_infinitePi
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ rows, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)
          ∂(Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d))
      Filter.atTop
      (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ t.ofLp) / 2))) := by
  have h_ae := charFun_integrand_tendsto_ae φ X hφ_meas hφ_L2 t
  have h_bound : ∀ n : ℕ, ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d),
      ‖Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)‖ ≤ (1 : ℝ) :=
    fun n => ae_of_all _ fun rows => norm_charFun_readout_le_one n φ _ X t
  have h_meas (n : ℕ) : Measurable (fun rows : ℕ → Fin d → ℝ =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)) := by
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
The unconditional characteristic function of the network output converges to the Gaussian characteristic
function:
  `lim_{n → ∞} charFun (outputMeasure n d φ X) t = exp(- (1/2) t ⬝ᵥ Φ^{(∞)} *ᵥ t)`. -/
lemma tendsto_charFun_outputMeasure
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ => charFun (outputMeasure n d φ X) t)
      Filter.atTop
      (nhds (Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ t.ofLp) / 2))) := by
  have h_eq (n : ℕ) : charFun (outputMeasure n d φ X) t =
      ∫ rows, Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ t.ofLp) / 2)
        ∂(Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d) := by
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ => charFun (outputMeasure n d φ X) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (limitingCovariance φ X)) t)) := by
  have hPos : (limitingCovariance φ X).PosSemidef :=
    limitingCovariance_posSemidef φ X hφ_meas hφ_L2
  have h_cf : charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (limitingCovariance φ X)) t =
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (u : Fin m → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
      Filter.Tendsto
        (fun n : ℕ => u ⬝ᵥ (empiricalCovariance n φ (fun i => rows i.val) X) *ᵥ u)
        Filter.atTop
        (nhds (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u)) := by
  have h_mat := empiricalCovariance_tendsto_limitingCovariance φ X hφ_meas hφ_L2
  filter_upwards [h_mat] with rows hrows
  exact ((continuous_matrix_quadratic u).tendsto (limitingCovariance φ X)).comp hrows

/-- Characteristic function of the projection expressed as evaluation of `charFun (outputMeasure n)`. -/
lemma charFun_map_projection_eq_outputMeasure
    (n : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (X : Fin m → Fin d → ℝ)
    (u : Fin m → ℝ) (t : ℝ) :
    charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) (initMeasure n d)) t =
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
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) (initMeasure n d)) t =
      ∫ W, Complex.exp (- Complex.ofReal (t ^ 2 * (u ⬝ᵥ (empiricalCovariance n φ W X) *ᵥ u)) / 2)
        ∂(gaussianInit n d) := by
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (u : Fin m → ℝ) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) (initMeasure n d)) t)
      Filter.atTop
      (nhds (Complex.exp (- Complex.ofReal (t ^ 2 * (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u)) / 2))) := by
  have h_eq (n : ℕ) :
      charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) (initMeasure n d)) t =
      charFun (outputMeasure n d φ X) (WithLp.toLp 2 (t • u)) :=
    charFun_map_projection_eq_outputMeasure n φ hφ_meas X u t
  simp_rw [h_eq]
  have h_lim := tendsto_charFun_outputMeasure φ X hφ_meas hφ_L2 (WithLp.toLp 2 (t • u))
  have h_quad : (WithLp.toLp 2 (t • u)).ofLp ⬝ᵥ (limitingCovariance φ X) *ᵥ (WithLp.toLp 2 (t • u)).ofLp =
      t ^ 2 * (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u) := by
    rw [WithLp.ofLp_toLp, dot_mulVec_smul]
  rwa [h_quad] at h_lim

/-- Pointwise convergence of scalar characteristic functions to the characteristic function
of the univariate Gaussian `𝒩(0, u ⬝ᵥ Φ^{(∞)} *ᵥ u)`. -/
lemma tendsto_charFun_map_projection_eq_gaussianReal
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (u : Fin m → ℝ) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => charFun (Measure.map (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) (initMeasure n d)) t)
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
      ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) (initMeasure n d)) :=
  (Measure.isProbabilityMeasure_map_iff (projection_joint_measurable φ hφ_meas X u).aemeasurable).mpr inferInstance



end Theorem3

section MultilayerSequentialNNGP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
      t.ofLp ⬝ᵥ (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n, H j α * H j β) *ᵥ t.ofLp := by
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

lemma empirical_layer_covariance_nonneg_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    0 ≤ t.ofLp ⬝ᵥ (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
      ∑ j : Fin n, H j α * H j β) *ᵥ t.ofLp := by
  rw [← projection_layer_variance_eq_multivariate]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

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
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (hg_meas : Measurable g)
    (hg_int : Integrable g (multivariateGaussian 0 K)) :
    ∀ᵐ seq : ℕ → EuclideanSpace ℝ (Fin m)
      ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K),
      Filter.Tendsto
        (fun width : ℕ => (width : ℝ)⁻¹ * ∑ j : Fin width, g (seq j))
        Filter.atTop (nhds (∫ z, g z ∂(multivariateGaussian 0 K))) := by
  set μ := Measure.infinitePi (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)
  have hmap_eval : ∀ i : ℕ, μ.map (fun seq => seq i) = multivariateGaussian 0 K :=
    fun i => Measure.infinitePi_map_eval _ i
  have hmp : MeasurePreserving (fun seq : ℕ → EuclideanSpace ℝ (Fin m) => seq 0) μ
      (multivariateGaussian 0 K) :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => multivariateGaussian 0 K) 0
  have hint : Integrable (fun seq : ℕ → EuclideanSpace ℝ (Fin m) => g (seq 0)) μ :=
    (hmp.integrable_comp hg_meas.aestronglyMeasurable).2 hg_int
  have hindep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) fun j seq => g (seq j)) := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ => multivariateGaussian 0 K)
      (X := fun _ : ℕ => g) (fun _ => hg_meas)
    intro i j hij
    exact h.indepFun hij
  have hident : ∀ i : ℕ,
      IdentDistrib (fun seq : ℕ → EuclideanSpace ℝ (Fin m) => g (seq i))
        (fun seq : ℕ → EuclideanSpace ℝ (Fin m) => g (seq 0)) μ μ := by
    intro i
    have hcoord : IdentDistrib (fun seq : ℕ → EuclideanSpace ℝ (Fin m) => seq i)
        (fun seq : ℕ → EuclideanSpace ℝ (Fin m) => seq 0) μ μ := by
      refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
      rw [hmap_eval i, hmap_eval 0]
    exact hcoord.comp hg_meas
  have hslln : ∀ᵐ seq ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (seq i))
      Filter.atTop (nhds (∫ seq, g (seq 0) ∂μ)) :=
    strong_law_ae _ hint hindep hident
  have hexp : ∫ seq, g (seq 0) ∂μ = ∫ z, g z ∂(multivariateGaussian 0 K) := by
    rw [← hmap_eval 0]
    exact (MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable
      hg_meas.stronglyMeasurable.aestronglyMeasurable).symm
  filter_upwards [hslln] with seq hseq
  rw [← hexp]
  convert hseq using 1
  ext width
  rw [smul_eq_mul, Fin.sum_univ_eq_sum_range (fun i => g (seq i)) width]

/-- Almost-sure convergence of every entry of the empirical covariance recurrence. -/
theorem empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
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
      ∀ᵐ Z : ℕ → EuclideanSpace ℝ (Fin m) ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K),
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
  have h_all :
      ∀ᵐ Z : ℕ → EuclideanSpace ℝ (Fin m) ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K),
        ∀ α β : Fin m, Filter.Tendsto
          (fun n : ℕ => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
            ∑ j : Fin n, φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β))
          Filter.atTop
          (nhds (σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
            φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) := by
    rw [ae_all_iff]
    intro α
    rw [ae_all_iff]
    intro β
    exact h_entry α β
  filter_upwards [h_all] with Z hZ
  exact tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => hZ α β

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
      ∂gaussianReadoutMeasure n) =
      Complex.exp (- Complex.ofReal (∑ j : Fin n, (c j) ^ 2) / 2) := by
  have h_map := map_gaussianReadoutMeasure_inner c
  have h_meas_dot : Measurable (fun w : Fin n → ℝ => ∑ j : Fin n, w j * c j) := by
    refine Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  have h_int : (∫ w : Fin n → ℝ, Complex.exp ((∑ j : Fin n, w j * c j : ℝ) * Complex.I)
      ∂gaussianReadoutMeasure n) = ∫ y : ℝ, Complex.exp (y * Complex.I)
        ∂Measure.map (fun w => ∑ j : Fin n, w j * c j) (gaussianReadoutMeasure n) := by
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

/-- Conditional on deterministic previous-layer activations, the full `m`-vector of
preactivations is exactly Gaussian. -/
lemma exact_conditional_normality_general_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) :
    Measure.map
      (fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
        σb * p.2 + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j, p.1 j * H j α)
      ((gaussianReadoutMeasure n).prod (gaussianReal 0 1)) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
          ∑ j : Fin n, H j α * H j β) := by
  have hPos : (show Matrix (Fin m) (Fin m) ℝ from fun α β : Fin m => σb ^ 2 +
      (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n, H j α * H j β).PosSemidef :=
    empirical_layer_covariance_posSemidef_multivariate σw σb n m H
  have : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
      (show Matrix (Fin m) (Fin m) ℝ from fun α β : Fin m => σb ^ 2 +
        (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n, H j α * H j β)) := by infer_instance
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
        ∑ j : Fin n, p.1 j * ((σw * (n : ℝ)⁻¹.sqrt) * ∑ α : Fin m, t.ofLp α * H j α)) : ℝ) * Complex.I) =
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
      ∂(gaussianReadoutMeasure n).prod (gaussianReal 0 1)) =
    (∫ w : Fin n → ℝ, Complex.exp ((∑ j : Fin n, w j * cw j : ℝ) * Complex.I)
      ∂gaussianReadoutMeasure n) *
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

lemma charFun_conditional_preactivation_multivariate (σw σb : ℝ) (n m : ℕ)
    (H : Fin n → Fin m → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    charFun
      (Measure.map (fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
        σb * p.2 + (σw * (n : ℝ)⁻¹.sqrt) * ∑ j, p.1 j * H j α)
        ((gaussianReadoutMeasure n).prod (gaussianReal 0 1))) t =
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
        (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
          ∑ j : Fin n, H j α * H j β) *ᵥ t.ofLp) / 2) := by
  rw [exact_conditional_normality_general_multivariate]
  rw [charFun_multivariateGaussian
    (empirical_layer_covariance_posSemidef_multivariate σw σb n m H)]
  simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub, neg_div]

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

lemma limitingRecurrence_nonneg_multivariate (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ)
    (hφ_meas : Measurable φ) (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) (c : Fin m → ℝ) :
    0 ≤ c ⬝ᵥ (fun α β => σb ^ 2 + σw ^ 2 *
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) *ᵥ c := by
  have hslln := empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate σw σb m φ hφ_meas K hφ_L2
  rcases hslln.exists with ⟨Z, hZ⟩
  have h_quad : Filter.Tendsto
      (fun n : ℕ => c ⬝ᵥ (fun α β : Fin m => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) *
        ∑ j : Fin n, φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ c)
      Filter.atTop
      (nhds (c ⬝ᵥ (fun α β => σb ^ 2 + σw ^ 2 *
        ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)) *ᵥ c)) :=
    (continuous_matrix_quadratic c).continuousAt.tendsto.comp hZ
  refine ge_of_tendsto h_quad (Filter.Eventually.of_forall fun n => ?_)
  exact empirical_layer_covariance_nonneg_multivariate σw σb n m
    (fun j α => φ ((Z j).ofLp α)) (WithLp.toLp 2 c)

lemma limitingRecurrence_posSemidef_multivariate (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ)
    (hφ_meas : Measurable φ) (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β => σb ^ 2 + σw ^ 2 *
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)).PosSemidef :=
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
    refine (measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_))).mul_const _
    refine (hφ_meas.comp ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable.comp
      (measurable_pi_apply j.val))).mul ?_
    exact hφ_meas.comp ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable.comp
      (measurable_pi_apply j.val))
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp h_quad).neg.div_const 2)

lemma tendsto_charFun_preactivation_dct_multivariate
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (_hK_pos : K.PosSemidef)
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
  have hslln := empiricalCovariance_tendsto_limitingRecurrence_ae_multivariate σw σb m φ hφ_meas K hφ_L2
  have h_cont : Continuous (fun M : Matrix (Fin m) (Fin m) ℝ =>
      Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ M *ᵥ t.ofLp) / 2)) :=
    continuous_charFun_integrand t
  have h_ae : ∀ᵐ Z : ℕ → EuclideanSpace ℝ (Fin m) ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K),
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

lemma charFun_map_sequential_preactivation_multivariate
    (σw σb : ℝ) (n m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun (Measure.map
      (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
          ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
      ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
        ((gaussianReadoutMeasure n).prod (gaussianReal 0 1)))) t =
      ∫ Z : ℕ → EuclideanSpace ℝ (Fin m),
        Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
          (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
            φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)
        ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K) := by
  set F := fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
    WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
      ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α)
  set μZ := Measure.infinitePi fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K
  set μP := (gaussianReadoutMeasure n).prod (gaussianReal 0 1)
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

lemma tendsto_charFun_sequential_preactivation_multivariate
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (hK_pos : K.PosSemidef)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto
      (fun n : ℕ => charFun (Measure.map
        (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
          WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
            ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
        ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
          ((gaussianReadoutMeasure n).prod (gaussianReal 0 1)))) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) t)) := by
  have hPos : (show Matrix (Fin m) (Fin m) ℝ from fun α β => σb ^ 2 + σw ^ 2 *
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)).PosSemidef :=
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
        ((gaussianReadoutMeasure n).prod (gaussianReal 0 1)))) t =
      ∫ Z : ℕ → EuclideanSpace ℝ (Fin m),
        Complex.exp (- Complex.ofReal (t.ofLp ⬝ᵥ
          (fun α β => σb ^ 2 + (σw ^ 2 * (n : ℝ)⁻¹) * ∑ j : Fin n,
            φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β)) *ᵥ t.ofLp) / 2)
        ∂(Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K) :=
    charFun_map_sequential_preactivation_multivariate σw σb n m φ hφ_meas K t
  simp_rw [h_eq]
  exact tendsto_charFun_preactivation_dct_multivariate σw σb m φ hφ_meas K hK_pos hφ_L2 t



end MultilayerSequentialNNGP

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

section DeepNNGPRecursion

/-! ## Theorem 2.13 (Deep NNGP Recursion)

This section assembles the single-layer-transition machinery above
(`layerCovarianceSeq`, `exact_conditional_normality_general_multivariate`,
`conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq`) into an actual depth-`L`
network with real weight matrices chained together at every layer, and proves that its empirical
covariance converges layer by layer (Part 1) and that its output converges in distribution to the
NNGP limit (Part 2).  The final theorem statements and full proof narratives are given in the
second `DeepNNGPRecursion` section later in this file; this section contains the network
construction and the supporting lemmas it needs.

Following the recursive pre-activation family `deepPreactivation` below, the per-layer empirical
covariance and the joint initialization measure are both written out inline at each point of use
(rather than named as separate definitions) to avoid adding more top-level declarations to an
already-large file: the empirical covariance of a width-`n` post-activation family
`H : Fin n → Fin m → ℝ` is `fun α β => (n:ℝ)⁻¹ * ∑ j, φ (H j α) * φ (H j β)` (the same formula
already inlined throughout `AsymptoticEmpiricalCovariancePropagation`, e.g. in
`conditional_preactivations_eq_pi`), and the joint initialization measure of a depth-`L` network is
`(Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)` (as in
`indepFun_deepLayer_history` below).

The covariance update is continuous relative to `PosSemidef`, including the singular boundary;
see `continuousWithinAt_covarianceMap` below.
-/

/-! ### Depth-`L` Network Construction -/

/-- The recursive pre-activation family `h_1, …, h_L` of a depth-`L` MLP with input dimension `d`,
uniform hidden width, activation `φ`, and evaluation inputs `X`.

`W : ℕ → ℕ → ℕ → ℝ` is a single infinite population of i.i.d. standard Gaussian weights, indexed by
`(layer, neuron, source-neuron)`: layer `0` (restricted to its first `d` "columns") plays the role
of the input weight matrix `W₀`, and layer `ℓ + 1` (restricted to its first `n` columns) plays the
role of the `(ℓ+1)`-th hidden-to-hidden weight matrix.  Folding the input layer into the *same*
uniform population as the hidden layers (rather than giving it a separate type/measure) is what
lets `indepFun_deepLayer_history` below supply independence for *every* layer transition, including
the first, via a single application of `iIndepFun_pi` — avoiding the need to separately combine
independence facts across two differently-shaped blocks.

`n` is the width cutoff used at every hidden layer; sending `n → ∞` over a single fixed probability
space (rather than building a different space per width) is the same device already used for
`Measure.infinitePi` throughout this file, e.g. in `empiricalCovariance_tendsto_limitingCovariance`.

Indexing starts at `0` so that `deepPreactivation … 0 = h_1` and, matching `layerCovarianceSeq`'s
own `0`-indexed recursion, the empirical covariance of `deepPreactivation … ℓ` is the quantity that
converges to `layerCovarianceSeq 1 0 φ m Φ0 (ℓ + 1)`. -/
noncomputable def deepPreactivation (d m n : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (W : ℕ → ℕ → ℕ → ℝ) : ℕ → Fin m → Fin n → ℝ
  | 0 => fun α j => (d : ℝ)⁻¹.sqrt * ((fun k : Fin d => W 0 j.val k.val) ⬝ᵥ X α)
  | ℓ + 1 => fun α j => (n : ℝ)⁻¹.sqrt * ∑ k : Fin n,
      W (ℓ + 1) j.val k.val * φ (deepPreactivation d m n φ X W ℓ α k)

/-- A preactivation at layer `ℓ` depends only on weight populations at indices at most `ℓ`.
This is the deterministic bridge from the finite earlier-layer history in
`indepFun_deepLayer_history` back to `deepPreactivation`. -/
lemma deepPreactivation_congr_of_eqOn (d m n : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (W W' : ℕ → ℕ → ℕ → ℝ) (ℓ : ℕ)
    (hW : ∀ k : ℕ, k ≤ ℓ → W k = W' k) :
    deepPreactivation d m n φ X W ℓ = deepPreactivation d m n φ X W' ℓ := by
  induction ℓ with
  | zero =>
      simp only [deepPreactivation]
      rw [hW 0 le_rfl]
  | succ ℓ ih =>
      simp only [deepPreactivation]
      rw [hW (ℓ + 1) le_rfl]
      apply funext
      intro α
      apply funext
      intro j
      apply congrArg (fun q : Fin n → ℝ => (n : ℝ)⁻¹.sqrt * ∑ k : Fin n,
        W' (ℓ + 1) j.val k.val * φ (q k))
      apply funext
      intro k
      exact congrFun (congrFun (ih fun r hr => hW r (Nat.le_succ_of_le hr)) α) k

/-- The infinite input-weight population, evaluated at the fixed inputs and normalized by the
input dimension, is an i.i.d. family of centered Gaussians with the base Gram covariance. This
is the distributional bridge needed for the base case of the deep covariance induction. -/
lemma map_infinitePi_input_preactivations (d m : ℕ) (X : Fin m → Fin d → ℝ) :
    Measure.map
      (fun W : ℕ → ℕ → ℝ => fun j : ℕ => WithLp.toLp 2 fun α : Fin m =>
        (d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j k.val * X α k)
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
  let restrictRows : (ℕ → ℕ → ℝ) → (ℕ → Fin d → ℝ) :=
    fun W j k => W j k.val
  have hrestrictRows_meas : Measurable restrictRows := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => ?_
    exact (measurable_pi_apply k.val).comp (measurable_pi_apply j)
  have hrestrictRows :
      Measure.map restrictRows
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d := by
    calc
      Measure.map restrictRows
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
        Measure.infinitePi fun _ : ℕ =>
          Measure.map (fun r : ℕ → ℝ => fun k : Fin d => r k.val)
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
          simpa [restrictRows] using
            (Measure.infinitePi_map_pi
              (μ := fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
              (f := fun _ (r : ℕ → ℝ) (k : Fin d) => r k.val)
              (fun _ => measurable_pi_iff.2 fun k => measurable_pi_apply k.val))
      _ = Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d := by
        congr 1
        funext j
        rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
          Measure.infinitePi_eq_pi]
  let u : Fin m → Fin d → ℝ := fun α k => (d : ℝ)⁻¹.sqrt * X α k
  let projectRows : (ℕ → Fin d → ℝ) → (ℕ → EuclideanSpace ℝ (Fin m)) :=
    fun W j => WithLp.toLp 2 fun α => W j ⬝ᵥ u α
  have hprojectRows_meas : Measurable projectRows := by
    refine measurable_pi_iff.2 fun j => ?_
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.2 fun α => ?_
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp (measurable_pi_apply j)).mul_const _
  have hprojectRows :
      Measure.map projectRows (Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d) =
      Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
    calc
      Measure.map projectRows (Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d) =
        Measure.infinitePi fun _ : ℕ => Measure.map
          (fun r : Fin d → ℝ => WithLp.toLp 2 fun α => r ⬝ᵥ u α)
          (gaussianReadoutMeasure d) := by
          simpa [projectRows] using
            (Measure.infinitePi_map_pi
              (μ := fun _ : ℕ => gaussianReadoutMeasure d)
              (f := fun _ (r : Fin d → ℝ) => WithLp.toLp 2 fun α => r ⬝ᵥ u α)
              (fun _ => (PiLp.continuous_toLp 2 _).measurable.comp
                (continuous_pi fun α => by fun_prop).measurable))
      _ = Measure.infinitePi fun _ : ℕ =>
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
            (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
        apply congrArg Measure.infinitePi
        funext j
        have hcov : (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β) =
            (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
          ext α β
          change (∑ k : Fin d, (d : ℝ)⁻¹.sqrt * X α k *
            ((d : ℝ)⁻¹.sqrt * X β k)) = (d : ℝ)⁻¹ * ∑ k : Fin d, X α k * X β k
          have hroot : (d : ℝ)⁻¹.sqrt * (d : ℝ)⁻¹.sqrt = (d : ℝ)⁻¹ :=
            Real.mul_self_sqrt (by positivity)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [show (d : ℝ)⁻¹.sqrt * X α k * ((d : ℝ)⁻¹.sqrt * X β k) =
              ((d : ℝ)⁻¹.sqrt * (d : ℝ)⁻¹.sqrt) * (X α k * X β k) by ring, hroot]
        rw [stdGaussian_inner_family, hcov]
  have hcomp : projectRows ∘ restrictRows =
      fun W : ℕ → ℕ → ℝ => fun j : ℕ => WithLp.toLp 2 fun α : Fin m =>
        (d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j k.val * X α k := by
    funext W j
    simp only [Function.comp_apply, projectRows, restrictRows]
    congr 1
    funext α
    simp only [u, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [← hcomp, ← Measure.map_map hprojectRows_meas hrestrictRows_meas, hrestrictRows, hprojectRows]

/-- **Independence Across Depth**, for the uniform `Fin L → ℕ → ℕ → ℝ` layer population feeding
`deepPreactivation`.  This is the infinite-population analogue of `indepFun_layer_history`
(`InitializationHelpers.lean`); the proof is identical (`iIndepFun_pi` is generic in the per-index
measurable space and measure), only the per-layer type changes from the finite-width
`Fin n → Fin d → ℝ` to the infinite-population `ℕ → ℕ → ℝ`. -/
theorem indepFun_deepLayer_history (L : ℕ) (ℓ : Fin L) :
    IndepFun (fun ω : Fin L → ℕ → ℕ → ℝ => ω ℓ)
      (fun ω : Fin L → ℕ → ℕ → ℝ => fun i : Finset.Iio ℓ => ω i)
      (Measure.pi (fun _ : Fin L =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
  have h_indep : iIndepFun (fun ℓ : Fin L => fun ω : Fin L → ℕ → ℕ → ℝ => ω ℓ)
      (Measure.pi (fun _ : Fin L =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h_meas : ∀ i : Fin L, Measurable (fun ω : Fin L → ℕ → ℕ → ℝ => ω i) :=
    fun i => measurable_pi_apply i
  have h_disj : Disjoint ({ℓ} : Finset (Fin L)) (Finset.Iio ℓ) :=
    Finset.disjoint_singleton_left.2 (by simp)
  have h := h_indep.indepFun_finset {ℓ} (Finset.Iio ℓ) h_disj h_meas
  exact h.comp (measurable_pi_apply (⟨ℓ, Finset.mem_singleton_self ℓ⟩ :
    ({ℓ} : Finset (Fin L)))) measurable_id

/-- The current infinite weight population is independent of all earlier populations.  This
pushforward form is the measure-theoretic interface used by the deep covariance induction: it
separates the fresh layer weights from the history without introducing a second network state. -/
lemma map_deepLayer_history_eq_prod (L : ℕ) (ℓ : Fin L) :
    Measure.map
      (fun w : Fin L → ℕ → ℕ → ℝ => (w ℓ, fun i : Finset.Iio ℓ => w i))
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        (Measure.map (fun w : Fin L → ℕ → ℕ → ℝ => fun i : Finset.Iio ℓ => w i)
          (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
  have hhistory_meas : Measurable
      (fun w : Fin L → ℕ → ℕ → ℝ => fun i : Finset.Iio ℓ => w i) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact measurable_pi_apply (i : Fin L)
  rw [(indepFun_deepLayer_history L ℓ).map_prod_eq_prod_map_map]
  · rw [(measurePreserving_eval (fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) ℓ).map_eq]
  · exact (measurable_pi_apply ℓ).aemeasurable
  · exact hhistory_meas.aemeasurable

/-- The total weight family reconstructed from the populations strictly before `r`.  Values at
and after `r` are irrelevant for preactivations before `r` and are set to zero. -/
noncomputable def deepHistoryWeight (L : ℕ) (r : Fin L)
    (h : Finset.Iio r → ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ := fun k =>
  if hk : k < r.val then
    h ⟨⟨k, lt_trans hk r.isLt⟩, Finset.mem_Iio.mpr (show (⟨k, lt_trans hk r.isLt⟩ : Fin L) < r
      from hk)⟩
  else 0

/-- A preactivation before `r` depends only on the `Iio r` history. -/
lemma deepPreactivation_eq_deepHistoryWeight
    (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (r : Fin L) (ℓ : ℕ) (hℓ : ℓ < r.val)
    (w : Fin L → ℕ → ℕ → ℝ) :
    deepPreactivation d m n φ X
      (fun k => if hk : k < L then w ⟨k, hk⟩ else 0) ℓ =
    deepPreactivation d m n φ X (deepHistoryWeight L r (fun i : Finset.Iio r => w i)) ℓ := by
  apply deepPreactivation_congr_of_eqOn d m n φ X _ _ ℓ
  intro k hk
  have hkr : k < r.val := lt_of_le_of_lt hk hℓ
  simp [deepHistoryWeight, hkr, lt_trans hkr r.isLt]

/-! ### General-Purpose Convergence-in-Probability Lemmas

The two lemmas below are genuinely general (not NTK-specific): they are missing pieces of
`Mathlib.MeasureTheory.Function.ConvergenceInMeasure`'s API that the induction and the final
characteristic-function argument in the second `DeepNNGPRecursion` section both need. Neither is
hard to prove — they are direct consequences of tools already in this Mathlib checkout
(`EMetric.continuousAt_iff`, `TendstoInMeasure.exists_seq_tendsto_ae`,
`tendsto_of_subseq_tendsto`) — but Mathlib itself does not compose `TendstoInMeasure` with a
continuous map of the codomain, nor with dominated convergence of integrals, so both are proved
from scratch here.
-/

/-- `Matrix` inherits its `PseudoEMetricSpace` structure from the underlying Pi type. Mathlib does
not register this instance directly for `Matrix` (to avoid a diamond with other norms such as the
operator or Frobenius norm — `Matrix` is a `def`, not `abbrev`, over `m → n → α`, so instance
search does not unfold it automatically), so it is registered here. Needed so
`tendstoInMeasure_comp_of_continuousAt` below applies to the `Matrix`-valued sequences in Part 1
and Part 2. -/
instance instPseudoEMetricSpaceMatrix (m : ℕ) : PseudoEMetricSpace (Matrix (Fin m) (Fin m) ℝ) := by
  unfold Matrix; infer_instance

/-- The matching pseudo-metric instance is needed for the real-valued `dist` tail events used in
convergence-in-measure statements.  As above, it is inherited from the underlying finite Pi type. -/
instance instPseudoMetricSpaceMatrix (m : ℕ) : PseudoMetricSpace (Matrix (Fin m) (Fin m) ℝ) := by
  unfold Matrix; infer_instance

/-- **Continuous mapping theorem for convergence in probability to a constant.** If `f n → y` in
probability and `g` is continuous at `y`, then `g ∘ f n → g y` in probability. Used below to turn
the inductive hypothesis `Φ_ℓ^{(n)} → Φ_ℓ` into `𝒞_φ(Φ_ℓ^{(n)}) → 𝒞_φ(Φ_ℓ)`. -/
theorem tendstoInMeasure_comp_of_continuousAt
    {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : ℕ → α → E} {y : E} {g : E → F}
    (hfg : TendstoInMeasure μ f Filter.atTop (fun _ => y)) (hg : ContinuousAt g y) :
    TendstoInMeasure μ (fun n a => g (f n a)) Filter.atTop (fun _ => g y) := by
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := EMetric.continuousAt_iff.mp hg ε hε
  have hmono : ∀ n, μ {a | ε ≤ edist (g (f n a)) (g y)} ≤ μ {a | δ ≤ edist (f n a) y} := by
    intro n
    refine measure_mono fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_contra hlt
    push Not at hlt
    exact absurd (hδg hlt) (not_lt.mpr ha)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg δ hδ)
    (fun _ => zero_le) hmono

/-- **Continuous mapping on an invariant set.** If `f n → y` in probability, all values of `f`
lie in `s`, and `g` is continuous at `y` relative to `s`, then `g ∘ f n → g y` in probability.
This is the form needed for covariance matrices: `multivariateGaussian` is naturally continuous in
its covariance only on the positive-semidefinite cone. -/
theorem tendstoInMeasure_comp_of_continuousWithinAt
    {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : ℕ → α → E} {y : E} {g : E → F}
    {s : Set E} (hfg : TendstoInMeasure μ f Filter.atTop (fun _ => y))
    (hf : ∀ n a, f n a ∈ s) (hg : ContinuousWithinAt g s y) :
    TendstoInMeasure μ (fun n a => g (f n a)) Filter.atTop (fun _ => g y) := by
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := EMetric.continuousWithinAt_iff.mp hg ε hε
  have hmono : ∀ n, μ {a | ε ≤ edist (g (f n a)) (g y)} ≤ μ {a | δ ≤ edist (f n a) y} := by
    intro n
    refine measure_mono fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_contra hlt
    push Not at hlt
    exact absurd (hδg (hf n a) hlt) (not_lt.mpr ha)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg δ hδ)
    (fun _ => zero_le) hmono

/-- A two-stage convergence-in-probability argument.  If `f n` is close in probability to a
possibly `n`-dependent intermediate approximation `g n`, and `g n` converges in probability to
`h`, then `f n` converges in probability to `h`.  The deep covariance induction uses this after
separating the fresh-layer empirical fluctuation from the deterministic covariance update. -/
theorem tendstoInMeasure_trans
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoMetricSpace E] {f g : ℕ → α → E} {h : α → E}
    (hfg : ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun n => μ {a | ε ≤ dist (f n a) (g n a)}) Filter.atTop (nhds 0))
    (hgh : TendstoInMeasure μ g Filter.atTop h) :
    TendstoInMeasure μ f Filter.atTop h := by
  rw [tendstoInMeasure_iff_dist] at hgh ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hsum := (hfg (ε / 2) hhalf).add (hgh (ε / 2) hhalf)
  have hmono : ∀ n, μ {a | ε ≤ dist (f n a) (h a)} ≤
      μ {a | ε / 2 ≤ dist (f n a) (g n a)} +
        μ {a | ε / 2 ≤ dist (g n a) (h a)} := by
    intro n
    calc
      μ {a | ε ≤ dist (f n a) (h a)} ≤
          μ ({a | ε / 2 ≤ dist (f n a) (g n a)} ∪
            {a | ε / 2 ≤ dist (g n a) (h a)}) := by
        apply measure_mono
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        by_cases hfg' : ε / 2 ≤ dist (f n a) (g n a)
        · exact Or.inl hfg'
        · right
          by_contra hgh'
          have hfg_lt : dist (f n a) (g n a) < ε / 2 := lt_of_not_ge hfg'
          have hgh_lt : dist (g n a) (h a) < ε / 2 := lt_of_not_ge hgh'
          have hlt : dist (f n a) (h a) < ε := by
            calc
              dist (f n a) (h a) ≤ dist (f n a) (g n a) + dist (g n a) (h a) :=
                dist_triangle _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add hfg_lt hgh_lt
              _ = ε := by ring
          exact (not_lt_of_ge ha) hlt
      _ ≤ μ {a | ε / 2 ≤ dist (f n a) (g n a)} +
          μ {a | ε / 2 ≤ dist (g n a) (h a)} := measure_union_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hsum)
    (fun _ => zero_le) hmono

/-- To prove convergence in measure of a finite matrix-valued family, it suffices to prove the
corresponding tail estimate for every entry.  The proof uses the sup metric on Pi types and finite
subadditivity of measure.  This is the matrix reduction used by the conditional covariance
concentration argument. -/
theorem tendsto_matrixTail_of_tendsto_entrywise
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} (m : ℕ)
    {f g : ℕ → Ω → Matrix (Fin m) (Fin m) ℝ}
    (hentry : ∀ (α β : Fin m) (ε : ℝ), 0 < ε →
      Filter.Tendsto (fun n => μ {a | ε ≤ dist (f n a α β) (g n a α β)})
        Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun n => μ {a | ε ≤ dist (f n a) (g n a)})
        Filter.atTop (nhds 0) := by
  intro ε hε
  have hsum : Filter.Tendsto
      (fun n => ∑ q : Fin m × Fin m,
        μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)})
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_finsetSum
      (f := fun q : Fin m × Fin m => fun n =>
        μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)})
      (a := fun _ => 0) (s := Finset.univ)
      (fun q _ => hentry q.1 q.2 ε hε))
  have hbound : ∀ n : ℕ,
      μ {a | ε ≤ dist (f n a) (g n a)} ≤
        ∑ q : Fin m × Fin m, μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)} := by
    intro n
    calc
      μ {a | ε ≤ dist (f n a) (g n a)} ≤
          μ (⋃ q : Fin m × Fin m, {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)}) := by
        apply measure_mono
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha
        by_contra h
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h
        push Not at h
        exact (not_lt_of_ge ha) ((dist_pi_lt_iff hε).2 fun α =>
          (dist_pi_lt_iff hε).2 fun β => h ⟨α, β⟩)
      _ ≤ ∑ q : Fin m × Fin m,
          μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)} :=
        measure_iUnion_fintype_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

/-- Convergence in probability is preserved by precomposition with a measure-preserving map.
The explicit measurability hypotheses make the result applicable to the finite-dimensional
covariance maps used below without relying on an implicit completion of the source measure. -/
theorem tendstoInMeasure_comp_measurePreserving
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {ν : Measure β} [PseudoEMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {T : α → β} {f : ℕ → β → E} {g : β → E}
    (hfg : TendstoInMeasure ν f Filter.atTop g) (hT : MeasurePreserving T μ ν)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) :
    TendstoInMeasure μ (fun n a => f n (T a)) Filter.atTop (fun a => g (T a)) := by
  intro ε hε
  have hset : ∀ n, MeasurableSet {b | ε ≤ edist (f n b) (g b)} := fun n =>
    ((hf n).edist hg) measurableSet_Ici
  have heq : (fun n => μ {a | ε ≤ edist (f n (T a)) (g (T a))}) =
      fun n => ν {b | ε ≤ edist (f n b) (g b)} := by
    funext n
    change μ (T ⁻¹' {b | ε ≤ edist (f n b) (g b)}) = _
    rw [← hT.map_eq, Measure.map_apply hT.measurable (hset n)]
  rw [heq]
  exact hfg ε hε

/-- **Bounded convergence for convergence in probability.** If `f n → g` in probability and the
`f n` are uniformly bounded in norm by a constant, then `∫ f n → ∫ g`. Proof: given any
subsequence, `TendstoInMeasure.exists_seq_tendsto_ae` extracts a further a.e.-convergent
subsequence, along which the ordinary dominated convergence theorem gives convergence of the
integrals; since every subsequence has such a further convergent subsequence,
`tendsto_of_subseq_tendsto` closes the full sequence. Used below in place of Theorem 3's dominated
convergence step (`tendsto_charFun_outputMeasure`), since Part 1 below only supplies convergence in
probability, not the almost-sure convergence Theorem 3 had from Kolmogorov's SLLN. -/
theorem tendsto_integral_of_tendstoInMeasure_of_bounded
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℕ → α → E} {g : α → E}
    (hfg : TendstoInMeasure μ f Filter.atTop g)
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ) (C : ℝ)
    (hf_bound : ∀ n, ∀ᵐ a ∂μ, ‖f n a‖ ≤ C) [IsFiniteMeasure μ] :
    Filter.Tendsto (fun n => ∫ a, f n a ∂μ) Filter.atTop (nhds (∫ a, g a ∂μ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hms_ae⟩ := (hfg.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  simpa using tendsto_integral_of_dominated_convergence (bound := fun _ => C)
    (fun k => hf_meas (ns (ms k))) (integrable_const C)
    (fun k => hf_bound (ns (ms k))) hms_ae

/-! ### Continuity of the Covariance-Update Map -/

section CovarianceMapContinuity

open scoped Matrix.Norms.L2Operator

/-- A coordinate of `toEuclideanCLM K z` is controlled by the operator norm of `K`, uniformly in
the coordinate index. This is the linear-algebra fact behind the dominating function used by
`continuousWithinAt_covarianceMap`'s dominated-convergence argument. -/
lemma abs_toEuclideanCLM_ofLp_le {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (α : Fin m) :
    |(toEuclideanCLM (𝕜 := ℝ) K z).ofLp α| ≤ ‖K‖ * ‖z‖ := by
  rw [← Real.norm_eq_abs]
  change ‖(toEuclideanCLM (𝕜 := ℝ) K z) α‖ ≤ ‖K‖ * ‖z‖
  calc
    ‖(toEuclideanCLM (𝕜 := ℝ) K z) α‖ ≤ ‖toEuclideanCLM (𝕜 := ℝ) K z‖ :=
      PiLp.norm_apply_le _ _
    _ ≤ ‖toEuclideanCLM (𝕜 := ℝ) K‖ * ‖z‖ :=
      (toEuclideanCLM (𝕜 := ℝ) K).le_opNorm z
    _ = ‖K‖ * ‖z‖ := by rw [l2_opNorm_toEuclideanCLM]

-- Polynomial-growth bound on a product `φ a * φ b`, given a common bound `r` on `|a|` and `|b|`.
-- Pure real-analysis; no measure theory or matrices involved.
private lemma abs_mul_le_of_polynomial_growth (φ : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (a b r : ℝ) (hr : 0 ≤ r) (ha : |a| ≤ r) (hb : |b| ≤ r) :
    |φ a * φ b| ≤ 2 * C ^ 2 * (1 + r ^ (2 * p)) := by
  have hpa : |a| ^ p ≤ r ^ p := pow_le_pow_left₀ (abs_nonneg a) ha p
  have hpb : |b| ^ p ≤ r ^ p := pow_le_pow_left₀ (abs_nonneg b) hb p
  have hφa : |φ a| ≤ C * (1 + r ^ p) := by
    calc
      |φ a| ≤ C * (1 + |a| ^ p) := hφ_growth a
      _ ≤ C * (1 + r ^ p) := by gcongr
  have hφb : |φ b| ≤ C * (1 + r ^ p) := by
    calc
      |φ b| ≤ C * (1 + |b| ^ p) := hφ_growth b
      _ ≤ C * (1 + r ^ p) := by gcongr
  have hsquare : (1 + r ^ p) ^ 2 ≤ 2 * (1 + r ^ (2 * p)) := by
    have hpow : r ^ (2 * p) = (r ^ p) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow]
    nlinarith [sq_nonneg (r ^ p - 1)]
  calc
    |φ a * φ b| = |φ a| * |φ b| := abs_mul _ _
    _ ≤ (C * (1 + r ^ p)) * (C * (1 + r ^ p)) := by gcongr
    _ = C ^ 2 * (1 + r ^ p) ^ 2 := by ring
    _ ≤ C ^ 2 * (2 * (1 + r ^ (2 * p))) :=
      mul_le_mul_of_nonneg_left hsquare (sq_nonneg C)
    _ = 2 * C ^ 2 * (1 + r ^ (2 * p)) := by ring

/-- Rewrites the covariance integral against `multivariateGaussian 0 K` as an integral against the
fixed reference measure `stdGaussian`, with all `K`-dependence isolated in `CFC.sqrt K`. This is
the measure-theoretic reduction step behind `continuousWithinAt_covarianceMap`: once the reference
measure no longer depends on `K`, continuity in `K` becomes an ordinary dominated-convergence
argument in the integrand. -/
private lemma integral_activationProduct_multivariateGaussian_eq_stdGaussian
    {m : ℕ} (φ : ℝ → ℝ) (hφ_cont : Continuous φ) (K : Matrix (Fin m) (Fin m) ℝ) (α β : Fin m) :
    ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K) =
      ∫ x : EuclideanSpace ℝ (Fin m),
        φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) x).ofLp α) *
          φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) x).ofLp β) ∂stdGaussian _ := by
  rw [multivariateGaussian, integral_map]
  · simp
  · exact (by fun_prop : AEMeasurable (fun x : EuclideanSpace ℝ (Fin m) =>
      0 + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) x) (stdGaussian _))
  · exact (hφ_cont.measurable.comp
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable).mul
      (hφ_cont.measurable.comp
        (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable) |>.aestronglyMeasurable

/-- **
The claim: `K ↦ 𝒞_φ(K) := fun α β => ∫ z, φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)`
is continuous *within the positive-semidefinite cone* at every
`K0 : Matrix (Fin m) (Fin m) ℝ` in that cone — in particular at singular / rank-deficient `K0`,
not only at positive-definite ones. The relative formulation is essential: Mathlib deliberately
defines `multivariateGaussian 0 K` as a Dirac measure for non-PSD `K`, so ambient continuity at a
nonzero singular PSD matrix would be false. In the Part 1 induction this theorem turns
`Φ_ℓ^{(n)} → Φ_ℓ` into `𝒞_φ(Φ_ℓ^{(n)}) → 𝒞_φ(Φ_ℓ)` through
`tendstoInMeasure_comp_of_continuousWithinAt` and the PSD invariant.

**Why this should be true in general, not just for positive-definite `K`**: the underlying
mathematical fact is standard on the *whole* PSD cone. Mathlib's own
`multivariateGaussian μ S = (stdGaussian _).map (μ + toEuclideanCLM (CFC.sqrt S))`
(`Mathlib.Probability.Distributions.Gaussian.Multivariate`) rewrites the integral above as an
integral against a *fixed* reference measure `stdGaussian` with a `K`-dependent integrand built from
`CFC.sqrt K`, so continuity in `K` reduces to: (a) continuity of `K ↦ CFC.sqrt K` on all PSD
matrices — a soft continuous-functional-calculus fact about the whole operator, which survives
eigenvalue collisions/rank drops even though the individual eigenprojections are *not* continuous
there — composed with continuity of `φ`; plus (b) the Dominated Convergence Theorem, with
domination supplied by `φ`'s polynomial growth exactly as in
`memLp_activation_coordinate_of_polynomial_growth`. The measure-theoretic reduction is
`integral_activationProduct_multivariateGaussian_eq_stdGaussian`, the linear-algebra bound is
`abs_toEuclideanCLM_ofLp_le`, and the growth bound on the integrand is
`abs_mul_le_of_polynomial_growth`.
-/
theorem continuousWithinAt_covarianceMap (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (m : ℕ) (K0 : Matrix (Fin m) (Fin m) ℝ) (hK0 : K0.PosSemidef) :
    ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ => fun α β : Fin m =>
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))
      {K | K.PosSemidef} K0 := by
  rw [continuousWithinAt_pi]
  intro α
  rw [continuousWithinAt_pi]
  intro β
  let : CompleteSpace (Matrix (Fin m) (Fin m) ℝ) := FiniteDimensional.complete ℝ _
  have hsqrt : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ => CFC.sqrt K)
      {K | K.PosSemidef} K0 := by
    have hsqrt' : ContinuousOn (fun K : Matrix (Fin m) (Fin m) ℝ => CFC.sqrt K)
        {K | K.PosSemidef} := by
      simpa only [Matrix.nonneg_iff_posSemidef] using
        (@CFC.continuousOn_sqrt (Matrix (Fin m) (Fin m) ℝ) _ _ _ _ _ _ _ _ _ _)
    exact hsqrt' K0 hK0
  let R : ℝ := ‖CFC.sqrt K0‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hnorm : ∀ᶠ K : Matrix (Fin m) (Fin m) ℝ in nhdsWithin K0 {K | K.PosSemidef},
      ‖CFC.sqrt K‖ < R := by
    have hnorm_tendsto : Filter.Tendsto (fun K : Matrix (Fin m) (Fin m) ℝ => ‖CFC.sqrt K‖)
        (nhdsWithin K0 {K | K.PosSemidef}) (nhds ‖CFC.sqrt K0‖) := hsqrt.norm
    exact hnorm_tendsto.eventually (show ∀ᶠ x : ℝ in nhds ‖CFC.sqrt K0‖, x < R from by
      apply eventually_lt_nhds
      dsimp [R]
      linarith)
  have h_integrable : Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
      2 * C ^ 2 * (1 + R ^ (2 * p) * ‖z‖ ^ (2 * p))) (stdGaussian _) := by
    have hmoment : Integrable (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖ ^ (2 * p))
        (stdGaussian _) := by
      simpa only [id_eq] using
        (ProbabilityTheory.IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin m)))
          ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top (2 * p))).integrable_norm_pow
          (by omega)
    exact ((integrable_const (1 : ℝ)).add (hmoment.const_mul (R ^ (2 * p)))).const_mul
      (2 * C ^ 2)
  simp_rw [integral_activationProduct_multivariateGaussian_eq_stdGaussian φ hφ_cont]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun z : EuclideanSpace ℝ (Fin m) =>
      2 * C ^ 2 * (1 + R ^ (2 * p) * ‖z‖ ^ (2 * p)))
  · filter_upwards with K
    exact ((hφ_cont.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).comp
        (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K)).continuous)).mul
      (hφ_cont.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).comp
          (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K)).continuous))).aestronglyMeasurable
  · filter_upwards [hnorm] with K hK
    filter_upwards with z
    rw [Real.norm_eq_abs]
    have hα : |(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp α| ≤ R * ‖z‖ :=
      (abs_toEuclideanCLM_ofLp_le (CFC.sqrt K) z α).trans
        (mul_le_mul_of_nonneg_right (le_of_lt hK) (norm_nonneg z))
    have hβ : |(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp β| ≤ R * ‖z‖ :=
      (abs_toEuclideanCLM_ofLp_le (CFC.sqrt K) z β).trans
        (mul_le_mul_of_nonneg_right (le_of_lt hK) (norm_nonneg z))
    simpa [mul_pow] using
      (abs_mul_le_of_polynomial_growth φ C hC p hφ_growth _ _ (R * ‖z‖)
        (mul_nonneg hR (norm_nonneg z)) hα hβ)
  · exact h_integrable
  · filter_upwards with z
    have hlinear : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ =>
        toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z) {K | K.PosSemidef} K0 := by
      have hpair : ContinuousWithinAt
          (fun K : Matrix (Fin m) (Fin m) ℝ => (CFC.sqrt K, z)) {K | K.PosSemidef} K0 :=
        hsqrt.prodMk continuousWithinAt_const
      change ContinuousWithinAt
        ((fun p : Matrix (Fin m) (Fin m) ℝ × EuclideanSpace ℝ (Fin m) =>
          toEuclideanCLM (𝕜 := ℝ) p.1 p.2) ∘ fun K => (CFC.sqrt K, z))
        {K | K.PosSemidef} K0
      exact continuous_uncurry_toEuclideanCLM.continuousAt.continuousWithinAt.comp hpair
        (Set.mapsTo_univ _ _)
    have hα : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ =>
        φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp α)) {K | K.PosSemidef} K0 := by
      exact hφ_cont.continuousAt.continuousWithinAt.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).continuousAt.continuousWithinAt.comp
          hlinear (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
    have hβ : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ =>
        φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp β)) {K | K.PosSemidef} K0 := by
      exact hφ_cont.continuousAt.continuousWithinAt.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).continuousAt.continuousWithinAt.comp
          hlinear (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
    exact hα.mul hβ

/-- The conditional second-moment matrix of activated Gaussian coordinates is continuous on the
positive-semidefinite cone.  This is `continuousWithinAt_covarianceMap` applied to `φ²`, with the
entries normalized back to the form used by the conditional Chebyshev estimate. -/
theorem continuousWithinAt_activationProductSq
    (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (_hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (m : ℕ) (K0 : Matrix (Fin m) (Fin m) ℝ) (hK0 : K0.PosSemidef) :
    ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ => fun α β : Fin m =>
      ∫ z : EuclideanSpace ℝ (Fin m),
        (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K)
      {K | K.PosSemidef} K0 := by
  have hφsq_growth : ∀ x : ℝ, |φ x ^ 2| ≤ (2 * C ^ 2) * (1 + |x| ^ (2 * p)) := by
    intro x
    have hpow : |x| ^ (2 * p) = (|x| ^ p) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    have hsq : (1 + |x| ^ p) ^ 2 ≤ 2 * (1 + |x| ^ (2 * p)) := by
      rw [hpow]
      nlinarith [sq_nonneg (|x| ^ p - 1)]
    calc
      |φ x ^ 2| = |φ x| ^ 2 := by rw [abs_pow]
      _ ≤ (C * (1 + |x| ^ p)) ^ 2 := by
        nlinarith [hφ_growth x, abs_nonneg (φ x),
          mul_nonneg _hC (by positivity)]
      _ = C ^ 2 * (1 + |x| ^ p) ^ 2 := by ring
      _ ≤ C ^ 2 * (2 * (1 + |x| ^ (2 * p))) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
      _ = (2 * C ^ 2) * (1 + |x| ^ (2 * p)) := by ring
  have hcont := continuousWithinAt_covarianceMap (fun x : ℝ => φ x ^ 2)
    (hφ_cont.pow 2) (2 * C ^ 2) (by positivity) (2 * p) (by omega) hφsq_growth m K0 hK0
  simpa only [pow_two, mul_mul_mul_comm] using hcont

end CovarianceMapContinuity

end DeepNNGPRecursion

section Theorem1

/-- **Step 5 / Theorem 1 (Exact Conditional Normality)**:
Conditional on the input weights `W` (the sub-$\sigma$-algebra $\mathcal{F}$), the output
vector `f_m(W, a)` under the readout distribution is an exact centered multivariate Gaussian:
  `f_m | ℱ ~ 𝒩(0, Φ^{(n)})`.

Informal proof:
By the Cramér-Wold device (extensionality of characteristic functions in Mathlib),
two finite measures are equal if their Fourier transforms (characteristic functions) coincide.
For every projection vector `t ∈ EuclideanSpace ℝ (Fin m)`, the characteristic function of the
pushforward measure is computed via the 1D projection theorem to be
`exp(- (1/2) t ⬝ᵥ Φ^{(n)} *ᵥ t)`. This matches the characteristic function of Mathlib's
`multivariateGaussian 0 Φ^{(n)}` exactly, proving Theorem 1. -/
theorem exact_conditional_normality
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Measure.map (fun a => evalVector φ W a X) (gaussianReadoutMeasure n) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (empiricalCovariance n φ W X) := by
  have hPos : (empiricalCovariance n φ W X).PosSemidef :=
    empiricalCovariance_posSemidef n φ W X
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_readout_evalVector, charFun_multivariateGaussian hPos]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]

/-- The conditional distribution of the output vector satisfies `IsGaussian`. -/
instance isGaussian_conditional_output
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    IsGaussian (Measure.map (fun a => evalVector φ W a X) (gaussianReadoutMeasure n)) := by
  rw [exact_conditional_normality]
  infer_instance


/-- **Definition 2.2 (Gaussian Process)**:
Conditional on input weights `W`, the scalar random network output function
`x ↦ evalSingle φ W a x` under the readout measure `gaussianReadoutMeasure n`
is an exact Gaussian process in the sense of Mathlib's `ProbabilityTheory.IsGaussianProcess`. -/
theorem isGaussianProcess_exact_conditional_output
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) :
    ProbabilityTheory.IsGaussianProcess
      (fun (x : Fin d → ℝ) (a : Fin n → ℝ) => evalSingle φ W a x)
      (gaussianReadoutMeasure n) where
  hasGaussianLaw I := by
    let e := Fintype.equivFin I
    let X : Fin (Fintype.card I) → Fin d → ℝ := fun α => (e.symm α).1
    have h_gauss : HasGaussianLaw (fun a => evalVector φ W a X) (gaussianReadoutMeasure n) :=
      ⟨(evalVector_measurable φ W X).aemeasurable, isGaussian_conditional_output φ W X⟩
    let L : EuclideanSpace ℝ (Fin (Fintype.card I)) →L[ℝ] (I → ℝ) :=
      { toFun := fun v i => v.ofLp (e i)
        map_add' := fun u v => by ext i; simp
        map_smul' := fun c v => by ext i; simp }
    have h_eq : (fun a => I.restrict (fun x => evalSingle φ W a x)) =
        (fun a => L (evalVector φ W a X)) := by
      ext a i
      simp [L, X, evalVector]
    rw [h_eq]
    exact h_gauss.map L


end Theorem1

section Theorem2

/-- **Theorem 2 (Full Matrix Strong Law of Large Numbers for the Covariance Tensor)**:
As width `n → ∞`, the empirical covariance matrix converges almost surely to the deterministic
limiting NNGP Gram matrix in `Matrix (Fin m) (Fin m) ℝ`:
  `Φ^{(n)} →_as (fun α β => 𝔼_{w ~ 𝒩(0, I_d)}[φ(w ⬝ᵥ X α) φ(w ⬝ᵥ X β)])`. -/
theorem empiricalCovariance_tendsto_matrix_integral
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
      Filter.Tendsto
        (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X)
        Filter.atTop
        (nhds ((fun α β => ∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) : Matrix (Fin m) (Fin m) ℝ)) := by
  have h_entry : ∀ α β : Fin m,
      ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
        Filter.Tendsto
          (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X α β)
          Filter.atTop
          (nhds (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d))) :=
    fun α β => empiricalCovariance_tendsto_integral φ X hφ_meas hφ_L2 α β
  have h_all :
      ∀ᵐ rows : ℕ → Fin d → ℝ ∂(Measure.infinitePi fun _ => gaussianRowMeasure d),
        ∀ α β : Fin m,
          Filter.Tendsto
            (fun n : ℕ => empiricalCovariance n φ (fun i => rows i.val) X α β)
            Filter.atTop
            (nhds (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d))) := by
    simp_rw [ae_all_iff]
    exact h_entry
  filter_upwards [h_all] with rows hrows
  exact tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => hrows α β

end Theorem2

section Theorem3

/-- **Theorem 3 (Weak Convergence of Output Measure to NNGP Limit)**:
As width `n → ∞`, the joint distribution of network outputs across evaluation points
converges weakly to the multivariate Gaussian distribution `𝒩(0, Φ^{(∞)})`:
  `outputMeasure n d φ X →_w 𝒩(0, Φ^{(∞)})`. -/
theorem outputMeasure_tendsto_multivariateGaussian
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d)) :
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
* Step 1: By `charFun_readout_evalVector`, the conditional characteristic function given input weights
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) => evalVector φ p.1 p.2 X)
      Filter.atTop
      id
      (fun n => initMeasure n d)
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
      (gaussianRowMeasure d)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))
      Filter.atTop
      id
      (fun n => initMeasure n d)
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
      (gaussianRowMeasure d)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) - y)
      Filter.atTop
      (fun G => G - y)
      (fun n => initMeasure n d)
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d)) :
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
      (gaussianRowMeasure d)) :
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
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (u : Fin m → ℝ) :
    Filter.Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ => ⟨Measure.map (fun p => ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α)) (initMeasure n d),
        isProbabilityMeasure_map_projection n d φ hφ_meas X u⟩)
      Filter.atTop
      (nhds ⟨gaussianReal 0 (Real.toNNReal (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u)), inferInstance⟩) := by
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
* Step 3: `conditionalVariance_tendsto_limitingVariance_ae` proves `u ⬝ᵥ Φ^{(n)} *ᵥ u →_as u ⬝ᵥ Φ^{(∞)} *ᵥ u`.
* Step 4: `charFun_map_projection` evaluates the unconditional characteristic function as
  `𝔼_W [exp(- (t²/2) u ⬝ᵥ Φ^{(n)} *ᵥ u)]`.
* Step 5: `tendsto_charFun_map_projection` uses Dominated Convergence to show that the characteristic
  function converges to `exp(- (t²/2) u ⬝ᵥ Φ^{(∞)} *ᵥ u)`.
* Step 6: `tendstoInDistribution_projection` concludes convergence in distribution by Lévy's
  Continuity Theorem (`ProbabilityMeasure.tendsto_of_tendsto_charFun`). -/
theorem tendstoInDistribution_projection
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (u : Fin m → ℝ) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) => ∑ α : Fin m, u α * evalSingle φ p.1 p.2 (X α))
      Filter.atTop
      id
      (fun n => initMeasure n d)
      (gaussianReal 0 (Real.toNNReal (u ⬝ᵥ (limitingCovariance φ X) *ᵥ u))) where
  forall_aemeasurable n := (projection_joint_measurable φ hφ_meas X u).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    convert! map_projection_tendsto_gaussianReal φ X hφ_meas hφ_L2 u
    exact Subtype.ext Measure.map_id

end Theorem3

section MultilayerSequentialNNGP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency.types false in
theorem tendstoInDistribution_sequential_preactivation
    (σw σb : ℝ) (m : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) K)]
    (hK_pos : K.PosSemidef)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) :
    TendstoInDistribution
      (fun n (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
          ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
      Filter.atTop id
      (fun n => (Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
        ((gaussianReadoutMeasure n).prod (gaussianReal 0 1)))
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
          ((gaussianReadoutMeasure n).prod (gaussianReal 0 1))) :=
      (measurable_sequential_preactivation σw σb n m φ hφ_meas).aemeasurable
    have h_weak : Filter.Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
        (fun n : ℕ => ⟨Measure.map
          (fun (p : (ℕ → EuclideanSpace ℝ (Fin m)) × ((Fin n → ℝ) × ℝ)) =>
            WithLp.toLp 2 fun α : Fin m => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
              ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
          ((Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
            ((gaussianReadoutMeasure n).prod (gaussianReal 0 1))),
          (Measure.isProbabilityMeasure_map_iff (h_meas n)).mpr inferInstance⟩)
        Filter.atTop
        (nhds ⟨multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin m),
            φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)), inferInstance⟩) := by
      apply ProbabilityMeasure.tendsto_of_tendsto_charFun
      intro t
      exact tendsto_charFun_sequential_preactivation_multivariate σw σb m φ hφ_meas K hK_pos hφ_L2 t
    convert! h_weak
    exact Measure.map_id

set_option backward.isDefEq.respectTransparency.types false in
/-- **Sequential Multilayer NNGP Limit (Bivariate Corollary)**:
For two evaluation points `m = 2`, the joint layer-to-layer preactivation vector converges in
distribution to the centered bivariate Gaussian with covariance determined by the limiting
recurrence `fun α β => σb ^ 2 + σw ^ 2 * ∫ z, φ (z.ofLp α) * φ (z.ofLp β) d𝒩(0, K)`. -/
theorem tendstoInDistribution_sequential_bivariate
    (σw σb : ℝ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (K : Matrix (Fin 2) (Fin 2) ℝ)
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) K)]
    (hK_pos : K.PosSemidef)
    (hφ_L2 : ∀ α : Fin 2, MemLp (fun z : EuclideanSpace ℝ (Fin 2) => φ (z.ofLp α)) 2
      (multivariateGaussian 0 K)) :
    TendstoInDistribution
      (fun n (p : (ℕ → EuclideanSpace ℝ (Fin 2)) × ((Fin n → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin 2 => σb * p.2.2 + (σw * (n : ℝ)⁻¹.sqrt) *
          ∑ j : Fin n, p.2.1 j * φ ((p.1 j.val).ofLp α))
      Filter.atTop id
      (fun n => (Measure.infinitePi fun _ : ℕ => multivariateGaussian 0 K).prod
        ((gaussianReadoutMeasure n).prod (gaussianReal 0 1)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        (fun α β => σb ^ 2 + σw ^ 2 * ∫ z : EuclideanSpace ℝ (Fin 2),
          φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))) :=
  tendstoInDistribution_sequential_preactivation σw σb 2 φ hφ_meas K hK_pos hφ_L2

end MultilayerSequentialNNGP

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

/-- **Deterministic recursive forward kernel.**  At every fixed depth `ℓ`, an i.i.d. conditional
Gaussian layer with covariance `layerCovarianceSeq 1 0 φ m Φ0 ℓ` has empirical activated
covariance converging in probability to the next deterministic forward kernel. -/
theorem conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq
    (m ℓ : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 ℓ))
      (fun n : ℕ => fun (Z : ℕ → EuclideanSpace ℝ (Fin m)) => fun α β : Fin m =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m Φ0 (ℓ + 1)) := by
  simpa [layerCovarianceSeq] using
    (conditional_empiricalCovariance_tendstoInMeasure_of_polynomial_growth
      m φ hφ_cont C hC p hp hφ_growth
        (layerCovarianceSeq 1 0 φ m Φ0 ℓ))

/-- The input layer is an exact transport of the reusable i.i.d.-Gaussian empirical-covariance
theorem.  Keeping this bridge separate makes the base case of the deep recursion independent of
the representation of the input weights. -/
lemma input_empiricalCovariance_tendstoInMeasure
    (d m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p)) (X : Fin m → Fin d → ℝ) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun W : ℕ → ℕ → ℝ => fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X α k) *
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X β k))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1) := by
  let Z : (ℕ → ℕ → ℝ) → ℕ → EuclideanSpace ℝ (Fin m) :=
    fun W j => WithLp.toLp 2 fun α =>
      (d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j k.val * X α k
  have hZ_meas : Measurable Z := by
    refine measurable_pi_iff.2 fun j => ?_
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.2 fun α => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact ((measurable_pi_apply k.val).comp (measurable_pi_apply j)).mul_const _
  have hZ_map : Measure.map Z
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
    simpa [Z] using map_infinitePi_input_preactivations d m X
  let f : ℕ → (ℕ → EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ :=
    fun n z α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ ((z j.val).ofLp α) * φ ((z j.val).ofLp β)
  let g : (ℕ → EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ :=
    fun _ => layerCovarianceSeq 1 0 φ m
      (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1
  have hf_meas : ∀ n, Measurable (f n) := by
    intro n
    refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact
      (hφ_cont.measurable.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable.comp
          (measurable_pi_apply j.val))).mul
      (hφ_cont.measurable.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable.comp
          (measurable_pi_apply j.val)))
  have hbase := conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq
    m 0 φ hφ_cont C hC p hp hφ_growth
      (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β))
  have htransport := tendstoInMeasure_comp_measurePreserving
    (E := Fin m → Fin m → ℝ) hbase
    ({ measurable := hZ_meas, map_eq := hZ_map } : MeasurePreserving Z
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℕ => multivariateGaussian 0
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) hf_meas
      (measurable_const : Measurable g)
  simpa [f, g, Z] using htransport

/-- The layer-zero case of the deep covariance recursion.  This is the input empirical-covariance
transport composed with evaluation of the first independent layer population. -/
lemma deepEmpiricalCovariance_zero_tendstoInMeasure
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (hL : 0 < L) :
    TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) 0 α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) 0 β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1) := by
  let T : (Fin L → ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ := fun w => w ⟨0, hL⟩
  have hT : MeasurePreserving T
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
    simpa [T] using
      (measurePreserving_eval (fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) ⟨0, hL⟩)
  have hbase := input_empiricalCovariance_tendstoInMeasure d m φ hφ_cont C hC p hp hφ_growth X
  have hf : ∀ n : ℕ, Measurable (fun W : ℕ → ℕ → ℝ => fun α β : Fin m =>
      (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X α k) *
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X β k)) := by
    intro n
    refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact
      (hφ_cont.measurable.comp
        (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
          ((measurable_pi_apply k.val).comp (measurable_pi_apply j.val)).mul_const _))).mul
      (hφ_cont.measurable.comp
        (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
          ((measurable_pi_apply k.val).comp (measurable_pi_apply j.val)).mul_const _)))
  have htransport := tendstoInMeasure_comp_measurePreserving
    (E := Fin m → Fin m → ℝ) hbase hT hf
      (measurable_const : Measurable fun _ : ℕ → ℕ → ℝ =>
        layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1)
  simpa [T, deepPreactivation, hL, dotProduct] using htransport

/-- Restricting an infinite independent Gaussian weight population to its first `n` rows and
columns gives the finite conditional Gaussian layer law.  This is the raw-population counterpart
of `conditional_preactivations_eq_pi`; keeping it separate avoids rebuilding finite restrictions
inside the depth induction. -/
lemma conditional_preactivations_infinite_eq_pi (n m : ℕ) (φ : ℝ → ℝ)
    (H : Fin n → EuclideanSpace ℝ (Fin m)) :
    Measure.map
      (fun W : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j.val k.val * φ ((H k).ofLp α))
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ k : Fin n,
            φ ((H k).ofLp α) * φ ((H k).ofLp β))) := by
  let restrictColumns : (ℕ → ℕ → ℝ) → (ℕ → Fin n → ℝ) :=
    fun W j k => W j k.val
  have hrestrictColumns_meas : Measurable restrictColumns := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => ?_
    exact (measurable_pi_apply k.val).comp (measurable_pi_apply j)
  have hrestrictColumns : Measure.map restrictColumns
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ => gaussianRowMeasure n := by
    calc
      Measure.map restrictColumns
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
        Measure.infinitePi fun _ : ℕ =>
          Measure.map (fun r : ℕ → ℝ => fun k : Fin n => r k.val)
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
          simpa [restrictColumns] using
            (Measure.infinitePi_map_pi
              (μ := fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
              (f := fun _ (r : ℕ → ℝ) (k : Fin n) => r k.val)
              (fun _ => measurable_pi_iff.2 fun k => measurable_pi_apply k.val))
      _ = Measure.infinitePi fun _ : ℕ => gaussianRowMeasure n := by
        congr 1
        funext j
        rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
          Measure.infinitePi_eq_pi]
        rfl
  let restrictRows : (ℕ → Fin n → ℝ) → (Fin n → Fin n → ℝ) :=
    fun W j k => W j.val k
  have hrestrictRows_meas : Measurable restrictRows := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => ?_
    exact (measurable_pi_apply k).comp (measurable_pi_apply j.val)
  have hrestrictRows : Measure.map restrictRows
      (Measure.infinitePi fun _ : ℕ => gaussianRowMeasure n) = gaussianInit n n := by
    exact map_infinitePi_rows_eq_gaussianInit n n
  let F : (Fin n → Fin n → ℝ) → Fin n → EuclideanSpace ℝ (Fin m) :=
    fun W j => WithLp.toLp 2 fun α =>
      (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j k * φ ((H k).ofLp α)
  have hF_meas : Measurable F := by
    refine measurable_pi_iff.2 fun j => ?_
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.2 fun α => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact ((measurable_pi_apply k).comp (measurable_pi_apply j)).mul_const _
  have hcomp : F ∘ restrictRows ∘ restrictColumns =
      fun W : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j.val k.val * φ ((H k).ofLp α) := rfl
  rw [← hcomp]
  calc
    Measure.map ((F ∘ restrictRows) ∘ restrictColumns)
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.map (F ∘ restrictRows)
        (Measure.map restrictColumns
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
        rw [← Measure.map_map (hF_meas.comp hrestrictRows_meas) hrestrictColumns_meas]
    _ = Measure.map (F ∘ restrictRows) (Measure.infinitePi fun _ : ℕ => gaussianRowMeasure n) := by
      rw [hrestrictColumns]
    _ = Measure.map F (Measure.map restrictRows
        (Measure.infinitePi fun _ : ℕ => gaussianRowMeasure n)) := by
      rw [← Measure.map_map hF_meas hrestrictRows_meas]
    _ = Measure.map F (gaussianInit n n) := by rw [hrestrictRows]
    _ = Measure.pi (fun _ : Fin n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ k : Fin n,
            φ ((H k).ofLp α) * φ ((H k).ofLp β))) :=
      conditional_preactivations_eq_pi n n m φ H

/-- With all preceding populations fixed, a fresh infinite population produces an i.i.d. Gaussian
next preactivation layer.  This is the `deepPreactivation` specialization of
`conditional_preactivations_infinite_eq_pi`; it is the conditional-law bridge for the successor
step of the deep covariance induction. -/
lemma conditional_deepPreactivation_succ_infinite_eq_pi
    (d m n : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (W : ℕ → ℕ → ℕ → ℝ) (ℓ : ℕ) :
    Measure.map
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        deepPreactivation d m n φ X
          (fun k => if _ : k ≤ ℓ then W k else if k = ℓ + 1 then V else 0) (ℓ + 1) α j)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin n => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ k : Fin n,
          φ (deepPreactivation d m n φ X W ℓ α k) *
          φ (deepPreactivation d m n φ X W ℓ β k))) := by
  let Wnext : (ℕ → ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ :=
    fun V k => if _ : k ≤ ℓ then W k else if k = ℓ + 1 then V else 0
  have hprevious : ∀ V : ℕ → ℕ → ℝ,
      deepPreactivation d m n φ X (Wnext V) ℓ = deepPreactivation d m n φ X W ℓ := by
    intro V
    apply deepPreactivation_congr_of_eqOn d m n φ X (Wnext V) W ℓ
    intro k hk
    simp [Wnext, hk]
  let H : Fin n → EuclideanSpace ℝ (Fin m) := fun k => WithLp.toLp 2 fun α : Fin m =>
    deepPreactivation d m n φ X W ℓ α k
  have hmap :
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        deepPreactivation d m n φ X (Wnext V) (ℓ + 1) α j) =
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, V j.val k.val * φ ((H k).ofLp α)) := by
    funext V j
    congr 1
    funext α
    simp only [deepPreactivation]
    rw [show Wnext V (ℓ + 1) = V by simp [Wnext]]
    rw [hprevious V]
  rw [show (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
      deepPreactivation d m n φ X
        (fun k => if _ : k ≤ ℓ then W k else if k = ℓ + 1 then V else 0) (ℓ + 1) α j) =
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        deepPreactivation d m n φ X (Wnext V) (ℓ + 1) α j) by rfl, hmap]
  simpa only [H, WithLp.ofLp_toLp] using
    conditional_preactivations_infinite_eq_pi n m φ H

end AsymptoticEmpiricalCovariancePropagation

section DeepNNGPRecursion

/-! ## Theorem 2.13 (Deep NNGP Recursion): Main Theorems

The ambient probability space throughout is the joint depth-`L` initialization measure built in
the first `DeepNNGPRecursion` section: a `Fin L`-indexed family of mutually independent, i.i.d.
standard-Gaussian layer weight populations `q.1 : Fin L → ℕ → ℕ → ℝ` (layer `0` doubling as the
input weight matrix, restricted to its first `d` columns — see `deepPreactivation`), together with
a readout population. `deepPreactivation`'s `W : ℕ → ℕ → ℕ → ℝ` argument is recovered from
`q.1 : Fin L → ℕ → ℕ → ℝ` by extending with the junk value `0` past layer `L`
(`fun k => if h : k < L then q.1 ⟨k, h⟩ else 0`), written out at each site below rather than named,
per the same "no extra top-level definitions" preference as the network construction above. -/

-- The base Gram matrix `(d)⁻¹ * (X α ⬝ᵥ X β)` built from the evaluation points is positive
-- semidefinite: the `σw = 1, σb = 0` case of `empirical_layer_covariance_posSemidef_multivariate`,
-- applied to the input rows themselves rather than to activated preactivations.
private lemma inputGramMatrix_posSemidef (d m : ℕ) (X : Fin m → Fin d → ℝ) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)).PosSemidef := by
  simpa [dotProduct] using
    empirical_layer_covariance_posSemidef_multivariate 1 0 d m (fun k α => X α k)

/-- Given that the seed matrix `Φ0` is positive semidefinite, every term of the recursive
covariance sequence `layerCovarianceSeq 1 0 φ m Φ0` is itself positive semidefinite, and the
corresponding Gaussian activation coordinates are square-integrable. Both facts are always needed
together (to invoke `continuousWithinAt_covarianceMap` at the next depth, and to bound the
characteristic-function integrand), so they are bundled here rather than re-derived at each of the
two sites below that need them. -/
private lemma memLp_and_posSemidef_layerCovarianceSeq_of_polynomial_growth
    (m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) (hΦ0 : Φ0.PosSemidef) :
    (∀ r : ℕ, ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 r))) ∧
      ∀ r : ℕ, (layerCovarianceSeq 1 0 φ m Φ0 r).PosSemidef := by
  have hφ_L2 : ∀ r : ℕ, ∀ α : Fin m,
      MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 r)) := fun r α =>
    memLp_activation_coordinate_of_polynomial_growth m (layerCovarianceSeq 1 0 φ m Φ0 r) φ
      hφ_cont.measurable C hC p hp hφ_growth α
  exact ⟨hφ_L2, layerCovarianceSeq_posSemidef 1 0 φ hφ_cont.measurable m Φ0 hΦ0 hφ_L2⟩

/-- **Theorem 2.13, Part 1 (Covariance Convergence in Probability).** As width `n → ∞`, the
empirical covariance of the depth-`L` network's layer-`(ℓ+1)` post-activations converges in
probability to the deterministic recursive kernel `layerCovarianceSeq 1 0 φ m Φ0 (ℓ + 1)`, where
`Φ0 α β := (d:ℝ)⁻¹ * (X α ⬝ᵥ X β)` is the base Gram matrix.

The base-layer transport is `input_empiricalCovariance_tendstoInMeasure`.  The remaining proof
must package the conditional Gaussian product law for a layer whose preceding empirical covariance
is random, then combine its conditional Chebyshev bound with the relative continuous-mapping
theorem. -/
theorem deepEmpiricalCovariance_tendstoInMeasure
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (hℓ : ℓ < L) :
    TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (ℓ + 1)) := by
  induction ℓ with
  | zero =>
      exact deepEmpiricalCovariance_zero_tendstoInMeasure d m L φ hφ_cont C hC p hp
        hφ_growth X (Nat.zero_lt_of_lt hℓ)
  | succ ℓ ih =>
      have hℓ' : ℓ < L := by omega
      have hprevious := ih hℓ'
      obtain ⟨hφ_L2, hlimit_pos⟩ := memLp_and_posSemidef_layerCovarianceSeq_of_polynomial_growth
        m φ hφ_cont C hC p hp hφ_growth
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (inputGramMatrix_posSemidef d m X)
      have hempirical_pos : ∀ (n : ℕ) (w : Fin L → ℕ → ℕ → ℝ),
          (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
            φ (deepPreactivation d m n φ X
              (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
            φ (deepPreactivation d m n φ X
              (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j)).PosSemidef := by
        intro n w
        simpa using empirical_layer_covariance_posSemidef_multivariate 1 0 n m
          (fun j α => φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j))
      have hmapped := tendstoInMeasure_comp_of_continuousWithinAt hprevious hempirical_pos
        (continuousWithinAt_covarianceMap φ hφ_cont C hC p hp hφ_growth m
          (layerCovarianceSeq 1 0 φ m
            (show Matrix (Fin m) (Fin m) ℝ from
              fun α β => (d : ℝ)⁻¹ * ∑ k : Fin d, X α k * X β k) (ℓ + 1))
          (hlimit_pos (ℓ + 1)))
      have hmean : TendstoInMeasure
          (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
          (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ => fun α β : Fin m =>
            ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂
              multivariateGaussian 0 (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
                φ (deepPreactivation d m n φ X
                  (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
                φ (deepPreactivation d m n φ X
                  (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j)))
          Filter.atTop
          (fun _ => layerCovarianceSeq 1 0 φ m
            (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (ℓ + 1 + 1)) := by
        simpa [layerCovarianceSeq, dotProduct] using hmapped
      apply tendstoInMeasure_trans ?_ hmean
      intro ε hε
      refine tendsto_matrixTail_of_tendsto_entrywise m ?_ ε hε
      intro α β δ hδ
      sorry

/-- Bridge: pushforward of the infinite real population restricted to `Fin n` coordinates is
`gaussianReadoutMeasure n`. Mirrors `map_infinitePi_rows_eq_gaussianInit`. -/
lemma map_infinitePi_real_eq_gaussianReadoutMeasure (n : ℕ) :
    Measure.map (fun (rows : ℕ → ℝ) (i : Fin n) => rows i.val)
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) = gaussianReadoutMeasure n := by
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

/-- Measurability of `deepPreactivation` as a function of the layer-weight population, for fixed
width `n` and layer `ℓ`. -/
lemma measurable_deepPreactivation (d m n L : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (α : Fin m) (j : Fin n) :
    Measurable (fun w : Fin L → ℕ → ℕ → ℝ =>
      deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) := by
  have h_coord : ∀ ℓ0 : ℕ, Measurable
      (fun w : Fin L → ℕ → ℕ → ℝ => (if h : ℓ0 < L then w ⟨ℓ0, h⟩ else 0)) := by
    intro ℓ0
    by_cases hℓ0 : ℓ0 < L
    · simpa [hℓ0] using measurable_pi_apply (⟨ℓ0, hℓ0⟩ : Fin L)
    · simp [hℓ0]
  induction ℓ generalizing α j with
  | zero =>
    simp only [deepPreactivation]
    unfold dotProduct
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact ((measurable_pi_apply k.val).comp
      ((measurable_pi_apply j.val).comp (h_coord 0))).mul_const _
  | succ ℓ ih =>
    simp only [deepPreactivation]
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact (((measurable_pi_apply k.val).comp
      ((measurable_pi_apply j.val).comp (h_coord (ℓ + 1)))).mul (hφ_meas.comp (ih α k)))

/-- Measurability of the depth-`L` network's width-`n` output map (readout weights times the
final hidden layer's activations, summed and scaled), jointly in the hidden and readout weight
populations. -/
lemma measurable_deepEval (d m L : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (X : Fin m → Fin d → ℝ) (n : ℕ) :
    Measurable (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
      WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
        φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)) := by
  change Measurable ((WithLp.toLp 2) ∘
    (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) α => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
      q.2.1 j.val * φ (deepPreactivation d m n φ X
        (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)))
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun α => ?_)
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  have h_a : Measurable (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) => q.2.1 j.val) :=
    (measurable_pi_apply j.val).comp (measurable_fst.comp measurable_snd)
  have h_φ : Measurable (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) =>
      φ (deepPreactivation d m n φ X (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)) :=
    (hφ_meas.comp (measurable_deepPreactivation d m n L φ hφ_meas X (L - 1) α j)).comp measurable_fst
  exact h_a.mul h_φ

/-- Positive semidefiniteness of the depth-`L` network's width-`n` output covariance (the
`σw = 1`, `σb = 0` case of `empirical_layer_covariance_posSemidef_multivariate`, applied to the
final hidden layer's activations). -/
lemma deepEval_covariance_posSemidef (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin L → ℕ → ℕ → ℝ) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
      φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j)
      ).PosSemidef := by
  simpa using empirical_layer_covariance_posSemidef_multivariate 1 0 n m
    (fun j α => φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))

/-- For a fixed realization `w` of the hidden weights, the pushforward of the readout population
(together with one unused throwaway real coordinate, see `tendstoInDistribution_deepEval`) under
the depth-`L` network's width-`n` output map is exactly the centered multivariate Gaussian with
the width-`n` output covariance — the exact conditional normality of the readout layer
(`exact_conditional_normality_general_multivariate`), transported along
`map_infinitePi_real_eq_gaussianReadoutMeasure` from the infinite readout population down to the
finite-width `gaussianReadoutMeasure n` it is built on. -/
lemma map_deepEval_snd_eq_multivariateGaussian (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin L → ℕ → ℕ → ℝ) :
    Measure.map
      (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
        r.1 j.val * φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
      ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j)) := by
  set H : Fin n → Fin m → ℝ := fun j α =>
    φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j)
    with hH_def
  have h_split : (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
        r.1 j.val * H j α) =
      (fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
        (0 : ℝ) * p.2 + (1 * (n : ℝ)⁻¹.sqrt) * ∑ j : Fin n, p.1 j * H j α) ∘
        (fun r : (ℕ → ℝ) × ℝ => ((fun j : Fin n => r.1 j.val), r.2)) := by
    funext r
    simp only [Function.comp_apply]
    congr 1
    funext α
    ring
  rw [h_split, ← Measure.map_map (by fun_prop) (by fun_prop),
    show (fun r : (ℕ → ℝ) × ℝ => ((fun j : Fin n => r.1 j.val), r.2)) =
      Prod.map (fun (rows : ℕ → ℝ) (j : Fin n) => rows j.val) id from rfl,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    map_infinitePi_real_eq_gaussianReadoutMeasure, Measure.map_id]
  simpa using exact_conditional_normality_general_multivariate 1 0 n m H

/-- **Law of Total Expectation for the depth-`L` network's characteristic function.** The
characteristic function of the width-`n` output distribution is the expectation, over the hidden
weights, of the conditional characteristic function `exp(-t·Φ_L^{(n)}(w)·t/2)` given by
`map_deepEval_snd_eq_multivariateGaussian` and `charFun_multivariateGaussian`. Mirrors
`charFun_outputMeasure`'s proof shape (Fubini on the product measure). -/
lemma charFun_map_deepEval (d m L : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (X : Fin m → Fin d → ℝ)
    (n : ℕ) (t : EuclideanSpace ℝ (Fin m)) :
    charFun (Measure.map
      (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
      ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))) t =
      ∫ w : Fin L → ℕ → ℕ → ℝ, Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ
        (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
        *ᵥ t.ofLp) / 2)
      ∂(Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  have h_meas := measurable_deepEval d m L φ hφ_meas X n
  have h_inner : Measurable (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) =>
      ⟪(WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)
        : EuclideanSpace ℝ (Fin m)), t⟫) :=
    (continuous_id.inner continuous_const).measurable.comp h_meas
  have h_exp_meas : AEStronglyMeasurable
      (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) =>
        Complex.exp (⟪(WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)
          : EuclideanSpace ℝ (Fin m)), t⟫ * Complex.I))
      ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp h_inner).mul_const Complex.I)).aestronglyMeasurable
  rw [charFun_apply, integral_map h_meas.aemeasurable (by fun_prop),
    integral_prod _ (Integrable.of_bound h_exp_meas 1
      (ae_of_all _ fun p => (Complex.norm_exp_ofReal_mul_I _).le))]
  congr 1
  funext w
  have h_meas_w : Measurable (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
      (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, r.1 j.val * φ (deepPreactivation d m n φ X
        (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j)) :=
    h_meas.comp (measurable_const.prodMk measurable_id)
  calc
    (∫ r : (ℕ → ℝ) × ℝ, Complex.exp (⟪(WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
        r.1 j.val * φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) : EuclideanSpace ℝ (Fin m)), t⟫
        * Complex.I) ∂((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))) =
        charFun (Measure.map (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, r.1 j.val * φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
          ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))) t := by
      rw [charFun_apply, integral_map h_meas_w.aemeasurable (by fun_prop)]
    _ = charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))) t := by
      rw [map_deepEval_snd_eq_multivariateGaussian d m n L φ X w]
    _ = Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ (show Matrix (Fin m) (Fin m) ℝ from fun α β =>
          (n : ℝ)⁻¹ * ∑ j : Fin n,
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
          *ᵥ t.ofLp) / 2) := by
      rw [charFun_multivariateGaussian (deepEval_covariance_posSemidef d m n L φ X w)]
      simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub]
      congr 1
      ring

/-- The characteristic integrand for the depth-`L` network's width-`n` output covariance is
bounded by `1` (since the covariance is positive semidefinite). -/
lemma norm_charFun_deepEval_le_one (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin L → ℕ → ℕ → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    ‖Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      *ᵥ t.ofLp) / 2)‖ ≤ 1 :=
  norm_exp_neg_ofReal_div_two_le_one (by
    simpa using empirical_layer_covariance_nonneg_multivariate 1 0 n m
      (fun j α => φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
      t)

/-- Measurability, in the hidden weights `w`, of the depth-`L` network's width-`n` characteristic
integrand. -/
lemma aestronglyMeasurable_charFun_deepEval (d m n L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (X : Fin m → Fin d → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    AEStronglyMeasurable (fun w : Fin L → ℕ → ℕ → ℝ => Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      *ᵥ t.ofLp) / 2))
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  have h_quad : Measurable (fun w : Fin L → ℕ → ℕ → ℝ => t.ofLp ⬝ᵥ
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      *ᵥ t.ofLp) := by
    have h_eq : (fun w : Fin L → ℕ → ℕ → ℝ => t.ofLp ⬝ᵥ
        (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
        *ᵥ t.ofLp) =
        fun w => ∑ α : Fin m, ∑ β : Fin m, t.ofLp α * ((n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
          * t.ofLp β := by
      funext w
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    rw [h_eq]
    refine Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun β _ => ?_
    have h_cov : Measurable (fun w : Fin L → ℕ → ℕ → ℝ => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j)) := by
      refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
      exact (hφ_cont.measurable.comp
          (measurable_deepPreactivation d m n L φ hφ_cont.measurable X (L - 1) α j)).mul
        (hφ_cont.measurable.comp
          (measurable_deepPreactivation d m n L φ hφ_cont.measurable X (L - 1) β j))
    exact (measurable_const.mul h_cov).mul measurable_const
  exact (Complex.measurable_exp.comp
    (((Complex.measurable_ofReal.comp h_quad).neg).div_const 2)).aestronglyMeasurable

/-- Pointwise characteristic function convergence for the depth-`L` network's output under an
arbitrary sequence of empirical covariances converging in measure to the limiting forward kernel.
This decouples the Step 6 output-layer argument from the specific inductive proof of Part 1. -/
lemma tendsto_charFun_map_deepEval_of_covariance_tendsto
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (t : EuclideanSpace ℝ (Fin m))
    (hP : TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) :
    Filter.Tendsto (fun (n : ℕ) => charFun (Measure.map
        (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
        ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
          ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) t)) := by
  obtain ⟨_, hΦr_pos⟩ := memLp_and_posSemidef_layerCovarianceSeq_of_polynomial_growth
    m φ hφ_cont C hC p hp hφ_growth
    (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (inputGramMatrix_posSemidef d m X)
  simp_rw [charFun_map_deepEval d m L φ hφ_cont.measurable X _ t]
  have h_comp := tendstoInMeasure_comp_of_continuousAt hP
    (continuous_charFun_integrand t).continuousAt
    (g := fun M : Matrix (Fin m) (Fin m) ℝ =>
      Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ M *ᵥ t.ofLp) / 2))
  have h_lim := tendsto_integral_of_tendstoInMeasure_of_bounded h_comp
    (fun n => aestronglyMeasurable_charFun_deepEval d m n L φ hφ_cont X t) 1
    (fun n => ae_of_all _ fun w => norm_charFun_deepEval_le_one d m n L φ X w t)
  rw [charFun_multivariateGaussian (hΦr_pos L)]
  simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub, neg_div]
  simpa [integral_const, neg_div] using h_lim

/-- **Pointwise characteristic function convergence for the depth-`L` network's output**
(Theorem 2.13 Part 2, Steps 2-5): combines the Law of Total Expectation
(`charFun_map_deepEval`) with Part 1 (`deepEmpiricalCovariance_tendstoInMeasure`) via the
continuous-mapping and bounded-convergence lemmas. -/
lemma tendsto_charFun_map_deepEval (d m L : ℕ) (hL : 0 < L) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto (fun (n : ℕ) => charFun (Measure.map
        (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
        ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
          ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) t)) := by
  have hL1 : L - 1 + 1 = L := by omega
  have hP1 := deepEmpiricalCovariance_tendstoInMeasure d m L φ hφ_cont C hC p hp hφ_growth X
    (L - 1) (by omega)
  rw [hL1] at hP1
  exact tendsto_charFun_map_deepEval_of_covariance_tendsto d m L φ hφ_cont C hC p hp hφ_growth X t hP1

/-- **Theorem 2.13, Part 2 (Output Convergence in Distribution - Standalone Form).** Under any
probability space where the depth-`L` network's layer-`L` empirical covariance converges in
probability to `layerCovarianceSeq 1 0 φ m Φ0 L`, the output vector converges in distribution to
the centered multivariate Gaussian `𝒩(0, Φ_L)`.  This theorem is mathematically self-contained,
depends on zero unproved steps, and establishes Step 6 of the Deep NNGP Recursion. -/
theorem tendstoInDistribution_deepEval_of_covariance_tendsto
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ)
    (hP : TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) :
    TendstoInDistribution
      (fun (n : ℕ) (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
          φ (deepPreactivation d m n φ X
              (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
      Filter.atTop id
      (fun _ => (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))
      (multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) where
  forall_aemeasurable n := (measurable_deepEval d m L φ hφ_cont.measurable X n).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    have h_weak : Filter.Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
        (fun n : ℕ => ⟨Measure.map
            (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
              (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
                (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
            ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
                Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
              ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))),
          (Measure.isProbabilityMeasure_map_iff
            (measurable_deepEval d m L φ hφ_cont.measurable X n).aemeasurable).mpr inferInstance⟩)
        Filter.atTop
        (nhds ⟨multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L),
          inferInstance⟩) := by
      apply ProbabilityMeasure.tendsto_of_tendsto_charFun
      intro t
      exact tendsto_charFun_map_deepEval_of_covariance_tendsto d m L φ hφ_cont C hC p hp hφ_growth X t hP
    convert! h_weak
    exact congrArg nhds (Subtype.ext Measure.map_id)

/-- **Theorem 2.13, Part 2 (Output Convergence in Distribution).** As width `n → ∞`, the depth-`L`
network's output vector `f_m(θ) = n⁻¹ᐟ² ∑ⱼ aⱼ φ(h_L(X^α)ⱼ)` converges in distribution to the
centered multivariate Gaussian `𝒩(0, Φ_L)`, `Φ_L := layerCovarianceSeq 1 0 φ m Φ0 L`.  (The ambient
sample space carries one extra, unused `ℝ`-valued coordinate `q.2.2` alongside the readout
population `q.2.1 : ℕ → ℝ`, purely so the proof can invoke
`exact_conditional_normality_general_multivariate` — whose general `σw, σb` signature includes a
bias-noise slot — with `σb := 0` at no extra cost, rather than adding a marginalization lemma.
The `hφ_L2` hypothesis, matching `layerCovarianceSeq_posSemidef`'s, is needed so the limit
`Φ_L` is positive semidefinite, which `charFun_multivariateGaussian` needs for its closed form.)

**Proof.**  Mirrors `tendstoInDistribution_evalVector` (Theorem 3) step for step, factored through
the helper lemmas above (`measurable_deepEval`, `map_deepEval_snd_eq_multivariateGaussian`,
`charFun_map_deepEval`, `tendsto_charFun_map_deepEval`):

1. *Exact conditional normality*: `exact_conditional_normality_general_multivariate 1 0 n m H`
   with `H j α := φ (deepPreactivation … (L - 1) α j)` gives, with **zero new proof**, that
   `f_m(θ) | (hidden weights) ~ 𝒩(0, Φ_L^{(n)})` exactly, where `Φ_L^{(n)}` is the width-`n`
   empirical covariance from Part 1 at `ℓ = L - 1` (`map_deepEval_snd_eq_multivariateGaussian`).
2. *Law of total expectation* for the characteristic function via Fubini on the product measure,
   mirroring `charFun_outputMeasure`'s proof shape (`charFun_map_deepEval`).
3. *Boundedness*: reuse `norm_exp_neg_ofReal_div_two_le_one` verbatim (PosSemidef of `Φ_L^{(n)}`,
   `norm_charFun_deepEval_le_one`).
4. *Continuity* of `M ↦ exp(-t·M·t/2)`: reuse `continuous_charFun_integrand` verbatim.
5. *Passing the limit*: `tendsto_integral_of_tendstoInMeasure_of_bounded` (already proved above)
   applied to Part 1 at `ℓ = L - 1`, in place of Theorem 3's dominated-convergence step (Part 1
   only supplies convergence in probability, not the a.s. convergence Theorem 3 had from
   Kolmogorov's SLLN) — assembled as `tendsto_charFun_map_deepEval`.
6. *Lévy continuity*: `ProbabilityMeasure.tendsto_of_tendsto_charFun`, reused directly.

The hypotheses otherwise match Part 1's exactly (continuity and polynomial growth, not just
measurability), since this theorem invokes Part 1 at `ℓ = L - 1`. -/
theorem tendstoInDistribution_deepEval
    (d m L : ℕ) (hL : 0 < L) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
          φ (deepPreactivation d m n φ X
              (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
      Filter.atTop id
      (fun _ => (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))
      (multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) := by
  have hL1 : L - 1 + 1 = L := by omega
  have hP1 := deepEmpiricalCovariance_tendstoInMeasure d m L φ hφ_cont C hC p hp hφ_growth X
    (L - 1) (by omega)
  rw [hL1] at hP1
  exact tendstoInDistribution_deepEval_of_covariance_tendsto d m L φ hφ_cont C hC p hp hφ_growth X hP1

end DeepNNGPRecursion



/-! ## Full Two-Layer NTK Initialization and Infinite-Width Limit -/

section FullTwoLayerNTKInitialization

/-! ### Joint Neuron Law

The joint initialization law of a single hidden neuron `(w, a)` with input weights
`w ~ 𝒩(0, I_d)` and readout weight `a ~ 𝒩(0, 1)`. -/

/-- The single-neuron initialization probability measure on `(Fin d → ℝ) × ℝ`:
the product of the input row Gaussian measure and the scalar readout Gaussian measure. -/
noncomputable def singleNeuronMeasure (d : ℕ) : Measure ((Fin d → ℝ) × ℝ) :=
  (gaussianRowMeasure d).prod (gaussianReal 0 1)

/-- Instance: `singleNeuronMeasure d` is a probability measure. -/
instance instIsProbabilityMeasureSingleNeuronMeasure (d : ℕ) :
    IsProbabilityMeasure (singleNeuronMeasure d) := by
  dsimp [singleNeuronMeasure]
  infer_instance

/-- Measure-preserving rearrangement between a finite array of neuron pairs
and the repository's `(W, a)` initialization representation `initMeasure n d`. -/
theorem measurePreserving_arrowProd_singleNeuronMeasure (n d : ℕ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n))
      (Measure.pi fun _ : Fin n => singleNeuronMeasure d)
      (initMeasure n d) := by
  dsimp [singleNeuronMeasure, initMeasure, gaussianInit, gaussianReadoutMeasure]
  exact measurePreserving_arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n)
    (fun _ => gaussianRowMeasure d) (fun _ => gaussianReal 0 1)

/-- **Markov bound for neuron averages.** For a nonnegative measurable single-neuron observable
`g` that is integrable under `singleNeuronMeasure d`, the width-normalized empirical average
`n⁻¹ ∑ᵢ g (Wᵢ, aᵢ)` is at most `τ` with `initMeasure n d`-probability at least `1 - δ`, as soon as
`E g ≤ τ δ`. The threshold is independent of the width, in contrast with the maximum-readout bound
whose threshold grows like `√(log n)`. -/
theorem measureReal_initMeasure_neuronAverage_le {n d : ℕ} (hn : 0 < n)
    {g : (Fin d → ℝ) × ℝ → ℝ} (hg : Measurable g) (hint : Integrable g (singleNeuronMeasure d))
    (hnn : ∀ q, 0 ≤ g q) {τ δ : ℝ} (hτ : 0 < τ)
    (hv : ∫ q, g q ∂(singleNeuronMeasure d) ≤ τ * δ) :
    (initMeasure n d).real {p | (n : ℝ)⁻¹ * ∑ i : Fin n, g (p.1 i, p.2 i) ≤ τ} ≥ 1 - δ := by
  have hpi := measureReal_pi_average_le_ge_one_sub (μ := singleNeuronMeasure d) (n := n) hn hg hint
    hnn hτ hv
  have hmp := measurePreserving_arrowProd_singleNeuronMeasure n d
  have hpre := hmp.measure_preimage_equiv
    {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | (n : ℝ)⁻¹ * ∑ i : Fin n, g (p.1 i, p.2 i) ≤ τ}
  rw [Measure.real, ← hpre]
  exact hpi

/-- Equivalence between `Fin n` and `{i : ℕ // i ∈ Finset.range n}`. -/
private def finEquivRange (n : ℕ) : Fin n ≃ ↑(Finset.range n) where
  toFun i := ⟨i.val, Finset.mem_range.2 i.isLt⟩
  invFun j := ⟨j.val, Finset.mem_range.1 j.2⟩
  left_inv i := by ext; rfl
  right_inv j := by ext; rfl

/-- Restricting an infinite sequence under `Measure.infinitePi` to `Finset.range n` preserves
measure with respect to the finite product measure on `↑(Finset.range n)`. -/
private theorem measurePreserving_restrict_range {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (Finset.range n).restrict
      (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.pi fun _ : ↑(Finset.range n) => ν) where
  measurable := measurable_pi_iff.2 fun i => measurable_pi_apply i.1
  map_eq := Measure.infinitePi_map_restrict (fun _ : ℕ => ν)

/-- Restricting an infinite sequence under `Measure.infinitePi` to its first `n` elements
indexed by `Fin n` is measure-preserving with respect to `Measure.pi (fun _ : Fin n => ν)`. -/
theorem measurePreserving_prefixMap {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (fun (seq : ℕ → α) (i : Fin n) => seq i.val)
      (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.pi fun _ : Fin n => ν) := by
  have h_restrict := measurePreserving_restrict_range ν n
  have h_congr := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) (finEquivRange n).symm)
  have h_comp := h_congr.comp h_restrict
  have heq : (MeasurableEquiv.piCongrLeft (fun _ => α) (finEquivRange n).symm ∘
      (Finset.range n).restrict) =
      (fun (seq : ℕ → α) (i : Fin n) => seq i.val) := by
    ext seq i
    rfl
  rwa [heq] at h_comp

/-- The measure-preserving map from the infinite sequence space
`Measure.infinitePi (fun _ => singleNeuronMeasure d)` to the repository's finite-width
initialization representation `initMeasure n d`.
Composes the prefix restriction map with the finite array rearrangement
`measurePreserving_arrowProd_singleNeuronMeasure`. -/
theorem measurePreserving_infiniteSeq_to_init (n d : ℕ) :
    MeasurePreserving
      (fun (seq : ℕ → (Fin d → ℝ) × ℝ) =>
        (fun (i : Fin n) => (seq i.val).1, fun (i : Fin n) => (seq i.val).2))
      (Measure.infinitePi fun _ : ℕ => singleNeuronMeasure d)
      (initMeasure n d) := by
  have h_pref := measurePreserving_prefixMap (singleNeuronMeasure d) n
  have h_rearr := measurePreserving_arrowProd_singleNeuronMeasure n d
  exact h_rearr.comp h_pref

/-! ### Full NTK Summand Measurability and Moments -/

/-- Measurability of the full activation-plus-derivative single-neuron NTK summand.
We state measurability directly for the full expression without introducing a one-line wrapper. -/
lemma measurable_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (hderiv_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ) :
    Measurable (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) := by
  have h_w : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1) := measurable_fst
  have h_a : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2) := measurable_snd
  have h_wx : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x) :=
    (measurable_dotProduct_left x).comp h_w
  have h_wx' : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x') :=
    (measurable_dotProduct_left x').comp h_w
  have h_φx : Measurable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x)) :=
    hφ_meas.comp h_wx
  have h_φx' : Measurable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x')) :=
    hφ_meas.comp h_wx'
  have h_dφx : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x)) :=
    hderiv_meas.comp h_wx
  have h_dφx' : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x')) :=
    hderiv_meas.comp h_wx'
  have h_a2 : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2 ^ 2) :=
    (continuous_pow 2).measurable.comp h_a
  exact (h_φx.mul h_φx').add (((h_a2.mul h_dφx).mul h_dφx').mul_const (x ⬝ᵥ x'))

/-- Integrability of the full activation-plus-derivative single-neuron NTK summand
under `singleNeuronMeasure d`. Follows from product-measure Fubini and independence of
weights and readouts. -/
lemma integrable_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hφ_int : Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (gaussianRowMeasure d))
    (hdφ_int : Integrable (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) (gaussianRowMeasure d)) :
    Integrable (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      (singleNeuronMeasure d) := by
  dsimp [singleNeuronMeasure]
  have h1 : Integrable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hφ_int.comp_fst (gaussianReal 0 1)
  have h2_prod : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) * p.2 ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    (hdφ_int.mul_const (x ⬝ᵥ x')).mul_prod integrable_sq_gaussianReal
  have h2 : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) := by
    refine h2_prod.congr (ae_of_all _ (fun p => ?_))
    ring
  exact h1.add h2

/-- Integrability of the full NTK summand under `MemLp 2` hypotheses on `φ` and `deriv φ`. -/
lemma integrable_fullNTK_summand_of_memLp {d : ℕ}
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hφ : MemLp (fun w => φ (w ⬝ᵥ x)) 2 (gaussianRowMeasure d))
    (hφ' : MemLp (fun w => φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d))
    (hdφ : MemLp (fun w => deriv φ (w ⬝ᵥ x)) 2 (gaussianRowMeasure d))
    (hdφ' : MemLp (fun w => deriv φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d)) :
    Integrable (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      (singleNeuronMeasure d) :=
  integrable_fullNTK_summand φ x x' (hφ.integrable_mul hφ') (hdφ.integrable_mul hdφ')

/-- Square-integrability (`MemLp 2`) of the full single-neuron NTK summand under
`MemLp 2` hypotheses on the activation product and derivative product.
Uses the fourth-moment Gaussian readout bound `integrable_pow_four_gaussianReal`. -/
lemma memLp_two_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (hdφ_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ)
    (hφ_L2 : MemLp (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d))
    (hdφ_L2 : MemLp (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d)) :
    MemLp (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      2 (singleNeuronMeasure d) := by
  dsimp [singleNeuronMeasure]
  have h1 : MemLp (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x')) 2
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hφ_L2.comp_fst (gaussianReal 0 1)
  have hd_scaled : MemLp (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') * (x ⬝ᵥ x')) 2
      (gaussianRowMeasure d) :=
    hdφ_L2.mul_const (x ⬝ᵥ x')
  have hd_sq : Integrable (fun w => (deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2)
      (gaussianRowMeasure d) :=
    (memLp_two_iff_integrable_sq hd_scaled.aestronglyMeasurable).1 hd_scaled
  have ha4 : Integrable (fun a : ℝ => (a ^ 2) ^ 2) (gaussianReal 0 1) := by
    have heq : (fun a : ℝ => (a ^ 2) ^ 2) = (fun a => a ^ 4) := by ext a; ring
    rw [heq]
    exact integrable_pow_four_gaussianReal
  have h2_sq_prod : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2 * (p.2 ^ 2) ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hd_sq.mul_prod ha4
  have h2_sq : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) := by
    refine h2_sq_prod.congr (ae_of_all _ (fun p => ?_))
    dsimp
    ring
  have h_w : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1) := measurable_fst
  have h_a : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2) := measurable_snd
  have h_wx : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x) :=
    (measurable_dotProduct_left x).comp h_w
  have h_wx' : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x') :=
    (measurable_dotProduct_left x').comp h_w
  have h_dφx : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x)) :=
    hdφ_meas.comp h_wx
  have h_dφx' : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x')) :=
    hdφ_meas.comp h_wx'
  have h_a2 : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2 ^ 2) :=
    (continuous_pow 2).measurable.comp h_a
  have h2_meas : Measurable (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) :=
    ((h_a2.mul h_dφx).mul h_dφx').mul_const (x ⬝ᵥ x')
  have h2 : MemLp (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) 2
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    (memLp_two_iff_integrable_sq h2_meas.aestronglyMeasurable).2 h2_sq
  exact h1.add h2

/-- Integrability of the squared full NTK summand under `singleNeuronMeasure d`,
providing second-moment bounds needed for quantitative concentration and Chebyshev bounds. -/
lemma integrable_sq_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ)
    (hφ_L2 : MemLp (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d))
    (hdφ_L2 : MemLp (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d)) :
    Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2)
      (singleNeuronMeasure d) := by
  have h_mem := memLp_two_fullNTK_summand φ hdφ_meas x x' hφ_L2 hdφ_L2
  have h_meas := measurable_fullNTK_summand φ hφ_meas hdφ_meas x x'
  exact (memLp_two_iff_integrable_sq h_meas.aestronglyMeasurable).1 h_mem

/-- The expectation of the full single-neuron NTK summand under `singleNeuronMeasure d`
equals the sum of the NNGP activation kernel entry and the derivative kernel entry
scaled by the input inner product `x ⬝ᵥ x'`. -/
lemma integral_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hφ_int : Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (gaussianRowMeasure d))
    (hdφ_int : Integrable (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) (gaussianRowMeasure d)) :
    ∫ p : (Fin d → ℝ) × ℝ,
      (φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      ∂(singleNeuronMeasure d) =
      (∫ w, φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) +
        (∫ w, deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) * (x ⬝ᵥ x') := by
  dsimp [singleNeuronMeasure]
  have h1 : Integrable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hφ_int.comp_fst (gaussianReal 0 1)
  have h2_prod : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) * p.2 ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    (hdφ_int.mul_const (x ⬝ᵥ x')).mul_prod integrable_sq_gaussianReal
  have h2 : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) := by
    refine h2_prod.congr (ae_of_all _ (fun p => ?_))
    ring
  rw [integral_add h1 h2]
  have h_int1 : ∫ p : (Fin d → ℝ) × ℝ, φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x')
      ∂((gaussianRowMeasure d).prod (gaussianReal 0 1)) =
      ∫ w, φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d) := by
    have hfst := integral_fun_fst (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x'))
      (μ := gaussianRowMeasure d) (ν := gaussianReal 0 1)
    rw [hfst]
    simp
  have h_int2 : ∫ p : (Fin d → ℝ) × ℝ,
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')
      ∂((gaussianRowMeasure d).prod (gaussianReal 0 1)) =
      (∫ w, deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) * (x ⬝ᵥ x') := by
    have h_eq : (fun p : (Fin d → ℝ) × ℝ =>
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) =
        (fun p : (Fin d → ℝ) × ℝ =>
        (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) * p.2 ^ 2) := by
      ext p; ring
    rw [h_eq]
    rw [integral_prod_mul (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') * (x ⬝ᵥ x'))
      (fun a => a ^ 2)]
    rw [integral_sq_gaussianReal]
    rw [mul_one]
    exact integral_mul_const (x ⬝ᵥ x') (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x'))
  rw [h_int1, h_int2]

/-! ### Strong Law of Large Numbers for the Full NTK -/

/-- Strong law of large numbers for empirical averages of the full NTK summand
over an i.i.d. neuron sequence drawn from `singleNeuronMeasure d`.
Reuses the generalized `iid_average_tendsto_integral` from `Kernel.lean`. -/
theorem fullNTKSummand_tendsto_integral {d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ)
    (hφ_int : Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (gaussianRowMeasure d))
    (hdφ_int : Integrable (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ x) * φ ((seq j).1 ⬝ᵥ x') +
            (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ x) * deriv φ ((seq j).1 ⬝ᵥ x') * (x ⬝ᵥ x')))
        Filter.atTop
        (nhds ((∫ w, φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) +
          (∫ w, deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) * (x ⬝ᵥ x'))) := by
  set g := fun p : (Fin d → ℝ) × ℝ =>
    φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')
  have hg_meas : Measurable g := measurable_fullNTK_summand φ hφ_meas hdφ_meas x x'
  have hg_int : Integrable g (singleNeuronMeasure d) :=
    integrable_fullNTK_summand φ x x' hφ_int hdφ_int
  have h_slln := iid_average_tendsto_integral (singleNeuronMeasure d) g hg_meas hg_int
  rw [integral_fullNTK_summand φ x x' hφ_int hdφ_int] at h_slln
  exact h_slln

/-- Full matrix almost-sure convergence of the empirical NTK Gram matrix on dataset `X`
to the deterministic limiting NTK Gram matrix. Assembles entrywise SLLN convergence
over the finite index space `Fin m × Fin m` using `tendsto_pi_nhds` and `ae_all_iff`. -/
theorem fullNTKMatrix_tendsto_integral {m d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β)) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ => ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
            (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
              (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ))
        Filter.atTop
        (nhds ((fun α β =>
          (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
            (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
              (X α ⬝ᵥ X β)) : Matrix (Fin m) (Fin m) ℝ)) := by
  have h_entry : ∀ α β : Fin m,
      ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
        Filter.Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j : Fin n,
            (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
              (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
                (X α ⬝ᵥ X β)))
          Filter.atTop
          (nhds ((∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
            (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
              (X α ⬝ᵥ X β))) :=
    fun α β => fullNTKSummand_tendsto_integral φ hφ_meas hdφ_meas (X α) (X β)
      (hφ_int α β) (hdφ_int α β)
  have h_all :
      ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
        ∀ α β : Fin m,
          Filter.Tendsto
            (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j : Fin n,
              (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
                (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
                  (X α ⬝ᵥ X β)))
            Filter.atTop
            (nhds ((∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
              (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
                (X α ⬝ᵥ X β))) := by
    simp_rw [ae_all_iff]
    exact h_entry
  filter_upwards [h_all] with seq hseq
  exact tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => hseq α β

/-- Full matrix almost-sure convergence of the empirical NTK on the paper's scaled dataset
`(1 / √d) * X`, with explicit scaling `1 / d` on the derivative covariance factor. -/
theorem fullNTKMatrix_scaled_dataset_tendsto_integral {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ => ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
             φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
            (seq j).2 ^ 2 *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
              ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ))
        Filter.atTop
        (nhds ((fun α β =>
          (∫ w, φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
            φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) +
            (∫ w, deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
              deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) *
                ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ)) := by
  have h_base := fullNTKMatrix_tendsto_integral φ hφ_meas hdφ_meas
    (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) hφ_int hdφ_int
  simp_rw [dotProduct_scaled_dataset d hd] at h_base
  exact h_base

/-- Matrix norm almost-sure convergence of the empirical NTK Gram matrix on dataset `X`
to the deterministic limiting NTK Gram matrix: `‖K_n(0) - K_∞‖ → 0` almost surely. -/
theorem fullNTKMatrix_norm_sub_tendsto_zero {m d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β)) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ =>
          ‖((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
              (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
                (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
                  (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ) -
            ((fun α β =>
              (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
                (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
                  (X α ⬝ᵥ X β)) : Matrix (Fin m) (Fin m) ℝ)‖)
        Filter.atTop
        (nhds 0) := by
  set L : Matrix (Fin m) (Fin m) ℝ := fun α β =>
    (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
      (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) * (X α ⬝ᵥ X β)
  have h := fullNTKMatrix_tendsto_integral φ hφ_meas hdφ_meas X hφ_int hdφ_int
  filter_upwards [h] with seq hseq
  have h_sub := hseq.sub (tendsto_const_nhds (x := L))
  rw [sub_self] at h_sub
  exact tendsto_zero_iff_norm_tendsto_zero.1 h_sub

/-- Convergence in probability (`TendstoInMeasure`) of the empirical NTK Gram matrix
to the deterministic limiting NTK Gram matrix on dataset `X`. -/
theorem fullNTKMatrix_tendstoInMeasure {m d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β)) (gaussianRowMeasure d)) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ => singleNeuronMeasure d)
      (fun n : ℕ => fun seq : ℕ → (Fin d → ℝ) × ℝ =>
        ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
            (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
              (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ))
      Filter.atTop
      (fun _ => ((fun α β =>
        (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
          (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
            (X α ⬝ᵥ X β)) : Matrix (Fin m) (Fin m) ℝ)) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    refine (measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_).aestronglyMeasurable
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    have h_eval : Measurable (fun seq : ℕ → (Fin d → ℝ) × ℝ => seq j.val) :=
      measurable_pi_apply j.val
    have h_summand := measurable_fullNTK_summand φ hφ_meas hdφ_meas (X α) (X β)
    exact h_summand.comp h_eval
  · exact fullNTKMatrix_tendsto_integral φ hφ_meas hdφ_meas X hφ_int hdφ_int

/-- Convergence in probability (`TendstoInMeasure`) of the empirical NTK Gram matrix
on the paper's scaled dataset `(1 / √d) * X`. -/
theorem fullNTKMatrix_scaled_dataset_tendstoInMeasure {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d)) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ => singleNeuronMeasure d)
      (fun n : ℕ => fun seq : ℕ → (Fin d → ℝ) × ℝ =>
        ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
             φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
            (seq j).2 ^ 2 *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
              ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ))
      Filter.atTop
      (fun _ => ((fun α β =>
        (∫ w, φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
          φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) +
          (∫ w, deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
            deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) *
              ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ)) := by
  have h_base := fullNTKMatrix_tendstoInMeasure φ hφ_meas hdφ_meas
    (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) hφ_int hdφ_int
  simp_rw [dotProduct_scaled_dataset d hd] at h_base
  exact h_base

/-- The deterministic limiting full NTK Gram matrix on dataset `X` with input dimension `d`:
  `Θ_∞ = limitingCovariance φ scaledX + (d⁻¹ • (X Xᵀ)) ∘ limitingCovariance (deriv φ) scaledX`,
  where `∘` is the entrywise (Hadamard) product. -/
noncomputable def limitingFullNTKMatrix {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun α β =>
    limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β +
      limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β *
        ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))

/-- Equation lemma for `limitingFullNTKMatrix`. -/
lemma limitingFullNTKMatrix_apply {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (α β : Fin m) :
    limitingFullNTKMatrix φ X α β =
      limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β +
        limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β *
          ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := rfl

/-- The limiting full NTK Gram matrix is symmetric (Hermitian). -/
lemma limitingFullNTKMatrix_isHermitian {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    (limitingFullNTKMatrix φ X).IsHermitian := by
  ext α β
  simp only [limitingFullNTKMatrix_apply, conjTranspose_apply, star_trivial]
  have h1 : limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) β α =
      limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β := by
    rw [limitingCovariance_apply, limitingCovariance_apply]
    congr 1 with w
    ring
  have h2 : limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) β α =
      limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β := by
    rw [limitingCovariance_apply, limitingCovariance_apply]
    congr 1 with w
    ring
  rw [h1, h2, dotProduct_comm]

/-- The limiting full NTK is the NNGP covariance of `φ` plus the Schur product of the covariance of
`φ'` with the input Gram matrix of the scaled dataset. -/
lemma limitingFullNTKMatrix_eq_add_hadamard {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    limitingFullNTKMatrix φ X =
      (limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) +
        (limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k)).hadamard
          ((Matrix.of fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k : Matrix (Fin m) (Fin d) ℝ) *
            (Matrix.of fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k :
              Matrix (Fin m) (Fin d) ℝ).conjTranspose) := by
  set scaledX : Matrix (Fin m) (Fin d) ℝ := fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k
  ext α β
  simp only [limitingFullNTKMatrix_apply, Matrix.add_apply, Matrix.hadamard_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  dsimp [scaledX]
  have hsqrt : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ = (d : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  have hterm (k : Fin d) :
      ((Real.sqrt (d : ℝ))⁻¹ * X α k) * ((Real.sqrt (d : ℝ))⁻¹ * X β k) =
        (d : ℝ)⁻¹ * (X α k * X β k) := by
    rw [mul_mul_mul_comm, hsqrt]
  simp_rw [hterm, ← Finset.mul_sum]
  rfl

/-- The deterministic limiting full NTK matrix is positive semidefinite (`PosSemidef`),
established via Schur product theorem for the derivative covariance and input Gram matrix. -/
theorem limitingFullNTKMatrix_posSemidef {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hdφ_meas : Measurable (deriv φ))
    (hφ_L2 : ∀ α : Fin m,
      MemLp (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α : Fin m,
      MemLp (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d)) :
    (limitingFullNTKMatrix φ X).PosSemidef := by
  set scaledX : Matrix (Fin m) (Fin d) ℝ := fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k
  have h_cov1 : (limitingCovariance φ scaledX).PosSemidef :=
    limitingCovariance_posSemidef φ scaledX hφ_meas hφ_L2
  have h_cov2 : (limitingCovariance (deriv φ) scaledX).PosSemidef :=
    limitingCovariance_posSemidef (deriv φ) scaledX hdφ_meas hdφ_L2
  have h_gram : (scaledX * scaledX.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose scaledX
  have h_schur : ((limitingCovariance (deriv φ) scaledX).hadamard
      (scaledX * scaledX.conjTranspose)).PosSemidef :=
    h_cov2.hadamard h_gram
  have h_sum : ((limitingCovariance φ scaledX) +
      (limitingCovariance (deriv φ) scaledX).hadamard
        (scaledX * scaledX.conjTranspose)).PosSemidef :=
    h_cov1.add h_schur
  have heq := limitingFullNTKMatrix_eq_add_hadamard φ X
  rw [heq]
  exact h_sum

/-- **Strict positive definiteness of the NNGP covariance from feature independence.** If the
features `w ↦ φ(w ⬝ᵥ X α)` are linearly independent modulo Gaussian-null sets -- no nontrivial
combination `∑ α, u α * φ (w ⬝ᵥ X α)` vanishes `gaussianRowMeasure d`-almost everywhere -- then
`limitingCovariance φ X` is positive definite. The argument is the quadratic-form identity
`u ⬝ᵥ Φ u = 𝔼[(∑ α, u α φ(w ⬝ᵥ X α))²]`, which is positive as soon as the square is not
a.e. zero. -/
theorem limitingCovariance_posDef_of_ae_independent {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d), ∑ α : Fin m, u α * φ (w ⬝ᵥ X α) = 0) → u = 0) :
    (limitingCovariance φ X).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨limitingCovariance_isHermitian φ X, ?_⟩
  intro c hc
  have hq : star c ⬝ᵥ (limitingCovariance φ X) *ᵥ c =
      ∫ w, (∑ α : Fin m, c α * φ (w ⬝ᵥ X α)) ^ 2 ∂(gaussianRowMeasure d) := by
    rw [← sum_sum_mul_limitingCovariance_eq_integral_sq φ X hφ_L2 c]
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  rw [hq]
  have hg : MemLp (fun w => ∑ α : Fin m, c α * φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d) :=
    memLp_finsetSum _ fun α _ => (hφ_L2 α).const_mul (c α)
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun w => sq_nonneg _)
    hg.integrable_sq]
  refine pos_iff_ne_zero.2 fun h0 => hc (hind c ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with w hw
  by_contra hne
  exact hw (pow_ne_zero 2 hne)

/-- **The limiting full NTK is positive definite under feature independence.**
`K_∞ = Φ_φ + Φ_{φ'} ⬝ᵥ (X Xᵀ / d)` with the second summand positive semidefinite (Schur product), so
`K_∞` is positive definite as soon as `Φ_φ` is
(`limitingCovariance_posDef_of_ae_independent`). Independence of the *values* `φ(w ⬝ᵥ X α)` is the
relevant hypothesis; the derivative term only helps. -/
theorem limitingFullNTKMatrix_posDef_of_ae_independent {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (hdφ_meas : Measurable (deriv φ))
    (hφ_L2 : ∀ α : Fin m,
      MemLp (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α : Fin m,
      MemLp (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d))
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d),
        ∑ α : Fin m, u α * φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0) :
    (limitingFullNTKMatrix φ X).PosDef := by
  set scaledX : Matrix (Fin m) (Fin d) ℝ := fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k
  rw [limitingFullNTKMatrix_eq_add_hadamard]
  exact (limitingCovariance_posDef_of_ae_independent φ scaledX hφ_L2 hind).add_posSemidef
    ((limitingCovariance_posSemidef (deriv φ) scaledX hdφ_meas hdφ_L2).hadamard
      (Matrix.posSemidef_self_mul_conjTranspose scaledX))

/-- **Feature independence forces distinct inputs.** If the scaled features are linearly independent
modulo Gaussian-null sets, the inputs `X α` are pairwise distinct. This is the necessary half of the
source's informal condition "distinct inputs and an expressive activation": the hypothesis of
`limitingCovariance_posDef_of_ae_independent` cannot hold for a dataset with a repeated input, and
the remaining (sufficiency) content is exactly the independence hypothesis. -/
theorem injective_of_ae_independent {m d : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d),
        ∑ α : Fin m, u α * φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0) :
    Function.Injective X := by
  intro α β hαβ
  by_contra hne
  have h := hind (Pi.single α 1 - Pi.single β 1) (Filter.Eventually.of_forall fun w => by
    simp [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul, hαβ])
  have := congrFun h α
  simp [hne] at this

/-- Matrix almost-sure convergence of the empirical NTK neuron-average matrix to the
deterministic `limitingFullNTKMatrix` on the paper's scaled dataset `(1 / √d) * X`. -/
theorem fullNTKMatrix_scaled_dataset_tendsto_limitingFullNTKMatrix {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ =>
          ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
              (φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
                 φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
               (seq j).2 ^ 2 *
                 deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
                 deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
                 ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ))
        Filter.atTop
        (nhds (limitingFullNTKMatrix φ X)) :=
  fullNTKMatrix_scaled_dataset_tendsto_integral hd φ hφ_meas hdφ_meas X hφ_int hdφ_int

/-! ### Quantitative Concentration for the Full NTK Initializer -/

section FullNTKConcentration

/-- Uncentered second moment of the full activation-plus-derivative NTK summand under
`singleNeuronMeasure d`. Hides the bivariate Gaussian integral over hidden weight and readout
parameters `(w, a)`.

This moment is the core quantitative constant in:
1. `chebyshev_entrywise_empiricalNTKMatrix`: entrywise Chebyshev concentration for each `(α, β)`.
2. `chebyshev_matrix_empiricalNTKMatrix`: Frobenius-norm matrix concentration via union bound.
3. Downstream initial spectral gap transfer and lazy-training bootstrap bounds. -/
noncomputable def fullNTKSummandSecondMoment (d : ℕ) (φ : ℝ → ℝ)
    {m : ℕ} (X : Fin m → Fin d → ℝ) (α β : Fin m) : ℝ :=
  ∫ u : (Fin d → ℝ) × ℝ,
    (φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
     u.2 ^ 2 * deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
       ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) ^ 2
    ∂(singleNeuronMeasure d)

lemma fullNTKSummandSecondMoment_nonneg (d : ℕ) (φ : ℝ → ℝ) {m : ℕ} (X : Fin m → Fin d → ℝ)
    (α β : Fin m) : 0 ≤ fullNTKSummandSecondMoment d φ X α β :=
  integral_nonneg fun _ => sq_nonneg _

/-- Expectation of the full NTK summand on the scaled dataset `(1 / √d) * X` equals
the limiting full NTK matrix entry `limitingFullNTKMatrix φ X α β`. -/
lemma integral_fullNTK_summand_scaled_dataset_eq_limiting {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (α β : Fin m) :
    ∫ u : (Fin d → ℝ) × ℝ,
      (φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
         φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
       u.2 ^ 2 * deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
         deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
         ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)))
      ∂(singleNeuronMeasure d) =
      limitingFullNTKMatrix φ X α β := by
  have h := integral_fullNTK_summand φ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)
    (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k) (hφ_int α β) (hdφ_int α β)
  rw [h]
  rw [dotProduct_scaled_dataset d hd]
  rw [limitingFullNTKMatrix_apply, limitingCovariance_apply, limitingCovariance_apply]

end FullNTKConcentration

end FullTwoLayerNTKInitialization

end NTK

end
