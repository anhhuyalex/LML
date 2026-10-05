/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.Architecture
public import LeanMachineLearning.Optimization.NTK.Deep.LayerwiseNTK
public import LeanMachineLearning.Optimization.NTK.Deep.LimitingNTK
public import LeanMachineLearning.Optimization.NTK.Deep.GaussianDecoupling
public import LeanMachineLearning.Optimization.NTK.Deep.BackwardConcentration
public import LeanMachineLearning.Optimization.NTK.Deep.BackwardTop

/-!
# Deep Neural Tangent Kernel (Deep NTK) Curriculum

This module serves as the root umbrella export for the formalization of the deep Neural
Tangent Kernel (depth `d ≥ 1`), structured as follows:

* `NTK.Deep.Architecture`: Multilayer MLP parameters (`DeepMLPParams`), forward propagation
  of pre-activations (`deepMLPPreactivation`), backward sensitivities, forward feature Gram
  matrices (`deepActivationGram`), derivative feature Gram matrices (`deepDerivativeGram`),
  and backward sensitivity covariance matrices (`deepSensitivityGram`). Formally unified with
  infinite-width tensors via `deepMLPPreactivation_ofTensor_eq_deepPreactivation`.
* `NTK.Deep.LayerwiseNTK`: Exact algebraic layerwise decomposition of the empirical NTK
  `deepEmpiricalNTK` across parameter blocks (Proposition 2.25) and global positive
  semidefiniteness / Loewner dominance over the NNGP kernel (`deepEmpiricalNTK_ge_nngp`).
* `NTK.Deep.LimitingNTK`: Deterministic backward covariance tensor `deepLimitingSensitivityKernel`
  and recursive limiting NTK matrix `deepLimitingNTK` (Proposition 2.27), positive
  semidefiniteness, Loewner dominance, and two-layer consistency with `limitingFullNTKMatrix`.
* `NTK.Deep.GaussianDecoupling`: the deterministic layerwise assembly for Theorem 2.27 and the
  transport of forward activation and derivative Gram concentration to the `(W, w_out)` product
  measure.
  (The Gaussian matrix algebra, including Lemma 2.26, lives in
  `Initialization/GaussianMatrixAlgebra.lean`.)
* `NTK.Deep.LayerSplit`, `NTK.Deep.DeepSpaceForward`: the product of the first `d` Gaussian weight
  populations, the split of one layer from the rest (a measure-preserving map onto a product), and
  forward Gram concentration on that space.
* `NTK.Deep.BackwardAlgebra`, `NTK.Deep.DecouplingBounds`, `NTK.Deep.BackwardStructure`: the
  deterministic weighted-average algebra (Cauchy–Schwarz, fourth-moment bounds, projected part),
  the convergence-in-measure bounds for the decoupling, and the layer-substitution structure.
* `NTK.Deep.BackwardDecoupling`: the decoupling `G_k − G_{k+1} Φ'_k → 0` of the backward Gram matrix
  from the residual and projected parts of the back-propagated vector.
* `NTK.Deep.BackwardInduction`, `NTK.Deep.BackwardTop`, `NTK.Deep.BackwardConcentration`: the joint
  downward induction on Gram convergence and gradient independence, its readout-layer base case,
  and the convergence in probability of `deepEmpiricalNTK` to `deepLimitingNTK` (Theorem 2.27).
-/
