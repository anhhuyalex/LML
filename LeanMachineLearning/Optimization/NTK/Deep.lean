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
* `NTK.Deep.BackwardConcentration`: backward sensitivity Gram concentration (readout layer and the
  downward induction) and the convergence in probability of `deepEmpiricalNTK` to `deepLimitingNTK`
  (Theorem 2.27).
-/
