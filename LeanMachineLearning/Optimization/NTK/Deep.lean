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

/-!
# Deep Neural Tangent Kernel (Deep NTK) Curriculum

This module serves as the root umbrella export for the formalization of the deep Neural
Tangent Kernel (depth `d ≥ 1`), structured as follows:

* `NTK.Deep.Architecture`: Multilayer MLP parameters (`DeepMLPParams`), forward propagation
  of pre-activations (`deepMLPPreactivation`), backward sensitivities, forward feature Gram
  matrices (`empiricalForwardCov`), derivative feature Gram matrices (`empiricalDerivCov`),
  and backward sensitivity covariance matrices (`empiricalBackwardCov`). Formally unified with
  infinite-width tensors via `deepMLPPreactivation_ofTensor_eq_deepPreactivation`.
* `NTK.Deep.LayerwiseNTK`: Exact algebraic layerwise decomposition of the empirical NTK
  `deepEmpiricalNTK` across parameter blocks (Proposition 2.25) and global positive
  semidefiniteness / Loewner dominance over the NNGP kernel (`deepEmpiricalNTK_ge_nngp`).
* `NTK.Deep.LimitingNTK`: Deterministic backward covariance tensor `deepLimitingBackwardCov`
  and recursive limiting NTK matrix `deepLimitingNTK` (Proposition 2.27), positive
  semidefiniteness, Loewner dominance, and two-layer consistency with `limitingFullNTKMatrix`.
* `NTK.Deep.GaussianDecoupling`: One-sided Gaussian conditioning onto low-rank forward
  subspaces (Lemma 2.26), quadratic form evaluation under Gaussian matrix laws, and
  asymptotic convergence in probability of `deepEmpiricalNTK` to `deepLimitingNTK` (Theorem 2.27).
-/
