/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.Linearization
public import LeanMachineLearning.Optimization.NTK.Kernel
public import LeanMachineLearning.Optimization.NTK.ReluClosedForm
public import LeanMachineLearning.Optimization.NTK.Universal

/-!
# Neural tangent kernel and linearization near initialization

Re-exports all NTK results corresponding to Chapter 4 of the deep learning theory notes
(Telgarsky 2021).

## Structure

* `NTK.Basic` : scaled shallow networks, Gaussian initialization, Taylor linearization.
* `NTK.Linearization` : linearization bounds for smooth activations (Proposition 4.1)
  and for the ReLU via Gaussian concentration (Lemma 4.1 and Lemma 4.2).
* `NTK.Kernel` : empirical NTK with and without explicit outer coefficients, limiting NTK, and
  almost sure convergence along growing width (Lemma 4.3). It re-exports the three helper
  modules `NTK.IIDAverage` (i.i.d. averages and Chebyshev bounds), `NTK.MatrixUtil` (matrix and
  Frobenius-norm facts, `matrixCLM`) and `NTK.DatasetNTK` (the empirical NTK matrix on a finite
  dataset and the MSE gradient).
* `NTK.ReluClosedForm` : ReLU closed form (Proposition 4.2); it depends on the
  two-dimensional Gaussian computation in `NTK.Initialization`.
* `NTK.Universal` : NTK domain, RKHS predictor class, and universal approximation
  (Theorem 4.1).

## Main results

| Name | Statement |
|------|-----------|
| `NTK.smoothLinearizationBound` | `|f(x;W)−f₀,V(x;W)| ≤ β/(2√m)·‖W−V‖_F²` |
| `NTK.reluSignConcentration` | Hoeffding bound on sign-changing neurons |
| `NTK.reluLinearizationBound` | `‖f(x;W)−f₀(x;W)‖ ≤ (2B^{4/3}+…)/m^{1/6}` w.h.p. |
| `NTK.ntk_convergence` | `kₘ(x,x') →_as k(x,x')` by SLLN as width grows |
| `NTK.reluNTK_closedForm` | `k(x,x') = xᵀx'·(π−arccos(xᵀx'))/(2π)` |
| `NTK.isUniversal` | NTK RKHS is a universal approximator over `𝒳` |

-/
