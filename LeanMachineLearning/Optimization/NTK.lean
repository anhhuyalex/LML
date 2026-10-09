/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.FeatureLearning.Basic
public import LeanMachineLearning.Optimization.NTK.FeatureLearning.Criterion
public import LeanMachineLearning.Optimization.NTK.Foundations
public import LeanMachineLearning.Optimization.NTK.Shallow
public import LeanMachineLearning.Optimization.NTK.Initialization
public import LeanMachineLearning.Optimization.NTK.Initialization.Peripheral
public import LeanMachineLearning.Optimization.NTK.ReLU
public import LeanMachineLearning.Optimization.NTK.Training
public import LeanMachineLearning.Optimization.NTK.Deep

/-!
# Neural tangent kernel and linearization near initialization

Umbrella module for the whole NTK development.  Chapter 4 of the deep learning theory notes
(Telgarsky 2021) is `Basic` and `Shallow`; the random-initialization (NNGP) theory and the
two-layer training limit follow it.

## Structure

* `NTK.Basic` : scaled shallow networks, Gaussian initialization, Taylor linearization.
* `NTK.Foundations` : network-independent tools: `Foundations.MatrixUtil` (Frobenius-norm facts,
  `matrixCLM`), `IIDAverage` (i.i.d. averages and Chebyshev bounds), `SlutskyTightness`.
* `NTK.Shallow` : fixed outer layer. `Linearization` (Proposition 4.1, Lemmas 4.1 and 4.2),
  `Kernel` (empirical and limiting NTK, almost sure convergence, Lemma 4.3), `DatasetNTK` (Gram
  matrix on a finite dataset, MSE gradient), `Universal` (NTK RKHS, Theorem 4.1).
* `NTK.ReLU` : Cho–Saul arc-cosine kernel (`ChoSaul`, `ArcCosine`) and the
  ReLU NTK closed form `ClosedForm` (Proposition 4.2). It sits below `NTK.Initialization`.
* `NTK.Initialization` : random initialization of the two-layer network, NNGP limits and the
  full-NTK convergence; `Initialization.Peripheral` holds secondary consequences.
* `NTK.Training` : `GradientFlow` (gradient flow, lazy training bootstrap, prediction) and
  `TwoLayer` (parameter packing, concentration, and the end-to-end kernel-freeze bound).
* `NTK.FeatureLearning` : the two-layer network with an explicit scaling knob `γ`: single-neuron
  gradients, the exact one-step feature update, the predictor dynamics `∂_t f = -(η/(mγ²)) K r`, and
  the criterion `(1/n)‖Δh‖² = Θ(1) ↔ η = Θ(γ√n)`.
* `NTK.Deep` : multilayer MLP parameters, exact layerwise NTK decomposition (Proposition 2.25),
  recursive limiting NTK kernel (Proposition 2.27), and one-sided Gaussian
  conditioning (Lemma 2.26).

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
