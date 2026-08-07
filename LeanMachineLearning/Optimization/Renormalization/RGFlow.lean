/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.RGFlow.Metric
public import LeanMachineLearning.Optimization.Renormalization.RGFlow.FourPointVertex
public import LeanMachineLearning.Optimization.Renormalization.RGFlow.DepthInduction
public import LeanMachineLearning.Optimization.Renormalization.RGFlow.Marginalization
public import LeanMachineLearning.Optimization.Renormalization.RGFlow.Subleading
public import LeanMachineLearning.Optimization.Renormalization.RGFlow.Flow

/-!
# RG flow of preactivations

Formal infrastructure for the chapter "RG Flow of Preactivations" of `docs/Renormalization.md`:
the stochastic-metric mean/fluctuation decomposition, the four-point vertex and its
nearly-Gaussian action match, the depth-induction kernel and vertex recursions, marginalization
rules, the subleading (next-to-leading-order) metric correction, and the relevant/irrelevant
coupling vocabulary of representation-group flow.

The library reuses `NeuralNetwork.layerCovariance`/`map_evalBatch_layerGaussianInit`
(`InducedLaw.lean`) and `Renormalization.QuarticCoupling`/`EvenAction`/
`HierarchicallyNearlyGaussian` (`Quartic.lean`/`NearlyGaussian.lean`) throughout; no Wick-pairing
enumeration or quartic-response calculation is re-derived here.

See `LML/blueprint/src/chapters/renormalization.tex`, Chapter "RG flow of preactivations: from
Gaussian to nearly-Gaussian ensembles", for the full mathematical plan, module-by-module
correspondence, and the failure-analysis/compliance discussion this library implements.
-/
