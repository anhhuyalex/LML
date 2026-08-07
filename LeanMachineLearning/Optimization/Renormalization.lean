/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Basic
public import LeanMachineLearning.Optimization.Renormalization.Activation
public import LeanMachineLearning.Optimization.Renormalization.Action
public import LeanMachineLearning.Optimization.Renormalization.Cumulant
public import LeanMachineLearning.Optimization.Renormalization.Convolution
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear
public import LeanMachineLearning.Optimization.Renormalization.Finpartition
public import LeanMachineLearning.Optimization.Renormalization.Gaussian
public import LeanMachineLearning.Optimization.Renormalization.InducedLaw
public import LeanMachineLearning.Optimization.Renormalization.Initialization
public import LeanMachineLearning.Optimization.Renormalization.MLPInitialization
public import LeanMachineLearning.Optimization.Renormalization.Network
public import LeanMachineLearning.Optimization.Renormalization.NearlyGaussian
public import LeanMachineLearning.Optimization.Renormalization.ParameterizedMLP
public import LeanMachineLearning.Optimization.Renormalization.Perturbation
public import LeanMachineLearning.Optimization.Renormalization.Quartic
public import LeanMachineLearning.Optimization.Renormalization.RGFlow

/-!
# Renormalization

Formal infrastructure for the renormalization and nearly-Gaussian expansions used in machine
learning theory.

The library exports finite-partition algebra, joint moments, cumulants, Gaussian Wick calculus,
explicit actions and Gaussian expectation, general exponential perturbations, symmetric quartic
Gaussian specializations, general even-coupling hierarchies, the Chapter 2 neural-network
architecture, initialization, and induced-law APIs, and the RG-flow theory of preactivation
statistics at an arbitrary layer.
-/
