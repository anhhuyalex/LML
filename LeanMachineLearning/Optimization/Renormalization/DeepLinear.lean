/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Basic
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.GaussianLayer
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Moments
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Fluctuations
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Asymptotics
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Limits

/-!
# Deep linear networks at Gaussian initialization

Exact finite-width moment, cumulant, fluctuation, and asymptotic statements for LML's shape-safe
deep linear network model.
-/
