/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer

/-!
# Training dynamics of the two-layer NTK

Gradient flow, lazy training and kernel-freeze bounds for the two-layer network with
trainable inner and readout weights.
-/
