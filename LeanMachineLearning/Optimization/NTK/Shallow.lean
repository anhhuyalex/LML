/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Shallow.Linearization
public import LeanMachineLearning.Optimization.NTK.Shallow.Kernel
public import LeanMachineLearning.Optimization.NTK.Shallow.DatasetNTK
public import LeanMachineLearning.Optimization.NTK.Shallow.Universal

/-!
# Shallow-network NTK (fixed outer layer)

The fixed-outer-layer theory of Chapter 4 of the deep learning theory notes (Telgarsky 2021):
linearization bounds, the empirical and limiting NTK, the dataset Gram matrix and MSE gradient,
and the universality of the NTK RKHS.
-/
