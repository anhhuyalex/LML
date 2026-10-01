/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Foundations.IIDAverage
public import LeanMachineLearning.Optimization.NTK.Foundations.SlutskyTightness

/-!
# NTK foundations

Network-independent tools used throughout the NTK development: matrix and Frobenius-norm facts
(`matrixCLM`), i.i.d. averages with Chebyshev bounds, and Slutsky/tightness/Markov lemmas.
-/
