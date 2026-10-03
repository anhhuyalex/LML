/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Foundations.GramProjector
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixMeasurability
public import LeanMachineLearning.Optimization.NTK.Foundations.TendstoInMeasureUtil
public import LeanMachineLearning.Optimization.NTK.Foundations.IIDAverage
public import LeanMachineLearning.Optimization.NTK.Foundations.SlutskyTightness
public import LeanMachineLearning.Optimization.NTK.Foundations.Concentration
public import LeanMachineLearning.Optimization.NTK.Foundations.InfinitePiPrefix
public import LeanMachineLearning.Optimization.NTK.Foundations.ODE

/-!
# NTK foundations

Network-independent tools used throughout the NTK development:

* `MatrixUtil`, `GramProjector`, `MatrixMeasurability`: matrix and Frobenius-norm facts
  (`matrixCLM`), Gram projectors (`IsStarProjection`), and measurability of matrix operations;
* `IIDAverage`, `SlutskyTightness`, `TendstoInMeasureUtil`: i.i.d. averages with Chebyshev bounds,
  Slutsky/tightness/Markov lemmas, and convergence in measure for matrix-valued sequences;
* `InfinitePiPrefix`: restricting i.i.d. sequences/arrays to their first `n` coordinates;
* `Concentration`: standard-Gaussian moment and tail bounds with probability-measure union-bound
  algebra;
* `ODE`: Grönwall, the bootstrap principle, global flows of locally Lipschitz fields.
-/
