/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Basic
public import LeanMachineLearning.Optimization.Renormalization.Cumulant
public import LeanMachineLearning.Optimization.Renormalization.Finpartition
public import LeanMachineLearning.Optimization.Renormalization.Gaussian
public import LeanMachineLearning.Optimization.Renormalization.Perturbation
public import LeanMachineLearning.Optimization.Renormalization.Quartic

/-!
# Renormalization

Formal infrastructure for the renormalization and nearly-Gaussian expansions used in machine
learning theory.

The current library exports finite-partition algebra, joint moments, cumulants, Gaussian Wick
calculus, general exponential perturbations, and symmetric quartic Gaussian specializations.
-/
