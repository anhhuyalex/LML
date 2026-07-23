/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Basic
public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import LeanMachineLearning.Optimization.Lasso.LCP
public import LeanMachineLearning.Optimization.Lasso.MirrorFlow
public import LeanMachineLearning.Optimization.Lasso.Theorems

/-!
# Diagonal Linear Networks and the Lasso Regularization Path

This module formalizes the exact and approximate connections between the 
training trajectories of diagonal linear networks and the lasso regularization path.
-/
