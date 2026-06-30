/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import LeanMachineLearning.Optimization.Approximation.Univariate
public import LeanMachineLearning.Optimization.Approximation.Multivariate
public import LeanMachineLearning.Optimization.Approximation.Universal

/-!
# Neural network approximation theory

Re-exports all approximation theory results:

* `Approximation.Basic` : activations, network function classes
* `Approximation.Univariate` : Proposition 2.1 (Lipschitz → threshold net)
* `Approximation.Multivariate` : Theorem 2.1 (multivariate, curse of dimension)
* `Approximation.Universal` : Theorem 2.3 (universal approximation, Stone-Weierstrass)

-/
