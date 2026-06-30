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
public import LeanMachineLearning.Optimization.Approximation.InfiniteWidth
public import LeanMachineLearning.Optimization.Approximation.BarronNorm
public import LeanMachineLearning.Optimization.Approximation.Sampling

/-!
# Neural network approximation theory

Re-exports all approximation theory results:

* `Approximation.Basic` : activations, network function classes
* `Approximation.Univariate` : Proposition 2.1 (Lipschitz → threshold net)
* `Approximation.Multivariate` : Theorem 2.1 (multivariate, curse of dimension)
* `Approximation.Universal` : Theorem 2.3 (universal approximation, Stone-Weierstrass)
* `Approximation.InfiniteWidth` : Definition 3.2 (infinite-width networks), Prop 3.1
* `Approximation.BarronNorm` : Definition 3.1 (Barron norm), Theorem 3.1
* `Approximation.Sampling` : Lemma 3.1 (Maurey), Lemma 3.2 (signed measures), Barron bound

-/
