/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.ReLU.ChoSaul
public import LeanMachineLearning.Optimization.NTK.ReLU.ArcCosine
public import LeanMachineLearning.Optimization.NTK.ReLU.ClosedForm

/-!
# ReLU arc-cosine kernel

The Cho–Saul arc-cosine kernel for ReLU and the closed form of the ReLU NTK
(Proposition 4.2).

## Structure

* `ReLU.ChoSaul` : angular and polar-coordinate Gaussian integrals for the Cho–Saul kernel.
* `ReLU.ArcCosine` : the bivariate ReLU and ReLU-indicator expectations (arc-cosine kernel).
* `ReLU.ClosedForm` : the closed form of the ReLU NTK (Proposition 4.2).
-/
