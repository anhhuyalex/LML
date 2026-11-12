/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaTheorem
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaConstant
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# Fixed point of the replica-symmetric variational problem

Talagrand, *Spin Glasses* Vol. I, Section 1.13, Eq. (1.408).
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace SpinGlasses

end SpinGlasses
