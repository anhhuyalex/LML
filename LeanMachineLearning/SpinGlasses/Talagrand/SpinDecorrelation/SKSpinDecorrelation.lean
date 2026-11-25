/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.SpinDecorrelation.SpinDecorrelation

/-!
# Re-export of model-independent spin decorrelation (`SpinDecorrelation.lean`)

The model-independent Proposition 1.4.14 (`SpinGlasses.spinDecorrConst`,
`SpinGlasses.integral_sq_prod_sub_prod_le_finset`, etc.) lives in
`SpinDecorrelation/SpinDecorrelation.lean` so that both the Sherrington-Kirkpatrick and
perceptron developments can import it without an `SK*` module dependency.
-/
