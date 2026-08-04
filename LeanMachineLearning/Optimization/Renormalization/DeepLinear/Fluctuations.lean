/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Moments

/-!
# Connected correlators and energy fluctuations

Low-order results are stated as consequences of the general amplitude API.  This keeps the
probability proofs independent of an enumeration of the three or fifteen Wick pairings.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace NeuralNetwork.DeepLinear

/-- The two-point amplitude at the observed output layer. -/
def twoPointAmplitude (Cw : ℝ≥0) (q : ℝ) (widths : List ℕ) : ℝ :=
  (Cw : ℝ) ^ (widths.length + 1) * q

/-- The fourth correlator amplitude is the squared two-point amplitude times the width
correction.

Informal proof: unfold `correlatorAmplitude` at `m=2`; no probabilistic argument remains.  Then
use `widthMomentFactor_two` in every list factor.  Source: `docs/Renormalization.md`, equation
`eq:deep-linear-four-point-solution`.
-/
theorem fourPointAmplitude_eq (Cw : ℝ≥0) (q : ℝ) (widths : List ℕ) :
    correlatorAmplitude Cw q 2 widths =
      hiddenWidthCorrection 2 widths * twoPointAmplitude Cw q widths ^ 2 := by
  unfold correlatorAmplitude twoPointAmplitude
  ring

/-- Exact connected four-point output tensor.

Informal proof: apply `Renormalization.jointCumulant_four_of_centered`, substitute the exact
second and fourth moment formulas, and factor the common three-pairing Kronecker tensor.  This
leaves `C₂(widths)-1`.  Source: `docs/Renormalization.md`, equations
`eq:deep-linear-four-point-connected` and `eq:deep-linear-four-point-solution`.
-/
theorem jointCumulant_four_outputLaw {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (a : Fin 4 → Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    Renormalization.jointCumulant (S.deepLinearOutputLaw Cw x) (fun r z => z (a r)) =
      pairingTensor (m := 2) a * (hiddenWidthCorrection 2 S.hiddenWidths - 1) *
        twoPointAmplitude Cw (NeuralNetwork.normalizedEnergy x) S.hiddenWidths ^ 2 := by
  sorry

/-- Distinct output neurons have correlated squares at finite hidden width.

Informal proof: expand covariance as `E[z_j²z_k²]-E[z_j²]E[z_k²]`.  For `j≠k`, exactly one of the
three fourth-order Kronecker pairings survives, while each second moment is the two-point
amplitude.  Source: `docs/Renormalization.md`, equation `eq:deep-linear-scale`.
-/
theorem covariance_sq_coordinates {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (j k : Fin dOut) (hjk : j ≠ k)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    covariance (fun z => z j ^ 2) (fun z => z k ^ 2) (S.deepLinearOutputLaw Cw x) =
      (hiddenWidthCorrection 2 S.hiddenWidths - 1) *
        twoPointAmplitude Cw (NeuralNetwork.normalizedEnergy x) S.hiddenWidths ^ 2 := by
  sorry

/-- Exact variance of normalized output energy.

Informal proof: use `variance_eq_sub` and the scalar energy moments for orders one and two.  The
order-two correction includes the observed width, hence `widthMomentFactor 2 dOut` multiplies the
hidden correction.  Source: `docs/Renormalization.md`, Section `sec:fluctuations_DLN`.
-/
theorem variance_normalizedEnergy {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ)
    (hIn : 0 < dIn) (hOut : 0 < dOut)
    (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    variance NeuralNetwork.normalizedEnergy (S.deepLinearOutputLaw Cw x) =
      (hiddenWidthCorrection 2 S.hiddenWidths * widthMomentFactor 2 dOut - 1) *
        twoPointAmplitude Cw (NeuralNetwork.normalizedEnergy x) S.hiddenWidths ^ 2 := by
  sorry

/-- Equal-width specialization of the exact normalized-energy variance.

Informal proof: every factor `widthMomentFactor 2 n` is `1+2/n`; multiplying the hidden factors
and the observed-width factor gives the power `L`.  This is finite-product algebra after
`variance_normalizedEnergy`.  Source: `docs/Renormalization.md`, final formula of Section
`sec:fluctuations_DLN`.
-/
theorem variance_normalizedEnergy_equalWidth (dIn width hiddenDepth : ℕ)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (hIn : 0 < dIn) (hWidth : 0 < width) :
    variance NeuralNetwork.normalizedEnergy
        ((MLPShape.constantHiddenShape dIn width width hiddenDepth).deepLinearOutputLaw Cw x) =
      ((1 + 2 / (width : ℝ)) ^ (hiddenDepth + 1) - 1) *
        ((Cw : ℝ) ^ (hiddenDepth + 1) * NeuralNetwork.normalizedEnergy x) ^ 2 := by
  sorry

/-- Exact sixth correlator amplitude.

Informal proof: unfold the general amplitude at `m=3` and apply
`widthMomentFactor_three` in each hidden width.  Source: `docs/Renormalization.md`, equation
`eq:deep-linear-six-point-solution`.
-/
theorem sixPointAmplitude_eq (Cw : ℝ≥0) (q : ℝ) (widths : List ℕ) :
    correlatorAmplitude Cw q 3 widths =
      hiddenWidthCorrection 3 widths * twoPointAmplitude Cw q widths ^ 3 := by
  unfold correlatorAmplitude twoPointAmplitude
  ring

/-- Coefficient of the connected sixth-order Kronecker tensor.

Informal proof: the moment-cumulant relation at order six has one sixth moment, fifteen products
of a fourth and a second moment, and thirty products of three second moments.  After factoring the
fifteen-pairing tensor, the amplitude is `C₃-3C₂+2`.  Source:
`docs/Renormalization.md`, Section `sec:higher-point-functions_DLN`, and the general
moment-cumulant relation at <https://en.wikipedia.org/wiki/Cumulant#Joint_cumulants>.
-/
theorem sixthCumulantAmplitude_eq (Cw : ℝ≥0) (q : ℝ) (widths : List ℕ) :
    correlatorAmplitude Cw q 3 widths
        - 3 * hiddenWidthCorrection 2 widths * twoPointAmplitude Cw q widths ^ 3
        + 2 * twoPointAmplitude Cw q widths ^ 3 =
      (hiddenWidthCorrection 3 widths - 3 * hiddenWidthCorrection 2 widths + 2) *
        twoPointAmplitude Cw q widths ^ 3 := by
  rw [sixPointAmplitude_eq]
  ring

/-- Appending one hidden width gives the public general correlator recurrence.

Informal proof: unfold the list product, use `List.prod_append`, and split the power of `Cw` at
the new list length.  Source: `docs/Renormalization.md`, equation
`eq:deep-linear-recursion-relation-2m`.
-/
theorem correlatorAmplitude_append (Cw : ℝ≥0) (q : ℝ) (m n : ℕ)
    (widths : List ℕ) :
    correlatorAmplitude Cw q m (widths ++ [n]) =
      (Cw : ℝ) ^ m * widthMomentFactor m n * correlatorAmplitude Cw q m widths := by
  simp only [correlatorAmplitude, hiddenWidthCorrection, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, List.length_append,
    List.length_singleton, mul_one]
  rw [show widths.length + 1 + 1 = 1 + (widths.length + 1) by omega, pow_add, mul_pow]
  ring

end NeuralNetwork.DeepLinear

end

end
