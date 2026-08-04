/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.GaussianLayer

/-!
# Exact finite-depth moments of deep linear networks

The main statements are shape-safe integral identities for LML's existing output law.  Scalar
amplitudes and Wick tensors are factored out as reusable deterministic definitions.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology

namespace NeuralNetwork.DeepLinear

universe uA uJ

/-- Product of all finite-width radial corrections before the observed output layer. -/
def hiddenWidthCorrection (m : ℕ) (widths : List ℕ) : ℝ :=
  (widths.map (widthMomentFactor m)).prod

/-- Scalar amplitude multiplying the output-index Wick tensor. -/
def correlatorAmplitude (Cw : ℝ≥0) (q : ℝ) (m : ℕ) (widths : List ℕ) : ℝ :=
  (((Cw : ℝ) ^ (widths.length + 1) * q) ^ m) * hiddenWidthCorrection m widths

@[simp] theorem hiddenWidthCorrection_nil (m : ℕ) : hiddenWidthCorrection m [] = 1 := by
  simp [hiddenWidthCorrection]

@[simp] theorem hiddenWidthCorrection_cons (m n : ℕ) (widths : List ℕ) :
    hiddenWidthCorrection m (n :: widths) =
      widthMomentFactor m n * hiddenWidthCorrection m widths := by
  simp [hiddenWidthCorrection]

/-- Wick's pairing sum for the Kronecker covariance on a list of output indices. -/
def pairingTensor {κ : Type uJ} [DecidableEq κ] {m : ℕ} (a : Fin (2 * m) → κ) : ℝ :=
  Renormalization.wick (fun r s => if a r = a s then 1 else 0) Finset.univ

/-- Every odd joint output moment vanishes.

Informal proof: condition on the penultimate layer.  The final output row is a centered Gaussian,
so its odd Wick moment is zero; integrating this zero conditional moment proves the claim.  The
base case is `Renormalization.integral_pow_gaussianReal_odd`.  Source:
`docs/Renormalization.md`, final paragraphs of Section `sec:DLN`.
-/
theorem jointMoment_outputLaw_odd {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m + 1) → Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, (∏ r, z (a r)) ∂S.deepLinearOutputLaw Cw x = 0 := by
  sorry

/-- Exact even joint output moment at arbitrary finite positive widths.

Informal proof: condition on the penultimate activations and apply Wick's theorem to the centered
Gaussian final layer.  The index contractions give `pairingTensor`; the random variance gives the
`m`-th normalized-energy moment.  Iterating
`integral_normalizedEnergy_pow_randomLayerKernel` over the shape yields precisely the product
`hiddenWidthCorrection`.  Source: `docs/Renormalization.md`, equations
`eq:deep-linear-inductive-ansatz`, `eq:combinatorial-2m`, and `eq:2m-full-solution`.
-/
theorem jointMoment_outputLaw_even {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m) → Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, (∏ r, z (a r)) ∂S.deepLinearOutputLaw Cw x =
      pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths := by
  sorry

/-- Exact even moment of one output coordinate.

Informal proof: specialize `jointMoment_outputLaw_even` to the constant output-index map.  Every
Kronecker factor is one and the number of pairings of `2m` points is
`(2m)!/(2^m m!) = gaussianEvenCoeff m`.  Source:
<https://en.wikipedia.org/wiki/Double_factorial#Applications>.
-/
theorem integral_coordinate_pow_outputLaw_even {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, z j ^ (2 * m) ∂S.deepLinearOutputLaw Cw x =
      gaussianEvenCoeff m *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths := by
  sorry

/-- Covariance of two batch-output coordinates.  The theorem explicitly uses Mathlib's
`covariance`, not merely an uncentered second moment.

Informal proof: all outputs are centered by the odd-moment theorem.  Conditioning one layer gives
zero for different output rows and `Cw` times the previous normalized Gram entry for equal rows.
Induction over `S` gives the displayed closed form.  Source: `docs/Renormalization.md`, equations
`eq:two-point-function-deep-linear-layer-ell` and `eq:deep-linear-kernel-recursion`.
-/
theorem covariance_batchOutputLaw {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    covariance (fun z => z a i) (fun z => z b j) (S.deepLinearBatchLaw Cw D) =
      if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 := by
  sorry

/-- Uncentered form of the exact finite-dataset covariance solution.

Informal proof: use `jointMoment_outputLaw_odd` to replace covariance by the second moment, then
apply `covariance_batchOutputLaw`.  This is the closed solution `G^(L)=Cw^L G^(0)` in
`docs/Renormalization.md`, equation `eq:deep-linear-exponential-solution`.
-/
theorem covariance_batchOutputLaw_closedForm {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, z a i * z b j ∂S.deepLinearBatchLaw Cw D =
      if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 := by
  sorry

/-- Subcritical covariance amplitudes tend to zero. -/
theorem tendsto_covariance_of_weightVariance_lt_one (Cw q : ℝ)
    (hCw0 : 0 ≤ Cw) (hCw1 : Cw < 1) :
    Tendsto (fun L : ℕ => Cw ^ L * q) atTop (nhds 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hCw0 hCw1).mul_const q

/-- At criticality the covariance amplitude is exactly constant. -/
@[simp] theorem covariance_eq_of_weightVariance_eq_one (q : ℝ) (L : ℕ) :
    (1 : ℝ) ^ L * q = q := by simp

/-- A positive supercritical covariance amplitude diverges to `+∞`.

Informal proof: `Cw^L → +∞` for `Cw>1`; multiplication by the fixed positive `q` preserves
divergence.  This is the geometric-sequence criterion; see
<https://en.wikipedia.org/wiki/Geometric_progression#Geometric_series>.
-/
theorem tendsto_covariance_atTop_of_one_lt_weightVariance (Cw q : ℝ)
    (hCw : 1 < Cw) (hq : 0 < q) :
    Tendsto (fun L : ℕ => Cw ^ L * q) atTop atTop := by
  exact Tendsto.atTop_mul_const hq (tendsto_pow_atTop_atTop_of_one_lt hCw)

/-- A negative supercritical off-diagonal covariance diverges in absolute value. -/
theorem tendsto_abs_covariance_atTop_of_one_lt_weightVariance (Cw q : ℝ)
    (hCw : 1 < Cw) (hq : q ≠ 0) :
    Tendsto (fun L : ℕ => |Cw ^ L * q|) atTop atTop := by
  simpa [abs_mul, abs_of_pos (lt_trans (by norm_num) hCw)] using
    tendsto_covariance_atTop_of_one_lt_weightVariance Cw |q| hCw (abs_pos.mpr hq)

/-- The first layer is exactly a product Gaussian law, not merely moment-equivalent to it.

Informal proof: specialize the one-layer conditional law to a singleton batch and transport along
the canonical equivalence between a singleton Euclidean vector and `ℝ`.  The resulting coordinate
variance is `Cw * normalizedEnergy x`.  Source: `docs/Renormalization.md`, equation
`eq:deep-linear-gaussian-first-layer`.
-/
theorem firstLayerOutputLaw_eq_pi_gaussianReal {dIn dOut : ℕ} (Cw : ℝ≥0)
    (x : Fin dIn → ℝ) (hIn : 0 < dIn) :
    (MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      Measure.pi (fun _ : Fin dOut =>
        gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x)) := by
  sorry

end NeuralNetwork.DeepLinear

end

end
