/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Fluctuations
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Asymptotics

/-!
# Width, depth, and double-scaling limits

Moment limits and weak convergence are separate declarations.  In particular, the weak Gaussian
limit is not inferred merely from convergence of every fixed moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology

namespace NeuralNetwork.DeepLinear

/-- Equal-width correction for a network with `depth` weight layers. -/
def equalWidthCorrection (m width depth : ℕ) : ℝ :=
  widthMomentFactor m width ^ (depth - 1)

/-- Product law of independent centered Gaussian output coordinates, bundled as a probability
measure. -/
def iidGaussianProbabilityMeasure (n : ℕ) (v : ℝ≥0) : ProbabilityMeasure (Fin n → ℝ) :=
  ⟨Measure.pi (fun _ : Fin n => gaussianReal 0 v), inferInstance⟩

/-- At fixed depth, every equal-width correlator amplitude approaches its Gaussian value.

Informal proof: each factor in `widthMomentFactor m n` tends to one, hence its fixed power tends to
one.  Multiply by the fixed two-point amplitude.  This is also an immediate consequence of
`widthMomentFactor_sub_linear_isBigO`.  Source: `docs/Renormalization.md`, Section
`sec:infinite-width-limit_DLN`.
-/
theorem tendsto_equalWidth_correlatorAmplitude (m depth : ℕ) (G2 : ℝ) :
    Tendsto (fun width : ℕ => equalWidthCorrection m width depth * G2 ^ m)
      atTop (nhds (G2 ^ m)) := by
  sorry

/-- Fixed-depth deep-linear outputs converge weakly to the appropriate product Gaussian.

Informal proof: couple each layer to a fresh standard Gaussian vector.  Its normalized squared
norm has mean one and variance `2/width`, so it converges to one in `L²` and probability.  Induct
over the fixed number of hidden layers; continuous mapping and Slutsky's theorem show that the
random output variance converges to the deterministic variance
`Cw^(hiddenDepth+1) * normalizedEnergy x`.  Bounded continuous test functions then give weak
convergence.  Source: <https://en.wikipedia.org/wiki/Slutsky%27s_theorem> and
`docs/Renormalization.md`, Section `sec:infinite-width-limit_DLN`.
-/
theorem tendsto_outputLaw_fixedDepth_atTop (dIn dOut hiddenDepth : ℕ)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (hIn : 0 < dIn) :
    Tendsto
      (fun width : ℕ =>
        (MLPShape.constantHiddenShape dIn dOut width hiddenDepth).deepLinearOutputProbabilityMeasure
          Cw x)
      atTop
      (nhds (iidGaussianProbabilityMeasure dOut
        (Cw ^ (hiddenDepth + 1) * NeuralNetwork.normalizedEnergyNNReal x))) := by
  sorry

/-- At criticality and fixed finite width, every moment order at least four diverges with depth.

Informal proof: for `m≥2` and positive `width`, the factor `widthMomentFactor m width` contains
the strictly larger-than-one term `1+2/width`; all remaining terms are at least one.  Its powers
therefore tend to `+∞`, and multiplication by `q^m>0` preserves divergence.  Source:
`docs/Renormalization.md`, Section `sec:large-depth-behavior_DLN`.
-/
theorem tendsto_correlatorAmplitude_fixedWidth_atTop (m width : ℕ) (q : ℝ)
    (hm : 2 ≤ m) (hwidth : 0 < width) (hq : 0 < q) :
    Tendsto (fun depth : ℕ => equalWidthCorrection m width depth * q ^ m)
      atTop atTop := by
  sorry

/-- The fixed-depth large-width and fixed-width large-depth regimes do not commute.

This real-valued statement records the two relevant filter limits separately; it does not pretend
that `+∞` is a real number.

Informal proof: combine `tendsto_equalWidth_correlatorAmplitude` with
`tendsto_correlatorAmplitude_fixedWidth_atTop`.  The former has finite limit `q^m`; the latter
diverges to `+∞`.  Source: `docs/Renormalization.md`, discussion of noncommuting limits.
-/
theorem width_depth_limits_do_not_commute (m width depth : ℕ) (q : ℝ)
    (hm : 2 ≤ m) (hwidth : 0 < width) (hq : 0 < q) :
    Tendsto (fun n : ℕ => equalWidthCorrection m n depth * q ^ m)
        atTop (nhds (q ^ m)) ∧
      Tendsto (fun L : ℕ => equalWidthCorrection m width L * q ^ m)
        atTop atTop := by
  exact ⟨tendsto_equalWidth_correlatorAmplitude m depth q,
    tendsto_correlatorAmplitude_fixedWidth_atTop m width q hm hwidth hq⟩

/-- Equal-width correction in the simultaneous width-depth scaling regime.

Informal proof: write the factor as `1 + m(m-1)/n + O(n⁻²)`.  Under `L(n)/n→r` and
`L(n)→∞`, the linear exponent tends to `m(m-1)r`, while `L(n)` times the quadratic error tends to
zero.  Apply the logarithmic `(1+u_n)^(L n)` exponential limit; the subtraction of one from depth
is negligible.  Source: <https://en.wikipedia.org/wiki/Exponential_function#Formal_definition>.
-/
theorem tendsto_equalWidthCorrection_doubleScaling (m : ℕ) (L : ℕ → ℕ) (r : ℝ)
    (hL : Tendsto L atTop atTop)
    (hRatio : Tendsto (fun n : ℕ => (L n : ℝ) / (n : ℝ)) atTop (nhds r)) :
    Tendsto (fun n : ℕ => equalWidthCorrection m n (L n)) atTop
      (nhds (Real.exp ((m : ℝ) * (m - 1 : ℕ) * r))) := by
  sorry

/-- Double-scaled fourth cumulant amplitude.

Informal proof: the fourth connected coefficient is `C₂-1`; specialize
`tendsto_equalWidthCorrection_doubleScaling` to `m=2` and use continuity of subtraction and
multiplication.  Source: `docs/Renormalization.md`, double-scaling four-point formula.
-/
theorem tendsto_fourthCumulantAmplitude_doubleScaling (L : ℕ → ℕ) (r q : ℝ)
    (hL : Tendsto L atTop atTop)
    (hRatio : Tendsto (fun n : ℕ => (L n : ℝ) / (n : ℝ)) atTop (nhds r)) :
    Tendsto (fun n : ℕ => (equalWidthCorrection 2 n (L n) - 1) * q ^ 2) atTop
      (nhds ((Real.exp (2 * r) - 1) * q ^ 2)) := by
  sorry

/-- Double-scaled sixth cumulant amplitude.

Informal proof: the sixth connected coefficient is `C₃-3C₂+2`.  Apply the double-scaling theorem
at `m=3` and `m=2`, then use continuity of the finite linear combination and multiplication by
`q³`.  Source: `docs/Renormalization.md`, double-scaling six-point formula.
-/
theorem tendsto_sixthCumulantAmplitude_doubleScaling (L : ℕ → ℕ) (r q : ℝ)
    (hL : Tendsto L atTop atTop)
    (hRatio : Tendsto (fun n : ℕ => (L n : ℝ) / (n : ℝ)) atTop (nhds r)) :
    Tendsto
      (fun n : ℕ =>
        (equalWidthCorrection 3 n (L n) - 3 * equalWidthCorrection 2 n (L n) + 2) * q ^ 3)
      atTop (nhds ((Real.exp (6 * r) - 3 * Real.exp (2 * r) + 2) * q ^ 3)) := by
  sorry

end NeuralNetwork.DeepLinear

end

end
