/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Infinite-width shallow networks and the univariate integral representation

This file covers Section 3.1 and Definition 3.2 of the deep learning theory notes
(Telgarsky 2021).

Two ideas are developed here.

1. **Infinite-width networks** (Definition 3.2): shallow networks defined not by a finite
   parameter tuple but by a signed measure ν over weight space.  Evaluating such a network
   at x ∈ ℝᵈ gives `∫ σ(wᵀx) dν(w)`.  The *mass* of the network is the total variation
   `|ν|(ℝᵖ)`.

2. **Univariate integral representation** (Proposition 3.1): every differentiable function
   g : ℝ → ℝ with g(0) = 0 can be written *exactly* as an infinite-width threshold network
   on [0, 1]:
   ```
   g(x) = ∫₀¹ 1[x ≥ b] · g'(b) db.
   ```
   This is essentially just the fundamental theorem of calculus.

## Main definitions

* `InfiniteWidthNetwork σ p` : an infinite-width shallow network with activation σ and
  weight space ℝᵖ, parameterized by a signed measure ν on ℝᵖ.
* `InfiniteWidthNetwork.eval` : evaluate the network, `x ↦ ∫ σ(wᵀx) dν(w)`.
* `InfiniteWidthNetwork.mass` : total-variation mass |ν|(ℝᵖ).
* `thresholdInfiniteWidth` : the threshold-network form of the univariate representation.

## Main results

* `univariateIntegralRep` : Proposition 3.1 — for differentiable g with g(0) = 0,
  `g(x) = ∫₀¹ 1[x ≥ b] * g'(b) db` for all x ∈ [0, 1].

-/

@[expose] public section

open MeasureTheory Real Set

namespace Approximation.InfiniteWidth

/-! ### Infinite-width network (Definition 3.2) -/

/-- An infinite-width shallow network over weight space ℝᵖ with scalar output.
The network is characterized by a signed measure ν over weight vectors in ℝᵖ:
  `x ↦ ∫ σ(wᵀx) dν(w)`.
(Definition 3.2, Telgarsky 2021.) -/
structure InfiniteWidthNetwork (σ : ℝ → ℝ) (p : ℕ) where
  /-- The signed measure over weight space ℝᵖ. -/
  measure : SignedMeasure (Fin p → ℝ)

/-- Evaluate an infinite-width network at a point x ∈ ℝᵈ.
Returns `∫ σ(∑ⱼ wⱼ xⱼ) dν(w)`. -/
noncomputable def InfiniteWidthNetwork.eval
    (σ : ℝ → ℝ) {p : ℕ}
    (net : InfiniteWidthNetwork σ p)
    (φ : (Fin p → ℝ) → ℝ) -- feature map from weight space (e.g. w ↦ σ(wᵀx))
    : ℝ :=
  integral net.measure.toJordanDecomposition.posPart φ -
  integral net.measure.toJordanDecomposition.negPart φ

/-- The mass (total variation) of an infinite-width network is
  |ν|(ℝᵖ) = ν₊(ℝᵖ) + ν₋(ℝᵖ).
(Definition 3.2, Telgarsky 2021.) -/
noncomputable def InfiniteWidthNetwork.mass
    (σ : ℝ → ℝ) {p : ℕ}
    (net : InfiniteWidthNetwork σ p) : ℝ :=
  (net.measure.toJordanDecomposition.posPart Set.univ).toReal +
  (net.measure.toJordanDecomposition.negPart Set.univ).toReal

/-! ### Univariate integral representation (Proposition 3.1) -/

/-- The threshold integrand: `b ↦ 1[x ≥ b] · c` for scalar weight c.
This is the "neuron" in the infinite-width threshold representation. -/
noncomputable def thresholdUnit (x b c : ℝ) : ℝ :=
  if x ≥ b then c else 0

/-- The integral representation of a univariate function via threshold units.
  `g(x) = ∫₀¹ 1[x ≥ b] g'(b) db`.
(Proposition 3.1, Telgarsky 2021.) -/
noncomputable def univariateThresholdRep (g' : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ b in Icc (0 : ℝ) 1, thresholdUnit x b (g' b)

/-- **Proposition 3.1** (Telgarsky 2021).
If g : ℝ → ℝ is differentiable on [0, 1] with g(0) = 0, then for all x ∈ [0, 1]:
  `g(x) = ∫₀¹ 1[x ≥ b] * g'(b) db`.

This is an exact infinite-width threshold-network representation of g.
**Proof:** Immediate from the fundamental theorem of calculus:
  g(x) = g(0) + ∫₀ˣ g'(b) db = ∫₀¹ 1[x ≥ b] g'(b) db. -/
-- For x ∈ [0,1], the intersection of Icc 0 1 with Iic x equals Icc 0 x.
-- This set equality bridges the threshold indicator domain with the FTC integration domain.
private lemma Icc_inter_Iic_eq_Icc {x : ℝ} (hx1 : x ≤ 1) :
    Set.Icc (0 : ℝ) 1 ∩ Set.Iic x = Set.Icc (0 : ℝ) x := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, and_congr_left_iff,
    and_iff_left_iff_imp]
  exact fun hyx hy0 => hyx.trans hx1

theorem univariateIntegralRep
    {g : ℝ → ℝ}
    (hg_diff : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (deriv g x) x)
    (hg0 : g 0 = 0)
    (hg'_int : IntervalIntegrable (deriv g) MeasureTheory.volume 0 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    g x = univariateThresholdRep (deriv g) x := by
  simp only [univariateThresholdRep, thresholdUnit]
  have eq1 : (fun b => if x ≥ b then deriv g b else 0) =
      (fun b => (Set.Iic x).indicator (deriv g) b) := by
    ext b; simp only [Set.indicator, Set.mem_Iic, ge_iff_le]
  rw [eq1]
  -- Extract bounds from hx
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ (1 : ℝ) := hx.2
  -- Restrict differentiability hypothesis from [0,1] to [0,x]
  have hderiv_sub : ∀ y ∈ Set.uIcc (0 : ℝ) x, HasDerivAt g (deriv g y) y := by
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    rcases hy with ⟨hy0, hyx⟩
    exact hg_diff y ⟨hy0, hyx.trans hx1⟩
  -- Restrict integrability hypothesis from [0,1] to [0,x]
  have hint_sub : IntervalIntegrable (deriv g) MeasureTheory.volume (0 : ℝ) x := by
    apply hg'_int.mono_set
    rw [Set.uIcc_of_le hx0, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl hx1
  -- Apply the Fundamental Theorem of Calculus (FTC-2) for the Lebesgue integral
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_sub hint_sub
  -- hftc : ∫ y in (0 : ℝ)..x, deriv g y = g x - g 0
  rw [hg0, sub_zero] at hftc
  -- hftc: ∫ y in (0 : ℝ)..x, deriv g y = g x
  rw [intervalIntegral.integral_of_le hx0,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc' (volume_singleton (a := 0))] at hftc
  -- Now hftc: ∫ y in Icc 0 x, deriv g y = g x
  -- Relate Icc 0 x to the indicator integral over Icc 0 1 via Iic x
  calc
    g x = (∫ y in Set.Icc (0 : ℝ) x, deriv g y) := by rw [← hftc]
    _ = (∫ y in Set.Icc (0 : ℝ) 1 ∩ Set.Iic x, deriv g y) := by
      rw [Icc_inter_Iic_eq_Icc hx1]
    _ = (∫ y in Set.Icc (0 : ℝ) 1, (Set.Iic x).indicator (deriv g) y) := by
      rw [← MeasureTheory.setIntegral_indicator measurableSet_Iic]

/-- **Remark** (Remark 3.1): The error from sampling the univariate infinite-width
representation scales with ∫₀¹ |g'(x)| dx (the total variation of g), which is
adaptive and does not pay for flat regions. -/
noncomputable def totalVariationCost (g' : ℝ → ℝ) : ℝ :=
  ∫ b in Icc (0 : ℝ) 1, |g' b|

end Approximation.InfiniteWidth

end
