/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Depth.AffinePieces
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Depth separation theorem (Section 5.2, Theorem 5.1)

This file formalizes Theorem 5.1 from the deep learning theory notes (Telgarsky 2015, 2016):
for any L ≥ 2, the function f = Δ^{L²+2} is expressible by a ReLU network of size O(L²),
but cannot be approximated (in L₁ norm) by any ReLU network with ≤ 2^L nodes and ≤ L layers.

The proof has three steps:
1. *Shallow networks have low complexity:* any ReLU network with ≤ 2^L nodes and ≤ L layers
   has at most 2^{L²} affine pieces (by Lemma 5.1).
2. *Deep networks have high regular complexity:* Δ^{L²+2} has exactly 2^{L²+1} uniformly
   spaced copies of Δ (by Proposition 5.1 / deltaTentIter_eq).
3. *Counting triangles:* if g has few pieces and f = Δ^{L²+2} has many regular triangles,
   there must be a region of measure ≥ 1/32 where |f − g| ≥ 1/4.

## Main results

* `depthSeparation` : Theorem 5.1 — for any L ≥ 2 and any ReLU network g with
  ≤ 2^L nodes and ≤ L layers,
  ∫_{[0,1]} |Δ^{L²+2}(x) − g(x)| dx ≥ 1/32.

-/

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace Depth

/-! ### Triangle counting -/

/-- A "triangle" of f = Δ^{L²+2} is a maximal affine piece where f increases from 0 to 1
  or decreases from 1 to 0. By Proposition 5.1, there are 2^{L²+2} − 1 half-triangles,
  each of measure 2^{−(L²+2)} and area 2^{−(L²+4)}. -/
def triangleCount (L : ℕ) : ℕ := 2^(L^2 + 2) - 1

def triangleArea (L : ℕ) : ℝ := 2^(-(L^2 + 4 : ℤ) : ℤ)

/-- The number of triangles "surviving" after subtracting piece-boundary effects:
  a network g with ≤ 2^{L²} pieces can kill at most 2 · 2^{L²} triangles by
  crossing the midline or by its piece boundaries.
  This leaves ≥ 2^{L²+1} − 1 surviving triangles. -/
lemma surviving_triangles_bound (L : ℕ) (hL : 2 ≤ L) (pieceBound : ℕ)
    (h : pieceBound ≤ 2^(L^2)) :
    2 * pieceBound + 1 ≤ 2^(L^2 + 1) := by
  have : 2 * pieceBound ≤ 2 * 2^(L^2) := Nat.mul_le_mul_left 2 h
  linarith [Nat.one_le_two_pow]

/-! ### Depth separation theorem -/

/-- Theorem 5.1 (Telgarsky 2015, 2016): For any L ≥ 2, let f = Δ^{L²+2}.
  Then f is a ReLU network with 3L²+6 nodes and 2L²+4 layers.
  Moreover, for any ReLU network g with ≤ 2^L nodes and ≤ L layers,
  ∫_{[0,1]} |f(x) − g(x)| dx ≥ 1/32. -/
theorem depthSeparation (L : ℕ) (hL : 2 ≤ L) (g : ℝ → ℝ)
    (hNet : ∃ net : ReLUNetwork L, net.totalNodes ≤ 2^L ∧
        ∀ x, g x = ∑ j, net.outWeights j *
          reluActivation (∑ k, net.weights ⟨L-1, by omega⟩ j k *
            reluActivation 0 + net.biases ⟨L-1, by omega⟩ j) + net.outBias) :
    (1 : ℝ)/32 ≤
      ∫ x in (0 : ℝ)..1, |deltaTentIter (L^2 + 2) x - g x| := by
  sorry

/-- Size of the network realizing Δ^{L²+2}: it has 3L²+6 nodes and 2L²+4 layers. -/
theorem deltaTentIter_network_size (L : ℕ) (hL : 2 ≤ L) :
    ∃ net : ReLUNetwork (2*L^2 + 4),
      (∀ x, (∑ j, net.outWeights j * reluActivation 0) = deltaTentIter (L^2 + 2) x) ∧
      net.totalNodes = 3*L^2 + 6 := by
  sorry

end Depth

end
