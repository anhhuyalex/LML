/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Depth.Basic
public import LeanMachineLearning.Optimization.Depth.AffinePieces
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Approximation of x² by deep ReLU networks (Section 5.3, Theorem 5.2)

This file formalizes Theorem 5.2 (roughly following Yarotsky 2016), which shows that
x² can be approximated on [0,1] by a deep ReLU network of logarithmic size.

## Construction

Define the grid Sᵢ := {0, 1/2^i, 2/2^i, …, 1} and let hᵢ be the piecewise-linear
interpolation of x² on Sᵢ. The key recursion is:
```
hᵢ₊₁ = hᵢ − Δ^{i+1} / 4^{i+1}
```
with h₀(x) = x (the zero-th interpolation of x²).

Therefore:
```
hᵢ(x) = x − ∑_{j=1}^{i} Δʲ(x) / 4ʲ
```

This gives:
* **Upper bound:** sup_{x ∈ [0,1]} |hᵢ(x) − x²| ≤ 4^{−i−1}
* **Network size:** hᵢ can be realized with 2i layers and 4i nodes
  (or 3i nodes with skip connections)
* **Lower bound (part 4):** any L-layer, N-node network satisfies
  ∫_{[0,1]} (f(x) − x²)² dx ≥ 1 / (5760 · (2N/L)^{4L})

## Main definitions

* `squareInterpGrid i` : the grid Sᵢ = {k/2^i | k = 0, …, 2^i}
* `squareInterp i` : the piecewise-linear interpolation hᵢ of x² on Sᵢ

## Main results

* `squareInterp_recursion` : hᵢ₊₁ = hᵢ − Δ^{i+1} / 4^{i+1}
* `squareInterp_formula` : hᵢ(x) = x − ∑_{j=1}^{i} Δʲ(x) / 4ʲ
* `squareInterp_error` : sup-norm error |hᵢ(x) − x²| ≤ 4^{−i−1}
* `squareInterp_network_size` : hᵢ is a ReLU network with 2i layers, 4i nodes
* `squareApprox_lower_bound` : L₂ lower bound for any shallow ReLU approximant

-/

@[expose] public section

open Real Finset MeasureTheory intervalIntegral Approximation

namespace Depth

/-! ### Piecewise-linear interpolation grid -/

/-- The grid Sᵢ = {k/2^i | k = 0, …, 2^i} of 2^i+1 equally spaced points in [0,1]. -/
noncomputable def squareInterpGrid (i : ℕ) : Finset ℝ :=
  Finset.image (fun (k : ℕ) => (k : ℝ) / (2^i : ℝ)) (Finset.range (2^i + 1))

/-- The piecewise-linear interpolation of x² on Sᵢ.
  hᵢ(x) = x − ∑_{j=1}^{i} Δʲ(x)/4ʲ, with h₀(x) = x. -/
noncomputable def squareInterp (i : ℕ) (x : ℝ) : ℝ :=
  x - ∑ j ∈ range i, deltaTentIter (j + 1) x / 4^(j + 1)

/-! ### Recursion and formula -/

/-- The zero-th interpolation is the identity: h₀(x) = x. -/
@[simp]
lemma squareInterp_zero (x : ℝ) : squareInterp 0 x = x := by
  simp [squareInterp]

/-- Key recursion: hᵢ₊₁(x) = hᵢ(x) − Δ^{i+1}(x) / 4^{i+1}. -/
theorem squareInterp_recursion (i : ℕ) (x : ℝ) :
    squareInterp (i + 1) x = squareInterp i x - deltaTentIter (i + 1) x / 4^(i + 1) := by
  simp [squareInterp, sum_range_succ]
  ring

/-- On grid points, hᵢ interpolates x²: hᵢ(k/2^i) = (k/2^i)². -/
theorem squareInterp_on_grid (i k : ℕ) (hk : k ≤ 2 ^ i) :
    squareInterp i ((k : ℝ) / 2^i) = ((k : ℝ) / 2^i)^2 := by
  sorry

/-- The refinement hᵢ₊₁ agrees with hᵢ on the coarser grid Sᵢ. -/
theorem squareInterp_agrees_on_coarser (i k : ℕ) (hk : k ≤ 2 ^ i) :
    squareInterp (i + 1) ((k : ℝ) / 2^i) = squareInterp i ((k : ℝ) / 2^i) := by
  have hk' : 2 * k ≤ 2^(i+1) := by
    calc
      2 * k ≤ 2 * (2^i) := Nat.mul_le_mul_left 2 hk
      _ = 2^(i+1) := by simp [pow_succ, mul_comm]
  have h_arg_eq : ((k : ℝ) / 2^i) = (((2 * k : ℕ) : ℝ) / 2^(i+1)) := by
    push_cast
    ring
  calc
    squareInterp (i + 1) ((k : ℝ) / 2^i)
        = squareInterp (i + 1) (((2 * k : ℕ) : ℝ) / 2^(i+1)) := by rw [h_arg_eq]
    _ = (((2 * k : ℕ) : ℝ) / 2^(i+1))^2 := by rw [squareInterp_on_grid (i + 1) (2 * k) hk']
    _ = ((k : ℝ) / 2^i)^2 := by
      push_cast
      ring
    _ = squareInterp i ((k : ℝ) / 2^i) := by rw [squareInterp_on_grid i k hk]

/-- The mid-point correction is constant: hᵢ((2k+1)/2^{i+1}) − hᵢ₊₁((2k+1)/2^{i+1}) = 1/4^{i+1}. -/
theorem squareInterp_midpoint_diff (i k : ℕ) (hk : k < 2 ^ i) :
    let x := ((2*k + 1 : ℕ) : ℝ) / 2^(i+1)
    squareInterp i x - squareInterp (i + 1) x = 1 / 4^(i + 1) := by
  sorry

/-! ### Error bounds (Theorem 5.2, parts 2 and 3) -/

/-- Theorem 5.2(3): The sup-norm error of hᵢ approximating x² is at most 4^{−i−1}. -/
theorem squareInterp_error (i : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |squareInterp i x - x^2| ≤ 4^(-(i + 1 : ℤ)) := by
  sorry

/-- Corollary: given error ε > 0, choosing i = ⌈log₄(1/ε)⌉ gives |hᵢ(x) − x²| ≤ ε. -/
theorem squareInterp_approx (ε : ℝ) (hε : 0 < ε) :
    let i := ⌈Real.log (1/ε) / Real.log 4⌉₊
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |squareInterp i x - x^2| ≤ ε := by
  sorry

/-! ### Network size (Theorem 5.2, part 2) -/

/-- Theorem 5.2(2): hᵢ is realized by a pure ReLU network with 2i layers and 4i nodes.
  (With skip connections, only 3i nodes are needed.) -/
theorem squareInterp_network_size (i : ℕ) :
    ∃ net : ReLUNetwork (2 * i),
      net.totalNodes ≤ 4 * i ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (∑ j, net.outWeights j * reluActivation 0) = squareInterp i x := by
  sorry

/-! ### Lower bound (Theorem 5.2, part 4) -/

/-- Minimum L₂ error of a linear function on an interval [a,b].
  ∫_{[a,b]} (x² − (cx+d))² dx is minimized over (c,d) to (b−a)⁵/180. -/
theorem minL2Error_affine_on_interval (a b : ℝ) (hab : a < b) :
    ∀ c d : ℝ, (b - a)^5 / 180 ≤ ∫ x in a..b, (x^2 - (c*x + d))^2 := by
  sorry

/-- Theorem 5.2(4): Any L-layer, N-node ReLU network f satisfies
  ∫_{[0,1]} (f(x) − x²)² dx ≥ 1 / (5760 · (2N/L)^{4L}). -/
theorem squareApprox_lower_bound {L : ℕ} (hL : 0 < L) (net : ReLUNetwork L) (f : ℝ → ℝ) :
    1 / (5760 * (2 * net.totalNodes / L)^(4*L)) ≤
      ∫ x in (0 : ℝ)..1, (f x - x^2)^2 := by
  sorry

end Depth

end
