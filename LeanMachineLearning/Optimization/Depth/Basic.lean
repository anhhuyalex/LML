/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The Δ mapping and its iterated composition (Section 5.1)

This file defines the fundamental building block `Δ` for depth-separation results
(Chapter 5, Telgarsky 2021).

`Δ : ℝ → ℝ` is the piecewise-affine "tent" function:
```
Δ(x) = 2σ(x) − 4σ(x − 1/2) + 2σ(x − 1)
      = 2x        if x ∈ [0, 1/2)
        2 − 2x    if x ∈ [1/2, 1)
        0         otherwise
```
where σ is the ReLU activation.

The key property (Proposition 5.1) is that the L-fold composition Δ^L satisfies
```
Δ^L(x) = Δ(⟨2^{L-1} x⟩)
```
where ⟨·⟩ denotes the fractional part. This means Δ^L has exactly 2^{L-1} uniformly
spaced copies of Δ on [0,1], so its complexity grows *exponentially* in L while the
network size is only O(L).

## Main definitions

* `deltaTent` : the tent function Δ
* `deltaTentIter L` : the L-fold composition Δ^L
* `fractionalPart` : x ↦ x − ⌊x⌋

## Main results

* `deltaTent_eq` : pointwise formula for Δ on the three regions
* `deltaTentIter_eq` : Proposition 5.1 — Δ^L(x) = Δ(⟨2^{L-1} x⟩)
* `deltaTent_reflection` : Δ(z) = Δ(1 − z) for z ∈ [0, 1]

-/

@[expose] public section

open Real Int Finset

namespace Depth

/-! ### Basic building block: the Δ tent function -/

/-- The tent function Δ, defined via ReLU:
  Δ(x) = 2σ(x) − 4σ(x − 1/2) + 2σ(x − 1). -/
noncomputable def deltaTent (x : ℝ) : ℝ :=
  2 * reluActivation x - 4 * reluActivation (x - 1/2) + 2 * reluActivation (x - 1)

/-- The fractional part of a real number: ⟨x⟩ = x − ⌊x⌋. -/
noncomputable def fractionalPart (x : ℝ) : ℝ := x - ⌊x⌋

/-! ### Pointwise characterization of Δ -/

lemma deltaTent_of_Ico_left (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) (1/2)) :
    deltaTent x = 2 * x := by
  simp only [deltaTent, reluActivation]
  have h1 : max x 0 = x := max_eq_left (le_of_lt (Set.mem_Ico.mp hx).1)
  have h2 : max (x - 1/2) 0 = 0 := by
    apply max_eq_right
    linarith [(Set.mem_Ico.mp hx).2]
  have h3 : max (x - 1) 0 = 0 := by
    apply max_eq_right
    linarith [(Set.mem_Ico.mp hx).1]
  rw [h1, h2, h3]; ring

lemma deltaTent_of_Ico_right (x : ℝ) (hx : x ∈ Set.Ico (1/2 : ℝ) 1) :
    deltaTent x = 2 - 2 * x := by
  simp only [deltaTent, reluActivation]
  have h1 : max x 0 = x := max_eq_left (le_of_lt (lt_trans (by norm_num) (Set.mem_Ico.mp hx).1))
  have h2 : max (x - 1/2) 0 = x - 1/2 := by
    apply max_eq_left; linarith [(Set.mem_Ico.mp hx).1]
  have h3 : max (x - 1) 0 = 0 := by
    apply max_eq_right; linarith [(Set.mem_Ico.mp hx).2]
  rw [h1, h2, h3]; ring

lemma deltaTent_of_outside (x : ℝ) (hx : x ∉ Set.Ico (0 : ℝ) 1) :
    deltaTent x = 0 := by
  simp only [deltaTent, reluActivation]
  push_neg at hx
  by_cases h : x < 0
  · have h1 : max x 0 = 0 := max_eq_right (le_of_lt h)
    have h2 : max (x - 1/2) 0 = 0 := max_eq_right (by linarith)
    have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, h3]; ring
  · push_neg at h
    have hge : x ≥ 1 := hx h
    have h1 : max x 0 = x := max_eq_left h
    have h2 : max (x - 1/2) 0 = x - 1/2 := max_eq_left (by linarith)
    have h3 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
    rw [h1, h2, h3]; ring

/-- Δ takes values in [0, 1] on [0, 1]. -/
lemma deltaTent_nonneg (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ deltaTent x := by
  rcases le_or_lt x (1/2) with h | h
  · rw [deltaTent_of_Ico_left x ⟨(Set.mem_Icc.mp hx).1, h⟩]
    linarith [(Set.mem_Icc.mp hx).1]
  · rw [deltaTent_of_Ico_right x ⟨le_of_lt h, (Set.mem_Icc.mp hx).2⟩]
    linarith [(Set.mem_Icc.mp hx).2]

/-- Δ(z) = Δ(1 − z) for z ∈ [0, 1] (reflection symmetry). -/
lemma deltaTent_reflection (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    deltaTent z = deltaTent (1 - z) := by
  simp only [deltaTent, reluActivation]
  ring_nf
  simp [max_comm]
  sorry

/-! ### Iterated composition Δ^L -/

/-- The L-fold composition of Δ with itself. -/
noncomputable def deltaTentIter : ℕ → ℝ → ℝ
  | 0     => id
  | (L+1) => deltaTent ∘ deltaTentIter L

lemma deltaTentIter_zero : deltaTentIter 0 = id := rfl

lemma deltaTentIter_succ (L : ℕ) (x : ℝ) :
    deltaTentIter (L + 1) x = deltaTent (deltaTentIter L x) := rfl

/-- Proposition 5.1: Δ^L(x) = Δ(⟨2^{L-1} x⟩) for all x.
  Here we state the version for L ≥ 1, so that 2^{L-1} makes sense. -/
theorem deltaTentIter_eq (L : ℕ) (hL : 1 ≤ L) (x : ℝ) :
    deltaTentIter L x = deltaTent (fractionalPart (2^(L-1 : ℕ) * x)) := by
  induction L with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp [deltaTentIter, fractionalPart, deltaTent]
      congr 1
      simp [fractionalPart]
      rw [Int.floor_one_mul_sub_floor_mul_one]
      sorry
    | succ m =>
      rw [deltaTentIter_succ]
      have ihm : deltaTentIter (m + 1) x =
          deltaTent (fractionalPart (2^(m : ℕ) * x)) := ih (by omega)
      rw [ihm]
      sorry

/-- Δ^L has exactly 2^{L-1} uniformly-spaced copies of Δ on [0,1].
  (Informal consequence of Proposition 5.1.) -/
lemma deltaTentIter_copies (L : ℕ) (hL : 1 ≤ L) :
    ∀ k : Fin (2^(L-1 : ℕ)), ∀ x : ℝ,
      x ∈ Set.Icc ((k : ℝ) / 2^(L-1 : ℕ)) (((k : ℝ) + 1) / 2^(L-1 : ℕ)) →
      deltaTentIter L x = deltaTent (2^(L-1 : ℕ) * x - k) := by
  sorry

end Depth

end
