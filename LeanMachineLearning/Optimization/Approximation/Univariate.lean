/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Univariate Lipschitz approximation (folklore construction)

This file formalizes Proposition 2.1 from the deep learning theory notes:
a ρ-Lipschitz function on [0,1] can be approximated to accuracy ε by a
single-hidden-layer threshold network with ⌈ρ/ε⌉ nodes.

## Main results

* `stepApprox` : the step-function approximant constructed from breakpoints bᵢ = iε/ρ
* `stepApprox_mem_FunctionClass` : the approximant lies in OneHiddenLayer.FunctionClass
* `stepApprox_error` : sup-norm error bound ≤ ε on [0,1]

-/

@[expose] public section

open Real Finset

namespace Approximation.Univariate

variable {g : ℝ → ℝ} {ρ ε : ℝ}

/-! ### Breakpoints and coefficients -/

/-- Number of steps: m = ⌈ρ/ε⌉. -/
noncomputable def numSteps (ρ ε : ℝ) : ℕ := ⌈ρ / ε⌉₊

/-- Breakpoints bᵢ = iε/ρ for i = 0, ..., m-1. -/
noncomputable def breakpoint (ρ ε : ℝ) (i : ℕ) : ℝ := i * ε / ρ

/-- Coefficients: a₀ = g(0), aᵢ = g(bᵢ) - g(bᵢ₋₁) for i ≥ 1. -/
noncomputable def coeff (g : ℝ → ℝ) (ρ ε : ℝ) : ℕ → ℝ
  | 0     => g 0
  | (i+1) => g (breakpoint ρ ε (i+1)) - g (breakpoint ρ ε i)

/-! ### The step-function approximant -/

/-- The step-function approximant:
  f_ε(x) = ∑_{i=0}^{m-1} aᵢ · 1[x ≥ bᵢ] -/
noncomputable def stepApprox (g : ℝ → ℝ) (ρ ε : ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ range (numSteps ρ ε),
    coeff g ρ ε i * thresholdActivation (x - breakpoint ρ ε i)

/-- The step-function approximant lies in the threshold network function class. -/
theorem stepApprox_mem_FunctionClass (_hρ : 0 < ρ) (_hε : 0 < ε) :
    (fun (x : Fin 1 → ℝ)
      => stepApprox g ρ ε (x 0)) ∈
        OneHiddenLayer.FunctionClass thresholdActivation 1 (numSteps ρ ε) := by
  simp only [OneHiddenLayer.FunctionClass, Set.mem_setOf_eq]
  let net : OneHiddenLayer.Network thresholdActivation 1 (numSteps ρ ε) :=
    { weights := fun i _ => 1
      biases  := fun i => -(breakpoint ρ ε i.val)
      coeffs  := fun i => coeff g ρ ε i.val }
  exact ⟨net, by
    ext x
    simp only [OneHiddenLayer.Network.eval, stepApprox, thresholdActivation]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [net]
    have eq_sum : (∑ j : Fin 1, (1 : ℝ) * x j) = x 0 := by
      rw [Fin.sum_univ_one]
      ring
    rw [eq_sum]
    congr 2
  ⟩

/-! ### Error bound -/

/-- Telescoping: ∑_{i=0}^k aᵢ = g(b_k). -/
lemma sum_coeff_eq (g : ℝ → ℝ) (ρ ε : ℝ) (k : ℕ) :
    ∑ i ∈ range (k + 1), coeff g ρ ε i = g (breakpoint ρ ε k) := by
  induction k with
  | zero => simp [coeff, breakpoint]
  | succ k ih =>
    rw [sum_range_succ, ih, coeff]
    ring

/-- Main approximation error bound: sup_{x ∈ [0,1]} |f_ε(x) - g(x)| ≤ ε. -/
theorem stepApprox_error (hg : LipschitzWith ρ.toNNReal g) (hρ : 0 < ρ) (hε : 0 < ε)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |stepApprox g ρ ε x - g x| ≤ ε := by
  sorry

end Approximation.Univariate

end
