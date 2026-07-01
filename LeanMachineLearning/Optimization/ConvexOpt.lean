/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.ConvexOpt.Basic
public import LeanMachineLearning.Optimization.ConvexOpt.StationaryPoints
public import LeanMachineLearning.Optimization.ConvexOpt.ConvexConvergence
public import LeanMachineLearning.Optimization.ConvexOpt.StrongConvexity
public import LeanMachineLearning.Optimization.ConvexOpt.StochasticGradient

/-!
# Semi-classical convex optimization (Chapters 6–7)

Re-exports the full optimization library corresponding to Chapters 6–7 of the deep
learning theory notes (Telgarsky 2021).

## Overview

The central theme is proving convergence rates for first-order methods
(gradient descent and gradient flow) on structured objectives.
Our presentation avoids assuming the existence of a minimizer by using an
arbitrary **reference point** `z` in place of `argmin f` — this generality
is essential for later chapters on margin maximization.

## Structure

* `ConvexOpt.Basic` — core definitions and the quadratic upper bound from smoothness.
* `ConvexOpt.StationaryPoints` — convergence to stationary points (smooth objectives).
* `ConvexOpt.ConvexConvergence` — smooth+convex rates with reference point.
* `ConvexOpt.StrongConvexity` — exponential rates under strong convexity.
* `ConvexOpt.StochasticGradient` — stochastic gradient analysis and Azuma–Hoeffding.

## Main results

| Name | Statement |
|------|-----------|
| `ConvexOpt.smooth_upper_bound` | `f(v) ≤ f(w) + ⟪∇f(w), v-w⟫ + β/2·‖v-w‖²` |
| `ConvexOpt.gd_descent_step` | `f(w') ≤ f(w) - 1/(2β)·‖∇f(w)‖²` with η = 1/β |
| `ConvexOpt.gd_stationary_convergence` | `min_{i<t} ‖∇f(wᵢ)‖² ≤ 2β/t·(f(w₀)-inf f)` |
| `ConvexOpt.gf_stationary_convergence` | `inf_{s∈[0,t]} ‖∇f(w(s))‖² ≤ (f(w(0))-f(w(t)))/t` |
| `ConvexOpt.gd_convex_convergence` | `f(wₜ)-f(z) ≤ β‖w₀-z‖²/(2t)` (smooth+convex) |
| `ConvexOpt.gf_convex_convergence` | `f(w(t))-f(z) ≤ ‖w(0)-z‖²/(2t)` (convex) |
| `ConvexOpt.gd_strongly_convex_convergence` | `‖wₜ-w*‖² ≤ (1-λ/β)ᵗ·‖w₀-w*‖²` |
| `ConvexOpt.gf_strongly_convex_convergence` | `‖w(t)-w*‖² ≤ ‖w(0)-w*‖²·exp(-2λt)` |
| `ConvexOpt.gd_strongly_convex_ref` | `f(wₜ)-f(z)+λ/2·‖wₜ-z‖² ≤ ((β-λ)/(β+λ))ᵗ·(…)` |
| `ConvexOpt.approxGD_convergence` | Lemma 7.2: averaged SGD bound with noise term |
| `ConvexOpt.azuma_hoeffding` | Theorem 7.8: Azuma–Hoeffding inequality |
| `ConvexOpt.sgd_high_prob_convergence` | Lemma 7.3: SGD high-probability bound |

## Proposed refactors to existing infrastructure

1. **`NTK.BetaSmooth` → `ConvexOpt.BetaSmooth`** (unification):
   `NTK/Linearization.lean` defines `NTK.BetaSmooth σ β` as `|σ''| ≤ β` for a scalar
   activation.  This should be viewed as the specialization of `ConvexOpt.BetaSmooth`
   to the case `E = ℝ`.  Concretely, `ConvexOpt.BetaSmooth` (Lipschitz gradient)
   implies `NTK.BetaSmooth` for `σ : ℝ → ℝ` differentiable: the scalar gradient is
   `σ'`, and `LipschitzWith β σ'` is exactly `|σ'(w) - σ'(v)| ≤ β|w - v|`.
   **Refactor:** replace `NTK.BetaSmooth` with a `@[simp]` corollary of
   `ConvexOpt.BetaSmooth`, specializing `E := ℝ`.

2. **`NTK.frobeniusInner` / `NTK.frobeniusNorm` → Mathlib `Matrix` norms**:
   These are currently defined from scratch in `NTK/Basic.lean`.  Mathlib provides
   `Matrix.inner` and `‖·‖` (via `PiLp 2`) on matrix spaces.  Switching to Mathlib
   representations would allow the Jacobian Lipschitz bound
   `‖J_w - J_v‖ ≤ β‖w - v‖`
   (used in Theorem 8.1) to be a special case of `ConvexOpt.BetaSmooth` applied to
   the Jacobian map `w ↦ J_w`.

3. **Gradient flow ODE interface**:
   `ConvexOpt.GFTrajectory` uses `HasDerivAt`.  In the NTK optimization proof
   (Theorem 8.1), the gradient flow `ẇ(t) = -α Jₜᵀ ∇R(αf(w(t)))` is a
   time-varying ODE.  This could be abstracted as a `VaryingGFTrajectory` predicate
   that takes the vector field as a parameter, making the NTK analysis a special case.

4. **`IsStochasticGradient` ↔ `SequentialLearning.Algorithm`**:
   The `SequentialLearning` module models stochastic interaction via Markov kernels
   (Ionescu–Tulcea).  An SGD run can be viewed as a `Learning.Algorithm` with
   action space `E` and observation space `E × ℝ` (returning gradient + loss).
   Future work: provide a `toAlgorithm` function converting an `IsStochasticGradient`
   into a `Learning.Algorithm`, enabling reuse of the concentration machinery
   (Azuma–Hoeffding is already implicit in the bandit regret analysis).

-/
