/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.PredictionLimits

/-!
# Training limits of the two-layer network: global positive-gap theorem

The global lazy-training theorem under a positive limiting spectral gap `λ_min(K_∞) > 0`:
uniform-in-time kernel control and exponential residual and loss decay with high probability.

See `LeanMachineLearning.Optimization.NTK.Training.TwoLayer` for the overview of the whole
development.
-/

namespace NTK

open ConvexOpt MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

@[expose] public section

section GlobalPositiveGapLimit

/-!
#### Target Theorem 2: Global Positive-Gap Lazy Training Limit (Phase 0 Target)

**Status.** Proved as `global_positive_gap_lazy_training_limit` (any family solving the ODE almost
everywhere) and `gradientFlow_global_positive_gap_lazy_training_limit` (the constructed family),
with
the following differences from the original target below: the uniform finite-width gap is
`lambda_inf / 4` rather than `lambda_inf / 2` (initialization transfers a half-gap and the bootstrap
halves it again; the quarter-gap suffices), the drift rate is `O(√(log n / n))` in
`global_positive_gap_lazy_training_limit` (the logarithm comes from the maximum readout weight) and
`O(n⁻¹ᐟ²)` in `global_positive_gap_lazy_training_limit_inv_sqrt_width` (average moments), the
residual and loss decay rates are `lambda_inf / (4 m)` and `lambda_inf / (2 m)`, and the event is a
measurable initialization event of probability `≥ 1 - η`. The commented signature below is kept as
the original target.

**Statement**:
Under the same hypotheses as Theorem 1, assume in addition that the limiting
kernel `limitingFullNTKMatrix φ X`
satisfies a strictly positive spectral gap:
  `λ_min(limitingFullNTKMatrix φ X) = lambda_inf > 0`.

Then for any fixed confidence `δ ∈ (0, 1)`, there exist `N : ℕ` and `C > 0` such that for all
`n ≥ N`, with probability at least `1 - δ` under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`:
1. **Uniform Spectral Gap**: For all `t ≥ 0`, `λ_min(K_n(t)) ≥ lambda_inf / 2`.
2. **Uniform Kernel Freeze**: For all `t ≥ 0`:
   `‖K_n(t) - K_n(0)‖ ≤ C * √(log n / n)` in the Frobenius norm.
3. **Exponential Residual Decay**: For all `t ≥ 0`:
   `‖r_n(t)‖ ≤ ‖r_n(0)‖ * exp(-(lambda_inf / (2 * m)) * t)`.
4. **Exponential Loss Decay**: For all `t ≥ 0`:
   `mseLoss f_n X y (θ_traj t) ≤ mseLoss f_n X y (θ_traj 0) * exp(-(lambda_inf / m) * t)`.
5. **Infinite-Time Convergence**:
   `lim_{t → ∞} mseLoss f_n X y (θ_traj t) = 0`.

A polynomial rate `1 - O(n^{-c})` may be derived as a corollary after quantitative
concentration estimates are established in Phase 3.5 or commit step 5.

**Frobenius Matrix Norm**:
The matrix norm `‖·‖` on `Matrix (Fin m) (Fin m) ℝ` throughout this target specification is the
Frobenius norm (`Matrix.Norms.Frobenius`), which dominates entrywise differences via
`|A i j| ≤ ‖A‖`.

**Uniform-Time Event Measurability**:
By path continuity of the gradient flow trajectory `t ↦ θ n p t` and continuity of the
matrix operations, residual, and MSE loss, each uniform-over-time condition `∀ t ≥ 0, ...`
is equivalent to the countable intersection over non-negative rationals `t ∈ ℚ, 0 ≤ t`.
Because each fixed-time evaluation is measurable from trajectory measurability (`hθ_meas`),
the uniform-time intersection event is measurable under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`.

**Commented Formal Lean Signature**:
```lean
/-
theorem global_positive_gap_lazy_training_limit
    {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hderiv_lip : ∃ L_φ' : ℝ, 0 ≤ L_φ' ∧ LipschitzWith (Real.toNNReal L_φ') (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : Matrix.PosSemidef (limitingFullNTKMatrix φ X - lambda_inf • 1))
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∃ (N : ℕ) (C : ℝ), 0 < C ∧ ∀ n ≥ N,
      (𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)) {p |
        (∀ t ≥ 0, Matrix.PosSemidef
          (empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) - (lambda_inf / 2) • 1)) ∧
        (∀ t ≥ 0,
          ‖empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
            empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖ ≤
            C * Real.sqrt (Real.log n / n)) ∧
        (∀ t ≥ 0,
          ‖trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
            ‖trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)‖ *
              Real.exp (- (lambda_inf / (2 * m)) * t)) ∧
        (∀ t ≥ 0,
          mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t) ≤
            mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
              (θ n p 0) * Real.exp (- (lambda_inf / (m : ℝ)) * t))} ≥
        ENNReal.ofReal (1 - δ)
-/
```
-/

end GlobalPositiveGapLimit

end

end NTK
