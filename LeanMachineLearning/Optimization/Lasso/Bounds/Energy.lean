/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Definitions
public import LeanMachineLearning.Optimization.Lasso.Bounds.Delta

/-!
# Energy bounds for positive Lasso dynamics

This file develops the differential and integral energy estimates used to control the positive
Lasso trajectory.
-/

@[expose] public section

namespace Lasso

open Filter Topology
variable {ι : Type*} [Fintype ι]
set_option linter.unusedFintypeInType false

/--
Helper lemma for `positive_energy_differential_inequality`.
Bounds the first term of the product rule derivative.

Informal proof reference: `docs/Lasso.md`, Section 4.6 (text after Eq. (4.15)).
The derivative of `(1 / (1 + τ * lambda)) • w τ` is bounded in norm by `‖r‖_M†`
according to Lemma 4.11 (`ParametricLCPDualRegular`). By Cauchy-Schwarz, its inner
product with `zε τ - z τ` is bounded by `‖r‖_M† * sqrt(2 * Δᵋ(τ))`.
-/
lemma dual_path_derivative_inner_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (w z zε : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w) (τ : ℝ) :
    inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ) (zε τ - z τ)
    ≤ pseudoInverseSeminorm Mdagger r * Real.sqrt (2 * pathDelta M zε z τ) := by
  sorry

/--
Helper lemma for `positive_energy_differential_inequality`.
Shows that the algebraic sum of the remaining product rule terms is exactly bounded by
the complementarity bound from `positive_delta_differential_inequality`.
We also assert that `C` is at least `‖r‖_M†` so that it can bound both parts simultaneously.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.14) and Eq. (789).
The product rule on `Eᵋ(τ)/(1+τ*λ)` yields terms involving `w(τ)` and `(zε - z)'`, and
the derivative of `Δᵋ(τ)`. Their sum algebraically simplifies to exactly the first four
complementarity defect terms analyzed in Eq. (4.14). These defect terms are uniformly
bounded by `C * [ 1/log(1/ε) * (1 + (z↑)') + (z↓)' ]` as established by the global bound
in `positive_delta_differential_inequality`.
-/
lemma energy_complementarity_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, pseudoInverseSeminorm Mdagger r ≤ C ∧ ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        deriv
          (fun σ =>
            (1 / (1 + σ * lambda)) *
              (inner ℝ (w σ)
                  (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
                pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
                  (scaledPrimalPath x_lasso) σ)) τ -
        inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
          (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)
        ≤ C *
          (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  sorry

/--
Section 4.6 energy differential inequality for
`Eᵋ(s)=<w(s),zᵋ(s)-z(s)>+Δᵋ(s)`.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (806).
The derivative of the scaled energy expands by the product rule. The first term is
controlled by the dual-path derivative bound from Lemma 4.11 and the Cauchy-Schwarz
inequality (yielding `‖r‖_M† * ‖zᵋ(s) - z(s)‖_M = ‖r‖_M† * sqrt(2 * Δᵋ(s))`).
The remaining terms precisely match the complementarity defects analyzed in Eq. (4.14),
which are bounded globally by `positive_delta_differential_inequality`.
Summing these bounds gives the final total differential inequality.
-/
theorem positive_energy_differential_inequality
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        deriv
          (fun σ =>
            (1 / (1 + σ * lambda)) *
              (inner ℝ (w σ)
                  (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
                pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
                  (scaledPrimalPath x_lasso) σ)) τ
        ≤ C *
          (Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) τ) +
            1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  obtain ⟨C, hC_pos, hC_ge, h_bound⟩ := energy_complementarity_bound M Mdagger r lambda β s hs u
    hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_regular
  use C, hC_pos
  intro δ hδ
  filter_upwards [h_bound δ hδ] with ε hε τ hτ
  have h_comp := hε τ hτ
  have h_dual := dual_path_derivative_inner_bound M Mdagger r lambda w
    (scaledPrimalPath x_lasso) (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) hdual τ
  let Δ := pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    (scaledPrimalPath x_lasso) τ
  have h_sqrt_nonneg := Real.sqrt_nonneg (2 * Δ)
  have h_dual' : inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
      (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)
      ≤ C * Real.sqrt (2 * Δ) := by
    calc
      inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
        (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)
      ≤ pseudoInverseSeminorm Mdagger r * Real.sqrt (2 * Δ) := h_dual
      _ ≤ C * Real.sqrt (2 * Δ) := mul_le_mul_of_nonneg_right hC_ge h_sqrt_nonneg
  have h_sum := add_le_add h_dual' h_comp
  calc
    deriv
      (fun σ =>
        (1 / (1 + σ * lambda)) *
          (inner ℝ (w σ)
              (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
            pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ)) τ
    = inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
        (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ) +
      (deriv
        (fun σ =>
          (1 / (1 + σ * lambda)) *
            (inner ℝ (w σ)
                (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
              pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
                (scaledPrimalPath x_lasso) σ)) τ -
        inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
          (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)) := by ring
    _ ≤ C * Real.sqrt (2 * Δ) +
        (C * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
          deriv (positiveZDownward x_lasso) τ) + δ) := h_sum
    _ = C * (Real.sqrt (2 * Δ) +
          1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
          deriv (positiveZDownward x_lasso) τ) + δ := by ring

/--
Helper lemma: The initial positive energy $E^\varepsilon(0)$ is exactly zero.

Informal proof:
The energy is defined as $E^\varepsilon(s) =
\langle w(s), z^\varepsilon(s) - z(s) \rangle + \Delta^\varepsilon(s)$.
At $s=0$, the scaled trajectory $z^\varepsilon(0)$ is $0$ because the unscaled trajectory
$u^\varepsilon(t)$ has initial condition $u^\varepsilon(0) = \sqrt{\varepsilon}\alpha$,
which means $x^\varepsilon(0) = \varepsilon \alpha^2$.
When integrating $x^\varepsilon$ from $0$ to $0$, we get $0$. Thus $z^\varepsilon(0) = 0$.
Similarly, the lasso minimizer at $\mu=0$ is $x(0) = 0$, so $z(0) = 0$.
Since $z^\varepsilon(0) - z(0) = 0$, both the inner product and the $\Delta$ term
(which is $\frac{1}{2}\|0\|_M^2$) vanish.
Therefore, $E^\varepsilon(0) = 0$.
-/
lemma initial_positive_energy_zero
    (M : Matrix ι ι ℝ) (ε : ℝ) (u : ℝ → EuclideanSpace ℝ ι)
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (w : ℝ → EuclideanSpace ℝ ι) :
    inner ℝ (w 0) (posIntegratedTrajectoryRescaled ε u 0 - scaledPrimalPath x_lasso 0) +
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε u ρ)
        (scaledPrimalPath x_lasso) 0 = 0 := by
  sorry

/--
Helper lemma: The positive lasso objective gap is exactly $1/s^2$ times
the energy $E^\varepsilon(s)$.

Informal proof reference: `docs/Lasso.md`, Eq. (782).
By the second-order Taylor expansion of the quadratic function $g_s(x) = \operatorname{Lasso}(x, s)$
over the non-negative orthant (where $\|x\|_1 = \langle \mathbb{1}, x \rangle$), we have:
$g_s(x) - g_s(y) = \langle \nabla g_s(y), x - y \rangle + \frac{1}{2}\|x - y\|_M^2$.
At the minimizer $y = x(s) = z(s)/s$, the gradient is $\nabla g_s(x(s)) = v(s) = w(s)/s$.
Substituting $x = \bar{x}^\varepsilon(s) = z^\varepsilon(s)/s$, the objective difference becomes:
$\frac{1}{s^2} \left[ \langle w(s), z^\varepsilon(s) - z(s) \rangle +
  \frac{1}{2}\|z^\varepsilon(s) - z(s)\|_M^2 \right]$,
which is exactly $\frac{1}{s^2} E^\varepsilon(s)$.
To formally prove this in Lean, apply `positiveLassoObjective_eq` to both $x$ and $y$,
subtract them, and use `quadratic_expansion` from `LCP.lean` to group the quadratic forms.
-/
lemma positiveLassoObjective_eq_energy
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (s : ℝ) (hs : 0 < s)
    (z zε : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ ι)
    (hx_nonneg : Nonnegative (s⁻¹ • z)) (hxE_nonneg : Nonnegative (s⁻¹ • zε))
    (hw_eq : matVec M (s⁻¹ • z) + lcpQ r lambda s = s⁻¹ • w)
    (hM_symm : M.IsSymm) :
    positiveLassoObjective M r lambda s (s⁻¹ • zε) - positiveLassoObjective M r lambda s (s⁻¹ • z) =
      s⁻¹ ^ 2 * (inner ℝ w (zε - z) + (1 / 2 : ℝ) * inner ℝ (zε - z) (matVec M (zε - z))) := by
  sorry

end Lasso
