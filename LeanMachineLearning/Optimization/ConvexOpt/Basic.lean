/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Core definitions for semi-classical convex optimization (Chapter 7)

This file defines the fundamental objects for the convergence analysis of gradient
descent and gradient flow in Chapters 6–7 of the deep learning theory notes
(Telgarsky 2021).

We work in an abstract inner product space `E` over `ℝ`, which includes `EuclideanSpace ℝ (Fin d)`
as the canonical finite-dimensional instance.

## Main definitions

* `ConvexOpt.BetaSmooth f β` : the gradient of `f` is `β`-Lipschitz (Definition 7.1).
* `ConvexOpt.smooth_upper_bound` : the quadratic upper bound implied by smoothness (Lemma 7.1).
* `ConvexOpt.gd_descent_step` : one step of gradient descent decreases `f` (Lemma 7.2).
* `ConvexOpt.gdIterate` : the gradient descent iterate sequence (Definition 6.1).
* `ConvexOpt.GFTrajectory` : predicate for gradient flow solutions (Definition 6.2).
* `ConvexOpt.hasDerivAt_comp_of_neg_gradient`,
  `ConvexOpt.ForwardGFTrajectory.integral_norm_sq_gradient_eq_sub`,
  `ConvexOpt.ForwardGFTrajectory.integral_norm_deriv_sq_eq_sub` : the energy identity
  `(f ∘ w)' = -‖∇f(w)‖² = -‖w'‖²` along gradient flow and its integrated (kinetic energy) form.
* `ConvexOpt.IsConvex f` : first-order characterization of convexity (Definition 7.3).
* `ConvexOpt.IsStronglyConvex f c` : first-order characterization of strong convexity (Def. 7.5).
* `ConvexOpt.approxGDIterate` : generalized GD with approximate gradients (Definition 7.7).
* `ConvexOpt.IsStochasticGradient` : unbiased stochastic gradient oracle (Definition 7.8).

## Proposed refactors to existing code

The existing `NTK/Linearization.lean` defines `NTK.BetaSmooth` for scalar
functions `σ : ℝ → ℝ` (measuring `|σ''| ≤ β`).  The present definition unifies
smoothness as a Lipschitz condition on the gradient, which subsumes the scalar
case via `‖∇σ(w) - ∇σ(v)‖ = |σ'(w) - σ'(v)|`.

Future work: replace `NTK.frobeniusInner` / `NTK.frobeniusNorm` with
Mathlib's `inner` and `‖·‖` on `Matrix`-typed spaces, so that
the Jacobian smoothness bound `‖J_w - J_v‖ ≤ β‖w - v‖` becomes a special case
of `BetaSmooth` applied to the map `w ↦ J_w`.

-/

@[expose] public section

open Real MeasureTheory Filter

namespace ConvexOpt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### β-smooth functions (Definition 7.1) -/

/-- **Definition 7.1** (Telgarsky 2021, §7.1).
A differentiable function `f : E → ℝ` is *`β`-smooth* if its gradient is `β`-Lipschitz:
  `‖∇f(w) - ∇f(v)‖ ≤ β · ‖w - v‖`  for all `w v : E`.

The gradient `∇f(w)` is the Riesz representative of `fderiv ℝ f w`,
available in Mathlib as `gradient f w`. -/
structure BetaSmooth (f : E → ℝ) (β : ℝ) : Prop where
  /-- `f` is differentiable everywhere. -/
  differentiable : Differentiable ℝ f
  /-- The gradient `∇f` is `β`-Lipschitz. -/
  lipschitz_gradient : LipschitzWith β.toNNReal (fun w => gradient f w)

/-- The quadratic upper bound implied by β-smoothness:
  `f(v) ≤ f(w) + ⟪∇f(w), v - w⟫ + β/2 · ‖v - w‖²`.

This is the key inequality used throughout all subsequent convergence proofs. -/
theorem smooth_upper_bound {f : E → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hf : BetaSmooth f β) (w v : E) :
    f v ≤ f w + inner ℝ (gradient f w) (v - w) + β / 2 * ‖v - w‖ ^ 2 := by
  let g : ℝ → ℝ := fun t =>
    f (w + t • (v - w)) - t * inner ℝ (gradient f w) (v - w) -
      β / 2 * t ^ 2 * ‖v - w‖ ^ 2
  have hg0 : g 0 = f w := by
    simp [g]
  have hg1 :
      g 1 = f v - inner ℝ (gradient f w) (v - w) - β / 2 * ‖v - w‖ ^ 2 := by
    simp [g]
  have hdg : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g
        (inner ℝ (gradient f (w + x • (v - w)) - gradient f w) (v - w) -
          β * x * ‖v - w‖ ^ 2) x := by
    intro x _
    sorry
  have h_bound : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      inner ℝ (gradient f (w + x • (v - w)) - gradient f w) (v - w) -
        β * x * ‖v - w‖ ^ 2 ≤ 0 := by
    intro x _
    sorry
  have h_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    sorry
  have h_mean_value : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      inner ℝ (gradient f (w + c • (v - w)) - gradient f w) (v - w) -
        β * c * ‖v - w‖ ^ 2 = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope g
      (fun x =>
        inner ℝ (gradient f (w + x • (v - w)) - gradient f w) (v - w) -
          β * x * ‖v - w‖ ^ 2)
      (by norm_num) h_cont
    exact hdg
  rcases h_mean_value with ⟨c, hc, hc_eq⟩
  have h_le := h_bound c hc
  rw [hc_eq] at h_le
  have h_le2 : g 1 - g 0 ≤ 0 := by
    have h1 : (1 : ℝ) - 0 = 1 := by norm_num
    rw [h1, div_one] at h_le
    exact h_le
  linarith

/-- A single gradient descent step with step size `1/β` on a `β`-smooth function
decreases the objective by at least `1/(2β) · ‖∇f(w)‖²`. -/
theorem gd_descent_step {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hf : BetaSmooth f β) (w : E) :
    f (w - β⁻¹ • gradient f w) ≤ f w - (2 * β)⁻¹ * ‖gradient f w‖ ^ 2 := by
  have hkey := smooth_upper_bound hβ.le hf w (w - β⁻¹ • gradient f w)
  -- Simplify the vector expression: (w - β⁻¹ • ∇f w) - w = -(β⁻¹ • ∇f w)
  have hsub : (w - β⁻¹ • gradient f w) - w = -(β⁻¹ • gradient f w) := by
    simp
  rw [hsub] at hkey
  -- Simplify inner product and norm
  have hnorm : ‖-(β⁻¹ • gradient f w)‖ ^ 2 = (β⁻¹) ^ 2 * ‖gradient f w‖ ^ 2 := by
    calc
      ‖-(β⁻¹ • gradient f w)‖ ^ 2 = ‖β⁻¹ • gradient f w‖ ^ 2 := by simp
      _ = (‖β⁻¹‖ * ‖gradient f w‖) ^ 2 := by rw [norm_smul]
      _ = (|β⁻¹| * ‖gradient f w‖) ^ 2 := by rw [Real.norm_eq_abs]
      _ = (β⁻¹ * ‖gradient f w‖) ^ 2 := by rw [abs_of_pos (inv_pos.mpr hβ)]
      _ = (β⁻¹) ^ 2 * ‖gradient f w‖ ^ 2 := by ring
  rw [hnorm] at hkey
  simp only [inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq] at hkey
  -- Now hkey: f (w - β⁻¹ • ∇f w) ≤ f w + (-β⁻¹) * ‖∇f w‖ ^ 2 + β/2 * (β⁻² * ‖∇f w‖ ^ 2)
  have hcalc : f w + (-β⁻¹) * ‖gradient f w‖ ^ 2 + β / 2 * ((β⁻¹) ^ 2 * ‖gradient f w‖ ^ 2) =
      f w - (2 * β)⁻¹ * ‖gradient f w‖ ^ 2 := by
    field_simp [hβ.ne']
    ring
  linarith

/-! ### Gradient descent iteration (Definition 6.1) -/

/-- **Definition 6.1** (Telgarsky 2021, §7.1.1).
The gradient descent iterates starting at `w₀` with step sizes `η : ℕ → ℝ`:
  `w₀ = w₀`,  `w_{i+1} = w_i - η_i · ∇f(w_i)`. -/
noncomputable def gdIterate (f : E → ℝ) (η : ℕ → ℝ) (w₀ : E) : ℕ → E
  | 0     => w₀
  | i + 1 => gdIterate f η w₀ i - η i • gradient f (gdIterate f η w₀ i)

/-! ### Gradient flow (Definition 6.2) -/

/-- **Definition 6.2** (Telgarsky 2021, §7.1.1), two-sided form.
A curve `w : ℝ → E` is a gradient flow trajectory for `f` starting at `w₀` if it is `C¹` and
satisfies the ODE `w'(t) = -∇f(w(t))` at *every* real time, with initial condition `w(0) = w₀`.
This is the older, stronger predicate; for training only `t ≥ 0` matters, see
`ForwardGFTrajectory`. -/
structure GFTrajectory (f : E → ℝ) (w₀ : E) (w : ℝ → E) : Prop where
  /-- The curve starts at `w₀`. -/
  init : w 0 = w₀
  /-- `w` is continuously differentiable. -/
  cont_diff : ContDiff ℝ 1 w
  /-- The gradient flow ODE holds pointwise. -/
  ode : ∀ t : ℝ, HasDerivAt w (-gradient f (w t)) t

/-- **Forward-time gradient flow.** A curve `w : ℝ → E` is a forward gradient-flow trajectory for
`f` starting at `w₀` if `w 0 = w₀`, `w` is continuous on `[0, ∞)`, and `w' = -∇f(w)` for `t > 0`;
values at negative times are irrelevant. This is the notion used for training: a solution on
`[0, ∞)` need not extend backward (for an unbounded activation it can blow up in negative time), so
`GFTrajectory`, which asks for the ODE at every real time, is strictly stronger
(`GFTrajectory.forward`). -/
structure ForwardGFTrajectory (f : E → ℝ) (w₀ : E) (w : ℝ → E) : Prop where
  /-- The curve starts at `w₀`. -/
  init : w 0 = w₀
  /-- `w` is continuous on `[0, ∞)`. -/
  continuousOn : ContinuousOn w (Set.Ici 0)
  /-- The gradient flow ODE holds for positive times. -/
  ode : ∀ t : ℝ, 0 < t → HasDerivAt w (-gradient f (w t)) t

/-- Every (two-sided) gradient-flow trajectory restricts to a forward one. -/
theorem GFTrajectory.forward {f : E → ℝ} {w₀ : E} {w : ℝ → E} (h : GFTrajectory f w₀ w) :
    ForwardGFTrajectory f w₀ w :=
  ⟨h.init, h.cont_diff.continuous.continuousOn, fun t _ => h.ode t⟩

/-! ### Energy identity along gradient flow

Along `w' = -∇f(w)` the value `f(w(t))` decreases at rate `‖∇f(w(t))‖² = ‖w'(t)‖²`. These are
generic facts about gradient flows; the NTK files specialize them to the training risk. -/

/-- **Chain rule along a gradient curve.** If `w' = -∇f(w)` at `t` within `s` and `f` is
differentiable at `w t`, then `(f ∘ w)' = -‖∇f(w t)‖²` within `s` at `t`. -/
theorem hasDerivWithinAt_comp_of_neg_gradient {f : E → ℝ} {w : ℝ → E} {s : Set ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (w t)) (hw : HasDerivWithinAt w (-gradient f (w t)) s t) :
    HasDerivWithinAt (fun u => f (w u)) (-‖gradient f (w t)‖ ^ 2) s t := by
  have h := hf.hasGradientAt.hasFDerivAt.comp_hasDerivWithinAt t hw
  rwa [InnerProductSpace.toDual_apply_apply, inner_neg_right, real_inner_self_eq_norm_sq] at h

/-- Two-sided version of `hasDerivWithinAt_comp_of_neg_gradient`. -/
theorem hasDerivAt_comp_of_neg_gradient {f : E → ℝ} {w : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (w t)) (hw : HasDerivAt w (-gradient f (w t)) t) :
    HasDerivAt (fun u => f (w u)) (-‖gradient f (w t)‖ ^ 2) t := by
  rw [← hasDerivWithinAt_univ] at hw ⊢
  exact hasDerivWithinAt_comp_of_neg_gradient hf hw

namespace ForwardGFTrajectory

variable {f : E → ℝ} {w₀ : E} {w : ℝ → E}

/-- Along a forward gradient flow, `(f ∘ w)'(t) = -‖∇f(w t)‖²` at every positive time. -/
theorem hasDerivAt_comp (hw : ForwardGFTrajectory f w₀ w) {t : ℝ} (ht : 0 < t)
    (hf : DifferentiableAt ℝ f (w t)) :
    HasDerivAt (fun u => f (w u)) (-‖gradient f (w t)‖ ^ 2) t :=
  hasDerivAt_comp_of_neg_gradient hf (hw.ode t ht)

/-- The velocity of a forward gradient flow at a positive time is `-∇f(w t)`. -/
theorem deriv_eq_neg_gradient (hw : ForwardGFTrajectory f w₀ w) {t : ℝ} (ht : 0 < t) :
    deriv w t = -gradient f (w t) :=
  (hw.ode t ht).deriv

/-- **Kinetic energy.** The squared speed of a forward gradient flow is `‖∇f(w t)‖²`. -/
theorem norm_deriv_sq (hw : ForwardGFTrajectory f w₀ w) {t : ℝ} (ht : 0 < t) :
    ‖deriv w t‖ ^ 2 = ‖gradient f (w t)‖ ^ 2 := by
  rw [hw.deriv_eq_neg_gradient ht, norm_neg]

/-- The loss is continuous along a forward gradient flow on `[0, T]` wherever it is differentiable
at the curve. -/
theorem continuousOn_comp (hw : ForwardGFTrajectory f w₀ w) {T : ℝ}
    (hf : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ f (w t)) :
    ContinuousOn (fun u => f (w u)) (Set.Icc 0 T) := fun t ht =>
  (hf t ht).continuousAt.comp_continuousWithinAt
    ((hw.continuousOn t ht.1).mono Set.Icc_subset_Ici_self)

/-- The dissipation rate `‖∇f(w t)‖²` of a forward gradient flow is interval integrable on
`[0, T]`; no continuity of `∇f` is needed, only that `f ∘ w` is monotone. -/
theorem intervalIntegrable_norm_sq_gradient (hw : ForwardGFTrajectory f w₀ w) {T : ℝ}
    (hT : 0 ≤ T) (hf : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ f (w t)) :
    IntervalIntegrable (fun t => ‖gradient f (w t)‖ ^ 2) volume 0 T := by
  have hcont : ContinuousOn (fun u => -f (w u)) (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]
    exact (hw.continuousOn_comp hf).neg
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont (fun t ht => ?_)
    (fun t _ => sq_nonneg _)
  rw [min_eq_left hT, max_eq_right hT] at ht
  simpa using (hw.hasDerivAt_comp ht.1 (hf t ⟨ht.1.le, ht.2.le⟩)).fun_neg

/-- **Integrated energy identity.** `f(w 0) - f(w T) = ∫₀ᵀ ‖∇f(w t)‖² dt` along a forward
gradient flow, whenever `f` is differentiable at the curve on `[0, T]`. -/
theorem integral_norm_sq_gradient_eq_sub (hw : ForwardGFTrajectory f w₀ w) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ f (w t)) :
    ∫ t in (0 : ℝ)..T, ‖gradient f (w t)‖ ^ 2 = f (w 0) - f (w T) := by
  have hcont : ContinuousOn (fun u => -f (w u)) (Set.Icc 0 T) := (hw.continuousOn_comp hf).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont
    (f' := fun t => ‖gradient f (w t)‖ ^ 2) (fun t ht => by
      simpa using (hw.hasDerivAt_comp ht.1 (hf t ⟨ht.1.le, ht.2.le⟩)).fun_neg)
    (hw.intervalIntegrable_norm_sq_gradient hT hf)
  rw [h]
  ring

/-- The integrated energy identity in terms of the actual velocity:
`∫₀ᵀ ‖w'(t)‖² dt = f(w 0) - f(w T)`. -/
theorem integral_norm_deriv_sq_eq_sub (hw : ForwardGFTrajectory f w₀ w) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ f (w t)) :
    ∫ t in (0 : ℝ)..T, ‖deriv w t‖ ^ 2 = f (w 0) - f (w T) := by
  rw [← hw.integral_norm_sq_gradient_eq_sub hT hf, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le hT]
  exact setIntegral_congr_fun measurableSet_Ioc fun t ht => hw.norm_deriv_sq ht.1

end ForwardGFTrajectory

/-- A curve `w : ℝ → E` is a trajectory for a time-dependent vector field `v : ℝ → E → E`
starting at `w₀` if it satisfies the ODE `w_prime(t) = v t (w(t))` with initial condition
`w(0) = w₀`.
We use this for coupled or non-autonomous gradient flows. -/
structure VaryingGFTrajectory (v : ℝ → E → E) (w₀ : E) (w : ℝ → E) : Prop where
  /-- The curve starts at `w₀`. -/
  init : w 0 = w₀
  /-- `w` is continuously differentiable. -/
  cont_diff : ContDiff ℝ 1 w
  /-- The generalized flow ODE holds pointwise. -/
  ode : ∀ t : ℝ, HasDerivAt w (v t (w t)) t

/-! ### Convexity (Definition 7.3) -/

/-- **Definition 7.3** (First-order characterization of convexity, Telgarsky 2021, §7.2).
A differentiable function `f : E → ℝ` is convex if for all `w, v : E`,
  `f(v) ≥ f(w) + ⟪∇f(w), v - w⟫`. -/
def IsConvex (f : E → ℝ) : Prop :=
  ∀ w v : E, f w + inner ℝ (gradient f w) (v - w) ≤ f v

/-- A convex function's value is non-decreasing along gradient flow.
Equivalently, `d/dt f(w(t)) = -‖∇f(w(t))‖² ≤ 0`. -/
lemma gf_monotone_decrease {f : E → ℝ} {w₀ : E} {w : ℝ → E}
    (hf : Differentiable ℝ f) (hw : GFTrajectory f w₀ w) (t : ℝ) :
    HasDerivAt (f ∘ w) (-‖gradient f (w t)‖ ^ 2) t :=
  hasDerivAt_comp_of_neg_gradient (f := f) (w := w) (hf (w t)) (hw.ode t)

/-! ### Strong convexity (Definition 7.5) -/

/-- **Definition 7.5** (Telgarsky 2021, §7.2).
A differentiable function `f : E → ℝ` is `λ`-strongly convex if for all `w, v : E`,
  `f(v) ≥ f(w) + ⟪∇f(w), v - w⟫ + λ/2 · ‖v - w‖²`.

Equivalently, `f - λ/2 · ‖·‖²` is convex. -/
def IsStronglyConvex (f : E → ℝ) (c : ℝ) : Prop :=
  ∀ w v : E, f w + inner ℝ (gradient f w) (v - w) + c / 2 * ‖v - w‖ ^ 2 ≤ f v

/-- Strong convexity implies convexity (when `λ ≥ 0`). -/
lemma IsStronglyConvex.isConvex {f : E → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : IsStronglyConvex f c) : IsConvex f := by
  intro w v
  have := hf w v
  linarith [mul_nonneg (div_nonneg hc (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg ‖v - w‖)]

/-- A `λ`-strongly convex function has a unique critical point, which is its global minimizer. -/
lemma IsStronglyConvex.unique_minimizer {f : E → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : IsStronglyConvex f c) (hdf : Differentiable ℝ f)
    {w v : E} (hw : gradient f w = 0) (hv : gradient f v = 0) : w = v := by
  sorry

/-! ### Approximate gradient iteration (Definition 7.7) -/

/-- **Definition 7.7** (Approximate gradient iteration, Telgarsky 2021, §7.9).
Given approximate gradient vectors `(g_i)_{i ≥ 0}` and step size `η`, the iterate sequence is
  `w₀ = w₀`,  `w_{i+1} = w_i - η · g_i`. -/
noncomputable def approxGDIterate (η : ℝ) (w₀ : E) (g : ℕ → E) : ℕ → E
  | 0     => w₀
  | i + 1 => approxGDIterate η w₀ g i - η • g i

/-- The noise term `εᵢ = ⟪gᵢ - ∇f(wᵢ), z - wᵢ⟫` for a fixed reference point `z`.
This term appears in the convergence bound of Lemma 7.2 (approxGDConvergence). -/
noncomputable def approxNoiseTerm (f : E → ℝ) (g : ℕ → E) (w : ℕ → E) (z : E) (i : ℕ) : ℝ :=
  inner ℝ (g i - gradient f (w i)) (z - w i)

/-! ### Stochastic gradient oracle (Definition 7.8) -/

/-- **Definition 7.8** (Stochastic gradient oracle, Telgarsky 2021, §7.9).
Random vectors `(w_i, g_i)` on a probability space `(Ω, ℱ, P)` form a stochastic
gradient oracle for `f` if the conditional expectation of `g_i` given the filtration
up to step `i` equals the true gradient: `E[g_i | ℱ_i] = ∇f(w_i)` a.s.

In this definition we capture the essential unbiasedness condition.
The full measure-theoretic formalization uses `MeasureTheory.condExp`
from Mathlib and follows the pattern of `SequentialLearning.Algorithm`. -/
structure IsStochasticGradient {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (f : E → ℝ) (P : Measure Ω)
    (w g : ℕ → Ω → E)
    (ℱ : ℕ → MeasurableSpace Ω) : Prop where
  /-- Each `wᵢ` is `ℱᵢ`-measurable. -/
  adapted_w : ∀ i, Measurable[ℱ i] (w i)
  /-- Each `gᵢ` is `ℱᵢ`-measurable. -/
  adapted_g : ∀ i, Measurable[ℱ i] (g i)
  /-- `gᵢ` is an unbiased estimate of `∇f(wᵢ)` given `ℱᵢ`. -/
  unbiased : ∀ i, ∀ᵐ ω ∂P,
    (condExp (ℱ i) P (fun ω => g i ω) ω) = gradient f (w i ω)

end ConvexOpt

end
