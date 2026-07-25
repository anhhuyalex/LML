/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Mirror Flow Interpretation of Diagonal Linear Networks

This file formalizes the mirror flow interpretation of the DLN dynamics.
-/

open scoped Matrix

@[expose] public section

namespace Lasso

open Filter Topology Asymptotics

variable {ι : Type*} [Fintype ι]

/-- The gradient of the entropy mirror map, `∇h(x) = 1/4 * log x`, coordinatewise. -/
noncomputable def entropyMirrorGradient (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun i => (1 / 4 : ℝ) * Real.log (x i))

/-- The closed-form positive-DLN vector field in the effective parameter `x = u²`. -/
noncomputable def positiveEffectiveVectorField
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun i => -4 * x i * ((matVec M x) i - r i + lambda))



-- Exact second-order expansion of the quadratic form `x ↦ (1/2)⟪x, Mx⟫`.
private lemma quadratic_form_increment
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (y a : EuclideanSpace ℝ ι) :
    (1 / 2 : ℝ) * inner ℝ (y + a) (matVec M (y + a)) -
        (1 / 2 : ℝ) * inner ℝ y (matVec M y) =
      inner ℝ (matVec M y) a +
        (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
  rw [matVec_add]
  rw [inner_add_left, inner_add_right, inner_add_right]
  rw [inner_matVec_comm_of_isSymm M hM y a]
  rw [real_inner_comm a (matVec M y)]
  ring

-- Taylor expansion of the quadratic loss in the effective variable.
private lemma quadraticLoss_add_sub
    (M : Matrix ι ι ℝ) (r y a : EuclideanSpace ℝ ι) (hM : M.IsSymm) :
    quadraticLoss M r (y + a) - quadraticLoss M r y =
      inner ℝ (matVec M y - r) a +
        (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
  have h_linear_increment :
      - inner ℝ r (y + a) + inner ℝ r y = - inner ℝ r a := by
    rw [inner_add_right]
    ring
  have h_first_order_collect :
      inner ℝ (matVec M y) a - inner ℝ r a =
        inner ℝ (matVec M y - r) a := (inner_sub_left _ _ _).symm
  calc
    quadraticLoss M r (y + a) - quadraticLoss M r y
        = ((1 / 2 : ℝ) * inner ℝ (y + a) (matVec M (y + a)) -
              inner ℝ r (y + a)) -
            ((1 / 2 : ℝ) * inner ℝ y (matVec M y) - inner ℝ r y) := by
          simp [quadraticLoss]
    _ = ((1 / 2 : ℝ) * inner ℝ (y + a) (matVec M (y + a)) -
              (1 / 2 : ℝ) * inner ℝ y (matVec M y)) +
            (- inner ℝ r (y + a) + inner ℝ r y) := by
          ring
    _ = (inner ℝ (matVec M y) a +
              (1 / 2 : ℝ) * inner ℝ a (matVec M a)) +
            (- inner ℝ r a) := by
          rw [quadratic_form_increment M hM y a, h_linear_increment]
    _ = inner ℝ (matVec M y - r) a +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
          rw [← h_first_order_collect]
          ring

-- Coordinatewise square expansion around `u`, written without local `let`
-- bindings so it can be reused directly at call sites.
omit [Fintype ι] in
private lemma coordinateSquare_eq_base_add_increment
    (u x' : EuclideanSpace ℝ ι) :
    coordinateSquare x' =
      coordinateSquare u +
        euclideanOf fun i ↦ 2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i) := by
  ext i
  simp [coordinateSquare, euclideanOf]
  ring

-- The effective square increment splits into a linear term plus a quadratic
-- remainder in the displacement.
omit [Fintype ι] in
private lemma square_increment_decompose
    (u h : EuclideanSpace ℝ ι) :
    (euclideanOf fun i ↦ 2 * u i * h i + h i * h i) =
      (euclideanOf fun i ↦ 2 * u i * h i) + coordinateSquare h := by
  ext i
  simp [coordinateSquare, euclideanOf]

-- Exact expansion of the weight-decay term after subtracting its linear part.
private lemma weight_decay_increment
    (lambda : ℝ) (u h : EuclideanSpace ℝ ι) :
    lambda * ‖u + h‖ ^ 2 - lambda * ‖u‖ ^ 2 -
        inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h =
      lambda * ‖h‖ ^ 2 := by
  rw [norm_add_sq_real]
  have H : (euclideanOf fun i ↦ 2 * lambda * (u : ι → ℝ) i) = (2 * lambda) • u := by
    ext i
    dsimp [euclideanOf]
  rw [H, inner_smul_left, starRingEnd_apply, star_trivial]
  ring

-- The same weight-decay expansion, stated at an arbitrary endpoint `x'`.
private lemma weight_decay_sub_increment
    (lambda : ℝ) (u x' : EuclideanSpace ℝ ι) :
    lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2 -
        inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) (x' - u) =
      lambda * ‖x' - u‖ ^ 2 := by
  have hx' : x' = u + (x' - u) := by abel
  rw [hx']
  have hdisp : u + (x' - u) - u = x' - u := by abel
  simpa [hdisp] using weight_decay_increment lambda u (x' - u)

-- Split the displayed linear term into the loss-linear and weight-decay-linear
-- contributions.
private lemma inner_linear_split
    (lambda : ℝ) (u g h : EuclideanSpace ℝ ι) :
    inner ℝ (euclideanOf fun i ↦ 2 * u i * (g i + lambda)) h =
      inner ℝ g (euclideanOf fun i ↦ 2 * u i * h i) +
        inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h := by
  have h_lhs :
      inner ℝ (euclideanOf fun i ↦ 2 * u i * (g i + lambda)) h =
        ∑ i, (2 * u i * (g i + lambda)) * h i := by
    dsimp [euclideanOf]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  have h_loss :
      inner ℝ g (euclideanOf fun i ↦ 2 * u i * h i) =
        ∑ i, g i * (2 * u i * h i) := by
    dsimp [euclideanOf]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  have h_decay :
      inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h =
        ∑ i, (2 * lambda * u i) * h i := by
    dsimp [euclideanOf]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  rw [h_lhs, h_loss, h_decay, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

-- Coordinate form of the tilted-loss gradient paired against a displacement.
private lemma inner_tilted_gradient
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x h : EuclideanSpace ℝ ι) :
    inner ℝ (euclideanOf fun i => (M.mulVec x) i - r i + lambda) h =
      inner ℝ (matVec M x) h - inner ℝ r h + lambda * inner ℝ ones h := by
  have h1 : inner ℝ (euclideanOf fun i => (M.mulVec x) i - r i + lambda) h =
      ∑ i, ((M.mulVec x) i - r i + lambda) * h i := by
    dsimp [euclideanOf]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  rw [h1]
  have h2 : inner ℝ (matVec M x) h = ∑ i, (M.mulVec x) i * h i := by
    dsimp [matVec, euclideanOf]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  have h3 : inner ℝ r h = ∑ i, r i * h i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  have h4 : lambda * inner ℝ ones h = ∑ i, lambda * h i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [ones, euclideanOf, dotProduct]
    have h_lambda : (∑ i, lambda * (1 * h i)) = ∑ i, lambda * h i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [←h_lambda, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [h2, h3, h4, ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option linter.unusedFintypeInType false
/--
The derivative of the coordinate square of a function `u`.

Informal proof reference: `docs/Lasso.md`, Section 3, Eq. (3.3).
Coordinatewise, this is just the chain/product rule:
`d (u_i(t)^2) / dt = 2 * u_i(t) * u_i'(t)`.
-/
lemma hasDerivAt_coordinateSquare
    (u : ℝ → EuclideanSpace ℝ ι) (t : ℝ) (u' : EuclideanSpace ℝ ι)
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun τ => coordinateSquare (u τ))
      (euclideanOf (fun i => 2 * u t i * u' i)) t := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have h1 : HasDerivAt (fun τ => e (u τ)) (e u') t := e.hasFDerivAt.comp_hasDerivAt t hu
  dsimp [coordinateSquare, euclideanOf]
  have hd_pi : HasDerivAt (fun τ => (fun i => u τ i * u τ i)) (fun i => 2 * u t i * u' i) t := by
    apply hasDerivAt_pi.2
    intro i
    have hui : HasDerivAt (fun τ => e (u τ) i) (e u' i) t := hasDerivAt_pi.1 h1 i
    exact HasDerivAt.mul hui hui |>.congr_deriv (by
      dsimp [e, ContinuousLinearEquiv.coe_coe]
      simp; ring_nf)
  exact e.symm.hasFDerivAt.comp_hasDerivAt t hd_pi

-- Algebraic Taylor expansion of the positive-DLN objective after subtracting
-- the claimed first-order term.
private lemma posDlnObjective_taylor_remainder
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (u x' : EuclideanSpace ℝ ι) :
    posDlnObjective M r lambda x' - posDlnObjective M r lambda u -
        inner ℝ
          (euclideanOf fun i ↦
            2 * u i * ((matVec M (coordinateSquare u)) i - r i + lambda))
          (x' - u) =
      inner ℝ ((matVec M (coordinateSquare u)) - r) (coordinateSquare (x' - u)) +
        lambda * ‖x' - u‖ ^ 2 +
          (1 / 2 : ℝ) *
          inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i))
            (matVec M
              (euclideanOf fun i ↦
                2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i))) := by
  let h : EuclideanSpace ℝ ι := x' - u
  let y : EuclideanSpace ℝ ι := coordinateSquare u
  let a : EuclideanSpace ℝ ι :=
    euclideanOf fun i ↦ 2 * u i * h i + h i * h i
  have h_square_increment : coordinateSquare x' = y + a := by
    simpa [h, y, a] using coordinateSquare_eq_base_add_increment u x'
  have h_loss_expansion :
      quadraticLoss M r (y + a) - quadraticLoss M r y =
        inner ℝ (matVec M y - r) a +
          (1 / 2 : ℝ) * inner ℝ a (matVec M a) :=
    quadraticLoss_add_sub M r y a hM
  have h_a_decompose :
      a = (euclideanOf fun i ↦ 2 * u i * h i) + coordinateSquare h := by
    simpa [a] using square_increment_decompose u h
  have h_norm_expansion :
      lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2 -
          inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h =
        lambda * ‖h‖ ^ 2 := by
    simpa [h] using weight_decay_sub_increment lambda u x'
  have h_linear_split :
      inner ℝ
          (euclideanOf fun i ↦
            2 * u i * ((matVec M y) i - r i + lambda)) h =
        inner ℝ (matVec M y - r) (euclideanOf fun i ↦ 2 * u i * h i) +
          inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h := by
    simpa using inner_linear_split lambda u (matVec M y - r) h
  have h_combined :
      posDlnObjective M r lambda x' - posDlnObjective M r lambda u -
          inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((matVec M y) i - r i + lambda)) h =
        inner ℝ (matVec M y - r) (coordinateSquare h) +
          lambda * ‖h‖ ^ 2 +
          (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
    have h_norm_collect :
        lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2 =
          lambda * ‖h‖ ^ 2 +
            inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h := by
      linarith [h_norm_expansion]
    calc
      posDlnObjective M r lambda x' - posDlnObjective M r lambda u -
          inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((matVec M y) i - r i + lambda)) h
          =
        (quadraticLoss M r (y + a) - quadraticLoss M r y) +
          (lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2) -
          inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((matVec M y) i - r i + lambda)) h := by
            simp [posDlnObjective, h_square_increment, y]
            ring
      _ =
        (inner ℝ (matVec M y - r) a +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a)) +
          (lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2) -
          inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((matVec M y) i - r i + lambda)) h := by
            rw [h_loss_expansion]
      _ =
        (inner ℝ (matVec M y - r)
            ((euclideanOf fun i ↦ 2 * u i * h i) + coordinateSquare h) +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a)) +
          (lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2) -
          inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((matVec M y) i - r i + lambda)) h := by
            rw [h_a_decompose]
      _ =
        (inner ℝ (matVec M y - r) (euclideanOf fun i ↦ 2 * u i * h i) +
            inner ℝ (matVec M y - r) (coordinateSquare h) +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a)) +
          (lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2) -
          inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((matVec M y) i - r i + lambda)) h := by
            rw [inner_add_right]
      _ =
        (inner ℝ (matVec M y - r) (euclideanOf fun i ↦ 2 * u i * h i) +
            inner ℝ (matVec M y - r) (coordinateSquare h) +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a)) +
          (lambda * ‖h‖ ^ 2 +
            inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h) -
          (inner ℝ (matVec M y - r) (euclideanOf fun i ↦ 2 * u i * h i) +
            inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h) := by
            rw [h_norm_collect, h_linear_split]
      _ =
        inner ℝ (matVec M y - r) (coordinateSquare h) +
          lambda * ‖h‖ ^ 2 +
          (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
            ring
  simpa [h, y, a] using h_combined

/--
The gradient of the positive DLN objective function.

Informal proof reference: `docs/Lasso.md`, Section 3, Eq. (3.3).
The objective is $L(u) = \ell(u^2) + \lambda\|u\|^2$ where
$\ell(x) = \frac{1}{2}\langle x, Mx \rangle - \langle r, x \rangle$.
Taking the differential, we have
$d\ell(v) = \frac{1}{2}(\langle v, Mx \rangle + \langle x, Mv \rangle)
  - \langle r, v \rangle$.
Since $M$ is assumed to be symmetric, $\langle x, Mv \rangle = \langle Mx, v \rangle$.
Thus the gradient is $\nabla \ell(x) = Mx - r$.
Applying the chain rule with respect to $u$, we obtain
$\frac{\partial L}{\partial u_i}
  = 2 u_i \frac{\partial \ell}{\partial x_i} + 2 \lambda u_i
  = 2 u_i ( (M x)_i - r_i + \lambda)$.
-/
lemma hasGradientAt_posDlnObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (u : EuclideanSpace ℝ ι) :
    HasGradientAt (fun u' => posDlnObjective M r lambda u')
      (euclideanOf
        (fun i => 2 * u i * ((matVec M (coordinateSquare u)) i - r i + lambda))) u := by
  -- The Taylor remainder is quadratic (or higher order) in
  -- `x' - u`, hence little-o of `x' - u` at `u`.
  have h_remainder_o :
      (fun x' : EuclideanSpace ℝ ι ↦
        inner ℝ ((matVec M (coordinateSquare u)) - r) (coordinateSquare (x' - u)) +
          lambda * ‖x' - u‖ ^ 2 +
          (1 / 2 : ℝ) *
            inner ℝ
              (euclideanOf fun i ↦
                2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i))
              (matVec M
                (euclideanOf fun i ↦
                  2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i))))
        =o[nhds u] fun x' : EuclideanSpace ℝ ι ↦ x' - u := by
    -- Sketch: prove each summand separately.
    -- * `coordinateSquare (x' - u)` is `O(‖x' - u‖^2)`, so its inner product
    --   with the fixed vector `matVec M (coordinateSquare u) - r` is little-o
    --   of `x' - u`.
    -- * `lambda * ‖x' - u‖^2` is little-o by the standard quadratic estimate.
    -- * the final quadratic-form term is `O(‖2*u*(x'-u)+(x'-u)^2‖^2)`, and the
    --   vector inside is `O(‖x' - u‖)`, hence the term is again little-o.
    sorry
  have h_grad : HasGradientAt (fun u' => posDlnObjective M r lambda u')
      (euclideanOf (fun i => 2 * u i * ((matVec M (coordinateSquare u)) i - r i + lambda))) u := by
    rw [hasGradientAt_iff_isLittleO]
    -- Write `h = x' - u`.  The next identity is the Taylor expansion of the
    -- polynomial objective after the claimed linear part is subtracted.  It is
    -- proved coordinatewise by unfolding `posDlnObjective`, `quadraticLoss`,
    -- `coordinateSquare`, `matVec`, and `euclideanOf`; the only non-ring step is
    -- using `hM : M.IsSymm` to combine the two cross-terms of the quadratic form.
    exact h_remainder_o.congr_left
      (fun x' => (posDlnObjective_taylor_remainder M r lambda hM u x').symm)
  exact h_grad

/-- The gradient of the positive-DLN objective in weight coordinates. -/
lemma gradient_posDlnObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (u : EuclideanSpace ℝ ι) :
    gradient (fun u' => posDlnObjective M r lambda u') u =
      euclideanOf
        (fun i => 2 * u i * ((matVec M (coordinateSquare u)) i - r i + lambda)) :=
  (hasGradientAt_posDlnObjective M r lambda hM u).gradient

/-- The mirror-flow ODE `d ∇h(x(t)) / dt = -∇ \widetilde L(x(t))`. -/
def IsEntropyMirrorFlow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : ℝ → EuclideanSpace ℝ ι) : Prop :=
  ∀ t : ℝ,
    HasDerivAt (fun τ => entropyMirrorGradient (x τ))
      (-gradient (tiltedLoss M r lambda) (x t)) t

/--
Equation (3.3) from `docs/Lasso.md`: the effective positive parameter
`x = u²` satisfies a closed ODE.

Informal proof reference: `docs/Lasso.md`, Section 3, Eq. (3.3).
Differentiate `x_i = u_i^2`, use the gradient flow equation for `u_i`, and
apply the chain rule to `ell(u²) + lambda ‖u‖²`.
-/
theorem pos_effective_parameter_hasDerivAt
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) (hM : M.IsSymm) :
    ∀ t : ℝ,
      HasDerivAt (fun τ => posEffectiveParameter u τ)
        (positiveEffectiveVectorField M r lambda (posEffectiveParameter u t)) t := by
  intro t
  have hu_ode := hu.ode t
  dsimp [posDlnVectorField] at hu_ode
  rw [gradient_posDlnObjective M r lambda hM] at hu_ode
  exact (hasDerivAt_coordinateSquare u t _ hu_ode).congr_deriv (by
    ext i
    dsimp [positiveEffectiveVectorField, posEffectiveParameter, coordinateSquare, euclideanOf]
    ring)

/--
Section 4.2 from `docs/Lasso.md`: The Mirror Flow interpretation of the positive DLN dynamics.
An informal proof:
The positive DLN dynamics are given by `du/dt = -∇ᵤ L(u)`. By the chain rule,
the effective linear parameter `x = u ∘ u` evolves as
`dx/dt = -4 x ∘ ∇ell(x) - 4 lambda x`.
Using the entropy mirror map `h(x) = (1/4) * Σᵢ (xᵢ log xᵢ - xᵢ)`, we have
`∇h(x) = (1/4) log x`. Thus
`d ∇h(x) / dt = -∇ell(x) - lambda * 𝟙 = -∇L̃(x)`.
Thus the DLN dynamics can be written as a mirror flow in the dual space.
-/
lemma dln_is_mirror_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε β u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0) (hM : M.IsSymm) :
    ∀ t,
      HasDerivAt
        (fun t =>
          (WithLp.equiv 2 _).symm
            (fun i => (1 / 4 : ℝ) * Real.log (posEffectiveParameter u t i)))
        ((WithLp.equiv 2 _).symm
          (fun i => -((M.mulVec (posEffectiveParameter u t)) i - r i + lambda))) t := by
  intro t
  have hd := pos_effective_parameter_hasDerivAt M r lambda ε β u hu hM t
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have hd_e : HasDerivAt (fun τ => e (posEffectiveParameter u τ))
      (e (positiveEffectiveVectorField M r lambda (posEffectiveParameter u t))) t :=
    e.hasFDerivAt.comp_hasDerivAt t hd
  have h_pi : HasDerivAt (fun τ => (fun i => (1 / 4 : ℝ) * Real.log (posEffectiveParameter u τ i)))
      (fun i => -((M.mulVec (posEffectiveParameter u t)) i - r i + lambda)) t := by
    apply hasDerivAt_pi.2
    intro i
    have hd_i : HasDerivAt (fun τ => posEffectiveParameter u τ i)
      (e (positiveEffectiveVectorField M r lambda (posEffectiveParameter u t)) i) t :=
        hasDerivAt_pi.1 hd_e i
    have hlog : HasDerivAt Real.log (posEffectiveParameter u t i)⁻¹
        (posEffectiveParameter u t i) :=
      Real.hasDerivAt_log (hu_pos t i)
    have hcomp := HasDerivAt.comp t hlog hd_i
    have hmul := HasDerivAt.const_mul (1 / 4 : ℝ) hcomp
    exact hmul.congr_deriv (by
      dsimp [positiveEffectiveVectorField, euclideanOf, matVec, e,
        ContinuousLinearEquiv.coe_coe, Equiv.toFun_as_coe,
        LinearEquiv.coe_coe, WithLp.linearEquiv, WithLp.equiv, WithLp.toLp]
      change (1 / 4 : ℝ) * ((posEffectiveParameter u t i)⁻¹ *
        (-4 * posEffectiveParameter u t i *
          (((M.mulVec (posEffectiveParameter u t)) i) - r i + lambda))) =
        -(((M.mulVec (posEffectiveParameter u t)) i) - r i + lambda)
      have hp := hu_pos t i
      field_simp [hp]
    )
  exact e.symm.hasFDerivAt.comp_hasDerivAt t h_pi

/--
The gradient of the tilted loss function.

Informal proof reference: `docs/Lasso.md`, Section 4.2.
The objective function is
$\widetilde{L}(x) = \frac{1}{2}\langle x, Mx \rangle - \langle r, x \rangle
  + \lambda \langle \mathbf{1}, x \rangle$.
Taking the differential in the direction $v$:
1. For the quadratic term:
   $d(\frac{1}{2}\langle x, Mx \rangle)(v)
     = \frac{1}{2}(\langle v, Mx \rangle + \langle x, Mv \rangle)$.
   Since $M$ is symmetric, this equals $\langle Mx, v \rangle$.
2. For the linear term $-r$: $d(-\langle r, x \rangle)(v) = -\langle r, v \rangle$.
3. For the linear term $\lambda \mathbf{1}$:
   $d(\lambda \langle \mathbf{1}, x \rangle)(v)
     = \lambda \langle \mathbf{1}, v \rangle
     = \langle \lambda \mathbf{1}, v \rangle$.
Thus, by the Riesz representation theorem, the gradient is $Mx - r + \lambda \mathbf{1}$.
-/
lemma isLittleO_inner_matVec
    (M : Matrix ι ι ℝ) (_hM : M.IsSymm) :
    (fun (h : EuclideanSpace ℝ ι) => inner ℝ h (matVec M h)) =o[nhds 0] fun h => h := by
  apply Asymptotics.IsLittleO.of_isBigOWith
  intro c hc
  rw [Asymptotics.isBigOWith_iff]
  have h_cont : Continuous (matVec M) := by
    have h_eq : matVec M = fun (x : EuclideanSpace ℝ ι) =>
        ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv).symm
          (M.mulVec (x : ι → ℝ)) := rfl
    rw [h_eq]
    apply Continuous.comp ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv).symm.continuous
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    exact Continuous.mul continuous_const
      ((continuous_apply j).comp
        (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous)
  have h_tendsto : Tendsto (fun h => ‖matVec M h‖) (nhds 0) (nhds 0) := by
    refine tendsto_norm_zero.comp ?_
    simpa [matVec, euclideanOf] using h_cont.tendsto 0
  have h_eventually : ∀ᶠ h in nhds 0, ‖matVec M h‖ < c := by
    apply (tendsto_order.1 h_tendsto).2 c hc
  apply h_eventually.mono
  intro h hh
  calc ‖inner ℝ h (matVec M h)‖
    _ ≤ ‖h‖ * ‖matVec M h‖ := norm_inner_le_norm h (matVec M h)
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left (le_of_lt hh) (norm_nonneg _)
    _ = c * ‖h‖ := mul_comm _ _

/-- The tilted loss has gradient `M x - r + lambda * 𝟙` at every point. -/
lemma hasGradientAt_tiltedLoss
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (tiltedLoss M r lambda)
      (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) x := by
  have h_grad : HasGradientAt (tiltedLoss M r lambda)
      (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) x := by
    rw [hasGradientAt_iff_isLittleO]
    have h_expansion : ∀ h, tiltedLoss M r lambda (x + h) - tiltedLoss M r lambda x -
      inner ℝ (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) h =
        (1 / 2 : ℝ) * inner ℝ h (matVec M h) := by
      intro h
      dsimp [tiltedLoss, quadraticLoss]
      have h_M_add : matVec M (x + h) = matVec M x + matVec M h := matVec_add M x h
      rw [h_M_add]
      have h_inner_M : inner ℝ (x + h) (matVec M x + matVec M h) =
          inner ℝ x (matVec M x) + inner ℝ x (matVec M h) +
            inner ℝ h (matVec M x) + inner ℝ h (matVec M h) := by
        rw [inner_add_left, inner_add_right, inner_add_right]
        ring
      rw [h_inner_M]
      have h_cross : inner ℝ x (matVec M h) = inner ℝ (matVec M x) h :=
        inner_matVec_comm_of_isSymm M hM x h
      have h_inner_r : inner ℝ r (x + h) = inner ℝ r x + inner ℝ r h := inner_add_right _ _ _
      rw [h_inner_r]
      have h_inner_ones : inner ℝ ones (x + h) =
          inner ℝ ones x + inner ℝ ones h := inner_add_right _ _ _
      rw [h_inner_ones]
      have h_symm : inner ℝ (matVec M x) h = inner ℝ h (matVec M x) := real_inner_comm _ _
      rw [h_cross, h_symm]
      have h_inner_grad : inner ℝ (euclideanOf fun i => (M.mulVec x) i - r i + lambda) h =
          inner ℝ (matVec M x) h - inner ℝ r h + lambda * inner ℝ ones h :=
        inner_tilted_gradient M r lambda x h
      rw [h_inner_grad, h_symm]
      ring
    have h_expansion_x' : ∀ x', tiltedLoss M r lambda x' - tiltedLoss M r lambda x -
      inner ℝ (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) (x' - x) =
        (1 / 2 : ℝ) * inner ℝ (x' - x) (matVec M (x' - x)) := by
      intro x'
      simpa [show x + (x' - x) = x' by abel] using h_expansion (x' - x)
    have h_o1 := (isLittleO_inner_matVec M hM).const_mul_left (1 / 2 : ℝ)
    have h_tendsto : Filter.Tendsto (fun x' => x' - x) (nhds x) (nhds 0) := by
      have h2 : Filter.Tendsto (fun x' : EuclideanSpace ℝ ι => x' - x)
          (nhds x) (nhds (x - x)) := (continuous_id.sub continuous_const).tendsto x
      simpa using h2
    have h_o2 := h_o1.comp_tendsto h_tendsto
    exact Asymptotics.IsLittleO.congr_left h_o2 (fun x' => (h_expansion_x' x').symm)
  exact h_grad

/-- The gradient of the tilted loss `quadraticLoss M r + lambda * inner ones`. -/
lemma gradient_tiltedLoss
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (x : EuclideanSpace ℝ ι) :
    gradient (tiltedLoss M r lambda) x =
      euclideanOf (fun i => (M.mulVec x) i - r i + lambda) :=
  (hasGradientAt_tiltedLoss M r lambda hM x).gradient

/-- The exact coordinatewise energy-dissipation identity for the positive effective field. -/
lemma inner_tiltedGradient_positiveEffectiveVectorField
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : EuclideanSpace ℝ ι) :
    inner ℝ (euclideanOf fun i => (matVec M x) i - r i + lambda)
        (positiveEffectiveVectorField M r lambda x) =
      ∑ i, -4 * x i * ((matVec M x) i - r i + lambda) ^ 2 := by
  dsimp [positiveEffectiveVectorField, euclideanOf]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/-- The positive effective field is a descent direction for the tilted loss at nonnegative `x`. -/
lemma inner_tiltedGradient_positiveEffectiveVectorField_nonpos
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) :
    inner ℝ (euclideanOf fun i => (matVec M x) i - r i + lambda)
        (positiveEffectiveVectorField M r lambda x) ≤ 0 := by
  rw [inner_tiltedGradient_positiveEffectiveVectorField]
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hx i)) (sq_nonneg _)

omit [Fintype ι] in
/-- The positive effective parameter `u(t)²` is coordinatewise nonnegative. -/
lemma posEffectiveParameter_nonnegative
    (u : ℝ → EuclideanSpace ℝ ι) (t : ℝ) :
    Nonnegative (posEffectiveParameter u t) := by
  intro i
  dsimp [posEffectiveParameter, coordinateSquare, euclideanOf]
  exact mul_self_nonneg (u t i)

/-- Evaluating the tilted loss at `u²` gives the positive-DLN objective at `u`. -/
lemma tiltedLoss_coordinateSquare_eq_posDlnObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (u : EuclideanSpace ℝ ι) :
    tiltedLoss M r lambda (coordinateSquare u) = posDlnObjective M r lambda u := by
  dsimp [tiltedLoss, posDlnObjective]
  congr 1
  rw [← real_inner_self_eq_norm_sq]
  dsimp [ones, coordinateSquare, euclideanOf]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [dotProduct]
  simp

/-- The weight-space positive-DLN objective decreases along its gradient flow. -/
lemma posDlnObjective_antitone_along_pos_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) (hM : M.IsSymm) :
    Antitone (fun t => posDlnObjective M r lambda (u t)) := by
  have h_differentiable : Differentiable ℝ (posDlnObjective M r lambda) :=
    fun x => (hasGradientAt_posDlnObjective M r lambda hM x).differentiableAt
  have h_gradient_flow : ConvexOpt.GFTrajectory (posDlnObjective M r lambda)
      (Real.sqrt ε • α) u :=
    { init := hu.init
      cont_diff := hu.cont_diff
      ode := fun t => by
        simpa only [posDlnVectorField] using hu.ode t }
  apply antitone_of_hasDerivAt_nonpos
    (f' := fun t => -‖gradient (posDlnObjective M r lambda) (u t)‖ ^ 2)
  · intro t
    convert ConvexOpt.gf_monotone_decrease h_differentiable h_gradient_flow t using 1
    rfl
  · intro t
    exact neg_nonpos.mpr (sq_nonneg _)

/--
Mirror-flow formulation of the positive-DLN dynamics, packaged with the reusable
predicate `IsEntropyMirrorFlow`.

Informal proof reference: `docs/Lasso.md`, Section 4.2, Eq. (4.1).
This is the same chain-rule computation as `dln_is_mirror_flow`, but stated
using the local API for `entropyMirrorGradient` and `tiltedLoss`.
-/
theorem pos_dln_is_entropy_mirror_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0) (hM : M.IsSymm) :
    IsEntropyMirrorFlow M r lambda (fun t => posEffectiveParameter u t) := by
  intro t
  have hd := dln_is_mirror_flow M r lambda ε α u hu hu_pos hM t
  dsimp [IsEntropyMirrorFlow, entropyMirrorGradient]
  have h_grad := gradient_tiltedLoss M r lambda hM (posEffectiveParameter u t)
  rw [h_grad]
  exact hd

/--
Lemma 4.2 from `docs/Lasso.md`: the tilted loss is nonincreasing along the
positive-DLN effective trajectory.

Informal proof reference: Section 4.3, Lemma 4.2. Differentiate
`\widetilde L(x(t))` and use Eq. (3.3) to obtain
`-4 * Σᵢ xᵢ(t) * (∂ᵢ \widetilde L(x(t)))² ≤ 0`.
-/
theorem tiltedLoss_antitone_along_pos_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) (hM : M.IsSymm) :
    Antitone (fun t => tiltedLoss M r lambda (posEffectiveParameter u t)) := by
  intro s t hst
  simpa only [posEffectiveParameter, tiltedLoss_coordinateSquare_eq_posDlnObjective] using
    posDlnObjective_antitone_along_pos_flow M r lambda ε α u hu hM hst

/-- The effective parameter starts at `ε • α²` along a positive-DLN flow. -/
lemma posEffectiveParameter_zero_eq_smul_coordinateSquare
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) (hε : 0 ≤ ε) :
    posEffectiveParameter u 0 = ε • coordinateSquare α := by
  dsimp [posEffectiveParameter]
  rw [show u 0 = Real.sqrt ε • α from hu.init]
  ext i
  dsimp [coordinateSquare, euclideanOf]
  calc
    Real.sqrt ε * α i * (Real.sqrt ε * α i) =
        (Real.sqrt ε * Real.sqrt ε) * (α i * α i) := by ring
    _ = ε * (α i * α i) := by rw [Real.mul_self_sqrt hε]

/--
Lemma 4.3 from `docs/Lasso.md`: in the non-coercive case, energy decrease still
controls the image `M xᵋ(t)`.

Informal proof reference: Section 4.3, Lemma 4.3. Choose `y` with `M y = r`.
Completing the square controls the quadratic form of `xᵋ(t) - y` by the
initial energy. Semidefinite Cauchy--Schwarz, applied coordinatewise, then
bounds `‖M (xᵋ(t) - y)‖²` by the trace of `M` times that quadratic form.
-/
theorem pos_trajectory_matVec_uniform_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (α : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r 0) (_hα : NonzeroCoordinates α)
    (hu : ∀ ε > 0, posDlnGradientFlow M r 0 ε α (u ε)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ,
        0 ≤ t → ‖matVec M (posEffectiveParameter (u ε) t)‖ ≤ C := by
  classical
  obtain ⟨y, hy⟩ := hdata.r_mem_span
  let a := coordinateSquare α
  let K := (1 / 2 : ℝ) * inner ℝ a (matVec M a) + |inner ℝ r a|
  let Q := 2 * K + |inner ℝ y (matVec M y)|
  let A := (∑ i, M i i) * Q
  refine ⟨A + 2 + ‖r‖, ?_, ?_⟩
  · have hK : 0 ≤ K := add_nonneg
      (mul_nonneg (by norm_num) (hdata.psd.nonneg a)) (abs_nonneg _)
    have hQ : 0 ≤ Q := add_nonneg (mul_nonneg (by norm_num) hK) (abs_nonneg _)
    have hA : 0 ≤ A := mul_nonneg hdata.psd.trace_nonnegative hQ
    positivity
  · intro ε hε hε_one t ht
    have hflow := hu ε hε
    have hx0 : posEffectiveParameter (u ε) 0 = ε • a := by
      simpa [a] using
        posEffectiveParameter_zero_eq_smul_coordinateSquare M r 0 ε α (u ε) hflow hε.le
    have henergy : quadraticLoss M r (posEffectiveParameter (u ε) t) ≤ K := by
      have hmono :=
        tiltedLoss_antitone_along_pos_flow M r 0 ε α (u ε) hflow hdata.psd.symm ht
      have hinit : quadraticLoss M r (ε • a) ≤ K := by
        rw [quadraticLoss_smul]
        have haa : 0 ≤ inner ℝ a (matVec M a) := hdata.psd.nonneg a
        have hε_sq : ε ^ 2 ≤ 1 := by nlinarith
        have hquad :
            (1 / 2 : ℝ) * ε ^ 2 * inner ℝ a (matVec M a) ≤
              (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
          nlinarith
        have hlin₁ : ε * (-inner ℝ r a) ≤ ε * |inner ℝ r a| :=
          mul_le_mul_of_nonneg_left (neg_le_abs _) hε.le
        have hlin₂ : ε * |inner ℝ r a| ≤ |inner ℝ r a| := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hε_one (abs_nonneg (inner ℝ r a))
        dsimp [K]
        nlinarith
      have hmono_loss :
          quadraticLoss M r (posEffectiveParameter (u ε) t) ≤
            quadraticLoss M r (ε • a) := by
        simpa [tiltedLoss, hx0] using hmono
      exact hmono_loss.trans hinit
    let x := posEffectiveParameter (u ε) t
    let z := x - y
    have hz_energy : inner ℝ z (matVec M z) ≤ Q := by
      rw [quadraticLoss_complete_square M r x y hdata.psd.symm hy]
      have hxy : quadraticLoss M r x ≤ K := henergy
      dsimp [Q]
      linarith [le_abs_self (inner ℝ y (matVec M y))]
    have hK : 0 ≤ K := add_nonneg
      (mul_nonneg (by norm_num) (hdata.psd.nonneg a)) (abs_nonneg _)
    have hQ : 0 ≤ Q := add_nonneg (mul_nonneg (by norm_num) hK) (abs_nonneg _)
    have htrace : 0 ≤ ∑ i, M i i := hdata.psd.trace_nonnegative
    have hA : 0 ≤ A := mul_nonneg htrace hQ
    have hz_sq : ‖matVec M z‖ ^ 2 ≤ A :=
      (matVec_norm_sq_le_trace_mul M hdata.psd z).trans
        (mul_le_mul_of_nonneg_left hz_energy htrace)
    have hz_norm : ‖matVec M z‖ ≤ A + 1 := by
      nlinarith [sq_nonneg (‖matVec M z‖ - (1 / 2 : ℝ))]
    have hx_decomp : matVec M x = matVec M z + r := by
      rw [show x = z + y by simp [z], matVec_add, hy]
    calc
      ‖matVec M (posEffectiveParameter (u ε) t)‖ = ‖matVec M z + r‖ := by
        rw [show posEffectiveParameter (u ε) t = x from rfl, hx_decomp]
      _ ≤ ‖matVec M z‖ + ‖r‖ := norm_add_le _ _
      _ ≤ A + 2 + ‖r‖ := by linarith

/--
Coordinatewise identity connecting an `entropyBregman` term to the Kullback--Leibler
generator `InformationTheory.klFun t = t * log t + 1 - t`: `a log(a/b) - a + b = b * klFun (a/b)`.

This is the standard fact that the (unnormalized, univariate) relative entropy
`a log(a/b) - a + b` is `b` times the KL generator evaluated at the ratio `a/b`; it lets us
reuse Mathlib's `klFun_nonneg`/`klFun_eq_zero_iff` (built from `strictConvexOn_klFun`) instead of
reproving Gibbs' inequality from scratch.
-/
private lemma entropyBregmanTerm_eq_mul_klFun {a b : ℝ} (hb : b ≠ 0) :
    a * Real.log (a / b) - a + b = b * InformationTheory.klFun (a / b) := by
  dsimp [InformationTheory.klFun]
  field_simp
  ring

/-- Each coordinate of the entropy Bregman divergence is nonnegative once the base point `b`
is positive; the numerator `a` need only be nonnegative (this is the boundary case `a = 0`,
extended by continuity via `Real.log 0 = 0`, mentioned in `docs/Lasso.md` after Lemma 4.4). -/
private lemma entropyBregmanTerm_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.log (a / b) - a + b := by
  rw [entropyBregmanTerm_eq_mul_klFun hb.ne']
  exact mul_nonneg hb.le (InformationTheory.klFun_nonneg (div_nonneg ha hb.le))

/-- The equality case of `entropyBregmanTerm_nonneg`: the term vanishes exactly at `a = b`. -/
private lemma entropyBregmanTerm_eq_zero_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log (a / b) - a + b = 0 ↔ a = b := by
  rw [entropyBregmanTerm_eq_mul_klFun hb.ne', mul_eq_zero, or_iff_right hb.ne',
    InformationTheory.klFun_eq_zero_iff (div_nonneg ha hb.le)]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    exact div_self hb.ne'

/--
The entropy Bregman divergence is nonnegative as soon as the base point `y` is (coordinatewise)
positive; the first argument `x` need only be nonnegative.

This is the natural generality for `entropyBregman`: along the positive-DLN trajectory the
reference point `y = x^ε(0)` is always positive, but points being compared against it (e.g.
arbitrary feasible points of a Bregman projection) may have zero coordinates, handled via the
`docs/Lasso.md` continuity convention `0 log 0 = 0`.
-/
lemma entropyBregman_nonneg_of_nonneg
    (x y : EuclideanSpace ℝ ι) (hx : Nonnegative x) (hy : Positive y) :
    0 ≤ entropyBregman x y := by
  dsimp [entropyBregman]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  exact entropyBregmanTerm_nonneg (hx i) (hy i)

/--
The Bregman divergence associated with the entropy mirror map is nonnegative.

Informal proof reference: `docs/Lasso.md`, Section 4.2 after Eq. (4.2).
It follows from convexity of `h`; in coordinates this is the usual nonnegativity
of relative entropy. Concretely, coordinate `i` contributes
`x_i log(x_i/y_i) - x_i + y_i = y_i * klFun(x_i/y_i) ≥ 0`, where `klFun t = t log t + 1 - t`
is Mathlib's Kullback--Leibler generator, nonnegative on `[0,∞)` by strict convexity
(`InformationTheory.klFun_nonneg`).
-/
theorem entropyBregman_nonnegative
    (x y : EuclideanSpace ℝ ι) (hx : Positive x) (hy : Positive y) :
    0 ≤ entropyBregman x y :=
  entropyBregman_nonneg_of_nonneg x y (fun i => (hx i).le) hy

/--
The entropy Bregman divergence vanishes at `(x, y)` (with `x` nonnegative and `y` positive)
exactly when `x = y`. This is the strict-convexity / uniqueness half of Gibbs' inequality,
used to identify the unique minimizer of a Bregman projection.
-/
lemma entropyBregman_eq_zero_iff
    (x y : EuclideanSpace ℝ ι) (hx : Nonnegative x) (hy : Positive y) :
    entropyBregman x y = 0 ↔ x = y := by
  constructor
  · intro h
    dsimp [entropyBregman] at h
    have hsum : (∑ i, (x i * Real.log (x i / y i) - x i + y i)) = 0 := by linarith
    have hterm : ∀ i ∈ Finset.univ, x i * Real.log (x i / y i) - x i + y i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => entropyBregmanTerm_nonneg (hx i) (hy i))).1 hsum
    ext i
    exact (entropyBregmanTerm_eq_zero_iff (hx i) (hy i)).1 (hterm i (Finset.mem_univ i))
  · intro h
    subst h
    dsimp [entropyBregman]
    have : ∀ i, x i * Real.log (x i / x i) - x i + x i = 0 := by
      intro i
      rcases (hx i).lt_or_eq with h0 | h0
      · rw [div_self h0.ne']
        simp
      · simp [← h0]
    simp only [this, Finset.sum_const_zero, mul_zero]

/-- Coordinate projection out of `EuclideanSpace ℝ ι` is continuous. -/
private lemma continuous_apply_euclidean (i : ι) :
    Continuous (fun x : EuclideanSpace ℝ ι => x i) :=
  (continuous_apply i).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous

/--
The positive effective parameter trajectory is continuous in time.

Reused from the derivative already computed in `pos_effective_parameter_hasDerivAt`: a
`HasDerivAt` fact at every point of `ℝ` gives continuity for free via `HasDerivAt.continuousAt`.
-/
private lemma continuous_posEffectiveParameter
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r 0 ε α u) (hM : M.IsSymm) :
    Continuous (posEffectiveParameter u) :=
  continuous_iff_continuousAt.mpr
    (fun τ => (pos_effective_parameter_hasDerivAt M r 0 ε α u hu hM τ).continuousAt)

/--
Chain rule for `matVec M` along a curve, proved coordinatewise (the same
`WithLp`-unfolding pattern as `hasDerivAt_coordinateSquare`).
-/
private lemma hasDerivAt_matVec_comp
    (M : Matrix ι ι ℝ) (g : ℝ → EuclideanSpace ℝ ι) (g' : EuclideanSpace ℝ ι) (t : ℝ)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun τ => matVec M (g τ)) (matVec M g') t := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have h1 : HasDerivAt (fun τ => e (g τ)) (e g') t := e.hasFDerivAt.comp_hasDerivAt t hg
  dsimp [matVec, euclideanOf]
  have hd_pi : HasDerivAt (fun τ => M.mulVec (e (g τ))) (M.mulVec (e g')) t := by
    apply hasDerivAt_pi.2
    intro i
    dsimp [Matrix.mulVec, dotProduct]
    have hterm : ∀ j, HasDerivAt (fun τ => M i j * e (g τ) j) (M i j * e g' j) t := fun j =>
      (hasDerivAt_pi.1 h1 j).const_mul (M i j)
    exact HasDerivAt.fun_sum (fun j _ => hterm j)
  exact e.symm.hasFDerivAt.comp_hasDerivAt t hd_pi

/--
Fundamental theorem of calculus for the integrated positive-effective trajectory:
`d/dt ∫₀ᵗ x(v) dv = x(t)`, taken coordinatewise via
`intervalIntegral.integral_hasDerivAt_right`.
-/
private lemma hasDerivAt_posIntegratedTrajectory
    (u : ℝ → EuclideanSpace ℝ ι) (hcont : Continuous (posEffectiveParameter u)) (t : ℝ) :
    HasDerivAt (fun τ => posIntegratedTrajectory u τ) (posEffectiveParameter u t) t := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  dsimp [posIntegratedTrajectory, euclideanOf]
  have h_pi : HasDerivAt (fun τ => (fun i => ∫ v in (0:ℝ)..τ, posEffectiveParameter u v i))
      (fun i => posEffectiveParameter u t i) t := by
    apply hasDerivAt_pi.2
    intro i
    have hcont_i : Continuous (fun v => posEffectiveParameter u v i) :=
      (continuous_apply_euclidean i).comp hcont
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont_i.intervalIntegrable 0 t)
      (hcont_i.stronglyMeasurableAtFilter _ _)
      hcont_i.continuousAt
  exact e.symm.hasFDerivAt.comp_hasDerivAt t h_pi

/--
The key identity behind Lemma 4.4's optimality condition: the mirror-map gradient increment
along the (λ = 0) positive-DLN trajectory is `t • r - M (integrated trajectory)`.

Informal proof: let
`F(τ) = ∇h(x(τ)) - τ • r + M z(τ)`, where `z(τ) = ∫₀^τ x(v) dv`.
By the mirror-flow equation (`pos_dln_is_entropy_mirror_flow` at `λ = 0`),
`d∇h(x(τ))/dτ = -∇ℓ(x(τ)) = r - M x(τ)`; by the Fundamental Theorem of Calculus,
`dz(τ)/dτ = x(τ)`, so `d(M z(τ))/dτ = M x(τ)` by linearity of `M`. Hence `F'(τ) = 0`
for every `τ`, so `F` is constant, i.e. `F(t) = F(0)`. Since `z(0) = 0`, this rearranges to
`∇h(x(t)) - ∇h(x(0)) = t • r - M z(t)`.
-/
private lemma entropyMirrorGradient_sub_eq
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r 0 ε α u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0)
    (hM : M.IsSymm) (t : ℝ) :
    entropyMirrorGradient (posEffectiveParameter u t) -
        entropyMirrorGradient (posEffectiveParameter u 0) =
      t • r - matVec M (posIntegratedTrajectory u t) := by
  set F : ℝ → EuclideanSpace ℝ ι := fun τ =>
    entropyMirrorGradient (posEffectiveParameter u τ) - τ • r +
      matVec M (posIntegratedTrajectory u τ) with hF_def
  have hcont : Continuous (posEffectiveParameter u) :=
    continuous_posEffectiveParameter M r ε α u hu hM
  have hderiv : ∀ τ : ℝ, HasDerivAt F 0 τ := by
    intro τ
    have h1 : HasDerivAt (fun τ => entropyMirrorGradient (posEffectiveParameter u τ))
        (r - matVec M (posEffectiveParameter u τ)) τ := by
      have hmf := pos_dln_is_entropy_mirror_flow M r 0 ε α u hu hu_pos hM τ
      dsimp [IsEntropyMirrorFlow] at hmf
      rw [gradient_tiltedLoss M r 0 hM (posEffectiveParameter u τ)] at hmf
      convert hmf using 1
      ext i
      dsimp [matVec, euclideanOf]
      ring
    have h2 : HasDerivAt (fun τ : ℝ => τ • r) r τ := by
      simpa using (hasDerivAt_id τ).smul_const r
    have h3 : HasDerivAt (fun τ => matVec M (posIntegratedTrajectory u τ))
        (matVec M (posEffectiveParameter u τ)) τ :=
      hasDerivAt_matVec_comp M (posIntegratedTrajectory u) (posEffectiveParameter u τ) τ
        (hasDerivAt_posIntegratedTrajectory u hcont τ)
    have hsum := (h1.sub h2).add h3
    have hval : (r - matVec M (posEffectiveParameter u τ)) - r +
        matVec M (posEffectiveParameter u τ) = 0 := by abel
    rw [hval] at hsum
    exact hsum
  have hconst : F t - F 0 = ∫ _τ in (0:ℝ)..t, (0 : EuclideanSpace ℝ ι) :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      intervalIntegrable_const).symm
  simp only [intervalIntegral.integral_zero, sub_eq_zero] at hconst
  -- `hconst : F t = F 0`
  have hz : posIntegratedTrajectory u 0 = 0 := by
    ext i
    simp [posIntegratedTrajectory, euclideanOf]
  have hF0 : F 0 = entropyMirrorGradient (posEffectiveParameter u 0) := by
    change entropyMirrorGradient (posEffectiveParameter u 0) - (0 : ℝ) • r +
        matVec M (posIntegratedTrajectory u 0) = entropyMirrorGradient (posEffectiveParameter u 0)
    rw [hz]
    have hmz : matVec M (0 : EuclideanSpace ℝ ι) = 0 := by
      ext i
      simp [matVec, euclideanOf]
    simp [hmz]
  have hFt : F t = entropyMirrorGradient (posEffectiveParameter u t) - t • r +
      matVec M (posIntegratedTrajectory u t) := rfl
  rw [hFt, hF0] at hconst
  rw [← hconst]
  abel

/--
The mirror-map gradient increment along a (λ = 0) positive-DLN trajectory lies in the
column span of `M`. This is the first-order optimality condition of Lemma 4.4 of
`docs/Lasso.md`.
-/
private lemma entropyMirrorGradient_sub_mem_span
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r 0 ε α u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0)
    (hM : M.IsSymm) (hr : InMatrixSpan M r) (t : ℝ) :
    InMatrixSpan M
      (entropyMirrorGradient (posEffectiveParameter u t) -
        entropyMirrorGradient (posEffectiveParameter u 0)) := by
  obtain ⟨y₀, hy₀⟩ := hr
  refine ⟨t • y₀ - posIntegratedTrajectory u t, ?_⟩
  rw [matVec_sub, matVec_smul_eq, hy₀]
  rw [entropyMirrorGradient_sub_eq M r ε α u hu hu_pos hM t]

/--
Coordinatewise three-point identity for the (unnormalized) entropy Bregman term
`a ↦ a log(a/b) - a + b`: this is the standard Bregman "law of cosines"
`D(z,y) - D(x,y) - D(z,x) = ⟨∇h(x) - ∇h(y), z - x⟩`, written out coordinatewise with
`∇h(a) = (1/4) log a` (the `1/4` is applied later, in `entropyBregman_three_point`).
The `z = 0` case is handled separately since `Real.log (0/y)` does not literally split as
`Real.log 0 - Real.log y` in Lean, but the `0 *` factor makes the term vanish regardless.
-/
private lemma bregmanThreePointTerm
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 ≤ z) :
    (z * Real.log (z / y) - z + y) - (x * Real.log (x / y) - x + y) -
        (z * Real.log (z / x) - z + x) =
      (Real.log x - Real.log y) * (z - x) := by
  rcases hz.eq_or_lt with hz0 | hz0
  · simp [← hz0, Real.log_div hx.ne' hy.ne']
    ring
  · rw [Real.log_div hz0.ne' hy.ne', Real.log_div hx.ne' hy.ne', Real.log_div hz0.ne' hx.ne']
    ring

omit [Fintype ι] in
/-- The difference of two entropy-mirror gradients as a single `euclideanOf`. -/
private lemma entropyMirrorGradient_sub_eq_euclideanOf (x y : EuclideanSpace ℝ ι) :
    entropyMirrorGradient x - entropyMirrorGradient y =
      euclideanOf (fun i => (1 / 4 : ℝ) * (Real.log (x i) - Real.log (y i))) := by
  ext i
  dsimp [entropyMirrorGradient, euclideanOf]
  ring

/-- Coordinate expansion of the inner product against a difference of mirror gradients. -/
private lemma inner_entropyMirrorGradient_sub
    (x y h : EuclideanSpace ℝ ι) :
    inner ℝ (entropyMirrorGradient x - entropyMirrorGradient y) h =
      ∑ i, (1 / 4 : ℝ) * (Real.log (x i) - Real.log (y i)) * h i := by
  rw [entropyMirrorGradient_sub_eq_euclideanOf]
  dsimp [euclideanOf]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/--
The three-point (Bregman "law of cosines") identity for `entropyBregman`:
`D(z,y) - D(x,y) - D(z,x) = ⟨∇h(x) - ∇h(y), z - x⟩`.

Informal proof: expand both sides coordinatewise using `bregmanThreePointTerm` and
`inner_entropyMirrorGradient_sub`. This is the standard three-point identity for Bregman
divergences (see e.g. Bregman 1967 or Chen–Teboulle 1993, "Convergence Analysis of Proximal-Like
Minimization Algorithms Using Bregman Functions"), specialized to the entropy mirror map.
-/
private lemma entropyBregman_three_point
    (x y z : EuclideanSpace ℝ ι) (hx : Positive x) (hy : Positive y) (hz : Nonnegative z) :
    entropyBregman z y - entropyBregman x y - entropyBregman z x =
      inner ℝ (entropyMirrorGradient x - entropyMirrorGradient y) (z - x) := by
  rw [inner_entropyMirrorGradient_sub]
  dsimp [entropyBregman]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := bregmanThreePointTerm (hx i) (hy i) (hz i)
  change (1 / 4 : ℝ) * (z i * Real.log (z i / y i) - z i + y i) -
      (1 / 4 : ℝ) * (x i * Real.log (x i / y i) - x i + y i) -
      (1 / 4 : ℝ) * (z i * Real.log (z i / x i) - z i + x i) =
      (1 / 4 : ℝ) * (Real.log (x i) - Real.log (y i)) * (z - x) i
  rw [show (z - x) i = z i - x i from rfl]
  linear_combination (1 / 4 : ℝ) * h

/--
Lemma 4.4 from `docs/Lasso.md`: the positive-DLN trajectory is the Bregman
projection of its initialization onto the affine fiber with the same `M x`.

Informal proof reference: Section 4.3, Lemma 4.4. The first-order optimality
condition for the constrained Bregman projection is
`∇h(x(t)) - ∇h(x(0)) ∈ Span M`; integrating the mirror-flow equation shows this
condition for the DLN trajectory. Strict convexity gives uniqueness.

Note on hypotheses: `docs/Lasso.md` proves this lemma only for `λ = 0` (see the discussion
preceding Lemma 4.3 in Section 4.3, "We now assume that we are in this case"), so this
theorem fixes `lambda = 0` via `ProblemData M r 0` rather than taking a free `lambda`
(matching `pos_trajectory_matVec_uniform_bound`, the Lean statement of Lemma 4.3). The
uniqueness clause also requires `y` to lie in the feasible set: `IsMinOn f s y` alone only
says `f y ≤ f x` for `x ∈ s` and does not imply `y ∈ s` (e.g. `y = posEffectiveParameter u 0`
trivially satisfies `IsMinOn` since `entropyBregman` is everywhere nonnegative and vanishes
there), so without a membership hypothesis the uniqueness claim would be false.
-/
theorem bregman_projection_characterization
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r 0)
    (hu : posDlnGradientFlow M r 0 ε α u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0)
    (t : ℝ) :
    IsMinOn
        (fun x => entropyBregman x (posEffectiveParameter u 0))
        {x | Nonnegative x ∧ matVec M x = matVec M (posEffectiveParameter u t)}
        (posEffectiveParameter u t) ∧
      ∀ y : EuclideanSpace ℝ ι,
        Nonnegative y → matVec M y = matVec M (posEffectiveParameter u t) →
        IsMinOn
          (fun x => entropyBregman x (posEffectiveParameter u 0))
          {x | Nonnegative x ∧ matVec M x = matVec M (posEffectiveParameter u t)}
          y →
        y = posEffectiveParameter u t := by
  have hM : M.IsSymm := hdata.psd.get_symm
  have hx_nonneg : Nonnegative (posEffectiveParameter u t) := posEffectiveParameter_nonnegative u t
  have hy0_nonneg : Nonnegative (posEffectiveParameter u 0) := posEffectiveParameter_nonnegative u 0
  have hx_pos : Positive (posEffectiveParameter u t) :=
    fun i => lt_of_le_of_ne (hx_nonneg i) (Ne.symm (hu_pos t i))
  have hy0_pos : Positive (posEffectiveParameter u 0) :=
    fun i => lt_of_le_of_ne (hy0_nonneg i) (Ne.symm (hu_pos 0 i))
  obtain ⟨w, hw⟩ :=
    entropyMirrorGradient_sub_mem_span M r ε α u hu hu_pos hM hdata.r_mem_span t
  have hcross : ∀ z : EuclideanSpace ℝ ι, matVec M z = matVec M (posEffectiveParameter u t) →
      inner ℝ (entropyMirrorGradient (posEffectiveParameter u t) -
        entropyMirrorGradient (posEffectiveParameter u 0)) (z - posEffectiveParameter u t) = 0 := by
    intro z hz
    rw [← hw, ← inner_matVec_comm_of_isSymm M hM w (z - posEffectiveParameter u t), matVec_sub, hz,
      sub_self]
    exact inner_zero_right w
  have hmin : ∀ z : EuclideanSpace ℝ ι, Nonnegative z →
      matVec M z = matVec M (posEffectiveParameter u t) →
      entropyBregman (posEffectiveParameter u t) (posEffectiveParameter u 0) ≤
        entropyBregman z (posEffectiveParameter u 0) := by
    intro z hz_nonneg hz_eq
    have h3pt := entropyBregman_three_point (posEffectiveParameter u t) (posEffectiveParameter u 0)
      z hx_pos hy0_pos hz_nonneg
    rw [hcross z hz_eq] at h3pt
    have hnn : 0 ≤ entropyBregman z (posEffectiveParameter u t) :=
      entropyBregman_nonneg_of_nonneg z (posEffectiveParameter u t) hz_nonneg hx_pos
    linarith [h3pt, hnn]
  refine ⟨isMinOn_iff.mpr fun z hz => hmin z hz.1 hz.2, ?_⟩
  intro y hy_nonneg hy_eq hy_min
  rw [isMinOn_iff] at hy_min
  have hxy : entropyBregman y (posEffectiveParameter u 0) ≤
      entropyBregman (posEffectiveParameter u t) (posEffectiveParameter u 0) :=
    hy_min (posEffectiveParameter u t) ⟨hx_nonneg, rfl⟩
  have hyx : entropyBregman (posEffectiveParameter u t) (posEffectiveParameter u 0) ≤
      entropyBregman y (posEffectiveParameter u 0) := hmin y hy_nonneg hy_eq
  have heq : entropyBregman y (posEffectiveParameter u 0) =
      entropyBregman (posEffectiveParameter u t) (posEffectiveParameter u 0) :=
    le_antisymm hxy hyx
  have h3pt := entropyBregman_three_point (posEffectiveParameter u t) (posEffectiveParameter u 0)
    y hx_pos hy0_pos hy_nonneg
  rw [hcross y hy_eq, heq] at h3pt
  have hzero : entropyBregman y (posEffectiveParameter u t) = 0 := by linarith [h3pt]
  exact (entropyBregman_eq_zero_iff y (posEffectiveParameter u t) hy_nonneg hx_pos).1 hzero

/--
Lemma 4.5 from `docs/Lasso.md`: Bregman projections on nonnegative affine
fibers have a norm bound polynomial in the fiber value.

Informal proof reference: Section 4.3, Lemma 4.5.  Compare the entropy
Bregman objective at its minimizer with a minimum-norm feasible nonnegative
solution supplied by Lemma 4.7.  The coordinate expression for the Bregman
divergence is sandwiched between a linear lower bound and a quadratic upper
bound in `‖x‖`, uniformly for small `ε`.
-/
theorem bregman_projection_fiber_norm_bound
    (M : Matrix ι ι ℝ) (α : EuclideanSpace ℝ ι) (hα : NonzeroCoordinates α) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ y : EuclideanSpace ℝ ι,
          (∃ u : EuclideanSpace ℝ ι, Nonnegative u ∧ matVec M u = y) →
          ∀ x : EuclideanSpace ℝ ι,
            IsMinOn
              (fun z => entropyBregman z (ε • coordinateSquare α))
              {z | Nonnegative z ∧ matVec M z = y}
              x →
            ‖x‖ ≤ C * (1 + ‖y‖ ^ 2) := by
  sorry

/--
Proposition 4.1 from `docs/Lasso.md`: the positive effective trajectories are
uniformly bounded in time for all sufficiently small initializations.

Informal proof reference: Section 4.3, Proposition 4.1. Lemma 4.2 bounds
`\widetilde L`; Lemma 4.3 bounds `M x(t)` when coercivity is unavailable; Lemma
4.4 turns the trajectory into a Bregman projection; Lemma 4.5 bounds that
projection by a polynomial in `‖M x(t)‖`.
-/
theorem pos_trajectory_uniform_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hα : NonzeroCoordinates α)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε α (u ε)) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ t : ℝ,
        0 ≤ t → ‖posEffectiveParameter (u ε) t‖ ≤ C := by
  sorry

end Lasso

end
