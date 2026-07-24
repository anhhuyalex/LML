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
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped Matrix

/-!
# Mirror Flow Interpretation of Diagonal Linear Networks

This file formalizes the mirror flow interpretation of the DLN dynamics.
-/

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
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
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

/--
The gradient of the positive DLN objective function.

Informal proof reference: `docs/Lasso.md`, Section 3, Eq. (3.3).
The objective is $L(u) = \ell(u^2) + \lambda\|u\|^2$ where
$\ell(x) = \frac{1}{2}\langle x, Mx \rangle - \langle r, x \rangle$.
Taking the differential, we have $d\ell(v) = \frac{1}{2}(\langle v, Mx \rangle + \langle x, Mv \rangle) - \langle r, v \rangle$.
Since $M$ is assumed to be symmetric, $\langle x, Mv \rangle = \langle Mx, v \rangle$.
Thus the gradient is $\nabla \ell(x) = Mx - r$.
Applying the chain rule with respect to $u$, we obtain
$\frac{\partial L}{\partial u_i}
  = 2 u_i \frac{\partial \ell}{\partial x_i} + 2 \lambda u_i
  = 2 u_i ( (M x)_i - r_i + \lambda)$.
-/
lemma gradient_posDlnObjective
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (u : EuclideanSpace ℝ ι) :
    gradient (fun u' => posDlnObjective M r lambda u') u =
      euclideanOf
        (fun i => 2 * u i * ((matVec M (coordinateSquare u)) i - r i + lambda)) := by
  have h_expansion : ∀ x' : EuclideanSpace ℝ ι,
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
    intro x'
    -- We organize the algebra around the displacement `h = x' - u`, the base
    -- effective parameter `y = u²`, and the effective increment
    -- `a = x'² - u² = 2*u*h + h²`.
    let h : EuclideanSpace ℝ ι := x' - u
    let y : EuclideanSpace ℝ ι := coordinateSquare u
    let a : EuclideanSpace ℝ ι :=
      euclideanOf fun i ↦ 2 * u i * h i + h i * h i

    -- Step 1: coordinatewise square expansion.  Prove by `ext i`, unfolding
    -- `coordinateSquare`, `euclideanOf`, `h`, `y`, and `a`, then `ring`.
    have h_square_increment : coordinateSquare x' = y + a := by
      -- Work coordinatewise; after unfolding `h`, `y`, `a`, and
      -- `coordinateSquare`, this is the scalar identity
      -- `(u_i + h_i)^2 = u_i^2 + 2*u_i*h_i + h_i^2` with `h_i = x'_i-u_i`.
      ext i
      simp [coordinateSquare, euclideanOf, h, y, a]
      ring

    -- Step 2: Taylor expansion of the quadratic loss in the effective variable.
    -- After unfolding `quadraticLoss`, expand bilinearly.  The only non-ring
    -- point is the use of `hM : M.IsSymm` to rewrite the cross-term
    -- `inner ℝ y (matVec M a)` as `inner ℝ a (matVec M y)`.
    have h_loss_expansion :
        quadraticLoss M r (y + a) - quadraticLoss M r y =
          inner ℝ (matVec M y - r) a +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
      -- First isolate the purely quadratic part.  This is the exact
      -- second-order expansion of `x ↦ (1/2) * ⟪x, Mx⟫` at `y` in the
      -- direction `a`.  The proof should unfold `matVec`, use linearity of
      -- matrix-vector multiplication, expand both inner-product arguments, and
      -- use `hM` to identify the two cross terms.
      have h_quad_increment :
          (1 / 2 : ℝ) * inner ℝ (y + a) (matVec M (y + a)) -
              (1 / 2 : ℝ) * inner ℝ y (matVec M y) =
            inner ℝ (matVec M y) a +
              (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
        -- Coordinate proof sketch:
        --   * show `matVec M (y + a) = matVec M y + matVec M a` by `ext i`;
        --   * expand with `inner_add_left` and `inner_add_right`;
        --   * prove `inner ℝ y (matVec M a) = inner ℝ (matVec M y) a`
        --     by expanding both sides as finite sums and rewriting with
        --     `hM.apply i j`;
        --   * finish the scalar arithmetic by `ring`.

        -- Matrix-vector multiplication is additive in the vector argument.
        -- A direct proof is coordinatewise: unfold `matVec`, `euclideanOf`,
        -- and `Matrix.mulVec`, then use `Finset.sum_add_distrib` and `mul_add`.
        have h_matVec_add : matVec M (y + a) = matVec M y + matVec M a := by
          -- It is enough to compare coordinates.  After unfolding the local
          -- wrapper `matVec`, this is exactly additivity of `Matrix.mulVec`.
          ext i
          simp [matVec, euclideanOf, Matrix.mulVec_add]

        -- Symmetry of `M` makes the bilinear cross-term symmetric.  The proof
        -- expands both Euclidean inner products as finite sums over coordinates,
        -- unfolds `matVec`, swaps the two finite sums, and rewrites matrix
        -- entries using `hM.apply i j : M j i = M i j`.
        have h_cross : inner ℝ y (matVec M a) = inner ℝ (matVec M y) a := by
          dsimp [matVec, euclideanOf]
          rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
          dsimp
          rw [star_trivial, star_trivial]
          have H0 : (M *ᵥ a.ofLp) ⬝ᵥ y.ofLp = y.ofLp ⬝ᵥ (M *ᵥ a.ofLp) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [H0]
          have H1 : y.ofLp ⬝ᵥ (M *ᵥ a.ofLp) = (y.ofLp ᵥ* M) ⬝ᵥ a.ofLp := Matrix.dotProduct_mulVec _ _ _
          rw [H1]
          have H2 : a.ofLp ⬝ᵥ (M *ᵥ y.ofLp) = (M *ᵥ y.ofLp) ⬝ᵥ a.ofLp := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [H2]
          congr 1
          ext i
          dsimp [Matrix.vecMul, Matrix.mulVec]
          apply Finset.sum_congr rfl
          intro j _
          change y.ofLp j * M j i = M i j * y.ofLp j
          have hm : M j i = M i j := (hM.apply j i).symm
          rw [hm]
          ring

        -- The other cross-term is just symmetry of the real inner product.
        have h_cross' : inner ℝ a (matVec M y) = inner ℝ (matVec M y) a := by
          simpa using (real_inner_comm (matVec M y) a)

        -- Now expand `⟪y+a, M(y+a)⟫` bilinearly, rewrite the two cross-terms,
        -- and finish with scalar algebra.
        rw [h_matVec_add]
        rw [inner_add_left, inner_add_right, inner_add_right]
        rw [h_cross, h_cross']
        ring
      -- The linear part of the loss contributes exactly `-⟪r,a⟫`.
      have h_linear_increment :
          - inner ℝ r (y + a) + inner ℝ r y = - inner ℝ r a := by
        -- Expand `inner ℝ r (y + a)` using additivity in the second argument.
        -- Then the two `inner ℝ r y` terms cancel.
        rw [inner_add_right]
        ring
      -- Rewrite the first-order term in the desired gradient form.
      have h_first_order_collect :
          inner ℝ (matVec M y) a - inner ℝ r a =
            inner ℝ (matVec M y - r) a := by
        -- This is additivity of the inner product in the first argument,
        -- equivalently `inner_sub_left`, followed by scalar arithmetic.
        exact (inner_sub_left _ _ _).symm
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
              rw [h_quad_increment, h_linear_increment]
        _ = inner ℝ (matVec M y - r) a +
                (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
              rw [← h_first_order_collect]
              ring

    -- Step 3: split the effective increment into its linear and quadratic parts.
    -- This is again coordinatewise and follows by `ext i; simp [a, h]; ring`.
    have h_a_decompose :
        a = (euclideanOf fun i ↦ 2 * u i * h i) + coordinateSquare h := by
      ext i
      simp [a, h, coordinateSquare, euclideanOf]

    -- Step 4: expand the weight-decay term around `u`.
    -- Use `x' = u + h`, the real inner-product identity
    -- `‖u+h‖² = ‖u‖² + 2*inner ℝ u h + ‖h‖²`, and then `ring`.
    have h_norm_expansion :
        lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2 -
            inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h =
          lambda * ‖h‖ ^ 2 := by
      sorry

    -- Step 5: identify the displayed linear term with the sum of the linear
    -- part of the loss expansion and the linear part of the norm expansion.
    -- This is a finite-coordinate calculation after unfolding `inner` on
    -- `EuclideanSpace` and `euclideanOf`.
    have h_linear_split :
        inner ℝ
            (euclideanOf fun i ↦
              2 * u i * ((matVec M y) i - r i + lambda)) h =
          inner ℝ (matVec M y - r) (euclideanOf fun i ↦ 2 * u i * h i) +
            inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h := by
      sorry

    -- Step 6: combine the previous expansions and cancel the linear terms.
    -- Rewrite `posDlnObjective`, use `h_square_increment` to replace
    -- `coordinateSquare x'` by `y+a`, use `h_loss_expansion`, `h_a_decompose`,
    -- `h_norm_expansion`, and `h_linear_split`, then finish with `ring_nf`.
    have h_combined :
        posDlnObjective M r lambda x' - posDlnObjective M r lambda u -
            inner ℝ
              (euclideanOf fun i ↦
                2 * u i * ((matVec M y) i - r i + lambda)) h =
          inner ℝ (matVec M y - r) (coordinateSquare h) +
            lambda * ‖h‖ ^ 2 +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
      sorry

    -- Unfold the bookkeeping abbreviations to recover the statement in the goal.
    simpa [h, y, a] using h_combined
  -- The right-hand side of `h_expansion` is quadratic (or higher order) in
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
    exact h_remainder_o.congr_left (fun x' => (h_expansion x').symm)
  exact h_grad.gradient

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
  have hd := hasDerivAt_coordinateSquare u t _ hu_ode
  exact hd.congr_deriv (by
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
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have hd_e : HasDerivAt (fun τ => e (posEffectiveParameter u τ)) (e (positiveEffectiveVectorField M r lambda (posEffectiveParameter u t))) t :=
    e.hasFDerivAt.comp_hasDerivAt t hd
  have h_pi : HasDerivAt (fun τ => (fun i => (1 / 4 : ℝ) * Real.log (posEffectiveParameter u τ i)))
      (fun i => -((M.mulVec (posEffectiveParameter u t)) i - r i + lambda)) t := by
    apply hasDerivAt_pi.2
    intro i
    have hd_i : HasDerivAt (fun τ => posEffectiveParameter u τ i)
      (e (positiveEffectiveVectorField M r lambda (posEffectiveParameter u t)) i) t := hasDerivAt_pi.1 hd_e i
    have hlog : HasDerivAt Real.log (posEffectiveParameter u t i)⁻¹ (posEffectiveParameter u t i) := Real.hasDerivAt_log (hu_pos t i)
    have hcomp := HasDerivAt.comp t hlog hd_i
    have hmul := HasDerivAt.const_mul (1 / 4 : ℝ) hcomp
    exact hmul.congr_deriv (by
      dsimp [positiveEffectiveVectorField, euclideanOf, matVec, e, ContinuousLinearEquiv.coe_coe, Equiv.toFun_as_coe, LinearEquiv.coe_coe, WithLp.linearEquiv, WithLp.equiv, WithLp.toLp]
      change (1 / 4 : ℝ) * ((posEffectiveParameter u t i)⁻¹ * (-4 * posEffectiveParameter u t i * (((M.mulVec (posEffectiveParameter u t)) i) - r i + lambda))) = -(((M.mulVec (posEffectiveParameter u t)) i) - r i + lambda)
      have hp := hu_pos t i
      field_simp [hp]
    )
  exact e.symm.hasFDerivAt.comp_hasDerivAt t h_pi

/--
The gradient of the tilted loss function.

Informal proof reference: `docs/Lasso.md`, Section 4.2.
The objective function is $\widetilde{L}(x) = \frac{1}{2}\langle x, Mx \rangle - \langle r, x \rangle + \lambda \langle \mathbf{1}, x \rangle$.
Taking the differential in the direction $v$:
1. For the quadratic term: $d(\frac{1}{2}\langle x, Mx \rangle)(v) = \frac{1}{2}(\langle v, Mx \rangle + \langle x, Mv \rangle)$.
   Since $M$ is symmetric, this equals $\langle Mx, v \rangle$.
2. For the linear term $-r$: $d(-\langle r, x \rangle)(v) = -\langle r, v \rangle$.
3. For the linear term $\lambda \mathbf{1}$: $d(\lambda \langle \mathbf{1}, x \rangle)(v) = \lambda \langle \mathbf{1}, v \rangle = \langle \lambda \mathbf{1}, v \rangle$.
Thus, by the Riesz representation theorem, the gradient is $Mx - r + \lambda \mathbf{1}$.
-/
lemma isLittleO_inner_matVec
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    (fun (h : EuclideanSpace ℝ ι) => inner ℝ h (matVec M h)) =o[nhds 0] fun h => h := by
  apply Asymptotics.IsLittleO.of_isBigOWith
  intro c hc
  rw [Asymptotics.isBigOWith_iff]
  have h_cont : Continuous (matVec M) := by
    have h_eq : matVec M = fun (x : EuclideanSpace ℝ ι) => ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv).symm (M.mulVec (x : ι → ℝ)) := rfl
    rw [h_eq]
    apply Continuous.comp ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv).symm.continuous
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    exact Continuous.mul continuous_const ((continuous_apply j).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous)
  have h_tendsto : Tendsto (fun h => ‖matVec M h‖) (nhds 0) (nhds 0) := by
    have h1 : Tendsto (matVec M) (nhds 0) (nhds (matVec M 0)) := h_cont.tendsto 0
    have h2 : matVec M 0 = 0 := by
      ext i
      simp [matVec, euclideanOf]
    rw [h2] at h1
    exact tendsto_norm_zero.comp h1
  have h_eventually : ∀ᶠ h in nhds 0, ‖matVec M h‖ < c := by
    apply (tendsto_order.1 h_tendsto).2 c hc
  apply h_eventually.mono
  intro h hh
  calc ‖inner ℝ h (matVec M h)‖
    _ ≤ ‖h‖ * ‖matVec M h‖ := norm_inner_le_norm h (matVec M h)
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left (le_of_lt hh) (norm_nonneg _)
    _ = c * ‖h‖ := mul_comm _ _

lemma gradient_tiltedLoss
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (x : EuclideanSpace ℝ ι) :
    gradient (tiltedLoss M r lambda) x =
      euclideanOf (fun i => (M.mulVec x) i - r i + lambda) := by
  have h_grad : HasGradientAt (tiltedLoss M r lambda)
      (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) x := by
    rw [hasGradientAt_iff_isLittleO]
    have h_expansion : ∀ h, tiltedLoss M r lambda (x + h) - tiltedLoss M r lambda x -
      inner ℝ (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) h =
        (1 / 2 : ℝ) * inner ℝ h (matVec M h) := by
      intro h
      dsimp [tiltedLoss, quadraticLoss]
      have h_M_add : matVec M (x + h) = matVec M x + matVec M h := by
        ext i
        dsimp [matVec, euclideanOf, Matrix.mulVec]
        have h_sum : (∑ j, M i j * (x j + h j)) = (∑ j, M i j * x j) + (∑ j, M i j * h j) := by
          simp [mul_add, Finset.sum_add_distrib]
        exact h_sum
      rw [h_M_add]
      have h_inner_M : inner ℝ (x + h) (matVec M x + matVec M h) =
          inner ℝ x (matVec M x) + inner ℝ x (matVec M h) + inner ℝ h (matVec M x) + inner ℝ h (matVec M h) := by
        rw [inner_add_left, inner_add_right, inner_add_right]
        ring
      rw [h_inner_M]
      have h_cross : inner ℝ x (matVec M h) = inner ℝ (matVec M x) h := by
        dsimp [matVec, euclideanOf]
        rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
        dsimp
        rw [star_trivial, star_trivial]
        have H0 : (M *ᵥ h.ofLp) ⬝ᵥ x.ofLp = x.ofLp ⬝ᵥ (M *ᵥ h.ofLp) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [H0]
        have H1 : x.ofLp ⬝ᵥ (M *ᵥ h.ofLp) = (x.ofLp ᵥ* M) ⬝ᵥ h.ofLp := Matrix.dotProduct_mulVec _ _ _
        rw [H1]
        have H2 : h.ofLp ⬝ᵥ (M *ᵥ x.ofLp) = (M *ᵥ x.ofLp) ⬝ᵥ h.ofLp := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [H2]
        congr 1
        ext i
        dsimp [Matrix.vecMul, Matrix.mulVec]
        apply Finset.sum_congr rfl
        intro j _
        change x.ofLp j * M j i = M i j * x.ofLp j
        have hm : M j i = M i j := (hM.apply j i).symm
        rw [hm]
        ring
      have h_inner_r : inner ℝ r (x + h) = inner ℝ r x + inner ℝ r h := inner_add_right _ _ _
      rw [h_inner_r]
      have h_inner_ones : inner ℝ ones (x + h) = inner ℝ ones x + inner ℝ ones h := inner_add_right _ _ _
      rw [h_inner_ones]
      have h_symm : inner ℝ (matVec M x) h = inner ℝ h (matVec M x) := real_inner_comm _ _
      rw [h_cross, h_symm]
      have h_inner_grad : inner ℝ (euclideanOf fun i => (M.mulVec x) i - r i + lambda) h =
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
          try ring
        rw [h2, h3, h4, ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
        try apply Finset.sum_congr rfl
        try intro i _
        try ring
      rw [h_inner_grad, h_symm]
      ring
    have h_expansion_x' : ∀ x', tiltedLoss M r lambda x' - tiltedLoss M r lambda x -
      inner ℝ (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) (x' - x) =
        (1 / 2 : ℝ) * inner ℝ (x' - x) (matVec M (x' - x)) := by
      intro x'
      have H := h_expansion (x' - x)
      have h_eq : x + (x' - x) = x' := by abel
      rw [h_eq] at H
      exact H
    have h_o1 := (isLittleO_inner_matVec M hM).const_mul_left (1 / 2 : ℝ)
    have h_tendsto : Filter.Tendsto (fun x' => x' - x) (nhds x) (nhds 0) := by
      have : (fun x' => x' - x) = (fun x' => x' - x) := rfl
      rw [this]
      have h2 : Filter.Tendsto (fun x' => x' - x) (nhds x) (nhds (x - x)) := (continuous_id.sub continuous_const).tendsto x
      have h3 : x - x = 0 := sub_self x
      rw [h3] at h2
      exact h2
    have h_o2 := h_o1.comp_tendsto h_tendsto
    exact Asymptotics.IsLittleO.congr_left h_o2 (fun x' => (h_expansion_x' x').symm)
  exact h_grad.gradient

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
  sorry

/--
Lemma 4.3 from `docs/Lasso.md`: in the non-coercive case, energy decrease still
controls the image `M xᵋ(t)`.

Informal proof reference: Section 4.3, Lemma 4.3.  Let `x_*` be the minimum-norm
minimizer of `ell`.  Since `r ∈ Span M`, the quadratic loss is bounded below
and `‖M x‖²` is controlled by `‖M^(1/2)(x-x_*)‖²`, hence by the tilted loss
bound from Lemma 4.2.
-/
theorem pos_trajectory_matVec_uniform_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (α : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r 0) (hα : NonzeroCoordinates α)
    (hu : ∀ ε > 0, posDlnGradientFlow M r 0 ε α (u ε)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ,
        ‖matVec M (posEffectiveParameter (u ε) t)‖ ≤ C := by
  sorry

/--
The Bregman divergence associated with the entropy mirror map is nonnegative.

Informal proof reference: `docs/Lasso.md`, Section 4.2 after Eq. (4.2).
It follows from convexity of `h`; in coordinates this is the usual nonnegativity
of relative entropy.
-/
theorem entropyBregman_nonnegative
    (x y : EuclideanSpace ℝ ι) (hx : Positive x) (hy : Positive y) :
    0 ≤ entropyBregman x y := by
  sorry

/--
Lemma 4.4 from `docs/Lasso.md`: the positive-DLN trajectory is the Bregman
projection of its initialization onto the affine fiber with the same `M x`.

Informal proof reference: Section 4.3, Lemma 4.4. The first-order optimality
condition for the constrained Bregman projection is
`∇h(x(t)) - ∇h(x(0)) ∈ Span M`; integrating the mirror-flow equation shows this
condition for the DLN trajectory. Strict convexity gives uniqueness.
-/
theorem bregman_projection_characterization
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) (t : ℝ) :
    IsMinOn
        (fun x => entropyBregman x (posEffectiveParameter u 0))
        {x | Nonnegative x ∧ matVec M x = matVec M (posEffectiveParameter u t)}
        (posEffectiveParameter u t) ∧
      ∀ y : EuclideanSpace ℝ ι,
        IsMinOn
          (fun x => entropyBregman x (posEffectiveParameter u 0))
          {x | Nonnegative x ∧ matVec M x = matVec M (posEffectiveParameter u t)}
          y →
        y = posEffectiveParameter u t := by
  sorry

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
        ‖posEffectiveParameter (u ε) t‖ ≤ C := by
  sorry

end Lasso

end
