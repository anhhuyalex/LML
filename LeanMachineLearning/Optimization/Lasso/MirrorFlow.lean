/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import LeanMachineLearning.Optimization.Lasso.LCP
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
  rw [matVec_add, inner_add_left, inner_add_right, inner_add_right,
    inner_matVec_comm_of_isSymm M hM y a, real_inner_comm a (matVec M y)]
  ring

-- Taylor expansion of the quadratic loss in the effective variable.
private lemma quadraticLoss_add_sub
    (M : Matrix ι ι ℝ) (r y a : EuclideanSpace ℝ ι) (hM : M.IsSymm) :
    quadraticLoss M r (y + a) - quadraticLoss M r y =
      inner ℝ (matVec M y - r) a +
        (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
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
          rw [quadratic_form_increment M hM y a, show - inner ℝ r (y + a) + inner ℝ r y =
            - inner ℝ r a by rw [inner_add_right]; ring]
    _ = inner ℝ (matVec M y - r) a +
            (1 / 2 : ℝ) * inner ℝ a (matVec M a) := by
          rw [← (inner_sub_left _ _ _).symm]
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
  rw [norm_add_sq_real,
    show (euclideanOf fun i ↦ 2 * lambda * (u : ι → ℝ) i) = (2 * lambda) • u by
      ext i; dsimp [euclideanOf],
    inner_smul_left, starRingEnd_apply, star_trivial]
  ring

-- The same weight-decay expansion, stated at an arbitrary endpoint `x'`.
private lemma weight_decay_sub_increment
    (lambda : ℝ) (u x' : EuclideanSpace ℝ ι) :
    lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2 -
        inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) (x' - u) =
      lambda * ‖x' - u‖ ^ 2 := by
  rw [show x' = u + (x' - u) by abel]
  simpa [show u + (x' - u) - u = x' - u by abel] using
    weight_decay_increment lambda u (x' - u)

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
    rw [← show (∑ i, lambda * (1 * h i)) = ∑ i, lambda * h i by
      refine Finset.sum_congr rfl (fun i _ => ?_); ring, Finset.mul_sum]
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
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := euclideanToPiEquiv
  dsimp [coordinateSquare, euclideanOf]
  have hd_pi : HasDerivAt (fun τ => (fun i => u τ i * u τ i)) (fun i => 2 * u t i * u' i) t := by
    apply hasDerivAt_pi.2
    intro i
    have hui : HasDerivAt (fun τ => e (u τ) i) (e u' i) t :=
      hasDerivAt_pi.1 (e.hasFDerivAt.comp_hasDerivAt t hu) i
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
            rw [show lambda * ‖x'‖ ^ 2 - lambda * ‖u‖ ^ 2 =
              lambda * ‖h‖ ^ 2 +
                inner ℝ (euclideanOf fun i ↦ 2 * lambda * u i) h from by
              linarith [h_norm_expansion], h_linear_split]
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
-- For any vector `h`, the coordinatewise square `coordinateSquare h` satisfies
-- `‖coordinateSquare h‖ ≤ ‖h‖ ^ 2`.  This bounds the ℓ²-norm of the
-- coordinatewise square by the squared norm of the original vector.
private lemma norm_coordinateSquare_le_norm_sq (h : EuclideanSpace ℝ ι) :
    ‖coordinateSquare h‖ ≤ ‖h‖ ^ 2 := by
  -- For each coordinate i, (h i)^2 ≤ ‖h‖^2 because the latter is a sum
  -- of nonnegative squares containing (h i)^2 as a term.
  have h_sq_le_norm_sq (i : ι) : (h i)^2 ≤ ‖h‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (h j)) (Finset.mem_univ i)
  -- Compute ‖coordinateSquare h‖^2 = ∑ (h i)^4
  have h_norm_cs_sq_eq : ‖coordinateSquare h‖^2 = ∑ i : ι, ((h i)^2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [coordinateSquare, euclideanOf, sq]
  -- Bound the sum of fourth powers by (‖h‖^2)^2
  have h_sum_ineq : (∑ i : ι, ((h i)^2)^2) ≤ (‖h‖^2)^2 := by
    calc
      (∑ i : ι, ((h i)^2)^2) = ∑ i : ι, ((h i)^2 * (h i)^2) := by
        simp [sq]
      _ ≤ ∑ i : ι, ((h i)^2 * (‖h‖^2)) :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (h_sq_le_norm_sq i) (sq_nonneg (h i)))
      _ = (∑ i : ι, (h i)^2) * (‖h‖^2) := by simp [Finset.sum_mul]
      _ = (‖h‖^2) * (‖h‖^2) := by rw [EuclideanSpace.real_norm_sq_eq]
      _ = (‖h‖^2)^2 := by ring
  have h_sq_ineq : ‖coordinateSquare h‖^2 ≤ (‖h‖^2)^2 := by
    calc
      ‖coordinateSquare h‖^2 = ∑ i : ι, ((h i)^2)^2 := h_norm_cs_sq_eq
      _ ≤ (‖h‖^2)^2 := h_sum_ineq
  have h_nonneg_cs : 0 ≤ ‖coordinateSquare h‖ := norm_nonneg _
  have h_nonneg_norm_sq : 0 ≤ ‖h‖^2 := pow_two_nonneg _
  nlinarith

-- The translation `x' ↦ x' - u` tends to `0` as `x' → u`.
private lemma tendsto_sub_self (u : EuclideanSpace ℝ ι) :
    Filter.Tendsto (fun x' : EuclideanSpace ℝ ι => x' - u) (nhds u) (nhds 0) := by
  have h2 : Filter.Tendsto (fun x' : EuclideanSpace ℝ ι => x' - u)
      (nhds u) (nhds (u - u)) :=
    (continuous_id.sub continuous_const).tendsto u
  simpa using h2

-- For any fixed vector `a`, the inner product `⟨a, coordinateSquare h⟩` is
-- `O(‖h‖^2)` near zero, by Cauchy-Schwarz and `‖coordinateSquare h‖ ≤ ‖h‖^2`.
private lemma inner_coordinateSquare_isBigO_norm_sq (a : EuclideanSpace ℝ ι) :
    (fun h : EuclideanSpace ℝ ι => inner ℝ a (coordinateSquare h)) =O[nhds 0] fun h => ‖h‖ ^ 2 := by
  have h_bound : ∀ h : EuclideanSpace ℝ ι,
      ‖inner ℝ a (coordinateSquare h)‖ ≤ ‖a‖ * (‖h‖ ^ 2) := by
    intro h
    calc
      ‖inner ℝ a (coordinateSquare h)‖ = |inner ℝ a (coordinateSquare h)| := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖a‖ * ‖coordinateSquare h‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖a‖ * (‖h‖ ^ 2) := by
        nlinarith [norm_coordinateSquare_le_norm_sq h, norm_nonneg a]
  have h_eventually : ∀ᶠ (h : EuclideanSpace ℝ ι) in 𝓝 0,
      ‖inner ℝ a (coordinateSquare h)‖ ≤ ‖a‖ * ‖(fun h' => ‖h'‖ ^ 2) h‖ := by
    refine Eventually.of_forall fun h => ?_
    simpa using h_bound h
  exact IsBigO.of_bound ‖a‖ h_eventually

-- Helper: `‖h‖^2 = o(h)` near zero in a normed space.
private lemma norm_sq_isLittleO_id_at_zero :
    (fun h : EuclideanSpace ℝ ι => ‖h‖ ^ 2) =o[nhds 0] fun h => h :=
  Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2)

-- `coordinateSquare h` is `O(‖h‖^2)` near zero, using `‖coordinateSquare h‖ ≤ ‖h‖^2`.
private lemma coordinateSquare_isBigO_norm_sq_at_zero :
    (fun h : EuclideanSpace ℝ ι => coordinateSquare h) =O[nhds 0] fun h => ‖h‖ ^ 2 := by
  have h_eventually : ∀ᶠ h in (nhds 0 : Filter (EuclideanSpace ℝ ι)),
      ‖coordinateSquare h‖ ≤ 1 * ‖(fun h' => ‖h'‖^2) h‖ := by
    refine Eventually.of_forall (fun h => ?_)
    simpa [Real.norm_of_nonneg (pow_two_nonneg ‖h‖), one_mul] using
      norm_coordinateSquare_le_norm_sq h
  exact IsBigO.of_bound 1 h_eventually

-- `coordinateSquare h = o(h)` near zero, combining the above with `‖h‖^2 = o(h)`.
private lemma coordinateSquare_isLittleO_id_at_zero :
    (fun h : EuclideanSpace ℝ ι => coordinateSquare h) =o[nhds 0] id :=
  coordinateSquare_isBigO_norm_sq_at_zero.trans_isLittleO norm_sq_isLittleO_id_at_zero

-- If `a = O(g)` near `u` and `g → 0` at `u`, then `⟨a, M·a⟩ = o(g)`.
-- This uses that `matVec M` is continuous linear and the inner product is
-- bounded bilinear, so `⟨a, M·a⟩ = O(‖g‖^2) = o(g)`.
private lemma inner_matVec_isLittleO_of_isBigO_tendsto
    (M : Matrix ι ι ℝ) (a g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ ι)
    (ha_O : a =O[nhds u] g) (hg_tendsto : Filter.Tendsto g (nhds u) (nhds 0)) :
    (fun x' => inner ℝ (a x') (matVec M (a x'))) =o[nhds u] g := by
  let M_lin : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
    { toFun := matVec M
      map_add' := matVec_add M
      map_smul' := matVec_smul_eq M
    }
  have hMa_O_g : (fun x' => matVec M (a x')) =O[nhds u] g :=
    (M_lin.toContinuousLinearMap.isBigO_comp a (nhds u)).trans ha_O
  -- Product of norms is O(‖g‖^2)
  have h_norm_prod : (fun x' => ‖a x'‖ * ‖matVec M (a x')‖) =O[nhds u]
      fun x' => ‖g x'‖ * ‖g x'‖ :=
    (ha_O.norm_norm).mul (hMa_O_g.norm_norm)
  -- Inner product is O(‖a‖ * ‖matVec M (a)‖) by bounded-bilinearity of inner, then o(g)
  have h_inner_O : (fun x' => inner ℝ (a x') (matVec M (a x'))) =O[nhds u]
      fun x' => ‖g x'‖ * ‖g x'‖ :=
    (isBoundedBilinearMap_inner.isBigO_comp
      (g := a) (h := fun x' => matVec M (a x')) (l := nhds u)).trans h_norm_prod
  have h_norm_sq_o_at_zero : (fun h : EuclideanSpace ℝ ι => ‖h‖ * ‖h‖) =o[nhds 0] fun h => h := by
    simpa [sq] using norm_sq_isLittleO_id_at_zero (ι := ι)
  exact h_inner_O.trans_isLittleO (h_norm_sq_o_at_zero.comp_tendsto hg_tendsto)

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
    -- We split the displayed remainder into its three genuinely quadratic
    -- pieces and combine the little-o estimates additively.
    have h_loss_quad :
        (fun x' : EuclideanSpace ℝ ι ↦
          inner ℝ ((matVec M (coordinateSquare u)) - r) (coordinateSquare (x' - u)))
          =o[nhds u] fun x' : EuclideanSpace ℝ ι ↦ x' - u :=
      ((inner_coordinateSquare_isBigO_norm_sq ((matVec M (coordinateSquare u)) - r)).trans_isLittleO
        (norm_sq_isLittleO_id_at_zero (ι := ι))).comp_tendsto (tendsto_sub_self u)
    have h_weight_decay_quad :
        (fun x' : EuclideanSpace ℝ ι ↦ lambda * ‖x' - u‖ ^ 2)
          =o[nhds u] fun x' : EuclideanSpace ℝ ι ↦ x' - u :=
      ((norm_sq_isLittleO_id_at_zero (ι := ι)).const_mul_left lambda).comp_tendsto
        (tendsto_sub_self u)
    have h_increment_linear_or_higher :
        (fun x' : EuclideanSpace ℝ ι ↦
          euclideanOf fun i ↦
            2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i))
          =O[nhds u] fun x' : EuclideanSpace ℝ ι ↦ x' - u := by
      -- The first summand is a fixed diagonal linear map applied to `x' - u`,
      -- hence `O(x' - u)`.  The second summand is coordinatewise quadratic,
      -- hence even `o(x' - u)` and therefore `O(x' - u)`.
      -- Construct the diagonal linear map h ↦ euclideanOf (fun i ↦ 2 * u i * h i)
      let L_lin : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
        { toFun := fun h => euclideanOf (fun i => 2 * u i * h i)
          map_add' := by
            intro h₁ h₂
            ext i
            simp [euclideanOf]
            ring
          map_smul' := by
            intro c h
            ext i
            simp [euclideanOf, smul_eq_mul]
            ring
        }
      -- Assemble: the original function equals linear part + quadratic part pointwise
      apply (IsBigO.add (L_lin.toContinuousLinearMap.isBigO_sub (nhds u) u)
        (((coordinateSquare_isLittleO_id_at_zero (ι := ι)).isBigO).comp_tendsto
          (tendsto_sub_self u))).congr_left
      intro x'
      ext i
      dsimp [L_lin]
      simp [coordinateSquare, euclideanOf]
    have h_quadratic_form_quad :
        (fun x' : EuclideanSpace ℝ ι ↦
          (1 / 2 : ℝ) *
            inner ℝ
              (euclideanOf fun i ↦
                2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i))
              (matVec M
                (euclideanOf fun i ↦
                  2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i))))
          =o[nhds u] fun x' : EuclideanSpace ℝ ι ↦ x' - u := by
      -- Let `a(x') = 2*u*(x'-u) + (x'-u)^2` and `g(x') = x'-u`.
      -- Since `a = O(g)` and `g → 0`, the core lemma gives `⟨a, M·a⟩ = o(g)`.
      -- The prefactor `1/2` is harmless.
      let a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x' =>
        euclideanOf fun i ↦ 2 * u i * ((x' - u) i) + ((x' - u) i) * ((x' - u) i)
      let g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x' => x' - u
      have h_inner_o := inner_matVec_isLittleO_of_isBigO_tendsto M a g u
        h_increment_linear_or_higher
        (by simpa [g] using tendsto_sub_self u)
      simpa [a, g] using h_inner_o.const_mul_left (1/2 : ℝ)
    exact (h_loss_quad.add h_weight_decay_quad).add h_quadratic_form_quad
  rw [hasGradientAt_iff_isLittleO]
  exact h_remainder_o.congr_left
    (fun x' => (posDlnObjective_taylor_remainder M r lambda hM u x').symm)

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
`d ∇h(x) / dt = -∇ell(x) - lambda * 𝟙 = -∇L_tilde(x)`.
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
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := euclideanToPiEquiv
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
      dsimp [positiveEffectiveVectorField, euclideanOf, matVec, e, euclideanToPiEquiv,
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
        euclideanToPiEquiv.symm (M.mulVec (x : ι → ℝ)) := rfl
    rw [h_eq]
    apply Continuous.comp euclideanToPiEquiv.symm.continuous
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    exact Continuous.mul continuous_const
      ((continuous_apply j).comp euclideanToPiEquiv.continuous)
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
  have h_tendsto : Filter.Tendsto (fun x' : EuclideanSpace ℝ ι => x' - x) (nhds x) (nhds 0) :=
    tendsto_sub_self x
  have h_expansion_x' : ∀ x', tiltedLoss M r lambda x' - tiltedLoss M r lambda x -
    inner ℝ (euclideanOf (fun i => (M.mulVec x) i - r i + lambda)) (x' - x) =
      (1 / 2 : ℝ) * inner ℝ (x' - x) (matVec M (x' - x)) := by
    intro x'
    simpa [show x + (x' - x) = x' by abel] using h_expansion (x' - x)
  exact Asymptotics.IsLittleO.congr_left
    (((isLittleO_inner_matVec M hM).const_mul_left (1 / 2 : ℝ)).comp_tendsto h_tendsto)
    (fun x' => (h_expansion_x' x').symm)

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

/-- Nonzero initialization coordinates never reach zero along a positive-DLN
gradient flow.

Coordinate `uᵢ` solves the scalar linear ODE
`uᵢ' = aᵢ(t) uᵢ`.  Hence `uᵢ(t)=uᵢ(0) exp(∫ aᵢ)`, so a nonzero initial value
cannot vanish; squaring gives the result for `posEffectiveParameter`.  This is
the invariant used implicitly in Lemma 4.4 of
<https://arxiv.org/abs/2509.18766>.  The exponential solution/uniqueness
principle is standard; compare Teschl, *Ordinary Differential Equations and
Dynamical Systems*, Section 2.1
<https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf>.
-/
theorem posEffectiveParameter_ne_zero
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (α : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε α u) (hε : 0 < ε)
    (hα : NonzeroCoordinates α) (hM : M.IsSymm) :
    ∀ t i, posEffectiveParameter u t i ≠ 0 := by
  -- Initial values are nonzero: u(0) = √ε • α, ε > 0, α_i ≠ 0 ⇒ u_i(0) ≠ 0
  have hu0_ne_zero : ∀ i, u 0 i ≠ 0 := by
    intro i
    rw [hu.init]
    have hsqrt_pos : Real.sqrt ε > 0 := Real.sqrt_pos.mpr hε
    simp [hsqrt_pos.ne', hα i, smul_eq_mul]
  -- Linear equivalence between EuclideanSpace and bare functions
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := euclideanToPiEquiv
  intro t i
  -- Define the coefficient a_i : ℝ → ℝ
  let a : ℝ → ℝ := fun τ => -2 * ((matVec M (coordinateSquare (u τ))) i - r i + lambda)
  -- a is continuous because u is C¹ and matVec, coordinateSquare, etc. are continuous.
  have ha_cont : Continuous a := by
    dsimp [a]
    have hu_cont : Continuous u := hu.cont_diff.continuous
    have h_coordSquare_cont :
        Continuous (coordinateSquare : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
      have h_sq : Continuous (fun (x : EuclideanSpace ℝ ι) (i : ι) => x i * x i) :=
        continuous_pi fun i =>
          Continuous.mul (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i)
            (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i)
      have h_euclideanOf_cont : Continuous (euclideanOf : (ι → ℝ) → EuclideanSpace ℝ ι) :=
        euclideanToPiEquiv.symm.continuous_of_finiteDimensional
      exact h_euclideanOf_cont.comp h_sq
    have h_matVec_cont : Continuous (matVec M) := by
      let M_lin : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
        { toFun := matVec M
          map_add' := matVec_add M
          map_smul' := matVec_smul_eq M }
      exact M_lin.continuous_of_finiteDimensional
    have h_apply_i : Continuous (fun (x : EuclideanSpace ℝ ι) => x i) :=
      PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i
    have h_inner : Continuous (fun τ : ℝ =>
        ((matVec M (coordinateSquare (u τ))) i - r i + lambda)) := by
      refine Continuous.add (Continuous.sub ?_ continuous_const) continuous_const
      exact h_apply_i.comp (h_matVec_cont.comp (h_coordSquare_cont.comp hu_cont))
    exact Continuous.mul continuous_const h_inner
  -- For each τ, the scalar ODE holds: u_i'(τ) = a(τ) * u_i(τ)
  have h_ode_scalar : ∀ (τ : ℝ), HasDerivAt (fun (s : ℝ) => u s i) (a τ * u τ i) τ := by
    intro τ
    have h_ode := hu.ode τ
    dsimp [posDlnVectorField] at h_ode
    rw [gradient_posDlnObjective M r lambda hM (u τ)] at h_ode
    -- h_ode : HasDerivAt u (-euclideanOf (fun i => 2 * u τ i * ...)) τ
    -- Convert to component form via e
    have h_ode' : HasDerivAt (fun s => e (u s))
        (e (-euclideanOf (fun i => 2 * u τ i *
          ((matVec M (coordinateSquare (u τ))) i - r i + lambda)))) τ :=
      e.hasFDerivAt.comp_hasDerivAt τ h_ode
    have h_pi := (hasDerivAt_pi.1 h_ode') i
    simpa [a, e, euclideanToPiEquiv, WithLp.linearEquiv, euclideanOf, mul_comm, mul_left_comm,
      mul_assoc] using h_pi
  -- Integrating factor: B(τ) = ∫_0^τ a(s) ds
  let B : ℝ → ℝ := fun τ => ∫ s in (0 : ℝ)..τ, a s
  have hB_deriv : ∀ (τ : ℝ), HasDerivAt B (a τ) τ := by
    intro τ
    have h_int : IntervalIntegrable a MeasureTheory.volume 0 τ :=
      ha_cont.intervalIntegrable _ _
    have h_meas : StronglyMeasurableAtFilter a (𝓝 τ) :=
      ha_cont.stronglyMeasurableAtFilter _ _
    have h_cont_at : ContinuousAt a τ := ha_cont.continuousAt
    exact intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont_at
  have hB_zero : B 0 = 0 := by simp [B]
  -- Define φ(τ) = u_i(τ) * exp(-B(τ))
  let φ : ℝ → ℝ := fun τ => u τ i * Real.exp (-B τ)
  -- φ'(τ) = 0 for all τ
  have hφ_deriv : ∀ (τ : ℝ), HasDerivAt φ 0 τ := by
    intro τ
    -- φ' = u_i' * exp(-B) + u_i * exp(-B) * (-B')
    --    = (a * u_i) * exp(-B) + u_i * exp(-B) * (-a) = 0
    have h1 : HasDerivAt (fun s => u s i) (a τ * u τ i) τ := h_ode_scalar τ
    have h_negB : HasDerivAt (-B) (-a τ) τ := by
      simpa using (hB_deriv τ).neg
    have h_exp : HasDerivAt (fun s => Real.exp (-B s)) (Real.exp (-B τ) * (-a τ)) τ :=
      h_negB.exp
    -- HasDerivAt.mul gives (exp * u) with derivative (exp'*u + exp*u')
    have h_mul := HasDerivAt.mul h_exp h1
    -- Simplify the derivative: exp'*u + exp*u' = exp*(-a)*u + exp*(a*u) = 0
    have h_deriv_simp : (Real.exp (-B τ) * (-a τ)) * (u τ).ofLp i +
        Real.exp (-B τ) * (a τ * (u τ).ofLp i) = 0 := by
      ring
    have h_mul_simp := h_mul.congr_deriv h_deriv_simp
    -- h_mul_simp: HasDerivAt (fun s => exp(-B s) * (u s).ofLp i) 0 τ
    -- Reorder multiplication to match φ
    -- h_mul_simp: HasDerivAt ((fun s => exp(-B s)) * (fun s => u s i)) 0 τ
    -- We want: HasDerivAt (fun s => (u s).ofLp i * exp(-B s)) 0 τ = HasDerivAt φ 0 τ
    have h_mul_reorder : HasDerivAt (fun s => (u s).ofLp i * Real.exp (-B s)) 0 τ := by
      -- The two functions are equal pointwise by mul_comm
      have h_eq : ((fun s => Real.exp (-B s)) * fun s => (u s).ofLp i) =
                 (fun s => (u s).ofLp i * Real.exp (-B s)) := by
        ext s; apply mul_comm
      exact h_eq ▸ h_mul_simp
    simpa [φ] using h_mul_reorder
  -- Since φ' = 0 everywhere, φ is constant (mean value theorem)
  have hφ_const : ∀ (τ : ℝ), φ τ = φ 0 := by
    have hφ_diff : Differentiable ℝ φ := by
      have hu_i_diff : Differentiable ℝ (fun τ => u τ i) :=
        fun τ => (h_ode_scalar τ).differentiableAt
      have hB_diff : Differentiable ℝ B :=
        fun τ => (hB_deriv τ).differentiableAt
      have h_exp_negB_diff : Differentiable ℝ (fun τ => Real.exp (-B τ)) :=
        Real.differentiable_exp.comp hB_diff.neg
      dsimp [φ]
      exact Differentiable.mul hu_i_diff h_exp_negB_diff
    have hφ_deriv_eq_zero : ∀ τ, deriv φ τ = 0 := by
      intro τ
      exact (hφ_deriv τ).deriv
    exact fun τ => is_const_of_deriv_eq_zero hφ_diff hφ_deriv_eq_zero τ 0
  have hφ0_ne_zero : φ 0 ≠ 0 := by
    dsimp [φ, B]
    simp [Real.exp_zero, hu0_ne_zero i]
  -- Therefore u t i ≠ 0
  have hu_t_ne_zero : u t i ≠ 0 := by
    intro hzero
    apply hφ0_ne_zero
    have := hφ_const t
    dsimp [φ] at this
    rw [hzero] at this
    simp at this
    -- this: (u 0).ofLp i = 0  (after simplification of exp(-B 0) = 1)
    -- Goal: φ 0 = 0, i.e., (u 0).ofLp i * Real.exp (-B 0) = 0
    simpa [φ, B] using this
  -- Finally, posEffectiveParameter u t i = (u t i)^2 ≠ 0
  dsimp [posEffectiveParameter, coordinateSquare, euclideanOf]
  exact mul_ne_zero hu_t_ne_zero hu_t_ne_zero

-- Bounds the quadratic loss at the initial-energy scale `ε • a`, for `0 < ε ≤ 1`.
-- Shared by `pos_trajectory_matVec_uniform_bound` and `pos_trajectory_uniform_bound`,
-- both of which need this bound for the same `K := (1/2)⟨a, Ma⟩ + |⟨r, a⟩|`.
private lemma quadraticLoss_smul_le_energy_bound
    (M : Matrix ι ι ℝ) (r a : EuclideanSpace ℝ ι) (hM_psd : IsPositiveSemidefinite M)
    {ε : ℝ} (hε : 0 < ε) (hε_one : ε ≤ 1) :
    quadraticLoss M r (ε • a) ≤ (1 / 2 : ℝ) * inner ℝ a (matVec M a) + |inner ℝ r a| := by
  rw [quadraticLoss_smul]
  have haa : 0 ≤ inner ℝ a (matVec M a) := hM_psd.nonneg a
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
  nlinarith

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
      have hinit : quadraticLoss M r (ε • a) ≤ K :=
        quadraticLoss_smul_le_energy_bound M r a hdata.psd hε hε_one
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
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := euclideanToPiEquiv
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
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := euclideanToPiEquiv
  dsimp [posIntegratedTrajectory, euclideanOf]
  have h_pi : HasDerivAt (fun τ => (fun i => ∫ v in (0:ℝ)..τ, posEffectiveParameter u v i))
      (fun i => posEffectiveParameter u t i) t := by
    apply hasDerivAt_pi.2
    intro i
    have hcont_i : Continuous (fun v => posEffectiveParameter u v i) :=
      (continuous_euclidean_apply i).comp hcont
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
    (hε : 0 < ε) (hα : NonzeroCoordinates α)
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
  have hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0 :=
    posEffectiveParameter_ne_zero M r 0 ε α u hu hε hα hM
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

-- Splits `x * log(x/y)` even when `x = 0` (both sides vanish, matching the
-- `0 log 0 = 0` convention from `docs/Lasso.md`).
private lemma mul_log_div_eq (x y : ℝ) (hy : y ≠ 0) :
    x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0]
  · rw [Real.log_div hx0 hy]; ring

-- Algebraic expansion of `4 * D(x', ε α²)` used to bound the Bregman
-- projection in Lemma 4.5.  Writing `L = -log ε`, this is Eq. (4.8) from
-- `docs/Lasso.md` before the coordinatewise bounds are applied.
private lemma entropyBregman_scaled_four_eq
    (α x' : EuclideanSpace ℝ ι) (hα : NonzeroCoordinates α) (ε : ℝ) (hε : 0 < ε) :
    4 * entropyBregman x' (ε • coordinateSquare α) =
      (∑ i, (x' i * Real.log (x' i) - x' i))
        + (-Real.log ε) * (∑ i, x' i)
        - (∑ i, x' i * Real.log (α i * α i))
        + ε * (∑ i, α i * α i) := by
  have hshape : entropyBregman x' (ε • coordinateSquare α) =
      (1 / 4 : ℝ) * ∑ i, (x' i * Real.log (x' i / (ε * (α i * α i))) - x' i + ε * (α i * α i)) :=
    rfl
  rw [hshape]
  have hpt : ∀ i,
      x' i * Real.log (x' i / (ε * (α i * α i))) - x' i + ε * (α i * α i) =
      (x' i * Real.log (x' i) - x' i) + (-Real.log ε) * x' i - x' i * Real.log (α i * α i) +
        ε * (α i * α i) := by
    intro i
    have hy : ε * (α i * α i) ≠ 0 := mul_ne_zero hε.ne' (mul_ne_zero (hα i) (hα i))
    rw [mul_log_div_eq (x' i) (ε * (α i * α i)) hy,
      Real.log_mul hε.ne' (mul_ne_zero (hα i) (hα i))]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  ring

-- `t - 1 ≤ t * log t` for `t ≥ 0`, reusing Mathlib's KL-generator nonnegativity
-- (`InformationTheory.klFun t = t * log t + 1 - t ≥ 0`) rather than reproving
-- the boundedness of `t ↦ t log t` from scratch.
private lemma mul_log_sub_one_le (t : ℝ) (ht : 0 ≤ t) : t - 1 ≤ t * Real.log t := by
  have h := InformationTheory.klFun_nonneg ht
  dsimp [InformationTheory.klFun] at h
  linarith

-- `t * log t ≤ t ^ 2` for `t ≥ 0`, from the standard bound `log t ≤ t - 1`.
private lemma mul_log_le_sq (t : ℝ) (ht : 0 ≤ t) : t * Real.log t ≤ t ^ 2 := by
  rcases ht.eq_or_lt with h0 | h0
  · simp [← h0]
  · have hlog : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos h0
    nlinarith [h0.le]

-- `‖x‖ ≤ ∑ᵢ xᵢ` for nonnegative `x`: the ℓ² norm is dominated by the ℓ¹ norm
-- (= the sum, since `x ≥ 0`) coordinatewise.
private lemma norm_le_sum_of_nonneg (x : EuclideanSpace ℝ ι) (hx : Nonnegative x) :
    ‖x‖ ≤ ∑ i, x i := by
  have hsq : ‖x‖ ^ 2 ≤ (∑ i, x i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hterm : ∀ i, x.ofLp i ^ 2 ≤ x.ofLp i * ∑ j, x j := by
      intro i
      have hle : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      have hxi : (0 : ℝ) ≤ x.ofLp i := hx i
      calc x.ofLp i ^ 2 = x.ofLp i * x.ofLp i := sq (x.ofLp i)
        _ ≤ x.ofLp i * ∑ j, x j := mul_le_mul_of_nonneg_left hle hxi
    calc ∑ i, x.ofLp i ^ 2 ≤ ∑ i, x.ofLp i * ∑ j, x j := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (∑ i, x.ofLp i) * (∑ j, x j) := by rw [← Finset.sum_mul]
      _ = (∑ i, x i) ^ 2 := (sq _).symm
  have hnn1 : 0 ≤ ‖x‖ := norm_nonneg x
  have hnn2 : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at this

private lemma sum_eq_inner_ones (x : EuclideanSpace ℝ ι) :
    (∑ i, x i) = inner ℝ (ones : EuclideanSpace ℝ ι) x := by
  dsimp [ones, euclideanOf]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The fixed "log-scale" vector `ℓᵢ = log(αᵢ²)` used to compare `D(·, εα²)` to `‖·‖`
via Cauchy–Schwarz. -/
private noncomputable def alphaLogSq (α : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun i => Real.log (α i * α i))

private lemma inner_eq_sum_mul_alphaLogSq (α x' : EuclideanSpace ℝ ι) :
    (∑ i, x' i * Real.log (α i * α i)) = inner ℝ x' (alphaLogSq α) := by
  dsimp [alphaLogSq, euclideanOf]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/--
Lower half of Eq. (4.8) from `docs/Lasso.md`, stated with `L = -log ε` in place
of `log(1/ε)` and with the Euclidean norm `‖x'‖` in place of `‖x'‖₁` (valid
since `‖x'‖ ≤ ‖x'‖₁ = ∑ x'ᵢ` for `x' ≥ 0`, `norm_le_sum_of_nonneg`).  Requires
`log ε ≤ -1` (i.e. `ε ≤ 1/e`) so that the coefficient of `∑ x'ᵢ` is nonnegative.
-/
private lemma entropyBregman_scaled_lower_bound
    (α x' : EuclideanSpace ℝ ι) (hα : NonzeroCoordinates α) (hx' : Nonnegative x')
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : Real.log ε ≤ -1) :
    ((-Real.log ε - ‖alphaLogSq α‖) * ‖x'‖ - Fintype.card ι) ≤
      4 * entropyBregman x' (ε • coordinateSquare α) := by
  rw [entropyBregman_scaled_four_eq α x' hα ε hε0]
  have h1 : (-(Fintype.card ι : ℝ)) ≤ ∑ i, (x' i * Real.log (x' i) - x' i) := by
    have hb : ∀ i ∈ (Finset.univ : Finset ι), (-1 : ℝ) ≤ x' i * Real.log (x' i) - x' i :=
      fun i _ => by linarith [mul_log_sub_one_le (x' i) (hx' i)]
    calc (-(Fintype.card ι : ℝ)) = ∑ _i : ι, (-1 : ℝ) := by simp
      _ ≤ ∑ i, (x' i * Real.log (x' i) - x' i) := Finset.sum_le_sum hb
  have h2 : - ‖alphaLogSq α‖ * ‖x'‖ ≤ - (∑ i, x' i * Real.log (α i * α i)) := by
    have hCS : ∑ i, x' i * Real.log (α i * α i) ≤ ‖x'‖ * ‖alphaLogSq α‖ := by
      rw [inner_eq_sum_mul_alphaLogSq]; exact real_inner_le_norm x' (alphaLogSq α)
    nlinarith [hCS]
  have h3 : (-Real.log ε) * ‖x'‖ ≤ (-Real.log ε) * (∑ i, x' i) :=
    mul_le_mul_of_nonneg_left (norm_le_sum_of_nonneg x' hx') (by linarith)
  have hε2 : (0 : ℝ) ≤ ε * ∑ i, α i * α i :=
    mul_nonneg hε0.le (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
  linarith [h1, h2, h3, hε2]

/--
Upper half of Eq. (4.8) from `docs/Lasso.md`, in the same `L = -log ε` /
Euclidean-norm normalization as `entropyBregman_scaled_lower_bound`.  Requires
only `ε ≤ 1` (so `L ≥ 0`).
-/
private lemma entropyBregman_scaled_upper_bound
    (α x' : EuclideanSpace ℝ ι) (hα : NonzeroCoordinates α) (hx' : Nonnegative x')
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    4 * entropyBregman x' (ε • coordinateSquare α) ≤
      ‖x'‖ ^ 2 + (-Real.log ε) * ‖(ones : EuclideanSpace ℝ ι)‖ * ‖x'‖ +
        ‖x'‖ * ‖alphaLogSq α‖ + ‖α‖ ^ 2 := by
  rw [entropyBregman_scaled_four_eq α x' hα ε hε0]
  have hlogε0 : Real.log ε ≤ 0 := (Real.log_nonpos_iff hε0.le).mpr hε1
  have h1 : ∑ i, (x' i * Real.log (x' i) - x' i) ≤ ‖x'‖ ^ 2 := by
    have hb : ∀ i ∈ (Finset.univ : Finset ι), x' i * Real.log (x' i) - x' i ≤ x' i ^ 2 := by
      intro i _
      have := mul_log_le_sq (x' i) (hx' i)
      linarith [hx' i]
    calc ∑ i, (x' i * Real.log (x' i) - x' i) ≤ ∑ i, x' i ^ 2 := Finset.sum_le_sum hb
      _ = ‖x'‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq x').symm
  have h2 : (-Real.log ε) * (∑ i, x' i) ≤ (-Real.log ε) * ‖(ones : EuclideanSpace ℝ ι)‖ * ‖x'‖ := by
    have hCS : (∑ i, x' i) ≤ ‖(ones : EuclideanSpace ℝ ι)‖ * ‖x'‖ := by
      rw [sum_eq_inner_ones]; exact real_inner_le_norm ones x'
    have := mul_le_mul_of_nonneg_left hCS (by linarith : (0 : ℝ) ≤ -Real.log ε)
    linarith [this]
  have h3 : - (∑ i, x' i * Real.log (α i * α i)) ≤ ‖x'‖ * ‖alphaLogSq α‖ := by
    rw [inner_eq_sum_mul_alphaLogSq]
    exact (neg_le_abs _).trans (abs_real_inner_le_norm x' (alphaLogSq α))
  have h4 : ε * (∑ i, α i * α i) ≤ ‖α‖ ^ 2 := by
    have hSnn : (0 : ℝ) ≤ ∑ i, α i * α i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hSeq : (∑ i, α i * α i) = ‖α‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      ring
    nlinarith [hSeq, hSnn, hε1]
  linarith [h1, h2, h3, h4]

-- Evaluating a finite sum of `EuclideanSpace` vectors coordinatewise.
private lemma sum_apply_euclidean (f : ι → EuclideanSpace ℝ ι) (j : ι) :
    (∑ i, f i) j = ∑ i, (f i) j := by
  simp

/-- The `j`-th column of `M`, as a Euclidean vector. -/
private noncomputable def matVecColumn (M : Matrix ι ι ℝ) (j : ι) : EuclideanSpace ℝ ι :=
  euclideanOf (fun k => M k j)

omit [Fintype ι] in
private lemma matVecColumn_apply (M : Matrix ι ι ℝ) (j k : ι) :
    matVecColumn M j k = M k j := rfl

-- `matVec M` applied to a vector `u` agrees with the conic combination of the columns
-- of `M` weighted by the coordinates of `u`; the bridge needed to view `InCone (columns
-- of M) y` as `∃ u ≥ 0, matVec M u = y` for `Lemma 4.7` (`nonnegative_solution_norm_bound`).
private lemma sum_smul_matVecColumn (M : Matrix ι ι ℝ) (u : EuclideanSpace ℝ ι) :
    (∑ j, u j • matVecColumn M j) = matVec M u := by
  ext k
  rw [sum_apply_euclidean]
  have hshape : (matVec M u) k = ∑ j, M k j * u j := rfl
  rw [hshape]
  have hpt : ∀ j, (u j • matVecColumn M j) k = M k j * u j := by
    intro j
    change u j * matVecColumn M j k = M k j * u j
    rw [matVecColumn_apply]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hpt j)]

/--
Lemma 4.7 from `docs/Lasso.md`, specialized to the columns of `M`: every
nonnegative-feasible `y = M u` (`u ≥ 0`) has a nonnegative-feasible witness
`β` whose norm is controlled by `‖y‖`, uniformly in `y`.

This packages `nonnegative_solution_norm_bound` from `LeanMachineLearning.Optimization.Lasso.LCP`
(the conic-Carathéodory-based proof of Lemma 4.7) against the column family
`a j = matVecColumn M j`, using `sum_smul_matVecColumn` to identify conic
combinations of columns with `matVec M`.
-/
private lemma feasible_norm_controlled_solution (M : Matrix ι ι ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : EuclideanSpace ℝ ι, (∃ u : EuclideanSpace ℝ ι, Nonnegative u ∧ matVec M u = y) →
        ∃ β : EuclideanSpace ℝ ι, Nonnegative β ∧ matVec M β = y ∧ ‖β‖ ≤ C * ‖y‖ := by
  set a : ι → EuclideanSpace ℝ ι := matVecColumn M with ha
  obtain ⟨C, hC0, hCbound⟩ := nonnegative_solution_norm_bound a
  refine ⟨C, hC0, ?_⟩
  rintro y ⟨u, hu_nonneg, hu_eq⟩
  have hy_cone : InCone a y := ⟨u, hu_nonneg, by rw [ha]; exact hu_eq ▸ sum_smul_matVecColumn M u⟩
  obtain ⟨x, hx_nonneg, hx_sum, hx_norm⟩ := hCbound y hy_cone
  refine ⟨euclideanOf x, fun i => hx_nonneg i, ?_, hx_norm⟩
  rw [← hx_sum, ha, ← sum_smul_matVecColumn M (euclideanOf x)]
  rfl

/--
Lemma 4.5 from `docs/Lasso.md`: Bregman projections on nonnegative affine
fibers have a norm bound polynomial in the fiber value.

Informal proof reference: Section 4.3, Lemma 4.5.  Compare the entropy
Bregman objective at its minimizer with a minimum-norm feasible nonnegative
solution supplied by Lemma 4.7.  The coordinate expression for the Bregman
divergence is sandwiched between a linear lower bound and a quadratic upper
bound in `‖x‖`, uniformly for small `ε`.

Note on hypotheses: as in `bregman_projection_characterization`, `IsMinOn f s x`
alone does not imply `x ∈ s`, so the minimality hypothesis alone cannot pin down
`Nonnegative x` (e.g. `x = ε • coordinateSquare α` trivially satisfies `IsMinOn`
against any `s` on which `entropyBregman` is nonnegative, since it makes the
divergence itself vanish). We therefore add `Nonnegative x` explicitly; at every
call site (`pos_trajectory_uniform_bound` below) this holds automatically via
`posEffectiveParameter_nonnegative`.
-/
theorem bregman_projection_fiber_norm_bound_fixed_initialization
    (M : Matrix ι ι ℝ) (α : EuclideanSpace ℝ ι) (hα : NonzeroCoordinates α) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ y : EuclideanSpace ℝ ι,
          (∃ u : EuclideanSpace ℝ ι, Nonnegative u ∧ matVec M u = y) →
          ∀ x : EuclideanSpace ℝ ι, Nonnegative x →
            IsMinOn
              (fun z => entropyBregman z (ε • coordinateSquare α))
              {z | Nonnegative z ∧ matVec M z = y}
              x →
            ‖x‖ ≤ C * (1 + ‖y‖ ^ 2) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := feasible_norm_controlled_solution M
  set ℓ := alphaLogSq α with hℓdef
  set K : ℝ := ‖ℓ‖ + (‖ℓ‖ + 1) * ‖(ones : EuclideanSpace ℝ ι)‖ with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1,
    Real.exp (-(‖ℓ‖ + 1)), by positivity, Real.exp_pos _, ?_⟩
  intro ε hε0 hεε₀ y ⟨u, hu_nonneg, hu_eq⟩ x hx_nonneg hx_min
  obtain ⟨β, hβ_nonneg, hβ_eq, hβ_norm⟩ := hC₀ y ⟨u, hu_nonneg, hu_eq⟩
  have hL_ge : (‖ℓ‖ + 1 : ℝ) ≤ -Real.log ε := by
    have hlog_le : Real.log ε ≤ Real.log (Real.exp (-(‖ℓ‖ + 1))) :=
      Real.log_le_log hε0 hεε₀
    rwa [Real.log_exp, le_neg] at hlog_le
  have hε1 : ε ≤ 1 := by
    have hexp_le_one : Real.exp (-(‖ℓ‖ + 1)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [norm_nonneg ℓ])
    linarith [hεε₀, hexp_le_one]
  have hlogε_le : Real.log ε ≤ -1 := by nlinarith [norm_nonneg ℓ, hL_ge]
  have hx_beta : entropyBregman x (ε • coordinateSquare α) ≤
      entropyBregman β (ε • coordinateSquare α) :=
    hx_min ⟨hβ_nonneg, hβ_eq⟩
  have hlow := entropyBregman_scaled_lower_bound α x hα hx_nonneg ε hε0 hlogε_le
  have hup := entropyBregman_scaled_upper_bound α β hα hβ_nonneg ε hε0 hε1
  have hcombine : (-Real.log ε - ‖ℓ‖) * ‖x‖ - (Fintype.card ι : ℝ) ≤
      ‖β‖ ^ 2 + (-Real.log ε) * ‖(ones : EuclideanSpace ℝ ι)‖ * ‖β‖ + ‖β‖ * ‖ℓ‖ + ‖α‖ ^ 2 := by
    linarith [hlow, hup, hx_beta]
  have hLm1 : (0 : ℝ) ≤ -Real.log ε - ‖ℓ‖ - 1 := by linarith [hL_ge]
  have hpos : (0 : ℝ) < -Real.log ε - ‖ℓ‖ := by linarith [hLm1]
  have hstep : (-Real.log ε - ‖ℓ‖) * ‖x‖ ≤
      (-Real.log ε - ‖ℓ‖) * ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + ‖β‖ ^ 2 + K * ‖β‖) := by
    have hterm1 : (Fintype.card ι : ℝ) ≤
        (-Real.log ε - ‖ℓ‖) * (Fintype.card ι : ℝ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith [hLm1])
    have hterm2 : ‖α‖ ^ 2 ≤ (-Real.log ε - ‖ℓ‖) * ‖α‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (by linarith [hLm1])
    have hterm3 : ‖β‖ ^ 2 ≤ (-Real.log ε - ‖ℓ‖) * ‖β‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (by linarith [hLm1])
    have hterm4 : ‖β‖ * ‖ℓ‖ + (-Real.log ε) * ‖(ones : EuclideanSpace ℝ ι)‖ * ‖β‖ ≤
        (-Real.log ε - ‖ℓ‖) * (K * ‖β‖) := by
      have hratio : -Real.log ε ≤ (‖ℓ‖ + 1) * (-Real.log ε - ‖ℓ‖) := by
        nlinarith [hLm1, norm_nonneg ℓ]
      have hones_nonneg : (0 : ℝ) ≤ ‖(ones : EuclideanSpace ℝ ι)‖ := norm_nonneg _
      have hβ0 : (0 : ℝ) ≤ ‖β‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hratio (mul_nonneg hones_nonneg hβ0),
        mul_nonneg (norm_nonneg ℓ) hLm1, hβ0]
    nlinarith [hterm1, hterm2, hterm3, hterm4]
  have hxle : ‖x‖ ≤ (Fintype.card ι : ℝ) + ‖α‖ ^ 2 + ‖β‖ ^ 2 + K * ‖β‖ :=
    le_of_mul_le_mul_left (hstep.trans (by linarith [hcombine])) hpos
  have hβsq : ‖β‖ ^ 2 ≤ C₀ ^ 2 * ‖y‖ ^ 2 := by
    have hβ0 : (0 : ℝ) ≤ ‖β‖ := norm_nonneg β
    have hCy0 : (0 : ℝ) ≤ C₀ * ‖y‖ := mul_nonneg hC₀0 (norm_nonneg y)
    calc ‖β‖ ^ 2 ≤ (C₀ * ‖y‖) ^ 2 := by nlinarith [hβ_norm, hβ0, hCy0]
      _ = C₀ ^ 2 * ‖y‖ ^ 2 := by ring
  have hβK : K * ‖β‖ ≤ K * C₀ * ‖y‖ :=
    mul_le_mul_of_nonneg_left hβ_norm hK0 |>.trans_eq (by ring)
  have hamgm : ‖y‖ ≤ (1 + ‖y‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hKC₀y : K * C₀ * ‖y‖ ≤ K * C₀ * ((1 + ‖y‖ ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left hamgm (mul_nonneg hK0 hC₀0)
  have hy20 : (0 : ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hKC₀0 : (0 : ℝ) ≤ K * C₀ := mul_nonneg hK0 hC₀0
  have hC₀sq0 : (0 : ℝ) ≤ C₀ ^ 2 := sq_nonneg C₀
  have hcard0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hαsq0 : (0 : ℝ) ≤ ‖α‖ ^ 2 := sq_nonneg _
  have hleft : (Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ / 2 ≤
      (Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1 := by linarith
  have hright : C₀ ^ 2 + K * C₀ / 2 ≤ (Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1 := by
    linarith
  have hfinal :
      ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ / 2) +
          (C₀ ^ 2 + K * C₀ / 2) * ‖y‖ ^ 2 ≤
        ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1) * (1 + ‖y‖ ^ 2) := by
    have := add_le_add hleft (mul_le_mul_of_nonneg_right hright hy20)
    calc
      ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ / 2) + (C₀ ^ 2 + K * C₀ / 2) * ‖y‖ ^ 2 ≤
          ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1) +
            ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1) * ‖y‖ ^ 2 := this
      _ = ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1) * (1 + ‖y‖ ^ 2) := by ring
  calc ‖x‖ ≤ (Fintype.card ι : ℝ) + ‖α‖ ^ 2 + ‖β‖ ^ 2 + K * ‖β‖ := hxle
    _ ≤ (Fintype.card ι : ℝ) + ‖α‖ ^ 2 + C₀ ^ 2 * ‖y‖ ^ 2 + K * C₀ * ‖y‖ := by
        linarith [hβsq, hβK]
    _ ≤ (Fintype.card ι : ℝ) + ‖α‖ ^ 2 + C₀ ^ 2 * ‖y‖ ^ 2 + K * C₀ * ((1 + ‖y‖ ^ 2) / 2) := by
        linarith [hKC₀y]
    _ = ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ / 2) + (C₀ ^ 2 + K * C₀ / 2) * ‖y‖ ^ 2 := by
        ring
    _ ≤ ((Fintype.card ι : ℝ) + ‖α‖ ^ 2 + K * C₀ + C₀ ^ 2 + 1) * (1 + ‖y‖ ^ 2) := hfinal

/-- Faithful quantifier order for Lemma 4.5: `C` depends only on the matrix
(and the ambient finite dimension), while the smallness threshold may depend
on the initialization `α`.

The proof compares the Bregman minimizer with the nonnegative minimum-norm
solution from Lemma 4.7. Uniform entropy estimates absorb the fixed
`log(αᵢ²)` terms by choosing `ε₀(α)` sufficiently small; the remaining
polynomial coefficient depends only on `M` and the dimension. This is the
argument around Eq. (4.8) in <https://arxiv.org/abs/2509.18766>, cross-checked
with the standard convex minimizer framework in Boyd--Vandenberghe
<https://web.stanford.edu/~boyd/cvxbook/>.
-/
theorem bregman_projection_fiber_norm_bound (M : Matrix ι ι ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α : EuclideanSpace ℝ ι, NonzeroCoordinates α →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
            ∀ y : EuclideanSpace ℝ ι,
              (∃ u : EuclideanSpace ℝ ι, Nonnegative u ∧ matVec M u = y) →
              ∀ x : EuclideanSpace ℝ ι, Nonnegative x →
                IsMinOn
                    (fun z => entropyBregman z (ε • coordinateSquare α))
                    {z | Nonnegative z ∧ matVec M z = y} x →
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
  rcases hdata.lambda_nonneg.eq_or_lt with hlam0 | hlampos
  · -- `lambda = 0`: the hard case, combining Lemma 4.3 (`pos_trajectory_matVec_uniform_bound`),
    -- Lemma 4.4 (`bregman_projection_characterization`) and Lemma 4.5
    -- (`bregman_projection_fiber_norm_bound`) as in the proof of Prop. 4.1.
    subst hlam0
    obtain ⟨C₃, hC₃0, hC₃⟩ := pos_trajectory_matVec_uniform_bound M r α u hdata hα hu
    obtain ⟨C₄, hC₄0, hC₄all⟩ := bregman_projection_fiber_norm_bound M
    obtain ⟨ε₀breg, hε₀breg0, hC₄⟩ := hC₄all α hα
    refine ⟨C₄ * (1 + C₃ ^ 2), min ε₀breg 1, by positivity, lt_min hε₀breg0 one_pos, ?_⟩
    intro ε hε0 hεε₀ t ht
    have hε_breg : ε ≤ ε₀breg := hεε₀.trans (min_le_left _ _)
    have hε1 : ε ≤ 1 := hεε₀.trans (min_le_right _ _)
    have hchar := bregman_projection_characterization M r ε α (u ε) hdata (hu ε hε0)
      hε0 hα t
    have hzero_eq : posEffectiveParameter (u ε) 0 = ε • coordinateSquare α :=
      posEffectiveParameter_zero_eq_smul_coordinateSquare M r 0 ε α (u ε) (hu ε hε0) hε0.le
    rw [hzero_eq] at hchar
    have hy_feas : ∃ w : EuclideanSpace ℝ ι, Nonnegative w ∧
        matVec M w = matVec M (posEffectiveParameter (u ε) t) :=
      ⟨posEffectiveParameter (u ε) t, posEffectiveParameter_nonnegative _ _, rfl⟩
    have hbound := hC₄ ε hε0 hε_breg (matVec M (posEffectiveParameter (u ε) t)) hy_feas
      (posEffectiveParameter (u ε) t) (posEffectiveParameter_nonnegative _ _) hchar.1
    have hmatvec_bound := hC₃ ε hε0 hε1 t ht
    calc ‖posEffectiveParameter (u ε) t‖ ≤
        C₄ * (1 + ‖matVec M (posEffectiveParameter (u ε) t)‖ ^ 2) := hbound
      _ ≤ C₄ * (1 + C₃ ^ 2) := by
          have h1 : ‖matVec M (posEffectiveParameter (u ε) t)‖ ^ 2 ≤ C₃ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hmatvec_bound 2
          nlinarith [hC₄0, h1]
  · -- `lambda > 0`: the coercive case. Lemma 4.2 (`tiltedLoss_antitone_along_pos_flow`, valid
    -- for general `lambda`) bounds `\widetilde L` along the trajectory; completing the square
    -- (`quadraticLoss_complete_square`) bounds `ℓ` from below, so `lambda * ⟨1, x⟩` -- and
    -- hence `‖x‖ ≤ ⟨1, x⟩` -- is controlled.
    classical
    obtain ⟨y, hy⟩ := hdata.r_mem_span
    let a := coordinateSquare α
    have ha_inner_nonneg : 0 ≤ inner ℝ (ones : EuclideanSpace ℝ ι) a := by
      rw [← sum_eq_inner_ones]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (α i))
    let K := (1 / 2 : ℝ) * inner ℝ a (matVec M a) + |inner ℝ r a|
    have hK0 : 0 ≤ K := add_nonneg (mul_nonneg (by norm_num) (hdata.psd.nonneg a)) (abs_nonneg _)
    let K' := K + lambda * inner ℝ (ones : EuclideanSpace ℝ ι) a
    have hK'0 : 0 ≤ K' := add_nonneg hK0 (mul_nonneg hlampos.le ha_inner_nonneg)
    let K'' := K' + (1 / 2 : ℝ) * inner ℝ y (matVec M y)
    have hK''0 : 0 ≤ K'' := add_nonneg hK'0 (mul_nonneg (by norm_num) (hdata.psd.nonneg y))
    refine ⟨K'' / lambda + 1, 1, by linarith [div_nonneg hK''0 hlampos.le], one_pos, ?_⟩
    intro ε hε0 hεε₀ t ht
    have hflow := hu ε hε0
    have hx0 : posEffectiveParameter (u ε) 0 = ε • a :=
      posEffectiveParameter_zero_eq_smul_coordinateSquare M r lambda ε α (u ε) hflow hε0.le
    have hmono := tiltedLoss_antitone_along_pos_flow M r lambda ε α (u ε) hflow
      hdata.psd.get_symm ht
    simp only [hx0] at hmono
    have hquadinit : quadraticLoss M r (ε • a) ≤ K :=
      quadraticLoss_smul_le_energy_bound M r a hdata.psd hε0 hεε₀
    have hones_smul : inner ℝ (ones : EuclideanSpace ℝ ι) (ε • a) =
        ε * inner ℝ (ones : EuclideanSpace ℝ ι) a :=
      real_inner_smul_right (ones : EuclideanSpace ℝ ι) a ε
    have hlaminit : lambda * inner ℝ (ones : EuclideanSpace ℝ ι) (ε • a) ≤
        lambda * inner ℝ (ones : EuclideanSpace ℝ ι) a := by
      rw [hones_smul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by nlinarith [hεε₀, hlampos.le]) ha_inner_nonneg
    have hinit : tiltedLoss M r lambda (ε • a) ≤ K' := by
      dsimp only [K', tiltedLoss]
      linarith [hquadinit, hlaminit]
    have hcs := quadraticLoss_complete_square M r (posEffectiveParameter (u ε) t) y
      hdata.psd.get_symm hy
    have hnn : 0 ≤ inner ℝ (posEffectiveParameter (u ε) t - y)
        (matVec M (posEffectiveParameter (u ε) t - y)) := hdata.psd.nonneg _
    have hqlb : -(1 / 2 : ℝ) * inner ℝ y (matVec M y) ≤
        quadraticLoss M r (posEffectiveParameter (u ε) t) := by nlinarith [hcs, hnn]
    have htilt_eq : tiltedLoss M r lambda (posEffectiveParameter (u ε) t) =
        quadraticLoss M r (posEffectiveParameter (u ε) t) +
          lambda * inner ℝ (ones : EuclideanSpace ℝ ι) (posEffectiveParameter (u ε) t) := rfl
    have hlam_bound : lambda * inner ℝ (ones : EuclideanSpace ℝ ι)
        (posEffectiveParameter (u ε) t) ≤ K'' := by
      have := hmono.trans hinit
      rw [htilt_eq] at this
      dsimp only [K'']
      linarith [this, hqlb]
    have hones_bound : inner ℝ (ones : EuclideanSpace ℝ ι)
        (posEffectiveParameter (u ε) t) ≤ K'' / lambda := by
      rw [le_div_iff₀ hlampos]
      nlinarith [hlam_bound]
    have hx_nonneg : Nonnegative (posEffectiveParameter (u ε) t) :=
      posEffectiveParameter_nonnegative (u ε) t
    calc ‖posEffectiveParameter (u ε) t‖ ≤ ∑ i, posEffectiveParameter (u ε) t i :=
        norm_le_sum_of_nonneg _ hx_nonneg
      _ = inner ℝ (ones : EuclideanSpace ℝ ι) (posEffectiveParameter (u ε) t) :=
        sum_eq_inner_ones _
      _ ≤ K'' / lambda := hones_bound
      _ ≤ K'' / lambda + 1 := by linarith

end Lasso

end
