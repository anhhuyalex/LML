/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The neural tangent kernel (NTK)

This file formalizes the neural tangent kernel (NTK) corresponding to Section 4.3 of the
deep learning theory notes (Telgarsky 2021).

The NTK arises naturally from the gradient-feature view of the linearization `f₀`.
Because `f₀(x; W) = ⟨∇_W f(x; W₀), W⟩_F` is a linear predictor in the feature space
`{∇_W f(x; W₀) : x ∈ ℝᵈ}`, the corresponding kernel is the inner product between
feature maps:
  `kₘ(x, x') = ⟨∇_W f(x; W₀), ∇_W f(x'; W₀)⟩_F`.

As `m → ∞`, the rows `wⱼ₀` are i.i.d. Gaussian and the empirical average converges
almost surely to the **limiting NTK**:
  `k(x, x') = xᵀx' · 𝔼_w[σ'(wᵀx)σ'(wᵀx')]`.

For the ReLU, this expectation has the elegant closed form
  `k(x, x') = xᵀx' · (π − arccos(xᵀx')) / (2π)`
derived via a geometric argument on the sphere.

## Main definitions

* `NTK.empiricalNTKWithOuter` : the empirical NTK with arbitrary fixed outer coefficients.
* `NTK.empiricalNTK` : the simplified empirical NTK when `aⱼ² = 1`.
* `NTK.limitingNTK` : the limiting NTK `k(x, x')`.
* `NTK.ntkSummand` : the iid summand `σ'(wᵀx)σ'(wᵀx')` of the empirical average,
  with measurability/boundedness/integrability API (`measurable_ntkSummand`,
  `abs_ntkSummand_le`, `integrable_ntkSummand`).
* `NTK.ntk_convergence` : almost sure convergence `kₘ(x,x') → k(x,x')` (SLLN).
* `NTK.reluNTK_closedForm` : closed form `k(x,x') = xᵀx'·(π−arccos(xᵀx'))/(2π)` for ReLU.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter

namespace NTK

variable {d m : ℕ}

/-! ### Inner product and norm helpers -/

/-- The standard inner product on `Fin d → ℝ`. -/
noncomputable def innerProduct (x y : Fin d → ℝ) : ℝ :=
  ∑ k : Fin d, x k * y k

/-- Notation `x ⊙ y` for the standard inner product `innerProduct x y`. -/
infixl:73 " ⊙ " => innerProduct

lemma innerProduct_comm (x y : Fin d → ℝ) : x ⊙ y = y ⊙ x := by
  simp [innerProduct, mul_comm]

lemma innerProduct_self_nonneg (x : Fin d → ℝ) : 0 ≤ x ⊙ x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- `x ⊙ x` is the sum of the coordinate squares. -/
lemma innerProduct_self_eq_sum_sq (x : Fin d → ℝ) : x ⊙ x = ∑ k : Fin d, x k ^ 2 := by
  simp [innerProduct, pow_two]

/-- For the Euclidean `L²` norm on `EuclideanSpace ℝ (Fin d)`, `‖x‖² = x ⊙ x`.

The default norm on `Fin d → ℝ` is the sup norm, so the analogous statement is false for the raw
Pi type. -/
lemma norm_sq_eq_innerProduct (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = x.ofLp ⊙ x.ofLp := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa using (innerProduct_self_eq_sum_sq x.ofLp).symm

/-! ### Empirical NTK (Definition 4.5) -/

/-- The empirical NTK with arbitrary fixed outer coefficients:
  `kₘ,a(x,x') = (xᵀx') · (1/m)∑ⱼ aⱼ² σ'(wⱼ₀ᵀx)σ'(wⱼ₀ᵀx')`.

The lecture notes immediately simplify this expression using `aⱼ ∈ {±1}`. Keeping this
general form around makes the connection to `gradientMatrix` explicit. -/
noncomputable def empiricalNTKWithOuter
    (σ' : ℝ → ℝ)
    (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ)
    (x x' : Fin d → ℝ) : ℝ :=
  (x ⊙ x') *
    ((m : ℝ)⁻¹ * ∑ j : Fin m,
      outerCoeffs j ^ 2 *
      σ' (∑ k : Fin d, W₀ j k * x k) *
      σ' (∑ k : Fin d, W₀ j k * x' k))

/-- **Definition 4.5** (Empirical neural tangent kernel, `aⱼ² = 1` case).
Given initialization `W₀ : Fin m → Fin d → ℝ` and outer coefficients satisfying
`aⱼ² = 1`, the empirical NTK is the kernel obtained as the Frobenius inner product
of gradients:
  `kₘ(x, x') = ⟨∇_W f(x; W₀), ∇_W f(x'; W₀)⟩_F
              = (xᵀx') · (1/m) ∑ⱼ σ'(wⱼ₀ᵀx) σ'(wⱼ₀ᵀx')`.

The second equality uses `aⱼ² = 1` and `⟨xσ'(·), x'σ'(·)⟩ = (xᵀx')σ'(·)σ'(·)`. -/
noncomputable def empiricalNTK
    (σ' : ℝ → ℝ)
    (W₀ : Fin m → Fin d → ℝ)
    (x x' : Fin d → ℝ) : ℝ :=
  (x ⊙ x') *
    ((m : ℝ)⁻¹ * ∑ j : Fin m,
      σ' (∑ k : Fin d, W₀ j k * x k) *
      σ' (∑ k : Fin d, W₀ j k * x' k))

-- The square of the square root of the inverse of m (cast to real) is the inverse of m.
private lemma sq_sqrt_inv_cast_nat (m : ℕ) :
    ((m : ℝ)⁻¹.sqrt) * ((m : ℝ)⁻¹.sqrt) = (m : ℝ)⁻¹ := by
  rw [← sq, Real.sq_sqrt]
  exact inv_nonneg.mpr (Nat.cast_nonneg m)

-- Term-level algebraic identity for the Frobenius inner product of gradients.
private lemma gradient_matrix_term_eq (m : ℕ) (outerCoeffs_j : ℝ) (val_x val_x' : ℝ)
    (x_k x'_k : ℝ) :
    ((m : ℝ)⁻¹.sqrt * outerCoeffs_j * val_x * x_k) *
    ((m : ℝ)⁻¹.sqrt * outerCoeffs_j * val_x' * x'_k) =
    (x_k * x'_k) * ((m : ℝ)⁻¹ * outerCoeffs_j ^ 2 * val_x * val_x') := by
  calc
    _ = ((m : ℝ)⁻¹.sqrt * (m : ℝ)⁻¹.sqrt) *
          (outerCoeffs_j * outerCoeffs_j) * val_x * val_x' * (x_k * x'_k) := by
      ring
    _ = (m : ℝ)⁻¹ * outerCoeffs_j ^ 2 * val_x * val_x' * (x_k * x'_k) := by
      rw [sq_sqrt_inv_cast_nat m, ← sq]
    _ = _ := by ring

/-- The Frobenius inner product of gradient features is the empirical NTK with the
outer-coefficient squares included. -/
lemma frobeniusInner_gradientMatrix_eq_empiricalNTKWithOuter
    (σ' : ℝ → ℝ) (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ) :
    frobeniusInner
      (gradientMatrix (σ' := σ') outerCoeffs x W₀)
      (gradientMatrix (σ' := σ') outerCoeffs x' W₀) =
    empiricalNTKWithOuter σ' outerCoeffs W₀ x x' := by
  unfold frobeniusInner gradientMatrix empiricalNTKWithOuter innerProduct
  simp_rw [gradient_matrix_term_eq]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]
  congr 1; ext i
  ring

/-- If all fixed outer coefficients satisfy `aⱼ² = 1`, the general empirical NTK
reduces to the simplified expression used in the notes. -/
lemma empiricalNTKWithOuter_eq_empiricalNTK_of_sq_one
    (σ' : ℝ → ℝ) (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ)
    (houter : ∀ j : Fin m, outerCoeffs j ^ 2 = 1) :
    empiricalNTKWithOuter σ' outerCoeffs W₀ x x' =
    empiricalNTK σ' W₀ x x' := by
  simp [empiricalNTKWithOuter, empiricalNTK, houter]

/-- The empirical NTK is symmetric: `kₘ(x, x') = kₘ(x', x)`. -/
lemma empiricalNTK_symm
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ) :
    empiricalNTK σ' W₀ x x' = empiricalNTK σ' W₀ x' x := by
  simp only [empiricalNTK, innerProduct_comm x x', mul_comm (σ' _) (σ' _)]

-- Helper 1: Reorder
private lemma quadruple_sum_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ i : α, ∑ i' : β, ∑ j : γ, ∑ k : δ, f i i' j k =
      ∑ j : γ, ∑ k : δ, ∑ i : α, ∑ i' : β, f i i' j k := by
  calc
    ∑ i : α, ∑ i' : β, ∑ j : γ, ∑ k : δ, f i i' j k
        = ∑ x : α × β, ∑ j : γ, ∑ k : δ, f x.1 x.2 j k := by
            rw [← Fintype.sum_prod_type']
    _ = ∑ x : α × β, ∑ y : γ × δ, f x.1 x.2 y.1 y.2 := by
          congr 1
          ext x
          rw [← Fintype.sum_prod_type']
    _ = ∑ z : (α × β) × (γ × δ), f z.1.1 z.1.2 z.2.1 z.2.2 := by
          rw [← Fintype.sum_prod_type']
    _ = ∑ y : γ × δ, ∑ x : α × β, f x.1 x.2 y.1 y.2 := by
          simpa using
            (Fintype.sum_prod_type_right'
              (f := fun (x : α × β) (y : γ × δ) =>
                f x.1 x.2 y.1 y.2))
    _ = ∑ j : γ, ∑ k : δ, ∑ x : α × β, f x.1 x.2 j k := by
          simpa using
            (Fintype.sum_prod_type' (f := fun j k => ∑ x : α × β, f x.1 x.2 j k))
    _ = ∑ j : γ, ∑ k : δ, ∑ i : α, ∑ i' : β, f i i' j k := by
          congr 1
          ext j
          congr 1
          ext k
          simpa using (Fintype.sum_prod_type' (f := fun i i' => f i i' j k))

-- Helper 2: Expand
private lemma empiricalNTK_term_expand
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ) {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ)
    (i i' : Fin n) :
    α i * α i' * empiricalNTK σ' W₀ (pts i) (pts i') =
      ∑ j : Fin m, ∑ k : Fin d,
        (m : ℝ)⁻¹ *
          (α i * α i' * (pts i k * pts i' k) *
            (σ' (∑ l : Fin d, W₀ j l * pts i l) *
              σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
  unfold empiricalNTK innerProduct
  calc
    α i * α i' *
        ((∑ k : Fin d, pts i k * pts i' k) *
          ((m : ℝ)⁻¹ *
            ∑ j : Fin m, σ' (∑ k : Fin d, W₀ j k * pts i k) * σ' (∑ k : Fin d, W₀ j k * pts i' k)))
        =
          (α i * α i' * ∑ k : Fin d, pts i k * pts i' k) * (m : ℝ)⁻¹ *
            ∑ j : Fin m,
              σ' (∑ k : Fin d, W₀ j k * pts i k) *
                σ' (∑ k : Fin d, W₀ j k * pts i' k) := by
            ring
    _ =
      (α i * α i' * ∑ k : Fin d, pts i k * pts i' k) * (m : ℝ)⁻¹ *
        ∑ j : Fin m, σ' (∑ k : Fin d, W₀ j k * pts i k) * σ' (∑ k : Fin d, W₀ j k * pts i' k)
        := by rfl
    _ =
        ((m : ℝ)⁻¹ * α i * α i') *
            ((∑ k : Fin d, pts i k * pts i' k) *
              ∑ j : Fin m, σ' (∑ k : Fin d, W₀ j k * pts i k) *
                σ' (∑ k : Fin d, W₀ j k * pts i' k)) := by
            ring
    _ =
        ((m : ℝ)⁻¹ * α i * α i') *
          ∑ k : Fin d,
            ∑ j : Fin m,
              (pts i k * pts i' k) *
                (σ' (∑ k : Fin d, W₀ j k * pts i k) *
                  σ' (∑ k : Fin d, W₀ j k * pts i' k)) := by
            rw [Fintype.sum_mul_sum]
    _ =
        ((m : ℝ)⁻¹ * α i * α i') *
          ∑ j : Fin m,
            ∑ k : Fin d,
              (pts i k * pts i' k) *
                (σ' (∑ k : Fin d, W₀ j k * pts i k) *
                  σ' (∑ k : Fin d, W₀ j k * pts i' k)) := by
            rw [Finset.sum_comm]
    _ = ∑ j : Fin m, ∑ k : Fin d,
          (m : ℝ)⁻¹ *
            (α i * α i' * (pts i k * pts i' k) *
              (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

-- Helper 3: Square
private lemma empiricalNTK_term_square
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ) {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ)
    (j : Fin m) (k : Fin d) :
    ∑ i : Fin n, ∑ i' : Fin n,
      (m : ℝ)⁻¹ *
        (α i * α i' * (pts i k * pts i' k) *
          (σ' (∑ l : Fin d, W₀ j l * pts i l) *
            σ' (∑ l : Fin d, W₀ j l * pts i' l))) =
      (m : ℝ)⁻¹ *
        (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
  calc
    ∑ i : Fin n, ∑ i' : Fin n,
      (m : ℝ)⁻¹ *
        (α i * α i' * (pts i k * pts i' k) *
          (σ' (∑ l : Fin d, W₀ j l * pts i l) *
            σ' (∑ l : Fin d, W₀ j l * pts i' l)))
        = ∑ i : Fin n, ∑ i' : Fin n,
            (m : ℝ)⁻¹ *
              ((α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro i' _
            ring
    _ = (m : ℝ)⁻¹ *
          ∑ i : Fin n, ∑ i' : Fin n,
            (α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
              (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)) := by
            calc
              ∑ i : Fin n, ∑ i' : Fin n,
                  (m : ℝ)⁻¹ *
                    ((α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                      (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)))
                  =
                    ∑ i : Fin n,
                      (m : ℝ)⁻¹ *
                        ∑ i' : Fin n,
                          (α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                            (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [← Finset.mul_sum]
              _ = (m : ℝ)⁻¹ *
                    ∑ i : Fin n, ∑ i' : Fin n,
                      (α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                        (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)) := by
                      rw [← Finset.mul_sum]
    _ = (m : ℝ)⁻¹ *
          (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
            rw [pow_two, Fintype.sum_mul_sum]

/-- The empirical NTK is positive semidefinite: for any finite set of points
and coefficients `(αᵢ, xᵢ)`, `∑ᵢⱼ αᵢαⱼ kₘ(xᵢ, xⱼ) ≥ 0`.
This follows from being the Gram matrix of the gradient features. -/
lemma empiricalNTK_posSemidef
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ)
    {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      α i * α j * empiricalNTK σ' W₀ (pts i) (pts j) := by
  have h_eq : ∑ i : Fin n, ∑ j : Fin n, α i * α j * empiricalNTK σ' W₀ (pts i) (pts j) =
      (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
        (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, α i * α j * empiricalNTK σ' W₀ (pts i) (pts j)
          = ∑ i : Fin n, ∑ i' : Fin n, ∑ j : Fin m, ∑ k : Fin d,
              (m : ℝ)⁻¹ *
                (α i * α i' * (pts i k * pts i' k) *
                  (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                    σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
              -- Step 1: Expand the kernel into a quadruple sum.
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro i' _
              exact empiricalNTK_term_expand σ' W₀ α pts i i'
      _ = ∑ j : Fin m, ∑ k : Fin d, ∑ i : Fin n, ∑ i' : Fin n,
            (m : ℝ)⁻¹ *
              (α i * α i' * (pts i k * pts i' k) *
                (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                  σ' (∑ l : Fin d, W₀ j l * pts i' l))) := quadruple_sum_comm _
      _ = (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
            (∑ i : Fin n,
              α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
              -- Step 2: Repackage the quadruple sum as a sum of squares.
              calc
                ∑ j : Fin m, ∑ k : Fin d, ∑ i : Fin n, ∑ i' : Fin n,
                    (m : ℝ)⁻¹ *
                      (α i * α i' * (pts i k * pts i' k) *
                        (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                          σ' (∑ l : Fin d, W₀ j l * pts i' l)))
                    = ∑ j : Fin m, ∑ k : Fin d,
                        (m : ℝ)⁻¹ *
                          (∑ i : Fin n,
                            α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                            apply Finset.sum_congr rfl
                            intro j _
                            apply Finset.sum_congr rfl
                            intro k _
                            exact empiricalNTK_term_square σ' W₀ α pts j k
                _ = (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
                      (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                            calc
                              ∑ j : Fin m, ∑ k : Fin d,
                                  (m : ℝ)⁻¹ *
                                    (∑ i : Fin n,
                                      α i * pts i k *
                                        σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2
                                  =
                                    ∑ j : Fin m,
                                      (m : ℝ)⁻¹ *
                                        ∑ k : Fin d,
                                          (∑ i : Fin n,
                                            α i * pts i k *
                                              σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                                      apply Finset.sum_congr rfl
                                      intro j _
                                      rw [← Finset.mul_sum]
                              _ = (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
                                    (∑ i : Fin n,
                                      α i * pts i k *
                                        σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                                      rw [← Finset.mul_sum]
  rw [h_eq]
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg m)
  · apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact sq_nonneg _

/-! ### Limiting NTK (Definition 4.6) -/

/-- **Definition 4.6** (Limiting neural tangent kernel).
The limiting NTK is the expectation of the gradient-feature inner product
as `m → ∞`:
  `k(x, x') = (xᵀx') · 𝔼_{w ~ 𝒩(0,Iᵈ)}[σ'(wᵀx) σ'(wᵀx')]`.

This is positive semidefinite and symmetric. For the ReLU, it has the closed form
given in `reluNTK_closedForm`. -/
noncomputable def limitingNTK (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) : ℝ :=
  (x ⊙ x') *
    ∫ w : Fin d → ℝ,
      σ' (w ⊙ x) * σ' (w ⊙ x') ∂(gaussianRowMeasure d)

/-- The limiting NTK is symmetric. -/
lemma limitingNTK_symm (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) :
    limitingNTK σ' x x' = limitingNTK σ' x' x := by
  simp only [limitingNTK, innerProduct_comm x x', mul_comm (σ' _) (σ' _)]

/-! ### Measurability and integrability of the NTK summand -/

/-- The standard Gaussian row measure `𝒩(0, Iᵈ)` is a probability measure. -/
instance : IsProbabilityMeasure (gaussianRowMeasure d) := by
  unfold gaussianRowMeasure
  infer_instance

/-- The dot product `w ↦ wᵀx` with a fixed vector is measurable. -/
lemma measurable_innerProduct_left (x : Fin d → ℝ) :
    Measurable fun w : Fin d → ℝ => w ⊙ x :=
  Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).mul measurable_const

/-- The iid summand appearing in the empirical NTK average:
  `Y(w) = σ'(wᵀx) · σ'(wᵀx')`.
The empirical NTK is `xᵀx'` times the empirical mean of `Y` over the rows, and the
limiting NTK is `xᵀx'` times the expectation of `Y`. -/
noncomputable def ntkSummand (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) (w : Fin d → ℝ) : ℝ :=
  σ' (w ⊙ x) * σ' (w ⊙ x')

/-- The NTK summand is measurable whenever `σ'` is. -/
lemma measurable_ntkSummand {σ' : ℝ → ℝ} (hσ' : Measurable σ') (x x' : Fin d → ℝ) :
    Measurable (ntkSummand σ' x x') :=
  (hσ'.comp (measurable_innerProduct_left x)).mul (hσ'.comp (measurable_innerProduct_left x'))

/-- If `σ'` is bounded by `C`, the NTK summand is bounded by `C²`. -/
lemma abs_ntkSummand_le {σ' : ℝ → ℝ} {C : ℝ} (hC : ∀ z, |σ' z| ≤ C)
    (x x' : Fin d → ℝ) (w : Fin d → ℝ) :
    |ntkSummand σ' x x' w| ≤ C * C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (σ' 0)) (hC 0)
  rw [ntkSummand, abs_mul]
  exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0

/-- A bounded measurable NTK summand is integrable against the Gaussian row measure. -/
lemma integrable_ntkSummand {σ' : ℝ → ℝ} (hσ'm : Measurable σ') {C : ℝ}
    (hC : ∀ z, |σ' z| ≤ C) (x x' : Fin d → ℝ) :
    Integrable (ntkSummand σ' x x') (gaussianRowMeasure d) :=
  Integrable.of_bound (measurable_ntkSummand hσ'm x x').aestronglyMeasurable (C * C)
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact abs_ntkSummand_le hC x x' w)

/-! ### Almost sure convergence of the empirical NTK (Lemma 4.3) -/

/-- The width-`m` empirical NTK built from the first `m` rows of an infinite iid
initialization. This is the right object for the notes' `m → ∞` limit. -/
noncomputable def empiricalNTKFromRows
    (σ' : ℝ → ℝ)
    (rows : ℕ → Fin d → ℝ)
    (width : ℕ)
    (x x' : Fin d → ℝ) : ℝ :=
  (x ⊙ x') *
    ((width : ℝ)⁻¹ * ∑ j : Fin width,
      σ' (rows j.val ⊙ x) * σ' (rows j.val ⊙ x'))

/-- **Lemma 4.3** (Almost sure convergence of the empirical NTK).
For fixed `x, x' ∈ ℝᵈ`, a measurable bounded `σ'`, and an infinite sequence of iid
rows `w₀, w₁, ... ~ 𝒩(0,Iᵈ)`:
  `kₘ(x, x') →_as k(x, x')  as  m → ∞`.

**Proof:** The summands `Yⱼ = σ'(wⱼ₀ᵀx)σ'(wⱼ₀ᵀx')` are measurable functions of the
independent rows `wⱼ₀`, hence pairwise independent; they are identically distributed
(each row has law `𝒩(0,Iᵈ)`) and integrable (bounded by `C²` on a probability space).
The strong law of large numbers (Etemadi's version, `ProbabilityTheory.strong_law_ae`,
which only needs pairwise independence) gives `(1/m)∑ⱼ Yⱼ →_as 𝔼[Y₀]`, and multiplying
by the constant `xᵀx'` yields the claim, since
`𝔼[Y₀] = 𝔼_{w ~ 𝒩(0,Iᵈ)}[σ'(wᵀx)σ'(wᵀx')]`.

The measurability hypothesis `hσ'_meas` is implicit in the informal notes (their `σ'`
is the ReLU derivative `𝟏[· ≥ 0]`, which is measurable: `measurable_reluIndicator`);
it is needed for the integrability required by the strong law. -/
theorem ntk_convergence
    (σ' : ℝ → ℝ)
    (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C)
    (x x' : Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)),
      Filter.Tendsto
        (fun width => empiricalNTKFromRows σ' rows width x x')
        Filter.atTop
        (nhds (limitingNTK σ' x x')) := by
  obtain ⟨C, hC⟩ := hσ'_bounded
  have hg_meas : Measurable (ntkSummand σ' x x') := measurable_ntkSummand hσ'_meas x x'
  set μ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d) with hμ
  -- Each row `rows i` has law `gaussianRowMeasure d` under the product measure.
  have hmap_eval : ∀ i : ℕ, μ.map (fun rows => rows i) = gaussianRowMeasure d :=
    fun i => Measure.infinitePi_map_eval _ i
  -- The summands are measurable and bounded, hence integrable.
  have hX_meas : ∀ j : ℕ,
      Measurable (fun rows : ℕ → Fin d → ℝ => ntkSummand σ' x x' (rows j)) :=
    fun j => hg_meas.comp (measurable_pi_apply j)
  have hint : Integrable (fun rows : ℕ → Fin d → ℝ => ntkSummand σ' x x' (rows 0)) μ :=
    Integrable.of_bound (hX_meas 0).aestronglyMeasurable (C * C)
      (Filter.Eventually.of_forall fun rows => by
        rw [Real.norm_eq_abs]; exact abs_ntkSummand_le hC x x' (rows 0))
  -- The summands are pairwise independent, being functions of independent rows.
  have hindep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·)
      fun j rows => ntkSummand σ' x x' (rows j)) := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ => gaussianRowMeasure d)
      (X := fun _ : ℕ => ntkSummand σ' x x') (fun _ => hg_meas)
    intro i j hij
    exact h.indepFun hij
  -- The summands are identically distributed, since the rows are.
  have hident : ∀ i : ℕ,
      IdentDistrib (fun rows : ℕ → Fin d → ℝ => ntkSummand σ' x x' (rows i))
        (fun rows : ℕ → Fin d → ℝ => ntkSummand σ' x x' (rows 0)) μ μ := by
    intro i
    have hcoord : IdentDistrib (fun rows : ℕ → Fin d → ℝ => rows i)
        (fun rows : ℕ → Fin d → ℝ => rows 0) μ μ := by
      refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
        ?_⟩
      rw [hmap_eval i, hmap_eval 0]
    exact hcoord.comp hg_meas
  -- Etemadi's strong law: the empirical means converge a.s. to the common mean.
  have hslln : ∀ᵐ rows ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, ntkSummand σ' x x' (rows i))
      Filter.atTop (nhds (∫ rows, ntkSummand σ' x x' (rows 0) ∂μ)) :=
    strong_law_ae _ hint hindep hident
  -- The common mean is the expectation over a single Gaussian row.
  have hexp : ∫ rows, ntkSummand σ' x x' (rows 0) ∂μ =
      ∫ w, ntkSummand σ' x x' w ∂(gaussianRowMeasure d) := by
    rw [← hmap_eval 0]
    exact (MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable
      hg_meas.stronglyMeasurable.aestronglyMeasurable).symm
  filter_upwards [hslln] with rows hrows
  -- Repackage the `Finset.range` average as a `Fin width` average.
  have hfin : Filter.Tendsto
      (fun width : ℕ => (width : ℝ)⁻¹ * ∑ j : Fin width, ntkSummand σ' x x' (rows j))
      Filter.atTop (nhds (∫ w, ntkSummand σ' x x' w ∂(gaussianRowMeasure d))) := by
    rw [← hexp]
    have hcongr :
        (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, ntkSummand σ' x x' (rows i))
        = fun width : ℕ =>
            (width : ℝ)⁻¹ * ∑ j : Fin width, ntkSummand σ' x x' (rows j) := by
      ext n
      rw [smul_eq_mul, Fin.sum_univ_eq_sum_range (fun i => ntkSummand σ' x x' (rows i)) n]
    rw [← hcongr]
    exact hrows
  -- Multiply by the constant `xᵀx'`: this is exactly `empiricalNTKFromRows → limitingNTK`.
  exact hfin.const_mul (x ⊙ x')

/-! ### ReLU NTK closed form (Proposition 4.2) -/

/-- The ReLU derivative: `𝟏[z ≥ 0]` (a.e. equal to the actual derivative). -/
noncomputable def reluIndicator : ℝ → ℝ := fun z => if 0 ≤ z then 1 else 0

/-- The ReLU derivative is measurable: it is the indicator of the closed
measurable set `[0, ∞)`. Together with `abs_reluIndicator_le` this shows that
`reluIndicator` satisfies the hypotheses of `ntk_convergence`. -/
lemma measurable_reluIndicator : Measurable reluIndicator := by
  have h : reluIndicator = Set.indicator (Set.Ici 0) fun _ => (1 : ℝ) := by
    ext z
    simp [reluIndicator, Set.indicator]
  rw [h]
  exact Measurable.indicator measurable_const measurableSet_Ici

/-- The ReLU derivative is bounded by `1`. -/
lemma abs_reluIndicator_le (z : ℝ) : |reluIndicator z| ≤ 1 := by
  simp only [reluIndicator]
  split_ifs <;> simp

/-- The angle between two unit vectors in ℝᵈ:
  `angle x x' = arccos(xᵀx')` for `x ⊙ x = x' ⊙ x' = 1`. -/
noncomputable def vectorAngle (x x' : Fin d → ℝ) : ℝ :=
  Real.arccos (x ⊙ x')

/-- **Proposition 4.2** (ReLU NTK closed form, Telgarsky 2021).
For `σ' = 𝟏[· ≥ 0]` (the ReLU derivative) and `x, x' ∈ ℝᵈ` with
`x ⊙ x = x' ⊙ x' = 1`:
  `k(x, x') = (xᵀx') · (π − arccos(xᵀx')) / (2π)`.

**Proof sketch:**
- By rotational invariance of `𝒩(0, Iᵈ)`, we may project `w` onto `span(x, x')`.
- In the 2D plane, `w` is effectively uniform on the unit circle.
- The event `{wᵀx ≥ 0} ∩ {wᵀx' ≥ 0}` is a sector of angle `π − θ` where `θ = arccos(xᵀx')`.
- The probability of this sector is `(π − θ)/(2π)`.
- Multiplying by `xᵀx'` gives the result. -/
theorem reluNTK_closedForm
    (x x' : Fin d → ℝ)
    (hx : x ⊙ x = 1)
    (hx' : x' ⊙ x' = 1) :
    limitingNTK reluIndicator x x' =
      (x ⊙ x') * (Real.pi - Real.arccos (x ⊙ x')) / (2 * Real.pi) := by
  sorry

/-- The ReLU NTK is nonneg when `xᵀx' ≥ 0`. -/
lemma reluNTK_nonneg_of_nonneg_inner
    (x x' : Fin d → ℝ)
    (hx : x ⊙ x = 1) (hx' : x' ⊙ x' = 1)
    (hinn : 0 ≤ x ⊙ x') :
    0 ≤ limitingNTK reluIndicator x x' := by
  rw [reluNTK_closedForm x x' hx hx']
  apply div_nonneg
  · apply mul_nonneg hinn
    linarith [Real.arccos_le_pi (x ⊙ x'), Real.pi_pos]
  · linarith [Real.pi_pos]

/-- The ReLU NTK at equal inputs normalized by the local inner product. -/
lemma reluNTK_self
    (x : Fin d → ℝ) (hx : x ⊙ x = 1) :
    limitingNTK reluIndicator x x = 1 / 2 := by
  rw [reluNTK_closedForm x x hx hx]
  rw [hx]
  simp [Real.arccos_one]
  ring_nf
  simp [Real.pi_pos.ne']

end NTK

end
