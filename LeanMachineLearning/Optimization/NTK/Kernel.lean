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
private lemma gradient_matrix_term_eq (m : ℕ) (outerCoeffs_j : ℝ) (val_x val_x' : ℝ) (x_k x'_k : ℝ) :
    ((m : ℝ)⁻¹.sqrt * outerCoeffs_j * val_x * x_k) *
    ((m : ℝ)⁻¹.sqrt * outerCoeffs_j * val_x' * x'_k) =
    (x_k * x'_k) * ((m : ℝ)⁻¹ * outerCoeffs_j ^ 2 * val_x * val_x') := by
  calc
    _ = ((m : ℝ)⁻¹.sqrt * (m : ℝ)⁻¹.sqrt) * (outerCoeffs_j * outerCoeffs_j) * val_x * val_x' * (x_k * x'_k) := by ring
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
            ∑ j : Fin m, σ' (∑ k : Fin d, W₀ j k * pts i k) * σ' (∑ k : Fin d, W₀ j k * pts i' k) := by
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
              -- Step 1: Expand the kernel into a quadruple sum over samples, neurons, and coordinates.
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
            (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
              -- Step 2: Repackage the quadruple sum as a sum of squares.
              calc
                ∑ j : Fin m, ∑ k : Fin d, ∑ i : Fin n, ∑ i' : Fin n,
                    (m : ℝ)⁻¹ *
                      (α i * α i' * (pts i k * pts i' k) *
                        (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                          σ' (∑ l : Fin d, W₀ j l * pts i' l)))
                    = ∑ j : Fin m, ∑ k : Fin d,
                        (m : ℝ)⁻¹ *
                          (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
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
                                    (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2
                                  =
                                    ∑ j : Fin m,
                                      (m : ℝ)⁻¹ *
                                        ∑ k : Fin d,
                                          (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                                      apply Finset.sum_congr rfl
                                      intro j _
                                      rw [← Finset.mul_sum]
                              _ = (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
                                    (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
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
For fixed `x, x' ∈ ℝᵈ` and an infinite sequence of iid rows
`w₀, w₁, ... ~ 𝒩(0,Iᵈ)`:
  `kₘ(x, x') →_as k(x, x')  as  m → ∞`.

**Proof:** The summands `σ'(wⱼ₀ᵀx)σ'(wⱼ₀ᵀx')` are i.i.d. with mean
`𝔼[σ'(wᵀx)σ'(wᵀx')]`; apply the strong law of large numbers. -/
theorem ntk_convergence
    (σ' : ℝ → ℝ)
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C)
    (x x' : Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)),
      Filter.Tendsto
        (fun width => empiricalNTKFromRows σ' rows width x x')
        Filter.atTop
        (nhds (limitingNTK σ' x x')) := by
  sorry

/-! ### ReLU NTK closed form (Proposition 4.2) -/

/-- The ReLU derivative: `𝟏[z ≥ 0]` (a.e. equal to the actual derivative). -/
noncomputable def reluIndicator : ℝ → ℝ := fun z => if 0 ≤ z then 1 else 0

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
