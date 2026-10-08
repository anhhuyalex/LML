/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.GramProjector
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.SampleBottleneck

/-!
# Row-space and residual decomposition in the sample-bottleneck regime

Deterministic half of the sample-bottleneck analysis (Lemma 3.7 of the plan; [Bach, 2024]). In the
regime `m < min {n₀, n}` write `X ∈ ℝ^{m×n₀}` for the design, `S ∈ ℝ^{n₀×n}` for the random
features, `Z = X S`, `Z† = Zᵀ (Z Zᵀ)⁻¹` for the minimum-norm interpolator and `M = S Z†` for the
measurement operator of `θ̂ = M y`. With `P = P_X = Xᵀ (X Xᵀ)⁻¹ X` the projector onto the row space
of `X` (`Matrix.gramProjector Xᵀ`) and `Pᗮ = 1 - P`:

* `operator_eq_rowSpace_add_residual`: `M = Xᵀ (X Xᵀ)⁻¹ + Pᗮ M`, because `P S = Xᵀ (X Xᵀ)⁻¹ Z` and
  `Z Z† = 1` (`gramProjector_transpose_mul_operator`);
* `trace_operator_transpose_mul_self_eq_add`: since `X Pᗮ = 0` the two summands are orthogonal,
  `Tr (Mᵀ M) = Tr ((X Xᵀ)⁻¹) + Tr ((Pᗮ M)ᵀ (Pᗮ M))`, where the second term is the variance
  contributed by the part of `S` outside the row space of `X`
  (`trace_residual_operator_eq`: `Tr ((Z† Z†ᵀ) (Sᵀ Pᗮ S))`);
* `operator_mul_design_sub_one_mulVec`: the bias vector is `(M X - 1) θ = Pᗮ S b - Pᗮ θ` with
  `b = Z† X θ`.

Nothing here is probabilistic. The random half (Gaussian `S`, so `Pᗮ S` is independent of `Z`)
lives in `SampleBottleneckLimits.lean`.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Matrix
open scoped Matrix

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq m] [DecidableEq n₀]

omit [DecidableEq n₀] in
/-- **Row-space part of the measurement operator.** If `Z = X S` has full row rank, the row-space
projector of `X` sends the minimum-norm operator `M = S Zᵀ (Z Zᵀ)⁻¹` to `Xᵀ (X Xᵀ)⁻¹`:
`P_X S Z† = Xᵀ (X Xᵀ)⁻¹` because `X S Z† = Z Z† = 1`. -/
theorem gramProjector_transpose_mul_operator (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hZ : IsUnit ((X * S) * (X * S)ᵀ).det) :
    gramProjector Xᵀ * (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) = Xᵀ * (X * Xᵀ)⁻¹ := by
  calc gramProjector Xᵀ * (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹))
      = Xᵀ * (X * Xᵀ)⁻¹ * ((X * S) * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) := by
        rw [gramProjector_transpose_eq]; simp only [Matrix.mul_assoc]
    _ = Xᵀ * (X * Xᵀ)⁻¹ := by rw [self_mul_rightInverse (X * S) hZ, Matrix.mul_one]

/-- **Row-space/residual splitting of the measurement operator.** With `M = S Z†` and
`P = P_X`, `M = Xᵀ (X Xᵀ)⁻¹ + (1 - P) M`. -/
theorem operator_eq_rowSpace_add_residual (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hZ : IsUnit ((X * S) * (X * S)ᵀ).det) :
    S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹) =
      Xᵀ * (X * Xᵀ)⁻¹ +
        (1 - gramProjector Xᵀ) * (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) := by
  rw [Matrix.sub_mul, Matrix.one_mul, gramProjector_transpose_mul_operator X S hZ]
  abel

/-- **Pythagoras for the measurement operator.** If `X Xᵀ` and `Z Zᵀ`, `Z = X S`, are invertible,
`Tr (Mᵀ M) = Tr ((X Xᵀ)⁻¹) + Tr (((1 - P_X) M)ᵀ ((1 - P_X) M))` for `M = S Zᵀ (Z Zᵀ)⁻¹`: the row
space part `Xᵀ (X Xᵀ)⁻¹` is orthogonal to the residual part because `X (1 - P_X) = 0`. -/
theorem trace_operator_transpose_mul_self_eq_add (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hX : IsUnit (X * Xᵀ).det) (hZ : IsUnit ((X * S) * (X * S)ᵀ).det) :
    ((S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹))ᵀ *
        (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹))).trace =
      ((X * Xᵀ)⁻¹).trace +
        (((1 - gramProjector Xᵀ) * (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)))ᵀ *
          ((1 - gramProjector Xᵀ) * (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)))).trace := by
  set M : Matrix n₀ m ℝ := S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹) with hM
  set A : Matrix n₀ m ℝ := Xᵀ * (X * Xᵀ)⁻¹ with hA
  set R : Matrix n₀ m ℝ := (1 - gramProjector Xᵀ) * M with hR
  have hsymm : ((X * Xᵀ)⁻¹)ᵀ = (X * Xᵀ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hAT : Aᵀ = (X * Xᵀ)⁻¹ * X := by
    rw [hA, Matrix.transpose_mul, hsymm, Matrix.transpose_transpose]
  have hAR : Aᵀ * R = 0 := by
    rw [hAT, hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ X,
      mul_one_sub_gramProjector_transpose X hX]
    simp
  have hAA : Aᵀ * A = (X * Xᵀ)⁻¹ := by
    rw [hAT, hA, Matrix.mul_assoc, ← Matrix.mul_assoc X, Matrix.mul_nonsing_inv _ hX,
      Matrix.mul_one]
  have hRA : Rᵀ * A = 0 := by
    have := congrArg Matrix.transpose hAR
    rwa [Matrix.transpose_mul, Matrix.transpose_zero, Matrix.transpose_transpose] at this
  have hMAR : M = A + R := operator_eq_rowSpace_add_residual X S hZ
  have : Mᵀ * M = Aᵀ * A + Rᵀ * R := by
    rw [hMAR, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAR, hRA]
    rw [add_zero, zero_add]
  rw [this, Matrix.trace_add, hAA]

/-- **Trace of the residual part.** For `R = (1 - P_X) S Z†`,
`Tr (Rᵀ R) = Tr ((Z† Z†ᵀ) (Sᵀ (1 - P_X) S))`, as `(1 - P_X)` is a symmetric idempotent. -/
theorem trace_residual_operator_eq (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hX : IsUnit (X * Xᵀ).det) :
    (((1 - gramProjector Xᵀ) * (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)))ᵀ *
          ((1 - gramProjector Xᵀ) * (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)))).trace =
      ((((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹) * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)ᵀ) *
        (Sᵀ * (1 - gramProjector Xᵀ) * S)).trace := by
  set D : Matrix n₀ n₀ ℝ := 1 - gramProjector Xᵀ with hD
  set Zd : Matrix n m ℝ := (X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹ with hZd
  have hDP : IsStarProjection D :=
    (isOrthogonalProjection_gramProjector Xᵀ (by simpa using hX)).one_sub
  have hDD : Dᵀ * D = D := by
    rw [hDP.transpose_eq]; exact ((isStarProjection_matrix_real_iff _).1 hDP).2
  have h1 : (D * (S * Zd))ᵀ * (D * (S * Zd)) = Zdᵀ * (Sᵀ * D * S) * Zd := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    calc Zdᵀ * Sᵀ * Dᵀ * (D * (S * Zd)) = Zdᵀ * Sᵀ * (Dᵀ * D) * (S * Zd) := by
          simp only [Matrix.mul_assoc]
      _ = Zdᵀ * (Sᵀ * D * S) * Zd := by rw [hDD]; simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- **Residual action on the targets.** In the model `y = X θ` write `b = Z† X θ` for the
interpolating coefficients. Then `(M X - 1) θ = (1 - P_X) S b - (1 - P_X) θ`: the bias vector is
the residual of `θ` plus the residual part of the random-feature fit. -/
theorem operator_mul_design_sub_one_mulVec (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hZ : IsUnit ((X * S) * (X * S)ᵀ).det) (θ : n₀ → ℝ) :
    ((S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) * X - 1) *ᵥ θ =
      ((1 - gramProjector Xᵀ) * S) *ᵥ (((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹) *ᵥ (X *ᵥ θ)) -
        (1 - gramProjector Xᵀ) *ᵥ θ := by
  set P : Matrix n₀ n₀ ℝ := gramProjector Xᵀ with hP
  set Zd : Matrix n m ℝ := (X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹ with hZd
  have hPM : P * (S * Zd) = Xᵀ * (X * Xᵀ)⁻¹ := gramProjector_transpose_mul_operator X S hZ
  have hPe : P = Xᵀ * (X * Xᵀ)⁻¹ * X := gramProjector_transpose_eq X
  have hPSX : P * (S * Zd * X) = P := by
    rw [← Matrix.mul_assoc, hPM, ← hPe]
  have key : (S * Zd) * X - 1 = (1 - P) * ((S * Zd) * X - 1) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, hPSX, Matrix.mul_one]
    abel
  rw [key]
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec]

end LinearRegression.DoubleDescent

end
