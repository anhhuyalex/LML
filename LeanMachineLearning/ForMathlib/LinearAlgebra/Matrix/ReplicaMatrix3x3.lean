/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# The `3 × 3` replica matrix and its universal left eigenvectors

For coefficients `b2 b1 b0` in a commutative ring, the matrix
```
[b2,  -4 b1,             3 b0            ]
[b1,  b2 - 2 b1 - 3 b0,  6 b0 - 3 b1     ]
[b0,  4 b1 - 8 b0,       b2 - 8 b1 + 10 b0]
```
has the left eigenvectors `(1, -2, 1)` and `(1, -4, 3)` with eigenvalues `b2 - 2 b1 + b0` and
`b2 - 4 b1 + 3 b0`, whatever the coefficients are.  This is the algebra behind the replica
covariance system of Talagrand's Section 1.8 (Eqs. 1.234–1.236); nothing here depends on the
probabilistic setting.

## Main declarations

* `Matrix.atMatrix`, `Matrix.atEigenvectorOne`, `Matrix.atEigenvectorTwo`
* `Matrix.atMatrix_transpose_mulVec_one`, `Matrix.atMatrix_transpose_mulVec_two`
* `Matrix.atRowZero`, `Matrix.atRowOne`, `Matrix.atRowTwo`, `Matrix.atMatrix_mulVec_eq`
* `Matrix.abs_atEigenvectorOne_dot_le`, `Matrix.abs_atEigenvectorTwo_dot_le`: the `ℓ¹` norms
  `4`, `8` of the eigenvectors bound the projections of a remainder vector
-/

@[expose] public section

open Matrix

namespace Matrix

variable {K : Type*} [CommRing K]

/-- The `3 × 3` matrix of the cavity covariance system (Talagrand Eq. 1.234):
`[b(2),              -4 b(1),              3 b(0)             ]`
`[b(1),  b(2) - 2 b(1) - 3 b(0),        6 b(0) - 3 b(1)       ]`
`[b(0),        4 b(1) - 8 b(0),   b(2) - 8 b(1) + 10 b(0)     ]` -/
def atMatrix (b2 b1 b0 : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![b2, -4 * b1, 3 * b0],
    ![b1, b2 - 2 * b1 - 3 * b0, 6 * b0 - 3 * b1],
    ![b0, 4 * b1 - 8 * b0, b2 - 8 * b1 + 10 * b0]]

variable (K) in
/-- The first eigenvector of the transposed matrix `atMatrix`: `(1, -2, 1)`. -/
def atEigenvectorOne : Fin 3 → K :=
  ![1, -2, 1]

variable (K) in
/-- The second eigenvector of the transposed matrix `atMatrix`: `(1, -4, 3)`. -/
def atEigenvectorTwo : Fin 3 → K :=
  ![1, -4, 3]

/-- **Talagrand, Eq. (1.235): universal eigenvector `(1, -2, 1)` of the transposed matrix.**
For any coefficients `b(2), b(1), b(0)`, `(1, -2, 1)` is an eigenvector of `(atMatrix b2 b1 b0)ᵀ`
with eigenvalue `b(2) - 2 b(1) + b(0)`. -/
theorem atMatrix_transpose_mulVec_one (b2 b1 b0 : K) :
    (atMatrix b2 b1 b0)ᵀ *ᵥ atEigenvectorOne K = (b2 - 2 * b1 + b0) • atEigenvectorOne K := by
  ext i
  fin_cases i
  · change (∑ j : Fin 3, (atMatrix b2 b1 b0)ᵀ 0 j * atEigenvectorOne K j) = _
    rw [Fin.sum_univ_three]
    change b2 * 1 + b1 * (-2) + b0 * 1 = (b2 - 2 * b1 + b0) * 1
    ring
  · change (∑ j : Fin 3, (atMatrix b2 b1 b0)ᵀ 1 j * atEigenvectorOne K j) = _
    rw [Fin.sum_univ_three]
    change (-4 * b1) * 1 + (b2 - 2 * b1 - 3 * b0) * (-2) + (4 * b1 - 8 * b0) * 1 =
        (b2 - 2 * b1 + b0) * (-2)
    ring
  · change (∑ j : Fin 3, (atMatrix b2 b1 b0)ᵀ 2 j * atEigenvectorOne K j) = _
    rw [Fin.sum_univ_three]
    change (3 * b0) * 1 + (6 * b0 - 3 * b1) * (-2) + (b2 - 8 * b1 + 10 * b0) * 1 =
        (b2 - 2 * b1 + b0) * 1
    ring

/-- **Talagrand, Eq. (1.236): universal eigenvector `(1, -4, 3)` of the transposed matrix.**
For any coefficients `b(2), b(1), b(0)`, `(1, -4, 3)` is an eigenvector of `(atMatrix b2 b1 b0)ᵀ`
with eigenvalue `b(2) - 4 b(1) + 3 b(0)`. -/
theorem atMatrix_transpose_mulVec_two (b2 b1 b0 : K) :
    (atMatrix b2 b1 b0)ᵀ *ᵥ atEigenvectorTwo K = (b2 - 4 * b1 + 3 * b0) • atEigenvectorTwo K := by
  ext i
  fin_cases i
  · change (∑ j : Fin 3, (atMatrix b2 b1 b0)ᵀ 0 j * atEigenvectorTwo K j) = _
    rw [Fin.sum_univ_three]
    change b2 * 1 + b1 * (-4) + b0 * 3 = (b2 - 4 * b1 + 3 * b0) * 1
    ring
  · change (∑ j : Fin 3, (atMatrix b2 b1 b0)ᵀ 1 j * atEigenvectorTwo K j) = _
    rw [Fin.sum_univ_three]
    change (-4 * b1) * 1 + (b2 - 2 * b1 - 3 * b0) * (-4) + (4 * b1 - 8 * b0) * 3 =
        (b2 - 4 * b1 + 3 * b0) * (-4)
    ring
  · change (∑ j : Fin 3, (atMatrix b2 b1 b0)ᵀ 2 j * atEigenvectorTwo K j) = _
    rw [Fin.sum_univ_three]
    change (3 * b0) * 1 + (6 * b0 - 3 * b1) * (-4) + (b2 - 8 * b1 + 10 * b0) * 3 =
        (b2 - 4 * b1 + 3 * b0) * 3
    ring

/-- The first row linear form of the matrix system (Eq. 1.231):
`b(2) U - 4 b(1) V + 3 b(0) W`. -/
def atRowZero (b2 b1 b0 U V W : K) : K :=
  b2 * U - 4 * b1 * V + 3 * b0 * W

/-- The second row linear form of the matrix system (Eq. 1.232):
`b(1) U + (b(2) - 2 b(1) - 3 b(0)) V + (6 b(0) - 3 b(1)) W`. -/
def atRowOne (b2 b1 b0 U V W : K) : K :=
  b1 * U + (b2 - 2 * b1 - 3 * b0) * V + (6 * b0 - 3 * b1) * W

/-- The third row linear form of the matrix system (Eq. 1.233):
`b(0) U + (4 b(1) - 8 b(0)) V + (b(2) - 8 b(1) + 10 b(0)) W`. -/
def atRowTwo (b2 b1 b0 U V W : K) : K :=
  b0 * U + (4 * b1 - 8 * b0) * V + (b2 - 8 * b1 + 10 * b0) * W

theorem atMatrix_mulVec_zero (b2 b1 b0 : K) (v : Fin 3 → K) :
    (atMatrix b2 b1 b0 *ᵥ v) 0 = atRowZero b2 b1 b0 (v 0) (v 1) (v 2) := by
  change (∑ j : Fin 3, atMatrix b2 b1 b0 0 j * v j) = _
  rw [Fin.sum_univ_three]
  change b2 * v 0 + (-4 * b1) * v 1 + (3 * b0) * v 2 = _
  dsimp [atRowZero]
  ring

theorem atMatrix_mulVec_one (b2 b1 b0 : K) (v : Fin 3 → K) :
    (atMatrix b2 b1 b0 *ᵥ v) 1 = atRowOne b2 b1 b0 (v 0) (v 1) (v 2) := by
  change (∑ j : Fin 3, atMatrix b2 b1 b0 1 j * v j) = _
  rw [Fin.sum_univ_three]
  rfl

theorem atMatrix_mulVec_two (b2 b1 b0 : K) (v : Fin 3 → K) :
    (atMatrix b2 b1 b0 *ᵥ v) 2 = atRowTwo b2 b1 b0 (v 0) (v 1) (v 2) := by
  change (∑ j : Fin 3, atMatrix b2 b1 b0 2 j * v j) = _
  rw [Fin.sum_univ_three]
  rfl

/-- The rows of `atMatrix` applied to `v = ![U, V, W]` match the three linear forms. -/
theorem atMatrix_mulVec_eq (b2 b1 b0 U V W : K) :
    atMatrix b2 b1 b0 *ᵥ ![U, V, W] =
      ![atRowZero b2 b1 b0 U V W, atRowOne b2 b1 b0 U V W, atRowTwo b2 b1 b0 U V W] := by
  ext i
  fin_cases i
  · exact atMatrix_mulVec_zero b2 b1 b0 ![U, V, W]
  · exact atMatrix_mulVec_one b2 b1 b0 ![U, V, W]
  · exact atMatrix_mulVec_two b2 b1 b0 ![U, V, W]

/-- A remainder `(R₀, R₁, R₂)` with entries at most `E` has projection on the eigenvector
`(1, -2, 1)` at most `4 E` (its `ℓ¹` norm times `E`). -/
theorem abs_atEigenvectorOne_dot_le {L : Type*} [CommRing L] [LinearOrder L] [IsStrictOrderedRing L]
    {R₀ R₁ R₂ E : L} (h₀ : |R₀| ≤ E) (h₁ : |R₁| ≤ E)
    (h₂ : |R₂| ≤ E) : |R₀ - 2 * R₁ + R₂| ≤ 4 * E := by
  rw [abs_le] at *
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

/-- The same for the eigenvector `(1, -4, 3)`, with `ℓ¹` norm `8`. -/
theorem abs_atEigenvectorTwo_dot_le {L : Type*} [CommRing L] [LinearOrder L] [IsStrictOrderedRing L]
    {R₀ R₁ R₂ E : L} (h₀ : |R₀| ≤ E) (h₁ : |R₁| ≤ E)
    (h₂ : |R₂| ≤ E) : |R₀ - 4 * R₁ + 3 * R₂| ≤ 8 * E := by
  rw [abs_le] at *
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

end Matrix
