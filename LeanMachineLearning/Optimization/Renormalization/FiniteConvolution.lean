/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Convolution
public import Mathlib.Data.ZMod.Basic

/-!
# A finite convolution as one sparse, weight-tied dense layer

The local-patch theorem in `Convolution` does not by itself construct the single global matrix often
used to describe convolution.  Here a `FiniteBoundary` fixes the finite spatial domain and boundary
convention, after which `toGlobalDenseLayer` constructs that matrix.  Several window offsets may
hit the same input position (for example on a very small periodic grid), so the corresponding
kernel coefficients are summed rather than silently overwritten.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace NeuralNetwork

universe uP uι uκ

/-- Boundary convention on a finite spatial domain.  `shift p dc dd` is the input position sampled
at offset `(dc, dd)` from output position `p`. -/
structure FiniteBoundary (P : Type uP) where
  /-- Resolve an integer spatial offset inside the finite domain. -/
  shift : P → ℤ → ℤ → P

namespace FiniteBoundary

/-- Periodic boundary conditions on a finite two-dimensional torus. -/
def periodic (rows cols : ℕ) :
    FiniteBoundary (ZMod rows × ZMod cols) where
  shift p dc dd := (p.1 + dc, p.2 + dd)

end FiniteBoundary

namespace Conv2DLayer

variable {P : Type uP} {ι : Type uι} {κ : Type uκ}

/-- Convolutional preactivation on a finite spatial domain with an explicit boundary convention. -/
def finitePreactivation [Fintype ι] (L : Conv2DLayer ι κ) (B : FiniteBoundary P)
    (k : ℕ) (x : ι × P → ℝ) : κ × P → ℝ :=
  fun op => L.bias op.1 +
    ∑ i, ∑ dc : WindowIndex k, ∑ dd : WindowIndex k,
      L.weight op.1 i dc dd * x (i, B.shift op.2 dc dd)

@[simp] theorem finitePreactivation_apply [Fintype ι] (L : Conv2DLayer ι κ)
    (B : FiniteBoundary P) (k : ℕ) (x : ι × P → ℝ) (o : κ) (p : P) :
    L.finitePreactivation B k x (o, p) = L.bias o +
      ∑ i, ∑ dc : WindowIndex k, ∑ dd : WindowIndex k,
        L.weight o i dc dd * x (i, B.shift p dc dd) := rfl

/-- The global sparse dense layer implementing a finite convolution.  Its output coordinates are
channel-position pairs, as are its input coordinates.  The matrix coefficient is zero when no
window offset connects the two positions, and it sums coefficients if the boundary convention
identifies several offsets. -/
def toGlobalDenseLayer [DecidableEq P] (L : Conv2DLayer ι κ)
    (B : FiniteBoundary P) (k : ℕ) : DenseLayer (ι × P) (κ × P) where
  weight op iq :=
    ∑ r : WindowIndex k × WindowIndex k,
      if B.shift op.2 r.1 r.2 = iq.2 then L.weight op.1 iq.1 r.1 r.2 else 0
  bias op := L.bias op.1

@[simp] theorem toGlobalDenseLayer_bias [DecidableEq P]
    (L : Conv2DLayer ι κ) (B : FiniteBoundary P) (k : ℕ) (o : κ) (p : P) :
    (L.toGlobalDenseLayer B k).bias (o, p) = L.bias o := rfl

@[simp] theorem toGlobalDenseLayer_weight [DecidableEq P]
    (L : Conv2DLayer ι κ) (B : FiniteBoundary P) (k : ℕ)
    (o : κ) (p : P) (i : ι) (q : P) :
    (L.toGlobalDenseLayer B k).weight (o, p) (i, q) =
      ∑ r : WindowIndex k × WindowIndex k,
        if B.shift p r.1 r.2 = q then L.weight o i r.1 r.2 else 0 := rfl

/-- Entries outside the receptive field are structurally zero. -/
theorem toGlobalDenseLayer_weight_eq_zero_of_not_reachable
    [DecidableEq P]
    (L : Conv2DLayer ι κ) (B : FiniteBoundary P) (k : ℕ)
    (o : κ) (p : P) (i : ι) (q : P)
    (h : ∀ dc : WindowIndex k, ∀ dd : WindowIndex k, B.shift p dc dd ≠ q) :
    (L.toGlobalDenseLayer B k).weight (o, p) (i, q) = 0 := by
  simp [toGlobalDenseLayer, h]

/-- The constructed global dense matrix agrees with convolution at every output position.

Informal proof: expand the dense matrix-vector product, split the sum over input channel-position
pairs, and interchange it with the finite sum over window offsets.  For a fixed offset, exactly the
term `q = B.shift p dc dd` survives the indicator sum over positions.  This remains valid when
different offsets collide because the construction sums their coefficients.  This is the standard
sparse doubly-block Toeplitz representation of discrete convolution; see
<https://en.wikipedia.org/wiki/Toeplitz_matrix#Discrete_convolution>.
-/
theorem preactivation_toGlobalDenseLayer [Fintype ι] [Fintype P] [DecidableEq P]
    (L : Conv2DLayer ι κ) (B : FiniteBoundary P) (k : ℕ) (x : ι × P → ℝ) :
    (L.toGlobalDenseLayer B k).preactivation x = L.finitePreactivation B k x := by
  funext op
  rcases op with ⟨o, p⟩
  simp only [DenseLayer.preactivation_apply, finitePreactivation_apply,
    toGlobalDenseLayer_bias]
  congr 1
  rw [Conv2DLayer.sum_over_prod]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [toGlobalDenseLayer_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Conv2DLayer.sum_over_prod
    (fun r : WindowIndex k × WindowIndex k =>
      L.weight o i r.1 r.2 * x (i, B.shift p r.1 r.2))]
  apply Finset.sum_congr rfl
  intro r _
  rcases r with ⟨dc, dd⟩
  simp

/-- Number of scalar parameters in an unrestricted global dense layer with the same input and
output coordinates as the finite convolution. -/
def unrestrictedGlobalDenseParamCount [Fintype ι] [Fintype κ] [Fintype P] : ℕ :=
  Fintype.card (κ × P) * Fintype.card (ι × P) + Fintype.card (κ × P)

theorem toGlobalDenseLayer_paramCount [Fintype ι] [Fintype κ] [Fintype P] [DecidableEq P]
    (L : Conv2DLayer ι κ) (B : FiniteBoundary P) (k : ℕ) :
    (L.toGlobalDenseLayer B k).paramCount =
      unrestrictedGlobalDenseParamCount (ι := ι) (κ := κ) (P := P) := rfl

/-- A convolution uses no more free parameters than the corresponding unrestricted global dense
layer when its window contains no more positions than the spatial domain.

Informal proof: write `I`, `O`, `S`, and `W` for the input-channel, output-channel, spatial, and
window cardinalities.  The counts are `O + O*I*W` and `O*S + O*S*I*S`.  From `1 ≤ S` and `W ≤ S`,
monotonicity of multiplication bounds the bias and weight terms separately.  See the elementary
ordered-semiring lemmas documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Ring/Nat.html>.
-/
theorem paramCount_le_unrestrictedGlobalDense [Fintype ι] [Fintype κ] [Fintype P]
    (L : Conv2DLayer ι κ) (k : ℕ) (hP : 0 < Fintype.card P)
    (hwindow : (2 * k + 1) ^ 2 ≤ Fintype.card P) :
    L.paramCount k ≤ unrestrictedGlobalDenseParamCount (ι := ι) (κ := κ) (P := P) := by
  let O := Fintype.card κ
  let I := Fintype.card ι
  let S := Fintype.card P
  let W := (2 * k + 1) ^ 2
  have hS : 1 ≤ S := hP
  have hbias : O ≤ O * S := by
    simpa using Nat.mul_le_mul_left O hS
  have hweight₁ : O * I * W ≤ O * I * S := by
    exact Nat.mul_le_mul_left (O * I) hwindow
  have hweight₂ : O * I * S ≤ O * I * S * S := by
    simpa using Nat.mul_le_mul_left (O * I * S) hS
  have hweight : O * I * W ≤ O * S * (I * S) := by
    calc
      O * I * W ≤ O * I * S := hweight₁
      _ ≤ O * I * S * S := hweight₂
      _ = O * S * (I * S) := by ac_rfl
  unfold Conv2DLayer.paramCount unrestrictedGlobalDenseParamCount
  simp only [Fintype.card_prod]
  change O + O * I * W ≤ O * S * (I * S) + O * S
  omega

end Conv2DLayer

end NeuralNetwork

end

end
