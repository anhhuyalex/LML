/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Network
public import Mathlib.Data.Int.Interval

/-!
# The convolutional-layer equation from Chapter 2

The source presents convolution only as an architectural comparison with an MLP.  This file
formalizes that displayed equation and makes its weight-sharing claim precise.  A convolution is
translation *equivariant*; invariance arises only after an invariant readout such as pooling.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace NeuralNetwork

universe u v

/-- A two-dimensional convolutional affine layer.  Kernel weights depend on output channel, input
channel, and relative spatial offset, but not on absolute spatial position. -/
structure Conv2DLayer (ι : Type u) (κ : Type v) where
  /-- The convolution kernel, indexed by output channel, input channel, and two offsets. -/
  weight : κ → ι → ℤ → ℤ → ℝ
  /-- One bias per output channel, shared across spatial positions. -/
  bias : κ → ℝ

namespace Conv2DLayer

variable {ι : Type u} {κ : Type v}

/-- Integer offsets in a radius-`k` convolution window. -/
def window (k : ℕ) : Finset ℤ := Finset.Icc (-(k : ℤ)) (k : ℤ)

/-- An offset occurring in a radius-`k` convolutional window. -/
abbrev WindowIndex (k : ℕ) := {d : ℤ // d ∈ window k}

/-- The finite input-coordinate type seen by one convolutional output location. -/
abbrev PatchIndex (ι : Type u) (k : ℕ) := ι × (WindowIndex k × WindowIndex k)

/-- The two-dimensional convolutional preactivation from the source, in the usual generality where
the kernel may depend on the relative offset. -/
def preactivation [Fintype ι] (L : Conv2DLayer ι κ) (k : ℕ)
    (x : ι → ℤ → ℤ → ℝ) : κ → ℤ → ℤ → ℝ :=
  fun o c d => L.bias o +
    ∑ i, ∑ dc ∈ window k, ∑ dd ∈ window k,
      L.weight o i dc dd * x i (c + dc) (d + dd)

@[simp] theorem preactivation_apply [Fintype ι] (L : Conv2DLayer ι κ) (k : ℕ)
    (x : ι → ℤ → ℤ → ℝ) (o : κ) (c d : ℤ) :
    L.preactivation k x o c d = L.bias o +
      ∑ i, ∑ dc ∈ window k, ∑ dd ∈ window k,
        L.weight o i dc dd * x i (c + dc) (d + dd) := rfl

/-- Spatial translation of a channel-indexed signal. -/
def shift (a b : ℤ) (x : ι → ℤ → ℤ → ℝ) : ι → ℤ → ℤ → ℝ :=
  fun i c d => x i (c + a) (d + b)

/-- Convolution commutes with spatial translations.  This is translation equivariance, the precise
mathematical content behind the source's informal phrase "translational invariance". -/
theorem preactivation_shift [Fintype ι] (L : Conv2DLayer ι κ) (k : ℕ)
    (x : ι → ℤ → ℤ → ℝ) (a b : ℤ) :
    L.preactivation k (shift a b x) = shift a b (L.preactivation k x) := by
  funext o c d
  simp only [preactivation_apply, shift]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro dc _
  apply Finset.sum_congr rfl
  intro dd _
  congr 2 <;> omega

/-- Extract the finite local patch centered at spatial coordinate `(c,d)`. -/
def extractPatch (k : ℕ) (x : ι → ℤ → ℤ → ℝ) (c d : ℤ) : PatchIndex ι k → ℝ :=
  fun p => x p.1 (c + p.2.1) (d + p.2.2)

/-- The dense affine layer applied at every spatial location of a convolution. -/
def toLocalDenseLayer (L : Conv2DLayer ι κ) (k : ℕ) : DenseLayer (PatchIndex ι k) κ where
  weight o p := L.weight o p.1 p.2.1 p.2.2
  bias := L.bias

/-- Summing over integer offsets in the window is the same as summing over the corresponding
subtype of admissible offsets. -/
private theorem sum_window_eq_sum_windowIndex (k : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ window k, f z) = ∑ z : WindowIndex k, f z := by
  exact Finset.sum_subtype (window k) (fun z => Iff.rfl) f

/-- A sum over a local patch decomposes as nested sums over the channel and the two window
offsets. -/
private theorem sum_patchIndex [Fintype ι] (k : ℕ)
    (f : ι → WindowIndex k → WindowIndex k → ℝ) :
    (∑ p : PatchIndex ι k, f p.1 p.2.1 p.2.2) =
      ∑ i, ∑ dc : WindowIndex k, ∑ dd : WindowIndex k, f i dc dd := by
  calc
    (∑ p : PatchIndex ι k, f p.1 p.2.1 p.2.2)
        = ∑ i : ι, ∑ q : WindowIndex k × WindowIndex k, f i q.1 q.2 := by
          simpa [PatchIndex] using
            (Fintype.sum_prod_type' (fun (i : ι) (q : WindowIndex k × WindowIndex k) =>
              f i q.1 q.2))
    _ = ∑ i, ∑ dc : WindowIndex k, ∑ dd : WindowIndex k, f i dc dd := by
      congr with i
      exact Fintype.sum_prod_type' (fun (dc : WindowIndex k) (dd : WindowIndex k) =>
        f i dc dd)

/-- A convolutional preactivation is one fixed dense affine map applied to every extracted local
patch. This is the precise weight-tying statement from Chapter 2.

Informal proof: expand both preactivations. A sum over the subtype `WindowIndex k` is the same as a
sum over integers restricted to `window k`; after this finite-sum reindexing, corresponding
summands are definitionally equal. See the standard sparse-matrix description of convolution:
<https://en.wikipedia.org/wiki/Toeplitz_matrix#Discrete_convolution>. -/
theorem preactivation_eq_toLocalDenseLayer [Fintype ι] (L : Conv2DLayer ι κ) (k : ℕ)
    (x : ι → ℤ → ℤ → ℝ) (o : κ) (c d : ℤ) :
    L.preactivation k x o c d =
      (L.toLocalDenseLayer k).preactivation (extractPatch k x c d) o := by
  simp only [preactivation_apply, PatchIndex, WindowIndex, toLocalDenseLayer,
    DenseLayer.preactivation_apply, extractPatch, add_right_inj]
  simp_rw [sum_window_eq_sum_windowIndex]
  symm
  exact sum_patchIndex k (fun i dc dd =>
    L.weight o i dc dd * x i (c + dc) (d + dd))

/-- Embed the literal source formula, whose displayed weights do not carry offset indices, into the
more general convolutional representation. -/
def ofOffsetTiedDense (L : DenseLayer ι κ) : Conv2DLayer ι κ where
  weight o i _ _ := L.weight o i
  bias := L.bias

theorem preactivation_ofOffsetTiedDense [Fintype ι] (L : DenseLayer ι κ) (k : ℕ)
    (x : ι → ℤ → ℤ → ℝ) (o : κ) (c d : ℤ) :
    (ofOffsetTiedDense L).preactivation k x o c d = L.bias o +
      ∑ i, ∑ dc ∈ window k, ∑ dd ∈ window k,
        L.weight o i * x i (c + dc) (d + dd) := rfl

/-- Number of independent scalar parameters in a radius-`k` convolutional layer. -/
def paramCount [Fintype ι] [Fintype κ] (_L : Conv2DLayer ι κ) (k : ℕ) : ℕ :=
  Fintype.card κ + Fintype.card κ * Fintype.card ι * (2 * k + 1) ^ 2

end Conv2DLayer

end NeuralNetwork

end

end
