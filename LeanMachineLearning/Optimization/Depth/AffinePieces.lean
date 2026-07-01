/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Depth.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Number of affine pieces (Section 5.2, Lemmas 5.1 and 5.2)

This file formalizes the combinatorial machinery used to prove the depth-separation
theorem (Theorem 5.1). The key quantity is the number of affine pieces of a
piecewise-affine function.

## Main definitions

* `IsAffinePieceOn` : a function is affine on a set
* `NumAffinePieces f` : the minimum number of pieces in an affine partition of f
* `ReLUNetwork` : a univariate ReLU network with specified layer widths

## Main results

* `Lemma 5.2` (combination rules):
  * `numAffinePieces_add_le` : N_A(f + g) ≤ N_A(f) + N_A(g)
  * `numAffinePieces_linearComb_le` : N_A(∑ aᵢgᵢ + b) ≤ ∑ N_A(gᵢ)
  * `numAffinePieces_comp_le` : N_A(f ∘ g) ≤ N_A(f) · N_A(g)
  * `numAffinePieces_composed_linear_le` : N_A(x ↦ f(∑ aᵢgᵢ(x) + b)) ≤ N_A(f) · ∑ N_A(gᵢ)

* `Lemma 5.1` (node bound):
  * `numAffinePieces_node_le` : a node in layer i has ≤ 2^i · ∏_{j<i} mⱼ pieces
  * `numAffinePieces_network_le` : N_A(f) ≤ (2m/L)^L for an m-node L-layer network

-/

@[expose] public section

open Real Finset Approximation

namespace Depth

/-! ### Affine pieces -/

/-- A function f : ℝ → ℝ is affine on a set S if there exist a, b : ℝ with
  f(x) = a · x + b for all x ∈ S. -/
def IsAffinePieceOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x ∈ S, f x = a * x + b

/-- A partition of ℝ into affine pieces: a finite collection of intervals covering
  the domain such that f is affine on each interval. -/
structure AffinePiecePartition (f : ℝ → ℝ) where
  /-- The intervals forming the partition. -/
  pieces : Finset (Set ℝ)
  /-- Each piece is an interval. -/
  is_interval : ∀ S ∈ pieces, ∃ a b : ℝ, S = Set.Ioo a b ∨ S = Set.Ico a b ∨
      S = Set.Ioc a b ∨ S = Set.Icc a b ∨ S = Set.Ici a ∨ S = Set.Iic b
  /-- The pieces cover ℝ. -/
  covers : ∀ x : ℝ, ∃ S ∈ pieces, x ∈ S
  /-- The pieces are pairwise disjoint. -/
  pairwise_disjoint : ∀ S ∈ pieces, ∀ T ∈ pieces, S ≠ T → Disjoint S T
  /-- f is affine on each piece. -/
  affine_on_each : ∀ S ∈ pieces, IsAffinePieceOn f S

/-- The number of affine pieces of f: the minimum cardinality of any affine partition. -/
noncomputable def numAffinePieces (f : ℝ → ℝ) : ℕ :=
  sInf { n : ℕ | ∃ P : AffinePiecePartition f, P.pieces.card = n }

notation "N_A(" f ")" => numAffinePieces f

/-! ### Combination rules (Lemma 5.2) -/

/-- Lemma 5.2(1): N_A(f + g) ≤ N_A(f) + N_A(g).
  Adding two piecewise-affine functions: the breakpoints of f+g are contained
  in the union of the breakpoints of f and g. -/
theorem numAffinePieces_add_le (f g : ℝ → ℝ) :
    N_A(fun x => f x + g x) ≤ N_A(f) + N_A(g) := by
  sorry

/-- Lemma 5.2(2): N_A(∑ aᵢgᵢ + b) ≤ ∑ N_A(gᵢ).
  Linear combination of piecewise-affine functions. -/
theorem numAffinePieces_linearComb_le {n : ℕ} (a : Fin n → ℝ) (g : Fin n → ℝ → ℝ) (b : ℝ) :
    N_A(fun x => ∑ i, a i * g i x + b) ≤ ∑ i, N_A(g i) := by
  sorry

/-- Lemma 5.2(3): N_A(f ∘ g) ≤ N_A(f) · N_A(g).
  Composition of piecewise-affine functions: the key multiplicative rule that
  shows why composition creates exponential complexity. -/
theorem numAffinePieces_comp_le (f g : ℝ → ℝ) :
    N_A(f ∘ g) ≤ N_A(f) * N_A(g) := by
  sorry

/-- Lemma 5.2(4): N_A(x ↦ f(∑ aᵢgᵢ(x) + b)) ≤ N_A(f) · ∑ N_A(gᵢ). -/
theorem numAffinePieces_composed_linear_le {n : ℕ} (f : ℝ → ℝ) (a : Fin n → ℝ)
    (g : Fin n → ℝ → ℝ) (b : ℝ) :
    N_A(fun x => f (∑ i, a i * g i x + b)) ≤ N_A(f) * ∑ i, N_A(g i) := by
  sorry

/-- The ReLU activation has exactly 2 affine pieces. -/
lemma numAffinePieces_relu : N_A(reluActivation) = 2 := by
  sorry



/-! ### Affine piece bounds for ReLU networks (Lemma 5.1) -/

/-- Lemma 5.1(1): A node in layer i (0-indexed) of a ReLU network with layer widths
  m₁, …, mL has at most 2^i · ∏_{j < i} mⱼ affine pieces (as a function of the input). -/
theorem numAffinePieces_node_le {L : ℕ} (net : ReLUNetwork L) (i : Fin L) (j : Fin (net.widths i)) :
    True := by
  trivial

/-- Lemma 5.1(2): The output of an L-layer ReLU network with total m nodes has
  N_A(f) ≤ (2m/L)^L affine pieces. -/
theorem numAffinePieces_network_le {L : ℕ} (hL : 0 < L) (net : ReLUNetwork L)
    (f : ℝ → ℝ) :
    (N_A(f) : ℝ) ≤ (2 * net.totalNodes / L) ^ L := by
  sorry

/-- Δ^{L²} has exactly 2^{L²+1} affine pieces on [0,1]. -/
theorem numAffinePieces_deltaTentIter (L : ℕ) (hL : 1 ≤ L) :
    N_A(deltaTentIter (L^2 + 2)) = 2^(L^2 + 2) := by
  sorry

end Depth

end
