/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Depth.SquareApprox

/-!
# Approximate multiplication via squaring (Section 5.3, Lemma 5.3)

This file formalizes Lemma 5.3, which constructs a ReLU network that approximates
the product of l numbers via repeated application of the approximate squaring network hₖ.

## Construction

**Pairwise multiplication (l = 2):**
Using the polarization identity xy = ½((x+y)² − x² − y²), define:
```
prod_{k,2}(a, b) := ½(4·hₖ((a+b)/2) − hₖ(a) − hₖ(b))
```
This approximates ab with error ≤ 4^{−k}.

**General multiplication (l > 2):**
Use l−1 copies of prod_{k,2} in a binary tree structure:
```
prod_{k,l}(x₁,…,xₗ) := prod_{k,2}(prod_{k,l-1}(x₁,…,xₗ₋₁), xₗ)
```

## Main results

* `approxProd2` : the network implementing prod_{k,2}
* `approxProd2_eval` : |prod_{k,2}(a, b) − a · b| ≤ 4^{−k} for (a,b) ∈ [0,1]²
* `approxProd2_range` : prod_{k,2}(a, b) ∈ [0, 1] for (a, b) ∈ [0, 1]²
* `approxProdL` : the network implementing prod_{k,l}
* `approxProdL_eval` : |prod_{k,l}(x) − ∏ xⱼ| ≤ l · 4^{−k} for x ∈ [0,1]ˡ
* `approxProdL_zero_of_zero` : prod_{k,l}(x) = 0 if any xⱼ = 0
* `approxProdL_network_size` : prod_{k,l} has O(kl) layers and O(kl + l²) nodes

-/

@[expose] public section

open Real Finset

namespace Depth

/-! ### Pairwise approximate multiplication -/

/-- The approximate pairwise product network:
  prod_{k,2}(a, b) = ½(4·hₖ((a+b)/2) − hₖ(a) − hₖ(b)).
  This uses three copies of the squaring approximation hₖ. -/
noncomputable def approxProd2 (k : ℕ) (a b : ℝ) : ℝ :=
  (1/2) * (4 * squareInterp k ((a + b) / 2) - squareInterp k a - squareInterp k b)

/-- prod_{k,2}(a, b) approximates a · b with error ≤ 4^{−k}. -/
theorem approxProd2_eval (k : ℕ) (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |approxProd2 k a b - a * b| ≤ 4^(-(k : ℤ)) := by
  sorry

/-- prod_{k,2}(a, b) ∈ [0, 1] when a, b ∈ [0, 1]. -/
theorem approxProd2_range (k : ℕ) (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    approxProd2 k a b ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- prod_{k,2}(a, 0) = 0 and prod_{k,2}(0, b) = 0. -/
theorem approxProd2_zero_right (k : ℕ) (a : ℝ) : approxProd2 k a 0 = 0 := by
  simp [approxProd2, squareInterp_zero]
  ring

theorem approxProd2_zero_left (k : ℕ) (b : ℝ) : approxProd2 k 0 b = 0 := by
  simp [approxProd2, squareInterp_zero]
  ring

/-! ### Multi-argument approximate multiplication -/

/-- The approximate l-way product, defined by induction on l via prod_{k,2}.
  prod_{k,1}(x₁) = x₁
  prod_{k,l}(x₁,…,xₗ) = prod_{k,2}(prod_{k,l-1}(x₁,…,xₗ₋₁), xₗ) -/
noncomputable def approxProdL (k : ℕ) : ∀ (l : ℕ), (Fin l → ℝ) → ℝ
  | 0     => fun _ => 1
  | 1     => fun x => x 0
  | (l+2) => fun x =>
      approxProd2 k (approxProdL k (l+1) (fun i => x (Fin.castSucc i))) (x (Fin.last (l+1)))

/-- Lemma 5.3: |prod_{k,l}(x) − ∏ⱼ xⱼ| ≤ l · 4^{−k} for x ∈ [0,1]ˡ. -/
theorem approxProdL_eval (k l : ℕ) (x : Fin l → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) :
    |approxProdL k l x - ∏ j, x j| ≤ l * 4^(-(k : ℤ)) := by
  induction l with
  | zero =>
    simp [approxProdL]
  | succ n ih =>
    cases n with
    | zero => simp [approxProdL]
    | succ m =>
      simp only [approxProdL]
      have ih' := ih (fun i => x (Fin.castSucc i)) (fun j => hx (Fin.castSucc j))
      sorry

/-- prod_{k,l}(x) = 0 if any component xⱼ = 0. -/
theorem approxProdL_zero_of_zero (k l : ℕ) (x : Fin l → ℝ) (j₀ : Fin l) (hj : x j₀ = 0) :
    approxProdL k l x = 0 := by
  sorry

/-- prod_{k,l}(x) ∈ [0, 1] for x ∈ [0, 1]ˡ. -/
theorem approxProdL_range (k l : ℕ) (x : Fin l → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) :
    approxProdL k l x ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- Network size for approxProdL: O(kl) layers, O(kl + l²) nodes. -/
theorem approxProdL_network_size (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ∃ net : ReLUNetwork (3 * k * l),
      net.totalNodes ≤ 2 * (k * l + l^2) ∧
      ∀ x : Fin l → ℝ, (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) →
        ∑ j, net.outWeights j * reluActivation 0 = approxProdL k l x := by
  sorry

end Depth

end
