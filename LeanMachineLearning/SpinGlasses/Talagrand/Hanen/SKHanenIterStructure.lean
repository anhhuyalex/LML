/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIterChoices

/-!
# Pointwise structure of the iterated cavity kernel (Talagrand, Lemma 1.11.3, Eq. (1.334))

Each cavity derivative brings out one factor `β² ε_a ε_b (R⁻_{ab} - q)` on a pair of distinct
replicas (Eq. (1.151)). Iterating `m` times, the observable `skCavityIterKernel N β q m n f` is
`f` evaluated on the original `n` replicas, times a signed finite sum, over a finite index type
`T` of `m`-tuples of replica pairs, of products of `m` such factors.  The index structure
(`T`, the weights, the replica positions) does not depend on `N`, `β`, `q` or `f`; the total
absolute weight is the explicit number `skCavityIterWeightBound m n = ∏_{r < m} 2 (n + 2r)²`.

## Main declarations

* `SpinGlasses.skCavityIterWeightBound`: the total absolute weight `∏_{r<m} 2 (n+2r)²`.
* `SpinGlasses.skCavityIterKernel_structure`: the exact formula.
* `SpinGlasses.abs_skCavityIterKernel_le`: the resulting pointwise bound by
  `β^{2m} |f| ∑ |w| ∏ |R⁻ - q|`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.11.3.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace SpinGlasses

/-- The total absolute weight of the `m`-fold iterated cavity derivative on `n` replicas:
`∏_{r < m} 2 (n + 2r)²` (each derivative on `k` replicas has total weight `2 k²`). -/
def skCavityIterWeightBound : ℕ → ℕ → ℝ
  | 0, _ => 1
  | m + 1, n => 2 * (n : ℝ) ^ 2 * skCavityIterWeightBound m (n + 2)

theorem skCavityIterWeightBound_nonneg (m n : ℕ) : 0 ≤ skCavityIterWeightBound m n := by
  induction m generalizing n with
  | zero => simp [skCavityIterWeightBound]
  | succ m ih =>
    simp only [skCavityIterWeightBound]
    have := ih (n + 2)
    positivity

/-- The canonical choice enumeration has the same total absolute weight as the
previous existential expansion. -/
theorem sum_abs_skCavityChoiceWeight (m n : ℕ) :
    (∑ c : SKCavityDerivativeChoices m n, |skCavityChoiceWeight m n c|) =
      skCavityIterWeightBound m n := by
  induction m generalizing n with
  | zero =>
    change (∑ _ : Unit, |(1 : ℝ)|) = 1
    simp
  | succ m ih =>
    change (∑ c : SKCavityReplicaPair n × SKCavityDerivativeChoices m (n + 2),
      |skCavityReplicaPairWeight n c.1 * skCavityChoiceWeight m (n + 2) c.2|) = _
    simp only [abs_mul, Fintype.sum_prod_type]
    rw [← sum_mul_sum, sum_abs_skCavityReplicaPairWeight, ih]
    rfl

/-- **Pointwise structure of the iterated cavity kernel.**  There are a finite index type `T`
(of `m`-tuples of replica pairs), weights `w`, a position map `ι` of the `n` old replicas and
position maps `a t r ≠ b t r` of the pair `r` of the tuple `t`, all independent of `N, β, q, f`,
such that `skCavityIterKernel N β q m n f` is `f ∘ ι` times `∑_t w_t ∏_r K(a_{t,r}, b_{t,r})`
with `K = skCavityPathKernel`.  Moreover `∑_t |w_t| = skCavityIterWeightBound m n`. -/
theorem skCavityIterKernel_structure (m n : ℕ) :
    ∃ (T : Type) (_ : Fintype T) (w : T → ℝ) (ι : Fin n → Fin (skCavityIterReplicaCount m n))
      (a b : T → Fin m → Fin (skCavityIterReplicaCount m n)),
      Function.Injective ι ∧ (∀ t r, a t r ≠ b t r) ∧
      ∑ t, |w t| = skCavityIterWeightBound m n ∧
      ∀ (N : ℕ) (β q : ℝ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
        (τ : Fin (skCavityIterReplicaCount m n) → Fin (N + 1) → ℤˣ),
        skCavityIterKernel N β q m n f τ = f (fun r => τ (ι r)) *
          ∑ t, w t * ∏ r, skCavityPathKernel N β q (τ (a t r)) (τ (b t r)) := by
  refine ⟨SKCavityDerivativeChoices m n, inferInstance, skCavityChoiceWeight m n,
    skCavityIterOldEmbedding m n,
    (fun c r => (skCavityChoiceEndpoints m n c r).1),
    (fun c r => (skCavityChoiceEndpoints m n c r).2),
    (skCavityIterOldEmbedding m n).injective, skCavityChoiceEndpoints_ne m n,
    sum_abs_skCavityChoiceWeight m n, ?_⟩
  exact fun N β q f τ => skCavityIterKernel_eq_choice_sum N m n β q f τ

/-- Pointwise bound on the iterated cavity kernel: `β^{2m} |f ∘ ι|` times a nonnegative
weighted sum of products of truncated overlap deviations. -/
theorem abs_skCavityIterKernel_le (m n : ℕ) :
    ∃ (T : Type) (_ : Fintype T) (w : T → ℝ) (ι : Fin n → Fin (skCavityIterReplicaCount m n))
      (a b : T → Fin m → Fin (skCavityIterReplicaCount m n)),
      Function.Injective ι ∧ (∀ t r, a t r ≠ b t r) ∧ (∀ t, 0 ≤ w t) ∧
      ∑ t, w t = skCavityIterWeightBound m n ∧
      ∀ (N : ℕ) (β q : ℝ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
        (τ : Fin (skCavityIterReplicaCount m n) → Fin (N + 1) → ℤˣ),
        |skCavityIterKernel N β q m n f τ| ≤ (β ^ 2) ^ m * |f (fun r => τ (ι r))| *
          ∑ t, w t * ∏ r, skCavityTruncDev N q (τ (a t r)) (τ (b t r)) := by
  obtain ⟨T, hT, w, ι, a, b, hι, hab, hw, h⟩ := skCavityIterKernel_structure m n
  refine ⟨T, hT, fun t => |w t|, ι, a, b, hι, hab, fun t => abs_nonneg _, hw, ?_⟩
  intro N β q f τ
  have hprod : ∀ t, |∏ r, skCavityPathKernel N β q (τ (a t r)) (τ (b t r))| ≤
      (β ^ 2) ^ m * ∏ r, skCavityTruncDev N q (τ (a t r)) (τ (b t r)) := fun t => by
    rw [abs_prod]
    calc _ ≤ ∏ r : Fin m, (β ^ 2 * skCavityTruncDev N q (τ (a t r)) (τ (b t r))) :=
          by gcongr with r _; exact abs_skCavityPathKernel_le N β q _ _
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hkey : |∑ t, w t * ∏ r, skCavityPathKernel N β q (τ (a t r)) (τ (b t r))| ≤
      (β ^ 2) ^ m * ∑ t, |w t| * ∏ r, skCavityTruncDev N q (τ (a t r)) (τ (b t r)) := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [abs_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hprod t) (abs_nonneg _)
  rw [h N β q f τ, abs_mul, mul_comm ((β ^ 2) ^ m), mul_assoc]
  exact mul_le_mul_of_nonneg_left hkey (abs_nonneg _)

end SpinGlasses
