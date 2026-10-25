/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsGramMoments

/-!
# The model-independent core of Theorem 1.7.11

For a Gibbs measure `μ = count.tilted f` on a finite set `α` carrying `±1` observables `ξ_i`, put
`u a i = N^{-1/2} (ξ_i(a) - ⟨ξ_i⟩)`.  For an exponentially tame `V` with `∫ V(v t) dγ = 0` and
`v² = 1 - q`, the Taylor step (`exists_gibbs_fluctuation_abs_le`) bounds
`|𝔼_y (⟨V(u ⬝ y)⟩)^{2k}|` by the Gibbs average of products of `2k` Gram entries.  The
arithmetic-geometric mean inequality and the moment bound `integral_projGram_pow_le` for the Gram
entries turn this into a multiple of the overlap moment `E⟨(R - q)^{2k}⟩`:

`𝔼_y (⟨V(u ⬝ y)⟩)^{2k} ≤ C · E⟨(R - q)^{2k}⟩`, with `C` depending only on `k` and explicit
derivative bounds for `V` (`exists_gibbs_fluctuation_pow_le`).

Nothing here refers to a particular model: the SK model enters only through the overlap moment
bound `E⟨(R - q)^{2k}⟩ ≤ K / N^k` (`sk_overlap_moment_le_of_exp`), see `SKGaussianFluctuation.lean`.

## Main declarations

* `SpinGlasses.sum_integral_abs_pairProd_le`: the Gibbs average of products of `2k` Gram entries
  is bounded by the overlap moment.
* `SpinGlasses.exists_gibbs_fluctuation_pow_le`: the model-independent bound above.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

/-- Crude arithmetic-geometric mean inequality: `∏ |a_j| ≤ ∑ |a_j|^n` for `n` numbers. -/
theorem prod_abs_le_sum_pow {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ∏ j, |a j| ≤ ∑ j, |a j| ^ n := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun j => |a j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  calc ∏ j, |a j| ≤ ∏ _j : Fin n, |a j₀| :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hj₀ j (Finset.mem_univ j)
    _ = |a j₀| ^ n := by simp
    _ ≤ ∑ j, |a j| ^ n :=
        Finset.single_le_sum (f := fun j => |a j| ^ n) (fun j _ => by positivity)
          (Finset.mem_univ j₀)

section Ising

attribute [local instance] Fintype.ofFinite

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ)

/-- The Gibbs average of the products of `2k` Gram entries is bounded by the overlap moment. -/
theorem sum_integral_abs_pairProd_le (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (hN : 0 < N) (f : α → ℝ)
    (u : α → Fin N → ℝ)
    (hu : ∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f)))
    (q v : ℝ) (hv : v ^ 2 = 1 - q) {k : ℕ} (hk : 1 ≤ k) :
    ∑ p : Fin (2 * k) → Fin (2 * k) × Fin (2 * k), ∫ σ : Fin (2 * k) → α,
        |∏ i, (u (σ (p i).1) ⬝ᵥ u (σ (p i).2) - if (p i).1 = (p i).2 then v ^ 2 else 0)|
          ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) ≤
      ((2 * k) * (2 * k) : ℝ) ^ (2 * k) *
        ((2 * k : ℝ) * (4 ^ (2 * k) * overlapMoment ξ f q k)) := by
  have hn : 0 < 2 * k := by omega
  have hone : ∀ p : Fin (2 * k) → Fin (2 * k) × Fin (2 * k),
      ∫ σ : Fin (2 * k) → α,
          |∏ i, (u (σ (p i).1) ⬝ᵥ u (σ (p i).2) - if (p i).1 = (p i).2 then v ^ 2 else 0)|
          ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) ≤
        (2 * k : ℝ) * (4 ^ (2 * k) * overlapMoment ξ f q k) := fun p => by
    calc _ ≤ ∫ σ : Fin (2 * k) → α, ∑ j : Fin (2 * k),
            (u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) := by
          refine integral_mono Integrable.of_finite Integrable.of_finite fun σ => ?_
          rw [Finset.abs_prod]
          refine (prod_abs_le_sum_pow hn (fun j =>
            u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0)).trans
            (le_of_eq ?_)
          exact Finset.sum_congr rfl fun j _ => Even.pow_abs ⟨k, by ring⟩ _
      _ = ∑ j : Fin (2 * k), ∫ σ : Fin (2 * k) → α,
            (u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) :=
          integral_finsetSum _ fun j _ => Integrable.of_finite
      _ ≤ ∑ _j : Fin (2 * k), 4 ^ (2 * k) * overlapMoment ξ f q k :=
          Finset.sum_le_sum fun j _ =>
            integral_projGram_pow_le ξ hξ2 hN f u hu q v hv hk _ _
      _ = _ := by simp
  calc _ ≤ ∑ _p : Fin (2 * k) → Fin (2 * k) × Fin (2 * k),
        (2 * k : ℝ) * (4 ^ (2 * k) * overlapMoment ξ f q k) :=
        Finset.sum_le_sum fun p _ => hone p
    _ = _ := by simp [Finset.sum_const, Fintype.card_prod]

omit [Finite α] [MeasurableSingletonClass α] in
/-- Centering inside a Gibbs average: `∫ g dμ - c₀ = ∫ (g - c₀) dμ` (`μ` a probability
measure). -/
theorem sub_integral_count_tilted_eq {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f g : α → ℝ) (c₀ : ℝ) :
    (∫ a, g a ∂(Measure.count.tilted f)) - c₀ = ∫ a, (g a - c₀) ∂(Measure.count.tilted f) := by
  rw [integral_sub Integrable.of_finite (integrable_const _)]
  simp

end Ising

/-- **The model-independent core of Theorem 1.7.11.**  Let `k ≥ 1` and let `Cb`, `c` be explicit
exponential bounds for the derivatives of order `≤ 4 k`.  There is `C ≥ 0`, depending only on `k`,
`Cb`, `c`, such that for every exponentially tame `V` obeying these bounds, all `q ≥ 0` and `v` with
`v² = 1 - q` and `∫ V(v t) dγ = 0`, every Gibbs measure `μ = count.tilted f` on a finite set `α` and
`±1` observables `ξ_i` (`N ≥ 1`), with `u a i = N^{-1/2} (ξ_i(a) - ⟨ξ_i⟩)`:
`𝔼_y (∫ V(u ⬝ y) dμ)^{2k} ≤ C · E⟨(R - q)^{2k}⟩`. -/
theorem exists_gibbs_fluctuation_pow_le {k : ℕ} (hk : 1 ≤ k) {Cb : ℕ → ℝ} {c : ℝ}
    (hCb : ∀ j ≤ 2 * (2 * k), 0 ≤ Cb j) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℝ), ExpTame V →
      (∀ j ≤ 2 * (2 * k), ∀ x, |deriv^[j] V x| ≤ Cb j * Real.exp (c * |x|)) →
      ∀ q v : ℝ, 0 ≤ q → v ^ 2 = 1 - q → ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0 →
      ∀ (N : ℕ), 0 < N → ∀ (α : Type) [Fintype α] [Nonempty α] [MeasurableSpace α]
      [MeasurableSingletonClass α] (ξ : Fin N → α → ℝ), (∀ i a, ξ i a ^ 2 = 1) →
      ∀ (f : α → ℝ) (u : α → Fin N → ℝ),
      (∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f))) →
      ∫ y : Fin N → ℝ, (∫ a, V (u a ⬝ᵥ y) ∂(Measure.count.tilted f)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤ C * overlapMoment ξ f q k := by
  obtain ⟨C, hC0, hC⟩ := exists_gibbs_fluctuation_abs_le (m := 2 * k) (by omega) hCb hc
  refine ⟨C * (((2 * k) * (2 * k) : ℝ) ^ (2 * k) * ((2 * k : ℝ) * 4 ^ (2 * k))), by positivity, ?_⟩
  intro V hV hbd q v hq hv hV0 N hN α _ _ _ _ ξ hξ2 f u hu
  have hξ : ∀ i a, |ξ i a| ≤ 1 := fun i a =>
    abs_le.2 ⟨by nlinarith [hξ2 i a], by nlinarith [hξ2 i a]⟩
  have h1 := hC V hV hbd v (by nlinarith) hV0 N α u (dotProduct_centered_le u ξ hξ f hu) f
    (integral_centered_eq_zero u ξ f hu)
  have h2 := sum_integral_abs_pairProd_le ξ hξ2 hN f u hu q v hv hk
  calc _ ≤ _ := le_abs_self _
    _ ≤ _ := h1
    _ ≤ C * (((2 * k) * (2 * k) : ℝ) ^ (2 * k) *
          ((2 * k : ℝ) * (4 ^ (2 * k) * overlapMoment ξ f q k))) :=
        mul_le_mul_of_nonneg_left h2 hC0
    _ = _ := by ring

end SpinGlasses
