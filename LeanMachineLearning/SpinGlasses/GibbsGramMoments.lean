/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsProjectionBound
public import Mathlib.Algebra.Order.Chebyshev
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-!
# Moments of the Gram entries `T_{ℓ ℓ'}` (Talagrand, Eq. (1.201))

For a Gibbs measure `μ = count.tilted f` on a finite set `α` carrying `±1` observables `ξ_i`
(`ξ_i² = 1`), with overlap `R(a, b) = N⁻¹ ∑ ξ_i(a) ξ_i(b)`, the entries
`T_{ℓ ℓ'} = N⁻¹ ∑_i ξ̇_i(σ_ℓ) ξ̇_i(σ_ℓ') - (1 - q) δ_{ℓ ℓ'}` of the centered data satisfy
`∫ T_{ℓ ℓ'}^{2k} ∂μ^{⊗m} ≤ 4^{2k} J` where `J = ∫ (R(σ_0, σ_1) - q)^{2k} ∂μ^{⊗2}`.  The proof writes
`T` as a signed sum of four terms `R - q`, `A(σ_ℓ) - q`, `A(σ_ℓ') - q`, `B - q` with
`A(a) = ∫ R(a, b) dμ(b)` and `B = ∫ A dμ`, and applies Jensen's inequality to each.

## Main declarations

* `SpinGlasses.overlapGibbs`: the overlap `R`.
* `SpinGlasses.integral_projGram_pow_le`: the bound on the `2k`-th moment of `T_{ℓ ℓ'}`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eq. (1.201).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

section Moments

attribute [local instance] Fintype.ofFinite

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ)

/-- The overlap `R(a, b) = N⁻¹ ∑_i ξ_i(a) ξ_i(b)`. -/
noncomputable def overlapGibbs (a b : α) : ℝ := (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b

/-- **Jensen's inequality for even powers under a Gibbs measure.** -/
theorem pow_integral_count_tilted_le (f h : α → ℝ) (k : ℕ) :
    (∫ a, h a ∂(Measure.count.tilted f)) ^ (2 * k) ≤
      ∫ a, h a ^ (2 * k) ∂(Measure.count.tilted f) := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * k)) :=
    (Even.convexOn_pow (𝕜 := ℝ) ⟨k, by ring⟩)
  have := hconv.map_integral_le (μ := Measure.count.tilted f) (f := h)
    (continuous_pow (2 * k)).continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _)
    Integrable.of_finite Integrable.of_finite
  simpa [average_eq_integral] using this

omit [Nonempty α] in
/-- The partial average `A(a) = ∫ R(a, b) dμ(b) = N⁻¹ ∑_i ξ_i(a) ⟨ξ_i⟩`. -/
theorem integral_overlapGibbs_right (f : α → ℝ) (a : α) :
    ∫ b, overlapGibbs ξ a b ∂(Measure.count.tilted f) =
      (N : ℝ)⁻¹ * ∑ i, ξ i a * ∫ b, ξ i b ∂(Measure.count.tilted f) := by
  unfold overlapGibbs
  rw [integral_const_mul, integral_finsetSum _ fun i _ => Integrable.of_finite]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- The partial overlap `A(a) = ∫ R(a, b) dμ(b)`. -/
noncomputable def partialOverlap (f : α → ℝ) (a : α) : ℝ :=
  ∫ b, overlapGibbs ξ a b ∂(Measure.count.tilted f)

/-- The mean overlap `B = ∫ A dμ`. -/
noncomputable def meanOverlap (f : α → ℝ) : ℝ :=
  ∫ a, partialOverlap ξ f a ∂(Measure.count.tilted f)

/-- `E_{σ ~ μ^{⊗2}} (R(σ_0, σ_1) - q)^{2k}`: the `2k`-th moment of the centered overlap. -/
noncomputable def overlapMoment (f : α → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  ∫ τ : Fin 2 → α, (overlapGibbs ξ (τ 0) (τ 1) - q) ^ (2 * k)
    ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f)

omit [Nonempty α] in
theorem overlapMoment_eq (f : α → ℝ) (q : ℝ) (k : ℕ) :
    overlapMoment ξ f q k = ∫ a, ∫ b, (overlapGibbs ξ a b - q) ^ (2 * k)
      ∂(Measure.count.tilted f) ∂(Measure.count.tilted f) := by
  have h2 := integral_pi_fin_two_count_tilted f (fun a b => (overlapGibbs ξ a b - q) ^ (2 * k))
  unfold overlapMoment
  rw [h2, integral_count_tilted]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_count_tilted, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [Finite α] [MeasurableSingletonClass α] [Nonempty α] in
theorem overlapMoment_nonneg (f : α → ℝ) (q : ℝ) (k : ℕ) : 0 ≤ overlapMoment ξ f q k :=
  integral_nonneg fun τ => Even.pow_nonneg ⟨k, by ring⟩ _

/-- `A(a) - q = ∫ (R(a, b) - q) dμ(b)` and Jensen's inequality. -/
theorem partialOverlap_sub_pow_le (f : α → ℝ) (q : ℝ) (k : ℕ) (a : α) :
    (partialOverlap ξ f a - q) ^ (2 * k) ≤
      ∫ b, (overlapGibbs ξ a b - q) ^ (2 * k) ∂(Measure.count.tilted f) := by
  have h : partialOverlap ξ f a - q = ∫ b, (overlapGibbs ξ a b - q) ∂(Measure.count.tilted f) := by
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    simp [partialOverlap]
  rw [h]
  exact pow_integral_count_tilted_le f _ k

theorem meanOverlap_sub_pow_le (f : α → ℝ) (q : ℝ) (k : ℕ) :
    (meanOverlap ξ f - q) ^ (2 * k) ≤ overlapMoment ξ f q k := by
  have h : meanOverlap ξ f - q = ∫ a, (partialOverlap ξ f a - q) ∂(Measure.count.tilted f) := by
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    simp [meanOverlap]
  rw [overlapMoment_eq, h]
  refine (pow_integral_count_tilted_le f _ k).trans (integral_mono Integrable.of_finite
    Integrable.of_finite fun a => partialOverlap_sub_pow_le ξ f q k a)

/-- One replica marginal: the Gibbs average over `m` replicas of a function of replica `ℓ`. -/
theorem integral_pi_comp_eval_count_tilted {m : ℕ} (f : α → ℝ) (ℓ : Fin m) (G : α → ℝ) :
    ∫ σ : Fin m → α, G (σ ℓ) ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) =
      ∫ a, G a ∂(Measure.count.tilted f) :=
  integral_comp_eval (μ := fun _ : Fin m => Measure.count.tilted f)
    (Measurable.of_discrete (f := G)).aestronglyMeasurable

theorem integral_partialOverlap_sub_pow_le {m : ℕ} (f : α → ℝ) (q : ℝ) (k : ℕ) (ℓ : Fin m) :
    ∫ σ : Fin m → α, (partialOverlap ξ f (σ ℓ) - q) ^ (2 * k)
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) ≤ overlapMoment ξ f q k := by
  rw [integral_pi_comp_eval_count_tilted f ℓ (fun a => (partialOverlap ξ f a - q) ^ (2 * k)),
    overlapMoment_eq]
  exact integral_mono Integrable.of_finite Integrable.of_finite fun a =>
    partialOverlap_sub_pow_le ξ f q k a

section Ising

variable (hξ2 : ∀ i a, ξ i a ^ 2 = 1)

omit [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
include hξ2 in
theorem overlapGibbs_self (hN : 0 < N) (a : α) : overlapGibbs ξ a a = 1 := by
  unfold overlapGibbs
  have : ∀ i, ξ i a * ξ i a = 1 := fun i => by rw [← sq]; exact hξ2 i a
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

omit [Nonempty α] in
/-- The mean overlap is `B = N⁻¹ ∑ ⟨ξ_i⟩²`. -/
theorem meanOverlap_eq (f : α → ℝ) :
    meanOverlap ξ f = (N : ℝ)⁻¹ * ∑ i, (∫ b, ξ i b ∂(Measure.count.tilted f)) ^ 2 := by
  unfold meanOverlap
  have h : ∀ a, partialOverlap ξ f a =
      (N : ℝ)⁻¹ * ∑ i, ξ i a * ∫ b, ξ i b ∂(Measure.count.tilted f) := fun a =>
    integral_overlapGibbs_right ξ f a
  simp_rw [h]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => Integrable.of_finite]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, sq]

omit [Nonempty α] in
include hξ2 in
/-- **The Gram entry as a signed sum of centered overlaps.**  For `v² = 1 - q` and `N > 0`,
`T_{ℓ ℓ'} = x₁ - (A(σ_ℓ) - q) - (A(σ_ℓ') - q) + (B - q)` with `x₁ = R(σ_ℓ, σ_ℓ') - q` for
`ℓ ≠ ℓ'` and `x₁ = 0` for `ℓ = ℓ'`. -/
theorem projGram_centeredData_eq (hN : 0 < N) {m : ℕ} (f : α → ℝ) (σ : Fin m → α) (q v : ℝ)
    (hv : v ^ 2 = 1 - q) (ℓ ℓ' : Fin m) :
    projGram (centeredData ξ f σ) v ℓ ℓ' =
      (if ℓ = ℓ' then 0 else overlapGibbs ξ (σ ℓ) (σ ℓ') - q) -
        (partialOverlap ξ f (σ ℓ) - q) - (partialOverlap ξ f (σ ℓ') - q) +
          (meanOverlap ξ f - q) := by
  have hB := meanOverlap_eq ξ f
  have hA : ∀ a, partialOverlap ξ f a =
      (N : ℝ)⁻¹ * ∑ i, ξ i a * ∫ b, ξ i b ∂(Measure.count.tilted f) := fun a =>
    integral_overlapGibbs_right ξ f a
  set mu : Fin N → ℝ := fun i => ∫ b, ξ i b ∂(Measure.count.tilted f) with hmu
  have hdot : centeredData ξ f σ ℓ ⬝ᵥ centeredData ξ f σ ℓ' =
      overlapGibbs ξ (σ ℓ) (σ ℓ') - partialOverlap ξ f (σ ℓ) - partialOverlap ξ f (σ ℓ') +
        meanOverlap ξ f := by
    have e : ∀ i, centeredData ξ f σ ℓ i * centeredData ξ f σ ℓ' i =
        (N : ℝ)⁻¹ * (ξ i (σ ℓ) * ξ i (σ ℓ')) - (N : ℝ)⁻¹ * (ξ i (σ ℓ) * mu i) -
          (N : ℝ)⁻¹ * (ξ i (σ ℓ') * mu i) + (N : ℝ)⁻¹ * mu i ^ 2 := fun i => by
      unfold centeredData
      have : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
      calc _ = ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) *
            ((ξ i (σ ℓ) - mu i) * (ξ i (σ ℓ') - mu i)) := by ring
        _ = _ := by rw [this]; ring
    rw [dotProduct]
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hB, hA, hA]
    unfold overlapGibbs
    ring
  unfold projGram
  rw [hdot]
  by_cases h : ℓ = ℓ'
  · subst h
    simp only [ite_true, hv, overlapGibbs_self ξ hξ2 hN]
    ring
  · simp only [h, ite_false]
    ring

include hξ2 in
/-- **Moments of the Gram entries (Talagrand, Eq. (1.201)).**  For `v² = 1 - q`, `N > 0`, `k ≥ 1`
and any replicas `ℓ, ℓ'`, `∫ T_{ℓ ℓ'}^{2k} ∂μ^{⊗m} ≤ 4^{2k} ∫ (R(σ_0, σ_1) - q)^{2k} ∂μ^{⊗2}`. -/
theorem integral_projGram_pow_le (hN : 0 < N) {m : ℕ} (f : α → ℝ) (q v : ℝ)
    (hv : v ^ 2 = 1 - q) {k : ℕ} (hk : 1 ≤ k) (ℓ ℓ' : Fin m) :
    ∫ σ : Fin m → α, (projGram (centeredData ξ f σ) v ℓ ℓ') ^ (2 * k)
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) ≤
        4 ^ (2 * k) * overlapMoment ξ f q k := by
  classical
  set J := overlapMoment ξ f q k with hJ
  set μ : Measure α := Measure.count.tilted f with hμ
  have hJ0 : 0 ≤ J := overlapMoment_nonneg ξ f q k
  let x1 : (Fin m → α) → ℝ := fun σ => if ℓ = ℓ' then 0 else overlapGibbs ξ (σ ℓ) (σ ℓ') - q
  let x2 : (Fin m → α) → ℝ := fun σ => partialOverlap ξ f (σ ℓ) - q
  let x3 : (Fin m → α) → ℝ := fun σ => partialOverlap ξ f (σ ℓ') - q
  let x4 : (Fin m → α) → ℝ := fun _ => meanOverlap ξ f - q
  have hpt : ∀ σ, (projGram (centeredData ξ f σ) v ℓ ℓ') ^ (2 * k) ≤
      4 ^ (2 * k - 1) * (x1 σ ^ (2 * k) + x2 σ ^ (2 * k) + x3 σ ^ (2 * k) + x4 σ ^ (2 * k)) :=
    fun σ => by
      rw [projGram_centeredData_eq ξ hξ2 hN f σ q v hv ℓ ℓ']
      have := add_pow_four_two_mul_le hk (x1 σ) (-x2 σ) (-x3 σ) (x4 σ)
      rw [Even.neg_pow ⟨k, by ring⟩, Even.neg_pow ⟨k, by ring⟩] at this
      simpa [sub_eq_add_neg, add_assoc, x1, x2, x3, x4] using this
  have h1 : ∫ σ : Fin m → α, x1 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ) ≤ J := by
    by_cases h : ℓ = ℓ'
    · simp only [x1, h, ite_true]
      rw [zero_pow (by omega)]
      simpa using hJ0
    · have := integral_pi_count_tilted_pair (R := Fin m) h f
        (fun a b => (overlapGibbs ξ a b - q) ^ (2 * k))
      simp only [x1, h, ite_false]
      rw [hμ, this]
      exact le_of_eq rfl
  have h2 := integral_partialOverlap_sub_pow_le ξ f q k ℓ
  have h3 := integral_partialOverlap_sub_pow_le ξ f q k ℓ'
  have h4 : ∫ σ : Fin m → α, x4 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ) ≤ J := by
    simp only [x4, integral_const, probReal_univ, one_smul]
    exact meanOverlap_sub_pow_le ξ f q k
  calc ∫ σ : Fin m → α, (projGram (centeredData ξ f σ) v ℓ ℓ') ^ (2 * k)
        ∂(Measure.pi fun _ : Fin m => μ)
      ≤ ∫ σ : Fin m → α, 4 ^ (2 * k - 1) *
          (x1 σ ^ (2 * k) + x2 σ ^ (2 * k) + x3 σ ^ (2 * k) + x4 σ ^ (2 * k))
          ∂(Measure.pi fun _ : Fin m => μ) :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = 4 ^ (2 * k - 1) * ((∫ σ : Fin m → α, x1 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ)) +
          (∫ σ : Fin m → α, x2 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ)) +
          (∫ σ : Fin m → α, x3 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ)) +
          (∫ σ : Fin m → α, x4 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ))) := by
        rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite]
    _ ≤ 4 ^ (2 * k - 1) * (J + J + J + J) := by
        gcongr
    _ = 4 ^ (2 * k) * J := by
        have : (4 : ℝ) ^ (2 * k) = 4 ^ (2 * k - 1) * 4 := by
          rw [← pow_succ]; congr 1; omega
        rw [this]; ring

end Ising

end Moments

end SpinGlasses
