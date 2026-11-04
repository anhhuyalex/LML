/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsProjectionBound
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.GramKernel
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ParametrizedL2
public import Mathlib.Algebra.Order.Chebyshev
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-!
# Moments of the Gram entries `T_{ℓ ℓ'}` (Talagrand, Eq. (1.201))

Two ingredients.

* **A general kernel lemma** (`integral_pi_doubleCentered_pow_le`).  For a Gibbs measure
  `μ = count.tilted f` on a finite set and any kernel `K : α → α → ℝ`, the doubly centered
  quantity `K(σ_ℓ, σ_ℓ') - ∫ K(σ_ℓ, ·) dμ - ∫ K(σ_ℓ', ·) dμ + ∬ K dμ dμ` has `2k`-th moment at
  most `4^{2k} ∬ K^{2k} dμ dμ`.  The proof splits it into four terms and applies Jensen's
  inequality to each.
* **The Gram entries are doubly centered overlaps** (`gram_centered_eq`).  For `±1` observables
  `ξ_i` (`ξ_i² = 1`) with overlap `R(a, b) = N⁻¹ ∑ ξ_i(a) ξ_i(b)`, and `u a i = N^{-1/2}
  (ξ_i(a) - ⟨ξ_i⟩)`, one has `u(σ_ℓ) ⬝ u(σ_ℓ') - v² δ_{ℓ ℓ'}` equal to the doubly centered
  quantity of the kernel `K = R - q` when `v² = 1 - q`.

Together they give `∫ T_{ℓ ℓ'}^{2k} ∂μ^{⊗m} ≤ 4^{2k} E⟨(R - q)^{2k}⟩` (`integral_projGram_pow_le`).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eq. (1.201).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

section Kernel

attribute [local instance] Fintype.ofFinite

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

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

/-- Two distinct replicas of `m` have the product Gibbs law. -/
theorem integral_pi_pair_count_tilted {m : ℕ} {ℓ ℓ' : Fin m} (hℓ : ℓ ≠ ℓ') (f : α → ℝ)
    (H : α → α → ℝ) :
    ∫ σ : Fin m → α, H (σ ℓ) (σ ℓ') ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) =
      ∫ a, ∫ b, H a b ∂(Measure.count.tilted f) ∂(Measure.count.tilted f) := by
  rw [integral_pi_count_tilted_pair hℓ f H, integral_pi_fin_two_count_tilted, integral_count_tilted]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_count_tilted, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **Double centering costs at most a factor `4^{2k}` in the `2k`-th moment.**  If
`T σ = K(σ_ℓ, σ_ℓ') - ∫ K(σ_ℓ, ·) dμ - ∫ K(σ_ℓ', ·) dμ + ∬ K dμ dμ` (the first term replaced by `0`
when `ℓ = ℓ'`), then `∫ T^{2k} dμ^{⊗m} ≤ 4^{2k} ∬ K^{2k} dμ dμ`. -/
theorem integral_pi_doubleCentered_pow_le {m : ℕ} (f : α → ℝ) (K : α → α → ℝ) {k : ℕ}
    (hk : 1 ≤ k) (ℓ ℓ' : Fin m) (T : (Fin m → α) → ℝ)
    (hT : ∀ σ, T σ = (if ℓ = ℓ' then 0 else K (σ ℓ) (σ ℓ')) -
      ∫ b, K (σ ℓ) b ∂(Measure.count.tilted f) - ∫ b, K (σ ℓ') b ∂(Measure.count.tilted f) +
        ∫ a, ∫ b, K a b ∂(Measure.count.tilted f) ∂(Measure.count.tilted f)) :
    ∫ σ : Fin m → α, T σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) ≤
      4 ^ (2 * k) * ∫ a, ∫ b, K a b ^ (2 * k) ∂(Measure.count.tilted f)
        ∂(Measure.count.tilted f) := by
  set μ : Measure α := Measure.count.tilted f with hμ
  set J := ∫ a, ∫ b, K a b ^ (2 * k) ∂μ ∂μ with hJ
  have hJ0 : 0 ≤ J :=
    integral_nonneg fun a => integral_nonneg fun b => Even.pow_nonneg ⟨k, by ring⟩ _
  have hrow : ∀ l : Fin m,
      ∫ σ : Fin m → α, (∫ b, K (σ l) b ∂μ) ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ) ≤ J :=
    fun l => by
    rw [integral_comp_eval (μ := fun _ : Fin m => μ) (i := l)
      (Measurable.of_discrete (f := fun a => (∫ b, K a b ∂μ) ^ (2 * k))).aestronglyMeasurable]
    exact integral_mono Integrable.of_finite Integrable.of_finite fun a =>
      pow_integral_count_tilted_le f (K a) k
  have hmean : (∫ a, ∫ b, K a b ∂μ ∂μ) ^ (2 * k) ≤ J :=
    (pow_integral_count_tilted_le f (fun a => ∫ b, K a b ∂μ) k).trans
      (integral_mono Integrable.of_finite Integrable.of_finite fun a =>
        pow_integral_count_tilted_le f (K a) k)
  let x1 : (Fin m → α) → ℝ := fun σ => if ℓ = ℓ' then 0 else K (σ ℓ) (σ ℓ')
  let x2 : (Fin m → α) → ℝ := fun σ => ∫ b, K (σ ℓ) b ∂μ
  let x3 : (Fin m → α) → ℝ := fun σ => ∫ b, K (σ ℓ') b ∂μ
  let x4 : (Fin m → α) → ℝ := fun _ => ∫ a, ∫ b, K a b ∂μ ∂μ
  have hpt : ∀ σ, T σ ^ (2 * k) ≤
      4 ^ (2 * k - 1) * (x1 σ ^ (2 * k) + x2 σ ^ (2 * k) + x3 σ ^ (2 * k) + x4 σ ^ (2 * k)) :=
    fun σ => by
      rw [hT σ]
      have := add_pow_four_two_mul_le hk (x1 σ) (-x2 σ) (-x3 σ) (x4 σ)
      rw [Even.neg_pow ⟨k, by ring⟩, Even.neg_pow ⟨k, by ring⟩] at this
      simpa [sub_eq_add_neg, add_assoc, x1, x2, x3, x4] using this
  have h1 : ∫ σ : Fin m → α, x1 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ) ≤ J := by
    by_cases h : ℓ = ℓ'
    · simp only [x1, h, ite_true]
      rw [zero_pow (by omega)]
      simpa using hJ0
    · simp only [x1, h, ite_false]
      exact (integral_pi_pair_count_tilted h f (fun a b => K a b ^ (2 * k))).le
  have h4 : ∫ σ : Fin m → α, x4 σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ) ≤ J := by
    simpa [x4, integral_const, probReal_univ] using hmean
  calc ∫ σ : Fin m → α, T σ ^ (2 * k) ∂(Measure.pi fun _ : Fin m => μ)
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
        · exact hrow ℓ
        · exact hrow ℓ'
    _ = 4 ^ (2 * k) * J := by
        have : (4 : ℝ) ^ (2 * k) = 4 ^ (2 * k - 1) * 4 := by
          rw [← pow_succ]; congr 1; omega
        rw [this]; ring

end Kernel

section Ising

attribute [local instance] Fintype.ofFinite

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ)

/-- `E_{σ ~ μ^{⊗2}} (R(σ_0, σ_1) - q)^{2k}`: the `2k`-th moment of the centered overlap
`R(a, b) = N⁻¹ ∑ ξ_i(a) ξ_i(b)`. -/
noncomputable def overlapMoment (f : α → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  ∫ τ : Fin 2 → α, ((N : ℝ)⁻¹ * ∑ i, ξ i (τ 0) * ξ i (τ 1) - q) ^ (2 * k)
    ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f)

omit [Nonempty α] in
theorem overlapMoment_eq (f : α → ℝ) (q : ℝ) (k : ℕ) (K : α → α → ℝ)
    (hK : ∀ a b, K a b = (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q) :
    overlapMoment ξ f q k =
      ∫ a, ∫ b, K a b ^ (2 * k) ∂(Measure.count.tilted f) ∂(Measure.count.tilted f) := by
  simp_rw [hK]
  have h2 := integral_pi_fin_two_count_tilted f
    (fun a b => ((N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q) ^ (2 * k))
  unfold overlapMoment
  rw [h2, integral_count_tilted]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_count_tilted, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [Nonempty α] in
/-- The partial average `∫ R(a, b) dμ(b) = N⁻¹ ∑_i ξ_i(a) ⟨ξ_i⟩`. -/
theorem integral_overlap_right (f : α → ℝ) (a : α) :
    ∫ b, (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b ∂(Measure.count.tilted f) =
      (N : ℝ)⁻¹ * ∑ i, ξ i a * ∫ b, ξ i b ∂(Measure.count.tilted f) := by
  rw [integral_const_mul, integral_finsetSum _ fun i _ => Integrable.of_finite]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- The doubly integrated centered overlap kernel is the centered mean overlap
`∬ (R(a, b) - q) dμ dμ = N⁻¹ ∑_i ⟨ξ_i⟩² - q`. -/
theorem integral_integral_overlap (f : α → ℝ) (q : ℝ) :
    ∫ a, ∫ b, ((N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q) ∂(Measure.count.tilted f)
        ∂(Measure.count.tilted f) =
      (N : ℝ)⁻¹ * ∑ i, (∫ a, ξ i a ∂(Measure.count.tilted f)) ^ 2 - q := by
  set μ : Measure α := Measure.count.tilted f with hμ
  have hin : ∀ a, ∫ b, ((N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q) ∂μ =
      (N : ℝ)⁻¹ * ∫ b, ∑ i, ξ i a * ξ i b ∂μ - q := fun a => by
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul]
    simp
  simp_rw [hin]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_integral_finset_sum_mul μ Finset.univ ξ fun i _ => Integrable.of_finite]
  simp

/-- **Jensen for the mean overlap:** `(N⁻¹ ∑_i ⟨ξ_i⟩² - q)² ≤ E (R_{1,2} - q)²`.  The left side is
the squared deviation of the replica-averaged overlap `⟨R_{1,2}⟩ = N⁻¹ ∑_i ⟨ξ_i⟩²` from `q`. -/
theorem sq_meanOverlap_sub_le_overlapMoment (f : α → ℝ) (q : ℝ) :
    ((N : ℝ)⁻¹ * ∑ i, (∫ a, ξ i a ∂(Measure.count.tilted f)) ^ 2 - q) ^ 2 ≤
      overlapMoment ξ f q 1 := by
  set μ : Measure α := Measure.count.tilted f with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  obtain ⟨K, hK⟩ : ∃ K : α → α → ℝ, ∀ a b, K a b = (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q :=
    ⟨_, fun _ _ => rfl⟩
  have hout : ∫ a, ∫ b, K a b ∂μ ∂μ = (N : ℝ)⁻¹ * ∑ i, (∫ a, ξ i a ∂μ) ^ 2 - q := by
    simp_rw [hK]
    exact integral_integral_overlap ξ f q
  rw [overlapMoment_eq ξ f q 1 K hK, ← hout]
  calc (∫ a, ∫ b, K a b ∂μ ∂μ) ^ 2 ≤ ∫ a, (∫ b, K a b ∂μ) ^ 2 ∂μ :=
        sq_integral_le_integral_sq (measurable_of_finite _) Integrable.of_finite
    _ ≤ ∫ a, ∫ b, K a b ^ (2 * 1) ∂μ ∂μ :=
        integral_mono Integrable.of_finite Integrable.of_finite fun a => by
          simpa using sq_integral_le_integral_sq (measurable_of_finite (K a)) Integrable.of_finite

omit [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem overlap_self (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (hN : 0 < N) (a : α) :
    (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i a = 1 := by
  have : ∀ i, ξ i a * ξ i a = 1 := fun i => by rw [← sq]; exact hξ2 i a
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The Gram entry is a doubly centered overlap.**  Let `u a i = N^{-1/2} (ξ_i(a) - ⟨ξ_i⟩)`,
`K(a, b) = R(a, b) - q` and `v² = 1 - q`.  Then
`u(σ_ℓ) ⬝ u(σ_ℓ') - v² δ_{ℓ ℓ'} = K(σ_ℓ, σ_ℓ') - ∫ K(σ_ℓ, ·) dμ - ∫ K(σ_ℓ', ·) dμ + ∬ K dμ dμ`,
where the first term is `0` for `ℓ = ℓ'`. -/
theorem gram_centered_eq (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (hN : 0 < N) (f : α → ℝ)
    (u : α → Fin N → ℝ)
    (hu : ∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f)))
    (q v : ℝ) (hv : v ^ 2 = 1 - q) (K : α → α → ℝ)
    (hK : ∀ a b, K a b = (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q) {m : ℕ} (σ : Fin m → α)
    (ℓ ℓ' : Fin m) :
    u (σ ℓ) ⬝ᵥ u (σ ℓ') - (if ℓ = ℓ' then v ^ 2 else 0) =
      (if ℓ = ℓ' then 0 else K (σ ℓ) (σ ℓ')) - ∫ b, K (σ ℓ) b ∂(Measure.count.tilted f) -
        ∫ b, K (σ ℓ') b ∂(Measure.count.tilted f) +
          ∫ a, ∫ b, K a b ∂(Measure.count.tilted f) ∂(Measure.count.tilted f) := by
  set μ : Measure α := Measure.count.tilted f with hμ
  set mu : Fin N → ℝ := fun i => ∫ b, ξ i b ∂μ with hmu
  have hA : ∀ a, ∫ b, K a b ∂μ = (N : ℝ)⁻¹ * ∑ i, ξ i a * mu i - q := fun a => by
    simp_rw [hK]
    rw [integral_sub Integrable.of_finite (integrable_const _), integral_overlap_right]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  have hB : ∫ a, ∫ b, K a b ∂μ ∂μ = (N : ℝ)⁻¹ * ∑ i, mu i * mu i - q := by
    simp_rw [hK, ← sq]
    exact integral_integral_overlap ξ f q
  have hdot : u (σ ℓ) ⬝ᵥ u (σ ℓ') = (N : ℝ)⁻¹ * ∑ i, ξ i (σ ℓ) * ξ i (σ ℓ') -
      (N : ℝ)⁻¹ * ∑ i, ξ i (σ ℓ) * mu i - (N : ℝ)⁻¹ * ∑ i, ξ i (σ ℓ') * mu i +
        (N : ℝ)⁻¹ * ∑ i, mu i * mu i := by
    have e : ∀ i, u (σ ℓ) i * u (σ ℓ') i =
        (N : ℝ)⁻¹ * (ξ i (σ ℓ) * ξ i (σ ℓ')) - (N : ℝ)⁻¹ * (ξ i (σ ℓ) * mu i) -
          (N : ℝ)⁻¹ * (ξ i (σ ℓ') * mu i) + (N : ℝ)⁻¹ * (mu i * mu i) := fun i => by
      have : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
      rw [hu, hu]
      calc _ = ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) *
            ((ξ i (σ ℓ) - mu i) * (ξ i (σ ℓ') - mu i)) := by ring
        _ = _ := by rw [this]; ring
    rw [dotProduct]
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdot, hA, hA, hB]
  by_cases h : ℓ = ℓ'
  · subst h
    simp only [ite_true, hv, overlap_self ξ hξ2 hN]
    ring
  · simp only [h, ite_false, hK]
    ring

/-- **Moments of the Gram entries (Talagrand, Eq. (1.201)).**  For `v² = 1 - q`, `N > 0`, `k ≥ 1`
and any replicas `ℓ, ℓ'`, `∫ T_{ℓ ℓ'}^{2k} ∂μ^{⊗m} ≤ 4^{2k} ∫ (R(σ_0, σ_1) - q)^{2k} ∂μ^{⊗2}`,
where `T_{ℓ ℓ'} = u(σ_ℓ) ⬝ u(σ_ℓ') - v² δ_{ℓ ℓ'}` and `u a i = N^{-1/2} (ξ_i(a) - ⟨ξ_i⟩)`. -/
theorem integral_projGram_pow_le (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (hN : 0 < N) {m : ℕ} (f : α → ℝ)
    (u : α → Fin N → ℝ)
    (hu : ∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f)))
    (q v : ℝ) (hv : v ^ 2 = 1 - q) {k : ℕ} (hk : 1 ≤ k) (ℓ ℓ' : Fin m) :
    ∫ σ : Fin m → α, (u (σ ℓ) ⬝ᵥ u (σ ℓ') - if ℓ = ℓ' then v ^ 2 else 0) ^ (2 * k)
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) ≤
        4 ^ (2 * k) * overlapMoment ξ f q k := by
  set K : α → α → ℝ := fun a b => (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q with hKdef
  rw [overlapMoment_eq ξ f q k K fun a b => rfl]
  exact integral_pi_doubleCentered_pow_le f K hk ℓ ℓ' _
    fun σ => gram_centered_eq ξ hξ2 hN f u hu q v hv K (fun a b => rfl) σ ℓ ℓ'

end Ising

end SpinGlasses
