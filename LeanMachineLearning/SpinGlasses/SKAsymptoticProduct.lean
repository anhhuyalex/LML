/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCorrelationDecay
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The Gibbs measure is asymptotically a product measure (Talagrand, Theorem 1.4.15)

The law `G_{N,n}` of the first `n` spins under the Gibbs measure is close, in total variation, to
the product measure `μ_n` with density `∏ᵢ (1 + ηᵢ ⟨σᵢ⟩)` with respect to the uniform measure.  The
proof expands the indicator of a cylinder `{σ ; σᵢ = ηᵢ for i ≤ n}` in the Walsh basis
`2^{-n} ∑_{I ⊆ [n]} η_I σ_I` and applies the decay of truncated correlations
(`SpinGlasses.integral_sq_prod_sub_prod_le_finset`) to every `σ_I`.

This file contains the deterministic Walsh/Cauchy-Schwarz estimate
`SpinGlasses.sq_sum_abs_le_sum_sq` and its integration over the disorder.

## Main declarations

* `SpinGlasses.sq_sum_abs_le_sum_sq`: for a probability vector `w` and `±1`-valued observables,
  `(∑_η |G(A_η) - ∏ᵢ (1 + ηᵢ ⟨ξᵢ⟩)/2|)² ≤ 2^n ∑_{I ⊆ [n]} (⟨ξ_I⟩ - ∏_{i ∈ I} ⟨ξᵢ⟩)²`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.4.15.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

section Walsh

variable {N n : ℕ} {α : Type*} [Fintype α]

/-- The product of `1 + x e` over `n` sites, for signs `x` and `e`, is `2^n` times the indicator
that all signs agree. -/
theorem prod_one_add_mul_eq {x e : Fin n → ℝ} (hx : ∀ i, x i = 1 ∨ x i = -1)
    (he : ∀ i, e i = 1 ∨ e i = -1) [Decidable (∀ i, x i = e i)] :
    ∏ i, (1 + x i * e i) = 2 ^ n * (if ∀ i, x i = e i then 1 else 0) := by
  have key : ∀ a b : ℝ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      1 + a * b = if a = b then 2 else 0 := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  rw [Finset.prod_congr rfl fun i _ => key _ _ (hx i) (he i), Finset.prod_ite_zero]
  by_cases hall : ∀ i, x i = e i <;> simp [hall]

open scoped Classical in
/-- **Walsh expansion of the cylinder indicator (Eq. (1.134)).**  For `±1`-valued observables, the
Gibbs weight of the cylinder `{ξ_{ι i} = ηᵢ}` minus the product density `∏ᵢ (1 + ηᵢ ⟨ξ_{ι i}⟩) / 2`
is `2^{-n} ∑_{I ⊆ [n]} η_I (⟨ξ_I⟩ - ∏_{i ∈ I} ⟨ξ_{ι i}⟩)`. -/
theorem sum_mul_indicator_sub_prod_eq {ξ : Fin N → α → ℝ} (hξ : ∀ j a, ξ j a = 1 ∨ ξ j a = -1)
    (w : α → ℝ) (ι : Fin n → Fin N) (η : Fin n → ℤˣ) :
    (∑ a, w a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then 1 else 0)) -
        ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, w a * ξ (ι i) a) / 2 =
      (1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ I, ((η i : ℤ) : ℝ)) *
          (∑ a, w a * ∏ i ∈ I, ξ (ι i) a - ∏ i ∈ I, ∑ a, w a * ξ (ι i) a) := by
  have he : ∀ i, ((η i : ℤ) : ℝ) = 1 ∨ ((η i : ℤ) : ℝ) = -1 := fun i => by
    rcases Int.units_eq_one_or (η i) with h | h <;> simp [h]
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hind : ∀ a, (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then (1 : ℝ) else 0) =
      (1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ I, ((η i : ℤ) : ℝ)) * ∏ i ∈ I, ξ (ι i) a := fun a => by
    have h := prod_one_add_mul_eq (x := fun i => ξ (ι i) a) (e := fun i => ((η i : ℤ) : ℝ))
      (fun i => hξ _ _) he
    rw [Finset.prod_one_add] at h
    have h' : ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ I, ((η i : ℤ) : ℝ)) * ∏ i ∈ I, ξ (ι i) a =
        2 ^ n * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then (1 : ℝ) else 0) := by
      rw [← h]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_comm _ _
    rw [h', ← mul_assoc, ← mul_pow]
    norm_num
  have hlhs : ∑ a, w a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then (1 : ℝ) else 0) =
      (1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ I, ((η i : ℤ) : ℝ)) * ∑ a, w a * ∏ i ∈ I, ξ (ι i) a := by
    simp only [hind, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun a _ => by ring
  have hprod : ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, w a * ξ (ι i) a) / 2 =
      (1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ I, ((η i : ℤ) : ℝ)) * ∏ i ∈ I, ∑ a, w a * ξ (ι i) a := by
    rw [Finset.prod_div_distrib, Finset.prod_one_add]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib]
    rw [one_div, inv_pow, inv_mul_eq_div]
  rw [hlhs, hprod, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun I _ => by ring

open scoped Classical in
/-- **The total variation distance to the product measure, deterministically.**  For `±1`-valued
observables and any weight vector `w`, with `c_I = ⟨ξ_I⟩ - ∏_{i ∈ I} ⟨ξ_{ι i}⟩` the truncated
correlations,
`(∑_η |G(A_η) - ∏ᵢ (1 + ηᵢ ⟨ξ_{ι i}⟩) / 2|)² ≤ 2^n ∑_{I ⊆ [n]} c_I²`. -/
theorem sq_sum_abs_le_sum_sq {ξ : Fin N → α → ℝ} (hξ : ∀ j a, ξ j a = 1 ∨ ξ j a = -1)
    (w : α → ℝ) (ι : Fin n → Fin N) :
    (∑ η : Fin n → ℤˣ, |(∑ a, w a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then 1 else 0)) -
        ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, w a * ξ (ι i) a) / 2|) ^ 2 ≤
      2 ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∑ a, w a * ∏ i ∈ I, ξ (ι i) a - ∏ i ∈ I, ∑ a, w a * ξ (ι i) a) ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : Finset (Fin n) → ℝ, ∀ I, c I =
      ∑ a, w a * ∏ i ∈ I, ξ (ι i) a - ∏ i ∈ I, ∑ a, w a * ξ (ι i) a := ⟨_, fun _ => rfl⟩
  simp only [← hc]
  have hcardη : (Finset.univ : Finset (Fin n → ℤˣ)).card = 2 ^ n := by
    simp [Fintype.card_units_int]
  have hcardI : ((Finset.univ : Finset (Fin n)).powerset).card = 2 ^ n := by simp
  have he2 : ∀ (η : Fin n → ℤˣ) (I : Finset (Fin n)), (∏ i ∈ I, ((η i : ℤ) : ℝ)) ^ 2 = 1 :=
    fun η I => by
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rcases Int.units_eq_one_or (η i) with h | h <;> simp [h]
  simp only [sum_mul_indicator_sub_prod_eq hξ w ι, ← hc]
  have hD : ∀ η : Fin n → ℤˣ, ((1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
      (∏ i ∈ I, ((η i : ℤ) : ℝ)) * c I) ^ 2 ≤ (1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset
        (Fin n)).powerset, c I ^ 2 := fun η => by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)).powerset)
      (f := fun I => (∏ i ∈ I, ((η i : ℤ) : ℝ)) * c I)
    simp only [mul_pow, he2, one_mul, hcardI] at h
    calc _ = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n * (∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ i ∈ I, ((η i : ℤ) : ℝ)) * c I) ^ 2 := by ring
      _ ≤ (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n * (2 ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
          c I ^ 2) := by gcongr; exact_mod_cast h
      _ = _ := by
          have h2' : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
          linear_combination ((1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
            c I ^ 2) * h2'
  calc _ ≤ ((Finset.univ : Finset (Fin n → ℤˣ)).card : ℝ) * ∑ η : Fin n → ℤˣ,
        |(1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ i ∈ I, ((η i : ℤ) : ℝ)) * c I| ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ 2 ^ n * ∑ η : Fin n → ℤˣ, (1 / 2 : ℝ) ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
          c I ^ 2 := by
        rw [hcardη]
        push_cast
        gcongr with η _
        rw [sq_abs]
        exact hD η
    _ = _ := by
        rw [Finset.sum_const, hcardη]
        simp only [nsmul_eq_mul]
        push_cast
        have h2 : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
        linear_combination (2 ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, c I ^ 2) * h2

end Walsh

section Integrated

variable {N n : ℕ} {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] {P : Measure Ω}
  [IsProbabilityMeasure P] {ξ : Fin N → α → ℝ} {w : Ω → α → ℝ}

open scoped Classical in
/-- **Theorem 1.4.15 for a site-symmetric random Gibbs state.**  If the observables are `±1`-valued
and the law of the random Gibbs weights is symmetric between sites, then for every `|q| ≤ 1` and
every injective choice `ι` of `n` sites,
`𝔼 ‖G_{N,n} - μ_n‖² ≤ 4^n K(n) ν((R₁,₂ - q)²)`, where `‖⋅‖` is the total variation distance
`∑_η |G(A_η) - μ_n({η})|`, `A_η = {ξ_{ι i} = ηᵢ}`, and `μ_n({η}) = ∏ᵢ (1 + ηᵢ ⟨ξ_{ι i}⟩) / 2`. -/
theorem integral_sq_sum_abs_le (hN : 0 < N) (hξ : ∀ j a, ξ j a = 1 ∨ ξ j a = -1)
    (hw0 : ∀ ω a, 0 ≤ w ω a) (hw1 : ∀ ω, ∑ a, w ω a = 1) (hwm : ∀ a, Measurable fun ω => w ω a)
    (act : Equiv.Perm (Fin N) → α ≃ α) (hact : ∀ π i a, ξ i (act π a) = ξ (π i) a)
    (hsym : ∀ π : Equiv.Perm (Fin N), ∃ φ : Ω → Ω, MeasurePreserving φ P P ∧
      ∀ ω a, w (φ ω) a = w ω (act π a)) {q : ℝ} (hq : |q| ≤ 1) (ι : Fin n → Fin N)
    (hι : Function.Injective ι) :
    ∫ ω, (∑ η : Fin n → ℤˣ, |(∑ a, w ω a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then 1 else 0)) -
        ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, w ω a * ξ (ι i) a) / 2|) ^ 2 ∂P ≤
      4 ^ n * spinDecorrConst n * ∫ ω, ∑ x, ∑ y, w ω x * w ω y *
        ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 ∂P := by
  have habs : ∀ i a, |ξ i a| ≤ 1 := fun i a => by rcases hξ i a with h | h <;> simp [h]
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∫ ω, ∑ x, ∑ y, w ω x * w ω y *
      ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 ∂P := ⟨_, rfl⟩
  rw [← hX]
  obtain ⟨TV, hTV⟩ : ∃ TV : Ω → ℝ, ∀ ω, TV ω = (∑ η : Fin n → ℤˣ,
      |(∑ a, w ω a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then 1 else 0)) -
        ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, w ω a * ξ (ι i) a) / 2|) ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : Finset (Fin n) → Ω → ℝ, ∀ I ω, cc I ω =
      (∑ a, w ω a * ∏ i ∈ I, ξ (ι i) a - ∏ i ∈ I, ∑ a, w ω a * ξ (ι i) a) ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  have hTVint : Integrable TV P := by
    have h : TV = fun ω => (fun v : α → ℝ => (∑ η : Fin n → ℤˣ,
        |(∑ a, v a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then 1 else 0)) -
          ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, v a * ξ (ι i) a) / 2|) ^ 2) (w ω) := funext hTV
    rw [h]
    exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : α → ℝ => (∑ η : Fin n → ℤˣ,
        |(∑ a, v a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then 1 else 0)) -
          ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, v a * ξ (ι i) a) / 2|) ^ 2) (by fun_prop)
  have hccint : ∀ I, Integrable (cc I) P := fun I => by
    have h : cc I = fun ω => (fun v : α → ℝ => (∑ a, v a * ∏ i ∈ I, ξ (ι i) a -
        ∏ i ∈ I, ∑ a, v a * ξ (ι i) a) ^ 2) (w ω) := funext (hcc I)
    rw [h]
    exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : α → ℝ => (∑ a, v a *
        ∏ i ∈ I, ξ (ι i) a - ∏ i ∈ I, ∑ a, v a * ξ (ι i) a) ^ 2) (by fun_prop)
  have hccle : ∀ I : Finset (Fin n), ∫ ω, cc I ω ∂P ≤ spinDecorrConst n * X := fun I => by
    have h := integral_sq_prod_sub_prod_le_finset hN habs hw0 hw1 hwm act hact hsym hq
      (I.map ⟨ι, hι⟩)
    rw [← hX] at h
    simp only [Finset.prod_map, Function.Embedding.coeFn_mk, Finset.card_map] at h
    calc ∫ ω, cc I ω ∂P ≤ spinDecorrConst I.card * X := by simpa only [hcc] using h
      _ ≤ spinDecorrConst n * X := by
          refine mul_le_mul_of_nonneg_right (spinDecorrConst_mono ?_) ?_
          · simpa using Finset.card_le_univ I
          · rw [hX]
            exact integral_nonneg fun ω => Finset.sum_nonneg fun x _ => Finset.sum_nonneg
              fun y _ => mul_nonneg (mul_nonneg (hw0 ω x) (hw0 ω y)) (sq_nonneg _)
  have hpt : ∀ ω, TV ω ≤ 2 ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, cc I ω :=
    fun ω => by
      rw [hTV]; simp only [hcc]
      exact sq_sum_abs_le_sum_sq hξ (w ω) ι
  rw [show (∫ ω, (∑ η : Fin n → ℤˣ,
      |(∑ a, w ω a * (if ∀ i, ξ (ι i) a = ((η i : ℤ) : ℝ) then 1 else 0)) -
        ∏ i, (1 + ((η i : ℤ) : ℝ) * ∑ a, w ω a * ξ (ι i) a) / 2|) ^ 2 ∂P) = ∫ ω, TV ω ∂P from
    integral_congr_ae (ae_of_all _ fun ω => (hTV ω).symm)]
  calc ∫ ω, TV ω ∂P ≤ ∫ ω, 2 ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, cc I ω ∂P :=
        integral_mono hTVint ((integrable_finsetSum _ fun I _ => hccint I).const_mul _) hpt
    _ = 2 ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, ∫ ω, cc I ω ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun I _ => hccint I]
    _ ≤ 2 ^ n * ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, spinDecorrConst n * X := by
        gcongr with I _
        exact hccle I
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, Finset.card_univ,
          Fintype.card_fin]
        have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
        push_cast
        rw [h4]
        ring

end Integrated

end SpinGlasses
