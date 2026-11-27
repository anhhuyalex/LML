/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Moments of a sum of i.i.d. variables: the recurrence in the number of summands

Let `ν` be a probability measure on a measurable space `Ω` and `f : Ω → ℝ` with all powers
`f^j` `ν`-integrable.
For the product measure `ν^{⊗n}` on `Fin n → Ω` put `S_n(y) = ∑ᵢ f (yᵢ)`.
Splitting off the first coordinate (`measurePreserving_piFinSuccAbove`) gives

`𝔼 S_{n+1}^k = ∑_{j ≤ k} C(k, j) (∫ f^j dν) 𝔼 S_n^{k-j}`.

This is the one-step recurrence used for the quantitative central limit theorem for i.i.d. sums
(Talagrand, Spin Glasses, proof of Theorem 1.4.11, Eq. (1.122)).

## Main declarations

* `ProbabilityTheory.integrable_pow_sum_pi`: powers of `S_n` are integrable.
* `ProbabilityTheory.integral_pow_sum_pi_succ`: the recurrence.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, after Eq. (1.122).
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ}

/-- Every power of a finite sum of variables with integrable powers is integrable; no
independence is needed. -/
theorem integrable_pow_finsetSum {Ω' ι : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsFiniteMeasure μ] (s : Finset ι) {X : ι → Ω' → ℝ} (k : ℕ)
    (hint : ∀ i ∈ s, ∀ j ≤ k, Integrable (fun ω => X i ω ^ j) μ) :
    Integrable (fun ω => (∑ i ∈ s, X i ω) ^ k) μ := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hmem : ∀ i ∈ s, MemLp (X i) k μ := fun i hi => by
    have hm : AEStronglyMeasurable (X i) μ := by
      simpa only [pow_one] using
        (hint i hi 1 (Nat.one_le_iff_ne_zero.2 hk)).aestronglyMeasurable
    refine (integrable_norm_rpow_iff hm (by exact_mod_cast hk) (by simp)).1 ?_
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, norm_pow] using (hint i hi k le_rfl).norm
  have hs : MemLp (fun ω => ∑ i ∈ s, X i ω) k μ := memLp_finsetSum s hmem
  refine (hs.integrable_norm_pow hk).mono' ?_ (ae_of_all _ fun ω => (norm_pow _ _).le)
  exact hs.aestronglyMeasurable.pow k

/-- **Moments of a sum of two independent variables:**
`𝔼 (X + Y)^k = ∑_{j ≤ k} C(k, j) 𝔼 X^j 𝔼 Y^{k-j}`. -/
theorem integral_add_pow_of_indepFun {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {X Y : Ω' → ℝ} (h : IndepFun X Y μ) (k : ℕ)
    (hX : ∀ j ≤ k, Integrable (fun ω => X ω ^ j) μ)
    (hY : ∀ j ≤ k, Integrable (fun ω => Y ω ^ j) μ) :
    ∫ ω, (X ω + Y ω) ^ k ∂μ =
      ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (∫ ω, X ω ^ j ∂μ) *
        ∫ ω, Y ω ^ (k - j) ∂μ := by
  have hind : ∀ i j : ℕ, IndepFun (fun ω => X ω ^ i) (fun ω => Y ω ^ j) μ := fun i j =>
    h.comp (φ := fun x : ℝ => x ^ i) (ψ := fun y : ℝ => y ^ j) (by fun_prop) (by fun_prop)
  simp_rw [add_pow]
  have hle : ∀ j ∈ range (k + 1), j ≤ k := fun j hj => Nat.lt_succ_iff.1 (mem_range.1 hj)
  have hi : ∀ j ∈ range (k + 1),
      Integrable (fun ω => X ω ^ j * Y ω ^ (k - j) * (k.choose j : ℝ)) μ := fun j hj =>
    ((hind j (k - j)).integrable_mul (hX j (hle j hj)) (hY _ (Nat.sub_le _ _))).mul_const _
  rw [integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_mul_const, (hind j (k - j)).integral_fun_mul_eq_mul_integral
    (hX j (hle j hj)).aestronglyMeasurable (hY _ (Nat.sub_le _ _)).aestronglyMeasurable]
  ring

/-- The `k`-th power of the i.i.d. sum `S_n` is integrable if the powers of `f` up to order `k`
are. -/
theorem integrable_pow_sum_pi {k : ℕ} (hint : ∀ j ≤ k, Integrable (fun x => f x ^ j) ν)
    (n : ℕ) :
    Integrable (fun y : Fin n → Ω => (∑ i, f (y i)) ^ k) (Measure.pi fun _ : Fin n => ν) :=
  integrable_pow_finsetSum Finset.univ (X := fun i (y : Fin n → Ω) => f (y i)) k
    fun i _ j hj => ((measurePreserving_eval (fun _ : Fin n => ν) i).integrable_comp
      (hint j hj).aestronglyMeasurable).2 (hint j hj)

/-- **The recurrence for the moments of an i.i.d. sum:**
`𝔼 S_{n+1}^k = ∑_{j ≤ k} C(k, j) (∫ f^j dν) 𝔼 S_n^{k-j}`. -/
theorem integral_pow_sum_pi_succ {k : ℕ} (hint : ∀ j ≤ k, Integrable (fun x => f x ^ j) ν)
    (n : ℕ) :
    ∫ y : Fin (n + 1) → Ω, (∑ i, f (y i)) ^ k ∂(Measure.pi fun _ : Fin (n + 1) => ν) =
      ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (∫ x, f x ^ j ∂ν) *
        ∫ y : Fin n → Ω, (∑ i, f (y i)) ^ (k - j) ∂(Measure.pi fun _ : Fin n => ν) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
  have hcomp : (fun y : Fin (n + 1) → Ω => (∑ i, f (y i)) ^ k) =
      (fun p : Ω × (Fin n → Ω) => (f p.1 + ∑ i, f (p.2 i)) ^ k) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0) := by
    funext y
    simp [Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  rw [hcomp]
  refine (hmp.integral_comp' (fun p : Ω × (Fin n → Ω) => (f p.1 + ∑ i, f (p.2 i)) ^ k)).trans ?_
  have hf : AEMeasurable f ν := by
    simpa only [pow_one] using
      (hint 1 (Nat.one_le_iff_ne_zero.2 hk)).aestronglyMeasurable.aemeasurable
  have hS : AEMeasurable (fun y : Fin n → Ω => ∑ i, f (y i))
      (Measure.pi fun _ : Fin n => ν) :=
    Finset.aemeasurable_fun_sum _ fun i _ => hf.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin n => ν) i).quasiMeasurePreserving
  rw [integral_add_pow_of_indepFun (indepFun_prod₀ hf hS) k
    (fun j hj => (hint j hj).comp_fst _)
    (fun j hj => (integrable_pow_sum_pi (fun i hi => hint i (hi.trans hj)) n).comp_snd _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_fun_fst (fun x => f x ^ j),
    integral_fun_snd (fun y : Fin n → Ω => (∑ i, f (y i)) ^ (k - j)), probReal_univ, probReal_univ,
    one_smul, one_smul]

end ProbabilityTheory
