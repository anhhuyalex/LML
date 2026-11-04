/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGibbsMoments
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Conditional mixed moments with enumerated factors

The pair/single monomial estimates extend to arbitrary enumerated factors. The
reference is an integral over explicit independent Gaussian coordinates, so that
finite linear combinations can be expanded on both sides with the same algebra.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real ENNReal

universe u v

namespace SpinGlasses

/-- Conditional pair/single moments for an arbitrary finite enumeration, with an
explicit independent-Gaussian reference. All constants precede the physical parameters. -/
theorem sk_T_enumerated_gibbs_moments_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type u} [Fintype R] [LinearOrder R] [Nonempty R]
    {K : Type v} [Fintype K] (S : K → Bool) (a b : K → R)
    (hord : ∀ j, S j = true → a j < b j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T := fun j g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ (a j) i : ℝ) - bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)
    let V := fun g => ((N : ℝ) + 1) ^ ((Fintype.card K : ℝ) / 2) *
      ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ j, T j g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let A2 : ℝ := α / (1 - β ^ 2 * α)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * A2) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh))
    let G : ℝ := ∫ z : (R × R) ⊕ R → ℝ,
      ∏ j, if S j then Real.sqrt A2 * z (.inl (a j, b j))
        else Real.sqrt B2 * z (.inr (a j))
      ∂(Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1)
    let P := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
    MemLp V 2 P ∧ |(∫ g, V g ∂P) - G| ≤ C / Real.sqrt ((N : ℝ) + 1) ∧
      (∫ g, (V g - G) ^ 2 ∂P) ≤ C / Real.sqrt ((N : ℝ) + 1) := by
  let D := (R × R) ⊕ R
  let d : K → D := fun j => if S j then .inl (a j, b j) else .inr (a j)
  let c : D → ℕ := fun κ => ((univ : Finset K).filter fun j => d j = κ).card
  let kP : R × R → ℕ := fun p => c (.inl p)
  let kS : R → ℕ := fun r => c (.inr r)
  have hcard : (∑ p, kP p) + ∑ r, kS r = Fintype.card K := by
    have hc := (Finset.card_eq_sum_card_fiberwise (f := d) (s := univ) (t := univ)
      (fun _ _ => mem_univ _)).symm
    rw [Fintype.sum_sum_type] at hc
    exact hc
  have ho : ∀ p, 0 < kP p → p.1 < p.2 := by
    intro p hp
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hp
    have hd := (Finset.mem_filter.mp hj).2
    by_cases hs : S j = true
    · change (if S j then Sum.inl (a j, b j) else Sum.inr (a j)) = Sum.inl p at hd
      rw [ite_eq_left hs] at hd
      have he : (a j, b j) = p := Sum.inl.inj hd
      simpa only [← he] using hord j hs
    · simp [d, hs] at hd
  have hfiber (F : D → ℝ) : (∏ j, F (d j)) = ∏ κ, F κ ^ c κ := by
    simpa only [Finset.prod_const] using
      (Finset.prod_fiberwise' (univ : Finset K) d F).symm
  have hpow (F : D → ℝ) : (∏ j, F (d j)) =
      (∏ p, F (.inl p) ^ kP p) * ∏ r, F (.inr r) ^ kS r := by
    rw [hfiber, Fintype.prod_sum_type]
  obtain ⟨C₁, hC₁0, _, _, hMean⟩ := sk_T_gibbs_moment_first_two_uniform β₀ hβ₀ kP kS ho
  obtain ⟨C₀, hC₀0, hMSE⟩ := sk_T_gibbs_moment_variance_uniform β₀ hβ₀ kP kS ho
  refine ⟨C₁ + C₀, by positivity, fun β h q hfix hb N => ?_⟩
  intro E bmean T V qh α A2 B2 G P
  let TP := fun (p : R × R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
    (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ p.1 i : ℝ) - bmean g i) *
      ((ρ p.2 i : ℝ) - bmean g i)
  let TS := fun (r : R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
    (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ r i : ℝ) - bmean g i) * bmean g i
  let V₀ := fun g => ((N : ℝ) + 1) ^
    ((((∑ p, kP p) + ∑ r, kS r : ℕ) : ℝ) / 2) *
      ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (∏ p, TP p g ρ ^ kP p) * ∏ r, TS r g ρ ^ kS r
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
  let G₀ : ℝ := (∏ p, ∫ x : ℝ, (Real.sqrt A2 * x) ^ kP p ∂gaussianReal 0 1) *
    (∏ r, ∫ x : ℝ, (Real.sqrt B2 * x) ^ kS r ∂gaussianReal 0 1)
  have hprod (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ) :
      (∏ j, T j g ρ) = (∏ p, TP p g ρ ^ kP p) * ∏ r, TS r g ρ ^ kS r := by
    let F : D → ℝ := Sum.elim (fun p => TP p g ρ) (fun r => TS r g ρ)
    have hj (j : K) : T j g ρ = F (d j) := by
      cases hs : S j <;> simp [T, F, d, hs, TP, TS]
    simp_rw [hj]
    exact hpow F
  have hVeq : V = V₀ := by
    funext g
    dsimp only [V, V₀]
    rw [hcard]
    simp_rw [hprod]
  have hG : G = G₀ := by
    let σ : D → ℝ := Sum.elim (fun _ => Real.sqrt A2) (fun _ => Real.sqrt B2)
    have hg (z : D → ℝ) :
        (∏ j, if S j then Real.sqrt A2 * z (.inl (a j, b j))
          else Real.sqrt B2 * z (.inr (a j))) = ∏ κ, (σ κ * z κ) ^ c κ := by
      rw [← hfiber]
      apply Finset.prod_congr rfl
      intro j _
      cases hs : S j <;> simp [d, σ, hs]
    dsimp only [G]
    simp_rw [hg]
    rw [integral_fintype_prod_eq_prod (μ := fun _ : D => gaussianReal 0 1)
      (fun κ (x : ℝ) => (σ κ * x) ^ c κ), Fintype.prod_sum_type]
    rfl
  have hm : MemLp V₀ 2 P :=
    (sk_T_multiindex_memLp N β h kP kS 2 (μ := P)).const_mul _
  have he : |(∫ g, V₀ g ∂P) - G₀| ≤ C₁ / Real.sqrt ((N : ℝ) + 1) :=
    (hMean β h q hfix hb N).1
  have hs : (∫ g, (V₀ g - G₀) ^ 2 ∂P) ≤ C₀ / Real.sqrt ((N : ℝ) + 1) :=
    (hMSE β h q hfix hb N).1
  rw [← hVeq] at hm
  rw [← hVeq, ← hG] at he hs
  refine ⟨hm, he.trans ?_, hs.trans ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end SpinGlasses
