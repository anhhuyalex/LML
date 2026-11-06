/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectLeading
public import
  LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.Contractions.SKOverlapCLTComparison

/-!
# Comparison of rectangular products (Talagrand, Eq. (1.344))

Step E3c of the proof of Proposition 1.11.10: for two pairings `P₀`, `P` of the `2m` difference
labels, the product of the truncated rectangles `∏_{P₀} U⁻ ∏_P U⁻` has (i) nearly the same mean
under the decoupled system (`u = 0`) as under the coupled `(N+1)`-spin system (`u = 1`), and
(ii) nearly the same coupled mean as the product of the full rectangles `∏_{P₀} U ∏_P U`.
Both errors are `O((N+1)^{-(2m+1)/2})`. The book states this as "we have explained in detail
why" (D1 of the generality audit); these are the precise lemmas.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- Second moment of a product of two pairing block products of truncated rectangles. It is the
product of `m + m` rectangles, so it decays like `(N+1)^{-(m+m)}`. -/
theorem sk_hanen_two_pairings_sq_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ)
      (P₀ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n),
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      skCavityPathMean N n β q h 1 (fun σ =>
        (P₀.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)) *
          P.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc))) ^ 2) ≤
        C / ((N : ℝ) + 1) ^ (m + m) := by
  obtain ⟨C, hC, hCb⟩ := sk_hanen_rect_prod_sq_le β₀ hβ₀ (m + m) 1
  refine ⟨C, hC, ?_⟩
  intro β h q hfix hβ N n P₀ P pairMap hdisj
  obtain ⟨u, v, huv, hlab⟩ :=
    Renormalization.exists_labels_prod_pairWeight_mul (m := m) P₀ P (by simp)
  have hb := hCb β h q hfix hβ N n m pairMap hdisj u v huv (fun _ => 1) (by simp)
  have hprod (ρ : Fin n → Fin N → ℤˣ) :
      (∏ j : Fin (m + m), skCavityRectTrunc N n m q pairMap (u j) (v j) ρ) =
        P₀.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v ρ) *
        P.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v ρ) :=
    hlab _ fun a b => skCavityRectTrunc_comm N n m q pairMap a b ρ
  simpa only [hprod, one_mul] using hb

/-- **Eq. (1.344), first half.** The decoupled and coupled means of a product of two pairing
block products of truncated rectangles agree up to `O((N+1)^{-(2m+1)/2})`: one application of
the order-zero Taylor estimate with the second-moment bound of `sk_hanen_two_pairings_sq_le`. -/
theorem sk_hanen_trunc_old_vs_coupled (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P₀ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n),
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      let f := fun σ : Fin n → Fin (N + 1) → ℤˣ =>
        P₀.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)) *
          P.blockProduct (Renormalization.pairWeight fun u v =>
            skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc))
      |skCavityPathMean N n β q h 1 f - skCavityPathMean N n β q h 0 f| ≤
        K / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨D, hD, hDb⟩ := skCavityPathMean_taylor_coefficient_le β₀ hβ₀ 0 (m + m) n
  obtain ⟨C, hC, hCb⟩ := sk_hanen_two_pairings_sq_le β₀ hβ₀ m
  refine ⟨D * Real.sqrt C, mul_pos hD (Real.sqrt_pos.2 hC), ?_⟩
  intro β h q hfix hβ N P₀ P pairMap hdisj f
  have hb := hDb β h q hfix hβ N f C hC.le (hCb β h q hfix hβ N n P₀ P pairMap hdisj)
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  have hexp : ((0 : ℕ) : ℝ) + ((m + m : ℕ) : ℝ) + 1 = ((2 * m + 1 : ℕ) : ℝ) := by
    push_cast; ring
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDerivWithin_zero,
    hexp] at hb
  exact hb

/-- **Eq. (1.344), second half.** Replacing the truncated rectangles by the full rectangles on
`N + 1` sites changes the coupled mean of a product of two pairing block products by
`O((N+1)^{-(2m+1)/2})`: the two differ by the spin correction `(N+1)^{-1} η_J` of each of the
`m + m` rectangles (`sk_overlap_prod_sub_truncated_le`). -/
theorem sk_hanen_trunc_vs_full (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P₀ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n),
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      (∀ j, (pairMap j).1 ≠ (pairMap j).2) →
      let C := fun (σ : Fin n → Fin (N + 1) → ℤˣ) (u v : Fin (2 * m)) =>
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).2 i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).2 i : ℝ))
      |skCavityPathMean N n β q h 1 (fun σ =>
          P₀.blockProduct (Renormalization.pairWeight fun u v =>
              skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)) *
            P.blockProduct (Renormalization.pairWeight fun u v =>
              skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc))) -
        skCavityPathMean N n β q h 1 (fun σ =>
          P₀.blockProduct (Renormalization.pairWeight (C σ)) *
            P.blockProduct (Renormalization.pairWeight (C σ)))| ≤
        K / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK, hKb⟩ := sk_overlap_prod_sub_truncated_le β₀ hβ₀ (κ := Fin (m + m))
    (ι := fun _ => Bool × Bool)
    (fun _ e => (if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) 1
  refine ⟨K, hK, ?_⟩
  intro β h q hfix hβ N P₀ P pairMap hdisj hxy C
  obtain ⟨u, v, huv, hlab⟩ :=
    Renormalization.exists_labels_prod_pairWeight_mul (m := m) P₀ P (by simp)
  let a : Fin (m + m) → Bool × Bool → Fin n := fun j e =>
    if e.1 then (pairMap (u j)).2 else (pairMap (u j)).1
  let b : Fin (m + m) → Bool × Bool → Fin n := fun j e =>
    if e.2 then (pairMap (v j)).2 else (pairMap (v j)).1
  have hab (j : Fin (m + m)) (e : Bool × Bool) : a j e ≠ b j e := by
    have hd := hdisj (u j) (v j) (huv j)
    rcases e with ⟨e₁, e₂⟩
    cases e₁ <;> cases e₂ <;> simp only [a, b, Bool.false_eq_true, ite_false, ite_true]
    · exact hd.1
    · exact hd.2.1
    · exact hd.2.2.1
    · exact hd.2.2.2
  have hkernel (σ : Fin n → Fin (N + 1) → ℤˣ) (x y : Fin (2 * m)) :
      C σ x y = ∑ e : Bool × Bool,
        ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
          ((N + 1 : ℝ)⁻¹ * ((fun w : Fin (N + 1) =>
            (σ (if e.1 then (pairMap x).2 else (pairMap x).1) w : ℝ)) ⬝ᵥ
            fun w : Fin (N + 1) => (σ (if e.2 then (pairMap y).2 else (pairMap y).1) w : ℝ))
            - q) := by
    simp only [C, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ite_false,
      ite_true, dotProduct]
    ring
  have hb := hKb β h q hfix hβ N n a b hab (skCavityPathMean N n β q h 1)
    (fun Φ => skCavityPathMean_one N n β q h Φ)
    (fun j σ => C σ (u j) (v j))
    (fun j σ => skCavityRectTrunc N n m q pairMap (u j) (v j) (fun r i => σ r i.castSucc))
    (fun j σ => ∑ e : Bool × Bool,
      ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
        ((σ (a j e) (Fin.last N) : ℝ) * (σ (b j e) (Fin.last N) : ℝ)))
    (fun j σ => hkernel σ (u j) (v j))
    (fun j σ => skCavityRectTrunc_eq_sum_bool N n m q pairMap (u j) (v j)
      (fun r i => σ r i.castSucc))
    (fun j σ => rfl) (fun _ => 1) (by simp)
  have hprod (G : Fin (2 * m) → Fin (2 * m) → ℝ) (hG : ∀ x y, G x y = G y x) :
      ∏ j : Fin (m + m), G (u j) (v j) =
        P₀.blockProduct (Renormalization.pairWeight G) *
          P.blockProduct (Renormalization.pairWeight G) := hlab G hG
  have hCsymm (σ : Fin n → Fin (N + 1) → ℤˣ) (x y : Fin (2 * m)) : C σ x y = C σ y x := by
    simp only [C]
    have h1 (s t : Fin n) : ∑ i : Fin (N + 1), (σ s i : ℝ) * (σ t i : ℝ) =
        ∑ i : Fin (N + 1), (σ t i : ℝ) * (σ s i : ℝ) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1 (pairMap x).1 (pairMap y).1, h1 (pairMap x).2 (pairMap y).1,
      h1 (pairMap x).1 (pairMap y).2, h1 (pairMap x).2 (pairMap y).2]
    ring
  have hFull (σ : Fin n → Fin (N + 1) → ℤˣ) :
      ∏ j : Fin (m + m), C σ (u j) (v j) =
        P₀.blockProduct (Renormalization.pairWeight (C σ)) *
          P.blockProduct (Renormalization.pairWeight (C σ)) := hprod _ (hCsymm σ)
  have hTrunc (σ : Fin n → Fin (N + 1) → ℤˣ) :
      ∏ j : Fin (m + m), skCavityRectTrunc N n m q pairMap (u j) (v j) (fun r i => σ r i.castSucc)
        = P₀.blockProduct (Renormalization.pairWeight fun x y =>
            skCavityRectTrunc N n m q pairMap x y (fun r i => σ r i.castSucc)) *
          P.blockProduct (Renormalization.pairWeight fun x y =>
            skCavityRectTrunc N n m q pairMap x y (fun r i => σ r i.castSucc)) :=
    hprod _ fun x y => skCavityRectTrunc_comm N n m q pairMap x y _
  simp only [hFull, hTrunc, one_mul, Fintype.card_fin] at hb
  have hcard : ((m + m + 1 : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcard] at hb
  have hsub := (skCavityPathMeanLM N n β q h 1).map_sub
    (fun σ => P₀.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)) *
      P.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)))
    (fun σ => P₀.blockProduct (Renormalization.pairWeight (C σ)) *
      P.blockProduct (Renormalization.pairWeight (C σ)))
  simp only [skCavityPathMeanLM_apply] at hsub
  rw [← hsub]
  exact (abs_skCavityPathMean_le N n β q h 1 (H := fun σ =>
    |(P₀.blockProduct (Renormalization.pairWeight (C σ)) *
        P.blockProduct (Renormalization.pairWeight (C σ))) -
      (P₀.blockProduct (Renormalization.pairWeight fun x y =>
          skCavityRectTrunc N n m q pairMap x y (fun r i => σ r i.castSucc)) *
        P.blockProduct (Renormalization.pairWeight fun x y =>
          skCavityRectTrunc N n m q pairMap x y (fun r i => σ r i.castSucc)))|)
    (fun σ => (abs_sub_comm _ _).le)).trans hb

end SpinGlasses
