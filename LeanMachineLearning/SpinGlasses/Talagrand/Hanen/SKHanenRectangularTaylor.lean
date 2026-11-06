/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingBasic
public import
  LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.HigherOrderCavity.SKCavityHigherOrderMoments

/-!
# Taylor isolation for products of rectangular overlaps

The moment bound allows any family of rectangles and any bounded spin observable.
The Taylor argument uses the common arbitrary-observable estimate, rather than a second
copy of the two-site spin-product proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- Square-moment decay for any finite product of truncated rectangles. Repeated rectangles
are allowed; only the two difference labels within each rectangle must be distinct. -/
theorem sk_hanen_rect_prod_sq_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n m : ℕ) (pairMap : Fin (2 * m) → Fin n × Fin n),
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      ∀ (u v : Fin k → Fin (2 * m)), (∀ j, u j ≠ v j) →
      ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, |W σ| ≤ M) →
      skCavityPathMean N n β q h 1 (fun σ =>
        (W σ * ∏ j : Fin k, skCavityRectTrunc N n m q pairMap (u j) (v j)
          (fun r i => σ r i.castSucc)) ^ 2) ≤ C / ((N : ℝ) + 1) ^ k := by
  let c : Fin k → Bool × Bool → ℝ := fun _ e =>
    (if e.1 then -1 else 1) * (if e.2 then -1 else 1)
  obtain ⟨C, hC, hCb⟩ := sk_cavity_lincomb_sq_le β₀ hβ₀ k M c
  refine ⟨C, hC, ?_⟩
  intro β h q hfix hβ N n m pairMap hdisj u v huv W hW
  let a : Fin k → Bool × Bool → Fin n := fun j e =>
    if e.1 then (pairMap (u j)).2 else (pairMap (u j)).1
  let b : Fin k → Bool × Bool → Fin n := fun j e =>
    if e.2 then (pairMap (v j)).2 else (pairMap (v j)).1
  have hab (j : Fin k) (e : Bool × Bool) : a j e ≠ b j e := by
    have hd := hdisj (u j) (v j) (huv j)
    rcases e with ⟨e₁, e₂⟩
    cases e₁ <;> cases e₂ <;> simp only [a, b, Bool.false_eq_true, ite_false, ite_true]
    · exact hd.1
    · exact hd.2.1
    · exact hd.2.2.1
    · exact hd.2.2.2
  have hR (j : Fin k) (σ : Fin n → Fin (N + 1) → ℤˣ) :
      (∑ e : Bool × Bool, c j e * ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (σ (a j e) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (b j e) i.castSucc : ℝ)) - q)) =
      skCavityRectTrunc N n m q pairMap (u j) (v j) (fun r i => σ r i.castSucc) := by
    rw [skCavityRectTrunc_eq_sum_bool N n m q pairMap (u j) (v j)]
  have hb := hCb β h q hfix hβ N n a b hab W hW
  rw [← skCavityPathMean_one N n β q h] at hb
  simpa only [hR] using hb

/-- Square-moment decay for the block product of any pairing, with no preferred ordering
or orientation of its blocks. The replica endpoints within a difference may coincide. -/
theorem sk_hanen_pairing_rect_prod_sq_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (m : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ)
      (P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n),
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, |W σ| ≤ M) →
      skCavityPathMean N n β q h 1 (fun σ => (W σ * P.blockProduct
        (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc))) ^ 2) ≤
        C / ((N : ℝ) + 1) ^ m := by
  obtain ⟨C, hC, hCb⟩ := sk_hanen_rect_prod_sq_le β₀ hβ₀ m M
  refine ⟨C, hC, ?_⟩
  intro β h q hfix hβ N n P pairMap hdisj W hW
  obtain ⟨u, v, huv, hlabels⟩ := Renormalization.exists_labels_prod_pairWeight (m := m) P (by simp)
  have hprod (ρ : Fin n → Fin N → ℤˣ) :
      (∏ j : Fin m, skCavityRectTrunc N n m q pairMap (u j) (v j) ρ) =
        P.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q pairMap u v ρ) :=
    hlabels _ fun a b => skCavityRectTrunc_comm N n m q pairMap a b ρ
  simpa only [hprod] using hCb β h q hfix hβ N n m pairMap hdisj u v huv W hW

/-- **Eq. (1.342).** Isolate the leading Taylor term for the rectangular product of any
pairing. The error is homogeneous in the bound on `fhat`. No positivity of the fixed point,
choice of consecutive blocks or endpoint-derivative estimates are required. -/
theorem sk_hanen_rect_product_taylor (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n),
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      ∀ (fhat : (Fin n → ℤˣ) → ℝ) (M : ℝ), (∀ ε, |fhat ε| ≤ M) →
      (∀ ε i t, i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
        fhat (Function.update ε i t) = fhat ε) →
      let F := fun ρ : Fin n → Fin N → ℤˣ => P.blockProduct
        (Renormalization.pairWeight fun u v => skCavityRectTrunc N n m q pairMap u v ρ)
      let f := fun σ : Fin n → Fin (N + 1) → ℤˣ =>
        (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
          (σ (pairMap w).2 (Fin.last N) : ℝ))) *
        fhat (fun r => σ r (Fin.last N)) * F (fun r i => σ r i.castSucc)
      let φ := fun t => skCavityPathMean N n β q h t f
      |φ 1 - (m.factorial : ℝ)⁻¹ * iteratedDerivWithin m φ (Set.Icc 0 1) 0| ≤
        K * M / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨D, hD, hDb⟩ := skCavityPathMean_taylor_coefficient_le β₀ hβ₀ m m n
  obtain ⟨C, hC, hCb⟩ := sk_hanen_pairing_rect_prod_sq_le β₀ hβ₀ m (2 ^ (2 * m))
  refine ⟨D * Real.sqrt C, mul_pos hD (Real.sqrt_pos.2 hC), ?_⟩
  intro β h q hfix hβ N P pairMap hdisj fhat M hfbound hfhat F f φ
  have hM : 0 ≤ M := (abs_nonneg (fhat fun _ => 1)).trans (hfbound _)
  let W := fun σ : Fin n → Fin (N + 1) → ℤˣ =>
    (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
      (σ (pairMap w).2 (Fin.last N) : ℝ))) * (fhat (fun r => σ r (Fin.last N)) / M)
  have hnorm (ε : Fin n → ℤˣ) : |fhat ε / M| ≤ 1 := by
    by_cases hM0 : M = 0
    · simp [hM0]
    · rw [abs_div, abs_of_nonneg hM]
      exact (div_le_one₀ (lt_of_le_of_ne hM (Ne.symm hM0))).2 (hfbound ε)
  have hW (σ : Fin n → Fin (N + 1) → ℤˣ) : |W σ| ≤ 2 ^ (2 * m) := by
    have hp : |∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
        (σ (pairMap w).2 (Fin.last N) : ℝ))| ≤ 2 ^ (2 * m) := by
      simpa using abs_prod_units_sub_le_two_pow (fun w : Fin (2 * m) => σ (pairMap w).1 (Fin.last N))
        (fun w : Fin (2 * m) => σ (pairMap w).2 (Fin.last N))
    calc
      |W σ| = |∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
          (σ (pairMap w).2 (Fin.last N) : ℝ))| *
          |fhat (fun r => σ r (Fin.last N)) / M| := abs_mul _ _
      _ ≤ 2 ^ (2 * m) * 1 := mul_le_mul hp (hnorm _) (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hf (σ : Fin n → Fin (N + 1) → ℤˣ) :
      f σ = M * (W σ * F (fun r i => σ r i.castSucc)) := by
    by_cases hM0 : M = 0
    · have hzero : ∀ ε, fhat ε = 0 := fun ε => abs_nonpos_iff.mp (hM0 ▸ hfbound ε)
      simp only [f, hzero, mul_zero, zero_mul, hM0]
    · dsimp only [f, W]
      field_simp
  have hmoment : skCavityPathMean N n β q h 1 (fun σ => f σ ^ 2) ≤
      (C * M ^ 2) / ((N : ℝ) + 1) ^ m := by
    have hb := hCb β h q hfix hβ N n P pairMap hdisj W hW
    have he : (fun σ => f σ ^ 2) = fun σ => M ^ 2 *
        (W σ * F (fun r i => σ r i.castSucc)) ^ 2 := by
      funext σ
      rw [hf, mul_pow]
    rw [he, skCavityPathMean_const_mul]
    calc
      _ ≤ M ^ 2 * (C / ((N : ℝ) + 1) ^ m) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg M)
      _ = _ := by ring
  have hzero (j : ℕ) (hj : j < m) : iteratedDerivWithin j φ (Set.Icc 0 1) 0 = 0 := by
    have hb := iteratedDerivWithin_skCavityPathMean_zero_vanishing N j n β q h
      (fixedPoint_mem_Icc hfix) (univ : Finset (Fin (2 * m))) pairMap
      (fun u _ v _ huv => hdisj u v huv) ∅ (by simp) (r := 0)
      (by simp only [card_univ, Fintype.card_fin]; omega) F fhat hfhat
    have he : (fun σ : Fin n → Fin (N + 1) → ℤˣ => F (fun r i => σ r i.castSucc) *
        (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
          (σ (pairMap w).2 (Fin.last N) : ℝ))) * fhat (fun r => σ r (Fin.last N))) = f := by
      funext σ
      dsimp only [f]
      ring
    simpa only [prod_empty, mul_one, he] using hb
  have hb := hDb β h q hfix hβ N f (C * M ^ 2) (by positivity) hmoment hzero
  have hexp : (m : ℝ) + m + 1 = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.sqrt_mul hC.le, Real.sqrt_sq hM, hexp] at hb
  simpa only [mul_assoc] using hb

end SpinGlasses
