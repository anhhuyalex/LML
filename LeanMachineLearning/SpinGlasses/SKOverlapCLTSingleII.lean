/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTSingleRecurrence
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTLiveMoments
public import Mathlib.Data.Sym.Sym2.Order

/-!
# The evaluation of the term II (Talagrand, Eq. (1.319))

The truncated increment against the truncated product is replaced by the full increment against
the full product (the book's "as usual" step), and the full average is then evaluated by the
live-replica `T`-expansion: unmatched replicas contribute `O(k+1)` and each replica that is the
last fresh replica of a single factor with the label of the leading one contributes
`A²/(N+1)` times the product of the other factors.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Truncated versus full increment against a product.** Adding the increment as one more
factor of `sk_overlap_prod_sub_truncated_le`: the full average of `Inc · ∏ U_b` and the truncated
one differ by `O(k+1)`, uniformly in the temperature range. -/
theorem sk_inc_prod_full_trunc_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {B : Type*} [Fintype B] (c : B → Bool × Bool → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ) (A Bb : B → Bool × Bool → Fin n) (X Y : Bool → Fin n),
      (∀ b i, A b i ≠ Bb b i) → (∀ i₁ i₂, X i₁ ≠ Y i₂) →
      ∀ (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
        (_ : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)),
      |ν (fun σ => (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), (σ (X i.1) v : ℝ) * (σ (Y i.2) v : ℝ) - q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (A b i) v : ℝ) * (σ (Bb b i) v : ℝ) - q)) -
      ν (fun σ => (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (X i.1) v.castSucc : ℝ) * (σ (Y i.2) v.castSucc : ℝ) -
            q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
          (σ (A b i) v.castSucc : ℝ) * (σ (Bb b i) v.castSucc : ℝ) - q))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card B + 2 : ℕ) : ℝ) / 2) := by
  let c' : Option B → Bool × Bool → ℝ := fun j i =>
    Option.elim j ((if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1)) (fun b => c b i)
  obtain ⟨C, hC0, hC⟩ := sk_overlap_prod_sub_truncated_le β₀ hβ₀
    (κ := Option B) (ι := fun _ => Bool × Bool) c' 1
  refine ⟨C, hC0, fun β h q hfix hb N n A Bb X Y hAB hXY ν hν => ?_⟩
  let a' : Option B → Bool × Bool → Fin n := fun j i => Option.elim j (X i.1) (fun b => A b i)
  let b' : Option B → Bool × Bool → Fin n := fun j i => Option.elim j (Y i.2) (fun b => Bb b i)
  have hab' : ∀ j i, a' j i ≠ b' j i := fun j i => by
    cases j with
    | none => exact hXY _ _
    | some b => exact hAB b i
  let Uf : Option B → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j σ => ∑ i, c' j i *
    ((N + 1 : ℝ)⁻¹ * ((fun v : Fin (N + 1) => (σ (a' j i) v : ℝ)) ⬝ᵥ
      fun v : Fin (N + 1) => (σ (b' j i) v : ℝ)) - q)
  let Um : Option B → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j σ => ∑ i, c' j i *
    ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ (a' j i) v.castSucc : ℝ)) ⬝ᵥ
      fun v : Fin N => (σ (b' j i) v.castSucc : ℝ)) - q)
  let e : Option B → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j σ => ∑ i, c' j i *
    ((σ (a' j i) (Fin.last N) : ℝ) * (σ (b' j i) (Fin.last N) : ℝ))
  have hmain := hC β h q hfix hb N n a' b' hab' ν hν Uf Um e (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => 1) (fun _ => by simp)
  obtain ⟨hadd, hsmul, hmono, -⟩ := sk_replica_avg_calculus N n β h ν hν
  let Λ : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ := ⟨⟨ν, hadd⟩, hsmul⟩
  have hfull : (fun σ : Fin n → Fin (N + 1) → ℤˣ => ∏ j, Uf j σ) =
      fun σ => (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), (σ (X i.1) v : ℝ) * (σ (Y i.2) v : ℝ) - q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (A b i) v : ℝ) * (σ (Bb b i) v : ℝ) - q) := funext fun σ => by
    rw [Fintype.prod_option]
    rfl
  have htrunc : (fun σ : Fin n → Fin (N + 1) → ℤˣ => ∏ j, Um j σ) =
      fun σ => (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (X i.1) v.castSucc : ℝ) * (σ (Y i.2) v.castSucc : ℝ) -
            q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
          (σ (A b i) v.castSucc : ℝ) * (σ (Bb b i) v.castSucc : ℝ) - q) := funext fun σ => by
    rw [Fintype.prod_option]
    rfl
  rw [← hfull, ← htrunc]
  change |Λ (fun σ => ∏ j, Uf j σ) - Λ (fun σ => ∏ j, Um j σ)| ≤ _
  rw [← map_sub]
  refine (Λ.abs_apply_le_apply_abs hmono _).trans ?_
  simpa only [one_mul, Pi.sub_apply, Fintype.card_option, Λ, LinearMap.coe_mk,
    AddHom.coe_mk] using hmain

/-- **Summing the per-replica statements of (1.319).** If `Y ℓ` is within `e` of `X ℓ`, `X ℓ` is
within `e` of `0` off the matched set `M` and within `e` of `c * D` on `M`, then the sum of `Y`
over `L ⊇ M` is within `2 |L| e` of `|M| c D`. -/
theorem sum_sub_card_mul_le {ι : Type*} [DecidableEq ι] (L M : Finset ι) (hML : M ⊆ L)
    (Y X : ι → ℝ) (c D e : ℝ) (hYX : ∀ ℓ ∈ L, |Y ℓ - X ℓ| ≤ e)
    (hun : ∀ ℓ ∈ L, ℓ ∉ M → |X ℓ| ≤ e) (hma : ∀ ℓ ∈ M, |X ℓ - c * D| ≤ e) :
    |∑ ℓ ∈ L, Y ℓ - (M.card : ℝ) * (c * D)| ≤ 2 * L.card * e := by
  have h1 : ∑ ℓ ∈ L, Y ℓ - (M.card : ℝ) * (c * D) =
      ∑ ℓ ∈ L, (Y ℓ - X ℓ) + (∑ ℓ ∈ L \ M, X ℓ + ∑ ℓ ∈ M, (X ℓ - c * D)) := by
    have hsplit : ∑ ℓ ∈ L, X ℓ = ∑ ℓ ∈ L \ M, X ℓ + ∑ ℓ ∈ M, X ℓ :=
      (Finset.sum_sdiff hML).symm
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsplit]
    ring
  rw [h1]
  have hcard : ((L \ M).card : ℝ) + (M.card : ℝ) = (L.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hML
  calc _ ≤ |∑ ℓ ∈ L, (Y ℓ - X ℓ)| + (|∑ ℓ ∈ L \ M, X ℓ| + |∑ ℓ ∈ M, (X ℓ - c * D)|) :=
        (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (L.card * e) + (((L \ M).card : ℝ) * e + (M.card : ℝ) * e) := by
        refine add_le_add ?_ (add_le_add ?_ ?_)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans
            ((Finset.sum_le_sum hYX).trans_eq (by simp))
        · exact (Finset.abs_sum_le_sum_abs _ _).trans
            ((Finset.sum_le_sum fun ℓ hℓ => hun ℓ (Finset.mem_sdiff.mp hℓ).1
              (Finset.mem_sdiff.mp hℓ).2).trans_eq (by simp))
        · exact (Finset.abs_sum_le_sum_abs _ _).trans
            ((Finset.sum_le_sum hma).trans_eq (by simp))
    _ = 2 * L.card * e := by
        rw [← add_mul, hcard]
        ring

/-- Unordered pairs given by `(min, max)` are equal iff they agree up to swapping. -/
theorem minmax_pair_eq_iff {α : Type*} [LinearOrder α] {x y x' y' : α} :
    (min x y, max x y) = (min x' y', max x' y') ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  rw [Prod.mk.injEq]
  exact (Sym2.inf_eq_inf_and_sup_eq_sup
    (s := s(x, y)) (t := s(x', y'))).trans Sym2.eq_iff

/-- **Unmatched replicas contribute `O(k+1)` to the term II.** The full increment against the
full product of the other fresh factors, for a replica `ℓ` that is not the last fresh replica of
a single factor with the label of the leading one. -/
theorem sk_single_Xfull_unmatched_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J)
    (a b : J → R) (n : ℕ) (e : Option (R ⊕ (J ⊕ J)) ≃ Fin n) (ℓ : R ⊕ (J ⊕ J))
    (hℓ1 : ℓ ≠ .inl (a p)) (hℓ2 : ℓ ≠ .inr (.inl p))
    (hun : ∀ u, u ≠ p → L u = true → a u = a p → ℓ ≠ .inr (.inr u)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    |∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (if i.1 then some (.inl (a p)) else some (.inr (.inl p)))) v : ℝ) *
            (σ (e (if i.2 then some ℓ else none)) v : ℝ) - q)) *
        ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let base : Finset J := Finset.univ.erase p
  let cc : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  let Aq : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let Bq : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  let Xs : Bool → Option (R ⊕ (J ⊕ J)) := fun t =>
    if t then some (.inl (a p)) else some (.inr (.inl p))
  let Ys : Bool → Option (R ⊕ (J ⊕ J)) := fun t => if t then some ℓ else none
  have hBq : ∀ j i, Bq j i = .inr (.inr j) := fun j i => by simp [Bq, hnp j]
  have hAB : ∀ (j : ↥base) i, e (some (Aq j i)) ≠ e (some (Bq j i)) := fun j i =>
    e.injective.ne (fun h => flagged_pair_ne (a j.1) (b j.1) j.1 (L j.1) (S j.1)
      (fun _ hs => by simp [hnp j.1] at hs) i (Option.some_injective _ h))
  have hXY : ∀ i₁ i₂, e (Xs i₁) ≠ e (Ys i₂) := fun i₁ i₂ => by
    refine e.injective.ne ?_
    cases i₁ <;> cases i₂ <;> simp [Xs, Ys, hℓ1.symm, hℓ2.symm]
  have hrest : ∀ (j j' : ↥base) i i', j ≠ j' → cc j i ≠ 0 → cc j' i' ≠ 0 →
      (min (e (some (Aq j i))) (e (some (Bq j i))), max (e (some (Aq j i))) (e (some (Bq j i)))) ≠
        (min (e (some (Aq j' i'))) (e (some (Bq j' i'))),
          max (e (some (Aq j' i'))) (e (some (Bq j' i')))) := by
    intro j j' i i' hjj' _ _ heq
    rw [minmax_pair_eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := Option.some_injective _ (e.injective h2)
      rw [hBq, hBq] at this
      exact hjj' (Subtype.ext (Sum.inr_injective (Sum.inr_injective this)))
    · have := Option.some_injective _ (e.injective h1)
      rw [hBq] at this
      revert this
      simp only [Aq]
      split_ifs <;> simp
  have hinc : ∀ i₁ i₂ (j : ↥base) i, cc j i ≠ 0 →
      (min (e (Xs i₁)) (e (Ys i₂)), max (e (Xs i₁)) (e (Ys i₂))) ≠
        (min (e (some (Aq j i))) (e (some (Bq j i))),
          max (e (some (Aq j i))) (e (some (Bq j i)))) := by
    intro i₁ i₂ j i _ heq
    rw [minmax_pair_eq_iff] at heq
    have hjp : j.1 ≠ p := Finset.ne_of_mem_erase j.2
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx : Xs i₁ = some (Aq j i) := e.injective h1
      have hy : Ys i₂ = some (Bq j i) := e.injective h2
      rw [hBq] at hy
      cases i₂
      · simp [Ys] at hy
      · have hl : ℓ = .inr (.inr j.1) := by simpa [Ys] using hy
        cases i₁
        · simp only [Xs, Bool.false_eq_true, ite_false] at hx
          have := Option.some_injective _ hx
          by_cases hc : (L j.1 && i.1) = true
          · simp only [Aq, hc, ite_true] at this
            exact Sum.inr_ne_inl this
          · simp only [Aq, hc] at this
            exact hjp (Sum.inl_injective (Sum.inr_injective this)).symm
        · simp only [Xs, ite_true] at hx
          have := Option.some_injective _ hx
          by_cases hc : (L j.1 && i.1) = true
          · simp only [Aq, hc, ite_true] at this
            have hc' : L j.1 = true := by simpa using (Bool.and_eq_true_iff.mp hc).1
            exact hun j.1 hjp hc' (Sum.inl_injective this).symm hl
          · simp only [Aq, hc] at this
            exact Sum.inl_ne_inr this
    · have hx : Xs i₁ = some (Bq j i) := e.injective h1
      rw [hBq] at hx
      cases i₁ <;> simp [Xs] at hx
  obtain ⟨C, hC0, hC⟩ := sk_live_inc_unmatched_uniform β₀ hβ₀ (R := Fin n) (B := ↥base)
    (fun (j : ↥base) i => cc j i) (fun (j : ↥base) i => e (some (Aq j i)))
    (fun (j : ↥base) i => e (some (Bq j i))) (fun i₁ => e (Xs i₁)) (fun i₂ => e (Ys i₂))
    hAB hXY hrest hinc
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro Esk U
  have hU : ∀ (j : J) (σ : Fin n → Fin (N + 1) → ℤˣ),
      U j (fun r => σ (e (some r))) = ∑ i : Bool × Bool, cc j i * ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin (N + 1), (σ (e (some (Aq j i))) v : ℝ) * (σ (e (some (Bq j i))) v : ℝ) - q) :=
    fun j σ => by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin (N + 1) → ℤˣ) (v : Fin (N + 1)) => (s v : ℝ)) (fun r => σ (e (some r)))
      (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hprod : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r))) =
      ∏ j : ↥base, ∑ i : Bool × Bool, cc j i * ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin (N + 1), (σ (e (some (Aq j i))) v : ℝ) * (σ (e (some (Bq j i))) v : ℝ) - q) :=
    fun σ => by
    rw [← Finset.prod_coe_sort base]
    exact Finset.prod_congr rfl fun j _ => hU j σ
  have h1 := hC β h q hfix hb N
  have hcard : Fintype.card ↥base + 2 = Fintype.card J + 1 := by
    have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨p⟩
    simp only [Fintype.card_coe, base, Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
    omega
  rw [hcard] at h1
  simp_rw [hprod]
  exact h1

/-- **A matched replica contributes `A²/(N+1)` times the product of the remaining factors.**
Here `ℓ = inr (inr u)` is the last fresh replica of a single factor `u` with the label of the
leading single factor `p`. The full increment against the full product equals
`α/(1-β²α)/(N+1)` times the product over the factors other than `p` and `u`, up to `O(k+1)`. -/
theorem sk_single_Xfull_matched_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J)
    (a b : J → R) (n : ℕ) (e : Option (R ⊕ (J ⊕ J)) ≃ Fin n) (u : J)
    (hup : u ≠ p) (hLu : L u = true) (hau : a u = a p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (if i.1 then some (.inl (a p)) else some (.inr (.inl p)))) v : ℝ) *
            (σ (e (if i.2 then some (.inr (.inr u)) else none)) v : ℝ) - q)) *
        ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) *
      (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        ∏ j ∈ (Finset.univ.erase p).erase u, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let base : Finset J := Finset.univ.erase p
  let base' : Finset J := base.erase u
  have hubase : u ∈ base := Finset.mem_erase.mpr ⟨hup, Finset.mem_univ u⟩
  let cc : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  let Aq : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let Bq : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  let Xs : Bool → Option (R ⊕ (J ⊕ J)) := fun t =>
    if t then some (.inl (a p)) else some (.inr (.inl p))
  let Ys : Bool → Option (R ⊕ (J ⊕ J)) := fun t => if t then some (.inr (.inr u)) else none
  have hBq : ∀ j i, Bq j i = .inr (.inr j) := fun j i => by simp [Bq, hnp j]
  have hABj : ∀ (j : J) i, e (some (Aq j i)) ≠ e (some (Bq j i)) := fun j i =>
    e.injective.ne (fun h => flagged_pair_ne (a j) (b j) j (L j) (S j)
      (fun _ hs => by simp [hnp j] at hs) i (Option.some_injective _ h))
  have hXY : ∀ i₁ i₂, e (Xs i₁) ≠ e (Ys i₂) := fun i₁ i₂ => by
    refine e.injective.ne ?_
    cases i₁ <;> cases i₂ <;> simp [Xs, Ys]
  have hrestj : ∀ (j j' : J) i i', j ≠ j' →
      (min (e (some (Aq j i))) (e (some (Bq j i))), max (e (some (Aq j i))) (e (some (Bq j i)))) ≠
        (min (e (some (Aq j' i'))) (e (some (Bq j' i'))),
          max (e (some (Aq j' i'))) (e (some (Bq j' i')))) := by
    intro j j' i i' hjj' heq
    rw [minmax_pair_eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := Option.some_injective _ (e.injective h2)
      rw [hBq, hBq] at this
      exact hjj' (Sum.inr_injective (Sum.inr_injective this))
    · have := Option.some_injective _ (e.injective h1)
      rw [hBq] at this
      revert this
      simp only [Aq]
      split_ifs <;> simp
  have hincj : ∀ i₁ i₂ (j : J), j ≠ p → j ≠ u → ∀ i,
      (min (e (Xs i₁)) (e (Ys i₂)), max (e (Xs i₁)) (e (Ys i₂))) ≠
        (min (e (some (Aq j i))) (e (some (Bq j i))),
          max (e (some (Aq j i))) (e (some (Bq j i)))) := by
    intro i₁ i₂ j hjp hju i heq
    rw [minmax_pair_eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hy : Ys i₂ = some (Bq j i) := e.injective h2
      rw [hBq] at hy
      cases i₂
      · simp [Ys] at hy
      · simp only [Ys, ite_true] at hy
        exact hju (Sum.inr_injective (Sum.inr_injective (Option.some_injective _ hy))).symm
    · have hx : Xs i₁ = some (Bq j i) := e.injective h1
      rw [hBq] at hx
      cases i₁ <;> simp [Xs] at hx
  have hcc1 : cc u (true, true) = 1 := by simp [cc, hLu, hnp u]
  have hX : e (Xs true) = e (some (Aq u (true, true))) := by
    simp [Xs, Aq, hLu, hau]
  have hY : e (Ys true) = e (some (Bq u (true, true))) := by
    simp [Ys, hBq]
  have hinc_u : ∀ i₁ i₂ i, (i₁, i₂) ≠ (true, true) → cc u i ≠ 0 →
      (min (e (Xs i₁)) (e (Ys i₂)), max (e (Xs i₁)) (e (Ys i₂))) ≠
        (min (e (some (Aq u i))) (e (some (Bq u i))),
          max (e (some (Aq u i))) (e (some (Bq u i)))) := by
    intro i₁ i₂ i hne _ heq
    rw [minmax_pair_eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx : Xs i₁ = some (Aq u i) := e.injective h1
      have hy : Ys i₂ = some (Bq u i) := e.injective h2
      cases i₂
      · simp [Ys, hBq] at hy
      · cases i₁
        · simp only [Xs, Bool.false_eq_true, ite_false] at hx
          have := Option.some_injective _ hx
          by_cases hc : (L u && i.1) = true
          · simp only [Aq, hc, ite_true] at this
            exact Sum.inr_ne_inl this
          · simp only [Aq, hc] at this
            exact hup (Sum.inl_injective (Sum.inr_injective this)).symm
        · exact hne rfl
    · have hx : Xs i₁ = some (Bq u i) := e.injective h1
      rw [hBq] at hx
      cases i₁ <;> simp [Xs] at hx
  have hT1_u : ∀ i, i ≠ (true, true) → cc u i ≠ 0 →
      (min (e (Xs true)) (e (Ys true)), max (e (Xs true)) (e (Ys true))) ≠
        (min (e (some (Aq u i))) (e (some (Bq u i))),
          max (e (some (Aq u i))) (e (some (Bq u i)))) := by
    intro i hne hci heq
    rw [minmax_pair_eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx : Xs true = some (Aq u i) := e.injective h1
      simp only [Xs, ite_true] at hx
      have := Option.some_injective _ hx
      rcases i with ⟨i1, i2⟩
      by_cases hc : (L u && i1) = true
      · have hi1 : i1 = true := (Bool.and_eq_true_iff.mp hc).2
        subst hi1
        have hi2 : i2 = false := by
          by_contra hi2
          exact hne (by rw [show i2 = true from by simpa using hi2])
        subst hi2
        simp [cc, hnp u] at hci
      · simp only [Aq, hc] at this
        exact Sum.inl_ne_inr this
    · have hx : Xs true = some (Bq u i) := e.injective h1
      rw [hBq] at hx
      simp [Xs] at hx
  obtain ⟨C, hC0, hC⟩ := sk_live_inc_matched_uniform β₀ hβ₀ (R := Fin n) (B := ↥base')
    (fun (j : ↥base') i => cc j i) (fun (j : ↥base') i => e (some (Aq j i)))
    (fun (j : ↥base') i => e (some (Bq j i))) (fun i₁ => e (Xs i₁)) (fun i₂ => e (Ys i₂))
    (cc u) (fun i => e (some (Aq u i))) (fun i => e (some (Bq u i)))
    (fun j i => hABj j i) hXY (fun i => hABj u i) hcc1 hX hY
    (fun j j' i i' hjj' _ _ => hrestj j j' i i' (fun h => hjj' (Subtype.ext h)))
    (fun i₁ i₂ j i _ => hincj i₁ i₂ j (Finset.ne_of_mem_erase (Finset.mem_erase.mp j.2).2)
      (Finset.ne_of_mem_erase j.2) i)
    (fun i j i' _ _ => hrestj u j i i' (Finset.ne_of_mem_erase j.2).symm)
    hinc_u hT1_u
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro Esk U α
  have hU : ∀ (j : J) (σ : Fin n → Fin (N + 1) → ℤˣ),
      U j (fun r => σ (e (some r))) = ∑ i : Bool × Bool, cc j i * ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin (N + 1), (σ (e (some (Aq j i))) v : ℝ) * (σ (e (some (Bq j i))) v : ℝ) - q) :=
    fun j σ => by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin (N + 1) → ℤˣ) (v : Fin (N + 1)) => (s v : ℝ)) (fun r => σ (e (some r)))
      (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hprod' : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      ∏ j ∈ (Finset.univ.erase p).erase u, U j (fun r => σ (e (some r))) =
      ∏ j : ↥base', ∑ i : Bool × Bool, cc j i * ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin (N + 1), (σ (e (some (Aq j i))) v : ℝ) * (σ (e (some (Bq j i))) v : ℝ) - q) :=
    fun σ => by
    rw [← Finset.prod_coe_sort base']
    exact Finset.prod_congr rfl fun j _ => hU j σ
  have hprod : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r))) =
      (∑ i : Bool × Bool, cc u i * ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin (N + 1), (σ (e (some (Aq u i))) v : ℝ) * (σ (e (some (Bq u i))) v : ℝ) - q)) *
      ∏ j ∈ (Finset.univ.erase p).erase u, U j (fun r => σ (e (some r))) := fun σ => by
    rw [← hU u σ, mul_comm]
    exact (Finset.prod_erase_mul base (fun j => U j (fun r => σ (e (some r)))) hubase).symm
  have h1 := hC β h q hfix hb N
  have hcard : Fintype.card ↥base' + 3 = Fintype.card J + 1 := by
    have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨p⟩
    have h2 : Fintype.card ↥base' = Fintype.card J - 2 := by
      simp only [Fintype.card_coe, base', base,
        Finset.card_erase_of_mem hubase, Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ]
      omega
    have h3 : 2 ≤ Fintype.card J := by
      have := Finset.card_le_card (show ({p, u} : Finset J) ⊆ Finset.univ from Finset.subset_univ _)
      rw [Finset.card_pair (Ne.symm hup)] at this
      simpa using this
    omega
  rw [hcard] at h1
  simp_rw [hprod, hprod']
  convert h1 using 3
  refine integral_congr_ae (ae_of_all _ fun g => integral_congr_ae (ae_of_all _ fun σ => ?_))
  exact (mul_assoc _ _ _).symm

/-- **The truncated term II summand is the full one, up to `O(k+1)`.** For a replica `ℓ` other
than the leading label and its fresh partner, the fresh-language increment of the feedback
theorem equals the average over `Fin n` live replicas of the truncated increment against the
truncated product, and differs from the full-site version by `O(k+1)`. -/
theorem sk_single_Y_conv_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J)
    (a b : J → R) (n : ℕ) (e : Option (R ⊕ (J ⊕ J)) ≃ Fin n) (ℓ : R ⊕ (J ⊕ J))
    (hℓ1 : ℓ ≠ .inl (a p)) (hℓ2 : ℓ ≠ .inr (.inl p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let V : J → ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let ν₂ : ((Option (Option (R ⊕ (J ⊕ J))) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (R ⊕ (J ⊕ J))) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let Jf : Option (Option (R ⊕ (J ⊕ J))) → Option (Option (R ⊕ (J ⊕ J))) → ℝ := fun x y =>
      ν₂ (fun σ => (∏ j ∈ Finset.univ.erase p, V j (fun r v => σ (some (some r)) v.castSucc)) *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ x v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ y v.castSucc : ℝ)) - q))
    |(Jf (some (some (.inl (a p)))) (some (some ℓ)) -
        Jf (some (some (.inr (.inl p)))) (some (some ℓ)) -
        (Jf (some (some (.inl (a p)))) (some none) -
          Jf (some (some (.inr (.inl p)))) (some none))) -
      ∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (if i.1 then some (.inl (a p)) else some (.inr (.inl p)))) v : ℝ) *
            (σ (e (if i.2 then some ℓ else none)) v : ℝ) - q)) *
        ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let base : Finset J := Finset.univ.erase p
  let cc : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  let Aq : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let Bq : J → Bool × Bool → R ⊕ (J ⊕ J) := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  let Xs : Bool → Option (R ⊕ (J ⊕ J)) := fun t =>
    if t then some (.inl (a p)) else some (.inr (.inl p))
  let Ys : Bool → Option (R ⊕ (J ⊕ J)) := fun t => if t then some ℓ else none
  have hABj : ∀ (j : ↥base) i, e (some (Aq j i)) ≠ e (some (Bq j i)) := fun j i =>
    e.injective.ne (fun h => flagged_pair_ne (a j.1) (b j.1) j.1 (L j.1) (S j.1)
      (fun _ hs => by simp [hnp j.1] at hs) i (Option.some_injective _ h))
  have hXY : ∀ i₁ i₂, e (Xs i₁) ≠ e (Ys i₂) := fun i₁ i₂ => by
    refine e.injective.ne ?_
    cases i₁ <;> cases i₂ <;> simp [Xs, Ys, hℓ1.symm, hℓ2.symm]
  obtain ⟨C, hC0, hC⟩ := sk_inc_prod_full_trunc_uniform β₀ hβ₀ (B := ↥base)
    (fun (j : ↥base) i => cc j i)
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro Esk U V ν₂ Jf
  let νf : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hJ : ∀ x' y' : Option (R ⊕ (J ⊕ J)), Jf (some x') (some y') =
      νf (fun σ => (∏ j ∈ base, V j (fun r v => σ (e (some r)) v.castSucc)) *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ (e x') v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (e y') v.castSucc : ℝ)) - q)) := fun x' y' => by
    dsimp only [Jf, ν₂, νf]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    rw [integral_pi_option_count_tilted_marginal (R := Option (R ⊕ (J ⊕ J))) (Esk g)
      (fun ρ => (∏ j ∈ base, V j (fun r v => ρ (some r) v.castSucc)) *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ x' v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (ρ y' v.castSucc : ℝ)) - q))]
    exact integral_pi_count_tilted_reindex e (Esk g) _
  obtain ⟨hadd, hsmul, -, -⟩ := sk_replica_avg_calculus N n β h νf (fun Φ => rfl)
  let Λ : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ := ⟨⟨νf, hadd⟩, hsmul⟩
  have hY : (Jf (some (some (.inl (a p)))) (some (some ℓ)) -
        Jf (some (some (.inr (.inl p)))) (some (some ℓ)) -
        (Jf (some (some (.inl (a p)))) (some none) -
          Jf (some (some (.inr (.inl p)))) (some none))) =
      νf (fun σ => (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e (Xs i.1)) v.castSucc : ℝ) *
            (σ (e (Ys i.2)) v.castSucc : ℝ) - q)) *
        ∏ j ∈ base, V j (fun r v => σ (e (some r)) v.castSucc)) := by
    rw [hJ, hJ, hJ, hJ]
    change Λ _ - Λ _ - (Λ _ - Λ _) = Λ _
    rw [← map_sub, ← map_sub, ← map_sub]
    congr 1
    funext σ
    simp only [Pi.sub_apply, Fintype.sum_prod_type, Fintype.sum_bool, Xs, Ys, dotProduct,
      ite_true, Bool.false_eq_true, ite_false]
    ring
  have hU : ∀ (j : J) (σ : Fin n → Fin (N + 1) → ℤˣ),
      U j (fun r => σ (e (some r))) = ∑ i : Bool × Bool, cc j i * ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin (N + 1), (σ (e (some (Aq j i))) v : ℝ) * (σ (e (some (Bq j i))) v : ℝ) - q) :=
    fun j σ => by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin (N + 1) → ℤˣ) (v : Fin (N + 1)) => (s v : ℝ)) (fun r => σ (e (some r)))
      (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hV : ∀ (j : J) (σ : Fin n → Fin (N + 1) → ℤˣ),
      V j (fun r v => σ (e (some r)) v.castSucc) = ∑ i : Bool × Bool, cc j i *
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e (some (Aq j i))) v.castSucc : ℝ) *
          (σ (e (some (Bq j i))) v.castSucc : ℝ) - q) :=
    fun j σ => by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin N → ℤˣ) (v : Fin N) => (s v : ℝ))
      (fun r v => σ (e (some r)) v.castSucc)
      (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hmain := hC β h q hfix hb N n (fun (j : ↥base) i => e (some (Aq j i)))
    (fun (j : ↥base) i => e (some (Bq j i))) (fun i₁ => e (Xs i₁)) (fun i₂ => e (Ys i₂))
    hABj hXY νf (fun Φ => rfl)
  have hcard : Fintype.card ↥base + 2 = Fintype.card J + 1 := by
    have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨p⟩
    simp only [Fintype.card_coe, base, Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
    omega
  rw [hcard] at hmain
  have hfu : (fun σ : Fin n → Fin (N + 1) → ℤˣ =>
      (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e (Xs i.1)) v : ℝ) * (σ (e (Ys i.2)) v : ℝ) - q)) *
      ∏ j ∈ base, U j (fun r => σ (e (some r)))) =
      fun σ => (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (Xs i.1)) v : ℝ) * (σ (e (Ys i.2)) v : ℝ) - q)) *
        ∏ j : ↥base, ∑ i : Bool × Bool, cc j i * ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e (some (Aq j i))) v : ℝ) * (σ (e (some (Bq j i))) v : ℝ) - q) := funext fun σ => by
    rw [← Finset.prod_coe_sort base]
    exact congrArg _ (Finset.prod_congr rfl fun j _ => hU j σ)
  have hft : (fun σ : Fin n → Fin (N + 1) → ℤˣ =>
      (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e (Xs i.1)) v.castSucc : ℝ) *
          (σ (e (Ys i.2)) v.castSucc : ℝ) - q)) *
      ∏ j ∈ base, V j (fun r v => σ (e (some r)) v.castSucc)) =
      fun σ => (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e (Xs i.1)) v.castSucc : ℝ) *
            (σ (e (Ys i.2)) v.castSucc : ℝ) - q)) *
        ∏ j : ↥base, ∑ i : Bool × Bool, cc j i * ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
          (σ (e (some (Aq j i))) v.castSucc : ℝ) *
            (σ (e (some (Bq j i))) v.castSucc : ℝ) - q) := funext fun σ => by
    rw [← Finset.prod_coe_sort base]
    exact congrArg _ (Finset.prod_congr rfl fun j _ => hV j σ)
  have hmain' : |νf (fun σ : Fin n → Fin (N + 1) → ℤˣ =>
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e (Xs i.1)) v.castSucc : ℝ) *
            (σ (e (Ys i.2)) v.castSucc : ℝ) - q)) *
        ∏ j ∈ base, V j (fun r v => σ (e (some r)) v.castSucc)) -
      νf (fun σ : Fin n → Fin (N + 1) → ℤˣ =>
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (Xs i.1)) v : ℝ) * (σ (e (Ys i.2)) v : ℝ) - q)) *
        ∏ j ∈ base, U j (fun r => σ (e (some r))))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
    rw [hfu, hft, abs_sub_comm]
    exact hmain
  rw [hY]
  exact hmain'

/-- **Replica symmetry between two equal fresh factors.** The full products over all factors but
`u` and over all factors but `w` have the same average when `u` and `w` have the same flags and
the same used original labels. -/
theorem sk_fresh_prod_erase_symm (N : ℕ) (β h q : ℝ)
    {R J : Type*} [Fintype R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (a b : J → R) (s : Finset J) {u w : J} (hu : u ∈ s) (hw : w ∈ s)
    (hL : L u = L w) (hS : S u = S w) (ha : L u = true → a u = a w)
    (hb : S u = true → b u = b w) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    (∫ g, ∫ σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ, ∏ j ∈ s.erase u, U j σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, ∫ σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ, ∏ j ∈ s.erase w, U j σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro Esk U
  apply integral_congr_ae (ae_of_all _ fun g => ?_)
  exact MeasureTheory.integral_fresh_overlap_prod_erase_eq (Measure.count.tilted (Esk g))
    (fun (s : Fin (N + 1) → ℤˣ) (v : Fin (N + 1)) => (s v : ℝ)) (N + 1 : ℝ)⁻¹ q a b L S s hu hw
    hL hS ha hb

/-- **Full versus truncated product over a set of fresh factors.** The average of the full
product of fresh kernels differs from that of the truncated product by `O(k+1)`, uniformly in
the temperature range. -/
theorem sk_fresh_prod_full_trunc_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [Fintype J]
    (L S : J → Bool) (a b : J → R) (hab : ∀ j, L j = true → S j = true → a j ≠ b j)
    (s : Finset J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let V : J → ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    |(∫ g, ∫ σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ, ∏ j ∈ s, U j σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      ∫ g, ∫ σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ, ∏ j ∈ s, V j (fun r v => σ r v.castSucc)
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  let Q := R ⊕ (J ⊕ J)
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let c : J → Bool × Bool → ℝ := fun j i =>
    (if L j then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
    (if S j then if i.2 then 1 else -1 else if i.2 then 1 else 0)
  let A : J → Bool × Bool → Q := fun j i =>
    if L j && i.1 then .inl (a j) else .inr (.inl j)
  let B : J → Bool × Bool → Q := fun j i =>
    if S j && i.2 then .inl (b j) else .inr (.inr j)
  obtain ⟨C, hC0, hC⟩ := sk_overlap_prod_sub_truncated_le β₀ hβ₀ (fun (j : s) => c j) 1
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro Esk U V
  let νf : ((Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun H =>
    ∫ g, ∫ σ, H σ
      ∂(Measure.pi fun _ : Fin (Fintype.card Q) => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have havg : ∀ H : (Q → Fin (N + 1) → ℤˣ) → ℝ,
      (∫ g, ∫ σ : Q → Fin (N + 1) → ℤˣ, H σ
        ∂(Measure.pi fun _ : Q => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      νf (fun σ => H (fun r => σ (e r))) := fun H => by
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    exact integral_pi_count_tilted_reindex e (Esk g) H
  obtain ⟨hadd, hsmul, hmono, -⟩ := sk_replica_avg_calculus N (Fintype.card Q) β h νf
    (fun _ => rfl)
  let Λ : ((Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ := ⟨⟨νf, hadd⟩, hsmul⟩
  have hU : ∀ (j : J) (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ),
      U j (fun r => σ (e r)) = ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v => (σ (e (A j i)) v : ℝ)) ⬝ᵥ fun v => (σ (e (B j i)) v : ℝ)) - q) :=
    fun j σ => by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin (N + 1) → ℤˣ) (v : Fin (N + 1)) => (s v : ℝ)) (fun r => σ (e r))
      (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hV : ∀ (j : J) (σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ),
      V j (fun r v => σ (e r) v.castSucc) = ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (e (A j i)) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (e (B j i)) v.castSucc : ℝ)) - q) :=
    fun j σ => by
    symm
    simpa only [dotProduct] using Finset.sum_centered_pairs_eq_fresh_overlap
      (fun (s : Fin N → ℤˣ) (v : Fin N) => (s v : ℝ))
      (fun r v => σ (e r) v.castSucc) (a j) (b j) j (L j) (S j) (N + 1 : ℝ)⁻¹ q
  have hAB : ∀ (j : s) (i : Bool × Bool), e (A j i) ≠ e (B j i) := fun j i =>
    e.injective.ne (flagged_pair_ne (a j.1) (b j.1) j.1 (L j.1) (S j.1) (hab j.1) i)
  have hmain := hC β h q hfix hb N (Fintype.card Q) (fun (j : s) i => e (A j i))
    (fun (j : s) i => e (B j i)) hAB νf (fun _ => rfl)
    (fun (j : s) σ => ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
      ((fun v => (σ (e (A j i)) v : ℝ)) ⬝ᵥ fun v => (σ (e (B j i)) v : ℝ)) - q))
    (fun (j : s) σ => ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
      ((fun v : Fin N => (σ (e (A j i)) v.castSucc : ℝ)) ⬝ᵥ
        fun v : Fin N => (σ (e (B j i)) v.castSucc : ℝ)) - q))
    (fun (j : s) σ => ∑ i : Bool × Bool, c j i * ((σ (e (A j i)) (Fin.last N) : ℝ) *
      (σ (e (B j i)) (Fin.last N) : ℝ)))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => 1) (fun _ => by simp)
  rw [havg, havg]
  change |Λ (fun σ => ∏ j ∈ s, U j (fun r => σ (e r))) -
    Λ (fun σ => ∏ j ∈ s, V j (fun r v => σ (e r) v.castSucc))| ≤ _
  rw [← map_sub]
  refine (Λ.abs_apply_le_apply_abs hmono _).trans ?_
  have hfu : (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ => ∏ j ∈ s, U j (fun r => σ (e r))) =
      fun σ => ∏ j : s, ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v => (σ (e (A j i)) v : ℝ)) ⬝ᵥ fun v => (σ (e (B j i)) v : ℝ)) - q) :=
    funext fun σ => by
    rw [← Finset.prod_coe_sort s]
    exact Finset.prod_congr rfl fun j _ => hU j σ
  have hfv : (fun σ : Fin (Fintype.card Q) → Fin (N + 1) → ℤˣ =>
      ∏ j ∈ s, V j (fun r v => σ (e r) v.castSucc)) =
      fun σ => ∏ j : s, ∑ i : Bool × Bool, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (e (A j i)) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (e (B j i)) v.castSucc : ℝ)) - q) :=
    funext fun σ => by
    rw [← Finset.prod_coe_sort s]
    exact Finset.prod_congr rfl fun j _ => hV j σ
  rw [hfu, hfv]
  simpa only [one_mul, Pi.sub_apply, Fintype.card_coe, Λ, LinearMap.coe_mk, AddHom.coe_mk]
    using hmain
theorem sk_single_Y_conv_all_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J)
    (a b : J → R) (n : ℕ) (e : Option (R ⊕ (J ⊕ J)) ≃ Fin n) :
    ∃ E : ℝ, 0 < E ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let V : J → ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let ν₂ : ((Option (Option (R ⊕ (J ⊕ J))) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (R ⊕ (J ⊕ J))) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let Jf : Option (Option (R ⊕ (J ⊕ J))) → Option (Option (R ⊕ (J ⊕ J))) → ℝ := fun x y =>
      ν₂ (fun σ => (∏ j ∈ Finset.univ.erase p, V j (fun r v => σ (some (some r)) v.castSucc)) *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ x v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ y v.castSucc : ℝ)) - q))
    ∀ ℓ : R ⊕ (J ⊕ J), ℓ ≠ .inl (a p) → ℓ ≠ .inr (.inl p) →
    |(Jf (some (some (.inl (a p)))) (some (some ℓ)) -
        Jf (some (some (.inr (.inl p)))) (some (some ℓ)) -
        (Jf (some (some (.inl (a p)))) (some none) -
          Jf (some (some (.inr (.inl p)))) (some none))) -
      ∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (if i.1 then some (.inl (a p)) else some (.inr (.inl p)))) v : ℝ) *
            (σ (e (if i.2 then some ℓ else none)) v : ℝ) - q)) *
        ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      E / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  choose C hC0 hC using fun ℓ : {ℓ : R ⊕ (J ⊕ J) // ℓ ≠ .inl (a p) ∧ ℓ ≠ .inr (.inl p)} =>
    sk_single_Y_conv_uniform β₀ hβ₀ L S hnp p a b n e ℓ.1 ℓ.2.1 ℓ.2.2
  refine ⟨∑ ℓ, C ℓ + 1, by
    have := Finset.sum_nonneg (fun ℓ (_ : ℓ ∈ (Finset.univ : Finset _)) => (hC0 ℓ).le)
    linarith, fun β h q hfix hb N => ?_⟩
  intro Esk U V ν₂ Jf ℓ h1 h2
  refine le_trans (hC ⟨ℓ, h1, h2⟩ β h q hfix hb N) ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have := Finset.single_le_sum (f := C) (fun ℓ _ => (hC0 ℓ).le) (Finset.mem_univ ⟨ℓ, h1, h2⟩)
  linarith

/-- Unmatched replicas, uniformly over `ℓ`. -/
theorem sk_single_Xfull_unmatched_all_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J)
    (a b : J → R) (n : ℕ) (e : Option (R ⊕ (J ⊕ J)) ≃ Fin n) :
    ∃ E : ℝ, 0 < E ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    ∀ ℓ : R ⊕ (J ⊕ J), ℓ ≠ .inl (a p) → ℓ ≠ .inr (.inl p) →
    (∀ u, u ≠ p → L u = true → a u = a p → ℓ ≠ .inr (.inr u)) →
    |∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (if i.1 then some (.inl (a p)) else some (.inr (.inl p)))) v : ℝ) *
            (σ (e (if i.2 then some ℓ else none)) v : ℝ) - q)) *
        ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      E / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  choose C hC0 hC using fun ℓ : {ℓ : R ⊕ (J ⊕ J) // ℓ ≠ .inl (a p) ∧ ℓ ≠ .inr (.inl p) ∧
      ∀ u, u ≠ p → L u = true → a u = a p → ℓ ≠ .inr (.inr u)} =>
    sk_single_Xfull_unmatched_uniform β₀ hβ₀ L S hnp p a b n e ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2
  refine ⟨∑ ℓ, C ℓ + 1, by
    have := Finset.sum_nonneg (fun ℓ (_ : ℓ ∈ (Finset.univ : Finset _)) => (hC0 ℓ).le)
    linarith, fun β h q hfix hb N => ?_⟩
  intro Esk U ℓ h1 h2 h3
  refine le_trans (hC ⟨ℓ, h1, h2, h3⟩ β h q hfix hb N) ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have := Finset.single_le_sum (f := C) (fun ℓ _ => (hC0 ℓ).le) (Finset.mem_univ ⟨ℓ, h1, h2, h3⟩)
  linarith

/-- Matched replicas, uniformly over `u`. -/
theorem sk_single_Xfull_matched_all_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [DecidableEq R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J)
    (a b : J → R) (n : ℕ) (e : Option (R ⊕ (J ⊕ J)) ≃ Fin n) :
    ∃ E : ℝ, 0 < E ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    ∀ u : J, u ≠ p → L u = true → a u = a p →
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
            (σ (e (if i.1 then some (.inl (a p)) else some (.inr (.inl p)))) v : ℝ) *
            (σ (e (if i.2 then some (.inr (.inr u)) else none)) v : ℝ) - q)) *
        ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) *
      (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        ∏ j ∈ (Finset.univ.erase p).erase u, U j (fun r => σ (e (some r)))
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      E / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  choose C hC0 hC using fun u : {u : J // u ≠ p ∧ L u = true ∧ a u = a p} =>
    sk_single_Xfull_matched_uniform β₀ hβ₀ L S hnp p a b n e u.1 u.2.1 u.2.2.1 u.2.2.2
  refine ⟨∑ u, C u + 1, by
    have := Finset.sum_nonneg (fun u (_ : u ∈ (Finset.univ : Finset _)) => (hC0 u).le)
    linarith, fun β h q hfix hb N => ?_⟩
  intro Esk U α u h1 h2 h3
  refine le_trans (hC ⟨u, h1, h2, h3⟩ β h q hfix hb N) ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have := Finset.single_le_sum (f := C) (fun u _ => (hC0 u).le) (Finset.mem_univ ⟨u, h1, h2, h3⟩)
  linarith

/-- **Assembling the term II.** Pure bookkeeping for the hard step (1.319): per-replica
approximations, the matched value `c D` and the replacement of `D` by `D'` give the value
`|M| c D'` of the sum, with an explicit error. -/
theorem sum_sub_card_mul_le' {ι : Type*} [DecidableEq ι] (L M : Finset ι) (hML : M ⊆ L)
    (Y X : ι → ℝ) (c D D' e δ : ℝ) (hc : 0 ≤ c) (hYX : ∀ ℓ ∈ L, |Y ℓ - X ℓ| ≤ e)
    (hun : ∀ ℓ ∈ L, ℓ ∉ M → |X ℓ| ≤ e) (hma : ∀ ℓ ∈ M, |X ℓ - c * D| ≤ e)
    (hD : |D - D'| ≤ δ) :
    |∑ ℓ ∈ L, Y ℓ - (M.card : ℝ) * (c * D')| ≤ 2 * L.card * e + M.card * (c * δ) := by
  have h1 := sum_sub_card_mul_le L M hML Y X c D e hYX hun hma
  have h2 : |(M.card : ℝ) * (c * D) - (M.card : ℝ) * (c * D')| ≤ M.card * (c * δ) := by
    rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hc) (Nat.cast_nonneg _)
  calc _ = |(∑ ℓ ∈ L, Y ℓ - (M.card : ℝ) * (c * D)) +
        ((M.card : ℝ) * (c * D) - (M.card : ℝ) * (c * D'))| := congrArg abs (by ring)
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The final numerical estimate of the hard step (1.319). -/
theorem final_arith_term_II (l m E C1 c N' Dd κ : ℝ) (hm : 0 ≤ m)
    (hC1 : 0 ≤ C1) (hDd : 0 < Dd) (hκ : 0 < κ) (hN : 0 < N')
    (hDdκ : m ≠ 0 → Dd = N' * κ) (hc : c ≤ 4 / 3 / N') :
    2 * l * (E / Dd) + m * (c * (C1 / κ)) ≤ (2 * l * E + 4 / 3 * m * C1 + 1) / Dd := by
  by_cases hm0 : m = 0
  · subst hm0
    rw [zero_mul, add_zero, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hDd.le
  · have h1 : c * (C1 / κ) ≤ 4 / 3 / N' * (C1 / κ) :=
      mul_le_mul_of_nonneg_right hc (div_nonneg hC1 hκ.le)
    have h2 : m * (c * (C1 / κ)) ≤ 4 / 3 * m * C1 / Dd := by
      calc _ ≤ m * (4 / 3 / N' * (C1 / κ)) := mul_le_mul_of_nonneg_left h1 hm
        _ = _ := by
          rw [hDdκ hm0]
          field_simp
    calc 2 * l * (E / Dd) + _ ≤ 2 * l * (E / Dd) + 4 / 3 * m * C1 / Dd := add_le_add le_rfl h2
      _ ≤ _ := by
        rw [← mul_div_assoc, ← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hDd.le

/-- **The hard step (1.319).** The term II of the single-factor feedback equals
`(|cls| - 1)` times `A²/(N+1)` times the truncated product over the factors other than the
leading one and a reference member `u₀` of its class, up to `O(k+1)`; here
`A² = α/(1-β²α)`. The constant is chosen before the temperature, the field and the site count. -/
theorem sk_cavity_single_II_eval_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R] [Fintype J] [DecidableEq J]
    (L S : J → Bool) (hnp : ∀ j, S j = false) (p : J) (hLp : L p = true)
    (a b : J → R) (u₀ : J)
    (href : ((Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p).Nonempty →
      u₀ ∈ (Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let V : J → ((R ⊕ (J ⊕ J)) → Fin N → ℤˣ) → ℝ := fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
    let ν : (((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let ν₂ : ((Option (Option (R ⊕ (J ⊕ J))) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (R ⊕ (J ⊕ J))) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let Jf : Option (Option (R ⊕ (J ⊕ J))) → Option (Option (R ⊕ (J ⊕ J))) → ℝ := fun x y =>
      ν₂ (fun σ => (∏ j ∈ Finset.univ.erase p, V j (fun r v => σ (some (some r)) v.castSucc)) *
        ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ x v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ y v.castSucc : ℝ)) - q))
    let II : ℝ := ∑ l ∈ Finset.univ.filter (fun l : R ⊕ (J ⊕ J) =>
            l ≠ .inl (a p) ∧ l ≠ .inr (.inl p) ∧ l ≠ .inr (.inr p)),
          (Jf (some (some (.inl (a p)))) (some (some l)) -
            Jf (some (some (.inr (.inl p)))) (some (some l)) -
            (Jf (some (some (.inl (a p)))) (some none) -
              Jf (some (some (.inr (.inl p)))) (some none)))
    let cls : Finset J := Finset.univ.filter fun u =>
      L u = true ∧ S u = false ∧ a u = a p
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |II - ((cls.card - 1 : ℕ) : ℝ) * (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) *
        ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀, V j (fun r v => σ r v.castSucc))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) := by
  let Q := R ⊕ (J ⊕ J)
  let n := Fintype.card (Option Q)
  let e : Option Q ≃ Fin n := Fintype.equivFin (Option Q)
  let Lset : Finset Q := Finset.univ.filter (fun l : Q =>
    l ≠ .inl (a p) ∧ l ≠ .inr (.inl p) ∧ l ≠ .inr (.inr p))
  let cls0 : Finset J := (Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p).erase p
  let M : Finset Q := cls0.image (fun u => (.inr (.inr u) : Q))
  have hmem : ∀ u : J, u ∈ cls0 ↔ u ≠ p ∧ L u = true ∧ a u = a p := fun u => by
    simp only [cls0, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, hnp u,
      and_comm]
  have hMsub : M ⊆ Lset := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    have hup := ((hmem u).mp hu).1
    simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Sum.inr_ne_inl, fun h => Sum.inr_ne_inl (Sum.inr_injective h),
      fun h => hup (Sum.inr_injective (Sum.inr_injective h))⟩
  have hMcard : M.card = cls0.card :=
    Finset.card_image_of_injective _ (fun u v h => Sum.inr_injective (Sum.inr_injective h))
  have hLs : ∀ l ∈ Lset, l ≠ .inl (a p) ∧ l ≠ .inr (.inl p) := fun l hl => by
    simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact ⟨hl.1, hl.2.1⟩
  have hun : ∀ l ∈ Lset \ M, ∀ u, u ≠ p → L u = true → a u = a p → l ≠ .inr (.inr u) := by
    intro l hl u hup hLu hau hlu
    refine (Finset.mem_sdiff.mp hl).2 (Finset.mem_image.mpr ⟨u, (hmem u).mpr ⟨hup, hLu, hau⟩, ?_⟩)
    rw [hlu]
  obtain ⟨Ea, hEa0, hEa⟩ := sk_single_Y_conv_all_uniform β₀ hβ₀ L S hnp p a b n e
  obtain ⟨Eb, hEb0, hEb⟩ := sk_single_Xfull_unmatched_all_uniform β₀ hβ₀ L S hnp p a b n e
  obtain ⟨Ec, hEc0, hEc⟩ := sk_single_Xfull_matched_all_uniform β₀ hβ₀ L S hnp p a b n e
  obtain ⟨C1, hC10, hC1⟩ := sk_fresh_prod_full_trunc_uniform β₀ hβ₀ L S a b
    (fun j _ hs => by simp [hnp j] at hs) ((Finset.univ.erase p).erase u₀)
  have hCpos : 0 < 2 * (Lset.card : ℝ) * (Ea + Eb + Ec) + 4 / 3 * (M.card : ℝ) * C1 + 1 :=
    add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith))
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hC10.le)) one_pos
  refine ⟨_, hCpos, fun β h q hfix hb N => ?_⟩
  intro Esk V ν ν₂ Jf II cls α
  let U : J → ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ := fun j ρ =>
    ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
      (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
        else (ρ (.inr (.inl j)) v : ℝ)) *
      (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
        else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q)
  let νf : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hνQ : ∀ G : ((R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ) → ℝ,
      νf (fun σ => G (fun r => σ (e (some r)))) =
      ∫ g, ∫ σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ, G σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := fun G => by
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    rw [← integral_pi_count_tilted_reindex e (Esk g) (fun ρ => G (fun r => ρ (some r)))]
    exact integral_pi_option_count_tilted_marginal (R := R ⊕ (J ⊕ J)) (Esk g) G
  let Dd : ℝ := ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2)
  have hDd : 0 < Dd := by positivity
  have hα01 := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hα : 0 ≤ α ∧ α ≤ 1 := hα01
  have hden : 3 / 4 ≤ 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
    linarith only [h2, hb, hβ₀]
  have hDpos : 0 < 1 - β ^ 2 * α := by linarith only [hden]
  have hc2 : 0 ≤ α / (1 - β ^ 2 * α) / (N + 1 : ℝ) ∧
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) ≤ 4 / 3 / (N + 1 : ℝ) := by
    refine ⟨div_nonneg (div_nonneg hα.1 hDpos.le) (by positivity),
      div_le_div_of_nonneg_right ?_ (by positivity)⟩
    rw [div_le_iff₀ hDpos]
    nlinarith only [hden, hα.2]
  let Yf : Q → ℝ := fun l =>
    (Jf (some (some (.inl (a p)))) (some (some l)) -
      Jf (some (some (.inr (.inl p)))) (some (some l)) -
      (Jf (some (some (.inl (a p)))) (some none) - Jf (some (some (.inr (.inl p)))) (some none)))
  let Xf : Q → ℝ := fun l => νf (fun σ =>
    (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (σ (e (if i.1 then some (.inl (a p)) else some (.inr (.inl p)))) v : ℝ) *
        (σ (e (if i.2 then some l else none)) v : ℝ) - q)) *
    ∏ j ∈ Finset.univ.erase p, U j (fun r => σ (e (some r))))
  have hYX : ∀ l ∈ Lset, |Yf l - Xf l| ≤ Ea / Dd := fun l hl =>
    hEa β h q hfix hb N l (hLs l hl).1 (hLs l hl).2
  have hunX : ∀ l ∈ Lset, l ∉ M → |Xf l| ≤ Eb / Dd := fun l hl hlM =>
    hEb β h q hfix hb N l (hLs l hl).1 (hLs l hl).2
      (hun l (Finset.mem_sdiff.mpr ⟨hl, hlM⟩))
  let Dfull : ℝ := νf (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀,
    U j (fun r => σ (e (some r))))
  have hmaX : ∀ l ∈ M, |Xf l - α / (1 - β ^ 2 * α) / (N + 1 : ℝ) * Dfull| ≤ Ec / Dd := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hup, hLu, hau⟩ := (hmem u).mp hu
    have hu₀ : u₀ ∈ cls0 := href ⟨u, hu⟩
    obtain ⟨hu₀p, hLu₀, hau₀⟩ := (hmem u₀).mp hu₀
    have hsym := sk_fresh_prod_erase_symm N β h q L S a b (Finset.univ.erase p)
      (u := u) (w := u₀) (Finset.mem_erase.mpr ⟨hup, Finset.mem_univ u⟩)
      (Finset.mem_erase.mpr ⟨hu₀p, Finset.mem_univ u₀⟩) (by rw [hLu, hLu₀])
      (by rw [hnp u, hnp u₀]) (fun _ => by rw [hau, hau₀]) (fun hs => by simp [hnp u] at hs)
    have hD : νf (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u, U j (fun r => σ (e (some r)))) =
        Dfull := by
      rw [hνQ (fun ρ => ∏ j ∈ (Finset.univ.erase p).erase u, U j ρ)]
      exact hsym.trans (hνQ (fun ρ => ∏ j ∈ (Finset.univ.erase p).erase u₀, U j ρ)).symm
    have := hEc β h q hfix hb N u hup hLu hau
    rw [← hD]
    exact this
  have hDD : |Dfull - ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀,
        V j (fun r v => σ r v.castSucc))| ≤
      C1 / ((N : ℝ) + 1) ^
        ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2) := by
    have e1 : Dfull = ∫ g, ∫ σ : (R ⊕ (J ⊕ J)) → Fin (N + 1) → ℤˣ,
        ∏ j ∈ (Finset.univ.erase p).erase u₀, U j σ
        ∂(Measure.pi fun _ : R ⊕ (J ⊕ J) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
      hνQ (fun ρ => ∏ j ∈ (Finset.univ.erase p).erase u₀, U j ρ)
    rw [e1]
    exact hC1 β h q hfix hb N
  have hpcls : p ∈ (Finset.univ.filter fun u => L u = true ∧ S u = false ∧ a u = a p) := by
    simp [hLp, hnp p]
  have hclscard : ((cls.card - 1 : ℕ) : ℝ) = (M.card : ℝ) := by
    rw [hMcard]
    have : cls0.card = cls.card - 1 := Finset.card_erase_of_mem hpcls
    rw [this]
  have hsum := sum_sub_card_mul_le' Lset M hMsub Yf Xf (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) Dfull
    (ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀, V j (fun r v => σ r v.castSucc)))
    ((Ea + Eb + Ec) / Dd)
    (C1 / ((N : ℝ) + 1) ^ ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2))
    hc2.1
    (fun l hl => (hYX l hl).trans (div_le_div_of_nonneg_right (by linarith) hDd.le))
    (fun l hl hlM => (hunX l hl hlM).trans (div_le_div_of_nonneg_right (by linarith) hDd.le))
    (fun l hl => (hmaX l hl).trans (div_le_div_of_nonneg_right (by linarith) hDd.le)) hDD
  rw [hclscard]
  have hII : II = ∑ l ∈ Lset, Yf l := rfl
  rw [hII]
  have hDdκ : (M.card : ℝ) ≠ 0 → Dd = ((N : ℝ) + 1) * ((N : ℝ) + 1) ^
      ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2) := by
    intro hM0
    have hpos : 0 < M.card := Nat.pos_of_ne_zero (fun h0 => hM0 (by rw [h0, Nat.cast_zero]))
    have hne : cls0.Nonempty := Finset.card_pos.mp (by rw [← hMcard]; exact hpos)
    have hu₀ := href hne
    have hu₀p : u₀ ≠ p := ((hmem u₀).mp hu₀).1
    have hcardd : (((Finset.univ : Finset J).erase p).erase u₀).card + 3 = Fintype.card J + 1 := by
      have hmem0 : u₀ ∈ (Finset.univ : Finset J).erase p :=
        Finset.mem_erase.mpr ⟨hu₀p, Finset.mem_univ u₀⟩
      rw [Finset.card_erase_of_mem hmem0, Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ]
      have h2 : 2 ≤ Fintype.card J := by
        have := Finset.card_le_card (show ({p, u₀} : Finset J) ⊆ Finset.univ from
          Finset.subset_univ _)
        rw [Finset.card_pair (Ne.symm hu₀p)] at this
        simpa using this
      omega
    have hexp : ((Fintype.card J + 1 : ℕ) : ℝ) / 2 =
        1 + ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2) := by
      rw [← hcardd]; push_cast; ring
    show ((N : ℝ) + 1) ^ (((Fintype.card J + 1 : ℕ) : ℝ) / 2) = _
    rw [hexp, Real.rpow_add (by positivity), Real.rpow_one]
  have hrhs := final_arith_term_II (Lset.card : ℝ) (M.card : ℝ) (Ea + Eb + Ec) C1
    (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) ((N : ℝ) + 1) Dd
    (((N : ℝ) + 1) ^ ((((((Finset.univ : Finset J).erase p).erase u₀).card + 1 : ℕ) : ℝ) / 2))
    (Nat.cast_nonneg _) hC10.le hDd (by positivity) (by positivity) hDdκ hc2.2
  calc |∑ l ∈ Lset, Yf l - (M.card : ℝ) * (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) *
        ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀, V j (fun r v => σ r v.castSucc))|
      = |∑ l ∈ Lset, Yf l - (M.card : ℝ) * (α / (1 - β ^ 2 * α) / (N + 1 : ℝ) *
        ν (fun σ => ∏ j ∈ (Finset.univ.erase p).erase u₀, V j (fun r v => σ r v.castSucc)))| :=
        congrArg abs (by ring)
    _ ≤ _ := hsum.trans hrhs

end SpinGlasses
