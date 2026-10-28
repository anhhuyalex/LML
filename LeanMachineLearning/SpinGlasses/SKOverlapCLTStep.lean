/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCovarianceRows
public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrderMoments
public import LeanMachineLearning.SpinGlasses.SKCavityOverlap
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.ProductExpansion

/-!
# The last-site expansion of products of overlap factors (Talagrand, Eqs. (1.309)-(1.311))

Let `U_0, ..., U_{k'}` be factors, each a finite linear combination of centered overlaps
`R_{ab} - q` of the `(N+1)`-spin system, and write `U_j = U_j⁻ + e_j / (N+1)` where `U_j⁻` uses the
first `N` sites and `e_j` collects the last-site spin products. This file proves the exact
identity of the proof of Proposition 1.10.4: if the leading factor has zero total
coefficient, then
`ν(U_0 ∏_j U_j) = ν(e_0 ∏_j U_j⁻) + (N+1)⁻¹ ∑_u ν(e_0 e_u ∏_{j ≠ u} U_j⁻) + (remainder)`,
where the remainder is the explicit sum over the subsets with at least two last-site
corrections, together with the estimate that it is `O(k + 1)`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Eq. (1.297) for a product over a finite set of factors, squared form.** The version of
`sk_cavity_lincomb_sq_le` where the factors are indexed by a finite subset of an arbitrary
index type, as needed for the sub-products appearing in the last-site expansion. -/
theorem sk_cavity_lincomb_sq_le_finset (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) {κ : Type*}
    (s : Finset κ) (M : ℝ) {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ) (a b : ∀ j, ι j → Fin n),
      (∀ j i, a j i ≠ b j i) → ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ,
      (∀ σ, |W σ| ≤ M) →
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          (W σ * ∏ j ∈ s, ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
            ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
              fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q)) ^ 2
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun s : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (s p.val.1 : ℝ) * (s p.val.2 : ℝ)) +
              h * ∑ v : Fin (N + 1), (s v : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        K / ((N : ℝ) + 1) ^ s.card := by
  let e := s.equivFin
  obtain ⟨K, hK0, hK⟩ := sk_cavity_lincomb_sq_le β₀ hβ₀ s.card M
    (ι := fun i => ι (e.symm i).1) (fun i x => c (e.symm i).1 x)
  refine ⟨K, hK0, fun β h q hfix hb N n a b hab W hW => ?_⟩
  have hprod : ∀ G : κ → ℝ, ∏ j ∈ s, G j = ∏ i : Fin s.card, G (e.symm i).1 := fun G => by
    rw [← Finset.prod_coe_sort s G]
    exact (Equiv.prod_comp e.symm fun x : s => G x.1).symm
  simp only [hprod]
  exact hK β h q hfix hb N n (fun i x => a (e.symm i).1 x) (fun i x => b (e.symm i).1 x)
    (fun i x => hab _ x) W hW

/-- **The exact last-site expansion (Eqs. (1.309)-(1.311)).** Let `ν` be an `n`-replica SK
average, `ξ` an observable of one site, and `U_j = U_j⁻ + e_j / (N+1)` symmetric factors. Then
`ν(((N+1)⁻¹ ∑_s ξ_s) ∏_j U_j)` is the sum of: the term with all `U_j⁻`, the terms with exactly
one correction `e_u / (N+1)`, and the explicit sum over the subsets `t` with at least two
corrections. -/
theorem sk_overlap_step_identity (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (ξ : (Fin n → ℤˣ) → ℝ)
    (Uf Um e : κ → (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (hsplit : ∀ j σ, Uf j σ = Um j σ + (N + 1 : ℝ)⁻¹ * e j σ)
    (hsym : ∀ j (pm : Equiv.Perm (Fin (N + 1))) σ, Uf j (fun r i => σ r (pm i)) = Uf j σ) :
    ν (fun σ => ((N + 1 : ℝ)⁻¹ * ∑ s : Fin (N + 1), ξ (fun r => σ r s)) * ∏ j, Uf j σ) =
      ν (fun σ => ξ (fun r => σ r (Fin.last N)) * ∏ j, Um j σ) +
      (N + 1 : ℝ)⁻¹ * ∑ u, ν (fun σ => ξ (fun r => σ r (Fin.last N)) *
        (e u σ * ∏ j ∈ univ.erase u, Um j σ)) +
      ∑ t ∈ (univ : Finset κ).powerset with 2 ≤ t.card, ((N + 1 : ℝ)⁻¹) ^ t.card *
        ν (fun σ => ξ (fun r => σ r (Fin.last N)) *
          ((∏ i ∈ t, e i σ) * ∏ j ∈ univ \ t, Um j σ)) := by
  obtain ⟨hadd, hsmul, -, -⟩ := sk_replica_avg_calculus N n β h ν hν
  rw [sk_replica_avg_site_mean N n β h ν hν ξ _ (fun pm σ => by simp only [hsym])]
  have hexp : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      ξ (fun r => σ r (Fin.last N)) * ∏ j, Uf j σ =
        (ξ (fun r => σ r (Fin.last N)) * ∏ j, Um j σ +
          ∑ u, (N + 1 : ℝ)⁻¹ * (ξ (fun r => σ r (Fin.last N)) *
            (e u σ * ∏ j ∈ univ.erase u, Um j σ))) +
          ∑ t ∈ (univ : Finset κ).powerset with 2 ≤ t.card, ((N + 1 : ℝ)⁻¹) ^ t.card *
            (ξ (fun r => σ r (Fin.last N)) *
              ((∏ i ∈ t, e i σ) * ∏ j ∈ univ \ t, Um j σ)) := fun σ => by
    simp only [hsplit]
    rw [Finset.prod_add_eq_prod_add_single_add_rest univ (fun j => Um j σ)
      (fun j => (N + 1 : ℝ)⁻¹ * e j σ)]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, mul_add, Finset.mul_sum]
    refine congrArg₂ _ (congrArg₂ _ rfl (Finset.sum_congr rfl fun u _ => ?_))
      (Finset.sum_congr rfl fun t _ => ?_) <;> ring
  simp only [hexp]
  have h1 := sk_replica_avg_finset_sum N n β h ν hν (Finset.univ : Finset κ)
    (fun _ => (N + 1 : ℝ)⁻¹) (fun u σ => ξ (fun r => σ r (Fin.last N)) *
      (e u σ * ∏ j ∈ univ.erase u, Um j σ))
  have h2 := sk_replica_avg_finset_sum N n β h ν hν
    ((Finset.univ : Finset κ).powerset.filter fun t => 2 ≤ t.card)
    (fun t => ((N + 1 : ℝ)⁻¹) ^ t.card) (fun t σ => ξ (fun r => σ r (Fin.last N)) *
      ((∏ i ∈ t, e i σ) * ∏ j ∈ univ \ t, Um j σ))
  beta_reduce at h1 h2
  rw [hadd, hadd, h1, h2, ← Finset.mul_sum]

/-- **Cauchy-Schwarz for an `n`-replica SK average:** `ν(f)² ≤ ν(f²)`. -/
theorem sk_nu_sq_le (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) : ν f ^ 2 ≤ ν (fun σ => f σ ^ 2) := by
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N n β h ν hν
  have h0 := hmono (fun _ => 0) (fun σ => (f σ - ν f) ^ 2) fun σ => sq_nonneg _
  have e : (fun σ => (f σ - ν f) ^ 2) =
      fun σ => (f σ ^ 2 + (-2 * ν f) * f σ) + ν f ^ 2 := by
    funext σ; ring
  rw [hconst, e, hadd, hadd, hsmul, hconst] at h0
  nlinarith [h0]

/-- **The remainder of the last-site expansion is `O(k + 1)` (Eq. (1.310)).** With `k'`
factors `U_j⁻ = ∑_x c_{jx} (R⁻_{a_{jx} b_{jx}} - q)` and last-site parts
`e_j = ∑_x c_{jx} ε_{a_{jx}} ε_{b_{jx}}`, every sum over subsets `t` with at least two
corrections, weighted by `(N+1)^{-|t|}`, is of order `(N+1)^{-(k'+2)/2}`. The constant depends
on the coefficients and the bound of the one-site observable `ξ` only. -/
theorem sk_overlap_step_remainder_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) {κ : Type*} [Fintype κ]
    [DecidableEq κ] {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) (Mξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ) (a b : ∀ j, ι j → Fin n), (∀ j i, a j i ≠ b j i) →
      ∀ (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
        (_ : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
        (Um e : κ → (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ j σ, Um j σ = ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q)) →
      (∀ j σ, e j σ = ∑ i : ι j, c j i *
        ((σ (a j i) (Fin.last N) : ℝ) * (σ (b j i) (Fin.last N) : ℝ))) →
      ∀ ξ : (Fin n → ℤˣ) → ℝ, (∀ x, |ξ x| ≤ Mξ) →
      |∑ t ∈ (Finset.univ : Finset κ).powerset with 2 ≤ t.card, ((N + 1 : ℝ)⁻¹) ^ t.card *
        ν (fun σ => ξ (fun r => σ r (Fin.last N)) *
          ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card κ + 2 : ℕ) : ℝ) / 2) := by
  set Mt : Finset κ → ℝ := fun t => |Mξ| * ∏ i ∈ t, ∑ x : ι i, |c i x| with hMt
  choose K hK0 hK using fun t : Finset κ =>
    sk_cavity_lincomb_sq_le_finset β₀ hβ₀ (Finset.univ \ t) (Mt t) c
  refine ⟨∑ t : Finset κ, Real.sqrt (K t) + 1, by positivity, ?_⟩
  intro β h q hfix hb N n a b hab ν hν Um e hUm he ξ hξ
  have hx : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  set s : ℝ := Real.sqrt ((N : ℝ) + 1) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hx
  have hs2 : s ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hrp : ∀ m : ℕ, ((N : ℝ) + 1) ^ ((m : ℝ) / 2) = s ^ m := fun m => by
    rw [Real.rpow_div_two_eq_sqrt _ (by linarith), Real.rpow_natCast]
  rw [hrp]
  have hterm : ∀ t ∈ ((Finset.univ : Finset κ).powerset.filter fun t => 2 ≤ t.card),
      |((N + 1 : ℝ)⁻¹) ^ t.card * ν (fun σ => ξ (fun r => σ r (Fin.last N)) *
          ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ))| ≤
        Real.sqrt (K t) / s ^ (Fintype.card κ + 2) := by
    intro t ht
    have ht2 : 2 ≤ t.card := (Finset.mem_filter.1 ht).2
    have htk : t.card ≤ Fintype.card κ := by simpa using Finset.card_le_univ t
    set W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      ξ (fun r => σ r (Fin.last N)) * ∏ i ∈ t, e i σ with hW
    have hWb : ∀ σ, |W σ| ≤ Mt t := fun σ => by
      rw [hW, hMt, abs_mul, abs_prod]
      refine mul_le_mul ((hξ _).trans (le_abs_self _)) (Finset.prod_le_prod₀
        (fun _ _ => abs_nonneg _) fun i _ => ?_) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        (abs_nonneg _)
      rw [he]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      rw [abs_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) ((mul_le_mul (abs_units_cast_le_one _)
        (abs_units_cast_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
    set f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      W σ * ∏ j ∈ Finset.univ \ t, Um j σ with hf
    have hfeq : (fun σ => ξ (fun r => σ r (Fin.last N)) *
        ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ)) = f := funext fun σ => by
      simp only [hf, hW, mul_assoc]
    have hν2 : ν (fun σ => f σ ^ 2) ≤ K t / ((N : ℝ) + 1) ^ (Fintype.card κ - t.card) := by
      rw [hν]
      have := hK t β h q hfix hb N n a b hab W hWb
      rw [Finset.card_univ_sdiff] at this
      simpa only [hf, hUm] using this
    have hs3 : Real.sqrt (K t / ((N : ℝ) + 1) ^ (Fintype.card κ - t.card)) =
        Real.sqrt (K t) / s ^ (Fintype.card κ - t.card) := by
      have hpw : ((N : ℝ) + 1) ^ (Fintype.card κ - t.card) =
          (s ^ (Fintype.card κ - t.card)) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul, hs2]
      rw [Real.sqrt_div (hK0 t).le, hpw, Real.sqrt_sq (by positivity)]
    have hnu : |ν f| ≤ Real.sqrt (K t) / s ^ (Fintype.card κ - t.card) := by
      refine (Real.abs_le_sqrt (sk_nu_sq_le N n β h ν hν f)).trans ?_
      rw [← hs3]
      exact Real.sqrt_le_sqrt hν2
    rw [hfeq, abs_mul, abs_pow, abs_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < (N : ℝ) + 1))]
    calc _ ≤ ((N + 1 : ℝ)⁻¹) ^ t.card * (Real.sqrt (K t) / s ^ (Fintype.card κ - t.card)) :=
          mul_le_mul_of_nonneg_left hnu (by positivity)
      _ = Real.sqrt (K t) / s ^ (2 * t.card + (Fintype.card κ - t.card)) := by
          rw [← hs2, inv_pow, ← pow_mul, pow_add]
          field_simp
      _ ≤ Real.sqrt (K t) / s ^ (Fintype.card κ + 2) :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
            (pow_le_pow_right₀ hs1 (by omega))
  calc _ ≤ ∑ t ∈ (Finset.univ : Finset κ).powerset with 2 ≤ t.card, |((N + 1 : ℝ)⁻¹) ^ t.card *
        ν (fun σ => ξ (fun r => σ r (Fin.last N)) *
          ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ (Finset.univ : Finset κ).powerset with 2 ≤ t.card,
        Real.sqrt (K t) / s ^ (Fintype.card κ + 2) := Finset.sum_le_sum hterm
    _ ≤ ∑ t : Finset κ, Real.sqrt (K t) / s ^ (Fintype.card κ + 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun t _ => Finset.mem_univ t)
          (fun t _ _ => by positivity)
    _ = (∑ t : Finset κ, Real.sqrt (K t)) / s ^ (Fintype.card κ + 2) := by
        rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **The last-site expansion of a product of overlap factors (Eqs. (1.309)-(1.311)).**
Let `ξ` be a one-site observable with `|ξ| ≤ Mξ` and `U_j = ∑_x c_{jx} (R_{a_{jx} b_{jx}} - q)`
a finite family of factors. With `U_j⁻`, `e_j` as in `sk_overlap_step_remainder_le`,
`ν(((N+1)⁻¹ ∑_s ξ_s) ∏_j U_j)` equals
`ν(ξ_last ∏_j U_j⁻) + (N+1)⁻¹ ∑_u ν(ξ_last e_u ∏_{j ≠ u} U_j⁻)` up to `O(k' + 2)`. -/
theorem sk_overlap_step_expansion (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) {κ : Type*} [Fintype κ]
    [DecidableEq κ] {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) (Mξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ) (a b : ∀ j, ι j → Fin n), (∀ j i, a j i ≠ b j i) →
      ∀ (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
        (_ : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
        (Uf Um e : κ → (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ j σ, Uf j σ = ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin (N + 1) => (σ (a j i) v : ℝ)) ⬝ᵥ
          fun v : Fin (N + 1) => (σ (b j i) v : ℝ)) - q)) →
      (∀ j σ, Um j σ = ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q)) →
      (∀ j σ, e j σ = ∑ i : ι j, c j i *
        ((σ (a j i) (Fin.last N) : ℝ) * (σ (b j i) (Fin.last N) : ℝ))) →
      ∀ ξ : (Fin n → ℤˣ) → ℝ, (∀ x, |ξ x| ≤ Mξ) →
      |ν (fun σ => ((N + 1 : ℝ)⁻¹ * ∑ s : Fin (N + 1), ξ (fun r => σ r s)) * ∏ j, Uf j σ) -
        (ν (fun σ => ξ (fun r => σ r (Fin.last N)) * ∏ j, Um j σ) +
          (N + 1 : ℝ)⁻¹ * ∑ u, ν (fun σ => ξ (fun r => σ r (Fin.last N)) *
            (e u σ * ∏ j ∈ Finset.univ.erase u, Um j σ)))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card κ + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_overlap_step_remainder_le β₀ hβ₀ c Mξ
  refine ⟨C, hC0, fun β h q hfix hb N n a b hab ν hν Uf Um e hUf hUm he ξ hξ => ?_⟩
  have hsplit : ∀ j σ, Uf j σ = Um j σ + (N + 1 : ℝ)⁻¹ * e j σ := fun j σ => by
    rw [hUf, hUm, he, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := sk_overlap_succ_eq_cavity N (σ (a j i)) (σ (b j i))
    rw [this]
    ring
  have hsym : ∀ j (pm : Equiv.Perm (Fin (N + 1))) σ,
      Uf j (fun r i => σ r (pm i)) = Uf j σ := fun j pm σ => by
    rw [hUf, hUf]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dotProduct]
    rw [Equiv.sum_comp pm (fun v => (σ (a j i) v : ℝ) * (σ (b j i) v : ℝ))]
  have hid := sk_overlap_step_identity N n β h ν hν ξ Uf Um e hsplit hsym
  rw [hid]
  have := hC β h q hfix hb N n a b hab ν hν Um e hUm he ξ hξ
  simpa only [add_sub_cancel_left] using this

end SpinGlasses
