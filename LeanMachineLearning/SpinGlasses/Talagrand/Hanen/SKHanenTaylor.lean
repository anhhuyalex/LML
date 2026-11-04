/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIterBound
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPathVanishing
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor bound for spin-difference observables (Talagrand, Corollary 1.11.6, Eq. (1.335))

If `V` has `s` pairs, `|V* ∩ J| ≤ r`, then the first `a - 1` derivatives of `u ↦ ν_u(η_V ε_J f̂ f⁻)`
vanish at `u = 0` (Lemma 1.11.5), where `a = ⌈(s - r)/2⌉`, so Taylor's formula with Lagrange
remainder and Lemma 1.11.3 bound the coupled value `ν_1 = ν`:
`|ν(η_V ε_J f̂ f⁻)| ≤ K (N+1)^{-a/2} ν((f̂ f⁻)²)^{1/2}`.

## Main declarations

* `SpinGlasses.skCavityPathMean_one`: `ν_1` is the `(N+1)`-spin SK average.
* `SpinGlasses.abs_sk_eta_taylor_le`: Corollary 1.11.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- At `u = 1` the cavity path is the coupled `(N+1)`-spin SK system. -/
theorem skCavityPathMean_one (N n : ℕ) (β q h : ℝ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h 1 f =
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  have := integral_sk_cavity_path_zero N n β q h f
  simp only [skCavityPathMean] at this ⊢
  rw [Real.sqrt_one, Real.arccos_one]
  exact this

/-- **Talagrand's Corollary 1.11.6 (Eq. (1.335)).**  Let `s` replica pairs `pairMap w` be pairwise
disjoint, `J` a set of replicas with `|V* ∩ J| ≤ r`, `F` a function of the old spins and `f̂` a
function of the last spins not depending on `V*`.  With `a = ⌈(s - r)/2⌉ = (s - r + 1)/2`
(natural division), the `(N+1)`-spin SK average of `F η_V ε_J f̂` is at most
`K (N+1)^{-a/2} ν((F f̂)²)^{1/2}`, with `K = K(s, n, r, β₀)` chosen before everything else. -/
theorem abs_sk_eta_taylor_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (n s r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (pairMap : Fin s → Fin n × Fin n)
      (_ : ∀ u v : Fin s, u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
      (J : Finset (Fin n))
      (_ : ((Finset.univ : Finset (Fin s)).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card ≤ r)
      (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
      (_ : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
        i ∈ (Finset.univ : Finset (Fin s)).biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
        fhat (Function.update ε i t) = fhat ε),
      |∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          F (fun k i => σ k i.castSucc) *
            (∏ w : Fin s, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
              ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
            (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)) * fhat (fun k => σ k (Fin.last N))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      K / ((N : ℝ) + 1) ^ (((((s - r + 1) / 2 : ℕ) : ℕ) : ℝ) / 2) *
        Real.sqrt (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
            (F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N))) ^ 2
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  obtain ⟨K0, hK0, hK0'⟩ := abs_iteratedDerivWithin_skCavityPathMean_le β₀ hβ₀ ((s - r + 1) / 2) n
  refine ⟨K0 * 2 ^ s + 1, by positivity, ?_⟩
  intro β h q hfix hβ N pairMap hdisj J hcard F fhat hfhat
  have hq := fixedPoint_mem_Icc hfix
  set a : ℕ := (s - r + 1) / 2 with ha
  set G : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ => F (fun k i => σ k i.castSucc) *
    (∏ w : Fin s, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
      ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
    (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)) * fhat (fun k => σ k (Fin.last N)) with hG
  set S : ℝ := ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
      (F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N))) ^ 2
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) with hS
  have hS0 : 0 ≤ S := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  -- the size of the spin-difference product
  have hgsq : ∀ σ, G σ ^ 2 ≤ (4 : ℝ) ^ s *
      (F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N))) ^ 2 := fun σ => by
    have hε : ∀ x : ℤˣ, |((x : ℤˣ) : ℝ)| = 1 := fun x => by
      rcases units_cast_eq_one_or x with hx | hx <;> simp [hx]
    have hd : |∏ w : Fin s, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
        ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))| ≤ 2 ^ s := by
      rw [Finset.abs_prod]
      calc _ ≤ ∏ _w : Fin s, (2 : ℝ) := by
            gcongr with w _
            refine (abs_sub _ _).trans ?_
            rw [hε, hε]; norm_num
        _ = 2 ^ s := by simp
    have hJ : |∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)| = 1 := by
      rw [Finset.abs_prod]; simp [hε]
    have hsq : G σ ^ 2 = (∏ w : Fin s, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
        ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) ^ 2 * (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)) ^ 2 *
        (F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N))) ^ 2 := by
      simp only [hG]; ring
    rw [hsq, ← sq_abs (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)), hJ, ← sq_abs (∏ w : Fin s, _)]
    have h4 : |∏ w : Fin s, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
        ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))| ^ 2 ≤ (4 : ℝ) ^ s := by
      calc _ ≤ ((2 : ℝ) ^ s) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
        _ = _ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    nlinarith [sq_nonneg (F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N)))]
  have hνg : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, G σ ^ 2
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ 4 ^ s * S := by
    calc _ ≤ ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, (4 : ℝ) ^ s *
          (F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N))) ^ 2
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
          integral_integral_sk_replica_mono N n β h hgsq
      _ = 4 ^ s * S := by simp only [integral_const_mul, hS]
  have hsqrt : ∀ x : ℝ, x ≤ 4 ^ s * S → Real.sqrt x ≤ 2 ^ s * Real.sqrt S := fun x hx => by
    refine (Real.sqrt_le_sqrt hx).trans_eq ?_
    rw [Real.sqrt_mul (by positivity), show (4 : ℝ) ^ s = (2 ^ s) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num, Real.sqrt_sq (by positivity)]
  set f₁ : ℝ → ℝ := fun t => skCavityPathMean N n β q h t G with hf₁
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDerivWithin a f₁ (Set.Icc 0 1) u| ≤
      K0 / ((N : ℝ) + 1) ^ ((a : ℝ) / 2) * (2 ^ s * Real.sqrt S) := fun u hu =>
    (hK0' β h q hfix hβ N G u hu).trans
      (mul_le_mul_of_nonneg_left (hsqrt _ hνg) (by positivity))
  have hvan : ∀ k, 2 * k + r < s → iteratedDerivWithin k f₁ (Set.Icc 0 1) 0 = 0 := fun k hk =>
    iteratedDerivWithin_skCavityPathMean_zero_vanishing N k n β q h hq
      (Finset.univ : Finset (Fin s)) pairMap (fun u _ v _ huv => hdisj u v huv) J hcard
      (by simpa using hk) F fhat (fun ε i t hi => hfhat ε i t hi)
  have key : |f₁ 1| ≤ K0 / ((N : ℝ) + 1) ^ ((a : ℝ) / 2) * (2 ^ s * Real.sqrt S) := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · calc |f₁ 1| = |iteratedDerivWithin a f₁ (Set.Icc 0 1) 1| := by
            rw [ha0, iteratedDerivWithin_zero]
        _ ≤ _ := hbound 1 ⟨zero_le_one, le_rfl⟩
    · have ha' : a = (a - 1) + 1 := by omega
      have hc : ∀ k : ℕ, ContDiffOn ℝ k f₁ (Set.Icc 0 1) :=
        contDiffOn_skCavityPathMean N n β q h hq G
      have hdiff : DifferentiableOn ℝ (iteratedDerivWithin (a - 1) f₁ (Set.Icc 0 1))
          (Set.Ioo 0 1) :=
        ((hc a).differentiableOn_iteratedDerivWithin
          (by exact_mod_cast Nat.sub_lt hapos one_pos) uniqueDiffOn_Icc_zero_one).mono
          Set.Ioo_subset_Icc_self
      have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
      have hu2 : Set.uIoo (0 : ℝ) 1 = Set.Ioo 0 1 := Set.uIoo_of_le zero_le_one
      obtain ⟨ξ, hξ, hrem⟩ := taylor_mean_remainder_lagrange (f := f₁) (x := 1) (x₀ := 0)
        (n := a - 1) zero_ne_one (by rw [hu1]; exact hc (a - 1)) (by rw [hu1, hu2]; exact hdiff)
      rw [hu1] at hrem
      rw [hu2] at hξ
      rw [taylor_within_apply, Finset.sum_eq_zero, sub_zero] at hrem
      · rw [hrem, ← ha']
        have hfac : (1 : ℝ) ≤ (Nat.factorial a : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero a)
        have hFpos : (0 : ℝ) < (Nat.factorial a : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos a)
        refine le_trans ?_ (hbound ξ ⟨hξ.1.le, hξ.2.le⟩)
        calc _ = |iteratedDerivWithin a f₁ (Set.Icc 0 1) ξ| / (Nat.factorial a : ℝ) := by
              rw [sub_zero, one_pow, mul_one, abs_div, abs_of_pos hFpos]
          _ ≤ _ := div_le_self (abs_nonneg _) hfac
      · intro k hk
        rw [Finset.mem_range] at hk
        rw [hvan k (by omega), smul_zero]
  rw [← skCavityPathMean_one N n β q h]
  calc _ ≤ _ := key
    _ = (K0 * 2 ^ s) / ((N : ℝ) + 1) ^ ((a : ℝ) / 2) * Real.sqrt S := by ring
    _ ≤ _ := by gcongr; linarith

end SpinGlasses
