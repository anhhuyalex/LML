/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityReplicaPairs
public import LeanMachineLearning.SpinGlasses.SKCavityDecoupledMonomials
public import LeanMachineLearning.SpinGlasses.SKCavityCovariance
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag

/-!
# The coefficient count behind Eq. (1.328)

The signed three-family sum of Eq. (1.152) weighs the pairs of replicas `ℓ < ℓ'`, `(ℓ, n+1)` and
`(n+1, n+2)` by `1`, `-n` and `n(n+1)/2`. For a leading pair `{x, y}` the coefficient of a pair is
`b(c)`, where `c` is the number of coincidences with `{x, y}`. This file evaluates three such sums:

* the plain sum is `b(2) - 4 b(1) + 3 b(0)`;
* the sum weighted by the number of replicas of the pair lying outside `{x, y}` is
  `(n - 2) (2 b(1) - 3 b(0))`;
* the sum over the pairs `{r, pt r}` of an involution on the replicas outside `{x, y}` is
  `(n - 2)/2 · b(0)`.

For `b(c) = β² b_unscaled(c)` these are the three coefficients of the end of the proof of
Theorem 1.10.1.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace SpinGlasses

/-- The coincidence count of a pair of replicas with the leading pair `{x, y}` equals the number of
its members in `{x, y}` when `x ≠ y` and the two replicas are distinct. -/
theorem coincidences_eq_ind {n : ℕ} {x y r s : Fin n} (hxy : x ≠ y) (hrs : r ≠ s) :
    skCavityCoincidences (some (some x)) (some (some y)) (some (some r)) (some (some s)) =
      (if r = x ∨ r = y then 1 else 0) + (if s = x ∨ s = y then 1 else 0) := by
  unfold skCavityCoincidences
  simp only [Option.some.injEq, @eq_comm _ x r, @eq_comm _ x s, @eq_comm _ y r, @eq_comm _ y s]
  by_cases h1 : r = x <;> by_cases h2 : s = x <;> by_cases h3 : r = y <;> by_cases h4 : s = y <;>
    simp_all

/-- The coincidence count with an extra replica is the indicator of membership in `{x, y}`. -/
theorem coincidences_extra {n : ℕ} {x y r : Fin n} (hxy : x ≠ y) :
    skCavityCoincidences (some (some x)) (some (some y)) (some (some r)) (some none) =
      if r = x ∨ r = y then 1 else 0 := by
  unfold skCavityCoincidences
  simp only [Option.some.injEq, reduceCtorEq, ite_false, add_zero, @eq_comm _ x r,
    @eq_comm _ y r]
  by_cases h1 : r = x <;> by_cases h3 : r = y <;> simp_all

/-- The two extra replicas have no coincidence with `{x, y}`. -/
theorem coincidences_extra_extra {n : ℕ} (x y : Fin n) :
    skCavityCoincidences (some (some x)) (some (some y)) (some none) none = 0 := by
  simp [skCavityCoincidences]

/-- **The coincidence coefficient is a polynomial in the indicators.** For distinct `r, s` and a
leading pair `x ≠ y`, `b(c(r,s)) = b₀ + (b₁ - b₀)(u_r + u_s) + (b₂ - 2 b₁ + b₀) u_r u_s`
where `u` is the indicator of `{x, y}`. -/
theorem coef_poly {n : ℕ} {x y r s : Fin n} (hxy : x ≠ y) (hrs : r ≠ s) (b : ℕ → ℝ) :
    b (skCavityCoincidences (some (some x)) (some (some y)) (some (some r)) (some (some s))) =
      b 0 + (b 1 - b 0) * ((if r = x ∨ r = y then 1 else 0) + (if s = x ∨ s = y then 1 else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if s = x ∨ s = y then 1 else 0)) := by
  rw [coincidences_eq_ind hxy hrs]
  by_cases h1 : r = x ∨ r = y <;> by_cases h2 : s = x ∨ s = y <;> (simp [h1, h2]; try ring)

/-- The indicator of `{x, y}` sums to `2`. -/
theorem sum_indicator_pair {n : ℕ} {x y : Fin n} (hxy : x ≠ y) :
    ∑ r : Fin n, (if r = x ∨ r = y then (1 : ℝ) else 0) = 2 := by
  have : (Finset.univ.filter fun r : Fin n => r = x ∨ r = y) = {x, y} := by
    ext r
    simp
  rw [Finset.sum_boole, this, Finset.card_pair hxy]
  norm_num

/-- The coincidence count is symmetric in the second pair. -/
theorem coincidences_comm {n : ℕ} (x y a b : Option (Option (Fin n))) :
    skCavityCoincidences x y a b = skCavityCoincidences x y b a := by
  unfold skCavityCoincidences
  ring

/-- **Expansion of the signed three-family sum** (Eq. (1.152)) for a coefficient `b(c)` times a
kernel `G`: the ordered old pairs, the old-extra pairs and the extra-extra pair. -/
theorem signed_sum_expand {n : ℕ} (x y : Fin n) (b : ℕ → ℝ)
    (G : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ) :
    ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
      (b (skCavityReplicaPairCoincidences x y j) *
        G (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2) =
    (∑ p : Fin n × Fin n with p.1 < p.2,
      b (skCavityCoincidences (some (some x)) (some (some y)) (some (some p.1))
        (some (some p.2))) * G (some (some p.1)) (some (some p.2))) -
    (n : ℝ) * ∑ r : Fin n, b (skCavityCoincidences (some (some x)) (some (some y))
        (some (some r)) (some none)) * G (some (some r)) (some none) +
    (n : ℝ) * ((n : ℝ) + 1) / 2 * (b 0 * G (some none) none) := by
  have := sk_cavity_signed_pair_sum (n := n)
    (fun α β : Option (Option (Fin n)) =>
      b (skCavityCoincidences (some (some x)) (some (some y)) α β) * G α β) id
  simp only [id] at this
  rw [coincidences_extra_extra] at this
  unfold skCavityReplicaPairCoincidences
  exact this.symm

/-- **The ordered old pairs as a polynomial double sum.** For a symmetric kernel `G₀`, twice the sum
of `b(c) G₀` over the pairs `r < s` is the off-diagonal double sum of the polynomial form of
`b(c)`. -/
theorem two_sum_lt_poly {n : ℕ} {x y : Fin n} (hxy : x ≠ y) (b : ℕ → ℝ)
    (G₀ : Fin n → Fin n → ℝ) (hG : ∀ r s, G₀ r s = G₀ s r) :
    2 * ∑ p : Fin n × Fin n with p.1 < p.2,
      b (skCavityCoincidences (some (some x)) (some (some y)) (some (some p.1))
        (some (some p.2))) * G₀ p.1 p.2 =
    ∑ r, ∑ s, (b 0 + (b 1 - b 0) * ((if r = x ∨ r = y then 1 else 0) +
        (if s = x ∨ s = y then 1 else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if s = x ∨ s = y then 1 else 0))) * G₀ r s -
    ∑ r, (b 0 + (b 1 - b 0) * (2 * (if r = x ∨ r = y then 1 else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if r = x ∨ r = y then 1 else 0))) * G₀ r r := by
  rw [← sum_sum_offDiag_eq_two_sum_lt (fun r s => b (skCavityCoincidences (some (some x))
    (some (some y)) (some (some r)) (some (some s))) * G₀ r s) (fun r s => by
      simp only [coincidences_comm (some (some x)) (some (some y)) (some (some r)), hG r s])]
  have hdiag : ∀ r s : Fin n, (if r = s then (0 : ℝ) else
      b (skCavityCoincidences (some (some x)) (some (some y)) (some (some r)) (some (some s))) *
        G₀ r s) =
      (b 0 + (b 1 - b 0) * ((if r = x ∨ r = y then 1 else 0) +
        (if s = x ∨ s = y then 1 else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if s = x ∨ s = y then 1 else 0))) * G₀ r s -
      (if r = s then (b 0 + (b 1 - b 0) * ((if r = x ∨ r = y then 1 else 0) +
        (if s = x ∨ s = y then 1 else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if s = x ∨ s = y then 1 else 0))) * G₀ r s else 0) := fun r s => by
    by_cases h : r = s
    · simp [h]
    · simp [h, coef_poly hxy h b]
  simp_rw [hdiag, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring_nf

/-- The indicator of `{x, y}` is idempotent. -/
theorem indicator_mul_self (P : Prop) [Decidable P] :
    (if P then (1 : ℝ) else 0) * (if P then 1 else 0) = if P then 1 else 0 := by
  split_ifs <;> simp

/-- **The plain coefficient (Eq. (1.328), coefficient of `ν(T^k)`).** -/
theorem sk_count_plain {n : ℕ} {x y : Fin n} (hxy : x ≠ y) (b : ℕ → ℝ) :
    ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
      (b (skCavityReplicaPairCoincidences x y j) * 1) = b 2 - 4 * b 1 + 3 * b 0 := by
  have h := signed_sum_expand x y b (fun _ _ => 1)
  rw [h]
  have hX := two_sum_lt_poly hxy b (fun _ _ => 1) (fun _ _ => rfl)
  have hS := sum_indicator_pair hxy
  have hext : ∀ r : Fin n, b (skCavityCoincidences (some (some x)) (some (some y))
      (some (some r)) (some none)) = b 0 + (b 1 - b 0) * (if r = x ∨ r = y then 1 else 0) :=
    fun r => by
    rw [coincidences_extra hxy]
    by_cases hr : r = x ∨ r = y <;> simp [hr]
  simp only [mul_one, hext, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS,
    indicator_mul_self] at hX ⊢
  have hn : (2 : ℝ) ≤ n := by
    have : 2 ≤ n := by
      have := Fintype.card_le_of_injective (![x, y] : Fin 2 → Fin n) (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all)
      simpa using this
    exact_mod_cast this
  nlinarith [hX]

/-- **The coefficient weighted by the number of replicas outside `{x, y}`** (Eq. (1.328), the
coefficient of the single squares `ν(T_x² T^{k-2})`). -/
theorem sk_count_touched {n : ℕ} {x y : Fin n} (hxy : x ≠ y) (b : ℕ → ℝ)
    (tch : Option (Option (Fin n)) → ℝ)
    (htch : ∀ r, tch (some (some r)) = 1 - (if r = x ∨ r = y then 1 else 0))
    (htch1 : tch (some none) = 0) (htch0 : tch none = 0) :
    ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
      (b (skCavityReplicaPairCoincidences x y j) *
        (tch (skCavityReplicaPairMap j).1 + tch (skCavityReplicaPairMap j).2)) =
      ((n : ℝ) - 2) * (2 * b 1 - 3 * b 0) := by
  have h := signed_sum_expand x y b (fun α β => tch α + tch β)
  rw [h]
  have hX := two_sum_lt_poly hxy b (fun r s => tch (some (some r)) + tch (some (some s)))
    (fun r s => add_comm _ _)
  have hS := sum_indicator_pair hxy
  have hext : ∀ r : Fin n, b (skCavityCoincidences (some (some x)) (some (some y))
      (some (some r)) (some none)) = b 0 + (b 1 - b 0) * (if r = x ∨ r = y then 1 else 0) :=
    fun r => by
    rw [coincidences_extra hxy]
    by_cases hr : r = x ∨ r = y <;> simp [hr]
  have hpt : ∀ r s : Fin n, (b 0 + (b 1 - b 0) * ((if r = x ∨ r = y then (1 : ℝ) else 0) +
        (if s = x ∨ s = y then 1 else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if s = x ∨ s = y then 1 else 0))) *
        (tch (some (some r)) + tch (some (some s))) =
      2 * b 0 + (b 1 - 2 * b 0) * ((if r = x ∨ r = y then 1 else 0) +
        (if s = x ∨ s = y then 1 else 0)) - 2 * (b 1 - b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if s = x ∨ s = y then 1 else 0)) := fun r s => by
    rw [htch, htch]
    by_cases h1 : r = x ∨ r = y <;> by_cases h2 : s = x ∨ s = y <;> (simp [h1, h2]; try ring)
  have hdg : ∀ r : Fin n, (b 0 + (b 1 - b 0) * (2 * (if r = x ∨ r = y then (1 : ℝ) else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if r = x ∨ r = y then 1 else 0))) *
        (tch (some (some r)) + tch (some (some r))) =
      2 * b 0 - 2 * b 0 * (if r = x ∨ r = y then 1 else 0) := fun r => by
    rw [htch]
    by_cases h1 : r = x ∨ r = y <;> (simp [h1]; try ring)
  have hex : ∀ r : Fin n, b (skCavityCoincidences (some (some x)) (some (some y))
      (some (some r)) (some none)) * (tch (some (some r)) + tch (some none)) =
      b 0 - b 0 * (if r = x ∨ r = y then 1 else 0) := fun r => by
    rw [hext, htch, htch1]
    by_cases h1 : r = x ∨ r = y <;> simp [h1]
  simp only [hpt, hdg] at hX
  simp only [hex]
  simp only [htch1, htch0, add_zero, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hS] at hX ⊢
  have hn : (2 : ℝ) ≤ n := by
    have : 2 ≤ n := by
      have := Fintype.card_le_of_injective (![x, y] : Fin 2 → Fin n) (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all)
      simpa using this
    exact_mod_cast this
  nlinarith [hX]

/-- **The coefficient of the pairs `{r, pt r}`** (Eq. (1.328), the coefficient of the squared pair
`ν(T_{xy}² T^{k-2})`): an involution `pt` on the replicas outside `{x, y}` pairs them into
`(n - 2)/2` blocks, each with coefficient `b(0)`. -/
theorem sk_count_blocks {n : ℕ} {x y : Fin n} (hxy : x ≠ y) (b : ℕ → ℝ) (pt : Fin n → Fin n)
    (hpt : ∀ r, r ≠ x → r ≠ y → pt r ≠ r ∧ pt r ≠ x ∧ pt r ≠ y ∧ pt (pt r) = r)
    (blk : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ)
    (hblk : ∀ r s, blk (some (some r)) (some (some s)) =
      if r ≠ x ∧ r ≠ y ∧ s = pt r then 1 else 0)
    (hblk1 : ∀ r, blk (some (some r)) (some none) = 0) (hblk0 : blk (some none) none = 0) :
    ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
      (b (skCavityReplicaPairCoincidences x y j) *
        blk (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2) =
      ((n : ℝ) - 2) / 2 * b 0 := by
  have h := signed_sum_expand x y b blk
  rw [h]
  have hiff : ∀ r s : Fin n, (r ≠ x ∧ r ≠ y ∧ s = pt r) → (s ≠ x ∧ s ≠ y ∧ r = pt s) :=
    fun r s ⟨hr1, hr2, hs⟩ => by
    obtain ⟨-, h3, h4, h5⟩ := hpt r hr1 hr2
    exact ⟨hs ▸ h3, hs ▸ h4, by rw [hs, h5]⟩
  have hsymm : ∀ r s : Fin n, blk (some (some r)) (some (some s)) =
      blk (some (some s)) (some (some r)) := fun r s => by
    rw [hblk, hblk]
    by_cases h1 : r ≠ x ∧ r ≠ y ∧ s = pt r
    · rw [ite_eq_left h1, ite_eq_left (hiff r s h1)]
    · by_cases h2 : s ≠ x ∧ s ≠ y ∧ r = pt s
      · exact absurd (hiff s r h2) h1
      · rw [ite_eq_right h1, ite_eq_right h2]
  have hX := two_sum_lt_poly hxy b (fun r s => blk (some (some r)) (some (some s))) hsymm
  have hS := sum_indicator_pair hxy
  have hpt0 : ∀ r s : Fin n, (b 0 + (b 1 - b 0) * ((if r = x ∨ r = y then (1 : ℝ) else 0) +
        (if s = x ∨ s = y then 1 else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if s = x ∨ s = y then 1 else 0))) * blk (some (some r)) (some (some s)) =
      b 0 * (if r ≠ x ∧ r ≠ y ∧ s = pt r then 1 else 0) := fun r s => by
    rw [hblk]
    by_cases h1 : r ≠ x ∧ r ≠ y ∧ s = pt r
    · obtain ⟨hr1, hr2, hs⟩ := h1
      obtain ⟨-, h3, h4, -⟩ := hpt r hr1 hr2
      have e1 : ¬(r = x ∨ r = y) := by tauto
      have e2 : ¬(s = x ∨ s = y) := by rw [hs]; tauto
      have hc : r ≠ x ∧ r ≠ y ∧ s = pt r := ⟨hr1, hr2, hs⟩
      rw [ite_eq_left hc, ite_eq_right e1, ite_eq_right e2]
      ring
    · rw [ite_eq_right h1]
      ring
  have hdg : ∀ r : Fin n, (b 0 + (b 1 - b 0) * (2 * (if r = x ∨ r = y then (1 : ℝ) else 0)) +
        (b 2 - 2 * b 1 + b 0) * ((if r = x ∨ r = y then 1 else 0) *
          (if r = x ∨ r = y then 1 else 0))) * blk (some (some r)) (some (some r)) = 0 :=
    fun r => by
    rw [hblk]
    have : ¬(r ≠ x ∧ r ≠ y ∧ r = pt r) := by
      rintro ⟨h1, h2, h3⟩
      exact (hpt r h1 h2).1 h3.symm
    rw [ite_eq_right this]
    ring
  have hcol : ∀ r : Fin n, ∑ s : Fin n, (if r ≠ x ∧ r ≠ y ∧ s = pt r then (1 : ℝ) else 0) =
      if r ≠ x ∧ r ≠ y then 1 else 0 := fun r => by
    by_cases h1 : r ≠ x ∧ r ≠ y
    · simp [h1.1, h1.2]
    · rw [ite_eq_right h1]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact ite_eq_right fun h => h1 ⟨h.1, h.2.1⟩
  have hrow : ∑ r : Fin n, (if r ≠ x ∧ r ≠ y then (1 : ℝ) else 0) = (n : ℝ) - 2 := by
    have : ∀ r : Fin n, (if r ≠ x ∧ r ≠ y then (1 : ℝ) else 0) =
        1 - (if r = x ∨ r = y then 1 else 0) := fun r => by
      by_cases h1 : r = x ∨ r = y
      · have h2 : ¬(r ≠ x ∧ r ≠ y) := by tauto
        rw [ite_eq_right h2, ite_eq_left h1]
        ring
      · have h2 : r ≠ x ∧ r ≠ y := by tauto
        rw [ite_eq_left h2, ite_eq_right h1]
        ring
    simp only [this, Finset.sum_sub_distrib, hS, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp only [hpt0, hdg, hblk1, hblk0, mul_zero, add_zero, Finset.sum_const_zero, sub_zero,
    ← Finset.mul_sum, hcol, hrow] at hX ⊢
  linarith [hX]

end SpinGlasses
