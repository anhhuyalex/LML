/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeTree
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Hilbert-space geometry of finite-depth cascades

The orthonormal family is a hypothesis, not a constructed basis: the results hold in
any real inner product space admitting the indicated family. Vertices are indexed by
`(p : Fin r) × (Fin (p.val + 1) → ℕ)` (the non-root levels).
-/

@[expose] public section

namespace SpinGlasses

open Real Finset

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The point associated to a leaf, as a sum of orthogonal prefix increments. -/
noncomputable def cascadePoint {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (q : Fin (r + 1) → ℝ) (α : Fin r → ℕ) : H :=
  ∑ p : Fin r, (Real.sqrt (q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
    q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩)) •
    e ⟨p, cascadePrefix (Nat.succ_le_of_lt p.isLt) α⟩

/-- The inner product is the sum of the increments at matching prefix vertices. -/
theorem inner_cascadePoint_eq_sum {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (α β : Fin r → ℕ) :
    (inner ℝ (cascadePoint e q α) (cascadePoint e q β)) =
      ∑ p : Fin r, if cascadePrefix (Nat.succ_le_of_lt p.isLt) α =
        cascadePrefix (Nat.succ_le_of_lt p.isLt) β then
        q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
          q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩ else 0 := by
  classical
  unfold cascadePoint
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp_rw [show ∀ (p t : Fin r),
      (inner ℝ (e ⟨p, cascadePrefix (Nat.succ_le_of_lt p.isLt) α⟩)
        (e ⟨t, cascadePrefix (Nat.succ_le_of_lt t.isLt) β⟩)) =
        if (⟨p, cascadePrefix (Nat.succ_le_of_lt p.isLt) α⟩ :
            Σ p : Fin r, Fin (p.val + 1) → ℕ) =
          ⟨t, cascadePrefix (Nat.succ_le_of_lt t.isLt) β⟩ then 1 else 0 from
    fun p t => orthonormal_iff_ite.mp he _ _]
  simp only [mul_ite, mul_one, mul_zero]
  apply sum_congr rfl
  intro p _
  have hle : q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩ ≤
      q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ :=
    hq (Fin.le_iff_val_le_val.mpr (Nat.le_succ p.val))
  simp only [Sigma.mk.injEq]
  have hsum : (∑ t : Fin r,
      if t = p ∧ cascadePrefix (Nat.succ_le_of_lt t.isLt) α ≍
          cascadePrefix (Nat.succ_le_of_lt p.isLt) β then
        Real.sqrt (q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
          q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩) *
          Real.sqrt (q ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩ -
            q ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) else 0) =
      if cascadePrefix (Nat.succ_le_of_lt p.isLt) α =
        cascadePrefix (Nat.succ_le_of_lt p.isLt) β then
        (Real.sqrt (q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
          q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩)) ^ 2 else 0 := by
    classical
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    by_cases h : cascadePrefix (Nat.succ_le_of_lt p.isLt) α =
        cascadePrefix (Nat.succ_le_of_lt p.isLt) β
    · have hf : (Finset.univ.filter fun t : Fin r =>
          t = p ∧ cascadePrefix (Nat.succ_le_of_lt t.isLt) α ≍
            cascadePrefix (Nat.succ_le_of_lt p.isLt) β) = {p} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨And.left, fun ht => by subst t; exact ⟨rfl, heq_of_eq h⟩⟩
      rw [hf]
      simp [h, pow_two]
    · have hf : (Finset.univ.filter fun t : Fin r =>
          t = p ∧ cascadePrefix (Nat.succ_le_of_lt t.isLt) α ≍
            cascadePrefix (Nat.succ_le_of_lt p.isLt) β) = ∅ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ht
          exact False.elim (h (eq_of_heq (ht.1 ▸ ht.2)))
        · simp
      rw [hf]
      simp [h]
  rw [hsum]
  split_ifs
  · exact Real.sq_sqrt (sub_nonneg.mpr hle)
  · rfl

/-- A matching prefix at level `p+1` is equivalent to `p+1` being within the overlap. -/
theorem cascadePrefix_succ_eq_iff {r : ℕ} (p : Fin r) (α β : Fin r → ℕ) :
    (cascadePrefix (Nat.succ_le_of_lt p.isLt) α =
      cascadePrefix (Nat.succ_le_of_lt p.isLt) β) ↔
        p.val + 1 ≤ (prefixOverlap α β).val :=
  cascadePrefix_eq_iff_le_overlap _ α β

/-- The inner product is the overlap parameter, with a simple finite telescoping proof. -/
theorem inner_cascadePoint_eq {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (α β : Fin r → ℕ) :
    inner ℝ (cascadePoint e q α) (cascadePoint e q β) = q (prefixOverlap α β) := by
  rw [inner_cascadePoint_eq_sum e he q hq α β]
  simp_rw [cascadePrefix_succ_eq_iff]
  let k := (prefixOverlap α β).val
  have hk : k ≤ r := Fin.le_last _
  have hsum (p : Fin r) :
      (if p.val + 1 ≤ k then
        q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
          q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩ else 0) =
      if p.val < k then
        q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
          q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩ else 0 := by
    simp only [Nat.succ_le_iff]
  have htel : (∑ p : Fin r, if p.val < k then
      q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
        q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩ else 0) =
      q ⟨k, Nat.lt_succ_of_le hk⟩ - q 0 := by
    let f : ℕ → ℝ := fun j => if h : j ≤ r then
      q ⟨j, Nat.lt_succ_of_le h⟩ else 0
    have hf (j : Fin r) :
        q ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ -
          q ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = f (j.val + 1) - f j.val := by
      simp [f, Nat.succ_le_of_lt j.isLt, j.isLt.le]
    simp_rw [hf]
    have hfilter : (∑ p : Fin r, if p.val < k then f (p.val + 1) - f p.val
        else 0) = ∑ j ∈ Finset.range k, (f (j + 1) - f j) := by
      classical
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      apply Finset.sum_bij (fun j _ => j.val)
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
      · intro _ _ _ _ h
        exact Fin.ext h
      · intro j hj
        refine ⟨⟨j, lt_of_lt_of_le (Finset.mem_range.mp hj) hk⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩
      · intro _ _
        rfl
    rw [hfilter, Finset.sum_range_sub]
    simp [f, hk]
  simpa only [hsum, k, hq0, sub_zero] using htel

/-- Every cascade point lies on the sphere of squared radius `q r`. -/
theorem norm_cascadePoint_sq {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (α : Fin r → ℕ) :
    ‖cascadePoint e q α‖ ^ 2 = q (Fin.last r) := by
  rw [← real_inner_self_eq_norm_sq, inner_cascadePoint_eq e he q hq hq0,
    prefixOverlap_self]
  rfl

/-- Squared distance depends only on the common prefix depth. -/
theorem norm_sub_cascadePoint_sq {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (α β : Fin r → ℕ) :
    ‖cascadePoint e q α - cascadePoint e q β‖ ^ 2 =
      2 * (q (Fin.last r) - q (prefixOverlap α β)) := by
  rw [norm_sub_sq_real, norm_cascadePoint_sq e he q hq hq0,
    norm_cascadePoint_sq e he q hq hq0, inner_cascadePoint_eq e he q hq hq0]
  ring

/-- Ultrametricity of the embedded cascade support (stated on its indexed points). -/
theorem norm_sub_cascadePoint_le_max {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (α β γ : Fin r → ℕ) :
    ‖cascadePoint e q β - cascadePoint e q γ‖ ≤
      max ‖cascadePoint e q α - cascadePoint e q β‖
        ‖cascadePoint e q α - cascadePoint e q γ‖ := by
  have hover := prefixOverlap_min_le β γ α
  have hqmin : min (q (prefixOverlap β α)) (q (prefixOverlap γ α)) ≤
      q (prefixOverlap β γ) := by
    rcases le_total (prefixOverlap β α) (prefixOverlap γ α) with h | h
    · rw [min_eq_left (hq h)]
      exact hq (by rw [min_eq_left h] at hover; exact hover)
    · rw [min_eq_right (hq h)]
      exact hq (by rw [min_eq_right h] at hover; exact hover)
  have hleft : q (prefixOverlap β α) ≤ q (prefixOverlap β γ) ∨
      q (prefixOverlap γ α) ≤ q (prefixOverlap β γ) :=
    (min_le_iff.mp hqmin)
  have hsq : ‖cascadePoint e q β - cascadePoint e q γ‖ ^ 2 ≤
      max (‖cascadePoint e q α - cascadePoint e q β‖ ^ 2)
        (‖cascadePoint e q α - cascadePoint e q γ‖ ^ 2) := by
    rw [norm_sub_cascadePoint_sq e he q hq hq0,
      norm_sub_cascadePoint_sq e he q hq hq0,
      norm_sub_cascadePoint_sq e he q hq hq0]
    rw [prefixOverlap_comm α β, prefixOverlap_comm α γ]
    rcases hleft with hleft | hright
    · exact le_max_of_le_left (by gcongr)
    · exact le_max_of_le_right (by gcongr)
  rcases (le_max_iff.mp hsq) with h | h
  · exact le_max_of_le_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h)
  · exact le_max_of_le_right ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h)

end SpinGlasses
