/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.InnerProductSpace.UltrametricEmbed
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
    e ⟨p, Fin.take (p.val + 1) p.isLt α⟩

/-- The inner product is the sum of the increments at matching prefix vertices. -/
theorem inner_cascadePoint_eq_sum {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (α β : Fin r → ℕ) :
    (inner ℝ (cascadePoint e q α) (cascadePoint e q β)) =
      ∑ p : Fin r, if Fin.take (p.val + 1) p.isLt α =
        Fin.take (p.val + 1) p.isLt β then
        q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ -
          q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩ else 0 := by
  classical
  unfold cascadePoint
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp_rw [show ∀ (p t : Fin r),
      (inner ℝ (e ⟨p, Fin.take (p.val + 1) p.isLt α⟩)
        (e ⟨t, Fin.take (t.val + 1) t.isLt β⟩)) =
        if (⟨p, Fin.take (p.val + 1) p.isLt α⟩ :
            Σ p : Fin r, Fin (p.val + 1) → ℕ) =
          ⟨t, Fin.take (t.val + 1) t.isLt β⟩ then 1 else 0 from
    fun p t => orthonormal_iff_ite.mp he _ _]
  simp only [mul_ite, mul_one, mul_zero]
  apply sum_congr rfl
  intro p _
  have hle : q ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩ ≤
      q ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ :=
    hq (Fin.le_iff_val_le_val.mpr (Nat.le_succ p.val))
  simp only [Sigma.mk.injEq]
  rw [Finset.sum_eq_single p (fun t _ ht => by simp [ht]) (by simp)]
  by_cases h : Fin.take (p.val + 1) p.isLt α = Fin.take (p.val + 1) p.isLt β
  · simp [h, Real.mul_self_sqrt (sub_nonneg.mpr hle)]
  · simp [h]

/-- The inner product is the overlap parameter, with a simple finite telescoping proof. -/
theorem inner_cascadePoint_eq {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (α β : Fin r → ℕ) :
    inner ℝ (cascadePoint e q α) (cascadePoint e q β) = q (prefixOverlap α β) := by
  rw [inner_cascadePoint_eq_sum e he q hq α β]
  simp_rw [take_eq_take_iff_le_prefixOverlap]
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
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then f (j + 1) - f j else 0) r,
      ← Finset.sum_filter, show (range r).filter (· < k) = range k from by
        ext j; simp only [mem_filter, mem_range]; omega,
      Finset.sum_range_sub]
    simp [f, hk]
  simpa only [hsum, k, hq0, sub_zero] using htel

/-- The scalar-product form of the cascade ultrametric inequality. -/
theorem inner_cascadePoint_min_le {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (α β γ : Fin r → ℕ) :
    min (inner ℝ (cascadePoint e q α) (cascadePoint e q β))
        (inner ℝ (cascadePoint e q α) (cascadePoint e q γ)) ≤
      inner ℝ (cascadePoint e q β) (cascadePoint e q γ) := by
  rw [inner_cascadePoint_eq e he q hq hq0,
    inner_cascadePoint_eq e he q hq hq0,
    inner_cascadePoint_eq e he q hq hq0]
  have h := prefixOverlap_min_le β γ α
  rw [prefixOverlap_comm β α, prefixOverlap_comm γ α] at h
  exact hq.map_min.symm.trans_le (hq h)

/-- Every cascade point lies on the sphere of squared radius `q r`. -/
theorem norm_cascadePoint_sq {r : ℕ}
    (e : (Σ p : Fin r, Fin (p.val + 1) → ℕ) → H)
    (he : Orthonormal ℝ e) (q : Fin (r + 1) → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (α : Fin r → ℕ) :
    ‖cascadePoint e q α‖ ^ 2 = q (Fin.last r) := by
  rw [← real_inner_self_eq_norm_sq, inner_cascadePoint_eq e he q hq hq0,
    prefixOverlap_self]

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
        ‖cascadePoint e q α - cascadePoint e q γ‖ :=
  norm_sub_le_max_of_inner_min_le (cascadePoint e q) _ (norm_cascadePoint_sq e he q hq hq0)
    (inner_cascadePoint_min_le e he q hq hq0) α β γ

end SpinGlasses
