/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichlet
public import Mathlib.Data.Nat.Find

/-!
# Prefix trees and deterministic cascade branch weights

Leaves at depth `r` are functions `Fin r → ℕ`. A vertex of depth `p` is a function
`Fin p → ℕ`. No ordering of Poisson atoms is needed for the deterministic results.
-/

@[expose] public section

namespace SpinGlasses

open ENNReal

/-- Restrict a leaf to its first `p` coordinates. -/
def cascadePrefix {r p : ℕ} (hp : p ≤ r) (α : Fin r → ℕ) : Fin p → ℕ :=
  fun i => α (Fin.castLE hp i)

@[simp] theorem cascadePrefix_self {r : ℕ} (α : Fin r → ℕ) :
    cascadePrefix (le_refl r) α = α := by
  funext i
  rfl

/-- The longest common prefix, with values from `0` through `r`. -/
def prefixOverlap {r : ℕ} (α β : Fin r → ℕ) : Fin (r + 1) :=
  ⟨Nat.findGreatest (fun p => ∀ i : Fin r, i.val < p → α i = β i) r,
    Nat.lt_succ_of_le (Nat.findGreatest_le r)⟩

/-- All coordinates before the overlap agree. -/
theorem prefixOverlap_agree {r : ℕ} (α β : Fin r → ℕ) (i : Fin r)
    (hi : i.val < (prefixOverlap α β).val) : α i = β i := by
  exact Nat.findGreatest_spec (P := fun p => ∀ j : Fin r,
    j.val < p → α j = β j) (Nat.zero_le r) (by simp) i hi

/-- An agreeing prefix is no longer than the maximal agreeing prefix. -/
theorem le_prefixOverlap {r : ℕ} (α β : Fin r → ℕ) (p : ℕ) (hp : p ≤ r)
    (h : ∀ i : Fin r, i.val < p → α i = β i) : p ≤ (prefixOverlap α β).val := by
  exact Nat.le_findGreatest hp h

@[simp] theorem prefixOverlap_self {r : ℕ} (α : Fin r → ℕ) :
    prefixOverlap α α = ⟨r, Nat.lt_succ_self r⟩ := by
  apply Fin.ext
  exact Nat.le_antisymm (Nat.findGreatest_le r)
    (le_prefixOverlap α α r le_rfl (by simp))

theorem prefixOverlap_comm {r : ℕ} (α β : Fin r → ℕ) :
    prefixOverlap α β = prefixOverlap β α := by
  apply Fin.ext
  apply Nat.le_antisymm
  · exact le_prefixOverlap β α _ (Fin.le_last _) (fun i hi =>
      (prefixOverlap_agree α β i hi).symm)
  · exact le_prefixOverlap α β _ (Fin.le_last _) (fun i hi =>
      (prefixOverlap_agree β α i hi).symm)

/-- Common-prefix depth obeys the reverse ultrametric triangle inequality. -/
theorem prefixOverlap_min_le {r : ℕ} (α β γ : Fin r → ℕ) :
    min (prefixOverlap α γ) (prefixOverlap β γ) ≤ prefixOverlap α β := by
  apply Fin.le_iff_val_le_val.mpr
  apply le_prefixOverlap α β _ (le_trans (Nat.min_le_left _ _) (Fin.le_last _))
  intro i hi
  exact (prefixOverlap_agree α γ i (lt_of_lt_of_le hi (Nat.min_le_left _ _))).trans
    (prefixOverlap_agree β γ i (lt_of_lt_of_le hi (Nat.min_le_right _ _))).symm

/-- A prefix agrees precisely when its length does not exceed the overlap. -/
theorem cascadePrefix_eq_iff_le_overlap {r p : ℕ} (hp : p ≤ r)
    (α β : Fin r → ℕ) :
    cascadePrefix hp α = cascadePrefix hp β ↔ p ≤ (prefixOverlap α β).val := by
  constructor
  · intro h
    apply le_prefixOverlap α β p hp
    intro i hi
    exact congrFun h ⟨i.val, hi⟩
  · intro h
    funext i
    exact prefixOverlap_agree α β _ (lt_of_lt_of_le i.isLt h)

/-- Vertices sharing a prefix at level `p` also share all preceding prefixes. -/
theorem cascadePrefix_eq_of_le {r p k : ℕ} (hp : p ≤ r) (hk : k ≤ p)
    (α β : Fin r → ℕ) (h : cascadePrefix hp α = cascadePrefix hp β) :
    cascadePrefix (hk.trans hp) α = cascadePrefix (hk.trans hp) β := by
  apply (cascadePrefix_eq_iff_le_overlap (hk.trans hp) α β).2
  exact hk.trans ((cascadePrefix_eq_iff_le_overlap hp α β).1 h)

/-- Branch products with one multiplier for each parent and child label. -/
noncomputable def cascadeBranchWeight (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    {r : ℕ} (α : Fin r → ℕ) : ENNReal :=
  Finset.univ.prod (fun i : Fin r =>
    u i.val (cascadePrefix (Nat.le_of_lt i.isLt) α) (α i))

@[simp] theorem cascadeBranchWeight_zero
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (α : Fin 0 → ℕ) :
    cascadeBranchWeight u α = 1 := by
  simp [cascadeBranchWeight]

/-- Appending a child multiplies its parent's weight by the corresponding branch mass. -/
theorem cascadeBranchWeight_snoc
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    {r : ℕ} (α : Fin r → ℕ) (n : ℕ) :
    cascadeBranchWeight u (Fin.snoc α n) = cascadeBranchWeight u α * u r α n := by
  simp only [cascadeBranchWeight, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    congr 1
    · funext j
      have hj : j.val < r := lt_of_lt_of_le j.isLt i.isLt.le
      simp [cascadePrefix, Fin.snoc, Fin.castLE, hj]
    · simp
  · congr 1
    · funext j
      simp [cascadePrefix, Fin.snoc, Fin.castLE]
    · simp

/-- Strictly positive, finite branch masses give strictly positive, finite leaf weights. -/
theorem cascadeBranchWeight_pos_finite
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu_pos : ∀ p α n, u p α n ≠ 0)
    (hu_fin : ∀ p α n, u p α n ≠ ∞)
    {r : ℕ} (α : Fin r → ℕ) :
    cascadeBranchWeight u α ≠ 0 ∧ cascadeBranchWeight u α ≠ ∞ := by
  unfold cascadeBranchWeight
  constructor
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact hu_pos _ _ _
  · exact ENNReal.prod_ne_top (fun i _ => hu_fin _ _ _)

/-- The total mass of all leaves at a fixed depth, including the depth-zero root. -/
noncomputable def cascadeTotalMass (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (r : ℕ) : ENNReal :=
  ∑' α : Fin r → ℕ, cascadeBranchWeight u α

/-- The depth-zero cascade has unit total mass. -/
@[simp] theorem cascadeTotalMass_zero
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) :
    cascadeTotalMass u 0 = 1 := by
  simp [cascadeTotalMass, cascadeBranchWeight_zero]

/-- The last-level total mass is the parent-weighted sum of its children's masses. -/
theorem cascadeTotalMass_succ
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ) :
    cascadeTotalMass u (r + 1) =
      ∑' α : Fin r → ℕ, cascadeBranchWeight u α * (∑' n, u r α n) := by
  classical
  simp only [cascadeTotalMass]
  rw [← (Fin.snocEquiv (fun _ : Fin (r + 1) => ℕ)).tsum_eq]
  change (∑' c : ℕ × (Fin r → ℕ),
    cascadeBranchWeight u (Fin.snoc c.2 c.1)) = _
  simp_rw [cascadeBranchWeight_snoc]
  rw [ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  congr 1
  funext α
  simpa only [Prod.fst, Prod.snd] using
    (ENNReal.tsum_mul_left (f := fun n => u r α n)
      (a := cascadeBranchWeight u α))

/-- Algebraic normalization, independent of the probabilistic finiteness argument. -/
noncomputable def cascadeProbabilityWeight
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (r : ℕ) (α : Fin r → ℕ) : ENNReal :=
  cascadeBranchWeight u α / cascadeTotalMass u r

/-- Finite, nonzero total mass gives a probability vector on the leaves. -/
theorem tsum_cascadeProbabilityWeight
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ)
    (hfinite : cascadeTotalMass u r ≠ ∞)
    (hpos : cascadeTotalMass u r ≠ 0) :
    (∑' α : Fin r → ℕ, cascadeProbabilityWeight u r α) = 1 := by
  simp only [cascadeProbabilityWeight, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]
  change cascadeTotalMass u r * (cascadeTotalMass u r)⁻¹ = 1
  exact ENNReal.mul_inv_cancel hpos hfinite

/-- If every branch mass is positive and finite, finite total mass makes every
normalized leaf weight positive and finite. -/
theorem cascadeProbabilityWeight_pos_finite
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu_pos : ∀ p α n, u p α n ≠ 0)
    (hu_fin : ∀ p α n, u p α n ≠ ∞)
    (r : ℕ) (hfinite : cascadeTotalMass u r ≠ ∞) (α : Fin r → ℕ) :
    cascadeProbabilityWeight u r α ≠ 0 ∧
      cascadeProbabilityWeight u r α ≠ ∞ := by
  have hw := cascadeBranchWeight_pos_finite u hu_pos hu_fin α
  have hmass : cascadeTotalMass u r ≠ 0 := by
    intro hzero
    have hle : cascadeBranchWeight u α ≤ cascadeTotalMass u r :=
      ENNReal.le_tsum (f := cascadeBranchWeight u) α
    exact hw.1 (nonpos_iff_eq_zero.mp (hzero ▸ hle))
  unfold cascadeProbabilityWeight
  constructor
  · exact ENNReal.div_ne_zero.mpr ⟨hw.1, hfinite⟩
  · exact ENNReal.div_ne_top hw.2 hmass

/-- Positive finite branch masses and finite total mass give a probability vector
with strictly positive entries. -/
theorem cascadeProbabilityWeight_probability
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu_pos : ∀ p α n, u p α n ≠ 0)
    (hu_fin : ∀ p α n, u p α n ≠ ∞)
    (r : ℕ) (hfinite : cascadeTotalMass u r ≠ ∞) :
    (∑' α : Fin r → ℕ, cascadeProbabilityWeight u r α) = 1 ∧
      ∀ α : Fin r → ℕ, cascadeProbabilityWeight u r α ≠ 0 := by
  have hmass : cascadeTotalMass u r ≠ 0 := by
    intro hzero
    have hw := (cascadeBranchWeight_pos_finite u hu_pos hu_fin
      (fun _ : Fin r => 0)).1
    exact hw (nonpos_iff_eq_zero.mp
      (hzero ▸ ENNReal.le_tsum (f := cascadeBranchWeight u) (fun _ : Fin r => 0)))
  exact ⟨tsum_cascadeProbabilityWeight u r hfinite hmass,
    fun α => (cascadeProbabilityWeight_pos_finite u hu_pos hu_fin r hfinite α).1⟩

/-- Measurability of the total mass of an arbitrary measurable vertex-indexed family. -/
theorem measurable_cascadeTotalMass
    {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ p α n, Measurable fun ω => u ω p α n) (r : ℕ) :
    Measurable fun ω => cascadeTotalMass (u ω) r := by
  unfold cascadeTotalMass cascadeBranchWeight
  exact Measurable.tsum (fun α =>
    Finset.measurable_prod Finset.univ (fun i _ =>
      hu i.val _ _))

/-- If child masses are bounded by a common finite factor, finiteness propagates one level.
This deterministic estimate does not assert that Poisson child masses admit such a bound. -/
theorem cascadeTotalMass_succ_le_mul
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ) (C : ENNReal)
    (hU : ∀ α : Fin r → ℕ, (∑' n, u r α n) ≤ C) :
    cascadeTotalMass u (r + 1) ≤ cascadeTotalMass u r * C := by
  rw [cascadeTotalMass_succ, cascadeTotalMass]
  calc
    (∑' α : Fin r → ℕ, cascadeBranchWeight u α * (∑' n, u r α n)) ≤
        ∑' α : Fin r → ℕ, cascadeBranchWeight u α * C :=
      ENNReal.tsum_le_tsum (fun α => mul_le_mul_left (hU α) _)
    _ = (∑' α : Fin r → ℕ, cascadeBranchWeight u α) * C :=
      ENNReal.tsum_mul_right

/-- A finite parent mass and a finite uniform child-mass bound give finite leaf mass. -/
theorem cascadeTotalMass_succ_lt_top_of_bound
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ) (C : ENNReal)
    (hparent : cascadeTotalMass u r < ∞) (hC : C < ∞)
    (hU : ∀ α : Fin r → ℕ, (∑' n, u r α n) ≤ C) :
    cascadeTotalMass u (r + 1) < ∞ := by
  exact lt_of_le_of_lt (cascadeTotalMass_succ_le_mul u r C hU)
    (ENNReal.mul_lt_top hparent hC)

end SpinGlasses
