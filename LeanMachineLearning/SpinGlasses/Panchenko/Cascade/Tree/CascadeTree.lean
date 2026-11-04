/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichlet
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Data.Nat.Find

/-!
# Prefix trees and deterministic cascade branch weights

Leaves at depth `r` are functions `Fin r → ℕ`. A vertex of depth `p` is a function
`Fin p → ℕ`. No ordering of Poisson atoms is needed for the deterministic results.
-/

@[expose] public section

namespace SpinGlasses

open ENNReal

/-- The longest common prefix, with values from `0` through `r`. -/
def prefixOverlap {ι : Type*} [DecidableEq ι] {r : ℕ} (α β : Fin r → ι) : Fin (r + 1) :=
  ⟨Nat.findGreatest (fun p => ∀ i : Fin r, i.val < p → α i = β i) r,
    Nat.lt_succ_of_le (Nat.findGreatest_le r)⟩

variable {ι : Type*} [DecidableEq ι]

/-- All coordinates before the overlap agree. -/
theorem prefixOverlap_agree {r : ℕ} (α β : Fin r → ι) (i : Fin r)
    (hi : i.val < (prefixOverlap α β).val) : α i = β i :=
  Nat.findGreatest_spec (P := fun p => ∀ j : Fin r, j.val < p → α j = β j)
    (Nat.zero_le r) (by simp) i hi

/-- An agreeing prefix is no longer than the maximal agreeing prefix. -/
theorem le_prefixOverlap {r : ℕ} (α β : Fin r → ι) (p : ℕ) (hp : p ≤ r)
    (h : ∀ i : Fin r, i.val < p → α i = β i) : p ≤ (prefixOverlap α β).val :=
  Nat.le_findGreatest hp h

@[simp] theorem prefixOverlap_self {r : ℕ} (α : Fin r → ι) :
    prefixOverlap α α = Fin.last r :=
  Fin.ext <| Nat.le_antisymm (Nat.findGreatest_le r)
    (le_prefixOverlap α α r le_rfl (by simp))

theorem prefixOverlap_comm {r : ℕ} (α β : Fin r → ι) :
    prefixOverlap α β = prefixOverlap β α := by
  refine Fin.ext (Nat.le_antisymm ?_ ?_)
  · exact le_prefixOverlap β α _ (Fin.le_last _) fun i hi =>
      (prefixOverlap_agree α β i hi).symm
  · exact le_prefixOverlap α β _ (Fin.le_last _) fun i hi =>
      (prefixOverlap_agree β α i hi).symm

/-- Common-prefix depth obeys the reverse ultrametric triangle inequality. -/
theorem prefixOverlap_min_le {r : ℕ} (α β γ : Fin r → ι) :
    min (prefixOverlap α γ) (prefixOverlap β γ) ≤ prefixOverlap α β := by
  refine Fin.le_iff_val_le_val.mpr
    (le_prefixOverlap α β _ (le_trans (Nat.min_le_left _ _) (Fin.le_last _)) fun i hi => ?_)
  exact (prefixOverlap_agree α γ i (hi.trans_le (Nat.min_le_left _ _))).trans
    (prefixOverlap_agree β γ i (hi.trans_le (Nat.min_le_right _ _))).symm

/-- The first `p` coordinates of two leaves agree precisely when `p` does not exceed
their overlap. -/
theorem take_eq_take_iff_le_prefixOverlap {r p : ℕ} (hp : p ≤ r) (α β : Fin r → ι) :
    Fin.take p hp α = Fin.take p hp β ↔ p ≤ (prefixOverlap α β).val := by
  refine ⟨fun h => le_prefixOverlap α β p hp fun i hi => congrFun h ⟨i.val, hi⟩, fun h => ?_⟩
  exact funext fun i => prefixOverlap_agree α β _ (i.isLt.trans_le h)

/-- Branch products with one multiplier for each parent and child label. -/
noncomputable def cascadeBranchWeight (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    {r : ℕ} (α : Fin r → ℕ) : ENNReal :=
  Finset.univ.prod (fun i : Fin r => u i.val (Fin.take i.val i.isLt.le α) (α i))

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
  · refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    · funext j
      have hj : j.val < r := j.isLt.trans_le i.isLt.le
      simp [Fin.take, Fin.snoc, Fin.castLE, hj]
    · simp
  · congr 1
    · funext j
      simp [Fin.take, Fin.snoc, Fin.castLE]
    · simp

/-- Peeling the first edge of a branch leaves the branch weight in the chosen subtree. -/
theorem cascadeBranchWeight_cons
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    {r : ℕ} (n : ℕ) (β : Fin r → ℕ) :
    cascadeBranchWeight u (Fin.cons n β) =
      u 0 (fun i : Fin 0 => i.elim0) n *
        cascadeBranchWeight (fun p γ m => u (p + 1) (Fin.cons n γ) m) β := by
  unfold cascadeBranchWeight
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.cons_zero]
  refine congrArg₂ (· * ·) (by congr 1; funext i; exact i.elim0) ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  · funext j
    cases j using Fin.cases with
    | zero => simp [Fin.take, Fin.cons]
    | succ k => simp [Fin.take, Fin.cons, Fin.castLE]

/-- The first `k + 1` coordinates of `cons n β` are `n` followed by the first `k` of `β`. -/
theorem take_succ_cons {r : ℕ} (n : ℕ) (β : Fin r → ℕ) (k : ℕ) (hk : k + 1 ≤ r + 1)
    (hk' : k ≤ r) :
    Fin.take (k + 1) hk (Fin.cons n β : Fin (r + 1) → ℕ) = Fin.cons n (Fin.take k hk' β) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [Fin.take, Fin.cons]
  | succ i => simp [Fin.take, Fin.cons, Fin.castLE]

/-- The first-level total is the root-child-weighted sum of subtree totals. -/
theorem tsum_cascadeBranchWeight_cons
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ) :
    ∑' α : Fin (r + 1) → ℕ, cascadeBranchWeight u α =
      ∑' n : ℕ, u 0 (fun i : Fin 0 => i.elim0) n *
        (∑' β : Fin r → ℕ,
          cascadeBranchWeight (fun p γ m => u (p + 1) (Fin.cons n γ) m) β) := by
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).tsum_eq]
  change (∑' c : ℕ × (Fin r → ℕ), cascadeBranchWeight u (Fin.cons c.1 c.2)) = _
  simp_rw [cascadeBranchWeight_cons]
  rw [ENNReal.tsum_prod']
  exact tsum_congr fun n => ENNReal.tsum_mul_left
    (f := fun β => cascadeBranchWeight (fun p γ m => u (p + 1) (Fin.cons n γ) m) β)
    (a := u 0 (fun i : Fin 0 => i.elim0) n)

/-- Strictly positive, finite branch masses give strictly positive, finite leaf weights. -/
theorem cascadeBranchWeight_pos_finite
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu_pos : ∀ p α n, u p α n ≠ 0)
    (hu_fin : ∀ p α n, u p α n ≠ ∞)
    {r : ℕ} (α : Fin r → ℕ) :
    cascadeBranchWeight u α ≠ 0 ∧ cascadeBranchWeight u α ≠ ∞ :=
  ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => hu_pos _ _ _,
    ENNReal.prod_ne_top fun _ _ => hu_fin _ _ _⟩

/-- The depth-zero cascade has unit total mass. -/
theorem tsum_cascadeBranchWeight_zero
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) :
    ∑' α : Fin 0 → ℕ, cascadeBranchWeight u α = 1 := by
  simp [cascadeBranchWeight_zero]

/-- Positive branch masses give a nonzero total mass (finiteness is not needed). -/
theorem tsum_cascadeBranchWeight_ne_zero
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu_pos : ∀ p α n, u p α n ≠ 0) (r : ℕ) :
    ∑' α : Fin r → ℕ, cascadeBranchWeight u α ≠ 0 := fun h =>
  (Finset.prod_ne_zero_iff.mpr fun _ _ => hu_pos _ _ _ : cascadeBranchWeight u
    (fun _ : Fin r => 0) ≠ 0)
    (nonpos_iff_eq_zero.mp (h ▸ ENNReal.le_tsum (f := cascadeBranchWeight u) _))

/-- The last-level total mass is the parent-weighted sum of its children's masses. -/
theorem tsum_cascadeBranchWeight_succ
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ) :
    ∑' α : Fin (r + 1) → ℕ, cascadeBranchWeight u α =
      ∑' α : Fin r → ℕ, cascadeBranchWeight u α * (∑' n, u r α n) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (r + 1) => ℕ)).tsum_eq]
  change (∑' c : ℕ × (Fin r → ℕ), cascadeBranchWeight u (Fin.snoc c.2 c.1)) = _
  simp_rw [cascadeBranchWeight_snoc]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  exact tsum_congr fun α =>
    ENNReal.tsum_mul_left (f := fun n => u r α n) (a := cascadeBranchWeight u α)

/-- Finite, nonzero total mass normalizes the leaf weights to a probability vector. -/
theorem tsum_cascadeBranchWeight_div
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ)
    (hfinite : ∑' α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞)
    (hpos : ∑' α : Fin r → ℕ, cascadeBranchWeight u α ≠ 0) :
    (∑' α : Fin r → ℕ, cascadeBranchWeight u α /
      ∑' β : Fin r → ℕ, cascadeBranchWeight u β) = 1 := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_inv_cancel hpos hfinite

/-- If every branch mass is positive and finite, finite total mass makes every
normalized leaf weight positive and finite. -/
theorem cascadeBranchWeight_div_pos_finite
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu_pos : ∀ p α n, u p α n ≠ 0)
    (hu_fin : ∀ p α n, u p α n ≠ ∞)
    (r : ℕ) (hfinite : ∑' α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞) (α : Fin r → ℕ) :
    cascadeBranchWeight u α / (∑' β : Fin r → ℕ, cascadeBranchWeight u β) ≠ 0 ∧
      cascadeBranchWeight u α / (∑' β : Fin r → ℕ, cascadeBranchWeight u β) ≠ ∞ := by
  have hw := cascadeBranchWeight_pos_finite u hu_pos hu_fin α
  exact ⟨ENNReal.div_ne_zero.mpr ⟨hw.1, hfinite⟩,
    ENNReal.div_ne_top hw.2 (tsum_cascadeBranchWeight_ne_zero u hu_pos r)⟩

/-- Positive finite branch masses and finite total mass give a probability vector
with strictly positive entries. -/
theorem cascadeBranchWeight_div_probability
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu_pos : ∀ p α n, u p α n ≠ 0)
    (hu_fin : ∀ p α n, u p α n ≠ ∞)
    (r : ℕ) (hfinite : ∑' α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞) :
    (∑' α : Fin r → ℕ, cascadeBranchWeight u α /
        ∑' β : Fin r → ℕ, cascadeBranchWeight u β) = 1 ∧
      ∀ α : Fin r → ℕ, cascadeBranchWeight u α /
        (∑' β : Fin r → ℕ, cascadeBranchWeight u β) ≠ 0 :=
  ⟨tsum_cascadeBranchWeight_div u r hfinite (tsum_cascadeBranchWeight_ne_zero u hu_pos r),
    fun α => (cascadeBranchWeight_div_pos_finite u hu_pos hu_fin r hfinite α).1⟩

/-- Measurability of the total mass of an arbitrary measurable vertex-indexed family. -/
theorem measurable_tsum_cascadeBranchWeight
    {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ p α n, Measurable fun ω => u ω p α n) (r : ℕ) :
    Measurable fun ω => ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α :=
  Measurable.tsum fun _ => Finset.measurable_prod _ fun i _ => hu i.val _ _

/-- Almost-sure finiteness and positive finite branch masses give almost-sure
normalization. This separates the deterministic conclusion of Lemma 2.4 from its
still-needed probabilistic finiteness and positivity inputs. -/
theorem ae_cascadeBranchWeight_div_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ)
    (hfinite : ∀ᵐ ω ∂P, ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α < ∞)
    (hpos : ∀ᵐ ω ∂P, ∀ p α n, u ω p α n ≠ 0)
    (hbranch : ∀ᵐ ω ∂P, ∀ p α n, u ω p α n ≠ ∞) :
    ∀ᵐ ω ∂P,
      (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α /
          ∑' β : Fin r → ℕ, cascadeBranchWeight (u ω) β) = 1 ∧
        ∀ α : Fin r → ℕ, cascadeBranchWeight (u ω) α /
          (∑' β : Fin r → ℕ, cascadeBranchWeight (u ω) β) ≠ 0 := by
  filter_upwards [hfinite, hpos, hbranch] with ω hf hp hb
  exact cascadeBranchWeight_div_probability (u ω) hp hb r hf.ne

/-- Measurability of every leaf's normalized weight, without a finiteness
hypothesis (division in `ENNReal` is defined also on exceptional samples). -/
theorem measurable_cascadeBranchWeight_div
    {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ p α n, Measurable fun ω => u ω p α n)
    (r : ℕ) (α : Fin r → ℕ) :
    Measurable fun ω => cascadeBranchWeight (u ω) α /
      ∑' β : Fin r → ℕ, cascadeBranchWeight (u ω) β :=
  (Finset.measurable_prod _ fun i _ => hu i.val _ _).div
    (measurable_tsum_cascadeBranchWeight u hu r)

/-- The depth-one cascade is finite almost surely when its child masses are the
positive-part masses of a Poisson counting measure with zeta intensity. The indexing
of positive atoms by natural numbers is supplied as an explicit, pointwise hypothesis. -/
theorem ae_tsum_cascadeBranchWeight_one_lt_top_of_poisson_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → MeasureTheory.Measure ℝ)
    [∀ n, MeasureTheory.IsProbabilityMeasure (ν n)] (rate : ℕ → NNReal)
    (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ n, Measurable (B n))
    (hlaw : ∀ n, ProbabilityTheory.HasLaw (B n)
      ((ProbabilityTheory.poissonMeasure (rate n)).prod
        (MeasureTheory.Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ =
      MeasureTheory.Measure.sum fun n => (rate n : ENNReal) • ν n)
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hroot : ∀ ω, (∑' n, u ω 0 (fun i : Fin 0 => i.elim0) n) =
      ∫⁻ x in Set.Ioi 0, ENNReal.ofReal x ∂
        poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)) :
    ∀ᵐ ω ∂P, ∑' α : Fin 1 → ℕ, cascadeBranchWeight (u ω) α < ∞ := by
  have hfin := ae_lintegral_poisson_lt_top_of_blocks (P := P)
    (M := fun ω => poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => (B n ω).2 l)) ν rate hζ0 hζ1 hBm hlaw hμ (fun _ => rfl)
  filter_upwards [hfin] with ω hω
  rw [tsum_cascadeBranchWeight_succ]
  simpa [cascadeBranchWeight_zero] using (hroot ω ▸ hω)

/-- The canonical decreasing enumeration of the root Poisson atoms has finite
total mass almost surely. No separate enumeration-to-integral assumption is needed. -/
theorem ae_tsum_cascadeBranchWeight_one_lt_top_of_ranked_poisson_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → MeasureTheory.Measure ℝ)
    [∀ n, MeasureTheory.IsProbabilityMeasure (ν n)] (rate : ℕ → NNReal)
    (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ n, Measurable (B n))
    (hlaw : ∀ n, ProbabilityTheory.HasLaw (B n)
      ((ProbabilityTheory.poissonMeasure (rate n)).prod
        (MeasureTheory.Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ =
      MeasureTheory.Measure.sum fun n => (rate n : ENNReal) • ν n) :
    ∀ᵐ ω ∂P, ∑' α : Fin 1 → ℕ, cascadeBranchWeight
      (fun (p : ℕ) (_ : Fin p → ℕ) n => MeasureTheory.nthLargestAtom n
        (poissonCountingMeasure (fun k => (B k ω).1) (fun k l => (B k ω).2 l))) α < ∞ := by
  refine ae_tsum_cascadeBranchWeight_one_lt_top_of_poisson_blocks hζ0 hζ1 ν rate B hBm hlaw
    hμ _ fun ω => MeasureTheory.tsum_nthLargestAtom fun s _ =>
      poissonCountingMeasure_apply_eq_top_or_natCast _ _ measurableSet_Ioi

/-- A summable weighted family of parent-specific bounds controls the next level.
Unlike a uniform bound, this can handle infinitely many parents with unbounded child masses. -/
theorem tsum_cascadeBranchWeight_succ_le_tsum_bounds
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ)
    (C : (Fin r → ℕ) → ENNReal)
    (hU : ∀ α : Fin r → ℕ, (∑' n, u r α n) ≤ C α) :
    ∑' α : Fin (r + 1) → ℕ, cascadeBranchWeight u α ≤
      ∑' α : Fin r → ℕ, cascadeBranchWeight u α * C α := by
  rw [tsum_cascadeBranchWeight_succ]
  exact ENNReal.tsum_le_tsum fun α => mul_le_mul_of_nonneg_left (hU α) zero_le

/-- Summability of weighted parent-specific child bounds implies finite leaf mass. -/
theorem tsum_cascadeBranchWeight_succ_lt_top_of_tsum_bounds
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ)
    (C : (Fin r → ℕ) → ENNReal)
    (hU : ∀ α : Fin r → ℕ, (∑' n, u r α n) ≤ C α)
    (hC : (∑' α : Fin r → ℕ, cascadeBranchWeight u α * C α) < ∞) :
    ∑' α : Fin (r + 1) → ℕ, cascadeBranchWeight u α < ∞ :=
  (tsum_cascadeBranchWeight_succ_le_tsum_bounds u r C hU).trans_lt hC

/-- Almost-sure summable parent-specific bounds yield almost-sure finiteness at the
next depth. The weighted bound is an explicit hypothesis, not a consequence of
independence of the child processes. -/
theorem ae_tsum_cascadeBranchWeight_succ_lt_top_of_tsum_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal) (r : ℕ)
    (C : Ω → (Fin r → ℕ) → ENNReal)
    (hU : ∀ᵐ ω ∂P, ∀ α : Fin r → ℕ, (∑' n, u ω r α n) ≤ C ω α)
    (hC : ∀ᵐ ω ∂P,
      (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α * C ω α) < ∞) :
    ∀ᵐ ω ∂P, ∑' α : Fin (r + 1) → ℕ, cascadeBranchWeight (u ω) α < ∞ := by
  filter_upwards [hU, hC] with ω hu hc
  exact tsum_cascadeBranchWeight_succ_lt_top_of_tsum_bounds (u ω) r (C ω) hu hc

end SpinGlasses
