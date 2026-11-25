/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Prékopa--Leindler and Brunn--Minkowski inequalities

For `0 < s < 1` and a.e.-measurable functions `U, V, W ≥ 0` with
`U x ^ s * V y ^ (1 - s) ≤ W (s • x + (1 - s) • y)` for all `x, y`, one has
`(∫ U) ^ s * (∫ V) ^ (1 - s) ≤ ∫ W` (Talagrand, *Spin Glasses*, Vol. I, Theorem 3.1.3).
The integrals are lower Lebesgue integrals, so no integrability is assumed.

The proof starts from the one-dimensional sumset inequality `|A| + |B| ≤ |A + B|`, applies it to
the super-level sets of bounded functions with supremum `1`, removes the normalization by rescaling
and truncation, and then inducts on the dimension by Tonelli's theorem. The general statement for an
additive Haar measure on a finite-dimensional real topological vector space follows from the
uniqueness of Haar measures.

## Main declarations

* `MeasureTheory.volume_add_volume_le_volume_add`: `|A| + |B| ≤ |A + B|` for nonempty compact
  subsets of `ℝ`.
* `MeasureTheory.lintegral_prekopa_leindler_addHaar`: the inequality for any additive Haar
  measure on any finite-dimensional real topological vector space.
* `MeasureTheory.measure_rpow_mul_measure_rpow_le`: the multiplicative Brunn--Minkowski
  inequality, `μ A ^ s * μ B ^ (1 - s) ≤ μ C` whenever `s • A + (1 - s) • B ⊆ C`.
-/

@[expose] public section

open Set
open scoped ENNReal Pointwise

namespace MeasureTheory

/-! ### The one-dimensional sumset inequality -/

/-- **One-dimensional Brunn--Minkowski for compact sets:** `|A| + |B| ≤ |A + B|`. The translates
`A + min B` and `max A + B` lie in `A + B` and meet in at most one point. -/
theorem volume_add_volume_le_volume_add {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) : volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, haA, ha⟩ := hA.exists_isGreatest hAne
  obtain ⟨b, hbB, hb⟩ := hB.exists_isLeast hBne
  have hsub : (fun x => x + b) '' A ∪ (fun y => a + y) '' B ⊆ A + B :=
    union_subset (image_subset_iff.2 fun x hx => add_mem_add hx hbB)
      (image_subset_iff.2 fun y hy => add_mem_add haA hy)
  have hdisj : AEDisjoint volume ((fun x => x + b) '' A) ((fun y => a + y) '' B) := by
    refine measure_mono_null (t := {a + b}) ?_ (measure_singleton _)
    rintro z ⟨⟨x, hx, rfl⟩, y, hy, hxy⟩
    have h1 : x ≤ a := ha hx
    have h2 : b ≤ y := hb hy
    have hxy' : a + y = x + b := hxy
    exact mem_singleton_iff.2 (by linarith)
  have hmeas : MeasurableSet ((fun y => a + y) '' B) :=
    (hB.image (continuous_const_add a)).measurableSet
  calc volume A + volume B
      = volume ((fun x => x + b) '' A) + volume ((fun y => a + y) '' B) := by
        rw [image_add_right, image_add_left, measure_preimage_add_right, measure_preimage_add]
    _ = volume ((fun x => x + b) '' A ∪ (fun y => a + y) '' B) :=
        (measure_union₀ hmeas.nullMeasurableSet hdisj).symm
    _ ≤ volume (A + B) := measure_mono hsub

/-- The weighted one-dimensional sumset inequality for measurable sets: if `A` and `B` are nonempty
and `s a + (1 - s) b ∈ C` for all `a ∈ A`, `b ∈ B`, then `s |A| + (1 - s) |B| ≤ |C|`. -/
theorem ofReal_mul_volume_add_ofReal_mul_volume_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAne : A.Nonempty)
    (hBne : B.Nonempty) (h : ∀ a ∈ A, ∀ b ∈ B, s * a + (1 - s) * b ∈ C) :
    ENNReal.ofReal s * volume A + ENNReal.ofReal (1 - s) * volume B ≤ volume C := by
  obtain ⟨a0, ha0⟩ := hAne
  obtain ⟨b0, hb0⟩ := hBne
  have hscale : ∀ {r : ℝ}, 0 ≤ r → ∀ S : Set ℝ, volume (r • S) = ENNReal.ofReal r * volume S :=
    fun hr S => by
      rw [Measure.addHaar_smul_of_nonneg volume hr, Module.finrank_self, pow_one]
  have key : ∀ K ⊆ A, IsCompact K → ∀ L ⊆ B, IsCompact L →
      ENNReal.ofReal s * volume K + ENNReal.ofReal (1 - s) * volume L ≤ volume C := by
    intro K hKA hK L hLB hL
    have hK' : IsCompact (s • insert a0 K) := (hK.insert a0).smul s
    have hL' : IsCompact ((1 - s) • insert b0 L) := (hL.insert b0).smul (1 - s)
    have hsum : s • insert a0 K + (1 - s) • insert b0 L ⊆ C := by
      rintro z ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, rfl⟩
      exact h a (insert_subset ha0 hKA ha) b (insert_subset hb0 hLB hb)
    calc ENNReal.ofReal s * volume K + ENNReal.ofReal (1 - s) * volume L
        ≤ volume (s • insert a0 K) + volume ((1 - s) • insert b0 L) := by
          rw [hscale hs0, hscale (sub_nonneg.2 hs1)]
          gcongr <;> exact subset_insert _ _
      _ ≤ volume (s • insert a0 K + (1 - s) • insert b0 L) :=
          volume_add_volume_le_volume_add hK' hL' ((insert_nonempty _ _).smul_set)
            ((insert_nonempty _ _).smul_set)
      _ ≤ volume C := measure_mono hsum
  have hreg : ∀ S : Set ℝ, MeasurableSet S →
      volume S = ⨆ K : {K : Set ℝ // K ⊆ S ∧ IsCompact K}, volume K.1 := fun S hS => by
    rw [hS.measure_eq_iSup_isCompact, iSup_subtype]
    simp only [iSup_and]
  have : Nonempty {K : Set ℝ // K ⊆ A ∧ IsCompact K} := ⟨⟨∅, empty_subset _, isCompact_empty⟩⟩
  have : Nonempty {K : Set ℝ // K ⊆ B ∧ IsCompact K} := ⟨⟨∅, empty_subset _, isCompact_empty⟩⟩
  rw [hreg A hA, hreg B hB, ENNReal.mul_iSup, ENNReal.mul_iSup]
  exact ENNReal.iSup_add_iSup_le fun K L => key K.1 K.2.1 K.2.2 L.1 L.2.1 L.2.2

/-! ### The inequality on the real line -/

/-- **Weighted arithmetic-geometric mean inequality in `ℝ≥0∞`.** -/
theorem _root_.ENNReal.rpow_mul_rpow_le_ofReal_mul_add {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (a b : ℝ≥0∞) :
    a ^ s * b ^ (1 - s) ≤ ENNReal.ofReal s * a + ENNReal.ofReal (1 - s) * b := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  have hpq : s⁻¹.HolderConjugate (1 - s)⁻¹ :=
    Real.holderConjugate_iff.2 ⟨(one_lt_inv₀ hs0).2 hs1, by rw [inv_inv, inv_inv]; ring⟩
  refine (ENNReal.young_inequality (a ^ s) (b ^ (1 - s)) hpq).trans_eq ?_
  rw [ENNReal.rpow_rpow_inv hs0.ne', ENNReal.rpow_rpow_inv h1s.ne', ENNReal.ofReal_inv_of_pos hs0,
    ENNReal.ofReal_inv_of_pos h1s, div_eq_mul_inv, div_eq_mul_inv, inv_inv, inv_inv, mul_comm a,
    mul_comm b]

/-- Layer-cake formula for a function with values in `[0, 1]`. -/
private theorem lintegral_eq_setLIntegral_Ioo_meas_lt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioo (0 : ℝ) 1, μ {x | ENNReal.ofReal t < f x} := by
  have htop : ∀ x, f x ≠ ∞ := fun x => ((hf1 x).trans_lt ENNReal.one_lt_top).ne
  have h1 : ∫⁻ x, f x ∂μ = ∫⁻ x, ENNReal.ofReal (f x).toReal ∂μ :=
    lintegral_congr fun x => (ENNReal.ofReal_toReal (htop x)).symm
  rw [h1, lintegral_eq_lintegral_meas_lt μ (ae_of_all _ fun x => ENNReal.toReal_nonneg)
    hf.ennreal_toReal.aemeasurable]
  have h2 : ∫⁻ t in Ioi (0 : ℝ), μ {a | t < (f a).toReal} =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} :=
    setLIntegral_congr_fun measurableSet_Ioi fun t ht => by
      congr 1
      ext x
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (htop x)).symm
  have h3 : ∫⁻ t in Ici (1 : ℝ), μ {x | ENNReal.ofReal t < f x} = 0 := by
    refine (setLIntegral_congr_fun measurableSet_Ici fun t ht => ?_).trans lintegral_zero
    have : {x | ENNReal.ofReal t < f x} = ∅ := eq_empty_of_forall_notMem fun x hx =>
      (hx.trans_le (hf1 x)).not_ge (ENNReal.one_le_ofReal.2 ht)
    simp [this]
  rw [h2, ← Ioo_union_Ici_eq_Ioi (zero_lt_one (α := ℝ)),
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.2 fun t (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : (1 : ℝ) ≤ t) => ht.2.not_ge ht'),
    h3, add_zero]

/-- Prékopa--Leindler on `ℝ` for `U, V ≤ 1` with supremum `1`, in additive form. -/
private theorem ofReal_mul_lintegral_add_le_of_iSup_eq_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {U V W : ℝ → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V) (hW : Measurable W)
    (hU1 : ⨆ x, U x = 1) (hV1 : ⨆ x, V x = 1)
    (h : ∀ x y, U x ^ s * V y ^ (1 - s) ≤ W (s * x + (1 - s) * y)) :
    (ENNReal.ofReal s * ∫⁻ x, U x) + (ENNReal.ofReal (1 - s) * ∫⁻ y, V y) ≤ ∫⁻ z, W z := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  set W1 : ℝ → ℝ≥0∞ := fun z => min (W z) 1 with hW1
  have hW1m : Measurable W1 := hW.min measurable_const
  have hmeas : ∀ f : ℝ → ℝ≥0∞, Measurable fun t : ℝ => volume {x | ENNReal.ofReal t < f x} :=
    fun f => Antitone.measurable fun t t' htt' =>
      measure_mono fun x hx => (ENNReal.ofReal_le_ofReal htt').trans_lt hx
  rw [lintegral_eq_setLIntegral_Ioo_meas_lt volume hU fun x => (le_iSup U x).trans_eq hU1,
    lintegral_eq_setLIntegral_Ioo_meas_lt volume hV fun x => (le_iSup V x).trans_eq hV1,
    ← lintegral_const_mul _ (hmeas U), ← lintegral_const_mul _ (hmeas V),
    ← lintegral_add_left ((hmeas U).const_mul _)]
  refine le_trans ?_ (lintegral_mono fun z => min_le_left (W z) 1)
  rw [lintegral_eq_setLIntegral_Ioo_meas_lt volume hW1m fun z => min_le_right _ _]
  refine setLIntegral_mono (hmeas W1) fun t ht => ?_
  have ht1 : ENNReal.ofReal t < 1 := ENNReal.ofReal_lt_one.2 ht.2
  have hne : ∀ f : ℝ → ℝ≥0∞, ⨆ x, f x = 1 → {x | ENNReal.ofReal t < f x}.Nonempty :=
    fun f hf => by
      have : ENNReal.ofReal t < ⨆ x, f x := by rw [hf]; exact ht1
      exact lt_iSup_iff.1 this
  refine ofReal_mul_volume_add_ofReal_mul_volume_le hs0.le hs1.le
    (measurableSet_lt measurable_const hU) (measurableSet_lt measurable_const hV) (hne U hU1)
    (hne V hV1) fun x hx y hy => lt_min ?_ ht1
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht.1).ne'
  calc ENNReal.ofReal t = ENNReal.ofReal t ^ s * ENNReal.ofReal t ^ (1 - s) := by
        rw [← ENNReal.rpow_add _ _ ht0 ENNReal.ofReal_ne_top, add_sub_cancel, ENNReal.rpow_one]
    _ < U x ^ s * V y ^ (1 - s) :=
        ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx hs0) (ENNReal.rpow_lt_rpow hy h1s)
    _ ≤ W (s * x + (1 - s) * y) := h x y

/-- Prékopa--Leindler on `ℝ` for bounded `U, V`. -/
private theorem lintegral_prekopa_leindler_real_of_iSup_ne_top {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) {U V W : ℝ → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V) (hW : Measurable W)
    (hUt : ⨆ x, U x ≠ ∞) (hVt : ⨆ x, V x ≠ ∞)
    (h : ∀ x y, U x ^ s * V y ^ (1 - s) ≤ W (s * x + (1 - s) * y)) :
    (∫⁻ x, U x) ^ s * (∫⁻ y, V y) ^ (1 - s) ≤ ∫⁻ z, W z := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  set a := ⨆ x, U x with ha
  set b := ⨆ x, V x with hb
  rcases eq_or_ne a 0 with ha0 | ha0
  · have : ∀ x, U x = 0 := fun x => nonpos_iff_eq_zero.1 ((le_iSup U x).trans_eq ha0)
    simp [this, ENNReal.zero_rpow_of_pos hs0]
  rcases eq_or_ne b 0 with hb0 | hb0
  · have : ∀ x, V x = 0 := fun x => nonpos_iff_eq_zero.1 ((le_iSup V x).trans_eq hb0)
    simp [this, ENNReal.zero_rpow_of_pos h1s]
  set c := a ^ s * b ^ (1 - s) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by simp [ENNReal.rpow_eq_zero_iff, ha0, hUt])
    (by simp [ENNReal.rpow_eq_zero_iff, hb0, hVt])
  have hct : c ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hs0.le hUt)
    (ENNReal.rpow_ne_top_of_nonneg h1s.le hVt)
  have hcinv : c⁻¹ = a⁻¹ ^ s * b⁻¹ ^ (1 - s) := by
    rw [ENNReal.inv_rpow, ENNReal.inv_rpow, hc, ENNReal.mul_inv
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg h1s.le hVt))
      (Or.inl (ENNReal.rpow_ne_top_of_nonneg hs0.le hUt))]
  have key := ofReal_mul_lintegral_add_le_of_iSup_eq_one hs0 hs1
    (U := fun x => U x * a⁻¹) (V := fun x => V x * b⁻¹) (W := fun x => W x * c⁻¹)
    (hU.mul_const _) (hV.mul_const _) (hW.mul_const _)
    (by rw [← ENNReal.iSup_mul, ← ha, ENNReal.mul_inv_cancel ha0 hUt])
    (by rw [← ENNReal.iSup_mul, ← hb, ENNReal.mul_inv_cancel hb0 hVt])
    (fun x y => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ENNReal.mul_rpow_of_nonneg _ _ h1s.le,
        mul_mul_mul_comm, ← hcinv]
      exact mul_le_mul_left (h x y) _)
  have key' := le_trans (ENNReal.rpow_mul_rpow_le_ofReal_mul_add hs0 hs1
    (∫⁻ x, U x * a⁻¹) (∫⁻ y, V y * b⁻¹)) key
  rw [lintegral_mul_const _ hU, lintegral_mul_const _ hV, lintegral_mul_const _ hW,
    ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ENNReal.mul_rpow_of_nonneg _ _ h1s.le,
    mul_mul_mul_comm, ← hcinv] at key'
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 hct)
    (ENNReal.inv_ne_top.2 hc0)).1 key'

/-- Prékopa--Leindler on `ℝ`, the base case of the induction on the dimension. -/
private theorem lintegral_prekopa_leindler_real {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {U V W : ℝ → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V) (hW : Measurable W)
    (h : ∀ x y, U x ^ s * V y ^ (1 - s) ≤ W (s * x + (1 - s) * y)) :
    (∫⁻ x, U x) ^ s * (∫⁻ y, V y) ^ (1 - s) ≤ ∫⁻ z, W z := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  have htrunc : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x = ⨆ n : ℕ, ∫⁻ x, min (f x) n := fun f hf => by
    rw [← lintegral_iSup (f := fun (n : ℕ) x => min (f x) n)
      (fun n => hf.min measurable_const)
      (fun n m hnm x => min_le_min_left _ (Nat.cast_le.2 hnm))]
    refine lintegral_congr fun x => ?_
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hbdd : ∀ (f : ℝ → ℝ≥0∞) (n : ℕ), ⨆ x, min (f x) n ≠ ∞ := fun f n =>
    ((iSup_le fun x => min_le_right _ _).trans_lt (ENNReal.natCast_lt_top n)).ne
  have hs := (ENNReal.orderIsoRpow s hs0).map_iSup fun n : ℕ => ∫⁻ x, min (U x) n
  have h1 := (ENNReal.orderIsoRpow (1 - s) h1s).map_iSup fun n : ℕ => ∫⁻ x, min (V x) n
  simp only [ENNReal.orderIsoRpow_apply] at hs h1
  rw [htrunc U hU, htrunc V hV, hs, h1, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  exact lintegral_prekopa_leindler_real_of_iSup_ne_top hs0 hs1 (hU.min measurable_const)
    (hV.min measurable_const) hW (hbdd U n) (hbdd V m) fun x y =>
      (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) hs0.le)
        (ENNReal.rpow_le_rpow (min_le_left _ _) h1s.le)).trans (h x y)

/-! ### Higher dimensions -/

/-- Prékopa--Leindler on `Fin n → ℝ`, by induction on the dimension (Talagrand, Eq. (A.86)). -/
private theorem lintegral_prekopa_leindler_pi {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ (n : ℕ) {U V W : (Fin n → ℝ) → ℝ≥0∞}, Measurable U → Measurable V → Measurable W →
      (∀ x y, U x ^ s * V y ^ (1 - s) ≤ W (s • x + (1 - s) • y)) →
      (∫⁻ x, U x) ^ s * (∫⁻ y, V y) ^ (1 - s) ≤ ∫⁻ z, W z := by
  intro n
  induction n with
  | zero =>
    intro U V W _ _ _ h
    have hdirac : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac default := by
      rw [volume_pi, Measure.pi_of_empty (x := default)]
    rw [hdirac, lintegral_dirac, lintegral_dirac, lintegral_dirac]
    exact (h default default).trans_eq (congrArg W (Subsingleton.elim _ _))
  | succ n ih =>
    intro U V W hU hV hW h
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
    have hmp : MeasurePreserving e.symm volume volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm e
    have hsplit : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f →
        ∫⁻ x, f x = ∫⁻ a : ℝ, ∫⁻ x : Fin n → ℝ, f (e.symm (a, x)) := fun f hf => by
      rw [← hmp.lintegral_comp hf, Measure.volume_eq_prod,
        lintegral_prod (fun p : ℝ × (Fin n → ℝ) => f (e.symm p))
          (hf.comp e.symm.measurable).aemeasurable]
    have hcons : ∀ (a : ℝ) (x : Fin n → ℝ), e.symm (a, x) = Fin.cons a x := fun a x => by
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' a x
    have hlin : ∀ (a b : ℝ) (x y : Fin n → ℝ),
        s • e.symm (a, x) + (1 - s) • e.symm (b, y) =
          e.symm (s * a + (1 - s) * b, s • x + (1 - s) • y) := fun a b x y => by
      simp only [hcons]
      funext i
      cases i using Fin.cases <;> simp
    have hsec : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f → ∀ a : ℝ,
        Measurable fun x : Fin n → ℝ => f (e.symm (a, x)) := fun f hf a =>
      hf.comp (e.symm.measurable.comp measurable_prodMk_left)
    have hint : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f →
        Measurable fun a : ℝ => ∫⁻ x : Fin n → ℝ, f (e.symm (a, x)) := fun f hf =>
      Measurable.lintegral_prod_right' (f := fun p : ℝ × (Fin n → ℝ) => f (e.symm p))
        (hf.comp e.symm.measurable)
    rw [hsplit U hU, hsplit V hV, hsplit W hW]
    refine lintegral_prekopa_leindler_real hs0 hs1 (hint U hU) (hint V hV) (hint W hW)
      fun a b => ?_
    refine ih (hsec U hU a) (hsec V hV b) (hsec W hW _) fun x y => ?_
    rw [← hlin]
    exact h _ _

section AddHaar

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Prékopa--Leindler for measurable functions, transported from `Fin n → ℝ` through a basis and
the uniqueness of Haar measure. -/
private theorem lintegral_prekopa_leindler_addHaar_of_measurable {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) {U V W : E → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V) (hW : Measurable W)
    (h : ∀ x y, U x ^ s * V y ^ (1 - s) ≤ W (s • x + (1 - s) • y)) :
    (∫⁻ x, U x ∂μ) ^ s * (∫⁻ y, V y ∂μ) ^ (1 - s) ≤ ∫⁻ z, W z ∂μ := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  set L := (Module.finBasis ℝ E).equivFunL with hL
  have : LocallyCompactSpace E := L.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology E := L.toHomeomorph.secondCountableTopology
  set ν : Measure E := Measure.map L.symm volume with hν
  have : ν.IsAddHaarMeasure :=
    L.symm.toAddEquiv.isAddHaarMeasure_map volume L.symm.continuous L.continuous
  set c := Measure.addHaarScalarFactor μ ν with hc
  have hμ : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  have hint : ∀ f : E → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = (c : ℝ≥0∞) * ∫⁻ v, f (L.symm v) :=
    fun f hf => by
      conv_lhs => rw [hμ]
      rw [lintegral_smul_measure, hν, lintegral_map hf L.symm.continuous.measurable,
        ENNReal.smul_def, smul_eq_mul]
  have hpi := lintegral_prekopa_leindler_pi hs0 hs1 _
    (U := fun v => U (L.symm v)) (V := fun v => V (L.symm v)) (W := fun v => W (L.symm v))
    (hU.comp L.symm.continuous.measurable) (hV.comp L.symm.continuous.measurable)
    (hW.comp L.symm.continuous.measurable) fun x y => by
      rw [map_add, map_smul, map_smul]
      exact h _ _
  have hcc : (c : ℝ≥0∞) ^ s * (c : ℝ≥0∞) ^ (1 - s) = c := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hs0.le h1s.le, add_sub_cancel, ENNReal.rpow_one]
  rw [hint U hU, hint V hV, hint W hW, ENNReal.mul_rpow_of_nonneg _ _ hs0.le,
    ENNReal.mul_rpow_of_nonneg _ _ h1s.le, mul_mul_mul_comm, hcc]
  exact mul_le_mul_right hpi _

/-- **Prékopa--Leindler inequality** for an additive Haar measure on a finite-dimensional real
topological vector space (Talagrand, Theorem 3.1.3, Eqs. (3.11)--(3.12)). -/
theorem lintegral_prekopa_leindler_addHaar {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {U V W : E → ℝ≥0∞} (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (hW : AEMeasurable W μ)
    (h : ∀ x y, U x ^ s * V y ^ (1 - s) ≤ W (s • x + (1 - s) • y)) :
    (∫⁻ x, U x ∂μ) ^ s * (∫⁻ y, V y ∂μ) ^ (1 - s) ≤ ∫⁻ z, W z ∂μ := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  -- measurable minorants of `U`, `V` and a measurable majorant of `W`, all a.e. equal to them
  have hminor : ∀ f : E → ℝ≥0∞, AEMeasurable f μ →
      ∃ g : E → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ f =ᵐ[μ] g := fun f hf => by
    obtain ⟨S, hS, hSm, hSae⟩ : ∃ S : Set E, (∀ x ∈ S, f x = hf.mk f x) ∧ MeasurableSet S ∧
        ∀ᵐ x ∂μ, x ∈ S := by
      obtain ⟨T, hT, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hf.ae_eq_mk)
      refine ⟨Tᶜ, fun x hx => ?_, hTm.compl, compl_mem_ae_iff.2 hT0⟩
      by_contra hne
      exact hx (hT hne)
    refine ⟨S.indicator (hf.mk f), hf.measurable_mk.indicator hSm, fun x => ?_, ?_⟩
    · by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, hS x hx]
      · simp [hx]
    · filter_upwards [hSae] with x hx
      rw [indicator_of_mem hx, hS x hx]
  obtain ⟨U', hU'm, hU'le, hU'ae⟩ := hminor U hU
  obtain ⟨V', hV'm, hV'le, hV'ae⟩ := hminor V hV
  obtain ⟨T, hT, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hW.ae_eq_mk)
  classical
  set W' : E → ℝ≥0∞ := T.piecewise (fun _ => ∞) (hW.mk W) with hW'
  have hW'm : Measurable W' := measurable_const.piecewise hTm hW.measurable_mk
  have hW'le : ∀ z, W z ≤ W' z := fun z => by
    by_cases hz : z ∈ T
    · simp [hW', hz]
    · have : W z = hW.mk W z := by
        by_contra hne
        exact hz (hT hne)
      simp [hW', hz, this]
  have hW'ae : W =ᵐ[μ] W' := by
    have : ∀ᵐ z ∂μ, z ∉ T := compl_mem_ae_iff.2 hT0
    filter_upwards [this, hW.ae_eq_mk] with z hz hz'
    simp [hW', hz, hz']
  rw [lintegral_congr_ae hU'ae, lintegral_congr_ae hV'ae, lintegral_congr_ae hW'ae]
  exact lintegral_prekopa_leindler_addHaar_of_measurable μ hs0 hs1 hU'm hV'm hW'm fun x y =>
    (mul_le_mul' (ENNReal.rpow_le_rpow (hU'le x) hs0.le)
      (ENNReal.rpow_le_rpow (hV'le y) h1s.le)).trans ((h x y).trans (hW'le _))

/-- **Multiplicative Brunn--Minkowski inequality** (Talagrand, Eq. (3.13)):
`μ A ^ s * μ B ^ (1 - s) ≤ μ C` whenever `s • a + (1 - s) • b ∈ C` for `a ∈ A`, `b ∈ B`.
The set `C` need not be measurable. -/
theorem measure_rpow_mul_measure_rpow_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {A B C : Set E}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : ∀ a ∈ A, ∀ b ∈ B, s • a + (1 - s) • b ∈ C) :
    μ A ^ s * μ B ^ (1 - s) ≤ μ C := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  have hC := measurableSet_toMeasurable μ C
  have key := lintegral_prekopa_leindler_addHaar μ hs0 hs1 (U := A.indicator 1)
    (V := B.indicator 1) (W := (toMeasurable μ C).indicator 1)
    (measurable_one.indicator hA).aemeasurable (measurable_one.indicator hB).aemeasurable
    (measurable_one.indicator hC).aemeasurable fun x y => by
      by_cases hx : x ∈ A
      · by_cases hy : y ∈ B
        · simp [hx, hy, indicator_of_mem (subset_toMeasurable μ C (h x hx y hy))]
        · simp [hy, ENNReal.zero_rpow_of_pos h1s]
      · simp [hx, ENNReal.zero_rpow_of_pos hs0]
  rwa [lintegral_indicator_one hA, lintegral_indicator_one hB, lintegral_indicator_one hC,
    measure_toMeasurable] at key

end AddHaar

end MeasureTheory
