/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.Lattice
public import Mathlib

@[expose] public section

open Finset

variable {ι α : Type*} [LinearOrder α] [Fintype ι] [Nonempty ι] (f : ι → α)

namespace Function

/-- The maximum value of a tuple. -/
abbrev max : α := univ.sup' (by simp) f

/-- The minimum value of a tuple. -/
abbrev min : α := univ.inf' (by simp) f

lemma le_max (x : ι) : f x ≤ max f := le_sup' _ (by simp)

lemma min_le (x : ι) : min f ≤ f x := inf'_le _ (by simp)

end Function

section Argmax

lemma exists_argmax : ∃ i, f i = f.max := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (by simp : Finset.univ.Nonempty) f
  exact ⟨i, hi.symm⟩

/-- The index of the maximum value of a tuple. -/
noncomputable def measurableArgmax := (exists_argmax f).choose

lemma argmax_spec : f (measurableArgmax f) = f.max := (exists_argmax f).choose_spec

lemma isMaxOn_measurableArgmax (x : ι) : f x ≤ f (measurableArgmax f) := by
  rw [argmax_spec f]
  exact f.le_max x

end Argmax

section Argmin

lemma exists_argmin : ∃ i, f i = f.min := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (by simp : Finset.univ.Nonempty) f
  exact ⟨i, hi.symm⟩

/-- The index of the minimum value of a tuple. -/
noncomputable def measurableArgmin := (exists_argmin f).choose

lemma argmin_spec : f (measurableArgmin f) = f.min := (exists_argmin f).choose_spec

lemma isMinOn_measurableArgmin (x : ι) : f (measurableArgmin f) ≤ f x := by
  rw [argmin_spec f]
  exact f.min_le x

end Argmin

lemma neg_max_eq_min_neg [AddGroup α] [AddLeftMono α] [AddRightMono α] : -f.max = (-f).min := by
  refine le_antisymm ?_ ?_
  · simp; grind
  · simp only [inf'_le_iff, mem_univ, Pi.neg_apply, neg_le_neg_iff, sup'_le_iff, forall_const,
      true_and]
    exact ⟨measurableArgmax f, isMaxOn_measurableArgmax f⟩

variable [MeasurableSpace α]

section MeasurableArgmax

@[fun_prop]
lemma measurable_max [MeasurableSup₂ α] : Measurable (fun (t : ι → α) => t.max) := by
  suffices (fun f : ι → α ↦ f.max) = (univ.sup' univ_nonempty fun i f => f i) by
    rw [this]
    exact measurable_sup' univ_nonempty (fun i _ => measurable_pi_apply i)
  ext; simp [Function.max]

@[fun_prop]
lemma measurable_argmax [MeasurableSpace ι] [MeasurableEq α] [MeasurableSup₂ α] :
    Measurable fun f : ι → α ↦ measurableArgmax f := by
  refine measurable_to_countable' fun i ↦ ?_
  simp only [Set.preimage, Set.mem_singleton_iff]
  let Maximizers (f : ι → α) : Set ι := {i | f i = f.max}
  suffices {f : ι → α | measurableArgmax f = i} = ⋃ (S)
      (hS : ∀ x, Maximizers x = S → measurableArgmax x = i), {f | Maximizers f = S} by
    rw [this]
    refine MeasurableSet.iUnion fun S ↦ (.iUnion fun hS ↦ ?_)
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
  constructor
  · intro hf x hx
    rw [← hf]
    exact Classical.choose.congr_simp hx (exists_argmax x)
  · intro h
    exact h f rfl

end MeasurableArgmax

section MeasurableArgmin

@[fun_prop]
lemma measurable_min [MeasurableInf₂ α] : Measurable (fun (f : ι → α) => f.min) := by
  suffices (fun f : ι → α ↦ f.min) = (univ.inf' univ_nonempty fun i f => f i) by
    rw [this]
    exact measurable_inf' univ_nonempty (fun i _ => measurable_pi_apply i)
  ext; simp [Function.min]

@[fun_prop]
lemma measurable_argmin [MeasurableSpace ι] [MeasurableEq α] [MeasurableInf₂ α] :
    Measurable fun f : ι → α ↦ measurableArgmin f := by
  refine measurable_to_countable' fun i ↦ ?_
  simp only [Set.preimage, Set.mem_singleton_iff]
  let Minimizers (f : ι → α) : Set ι := {i | f i = f.min}
  suffices {f : ι → α | measurableArgmin f = i} = ⋃ (S)
      (hS : ∀ x, Minimizers x = S → measurableArgmin x = i), {f | Minimizers f = S} by
    rw [this]
    refine MeasurableSet.iUnion fun S ↦ (.iUnion fun hS ↦ ?_)
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
  constructor
  · intro hf x hx
    rw [← hf]
    exact Classical.choose.congr_simp hx (exists_argmin x)
  · intro h
    exact h f rfl

end MeasurableArgmin
