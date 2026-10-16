/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.Probability.Independence.InfinitePi

/-! # Lemmas about independence and infinite products
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory Set Function

namespace MeasurableSpace

variable {δ : Type*} {X : δ → Type*} [m : ∀ a, MeasurableSpace (X a)] {α : Type*}

-- Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean
lemma comap_pi {g : α → ∀ a, X a} : pi.comap g = ⨆ a, (m a).comap (fun x ↦ g x a) := by
  simp_rw [pi, comap_iSup, comap_comp, comp_def]

lemma comap_pi_subtype {s : Set δ} (Y : (a : δ) → α → X a) :
    pi.comap (fun x (a : s) ↦ Y (a : δ) x) = ⨆ a ∈ s, (m a).comap (Y a) := by
  rw [MeasurableSpace.comap_pi, iSup_subtype']

lemma comap_pi_range {κ : Type*} (u : κ → δ) (Y : (a : δ) → α → X a) :
    pi.comap (fun x (k : κ) ↦ Y (u k) x) = ⨆ a ∈ range u, (m a).comap (Y a) := by
  rw [MeasurableSpace.comap_pi, iSup_range]

end MeasurableSpace

namespace ProbabilityTheory

lemma hasLaw_eval_infinitePi {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    HasLaw (Function.eval i) (μ i) (infinitePi μ) :=
  (measurePreserving_eval_infinitePi μ i).hasLaw

variable {ι κ : Type*} {𝓧 : ι → κ → Type*} [m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)]
    {μ : (i : ι) → (j : κ) → Measure (𝓧 i j)} [∀ i j, IsProbabilityMeasure (μ i j)]

-- Mathlib/Probability/Independence/InfinitePi.lean
lemma indepFun_proj_infinitePi_infinitePi {a b : κ} (h : a ≠ b) :
    IndepFun (fun ω i ↦ ω i a) (fun ω i ↦ ω i b) (infinitePi (fun i ↦ infinitePi (μ i))) := by
  simp_rw [IndepFun_iff_Indep, MeasurableSpace.comap_pi]
  have hd : Disjoint (range fun i : ι ↦ (i, a)) (range fun i ↦ (i, b)) := by
    simp [disjoint_range_iff, h]
  convert indep_iSup_of_disjoint (fun _ ↦ Measurable.comap_le (by fun_prop))
    (iIndepFun_uncurry_infinitePi' (X := fun _ _ x ↦ x) μ (by fun_prop)) hd
  all_goals rw [iSup_range]

section curry

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Converse of `iIndepFun_uncurry`: if the doubly indexed family `(Xᵢⱼ)` is independent, then the
random vectors `(Xᵢⱼ)ⱼ`, indexed by `i`, are independent. -/
lemma iIndepFun.curry {κ : ι → Type*} {𝓧 : (i : ι) → κ i → Type*}
    {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)} {X : (i : ι) → (j : κ i) → Ω → 𝓧 i j}
    (mX : ∀ i j, Measurable (X i j))
    (h : iIndepFun (fun (p : (i : ι) × κ i) ω ↦ X p.1 p.2 ω) P) :
    iIndepFun (fun i ω ↦ (X i · ω)) P := by
  have := h.isProbabilityMeasure
  have e : (MeasurableEquiv.piCurry 𝓧) ∘ (fun ω p ↦ X p.1 p.2 ω) = fun ω i j ↦ X i j ω := by
    ext; simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have h2 : ∀ i, P.map (fun ω j ↦ X i j ω) = infinitePi fun j ↦ P.map (X i j) := fun i =>
    (iIndepFun_iff_map_fun_eq_infinitePi_map (fun j => mX i j)).1
      (h.precomp (g := fun j => (⟨i, j⟩ : (i : ι) × κ i)) (fun a b hab => by simpa using hab))
  have h3 := (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h
  have h4 := congrArg (Measure.map (MeasurableEquiv.piCurry 𝓧)) h3
  rw [infinitePi_map_piCurry (fun i j ↦ P.map (X i j)), map_map (by fun_prop) (by fun_prop),
    e] at h4
  rw [h4]
  congrm infinitePi fun i ↦ ?_
  exact (h2 i).symm

/-- Non-dependent version of `iIndepFun.curry`. -/
lemma iIndepFun.curry' {X : (i : ι) → (j : κ) → Ω → 𝓧 i j} (mX : ∀ i j, Measurable (X i j))
    (h : iIndepFun (fun (p : ι × κ) ω ↦ X p.1 p.2 ω) P) :
    iIndepFun (fun i ω ↦ (X i · ω)) P :=
  iIndepFun.curry mX (h.precomp (Equiv.sigmaEquivProd ι κ).injective)

end curry

end ProbabilityTheory
