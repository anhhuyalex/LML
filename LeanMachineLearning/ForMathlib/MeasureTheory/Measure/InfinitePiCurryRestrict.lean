/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

/-!
# Restricting an iterated i.i.d. array to a set of positions

An array `y' k l` of i.i.d. variables, restricted to a set `A ⊆ ℕ × ℕ` of positions and
re-enumerated by a bijection `A ≃ ℕ`, is again an i.i.d. sequence with the same law.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {T : Type*} [MeasurableSpace T]

/-- Restricting an iterated i.i.d. array to a set of positions gives the i.i.d. family on that
set. -/
theorem map_infinitePi_infinitePi_restrict (τ : Measure T) [IsProbabilityMeasure τ]
    (A : Set (ℕ × ℕ)) :
    (infinitePi fun _ : ℕ => infinitePi fun _ : ℕ => τ).map
        (fun y' (a : A) => y' a.1.1 a.1.2) = infinitePi fun _ : A => τ := by
  have hcur := infinitePi_map_piCurry_symm (κ := fun _ : ℕ => ℕ)
    (X := fun _ _ => T) (fun _ _ => τ)
  have hinj : Function.Injective (fun a : A => (⟨a.1.1, a.1.2⟩ : Σ _ : ℕ, ℕ)) := by
    intro a b h
    apply Subtype.ext
    exact Prod.ext (congrArg Sigma.fst h) (eq_of_heq (Sigma.mk.inj h).2)
  have hres := map_infinitePi_infinitePi_of_inj (P := fun _ : (Σ _ : ℕ, ℕ) => τ) hinj
  have hm1 : Measurable (fun w : (Σ _ : ℕ, ℕ) → T => fun a : A => w ⟨a.1.1, a.1.2⟩) :=
    measurable_pi_iff.2 fun a => measurable_pi_apply _
  calc (infinitePi fun _ : ℕ => infinitePi fun _ : ℕ => τ).map
        (fun y' (a : A) => y' a.1.1 a.1.2)
      = (Measure.map (fun w : (Σ _ : ℕ, ℕ) → T => fun a : A => w ⟨a.1.1, a.1.2⟩)
          ((infinitePi fun _ : ℕ => infinitePi fun _ : ℕ => τ).map
            (MeasurableEquiv.piCurry (fun (_ : ℕ) (_ : ℕ) => T)).symm)) := by
        rw [Measure.map_map hm1 (MeasurableEquiv.piCurry _).symm.measurable]
        rfl
    _ = infinitePi fun _ : A => τ := by rw [hcur]; exact hres

/-- Re-enumerating the restriction of an iterated i.i.d. array by a bijection gives an i.i.d.
sequence. -/
theorem map_infinitePi_infinitePi_restrict_equiv (τ : Measure T) [IsProbabilityMeasure τ]
    (A : Set (ℕ × ℕ)) (e : A ≃ ℕ) :
    (infinitePi fun _ : ℕ => infinitePi fun _ : ℕ => τ).map
        (fun y' n => y' (e.symm n).1.1 (e.symm n).1.2) = infinitePi fun _ : ℕ => τ := by
  have h1 := map_infinitePi_infinitePi_restrict τ A
  have h2 := infinitePi_map_piCongrLeft (X := fun _ : ℕ => T) (fun _ => τ) e
  have hm1 : Measurable (fun y' : ℕ → ℕ → T => fun a : A => y' a.1.1 a.1.2) :=
    measurable_pi_iff.2 fun a => (measurable_pi_apply _).comp (measurable_pi_apply _)
  calc (infinitePi fun _ : ℕ => infinitePi fun _ : ℕ => τ).map
        (fun y' n => y' (e.symm n).1.1 (e.symm n).1.2)
      = (Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ℕ => T) e)
          ((infinitePi fun _ : ℕ => infinitePi fun _ : ℕ => τ).map
            (fun y' (a : A) => y' a.1.1 a.1.2))) := by
        rw [Measure.map_map (MeasurableEquiv.piCongrLeft (fun _ : ℕ => T) e).measurable hm1]
        congr 1
        funext y' n
        simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    _ = infinitePi fun _ : ℕ => τ := by rw [h1]; exact h2

end MeasureTheory.Measure
