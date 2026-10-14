/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.AldousHoover
public import LeanMachineLearning.SpinGlasses.OverlapExchangeability

/-!
# The Aldous–Hoover representation of curried symmetric arrays and of Gram-type laws

`SpinGlasses.exists_aldousHoover_representation` is stated for arrays indexed by unordered pairs.
The overlap array of §1.3 (`SpinGlasses.sk_annealed_gram_array`,
`SpinGlasses.exists_sk_asymptotic_overlap_law`) is instead a *curried* array `A : ℕ → ℕ → ℝ`, which
is only almost surely symmetric, with a law `Λ` invariant under `A ↦ (A (e l) (e l'))_{l, l'}`.
This file bridges the two and records the consequence for Gram-type arrays, the input of the
Dovbysh–Sudakov theorem (§1.5).

## Main declarations

* `SpinGlasses.exists_aldousHoover_representation_of_curried`: Theorem 1.5 for a random curried
  array `R : Ω → ℕ → ℕ → E` which is a.s. symmetric and whose law is invariant under the diagonal
  action of `ℕ ≃ ℕ`.
* `SpinGlasses.exists_aldousHoover_representation_of_gram`: a law `Λ` on `ℕ → ℕ → ℝ` which is
  exchangeable and concentrated on symmetric arrays with unit diagonal is the law of
  `(if l = l' then 1 else f (w, u_l, u_{l'}, x_{l, l'}))_{l, l'}`, with `f` symmetric in its two
  middle arguments.
* `SpinGlasses.exists_aldousHoover_representation_of_gram_set`: the same for an exchangeable law
  concentrated on the set of Gram-type arrays, the form of the limits produced by
  `SpinGlasses.exists_tendsto_exchangeable_gram_arrays` and
  `SpinGlasses.exists_sk_asymptotic_overlap_law`.

## Implementation notes

* The cell array is `s c ω = Φ (R ω) c` for the measurable map `Φ A s(a, b) = A (min a b) (max a b)`
  (`Φ` is obtained inside the proof together with its defining equation, so no definition is added).
  On symmetric arrays `Φ A s(a, b) = A a b`, so `s` is a.s. the original array, and the diagonal
  action on `Sym2 ℕ` becomes the curried diagonal action.
* Positive semidefiniteness and the bound `|R| ≤ 1` are not used here.  That `f` does not depend on
  the cell noise `x_{l, l'}` for positive semidefinite arrays is the content of §1.5 and is not
  formalized.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.4–1.5, Theorem 1.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped unitInterval

namespace SpinGlasses

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {P : Measure Ω}

/-- **Theorem 1.5 for a curried array.**  Let `R : Ω → ℕ → ℕ → E` be a random array with values in
a standard Borel space which is almost surely symmetric and whose law is invariant under
`R ↦ (R (e l) (e l'))_{l, l'}` for every permutation `e` of `ℕ`.  Then, as an array indexed by
`ℕ × ℕ`, `R` has the law of `g (w, u_l)` on the diagonal and `f (w, u_l, u_{l'}, x_{l, l'})` off
it, with `f` symmetric in its middle arguments and `w`, `(u_l)`, `(x_c)` independent and uniform. -/
theorem exists_aldousHoover_representation_of_curried [IsProbabilityMeasure P]
    [StandardBorelSpace E] [Nonempty E] {R : Ω → ℕ → ℕ → E}
    (hR : ∀ l l', Measurable fun ω => R ω l l')
    (hsymm : ∀ᵐ ω ∂P, ∀ l l', R ω l l' = R ω l' l)
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω l l' => R ω (e l) (e l')) R P P) :
    ∃ (g : I × I → E) (f : I × I × I × I → E), Measurable g ∧ Measurable f ∧
      (∀ w u₁ u₂ y, f (w, u₁, u₂, y) = f (w, u₂, u₁, y)) ∧
      IdentDistrib (fun ω (p : ℕ × ℕ) => R ω p.1 p.2)
        (fun (η : (I × (ℕ → I)) × (Sym2 ℕ → I)) (p : ℕ × ℕ) =>
          if p.1 = p.2 then g (η.1.1, η.1.2 p.1)
          else f (η.1.1, η.1.2 p.1, η.1.2 p.2, η.2 s(p.1, p.2))) P
        (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
          (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))) := by
  obtain ⟨Φ, hΦm, hΦ⟩ : ∃ Φ : (ℕ → ℕ → E) → Sym2 ℕ → E, Measurable Φ ∧
      ∀ A a b, Φ A s(a, b) = A (min a b) (max a b) := by
    refine ⟨fun A => Sym2.lift ⟨fun a b => A (min a b) (max a b), fun a b => by
      simp only [min_comm a b, max_comm a b]⟩, measurable_pi_iff.2 fun c => ?_, fun A a b => rfl⟩
    induction c using Sym2.ind with
    | _ a b =>
      exact (measurable_pi_apply (max a b)).comp (measurable_pi_apply (min a b))
  have hΦs : ∀ A : ℕ → ℕ → E, (∀ l l', A l l' = A l' l) → ∀ a b, Φ A s(a, b) = A a b := by
    intro A hA a b
    rw [hΦ]
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hab, max_eq_left hab, hA]
  have hRm : Measurable R := by fun_prop
  have hRe : ∀ e : ℕ ≃ ℕ, Measurable fun ω l l' => R ω (e l) (e l') := fun e => by fun_prop
  have hsm : ∀ e : ℕ ≃ ℕ, Measurable fun ω (c : Sym2 ℕ) => Φ (R ω) (Sym2.map e c) := fun e =>
    measurable_pi_iff.2 fun c => (measurable_pi_apply _).comp (hΦm.comp hRm)
  obtain ⟨g, f, hg, hf, hfs, hid⟩ := exists_aldousHoover_representation (P := P)
    (s := fun c ω => Φ (R ω) c) (fun c => (measurable_pi_apply c).comp (hΦm.comp hRm)) fun e => by
      have hae : (fun ω (c : Sym2 ℕ) => Φ (R ω) (Sym2.map e c)) =ᵐ[P]
          Φ ∘ fun ω l l' => R ω (e l) (e l') := by
        filter_upwards [hsymm] with ω h
        funext c
        induction c using Sym2.ind with
        | _ a b =>
          simp only [Sym2.map_mk, comp]
          rw [hΦs _ h, hΦs _ fun l l' => h _ _]
      exact (IdentDistrib.of_ae_eq (hsm e).aemeasurable hae).trans ((hexch e).comp hΦm)
  refine ⟨g, f, hg, hf, hfs, (IdentDistrib.of_ae_eq ?_ ?_).trans hid⟩
  · exact (measurable_pi_iff.2 fun p : ℕ × ℕ => hR p.1 p.2).aemeasurable
  · filter_upwards [hsymm] with ω h
    funext p
    exact (hΦs _ h p.1 p.2).symm

/-- A law on curried arrays `ℕ → ℕ → E` is recovered from the law of the same array viewed as a
function on `ℕ × ℕ`. -/
theorem map_map_curry_array {E : Type*} [MeasurableSpace E] (Λ : Measure (ℕ → ℕ → E)) :
    (Λ.map fun A (p : ℕ × ℕ) => A p.1 p.2).map (fun x l l' => x (l, l')) = Λ := by
  have hc : Measurable fun (x : ℕ × ℕ → E) (l l' : ℕ) => x (l, l') := by fun_prop
  have hX : Measurable fun (A : ℕ → ℕ → E) (p : ℕ × ℕ) => A p.1 p.2 := by fun_prop
  rw [Measure.map_map hc hX]
  exact Measure.map_id

/-- **Aldous–Hoover representation of an exchangeable law on symmetric arrays with unit diagonal**
(the form needed for the Dovbysh–Sudakov theorem).  Let `Λ` be a probability measure on
`ℕ → ℕ → ℝ`, concentrated on symmetric arrays with `A l l = 1`, and invariant under
`A ↦ (A (e l) (e l'))_{l, l'}` for every permutation `e` of `ℕ`.  Then `Λ` is the law of
`(if l = l' then 1 else f (w, u_l, u_{l'}, x_{l, l'}))_{l, l'}` for a measurable `f` which is
symmetric in its two middle arguments, with `w`, `(u_l)`, `(x_c)` independent and uniform: the
function `g` of Theorem 1.5 is `1`.

The hypotheses are satisfied by any law concentrated on Gram-type arrays, such as the asymptotic
overlap law of `SpinGlasses.exists_sk_asymptotic_overlap_law`
(see `SpinGlasses.exists_aldousHoover_representation_of_gram_set`); symmetry and the unit diagonal
are the only properties of Gram-type arrays which enter. -/
theorem exists_aldousHoover_representation_of_gram {Λ : Measure (ℕ → ℕ → ℝ)}
    [IsProbabilityMeasure Λ] (hK : ∀ᵐ A ∂Λ, (∀ l l', A l l' = A l' l) ∧ ∀ l, A l l = 1)
    (hexch : ∀ e : ℕ ≃ ℕ, Λ.map (fun A l l' => A (e l) (e l')) = Λ) :
    ∃ f : I × I × I × I → ℝ, Measurable f ∧ (∀ w u₁ u₂ y, f (w, u₁, u₂, y) = f (w, u₂, u₁, y)) ∧
      Λ = Measure.map (fun (η : (I × (ℕ → I)) × (Sym2 ℕ → I)) (l l' : ℕ) =>
          if l = l' then (1 : ℝ) else f (η.1.1, η.1.2 l, η.1.2 l', η.2 s(l, l')))
        (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
          (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))) := by
  have hm : ∀ e : ℕ ≃ ℕ, Measurable fun (A : ℕ → ℕ → ℝ) l l' => A (e l) (e l') := fun e => by
    fun_prop
  have hR : ∀ l l', Measurable fun A : ℕ → ℕ → ℝ => A l l' := fun l l' => by fun_prop
  obtain ⟨g, f, hg, hf, hfs, hid⟩ := exists_aldousHoover_representation_of_curried (P := Λ)
    (R := fun A => A) hR (hK.mono fun A h => h.1) fun e =>
    ⟨(hm e).aemeasurable, aemeasurable_id, (hexch e).trans Measure.map_id.symm⟩
  refine ⟨f, hf, hfs, ?_⟩
  have hc : Measurable fun (x : ℕ × ℕ → ℝ) (l l' : ℕ) => x (l, l') := by fun_prop
  have hD : MeasurableSet {x : ℕ × ℕ → ℝ | ∀ l, x (l, l) = 1} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun l => measurableSet_eq_fun (measurable_pi_apply _)
      measurable_const
  have hdiag := hid.ae_snd hD (by filter_upwards [hK] with A hA l using hA.2 l)
  calc Λ = (Λ.map fun A p => A p.1 p.2).map fun x l l' => x (l, l') :=
        (map_map_curry_array Λ).symm
    _ = _ := by
        rw [hid.map_eq, AEMeasurable.map_map_of_aemeasurable hc.aemeasurable
          hid.aemeasurable_snd]
        refine Measure.map_congr ?_
        filter_upwards [hdiag] with η hη
        funext l l'
        by_cases h : l = l'
        · subst h
          simpa using hη l
        · simp [h]

/-- **Aldous–Hoover representation of an exchangeable law on Gram-type arrays.**  This is the
form of the limits of `SpinGlasses.exists_tendsto_exchangeable_gram_arrays` and of the asymptotic
overlap law `SpinGlasses.exists_sk_asymptotic_overlap_law`: a probability measure `μ` on arrays,
concentrated on the (closed) set of Gram-type arrays and invariant under the diagonal action of
`ℕ ≃ ℕ`, is the law of `(if l = l' then 1 else f (w, u_l, u_{l'}, x_{l, l'}))_{l, l'}`.  What
remains for the Dovbysh–Sudakov theorem is to show, using positive semidefiniteness, that `f` does
not depend on `x`. -/
theorem exists_aldousHoover_representation_of_gram_set {μ : Measure (ℕ → ℕ → ℝ)}
    [IsProbabilityMeasure μ]
    (hK : μ {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
      (∀ l l', |A l l'| ≤ 1) ∧ ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} = 1)
    (hexch : ∀ e : ℕ ≃ ℕ, μ.map (fun A l l' => A (e l) (e l')) = μ) :
    ∃ f : I × I × I × I → ℝ, Measurable f ∧ (∀ w u₁ u₂ y, f (w, u₁, u₂, y) = f (w, u₂, u₁, y)) ∧
      μ = Measure.map (fun (η : (I × (ℕ → I)) × (Sym2 ℕ → I)) (l l' : ℕ) =>
          if l = l' then (1 : ℝ) else f (η.1.1, η.1.2 l, η.1.2 l', η.2 s(l, l')))
        (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
          (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))) :=
  exists_aldousHoover_representation_of_gram
    (Filter.Eventually.mono ((mem_ae_iff_prob_eq_one
      isCompact_setOf_gram_array.isClosed.measurableSet).2 hK) fun _ h => ⟨h.1, h.2.1⟩) hexch

end SpinGlasses
