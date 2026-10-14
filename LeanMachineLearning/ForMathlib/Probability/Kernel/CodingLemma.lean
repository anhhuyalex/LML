/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Representation

/-!
# The coding lemma (isolating the randomness of a conditional law)

[Panchenko, *The Sherrington-Kirkpatrick Model*, 2013, Lemma 1.4]: if `(X, Y)` is a random pair
whose second coordinate takes values in a standard Borel space, then `Y` can be generated from `X`
and an independent uniform variable `u` on `[0, 1]`, in the sense that `(X, Y) =_d (X, f (X, u))`
for a measurable `f`.  Mathlib already contains the quantile construction on the kernel level
(`ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`, Kallenberg Lemma 4.22) and the
disintegration `P.map X ⊗ₘ condDistrib Y X P = P.map (X, Y)`; this file only assembles them.

The statement is stated on the level of laws, and then transported to *any* probability space
carrying an `X'` with the right law and an independent uniform `U`; the textbook space
`Ω × [0, 1]` is one instance.

## Main declarations

* `ProbabilityTheory.Kernel.exists_measurable_map_compProd_eq`: for a Markov kernel `κ` into a
  standard Borel space and a measure `Q`, `(Q ⊗ volume).map (a, u) ↦ (a, f (a, u)) = Q ⊗ₘ κ`.
* `ProbabilityTheory.exists_coding_function`: the same for the law of a random pair `(X, Y)`.
* `ProbabilityTheory.identDistrib_coding`: transport of the identity to a probability
  space carrying `X'`, `U` with `X' =_d X`, `U` uniform and independent of `X'`.
* `ProbabilityTheory.exists_coding_identDistrib`: the textbook form on `Ω × [0, 1]`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], Lemma 1.4, Eq. (1.83).
* [O. Kallenberg, *Foundations of Modern Probability*, 2021], Lemma 4.22.
-/

@[expose] public section

open MeasureTheory unitInterval

namespace ProbabilityTheory

variable {Ω Ω' Ω₁ Ω₂ : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}

/-- **Coding lemma, kernel form.** A Markov kernel `κ` into a standard Borel space is realised by
a measurable `f : Ω₁ × [0, 1] → Ω₂`: coupling `Q` with the uniform law and applying
`(a, u) ↦ (a, f (a, u))` gives `Q ⊗ₘ κ`. -/
theorem Kernel.exists_measurable_map_compProd_eq [Nonempty Ω₂] [StandardBorelSpace Ω₂]
    (Q : Measure Ω₁) [SFinite Q] (κ : Kernel Ω₁ Ω₂) [IsMarkovKernel κ] :
    ∃ f : Ω₁ × I → Ω₂, Measurable f ∧
      (Q.prod volume).map (fun p => (p.1, f p)) = Q ⊗ₘ κ := by
  obtain ⟨g, hg, hgκ⟩ := κ.exists_measurable_map_eq_unitInterval
  refine ⟨fun p => g p.1 p.2, hg, ?_⟩
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply hs,
    Measure.prod_apply (hs.preimage (by fun_prop))]
  refine lintegral_congr fun a => ?_
  rw [← hgκ a, Measure.map_apply hg.of_uncurry_left (measurable_prodMk_left hs)]
  rfl

variable {P : Measure Ω} {X : Ω → Ω₁} {Y : Ω → Ω₂}

/-- **Coding lemma (Panchenko, Lemma 1.4), law form.** If `Y` takes values in a standard Borel
space, there is a measurable `f` with
`(P.map X ⊗ volume).map (x, u) ↦ (x, f (x, u)) = P.map (X, Y)`. -/
theorem exists_coding_function [Nonempty Ω₂] [StandardBorelSpace Ω₂] [IsFiniteMeasure P]
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    ∃ f : Ω₁ × I → Ω₂, Measurable f ∧
      ((P.map X).prod volume).map (fun p => (p.1, f p)) = P.map (fun ω => (X ω, Y ω)) := by
  obtain ⟨f, hf, h⟩ := Kernel.exists_measurable_map_compProd_eq (P.map X) (condDistrib Y X P)
  exact ⟨f, hf, h.trans (compProd_map_condDistrib hX hY)⟩

/-- **Transport of the coding identity.** Let `f` code `(X, Y)` as in `exists_coding_function`.
On any probability space with `X' =_d X` and a uniform `U` independent of `X'`,
`(X, Y) =_d (X', f (X', U))`. -/
theorem identDistrib_coding {f : Ω₁ × I → Ω₂} (hf : Measurable f)
    (hXY : ((P.map X).prod volume).map (fun p => (p.1, f p)) =
      P.map (fun ω => (X ω, Y ω)))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) {P' : Measure Ω'} [IsFiniteMeasure P']
    {X' : Ω' → Ω₁}
    {U : Ω' → I} (hX' : HasLaw X' (P.map X) P') (hU : HasLaw U volume P')
    (hind : IndepFun X' U P') :
    IdentDistrib (fun ω => (X ω, Y ω)) (fun ω' => (X' ω', f (X' ω', U ω'))) P P' where
  aemeasurable_fst := hX.prodMk hY
  aemeasurable_snd :=
    (measurable_fst.prodMk hf).comp_aemeasurable (hX'.aemeasurable.prodMk hU.aemeasurable)
  map_eq := by
    have h1 : P'.map (fun ω' => (X' ω', U ω')) = (P.map X).prod volume := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hX'.aemeasurable hU.aemeasurable).1 hind,
        hX'.map_eq, hU.map_eq]
    rw [← hXY, ← h1, AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      (hX'.aemeasurable.prodMk hU.aemeasurable)]
    rfl

/-- **The coding lemma in textbook form** (Panchenko, Eq. (1.83)): there is a measurable
`f : Ω₁ × [0, 1] → Ω₂` with `(X, Y) =_d (X, f (X, u))` on `Ω × [0, 1]` with `u` the uniform
coordinate, independent of `X`. -/
theorem exists_coding_identDistrib [Nonempty Ω₂] [StandardBorelSpace Ω₂] [IsProbabilityMeasure P]
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    ∃ f : Ω₁ × I → Ω₂, Measurable f ∧
      IdentDistrib (fun ω => (X ω, Y ω)) (fun p : Ω × I => (X p.1, f (X p.1, p.2)))
        P (P.prod volume) := by
  obtain ⟨f, hf, h⟩ := exists_coding_function hX hY
  have hfst : HasLaw (fun p : Ω × I => X p.1) (P.map X) (P.prod volume) :=
    ⟨hX.comp_fst, by
      change Measure.map (X ∘ Prod.fst) _ = _
      have h1 : (P.prod (volume : Measure I)).map Prod.fst = P := by simp
      rw [← AEMeasurable.map_map_of_aemeasurable (f := Prod.fst) (by rwa [h1])
        measurable_fst.aemeasurable, h1]⟩
  refine ⟨f, hf, identDistrib_coding hf h hX hY hfst measurePreserving_snd.hasLaw ?_⟩
  have h0 : IndepFun Prod.fst Prod.snd (P.prod (volume : Measure I)) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable]
    simp
  have h1 : (P.prod (volume : Measure I)).map Prod.fst = P := by simp
  exact h0.comp₀ measurable_fst.aemeasurable measurable_snd.aemeasurable (by rwa [h1])
    measurable_id.aemeasurable

end ProbabilityTheory
