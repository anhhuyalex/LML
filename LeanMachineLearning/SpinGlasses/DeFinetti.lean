/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.ConditionalExpectation.IdentDistrib
public import LeanMachineLearning.ForMathlib.MeasureTheory.ConditionalExpectation.SequentialDecoupling
public import LeanMachineLearning.ForMathlib.Probability.ConditionallyIID
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.Representation
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Exchangeable sequences and de Finetti's theorem (Panchenko §1.4)

A sequence `s : ℕ → Ω → E` is **exchangeable** if `(s (e l))_l =_d (s l)_l` for every permutation
`e : ℕ ≃ ℕ`.  No structure is introduced: the hypothesis is the `IdentDistrib` statement itself,
which is the form in which exchangeability is produced by mixtures of i.i.d. sequences
(`MeasureTheory.Measure.bind_infinitePi_map_comp_equiv`) and in which it is consumed downstream.

## Main declarations

* `SpinGlasses.identDistrib_comp_of_exchangeable`: finite re-indexings by injective maps have the
  same law.
* `SpinGlasses.identDistrib_subsequence_of_exchangeable`: Eq. (1.84), `(s (ι l))_l =_d (s l)_l`
  for every injection `ι : ℕ → ℕ`.
* `SpinGlasses.condExp_comp_ae_eq_condExp_compl`: Lemma 1.5.
* `SpinGlasses.condExp_prod_comp_eq_prod_condExp_of_exchangeable`: Eq. (1.88).
* `SpinGlasses.exists_de_finetti_representation`: Theorem 1.6.
* `SpinGlasses.identDistrib_deFinetti_comp_equiv`: the converse (the representation is
  exchangeable).

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.4, Lemma 1.5,
  Theorem 1.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology unitInterval

namespace SpinGlasses

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {P : Measure Ω}

section Exchangeable

variable {T : Type*} {s : T → Ω → E}

/-- Two injections from a finite type differ by a permutation of the target:
`e (a i) = b i` for all `i`. -/
lemma exists_equiv_comp_eq {ι : Type*} [Finite ι] {a b : ι → T} (ha : Injective a)
    (hb : Injective b) : ∃ e : T ≃ T, ∀ i, e (a i) = b i := by
  classical
  have hfin : Finite ↑{x | x ∈ range a} := (Set.finite_range a).to_subtype
  let e₀ : {x // x ∈ range a} ≃ {x // x ∈ range b} :=
    (Equiv.ofInjective a ha).symm.trans (Equiv.ofInjective b hb)
  refine ⟨Equiv.extendSubtype (p := (· ∈ range a)) (q := (· ∈ range b)) e₀, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e₀ (a i) ⟨i, rfl⟩]
  simp [e₀]

/-- **Exchangeability transfers to finite re-indexings:** if `s` is invariant in law under all
permutations of the index set, then `(s (a i))_i =_d (s (b i))_i` for any two injections `a, b`
from a finite type. -/
theorem identDistrib_comp_of_exchangeable {ι : Type*} [Finite ι]
    (hexch : ∀ e : T ≃ T, IdentDistrib (fun ω t => s (e t) ω) (fun ω t => s t ω) P P)
    {a b : ι → T} (ha : Injective a) (hb : Injective b) :
    IdentDistrib (fun ω i => s (a i) ω) (fun ω i => s (b i) ω) P P := by
  obtain ⟨e, he⟩ := exists_equiv_comp_eq ha hb
  have hu : Measurable fun (ξ : T → E) (i : ι) => ξ (a i) := measurable_pi_iff.2 fun i =>
    measurable_pi_apply (a i)
  have h := (hexch e).comp hu
  simp only [Function.comp_def, he] at h
  exact h.symm

/-- **Eq. (1.84).** Along any injection `ι` of the index set the sequence has the same law:
`(s (ι l))_l =_d (s l)_l`. -/
theorem identDistrib_subsequence_of_exchangeable [IsFiniteMeasure P] (hs : ∀ t, Measurable (s t))
    (hexch : ∀ e : T ≃ T, IdentDistrib (fun ω t => s (e t) ω) (fun ω t => s t ω) P P)
    {ι : T → T} (hι : Injective ι) :
    IdentDistrib (fun ω t => s (ι t) ω) (fun ω t => s t ω) P P := by
  have hm : ∀ ι : T → T, AEMeasurable (fun ω t => s (ι t) ω) P := fun ι =>
    (measurable_pi_iff.2 fun t => hs (ι t)).aemeasurable
  refine (identDistrib_iff_forall_finset_identDistrib (X := fun t ω => s (ι t) ω)
    (Y := s) (hm ι) (hm id)).2 fun J => ?_
  exact identDistrib_comp_of_exchangeable hexch (a := fun i : J => ι i) (b := fun i : J => i)
    (hι.comp Subtype.val_injective) Subtype.val_injective

end Exchangeable

section ConditionalNorms

variable {s : ℕ → Ω → E}

/-- **Lemma 1.5** [Panchenko, 2013]. For an exchangeable sequence, an infinite set `J` of
indices and `j ∉ J`, knowing the coordinates in `J` is as good as knowing all other coordinates
for predicting `s j`: `P[f (s j) | F_J] = P[f (s j) | F_{ℕ ∖ {j}}]` almost surely, for every
bounded measurable `f` (no continuity is needed).

This is `ProbabilityTheory.condExp_comp_ae_eq_of_exhaustion` for the exhaustions of `J` and of
`ℕ ∖ {j}` by their first `n` elements; the finite-dimensional laws agree by exchangeability. -/
theorem condExp_comp_ae_eq_condExp_compl [StandardBorelSpace E] [Nonempty E]
    [IsProbabilityMeasure P] (hs : ∀ l, Measurable (s l))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω l => s (e l) ω) (fun ω l => s l ω) P P)
    {J : Set ℕ} (hI : J.Infinite) {j : ℕ} (hj : j ∉ J) {f : E → ℝ} (hf : Measurable f)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    P[fun ω => f (s j ω) | ⨆ l ∈ J, mE.comap (s l)] =ᵐ[P]
      P[fun ω => f (s j ω) | ⨆ l ∈ ({j}ᶜ : Set ℕ), mE.comap (s l)] := by
  have hcompl : ({j}ᶜ : Set ℕ).Infinite := (Set.finite_singleton j).infinite_compl
  have hsub : J ⊆ {j}ᶜ := fun l hl hlj => hj (mem_singleton_iff.1 hlj ▸ hl)
  have hU : ∀ u : ℕ → ℕ, (⋃ n, range fun m : Fin n => u m) = range u := fun u => by
    ext x
    refine ⟨fun hx => ?_, fun ⟨m, hm⟩ => mem_iUnion.2 ⟨m + 1, ⟨m, Nat.lt_succ_self m⟩, hm⟩⟩
    obtain ⟨n, m, rfl⟩ := mem_iUnion.1 hx
    exact ⟨m, rfl⟩
  have hmono : ∀ (u : ℕ → ℕ) (n : ℕ), (range fun m : Fin n => u m) ⊆
      range fun m : Fin (n + 1) => u m := fun u n x ⟨m, hm⟩ => ⟨m.castSucc, hm⟩
  have hinj : ∀ (n : ℕ) (u : ℕ → ℕ), Injective u → j ∉ range u →
      Injective fun o : Option (Fin n) => o.elim j fun m => u m := by
    intro n u hu hj o o' h
    rcases o with _ | m <;> rcases o' with _ | m'
    · rfl
    · exact absurd ⟨m', h.symm⟩ hj
    · exact absurd ⟨m, h⟩ hj
    · exact congrArg some (Fin.ext (hu h))
  set u : ℕ → ℕ := Nat.nth (· ∈ J) with hu_def
  set u' : ℕ → ℕ := Nat.nth (· ∈ ({j}ᶜ : Set ℕ)) with hu'_def
  have hr : range u = J := Nat.range_nth_of_infinite hI
  have hr' : range u' = {j}ᶜ := Nat.range_nth_of_infinite hcompl
  have key := condExp_comp_ae_eq_of_exhaustion (P := P) (s := s) hs (κ := fun n => Fin n)
    (fun n m => u m) (fun n m => u' m) (hmono u) (hmono u')
    (by rw [hU, hU, hr, hr']; exact hsub) hf hfb (t := j) fun n => by
      have hid := identDistrib_comp_of_exchangeable hexch
        (hinj n u (Nat.nth_injective hI) (hr ▸ hj))
        (hinj n u' (Nat.nth_injective hcompl) (hr' ▸ (by simp : j ∉ ({j}ᶜ : Set ℕ))))
      exact hid.comp (u := fun ξ : Option (Fin n) → E => (fun m => ξ (some m), ξ none))
        (by fun_prop)
  rwa [hU, hU, hr, hr'] at key

/-- Conditionally on the coordinates in `K`, two coordinates outside `K` are identically
distributed: `P[f (s i) | F_K] = P[f (s i') | F_K]` for `i, i' ∉ K` (swap `i` and `i'`, which fixes
`K` pointwise). -/
theorem condExp_comp_ae_eq_of_exchangeable [StandardBorelSpace E] [Nonempty E]
    [IsProbabilityMeasure P] (hs : ∀ l, Measurable (s l))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω l => s (e l) ω) (fun ω l => s l ω) P P)
    {K : Set ℕ} {i i' : ℕ} (hi : i ∉ K) (hi' : i' ∉ K) {f : E → ℝ} (hf : Measurable f)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    P[fun ω => f (s i ω) | ⨆ k ∈ K, mE.comap (s k)] =ᵐ[P]
      P[fun ω => f (s i' ω) | ⨆ k ∈ K, mE.comap (s k)] := by
  have hcomap : (⨆ k ∈ K, mE.comap (s k)) =
      MeasurableSpace.pi.comap (fun ω (k : K) => s k ω) :=
    (MeasurableSpace.comap_pi_subtype s).symm
  rw [hcomap]
  have hid := (hexch (Equiv.swap i i')).comp
    (u := fun ξ : ℕ → E => (fun k : K => ξ k, ξ i')) (by fun_prop)
  have hfix : ∀ k : K, Equiv.swap i i' k = k := fun k =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ k.2)) fun h => hi' (h ▸ k.2)
  refine condExp_comp_ae_eq_of_map_eq (measurable_pi_iff.2 fun k => hs k) (hs i).aemeasurable
    (hs i').aemeasurable hf hfb ?_
  have := hid.map_eq
  simp only [Function.comp_def, hfix, Equiv.swap_apply_right] at this
  exact this

/-- **Eq. (1.88).** Let `K` be an infinite set of indices and `l i ∉ K` distinct indices.  For an
exchangeable sequence the coordinates `s (l i)` are conditionally independent given `F_K`:
`P[∏ f i (s (l i)) | F_K] = ∏ P[f i (s (l i)) | F_K]` almost surely, for bounded measurable
`f i`. -/
theorem condExp_prod_comp_eq_prod_condExp_of_exchangeable [StandardBorelSpace E] [Nonempty E]
    [IsProbabilityMeasure P] (hs : ∀ l, Measurable (s l))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω l => s (e l) ω) (fun ω l => s l ω) P P)
    {K : Set ℕ} (hK : K.Infinite) {ι : Type*} (t : Finset ι) (l : ι → ℕ) (hl : Set.InjOn l t)
    (hlK : ∀ i ∈ t, l i ∉ K) (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (hfb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C) :
    P[fun ω => ∏ i ∈ t, f i (s (l i) ω) | ⨆ k ∈ K, mE.comap (s k)] =ᵐ[P]
      fun ω => ∏ i ∈ t, P[fun ω' => f i (s (l i) ω') | ⨆ k ∈ K, mE.comap (s k)] ω := by
  exact condExp_finset_prod_comp_eq_prod_condExp hs K t l hl hlK f hf hfb
    fun i hi K' hKK' hn => (condExp_comp_ae_eq_condExp_compl hs hexch (hK.mono hKK') hn (hf i)
      (hfb i)).trans (condExp_comp_ae_eq_condExp_compl hs hexch hK (hlK i hi) (hf i) (hfb i)).symm

end ConditionalNorms

section Representation

variable {s : ℕ → Ω → E}

/-- **de Finetti's theorem** [Panchenko, 2013, Theorem 1.6, Eq. (1.82)]. An exchangeable sequence
with values in a standard Borel space is, in law, a function `g` of one uniform variable `w` (the
mixing parameter) and i.i.d. uniform variables `u_l`: `(s l)_l =_d (g (w, u_l))_l`, with
`w, (u_l)` independent and uniform on `[0, 1]`.

The proof follows the book.  Conditioning on the even coordinates `X`, Lemma 1.5 makes the odd
coordinates conditionally independent (Eq. (1.88)), and exchangeability makes them conditionally
identically distributed; they are therefore a mixture of i.i.d. sequences
(`ProbabilityTheory.map_eq_bind_infinitePi_condDistrib`).  The odd coordinates have the law of the
whole sequence by Eq. (1.84).  Finally `X` and the common conditional law are coded by uniform
variables (`MeasureTheory.Measure.exists_measurable_map_eq`,
`ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`). -/
theorem exists_de_finetti_representation [StandardBorelSpace E] [Nonempty E]
    [IsProbabilityMeasure P] (hs : ∀ l, Measurable (s l))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω l => s (e l) ω) (fun ω l => s l ω) P P) :
    ∃ g : I × I → E, Measurable g ∧
      IdentDistrib (fun ω l => s l ω) (fun (p : I × (ℕ → I)) l => g (p.1, p.2 l)) P
        ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) := by
  let X : Ω → ℕ → E := fun ω m => s (2 * m) ω
  have hX : Measurable X := measurable_pi_iff.2 fun m => hs _
  have hK : (range fun m : ℕ => 2 * m).Infinite :=
    infinite_range_of_injective fun a b h => by simpa using h
  have hF : MeasurableSpace.pi.comap X = ⨆ k ∈ range fun m : ℕ => 2 * m, mE.comap (s k) := by
    rw [MeasurableSpace.comap_pi, iSup_range]
  have hodd : ∀ i : ℕ, 2 * i + 1 ∉ range fun m : ℕ => 2 * m := by
    rintro i ⟨m, hm⟩
    have : 2 * m = 2 * i + 1 := hm
    omega
  have hinj : Injective fun i : ℕ => 2 * i + 1 := fun a b h => by simpa using h
  let Y : ℕ → Ω → E := fun i => s (2 * i + 1)
  have hmix : P.map (fun ω i => Y i ω) = (P.map X).bind fun x =>
      Measure.infinitePi fun _ : ℕ => condDistrib (Y 0) X P x := by
    refine map_eq_bind_infinitePi_condDistrib hX (fun i => hs _) (fun i f hf hfb => ?_)
      (fun t f hf hfb => ?_)
    · rw [hF]
      exact condExp_comp_ae_eq_of_exchangeable hs hexch (hodd i) (hodd 0) hf hfb
    · rw [hF]
      exact condExp_prod_comp_eq_prod_condExp_of_exchangeable hs hexch hK t (fun i => 2 * i + 1)
        (hinj.injOn) (fun i _ => hodd i) f hf hfb
  have hsub : IdentDistrib (fun ω i => Y i ω) (fun ω l => s l ω) P P :=
    identDistrib_subsequence_of_exchangeable hs hexch hinj
  obtain ⟨φ, hφ, hφX⟩ := Measure.exists_measurable_map_eq (P.map X)
  obtain ⟨h, hh, hhκ⟩ := Kernel.exists_measurable_map_eq_unitInterval (condDistrib (Y 0) X P)
  have hg : Measurable fun p : I × I => h (φ p.1) p.2 :=
    hh.comp ((hφ.comp measurable_fst).prodMk measurable_snd)
  have hν : Measurable fun x => Measure.infinitePi fun _ : ℕ => condDistrib (Y 0) X P x :=
    Measure.measurable_infinitePi_const (Kernel.measurable _)
  refine ⟨fun p => h (φ p.1) p.2, hg, ?_⟩
  refine ⟨(measurable_pi_iff.2 fun l => hs l).aemeasurable,
    (Measure.measurable_pi_curry (ι := ℕ) hg).aemeasurable, ?_⟩
  rw [← hsub.map_eq, hmix, Measure.map_prod_infinitePi_eq_bind hg, ← hφX]
  unfold Measure.bind
  rw [Measure.map_map hν hφ]
  congr 2
  funext w
  simp only [hhκ]
  rfl

/-- **The converse of de Finetti's theorem.** Every sequence of the form `(g (w, u_l))_l` with
`w, (u_l)` independent uniform is exchangeable: it is a mixture of i.i.d. sequences
(`MeasureTheory.Measure.bind_infinitePi_map_comp_equiv`). -/
theorem identDistrib_deFinetti_comp_equiv {g : I × I → E} (hg : Measurable g) (e : ℕ ≃ ℕ) :
    IdentDistrib (fun (p : I × (ℕ → I)) l => g (p.1, p.2 (e l)))
      (fun (p : I × (ℕ → I)) l => g (p.1, p.2 l))
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) := by
  have hG := Measure.measurable_pi_curry (ι := ℕ) (γ := I) hg
  have hν : Measurable fun w : I => (volume : Measure I).map fun c => g (w, c) :=
    Measure.measurable_map_curry hg _
  have hT : Measurable fun ξ : ℕ → E => ξ ∘ e := measurable_pi_iff.2 fun l => measurable_pi_apply _
  refine ⟨(hT.comp hG).aemeasurable, hG.aemeasurable, ?_⟩
  change Measure.map ((fun ξ : ℕ → E => ξ ∘ e) ∘ fun (p : I × (ℕ → I)) l => g (p.1, p.2 l)) _ = _
  rw [← Measure.map_map hT hG, Measure.map_prod_infinitePi_eq_bind hg]
  exact Measure.bind_infinitePi_map_comp_equiv hν e

end Representation

end SpinGlasses
