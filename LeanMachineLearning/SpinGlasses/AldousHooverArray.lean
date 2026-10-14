/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.AldousHoover

/-!
# Separately exchangeable arrays and the Aldous–Hoover theorem (Panchenko §1.4, Theorem 1.4)

An array `s : ℕ × ℕ → Ω → E` is **separately exchangeable** if
`(s (e₁ l, e₂ l'))_{l, l'} =_d (s (l, l'))_{l, l'}` for every pair of permutations `e₁, e₂` of `ℕ`
(Eq. (1.76)).  As for sequences and weakly exchangeable arrays no structure is introduced: the
hypothesis is the `IdentDistrib` statement itself.

## Main declarations

* `SpinGlasses.identDistrib_map_of_separately_exchangeable`: sub-arrays have the same law.
* `SpinGlasses.condExp_comp_ae_eq_condExp_compl_of_separately_exchangeable`: the analogue of
  Lemma 1.6 for rectangles of cells.
* `SpinGlasses.condExp_prod_comp_eq_prod_condExp_of_separately_exchangeable`: the analogue of
  Eq. (1.94).
* `SpinGlasses.identDistrib_vertexData_comp_inj`, `SpinGlasses.condExp_rowColData_ae_eq_integral`,
  `SpinGlasses.map_rowColData_eq_compProd`: the row and column vertex arrays and the entries at the
  odd rows and columns; given the vertex arrays the entries are independent with law
  `ν (S a, T b)`.
* `SpinGlasses.map_rowColData_eq_coded`: the vertex arrays are driven by independent row and
  column noise (de Finetti for the pairs `(S k, T k)`, then disjoint sub-sequences).
* `SpinGlasses.exists_aldousHoover_representation_separately`: Theorem 1.4.
* `SpinGlasses.identDistrib_aldousHoover_separately_comp_equiv`: the converse (Eq. (1.77)).

## Implementation notes

The proofs reuse the shared statements of the weakly exchangeable case: the exhaustion principle
`ProbabilityTheory.condExp_comp_ae_eq_of_exhaustion`, the sandwich lemma
`MeasureTheory.condExp_ae_eq_of_le_of_le` and the cell decoupling
`MeasureTheory.condExp_finset_prod_comp_eq_prod_condExp`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.4, Theorem 1.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped unitInterval

namespace SpinGlasses

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {P : Measure Ω}
  {s : ℕ × ℕ → Ω → E}

section Subarray

/-- **Sub-arrays of a separately exchangeable array.**  Along injections `ι₁, ι₂` of the row and
column indices a separately exchangeable array has the same law:
`(s (ι₁ l, ι₂ l'))_{l, l'} =_d (s (l, l'))_{l, l'}`. -/
theorem identDistrib_map_of_separately_exchangeable [IsFiniteMeasure P]
    (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {ι₁ ι₂ : ℕ → ℕ} (h₁ : Injective ι₁) (h₂ : Injective ι₂) :
    IdentDistrib (fun ω (p : ℕ × ℕ) => s (ι₁ p.1, ι₂ p.2) ω) (fun ω p => s p ω) P P := by
  classical
  have hm : AEMeasurable (fun ω (p : ℕ × ℕ) => s (ι₁ p.1, ι₂ p.2) ω) P :=
    (measurable_pi_iff.2 fun p : ℕ × ℕ => hs (ι₁ p.1, ι₂ p.2)).aemeasurable
  refine (identDistrib_iff_forall_finset_identDistrib
    (X := fun (p : ℕ × ℕ) ω => s (ι₁ p.1, ι₂ p.2) ω) (Y := s) hm
    (measurable_pi_iff.2 hs).aemeasurable).2 fun J => ?_
  obtain ⟨e₁, he₁⟩ := exists_equiv_comp_eq (T := ℕ) (ι := J.image Prod.fst)
    (a := fun v => ι₁ v) (b := fun v => (v : ℕ)) (h₁.comp Subtype.val_injective)
    Subtype.val_injective
  obtain ⟨e₂, he₂⟩ := exists_equiv_comp_eq (T := ℕ) (ι := J.image Prod.snd)
    (a := fun v => ι₂ v) (b := fun v => (v : ℕ)) (h₂.comp Subtype.val_injective)
    Subtype.val_injective
  have hu : Measurable fun (ξ : ℕ × ℕ → E) (p : J) => ξ (ι₁ p.1.1, ι₂ p.1.2) :=
    measurable_pi_iff.2 fun p => measurable_pi_apply _
  have h := (hexch e₁ e₂).comp hu
  have hc : ∀ p : J, (e₁ (ι₁ p.1.1), e₂ (ι₂ p.1.2)) = p.1 := fun p =>
    Prod.ext (he₁ ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩)
      (he₂ ⟨p.1.2, Finset.mem_image_of_mem _ p.2⟩)
  simp only [Function.comp_def, hc] at h
  exact h.symm

end Subarray

section Lemma16

/-- Enumerate an infinite set of vertices injectively, listing a prescribed element first. -/
theorem exists_enum_of_infinite_first {V : Set ℕ} (hV : V.Infinite) {j : ℕ} (hj : j ∈ V) :
    ∃ W : ℕ → ℕ, Injective W ∧ range W = V ∧ W 0 = j := by
  obtain ⟨j', hj', hne⟩ := (hV.sdiff (Set.toFinite {j})).nonempty
  obtain ⟨W, hW, hWr, h0, -⟩ := exists_enum_of_infinite hV (Ne.symm (by simpa using hne)) hj hj'
  exact ⟨W, hW, hWr, h0⟩

/-- Exhaustion of the cells in the rectangle `range W₁ × range W₂` (other than the corner
`(W₁ 0, W₂ 0)`) by the cells of the first `n + 1` rows and columns.  Comparing two pairs of
enumerations that agree at `0` gives the core of the analogue of Lemma 1.6. -/
private theorem condExp_cells_ae_eq [IsProbabilityMeasure P] [StandardBorelSpace E] [Nonempty E]
    (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {W₁ W₂ W₁' W₂' : ℕ → ℕ} (hW₁ : Injective W₁) (hW₂ : Injective W₂) (hW₁' : Injective W₁')
    (hW₂' : Injective W₂') (h₁ : W₁ 0 = W₁' 0) (h₂ : W₂ 0 = W₂' 0)
    (hsub₁ : range W₁ ⊆ range W₁') (hsub₂ : range W₂ ⊆ range W₂') {f : E → ℝ}
    (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    P[fun ω => f (s (W₁ 0, W₂ 0) ω) |
        ⨆ c ∈ {c | c ≠ (W₁ 0, W₂ 0) ∧ c.1 ∈ range W₁ ∧ c.2 ∈ range W₂}, mE.comap (s c)] =ᵐ[P]
      P[fun ω => f (s (W₁ 0, W₂ 0) ω) |
        ⨆ c ∈ {c | c ≠ (W₁ 0, W₂ 0) ∧ c.1 ∈ range W₁' ∧ c.2 ∈ range W₂'}, mE.comap (s c)] := by
  let κ : ℕ → Type := fun n => {p : ℕ × ℕ // p.1 < n + 1 ∧ p.2 < n + 1 ∧ p ≠ (0, 0)}
  have hU : ∀ V₁ V₂ : ℕ → ℕ, Injective V₁ → Injective V₂ →
      (⋃ n, range fun p : κ n => (V₁ p.1.1, V₂ p.1.2)) =
        {c | c ≠ (V₁ 0, V₂ 0) ∧ c.1 ∈ range V₁ ∧ c.2 ∈ range V₂} := by
    intro V₁ V₂ hV₁ hV₂
    ext ⟨x, y⟩
    refine ⟨fun hc => ?_, fun ⟨hne, ⟨a, ha⟩, ⟨b, hb⟩⟩ => ?_⟩
    · obtain ⟨n, p, hp⟩ := mem_iUnion.1 hc
      obtain ⟨hx, hy⟩ := Prod.mk.inj hp
      refine ⟨fun h => p.2.2.2 ?_, ⟨_, hx⟩, ⟨_, hy⟩⟩
      obtain ⟨h1, h2⟩ := Prod.mk.inj (hp.trans h)
      exact Prod.ext (hV₁ h1) (hV₂ h2)
    · refine mem_iUnion.2 ⟨max a b, ⟨(a, b), ⟨by omega, by omega, fun h => hne ?_⟩⟩, ?_⟩
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        exact Prod.ext ha.symm hb.symm
      · simp [ha, hb]
  have key := condExp_comp_ae_eq_of_exhaustion (P := P) (s := s) hs (κ := κ)
    (fun n p => (W₁ p.1.1, W₂ p.1.2)) (fun n p => (W₁' p.1.1, W₂' p.1.2))
    (fun n _ ⟨p, hp⟩ => ⟨⟨p.1, by have := p.2.1; omega, by have := p.2.2.1; omega, p.2.2.2⟩, hp⟩)
    (fun n _ ⟨p, hp⟩ => ⟨⟨p.1, by have := p.2.1; omega, by have := p.2.2.1; omega, p.2.2.2⟩, hp⟩)
    (by rw [hU W₁ W₂ hW₁ hW₂, hU W₁' W₂' hW₁' hW₂']
        exact fun c ⟨h1, h2, h3⟩ => ⟨by rwa [← h₁, ← h₂], hsub₁ h2, hsub₂ h3⟩)
    hf hfb (t := (W₁ 0, W₂ 0)) fun n => by
      obtain ⟨e₁, he₁⟩ := exists_equiv_comp_eq (T := ℕ) (ι := Fin (n + 1))
        (a := fun i => W₁ i) (b := fun i => W₁' i) (hW₁.comp Fin.val_injective)
        (hW₁'.comp Fin.val_injective)
      obtain ⟨e₂, he₂⟩ := exists_equiv_comp_eq (T := ℕ) (ι := Fin (n + 1))
        (a := fun i => W₂ i) (b := fun i => W₂' i) (hW₂.comp Fin.val_injective)
        (hW₂'.comp Fin.val_injective)
      have h := (hexch e₁ e₂).comp
        (u := fun ξ : ℕ × ℕ → E => (fun p : κ n => ξ (W₁ p.1.1, W₂ p.1.2), ξ (W₁ 0, W₂ 0)))
        (by fun_prop)
      have t₁ : e₁ (W₁ 0) = W₁ 0 := (he₁ ⟨0, by omega⟩).trans h₁.symm
      have t₂ : e₂ (W₂ 0) = W₂ 0 := (he₂ ⟨0, by omega⟩).trans h₂.symm
      have hc : ∀ p : κ n, (e₁ (W₁ p.1.1), e₂ (W₂ p.1.2)) = (W₁' p.1.1, W₂' p.1.2) := fun p =>
        Prod.ext (he₁ ⟨p.1.1, by have := p.2.1; omega⟩) (he₂ ⟨p.1.2, by have := p.2.2.1; omega⟩)
      simp only [Function.comp_def, hc, t₁, t₂] at h
      exact h.symm
  rw [hU W₁ W₂ hW₁ hW₂, hU W₁' W₂' hW₁' hW₂', ← h₁, ← h₂] at key
  exact key

/-- **The analogue of Lemma 1.6 for separately exchangeable arrays.**  Let `V₁, V₂` be infinite sets
of rows and columns containing `j` and `j'`, and let `C` be a set of cells which contains all the
cells of `V₁ × V₂` other than `(j, j')` but not `(j, j')` itself.  Then knowing the entries in `C`
is as good as knowing all the other entries for predicting `s (j, j')`:
`P[f (s (j, j')) | F_C] = P[f (s (j, j')) | F_{c ≠ (j, j')}]` almost surely, for every bounded
measurable `f`. -/
theorem condExp_comp_ae_eq_condExp_compl_of_separately_exchangeable [IsProbabilityMeasure P]
    [StandardBorelSpace E] [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {V₁ V₂ : Set ℕ} (hV₁ : V₁.Infinite) (hV₂ : V₂.Infinite) {j j' : ℕ} (hj : j ∈ V₁)
    (hj' : j' ∈ V₂) {C : Set (ℕ × ℕ)} (hC : {c | c ≠ (j, j') ∧ c.1 ∈ V₁ ∧ c.2 ∈ V₂} ⊆ C)
    (hC' : (j, j') ∉ C) {f : E → ℝ} (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    P[fun ω => f (s (j, j') ω) | ⨆ c ∈ C, mE.comap (s c)] =ᵐ[P]
      P[fun ω => f (s (j, j') ω) | ⨆ c ∈ ({(j, j')}ᶜ : Set (ℕ × ℕ)), mE.comap (s c)] := by
  obtain ⟨W₁, hW₁, hW₁r, h₁⟩ := exists_enum_of_infinite_first hV₁ hj
  obtain ⟨W₂, hW₂, hW₂r, h₂⟩ := exists_enum_of_infinite_first hV₂ hj'
  obtain ⟨W₁', hW₁', hW₁'r, h₁'⟩ := exists_enum_of_infinite_first infinite_univ (mem_univ j)
  obtain ⟨W₂', hW₂', hW₂'r, h₂'⟩ := exists_enum_of_infinite_first infinite_univ (mem_univ j')
  have key := condExp_cells_ae_eq hs hexch hW₁ hW₂ hW₁' hW₂' (h₁.trans h₁'.symm)
    (h₂.trans h₂'.symm) (by rw [hW₁'r]; exact subset_univ _) (by rw [hW₂'r]; exact subset_univ _)
    hf hfb
  rw [h₁, h₂, hW₁r, hW₂r, hW₁'r, hW₂'r] at key
  have hm₃ : (⨆ c ∈ ({(j, j')}ᶜ : Set (ℕ × ℕ)), mE.comap (s c)) ≤ mΩ :=
    iSup₂_le fun c _ => (hs c).comap_le
  refine condExp_ae_eq_of_le_of_le (biSup_mono hC) (biSup_mono fun c hc hct => hC' (hct ▸ hc)) hm₃
    ?_
  simpa [mem_univ] using key

end Lemma16

section Decoupling

/-- **The analogue of Eq. (1.94) for separately exchangeable arrays.**  Let `K` be a set of cells
and `l i ∉ K` distinct cells such that each `l i` is a corner `(j, j')` of a rectangle `V₁ × V₂`
with infinite sides all of whose other cells lie in `K`.  Then the entries `s (l i)` are
conditionally independent given `F_K = σ(s c : c ∈ K)`:
`P[∏ f i (s (l i)) | F_K] = ∏ P[f i (s (l i)) | F_K]` almost surely, for bounded measurable
`f i`. -/
theorem condExp_prod_comp_eq_prod_condExp_of_separately_exchangeable [IsProbabilityMeasure P]
    [StandardBorelSpace E] [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {K : Set (ℕ × ℕ)} {ι : Type*} (t : Finset ι) (l : ι → ℕ × ℕ) (hl : InjOn l t)
    (hlK : ∀ i ∈ t, l i ∉ K)
    (hrich : ∀ i ∈ t, ∃ V₁ V₂ : Set ℕ, V₁.Infinite ∧ V₂.Infinite ∧ (l i).1 ∈ V₁ ∧
      (l i).2 ∈ V₂ ∧ {c | c ≠ l i ∧ c.1 ∈ V₁ ∧ c.2 ∈ V₂} ⊆ K)
    (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i)) (hfb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C) :
    P[fun ω => ∏ i ∈ t, f i (s (l i) ω) | ⨆ c ∈ K, mE.comap (s c)] =ᵐ[P]
      fun ω => ∏ i ∈ t, P[fun ω' => f i (s (l i) ω') | ⨆ c ∈ K, mE.comap (s c)] ω := by
  refine condExp_finset_prod_comp_eq_prod_condExp hs K t l hl hlK f hf hfb
    fun i hi K' hKK' hn => ?_
  obtain ⟨V₁, V₂, hV₁, hV₂, hj, hj', hVK⟩ := hrich i hi
  have hiK := hlK i hi
  have key := fun {C : Set (ℕ × ℕ)} (hC : {c | c ≠ l i ∧ c.1 ∈ V₁ ∧ c.2 ∈ V₂} ⊆ C)
    (hC' : l i ∉ C) => condExp_comp_ae_eq_condExp_compl_of_separately_exchangeable (j := (l i).1)
      (j' := (l i).2) hs hexch hV₁ hV₂ hj hj' (by simpa using hC) (by simpa using hC') (hf i)
      (hfb i)
  exact (key (hVK.trans hKK') hn).trans (key hVK hiK).symm

end Decoupling

section VertexData

/-- An injection of the odd numbers `2 a + 1` extends to an injection of `ℕ` fixing the even
numbers. -/
theorem exists_injective_fix_even {ι : ℕ → ℕ} (hι : Injective ι) :
    ∃ j : ℕ → ℕ, Injective j ∧ (∀ m, j (2 * m) = 2 * m) ∧ ∀ a, j (2 * a + 1) = 2 * ι a + 1 := by
  refine ⟨fun x => if x % 2 = 0 then x else 2 * ι (x / 2) + 1, fun x y h => ?_, fun m => ?_,
    fun a => ?_⟩
  · by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0 <;> simp only [hx, hy, ite_true,
      ite_false] at h
    · exact h
    · omega
    · omega
    · have := hι (by omega : ι (x / 2) = ι (y / 2))
      omega
  · simp
  · have h1 : (2 * a + 1) % 2 ≠ 0 := by omega
    have h2 : (2 * a + 1) / 2 = a := by omega
    simp only [h1, h2, ite_false]

/-- **Exchangeability of the vertex data.**  Let `S a` be the sub-array of the row `2 a + 1` with
the even columns together with the block of even rows and columns (the row vertex array),
`T b` the same for the column `2 b + 1`, and `Q (a, b)` the entry at the odd row `2 a + 1` and the
odd column `2 b + 1`.  Along injections `ι₁, ι₂` of the odd rows and columns the family
`(S, T, Q)` has the same law. -/
theorem identDistrib_vertexData_comp_inj [IsFiniteMeasure P] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S T : ℕ → Ω → ℕ × ℕ → E} (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω)
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) {Q : ℕ × ℕ → Ω → E}
    (hQ : ∀ c ω, Q c ω = s (2 * c.1 + 1, 2 * c.2 + 1) ω) {ι₁ ι₂ : ℕ → ℕ} (h₁ : Injective ι₁)
    (h₂ : Injective ι₂) :
    IdentDistrib
      (fun ω => ((fun a => S (ι₁ a) ω, fun b => T (ι₂ b) ω), fun c : ℕ × ℕ => Q (ι₁ c.1, ι₂ c.2) ω))
      (fun ω => ((fun a => S a ω, fun b => T b ω), fun c => Q c ω)) P P := by
  obtain ⟨j₁, hj₁, hj₁e, hj₁o⟩ := exists_injective_fix_even h₁
  obtain ⟨j₂, hj₂, hj₂e, hj₂o⟩ := exists_injective_fix_even h₂
  have hκ : ∀ (j : ℕ → ℕ) (ι : ℕ → ℕ), (∀ m, j (2 * m) = 2 * m) →
      (∀ a, j (2 * a + 1) = 2 * ι a + 1) → ∀ a n, j (κ a n) = κ (ι a) n := fun j ι he ho a n => by
    cases n <;> simp [hκ0, hκ1, he, ho]
  have hu : Measurable fun ξ : ℕ × ℕ → E =>
      ((fun (a : ℕ) (p : ℕ × ℕ) => ξ (κ a p.1, 2 * p.2),
        fun (b : ℕ) (p : ℕ × ℕ) => ξ (2 * p.1, κ b p.2)),
        fun c : ℕ × ℕ => ξ (2 * c.1 + 1, 2 * c.2 + 1)) :=
    ((measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun p => measurable_pi_apply _).prodMk
      (measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun p => measurable_pi_apply _)).prodMk
      (measurable_pi_iff.2 fun c => measurable_pi_apply _)
  have h := (identDistrib_map_of_separately_exchangeable hs hexch hj₁ hj₂).comp hu
  have hS' : ∀ a ω, S a ω = fun p => s (κ a p.1, 2 * p.2) ω := fun a ω => funext (hS a ω)
  have hT' : ∀ b ω, T b ω = fun p => s (2 * p.1, κ b p.2) ω := fun b ω => funext (hT b ω)
  have hQ' : ∀ c ω, Q c ω = s (2 * c.1 + 1, 2 * c.2 + 1) ω := hQ
  simp only [Function.comp_def, hκ j₁ ι₁ hj₁e hj₁o, hκ j₂ ι₂ hj₂e hj₂o, hj₁e, hj₂e, hj₁o,
    hj₂o, hS', hT', hQ'] at h ⊢
  exact h

/-- The vertex data of one odd row and one odd column behave like the first ones:
`(S a, T b, Q (a, b))` has the same law as `(S 0, T 0, Q (0, 0))`. -/
theorem identDistrib_rowColPair [IsFiniteMeasure P] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S T : ℕ → Ω → ℕ × ℕ → E} (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω)
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) {Q : ℕ × ℕ → Ω → E}
    (hQ : ∀ c ω, Q c ω = s (2 * c.1 + 1, 2 * c.2 + 1) ω) (a b : ℕ) :
    IdentDistrib (fun ω => ((S a ω, T b ω), Q (a, b) ω))
      (fun ω => ((S 0 ω, T 0 ω), Q (0, 0) ω)) P P := by
  have h := (identDistrib_vertexData_comp_inj hs hexch hκ0 hκ1 hS hT hQ
    (Equiv.swap 0 a).injective (Equiv.swap 0 b).injective).comp
    (u := fun x : ((ℕ → ℕ × ℕ → E) × (ℕ → ℕ × ℕ → E)) × (ℕ × ℕ → E) =>
      ((x.1.1 0, x.1.2 0), x.2 (0, 0))) (by fun_prop)
  simpa [Function.comp_def, Equiv.swap_apply_left] using h

/-- A row vertex array is measurable. -/
theorem measurable_rowData {κ : ℕ → ℕ → ℕ} {S : ℕ → Ω → ℕ × ℕ → E} (hs : ∀ c, Measurable (s c))
    (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω) (a : ℕ) : Measurable (S a) := by
  rw [show S a = fun ω p => s (κ a p.1, 2 * p.2) ω from funext fun ω => funext (hS a ω)]
  exact measurable_pi_iff.2 fun p => hs _

/-- A column vertex array is measurable. -/
theorem measurable_colData {κ : ℕ → ℕ → ℕ} {T : ℕ → Ω → ℕ × ℕ → E} (hs : ∀ c, Measurable (s c))
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) (b : ℕ) : Measurable (T b) := by
  rw [show T b = fun ω p => s (2 * p.1, κ b p.2) ω from funext fun ω => funext (hT b ω)]
  exact measurable_pi_iff.2 fun p => hs _

/-- An entry at an odd row and an odd column is measurable. -/
theorem measurable_oddEntry {Q : ℕ × ℕ → Ω → E} (hs : ∀ c, Measurable (s c))
    (hQ : ∀ c ω, Q c ω = s (2 * c.1 + 1, 2 * c.2 + 1) ω) (c : ℕ × ℕ) : Measurable (Q c) := by
  rw [show Q c = s (2 * c.1 + 1, 2 * c.2 + 1) from funext (hQ c)]
  exact hs _

/-- The cells of the row vertex array `S a`. -/
theorem range_vertexRow {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) (a : ℕ) :
    range (fun p : ℕ × ℕ => (κ a p.1, 2 * p.2)) =
      {c | (c.1 % 2 = 0 ∨ c.1 = 2 * a + 1) ∧ c.2 % 2 = 0} := by
  have : (fun p : ℕ × ℕ => (κ a p.1, 2 * p.2)) = Prod.map (κ a) (fun m => 2 * m) := rfl
  rw [this, range_prodMap]
  ext ⟨x, y⟩
  simp only [mem_prod, mem_ofPred_eq, mem_range_vertexMap hκ0 hκ1]
  exact and_congr_right fun _ => ⟨fun ⟨m, hm⟩ => by have : 2 * m = y := hm; omega,
    fun h => ⟨y / 2, show 2 * (y / 2) = y by omega⟩⟩

/-- The cells of the column vertex array `T b`. -/
theorem range_vertexCol {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) (b : ℕ) :
    range (fun p : ℕ × ℕ => (2 * p.1, κ b p.2)) =
      {c | c.1 % 2 = 0 ∧ (c.2 % 2 = 0 ∨ c.2 = 2 * b + 1)} := by
  have : (fun p : ℕ × ℕ => (2 * p.1, κ b p.2)) = Prod.map (fun m => 2 * m) (κ b) := rfl
  rw [this, range_prodMap]
  ext ⟨x, y⟩
  simp only [mem_prod, mem_ofPred_eq, mem_range_vertexMap hκ0 hκ1]
  exact and_congr_left fun _ => ⟨fun ⟨m, hm⟩ => by have : 2 * m = x := hm; omega,
    fun h => ⟨x / 2, show 2 * (x / 2) = x by omega⟩⟩

/-- The σ-algebra of a row vertex array is generated by its cells. -/
theorem comap_rowData {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) {S : ℕ → Ω → ℕ × ℕ → E}
    (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω) (a : ℕ) :
    MeasurableSpace.pi.comap (S a) =
      ⨆ c ∈ {c : ℕ × ℕ | (c.1 % 2 = 0 ∨ c.1 = 2 * a + 1) ∧ c.2 % 2 = 0}, mE.comap (s c) := by
  rw [← range_vertexRow hκ0 hκ1,
    show S a = fun ω p => s ((fun p : ℕ × ℕ => (κ a p.1, 2 * p.2)) p) ω from
      funext fun ω => funext (hS a ω)]
  exact MeasurableSpace.comap_pi_range _ s

/-- The σ-algebra of a column vertex array is generated by its cells. -/
theorem comap_colData {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) {T : ℕ → Ω → ℕ × ℕ → E}
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) (b : ℕ) :
    MeasurableSpace.pi.comap (T b) =
      ⨆ c ∈ {c : ℕ × ℕ | c.1 % 2 = 0 ∧ (c.2 % 2 = 0 ∨ c.2 = 2 * b + 1)}, mE.comap (s c) := by
  rw [← range_vertexCol hκ0 hκ1,
    show T b = fun ω p => s ((fun p : ℕ × ℕ => (2 * p.1, κ b p.2)) p) ω from
      funext fun ω => funext (hT b ω)]
  exact MeasurableSpace.comap_pi_range _ s

/-- The σ-algebra generated by a row vertex array and a column vertex array is generated by their
cells. -/
theorem comap_rowColPair {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) {S T : ℕ → Ω → ℕ × ℕ → E}
    (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω)
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) (a b : ℕ) :
    MeasurableSpace.comap (fun ω => (S a ω, T b ω)) inferInstance =
      ⨆ c ∈ {c : ℕ × ℕ | (c.1 % 2 = 0 ∨ c.1 = 2 * a + 1) ∧ c.2 % 2 = 0} ∪
        {c | c.1 % 2 = 0 ∧ (c.2 % 2 = 0 ∨ c.2 = 2 * b + 1)}, mE.comap (s c) := by
  refine (MeasurableSpace.comap_prodMk (S a) (T b)).trans ?_
  rw [iSup_union, comap_rowData hκ0 hκ1 hS a, comap_colData hκ0 hκ1 hT b]

/-- The σ-algebra generated by all the vertex arrays is generated by the cells with an even row
or an even column. -/
theorem comap_rowColData {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) {S T : ℕ → Ω → ℕ × ℕ → E}
    (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω)
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) :
    MeasurableSpace.comap (fun ω => (fun a => S a ω, fun b => T b ω)) inferInstance =
      ⨆ c ∈ {c : ℕ × ℕ | c.2 % 2 = 0} ∪ {c | c.1 % 2 = 0}, mE.comap (s c) := by
  have hrow : (⋃ a, {c : ℕ × ℕ | (c.1 % 2 = 0 ∨ c.1 = 2 * a + 1) ∧ c.2 % 2 = 0}) =
      {c | c.2 % 2 = 0} := by
    ext ⟨x, y⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨a, ha⟩ := mem_iUnion.1 h
      exact ha.2
    · exact mem_iUnion.2 ⟨x / 2, by simp only [mem_ofPred_eq] at h ⊢; omega⟩
  have hcol : (⋃ b, {c : ℕ × ℕ | c.1 % 2 = 0 ∧ (c.2 % 2 = 0 ∨ c.2 = 2 * b + 1)}) =
      {c | c.1 % 2 = 0} := by
    ext ⟨x, y⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨b, hb⟩ := mem_iUnion.1 h
      exact hb.1
    · exact mem_iUnion.2 ⟨y / 2, by simp only [mem_ofPred_eq] at h ⊢; omega⟩
  refine (MeasurableSpace.comap_prodMk (fun ω a => S a ω) (fun ω b => T b ω)).trans ?_
  rw [iSup_union, ← hrow, ← hcol, iSup_iUnion, iSup_iUnion, MeasurableSpace.comap_pi,
    MeasurableSpace.comap_pi]
  exact congrArg₂ _ (iSup_congr fun a => comap_rowData hκ0 hκ1 hS a)
    (iSup_congr fun b => comap_colData hκ0 hκ1 hT b)

/-- The even numbers together with one odd number form an infinite set. -/
theorem infinite_vertexSet_sep (a : ℕ) : Set.Infinite {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1} :=
  (infinite_range_of_injective (f := fun m : ℕ => 2 * m) fun m n h => by
    simpa using h).mono fun x hx => by
      obtain ⟨m, hm⟩ := hx
      have : 2 * m = x := hm
      exact Or.inl (by omega)

/-- **The cells revealed by the vertex arrays.**  The cell `(2 a + 1, 2 b + 1)` is revealed neither
by all the vertex arrays nor by `S a` and `T b`, while the other cells of the rectangle spanned by
`{2 a + 1}` ∪ evens and `{2 b + 1}` ∪ evens are revealed by `S a` and `T b`, hence by all of
them. -/
theorem cells_rowColData (a b : ℕ) :
    ((2 * a + 1, 2 * b + 1) ∉ {c : ℕ × ℕ | c.2 % 2 = 0} ∪ {c | c.1 % 2 = 0} ∧
      {c | c ≠ (2 * a + 1, 2 * b + 1) ∧ c.1 ∈ {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1} ∧
        c.2 ∈ {y : ℕ | y % 2 = 0 ∨ y = 2 * b + 1}} ⊆
        {c : ℕ × ℕ | c.2 % 2 = 0} ∪ {c | c.1 % 2 = 0}) ∧
    ((2 * a + 1, 2 * b + 1) ∉ {c : ℕ × ℕ | (c.1 % 2 = 0 ∨ c.1 = 2 * a + 1) ∧ c.2 % 2 = 0} ∪
        {c | c.1 % 2 = 0 ∧ (c.2 % 2 = 0 ∨ c.2 = 2 * b + 1)} ∧
      {c | c ≠ (2 * a + 1, 2 * b + 1) ∧ c.1 ∈ {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1} ∧
        c.2 ∈ {y : ℕ | y % 2 = 0 ∨ y = 2 * b + 1}} ⊆
        {c : ℕ × ℕ | (c.1 % 2 = 0 ∨ c.1 = 2 * a + 1) ∧ c.2 % 2 = 0} ∪
          {c | c.1 % 2 = 0 ∧ (c.2 % 2 = 0 ∨ c.2 = 2 * b + 1)}) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [mem_union, mem_ofPred_eq]
    omega
  · rintro ⟨x, y⟩ ⟨hne, hx, hy⟩
    have : ¬(x = 2 * a + 1 ∧ y = 2 * b + 1) := fun h => hne (by rw [h.1, h.2])
    simp only [mem_union, mem_ofPred_eq] at hx hy ⊢
    omega
  · simp only [mem_union, mem_ofPred_eq]
    omega
  · rintro ⟨x, y⟩ ⟨hne, hx, hy⟩
    have : ¬(x = 2 * a + 1 ∧ y = 2 * b + 1) := fun h => hne (by rw [h.1, h.2])
    simp only [mem_union, mem_ofPred_eq] at hx hy ⊢
    omega

/-- **The entry of an odd row and an odd column, given all the vertex arrays.**  The conditional
law of the entry `(2 a + 1, 2 b + 1)` given all the vertex arrays depends only on `(S a, T b)`,
through the same kernel `ν` for every pair `(a, b)` (second half of the analogue of
Eq. (1.94)). -/
theorem condExp_rowColData_ae_eq_integral [IsProbabilityMeasure P] [StandardBorelSpace E]
    [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S T : ℕ → Ω → ℕ × ℕ → E} (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω)
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) {Q : ℕ × ℕ → Ω → E}
    (hQ : ∀ c ω, Q c ω = s (2 * c.1 + 1, 2 * c.2 + 1) ω)
    {ν : Kernel ((ℕ × ℕ → E) × (ℕ × ℕ → E)) E}
    (hν : ν = condDistrib (Q (0, 0)) (fun ω => (S 0 ω, T 0 ω)) P) (a b : ℕ) {g : E → ℝ}
    (hg : Measurable g) (hgb : ∃ C, ∀ x, |g x| ≤ C) :
    P[fun ω => g (Q (a, b) ω) |
        MeasurableSpace.comap (fun ω => (fun a => S a ω, fun b => T b ω)) inferInstance] =ᵐ[P]
      fun ω => ∫ y, g y ∂ν (S a ω, T b ω) := by
  have hSm : ∀ a, Measurable (S a) := measurable_rowData hs hS
  have hTm : ∀ b, Measurable (T b) := measurable_colData hs hT
  have hQab : Q (a, b) = s (2 * a + 1, 2 * b + 1) := funext (hQ _)
  have hQm : Measurable (Q (a, b)) := by rw [hQab]; exact hs _
  obtain ⟨C, hC⟩ := hgb
  have hint : Integrable (fun ω => g (Q (a, b) ω)) P :=
    Integrable.of_bound (hg.comp hQm).aestronglyMeasurable C
      (.of_forall fun ω => by simpa using hC _)
  obtain ⟨⟨hn₁, hsub₁⟩, ⟨hn₂, hsub₂⟩⟩ := cells_rowColData a b
  have key : ∀ D : Set (ℕ × ℕ),
      {c | c ≠ (2 * a + 1, 2 * b + 1) ∧ c.1 ∈ {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1} ∧
        c.2 ∈ {y : ℕ | y % 2 = 0 ∨ y = 2 * b + 1}} ⊆ D → (2 * a + 1, 2 * b + 1) ∉ D →
      P[fun ω => g (s (2 * a + 1, 2 * b + 1) ω) | ⨆ c ∈ D, mE.comap (s c)] =ᵐ[P]
        P[fun ω => g (s (2 * a + 1, 2 * b + 1) ω) |
          ⨆ c ∈ ({(2 * a + 1, 2 * b + 1)}ᶜ : Set (ℕ × ℕ)), mE.comap (s c)] :=
    fun D hD hD' => condExp_comp_ae_eq_condExp_compl_of_separately_exchangeable hs hexch
      (infinite_vertexSet_sep a) (infinite_vertexSet_sep b) (Or.inr rfl) (Or.inr rfl) hD hD' hg
      ⟨C, hC⟩
  have h1 := (key _ hsub₁ hn₁).trans (key _ hsub₂ hn₂).symm
  have h2 : P[fun ω => g (s (2 * a + 1, 2 * b + 1) ω) |
      ⨆ c ∈ {c : ℕ × ℕ | (c.1 % 2 = 0 ∨ c.1 = 2 * a + 1) ∧ c.2 % 2 = 0} ∪
        {c | c.1 % 2 = 0 ∧ (c.2 % 2 = 0 ∨ c.2 = 2 * b + 1)}, mE.comap (s c)] =ᵐ[P]
      fun ω => ∫ y, g y ∂condDistrib (Q (a, b)) (fun ω => (S a ω, T b ω)) P (S a ω, T b ω) := by
    rw [← comap_rowColPair hκ0 hκ1 hS hT a b, ← hQab]
    exact condExp_ae_eq_integral_condDistrib ((hSm a).prodMk (hTm b)) hQm.aemeasurable
      hg.stronglyMeasurable hint
  have h3 : condDistrib (Q (a, b)) (fun ω => (S a ω, T b ω)) P = ν := by
    rw [hν]
    exact condDistrib_eq_of_map_eq (identDistrib_rowColPair hs hexch hκ0 hκ1 hS hT hQ a b).map_eq
  rw [h3] at h2
  rw [hQab, comap_rowColData hκ0 hκ1 hS hT]
  exact h1.trans h2

/-- **The analogue of Eq. (1.94) for the vertex arrays.**  Given all the row vertex arrays `S` and
column vertex arrays `T`, the entries `Q (a, b)` at the odd rows and columns are independent, and
the entry `(a, b)` has the law `ν (S a, T b)`: the joint law of `((S, T), Q)` is
`P.map (S, T) ⊗ₘ K`, where `K (x, y)` is the product over the cells `(a, b)` of `ν (x a, y b)`. -/
theorem map_rowColData_eq_compProd [IsProbabilityMeasure P] [StandardBorelSpace E] [Nonempty E]
    (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P)
    {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S T : ℕ → Ω → ℕ × ℕ → E} (hS : ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω)
    (hT : ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω) {Q : ℕ × ℕ → Ω → E}
    (hQ : ∀ c ω, Q c ω = s (2 * c.1 + 1, 2 * c.2 + 1) ω)
    {ν : Kernel ((ℕ × ℕ → E) × (ℕ × ℕ → E)) E}
    (hν : ν = condDistrib (Q (0, 0)) (fun ω => (S 0 ω, T 0 ω)) P)
    (K : Kernel ((ℕ → ℕ × ℕ → E) × (ℕ → ℕ × ℕ → E)) (ℕ × ℕ → E)) [IsMarkovKernel K]
    (hK : ∀ x, K x = Measure.infinitePi fun c : ℕ × ℕ => ν (x.1 c.1, x.2 c.2)) :
    P.map (fun ω => ((fun a => S a ω, fun b => T b ω), fun c : ℕ × ℕ => Q c ω)) =
      (P.map fun ω => (fun a => S a ω, fun b => T b ω)) ⊗ₘ K := by
  have hSm : ∀ a, Measurable (S a) := measurable_rowData hs hS
  have hTm : ∀ b, Measurable (T b) := measurable_colData hs hT
  have hQm : ∀ c, Measurable (Q c) := measurable_oddEntry hs hQ
  have : IsMarkovKernel ν := by rw [hν]; infer_instance
  refine map_prodMk_eq_compProd_infinitePi
    (fun c : ℕ × ℕ => ν.comap (fun x : (ℕ → ℕ × ℕ → E) × (ℕ → ℕ × ℕ → E) => (x.1 c.1, x.2 c.2))
      (((measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply _).comp measurable_snd))) K hK
    ((measurable_pi_iff.2 hSm).prodMk (measurable_pi_iff.2 hTm)) hQm
    (fun c g hg hgb => ?_) (fun t f hf hfb => ?_)
  · exact condExp_rowColData_ae_eq_integral hs hexch hκ0 hκ1 hS hT hQ hν c.1 c.2 hg hgb
  · rw [comap_rowColData hκ0 hκ1 hS hT]
    simp only [hQ]
    refine condExp_prod_comp_eq_prod_condExp_of_separately_exchangeable hs hexch t
      (fun c : ℕ × ℕ => (2 * c.1 + 1, 2 * c.2 + 1)) ?_ ?_ ?_ f hf hfb
    · exact fun c _ d _ h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (by omega) (by omega)
    · intro c _
      simp only [mem_union, mem_ofPred_eq]
      omega
    · intro c _
      exact ⟨_, _, infinite_vertexSet_sep c.1, infinite_vertexSet_sep c.2, Or.inr rfl, Or.inr rfl,
        (cells_rowColData c.1 c.2).1.2⟩

end VertexData

section Representation

/-- **The law of the vertex data from de Finetti's theorem.**  Let `(S a)` and `(T b)` be sequences
such that the sequence of pairs `(S k, T k)` is represented by `G (w, u_k)` (de Finetti) and such
that the sub-families `(S (2 a))_a`, `(T (2 b + 1))_b` have the law of `((S a)_a, (T b)_b)`.  Then
`((S a)_a, (T b)_b)` has the law of `((X (w, u_a))_a, (Y (w, v_b))_b)`, where `G = (X, Y)` and
`w, (u_a), (v_b)` are independent and uniform: the row and column vertex variables are driven by
independent noise (the two sub-sequences use disjoint sets of the i.i.d. variables). -/
theorem map_rowColData_eq_coded {F : Type*} [MeasurableSpace F] {S T : ℕ → Ω → F}
    (hS : ∀ a, Measurable (S a)) (hT : ∀ b, Measurable (T b)) {G : I × I → F × F}
    (hG : Measurable G)
    (hinj : IdentDistrib (fun ω => (fun a => S (2 * a) ω, fun b => T (2 * b + 1) ω))
      (fun ω => (fun a => S a ω, fun b => T b ω)) P P)
    (hid : IdentDistrib (fun ω k => (S k ω, T k ω)) (fun (p : I × (ℕ → I)) k => G (p.1, p.2 k))
      P ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))) :
    P.map (fun ω => (fun a => S a ω, fun b => T b ω)) =
      ((volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
        (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))).map
        (fun q => (fun a => (G (q.1, q.2.1 a)).1, fun b => (G (q.1, q.2.2 b)).2)) := by
  have hφ : Measurable fun z : ℕ → F × F => (fun a => (z (2 * a)).1, fun b => (z (2 * b + 1)).2) :=
    (measurable_pi_iff.2 fun a => measurable_fst.comp (measurable_pi_apply _)).prodMk
      (measurable_pi_iff.2 fun b => measurable_snd.comp (measurable_pi_apply _))
  have hΘ : Measurable fun q : I × ((ℕ → I) × (ℕ → I)) =>
      (fun a => (G (q.1, q.2.1 a)).1, fun b => (G (q.1, q.2.2 b)).2) :=
    (measurable_pi_iff.2 fun a => measurable_fst.comp (hG.comp (measurable_fst.prodMk
      ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd))))).prodMk
      (measurable_pi_iff.2 fun b => measurable_snd.comp (hG.comp (measurable_fst.prodMk
      ((measurable_pi_apply b).comp (measurable_snd.comp measurable_snd)))))
  have hsplit := Measure.map_prod_infinitePi_pair_of_disjoint (volume : Measure I)
    (volume : Measure I) (f := fun a : ℕ => 2 * a) (g := fun b : ℕ => 2 * b + 1)
    (fun a b h => by simpa using h) (fun a b h => by simpa using h)
    (Set.disjoint_left.2 fun x ⟨a, ha⟩ ⟨b, hb⟩ => by
      have h1 : 2 * a = x := ha
      have h2 : 2 * b + 1 = x := hb
      omega)
  have hsm : Measurable fun p : I × (ℕ → I) =>
      (p.1, (fun a => p.2 (2 * a), fun b => p.2 (2 * b + 1))) :=
    measurable_fst.prodMk ((measurable_pi_iff.2 fun a => (measurable_pi_apply _).comp
      measurable_snd).prodMk (measurable_pi_iff.2 fun b => (measurable_pi_apply _).comp
      measurable_snd))
  calc P.map (fun ω => (fun a => S a ω, fun b => T b ω))
      = P.map (fun ω => (fun a => S (2 * a) ω, fun b => T (2 * b + 1) ω)) := hinj.map_eq.symm
    _ = (P.map (fun ω k => (S k ω, T k ω))).map
          (fun z : ℕ → F × F => (fun a => (z (2 * a)).1, fun b => (z (2 * b + 1)).2)) :=
        (Measure.map_map hφ (measurable_pi_iff.2 fun k => (hS k).prodMk (hT k))).symm
    _ = (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (fun (p : I × (ℕ → I)) k => G (p.1, p.2 k))).map
          (fun z : ℕ → F × F => (fun a => (z (2 * a)).1, fun b => (z (2 * b + 1)).2)) := by
        rw [hid.map_eq]
    _ = (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (fun p : I × (ℕ → I) => (p.1, (fun a => p.2 (2 * a), fun b => p.2 (2 * b + 1))))).map
          (fun q : I × ((ℕ → I) × (ℕ → I)) =>
            (fun a => (G (q.1, q.2.1 a)).1, fun b => (G (q.1, q.2.2 b)).2)) := by
        rw [Measure.map_map hφ (Measure.measurable_pi_curry hG), Measure.map_map hΘ hsm]
        rfl
    _ = _ := by rw [hsplit]


/-- **Aldous–Hoover representation of separately exchangeable arrays** [Panchenko, 2013,
Theorem 1.4, Eq. (1.77)].  A separately exchangeable array with values in a standard Borel space
is, in law, `τ (w, u_l, v_{l'}, x_{l, l'})` for a measurable `τ`, where `w`, `(u_l)`, `(v_{l'})`,
`(x_{l, l'})` are independent and uniform on `[0, 1]`.

The proof follows the book.  The row vertex arrays `S_a` and the column vertex arrays `T_b` (the
entries of the odd row `2 a + 1`, resp. odd column `2 b + 1`, against the even columns, resp. rows,
together with the block of even rows and columns) are such that the pairs `(S_k, T_k)` form an
exchangeable sequence, hence are coded by de Finetti's theorem.  Along the even, resp. odd, indices
the rows and the columns use disjoint sets of the i.i.d. variables (`map_rowColData_eq_coded`);
this is what makes the row noise `(u_a)` and the column noise `(v_b)` independent.  Given all the
vertex arrays, the entries on the odd rows and columns are conditionally independent with a law
depending only on the two adjacent vertex arrays (`map_rowColData_eq_compProd`), and the kernel is
coded by a uniform variable.  The array on the odd rows and columns has the law of the whole array
(`identDistrib_map_of_separately_exchangeable`). -/
theorem exists_aldousHoover_representation_separately [IsProbabilityMeasure P]
    [StandardBorelSpace E] [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e₁ e₂ : ℕ ≃ ℕ,
      IdentDistrib (fun ω (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) ω) (fun ω p => s p ω) P P) :
    ∃ τ : I × I × I × I → E, Measurable τ ∧
      IdentDistrib (fun ω (p : ℕ × ℕ) => s p ω)
        (fun (η : (I × ((ℕ → I) × (ℕ → I))) × (ℕ × ℕ → I)) (p : ℕ × ℕ) =>
          τ (η.1.1, η.1.2.1 p.1, η.1.2.2 p.2, η.2 p)) P
        (((volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
          (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))).prod
          (Measure.infinitePi fun _ : ℕ × ℕ => (volume : Measure I))) := by
  classical
  obtain ⟨κ, hκ0, hκ1⟩ : ∃ κ : ℕ → ℕ → ℕ, (∀ a, κ a 0 = 2 * a + 1) ∧ ∀ a m, κ a (m + 1) = 2 * m :=
    ⟨fun a n => Nat.casesOn n (2 * a + 1) fun m => 2 * m, fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Ω → ℕ × ℕ → E, ∀ a ω p, S a ω p = s (κ a p.1, 2 * p.2) ω :=
    ⟨fun a ω p => s (κ a p.1, 2 * p.2) ω, fun _ _ _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Ω → ℕ × ℕ → E, ∀ b ω p, T b ω p = s (2 * p.1, κ b p.2) ω :=
    ⟨fun b ω p => s (2 * p.1, κ b p.2) ω, fun _ _ _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ × ℕ → Ω → E, ∀ c ω, Q c ω = s (2 * c.1 + 1, 2 * c.2 + 1) ω :=
    ⟨fun c ω => s (2 * c.1 + 1, 2 * c.2 + 1) ω, fun _ _ => rfl⟩
  have hSm : ∀ a, Measurable (S a) := measurable_rowData hs hS
  have hTm : ∀ b, Measurable (T b) := measurable_colData hs hT
  have hQm : ∀ c, Measurable (Q c) := measurable_oddEntry hs hQ
  have hinj : ∀ ι₁ ι₂ : ℕ → ℕ, Injective ι₁ → Injective ι₂ →
      IdentDistrib (fun ω => (fun a => S (ι₁ a) ω, fun b => T (ι₂ b) ω))
        (fun ω => (fun a => S a ω, fun b => T b ω)) P P := fun ι₁ ι₂ h₁ h₂ =>
    (identDistrib_vertexData_comp_inj hs hexch hκ0 hκ1 hS hT hQ h₁ h₂).comp measurable_fst
  have hZm : ∀ k, Measurable fun ω => (S k ω, T k ω) := fun k => (hSm k).prodMk (hTm k)
  -- de Finetti for the sequence of pairs of vertex arrays
  have hZexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω k => (S (e k) ω, T (e k) ω))
      (fun ω k => (S k ω, T k ω)) P P := fun e =>
    (hinj e e e.injective e.injective).comp
      (u := fun x : (ℕ → ℕ × ℕ → E) × (ℕ → ℕ × ℕ → E) => fun k => (x.1 k, x.2 k))
      (measurable_pi_iff.2 fun k => ((measurable_pi_apply k).comp measurable_fst).prodMk
        ((measurable_pi_apply k).comp measurable_snd))
  obtain ⟨G, hG, hid⟩ := exists_de_finetti_representation (s := fun k ω => (S k ω, T k ω)) hZm
    hZexch
  -- the kernel `ν` of an entry given the two adjacent vertex arrays, and its uniform coding `H`
  obtain ⟨ν, hν⟩ : ∃ ν : Kernel ((ℕ × ℕ → E) × (ℕ × ℕ → E)) E,
      ν = condDistrib (Q (0, 0)) (fun ω => (S 0 ω, T 0 ω)) P := ⟨_, rfl⟩
  have : IsMarkovKernel ν := by rw [hν]; infer_instance
  obtain ⟨H0, hHm, hH0ν⟩ := Kernel.exists_measurable_map_eq_unitInterval ν
  set H := uncurry H0 with hHdef
  have hHν : ∀ p, (volume : Measure I).map (fun y => H (p, y)) = ν p := hH0ν
  obtain ⟨τ, hσ⟩ : ∃ τ : I × I × I × I → E, ∀ w u v y,
      τ (w, u, v, y) = H (((G (w, u)).1, (G (w, v)).2), y) :=
    ⟨fun p => H (((G (p.1, p.2.1)).1, (G (p.1, p.2.2.1)).2), p.2.2.2), fun _ _ _ _ => rfl⟩
  have hσm : Measurable τ := by
    have : τ = fun p => H (((G (p.1, p.2.1)).1, (G (p.1, p.2.2.1)).2), p.2.2.2) :=
      funext fun p => hσ _ _ _ _
    rw [this]
    exact hHm.comp (((measurable_fst.comp (hG.comp (by fun_prop))).prodMk
      (measurable_snd.comp (hG.comp (by fun_prop)))).prodMk (by fun_prop))
  -- the kernel `K` of the odd entries given the vertex data
  let K : Kernel ((ℕ → ℕ × ℕ → E) × (ℕ → ℕ × ℕ → E)) (ℕ × ℕ → E) :=
    ⟨fun x => Measure.infinitePi fun c : ℕ × ℕ => ν (x.1 c.1, x.2 c.2),
      Measure.measurable_infinitePi fun c => ν.measurable.comp
        (((measurable_pi_apply _).comp measurable_fst).prodMk
          ((measurable_pi_apply _).comp measurable_snd))⟩
  have : IsMarkovKernel K := ⟨fun x => inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun c : ℕ × ℕ => ν (x.1 c.1, x.2 c.2)))⟩
  have hP := map_rowColData_eq_compProd hs hexch hκ0 hκ1 hS hT hQ hν K fun _ => rfl
  have hΛ := map_rowColData_eq_coded hSm hTm hG
    (hinj (fun a => 2 * a) (fun b => 2 * b + 1) (fun a b h => by simpa using h)
      fun a b h => by simpa using h) hid
  -- the coded array
  set Q0 := (volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
    (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) with hQ0
  set Θ : I × ((ℕ → I) × (ℕ → I)) → (ℕ → ℕ × ℕ → E) × (ℕ → ℕ × ℕ → E) := fun q =>
    (fun a => (G (q.1, q.2.1 a)).1, fun b => (G (q.1, q.2.2 b)).2) with hΘdef
  have hΘ : Measurable Θ :=
    (measurable_pi_iff.2 fun a => measurable_fst.comp (hG.comp (measurable_fst.prodMk
      ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd))))).prodMk
      (measurable_pi_iff.2 fun b => measurable_snd.comp (hG.comp (measurable_fst.prodMk
      ((measurable_pi_apply b).comp (measurable_snd.comp measurable_snd)))))
  set g : ℕ × ℕ → (I × ((ℕ → I) × (ℕ → I))) × I → E := fun c r =>
    τ (r.1.1, r.1.2.1 c.1, r.1.2.2 c.2, r.2) with hg
  have hgm : ∀ c, Measurable (g c) := fun c => hσm.comp (by fun_prop)
  have hcoded := map_codedCells_eq_compProd (μ := Q0) (ν := (volume : Measure I)) Θ hΘ g hgm K
    (Filter.Eventually.of_forall fun q => by
      change _ = Measure.infinitePi fun c : ℕ × ℕ => ν ((Θ q).1 c.1, (Θ q).2 c.2)
      exact congrArg Measure.infinitePi (funext fun c => by simp only [hg, hσ]; exact hHν _))
  have hjoint := hP.trans ((congrArg (· ⊗ₘ K) hΛ).trans hcoded.symm)
  have hpair : Measurable fun ω =>
      ((fun a => S a ω, fun b => T b ω), fun c : ℕ × ℕ => Q c ω) :=
    ((measurable_pi_iff.2 hSm).prodMk (measurable_pi_iff.2 hTm)).prodMk
      (measurable_pi_iff.2 hQm)
  have hcm : Measurable fun r : (I × ((ℕ → I) × (ℕ → I))) × (ℕ × ℕ → I) =>
      (Θ r.1, fun c : ℕ × ℕ => g c (r.1, r.2 c)) :=
    (hΘ.comp measurable_fst).prodMk (measurable_pi_iff.2 fun c => (hgm c).comp
      (measurable_fst.prodMk ((measurable_pi_apply c).comp measurable_snd)))
  have hQlaw : P.map (fun ω (c : ℕ × ℕ) => Q c ω) =
      (Q0.prod (Measure.infinitePi fun _ : ℕ × ℕ => (volume : Measure I))).map
        (fun r => fun c : ℕ × ℕ => g c (r.1, r.2 c)) := by
    have := congrArg (Measure.map Prod.snd) hjoint
    rw [Measure.map_map measurable_snd hpair, Measure.map_map measurable_snd hcm] at this
    exact this
  have hodd := (identDistrib_map_of_separately_exchangeable hs hexch
    (ι₁ := fun a => 2 * a + 1) (ι₂ := fun b => 2 * b + 1) (fun a b h => by simpa using h)
    fun a b h => by simpa using h).symm
  have hQ' : (fun ω (c : ℕ × ℕ) => Q c ω) = fun ω p => s (2 * p.1 + 1, 2 * p.2 + 1) ω :=
    funext fun ω => funext fun c => hQ c ω
  refine ⟨τ, hσm, hodd.trans ⟨(measurable_pi_iff.2 fun p => hs _).aemeasurable,
    (measurable_pi_iff.2 fun c => (hgm c).comp (measurable_fst.prodMk
      ((measurable_pi_apply c).comp measurable_snd))).aemeasurable, ?_⟩⟩
  rw [← hQ']
  exact hQlaw
/-- **The converse of the Aldous–Hoover theorem for separately exchangeable arrays**
[Panchenko, 2013, Eq. (1.77)].  Every array `T η (l, l') = τ (w, u_l, v_{l'}, x_{l, l'})`, with
`w`, `(u_l)`, `(v_{l'})`, `(x_{l, l'})` independent and uniform, is separately exchangeable:
permuting the rows and columns by `e₁, e₂` permutes the noise `(u_l)`, `(v_{l'})` and
`(x_{l, l'})`, whose law is invariant (`MeasureTheory.Measure.infinitePi_map_comp_equiv`). -/
theorem identDistrib_aldousHoover_separately_comp_equiv {τ : I × I × I × I → E}
    (hτ : Measurable τ) (T : (I × ((ℕ → I) × (ℕ → I))) × (ℕ × ℕ → I) → ℕ × ℕ → E)
    (hT : ∀ η p, T η p = τ (η.1.1, η.1.2.1 p.1, η.1.2.2 p.2, η.2 p)) (e₁ e₂ : ℕ ≃ ℕ) :
    IdentDistrib (fun η (p : ℕ × ℕ) => T η (e₁ p.1, e₂ p.2)) T
      (((volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
        (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))).prod
        (Measure.infinitePi fun _ : ℕ × ℕ => (volume : Measure I)))
      (((volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
        (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))).prod
        (Measure.infinitePi fun _ : ℕ × ℕ => (volume : Measure I))) := by
  set e : ℕ × ℕ ≃ ℕ × ℕ := Equiv.prodCongr e₁ e₂ with he
  set ρ : (I × ((ℕ → I) × (ℕ → I))) × (ℕ × ℕ → I) → (I × ((ℕ → I) × (ℕ → I))) × (ℕ × ℕ → I) :=
    fun η => ((η.1.1, (η.1.2.1 ∘ e₁, η.1.2.2 ∘ e₂)), η.2 ∘ e) with hρ
  have hρm : Measurable ρ := by
    refine ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_pi_iff.2 fun l => ?_).prodMk (measurable_pi_iff.2 fun l => ?_))).prodMk
      (measurable_pi_iff.2 fun c => ?_)
    · exact (measurable_pi_apply (e₁ l)).comp (measurable_fst.comp (measurable_snd.comp
        measurable_fst))
    · exact (measurable_pi_apply (e₂ l)).comp (measurable_snd.comp (measurable_snd.comp
        measurable_fst))
    · exact (measurable_pi_apply (e c)).comp measurable_snd
  have hTm : Measurable T := measurable_pi_iff.2 fun p => by
    simp_rw [hT]
    exact hτ.comp ((measurable_fst.comp measurable_fst).prodMk
      (((measurable_pi_apply p.1).comp (measurable_fst.comp (measurable_snd.comp
        measurable_fst))).prodMk
      (((measurable_pi_apply p.2).comp (measurable_snd.comp (measurable_snd.comp
        measurable_fst))).prodMk ((measurable_pi_apply p).comp measurable_snd))))
  have hcomp : (fun η (p : ℕ × ℕ) => T η (e₁ p.1, e₂ p.2)) = fun η => T (ρ η) := by
    funext η p
    simp only [hT, hρ, he, Function.comp_apply, Equiv.prodCongr_apply]
    rfl
  have hu₁ : Measurable fun ξ : ℕ → I => ξ ∘ e₁ :=
    measurable_pi_iff.2 fun l => measurable_pi_apply (e₁ l)
  have hu₂ : Measurable fun ξ : ℕ → I => ξ ∘ e₂ :=
    measurable_pi_iff.2 fun l => measurable_pi_apply (e₂ l)
  have hxm : Measurable fun ξ : ℕ × ℕ → I => ξ ∘ e :=
    measurable_pi_iff.2 fun c => measurable_pi_apply (e c)
  have h1 := Measure.map_prod_map (Measure.infinitePi fun _ : ℕ => (volume : Measure I))
    (Measure.infinitePi fun _ : ℕ => (volume : Measure I)) hu₁ hu₂
  rw [Measure.infinitePi_map_comp_equiv, Measure.infinitePi_map_comp_equiv] at h1
  have h2 := Measure.map_prod_map (volume : Measure I)
    ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) measurable_id
    (hu₁.prodMap hu₂)
  rw [Measure.map_id, ← h1] at h2
  have h3 := Measure.map_prod_map
    ((volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I))))
    (Measure.infinitePi fun _ : ℕ × ℕ => (volume : Measure I))
    (measurable_id.prodMap (hu₁.prodMap hu₂)) hxm
  rw [← h2, Measure.infinitePi_map_comp_equiv] at h3
  refine ⟨(measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp hTm).aemeasurable,
    hTm.aemeasurable, ?_⟩
  rw [hcomp]
  change Measure.map (T ∘ ρ) _ = _
  rw [← Measure.map_map hTm hρm]
  exact congrArg (Measure.map T) h3.symm

end Representation

end SpinGlasses
