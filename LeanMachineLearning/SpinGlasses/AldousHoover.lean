/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Data.Sym.Sym2
public import LeanMachineLearning.SpinGlasses.DeFinetti

/-!
# Weakly exchangeable arrays and the Aldous–Hoover theorem (Panchenko §1.4)

A symmetric array `s : Sym2 ℕ → Ω → E` is **weakly exchangeable** if `(s (c.map e))_c =_d (s c)_c`
for every permutation `e : ℕ ≃ ℕ` of the vertices.  As for sequences no structure is introduced:
the hypothesis is the `IdentDistrib` statement itself.

## Main declarations

* `SpinGlasses.identDistrib_map_of_weakly_exchangeable`: Eq. (1.89), sub-arrays have the same law.
* `SpinGlasses.condExp_comp_ae_eq_condExp_compl_of_weakly_exchangeable`: Lemma 1.6.
* `SpinGlasses.condExp_prod_comp_eq_prod_condExp_of_weakly_exchangeable`: Eq. (1.94), conditional
  independence of the entries given a set of cells.
* `SpinGlasses.condExp_vertexData_ae_eq_integral`, `SpinGlasses.map_vertexData_eq_compProd`: the
  entries on the odd vertices are conditionally independent given the vertex arrays, with the law
  `ν (S a, S b)` of an entry depending only on the two adjacent vertex arrays.
* `SpinGlasses.map_codedArray_eq_compProd`: the coded array has the same joint law with the
  vertex data.
* `SpinGlasses.exists_aldousHoover_representation`: Theorem 1.5.
* `SpinGlasses.identDistrib_aldousHoover_comp_equiv`: the converse (the representation is weakly
  exchangeable).

## Implementation notes

* The vertex arrays of Eq. (1.91) are `S a = (s {κ a x, κ a y})_{x,y}` for the vertex maps
  `κ a 0 = 2 a + 1`, `κ a (m + 1) = 2 m` (the odd vertex `2 a + 1` together with all even
  vertices); the family `κ`, and the families `S`, `Z` of vertex arrays and odd entries, are
  introduced inside the proofs together with their defining equations, so no definition is added.
* The array is indexed by cells `Sym2 ℕ`, so that symmetry holds by construction; the
  representation is stated for `ℕ × ℕ`-indexed arrays, which is the form used downstream.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.4, Lemma 1.6,
  Theorem 1.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped unitInterval

namespace SpinGlasses

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {P : Measure Ω}
  {s : Sym2 ℕ → Ω → E}

/-- A random array whose entries are entries of a family of random variables is measurable. -/
theorem measurable_reindex {ι κ : Type*} {X : κ → Ω → E} (hX : ∀ c, Measurable (X c)) {f : ι → κ}
    {S : Ω → ι → E} (hS : ∀ ω i, S ω i = X (f i) ω) : Measurable S :=
  measurable_pi_iff.2 fun i => by
    rw [show (fun ω => S ω i) = X (f i) from funext fun ω => hS ω i]
    exact hX _

section Subarray

/-- **Eq. (1.89).** Along any injection `ι : ℕ → ℕ` of the vertices a weakly exchangeable array has
the same law: `(s (c.map ι))_c =_d (s c)_c`. -/
theorem identDistrib_map_of_weakly_exchangeable [IsFiniteMeasure P] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    {ι : ℕ → ℕ} (hι : Injective ι) :
    IdentDistrib (fun ω c => s (Sym2.map ι c) ω) (fun ω c => s c ω) P P := by
  classical
  have hm : ∀ ι : ℕ → ℕ, AEMeasurable (fun ω (c : Sym2 ℕ) => s (c.map ι) ω) P := fun ι =>
    (measurable_pi_iff.2 fun c : Sym2 ℕ => hs (c.map ι)).aemeasurable
  refine (identDistrib_iff_forall_finset_identDistrib (X := fun (c : Sym2 ℕ) ω => s (c.map ι) ω)
    (Y := s) (hm ι) (measurable_pi_iff.2 hs).aemeasurable).2 fun J => ?_
  obtain ⟨e, he⟩ := exists_equiv_comp_eq (T := ℕ) (ι := J.biUnion Sym2.toFinset)
    (a := fun v => ι v) (b := fun v => (v : ℕ)) (hι.comp Subtype.val_injective)
    Subtype.val_injective
  have hu : Measurable fun (ξ : Sym2 ℕ → E) (c : J) => ξ (c.1.map ι) :=
    measurable_pi_iff.2 fun c => measurable_pi_apply _
  have h := (hexch e).comp hu
  have hc : ∀ c : J, (c.1.map ι).map e = c.1 := fun c => by
    rw [Sym2.map_map, Sym2.map_congr (g := id) fun v hv =>
      he ⟨v, Finset.mem_biUnion.2 ⟨c.1, c.2, Sym2.mem_toFinset.2 hv⟩⟩]
    exact congrFun Sym2.map_id c.1
  simp only [Function.comp_def, hc] at h
  exact h.symm

end Subarray

section Lemma16

/-- Enumerate an infinite set of vertices injectively, listing two prescribed elements first. -/
theorem exists_enum_of_infinite {V : Set ℕ} (hV : V.Infinite) {j j' : ℕ} (hjj' : j ≠ j')
    (hj : j ∈ V) (hj' : j' ∈ V) :
    ∃ W : ℕ → ℕ, Injective W ∧ range W = V ∧ W 0 = j ∧ W 1 = j' := by
  have hV' : (V \ {j, j'}).Infinite := hV.sdiff (Set.toFinite _)
  set u : ℕ → ℕ := Nat.nth (· ∈ V \ {j, j'}) with hu
  have hu_inj : Injective u := Nat.nth_injective hV'
  have hu_range : range u = V \ {j, j'} := Nat.range_nth_of_infinite hV'
  have hu_mem : ∀ n, u n ∈ V ∧ u n ≠ j ∧ u n ≠ j' := fun n => by
    have : u n ∈ V \ {j, j'} := hu_range ▸ mem_range_self n
    simpa [not_or] using this
  refine ⟨fun n => Nat.casesOn n j fun n => Nat.casesOn n j' u, ?_, ?_, rfl, rfl⟩
  · intro a b h
    rcases a with _ | _ | a <;> rcases b with _ | _ | b
    · rfl
    · exact absurd h hjj'
    · exact absurd h.symm (hu_mem b).2.1
    · exact absurd h.symm hjj'
    · rfl
    · exact absurd h.symm (hu_mem b).2.2
    · exact absurd h (hu_mem a).2.1
    · exact absurd h (hu_mem a).2.2
    · exact congrArg (fun n => n + 2) (hu_inj h)
  · ext x
    constructor
    · rintro ⟨n, rfl⟩
      rcases n with _ | _ | n
      · exact hj
      · exact hj'
      · exact (hu_mem n).1
    · intro hx
      by_cases h1 : x = j
      · exact ⟨0, h1.symm⟩
      by_cases h2 : x = j'
      · exact ⟨1, h2.symm⟩
      obtain ⟨n, hn⟩ : x ∈ range u := hu_range ▸ ⟨hx, by simp [h1, h2]⟩
      exact ⟨n + 2, hn⟩

/-- Exhaustion of the cells with both vertices in `range W` (other than `{W 0, W 1}`) by the cells
of the first `n + 2` vertices.  Comparing two enumerations `W`, `W'` that agree at `0, 1` gives the
core of Lemma 1.6. -/
private theorem condExp_cells_ae_eq [IsProbabilityMeasure P] [StandardBorelSpace E] [Nonempty E]
    (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    {W W' : ℕ → ℕ} (hW : Injective W) (hW' : Injective W') (h0 : W 0 = W' 0) (h1 : W 1 = W' 1)
    (hsub : range W ⊆ range W') {f : E → ℝ} (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    P[fun ω => f (s s(W 0, W 1) ω) |
        ⨆ c ∈ {c | c ≠ s(W 0, W 1) ∧ ∀ v ∈ c, v ∈ range W}, mE.comap (s c)] =ᵐ[P]
      P[fun ω => f (s s(W 0, W 1) ω) |
        ⨆ c ∈ {c | c ≠ s(W 0, W 1) ∧ ∀ v ∈ c, v ∈ range W'}, mE.comap (s c)] := by
  let κ : ℕ → Type := fun n => {p : Sym2 ℕ // (∀ v ∈ p, v < n + 2) ∧ p ≠ s(0, 1)}
  have hU : ∀ V : ℕ → ℕ, Injective V → ∀ t : Sym2 ℕ, s(V 0, V 1) = t →
      (⋃ n, range fun p : κ n => p.1.map V) = {c | c ≠ t ∧ ∀ v ∈ c, v ∈ range V} := by
    intro V hV t ht
    ext c
    refine ⟨fun hc => ?_, fun ⟨hct, hcv⟩ => ?_⟩
    · obtain ⟨n, p, rfl⟩ := mem_iUnion.1 hc
      refine ⟨fun h => p.2.2 (Sym2.map.injective hV ?_), fun v hv => ?_⟩
      · exact (show Sym2.map V p.1 = t from h).trans (ht.symm.trans (Sym2.map_mk V 0 1).symm)
      · obtain ⟨a, -, rfl⟩ := Sym2.mem_map.1 hv
        exact mem_range_self a
    · refine Sym2.ind (fun x y hct hcv => ?_) c hct hcv
      obtain ⟨a, ha⟩ := hcv x (Sym2.mem_mk_left x y)
      obtain ⟨b, hb⟩ := hcv y (Sym2.mem_mk_right x y)
      refine mem_iUnion.2 ⟨max a b, ⟨s(a, b), fun v hv => ?_, fun h => hct ?_⟩, ?_⟩
      · rcases Sym2.mem_iff.1 hv with rfl | rfl <;> omega
      · rw [← ht, ← ha, ← hb]
        exact congrArg (Sym2.map V) h
      · simp [ha, hb]
  have key := condExp_comp_ae_eq_of_exhaustion (P := P) (s := s) hs (κ := κ)
    (fun n p => p.1.map W) (fun n p => p.1.map W')
    (fun n _ ⟨p, hp⟩ => ⟨⟨p.1, fun v hv => by have := p.2.1 v hv; omega, p.2.2⟩, hp⟩)
    (fun n _ ⟨p, hp⟩ => ⟨⟨p.1, fun v hv => by have := p.2.1 v hv; omega, p.2.2⟩, hp⟩)
    (by rw [hU W hW _ rfl, hU W' hW' s(W 0, W 1) (by rw [h0, h1])]
        exact fun c ⟨h1, h2⟩ => ⟨h1, fun v hv => hsub (h2 v hv)⟩)
    hf hfb (t := s(W 0, W 1)) fun n => by
      obtain ⟨e, he⟩ := exists_equiv_comp_eq (T := ℕ) (ι := Fin (n + 2))
        (a := fun i => W i) (b := fun i => W' i) (hW.comp Fin.val_injective)
        (hW'.comp Fin.val_injective)
      have h := (hexch e).comp
        (u := fun ξ : Sym2 ℕ → E => (fun p : κ n => ξ (p.1.map W), ξ s(W 0, W 1)))
        (by fun_prop)
      have hc : ∀ p : κ n, (p.1.map W).map e = p.1.map W' := fun p => by
        rw [Sym2.map_map]
        exact Sym2.map_congr fun v hv => he ⟨v, p.2.1 v hv⟩
      have ht : (s(W 0, W 1)).map e = s(W 0, W 1) := by
        have e0 : e (W 0) = W' 0 := he ⟨0, by omega⟩
        have e1 : e (W 1) = W' 1 := he ⟨1, by omega⟩
        change s(e (W 0), e (W 1)) = s(W 0, W 1)
        rw [e0, e1, ← h0, ← h1]
      simp only [Function.comp_def, hc, ht] at h
      exact h.symm
  rwa [hU W hW _ rfl, hU W' hW' s(W 0, W 1) (by rw [h0, h1])] at key

/-- **Lemma 1.6** [Panchenko, 2013]. For a weakly exchangeable array, an infinite set `V` of
vertices containing two distinct vertices `j, j'`, and any set `C` of cells that contains all the
cells with both vertices in `V` except `{j, j'}`, but not `{j, j'}` itself, knowing the entries in
`C` is as good as knowing all the other entries for predicting `s {j, j'}`:
`P[f (s {j, j'}) | F_C] = P[f (s {j, j'}) | F_{c ≠ {j, j'}}]` almost surely, for every bounded
measurable `f`. -/
theorem condExp_comp_ae_eq_condExp_compl_of_weakly_exchangeable [IsProbabilityMeasure P]
    [StandardBorelSpace E] [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    {V : Set ℕ} (hV : V.Infinite) {j j' : ℕ} (hjj' : j ≠ j') (hj : j ∈ V) (hj' : j' ∈ V)
    {C : Set (Sym2 ℕ)} (hC : {c | c ≠ s(j, j') ∧ ∀ v ∈ c, v ∈ V} ⊆ C) (hC' : s(j, j') ∉ C)
    {f : E → ℝ} (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    P[fun ω => f (s s(j, j') ω) | ⨆ c ∈ C, mE.comap (s c)] =ᵐ[P]
      P[fun ω => f (s s(j, j') ω) | ⨆ c ∈ ({s(j, j')}ᶜ : Set (Sym2 ℕ)), mE.comap (s c)] := by
  obtain ⟨W, hW, hWr, h0, h1⟩ := exists_enum_of_infinite hV hjj' hj hj'
  obtain ⟨W', hW', hW'r, h0', h1'⟩ :=
    exists_enum_of_infinite infinite_univ hjj' (mem_univ j) (mem_univ j')
  have key := condExp_cells_ae_eq hs hexch hW hW' (h0.trans h0'.symm) (h1.trans h1'.symm)
    (by rw [hW'r]; exact subset_univ _) hf hfb
  rw [h0, h1, hWr, hW'r] at key
  have hm₃ : (⨆ c ∈ ({s(j, j')}ᶜ : Set (Sym2 ℕ)), mE.comap (s c)) ≤ mΩ :=
    iSup₂_le fun c _ => (hs c).comap_le
  refine condExp_ae_eq_of_le_of_le (biSup_mono hC) (biSup_mono fun c hc hct => hC' (hct ▸ hc)) hm₃
    ?_
  simpa [mem_univ] using key

end Lemma16

section Decoupling

/-- **Eq. (1.94).** Let `K` be a set of cells and `l i ∉ K` distinct cells such that each `l i` is a
pair `{j, j'}` of vertices of an infinite vertex set `V` all of whose other cells lie in `K`.  For a
weakly exchangeable array the entries `s (l i)` are conditionally independent given
`F_K = σ(s c : c ∈ K)`: `P[∏ f i (s (l i)) | F_K] = ∏ P[f i (s (l i)) | F_K]` almost surely, for
bounded measurable `f i`. -/
theorem condExp_prod_comp_eq_prod_condExp_of_weakly_exchangeable [IsProbabilityMeasure P]
    [StandardBorelSpace E] [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    {K : Set (Sym2 ℕ)} {ι : Type*} (t : Finset ι) (l : ι → Sym2 ℕ) (hl : InjOn l t)
    (hlK : ∀ i ∈ t, l i ∉ K)
    (hrich : ∀ i ∈ t, ∃ (V : Set ℕ) (j j' : ℕ), V.Infinite ∧ j ≠ j' ∧ j ∈ V ∧ j' ∈ V ∧
      l i = s(j, j') ∧ {c | c ≠ l i ∧ ∀ v ∈ c, v ∈ V} ⊆ K)
    (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i)) (hfb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C) :
    P[fun ω => ∏ i ∈ t, f i (s (l i) ω) | ⨆ c ∈ K, mE.comap (s c)] =ᵐ[P]
      fun ω => ∏ i ∈ t, P[fun ω' => f i (s (l i) ω') | ⨆ c ∈ K, mE.comap (s c)] ω := by
  refine condExp_finset_prod_comp_eq_prod_condExp hs K t l hl hlK f hf hfb
    fun i hi K' hKK' hn => ?_
  obtain ⟨V, j, j', hV, hjj', hj, hj', hli, hVK⟩ := hrich i hi
  have hiK := hlK i hi
  rw [hli] at hVK hn hiK ⊢
  exact (condExp_comp_ae_eq_condExp_compl_of_weakly_exchangeable hs hexch hV hjj' hj hj'
    (hVK.trans hKK') hn (hf i) (hfb i)).trans
    (condExp_comp_ae_eq_condExp_compl_of_weakly_exchangeable hs hexch hV hjj' hj hj' hVK
      hiK (hf i) (hfb i)).symm

end Decoupling

section VertexData

/-- A permutation of the odd numbers `2 a + 1` extends to a permutation of `ℕ` fixing the even
numbers. -/
theorem exists_equiv_fix_even (π : ℕ ≃ ℕ) :
    ∃ e : ℕ ≃ ℕ, (∀ m, e (2 * m) = 2 * m) ∧ ∀ a, e (2 * a + 1) = 2 * π a + 1 := by
  refine ⟨Equiv.natSumNatEquivNat.symm.trans
    (((Equiv.refl ℕ).sumCongr π).trans Equiv.natSumNatEquivNat), fun m => ?_, fun a => ?_⟩
  · simp [Equiv.natSumNatEquivNat_apply]
  · simp [Equiv.natSumNatEquivNat_apply]

/-- **Exchangeability of the vertex data.**  Let `S a` be the sub-array of the vertex `2 a + 1`
together with all even vertices (the vertex array of Eq. (1.91)), reindexed along `κ a`, and let
`Z c` be the entries of the array on the odd vertices.  Permuting the odd vertices by `π` (and
fixing the even ones) permutes `S` and `Z` accordingly without changing their joint law. -/
theorem identDistrib_vertexData_comp_equiv {κ : ℕ → ℕ → ℕ}
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S : ℕ → Ω → Sym2 ℕ → E} (hS : ∀ a ω c, S a ω c = s (Sym2.map (κ a) c) ω)
    {Z : Sym2 ℕ → Ω → E} (hZ : ∀ c ω, Z c ω = s (Sym2.map (fun a => 2 * a + 1) c) ω)
    (π : ℕ ≃ ℕ) :
    IdentDistrib (fun ω => (fun a => S (π a) ω, fun c => Z (Sym2.map π c) ω))
      (fun ω => (fun a => S a ω, fun c => Z c ω)) P P := by
  obtain ⟨e, he0, he1⟩ := exists_equiv_fix_even π
  have hκe : ∀ a n, e (κ a n) = κ (π a) n := fun a n => by
    cases n <;> simp [hκ0, hκ1, he0, he1]
  have hS' : ∀ a ω, S a ω = fun c => s (Sym2.map (κ a) c) ω := fun a ω => funext (hS a ω)
  have h := (hexch e).comp
    (u := fun ξ : Sym2 ℕ → E => (fun a c => ξ (Sym2.map (κ a) c),
      fun c => ξ (Sym2.map (fun a => 2 * a + 1) c)))
    ((measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c => measurable_pi_apply _).prodMk
      (measurable_pi_iff.2 fun c => measurable_pi_apply _))
  simp only [Function.comp_def, Sym2.map_map, hκe, he1, hS', hZ] at h ⊢
  exact h

/-- The vertices of the sub-array `κ a`: the even numbers and `2 a + 1`. -/
theorem mem_range_vertexMap {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) (a x : ℕ) :
    x ∈ range (κ a) ↔ x % 2 = 0 ∨ x = 2 * a + 1 := by
  refine ⟨fun ⟨n, hn⟩ => ?_, fun h => ?_⟩
  · cases n with
    | zero => exact Or.inr (hn.symm.trans (hκ0 a))
    | succ m => left; rw [← hn, hκ1]; omega
  · rcases h with h | h
    · exact ⟨x / 2 + 1, by rw [hκ1]; omega⟩
    · exact ⟨0, by rw [hκ0, h]⟩

/-- A cell `{x, y}` lies in the image of `Sym2.map f` iff both its vertices lie in the range
of `f`. -/
theorem mk_mem_range_map {α β : Type*} {f : α → β} {x y : β} :
    s(x, y) ∈ range (Sym2.map f) ↔ x ∈ range f ∧ y ∈ range f := by
  refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨⟨n, hn⟩, ⟨n', hn'⟩⟩ => ⟨s(n, n'), by simp [Sym2.map_mk, hn, hn']⟩⟩
  induction c using Sym2.ind with
  | h n n' =>
    rcases Sym2.eq_iff.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨n, h1⟩, ⟨n', h2⟩⟩
    · exact ⟨⟨n', h2⟩, ⟨n, h1⟩⟩

/-- The σ-algebra of the vertex array `S a` is generated by the cells of its sub-array. -/
theorem comap_vertexData {κ : ℕ → ℕ → ℕ} {S : ℕ → Ω → Sym2 ℕ → E}
    (hS : ∀ a ω c, S a ω c = s (Sym2.map (κ a) c) ω) (a : ℕ) :
    MeasurableSpace.pi.comap (S a) = ⨆ c ∈ range (Sym2.map (κ a)), mE.comap (s c) := by
  have : S a = fun ω c => s (Sym2.map (κ a) c) ω := funext fun ω => funext (hS a ω)
  rw [this]
  exact MeasurableSpace.comap_pi_range (Sym2.map (κ a)) s

/-- The σ-algebra of all the vertex arrays is generated by the cells of their sub-arrays. -/
theorem comap_vertexData_iSup {κ : ℕ → ℕ → ℕ} {S : ℕ → Ω → Sym2 ℕ → E}
    (hS : ∀ a ω c, S a ω c = s (Sym2.map (κ a) c) ω) :
    MeasurableSpace.pi.comap (fun ω a => S a ω) =
      ⨆ c ∈ ⋃ a', range (Sym2.map (κ a')), mE.comap (s c) := by
  rw [MeasurableSpace.comap_pi, iSup_iUnion]
  exact iSup_congr fun a' => comap_vertexData hS a'

/-- **The vertex arrays of two odd vertices behave like the first two.** For `a ≠ b`, the triple
`(S a, S b, entry {a, b})` has the same law as `(S 0, S 1, entry {0, 1})`. -/
theorem identDistrib_vertexPair {κ : ℕ → ℕ → ℕ}
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S : ℕ → Ω → Sym2 ℕ → E} (hS : ∀ a ω c, S a ω c = s (Sym2.map (κ a) c) ω)
    {Z : Sym2 ℕ → Ω → E} (hZ : ∀ c ω, Z c ω = s (Sym2.map (fun a => 2 * a + 1) c) ω)
    {a b : ℕ} (hab : a ≠ b) :
    IdentDistrib (fun ω => ((S a ω, S b ω), Z s(a, b) ω))
      (fun ω => ((S 0 ω, S 1 ω), Z s(0, 1) ω)) P P := by
  obtain ⟨π, hπ⟩ := exists_equiv_comp_eq (T := ℕ) (ι := Fin 2) (a := ![0, 1]) (b := ![a, b])
    (fun i j h => by fin_cases i <;> fin_cases j <;> simp_all)
    (fun i j h => by fin_cases i <;> fin_cases j <;> simp_all [hab.symm])
  have hπ0 : π 0 = a := by simpa using hπ 0
  have hπ1 : π 1 = b := by simpa using hπ 1
  have h := (identDistrib_vertexData_comp_equiv hexch hκ0 hκ1 hS hZ π).comp
    (u := fun p : (ℕ → Sym2 ℕ → E) × (Sym2 ℕ → E) => ((p.1 0, p.1 1), p.2 s(0, 1)))
    (by fun_prop)
  simpa [Function.comp_def, Sym2.map_mk, hπ0, hπ1] using h

/-- The even numbers are the range of `m ↦ 2 * m`. -/
theorem range_two_mul : range (fun m : ℕ => 2 * m) = {x : ℕ | x % 2 = 0} := by
  ext x
  exact ⟨fun ⟨m, hm⟩ => by have : 2 * m = x := hm; simp only [mem_ofPred_eq]; omega,
    fun h => ⟨x / 2, show 2 * (x / 2) = x by simp only [mem_ofPred_eq] at h; omega⟩⟩

/-- The even numbers form an infinite set. -/
theorem infinite_even : Set.Infinite {x : ℕ | x % 2 = 0} :=
  range_two_mul ▸ infinite_range_of_injective fun m n h => by simpa using h

/-- The even numbers together with two odd ones form an infinite set. -/
theorem infinite_vertexSet (a b : ℕ) :
    Set.Infinite {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1 ∨ x = 2 * b + 1} :=
  infinite_even.mono fun _ hx => Or.inl hx

/-- **The cells revealed by the vertex arrays.**  For distinct odd vertices `2 a + 1`, `2 b + 1`
the cell `t = {2 a + 1, 2 b + 1}` is not revealed by any vertex array, while all the other cells
spanned by `{2 a + 1, 2 b + 1}` and the even vertices are revealed by the arrays `S a`, `S b`. -/
theorem cells_vertexData {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) {a b : ℕ} (hab : a ≠ b) :
    s(2 * a + 1, 2 * b + 1) ∉ ⋃ a', range (Sym2.map (κ a')) ∧
    {c | c ≠ s(2 * a + 1, 2 * b + 1) ∧
        ∀ v ∈ c, v ∈ {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1 ∨ x = 2 * b + 1}} ⊆
      range (Sym2.map (κ a)) ∪ range (Sym2.map (κ b)) := by
  refine ⟨fun h => ?_, fun c ⟨hct, hcv⟩ => ?_⟩
  · obtain ⟨a', ha'⟩ := mem_iUnion.1 h
    obtain ⟨h1, h2⟩ := mk_mem_range_map.1 ha'
    rw [mem_range_vertexMap hκ0 hκ1] at h1 h2
    omega
  · induction c using Sym2.ind with
    | h x y =>
      have hx := hcv x (Sym2.mem_mk_left x y)
      have hy := hcv y (Sym2.mem_mk_right x y)
      have hne : ¬(x = 2 * a + 1 ∧ y = 2 * b + 1 ∨ x = 2 * b + 1 ∧ y = 2 * a + 1) := fun h =>
        hct (Sym2.eq_iff.2 h)
      simp only [mem_ofPred_eq] at hx hy
      simp only [mem_union, mk_mem_range_map, mem_range_vertexMap hκ0 hκ1]
      omega

/-- The cells revealed by all the vertex arrays and those revealed by the two arrays `S a`, `S b`
both contain all cells spanned by `{2 a + 1, 2 b + 1}` and the even vertices other than
`{2 a + 1, 2 b + 1}`, and neither contains that cell. -/
theorem cells_vertexData_subset {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1)
    (hκ1 : ∀ a m, κ a (m + 1) = 2 * m) {a b : ℕ} (hab : a ≠ b) :
    {c | c ≠ s(2 * a + 1, 2 * b + 1) ∧
        ∀ v ∈ c, v ∈ {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1 ∨ x = 2 * b + 1}} ⊆
      ⋃ a', range (Sym2.map (κ a')) :=
  (cells_vertexData hκ0 hκ1 hab).2.trans fun _ hc =>
    hc.elim (fun h => mem_iUnion.2 ⟨a, h⟩) fun h => mem_iUnion.2 ⟨b, h⟩

/-- **The entry of a pair of odd vertices, given all the vertex arrays.**  For distinct `a, b`,
the conditional law of the entry `{2 a + 1, 2 b + 1}` given all the vertex arrays `S` depends only
on `(S a, S b)`, through the same kernel `ν` for every pair (second half of Eq. (1.94)). -/
theorem condExp_vertexData_ae_eq_integral [IsProbabilityMeasure P] [StandardBorelSpace E]
    [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S : ℕ → Ω → Sym2 ℕ → E} (hS : ∀ a ω c, S a ω c = s (Sym2.map (κ a) c) ω)
    {Z : Sym2 ℕ → Ω → E} (hZ : ∀ c ω, Z c ω = s (Sym2.map (fun a => 2 * a + 1) c) ω)
    {ν : Kernel ((Sym2 ℕ → E) × (Sym2 ℕ → E)) E}
    (hν : ν = condDistrib (Z s(0, 1)) (fun ω => (S 0 ω, S 1 ω)) P)
    {a b : ℕ} (hab : a ≠ b) {g : E → ℝ} (hg : Measurable g) (hgb : ∃ C, ∀ x, |g x| ≤ C) :
    P[fun ω => g (Z s(a, b) ω) | MeasurableSpace.pi.comap fun ω a => S a ω] =ᵐ[P]
      fun ω => ∫ y, g y ∂ν (S a ω, S b ω) := by
  have hSm : ∀ a, Measurable (S a) := fun a => measurable_reindex hs (hS a)
  have hZab : Z s(a, b) = s s(2 * a + 1, 2 * b + 1) := funext fun ω => by rw [hZ]; rfl
  have hZm : Measurable (Z s(a, b)) := by rw [hZab]; exact hs _
  obtain ⟨C, hC⟩ := hgb
  have hint : Integrable (fun ω => g (Z s(a, b) ω)) P :=
    Integrable.of_bound (hg.comp hZm).aestronglyMeasurable C
      (.of_forall fun ω => by simpa using hC _)
  have hσ := comap_vertexData_iSup (mE := mE) hS
  have hσ' : MeasurableSpace.comap (fun ω => (S a ω, S b ω)) inferInstance =
      ⨆ c ∈ range (Sym2.map (κ a)) ∪ range (Sym2.map (κ b)), mE.comap (s c) := by
    refine (MeasurableSpace.comap_prodMk (S a) (S b)).trans ?_
    rw [comap_vertexData hS a, comap_vertexData hS b, iSup_union]
  obtain ⟨hn₁, hsub₂⟩ := cells_vertexData hκ0 hκ1 hab
  have hsub₁ := cells_vertexData_subset hκ0 hκ1 hab
  have hn₂ : s(2 * a + 1, 2 * b + 1) ∉ range (Sym2.map (κ a)) ∪ range (Sym2.map (κ b)) :=
    fun h => hn₁ (mem_iUnion.2 (h.elim (fun h => ⟨a, h⟩) fun h => ⟨b, h⟩))
  have hV := infinite_vertexSet a b
  have key : ∀ D : Set (Sym2 ℕ),
      {c | c ≠ s(2 * a + 1, 2 * b + 1) ∧
        ∀ v ∈ c, v ∈ {x : ℕ | x % 2 = 0 ∨ x = 2 * a + 1 ∨ x = 2 * b + 1}} ⊆ D →
      s(2 * a + 1, 2 * b + 1) ∉ D →
      P[fun ω => g (s s(2 * a + 1, 2 * b + 1) ω) | ⨆ c ∈ D, mE.comap (s c)] =ᵐ[P]
        P[fun ω => g (s s(2 * a + 1, 2 * b + 1) ω) |
          ⨆ c ∈ ({s(2 * a + 1, 2 * b + 1)}ᶜ : Set (Sym2 ℕ)), mE.comap (s c)] :=
    fun D hD hD' => condExp_comp_ae_eq_condExp_compl_of_weakly_exchangeable hs hexch hV
      (by omega) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hD hD' hg ⟨C, hC⟩
  have h1 := (key _ hsub₁ hn₁).trans (key _ hsub₂ hn₂).symm
  have h2 : P[fun ω => g (s s(2 * a + 1, 2 * b + 1) ω) |
      ⨆ c ∈ range (Sym2.map (κ a)) ∪ range (Sym2.map (κ b)), mE.comap (s c)] =ᵐ[P]
      fun ω => ∫ y, g y ∂condDistrib (Z s(a, b)) (fun ω => (S a ω, S b ω)) P (S a ω, S b ω) := by
    rw [← hσ', ← hZab]
    exact condExp_ae_eq_integral_condDistrib ((hSm a).prodMk (hSm b)) hZm.aemeasurable
      hg.stronglyMeasurable hint
  have h3 : condDistrib (Z s(a, b)) (fun ω => (S a ω, S b ω)) P = ν := by
    rw [hν]
    exact condDistrib_eq_of_map_eq (identDistrib_vertexPair hexch hκ0 hκ1 hS hZ hab).map_eq
  rw [h3] at h2
  rw [hZab, hσ]
  exact h1.trans h2

/-- An orientation of an off-diagonal cell has distinct endpoints. -/
lemma ne_of_mk_eq {c : Sym2 ℕ} (hc : ¬ c.IsDiag) {p : ℕ × ℕ} (hp : s(p.1, p.2) = c) :
    p.1 ≠ p.2 := fun h => hc (by rw [← hp, h]; exact Sym2.mk_isDiag_iff.2 rfl)

/-- **Eq. (1.94) for the vertex arrays.**  Given all the vertex arrays `S`, the entries `Z c`
of the array on the odd vertices are independent, and the entry of the pair `(a, b)` has the
law `ν (S a, S b)`: the joint law of `(S, Z)` is `P.map S ⊗ₘ K`, where `K x` is the product over
the off-diagonal cells `c = {a, b}` of `ν (x a, x b)`.  (Here `ori c = (a, b)` is an arbitrary
orientation of the cell `c`.) -/
theorem map_vertexData_eq_compProd [IsProbabilityMeasure P] [StandardBorelSpace E] [Nonempty E]
    (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P)
    {κ : ℕ → ℕ → ℕ} (hκ0 : ∀ a, κ a 0 = 2 * a + 1) (hκ1 : ∀ a m, κ a (m + 1) = 2 * m)
    {S : ℕ → Ω → Sym2 ℕ → E} (hS : ∀ a ω c, S a ω c = s (Sym2.map (κ a) c) ω)
    {Z : Sym2 ℕ → Ω → E} (hZ : ∀ c ω, Z c ω = s (Sym2.map (fun a => 2 * a + 1) c) ω)
    {ν : Kernel ((Sym2 ℕ → E) × (Sym2 ℕ → E)) E}
    (hν : ν = condDistrib (Z s(0, 1)) (fun ω => (S 0 ω, S 1 ω)) P)
    (ori : {c : Sym2 ℕ // ¬ c.IsDiag} → ℕ × ℕ) (hori : ∀ c, s((ori c).1, (ori c).2) = c.1)
    (K : Kernel (ℕ → Sym2 ℕ → E) ({c : Sym2 ℕ // ¬ c.IsDiag} → E)) [IsMarkovKernel K]
    (hK : ∀ x, K x = Measure.infinitePi fun c => ν (x (ori c).1, x (ori c).2)) :
    P.map (fun ω => (fun a => S a ω, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => Z c.1 ω)) =
      (P.map fun ω a => S a ω) ⊗ₘ K := by
  have hSm : ∀ a, Measurable (S a) := fun a => measurable_reindex hs (hS a)
  have hZm : ∀ c, Measurable (Z c) := fun c => by
    rw [show Z c = s (Sym2.map (fun a => 2 * a + 1) c) from funext (hZ c)]
    exact hs _
  have : IsMarkovKernel ν := by rw [hν]; infer_instance
  have hne : ∀ c : {c : Sym2 ℕ // ¬ c.IsDiag}, (ori c).1 ≠ (ori c).2 := fun c =>
    ne_of_mk_eq c.2 (hori c)
  have hl : ∀ c : {c : Sym2 ℕ // ¬ c.IsDiag}, Sym2.map (fun a => 2 * a + 1) c.1 =
      s(2 * (ori c).1 + 1, 2 * (ori c).2 + 1) := fun c => by rw [← hori c]; rfl
  refine map_prodMk_eq_compProd_infinitePi
    (fun c => ν.comap (fun x : ℕ → Sym2 ℕ → E => (x (ori c).1, x (ori c).2))
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))) K hK
    (measurable_pi_iff.2 hSm) (fun c => hZm c.1) (fun c g hg hgb => ?_) (fun t f hf hfb => ?_)
  · have h := condExp_vertexData_ae_eq_integral hs hexch hκ0 hκ1 hS hZ hν (hne c) hg hgb
    rw [hori c] at h
    exact h
  · rw [comap_vertexData_iSup hS]
    simp only [hZ]
    refine condExp_prod_comp_eq_prod_condExp_of_weakly_exchangeable hs hexch t
      (fun i => Sym2.map (fun a => 2 * a + 1) i.1) ?_ ?_ ?_ f hf hfb
    · exact fun i _ j _ h => Subtype.ext (Sym2.map.injective (fun x y h => by simpa using h) h)
    · intro i _
      rw [hl i]
      exact (cells_vertexData hκ0 hκ1 (hne i)).1
    · intro i _
      refine ⟨_, 2 * (ori i).1 + 1, 2 * (ori i).2 + 1, infinite_vertexSet _ _,
        by have := hne i; omega, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hl i, ?_⟩
      rw [hl i]
      exact cells_vertexData_subset hκ0 hκ1 (hne i)

end VertexData

section Coding

variable {V D F : Type*} [MeasurableSpace V] [MeasurableSpace F] [Countable D]

omit [Countable D] in
/-- **Coded cells given the vertex data.**  Let `Θ q` be the vertex data attached to a parameter
`q ~ μ`, and let the cells `c` be coded by i.i.d. noise `y_c ~ ν`, independent of `q`, through
`g c (q, y_c)`.  If, for almost every `q`, the law of the cell `c` coded from `y` is the `c`-th
coordinate law of a Markov kernel `K (Θ q)` (the product over `c` of these laws), then the vertex
data and the coded cells have the joint law `μ.map Θ ⊗ₘ K`. -/
theorem map_codedCells_eq_compProd {α γ Ξ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    [MeasurableSpace Ξ] {μ : Measure α} [IsProbabilityMeasure μ] {ν : Measure γ}
    [IsProbabilityMeasure ν] (Θ : α → Ξ) (hΘ : Measurable Θ) (g : D → α × γ → F)
    (hg : ∀ c, Measurable (g c)) (K : Kernel Ξ (D → F)) [IsMarkovKernel K]
    (hae : ∀ᵐ q ∂μ, Measure.infinitePi (fun c => ν.map fun y => g c (q, y)) = K (Θ q)) :
    (μ.prod (Measure.infinitePi fun _ : D => ν)).map
      (fun r => (Θ r.1, fun c => g c (r.1, r.2 c))) = μ.map Θ ⊗ₘ K := by
  have hνg : Measurable fun q => Measure.infinitePi fun c : D => ν.map fun y => g c (q, y) :=
    Measure.measurable_infinitePi fun c => Measure.measurable_map_curry (hg c) _
  let K' : Kernel α (D → F) := ⟨_, hνg⟩
  have hK' : IsMarkovKernel K' := ⟨fun q => inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun c : D => ν.map fun y => g c (q, y)))⟩
  have h1 := Measure.map_prod_infinitePi_eq_compProd (μ := μ) (ν := ν) (g := g) hg K'
    fun _ => rfl
  have h2 : μ ⊗ₘ K' = μ ⊗ₘ K.comap Θ hΘ := Measure.compProd_congr hae
  rw [← Measure.map_compProd_comap μ K hΘ, ← h2, ← h1, Measure.map_map (by fun_prop)
    (by fun_prop)]
  rfl

/-- **The coded array has the law prescribed by the kernel.**  Let `X : I × I → V` code the vertex
data, `ν` be a Markov kernel from pairs of vertex data to the entries, `H` code `ν` by a uniform
variable, and `f(w, u₁, u₂, y)` be `H (X(w,u₁), X(w,u₂), y)` for `u₁ ≤ u₂` and the same with
the arguments swapped otherwise.  If `ν` is symmetric in law-almost every pair, then the vertex
data `(X(w, u_a))_a`, together with the entries `f(w, u_a, u_b, y_c)` at the cells `c = {a, b}`
(`y_c` i.i.d. uniform), have the joint law `μ ⊗ₘ K`, where `μ` is the law of the vertex data and
`K x` is the product over the cells of `ν (x a, x b)`. -/
theorem map_codedArray_eq_compProd (X : I × I → V) (hX : Measurable X)
    (ν : Kernel (V × V) F) (H : (V × V) × I → F)
    (hHν : ∀ p, (volume : Measure I).map (fun y => H (p, y)) = ν p)
    (f : I × I × I × I → F) (hfm : Measurable f)
    (hf : ∀ w u₁ u₂ y, f (w, u₁, u₂, y) =
      if u₁ ≤ u₂ then H ((X (w, u₁), X (w, u₂)), y) else H ((X (w, u₂), X (w, u₁)), y))
    (ori : D → ℕ × ℕ) (hne : ∀ c, (ori c).1 ≠ (ori c).2)
    (hsymm : ∀ a b, a ≠ b → ∀ᵐ q ∂(volume : Measure I).prod
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)),
      ν (X (q.1, q.2 b), X (q.1, q.2 a)) = ν (X (q.1, q.2 a), X (q.1, q.2 b)))
    (K : Kernel (ℕ → V) (D → F)) [IsMarkovKernel K]
    (hK : ∀ x, K x = Measure.infinitePi fun c => ν (x (ori c).1, x (ori c).2)) :
    (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
      (Measure.infinitePi fun _ : D => (volume : Measure I))).map
      (fun r => (fun a => X (r.1.1, r.1.2 a), fun c => f (r.1.1, r.1.2 (ori c).1,
        r.1.2 (ori c).2, r.2 c))) =
    (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
      fun q a => X (q.1, q.2 a)) ⊗ₘ K := by
  set Q0 := (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))
    with hQ0
  set Xh : I × (ℕ → I) → ℕ → V := fun q a => X (q.1, q.2 a) with hXh
  have hXh_m : Measurable Xh := Measure.measurable_pi_curry hX
  set g : D → (I × (ℕ → I)) × I → F := fun c r =>
    f (r.1.1, r.1.2 (ori c).1, r.1.2 (ori c).2, r.2) with hg
  have hgm : ∀ c, Measurable (g c) := fun c => hfm.comp (by fun_prop)
  refine map_codedCells_eq_compProd Xh hXh_m g hgm K ?_
  have : ∀ c : D, ∀ᵐ q ∂Q0, (volume : Measure I).map (fun y => g c (q, y)) =
      ν (Xh q (ori c).1, Xh q (ori c).2) := fun c => by
    filter_upwards [hsymm _ _ (hne c)] with q hq
    by_cases hle : q.2 (ori c).1 ≤ q.2 (ori c).2
    · simp only [hg, hf, hle, ↓reduceIte, hXh]
      exact hHν _
    · simp only [hg, hf, hle, ↓reduceIte, hXh]
      rw [hHν, hq]
  filter_upwards [ae_all_iff.2 this] with q hq
  rw [hK]
  exact congrArg Measure.infinitePi (funext hq)

end Coding

section Representation

/-- **Aldous–Hoover representation of weakly exchangeable arrays** [Panchenko, 2013,
Theorem 1.5, Eq. (1.80)].  A weakly exchangeable array with values in a standard Borel space
is, in law, given by `s {l, l} = g (w, u_l)` and `s {l, l'} = f (w, u_l, u_{l'}, x_{l, l'})`
for `l ≠ l'`, where `g`, `f` are measurable, `f` is symmetric in its two middle arguments and
`w`, `(u_l)`, `(x_{l, l'})` are independent and uniform on `[0, 1]`.

The proof follows the book.  The vertex arrays `S_a` of the odd vertices `2 a + 1` together with
the even vertices are exchangeable, hence coded by de Finetti's theorem (`SpinGlasses.
exists_de_finetti_representation`).  Given them, the entries on the odd vertices are conditionally
independent (Eq. (1.94), from Lemma 1.6) with a law `ν (S_a, S_b)` depending only on the two
adjacent vertex arrays; coding `ν` by a uniform variable gives `f`, which is made symmetric by
ordering the two vertex variables.  Finally the array on the odd vertices has the law of the whole
array (Eq. (1.89)). -/
theorem exists_aldousHoover_representation [IsProbabilityMeasure P] [StandardBorelSpace E]
    [Nonempty E] (hs : ∀ c, Measurable (s c))
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω c => s (Sym2.map e c) ω) (fun ω c => s c ω) P P) :
    ∃ (g : I × I → E) (f : I × I × I × I → E), Measurable g ∧ Measurable f ∧
      (∀ w u₁ u₂ y, f (w, u₁, u₂, y) = f (w, u₂, u₁, y)) ∧
      IdentDistrib (fun ω (p : ℕ × ℕ) => s s(p.1, p.2) ω)
        (fun (η : (I × (ℕ → I)) × (Sym2 ℕ → I)) (p : ℕ × ℕ) =>
          if p.1 = p.2 then g (η.1.1, η.1.2 p.1)
          else f (η.1.1, η.1.2 p.1, η.1.2 p.2, η.2 s(p.1, p.2))) P
        (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
          (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))) := by
  classical
  obtain ⟨κ, hκ0, hκ1⟩ : ∃ κ : ℕ → ℕ → ℕ, (∀ a, κ a 0 = 2 * a + 1) ∧ ∀ a m, κ a (m + 1) = 2 * m :=
    ⟨fun a n => Nat.casesOn n (2 * a + 1) fun m => 2 * m, fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Ω → Sym2 ℕ → E, ∀ a ω c, S a ω c = s (Sym2.map (κ a) c) ω :=
    ⟨fun a ω c => s (Sym2.map (κ a) c) ω, fun _ _ _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Sym2 ℕ → Ω → E, ∀ c ω, Z c ω = s (Sym2.map (fun a => 2 * a + 1) c) ω :=
    ⟨fun c ω => s (Sym2.map (fun a => 2 * a + 1) c) ω, fun _ _ => rfl⟩
  have hSm : ∀ a, Measurable (S a) := fun a => measurable_reindex hs (hS a)
  have hZm : ∀ c, Measurable (Z c) := fun c => by
    rw [show Z c = s (Sym2.map (fun a => 2 * a + 1) c) from funext (hZ c)]
    exact hs _
  -- de Finetti for the vertex arrays
  have hSexch : ∀ π : ℕ ≃ ℕ, IdentDistrib (fun ω a => S (π a) ω) (fun ω a => S a ω) P P :=
    fun π => (identDistrib_vertexData_comp_equiv hexch hκ0 hκ1 hS hZ π).comp measurable_fst
  obtain ⟨X, hXm, hXid⟩ := exists_de_finetti_representation (s := S) hSm hSexch
  -- the kernel `ν` of an entry given the two adjacent vertex arrays, and its uniform coding `H`
  set ν := condDistrib (Z s(0, 1)) (fun ω => (S 0 ω, S 1 ω)) P with hν
  obtain ⟨H0, hHm, hH0ν⟩ := Kernel.exists_measurable_map_eq_unitInterval ν
  set H := uncurry H0 with hHdef
  have hHν : ∀ p, (volume : Measure I).map (fun y => H (p, y)) = ν p := hH0ν
  -- the coded entry, symmetrised by ordering the two vertex variables
  obtain ⟨f, hf⟩ : ∃ f : I × I × I × I → E, ∀ w u₁ u₂ y, f (w, u₁, u₂, y) =
      if u₁ ≤ u₂ then H ((X (w, u₁), X (w, u₂)), y) else H ((X (w, u₂), X (w, u₁)), y) :=
    ⟨fun p => if p.2.1 ≤ p.2.2.1 then H ((X (p.1, p.2.1), X (p.1, p.2.2.1)), p.2.2.2)
      else H ((X (p.1, p.2.2.1), X (p.1, p.2.1)), p.2.2.2), fun _ _ _ _ => rfl⟩
  have hfm : Measurable f := by
    have : f = fun p => if p.2.1 ≤ p.2.2.1 then H ((X (p.1, p.2.1), X (p.1, p.2.2.1)), p.2.2.2)
        else H ((X (p.1, p.2.2.1), X (p.1, p.2.1)), p.2.2.2) :=
      funext fun p => hf _ _ _ _
    rw [this]
    refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) ?_ ?_ <;>
      exact hHm.comp (by fun_prop)
  have hfsymm : ∀ w u₁ u₂ y, f (w, u₁, u₂, y) = f (w, u₂, u₁, y) := fun w u₁ u₂ y => by
    rw [hf, hf]
    rcases le_total u₁ u₂ with h | h
    · by_cases h' : u₂ ≤ u₁
      · rw [le_antisymm h h']
      · simp [h, h']
    · by_cases h' : u₁ ≤ u₂
      · rw [le_antisymm h' h]
      · simp [h, h']
  -- an orientation of every off-diagonal cell
  obtain ⟨ori, hori⟩ : ∃ ori : {c : Sym2 ℕ // ¬ c.IsDiag} → ℕ × ℕ,
      ∀ c, s((ori c).1, (ori c).2) = c.1 := ⟨fun c => Quot.out c.1, fun c => Quot.out_eq c.1⟩
  have hne : ∀ c : {c : Sym2 ℕ // ¬ c.IsDiag}, (ori c).1 ≠ (ori c).2 := fun c =>
    ne_of_mk_eq c.2 (hori c)
  have : IsMarkovKernel ν := by rw [hν]; infer_instance
  let K : Kernel (ℕ → Sym2 ℕ → E) ({c : Sym2 ℕ // ¬ c.IsDiag} → E) :=
    ⟨fun x => Measure.infinitePi fun c => ν (x (ori c).1, x (ori c).2),
      Measure.measurable_infinitePi fun c => ν.measurable.comp
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _))⟩
  have : IsMarkovKernel K := ⟨fun x => inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => ν (x (ori c).1, x (ori c).2)))⟩
  -- the law of the vertex arrays and the odd entries
  have hP := map_vertexData_eq_compProd hs hexch hκ0 hκ1 hS hZ hν ori hori K fun _ => rfl
  -- the kernel is symmetric
  have hswap : ∀ᵐ pq ∂P.map (fun ω => (S 0 ω, S 1 ω)), ν pq.swap = ν pq := by
    have h := identDistrib_vertexPair hexch hκ0 hκ1 hS hZ (a := 1) (b := 0) (by omega)
    rw [show (s(1, 0) : Sym2 ℕ) = s(0, 1) from Sym2.eq_swap] at h
    exact condDistrib_swap_ae_eq (hSm 0) (hSm 1) (hZm _) h
  have hsymm : ∀ a b, a ≠ b → ∀ᵐ q ∂(volume : Measure I).prod
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)),
      ν (X (q.1, q.2 b), X (q.1, q.2 a)) = ν (X (q.1, q.2 a), X (q.1, q.2 b)) := fun a b hab => by
    have hlaw : ((volume : Measure I).prod
        (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun q => (X (q.1, q.2 a), X (q.1, q.2 b))) = P.map (fun ω => (S 0 ω, S 1 ω)) := by
      have h1 := (identDistrib_vertexPair hexch hκ0 hκ1 hS hZ hab).comp measurable_fst
      have hm : Measurable fun x : ℕ → Sym2 ℕ → E => (x a, x b) :=
        (measurable_pi_apply a).prodMk (measurable_pi_apply b)
      have hXh : Measurable fun q : I × (ℕ → I) => fun a => X (q.1, q.2 a) :=
        Measure.measurable_pi_curry hXm
      calc _ = (((volume : Measure I).prod
            (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
            fun q a => X (q.1, q.2 a)).map fun x => (x a, x b) :=
            (Measure.map_map hm hXh).symm
        _ = (P.map fun ω a => S a ω).map fun x => (x a, x b) := by rw [hXid.map_eq]
        _ = P.map (fun ω => (S a ω, S b ω)) := Measure.map_map hm (measurable_pi_iff.2 hSm)
        _ = _ := h1.map_eq
    refine ae_of_ae_map (f := fun q : I × (ℕ → I) => (X (q.1, q.2 a), X (q.1, q.2 b)))
      (by fun_prop : Measurable _).aemeasurable (hlaw ▸ hswap)
  have hQ := map_codedArray_eq_compProd X hXm ν H hHν f hfm hf ori hne hsymm K fun _ => rfl
  -- assemble the array on the odd vertices from the vertex arrays and the entries
  let Φ : (ℕ → Sym2 ℕ → E) × ({c : Sym2 ℕ // ¬ c.IsDiag} → E) → ℕ × ℕ → E := fun xz p =>
    if h : p.1 = p.2 then xz.1 p.1 s(0, 0)
    else xz.2 ⟨s(p.1, p.2), fun h' => h (Sym2.mk_isDiag_iff.1 h')⟩
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun p => by
    by_cases h : p.1 = p.2
    · simp only [Φ, h, ↓reduceDIte]
      exact (measurable_pi_apply _).comp ((measurable_pi_apply p.2).comp measurable_fst)
    · simp only [Φ, h, ↓reduceDIte]
      exact (measurable_pi_apply _).comp measurable_snd
  have hAodd : (fun ω (p : ℕ × ℕ) => s s(2 * p.1 + 1, 2 * p.2 + 1) ω) = fun ω =>
      Φ (fun a => S a ω, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => Z c.1 ω) := by
    funext ω p
    by_cases h : p.1 = p.2
    · simp only [Φ, h, ↓reduceDIte]
      rw [hS, Sym2.map_mk, hκ0]
    · simp only [Φ, h, ↓reduceDIte]
      rw [hZ]
      rfl
  set Q0 := (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))
    with hQ0
  -- the coded array
  set F : (I × (ℕ → I)) × ({c : Sym2 ℕ // ¬ c.IsDiag} → I) → (ℕ → Sym2 ℕ → E) ×
      ({c : Sym2 ℕ // ¬ c.IsDiag} → E) := fun r => (fun a => X (r.1.1, r.1.2 a),
        fun c => f (r.1.1, r.1.2 (ori c).1, r.1.2 (ori c).2, r.2 c)) with hF
  have hT : (fun (η : (I × (ℕ → I)) × (Sym2 ℕ → I)) (p : ℕ × ℕ) =>
      if p.1 = p.2 then X (η.1.1, η.1.2 p.1) s(0, 0)
      else f (η.1.1, η.1.2 p.1, η.1.2 p.2, η.2 s(p.1, p.2))) =
      fun η => Φ (F (η.1, fun c => η.2 c.1)) := by
    funext η p
    by_cases h : p.1 = p.2
    · simp only [Φ, F, h, ↓reduceDIte, ↓reduceIte]
    · simp only [Φ, F, h, ↓reduceDIte, ↓reduceIte]
      set c : {c : Sym2 ℕ // ¬ c.IsDiag} := ⟨s(p.1, p.2), fun h' => h (Sym2.mk_isDiag_iff.1 h')⟩
      rcases Sym2.eq_iff.1 (hori c) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, hfsymm]
  -- restrict the cell noise to the off-diagonal cells
  have hRm : Measurable fun η : (I × (ℕ → I)) × (Sym2 ℕ → I) =>
      (η.1, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => η.2 c.1) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun c => (measurable_pi_apply _).comp measurable_snd)
  have hR : (Q0.prod (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))).map
      (fun η => (η.1, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => η.2 c.1)) =
      Q0.prod (Measure.infinitePi fun _ : {c : Sym2 ℕ // ¬ c.IsDiag} => (volume : Measure I)) := by
    have h : (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I)).map
        (fun x (c : {c : Sym2 ℕ | ¬ c.IsDiag}) => x c.1) =
        Measure.infinitePi fun _ : {c : Sym2 ℕ | ¬ c.IsDiag} => (volume : Measure I) :=
      Measure.infinitePi_map_restrict' _
    have := Measure.map_prod_map Q0 (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))
      measurable_id (measurable_pi_iff.2 fun c : {c : Sym2 ℕ | ¬ c.IsDiag} =>
        measurable_pi_apply c.1)
    rw [Measure.map_id, h] at this
    exact this.symm
  have hFm : Measurable F := by
    refine (measurable_pi_iff.2 fun a => hXm.comp (measurable_fst.comp measurable_fst |>.prodMk
      ((measurable_pi_apply a).comp (measurable_snd.comp measurable_fst)))).prodMk
      (measurable_pi_iff.2 fun c => hfm.comp ?_)
    fun_prop
  have hpair : Measurable fun ω =>
      (fun a => S a ω, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => Z c.1 ω) :=
    (measurable_pi_iff.2 hSm).prodMk (measurable_pi_iff.2 fun c => hZm c.1)
  have hmapPF : P.map (fun ω => (fun a => S a ω,
      fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => Z c.1 ω)) =
      (Q0.prod (Measure.infinitePi fun _ : {c : Sym2 ℕ // ¬ c.IsDiag} =>
        (volume : Measure I))).map F := by
    rw [hP, hXid.map_eq]
    exact hQ.symm
  have key : IdentDistrib (fun ω => Φ (fun a => S a ω, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} =>
      Z c.1 ω)) (fun η => Φ (F (η.1, fun c => η.2 c.1))) P
      (Q0.prod (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))) :=
    ⟨(hΦ.comp hpair).aemeasurable, (hΦ.comp (hFm.comp hRm)).aemeasurable, by
      calc P.map (fun ω => Φ (fun a => S a ω, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => Z c.1 ω))
          = (P.map (fun ω => (fun a => S a ω,
              fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => Z c.1 ω))).map Φ :=
            (Measure.map_map hΦ hpair).symm
        _ = (((Q0.prod (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))).map
              (fun η => (η.1, fun c : {c : Sym2 ℕ // ¬ c.IsDiag} => η.2 c.1))).map F).map Φ := by
            rw [hmapPF, hR]
        _ = _ := by
            rw [Measure.map_map hFm hRm, Measure.map_map hΦ (hFm.comp hRm)]
            rfl⟩
  -- the array on the odd vertices has the law of the whole array (Eq. (1.89))
  have hodd : IdentDistrib (fun ω (p : ℕ × ℕ) => s s(p.1, p.2) ω)
      (fun ω (p : ℕ × ℕ) => s s(2 * p.1 + 1, 2 * p.2 + 1) ω) P P :=
    (identDistrib_map_of_weakly_exchangeable hs hexch (ι := fun a => 2 * a + 1)
      (fun a b h => by simpa using h)).comp
      (u := fun ξ : Sym2 ℕ → E => fun p : ℕ × ℕ => ξ s(p.1, p.2)) (by fun_prop) |>.symm
  refine ⟨fun q => X q s(0, 0), f, (measurable_pi_apply _).comp hXm, hfm, hfsymm, ?_⟩
  rw [hAodd] at hodd
  rw [← hT] at key
  exact hodd.trans key

/-- **The converse of the Aldous–Hoover theorem.**  Every array of the form
`T η (l, l') = if l = l' then g (w, u_l) else f (w, u_l, u_{l'}, x_{l, l'})`, with `f` symmetric in
its middle arguments and `w`, `(u_l)`, `(x_{l, l'})` independent and uniform, is weakly
exchangeable: relabelling the vertices by `e` relabels the noise `(u_l)` and `(x_c)`, whose law is
invariant (`MeasureTheory.Measure.infinitePi_map_comp_equiv`). -/
theorem identDistrib_aldousHoover_comp_equiv {g : I × I → E} {f : I × I × I × I → E}
    (hg : Measurable g) (hf : Measurable f) (T : (I × (ℕ → I)) × (Sym2 ℕ → I) → ℕ × ℕ → E)
    (hT : ∀ η p, T η p = if p.1 = p.2 then g (η.1.1, η.1.2 p.1)
      else f (η.1.1, η.1.2 p.1, η.1.2 p.2, η.2 s(p.1, p.2))) (e : ℕ ≃ ℕ) :
    IdentDistrib (fun η (p : ℕ × ℕ) => T η (e p.1, e p.2)) T
      (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
        (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I)))
      (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
        (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))) := by
  classical
  have hTm : Measurable T := measurable_pi_iff.2 fun p => by
    simp_rw [hT]
    by_cases h : p.1 = p.2
    · simp only [h, ↓reduceIte]
      exact hg.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_pi_apply p.2).comp (measurable_snd.comp measurable_fst)))
    · simp only [h, ↓reduceIte]
      exact hf.comp ((measurable_fst.comp measurable_fst).prodMk
        (((measurable_pi_apply p.1).comp (measurable_snd.comp measurable_fst)).prodMk
        (((measurable_pi_apply p.2).comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_pi_apply s(p.1, p.2)).comp measurable_snd))))
  have hρ := ((MeasurePreserving.id (volume : Measure I)).prod
    (Measure.measurePreserving_comp_equiv_infinitePi (volume : Measure I) e)).prod
    (Measure.measurePreserving_comp_equiv_infinitePi (volume : Measure I) (Equiv.sym2Congr e))
  have hcomp : (fun η (p : ℕ × ℕ) => T η (e p.1, e p.2)) =
      T ∘ Prod.map (Prod.map id (· ∘ e)) (· ∘ Equiv.sym2Congr e) := by
    funext η p
    simp only [hT, comp_apply, Prod.map_fst, Prod.map_snd, id_eq, e.apply_eq_iff_eq,
      Equiv.sym2Congr_apply, Sym2.map_mk]
  refine ⟨(measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp hTm).aemeasurable,
    hTm.aemeasurable, ?_⟩
  rw [hcomp, ← Measure.map_map hTm hρ.measurable, hρ.map_eq]

end Representation

end SpinGlasses
