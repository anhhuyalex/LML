/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeGhirlandaGuerra
public import LeanMachineLearning.SpinGlasses.PoissonDirichletPower
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtomRpow

/-!
# The coalescent structure of the Ruelle cascade: Lemma 2.6 and Theorem 2.12

The power map `x ↦ x ^ e` carries the Poisson blocks of intensity `μ_ζ` to blocks of intensity
`μ_{ζ/e}` and commutes with the ranking of the points, so the powers `w_α ^ e` of the weights of
a cascade with exponents `ζ_p < e` are the weights of a cascade with exponents `ζ_p / e`
(Lemma 2.6 of Panchenko).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

/-- **Ranked atoms of powered blocks.** If the active points of the blocks `b` are positive,
distinct and summable, and their `e`-th powers are summable, the ranked atoms of the powered
blocks are the `e`-th powers of the ranked atoms. -/
theorem nthLargestAtom_poissonCountingMeasure_rpow (b : ℕ → ℕ × (ℕ → ℝ))
    [Infinite {q : ℕ × ℕ // q.2 < (b q.1).1}]
    (hpos : ∀ q : {q : ℕ × ℕ // q.2 < (b q.1).1}, 0 < (b q.1.1).2 q.1.2)
    (hinj : Function.Injective fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2)
    (hs : Summable fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2) {e : ℝ}
    (he : 0 < e)
    (hs' : Summable fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => ((b q.1.1).2 q.1.2) ^ e) (m : ℕ) :
    nthLargestAtom m (poissonCountingMeasure (fun k => (b k).1)
        (fun k l => ((b k).2 l) ^ e)) =
      nthLargestAtom m (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)) ^ e := by
  rw [poissonCountingMeasure_eq_sum_dirac, poissonCountingMeasure_eq_sum_dirac]
  exact nthLargestAtom_sum_dirac_rpow (fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} =>
    (b q.1.1).2 q.1.2) hinj hpos hs he hs' m

/-- **Powers of Poisson blocks.** Applying `x ↦ x ^ e` to every point of an independent family of
Poisson blocks `Po(rateₖ) ⊗ νₖ^{⊗ℕ}` gives the family of blocks with the sample laws `νₖ.map (· ^ e)`. -/
theorem map_infinitePi_blocks_rpow (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → ℝ≥0) (e : ℝ) :
    (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).map
        (fun (b : ℕ → ℕ × (ℕ → ℝ)) k => ((b k).1, fun l => ((b k).2 l) ^ e)) =
      Measure.infinitePi fun k => Po(rate k).prod
        (Measure.infinitePi fun _ : ℕ => (nu k).map fun x : ℝ => x ^ e) := by
  have hf : ∀ _k : ℕ, Measurable fun c : ℕ × (ℕ → ℝ) => (c.1, fun l => c.2 l ^ e) := fun _ => by
    fun_prop
  have h0 := Measure.infinitePi_map_pi
    (μ := fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k))
    (f := fun _ (c : ℕ × (ℕ → ℝ)) => (c.1, fun l => c.2 l ^ e)) hf
  refine h0.trans ?_
  congr 1
  funext k
  have h := hasLaw_map_prod_infinitePi (Ω := ℕ × (ℕ → ℝ))
    (P := Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) (r := rate k) (ν := nu k)
    (B := id) ⟨aemeasurable_id, by simp⟩ (f := fun x : ℝ => x ^ e) (by fun_prop)
  simpa using h.map_eq

section Power

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  (ζ : ℕ → ℝ) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
  (rate : (p : ℕ) → ℕ → ℝ≥0)
  (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
  (D D' : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) (e : ℕ → ℝ)

/-- **The powered data are again cascade data** (the model hypotheses of Lemma 2.6). If the vertex
data `D` consist of independent Poisson blocks of intensity `μ_{ζ_p}` and i.i.d. standard Gaussian
labels, then the data `D'` obtained by raising every point of every block at level `p` to the
power `e p > 0` are independent, with blocks of the same rates and the sample laws
`νₚₖ.map (· ^ e p)`, whose intensity is `μ_{ζ_p / e p}`; the labels are unchanged. -/
theorem cascade_power_model (hζ0 : ∀ p, 0 < ζ p) (he : ∀ p, 0 < e p)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hD' : D' = fun v ω => (fun k => (((D v ω).1 k).1, fun l => ((D v ω).1 k).2 l ^ e v.1),
      (D v ω).2)) :
    (∀ v, Measurable (D' v)) ∧ iIndepFun D' P ∧
    (∀ v, HasLaw (D' v) ((Measure.infinitePi fun k => Po(rate v.1 k).prod
      (Measure.infinitePi fun _ : ℕ => (nu v.1 k).map fun x : ℝ => x ^ e v.1)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) P) ∧
    (∀ p, zetaPoissonMeasure (ζ p / e p) =
      Measure.sum fun k => (rate p k : ℝ≥0∞) • (nu p k).map fun x : ℝ => x ^ e p) := by
  have hT : ∀ p : ℕ, Measurable fun (d : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) =>
      ((fun k => ((d.1 k).1, fun l => (d.1 k).2 l ^ e p), d.2) :
        (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) := fun p => by fun_prop
  subst hD'
  refine ⟨fun v => (hT v.1).comp (hDm v), hD.comp (fun v d => ((fun k => ((d.1 k).1,
    fun l => (d.1 k).2 l ^ e v.1), d.2) : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))) (fun v => hT v.1), ?_, ?_⟩
  · intro v
    have h : HasLaw (fun ω => ((fun k => (((D v ω).1 k).1, fun l => ((D v ω).1 k).2 l ^ e v.1),
        (D v ω).2) : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))) ((𝔡 v.1).map fun (d : (ℕ → ℕ × (ℕ → ℝ)) ×
          (ℕ → ℝ)) => ((fun k => ((d.1 k).1, fun l => (d.1 k).2 l ^ e v.1), d.2) :
            (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))) P :=
      ⟨((hT v.1).comp (hDm v)).aemeasurable, by
        have := Measure.map_map (hT v.1) (hDm v) (μ := P)
        rw [← (hDlaw v).map_eq]
        exact this.symm⟩
    rw [h𝔡 v.1] at h
    have hmap : ((Measure.infinitePi fun k => Po(rate v.1 k).prod
        (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
          (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)).map
        (fun (d : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) =>
          ((fun k => ((d.1 k).1, fun l => (d.1 k).2 l ^ e v.1), d.2) :
            (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))) = (Measure.infinitePi fun k =>
          Po(rate v.1 k).prod
            (Measure.infinitePi fun _ : ℕ => (nu v.1 k).map fun x : ℝ => x ^ e v.1)).prod
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
      rw [show (fun (d : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) =>
          ((fun k => ((d.1 k).1, fun l => (d.1 k).2 l ^ e v.1), d.2) :
            (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))) = Prod.map
          (fun (b : ℕ → ℕ × (ℕ → ℝ)) k => ((b k).1, fun l => ((b k).2 l) ^ e v.1)) id from rfl,
        ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id,
        map_infinitePi_blocks_rpow]
    rw [hmap] at h
    exact h
  · intro p
    rw [← zetaPoissonMeasure_map_rpow (hζ0 p) (he p), hmu p,
      poissonIntensity_map _ _ (by fun_prop : Measurable fun x : ℝ => x ^ e p)]

/-- The blocks of a vertex have the product law (the first marginal of the vertex law). -/
theorem map_blocks_eq_of_hasLaw {B : Measure (ℕ → ℕ × (ℕ → ℝ))} [IsProbabilityMeasure B]
    {G : Measure (ℕ → ℝ)} [IsProbabilityMeasure G] {X : Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)}
    (hX : HasLaw X (B.prod G) P) : P.map (fun ω => (X ω).1) = B := by
  rw [show (fun ω => (X ω).1) = Prod.fst ∘ X from rfl,
    ← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hX.aemeasurable,
    hX.map_eq, Measure.map_fst_prod]
  simp

/-- **Ranked atoms of the powered cascade (Lemma 2.6).** Let `ζ_p < e p` for the levels `p < r`.
For the cascade data `D` and the powered data `D'` (every point of every block at level `p` raised
to the power `e p`), almost surely the ranked atoms of the powered blocks of every vertex of level
`p < r` are the `e p`-th powers of the ranked atoms. -/
theorem ae_cascade_power_atoms (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1) (he : ∀ p, 0 < e p) (r : ℕ)
    (hr : ∀ p < r, ζ p < e p)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hD' : D' = fun v ω => (fun k => (((D v ω).1 k).1, fun l => ((D v ω).1 k).2 l ^ e v.1),
      (D v ω).2)) :
    ∀ᵐ ω ∂P, ∀ (v : Σ p : ℕ, Fin p → ℕ), v.1 < r → ∀ m : ℕ,
      nthLargestAtom m (poissonCountingMeasure (fun k => ((D' v ω).1 k).1)
        (fun k l => ((D' v ω).1 k).2 l)) =
      nthLargestAtom m (poissonCountingMeasure (fun k => ((D v ω).1 k).1)
        (fun k l => ((D v ω).1 k).2 l)) ^ e v.1 := by
  obtain ⟨hD'm, hD'i, hD'law, hmu'⟩ := cascade_power_model ζ nu rate 𝔡 D D' e hζ0 he hmu h𝔡 hDm hD
    hDlaw hD'
  subst hD'
  refine ae_all_iff.2 fun v => ?_
  by_cases hv : v.1 < r
  · have hζv : ζ v.1 / e v.1 < 1 := by
      rw [div_lt_one (he v.1)]; exact hr _ hv
    have hlaw : HasLaw (D v) ((Measure.infinitePi fun k => Po(rate v.1 k).prod
        (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
          (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) P := by
      rw [← h𝔡 v.1]; exact hDlaw v
    have h1 := ae_of_ae_map (hDm v).aemeasurable.fst
      (by rw [map_blocks_eq_of_hasLaw hlaw]
          exact ae_infinitePi_blocks_good (hζ0 v.1) (hζ1 v.1) (nu v.1) (rate v.1) (hmu v.1))
    have h2 := ae_of_ae_map (hD'm v).aemeasurable.fst
      (by rw [map_blocks_eq_of_hasLaw (hD'law v)]
          exact ae_infinitePi_blocks_good (div_pos (hζ0 v.1) (he v.1)) hζv (fun k => (nu v.1 k).map
            fun x : ℝ => x ^ e v.1) (rate v.1) (hmu' v.1))
    filter_upwards [h1, h2] with ω hω1 hω2 _ m
    obtain ⟨hinf, hpos, hsum, hinj⟩ := hω1
    have := hinf
    exact nthLargestAtom_poissonCountingMeasure_rpow ((D v ω).1) hpos hinj hsum (he v.1)
      hω2.2.2.1 m
  · exact Filter.Eventually.of_forall fun ω hv' => absurd hv' hv

/-- **Lemma 2.6 of Panchenko: the powers of the weights of a cascade are the weights of a cascade.**
Let `e p = e₀` and `ζ_p < e₀` for the levels `p < r`. Almost surely, for every depth `r' ≤ r` and
every leaf `α ∈ ℕ^{r'}`, the weight of `α` in the cascade built from the powered data `D'` (whose
blocks have exponents `ζ_p / e₀`, see `cascade_power_model`) is the `e₀`-th power of its weight in
the cascade built from `D`. Hence the normalized weights `w_α ^ e / ∑_β w_β ^ e` are the normalized weights of
a Ruelle cascade with the exponents `ζ_p / e`. -/
theorem ae_cascade_power_weights (u u' : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1) (he : ∀ p, 0 < e p) (r : ℕ) (e₀ : ℝ) (he₀ : 0 < e₀)
    (hec : ∀ p < r, e p = e₀) (hr : ∀ p < r, ζ p < e p)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hD' : D' = fun v ω => (fun k => (((D v ω).1 k).1, fun l => ((D v ω).1 k).2 l ^ e v.1),
      (D v ω).2))
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (hu' : u' = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D' ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D' ⟨p, γ⟩ ω).1 k).2 l))) :
    ∀ᵐ ω ∂P, ∀ r' ≤ r, ∀ α : Fin r' → ℕ,
      cascadeBranchWeight (u' ω) α = cascadeBranchWeight (u ω) α ^ e₀ := by
  filter_upwards [ae_cascade_power_atoms ζ nu rate 𝔡 D D' e hζ0 hζ1 he r hr hmu h𝔡 hDm hD hDlaw
    hD'] with ω h r' hr' α
  subst hu hu'
  unfold cascadeBranchWeight
  rw [← ENNReal.prod_rpow_of_nonneg he₀.le]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : i.val < r := lt_of_lt_of_le i.isLt hr'
  have h1 := h ⟨i.val, Fin.take i.val i.isLt.le α⟩ hi (α i)
  rw [hec _ hi] at h1
  exact h1

end Power

end SpinGlasses
