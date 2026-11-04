/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.PosSemidef
public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import LeanMachineLearning.SpinGlasses.Basic
public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Order.Compact

/-!
# The overlap array: positive semidefiniteness and exchangeability (Panchenko §1.3, Eq. (1.74))

Replicas `σ¹, σ², … ∈ Σ_N` drawn independently from the (random) Gibbs measure `G` have the
*overlap array* `R = (R_{l,l'})_{l,l' ≥ 1}`, `R_{l,l'} = N⁻¹ σˡ ⬝ σˡ'`.  This file proves the two
properties of its annealed law `𝔼 G^{⊗∞}` that the Dovbysh–Sudakov theorem (§1.4–1.5 of the book)
needs:

* `R` is **positive semidefinite** (all finite principal submatrices), symmetric, with entries in
  `[-1, 1]` and diagonal `1`: the law is concentrated on the compact set
  `{A | A symmetric, A l l = 1, |A l l'| ≤ 1, every finite principal submatrix PSD}`
  (`isCompact_setOf_gram_array`, `annealed_gram_array`);
* `R` is **exchangeable**: `(R_{π l, π l'}) =_d (R_{l, l'})` for every permutation `π` of the
  replicas (Eq. (1.74)), because a mixture of i.i.d. sequences is exchangeable
  (`MeasureTheory.Measure.bind_infinitePi_map_comp_equiv`).

Everything is proved for an arbitrary measurable family of probability measures `ν : Ω → Measure α`
(a random Gibbs measure) and an arbitrary positive semidefinite kernel `c : α → α → ℝ`
(`R_{l,l'} = c (σˡ) (σˡ')`), and specialized to the SK model in `sk_annealed_gram_array`.  No
definition is introduced: the annealed law is a hypothesis-defined `Measure (ℕ → ℕ → ℝ)`.

## Main declarations

* `SpinGlasses.isCompact_setOf_gram_array`: the set of Gram-type arrays is compact.
* `SpinGlasses.annealed_gram_array`: the annealed law of `(c (σˡ) (σˡ'))` is a probability
  measure, concentrated on the Gram-type arrays, and exchangeable.
* `SpinGlasses.sk_annealed_gram_array`: the same for the SK overlap `N⁻¹ σ ⬝ τ` and the Gibbs
  measures `Measure.count.tilted (f ω)`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.3, Eq. (1.74).
-/

@[expose] public section

open MeasureTheory Set Matrix
open scoped Matrix

namespace SpinGlasses

section Compact

/-- **Gram-type arrays form a compact set:** symmetric arrays `A : ℕ → ℕ → ℝ` with unit diagonal,
entries in `[-1, 1]` and positive semidefinite finite principal submatrices.  It is closed (an
intersection of closed conditions) and contained in the compact cube `[-1, 1]^{ℕ × ℕ}`. -/
theorem isCompact_setOf_gram_array :
    IsCompact {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
      (∀ l l', |A l l'| ≤ 1) ∧ ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} := by
  have hbox : IsCompact (Set.pi univ fun _ : ℕ => Set.pi univ fun _ : ℕ => Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {A : ℕ → ℕ → ℝ | ∀ l l', A l l' = A l' l} := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun l => isClosed_iInter fun l' => isClosed_eq
        ((continuous_apply l').comp (continuous_apply l))
        ((continuous_apply l).comp (continuous_apply l'))
    have h2 : IsClosed {A : ℕ → ℕ → ℝ | ∀ l, A l l = 1} := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun l => isClosed_eq
        ((continuous_apply l).comp (continuous_apply l)) continuous_const
    have h3 : IsClosed {A : ℕ → ℕ → ℝ | ∀ l l', |A l l'| ≤ 1} := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun l => isClosed_iInter fun l' => isClosed_le
        (continuous_abs.comp ((continuous_apply l').comp (continuous_apply l))) continuous_const
    have h4 : IsClosed {A : ℕ → ℕ → ℝ | ∀ k : ℕ,
        (Matrix.of fun l l' : Fin k => A l l').PosSemidef} := by
      simp_rw [Set.ofPred_forall]
      refine isClosed_iInter fun k => Matrix.isClosed_setOf_posSemidef.preimage ?_
      refine continuous_matrix fun l l' => ?_
      simp only [Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    convert h1.inter (h2.inter (h3.inter h4)) using 1
    ext A
    simp only [Set.mem_ofPred_eq, mem_inter_iff]
  · intro A hA l _ l' _
    exact abs_le.1 (hA.2.2.1 l l')

end Compact

section Annealed

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The annealed law of the overlap array** (Panchenko Eq. (1.74)).  Let `ν ω` be a measurable
family of probability measures on `α` (random Gibbs measures, with disorder `ω ~ P`) and `c` a
measurable positive semidefinite kernel on `α`, symmetric, with unit diagonal and `|c| ≤ 1`.  Then
the law `Λ` of the overlap array `(c (σˡ) (σˡ'))_{l,l'}` of i.i.d. replicas `σˡ ~ ν ω`, averaged
over `ω`, is a probability measure on arrays, concentrated on the compact set of Gram-type arrays
(`isCompact_setOf_gram_array`), and invariant under every permutation of the replicas. -/
theorem annealed_gram_array {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure α}
    [∀ ω, IsProbabilityMeasure (ν ω)] (hν : Measurable ν) {c : α → α → ℝ}
    (hc : Measurable fun p : α × α => c p.1 p.2) (hsymm : ∀ a b, c a b = c b a)
    (hdiag : ∀ a, c a a = 1) (hbd : ∀ a b, |c a b| ≤ 1)
    (hpsd : ∀ (k : ℕ) (a : Fin k → α), (Matrix.of fun l l' => c (a l) (a l')).PosSemidef)
    {Λ : Measure (ℕ → ℕ → ℝ)}
    (hΛ : Λ = (P.bind fun ω => Measure.infinitePi fun _ : ℕ => ν ω).map
      fun σ l l' => c (σ l) (σ l')) :
    IsProbabilityMeasure Λ ∧
      Λ {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
        (∀ l l', |A l l'| ≤ 1) ∧ ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} =
        1 ∧
      ∀ e : ℕ ≃ ℕ, Λ.map (fun A l l' => A (e l) (e l')) = Λ := by
  have hR : Measurable fun (σ : ℕ → α) (l l' : ℕ) => c (σ l) (σ l') :=
    measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun l' => by
      have h1 : Measurable fun σ : ℕ → α => σ l := measurable_pi_apply l
      have h2 : Measurable fun σ : ℕ → α => σ l' := measurable_pi_apply l'
      exact hc.comp (h1.prodMk h2)
  have hbind : IsProbabilityMeasure (P.bind fun ω => Measure.infinitePi fun _ : ℕ => ν ω) :=
    isProbabilityMeasure_bind (Measure.measurable_infinitePi_const hν).aemeasurable
      (ae_of_all _ fun ω => inferInstance)
  refine ⟨?_, ?_, fun e => ?_⟩
  · rw [hΛ]
    infer_instance
  · have hmeas := isCompact_setOf_gram_array.isClosed.measurableSet
    rw [hΛ, Measure.map_apply hR hmeas]
    convert measure_univ using 2
    · ext σ
      exact ⟨fun _ => trivial, fun _ => ⟨fun l l' => hsymm _ _, fun l => hdiag _,
        fun l l' => hbd _ _, fun k => hpsd k fun l => σ l⟩⟩
    · exact hbind
  · have hperm : Measurable fun (A : ℕ → ℕ → ℝ) (l l' : ℕ) => A (e l) (e l') := by fun_prop
    have hσ : Measurable fun (σ : ℕ → α) => σ ∘ e :=
      measurable_pi_iff.2 fun _ => measurable_pi_apply _
    rw [hΛ, Measure.map_map hperm hR]
    exact (Measure.map_map hR hσ).symm.trans
      (congrArg (Measure.map _) (Measure.bind_infinitePi_map_comp_equiv hν e))

end Annealed

section SK

/-- **The annealed overlap array of the SK model.**  For `N > 0`, random energies `f ω σ`
(measurable in the disorder `ω`, e.g. `f ω σ = β H_N(ω, σ)` or the auxiliary `β H'_N`), the Gibbs
measure `Measure.count.tilted (f ω)` on `Σ_N = {±1}^N` and the overlap `R σ τ = N⁻¹ σ ⬝ τ`: the
annealed law of the array `(R (σˡ) (σˡ'))` of i.i.d. replicas is a probability measure on arrays,
concentrated on Gram-type arrays, and invariant under every permutation of the replicas
(Eq. (1.74)). -/
theorem sk_annealed_gram_array {N : ℕ} (hN : 0 < N) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : Ω → (Fin N → ℤˣ) → ℝ)
    (hf : ∀ σ, Measurable fun ω => f ω σ) (R : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
    (hR : ∀ σ τ, R σ τ = (N : ℝ)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ)))
    {Λ : Measure (ℕ → ℕ → ℝ)}
    (hΛ : Λ = (P.bind fun ω => Measure.infinitePi fun _ : ℕ =>
      (Measure.count : Measure (Fin N → ℤˣ)).tilted (f ω)).map fun σ l l' => R (σ l) (σ l')) :
    IsProbabilityMeasure Λ ∧
      Λ {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
        (∀ l l', |A l l'| ≤ 1) ∧ ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} =
        1 ∧
      ∀ e : ℕ ≃ ℕ, Λ.map (fun A l l' => A (e l) (e l')) = Λ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine annealed_gram_array (measurable_count_tilted f hf) (c := R) Measurable.of_discrete
    (fun a b => by rw [hR, hR, dotProduct_comm]) (fun a => ?_) (fun a b => ?_) (fun k a => ?_) hΛ
  · rw [hR]
    simpa using card_inv_mul_dotProduct_self_eq_one (ι := Fin N) (fun i => ((a i : ℤ) : ℝ))
      fun i => units_cast_sq _
  · rw [hR]
    simpa using abs_card_inv_mul_dotProduct_le_one (ι := Fin N) (fun i => ((a i : ℤ) : ℝ))
      (fun i => ((b i : ℤ) : ℝ)) (fun i => abs_units_cast_le_one _)
      fun i => abs_units_cast_le_one _
  · simp_rw [hR]
    exact Matrix.posSemidef_of_const_mul_dotProduct (fun l i => ((a l i : ℤ) : ℝ))
      (inv_nonneg.2 (Nat.cast_nonneg _))

end SK

end SpinGlasses
