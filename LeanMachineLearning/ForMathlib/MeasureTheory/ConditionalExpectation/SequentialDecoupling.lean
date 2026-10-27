/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# From sequential conditioning to conditional independence

Suppose `Z₀, …, Z_{n-1}` are bounded random variables, `m` is a σ-algebra, and `𝒢 k ≥ m` is a
σ-algebra for which the earlier variables `Z_j`, `j < k`, are measurable and for which
`μ[Z_k | 𝒢 k] = μ[Z_k | m]` almost surely ("knowing the past does not help predicting `Z_k` beyond
`m`").  Then the conditional expectation of the product factorises:
`μ[∏ Z_j | m] = ∏ μ[Z_j | m]`.

This is the common induction behind Eq. (1.88) (de Finetti) and Eq. (1.94) (Aldous-Hoover) in
[Panchenko, 2013, §1.4].  It is proved once here, for an arbitrary family of σ-algebras `𝒢 k`; the
usual choice `𝒢 k = m ⊔ σ(Y_j : j < k)` is the corollary
`condExp_prod_comp_eq_prod_condExp`, whose hypothesis is only required for the functions that
actually occur in the product.

## Main declarations

* `MeasureTheory.condExp_mul_eq_mul_condExp_of_condExp_eq`: the one-step lemma.
* `MeasureTheory.condExp_prod_eq_prod_condExp`: the product formula for adapted bounded variables.
* `MeasureTheory.condExp_prod_comp_eq_prod_condExp`: the version for `f k (Y k)` with
  `𝒢 k = m ⊔ ⨆ j < k, σ(Y j)`.
* `MeasureTheory.condExp_finset_prod_comp_eq_prod_condExp`: the version for a finite family of
  cells `s (l i)` of an indexed family `s`, conditioned on `σ(s c : c ∈ K)`, where the hypothesis
  is that enlarging `K` by cells other than `l i` does not change the prediction of `s (l i)`.
  This is the shared shape of Eq. (1.88) (sequences) and Eq. (1.94) (arrays).

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], proofs of
  Eqs. (1.88), (1.94).
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m 𝒢 : MeasurableSpace Ω} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {A Z : Ω → ℝ}

/-- **One step of the decoupling.** If `m ≤ 𝒢 ≤ m₀`, `A` is bounded and `𝒢`-measurable, `Z` is
integrable and `μ[Z | 𝒢] = μ[Z | m]` almost surely, then
`μ[A * Z | m] = μ[A | m] * μ[Z | m]` almost surely. -/
theorem condExp_mul_eq_mul_condExp_of_condExp_eq (hm : m ≤ 𝒢) (h𝒢 : 𝒢 ≤ m₀)
    (hA : StronglyMeasurable[𝒢] A) (hAb : ∃ C, ∀ ω, ‖A ω‖ ≤ C) (hZ : Integrable Z μ)
    (h : μ[Z | 𝒢] =ᵐ[μ] μ[Z | m]) :
    μ[A * Z | m] =ᵐ[μ] μ[A | m] * μ[Z | m] := by
  obtain ⟨C, hC⟩ := hAb
  have hA₀ : StronglyMeasurable A := hA.mono h𝒢
  have hAZ : Integrable (A * Z) μ := hZ.bdd_mul hA₀.aestronglyMeasurable (.of_forall hC)
  have hAint : Integrable A μ := Integrable.of_bound hA₀.aestronglyMeasurable C (.of_forall hC)
  have hAZm : Integrable (A * μ[Z | m]) μ :=
    integrable_condExp.bdd_mul hA₀.aestronglyMeasurable (.of_forall hC)
  calc μ[A * Z | m] =ᵐ[μ] μ[μ[A * Z | 𝒢] | m] := (condExp_condExp_of_le hm h𝒢).symm
    _ =ᵐ[μ] μ[A * μ[Z | 𝒢] | m] :=
        condExp_congr_ae (condExp_mul_of_stronglyMeasurable_left hA hAZ hZ)
    _ =ᵐ[μ] μ[A * μ[Z | m] | m] := condExp_congr_ae (by filter_upwards [h] with ω hω; simp [hω])
    _ =ᵐ[μ] μ[A | m] * μ[Z | m] :=
        condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp hAZm hAint

/-- **Sequential conditioning gives conditional independence (product formula).**
Let `Z : Fin n → Ω → ℝ` be bounded and measurable, `m ≤ 𝒢 k ≤ m₀`, every `Z j` with `j < k` be
`𝒢 k`-measurable, and `μ[Z k | 𝒢 k] = μ[Z k | m]` almost surely for each `k`.  Then
`μ[∏ j, Z j | m] = ∏ j, μ[Z j | m]` almost surely. -/
theorem condExp_prod_eq_prod_condExp {n : ℕ} (Z : Fin n → Ω → ℝ) (𝒢 : Fin n → MeasurableSpace Ω)
    (hm₀ : m ≤ m₀) (hm : ∀ k, m ≤ 𝒢 k) (h𝒢 : ∀ k, 𝒢 k ≤ m₀) (hZ : ∀ k, Measurable (Z k))
    (hZb : ∀ k, ∃ C, ∀ ω, ‖Z k ω‖ ≤ C)
    (hadapt : ∀ j k, j < k → StronglyMeasurable[𝒢 k] (Z j))
    (hstep : ∀ k, μ[Z k | 𝒢 k] =ᵐ[μ] μ[Z k | m]) :
    μ[fun ω => ∏ j, Z j ω | m] =ᵐ[μ] fun ω => ∏ j, μ[Z j | m] ω := by
  induction n with
  | zero =>
    have h := condExp_const (μ := μ) hm₀ (1 : ℝ)
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact Filter.Eventually.of_forall fun ω => congrFun h ω
  | succ n ih =>
    have hL := ih (fun j => Z j.castSucc) (fun j => 𝒢 j.castSucc) (fun k => hm _) (fun k => h𝒢 _)
      (fun k => hZ _) (fun k => hZb _)
      (fun j k hjk => hadapt _ _ (Fin.castSucc_lt_castSucc_iff.2 hjk))
      (fun k => hstep _)
    choose C hC using hZb
    set A : Ω → ℝ := fun ω => ∏ j : Fin n, Z j.castSucc ω with hAdef
    have hA : StronglyMeasurable[𝒢 (Fin.last n)] A :=
      Finset.stronglyMeasurable_fun_prod _ fun j _ => hadapt _ _ (Fin.castSucc_lt_last j)
    have hAb : ∃ C', ∀ ω, ‖A ω‖ ≤ C' := by
      refine ⟨∏ j : Fin n, C j.castSucc, fun ω => ?_⟩
      rw [hAdef, norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => hC _ ω
    have hZint : Integrable (Z (Fin.last n)) μ :=
      Integrable.of_bound (hZ _).aestronglyMeasurable (C _) (.of_forall (hC _))
    have key := condExp_mul_eq_mul_condExp_of_condExp_eq (hm (Fin.last n)) (h𝒢 _) hA hAb hZint
      (hstep (Fin.last n))
    simp_rw [Fin.prod_univ_castSucc]
    have e : (fun ω => A ω * Z (Fin.last n) ω) = A * Z (Fin.last n) := rfl
    rw [e]
    refine key.trans ?_
    filter_upwards [hL] with ω hω
    simp only [Pi.mul_apply]
    rw [show μ[A | m] ω = μ[fun ω => ∏ j : Fin n, Z j.castSucc ω | m] ω from rfl, hω]

/-- **The decoupling for functions of random variables.** Let `Y k : Ω → E` be measurable,
`f k : E → ℝ` bounded and measurable, and suppose that, for every `k`, knowing `m` and the earlier
`Y j` does not improve the prediction of `f k (Y k)`:
`μ[f k (Y k) | m ⊔ ⨆ j < k, σ(Y j)] = μ[f k (Y k) | m]`.  Then
`μ[∏ k, f k (Y k) | m] = ∏ k, μ[f k (Y k) | m]` almost surely. -/
theorem condExp_prod_comp_eq_prod_condExp {n : ℕ} {E : Type*} [mE : MeasurableSpace E]
    (Y : Fin n → Ω → E) (f : Fin n → E → ℝ) (hm : m ≤ m₀) (hY : ∀ k, Measurable (Y k))
    (hf : ∀ k, Measurable (f k)) (hfb : ∀ k, ∃ C, ∀ x, ‖f k x‖ ≤ C)
    (hstep : ∀ k, μ[fun ω => f k (Y k ω) | m ⊔ ⨆ j < k, mE.comap (Y j)] =ᵐ[μ]
      μ[fun ω => f k (Y k ω) | m]) :
    μ[fun ω => ∏ k, f k (Y k ω) | m] =ᵐ[μ] fun ω => ∏ k, μ[fun ω' => f k (Y k ω') | m] ω := by
  refine condExp_prod_eq_prod_condExp (fun k ω => f k (Y k ω))
    (fun k => m ⊔ ⨆ j < k, mE.comap (Y j)) hm (fun k => le_sup_left)
    (fun k => sup_le hm (iSup₂_le fun j _ => (hY j).comap_le)) (fun k => (hf k).comp (hY k))
    (fun k => ?_) (fun j k hjk => ?_) hstep
  · obtain ⟨C, hC⟩ := hfb k
    exact ⟨C, fun ω => hC _⟩
  · have h1 : Measurable[mE.comap (Y j)] (fun ω => f j (Y j ω)) :=
      (hf j).comp (comap_measurable (Y j))
    exact (h1.stronglyMeasurable).mono (le_sup_of_le_right (le_iSup₂_of_le j hjk le_rfl))

/-- **Conditional independence of cells.**  Let `s : T → Ω → E` be a family of random variables,
`K` a set of cells, and `l : ι → T` an injective (on `t`) enumeration of cells outside `K`.  Suppose
that adding to `K` any further cells other than `l i` does not change the prediction of `s (l i)`:
`μ[f i (s (l i)) | σ(s c : c ∈ K')] = μ[f i (s (l i)) | σ(s c : c ∈ K)]` for `K ⊆ K'` not containing
`l i`.  Then the cells `s (l i)`, `i ∈ t`, are conditionally independent given `σ(s c : c ∈ K)`:
`μ[∏ i ∈ t, f i (s (l i)) | σ_K] = ∏ i ∈ t, μ[f i (s (l i)) | σ_K]`. -/
theorem condExp_finset_prod_comp_eq_prod_condExp {T E ι : Type*} [mE : MeasurableSpace E]
    {s : T → Ω → E} (hs : ∀ c, Measurable (s c)) (K : Set T) (t : Finset ι) (l : ι → T)
    (hl : Set.InjOn l t) (hlK : ∀ i ∈ t, l i ∉ K) (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (hfb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C)
    (hstep : ∀ i ∈ t, ∀ K' : Set T, K ⊆ K' → l i ∉ K' →
      μ[fun ω => f i (s (l i) ω) | ⨆ c ∈ K', mE.comap (s c)] =ᵐ[μ]
        μ[fun ω => f i (s (l i) ω) | ⨆ c ∈ K, mE.comap (s c)]) :
    μ[fun ω => ∏ i ∈ t, f i (s (l i) ω) | ⨆ c ∈ K, mE.comap (s c)] =ᵐ[μ]
      fun ω => ∏ i ∈ t, μ[fun ω' => f i (s (l i) ω') | ⨆ c ∈ K, mE.comap (s c)] ω := by
  let e : Fin t.card → ι := fun k => (t.equivFin.symm k : ι)
  have he_mem : ∀ k, e k ∈ t := fun k => (t.equivFin.symm k).2
  have he_inj : Function.Injective e := fun k k' h => t.equivFin.symm.injective (Subtype.ext h)
  have hconv : ∀ g : ι → ℝ, ∏ k : Fin t.card, g (e k) = ∏ i ∈ t, g i := fun g => by
    rw [← Finset.prod_coe_sort t g]
    exact Equiv.prod_comp t.equivFin.symm (fun i : t => g i)
  have hm : (⨆ c ∈ K, mE.comap (s c)) ≤ m₀ := iSup₂_le fun c _ => (hs c).comap_le
  have hstep' : ∀ k : Fin t.card,
      μ[fun ω => f (e k) (s (l (e k)) ω) |
          (⨆ c ∈ K, mE.comap (s c)) ⊔ ⨆ j < k, mE.comap (s (l (e j)))] =ᵐ[μ]
        μ[fun ω => f (e k) (s (l (e k)) ω) | ⨆ c ∈ K, mE.comap (s c)] := by
    intro k
    have hG : ((⨆ c ∈ K, mE.comap (s c)) ⊔ ⨆ j < k, mE.comap (s (l (e j)))) =
        ⨆ c ∈ K ∪ ((fun j => l (e j)) '' {j | j < k}), mE.comap (s c) := by
      rw [iSup_union, iSup_image]
      rfl
    have hnot : l (e k) ∉ K ∪ ((fun j => l (e j)) '' {j | j < k}) := by
      rintro (h | ⟨j, hj, hjk⟩)
      · exact hlK _ (he_mem k) h
      · exact absurd (he_inj (hl (he_mem j) (he_mem k) hjk)) (ne_of_lt hj)
    rw [hG]
    exact hstep _ (he_mem k) _ Set.subset_union_left hnot
  have key := condExp_prod_comp_eq_prod_condExp (μ := μ) (m := ⨆ c ∈ K, mE.comap (s c))
    (fun k ω => s (l (e k)) ω) (fun k => f (e k)) hm (fun k => hs _) (fun k => hf _)
    (fun k => by simpa using hfb (e k)) hstep'
  have e1 : (fun ω => ∏ i ∈ t, f i (s (l i) ω)) = fun ω => ∏ k, f (e k) (s (l (e k)) ω) :=
    funext fun ω => (hconv (fun i => f i (s (l i) ω))).symm
  have e2 : (fun ω => ∏ i ∈ t, μ[fun ω' => f i (s (l i) ω') | ⨆ c ∈ K, mE.comap (s c)] ω) =
      fun ω => ∏ k, μ[fun ω' => f (e k) (s (l (e k)) ω') | ⨆ c ∈ K, mE.comap (s c)] ω :=
    funext fun ω =>
      (hconv (fun i => μ[fun ω' => f i (s (l i) ω') | ⨆ c ∈ K, mE.comap (s c)] ω)).symm
  rw [e1, e2]
  exact key

end MeasureTheory
