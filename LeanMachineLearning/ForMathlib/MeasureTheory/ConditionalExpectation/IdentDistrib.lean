/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.ConditionalExpectation.L2Projection
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional expectations only depend on the joint law

If `A` takes values in a standard Borel space, the conditional expectation `P[F ∘ A | σ(B)]` is a
fixed function of `B`, namely `y ↦ ∫ F d(condDistrib A B P y)`, and `condDistrib A B P` is by
definition the disintegration of the joint law `P.map (B, A)`.  Hence everything computed from
`P[F ∘ A | σ(B)]` is determined by the law of the pair `(B, A)`:

* the conditional expectations of two pairs with the same law are the same function of `B`
  (`condExp_comp_ae_eq_of_map_eq`);
* their `L²` norms agree (`integral_sq_condExp_comp_eq_of_map_eq`), even on different probability
  spaces;
* if a family of cells is exhausted by finite sub-families whose joint laws with the target agree
  with those of another exhaustion, then the conditional expectations given the two (nested)
  σ-algebras agree (`condExp_comp_ae_eq_of_exhaustion`).

The second statement is how exchangeability enters the proofs of Lemmas 1.5 and 1.6 of
[Panchenko, 2013, §1.4]: exchangeability gives equality in law of pairs, and this file turns that
into equality of the `L²` norms of conditional expectations.

## Main declarations

* `ProbabilityTheory.condExp_comp_ae_eq_of_map_eq`
* `ProbabilityTheory.integral_sq_condExp_comp_eq_integral_condDistrib`
* `ProbabilityTheory.integral_sq_condExp_comp_eq_of_map_eq`
* `ProbabilityTheory.condDistrib_swap_ae_eq`: the conditional law given an exchangeable pair is
  symmetric in the pair.
* `ProbabilityTheory.condExp_comp_ae_eq_of_exhaustion`: the common core of Lemmas 1.5 and 1.6.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {Ω Ω' β E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {mE : MeasurableSpace E} [StandardBorelSpace E] [Nonempty E]
  {P : Measure Ω} {P' : Measure Ω'} {B : Ω → β} {A : Ω → E} {F : E → ℝ}

/-- `condDistrib` only depends on the joint law of `(B, A)`. -/
theorem condDistrib_eq_of_map_eq [IsFiniteMeasure P] [IsFiniteMeasure P'] {B' : Ω' → β}
    {A' : Ω' → E} (h : P.map (fun ω => (B ω, A ω)) = P'.map (fun ω => (B' ω, A' ω))) :
    condDistrib A B P = condDistrib A' B' P' := by
  have key : ∀ (ρ ρ' : Measure (β × E)) [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'], ρ = ρ' →
      ρ.condKernel = ρ'.condKernel := by
    rintro ρ ρ' _ _ rfl
    rfl
  rw [condDistrib_def, condDistrib_def]
  exact key _ _ h

/-- The `L²` norm of `P[F ∘ A | σ(B)]` is the `L²(P.map B)` norm of
`y ↦ ∫ F d(condDistrib A B P y)`. -/
theorem integral_sq_condExp_comp_eq_integral_condDistrib [IsFiniteMeasure P] (hB : Measurable B)
    (hA : AEMeasurable A P) (hF : Measurable F) (hFb : ∃ C, ∀ x, |F x| ≤ C) :
    ∫ ω, P[fun ω => F (A ω) | mβ.comap B] ω ^ 2 ∂P =
      ∫ y, (∫ x, F x ∂condDistrib A B P y) ^ 2 ∂P.map B := by
  obtain ⟨C, hC⟩ := hFb
  have hint : Integrable (fun ω => F (A ω)) P :=
    Integrable.of_bound (hF.comp_aemeasurable hA).aestronglyMeasurable C
      (.of_forall fun ω => by simpa using hC (A ω))
  have hψ : StronglyMeasurable fun y => ∫ x, F x ∂condDistrib A B P y :=
    hF.stronglyMeasurable.integral_kernel
  have hψ2 : StronglyMeasurable fun y => (∫ x, F x ∂condDistrib A B P y) ^ 2 := hψ.pow 2
  rw [integral_map hB.aemeasurable hψ2.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [condExp_ae_eq_integral_condDistrib hB hA hF.stronglyMeasurable hint] with ω hω
  rw [hω]

/-- If `(B, A)` and `(B', A')` have the same law, then `P[F ∘ A | σ(B)]` and `P'[F ∘ A' | σ(B')]`
have the same `L²` norm (even though they live on different probability spaces). -/
theorem integral_sq_condExp_comp_eq_of_map_eq [IsFiniteMeasure P] [IsFiniteMeasure P']
    {B' : Ω' → β} {A' : Ω' → E} (hB : Measurable B) (hA : AEMeasurable A P) (hB' : Measurable B')
    (hA' : AEMeasurable A' P') (hF : Measurable F) (hFb : ∃ C, ∀ x, |F x| ≤ C)
    (h : P.map (fun ω => (B ω, A ω)) = P'.map (fun ω => (B' ω, A' ω))) :
    ∫ ω, P[fun ω => F (A ω) | mβ.comap B] ω ^ 2 ∂P =
      ∫ ω, P'[fun ω => F (A' ω) | mβ.comap B'] ω ^ 2 ∂P' := by
  rw [integral_sq_condExp_comp_eq_integral_condDistrib hB hA hF hFb,
    integral_sq_condExp_comp_eq_integral_condDistrib hB' hA' hF hFb]
  have hm : P.map B = P'.map B' := by
    rw [← Measure.fst_map_prodMk₀ hB.aemeasurable hA,
      ← Measure.fst_map_prodMk₀ hB'.aemeasurable hA', h]
  rw [condDistrib_eq_of_map_eq h, hm]

/-- If `(B, A)` and `(B, A')` have the same law under `P`, then `P[F ∘ A | σ(B)]` and
`P[F ∘ A' | σ(B)]` coincide almost surely: the conditional expectation is the same function of
`B`. -/
theorem condExp_comp_ae_eq_of_map_eq [IsFiniteMeasure P] {A' : Ω → E} (hB : Measurable B)
    (hA : AEMeasurable A P) (hA' : AEMeasurable A' P) (hF : Measurable F)
    (hFb : ∃ C, ∀ x, |F x| ≤ C)
    (h : P.map (fun ω => (B ω, A ω)) = P.map (fun ω => (B ω, A' ω))) :
    P[fun ω => F (A ω) | mβ.comap B] =ᵐ[P] P[fun ω => F (A' ω) | mβ.comap B] := by
  obtain ⟨C, hC⟩ := hFb
  have hint : ∀ {A : Ω → E}, AEMeasurable A P → Integrable (fun ω => F (A ω)) P := fun hA =>
    Integrable.of_bound (hF.comp_aemeasurable hA).aestronglyMeasurable C
      (.of_forall fun ω => by simpa using hC _)
  filter_upwards [condExp_ae_eq_integral_condDistrib hB hA hF.stronglyMeasurable (hint hA),
    condExp_ae_eq_integral_condDistrib hB hA' hF.stronglyMeasurable (hint hA')] with ω h1 h2
  rw [h1, h2, condDistrib_eq_of_map_eq h]

/-- **Exhaustion principle (the core of Lemmas 1.5 and 1.6 of [Panchenko, 2013, §1.4]).**
Let `s : T → Ω → E` be a family of random variables, `t : T` a target, and let two sets of cells be
exhausted by increasing sequences `a n : κ n → T` and `a' n : κ n → T`, the first set inside the
second.  If for every `n` the finite family `(s (a n k))_k` has, jointly with `s t`, the same law as
`(s (a' n k))_k` has, then predicting `F (s t)` from the first set is as good as predicting it from
the second: the conditional expectations coincide almost surely.

The proof compares `L²` norms: by Lévy's upward theorem they are limits of the norms of the finite
sub-families, which coincide because the laws do (`integral_sq_condExp_comp_eq_of_map_eq`), and
`condExp_ae_eq_of_integral_sq_condExp_eq` turns equal norms into equal conditional expectations. -/
theorem condExp_comp_ae_eq_of_exhaustion [IsFiniteMeasure P] {T : Type*} {s : T → Ω → E}
    (hs : ∀ c, Measurable (s c)) {κ : ℕ → Type*} (a a' : ∀ n, κ n → T)
    (ha : ∀ n, range (a n) ⊆ range (a (n + 1))) (ha' : ∀ n, range (a' n) ⊆ range (a' (n + 1)))
    (hsub : (⋃ n, range (a n)) ⊆ ⋃ n, range (a' n)) {t : T} (hF : Measurable F)
    (hFb : ∃ C, ∀ x, |F x| ≤ C)
    (hid : ∀ n, IdentDistrib (fun ω => (fun k => s (a n k) ω, s t ω))
      (fun ω => (fun k => s (a' n k) ω, s t ω)) P P) :
    P[fun ω => F (s t ω) | ⨆ c ∈ ⋃ n, range (a n), mE.comap (s c)] =ᵐ[P]
      P[fun ω => F (s t ω) | ⨆ c ∈ ⋃ n, range (a' n), mE.comap (s c)] := by
  obtain ⟨C, hC⟩ := hFb
  have hle : ∀ A : Set T, (⨆ c ∈ A, mE.comap (s c)) ≤ mΩ := fun A =>
    iSup₂_le fun c _ => (hs c).comap_le
  have hsup : ∀ a : ∀ n, κ n → T, (⨆ n, ⨆ c ∈ range (a n), mE.comap (s c)) =
      ⨆ c ∈ ⋃ n, range (a n), mE.comap (s c) := fun a => (iSup_iUnion _ _).symm
  have hlim : ∀ (a : ∀ n, κ n → T), (∀ n, range (a n) ⊆ range (a (n + 1))) →
      Tendsto (fun n => ∫ ω, P[fun ω => F (s t ω) | ⨆ c ∈ range (a n), mE.comap (s c)] ω ^ 2 ∂P)
        atTop (𝓝 (∫ ω, P[fun ω => F (s t ω) | ⨆ c ∈ ⋃ n, range (a n), mE.comap (s c)] ω ^ 2 ∂P)) :=
    fun a ha => by
      have := tendsto_integral_sq_condExp (μ := P) (fun n => ⨆ c ∈ range (a n), mE.comap (s c))
        (monotone_nat_of_le_succ fun n => biSup_mono (ha n)) (fun n => hle _)
        (f := fun ω => F (s t ω)) (C := C) fun ω => hC _
      rwa [hsup a] at this
  have hnorm : ∀ n, ∫ ω, P[fun ω => F (s t ω) | ⨆ c ∈ range (a n), mE.comap (s c)] ω ^ 2 ∂P =
      ∫ ω, P[fun ω => F (s t ω) | ⨆ c ∈ range (a' n), mE.comap (s c)] ω ^ 2 ∂P := fun n => by
    rw [← MeasurableSpace.comap_pi_range (a n) s, ← MeasurableSpace.comap_pi_range (a' n) s]
    exact integral_sq_condExp_comp_eq_of_map_eq (measurable_pi_iff.2 fun k => hs _)
      (hs t).aemeasurable (measurable_pi_iff.2 fun k => hs _) (hs t).aemeasurable hF ⟨C, hC⟩
      (hid n).map_eq
  refine condExp_ae_eq_of_integral_sq_condExp_eq (biSup_mono hsub) (hle _)
    (MemLp.of_bound (hF.comp (hs t)).aestronglyMeasurable C
      (ae_of_all _ fun ω => by simpa using hC _)) ?_
  exact tendsto_nhds_unique (hlim a ha) ((hlim a' ha').congr fun n => (hnorm n).symm)

/-- **The conditional law given an exchangeable pair is symmetric.** If `((B, A), Y)` and
`((A, B), Y)` have the same law, then `condDistrib Y (A, B)` takes the same value at `(x, x')`
and at `(x', x)` for almost every `(x, x')` in the law of `(A, B)`. -/
theorem condDistrib_swap_ae_eq [IsFiniteMeasure P] {α : Type*} [MeasurableSpace α] {A B : Ω → α}
    {Y : Ω → E} (hA : Measurable A) (hB : Measurable B) (hY : Measurable Y)
    (h : IdentDistrib (fun ω => ((B ω, A ω), Y ω)) (fun ω => ((A ω, B ω), Y ω)) P P) :
    ∀ᵐ p ∂P.map (fun ω => (A ω, B ω)),
      condDistrib Y (fun ω => (A ω, B ω)) P p.swap = condDistrib Y (fun ω => (A ω, B ω)) P p := by
  set ν := condDistrib Y (fun ω => (A ω, B ω)) P with hν
  set μ := P.map fun ω => (A ω, B ω) with hμdef
  have hAB : Measurable fun ω => (A ω, B ω) := hA.prodMk hB
  set T : (α × α) × E → (α × α) × E := fun p => (p.1.swap, p.2) with hTdef
  have hT : Measurable T := by fun_prop
  have hTT : T ∘ T = id := funext fun p => by simp [hTdef]
  have hρ : μ ⊗ₘ ν = P.map fun ω => ((A ω, B ω), Y ω) :=
    compProd_map_condDistrib hAB.aemeasurable hY.aemeasurable
  have hμ : μ.map Prod.swap = μ := by
    rw [hμdef, Measure.map_map measurable_swap hAB]
    exact (h.comp measurable_fst).map_eq
  have hρT : (μ ⊗ₘ ν).map T = μ ⊗ₘ ν := by
    rw [hρ, Measure.map_map hT (hAB.prodMk hY)]
    exact h.map_eq
  have hM : (μ ⊗ₘ ν.comap Prod.swap measurable_swap).map T = μ ⊗ₘ ν := by
    have := Measure.map_compProd_comap μ ν measurable_swap
    rwa [hμ] at this
  have hM' : μ ⊗ₘ ν.comap Prod.swap measurable_swap = μ ⊗ₘ ν := by
    have h1 := congrArg (Measure.map T) hM
    rw [Measure.map_map hT hT, hTT, Measure.map_id, hρT] at h1
    exact h1
  filter_upwards [Kernel.ae_eq_of_compProd_eq hM'] with p hp
  exact hp


end ProbabilityTheory
