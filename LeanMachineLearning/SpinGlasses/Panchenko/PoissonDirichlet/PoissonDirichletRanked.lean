/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraAssembly
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtomRank

/-!
# Ranking the Poisson--Dirichlet block masses

The Gaussian IBP identity is already proved for the active block indices. Here
we use simplicity of the *unmarked mass* process to identify those indices
with the decreasing enumeration of its positive masses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- The positive active masses of the marked reference process are pairwise
distinct almost surely, not merely distinct as marked points. -/
theorem ae_poissonDirichlet_gaussian_masses_injective
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1)) :
    ∀ᵐ ω ∂P, Function.Injective
      (fun a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
        ((B a.1.1 ω).2 a.1.2).1) := by
  have hν : ∀ n, IsProbabilityMeasure
      (((ν n).prod (gaussianReal 0 1)).map Prod.fst) := fun _ => inferInstance
  have hnull (n : ℕ) (hn : r n ≠ 0) :
      NullSingletonClass (((ν n).prod (gaussianReal 0 1)).map Prod.fst) := by
    have hmap : (Measure.sum fun k => (r k : ℝ≥0∞) •
        (ν k).prod (gaussianReal 0 1)).map Prod.fst = zetaPoissonMeasure ζ := by
      rw [← hμ, Measure.map_fst_prod, measure_univ, one_smul]
    exact nullSingletonClass_map_block
      (fun k => (ν k).prod (gaussianReal 0 1)) r measurable_fst
      (hmap ▸ inferInstance) hn
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw measurable_fst
  filter_upwards [ae_pairwise_ne_poissonBlocks
    (fun n => ((ν n).prod (gaussianReal 0 1)).map Prod.fst)
    r hCm hCi hClaw hnull]
    with ω hω a b hab
  by_cases hab' : (a : ℕ × ℕ) = b
  · exact Subtype.ext hab'
  · exact False.elim (hω a.1 b.1 hab' a.2 b.2 hab)

/-- The active-index type is infinite almost surely: the mass process has
infinitely many positive atoms, while its mass-index count is its measure of
`(0, ∞)`. -/
theorem ae_poissonDirichlet_gaussian_active_infinite
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1)) :
    ∀ᵐ ω ∂P, Infinite {p : ℕ × ℕ // p.2 < (B p.1 ω).1} := by
  have hν : ∀ n, IsProbabilityMeasure
      (((ν n).prod (gaussianReal 0 1)).map Prod.fst) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw measurable_fst
  have hμ0 := eq_sum_map_fst_of_prod_eq
    (fun n => (ν n).prod (gaussianReal 0 1)) r hμ
  let M : Ω → Measure ℝ := fun ω => poissonCountingMeasure
    (fun n => (B n ω).1) (fun n l => ((B n ω).2 l).1)
  have hL := (iIndepFun_hasLaw_poissonCountingMeasure_apply (κ := Unit)
    (fun n => ((ν n).prod (gaussianReal 0 1)).map Prod.fst)
    r hCm hCi hClaw hμ0 (fun _ => rfl)
    (A := fun _ => Set.Ioi (0 : ℝ)) (fun _ => measurableSet_Ioi)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)).1 ()
  simp only [zetaPoissonMeasure_Ioi_zero hζ, ↓reduceIte] at hL
  have htop : ∀ᵐ ω ∂P, M ω (Set.Ioi 0) = ∞ := by
    have hd : ∀ᵐ y ∂(P.map fun ω => M ω (Set.Ioi 0)), y = ∞ := by
      rw [hL.map_eq, ae_dirac_eq]
      simp
    exact (ae_map_iff hL.aemeasurable (measurableSet_singleton ∞)).1 hd
  filter_upwards [htop] with ω hω
  have hcount := poissonCountingMeasure_apply_eq_encard_index
    (fun n => (B n ω).1) (fun n l => ((B n ω).2 l).1)
    (A := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  change M ω (Set.Ioi 0) = _ at hcount
  rw [hcount] at hω
  have hinf : {a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} |
      0 < ((B a.1.1 ω).2 a.1.2).1}.Infinite :=
    Set.encard_eq_top_iff.mp (by exact_mod_cast hω)
  let _ : Infinite {a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} |
      0 < ((B a.1.1 ω).2 a.1.2).1} := hinf.to_subtype
  exact Infinite.of_injective (fun a : {a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} |
      0 < ((B a.1.1 ω).2 a.1.2).1} => a.1) Subtype.val_injective

/-- For a positive summable family of distinct masses, some bijection `e : α ≃ ℕ`
sends each index to its rank, and the normalized `nthLargestAtom` weight at rank
`e a` equals the normalized mass `u a`. This is the deterministic transport needed
for replica series. -/
theorem exists_equiv_poissonDirichletWeight_sum_dirac
    {α : Type*} [Infinite α] (u : α → ℝ)
    (hu : Function.Injective u) (hpos : ∀ a, 0 < u a) (hs : Summable u) :
    ∃ e : α ≃ ℕ, ∀ a, poissonDirichletWeight (e a)
      (Measure.sum fun b : α => Measure.dirac (u b)) = u a / ∑' b, u b := by
  obtain ⟨e, hmass⟩ := exists_equiv_nthLargestAtom_sum_dirac u hu hpos hs
  refine ⟨e, fun a => ?_⟩
  have htotal := tsum_nthLargestAtom_sum_dirac u hu hpos hs
  change (nthLargestAtom (e a) (Measure.sum fun b : α => Measure.dirac (u b)) /
    ∑' k, nthLargestAtom k (Measure.sum fun b : α => Measure.dirac (u b))).toReal = _
  rw [hmass, htotal]
  have hsum : 0 < ∑' b, u b := hs.tsum_pos
    (fun b => (hpos b).le) (Classical.choice (Infinite.nonempty α)) (hpos _)
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (hpos a).le,
    ENNReal.toReal_ofReal hsum.le]

/-- Reindexing any finite-replica observable by the ranks of positive distinct
masses preserves its Gibbs series and every equality-of-indices overlap. -/
theorem tsum_normalized_masses_eq_ranked
    {α J : Type*} [Infinite α] [Fintype J] [DecidableEq α]
    (u : α → ℝ) (hu : Function.Injective u)
    (hpos : ∀ a, 0 < u a) (hs : Summable u)
    (F : (J → J → ℝ) → ℝ) :
    (∑' σ : J → α, (∏ i, u (σ i) / ∑' a, u a) *
      F (fun i j => if σ i = σ j then 1 else 0)) =
    ∑' σ : J → ℕ,
      (∏ i, poissonDirichletWeight (σ i)
        (Measure.sum fun a : α => Measure.dirac (u a))) *
      F (fun i j => if σ i = σ j then 1 else 0) := by
  obtain ⟨e, hw⟩ := exists_equiv_poissonDirichletWeight_sum_dirac u hu hpos hs
  let E : (J → α) ≃ (J → ℕ) := Equiv.arrowCongr (Equiv.refl J) e
  rw [← E.tsum_eq (fun σ : J → ℕ =>
    (∏ i, poissonDirichletWeight (σ i)
      (Measure.sum fun a : α => Measure.dirac (u a))) *
      F (fun i j => if σ i = σ j then 1 else 0))]
  apply tsum_congr
  intro σ
  have he (i : J) : E σ i = e (σ i) := rfl
  simp only [he, hw, e.injective.eq_iff]

/-- The fresh replica's index-coincidence observable also transports under
any ranking bijection: it is the previous statement for the replica set
`Option J` and the observable `R ↦ F(R|_J) * R(r₀, fresh)`. -/
theorem tsum_normalized_masses_fresh_eq_ranked
    {α J : Type*} [Infinite α] [Fintype J] [DecidableEq α]
    (u : α → ℝ) (hu : Function.Injective u)
    (hpos : ∀ a, 0 < u a) (hs : Summable u)
    (r₀ : J) (F : (J → J → ℝ) → ℝ) :
    (∑' τ : Option J → α, (∏ i, u (τ i) / ∑' a, u a) *
      (F (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
        if τ (some r₀) = τ none then 1 else 0)) =
    ∑' τ : Option J → ℕ,
      (∏ i, poissonDirichletWeight (τ i)
        (Measure.sum fun a : α => Measure.dirac (u a))) *
      (F (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
        if τ (some r₀) = τ none then 1 else 0) :=
  tsum_normalized_masses_eq_ranked u hu hpos hs
    (fun R => F (fun i j => R (some i) (some j)) * R (some r₀) none)

/-- Almost surely, every finite-replica block-index overlap average is the
corresponding average formed from `poissonDirichletWeight` of the unmarked mass
process. No measurability of the random ranking permutation is required. -/
theorem ae_poissonDirichlet_gaussian_replica_eq_ranked
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (J : Type*) [Fintype J] (F : (J → J → ℝ) → ℝ) :
    ∀ᵐ ω ∂P,
      (∑' σ : J → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ i, ((B (σ i).1.1 ω).2 (σ i).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          F (fun i j => if σ i = σ j then 1 else 0)) =
      ∑' σ : J → ℕ,
        (∏ i, poissonDirichletWeight (σ i)
          (poissonCountingMeasure (fun k => (B k ω).1)
            (fun k l => ((B k ω).2 l).1))) *
          F (fun i j => if σ i = σ j then 1 else 0) := by
  filter_upwards [ae_poissonDirichlet_gaussian_masses_injective ν r hBm hB hlaw hμ,
    ae_poissonDirichlet_gaussian_active_infinite hζ ν r hBm hB hlaw hμ,
    ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
      (fun n => (ν n).prod (gaussianReal 0 1)) r hBm hB hlaw hμ]
    with ω hinj hinf henv
  let α := {p : ℕ × ℕ // p.2 < (B p.1 ω).1}
  let _ : Infinite α := hinf
  let u : α → ℝ := fun a => ((B a.1.1 ω).2 a.1.2).1
  have hr := tsum_normalized_masses_eq_ranked u hinj henv.2.1 henv.2.2 F
  rw [poissonCountingMeasure_eq_sum_dirac] at ⊢
  exact hr

/-- The extra-replica overlap average also agrees almost surely with its
ranked counterpart. -/
theorem ae_poissonDirichlet_gaussian_fresh_eq_ranked
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (J : Type*) [Fintype J] (r₀ : J) (F : (J → J → ℝ) → ℝ) :
    ∀ᵐ ω ∂P,
      (∑' τ : Option J → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ i, ((B (τ i).1.1 ω).2 (τ i).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          (F (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            if τ (some r₀) = τ none then 1 else 0)) =
      ∑' τ : Option J → ℕ,
        (∏ i, poissonDirichletWeight (τ i)
          (poissonCountingMeasure (fun k => (B k ω).1)
            (fun k l => ((B k ω).2 l).1))) *
          (F (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            if τ (some r₀) = τ none then 1 else 0) :=
  ae_poissonDirichlet_gaussian_replica_eq_ranked hζ hζ1 ν r hBm hB hlaw hμ (Option J)
    (fun R => F (fun i j => R (some i) (some j)) * R (some r₀) none)

/-- Equation (2.34) for the ranked Poisson--Dirichlet masses: the expected
probability that two independently sampled ranks coincide is `1 - ζ`. -/
theorem poissonDirichlet_ranked_expected_overlap_eq_one_sub_zeta
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1)) :
    (∫ ω, ∑' τ : Option (Fin 1) → ℕ,
      (∏ j, poissonDirichletWeight (τ j)
        (poissonCountingMeasure (fun k => (B k ω).1)
          (fun k l => ((B k ω).2 l).1))) *
        (if τ (some 0) = τ none then (1 : ℝ) else 0) ∂P) = 1 - ζ := by
  have hr := ae_poissonDirichlet_gaussian_fresh_eq_ranked
    hζ hζ1 ν r hBm hB hlaw hμ (Fin 1) 0 (fun _ => 1)
  have hblock := poissonDirichlet_blocks_expected_overlap_eq_one_sub_zeta
    hζ hζ1 ν r hBm hB hlaw hμ
  rw [← integral_congr_ae (hr.mono fun ω hω => by simpa only [one_mul] using hω)]
  exact hblock

/-- Equation (2.34) in its squared-weight formulation for ranked masses. -/
theorem poissonDirichlet_ranked_expected_weight_sq_eq_one_sub_zeta
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1)) :
    (∫ ω, ∑' k : ℕ,
      poissonDirichletWeight k
        (poissonCountingMeasure (fun n => (B n ω).1)
          (fun n l => ((B n ω).2 l).1)) ^ 2 ∂P) = 1 - ζ := by
  have hr : ∀ᵐ ω ∂P,
      (∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (((B a.1.1 ω).2 a.1.2).1 /
          ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B b.1.1 ω).2 b.1.2).1) ^ 2) =
      ∑' k : ℕ,
        poissonDirichletWeight k
          (poissonCountingMeasure (fun n => (B n ω).1)
            (fun n l => ((B n ω).2 l).1)) ^ 2 := by
    filter_upwards [ae_poissonDirichlet_gaussian_masses_injective ν r hBm hB hlaw hμ,
      ae_poissonDirichlet_gaussian_active_infinite hζ ν r hBm hB hlaw hμ,
      ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
        (fun n => (ν n).prod (gaussianReal 0 1)) r hBm hB hlaw hμ]
      with ω hinj hinf henv
    let α := {p : ℕ × ℕ // p.2 < (B p.1 ω).1}
    let _ : Infinite α := hinf
    let u : α → ℝ := fun a => ((B a.1.1 ω).2 a.1.2).1
    obtain ⟨e, hw⟩ := exists_equiv_poissonDirichletWeight_sum_dirac u hinj henv.2.1 henv.2.2
    rw [poissonCountingMeasure_eq_sum_dirac]
    change (∑' a : α, (u a / ∑' b, u b) ^ 2) =
      ∑' k, (poissonDirichletWeight k
        (Measure.sum fun a : α => Measure.dirac (u a))) ^ 2
    rw [← e.tsum_eq (fun k => (poissonDirichletWeight k
      (Measure.sum fun a : α => Measure.dirac (u a))) ^ 2)]
    exact tsum_congr fun a => by rw [hw]
  rw [← integral_congr_ae hr]
  exact poissonDirichlet_blocks_expected_weight_sq_eq_one_sub_zeta
    hζ hζ1 ν r hBm hB hlaw hμ

/-- Theorem 2.7 for the ranked weights of the Gaussian-marked reference
Poisson process, in its parameter form. Together with the ranked Equation
(2.34), this is the Ghirlanda--Guerra relation for `PD(ζ)`. -/
theorem ghirlanda_guerra_poissonDirichlet_ranked_parameter
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    (n : ℝ) * (∫ ω,
      ∑' τ : Option (Fin n) → ℕ,
        (∏ j, poissonDirichletWeight (τ j)
          (poissonCountingMeasure (fun k => (B k ω).1)
            (fun k l => ((B k ω).2 l).1))) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            if τ (some r₀) = τ none then 1 else 0) ∂P) =
      (1 - ζ) * (∫ ω,
        ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => ((B m ω).2 l).1))) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
        ∫ ω, ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => ((B m ω).2 l).1))) *
            (f (fun i l => if σ i = σ l then 1 else 0) *
              if σ r₀ = σ j then 1 else 0) ∂P := by
  have hbase := ghirlanda_guerra_poissonDirichlet_blocks_parameter
    hζ hζ1 ν r hBm hB hlaw hμ n r₀ f hf
  have hfresh := ae_poissonDirichlet_gaussian_fresh_eq_ranked
    hζ hζ1 ν r hBm hB hlaw hμ (Fin n) r₀ f
  have hplain := ae_poissonDirichlet_gaussian_replica_eq_ranked
    hζ hζ1 ν r hBm hB hlaw hμ (Fin n) f
  have hold (j : Fin n) := ae_poissonDirichlet_gaussian_replica_eq_ranked
    hζ hζ1 ν r hBm hB hlaw hμ (Fin n)
      (fun R => f R * R r₀ j)
  rw [integral_congr_ae hfresh, integral_congr_ae hplain] at hbase
  convert hbase using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← integral_congr_ae (hold j)]

/-- Theorem 2.7 in the book's form: the fresh-replica overlap average
is a convex combination of the plain average times the two-replica overlap
expectation and the old-replica overlap averages. -/
theorem ghirlanda_guerra_poissonDirichlet_ranked
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    (∫ ω, ∑' τ : Option (Fin n) → ℕ,
      (∏ j, poissonDirichletWeight (τ j)
        (poissonCountingMeasure (fun k => (B k ω).1)
          (fun k l => ((B k ω).2 l).1))) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P) =
      (1 / (n : ℝ)) *
        (∫ ω, ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => ((B m ω).2 l).1))) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P) *
        (∫ ω, ∑' k : ℕ,
          poissonDirichletWeight k
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => ((B m ω).2 l).1)) ^ 2 ∂P) +
      (1 / (n : ℝ)) *
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → ℕ,
            (∏ k, poissonDirichletWeight (σ k)
              (poissonCountingMeasure (fun m => (B m ω).1)
                (fun m l => ((B m ω).2 l).1))) *
              (f (fun i l => if σ i = σ l then 1 else 0) *
                if σ r₀ = σ j then 1 else 0) ∂P := by
  have h := ghirlanda_guerra_poissonDirichlet_ranked_parameter
    hζ hζ1 ν r hBm hB hlaw hμ n r₀ f hf
  have hsq := poissonDirichlet_ranked_expected_weight_sq_eq_one_sub_zeta
    hζ hζ1 ν r hBm hB hlaw hμ
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_le r₀.val |>.trans_lt r₀.isLt))
  rw [hsq]
  calc
    _ = ((1 - ζ) * (∫ ω, ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => ((B m ω).2 l).1))) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → ℕ,
            (∏ k, poissonDirichletWeight (σ k)
              (poissonCountingMeasure (fun m => (B m ω).1)
                (fun m l => ((B m ω).2 l).1))) *
              (f (fun i l => if σ i = σ l then 1 else 0) *
                if σ r₀ = σ j then 1 else 0) ∂P) / n :=
          (eq_div_iff hn).2 (by simpa only [mul_comm] using h)
    _ = _ := by ring

/-- The joint ranked-weight law of an arbitrary unmarked Poisson block construction
agrees with that of a split Gaussian-marked reference construction. This is a
consequence of the counting-measure equivalence theorem; no measurable random
ranking bijection is needed. -/
theorem identDistrib_poissonDirichlet_weights_of_unmarked_blocks
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (ν' : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n)
      (Po(r' n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν' n).prod (gaussianReal 0 1))) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • (ν' n).prod (gaussianReal 0 1)) :
    IdentDistrib
      (fun ω k => poissonDirichletWeight k
        (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)))
      (fun ω k => poissonDirichletWeight k
        (poissonCountingMeasure (fun n => (B' n ω).1)
          (fun n l => ((B' n ω).2 l).1))) P Q := by
  have hν' : ∀ n, IsProbabilityMeasure
      (((ν' n).prod (gaussianReal 0 1)).map Prod.fst) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm' hB' hlaw' measurable_fst
  have hμmass := eq_sum_map_fst_of_prod_eq
    (fun n => (ν' n).prod (gaussianReal 0 1)) r' hμ'
  have hid := identDistrib_poissonCountingMeasure_of_intensity_eq
    ν r (fun n => ((ν' n).prod (gaussianReal 0 1)).map Prod.fst) r'
    hBm hB hlaw hCm hCi hClaw (hμ.symm.trans hμmass)
  exact hid.comp (measurable_pi_iff.2 measurable_poissonDirichletWeight)

/-- An unmarked Poisson construction has the same joint distribution of
normalized ranked masses as any other construction of the same intensity.
This is the construction-independent interface for ranked overlap observables. -/
theorem identDistrib_poissonDirichlet_weights_of_intensity_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    (ν' : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n)
      (Po(r' n).prod (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ : (Measure.sum fun n => (r n : ℝ≥0∞) • ν n) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n) :
    IdentDistrib
      (fun ω k => poissonDirichletWeight k
        (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)))
      (fun ω k => poissonDirichletWeight k
        (poissonCountingMeasure (fun n => (B' n ω).1) (fun n l => (B' n ω).2 l)))
      P Q :=
  (identDistrib_poissonCountingMeasure_of_intensity_eq
    ν r ν' r' hBm hB hlaw hBm' hB' hlaw' hμ).comp
    (measurable_pi_iff.2 measurable_poissonDirichletWeight)

/-- A finite replica overlap series is measurable as a function of the
entire ranked-weight sequence. The matrix observable is constant for each
fixed tuple of ranks, so no measurability assumption on `F` is needed. -/
theorem measurable_ranked_replica_series
    (J : Type*) [Fintype J] (F : (J → J → ℝ) → ℝ) :
    Measurable (fun w : ℕ → ℝ =>
      ∑' σ : J → ℕ, (∏ i, w (σ i)) *
        F (fun i j => if σ i = σ j then 1 else 0)) := by
  apply Measurable.tsum
  intro σ
  have hp : Measurable (fun w : ℕ → ℝ => ∏ i, w (σ i)) := by fun_prop
  exact hp.mul measurable_const

/-- A fresh-replica overlap series is measurable in the ranked weights, including
the diagonal coincidence with the extra replica. -/
theorem measurable_ranked_fresh_replica_series
    (J : Type*) [Fintype J] (r₀ : J) (F : (J → J → ℝ) → ℝ) :
    Measurable (fun w : ℕ → ℝ =>
      ∑' τ : Option J → ℕ, (∏ i, w (τ i)) *
        (F (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0)) := by
  apply Measurable.tsum
  intro τ
  have hp : Measurable (fun w : ℕ → ℝ => ∏ i, w (τ i)) := by fun_prop
  exact hp.mul measurable_const

/-- Equation (2.34) for any independent-block realization of the unmarked
`ζ`-Poisson process, regardless of its choice of intensity decomposition. -/
theorem poissonDirichlet_expected_weight_sq_eq_one_sub_zeta_of_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    (∫ ω, ∑' k : ℕ, poissonDirichletWeight k
      (poissonCountingMeasure (fun n => (B n ω).1)
        (fun n l => (B n ω).2 l)) ^ 2 ∂P) = 1 - ζ := by
  obtain ⟨ν', r', Q, hν', hQ, hBm', hB', hlaw', hμ'⟩ :=
    exists_poissonDirichlet_gaussian_split_blocks ζ
  let _ : ∀ n, IsProbabilityMeasure (ν' n) := hν'
  let _ : IsProbabilityMeasure Q := hQ
  have hid := identDistrib_poissonDirichlet_weights_of_unmarked_blocks
    ν r hBm hB hlaw hμ ν' r' hBm' hB' hlaw' hμ'
  have hseries : Measurable (fun w : ℕ → ℝ => ∑' k, w k ^ 2) :=
    Measurable.tsum fun k => by
      exact (measurable_pi_apply k).pow_const 2
  have heq := (hid.comp hseries).integral_eq
  exact heq.trans (poissonDirichlet_ranked_expected_weight_sq_eq_one_sub_zeta
    hζ hζ1 ν' r' hBm' hB' hlaw' hμ')

/-- The parameter form of Theorem 2.7 for every independent-block
construction of the unmarked `ζ`-Poisson process. The Gaussian marks are used
only in the reference proof, not in the statement or the observable. -/
theorem ghirlanda_guerra_poissonDirichlet_of_blocks_parameter
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    (n : ℝ) * (∫ ω,
      ∑' τ : Option (Fin n) → ℕ,
        (∏ j, poissonDirichletWeight (τ j)
          (poissonCountingMeasure (fun k => (B k ω).1)
            (fun k l => (B k ω).2 l))) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            if τ (some r₀) = τ none then 1 else 0) ∂P) =
      (1 - ζ) * (∫ ω,
        ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => (B m ω).2 l))) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
        ∫ ω, ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => (B m ω).2 l))) *
            (f (fun i l => if σ i = σ l then 1 else 0) *
              if σ r₀ = σ j then 1 else 0) ∂P := by
  obtain ⟨ν', r', Q, hν', hQ, hBm', hB', hlaw', hμ'⟩ :=
    exists_poissonDirichlet_gaussian_split_blocks ζ
  let _ : ∀ k, IsProbabilityMeasure (ν' k) := hν'
  let _ : IsProbabilityMeasure Q := hQ
  have hid := identDistrib_poissonDirichlet_weights_of_unmarked_blocks
    ν r hBm hB hlaw hμ ν' r' hBm' hB' hlaw' hμ'
  have hfresh := (hid.comp
    (measurable_ranked_fresh_replica_series (Fin n) r₀ f)).integral_eq
  have hplain := (hid.comp
    (measurable_ranked_replica_series (Fin n) f)).integral_eq
  have hold (j : Fin n) := (hid.comp
    (measurable_ranked_replica_series (Fin n)
      (fun R => f R * R r₀ j))).integral_eq
  simp only [Function.comp_def] at hfresh hplain hold
  rw [hfresh, hplain]
  have hbase := ghirlanda_guerra_poissonDirichlet_ranked_parameter
    hζ hζ1 ν' r' hBm' hB' hlaw' hμ' n r₀ f hf
  convert hbase using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hold j]

/-- Theorem 2.7 for every independent-block construction of the unmarked
`ζ`-Poisson process, stated with the expected squared-weight overlap. -/
theorem ghirlanda_guerra_poissonDirichlet_of_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    (∫ ω, ∑' τ : Option (Fin n) → ℕ,
      (∏ j, poissonDirichletWeight (τ j)
        (poissonCountingMeasure (fun k => (B k ω).1)
          (fun k l => (B k ω).2 l))) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P) =
      (1 / (n : ℝ)) *
        (∫ ω, ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => (B m ω).2 l))) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P) *
        (∫ ω, ∑' k : ℕ, poissonDirichletWeight k
          (poissonCountingMeasure (fun m => (B m ω).1)
            (fun m l => (B m ω).2 l)) ^ 2 ∂P) +
      (1 / (n : ℝ)) *
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → ℕ,
            (∏ k, poissonDirichletWeight (σ k)
              (poissonCountingMeasure (fun m => (B m ω).1)
                (fun m l => (B m ω).2 l))) *
              (f (fun i l => if σ i = σ l then 1 else 0) *
                if σ r₀ = σ j then 1 else 0) ∂P := by
  have h := ghirlanda_guerra_poissonDirichlet_of_blocks_parameter
    hζ hζ1 ν r hBm hB hlaw hμ n r₀ f hf
  have hsq := poissonDirichlet_expected_weight_sq_eq_one_sub_zeta_of_blocks
    hζ hζ1 ν r hBm hB hlaw hμ
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_le r₀.val |>.trans_lt r₀.isLt))
  rw [hsq]
  calc
    _ = ((1 - ζ) * (∫ ω, ∑' σ : Fin n → ℕ,
          (∏ k, poissonDirichletWeight (σ k)
            (poissonCountingMeasure (fun m => (B m ω).1)
              (fun m l => (B m ω).2 l))) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → ℕ,
            (∏ k, poissonDirichletWeight (σ k)
              (poissonCountingMeasure (fun m => (B m ω).1)
                (fun m l => (B m ω).2 l))) *
              (f (fun i l => if σ i = σ l then 1 else 0) *
                if σ r₀ = σ j then 1 else 0) ∂P) / n :=
          (eq_div_iff hn).2 (by simpa only [mul_comm] using h)
    _ = _ := by ring

end SpinGlasses
