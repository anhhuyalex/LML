/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletTalagrand
public import LeanMachineLearning.SpinGlasses.PoissonDirichletRanked

/-!
# Uniqueness of the Poisson-Dirichlet law from the Ghirlanda-Guerra identities

Theorem 2.7 applied to a block-overlap observable shows that the partition moments
`E ∏ₘ ∑ⱼ vⱼ^{nₘ}` of a random weight sequence satisfy Talagrand's recursion. Induction on the
number of replicas then shows that any two weight sequences satisfying the Ghirlanda-Guerra
relations have the same moments, hence (Theorem 2.8) the same law.

The relations are stated in the parameter form proved for `PD(ζ)` in
`ghirlanda_guerra_poissonDirichlet_of_blocks_parameter`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- Every old-replica term of Theorem 2.7 for a block-overlap observable is again a block
observable, for a surjective block map `g`: `b` itself when the two replicas already share a
block, and the map merging their blocks otherwise. -/
theorem partition_overlap_old_exists {I : Type*} {K : Type} [Fintype I] [Finite K]
    [DecidableEq K] (b : I → K) (hb : Function.Surjective b) (r l : I) :
    ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (g : I → K'),
      Function.Surjective g ∧ ∀ {w : ℕ → ℝ}, (∀ a, 0 ≤ w a) → Summable w →
        (∑' σ : I → ℕ, (∏ i, w (σ i)) *
          ((∏ i : I, ∏ j : I, if b i = b j then
            (if σ i = σ j then (1 : ℝ) else 0) else 1) *
            (if σ r = σ l then 1 else 0))) =
          ∏ m : K', ∑' a, w a ^ Fintype.card {i : I // g i = m} := by
  have := Fintype.ofFinite K
  by_cases h : b r = b l
  · refine ⟨K, inferInstance, inferInstance, b, hb, fun {w} hw0 hws => ?_⟩
    simp only [partition_overlap_same_block b _ r l h]
    exact tsum_partition_overlap_eq_powerSums b hb hw0 hws
  · exact ⟨{m : K // m ≠ b l}, inferInstance, inferInstance, _,
      partition_merge_surjective b hb r l h,
      fun {w} hw0 hws => tsum_partition_overlap_merged_eq_powerSums b hb r l h hw0 hws⟩

section Recurrence

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {v : Ω → ℕ → ℝ} {ζ : ℝ}
  (hv : ∀ᵐ ω ∂P, (∀ a, 0 ≤ v ω a) ∧ HasSum (v ω) 1)
  -- Theorem 2.7 in parameter form, the statement of
  -- `ghirlanda_guerra_poissonDirichlet_of_blocks_parameter`.
  (hGG : ∀ (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ), Measurable f →
    (n : ℝ) * (∫ ω, ∑' τ : Option (Fin n) → ℕ, (∏ j, v ω (τ j)) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P) =
      (1 - ζ) * (∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v ω (σ k)) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v ω (σ k)) *
            (f (fun i l => if σ i = σ l then 1 else 0) *
              if σ r₀ = σ j then 1 else 0) ∂P)

omit [IsProbabilityMeasure P] in
include hv hGG in
/-- Theorem 2.7 for the block-overlap observable of a surjective block map `b`: with the
fresh replica joined to the block of `r₀`, the moment of the enlarged block sizes is a
combination of the moment of `b` and the old-replica series. -/
theorem ghirlanda_guerra_partition_fresh {N : ℕ} {K : Type} [Fintype K] [DecidableEq K]
    (b : Fin N → K) (hb : Function.Surjective b) (r₀ : Fin N) :
    (N : ℝ) * ∫ ω, ∏ m : K, ∑' a, v ω a ^
        Fintype.card {o : Option (Fin N) // o.elim (b r₀) b = m} ∂P =
      (1 - ζ) * (∫ ω, ∏ m : K, ∑' a, v ω a ^ Fintype.card {i : Fin N // b i = m} ∂P) +
        ∑ j ∈ (Finset.univ : Finset (Fin N)).erase r₀,
          ∫ ω, ∑' σ : Fin N → ℕ, (∏ k, v ω (σ k)) *
            ((∏ i : Fin N, ∏ j' : Fin N, if b i = b j' then
              (if σ i = σ j' then (1 : ℝ) else 0) else 1) *
              if σ r₀ = σ j then 1 else 0) ∂P := by
  have h := hGG N r₀ (fun R => ∏ i : Fin N, ∏ j : Fin N, if b i = b j then R i j else 1)
    (measurable_partition_overlap_observable b)
  beta_reduce at h
  have hfresh : ∀ᵐ ω ∂P, (∑' τ : Option (Fin N) → ℕ, (∏ j, v ω (τ j)) *
      ((∏ i : Fin N, ∏ j : Fin N, if b i = b j then
        (if τ (some i) = τ (some j) then (1 : ℝ) else 0) else 1) *
        if τ (some r₀) = τ none then 1 else 0)) =
      ∏ m : K, ∑' a, v ω a ^
        Fintype.card {o : Option (Fin N) // o.elim (b r₀) b = m} := by
    filter_upwards [hv] with ω ⟨hw0, hw⟩
    exact tsum_partition_overlap_fresh_eq_powerSums b hb r₀ hw0 hw.summable
  have hplain : ∀ᵐ ω ∂P, (∑' σ : Fin N → ℕ, (∏ k, v ω (σ k)) *
      (∏ i : Fin N, ∏ j : Fin N, if b i = b j then
        (if σ i = σ j then (1 : ℝ) else 0) else 1)) =
      ∏ m : K, ∑' a, v ω a ^ Fintype.card {i : Fin N // b i = m} := by
    filter_upwards [hv] with ω ⟨hw0, hw⟩
    exact tsum_partition_overlap_eq_powerSums b hb hw0 hw.summable
  rw [integral_congr_ae hfresh, integral_congr_ae hplain] at h
  exact h

omit [IsProbabilityMeasure P] in
include hv in
/-- If the weights sum to one, a product of first power sums is `1`. -/
theorem integral_prod_tsum_pow_one [IsProbabilityMeasure P] {K : Type} [Fintype K] :
    (∫ ω, ∏ _m : K, ∑' a, v ω a ^ 1 ∂P) = 1 := by
  have : ∀ᵐ ω ∂P, (∏ _m : K, ∑' a, v ω a ^ 1) = 1 := by
    filter_upwards [hv] with ω ⟨_, hw⟩
    simp [hw.tsum_eq]
  rw [integral_congr_ae this]
  simp

end Recurrence

section Uniqueness

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {v : Ω → ℕ → ℝ} {v' : Ω' → ℕ → ℝ} {ζ : ℝ}
  (hv : ∀ᵐ ω ∂P, (∀ a, 0 ≤ v ω a) ∧ HasSum (v ω) 1)
  (hv' : ∀ᵐ ω ∂P', (∀ a, 0 ≤ v' ω a) ∧ HasSum (v' ω) 1)
  (hGG : ∀ (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ), Measurable f →
    (n : ℝ) * (∫ ω, ∑' τ : Option (Fin n) → ℕ, (∏ j, v ω (τ j)) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P) =
      (1 - ζ) * (∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v ω (σ k)) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v ω (σ k)) *
            (f (fun i l => if σ i = σ l then 1 else 0) *
              if σ r₀ = σ j then 1 else 0) ∂P)
  (hGG' : ∀ (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ), Measurable f →
    (n : ℝ) * (∫ ω, ∑' τ : Option (Fin n) → ℕ, (∏ j, v' ω (τ j)) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P') =
      (1 - ζ) * (∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v' ω (σ k)) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P') +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v' ω (σ k)) *
            (f (fun i l => if σ i = σ l then 1 else 0) *
              if σ r₀ = σ j then 1 else 0) ∂P')

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P'] in
include hv hv' hGG hGG' in
/-- The inductive step of Talagrand's recursion: if two weight sequences have the same
partition moments for all partitions of `N` replicas, they have the same moment for the
partition obtained by adding a replica to a block (when `N ≥ 1`). -/
theorem integral_partition_fresh_eq {N : ℕ} {K : Type} [Fintype K] [DecidableEq K]
    (b : Fin N → K) (hb : Function.Surjective b) (r₀ : Fin N)
    (hIH : ∀ (I : Type) [Fintype I], Fintype.card I = N →
      ∀ (K : Type) [Fintype K] [DecidableEq K] (g : I → K), Function.Surjective g →
        ∫ ω, ∏ m : K, ∑' a, v ω a ^ Fintype.card {i : I // g i = m} ∂P =
          ∫ ω, ∏ m : K, ∑' a, v' ω a ^ Fintype.card {i : I // g i = m} ∂P') :
    ∫ ω, ∏ m : K, ∑' a, v ω a ^
        Fintype.card {o : Option (Fin N) // o.elim (b r₀) b = m} ∂P =
      ∫ ω, ∏ m : K, ∑' a, v' ω a ^
        Fintype.card {o : Option (Fin N) // o.elim (b r₀) b = m} ∂P' := by
  have h1 := ghirlanda_guerra_partition_fresh hv hGG b hb r₀
  have h2 := ghirlanda_guerra_partition_fresh hv' hGG' b hb r₀
  have hbase := hIH (Fin N) (Fintype.card_fin N) K b hb
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin N)).erase r₀,
      (∫ ω, ∑' σ : Fin N → ℕ, (∏ k, v ω (σ k)) *
        ((∏ i : Fin N, ∏ j' : Fin N, if b i = b j' then
          (if σ i = σ j' then (1 : ℝ) else 0) else 1) *
          if σ r₀ = σ j then 1 else 0) ∂P) =
      ∫ ω, ∑' σ : Fin N → ℕ, (∏ k, v' ω (σ k)) *
        ((∏ i : Fin N, ∏ j' : Fin N, if b i = b j' then
          (if σ i = σ j' then (1 : ℝ) else 0) else 1) *
          if σ r₀ = σ j then 1 else 0) ∂P' := by
    intro j _
    obtain ⟨K', _, _, g, hg, hgw⟩ := partition_overlap_old_exists b hb r₀ j
    have hl : (∫ ω, ∑' σ : Fin N → ℕ, (∏ k, v ω (σ k)) *
        ((∏ i : Fin N, ∏ j' : Fin N, if b i = b j' then
          (if σ i = σ j' then (1 : ℝ) else 0) else 1) *
          if σ r₀ = σ j then 1 else 0) ∂P) =
        ∫ ω, ∏ m : K', ∑' a, v ω a ^ Fintype.card {i : Fin N // g i = m} ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hv] with ω ⟨hw0, hw⟩
      exact hgw hw0 hw.summable
    have hr : (∫ ω, ∑' σ : Fin N → ℕ, (∏ k, v' ω (σ k)) *
        ((∏ i : Fin N, ∏ j' : Fin N, if b i = b j' then
          (if σ i = σ j' then (1 : ℝ) else 0) else 1) *
          if σ r₀ = σ j then 1 else 0) ∂P') =
        ∫ ω, ∏ m : K', ∑' a, v' ω a ^ Fintype.card {i : Fin N // g i = m} ∂P' := by
      refine integral_congr_ae ?_
      filter_upwards [hv'] with ω ⟨hw0, hw⟩
      exact hgw hw0 hw.summable
    rw [hl, hr]
    exact hIH (Fin N) (Fintype.card_fin N) K' g hg
  have hN : (N : ℝ) ≠ 0 := by
    have : 0 < N := Fin.pos r₀
    positivity
  apply mul_left_cancel₀ hN
  rw [h1, h2, hbase, Finset.sum_congr rfl hsum]

include hv hv' hGG hGG' in
/-- Talagrand's recursion determines all partition moments: two weight sequences summing to
one that satisfy the Ghirlanda-Guerra relations with the same parameter have the same moment
`E ∏ₘ ∑ⱼ vⱼ^{|g⁻¹ m|}` for every surjective block map `g` on a finite set of replicas. -/
theorem integral_partition_powerSums_eq_of_ghirlanda_guerra :
    ∀ (N : ℕ) (I : Type) [Fintype I], Fintype.card I = N →
      ∀ (K : Type) [Fintype K] [DecidableEq K] (g : I → K), Function.Surjective g →
        ∫ ω, ∏ m : K, ∑' a, v ω a ^ Fintype.card {i : I // g i = m} ∂P =
          ∫ ω, ∏ m : K, ∑' a, v' ω a ^ Fintype.card {i : I // g i = m} ∂P' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro I _ hI K _ _ g hg
  classical
  by_cases hinj : Function.Injective g
  · have hone : ∀ m : K, Fintype.card {i : I // g i = m} = 1 := by
      intro m
      obtain ⟨a, ha⟩ := hg m
      exact Fintype.card_eq_one_iff.2
        ⟨⟨a, ha⟩, fun ⟨c, hc⟩ => Subtype.ext (hinj (hc.trans ha.symm))⟩
    simp only [hone]
    rw [integral_prod_tsum_pow_one hv, integral_prod_tsum_pow_one hv']
  · obtain ⟨x, r, hxr, hne⟩ := Function.not_injective_iff.1 hinj
    have h2 : 1 < Fintype.card I := Fintype.one_lt_card_iff.2 ⟨x, r, hne⟩
    obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    let e0 : Option (Fin N') ≃ I :=
      Fintype.equivOfCardEq (by simp [Fintype.card_option, hI, hN'])
    let E : Option (Fin N') ≃ I := e0.trans (Equiv.swap (e0 none) x)
    have hE : E none = x := Equiv.swap_apply_left _ _
    have hcard (m : K) : Fintype.card {i : I // g i = m} =
        Fintype.card {o : Option (Fin N') // g (E o) = m} :=
      (Fintype.card_congr (E.subtypeEquiv fun _ => Iff.rfl)).symm
    simp only [hcard]
    have hr : E.symm r ≠ none := fun h => hne (by
      rw [Equiv.symm_apply_eq, hE] at h
      exact h.symm)
    obtain ⟨r0, hr0⟩ := Option.ne_none_iff_exists'.mp hr
    have hEr : E (some r0) = r := by rw [← hr0]; exact E.apply_symm_apply r
    let b : Fin N' → K := fun i => g (E (some i))
    have hbr : b r0 = g (E none) := by
      change g (E (some r0)) = g (E none)
      rw [hEr, hE]
      exact hxr.symm
    have hpt : ∀ o : Option (Fin N'), o.elim (b r0) b = g (E o) := fun o => by
      cases o with
      | none => exact hbr
      | some i => rfl
    have hbs : Function.Surjective b := by
      intro m
      obtain ⟨i, hi⟩ := hg m
      obtain ⟨o, rfl⟩ := E.surjective i
      cases o with
      | none => exact ⟨r0, hbr.trans hi⟩
      | some j => exact ⟨j, hi⟩
    have key := integral_partition_fresh_eq hv hv' hGG hGG' b hbs r0
      (ih N' (by omega))
    simpa only [hpt] using key

include hv hv' hGG hGG' in
/-- Mixed higher power sums of two weight sequences satisfying the same Ghirlanda-Guerra
relations have the same expectation (the moments `S(n₁, …, n_k)` of (2.36)). -/
theorem integral_prod_powerSums_eq_of_ghirlanda_guerra (k : ℕ) (s : Fin k → ℕ)
    (hs : ∀ i, 0 < s i) :
    ∫ ω, ∏ i, ∑' j, v ω j ^ s i ∂P = ∫ ω, ∏ i, ∑' j, v' ω j ^ s i ∂P' := by
  have hcard (m : Fin k) :
      Fintype.card {i : (Σ m : Fin k, Fin (s m)) // i.1 = m} = s m := by
    rw [Fintype.card_congr (Equiv.sigmaSubtype m)]
    exact Fintype.card_fin _
  have := integral_partition_powerSums_eq_of_ghirlanda_guerra hv hv' hGG hGG' _
    (Σ m : Fin k, Fin (s m)) rfl (Fin k) Sigma.fst
    (fun m => ⟨⟨m, ⟨0, hs m⟩⟩, rfl⟩)
  simpa only [hcard] using this

include hv hv' hGG hGG' in
/-- **Theorem 2.8** (uniqueness of the Poisson-Dirichlet law). Two measurable random
nonincreasing nonnegative weight sequences with total mass one that satisfy the
Ghirlanda-Guerra relations of Theorem 2.7 with the same parameter `ζ` have the same law. -/
theorem identDistrib_of_ghirlanda_guerra (hvm : Measurable v) (hv'm : Measurable v')
    (hanti : ∀ᵐ ω ∂P, Antitone (v ω)) (hanti' : ∀ᵐ ω ∂P', Antitone (v' ω)) :
    IdentDistrib v v' P P' := by
  refine identDistrib_of_poissonDirichlet_powerSum_products P P' v v' hvm hv'm ?_ ?_ ?_
  · filter_upwards [hv, hanti] with ω ⟨hw0, hw⟩ ha
    exact mem_poissonDirichletSimplex_of_hasSum hw0 ha hw
  · filter_upwards [hv', hanti'] with ω ⟨hw0, hw⟩ ha
    exact mem_poissonDirichletSimplex_of_hasSum hw0 ha hw
  · intro k s hs
    exact integral_prod_powerSums_eq_of_ghirlanda_guerra hv hv' hGG hGG' k s
      fun i => lt_of_lt_of_le (by norm_num) (hs i)

omit hv hGG hv' hGG' in
/-- The ranked weights of any independent-block realization of the `ζ`-Poisson process have
the same law as every measurable nonincreasing weight sequence with total mass one that
satisfies the Ghirlanda-Guerra relations with parameter `ζ`. In particular `PD(ζ)` is
characterized by (2.34)-(2.35). -/
theorem identDistrib_poissonDirichlet_of_ghirlanda_guerra
    (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      ((poissonMeasure (r n)).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum (fun n => (r n : ENNReal) • ν n))
    (hv'm : Measurable v') (hv' : ∀ᵐ ω ∂P', (∀ a, 0 ≤ v' ω a) ∧ HasSum (v' ω) 1)
    (hanti' : ∀ᵐ ω ∂P', Antitone (v' ω))
    (hGG' : ∀ (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ), Measurable f →
      (n : ℝ) * (∫ ω, ∑' τ : Option (Fin n) → ℕ, (∏ j, v' ω (τ j)) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            if τ (some r₀) = τ none then 1 else 0) ∂P') =
        (1 - ζ) * (∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v' ω (σ k)) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P') +
          ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
            ∫ ω, ∑' σ : Fin n → ℕ, (∏ k, v' ω (σ k)) *
              (f (fun i l => if σ i = σ l then 1 else 0) *
                if σ r₀ = σ j then 1 else 0) ∂P') :
    IdentDistrib (fun ω k => poissonDirichletWeight k
      (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l))) v' P P' := by
  have hae := ae_poissonDirichletWeight ν r hζ hζ1 hBm hB hlaw hμ (fun ω => rfl)
  refine identDistrib_of_ghirlanda_guerra
    (v := fun ω k => poissonDirichletWeight k
      (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)))
    (hae.mono fun ω h => ⟨fun a => (h.2.2.2.1 a).le, h.2.2.1⟩) hv'
    (fun n r₀ f hf => ghirlanda_guerra_poissonDirichlet_of_blocks_parameter
      hζ hζ1 ν r hBm hB hlaw hμ n r₀ f hf) hGG'
    ((measurable_pi_iff.2 measurable_poissonDirichletWeight).comp
      (measurable_poissonCountingMeasure_of_blocks hBm (fun ω => rfl))) hv'm
    (hae.mono fun ω h => h.2.2.2.2) hanti'

end Uniqueness

end SpinGlasses
