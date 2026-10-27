/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraCentering

/-!
# Final overlap algebra for Gaussian-marked Poisson--Dirichlet blocks

The marked tilt identity and the Gaussian integration-by-parts correction are
already available. This file transfers the remaining finite-valued overlap
observables through the Poisson marking invariance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- A finite overlap observable, multiplied by one zero-one overlap, is again
bounded on index-coincidence matrices. -/
theorem bound_index_overlap_mul_entry
    {J α : Type*} [Finite J] [DecidableEq α]
    (f : (J → J → ℝ) → ℝ) (i j : J) :
    ∃ M : ℝ, ∀ σ : J → α,
      |f (fun a b => if σ a = σ b then 1 else 0) *
        (if σ i = σ j then 1 else 0)| ≤ M :=
  exists_bound_index_overlap_observable (α := α) (fun R => f R * R i j)

/-- The old-replica overlap sum is bounded uniformly over every index array. -/
theorem bound_index_overlap_sum
    {J α : Type*} [Fintype J] [DecidableEq α]
    (f : (J → J → ℝ) → ℝ) (i : J) :
    ∃ M : ℝ, ∀ σ : J → α,
      |f (fun a b => if σ a = σ b then 1 else 0) *
        (∑ j : J, if σ i = σ j then 1 else 0)| ≤ M :=
  exists_bound_index_overlap_observable (α := α) (fun R => f R * ∑ j, R i j)

/-- On the split-block probability space the old-overlap series separates into
its diagonal term and a finite sum of off-diagonal overlap series. -/
theorem ae_poissonDirichlet_gaussian_old_overlap_split
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
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ) :
    ∀ᵐ ω ∂P,
      let α := {p : ℕ × ℕ // p.2 < (B p.1 ω).1}
      let w : α → ℝ := fun a =>
        ((B a.1.1 ω).2 a.1.2).1 * Real.exp (((B a.1.1 ω).2 a.1.2).2) /
          ∑' b : α, ((B b.1.1 ω).2 b.1.2).1 *
            Real.exp (((B b.1.1 ω).2 b.1.2).2)
      (∑' σ : Fin n → α, (∏ j, w (σ j)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ∑ j : Fin n, if σ r₀ = σ j then 1 else 0)) =
        (∑' σ : Fin n → α, (∏ j, w (σ j)) *
          f (fun i j => if σ i = σ j then 1 else 0)) +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∑' σ : Fin n → α, (∏ k, w (σ k)) *
            (f (fun i l => if σ i = σ l then 1 else 0) *
              if σ r₀ = σ j then 1 else 0) := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω m l => ((B m ω).2 l).2
  have htilt : ∀ᵐ ω ∂P,
      (∑' p : ℕ × ℕ, ENNReal.ofReal
        (if p.2 < (Z ω p.1).1 then
          (Z ω p.1).2 p.2 * Real.exp (G ω p.1 p.2) else 0)) < ⊤ := by
    filter_upwards [ae_poissonDirichlet_gaussian_tilt_summable_blocks hζ hζ1 1 ν r
      hBm hB hlaw hμ] with ω h
    simpa only [one_mul] using h
  have hmass := ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
    (fun m => (ν m).prod (gaussianReal 0 1)) r hBm hB hlaw hμ
  filter_upwards [htilt, hmass] with ω ht ⟨hn, hp, hs⟩
  let α := {p : ℕ × ℕ // p.2 < (B p.1 ω).1}
  let _ : Nonempty α := hn
  let v : α → ℝ := fun a =>
    ((B a.1.1 ω).2 a.1.2).1 * Real.exp (((B a.1.1 ω).2 a.1.2).2)
  have hv (a : α) : 0 ≤ v a := mul_nonneg (hp a).le (Real.exp_pos _).le
  have hts0 : Summable (fun p : ℕ × ℕ =>
      if p.2 < (Z ω p.1).1 then
        (Z ω p.1).2 p.2 * Real.exp (G ω p.1 p.2) else 0) := by
    apply summable_of_tsum_ofReal_lt_top (fun p => ?_) ht
    split_ifs with h
    · exact mul_nonneg (hp ⟨p, h⟩).le (Real.exp_pos _).le
    · exact le_refl 0
  have hvs : Summable v :=
    (summable_subtype_guard_iff (fun p : ℕ × ℕ => p.2 < (Z ω p.1).1)
      (fun p : ℕ × ℕ => (Z ω p.1).2 p.2 * Real.exp (G ω p.1 p.2))).2 hts0
  let w : α → ℝ := fun a => v a / ∑' b, v b
  have hw (a : α) : 0 ≤ w a := div_nonneg (hv a) (tsum_nonneg hv)
  have hws : Summable w := hvs.div_const _
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  have hM' (σ : Fin n → α) :
      |f (fun i j => if σ i = σ j then 1 else 0)| ≤ M := by
    simpa only [Subtype.coe_inj] using hM (fun j => (σ j).1)
  exact gibbs_old_replica_self_overlap w hw hws r₀
    (fun σ => f (fun i j => if σ i = σ j then 1 else 0)) hM'

/-- The extra-replica overlap observable is an ordinary measurable function of
the `(n+1)`-replica matrix, with the fresh replica in the last coordinate. -/
theorem measurable_fresh_replica_overlap
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    Measurable (fun R : Fin (n + 1) → Fin (n + 1) → ℝ =>
      f (fun i j => R (Fin.castSucc i) (Fin.castSucc j)) *
        R (Fin.castSucc r₀) (Fin.last n)) := by
  fun_prop

/-- Reindex the extra-replica coincidence observable, preserving its full
replica product and the restriction of the overlap matrix. -/
theorem tsum_fresh_replica_overlap_reindex
    {α : Type*} [DecidableEq α] (n : ℕ) (r₀ : Fin n)
    (w : α → ℝ) (f : (Fin n → Fin n → ℝ) → ℝ) :
    (∑' τ : Option (Fin n) → α, (∏ o, w (τ o)) *
      (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
        if τ (some r₀) = τ none then 1 else 0)) =
    ∑' σ : Fin (n + 1) → α, (∏ j, w (σ j)) *
      (f (fun i j => if σ (Fin.castSucc i) = σ (Fin.castSucc j) then 1 else 0) *
        if σ (Fin.castSucc r₀) = σ (Fin.last n) then 1 else 0) := by
  classical
  rw [tsum_option_fin_replica_eq n w]
  apply tsum_congr
  intro σ
  simp only [Function.comp_apply, finSuccEquivLast_symm_some,
    finSuccEquivLast_symm_none]

/-- Zero-exponent Gaussian marking invariance transfers any finite-valued
overlap observable from tilted to untilted Poisson block Gibbs weights. -/
theorem integral_poissonDirichlet_gaussian_overlap_tilt_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (f : (Fin n → Fin n → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        f (fun i j => if σ i = σ j then 1 else 0) ∂P) =
    ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1) *
        f (fun i j => if σ i = σ j then 1 else 0) ∂P := by
  have h := integral_gibbs_tilt_eq hζ t
    (fun m => (ν m).prod (gaussianReal 0 1)) r hBm hB hlaw hμ
    n (fun _ => 0) hf
  convert h using 1
  · congr 1
    funext ω
    apply tsum_congr
    intro σ
    simp only [pow_zero, Finset.prod_const_one, mul_one]
  · congr 1
    funext ω
    apply tsum_congr
    intro σ
    simp only [pow_zero, Finset.prod_const_one, mul_one]

/-- The fresh-replica overlap average has the same expectation under the
Gaussian tilt as under the reference Poisson--Dirichlet Gibbs weights. -/
theorem integral_poissonDirichlet_gaussian_fresh_overlap_tilt_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ)
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
    (∫ ω, ∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
          Real.exp (((B (τ j).1.1 ω).2 (τ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P) =
    ∫ ω, ∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P := by
  let f' : (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ := fun R =>
    f (fun i j => R (Fin.castSucc i) (Fin.castSucc j)) *
      R (Fin.castSucc r₀) (Fin.last n)
  have hf' : Measurable f' := measurable_fresh_replica_overlap n r₀ f hf
  have h := integral_poissonDirichlet_gaussian_overlap_tilt_eq hζ 1
    ν r hBm hB hlaw hμ (n + 1) f' hf'
  calc
    _ = ∫ ω, ∑' σ : Fin (n + 1) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        f' (fun i j => if σ i = σ j then 1 else 0) ∂P := by
      congr 1
      funext ω
      simpa only [f', Function.comp_apply] using
        tsum_fresh_replica_overlap_reindex n r₀
          (fun a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (((B a.1.1 ω).2 a.1.2).2) /
              ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
                ((B b.1.1 ω).2 b.1.2).1 *
                  Real.exp (((B b.1.1 ω).2 b.1.2).2)) f
    _ = _ := by
      simpa only [one_mul] using h.trans (by
        congr 1
        funext ω
        simpa only [f', Function.comp_apply] using
          (tsum_fresh_replica_overlap_reindex n r₀
            (fun a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
              ((B a.1.1 ω).2 a.1.2).1 /
                ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
                  ((B b.1.1 ω).2 b.1.2).1) f).symm)


/-- Every off-diagonal overlap expectation is invariant under the unit
Gaussian tilt, with no boundedness hypothesis on the matrix observable. -/
theorem integral_poissonDirichlet_gaussian_old_overlap_tilt_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ j : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
          Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i l => if σ i = σ l then 1 else 0) *
          if σ r₀ = σ j then 1 else 0) ∂P) =
    ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1) *
        (f (fun i l => if σ i = σ l then 1 else 0) *
          if σ r₀ = σ j then 1 else 0) ∂P := by
  let f' : (Fin n → Fin n → ℝ) → ℝ := fun R => f R * R r₀ j
  have hf' : Measurable f' := by fun_prop
  simpa only [f', one_mul] using
    integral_poissonDirichlet_gaussian_overlap_tilt_eq hζ 1
      ν r hBm hB hlaw hμ n f' hf'

/-- Expected old-replica overlaps split into their self-overlap and the
sum over the remaining replicas. -/
theorem integral_poissonDirichlet_gaussian_old_overlap_split
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
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ) :
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
          Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ∑ j : Fin n, if σ r₀ = σ j then 1 else 0) ∂P) =
      (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
            Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
          ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
                Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
              ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
                ((B a.1.1 ω).2 a.1.2).1 *
                  Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
              (f (fun i l => if σ i = σ l then 1 else 0) *
                if σ r₀ = σ j then 1 else 0) ∂P := by
  let F : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  obtain ⟨Msum, hMsum⟩ := bound_index_overlap_sum (α := ℕ × ℕ) f r₀
  have hplain := integrable_poissonDirichlet_gaussian_tilt_overlap
    hζ hζ1 1 ν r hBm hB hlaw hμ F M hM
  have hterms (j : Fin n) := integrable_poissonDirichlet_gaussian_tilt_overlap
    hζ hζ1 1 ν r hBm hB hlaw hμ
      (fun σ => F σ * if σ r₀ = σ j then 1 else 0)
      M (by
        intro σ
        dsimp [F]
        split_ifs
        · simpa using hM σ
        · simpa using (abs_nonneg _).trans (hM σ))
  have hsum := integrable_poissonDirichlet_gaussian_tilt_overlap
    hζ hζ1 1 ν r hBm hB hlaw hμ
      (fun σ => F σ * ∑ j : Fin n, if σ r₀ = σ j then 1 else 0)
      Msum hMsum
  have hsplit := ae_poissonDirichlet_gaussian_old_overlap_split
    hζ hζ1 ν r hBm hB hlaw hμ n r₀ f
  have hplain' : Integrable (fun ω =>
      ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
          Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
          f (fun i j => if σ i = σ j then 1 else 0)) P := by
    simpa only [one_mul, F, Subtype.coe_inj] using hplain
  have hterms' (j : Fin n) : Integrable (fun ω =>
      ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
          Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i l => if σ i = σ l then 1 else 0) *
            if σ r₀ = σ j then 1 else 0)) P := by
    simpa only [one_mul, F, Subtype.coe_inj] using hterms j
  have hsum' : Integrable (fun ω =>
      ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
          Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∑ j : Fin n, if σ r₀ = σ j then 1 else 0)) P := by
    simpa only [one_mul, F, Subtype.coe_inj] using hsum
  rw [integral_congr_ae hsplit]
  rw [integral_add hplain'
    (integrable_finsetSum (Finset.univ.erase r₀) fun j _ => hterms' j)]
  congr 1
  exact integral_finsetSum _ fun j _ => hterms' j

/-- The fresh-replica coincidence series is integrable on the split-block
space; reindexing reduces this to bounded tilted overlap integrability. -/
theorem integrable_poissonDirichlet_gaussian_fresh_overlap
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
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ) :
    Integrable (fun ω =>
      ∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
            Real.exp (((B (τ j).1.1 ω).2 (τ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            if τ (some r₀) = τ none then 1 else 0)) P := by
  let F : (Option (Fin n) → ℕ × ℕ) → ℝ := fun τ =>
    f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
      if τ (some r₀) = τ none then 1 else 0
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  have hF (τ : Option (Fin n) → ℕ × ℕ) : |F τ| ≤ M := by
    dsimp [F]
    split_ifs
    · simpa using hM (fun i => τ (some i))
    · simpa using (abs_nonneg _).trans (hM (fun i => τ (some i)))
  have h := integrable_poissonDirichlet_gaussian_tilt_overlap
    hζ hζ1 1 ν r hBm hB hlaw hμ F M hF
  simpa only [one_mul, F, Subtype.coe_inj] using h

/-- Equation (2.35), before eliminating the Poisson--Dirichlet parameter:
Gaussian IBP and marking invariance give the block-index overlap relation. -/
theorem ghirlanda_guerra_poissonDirichlet_blocks_parameter
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
      ∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            if τ (some r₀) = τ none then 1 else 0) ∂P) =
      (1 - ζ) * (∫ ω,
        ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 /
            ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
              ((B a.1.1 ω).2 a.1.2).1) *
            f (fun i j => if σ i = σ j then 1 else 0) ∂P) +
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase r₀,
        ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 /
            ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
              ((B a.1.1 ω).2 a.1.2).1) *
            (f (fun i l => if σ i = σ l then 1 else 0) *
              if σ r₀ = σ j then 1 else 0) ∂P := by
  have hmark := integral_poissonDirichlet_gaussian_unit_tilt_mark
    hζ hζ1 ν r hBm hB hlaw hμ n r₀ f hf
  have hibp := integral_poissonDirichlet_gaussian_overlap_correction
    hζ hζ1 1 ν r hBm hB hlaw hμ n r₀ f hf
  have hsplit := integral_poissonDirichlet_gaussian_old_overlap_split
    hζ hζ1 ν r hBm hB hlaw hμ n r₀ f
  have hplain := integral_poissonDirichlet_gaussian_overlap_tilt_eq
    hζ 1 ν r hBm hB hlaw hμ n f hf
  have hold (j : Fin n) := integral_poissonDirichlet_gaussian_old_overlap_tilt_eq
    hζ ν r hBm hB hlaw hμ n r₀ j f hf
  have hfresh := integral_poissonDirichlet_gaussian_fresh_overlap_tilt_eq
    hζ ν r hBm hB hlaw hμ n r₀ f hf
  have hL := integrable_poissonDirichlet_gaussian_tilt_overlap
    hζ hζ1 1 ν r hBm hB hlaw hμ
      (fun σ : Fin n → ℕ × ℕ =>
        f (fun i j => if σ i = σ j then 1 else 0) *
          ∑ j : Fin n, if σ r₀ = σ j then 1 else 0)
      (Classical.choose (bound_index_overlap_sum (α := ℕ × ℕ) f r₀))
      (Classical.choose_spec (bound_index_overlap_sum (α := ℕ × ℕ) f r₀))
  have hR := integrable_poissonDirichlet_gaussian_fresh_overlap
    hζ hζ1 ν r hBm hB hlaw hμ n r₀ f
  have hL' : Integrable (fun ω =>
      ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
          Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∑ j : Fin n, if σ r₀ = σ j then 1 else 0)) P := by
    simpa only [one_mul, Subtype.coe_inj] using hL
  have hcorr : (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 *
          Real.exp (((B (σ k).1.1 ω).2 (σ k).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ∑ j : Fin n, if σ r₀ = σ j then 1 else 0) ∂P) =
    (∫ ω, ∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
          Real.exp (((B (τ j).1.1 ω).2 (τ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          if τ (some r₀) = τ none then 1 else 0) ∂P) * n +
      ζ * (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          f (fun i j => if σ i = σ j then 1 else 0) ∂P) := by
    simp only [one_mul] at hibp
    rw [integral_sub hL' (hR.const_mul n), integral_const_mul] at hibp
    rw [hmark] at hibp
    linarith
  have hplain' := hplain
  simp only [one_mul] at hplain'
  simp only [one_mul] at hibp
  rw [integral_sub hL' (hR.const_mul n), integral_const_mul] at hibp
  rw [hmark] at hibp
  have hlin := hcorr
  rw [hsplit] at hlin
  rw [hplain'] at hlin
  simp_rw [hold] at hlin
  rw [hfresh] at hlin
  linarith

/-- An active Poisson block has total normalized mass one, almost surely. -/
theorem ae_poissonDirichlet_gaussian_normalized_mass_one
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
    ∀ᵐ ω ∂P,
      ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        ((B a.1.1 ω).2 a.1.2).1 /
          ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B b.1.1 ω).2 b.1.2).1 = 1 := by
  filter_upwards [ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
    (fun m => (ν m).prod (gaussianReal 0 1)) r hBm hB hlaw hμ]
    with ω ⟨hn, hp, hs⟩
  let _ : Nonempty {p : ℕ × ℕ // p.2 < (B p.1 ω).1} := hn
  have hpos : 0 < ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      ((B b.1.1 ω).2 b.1.2).1 :=
    hs.tsum_pos (fun a => (hp a).le) (Classical.choice hn)
      (hp (Classical.choice hn))
  exact tsum_div_tsum_eq_one hpos

/-- The one-replica Gibbs overlap average is identically one almost surely. -/
theorem ae_poissonDirichlet_gaussian_one_replica_average
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
    ∀ᵐ ω ∂P,
      (∑' σ : Fin 1 → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          (1 : ℝ)) = 1 := by
  filter_upwards [ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
    (fun m => (ν m).prod (gaussianReal 0 1)) r hBm hB hlaw hμ]
    with ω ⟨hn, hp, hs⟩
  let _ : Nonempty {p : ℕ × ℕ // p.2 < (B p.1 ω).1} := hn
  let w : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} → ℝ := fun a =>
    ((B a.1.1 ω).2 a.1.2).1 /
      ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        ((B b.1.1 ω).2 b.1.2).1
  have hpos : 0 < ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      ((B b.1.1 ω).2 b.1.2).1 :=
    hs.tsum_pos (fun a => (hp a).le) (Classical.choice hn) (hp (Classical.choice hn))
  have hw (a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1}) : 0 ≤ w a :=
    div_nonneg (hp a).le hpos.le
  have hws : Summable w := hs.div_const _
  simpa only [mul_one, w] using
    (tsum_prod_pi (J := Fin 1) (f := fun _ => w)
      (fun _ a => hw a) (fun _ => hws)).trans (by
        simp only [w, tsum_div_tsum_eq_one hpos, Finset.prod_const_one])

/-- Equation (2.34): the expected coincidence overlap of two replicas
sampled from the unmarked Poisson--Dirichlet Gibbs weights is `1 - ζ`. -/
theorem poissonDirichlet_blocks_expected_overlap_eq_one_sub_zeta
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
    (∫ ω, ∑' τ : Option (Fin 1) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1) *
        (if τ (some 0) = τ none then (1 : ℝ) else 0) ∂P) = 1 - ζ := by
  have h := ghirlanda_guerra_poissonDirichlet_blocks_parameter
    hζ hζ1 ν r hBm hB hlaw hμ 1 0 (fun _ => 1) measurable_const
  have havg := ae_poissonDirichlet_gaussian_one_replica_average
    hζ hζ1 ν r hBm hB hlaw hμ
  have hone : (∫ ω, ∑' σ : Fin 1 → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1) * (1 : ℝ) ∂P) = 1 := by
    rw [integral_congr_ae havg]
    simp
  have hempty : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simp only [mul_one, one_mul, hempty, Finset.sum_empty] at h
  have hone' : (∫ ω, ∑' σ : Fin 1 → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      ∏ k, ((B (σ k).1.1 ω).2 (σ k).1.2).1 /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 ∂P) = 1 := by
    simpa only [mul_one] using hone
  rw [hone'] at h
  simpa only [Nat.cast_one, one_mul, mul_one, add_zero] using h

/-- Equation (2.34) as the expected sum of squared normalized *block*
weights. Ranking the atoms to `poissonDirichletWeight` is a separate bridge. -/
theorem poissonDirichlet_blocks_expected_weight_sq_eq_one_sub_zeta
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
    (∫ ω, ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (((B a.1.1 ω).2 a.1.2).1 /
        ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B b.1.1 ω).2 b.1.2).1) ^ 2 ∂P) = 1 - ζ := by
  have hbase := poissonDirichlet_blocks_expected_overlap_eq_one_sub_zeta
    hζ hζ1 ν r hBm hB hlaw hμ
  have hpoint : ∀ᵐ ω ∂P,
      (∑' τ : Option (Fin 1) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1) *
          (if τ (some 0) = τ none then (1 : ℝ) else 0)) =
      ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (((B a.1.1 ω).2 a.1.2).1 /
          ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B b.1.1 ω).2 b.1.2).1) ^ 2 := by
    filter_upwards [ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
      (fun m => (ν m).prod (gaussianReal 0 1)) r hBm hB hlaw hμ]
      with ω ⟨_, hp, hs⟩
    let w : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} → ℝ := fun a =>
      ((B a.1.1 ω).2 a.1.2).1 /
        ∑' b : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B b.1.1 ω).2 b.1.2).1
    have hnonneg (a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1}) : 0 ≤ w a :=
      div_nonneg (hp a).le (tsum_nonneg fun b => (hp b).le)
    have hsum : Summable w := hs.div_const _
    have hreindex := tsum_option_fin_replica_eq 1 w
      (fun τ => if τ (some 0) = τ none then (1 : ℝ) else 0)
    rw [hreindex]
    have hall := tsum_prod_pi_all_eq (I := Fin 2) hnonneg hsum
    rw [Fintype.card_fin] at hall
    refine Eq.trans (tsum_congr fun σ => ?_) hall
    have hiff : (σ ∘ finSuccEquivLast.symm) (some 0) = (σ ∘ finSuccEquivLast.symm) none ↔
        ∀ i j : Fin 2, σ i = σ j := by
      simp only [Function.comp_apply, finSuccEquivLast_symm_some,
        finSuccEquivLast_symm_none]
      refine ⟨fun h i j => ?_, fun h => h _ _⟩
      change σ 0 = σ 1 at h
      fin_cases i <;> fin_cases j
      exacts [rfl, h, h.symm, rfl]
    by_cases h : ∀ i j : Fin 2, σ i = σ j
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]
  rw [← integral_congr_ae hpoint]
  exact hbase

end SpinGlasses
