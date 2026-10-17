/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities
public import LeanMachineLearning.SpinGlasses.PoissonProcessIndepMarks

/-!
# Lemma 2.3 as a statement about Gibbs measures on block indices

Lemma 2.3 of Panchenko compares replica averages for the tilted and the reference marked Poisson
process. Here both averages are written as Gibbs series over replica tuples of the actual block
indices `(n, l)`, `l < Nₙ`, with weights `uₚ exp (t gₚ) / ∑ᵩ u_q exp (t g_q)`. Writing them on one
probability space is what lets the Gaussian marks `g` be integrated by parts while the counts and
masses are held fixed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- Almost surely every sampled point of the active indices lies in a measurable set `A` that
carries all the mass of the blocks of positive intensity. -/
theorem ae_poissonBlocks_forall_mem {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {A : Set S} (hA : MeasurableSet A) (hν : ∀ n, r n ≠ 0 → ∀ᵐ x ∂ν n, x ∈ A) :
    ∀ᵐ ω ∂P, ∀ n, ∀ l < (B n ω).1, (B n ω).2 l ∈ A := by
  refine ae_all_iff.2 fun n => ?_
  by_cases hn : r n = 0
  · have hN : HasLaw (fun ω => (B n ω).1) Po(0) P := by
      have h := measurePreserving_fst.hasLaw.comp (hlaw n)
      rwa [hn] at h
    filter_upwards [hN.ae_eq_zero_of_poisson_zero] with ω hω l hl
    omega
  · have hsamp : HasLaw (fun ω => (B n ω).2) (Measure.infinitePi fun _ : ℕ => ν n) P :=
      measurePreserving_snd.hasLaw.comp (hlaw n)
    filter_upwards [ae_all_mem_of_hasLaw_infinitePi hsamp hA (hν n hn)] with ω hω l _
    exact hω l


/-- The ζ-Poisson intensity does not charge the nonpositive half-line. -/
theorem zetaPoissonMeasure_Iic_zero (ζ : ℝ) : zetaPoissonMeasure ζ (Set.Iic 0) = 0 := by
  rw [zetaPoissonMeasure, withDensity_apply _ measurableSet_Iic]
  rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0)
    fun x hx => by simp [not_lt.2 (Set.mem_Iic.1 hx)]]
  simp

/-- Almost surely all masses of the Gaussian-marked reference process are positive. -/
theorem ae_poissonDirichlet_gaussian_mass_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ζ : ℝ} (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, ∀ n, ∀ l < (B n ω).1, 0 < ((B n ω).2 l).1 := by
  have hA : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hmem : ∀ n, r n ≠ 0 → ∀ᵐ x ∂ν n, x ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := by
    intro n hn
    rw [ae_iff]
    have hset : {x : ℝ × ℝ | ¬ x ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)} =
        Set.Iic 0 ×ˢ Set.univ := by
      ext x; simp
    rw [hset]
    have hle := Measure.le_iff'.1 (Measure.le_sum (fun n => (r n : ℝ≥0∞) • ν n) n)
      (Set.Iic 0 ×ˢ Set.univ)
    rw [← hμ, Measure.prod_prod, zetaPoissonMeasure_Iic_zero, zero_mul] at hle
    rw [Measure.smul_apply, smul_eq_mul, nonpos_iff_eq_zero, mul_eq_zero] at hle
    exact hle.resolve_left (by simpa using hn)
  filter_upwards [ae_poissonBlocks_forall_mem ν r hlaw hA hmem] with ω h n l hl
  exact (h n l hl).1

/-- Almost surely the Gaussian-marked reference process has a summable family of
positive masses on its active block indices. These are the deterministic Gibbs weights
needed after conditioning on the counts and masses. -/
theorem ae_poissonDirichlet_gaussian_summable_masses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, Summable (fun p : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
      ((B p.1.1 ω).2 p.1.2).1) := by
  have hν : ∀ n, IsProbabilityMeasure ((ν n).map Prod.fst) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw measurable_fst
  have hμ0 := eq_sum_map_fst_of_prod_eq ν r hμ
  have hfin := ae_lintegral_poisson_lt_top_of_blocks
    (P := P) (M := fun ω => poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => ((B n ω).2 l).1)) (fun n => (ν n).map Prod.fst) r hζ hζ1
    hCm hClaw hμ0 (fun _ => rfl)
  have hpos := ae_poissonDirichlet_gaussian_mass_pos ν r hlaw hμ
  filter_upwards [hfin, hpos] with ω hω hp
  have hsum := lintegral_poissonCountingMeasure_restrict_eq_tsum
    (fun n => (B n ω).1) (fun n l => ((B n ω).2 l).1)
    (A := Set.Ioi (0 : ℝ)) measurableSet_Ioi ENNReal.measurable_ofReal
  simp only [Set.mem_Ioi] at hsum
  rw [hsum] at hω
  have hω' : (∑' q : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      ENNReal.ofReal (((B q.1.1 ω).2 q.1.2).1)) < ∞ := by
    convert hω using 1
    apply tsum_congr
    intro q
    simp [hp q.1.1 q.1.2 q.2]
  exact summable_of_tsum_ofReal_lt_top (fun p => (hp _ _ p.2).le) hω'

/-- **Lemma 2.3's replica average as a Gibbs series over block indices.** For a counting measure
whose active atoms `(xₚ, yₚ)` have positive masses and are pairwise distinct, the ratio of
order-free integrals
`∫ (∏ₗ xₗ) f(R) ∏ₗ yₗ^{kₗ} dM^{⊗n} / ∫ ∏ₗ xₗ dM^{⊗n}` against `M` restricted to `{x > 0}` is the
series `∑_σ (∏ₗ x_{σₗ} / ∑ₚ xₚ) f(1{σₗ = σₗ'}) ∏ₗ y_{σₗ}^{kₗ}` over replica tuples of block
indices: the overlap of two atoms is the indicator that their indices coincide. -/
theorem integral_div_pi_poissonCountingMeasure_restrict_pos_eq_tsum
    (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ × ℝ)
    [SigmaFinite ((poissonCountingMeasure N X).restrict (Set.Ioi 0 ×ˢ Set.univ))]
    (hpos : ∀ p : {p : ℕ × ℕ // p.2 < N p.1}, 0 < (X p.1.1 p.1.2).1)
    (hinj : ∀ a b : {p : ℕ × ℕ // p.2 < N p.1}, X a.1.1 a.1.2 = X b.1.1 b.1.2 → a = b)
    (n : ℕ) (k : Fin n → ℕ) (f : (Fin n → Fin n → ℝ) → ℝ) :
    (∫ q, (∏ l, (q l).1) * (f (fun l l' => if q l = q l' then 1 else 0) * ∏ l, (q l).2 ^ k l)
        ∂Measure.pi fun _ : Fin n =>
          (poissonCountingMeasure N X).restrict (Set.Ioi 0 ×ˢ Set.univ)) /
      (∫ q, ∏ l, (q l).1 ∂Measure.pi fun _ : Fin n =>
          (poissonCountingMeasure N X).restrict (Set.Ioi 0 ×ˢ Set.univ)) =
    ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < N p.1},
      (∏ i, (X (σ i).1.1 (σ i).1.2).1 / ∑' p : {p : ℕ × ℕ // p.2 < N p.1},
          (X p.1.1 p.1.2).1) *
        (f (fun i j => if σ i = σ j then 1 else 0) * ∏ i, (X (σ i).1.1 (σ i).1.2).2 ^ k i) := by
  have hA : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  rw [integral_div_pi_poissonCountingMeasure_restrict_eq_tsum N X hA Prod.fst n]
  have hW : ∑' p : {p : ℕ × ℕ // p.2 < N p.1},
      (if X p.1.1 p.1.2 ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) then (X p.1.1 p.1.2).1 else 0) =
      ∑' p : {p : ℕ × ℕ // p.2 < N p.1}, (X p.1.1 p.1.2).1 :=
    tsum_congr fun p => by simp [hpos p]
  rw [hW]
  refine tsum_congr fun σ => ?_
  have hg : ∀ i, X (σ i).1.1 (σ i).1.2 ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := fun i => by
    simpa using hpos (σ i)
  have hR : (fun i j => if X (σ i).1.1 (σ i).1.2 = X (σ j).1.1 (σ j).1.2 then (1 : ℝ) else 0) =
      fun i j => if σ i = σ j then 1 else 0 := by
    funext i j
    exact if_congr ⟨hinj _ _, fun h => by rw [h]⟩ rfl rfl
  simp only [hg, implies_true, ↓reduceIte, hR]

/-- The intensity of the transformed process of Lemma 2.3 is the pushforward of the reference
intensity under `T(u, g) = (u, (exp (t (g - tζ/2)), g - tζ))`, so the transformed process can be
realized on the probability space of the reference blocks by applying `T` to every atom. -/
theorem intensity_tilt_eq_sum_map {ζ : ℝ} (t : ℝ) (ν' : ℕ → Measure (ℝ × ℝ)) (r' : ℕ → ℝ≥0)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n) :
    (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum fun n => (r' n : ℝ≥0∞) •
        (ν' n).map (fun p : ℝ × ℝ => (p.1, (Real.exp (t * (p.2 - t * ζ / 2)), p.2 - t * ζ))) := by
  have hh : Measurable fun g : ℝ => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ) := by fun_prop
  have hT : Measurable fun p : ℝ × ℝ =>
      (p.1, (Real.exp (t * (p.2 - t * ζ / 2)), p.2 - t * ζ)) := by fun_prop
  rw [← poissonIntensity_map ν' r' hT, ← hμ']
  have h := Measure.map_prod_map (zetaPoissonMeasure ζ) (gaussianReal 0 1) measurable_id hh
  rw [Measure.map_id] at h
  exact h


/-- **Lemma 2.3 in block-index Gibbs form, on one probability space.** For the Gaussian-marked
reference process with atoms `(uₚ, gₚ)`, `p = (n, l)`, `l < Nₙ`, and an overlap observable `f`,
the expected tilted Gibbs average (weights `uₚ exp (t gₚ)`, marks `gₚ - tζ`) equals the expected
reference Gibbs average (weights `uₚ`, marks `gₚ`). Overlaps are index coincidences. -/
theorem integral_gibbs_tilt_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B' : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' P)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod (Measure.infinitePi fun _ : ℕ => ν' n)) P)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n)
    (n : ℕ) (k : Fin n → ℕ) {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).1 * Real.exp (t * ((B' (σ i).1.1 ω).2 (σ i).1.2).2) /
          ∑' p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
            ((B' p.1.1 ω).2 p.1.2).1 * Real.exp (t * ((B' p.1.1 ω).2 p.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, (((B' (σ i).1.1 ω).2 (σ i).1.2).2 - t * ζ) ^ k i) ∂P =
      ∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).1 /
          ∑' p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1}, ((B' p.1.1 ω).2 p.1.2).1) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∏ i, ((B' (σ i).1.1 ω).2 (σ i).1.2).2 ^ k i) ∂P := by
  let Tt : ℝ × ℝ → ℝ × (ℝ × ℝ) :=
    fun p => (p.1, (Real.exp (t * (p.2 - t * ζ / 2)), p.2 - t * ζ))
  have hTt : Measurable Tt := by fun_prop
  have hν : ∀ m, IsProbabilityMeasure ((ν' m).map Tt) := fun m => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm' hB' hlaw' hTt
  have hμt := intensity_tilt_eq_sum_map t ν' r' hμ'
  have hid := identDistrib_replica_average_poissonDirichlet_gaussian hζ t
    (fun m => (ν' m).map Tt) r' hCm hCi hClaw hμt ν' r' hBm' hB' hlaw' hμ' n k hf
  have hint := hid.integral_eq
  have hpos := ae_poissonDirichlet_gaussian_mass_pos ν' r' hlaw' hμ'
  have hnull : ∀ m, r' m ≠ 0 → NullSingletonClass (ν' m) := by
    intro m hm
    have h := nullSingletonClass_map_block ν' r' measurable_id
      (by rw [Measure.map_id, ← hμ']; infer_instance) hm
    rwa [Measure.map_id] at h
  have hdist := ae_poissonBlocks_point_eq_iff_index_eq ν' r' hBm' hB' hlaw' hnull
  have hsf0 := ae_sigmaFinite_poissonDirichlet_gaussian_restrict_pos hζ ν' r' hBm' hB' hlaw' hμ'
  have hshell := ae_forall_measure_Ioi_inv_succ_transform_lt_top hζ t
    (fun m => (ν' m).map Tt) r' hCm hCi hClaw hμt ν' r' hBm' hB' hlaw' hμ'
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => (p.1 * p.2.1, p.2.2) := by fun_prop
  refine (integral_congr_ae ?_).trans (hint.trans (integral_congr_ae ?_))
  · filter_upwards [hpos, hdist, hshell] with ω h1 h2 h3
    have hmap := poissonCountingMeasure_map (fun j => (B' j ω).1)
      (fun j l => Tt ((B' j ω).2 l)) hm
    have h3' : ∀ k : ℕ, poissonCountingMeasure (fun j => (B' j ω).1)
        (fun j l => (((B' j ω).2 l).1 * Real.exp (t * (((B' j ω).2 l).2 - t * ζ / 2)),
          ((B' j ω).2 l).2 - t * ζ)) (Set.Ioi (1 / ((k : ℝ) + 1)) ×ˢ Set.univ) < ∞ := by
      intro k
      have := h3 k
      rwa [hmap] at this
    have hsf := sigmaFinite_poissonCountingMeasure_restrict_pos_of_shells
      (fun j => (B' j ω).1) (fun j l => (((B' j ω).2 l).1 *
        Real.exp (t * (((B' j ω).2 l).2 - t * ζ / 2)), ((B' j ω).2 l).2 - t * ζ)) h3'
    let _ := hsf
    have hpos' : ∀ p : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        0 < ((B' p.1.1 ω).2 p.1.2).1 * Real.exp (t * (((B' p.1.1 ω).2 p.1.2).2 - t * ζ / 2)) :=
      fun p => mul_pos (h1 p.1.1 p.1.2 p.2) (Real.exp_pos _)
    have hinj' : ∀ a b : {p : ℕ × ℕ // p.2 < (B' p.1 ω).1},
        (((B' a.1.1 ω).2 a.1.2).1 * Real.exp (t * (((B' a.1.1 ω).2 a.1.2).2 - t * ζ / 2)),
          ((B' a.1.1 ω).2 a.1.2).2 - t * ζ) =
        (((B' b.1.1 ω).2 b.1.2).1 * Real.exp (t * (((B' b.1.1 ω).2 b.1.2).2 - t * ζ / 2)),
          ((B' b.1.1 ω).2 b.1.2).2 - t * ζ) → a = b := by
      intro a b hab
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj hab
      have hg : ((B' a.1.1 ω).2 a.1.2).2 = ((B' b.1.1 ω).2 b.1.2).2 := sub_left_injective h₂
      rw [hg] at h₁
      have hu := mul_right_cancel₀ (Real.exp_pos _).ne' h₁
      exact (h2 a b).1 (Prod.ext hu hg)
    rw [hmap]
    rw [integral_div_pi_poissonCountingMeasure_restrict_pos_eq_tsum _ _ hpos' hinj' n k f]
    have hc0 : Real.exp (-(t * t * ζ / 2)) ≠ 0 := (Real.exp_pos _).ne'
    have hw : ∀ u g : ℝ, u * Real.exp (t * (g - t * ζ / 2)) =
        Real.exp (-(t * t * ζ / 2)) * (u * Real.exp (t * g)) := by
      intro u g
      have : t * (g - t * ζ / 2) = -(t * t * ζ / 2) + t * g := by ring
      rw [this, Real.exp_add]
      ring
    simp only [Tt, hw, tsum_mul_left, mul_div_mul_left _ _ hc0]
  · filter_upwards [hpos, hdist, hsf0] with ω h1 h2 h3
    let _ := h3
    exact (integral_div_pi_poissonCountingMeasure_restrict_pos_eq_tsum (fun j => (B' j ω).1)
      (fun j l => (B' j ω).2 l) (fun p => h1 p.1.1 p.1.2 p.2) (fun a b h => (h2 a b).1 h)
      n k f)

end SpinGlasses
