/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeParisiTree

/-!
# Moments of the marked partition sum

The vertex data model for the cascade: positivity of all ranked atoms, measurability of the marked
partition sum, and the finiteness of its `a`-th moment (the analogue of Lemma 2.4 with a final-level
mark).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- Independent ζ-Poisson blocks have positive finite ranked atoms almost surely. -/
theorem ae_infinitePi_blocks_atoms_pos_finite {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k) :
    ∀ᵐ b ∂(Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)),
      ∀ m, nthLargestAtom m (poissonCountingMeasure
        (fun k => (b k).1) (fun k l => (b k).2 l)) ≠ 0 ∧
      nthLargestAtom m (poissonCountingMeasure
        (fun k => (b k).1) (fun k l => (b k).2 l)) ≠ ∞ := by
  have hBm : ∀ k, Measurable fun b : ℕ → ℕ × (ℕ → ℝ) => b k := fun k => measurable_pi_apply k
  have hB : iIndepFun (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k)
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) :=
    iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
  have hlaw : ∀ k, HasLaw (fun b : ℕ → ℕ × (ℕ → ℝ) => b k)
      (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k))
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) :=
    fun k => hasLaw_eval_infinitePi
      (fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) k
  have hM : ∀ b : ℕ → ℕ × (ℕ → ℝ), (poissonCountingMeasure
      (fun k => (b k).1) (fun k l => (b k).2 l)) = poissonCountingMeasure
      (fun n => ((fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k) n b).1)
      (fun n l => ((fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k) n b).2 l) := fun b => rfl
  have h := ae_poissonDirichletWeight (P := Measure.infinitePi fun k =>
      Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) (ζ := ζ) nu rate hζ0 hζ1 hBm hB
    hlaw hmu (M := fun b => poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)) hM
  filter_upwards [h] with b hb m
  exact ⟨(hb.1 m).ne', ne_top_of_le_ne_top hb.2.1.ne
    (ENNReal.le_tsum (f := fun n => nthLargestAtom n
      (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l))) m)⟩

/-- In the vertex data model all ranked atoms of all vertices are positive and finite almost
surely. -/
theorem ae_cascadeData_atoms_pos_finite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ζ : ℕ → ℝ) (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) (hDm : ∀ v, Measurable (D v))
    (hDlaw : ∀ v, HasLaw (D v) ((Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)) P) :
    ∀ᵐ ω ∂P, ∀ (v : Σ p : ℕ, Fin p → ℕ) (m : ℕ),
      nthLargestAtom m (poissonCountingMeasure
        (fun k => ((D v ω).1 k).1) (fun k l => ((D v ω).1 k).2 l)) ≠ 0 ∧
      nthLargestAtom m (poissonCountingMeasure
        (fun k => ((D v ω).1 k).1) (fun k l => ((D v ω).1 k).2 l)) ≠ ∞ := by
  refine ae_all_iff.2 fun v => ?_
  have hmap : P.map (fun ω => (D v ω).1) = Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k) := by
    rw [show (fun ω => (D v ω).1) = Prod.fst ∘ D v from rfl,
      ← Measure.map_map measurable_fst (hDm v), (hDlaw v).map_eq, Measure.map_fst_prod,
      measure_univ, one_smul]
  have h := ae_infinitePi_blocks_atoms_pos_finite (hζ0 v.1) (hζ1 v.1) (nu v.1) (rate v.1)
    (hmu v.1)
  exact ae_of_ae_map (measurable_fst.comp (hDm v)).aemeasurable (hmap ▸ h)

/-- The `m`-th largest atom at a vertex is a measurable function of the vertex data. -/
theorem measurable_cascadeAtom (v : Σ p : ℕ, Fin p → ℕ) (m : ℕ) :
    Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      nthLargestAtom m (poissonCountingMeasure
        (fun k => ((d v).1 k).1) (fun k l => ((d v).1 k).2 l)) := by
  have h1 : Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      (d v).1 := measurable_fst.comp (measurable_pi_apply v)
  exact (measurable_nthLargestAtom m).comp (measurable_poissonCountingMeasure.comp h1)

/-- The marked partition sum is jointly measurable in a parameter of the exponent function and
the vertex data. -/
theorem measurable_cascadeMarkedSum_param {α : Type*} [MeasurableSpace α] (r : ℕ)
    {X : α → (Fin r → Ξ) → ℝ} (hX : Measurable (Function.uncurry X))
    {g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun q : α × ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) =>
      cascadeMarkedSum r (X q.1) g q.2 := by
  unfold cascadeMarkedSum
  refine Measurable.tsum fun α' => ?_
  have hw : Measurable fun q : α × ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) =>
      cascadeBranchWeight (fun p γ m => nthLargestAtom m (poissonCountingMeasure
        (fun k => ((q.2 ⟨p, γ⟩).1 k).1) (fun k l => ((q.2 ⟨p, γ⟩).1 k).2 l))) α' :=
    Finset.measurable_prod _ fun i _ => (measurable_cascadeAtom (Ξ := Ξ) _ _).comp measurable_snd
  have hgm : Measurable fun q : α × ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) =>
      g (q.2 ⟨r, α'⟩) := hg.comp ((measurable_pi_apply _).comp measurable_snd)
  have hpath : Measurable fun q : α × ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) =>
      (fun i : Fin r => (q.2 ⟨i, Fin.take i i.isLt.le α'⟩).2 (α' i)) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply (α' i)).comp
      (measurable_snd.comp ((measurable_pi_apply _).comp measurable_snd))
  have hXq : Measurable fun q : α × ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) =>
      X q.1 (fun i : Fin r => (q.2 ⟨i, Fin.take i i.isLt.le α'⟩).2 (α' i)) :=
    hX.comp (measurable_fst.prodMk hpath)
  exact (hw.mul hgm).mul (ENNReal.measurable_ofReal.comp hXq.exp)

/-- The marked partition sum is a measurable function of the vertex data. -/
theorem measurable_cascadeMarkedSum (r : ℕ) {X : (Fin r → Ξ) → ℝ} (hX : Measurable X)
    {g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      cascadeMarkedSum r X g d := by
  unfold cascadeMarkedSum
  refine Measurable.tsum fun α => ?_
  have hw : Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      cascadeBranchWeight (fun p γ m => nthLargestAtom m (poissonCountingMeasure
        (fun k => ((d ⟨p, γ⟩).1 k).1) (fun k l => ((d ⟨p, γ⟩).1 k).2 l))) α :=
    Finset.measurable_prod _ fun i _ => measurable_cascadeAtom _ _
  have hgm : Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      g (d ⟨r, α⟩) := hg.comp (measurable_pi_apply _)
  have hpath : Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      (fun i : Fin r => (d ⟨i, Fin.take i i.isLt.le α⟩).2 (α i)) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply (α i)).comp
      (measurable_snd.comp (measurable_pi_apply _))
  exact (hw.mul hgm).mul (ENNReal.measurable_ofReal.comp (hX.comp hpath).exp)

omit [MeasurableSpace Ξ] in
/-- A positive total weight: if all atoms and all leaf marks are nonzero, so is the marked sum. -/
theorem cascadeMarkedSum_ne_zero (r : ℕ) (X : (Fin r → Ξ) → ℝ)
    (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞)
    (d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))
    (hu : ∀ (p : ℕ) (γ : Fin p → ℕ) (m : ℕ), nthLargestAtom m (poissonCountingMeasure
      (fun k => ((d ⟨p, γ⟩).1 k).1) (fun k l => ((d ⟨p, γ⟩).1 k).2 l)) ≠ 0)
    (hg : ∀ α : Fin r → ℕ, g (d ⟨r, α⟩) ≠ 0) : cascadeMarkedSum r X g d ≠ 0 := by
  intro h
  have hle := ENNReal.le_tsum (f := fun α : Fin r → ℕ => cascadeBranchWeight
    (fun p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((d ⟨p, γ⟩).1 k).1) (fun k l => ((d ⟨p, γ⟩).1 k).2 l))) α * g (d ⟨r, α⟩) *
    ENNReal.ofReal (Real.exp (X fun i : Fin r =>
      (d ⟨i, Fin.take i i.isLt.le α⟩).2 (α i)))) (fun _ => 0)
  have hz : (cascadeBranchWeight
    (fun p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((d ⟨p, γ⟩).1 k).1) (fun k l => ((d ⟨p, γ⟩).1 k).2 l))) (fun _ : Fin r => 0) *
      g (d ⟨r, fun _ => 0⟩) * ENNReal.ofReal (Real.exp (X fun i : Fin r =>
        (d ⟨i, Fin.take i i.isLt.le (fun _ => 0)⟩).2 0))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (hg _)) (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    exact Finset.prod_ne_zero_iff.2 fun i _ => hu _ _ _
  have hle' : _ ≤ cascadeMarkedSum r X g d := hle
  rw [h] at hle'
  exact hz (le_zero_iff.1 hle')

/-- For `0 < a ≤ b`, `x ^ a ≤ 1 + x ^ b`. -/
theorem rpow_le_one_add_rpow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ≥0∞) :
    x ^ a ≤ 1 + x ^ b := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one hx ha.le).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le (not_le.1 hx).le hab).trans le_add_self

/-- **Moment of the marked partition sum.** In the vertex data model with strictly increasing
exponents, the `a`-th moment of `∑_α w_α g(d (r, α))` is finite for `0 < a < ζ 0` as soon as the
leaf mark `g` has a finite `b`-th moment, where `b ≥ ζ (r - 1)` for `r ≥ 1` and `b ≥ a` for
`r = 0`. -/
theorem lintegral_cascadeMarkedSum_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) :
    ∀ (ζ : ℕ → ℝ), (∀ p, 0 < ζ p) → (∀ p, ζ p < 1) → StrictMono ζ →
    ∀ (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
      (rate : (p : ℕ) → ℕ → ℝ≥0),
    (∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k) →
    ∀ (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))),
    (∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)) →
    ∀ (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)), (∀ v, Measurable (D v)) →
    iIndepFun D P → (∀ v, HasLaw (D v) (𝔡 v.1) P) →
    ∀ (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞), Measurable g →
    (∀ᵐ x ∂𝔡 r, g x ≠ 0) → (∀ᵐ x ∂𝔡 r, g x ≠ ∞) →
    ∀ (a b : ℝ), 0 < a → a < ζ 0 → (r = 0 → a ≤ b) → (∀ k, r = k + 1 → ζ k ≤ b) →
    ∫⁻ x, g x ^ b ∂𝔡 r < ∞ →
    ∫⁻ ω, (cascadeMarkedSum r (fun _ => (0 : ℝ)) g (fun v => D v ω)) ^ a ∂P < ∞ := by
  induction r with
  | zero =>
    intro ζ hζ0 hζ1 hmono nu _ rate hmu ρ _ 𝔡 h𝔡 D hDm hD hDlaw g hg hg0 hgf a b ha0 haζ hab hbζ
      hgb
    have hS : ∀ ω, cascadeMarkedSum 0 (fun _ => (0 : ℝ)) g (fun v => D v ω) =
        g (D ⟨0, fun i => i.elim0⟩ ω) := by
      intro ω
      simp only [cascadeMarkedSum, tsum_fintype, cascadeBranchWeight_zero, Real.exp_zero,
        ENNReal.ofReal_one, mul_one, one_mul]
      exact Fintype.sum_unique _ |>.trans (congrArg (fun γ => g (D ⟨0, γ⟩ ω))
        (Subsingleton.elim _ _))
    have hprob : IsProbabilityMeasure (𝔡 0) := by rw [h𝔡 0]; infer_instance
    simp_rw [hS]
    rw [(hDlaw ⟨0, fun i => i.elim0⟩).lintegral_comp (f := fun x => g x ^ a)
      (hg.pow_const a).aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono fun x => rpow_le_one_add_rpow ha0 (hab rfl) (g x)) ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hgb⟩
  | succ r ih =>
    intro ζ hζ0 hζ1 hmono nu _ rate hmu ρ _ 𝔡 h𝔡 D hDm hD hDlaw g hg hg0 hgf a b ha0 haζ hab hbζ
      hgb
    have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
    have hSm : ∀ n, Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) =>
        D ⟨v.1 + 1, Fin.cons n v.2⟩ ω := fun n =>
      measurable_pi_iff.2 fun v => hDm _
    have hF : Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
        cascadeMarkedSum r (fun _ => (0 : ℝ)) g d :=
      measurable_cascadeMarkedSum r measurable_const hg
    obtain ⟨T, hT⟩ : ∃ T : Ω → ℕ → ℝ≥0∞, ∀ ω n, T ω n =
        cascadeMarkedSum r (fun _ => (0 : ℝ)) g (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) :=
      ⟨_, fun _ _ => rfl⟩
    have hTm : Measurable T := by
      refine measurable_pi_iff.2 fun n => ?_
      have h := hF.comp (hSm n)
      have e : T = fun ω n => cascadeMarkedSum r (fun _ => (0 : ℝ)) g
          (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) := funext fun ω => funext fun n => hT ω n
      rw [e]
      exact h
    have hDlaw' : ∀ v, HasLaw (D v) ((Measure.infinitePi fun k =>
        Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
          (Measure.infinitePi fun _ : ℕ => ρ)) P := by
      intro v
      rw [← h𝔡 v.1]
      exact hDlaw v
    have hatoms := ae_cascadeData_atoms_pos_finite ζ hζ0 hζ1 nu rate hmu ρ D hDm hDlaw'
    have hgpos : ∀ᵐ ω ∂P, ∀ γ : Fin (r + 1) → ℕ,
        g (D ⟨r + 1, γ⟩ ω) ≠ 0 ∧ g (D ⟨r + 1, γ⟩ ω) ≠ ∞ :=
      ae_all_iff.2 fun γ => ae_of_ae_map (hDm _).aemeasurable
        (by rw [(hDlaw ⟨r + 1, γ⟩).map_eq]; exact hg0.and hgf)
    have hTpos : ∀ᵐ ω ∂P, ∀ n, T ω n ≠ 0 := by
      filter_upwards [hatoms, hgpos] with ω h1 h2 n
      rw [hT]
      exact cascadeMarkedSum_ne_zero r (fun _ => (0 : ℝ)) g
        (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) (fun p γ m => (h1 ⟨p + 1, Fin.cons n γ⟩ m).1)
        (fun β => (h2 (Fin.cons n β)).1)
    have hUpos := hatoms.mono fun ω h n => h ⟨0, fun i => i.elim0⟩ n
    -- the induction hypothesis for the subtree below child `0`, with exponent `ζ 0`
    have hih := ih (fun p => ζ (p + 1)) (fun p => hζ0 _) (fun p => hζ1 _)
      (fun p q h => hmono (Nat.succ_lt_succ h)) (fun p k => nu (p + 1) k)
      (fun p k => rate (p + 1) k) (fun p => hmu (p + 1)) ρ (fun p => 𝔡 (p + 1))
      (fun p => h𝔡 (p + 1)) (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩) (fun v => hDm _)
      (iIndepFun_cascadeChildData D hD 0) (fun v => hDlaw _) g hg hg0 hgf (ζ 0) b
      (hζ0 0) (hmono Nat.zero_lt_one) (fun hr => hbζ 0 (by omega))
      (fun k hk => hbζ (k + 1) (by omega)) hgb
    -- the common law of the subtree totals
    have : ∀ p, IsProbabilityMeasure (𝔡 p) := h𝔡p
    obtain ⟨τ, hτ⟩ : ∃ τ : Measure ℝ≥0∞, τ = (Measure.infinitePi
        fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)).map
        (fun d => cascadeMarkedSum r (fun _ => (0 : ℝ)) g d) := ⟨_, rfl⟩
    have : IsProbabilityMeasure τ := by
      rw [hτ]
      exact (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
    have hlawT : ∀ n, HasLaw (fun ω => T ω n) τ P := by
      intro n
      have h1 : HasLaw (fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
          cascadeMarkedSum r (fun _ => (0 : ℝ)) g d) τ
          (Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)) :=
        ⟨hF.aemeasurable, hτ.symm⟩
      have h2 := h1.comp (hasLaw_cascadeSubtreeData D hDm hD 𝔡 hDlaw n)
      have e : (fun ω => T ω n) = (fun d : (Σ p : ℕ, Fin p → ℕ) →
          (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => cascadeMarkedSum r (fun _ => (0 : ℝ)) g d) ∘
          (fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) :=
        funext fun ω => hT ω n
      rw [e]
      exact h2
    have hmom : ∫⁻ t, t ^ ζ 0 ∂τ ≠ ∞ := by
      have hl := (hlawT 0).lintegral_comp (f := fun t : ℝ≥0∞ => t ^ ζ 0)
        (by fun_prop : Measurable fun t : ℝ≥0∞ => t ^ ζ 0).aemeasurable
      rw [← hl]
      simp_rw [hT]
      exact hih.ne
    -- independence of the root blocks from the subtree totals
    have hind : IndepFun (fun ω k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k)) T P := by
      have h := (indepFun_cascadeRoot_subtreeData D hDm hD).comp
        (φ := fun x : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => x.1)
        (ψ := fun s : ℕ → (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
          fun n => cascadeMarkedSum r (fun _ => (0 : ℝ)) g (s n))
        measurable_fst (measurable_pi_iff.2 fun n => hF.comp (measurable_pi_apply n))
      have e : T = (fun s : ℕ → (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
          fun n => cascadeMarkedSum r (fun _ => (0 : ℝ)) g (s n)) ∘
          (fun ω (n : ℕ) (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) :=
        funext fun ω => funext fun n => hT ω n
      rw [e]
      exact h
    -- the root blocks are independent Poisson blocks
    have hBvec : HasLaw (fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1) (Measure.infinitePi fun k =>
        Po(rate 0 k).prod (Measure.infinitePi fun _ : ℕ => nu 0 k)) P := by
      refine ⟨(measurable_fst.comp (hDm _)).aemeasurable, ?_⟩
      rw [show (fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1) = Prod.fst ∘ D ⟨0, fun i => i.elim0⟩
        from rfl, ← Measure.map_map measurable_fst (hDm _), (hDlaw' _).map_eq,
        Measure.map_fst_prod, measure_univ, one_smul]
    obtain ⟨hB, hBlaw⟩ := iIndepFun_hasLaw_of_hasLaw_infinitePi hBvec
    have hstep := lintegral_rankedRoot_marked_sum_rpow_lt_top (hζ0 0) ha0 haζ (hζ1 0) (nu 0)
      (rate 0) (fun k ω => (D ⟨0, fun i => i.elim0⟩ ω).1 k)
      (fun k => (measurable_pi_apply k).comp (measurable_fst.comp (hDm _))) hB hBlaw (hmu 0) T
      hTm hind τ hlawT hmom hTpos hUpos
    have hS : ∀ ω, cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g (fun v => D v ω) =
        ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
          (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) * T ω n := fun ω => by
      rw [cascadeMarkedSum_succ]
      simp only [hT]
    simp_rw [hS]
    exact hstep

end SpinGlasses
