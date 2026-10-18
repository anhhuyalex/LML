/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletPower
public import LeanMachineLearning.SpinGlasses.PoissonProcessEquivalence
public import LeanMachineLearning.SpinGlasses.PoissonProcessTransform
public import LeanMachineLearning.ForMathlib.Probability.InfinitePiZip
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.RankedMark
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtomRpow

/-!
# Superposition of marked Poisson processes (Theorem 2.12 of Panchenko)

Independent `ζ`-Poisson blocks `B_{γ,k}` carry the points of a Poisson process of intensity `μ_ζ`
for every `γ`. Scaling the points of the `γ`-th process by `w_γ` and marking them by `γ` and
superposing gives a marked Poisson process of intensity `∑_γ w_γ^ζ μ_ζ ⊗ δ_γ = λ μ_ζ ⊗ Λ`, with
`λ = ∑_γ w_γ^ζ` and `Λ = (w_γ^ζ / λ)_γ`: it has the law of a Poisson process of intensity
`λ μ_ζ` whose points carry independent marks of law `Λ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

variable {Γ : Type*} [MeasurableSpace Γ]

/-- **The intensity of the superposition.** Scaling the `ζ`-Poisson intensity by `w_γ` and
marking by `γ`, then summing over `γ`, is the product of `λ μ_ζ` with the probability
`Λ = (w_γ^ζ / λ)_γ`. -/
theorem marked_intensity_eq [Countable Γ] {e : ℝ} (he : 0 < e)
    (nu : ℕ → Measure ℝ) (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure e = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (w : Γ → ℝ) (hw : ∀ γ, 0 < w γ) {c : ℝ} (hc : 0 < c) (hce : c ^ e = ∑' γ, w γ ^ e)
    (Λ : Measure Γ) (hΛ : Λ = Measure.sum fun γ =>
      ENNReal.ofReal (w γ ^ e / ∑' γ', w γ' ^ e) • Measure.dirac γ) :
    (Measure.sum fun p : Γ × ℕ => (rate p.2 : ℝ≥0∞) •
        (nu p.2).map (fun x : ℝ => (x * w p.1, p.1))) =
      Measure.sum fun k => (rate k : ℝ≥0∞) • ((nu k).map fun x : ℝ => x * c).prod Λ := by
  classical
  have hmeasf : ∀ γ : Γ, Measurable fun x : ℝ => (x * w γ, γ) := fun γ => by fun_prop
  have hL : (Measure.sum fun p : Γ × ℕ => (rate p.2 : ℝ≥0∞) •
        (nu p.2).map (fun x : ℝ => (x * w p.1, p.1))) =
      Measure.sum fun γ => ENNReal.ofReal (w γ ^ e) •
        (zetaPoissonMeasure e).map (fun x : ℝ => (x, γ)) := by
    rw [← Measure.sum_sum (fun γ k => (rate k : ℝ≥0∞) • (nu k).map (fun x : ℝ => (x * w γ, γ)))]
    refine congrArg Measure.sum (funext fun γ => ?_)
    rw [← poissonIntensity_map nu rate (hmeasf γ), ← hmu]
    have : (fun x : ℝ => (x * w γ, γ)) = (fun x : ℝ => (x, γ)) ∘ (fun x : ℝ => x * w γ) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), zetaPoissonMeasure_map_mul he (hw γ),
      Measure.map_smul]
    exact (by fun_prop : Measurable fun x : ℝ => (x, γ)).aemeasurable
  have hsm : ∀ (a : ℝ≥0∞) (m : Γ → Measure (ℝ × Γ)),
      a • Measure.sum m = Measure.sum fun γ => a • m γ := fun a m => by
    ext s hs
    simp [Measure.sum_apply _ hs, ENNReal.tsum_mul_left]
  have hlam : 0 < ∑' γ, w γ ^ e := hce ▸ Real.rpow_pos_of_pos hc e
  have hR : (Measure.sum fun k => (rate k : ℝ≥0∞) • ((nu k).map fun x : ℝ => x * c).prod Λ) =
      Measure.sum fun γ => ENNReal.ofReal (w γ ^ e) •
        (zetaPoissonMeasure e).map (fun x : ℝ => (x, γ)) := by
    have h1 : (Measure.sum fun k => (rate k : ℝ≥0∞) • ((nu k).map fun x : ℝ => x * c).prod Λ) =
        (Measure.sum fun k => (rate k : ℝ≥0∞) • (nu k).map fun x : ℝ => x * c).prod Λ := by
      rw [Measure.prod_sum_left]
      exact congrArg Measure.sum (funext fun k => by rw [Measure.prod_smul_left])
    rw [h1, ← poissonIntensity_map nu rate (by fun_prop : Measurable fun x : ℝ => x * c), ← hmu,
      zetaPoissonMeasure_map_mul he hc, Measure.prod_smul_left, hΛ, Measure.prod_sum_right,
      hsm]
    refine congrArg Measure.sum (funext fun γ => ?_)
    rw [Measure.prod_smul_right, Measure.prod_dirac, smul_smul,
      ← ENNReal.ofReal_mul (by positivity), hce]
    congr 2
    field_simp
  rw [hL, hR]

section Law

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **Superposition of marked Poisson processes (the first half of Theorem 2.12).** Let independent
blocks `B γ k` have the law `Po(rate k) ⊗ (nu k)^{⊗ℕ}`, where `∑ₖ rate k • nu k = μ_e`. The counting
measure of the points `(w_γ x, γ)` (all sampled points `x` of the blocks of `γ`, scaled by `w_γ` and
marked by `γ`) has the law of the counting measure of independent blocks with sample laws
`(nu k).map (· * c) ⊗ Λ`, where `c ^ e = ∑ w_γ ^ e` and `Λ = (w_γ ^ e / ∑ w ^ e)_γ`: positions
`c x` with i.i.d. marks of law `Λ` independent of the positions. -/
theorem identDistrib_marked_superposition [Countable Γ] [Nonempty Γ] [MeasurableSingletonClass Γ]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {e : ℝ} (he : 0 < e)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure e = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (w : Γ → ℝ) (hw : ∀ γ, 0 < w γ) {c : ℝ} (hc : 0 < c) (hce : c ^ e = ∑' γ, w γ ^ e)
    (Λ : Measure Γ) [IsProbabilityMeasure Λ] (hΛ : Λ = Measure.sum fun γ =>
      ENNReal.ofReal (w γ ^ e / ∑' γ', w γ' ^ e) • Measure.dirac γ)
    {B : Γ → ℕ → Ω₀ → ℕ × (ℕ → ℝ)} (hBm : ∀ γ k, Measurable (B γ k))
    (hB : iIndepFun (fun p : Γ × ℕ => B p.1 p.2) P₀)
    (hlaw : ∀ γ k, HasLaw (B γ k) (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) P₀) :
    IdentDistrib
      (fun ω => Measure.sum fun γ => (poissonCountingMeasure (fun k => (B γ k ω).1)
        (fun k l => (B γ k ω).2 l)).map (fun x : ℝ => (x * w γ, γ)))
      (fun ω' : ℕ → (ℕ × (ℕ → ℝ)) × (ℕ → Γ) => poissonCountingMeasure (fun k => (ω' k).1.1)
        (fun k l => ((ω' k).1.2 l * c, (ω' k).2 l)))
      P₀ (Measure.infinitePi fun k => (Po(rate k).prod
        (Measure.infinitePi fun _ : ℕ => nu k)).prod (Measure.infinitePi fun _ : ℕ => Λ)) := by
  classical
  have : Infinite (Γ × ℕ) := inferInstance
  obtain ⟨ι⟩ : Nonempty (ℕ ≃ Γ × ℕ) := nonempty_equiv_of_countable
  -- the combined blocks of the actual construction, indexed by `ℕ`
  have hfm : ∀ j : ℕ, Measurable fun x : ℝ => ((x * w (ι j).1, (ι j).1) : ℝ × Γ) :=
    fun j => by fun_prop
  have hν : ∀ j : ℕ, IsProbabilityMeasure ((nu (ι j).2).map fun x : ℝ =>
      ((x * w (ι j).1, (ι j).1) : ℝ × Γ)) := fun j => inferInstance
  have hCm : ∀ j : ℕ, Measurable fun ω => (((B (ι j).1 (ι j).2 ω).1, fun l =>
      (((B (ι j).1 (ι j).2 ω).2 l * w (ι j).1, (ι j).1) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ)) :=
    fun j => by have := hBm (ι j).1 (ι j).2; fun_prop
  have hCi : iIndepFun (fun (j : ℕ) ω => (((B (ι j).1 (ι j).2 ω).1, fun l =>
      (((B (ι j).1 (ι j).2 ω).2 l * w (ι j).1, (ι j).1) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ))) P₀ :=
    (hB.precomp ι.injective).comp (fun j (b : ℕ × (ℕ → ℝ)) => ((b.1, fun l =>
      ((b.2 l * w (ι j).1, (ι j).1) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ))) (fun j => by fun_prop)
  have hClaw : ∀ j : ℕ, HasLaw (fun ω => (((B (ι j).1 (ι j).2 ω).1, fun l =>
      (((B (ι j).1 (ι j).2 ω).2 l * w (ι j).1, (ι j).1) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ)))
      (Po(rate (ι j).2).prod (Measure.infinitePi fun _ : ℕ => (nu (ι j).2).map fun x : ℝ =>
        ((x * w (ι j).1, (ι j).1) : ℝ × Γ))) P₀ := fun j =>
    hasLaw_map_prod_infinitePi (hlaw (ι j).1 (ι j).2) (hfm j)
  -- the reference construction: positions `x * c` with independent marks of law `Λ`
  have hgm : Measurable fun y : ℝ × Γ => ((y.1 * c, y.2) : ℝ × Γ) := by fun_prop
  have hB'm : ∀ k : ℕ, Measurable fun ω' : ℕ → (ℕ × (ℕ → ℝ)) × (ℕ → Γ) =>
      (((ω' k).1.1, fun l => (((ω' k).1.2 l * c, (ω' k).2 l) : ℝ × Γ)) :
        ℕ × (ℕ → ℝ × Γ)) := fun k => by fun_prop
  have hB'i : iIndepFun (fun (k : ℕ) (ω' : ℕ → (ℕ × (ℕ → ℝ)) × (ℕ → Γ)) =>
      (((ω' k).1.1, fun l => (((ω' k).1.2 l * c, (ω' k).2 l) : ℝ × Γ)) :
        ℕ × (ℕ → ℝ × Γ))) (Measure.infinitePi fun k => (Po(rate k).prod
        (Measure.infinitePi fun _ : ℕ => nu k)).prod (Measure.infinitePi fun _ : ℕ => Λ)) :=
    iIndepFun_infinitePi (P := fun k => (Po(rate k).prod
      (Measure.infinitePi fun _ : ℕ => nu k)).prod (Measure.infinitePi fun _ : ℕ => Λ))
      (X := fun _ (z : (ℕ × (ℕ → ℝ)) × (ℕ → Γ)) => (((z.1.1, fun l =>
        (((z.1.2 l * c, z.2 l) : ℝ × Γ))) : ℕ × (ℕ → ℝ × Γ)))) (fun _ => by fun_prop)
  have hB'law : ∀ k : ℕ, HasLaw (fun ω' : ℕ → (ℕ × (ℕ → ℝ)) × (ℕ → Γ) =>
      (((ω' k).1.1, fun l => (((ω' k).1.2 l * c, (ω' k).2 l) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ)))
      (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => ((nu k).map fun x : ℝ => x * c).prod Λ))
      (Measure.infinitePi fun k => (Po(rate k).prod
        (Measure.infinitePi fun _ : ℕ => nu k)).prod (Measure.infinitePi fun _ : ℕ => Λ)) := by
    intro k
    have h1 := hasLaw_eval_infinitePi (fun k => (Po(rate k).prod
      (Measure.infinitePi fun _ : ℕ => nu k)).prod (Measure.infinitePi fun _ : ℕ => Λ)) k
    have hz : HasLaw (fun ω' : ℕ → (ℕ × (ℕ → ℝ)) × (ℕ → Γ) =>
        (((ω' k).1.1, fun l => (((ω' k).1.2 l, (ω' k).2 l) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ)))
        (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => (nu k).prod Λ))
        (Measure.infinitePi fun k => (Po(rate k).prod
          (Measure.infinitePi fun _ : ℕ => nu k)).prod (Measure.infinitePi fun _ : ℕ => Λ)) := by
      refine ⟨by fun_prop, ?_⟩
      rw [← Measure.prod_infinitePi_map_assoc_zip (Po(rate k)) (fun _ : ℕ => nu k) (fun _ : ℕ => Λ),
        ← h1.map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    have h2 := hasLaw_map_prod_infinitePi (ν := (nu k).prod Λ) hz hgm
    have h3 : ((nu k).prod Λ).map (fun y : ℝ × Γ => ((y.1 * c, y.2) : ℝ × Γ)) =
        ((nu k).map fun x : ℝ => x * c).prod Λ := by
      rw [show (fun y : ℝ × Γ => ((y.1 * c, y.2) : ℝ × Γ)) =
        Prod.map (fun x : ℝ => x * c) id from rfl, ← Measure.map_prod_map _ _
        (by fun_prop) measurable_id, Measure.map_id]
    rw [h3] at h2
    exact h2
  have hμ : (Measure.sum fun j : ℕ => (rate (ι j).2 : ℝ≥0∞) • (nu (ι j).2).map fun x : ℝ =>
      ((x * w (ι j).1, (ι j).1) : ℝ × Γ)) =
      Measure.sum fun k => (rate k : ℝ≥0∞) • ((nu k).map fun x : ℝ => x * c).prod Λ := by
    have h0 := Measure.sum_comp_equiv ι (fun p : Γ × ℕ => (rate p.2 : ℝ≥0∞) • (nu p.2).map
      (fun x : ℝ => ((x * w p.1, p.1) : ℝ × Γ)))
    exact h0.trans (marked_intensity_eq he nu rate hmu w hw hc hce Λ hΛ)
  have h := identDistrib_poissonCountingMeasure_of_intensity_eq
    (fun j => (nu (ι j).2).map fun x : ℝ => ((x * w (ι j).1, (ι j).1) : ℝ × Γ))
    (fun j => rate (ι j).2) (fun k => ((nu k).map fun x : ℝ => x * c).prod Λ) rate hCm hCi hClaw
    hB'm hB'i hB'law hμ
  have e1 : (fun ω => Measure.sum fun γ => (poissonCountingMeasure (fun k => (B γ k ω).1)
      (fun k l => (B γ k ω).2 l)).map (fun x : ℝ => (x * w γ, γ))) = fun ω =>
      poissonCountingMeasure (fun j => (((B (ι j).1 (ι j).2 ω).1, fun l =>
        (((B (ι j).1 (ι j).2 ω).2 l * w (ι j).1, (ι j).1) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ)).1)
        (fun j l => (((B (ι j).1 (ι j).2 ω).1, fun l =>
        (((B (ι j).1 (ι j).2 ω).2 l * w (ι j).1, (ι j).1) : ℝ × Γ)) : ℕ × (ℕ → ℝ × Γ)).2 l) := by
    funext ω
    have step1 : (Measure.sum fun γ => (poissonCountingMeasure (fun k => (B γ k ω).1)
        (fun k l => (B γ k ω).2 l)).map (fun x : ℝ => (x * w γ, γ))) =
        Measure.sum fun γ => Measure.sum fun k =>
          ∑ l ∈ Finset.range (B γ k ω).1,
            Measure.dirac (((B γ k ω).2 l * w γ, γ) : ℝ × Γ) := by
      refine congrArg Measure.sum (funext fun γ => ?_)
      rw [poissonCountingMeasure_map _ _ (by fun_prop : Measurable fun x : ℝ => (x * w γ, γ))]
      rfl
    rw [step1, Measure.sum_sum (fun γ k => ∑ l ∈ Finset.range (B γ k ω).1,
      Measure.dirac (((B γ k ω).2 l * w γ, γ) : ℝ × Γ))]
    exact (Measure.sum_comp_equiv ι (fun p : Γ × ℕ => ∑ l ∈ Finset.range (B p.1 p.2 ω).1,
      Measure.dirac (((B p.1 p.2 ω).2 l * w p.1, p.1) : ℝ × Γ))).symm
  rw [e1]
  exact h

end Law

section Reference

variable [MeasurableSingletonClass Γ] [Encodable Γ] [Inhabited Γ]

/-- The positions of the reference process: scaling does not change the normalized ranked
weights. -/
theorem poissonDirichletWeight_counting_mul (b : ℕ → ℕ × (ℕ → ℝ))
    [Infinite {q : ℕ × ℕ // q.2 < (b q.1).1}]
    (hpos : ∀ q : {q : ℕ × ℕ // q.2 < (b q.1).1}, 0 < (b q.1.1).2 q.1.2)
    (hinj : Function.Injective fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2)
    (hs : Summable fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2) {c : ℝ}
    (hc : 0 < c) (l : ℕ) :
    poissonDirichletWeight l (poissonCountingMeasure (fun k => (b k).1)
        (fun k l => (b k).2 l * c)) =
      poissonDirichletWeight l (poissonCountingMeasure (fun k => (b k).1)
        (fun k l => (b k).2 l)) := by
  have hW : ∀ m, nthLargestAtom m (poissonCountingMeasure (fun k => (b k).1)
      (fun k l => (b k).2 l * c)) = nthLargestAtom m (poissonCountingMeasure (fun k => (b k).1)
      (fun k l => (b k).2 l)) * ENNReal.ofReal c := fun m => by
    rw [poissonCountingMeasure_eq_sum_dirac, poissonCountingMeasure_eq_sum_dirac]
    exact nthLargestAtom_sum_dirac_mul (fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} =>
      (b q.1.1).2 q.1.2) hinj hpos hs hc m
  unfold poissonDirichletWeight
  simp_rw [hW]
  rw [ENNReal.tsum_mul_right, ENNReal.mul_div_mul_right _ _ (ENNReal.ofReal_pos.2 hc).ne'
    ENNReal.ofReal_ne_top]

end Reference

end SpinGlasses
