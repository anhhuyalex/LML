/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeReplicaLaw
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFstSndInfinitePi

/-!
# Bolthausen--Sznitman invariance of the Gibbs measure of a Ruelle cascade

The Gibbs average `⟨·⟩_t` of the Ruelle probability cascade with vertex data `d` for the Gaussian
field `g(α) = ∑ᵢ σᵢ (label of α at level i)`, tilted by `exp (t g)`. Lemma 2.5 of Panchenko says
that the tilt, compensated by the shift `g ↦ g - t b`, does not change the law of the Gibbs
average of a function of the overlaps. It is deduced from the equality in law of replica sums
(`identDistrib_cascadeReplicaSum_tilt`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

/-- **Lemma 2.5 of Panchenko for `k = 0`: overlap invariance under the tilt.** For the Ruelle
cascade with exponents `0 < ζ_p < 1`, i.i.d. standard Gaussian labels and any nonnegative
function `f` of the overlap matrix of `n` replicas, the expected Gibbs average
`E ⟨f(Rⁿ)⟩_t` does not depend on the tilt parameter `t`. -/
theorem lintegral_cascadeGibbs_tilt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ σ : ℕ → ℝ) (t : ℝ) (hζ0 : ∀ p, 0 < ζ p)
    (hζ1 : ∀ p, ζ p < 1) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (lab : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ)
    (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) :
    ∫⁻ ω, replicaGibbs r n σ t F (u ω) (lab ω) ∂P =
      ∫⁻ ω, replicaGibbs r n σ 0 F (u ω) (lab ω) ∂P := by
  subst hu hlab
  have h := identDistrib_cascadeReplicaSum_tilt (P := P) r ζ σ t hζ0 hζ1 nu rate hmu 𝔡 h𝔡 D hDm
    hD hDlaw (X := Fin n → Fin n → Fin (r + 1)) (fun _ => Fin n) (fun P l l' => (P l l').val)
    (fun _ _ _ => fun _ => 1) fun _ _ _ => measurable_const
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ((Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) → ℝ≥0∞, ∀ z, Ψ z =
      (∑ P : Fin n → Fin n → Fin (r + 1), F P * z P) /
        ∑ P : Fin n → Fin n → Fin (r + 1), z P := ⟨_, fun _ => rfl⟩
  have hΨm : Measurable Ψ := by
    have e : Ψ = fun z => (∑ P : Fin n → Fin n → Fin (r + 1), F P * z P) /
        ∑ P : Fin n → Fin n → Fin (r + 1), z P := funext hΨ
    rw [e]
    exact (Finset.measurable_sum _ fun P _ => (measurable_pi_apply P).const_mul _).mul
      (Finset.measurable_sum _ fun P _ => measurable_pi_apply P).inv
  have h2 := (h.comp hΨm).lintegral_eq
  convert h2 using 2
  · funext ω
    rw [Function.comp_apply, hΨ]
    rw [replicaGibbs_eq_div r n σ ζ t F]
    rfl
  · funext ω
    rw [Function.comp_apply, hΨ]
    rw [replicaGibbs_eq_div r n σ ζ 0 F]
    simp only [zero_mul, tiltTest_zero]
    rfl

/-- **Lemma 2.5 of Panchenko for `k = (1, 0, …, 0)`, in law.** The Gibbs averages
`⟨f(Rⁿ) (σᵢ (label of σ^{l₀} at level i - tσᵢζᵢ))^±⟩_t` have the joint law of the untilted
averages `⟨f(Rⁿ) (σᵢ (label of σ^{l₀} at level i))^±⟩`. Summing over the levels `i` gives
`⟨f (g(σ^{l₀}) - t b)⟩_t =ᵈ ⟨f g(σ^{l₀})⟩` with `b = ∑ᵢ σᵢ² ζᵢ`. -/
theorem identDistrib_cascadeGibbsAt_tilt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ σ : ℕ → ℝ) (t : ℝ) (hζ0 : ∀ p, 0 < ζ p)
    (hζ1 : ∀ p, ζ p < 1) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (lab : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ)
    (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) (l₀ : Fin n) :
    IdentDistrib
      (fun ω (o : Fin r × Bool) => replicaGibbsAt r n σ t F l₀ o.1
        (if o.2 then fun y => ENNReal.ofReal (σ o.1 * y)
          else fun y => ENNReal.ofReal (-(σ o.1 * y)))
        (t * σ o.1 * ζ o.1) (u ω) (lab ω))
      (fun ω (o : Fin r × Bool) => replicaGibbsAt r n σ 0 F l₀ o.1
        (if o.2 then fun y => ENNReal.ofReal (σ o.1 * y)
          else fun y => ENNReal.ofReal (-(σ o.1 * y)))
        0 (u ω) (lab ω)) P P := by
  subst hu hlab
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin r × Bool → ℝ → ℝ≥0∞, ∀ o, ψ o =
      if o.2 then fun y => ENNReal.ofReal (σ o.1 * y) else fun y => ENNReal.ofReal (-(σ o.1 * y)) :=
    ⟨_, fun _ => rfl⟩
  have hψm : ∀ o, Measurable (ψ o) := fun o => by
    rw [hψ]
    by_cases ho : o.2
    · simp only [ho, ite_true]
      exact ENNReal.measurable_ofReal.comp (measurable_id.const_mul _)
    · simp only [ho]
      exact ENNReal.measurable_ofReal.comp (measurable_id.const_mul _).neg
  -- the family of replica sums: numerators with the test at one replica, and denominators
  obtain ⟨A, hA⟩ : ∃ A : Option (Fin r × Bool) → Fin n → ℕ → ℝ → ℝ≥0∞, ∀ x l i, A x l i =
      Option.elim x (fun _ => 1) (fun o => if l = l₀ ∧ i = o.1.val then ψ o else fun _ => 1) :=
    ⟨fun x l i => Option.elim x (fun _ => 1)
      (fun o => if l = l₀ ∧ i = o.1.val then ψ o else fun _ => 1), fun _ _ _ => rfl⟩
  have hAm : ∀ x l i, Measurable (A x l i) := fun x l i => by
    rw [hA]
    cases x with
    | none => exact measurable_const
    | some o =>
      simp only [Option.elim_some]
      by_cases h : l = l₀ ∧ i = o.1.val
      · simp only [h, and_self, ite_true]
        exact hψm o
      · simp only [h, ite_false]
        exact measurable_const
  have h := identDistrib_cascadeReplicaSum_tilt (P := P) r ζ σ t hζ0 hζ1 nu rate hmu 𝔡 h𝔡 D hDm
    hD hDlaw (X := (Fin n → Fin n → Fin (r + 1)) × Option (Fin r × Bool)) (fun _ => Fin n)
    (fun x l l' => (x.1 l l').val) (fun x => A x.2) fun x l i => hAm x.2 l i
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (((Fin n → Fin n → Fin (r + 1)) × Option (Fin r × Bool)) → ℝ≥0∞) →
      (Fin r × Bool → ℝ≥0∞), ∀ z o, Ψ z o =
      (∑ P : Fin n → Fin n → Fin (r + 1), F P * z (P, some o)) /
        ∑ P : Fin n → Fin n → Fin (r + 1), z (P, none) := ⟨_, fun _ _ => rfl⟩
  have hΨm : Measurable Ψ := measurable_pi_iff.2 fun o => by
    have e : (fun z => Ψ z o) = fun z => (∑ P : Fin n → Fin n → Fin (r + 1),
        F P * z (P, some o)) /
          ∑ P : Fin n → Fin n → Fin (r + 1), z (P, none) := funext fun z => hΨ z o
    rw [e]
    exact (Finset.measurable_sum _ fun P _ => (measurable_pi_apply (P, some o)).const_mul _).mul
      (Finset.measurable_sum _ fun P _ => measurable_pi_apply (P, none)).inv
  have hAs : ∀ o, A (some o) = fun l i => if l = l₀ ∧ i = o.1.val then ψ o else fun _ => 1 :=
    fun o => funext fun l => funext fun i => by rw [hA]; rfl
  have hAn : A none = fun _ _ => fun _ => 1 := funext fun l => funext fun i => by rw [hA]; rfl
  have h2 := h.comp hΨm
  simp only [← hψ]
  convert h2 using 1
  · funext ω o
    rw [Function.comp_apply, hΨ]
    rw [replicaGibbsAt_eq_div r n σ ζ t F l₀ o.1 (ψ o) _ rfl]
    simp only [hAs, hAn]
    rfl
  · funext ω o
    rw [Function.comp_apply, hΨ]
    rw [replicaGibbsAt_eq_div r n σ ζ 0 F l₀ o.1 (ψ o) 0 (by simp)]
    simp only [hAs, hAn, zero_mul, tiltTest_zero]
    rfl

/-- The branch weight of a leaf is a measurable function of the blocks of the vertices. -/
theorem measurable_branchWeight_blocks {r : ℕ} (α : Fin r → ℕ) :
    Measurable fun b : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ) =>
      cascadeBranchWeight (fun p γ m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (b ⟨p, γ⟩ k).1) (fun k l => (b ⟨p, γ⟩ k).2 l))) α :=
  Finset.measurable_prod _ fun _ _ => (measurable_nthLargestAtom _).comp
    (measurable_poissonCountingMeasure.comp (measurable_pi_apply _))

/-- At `t = 0` the Gibbs average with a test of one label factorizes: the weights are independent
of the labels, and every label is distributed as `ρ`. -/
theorem lintegral_cascadeGibbsAt_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (σ : ℕ → ℝ) (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → ℝ≥0)
    (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (lab : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ)
    (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) (l₀ : Fin n) (i₀ : Fin r) (ψ : ℝ → ℝ≥0∞)
    (hψ : Measurable ψ) :
    ∫⁻ ω, replicaGibbsAt r n σ 0 F l₀ i₀ ψ 0 (u ω) (lab ω) ∂P =
      (∫⁻ y, ψ y ∂gaussianReal 0 1) * ∫⁻ ω, replicaGibbs r n σ 0 F (u ω) (lab ω) ∂P := by
  classical
  have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
  obtain ⟨-, hLlaw, hind⟩ := hasLaw_indepFun_fst_snd_of_iIndepFun D hDm hD
    (fun v => Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k))
    (fun _ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
    (fun v => by rw [← h𝔡 v.1]; exact hDlaw v)
  -- the weights, as a function of the blocks, and the test, as a function of the labels
  obtain ⟨Xb, hXb⟩ : ∃ Xb : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) →
      (Fin n → Fin r → ℕ) → ℝ≥0∞, ∀ b α, Xb b α =
      ((∏ l, cascadeBranchWeight (fun p γ m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (b ⟨p, γ⟩ k).1) (fun k l => (b ⟨p, γ⟩ k).2 l))) (α l)) *
        F fun l l' => prefixOverlap (α l) (α l')) /
      (∑' β : Fin r → ℕ, cascadeBranchWeight (fun p γ m => nthLargestAtom m
        (poissonCountingMeasure (fun k => (b ⟨p, γ⟩ k).1)
          (fun k l => (b ⟨p, γ⟩ k).2 l))) β) ^ n := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Yl, hYl⟩ : ∃ Yl : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) → (Fin n → Fin r → ℕ) → ℝ≥0∞,
      ∀ ℓ α, Yl ℓ α = ψ (ℓ ⟨i₀, Fin.take i₀ i₀.isLt.le (α l₀)⟩ (α l₀ i₀)) := ⟨_, fun _ _ => rfl⟩
  have hXm : ∀ α, Measurable fun b => Xb b α := fun α => by
    have e : (fun b => Xb b α) = fun b => ((∏ l, cascadeBranchWeight (fun p γ m =>
        nthLargestAtom m (poissonCountingMeasure (fun k => (b ⟨p, γ⟩ k).1)
          (fun k l => (b ⟨p, γ⟩ k).2 l))) (α l)) *
        F fun l l' => prefixOverlap (α l) (α l')) /
      (∑' β : Fin r → ℕ, cascadeBranchWeight (fun p γ m => nthLargestAtom m
        (poissonCountingMeasure (fun k => (b ⟨p, γ⟩ k).1)
          (fun k l => (b ⟨p, γ⟩ k).2 l))) β) ^ n := funext fun b => hXb b α
    rw [e]
    exact ((Finset.measurable_prod _ fun l _ => measurable_branchWeight_blocks (α l)).mul_const
      _).mul (((Measurable.tsum fun β => measurable_branchWeight_blocks β).pow_const n).inv)
  have hYm : ∀ α, Measurable fun ℓ => Yl ℓ α := fun α => by
    have e : (fun ℓ => Yl ℓ α) = fun ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ =>
        ψ (ℓ ⟨i₀, Fin.take i₀ i₀.isLt.le (α l₀)⟩ (α l₀ i₀)) := funext fun ℓ => hYl ℓ α
    rw [e]
    exact hψ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
  have hB : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => (D v ω).1 :=
    measurable_pi_iff.2 fun v => measurable_fst.comp (hDm v)
  have hL : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => (D v ω).2 :=
    measurable_pi_iff.2 fun v => measurable_snd.comp (hDm v)
  have hkey : ∀ ω, replicaGibbsAt r n σ 0 F l₀ i₀ ψ 0 (u ω) (lab ω) =
      ∑' α, Xb (fun v => (D v ω).1) α * Yl (fun v => (D v ω).2) α := by
    intro ω
    subst hu hlab
    unfold replicaGibbsAt
    simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one, sub_zero, leafLabel]
    simp_rw [hXb, hYl]
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun α => ?_
    simp only [div_eq_mul_inv]
    ring
  have hgibbs : ∀ ω, replicaGibbs r n σ 0 F (u ω) (lab ω) =
      ∑' α, Xb (fun v => (D v ω).1) α := by
    intro ω
    subst hu hlab
    unfold replicaGibbs
    simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one]
    simp_rw [hXb]
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun α => ?_
    simp only [div_eq_mul_inv]
  have hcoord : ∀ (v : Σ p : ℕ, Fin p → ℕ) (k : ℕ),
      HasLaw (fun ω => (D v ω).2 k) (gaussianReal 0 1) P := fun v k =>
    (hasLaw_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) k).comp
      ((hasLaw_eval_infinitePi (fun _ : (Σ p : ℕ, Fin p → ℕ) =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) v).comp hLlaw)
  have hYint : ∀ α, ∫⁻ ω, Yl (fun v => (D v ω).2) α ∂P = ∫⁻ y, ψ y ∂gaussianReal 0 1 := fun α => by
    simp_rw [hYl]
    exact (hcoord ⟨i₀, Fin.take i₀ i₀.isLt.le (α l₀)⟩ (α l₀ i₀)).lintegral_comp hψ.aemeasurable
  have hXmB : ∀ α, Measurable fun ω => Xb (fun v => (D v ω).1) α := fun α => (hXm α).comp hB
  have hYmL : ∀ α, Measurable fun ω => Yl (fun v => (D v ω).2) α := fun α => (hYm α).comp hL
  simp_rw [hkey, hgibbs]
  calc ∫⁻ ω, ∑' α, Xb (fun v => (D v ω).1) α * Yl (fun v => (D v ω).2) α ∂P
      = ∑' α, ∫⁻ ω, Xb (fun v => (D v ω).1) α * Yl (fun v => (D v ω).2) α ∂P :=
        lintegral_tsum fun α => ((hXmB α).mul (hYmL α)).aemeasurable
    _ = ∑' α, (∫⁻ ω, Xb (fun v => (D v ω).1) α ∂P) * ∫⁻ y, ψ y ∂gaussianReal 0 1 :=
        tsum_congr fun α => by
          rw [← hYint α]
          exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hXmB α) (hYmL α)
            (hind.comp (hXm α) (hYm α))
    _ = (∫⁻ y, ψ y ∂gaussianReal 0 1) * ∫⁻ ω, ∑' α, Xb (fun v => (D v ω).1) α ∂P := by
        rw [lintegral_tsum fun α => (hXmB α).aemeasurable, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun α => mul_comm _ _

/-- The positive and negative parts of a centred Gaussian have the same integral. -/
theorem lintegral_ofReal_mul_gaussian_symm (c : ℝ) :
    ∫⁻ y, ENNReal.ofReal (c * y) ∂gaussianReal 0 1 =
      ∫⁻ y, ENNReal.ofReal (-(c * y)) ∂gaussianReal 0 1 := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (c * y) :=
    ENNReal.measurable_ofReal.comp (measurable_id.const_mul c)
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have h := lintegral_map hm (measurable_neg (G := ℝ)) (μ := gaussianReal 0 1)
  rw [show Measure.map (Neg.neg : ℝ → ℝ) (gaussianReal 0 1) = gaussianReal 0 1 from hneg] at h
  rw [h]
  simp [mul_neg]

/-- Positive parts of a Gaussian have a finite integral. -/
theorem lintegral_ofReal_mul_gaussian_lt_top (c : ℝ) :
    ∫⁻ y, ENNReal.ofReal (c * y) ∂gaussianReal 0 1 < ∞ :=
  (IsGaussian.integrable_id (μ := gaussianReal 0 1)).const_mul c |>.lintegral_lt_top

/-- The total mass of the Ruelle cascade is almost surely positive and finite. -/
theorem ae_cascadeMass_pos_finite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ : ℕ → ℝ) (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ) (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P) :
    ∀ᵐ ω ∂P, (∑' α : Fin r → ℕ, cascadeBranchWeight (fun p γ m => nthLargestAtom m
      (poissonCountingMeasure (fun k => ((D ⟨p, γ⟩ ω).1 k).1)
        (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l))) α) ≠ 0 ∧
      (∑' α : Fin r → ℕ, cascadeBranchWeight (fun p γ m => nthLargestAtom m
        (poissonCountingMeasure (fun k => ((D ⟨p, γ⟩ ω).1 k).1)
          (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l))) α) < ∞ := by
  have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
  have hmom := lintegral_cascadeMarkedSum_rpow_lt_top (P := P) r ζ hζ0 hζ1 hmono nu rate hmu
    (gaussianReal 0 1) 𝔡 h𝔡 D hDm hD hDlaw (fun _ => 1) measurable_const
    (Filter.Eventually.of_forall fun _ => one_ne_zero)
    (Filter.Eventually.of_forall fun _ => ENNReal.one_ne_top) (ζ 0 / 2) 1 (half_pos (hζ0 0))
    (half_lt_self (hζ0 0)) (fun _ => by linarith [hζ1 0, hζ0 0])
    (fun k _ => (hζ1 k).le) (by simp)
  have hDvec : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D v ω := measurable_pi_iff.2 hDm
  have hmeas := measurable_cascadeMarkedSum r (X := fun _ : Fin r → ℝ => (0 : ℝ)) measurable_const
    (g := fun _ => 1) measurable_const
  have hfin := ae_lt_top ((hmeas.comp hDvec).pow_const (ζ 0 / 2)) hmom.ne
  have hatoms := ae_cascadeData_atoms_pos_finite ζ hζ0 hζ1 nu rate hmu (gaussianReal 0 1) D hDm
    fun v => by rw [← h𝔡 v.1]; exact hDlaw v
  filter_upwards [hfin, hatoms] with ω h1 h2
  have hS : cascadeMarkedSum r (fun _ => (0 : ℝ)) (fun _ => 1) (fun v => D v ω) =
      ∑' α : Fin r → ℕ, cascadeBranchWeight (fun p γ m => nthLargestAtom m
        (poissonCountingMeasure (fun k => ((D ⟨p, γ⟩ ω).1 k).1)
          (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l))) α := by
    simp [cascadeMarkedSum]
  refine ⟨?_, ?_⟩
  · rw [← hS]
    exact cascadeMarkedSum_ne_zero r (fun _ => (0 : ℝ)) (fun _ => 1) (fun v => D v ω)
      (fun p γ m => (h2 ⟨p, γ⟩ m).1) fun _ => one_ne_zero
  · rw [← hS]
    exact (ENNReal.rpow_lt_top_iff_of_pos (half_pos (hζ0 0))).1 h1

/-- **Lemma 2.5 of Panchenko for `k = (1, 0, …, 0)`, in expectation.** For a function `F` of the
overlap pattern bounded by `C`, the expected positive and negative parts of the Gibbs averages
`⟨f(Rⁿ) σᵢ (label of σ^{l₀} at level i - tσᵢζᵢ)⟩_t` coincide and are finite, for every `t`.
Summing over the levels, `E⟨f (g(σ^{l₀}) - t b)⟩_t = 0` with `b = ∑ᵢ σᵢ² ζᵢ`. -/
theorem lintegral_cascadeGibbsAt_tilt_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ σ : ℕ → ℝ) (t : ℝ) (hζ0 : ∀ p, 0 < ζ p)
    (hζ1 : ∀ p, ζ p < 1) (hmono : StrictMono ζ) (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (lab : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ)
    (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ∞) (hf : ∀ P, F P ≤ C)
    (l₀ : Fin n) (i : Fin r) :
    ∫⁻ ω, replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (σ i * y))
        (t * σ i * ζ i) (u ω) (lab ω) ∂P =
      ∫⁻ ω, replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (-(σ i * y)))
        (t * σ i * ζ i) (u ω) (lab ω) ∂P ∧
    ∫⁻ ω, replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (σ i * y))
        (t * σ i * ζ i) (u ω) (lab ω) ∂P < ∞ := by
  have h := identDistrib_cascadeGibbsAt_tilt r ζ σ t hζ0 hζ1 nu rate hmu 𝔡 h𝔡 D hDm hD hDlaw u hu
    lab hlab n F
    l₀
  have hp := (h.comp (measurable_pi_apply (i, true))).lintegral_eq
  have hn := (h.comp (measurable_pi_apply (i, false))).lintegral_eq
  simp only [Function.comp_apply, ite_true, Bool.false_eq_true, ite_false] at hp hn
  have hmeas : ∀ c : ℝ, Measurable fun y : ℝ => ENNReal.ofReal (c * y) := fun c =>
    ENNReal.measurable_ofReal.comp (measurable_id.const_mul c)
  have hmeas' : Measurable fun y : ℝ => ENNReal.ofReal (-(σ i * y)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.const_mul (σ i)).neg
  have hz1 := lintegral_cascadeGibbsAt_zero r σ nu rate 𝔡 h𝔡 D hDm hD hDlaw u hu lab hlab n F l₀ i _
    (hmeas (σ i))
  have hz2 := lintegral_cascadeGibbsAt_zero r σ nu rate 𝔡 h𝔡 D hDm hD hDlaw u hu lab hlab n F l₀ i _
    hmeas'
  have hbound : ∫⁻ ω, replicaGibbs r n σ 0 F (u ω) (lab ω) ∂P ≤ C := by
    have hae := ae_cascadeMass_pos_finite (P := P) r ζ hζ0 hζ1 hmono nu rate hmu 𝔡 h𝔡 D hDm hD
      hDlaw
    calc ∫⁻ ω, replicaGibbs r n σ 0 F (u ω) (lab ω) ∂P ≤ ∫⁻ _, C ∂P :=
          lintegral_mono_ae (by
            filter_upwards [hae] with ω hω
            obtain ⟨h1, h2⟩ := hω
            subst hu hlab
            simpa using replicaGibbs_le r n σ 0 F C hf _ _ (by simpa using h1)
              (by simpa using h2.ne))
      _ = C := by simp
  refine ⟨?_, ?_⟩
  · rw [hp, hn, hz1, hz2, lintegral_ofReal_mul_gaussian_symm (σ i)]
  · rw [hp, hz1]
    exact ENNReal.mul_lt_top (lintegral_ofReal_mul_gaussian_lt_top (σ i))
      (lt_of_le_of_lt hbound hC.lt_top)

end SpinGlasses
