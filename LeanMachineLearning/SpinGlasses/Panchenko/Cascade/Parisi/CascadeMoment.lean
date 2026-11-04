/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeMarked
public import LeanMachineLearning.SpinGlasses.PoissonDirichlet

/-!
# Fractional moments of the ranked marked sum

One step of the moment induction behind Lemma 2.4: if the marks `T n` of the ranked root
atoms are independent of the root, identically distributed, and have a finite `ζ`-th moment,
then the marked sum `∑ n, U n * T n` has a finite `a`-th moment for every `0 < a < ζ`.
-/

@[expose] public section

namespace SpinGlasses

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The `a`-th moment of the marked ranked sum is finite when the marks have a finite
`ζ`-th moment, for `0 < a < ζ < 1`. The marks need not be finite or positive a priori
on a null set; the root atoms and the marks are only assumed positive almost surely. -/
theorem lintegral_rankedRoot_marked_sum_rpow_lt_top
    [IsProbabilityMeasure P] {ζ a : ℝ}
    (hζ : 0 < ζ) (ha0 : 0 < a) (haζ : a < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ENNReal) • nu k)
    (T : Ω → ℕ → ENNReal) (hTm : Measurable T)
    (hind : IndepFun (fun ω => fun k => B k ω) T P)
    (τ : Measure ENNReal) [IsProbabilityMeasure τ]
    (hTlaw : ∀ n, HasLaw (fun ω => T ω n) τ P)
    (hmom : ∫⁻ t, t ^ ζ ∂τ ≠ ∞)
    (hTpos : ∀ᵐ ω ∂P, ∀ n, T ω n ≠ 0)
    (hUpos : ∀ᵐ ω ∂P, ∀ n, nthLargestAtom n (poissonCountingMeasure
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) ≠ 0 ∧
      nthLargestAtom n (poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) ≠ ∞) :
    ∫⁻ ω, (∑' n, nthLargestAtom n (poissonCountingMeasure
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n) ^ a ∂P < ∞ := by
  let U (ω : Ω) (n : ℕ) := nthLargestAtom n (poissonCountingMeasure
    (fun k => (B k ω).1) (fun k l => (B k ω).2 l))
  have hpow : Measurable (fun t : ENNReal => t ^ ζ) := by fun_prop
  have hfinite : ∀ᵐ t ∂τ, t ≠ ∞ := by
    filter_upwards [ae_lt_top hpow hmom] with t ht
    rintro rfl
    simp [ENNReal.top_rpow_of_pos hζ] at ht
  have hm0 : ∫⁻ t, t ^ ζ ∂τ ≠ 0 := by
    intro h0
    have hzero : ∀ᵐ t ∂τ, t = 0 := by
      filter_upwards [(lintegral_eq_zero_iff hpow).1 h0] with t ht
      exact (ENNReal.rpow_eq_zero_iff_of_pos hζ).1 ht
    have hzero' : ∀ᵐ ω ∂P, T ω 0 = 0 :=
      (ae_map_iff (hTlaw 0).aemeasurable (measurableSet_singleton 0)).1
        (by rw [(hTlaw 0).map_eq]; exact hzero)
    obtain ⟨ω, h1, h2⟩ := (hTpos.and hzero').exists
    exact h1 0 h2
  let c : ENNReal := (∫⁻ t, t ^ ζ ∂τ) ^ ζ⁻¹
  have hc0 : c ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hm0) hmom).ne'
  have hcfin : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hζ.le) hmom
  have hmoment : ∫⁻ t, t ^ ζ ∂τ = c ^ ζ := (ENNReal.rpow_inv_rpow hζ.ne' _).symm
  have two := lintegral_rankedRoot_normalized_two_tests hζ ha0 haζ hζ1 nu rate B hBm hB hlaw
    hmu T hTm hind τ hTlaw hfinite c hc0 hcfin hmoment
  let M (ω : Ω) : Measure ℝ := poissonCountingMeasure (fun _ => 1)
    (fun n _ => (U ω n * T ω n / c).toReal)
  have hUm (n : ℕ) : Measurable fun ω => U ω n :=
    (measurable_nthLargestAtom n).comp
      (measurable_poissonCountingMeasure_comp hBm)
  have hTmn (n : ℕ) : Measurable fun ω => T ω n := (measurable_pi_apply n).comp hTm
  have hMm : Measurable M :=
    measurable_poissonCountingMeasure_comp (B := fun n ω => ((1 : ℕ),
      fun _ => (U ω n * T ω n / c).toReal))
      fun n => measurable_const.prodMk (measurable_pi_iff.2 fun _ =>
        ENNReal.measurable_toReal.comp (((hUm n).mul (hTmn n)).div_const c))
  have bound := lintegral_poisson_sum_rpow_le_of_two_tests (M := M) ha0 haζ hζ1 hMm
    (fun ω => ⟨_, _, rfl⟩) two.1 two.2
  have hTfin : ∀ᵐ ω ∂P, ∀ n, T ω n ≠ ∞ := by
    refine ae_all_iff.2 fun n => ?_
    exact (ae_map_iff (hTlaw n).aemeasurable (measurableSet_singleton ∞).compl).1
      (by rw [(hTlaw n).map_eq]; exact hfinite)
  have hmass : ∀ᵐ ω ∂P, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) =
      (∑' n, U ω n * T ω n) / c := by
    filter_upwards [hTpos, hUpos, hTfin] with ω hT hU hF
    rw [← lintegral_indicator measurableSet_Ioi]
    change ∫⁻ x, (Ioi (0 : ℝ)).indicator ENNReal.ofReal x ∂poissonCountingMeasure
      (fun _ => 1) (fun n _ => (U ω n * T ω n / c).toReal) = _
    rw [lintegral_poissonCountingMeasure_singletons _
      (ENNReal.measurable_ofReal.indicator measurableSet_Ioi)]
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun n => ?_
    have hne : U ω n * T ω n * c⁻¹ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (hU n).2 (hF n)) (ENNReal.inv_ne_top.2 hc0)
    have hpos : 0 < U ω n * T ω n * c⁻¹ :=
      pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero (hU n).1 (hT n))
        (ENNReal.inv_ne_zero.2 hcfin))
    rw [indicator_of_mem (by simpa using ENNReal.toReal_pos hpos.ne' hne),
      ENNReal.ofReal_toReal hne]
  have hident : ∀ ω, (∑' n, U ω n * T ω n) ^ a =
      c ^ a * ((∑' n, U ω n * T ω n) / c) ^ a := by
    intro ω
    rw [ENNReal.div_rpow_of_nonneg _ _ ha0.le, ENNReal.mul_div_cancel
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hcfin).ne'
      (ENNReal.rpow_ne_top_of_nonneg ha0.le hcfin)]
  calc ∫⁻ ω, (∑' n, U ω n * T ω n) ^ a ∂P
      = ∫⁻ ω, c ^ a * ((∑' n, U ω n * T ω n) / c) ^ a ∂P := lintegral_congr hident
    _ = c ^ a * ∫⁻ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)) ^ a ∂P := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg ha0.le hcfin)]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [hmass] with ω hω
        rw [hω]
    _ < ∞ := by
        refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ha0.le hcfin) ?_
        refine lt_of_le_of_lt bound ?_
        simp [ENNReal.add_lt_top]

/-- **Moment induction for Lemma 2.4.** For a globally independent family of vertex blocks with
`0 < ζ p < 1` and `ζ` strictly increasing, the `a`-th moment of the depth-`r` total mass is
finite for every `0 < a < ζ 0`. The strict monotonicity is what lets the induction hypothesis
for the shifted exponents `ζ ∘ succ` control the `ζ 0`-th moment of a subtree total. -/
theorem lintegral_tsum_cascadeBranchWeight_rpow_lt_top
    [IsProbabilityMeasure P] (r : ℕ) (zeta : ℕ → ℝ)
    (hzeta0 : ∀ p, 0 < zeta p) (hzeta1 : ∀ p, zeta p < 1) (hmono : StrictMono zeta)
    (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : ∀ p, zetaPoissonMeasure (zeta p) =
      Measure.sum fun k => (rate p k : ENNReal) • nu p k)
    {a : ℝ} (ha0 : 0 < a) (haζ : a < zeta 0) :
    ∫⁻ ω, (∑' beta : Fin r → ℕ, cascadeBranchWeight
      (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l))) beta) ^ a ∂P
      < ∞ := by
  induction r generalizing zeta nu rate B a with
  | zero =>
    simp only [tsum_cascadeBranchWeight_zero, ENNReal.one_rpow, lintegral_const, measure_univ,
      mul_one]
    exact ENNReal.one_lt_top
  | succ r ih =>
    let T (ω : Ω) (n : ℕ) := ∑' beta : Fin r → ℕ, cascadeBranchWeight
      (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
        (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l))) beta
    have hTm : Measurable T := measurable_pi_iff.2 fun n => by
      apply measurable_tsum_cascadeBranchWeight
      intro p gamma m
      exact (measurable_nthLargestAtom m).comp
        (measurable_poissonCountingMeasure_comp (fun k => hBm ⟨p + 1, Fin.cons n gamma⟩ k))
    have hmomn (n : ℕ) : ∫⁻ ω, T ω n ^ zeta 0 ∂P < ∞ :=
      ih (fun p => zeta (p + 1)) (fun p => hzeta0 _) (fun p => hzeta1 _)
        (fun p q h => hmono (Nat.succ_lt_succ h)) (fun p k => nu (p + 1) k)
        (fun p k => rate (p + 1) k)
        (fun v k => B ⟨v.1 + 1, Fin.cons n v.2⟩ k)
        (fun v k => hBm _ k) (iIndepFun_cascadeChildBlocks B hB n)
        (fun v k => hlaw ⟨v.1 + 1, Fin.cons n v.2⟩ k) (fun p => hmu (p + 1))
        (hzeta0 0) (hmono Nat.zero_lt_one)
    have hTmn (n : ℕ) : Measurable fun ω => T ω n := (measurable_pi_apply n).comp hTm
    let τ : Measure ENNReal := P.map fun ω => T ω 0
    have hlawT (n : ℕ) : HasLaw (fun ω => T ω n) τ P :=
      ⟨(hTmn n).aemeasurable,
        (hasLaw_cascadeChildTotal nu rate B hBm hB hlaw n r).map_eq.trans
          (hasLaw_cascadeChildTotal nu rate B hBm hB hlaw 0 r).map_eq.symm⟩
    have hmom : ∫⁻ t, t ^ zeta 0 ∂τ ≠ ∞ := by
      have := (hlawT 0).lintegral_comp (f := fun t : ENNReal => t ^ zeta 0) (by fun_prop)
      exact (this.symm.trans_ne (hmomn 0).ne)
    have hpos := ae_cascadeRankedMass_pos_finite zeta hzeta0 hzeta1 nu rate B
      (fun ω p gamma m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)))
      (fun _ _ _ _ => rfl) hBm hB hlaw hmu
    have hstep := lintegral_rankedRoot_marked_sum_rpow_lt_top (hzeta0 0) ha0 haζ (hzeta1 0)
      (nu 0) (rate 0) (B ⟨0, fun i => i.elim0⟩) (fun k => hBm _ k)
      (iIndepFun_cascadeVertexBlocks B hB _) (fun k => hlaw _ k) (hmu 0) T hTm
      (indepFun_cascadeRoot_subtreeTotals B hBm hB r) τ hlawT hmom
      (by
        filter_upwards [hpos] with ω hω n
        exact tsum_cascadeBranchWeight_ne_zero _ (fun p gamma m => (hω _ _ _).1) r)
      (by
        filter_upwards [hpos] with ω hω n
        exact hω 0 (fun i => i.elim0) n)
    simpa only [tsum_cascadeBranchWeight_cons] using hstep

/-- **Lemma 2.4 (Panchenko), unconditional.** In the independent-vertex Poisson cascade the
total mass `∑_{α ∈ ℕ^r} w_α` is almost surely finite at every depth `r`. -/
theorem ae_cascadeRankedMass_lt_top
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : ∀ p, 0 < zeta p) (hzeta1 : ∀ p, zeta p < 1) (hmono : StrictMono zeta)
    (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ ω p gamma m, u ω p gamma m = nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : ∀ p, zetaPoissonMeasure (zeta p) =
      Measure.sum fun k => (rate p k : ENNReal) • nu p k) (r : ℕ) :
    ∀ᵐ ω ∂P, ∑' alpha : Fin r → ℕ, cascadeBranchWeight (u ω) alpha < ∞ := by
  have hu' : u = fun ω p gamma m => nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)) := by
    funext ω p gamma m
    exact hu ω p gamma m
  subst hu'
  have ha0 : 0 < zeta 0 / 2 := half_pos (hzeta0 0)
  have hmom := lintegral_tsum_cascadeBranchWeight_rpow_lt_top r zeta hzeta0 hzeta1 hmono nu
    rate B hBm hB hlaw hmu ha0 (half_lt_self (hzeta0 0))
  have hmeas := measurable_tsum_cascadeRankedMass B _ (fun _ _ _ _ => rfl) hBm r
  filter_upwards [ae_lt_top (hmeas.pow_const (zeta 0 / 2)) hmom.ne] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos ha0).1 hω

/-- **Lemma 2.4, normalized form.** The normalized branch weights of the independent-vertex
Poisson cascade sum to one and are strictly positive, almost surely, at every depth. -/
theorem ae_cascadeRankedMass_div_probability
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : ∀ p, 0 < zeta p) (hzeta1 : ∀ p, zeta p < 1) (hmono : StrictMono zeta)
    (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ ω p gamma m, u ω p gamma m = nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : ∀ p, zetaPoissonMeasure (zeta p) =
      Measure.sum fun k => (rate p k : ENNReal) • nu p k) (r : ℕ) :
    ∀ᵐ ω ∂P,
      (∑' alpha : Fin r → ℕ, cascadeBranchWeight (u ω) alpha /
        ∑' beta : Fin r → ℕ, cascadeBranchWeight (u ω) beta) = 1 ∧
      ∀ alpha : Fin r → ℕ,
        cascadeBranchWeight (u ω) alpha /
          (∑' beta : Fin r → ℕ, cascadeBranchWeight (u ω) beta) ≠ 0 := by
  have hf := ae_cascadeRankedMass_lt_top zeta hzeta0 hzeta1 hmono nu rate B u hu hBm hB hlaw
    hmu r
  have hp := ae_cascadeRankedMass_pos_finite
    zeta hzeta0 hzeta1 nu rate B u hu hBm hB hlaw hmu
  exact ae_cascadeBranchWeight_div_probability (u) r hf
    (hp.mono fun _ h p gamma m => (h p gamma m).1)
    (hp.mono fun _ h p gamma m => (h p gamma m).2)

end SpinGlasses
