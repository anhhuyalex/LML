/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeIdentities

/-!
# The Gibbs series of the Ruelle cascade as a linear functional

For `m` replicas and a function `Ξ` of their overlap pattern, `gibbs m t Ξ ω` is the Gibbs series
of the weights `w_α exp (t g(α))` of the cascade at `ω`. It is an abstract function given by the
equation `hgibbs`, as is done for the atoms `u` and the labels `lab`. This file collects its
properties: measurability, boundedness, linearity in `Ξ` (every function of a pattern is bounded,
the pattern set being finite), invariance under adding a replica, and the invariance of its
expectation under the tilt (Lemma 2.5 for `k = 0`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

section Gibbs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (r : ℕ) (ζ σ : ℕ → ℝ) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
  (rate : (p : ℕ) → ℕ → ℝ≥0)
  (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
  (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))
  (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
  (lab : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)
  (gibbs : (m : ℕ) → ℝ → ((Fin m → Fin m → Fin (r + 1)) → ℝ) → Ω → ℝ)

/-- Every real function of the overlap pattern of `m` replicas is bounded. -/
theorem exists_abs_le_pattern {m : ℕ} (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    ∃ M : ℝ, ∀ P, |Ξ P| ≤ M := by
  obtain ⟨M, hM⟩ := Set.Finite.bddAbove (Set.finite_range fun P => |Ξ P|)
  exact ⟨M, fun P => hM ⟨P, rfl⟩⟩

variable (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1) (hmono : StrictMono ζ)
  (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
  (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
    Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
  (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
  (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
    (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
  (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k)
  (hgibbs : ∀ (m : ℕ) (t : ℝ) (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) (ω : Ω),
    gibbs m t Ξ ω = ∑' τ : Fin m → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
        Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
      ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
        Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
      Ξ (fun l l' => prefixOverlap (τ l) (τ l')))

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab in
/-- The weights `w_α exp (t g(α))` are almost surely nonnegative, summable, with a nonzero sum. -/
theorem ae_cascadeWeights_good (t : ℝ) : ∀ᵐ ω ∂P,
    (∀ α : Fin r → ℕ, 0 ≤ (cascadeBranchWeight (u ω) α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i)) ∧
    Summable (fun α : Fin r → ℕ => (cascadeBranchWeight (u ω) α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i)) ∧
    ∑' α : Fin r → ℕ, (cascadeBranchWeight (u ω) α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i) ≠ 0 := by
  have h0 := ae_cascadeMass_pos_finite_omega r ζ nu rate 𝔡 D u hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu
  have ht := ae_tiltedMass_pos_finite (P := P) r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab t
  filter_upwards [h0, ht] with ω hω0 hωt
  obtain ⟨hs, hne⟩ := summable_tsum_ne_zero_cascadeWeight r σ t (u ω) (lab ω)
    (fun α => ENNReal.ne_top_of_tsum_ne_top hω0.2.ne α) hωt.1 hωt.2
  exact ⟨fun α => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le, hs, hne⟩

include hDm hu hlab hgibbs in
/-- The Gibbs series is a measurable function of `ω`. -/
theorem measurable_gibbs (m : ℕ) (t : ℝ) (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    Measurable (gibbs m t Ξ) := by
  have hBm : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => (D v ω).1 :=
    measurable_pi_iff.2 fun v => measurable_fst.comp (hDm v)
  have hw : ∀ α : Fin r → ℕ, Measurable fun ω => (cascadeBranchWeight (u ω) α).toReal :=
    fun α => by
      subst hu
      have h := (measurable_branchWeight_blocks α).comp hBm
      exact ENNReal.measurable_toReal.comp h
  have hl : ∀ (α : Fin r → ℕ) (i : Fin r), Measurable fun ω => leafLabel (lab ω) α i :=
    fun α i => by
      subst hlab
      exact (measurable_pi_apply (α i)).comp (measurable_snd.comp (hDm _))
  have hW : ∀ α : Fin r → ℕ, Measurable fun ω => (cascadeBranchWeight (u ω) α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i) := fun α =>
    (hw α).mul (Real.measurable_exp.comp (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => measurable_const.mul (hl α i))))
  have h := measurable_tsum_prod_div_mul (K := Fin m)
    (fun (ω : Ω) (α : Fin r → ℕ) => (cascadeBranchWeight (u ω) α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i)) hW
    (fun τ _ => Ξ (fun l l' => prefixOverlap (τ l) (τ l'))) fun τ => measurable_const
  have e : gibbs m t Ξ = _ := funext (hgibbs m t Ξ)
  rw [e]
  exact h

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs in
/-- The Gibbs series of a bounded observable is bounded by the same constant. -/
theorem abs_gibbs_le (t : ℝ) {m : ℕ} (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) {M : ℝ}
    (hΞ : ∀ P, |Ξ P| ≤ M) : ∀ᵐ ω ∂P, |gibbs m t Ξ ω| ≤ M := by
  filter_upwards [ae_cascadeWeights_good r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab t] with ω ⟨h1, h2, h3⟩
  rw [hgibbs]
  exact abs_tsum_prod_div_mul_le h1 h2 h3 fun τ => hΞ _

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs in
/-- The Gibbs series of a function of the overlap pattern is integrable. -/
theorem integrable_gibbs (t : ℝ) {m : ℕ} (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    Integrable (gibbs m t Ξ) P := by
  obtain ⟨M, hM⟩ := exists_abs_le_pattern r Ξ
  refine Integrable.of_bound (measurable_gibbs r σ D u lab gibbs hDm hu hlab hgibbs m t
    Ξ).aestronglyMeasurable M ?_
  exact (abs_gibbs_le r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab
    hgibbs t Ξ hM).mono fun ω h => by rwa [Real.norm_eq_abs]

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs in
/-- The Gibbs series is additive in the observable (finite sums). -/
theorem gibbs_finset_sum (t : ℝ) {m : ℕ} {ι : Type*} (s : Finset ι)
    (Ξ : ι → (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    ∀ᵐ ω ∂P, gibbs m t (fun P => ∑ i ∈ s, Ξ i P) ω = ∑ i ∈ s, gibbs m t (Ξ i) ω := by
  filter_upwards [ae_cascadeWeights_good r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab t] with ω ⟨h1, h2, h3⟩
  have hs : ∀ i ∈ s, Summable fun τ : Fin m → Fin r → ℕ =>
      (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        Ξ i (fun l l' => prefixOverlap (τ l) (τ l')) := fun i _ => by
    obtain ⟨M, hM⟩ := exists_abs_le_pattern r (Ξ i)
    exact summable_prod_div_mul h1 h2 h3 (Φ := fun τ => Ξ i (fun l l' => prefixOverlap (τ l)
      (τ l'))) (M := M) fun τ => hM _
  simp only [hgibbs]
  rw [← Summable.tsum_finsetSum hs]
  refine tsum_congr fun τ => ?_
  rw [Finset.mul_sum]

omit [MeasurableSpace Ω] in
include hgibbs in
/-- The Gibbs series is homogeneous in the observable. -/
theorem gibbs_const_mul (t : ℝ) {m : ℕ} (c : ℝ) (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ)
    (ω : Ω) : gibbs m t (fun P => c * Ξ P) ω = c * gibbs m t Ξ ω := by
  simp only [hgibbs]
  rw [← tsum_mul_left]
  refine tsum_congr fun τ => ?_
  ring

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs in
/-- **Adding a replica does not change the Gibbs series** of an observable of the first `n`
replicas. -/
theorem gibbs_castSucc (t : ℝ) {n : ℕ} (Ξ : (Fin n → Fin n → Fin (r + 1)) → ℝ) :
    ∀ᵐ ω ∂P, gibbs (n + 1) t (fun P => Ξ fun l l' => P l.castSucc l'.castSucc) ω =
      gibbs n t Ξ ω := by
  obtain ⟨M, hM⟩ := exists_abs_le_pattern r Ξ
  filter_upwards [ae_cascadeWeights_good r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab t] with ω ⟨h1, h2, h3⟩
  simp only [hgibbs]
  exact tsum_prod_div_mul_castSucc h1 h2 h3 (Φ := fun τ => Ξ (fun l l' =>
    prefixOverlap (τ l) (τ l'))) (M := M) fun τ => hM _

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs in
/-- **Lemma 2.5 for `k = 0`:** the expected Gibbs series of a function of the overlap pattern
does not depend on the tilt. -/
theorem integral_gibbs_tilt (t : ℝ) {m : ℕ} (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    ∫ ω, gibbs m t Ξ ω ∂P = ∫ ω, gibbs m 0 Ξ ω ∂P := by
  obtain ⟨M, hM⟩ := exists_abs_le_pattern r Ξ
  simp_rw [hgibbs]
  exact integral_cascadeSeries_tilt r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
    hlab m t Ξ hM

omit [MeasurableSpace Ω] in
include hgibbs in
/-- The Gibbs series only depends on the values of the observable at realizable patterns. -/
theorem gibbs_congr (t : ℝ) {m : ℕ} (Ξ₁ Ξ₂ : (Fin m → Fin m → Fin (r + 1)) → ℝ)
    (h : ∀ τ : Fin m → Fin r → ℕ, Ξ₁ (fun l l' => prefixOverlap (τ l) (τ l')) =
      Ξ₂ (fun l l' => prefixOverlap (τ l) (τ l'))) (ω : Ω) :
    gibbs m t Ξ₁ ω = gibbs m t Ξ₂ ω := by
  simp only [hgibbs]
  exact tsum_congr fun τ => by rw [h τ]

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs in
/-- The expected Gibbs series is linear in the observable. -/
theorem integral_gibbs_sum_const_mul (t : ℝ) {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (Ξ : ι → (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    ∫ ω, gibbs m t (fun P => ∑ i ∈ s, c i * Ξ i P) ω ∂P =
      ∑ i ∈ s, c i * ∫ ω, gibbs m t (Ξ i) ω ∂P := by
  have h := gibbs_finset_sum r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
    hlab hgibbs t s (fun i P => c i * Ξ i P)
  rw [integral_congr_ae h, integral_finsetSum _ fun i _ =>
    integrable_gibbs r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab
      hgibbs t _]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [gibbs_const_mul r σ u lab gibbs hgibbs t (c i)]
  rw [integral_const_mul]

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs in
/-- **The Ghirlanda--Guerra identity for a general covariance `Q`.** Let `Q m = ∑_{i < m} σᵢ²`
and `b = ∑ᵢ σᵢ² ζᵢ`. For a nonnegative function `f` of the overlap pattern of `n` replicas,
`n E⟨f Q(σ^{l₀} ∧ σ^{n+1})⟩ = (Q_r - b) E⟨f⟩ + ∑_{l ≠ l₀} E⟨f Q(σ^{l₀} ∧ σ^l)⟩`,
where `⟨·⟩` is the Gibbs average of the weights `w_α`. -/
theorem ghirlandaGuerra_Q (n : ℕ) (f : (Fin n → Fin n → Fin (r + 1)) → ℝ) (hf : ∀ P, 0 ≤ f P)
    (l₀ : Fin n) (Q : Fin (r + 1) → ℝ)
    (hQ : ∀ m, Q m = ∑ i : Fin r, if i.val < m.val then σ i ^ 2 else 0) :
    (n : ℝ) * ∫ ω, gibbs (n + 1) 0 (fun P => f (fun l l' => P l.castSucc l'.castSucc) *
        Q (P l₀.castSucc (Fin.last n))) ω ∂P =
      (Q (Fin.last r) - ∑ i : Fin r, σ i ^ 2 * ζ i) * ∫ ω, gibbs n 0 f ω ∂P +
        ∑ l ∈ Finset.univ.erase l₀, ∫ ω, gibbs n 0 (fun P => f P * Q (P l₀ l)) ω ∂P := by
  obtain ⟨M, hM⟩ := exists_abs_le_pattern r f
  have hF : ∀ P, ENNReal.ofReal (f P) ≤ ENNReal.ofReal M := fun P =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM P))
  obtain ⟨-, h2, h3⟩ := integral_cascade_ibp r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab n (fun P => ENNReal.ofReal (f P)) (ENNReal.ofReal M) ENNReal.ofReal_ne_top hF l₀
    Q hQ
  obtain ⟨c, hc0, hc1⟩ : ∃ c : Option (Fin n) → ℝ, c none = -n ∧ ∀ k, c (some k) = 1 :=
    ⟨fun o => Option.elim o (-(n : ℝ)) fun _ => 1, rfl, fun _ => rfl⟩
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : Option (Fin n) → (Fin (n + 1) → Fin (n + 1) → Fin (r + 1)) → ℝ,
      ∀ o P, Ξ o P = f (fun l l' => P l.castSucc l'.castSucc) *
        Q (P l₀.castSucc (finSuccEquivLast.symm o)) := ⟨_, fun _ _ => rfl⟩
  have e2 : ∀ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        (ENNReal.ofReal (f fun l l' => prefixOverlap (τ l) (τ l'))).toReal =
      gibbs n 1 f ω := fun ω => by
    rw [hgibbs]
    simp_rw [one_mul]
    exact tsum_congr fun τ => by rw [ENNReal.toReal_ofReal (hf _)]
  have e3 : ∀ ω, ∑' τ : Option (Fin n) → Fin r → ℕ, (∏ o, (cascadeBranchWeight (u ω) (τ o)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ o) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((ENNReal.ofReal (f fun l l' => prefixOverlap (τ (some l)) (τ (some l')))).toReal *
          (∑ k : Fin n, Q (prefixOverlap (τ (some l₀)) (τ (some k))) -
            n * Q (prefixOverlap (τ (some l₀)) (τ none)))) =
      gibbs (n + 1) 1 (fun P => ∑ o, c o * Ξ o P) ω := fun ω => by
    rw [hgibbs]
    simp_rw [one_mul]
    refine (tsum_option_fin_eq (W := fun α => (cascadeBranchWeight (u ω) α).toReal *
      Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) α i)) _).trans ?_
    refine tsum_congr fun τ => ?_
    congr 1
    simp only [hΞ, Fintype.sum_option, hc0, hc1, one_mul, finSuccEquivLast_symm_some,
      finSuccEquivLast_symm_none, ENNReal.toReal_ofReal (hf _)]
    rw [← Finset.mul_sum]
    ring
  simp_rw [e2] at h2
  simp_rw [e3] at h3
  have hb := h2.symm.trans h3
  rw [integral_gibbs_tilt r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab
    hgibbs 1 f, integral_gibbs_tilt r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs 1 (fun P => ∑ o, c o * Ξ o P),
    integral_gibbs_sum_const_mul r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
      hlab hgibbs 0 Finset.univ c Ξ, Fintype.sum_option] at hb
  have hnone : ∫ ω, gibbs (n + 1) 0 (Ξ none) ω ∂P = ∫ ω, gibbs (n + 1) 0 (fun P =>
      f (fun l l' => P l.castSucc l'.castSucc) * Q (P l₀.castSucc (Fin.last n))) ω ∂P := by
    congr 1
    funext ω
    congr 1
    funext P
    rw [hΞ, finSuccEquivLast_symm_none]
  have hsome : ∀ k : Fin n, ∫ ω, gibbs (n + 1) 0 (Ξ (some k)) ω ∂P =
      ∫ ω, gibbs n 0 (fun P => f P * Q (P l₀ k)) ω ∂P := fun k => by
    have h := gibbs_castSucc r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
      hlab hgibbs 0 (fun P => f P * Q (P l₀ k))
    rw [← integral_congr_ae h]
    congr 1
    funext ω
    congr 1
    funext P
    rw [hΞ, finSuccEquivLast_symm_some]
  have hself : ∫ ω, gibbs n 0 (fun P => f P * Q (P l₀ l₀)) ω ∂P =
      Q (Fin.last r) * ∫ ω, gibbs n 0 f ω ∂P := by
    have e : ∀ ω, gibbs n 0 (fun P => f P * Q (P l₀ l₀)) ω =
        Q (Fin.last r) * gibbs n 0 f ω := fun ω => by
      rw [← gibbs_const_mul r σ u lab gibbs hgibbs 0 (Q (Fin.last r)) f ω]
      refine gibbs_congr r σ u lab gibbs hgibbs 0 _ _ (fun τ => ?_) ω
      simp only [prefixOverlap_self]
      ring
    simp_rw [e]
    rw [integral_const_mul]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun k : Fin n => ∫ ω, gibbs n 0 (fun P => f P * Q (P l₀ k)) ω ∂P) (Finset.mem_univ l₀)
  simp only [hc0, hc1, hnone, hsome, one_mul] at hb
  rw [hself] at hsplit
  linarith
end Gibbs

section Overlap

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (r : ℕ) (ζ : ℕ → ℝ) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
  (rate : (p : ℕ) → ℕ → ℝ≥0)
  (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
  (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))
  (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
  (lab : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)
  (gibbs0 : (m : ℕ) → ((Fin m → Fin m → Fin (r + 1)) → ℝ) → Ω → ℝ)
  (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1) (hmono : StrictMono ζ)
  (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
  (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
    Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
  (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
  (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
    (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
  (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k)
  (hgibbs0 : ∀ (m : ℕ) (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) (ω : Ω),
    gibbs0 m Ξ ω = ∑' τ : Fin m → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal /
      ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal) *
      Ξ (fun l l' => prefixOverlap (τ l) (τ l')))

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- **The Ghirlanda--Guerra identity for the indicator of "the overlap exceeds level `j`".**
For a nonnegative function `f` of the overlap pattern of `n` replicas and a level `j < r`,
`n E⟨f 1[σ^{l₀} ∧ σ^{n+1} > j]⟩ = (1 - ζ_j) E⟨f⟩ + ∑_{l ≠ l₀} E⟨f 1[σ^{l₀} ∧ σ^l > j]⟩`,
where `⟨·⟩` is the Gibbs average of the cascade weights. -/
theorem ghirlandaGuerra_overlap_gt (j : Fin r) (n : ℕ) (f : (Fin n → Fin n → Fin (r + 1)) → ℝ)
    (hf : ∀ P, 0 ≤ f P) (l₀ : Fin n) :
    (n : ℝ) * ∫ ω, gibbs0 (n + 1) (fun P => f (fun l l' => P l.castSucc l'.castSucc) *
        if j.val < (P l₀.castSucc (Fin.last n)).val then 1 else 0) ω ∂P =
      (1 - ζ j) * ∫ ω, gibbs0 n f ω ∂P +
        ∑ l ∈ Finset.univ.erase l₀, ∫ ω, gibbs0 n (fun P => f P *
          if j.val < (P l₀ l).val then 1 else 0) ω ∂P := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℝ, ∀ i, σ i = if i = j.val then 1 else 0 :=
    ⟨fun i => if i = j.val then 1 else 0, fun _ => rfl⟩
  obtain ⟨gibbs, hgibbs⟩ : ∃ gibbs : (m : ℕ) → ℝ → ((Fin m → Fin m → Fin (r + 1)) → ℝ) →
      Ω → ℝ, ∀ (m : ℕ) (t : ℝ) (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) (ω : Ω),
      gibbs m t Ξ ω = ∑' τ : Fin m → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l')) := ⟨_, fun _ _ _ _ => rfl⟩
  have h0 : ∀ m Ξ ω, gibbs m 0 Ξ ω = gibbs0 m Ξ ω := fun m Ξ ω => by
    rw [hgibbs, hgibbs0]
    simp
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin (r + 1) → ℝ, ∀ m, Q m = if j.val < m.val then 1 else 0 :=
    ⟨fun m => if j.val < m.val then 1 else 0, fun _ => rfl⟩
  have hQσ : ∀ m, Q m = ∑ i : Fin r, if i.val < m.val then σ i ^ 2 else 0 := fun m => by
    rw [hQ, Finset.sum_eq_single j]
    · simp [hσ]
    · intro i _ hi
      have : i.val ≠ j.val := fun h => hi (Fin.ext h)
      simp [hσ, this]
    · simp
  have hG := ghirlandaGuerra_Q r ζ σ nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
    hlab hgibbs n f hf l₀ Q hQσ
  have hb : ∑ i : Fin r, σ i ^ 2 * ζ i = ζ j := by
    rw [Finset.sum_eq_single j]
    · simp [hσ]
    · intro i _ hi
      have : i.val ≠ j.val := fun h => hi (Fin.ext h)
      simp [hσ, this]
    · simp
  have hQr : Q (Fin.last r) = 1 := by
    rw [hQ]
    simp
  simp only [h0, hb, hQr] at hG
  simp only [hQ] at hG
  exact hG

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- The Gibbs average of the constant function `1` is `1`, for any number of replicas. -/
theorem integral_gibbs0_one (m : ℕ) : ∫ ω, gibbs0 m (fun _ => 1) ω ∂P = 1 := by
  classical
  have h := ae_cascadeWeights_good r ζ 0 nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
    hlab 0
  have e : ∀ᵐ ω ∂P, gibbs0 m (fun _ => 1) ω = 1 := by
    filter_upwards [h] with ω ⟨h1, h2, h3⟩
    simp only [Pi.zero_apply, zero_mul, Real.exp_zero, mul_one] at h1 h2 h3
    rw [hgibbs0]
    simp only [mul_one]
    exact (hasSum_prod_div (K := Fin m) h1 h2 h3).tsum_eq
  rw [integral_congr_ae e]
  simp

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- **The functional order parameter.** The expected Gibbs probability that the overlap of two
replicas exceeds the level `j < r` is `1 - ζ_j`. -/
theorem integral_gibbs0_overlap_gt (j : Fin r) :
    ∫ ω, gibbs0 2 (fun P => if j.val < (P 0 1).val then 1 else 0) ω ∂P = 1 - ζ j := by
  have h := ghirlandaGuerra_overlap_gt r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs0 j 1 (fun _ => 1) (fun _ => zero_le_one) 0
  rw [integral_gibbs0_one r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab
    hgibbs0] at h
  simpa using h

omit [MeasurableSpace Ω] in
include hgibbs0 in
/-- The Gibbs averages at `t = 0` are the Gibbs series of the weights `w_α`, for any field. -/
theorem exists_gibbs_zero : ∃ gibbs : (m : ℕ) → ℝ →
    ((Fin m → Fin m → Fin (r + 1)) → ℝ) → Ω → ℝ,
    (∀ (m : ℕ) (t : ℝ) (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) (ω : Ω),
      gibbs m t Ξ ω = ∑' τ : Fin m → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, (fun _ : ℕ => (0 : ℝ)) i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, (fun _ : ℕ => (0 : ℝ)) i * leafLabel (lab ω) b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l'))) ∧
    ∀ (m : ℕ) (Ξ : (Fin m → Fin m → Fin (r + 1)) → ℝ) (ω : Ω), gibbs m 0 Ξ ω = gibbs0 m Ξ ω := by
  refine ⟨fun m t Ξ ω => ∑' τ : Fin m → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, (fun _ : ℕ => (0 : ℝ)) i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, (fun _ : ℕ => (0 : ℝ)) i * leafLabel (lab ω) b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l')), fun _ _ _ _ => rfl, fun m Ξ ω => ?_⟩
  rw [hgibbs0]
  simp

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- The expected Gibbs average is linear in the observable. -/
theorem integral_gibbs0_sum_const_mul {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (Ξ : ι → (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    ∫ ω, gibbs0 m (fun P => ∑ i ∈ s, c i * Ξ i P) ω ∂P =
      ∑ i ∈ s, c i * ∫ ω, gibbs0 m (Ξ i) ω ∂P := by
  obtain ⟨gibbs, hgibbs, h0⟩ := exists_gibbs_zero r u lab gibbs0 hgibbs0
  have := integral_gibbs_sum_const_mul r ζ (fun _ => 0) nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu
    h𝔡 hDm hD hDlaw hu hlab hgibbs 0 s c Ξ
  simpa only [h0] using this

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- Adding a replica does not change the expected Gibbs average of an observable of the first `n`
replicas. -/
theorem integral_gibbs0_castSucc {n : ℕ} (Ξ : (Fin n → Fin n → Fin (r + 1)) → ℝ) :
    ∫ ω, gibbs0 (n + 1) (fun P => Ξ fun l l' => P l.castSucc l'.castSucc) ω ∂P =
      ∫ ω, gibbs0 n Ξ ω ∂P := by
  obtain ⟨gibbs, hgibbs, h0⟩ := exists_gibbs_zero r u lab gibbs0 hgibbs0
  have := gibbs_castSucc r ζ (fun _ => 0) nu rate 𝔡 D u lab gibbs hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs 0 Ξ
  simp only [h0] at this
  exact integral_congr_ae this

/-- A function of the overlap level is a combination of indicators of "the level exceeds `j`". -/
theorem eq_add_sum_indicator (ψ : Fin (r + 1) → ℝ) (v : Fin (r + 1)) :
    ψ v = ψ 0 + ∑ j : Fin r, (ψ j.succ - ψ j.castSucc) * if j.val < v.val then 1 else 0 := by
  induction v using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h : ∀ j : Fin r, (if j.val < (i.succ).val then (1 : ℝ) else 0) =
        (if j.val < (i.castSucc).val then 1 else 0) + if j = i then 1 else 0 := fun j => by
      by_cases hj : j = i
      · subst hj; simp
      · have : j.val ≠ i.val := fun h => hj (Fin.ext h)
        simp only [Fin.val_succ, Fin.val_castSucc, hj, ite_false, add_zero]
        by_cases hlt : j.val < i.val
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · have : ¬ j.val < i.val + 1 := by omega
          simp [hlt, this]
    simp_rw [h, mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at ih ⊢
    linarith

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- The expected Gibbs average of `g · ψ(overlap of two replicas)` through the indicators of the
events "the overlap exceeds `j`". -/
theorem integral_gibbs0_apply {m : ℕ} (g : (Fin m → Fin m → Fin (r + 1)) → ℝ) (a b : Fin m)
    (ψ : Fin (r + 1) → ℝ) :
    ∫ ω, gibbs0 m (fun P => g P * ψ (P a b)) ω ∂P =
      ψ 0 * ∫ ω, gibbs0 m g ω ∂P + ∑ j : Fin r, (ψ j.succ - ψ j.castSucc) *
        ∫ ω, gibbs0 m (fun P => g P * if j.val < (P a b).val then 1 else 0) ω ∂P := by
  classical
  obtain ⟨c, hc0, hc1⟩ : ∃ c : Option (Fin r) → ℝ, c none = ψ 0 ∧
      ∀ j, c (some j) = ψ j.succ - ψ j.castSucc :=
    ⟨fun o => Option.elim o (ψ 0) fun j => ψ j.succ - ψ j.castSucc, rfl, fun _ => rfl⟩
  obtain ⟨Ξ, hΞ0, hΞ1⟩ : ∃ Ξ : Option (Fin r) → (Fin m → Fin m → Fin (r + 1)) → ℝ,
      (∀ P, Ξ none P = g P) ∧ ∀ j P, Ξ (some j) P = g P * if j.val < (P a b).val then 1 else 0 :=
    ⟨fun o P => Option.elim o (g P) fun j => g P * if j.val < (P a b).val then 1 else 0,
      fun _ => rfl, fun _ _ => rfl⟩
  have e : (fun P => g P * ψ (P a b)) = fun P => ∑ o, c o * Ξ o P := by
    funext Pt
    rw [Fintype.sum_option, hc0, hΞ0]
    simp only [hc1, hΞ1]
    rw [eq_add_sum_indicator r ψ (Pt a b), mul_add, Finset.mul_sum, mul_comm (g Pt) (ψ 0)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hΞn : Ξ none = g := funext hΞ0
  have hΞs : ∀ j, Ξ (some j) = fun P => g P * if j.val < (P a b).val then 1 else 0 :=
    fun j => funext (hΞ1 j)
  rw [e, integral_gibbs0_sum_const_mul r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs0, Fintype.sum_option, hc0, hΞn]
  simp only [hc1, hΞs]

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- **Theorem 2.10 (Ghirlanda--Guerra identities) for the Ruelle probability cascade**, for a
nonnegative function `f` of the overlap pattern of `n` replicas and any function `ψ` of the
overlap level `0, …, r`:
`n E⟨f ψ(σ^{l₀} ∧ σ^{n+1})⟩ = E⟨f⟩ E⟨ψ(σ¹ ∧ σ²)⟩ + ∑_{l ≠ l₀} E⟨f ψ(σ^{l₀} ∧ σ^l)⟩`. -/
theorem ghirlandaGuerra_nonneg (ψ : Fin (r + 1) → ℝ) (n : ℕ)
    (f : (Fin n → Fin n → Fin (r + 1)) → ℝ) (hf : ∀ P, 0 ≤ f P) (l₀ : Fin n) :
    (n : ℝ) * ∫ ω, gibbs0 (n + 1) (fun P => f (fun l l' => P l.castSucc l'.castSucc) *
        ψ (P l₀.castSucc (Fin.last n))) ω ∂P =
      (∫ ω, gibbs0 n f ω ∂P) * ∫ ω, gibbs0 2 (fun P => ψ (P 0 1)) ω ∂P +
        ∑ l ∈ Finset.univ.erase l₀, ∫ ω, gibbs0 n (fun P => f P * ψ (P l₀ l)) ω ∂P := by
  classical
  have hn : 0 < n := Fin.pos l₀
  have hA := integral_gibbs0_apply r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab hgibbs0 (m := n + 1) (fun P => f (fun l l' => P l.castSucc l'.castSucc))
    l₀.castSucc (Fin.last n) ψ
  have hB := integral_gibbs0_apply r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab hgibbs0 (m := 2) (fun _ => 1) 0 1 ψ
  have hC := fun l : Fin n => integral_gibbs0_apply r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu
    h𝔡 hDm hD hDlaw hu hlab hgibbs0 (m := n) f l₀ l ψ
  have hcast := integral_gibbs0_castSucc r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs0 f
  have h1 := integral_gibbs0_one r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab hgibbs0 2
  have hfop := integral_gibbs0_overlap_gt r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs0
  have hGG := fun j : Fin r => ghirlandaGuerra_overlap_gt r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1
    hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 j n f hf l₀
  simp only [one_mul] at hB
  rw [hcast] at hA
  rw [h1] at hB
  simp only [hfop] at hB
  rw [hA, hB]
  simp_rw [hC]
  have hcard : ((Finset.univ.erase l₀).card : ℝ) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hn]
    simp
  set B := ∫ ω, gibbs0 n f ω ∂P with hBdef
  have hS : ∑ j : Fin r, (ψ j.succ - ψ j.castSucc) * ((n : ℝ) * ∫ ω, gibbs0 (n + 1) (fun P =>
      f (fun l l' => P l.castSucc l'.castSucc) *
        if j.val < (P l₀.castSucc (Fin.last n)).val then 1 else 0) ω ∂P) =
      ∑ j : Fin r, (ψ j.succ - ψ j.castSucc) * ((1 - ζ j) * B) +
        ∑ j : Fin r, ∑ l ∈ Finset.univ.erase l₀, (ψ j.succ - ψ j.castSucc) *
          ∫ ω, gibbs0 n (fun P => f P * if j.val < (P l₀ l).val then 1 else 0) ω ∂P := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hGG j, ← Finset.mul_sum, ← mul_add]
  rw [Finset.sum_add_distrib] at *
  simp only [mul_add, Finset.mul_sum] at hS ⊢
  rw [Finset.sum_comm] at hS
  have e1 : ∑ i : Fin r, (n : ℝ) * ((ψ i.succ - ψ i.castSucc) * ∫ ω, gibbs0 (n + 1) (fun P =>
      f (fun l l' => P l.castSucc l'.castSucc) *
        if i.val < (P l₀.castSucc (Fin.last n)).val then 1 else 0) ω ∂P) =
      ∑ j : Fin r, (ψ j.succ - ψ j.castSucc) * ((n : ℝ) * ∫ ω, gibbs0 (n + 1) (fun P =>
      f (fun l l' => P l.castSucc l'.castSucc) *
        if j.val < (P l₀.castSucc (Fin.last n)).val then 1 else 0) ω ∂P) :=
    Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ x ∈ Finset.univ.erase l₀, ψ 0 * B = ((n : ℝ) - 1) * (ψ 0 * B) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have e3 : ∑ j : Fin r, (ψ j.succ - ψ j.castSucc) * ((1 - ζ j) * B) =
      ∑ i : Fin r, B * ((ψ i.succ - ψ i.castSucc) * (1 - ζ i)) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, hS, e3]
  ring

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- The expected Gibbs average of a difference. -/
theorem integral_gibbs0_sub {m : ℕ} (g₁ g₂ : (Fin m → Fin m → Fin (r + 1)) → ℝ) :
    ∫ ω, gibbs0 m (fun P => g₁ P - g₂ P) ω ∂P =
      ∫ ω, gibbs0 m g₁ ω ∂P - ∫ ω, gibbs0 m g₂ ω ∂P := by
  have h := integral_gibbs0_sum_const_mul r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm
    hD hDlaw hu hlab hgibbs0 (Finset.univ : Finset Bool) (fun b => if b then 1 else -1)
    (fun b => if b then g₁ else g₂)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  simp only [one_mul, neg_mul] at h
  have e : (fun P => g₁ P - g₂ P) = fun P => g₁ P + -g₂ P := funext fun P => sub_eq_add_neg _ _
  rw [e]
  simpa [sub_eq_add_neg] using h

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- **Theorem 2.10 (Ghirlanda--Guerra identities) for the Ruelle probability cascade.** For every
function `f` of the overlap pattern of `n` replicas and every function `ψ` of the overlap level
`0, …, r`, with `E⟨·⟩` the expected Gibbs average of the cascade weights,
`n E⟨f ψ(σ^{l₀} ∧ σ^{n+1})⟩ = E⟨f⟩ E⟨ψ(σ¹ ∧ σ²)⟩ + ∑_{l ≠ l₀} E⟨f ψ(σ^{l₀} ∧ σ^l)⟩`. -/
theorem ghirlandaGuerra (ψ : Fin (r + 1) → ℝ) (n : ℕ)
    (f : (Fin n → Fin n → Fin (r + 1)) → ℝ) (l₀ : Fin n) :
    (n : ℝ) * ∫ ω, gibbs0 (n + 1) (fun P => f (fun l l' => P l.castSucc l'.castSucc) *
        ψ (P l₀.castSucc (Fin.last n))) ω ∂P =
      (∫ ω, gibbs0 n f ω ∂P) * ∫ ω, gibbs0 2 (fun P => ψ (P 0 1)) ω ∂P +
        ∑ l ∈ Finset.univ.erase l₀, ∫ ω, gibbs0 n (fun P => f P * ψ (P l₀ l)) ω ∂P := by
  have hp := ghirlandaGuerra_nonneg r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab hgibbs0 ψ n (fun P => max (f P) 0) (fun P => le_max_right _ _) l₀
  have hn := ghirlandaGuerra_nonneg r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab hgibbs0 ψ n (fun P => max (-f P) 0) (fun P => le_max_right _ _) l₀
  have hsplit : ∀ P, f P = max (f P) 0 - max (-f P) 0 := fun P => by
    rcases le_total 0 (f P) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  have sub : ∀ {m : ℕ} (g₁ g₂ : (Fin m → Fin m → Fin (r + 1)) → ℝ),
      ∫ ω, gibbs0 m (fun P => g₁ P - g₂ P) ω ∂P =
        ∫ ω, gibbs0 m g₁ ω ∂P - ∫ ω, gibbs0 m g₂ ω ∂P := fun {m} g₁ g₂ =>
    integral_gibbs0_sub r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab
      hgibbs0 g₁ g₂
  have e1 : (fun P : Fin (n + 1) → Fin (n + 1) → Fin (r + 1) =>
        f (fun l l' => P l.castSucc l'.castSucc) * ψ (P l₀.castSucc (Fin.last n))) =
      fun P : Fin (n + 1) → Fin (n + 1) → Fin (r + 1) =>
      max (f fun l l' => P l.castSucc l'.castSucc) 0 * ψ (P l₀.castSucc (Fin.last n)) -
        max (-f fun l l' => P l.castSucc l'.castSucc) 0 * ψ (P l₀.castSucc (Fin.last n)) :=
    funext fun P => by rw [← sub_mul, ← hsplit]
  have e2 : f = fun P => max (f P) 0 - max (-f P) 0 := funext hsplit
  have e3 : ∀ l : Fin n, (fun P => f P * ψ (P l₀ l)) = fun P =>
      max (f P) 0 * ψ (P l₀ l) - max (-f P) 0 * ψ (P l₀ l) := fun l =>
    funext fun P => by rw [← sub_mul, ← hsplit]
  have hB : ∫ ω, gibbs0 n f ω ∂P = ∫ ω, gibbs0 n (fun P => max (f P) 0) ω ∂P -
      ∫ ω, gibbs0 n (fun P => max (-f P) 0) ω ∂P := by
    have : gibbs0 n f = gibbs0 n (fun P => max (f P) 0 - max (-f P) 0) := by rw [← e2]
    rw [this]
    exact sub _ _
  have hS : ∑ l ∈ Finset.univ.erase l₀, ∫ ω, gibbs0 n (fun P => f P * ψ (P l₀ l)) ω ∂P =
      ∑ l ∈ Finset.univ.erase l₀, ∫ ω, gibbs0 n (fun P => max (f P) 0 * ψ (P l₀ l)) ω ∂P -
        ∑ l ∈ Finset.univ.erase l₀, ∫ ω, gibbs0 n (fun P => max (-f P) 0 * ψ (P l₀ l)) ω ∂P := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [e3 l]
    exact sub _ _
  rw [e1, sub _ _, hB, hS]
  linear_combination hp - hn

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- **The expected overlap law, through any function of the overlap level**:
`E⟨ψ(σ¹ ∧ σ²)⟩ = ψ(0) + ∑_{j < r} (ψ(j+1) - ψ(j)) (1 - ζ_j)`. -/
theorem integral_gibbs0_overlap_apply (ψ : Fin (r + 1) → ℝ) :
    ∫ ω, gibbs0 2 (fun P => ψ (P 0 1)) ω ∂P =
      ψ 0 + ∑ j : Fin r, (ψ j.succ - ψ j.castSucc) * (1 - ζ j) := by
  have h := integral_gibbs0_apply r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab hgibbs0 (m := 2) (fun _ => 1) 0 1 ψ
  have h1 := integral_gibbs0_one r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab hgibbs0 2
  simp only [one_mul] at h
  rw [h1] at h
  simp only [integral_gibbs0_overlap_gt r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs0, mul_one] at h
  exact h

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- **The functional order parameter.** The expected Gibbs probability that the overlap of two
replicas is exactly the level `p` is `ζ_p - ζ_{p-1}`, with the conventions `ζ_{-1} = 0` and
`ζ_r = 1`. -/
theorem integral_gibbs0_overlap_eq (p : Fin (r + 1)) :
    ∫ ω, gibbs0 2 (fun P => if P 0 1 = p then 1 else 0) ω ∂P =
      (if p.val < r then ζ p.val else 1) - (if p.val = 0 then 0 else ζ (p.val - 1)) := by
  classical
  rw [integral_gibbs0_overlap_apply r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs0 (fun v => if v = p then 1 else 0)]
  have hA : ∑ j : Fin r, ((if j.succ = p then (1 : ℝ) else 0) * (1 - ζ j)) =
      if 0 < p.val then 1 - ζ (p.val - 1) else 0 := by
    by_cases hp : 0 < p.val
    · have hpr : p.val - 1 < r := by have := p.isLt; omega
      rw [Finset.sum_eq_single ⟨p.val - 1, hpr⟩]
      · have : (⟨p.val - 1, hpr⟩ : Fin r).succ = p := Fin.ext (by simp; omega)
        simp [this, hp]
      · intro j _ hj
        have : j.succ ≠ p := fun h => hj (Fin.ext (by
          have := congrArg Fin.val h
          simp at this
          simp
          omega))
        simp [this]
      · simp
    · simp only [hp, ite_false]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : j.succ ≠ p := fun h => hp (by rw [← h]; simp)
      simp [this]
  have hB : ∑ j : Fin r, ((if j.castSucc = p then (1 : ℝ) else 0) * (1 - ζ j)) =
      if p.val < r then 1 - ζ p.val else 0 := by
    by_cases hp : p.val < r
    · rw [Finset.sum_eq_single ⟨p.val, hp⟩]
      · have : (⟨p.val, hp⟩ : Fin r).castSucc = p := Fin.ext rfl
        simp [this, hp]
      · intro j _ hj
        have : j.castSucc ≠ p := fun h => hj (Fin.ext (by
          have := congrArg Fin.val h
          simpa using this))
        simp [this]
      · simp
    · simp only [hp, ite_false]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : j.castSucc ≠ p := fun h => hp (by rw [← h]; simp)
      simp [this]
  simp only [sub_mul, Finset.sum_sub_distrib, hA, hB]
  by_cases h0 : p.val = 0
  · have hp0 : p = 0 := Fin.ext h0
    subst hp0
    by_cases hr : 0 < r
    · simp [hr]
    · have : r = 0 := by omega
      subst this
      simp
  · have hp : 0 < p.val := Nat.pos_of_ne_zero h0
    have hne : (0 : Fin (r + 1)) ≠ p := fun h => h0 (by rw [← h]; rfl)
    by_cases hpr : p.val < r
    · simp [hne, hp, hpr, h0]
    · simp [hne, hp, hpr, h0]

include hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab hgibbs0 in
/-- **The mean overlap.** For `Q m = ∑_{i < m} σᵢ²` (the overlap values of the cascade built with
the variances `σᵢ²`), `E⟨Q(σ¹ ∧ σ²)⟩ = ∑ᵢ σᵢ² (1 - ζᵢ) = Q_r - b`. -/
theorem integral_gibbs0_overlap_mean (σ : ℕ → ℝ) (Q : Fin (r + 1) → ℝ)
    (hQ : ∀ m, Q m = ∑ i : Fin r, if i.val < m.val then σ i ^ 2 else 0) :
    ∫ ω, gibbs0 2 (fun P => Q (P 0 1)) ω ∂P = ∑ j : Fin r, σ j ^ 2 * (1 - ζ j) := by
  classical
  rw [integral_gibbs0_overlap_apply r ζ nu rate 𝔡 D u lab gibbs0 hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab hgibbs0 Q]
  have h0 : Q 0 = 0 := by simp [hQ]
  have hd : ∀ j : Fin r, Q j.succ - Q j.castSucc = σ j ^ 2 := fun j => by
    simp only [hQ, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      have hij : i.val ≠ j.val := fun h => hi (Fin.ext h)
      by_cases hlt : i.val < j.val
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have : ¬ i.val < j.val + 1 := by omega
        simp [hlt, this]
    · simp
  simp [h0, hd]

end Overlap

end SpinGlasses
