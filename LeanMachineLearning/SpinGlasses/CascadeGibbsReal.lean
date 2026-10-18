/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeInvariance
public import LeanMachineLearning.SpinGlasses.GaussianIBPCountable
public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities

/-!
# Real-valued Gibbs series for the Ruelle cascade (no definitions, only lemmas)

The Gibbs average of a real observable of `K` replicas for the weights `W(α) = w(α) exp (t g(α))`
is the series `∑_σ (∏_k W(σ_k) / ∑_α W(α)) Φ(σ)`; this is the form in which countable Gaussian
integration by parts is stated. For nonnegative finite observables it is the real part of the
quotient of `[0, ∞]`-valued sums used in the Bolthausen--Sznitman invariance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

/-- **From quotients in `[0, ∞]` to real Gibbs series.** For finite weights and a finite
observable the real part of the quotient `∑_σ ∏_k w(σ_k) F(σ) / (∑ w)^{|K|}` is the series
`∑_σ ∏_k (w(σ_k) / ∑ w) F(σ)` of the real parts. -/
theorem toReal_tsum_prod_div_eq_tsum {α K : Type*} [Fintype K] (w : α → ℝ≥0∞)
    (hw : ∀ a, w a ≠ ∞) (F : (K → α) → ℝ≥0∞) (hF : ∀ σ, F σ ≠ ∞) :
    ((∑' σ : K → α, (∏ k, w (σ k)) * F σ) / (∑' a, w a) ^ Fintype.card K).toReal =
      ∑' σ : K → α, (∏ k, (w (σ k)).toReal / ∑' b, (w b).toReal) * (F σ).toReal := by
  rw [ENNReal.toReal_div, ENNReal.tsum_toReal_eq (fun σ => ENNReal.mul_ne_top
    (ENNReal.prod_ne_top fun k _ => hw _) (hF σ)), ENNReal.toReal_pow,
    ENNReal.tsum_toReal_eq hw, ← tsum_div_const]
  refine tsum_congr fun σ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ]
  ring

/-- If the quotient series in `[0, ∞]` has a finite numerator, the real series is summable. -/
theorem summable_prod_div_toReal {α K : Type*} [Fintype K] (w : α → ℝ≥0∞)
    (F : (K → α) → ℝ≥0∞)
    (hfin : ∑' σ : K → α, (∏ k, w (σ k)) * F σ ≠ ∞) :
    Summable fun σ : K → α => (∏ k, (w (σ k)).toReal / ∑' b, (w b).toReal) * (F σ).toReal := by
  have h := (ENNReal.summable_toReal hfin).div_const ((∑' b, (w b).toReal) ^ Fintype.card K)
  refine h.congr fun σ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ]
  ring

section GibbsSeries

variable {α K : Type*} [Fintype K] {W : α → ℝ}

/-- The Gibbs weights `∏_k W(σ_k) / ∑ W` of `K` replicas are a probability on `K → α`. -/
theorem hasSum_prod_div (hW : ∀ a, 0 ≤ W a) (hs : Summable W) (h0 : ∑' b, W b ≠ 0) :
    HasSum (fun σ : K → α => ∏ k, W (σ k) / ∑' b, W b) 1 := by
  have hZ : 0 < ∑' b, W b := lt_of_le_of_ne (tsum_nonneg hW) (Ne.symm h0)
  have hnn : ∀ σ : K → α, 0 ≤ ∏ k, W (σ k) / ∑' b, W b := fun σ =>
    Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le
  have hone : ∑' a, ENNReal.ofReal (W a / ∑' b, W b) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => div_nonneg (hW a) hZ.le)
      (hs.div_const _), tsum_div_const, div_self h0, ENNReal.ofReal_one]
  have hprod : ∑' σ : K → α, ENNReal.ofReal (∏ k, W (σ k) / ∑' b, W b) = 1 := by
    simp_rw [ENNReal.ofReal_prod_of_nonneg fun k _ => div_nonneg (hW _) hZ.le]
    rw [ENNReal.tsum_pi_prod fun _ a => ENNReal.ofReal (W a / ∑' b, W b)]
    simp [hone]
  have hsum : Summable fun σ : K → α => ∏ k, W (σ k) / ∑' b, W b :=
    summable_of_tsum_ofReal_lt_top hnn (by rw [hprod]; exact ENNReal.one_lt_top)
  refine hsum.hasSum_iff.2 ?_
  have h := ENNReal.ofReal_tsum_of_nonneg hnn hsum
  rw [hprod] at h
  exact ENNReal.ofReal_eq_one.1 h

/-- A bounded observable is summable against the Gibbs weights. -/
theorem summable_prod_div_mul (hW : ∀ a, 0 ≤ W a) (hs : Summable W) (h0 : ∑' b, W b ≠ 0)
    {Φ : (K → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    Summable fun σ : K → α => (∏ k, W (σ k) / ∑' b, W b) * Φ σ := by
  have hZ : 0 < ∑' b, W b := lt_of_le_of_ne (tsum_nonneg hW) (Ne.symm h0)
  refine Summable.of_norm_bounded ((hasSum_prod_div hW hs h0).summable.mul_right M) fun σ => ?_
  rw [norm_mul, Real.norm_of_nonneg (Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le)]
  exact mul_le_mul_of_nonneg_left (hΦ σ) (Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le)

/-- The Gibbs series of a bounded observable is bounded by the same constant. -/
theorem abs_tsum_prod_div_mul_le (hW : ∀ a, 0 ≤ W a) (hs : Summable W) (h0 : ∑' b, W b ≠ 0)
    {Φ : (K → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    |∑' σ : K → α, (∏ k, W (σ k) / ∑' b, W b) * Φ σ| ≤ M := by
  have hZ : 0 < ∑' b, W b := lt_of_le_of_ne (tsum_nonneg hW) (Ne.symm h0)
  have hnn : ∀ σ : K → α, 0 ≤ ∏ k, W (σ k) / ∑' b, W b := fun σ =>
    Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le
  have h1 := (hasSum_prod_div (K := K) hW hs h0)
  calc |∑' σ : K → α, (∏ k, W (σ k) / ∑' b, W b) * Φ σ|
      ≤ ∑' σ : K → α, ‖(∏ k, W (σ k) / ∑' b, W b) * Φ σ‖ :=
        norm_tsum_le_tsum_norm (summable_prod_div_mul hW hs h0 hΦ).norm
    _ ≤ ∑' σ : K → α, (∏ k, W (σ k) / ∑' b, W b) * M := by
        refine Summable.tsum_le_tsum (fun σ => ?_) (summable_prod_div_mul hW hs h0 hΦ).norm
          (h1.summable.mul_right M)
        rw [norm_mul, Real.norm_of_nonneg (hnn σ)]
        exact mul_le_mul_of_nonneg_left (hΦ σ) (hnn σ)
    _ = M := by rw [tsum_mul_right, h1.tsum_eq, one_mul]

/-- **Marginalizing the last replica.** The Gibbs series of an observable of the first `n`
replicas does not change when a further replica is added. -/
theorem tsum_prod_div_mul_castSucc {n : ℕ} (hW : ∀ a, 0 ≤ W a) (hs : Summable W)
    (h0 : ∑' b, W b ≠ 0) {Φ : (Fin n → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    ∑' τ : Fin (n + 1) → α, (∏ k, W (τ k) / ∑' b, W b) * Φ (fun k => τ k.castSucc) =
      ∑' σ : Fin n → α, (∏ k, W (σ k) / ∑' b, W b) * Φ σ := by
  rw [← (Fin.snocEquiv fun _ : Fin (n + 1) => α).tsum_eq]
  have e : ∀ x : α × (Fin n → α),
      (∏ k, W (Fin.snocEquiv (fun _ : Fin (n + 1) => α) x k) / ∑' b, W b) *
        Φ (fun k => Fin.snocEquiv (fun _ : Fin (n + 1) => α) x k.castSucc) =
      (W x.1 / ∑' b, W b) * ((∏ k, W (x.2 k) / ∑' b, W b) * Φ x.2) := by
    intro x
    rw [Fin.prod_univ_castSucc]
    simp [Fin.snocEquiv, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  simp_rw [e]
  have hg := summable_prod_div_mul (K := Fin n) hW hs h0 hΦ
  have hf : Summable fun a => W a / ∑' b, W b := hs.div_const _
  rw [← tsum_mul_tsum_of_summable_norm (hf.norm) (hg.norm), tsum_div_const, div_self h0,
    one_mul]

/-- A Gibbs series of measurable weights and measurable observables is a measurable function of
the parameter. -/
theorem measurable_tsum_prod_div_mul {X : Type*} [MeasurableSpace X] [Countable α]
    (W : X → α → ℝ) (hW : ∀ a, Measurable fun x => W x a) (Ψ : (K → α) → X → ℝ)
    (hΨ : ∀ τ, Measurable (Ψ τ)) :
    Measurable fun x => ∑' τ : K → α, (∏ k, W x (τ k) / ∑' c, W x c) * Ψ τ x := by
  have hZ : Measurable fun x => ∑' c, W x c := Measurable.tsum hW
  exact Measurable.tsum fun τ => (Finset.measurable_prod _ fun k _ => (hW (τ k)).div hZ).mul
    (hΨ τ)

end GibbsSeries

section Cascade

variable (r n : ℕ) (σ : ℕ → ℝ) (t : ℝ) (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
  (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)

/-- **The Gibbs average of the cascade as a real series.** If the branch weights are finite and
the observable is finite, the real part of `⟨F(Rⁿ)⟩_t` is the Gibbs series of the real weights
`w_α exp (t g(α))`. -/
theorem toReal_replicaGibbs_eq_tsum (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞)
    (hu : ∀ α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞) (hF : ∀ P, F P ≠ ∞) :
    (replicaGibbs r n σ t F u lab).toReal =
      ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        (F fun l l' => prefixOverlap (τ l) (τ l')).toReal := by
  have h := toReal_tsum_prod_div_eq_tsum (K := Fin n)
    (fun α : Fin r → ℕ => cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)))
    (fun α => ENNReal.mul_ne_top (hu α) ENNReal.ofReal_ne_top)
    (fun τ => F fun l l' => prefixOverlap (τ l) (τ l')) (fun τ => hF _)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  rw [Fintype.card_fin] at h
  exact h

/-- The Gibbs average with a test of one label, as a real series. -/
theorem toReal_replicaGibbsAt_eq_tsum (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) (l₀ : Fin n)
    (i₀ : Fin r) (ψ : ℝ → ℝ≥0∞) (s : ℝ) (hu : ∀ α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞)
    (hF : ∀ P, F P ≠ ∞) (hψ : ∀ y, ψ y ≠ ∞) :
    (replicaGibbsAt r n σ t F l₀ i₀ ψ s u lab).toReal =
      ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (ψ (leafLabel lab (τ l₀) i₀ - s)).toReal) := by
  have h := toReal_tsum_prod_div_eq_tsum (K := Fin n)
    (fun α : Fin r → ℕ => cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)))
    (fun α => ENNReal.mul_ne_top (hu α) ENNReal.ofReal_ne_top)
    (fun τ => (F fun l l' => prefixOverlap (τ l) (τ l')) *
      ψ (leafLabel lab (τ l₀) i₀ - s)) (fun τ => ENNReal.mul_ne_top (hF _) (hψ _))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  rw [Fintype.card_fin] at h
  unfold replicaGibbsAt
  simp_rw [mul_assoc] at h ⊢
  exact h

/-- The real weights of a cascade with finite branch weights and positive finite total mass are
nonnegative, summable, with a nonzero sum. -/
theorem summable_tsum_ne_zero_cascadeWeight (hu : ∀ α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞)
    (h0 : ∑' α : Fin r → ℕ, cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) ≠ 0)
    (ht : ∑' α : Fin r → ℕ, cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) ≠ ∞) :
    Summable (fun α : Fin r → ℕ => (cascadeBranchWeight u α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) ∧
    ∑' α : Fin r → ℕ, (cascadeBranchWeight u α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i) ≠ 0 := by
  have e : ∀ α : Fin r → ℕ, (cascadeBranchWeight u α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i) = (cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i))).toReal := fun α => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp_rw [e]
  refine ⟨ENNReal.summable_toReal ht, ?_⟩
  rw [← ENNReal.tsum_toReal_eq (f := fun α => cascadeBranchWeight u α *
    ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)))
    fun α => ENNReal.mul_ne_top (hu α) ENNReal.ofReal_ne_top]
  exact (ENNReal.toReal_pos h0 ht).ne'

/-- **The Gibbs series of a bounded real pattern observable** is the difference of the real parts
of the Gibbs averages of its positive and negative parts. -/
theorem tsum_cascadeSeries_eq_toReal_sub (Ξ : (Fin n → Fin n → Fin (r + 1)) → ℝ) {M : ℝ}
    (hΞ : ∀ P, |Ξ P| ≤ M) (hu : ∀ α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞)
    (h0 : ∑' α : Fin r → ℕ, cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) ≠ 0)
    (ht : ∑' α : Fin r → ℕ, cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) ≠ ∞) :
    ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l')) =
      (replicaGibbs r n σ t (fun P => ENNReal.ofReal (Ξ P)) u lab).toReal -
        (replicaGibbs r n σ t (fun P => ENNReal.ofReal (-Ξ P)) u lab).toReal := by
  obtain ⟨hs, hne⟩ := summable_tsum_ne_zero_cascadeWeight r σ t u lab hu h0 ht
  have hW : ∀ α : Fin r → ℕ, 0 ≤ (cascadeBranchWeight u α).toReal *
      Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i) := fun α =>
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  rw [toReal_replicaGibbs_eq_tsum r n σ t u lab _ hu fun P => ENNReal.ofReal_ne_top,
    toReal_replicaGibbs_eq_tsum r n σ t u lab _ hu fun P => ENNReal.ofReal_ne_top,
    ← Summable.tsum_sub]
  · refine tsum_congr fun τ => ?_
    rw [← mul_sub, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    congr 1
    rcases le_total 0 (Ξ fun l l' => prefixOverlap (τ l) (τ l')) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  · refine summable_prod_div_mul hW hs hne (Φ := fun τ => (ENNReal.ofReal
      (Ξ fun l l' => prefixOverlap (τ l) (τ l'))).toReal) (M := M) fun τ => ?_
    rw [ENNReal.toReal_ofReal', abs_of_nonneg (le_max_right _ _)]
    have hb := hΞ fun l l' => prefixOverlap (τ l) (τ l')
    exact max_le ((le_abs_self _).trans hb) ((abs_nonneg _).trans hb)
  · refine summable_prod_div_mul hW hs hne (Φ := fun τ => (ENNReal.ofReal
      (-Ξ fun l l' => prefixOverlap (τ l) (τ l'))).toReal) (M := M) fun τ => ?_
    rw [ENNReal.toReal_ofReal', abs_of_nonneg (le_max_right _ _)]
    have hb := hΞ fun l l' => prefixOverlap (τ l) (τ l')
    exact max_le ((neg_le_abs _).trans hb) ((abs_nonneg _).trans hb)

/-- If the Gibbs average with a test of one label is finite, the corresponding real series is
summable. -/
theorem summable_replicaGibbsAt_series (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) (l₀ : Fin n)
    (i₀ : Fin r) (ψ : ℝ → ℝ≥0∞) (s : ℝ)
    (ht : ∑' α : Fin r → ℕ, cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) ≠ ∞)
    (hA : replicaGibbsAt r n σ t F l₀ i₀ ψ s u lab ≠ ∞) :
    Summable fun τ : Fin n → Fin r → ℕ => (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (ψ (leafLabel lab (τ l₀) i₀ - s)).toReal) := by
  have hfin : ∑' τ : Fin n → Fin r → ℕ, (∏ l, cascadeBranchWeight u (τ l) *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i))) *
      ((F fun l l' => prefixOverlap (τ l) (τ l')) * ψ (leafLabel lab (τ l₀) i₀ - s)) ≠ ∞ := by
    intro h
    apply hA
    unfold replicaGibbsAt
    simp_rw [mul_assoc]
    rw [h]
    exact ENNReal.top_div_of_ne_top (ENNReal.pow_ne_top ht)
  have h := summable_prod_div_toReal (K := Fin n)
    (fun α : Fin r → ℕ => cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)))
    (fun τ => (F fun l l' => prefixOverlap (τ l) (τ l')) * ψ (leafLabel lab (τ l₀) i₀ - s))
    hfin
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

/-- The positive and negative parts of a real number, as real numbers, recover it. -/
theorem toReal_ofReal_sub_toReal_ofReal_neg (x : ℝ) :
    (ENNReal.ofReal x).toReal - (ENNReal.ofReal (-x)).toReal = x := by
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring

/-- **The Gibbs series of an observable times the centred field, through the Gibbs averages with a
test of one label.** If the Gibbs averages `⟨F (±σᵢ(labelᵢ - tσᵢζᵢ))^+⟩_t` of the replica `l₀` are
finite for every level `i`, the Gibbs series of `F (g(α^{l₀}) - t ∑ᵢ σᵢ² ζᵢ)` is the sum over the
levels of their real differences. -/
theorem tsum_cascadeSeries_energy_eq (ζ : ℕ → ℝ) (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞)
    (hF : ∀ P, F P ≠ ∞) (l₀ : Fin n) (hu : ∀ α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞)
    (ht : ∑' α : Fin r → ℕ, cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) ≠ ∞)
    (hA : ∀ i : Fin r, replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (σ i * y))
        (t * σ i * ζ i) u lab ≠ ∞ ∧
      replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (-(σ i * y)))
        (t * σ i * ζ i) u lab ≠ ∞) :
    Summable (fun τ : Fin n → Fin r → ℕ => (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel lab (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i))) ∧
    ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel lab (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i)) =
      ∑ i : Fin r, ((replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (σ i * y))
        (t * σ i * ζ i) u lab).toReal - (replicaGibbsAt r n σ t F l₀ i
          (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i) u lab).toReal) := by
  have e1 := fun i : Fin r => toReal_replicaGibbsAt_eq_tsum r n σ t u lab F l₀ i
    (fun y => ENNReal.ofReal (σ i * y)) (t * σ i * ζ i) hu hF fun _ => ENNReal.ofReal_ne_top
  have e2 := fun i : Fin r => toReal_replicaGibbsAt_eq_tsum r n σ t u lab F l₀ i
    (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i) hu hF fun _ => ENNReal.ofReal_ne_top
  have s1 := fun i : Fin r => summable_replicaGibbsAt_series r n σ t u lab F l₀ i
    (fun y => ENNReal.ofReal (σ i * y)) (t * σ i * ζ i) ht (hA i).1
  have s2 := fun i : Fin r => summable_replicaGibbsAt_series r n σ t u lab F l₀ i
    (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i) ht (hA i).2
  simp_rw [e1, e2]
  have hterm : ∀ τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel lab (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i)) =
      ∑ i : Fin r, ((∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (ENNReal.ofReal (σ i * (leafLabel lab (τ l₀) i - t * σ i * ζ i))).toReal) -
        (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (ENNReal.ofReal (-(σ i * (leafLabel lab (τ l₀) i - t * σ i * ζ i)))).toReal)) := by
    intro τ
    simp_rw [← mul_sub]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simp_rw [toReal_ofReal_sub_toReal_ofReal_neg]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsum : Summable (fun τ : Fin n → Fin r → ℕ => ∑ i : Fin r,
      ((∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (ENNReal.ofReal (σ i * (leafLabel lab (τ l₀) i - t * σ i * ζ i))).toReal) -
        (∏ l, (cascadeBranchWeight u (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight u b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (ENNReal.ofReal (-(σ i * (leafLabel lab (τ l₀) i - t * σ i * ζ i)))).toReal))) :=
    summable_sum fun i _ => (s1 i).sub (s2 i)
  refine ⟨hsum.congr fun τ => (hterm τ).symm, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => (Summable.tsum_sub (s1 i) (s2 i)).symm,
    ← Summable.tsum_finsetSum fun i _ => (s1 i).sub (s2 i)]
  exact tsum_congr hterm

end Cascade

end SpinGlasses
