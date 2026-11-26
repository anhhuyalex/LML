/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector

/-!
# Gaussian integration by parts for a ratio with a normalizer

Talagrand's cavity computation (Section 2.3, the "term created by the denominator") integrates by
parts a quantity `F(X) / Z(Y)^n`, where the numerator `F` depends on one Gaussian family `X` and
the normalizer `Z` on another family `Y` (`Z` is positive and bounded below). With `W` a centered
Gaussian variable jointly Gaussian with `(X, Y)`,

`𝔼[W F(X) / Z(Y)^n] = ∑ₗ 𝔼[W Xₗ] 𝔼[∂ₗF(X) / Z(Y)^n]
  - n ∑ₘ 𝔼[W Yₘ] 𝔼[F(X) ∂ₘZ(Y) / Z(Y)^{n+1}]`.

All of these are instances of the integration by parts of `F(X) H(Z(Y))`.

* `integral_smul_comp_smul_eq_integral_fderiv`: `F(X) H(Z(Y))` for vector-valued `X`, `Y`, `F`.
* `integral_mul_mul_comp_eq_sum`: its coordinate form.
* `integral_mul_div_pow_eq_sum`: `H(t) = t⁻ⁿ`.
* `integral_mul_div_pow_mul_comp_log_eq_sum`, `integral_mul_div_mul_comp_log_eq_sum`:
  `H(t) = t⁻ⁿ G(log t)` when `Z ∈ [z₀, z₁]` (`z₀ > 0`).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- **Gaussian integration by parts for `F(X) H(Z(Y))`**, vector-valued. Let `(W, X, Y)` be a
centered Gaussian vector, `F` differentiable with exponential growth, `Z` a differentiable function
with values in `s` and derivative of exponential growth, and `H` differentiable on `s` with `H` and
`H'` bounded on `s`. Then
`𝔼[W H(Z(Y)) F(X)] = 𝔼[H(Z(Y)) DF(X)(𝔼[W X])] + 𝔼[H'(Z(Y)) DZ(Y)(𝔼[W Y]) F(X)]`. -/
theorem integral_smul_comp_smul_eq_integral_fderiv {Ω E E' V : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {W : Ω → ℝ} {X : Ω → E} {Y : Ω → E'}
    (hWXY : HasGaussianLaw (fun ω => (W ω, X ω, Y ω)) P) (hW : ∫ ω, W ω ∂P = 0)
    (hX : ∫ ω, X ω ∂P = 0) (hY : ∫ ω, Y ω ∂P = 0)
    {F : E → V} (hF : Differentiable ℝ F) {C c D d : ℝ}
    (hFg : ∀ x, ‖F x‖ ≤ C * Real.exp (c * ‖x‖))
    (hFg' : ∀ x, ‖fderiv ℝ F x‖ ≤ D * Real.exp (d * ‖x‖))
    {Z : E' → ℝ} (hZ : Differentiable ℝ Z) {DZ dZ : ℝ}
    (hZg : ∀ y, ‖fderiv ℝ Z y‖ ≤ DZ * Real.exp (dZ * ‖y‖))
    {s : Set ℝ} (hZs : ∀ y, Z y ∈ s) {H H' : ℝ → ℝ} (hH : ∀ t ∈ s, HasDerivAt H (H' t) t)
    {M M' : ℝ} (hHb : ∀ t ∈ s, |H t| ≤ M) (hH'b : ∀ t ∈ s, |H' t| ≤ M') :
    ∫ ω, W ω • (H (Z (Y ω)) • F (X ω)) ∂P =
      (∫ ω, H (Z (Y ω)) • fderiv ℝ F (X ω) (∫ ω', W ω' • X ω' ∂P) ∂P) +
        ∫ ω, (H' (Z (Y ω)) * fderiv ℝ Z (Y ω) (∫ ω', W ω' • Y ω' ∂P)) • F (X ω) ∂P := by
  have hP := hWXY.isProbabilityMeasure
  have hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P := hWXY.snd
  have hXG : HasGaussianLaw X P := hXY.fst
  have hYG : HasGaussianLaw Y P := hXY.snd
  have hWG : HasGaussianLaw W P := hWXY.fst
  set Φ : E × E' → V := fun p => H (Z p.2) • F p.1 with hΦ
  have hHZ : ∀ y, HasFDerivAt (fun y => H (Z y)) (H' (Z y) • fderiv ℝ Z y) y := fun y =>
    (hH _ (hZs y)).comp_hasFDerivAt y (hZ y).hasFDerivAt
  have hΦ' : ∀ p : E × E', HasFDerivAt Φ
      (H (Z p.2) • (fderiv ℝ F p.1).comp (ContinuousLinearMap.fst ℝ E E') +
        ((H' (Z p.2) • fderiv ℝ Z p.2).comp (ContinuousLinearMap.snd ℝ E E')).smulRight
          (F p.1)) p := fun p =>
    ((hHZ p.2).comp p hasFDerivAt_snd).smul ((hF p.1).hasFDerivAt.comp p hasFDerivAt_fst)
  have hΦd : Differentiable ℝ Φ := fun p => (hΦ' p).differentiableAt
  have hΦv : ∀ p v : E × E', fderiv ℝ Φ p v =
      H (Z p.2) • fderiv ℝ F p.1 v.1 + (H' (Z p.2) * fderiv ℝ Z p.2 v.2) • F p.1 := fun p v => by
    rw [(hΦ' p).fderiv]
    simp
  have hM : 0 ≤ M := (abs_nonneg _).trans (hHb _ (hZs 0))
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hH'b _ (hZs 0))
  have hmono : ∀ (K r t R : ℝ), 0 ≤ t → t ≤ R →
      K * Real.exp (r * t) ≤ |K| * Real.exp (|r| * R) := fun K r t R ht htR =>
    mul_le_mul (le_abs_self K) (Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right (le_abs_self r)
      ht).trans (mul_le_mul_of_nonneg_left htR (abs_nonneg r)))) (Real.exp_pos _).le
      (abs_nonneg K)
  have hΦg : ∀ p : E × E', ‖Φ p‖ ≤ M * |C| * Real.exp (|c| * ‖p‖) := fun p => by
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul (hHb _ (hZs _)) ((hFg _).trans (hmono C c _ _ (norm_nonneg _)
      (norm_fst_le p))) (norm_nonneg _) hM
  have hΦg' : ∀ p : E × E', ‖fderiv ℝ Φ p‖ ≤ (M * |D| + M' * |DZ| * |C|) *
      Real.exp ((|d| + |dZ| + |c|) * ‖p‖) := fun p => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hle : ∀ a : ℝ, 0 ≤ a → a ≤ |d| + |dZ| + |c| →
        Real.exp (a * ‖p‖) ≤ Real.exp ((|d| + |dZ| + |c|) * ‖p‖) := fun a _ h =>
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    have h1 : ‖H (Z p.2) • fderiv ℝ F p.1 v.1‖ ≤
        M * |D| * Real.exp ((|d| + |dZ| + |c|) * ‖p‖) * ‖v‖ := by
      have hD : ‖fderiv ℝ F p.1‖ ≤ |D| * Real.exp ((|d| + |dZ| + |c|) * ‖p‖) :=
        (hFg' _).trans ((hmono D d _ _ (norm_nonneg _) (norm_fst_le p)).trans
          (mul_le_mul_of_nonneg_left (hle _ (abs_nonneg _) (by
            linarith [abs_nonneg dZ, abs_nonneg c])) (abs_nonneg _)))
      rw [norm_smul, Real.norm_eq_abs]
      refine (mul_le_mul (hHb _ (hZs _)) (((fderiv ℝ F p.1).le_opNorm v.1).trans
        (mul_le_mul hD (norm_fst_le v) (norm_nonneg _) (by positivity)))
        (norm_nonneg _) hM).trans_eq ?_
      ring
    have h2 : ‖(H' (Z p.2) * fderiv ℝ Z p.2 v.2) • F p.1‖ ≤
        M' * |DZ| * |C| * Real.exp ((|d| + |dZ| + |c|) * ‖p‖) * ‖v‖ := by
      have hDZ : ‖fderiv ℝ Z p.2‖ ≤ |DZ| * Real.exp (|dZ| * ‖p‖) :=
        (hZg _).trans (hmono DZ dZ _ _ (norm_nonneg _) (norm_snd_le p))
      have hC : ‖F p.1‖ ≤ |C| * Real.exp (|c| * ‖p‖) :=
        (hFg _).trans (hmono C c _ _ (norm_nonneg _) (norm_fst_le p))
      rw [norm_smul, norm_mul, Real.norm_eq_abs]
      refine (mul_le_mul (mul_le_mul (hH'b _ (hZs _)) (((fderiv ℝ Z p.2).le_opNorm v.2).trans
        (mul_le_mul hDZ (norm_snd_le v) (norm_nonneg _) (by positivity)))
        (norm_nonneg _) hM') hC (norm_nonneg _) (by positivity)).trans ?_
      have he : Real.exp (|dZ| * ‖p‖) * Real.exp (|c| * ‖p‖) ≤
          Real.exp ((|d| + |dZ| + |c|) * ‖p‖) := by
        rw [← Real.exp_add, ← add_mul]
        exact hle _ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by linarith [abs_nonneg d])
      calc M' * (|DZ| * Real.exp (|dZ| * ‖p‖) * ‖v‖) * (|C| * Real.exp (|c| * ‖p‖))
          = M' * |DZ| * |C| * (Real.exp (|dZ| * ‖p‖) * Real.exp (|c| * ‖p‖)) * ‖v‖ := by ring
        _ ≤ M' * |DZ| * |C| * Real.exp ((|d| + |dZ| + |c|) * ‖p‖) * ‖v‖ := by gcongr
    rw [hΦv]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    ring
  have hXi : Integrable X P := hXG.integrable
  have hYi : Integrable Y P := hYG.integrable
  have hmean : ∫ ω, (X ω, Y ω) ∂P = 0 := by
    rw [integral_pair hXi hYi, hX, hY]
    rfl
  have hWX : Integrable (fun ω => W ω • X ω) P :=
    memLp_one_iff_integrable.1 (hWG.memLp_two.smul hXG.memLp_two)
  have hWY : Integrable (fun ω => W ω • Y ω) P :=
    memLp_one_iff_integrable.1 (hWG.memLp_two.smul hYG.memLp_two)
  have hcov : ∫ ω, W ω • (X ω, Y ω) ∂P = (∫ ω, W ω • X ω ∂P, ∫ ω, W ω • Y ω ∂P) :=
    integral_pair hWX hWY
  have h := integral_smul_comp_eq_integral_fderiv_apply (X := fun ω => (X ω, Y ω)) hWXY hW hmean
    hΦd hΦg hΦg'
  rw [hcov] at h
  set a := ∫ ω, W ω • X ω ∂P
  set b := ∫ ω, W ω • Y ω ∂P
  have hI : ∀ v : E × E', Integrable (fun ω => fderiv ℝ Φ (X ω, Y ω) v) P := fun v => by
    refine ((hXY.integrable_exp_mul_norm (|d| + |dZ| + |c|)).const_mul
      ((M * |D| + M' * |DZ| * |C|) * ‖v‖)).mono'
      ((stronglyMeasurable_fderiv_apply_of_differentiable hΦd v).aestronglyMeasurable
        |>.comp_aemeasurable hXY.aemeasurable) (ae_of_all _ fun ω => ?_)
    refine ((fderiv ℝ Φ (X ω, Y ω)).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_right (hΦg' _) (norm_nonneg v)).trans_eq ?_)
    ring
  have h1 : ∀ ω, H (Z (Y ω)) • fderiv ℝ F (X ω) a = fderiv ℝ Φ (X ω, Y ω) (a, 0) := fun ω => by
    simp [hΦv]
  have h2 : ∀ ω, (H' (Z (Y ω)) * fderiv ℝ Z (Y ω) b) • F (X ω) =
      fderiv ℝ Φ (X ω, Y ω) (0, b) := fun ω => by
    simp [hΦv]
  simp only [h1, h2]
  rw [← integral_add (hI _) (hI _)]
  refine h.trans (integral_congr_ae (ae_of_all _ fun ω => ?_))
  simp only [← map_add, Prod.mk_add_mk, add_zero, zero_add]

variable {Ω κ₁ κ₂ κ₃ : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [Finite κ₁] [Fintype κ₂] [Fintype κ₃] [DecidableEq κ₂] [DecidableEq κ₃]

/-- **Gaussian integration by parts for `F(X) H(Z(Y))`**, coordinate form. With `(W, X, Y)` a
Gaussian family in which `W i`, `X` and `Y` are centered,
`𝔼[W i F(X) H(Z(Y))] = ∑ₗ 𝔼[W i Xₗ] 𝔼[∂ₗF(X) H(Z(Y))]
  + ∑ₘ 𝔼[W i Yₘ] 𝔼[F(X) ∂ₘZ(Y) H'(Z(Y))]`. -/
theorem integral_mul_mul_comp_eq_sum {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ} {Y : κ₃ → Ω → ℝ}
    (hWXY : HasGaussianLaw (fun ω s => Sum.elim W (Sum.elim X Y) s ω) P) {i : κ₁}
    (hW : ∫ ω, W i ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ m, ∫ ω, Y m ω ∂P = 0)
    {F : (κ₂ → ℝ) → ℝ} (hF : Differentiable ℝ F) {C c : ℝ}
    (hFg : ∀ x, |F x| ≤ C * Real.exp (c * ∑ l, |x l|)) {D d : κ₂ → ℝ}
    (hFg' : ∀ l x, |fderiv ℝ F x (Pi.single l 1)| ≤ D l * Real.exp (d l * ∑ l, |x l|))
    {Z : (κ₃ → ℝ) → ℝ} (hZ : Differentiable ℝ Z) {DZ dZ : κ₃ → ℝ}
    (hZg : ∀ m y, |fderiv ℝ Z y (Pi.single m 1)| ≤ DZ m * Real.exp (dZ m * ∑ m, |y m|))
    {s : Set ℝ} (hZs : ∀ y, Z y ∈ s) {H H' : ℝ → ℝ} (hH : ∀ t ∈ s, HasDerivAt H (H' t) t)
    {M M' : ℝ} (hHb : ∀ t ∈ s, |H t| ≤ M) (hH'b : ∀ t ∈ s, |H' t| ≤ M') :
    ∫ ω, W i ω * (F (fun l => X l ω) * H (Z fun m => Y m ω)) ∂P =
      (∑ l, (∫ ω, W i ω * X l ω ∂P) *
        ∫ ω, fderiv ℝ F (fun k => X k ω) (Pi.single l 1) * H (Z fun m => Y m ω) ∂P) +
      ∑ m, (∫ ω, W i ω * Y m ω ∂P) *
        ∫ ω, F (fun l => X l ω) * fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) *
          H' (Z fun k => Y k ω) ∂P := by
  have := Fintype.ofFinite κ₁
  have hP := hWXY.isProbabilityMeasure
  set R : (κ₁ ⊕ κ₂ ⊕ κ₃ → ℝ) →L[ℝ] ℝ × (κ₂ → ℝ) × (κ₃ → ℝ) :=
    (ContinuousLinearMap.proj (Sum.inl i)).prod
      ((ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr (Sum.inl l))).prod
        (ContinuousLinearMap.pi fun m => ContinuousLinearMap.proj (Sum.inr (Sum.inr m)))) with hR
  have htrip : HasGaussianLaw (fun ω => (W i ω, (fun l => X l ω), fun m => Y m ω)) P :=
    hWXY.map_fun R
  have hXYG : HasGaussianLaw (fun ω => ((fun l => X l ω), fun m => Y m ω)) P := htrip.snd
  have hXG : HasGaussianLaw (fun ω l => X l ω) P := hXYG.fst
  have hYG : HasGaussianLaw (fun ω m => Y m ω) P := hXYG.snd
  have hXmean : ∫ ω, (fun l => X l ω) ∂P = 0 := by
    funext l
    rw [eval_integral fun l => (hXG.eval l).integrable]
    exact hX l
  have hYmean : ∫ ω, (fun m => Y m ω) ∂P = 0 := by
    funext m
    rw [eval_integral fun m => (hYG.eval m).integrable]
    exact hY m
  have h := integral_smul_comp_smul_eq_integral_fderiv htrip hW hXmean hYmean hF
    (fun x => (hFg x).trans (mul_exp_mul_sum_abs_le_mul_exp_norm C c x))
    (norm_fderiv_le_of_abs_fderiv_pi_single_le hFg') hZ
    (norm_fderiv_le_of_abs_fderiv_pi_single_le hZg) hZs hH hHb hH'b
  have hcovX : ∀ l, (∫ ω, W i ω • (fun l => X l ω) ∂P) l = ∫ ω, W i ω * X l ω ∂P :=
    integral_smul_pi_apply_eq_integral_mul htrip.fst.memLp_two hXG.memLp_two
  have hcovY : ∀ m, (∫ ω, W i ω • (fun m => Y m ω) ∂P) m = ∫ ω, W i ω * Y m ω ∂P :=
    integral_smul_pi_apply_eq_integral_mul htrip.fst.memLp_two hYG.memLp_two
  have hHZ : ∀ y, HasFDerivAt (fun y => H (Z y)) (H' (Z y) • fderiv ℝ Z y) y := fun y =>
    (hH _ (hZs y)).comp_hasFDerivAt y (hZ y).hasFDerivAt
  have hHZc : Continuous fun y => H (Z y) :=
    continuous_iff_continuousAt.2 fun y => (hHZ y).continuousAt
  have hHZm : AEStronglyMeasurable (fun ω => H (Z fun m => Y m ω)) P :=
    hHZc.comp_aestronglyMeasurable hYG.aemeasurable.aestronglyMeasurable
  have hi1 : ∀ l, Integrable (fun ω =>
      fderiv ℝ F (fun k => X k ω) (Pi.single l 1) * H (Z fun m => Y m ω)) P := fun l =>
    (integrable_comp_of_exp_growth hXG hX (measurable_fderiv_apply_const ℝ F _)
      (hFg' l)).mul_bdd (c := M) hHZm (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hHb _ (hZs _))
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hH'b _ (hZs 0))
  have hi2 : ∀ m, Integrable (fun ω => F (fun l => X l ω) *
      fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) * H' (Z fun k => Y k ω)) P := fun m => by
    set rX : ℝ := |c| * Fintype.card κ₂ with hrX
    set rY : ℝ := |dZ m| * Fintype.card κ₃ with hrY
    have hm : AEStronglyMeasurable (fun ω => F (fun l => X l ω) *
        fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) * H' (Z fun k => Y k ω)) P := by
      have h2 : StronglyMeasurable fun y => fderiv ℝ (fun y => H (Z y)) y (Pi.single m 1) :=
        stronglyMeasurable_fderiv_apply_of_differentiable (fun y => (hHZ y).differentiableAt) _
      refine ((hF.continuous.comp_aestronglyMeasurable
        hXG.aemeasurable.aestronglyMeasurable).mul (h2.aestronglyMeasurable.comp_aemeasurable
          hYG.aemeasurable)).congr (ae_of_all _ fun ω => ?_)
      simp only [Pi.mul_apply, Function.comp_apply, (hHZ _).fderiv, smul_apply, smul_eq_mul]
      ring
    refine ((hXYG.integrable_exp_mul_norm (rX + rY)).const_mul
      (|C| * |DZ m| * M')).mono' hm (ae_of_all _ fun ω => ?_)
    have hx : |F fun l => X l ω| ≤
        |C| * Real.exp (rX * ‖((fun l => X l ω), fun m => Y m ω)‖) :=
      ((hFg _).trans (mul_exp_mul_sum_abs_le_mul_exp_norm C c _)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
          (norm_fst_le ((fun l => X l ω), fun m => Y m ω)) (by positivity))) (abs_nonneg _))
    have hy : |fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1)| ≤
        |DZ m| * Real.exp (rY * ‖((fun l => X l ω), fun m => Y m ω)‖) :=
      ((hZg m _).trans (mul_exp_mul_sum_abs_le_mul_exp_norm (DZ m) (dZ m) _)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
          (norm_snd_le ((fun l => X l ω), fun m => Y m ω)) (by positivity))) (abs_nonneg _))
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    refine (mul_le_mul (mul_le_mul hx hy (abs_nonneg _) (by positivity)) (hH'b _ (hZs _))
      (abs_nonneg _) (by positivity)).trans_eq ?_
    rw [add_mul, Real.exp_add]
    ring
  have e1 : ∀ ω, H (Z fun m => Y m ω) • fderiv ℝ F (fun k => X k ω)
        (∫ ω, W i ω • (fun l => X l ω) ∂P) =
      ∑ l, (∫ ω, W i ω * X l ω ∂P) *
        (fderiv ℝ F (fun k => X k ω) (Pi.single l 1) * H (Z fun m => Y m ω)) := fun ω => by
    rw [apply_eq_sum_smul_apply_pi_single (fderiv ℝ F _), smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hcovX l, smul_eq_mul]
    ring
  have e2 : ∀ ω, (H' (Z fun m => Y m ω) * fderiv ℝ Z (fun k => Y k ω)
        (∫ ω, W i ω • (fun m => Y m ω) ∂P)) • F (fun l => X l ω) =
      ∑ m, (∫ ω, W i ω * Y m ω ∂P) * (F (fun l => X l ω) *
        fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) * H' (Z fun k => Y k ω)) := fun ω => by
    rw [apply_eq_sum_smul_apply_pi_single (fderiv ℝ Z _), smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcovY m, smul_eq_mul]
    ring
  simp only [e1, e2] at h
  rw [integral_finsetSum _ fun l _ => (hi1 l).const_mul _,
    integral_finsetSum _ fun m _ => (hi2 m).const_mul _] at h
  simp only [integral_const_mul, smul_eq_mul] at h
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun ω => ?_)) h
  ring

/-- The derivative of `t ↦ (t ^ n)⁻¹` away from zero. -/
theorem hasDerivAt_inv_pow {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    HasDerivAt (fun t : ℝ => (t ^ n)⁻¹) (-(n * (t ^ (n + 1))⁻¹)) t := by
  refine ((hasDerivAt_pow n t).fun_inv (pow_ne_zero _ ht)).congr_deriv ?_
  rcases n with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

/-- **Gaussian integration by parts with a normalizer:** the case `H(t) = t⁻ⁿ` of
`integral_mul_mul_comp_eq_sum`, for a normalizer `Z ≥ z₀ > 0`. -/
theorem integral_mul_div_pow_eq_sum {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ} {Y : κ₃ → Ω → ℝ}
    (hWXY : HasGaussianLaw (fun ω s => Sum.elim W (Sum.elim X Y) s ω) P) {i : κ₁}
    (hW : ∫ ω, W i ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ m, ∫ ω, Y m ω ∂P = 0)
    {F : (κ₂ → ℝ) → ℝ} (hF : Differentiable ℝ F) {C c : ℝ}
    (hFg : ∀ x, |F x| ≤ C * Real.exp (c * ∑ l, |x l|)) {D d : κ₂ → ℝ}
    (hFg' : ∀ l x, |fderiv ℝ F x (Pi.single l 1)| ≤ D l * Real.exp (d l * ∑ l, |x l|))
    {Z : (κ₃ → ℝ) → ℝ} (hZ : Differentiable ℝ Z) {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hZb : ∀ y, z₀ ≤ Z y) {DZ dZ : κ₃ → ℝ}
    (hZg : ∀ m y, |fderiv ℝ Z y (Pi.single m 1)| ≤ DZ m * Real.exp (dZ m * ∑ m, |y m|))
    (n : ℕ) :
    ∫ ω, W i ω * (F (fun l => X l ω) / Z (fun m => Y m ω) ^ n) ∂P =
      (∑ l, (∫ ω, W i ω * X l ω ∂P) *
        ∫ ω, fderiv ℝ F (fun k => X k ω) (Pi.single l 1) / Z (fun m => Y m ω) ^ n ∂P) -
      n * ∑ m, (∫ ω, W i ω * Y m ω ∂P) *
        ∫ ω, F (fun l => X l ω) * fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) /
          Z (fun k => Y k ω) ^ (n + 1) ∂P := by
  have hpos : ∀ t ∈ Set.Ici z₀, 0 < t := fun t ht => hz₀.trans_le ht
  have hinv : ∀ (k : ℕ), ∀ t ∈ Set.Ici z₀, |(t ^ k)⁻¹| ≤ (z₀ ^ k)⁻¹ := fun k t ht => by
    rw [abs_of_pos (inv_pos.2 (pow_pos (hpos t ht) k))]
    exact inv_anti₀ (pow_pos hz₀ k) (pow_le_pow_left₀ hz₀.le ht k)
  have h := integral_mul_mul_comp_eq_sum hWXY hW hX hY hF hFg hFg' hZ hZg (s := Set.Ici z₀)
    hZb (H := fun t => (t ^ n)⁻¹) (H' := fun t => -(n * (t ^ (n + 1))⁻¹))
    (fun t ht => hasDerivAt_inv_pow (hpos t ht).ne' n) (hinv n)
    (M' := n * (z₀ ^ (n + 1))⁻¹) (fun t ht => by
      rw [abs_neg, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hinv (n + 1) t ht) (Nat.cast_nonneg n))
  have hneg : ∀ m, (∫ ω, W i ω * Y m ω ∂P) * ∫ ω, F (fun l => X l ω) *
        fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) *
          -((n : ℝ) * (Z (fun k => Y k ω) ^ (n + 1))⁻¹) ∂P =
      -((n : ℝ) * ((∫ ω, W i ω * Y m ω ∂P) * ∫ ω, F (fun l => X l ω) *
        fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) / Z (fun k => Y k ω) ^ (n + 1) ∂P)) := by
    intro m
    rw [mul_left_comm (n : ℝ), ← integral_const_mul (n : ℝ), ← mul_neg, ← integral_neg]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    ring
  simp only [hneg] at h
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← sub_eq_add_neg] at h
  simpa only [div_eq_mul_inv] using h

/-- **Gaussian integration by parts for `(F(X) / Z(Y)^n) * G(log Z(Y))`**, the case
`H(t) = t⁻ⁿ G(log t)` of `integral_mul_mul_comp_eq_sum`.
With `(W, X, Y)` jointly Gaussian and `W i`, `X`, `Y` centered, `F` bounded with bounded partials,
`Z ∈ [z₀, z₁]` (`z₀ > 0`) with bounded partials, and `G : ℝ → ℝ` differentiable on
`[log z₀, log z₁]` with `|G|`, `|deriv G|` bounded there,
`𝔼[W (F(X) / Z(Y)^n) G(log Z(Y))] =
  ∑_l 𝔼[W X_l] 𝔼[(∂_l F(X) / Z(Y)^n) G(log Z(Y))]
  + ∑_m 𝔼[W Y_m] 𝔼[(F(X) ∂_m Z(Y) / Z(Y)^{n+1}) (G'(log Z(Y)) - n G(log Z(Y)))]`. -/
theorem integral_mul_div_pow_mul_comp_log_eq_sum
    {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ} {Y : κ₃ → Ω → ℝ}
    (hWXY : HasGaussianLaw (fun ω s => Sum.elim W (Sum.elim X Y) s ω) P) {i : κ₁}
    (hW : ∫ ω, W i ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ m, ∫ ω, Y m ω ∂P = 0)
    {F : (κ₂ → ℝ) → ℝ} (hF : Differentiable ℝ F) {CF : ℝ} (hFb : ∀ x, |F x| ≤ CF)
    {DF : κ₂ → ℝ} (hFd : ∀ l x, |fderiv ℝ F x (Pi.single l 1)| ≤ DF l)
    {Z : (κ₃ → ℝ) → ℝ} (hZ : Differentiable ℝ Z) {z₀ z₁ : ℝ} (hz₀ : 0 < z₀)
    (hZb : ∀ y, z₀ ≤ Z y) (hZu : ∀ y, Z y ≤ z₁)
    {DZ : κ₃ → ℝ} (hZd : ∀ m y, |fderiv ℝ Z y (Pi.single m 1)| ≤ DZ m)
    {G : ℝ → ℝ} (hG : ∀ t ∈ Set.Icc (Real.log z₀) (Real.log z₁), DifferentiableAt ℝ G t)
    {CG CG' : ℝ}
    (hGb : ∀ t ∈ Set.Icc (Real.log z₀) (Real.log z₁), |G t| ≤ CG)
    (hGd : ∀ t ∈ Set.Icc (Real.log z₀) (Real.log z₁), |deriv G t| ≤ CG')
    (n : ℕ) :
    ∫ ω, W i ω * ((F (fun l => X l ω) / Z (fun m => Y m ω) ^ n) *
        G (Real.log (Z (fun m => Y m ω)))) ∂P =
      (∑ l, (∫ ω, W i ω * X l ω ∂P) *
        ∫ ω, (fderiv ℝ F (fun k => X k ω) (Pi.single l 1) / Z (fun m => Y m ω) ^ n) *
          G (Real.log (Z (fun m => Y m ω))) ∂P) +
      (∑ m, (∫ ω, W i ω * Y m ω ∂P) *
        ∫ ω, (F (fun l => X l ω) * fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) /
          Z (fun k => Y k ω) ^ (n + 1)) *
            (deriv G (Real.log (Z (fun k => Y k ω))) -
              (n : ℝ) * G (Real.log (Z (fun k => Y k ω)))) ∂P) := by
  have hmem : ∀ t ∈ Set.Icc z₀ z₁, Real.log t ∈ Set.Icc (Real.log z₀) (Real.log z₁) :=
    fun t ht => ⟨Real.log_le_log hz₀ ht.1, Real.log_le_log (hz₀.trans_le ht.1) ht.2⟩
  have hpos : ∀ t ∈ Set.Icc z₀ z₁, 0 < t := fun t ht => hz₀.trans_le ht.1
  have hinv : ∀ (k : ℕ), ∀ t ∈ Set.Icc z₀ z₁, |(t ^ k)⁻¹| ≤ (z₀ ^ k)⁻¹ := fun k t ht => by
    rw [abs_of_pos (inv_pos.2 (pow_pos (hpos t ht) k))]
    exact inv_anti₀ (pow_pos hz₀ k) (pow_le_pow_left₀ hz₀.le ht.1 k)
  have hH : ∀ t ∈ Set.Icc z₀ z₁, HasDerivAt (fun t : ℝ => (t ^ n)⁻¹ * G (Real.log t))
      ((t ^ (n + 1))⁻¹ * (deriv G (Real.log t) - n * G (Real.log t))) t := fun t ht => by
    have ht0 := (hpos t ht).ne'
    refine ((hasDerivAt_inv_pow ht0 n).mul
      ((hG _ (hmem t ht)).hasDerivAt.comp t (Real.hasDerivAt_log ht0))).congr_deriv ?_
    rw [pow_succ, mul_inv]
    simp only [Function.comp_apply]
    ring
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hFb 0)
  have hCG : 0 ≤ CG := (abs_nonneg _).trans (hGb _ (hmem _ ⟨hZb 0, hZu 0⟩))
  have h := integral_mul_mul_comp_eq_sum hWXY hW hX hY hF (C := CF) (c := 0)
    (fun x => by simpa using hFb x) (D := DF) (d := fun _ => 0)
    (fun l x => by simpa using hFd l x) hZ (DZ := DZ) (dZ := fun _ => 0)
    (fun m y => by simpa using hZd m y) (s := Set.Icc z₀ z₁) (fun y => ⟨hZb y, hZu y⟩) hH
    (M := (z₀ ^ n)⁻¹ * CG) (fun t ht => by
      rw [abs_mul]
      exact mul_le_mul (hinv n t ht) (hGb _ (hmem t ht)) (abs_nonneg _)
        (inv_nonneg.2 (pow_nonneg hz₀.le _)))
    (M' := (z₀ ^ (n + 1))⁻¹ * (CG' + n * CG)) (fun t ht => by
      rw [abs_mul]
      refine mul_le_mul (hinv (n + 1) t ht) ((abs_sub _ _).trans
        (add_le_add (hGd _ (hmem t ht)) ?_)) (abs_nonneg _)
        (inv_nonneg.2 (pow_nonneg hz₀.le _))
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hGb _ (hmem t ht)) (Nat.cast_nonneg n))
  have e0 : ∀ a z g : ℝ, a / z ^ n * g = a * ((z ^ n)⁻¹ * g) := fun a z g => by ring
  have e1 : ∀ a z g : ℝ, a / z ^ (n + 1) * g = a * ((z ^ (n + 1))⁻¹ * g) := fun a z g => by ring
  simp only [e0, e1]
  exact h

/-- **Gaussian integration by parts for `(F(X) / Z(Y)) * G(log Z(Y))`** (`n = 1` specialization). -/
theorem integral_mul_div_mul_comp_log_eq_sum
    {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ} {Y : κ₃ → Ω → ℝ}
    (hWXY : HasGaussianLaw (fun ω s => Sum.elim W (Sum.elim X Y) s ω) P) {i : κ₁}
    (hW : ∫ ω, W i ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ m, ∫ ω, Y m ω ∂P = 0)
    {F : (κ₂ → ℝ) → ℝ} (hF : Differentiable ℝ F) {CF : ℝ} (hFb : ∀ x, |F x| ≤ CF)
    {DF : κ₂ → ℝ} (hFd : ∀ l x, |fderiv ℝ F x (Pi.single l 1)| ≤ DF l)
    {Z : (κ₃ → ℝ) → ℝ} (hZ : Differentiable ℝ Z) {z₀ z₁ : ℝ} (hz₀ : 0 < z₀)
    (hZb : ∀ y, z₀ ≤ Z y) (hZu : ∀ y, Z y ≤ z₁)
    {DZ : κ₃ → ℝ} (hZd : ∀ m y, |fderiv ℝ Z y (Pi.single m 1)| ≤ DZ m)
    {G : ℝ → ℝ} (hG : ∀ t ∈ Set.Icc (Real.log z₀) (Real.log z₁), DifferentiableAt ℝ G t)
    {CG CG' : ℝ}
    (hGb : ∀ t ∈ Set.Icc (Real.log z₀) (Real.log z₁), |G t| ≤ CG)
    (hGd : ∀ t ∈ Set.Icc (Real.log z₀) (Real.log z₁), |deriv G t| ≤ CG') :
    ∫ ω, W i ω * ((F (fun l => X l ω) / Z (fun m => Y m ω)) *
        G (Real.log (Z (fun m => Y m ω)))) ∂P =
      (∑ l, (∫ ω, W i ω * X l ω ∂P) *
        ∫ ω, (fderiv ℝ F (fun k => X k ω) (Pi.single l 1) / Z (fun m => Y m ω)) *
          G (Real.log (Z (fun m => Y m ω))) ∂P) +
      (∑ m, (∫ ω, W i ω * Y m ω ∂P) *
        ∫ ω, (F (fun l => X l ω) * fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) /
          Z (fun k => Y k ω) ^ 2) *
            (deriv G (Real.log (Z (fun k => Y k ω))) - G (Real.log (Z (fun k => Y k ω)))) ∂P) := by
  simpa only [pow_one, Nat.cast_one, one_mul] using
    integral_mul_div_pow_mul_comp_log_eq_sum hWXY hW hX hY hF hFb hFd hZ hz₀ hZb hZu hZd
      hG hGb hGd 1

end ProbabilityTheory
