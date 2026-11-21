/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianIBPSecondDerivative

/-!
# Partial derivatives of the replica ratio in the site variables

For positive weights `w` and a positive function `ψ` on a finite spin set `κ`, the ratio
`G y = (∑_σ f σ ∏_r w (σ_r) ψ (y (σ_r))) / (∑_a w a ψ (y a)) ^ n` is the `n`-replica Gibbs average
of `f` for the site energies `log w a + log ψ (y a)` (`integral_pi_count_tilted_eq_sum_div`). Its
first partial derivative in `y_k` is `L'(y_k) ⟨(N_k - n G_k) f⟩` with `L = log ψ`, and the second
partial derivatives are the Hessian of `hasDerivAt_integral_pi_count_tilted_site_site`. This is the
bridge between the explicit ratio of the cavity (Talagrand Section 2.3), to which the Gaussian
interpolation with parameters applies, and the replica sums of (2.55)--(2.58).

* `SpinGlasses.replicaRatio_eq_integral_pi_count_tilted`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {κ R : Type*} [Fintype κ] [Fintype R] [DecidableEq R] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

/-- **The replica ratio is a Gibbs replica average.** For positive weights `w` and `ψ`, the ratio
`(∑_σ f σ ∏_r w (σ_r) ψ (σ_r)) / (∑_a w a ψ a) ^ |R|` is the `R`-replica Gibbs average of `f` for
the energy `log w + log ψ`. -/
theorem replicaRatio_eq_integral_pi_count_tilted {w ψ : κ → ℝ} (hw : ∀ a, 0 < w a)
    (hψ : ∀ a, 0 < ψ a) (f : (R → κ) → ℝ) :
    (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (σ r))) / (∑ a, w a * ψ a) ^ Fintype.card R =
      ∫ σ, f σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w a) + Real.log (ψ a))) :=
  (integral_pi_count_tilted_eq_sum_div (fun a => by
    rw [Real.exp_add, Real.exp_log (hw a), Real.exp_log (hψ a)]) f).symm

section Derivatives

variable [DecidableEq κ] [Nonempty κ] {w : κ → ℝ} {ψ ψ' : ℝ → ℝ}

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] [DecidableEq κ] in
/-- The replica ratio is differentiable in the site variables. -/
theorem differentiable_replicaRatio (hw : ∀ a, 0 < w a) (hψp : ∀ x, 0 < ψ x)
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (f : (R → κ) → ℝ) :
    Differentiable ℝ fun y : κ → ℝ => (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (y (σ r)))) /
      (∑ a, w a * ψ (y a)) ^ Fintype.card R := by
  have hψd : Differentiable ℝ ψ := fun x => (hψ x).differentiableAt
  have hcomp : ∀ a : κ, Differentiable ℝ fun y : κ → ℝ => ψ (y a) := fun a =>
    hψd.comp (differentiable_apply a)
  have hnum : Differentiable ℝ fun y : κ → ℝ =>
      ∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (y (σ r))) := by
    fun_prop
  have hden : Differentiable ℝ fun y : κ → ℝ => ∑ a, w a * ψ (y a) := by
    fun_prop
  have hne : ∀ y : κ → ℝ, (∑ a, w a * ψ (y a)) ^ Fintype.card R ≠ 0 := fun y =>
    pow_ne_zero _ (Finset.sum_pos (fun a _ => mul_pos (hw a) (hψp _)) Finset.univ_nonempty).ne'
  have hinv : Differentiable ℝ fun y : κ → ℝ => ((∑ a, w a * ψ (y a)) ^ Fintype.card R)⁻¹ :=
    (hden.pow _).inv hne
  exact hnum.mul hinv

/-- **First partial derivative of the replica ratio.** For `L = log ψ`,
`∂_{y_k} G = L'(y_k) ⟨(N_k - n G_k) f⟩` for the site energies `log w a + log ψ (y a)`. -/
theorem fderiv_replicaRatio_single (hw : ∀ a, 0 < w a) (hψp : ∀ x, 0 < ψ x)
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (f : (R → κ) → ℝ) (y : κ → ℝ) (k : κ) :
    fderiv ℝ (fun y : κ → ℝ => (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (y (σ r)))) /
        (∑ a, w a * ψ (y a)) ^ Fintype.card R) y (Pi.single k 1) =
      ψ' (y k) / ψ (y k) * ∫ σ, ((∑ r, if σ r = k then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (y a)))).real {k}) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => Real.log (w a) + Real.log (ψ (y a)))) := by
  have hG := differentiable_replicaRatio hw hψp hψ f
  have hline : HasDerivAt (fun ε : ℝ => y + ε • (Pi.single k (1 : ℝ) : κ → ℝ))
      (Pi.single k (1 : ℝ) : κ → ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (1 : ℝ) : κ → ℝ)).const_add y
  have h1 := (hG (y + (0 : ℝ) • (Pi.single k (1 : ℝ) : κ → ℝ))).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hline
  simp only [zero_smul, add_zero] at h1
  have hfun : (fun ε : ℝ => (fun y : κ → ℝ => (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (y (σ r)))) /
        (∑ a, w a * ψ (y a)) ^ Fintype.card R) (y + ε • (Pi.single k (1 : ℝ) : κ → ℝ))) =
      fun ε : ℝ => ∫ σ, f σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w a) +
          Real.log (ψ (y a + ε * if a = k then 1 else 0)))) := by
    funext ε
    rw [← replicaRatio_eq_integral_pi_count_tilted
      (ψ := fun a => ψ (y a + ε * if a = k then 1 else 0)) hw (fun a => hψp _)]
    simp [Pi.single_apply]
  have hL : ∀ x, HasDerivAt (fun x => Real.log (ψ x)) (ψ' x / ψ x) x := fun x =>
    (hψ x).log (hψp x).ne'
  have h2 := hasDerivAt_integral_pi_count_tilted_site (R := R) f (fun a => Real.log (w a)) hL y k
  rw [Function.comp_def, hfun] at h1
  exact h1.unique h2

/-- **Second partial derivative of the replica ratio.** For `L = log ψ`, `L' = ψ'/ψ` and
`L'' = (ψ'/ψ)'`, the mixed partial `∂_{y_k} ∂_{y_l} G` is
`1[l = k] L''(y_l) ⟨(N_l - n G_l) f⟩
  + L'(y_l) L'(y_k) ⟨f [(N_l - n G_l)(N_k - n G_k) - n G_l (1[l = k] - G_k)]⟩`. -/
theorem fderiv_fderiv_replicaRatio_single {ψ'' : ℝ → ℝ} (hw : ∀ a, 0 < w a)
    (hψp : ∀ x, 0 < ψ x) (hψc : ContDiff ℝ 2 ψ) (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hL' : ∀ x, HasDerivAt (fun x => ψ' x / ψ x) (ψ'' x) x) (f : (R → κ) → ℝ) (y : κ → ℝ)
    (k l : κ) :
    fderiv ℝ (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
        (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (y (σ r)))) /
          (∑ a, w a * ψ (y a)) ^ Fintype.card R) y (Pi.single l 1)) y (Pi.single k 1) =
      (if l = k then ψ'' (y l) else 0) * ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (y a)))).real {l}) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => Real.log (w a) + Real.log (ψ (y a)))) +
        ψ' (y l) / ψ (y l) * (ψ' (y k) / ψ (y k)) * ∫ σ, (((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (y a)))).real {l}) *
        ((∑ r, if σ r = k then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (y a)))).real {k}) -
        Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (y a)))).real {l} *
          ((if l = k then 1 else 0) - (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (y a)))).real {k})) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => Real.log (w a) + Real.log (ψ (y a)))) := by
  have hψd : Differentiable ℝ ψ := fun x => (hψ x).differentiableAt
  set G : (κ → ℝ) → ℝ := fun y => (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (y (σ r)))) /
    (∑ a, w a * ψ (y a)) ^ Fintype.card R with hGdef
  have hGc : ContDiff ℝ 2 G := by
    have hnum : ContDiff ℝ 2 fun y : κ → ℝ =>
        ∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ (y (σ r))) := by fun_prop
    have hden : ContDiff ℝ 2 fun y : κ → ℝ => (∑ a, w a * ψ (y a)) ^ Fintype.card R := by
      fun_prop
    exact hnum.div hden fun y => pow_ne_zero _ (Finset.sum_pos
      (fun a _ => mul_pos (hw a) (hψp _)) Finset.univ_nonempty).ne'
  have hQ : Differentiable ℝ fun y : κ → ℝ => fderiv ℝ G y (Pi.single l 1) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ G) := hGc.fderiv_right (by norm_num)
    exact (h1.clm_apply contDiff_const).differentiable one_ne_zero
  have hline : HasDerivAt (fun ε : ℝ => y + ε • (Pi.single k (1 : ℝ) : κ → ℝ))
      (Pi.single k (1 : ℝ) : κ → ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (1 : ℝ) : κ → ℝ)).const_add y
  have h1 := (hQ (y + (0 : ℝ) • (Pi.single k (1 : ℝ) : κ → ℝ))).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hline
  simp only [zero_smul, add_zero] at h1
  have hfun : (fun ε : ℝ => (fun y : κ → ℝ => fderiv ℝ G y (Pi.single l 1))
      (y + ε • (Pi.single k (1 : ℝ) : κ → ℝ))) = fun ε : ℝ =>
        ψ' (y l + ε * if l = k then 1 else 0) / ψ (y l + ε * if l = k then 1 else 0) *
        ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (fun a => Real.log (w a) +
            Real.log (ψ (y a + ε * if a = k then 1 else 0)))).real {l}) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (fun a => Real.log (w a) +
            Real.log (ψ (y a + ε * if a = k then 1 else 0)))) := by
    funext ε
    have := fderiv_replicaRatio_single hw hψp hψ f (y + ε • (Pi.single k (1 : ℝ) : κ → ℝ)) l
    simpa [Pi.single_apply] using this
  have hL : ∀ x, HasDerivAt (fun x => Real.log (ψ x)) (ψ' x / ψ x) x := fun x =>
    (hψ x).log (hψp x).ne'
  have h2 := hasDerivAt_integral_pi_count_tilted_site_site (R := R) f (fun a => Real.log (w a))
    hL hL' y l k
  rw [Function.comp_def, hfun] at h1
  exact h1.unique h2

/-- **Parameter derivative of the replica ratio.** If `s ↦ ψ s x` has derivative `dψ x` at `t`
(with `ψ s x > 0`), the ratio built from `ψ s` has derivative
`∑_l (dψ (y_l) / ψ t (y_l)) ⟨(N_l - n G_l) f⟩` at `t`: the energy path
`log w a + log ψ s (y a)` has velocity `dψ (y a) / ψ t (y a)`. -/
theorem hasDerivAt_replicaRatio_param {ψ : ℝ → ℝ → ℝ} {dψ : ℝ → ℝ} {t : ℝ}
    (hw : ∀ a, 0 < w a) (hψp : ∀ s x, 0 < ψ s x) (hψ : ∀ x, HasDerivAt (fun s => ψ s x) (dψ x) t)
    (f : (R → κ) → ℝ) (y : κ → ℝ) :
    HasDerivAt (fun s : ℝ => (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ s (y (σ r)))) /
        (∑ a, w a * ψ s (y a)) ^ Fintype.card R)
      (∑ l, dψ (y l) / ψ t (y l) * ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ t (y a)))).real {l}) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => Real.log (w a) + Real.log (ψ t (y a))))) t := by
  have hfun : (fun s : ℝ => (∑ σ : R → κ, f σ * ∏ r, (w (σ r) * ψ s (y (σ r)))) /
        (∑ a, w a * ψ s (y a)) ^ Fintype.card R) = fun s : ℝ =>
      ∫ σ, f σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w a) + Real.log (ψ s (y a)))) := by
    funext s
    exact replicaRatio_eq_integral_pi_count_tilted (ψ := fun a => ψ s (y a)) hw
      (fun a => hψp _ _) f
  rw [hfun]
  have hf : ∀ a, HasDerivAt (fun s : ℝ => Real.log (w a) + Real.log (ψ s (y a)))
      (dψ (y a) / ψ t (y a)) t := fun a =>
    ((hψ (y a)).log (hψp _ _).ne').const_add _
  have key := hasDerivAt_integral_pi_count_tilted_path (R := R) f
    (fun s a => Real.log (w a) + Real.log (ψ s (y a))) (fun a => dψ (y a) / ψ t (y a)) t hf
  refine key.congr_deriv ?_
  have hmean : ∫ τ, dψ (y τ) / ψ t (y τ) ∂(Measure.count.tilted
      (fun a => Real.log (w a) + Real.log (ψ t (y a)))) =
      ∑ l, dψ (y l) / ψ t (y l) * (Measure.count.tilted
        (fun a => Real.log (w a) + Real.log (ψ t (y a)))).real {l} := by
    rw [integral_count_tilted]
    exact Finset.sum_congr rfl fun l _ => by rw [real_count_tilted_singleton]; ring
  rw [hmean]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun l _ => Integrable.of_finite)]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  have h1 : ∑ r, dψ (y (σ r)) / ψ t (y (σ r)) =
      ∑ l, dψ (y l) / ψ t (y l) * ∑ r, if σ r = l then (1 : ℝ) else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp
  beta_reduce
  rw [h1, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Derivatives

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The diagonal cancellation of (2.58), as an identity of finite sums.** Let `c l k` be a matrix
with constant diagonal `c l l = -d`, and set `X_l = N_l - n G_l`. The covariance-difference term
`∑_{l,k} c l k [1[l=k] L''_l X_l + u_l u_k (X_l X_k - n G_l (1[l=k] - G_k))]` and the `τ`-term
`d ∑_l (L''_l + u_l²) X_l` combine to the sum over pairs without the `L''` terms and with the
diagonal pieces `c l l u_l² X_l` removed. -/
theorem sum_hessian_add_tau_term (c : ι → ι → ℝ) (d : ℝ) (hc : ∀ l, c l l = -d)
    (u L2 G N : ι → ℝ) (n : ℝ) :
    ∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * (N l - n * G l) +
        u l * u k * ((N l - n * G l) * (N k - n * G k) -
          n * G l * ((if l = k then 1 else 0) - G k))) +
      d * ∑ l, (L2 l + u l ^ 2) * (N l - n * G l) =
    ∑ l, ∑ k, c l k * (u l * u k * ((N l - n * G l) * (N k - n * G k) -
          n * G l * ((if l = k then 1 else 0) - G k))) -
      ∑ l, c l l * u l ^ 2 * (N l - n * G l) := by
  have hdiag : ∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * (N l - n * G l)) =
      ∑ l, (-d * L2 l * (N l - n * G l)) :=
    Finset.sum_congr rfl fun l _ => by
      rw [Finset.sum_eq_single l (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
      simp [hc]
      ring
  have hsplit : ∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * (N l - n * G l) +
        u l * u k * ((N l - n * G l) * (N k - n * G k) -
          n * G l * ((if l = k then 1 else 0) - G k))) =
      ∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * (N l - n * G l)) +
      ∑ l, ∑ k, c l k * (u l * u k * ((N l - n * G l) * (N k - n * G k) -
          n * G l * ((if l = k then 1 else 0) - G k))) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  have hlast : ∑ l, c l l * u l ^ 2 * (N l - n * G l) = ∑ l, (-d * u l ^ 2 * (N l - n * G l)) :=
    Finset.sum_congr rfl fun l _ => by rw [hc]
  have key : ∑ l, (-d * L2 l * (N l - n * G l)) + d * ∑ l, (L2 l + u l ^ 2) * (N l - n * G l) +
      ∑ l, (-d * u l ^ 2 * (N l - n * G l)) = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => by ring
  rw [hsplit, hdiag, hlast]
  linarith

omit [DecidableEq R] in
/-- **The diagonal cancellation under a finite replica average.** The identity
`sum_hessian_add_tau_term` with `N_l = ∑_r 1[σ_r = l]` integrated against `f` over any replica
measure on a finite configuration space. -/
theorem integral_sum_hessian_add_tau_term [DecidableEq κ] (μ : Measure (R → κ))
    [IsFiniteMeasure μ]
    (c : κ → κ → ℝ) (d : ℝ) (hc : ∀ l, c l l = -d) (u L2 G : κ → ℝ) (f : (R → κ) → ℝ) :
    ∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * G l) * f σ ∂μ +
        u l * u k * ∫ σ, (((∑ r, if σ r = l then (1 : ℝ) else 0) - Fintype.card R * G l) *
          ((∑ r, if σ r = k then (1 : ℝ) else 0) - Fintype.card R * G k) -
          Fintype.card R * G l * ((if l = k then 1 else 0) - G k)) * f σ ∂μ) +
      d * ∑ l, (L2 l + u l ^ 2) * ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * G l) * f σ ∂μ =
    ∑ l, ∑ k, c l k * (u l * u k * ∫ σ, (((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * G l) * ((∑ r, if σ r = k then (1 : ℝ) else 0) -
          Fintype.card R * G k) - Fintype.card R * G l * ((if l = k then 1 else 0) - G k)) *
          f σ ∂μ) -
      ∑ l, c l l * u l ^ 2 * ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * G l) * f σ ∂μ := by
  have hI : ∀ g : (R → κ) → ℝ, Integrable g μ := fun g => Integrable.of_finite
  set X : κ → (R → κ) → ℝ := fun l σ => (∑ r, if σ r = l then (1 : ℝ) else 0) -
    Fintype.card R * G l with hX
  set T : κ → κ → (R → κ) → ℝ := fun l k σ => X l σ * X k σ -
    Fintype.card R * G l * ((if l = k then 1 else 0) - G k) with hT
  have hpt : ∀ σ : R → κ,
      (∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * (X l σ * f σ) +
        u l * u k * (T l k σ * f σ)) + d * ∑ l, (L2 l + u l ^ 2) * (X l σ * f σ)) =
      ∑ l, ∑ k, c l k * (u l * u k * (T l k σ * f σ)) -
        ∑ l, c l l * u l ^ 2 * (X l σ * f σ) := fun σ => by
    have h := sum_hessian_add_tau_term (fun l k => f σ * c l k) (f σ * d)
      (fun l => by rw [hc]; ring) u L2 G
      (fun l => ∑ r, if σ r = l then (1 : ℝ) else 0) (Fintype.card R : ℝ)
    simp only [hX, hT] at h ⊢
    convert h using 1
    · refine congrArg₂ _ ?_ ?_
      · exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
      · rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    · refine congrArg₂ _ ?_ ?_
      · exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
      · exact Finset.sum_congr rfl fun l _ => by ring
  have e1 : ∫ σ, (∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * (X l σ * f σ) +
        u l * u k * (T l k σ * f σ)) + d * ∑ l, (L2 l + u l ^ 2) * (X l σ * f σ)) ∂μ =
      ∑ l, ∑ k, c l k * ((if l = k then L2 l else 0) * ∫ σ, X l σ * f σ ∂μ +
        u l * u k * ∫ σ, T l k σ * f σ ∂μ) +
      d * ∑ l, (L2 l + u l ^ 2) * ∫ σ, X l σ * f σ ∂μ := by
    simp (disch := first | exact Integrable.of_finite |
        (intro _ _; exact Integrable.of_finite)) only [integral_add, integral_finsetSum,
      integral_const_mul]
  have e2 : ∫ σ, (∑ l, ∑ k, c l k * (u l * u k * (T l k σ * f σ)) -
        ∑ l, c l l * u l ^ 2 * (X l σ * f σ)) ∂μ =
      ∑ l, ∑ k, c l k * (u l * u k * ∫ σ, T l k σ * f σ ∂μ) -
      ∑ l, c l l * u l ^ 2 * ∫ σ, X l σ * f σ ∂μ := by
    simp (disch := first | exact Integrable.of_finite |
        (intro _ _; exact Integrable.of_finite)) only [integral_sub, integral_finsetSum,
      integral_const_mul]
  have := integral_congr_ae (μ := μ) (ae_of_all _ hpt)
  rw [e1, e2] at this
  exact this

end Algebra

end SpinGlasses
