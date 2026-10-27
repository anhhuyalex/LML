/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Concentration
public import LeanMachineLearning.SpinGlasses.FreeEnergy
public import LeanMachineLearning.SpinGlasses.GibbsMeasure

/-!
# Free energy of a Gaussian field tilted by a deterministic observable

For a finite configuration space `α`, a linear Gaussian field `x ↦ a x ⬝ᵥ g` of an i.i.d. standard
Gaussian disorder `g`, an offset `d` and a tilt `b`, put
`Z(s, g) = ∑ₓ exp (a x ⬝ᵥ g + d x + s b x)`.  This file proves the calculus and concentration of
`s ↦ 𝔼 log Z(s, ·)` which is needed for the coupled free energy of Talagrand's Section 1.9:

* `convexOn_log_sum_exp_add_mul`, `convexOn_integral_log_sum_exp_tilt`: convexity in `s`;
* `hasDerivAt_integral_log_sum_exp_tilt`: `(d/ds) 𝔼 log Z = 𝔼 ⟨b⟩_s`;
* `measureReal_abs_sub_integral_log_sum_exp_tilt_ge_le`: Gaussian concentration of `log Z(s)`;
* `log_sum_exp_add_mul_sub_ge`: the lower bound by the Gibbs mass of a set where `s b` is large.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix

namespace SpinGlasses

section Finite

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **Convexity of the log-partition function in a tilt parameter.**  For weights `exp (d x)` and
an observable `b`, `s ↦ log ∑ₓ exp (d x + s b x)` is convex (Hölder's inequality, here in the form
of the weighted AM-GM inequality for the normalized weights at `s` and `t`). -/
theorem convexOn_log_sum_exp_add_mul (d b : α → ℝ) :
    ConvexOn ℝ Set.univ (fun s => Real.log (∑ x, Real.exp (d x + s * b x))) := by
  refine ⟨convex_univ, fun s _ t _ θ₁ θ₂ h₁ h₂ h12 => ?_⟩
  have hZ : ∀ r : ℝ, 0 < ∑ x, Real.exp (d x + r * b x) := fun r =>
    Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  set Zs := ∑ x, Real.exp (d x + s * b x) with hZs
  set Zt := ∑ x, Real.exp (d x + t * b x) with hZt
  have hs0 : Zs ≠ 0 := (hZ s).ne'
  have ht0 : Zt ≠ 0 := (hZ t).ne'
  have key : ∀ x, Real.exp (d x + (θ₁ • s + θ₂ • t) * b x) ≤
      Zs ^ θ₁ * Zt ^ θ₂ * (θ₁ * (Real.exp (d x + s * b x) / Zs) +
        θ₂ * (Real.exp (d x + t * b x) / Zt)) := fun x => by
    have e : Real.exp (d x + (θ₁ • s + θ₂ • t) * b x) =
        Zs ^ θ₁ * Zt ^ θ₂ * ((Real.exp (d x + s * b x) / Zs) ^ θ₁ *
          (Real.exp (d x + t * b x) / Zt) ^ θ₂) := by
      have h1 : Real.exp (d x + s * b x) = Zs * (Real.exp (d x + s * b x) / Zs) := by
        field_simp
      have h2 : Real.exp (d x + t * b x) = Zt * (Real.exp (d x + t * b x) / Zt) := by
        field_simp
      have h3 : Real.exp (d x + (θ₁ • s + θ₂ • t) * b x) =
          Real.exp (d x + s * b x) ^ θ₁ * Real.exp (d x + t * b x) ^ θ₂ := by
        rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
        congr 1
        simp only [smul_eq_mul]
        have : θ₂ = 1 - θ₁ := by linarith
        subst this
        ring
      rw [h3]
      conv_lhs => rw [h1, h2]
      rw [Real.mul_rpow (hZ s).le (div_nonneg (Real.exp_pos _).le (hZ s).le),
        Real.mul_rpow (hZ t).le (div_nonneg (Real.exp_pos _).le (hZ t).le)]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.rpow_nonneg (hZ s).le _)
      (Real.rpow_nonneg (hZ t).le _))
    exact Real.geom_mean_le_arith_mean2_weighted h₁ h₂ (div_nonneg (Real.exp_pos _).le
      (hZ s).le) (div_nonneg (Real.exp_pos _).le (hZ t).le) h12
  have hsum : ∑ x, Real.exp (d x + (θ₁ • s + θ₂ • t) * b x) ≤ Zs ^ θ₁ * Zt ^ θ₂ := by
    refine (Finset.sum_le_sum fun x _ => key x).trans_eq ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.sum_div, ← Finset.sum_div, div_self (hZ s).ne', div_self (hZ t).ne']
    rw [mul_one, mul_one, h12, mul_one]
  have hpos := hZ (θ₁ • s + θ₂ • t)
  calc Real.log (∑ x, Real.exp (d x + (θ₁ • s + θ₂ • t) * b x))
      ≤ Real.log (Zs ^ θ₁ * Zt ^ θ₂) := Real.log_le_log hpos hsum
    _ = θ₁ • Real.log Zs + θ₂ • Real.log Zt := by
      rw [Real.log_mul (Real.rpow_pos_of_pos (hZ s) _).ne' (Real.rpow_pos_of_pos (hZ t) _).ne',
        Real.log_rpow (hZ s), Real.log_rpow (hZ t)]
      rfl

/-- **Lower bound by a set where the tilt is large.**  If `m ≤ s b x` on a nonempty set `T`, the
log-partition function of the tilted energy exceeds that of `f` by at least `m` plus the log of the
Gibbs mass of `T`:
`m + log (∑_{x ∈ T} e^{f x} / ∑ₓ e^{f x}) ≤ log ∑ₓ e^{f x + s b x} - log ∑ₓ e^{f x}`. -/
theorem log_sum_exp_add_mul_sub_ge (f b : α → ℝ) (s m : ℝ) (T : Finset α) (hT : T.Nonempty)
    (hm : ∀ x ∈ T, m ≤ s * b x) :
    m + Real.log ((∑ x ∈ T, Real.exp (f x)) / ∑ x, Real.exp (f x)) ≤
      Real.log (∑ x, Real.exp (f x + s * b x)) - Real.log (∑ x, Real.exp (f x)) := by
  have hZ : 0 < ∑ x, Real.exp (f x) :=
    Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  have hA : 0 < ∑ x ∈ T, Real.exp (f x) := Finset.sum_pos (fun x _ => Real.exp_pos _) hT
  have h1 : Real.exp m * ∑ x ∈ T, Real.exp (f x) ≤ ∑ x, Real.exp (f x + s * b x) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun x hx => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ T) fun x _ _ => (Real.exp_pos _).le)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [hm x hx])
  have h2 := Real.log_le_log (mul_pos (Real.exp_pos m) hA) h1
  rw [Real.log_mul (Real.exp_pos m).ne' hA.ne', Real.log_exp] at h2
  rw [Real.log_div hA.ne' hZ.ne']
  linarith

end Finite

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A bounded variable with mean at least `e` is at least `e / 2` with probability at least
`e / 2`:** `𝔼 X ≤ e / 2 + ℙ(X ≥ e / 2)` for `0 ≤ X ≤ 1`. -/
theorem measureReal_ge_half_of_le_integral {X : Ω → ℝ} (hX : Measurable X)
    (hX01 : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) {e : ℝ} (he : 0 ≤ e) (hXe : e ≤ ∫ ω, X ω ∂P) :
    e / 2 ≤ P.real {ω | e / 2 ≤ X ω} := by
  have hmeas : MeasurableSet {ω | e / 2 ≤ X ω} := measurableSet_le measurable_const hX
  have hind : Integrable ((fun _ => e / 2) + {ω | e / 2 ≤ X ω}.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const _).add ((integrable_const _).indicator hmeas)
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX01 ω).1]
      exact (hX01 ω).2)
  have := integral_mono hXi hind fun ω => by
    simp only [Pi.add_apply, Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : e / 2 ≤ X ω
    · simp only [h, ↓reduceIte]
      linarith [(hX01 ω).2, (hX01 ω).1]
    · simp only [h, ↓reduceIte]
      linarith [not_le.1 h]
  simp only [Pi.add_apply] at this
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hmeas),
    integral_indicator_const _ hmeas] at this
  simp only [integral_const, smul_eq_mul, mul_one] at this
  rw [probReal_univ, one_mul] at this
  linarith

/-- **Concentration transfers a samplewise bound on the event of a non-negligible Gibbs mass to the
mean.**  Let `A`, `B` be integrable with tails `ℙ(s ≤ |A - 𝔼 A|), ℙ(s ≤ |B - 𝔼 B|) ≤ c`, let
`X ∈ [0, 1]` have mean at least `e > 0`, and suppose `m ≤ A - B` whenever `X ≥ e / 2`.  If
`2 c < e / 2` then `m - 2 s < 𝔼 A - 𝔼 B`. -/
theorem lt_integral_sub_of_tail {A B X : Ω → ℝ} (hX : Measurable X)
    (hX01 : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) {e m s c : ℝ} (he : 0 ≤ e) (hXe : e ≤ ∫ ω, X ω ∂P)
    (hAB : ∀ ω, e / 2 ≤ X ω → m ≤ A ω - B ω)
    (hcA : P.real {ω | s ≤ |A ω - ∫ ω', A ω' ∂P|} ≤ c)
    (hcB : P.real {ω | s ≤ |B ω - ∫ ω', B ω' ∂P|} ≤ c) (hc : 2 * c < e / 2) :
    m - 2 * s < ∫ ω, A ω ∂P - ∫ ω, B ω ∂P := by
  have hE := measureReal_ge_half_of_le_integral hX hX01 he hXe
  by_contra hcon
  have hsub : {ω | e / 2 ≤ X ω} ⊆ {ω | s ≤ |A ω - ∫ ω', A ω' ∂P|} ∪
      {ω | s ≤ |B ω - ∫ ω', B ω' ∂P|} := fun ω hω => by
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
    have h1 := hAB ω hω
    obtain ⟨ha, hb⟩ := hn
    rw [abs_lt] at ha hb
    exact hcon (by linarith [ha.1, ha.2, hb.1, hb.2])
  have := (measureReal_mono (μ := P) hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  linarith

end Probability

section GaussianTilt

variable {α κ : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype κ] (a : α → κ → ℝ) (d b : α → ℝ)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The mean log-partition function of the tilted Gaussian energy is convex in the tilt. -/
theorem convexOn_integral_log_sum_exp_tilt :
    ConvexOn ℝ Set.univ (fun s => ∫ g : κ → ℝ,
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + s * b x))
        ∂(Measure.pi fun _ : κ => gaussianReal 0 1)) := by
  refine integral_convexOn_of_integrand_ae convex_univ ?_ ?_
  · exact Filter.Eventually.of_forall fun g =>
      convexOn_log_sum_exp_add_mul (fun x => a x ⬝ᵥ g + d x) b
  · intro s _
    simpa only [add_assoc] using integrable_log_sum_exp_linear_gaussian a (fun x => d x + s * b x)

/-- **Derivative of the mean log-partition function in the tilt:** `(d/ds) 𝔼 log Z(s) = 𝔼 ⟨b⟩_s`,
where `⟨·⟩_s` is the Gibbs average of the energy `a x ⬝ᵥ g + d x + s b x`.  This is
`hasDerivAt_integral_log_sum_exp_path` with the constant bound `∑ₓ |b x|` on `∂ₛ`. -/
theorem hasDerivAt_integral_log_sum_exp_tilt (t : ℝ) :
    HasDerivAt (fun s => ∫ g : κ → ℝ, Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + s * b x))
        ∂(Measure.pi fun _ : κ => gaussianReal 0 1))
      (∫ g : κ → ℝ, ∑ x, Real.exp (a x ⬝ᵥ g + d x + t * b x) /
          (∑ y, Real.exp (a y ⬝ᵥ g + d y + t * b y)) * b x
        ∂(Measure.pi fun _ : κ => gaussianReal 0 1)) t := by
  have hint : Integrable (fun g : κ → ℝ =>
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + t * b x)))
      (Measure.pi fun _ : κ => gaussianReal 0 1) := by
    simpa only [add_assoc] using integrable_log_sum_exp_linear_gaussian a (fun x => d x + t * b x)
  have h := hasDerivAt_integral_log_sum_exp_path (μ := Measure.pi fun _ : κ => gaussianReal 0 1)
    (f := fun s g x => a x ⬝ᵥ g + d x + s * b x) (f' := fun _ _ x => b x) (t := t)
    (S := Set.univ) Filter.univ_mem (fun s x => by fun_prop) (fun x => aemeasurable_const) hint
    (fun g s _ x => (((hasDerivAt_id s).mul_const (b x)).const_add (a x ⬝ᵥ g + d x)).congr_deriv
      (one_mul _)) (integrable_const (∑ x, |b x|))
    (fun g s _ x => Finset.single_le_sum (f := fun y => |b y|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x))
  simp only [integral_count_tilted] at h
  exact h

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Gaussian concentration of the tilted log-partition function:** if
`a x ⬝ᵥ a x ≤ v` for all `x` then
`ℙ(y ≤ |log Z(s) - 𝔼 log Z(s)|) ≤ 2 exp (-y² / (4 v))`. -/
theorem measureReal_abs_sub_integral_log_sum_exp_tilt_ge_le {v : ℝ} (hv : ∀ x, a x ⬝ᵥ a x ≤ v)
    (s : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).real
      {g | y ≤ |Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + s * b x)) -
        ∫ g', Real.log (∑ x, Real.exp (a x ⬝ᵥ g' + d x + s * b x))
          ∂(Measure.pi fun _ : κ => gaussianReal 0 1)|} ≤
      2 * Real.exp (-y ^ 2 / (4 * v)) := by
  have hg := hasGaussianLaw_dotProduct_family a
  have := measureReal_abs_sub_integral_ge_le_of_log_sum_exp (g := fun x (g : κ → ℝ) => a x ⬝ᵥ g)
    (P := Measure.pi fun _ : κ => gaussianReal 0 1) hg (fun x => by fun_prop)
    (fun x => integral_dotProduct_pi_gaussianReal (a x)) (v := v)
    (fun x => by
      rw [show (fun g : κ → ℝ => (a x ⬝ᵥ g) ^ 2) = fun g => (a x ⬝ᵥ g) * (a x ⬝ᵥ g) from
        funext fun g => sq _, integral_dotProduct_mul_dotProduct_pi_gaussianReal]
      exact hv x) (fun x => d x + s * b x) hy
  simpa only [add_assoc] using this

end GaussianTilt

section Convex

/-- **Derivative separation from a one-sided tail bound.**  Let `ψ` be convex with `ψ 0 = 0` and
derivative `ψ'`, and put `x = ψ' 0`.  If `ψ λ > λ x + c λ` for some `λ > 0`, or
`ψ (-λ) > -λ x + c λ`, then `ψ' λ - ψ' (-λ) > c`.  (Talagrand, last line of the proof of
Proposition 1.9.7.) -/
theorem deriv_sub_deriv_gt_of_convex {ψ ψ' : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ ψ)
    (hd : ∀ t, HasDerivAt ψ (ψ' t) t) (h0 : ψ 0 = 0) {lam c : ℝ} (hlam : 0 < lam)
    (h : lam * ψ' 0 + c * lam < ψ lam ∨ -lam * ψ' 0 + c * lam < ψ (-lam)) :
    c < ψ' lam - ψ' (-lam) := by
  have hmono : MonotoneOn (deriv ψ) Set.univ :=
    hc.monotoneOn_deriv fun t _ => (hd t).differentiableAt
  have h1 : ψ' (-lam) ≤ ψ' 0 := by
    have := hmono (Set.mem_univ (-lam)) (Set.mem_univ 0) (by linarith)
    rwa [(hd _).deriv, (hd _).deriv] at this
  have h2 : ψ' 0 ≤ ψ' lam := by
    have := hmono (Set.mem_univ 0) (Set.mem_univ lam) hlam.le
    rwa [(hd _).deriv, (hd _).deriv] at this
  rcases h with h | h
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ lam) hlam (hd lam)
    rw [slope_def_field, h0, sub_zero, sub_zero, div_le_iff₀ hlam] at this
    nlinarith
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ (-lam)) (Set.mem_univ 0) (by linarith)
      (hd (-lam))
    rw [slope_def_field, h0, zero_sub, zero_sub, neg_neg, le_div_iff₀ hlam] at this
    nlinarith

end Convex

section Mass

variable {α κ : Type*} [Fintype α] [Nonempty α] [Fintype κ] (a : α → κ → ℝ) (d : α → ℝ)

omit [Nonempty α] in
/-- The Gibbs mass of a set `T` is a measurable function of the disorder. -/
theorem measurable_gibbs_mass (T : Finset α) :
    Measurable (fun g : κ → ℝ => (∑ x ∈ T, Real.exp (a x ⬝ᵥ g + d x)) /
      ∑ y, Real.exp (a y ⬝ᵥ g + d y)) := by
  fun_prop

/-- The Gibbs mass of a set `T` lies in `[0, 1]`. -/
theorem gibbs_mass_mem_Icc (T : Finset α) (g : κ → ℝ) :
    0 ≤ (∑ x ∈ T, Real.exp (a x ⬝ᵥ g + d x)) / ∑ y, Real.exp (a y ⬝ᵥ g + d y) ∧
      (∑ x ∈ T, Real.exp (a x ⬝ᵥ g + d x)) / ∑ y, Real.exp (a y ⬝ᵥ g + d y) ≤ 1 := by
  have hZ : 0 < ∑ y, Real.exp (a y ⬝ᵥ g + d y) :=
    Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  refine ⟨div_nonneg (Finset.sum_nonneg fun x _ => (Real.exp_pos _).le) hZ.le, ?_⟩
  rw [div_le_one hZ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    fun x _ _ => (Real.exp_pos _).le

/-- The Gibbs mass of a set `T` is integrable against the Gaussian disorder. -/
theorem integrable_gibbs_mass (T : Finset α) :
    Integrable (fun g : κ → ℝ => (∑ x ∈ T, Real.exp (a x ⬝ᵥ g + d x)) /
      ∑ y, Real.exp (a y ⬝ᵥ g + d y)) (Measure.pi fun _ : κ => gaussianReal 0 1) :=
  Integrable.of_bound (measurable_gibbs_mass a d T).aestronglyMeasurable 1
    (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbs_mass_mem_Icc a d T g).1]
      exact (gibbs_mass_mem_Icc a d T g).2)

end Mass

end SpinGlasses
