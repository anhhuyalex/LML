/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.SpinGlasses.Basic
public import LeanMachineLearning.SpinGlasses.SKModel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Free energy and the smooth approximation of the ground-state energy

The partition function at inverse temperature `β` of an energy function `H : α → ℝ` on a finite
configuration space is `Z(β) = ∑ a, exp (β * H a)`, and the free energy is the normalized expected
log-partition function `N⁻¹ 𝔼 log Z(β)` ([Panchenko, 2013, §1.1]).  The elementary sandwich
`max H ≤ β⁻¹ log Z(β) ≤ β⁻¹ log |α| + max H` ([Panchenko, 2013, Eq. (1.7)]) says that the free
energy at large `β` approximates the ground-state energy.

No definition is introduced: the partition function is the explicit sum, the maximum is
`Function.max` (`ForMathlib/MeasureTheory/Order/MeasurableArg.lean`, with its measurability), and
the expectation is the Bochner integral.  The three layers are kept apart, so that each is reusable
for any finite Gibbs system (Potts, random-field Ising, mixed `p`-spin, ...).

## Main declarations

* **Deterministic** (any finite nonempty `α`, `β > 0`):
  `SpinGlasses.max_le_inv_mul_log_sum_exp`, `SpinGlasses.inv_mul_log_sum_exp_le`,
  `SpinGlasses.abs_inv_mul_log_sum_exp_sub_max_le`.
* **Random energy** `H : Ω → α → ℝ` with measurable, integrable coordinates on a probability
  space: `SpinGlasses.integrable_max`, `SpinGlasses.integrable_log_sum_exp` and the integrated
  sandwich `SpinGlasses.integral_max_le_inv_mul_integral_log_sum_exp`,
  `SpinGlasses.inv_mul_integral_log_sum_exp_le`,
  `SpinGlasses.abs_inv_mul_integral_log_sum_exp_sub_integral_max_le`.
* **Hypercube** `α = ι → ℤˣ`, `|α| = 2 ^ N`, after dividing by `N`:
  `SpinGlasses.smooth_approximation_sandwich` (Eq. (1.7)) and
  `SpinGlasses.smooth_approximation_error_bound` (the error `log 2 / β`).
* **SK model**: `SpinGlasses.sk_smooth_approximation_sandwich` and
  `SpinGlasses.sk_smooth_approximation_error_bound` discharge the measurability and integrability
  hypotheses for the Hamiltonian of `SKModel.lean` (Gaussian disorder, via
  `memLp_linearForm_gaussianInit`).  The Hamiltonian enters through its defining equation, as a
  hypothesis `hH : ∀ G σ, H G σ = (√N)⁻¹ * (σ ⬝ᵥ (G *ᵥ σ))`, instead of a named definition.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Matrix

namespace SpinGlasses

section Deterministic

variable {α : Type*} [Fintype α] [Nonempty α] {β : ℝ}

/-- **Log-sum-exp, lower bound:** `max_a f a ≤ β⁻¹ log ∑ₐ exp (β f a)` for `β > 0`. -/
theorem max_le_inv_mul_log_sum_exp (hβ : 0 < β) (f : α → ℝ) :
    f.max ≤ β⁻¹ * Real.log (∑ a, Real.exp (β * f a)) := by
  obtain ⟨a, ha⟩ := exists_argmax f
  rw [le_inv_mul_iff₀ hβ, ← ha, mul_comm, ← Real.log_exp (f a * β)]
  exact Real.log_le_log (Real.exp_pos _)
    (Finset.single_le_sum (f := fun a => Real.exp (β * f a)) (fun _ _ => (Real.exp_pos _).le)
      (mem_univ a) |>.trans_eq' (by rw [mul_comm]))

/-- **Log-sum-exp, upper bound:** `β⁻¹ log ∑ₐ exp (β f a) ≤ β⁻¹ log |α| + max_a f a` for `β > 0`. -/
theorem inv_mul_log_sum_exp_le (hβ : 0 < β) (f : α → ℝ) :
    β⁻¹ * Real.log (∑ a, Real.exp (β * f a)) ≤ β⁻¹ * Real.log (Fintype.card α) + f.max := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : ∑ a, Real.exp (β * f a) ≤ Fintype.card α * Real.exp (β * f.max) := by
    calc ∑ a, Real.exp (β * f a) ≤ ∑ _a : α, Real.exp (β * f.max) :=
          Finset.sum_le_sum fun a _ =>
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (f.le_max a) hβ.le)
      _ = Fintype.card α * Real.exp (β * f.max) := by simp
  have hpos : 0 < ∑ a, Real.exp (β * f a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  calc β⁻¹ * Real.log (∑ a, Real.exp (β * f a))
      ≤ β⁻¹ * Real.log (Fintype.card α * Real.exp (β * f.max)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hpos hsum) (inv_nonneg.2 hβ.le)
    _ = β⁻¹ * Real.log (Fintype.card α) + f.max := by
        rw [Real.log_mul hcard (Real.exp_pos _).ne', Real.log_exp, mul_add,
          inv_mul_cancel_left₀ hβ.ne']

/-- The smooth approximation error: `|β⁻¹ log ∑ₐ exp (β f a) - max_a f a| ≤ β⁻¹ log |α|`. -/
theorem abs_inv_mul_log_sum_exp_sub_max_le (hβ : 0 < β) (f : α → ℝ) :
    |β⁻¹ * Real.log (∑ a, Real.exp (β * f a)) - f.max| ≤ β⁻¹ * Real.log (Fintype.card α) := by
  have hlog : 0 ≤ β⁻¹ * Real.log (Fintype.card α) :=
    mul_nonneg (inv_nonneg.2 hβ.le) (Real.log_natCast_nonneg _)
  exact abs_le.2 ⟨by linarith [max_le_inv_mul_log_sum_exp hβ f],
    by linarith [inv_mul_log_sum_exp_le hβ f]⟩

end Deterministic

section Random

variable {α : Type*} [Fintype α] [Nonempty α] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {H : Ω → α → ℝ} {β : ℝ}

/-- The maximum of a random energy landscape with integrable coordinates is integrable, since
`|max_a H a| ≤ ∑ₐ |H a|`. -/
theorem integrable_max (hmeas : ∀ a, Measurable fun ω => H ω a)
    (hint : ∀ a, Integrable (fun ω => H ω a) μ) : Integrable (fun ω => (H ω).max) μ := by
  have hm : Measurable fun ω => (H ω).max :=
    measurable_max.comp (measurable_pi_iff.2 hmeas)
  refine Integrable.mono' (g := fun ω => ∑ b, |H ω b|)
    (integrable_finsetSum univ fun a _ => (hint a).abs) hm.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hle : ∀ a, |H ω a| ≤ ∑ b, |H ω b| := fun a =>
    Finset.single_le_sum (f := fun b => |H ω b|) (fun _ _ => abs_nonneg _) (mem_univ a)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [neg_abs_le (H ω a₀), (H ω).le_max a₀, hle a₀],
    Finset.sup'_le _ _ fun a _ => (le_abs_self _).trans (hle a)⟩

omit [Nonempty α] in
/-- The log-partition function of a random energy landscape with measurable coordinates is
measurable. -/
theorem measurable_log_sum_exp (hmeas : ∀ a, Measurable fun ω => H ω a) (β : ℝ) :
    Measurable fun ω => Real.log (∑ a, Real.exp (β * H ω a)) :=
  (Finset.measurable_sum _ fun a _ => ((hmeas a).const_mul β).exp).log

/-- The log-partition function of a random energy landscape with integrable coordinates is
integrable for `β > 0`, since `|log Z| ≤ β |max H| + log |α|`. -/
theorem integrable_log_sum_exp [IsFiniteMeasure μ] (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    Integrable (fun ω => Real.log (∑ a, Real.exp (β * H ω a))) μ := by
  refine Integrable.mono' (((integrable_max hmeas hint).abs.const_mul β).add
    (integrable_const (Real.log (Fintype.card α))))
    (measurable_log_sum_exp hmeas β).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h := abs_inv_mul_log_sum_exp_sub_max_le hβ (H ω)
  have hX : |β⁻¹ * Real.log (∑ a, Real.exp (β * H ω a))| ≤ |(H ω).max| +
      β⁻¹ * Real.log (Fintype.card α) := by
    linarith [abs_sub_abs_le_abs_sub (β⁻¹ * Real.log (∑ a, Real.exp (β * H ω a))) (H ω).max]
  rw [Real.norm_eq_abs]
  calc |Real.log (∑ a, Real.exp (β * H ω a))|
      = β * |β⁻¹ * Real.log (∑ a, Real.exp (β * H ω a))| := by
        rw [abs_mul, abs_inv, abs_of_pos hβ, mul_inv_cancel_left₀ hβ.ne']
    _ ≤ β * (|(H ω).max| + β⁻¹ * Real.log (Fintype.card α)) :=
        mul_le_mul_of_nonneg_left hX hβ.le
    _ = β * |(H ω).max| + Real.log (Fintype.card α) := by
        rw [mul_add, mul_inv_cancel_left₀ hβ.ne']

/-- A finite log-partition function of an affine finite Gaussian family is integrable.
The deterministic offsets are arbitrary, so this is reusable for external fields as well as
for Gaussian Hamiltonians. -/
theorem integrable_log_sum_exp_linear_gaussian {κ : Type*} [Fintype κ]
    (a : α → κ → ℝ) (d : α → ℝ) :
    Integrable (fun g : κ → ℝ =>
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x)))
      (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have hm : ∀ x, Measurable fun g : κ → ℝ => a x ⬝ᵥ g + d x := by
    intro x
    fun_prop
  have hi : ∀ x, Integrable (fun g : κ → ℝ => a x ⬝ᵥ g + d x)
      (Measure.pi fun _ : κ => gaussianReal 0 1) := by
    intro x
    refine (((ProbabilityTheory.hasGaussianLaw_dotProduct_family a).eval x).integrable.add
      (integrable_const (d x))).congr ?_
    exact ae_of_all _ fun g => by simp only [Pi.add_apply]
  simpa only [one_mul] using integrable_log_sum_exp one_pos hm hi

/-- A finite log-partition function of an affine family of two independent Gaussian blocks is
integrable.  This is the product-space counterpart of `integrable_log_sum_exp`; it keeps the
configuration type and both coefficient arrays arbitrary. -/
theorem integrable_log_sum_exp_linear_gaussian_prod {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (a : α → κ₁ → ℝ) (b : α → κ₂ → ℝ) (d : α → ℝ) :
    Integrable (fun q : (κ₁ → ℝ) × (κ₂ → ℝ) =>
      Real.log (∑ x, Real.exp (a x ⬝ᵥ q.1 + b x ⬝ᵥ q.2 + d x)))
      ((Measure.pi fun _ : κ₁ => gaussianReal 0 1).prod
        (Measure.pi fun _ : κ₂ => gaussianReal 0 1)) := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : κ₁ ⊕ κ₂ => ℝ) (fun _ => gaussianReal 0 1)
  have h := integrable_log_sum_exp_linear_gaussian
    (fun x => Sum.elim (a x) (b x)) d
  refine (hmp.integrable_comp_of_integrable h).congr (ae_of_all _ fun q => ?_)
  simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  congr 3
  funext x
  simp [dotProduct, Fintype.sum_sum_type]

variable [IsProbabilityMeasure μ]

/-- **Smooth approximation, lower bound, in expectation:**
`𝔼 max_a H a ≤ β⁻¹ 𝔼 log ∑ₐ exp (β H a)` for `β > 0`. -/
theorem integral_max_le_inv_mul_integral_log_sum_exp (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    ∫ ω, (H ω).max ∂μ ≤ β⁻¹ * ∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono (integrable_max hmeas hint)
    ((integrable_log_sum_exp hβ hmeas hint).const_mul _)
    fun ω => max_le_inv_mul_log_sum_exp hβ (H ω)

/-- **Smooth approximation, upper bound, in expectation:**
`β⁻¹ 𝔼 log ∑ₐ exp (β H a) ≤ β⁻¹ log |α| + 𝔼 max_a H a` for `β > 0`. -/
theorem inv_mul_integral_log_sum_exp_le (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    β⁻¹ * ∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ ≤
      β⁻¹ * Real.log (Fintype.card α) + ∫ ω, (H ω).max ∂μ := by
  rw [← integral_const_mul]
  calc _ ≤ ∫ ω, (β⁻¹ * Real.log (Fintype.card α) + (H ω).max) ∂μ :=
        integral_mono ((integrable_log_sum_exp hβ hmeas hint).const_mul _)
          ((integrable_const _).add (integrable_max hmeas hint))
          fun ω => inv_mul_log_sum_exp_le hβ (H ω)
    _ = _ := by rw [integral_add (integrable_const _) (integrable_max hmeas hint)]; simp

/-- **Smooth approximation error in expectation:**
`|β⁻¹ 𝔼 log ∑ₐ exp (β H a) - 𝔼 max_a H a| ≤ β⁻¹ log |α|`. -/
theorem abs_inv_mul_integral_log_sum_exp_sub_integral_max_le (hβ : 0 < β)
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    |β⁻¹ * ∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ - ∫ ω, (H ω).max ∂μ| ≤
      β⁻¹ * Real.log (Fintype.card α) := by
  have hlog : 0 ≤ β⁻¹ * Real.log (Fintype.card α) :=
    mul_nonneg (inv_nonneg.2 hβ.le) (Real.log_natCast_nonneg _)
  exact abs_le.2 ⟨by linarith [integral_max_le_inv_mul_integral_log_sum_exp hβ hmeas hint],
    by linarith [inv_mul_integral_log_sum_exp_le hβ hmeas hint]⟩

end Random

section Hypercube

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Ω → (ι → ℤˣ) → ℝ} {β : ℝ}

/-- The entropy of the hypercube: `log |{-1, 1}^ι| = |ι| log 2`. -/
lemma log_card_spin_configurations :
    Real.log (Fintype.card (ι → ℤˣ)) = Fintype.card ι * Real.log 2 := by
  rw [card_spin_configurations, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]

/-- **Smooth approximation sandwich** ([Panchenko, 2013, Eq. (1.7)]). For a random energy
`H : Ω → (ι → ℤˣ) → ℝ` on the hypercube with integrable coordinates and `β > 0`,
`N⁻¹ 𝔼 max_σ H(σ) ≤ (N β)⁻¹ 𝔼 log Z(β) ≤ log 2 / β + N⁻¹ 𝔼 max_σ H(σ)`, where
`Z(β) = ∑_σ exp (β H(σ))`, `N = |ι|` and `|{-1, 1}^ι| = 2 ^ N`. -/
theorem smooth_approximation_sandwich (hβ : 0 < β) (hmeas : ∀ σ, Measurable fun ω => H ω σ)
    (hint : ∀ σ, Integrable (fun ω => H ω σ) μ) :
    (Fintype.card ι : ℝ)⁻¹ * ∫ ω, (H ω).max ∂μ ≤
        ((Fintype.card ι : ℝ) * β)⁻¹ * ∫ ω, Real.log (∑ σ, Real.exp (β * H ω σ)) ∂μ ∧
      ((Fintype.card ι : ℝ) * β)⁻¹ * ∫ ω, Real.log (∑ σ, Real.exp (β * H ω σ)) ∂μ ≤
        Real.log 2 / β + (Fintype.card ι : ℝ)⁻¹ * ∫ ω, (H ω).max ∂μ := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp only [h0, Nat.cast_zero, inv_zero, zero_mul]
    exact ⟨le_rfl, by rw [add_zero]; exact div_nonneg (Real.log_pos one_lt_two).le hβ.le⟩
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hpos
  have h1 := integral_max_le_inv_mul_integral_log_sum_exp hβ hmeas hint
  have h2 := inv_mul_integral_log_sum_exp_le hβ hmeas hint
  rw [log_card_spin_configurations] at h2
  rw [mul_inv]
  refine ⟨?_, ?_⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hN.le)
  · calc _ = (Fintype.card ι : ℝ)⁻¹ * (β⁻¹ * ∫ ω, Real.log (∑ σ, Real.exp (β * H ω σ)) ∂μ) :=
          mul_assoc _ _ _
      _ ≤ (Fintype.card ι : ℝ)⁻¹ * (β⁻¹ * (Fintype.card ι * Real.log 2) + ∫ ω, (H ω).max ∂μ) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hN.le)
      _ = _ := by field_simp

/-- **Smooth approximation error bound:** the normalized free energy at inverse temperature `β`
approximates the normalized ground-state energy up to `log 2 / β`,
`|(N β)⁻¹ 𝔼 log Z(β) - N⁻¹ 𝔼 max_σ H(σ)| ≤ log 2 / β`. -/
theorem smooth_approximation_error_bound (hβ : 0 < β) (hmeas : ∀ σ, Measurable fun ω => H ω σ)
    (hint : ∀ σ, Integrable (fun ω => H ω σ) μ) :
    |((Fintype.card ι : ℝ) * β)⁻¹ * ∫ ω, Real.log (∑ σ, Real.exp (β * H ω σ)) ∂μ -
        (Fintype.card ι : ℝ)⁻¹ * ∫ ω, (H ω).max ∂μ| ≤ Real.log 2 / β := by
  obtain ⟨h1, h2⟩ := smooth_approximation_sandwich hβ hmeas hint
  exact abs_le.2 ⟨by linarith [div_nonneg (Real.log_pos one_lt_two).le hβ.le], by linarith⟩

end Hypercube

section SK

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ℝ}

omit [DecidableEq ι] in
/-- Each coordinate `G ↦ (√N)⁻¹ * (σ ⬝ᵥ (G *ᵥ σ))` of the SK Hamiltonian is measurable and
integrable under the Gaussian disorder; this discharges the hypotheses of the generic layers. -/
lemma sk_measurable_integrable (σ : ι → ℤˣ) :
    Measurable (fun G : ι → ι → ℝ => (Real.sqrt (Fintype.card ι))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ)))) ∧
    Integrable (fun G : ι → ι → ℝ => (Real.sqrt (Fintype.card ι))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine ⟨?_, ((memLp_linearForm_gaussianInit _ _).integrable one_le_two).const_mul _⟩
  simp only [dotProduct_mulVec_of_eq_sum]
  fun_prop

/-- **Smooth approximation sandwich for the SK model** ([Panchenko, 2013, Eq. (1.7)]): for the
Hamiltonian `H G σ = (√N)⁻¹ * (σ ⬝ᵥ (G *ᵥ σ))` with standard Gaussian disorder `G`, the
free energy `(N β)⁻¹ 𝔼 log Z_N(β)` lies between `N⁻¹ 𝔼 max_σ H_N(σ)` and
`log 2 / β + N⁻¹ 𝔼 max_σ H_N(σ)`.  The Hamiltonian is passed with its defining equation `hH`
instead of being named. -/
theorem sk_smooth_approximation_sandwich (H : (ι → ι → ℝ) → (ι → ℤˣ) → ℝ)
    (hH : ∀ G σ, H G σ = (Real.sqrt (Fintype.card ι))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ)))) (hβ : 0 < β) :
    (Fintype.card ι : ℝ)⁻¹ * ∫ G, (H G).max
          ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1) ≤
        ((Fintype.card ι : ℝ) * β)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H G σ))
          ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1) ∧
      ((Fintype.card ι : ℝ) * β)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H G σ))
          ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1) ≤
        Real.log 2 / β + (Fintype.card ι : ℝ)⁻¹ * ∫ G, (H G).max
          ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1) := by
  obtain rfl : H = fun G σ => (Real.sqrt (Fintype.card ι))⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))) :=
    funext fun G => funext (hH G)
  exact smooth_approximation_sandwich hβ (fun σ => (sk_measurable_integrable σ).1)
    (fun σ => (sk_measurable_integrable σ).2)

/-- **Smooth approximation error bound for the SK model:**
`|(N β)⁻¹ 𝔼 log Z_N(β) - N⁻¹ 𝔼 max_σ H_N(σ)| ≤ log 2 / β`. -/
theorem sk_smooth_approximation_error_bound (H : (ι → ι → ℝ) → (ι → ℤˣ) → ℝ)
    (hH : ∀ G σ, H G σ = (Real.sqrt (Fintype.card ι))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ)))) (hβ : 0 < β) :
    |((Fintype.card ι : ℝ) * β)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H G σ))
          ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1) -
        (Fintype.card ι : ℝ)⁻¹ * ∫ G, (H G).max
          ∂(Measure.pi fun _ : ι => Measure.pi fun _ : ι => gaussianReal 0 1)| ≤
      Real.log 2 / β := by
  obtain rfl : H = fun G σ => (Real.sqrt (Fintype.card ι))⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))) :=
    funext fun G => funext (hH G)
  exact smooth_approximation_error_bound hβ (fun σ => (sk_measurable_integrable σ).1)
    (fun σ => (sk_measurable_integrable σ).2)

end SK

end SpinGlasses
