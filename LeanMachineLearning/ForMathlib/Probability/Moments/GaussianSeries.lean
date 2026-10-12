/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import LeanMachineLearning.ForMathlib.Probability.Independence.IntegralTsumMul
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm

/-!
# Series of Gaussian linear forms

Let `g p` (for `p` in a countable index type `τ`) be independent vectors with i.i.d. standard
Gaussian coordinates, `g p : κ p → ℝ`, i.e. `g ∼ infinitePi fun p => pi fun _ : κ p => 𝒩(0, 1)`.
For coefficient vectors `a p : κ p → ℝ` with `∑ₚ ‖a p‖ < ∞`, the Gaussian series
`H_a(g) = ∑ₚ a p ⬝ᵥ g p` converges absolutely almost surely and in `L¹`, is centered, and has
covariance `𝔼[H_a H_b] = ∑ₚ a p ⬝ᵥ b p`.  The mixed `p`-spin Hamiltonians of
`SpinGlasses/MixedPSpin.lean` are of this form, with `κ p = (Fin p → ι)`.

## Main declarations

* `ProbabilityTheory.integral_tsum_dotProduct_mul_tsum_dotProduct`: the covariance formula.
* `ProbabilityTheory.integrable_tsum_dotProduct`, `ProbabilityTheory.measurable_tsum_dotProduct`:
  integrability and measurability of the series.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace ProbabilityTheory

variable {τ : Type*} [Countable τ] {κ : τ → Type*} [∀ p, Fintype (κ p)]

/-- The disorder law: independent vectors with i.i.d. standard Gaussian coordinates. -/
local notation "gaussianField" =>
  Measure.infinitePi fun p => Measure.pi fun _ : κ p => gaussianReal 0 1

omit [Countable τ] in
private lemma measurable_dotProduct (p : τ) (c : κ p → ℝ) :
    Measurable fun g : κ p → ℝ => c ⬝ᵥ g := by
  simp only [dotProduct]
  fun_prop

omit [Countable τ] in
/-- A function of a single coordinate block integrates as under the marginal law. -/
private lemma integral_comp_eval (p : τ) {F : (κ p → ℝ) → ℝ}
    (hF : AEStronglyMeasurable F (Measure.pi fun _ : κ p => gaussianReal 0 1)) :
    ∫ g : ∀ p, κ p → ℝ, F (g p) ∂gaussianField =
      ∫ g, F g ∂(Measure.pi fun _ : κ p => gaussianReal 0 1) := by
  have hmp := measurePreserving_eval_infinitePi
    (fun p => Measure.pi fun _ : κ p => gaussianReal 0 1) p
  calc _ = ∫ x, F x ∂(Measure.map (Function.eval p) gaussianField) :=
        (integral_map (measurable_pi_apply p).aemeasurable (by rwa [hmp.map_eq])).symm
    _ = _ := by rw [hmp.map_eq]

omit [Countable τ] in
private lemma memLp_coord (p : τ) (a : κ p → ℝ) :
    MemLp (fun g : ∀ p, κ p → ℝ => a ⬝ᵥ g p) 2 gaussianField :=
  (memLp_dotProduct_pi_gaussianReal a).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun p => Measure.pi fun _ : κ p => gaussianReal 0 1) p)

omit [Countable τ] in
private lemma integral_coord_mul (p : τ) (a b : κ p → ℝ) :
    ∫ g : ∀ p, κ p → ℝ, (a ⬝ᵥ g p) * (b ⬝ᵥ g p) ∂gaussianField = a ⬝ᵥ b := by
  rw [integral_comp_eval p (F := fun g => (a ⬝ᵥ g) * (b ⬝ᵥ g))
    ((measurable_dotProduct p a).mul (measurable_dotProduct p b)).aestronglyMeasurable,
    integral_dotProduct_mul_dotProduct_pi_gaussianReal]

omit [Countable τ] in
private lemma tsum_eLpNorm_coord_ne_top {a : ∀ p, κ p → ℝ}
    (ha : Summable fun p => Real.sqrt (a p ⬝ᵥ a p)) :
    ∑' p, eLpNorm (fun g : ∀ p, κ p → ℝ => a p ⬝ᵥ g p) 2 gaussianField ≠ ∞ := by
  have hle : ∀ p, eLpNorm (fun g : ∀ p, κ p → ℝ => a p ⬝ᵥ g p) 2 gaussianField ≤
      ENNReal.ofReal (Real.sqrt (a p ⬝ᵥ a p)) := fun p =>
    eLpNorm_two_le_ofReal_of_integral_sq_le (memLp_coord p (a p)) (Real.sqrt_nonneg _)
      (by
        have hnn : 0 ≤ a p ⬝ᵥ a p := Finset.sum_nonneg fun i _ => mul_self_nonneg (a p i)
        rw [Real.sq_sqrt hnn]
        simpa [sq] using (integral_coord_mul p (a p) (a p)).le)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.sqrt_nonneg _) ha]
  exact ENNReal.ofReal_ne_top

/-- **Covariance of Gaussian series.** For coefficient vectors `a p`, `b p` with
`∑ₚ ‖a p‖ < ∞` and `∑ₚ ‖b p‖ < ∞`,
`𝔼[(∑ₚ a p ⬝ᵥ g p)(∑ₚ b p ⬝ᵥ g p)] = ∑ₚ a p ⬝ᵥ b p`. -/
theorem integral_tsum_dotProduct_mul_tsum_dotProduct {a b : ∀ p, κ p → ℝ}
    (ha : Summable fun p => Real.sqrt (a p ⬝ᵥ a p))
    (hb : Summable fun p => Real.sqrt (b p ⬝ᵥ b p)) :
    ∫ g : ∀ p, κ p → ℝ, (∑' p, a p ⬝ᵥ g p) * (∑' p, b p ⬝ᵥ g p) ∂gaussianField =
      ∑' p, a p ⬝ᵥ b p := by
  have hind : ∀ p q, p ≠ q → IndepFun (fun g : ∀ p, κ p → ℝ => a p ⬝ᵥ g p)
      (fun g : ∀ p, κ p → ℝ => b q ⬝ᵥ g q) gaussianField := fun p q hpq => by
    have h := (iIndepFun_infinitePi (P := fun p => Measure.pi fun _ : κ p => gaussianReal 0 1)
      (X := fun p (g : κ p → ℝ) => (a p ⬝ᵥ g, b p ⬝ᵥ g))
      fun p => (measurable_dotProduct p (a p)).prodMk (measurable_dotProduct p (b p))).indepFun hpq
    exact h.comp measurable_fst measurable_snd
  have hmain := integral_tsum_mul_tsum_of_indepFun (μ := gaussianField)
    (X := fun p (g : ∀ p, κ p → ℝ) => a p ⬝ᵥ g p) (Y := fun p (g : ∀ p, κ p → ℝ) => b p ⬝ᵥ g p)
    (fun p => memLp_coord p (a p)) (fun p => memLp_coord p (b p))
    (tsum_eLpNorm_coord_ne_top ha) (tsum_eLpNorm_coord_ne_top hb) hind fun p => by
      rw [integral_comp_eval p (F := fun g => a p ⬝ᵥ g)
        (measurable_dotProduct p (a p)).aestronglyMeasurable, integral_dotProduct_pi_gaussianReal]
  rw [hmain]
  exact tsum_congr fun p => integral_coord_mul p (a p) (b p)

/-- The Gaussian series is measurable. -/
theorem measurable_tsum_dotProduct (a : ∀ p, κ p → ℝ) :
    Measurable fun g : ∀ p, κ p → ℝ => ∑' p, a p ⬝ᵥ g p :=
  Measurable.tsum fun p => (measurable_dotProduct p (a p)).comp (measurable_pi_apply p)

/-- The Gaussian series is integrable when `∑ₚ ‖a p‖ < ∞`. -/
theorem integrable_tsum_dotProduct {a : ∀ p, κ p → ℝ}
    (ha : Summable fun p => Real.sqrt (a p ⬝ᵥ a p)) :
    Integrable (fun g : ∀ p, κ p → ℝ => ∑' p, a p ⬝ᵥ g p) gaussianField :=
  integrable_tsum_of_tsum_eLpNorm_two_ne_top (fun p => (memLp_coord p (a p)).1)
    (tsum_eLpNorm_coord_ne_top ha)

end ProbabilityTheory
