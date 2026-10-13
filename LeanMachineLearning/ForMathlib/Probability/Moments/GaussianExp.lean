/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Independence.IntegralTsumMul
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector

/-!
# Exponential moments of Gaussian random variables

A random variable `Z` with `HasGaussianLaw` has `exp (t Z)` integrable with
`𝔼 exp (t Z) = exp (t 𝔼 Z + t² Var Z / 2)` (`integral_exp_mul_of_hasGaussianLaw`).  Together with
Hölder's inequality this gives the Cauchy--Schwarz bound
`‖X exp Z‖₁ ≤ √a exp v` for a centered Gaussian `Z` with `𝔼 Z² ≤ v` and `𝔼 X² ≤ a`
(`eLpNorm_one_mul_exp_le`), which controls the Gibbs weights of a Gaussian energy in
`SpinGlasses/GaussianIBPCountable.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A Gaussian variable has the corresponding Gaussian law. -/
theorem hasGaussianLaw_hasLaw {Z : Ω → ℝ} (hZ : HasGaussianLaw Z P) :
    HasLaw Z (gaussianReal P[Z] Var[Z; P].toNNReal) P :=
  ⟨hZ.aemeasurable, hZ.map_eq_gaussianReal⟩

/-- **Exponential moments of a Gaussian variable:** `𝔼 exp (t Z) = exp (t 𝔼 Z + t² Var Z / 2)`. -/
theorem integral_exp_mul_of_hasGaussianLaw {Z : Ω → ℝ} (hZ : HasGaussianLaw Z P) (t : ℝ) :
    ∫ ω, Real.exp (t * Z ω) ∂P = Real.exp (t * P[Z] + Var[Z; P] * t ^ 2 / 2) := by
  have h := mgf_gaussianReal (hasGaussianLaw_hasLaw hZ) t
  have hv : ((Var[Z; P].toNNReal : ℝ≥0) : ℝ) = Var[Z; P] :=
    Real.coe_toNNReal _ (variance_nonneg _ _)
  rw [hv] at h
  rw [mul_comm t]
  exact h

/-- `exp (t Z)` is integrable for a Gaussian variable `Z`. -/
theorem integrable_exp_mul_of_hasGaussianLaw {Z : Ω → ℝ} (hZ : HasGaussianLaw Z P) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * Z ω)) P := by
  have hP := hZ.isProbabilityMeasure
  have := integrable_exp_mul_gaussianReal (μ := P[Z]) (v := Var[Z; P].toNNReal) t
  rw [← hZ.map_eq_gaussianReal] at this
  exact (integrable_map_measure (by fun_prop) hZ.aemeasurable).1 this

/-- **Cauchy–Schwarz bound for a variable times the exponential of a Gaussian:**
if `Z` is a centered Gaussian with `𝔼 Z² ≤ v` and `𝔼 X² ≤ a`, then
`‖X exp Z‖₁ ≤ √a exp v`. -/
theorem eLpNorm_one_mul_exp_le {X Z : Ω → ℝ} (hZ : HasGaussianLaw Z P) (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hX : MemLp X 2 P) {a v : ℝ} (ha : ∫ ω, X ω ^ 2 ∂P ≤ a) (hv : ∫ ω, Z ω ^ 2 ∂P ≤ v) :
    eLpNorm (fun ω => X ω * Real.exp (Z ω)) 1 P ≤ ENNReal.ofReal (√a * Real.exp v) := by
  have hP := hZ.isProbabilityMeasure
  have ha0 : 0 ≤ a := (integral_nonneg fun _ => sq_nonneg _).trans ha
  have hvar : Var[Z; P] = ∫ ω, Z ω ^ 2 ∂P := variance_of_integral_eq_zero hZ.aemeasurable hZ0
  have hexp2 : ∀ ω, Real.exp (Z ω) ^ 2 = Real.exp (2 * Z ω) := fun ω => by
    rw [← Real.exp_nat_mul]; norm_num
  have hE : MemLp (fun ω => Real.exp (Z ω)) 2 P := by
    refine (memLp_two_iff_integrable_sq
      (Real.measurable_exp.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable).2 ?_
    exact (integrable_exp_mul_of_hasGaussianLaw hZ 2).congr
      (ae_of_all _ fun ω => (hexp2 ω).symm)
  have hEn : eLpNorm (fun ω => Real.exp (Z ω)) 2 P ≤ ENNReal.ofReal (Real.exp v) := by
    refine eLpNorm_two_le_ofReal_of_integral_sq_le hE (Real.exp_pos _).le ?_
    rw [integral_congr_ae (ae_of_all _ hexp2), integral_exp_mul_of_hasGaussianLaw hZ 2, hZ0, hvar,
      ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith
  have hXn : eLpNorm X 2 P ≤ ENNReal.ofReal (√a) := by
    refine eLpNorm_two_le_ofReal_of_integral_sq_le hX (Real.sqrt_nonneg _) ?_
    rw [Real.sq_sqrt ha0]; exact ha
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := P) (p := 2) (q := 2) (r := 1) hE.1 hX.1
    (hpqr := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩)
  calc eLpNorm (fun ω => X ω * Real.exp (Z ω)) 1 P
      ≤ eLpNorm X 2 P * eLpNorm (fun ω => Real.exp (Z ω)) 2 P := by
        exact h
    _ ≤ ENNReal.ofReal (√a) * ENNReal.ofReal (Real.exp v) := mul_le_mul' hXn hEn
    _ = ENNReal.ofReal (√a * Real.exp v) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm

/-- **A Gaussian-weighted series with summable coefficients is a.s. summable and integrable:**
if `Z b` are centered Gaussians with `𝔼 (Z b)² ≤ v` and `X b` satisfy `𝔼 (X b)² ≤ a`, then for
`G ≥ 0` summable, `∑_b G b |X b| exp (Z b)` converges a.s. and is integrable. -/
theorem ae_summable_and_integrable_tsum_mul_exp [IsProbabilityMeasure P] {κ : Type*}
    [Countable κ] {X Z : κ → Ω → ℝ} {G : κ → ℝ} (hG0 : ∀ b, 0 ≤ G b) (hG : Summable G)
    (hZ : ∀ b, HasGaussianLaw (Z b) P) (hZ0 : ∀ b, ∫ ω, Z b ω ∂P = 0)
    (hX : ∀ b, MemLp (X b) 2 P) {a v : ℝ}
    (ha : ∀ b, ∫ ω, X b ω ^ 2 ∂P ≤ a) (hv : ∀ b, ∫ ω, Z b ω ^ 2 ∂P ≤ v) :
    (∀ᵐ ω ∂P, Summable fun b => G b * (|X b ω| * Real.exp (Z b ω))) ∧
      Integrable (fun ω => ∑' b, G b * (|X b ω| * Real.exp (Z b ω))) P := by
  set K : ℝ := √a * Real.exp v with hK
  set f : κ → Ω → ℝ := fun b ω => G b * (|X b ω| * Real.exp (Z b ω)) with hf
  have hfm : ∀ b, AEStronglyMeasurable (f b) P := fun b =>
    (((hX b).1.norm.mul (Real.measurable_exp.comp_aemeasurable
      (hZ b).aemeasurable).aestronglyMeasurable).const_mul (G b))
  have hnorm : ∀ b, eLpNorm (f b) 1 P ≤ ENNReal.ofReal (G b) * ENNReal.ofReal K := fun b => by
    have h1 := eLpNorm_one_mul_exp_le (hZ b) (hZ0 b) (hX b).abs (a := a) (v := v)
      (by simpa using ha b) (hv b)
    have : f b = G b • fun ω => |X b ω| * Real.exp (Z b ω) := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal (hG0 b)]
    exact mul_le_mul' le_rfl h1
  have hsum : ∑' b, eLpNorm (f b) 1 P ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hnorm)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hG0 hG]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨?_, integrable_tsum_of_tsum_eLpNorm_ne_top le_rfl hfm hsum⟩
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top le_rfl hfm hsum] with ω hω
  refine hω.congr fun b => ?_
  simp only [hf, Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (hG0 b) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))

end ProbabilityTheory
