/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianExp
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianSeries
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The law of a Gaussian series

Let `g p`, `p ∈ ℕ`, be independent vectors with i.i.d. standard Gaussian coordinates
(`g ∼ infinitePi fun p => pi fun _ => 𝒩(0, 1)`) and `a p` coefficient vectors with
`∑ₚ ‖a p‖ < ∞`.  Then the series `H_a(g) = ∑ₚ a p ⬝ᵥ g p` is exactly Gaussian,
`H_a ∼ 𝒩(0, ∑ₚ ‖a p‖²)`, and finitely many such series form a Gaussian vector.  (The partial sums
are sums of independent Gaussians; the series is their almost sure limit, and the characteristic
function passes to the limit by dominated convergence.)  This is the missing input that makes the
mixed `p`-spin Hamiltonian of `SpinGlasses/MixedPSpin.lean` a Gaussian process.

## Main declarations

* `ProbabilityTheory.map_tsum_dotProduct_eq_gaussianReal`: the law of a single Gaussian series.
* `ProbabilityTheory.hasGaussianLaw_tsum_dotProduct`: a finite family of Gaussian series is a
  Gaussian vector.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Matrix Topology ENNReal NNReal

namespace ProbabilityTheory

variable {ρ : ℕ → Type*} [∀ p, Fintype (ρ p)]

/-- The disorder law: independent vectors with i.i.d. standard Gaussian coordinates. -/
local notation "gaussianField" =>
  Measure.infinitePi fun p => Measure.pi fun _ : ρ p => gaussianReal 0 1

/-- Each coordinate block `a ⬝ᵥ g p` of the disorder is a Gaussian variable. -/
theorem hasGaussianLaw_coord (p : ℕ) (a : ρ p → ℝ) :
    HasGaussianLaw (fun g : ∀ p, ρ p → ℝ => a ⬝ᵥ g p) gaussianField := by
  let L : (ρ p → ℝ) →L[ℝ] ℝ := ∑ i, a i • ContinuousLinearMap.proj i
  have hL : ∀ x, L x = a ⬝ᵥ x := fun x => by simp [L, dotProduct]
  have hmp := measurePreserving_eval_infinitePi
    (fun p => Measure.pi fun _ : ρ p => gaussianReal 0 1) p
  have := isGaussian_pi_gaussianReal (κ := ρ p)
  refine ⟨((measurable_dotProduct p a).comp (measurable_pi_apply p)).aemeasurable, ?_⟩
  have h : Measure.map (fun g : ∀ p, ρ p → ℝ => a ⬝ᵥ g p) gaussianField =
      (Measure.pi fun _ : ρ p => gaussianReal 0 1).map L := by
    rw [← hmp.map_eq, Measure.map_map L.continuous.measurable (measurable_pi_apply p)]
    congr 1
    exact funext fun g => (hL (g p)).symm
  rw [h]
  infer_instance

/-- The coordinate blocks are independent. -/
theorem iIndepFun_coord (a : ∀ p, ρ p → ℝ) :
    iIndepFun (fun p (g : ∀ p, ρ p → ℝ) => a p ⬝ᵥ g p) gaussianField :=
  iIndepFun_infinitePi (P := fun p => Measure.pi fun _ : ρ p => gaussianReal 0 1)
    (X := fun p (g : ρ p → ℝ) => a p ⬝ᵥ g) fun p => measurable_dotProduct p (a p)

/-- **The law of a partial sum:** `∑_{p < n} a p ⬝ᵥ g p ∼ 𝒩(0, ∑_{p < n} ‖a p‖²)`. -/
theorem map_sum_range_dotProduct (a : ∀ p, ρ p → ℝ) (n : ℕ) :
    Measure.map (fun g : ∀ p, ρ p → ℝ => ∑ p ∈ range n, a p ⬝ᵥ g p) gaussianField =
      gaussianReal 0 (∑ p ∈ range n, a p ⬝ᵥ a p).toNNReal := by
  have hG : HasGaussianLaw (fun g : ∀ p, ρ p → ℝ => ∑ p ∈ range n, a p ⬝ᵥ g p) gaussianField := by
    have := (iIndepFun_coord a).precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
    have h := iIndepFun.hasGaussianLaw_fun_sum
      (X := fun (i : Fin n) (g : ∀ p, ρ p → ℝ) => a i ⬝ᵥ g i)
      (fun i => hasGaussianLaw_coord (i : ℕ) (a i)) this
    simpa [Finset.sum_range] using h
  -- the centered coefficient family `a' p = 1[p < n] a p` has the same series
  set a' : ∀ p, ρ p → ℝ := fun p => if p < n then a p else 0 with ha'
  have hsupp : ∀ p ∉ range n, a' p = 0 := fun p hp => by
    simp [ha', mem_range.not.1 hp]
  have hsum : ∀ g : ∀ p, ρ p → ℝ, ∑ p ∈ range n, a p ⬝ᵥ g p = ∑' p, a' p ⬝ᵥ g p := fun g => by
    rw [tsum_eq_sum (s := range n) fun p hp => by simp [hsupp p hp]]
    exact sum_congr rfl fun p hp => by simp [ha', mem_range.1 hp]
  have hsumm : Summable fun p => Real.sqrt (a' p ⬝ᵥ a' p) :=
    summable_of_ne_finset_zero (s := range n) fun p hp => by simp [hsupp p hp]
  have hmean : ∫ g : ∀ p, ρ p → ℝ, ∑ p ∈ range n, a p ⬝ᵥ g p ∂gaussianField = 0 := by
    rw [integral_finsetSum _ fun p _ => (memLp_coord p (a p)).integrable one_le_two]
    refine sum_eq_zero fun p _ => ?_
    rw [integral_comp_eval p (F := fun g => a p ⬝ᵥ g)
      (measurable_dotProduct p (a p)).aestronglyMeasurable, integral_dotProduct_pi_gaussianReal]
  have hvar : ∫ g : ∀ p, ρ p → ℝ, (∑ p ∈ range n, a p ⬝ᵥ g p) ^ 2 ∂gaussianField =
      ∑ p ∈ range n, a p ⬝ᵥ a p := by
    have h1 : ∑' p, a' p ⬝ᵥ a' p = ∑ p ∈ range n, a p ⬝ᵥ a p := by
      rw [tsum_eq_sum (f := fun p => a' p ⬝ᵥ a' p) (s := range n) fun p hp => by
        simp [hsupp p hp]]
      refine sum_congr rfl fun p hp => ?_
      have hpn : p < n := mem_range.1 hp
      simp [ha', hpn]
    have e : ∀ g : ∀ p, ρ p → ℝ, (∑ p ∈ range n, a p ⬝ᵥ g p) ^ 2 =
        (∑' p, a' p ⬝ᵥ g p) * ∑' p, a' p ⬝ᵥ g p := fun g => by rw [hsum g, sq]
    simp only [e]
    rw [integral_tsum_dotProduct_mul_tsum_dotProduct hsumm hsumm, h1]
  have h := (hasGaussianLaw_hasLaw hG).map_eq
  rwa [hmean, variance_of_integral_eq_zero hG.aemeasurable hmean, hvar] at h

/-- `∑ₚ ‖a p‖ < ∞` implies `∑ₚ ‖a p‖² < ∞`. -/
theorem summable_dotProduct_self {a : ∀ p, ρ p → ℝ}
    (ha : Summable fun p => Real.sqrt (a p ⬝ᵥ a p)) : Summable fun p => a p ⬝ᵥ a p := by
  have hnn : ∀ p, 0 ≤ a p ⬝ᵥ a p := fun p => Finset.sum_nonneg fun i _ => mul_self_nonneg (a p i)
  refine Summable.of_nonneg_of_le hnn (fun p => ?_) (ha.mul_left (∑' q, Real.sqrt (a q ⬝ᵥ a q)))
  calc a p ⬝ᵥ a p = Real.sqrt (a p ⬝ᵥ a p) * Real.sqrt (a p ⬝ᵥ a p) :=
        (Real.mul_self_sqrt (hnn p)).symm
    _ ≤ (∑' q, Real.sqrt (a q ⬝ᵥ a q)) * Real.sqrt (a p ⬝ᵥ a p) :=
        mul_le_mul_of_nonneg_right (ha.le_tsum p fun _ _ => Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)

/-- **The law of a Gaussian series** (an `L²`-limit of independent Gaussians is Gaussian):
for `∑ₚ ‖a p‖ < ∞`, `∑ₚ a p ⬝ᵥ g p ∼ 𝒩(0, ∑ₚ ‖a p‖²)`. -/
theorem map_tsum_dotProduct_eq_gaussianReal {a : ∀ p, ρ p → ℝ}
    (ha : Summable fun p => Real.sqrt (a p ⬝ᵥ a p)) :
    Measure.map (fun g : ∀ p, ρ p → ℝ => ∑' p, a p ⬝ᵥ g p) gaussianField =
      gaussianReal 0 (∑' p, a p ⬝ᵥ a p).toNNReal := by
  have hnn : ∀ p, 0 ≤ a p ⬝ᵥ a p := fun p => Finset.sum_nonneg fun i _ => mul_self_nonneg (a p i)
  have hv : 0 ≤ ∑' p, a p ⬝ᵥ a p := tsum_nonneg hnn
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_gaussianReal, charFun_apply_real,
    integral_map (measurable_tsum_dotProduct a).aemeasurable (by fun_prop)]
  -- the partial sums converge almost surely to the series
  have hae : ∀ᵐ g ∂gaussianField, Tendsto (fun n => ∑ p ∈ range n, a p ⬝ᵥ g p) atTop
      (𝓝 (∑' p, a p ⬝ᵥ g p)) := by
    have := ae_summable_of_tsum_eLpNorm_ne_top (μ := gaussianField)
      (f := fun p (g : ∀ p, ρ p → ℝ) => a p ⬝ᵥ g p)
      (fun p => (memLp_coord p (a p)).1) (by
        refine ne_top_of_le_ne_top (tsum_eLpNorm_coord_ne_top ha) (ENNReal.tsum_le_tsum fun p => ?_)
        exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two (memLp_coord p (a p)).1)
    filter_upwards [this] with g hg using hg.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun n => ∫ g, Complex.exp (t * (∑ p ∈ range n, a p ⬝ᵥ g p) * Complex.I)
      ∂gaussianField) atTop
      (𝓝 (∫ g, Complex.exp (t * (∑' p, a p ⬝ᵥ g p) * Complex.I) ∂gaussianField)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun g => ?_) ?_
    · have : Measurable fun g : ∀ p, ρ p → ℝ => ∑ p ∈ range n, a p ⬝ᵥ g p :=
        Finset.measurable_sum _ fun p _ => (measurable_dotProduct p (a p)).comp
          (measurable_pi_apply p)
      exact (Complex.measurable_exp.comp (((Complex.measurable_ofReal.comp this).const_mul
        (t : ℂ)).mul_const Complex.I)).aestronglyMeasurable
    · simp [Complex.norm_exp]
    · filter_upwards [hae] with g hg
      exact ((Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp hg).const_mul (t : ℂ) |>.mul_const
          Complex.I))
  -- the characteristic function of the partial sums is explicit
  have hS : ∀ n, ∫ g, Complex.exp (t * (∑ p ∈ range n, a p ⬝ᵥ g p) * Complex.I) ∂gaussianField =
      Complex.exp (-((∑ p ∈ range n, a p ⬝ᵥ a p : ℝ) : ℂ) * t ^ 2 / 2) := fun n => by
    have h := congrArg (fun μ => charFun μ t) (map_sum_range_dotProduct a n)
    have hmeas : Measurable fun g : ∀ p, ρ p → ℝ => ∑ p ∈ range n, a p ⬝ᵥ g p :=
      Finset.measurable_sum _ fun p _ => (measurable_dotProduct p (a p)).comp
        (measurable_pi_apply p)
    rw [charFun_gaussianReal, charFun_apply_real,
      integral_map hmeas.aemeasurable (by fun_prop)] at h
    rw [h]
    have hn : 0 ≤ ∑ p ∈ range n, a p ⬝ᵥ a p := sum_nonneg fun p _ => hnn p
    simp only [Real.coe_toNNReal _ hn]
    congr 1
    push_cast
    ring
  have hv' : Tendsto (fun n => ∑ p ∈ range n, a p ⬝ᵥ a p) atTop (𝓝 (∑' p, a p ⬝ᵥ a p)) :=
    (summable_dotProduct_self ha).hasSum.tendsto_sum_nat
  have hlim2 : Tendsto (fun n => Complex.exp (-((∑ p ∈ range n, a p ⬝ᵥ a p : ℝ) : ℂ) * t ^ 2 / 2))
      atTop (𝓝 (Complex.exp (-((∑' p, a p ⬝ᵥ a p : ℝ) : ℂ) * t ^ 2 / 2))) :=
    (Complex.continuous_exp.tendsto _).comp
      ((((Complex.continuous_ofReal.tendsto _).comp hv').neg.mul_const _).div_const _)
  simp only [hS] at hlim
  rw [tendsto_nhds_unique hlim hlim2, Real.coe_toNNReal _ hv]
  congr 1
  push_cast
  ring

/-- A Gaussian series is centered. -/
theorem integral_tsum_dotProduct_eq_zero {a : ∀ p, ρ p → ℝ}
    (ha : Summable fun p => Real.sqrt (a p ⬝ᵥ a p)) :
    ∫ g : ∀ p, ρ p → ℝ, ∑' p, a p ⬝ᵥ g p ∂gaussianField = 0 := by
  have h := map_tsum_dotProduct_eq_gaussianReal ha
  have := integral_map (measurable_tsum_dotProduct a).aemeasurable
    (f := id) aestronglyMeasurable_id (μ := gaussianField)
  rw [h] at this
  simp only [id] at this
  rw [integral_id_gaussianReal] at this
  exact this.symm

/-- Minkowski for the Euclidean norm `√(x ⬝ᵥ x)`. -/
theorem sqrt_dotProduct_self_sum_le {κ S : Type*} [Fintype κ] (s : Finset S) (v : S → κ → ℝ) :
    Real.sqrt ((∑ i ∈ s, v i) ⬝ᵥ (∑ i ∈ s, v i)) ≤ ∑ i ∈ s, Real.sqrt (v i ⬝ᵥ v i) := by
  have key : ∀ x : κ → ℝ, Real.sqrt (x ⬝ᵥ x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ κ)‖ :=
    fun x => by simp [EuclideanSpace.norm_eq, dotProduct, sq]
  simp only [key]
  have : (WithLp.toLp 2 (∑ i ∈ s, v i) : EuclideanSpace ℝ κ) =
      ∑ i ∈ s, (WithLp.toLp 2 (v i) : EuclideanSpace ℝ κ) := by
    ext j; simp
  rw [this]
  exact norm_sum_le _ _

/-- **A finite family of Gaussian series is a Gaussian vector:** if `∑ₚ ‖a s p‖ < ∞` for each `s`
then `g ↦ (∑ₚ a s p ⬝ᵥ g p)_s` has a Gaussian law.  Every linear functional of the vector is again
a Gaussian series, with coefficients the corresponding linear combinations. -/
theorem hasGaussianLaw_tsum_dotProduct {S : Type*} [Finite S] {a : S → ∀ p, ρ p → ℝ}
    (ha : ∀ s, Summable fun p => Real.sqrt (a s p ⬝ᵥ a s p)) :
    HasGaussianLaw (fun g (s : S) => ∑' p, a s p ⬝ᵥ g p) gaussianField := by
  have := Fintype.ofFinite S
  classical
  have hm : Measurable fun g : ∀ p, ρ p → ℝ => fun s : S => ∑' p, a s p ⬝ᵥ g p :=
    measurable_pi_iff.2 fun s => measurable_tsum_dotProduct (a s)
  refine ⟨hm.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  -- `L x = ∑ₛ cₛ xₛ`, so `L ∘ X` is the Gaussian series with coefficients `∑ₛ cₛ a s p`
  set c : S → ℝ := fun s => L fun j => if s = j then 1 else 0 with hc
  have hL : ∀ x : S → ℝ, L x = ∑ s, c s * x s := fun x => by
    have := LinearMap.pi_apply_eq_sum_univ (L : (S → ℝ) →ₗ[ℝ] ℝ) x
    simpa [hc, smul_eq_mul, mul_comm] using this
  set b : ∀ p, ρ p → ℝ := fun p => ∑ s, c s • a s p with hb
  have hsq : ∀ s p, Real.sqrt ((c s • a s p) ⬝ᵥ (c s • a s p)) =
      |c s| * Real.sqrt (a s p ⬝ᵥ a s p) := fun s p => by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hbsum : Summable fun p => Real.sqrt (b p ⬝ᵥ b p) := by
    refine Summable.of_nonneg_of_le (fun p => Real.sqrt_nonneg _) (fun p => ?_)
      (summable_sum (s := (univ : Finset S)) fun s _ => (ha s).mul_left |c s|)
    refine (sqrt_dotProduct_self_sum_le univ fun s => c s • a s p).trans ?_
    exact (sum_congr rfl fun s _ => hsq s p).le
  -- almost surely every series converges, so `L X = H_b`
  have hae : ∀ᵐ g ∂gaussianField, ∀ s, Summable fun p => a s p ⬝ᵥ g p :=
    ae_all_iff.2 fun s => by
      have := ae_summable_of_tsum_eLpNorm_ne_top (μ := gaussianField)
        (f := fun p (g : ∀ p, ρ p → ℝ) => a s p ⬝ᵥ g p)
        (fun p => (memLp_coord p (a s p)).1) (by
          refine ne_top_of_le_ne_top (tsum_eLpNorm_coord_ne_top (ha s))
            (ENNReal.tsum_le_tsum fun p => ?_)
          exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two (memLp_coord p (a s p)).1)
      exact this
  have hEq : (fun g : ∀ p, ρ p → ℝ => L fun s => ∑' p, a s p ⬝ᵥ g p) =ᵐ[gaussianField]
      fun g => ∑' p, b p ⬝ᵥ g p := by
    filter_upwards [hae] with g hg
    simp only [hL, hb]
    simp_rw [sum_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [Summable.tsum_finsetSum fun s _ => (hg s).mul_left (c s)]
    exact sum_congr rfl fun s _ => by rw [tsum_mul_left]
  refine ⟨0, (∑' p, b p ⬝ᵥ b p).toNNReal, ?_⟩
  rw [Measure.map_map L.continuous.measurable hm]
  exact (Measure.map_congr hEq).trans (map_tsum_dotProduct_eq_gaussianReal hbsum)

end ProbabilityTheory
