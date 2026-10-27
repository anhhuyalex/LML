/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment

/-!
# The standard Gaussian matrix `𝒩(0,1)^{ι×κ}`

Architecture-independent facts about a matrix `G : ι → κ → ℝ` with i.i.d. `𝒩(0, 1)` entries
(`Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1`, `ι, κ` finite):

1. **Coordinate moments**: `integral_gaussianInit_entry`, `integral_gaussianInit_entry_sq`, and the
   covariance tensor `integral_gaussianInit_entry_mul_entry` (`E[G_{ik} G_{jl}] = δ_{ij} δ_{kl}`).
2. **Linear forms** `u ⬝ᵥ (G v)`: finite combinations of the entries
   (`dotProduct_mulVec_of_eq_sum`), centered (`integral_linearForm_gaussianInit`), in `L²`
   (`memLp_linearForm_gaussianInit`) with bilinear covariance
   (`integral_gaussianMatrix_bilinear_mul_bilinear`).
3. **Joint Gaussianity** (`hasGaussianLaw_gaussianInit_id`), so every linear image of `G` is a
   Gaussian vector; in particular any finite family of bilinear forms
   (`hasGaussianLaw_bilinear_family`).

They serve both the NTK initialization (`Optimization/NTK/Initialization`) and the Sherrington–
Kirkpatrick Hamiltonian (`SpinGlasses/SKModel.lean`).
-/

@[expose] public section

open scoped Matrix Real BigOperators
open MeasureTheory ProbabilityTheory Matrix

namespace ProbabilityTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Coordinate Expectations under the Gaussian Matrix Law -/

/-- Every single coordinate `W i k` of a Gaussian matrix initialized by `𝒩(0,1)^{ι×κ}`
has unit variance: `∫ (W i k)² = 1`. -/
theorem integral_gaussianInit_entry_sq (i : ι) (k : κ) :
    ∫ W : ι → κ → ℝ, (W i k) ^ 2 ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ =>
        gaussianReal 0 1) = 1 := by
  have h2 := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral (X := id) measurable_id'.aemeasurable] at h2
  rw [MeasureTheory.integral_comp_eval
      (μ := fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) (i := i)
      (f := fun a : κ → ℝ => a k ^ 2)
      (by fun_prop : Measurable fun a : κ → ℝ => a k ^ 2).aestronglyMeasurable,
    MeasureTheory.integral_comp_eval (μ := fun _ : κ => gaussianReal 0 1) (i := k)
      (f := fun x : ℝ => x ^ 2)
      (by fun_prop : Measurable fun x : ℝ => x ^ 2).aestronglyMeasurable]
  simpa [id] using h2

/-- Every single coordinate `W i k` of a Gaussian matrix has zero mean: `∫ W i k = 0`. -/
theorem integral_gaussianInit_entry (i : ι) (k : κ) :
    ∫ W : ι → κ → ℝ, W i k ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ =>
        gaussianReal 0 1) = 0 := by
  rw [MeasureTheory.integral_comp_eval
      (μ := fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) (i := i)
      (f := fun a : κ → ℝ => a k)
      (by fun_prop : Measurable fun a : κ → ℝ => a k).aestronglyMeasurable, integral_eval,
    ProbabilityTheory.integral_id_gaussianReal]

/-! ### Bilinear Gaussian Form Expectation (Proposition 2.27 Step 4) -/

/-- Every single coordinate of a standard Gaussian matrix is square-integrable (in `L²`). -/
lemma memLp_entry (i : ι) (l : κ) :
    MemLp (fun W : ι → κ → ℝ => W i l) 2 (Measure.pi fun _ : ι => Measure.pi fun _ : κ =>
        gaussianReal 0 1) := by
  have h_base : MemLp id (2 : ENNReal) (gaussianReal 0 1) := memLp_id_gaussianReal (2 : NNReal)
  exact h_base.comp_measurePreserving
    ((measurePreserving_eval (fun _ : κ => gaussianReal 0 1) l).comp
      (measurePreserving_eval (fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) i))

/-- Bilinear product of any two matrix coordinates `W i k * W j l` is integrable. -/
lemma integrable_entry_mul_entry (i j : ι) (k l : κ) :
    Integrable (fun W : ι → κ → ℝ => W i k * W j l) (Measure.pi fun _ : ι => Measure.pi
        fun _ : κ => gaussianReal 0 1) := by
  have h1 := memLp_entry i k
  have h2 := memLp_entry j l
  exact h1.integrable_mul h2

/-- Exact coordinate covariance under the standard Gaussian matrix law:
`∫ W i k * W j l ∂(𝒩(0,1)^{ι×κ}) = if i = j ∧ k = l then 1 else 0`. -/
theorem integral_gaussianInit_entry_mul_entry [DecidableEq ι] [DecidableEq κ] (i j : ι)
    (k l : κ) :
    ∫ W : ι → κ → ℝ, W i k * W j l ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ =>
        gaussianReal 0 1) =
      if i = j ∧ k = l then 1 else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    have h_sq : (fun W : ι → κ → ℝ => W i k * W i k) =
        fun W => (W i k) ^ 2 := by ext W; ring
    rw [h_sq, integral_gaussianInit_entry_sq]
  · by_cases hij : i = j
    · subst hij
      have hkl : k ≠ l := fun h_eq => h ⟨rfl, h_eq⟩
      rw [MeasureTheory.integral_comp_eval
          (μ := fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) (i := i)
        (f := fun a : κ → ℝ => a k * a l) (by fun_prop)]
      have h_indep := (iIndepFun_pi (μ := fun _ : κ => gaussianReal 0 1)
        fun _ => aemeasurable_id).indepFun hkl
      change (fun a => a k) ⟂ᵢ[(Measure.pi fun _ : κ => gaussianReal 0 1)] (fun a => a
          l) at h_indep
      rw [h_indep.integral_fun_mul_eq_mul_integral
          (by fun_prop : Measurable fun a : κ → ℝ => a k).aestronglyMeasurable
          (by fun_prop : Measurable fun a : κ → ℝ => a l).aestronglyMeasurable, integral_eval,
        ProbabilityTheory.integral_id_gaussianReal, zero_mul]
    · have h_indep_row := (iIndepFun_pi
        (μ := fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1)
        fun _ => aemeasurable_id).indepFun hij
      have h_indep_entry := h_indep_row.comp (measurable_pi_apply k) (measurable_pi_apply l)
      change (fun W : ι → κ → ℝ => W i k) ⟂ᵢ[Measure.pi fun _ : ι =>
        Measure.pi fun _ : κ => gaussianReal 0 1] (fun W : ι → κ → ℝ => W j l)
        at h_indep_entry
      rw [h_indep_entry.integral_fun_mul_eq_mul_integral
          (by fun_prop : Measurable fun W : ι → κ → ℝ => W i k).aestronglyMeasurable
          (by fun_prop : Measurable fun W : ι → κ → ℝ => W j l).aestronglyMeasurable,
        integral_gaussianInit_entry i k, zero_mul]

/-- The rank-one weight `u vᵀ` turns the trace form into the bilinear form `u ⬝ᵥ (M v)`:
`u ⬝ᵥ (M v) = ∑ᵢⱼ (u vᵀ)ᵢⱼ Mᵢⱼ`. -/
lemma dotProduct_mulVec_eq_sum_vecMulVec (u : ι → ℝ) (v : κ → ℝ) (M : Matrix ι κ ℝ) :
    u ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, Matrix.vecMulVec u v i j * M i j := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A linear form `u ⬝ᵥ (G v)` of a standard Gaussian matrix `G` is the finite combination
`∑ᵢⱼ uᵢ vⱼ Gᵢⱼ` of its coordinates. -/
lemma dotProduct_mulVec_of_eq_sum (u : ι → ℝ) (v : κ → ℝ) (G : ι → κ → ℝ) :
    u ⬝ᵥ (Matrix.of G *ᵥ v) = ∑ i, ∑ j, (u i * v j) * G i j := by
  simpa only [vecMulVec_apply, Matrix.of_apply] using
    dotProduct_mulVec_eq_sum_vecMulVec u v (Matrix.of G)

/-- A linear form `u ⬝ᵥ (G v)` of a standard Gaussian matrix `G` is in `L²`. -/
theorem memLp_linearForm_gaussianInit (u : ι → ℝ) (v : κ → ℝ) :
    MemLp (fun G : ι → κ → ℝ => u ⬝ᵥ (Matrix.of G *ᵥ v)) 2
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) := by
  simp_rw [dotProduct_mulVec_of_eq_sum]
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => (memLp_entry i j).const_mul _

/-- A linear form `u ⬝ᵥ (G v)` of a standard Gaussian matrix `G` has mean zero. -/
theorem integral_linearForm_gaussianInit (u : ι → ℝ) (v : κ → ℝ) :
    ∫ G : ι → κ → ℝ, u ⬝ᵥ (Matrix.of G *ᵥ v)
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) = 0 := by
  simp_rw [dotProduct_mulVec_of_eq_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((memLp_entry i j).integrable (by norm_num)).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((memLp_entry i j).integrable (by norm_num)).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, integral_gaussianInit_entry, mul_zero]

/-- **Bilinear covariance of a standard Gaussian matrix.** For `G ~ 𝒩(0,1)^{ι×κ}` and deterministic
vectors `u, x : ι → ℝ`, `v, y : κ → ℝ`,
`E[(u ⬝ᵥ G v) (x ⬝ᵥ G y)] = (u ⬝ᵥ x) (v ⬝ᵥ y)`.
The proof views `G` as the random vector `p ↦ G p.1 p.2` on `ι × κ` with second-moment matrix `1`
(`integral_gaussianInit_entry_mul_entry`) and `u ⬝ᵥ G v` as its pairing with `u ⊗ v`. -/
theorem integral_gaussianMatrix_bilinear_mul_bilinear (u x : ι → ℝ) (v y : κ → ℝ) :
    ∫ G : ι → κ → ℝ, (u ⬝ᵥ (Matrix.of G *ᵥ v)) * (x ⬝ᵥ (Matrix.of G *ᵥ y))
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) =
      (u ⬝ᵥ x) * (v ⬝ᵥ y) := by
  have hpair : ∀ (u : ι → ℝ) (v : κ → ℝ) (G : ι → κ → ℝ), u ⬝ᵥ (Matrix.of G *ᵥ v) =
      (fun q : ι × κ => G q.1 q.2) ⬝ᵥ (fun q => u q.1 * v q.2) := fun u v G => by
    simp only [dotProduct, mulVec, Matrix.of_apply, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpair]
  refine (integral_dotProduct_mul_dotProduct (fun (G : ι → κ → ℝ) (q : ι × κ) => G q.1 q.2)
    (fun q => memLp_entry q.1 q.2) 1 (fun q r => ?_) _ _).trans ?_
  · simp only [integral_gaussianInit_entry_mul_entry, Matrix.one_apply, Prod.ext_iff]
  simp only [one_mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Joint Gaussianity -/

/-- The whole matrix `G ~ 𝒩(0,1)^{ι×κ}` is a jointly Gaussian vector: its rows are independent
Gaussian vectors (`isGaussian_pi_gaussianReal`), so every linear image `G ↦ (G A, G B)` is
jointly Gaussian. -/
lemma hasGaussianLaw_gaussianInit_id :
    HasGaussianLaw (fun G : ι → κ → ℝ => G)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have := isGaussian_pi_gaussianReal (κ := κ)
  refine iIndepFun.hasGaussianLaw (fun i => ?_) (iIndepFun_pi fun _ => aemeasurable_id)
  have : IsGaussian ((Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1).map
      (fun G : ι → κ → ℝ => G i)) := by
    rw [(measurePreserving_eval (fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) i).map_eq]
    infer_instance
  exact IsGaussian.hasGaussianLaw (measurable_pi_apply i).aemeasurable

/-- **Any finite family of bilinear forms `u r ⬝ᵥ (G v r)` of a standard Gaussian matrix is a
Gaussian vector.**  This is the Hamiltonian `r ↦ (√N)⁻¹ σ_r ⬝ᵥ (G σ_r)` of the
Sherrington–Kirkpatrick model with `u r = (√N)⁻¹ • σ_r`, `v r = σ_r`. -/
lemma hasGaussianLaw_bilinear_family {A : Type*} [Finite A] (u : A → ι → ℝ) (v : A → κ → ℝ) :
    HasGaussianLaw (fun (G : ι → κ → ℝ) (r : A) => u r ⬝ᵥ (Matrix.of G *ᵥ v r))
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have := Fintype.ofFinite A
  let L : (ι → κ → ℝ) →L[ℝ] (A → ℝ) := ContinuousLinearMap.pi fun r =>
    ∑ i, ∑ j, (u r i * v r j) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => κ → ℝ) i)
  convert hasGaussianLaw_gaussianInit_id.map_fun L using 1
  ext G r
  simp [dotProduct_mulVec_of_eq_sum, L]

end ProbabilityTheory

end
