/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.GaussianField
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Decoupling

/-!
# The fixed-point map of (1.372)--(1.373) and its contraction estimate

The map `T(q, ρ) = (E⟨x_u⟩⟨x_v⟩, E⟨x_u x_v⟩)` of the right-hand sides of (1.372)--(1.373), for a
Gaussian field `Y` of covariance `β² q` and Gibbs measure with exponent (1.371).  Along the
interpolation (1.386) it is Lipschitz with constant `18 β² d²` in the Frobenius distance, and
`18 β² d³` in the entrywise sup distance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- The field exponent (1.371) is jointly measurable in the field and the spin. -/
theorem measurable_skVectorFieldExponent_joint {d : ℕ} (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (β : ℝ) (ρ q : Fin d → Fin d → ℝ) :
    Measurable fun p : (Fin d → ℝ) × α => skVectorFieldExponent ξ β ρ q p.1 p.2 := by
  unfold skVectorFieldExponent
  exact (Finset.measurable_sum _ fun w _ => ((measurable_pi_apply w).comp measurable_fst).mul
    ((hξ w).comp measurable_snd)).add (measurable_const.mul (Finset.measurable_sum _
      fun w _ => Finset.measurable_sum _ fun w' _ =>
        (((hξ w).comp measurable_snd).mul ((hξ w').comp measurable_snd)).mul measurable_const))

/-- The replica Gibbs average of the field model is measurable in the field. -/
theorem measurable_skVectorFieldAverage {d : ℕ} {R : Type*} [Fintype R] (μ : Measure α)
    [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (F : (R → α) → ℝ) (hF : Measurable F) :
    Measurable (skVectorFieldAverage μ ξ β ρ q F) :=
  measurable_integral_pi_tilted (μ := μ) (ι := R)
    (E := fun y a => skVectorFieldExponent ξ β ρ q y a)
    (measurable_skVectorFieldExponent_joint ξ hξ β ρ q) hF

/-- The right-hand sides of (1.372) and (1.373) as a map on pairs `(q, ρ)` of matrices:
`T(q, ρ) = (E⟨ξᵤ⟩⟨ξᵥ⟩, E⟨ξᵤ ξᵥ⟩)` for the Gaussian field of covariance `β² q` and the field
exponent (1.371) with matrix `ρ - q`. -/
noncomputable def skVectorFixedPointMap {d : ℕ} (μ : Measure α) (ξ : α → Fin d → ℝ) (β : ℝ)
    (x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (fun u v => ∫ y, skVectorFieldAverage μ ξ β x.2 x.1
      (fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 1) v) y ∂(skVectorGaussianLaw β x.1),
   fun u v => ∫ y, skVectorFieldAverage μ ξ β x.2 x.1
      (fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 0) v) y ∂(skVectorGaussianLaw β x.1))

/-- The disorder average over the pair of Gaussian fields is the average over the first field. -/
theorem integral_skVectorGaussianPairField_avg_inl {d : ℕ} {R : Type*} [Fintype R] (μ : Measure α)
    [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (β : ℝ) (ρ q q' : Fin d → Fin d → ℝ) (F : (R → α) → ℝ) (hF : Measurable F) :
    ∫ ω, skVectorFieldAverage μ ξ β ρ q F (fun x => skVectorGaussianPairField (Sum.inl x) ω)
        ∂(skVectorGaussianPairLaw β q q') =
      ∫ y, skVectorFieldAverage μ ξ β ρ q F y ∂(skVectorGaussianLaw β q) := by
  have hm := measurable_skVectorFieldAverage μ ξ hξ β ρ q F hF
  have h1 := integral_skVectorGaussianPairField_fst β q q'
    (fun z : EuclideanSpace ℝ (Fin d) => skVectorFieldAverage μ ξ β ρ q F z.ofLp)
  have h2 : ∫ y, skVectorFieldAverage μ ξ β ρ q F y ∂(skVectorGaussianLaw β q) =
      ∫ z : EuclideanSpace ℝ (Fin d), skVectorFieldAverage μ ξ β ρ q F z.ofLp
        ∂(multivariateGaussian 0 (β ^ 2 • Matrix.of q)) := by
    unfold skVectorGaussianLaw
    exact integral_map (by fun_prop) hm.aestronglyMeasurable
  rw [h2, ← h1]
  rfl

/-- The disorder average over the pair of Gaussian fields is the average over the second field. -/
theorem integral_skVectorGaussianPairField_avg_inr {d : ℕ} {R : Type*} [Fintype R] (μ : Measure α)
    [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (β : ℝ) (ρ q q' : Fin d → Fin d → ℝ) (F : (R → α) → ℝ) (hF : Measurable F) :
    ∫ ω, skVectorFieldAverage μ ξ β ρ q' F (fun x => skVectorGaussianPairField (Sum.inr x) ω)
        ∂(skVectorGaussianPairLaw β q q') =
      ∫ y, skVectorFieldAverage μ ξ β ρ q' F y ∂(skVectorGaussianLaw β q') := by
  have hm := measurable_skVectorFieldAverage μ ξ hξ β ρ q' F hF
  have h1 := integral_skVectorGaussianPairField_snd β q q'
    (fun z : EuclideanSpace ℝ (Fin d) => skVectorFieldAverage μ ξ β ρ q' F z.ofLp)
  have h2 : ∫ y, skVectorFieldAverage μ ξ β ρ q' F y ∂(skVectorGaussianLaw β q') =
      ∫ z : EuclideanSpace ℝ (Fin d), skVectorFieldAverage μ ξ β ρ q' F z.ofLp
        ∂(multivariateGaussian 0 (β ^ 2 • Matrix.of q')) := by
    unfold skVectorGaussianLaw
    exact integral_map (by fun_prop) hm.aestronglyMeasurable
  rw [h2, ← h1]
  rfl

/-- A bounded replica Gibbs average of the field model is bounded by the same constant. -/
theorem abs_skVectorFieldAverage_le {d : ℕ} {R : Type*} [Fintype R] (μ : Measure α)
    [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (ρ q : Fin d → Fin d → ℝ) (y : Fin d → ℝ)
    (F : (R → α) → ℝ) {M : ℝ} (hFb : ∀ σ, |F σ| ≤ M) :
    |skVectorFieldAverage μ ξ β ρ q F y| ≤ M := by
  have hprob : IsProbabilityMeasure (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
    isProbabilityMeasure_tilted
      (integrable_exp_skVectorFieldExponent μ ξ hξ (Nat.cast_nonneg d) hbound β ρ q y)
  unfold skVectorFieldAverage
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun _ : R => μ.tilted (skVectorFieldExponent ξ β ρ q y)) (f := F) (C := M)
    (Filter.Eventually.of_forall fun σ => by simpa using hFb σ)
  simpa using this

/-- **Linearity of the Gaussian average of replica Gibbs averages.** -/
theorem integral_skVectorFieldAverage_sum {d : ℕ} {R κ : Type*} [Fintype R] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) {P : Measure (Fin d → ℝ)} [IsProbabilityMeasure P]
    (G : κ → (R → α) → ℝ) (hG : ∀ i, Measurable (G i)) {M : ℝ} (hGb : ∀ i σ, |G i σ| ≤ M)
    (c : κ → ℝ) :
    ∫ y, skVectorFieldAverage μ ξ β ρ q (fun σ => ∑ i, c i * G i σ) y ∂P =
      ∑ i, c i * ∫ y, skVectorFieldAverage μ ξ β ρ q (G i) y ∂P := by
  have hinner : ∀ y, skVectorFieldAverage μ ξ β ρ q (fun σ => ∑ i, c i * G i σ) y =
      ∑ i, c i * skVectorFieldAverage μ ξ β ρ q (G i) y := fun y => by
    have hprob : IsProbabilityMeasure (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
      isProbabilityMeasure_tilted
        (integrable_exp_skVectorFieldExponent μ ξ hξ (Nat.cast_nonneg d) hbound β ρ q y)
    unfold skVectorFieldAverage
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    · exact fun i _ => (Integrable.of_bound (hG i).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun σ => by simpa using hGb i σ)).const_mul _
  simp_rw [hinner]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · exact fun i _ => (Integrable.of_bound
      (measurable_skVectorFieldAverage μ ξ hξ β ρ q (G i) (hG i)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by
        simpa using abs_skVectorFieldAverage_le μ ξ hξ hbound β ρ q y (G i) (hGb i))).const_mul _

/-- **The Lipschitz estimate for one replica Gibbs average** (Frobenius form).  For two pairs of
matrices with `q`, `q'` positive semidefinite and Frobenius distance at most `ε`, the Gaussian
averages of the replica averages of a function `F` bounded by `M` differ by at most
`18 β² M d ε`. -/
theorem abs_skVectorFieldAverage_sub_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {x x' : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : (Matrix.of x.1).PosSemidef)
    (hx' : (Matrix.of x'.1).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε)
    (h1 : ∑ u, ∑ v, (x.1 u v - x'.1 u v) ^ 2 ≤ ε ^ 2)
    (h2 : ∑ u, ∑ v, (x.2 u v - x'.2 u v) ^ 2 ≤ ε ^ 2)
    (F : (Fin 2 → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M) :
    |(∫ y, skVectorFieldAverage μ ξ β x.2 x.1 F y ∂(skVectorGaussianLaw β x.1)) -
        ∫ y, skVectorFieldAverage μ ξ β x'.2 x'.1 F y ∂(skVectorGaussianLaw β x'.1)| ≤
      18 * β ^ 2 * M * (d : ℝ) * ε := by
  have h := abs_skVectorFieldAverage_interpolation_sub_le μ ξ hξ hbound β x.2 x.1 x'.2 x'.1 hε h2
    h1 F hF hM hFb
    (hasGaussianLaw_skVectorGaussianPairField β x.1 x'.1) (measurable_skVectorGaussianPairField)
    (integral_skVectorGaussianPairField β x.1 x'.1)
    (integral_skVectorGaussianPairField_inl_mul β x.1 x'.1 hx)
    (integral_skVectorGaussianPairField_inr_mul β x.1 x'.1 hx')
    (integral_skVectorGaussianPairField_inl_inr_mul β x.1 x'.1)
  rw [integral_skVectorGaussianPairField_avg_inl μ ξ hξ β x.2 x.1 x'.1 F hF,
    integral_skVectorGaussianPairField_avg_inr μ ξ hξ β x'.2 x.1 x'.1 F hF] at h
  simp only [Fintype.card_fin] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Frobenius contraction of a block of the fixed-point map.**  If `W σ` is a rank-one matrix
`a bᵀ` with `‖a‖², ‖b‖² ≤ d` for every pair of spins `σ`, then the matrix of Gaussian averages of
the replica averages of `W σ u v` moves by at most `18 β² d² ε` in Frobenius norm when the
pair `(q, ρ)` moves by at most `ε` in Frobenius norm. -/
theorem sum_sq_skVectorFieldAverage_sub_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {x x' : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : (Matrix.of x.1).PosSemidef)
    (hx' : (Matrix.of x'.1).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε)
    (h1 : ∑ u, ∑ v, (x.1 u v - x'.1 u v) ^ 2 ≤ ε ^ 2)
    (h2 : ∑ u, ∑ v, (x.2 u v - x'.2 u v) ^ 2 ≤ ε ^ 2)
    (W : (Fin 2 → α) → Fin d → Fin d → ℝ) (hWm : ∀ u v, Measurable fun σ => W σ u v)
    (hW : ∀ σ, ∃ a b : Fin d → ℝ, ∑ u, a u ^ 2 ≤ d ∧ ∑ v, b v ^ 2 ≤ d ∧
      ∀ u v, W σ u v = a u * b v)
    (hWb : ∀ σ u v, |W σ u v| ≤ d) :
    ∑ u, ∑ v, ((∫ y, skVectorFieldAverage μ ξ β x.2 x.1 (fun σ => W σ u v) y
        ∂(skVectorGaussianLaw β x.1)) - ∫ y, skVectorFieldAverage μ ξ β x'.2 x'.1 (fun σ => W σ u
          v) y
        ∂(skVectorGaussianLaw β x'.1)) ^ 2 ≤ (18 * β ^ 2 * (d : ℝ) ^ 2 * ε) ^ 2 := by
  classical
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  set D : Fin d → Fin d → ℝ := fun u v =>
    (∫ y, skVectorFieldAverage μ ξ β x.2 x.1 (fun σ => W σ u v) y ∂(skVectorGaussianLaw β x.1)) -
      ∫ y, skVectorFieldAverage μ ξ β x'.2 x'.1 (fun σ => W σ u v) y ∂(skVectorGaussianLaw β x'.1)
    with hD
  change ∑ u, ∑ v, D u v ^ 2 ≤ _
  set S : ℝ := ∑ u, ∑ v, D u v ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
  have hsd : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd
  set F : (Fin 2 → α) → ℝ := fun σ => ∑ j : Fin d × Fin d, D j.1 j.2 * W σ j.1 j.2 with hF
  have hFm : Measurable F :=
    Finset.measurable_sum _ fun j _ => measurable_const.mul (hWm j.1 j.2)
  have hFb : ∀ σ, |F σ| ≤ Real.sqrt S * d := fun σ => by
    obtain ⟨a, b, ha, hb, hab⟩ := hW σ
    have : F σ = ∑ u, ∑ v, D u v * (a u * b v) := by
      simp only [hF, Fintype.sum_prod_type, hab]
    rw [this]
    have := abs_sum_bilinear_le D a b (Real.sqrt_nonneg S) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (by rw [hsS]) (by rw [hsd]; exact ha) (by rw [hsd]; exact hb)
    calc _ ≤ Real.sqrt S * Real.sqrt d * Real.sqrt d := this
      _ = Real.sqrt S * d := by rw [mul_assoc, Real.mul_self_sqrt hd]
  have key := abs_skVectorFieldAverage_sub_le μ ξ hξ hbound β hx hx' hε h1 h2 F hFm
    (mul_nonneg (Real.sqrt_nonneg S) hd) hFb
  have lin : ∀ (y' : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)),
      ∫ y, skVectorFieldAverage μ ξ β y'.2 y'.1 F y ∂(skVectorGaussianLaw β y'.1) =
        ∑ j : Fin d × Fin d, D j.1 j.2 * ∫ y, skVectorFieldAverage μ ξ β y'.2 y'.1
          (fun σ => W σ j.1 j.2) y ∂(skVectorGaussianLaw β y'.1) := fun y' => by
    have := isGaussian_skVectorGaussianLaw β y'.1
    exact integral_skVectorFieldAverage_sum μ ξ hξ hbound β y'.2 y'.1
      (G := fun (j : Fin d × Fin d) σ => W σ j.1 j.2)
      (fun j => hWm j.1 j.2) (M := d) (fun j σ => hWb σ j.1 j.2)
      (fun (j : Fin d × Fin d) => D j.1 j.2)
  rw [lin x, lin x', ← Finset.sum_sub_distrib] at key
  have hSeq : ∑ j : Fin d × Fin d, (D j.1 j.2 * ∫ y, skVectorFieldAverage μ ξ β x.2 x.1
      (fun σ => W σ j.1 j.2) y ∂(skVectorGaussianLaw β x.1) - D j.1 j.2 * ∫ y,
        skVectorFieldAverage μ ξ β
      x'.2 x'.1 (fun σ => W σ j.1 j.2) y ∂(skVectorGaussianLaw β x'.1)) = S := by
    rw [hS, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    simp only [hD]; ring
  rw [hSeq, abs_of_nonneg hS0] at key
  set r := Real.sqrt S with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg S
  have hK0 : 0 ≤ 18 * β ^ 2 * (d : ℝ) ^ 2 * ε := by positivity
  have hrK : r ≤ 18 * β ^ 2 * (d : ℝ) ^ 2 * ε := by
    by_contra hcon
    replace hcon := not_le.mp hcon
    have : r * r ≤ 18 * β ^ 2 * (d : ℝ) ^ 2 * ε * r := by nlinarith [key, hsS]
    nlinarith
  rw [← hsS]
  exact pow_le_pow_left₀ hr0 hrK 2

/-- **The Lipschitz estimate for the right-hand sides of (1.372)--(1.373)** (entrywise form).
For two pairs of matrices with `q`, `q'` positive semidefinite and entrywise distance at most
`δ`, the entries of `T(q, ρ)` and `T(q', ρ')` differ by at most `18 β² d³ δ`. -/
theorem abs_skVectorFixedPointMap_apply_sub_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {x x' : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : (Matrix.of x.1).PosSemidef)
    (hx' : (Matrix.of x'.1).PosSemidef) {δ : ℝ} (h1 : ∀ u v, |x.1 u v - x'.1 u v| ≤ δ)
    (h2 : ∀ u v, |x.2 u v - x'.2 u v| ≤ δ) (u v : Fin d) :
    |(skVectorFixedPointMap μ ξ β x).1 u v - (skVectorFixedPointMap μ ξ β x').1 u v| ≤
        18 * β ^ 2 * (d : ℝ) ^ 3 * δ ∧
      |(skVectorFixedPointMap μ ξ β x).2 u v - (skVectorFixedPointMap μ ξ β x').2 u v| ≤
        18 * β ^ 2 * (d : ℝ) ^ 3 * δ := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (h1 u v)
  have hε : 0 ≤ (d : ℝ) * δ := mul_nonneg hd hδ
  have hsum : ∀ M N : Fin d → Fin d → ℝ, (∀ u v, |M u v - N u v| ≤ δ) →
      ∑ u, ∑ v, (M u v - N u v) ^ 2 ≤ ((d : ℝ) * δ) ^ 2 := fun M N h => by
    calc _ ≤ ∑ _u : Fin d, ∑ _v : Fin d, δ ^ 2 :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
            calc _ = |M u v - N u v| ^ 2 := (sq_abs _).symm
              _ ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h u v) 2
      _ = ((d : ℝ) * δ) ^ 2 := by simp [mul_pow]; ring
  have hs1 := hsum _ _ h1
  have hs2 := hsum _ _ h2
  have hent : ∀ M : Fin d → Fin d → ℝ, ∑ u, ∑ v, M u v ^ 2 ≤ (18 * β ^ 2 * (d : ℝ) ^ 2 *
      ((d : ℝ) * δ)) ^ 2 → |M u v| ≤ 18 * β ^ 2 * (d : ℝ) ^ 3 * δ := fun M hM => by
    have h3 : M u v ^ 2 ≤ ∑ u, ∑ v, M u v ^ 2 :=
      (Finset.single_le_sum (f := fun v => M u v ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ v)).trans
        (Finset.single_le_sum (f := fun u => ∑ v, M u v ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ u))
    have h4 : (18 * β ^ 2 * (d : ℝ) ^ 2 * ((d : ℝ) * δ)) = 18 * β ^ 2 * (d : ℝ) ^ 3 * δ := by
      ring
    rw [← h4]
    exact abs_le_of_sq_le_sq' (h3.trans hM) (by positivity) |> fun h => abs_le.2 h
  refine ⟨?_, ?_⟩
  · exact hent _ (sum_sq_skVectorFieldAverage_sub_le μ ξ hξ hbound β hx hx' hε hs1 hs2
      (fun σ u v => ξ (σ 0) u * ξ (σ 1) v)
      (fun u v => ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 1)))
      (fun σ => ⟨ξ (σ 0), ξ (σ 1), hbound _, hbound _, fun _ _ => rfl⟩)
      (fun σ u v => abs_spin_mul_le ξ hd hbound (σ 0) (σ 1) u v))
  · exact hent _ (sum_sq_skVectorFieldAverage_sub_le μ ξ hξ hbound β hx hx' hε hs1 hs2
      (fun σ u v => ξ (σ 0) u * ξ (σ 0) v)
      (fun u v => ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 0)))
      (fun σ => ⟨ξ (σ 0), ξ (σ 0), hbound _, hbound _, fun _ _ => rfl⟩)
      (fun σ u v => abs_spin_mul_le ξ hd hbound (σ 0) (σ 0) u v))

end SpinGlasses
