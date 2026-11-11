/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.Stationarity
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.LogPartition
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FixedPoint.Temperature

/-!
# The replica-symmetric pressure (Talagrand Eq. (1.387))

`G(β, q, ρ) = -(β²/4) ∑ (ρ² - q²) + 𝔼 log ∫ ℰ dμ`, defined through the canonical Gaussian
realization of covariance `q`.  Its value does not depend on the realization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- **The replica-symmetric pressure** `-(β²/4) ∑ᵤᵥ (ρᵤᵥ² - qᵤᵥ²) + 𝔼 log ∫ ℰ dμ` of Eq. (1.387),
as a function of `β` and the pair `z = (q, ρ)`; the Gaussian field has covariance `q` and enters
the exponent as `β X`. -/
noncomputable def skVectorPressure {d : ℕ} (μ : Measure α) (ξ : α → Fin d → ℝ) (β : ℝ)
    (z : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) : ℝ :=
  -(β ^ 2 / 4) * (∑ u, ∑ v, z.2 u v ^ 2 - ∑ u, ∑ v, z.1 u v ^ 2) +
    skVectorGaussianFreeEnergy μ ξ z.2 z.1 (skVectorGaussianLaw 1 z.1) (fun u y => y u) β

/-- The log-partition function of the field model is measurable in the field. -/
theorem measurable_skVectorLogPartition {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) :
    Measurable fun y : Fin d → ℝ => Real.log (∫ a, Real.exp (β * ∑ u, y u * ξ a u +
      β ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (ρ u v - q u v)) ∂μ) := by
  have hE : Measurable fun p : (Fin d → ℝ) × α => β * ∑ u, p.1 u * ξ p.2 u +
      β ^ 2 / 2 * ∑ u, ∑ v, ξ p.2 u * ξ p.2 v * (ρ u v - q u v) :=
    (measurable_const.mul (Finset.measurable_sum _ fun u _ =>
      ((measurable_pi_apply u).comp measurable_fst).mul ((hξ u).comp measurable_snd))).add
      (measurable_const.mul (Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
        (((hξ u).comp measurable_snd).mul ((hξ v).comp measurable_snd)).mul measurable_const))
  exact ((Real.measurable_exp.comp hE).stronglyMeasurable.integral_prod_right').measurable.log

/-- **The free energy does not depend on the realization of the Gaussian field.** -/
theorem skVectorGaussianFreeEnergy_eq_canonical {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (ρ q : Fin d → Fin d → ℝ) {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Fin d → Ω → ℝ} (hX : HasGaussianLaw (fun ω u => X u ω) P)
    (hXm : ∀ u, Measurable (X u)) (hX0 : ∀ u, ∫ ω, X u ω ∂P = 0)
    (hXc : ∀ u v, ∫ ω, X u ω * X v ω ∂P = q u v) (β : ℝ) :
    skVectorGaussianFreeEnergy μ ξ ρ q P X β =
      skVectorGaussianFreeEnergy μ ξ ρ q (skVectorGaussianLaw 1 q) (fun u y => y u) β := by
  have hlaw : P.map (fun ω u => X u ω) = skVectorGaussianLaw 1 q :=
    map_eq_skVectorGaussianLaw 1 q hX hX0 (fun u v => by simpa using hXc u v)
  have hXv : Measurable fun ω u => X u ω := measurable_pi_iff.2 hXm
  unfold skVectorGaussianFreeEnergy
  have := integral_map (μ := P) (φ := fun ω u => X u ω) hXv.aemeasurable
    (f := fun y : Fin d → ℝ => Real.log (∫ a, Real.exp (β * ∑ u, y u * ξ a u +
      β ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (ρ u v - q u v)) ∂μ))
    (measurable_skVectorLogPartition μ ξ hξ β ρ q).aestronglyMeasurable
  rw [hlaw] at this
  exact this.symm

/-- Scaling the canonical Gaussian field by `b` gives the Gaussian field of covariance `b² q`. -/
theorem integral_skVectorGaussianLaw_scale {d : ℕ} (b : ℝ) (q : Fin d → Fin d → ℝ)
    (hq : (Matrix.of q).PosSemidef) {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) :
    ∫ y, g (fun u => b * y u) ∂(skVectorGaussianLaw 1 q) = ∫ y, g y ∂(skVectorGaussianLaw b q) := by
  have := isGaussian_skVectorGaussianLaw 1 q
  set P := skVectorGaussianLaw 1 q with hP
  have hZ : HasGaussianLaw (fun (y : Fin d → ℝ) (k : Fin d) => y k) P :=
    IsGaussian.hasGaussianLaw_id
  have hmean : ∀ k : Fin d, ∫ y : Fin d → ℝ, y k ∂P = 0 := fun k =>
    integral_skVectorGaussianLaw_coord 1 q k
  have hcov : ∀ x y : Fin d, ∫ ω : Fin d → ℝ, ω x * ω y ∂P = q x y := fun x y => by
    simpa using integral_skVectorGaussianLaw_mul 1 q hq x y
  have hlaw : P.map (fun (ω : Fin d → ℝ) (u : Fin d) => b * ω u) = skVectorGaussianLaw b q :=
    map_eq_skVectorGaussianLaw b q (hZ.mul (fun _ => b)) (fun u => by
      rw [integral_const_mul, hmean, mul_zero]) (fun u v => by
      have : ∫ ω : Fin d → ℝ, b * ω u * (b * ω v) ∂P = b ^ 2 * ∫ ω, ω u * ω v ∂P := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      rw [this, hcov])
  have hm : Measurable fun (ω : Fin d → ℝ) (u : Fin d) => b * ω u :=
    measurable_pi_iff.2 fun u => measurable_const.mul (measurable_pi_apply u)
  rw [← hlaw, integral_map hm.aemeasurable hg.aestronglyMeasurable]

/-- **The gradient of the pressure in `ρ` is `(β²/2)(T₂(q, ρ) - ρ)`** (Lemma 1.12.6 for `ρ`, in the
language of the fixed-point map): along `ρ(s) = ρ + s (ρ' - ρ)` the derivative of the pressure at
`s₀` is `(β²/2) ∑ᵤᵥ (ρ' - ρ)ᵤᵥ ((T(q, ρ(s₀))).2 - ρ(s₀))ᵤᵥ`. -/
theorem hasDerivAt_skVectorPressure_rho_segment {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (b : ℝ) (q ρ ρ' : Fin d → Fin d → ℝ)
    (hq : (Matrix.of q).PosSemidef) (s₀ : ℝ) :
    HasDerivAt (fun s => skVectorPressure μ ξ b (q, fun u v => ρ u v + s * (ρ' u v - ρ u v)))
      (b ^ 2 / 2 * ∑ u, ∑ v, (ρ' u v - ρ u v) *
        ((skVectorFixedPointMap μ ξ b (q, fun u v => ρ u v + s₀ * (ρ' u v - ρ u v))).2 u v -
          (ρ u v + s₀ * (ρ' u v - ρ u v)))) s₀ := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := isGaussian_skVectorGaussianLaw 1 q
  set P := skVectorGaussianLaw 1 q with hP
  have hX : HasGaussianLaw (fun (y : Fin d → ℝ) (u : Fin d) => y u) P :=
      IsGaussian.hasGaussianLaw_id
  have hXm : ∀ u : Fin d, Measurable fun y : Fin d → ℝ => y u := fun u => measurable_pi_apply u
  have hX0 : ∀ u : Fin d, ∫ y : Fin d → ℝ, y u ∂P = 0 := fun u =>
    integral_skVectorGaussianLaw_coord 1
      q u
  have h := hasDerivAt_skVectorPressure_rho μ ξ hξ hr hbound ρ q (fun u v => ρ' u v - ρ u v)
    hX hXm hX0 b s₀
  have hfun : (fun s => skVectorPressure μ ξ b
      (q, fun u v => ρ u v + s * (ρ' u v - ρ u v))) = fun s =>
      -(b ^ 2 / 4) * ∑ u, ∑ v, ((ρ u v + s * (fun u v => ρ' u v - ρ u v) u v) ^ 2 - q u v ^ 2) +
        skVectorGaussianFreeEnergy μ ξ (fun u v => ρ u v + s * (fun u v => ρ' u v - ρ u v) u v) q P
          (fun u y => y u) b := by
    funext s
    unfold skVectorPressure
    simp [Finset.sum_sub_distrib]
    rfl
  rw [hfun]
  refine h.congr_deriv ?_
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  congr 2
  -- identify the Gibbs mean with the fixed-point map
  set ρs : Fin d → Fin d → ℝ := fun u v => ρ u v + s₀ * (ρ' u v - ρ u v) with hρs
  have hmeasG : Measurable fun y : Fin d → ℝ =>
      ∫ a, ξ a u * ξ a v ∂(μ.tilted (skVectorFieldExponent ξ b ρs q y)) :=
    measurable_integral_tilted (e := fun y a => skVectorFieldExponent ξ b ρs q y a)
      (measurable_skVectorFieldExponent_joint ξ hξ b ρs q) (measurable_spin_mul ξ hξ u v)
  have hT : (skVectorFixedPointMap μ ξ b (q, ρs)).2 u v = ∫ y,
      ∫ a, ξ a u * ξ a v ∂(μ.tilted (skVectorFieldExponent ξ b ρs q y))
      ∂(skVectorGaussianLaw b q) := by
    simp only [skVectorFixedPointMap]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
      skVectorFieldAverage_diag μ ξ hξ hbound b ρs q u v y)
  rw [hT, ← integral_skVectorGaussianLaw_scale b q hq hmeasG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  have heq : (fun a => b * ∑ w, y w * ξ a w +
      b ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' + s₀ * (ρ' w w' - ρ w w') - q w w')) =
      skVectorFieldExponent ξ b ρs q (fun u => b * y u) := by
    funext a
    unfold skVectorFieldExponent
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [heq]

/-- **Quadratic estimate in `ρ`.**  If `(q', ρ')` is a fixed point of `T_b` and `(q, ρ)` is within
`δ` of it (entrywise, with `q ⪰ 0`), moving `ρ` to `ρ'` changes the pressure by at most
`(b²/2) d² (1 + 18 b² d³) δ²`. -/
theorem abs_skVectorPressure_rho_sub_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (b : ℝ) {q ρ q' ρ' : Fin d → Fin d → ℝ}
    (hq : (Matrix.of q).PosSemidef) (hq' : (Matrix.of q').PosSemidef)
    (hfix : skVectorFixedPointMap μ ξ b (q', ρ') = (q', ρ')) {δ : ℝ} (hδ : 0 ≤ δ)
    (hqδ : ∀ u v, |q u v - q' u v| ≤ δ) (hρδ : ∀ u v, |ρ u v - ρ' u v| ≤ δ) :
    |skVectorPressure μ ξ b (q, ρ') - skVectorPressure μ ξ b (q, ρ)| ≤
      b ^ 2 / 2 * ((d : ℝ) * d * ((1 + 18 * b ^ 2 * (d : ℝ) ^ 3) * δ * δ)) := by
  classical
  set ψ : ℝ → ℝ := fun s => skVectorPressure μ ξ b
    (q, fun u v => ρ u v + s * (ρ' u v - ρ u v)) with hψ
  have hder := fun s₀ => hasDerivAt_skVectorPressure_rho_segment μ ξ hξ hbound b q ρ ρ' hq s₀
  have hdiff : Differentiable ℝ ψ := fun s => (hder s).differentiableAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope ψ zero_lt_one hdiff.continuous.continuousOn
    hdiff.differentiableOn
  have h0 : ψ 0 = skVectorPressure μ ξ b (q, ρ) := by simp [hψ]
  have h1 : ψ 1 = skVectorPressure μ ξ b (q, ρ') := by
    simp only [hψ, one_mul, add_sub_cancel]
  rw [← h0, ← h1]
  have hE : ψ 1 - ψ 0 = deriv ψ c := by rw [hcd]; ring
  rw [hE, (hder c).deriv, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set ρc : Fin d → Fin d → ℝ := fun u v => ρ u v + c * (ρ' u v - ρ u v) with hρc
  have hρcδ : ∀ u v, |ρc u v - ρ' u v| ≤ δ := fun u v => by
    have : ρc u v - ρ' u v = (1 - c) * (ρ u v - ρ' u v) := by simp only [hρc]; ring
    rw [this, abs_mul, abs_of_nonneg (by linarith [hc.2])]
    calc (1 - c) * |ρ u v - ρ' u v| ≤ 1 * δ :=
          mul_le_mul (by linarith [hc.1]) (hρδ u v) (abs_nonneg _) zero_le_one
      _ = δ := one_mul _
  have hlip := abs_skVectorFixedPointMap_apply_sub_le μ ξ hξ hbound b (x := (q, ρc)) (x' := (q',
    ρ')) hq hq'
    hqδ hρcδ
  have hterm : ∀ u v, |(skVectorFixedPointMap μ ξ b (q, ρc)).2 u v - ρc u v| ≤
      (1 + 18 * b ^ 2 * (d : ℝ) ^ 3) * δ := fun u v => by
    have h2 := (hlip u v).2
    rw [hfix] at h2
    calc |(skVectorFixedPointMap μ ξ b (q, ρc)).2 u v - ρc u v| ≤
          |(skVectorFixedPointMap μ ξ b (q, ρc)).2 u v - ρ' u v| + |ρ' u v - ρc u v| := by
          exact abs_sub_le _ (ρ' u v) _
      _ ≤ 18 * b ^ 2 * (d : ℝ) ^ 3 * δ + δ := by
          refine add_le_add ?_ ?_
          · simpa [abs_sub_comm] using h2
          · rw [abs_sub_comm]; exact hρcδ u v
      _ = _ := by ring
  have hEb : ∀ u v, |ρ' u v - ρ u v| ≤ δ := fun u v => by rw [abs_sub_comm]; exact hρδ u v
  have hterm2 : ∀ u v, |(ρ' u v - ρ u v) *
      ((skVectorFixedPointMap μ ξ b (q, ρc)).2 u v - (ρ u v + c * (ρ' u v - ρ u v)))| ≤
      δ * ((1 + 18 * b ^ 2 * (d : ℝ) ^ 3) * δ) := fun u v => by
    rw [abs_mul]
    exact mul_le_mul (hEb u v) (hterm u v) (abs_nonneg _) hδ
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun u _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => hterm2 u v)).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-- The combination `c₁ Z¹ + c₀ Z²` of the two independent fields is centered. -/
theorem integral_skVectorGaussianPairField_combination {d : ℕ} (q' q : Fin d → Fin d → ℝ) (c₁ c₀ :
  ℝ) (u : Fin d) :
    ∫ ω, (c₁ * skVectorGaussianPairField (Sum.inl u) ω + c₀ * skVectorGaussianPairField (Sum.inr
      u) ω)
      ∂(skVectorGaussianPairLaw 1 q' q) = 0 := by
  have hZ := hasGaussianLaw_skVectorGaussianPairField (d := d) 1 q' q
  have hint : ∀ k : Fin d ⊕ Fin d, Integrable (skVectorGaussianPairField k)
    (skVectorGaussianPairLaw 1 q' q) :=
    fun k => (hZ.eval k).integrable
  rw [integral_add ((hint _).const_mul c₁) ((hint _).const_mul c₀), integral_const_mul,
    integral_const_mul, integral_skVectorGaussianPairField, integral_skVectorGaussianPairField]
  simp

/-- Covariance of the combination `c₁ Z¹ + c₀ Z²` of the two independent fields. -/
theorem integral_skVectorGaussianPairField_combination_mul {d : ℕ} (q' q : Fin d → Fin d → ℝ)
    (hq' : (Matrix.of q').PosSemidef) (hq : (Matrix.of q).PosSemidef) (c₁ c₀ : ℝ) (u v : Fin d) :
    ∫ ω, (c₁ * skVectorGaussianPairField (Sum.inl u) ω + c₀ * skVectorGaussianPairField (Sum.inr
      u) ω) *
      (c₁ * skVectorGaussianPairField (Sum.inl v) ω + c₀ * skVectorGaussianPairField (Sum.inr v) ω)
      ∂(skVectorGaussianPairLaw 1 q' q) = c₁ ^ 2 * q' u v + c₀ ^ 2 * q u v := by
  have hZ := hasGaussianLaw_skVectorGaussianPairField (d := d) 1 q' q
  have h11 := integral_skVectorGaussianPairField_inl_mul 1 q' q hq'
  have h00 := integral_skVectorGaussianPairField_inr_mul 1 q' q hq
  have h10 := integral_skVectorGaussianPairField_inl_inr_mul 1 q' q
  have hint2 : ∀ k l : Fin d ⊕ Fin d, Integrable (fun ω => skVectorGaussianPairField k ω *
      skVectorGaussianPairField l ω) (skVectorGaussianPairLaw 1 q' q) := fun k l =>
    (hZ.eval k).memLp_two.integrable_mul (hZ.eval l).memLp_two
  have e : ∀ ω, (c₁ * skVectorGaussianPairField (Sum.inl u) ω + c₀ * skVectorGaussianPairField
    (Sum.inr u) ω) *
      (c₁ * skVectorGaussianPairField (Sum.inl v) ω + c₀ * skVectorGaussianPairField (Sum.inr v)
        ω) =
      c₁ ^ 2 * (skVectorGaussianPairField (Sum.inl u) ω * skVectorGaussianPairField (Sum.inl v) ω) +
      c₁ * c₀ * (skVectorGaussianPairField (Sum.inl u) ω * skVectorGaussianPairField (Sum.inr v)
        ω) +
      c₀ * c₁ * (skVectorGaussianPairField (Sum.inr u) ω * skVectorGaussianPairField (Sum.inl v)
        ω) +
      c₀ ^ 2 * (skVectorGaussianPairField (Sum.inr u) ω * skVectorGaussianPairField (Sum.inr v) ω)
        :=
    fun ω => by ring
  simp_rw [e]
  set Pm := skVectorGaussianPairLaw 1 q' q with hPm
  have iA : Integrable (fun ω => c₁ ^ 2 * (skVectorGaussianPairField (Sum.inl u) ω *
      skVectorGaussianPairField (Sum.inl v) ω)) Pm := (hint2 _ _).const_mul _
  have iB : Integrable (fun ω => c₁ * c₀ * (skVectorGaussianPairField (Sum.inl u) ω *
      skVectorGaussianPairField (Sum.inr v) ω)) Pm := (hint2 _ _).const_mul _
  have iC : Integrable (fun ω => c₀ * c₁ * (skVectorGaussianPairField (Sum.inr u) ω *
      skVectorGaussianPairField (Sum.inl v) ω)) Pm := (hint2 _ _).const_mul _
  have iD : Integrable (fun ω => c₀ ^ 2 * (skVectorGaussianPairField (Sum.inr u) ω *
      skVectorGaussianPairField (Sum.inr v) ω)) Pm := (hint2 _ _).const_mul _
  have iAB : Integrable (fun ω => c₁ ^ 2 * (skVectorGaussianPairField (Sum.inl u) ω *
      skVectorGaussianPairField (Sum.inl v) ω) + c₁ * c₀ * (skVectorGaussianPairField (Sum.inl u)
        ω *
      skVectorGaussianPairField (Sum.inr v) ω)) Pm := iA.add iB
  have iABC : Integrable (fun ω => c₁ ^ 2 * (skVectorGaussianPairField (Sum.inl u) ω *
      skVectorGaussianPairField (Sum.inl v) ω) + c₁ * c₀ * (skVectorGaussianPairField (Sum.inl u)
        ω *
      skVectorGaussianPairField (Sum.inr v) ω) + c₀ * c₁ * (skVectorGaussianPairField (Sum.inr u)
        ω *
      skVectorGaussianPairField (Sum.inl v) ω)) Pm := iAB.add iC
  rw [integral_add iABC iD, integral_add iAB iC, integral_add iA iB]
  simp only [integral_const_mul, h11, h00, h10]
  have h01 : ∫ ω, skVectorGaussianPairField (Sum.inr u) ω * skVectorGaussianPairField (Sum.inl v)
    ω ∂Pm = 0 := by
    rw [← h10 v u]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  rw [h01]
  ring

/-- **A combination of the two independent fields is a Gaussian field with the combined
covariance.**
For `Z` the pair of fields of covariances `q'`, `q` (with `β = 1`) and real coefficients `c₁`, `c₀`,
the field `c₁ Z¹ + c₀ Z²` has law `skVectorGaussianLaw β Q` whenever `β² Q = c₁² q' + c₀² q`. -/
theorem map_skVectorGaussianPairField_combination {d : ℕ} (q' q : Fin d → Fin d → ℝ) (hq' :
  (Matrix.of
    q').PosSemidef)
    (hq : (Matrix.of q).PosSemidef) (c₁ c₀ β : ℝ) (Q : Fin d → Fin d → ℝ)
    (hQ : ∀ u v, β ^ 2 * Q u v = c₁ ^ 2 * q' u v + c₀ ^ 2 * q u v) :
    (skVectorGaussianPairLaw 1 q' q).map (fun ω (u : Fin d) =>
        c₁ * skVectorGaussianPairField (Sum.inl u) ω + c₀ * skVectorGaussianPairField (Sum.inr u)
          ω) =
      skVectorGaussianLaw β Q := by
  have hZ := hasGaussianLaw_skVectorGaussianPairField (d := d) 1 q' q
  refine map_eq_skVectorGaussianLaw β Q ?_ (integral_skVectorGaussianPairField_combination q' q c₁
    c₀) ?_
  · have := hZ.map_fun (L := (ContinuousLinearMap.pi fun u : Fin d =>
      c₁ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ⊕ Fin d => ℝ) (Sum.inl u) +
      c₀ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ⊕ Fin d => ℝ) (Sum.inr u)))
    convert this using 2 with ω
    ext u
    simp
  · intro u v
    rw [integral_skVectorGaussianPairField_combination_mul q' q hq' hq, hQ]

/-- A combination of the two independent fields is a Gaussian vector. -/
theorem hasGaussianLaw_skVectorGaussianPairField_combination {d : ℕ} (q' q : Fin d → Fin d → ℝ)
    (hq' : (Matrix.of q').PosSemidef) (hq : (Matrix.of q).PosSemidef) (c₁ c₀ β : ℝ)
    (Q : Fin d → Fin d → ℝ) (hQ : ∀ u v, β ^ 2 * Q u v = c₁ ^ 2 * q' u v + c₀ ^ 2 * q u v) :
    HasGaussianLaw (fun ω (u : Fin d) =>
      c₁ * skVectorGaussianPairField (Sum.inl u) ω + c₀ * skVectorGaussianPairField (Sum.inr u) ω)
      (skVectorGaussianPairLaw 1 q' q) where
  aemeasurable := (measurable_pi_iff.2 fun u => (measurable_const.mul
    (measurable_skVectorGaussianPairField (Sum.inl u))).add (measurable_const.mul
    (measurable_skVectorGaussianPairField (Sum.inr u)))).aemeasurable
  isGaussian_map := by
    rw [map_skVectorGaussianPairField_combination q' q hq' hq c₁ c₀ β Q hQ]
    exact isGaussian_skVectorGaussianLaw β Q

/-- **Continuity of the segment free energy** (including the endpoints `s = 0, 1`, where `√s`,
`√(1 - s)` are not differentiable): `s ↦ 𝔼 log ∫ e^{segExp(clamp s)} dμ` is continuous. -/
theorem continuous_skVectorSegment_logPartition {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d)
    (ρ q₀ q₁ : Fin d → Fin d → ℝ) (b : ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Fin d ⊕ Fin d → Ω → ℝ} (hZm : ∀ l, Measurable (Z l)) (hZi : ∀ l, Integrable (Z l) P) :
    Continuous (fun s : ℝ => ∫ ω, Real.log (∫ a, Real.exp (skVectorFieldExponent ξ b ρ
      (fun u v => max 0 (min 1 s) * q₁ u v + (1 - max 0 (min 1 s)) * q₀ u v)
      (fun u => b * (Real.sqrt (max 0 (min 1 s)) * Z (.inl u) ω +
        Real.sqrt (1 - max 0 (min 1 s)) * Z (.inr u) ω)) a) ∂μ) ∂P) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxs : ∀ a u v, |ξ a u * ξ a v| ≤ d := fun a u v =>
    abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound a a u v
  set c : ℝ → ℝ := fun s => max 0 (min 1 s) with hc
  have hc0 : ∀ s, 0 ≤ c s := fun s => le_max_left _ _
  have hc1 : ∀ s, c s ≤ 1 := fun s => max_le zero_le_one (min_le_left _ _)
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  set D0 : α → ℝ := fun a => b ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q₀ w w') with hD0
  set X' : (Fin d ⊕ Fin d) ⊕ Unit → α → ℝ := Sum.elim (Sum.elim (fun u a => ξ a u) (fun u a => ξ a
      u))
    (fun _ a => b ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (q₁ w w' - q₀ w w')) with hX'
  set Eb : ℝ := b ^ 2 / 2 * ∑ w, ∑ w', d * |ρ w w' - q₀ w w'| with hEb
  set B : ℝ := Real.sqrt d + b ^ 2 / 2 * ∑ w, ∑ w', d * |q₁ w w' - q₀ w w'| with hB
  have hB0 : 0 ≤ B := by positivity
  have hξm2 : ∀ u v, Measurable fun a => ξ a u * ξ a v := measurable_spin_mul ξ hξ
  have hD0m : Measurable D0 :=
    measurable_const.mul (Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun w' _ =>
      (hξm2 w w').mul measurable_const)
  have hD0b : ∀ a, |D0 a| ≤ Eb := fun a => by
    simp only [hD0, hEb]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hxs a w w') (abs_nonneg _)
  have hX'm : ∀ k, Measurable (X' k) := by
    rintro ((u | u) | ⟨⟩)
    · exact hξ u
    · exact hξ u
    · exact measurable_const.mul (Finset.measurable_sum _ fun w _ => Finset.measurable_sum _
        fun w' _ => (hξm2 w w').mul measurable_const)
  have hX'b : ∀ k a, |X' k a| ≤ B := by
    have hnn : 0 ≤ b ^ 2 / 2 * ∑ w, ∑ w', (d : ℝ) * |q₁ w w' - q₀ w w'| := by positivity
    rintro ((u | u) | ⟨⟩) a
    · exact (hxb a u).trans (by simp only [hB]; linarith)
    · exact (hxb a u).trans (by simp only [hB]; linarith)
    · have e : X' (Sum.inr ()) a =
          b ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (q₁ w w' - q₀ w w') := rfl
      rw [e]
      refine le_trans ?_ (le_add_of_nonneg_left (Real.sqrt_nonneg _))
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hxs a w w') (abs_nonneg _)
  set zf : ℝ → Ω → (Fin d ⊕ Fin d) ⊕ Unit → ℝ := fun s ω => Sum.elim
    (Sum.elim (fun u => b * Real.sqrt (c s) * Z (.inl u) ω)
      (fun u => b * Real.sqrt (1 - c s) * Z (.inr u) ω)) (fun _ => -c s) with hzf
  have hzc : ∀ ω, Continuous fun s => zf s ω := fun ω => by
    refine continuous_pi_iff.2 ?_
    rintro ((u | u) | ⟨⟩)
    · exact (continuous_const.mul (Real.continuous_sqrt.comp hcc)).mul continuous_const
    · exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub hcc))).mul
        continuous_const
    · exact hcc.neg
  have hzm : ∀ s, Measurable (zf s) := fun s => by
    refine measurable_pi_iff.2 ?_
    rintro ((u | u) | ⟨⟩)
    · exact measurable_const.mul (hZm _)
    · exact measurable_const.mul (hZm _)
    · exact measurable_const
  set g : Ω → ℝ := fun ω => |b| * ∑ l, |Z l ω| + 1 with hg
  have hgi : Integrable g P :=
    ((integrable_finsetSum _ fun l _ => (hZi l).abs).const_mul |b|).add (integrable_const 1)
  have hgb : ∀ s ω l, |zf s ω l| ≤ g ω := by
    intro s ω l
    have hs0 := Real.sqrt_nonneg (c s)
    have hs1 : Real.sqrt (c s) ≤ 1 := Real.sqrt_le_one.2 (hc1 s)
    have ht0 := Real.sqrt_nonneg (1 - c s)
    have ht1 : Real.sqrt (1 - c s) ≤ 1 := Real.sqrt_le_one.2 (by linarith [hc0 s])
    have hsum : ∀ k : Fin d ⊕ Fin d, |Z k ω| ≤ ∑ l, |Z l ω| := fun k =>
      Finset.single_le_sum (f := fun l => |Z l ω|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have hsum0 : 0 ≤ ∑ l, |Z l ω| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases l with (u | u) | ⟨⟩
    · change |b * Real.sqrt (c s) * Z (.inl u) ω| ≤ g ω
      rw [abs_mul, abs_mul, abs_of_nonneg hs0]
      calc |b| * Real.sqrt (c s) * |Z (.inl u) ω| ≤ |b| * 1 * ∑ l, |Z l ω| :=
            mul_le_mul (mul_le_mul_of_nonneg_left hs1 (abs_nonneg _)) (hsum _) (abs_nonneg _)
              (by positivity)
        _ ≤ g ω := by simp only [hg]; linarith
    · change |b * Real.sqrt (1 - c s) * Z (.inr u) ω| ≤ g ω
      rw [abs_mul, abs_mul, abs_of_nonneg ht0]
      calc |b| * Real.sqrt (1 - c s) * |Z (.inr u) ω| ≤ |b| * 1 * ∑ l, |Z l ω| :=
            mul_le_mul (mul_le_mul_of_nonneg_left ht1 (abs_nonneg _)) (hsum _) (abs_nonneg _)
              (by positivity)
        _ ≤ g ω := by simp only [hg]; linarith
    · change |-c s| ≤ g ω
      rw [abs_neg, abs_of_nonneg (hc0 s)]
      simp only [hg]
      nlinarith [hc1 s, mul_nonneg (abs_nonneg b) hsum0]
  have hcont := continuous_integral_log_partition_path (μ := μ) (D := D0) (X := X') (B := B)
    (Eb := Eb) (P := P) hD0m hX'm hB0 hD0b hX'b hzc hzm hgi hgb
  convert hcont using 4 with s ω a
  simp only [skVectorFieldExponent, hD0, hX', hzf, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
  congr 2
  funext a
  congr 1
  have e1 : ∑ x, b * (Real.sqrt (c s) * Z (Sum.inl x) ω + Real.sqrt (1 - c s) * Z (Sum.inr x) ω) *
      ξ a x = ∑ x, b * Real.sqrt (c s) * Z (Sum.inl x) ω * ξ a x +
        ∑ x, b * Real.sqrt (1 - c s) * Z (Sum.inr x) ω * ξ a x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : ∑ u, ∑ v, ξ a u * ξ a v * (ρ u v - (c s * q₁ u v + (1 - c s) * q₀ u v)) =
      ∑ u, ∑ v, ξ a u * ξ a v * (ρ u v - q₀ u v) -
        c s * ∑ u, ∑ v, ξ a u * ξ a v * (q₁ u v - q₀ u v) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  simp only [hc] at e1 e2 ⊢
  rw [e1, e2]
  ring

/-- On the segment `q(s) = s q' + (1 - s) q` the free energy of the interpolated field is the
canonical free energy at `q(s)`. -/
theorem skVectorSegment_logPartition_eq {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) (ρ q q' : Fin d → Fin d → ℝ)
    (hq : (Matrix.of q).PosSemidef) (hq' : (Matrix.of q').PosSemidef) (b : ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, Real.log (∫ a, Real.exp (skVectorFieldExponent ξ b ρ
        (fun u v => s * q' u v + (1 - s) * q u v)
        (fun u => b * (Real.sqrt s * skVectorGaussianPairField (Sum.inl u) ω +
          Real.sqrt (1 - s) * skVectorGaussianPairField (Sum.inr u) ω)) a)
        ∂μ) ∂(skVectorGaussianPairLaw 1 q' q) =
      skVectorGaussianFreeEnergy μ ξ ρ (fun u v => s * q' u v + (1 - s) * q u v)
        (skVectorGaussianLaw 1 (fun u v => s * q' u v + (1 - s) * q u v)) (fun u y => y u) b := by
  have hQ : ∀ u v, (1 : ℝ) ^ 2 * (s * q' u v + (1 - s) * q u v) =
      Real.sqrt s ^ 2 * q' u v + Real.sqrt (1 - s) ^ 2 * q u v := fun u v => by
    rw [Real.sq_sqrt hs.1, Real.sq_sqrt (by linarith [hs.2])]; ring
  have hX := hasGaussianLaw_skVectorGaussianPairField_combination q' q hq' hq (Real.sqrt s)
    (Real.sqrt (1 - s)) 1
    _ hQ
  have hXm : ∀ u : Fin d, Measurable fun ω => Real.sqrt s * skVectorGaussianPairField (Sum.inl u)
    ω +
      Real.sqrt (1 - s) * skVectorGaussianPairField (Sum.inr u) ω := fun u =>
    (measurable_const.mul (measurable_skVectorGaussianPairField _)).add
      (measurable_const.mul (measurable_skVectorGaussianPairField _))
  have hcanon := skVectorGaussianFreeEnergy_eq_canonical μ ξ hξ ρ
    (fun u v => s * q' u v + (1 - s) * q u v)
    (P := skVectorGaussianPairLaw 1 q' q) hX hXm (integral_skVectorGaussianPairField_combination
      q' q _ _)
    (fun u v => by
      rw [integral_skVectorGaussianPairField_combination_mul q' q hq' hq, ← hQ u v]; ring) b
  simp_rw [skVectorFieldExponent_mul_left]
  exact hcanon

/-- The Gibbs means along the segment are the fixed-point map at `q(t)`. -/
theorem skVectorSegment_gibbs_eq {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (ρ q q' : Fin d → Fin d → ℝ)
    (hq : (Matrix.of q).PosSemidef) (hq' : (Matrix.of q').PosSemidef) (b : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u v : Fin d) :
    ∫ ω, (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ b ρ
        (fun u v => t * q' u v + (1 - t) * q u v)
        (fun w => b * (Real.sqrt t * skVectorGaussianPairField (Sum.inl w) ω +
          Real.sqrt (1 - t) * skVectorGaussianPairField (Sum.inr w) ω))))) *
      (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ b ρ
        (fun u v => t * q' u v + (1 - t) * q u v)
        (fun w => b * (Real.sqrt t * skVectorGaussianPairField (Sum.inl w) ω +
          Real.sqrt (1 - t) * skVectorGaussianPairField (Sum.inr w) ω)))))
        ∂(skVectorGaussianPairLaw 1 q' q) =
      (skVectorFixedPointMap μ ξ b (fun u v => t * q' u v + (1 - t) * q u v, ρ)).1 u v := by
  have hQ : ∀ u v, b ^ 2 * (t * q' u v + (1 - t) * q u v) =
      (b * Real.sqrt t) ^ 2 * q' u v + (b * Real.sqrt (1 - t)) ^ 2 * q u v := fun u v => by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht.1, Real.sq_sqrt (by linarith [ht.2])]; ring
  have hlaw := map_skVectorGaussianPairField_combination q' q hq' hq (b * Real.sqrt t) (b *
    Real.sqrt (1 - t)) b
    _ hQ
  have hYm : ∀ w : Fin d, Measurable fun ω => b * Real.sqrt t * skVectorGaussianPairField (Sum.inl
    w) ω +
      b * Real.sqrt (1 - t) * skVectorGaussianPairField (Sum.inr w) ω := fun w =>
    (measurable_const.mul (measurable_skVectorGaussianPairField _)).add
      (measurable_const.mul (measurable_skVectorGaussianPairField _))
  have hF : Measurable fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 1) v :=
    ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 1))
  have key := integral_skVectorFieldAverage_realization μ ξ hξ b ρ
    (fun u v => t * q' u v + (1 - t) * q u v) _ hF hYm hlaw
  simp only [skVectorFixedPointMap]
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [skVectorFieldAverage_pair μ ξ b ρ _ u v]
  have hdistr : (fun w => b * Real.sqrt t * skVectorGaussianPairField (Sum.inl w) ω +
      b * Real.sqrt (1 - t) * skVectorGaussianPairField (Sum.inr w) ω) =
    fun w => b * (Real.sqrt t * skVectorGaussianPairField (Sum.inl w) ω +
      Real.sqrt (1 - t) * skVectorGaussianPairField (Sum.inr w) ω) := by
    funext w; ring
  rw [hdistr]

/-- **Quadratic estimate in `q`.**  If `(q', ρ')` is a fixed point of `T_b` and `q` is within `δ`
of `q'`, moving `q` to `q'` (at fixed `ρ'`) changes the pressure by at most
`(b²/2) d² (1 + 18 b² d³) δ²`. -/
theorem abs_skVectorPressure_q_sub_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {b : ℝ} (hb : 0 < b) {q q' ρ' : Fin d → Fin d → ℝ}
    (hq : (Matrix.of q).PosSemidef) (hq' : (Matrix.of q').PosSemidef)
    (hfix : skVectorFixedPointMap μ ξ b (q', ρ') = (q', ρ')) {δ : ℝ} (hδ : 0 ≤ δ)
    (hqδ : ∀ u v, |q u v - q' u v| ≤ δ) :
    |skVectorPressure μ ξ b (q', ρ') - skVectorPressure μ ξ b (q, ρ')| ≤
      b ^ 2 / 2 * ((d : ℝ) * d * ((1 + 18 * b ^ 2 * (d : ℝ) ^ 3) * δ * δ)) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set P := skVectorGaussianPairLaw 1 q' q with hP
  set Z : Fin d ⊕ Fin d → (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) → ℝ :=
    skVectorGaussianPairField with hZdef
  have hZ := hasGaussianLaw_skVectorGaussianPairField (d := d) 1 q' q
  have hZm := measurable_skVectorGaussianPairField (d := d)
  have hZ0 := integral_skVectorGaussianPairField (d := d) 1 q' q
  have h11 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inl v) ω ∂P = q' u v := fun u v => by
    simpa using integral_skVectorGaussianPairField_inl_mul 1 q' q hq' u v
  have h00 : ∀ u v, ∫ ω, Z (.inr u) ω * Z (.inr v) ω ∂P = q u v := fun u v => by
    simpa using integral_skVectorGaussianPairField_inr_mul 1 q' q hq u v
  have h10 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inr v) ω ∂P = 0 :=
    integral_skVectorGaussianPairField_inl_inr_mul 1 q' q
  have hZi : ∀ l, Integrable (Z l) P := fun l => (hZ.eval l).integrable
  set qs : ℝ → Fin d → Fin d → ℝ := fun s u v => s * q' u v + (1 - s) * q u v with hqs
  have hqsPSD : ∀ s ∈ Set.Icc (0 : ℝ) 1, (Matrix.of (qs s)).PosSemidef := fun s hs => by
    have : Matrix.of (qs s) = s • Matrix.of q' + (1 - s) • Matrix.of q := by
      ext u v; simp [hqs]
    rw [this]
    exact (hq'.smul hs.1).add (hq.smul (by linarith [hs.2]))
  set φ : ℝ → ℝ := fun s => -(b ^ 2 / 4) * ∑ u, ∑ v,
      (ρ' u v ^ 2 - (s * q' u v + (1 - s) * q u v) ^ 2) +
      ∫ ω, Real.log (∫ a, Real.exp (skVectorFieldExponent ξ b ρ'
        (fun u v => s * q' u v + (1 - s) * q u v)
        (fun u => b * (Real.sqrt s * Z (.inl u) ω +
          Real.sqrt (1 - s) * Z (.inr u) ω)) a) ∂μ) ∂P with hφ
  have hφ_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, φ s = skVectorPressure μ ξ b (qs s, ρ') := fun s hs => by
    simp only [hφ, skVectorPressure]
    rw [skVectorSegment_logPartition_eq μ ξ hξ ρ' q q' hq hq' b hs]
    simp only [Finset.sum_sub_distrib, hqs]
  have hφ0 : φ 0 = skVectorPressure μ ξ b (q, ρ') := by
    rw [hφ_eq 0 ⟨le_rfl, zero_le_one⟩]
    congr 2
    funext u v; simp [hqs]
  have hφ1 : φ 1 = skVectorPressure μ ξ b (q', ρ') := by
    rw [hφ_eq 1 ⟨zero_le_one, le_rfl⟩]
    congr 2
    funext u v; simp [hqs]
  -- continuity on `[0, 1]`
  have hcont : ContinuousOn φ (Set.Icc 0 1) := by
    have h1 := continuous_skVectorSegment_logPartition μ ξ hξ hbound ρ' q q' b hZm hZi (P := P)
    have h2 : Continuous fun s : ℝ => -(b ^ 2 / 4) * ∑ u, ∑ v,
        (ρ' u v ^ 2 - (s * q' u v + (1 - s) * q u v) ^ 2) := by fun_prop
    refine (h2.add h1).continuousOn.congr fun s hs => ?_
    have hcl : max 0 (min 1 s) = s := by
      rw [min_eq_right hs.2, max_eq_right hs.1]
    simp only [hφ, Pi.add_apply, hcl]
    rfl
  have hder : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (b ^ 2 / 2 * ∑ u, ∑ v, (q' u v - q u v) *
      ((t * q' u v + (1 - t) * q u v) - ∫ ω,
        (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ b ρ'
          (fun u v => t * q' u v + (1 - t) * q u v)
          (fun w => b * (Real.sqrt t * Z (.inl w) ω +
            Real.sqrt (1 - t) * Z (.inr w) ω))))) *
        (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ b ρ'
          (fun u v => t * q' u v + (1 - t) * q u v)
          (fun w => b * (Real.sqrt t * Z (.inl w) ω +
            Real.sqrt (1 - t) * Z (.inr w) ω))))) ∂P)) t := fun t ht =>
    hasDerivAt_skVectorPressure_segment μ ξ hξ hr hbound ρ' q q' hZ hZm hZ0 h11 h00 h10 hb.ne'
      ht.1 ht.2
  have hdiff : DifferentiableOn ℝ φ (Set.Ioo 0 1) := fun t ht =>
    (hder t ht).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope φ zero_lt_one hcont hdiff
  rw [← hφ0, ← hφ1]
  have hE : φ 1 - φ 0 = deriv φ c := by rw [hcd]; ring
  rw [hE, (hder c hc).deriv, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcI : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  have hlip := abs_skVectorFixedPointMap_apply_sub_le μ ξ hξ hbound b (x := (qs c, ρ')) (x' :=
    (q', ρ'))
    (hqsPSD c hcI) hq' (δ := δ) (fun u v => by
      have : qs c u v - q' u v = (1 - c) * (q u v - q' u v) := by simp only [hqs]; ring
      change |qs c u v - q' u v| ≤ δ
      rw [this, abs_mul, abs_of_nonneg (by linarith [hc.2])]
      calc (1 - c) * |q u v - q' u v| ≤ 1 * δ :=
            mul_le_mul (by linarith [hc.1]) (hqδ u v) (abs_nonneg _) zero_le_one
        _ = δ := one_mul _) (fun u v => by simpa using hδ)
  have hterm : ∀ u v, |(q' u v - q u v) * ((c * q' u v + (1 - c) * q u v) -
      ∫ ω, (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ b ρ'
        (fun u v => c * q' u v + (1 - c) * q u v)
        (fun w => b * (Real.sqrt c * Z (.inl w) ω +
          Real.sqrt (1 - c) * Z (.inr w) ω))))) *
      (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ b ρ'
        (fun u v => c * q' u v + (1 - c) * q u v)
        (fun w => b * (Real.sqrt c * Z (.inl w) ω +
          Real.sqrt (1 - c) * Z (.inr w) ω))))) ∂P)| ≤
      δ * ((1 + 18 * b ^ 2 * (d : ℝ) ^ 3) * δ) := fun u v => by
    rw [abs_mul]
    refine mul_le_mul (by rw [abs_sub_comm]; exact hqδ u v) ?_ (abs_nonneg _) hδ
    have h1 := skVectorSegment_gibbs_eq μ ξ hξ ρ' q q' hq hq' b hcI u v
    rw [h1]
    have h2 := (hlip u v).1
    rw [hfix] at h2
    have h3 : |qs c u v - q' u v| ≤ δ := by
      have : qs c u v - q' u v = (1 - c) * (q u v - q' u v) := by simp only [hqs]; ring
      rw [this, abs_mul, abs_of_nonneg (by linarith [hc.2])]
      calc (1 - c) * |q u v - q' u v| ≤ 1 * δ :=
            mul_le_mul (by linarith [hc.1]) (hqδ u v) (abs_nonneg _) zero_le_one
        _ = δ := one_mul _
    calc |c * q' u v + (1 - c) * q u v -
          (skVectorFixedPointMap μ ξ b (fun u v => c * q' u v + (1 - c) * q u v, ρ')).1 u v| ≤
        |qs c u v - q' u v| + |q' u v - (skVectorFixedPointMap μ ξ b (qs c, ρ')).1 u v| :=
          abs_sub_le _ (q' u v) _
      _ ≤ δ + 18 * b ^ 2 * (d : ℝ) ^ 3 * δ := by
          refine add_le_add h3 ?_
          rw [abs_sub_comm]
          simpa using h2
      _ = _ := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun u _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => hterm u v)).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-- **The `β`-derivative of the pressure at a fixed point** (Eq. (1.393)): if `z = (q, ρ)` is a
fixed
point of `T_β` (`β ≠ 0`, `q ⪰ 0`) then `b ↦ G(b, z)` has derivative `(β/2) ∑ (ρ² - q²)` at `β`. -/
theorem hasDerivAt_skVectorPressure_beta {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β : ℝ} (hβ : β ≠ 0) {q ρ : Fin d → Fin d → ℝ}
    (hq : (Matrix.of q).PosSemidef) (hfix : skVectorFixedPointMap μ ξ β (q, ρ) = (q, ρ)) :
    HasDerivAt (fun b => skVectorPressure μ ξ b (q, ρ))
      (β / 2 * (∑ u, ∑ v, ρ u v ^ 2 - ∑ u, ∑ v, q u v ^ 2)) β := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := isGaussian_skVectorGaussianLaw 1 q
  set P := skVectorGaussianLaw 1 q with hP
  have hX : HasGaussianLaw (fun (y : Fin d → ℝ) (u : Fin d) => y u) P :=
      IsGaussian.hasGaussianLaw_id
  have hXm : ∀ u : Fin d, Measurable fun y : Fin d → ℝ => y u := fun u => measurable_pi_apply u
  have hX0 : ∀ u : Fin d, ∫ y : Fin d → ℝ, y u ∂P = 0 := fun u =>
    integral_skVectorGaussianLaw_coord 1
      q u
  have hXc : ∀ u v : Fin d, ∫ y : Fin d → ℝ, y u * y v ∂P = q u v := fun u v => by
    simpa using integral_skVectorGaussianLaw_mul 1 q hq u v
  -- the fixed-point equations in the form of `hasDerivAt_skVectorGaussianFreeEnergy`
  have hYg : HasGaussianLaw (fun (y : Fin d → ℝ) (u : Fin d) => β * y u) P := hX.mul (fun _ => β)
  have hYc : ∀ u v : Fin d, ∫ y : Fin d → ℝ, β * y u * (β * y v) ∂P = β ^ 2 * q u v := fun u v => by
    have : ∫ y : Fin d → ℝ, β * y u * (β * y v) ∂P = β ^ 2 * ∫ y, y u * y v ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [this, hXc]
  obtain ⟨hq', hρ'⟩ := (skVectorFixedPointMap_eq_iff_equations μ ξ hξ hbound β (q, ρ)
    (Y := fun (u : Fin d) (y : Fin d → ℝ) => β * y u) hYg
    (fun u => (measurable_const.mul (measurable_pi_apply u) : Measurable fun y : Fin d → ℝ =>
      β * y u))
    (fun u => by rw [integral_const_mul, hX0, mul_zero]) hYc).1 hfix
  have hd := hasDerivAt_skVectorGaussianFreeEnergy μ ξ hξ hr hbound ρ q hX hXm hX0
    (fun u v => by simpa using hXc u v) hβ hρ' hq'
  have hpoly : HasDerivAt (fun b : ℝ => -(b ^ 2 / 4) * (∑ u, ∑ v, ρ u v ^ 2 - ∑ u, ∑ v, q u v ^ 2))
      (-(β / 2) * (∑ u, ∑ v, ρ u v ^ 2 - ∑ u, ∑ v, q u v ^ 2)) β := by
    have := (((hasDerivAt_id β).pow 2).div_const 4).neg.mul_const
      (∑ u, ∑ v, ρ u v ^ 2 - ∑ u, ∑ v, q u v ^ 2)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, id_eq]
    ring
  have hsum : ∑ u, ∑ v, (ρ u v ^ 2 - q u v ^ 2) = ∑ u, ∑ v, ρ u v ^ 2 - ∑ u, ∑ v, q u v ^ 2 := by
    simp only [Finset.sum_sub_distrib]
  refine (hpoly.add hd).congr_deriv ?_
  rw [← hsum]
  ring

/-- **The two quadratic legs together**: if `z' = (q', ρ')` is a fixed point of `T_b` and
`z = (q, ρ)` has `q ⪰ 0` and sup-distance at most `δ` from `z'`, then
`|G(b, z') - G(b, z)| ≤ b² d² (1 + 18 b² d³) δ²`. -/
theorem abs_skVectorPressure_sub_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {b : ℝ} (hb : 0 < b)
    {z z' : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hz : (Matrix.of z.1).PosSemidef)
    (hz' : (Matrix.of z'.1).PosSemidef) (hfix : skVectorFixedPointMap μ ξ b z' = z') {δ : ℝ}
    (hδ : 0 ≤ δ) (hzδ : dist z z' ≤ δ) :
    |skVectorPressure μ ξ b z' - skVectorPressure μ ξ b z| ≤
      b ^ 2 * ((d : ℝ) * d * ((1 + 18 * b ^ 2 * (d : ℝ) ^ 3) * δ * δ)) := by
  have h1 : ∀ u v, |z.1 u v - z'.1 u v| ≤ δ := fun u v => by
    calc |z.1 u v - z'.1 u v| = dist (z.1 u v) (z'.1 u v) := (Real.dist_eq _ _).symm
      _ ≤ dist (z.1 u) (z'.1 u) := dist_le_pi_dist _ _ v
      _ ≤ dist z.1 z'.1 := dist_le_pi_dist _ _ u
      _ ≤ dist z z' := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ δ := hzδ
  have h2 : ∀ u v, |z.2 u v - z'.2 u v| ≤ δ := fun u v => by
    calc |z.2 u v - z'.2 u v| = dist (z.2 u v) (z'.2 u v) := (Real.dist_eq _ _).symm
      _ ≤ dist (z.2 u) (z'.2 u) := dist_le_pi_dist _ _ v
      _ ≤ dist z.2 z'.2 := dist_le_pi_dist _ _ u
      _ ≤ dist z z' := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ ≤ δ := hzδ
  have hz'fix : skVectorFixedPointMap μ ξ b (z'.1, z'.2) = (z'.1, z'.2) := hfix
  have hq := abs_skVectorPressure_q_sub_le μ ξ hξ hbound hb (q := z.1) (q' := z'.1) (ρ' := z'.2)
    hz hz' hz'fix hδ h1
  have hρ := abs_skVectorPressure_rho_sub_le μ ξ hξ hbound b (q := z.1) (ρ := z.2) (q' := z'.1)
    (ρ' := z'.2) hz hz' hz'fix hδ h1 h2
  have : skVectorPressure μ ξ b z' - skVectorPressure μ ξ b z =
      (skVectorPressure μ ξ b (z'.1, z'.2) - skVectorPressure μ ξ b (z.1, z'.2)) +
      (skVectorPressure μ ξ b (z.1, z'.2) - skVectorPressure μ ξ b (z.1, z.2)) := by
    simp
  rw [this]
  refine (abs_add_le _ _).trans ?_
  nlinarith [hq, hρ]

/-- **`F(β) = G(β, z(β))` is differentiable with derivative `(β/2) ∑ (ρ² - q²)`** for any family of
fixed points `z(b)` of `T_b` in the cone (proof of Theorem 1.12.3: the stationarity of `G` in `z`,
Lemma 1.12.6, makes the dependence of `z` on `β` second order). -/
theorem hasDerivAt_skVectorPressure_fixedPoint {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β β₁ : ℝ} (hβ : 0 < β) (hββ₁ : β < β₁)
    (hκ : 18 * β₁ ^ 2 * (d : ℝ) ^ 2 < 1)
    (z : ℝ → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ))
    (hz : ∀ b ∈ Set.Ioo (β / 2) β₁, z b ∈ skVectorFixedPointCone d ∧ skVectorFixedPointMap μ ξ b
      (z b) = z b)
        :
    HasDerivAt (fun b => skVectorPressure μ ξ b (z b))
      (β / 2 * (∑ u, ∑ v, (z β).2 u v ^ 2 - ∑ u, ∑ v, (z β).1 u v ^ 2)) β := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hβmem : β ∈ Set.Ioo (β / 2) β₁ := ⟨by linarith, hββ₁⟩
  set κ : ℝ := 18 * β₁ ^ 2 * (d : ℝ) ^ 2 with hκdef
  set κ₃ : ℝ := 18 * β₁ ^ 2 * (d : ℝ) ^ 3 with hκ₃def
  set K0 : ℝ := (d : ℝ) * d * d * (4 * 2 * (2 + 1) * d * d) +
    (d : ℝ) * d * (2 * d) * (2 * (2 + 1) * d * d) with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hβ₁0 : 0 < β₁ := by linarith
  set L : ℝ := β₁ * ((d : ℝ) * K0) / (1 - κ) with hL
  have hL0 : 0 ≤ L := by
    have : 0 < 1 - κ := by linarith
    exact div_nonneg (mul_nonneg (by linarith) (mul_nonneg hr hK00)) this.le
  -- Lipschitz dependence of the fixed point on `b`
  have hdist : ∀ b ∈ Set.Ioo (β / 2) β₁, dist (z b) (z β) ≤ L * |b - β| := by
    intro b hb
    have hb0 : 0 < b := by linarith [hb.1]
    have hbd := hz b hb
    have hβd := hz β hβmem
    rcases le_total b β with h | h
    · have h18 : 18 * b ^ 2 * (d : ℝ) ^ 2 < 1 := by
        have : b ^ 2 ≤ β₁ ^ 2 := by nlinarith [hb.2, hb0]
        have h4 : 0 ≤ (d : ℝ) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right this h4]
      have := skVectorFixedPoint_beta_dist_le μ ξ hξ hbound hb0 h h18 hbd.1 hβd.1 hbd.2 hβd.2
      refine this.trans ?_
      have hden : 1 - κ ≤ 1 - 18 * b ^ 2 * (d : ℝ) ^ 2 := by
        have : b ^ 2 ≤ β₁ ^ 2 := by nlinarith [hb.2, hb0]
        have h4 : 0 ≤ (d : ℝ) ^ 2 := by positivity
        simp only [hκdef]
        nlinarith [mul_le_mul_of_nonneg_right this h4]
      have hnum : (d : ℝ) * (β * K0 * (β - b)) ≤ β₁ * ((d : ℝ) * K0) * |b - β| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
        have := mul_le_mul (mul_le_mul_of_nonneg_right hββ₁.le hK00) le_rfl (sub_nonneg.2 h)
          (mul_nonneg hβ₁0.le hK00)
        nlinarith [mul_le_mul_of_nonneg_left this hr]
      calc (d : ℝ) * (β * K0 * (β - b)) / (1 - 18 * b ^ 2 * (d : ℝ) ^ 2) ≤
          β₁ * ((d : ℝ) * K0) * |b - β| / (1 - 18 * b ^ 2 * (d : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right hnum (by linarith)
        _ ≤ β₁ * ((d : ℝ) * K0) * |b - β| / (1 - κ) :=
            div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hβ₁0.le (mul_nonneg hr hK00))
              (abs_nonneg _)) (by linarith) hden
        _ = L * |b - β| := by simp only [hL]; ring
    · have h18 : 18 * β ^ 2 * (d : ℝ) ^ 2 < 1 := by
        have : β ^ 2 ≤ β₁ ^ 2 := by nlinarith [hββ₁, hβ]
        have h4 : 0 ≤ (d : ℝ) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right this h4]
      have := skVectorFixedPoint_beta_dist_le μ ξ hξ hbound hβ h h18 hβd.1 hbd.1 hβd.2 hbd.2
      rw [dist_comm]
      refine this.trans ?_
      have hden : 1 - κ ≤ 1 - 18 * β ^ 2 * (d : ℝ) ^ 2 := by
        have : β ^ 2 ≤ β₁ ^ 2 := by nlinarith [hββ₁, hβ]
        have h4 : 0 ≤ (d : ℝ) ^ 2 := by positivity
        simp only [hκdef]
        nlinarith [mul_le_mul_of_nonneg_right this h4]
      have hnum : (d : ℝ) * (b * K0 * (b - β)) ≤ β₁ * ((d : ℝ) * K0) * |b - β| := by
        rw [abs_of_nonneg (sub_nonneg.2 h)]
        have := mul_le_mul (mul_le_mul_of_nonneg_right hb.2.le hK00) le_rfl (sub_nonneg.2 h)
          (mul_nonneg hβ₁0.le hK00)
        nlinarith [mul_le_mul_of_nonneg_left this hr]
      calc (d : ℝ) * (b * K0 * (b - β)) / (1 - 18 * β ^ 2 * (d : ℝ) ^ 2) ≤
          β₁ * ((d : ℝ) * K0) * |b - β| / (1 - 18 * β ^ 2 * (d : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right hnum (by linarith)
        _ ≤ β₁ * ((d : ℝ) * K0) * |b - β| / (1 - κ) :=
            div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hβ₁0.le (mul_nonneg hr hK00))
              (abs_nonneg _)) (by linarith) hden
        _ = L * |b - β| := by simp only [hL]; ring
  have hz0 := hz β hβmem
  have hG1 := hasDerivAt_skVectorPressure_beta μ ξ hξ hbound hβ.ne' hz0.1.1 hz0.2
  rw [hasDerivAt_iff_isLittleO] at hG1 ⊢
  -- the second-order term
  set C0 : ℝ := β₁ ^ 2 * ((d : ℝ) * d * ((1 + κ₃) * L * L)) with hC0
  have hC00 : 0 ≤ C0 := by
    have : 0 ≤ 1 + κ₃ := by
      have : 0 ≤ κ₃ := by simp only [hκ₃def]; positivity
      linarith
    positivity
  have hA : (fun b => (skVectorPressure μ ξ b (z b) - skVectorPressure μ ξ b (z β))) =O[nhds β]
      fun b => (b - β) ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C0 ?_
    have hnb : ∀ᶠ b in nhds β, b ∈ Set.Ioo (β / 2) β₁ := Ioo_mem_nhds (by linarith) hββ₁
    filter_upwards [hnb] with b hb
    have hb0 : 0 < b := by linarith [hb.1]
    have hbd := hz b hb
    have hδ0 : 0 ≤ L * |b - β| := mul_nonneg hL0 (abs_nonneg _)
    have hd' : dist (z β) (z b) ≤ L * |b - β| := by rw [dist_comm]; exact hdist b hb
    have := abs_skVectorPressure_sub_le μ ξ hξ hbound hb0 hz0.1.1 hbd.1.1 hbd.2 hδ0 hd'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    refine this.trans ?_
    have hb2 : b ^ 2 ≤ β₁ ^ 2 := by nlinarith [hb.2, hb0]
    have hK : 18 * b ^ 2 * (d : ℝ) ^ 3 ≤ κ₃ := by
      simp only [hκ₃def]
      have h4 : 0 ≤ (d : ℝ) ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hb2 h4]
    have h5 : (1 + 18 * b ^ 2 * (d : ℝ) ^ 3) ≤ 1 + κ₃ := by linarith
    have hδsq : L * |b - β| * (L * |b - β|) = L * L * (b - β) ^ 2 := by
      rw [← sq_abs (b - β)]; ring
    calc b ^ 2 * ((d : ℝ) * d * ((1 + 18 * b ^ 2 * (d : ℝ) ^ 3) * (L * |b - β|) * (L * |b - β|)))
        ≤ β₁ ^ 2 * ((d : ℝ) * d * ((1 + κ₃) * (L * |b - β|) * (L * |b - β|))) := by
          refine mul_le_mul hb2 (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
            (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 hδ0) hδ0
      _ = C0 * (b - β) ^ 2 := by
          simp only [hC0]
          rw [← sq_abs (b - β)]
          ring
  have hA' : (fun b => (skVectorPressure μ ξ b (z b) - skVectorPressure μ ξ b (z β))) =o[nhds β]
      fun b => b - β := by
    refine hA.trans_isLittleO ?_
    have ht : Filter.Tendsto (fun b : ℝ => b - β) (nhds β) (nhds 0) := by
      simpa using (Filter.tendsto_id (x := nhds β)).sub_const β
    exact (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)).comp_tendsto ht
  have := hA'.add hG1
  refine this.congr_left fun b => ?_
  simp only [smul_eq_mul]
  ring

end SpinGlasses
