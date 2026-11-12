/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.Pressure

/-!
# The pressure is `O(β)` at small `β`

For `‖q‖_F, ‖ρ‖_F ≤ d` the replica-symmetric pressure satisfies
`|G(b, (q, ρ))| ≤ b² d²/2 + |b| d² + b² d³`, so `F(b) = G(b, z(b)) → 0` as `b → 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- `∫ |y_u| dγ ≤ √(q_uu)` for the centered Gaussian field of covariance `q`. -/
theorem integral_abs_skVectorGaussianLaw_le {d : ℕ} (q : Fin d → Fin d → ℝ)
    (hq : (Matrix.of q).PosSemidef) (u : Fin d) :
    ∫ y, |y u| ∂(skVectorGaussianLaw 1 q) ≤ Real.sqrt (q u u) := by
  have := isGaussian_skVectorGaussianLaw 1 q
  have hZ : HasGaussianLaw (fun (y : Fin d → ℝ) (k : Fin d) => y k) (skVectorGaussianLaw 1 q) :=
    IsGaussian.hasGaussianLaw_id
  have hmem : MemLp (fun y : Fin d → ℝ => y u) 2 (skVectorGaussianLaw 1 q) := (hZ.eval u).memLp_two
  have hm2 : MemLp (fun y : Fin d → ℝ => |y u|) 2 (skVectorGaussianLaw 1 q) := hmem.abs
  have hvar := variance_nonneg (fun y : Fin d → ℝ => |y u|) (skVectorGaussianLaw 1 q)
  rw [variance_eq_sub hm2] at hvar
  have hsq : ∫ y : Fin d → ℝ, (fun y => |y u|) y ^ 2 ∂(skVectorGaussianLaw 1 q) = q u u := by
    have := integral_skVectorGaussianLaw_mul 1 q hq u u
    simp only [one_pow, one_mul] at this
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [sq]
      exact abs_mul_abs_self _)
  have h1 : (∫ y : Fin d → ℝ, |y u| ∂(skVectorGaussianLaw 1 q)) ^ 2 ≤ q u u := by
    simp only [Pi.pow_apply] at hvar
    nlinarith [hsq]
  exact Real.le_sqrt_of_sq_le h1

/-- **The pressure is small for small `b`.**  For `q ⪰ 0` and `‖q‖_F, ‖ρ‖_F ≤ d`,
`|G(b, (q, ρ))| ≤ b² d²/2 + |b| d² + b² d³`. -/
theorem abs_skVectorPressure_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (b : ℝ)
    {z : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hz : (Matrix.of z.1).PosSemidef) (hq2 : ∑ u, ∑ v, z.1 u v ^ 2 ≤ (d : ℝ) ^ 2)
    (hρ2 : ∑ u, ∑ v, z.2 u v ^ 2 ≤ (d : ℝ) ^ 2) :
    |skVectorPressure μ ξ b z| ≤
      b ^ 2 * (d : ℝ) ^ 2 / 2 + |b| * (d : ℝ) ^ 2 + b ^ 2 * (d : ℝ) ^ 3 := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxs : ∀ a u v, |ξ a u * ξ a v| ≤ d := fun a u v =>
    abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound a a u v
  -- the entries and the sums of absolute values of the matrices
  have habs : ∀ M : Fin d → Fin d → ℝ, ∑ u, ∑ v, M u v ^ 2 ≤ (d : ℝ) ^ 2 →
      ∑ u, ∑ v, |M u v| ≤ (d : ℝ) ^ 2 := fun M hM => by
    have h1 : ∀ u v, |M u v| ≤ (M u v ^ 2 + 1) / 2 := fun u v => by
      nlinarith [sq_nonneg (|M u v| - 1), sq_abs (M u v)]
    calc ∑ u, ∑ v, |M u v| ≤ ∑ u, ∑ v, (M u v ^ 2 + 1) / 2 :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h1 u v
      _ = (∑ u, ∑ v, M u v ^ 2 + (d : ℝ) ^ 2) / 2 := by
          simp only [← Finset.sum_div, Finset.sum_add_distrib]
          simp [sq]
      _ ≤ (d : ℝ) ^ 2 := by linarith
  have hqu : ∀ u, z.1 u u ≤ d := fun u =>
    (le_abs_self _).trans (abs_entry_le_of_sum_sq_le z.1 hq2 u u)
  have hsq1 : ∑ u, ∑ v, |z.1 u v| ≤ (d : ℝ) ^ 2 := habs _ hq2
  have hsq2 : ∑ u, ∑ v, |z.2 u v| ≤ (d : ℝ) ^ 2 := habs _ hρ2
  set Dm : α → ℝ := fun a => b ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (z.2 u v - z.1 u v) with hDm
  have hDmeas : Measurable Dm := by
    refine Measurable.const_mul (Finset.measurable_sum _ fun u _ =>
      Finset.measurable_sum _ fun v _ => ?_) _
    exact (measurable_spin_mul ξ hξ u v).mul_const _
  have hDb : ∀ a, |Dm a| ≤ b ^ 2 * (d : ℝ) ^ 3 := fun a => by
    have h1 : |∑ u, ∑ v, ξ a u * ξ a v * (z.2 u v - z.1 u v)| ≤
        ∑ u, ∑ v, (d : ℝ) * (|z.2 u v| + |z.1 u v|) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (hxs a u v) ((abs_sub _ _)) (abs_nonneg _) hr
    have h2 : ∑ u, ∑ v, (d : ℝ) * (|z.2 u v| + |z.1 u v|) ≤ 2 * (d : ℝ) ^ 3 := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib]
      nlinarith
    rw [hDm]
    simp only
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 2)]
    nlinarith [sq_nonneg b]
  have hpt : ∀ y : Fin d → ℝ, |Real.log (∫ a, Real.exp (b * ∑ u, y u * ξ a u +
      b ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (z.2 u v - z.1 u v)) ∂μ)| ≤
      b ^ 2 * (d : ℝ) ^ 3 + |b| * Real.sqrt d * ∑ u, |y u| := fun y => by
    have := abs_log_partition_le (μ := μ) (D := Dm) (X := fun u a => ξ a u) hDmeas hξ hDb
      (fun u a => hxb a u) (fun k => b * y k)
    rw [probReal_univ, Real.log_one, abs_zero, zero_add] at this
    have heq : (fun a => Real.exp (b * ∑ u, y u * ξ a u +
        b ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (z.2 u v - z.1 u v))) =
        fun a => Real.exp (Dm a + ∑ k, b * y k * ξ a k) := by
      funext a
      have hs : b * ∑ u, y u * ξ a u = ∑ k, b * y k * ξ a k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hs, add_comm]
    rw [heq]
    refine this.trans ?_
    have : ∑ k, |b * y k| * Real.sqrt d = |b| * Real.sqrt d * ∑ u, |y u| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [abs_mul]; ring
    linarith
  have hmeas := measurable_skVectorLogPartition μ ξ hξ b z.2 z.1
  have hint : ∀ u, Integrable (fun y : Fin d → ℝ => |y u|) (skVectorGaussianLaw 1 z.1) := fun u =>
    by
    have := isGaussian_skVectorGaussianLaw 1 z.1
    have hZ : HasGaussianLaw (fun (y : Fin d → ℝ) (k : Fin d) => y k) (skVectorGaussianLaw 1 z.1) :=
      IsGaussian.hasGaussianLaw_id
    exact ((hZ.eval u).memLp_two.abs).integrable one_le_two
  have hI : Integrable (fun y : Fin d → ℝ => b ^ 2 * (d : ℝ) ^ 3 +
      |b| * Real.sqrt d * ∑ u, |y u|) (skVectorGaussianLaw 1 z.1) :=
    (integrable_const _).add ((integrable_finsetSum _ fun u _ => hint u).const_mul _)
  have hLint : Integrable (fun y : Fin d → ℝ => Real.log (∫ a, Real.exp (b * ∑ u, y u * ξ a u +
      b ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (z.2 u v - z.1 u v)) ∂μ)) (skVectorGaussianLaw 1 z.1) :=
    hI.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hpt y)
  have hG : |skVectorGaussianFreeEnergy μ ξ z.2 z.1 (skVectorGaussianLaw 1 z.1) (fun u y => y u)
    b| ≤
      b ^ 2 * (d : ℝ) ^ 3 + |b| * (d : ℝ) ^ 2 := by
    unfold skVectorGaussianFreeEnergy
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono hLint.abs hI (fun y => hpt y)).trans ?_
    rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun u _ => hint u).const_mul _),
      integral_const_mul (|b| * Real.sqrt d), integral_finsetSum _ fun u _ => hint u]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have h3 : ∑ u, ∫ y : Fin d → ℝ, |y u| ∂(skVectorGaussianLaw 1 z.1) ≤ d * Real.sqrt d := by
      calc _ ≤ ∑ _u : Fin d, Real.sqrt d := Finset.sum_le_sum fun u _ =>
            (integral_abs_skVectorGaussianLaw_le z.1 hz u).trans (Real.sqrt_le_sqrt (hqu u))
        _ = d * Real.sqrt d := by simp
    have h4 : |b| * Real.sqrt d * (d * Real.sqrt d) = |b| * (d : ℝ) ^ 2 := by
      calc |b| * Real.sqrt d * (d * Real.sqrt d)
          = |b| * d * (Real.sqrt d * Real.sqrt d) := by ring
        _ = |b| * (d : ℝ) ^ 2 := by rw [Real.mul_self_sqrt hr]; ring
    have h5 : |b| * Real.sqrt d * ∑ u, ∫ y : Fin d → ℝ, |y u| ∂(skVectorGaussianLaw 1 z.1) ≤
        |b| * Real.sqrt d * (d * Real.sqrt d) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hfirst : |-(b ^ 2 / 4) * (∑ u, ∑ v, z.2 u v ^ 2 - ∑ u, ∑ v, z.1 u v ^ 2)| ≤
      b ^ 2 * (d : ℝ) ^ 2 / 2 := by
    have h0 : 0 ≤ ∑ u, ∑ v, z.1 u v ^ 2 := Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h0' : 0 ≤ ∑ u, ∑ v, z.2 u v ^ 2 := Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hd : |∑ u, ∑ v, z.2 u v ^ 2 - ∑ u, ∑ v, z.1 u v ^ 2| ≤ (d : ℝ) ^ 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 4)]
    have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ b ^ 2 / 4)
    nlinarith [sq_nonneg b, sq_nonneg (d : ℝ), mul_nonneg (sq_nonneg b) (sq_nonneg (d : ℝ))]
  unfold skVectorPressure
  refine (abs_add_le _ _).trans ?_
  linarith

end SpinGlasses
