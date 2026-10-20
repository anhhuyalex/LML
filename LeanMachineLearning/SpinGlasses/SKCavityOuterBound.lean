/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityBounds

/-!
# Bounded cavity replica derivative

This is the uniform-in-the-old-disorder estimate for the conditional Gaussian
replica derivative. It is valid for an arbitrary deterministic base energy.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The derivative in the cavity angle is bounded independently of the base energy.
This estimate is the domination required when the old pair couplings are integrated out. -/
theorem abs_cavity_conditional_derivative_le (N n : ℕ) (β q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (A : (Fin (N + 1) → ℤˣ) → ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (M : ℝ) (hf : ∀ σ, |f σ| ≤ M) (t : ℝ) :
    |Real.sin t * Real.cos t *
      ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ r : Fin n, ∑ r' : Fin n,
                β ^ 2 * (τ (some (some r)) (Fin.last N) : ℝ) *
                  (τ (some (some r')) (Fin.last N) : ℝ) *
                  (q - (N + 1 : ℝ)⁻¹ *
                    ((fun i : Fin N => (τ (some (some r)) i.castSucc : ℝ)) ⬝ᵥ
                      fun i : Fin N => (τ (some (some r')) i.castSucc : ℝ)))) -
              2 * (n : ℝ) * ∑ r : Fin n,
                β ^ 2 * (τ (some (some r)) (Fin.last N) : ℝ) *
                  (τ (some none) (Fin.last N) : ℝ) *
                  (q - (N + 1 : ℝ)⁻¹ *
                    ((fun i : Fin N => (τ (some (some r)) i.castSucc : ℝ)) ⬝ᵥ
                      fun i : Fin N => (τ (some none) i.castSucc : ℝ))) -
              (n : ℝ) * (β ^ 2 * (τ (some none) (Fin.last N) : ℝ) *
                (τ (some none) (Fin.last N) : ℝ) *
                (q - (N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (τ (some none) i.castSucc : ℝ)) ⬝ᵥ
                    fun i : Fin N => (τ (some none) i.castSucc : ℝ)))) +
              (n : ℝ) * ((n : ℝ) + 1) *
                (β ^ 2 * (τ (some none) (Fin.last N) : ℝ) *
                  (τ none (Fin.last N) : ℝ) *
                  (q - (N + 1 : ℝ)⁻¹ *
                    ((fun i : Fin N => (τ (some none) i.castSucc : ℝ)) ⬝ᵥ
                      fun i : Fin N => (τ none i.castSucc : ℝ)))))
          ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
                (a (Fin.last N) : ℝ) *
                  ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
              Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))| ≤
      M * (2 * (n : ℝ) * (2 * (n : ℝ) + 1) * (2 * β ^ 2)) := by
  let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (b i.castSucc : ℝ)))
  let C : ℝ := 2 * (n : ℝ) * (2 * (n : ℝ) + 1) * (2 * β ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf (Classical.arbitrary _))
  have hφ : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
      |f (fun r => τ (some (some r))) *
        ((∑ r : Fin n, ∑ r' : Fin n,
            U (τ (some (some r))) (τ (some (some r')))) -
          2 * (n : ℝ) * ∑ r : Fin n,
            U (τ (some (some r))) (τ (some none)) -
          (n : ℝ) * U (τ (some none)) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))| ≤ M * C := by
    intro τ
    rw [abs_mul]
    apply mul_le_mul (hf _) ?_ (abs_nonneg _) hM
    simpa only [Fintype.card_fin, C] using
      abs_replica_covariance_combination_le U (2 * β ^ 2)
        (abs_sk_cavity_covariance_le N β q hq) τ
  have hinner (ω : (Fin N → ℝ) × ℝ) :
      |∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (some (some r))) *
          ((∑ r : Fin n, ∑ r' : Fin n,
              U (τ (some (some r))) (τ (some (some r')))) -
            2 * (n : ℝ) * ∑ r : Fin n,
              U (τ (some (some r))) (τ (some none)) -
            (n : ℝ) * U (τ (some none)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
              (a (Fin.last N) : ℝ) *
                ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
            Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a))| ≤
        M * C := by
    exact abs_integral_pi_count_tilted_le _ hφ
  have hm : AEStronglyMeasurable (fun ω : (Fin N → ℝ) × ℝ =>
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (some (some r))) *
          ((∑ r : Fin n, ∑ r' : Fin n,
              U (τ (some (some r))) (τ (some (some r')))) -
            2 * (n : ℝ) * ∑ r : Fin n,
              U (τ (some (some r))) (τ (some none)) -
            (n : ℝ) * U (τ (some none)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
              (a (Fin.last N) : ℝ) *
                ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
            Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a)))
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply (aemeasurable_integral_pi_count_tilted
      (μ := (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      (g := fun ω a =>
        Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
          (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
        Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a)
      (Θ := fun _ τ => f (fun r => τ (some (some r))) *
        ((∑ r : Fin n, ∑ r' : Fin n,
            U (τ (some (some r))) (τ (some (some r')))) -
          2 * (n : ℝ) * ∑ r : Fin n,
            U (τ (some (some r))) (τ (some none)) -
            (n : ℝ) * U (τ (some none)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none)))
      (fun a => ((show Measurable (fun ω : (Fin N → ℝ) × ℝ =>
        Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
          (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
        Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a)
        from by fun_prop).aemeasurable))
      (fun τ => aemeasurable_const)).aestronglyMeasurable
  have hi : Integrable (fun ω : (Fin N → ℝ) × ℝ =>
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (some (some r))) *
          ((∑ r : Fin n, ∑ r' : Fin n,
              U (τ (some (some r))) (τ (some (some r')))) -
            2 * (n : ℝ) * ∑ r : Fin n,
              U (τ (some (some r))) (τ (some none)) -
            (n : ℝ) * U (τ (some none)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
              (a (Fin.last N) : ℝ) *
                ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
            Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a)))
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    Integrable.of_bound hm (M * C)
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hinner ω)
  have houter := norm_integral_le_of_norm_le_const
    (μ := (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    (f := fun ω : (Fin N → ℝ) × ℝ =>
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (some (some r))) *
          ((∑ r : Fin n, ∑ r' : Fin n,
              U (τ (some (some r))) (τ (some (some r')))) -
            2 * (n : ℝ) * ∑ r : Fin n,
              U (τ (some (some r))) (τ (some none)) -
            (n : ℝ) * U (τ (some none)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
              (a (Fin.last N) : ℝ) *
                ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
            Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a)))
    (C := M * C) (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hinner ω)
  change |Real.sin t * Real.cos t *
    (∫ ω : (Fin N → ℝ) × ℝ,
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (some (some r))) *
          ((∑ r : Fin n, ∑ r' : Fin n,
              U (τ (some (some r))) (τ (some (some r')))) -
            2 * (n : ℝ) * ∑ r : Fin n,
              U (τ (some (some r))) (τ (some none)) -
            (n : ℝ) * U (τ (some none)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            Real.cos t * ((Real.sqrt (N + 1))⁻¹ * β *
              (a (Fin.last N) : ℝ) *
                ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
            Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + A a))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)))| ≤ M * C
  rw [abs_mul]
  have ht : |Real.sin t * Real.cos t| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one t) (Real.abs_cos_le_one t)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  exact (mul_le_mul ht (by simpa [Real.norm_eq_abs] using houter)
    (abs_nonneg _) (by positivity)).trans_eq (one_mul _)

end SpinGlasses
