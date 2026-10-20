/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityOuterBound

/-!
# Averaging the conditional cavity derivative

The new-edge/scalar interpolation can be differentiated with the old disorder
held fixed.  This module supplies the one missing analytic step: a uniformly
bounded conditional derivative remains differentiable after averaging any
independent old disorder.  The base energy is deliberately an argument rather
than an SK-specific definition, so this applies to other finite cavity models.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Average the conditional cavity derivative over arbitrary independent base
disorder.  The sole model-specific inputs are a measurable base energy and the
explicit last-spin fields; no cavity Gibbs-measure wrapper is introduced. -/
theorem hasDerivAt_integral_cavity_outer
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    [Nonempty Ω₀] (N n : ℕ) (β q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (B : Ω₀ → (Fin (N + 1) → ℤˣ) → ℝ) (hB : ∀ a, Measurable (fun η => B η a))
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (M : ℝ) (hf : ∀ σ, |f σ| ≤ M) (t : ℝ) :
    HasDerivAt (fun s =>
      ∫ η, ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
                (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
              Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B η a))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) ∂P₀)
      (∫ η, Real.sin t * Real.cos t *
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
                (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
              Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B η a))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) ∂P₀) t := by
  have hq0 : 0 ≤ q := hq.1
  let P : Measure ((Fin N → ℝ) × ℝ) :=
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
  let E : ℝ → Ω₀ → (Fin N → ℝ) × ℝ → (Fin (N + 1) → ℤˣ) → ℝ := fun s η ω a =>
    Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
      (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
    Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B η a
  let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)))
  let C : ℝ := 2 * (n : ℝ) * (2 * (n : ℝ) + 1) * (2 * β ^ 2)
  let F : ℝ → Ω₀ → ℝ := fun s η =>
    ∫ ω : (Fin N → ℝ) × ℝ,
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s η ω)) ∂P
  let D : ℝ → Ω₀ → ℝ := fun s η => Real.sin s * Real.cos s *
    ∫ ω : (Fin N → ℝ) × ℝ,
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (some (some r))) *
          ((∑ r : Fin n, ∑ r' : Fin n,
              U (τ (some (some r))) (τ (some (some r')))) -
            2 * (n : ℝ) * ∑ r : Fin n, U (τ (some (some r))) (τ (some none)) -
            (n : ℝ) * U (τ (some none)) (τ (some none)) +
            (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) =>
          Measure.count.tilted (E s η ω)) ∂P
  have hEm (s : ℝ) (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : Ω₀ × ((Fin N → ℝ) × ℝ) => E s x.1 x.2 a) := by
    dsimp [E]
    fun_prop
  have hFm : ∀ s, AEStronglyMeasurable (F s) P₀ := by
    intro s
    have hm : Measurable (fun x : Ω₀ × ((Fin N → ℝ) × ℝ) =>
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s x.1 x.2))) := by
      classical
      simp_rw [integral_pi_count_tilted]
      exact Finset.measurable_fun_sum _ fun σ _ =>
        (Finset.measurable_fun_prod _ fun r _ =>
          ((hEm s (σ r)).exp.div
            (Finset.measurable_fun_sum _ fun a _ => (hEm s a).exp))).mul measurable_const
    exact hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hDm : AEStronglyMeasurable (D t) P₀ := by
    have hm : Measurable (fun x : Ω₀ × ((Fin N → ℝ) × ℝ) =>
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ r : Fin n, ∑ r' : Fin n,
                U (τ (some (some r))) (τ (some (some r')))) -
              2 * (n : ℝ) * ∑ r : Fin n, U (τ (some (some r))) (τ (some none)) -
              (n : ℝ) * U (τ (some none)) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none))
          ∂(Measure.pi fun _ : Option (Option (Fin n)) =>
            Measure.count.tilted (E t x.1 x.2))) := by
      classical
      simp_rw [integral_pi_count_tilted]
      exact Finset.measurable_fun_sum _ fun τ _ =>
        (Finset.measurable_fun_prod _ fun r _ =>
          ((hEm t (τ r)).exp.div
            (Finset.measurable_fun_sum _ fun a _ => (hEm t a).exp))).mul measurable_const
    refine (stronglyMeasurable_const.mul ?_).aestronglyMeasurable
    exact hm.stronglyMeasurable.integral_prod_right'
  have hFi : Integrable (F t) P₀ := by
    refine Integrable.of_bound (hFm t) M (ae_of_all _ fun η => ?_)
    rw [Real.norm_eq_abs]
    dsimp [F]
    simpa only [Real.norm_eq_abs, P, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := P) (f := fun ω =>
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E t η ω)))
      (C := M) (ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs] using abs_integral_pi_count_tilted_le _ hf)
  have hderiv : ∀ η s, HasDerivAt (fun u => F u η) (D s η) s := by
    intro η s
    simpa only [F, D, E, U, P, Fintype.card_fin] using
      hasDerivAt_integral_cavity_conditional N n β q hq0 (B η) f s
  have hbound : ∀ η s, |D s η| ≤ M * C := by
    intro η s
    simpa only [D, E, U, C, P] using
      abs_cavity_conditional_derivative_le N n β q hq (B η) f M hf s
  simpa only [F, D, E, U, P] using
    hasDerivAt_integral_conditional_of_deriv_bound P₀ F D t hFm hDm hFi hderiv (M * C) hbound

/-- The old-pair-disorder specialization of the averaged cavity derivative.
It is the angle form of the analytic part of Talagrand's Lemma 1.6.3; the
next algebraic step cancels its constant diagonal and rewrites the ordered
off-diagonal sum. -/
theorem hasDerivAt_integral_sk_cavity_path_angle (N n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (t : ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    HasDerivAt (fun s =>
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
                (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
              Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
      (∫ g', Real.sin t * Real.cos t *
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
                (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
              Real.sin t * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) t := by
  dsimp
  obtain ⟨M, hM⟩ : ∃ M, ∀ σ, |f σ| ≤ M :=
    (Set.finite_range fun σ => |f σ|).bddAbove.imp fun M hM σ => hM ⟨σ, rfl⟩
  apply hasDerivAt_integral_cavity_outer
  · exact hq
  · intro a
    fun_prop
  · exact hM

end SpinGlasses
