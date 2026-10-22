/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import LeanMachineLearning.SpinGlasses.GaussianInterpolationReplica
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound

/-!
# Nested two-replica Gibbs averages

For a random energy `E η ω` depending on two independent sources of disorder, the three-level
average `∫ η, ∫ ω, ∫ p, Θ p.1 p.2 ∂(tilted (E η ω) ⊗ tilted (E η ω))` of a deterministic
two-replica observable is monotone and affine in `Θ`.  These are the finite-measure
bookkeeping steps used by every interpolation estimate that compares two such averages.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

section Nested

variable {Ω₀ Ω α : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (P : Measure Ω) [IsProbabilityMeasure P]
  (E : Ω₀ → Ω → α → ℝ) (hE : ∀ a, Measurable (fun x : Ω₀ × Ω => E x.1 x.2 a))

include hE in
/-- Integrability of the inner levels of a nested two-replica average of a deterministic
observable. -/
theorem integrable_nested_prod_gibbs (Θ : α → α → ℝ) :
    (∀ η, Integrable (fun ω => ∫ p : α × α, Θ p.1 p.2
      ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) P) ∧
    Integrable (fun η => ∫ ω, ∫ p : α × α, Θ p.1 p.2
      ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P) P₀ := by
  refine ⟨fun η => integrable_integral_prod_count_tilted_det (P := P)
    (A := fun ω a => E η ω a) (fun a => (hE a).comp measurable_prodMk_left) Θ, ?_⟩
  exact (integrable_integral_prod_count_tilted_det (P := P₀.prod P)
    (A := fun (x : Ω₀ × Ω) a => E x.1 x.2 a) hE Θ).integral_prod_left

include hE in
/-- **Domination of a nested two-replica average.** -/
theorem abs_integral_nested_prod_gibbs_le {G H : α → α → ℝ} (hGH : ∀ a b, |G a b| ≤ H a b) :
    |∫ η, ∫ ω, ∫ p : α × α, G p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀| ≤
      ∫ η, ∫ ω, ∫ p : α × α, H p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀ := by
  obtain ⟨h2, h3⟩ := integrable_nested_prod_gibbs P₀ P E hE H
  exact abs_integral_integral_integral_le P₀ P
    (fun η ω => (Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))
    (G := fun _ _ p => G p.1 p.2) (H := fun _ _ p => H p.1 p.2) (fun _ _ p => hGH p.1 p.2)
    (fun _ _ => Integrable.of_finite) h2 h3

include hE in
/-- **Affine maps pass through a nested two-replica average.** -/
theorem integral_nested_prod_gibbs_affine (f : α → α → ℝ) (c₁ c₂ : ℝ) :
    ∫ η, ∫ ω, ∫ p : α × α, (c₁ * f p.1 p.2 + c₂)
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀ =
      c₁ * (∫ η, ∫ ω, ∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀) + c₂ := by
  obtain ⟨h2, h3⟩ := integrable_nested_prod_gibbs P₀ P E hE f
  have e1 (η : Ω₀) (ω : Ω) : (∫ p : α × α, (c₁ * f p.1 p.2 + c₂)
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) =
      c₁ * (∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) + c₂ := by
    rw [integral_add (Integrable.of_finite.const_mul c₁) (integrable_const c₂),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have e2 (η : Ω₀) : (∫ ω, (c₁ * (∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) + c₂) ∂P) =
      c₁ * (∫ ω, ∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P) + c₂ := by
    rw [integral_add ((h2 η).const_mul c₁) (integrable_const c₂), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  simp_rw [e1, e2]
  rw [integral_add (h3.const_mul c₁) (integrable_const c₂), integral_const_mul, integral_const,
    probReal_univ, one_smul]

end Nested

section TwoReplica

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Reindexing two replicas along an equivalence.** -/
theorem integral_prod_count_tilted_equiv (e : β ≃ α) (f : α → ℝ) (Θ : α → α → ℝ) :
    ∫ p : α × α, Θ p.1 p.2 ∂((Measure.count.tilted f).prod (Measure.count.tilted f)) =
      ∫ p : β × β, Θ (e p.1) (e p.2)
        ∂((Measure.count.tilted fun b => f (e b)).prod
          (Measure.count.tilted fun b => f (e b))) := by
  rw [integral_prod_count_tilted_eq_double_sum f Θ,
    integral_prod_count_tilted_eq_double_sum (fun b => f (e b)) (fun a b => Θ (e a) (e b)),
    ← e.sum_comp (fun a => Real.exp (f a))]
  congr 1
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← e.sum_comp]

end TwoReplica

/-- Summing an Ising sign against `exp (ε x)` gives `2 cosh x`. -/
theorem sum_units_int_exp_mul (x : ℝ) : (∑ s : ℤˣ, Real.exp ((s : ℝ) * x)) = 2 * Real.cosh x := by
  rw [sum_units_int]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [Real.cosh_eq]
  ring

section Units

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Two-replica average over an Ising last spin, without sign weights.**  Summing out the
last spins of two replicas of `A x.1 + x.2 L x.1` leaves the two-replica average weighted by
`cosh (L a) cosh (L b) / ⟨cosh L⟩²`. -/
theorem integral_prod_count_tilted_units [Finite α] [Nonempty α] (A L : α → ℝ)
    (g : α → α → ℝ) :
    ∫ p : (α × ℤˣ) × (α × ℤˣ), g p.1.1 p.2.1
      ∂((Measure.count.tilted fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1).prod
        (Measure.count.tilted fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1)) =
    (∫ p : α × α, g p.1 p.2 * Real.cosh (L p.1) * Real.cosh (L p.2)
      ∂((Measure.count.tilted A).prod (Measure.count.tilted A))) /
      (∫ a, Real.cosh (L a) ∂(Measure.count.tilted A)) ^ 2 := by
  let _ := Fintype.ofFinite α
  let At := fun x : α × ℤˣ => A x.1 + (x.2 : ℝ) * L x.1
  let ZA := ∑ a : α, Real.exp (A a)
  have hZt : (∑ x : α × ℤˣ, Real.exp (At x)) =
      2 * (ZA * ∫ a, Real.cosh (L a) ∂(Measure.count.tilted A)) := by
    rw [sum_exp_prod_units, mul_integral_count_tilted]
  have h_lhs := integral_prod_count_tilted_eq_double_sum (f := At)
    (Θ := fun x y => g x.1 y.1)
  have h_rhs := integral_prod_count_tilted_eq_double_sum (f := A)
    (Θ := fun a b => g a b * Real.cosh (L a) * Real.cosh (L b))
  have h_eval (a b : α) : (∑ s : ℤˣ, ∑ t : ℤˣ,
      Real.exp (A a + (s : ℝ) * L a) * Real.exp (A b + (t : ℝ) * L b) * g a b) =
      4 * (Real.exp (A a) * Real.exp (A b) * (g a b * Real.cosh (L a) * Real.cosh (L b))) := by
    have : (∑ s : ℤˣ, ∑ t : ℤˣ,
        Real.exp (A a + (s : ℝ) * L a) * Real.exp (A b + (t : ℝ) * L b) * g a b) =
        (Real.exp (A a) * Real.exp (A b) * g a b) *
          ((∑ s : ℤˣ, Real.exp ((s : ℝ) * L a)) * ∑ t : ℤˣ, Real.exp ((t : ℝ) * L b)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Real.exp_add]
      ring
    rw [this, sum_units_int_exp_mul, sum_units_int_exp_mul]
    ring
  have h_num : (∑ x : α × ℤˣ, ∑ y : α × ℤˣ,
      Real.exp (At x) * Real.exp (At y) * g x.1 y.1) =
      4 * ∑ a : α, ∑ b : α, Real.exp (A a) * Real.exp (A b) *
        (g a b * Real.cosh (L a) * Real.cosh (L b)) := by
    simp_rw [Fintype.sum_prod_type]
    have h_comm : (∑ a : α, ∑ s : ℤˣ, ∑ b : α, ∑ t : ℤˣ,
        Real.exp (At (a, s)) * Real.exp (At (b, t)) * g a b) =
        ∑ a : α, ∑ b : α, ∑ s : ℤˣ, ∑ t : ℤˣ,
          Real.exp (At (a, s)) * Real.exp (At (b, t)) * g a b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    rw [h_comm]
    simp only [At]
    simp_rw [h_eval, ← Finset.mul_sum]
  rw [h_lhs, hZt, h_num, h_rhs]
  rw [div_eq_mul_inv, inv_pow]
  dsimp only [ZA]
  ring

end Units

end SpinGlasses
