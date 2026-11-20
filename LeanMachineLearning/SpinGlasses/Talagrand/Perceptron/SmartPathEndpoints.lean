/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.AuxiliaryMarginal
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathModel
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.GaussianFieldSplit
public import LeanMachineLearning.SpinGlasses.Gibbs.GibbsReplicaMarginal
public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# The original perceptron Gibbs law at the terminal smart-path endpoint

At `t = 1` the auxiliary Gaussian spins and last field drop out. The energy no longer depends on
the auxiliary coordinates, so they are integrated out with
`integral_pi_tilted_prod_fst_of_forall`; the old and last spin are then concatenated with the
shared measurable equivalence. This recovers the Section 2.1 Gibbs law with full normalization.
The argument needs no hypothesis on the potential: the energy no longer depends on the auxiliary
coordinates and the spin space is finite.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SpinGlasses

/-- A spin-only replica average at `t = 1` equals its original `(N + 1)`-spin Gibbs average.
This includes empty replica and constraint types, and one full spin. No hypothesis on `u` is
needed: at `t = 1` the energy does not depend on the auxiliary coordinates, and the spin space is
finite, so every exponential is integrable and every observable is measurable. -/
theorem integral_pi_perceptron_smart_path_one {N M : ℕ} {R : Type*} [Fintype R] (u : ℝ → ℝ)
    (g : Fin M → Fin (N + 1) → ℝ) (y : ℝ)
    (F : (R → Fin (N + 1) → ℤˣ) → ℝ) :
    ∫ x : R → SmartPathState N M,
      F (fun r => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x r).1.1 (x r).1.2)
      ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted
        (smartPathEnergy u 1 ((fun k i => g k i.castSucc, fun k => g k (Fin.last N)), y))) =
    ∫ σ : R → Fin (N + 1) → ℤˣ, F σ ∂(Measure.pi fun _ : R =>
      (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
      (fun τ : Fin (N + 1) → ℤˣ =>
        ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))) := by
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (MeasurableEquiv.finSuccProd ℤˣ N).symm.toEquiv
  have he (σ : (Fin N → ℤˣ) × ℤˣ) : e σ = Fin.snoc σ.1 σ.2 :=
    MeasurableEquiv.finSuccProd_symm_apply N σ
  let H : (Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))
  have hreindex := integral_pi_count_tilted_equiv (R := R) e H F
  refine Eq.trans ?_ hreindex.symm
  set ω : SmartPathDisorder N M := ((fun k i => g k i.castSucc, fun k => g k (Fin.last N)), y)
  have hH : (fun σ => H (e σ)) = fun σ => ∑ k, u (smartPathFieldNoAux 1 ω (σ, 0) k) := by
    funext σ
    dsimp only [H]
    rw [he]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    simpa only [smartPathFieldNoAux, div_one, one_div, Real.sqrt_inv, Nat.cast_add,
      Nat.cast_one] using normalized_constraint_field_snoc σ.1 σ.2 (g k)
  have hEn : smartPathEnergy u 1 ω = fun x : SmartPathState N M =>
      ∑ k, u (smartPathFieldNoAux 1 ω (x.1, 0) k) := by
    funext x
    simp [smartPathEnergy_eq, smartPathField_eq, smartPathFieldNoAux_eq]
  rw [hH, hEn, smartPathBase_eq]
  have := integral_pi_tilted_prod_fst_of_forall (μ := (Measure.count : Measure (PerceptronSpin N)))
    (ν := Measure.pi fun _ : Fin M => gaussianReal 0 1) (R := R)
    (E₁ := fun σ : PerceptronSpin N => ∑ k, u (smartPathFieldNoAux 1 ω (σ, 0) k))
    Integrable.of_finite (f := fun σ : R → PerceptronSpin N => F (fun r => e (σ r)))
    (measurable_of_finite _)
  simpa only [he] using this

end SpinGlasses
