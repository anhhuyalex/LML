/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Negation invariance of product measures

A finite product of probability measures that are invariant under `x ↦ -x` is invariant under
`f ↦ -f`. In particular a product of centered Gaussians has the same integrals after the
substitution `g ↦ -g`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

/-- A product measure is invariant under pointwise negation when every marginal is. -/
theorem Measure.pi_map_neg_eq {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    [Neg α] [MeasurableNeg α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, (μ i).map (fun x : α => -x) = μ i) :
    (Measure.pi μ).map (fun f : ι → α => -f) = Measure.pi μ := by
  have hIndep : iIndepFun (fun i : ι => fun f : ι → α => -f i) (Measure.pi μ) :=
    iIndepFun_pi (μ := μ) (X := fun _ : ι => fun x : α => -x)
      (mX := fun _ => (by fun_prop : Measurable fun x : α => -x).aemeasurable)
  have hmap := iIndepFun.map_fun_eq_pi_map
    (μ := Measure.pi μ)
    (f := fun (i : ι) (f : ι → α) => -f i)
    (hf := fun i => (by fun_prop : Measurable fun f : ι → α => -f i).aemeasurable)
    hIndep
  calc
    (Measure.pi μ).map (fun f : ι → α => -f)
        = Measure.pi (fun i : ι => (Measure.pi μ).map (fun f : ι → α => -f i)) := hmap
    _ = Measure.pi (fun i : ι => (μ i).map (fun x : α => -x)) := by
          congr 1
          funext i
          calc
            (Measure.pi μ).map (fun f : ι → α => -f i)
                = ((Measure.pi μ).map (fun f : ι → α => f i)).map (fun x : α => -x) :=
                  (Measure.map_map (g := fun x : α => -x) (f := fun f : ι → α => f i)
                    (by fun_prop : Measurable fun x : α => -x) (measurable_pi_apply i)).symm
            _ = (μ i).map (fun x : α => -x) :=
                  congrArg (fun ν : Measure α => ν.map (fun x : α => -x))
                    (measurePreserving_eval μ i).map_eq
    _ = Measure.pi μ := congrArg Measure.pi (funext hμ)

/-- **The standard Gaussian vector is symmetric:** `𝔼 F(-g) = 𝔼 F(g)` for the product of
standard Gaussians. -/
theorem integral_neg_pi_gaussianReal {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) :
    ∫ g : ι → ℝ, F (-g) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ g : ι → ℝ, F g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hneg : ∀ _i : ι, (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := fun _ => by
    rw [gaussianReal_map_neg, neg_zero]
  have hmp : MeasurePreserving (MeasurableEquiv.neg (ι → ℝ))
      (Measure.pi fun _ : ι => gaussianReal 0 1) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.neg (ι → ℝ)).measurable,
      Measure.pi_map_neg_eq (fun _ : ι => gaussianReal 0 1) hneg⟩
  exact hmp.integral_comp' F

/-- A standard Gaussian is symmetric: `𝔼 f(-z) = 𝔼 f(z)`. -/
theorem integral_neg_gaussianReal (f : ℝ → ℝ) :
    ∫ z : ℝ, f (-z) ∂(gaussianReal 0 1) = ∫ z : ℝ, f z ∂(gaussianReal 0 1) := by
  have hmp : MeasurePreserving (MeasurableEquiv.neg ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.neg ℝ).measurable, by
      rw [show (⇑(MeasurableEquiv.neg ℝ) : ℝ → ℝ) = fun x => -x from rfl, gaussianReal_map_neg,
        neg_zero]⟩
  exact hmp.integral_comp' f

end MeasureTheory
