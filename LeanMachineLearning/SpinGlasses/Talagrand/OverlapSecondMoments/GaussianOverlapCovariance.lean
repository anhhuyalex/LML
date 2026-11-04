/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram

/-!
# Covariances of the Gaussian reference for centered overlaps

The pair coordinate and the two endpoint coordinates form a centered Gaussian
linear form. Its covariance counts common pair and endpoint labels. This calculation
does not use the SK model or an ordering on the replica set.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The centered Gaussian family `U_xy + U_x + U_y` and its covariance, including
repeated endpoint labels. No replica order or spin-glass hypothesis is needed. -/
theorem gaussian_overlap_reference {R : Type*} [Fintype R] [DecidableEq R]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let G := fun (p : R × R) (z : (R × R) ⊕ R → ℝ) =>
      Real.sqrt a * z (.inl p) + Real.sqrt b * z (.inr p.1) +
        Real.sqrt b * z (.inr p.2)
    let P := Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1
    HasGaussianLaw (fun z p => G p z) P ∧
      (∀ p, ∫ z, G p z ∂P = 0) ∧ ∀ p q,
    (∫ z, G p z * G q z
      ∂(Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1)) =
        (if p = q then a else 0) + b *
          ((if p.1 = q.1 then 1 else 0) + (if p.1 = q.2 then 1 else 0) +
            (if p.2 = q.1 then 1 else 0) + (if p.2 = q.2 then 1 else 0)) := by
  intro G P
  let c := fun p : R × R =>
    (Pi.single (.inl p) (Real.sqrt a) : (R × R) ⊕ R → ℝ) +
      Pi.single (.inr p.1) (Real.sqrt b) + Pi.single (.inr p.2) (Real.sqrt b)
  have hlin (p : R × R) (z : (R × R) ⊕ R → ℝ) : G p z = c p ⬝ᵥ z := by
    simp [G, c, add_dotProduct]
  refine ⟨?_, ?_, fun p q => ?_⟩
  · simpa only [hlin] using hasGaussianLaw_dotProduct_family c
  · intro p
    simp_rw [hlin]
    exact integral_dotProduct_pi_gaussianReal (c p)
  simp_rw [hlin]
  rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
  simp [c, dotProduct_add, Pi.single_apply, add_mul, mul_add, ite_mul, mul_ite, ← sq,
    Real.sq_sqrt ha, Real.sq_sqrt hb, eq_comm]
  ring

/-- For ordered distinct pairs, the covariance has the three cases in Talagrand's
discussion after (1.295): identical pairs, one common endpoint, or disjoint pairs. -/
theorem gaussian_overlap_covariance_of_lt {R : Type*} [Fintype R] [LinearOrder R]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p q : R × R)
    (hp : p.1 < p.2) (hq : q.1 < q.2) :
    let G := fun (p : R × R) (z : (R × R) ⊕ R → ℝ) =>
      Real.sqrt a * z (.inl p) + Real.sqrt b * z (.inr p.1) +
        Real.sqrt b * z (.inr p.2)
    (∫ z, G p z * G q z
      ∂(Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1)) =
        if p = q then a + 2 * b else
          if (({p.1, p.2} : Finset R) ∩ {q.1, q.2}).Nonempty then b else 0 := by
  intro G
  rw [(gaussian_overlap_reference ha hb).2.2 p q]
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  dsimp only at hp hq ⊢
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    by_cases hyu : y = u <;> by_cases hyv : y = v <;>
    simp_all [eq_comm]
  all_goals first | (exfalso; order) | ring

end SpinGlasses
