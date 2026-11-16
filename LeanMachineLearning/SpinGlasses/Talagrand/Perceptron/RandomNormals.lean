/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.StdGaussianDirection
public import LeanMachineLearning.SpinGlasses.Basic

/-!
# Gaussian versus spherical normals in the binary perceptron

Talagrand, *Spin Glasses* Vol. I, Section 2.1, opening paragraph: the constraint
`∑ i, g k i * σ i ≥ 0` only depends on the direction of the normal `g k`, so replacing the Gaussian
normal by the uniformly distributed unit normal `‖g k‖⁻¹ • g k` does not change the set of feasible
spins.  Together with `ProbabilityTheory.map_normalize_toLp_pi_pi_gaussianReal` (the normalized
rows are i.i.d. uniform on the sphere) this identifies the Gaussian model with the model of
independent uniform spherical normals.

## Main declarations

* `SpinGlasses.forall_nonneg_sum_mul_normalize_iff`: feasibility is unchanged by normalizing the
  rows of the disorder.
-/

@[expose] public section

open ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

variable {N M : ℕ}

/-- **Normalizing the normals does not change the feasible spins.**  For every disorder
`g : Fin M → Fin N → ℝ` and spin `σ`, all constraints `0 ≤ ∑ i, g k i * σ i` hold iff all hold for
the unit normals `‖g k‖⁻¹ • g k` (a zero row stays zero and satisfies its constraint). -/
theorem forall_nonneg_sum_mul_normalize_iff (g : Fin M → Fin N → ℝ) (σ : Fin N → ℤˣ) :
    (∀ k, 0 ≤ ∑ i, g k i * ((σ i : ℤ) : ℝ)) ↔
      ∀ k, 0 ≤ ∑ i, (‖WithLp.toLp 2 (g k)‖⁻¹ • WithLp.toLp 2 (g k) :
        EuclideanSpace ℝ (Fin N)) i * ((σ i : ℤ) : ℝ) := by
  refine forall_congr' fun k => ?_
  have h : ∀ v : EuclideanSpace ℝ (Fin N),
      inner ℝ (WithLp.toLp 2 fun i => ((σ i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin N)) v =
        ∑ i, v i * ((σ i : ℤ) : ℝ) := fun v => by
    simp [PiLp.inner_apply]
  have h1 : ∑ i, g k i * ((σ i : ℤ) : ℝ) = inner ℝ
      (WithLp.toLp 2 fun i => ((σ i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin N)) (WithLp.toLp 2 (g k)) :=
    (h (WithLp.toLp 2 (g k))).symm
  rw [h1, ← h]
  exact (inner_nonneg_normalize_iff (WithLp.toLp 2 (g k)) _).symm

end SpinGlasses
