/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProdFactorization
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityDecomposition

/-!
# The interpolating system of the cavity in `M`

Talagrand Section 2.3, (2.33)--(2.35). Each replica carries the configuration `x` of the full
system and one more Gaussian coordinate `ξ`; the quenched randomness is the disorder `ω` of the
full system and one shared Gaussian `z`. With `θ = √q z + √(1-q) ξ` and the path parameter `s`, the
field is `S_s = cos s · S_{M,t} + sin s · θ` and the energy of the interpolating system is the old
energy (2.30) plus `u(S_s)`; `v = cos² s`. The average `ν_{t,v}` is not a new object: it is the
replica average under the product of `((μ × 𝒩(0,1)).tilted E_s)`.

* `integral_pi_tilted_cavityPath_eq_div`: the identity (2.35), a ratio of averages of the
  system whose energy is the old energy, with `V = u(S_s)`;
* `integral_pi_tilted_cavityPath_zero`: `ν_{t,1} = ν_t`: at `s = 0` the new coordinate is unused and
  the average of a function of the configurations is the average of the full system.

Replica consistency and the permutation symmetry of replicas follow from
`MeasureTheory.integral_pi_comp_injective` applied to the Gibbs law, a probability measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N M : ℕ} {μ : Measure (SmartPathState N (M + 1))} [IsFiniteMeasure μ] {u : ℝ → ℝ}
  {D : ℝ} (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t q s z : ℝ)
  (ω : SmartPathDisorder N (M + 1))

include hu hD in
/-- **The identity (2.35).** The replica average of an arbitrary function `Y` of the extended
configurations `(x, ξ)` under the interpolating system is the average of `Y exp ∑ u(S_s^ℓ)` for the
system with the old energy (the new coordinate `ξ` is a spectator), divided by the `|R|`-th power
of the one-replica average of `exp u(S_s)`. -/
theorem integral_pi_tilted_cavityPath_eq_div {R : Type*} [Fintype R]
    (Y : (R → SmartPathState N (M + 1) × ℝ) → ℝ) :
    ∫ σ, Y σ ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
      fun p : SmartPathState N (M + 1) × ℝ =>
        smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
          u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
            Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
      (∫ σ, Y σ * Real.exp (∑ r, u (Real.cos s * smartPathField t ω (σ r).1 (Fin.last M) +
            Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ r).2)))
          ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
            fun p : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
                (p.1.1, Fin.init p.1.2))) /
        (∫ p, Real.exp (u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
            Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))
          ∂((μ.prod (gaussianReal 0 1)).tilted fun p : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
              (p.1.1, Fin.init p.1.2))) ^ Fintype.card R :=
  integral_pi_tilted_add_eq_div (μ := μ.prod (gaussianReal 0 1)) (ι := R)
    ((integrable_exp_smartPathEnergy_init (μ := μ) hu hD t ω).comp_fst _)
    (V := fun p : SmartPathState N (M + 1) × ℝ => u (Real.cos s *
      smartPathField t ω p.1 (Fin.last M) +
      Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) Y

/-- **`⟨·⟩_{t,1} = ⟨·⟩_t` at fixed disorder.** At `s = 0` the field is `S_{M,t}` and the new
coordinate `ξ` does not enter the energy, so a function of the configurations has the same average
as under the Gibbs law of the full system with `M + 1` constraints. No hypothesis on `u` or on the
observable is needed: the new Gibbs factor is `γ.tilted 0 = γ`. Integrating this equality over the
disorder and `z` gives `ν_{t,1} = ν_t`. -/
theorem integral_pi_tilted_cavityPath_zero {R : Type*} [Fintype R]
    (f : (R → SmartPathState N (M + 1)) → ℝ) :
    ∫ σ : R → SmartPathState N (M + 1) × ℝ, f (fun r => (σ r).1)
      ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
        fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos 0 * smartPathField t ω p.1 (Fin.last M) +
              Real.sin 0 * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
      ∫ a, f a ∂(Measure.pi fun _ : R => μ.tilted (smartPathEnergy u t ω)) := by
  have e : (fun p : SmartPathState N (M + 1) × ℝ =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos 0 * smartPathField t ω p.1 (Fin.last M) +
          Real.sin 0 * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
      fun p => smartPathEnergy u t ω p.1 + (0 : ℝ → ℝ) p.2 := by
    funext p
    rw [smartPathEnergy_eq_init_add u t ω p.1]
    simp
  have h := integral_pi_tilted_prod_add_mul (μ := μ) (ν := gaussianReal 0 1) (ι := R)
    (smartPathEnergy u t ω) (0 : ℝ → ℝ) f (fun _ => 1)
  rw [e]
  simpa using h

end SpinGlasses
