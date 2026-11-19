/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDisorderDerivative
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPPotential
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityBounds

/-!
# Definitions and algebraic preparations for Gaussian integration by parts

This module introduces the minimal set of definitions for the perceptron smart path
(Talagrand Section 2.2, (2.15)--(2.16) and (2.27)--(2.28)), along with the algebraic
prefactors and two-replica difference identities for Gaussian integration by parts:

1. **Type abbreviations and core definitions:**
   `PerceptronSpin`, `SmartPathState`, `SmartPathDisorder`, `smartPathField`,
   `smartPathEnergy`, `smartPathEnergyDerivA`, `smartPathEnergyDerivXi`,
   `smartPathEnergyDerivY`, `smartPathBase`, `smartPathDisorder`, and `SmartPathPotential`.

2. **Auxiliary spin prefactor cancellation:**
   `(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1)) = - 1 / (2 * (N + 1))`
   cancels the `√(1 - t)` denominator in Term IV.

3. **Quenched disorder prefactor cancellation:**
   `(1 / (2 * √(N + 1))) * (1 / √t) * √(t / (N + 1)) = 1 / (2 * (N + 1))`
   cancels the `√t` denominator in Term III.

4. **Exact diagonal cancellation:**
   The diagonal terms `+1 / (2 * (N + 1))` and `-1 / (2 * (N + 1))` cancel identically.

5. **Constraint symmetry reduction:**
   `sum_div_eq_alpha_mul_last` reduces a sum of `1 / (N + 1)` over all `M + 1` constraints
   to `(M + 1) / (N + 1)` times the last constraint value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped BigOperators NNReal

namespace SpinGlasses

/-! ### D1. Type abbreviations -/

/-- Old spins and the last spin. -/
abbrev PerceptronSpin (N : ℕ) := (Fin N → ℤˣ) × ℤˣ

/-- The smart-path configuration: spins and the auxiliary Gaussian coordinates `ξ`. -/
abbrev SmartPathState (N M : ℕ) := PerceptronSpin N × (Fin M → ℝ)

/-- Quenched disorder `((g, a), y)`. -/
abbrev SmartPathDisorder (N M : ℕ) := ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ

/-! ### D2. Field, energy and the energy derivative components -/

/-- The smart-path field `S_{k,s}` of (2.15). -/
noncomputable def smartPathField {N M : ℕ} (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) (k : Fin M) : ℝ :=
  (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
    Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
    Real.sqrt ((1 - s) / (N + 1)) * x.2 k

/-- The smart-path energy `-H_{N,M,s}` of (2.16). -/
noncomputable def smartPathEnergy {N M : ℕ} (u : ℝ → ℝ) (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (smartPathField s ω x k)

/-- The quenched disorder derivative component of (2.27)/(2.28). -/
noncomputable def smartPathEnergyDerivA {N M : ℕ} (u : ℝ → ℝ) (s : ℝ)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) : ℝ :=
  ∑ k, deriv u (smartPathField s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
    (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s))

/-- The auxiliary coordinate derivative component of (2.27)/(2.28). -/
noncomputable def smartPathEnergyDerivXi {N M : ℕ} (u : ℝ → ℝ) (s : ℝ)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) : ℝ :=
  ∑ k, deriv u (smartPathField s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
    (- x.2 k / Real.sqrt (1 - s)))

/-- The last-field derivative component of (2.27)/(2.28). -/
noncomputable def smartPathEnergyDerivY {N M : ℕ} (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) : ℝ :=
  -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s))

/-- The pointwise derivative (2.27) with the three pieces: `E'_a + E'_ξ + E'_Y`,
as one statement (replaces `hasDerivAt_perceptron_smart_path_energy` plus
`perceptron_smart_path_E'_eq_three_terms`). -/
theorem hasDerivAt_smartPathEnergy {N M : ℕ} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) :
    HasDerivAt (fun s => smartPathEnergy u s ω x)
      (smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
        smartPathEnergyDerivY t ω x) t := by
  have h := hasDerivAt_perceptron_smart_path_energy ht (fun z => hu z) ω.1.1 ω.1.2 x.2 x.1.1
    x.1.2 ω.2
  refine h.congr_deriv ?_
  simp only [smartPathEnergyDerivA, smartPathEnergyDerivXi, smartPathEnergyDerivY,
    smartPathField]
  rw [← Finset.sum_add_distrib, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### D3. Base and disorder laws -/

/-- Counting measure on spins times standard Gaussian auxiliary coordinates. -/
noncomputable def smartPathBase (N M : ℕ) : Measure (SmartPathState N M) :=
  (Measure.count : Measure (PerceptronSpin N)).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)

instance (N M : ℕ) : IsFiniteMeasure (smartPathBase N M) := by
  unfold smartPathBase; infer_instance

instance (N M : ℕ) : NeZero (smartPathBase N M) := by
  unfold smartPathBase; infer_instance

/-- Quenched disorder law: old rows `Pold`, standard Gaussian `a`, and `y ∼ 𝒩(0, v)`. -/
noncomputable def smartPathDisorder {N M : ℕ} (Pold : Measure (Fin M → Fin N → ℝ))
    (v : ℝ≥0) : Measure (SmartPathDisorder N M) :=
  (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)

/-! ### D4. Bundled potential hypothesis -/

/-- The potential hypotheses of (2.7) used by the smart-path derivative: differentiable,
`|u| ≤ B`, `|u'| ≤ D`. -/
structure SmartPathPotential (u : ℝ → ℝ) (B D : ℝ) : Prop where
  differentiable : Differentiable ℝ u
  abs_le : ∀ z, |u z| ≤ B
  abs_deriv_le : ∀ z, |deriv u z| ≤ D

/-! ### D6. Interaction kernels -/

/-- Cross-replica interaction kernel of potential derivatives (term I). -/
noncomputable def smartPathPotentialKernel {N M : ℕ} (u : ℝ → ℝ) (t : ℝ)
    (ω : SmartPathDisorder N M) (k : Fin M) (x y : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k) *
    deriv u (smartPathField t ω y k)

/-- Last-spin interaction kernel (term II). -/
def lastSpinKernel {N M : ℕ} (x y : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ)

/-! ### Three-term expansion restated with the definitions -/

/-- **(2.26)-(2.28)** restated with the definitions; proved from the existing theorem. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms'
    {N M : ℕ} {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    HasDerivAt (fun s => ∫ ω, ∫ σ, F σ
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (∫ ω, replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω)) F
            (smartPathEnergyDerivA u t ω) +
          replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω)) F
            (smartPathEnergyDerivXi u t ω) +
          replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω)) F
            (smartPathEnergyDerivY t ω) ∂smartPathDisorder Pold v) t :=
  hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms ht hu.differentiable
    hu.abs_le hu.abs_deriv_le v F hF hFb

/-- **(2.26)-(2.28)** for spin-only observables restated with the definitions. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms_spin_only'
    {N M : ℕ} {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (∫ ω, replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
            (fun σ => f (fun r => (σ r).1)) (smartPathEnergyDerivA u t ω) +
          replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
            (fun σ => f (fun r => (σ r).1)) (smartPathEnergyDerivXi u t ω) +
          replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
            (fun σ => f (fun r => (σ r).1)) (smartPathEnergyDerivY t ω)
            ∂smartPathDisorder Pold v) t :=
  hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms_spin_only ht hu.differentiable
    hu.abs_le hu.abs_deriv_le v f (Pold := Pold)

/-! ### Algebraic prefactors and replica combination identities -/

/-- Simplification of the auxiliary spin prefactor: the product
`(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1))` simplifies to
`- 1 / (2 * (N + 1))`, cancelling the `√(1 - t)` denominator. -/
theorem perceptron_smart_path_auxiliary_prefactor {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  push_cast
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hsqN : (Real.sqrt ((N : ℝ) + 1)) ^ 2 = ((N : ℝ) + 1) := Real.sq_sqrt hN.le
  have hsqrt_t : Real.sqrt (1 - t) ≠ 0 := Real.sqrt_ne_zero'.mpr ht1
  rw [Real.sqrt_div ht1.le]
  have hmul : (1 / (2 * Real.sqrt ((N : ℝ) + 1))) * (- (1 / Real.sqrt (1 - t))) *
      (Real.sqrt (1 - t) / Real.sqrt ((N : ℝ) + 1)) =
      - ((1 / (2 * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1)))) *
         (Real.sqrt (1 - t) / Real.sqrt (1 - t))) := by ring
  rw [hmul, div_self hsqrt_t, mul_one, ← sq, hsqN]

/-- Simplification of the quenched disorder prefactor: the product
`(1 / (2 * √(N + 1))) * (1 / √t) * √(t / (N + 1))` simplifies to `1 / (2 * (N + 1))`,
cancelling the `√t` denominator. -/
theorem perceptron_smart_path_quenched_prefactor {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (1 / Real.sqrt t) *
      Real.sqrt (t / (N + 1 : ℕ)) =
    (1 / (2 * (N + 1 : ℝ))) := by
  push_cast
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht0 : 0 < t := ht.1
  have hsqN : (Real.sqrt ((N : ℝ) + 1)) ^ 2 = ((N : ℝ) + 1) := Real.sq_sqrt hN.le
  have hsqrt_t : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht0
  rw [Real.sqrt_div ht0.le]
  have hmul : (1 / (2 * Real.sqrt ((N : ℝ) + 1))) * (1 / Real.sqrt t) *
      (Real.sqrt t / Real.sqrt ((N : ℝ) + 1)) =
      ((1 / (2 * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1)))) *
       (Real.sqrt t / Real.sqrt t)) := by ring
  rw [hmul, div_self hsqrt_t, mul_one, ← sq, hsqN]

/-- Connection with the 4-term replica covariance combination from `SKCavityBounds.lean`:
for any kernel with constant diagonal, `replicaPairDiff` is exactly half of the 4-term
combination. -/
theorem replicaPairDiff_eq_half_replica_covariance_combination
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    replicaPairDiff U τ =
      ((∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, U (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            U (τ (some none)) (τ none)) / 2 := by
  rw [replica_covariance_combination_eq_two_sum_lt U C hdiag hsym τ]
  dsimp only [replicaPairDiff]
  ring

/-- Constraint symmetry reduction: for `M + 1` constraints, if every constraint
yields the same value as the last constraint `Fin.last M`, the sum of `1 / (N + 1)`
over all constraints equals `(M + 1) / (N + 1)` times the last constraint value. -/
theorem sum_div_eq_alpha_mul_last {N M : ℕ} (f : Fin (M + 1) → ℝ)
    (hconst : ∀ k : Fin (M + 1), f k = f (Fin.last M)) :
    (∑ k : Fin (M + 1), (1 / (N + 1 : ℝ)) * f k) =
      ((M + 1 : ℝ) / (N + 1 : ℝ)) * f (Fin.last M) := by
  have hsum : (∑ k : Fin (M + 1), f k) = (M + 1 : ℝ) * f (Fin.last M) := by
    rw [Finset.sum_congr rfl (fun k _ => hconst k)]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one]
  rw [← Finset.mul_sum, hsum]
  ring

end SpinGlasses
