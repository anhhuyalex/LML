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

@[fun_prop]
theorem measurable_smartPathField {N M : ℕ} (s : ℝ) (k : Fin M) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathField s p.1 p.2 k := by
  dsimp only [smartPathField]
  have : Measurable (fun ε : ℤˣ => ((ε : ℤ) : ℝ)) := measurable_of_countable _
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergy {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) (s : ℝ) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergy u s p.1 p.2 := by
  dsimp only [smartPathEnergy, smartPathField]
  have : Measurable (fun ε : ℤˣ => ((ε : ℤ) : ℝ)) := measurable_of_countable _
  fun_prop

theorem measurable_smartPathEnergy_slice {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (s : ℝ) (ω : SmartPathDisorder N M) :
    Measurable (smartPathEnergy u s ω) :=
  (measurable_smartPathEnergy hu s).comp (measurable_const.prodMk measurable_id)

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

/-- Extension of `SmartPathPotential` requiring `deriv u` to be differentiable with
its derivative `u''` bounded by `D₂`. -/
structure SmartPathPotential₂ (u : ℝ → ℝ) (B D D₂ : ℝ) : Prop extends
    SmartPathPotential u B D where
  differentiable_deriv : Differentiable ℝ (deriv u)
  abs_deriv₂_le : ∀ z, |deriv (deriv u) z| ≤ D₂

/-! ### D5. Path without auxiliary spins (Exercise 2.2.4) -/

/-- The smart-path field without auxiliary spins (Talagrand Eq. (2.14)). -/
noncomputable def smartPathFieldNoAux {N M : ℕ} (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) (k : Fin M) : ℝ :=
  (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
    Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ)

/-- The smart-path energy without auxiliary spins (Talagrand Eq. (2.14)). -/
noncomputable def smartPathEnergyNoAux {N M : ℕ} (u : ℝ → ℝ) (s : ℝ)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (smartPathFieldNoAux s ω x k)

/-! ### D6. Interaction kernels -/

/-- Cross-replica interaction kernel of potential derivatives (term I). -/
noncomputable def smartPathPotentialKernel {N M : ℕ} (u : ℝ → ℝ) (t : ℝ)
    (ω : SmartPathDisorder N M) (k : Fin M) (x y : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k) *
    deriv u (smartPathField t ω y k)

/-- Last-spin interaction kernel (term II). -/
def lastSpinKernel {N M : ℕ} (x y : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ)

/-! ### Algebraic prefactors and replica combination identities -/

/-- Square-root scaling prefactor of the Gaussian integration by parts on the smart path:
`(1 / (2 * √(N + 1))) * (1 / √s) * √(s / (N + 1)) = 1 / (2 * (N + 1))` for `s > 0`. With `s = t`
this is the quenched-disorder prefactor, with `s = 1 - t` the auxiliary-spin one. -/
theorem smartPath_sqrt_scaling_prefactor_eq {N : ℕ} {s : ℝ} (hs : 0 < s) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (1 / Real.sqrt s) *
      Real.sqrt (s / (N + 1 : ℕ)) =
    1 / (2 * (N + 1 : ℝ)) := by
  push_cast
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [Real.sqrt_div hs.le]
  have h1 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h2 : Real.sqrt ((N : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have h3 := Real.mul_self_sqrt hN.le
  field_simp
  nlinarith [h3]

/-- Simplification of the auxiliary spin prefactor: the product
`(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1))` simplifies to
`- 1 / (2 * (N + 1))`, cancelling the `√(1 - t)` denominator. -/
theorem smartPath_auxiliary_prefactor_eq_neg {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  have := smartPath_sqrt_scaling_prefactor_eq (N := N) (sub_pos.2 ht.2)
  linear_combination -this

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

/-- For the last-spin interaction kernel `lastSpinKernel x y = x.1.2 * y.1.2`, the
diagonal is identically 1 (since `(σ_{N+1})² = 1`), so `replicaPairDiff` is exactly half
of the 4-term replica covariance combination. Note: `[LinearOrder R]` is used to order pairs
`r < r'` without double counting. -/
theorem replicaPairDiff_lastSpinKernel {N M : ℕ} {R : Type*} [Fintype R] [LinearOrder R]
    (τ : Option (Option R) → SmartPathState N M) :
    replicaPairDiff (lastSpinKernel (N := N) (M := M)) τ =
      ((∑ r : R, ∑ r' : R, ((τ (some (some r))).1.2 : ℝ) * ((τ (some (some r'))).1.2 : ℝ)) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, ((τ (some (some r))).1.2 : ℝ) * ((τ (some none)).1.2 : ℝ)) -
          (Fintype.card R : ℝ) * 1 +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            (((τ (some none)).1.2 : ℝ) * ((τ none).1.2 : ℝ))) / 2 := by
  have hdiag (a : SmartPathState N M) : lastSpinKernel a a = 1 := by
    unfold lastSpinKernel
    have : ((a.1.2 : ℤ) : ℝ) * ((a.1.2 : ℤ) : ℝ) = (((a.1.2 : ℤ) : ℝ) ^ 2) := by ring
    rw [this]
    rcases Int.units_eq_one_or a.1.2 with h1 | h1 <;> simp [h1]
  have hsym (a b : SmartPathState N M) : lastSpinKernel a b = lastSpinKernel b a := by
    unfold lastSpinKernel; ring
  have h := replicaPairDiff_eq_half_replica_covariance_combination
    (lastSpinKernel (N := N) (M := M)) 1 hdiag hsym τ
  have hd : lastSpinKernel (τ (some none)) (τ (some none)) = 1 := hdiag _
  rw [hd] at h
  simpa only [lastSpinKernel] using h

end SpinGlasses
