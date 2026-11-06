/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIteratedDeriv

/-!
# The cavity-path average as a positive linear functional

For fixed `N, n, β, q, h` and `u`, the cavity-path average `f ↦ ν_u(f)` of an `n`-replica
observable (`skCavityPathMean`) is a positive linear functional.  Bundling it as a
`LinearMap` gives access to the generic bounds of
`ForMathlib/LinearAlgebra/FiniteProductBound.lean` (Cauchy-Schwarz, absolute values, products
of linear combinations).

## Main declarations

* `SpinGlasses.skCavityPathEnergy`: the path energy `E_u(g', ω, a)` written explicitly.
* `SpinGlasses.skCavityPathMeanLM`: `ν_u` as a linear functional.
* `SpinGlasses.skCavityPathMean_mono`: monotonicity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The cavity-path energy at parameter `u ∈ [0, 1]` (angle `arccos √u`). -/
noncomputable def skCavityPathEnergy (N : ℕ) (β q h u : ℝ) (g' : FinPairs N → ℝ)
    (ω : (Fin N → ℝ) × ℝ) (a : Fin (N + 1) → ℤˣ) : ℝ :=
  Real.cos (Real.arccos (Real.sqrt u)) * ((Real.sqrt (N + 1))⁻¹ * β *
    (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
  Real.sin (Real.arccos (Real.sqrt u)) * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) +
  ((Real.sqrt (N + 1))⁻¹ * β *
    (∑ p : FinPairs N, g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
    h * ∑ i : Fin (N + 1), (a i : ℝ))

/-- `skCavityPathMean` is the nested Gibbs average for `skCavityPathEnergy`. -/
theorem skCavityPathMean_eq (N n : ℕ) (β q h u : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h u f =
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityPathEnergy N β q h u g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := rfl

theorem measurable_skCavityPathEnergy (N : ℕ) (β q h u : ℝ) (a : Fin (N + 1) → ℤˣ) :
    Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) =>
      skCavityPathEnergy N β q h u x.1 x.2 a) := by
  unfold skCavityPathEnergy
  fun_prop

theorem skCavityPathMean_finset_sum (N n : ℕ) (β q h u : ℝ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (G : ι → (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h u (fun σ => ∑ j ∈ s, c j * G j σ) =
      ∑ j ∈ s, c j * skCavityPathMean N n β q h u (G j) := by
  simp only [skCavityPathMean_eq]
  exact integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    (R := Fin n) (skCavityPathEnergy N β q h u) (measurable_skCavityPathEnergy N β q h u)
    s c G

/-- Marginalizing unused replicas preserves the cavity-path average at every path parameter. -/
theorem skCavityPathMean_comp_injective (N : ℕ) (β q h u : ℝ) {n R : ℕ}
    {ι : Fin n → Fin R} (hι : Function.Injective ι)
    (F : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    skCavityPathMean N R β q h u (fun σ => F (fun r => σ (ι r))) =
      skCavityPathMean N n β q h u F := by
  simp only [skCavityPathMean_eq]
  apply integral_congr_ae (ae_of_all _ fun _ => ?_)
  apply integral_congr_ae (ae_of_all _ fun _ => ?_)
  exact integral_pi_count_tilted_comp_injective hι _ F

/-- Domination passes through the cavity-path average. -/
theorem abs_skCavityPathMean_le (N n : ℕ) (β q h u : ℝ)
    {G H : (Fin n → Fin (N + 1) → ℤˣ) → ℝ} (hGH : ∀ σ, |G σ| ≤ H σ) :
    |skCavityPathMean N n β q h u G| ≤ skCavityPathMean N n β q h u H := by
  simp only [skCavityPathMean_eq]
  exact abs_integral_nested_gibbs_le (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    (skCavityPathEnergy N β q h u) (measurable_skCavityPathEnergy N β q h u) hGH

/-- The cavity-path average as a linear functional of the observable. -/
noncomputable def skCavityPathMeanLM (N n : ℕ) (β q h u : ℝ) :
    ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ where
  toFun f := skCavityPathMean N n β q h u f
  map_add' f g := by
    have := skCavityPathMean_finset_sum N n β q h u (Finset.univ : Finset (Fin 2)) (fun _ => 1)
      ![f, g]
    simp only [Fin.sum_univ_two, one_mul] at this
    exact this
  map_smul' c f := by
    have := skCavityPathMean_finset_sum N n β q h u (Finset.univ : Finset Unit) (fun _ => c)
      (fun _ => f)
    simp only [Finset.univ_unique, Finset.sum_singleton] at this
    simp only [RingHom.id_apply, smul_eq_mul]
    exact this

theorem skCavityPathMeanLM_apply (N n : ℕ) (β q h u : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    skCavityPathMeanLM N n β q h u f = skCavityPathMean N n β q h u f := rfl

/-- The cavity-path average commutes with multiplication by a constant. -/
theorem skCavityPathMean_const_mul (N n : ℕ) (β q h u c : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h u (fun σ => c * f σ) = c * skCavityPathMean N n β q h u f :=
  (skCavityPathMeanLM N n β q h u).map_smul c f

/-- The cavity-path average is monotone. -/
theorem skCavityPathMean_mono (N n : ℕ) (β q h u : ℝ)
    {f g : (Fin n → Fin (N + 1) → ℤˣ) → ℝ} (hfg : ∀ σ, f σ ≤ g σ) :
    skCavityPathMean N n β q h u f ≤ skCavityPathMean N n β q h u g := by
  have h1 := abs_skCavityPathMean_le N n β q h u (G := fun σ => g σ - f σ)
    (H := fun σ => g σ - f σ) fun σ => abs_of_nonneg (sub_nonneg.2 (hfg σ)) |>.le
  have h2 : skCavityPathMean N n β q h u (fun σ => g σ - f σ) =
      skCavityPathMean N n β q h u g - skCavityPathMean N n β q h u f := by
    exact (skCavityPathMeanLM N n β q h u).map_sub g f
  rw [h2] at h1
  linarith [(abs_nonneg _).trans h1, le_abs_self (skCavityPathMean N n β q h u g -
    skCavityPathMean N n β q h u f), abs_nonneg (skCavityPathMean N n β q h u g -
    skCavityPathMean N n β q h u f)]

/-- Cauchy-Schwarz for the cavity-path average. -/
theorem skCavityPathMean_mul_sq_le (N n : ℕ) (β q h u : ℝ)
    (f g : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h u (fun σ => f σ * g σ) ^ 2 ≤
      skCavityPathMean N n β q h u (fun σ => f σ ^ 2) *
        skCavityPathMean N n β q h u (fun σ => g σ ^ 2) :=
  (skCavityPathMeanLM N n β q h u).apply_mul_sq_le
    (fun _ _ hfg => skCavityPathMean_mono N n β q h u hfg) f g

end SpinGlasses
