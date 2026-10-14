/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.AizenmanSimsStarr
public import LeanMachineLearning.SpinGlasses.AsymptoticGibbsApproximation

/-!
# The Aizenman–Sims–Starr increment: bounds and Gram-matrix approximation

The increment `A_N = 𝔼 log Z_{N+1} - 𝔼 log Z_N` of the Sherrington–Kirkpatrick model is the
`u`-average of `𝔼_ζ log ⟨2 cosh (β z)⟩' - 𝔼_v log ⟨exp (β y)⟩'`
(`SpinGlasses.aizenman_sims_starr_representation`), where `⟨·⟩'` is the Gibbs average of the
auxiliary Hamiltonian `H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)` and the cavity fields `z`, `y` are centered
Gaussian families with covariances `2 β² a_N R(σ, τ)` and `β² a_N R(σ, τ)²`, `a_N = N/(N+1)`,
`R(σ, τ) = N⁻¹ σ ⬝ τ` ([Panchenko, 2013, Eq. (1.59)]).  Two consequences, obtained from the abstract
estimates of `SpinGlasses/AsymptoticGibbsApproximation.lean`:

* `SpinGlasses.sk_increment_bounds`: the *a priori* bounds
  `log 2 - β²/2 ≤ A_N ≤ log 2 + β²` (Jensen), which remove the boundedness hypotheses from the
  Cesàro bound `SpinGlasses.liminf_increment_le_liminf_free_energy_of_pos`:
  `liminf A_N ≤ liminf F_N`.
* `SpinGlasses.abs_increment_sub_integral_overlap_le` (Eq. (1.73)): for every `ε > 0`,
  `A_N` is within `ε` of the `u`-average of a Gibbs average of a bounded continuous function of the
  overlaps of finitely many replicas, uniformly in `N` (Theorem 1.3 applied to the cavity fields).

As in `AizenmanSimsStarr.lean`, no definitions are introduced: the Gibbs weights `wt`, the
auxiliary Hamiltonian `f`, the fields `z`, `y` and the overlap `R` are passed with their defining
equations (`SpinGlasses.sk_setup` provides them).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal Matrix

namespace SpinGlasses

section Cavity

local notation "γ[" K "]" => Measure.pi fun _ : K => gaussianReal 0 1
local notation "𝒢[" N "]" =>
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1

variable {β : ℝ} {N : ℕ}

/-- **The Gibbs weights of the auxiliary Hamiltonian** `H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)`, with
`f u σ = β H'(σ)`, are measurable in the disorder `u`, lie in `[0, 1]` and sum to `1`. -/
theorem sk_gibbsWeight (f : (Fin N × Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (wt : (Fin N × Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hf : ∀ u σ, f u σ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
        fun i => ((σ i : ℤ) : ℝ)))))
    (hwt : ∀ u σ, wt u σ = Real.exp (f u σ) / ∑ τ, Real.exp (f u τ)) :
    (∀ σ, Measurable fun u => wt u σ) ∧ (∀ u σ, 0 ≤ wt u σ) ∧ (∀ u, ∑ σ, wt u σ = 1) ∧
      ∀ u σ, wt u σ ≤ 1 := by
  have hfm : ∀ τ : Fin N → ℤˣ, Measurable fun u => f u τ := fun τ => by
    rw [show (fun u => f u τ) = fun u => (fun p : Fin N × Fin N =>
        (β * (Real.sqrt ((N : ℝ) + 1))⁻¹) * (((τ p.1 : ℤ) : ℝ) * ((τ p.2 : ℤ) : ℝ))) ⬝ᵥ u from
      funext fun u => by
        rw [hf, ← mul_assoc, mul_dotProduct_mulVec_eq_dotProduct]]
    simp only [dotProduct]
    fun_prop
  have h0 : ∀ u σ, 0 ≤ wt u σ := fun u σ => by rw [hwt]; positivity
  have h1 : ∀ u, ∑ σ, wt u σ = 1 := fun u => by
    simp only [hwt]
    rw [← Finset.sum_div]
    exact div_self (Finset.sum_pos (fun τ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  refine ⟨fun σ => ?_, h0, h1, fun u σ => ?_⟩
  · simp only [hwt]
    exact (Real.measurable_exp.comp (hfm σ)).div
      (Finset.measurable_sum _ fun τ _ => Real.measurable_exp.comp (hfm τ))
  · rw [← h1 u]
    exact Finset.single_le_sum (f := fun σ => wt u σ) (fun τ _ => h0 u τ) (Finset.mem_univ σ)

/-- The self-overlap `R σ σ = N⁻¹ σ ⬝ σ` of a configuration is `1`. -/
theorem sk_overlap_self (hN : 0 < N) (R : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
    (hR : ∀ σ τ, R σ τ = (N : ℝ)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) (σ : Fin N → ℤˣ) :
    R σ σ = 1 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [hR, show (fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((σ i : ℤ) : ℝ)) = N by
    simp [dotProduct, ← sq, units_cast_sq], inv_mul_cancel₀ hN0.ne']

/-- **The cavity field `z`** (a centered Gaussian family with covariance `2 β² a_N R`).  For
`z σ ζ = β (√(N+1))⁻¹ ∑ᵢ (ζ (inl (i+1)) + ζ (inr i)) σᵢ` and `R σ τ = N⁻¹ σ ⬝ τ`: `z σ` is
measurable,
the family is Gaussian and centered, and `𝔼 z σ z τ = β² (2 N/(N+1)) R σ τ` (Eq. (1.59)). -/
theorem sk_cavity_z (hN : 0 < N) (z : (Fin N → ℤˣ) → (Fin (N + 1) ⊕ Fin N → ℝ) → ℝ)
    (R : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
    (hz : ∀ σ ζ, z σ ζ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
      ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)))
    (hR : ∀ σ τ, R σ τ = (N : ℝ)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) :
    (∀ σ, Measurable (z σ)) ∧ HasGaussianLaw (fun ζ σ => z σ ζ) (γ[Fin (N + 1) ⊕ Fin N]) ∧
      (∀ σ, ∫ ζ, z σ ζ ∂(γ[Fin (N + 1) ⊕ Fin N]) = 0) ∧
      ∀ σ τ, ∫ ζ, z σ ζ * z τ ζ ∂(γ[Fin (N + 1) ⊕ Fin N]) =
        β ^ 2 * (2 * ((N : ℝ) / ((N : ℝ) + 1))) * R σ τ := by
  refine ⟨fun σ => ?_, ?_, fun σ => ?_, fun σ τ => ?_⟩
  · rw [show z σ = fun ζ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
      ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)) from funext (hz σ)]
    fun_prop
  · have := hasGaussianLaw_cavity_z (A := Fin N → ℤˣ) N β (fun σ i => ((σ i : ℤ) : ℝ))
    simpa only [hz] using this
  · simp only [hz]
    exact integral_cavity_z_eq_zero N β _
  · simp_rw [hz]
    have := integral_cavity_z_mul_z hN (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((τ i : ℤ) : ℝ))
    rw [show (fun ζ : Fin (N + 1) ⊕ Fin N → ℝ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)) * (β *
        ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((τ i : ℤ) : ℝ)))) = fun ζ => β ^ 2 *
        (((Real.sqrt ((N : ℝ) + 1))⁻¹ *
          ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)) *
        ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
          ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((τ i : ℤ) : ℝ))) from
      funext fun ζ => by ring, integral_const_mul, this, hR]
    ring

/-- **The cavity field `y`** (a centered Gaussian family with covariance `β² a_N R²`), for
`y σ v = β (√(N(N+1)))⁻¹ σ ⬝ (v σ)`: measurable, Gaussian, centered, with
`𝔼 y σ y τ = β² (N/(N+1)) R σ τ²` (Eq. (1.59)). -/
theorem sk_cavity_y (hN : 0 < N) (y : (Fin N → ℤˣ) → (Fin N × Fin N → ℝ) → ℝ)
    (R : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
    (hy : ∀ σ v, y σ v = β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
        fun i => ((σ i : ℤ) : ℝ)))))
    (hR : ∀ σ τ, R σ τ = (N : ℝ)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) :
    (∀ σ, Measurable (y σ)) ∧ HasGaussianLaw (fun v σ => y σ v) (γ[Fin N × Fin N]) ∧
      (∀ σ, ∫ v, y σ v ∂(γ[Fin N × Fin N]) = 0) ∧
      ∀ σ τ, ∫ v, y σ v * y τ v ∂(γ[Fin N × Fin N]) =
        β ^ 2 * ((N : ℝ) / ((N : ℝ) + 1)) * R σ τ ^ 2 := by
  refine ⟨fun σ => ?_, ?_, fun σ => ?_, fun σ τ => ?_⟩
  · rw [show y σ = fun v => (fun p : Fin N × Fin N =>
          (β * (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹) *
          (((σ p.1 : ℤ) : ℝ) * ((σ p.2 : ℤ) : ℝ))) ⬝ᵥ v from funext fun v => by
        rw [hy, ← mul_assoc, mul_dotProduct_mulVec_eq_dotProduct]]
    simp only [dotProduct]
    fun_prop
  · have := hasGaussianLaw_cavity_y (A := Fin N → ℤˣ) N
      (β * (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹) (fun σ i => ((σ i : ℤ) : ℝ))
    simpa only [hy, mul_assoc] using this
  · simp only [hy, ← mul_assoc]
    exact integral_cavity_y_eq_zero N _ _
  · simp_rw [hy]
    have := integral_cavity_y_mul_y hN (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((τ i : ℤ) : ℝ))
    rw [show (fun v : Fin N × Fin N → ℝ => β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
          fun i => ((σ i : ℤ) : ℝ)))) * (β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
        ((fun i => ((τ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
          fun i => ((τ i : ℤ) : ℝ)))))) = fun v => β ^ 2 *
        (((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
          ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
            fun i => ((σ i : ℤ) : ℝ)))) * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
          ((fun i => ((τ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
            fun i => ((τ i : ℤ) : ℝ))))) from funext fun v => by ring, integral_const_mul,
      this, hR]
    ring

/-- **The Gibbs average in the Aizenman–Sims–Starr integrand is a finite sum:** with the Gibbs
weights `wt u σ = exp (f u σ) / ∑ τ exp (f u τ)`,
`∫ φ d(count.tilted (f u)) = ∑ σ, wt u σ φ σ`. -/
theorem sk_integral_count_tilted (f : (Fin N × Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (wt : (Fin N × Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hwt : ∀ u σ, wt u σ = Real.exp (f u σ) / ∑ τ, Real.exp (f u τ)) (u : Fin N × Fin N → ℝ)
    (φ : (Fin N → ℤˣ) → ℝ) :
    ∫ σ, φ σ ∂(Measure.count.tilted (f u)) = ∑ σ, wt u σ * φ σ := by
  rw [integral_count_tilted]
  exact Finset.sum_congr rfl fun σ _ => by rw [hwt]

section Integrand

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The Aizenman–Sims–Starr integrand, in terms of the cavity fields.**  With
`f u σ = β H'(σ)` and the cavity fields `z`, `y` given by their defining equations, any `F` with
`F u = 𝔼_ζ log ⟨2 cosh z⟩ - 𝔼_v log ⟨exp y⟩` (the average `⟨·⟩` under `count.tilted (f u)`) is
integrable, and its integral is `A_N` (Eq. (1.58)). -/
theorem sk_integrable_and_eq {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (f : (Fin N × Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (z : (Fin N → ℤˣ) → (Fin (N + 1) ⊕ Fin N → ℝ) → ℝ)
    (y : (Fin N → ℤˣ) → (Fin N × Fin N → ℝ) → ℝ)
    (hf : ∀ u σ, f u σ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
        fun i => ((σ i : ℤ) : ℝ)))))
    (hz : ∀ σ ζ, z σ ζ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
      ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)))
    (hy : ∀ σ v, y σ v = β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
        fun i => ((σ i : ℤ) : ℝ)))))
    (F : (Fin N × Fin N → ℝ) → ℝ)
    (hF : ∀ u, F u =
      (∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
          Real.log (∫ σ, 2 * Real.cosh (z σ ζ) ∂(Measure.count.tilted (f u)))
            ∂(γ[Fin (N + 1) ⊕ Fin N])) -
        ∫ v : Fin N × Fin N → ℝ,
          Real.log (∫ σ, Real.exp (y σ v) ∂(Measure.count.tilted (f u))) ∂(γ[Fin N × Fin N])) :
    Integrable F (γ[Fin N × Fin N]) ∧
      (∫ G, Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N] = ∫ u, F u ∂(γ[Fin N × Fin N]) := by
  refine integrable_and_eq_aizenman_sims_starr H hH hβ hN F fun u => ?_
  rw [hF u, show f u = fun σ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
        fun i => ((σ i : ℤ) : ℝ)))) from funext (hf u)]
  simp only [hz, hy]

end Integrand

/-- The auxiliary Hamiltonian, Gibbs weights, cavity fields and overlap, introduced through their
defining equations (no definitions are made). -/
theorem sk_setup (β : ℝ) (N : ℕ) :
    ∃ (f wt : (Fin N × Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
      (z : (Fin N → ℤˣ) → (Fin (N + 1) ⊕ Fin N → ℝ) → ℝ)
      (y : (Fin N → ℤˣ) → (Fin N × Fin N → ℝ) → ℝ)
      (R : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ),
      (∀ u σ, f u σ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
          fun i => ((σ i : ℤ) : ℝ))))) ∧
      (∀ u σ, wt u σ = Real.exp (f u σ) / ∑ τ, Real.exp (f u τ)) ∧
      (∀ σ ζ, z σ ζ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ))) ∧
      (∀ σ v, y σ v = β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
          fun i => ((σ i : ℤ) : ℝ))))) ∧
      (∀ σ τ, R σ τ = (N : ℝ)⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) :=
  ⟨_, _, _, _, _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

section Bounds

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **A priori bounds for the Aizenman–Sims–Starr increment** (Panchenko, §1.3).  For every
`N ≥ 1`, `log 2 - β²/2 ≤ A_N ≤ log 2 + β²`, where `A_N = 𝔼 log Z_{N+1} - 𝔼 log Z_N`.  By
Eq. (1.58), `A_N` is the `u`-average of `𝔼_ζ log ⟨2 cosh (β z)⟩' - 𝔼_v log ⟨exp (β y)⟩'`, and by
Jensen `log 2 ≤ 𝔼 log ⟨2 cosh (β z)⟩' ≤ log 2 + β² a_N` while `0 ≤ 𝔼 log ⟨exp (β y)⟩' ≤ β² a_N / 2`,
with `a_N = N / (N + 1) ≤ 1`. -/
theorem sk_increment_bounds {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    Real.log 2 - β ^ 2 / 2 ≤ (∫ G, Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N] ∧
      (∫ G, Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N] ≤ Real.log 2 + β ^ 2 := by
  classical
  obtain ⟨f, wt, z, y, R, hf, hwt, hz, hy, hR⟩ := sk_setup β N
  obtain ⟨-, hw0, hw1, -⟩ := sk_gibbsWeight f wt hf hwt
  obtain ⟨hzm, hzg, hz0, hzcov⟩ := sk_cavity_z hN z R hz hR
  obtain ⟨hym, hyg, hy0, hycov⟩ := sk_cavity_y hN y R hy hR
  have hN1 : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).2 (by linarith)
  have hzv : ∀ σ : Fin N → ℤˣ, ∫ ζ, z σ ζ ^ 2 ∂(γ[Fin (N + 1) ⊕ Fin N]) ≤ 2 * β ^ 2 := fun σ => by
    rw [show (fun ζ => z σ ζ ^ 2) = fun ζ => z σ ζ * z σ ζ from funext fun ζ => sq _, hzcov,
      sk_overlap_self hN R hR]
    nlinarith [sq_nonneg β]
  have hyv : ∀ σ : Fin N → ℤˣ, ∫ v, y σ v ^ 2 ∂(γ[Fin N × Fin N]) ≤ β ^ 2 := fun σ => by
    rw [show (fun v => y σ v ^ 2) = fun v => y σ v * y σ v from funext fun v => sq _, hycov,
      sk_overlap_self hN R hR]
    nlinarith [sq_nonneg β]
  have hsz : ∀ σ, HasSubgaussianMGF (z σ) (2 * β ^ 2).toNNReal (γ[Fin (N + 1) ⊕ Fin N]) :=
    fun σ => (hzg.eval σ).hasSubgaussianMGF_of_integral_sq_le (hz0 σ) (hzv σ)
  have hsy : ∀ σ, HasSubgaussianMGF (y σ) (β ^ 2).toNNReal (γ[Fin N × Fin N]) :=
    fun σ => (hyg.eval σ).hasSubgaussianMGF_of_integral_sq_le (hy0 σ) (hyv σ)
  obtain ⟨F, hF⟩ : ∃ F : (Fin N × Fin N → ℝ) → ℝ, ∀ u, F u =
      (∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
          Real.log (∫ σ, 2 * Real.cosh (z σ ζ) ∂(Measure.count.tilted (f u)))
            ∂(γ[Fin (N + 1) ⊕ Fin N])) -
        ∫ v : Fin N × Fin N → ℝ,
          Real.log (∫ σ, Real.exp (y σ v) ∂(Measure.count.tilted (f u))) ∂(γ[Fin N × Fin N]) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hFi, hFeq⟩ := sk_integrable_and_eq H hH hβ hN f z y hf hz hy F hF
  have hpt : ∀ u, Real.log 2 - β ^ 2 / 2 ≤ F u ∧ F u ≤ Real.log 2 + β ^ 2 := fun u => by
    rw [hF u]
    simp_rw [sk_integral_count_tilted f wt hwt u]
    have h1 := log_two_le_integral_log_sum_mul_two_cosh (hw0 u) (hw1 u) hzm hsz
    have h2 := integral_log_sum_mul_two_cosh_le (hw0 u) (hw1 u) hzm hsz
    have h3 := zero_le_integral_log_sum_mul_exp (hw0 u) (hw1 u) hym hsy hy0
    have h4 := integral_log_sum_mul_exp_le (hw0 u) (hw1 u) hym hsy
    rw [Real.coe_toNNReal _ (by positivity)] at h2 h4
    constructor <;> linarith
  rw [hFeq]
  constructor
  · simpa using integral_mono (integrable_const _) hFi fun u => (hpt u).1
  · simpa using integral_mono hFi (integrable_const _) fun u => (hpt u).2

/-- **The Cesàro bound without boundedness hypotheses** (`liminf_N A_N ≤ liminf_N F_N`): the
increments `A_N` are bounded by `sk_increment_bounds`. -/
theorem liminf_increment_le_liminf_free_energy_of_pos {β : ℝ} (hβ : 0 < β) :
    liminf (fun N : ℕ => (∫ G, Real.log (∑ σ, Real.exp (β * H (N + 1) G σ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N]) atTop ≤
      liminf (fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N])
        atTop :=
  liminf_increment_le_liminf_free_energy H hH β
    (isBoundedUnder_of_eventually_le (a := Real.log 2 + β ^ 2)
      ((eventually_ge_atTop 1).mono fun _ hN => (sk_increment_bounds H hH hβ hN).2))
    (isBoundedUnder_of_eventually_ge (a := Real.log 2 - β ^ 2 / 2)
      ((eventually_ge_atTop 1).mono fun _ hN => (sk_increment_bounds H hH hβ hN).1))

end Bounds

section Approximation

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The Aizenman–Sims–Starr increment is a Gram-matrix functional (Panchenko Eq. (1.73)).**
For every `ε > 0` there are truncation levels `az`, `ay` and polynomials `pz`, `py`, depending only
on `β` and `ε` and not on `N`, such that for all `N ≥ 1`
`|A_N - 𝔼_u [∑_k pz_k ⟨Fz_k(R)⟩' - ∑_k py_k ⟨Fy_k(R)⟩']| ≤ ε`.
Here `⟨·⟩'` is the Gibbs average (weights `wt u`) of the auxiliary Hamiltonian
`f u σ = β (√(N+1))⁻¹ σ ⬝ (u σ)` over `k` independent replicas `j : Fin k → Σ_N`, `R` is the overlap
and `Fz_k`, `Fy_k` are the Gaussian replica functionals with covariance matrices
`2 β² a_N R(σ^l, σ^{l'})` and `β² a_N R(σ^l, σ^{l'})²`, `a_N = N/(N+1)` (Eq. (1.59)); they are
continuous and bounded functions of the overlap matrix
(`continuousOn_integral_prod_multivariateGaussian`).
This is `exists_gram_approx_free_energy` for the cavity fields of `SpinGlasses.sk_cavity_z`
and `SpinGlasses.sk_cavity_y`, integrated over `u`. -/
theorem abs_increment_sub_integral_overlap_le {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ (az ay : ℝ) (pz py : Polynomial ℝ), 0 ≤ az ∧ 0 ≤ ay ∧
      ∀ (N : ℕ), 0 < N →
        ∀ (f wt : (Fin N × Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
          (R : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ) (Gz Gy : (Fin N × Fin N → ℝ) → ℝ),
        (∀ u σ, f u σ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
          ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
            fun i => ((σ i : ℤ) : ℝ))))) →
        (∀ u σ, wt u σ = Real.exp (f u σ) / ∑ τ, Real.exp (f u τ)) →
        (∀ σ τ, R σ τ = (N : ℝ)⁻¹ *
          ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) →
        (∀ u, Gz u = ∑ k ∈ range (pz.natDegree + 1), pz.coeff k *
          ∑ j : Fin k → (Fin N → ℤˣ), (∏ l, wt u (j l)) *
            ∫ x : EuclideanSpace ℝ (Fin k),
              ∏ l, 2 * Real.cosh (max (-az) (min (x.ofLp l) az)) ∂(multivariateGaussian 0
                (Matrix.of fun l l' =>
                  β ^ 2 * (2 * ((N : ℝ) / ((N : ℝ) + 1))) * R (j l) (j l')))) →
        (∀ u, Gy u = ∑ k ∈ range (py.natDegree + 1), py.coeff k *
          ∑ j : Fin k → (Fin N → ℤˣ), (∏ l, wt u (j l)) *
            ∫ x : EuclideanSpace ℝ (Fin k),
              ∏ l, Real.exp (max (-ay) (min (x.ofLp l) ay)) ∂(multivariateGaussian 0
                (Matrix.of fun l l' =>
                  β ^ 2 * ((N : ℝ) / ((N : ℝ) + 1)) * R (j l) (j l') ^ 2))) →
        |((∫ G, Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ)) ∂𝒢[N + 1]) -
            ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N]) -
          ∫ u, (Gz u - Gy u) ∂(γ[Fin N × Fin N])| ≤ ε := by
  classical
  obtain ⟨az, ay, pz, py, haz, hay, h13⟩ := exists_gram_approx_free_energy.{0, 0}
    (2 * β ^ 2).toNNReal (β ^ 2).toNNReal hε
  refine ⟨az, ay, pz, py, haz, hay, fun N hN f wt R Gz Gy hf hwt hR hGz hGy => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z : (Fin N → ℤˣ) → (Fin (N + 1) ⊕ Fin N → ℝ) → ℝ, ∀ σ ζ,
      z σ ζ = β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (Fin N → ℤˣ) → (Fin N × Fin N → ℝ) → ℝ, ∀ σ v,
      y σ v = β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
          fun i => ((σ i : ℤ) : ℝ)))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨hwm, hw0, hw1, hwle⟩ := sk_gibbsWeight f wt hf hwt
  obtain ⟨hzm, hzg, hz0, hzcov⟩ := sk_cavity_z hN z R hz hR
  obtain ⟨hym, hyg, hy0, hycov⟩ := sk_cavity_y hN y R hy hR
  have hN1 : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).2 (by linarith)
  have hzv : ∀ σ : Fin N → ℤˣ, ∫ ζ, z σ ζ ^ 2 ∂(γ[Fin (N + 1) ⊕ Fin N]) ≤
      ((2 * β ^ 2).toNNReal : ℝ) := fun σ => by
    rw [show (fun ζ => z σ ζ ^ 2) = fun ζ => z σ ζ * z σ ζ from funext fun ζ => sq _, hzcov,
      sk_overlap_self hN R hR, Real.coe_toNNReal _ (by positivity)]
    nlinarith [sq_nonneg β]
  have hyv : ∀ σ : Fin N → ℤˣ, ∫ v, y σ v ^ 2 ∂(γ[Fin N × Fin N]) ≤
      ((β ^ 2).toNNReal : ℝ) := fun σ => by
    rw [show (fun v => y σ v ^ 2) = fun v => y σ v * y σ v from funext fun v => sq _, hycov,
      sk_overlap_self hN R hR, Real.coe_toNNReal _ (by positivity)]
    nlinarith [sq_nonneg β]
  obtain ⟨F, hF⟩ : ∃ F : (Fin N × Fin N → ℝ) → ℝ, ∀ u, F u =
      (∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
          Real.log (∫ σ, 2 * Real.cosh (z σ ζ) ∂(Measure.count.tilted (f u)))
            ∂(γ[Fin (N + 1) ⊕ Fin N])) -
        ∫ v : Fin N × Fin N → ℝ,
          Real.log (∫ σ, Real.exp (y σ v) ∂(Measure.count.tilted (f u))) ∂(γ[Fin N × Fin N]) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hFi, hFeq⟩ := sk_integrable_and_eq H hH hβ hN f z y hf hz hy F hF
  have hpt : ∀ u, |F u - (Gz u - Gy u)| ≤ ε := fun u => by
    have h := h13 (Fin N → ℤˣ) (wt u) (hw0 u) (hw1 u) (Fin (N + 1) ⊕ Fin N → ℝ)
      (γ[Fin (N + 1) ⊕ Fin N]) z (Fin N × Fin N → ℝ) (γ[Fin N × Fin N]) y hzm hzg hz0 hzv hym hyg
      hy0 hyv
    simp only [hzcov, hycov] at h
    rw [hF u, hGz u, hGy u]
    simp_rw [sk_integral_count_tilted f wt hwt u]
    exact h
  -- integrability of the Gram-matrix approximants
  have hprod : ∀ (k : ℕ) (j : Fin k → (Fin N → ℤˣ)),
      Integrable (fun u => ∏ l, wt u (j l)) (γ[Fin N × Fin N]) := fun k j =>
    Integrable.of_bound (C := 1)
      (Finset.measurable_prod _ fun l _ => hwm (j l)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun l _ => hw0 u _)]
        calc ∏ l, wt u (j l) ≤ ∏ _l : Fin k, (1 : ℝ) := by
              gcongr with l
              · exact fun l _ => hw0 u _
              · exact hwle u _
          _ = 1 := by simp)
  have hGzi : Integrable Gz (γ[Fin N × Fin N]) := by
    have : Integrable (fun u => ∑ k ∈ range (pz.natDegree + 1), pz.coeff k *
        ∑ j : Fin k → (Fin N → ℤˣ), (∏ l, wt u (j l)) *
          ∫ x : EuclideanSpace ℝ (Fin k),
            ∏ l, 2 * Real.cosh (max (-az) (min (x.ofLp l) az)) ∂(multivariateGaussian 0
              (Matrix.of fun l l' =>
                β ^ 2 * (2 * ((N : ℝ) / ((N : ℝ) + 1))) * R (j l) (j l'))))
        (γ[Fin N × Fin N]) :=
      integrable_finsetSum _ fun k _ =>
        (integrable_finsetSum _ fun j _ => (hprod k j).mul_const _).const_mul _
    exact this.congr (Filter.Eventually.of_forall fun u => (hGz u).symm)
  have hGyi : Integrable Gy (γ[Fin N × Fin N]) := by
    have : Integrable (fun u => ∑ k ∈ range (py.natDegree + 1), py.coeff k *
        ∑ j : Fin k → (Fin N → ℤˣ), (∏ l, wt u (j l)) *
          ∫ x : EuclideanSpace ℝ (Fin k),
            ∏ l, Real.exp (max (-ay) (min (x.ofLp l) ay)) ∂(multivariateGaussian 0
              (Matrix.of fun l l' =>
                β ^ 2 * ((N : ℝ) / ((N : ℝ) + 1)) * R (j l) (j l') ^ 2)))
        (γ[Fin N × Fin N]) :=
      integrable_finsetSum _ fun k _ =>
        (integrable_finsetSum _ fun j _ => (hprod k j).mul_const _).const_mul _
    exact this.congr (Filter.Eventually.of_forall fun u => (hGy u).symm)
  have hsub : ∫ u, (F u - (Gz u - Gy u)) ∂(γ[Fin N × Fin N]) =
      (∫ u, F u ∂(γ[Fin N × Fin N])) - ∫ u, (Gz u - Gy u) ∂(γ[Fin N × Fin N]) :=
    integral_sub hFi (hGzi.sub hGyi)
  rw [hFeq, ← hsub, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ε)
    (Filter.Eventually.of_forall fun u => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    exact hpt u
  · rw [probReal_univ, mul_one]

end Approximation

end Cavity

end SpinGlasses
