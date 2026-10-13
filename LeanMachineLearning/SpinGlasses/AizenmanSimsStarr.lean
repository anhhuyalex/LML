/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Cesaro
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.SpinGlasses.Concentration

/-!
# The Aizenman–Sims–Starr scheme

Let `Z_N = ∑_σ exp (β H_N(σ))` be the partition function of the Sherrington–Kirkpatrick model and
`A_N = 𝔼 log Z_{N+1} - 𝔼 log Z_N` ([Panchenko, 2013, Eqs. (1.48)–(1.58)]).  Then
`F_N = N⁻¹ 𝔼 log Z_N = N⁻¹ ∑_{j<N} A_j` (the Cesàro representation, `Z_0 = 1`), and the increment
`A_N` is computed through the *cavity* decomposition of the disorder.

## The cavity decomposition, in law

Write a configuration of `N + 1` spins as `ρ = (ε, σ)` with `ε = ρ 0` the cavity spin and `σ` the
`N` remaining spins.  The disorder `G` of size `N + 1` splits into the `N × N` block `u`
(coordinates `u (i, j) = g_{i+1, j+1}`) and the L-shaped cavity block `ζ`
(`ζ (inl j) = g_{0, j}`, `ζ (inr i) = g_{i+1, 0}`).  Then, *in law*,

  `H_{N+1}(ε, σ) = H'(σ) + ε z(σ) + (√(N+1))⁻¹ g_{00}`,

with `H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)`, `z(σ) = (√(N+1))⁻¹ ∑ᵢ (g_{0,i+1} + g_{i+1,0}) σ_i`
([Panchenko, 2013, Eqs. (1.50)–(1.52)]); and `H_N(σ) = H'(σ) + y(σ)` with an independent copy
`y(σ) = (√(N(N+1)))⁻¹ σ ⬝ (v σ)` of the `N × N` block (Eqs. (1.53)–(1.54)).

The statements are *distributional* rather than pathwise: both sides are centered Gaussian
families with the same covariance, so they have the same law (`ForMathlib/Probability/Moments/
GaussianGram.lean`) and any functional of the Hamiltonian, e.g. `𝔼 log Z_{N+1}`, can be computed
on the product of standard Gaussian blocks.  No change of variables on the nested disorder
`Fin (N+1) → Fin (N+1) → ℝ` is needed: the covariance check is the sum identity
`∑ (ρᵢ ρⱼ)(τᵢ τⱼ) = (ρ ⬝ τ)²` split along `Fin.sum_univ_succ`.  No definitions are introduced:
the fields `H'`, `z`, `y` are written out.

## Main declarations

* `SpinGlasses.integral_comp_skHamiltonian_succ`, `SpinGlasses.integral_comp_skHamiltonian_eq_add`:
  the two cavity decompositions in law.
* `SpinGlasses.integral_log_partition_succ_eq`, `SpinGlasses.integral_log_partition_eq_aux`
  (Eqs. (1.55)–(1.56)): `𝔼 log Z_{N+1}` and `𝔼 log Z_N` as expectations of
  `log ∑_σ exp (β H'(σ)) · 2 cosh (β z(σ))` and `log ∑_σ exp (β (H'(σ) + y(σ)))`.
* `SpinGlasses.aizenman_sims_starr_representation` (Eq. (1.58)): `A_N` is the expectation, over
  the auxiliary Gibbs measure `G'` of `H'`, of `log ⟨2 cosh (β z)⟩' - log ⟨exp (β y)⟩'`; the
  normalization `Z'` cancels.
* `SpinGlasses.integral_cavity_z_mul_z`, `SpinGlasses.integral_cavity_y_mul_y` (Eq. (1.59)): the
  covariances of the cavity fields depend on the overlap only.
* `SpinGlasses.inv_mul_integral_log_partition_eq_inv_mul_sum_range` (Eq. (1.49)) and
  `SpinGlasses.liminf_inv_mul_integral_log_partition_ge` (Cesàro).

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Matrix Topology

namespace SpinGlasses

/-! ### Deterministic algebra of the cavity split -/

section Algebra

/-- **Summing out the cavity spin:** a configuration of `N + 1` spins is a cavity spin `ε = ρ 0`
and `N` further spins, and `∑_{ε = ±1} exp (β ε z) = 2 cosh (β z)`.  For any fields `h`, `z` on
`N`-spin configurations and any constant `s`,
`∑_ρ exp (β (h ρ' + ε z ρ' + s)) = exp (β s) ∑_σ exp (β h σ) · 2 cosh (β z σ)`. -/
theorem sum_exp_cons_split {N : ℕ} (β s : ℝ) (h z : (Fin N → ℤˣ) → ℝ) :
    ∑ ρ : Fin (N + 1) → ℤˣ, Real.exp (β * (h (fun i => ρ i.succ) +
        ((ρ 0 : ℤ) : ℝ) * z (fun i => ρ i.succ) + s)) =
      Real.exp (β * s) * ∑ σ : Fin N → ℤˣ,
        Real.exp (β * h σ) * (2 * Real.cosh (β * z σ)) := by
  rw [← (Fin.consEquiv fun _ : Fin (N + 1) => ℤˣ).sum_comp, Fintype.sum_prod_type_right,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have e : ∀ x : ℤˣ, (Fin.consEquiv fun _ : Fin (N + 1) => ℤˣ) (x, σ) 0 = x ∧
      (fun i : Fin N => (Fin.consEquiv fun _ : Fin (N + 1) => ℤˣ) (x, σ) i.succ) = σ :=
    fun x => ⟨rfl, rfl⟩
  simp only [e]
  rw [UnitsInt.univ, Finset.sum_pair (by decide)]
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_mul]
  rw [Real.cosh_eq, show β * (h σ + z σ + s) = β * s + β * h σ + β * z σ by ring,
    show β * (h σ + -z σ + s) = β * s + β * h σ + -(β * z σ) by ring]
  simp only [Real.exp_add]
  ring

/-- **Gram identity of the cavity split:** the coefficient vectors of the `N × N` block and of
the L-shaped cavity block have inner products adding up to `(ρ ⬝ τ)²`, since
`∑_{i,j<N+1} ρᵢ ρⱼ τᵢ τⱼ` splits along `Fin.sum_univ_succ` into the corner, the cavity row and
column, and the `N × N` block. -/
theorem gram_succ (N : ℕ) (c : ℝ) (ρ τ : Fin (N + 1) → ℝ) :
    (fun p : Fin N × Fin N => c * (ρ p.1.succ * ρ p.2.succ)) ⬝ᵥ
        (fun p => c * (τ p.1.succ * τ p.2.succ)) +
      Sum.elim (fun j : Fin (N + 1) => c * (ρ 0 * ρ j)) (fun i : Fin N => c * (ρ i.succ * ρ 0)) ⬝ᵥ
        Sum.elim (fun j : Fin (N + 1) => c * (τ 0 * τ j)) (fun i : Fin N => c * (τ i.succ * τ 0)) =
      c ^ 2 * (ρ ⬝ᵥ τ) ^ 2 := by
  have h1 : ∑ i : Fin N, ∑ j : Fin N, ρ i.succ * ρ j.succ * (τ i.succ * τ j.succ) =
      (∑ i : Fin N, ρ i.succ * τ i.succ) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_succ,
    Sum.elim_inl, Sum.elim_inr]
  have h2 : ∑ i : Fin N, c * (ρ i.succ * ρ 0) * (c * (τ i.succ * τ 0)) =
      c ^ 2 * (ρ 0 * τ 0) * ∑ i : Fin N, ρ i.succ * τ i.succ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ j : Fin N, c * (ρ 0 * ρ j.succ) * (c * (τ 0 * τ j.succ)) =
      c ^ 2 * (ρ 0 * τ 0) * ∑ i : Fin N, ρ i.succ * τ i.succ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h4 : ∑ i : Fin N, ∑ j : Fin N, c * (ρ i.succ * ρ j.succ) * (c * (τ i.succ * τ j.succ)) =
      c ^ 2 * (∑ i : Fin N, ρ i.succ * τ i.succ) ^ 2 := by
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h3, h4]
  ring

/-- **Gram identity of the independent split:** the two `N × N` blocks have coefficient vectors
`c₁ σσ` and `c₂ σσ`, with `(σσ) ⬝ (ττ) = (σ ⬝ τ)²`. -/
theorem gram_eq_add (N : ℕ) (c₁ c₂ : ℝ) (σ τ : Fin N → ℝ) :
    (fun p : Fin N × Fin N => c₁ * (σ p.1 * σ p.2)) ⬝ᵥ (fun p => c₁ * (τ p.1 * τ p.2)) +
      (fun p : Fin N × Fin N => c₂ * (σ p.1 * σ p.2)) ⬝ᵥ (fun p => c₂ * (τ p.1 * τ p.2)) =
      (c₁ ^ 2 + c₂ ^ 2) * (σ ⬝ᵥ τ) ^ 2 := by
  have h1 : ∀ c : ℝ, ∑ i : Fin N, ∑ j : Fin N, c * (σ i * σ j) * (c * (τ i * τ j)) =
      c ^ 2 * (∑ i, σ i * τ i) ^ 2 := fun c => by
    rw [sq (∑ i, σ i * τ i), Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp only [dotProduct, Fintype.sum_prod_type]
  rw [h1, h1]
  ring

/-- A quadratic form in the `N × N` block `u` (read as the matrix `(u (i, j))`) is the linear
form with coefficient vector `c σᵢ σⱼ`. -/
theorem mul_dotProduct_mulVec_eq_dotProduct {N : ℕ} (c : ℝ) (σ : Fin N → ℝ)
    (u : Fin N × Fin N → ℝ) :
    c * (σ ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ σ)) =
      (fun p : Fin N × Fin N => c * (σ p.1 * σ p.2)) ⬝ᵥ u := by
  rw [ProbabilityTheory.dotProduct_mulVec_of_eq_sum]
  simp only [dotProduct, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Algebra

section Cavity

local notation "γ[" K "]" => Measure.pi fun _ : K => gaussianReal 0 1
local notation "𝒢[" N "]" =>
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The cavity decomposition in law** ([Panchenko, 2013, Eqs. (1.50)–(1.52)]).  For every
measurable functional `f` of the Hamiltonian of `N + 1` spins,
`𝔼 f (H_{N+1}) = 𝔼 f (H'(σ) + ε z(σ) + (√(N+1))⁻¹ g_{00})_{ρ = (ε, σ)}`, where the expectation on
the right is over the independent blocks `u ~ 𝒩(0,1)^{N×N}` and `ζ ~ 𝒩(0,1)^{(N+1) + N}`,
`H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)`, `z(σ) = (√(N+1))⁻¹ ∑ᵢ (ζ (inl (i+1)) + ζ (inr i)) σᵢ`,
`g_{00} = ζ (inl 0)`, and `ε = ρ 0`, `σ = (ρ (i+1))ᵢ`. -/
theorem integral_comp_skHamiltonian_succ (N : ℕ) {f : ((Fin (N + 1) → ℤˣ) → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ G, f (H (N + 1) G) ∂𝒢[N + 1] =
      ∫ q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ),
        f (fun ρ => (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((ρ i.succ : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((ρ i.succ : ℤ) : ℝ))) +
          ((ρ 0 : ℤ) : ℝ) * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
            ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((ρ i.succ : ℤ) : ℝ)) +
          (Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0)) ∂((γ[Fin N × Fin N]).prod
            (γ[Fin (N + 1) ⊕ Fin N])) := by
  have hH' : ∀ G σ, H (N + 1) G σ = (Real.sqrt (Fintype.card (Fin (N + 1))))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))) := fun G σ => by
    simpa only [Fintype.card_fin] using hH (N + 1) G σ
  have hc : (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 2 = ((N : ℝ) + 1)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [integral_comp_eq_integral_dotProduct_prod
    (X := fun ρ G => H (N + 1) G ρ)
    (fun ρ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
      (((ρ p.1.succ : ℤ) : ℝ) * ((ρ p.2.succ : ℤ) : ℝ)))
    (fun ρ => Sum.elim (fun j : Fin (N + 1) => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
        (((ρ 0 : ℤ) : ℝ) * ((ρ j : ℤ) : ℝ)))
      (fun i : Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ * (((ρ i.succ : ℤ) : ℝ) * ((ρ 0 : ℤ) : ℝ))))
    (hasGaussianLaw_skHamiltonian (H (N + 1)) hH')
    (integral_skHamiltonian_eq_zero (H (N + 1)) hH') (fun ρ τ => ?_) hf]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    congr 1
    funext ρ
    have h0 : ((ρ 0 : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq (ρ 0)
    rw [mul_dotProduct_mulVec_eq_dotProduct, add_assoc]
    congr 1
    simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, Sum.elim_inl, Sum.elim_inr]
    have h00 : (Real.sqrt ((N : ℝ) + 1))⁻¹ * (((ρ 0 : ℤ) : ℝ) * ((ρ 0 : ℤ) : ℝ)) *
        q.2 (Sum.inl 0) = (Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0) := by
      rw [← sq, h0, mul_one]
    have hsum : ∑ i : Fin N, (Real.sqrt ((N : ℝ) + 1))⁻¹ * (((ρ 0 : ℤ) : ℝ) *
          ((ρ i.succ : ℤ) : ℝ)) * q.2 (Sum.inl i.succ) +
        ∑ i : Fin N, (Real.sqrt ((N : ℝ) + 1))⁻¹ * (((ρ i.succ : ℤ) : ℝ) * ((ρ 0 : ℤ) : ℝ)) *
          q.2 (Sum.inr i) = ((ρ 0 : ℤ) : ℝ) * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((ρ i.succ : ℤ) : ℝ)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  · rw [integral_skHamiltonian_mul_skHamiltonian_units (H (N + 1)) hH' ρ τ]
    have := gram_succ N (Real.sqrt ((N : ℝ) + 1))⁻¹ (fun i => ((ρ i : ℤ) : ℝ))
      (fun i => ((τ i : ℤ) : ℝ))
    simp only [Fintype.card_fin, Nat.cast_succ]
    rw [this, hc]
    field_simp

/-- **The decomposition `H_N = H' + y` in law** ([Panchenko, 2013, Eqs. (1.53)–(1.54)]).  For every
measurable functional `f` of the Hamiltonian of `N ≥ 1` spins,
`𝔼 f (H_N) = 𝔼 f (H'(σ) + y(σ))_σ` for independent blocks `u, v ~ 𝒩(0,1)^{N×N}`, where
`H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)` and `y(σ) = (√(N(N+1)))⁻¹ σ ⬝ (v σ)`.  The covariances match
because `1/(N+1) + 1/(N(N+1)) = 1/N`, i.e. `N R² = N²/(N+1) R² + N/(N+1) R²`. -/
theorem integral_comp_skHamiltonian_eq_add {N : ℕ} (hN : 0 < N) {f : ((Fin N → ℤˣ) → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ G, f (H N G) ∂𝒢[N] =
      ∫ q : (Fin N × Fin N → ℝ) × (Fin N × Fin N → ℝ),
        f (fun σ => (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))) +
          (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.2 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))))
          ∂((γ[Fin N × Fin N]).prod (γ[Fin N × Fin N])) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hH' : ∀ G σ, H N G σ = (Real.sqrt (Fintype.card (Fin N)))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))) := fun G σ => by
    simpa only [Fintype.card_fin] using hH N G σ
  rw [integral_comp_eq_integral_dotProduct_prod
    (X := fun σ G => H N G σ)
    (fun σ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
      (((σ p.1 : ℤ) : ℝ) * ((σ p.2 : ℤ) : ℝ)))
    (fun σ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
      (((σ p.1 : ℤ) : ℝ) * ((σ p.2 : ℤ) : ℝ)))
    (hasGaussianLaw_skHamiltonian (H N) hH')
    (integral_skHamiltonian_eq_zero (H N) hH') (fun σ τ => ?_) hf]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    congr 1
    funext σ
    rw [mul_dotProduct_mulVec_eq_dotProduct, mul_dotProduct_mulVec_eq_dotProduct]
  · rw [integral_skHamiltonian_mul_skHamiltonian_units (H N) hH' σ τ,
      gram_eq_add N _ _ (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((τ i : ℤ) : ℝ)),
      inv_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    simp only [Fintype.card_fin]
    field_simp

end Cavity

end SpinGlasses
