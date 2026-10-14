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
`N` remaining spins.  (Panchenko puts the cavity site last; by relabeling invariance of the
Gaussian disorder it is the same, and `Fin.cons` / `Fin.succ` make the sums split by
`Fin.sum_univ_succ`.)  The disorder `G` of size `N + 1` splits into the `N × N` block `u`
(coordinates `u (i, j) = g_{i+1, j+1}`) and the L-shaped cavity block `ζ`
(`ζ (inl j) = g_{0, j}`, `ζ (inr i) = g_{i+1, 0}`).  Then, *in law* (`IdentDistrib`),

  `H_{N+1}(ε, σ) = H'(σ) + ε z(σ) + (√(N+1))⁻¹ g_{00}`,

with `H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)`, `z(σ) = (√(N+1))⁻¹ ∑ᵢ (g_{0,i+1} + g_{i+1,0}) σ_i`
([Panchenko, 2013, Eqs. (1.50)–(1.52)]); and `H_N(σ) = H'(σ) + y(σ)` with an independent copy
`y(σ) = (√(N(N+1)))⁻¹ σ ⬝ (v σ)` of the `N × N` block (Eqs. (1.53)–(1.54)).

The statements are *distributional* rather than pathwise: both sides are centered Gaussian
families with the same covariance, so they have the same law (`ForMathlib/Probability/Moments/
GaussianGram.lean`) and any functional of the Hamiltonian, e.g. `𝔼 log Z_{N+1}`, can be computed
on the product of standard Gaussian blocks.  This replaces the pathwise identity of the book
(and the independence of `H'`, `z`, `g_{00}` read off the entries of `G`) by a covariance check,
and avoids a measure-preserving change of variables on the *nested* disorder
`Fin (N+1) → Fin (N+1) → ℝ`: the check is the sum identity `∑ (ρᵢ ρⱼ)(τᵢ τⱼ) = (ρ ⬝ τ)²` split along
`Fin.sum_univ_succ` (`gram_succ`, `gram_eq_add`).  No definitions are introduced: the fields
`H'`, `z`, `y` are written out.

## Main declarations

* `SpinGlasses.map_skHamiltonian_succ`, `SpinGlasses.map_skHamiltonian_eq_add`: the two cavity
  decompositions in law.
* `SpinGlasses.integral_log_partition_succ_eq`, `SpinGlasses.integral_log_partition_eq_aux`
  (Eqs. (1.55)–(1.56)): `𝔼 log Z_{N+1}` and `𝔼 log Z_N` as expectations of
  `log ∑_σ exp (β H'(σ)) · 2 cosh (β z(σ))` and `log ∑_σ exp (β (H'(σ) + y(σ)))`.
* `SpinGlasses.aizenman_sims_starr_representation` (Eq. (1.58)): `A_N` is the expectation, over
  the auxiliary Gibbs measure `G'` of `H'`, of `log ⟨2 cosh (β z)⟩' - log ⟨exp (β y)⟩'`; the
  normalization `Z'` cancels.
* `SpinGlasses.integrable_and_eq_aizenman_sims_starr`: the same with the integrability of the
  integrand in `u`, for an integrand given by its defining equation.
* `SpinGlasses.integral_cavity_z_mul_z`, `SpinGlasses.integral_cavity_y_mul_y` (Eq. (1.59)): the
  covariances of the cavity fields depend on the overlap only; `SpinGlasses.hasGaussianLaw_cavity_z`,
  `SpinGlasses.hasGaussianLaw_cavity_y` and the centering lemmas show that the fields are centered
  Gaussian families.
* `SpinGlasses.inv_mul_integral_log_partition_eq` (Eq. (1.49)) and
  `SpinGlasses.liminf_increment_le_liminf_free_energy` (Cesàro,
  `ForMathlib/Analysis/Cesaro.lean`).

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

/-- The cavity field of `N + 1` spins in the blocks `(u, ζ)`:
`H'(σ) + ε z(σ) + (√(N+1))⁻¹ g_{00}` for `ρ = (ε, σ)`, equal to the linear form with coefficients
`(√(N+1))⁻¹ ρᵢ ρⱼ` on the `N × N` block and on the L-shaped block `ζ`. -/
private theorem cavity_eq_dotProduct (N : ℕ) (q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ))
    (ρ : Fin (N + 1) → ℤˣ) :
    (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((ρ i.succ : ℤ) : ℝ)) ⬝ᵥ
        (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((ρ i.succ : ℤ) : ℝ))) +
      ((ρ 0 : ℤ) : ℝ) * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((ρ i.succ : ℤ) : ℝ)) +
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0) =
    (fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
        (((ρ p.1.succ : ℤ) : ℝ) * ((ρ p.2.succ : ℤ) : ℝ))) ⬝ᵥ q.1 +
      Sum.elim (fun j : Fin (N + 1) => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
          (((ρ 0 : ℤ) : ℝ) * ((ρ j : ℤ) : ℝ)))
        (fun i : Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
          (((ρ i.succ : ℤ) : ℝ) * ((ρ 0 : ℤ) : ℝ))) ⬝ᵥ q.2 := by
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

/-- The cavity field is measurable in the blocks `(u, ζ)`. -/
private theorem measurable_cavity (N : ℕ) :
    Measurable fun (q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ)) (ρ : Fin (N + 1) → ℤˣ) =>
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((ρ i.succ : ℤ) : ℝ)) ⬝ᵥ
        (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((ρ i.succ : ℤ) : ℝ))) +
      ((ρ 0 : ℤ) : ℝ) * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((ρ i.succ : ℤ) : ℝ)) +
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0) := by
  have h := measurable_dotProduct_prod (A := Fin (N + 1) → ℤˣ)
    (K₁ := Fin N × Fin N) (K₂ := Fin (N + 1) ⊕ Fin N)
    (fun ρ p => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
      (((ρ p.1.succ : ℤ) : ℝ) * ((ρ p.2.succ : ℤ) : ℝ)))
    (fun ρ => Sum.elim (fun j => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
        (((ρ 0 : ℤ) : ℝ) * ((ρ j : ℤ) : ℝ)))
      (fun i => (Real.sqrt ((N : ℝ) + 1))⁻¹ * (((ρ i.succ : ℤ) : ℝ) * ((ρ 0 : ℤ) : ℝ))))
  convert h using 1
  funext q ρ
  exact cavity_eq_dotProduct N q ρ

/-- A coordinate of a standard Gaussian block is centered and integrable. -/
private theorem integral_coord_eq_zero {K : Type*} [Fintype K] (k : K) :
    ∫ ξ : K → ℝ, ξ k ∂(Measure.pi fun _ : K => gaussianReal 0 1) = 0 ∧
      Integrable (fun ξ : K → ℝ => ξ k) (Measure.pi fun _ : K => gaussianReal 0 1) := by
  classical
  have h := integral_dotProduct_pi_gaussianReal (κ := K) (Pi.single k 1)
  have h' := (memLp_dotProduct_pi_gaussianReal (κ := K) (Pi.single k 1)).integrable one_le_two
  simpa [single_dotProduct] using And.intro h h'

/-- **The measurable `log ∑ exp` functional.** -/
private theorem measurable_log_sum_exp_pi {M : ℕ} (β : ℝ) :
    Measurable fun x : (Fin M → ℤˣ) → ℝ => Real.log (∑ σ, Real.exp (β * x σ)) :=
  measurable_log_sum_exp (H := fun x : (Fin M → ℤˣ) → ℝ => x) (fun a => measurable_pi_apply a) β

/-- The SK Hamiltonian is a measurable function of the disorder with values in
`(Fin M → ℤˣ) → ℝ`. -/
private theorem measurable_skHamiltonian_pi
    (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ)))) (M : ℕ) :
    Measurable fun (G : Fin M → Fin M → ℝ) (σ : Fin M → ℤˣ) => H M G σ :=
  measurable_pi_iff.2 fun σ => by
    simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable (ι := Fin M) σ).1

/-- The cavity field `c (√(N+1))⁻¹ ∑ᵢ (ζ (inl (i+1)) + ζ (inr i)) ρᵢ` is a linear form of `ζ`. -/
theorem cavity_z_eq_dotProduct (N : ℕ) (c : ℝ) (ρ : Fin N → ℝ) (ζ : Fin (N + 1) ⊕ Fin N → ℝ) :
    c * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ρ i) =
      Sum.elim (Fin.cons 0 fun i => c * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ρ i))
        (fun i => c * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ρ i)) ⬝ᵥ ζ := by
  simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, Sum.elim_inl, Sum.elim_inr,
    Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add, add_mul, Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- **The cavity field `z` is a centered Gaussian family:** for any family `ρ s` of coefficient
vectors, `s ↦ c (√(N+1))⁻¹ ∑ᵢ (ζ (inl (i+1)) + ζ (inr i)) (ρ s)ᵢ` is jointly Gaussian in `ζ`. -/
theorem hasGaussianLaw_cavity_z {A : Type*} [Finite A] (N : ℕ) (c : ℝ) (ρ : A → Fin N → ℝ) :
    HasGaussianLaw (fun (ζ : Fin (N + 1) ⊕ Fin N → ℝ) (s : A) =>
      c * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ρ s i))
      (Measure.pi fun _ : Fin (N + 1) ⊕ Fin N => gaussianReal 0 1) := by
  have h := hasGaussianLaw_dotProduct_family (K := Fin (N + 1) ⊕ Fin N) fun s =>
    Sum.elim (Fin.cons 0 fun i => c * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ρ s i))
      (fun i => c * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ρ s i))
  convert h using 3 with ζ s
  exact cavity_z_eq_dotProduct N c (ρ s) ζ

/-- The cavity field `z` is centered. -/
theorem integral_cavity_z_eq_zero (N : ℕ) (c : ℝ) (ρ : Fin N → ℝ) :
    ∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
      c * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ρ i)
        ∂(Measure.pi fun _ : Fin (N + 1) ⊕ Fin N => gaussianReal 0 1) = 0 := by
  simp_rw [cavity_z_eq_dotProduct]
  exact integral_dotProduct_pi_gaussianReal _

/-- **The cavity field `y` is a centered Gaussian family:** for any family `ρ s` of vectors,
`s ↦ c ρ s ⬝ (v ρ s)` is jointly Gaussian in the `N × N` block `v`. -/
theorem hasGaussianLaw_cavity_y {A : Type*} [Finite A] (N : ℕ) (c : ℝ) (ρ : A → Fin N → ℝ) :
    HasGaussianLaw (fun (v : Fin N × Fin N → ℝ) (s : A) =>
      c * (ρ s ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ ρ s)))
      (Measure.pi fun _ : Fin N × Fin N => gaussianReal 0 1) := by
  have h := hasGaussianLaw_dotProduct_family (K := Fin N × Fin N) fun s =>
    fun p : Fin N × Fin N => c * (ρ s p.1 * ρ s p.2)
  convert h using 3 with v s
  exact mul_dotProduct_mulVec_eq_dotProduct c (ρ s) v

/-- The cavity field `y` is centered. -/
theorem integral_cavity_y_eq_zero (N : ℕ) (c : ℝ) (ρ : Fin N → ℝ) :
    ∫ v : Fin N × Fin N → ℝ, c * (ρ ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ ρ))
      ∂(Measure.pi fun _ : Fin N × Fin N => gaussianReal 0 1) = 0 := by
  simp_rw [mul_dotProduct_mulVec_eq_dotProduct]
  exact integral_dotProduct_pi_gaussianReal _

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The cavity decomposition in law** ([Panchenko, 2013, Eqs. (1.50)–(1.52)]).  The Hamiltonian
of `N + 1` spins has the law of
`ρ = (ε, σ) ↦ H'(σ) + ε z(σ) + (√(N+1))⁻¹ g_{00}`, where the blocks `u ~ 𝒩(0,1)^{N×N}` and
`ζ ~ 𝒩(0,1)^{(N+1) + N}` are independent and
`H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)`, `z(σ) = (√(N+1))⁻¹ ∑ᵢ (ζ (inl (i+1)) + ζ (inr i)) σᵢ`,
`g_{00} = ζ (inl 0)`, `ε = ρ 0`, `σ = (ρ (i+1))ᵢ`.  Equivalently, `𝔼 f (H_{N+1}) = 𝔼 f (cavity)` for
measurable `f`. -/
theorem map_skHamiltonian_succ (N : ℕ) :
    IdentDistrib (fun G ρ => H (N + 1) G ρ)
      (fun (q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ)) (ρ : Fin (N + 1) → ℤˣ) =>
        (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((ρ i.succ : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((ρ i.succ : ℤ) : ℝ))) +
          ((ρ 0 : ℤ) : ℝ) * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
            ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((ρ i.succ : ℤ) : ℝ)) +
          (Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0))
      𝒢[N + 1] ((γ[Fin N × Fin N]).prod (γ[Fin (N + 1) ⊕ Fin N])) := by
  have hH' : ∀ G σ, H (N + 1) G σ = (Real.sqrt (Fintype.card (Fin (N + 1))))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))) := fun G σ => by
    simpa only [Fintype.card_fin] using hH (N + 1) G σ
  have hc : (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 2 = ((N : ℝ) + 1)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  have h := map_eq_map_dotProduct_prod (X := fun ρ G => H (N + 1) G ρ)
    (fun ρ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
      (((ρ p.1.succ : ℤ) : ℝ) * ((ρ p.2.succ : ℤ) : ℝ)))
    (fun ρ => Sum.elim (fun j : Fin (N + 1) => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
        (((ρ 0 : ℤ) : ℝ) * ((ρ j : ℤ) : ℝ)))
      (fun i : Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ * (((ρ i.succ : ℤ) : ℝ) * ((ρ 0 : ℤ) : ℝ))))
    (hasGaussianLaw_skHamiltonian (H (N + 1)) hH')
    (integral_skHamiltonian_eq_zero (H (N + 1)) hH') fun ρ τ => by
      rw [integral_skHamiltonian_mul_skHamiltonian_units (H (N + 1)) hH' ρ τ]
      have := gram_succ N (Real.sqrt ((N : ℝ) + 1))⁻¹ (fun i => ((ρ i : ℤ) : ℝ))
        (fun i => ((τ i : ℤ) : ℝ))
      simp only [Fintype.card_fin, Nat.cast_succ]
      rw [this, hc]
      field_simp
  refine ⟨(measurable_skHamiltonian_pi H hH (N + 1)).aemeasurable,
    (measurable_cavity N).aemeasurable, ?_⟩
  rw [h]
  congr 1
  funext q ρ
  exact (cavity_eq_dotProduct N q ρ).symm

/-- **The decomposition `H_N = H' + y` in law** ([Panchenko, 2013, Eqs. (1.53)–(1.54)]).  For
`N ≥ 1`, the Hamiltonian of `N` spins has the law of `σ ↦ H'(σ) + y(σ)` for independent blocks
`u, v ~ 𝒩(0,1)^{N×N}`, where `H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)` and
`y(σ) = (√(N(N+1)))⁻¹ σ ⬝ (v σ)`.  The covariances match because
`1/(N+1) + 1/(N(N+1)) = 1/N`, i.e. `N R² = N²/(N+1) R² + N/(N+1) R²`. -/
theorem map_skHamiltonian_eq_add {N : ℕ} (hN : 0 < N) :
    IdentDistrib (fun G σ => H N G σ)
      (fun (q : (Fin N × Fin N → ℝ) × (Fin N × Fin N → ℝ)) (σ : Fin N → ℤˣ) =>
        (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))) +
          (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.2 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))))
      𝒢[N] ((γ[Fin N × Fin N]).prod (γ[Fin N × Fin N])) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hH' : ∀ G σ, H N G σ = (Real.sqrt (Fintype.card (Fin N)))⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))) := fun G σ => by
    simpa only [Fintype.card_fin] using hH N G σ
  have h := map_eq_map_dotProduct_prod (X := fun σ G => H N G σ)
    (fun σ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
      (((σ p.1 : ℤ) : ℝ) * ((σ p.2 : ℤ) : ℝ)))
    (fun σ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
      (((σ p.1 : ℤ) : ℝ) * ((σ p.2 : ℤ) : ℝ)))
    (hasGaussianLaw_skHamiltonian (H N) hH')
    (integral_skHamiltonian_eq_zero (H N) hH') fun σ τ => by
      rw [integral_skHamiltonian_mul_skHamiltonian_units (H N) hH' σ τ,
        gram_eq_add N _ _ (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((τ i : ℤ) : ℝ)),
        inv_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      simp only [Fintype.card_fin]
      field_simp
  have hm := measurable_dotProduct_prod (A := Fin N → ℤˣ) (K₁ := Fin N × Fin N)
    (K₂ := Fin N × Fin N)
    (fun σ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
      (((σ p.1 : ℤ) : ℝ) * ((σ p.2 : ℤ) : ℝ)))
    (fun σ => fun p : Fin N × Fin N => (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
      (((σ p.1 : ℤ) : ℝ) * ((σ p.2 : ℤ) : ℝ)))
  have e : (fun (q : (Fin N × Fin N → ℝ) × (Fin N × Fin N → ℝ)) (σ : Fin N → ℤˣ) =>
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
          (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))) +
        (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
          (Matrix.of (fun i j => q.2 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ)))) = _ :=
    funext fun q => funext fun σ => by
      rw [mul_dotProduct_mulVec_eq_dotProduct, mul_dotProduct_mulVec_eq_dotProduct]
  refine ⟨(measurable_skHamiltonian_pi H hH N).aemeasurable, (e ▸ hm).aemeasurable, ?_⟩
  rw [h, e]

/-- **`𝔼 log Z_{N+1}` through the cavity** ([Panchenko, 2013, Eq. (1.55)]): summing out the cavity
spin gives `∑_ε exp (β ε z) = 2 cosh (β z)`, and the scalar Gaussian `g_{00}` shifts `log Z_{N+1}`
by the centered `β (√(N+1))⁻¹ g_{00}`, so
`𝔼 log Z_{N+1} = 𝔼 log ∑_σ exp (β H'(σ)) · 2 cosh (β z(σ))`. -/
theorem integral_log_partition_succ_eq {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    Integrable (fun q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ) =>
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => q.1 (i, j)) *ᵥ
                fun i => ((σ i : ℤ) : ℝ))))) *
            (2 * Real.cosh (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((σ i : ℤ) : ℝ))))))
        ((γ[Fin N × Fin N]).prod (γ[Fin (N + 1) ⊕ Fin N])) ∧
      ∫ G, Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ)) ∂𝒢[N + 1] =
      ∫ q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ),
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => q.1 (i, j)) *ᵥ
                fun i => ((σ i : ℤ) : ℝ))))) *
            (2 * Real.cosh (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((σ i : ℤ) : ℝ)))))
          ∂((γ[Fin N × Fin N]).prod (γ[Fin (N + 1) ⊕ Fin N])) := by
  have hid := (map_skHamiltonian_succ H hH N).comp (measurable_log_sum_exp_pi (M := N + 1) β)
  have hHm := measurable_skHamiltonian_pi H hH (N + 1)
  -- the log-partition function is integrable, hence so is its image under the cavity law
  have hint : Integrable (fun G => Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ))) 𝒢[N + 1] :=
    integrable_log_sum_exp hβ (H := fun G ρ => H (N + 1) G ρ) (fun ρ => measurable_pi_iff.1 hHm ρ)
      fun ρ => by simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable ρ).2
  have hint' := hid.integrable_snd hint
  rw [Function.comp_def] at hid
  -- peel off the centered shift `β (√(N+1))⁻¹ g_{00}`
  obtain ⟨h0, hi0⟩ := integral_coord_eq_zero (K := Fin (N + 1) ⊕ Fin N) (Sum.inl 0)
  have hshift_int : Integrable (fun q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ) =>
      β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0)))
      ((γ[Fin N × Fin N]).prod (γ[Fin (N + 1) ⊕ Fin N])) :=
    ((hi0.comp_snd (γ[Fin N × Fin N])).const_mul _).const_mul _
  have hshift : ∫ q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ),
      β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0))
        ∂((γ[Fin N × Fin N]).prod (γ[Fin (N + 1) ⊕ Fin N])) = 0 := by
    rw [integral_const_mul, integral_const_mul,
      integral_fun_snd (fun ζ : Fin (N + 1) ⊕ Fin N → ℝ => ζ (Sum.inl 0)), h0]
    simp
  obtain ⟨R, hRdef⟩ : ∃ R : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ) → ℝ, ∀ q,
      R q = Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => q.1 (i, j)) *ᵥ
                fun i => ((σ i : ℤ) : ℝ))))) *
            (2 * Real.cosh (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((σ i : ℤ) : ℝ))))) :=
    ⟨_, fun _ => rfl⟩
  have hpt : ∀ q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ),
      Real.log (∑ ρ : Fin (N + 1) → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
          ((fun i => ((ρ i.succ : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => q.1 (i, j)) *ᵥ
            fun i => ((ρ i.succ : ℤ) : ℝ))) +
        ((ρ 0 : ℤ) : ℝ) * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
          ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((ρ i.succ : ℤ) : ℝ)) +
        (Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0)))) =
      β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0)) + R q := fun q => by
    have h := sum_exp_cons_split (N := N) β ((Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0))
      (fun σ => (Real.sqrt ((N : ℝ) + 1))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
        (Matrix.of (fun i j => q.1 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))))
      (fun σ => (Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (q.2 (Sum.inl i.succ) + q.2 (Sum.inr i)) * ((σ i : ℤ) : ℝ))
    rw [hRdef, h, Real.log_mul (Real.exp_pos _).ne', Real.log_exp]
    exact (Finset.sum_pos (fun σ _ => mul_pos (Real.exp_pos _) (by positivity))
      Finset.univ_nonempty).ne'
  have hRint : Integrable R ((γ[Fin N × Fin N]).prod (γ[Fin (N + 1) ⊕ Fin N])) :=
    (hint'.sub hshift_int).congr (ae_of_all _ fun q => by
      simp only [Function.comp_apply, Pi.sub_apply]
      rw [hpt q]
      ring)
  refine ⟨by rw [← funext hRdef]; exact hRint, hid.integral_eq.trans ?_⟩
  rw [← funext hRdef]
  calc _ = ∫ q : (Fin N × Fin N → ℝ) × (Fin (N + 1) ⊕ Fin N → ℝ),
        (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * q.2 (Sum.inl 0)) + R q)
        ∂((γ[Fin N × Fin N]).prod (γ[Fin (N + 1) ⊕ Fin N])) := integral_congr_ae (ae_of_all _ hpt)
    _ = _ := by rw [integral_add hshift_int hRint, hshift, zero_add]

/-- **`𝔼 log Z_N` through the cavity** ([Panchenko, 2013, Eq. (1.56)]): since `H_N = H' + y` in
law, `𝔼 log Z_N = 𝔼 log ∑_σ exp (β (H'(σ) + y(σ)))`. -/
theorem integral_log_partition_eq_aux {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    Integrable (fun q : (Fin N × Fin N → ℝ) × (Fin N × Fin N → ℝ) =>
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
            ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => q.1 (i, j)) *ᵥ
              fun i => ((σ i : ℤ) : ℝ))) +
          (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.2 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ)))))))
        ((γ[Fin N × Fin N]).prod (γ[Fin N × Fin N])) ∧
      ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N] =
      ∫ q : (Fin N × Fin N → ℝ) × (Fin N × Fin N → ℝ),
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
            ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => q.1 (i, j)) *ᵥ
              fun i => ((σ i : ℤ) : ℝ))) +
          (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
            (Matrix.of (fun i j => q.2 (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))))))
          ∂((γ[Fin N × Fin N]).prod (γ[Fin N × Fin N])) := by
  have hid := (map_skHamiltonian_eq_add H hH hN).comp (measurable_log_sum_exp_pi (M := N) β)
  have hHm := measurable_skHamiltonian_pi H hH N
  have hint : Integrable (fun G => Real.log (∑ σ, Real.exp (β * H N G σ))) 𝒢[N] :=
    integrable_log_sum_exp hβ (H := fun G σ => H N G σ) (fun σ => measurable_pi_iff.1 hHm σ)
      fun σ => by simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable σ).2
  rw [Function.comp_def] at hid
  exact ⟨hid.integrable_snd hint, hid.integral_eq⟩

/-- **Integrability in `u` and the Aizenman–Sims–Starr representation.**  This is
`aizenman_sims_starr_representation` for a function `F` given by its defining equation `hF`,
together with the integrability of `F` (needed to bound `A_N` by pointwise estimates in `u`). -/
theorem integrable_and_eq_aizenman_sims_starr {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (F : (Fin N × Fin N → ℝ) → ℝ)
    (hF : ∀ u, F u =
        ((∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
                Real.log (∫ σ, 2 * Real.cosh (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
                    ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)))
                  ∂(Measure.count.tilted fun σ : Fin N → ℤˣ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
                    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
                      fun i => ((σ i : ℤ) : ℝ)))))) ∂(γ[Fin (N + 1) ⊕ Fin N])) -
              ∫ v : Fin N × Fin N → ℝ,
                Real.log (∫ σ, Real.exp (β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
                    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
                      fun i => ((σ i : ℤ) : ℝ)))))
                  ∂(Measure.count.tilted fun σ : Fin N → ℤˣ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
                    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
                      fun i => ((σ i : ℤ) : ℝ)))))) ∂(γ[Fin N × Fin N]))) :
    Integrable F (γ[Fin N × Fin N]) ∧
      (∫ G, Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N] =
        ∫ u, F u ∂(γ[Fin N × Fin N]) := by
  obtain ⟨h1i, h1⟩ := integral_log_partition_succ_eq H hH hβ N
  obtain ⟨h2i, h2⟩ := integral_log_partition_eq_aux H hH hβ hN
  have hae : ∀ᵐ u ∂(γ[Fin N × Fin N]),
      ((∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
          Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
                fun i => ((σ i : ℤ) : ℝ))))) *
            (2 * Real.cosh (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)))))
          ∂(γ[Fin (N + 1) ⊕ Fin N])) -
        ∫ v : Fin N × Fin N → ℝ,
          Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
                fun i => ((σ i : ℤ) : ℝ))) +
            (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
              (Matrix.of (fun i j => v (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ))))))
          ∂(γ[Fin N × Fin N])) = F u := by
    filter_upwards [h1i.prod_right_ae, h2i.prod_right_ae] with u hu1 hu2
    rw [hF u]
    have e1 := fun ζ : Fin (N + 1) ⊕ Fin N → ℝ => log_integral_count_tilted
      (fun σ : Fin N → ℤˣ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
          fun i => ((σ i : ℤ) : ℝ)))))
      (fun σ : Fin N → ℤˣ => 2 * Real.cosh (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)))) fun σ => by positivity
    have e2 := fun v : Fin N × Fin N → ℝ => log_integral_count_tilted
      (fun σ : Fin N → ℤˣ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
          fun i => ((σ i : ℤ) : ℝ)))))
      (fun σ : Fin N → ℤˣ => Real.exp (β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
          fun i => ((σ i : ℤ) : ℝ)))))) fun σ => Real.exp_pos _
    have e2' : ∀ v : Fin N × Fin N → ℝ,
        Real.log (∫ σ, Real.exp (β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
            ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
              fun i => ((σ i : ℤ) : ℝ)))))
          ∂(Measure.count.tilted fun σ : Fin N → ℤˣ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
            ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
              fun i => ((σ i : ℤ) : ℝ)))))) =
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
              ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
                fun i => ((σ i : ℤ) : ℝ))) +
            (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ
              (Matrix.of (fun i j => v (i, j)) *ᵥ fun i => ((σ i : ℤ) : ℝ)))))) -
          Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
            ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
              fun i => ((σ i : ℤ) : ℝ)))))) := fun v => by
      rw [e2 v]
      congr 2
      exact Finset.sum_congr rfl fun σ _ => by rw [← Real.exp_add, ← mul_add]
    simp_rw [e1, e2']
    rw [integral_sub hu1 (integrable_const _), integral_sub hu2 (integrable_const _)]
    simp
  refine ⟨(h1i.integral_prod_left.sub h2i.integral_prod_left).congr hae, ?_⟩
  rw [h1, h2, integral_prod _ h1i, integral_prod _ h2i,
    ← integral_sub h1i.integral_prod_left h2i.integral_prod_left]
  exact integral_congr_ae hae

/-- **The Aizenman–Sims–Starr representation** ([Panchenko, 2013, Eq. (1.58)]).  Let `G'` be the
auxiliary Gibbs measure of `H'(σ) = (√(N+1))⁻¹ σ ⬝ (u σ)` (`Measure.count.tilted (β H')`).  Then
`A_N = 𝔼 log Z_{N+1} - 𝔼 log Z_N` is the `u`-average of
`𝔼_ζ log ⟨2 cosh (β z(σ))⟩' - 𝔼_v log ⟨exp (β y(σ))⟩'`, where `⟨·⟩'` is the average under `G'`
and the cavity fields `z`, `y` are independent of `G'`.  Indeed both partition functions are
`Z'(u)` times the corresponding `G'`-average (`log_integral_count_tilted`), so `log Z'(u)`
cancels. -/
theorem aizenman_sims_starr_representation {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    (∫ G, Real.log (∑ ρ, Real.exp (β * H (N + 1) G ρ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N] =
      ∫ u : Fin N × Fin N → ℝ,
        ((∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
            Real.log (∫ σ, 2 * Real.cosh (β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
                ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ((σ i : ℤ) : ℝ)))
              ∂(Measure.count.tilted fun σ : Fin N → ℤˣ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
                ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
                  fun i => ((σ i : ℤ) : ℝ)))))) ∂(γ[Fin (N + 1) ⊕ Fin N])) -
          ∫ v : Fin N × Fin N → ℝ,
            Real.log (∫ σ, Real.exp (β * ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ *
                ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ
                  fun i => ((σ i : ℤ) : ℝ)))))
              ∂(Measure.count.tilted fun σ : Fin N → ℤˣ => β * ((Real.sqrt ((N : ℝ) + 1))⁻¹ *
                ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of (fun i j => u (i, j)) *ᵥ
                  fun i => ((σ i : ℤ) : ℝ)))))) ∂(γ[Fin N × Fin N])) ∂(γ[Fin N × Fin N]) :=
  (integrable_and_eq_aizenman_sims_starr H hH hβ hN _ fun _ => rfl).2

omit hH in
/-- **Covariance of the cavity field `z`** ([Panchenko, 2013, Eq. (1.59)]):
`𝔼 z(σ) z(τ) = 2 a_N R(σ, τ)` with `a_N = N / (N + 1)` and `R(σ, τ) = N⁻¹ σ ⬝ τ`.  It depends on
the configurations through the overlap only. -/
theorem integral_cavity_z_mul_z {N : ℕ} (hN : 0 < N) (σ τ : Fin N → ℝ) :
    ∫ ζ : Fin (N + 1) ⊕ Fin N → ℝ,
        ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * σ i) *
          ((Real.sqrt ((N : ℝ) + 1))⁻¹ * ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * τ i)
        ∂(Measure.pi fun _ : Fin (N + 1) ⊕ Fin N => gaussianReal 0 1) =
      2 * ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ)⁻¹ * (σ ⬝ᵥ τ)) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hz : ∀ (ρ : Fin N → ℝ) (ζ : Fin (N + 1) ⊕ Fin N → ℝ),
      (Real.sqrt ((N : ℝ) + 1))⁻¹ * ∑ i, (ζ (Sum.inl i.succ) + ζ (Sum.inr i)) * ρ i =
        Sum.elim (Fin.cons 0 fun i => (Real.sqrt ((N : ℝ) + 1))⁻¹ * ρ i)
          (fun i => (Real.sqrt ((N : ℝ) + 1))⁻¹ * ρ i) ⬝ᵥ ζ := fun ρ ζ => by
    simpa only [one_mul] using cavity_z_eq_dotProduct N 1 ρ ζ
  simp_rw [hz]
  rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
  simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, Sum.elim_inl, Sum.elim_inr,
    Fin.cons_zero, Fin.cons_succ]
  have hc : (Real.sqrt ((N : ℝ) + 1))⁻¹ * (Real.sqrt ((N : ℝ) + 1))⁻¹ = ((N : ℝ) + 1)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have : ∑ i : Fin N, (Real.sqrt ((N : ℝ) + 1))⁻¹ * σ i * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * τ i) =
      ((N : ℝ) + 1)⁻¹ * ∑ i, σ i * τ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← hc]; ring
  rw [this]
  field_simp
  ring

omit hH in
/-- **Covariance of the cavity field `y`** ([Panchenko, 2013, Eq. (1.59)]):
`𝔼 y(σ) y(τ) = a_N R(σ, τ)²`, `a_N = N / (N + 1)`. -/
theorem integral_cavity_y_mul_y {N : ℕ} (hN : 0 < N) (σ τ : Fin N → ℝ) :
    ∫ v : Fin N × Fin N → ℝ,
        ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * (σ ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ σ))) *
          ((Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ * (τ ⬝ᵥ (Matrix.of (fun i j => v (i, j)) *ᵥ τ)))
        ∂(Measure.pi fun _ : Fin N × Fin N => gaussianReal 0 1) =
      ((N : ℝ) / ((N : ℝ) + 1)) * ((N : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ 2 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  simp_rw [mul_dotProduct_mulVec_eq_dotProduct]
  rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
  have h := gram_eq_add N (Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))⁻¹ 0 σ τ
  simp only [zero_mul, zero_pow two_ne_zero] at h
  rw [show ((fun _ : Fin N × Fin N => (0 : ℝ)) ⬝ᵥ fun _ => (0 : ℝ)) = 0 by simp [dotProduct],
    add_zero, add_zero] at h
  rw [h, inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

end Cavity

section Cesaro

local notation "𝒢[" N "]" =>
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The empty system has `log Z_0 = 0`** (`Z_0 = 1`, [Panchenko, 2013, Eq. (1.48)]): the unique
configuration has energy `0`. -/
theorem integral_log_partition_zero (β : ℝ) :
    ∫ G, Real.log (∑ σ, Real.exp (β * H 0 G σ)) ∂𝒢[0] = 0 := by
  simp [hH]

/-- **The Cesàro representation of the free energy** ([Panchenko, 2013, Eq. (1.49)]):
`F_N = N⁻¹ 𝔼 log Z_N = N⁻¹ ∑_{j<N} A_j`, `A_j = 𝔼 log Z_{j+1} - 𝔼 log Z_j`, by telescoping and
`Z_0 = 1`. -/
theorem inv_mul_integral_log_partition_eq (β : ℝ) (N : ℕ) :
    (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N] =
      (N : ℝ)⁻¹ * ∑ j ∈ range N,
        ((∫ G, Real.log (∑ σ, Real.exp (β * H (j + 1) G σ)) ∂𝒢[j + 1]) -
          ∫ G, Real.log (∑ σ, Real.exp (β * H j G σ)) ∂𝒢[j]) := by
  rw [Finset.sum_range_sub (fun j => ∫ G, Real.log (∑ σ, Real.exp (β * H j G σ)) ∂𝒢[j]),
    integral_log_partition_zero H hH β, sub_zero]

/-- **Cesàro bound on the free energy** ([Panchenko, 2013, §1.3]): if the increments `A_N` are
bounded, `liminf_N A_N ≤ liminf_N F_N`.  Together with the limit `F_N → F`
(`sk_tendsto_free_energy`), the Aizenman–Sims–Starr scheme bounds `F` below by `liminf A_N`. -/
theorem liminf_increment_le_liminf_free_energy (β : ℝ)
    (hu : IsBoundedUnder (· ≤ ·) atTop fun N : ℕ =>
      (∫ G, Real.log (∑ σ, Real.exp (β * H (N + 1) G σ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N])
    (hu' : IsBoundedUnder (· ≥ ·) atTop fun N : ℕ =>
      (∫ G, Real.log (∑ σ, Real.exp (β * H (N + 1) G σ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N]) :
    liminf (fun N : ℕ => (∫ G, Real.log (∑ σ, Real.exp (β * H (N + 1) G σ)) ∂𝒢[N + 1]) -
        ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N]) atTop ≤
      liminf (fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ)) ∂𝒢[N])
        atTop := by
  have h := liminf_le_liminf_inv_mul_sum_range hu hu'
  simp only [← inv_mul_integral_log_partition_eq H hH β] at h
  exact h

end Cesaro

end SpinGlasses
