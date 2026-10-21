/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityInterpolation
public import LeanMachineLearning.SpinGlasses.FreeEnergy
public import LeanMachineLearning.SpinGlasses.GaussianComparison
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint

/-!
# The finite cavity partition-function identity

These deterministic identities are the algebraic first step in Talagrand's
Proposition 1.6.8.  They sum out the last Ising spin from an unnormalised
partition function.  The first statement is independent of the SK model; the
second inserts the `FinPairs` decomposition of the SK interaction.  In
particular, the latter can be applied with the common coefficient
`β / √N = β₊ / √(N+1)` without defining a second Hamiltonian or a bundled
partition-function object.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace SpinGlasses

/-- Model-independent single-spin summation: summing out an Ising spin
`ε ∈ ℤˣ` against an arbitrary base weight `A` and field `L`. -/
theorem sum_exp_prod_units {α : Type*} [Fintype α] (A L : α → ℝ) :
    (∑ x : α × ℤˣ, Real.exp (A x.1 + (x.2 : ℝ) * L x.1)) =
      2 * ∑ a : α, Real.exp (A a) * Real.cosh (L a) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Real.exp_add, sum_units_int]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [show (fun a : α => Real.exp (A a) * Real.exp (L a) + Real.exp (A a) * Real.exp (-L a)) =
      fun a => 2 * (Real.exp (A a) * Real.cosh (L a)) by
        funext a; rw [Real.cosh_eq]; ring]
  rw [← Finset.mul_sum]

/-- **Unnormalised finite cavity identity.**  Summing the final Ising coordinate of
`exp (A ρ + ε L ρ)` gives `2 exp (A ρ) cosh (L ρ)`.  This is the partition-function
counterpart of `integral_count_tilted_fin_snoc_cavity_units`, and applies to any finite
base energy and cavity field. -/
theorem sum_exp_fin_snoc_cavity (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) :
    (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) *
        L (fun i => σ i.castSucc))) =
      2 * ∑ ρ : Fin N → ℤˣ, Real.exp (A ρ) * Real.cosh (L ρ) := by
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (Equiv.prodComm (Fin N → ℤˣ) ℤˣ).trans (Fin.snocEquiv fun _ => ℤˣ)
  rw [← e.sum_comp]
  simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply,
    Fin.snoc_castSucc, Fin.snoc_last]
  exact sum_exp_prod_units A L

/-- **Logarithmic finite cavity identity.**  Taking the logarithm of the last-spin
partition-function factorization splits it into the old partition function and the logarithm
of the old Gibbs average of `cosh L`.  This is the general algebraic core of Talagrand's
Eq. (1.176), before any SK specialization or disorder expectation. -/
theorem log_sum_exp_fin_snoc_cavity (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) :
    Real.log (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) *
        L (fun i => σ i.castSucc))) =
      Real.log 2 + Real.log (∑ ρ : Fin N → ℤˣ, Real.exp (A ρ)) +
        Real.log (∫ ρ : Fin N → ℤˣ, Real.cosh (L ρ) ∂Measure.count.tilted A) := by
  rw [sum_exp_fin_snoc_cavity]
  have hpos : 0 < ∑ ρ : Fin N → ℤˣ, Real.exp (A ρ) * Real.cosh (L ρ) :=
    Finset.sum_pos (fun ρ _ => mul_pos (Real.exp_pos _) (Real.cosh_pos _)) Finset.univ_nonempty
  rw [Real.log_mul two_ne_zero hpos.ne']
  have havg := log_integral_count_tilted A (fun ρ => Real.cosh (L ρ))
    (fun ρ => Real.cosh_pos (L ρ))
  linarith

/-- Split a pairwise SK energy and its uniform external field into its old-spin energy and
its final-spin cavity field.  The coefficient is arbitrary, which is exactly what is needed
for Talagrand's `β₊` comparison. -/
theorem sk_cavity_energy_snoc (N : ℕ) (c h : ℝ)
    (g : FinPairs (N + 1) → ℝ) (σ : Fin (N + 1) → ℤˣ) :
    c * (∑ p : FinPairs (N + 1),
      g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) =
      (c * ∑ p : FinPairs N,
        g (oldPair N p) * (σ p.val.1.castSucc : ℝ) * (σ p.val.2.castSucc : ℝ) +
        h * ∑ i : Fin N, (σ i.castSucc : ℝ)) +
      (σ (Fin.last N) : ℝ) *
        (c * ∑ i : Fin N, g (lastPair N i) * (σ i.castSucc : ℝ) + h) := by
  rw [sum_sk_pairs_succ_cavity, Fin.sum_univ_castSucc]
  ring

/-- The interaction coefficient of the `(N+1)`-spin system at
`β₊ = β √(1 + 1/N)` is the coefficient `β / √N` of its old `N`-spin system. -/
theorem sk_beta_plus_coefficient (N : ℕ) (β : ℝ) (hN : 0 < N) :
    (Real.sqrt (N + 1 : ℝ))⁻¹ * (β * Real.sqrt (1 + (N : ℝ)⁻¹)) =
      (Real.sqrt (N : ℝ))⁻¹ * β := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
  have hsNp : Real.sqrt (N + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have harg : 1 + (N : ℝ)⁻¹ = (N + 1 : ℝ) / N := by field_simp
  rw [harg, Real.sqrt_div (by positivity)]
  field_simp

/-- The two independent Gaussian coefficients in Talagrand's Eq. (1.174) have the
variance of the `β / √N` coefficient.  This is the scalar covariance calculation needed by a
Gaussian Gram-law proof of the distributional change from `β` to `β₊`. -/
theorem sk_beta_plus_variance (N : ℕ) (β : ℝ) (hN : 0 < N) :
    ((Real.sqrt (N + 1 : ℝ))⁻¹ * β) ^ 2 +
      (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹) ^ 2 =
      ((Real.sqrt (N : ℝ))⁻¹ * β) ^ 2 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNp0 : (0 : ℝ) < N + 1 := by positivity
  have hprod : (0 : ℝ) < (N : ℝ) * (N + 1) := mul_pos hN0 hNp0
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
  have hsNp : Real.sqrt (N + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNp0).ne'
  have hsprod : Real.sqrt ((N : ℝ) * (N + 1)) ≠ 0 := (Real.sqrt_pos.2 hprod).ne'
  simp only [mul_pow]
  rw [inv_pow, inv_pow, inv_pow, Real.sq_sqrt hN0.le,
    Real.sq_sqrt hNp0.le, Real.sq_sqrt hprod.le]
  field_simp

/-- **Talagrand's Eq. (1.174), Gaussian-coordinate law.**  The old disorder with coefficient
`β / √N` has the law of the sum of independent disorders with coefficients
`β / √(N+1)` and `β / √(N(N+1))`.  Applying this equality of pushforward measures to the
SK Hamiltonian is the distributional step in the free-energy comparison. -/
theorem map_pi_gaussianReal_sk_beta_plus (N : ℕ) (β : ℝ) (hN : 0 < N) :
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).map
      (fun g p => (Real.sqrt (N : ℝ))⁻¹ * β * g p) =
      ((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)).map
          (fun q p => (Real.sqrt (N + 1 : ℝ))⁻¹ * β * q.1 p +
            β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * q.2 p) := by
  exact ProbabilityTheory.map_pi_gaussianReal_scale_eq_prod_linear_combo
    ((Real.sqrt (N + 1 : ℝ))⁻¹ * β)
    (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹)
    ((Real.sqrt (N : ℝ))⁻¹ * β) (sk_beta_plus_variance N β hN).symm

/-- **Talagrand's Eq. (1.175), log-partition law transport.**  The Gaussian-coordinate law
of Eq. (1.174) transports the logarithmic partition function of the `(N+1)`-spin system to
the two independent disorder blocks which are used in Eq. (1.176).  This is an exact equality
of integrals; no interpolation estimate has entered yet. -/
theorem integral_log_partition_sk_beta_plus_eq (N : ℕ) (β h : ℝ) (hN : 0 < N) :
    ∫ g : FinPairs (N + 1) → ℝ,
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          ∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
      ∫ q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp ((∑ p : FinPairs (N + 1),
            ((Real.sqrt (N + 1 : ℝ))⁻¹ * β * q.1 p +
              β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * q.2 p) *
              (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ)))
        ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  let F : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
    Real.log (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp ((∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ)))
  have hF : Measurable F := by
    dsimp [F]
    simpa only [one_mul] using measurable_log_sum_exp (H := fun (g : FinPairs (N + 1) → ℝ)
      (σ : Fin (N + 1) → ℤˣ) =>
      (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))
      (by intro σ; fun_prop) 1
  simpa only [F, one_mul, Finset.mul_sum, mul_assoc, mul_add, add_mul] using
    ProbabilityTheory.integral_pi_gaussianReal_scale_eq_prod_linear_combo
      ((Real.sqrt (N + 1 : ℝ))⁻¹ * β)
      (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹)
      ((Real.sqrt (N : ℝ))⁻¹ * β) (sk_beta_plus_variance N β hN).symm hF

/-- **Talagrand's Eq. (1.175), pointwise Gibbs factorization.**  The log partition function
after adding an independent pair-disorder block equals the unperturbed log partition function
plus the logarithm of the corresponding Gibbs average of the exponential perturbation.  This
is a direct SK specialization of the generic finite Gibbs perturbation identity. -/
theorem log_partition_sk_pair_perturb (N : ℕ) (a b h : ℝ)
    (g g' : FinPairs (N + 1) → ℝ) :
    Real.log (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (a * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i, (σ i : ℝ) + b * (∑ p : FinPairs (N + 1),
          g' p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)))) =
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp (a * (∑ p : FinPairs (N + 1),
          g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) +
        Real.log (∫ σ : Fin (N + 1) → ℤˣ,
          Real.exp (b * ∑ p : FinPairs (N + 1),
            g' p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
          ∂Measure.count.tilted (fun σ =>
            a * (∑ p : FinPairs (N + 1),
              g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) := by
  exact log_sum_exp_add_eq_log_sum_exp_add_log_integral_exp
    (fun σ : Fin (N + 1) → ℤˣ =>
      a * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))
    (fun σ => b * ∑ p : FinPairs (N + 1),
      g' p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))

/-- Rewriting a constant multiple of the pair-spin coefficient vector against a Gaussian
vector.  This keeps the finite Gaussian integrability statement below independent of a
particular SK normalization. -/
theorem dotProduct_const_pair_spin (M : ℕ) (c : ℝ)
    (σ : Fin M → ℤˣ) (g : FinPairs M → ℝ) :
    (fun p : FinPairs M => c * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) ⬝ᵥ g =
      c * ∑ p : FinPairs M, g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ) := by
  rw [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Expand a pairwise Hamiltonian driven by a linear combination of two disorder blocks.
This deterministic identity is kept coefficient-agnostic so the Gaussian law transport and the
Gibbs perturbation factorization use exactly the same normal form. -/
theorem sk_pair_linear_combo_expand (N : ℕ) (a b h : ℝ)
    (g g' : FinPairs (N + 1) → ℝ) (σ : Fin (N + 1) → ℤˣ) :
    (∑ p : FinPairs (N + 1),
      (a * g p + b * g' p) * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) =
      a * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) +
        b * (∑ p : FinPairs (N + 1),
          g' p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) := by
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The two-block finite SK log-partition function is integrable.  This is the analytic
side condition needed to integrate the pointwise Gibbs factorization in Eq. (1.175), and is
an immediate specialization of the generic affine-Gaussian partition-function theorem. -/
theorem integrable_log_partition_sk_pair (N : ℕ) (a b h : ℝ) :
    Integrable (fun q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ) =>
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp (a * (∑ p : FinPairs (N + 1),
          q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) +
          b * (∑ p : FinPairs (N + 1),
            q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)))))
      ((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  refine (integrable_log_sum_exp_linear_gaussian_prod
    (fun (σ : Fin (N + 1) → ℤˣ) p => a * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
    (fun (σ : Fin (N + 1) → ℤˣ) p => b * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
    (fun (σ : Fin (N + 1) → ℤˣ) => h * ∑ i, (σ i : ℝ))).congr ?_
  exact ae_of_all _ fun q => by
    apply congrArg Real.log
    apply Finset.sum_congr rfl
    intro σ _
    apply congrArg Real.exp
    rw [dotProduct_const_pair_spin, dotProduct_const_pair_spin]
    ring

/-- The one-block instance of `integrable_log_partition_sk_pair`.  Kept separate because it
is exactly the marginal integrability hypothesis needed by the product-integral Fubini step. -/
theorem integrable_log_partition_sk (M : ℕ) (a h : ℝ) :
    Integrable (fun g : FinPairs M → ℝ =>
      Real.log (∑ σ : Fin M → ℤˣ,
        Real.exp (a * (∑ p : FinPairs M,
          g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))))
      (Measure.pi fun _ : FinPairs M => gaussianReal 0 1) := by
  refine (integrable_log_sum_exp_linear_gaussian
    (fun (σ : Fin M → ℤˣ) p => a * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
    (fun (σ : Fin M → ℤˣ) => h * ∑ i, (σ i : ℝ))).congr ?_
  exact ae_of_all _ fun g => by
    apply congrArg Real.log
    apply Finset.sum_congr rfl
    intro σ _
    apply congrArg Real.exp
    rw [dotProduct_const_pair_spin]

/-- **Talagrand's Eq. (1.175), integrated Gibbs factorization.**  The law-transported
two-block partition function splits into the one-block free energy and the expectation of the
logarithmic Gibbs perturbation.  The preceding integrability theorems make every use of
`integral_add` legitimate. -/
theorem integral_log_partition_sk_pair_perturb (N : ℕ) (a b h : ℝ) :
    ∫ q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp (a * (∑ p : FinPairs (N + 1),
          q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) +
          b * (∑ p : FinPairs (N + 1),
            q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      (∫ g : FinPairs (N + 1) → ℝ,
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp (a * (∑ p : FinPairs (N + 1),
            g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      ∫ q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
        Real.log (∫ σ : Fin (N + 1) → ℤˣ,
          Real.exp (b * ∑ p : FinPairs (N + 1),
            q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
          ∂Measure.count.tilted (fun σ =>
            a * (∑ p : FinPairs (N + 1),
              q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ)))
        ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  let μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
  let F : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
    Real.log (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (a * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ)))
  let P : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ) → ℝ := fun q =>
    Real.log (∫ σ : Fin (N + 1) → ℤˣ,
      Real.exp (b * ∑ p : FinPairs (N + 1),
        q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
      ∂Measure.count.tilted (fun σ =>
        a * (∑ p : FinPairs (N + 1),
          q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ)))
  have hF : Integrable F μ := by
    simpa only [F, μ] using integrable_log_partition_sk (N + 1) a h
  have hC : Integrable (fun q =>
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp (a * (∑ p : FinPairs (N + 1),
          q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) +
          b * (∑ p : FinPairs (N + 1),
            q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))))) (μ.prod μ) :=
    integrable_log_partition_sk_pair N a b h
  have hP : Integrable P (μ.prod μ) := by
    refine (hC.sub (hF.comp_fst μ)).congr (ae_of_all _ fun q => ?_)
    apply sub_eq_iff_eq_add.mpr
    change _ = P q + F q.1
    calc
      _ = F q.1 + P q := log_partition_sk_pair_perturb N a b h q.1 q.2
      _ = _ := add_comm _ _
  calc
    _ = ∫ q, F q.1 + P q ∂(μ.prod μ) := integral_congr_ae (ae_of_all _ fun q => by
      dsimp only [F, P]
      exact log_partition_sk_pair_perturb N a b h q.1 q.2)
    _ = (∫ q, F q.1 ∂(μ.prod μ)) + ∫ q, P q ∂(μ.prod μ) :=
      integral_add (hF.comp_fst μ) hP
    _ = _ := by
      rw [integral_prod_fun_fst_of_isProbabilityMeasure μ μ F]

/-- **Talagrand's Eq. (1.172), pointwise partition-function form.**  At a common pair
coefficient `c`, the `(N+1)`-spin partition function is twice the old-spin partition sum
weighted by the hyperbolic cosine of its final-spin cavity field.  Taking
`c = β / √N = β₊ / √(N+1)` gives the book's comparison of `Z_{N+1}(β₊)` with `Z_N(β)`. -/
theorem sum_exp_sk_cavity_snoc (N : ℕ) (c h : ℝ)
    (g : FinPairs (N + 1) → ℝ) :
    (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (c * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) =
      2 * ∑ ρ : Fin N → ℤˣ,
        Real.exp (c * (∑ p : FinPairs N,
          g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)) *
          Real.cosh (c * ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h) := by
  simp_rw [sk_cavity_energy_snoc N c h g]
  exact sum_exp_fin_snoc_cavity N
    (fun ρ => c * (∑ p : FinPairs N,
      g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ))
    (fun ρ => c * ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h)

/-- **Talagrand's Eq. (1.172), `β₊` form.**  For `N > 0`, set
`β₊ = β √(1 + 1/N)`.  The left side is the `(N+1)`-spin partition function at
`β₊`; the right side uses the genuine `N`-spin interaction coefficient `β / √N`.
This is a pointwise identity in the enlarged disorder. -/
theorem sum_exp_sk_cavity_beta_plus (N : ℕ) (β h : ℝ) (hN : 0 < N)
    (g : FinPairs (N + 1) → ℝ) :
    (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ *
        (β * Real.sqrt (1 + (N : ℝ)⁻¹)) *
        (∑ p : FinPairs (N + 1),
          g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) =
      2 * ∑ ρ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs N,
            g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)) *
          Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
            ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h) := by
  rw [sk_beta_plus_coefficient N β hN]
  exact sum_exp_sk_cavity_snoc N ((Real.sqrt (N : ℝ))⁻¹ * β) h g

/-- **Talagrand's Eq. (1.173), pointwise logarithmic cavity identity.**  Pointwise in the
disorder, the log partition function of the `(N+1)`-spin system at coefficient
`β / √N = β₊ / √(N+1)` splits into `log 2`, the `N`-spin log partition function, and the log
Gibbs average of `cosh` of the final-spin cavity field. -/
theorem log_sum_exp_sk_cavity_snoc (N : ℕ) (c h : ℝ)
    (g : FinPairs (N + 1) → ℝ) :
    Real.log (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (c * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) =
      Real.log 2 +
      Real.log (∑ ρ : Fin N → ℤˣ,
        Real.exp (c * (∑ p : FinPairs N,
          g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ))) +
      Real.log (∫ ρ : Fin N → ℤˣ,
        Real.cosh (c * ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h)
        ∂Measure.count.tilted (fun ρ =>
          c * (∑ p : FinPairs N,
            g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ))) := by
  simp_rw [sk_cavity_energy_snoc N c h g]
  exact log_sum_exp_fin_snoc_cavity N
    (fun ρ => c * (∑ p : FinPairs N,
      g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ))
    (fun ρ => c * ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h)

/-- **Talagrand's Eq. (1.175), integrated expectation comparison.**  The expectation of the
`(N+1)`-spin log partition function at coefficient `β / √N = β₊ / √(N+1)` equals the
unperturbed `(N+1)`-spin free energy at `β` plus the expectation of the independent pair-disorder
Gibbs perturbation. -/
theorem integral_log_partition_sk_beta_plus_eq_perturb (N : ℕ) (β h : ℝ) (hN : 0 < N) :
    (∫ g : FinPairs (N + 1) → ℝ,
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
    (∫ g : FinPairs (N + 1) → ℝ,
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
    ∫ q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
      Real.log (∫ σ : Fin (N + 1) → ℤˣ,
        Real.exp (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
        ∂Measure.count.tilted (fun σ =>
          (Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  let a := (Real.sqrt (N + 1 : ℝ))⁻¹ * β
  let b := β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹
  rw [integral_log_partition_sk_beta_plus_eq N β h hN]
  simp_rw [sk_pair_linear_combo_expand]
  exact integral_log_partition_sk_pair_perturb N a b h

/-- **Talagrand's Eq. (1.173), integrated cavity split.**  Integrating the pointwise cavity
identity over the full Gaussian disorder splits the `β₊` log partition expectation into `log 2`,
the unperturbed `N`-spin free energy at `β`, and the expected log Gibbs average of `cosh` of the
cavity field. -/
theorem integral_log_partition_sk_cavity_split (N : ℕ) (β h : ℝ) :
    (∫ g : FinPairs (N + 1) → ℝ,
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
    Real.log 2 +
    (∫ g : FinPairs N → ℝ,
      Real.log (∑ ρ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs N, g p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
          h * ∑ i, (ρ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) +
    (∫ w : (FinPairs N → ℝ) × (Fin N → ℝ),
      Real.log (∫ ρ : Fin N → ℤˣ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
          ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
        ∂Measure.count.tilted (fun ρ =>
          (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, w.1 p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
            h * ∑ i, (ρ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1))) := by
  let μ_all := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
  let μ_old := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  let μ_last := Measure.pi fun _ : Fin N => gaussianReal 0 1
  let c := (Real.sqrt (N : ℝ))⁻¹ * β
  let π : (FinPairs (N + 1) → ℝ) → (FinPairs N → ℝ) × (Fin N → ℝ) :=
    fun g => (fun p => g (oldPair N p), fun i => g (lastPair N i))
  have hπ : MeasurePreserving π μ_all (μ_old.prod μ_last) :=
    measurePreserving_sk_cavity_disorder N
  let F_old : (FinPairs N → ℝ) → ℝ := fun g' =>
    Real.log (∑ ρ : Fin N → ℤˣ,
      Real.exp (c * (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
        h * ∑ i, (ρ i : ℝ)))
  let H : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun w =>
    Real.log (∫ ρ : Fin N → ℤˣ,
      Real.cosh (c * ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
      ∂Measure.count.tilted (fun ρ =>
        c * (∑ p : FinPairs N, w.1 p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
        h * ∑ i, (ρ i : ℝ)))
  let F_total : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
    Real.log (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (c * (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i, (σ i : ℝ)))
  have hF_old : Integrable F_old μ_old := integrable_log_partition_sk N c h
  have hF_old_prod : Integrable (fun w => F_old w.1) (μ_old.prod μ_last) :=
    hF_old.comp_fst μ_last
  have hF_old_comp : Integrable (fun g => F_old (π g).1) μ_all :=
    hπ.integrable_comp_of_integrable hF_old_prod
  have hF_total : Integrable F_total μ_all := integrable_log_partition_sk (N + 1) c h
  have hLog2 : Integrable (fun _ : FinPairs (N + 1) → ℝ => Real.log 2) μ_all :=
    integrable_const (Real.log 2)
  have hptw : ∀ g, F_total g = Real.log 2 + F_old (π g).1 + H (π g) :=
    fun g => log_sum_exp_sk_cavity_snoc N c h g
  have hH_comp : Integrable (fun g => H (π g)) μ_all := by
    have heq : (fun g => H (π g)) = fun g => F_total g - Real.log 2 - F_old (π g).1 := by
      funext g
      rw [hptw g]
      ring
    rw [heq]
    exact (hF_total.sub hLog2).sub hF_old_comp
  have hsum_int : (∫ g, F_total g ∂μ_all) = (∫ g, Real.log 2 + F_old (π g).1 + H (π g) ∂μ_all) :=
    integral_congr_ae (ae_of_all _ fun g => hptw g)
  have h_add1 : Integrable (fun g => Real.log 2 + F_old (π g).1) μ_all := hLog2.add hF_old_comp
  rw [integral_add h_add1 hH_comp, integral_add hLog2 hF_old_comp] at hsum_int
  rw [integral_const, probReal_univ, one_smul] at hsum_int
  have h_old_eq : (∫ g, F_old (π g).1 ∂μ_all) = ∫ g', F_old g' ∂μ_old := by
    have hG_meas : AEStronglyMeasurable
        (fun w : (FinPairs N → ℝ) × (Fin N → ℝ) => F_old w.1) (μ_all.map π) := by
      rw [hπ.map_eq]
      exact hF_old_prod.aestronglyMeasurable
    rw [← integral_map hπ.measurable.aemeasurable hG_meas, hπ.map_eq,
      integral_prod_fun_fst_of_isProbabilityMeasure μ_old μ_last F_old]
  have hF_old_meas : Measurable F_old := by
    dsimp [F_old]
    refine (Finset.measurable_sum _ fun ρ _ => ?_).log
    apply Measurable.exp
    fun_prop
  have h_H_eq : (∫ g, H (π g) ∂μ_all) = ∫ w, H w ∂(μ_old.prod μ_last) := by
    have hH_decomp : ∀ w, H w =
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp ((c * (∑ p : FinPairs N,
            w.1 p * (σ p.val.1.castSucc : ℝ) * (σ p.val.2.castSucc : ℝ)) +
            h * ∑ i : Fin N, (σ i.castSucc : ℝ)) +
            (σ (Fin.last N) : ℝ) *
              (c * ∑ i : Fin N, w.2 i * (σ i.castSucc : ℝ) + h))) -
        Real.log 2 - F_old w.1 := by
      intro w
      dsimp [H, F_old]
      have := log_sum_exp_fin_snoc_cavity N
        (fun ρ => c * (∑ p : FinPairs N,
          w.1 p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ))
        (fun ρ => c * ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
      linarith
    have h_tot_meas : Measurable (fun w : (FinPairs N → ℝ) × (Fin N → ℝ) =>
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp ((c * (∑ p : FinPairs N,
            w.1 p * (σ p.val.1.castSucc : ℝ) * (σ p.val.2.castSucc : ℝ)) +
            h * ∑ i : Fin N, (σ i.castSucc : ℝ)) +
            (σ (Fin.last N) : ℝ) *
              (c * ∑ i : Fin N, w.2 i * (σ i.castSucc : ℝ) + h)))) := by
      refine (Finset.measurable_sum _ fun σ _ => ?_).log
      apply Measurable.exp
      fun_prop
    have hH_meas_fun : Measurable H := by
      rw [funext hH_decomp]
      exact (h_tot_meas.sub measurable_const).sub (hF_old_meas.comp measurable_fst)
    have hH_aestrong : AEStronglyMeasurable H (μ_all.map π) := by
      rw [hπ.map_eq]
      exact hH_meas_fun.aestronglyMeasurable
    rw [← integral_map hπ.measurable.aemeasurable hH_aestrong, hπ.map_eq]
  rw [h_old_eq, h_H_eq] at hsum_int
  exact hsum_int

/-- **Talagrand's Eq. (1.176), exact free-energy increment identity.**  The difference
between `(N+1) p_{N+1}(β)` and `N p_N(β)` is exactly `log 2` plus the expected log Gibbs average
of `cosh` of the cavity field, minus the expected log Gibbs average of the exponential
pair perturbation.  This is an exact finite identity valid for all `N > 0`, `β`, `h`. -/
theorem sk_free_energy_increment_eq (N : ℕ) (β h : ℝ) (hN : 0 < N) :
    (∫ g : FinPairs (N + 1) → ℝ,
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
    (∫ g : FinPairs N → ℝ,
      Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs N, g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    Real.log 2 +
    (∫ w : (FinPairs N → ℝ) × (Fin N → ℝ),
      Real.log (∫ ρ : Fin N → ℤˣ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
          ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
        ∂Measure.count.tilted (fun ρ =>
          (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, w.1 p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
            h * ∑ i, (ρ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1))) -
    ∫ q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
      Real.log (∫ σ : Fin (N + 1) → ℤˣ,
        Real.exp (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
        ∂Measure.count.tilted (fun σ =>
          (Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  have h1 := integral_log_partition_sk_beta_plus_eq_perturb N β h hN
  have h2 := integral_log_partition_sk_cavity_split N β h
  linarith

/-- **Algebraic decomposition of the free energy increment deviation from `A(β, h, q)`.**
The constant `A(β, h, q) = log 2 + (β² / 4) (1 - q)² + 𝔼 log cosh` matches exactly the
difference between `(β² / 2) (1 - q) + 𝔼 log cosh` and `(β² / 4) (1 - q²)`. -/
theorem sk_free_energy_step_algebra (β q : ℝ) (log_cosh cavity_cosh perturb : ℝ) :
    (Real.log 2 + cavity_cosh - perturb) -
      (Real.log 2 + β ^ 2 / 4 * (1 - q) ^ 2 + log_cosh) =
    (cavity_cosh - (β ^ 2 / 2 * (1 - q) + log_cosh)) -
      (perturb - β ^ 2 / 4 * (1 - q ^ 2)) := by
  ring

/-- **Triangle-inequality reduction for the cavity free-energy increment.**  Bounding the cavity
`cosh` error and the pair perturbation error bounds the total error against `A(β, h, q)`. -/
theorem abs_sk_free_energy_step_sub_le (β q : ℝ) (log_cosh cavity_cosh perturb : ℝ) :
    |(Real.log 2 + cavity_cosh - perturb) -
      (Real.log 2 + β ^ 2 / 4 * (1 - q) ^ 2 + log_cosh)| ≤
    |cavity_cosh - (β ^ 2 / 2 * (1 - q) + log_cosh)| +
      |perturb - β ^ 2 / 4 * (1 - q ^ 2)| := by
  rw [sk_free_energy_step_algebra]
  exact abs_sub _ _

/-- **Assembly theorem for Proposition 1.6.8 (Talagrand Eq. 1.170).**  Combining the exact
cavity increment identity (Eq. 1.176) with the cavity `cosh` estimate (Eq. 1.181) and the pair
perturbation estimate (Eq. 1.182) yields the quantitative rate
`K (1 / N + ν(|R_{1,2} - q|))` against `A(β, h, q)`. -/
theorem sk_cavity_free_energy_step_le_of_estimates (β q : ℝ) (N : ℕ) (hN : 0 < N)
    (log_cosh cavity_cosh perturb ν K1 K2 K3 K : ℝ)
    (h_cosh : |cavity_cosh - (β ^ 2 / 2 * (1 - q) + log_cosh)| ≤ K1 * ν)
    (h_perturb : |perturb - β ^ 2 / 4 * (1 - q ^ 2)| ≤ K2 / (N : ℝ) + K3 * ν)
    (hK1 : K2 ≤ K) (hK2 : K1 + K3 ≤ K) (hν : 0 ≤ ν) :
    |(Real.log 2 + cavity_cosh - perturb) -
      (Real.log 2 + β ^ 2 / 4 * (1 - q) ^ 2 + log_cosh)| ≤
    K * (1 / (N : ℝ) + ν) := by
  have h_tri := abs_sk_free_energy_step_sub_le β q log_cosh cavity_cosh perturb
  have hNpos : 0 ≤ 1 / (N : ℝ) := by positivity
  have h_add := add_le_add (mul_le_mul_of_nonneg_right hK1 hNpos)
    (mul_le_mul_of_nonneg_right hK2 hν)
  have : K2 / (N : ℝ) = K2 * (1 / (N : ℝ)) := by ring
  have : K * (1 / (N : ℝ) + ν) = K * (1 / (N : ℝ)) + K * ν := by ring
  linarith

/-- **Talagrand's Eq. (1.181), cavity `cosh` interpolation estimate.**  For any interpolating
path `φ : ℝ → ℝ` between the cavity `cosh` expectation at `0` and the decoupled standard
Gaussian expectation at `π / 2`, if its derivative along the trigonometric path has deviation from
`-β² (1 - q)` bounded by `2 * K1 * ν`, then the distance between the cavity `cosh` observable
and `(β² / 2) (1 - q) + 𝔼 log cosh(β z √q + h)` is at most `K1 * ν`. -/
theorem sk_cavity_cosh_estimate_le (β q : ℝ) (log_cosh cavity_cosh ν K1 : ℝ)
    (φ : ℝ → ℝ) (h0 : φ 0 = cavity_cosh) (hpi : φ (Real.pi / 2) = log_cosh)
    (hd : ∀ s, ∃ D, HasDerivAt φ (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |D - (-β ^ 2 * (1 - q))| ≤ 2 * K1 * ν)) :
    |cavity_cosh - (β ^ 2 / 2 * (1 - q) + log_cosh)| ≤ K1 * ν := by
  have hkey := Real.abs_sub_sub_half_le_of_exists_hasDerivAt (φ := φ)
    (C := -β ^ 2 * (1 - q)) (K := 2 * K1 * ν) hd
  rw [h0, hpi] at hkey
  rw [show log_cosh - cavity_cosh - (-β ^ 2 * (1 - q)) / 2 =
      -(cavity_cosh - (β ^ 2 / 2 * (1 - q) + log_cosh)) by ring, abs_neg] at hkey
  linarith

/-- **Talagrand's Eq. (1.182), pair perturbation interpolation estimate.**  For any interpolating
path `ψ : ℝ → ℝ` between the pair perturbation expectation at `0` and `0` at `π / 2`, if its
derivative along the trigonometric path has deviation from `-(β² / 2) (1 - q²)` bounded by
`2 * (K2 / N + K3 * ν)`, then the distance between the pair perturbation observable and
`(β² / 4) (1 - q²)` is at most `K2 / N + K3 * ν`. -/
theorem sk_pair_perturb_estimate_le (β q : ℝ) (N : ℕ) (perturb ν K2 K3 : ℝ)
    (ψ : ℝ → ℝ) (h0 : ψ 0 = perturb) (hpi : ψ (Real.pi / 2) = 0)
    (hd : ∀ s, ∃ D, HasDerivAt ψ (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |D - (-β ^ 2 / 2 * (1 - q ^ 2))| ≤
        2 * (K2 / (N : ℝ) + K3 * ν))) :
    |perturb - β ^ 2 / 4 * (1 - q ^ 2)| ≤ K2 / (N : ℝ) + K3 * ν := by
  have hkey := Real.abs_sub_sub_half_le_of_exists_hasDerivAt (φ := ψ)
    (C := -β ^ 2 / 2 * (1 - q ^ 2)) (K := 2 * (K2 / (N : ℝ) + K3 * ν)) hd
  rw [h0, hpi] at hkey
  rw [show 0 - perturb - (-β ^ 2 / 2 * (1 - q ^ 2)) / 2 =
      -(perturb - β ^ 2 / 4 * (1 - q ^ 2)) by ring, abs_neg] at hkey
  linarith

/-- **Proposition 1.6.8 (Talagrand Eq. 1.170).**  The free-energy increment `(N+1) p_{N+1} - N p_N`
deviates from the replica-symmetric cavity constant `A(β, h, q) = log 2 + (β² / 4) (1 - q)² +
𝔼 log cosh` by at most `K (1 / N + ν)`.  This is proved by combining the exact free-energy
increment identity (Eq. 1.176) with the cavity `cosh` interpolation estimate (Eq. 1.181) and
the pair perturbation interpolation estimate (Eq. 1.182) via
`sk_cavity_free_energy_step_le_of_estimates`. -/
theorem cavity_free_energy_step_le (N : ℕ) (β h q : ℝ) (hN : 0 < N)
    (log_cosh cavity_cosh perturb ν K1 K2 K3 K : ℝ)
    (h_inc : (∫ g : FinPairs (N + 1) → ℝ,
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
    (∫ g : FinPairs N → ℝ,
      Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs N, g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    Real.log 2 + cavity_cosh - perturb)
    (h_cosh : |cavity_cosh - (β ^ 2 / 2 * (1 - q) + log_cosh)| ≤ K1 * ν)
    (h_perturb : |perturb - β ^ 2 / 4 * (1 - q ^ 2)| ≤ K2 / (N : ℝ) + K3 * ν)
    (hK1 : K2 ≤ K) (hK2 : K1 + K3 ≤ K) (hν : 0 ≤ ν) :
    |(∫ g : FinPairs (N + 1) → ℝ,
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ,
          Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (Real.log 2 + β ^ 2 / 4 * (1 - q) ^ 2 + log_cosh)| ≤
    K * (1 / (N : ℝ) + ν) := by
  rw [h_inc]
  exact sk_cavity_free_energy_step_le_of_estimates β q N hN log_cosh cavity_cosh perturb
    ν K1 K2 K3 K h_cosh h_perturb hK1 hK2 hν

/-- **Proposition 1.6.8 (Talagrand Eq. 1.170), closed form with exact cavity increment.**
Specialization of `cavity_free_energy_step_le` where the increment identity is automatically
supplied by `sk_free_energy_increment_eq`. -/
theorem sk_cavity_free_energy_step_le (N : ℕ) (β h q : ℝ) (hN : 0 < N)
    (log_cosh ν K1 K2 K3 K : ℝ)
    (h_cosh : |(∫ w : (FinPairs N → ℝ) × (Fin N → ℝ),
      Real.log (∫ ρ : Fin N → ℤˣ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
          ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
        ∂Measure.count.tilted (fun ρ =>
          (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, w.1 p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
            h * ∑ i, (ρ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1))) -
      (β ^ 2 / 2 * (1 - q) + log_cosh)| ≤ K1 * ν)
    (h_perturb : |(∫ q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
      Real.log (∫ σ : Fin (N + 1) → ℤˣ,
        Real.exp (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
        ∂Measure.count.tilted (fun σ =>
          (Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))) -
      β ^ 2 / 4 * (1 - q ^ 2)| ≤ K2 / (N : ℝ) + K3 * ν)
    (hK1 : K2 ≤ K) (hK2 : K1 + K3 ≤ K) (hν : 0 ≤ ν) :
    |(∫ g : FinPairs (N + 1) → ℝ,
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g : FinPairs N → ℝ,
        Real.log (∑ σ : Fin N → ℤˣ,
          Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (Real.log 2 + β ^ 2 / 4 * (1 - q) ^ 2 + log_cosh)| ≤
    K * (1 / (N : ℝ) + ν) := by
  have h_inc := sk_free_energy_increment_eq N β h hN
  rw [h_inc]
  exact sk_cavity_free_energy_step_le_of_estimates β q N hN log_cosh _ _
    ν K1 K2 K3 K h_cosh h_perturb hK1 hK2 hν

end SpinGlasses
