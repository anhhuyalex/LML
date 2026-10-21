/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityInterpolation
public import LeanMachineLearning.SpinGlasses.FreeEnergy
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound

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
  rw [Fintype.sum_prod_type]
  simp_rw [Real.exp_add, sum_units_int]
  simp only [Prod.swap_prod_mk]
  norm_num
  rw [show (fun ρ : Fin N → ℤˣ =>
      Real.exp (A ρ) * Real.exp (L ρ) + Real.exp (A ρ) * Real.exp (-L ρ)) =
      fun ρ => 2 * (Real.exp (A ρ) * Real.cosh (L ρ)) by
        funext ρ
        rw [Real.cosh_eq]
        ring]
  rw [← Finset.mul_sum]

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
theorem dotProduct_const_pair_spin (N : ℕ) (c : ℝ)
    (σ : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) :
    (fun p : FinPairs (N + 1) => c * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) ⬝ᵥ g =
      c * ∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ) := by
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
  have hsum (c : ℝ) (u : FinPairs (N + 1) → ℝ) :
      (∑ p : FinPairs (N + 1),
        c * u p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) =
        c * ∑ p : FinPairs (N + 1), u p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, hsum a g, hsum b g']
  ring

/-- The two-block finite SK log-partition function is integrable.  This is the analytic
side condition needed to integrate the pointwise Gibbs factorization in Eq. (1.175), and is
an immediate specialization of the generic affine-Gaussian partition-function theorem. -/
theorem integrable_log_partition_sk_pair (N : ℕ) (a b h : ℝ) :
    Integrable (fun q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ) =>
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp (a * (∑ p : FinPairs (N + 1),
          q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          b * (∑ p : FinPairs (N + 1),
            q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))))
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

/-- The one-block instance of `integrable_log_partition_sk_pair`.  Kept separate because it
is exactly the marginal integrability hypothesis needed by the product-integral Fubini step. -/
theorem integrable_log_partition_sk (N : ℕ) (a h : ℝ) :
    Integrable (fun g : FinPairs (N + 1) → ℝ =>
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp (a * (∑ p : FinPairs (N + 1),
          g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  refine (integrable_log_sum_exp_linear_gaussian
    (fun (σ : Fin (N + 1) → ℤˣ) p => a * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
    (fun (σ : Fin (N + 1) → ℤˣ) => h * ∑ i, (σ i : ℝ))).congr ?_
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
    simpa only [F, μ] using integrable_log_partition_sk N a h
  have hC : Integrable (fun q =>
      Real.log (∑ σ : Fin (N + 1) → ℤˣ,
        Real.exp (a * (∑ p : FinPairs (N + 1),
          q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) +
          b * (∑ p : FinPairs (N + 1),
            q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))))) (μ.prod μ) := by
    refine (integrable_log_partition_sk_pair N a b h).congr (ae_of_all _ fun q => ?_)
    apply congrArg Real.log
    apply Finset.sum_congr rfl
    intro σ _
    apply congrArg Real.exp
    ring
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
  let A : (Fin N → ℤˣ) → ℝ := fun ρ =>
    c * (∑ p : FinPairs N,
      g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)
  let L : (Fin N → ℤˣ) → ℝ := fun ρ =>
    c * ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h
  have hsplit : ∀ σ : Fin (N + 1) → ℤˣ,
      c * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) =
      A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc) := by
    intro σ
    exact sk_cavity_energy_snoc N c h g σ
  rw [show (fun σ : Fin (N + 1) → ℤˣ =>
      Real.exp (c * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) =
      fun σ => Real.exp (A (fun i => σ i.castSucc) +
        (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc)) by
        funext σ
        rw [hsplit]]
  simpa only [A, L] using sum_exp_fin_snoc_cavity N A L

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

end SpinGlasses
