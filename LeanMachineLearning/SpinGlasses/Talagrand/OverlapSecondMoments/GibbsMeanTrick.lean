/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal

/-!
# The Gibbs-mean trick (Talagrand, proof of Proposition 1.8.7)

For the Gibbs measure `μ = count.tilted A` on `Fin M → ℤˣ` with mean vector
`b_i = ⟨σ_i⟩`, the quantities `T_{ℓℓ'} = (σ^ℓ - b)·(σ^ℓ' - b)/M` of Eq. (1.245) depend on the
disorder through `b`, so Lemma 1.6.3 does not apply to them directly.  The book's remedy is to
"replace each occurrence of `b` by a replica that has never been used before".  Here this is
proved by coordinates: both `⟨T_{12}²⟩` and the six-replica average
`⟨(σ¹-σ²)·(σ⁴-σ⁵)/M · (σ¹-σ³)·(σ⁴-σ⁶)/M⟩` equal `M⁻² ∑_{ij} C_ij²`, where
`C_ij = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩` is the Gibbs covariance
(`integral_dev_dot_sq_eq_six_replicas`).  The six replicas are two independent blocks of three
(`integral_pi_fin_add_mul`), and each block averages to `C_ij`
(`integral_three_replicas_cov`).

## Main declarations

* `SpinGlasses.integral_dev_mul_dev`: `⟨(σ_i-b_i)(σ_j-b_j)⟩ = ⟨σ_iσ_j⟩ - b_ib_j = C_ij`.
* `SpinGlasses.integral_dev_pair_sq`: `⟨(σ¹_i-b_i)(σ²_i-b_i)(σ¹_j-b_j)(σ²_j-b_j)⟩ = C_ij²`.
* `SpinGlasses.integral_three_replicas_cov`: `⟨(σ¹_i-σ²_i)(σ¹_j-σ³_j)⟩ = C_ij`.
* `SpinGlasses.integral_six_replicas_cov_sq`: the six-replica average is `C_ij²`.
* `SpinGlasses.integral_dev_dot_sq_eq_six_replicas`: the sum over sites, and
  `SpinGlasses.integral_disorder_dev_dot_sq_eq_six_replicas`: averaged over the disorder.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.8.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace SpinGlasses

variable {M : ℕ} (A : (Fin M → ℤˣ) → ℝ)

variable (b : Fin M → ℝ)
  (hb : ∀ i, b i = ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) ∂(Measure.count.tilted A))

include hb in
/-- The Gibbs covariance `C_ij = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩` is the average of
`(σ_i - b_i)(σ_j - b_j)`, where `b_i = ⟨σ_i⟩`. -/
theorem integral_dev_mul_dev (i j : Fin M) :
    ∫ x : Fin M → ℤˣ, (((x i : ℤˣ) : ℝ) - b i) * (((x j : ℤˣ) : ℝ) - b j)
      ∂(Measure.count.tilted A) =
    (∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ) ∂(Measure.count.tilted A)) -
      b i * b j := by
  rw [hb i, hb j]
  exact covariance_eq_sub MemLp.of_discrete MemLp.of_discrete

include hb in
/-- **Two replicas deviating from the Gibbs mean:**
`⟨(σ¹_i - b_i)(σ²_i - b_i)(σ¹_j - b_j)(σ²_j - b_j)⟩ = C_ij²`. -/
theorem integral_dev_pair_sq (i j : Fin M) :
    ∫ τ : Fin 2 → Fin M → ℤˣ,
        ((((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 1 i : ℤˣ) : ℝ) - b i)) *
          ((((τ 0 j : ℤˣ) : ℝ) - b j) * (((τ 1 j : ℤˣ) : ℝ) - b j))
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted A) =
      ((∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ) ∂(Measure.count.tilted A)) -
        b i * b j) ^ 2 := by
  set μ : Measure (Fin M → ℤˣ) := Measure.count.tilted A with hμ
  set K := ∫ x : Fin M → ℤˣ, (((x i : ℤˣ) : ℝ) - b i) * (((x j : ℤˣ) : ℝ) - b j) ∂μ with hK
  rw [← integral_dev_mul_dev A b hb i j, ← hK]
  let Θ : (Fin M → ℤˣ) → (Fin M → ℤˣ) → ℝ := fun x y =>
    ((((x i : ℤˣ) : ℝ) - b i) * (((y i : ℤˣ) : ℝ) - b i)) *
      ((((x j : ℤˣ) : ℝ) - b j) * (((y j : ℤˣ) : ℝ) - b j))
  have h2 := integral_pi_fin_two μ Θ
  refine h2.trans ?_
  have e : ∀ x : Fin M → ℤˣ, ∫ y, Θ x y ∂μ =
      ((((x i : ℤˣ) : ℝ) - b i) * (((x j : ℤˣ) : ℝ) - b j)) * K := fun x => by
    rw [hK, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [Θ]
    ring
  simp_rw [e]
  rw [integral_mul_const, ← hK]
  ring

include hb in
/-- **Three replicas and a covariance:** `⟨(σ¹_i - σ²_i)(σ¹_j - σ³_j)⟩ = ⟨σ_iσ_j⟩ - b_i b_j`. -/
theorem integral_three_replicas_cov (i j : Fin M) :
    ∫ τ : Fin 3 → Fin M → ℤˣ,
        (((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) * (((τ 0 j : ℤˣ) : ℝ) - ((τ 2 j : ℤˣ) : ℝ))
        ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted A) =
      (∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ) ∂(Measure.count.tilted A)) -
        b i * b j := by
  set μ : Measure (Fin M → ℤˣ) := Measure.count.tilted A with hμ
  have e : ∀ τ : Fin 3 → Fin M → ℤˣ,
      (((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) * (((τ 0 j : ℤˣ) : ℝ) - ((τ 2 j : ℤˣ) : ℝ)) =
        ((τ 0 i : ℤˣ) : ℝ) * ((τ 0 j : ℤˣ) : ℝ) - ((τ 0 i : ℤˣ) : ℝ) * ((τ 2 j : ℤˣ) : ℝ) -
          ((τ 1 i : ℤˣ) : ℝ) * ((τ 0 j : ℤˣ) : ℝ) + ((τ 1 i : ℤˣ) : ℝ) * ((τ 2 j : ℤˣ) : ℝ) :=
    fun τ => by ring
  simp_rw [e]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite]
  have key : ∀ (a c : Fin 3), a ≠ c → ∀ H : (Fin M → ℤˣ) → (Fin M → ℤˣ) → ℝ,
      ∫ τ : Fin 3 → Fin M → ℤˣ, H (τ a) (τ c) ∂(Measure.pi fun _ : Fin 3 => μ) =
        ∫ x, ∫ y, H x y ∂μ ∂μ := fun a c hac H =>
    (integral_pi_count_tilted_pair hac _ H).trans (integral_pi_fin_two _ H)
  have hprod : ∀ (u v : (Fin M → ℤˣ) → ℝ), ∫ x, ∫ y, u x * v y ∂μ ∂μ =
      (∫ x, u x ∂μ) * ∫ y, v y ∂μ := fun u v => by
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
  have t1 := key 0 1 (by decide)
    (fun x _ => ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ))
  have t2 := key 0 2 (by decide)
    (fun x y => ((x i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ))
  have t3 := key 1 0 (by decide)
    (fun x y => ((x i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ))
  have t4 := key 1 2 (by decide)
    (fun x y => ((x i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ))
  rw [t1, t2, t3, t4, hprod, ← hb i, ← hb j]
  simp only [integral_const, probReal_univ, one_smul]
  ring

include hb in
/-- **Six replicas and a covariance:** two independent blocks of three replicas give
`⟨(σ¹_i - σ²_i)(σ¹_j - σ³_j)(σ⁴_i - σ⁵_i)(σ⁴_j - σ⁶_j)⟩ = C_ij²`. -/
theorem integral_six_replicas_cov_sq (i j : Fin M) :
    ∫ τ : Fin 6 → Fin M → ℤˣ,
        ((((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) * (((τ 0 j : ℤˣ) : ℝ) - ((τ 2 j : ℤˣ) : ℝ))) *
          ((((τ 3 i : ℤˣ) : ℝ) - ((τ 4 i : ℤˣ) : ℝ)) * (((τ 3 j : ℤˣ) : ℝ) - ((τ 5 j : ℤˣ) : ℝ)))
        ∂(Measure.pi fun _ : Fin 6 => Measure.count.tilted A) =
      ((∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ) ∂(Measure.count.tilted A)) -
        b i * b j) ^ 2 := by
  set μ : Measure (Fin M → ℤˣ) := Measure.count.tilted A with hμ
  let F : (Fin 3 → Fin M → ℤˣ) → ℝ := fun ρ =>
    (((ρ 0 i : ℤˣ) : ℝ) - ((ρ 1 i : ℤˣ) : ℝ)) * (((ρ 0 j : ℤˣ) : ℝ) - ((ρ 2 j : ℤˣ) : ℝ))
  have h6 := integral_pi_fin_add_mul μ 3 3 F F
  have h3 : ∫ ρ : Fin 3 → Fin M → ℤˣ, F ρ ∂(Measure.pi fun _ : Fin 3 => μ) =
      (∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ) ∂μ) - b i * b j :=
    integral_three_replicas_cov A b hb i j
  rw [h3] at h6
  exact h6.trans (sq _).symm

include hb in
/-- **The Gibbs-mean trick for `T_{12}²` (proof of Proposition 1.8.7).**  With `b = ⟨σ⟩` and
`T_{12} = (σ¹ - b)·(σ² - b)/M`, the Gibbs average of `T_{12}²` equals the six-replica average of
`(σ¹-σ²)·(σ⁴-σ⁵)/M · (σ¹-σ³)·(σ⁴-σ⁶)/M`: both are `M⁻² ∑_{ij} C_ij²`. -/
theorem integral_dev_dot_sq_eq_six_replicas :
    ∫ τ : Fin 2 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 1 i : ℤˣ) : ℝ) - b i)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted A) =
      ∫ τ : Fin 6 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) *
            (((τ 3 i : ℤˣ) : ℝ) - ((τ 4 i : ℤˣ) : ℝ))) *
          ((M : ℝ)⁻¹ * ∑ j, (((τ 0 j : ℤˣ) : ℝ) - ((τ 2 j : ℤˣ) : ℝ)) *
            (((τ 3 j : ℤˣ) : ℝ) - ((τ 5 j : ℤˣ) : ℝ)))
        ∂(Measure.pi fun _ : Fin 6 => Measure.count.tilted A) := by
  have hL : ∀ τ : Fin 2 → Fin M → ℤˣ,
      ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 1 i : ℤˣ) : ℝ) - b i)) ^ 2 =
        ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j,
          ((((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 1 i : ℤˣ) : ℝ) - b i)) *
            ((((τ 0 j : ℤˣ) : ℝ) - b j) * (((τ 1 j : ℤˣ) : ℝ) - b j)) := fun τ => by
    rw [mul_pow, sq (∑ i, _), Finset.sum_mul_sum]
  have hR : ∀ τ : Fin 6 → Fin M → ℤˣ,
      ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) *
            (((τ 3 i : ℤˣ) : ℝ) - ((τ 4 i : ℤˣ) : ℝ))) *
          ((M : ℝ)⁻¹ * ∑ j, (((τ 0 j : ℤˣ) : ℝ) - ((τ 2 j : ℤˣ) : ℝ)) *
            (((τ 3 j : ℤˣ) : ℝ) - ((τ 5 j : ℤˣ) : ℝ))) =
        ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j,
          ((((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) * (((τ 0 j : ℤˣ) : ℝ) - ((τ 2 j : ℤˣ) : ℝ))) *
            ((((τ 3 i : ℤˣ) : ℝ) - ((τ 4 i : ℤˣ) : ℝ)) *
              (((τ 3 j : ℤˣ) : ℝ) - ((τ 5 j : ℤˣ) : ℝ))) := fun τ => by
    rw [mul_mul_mul_comm, ← sq, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ => Integrable.of_finite,
    integral_finsetSum _ fun i _ => Integrable.of_finite]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => Integrable.of_finite,
    integral_finsetSum _ fun j _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_dev_pair_sq A b hb i j, integral_six_replicas_cov_sq A b hb i j]

/-- **The Gibbs-mean trick, averaged over the disorder.**  For a family of energies `E η` with
Gibbs means `b η`, `ν(T_{12}²)` equals the six-replica average of Proposition 1.8.5's shape. -/
theorem integral_disorder_dev_dot_sq_eq_six_replicas {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P₀ : Measure Ω₀) (E : Ω₀ → (Fin M → ℤˣ) → ℝ) (b : Ω₀ → Fin M → ℝ)
    (hb : ∀ η i, b η i = ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) ∂(Measure.count.tilted (E η))) :
    ∫ η, ∫ τ : Fin 2 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b η i) * (((τ 1 i : ℤˣ) : ℝ) - b η i)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E η)) ∂P₀ =
      ∫ η, ∫ τ : Fin 6 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) *
            (((τ 3 i : ℤˣ) : ℝ) - ((τ 4 i : ℤˣ) : ℝ))) *
          ((M : ℝ)⁻¹ * ∑ j, (((τ 0 j : ℤˣ) : ℝ) - ((τ 2 j : ℤˣ) : ℝ)) *
            (((τ 3 j : ℤˣ) : ℝ) - ((τ 5 j : ℤˣ) : ℝ)))
        ∂(Measure.pi fun _ : Fin 6 => Measure.count.tilted (E η)) ∂P₀ :=
  integral_congr_ae (ae_of_all _ fun η => integral_dev_dot_sq_eq_six_replicas (E η) (b η) (hb η))

include hb in
/-- **`rect² = 4 T_{12}²` in the mean:** the Gibbs average of the squared rectangle
`((σ¹-σ²)·(σ³-σ⁴)/M)²` over four replicas is four times the Gibbs average of `T_{12}²`.  (The
cross terms `⟨T_{13}T_{14}⟩`, ... of the expansion `rect = T_{13} - T_{14} - T_{23} + T_{24}`
vanish by integrating over a replica occurring in one factor only; here this is read off from
`M⁻² ∑_{ij} C_ij²` on both sides.) -/
theorem integral_rect_sq_eq_four_mul_dev_dot_sq :
    ∫ τ : Fin 4 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) *
            (((τ 2 i : ℤˣ) : ℝ) - ((τ 3 i : ℤˣ) : ℝ))) ^ 2
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted A) =
      4 * ∫ τ : Fin 2 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 1 i : ℤˣ) : ℝ) - b i)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted A) := by
  have hL : ∀ τ : Fin 4 → Fin M → ℤˣ,
      ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) *
            (((τ 2 i : ℤˣ) : ℝ) - ((τ 3 i : ℤˣ) : ℝ))) ^ 2 =
        ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j,
          ((((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) * (((τ 0 j : ℤˣ) : ℝ) - ((τ 1 j : ℤˣ) : ℝ))) *
            ((((τ 2 i : ℤˣ) : ℝ) - ((τ 3 i : ℤˣ) : ℝ)) *
              (((τ 2 j : ℤˣ) : ℝ) - ((τ 3 j : ℤˣ) : ℝ))) := fun τ => by
    rw [mul_pow, sq (∑ i, _), Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hR : ∀ τ : Fin 2 → Fin M → ℤˣ,
      ((M : ℝ)⁻¹ * ∑ i, (((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 1 i : ℤˣ) : ℝ) - b i)) ^ 2 =
        ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j,
          ((((τ 0 i : ℤˣ) : ℝ) - b i) * (((τ 1 i : ℤˣ) : ℝ) - b i)) *
            ((((τ 0 j : ℤˣ) : ℝ) - b j) * (((τ 1 j : ℤˣ) : ℝ) - b j)) := fun τ => by
    rw [mul_pow, sq (∑ i, _), Finset.sum_mul_sum]
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ => Integrable.of_finite,
    integral_finsetSum _ fun i _ => Integrable.of_finite]
  rw [mul_left_comm]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => Integrable.of_finite,
    integral_finsetSum _ fun j _ => Integrable.of_finite, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_dev_pair_sq A b hb i j, integral_four_replicas_cov_sq A i j, ← hb i, ← hb j]

end SpinGlasses
