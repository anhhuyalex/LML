/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeanTrick
public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal

/-!
# The overlap covariances in the `T`-basis (Talagrand, Eq. (1.246) and Theorem 1.8.12)

For the Gibbs measure `μ = count.tilted A` on `Fin M → ℤˣ` with moments `m_ij = ⟨σ_iσ_j⟩`, means
`b_i = ⟨σ_i⟩`, covariance `C_ij = m_ij - b_ib_j` and a number `q`, the three overlap covariances
of independent replicas are exactly

* `U = ⟨(R_{12} - q)²⟩ = a + 2 B + c`,
* `V = ⟨(R_{12} - q)(R_{13} - q)⟩ = B + c`,
* `W = ⟨(R_{12} - q)(R_{34} - q)⟩ = c`,

where `a = M⁻² ∑_{ij} C_ij²` (this is `⟨T_{12}²⟩`), `B = M⁻² ∑_{ij} C_ij b_ib_j` (`⟨T_1²⟩`) and
`c = (M⁻¹ ∑_i b_i² - q)²` (`T²`).  These are the Gibbs-level forms of the cross-term
cancellations of Propositions 1.8.8 and 1.8.10 and of the decomposition (1.246); they reduce
Theorem 1.8.12 to the three asymptotic values of `a`, `B` and `c` (Propositions 1.8.7, 1.8.10,
1.8.11).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.8.12.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

namespace SpinGlasses

/-- Independent replicas: the average of a product `f₀(σ¹) f₁(σ²)` factorizes. -/
theorem integral_pi_fin_two_mul_fun {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f₀ f₁ : α → ℝ) :
    ∫ τ : Fin 2 → α, f₀ (τ 0) * f₁ (τ 1) ∂(Measure.pi fun _ : Fin 2 => μ) =
      (∫ x, f₀ x ∂μ) * ∫ x, f₁ x ∂μ := by
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 => μ) (fun r : Fin 2 => ![f₀, f₁] r)
  simpa [Fin.prod_univ_two] using this

/-- Independent replicas: the average of a product `f₀(σ¹) f₁(σ²) f₂(σ³)` factorizes. -/
theorem integral_pi_fin_three_mul_fun {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f₀ f₁ f₂ : α → ℝ) :
    ∫ τ : Fin 3 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) ∂(Measure.pi fun _ : Fin 3 => μ) =
      (∫ x, f₀ x ∂μ) * (∫ x, f₁ x ∂μ) * ∫ x, f₂ x ∂μ := by
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin 3 => μ)
    (fun r : Fin 3 => ![f₀, f₁, f₂] r)
  simpa [Fin.prod_univ_three] using this

/-- Independent replicas: the average of a product of four functions of four replicas
factorizes. -/
theorem integral_pi_fin_four_mul_fun {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f₀ f₁ f₂ f₃ : α → ℝ) :
    ∫ τ : Fin 4 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) * f₃ (τ 3)
        ∂(Measure.pi fun _ : Fin 4 => μ) =
      (∫ x, f₀ x ∂μ) * (∫ x, f₁ x ∂μ) * (∫ x, f₂ x ∂μ) * ∫ x, f₃ x ∂μ := by
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin 4 => μ)
    (fun r : Fin 4 => ![f₀, f₁, f₂, f₃] r)
  simpa [Fin.prod_univ_four] using this

/-- Expansion of a product of two centered overlaps. -/
theorem overlap_prod_expand {M : ℕ} (q : ℝ) (u v : Fin M → ℝ) :
    ((M : ℝ)⁻¹ * ∑ i, u i - q) * ((M : ℝ)⁻¹ * ∑ j, v j - q) =
      ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, u i * v j - q * (M : ℝ)⁻¹ * ∑ i, u i -
        q * (M : ℝ)⁻¹ * ∑ j, v j + q ^ 2 := by
  rw [← Finset.sum_mul_sum]
  ring

/-- The average of a product of two centered overlaps over a finite probability space. -/
theorem integral_overlap_prod {M : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ)
    (u v : Fin M → Ω → ℝ) :
    ∫ ω, ((M : ℝ)⁻¹ * ∑ i, u i ω - q) * ((M : ℝ)⁻¹ * ∑ j, v j ω - q) ∂P =
      ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, ∫ ω, u i ω * v j ω ∂P -
        q * (M : ℝ)⁻¹ * ∑ i, ∫ ω, u i ω ∂P - q * (M : ℝ)⁻¹ * ∑ j, ∫ ω, v j ω ∂P + q ^ 2 := by
  simp_rw [overlap_prod_expand]
  have hA : ∫ ω, ∑ i, ∑ j, u i ω * v j ω ∂P = ∑ i, ∑ j, ∫ ω, u i ω * v j ω ∂P := by
    rw [integral_finsetSum _ fun i _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_finsetSum _ fun j _ => Integrable.of_finite
  have hB : ∀ w : Fin M → Ω → ℝ, ∫ ω, ∑ i, w i ω ∂P = ∑ i, ∫ ω, w i ω ∂P := fun w =>
    integral_finsetSum _ fun i _ => Integrable.of_finite
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const_mul, integral_const_mul, hA, hB u, hB v]
  simp only [integral_const, probReal_univ, one_smul]

/-- `(∑ b_i²)² = ∑_{ij} b_i² b_j²`, in the form used for the overlap covariances. -/
theorem sq_sum_sq_eq {M : ℕ} (b : Fin M → ℝ) :
    (∑ i, b i * b i) * (∑ j, b j * b j) = ∑ i, ∑ j, b i * b i * (b j * b j) :=
  Finset.sum_mul_sum _ _ _ _

section Covariances

variable {M : ℕ} (A : (Fin M → ℤˣ) → ℝ) (q : ℝ) (b : Fin M → ℝ)
  (hb : ∀ i, b i = ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) ∂(Measure.count.tilted A))
  (m : Fin M → Fin M → ℝ)
  (hm : ∀ i j, m i j = ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ)
    ∂(Measure.count.tilted A))

include hb hm in
/-- **`U = a + 2 B + c`:** `⟨(R_{12} - q)²⟩ = M⁻² ∑ C_ij² + 2 M⁻² ∑ C_ij b_ib_j + (M⁻¹ ∑ b_i² - q)²`
where `C_ij = m_ij - b_ib_j`. -/
theorem integral_overlap_sq_eq :
    ∫ τ : Fin 2 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted A) =
      ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m i j - b i * b j) ^ 2 +
        2 * (((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m i j - b i * b j) * (b i * b j)) +
        ((M : ℝ)⁻¹ * ∑ i, b i * b i - q) ^ 2 := by
  have h2 := integral_overlap_prod (M := M) (Measure.pi fun _ : Fin 2 => Measure.count.tilted A) q
    (fun i τ => ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ))
    (fun i τ => ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ))
  simp_rw [sq]
  rw [h2]
  have e1 : ∀ i j, ∫ τ : Fin 2 → Fin M → ℤˣ,
      ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ) * (((τ 0 j : ℤˣ) : ℝ) * ((τ 1 j : ℤˣ) : ℝ))
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted A) = m i j * m i j := fun i j => by
    have := integral_pi_fin_two_mul_fun (Measure.count.tilted A)
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ))
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ))
    rw [← hm i j] at this
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    ring
  have e2 : ∀ i, ∫ τ : Fin 2 → Fin M → ℤˣ, ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted A) = b i * b i := fun i => by
    have := integral_pi_fin_two_mul_fun (Measure.count.tilted A)
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ)) (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ))
    rw [← hb i] at this
    exact this
  simp only [e1, e2]
  have hsq := sq_sum_sq_eq b
  have hsplit : ∑ i, ∑ j, m i j * m i j = ∑ i, ∑ j, (m i j - b i * b j) * (m i j - b i * b j) +
      2 * ∑ i, ∑ j, (m i j - b i * b j) * (b i * b j) + ∑ i, ∑ j, b i * b i * (b j * b j) := by
    have : ∀ i j, m i j * m i j = (m i j - b i * b j) * (m i j - b i * b j) +
        2 * ((m i j - b i * b j) * (b i * b j)) + b i * b i * (b j * b j) := fun i j => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit, ← hsq]
  ring

include hb hm in
/-- **`V = B + c`:** `⟨(R_{12} - q)(R_{13} - q)⟩ = M⁻² ∑ C_ij b_ib_j + (M⁻¹ ∑ b_i² - q)²`. -/
theorem integral_overlap_mul_overlap_eq :
    ∫ τ : Fin 3 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ) - q) *
          ((M : ℝ)⁻¹ * ∑ j, ((τ 0 j : ℤˣ) : ℝ) * ((τ 2 j : ℤˣ) : ℝ) - q)
        ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted A) =
      ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m i j - b i * b j) * (b i * b j) +
        ((M : ℝ)⁻¹ * ∑ i, b i * b i - q) ^ 2 := by
  set μ : Measure (Fin M → ℤˣ) := Measure.count.tilted A with hμ
  have h2 := integral_overlap_prod (M := M) (Measure.pi fun _ : Fin 3 => μ) q
    (fun i τ => ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ))
    (fun i τ => ((τ 0 i : ℤˣ) : ℝ) * ((τ 2 i : ℤˣ) : ℝ))
  rw [h2]
  have hone : ∫ y : Fin M → ℤˣ, (1 : ℝ) ∂μ = 1 := by simp [hμ]
  have e1 : ∀ i j, ∫ τ : Fin 3 → Fin M → ℤˣ,
      ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ) * (((τ 0 j : ℤˣ) : ℝ) * ((τ 2 j : ℤˣ) : ℝ))
      ∂(Measure.pi fun _ : Fin 3 => μ) = m i j * b i * b j := fun i j => by
    have := integral_pi_fin_three_mul_fun μ
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ))
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ)) (fun y : Fin M → ℤˣ => ((y j : ℤˣ) : ℝ))
    rw [← hm i j, ← hb i, ← hb j] at this
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    ring
  have e2 : ∀ i, ∫ τ : Fin 3 → Fin M → ℤˣ, ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin 3 => μ) = b i * b i := fun i => by
    have := integral_pi_fin_three_mul_fun μ (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ))
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ)) (fun _ => 1)
    rw [← hb i, hone] at this
    simpa using this
  have e3 : ∀ j, ∫ τ : Fin 3 → Fin M → ℤˣ, ((τ 0 j : ℤˣ) : ℝ) * ((τ 2 j : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin 3 => μ) = b j * b j := fun j => by
    have := integral_pi_fin_three_mul_fun μ (fun y : Fin M → ℤˣ => ((y j : ℤˣ) : ℝ))
      (fun _ => 1) (fun y : Fin M → ℤˣ => ((y j : ℤˣ) : ℝ))
    rw [← hb j, hone] at this
    simpa using this
  simp only [e1, e2, e3]
  have hsq := sq_sum_sq_eq b
  have hsplit : ∑ i, ∑ j, m i j * b i * b j = ∑ i, ∑ j, (m i j - b i * b j) * (b i * b j) +
      ∑ i, ∑ j, b i * b i * (b j * b j) := by
    have : ∀ i j, m i j * b i * b j = (m i j - b i * b j) * (b i * b j) +
        b i * b i * (b j * b j) := fun i j => by ring
    simp only [this, Finset.sum_add_distrib]
  rw [hsplit, ← hsq]
  ring

include hb in
/-- **`W = c`:** `⟨(R_{12} - q)(R_{34} - q)⟩ = (M⁻¹ ∑ b_i² - q)²`. -/
theorem integral_overlap_mul_overlap_disjoint_eq :
    ∫ τ : Fin 4 → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ) - q) *
          ((M : ℝ)⁻¹ * ∑ j, ((τ 2 j : ℤˣ) : ℝ) * ((τ 3 j : ℤˣ) : ℝ) - q)
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted A) =
      ((M : ℝ)⁻¹ * ∑ i, b i * b i - q) ^ 2 := by
  set μ : Measure (Fin M → ℤˣ) := Measure.count.tilted A with hμ
  have h2 := integral_overlap_prod (M := M) (Measure.pi fun _ : Fin 4 => μ) q
    (fun i τ => ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ))
    (fun i τ => ((τ 2 i : ℤˣ) : ℝ) * ((τ 3 i : ℤˣ) : ℝ))
  rw [h2]
  have hone : ∫ y : Fin M → ℤˣ, (1 : ℝ) ∂μ = 1 := by simp [hμ]
  have e1 : ∀ i j, ∫ τ : Fin 4 → Fin M → ℤˣ,
      ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ) * (((τ 2 j : ℤˣ) : ℝ) * ((τ 3 j : ℤˣ) : ℝ))
      ∂(Measure.pi fun _ : Fin 4 => μ) = b i * b i * (b j * b j) := fun i j => by
    have := integral_pi_fin_four_mul_fun μ (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ))
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ)) (fun y : Fin M → ℤˣ => ((y j : ℤˣ) : ℝ))
      (fun y : Fin M → ℤˣ => ((y j : ℤˣ) : ℝ))
    rw [← hb i, ← hb j] at this
    rw [show b i * b i * (b j * b j) = b i * b i * b j * b j by ring, ← this]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    ring
  have e2 : ∀ i, ∫ τ : Fin 4 → Fin M → ℤˣ, ((τ 0 i : ℤˣ) : ℝ) * ((τ 1 i : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin 4 => μ) = b i * b i := fun i => by
    have := integral_pi_fin_four_mul_fun μ (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ))
      (fun y : Fin M → ℤˣ => ((y i : ℤˣ) : ℝ)) (fun _ => 1) (fun _ => 1)
    rw [← hb i, hone] at this
    simpa using this
  have e3 : ∀ j, ∫ τ : Fin 4 → Fin M → ℤˣ, ((τ 2 j : ℤˣ) : ℝ) * ((τ 3 j : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin 4 => μ) = b j * b j := fun j => by
    have := integral_pi_fin_four_mul_fun μ (fun _ => 1) (fun _ => 1)
      (fun y : Fin M → ℤˣ => ((y j : ℤˣ) : ℝ)) (fun y : Fin M → ℤˣ => ((y j : ℤˣ) : ℝ))
    rw [← hb j, hone] at this
    simpa using this
  simp only [e1, e2, e3]
  have hsq := sq_sum_sq_eq b
  rw [← hsq]
  ring

include hb hm in
/-- **Overlaps of one pair of distinct replicas among any finite set of replicas:**
`⟨(R_{ab} - q)²⟩ = a + 2B + c` (`integral_overlap_sq_eq` for the replicas `a ≠ b` of `R`). -/
theorem integral_overlap_sq_eq_of_ne {R : Type*} [Fintype R] {x y : R} (hxy : x ≠ y) :
    ∫ τ : R → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, ((τ x i : ℤˣ) : ℝ) * ((τ y i : ℤˣ) : ℝ) - q) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted A) =
      ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m i j - b i * b j) ^ 2 +
        2 * (((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m i j - b i * b j) * (b i * b j)) +
        ((M : ℝ)⁻¹ * ∑ i, b i * b i - q) ^ 2 := by
  have hρ : Function.Injective (![x, y] : Fin 2 → R) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Ne.symm hxy]
  have := integral_pi_count_tilted_comp_injective hρ A
    (fun σ : Fin 2 → Fin M → ℤˣ =>
      ((M : ℝ)⁻¹ * ∑ i, ((σ 0 i : ℤˣ) : ℝ) * ((σ 1 i : ℤˣ) : ℝ) - q) ^ 2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [this]
  exact integral_overlap_sq_eq A q b hb m hm

include hb hm in
/-- **Two overlaps sharing one replica, among any finite set of replicas:**
`⟨(R_{st} - q)(R_{st'} - q)⟩ = B + c`. -/
theorem integral_overlap_mul_overlap_eq_of_ne {R : Type*} [Fintype R] {s t t' : R}
    (hst : s ≠ t) (hst' : s ≠ t') (htt' : t ≠ t') :
    ∫ τ : R → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, ((τ s i : ℤˣ) : ℝ) * ((τ t i : ℤˣ) : ℝ) - q) *
          ((M : ℝ)⁻¹ * ∑ j, ((τ s j : ℤˣ) : ℝ) * ((τ t' j : ℤˣ) : ℝ) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted A) =
      ((M : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, (m i j - b i * b j) * (b i * b j) +
        ((M : ℝ)⁻¹ * ∑ i, b i * b i - q) ^ 2 := by
  have hρ : Function.Injective (![s, t, t'] : Fin 3 → R) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Ne.symm hst, Ne.symm hst', Ne.symm htt']
  have := integral_pi_count_tilted_comp_injective hρ A
    (fun σ : Fin 3 → Fin M → ℤˣ =>
      ((M : ℝ)⁻¹ * ∑ i, ((σ 0 i : ℤˣ) : ℝ) * ((σ 1 i : ℤˣ) : ℝ) - q) *
        ((M : ℝ)⁻¹ * ∑ j, ((σ 0 j : ℤˣ) : ℝ) * ((σ 2 j : ℤˣ) : ℝ) - q))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at this
  rw [this]
  exact integral_overlap_mul_overlap_eq A q b hb m hm

include hb in
/-- **Two overlaps of disjoint pairs of replicas among any finite set of replicas:**
`⟨(R_{ab} - q)(R_{a'b'} - q)⟩ = c`. -/
theorem integral_overlap_mul_overlap_disjoint_eq_of_ne {R : Type*} [Fintype R] {x y x' y' : R}
    (hxy : x ≠ y) (hxx' : x ≠ x') (hxy' : x ≠ y') (hyx' : y ≠ x') (hyy' : y ≠ y')
    (hx'y' : x' ≠ y') :
    ∫ τ : R → Fin M → ℤˣ,
        ((M : ℝ)⁻¹ * ∑ i, ((τ x i : ℤˣ) : ℝ) * ((τ y i : ℤˣ) : ℝ) - q) *
          ((M : ℝ)⁻¹ * ∑ j, ((τ x' j : ℤˣ) : ℝ) * ((τ y' j : ℤˣ) : ℝ) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted A) =
      ((M : ℝ)⁻¹ * ∑ i, b i * b i - q) ^ 2 := by
  have hρ : Function.Injective (![x, y, x', y'] : Fin 4 → R) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp_all [Ne.symm hxy, Ne.symm hxx', Ne.symm hxy', Ne.symm hyx', Ne.symm hyy',
        Ne.symm hx'y']
  have := integral_pi_count_tilted_comp_injective hρ A
    (fun σ : Fin 4 → Fin M → ℤˣ =>
      ((M : ℝ)⁻¹ * ∑ i, ((σ 0 i : ℤˣ) : ℝ) * ((σ 1 i : ℤˣ) : ℝ) - q) *
        ((M : ℝ)⁻¹ * ∑ j, ((σ 2 j : ℤˣ) : ℝ) * ((σ 3 j : ℤˣ) : ℝ) - q))
  have h3 : (![x, y, x', y'] : Fin 4 → R) 3 = y' := rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, h3] at this
  rw [this]
  exact integral_overlap_mul_overlap_disjoint_eq A q b hb

end Covariances

end SpinGlasses
