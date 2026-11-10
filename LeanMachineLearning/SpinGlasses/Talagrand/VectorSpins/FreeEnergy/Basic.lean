/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Disorder
public import LeanMachineLearning.ForMathlib.Probability.GibbsTemperatureDerivative

/-!
# The free energy of the vector SK model and its temperature derivative

`p_N(β, μ) = N⁻¹ 𝔼 log ∫ exp (-H_N) dμ^{⊗N}` (Talagrand Eq. (1.360) and the definition of `p_N`).
Its
derivative in `β` is `(β/N) ∑_{i<j} 𝔼 (⟨s_{ij}²⟩ - ⟨s_{ij}⟩²) / N` with `s_{ij} = ∑ᵤ ξ(σᵢ)ᵤ ξ(σⱼ)ᵤ`
(first display in the proof of Theorem 1.12.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- The free energy `p_N(β, μ) = N⁻¹ 𝔼 log ∫ exp (-H_N(σ)) dμ^{⊗N}(σ)` of the vector SK model
with i.i.d. standard Gaussian couplings. -/
noncomputable def skVectorFreeEnergy {d : ℕ} (μ : Measure α) (ξ : α → Fin d → ℝ) (N : ℕ)
    (β : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∫ σ : Fin N → α,
    Real.exp (skVectorEnergy N β g (fun i => ξ (σ i))) ∂(Measure.pi fun _ : Fin N => μ))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)

/-- The normalized pair feature `X_{ij}(σ) = N^{-1/2} ∑ᵤ ξ(σᵢ)ᵤ ξ(σⱼ)ᵤ`. -/
noncomputable def skVectorPairFeature {d : ℕ} (ξ : α → Fin d → ℝ) (N : ℕ) (p : FinPairs N)
    (σ : Fin N → α) : ℝ :=
  (Real.sqrt N)⁻¹ * ∑ u, ξ (σ p.val.1) u * ξ (σ p.val.2) u

omit [MeasurableSpace α] in
theorem skVectorEnergy_eq_sum_features {d : ℕ} (ξ : α → Fin d → ℝ) (N : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) (σ : Fin N → α) :
    skVectorEnergy N β g (fun i => ξ (σ i)) =
      ∑ p, g p * (β * skVectorPairFeature ξ N p σ) := by
  unfold skVectorEnergy skVectorPairFeature
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **The temperature derivative of the free energy** (proof of Theorem 1.12.3).  The derivative of
`β ↦ 𝔼 log ∫ exp (-H_N) dμ^{⊗N}` is `β ∑_p 𝔼 (⟨X_p²⟩ - ⟨X_p⟩²)` with `X_p` the normalized pair
features. -/
theorem hasDerivAt_skVectorLogPartition {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (N : ℕ) (β : ℝ) :
    HasDerivAt (fun b => ∫ g : FinPairs N → ℝ, Real.log (∫ σ : Fin N → α,
        Real.exp (skVectorEnergy N b g (fun i => ξ (σ i))) ∂(Measure.pi fun _ : Fin N => μ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
      (β * ∑ p : FinPairs N, ∫ g : FinPairs N → ℝ,
        ((∫ σ : Fin N → α, skVectorPairFeature ξ N p σ ^ 2 *
              Real.exp (skVectorEnergy N β g (fun i => ξ (σ i))) ∂(Measure.pi fun _ : Fin N => μ)) /
            ∫ σ : Fin N → α, Real.exp (skVectorEnergy N β g (fun i => ξ (σ i)))
              ∂(Measure.pi fun _ : Fin N => μ) -
          ((∫ σ : Fin N → α, skVectorPairFeature ξ N p σ *
              Real.exp (skVectorEnergy N β g (fun i => ξ (σ i))) ∂(Measure.pi fun _ : Fin N => μ)) /
            ∫ σ : Fin N → α, Real.exp (skVectorEnergy N β g (fun i => ξ (σ i)))
              ∂(Measure.pi fun _ : Fin N => μ)) ^ 2)
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) β := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hXm : ∀ p : FinPairs N, Measurable (skVectorPairFeature ξ N p) := fun p => by
    unfold skVectorPairFeature
    exact measurable_const.mul (Finset.measurable_sum _ fun u _ =>
      ((hξ u).comp (measurable_pi_apply _)).mul ((hξ u).comp (measurable_pi_apply _)))
  have hXb : ∀ (p : FinPairs N) (σ : Fin N → α), |skVectorPairFeature ξ N p σ| ≤
      (Real.sqrt N)⁻¹ * (d * (Real.sqrt d * Real.sqrt d)) := fun p σ => by
    unfold skVectorPairFeature
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u, |ξ (σ p.val.1) u * ξ (σ p.val.2) u| ≤ ∑ _u : Fin d, Real.sqrt d * Real.sqrt d :=
          Finset.sum_le_sum fun u _ => by
            rw [abs_mul]
            exact mul_le_mul (hxb _ _) (hxb _ _) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = d * (Real.sqrt d * Real.sqrt d) := by simp
  have hg1 : IsGaussian (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    isGaussian_pi_gaussianReal
  have hlaw : HasGaussianLaw (fun (g : FinPairs N → ℝ) (p : FinPairs N) => g p)
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := IsGaussian.hasGaussianLaw_id
  have := hasDerivAt_integral_log_partition_temperature (μ := Measure.pi fun _ : Fin N => μ)
    (X := skVectorPairFeature ξ N) (B := (Real.sqrt N)⁻¹ * (d * (Real.sqrt d * Real.sqrt d)))
    (P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1) (g := fun p g => g p) hXm
    (by positivity) hXb hlaw (fun p => measurable_pi_apply p)
    (fun p => integral_pi_gaussianReal_coord p) (fun i l => integral_pi_gaussianReal_coord_mul i l)
        β
  simp only [skVectorEnergy_eq_sum_features]
  exact this

omit [MeasurableSpace α] in
/-- **Pair features and overlaps.**  The sum over pairs `i < j` of the product of the normalized
pair
features of two configurations is half the sum of the squared overlaps minus the diagonal:
`∑_p X_p(σ) X_p(τ) = (2N)⁻¹ ∑ᵤᵥ ((∑ᵢ ξ(σᵢ)ᵤ ξ(τᵢ)ᵥ)² - ∑ᵢ (ξ(σᵢ)ᵤ ξ(τᵢ)ᵥ)²)`. -/
theorem sum_skVectorPairFeature_mul {d : ℕ} (ξ : α → Fin d → ℝ) (N : ℕ) (σ τ : Fin N → α) :
    ∑ p : FinPairs N, skVectorPairFeature ξ N p σ * skVectorPairFeature ξ N p τ =
      (2 * (N : ℝ))⁻¹ * ∑ u, ∑ v, ((∑ i, ξ (σ i) u * ξ (τ i) v) ^ 2 -
        ∑ i, (ξ (σ i) u * ξ (τ i) v) ^ 2) := by
  have hN : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  have h1 : ∀ p : FinPairs N, skVectorPairFeature ξ N p σ * skVectorPairFeature ξ N p τ =
      (N : ℝ)⁻¹ * ∑ u, ∑ v, (ξ (σ p.val.1) u * ξ (τ p.val.1) v) *
        (ξ (σ p.val.2) u * ξ (τ p.val.2) v) := fun p => by
    unfold skVectorPairFeature
    rw [show (Real.sqrt N)⁻¹ * (∑ u, ξ (σ p.val.1) u * ξ (σ p.val.2) u) *
        ((Real.sqrt N)⁻¹ * ∑ v, ξ (τ p.val.1) v * ξ (τ p.val.2) v) =
        ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) * ((∑ u, ξ (σ p.val.1) u * ξ (σ p.val.2) u) *
          ∑ v, ξ (τ p.val.1) v * ξ (τ p.val.2) v) by ring, hN, Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  simp_rw [h1]
  rw [← Finset.mul_sum]
  have hswap : ∑ p : FinPairs N, ∑ u, ∑ v, (ξ (σ p.val.1) u * ξ (τ p.val.1) v) *
        (ξ (σ p.val.2) u * ξ (τ p.val.2) v) =
      ∑ u, ∑ v, ∑ p : FinPairs N, (ξ (σ p.val.1) u * ξ (τ p.val.1) v) *
        (ξ (σ p.val.2) u * ξ (τ p.val.2) v) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
  rw [hswap]
  have hpair : ∀ u v, ∑ p : FinPairs N, (ξ (σ p.val.1) u * ξ (τ p.val.1) v) *
      (ξ (σ p.val.2) u * ξ (τ p.val.2) v) = ((∑ i, ξ (σ i) u * ξ (τ i) v) ^ 2 -
        ∑ i, (ξ (σ i) u * ξ (τ i) v) ^ 2) / 2 := fun u v =>
    sum_finPairs_mul_eq_sub_sum_sq_div_two N (fun i => ξ (σ i) u * ξ (τ i) v)
  simp only [hpair]
  rw [mul_inv]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  ring

/-- **Gibbs variance as a two-replica average.**  For a probability measure `ν` and a bounded
measurable feature `X`, `⟨X²⟩ - ⟨X⟩² = ∫ (X(σ¹)² - X(σ¹) X(σ²)) d(ν ⊗ ν)`. -/
theorem variance_eq_integral_pi_two {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [IsProbabilityMeasure ν] {X : β → ℝ} (hX : Measurable X) {B : ℝ} (hXb : ∀ a, |X a| ≤ B) :
    ∫ a, X a ^ 2 ∂ν - (∫ a, X a ∂ν) ^ 2 =
      ∫ σ : Fin 2 → β, (X (σ 0) ^ 2 - X (σ 0) * X (σ 1)) ∂(Measure.pi fun _ : Fin 2 => ν) := by
  have hi : Integrable X ν := integrable_of_measurable_bound hX hXb
  have hi2 : Integrable (fun a => X a ^ 2) ν :=
    integrable_of_measurable_bound (hX.pow_const 2) (M := B ^ 2) fun a => by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc X a ^ 2 = |X a| ^ 2 := (sq_abs _).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hXb a) 2
  have h0 : ∫ σ : Fin 2 → β, X (σ 0) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν) = ∫ a, X a ^ 2 ∂ν :=
    integral_pi_eval ν 0 (fun a => X a ^ 2) (hX.pow_const 2).aestronglyMeasurable
  have h1 : ∫ σ : Fin 2 → β, X (σ 0) * X (σ 1) ∂(Measure.pi fun _ : Fin 2 => ν) =
      (∫ a, X a ∂ν) ^ 2 := by
    have := integral_fintype_prod_eq_prod (ι := Fin 2) (E := fun _ => β)
      (fun _ => X) (μ := fun _ => ν)
    simpa [Fin.prod_univ_two, sq] using this
  have hm0 : Measurable fun σ : Fin 2 → β => X (σ 0) ^ 2 :=
    (hX.comp (measurable_pi_apply 0)).pow_const 2
  have hm1 : Measurable fun σ : Fin 2 → β => X (σ 0) * X (σ 1) :=
    (hX.comp (measurable_pi_apply 0)).mul (hX.comp (measurable_pi_apply 1))
  rw [integral_sub (integrable_of_measurable_bound hm0 (M := B ^ 2) fun σ => by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc X (σ 0) ^ 2 = |X (σ 0)| ^ 2 := (sq_abs _).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hXb _) 2)
    (integrable_of_measurable_bound hm1 (M := B * B) fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hXb (σ 0)) (hXb (σ 1)) (abs_nonneg _) ((abs_nonneg _).trans (hXb (σ 0)))),
    h0, h1]

/-- The Gibbs-covariance sum over pairs, written through the squared overlaps of two replicas
(`∑_p (⟨X_p²⟩ - ⟨X_p⟩²) = ⟨(2M)⁻¹ ∑ᵤᵥ (S₀₀² - D₀₀ - S₀₁² + D₀₁)⟩`). -/
theorem sum_skVectorPairFeature_gibbsVariance_eq {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (N : ℕ) (β : ℝ) (g : FinPairs (N + 1) → ℝ) :
    ∑ p : FinPairs (N + 1),
      ((∫ σ : Fin (N + 1) → α, skVectorPairFeature ξ (N + 1) p σ ^ 2 *
            Real.exp (skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
              ∂(Measure.pi fun _ : Fin (N + 1) => μ)) /
          ∫ σ : Fin (N + 1) → α, Real.exp (skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
            ∂(Measure.pi fun _ : Fin (N + 1) => μ) -
        ((∫ σ : Fin (N + 1) → α, skVectorPairFeature ξ (N + 1) p σ *
            Real.exp (skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
              ∂(Measure.pi fun _ : Fin (N + 1) => μ)) /
          ∫ σ : Fin (N + 1) → α, Real.exp (skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
            ∂(Measure.pi fun _ : Fin (N + 1) => μ)) ^ 2) =
      ∫ σ : Fin 2 → Fin (N + 1) → α, (2 * ((N : ℝ) + 1))⁻¹ * ∑ u, ∑ v,
          (((∑ i, ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2 - ∑ i, (ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2) -
            ((∑ i, ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2 - ∑ i, (ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2))
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hXm : ∀ p : FinPairs (N + 1), Measurable (skVectorPairFeature ξ (N + 1) p) := fun p => by
    unfold skVectorPairFeature
    exact measurable_const.mul (Finset.measurable_sum _ fun u _ =>
      ((hξ u).comp (measurable_pi_apply _)).mul ((hξ u).comp (measurable_pi_apply _)))
  set B : ℝ := (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ * (d * (Real.sqrt d * Real.sqrt d)) with hB
  have hXb : ∀ (p : FinPairs (N + 1)) (σ : Fin (N + 1) → α),
      |skVectorPairFeature ξ (N + 1) p σ| ≤ B := fun p σ => by
    unfold skVectorPairFeature
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u, |ξ (σ p.val.1) u * ξ (σ p.val.2) u| ≤ ∑ _u : Fin d, Real.sqrt d * Real.sqrt d :=
          Finset.sum_le_sum fun u _ => by
            rw [abs_mul]
            exact mul_le_mul (hxb _ _) (hxb _ _) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = d * (Real.sqrt d * Real.sqrt d) := by simp
  set G := (Measure.pi fun _ : Fin (N + 1) => μ).tilted
    (fun σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i))) with hG
  have : IsProbabilityMeasure G :=
    isProbabilityMeasure_tilted_skVectorEnergy μ ξ hξ hr hbound N β g
  have hratio : ∀ Y : (Fin (N + 1) → α) → ℝ,
      (∫ σ, Y σ * Real.exp (skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
        ∂(Measure.pi fun _ : Fin (N + 1) => μ)) /
      ∫ σ, Real.exp (skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
        ∂(Measure.pi fun _ : Fin (N + 1) => μ) = ∫ σ, Y σ ∂G := fun Y =>
    (skVectorGibbs_eq_integral_tilted (μ := Measure.pi fun _ : Fin (N + 1) => μ)
      (fun σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i))) Y)
  simp only [hratio]
  have hvar := fun p => variance_eq_integral_pi_two G (hXm p) (hXb p)
  simp only [hvar]
  have hint0 : ∀ p : FinPairs (N + 1), Integrable (fun σ : Fin 2 → Fin (N + 1) → α =>
      skVectorPairFeature ξ (N + 1) p (σ 0) ^ 2 -
        skVectorPairFeature ξ (N + 1) p (σ 0) * skVectorPairFeature ξ (N + 1) p (σ 1))
      (Measure.pi fun _ : Fin 2 => G) := fun p =>
    integrable_of_measurable_bound
      (((hXm p).comp (measurable_pi_apply 0)).pow_const 2 |>.sub
        (((hXm p).comp (measurable_pi_apply 0)).mul ((hXm p).comp (measurable_pi_apply 1))))
      (M := B ^ 2 + B * B) fun σ => by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_of_nonneg (sq_nonneg _)]
          calc skVectorPairFeature ξ (N + 1) p (σ 0) ^ 2 =
              |skVectorPairFeature ξ (N + 1) p (σ 0)| ^ 2 := (sq_abs _).symm
            _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hXb p _) 2
        · rw [abs_mul]
          exact mul_le_mul (hXb p (σ 0)) (hXb p (σ 1)) (abs_nonneg _)
            ((abs_nonneg _).trans (hXb p (σ 0)))
  rw [← integral_finsetSum Finset.univ fun p _ => hint0 p]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only [Finset.sum_sub_distrib]
  have h0 := sum_skVectorPairFeature_mul ξ (N + 1) (σ 0) (σ 0)
  have h1 := sum_skVectorPairFeature_mul ξ (N + 1) (σ 0) (σ 1)
  simp only [sq, Nat.cast_add, Nat.cast_one] at h0 h1 ⊢
  rw [h0, h1, ← mul_sub]
  congr 1
  simp only [Finset.sum_sub_distrib]

/-- **`∂p_{N+1}/∂β` through the squared overlaps** (proof of Theorem 1.12.3, first display). -/
theorem hasDerivAt_skVectorFreeEnergy {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (N : ℕ) (β : ℝ) :
    HasDerivAt (skVectorFreeEnergy μ ξ (N + 1))
      (((N : ℝ) + 1)⁻¹ * (β * ∫ g : FinPairs (N + 1) → ℝ,
        ∫ σ : Fin 2 → Fin (N + 1) → α, (2 * ((N : ℝ) + 1))⁻¹ * ∑ u, ∑ v,
          (((∑ i, ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2 - ∑ i, (ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2) -
            ((∑ i, ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2 - ∑ i, (ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2))
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i))))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))) β := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hd := (hasDerivAt_skVectorLogPartition μ ξ hξ hbound (N + 1) β).const_mul
    (((N + 1 : ℕ) : ℝ)⁻¹)
  have hfun : skVectorFreeEnergy μ ξ (N + 1) = fun b => ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ g : FinPairs (N +
      1) → ℝ,
      Real.log (∫ σ : Fin (N + 1) → α, Real.exp (skVectorEnergy (N + 1) b g (fun i => ξ (σ i)))
        ∂(Measure.pi fun _ : Fin (N + 1) => μ)) ∂(Measure.pi fun _ : FinPairs (N + 1) =>
            gaussianReal 0 1) :=
    rfl
  rw [hfun]
  refine hd.congr_deriv ?_
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hXm : ∀ p : FinPairs (N + 1), Measurable (skVectorPairFeature ξ (N + 1) p) := fun p => by
    unfold skVectorPairFeature
    exact measurable_const.mul (Finset.measurable_sum _ fun u _ =>
      ((hξ u).comp (measurable_pi_apply _)).mul ((hξ u).comp (measurable_pi_apply _)))
  set B : ℝ := (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ * (d * (Real.sqrt d * Real.sqrt d)) with hB
  have hXb : ∀ (p : FinPairs (N + 1)) (σ : Fin (N + 1) → α),
      |skVectorPairFeature ξ (N + 1) p σ| ≤ B := fun p σ => by
    unfold skVectorPairFeature
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u, |ξ (σ p.val.1) u * ξ (σ p.val.2) u| ≤ ∑ _u : Fin d, Real.sqrt d * Real.sqrt d :=
          Finset.sum_le_sum fun u _ => by
            rw [abs_mul]
            exact mul_le_mul (hxb _ _) (hxb _ _) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = d * (Real.sqrt d * Real.sqrt d) := by simp
  have hB0 : 0 ≤ B := by positivity
  have hEm : Measurable fun q : (FinPairs (N + 1) → ℝ) × (Fin (N + 1) → α) =>
      skVectorEnergy (N + 1) β q.1 (fun i => ξ (q.2 i)) := measurable_skVectorEnergy_joint ξ hξ β
  have hexp : ∀ g : FinPairs (N + 1) → ℝ, Integrable (fun σ : Fin (N + 1) → α =>
      Real.exp (skVectorEnergy (N + 1) β g (fun i => ξ (σ i))))
      (Measure.pi fun _ : Fin (N + 1) => μ) := fun g =>
    integrable_exp_of_abs_le (b := ∑ p, |g p| * (|β| * B))
      (hEm.comp (measurable_const.prodMk measurable_id)) fun σ => by
        rw [skVectorEnergy_eq_sum_features]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hXb p σ) (abs_nonneg _))
          (abs_nonneg _)
  set Tp : FinPairs (N + 1) → (FinPairs (N + 1) → ℝ) → ℝ := fun p g =>
    skVectorGibbs (Measure.pi fun _ : Fin (N + 1) => μ)
        (fun σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
        (fun σ => skVectorPairFeature ξ (N + 1) p σ ^ 2) -
      skVectorGibbs (Measure.pi fun _ : Fin (N + 1) => μ)
        (fun σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i)))
        (fun σ => skVectorPairFeature ξ (N + 1) p σ) ^ 2 with hTp
  have hTm : ∀ p, Measurable (Tp p) := fun p =>
    (measurable_skVectorGibbs (μ := Measure.pi fun _ : Fin (N + 1) => μ)
      (e := fun g σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i))) hEm
      ((hXm p).pow_const 2)).sub
    ((measurable_skVectorGibbs (μ := Measure.pi fun _ : Fin (N + 1) => μ)
      (e := fun g σ => skVectorEnergy (N + 1) β g (fun i => ξ (σ i))) hEm (hXm p)).pow_const 2)
  have hTb : ∀ p g, |Tp p g| ≤ B ^ 2 + B ^ 2 := fun p g => by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · exact abs_skVectorGibbs_le (hexp g) fun σ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        calc skVectorPairFeature ξ (N + 1) p σ ^ 2 = |skVectorPairFeature ξ (N + 1) p σ| ^ 2 :=
              (sq_abs _).symm
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hXb p σ) 2
    · rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_skVectorGibbs_le (hexp g) (hXb p)) 2
  have hTi : ∀ p, Integrable (Tp p) (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    fun p => integrable_of_measurable_bound (hTm p) (hTb p)
  have hsum : ∑ p : FinPairs (N + 1), ∫ g, Tp p g ∂(Measure.pi fun _ : FinPairs (N + 1) =>
      gaussianReal 0 1) = ∫ g : FinPairs (N + 1) → ℝ, ∑ p, Tp p g
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    (integral_finsetSum Finset.univ fun p _ => hTi p).symm
  push_cast
  congr 2
  exact (Finset.sum_congr rfl fun p _ => rfl).trans (hsum.trans
    (integral_congr_ae (Filter.Eventually.of_forall fun g =>
      sum_skVectorPairFeature_gibbsVariance_eq μ ξ hξ hbound N β g)))

end SpinGlasses
