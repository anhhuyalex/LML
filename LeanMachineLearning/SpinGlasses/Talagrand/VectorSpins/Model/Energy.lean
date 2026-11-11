/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Geometry
public import
  LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKReplicaSymmetricBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityInterpolation

/-!
# The Gaussian pair Hamiltonian with vector spins

The model of Talagrand Section 1.12 uses one shared Gaussian coupling per site pair.
The component index is any finite type; spin coordinates are real, with no Ising restriction.
The diagonal correction in its covariance depends on the spin lengths and must be retained.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- The vector-spin SK energy `-H_N`, Eq. (1.360). This is the model Hamiltonian, used in
its coefficient representation, Gaussian moments and arbitrary-base-measure Gibbs bounds. -/
noncomputable def skVectorEnergy {D : Type*} [Fintype D] (N : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) (σ : Fin N → D → ℝ) : ℝ :=
  (Real.sqrt N)⁻¹ * β * ∑ p : FinPairs N, g p * ∑ u, σ p.val.1 u * σ p.val.2 u

/-- Eq. (1.361): components interact through the common couplings; the component sum can
be taken outside the site-pair sum. -/
theorem skVectorEnergy_eq_sum_components {D : Type*} [Fintype D] (N : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) (σ : Fin N → D → ℝ) :
    skVectorEnergy N β g σ =
      (Real.sqrt N)⁻¹ * β * ∑ u, ∑ p : FinPairs N, g p * σ p.val.1 u * σ p.val.2 u := by
  simp only [skVectorEnergy, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro p _
  ring

/-- The one-component model is the real-spin scalar pair Hamiltonian. Restricting the
scalar spin law to `+1,-1` recovers the Ising interaction without changing the formula. -/
theorem skVectorEnergy_one_component (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ)
    (σ : Fin N → ℝ) :
    skVectorEnergy N β g (fun i (_ : Fin 1) => σ i) =
      (Real.sqrt N)⁻¹ * β * ∑ p : FinPairs N, g p * σ p.val.1 * σ p.val.2 := by
  simp only [skVectorEnergy, Fin.sum_univ_one]
  congr 1
  apply sum_congr rfl
  intro p _
  ring

/-- The interaction part of Eq. (1.375). This reuses the scalar finite-pair splitting
identity for arbitrary real coordinates, with the full-system normalization retained. -/
theorem skVectorEnergy_succ_cavity {D : Type*} [Fintype D] (N : ℕ) (β : ℝ)
    (g : FinPairs (N + 1) → ℝ) (σ : Fin (N + 1) → D → ℝ) :
    skVectorEnergy (N + 1) β g σ = (Real.sqrt (N + 1))⁻¹ * β *
      ((∑ u, ∑ p : FinPairs N,
          g ⟨(p.val.1.castSucc, p.val.2.castSucc),
            Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ *
          σ p.val.1.castSucc u * σ p.val.2.castSucc u) +
        ∑ u, σ (Fin.last N) u * ∑ i : Fin N,
          g ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩ * σ i.castSucc u) := by
  rw [skVectorEnergy_eq_sum_components]
  have hs (u : D) := sum_finPairs_succ_cavity N g (fun i => σ i u)
  simp_rw [hs]
  rw [sum_add_distrib]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Coefficient-vector representation, so the existing Gaussian linear-form API applies. -/
theorem skVectorEnergy_eq_dotProduct {D : Type*} [Fintype D] (N : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) (σ : Fin N → D → ℝ) :
    skVectorEnergy N β g σ =
      (fun p : FinPairs N => (Real.sqrt N)⁻¹ * β * ∑ u, σ p.val.1 u * σ p.val.2 u) ⬝ᵥ g := by
  simp only [skVectorEnergy, dotProduct, mul_sum, sum_mul]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro u _
  ring

/-- The Gaussian vector-spin Hamiltonian is centered, for every configuration. -/
theorem integral_skVectorEnergy_eq_zero {D : Type*} [Fintype D] (N : ℕ) (β : ℝ)
    (σ : Fin N → D → ℝ) :
    (∫ g : FinPairs N → ℝ, skVectorEnergy N β g σ
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = 0 := by
  simp_rw [skVectorEnergy_eq_dotProduct]
  exact integral_dotProduct_pi_gaussianReal _

/-- The unnormalized covariance identity, with its configuration-dependent site diagonal.
This finite algebra has no boundedness, temperature or probability hypotheses. -/
theorem sum_sk_vector_pair_coeff_mul {D : Type*} [Fintype D] (N : ℕ)
    (σ τ : Fin N → D → ℝ) :
    (∑ p : FinPairs N, (∑ u, σ p.val.1 u * σ p.val.2 u) *
      ∑ v, τ p.val.1 v * τ p.val.2 v) =
      ((∑ u, ∑ v, (∑ i, σ i u * τ i v) ^ 2) -
        ∑ i, (∑ u, σ i u ^ 2) * ∑ v, τ i v ^ 2) / 2 := by
  have hdiag : (∑ u, ∑ v, ∑ i, (σ i u * τ i v) ^ 2) =
      ∑ i, (∑ u, σ i u ^ 2) * ∑ v, τ i v ^ 2 := by
    simp only [mul_pow, sum_mul_sum]
    calc
      _ = ∑ u, ∑ i, ∑ v, σ i u ^ 2 * τ i v ^ 2 := by
        apply sum_congr rfl
        intro u _
        rw [sum_comm]
      _ = _ := sum_comm
  calc
    _ = ∑ u, ∑ v, ∑ p : FinPairs N,
        (σ p.val.1 u * τ p.val.1 v) * (σ p.val.2 u * τ p.val.2 v) := by
      simp only [sum_mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro u _
      rw [sum_comm]
      apply sum_congr rfl
      intro v _
      apply sum_congr rfl
      intro p _
      ring
    _ = ((∑ u, ∑ v, (∑ i, σ i u * τ i v) ^ 2) -
        ∑ u, ∑ v, ∑ i, (σ i u * τ i v) ^ 2) / 2 := by
      have hp (u v : D) := sum_finPairs_mul_eq_sub_sum_sq_div_two N
        (fun i => σ i u * τ i v)
      simp_rw [hp]
      simp only [← Finset.sum_div, Finset.sum_sub_distrib]
    _ = _ := by rw [hdiag]

/-- Exact Gaussian covariance. The second term is a spin-length correction, not a constant
for a general vector-spin law. -/
theorem integral_skVectorEnergy_mul {D : Type*} [Fintype D] (N : ℕ)
    (β : ℝ) (σ τ : Fin N → D → ℝ) :
    (∫ g : FinPairs N → ℝ, skVectorEnergy N β g σ * skVectorEnergy N β g τ
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      β ^ 2 / (2 * N) * ((∑ u, ∑ v, (∑ i, σ i u * τ i v) ^ 2) -
        ∑ i, (∑ u, σ i u ^ 2) * ∑ v, τ i v ^ 2) := by
  simp_rw [skVectorEnergy_eq_dotProduct]
  rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
  have hs : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  have hp (p : FinPairs N) :
      ((Real.sqrt N)⁻¹ * β * ∑ u, σ p.val.1 u * σ p.val.2 u) *
        ((Real.sqrt N)⁻¹ * β * ∑ v, τ p.val.1 v * τ p.val.2 v) =
      ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) * β ^ 2 *
        ((∑ u, σ p.val.1 u * σ p.val.2 u) * ∑ v, τ p.val.1 v * τ p.val.2 v) := by ring
  simp only [dotProduct, hp, hs, ← mul_sum]
  rw [sum_sk_vector_pair_coeff_mul]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Bounded spins give a uniform energy bound, for each fixed disorder realization.
The squared radius `r` is independent of the number or labels of components. -/
theorem abs_skVectorEnergy_le {D : Type*} [Fintype D] (N : ℕ) (β : ℝ)
    (g : FinPairs N → ℝ) (σ : Fin N → D → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hσ : ∀ i, ∑ u, σ i u ^ 2 ≤ r) :
    |skVectorEnergy N β g σ| ≤ (Real.sqrt N)⁻¹ * |β| * r * ∑ p, |g p| := by
  have hpair (p : FinPairs N) : |∑ u, σ p.val.1 u * σ p.val.2 u| ≤ r := by
    have hcs := sum_mul_sq_le_sq_mul_sq univ (σ p.val.1) (σ p.val.2)
    have hb : (∑ u, σ p.val.1 u ^ 2) * (∑ u, σ p.val.2 u ^ 2) ≤ r ^ 2 := by
      simpa only [sq] using mul_le_mul (hσ p.val.1) (hσ p.val.2)
        (sum_nonneg fun _ _ => sq_nonneg _) hr
    exact (sq_le_sq₀ (abs_nonneg _) hr).mp
      (by simpa only [sq_abs] using hcs.trans hb)
  have hsum : |∑ p : FinPairs N, g p * ∑ u, σ p.val.1 u * σ p.val.2 u| ≤
      r * ∑ p, |g p| := by
    calc
      _ ≤ ∑ p : FinPairs N, |g p * ∑ u, σ p.val.1 u * σ p.val.2 u| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : FinPairs N, |g p| * r := by
        apply sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpair p) (abs_nonneg _)
      _ = _ := by rw [← sum_mul]; ring
  rw [skVectorEnergy, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ ≤ ((Real.sqrt N)⁻¹ * |β|) * (r * ∑ p, |g p|) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Partition-function integrability for an arbitrary finite spin law.
In particular the law may be continuous on the ball; no finite-support assumption is made. -/
theorem integrable_exp_skVectorEnergy {α D : Type*} [MeasurableSpace α] [Fintype D]
    (μ : Measure α) [IsFiniteMeasure μ] (ξ : α → D → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ) :
    Integrable (fun σ : Fin N → α => Real.exp (skVectorEnergy N β g (fun i => ξ (σ i))))
      (Measure.pi fun _ : Fin N => μ) := by
  have hm : Measurable (fun σ : Fin N → α => skVectorEnergy N β g (fun i => ξ (σ i))) := by
    unfold skVectorEnergy
    fun_prop
  apply integrable_exp_of_ae_le hm.aemeasurable
  exact ae_of_all _ fun σ => (le_abs_self _).trans
    (abs_skVectorEnergy_le N β g (fun i => ξ (σ i)) r hr (fun i => hbound (σ i)))

/-- Gibbs normalization for any probability law on bounded vector spins, using the
existing tilted-measure construction rather than a new model-specific Gibbs definition. -/
theorem isProbabilityMeasure_tilted_skVectorEnergy_of_sum_sq_le {α D : Type*} [MeasurableSpace α]
  [Fintype D]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → D → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ) :
    IsProbabilityMeasure ((Measure.pi fun _ : Fin N => μ).tilted
      (fun σ => skVectorEnergy N β g (fun i => ξ (σ i)))) :=
  isProbabilityMeasure_tilted (integrable_exp_skVectorEnergy μ ξ hξ r hr hbound N β g)

/-- The normalized partition function at zero interaction is one, not the number of
configurations: Section 1.12 uses a probability base law in Eq. (1.363). -/
theorem integral_exp_skVectorEnergy_zero_beta {α D : Type*}
    [MeasurableSpace α] [Fintype D] (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (N : ℕ) (g : FinPairs N → ℝ) :
    (∫ σ : Fin N → α, Real.exp (skVectorEnergy N 0 g (fun i => ξ (σ i)))
      ∂(Measure.pi fun _ : Fin N => μ)) = 1 := by
  simp [skVectorEnergy]

/-- A bounded vector-spin energy gives a finite logarithmic partition function with the
same bound. No finite-support assumption on the spin law is required. -/
theorem abs_log_integral_exp_skVectorEnergy_le {α D : Type*}
    [MeasurableSpace α] [Fintype D] (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (r : ℝ) (hr : 0 ≤ r) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r)
    (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ) :
    |Real.log (∫ σ : Fin N → α, Real.exp (skVectorEnergy N β g (fun i => ξ (σ i)))
      ∂(Measure.pi fun _ : Fin N => μ))| ≤
      (Real.sqrt N)⁻¹ * |β| * r * ∑ p, |g p| := by
  have hm : Measurable (fun σ : Fin N → α => skVectorEnergy N β g (fun i => ξ (σ i))) := by
    unfold skVectorEnergy
    fun_prop
  exact abs_log_integral_exp_le_of_ae_abs_le hm.aemeasurable (ae_of_all _ fun σ =>
    abs_skVectorEnergy_le N β g (fun i => ξ (σ i)) r hr (fun i => hbound (σ i)))

/-- Temperature differentiation of the vector-spin log-partition function at fixed disorder.
The arbitrary probability spin law may be continuous or singular; both signs of `β` are allowed. -/
theorem hasDerivAt_log_integral_exp_skVectorEnergy {α D : Type*}
    [MeasurableSpace α] [Fintype D] (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (r : ℝ) (hr : 0 ≤ r) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r)
    (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ) :
    HasDerivAt (fun b => Real.log (∫ σ : Fin N → α,
      Real.exp (skVectorEnergy N b g (fun i => ξ (σ i)))
        ∂(Measure.pi fun _ : Fin N => μ)))
      (∫ σ : Fin N → α, skVectorEnergy N 1 g (fun i => ξ (σ i))
        ∂((Measure.pi fun _ : Fin N => μ).tilted
          (fun σ => skVectorEnergy N β g (fun i => ξ (σ i))))) β := by
  have hm : Measurable (fun σ : Fin N → α => skVectorEnergy N 1 g (fun i => ξ (σ i))) := by
    unfold skVectorEnergy
    fun_prop
  have hscale (b : ℝ) (σ : Fin N → α) :
      b * skVectorEnergy N 1 g (fun i => ξ (σ i)) =
        skVectorEnergy N b g (fun i => ξ (σ i)) := by
    unfold skVectorEnergy
    ring
  simpa only [hscale] using hasDerivAt_log_integral_exp_mul_of_ae_abs_le
    hm.aemeasurable (ae_of_all _ fun σ =>
      abs_skVectorEnergy_le N 1 g (fun i => ξ (σ i)) r hr (fun i => hbound (σ i))) β

/-- The log-density of the decoupled last spin: the Gaussian field `Y` and the compensation
(Eq. (1.371)). -/
noncomputable def skVectorFieldExponent {α D : Type*} [Fintype D] (ξ : α → D → ℝ) (β : ℝ)
    (ρ q : D → D → ℝ) (y : D → ℝ) (a : α) : ℝ :=
  ∑ u, y u * ξ a u + β ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (ρ u v - q u v)

/-- Unfolding `skVectorFieldExponent` when the field is scaled by `β`. -/
theorem skVectorFieldExponent_mul_left {α D : Type*} [Fintype D] (ξ : α → D → ℝ) (β : ℝ)
    (ρ q : D → D → ℝ) (y : D → ℝ) (a : α) :
    skVectorFieldExponent ξ β ρ q (fun w => β * y w) a =
      β * ∑ w, y w * ξ a w +
        β ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q w w') := by
  unfold skVectorFieldExponent
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

end SpinGlasses
