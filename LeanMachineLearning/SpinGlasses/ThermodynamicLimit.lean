/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.DiscreteLyapunov
public import LeanMachineLearning.ForMathlib.Topology.UniformSpace.LimitInterchange
public import LeanMachineLearning.SpinGlasses.FreeEnergy
public import Mathlib.Topology.Order.OrderClosed

/-!
# Monotonicity in the temperature and the zero-temperature limit

For a random energy `H` on the hypercube with partition function `Z(β) = ∑_σ exp (β H(σ))` and free
energy `F_N(β) = N⁻¹ 𝔼 log Z(β)` ([Panchenko, 2013, §1.1]):

* **Lyapunov monotonicity.**  `β ↦ β⁻¹ (F_N(β) - log 2)` is non-decreasing on `(0, ∞)`.  With the
  uniform probability measure `μ₀` on the configurations, `β⁻¹ (log Z(β) - N log 2)` is
  `log ‖exp H‖_{L^β(μ₀)}`, which increases with the exponent `β` (the power-mean inequality).
* **Thermodynamic limit.**  If `F_N(β) → F(β)` for every `β > 0`, the monotonicity passes to the
  limit, `β ↦ β⁻¹ (F(β) - log 2)` is non-decreasing, because a pointwise limit of monotone functions
  is monotone.
* **Zero-temperature limit** ([Panchenko, 2013, Eq. (1.10)]).  If `F_N(β) → F(β)` for every
  `β > 0`, then `N⁻¹ 𝔼 max_σ H(σ)` converges, and `β⁻¹ F(β)` converges to the same limit as
  `β → ∞`.  The ground-state energy is not assumed to converge: the estimate
  `|(N β)⁻¹ 𝔼 log Z(β) - N⁻¹ 𝔼 max_σ H(σ)| ≤ log 2 / β` of `FreeEnergy.lean` makes it a uniform
  limit, see `exists_tendsto_of_dist_le_of_tendsto`.

The existence of the limit `F_N(β) → F(β)` is the hypothesis `h_lim` of these results.  It is
discharged, for the SK model and for the mixed `p`-spin models with even `p` and `p = 1`, by the
Guerra–Toninelli superadditivity of `SpinGlasses/GuerraToninelli.lean`
(`SpinGlasses.sk_tendsto_free_energy`, `SpinGlasses.mixedPSpin_tendsto_free_energy`).

No definition is introduced.  The same layering as in `FreeEnergy.lean` is used: a deterministic
statement for `f : α → ℝ`, its integrated form for a random energy, the hypercube, and finally a
*family* of hypercube models (indexed by any type `κ` with a filter `l`, e.g. `κ = ℕ`,
`l = atTop`, `ι N = Fin N`), whose measurability and integrability hypotheses are discharged for the
SK model with Gaussian disorder.

## Main declarations

* `SpinGlasses.monotoneOn_inv_mul_log_sum_exp_sub_log_card`: the deterministic Lyapunov
  monotonicity, for any finite nonempty `α`.
* `SpinGlasses.monotoneOn_inv_mul_integral_log_sum_exp_sub_log_card`: its integrated form.
* `SpinGlasses.monotoneOn_inv_mul_free_energy_sub_log_two`: the hypercube form.
* `SpinGlasses.monotoneOn_inv_mul_limit_sub_log_two`,
  `SpinGlasses.exists_tendsto_ground_state_energy`: the thermodynamic and zero-temperature limits
  for a family of hypercube models.
* `SpinGlasses.sk_monotoneOn_inv_mul_limit_sub_log_two`,
  `SpinGlasses.sk_exists_tendsto_ground_state_energy`: the SK instances.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Matrix Topology

namespace SpinGlasses

section Deterministic

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **Lyapunov monotonicity of the log-partition function.** For any `f : α → ℝ` on a finite
nonempty type, `β ↦ β⁻¹ (log ∑ₐ exp (β f a) - log |α|)` is non-decreasing on `(0, ∞)`.  It is the
logarithm of the `L^β` norm of `exp f` for the uniform probability measure on `α`, and the claim
is the power-mean inequality `(∑ₐ |α|⁻¹ z a)^p ≤ ∑ₐ |α|⁻¹ (z a)^p` with `z = exp (β₁ f)` and
`p = β₂ / β₁ ≥ 1`. -/
theorem monotoneOn_inv_mul_log_sum_exp_sub_log_card (f : α → ℝ) :
    MonotoneOn (fun β => β⁻¹ * (Real.log (∑ a, Real.exp (β * f a)) -
      Real.log (Fintype.card α))) (Set.Ioi 0) := by
  simpa using monotoneOn_inv_mul_log_sum_mul_exp_sub_log_sum f (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (by simpa using Fintype.card_pos (α := α))

end Deterministic

section Random

variable {α : Type*} [Fintype α] [Nonempty α] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {H : Ω → α → ℝ}

/-- **Lyapunov monotonicity in expectation:** for a random energy with integrable coordinates,
`β ↦ β⁻¹ (𝔼 log ∑ₐ exp (β H a) - log |α|)` is non-decreasing on `(0, ∞)`. -/
theorem monotoneOn_inv_mul_integral_log_sum_exp_sub_log_card
    (hmeas : ∀ a, Measurable fun ω => H ω a) (hint : ∀ a, Integrable (fun ω => H ω a) μ) :
    MonotoneOn (fun β => β⁻¹ * (∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ -
      Real.log (Fintype.card α))) (Set.Ioi 0) := by
  have key : ∀ β : ℝ, 0 < β → β⁻¹ * (∫ ω, Real.log (∑ a, Real.exp (β * H ω a)) ∂μ -
      Real.log (Fintype.card α)) = ∫ ω, β⁻¹ * (Real.log (∑ a, Real.exp (β * H ω a)) -
        Real.log (Fintype.card α)) ∂μ := fun β hβ => by
    rw [integral_const_mul, integral_sub (integrable_log_sum_exp hβ hmeas hint)
      (integrable_const _), integral_const]
    simp
  intro β₁ (hβ₁ : 0 < β₁) β₂ (hβ₂ : 0 < β₂) hle
  change β₁⁻¹ * _ ≤ β₂⁻¹ * _
  rw [key β₁ hβ₁, key β₂ hβ₂]
  exact integral_mono
    (((integrable_log_sum_exp hβ₁ hmeas hint).sub (integrable_const _)).const_mul _)
    (((integrable_log_sum_exp hβ₂ hmeas hint).sub (integrable_const _)).const_mul _)
    fun ω => monotoneOn_inv_mul_log_sum_exp_sub_log_card (H ω) hβ₁ hβ₂ hle

end Random

section Hypercube

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {H : Ω → (ι → ℤˣ) → ℝ}

/-- **Monotonicity of the free energy in the temperature** ([Panchenko, 2013, §1.1]): for a
random energy on the hypercube with integrable coordinates, with `F_N(β) = N⁻¹ 𝔼 log Z(β)`,
`β ↦ β⁻¹ (F_N(β) - log 2)` is non-decreasing on `(0, ∞)`. -/
theorem monotoneOn_inv_mul_free_energy_sub_log_two (hmeas : ∀ σ, Measurable fun ω => H ω σ)
    (hint : ∀ σ, Integrable (fun ω => H ω σ) μ) :
    MonotoneOn (fun β => β⁻¹ * ((Fintype.card ι : ℝ)⁻¹ *
      ∫ ω, Real.log (∑ σ, Real.exp (β * H ω σ)) ∂μ - Real.log 2)) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · intro β₁ (hβ₁ : 0 < β₁) β₂ _ hle
    simp only [h0, Nat.cast_zero, inv_zero, zero_mul, zero_sub, mul_neg, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hβ₁ hle) (Real.log_pos one_lt_two).le
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hpos
  have key : ∀ β : ℝ, 0 < β → β⁻¹ * ((Fintype.card ι : ℝ)⁻¹ *
      ∫ ω, Real.log (∑ σ, Real.exp (β * H ω σ)) ∂μ - Real.log 2) = (Fintype.card ι : ℝ)⁻¹ *
        (β⁻¹ * (∫ ω, Real.log (∑ σ, Real.exp (β * H ω σ)) ∂μ -
          Real.log (Fintype.card (ι → ℤˣ)))) := fun β hβ => by
    rw [log_card_spin_configurations]
    field_simp
  intro β₁ hβ₁ β₂ hβ₂ hle
  change _ * _ ≤ _ * _
  rw [key β₁ hβ₁, key β₂ hβ₂]
  exact mul_le_mul_of_nonneg_left
    (monotoneOn_inv_mul_integral_log_sum_exp_sub_log_card hmeas hint hβ₁ hβ₂ hle)
    (inv_nonneg.2 hN.le)

end Hypercube

section Limit

variable {κ : Type*} {l : Filter κ} [l.NeBot] {ι : κ → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)] {Ω : κ → Type*} [∀ k, MeasurableSpace (Ω k)]
  {μ : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (μ k)] {H : ∀ k, Ω k → (ι k → ℤˣ) → ℝ}
  (hmeas : ∀ k σ, Measurable fun ω => H k ω σ)
  (hint : ∀ k σ, Integrable (fun ω => H k ω σ) (μ k))

include hmeas hint

/-- **Monotonicity survives the thermodynamic limit.** For a family of hypercube models `H k`
(e.g. `k = N → ∞` along `atTop`, `ι N = Fin N`), if the free energies
`F_k(β) = |ι k|⁻¹ 𝔼 log Z_k(β)` converge to `F(β)` for every `β > 0`, then
`β ↦ β⁻¹ (F(β) - log 2)` is non-decreasing on `(0, ∞)`. -/
theorem monotoneOn_inv_mul_limit_sub_log_two {F : ℝ → ℝ}
    (h_lim : ∀ β > 0, Tendsto (fun k => (Fintype.card (ι k) : ℝ)⁻¹ *
      ∫ ω, Real.log (∑ σ, Real.exp (β * H k ω σ)) ∂(μ k)) l (𝓝 (F β))) :
    MonotoneOn (fun β => β⁻¹ * (F β - Real.log 2)) (Set.Ioi 0) :=
  monotoneOn_of_frequently_monotoneOn_of_tendsto
    (F := fun k β => β⁻¹ * ((Fintype.card (ι k) : ℝ)⁻¹ *
      ∫ ω, Real.log (∑ σ, Real.exp (β * H k ω σ)) ∂(μ k) - Real.log 2))
    (Eventually.of_forall fun k =>
      monotoneOn_inv_mul_free_energy_sub_log_two (hmeas k) (hint k)).frequently
    fun β hβ => ((h_lim β hβ).sub_const _).const_mul _

/-- **The zero-temperature limit** ([Panchenko, 2013, Eq. (1.10)]). For a family of hypercube
models, if the free energies `F_k(β) = |ι k|⁻¹ 𝔼 log Z_k(β)` converge to `F(β)` for every
`β > 0`, then the ground-state energies `|ι k|⁻¹ 𝔼 max_σ H_k(σ)` converge to some `E₀`, and
`β⁻¹ F(β) → E₀` as `β → ∞`.  The convergence of the ground-state energies is not an assumption. -/
theorem exists_tendsto_ground_state_energy {F : ℝ → ℝ}
    (h_lim : ∀ β > 0, Tendsto (fun k => (Fintype.card (ι k) : ℝ)⁻¹ *
      ∫ ω, Real.log (∑ σ, Real.exp (β * H k ω σ)) ∂(μ k)) l (𝓝 (F β))) :
    ∃ E₀, Tendsto (fun k => (Fintype.card (ι k) : ℝ)⁻¹ * ∫ ω, (H k ω).max ∂(μ k)) l (𝓝 E₀) ∧
      Tendsto (fun β => β⁻¹ * F β) atTop (𝓝 E₀) := by
  refine exists_tendsto_of_dist_le_of_tendsto
    (F := fun (β : ℝ) k => ((Fintype.card (ι k) : ℝ) * β)⁻¹ *
      ∫ ω, Real.log (∑ σ, Real.exp (β * H k ω σ)) ∂(μ k))
    (ε := fun β => Real.log 2 / β) (tendsto_const_nhds.div_atTop tendsto_id) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ k
    rw [Real.dist_eq]
    exact smooth_approximation_error_bound hβ (hmeas k) (hint k)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact ((h_lim β hβ).const_mul β⁻¹).congr fun k => by ring

end Limit

section SK

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))
  {F : ℝ → ℝ}

include hH

/-- **Monotonicity survives the thermodynamic limit, SK model:** for the Hamiltonian
`H N G σ = (√N)⁻¹ * (σ ⬝ᵥ (G *ᵥ σ))` with standard Gaussian disorder `G`, if
`N⁻¹ 𝔼 log Z_N(β) → F(β)` for every `β > 0`, then `β ↦ β⁻¹ (F(β) - log 2)` is non-decreasing. -/
theorem sk_monotoneOn_inv_mul_limit_sub_log_two
    (h_lim : ∀ β > 0, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ))
      ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) atTop
      (𝓝 (F β))) :
    MonotoneOn (fun β => β⁻¹ * (F β - Real.log 2)) (Set.Ioi 0) :=
  monotoneOn_inv_mul_limit_sub_log_two (ι := fun N : ℕ => Fin N) (l := atTop) (H := H)
    (μ := fun N : ℕ => Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (fun N σ => by simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable σ).1)
    (fun N σ => by simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable σ).2)
    (fun β hβ => by simpa only [Fintype.card_fin] using h_lim β hβ)

/-- **The zero-temperature limit, SK model** ([Panchenko, 2013, Eq. (1.10)]): if
`N⁻¹ 𝔼 log Z_N(β) → F(β)` for every `β > 0`, then `N⁻¹ 𝔼 max_σ H_N(σ)` converges to some `E₀` and
`β⁻¹ F(β) → E₀` as `β → ∞`. -/
theorem sk_exists_tendsto_ground_state_energy
    (h_lim : ∀ β > 0, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ))
      ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) atTop
      (𝓝 (F β))) :
    ∃ E₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, (H N G).max
      ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) atTop
        (𝓝 E₀) ∧ Tendsto (fun β => β⁻¹ * F β) atTop (𝓝 E₀) := by
  simpa only [Fintype.card_fin] using
    exists_tendsto_ground_state_energy (ι := fun N : ℕ => Fin N) (l := atTop)
      (μ := fun N : ℕ => Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)
      (H := H)
      (fun N σ => by simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable σ).1)
      (fun N σ => by simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable σ).2)
      (F := F) (fun β hβ => by simpa only [Fintype.card_fin] using h_lim β hβ)

end SK

end SpinGlasses
