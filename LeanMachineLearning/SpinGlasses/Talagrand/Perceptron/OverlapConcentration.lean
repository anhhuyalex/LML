/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IntegrableOfBound
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.RSFixedPoint
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDecoupling
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathCavityBound
public import LeanMachineLearning.SpinGlasses.Gibbs.GibbsReplicaMarginal
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.GaussianLayer

/-!
# Overlap concentration under the perceptron Gibbs measure (Talagrand Section 2.4, Eq. (2.69))

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.69)--(2.73)
(second half of Theorem 2.4.1).

1. **Site permutation symmetry (`perceptron_replica_site_perm`,
   `integral_perceptron_overlap_mul_eq_last_site`):** relabelling spin sites by `Equiv.Perm` leaves
   the disorder law and counting Gibbs law invariant, yielding Eq. (2.70)
   `ν((R_{1,2} - q) φ(R_{1,2} - q)) = ν((ε₁ ε₂ - q) φ(R_{1,2} - q))`, in particular for `φ = id`,
   `ν((R_{1,2} - q)²) = ν(f)` where `f = (ε₁ ε₂ - q)(R_{1,2} - q)`.
2. **Decoupling at `t = 0` (`integral_smartPath_zero_last_spin_eq`, Eq. (2.72)):** when
   `q = 𝔼 tanh²(z √r)` with `r = (variance : ℝ)`, Lemma 2.2.2 (`SmartPathDecoupling.lean`) kills
   `ν₀((ε₁ ε₂ - q)(R_{1,2}⁻ - q))`, leaving `ν₀(f) = (1 - q²) / (N + 1)`.
3. **Smart-path derivative and transport (`integral_perceptron_overlap_sub_sq_le`):**
   Proposition 2.3.6 (`p₁ = p₂ = 2`, Cauchy-Schwarz), `|f| ≤ 2 |R_{1,2} - q|`, Lemma 2.3.7
   (`ν_t ≤ 2 ν`), and MVT along `t ∈ [0, 1]` yield `ν((R_{1,2} - q)²) ≤ L / (N + 1)` whenever
   `α K(D) ≤ 1`, for any solution `(q, r)` of (2.68) (matching Talagrand's remark after the proof of
   Theorem 2.4.1) and for every `N, M : ℕ` (including `M = 0` and `N = 0`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

universe uR

/-! ### Site-permutation symmetry on `Fin L` and Eq. (2.70) -/

/-- **Site permutation symmetry of the perceptron Gibbs average.** Relabelling the spin sites of all
replicas by `pm : Equiv.Perm (Fin L)` leaves the disorder-averaged `R`-replica Gibbs expectation
invariant. No hypothesis on `u` or `Θ` is required. -/
theorem perceptron_replica_site_perm {L M : ℕ} {R : Type uR} [Fintype R]
    (u : ℝ → ℝ) (pm : Equiv.Perm (Fin L)) (Θ : (R → Fin L → ℤˣ) → ℝ) :
    let P := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin L => gaussianReal 0 1
    let E (g : Fin M → Fin L → ℝ) (τ : Fin L → ℤˣ) : ℝ :=
      ∑ k, u ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))
    ∫ g, ∫ σ : R → Fin L → ℤˣ, Θ (fun r i => σ r (pm i))
        ∂(Measure.pi fun _ : R => (Measure.count : Measure (Fin L → ℤˣ)).tilted (E g)) ∂P =
      ∫ g, ∫ σ : R → Fin L → ℤˣ, Θ σ
        ∂(Measure.pi fun _ : R => (Measure.count : Measure (Fin L → ℤˣ)).tilted (E g)) ∂P := by
  intro P E
  let e_spin : (Fin L → ℤˣ) ≃ (Fin L → ℤˣ) := Equiv.arrowCongr pm (Equiv.refl ℤˣ)
  have he_spin (τ : Fin L → ℤˣ) : (fun i => (e_spin τ) (pm i)) = τ :=
    funext fun i => by simp [e_spin]
  let e_col : (Fin L → ℝ) ≃ᵐ (Fin L → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) pm.symm
  have hmp_col : MeasurePreserving ⇑e_col
      (Measure.pi fun _ : Fin L => gaussianReal 0 1)
      (Measure.pi fun _ : Fin L => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) pm.symm
  let e_mat : (Fin M → Fin L → ℝ) ≃ᵐ (Fin M → Fin L → ℝ) :=
    MeasurableEquiv.piCongrRight fun _ => e_col
  have hmp_mat : MeasurePreserving ⇑e_mat P P :=
    measurePreserving_pi _ _ fun _ => hmp_col
  have hE_eq (g : Fin M → Fin L → ℝ) (τ : Fin L → ℤˣ) :
      E g (e_spin τ) = E (e_mat g) τ := by
    dsimp only [E]
    refine Finset.sum_congr rfl fun k _ => congrArg u (congrArg _ ?_)
    rw [← Equiv.sum_comp pm fun i => g k i * (((e_spin τ) i : ℤ) : ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg_i : (e_mat g) k i = g k (pm i) := by
      change (Equiv.piCongrLeft (fun _ : Fin L => ℝ) pm.symm (g k)) i = g k (pm i)
      rw [Equiv.piCongrLeft_apply]; simp
    have hτ_i : (e_spin τ) (pm i) = τ i := congrFun (he_spin τ) i
    rw [hg_i, hτ_i]
  have hpt (g : Fin M → Fin L → ℝ) :
      ∫ σ : R → Fin L → ℤˣ, Θ (fun r i => σ r (pm i))
        ∂(Measure.pi fun _ : R => (Measure.count : Measure (Fin L → ℤˣ)).tilted (E g)) =
      ∫ σ : R → Fin L → ℤˣ, Θ σ
        ∂(Measure.pi fun _ : R => (Measure.count : Measure (Fin L → ℤˣ)).tilted (E (e_mat g))) := by
    rw [integral_pi_count_tilted_equiv e_spin (E g) (fun σ => Θ (fun r i => σ r (pm i)))]
    have h_obs (σ : R → Fin L → ℤˣ) : (fun r i => (e_spin (σ r)) (pm i)) = σ :=
      funext fun r => he_spin (σ r)
    have h_en : (fun b => E g (e_spin b)) = E (e_mat g) := funext (hE_eq g)
    simp_rw [h_obs, h_en]
  simp_rw [hpt]
  exact hmp_mat.integral_comp'
    (fun g => ∫ σ : R → Fin L → ℤˣ, Θ σ
      ∂(Measure.pi fun _ : R => (Measure.count : Measure (Fin L → ℤˣ)).tilted (E g)))

/-- **Site-swap invariance for a two-replica spin observable under the perceptron Gibbs
measure.** -/
theorem integral_perceptron_two_replica_site_swap {N M : ℕ}
    (u : ℝ → ℝ) (Θ : Fin (N + 1) → (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ)
    (i : Fin (N + 1))
    (hΘ : ∀ x y : Fin (N + 1) → ℤˣ,
      Θ (Fin.last N) (fun j => x (Equiv.swap i (Fin.last N) j))
        (fun j => y (Equiv.swap i (Fin.last N) j)) = Θ i x y) :
    ∫ g : Fin M → Fin (N + 1) → ℝ,
      ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ i (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
            fun τ => ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, g k j * ((τ j : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) =
      ∫ g : Fin M → Fin (N + 1) → ℝ,
        ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ (Fin.last N) (σ 0) (σ 1)
          ∂(Measure.pi fun _ : Fin 2 =>
            (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
              fun τ => ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, g k j * ((τ j : ℤ) : ℝ)))
          ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
  have h1 := perceptron_replica_site_perm (L := N + 1) (M := M) (R := Fin 2) u
    (Equiv.swap i (Fin.last N)) (fun σ => Θ (Fin.last N) (σ 0) (σ 1))
  dsimp only at h1
  rw [← h1]
  exact integral_congr_ae (ae_of_all _ fun _ =>
    integral_congr_ae (ae_of_all _ fun σ => (hΘ (σ 0) (σ 1)).symm))

/-- **Talagrand Section 2.4, Eq. (2.70), for an arbitrary function `φ` of the overlap deviation.**
For `N + 1` spins and `M` constraints, site-permutation symmetry implies
`ν((R_{1,2} - q) φ(R_{1,2} - q)) = ν((ε₁ ε₂ - q) φ(R_{1,2} - q))` where `ε_r = σ_r(Fin.last N)` is
the last spin. Requires `u` measurable so the disorder average is integrable on each coordinate. -/
theorem integral_perceptron_overlap_mul_eq_last_site {N M : ℕ}
    {u : ℝ → ℝ} (hu : Measurable u) (q : ℝ) (φ : ℝ → ℝ) :
    let P := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let E (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
      ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))
    let Rf (x y : Fin (N + 1) → ℤˣ) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * ∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        (Rf (σ 0) (σ 1) - q) * φ (Rf (σ 0) (σ 1) - q)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))
        ∂P =
      ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((((σ 0 (Fin.last N) : ℤ) : ℝ) * ((σ 1 (Fin.last N) : ℤ) : ℝ) - q) *
          φ (Rf (σ 0) (σ 1) - q))
        ∂(Measure.pi fun _ : Fin 2 => (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g))
        ∂P := by
  intro P E Rf
  let Θ (i : Fin (N + 1)) (x y : Fin (N + 1) → ℤˣ) : ℝ :=
    (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q) * φ (Rf x y - q)
  let ν (Φ : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ) : ℝ :=
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ (σ 0) (σ 1)
      ∂(Measure.pi fun _ : Fin 2 => (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)) ∂P
  have hRperm (pm : Equiv.Perm (Fin (N + 1))) (x y : Fin (N + 1) → ℤˣ) :
      Rf (fun i => x (pm i)) (fun i => y (pm i)) = Rf x y := by
    dsimp only [Rf]
    rw [Equiv.sum_comp pm fun i => ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)]
  have hsite (i : Fin (N + 1)) : ν (Θ i) = ν (Θ (Fin.last N)) :=
    integral_perceptron_two_replica_site_swap u Θ i fun x y => by
      simp only [Θ, hRperm, Equiv.swap_apply_right]
  have hint (i : Fin (N + 1)) :
      Integrable (fun g => ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Θ i (σ 0) (σ 1)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted (E g)))
        P := by
    obtain ⟨C, hC⟩ := exists_abs_le_of_finite (fun σ : Fin 2 → Fin (N + 1) → ℤˣ => Θ i (σ 0) (σ 1))
    exact integrable_integral_pi_count_tilted_sum_potential hu
      (fun _ σ => Θ i (σ 0) (σ 1)) (fun _ => measurable_const) (fun _ σ => hC σ)
  have hsum : ν (fun x y => ∑ i, Θ i x y) = ∑ i, ν (Θ i) := by
    dsimp only [ν]
    exact integral_integral_finset_sum P
      (fun g => Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))
      Finset.univ (fun i (σ : Fin 2 → Fin (N + 1) → ℤˣ) => Θ i (σ 0) (σ 1))
      (fun _ _ _ => Integrable.of_finite) (fun i _ => hint i)
  have hpt (x y : Fin (N + 1) → ℤˣ) :
      ∑ i, Θ i x y = ((N : ℝ) + 1) * ((Rf x y - q) * φ (Rf x y - q)) := by
    have hL : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    dsimp only [Θ, Rf]
    rw [← Finset.sum_mul]
    have hsum_i : (∑ i : Fin (N + 1), (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)) =
        (∑ i : Fin (N + 1), ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) - ((N : ℝ) + 1) * q := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast; ring
    rw [hsum_i]
    field_simp
  have hν_lhs : ν (fun x y => ∑ i, Θ i x y) =
      ((N : ℝ) + 1) * ν (fun x y => (Rf x y - q) * φ (Rf x y - q)) := by
    dsimp only [ν]
    simp_rw [hpt, integral_const_mul]
  have hν_rhs : ∑ i : Fin (N + 1), ν (Θ i) = ((N : ℝ) + 1) * ν (Θ (Fin.last N)) := by
    simp_rw [hsite, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hν_lhs, hν_rhs] at hsum
  exact mul_left_cancel₀ (by positivity : ((N : ℝ) + 1) ≠ 0) hsum

/-! ### Decoupled `t = 0` identity Eq. (2.72) and smart-path monotonicity helpers -/

/-- **Monotonicity of a spin-only smart-path Gibbs average.** -/
private lemma integral_integral_pi_perceptron_smart_path_mono {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D) (t : ℝ) (variance : ℝ≥0)
    {G₁ G₂ : (R → PerceptronSpin N) → ℝ} (hle : ∀ a, G₁ a ≤ G₂ a) :
    let P := smartPathDisorder
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    (∫ ω, ∫ σ : R → SmartPathState N M, G₁ (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω)) ∂P) ≤
      ∫ ω, ∫ σ : R → SmartPathState N M, G₂ (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω)) ∂P := by
  intro P
  obtain ⟨C₁, hC₁⟩ := exists_abs_le_of_finite G₁
  obtain ⟨C₂, hC₂⟩ := exists_abs_le_of_finite G₂
  have hμ (ω : SmartPathDisorder N M) :
      IsProbabilityMeasure ((smartPathBase N M).tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hD ω t
  have hout1 : Integrable (fun ω => ∫ σ : R → SmartPathState N M, G₁ (fun r => (σ r).1)
      ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω))) P :=
    integrable_integral_pi_perceptron_smart_path hu hD t
      ((measurable_spin_only G₁).comp measurable_snd) (fun _ _ => hC₁ _)
  have hout2 : Integrable (fun ω => ∫ σ : R → SmartPathState N M, G₂ (fun r => (σ r).1)
      ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω))) P :=
    integrable_integral_pi_perceptron_smart_path hu hD t
      ((measurable_spin_only G₂).comp measurable_snd) (fun _ _ => hC₂ _)
  refine integral_mono hout1 hout2 fun ω => ?_
  have hin1 : Integrable (fun σ : R → SmartPathState N M => G₁ (fun r => (σ r).1))
      (Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω)) :=
    Integrable.of_bound (measurable_spin_only G₁).aestronglyMeasurable C₁
      (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hC₁ _)
  have hin2 : Integrable (fun σ : R → SmartPathState N M => G₂ (fun r => (σ r).1))
      (Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω)) :=
    Integrable.of_bound (measurable_spin_only G₂).aestronglyMeasurable C₂
      (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hC₂ _)
  exact integral_mono hin1 hin2 fun σ => hle _

/-- **Talagrand Section 2.4, Eq. (2.72): `ν₀(f) = (1 - q²) / (N + 1)` at `t = 0`.**
When `q = 𝔼 tanh²(z √r)` with `r = (variance : ℝ)`, the `t = 0` smart-path average of
`f(σ₁, σ₂) = (ε₁ ε₂ - q)(R_{1,2} - q)` equals `(1 - q²) / (N + 1)`. -/
theorem integral_smartPath_zero_last_spin_eq {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    {D : ℝ} (hD : ∀ x, u x ≤ D) (variance : ℝ≥0) {q : ℝ}
    (hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt (variance : ℝ)) ^ 2 ∂gaussianReal 0 1) :
    let P := smartPathDisorder
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let R_spin (σ τ : PerceptronSpin N) : ℝ :=
      ((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1)
    ∫ ω, ∫ σ : Fin 2 → SmartPathState N M,
        ((((σ 0).1.2 : ℤ) : ℝ) * (((σ 1).1.2 : ℤ) : ℝ) - q) *
          (R_spin (σ 0).1 (σ 1).1 - q)
        ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P =
      (1 - q ^ 2) / (N + 1) := by
  intro P R_spin
  have h_tanh_var : ∫ y : ℝ, Real.tanh y ^ 2 ∂gaussianReal 0 variance = q := by
    rw [NeuralNetwork.DeepLinear.gaussianReal_scaling variance]
    have hmap := integral_map (μ := gaussianReal 0 1)
      (φ := fun y : ℝ => Real.sqrt (variance : ℝ) * y) (by fun_prop)
      (f := fun y : ℝ => Real.tanh y ^ 2)
      ((continuous_pow 2).comp Real.continuous_tanh).aestronglyMeasurable
    rw [hmap, hq]
    exact integral_congr_ae (ae_of_all _ fun z => by dsimp only; congr 2; ring)
  let R_old (ρ : Fin 2 → Fin N → ℤˣ) : ℝ :=
    ((∑ i, ((ρ 0 i : ℤ) : ℝ) * ((ρ 1 i : ℤ) : ℝ)) / (N + 1)) - q
  have h_alg (σ : Fin 2 → PerceptronSpin N) :
      ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ) - q) * (R_spin (σ 0) (σ 1) - q) =
      R_old (fun l => (σ l).1) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ)) -
      q * R_old (fun l => (σ l).1) +
      (1 / (N + 1)) - (q / (N + 1)) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ)) := by
    have hε0 : (((σ 0).2 : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
    have hε1 : (((σ 1).2 : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
    dsimp only [R_spin, R_old]
    have hprod : ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ)) ^ 2 = 1 := by
      rw [mul_pow, hε0, hε1, mul_one]
    linear_combination (1 / ((N : ℝ) + 1)) * hprod
  let P_ga := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)
  have hFub (G : (Fin 2 → PerceptronSpin N) → ℝ) :
      (∫ ω, ∫ x : Fin 2 → SmartPathState N M, G (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P) =
        ∫ ω₀, ∫ y, ∫ x : Fin 2 → SmartPathState N M, G (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 =>
            (smartPathBase N M).tilted (smartPathEnergy u 0 (ω₀, y)))
          ∂gaussianReal 0 variance ∂P_ga := by
    obtain ⟨C, hC⟩ := exists_abs_le_of_finite G
    have hi : Integrable (fun ω => ∫ x : Fin 2 → SmartPathState N M, G (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)))
        (P_ga.prod (gaussianReal 0 variance)) := by
      have hi' : Integrable (fun ω => ∫ x : Fin 2 → SmartPathState N M, G (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) P :=
        integrable_integral_pi_perceptron_smart_path hu hD 0
          ((measurable_spin_only G).comp measurable_snd) (fun _ _ => hC _)
      dsimp only [P] at hi'
      rwa [smartPathDisorder_eq] at hi'
    dsimp only [P]
    rw [smartPathDisorder_eq]
    exact integral_prod _ hi
  have hdec1_pair := integral_perceptron_smart_path_decoupled_endpoint (N := N) (M := M) (n := 2)
    hu hD variance Finset.univ R_old
  dsimp only at hdec1_pair
  have hdec1 := hdec1_pair.1
  have hdec2_pair := integral_perceptron_smart_path_decoupled_endpoint (N := N) (M := M) (n := 2)
    hu hD variance Finset.univ (fun _ => (1 : ℝ))
  dsimp only at hdec2_pair
  have hdec2 := hdec2_pair.1
  have hcard2 : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
  have hprod2 (σ : Fin 2 → PerceptronSpin N) :
      ∏ l ∈ (Finset.univ : Finset (Fin 2)), (((σ l).2 : ℤˣ) : ℝ) =
        (((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ) := by
    rw [Fin.prod_univ_two]
  simp_rw [hcard2, hprod2, h_tanh_var] at hdec1 hdec2
  rw [← hFub (fun σ => R_old (fun l => (σ l).1) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))),
    ← hFub (fun σ => R_old (fun l => (σ l).1))] at hdec1
  rw [← hFub (fun σ => (1 : ℝ) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))),
    ← hFub (fun _ => (1 : ℝ))] at hdec2
  simp only [one_mul] at hdec2
  have hone : ∫ ω, ∫ _x : Fin 2 → SmartPathState N M, (1 : ℝ)
      ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P = 1 := by
    have hP : IsProbabilityMeasure P := by dsimp [P]; rw [smartPathDisorder_eq]; infer_instance
    have hμ (ω : SmartPathDisorder N M) :
        IsProbabilityMeasure ((smartPathBase N M).tilted (smartPathEnergy u 0 ω)) :=
      isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hD ω 0
    simp
  rw [hone, mul_one] at hdec2
  have hν_lin (G₁ G₂ : (Fin 2 → PerceptronSpin N) → ℝ) (c₁ c₂ : ℝ) :
      (∫ ω, ∫ x : Fin 2 → SmartPathState N M,
          (c₁ * G₁ (fun l => (x l).1) + c₂ * G₂ (fun l => (x l).1))
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P) =
        c₁ * (∫ ω, ∫ x : Fin 2 → SmartPathState N M, G₁ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P) +
        c₂ * (∫ ω, ∫ x : Fin 2 → SmartPathState N M, G₂ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 =>
            (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P) := by
    obtain ⟨C₁, hC₁⟩ := exists_abs_le_of_finite G₁
    obtain ⟨C₂, hC₂⟩ := exists_abs_le_of_finite G₂
    have hμ (ω : SmartPathDisorder N M) :
        IsProbabilityMeasure ((smartPathBase N M).tilted (smartPathEnergy u 0 ω)) :=
      isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hD ω 0
    have hin1 (ω : SmartPathDisorder N M) :
        Integrable (fun x : Fin 2 → SmartPathState N M => G₁ (fun l => (x l).1))
          (Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) :=
      Integrable.of_bound (measurable_spin_only G₁).aestronglyMeasurable C₁
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC₁ _)
    have hin2 (ω : SmartPathDisorder N M) :
        Integrable (fun x : Fin 2 → SmartPathState N M => G₂ (fun l => (x l).1))
          (Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) :=
      Integrable.of_bound (measurable_spin_only G₂).aestronglyMeasurable C₂
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC₂ _)
    have hpt_lin (ω : SmartPathDisorder N M) :
        (∫ x : Fin 2 → SmartPathState N M,
          (c₁ * G₁ (fun l => (x l).1) + c₂ * G₂ (fun l => (x l).1))
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) =
        c₁ * (∫ x : Fin 2 → SmartPathState N M, G₁ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) +
        c₂ * (∫ x : Fin 2 → SmartPathState N M, G₂ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) := by
      have heq : (fun x : Fin 2 → SmartPathState N M =>
          c₁ * G₁ (fun l => (x l).1) + c₂ * G₂ (fun l => (x l).1)) =
          (fun x => c₁ * G₁ (fun l => (x l).1)) + (fun x => c₂ * G₂ (fun l => (x l).1)) := rfl
      rw [heq, integral_add' ((hin1 ω).const_mul c₁) ((hin2 ω).const_mul c₂),
        integral_const_mul, integral_const_mul]
    simp_rw [hpt_lin]
    have hout1 : Integrable (fun ω => ∫ x : Fin 2 → SmartPathState N M, G₁ (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) P :=
      integrable_integral_pi_perceptron_smart_path hu hD 0
        ((measurable_spin_only G₁).comp measurable_snd) (fun _ _ => hC₁ _)
    have hout2 : Integrable (fun ω => ∫ x : Fin 2 → SmartPathState N M, G₂ (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) P :=
      integrable_integral_pi_perceptron_smart_path hu hD 0
        ((measurable_spin_only G₂).comp measurable_snd) (fun _ _ => hC₂ _)
    have heq2 : (fun ω =>
        c₁ * (∫ x : Fin 2 → SmartPathState N M, G₁ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) +
        c₂ * (∫ x : Fin 2 → SmartPathState N M, G₂ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)))) =
        (fun ω => c₁ * ∫ x, G₁ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) +
        (fun ω => c₂ * ∫ x, G₂ (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω))) := rfl
    rw [heq2, integral_add' (hout1.const_mul c₁) (hout2.const_mul c₂),
      integral_const_mul, integral_const_mul]
  let A_term (σ : Fin 2 → PerceptronSpin N) : ℝ :=
    R_old (fun l => (σ l).1) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ)) -
      q * R_old (fun l => (σ l).1)
  let B_term (σ : Fin 2 → PerceptronSpin N) : ℝ :=
    (1 / (N + 1)) - (q / (N + 1)) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))
  have hf_eq : (fun x : Fin 2 → SmartPathState N M =>
      ((((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ) - q) *
        (R_spin (x 0).1 (x 1).1 - q)) =
      fun x => 1 * A_term (fun l => (x l).1) + 1 * B_term (fun l => (x l).1) := by
    funext x
    rw [h_alg (fun l => (x l).1)]
    dsimp only [A_term, B_term]
    ring
  simp_rw [hf_eq]
  rw [hν_lin A_term B_term 1 1, one_mul, one_mul]
  let G_A1 (σ : Fin 2 → PerceptronSpin N) : ℝ :=
    R_old (fun l => (σ l).1) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))
  let G_A2 (σ : Fin 2 → PerceptronSpin N) : ℝ := R_old (fun l => (σ l).1)
  let G_B2 (σ : Fin 2 → PerceptronSpin N) : ℝ := (((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ)
  have hA_eq (x : Fin 2 → SmartPathState N M) :
      A_term (fun l => (x l).1) = 1 * G_A1 (fun l => (x l).1) + (-q) * G_A2 (fun l => (x l).1) := by
    dsimp only [A_term, G_A1, G_A2]; ring
  have hB_eq (x : Fin 2 → SmartPathState N M) :
      B_term (fun l => (x l).1) =
        (1 / ((N : ℝ) + 1)) * (fun _ : Fin 2 → PerceptronSpin N => (1 : ℝ)) (fun l => (x l).1) +
        (-(q / ((N : ℝ) + 1))) * G_B2 (fun l => (x l).1) := by
    dsimp only [B_term, G_B2]; ring
  have hA_int : (∫ ω, ∫ x : Fin 2 → SmartPathState N M, A_term (fun l => (x l).1)
      ∂(Measure.pi fun _ : Fin 2 =>
        (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P) = 0 := by
    simp_rw [hA_eq]
    rw [hν_lin G_A1 G_A2 1 (-q)]
    dsimp only [G_A1, G_A2]
    rw [hdec1]
    ring
  have hB_int : (∫ ω, ∫ x : Fin 2 → SmartPathState N M, B_term (fun l => (x l).1)
      ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N M).tilted (smartPathEnergy u 0 ω)) ∂P) =
      (1 - q ^ 2) / (N + 1) := by
    simp_rw [hB_eq]
    rw [hν_lin (fun _ => (1 : ℝ)) G_B2 (1 / ((N : ℝ) + 1)) (-(q / ((N : ℝ) + 1))), hone]
    dsimp only [G_B2]
    rw [hdec2]
    ring
  rw [hA_int, hB_int, zero_add]

/-! ### Overlap concentration Eq. (2.69) -/

/-- **Overlap concentration at `M = 0` constraints:** with `0` constraints (`α = 0`), the fixed
point of (2.68) is `r = 0, q = 0`, and under the uniform hypercube measure on `Fin (N + 1) → ℤˣ`,
`ν((R_{1,2} - 0)²) = 1 / (N + 1)`. -/
private lemma integral_perceptron_overlap_sq_zero_constraints (N : ℕ) (u : ℝ → ℝ) :
    ∫ g : Fin 0 → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - 0) ^ 2
        ∂(Measure.pi fun _ : Fin 2 =>
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
            fun τ : Fin (N + 1) → ℤˣ =>
              ∑ k : Fin 0, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) =
      1 / ((N : ℝ) + 1) := by
  have h0_sum (g : Fin 0 → Fin (N + 1) → ℝ) :
      (fun τ : Fin (N + 1) → ℤˣ =>
        ∑ k : Fin 0, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))) =
      fun τ : Fin (N + 1) → ℤˣ => ∑ k : Fin 0,
        (0 : ℝ → ℝ) ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)) := by
    funext _; exact Finset.sum_congr rfl fun k _ => Fin.elim0 k
  have h0_int : (∫ g : Fin 0 → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - 0) ^ 2
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
          fun τ : Fin (N + 1) → ℤˣ =>
            ∑ k : Fin 0, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) =
    ∫ g : Fin 0 → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - 0) ^ 2
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
          fun τ : Fin (N + 1) → ℤˣ =>
            ∑ k : Fin 0, (0 : ℝ → ℝ) ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) :=
    integral_congr_ae (ae_of_all _ fun g => by dsimp only; rw [h0_sum g])
  rw [h0_int]
  have hsym := integral_perceptron_overlap_mul_eq_last_site (N := N) (M := 0) (u := 0)
    measurable_const 0 id
  dsimp only [id_eq] at hsym
  have hlhs : (∫ g : Fin 0 → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - 0) ^ 2
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
          fun τ : Fin (N + 1) → ℤˣ =>
            ∑ k : Fin 0, (0 : ℝ → ℝ) ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) =
    ∫ g : Fin 0 → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((((σ 0 (Fin.last N) : ℤ) : ℝ) * ((σ 1 (Fin.last N) : ℤ) : ℝ) - 0) *
        (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - 0))
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
          fun τ : Fin (N + 1) → ℤˣ =>
            ∑ k : Fin 0, (0 : ℝ → ℝ) ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
    rw [← hsym]
    exact integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun _ => by ring))
  rw [hlhs, ← integral_integral_pi_perceptron_smart_path_one_eq (N := N) (M := 0) 0 0]
  let P_z := smartPathDisorder
    (Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin N => gaussianReal 0 1) 0
  have h10 : (∫ ω, ∫ x : Fin 2 → SmartPathState N 0,
      ((((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x 0).1.1 (x 0).1.2)
          (Fin.last N) : ℤ) : ℝ) *
        (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x 1).1.1 (x 1).1.2)
          (Fin.last N) : ℤ) : ℝ) - 0) *
        (((N : ℝ) + 1)⁻¹ *
          ∑ i, (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x 0).1.1 (x 0).1.2) i : ℤ) : ℝ) *
            (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x 1).1.1 (x 1).1.2) i : ℤ) : ℝ) - 0)
      ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N 0).tilted (smartPathEnergy 0 1 ω)) ∂P_z) =
    ∫ ω, ∫ x : Fin 2 → SmartPathState N 0,
      ((((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ) - 0) *
        (((∑ i, (((x 0).1.1 i : ℤ) : ℝ) * (((x 1).1.1 i : ℤ) : ℝ)) +
          (((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ)) / (N + 1) - 0)
      ∂(Measure.pi fun _ : Fin 2 => (smartPathBase N 0).tilted (smartPathEnergy 0 0 ω)) ∂P_z := by
    have hae : ∀ᵐ ω ∂P_z, ω.2 = 0 := by
      dsimp only [P_z]
      rw [smartPathDisorder_eq]
      have hy : ∀ᵐ y : ℝ ∂gaussianReal 0 (0 : ℝ≥0), y = 0 := by
        rw [gaussianReal_zero_var]
        exact (ae_dirac_iff (measurableSet_singleton 0)).2 rfl
      exact (Measure.quasiMeasurePreserving_snd).ae hy
    refine integral_congr_ae (hae.mono fun ω hω => ?_)
    dsimp only
    have hE : smartPathEnergy (0 : ℝ → ℝ) 1 ω = smartPathEnergy (0 : ℝ → ℝ) 0 ω := by
      funext x
      rw [smartPathEnergy_eq, smartPathEnergy_eq, hω]
      ring
    rw [hE]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hsum_snoc : ∑ i : Fin (N + 1),
        (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x 0).1.1 (x 0).1.2) i : ℤ) : ℝ) *
          (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x 1).1.1 (x 1).1.2) i : ℤ) : ℝ) =
        (∑ i : Fin N, (((x 0).1.1 i : ℤ) : ℝ) * (((x 1).1.1 i : ℤ) : ℝ)) +
          (((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ) := by
      rw [Fin.sum_univ_castSucc]
      simp
    simp only [Fin.snoc_last, hsum_snoc]
    ring
  rw [h10]
  have hdec0 := integral_smartPath_zero_last_spin_eq (N := N) (M := 0)
    (u := 0) measurable_const (D := 0) (fun _ => le_rfl) 0 (q := 0) (by simp)
  simpa using hdec0

/-- **Theorem 2.4.1 (overlap concentration part, Eq. (2.69)), for any solution `(q, r)` of (2.68).**
Given `D ∈ ℝ`, there exist constants `K(D) ≥ 0` and `L ≥ 0` (chosen before `N, M, u, q, r`) such
that whenever `u` satisfies (2.7), `α = M / (N + 1)` satisfies `α * K(D) ≤ 1`, and `(q, r)` solves
the replica-symmetric system (2.68) for load `α`, the two-replica overlap satisfies
`ν((R_{1,2} - q)²) ≤ L / (N + 1)` for every `N, M : ℕ` (including `M = 0` and `N = 0`).
As Talagrand emphasizes after the proof of Theorem 2.4.1, uniqueness of `(q, r)` is not used in this
proof. -/
theorem integral_perceptron_overlap_sub_sq_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) *
          perceptronRhat u q),
        ∫ g : Fin M → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                fun τ : Fin (N + 1) → ℤˣ =>
                  ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))
            ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
          L / ((N : ℝ) + 1) := by
  obtain ⟨K_der, hK_der0, h_der⟩ := exists_hasDerivAt_smartPath_abs_le_holder (Fin 2) D
  obtain ⟨K_dom, hK_dom0, h_dom⟩ := integral_smartPath_fin_two_le_two_mul_perceptron D
  let K' : ℝ := max K_dom (8 * K_der)
  refine ⟨K', 3, le_max_of_le_left hK_dom0, by norm_num, ?_⟩
  intro N M u hd hb hα q r hq hr
  rcases M with _ | M
  · have hr0 : r = 0 := by simp [hr]
    have hq0 : q = 0 := by simp [hq, hr0]
    rw [hq0, integral_perceptron_overlap_sq_zero_constraints N u]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
  have hα_cast : ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) = α := by push_cast; rfl
  rw [hα_cast] at hα hr
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα_dom : α * K_dom ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_max_left K_dom (8 * K_der)) hα0).trans hα
  have hα_der : α * (8 * K_der) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_max_right K_dom (8 * K_der)) hα0).trans hα
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
    rw [hq]
    have heq : (∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1) =
        ∫ z : ℝ, Real.tanh (1 * Real.sqrt r * z + 0) ^ 2 ∂gaussianReal 0 1 := by
      congr 1; ext z; ring_nf
    rw [heq]
    exact fixedPointMap_mem_Icc 1 0 r
  let rhat := perceptronRhat u q
  have hrhat0 : 0 ≤ rhat := perceptronRhat_nonneg u q
  let variance : ℝ≥0 := (α * rhat).toNNReal
  have hvar_eq : (variance : ℝ) = r := by
    rw [hr]; exact Real.coe_toNNReal _ (mul_nonneg hα0 hrhat0)
  let P_sp := smartPathDisorder
    (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
  let R_spin (a b : PerceptronSpin N) : ℝ :=
    ((∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)) + ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) / (N + 1)
  let f_sp (a : Fin 2 → PerceptronSpin N) : ℝ :=
    ((((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q) * (R_spin (a 0) (a 1) - q)
  let F_full (σ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q) ^ 2
  let Q_val : ℝ :=
    ∫ g : Fin (M + 1) → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, F_full σ
      ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
          (fun τ : Fin (N + 1) → ℤˣ =>
            ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))))
      ∂(Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
  have hQ_nonneg : 0 ≤ Q_val :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  let g_path (t : ℝ) : ℝ :=
    ∫ ω, ∫ σ : Fin 2 → SmartPathState N (M + 1), f_sp (fun r' => (σ r').1)
      ∂(Measure.pi fun _ : Fin 2 =>
        (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P_sp
  have hg1_eq : g_path 1 = Q_val := by
    let F_last (σ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
      ((((σ 0 (Fin.last N) : ℤ) : ℝ) * ((σ 1 (Fin.last N) : ℤ) : ℝ) - q) *
        (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q))
    have hsnoc (a : Fin 2 → PerceptronSpin N) :
        f_sp a =
          F_last (fun r' => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (a r').1 (a r').2) := by
      dsimp only [f_sp, F_last, R_spin]
      have hsum_snoc : ∑ i : Fin (N + 1),
          (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (a 0).1 (a 0).2) i : ℤ) : ℝ) *
            (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (a 1).1 (a 1).2) i : ℤ) : ℝ) =
          (∑ i : Fin N, (((a 0).1 i : ℤ) : ℝ) * (((a 1).1 i : ℤ) : ℝ)) +
            (((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) := by
        rw [Fin.sum_univ_castSucc]; simp
      simp only [Fin.snoc_last, hsum_snoc]
      ring
    dsimp only [g_path]
    simp_rw [hsnoc]
    rw [integral_integral_pi_perceptron_smart_path_one_eq (N := N) (M := M + 1) u variance F_last]
    have hsym := integral_perceptron_overlap_mul_eq_last_site (N := N) (M := M + 1)
      hu.measurable q id
    dsimp only [id_eq] at hsym
    rw [← hsym]
    exact integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun _ => by
      dsimp only [F_full]; ring))
  have hg0_eq : g_path 0 = (1 - q ^ 2) / ((N : ℝ) + 1) :=
    integral_smartPath_zero_last_spin_eq hu.measurable (fun x => hu.le x) variance
      (by rwa [hvar_eq])
  have hg_cont : ContinuousOn g_path (Icc 0 1) :=
    continuousOn_integral_integral_pi_perceptron_smart_path hu.continuous hu.abs_le variance f_sp
  let B_der : ℝ := α * K_der * (4 * Q_val + 4 / ((N : ℝ) + 1))
  have h_eps_sub (a : Fin 2 → PerceptronSpin N) :
      |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q| ≤ 2 := by
    have h1 : |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ)| = 1 := by
      rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
    have h2 := abs_sub ((((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ)) q
    rw [h1, abs_of_nonneg hq_mem.1] at h2
    linarith [hq_mem.2]
  have hf_le_two_d (a : Fin 2 → PerceptronSpin N) :
      |f_sp a| ≤ 2 * |R_spin (a 0) (a 1) - q| := by
    dsimp only [f_sp]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (h_eps_sub a) (abs_nonneg _)
  have hf_le_four (a : Fin 2 → PerceptronSpin N) : |f_sp a| ≤ 4 := by
    have hd2 : |R_spin (a 0) (a 1) - q| ≤ 2 := abs_perceptron_overlap_sub_le_two hq_mem _ _
    linarith [hf_le_two_d a]
  have hf_sq_le (a : Fin 2 → PerceptronSpin N) :
      |f_sp a| ^ (2 : ℝ) ≤ 4 * |R_spin (a 0) (a 1) - q| ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.rpow_two]
    have h1 := hf_le_two_d a
    nlinarith [abs_nonneg (f_sp a)]
  have hg_deriv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      ∃ d', HasDerivAt g_path d' t ∧ |d'| ≤ B_der := by
    have hp22 : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]; norm_num
    obtain ⟨d', hd', hbd⟩ := h_der N M ht hq_mem hd hb f_sp hp22
    refine ⟨d', hd', hbd.trans ?_⟩
    have hI1_le : (∫ ω, ∫ σ : Fin 2 → SmartPathState N (M + 1),
        |f_sp (fun r' => (σ r').1)|
        ∂(Measure.pi fun _ : Fin 2 =>
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P_sp) ≤ 4 := by
      have hm := integral_integral_pi_perceptron_smart_path_mono (N := N) (M := M + 1)
        hu.measurable (fun x => hu.le x) t variance
        (G₁ := fun a => |f_sp a|) (G₂ := fun _ => (4 : ℝ)) hf_le_four
      dsimp only at hm
      have hP_prob : IsProbabilityMeasure P_sp := by
        dsimp [P_sp]; rw [smartPathDisorder_eq]; infer_instance
      have hμ_prob (ω : SmartPathDisorder N (M + 1)) :
          IsProbabilityMeasure ((smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) :=
        isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable
          (fun x => hu.le x) ω t
      simpa using hm
    let B_t : ℝ := ∫ ω, ∫ a : Fin 2 → SmartPathState N (M + 1),
      |R_spin (a 0).1 (a 1).1 - q| ^ (2 : ℝ)
      ∂(Measure.pi fun _ : Fin 2 =>
        (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P_sp
    have hBt0 : 0 ≤ B_t := integral_nonneg fun _ => integral_nonneg fun _ =>
      Real.rpow_nonneg (abs_nonneg _) _
    have hBt_le_2Q : B_t ≤ 2 * Q_val := by
      have hBt_eq : B_t = ∫ ω, ∫ σ : Fin 2 → SmartPathState N (M + 1),
          F_full (fun r' => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (σ r').1.1 (σ r').1.2)
          ∂(Measure.pi fun _ : Fin 2 =>
            (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P_sp := by
        refine integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun σ => ?_))
        dsimp only [F_full, R_spin]
        rw [Real.rpow_two, sq_abs]
        have hsum_snoc : ∑ i : Fin (N + 1),
            (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (σ 0).1.1 (σ 0).1.2) i : ℤ) : ℝ) *
              (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (σ 1).1.1 (σ 1).1.2) i : ℤ) : ℝ) =
            (∑ i : Fin N, (((σ 0).1.1 i : ℤ) : ℝ) * (((σ 1).1.1 i : ℤ) : ℝ)) +
              (((σ 0).1.2 : ℤ) : ℝ) * (((σ 1).1.2 : ℤ) : ℝ) := by
          rw [Fin.sum_univ_castSucc]; simp
        rw [hsum_snoc]
        ring
      rw [hBt_eq]
      exact h_dom N M ⟨ht.1.le, ht.2.le⟩ hq_mem hd hb hα_dom F_full (fun _ => sq_nonneg _)
    let A_t : ℝ := ∫ ω, ∫ σ : Fin 2 → SmartPathState N (M + 1),
      |f_sp (fun r' => (σ r').1)| ^ (2 : ℝ)
      ∂(Measure.pi fun _ : Fin 2 =>
        (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P_sp
    have hAt0 : 0 ≤ A_t := integral_nonneg fun _ => integral_nonneg fun _ =>
      Real.rpow_nonneg (abs_nonneg _) _
    have hAt_le_4Bt : A_t ≤ 4 * B_t := by
      have hm := integral_integral_pi_perceptron_smart_path_mono (N := N) (M := M + 1)
        hu.measurable (fun x => hu.le x) t variance
        (G₁ := fun a => |f_sp a| ^ (2 : ℝ))
        (G₂ := fun a => 4 * |R_spin (a 0) (a 1) - q| ^ (2 : ℝ)) hf_sq_le
      dsimp only at hm
      refine hm.trans_eq ?_
      dsimp only [B_t]
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun ω => by
        dsimp only
        rw [integral_const_mul])
    have hprod_AtBt : A_t ^ (1 / (2 : ℝ)) * B_t ^ (1 / (2 : ℝ)) ≤ 4 * Q_val := by
      have hrpow_sqrt (x : ℝ) (_hx : 0 ≤ x) : x ^ (1 / (2 : ℝ)) = Real.sqrt x :=
        (Real.sqrt_eq_rpow x).symm
      rw [hrpow_sqrt A_t hAt0, hrpow_sqrt B_t hBt0]
      have hsqrt4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
      have hs1 : Real.sqrt A_t ≤ 2 * Real.sqrt B_t := by
        calc Real.sqrt A_t ≤ Real.sqrt (4 * B_t) := Real.sqrt_le_sqrt hAt_le_4Bt
          _ = Real.sqrt 4 * Real.sqrt B_t := Real.sqrt_mul (by norm_num) B_t
          _ = 2 * Real.sqrt B_t := by rw [hsqrt4]
      calc Real.sqrt A_t * Real.sqrt B_t
          ≤ (2 * Real.sqrt B_t) * Real.sqrt B_t :=
            mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg _)
        _ = 2 * (Real.sqrt B_t * Real.sqrt B_t) := by ring
        _ = 2 * B_t := by rw [Real.mul_self_sqrt hBt0]
        _ ≤ 2 * (2 * Q_val) := mul_le_mul_of_nonneg_left hBt_le_2Q zero_le_two
        _ = 4 * Q_val := by ring
    dsimp only [B_der]
    refine mul_le_mul_of_nonneg_left (add_le_add hprod_AtBt ?_) (mul_nonneg hα0 hK_der0)
    have h1N : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    calc 1 / ((N : ℝ) + 1) * _ ≤ 1 / ((N : ℝ) + 1) * 4 :=
          mul_le_mul_of_nonneg_left hI1_le h1N
      _ = 4 / ((N : ℝ) + 1) := by ring
  have hinc : |g_path 1 - g_path 0| ≤ B_der := by
    have h := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hg_cont hg_deriv
      (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    simpa only [sub_zero, abs_one, mul_one] using h
  rw [hg1_eq, hg0_eq] at hinc
  have hQ_le : Q_val ≤ (1 - q ^ 2) / ((N : ℝ) + 1) + B_der := by
    linarith [(abs_le.1 hinc).2]
  have h1q : (1 - q ^ 2) / ((N : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg q]) (by positivity)
  have h4α : 4 * (α * K_der) ≤ 1 / 2 := by linarith [hα_der]
  let invL : ℝ := 1 / ((N : ℝ) + 1)
  have h1N : 0 ≤ invL := by dsimp only [invL]; positivity
  have h1q' : (1 - q ^ 2) / ((N : ℝ) + 1) ≤ invL := h1q
  have hB_le : B_der ≤ (1 / 2) * Q_val + (1 / 2) * invL := by
    have heq : B_der = (4 * (α * K_der)) * Q_val + (4 * (α * K_der)) * invL := by
      dsimp only [B_der, invL]; ring
    rw [heq]
    exact add_le_add (mul_le_mul_of_nonneg_right h4α hQ_nonneg)
      (mul_le_mul_of_nonneg_right h4α h1N)
  have hhalf : (1 / 2) * Q_val ≤ (3 / 2) * invL := by linarith [hQ_le, h1q', hB_le]
  calc Q_val = 2 * ((1 / 2) * Q_val) := by ring
    _ ≤ 2 * ((3 / 2) * invL) := mul_le_mul_of_nonneg_left hhalf zero_le_two
    _ = 3 / ((N : ℝ) + 1) := by dsimp only [invL]; ring

/-- Talagrand's Theorem 2.4.1. A single small-load bound gives a unique solution of
the replica-symmetric equations and the overlap second-moment estimate. -/
theorem exists_unique_rs_fixed_point_and_overlap_sub_sq_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ},
        (∀ j < 3, Differentiable ℝ (iteratedDeriv j u)) →
        (∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D) →
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        α * K ≤ 1 →
        let P := Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let μ (g : Fin M → Fin (N + 1) → ℝ) :=
          (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
            fun τ => ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ *
                ∑ i, g k i * ((τ i : ℤ) : ℝ))
        let rhat (q : ℝ) := perceptronRhat u q
        let S (p : ℝ × ℝ) : Prop :=
          p.1 = (∫ z : ℝ, Real.tanh (z * Real.sqrt p.2) ^ 2 ∂gaussianReal 0 1) ∧
          p.2 = α * rhat p.1
        (∃! p, S p) ∧ ∀ p, S p →
          (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - p.1) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => μ g) ∂P) ≤ L / ((N : ℝ) + 1) := by
  obtain ⟨K₁, hK₁, hfixed⟩ := exists_unique_rs_fixed_point D
  obtain ⟨K₂, L, hK₂, hL, hoverlap⟩ := integral_perceptron_overlap_sub_sq_le D
  refine ⟨max K₁ K₂, L, hK₁.trans (le_max_left _ _), hL, ?_⟩
  intro N M u hd hb α hα P μ rhat S
  have hα₀ : 0 ≤ α := by dsimp only [α]; positivity
  have h₁ := (mul_le_mul_of_nonneg_left (le_max_left K₁ K₂) hα₀).trans hα
  have h₂ := (mul_le_mul_of_nonneg_left (le_max_right K₁ K₂) hα₀).trans hα
  refine ⟨hfixed hd hb hα₀ h₁, ?_⟩
  intro p hp
  exact hoverlap N M hd hb h₂ hp.1 hp.2

end SpinGlasses
