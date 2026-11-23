/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityCovariance
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDifferentiation
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianTiltedSteinRatio
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavitySpecialization
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathExchangeable

/-!
# Time covariances of the smart-path fields (2.60) and Exercise 2.3.3

Exercise 2.3.3 of Talagrand's Section 2.3. Each field `S^ℓ_{k,t}(σ)` is a linear form in the
Gaussian vector `(g_{·,k}, g_k, ξ_k^ℓ)` indexed by `(Fin N ⊕ Unit) ⊕ R`, with coefficient vector
`Sum.elim (cavityCoef N t σ) (Pi.single ℓ √((1 - t)/(N + 1)))`. Its time derivative
`S'^ℓ_{k,t} = (2 √(N+1))⁻¹ (g_k ε_ℓ / √t - ξ_k^ℓ / √(1-t))` (the book's
`S_{k,t}^{ℓ \prime}`) is the linear form with coefficient vector
`Sum.elim (Sum.elim 0 (ε_σ / (2 √(N+1) √t))) (Pi.single ℓ (-1 / (2 √(N+1) √(1-t))))`
(`hasDerivAt_cavityTimeCoef`).

* `SpinGlasses.cavityTimeCoef_dotProduct`, `cavityTimeCoef_dotProduct_self`,
  `cavityTimeCoef_dotProduct_of_ne`: same-row dot products of (2.60).
* `SpinGlasses.integral_cavityTimeDeriv_mul_smartPathField`: full Gaussian expectation form of
  (2.60), including zero covariance across distinct rows `k ≠ k'` from disjoint coordinates.
* `SpinGlasses.stein_cavity_last_constraint_split`,
  `SpinGlasses.integral_smartPathFieldDeriv_mul_deriv_last`,
  `SpinGlasses.integral_smartPathFieldDeriv_mul_deriv_constraint`: the one-step Gaussian
  integration by parts formula for `ν_t(S'^ℓ_{k,t} u'(S^ℓ_{k,t}) f)` via
  `stein_tilted_replica_ratio`.
* `SpinGlasses.smartPath_one_step_recovery_last`: recovery of term I of (2.23)--(2.24) in one
  step by summing the one-step formula over `ℓ ≤ n` and subtracting `n` times the `n + 1` case.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

section DotProduct

variable {N : ℕ} {t : ℝ} {R : Type*} [Fintype R] [DecidableEq R]

/-- **Relations (2.60) as dot products of coefficient vectors.** For `t ∈ (0,1)`,
`S'^ℓ_σ ⬝ S^{ℓ'}_τ = (ε_σ ε_τ - 1_{ℓ = ℓ'}) / (2 (N + 1))`. -/
theorem cavityTimeCoef_dotProduct (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ τ : PerceptronSpin N)
    (ℓ ℓ' : R) :
    (Sum.elim (Sum.elim (fun _ : Fin N => (0 : ℝ))
        (fun _ : Unit => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))
      (Pi.single ℓ (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) ⬝ᵥ
    (Sum.elim (cavityCoef N t τ) (Pi.single ℓ' (Real.sqrt ((1 - t) / (N + 1)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) =
      (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ) - if ℓ = ℓ' then 1 else 0) / (2 * (N + 1)) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hsN : 0 < Real.sqrt (N + 1 : ℕ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos N)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hs1 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (sub_pos.2 ht.2)
  have e1 : Real.sqrt (t / (N + 1)) = Real.sqrt t / Real.sqrt (N + 1 : ℕ) := by
    rw [Real.sqrt_div' _ hN.le]; push_cast; rfl
  have e2 : Real.sqrt ((1 - t) / (N + 1)) = Real.sqrt (1 - t) / Real.sqrt (N + 1 : ℕ) := by
    rw [Real.sqrt_div' _ hN.le]; push_cast; rfl
  have e3 : Real.sqrt (N + 1 : ℕ) * Real.sqrt (N + 1 : ℕ) = N + 1 := by
    rw [Real.mul_self_sqrt (by positivity)]; push_cast; rfl
  have hR : ∀ D E : ℝ, ∑ r : R, (Pi.single ℓ D : R → ℝ) r * (Pi.single ℓ' E : R → ℝ) r =
      if ℓ = ℓ' then D * E else 0 := fun D E => by
    by_cases h : ℓ = ℓ'
    · subst h
      simp [Pi.single_apply]
    · simp only [h, ite_false]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = ℓ
      · subst hr
        simp [Ne.symm h]
      · simp [Pi.single_apply, hr]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, cavityCoef,
    Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, zero_mul,
    smul_zero, zero_add, hR]
  have e4 : Real.sqrt (N + 1 : ℕ) ^ 2 = N + 1 := by rw [sq, e3]
  rw [e1, e2]
  split_ifs with h
  · field_simp
    rw [e4]
    ring
  · field_simp
    rw [e4]
    ring

/-- **The coefficient vector of `S'` is the time derivative of that of `S`** (for `t ∈ (0,1)`):
coordinatewise, the derivative of `t ↦ cavityCoef N t σ` is `0` on the old couplings and
`ε_σ / (2 √(N+1) √t)` on `g_{N,M}`, and that of the `ξ`-coefficient `√((1-t)/(N+1))` is
`-1 / (2 √(N+1) √(1-t))`. -/
theorem hasDerivAt_cavityTimeCoef (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ : PerceptronSpin N) :
    (∀ i : Fin N, HasDerivAt (fun t => cavityCoef N t σ (Sum.inl i)) 0 t) ∧
    HasDerivAt (fun t => cavityCoef N t σ (Sum.inr ()))
      (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)) t ∧
    HasDerivAt (fun t => Real.sqrt ((1 - t) / (N + 1)))
      (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) t := by
  have hL : (0 : ℝ) ≤ N + 1 := by positivity
  have hsN : 0 < Real.sqrt (N + 1 : ℕ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos N)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hs1 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (sub_pos.2 ht.2)
  refine ⟨fun i => by simpa [cavityCoef] using hasDerivAt_const t _, ?_, ?_⟩
  · have hp := (Real.hasDerivAt_sqrt_div_const hL ht.1.ne').mul_const ((σ.2 : ℤ) : ℝ)
    refine (by simpa [cavityCoef] using hp : HasDerivAt _ _ t).congr_deriv ?_
    push_cast
    field_simp
  · have hm := (Real.hasDerivAt_sqrt_div_const hL (sub_pos.mpr ht.2).ne').comp t
      ((hasDerivAt_id t).const_sub 1)
    refine hm.congr_deriv ?_
    push_cast
    field_simp

/-- **(2.60), same replica:** `E S'^ℓ S^ℓ = 0`. -/
theorem cavityTimeCoef_dotProduct_self (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ : PerceptronSpin N)
    (ℓ : R) :
    (Sum.elim (Sum.elim (fun _ : Fin N => (0 : ℝ))
        (fun _ : Unit => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))
      (Pi.single ℓ (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) ⬝ᵥ
    (Sum.elim (cavityCoef N t σ) (Pi.single ℓ (Real.sqrt ((1 - t) / (N + 1)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) = 0 := by
  rw [cavityTimeCoef_dotProduct ht]
  simp [← sq, units_cast_sq]

/-- **(2.60), distinct replicas:** `E S'^ℓ S^{ℓ'} = ε_σ ε_τ / (2 (N + 1))` for `ℓ ≠ ℓ'`. -/
theorem cavityTimeCoef_dotProduct_of_ne (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ τ : PerceptronSpin N)
    {ℓ ℓ' : R} (h : ℓ ≠ ℓ') :
    (Sum.elim (Sum.elim (fun _ : Fin N => (0 : ℝ))
        (fun _ : Unit => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))
      (Pi.single ℓ (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) ⬝ᵥ
    (Sum.elim (cavityCoef N t τ) (Pi.single ℓ' (Real.sqrt ((1 - t) / (N + 1)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) =
      ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ) / (2 * (N + 1)) := by
  rw [cavityTimeCoef_dotProduct ht]
  simp [h]

end DotProduct

/-! ### Full Gaussian expectation form of (2.60) and Exercise 2.3.3 -/

section OneStepStein

universe uJ

/-- **Gaussian expectation form of relations (2.60) across all rows and replicas.**
Over the i.i.d. standard Gaussian vector `w = (g_{k,i}, a_k, ξ_k^ℓ)`, the expectation of
`S'^ℓ_{k,t}(σ) * S^{ℓ'}_{k',t}(τ)` vanishes when `k ≠ k'` (disjoint Gaussian coordinates) and
equals `(ε_σ ε_τ - 1_{ℓ = ℓ'}) / (2 (N + 1))` when `k = k'`. -/
theorem integral_cavityTimeDeriv_mul_smartPathField
    {N M : ℕ} {R : Type uJ} [Fintype R] [DecidableEq R]
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (k k' : Fin M) (σ τ : PerceptronSpin N) (ℓ ℓ' : R) :
    let K := (Fin M × Fin N) ⊕ (Fin M ⊕ (R × Fin M))
    let γ := Measure.pi fun _ : K => gaussianReal 0 1
    let S' (w : K → ℝ) : ℝ :=
      (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (w (Sum.inr (Sum.inl k)) * ((σ.2 : ℤ) : ℝ) / Real.sqrt t -
          w (Sum.inr (Sum.inr (ℓ, k))) / Real.sqrt (1 - t))
    let S (w : K → ℝ) : ℝ :=
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin N, w (Sum.inl (k', i)) * ((τ.1 i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * w (Sum.inr (Sum.inl k')) * ((τ.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - t) / (N + 1)) * w (Sum.inr (Sum.inr (ℓ', k')))
    ∫ w, S' w * S w ∂γ =
      if k = k' then
        (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ) - if ℓ = ℓ' then 1 else 0) / (2 * (N + 1))
      else 0 := by
  intro K γ S' S
  let c' : K → ℝ := Sum.elim 0 (Sum.elim
    (Pi.single k (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))
    (Pi.single (ℓ, k) (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)))))
  let c : K → ℝ := Sum.elim
    (fun p => if p.1 = k' then (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ.1 p.2 : ℤ) : ℝ) else 0)
    (Sum.elim
      (Pi.single k' (Real.sqrt (t / (N + 1)) * ((τ.2 : ℤ) : ℝ)))
      (Pi.single (ℓ', k') (Real.sqrt ((1 - t) / (N + 1)))))
  have hS' (w : K → ℝ) : S' w = c' ⬝ᵥ w := by
    change S' w = ∑ x : K, c' x * w x
    rw [Fintype.sum_sum_type]
    simp only [c', Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      zero_add, Fintype.sum_sum_type, Pi.single_apply, ite_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, S']
    ring
  have hS (w : K → ℝ) : S w = c ⬝ᵥ w := by
    change S w = ∑ x : K, c x * w x
    rw [Fintype.sum_sum_type]
    simp only [c, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type, Pi.single_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have h1 : ∑ p : Fin M × Fin N,
        (if p.1 = k' then (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ.1 p.2 : ℤ) : ℝ) *
          w (Sum.inl p) else 0) =
        (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin N, w (Sum.inl (k', i)) * ((τ.1 i : ℤ) : ℝ) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    dsimp only [S]
    ring
  simp_rw [hS', hS]
  rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
  have hdot : c' ⬝ᵥ c =
      (Pi.single k (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)) : Fin M → ℝ) k' *
        (Real.sqrt (t / (N + 1)) * ((τ.2 : ℤ) : ℝ)) +
      (Pi.single (ℓ, k) (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) :
        R × Fin M → ℝ) (ℓ', k') * Real.sqrt ((1 - t) / (N + 1)) := by
    dsimp only [c', c]
    rw [sumElim_dotProduct_sumElim, zero_dotProduct, zero_add,
      sumElim_dotProduct_sumElim, dotProduct_single, dotProduct_single]
  rw [hdot]
  by_cases hk : k = k'
  · subst hk
    simp only [↓reduceIte, Pi.single_eq_same]
    rw [← cavityTimeCoef_dotProduct (R := R) ht σ τ ℓ ℓ']
    dsimp only [cavityCoef]
    rw [sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, single_dotProduct]
    simp [dotProduct, Pi.single_apply, eq_comm]
  · have hk' : k' ≠ k := Ne.symm hk
    have hpair : (ℓ', k') ≠ (ℓ, k) := fun h => hk' (congrArg Prod.snd h)
    rw [Pi.single_eq_of_ne hk', Pi.single_eq_of_ne hpair]
    simp [hk]

/-- Exact state-space split of a `(M + 1)`-constraint replica average into the `M`-constraint
Gibbs law and the last auxiliary Gaussian `ξ_M` indexed by `Unit`. -/
theorem smartPath_last_replica_split_eq
    {N M : ℕ} {J : Type uJ} [Fintype J]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t : ℝ) (ω : SmartPathDisorder N (M + 1))
    (G : (J → SmartPathState N M × (Unit → ℝ)) → ℝ) :
    ∫ σ : J → SmartPathState N (M + 1),
      G (fun r => (((σ r).1, Fin.init (σ r).2), fun _ => (σ r).2 (Fin.last M)))
      ∂(Measure.pi fun _ : J => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) =
    ∫ τ : J → SmartPathState N M × (Unit → ℝ), G τ
      ∂(Measure.pi fun _ : J =>
        (((smartPathBase N M).tilted
            (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2))).prod
          (Measure.pi fun _ : Unit => gaussianReal 0 1)).tilted
        fun y : SmartPathState N M × (Unit → ℝ) =>
          u (cavityCoef N t y.1.1 ⬝ᵥ
              Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
            Real.sqrt ((1 - t) / (N + 1)) * y.2 ())) := by
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let e : SmartPathState N (M + 1) ≃ᵐ SmartPathState N M × (Unit → ℝ) :=
    (smartPathStateSplit N M).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.funUnique Unit ℝ).symm)
  have he_apply (x : SmartPathState N (M + 1)) :
      e x = ((x.1, Fin.init x.2), fun _ => x.2 (Fin.last M)) := by
    change (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.funUnique Unit ℝ).symm) (smartPathStateSplit N M x) = _
    rw [smartPathStateSplit_apply]
    rfl
  have hmp_e : MeasurePreserving ⇑e (smartPathBase N (M + 1))
      ((smartPathBase N M).prod (Measure.pi fun _ : Unit => γ₁)) := by
    have h1 := measurePreserving_smartPathStateSplit N M
    have h2 := (MeasurePreserving.id (smartPathBase N M)).prod
      (measurePreserving_funUnique γ₁ Unit).symm
    exact h2.comp h1
  let E₀ : SmartPathState N M → ℝ :=
    smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
  let V_dst : SmartPathState N M × (Unit → ℝ) → ℝ := fun y =>
    u (cavityCoef N t y.1.1 ⬝ᵥ
        Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
      Real.sqrt ((1 - t) / (N + 1)) * y.2 ())
  have hE_comp : smartPathEnergy u t ω ∘ e.symm = (fun y => E₀ y.1) + V_dst := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    change smartPathEnergy u t ω (e.symm (e x)) = E₀ (e x).1 + V_dst (e x)
    rw [MeasurableEquiv.symm_apply_apply, smartPathEnergy_eq_init_add u t ω x, he_apply]
    dsimp only [E₀, V_dst]
    rw [smartPathField_last_eq_dotProduct]
  have hmap_tilt : ((smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)).map e =
      (((smartPathBase N M).tilted E₀).prod (Measure.pi fun _ : Unit => γ₁)).tilted V_dst := by
    rw [map_tilted_measurableEquiv e hmp_e (measurable_smartPathEnergy_slice hu t ω), hE_comp]
    have hexp_E₀ : Integrable (fun y : SmartPathState N M × (Unit → ℝ) => Real.exp (E₀ y.1))
        ((smartPathBase N M).prod (Measure.pi fun _ : Unit => γ₁)) :=
      (integrable_exp_perceptron_smart_path_energy hu hD _ t).comp_fst _
    rw [← tilted_tilted hexp_E₀ V_dst, tilted_prod_comp_fst]
  have : IsProbabilityMeasure ((smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hD ω t
  have hrhs := (integral_pi_map_equiv
    ((smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) e G).symm
  rw [hmap_tilt] at hrhs
  simp_rw [he_apply] at hrhs
  exact hrhs

private lemma measurable_integral_pi_last_split
    {N M : ℕ} {J : Type uJ} [Fintype J] (t : ℝ)
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    {F : (SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) →
      (J → SmartPathState N M × (Unit → ℝ)) → ℝ}
    (hF : Measurable fun p : (SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) ×
      (J → SmartPathState N M × (Unit → ℝ)) => F p.1 p.2) :
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let α_sh (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ := cavityCoef N t σ
    let α_aux : Unit → ℝ := fun _ => Real.sqrt ((1 - t) / (N + 1))
    let S (w : Fin N ⊕ Unit → ℝ) (q : SmartPathState N M × (Unit → ℝ)) : ℝ :=
      α_sh q.1.1 ⬝ᵥ w + α_aux ⬝ᵥ q.2
    Measurable fun p => ∫ σ : J → SmartPathState N M × (Unit → ℝ), F p σ
      ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x))) := by
  intro μ₀ γ_aux α_sh α_aux S
  let Ω := SmartPathDisorder N M
  let W := Fin N ⊕ Unit → ℝ
  let T := SmartPathState N M × (Unit → ℝ)
  have hS : Measurable fun p : W × T => S p.1 p.2 := by
    have hX (j : Fin N ⊕ Unit) : Measurable fun p : W × T => α_sh p.2.1.1 j :=
      (measurable_of_finite fun a => α_sh a j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hdot : Measurable fun p : W × T => α_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ => (hX j).mul
        ((measurable_pi_apply j).comp measurable_fst)
    have haux : Measurable fun p : W × T => α_aux ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hdot.add haux
  let H (p : Ω × W) (x : T) := smartPathEnergy u t p.1 x.1 + u (S p.2 x)
  have hH : Measurable fun p : (Ω × W) × T => H p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × T => (p.1.1, p.2.1) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    have hp2 : Measurable fun p : (Ω × W) × T => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have h1 := (measurable_smartPathEnergy (N := N) (M := M) hu t).comp hp1
    have h2 := (hu.comp hS).comp hp2
    exact h1.add h2
  have hν (p : Ω × W) : ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x)) =
      ((smartPathBase N M).prod γ_aux).tilted (H p) := by
    rw [← tilted_prod_comp_fst, tilted_tilted
      ((integrable_exp_perceptron_smart_path_energy hu hD p.1 t).comp_fst γ_aux)]
    rfl
  simp_rw [hν]
  exact measurable_integral_pi_tilted hH hF

/-- Transport of a jointly measurable split last-constraint replica average to the full
`(M + 1)`-constraint smart-path Gibbs law. -/
theorem integral_pi_last_split_eq_smartPath
    {N M : ℕ} {J : Type uJ} [Fintype J]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t : ℝ) (v : ℝ≥0)
    {G : (SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) →
      (J → SmartPathState N M × (Unit → ℝ)) → ℝ}
    (hG : Measurable fun p : (SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) ×
      (J → SmartPathState N M × (Unit → ℝ)) => G p.1 p.2) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    let Pfull := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    let γ_sh := Measure.pi fun _ : Fin N ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let α_sh (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ := cavityCoef N t σ
    let α_aux : Unit → ℝ := fun _ => Real.sqrt ((1 - t) / (N + 1))
    let S (w : Fin N ⊕ Unit → ℝ) (q : SmartPathState N M × (Unit → ℝ)) : ℝ :=
      α_sh q.1.1 ⬝ᵥ w + α_aux ⬝ᵥ q.2
    let splitΩ (ω : SmartPathDisorder N (M + 1)) :=
      (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
        Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)))
    let splitT (x : SmartPathState N (M + 1)) : SmartPathState N M × (Unit → ℝ) :=
      ((x.1, Fin.init x.2), fun _ => x.2 (Fin.last M))
    ∫ p, ∫ σ, G p σ
        ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x)))
        ∂(P₀.prod γ_sh) =
      ∫ ω, ∫ σ, G (splitΩ ω) (fun r => splitT (σ r))
        ∂(Measure.pi fun _ : J => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω))
        ∂Pfull := by
  intro P₀ Pfull γ_sh γ_aux μ₀ α_sh α_aux S splitΩ splitT
  let I (p : SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) :=
    ∫ σ, G p σ ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x)))
  have hIm : Measurable I := measurable_integral_pi_last_split t hu hD hG
  have hmp : MeasurePreserving splitΩ Pfull (P₀.prod γ_sh) :=
    measurePreserving_smartPathDisorder_lastSplit N M v
  rw [← hmp.integral_comp_of_aestronglyMeasurable hIm.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hs (x : SmartPathState N M × (Unit → ℝ)) :
      S (splitΩ ω).2 x = cavityCoef N t x.1.1 ⬝ᵥ
          Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
        Real.sqrt ((1 - t) / (N + 1)) * x.2 () := by
    simp [S, α_sh, α_aux, splitΩ, dotProduct]
  change (∫ σ, G (splitΩ ω) σ
      ∂(Measure.pi fun _ : J => ((μ₀ (splitΩ ω).1).prod γ_aux).tilted
        (fun x => u (S (splitΩ ω).2 x)))) = _
  simp_rw [hs]
  exact (smartPath_last_replica_split_eq hu hD t ω (G (splitΩ ω))).symm

private lemma integrable_integral_pi_last_split_of_bound
    {N M : ℕ} {J : Type uJ} [Fintype J] (t : ℝ) (v : ℝ≥0)
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    {G : (SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) →
      (J → SmartPathState N M × (Unit → ℝ)) → ℝ}
    (hG : Measurable fun p : (SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) ×
      (J → SmartPathState N M × (Unit → ℝ)) => G p.1 p.2)
    {K : ℝ} (hGb : ∀ p σ, |G p σ| ≤ K) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    let γ_sh := Measure.pi fun _ : Fin N ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let α_sh (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ := cavityCoef N t σ
    let α_aux : Unit → ℝ := fun _ => Real.sqrt ((1 - t) / (N + 1))
    let S (w : Fin N ⊕ Unit → ℝ) (q : SmartPathState N M × (Unit → ℝ)) : ℝ :=
      α_sh q.1.1 ⬝ᵥ w + α_aux ⬝ᵥ q.2
    Integrable
      (fun p => ∫ σ, G p σ
        ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x))))
      (P₀.prod γ_sh) := by
  intro P₀ γ_sh γ_aux μ₀ α_sh α_aux S
  have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  have hμ₀ (ω : SmartPathDisorder N M) : IsProbabilityMeasure (μ₀ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M) hu hD ω t
  have hS : Measurable fun p : (Fin N ⊕ Unit → ℝ) × (SmartPathState N M × (Unit → ℝ)) =>
      S p.1 p.2 := by
    have hX (j : Fin N ⊕ Unit) :
        Measurable fun p : (Fin N ⊕ Unit → ℝ) × (SmartPathState N M × (Unit → ℝ)) =>
          α_sh p.2.1.1 j :=
      (measurable_of_finite fun a => α_sh a j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hdot : Measurable fun p : (Fin N ⊕ Unit → ℝ) × (SmartPathState N M × (Unit → ℝ)) =>
        α_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ => (hX j).mul
        ((measurable_pi_apply j).comp measurable_fst)
    exact hdot.add (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hV (p : SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ)) :
      Measurable fun x : SmartPathState N M × (Unit → ℝ) => u (S p.2 x) := by
    have hp : Measurable fun x : SmartPathState N M × (Unit → ℝ) => (p.2, x) :=
      measurable_const.prodMk measurable_id
    have hs := hS.comp hp
    exact hu.comp hs
  have hm := measurable_integral_pi_last_split t hu hD hG
  refine Integrable.of_bound hm.aestronglyMeasurable K (ae_of_all _ fun p => ?_)
  have : IsProbabilityMeasure (((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x))) :=
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hD _)
  rw [Real.norm_eq_abs]
  exact abs_integral_le_of_forall_abs_le _ (hGb p)

/-- **One-step Gaussian integration by parts on the split last constraint** (pointwise in old
disorder `ω₀`). Instantiates `stein_tilted_replica_ratio` with `ψ_ℓ = deriv u` and `ψ_r = 1` for
`r ≠ ℓ`, using `cavityTimeCoef_dotProduct_self` to cancel the diagonal term `j = ℓ` and
`cavityTimeCoef_dotProduct_of_ne` for the off-diagonal and fresh-replica terms. -/
theorem stein_cavity_last_constraint_split
    {N M : ℕ} {J : Type uJ} [Fintype J] [DecidableEq J]
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ω₀ : SmartPathDisorder N M) (ℓ : J)
    {g : (J → SmartPathState N M) → ℝ}
    (hgi : Integrable g (Measure.pi fun _ : J =>
      (smartPathBase N M).tilted (smartPathEnergy u t ω₀))) :
    let μ₀ := (smartPathBase N M).tilted (smartPathEnergy u t ω₀)
    let γ_sh := Measure.pi fun _ : Fin N ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let α_sh (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ := cavityCoef N t σ
    let W_sh (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ :=
      Sum.elim 0 (fun _ => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t))
    let α_aux : Unit → ℝ := fun _ => Real.sqrt ((1 - t) / (N + 1))
    let W_aux : Unit → ℝ := fun _ => -1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))
    let S (w : Fin N ⊕ Unit → ℝ) (q : SmartPathState N M × (Unit → ℝ)) : ℝ :=
      α_sh q.1.1 ⬝ᵥ w + α_aux ⬝ᵥ q.2
    let Wt (w : Fin N ⊕ Unit → ℝ) (q : SmartPathState N M × (Unit → ℝ)) : ℝ :=
      W_sh q.1.1 ⬝ᵥ w + W_aux ⬝ᵥ q.2
    ∫ w, ∫ σ : J → SmartPathState N M × (Unit → ℝ),
        g (fun r => (σ r).1) * Wt w (σ ℓ) * deriv u (S w (σ ℓ))
        ∂(Measure.pi fun _ : J => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh =
      (1 / (2 * (N + 1))) *
        ((∑ j ∈ Finset.univ.erase ℓ,
          ∫ w, ∫ σ : J → SmartPathState N M × (Unit → ℝ),
            g (fun r => (σ r).1) * (((σ ℓ).1.1.2 : ℤ) : ℝ) * (((σ j).1.1.2 : ℤ) : ℝ) *
              deriv u (S w (σ ℓ)) * deriv u (S w (σ j))
            ∂(Measure.pi fun _ : J => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh) -
        (Fintype.card J : ℝ) *
          ∫ w, ∫ σ : Option J → SmartPathState N M × (Unit → ℝ),
            g (fun r => (σ (some r)).1) *
              (((σ (some ℓ)).1.1.2 : ℤ) : ℝ) * (((σ none).1.1.2 : ℤ) : ℝ) *
              deriv u (S w (σ (some ℓ))) * deriv u (S w (σ none))
            ∂(Measure.pi fun _ : Option J =>
              (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh) := by
  intro μ₀ γ_sh γ_aux α_sh W_sh α_aux W_aux S Wt
  have : IsProbabilityMeasure μ₀ :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω₀ t
  let ψ : J → ℝ → ℝ := fun r x => if r = ℓ then deriv u x else 1
  let ψ' : J → ℝ → ℝ := fun r x =>
    if r = ℓ then deriv (deriv u) x + deriv u x ^ 2 else deriv u x
  have hψd : ∀ r, Differentiable ℝ fun x => ψ r x * Real.exp (u x) := fun r => by
    dsimp only [ψ]
    split_ifs
    · exact hu.differentiable_deriv.mul hu.differentiable.exp
    · simpa using hu.differentiable.exp
  have hψ_deriv : ∀ r x, deriv (fun y => ψ r y * Real.exp (u y)) x = ψ' r x * Real.exp (u x) := by
    intro r x
    dsimp only [ψ, ψ']
    split_ifs
    · have h1 : HasDerivAt (fun y => deriv u y * Real.exp (u y))
          (deriv (deriv u) x * Real.exp (u x) + deriv u x * (Real.exp (u x) * deriv u x)) x :=
        (hu.differentiable_deriv x).hasDerivAt.mul ((hu.differentiable x).hasDerivAt.exp)
      rw [h1.deriv]
      ring
    · have h1 := (hu.differentiable x).hasDerivAt.exp
      simpa [one_mul, mul_comm] using h1.deriv
  let M₀ : J → ℝ := fun _ => 1 + |D|
  let M' : J → ℝ := fun _ => (1 + |D₂| + |D| ^ 2 + |D|) * Real.exp |B|
  have hM₀ : ∀ r x, |ψ r x| ≤ M₀ r := fun r x => by
    dsimp only [ψ, M₀]
    split_ifs
    · linarith [hu.abs_deriv_le x, le_abs_self D, abs_nonneg D]
    · rw [abs_one]; linarith [abs_nonneg D]
  have hM' : ∀ r x, |deriv (fun y => ψ r y * Real.exp (u y)) x| ≤ M' r := fun r x => by
    rw [hψ_deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul ?_ (Real.exp_le_exp.2 ((hu.le x).trans (le_abs_self B)))
      (Real.exp_pos _).le (by positivity)
    dsimp only [ψ']
    split_ifs
    · have h2 := (hu.abs_deriv₂_le x).trans (le_abs_self D₂)
      have h1 : |deriv u x ^ 2| ≤ |D| ^ 2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hu.abs_deriv_le x).trans (le_abs_self D)) 2
      exact (abs_add_le _ _).trans (by linarith [abs_nonneg D, abs_nonneg D₂])
    · exact (hu.abs_deriv_le x).trans (by
        linarith [le_abs_self D, abs_nonneg D₂, sq_nonneg |D|])
  have hstein := stein_tilted_replica_ratio μ₀ (fun x : SmartPathState N M => x.1) measurable_fst
    α_sh W_sh (fun _ => α_aux) (fun _ => W_aux) hu.differentiable hu.abs_le hu.abs_deriv_le
    ψ hψd hM₀ hM' ψ' hψ_deriv ℓ hgi
  dsimp only at hstein
  have hprod_J (w : Fin N ⊕ Unit → ℝ) (f_σ : J → SmartPathState N M × (Unit → ℝ)) :
      ∏ r : J, ψ r (S w (f_σ r)) = deriv u (S w (f_σ ℓ)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun r => ψ r (S w (f_σ r))) (Finset.mem_univ ℓ)]
    have her : ∏ r ∈ Finset.univ.erase ℓ, ψ r (S w (f_σ r)) = 1 :=
      Finset.prod_eq_one fun r hr => by
        have hne : r ≠ ℓ := Finset.ne_of_mem_erase hr
        simp [ψ, hne]
    rw [her, mul_one]
    simp [ψ]
  simp only [show ∀ w q, α_sh q.1.1 ⬝ᵥ w + α_aux ⬝ᵥ q.2 = S w q from fun _ _ => rfl,
    show ∀ w q, W_sh q.1.1 ⬝ᵥ w + W_aux ⬝ᵥ q.2 = Wt w q from fun _ _ => rfl, hprod_J] at hstein
  change (∫ w, ∫ σ : J → SmartPathState N M × (Unit → ℝ),
      g (fun r => (σ r).1) * Wt w (σ ℓ) * deriv u (S w (σ ℓ))
      ∂(Measure.pi fun _ : J => (μ₀.prod (Measure.pi fun _ : Unit => gaussianReal 0 1)).tilted
        (fun q => u (S w q)))
      ∂(Measure.pi fun _ : Fin N ⊕ Unit => gaussianReal 0 1)) = _ at hstein
  rw [hstein]
  have hcov_same (σ : PerceptronSpin N) : W_sh σ ⬝ᵥ α_sh σ + W_aux ⬝ᵥ α_aux = 0 := by
    have h0 := cavityTimeCoef_dotProduct_self (R := Unit) ht σ ()
    simpa [W_sh, α_sh, W_aux, α_aux, sumElim_dotProduct_sumElim, dotProduct] using h0
  have hcov_diff (σ τ : PerceptronSpin N) :
      W_sh σ ⬝ᵥ α_sh τ = (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (2 * (N + 1)) := by
    have h0 := cavityTimeCoef_dotProduct_of_ne (R := Fin 2) ht σ τ (by decide : (0 : Fin 2) ≠ 1)
    simpa [W_sh, α_sh, sumElim_dotProduct_sumElim, dotProduct, Pi.single_apply] using h0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]
  have hdiag : ∫ w, ∫ σ : J → SmartPathState N M × (Unit → ℝ),
      g (fun r => (σ r).1) *
        (W_sh (σ ℓ).1.1 ⬝ᵥ α_sh (σ ℓ).1.1 +
          if ℓ = ℓ then W_aux ⬝ᵥ α_aux else 0) *
        (ψ' ℓ (S w (σ ℓ)) * ∏ r ∈ Finset.univ.erase ℓ, ψ r (S w (σ r)))
      ∂(Measure.pi fun _ : J => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh = 0 := by
    simp only [↓reduceIte, hcov_same, mul_zero, zero_mul, integral_zero]
  rw [hdiag, zero_add]
  have hoff : ∀ j ∈ Finset.univ.erase ℓ,
      ∫ w, ∫ σ : J → SmartPathState N M × (Unit → ℝ),
        g (fun r => (σ r).1) *
          (W_sh (σ ℓ).1.1 ⬝ᵥ α_sh (σ j).1.1 +
            if ℓ = j then W_aux ⬝ᵥ α_aux else 0) *
          (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : J => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh =
      (1 / (2 * (N + 1))) *
        ∫ w, ∫ σ : J → SmartPathState N M × (Unit → ℝ),
          g (fun r => (σ r).1) * (((σ ℓ).1.1.2 : ℤ) : ℝ) * (((σ j).1.1.2 : ℤ) : ℝ) *
            deriv u (S w (σ ℓ)) * deriv u (S w (σ j))
          ∂(Measure.pi fun _ : J => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh := by
    intro j hj
    have hne : j ≠ ℓ := Finset.ne_of_mem_erase hj
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp only
    have hprod_j : ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)) = deriv u (S w (σ ℓ)) := by
      have hmem : ℓ ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase _ _ hmem]
      have her2 : ∏ r ∈ (Finset.univ.erase j).erase ℓ, ψ r (S w (σ r)) = 1 :=
        Finset.prod_eq_one fun r hr => by
          have hr_ne : r ≠ ℓ := Finset.ne_of_mem_erase hr
          simp [ψ, hr_ne]
      rw [her2, mul_one]
      simp [ψ]
    simp only [hne.symm, ↓reduceIte, add_zero, hcov_diff, ψ', hne, hprod_j]
    ring
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum]
  have hfresh : ∫ w, ∫ σ : Option J → SmartPathState N M × (Unit → ℝ),
      g (fun r => (σ (some r)).1) *
        (W_sh (σ (some ℓ)).1.1 ⬝ᵥ α_sh (σ none).1.1) *
        deriv u (S w (σ (some ℓ))) * deriv u (S w (σ none))
      ∂(Measure.pi fun _ : Option J => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh =
    (1 / (2 * (N + 1))) *
      ∫ w, ∫ σ : Option J → SmartPathState N M × (Unit → ℝ),
        g (fun r => (σ (some r)).1) *
          (((σ (some ℓ)).1.1.2 : ℤ) : ℝ) * (((σ none).1.1.2 : ℤ) : ℝ) *
          deriv u (S w (σ (some ℓ))) * deriv u (S w (σ none))
        ∂(Measure.pi fun _ : Option J => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp only
    rw [hcov_diff]
    ring
  rw [hfresh]
  ring

private lemma integrable_integral_pi_last_split_deriv
    {N M : ℕ} {J : Type uJ} [Fintype J]
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (v : ℝ≥0)
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (ℓ : J)
    {f : SmartPathDisorder N M → (J → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (J → SmartPathState N M) => f p.1 p.2)
    {C_f : ℝ} (hfb : ∀ ω a, |f ω a| ≤ C_f) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    let γ_sh := Measure.pi fun _ : Fin N ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let α_sh (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ := cavityCoef N t σ
    let W_sh (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ :=
      Sum.elim 0 (fun _ => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t))
    let α_aux : Unit → ℝ := fun _ => Real.sqrt ((1 - t) / (N + 1))
    let W_aux : Unit → ℝ := fun _ => -1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))
    let S (w : Fin N ⊕ Unit → ℝ) (q : SmartPathState N M × (Unit → ℝ)) : ℝ :=
      α_sh q.1.1 ⬝ᵥ w + α_aux ⬝ᵥ q.2
    let Wt (w : Fin N ⊕ Unit → ℝ) (q : SmartPathState N M × (Unit → ℝ)) : ℝ :=
      W_sh q.1.1 ⬝ᵥ w + W_aux ⬝ᵥ q.2
    Integrable
      (fun p : SmartPathDisorder N M × (Fin N ⊕ Unit → ℝ) =>
        ∫ σ : J → SmartPathState N M × (Unit → ℝ),
          f p.1 (fun r => (σ r).1) * Wt p.2 (σ ℓ) * deriv u (S p.2 (σ ℓ))
          ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x))))
      (P₀.prod γ_sh) := by
  intro P₀ γ_sh γ_aux μ₀ α_sh W_sh α_aux W_aux S Wt
  let Ω := SmartPathDisorder N M
  let W := Fin N ⊕ Unit → ℝ
  let T := SmartPathState N M × (Unit → ℝ)
  let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x))
  let G_lhs (p : Ω × W) (σ : J → T) : ℝ :=
    f p.1 (fun r => (σ r).1) * Wt p.2 (σ ℓ) * deriv u (S p.2 (σ ℓ))
  have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  have hμ₀ (ω₀ : Ω) : IsProbabilityMeasure (μ₀ ω₀) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω₀ t
  have hSm : Measurable fun p : W × T => S p.1 p.2 := by
    have hX (j : Fin N ⊕ Unit) : Measurable fun p : W × T => α_sh p.2.1.1 j :=
      (measurable_of_finite fun a => α_sh a j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hdot : Measurable fun p : W × T => α_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ => (hX j).mul
        ((measurable_pi_apply j).comp measurable_fst)
    exact hdot.add (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hWtm : Measurable fun p : W × T => Wt p.1 p.2 := by
    have hX (j : Fin N ⊕ Unit) : Measurable fun p : W × T => W_sh p.2.1.1 j :=
      (measurable_of_finite fun a => W_sh a j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hdot : Measurable fun p : W × T => W_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ => (hX j).mul
        ((measurable_pi_apply j).comp measurable_fst)
    exact hdot.add (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hGm_lhs : Measurable fun p : (Ω × W) × (J → T) => G_lhs p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (J → T) =>
        ((p.1.1, fun r => (p.2 r).1) : Ω × (J → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have hp2 : Measurable fun p : (Ω × W) × (J → T) => (p.1.2, p.2 ℓ) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply ℓ).comp measurable_snd)
    have m1 := hf.comp hp1
    have m2 := hWtm.comp hp2
    have m30 := hSm.comp hp2
    have m3 := (measurable_deriv u).comp m30
    exact ((m1.mul m2).mul m3 : _)
  let J_lhs (p : Ω × W) : ℝ := ∫ σ : J → T, G_lhs p σ ∂(Measure.pi fun _ : J => ν p)
  have hm : Measurable J_lhs := measurable_integral_pi_last_split t hu.measurable
    (fun x => hu.le x) (F := G_lhs) hGm_lhs
  have hm_ae : AEStronglyMeasurable J_lhs (P₀.prod γ_sh) := hm.aestronglyMeasurable
  let c1 : ℝ := 1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)
  let c2 : ℝ := 1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))
  have hc1 : 0 ≤ c1 := by dsimp only [c1]; positivity
  have hc2 : 0 ≤ c2 := by dsimp only [c2]; positivity
  have hw_int : Integrable (fun w : W => |w (Sum.inr ())|) γ_sh :=
    (integrable_comp_eval (μ := fun _ : Fin N ⊕ Unit => gaussianReal 0 1)
      (i := Sum.inr ()) IsGaussian.integrable_id).abs
  have hη_int : Integrable (fun η : Unit → ℝ => |η ()|) γ_aux :=
    (integrable_comp_eval (μ := fun _ : Unit => gaussianReal 0 1)
      (i := ()) IsGaussian.integrable_id).abs
  let M_η : ℝ := ∫ η : Unit → ℝ, |η ()| ∂γ_aux
  let dom_w (w : W) : ℝ :=
    |C_f| * |D| * (c1 * |w (Sum.inr ())| + c2 * (Real.exp (2 * |B|) * M_η))
  have hdom_w : Integrable dom_w γ_sh :=
    ((hw_int.const_mul c1).add (integrable_const _)).const_mul (|C_f| * |D|)
  have hdom_int : Integrable (fun p : Ω × W => dom_w p.2) (P₀.prod γ_sh) :=
    hdom_w.comp_snd P₀
  change Integrable J_lhs (P₀.prod γ_sh)
  refine Integrable.mono' (g := fun p : Ω × W => dom_w p.2) hdom_int hm_ae (ae_of_all _ fun p => ?_)
  have hV : Measurable fun x : T => u (S p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have hs := hSm.comp hp
    have hv := hu.measurable.comp hs
    exact hv
  have : IsProbabilityMeasure (ν p) :=
    isProbabilityMeasure_tilted_of_ae_le hV.aemeasurable (ae_of_all _ fun _ => hu.le _)
  rw [Real.norm_eq_abs]
  have hWt_le (q : T) : |Wt p.2 q| ≤ c1 * |p.2 (Sum.inr ())| + c2 * |q.2 ()| := by
    have heq : Wt p.2 q =
        (((q.1.1.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)) * p.2 (Sum.inr ()) +
        (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) * q.2 () := by
      simp [Wt, W_sh, W_aux, dotProduct]
    rw [heq]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_div, abs_units_cast_eq_one]
      exact le_of_eq (by simp [c1, abs_of_pos (Real.sqrt_pos.2 ht.1)])
    · rw [abs_mul, abs_div, abs_neg, abs_one]
      exact le_of_eq (by simp [c2, abs_of_pos (Real.sqrt_pos.2 (sub_pos.2 ht.2))])
  have hσ_tilt : Integrable (fun σ : J → T => |(σ ℓ).2 ()|) (Measure.pi fun _ : J => ν p) ∧
      (∫ σ : J → T, |(σ ℓ).2 ()| ∂(Measure.pi fun _ : J => ν p)) ≤
        Real.exp (2 * |B|) * M_η := by
    have hbase : Integrable (fun q : T => |q.2 ()|) ((μ₀ p.1).prod γ_aux) :=
      hη_int.comp_snd (μ₀ p.1)
    have h1 : Integrable (fun q : T => |q.2 ()|) (ν p) :=
      integrable_tilted_of_ae_le (C := B) hV.aemeasurable
        (ae_of_all _ fun _ => hu.le _) hbase
    have hσ_i : Integrable (fun σ : J → T => |(σ ℓ).2 ()|) (Measure.pi fun _ : J => ν p) :=
      integrable_comp_eval (μ := fun _ : J => ν p) (i := ℓ) h1
    have hσ_eq : ∫ σ : J → T, |(σ ℓ).2 ()| ∂(Measure.pi fun _ : J => ν p) =
        ∫ q : T, |q.2 ()| ∂ν p := by
      have h := MeasureTheory.integral_comp_eval (μ := fun _ : J => ν p) (i := ℓ)
        (f := fun q : T => |q.2 ()|) h1.aestronglyMeasurable
      simpa [probReal_univ] using h
    have htilt_le := abs_integral_tilted_le_exp_mul_integral_abs
      (μ := (μ₀ p.1).prod γ_aux) (e := fun x => u (S p.2 x)) (Y := fun q : T => |q.2 ()|)
      hV.aemeasurable (ae_of_all _ fun x => (hu.abs_le _).trans (le_abs_self B)) hbase
    have hsnd := integral_prod_fun_snd_of_isProbabilityMeasure (μ₀ p.1) γ_aux (fun η => |η ()|)
    rw [probReal_univ, div_one] at htilt_le
    simp only [abs_abs] at htilt_le
    rw [hsnd] at htilt_le
    exact ⟨hσ_i, hσ_eq.le.trans ((le_abs_self _).trans htilt_le)⟩
  have hG_le (σ : J → T) :
      |G_lhs p σ| ≤ |C_f| * |D| * (c1 * |p.2 (Sum.inr ())| + c2 * |(σ ℓ).2 ()|) := by
    dsimp only [G_lhs]
    rw [abs_mul, abs_mul]
    calc |f p.1 (fun r => (σ r).1)| * |Wt p.2 (σ ℓ)| * |deriv u (S p.2 (σ ℓ))|
        ≤ |C_f| * (c1 * |p.2 (Sum.inr ())| + c2 * |(σ ℓ).2 ()|) * |D| :=
          mul_le_mul (mul_le_mul ((hfb _ _).trans (le_abs_self _)) (hWt_le _)
            (abs_nonneg _) (abs_nonneg _))
            ((hu.abs_deriv_le _).trans (le_abs_self _))
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      _ = _ := by ring
  calc |∫ σ : J → T, G_lhs p σ ∂(Measure.pi fun _ : J => ν p)|
      ≤ ∫ σ : J → T, |G_lhs p σ| ∂(Measure.pi fun _ : J => ν p) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ σ : J → T, |C_f| * |D| * (c1 * |p.2 (Sum.inr ())| + c2 * |(σ ℓ).2 ()|)
          ∂(Measure.pi fun _ : J => ν p) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (((integrable_const _).add (hσ_tilt.1.const_mul c2)).const_mul _)
          (ae_of_all _ hG_le)
    _ = |C_f| * |D| *
          (c1 * |p.2 (Sum.inr ())| +
            c2 * ∫ σ : J → T, |(σ ℓ).2 ()| ∂(Measure.pi fun _ : J => ν p)) := by
        have hi1 : Integrable (fun _ : J → T => c1 * |p.2 (Sum.inr ())|)
            (Measure.pi fun _ : J => ν p) := integrable_const _
        have hi2 : Integrable (fun σ : J → T => c2 * |(σ ℓ).2 ()|)
            (Measure.pi fun _ : J => ν p) := hσ_tilt.1.const_mul c2
        rw [integral_const_mul, integral_add hi1 hi2, integral_const, probReal_univ, one_smul,
          integral_const_mul]
    _ ≤ dom_w p.2 := by
        dsimp only [dom_w]
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hσ_tilt.2 hc2))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **Exercise 2.3.3, one-step Stein formula for the last constraint.**
For a bounded jointly measurable observable `f` of the old disorder and old replica states,
`ν_t(S'^ℓ_{M,t} u'(S^ℓ_{M,t}) f)` equals
`1/(2(N+1)) (∑_{j ≠ ℓ} ν_t(ε_ℓ ε_j u'(S^ℓ) u'(S^j) f) - |J| ν_t(ε_ℓ ε_* u'(S^ℓ) u'(S^*) f))`. -/
theorem integral_smartPathFieldDeriv_mul_deriv_last
    {N M : ℕ} {J : Type uJ} [Fintype J] [DecidableEq J]
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (v : ℝ≥0) (ℓ : J)
    {f : SmartPathDisorder N M → (J → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (J → SmartPathState N M) => f p.1 p.2)
    {C_f : ℝ} (hfb : ∀ ω a, |f ω a| ≤ C_f) :
    let P := smartPathDisorder
      (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    let S' (ω : SmartPathDisorder N (M + 1)) (x : SmartPathState N (M + 1)) : ℝ :=
      (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 (Fin.last M) * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t -
          x.2 (Fin.last M) / Real.sqrt (1 - t))
    let f_ext (ω : SmartPathDisorder N (M + 1)) (σ : J → SmartPathState N (M + 1)) : ℝ :=
      f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((σ r).1, Fin.init (σ r).2))
    ∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f_ext ω σ * S' ω (σ ℓ) * deriv u (smartPathField t ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : J => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P =
      (1 / (2 * (N + 1))) *
        ((∑ j ∈ Finset.univ.erase ℓ,
          ∫ ω, ∫ σ : J → SmartPathState N (M + 1),
            f_ext ω σ * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
              deriv u (smartPathField t ω (σ ℓ) (Fin.last M)) *
              deriv u (smartPathField t ω (σ j) (Fin.last M))
            ∂(Measure.pi fun _ : J =>
              (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P) -
        (Fintype.card J : ℝ) *
          ∫ ω, ∫ σ : Option J → SmartPathState N (M + 1),
            f_ext ω (fun r => σ (some r)) *
              (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
              deriv u (smartPathField t ω (σ (some ℓ)) (Fin.last M)) *
              deriv u (smartPathField t ω (σ none) (Fin.last M))
            ∂(Measure.pi fun _ : Option J =>
              (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P) := by
  intro P S' f_ext
  let Ω := SmartPathDisorder N M
  let W := Fin N ⊕ Unit → ℝ
  let T := SmartPathState N M × (Unit → ℝ)
  let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
    Measure.pi fun _ : Fin N => gaussianReal 0 1) v
  let γ_sh : Measure W := Measure.pi fun _ => gaussianReal 0 1
  let γ_aux : Measure (Unit → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let μ₀ (ω₀ : Ω) := (smartPathBase N M).tilted (smartPathEnergy u t ω₀)
  let α_sh (σ : PerceptronSpin N) : W := cavityCoef N t σ
  let W_sh (σ : PerceptronSpin N) : W :=
    Sum.elim 0 (fun _ => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t))
  let α_aux : Unit → ℝ := fun _ => Real.sqrt ((1 - t) / (N + 1))
  let W_aux : Unit → ℝ := fun _ => -1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))
  let S (w : W) (q : T) : ℝ := α_sh q.1.1 ⬝ᵥ w + α_aux ⬝ᵥ q.2
  let Wt (w : W) (q : T) : ℝ := W_sh q.1.1 ⬝ᵥ w + W_aux ⬝ᵥ q.2
  let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S p.2 x))
  have hμ₀ (ω₀ : Ω) : IsProbabilityMeasure (μ₀ ω₀) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω₀ t
  have hfi (ω₀ : Ω) : Integrable (f ω₀) (Measure.pi fun _ : J => μ₀ ω₀) :=
    Integrable.of_bound (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      C_f (ae_of_all _ fun a => by simpa using hfb ω₀ a)
  have hSm : Measurable fun p : W × T => S p.1 p.2 := by
    have hX (j : Fin N ⊕ Unit) : Measurable fun p : W × T => α_sh p.2.1.1 j :=
      (measurable_of_finite fun a => α_sh a j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hdot : Measurable fun p : W × T => α_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ => (hX j).mul
        ((measurable_pi_apply j).comp measurable_fst)
    exact hdot.add (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hWtm : Measurable fun p : W × T => Wt p.1 p.2 := by
    have hX (j : Fin N ⊕ Unit) : Measurable fun p : W × T => W_sh p.2.1.1 j :=
      (measurable_of_finite fun a => W_sh a j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hdot : Measurable fun p : W × T => W_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ => (hX j).mul
        ((measurable_pi_apply j).comp measurable_fst)
    exact hdot.add (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  let G_lhs (p : Ω × W) (σ : J → T) : ℝ :=
    f p.1 (fun r => (σ r).1) * Wt p.2 (σ ℓ) * deriv u (S p.2 (σ ℓ))
  let G_off (j : J) (p : Ω × W) (σ : J → T) : ℝ :=
    f p.1 (fun r => (σ r).1) * (((σ ℓ).1.1.2 : ℤ) : ℝ) * (((σ j).1.1.2 : ℤ) : ℝ) *
      deriv u (S p.2 (σ ℓ)) * deriv u (S p.2 (σ j))
  let G_fresh (p : Ω × W) (σ : Option J → T) : ℝ :=
    f p.1 (fun r => (σ (some r)).1) *
      (((σ (some ℓ)).1.1.2 : ℤ) : ℝ) * (((σ none).1.1.2 : ℤ) : ℝ) *
      deriv u (S p.2 (σ (some ℓ))) * deriv u (S p.2 (σ none))
  have hGm_lhs : Measurable fun p : (Ω × W) × (J → T) => G_lhs p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (J → T) =>
        ((p.1.1, fun r => (p.2 r).1) : Ω × (J → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have hp2 : Measurable fun p : (Ω × W) × (J → T) => (p.1.2, p.2 ℓ) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply ℓ).comp measurable_snd)
    have m1 := hf.comp hp1
    have m2 := hWtm.comp hp2
    have m30 := hSm.comp hp2
    have m3 := (measurable_deriv u).comp m30
    exact ((m1.mul m2).mul m3 : _)
  have hGm_off (j : J) : Measurable fun p : (Ω × W) × (J → T) => G_off j p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (J → T) =>
        ((p.1.1, fun r => (p.2 r).1) : Ω × (J → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have m1 := hf.comp hp1
    have mS (r : J) : Measurable fun p : (Ω × W) × (J → T) => deriv u (S p.1.2 (p.2 r)) := by
      have hpr : Measurable fun p : (Ω × W) × (J → T) => (p.1.2, p.2 r) :=
        (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)
      have hs := hSm.comp hpr
      exact (measurable_deriv u).comp hs
    have hε (r : J) : Measurable fun p : (Ω × W) × (J → T) => (((p.2 r).1.1.2 : ℤ) : ℝ) := by
      have hpr : Measurable fun p : (Ω × W) × (J → T) => (p.2 r).1.1.2 :=
        measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
          ((measurable_pi_apply r).comp measurable_snd)))
      exact measurable_units_cast.comp hpr
    exact ((((m1.mul (hε ℓ)).mul (hε j)).mul (mS ℓ)).mul (mS j) : _)
  have hGm_fresh : Measurable fun p : (Ω × W) × (Option J → T) => G_fresh p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (Option J → T) =>
        ((p.1.1, fun r => (p.2 (some r)).1) : Ω × (J → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))
    have m1 := hf.comp hp1
    have mS (r : Option J) :
        Measurable fun p : (Ω × W) × (Option J → T) => deriv u (S p.1.2 (p.2 r)) := by
      have hpr : Measurable fun p : (Ω × W) × (Option J → T) => (p.1.2, p.2 r) :=
        (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)
      have hs := hSm.comp hpr
      exact (measurable_deriv u).comp hs
    have hε (r : Option J) :
        Measurable fun p : (Ω × W) × (Option J → T) => (((p.2 r).1.1.2 : ℤ) : ℝ) := by
      have hpr : Measurable fun p : (Ω × W) × (Option J → T) => (p.2 r).1.1.2 :=
        measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
          ((measurable_pi_apply r).comp measurable_snd)))
      exact measurable_units_cast.comp hpr
    exact ((((m1.mul (hε (some ℓ))).mul (hε none)).mul (mS (some ℓ))).mul (mS none) : _)
  have hI_lhs : Integrable
      (fun p : Ω × W => ∫ σ : J → T, G_lhs p σ ∂(Measure.pi fun _ : J => ν p))
      (P₀.prod γ_sh) :=
    integrable_integral_pi_last_split_deriv ht v hu.toSmartPathPotential ℓ hf hfb
  have hI_off (j : J) : Integrable
      (fun p : Ω × W => ∫ σ : J → T, G_off j p σ ∂(Measure.pi fun _ : J => ν p))
      (P₀.prod γ_sh) :=
    integrable_integral_pi_last_split_of_bound t v hu.measurable (fun x => hu.le x) (hGm_off j)
      (K := |C_f| * |D| ^ 2) fun p σ => by
        dsimp only [G_off]
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one,
          mul_one, mul_one, sq, mul_assoc]
        exact mul_le_mul ((hfb _ _).trans (le_abs_self _))
          (mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self _))
            ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hI_fresh : Integrable
      (fun p : Ω × W => ∫ σ : Option J → T, G_fresh p σ ∂(Measure.pi fun _ : Option J => ν p))
      (P₀.prod γ_sh) :=
    integrable_integral_pi_last_split_of_bound t v hu.measurable (fun x => hu.le x) hGm_fresh
      (K := |C_f| * |D| ^ 2) fun p σ => by
        dsimp only [G_fresh]
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one,
          mul_one, mul_one, sq, mul_assoc]
        exact mul_le_mul ((hfb _ _).trans (le_abs_self _))
          (mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self _))
            ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : Ω → ℝ, ∀ ω₀, L₀ ω₀ =
      ∫ w, ∫ σ : J → T, G_lhs (ω₀, w) σ ∂(Measure.pi fun _ : J => ν (ω₀, w)) ∂γ_sh :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨O₀, hO₀⟩ : ∃ O₀ : J → Ω → ℝ, ∀ j ω₀, O₀ j ω₀ =
      ∫ w, ∫ σ : J → T, G_off j (ω₀, w) σ ∂(Measure.pi fun _ : J => ν (ω₀, w)) ∂γ_sh :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Ω → ℝ, ∀ ω₀, F₀ ω₀ =
      ∫ w, ∫ σ : Option J → T, G_fresh (ω₀, w) σ
        ∂(Measure.pi fun _ : Option J => ν (ω₀, w)) ∂γ_sh :=
    ⟨_, fun _ => rfl⟩
  have hO_int (j : J) : Integrable (O₀ j) P₀ := by
    have := (hI_off j).integral_prod_left
    simpa only [← hO₀ j] using this
  have hF_int : Integrable F₀ P₀ := by
    have := hI_fresh.integral_prod_left
    simpa only [← hF₀] using this
  have ht_lhs := integral_pi_last_split_eq_smartPath hu.measurable (fun x => hu.le x) t v
    (G := G_lhs) hGm_lhs
  have ht_off (j : J) := integral_pi_last_split_eq_smartPath hu.measurable (fun x => hu.le x) t v
    (G := G_off j) (hGm_off j)
  have ht_fresh := integral_pi_last_split_eq_smartPath hu.measurable (fun x => hu.le x) t v
    (G := G_fresh) hGm_fresh
  have heq_lhs :
      (∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f_ext ω σ * S' ω (σ ℓ) * deriv u (smartPathField t ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : J => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P) =
      ∫ ω₀, L₀ ω₀ ∂P₀ := by
    simp_rw [hL₀]
    rw [← integral_prod _ hI_lhs, ht_lhs]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [G_lhs, f_ext, S', Wt, W_sh, W_aux, S, α_sh, α_aux]
    have hWt_eq :
        (Sum.elim (0 : Fin N → ℝ) (fun _ : Unit =>
            (((σ ℓ).1.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t))) ⬝ᵥ
          Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
        (fun _ : Unit => -1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) ⬝ᵥ
          (fun _ : Unit => (σ ℓ).2 (Fin.last M)) =
        (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
          (ω.1.2 (Fin.last M) * (((σ ℓ).1.2 : ℤ) : ℝ) / Real.sqrt t -
            (σ ℓ).2 (Fin.last M) / Real.sqrt (1 - t)) := by
      rw [sumElim_dotProduct_sumElim, zero_dotProduct, zero_add]
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      ring
    have hS_fl :
        cavityCoef N t (σ ℓ).1 ⬝ᵥ
          Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
        (fun _ : Unit => Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ
          (fun _ : Unit => (σ ℓ).2 (Fin.last M)) =
        smartPathField t ω (σ ℓ) (Fin.last M) := by
      rw [smartPathField_last_eq_dotProduct (t := t) ω (σ ℓ)]; simp [dotProduct]
    rw [hWt_eq, hS_fl]
  have heq_off (j : J) :
      (∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f_ext ω σ * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ ℓ) (Fin.last M)) *
          deriv u (smartPathField t ω (σ j) (Fin.last M))
        ∂(Measure.pi fun _ : J => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P) =
      ∫ ω₀, O₀ j ω₀ ∂P₀ := by
    simp_rw [hO₀ j]
    rw [← integral_prod _ (hI_off j), ht_off j]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [G_off, f_ext, S, α_sh, α_aux]
    have hS_fl (r : J) :
        cavityCoef N t (σ r).1 ⬝ᵥ
          Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
        (fun _ : Unit => Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ
          (fun _ : Unit => (σ r).2 (Fin.last M)) =
        smartPathField t ω (σ r) (Fin.last M) := by
      rw [smartPathField_last_eq_dotProduct (t := t) ω (σ r)]; simp [dotProduct]
    rw [hS_fl ℓ, hS_fl j]
  have heq_fresh :
      (∫ ω, ∫ σ : Option J → SmartPathState N (M + 1),
        f_ext ω (fun r => σ (some r)) *
          (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (smartPathField t ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option J =>
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) ∂P) =
      ∫ ω₀, F₀ ω₀ ∂P₀ := by
    simp_rw [hF₀]
    rw [← integral_prod _ hI_fresh, ht_fresh]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [G_fresh, f_ext, S, α_sh, α_aux]
    have hS_fl (r : Option J) :
        cavityCoef N t (σ r).1 ⬝ᵥ
          Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
        (fun _ : Unit => Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ
          (fun _ : Unit => (σ r).2 (Fin.last M)) =
        smartPathField t ω (σ r) (Fin.last M) := by
      rw [smartPathField_last_eq_dotProduct (t := t) ω (σ r)]; simp [dotProduct]
    rw [hS_fl (some ℓ), hS_fl none]
  rw [heq_lhs, Finset.sum_congr rfl fun j _ => heq_off j, heq_fresh]
  have hpt (ω₀ : Ω) : L₀ ω₀ =
      (1 / (2 * (N + 1))) *
        ((∑ j ∈ Finset.univ.erase ℓ, O₀ j ω₀) - (Fintype.card J : ℝ) * F₀ ω₀) := by
    rw [hL₀]
    simp_rw [hO₀, hF₀]
    exact stein_cavity_last_constraint_split ht hu ω₀ ℓ (hfi ω₀)
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrable_finsetSum _ fun j _ => hO_int j)
    (hF_int.const_mul _), integral_finsetSum _ fun j _ => hO_int j, integral_const_mul]

/-- **Exercise 2.3.3, one-step Stein formula for any constraint `k` (spin-only observable).**
Derived from the last-constraint formula by row-swap invariance of the i.i.d. Gaussian rows. -/
theorem integral_smartPathFieldDeriv_mul_deriv_constraint
    {N M : ℕ} {J : Type uJ} [Fintype J] [DecidableEq J]
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (v : ℝ≥0) (k : Fin (M + 1)) (ℓ : J)
    (f : (J → PerceptronSpin N) → ℝ) :
    let P := smartPathDisorder
      (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    let μ (ω : SmartPathDisorder N (M + 1)) :=
      (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
    let S' (ω : SmartPathDisorder N (M + 1)) (x : SmartPathState N (M + 1)) : ℝ :=
      (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t - x.2 k / Real.sqrt (1 - t))
    ∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * S' ω (σ ℓ) * deriv u (smartPathField t ω (σ ℓ) k)
        ∂(Measure.pi fun _ : J => μ ω) ∂P =
      (1 / (2 * (N + 1))) *
        ((∑ j ∈ Finset.univ.erase ℓ,
          ∫ ω, ∫ σ : J → SmartPathState N (M + 1),
            f (fun r => (σ r).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
              deriv u (smartPathField t ω (σ ℓ) k) * deriv u (smartPathField t ω (σ j) k)
            ∂(Measure.pi fun _ : J => μ ω) ∂P) -
        (Fintype.card J : ℝ) *
          ∫ ω, ∫ σ : Option J → SmartPathState N (M + 1),
            f (fun r => (σ (some r)).1) *
              (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
              deriv u (smartPathField t ω (σ (some ℓ)) k) *
              deriv u (smartPathField t ω (σ none) k)
            ∂(Measure.pi fun _ : Option J => μ ω) ∂P) := by
  intro P μ S'
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  let fJ (_ : SmartPathDisorder N M) (a : J → SmartPathState N M) : ℝ := f (fun r => (a r).1)
  have hfJ_m : Measurable fun p : SmartPathDisorder N M × (J → SmartPathState N M) => fJ p.1 p.2 :=
    (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
      measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
  have hlast := integral_smartPathFieldDeriv_mul_deriv_last ht hu v ℓ hfJ_m (fun _ a => hCf _)
  dsimp only [fJ] at hlast
  -- Relate row `k` to `Fin.last M` via `smartPathDisorderSwap` and `smartPathStateSwap`.
  have hP_swap : MeasurePreserving (smartPathDisorderSwap (N := N) k (Fin.last M)) P P :=
    measurePreserving_smartPathDisorderSwap v k (Fin.last M)
      (measurePreserving_pi_comp_injective
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)
        (Equiv.swap k (Fin.last M)).injective).map_eq
  have hμ_prob (ω : SmartPathDisorder N (M + 1)) : IsProbabilityMeasure (μ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  have hμ_swap (ω : SmartPathDisorder N (M + 1)) :
      μ (smartPathDisorderSwap k (Fin.last M) ω) =
        (μ ω).map (smartPathStateSwap k (Fin.last M)) :=
    tilted_swap hu.measurable t k (Fin.last M)
      (measurePreserving_smartPathStateSwap k (Fin.last M)) ω
  -- Helper to swap any replica integral!
  have hswap_int {ι : Type uJ} [Fintype ι]
      (H : SmartPathDisorder N (M + 1) → (ι → SmartPathState N (M + 1)) → ℝ)
      (hHm : Measurable fun p : SmartPathDisorder N (M + 1) × (ι → SmartPathState N (M + 1)) =>
        H p.1 p.2)
      (H' : SmartPathDisorder N (M + 1) → (ι → SmartPathState N (M + 1)) → ℝ)
      (hH_eq : ∀ ω σ, H (smartPathDisorderSwap k (Fin.last M) ω)
        (fun r => smartPathStateSwap k (Fin.last M) (σ r)) = H' ω σ) :
      ∫ ω, ∫ σ : ι → SmartPathState N (M + 1), H ω σ ∂(Measure.pi fun _ : ι => μ ω) ∂P =
      ∫ ω, ∫ σ : ι → SmartPathState N (M + 1), H' ω σ ∂(Measure.pi fun _ : ι => μ ω) ∂P := by
    let I (ω : SmartPathDisorder N (M + 1)) :=
      ∫ σ : ι → SmartPathState N (M + 1), H ω σ ∂(Measure.pi fun _ : ι => μ ω)
    have hIm : Measurable I := measurable_integral_pi_tilted
      (measurable_smartPathEnergy hu.measurable t) hHm
    rw [← hP_swap.integral_comp_of_aestronglyMeasurable hIm.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    dsimp only [I]
    rw [hμ_swap ω, integral_pi_map_equiv (μ ω) (smartPathStateSwap k (Fin.last M))]
    exact integral_congr_ae (ae_of_all _ fun σ => hH_eq ω σ)
  -- Apply hswap_int to LHS, RHS j, and RHS fresh of `hlast`!
  have h1 :
      (∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f (fun r => (σ r).1) *
          ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (ω.1.2 (Fin.last M) * (((σ ℓ).1.2 : ℤ) : ℝ) / Real.sqrt t -
              (σ ℓ).2 (Fin.last M) / Real.sqrt (1 - t))) *
          deriv u (smartPathField t ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : J => μ ω) ∂P) =
      ∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * S' ω (σ ℓ) * deriv u (smartPathField t ω (σ ℓ) k)
        ∂(Measure.pi fun _ : J => μ ω) ∂P := by
    refine hswap_int _ ?_ _ fun ω σ => ?_
    · have hf1 : Measurable fun p : SmartPathDisorder N (M + 1) × (J → SmartPathState N (M + 1)) =>
          f (fun r => (p.2 r).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      have hpℓ : Measurable fun p : SmartPathDisorder N (M + 1) × (J → SmartPathState N (M + 1)) =>
          (p.1, p.2 ℓ) :=
        measurable_fst.prodMk ((measurable_pi_apply ℓ).comp measurable_snd)
      have hfl := (measurable_smartPathField (N := N) (M := M + 1) t (Fin.last M)).comp hpℓ
      have hS'm : Measurable fun p : SmartPathDisorder N (M + 1) × (J → SmartPathState N (M + 1)) =>
          (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            (p.1.1.2 (Fin.last M) * (((p.2 ℓ).1.2 : ℤ) : ℝ) / Real.sqrt t -
              (p.2 ℓ).2 (Fin.last M) / Real.sqrt (1 - t)) := by fun_prop
      exact (hf1.mul hS'm).mul ((measurable_deriv u).comp hfl)
    · have hfl := smartPathField_swap t k (Fin.last M) ω
        (smartPathStateSwap k (Fin.last M) (σ ℓ)) (Fin.last M)
      rw [smartPathStateSwap_swap, Equiv.swap_apply_right] at hfl
      dsimp only
      rw [hfl]
      simp [S', smartPathDisorderSwap, smartPathStateSwap_apply]
  have h2 (j : J) :
      (∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ ℓ) (Fin.last M)) *
          deriv u (smartPathField t ω (σ j) (Fin.last M))
        ∂(Measure.pi fun _ : J => μ ω) ∂P) =
      ∫ ω, ∫ σ : J → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ ℓ) k) * deriv u (smartPathField t ω (σ j) k)
        ∂(Measure.pi fun _ : J => μ ω) ∂P := by
    refine hswap_int _ ?_ _ fun ω σ => ?_
    · have hf1 : Measurable fun p : SmartPathDisorder N (M + 1) × (J → SmartPathState N (M + 1)) =>
          f (fun r => (p.2 r).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      have hp (r : J) :
          Measurable fun p : SmartPathDisorder N (M + 1) × (J → SmartPathState N (M + 1)) =>
            (p.1, p.2 r) :=
        measurable_fst.prodMk ((measurable_pi_apply r).comp measurable_snd)
      have hfl (r : J) := (measurable_smartPathField (N := N) (M := M + 1) t (Fin.last M)).comp
        (hp r)
      have hdu := measurable_deriv u
      fun_prop
    · have hfl (r : J) : smartPathField t (smartPathDisorderSwap k (Fin.last M) ω)
          (smartPathStateSwap k (Fin.last M) (σ r)) (Fin.last M) =
          smartPathField t ω (σ r) k := by
        have h := smartPathField_swap t k (Fin.last M) ω
          (smartPathStateSwap k (Fin.last M) (σ r)) (Fin.last M)
        rw [smartPathStateSwap_swap, Equiv.swap_apply_right] at h
        exact h
      dsimp only
      rw [hfl ℓ, hfl j]
      simp [smartPathStateSwap_apply]
  have h3 :
      (∫ ω, ∫ σ : Option J → SmartPathState N (M + 1),
        f (fun r => (σ (some r)).1) *
          (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (smartPathField t ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option J => μ ω) ∂P) =
      ∫ ω, ∫ σ : Option J → SmartPathState N (M + 1),
        f (fun r => (σ (some r)).1) *
          (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some ℓ)) k) *
          deriv u (smartPathField t ω (σ none) k)
        ∂(Measure.pi fun _ : Option J => μ ω) ∂P := by
    refine hswap_int _ ?_ _ fun ω σ => ?_
    · have hf1 :
          Measurable fun p : SmartPathDisorder N (M + 1) × (Option J → SmartPathState N (M + 1)) =>
            f (fun r => (p.2 (some r)).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))
      have hp (r : Option J) :
          Measurable fun p : SmartPathDisorder N (M + 1) × (Option J → SmartPathState N (M + 1)) =>
            (p.1, p.2 r) :=
        measurable_fst.prodMk ((measurable_pi_apply r).comp measurable_snd)
      have hfl (r : Option J) :=
        (measurable_smartPathField (N := N) (M := M + 1) t (Fin.last M)).comp (hp r)
      have hdu := measurable_deriv u
      fun_prop
    · have hfl (r : Option J) : smartPathField t (smartPathDisorderSwap k (Fin.last M) ω)
          (smartPathStateSwap k (Fin.last M) (σ r)) (Fin.last M) =
          smartPathField t ω (σ r) k := by
        have h := smartPathField_swap t k (Fin.last M) ω
          (smartPathStateSwap k (Fin.last M) (σ r)) (Fin.last M)
        rw [smartPathStateSwap_swap, Equiv.swap_apply_right] at h
        exact h
      dsimp only
      rw [hfl (some ℓ), hfl none]
      simp [smartPathStateSwap_apply]
  rw [← h1, ← Finset.sum_congr rfl fun j _ => h2 j, ← h3]
  exact hlast

/-- **Exercise 2.3.3, recovery of term I of (2.23)--(2.24) in one step.**
Summing the one-step formula over `ℓ ∈ R` and subtracting `|R|` times the fresh-replica `Option R`
case yields `(1 / (N + 1))` times the expected `replicaPairAverage` of `smartPathPotentialKernel`
without separate integrations by parts in `a_M` and `ξ_M`. Multiplying by `M + 1` gives the load
factor `α = (M + 1) / (N + 1)` of term I. -/
theorem smartPath_one_step_recovery_last
    {N M : ℕ} {R : Type uJ} [Fintype R] [LinearOrder R]
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (v : ℝ≥0) (f : (R → PerceptronSpin N) → ℝ) :
    let P := smartPathDisorder
      (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin N => gaussianReal 0 1) v
    let μ (ω : SmartPathDisorder N (M + 1)) :=
      (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
    let S' (ω : SmartPathDisorder N (M + 1)) (x : SmartPathState N (M + 1)) : ℝ :=
      (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 (Fin.last M) * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t -
          x.2 (Fin.last M) / Real.sqrt (1 - t))
    (∑ ℓ : R, ∫ ω, ∫ σ : R → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * S' ω (σ ℓ) * deriv u (smartPathField t ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω) ∂P) -
      (Fintype.card R : ℝ) *
        ∫ ω, ∫ σ : Option R → SmartPathState N (M + 1),
          f (fun r => (σ (some r)).1) * S' ω (σ none) *
            deriv u (smartPathField t ω (σ none) (Fin.last M))
          ∂(Measure.pi fun _ : Option R => μ ω) ∂P =
      (1 / (N + 1)) * ∫ ω, replicaPairAverage (μ ω)
        (fun σ : R → SmartPathState N (M + 1) => f (fun r => (σ r).1))
        (smartPathPotentialKernel u t ω (Fin.last M)) ∂P := by
  intro P μ S'
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  let fR (_ : SmartPathDisorder N M) (a : R → SmartPathState N M) : ℝ := f (fun r => (a r).1)
  have hfR_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => fR p.1 p.2 :=
    (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
      measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
  have h1 (ℓ : R) := integral_smartPathFieldDeriv_mul_deriv_last ht hu v ℓ hfR_m
    (fun _ a => hCf _)
  let fO (_ : SmartPathDisorder N M) (a : Option R → SmartPathState N M) : ℝ :=
    f (fun r => (a (some r)).1)
  have hfO_m :
      Measurable fun p : SmartPathDisorder N M × (Option R → SmartPathState N M) => fO p.1 p.2 :=
    (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
      measurable_fst.comp ((measurable_pi_apply (some r)).comp measurable_snd))
  have h2 := integral_smartPathFieldDeriv_mul_deriv_last ht hu v (none : Option R) hfO_m
    (fun _ a => hCf _)
  have h1' (ℓ : R) :
      (∫ ω, ∫ σ : R → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * S' ω (σ ℓ) * deriv u (smartPathField t ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω) ∂P) = _ := h1 ℓ
  have h2' :
      (∫ ω, ∫ σ : Option R → SmartPathState N (M + 1),
        f (fun r => (σ (some r)).1) * S' ω (σ none) *
          deriv u (smartPathField t ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option R => μ ω) ∂P) = _ := h2
  rw [Finset.sum_congr rfl fun ℓ _ => h1' ℓ, h2']
  let U (ω : SmartPathDisorder N (M + 1)) := smartPathPotentialKernel u t ω (Fin.last M)
  have hU_symm (ω : SmartPathDisorder N (M + 1)) (a b : SmartPathState N (M + 1)) :
      U ω a b = U ω b a := by
    simp only [U, smartPathPotentialKernel_eq]; ring
  have hμ_prob (ω : SmartPathDisorder N (M + 1)) : IsProbabilityMeasure (μ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  have hP_prob : IsProbabilityMeasure P := by dsimp [P]; rw [smartPathDisorder_eq]; infer_instance
  let e₂ : R → Option (Option R) := fun r => some (some r)
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp (Option.some_injective _)
  let e₁ : Option R → Option (Option R) := some
  have he₁ : Function.Injective e₁ := Option.some_injective _
  let Φ (i j : Option (Option R)) (ω : SmartPathDisorder N (M + 1))
      (τ : Option (Option R) → SmartPathState N (M + 1)) : ℝ :=
    f (fun r => (τ (some (some r))).1) * U ω (τ i) (τ j)
  let T_pair (i j : Option (Option R)) (ω : SmartPathDisorder N (M + 1)) : ℝ :=
    ∫ τ : Option (Option R) → SmartPathState N (M + 1), Φ i j ω τ
      ∂(Measure.pi fun _ : Option (Option R) => μ ω)
  have hΦm (i j : Option (Option R)) : Measurable fun p : SmartPathDisorder N (M + 1) ×
      (Option (Option R) → SmartPathState N (M + 1)) => Φ i j p.1 p.2 := by
    have hf2 : Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) =>
        f (fun r => (p.2 (some (some r))).1) :=
      (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (some (some r))).comp measurable_snd))
    have hpU : Measurable fun p : SmartPathDisorder N (M + 1) ×
        (Option (Option R) → SmartPathState N (M + 1)) => (p.1, (p.2 i, p.2 j)) :=
      measurable_fst.prodMk
        (((measurable_pi_apply i).comp measurable_snd).prodMk
          ((measurable_pi_apply j).comp measurable_snd))
    have hUm := (measurable_potentialKernel_joint (N := N) (M := M + 1) (u := u) t
      (Fin.last M)).comp hpU
    exact hf2.mul hUm
  have hΦb (i j : Option (Option R)) (ω : SmartPathDisorder N (M + 1))
      (τ : Option (Option R) → SmartPathState N (M + 1)) : |Φ i j ω τ| ≤ |C_f| * |D| ^ 2 := by
    dsimp only [Φ, U]
    rw [smartPathPotentialKernel_eq, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_units_cast_eq_one, abs_units_cast_eq_one, one_mul, one_mul, sq]
    exact mul_le_mul ((hCf _).trans (le_abs_self _))
      (mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self _))
        ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hT_int (i j : Option (Option R)) : Integrable (T_pair i j) P :=
    integrable_integral_pi_perceptron_smart_path hu.measurable (fun x => hu.le x) t
      (hΦm i j) (hΦb i j)
  have hΦ_int (i j : Option (Option R)) (ω : SmartPathDisorder N (M + 1)) :
      Integrable (Φ i j ω) (Measure.pi fun _ : Option (Option R) => μ ω) :=
    Integrable.of_bound
      ((hΦm i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (|C_f| * |D| ^ 2) (ae_of_all _ fun τ => by simpa using hΦb i j ω τ)
  have hlift_0 (ℓ j : R) (ω : SmartPathDisorder N (M + 1)) :
      (∫ σ : R → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ ℓ) (Fin.last M)) *
          deriv u (smartPathField t ω (σ j) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω)) =
      T_pair (some (some ℓ)) (some (some j)) ω := by
    have hm : Measurable fun σ : R → SmartPathState N (M + 1) =>
        f (fun r => (σ r).1) * U ω (σ ℓ) (σ j) := by
      have hfm : Measurable fun σ : R → SmartPathState N (M + 1) => f (fun r => (σ r).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp (measurable_pi_apply r))
      have hUm : Measurable fun σ : R → SmartPathState N (M + 1) => U ω (σ ℓ) (σ j) := by
        simp only [U, smartPathPotentialKernel_eq]
        have := measurable_deriv u
        have := measurable_smartPathField_slice t ω (Fin.last M)
        fun_prop
      exact hfm.mul hUm
    have hpt (σ : R → SmartPathState N (M + 1)) :
        f (fun r => (σ r).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ ℓ) (Fin.last M)) *
          deriv u (smartPathField t ω (σ j) (Fin.last M)) =
        f (fun r => (σ r).1) * U ω (σ ℓ) (σ j) := by
      dsimp only [U]; rw [smartPathPotentialKernel_eq]; ring
    simp_rw [hpt]
    exact (integral_pi_comp_injective (μ ω) he₂ _ hm.aestronglyMeasurable).symm
  have hlift_1 (ℓ : R) (ω : SmartPathDisorder N (M + 1)) :
      (∫ σ : Option R → SmartPathState N (M + 1),
        f (fun r => (σ (some r)).1) * (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (smartPathField t ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option R => μ ω)) =
      T_pair (some (some ℓ)) (some none) ω := by
    have hm : Measurable fun σ : Option R → SmartPathState N (M + 1) =>
        f (fun r => (σ (some r)).1) * U ω (σ (some ℓ)) (σ none) := by
      have hfm : Measurable fun σ : Option R → SmartPathState N (M + 1) =>
          f (fun r => (σ (some r)).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r =>
          measurable_fst.comp (measurable_pi_apply (some r)))
      have hUm : Measurable fun σ : Option R → SmartPathState N (M + 1) =>
          U ω (σ (some ℓ)) (σ none) := by
        simp only [U, smartPathPotentialKernel_eq]
        have := measurable_deriv u
        have := measurable_smartPathField_slice t ω (Fin.last M)
        fun_prop
      exact hfm.mul hUm
    have hpt (σ : Option R → SmartPathState N (M + 1)) :
        f (fun r => (σ (some r)).1) * (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (smartPathField t ω (σ none) (Fin.last M)) =
        f (fun r => (σ (some r)).1) * U ω (σ (some ℓ)) (σ none) := by
      dsimp only [U]; rw [smartPathPotentialKernel_eq]; ring
    simp_rw [hpt]
    exact (integral_pi_comp_injective (μ ω) he₁ _ hm.aestronglyMeasurable).symm
  have hlift_1' (j : R) (ω : SmartPathDisorder N (M + 1)) :
      (∫ σ : Option R → SmartPathState N (M + 1),
        f (fun r => (σ (some r)).1) * (((σ none).1.2 : ℤ) : ℝ) * (((σ (some j)).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ none) (Fin.last M)) *
          deriv u (smartPathField t ω (σ (some j)) (Fin.last M))
        ∂(Measure.pi fun _ : Option R => μ ω)) =
      T_pair (some (some j)) (some none) ω := by
    rw [← hlift_1 j ω]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    ring
  have hlift_2 (ω : SmartPathDisorder N (M + 1)) :
      (∫ σ : Option (Option R) → SmartPathState N (M + 1),
        f (fun r => (σ (some (some r))).1) *
          (((σ (some none)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some none)) (Fin.last M)) *
          deriv u (smartPathField t ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω)) =
      T_pair (some none) none ω := by
    dsimp only [T_pair, Φ, U]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp only
    rw [smartPathPotentialKernel_eq]
    ring
  -- Rewrite all the integrals on the LHS into integrals of T_pair!
  dsimp only [fR, fO]
  have hs0 (ℓ j : R) :
      (∫ ω, ∫ σ : R → SmartPathState N (M + 1),
        f (fun r => (σ r).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ ℓ) (Fin.last M)) *
          deriv u (smartPathField t ω (σ j) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω) ∂P) =
      ∫ ω, T_pair (some (some ℓ)) (some (some j)) ω ∂P :=
    integral_congr_ae (ae_of_all _ (hlift_0 ℓ j))
  have hs1 (ℓ : R) :
      (∫ ω, ∫ σ : Option R → SmartPathState N (M + 1),
        f (fun r => (σ (some r)).1) * (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (smartPathField t ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option R => μ ω) ∂P) =
      ∫ ω, T_pair (some (some ℓ)) (some none) ω ∂P :=
    integral_congr_ae (ae_of_all _ (hlift_1 ℓ))
  have hs2 :
      (∫ ω, ∫ σ : Option (Option R) → SmartPathState N (M + 1),
        f (fun r => (σ (some (some r))).1) *
          (((σ (some none)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (smartPathField t ω (σ (some none)) (Fin.last M)) *
          deriv u (smartPathField t ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P) =
      ∫ ω, T_pair (some none) none ω ∂P :=
    integral_congr_ae (ae_of_all _ hlift_2)
  have herase_opt :
      (∑ j ∈ (Finset.univ : Finset (Option R)).erase none,
        ∫ ω, ∫ σ : Option R → SmartPathState N (M + 1),
          f (fun r => (σ (some r)).1) * (((σ none).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
            deriv u (smartPathField t ω (σ none) (Fin.last M)) *
            deriv u (smartPathField t ω (σ j) (Fin.last M))
          ∂(Measure.pi fun _ : Option R => μ ω) ∂P) =
      ∑ r : R, ∫ ω, T_pair (some (some r)) (some none) ω ∂P := by
    have hmap : ((Finset.univ : Finset (Option R)).erase none) =
        Finset.univ.map ⟨Option.some, Option.some_injective R⟩ := by
      ext x; cases x <;> simp
    rw [hmap, Finset.sum_map]
    exact Finset.sum_congr rfl fun r _ => integral_congr_ae (ae_of_all _ (hlift_1' r))
  change (∑ ℓ : R, (1 / (2 * ((N : ℝ) + 1))) *
      ((∑ j ∈ Finset.univ.erase ℓ,
        ∫ ω, ∫ σ : R → SmartPathState N (M + 1),
          f (fun r => (σ r).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
            deriv u (smartPathField t ω (σ ℓ) (Fin.last M)) *
            deriv u (smartPathField t ω (σ j) (Fin.last M))
          ∂(Measure.pi fun _ : R => μ ω) ∂P) -
      (Fintype.card R : ℝ) *
        ∫ ω, ∫ σ : Option R → SmartPathState N (M + 1),
          f (fun r => (σ (some r)).1) * (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
            deriv u (smartPathField t ω (σ (some ℓ)) (Fin.last M)) *
            deriv u (smartPathField t ω (σ none) (Fin.last M))
          ∂(Measure.pi fun _ : Option R => μ ω) ∂P)) -
    (Fintype.card R : ℝ) * ((1 / (2 * ((N : ℝ) + 1))) *
      ((∑ j ∈ (Finset.univ : Finset (Option R)).erase none,
        ∫ ω, ∫ σ : Option R → SmartPathState N (M + 1),
          f (fun r => (σ (some r)).1) * (((σ none).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
            deriv u (smartPathField t ω (σ none) (Fin.last M)) *
            deriv u (smartPathField t ω (σ j) (Fin.last M))
          ∂(Measure.pi fun _ : Option R => μ ω) ∂P) -
      (Fintype.card (Option R) : ℝ) *
        ∫ ω, ∫ σ : Option (Option R) → SmartPathState N (M + 1),
          f (fun r => (σ (some (some r))).1) *
            (((σ (some none)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
            deriv u (smartPathField t ω (σ (some none)) (Fin.last M)) *
            deriv u (smartPathField t ω (σ none) (Fin.last M))
          ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P)) = _
  simp_rw [hs0, hs1, herase_opt, hs2]
  -- Now pull sums and scalar multiplications inside ∫ ω ∂P and ∫ τ ∂(Measure.pi μ ω)!
  have hpull_ω (ℓ : R) :
      (∑ j ∈ Finset.univ.erase ℓ, ∫ ω, T_pair (some (some ℓ)) (some (some j)) ω ∂P) -
        (Fintype.card R : ℝ) * ∫ ω, T_pair (some (some ℓ)) (some none) ω ∂P =
      ∫ ω, ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
        (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω) ∂P := by
    rw [integral_sub (integrable_finsetSum _ fun j _ => hT_int _ _)
      ((hT_int _ _).const_mul _), integral_finsetSum _ fun j _ => hT_int _ _, integral_const_mul]
  have hpull_opt :
      (∑ r : R, ∫ ω, T_pair (some (some r)) (some none) ω ∂P) -
        (Fintype.card (Option R) : ℝ) * ∫ ω, T_pair (some none) none ω ∂P =
      ∫ ω, ((∑ r : R, T_pair (some (some r)) (some none) ω) -
        (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) ∂P := by
    rw [integral_sub (integrable_finsetSum _ fun r _ => hT_int _ _)
      ((hT_int _ _).const_mul _), integral_finsetSum _ fun r _ => hT_int _ _, integral_const_mul]
  simp_rw [hpull_ω, hpull_opt, ← Finset.mul_sum]
  have hI_sum : Integrable (fun ω => ∑ ℓ : R,
      ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
        (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω)) P :=
    integrable_finsetSum _ fun ℓ _ =>
      (integrable_finsetSum _ fun j _ => hT_int _ _).sub ((hT_int _ _).const_mul _)
  have hI_opt2 : Integrable (fun ω =>
      (∑ r : R, T_pair (some (some r)) (some none) ω) -
        (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) P :=
    (integrable_finsetSum _ fun r _ => hT_int _ _).sub ((hT_int _ _).const_mul _)
  rw [← integral_finsetSum Finset.univ (f := fun (ℓ : R) (ω : SmartPathDisorder N (M + 1)) =>
    (∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
      (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω) fun ℓ _ =>
    (integrable_finsetSum _ fun j _ => hT_int _ _).sub ((hT_int _ _).const_mul _)]
  have hcomb_outer :
      (1 / (2 * ((N : ℝ) + 1))) * ∫ ω, (∑ ℓ : R,
        ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
          (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω)) ∂P -
      (Fintype.card R : ℝ) * ((1 / (2 * ((N : ℝ) + 1))) * ∫ ω,
        ((∑ r : R, T_pair (some (some r)) (some none) ω) -
          (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) ∂P) =
      (1 / ((N : ℝ) + 1)) * ∫ ω, (1 / 2) *
        ((∑ ℓ : R, ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
          (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω)) -
        (Fintype.card R : ℝ) * ((∑ r : R, T_pair (some (some r)) (some none) ω) -
          (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω)) ∂P := by
    have hsub_eq := integral_sub hI_sum (hI_opt2.const_mul (Fintype.card R : ℝ))
    have hmul_eq := integral_const_mul (Fintype.card R : ℝ)
      (fun ω => (∑ r : R, T_pair (some (some r)) (some none) ω) -
        (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) (μ := P)
    rw [integral_const_mul (1 / 2), hsub_eq, hmul_eq]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    field_simp
  rw [hcomb_outer]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only [T_pair]
  -- Pull sums inside ∫ τ ∂(Measure.pi μ ω)!
  have hp_in1 (ℓ : R) :
      (∑ j ∈ Finset.univ.erase ℓ,
        ∫ τ, Φ (some (some ℓ)) (some (some j)) ω τ ∂(Measure.pi fun _ => μ ω)) -
      (Fintype.card R : ℝ) *
        ∫ τ, Φ (some (some ℓ)) (some none) ω τ ∂(Measure.pi fun _ => μ ω) =
      ∫ τ, ((∑ j ∈ Finset.univ.erase ℓ, Φ (some (some ℓ)) (some (some j)) ω τ) -
        (Fintype.card R : ℝ) * Φ (some (some ℓ)) (some none) ω τ) ∂(Measure.pi fun _ => μ ω) := by
    rw [integral_sub (integrable_finsetSum _ fun j _ => hΦ_int _ _ ω)
      ((hΦ_int _ _ ω).const_mul _), integral_finsetSum _ fun j _ => hΦ_int _ _ ω,
      integral_const_mul]
  have hp_in2 :
      (∑ r : R, ∫ τ, Φ (some (some r)) (some none) ω τ ∂(Measure.pi fun _ => μ ω)) -
      (Fintype.card (Option R) : ℝ) *
        ∫ τ, Φ (some none) none ω τ ∂(Measure.pi fun _ => μ ω) =
      ∫ τ, ((∑ r : R, Φ (some (some r)) (some none) ω τ) -
        (Fintype.card (Option R) : ℝ) * Φ (some none) none ω τ) ∂(Measure.pi fun _ => μ ω) := by
    rw [integral_sub (integrable_finsetSum _ fun r _ => hΦ_int _ _ ω)
      ((hΦ_int _ _ ω).const_mul _), integral_finsetSum _ fun r _ => hΦ_int _ _ ω,
      integral_const_mul]
  simp_rw [hp_in1, hp_in2]
  have hΦ_sum : Integrable (fun τ => ∑ ℓ : R,
      ((∑ j ∈ Finset.univ.erase ℓ, Φ (some (some ℓ)) (some (some j)) ω τ) -
        (Fintype.card R : ℝ) * Φ (some (some ℓ)) (some none) ω τ))
      (Measure.pi fun _ => μ ω) :=
    integrable_finsetSum _ fun ℓ _ =>
      (integrable_finsetSum _ fun j _ => hΦ_int _ _ ω).sub ((hΦ_int _ _ ω).const_mul _)
  have hΦ_opt2 : Integrable (fun τ =>
      (∑ r : R, Φ (some (some r)) (some none) ω τ) -
        (Fintype.card (Option R) : ℝ) * Φ (some none) none ω τ)
      (Measure.pi fun _ => μ ω) :=
    (integrable_finsetSum _ fun r _ => hΦ_int _ _ ω).sub ((hΦ_int _ _ ω).const_mul _)
  rw [← integral_finsetSum Finset.univ (f := fun (ℓ : R) τ =>
    (∑ j ∈ Finset.univ.erase ℓ, Φ (some (some ℓ)) (some (some j)) ω τ) -
      (Fintype.card R : ℝ) * Φ (some (some ℓ)) (some none) ω τ) fun ℓ _ =>
    (integrable_finsetSum _ fun j _ => hΦ_int _ _ ω).sub ((hΦ_int _ _ ω).const_mul _)]
  rw [← integral_const_mul (Fintype.card R : ℝ),
    ← integral_sub hΦ_sum (hΦ_opt2.const_mul _),
    ← integral_const_mul (1 / 2), replicaPairAverage_eq]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  dsimp only [Φ]
  have hoff_sum :
      ∑ ℓ : R, ∑ j ∈ Finset.univ.erase ℓ, U ω (τ (some (some ℓ))) (τ (some (some j))) =
      2 * ∑ p : R × R with p.1 < p.2, U ω (τ (some (some p.1))) (τ (some (some p.2))) := by
    have h1_eq :
        (∑ ℓ : R, ∑ j ∈ Finset.univ.erase ℓ, U ω (τ (some (some ℓ))) (τ (some (some j)))) =
        ∑ ℓ : R, ∑ j : R, if ℓ = j then 0 else U ω (τ (some (some ℓ))) (τ (some (some j))) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [← Finset.add_sum_erase Finset.univ
        (fun j => if ℓ = j then 0 else U ω (τ (some (some ℓ))) (τ (some (some j))))
        (Finset.mem_univ ℓ)]
      simp only [↓reduceIte, zero_add]
      exact Finset.sum_congr rfl fun j hj => by simp [(Finset.ne_of_mem_erase hj).symm]
    rw [h1_eq]
    exact sum_sum_offDiag_eq_two_sum_lt
      (fun r r' => U ω (τ (some (some r))) (τ (some (some r')))) (fun _ _ => hU_symm ω _ _)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Fintype.card_option,
    Nat.cast_succ, replicaPairCombination_eq, hoff_sum]
  ring

end OneStepStein

end SpinGlasses
