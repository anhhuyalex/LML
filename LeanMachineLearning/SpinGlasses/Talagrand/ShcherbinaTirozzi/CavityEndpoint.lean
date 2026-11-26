/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExchangeableCoordinates
public import LeanMachineLearning.ForMathlib.Analysis.Convex.LogConcaveMarginal
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaEquivariance
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.Convexity

/-!
# The Shcherbina--Tirozzi model: the cavity path and its decoupled endpoint

The cavity Hamiltonian (3.61) on `ℝ^(N+1)` interpolates between the model (3.1) at `t = 1` and a
system at `t = 0` in which the last spin `ε` is decoupled from the others. Together with the
symmetry between sites this gives Proposition 3.2.4 of Talagrand, *Spin Glasses*, Vol. I:
`ρ = ν (ε²)` and `q = ν (⟨ε⟩²)` at `t = 1`, while at `t = 0` these two averages are
`1 / a + (r + h²) / a²` and `(r + h²) / a²` with `a = 2 κ + r - r̄`.

## Main declarations

* `SpinGlasses.shcherbinaTirozziCavityHamiltonian`: the Hamiltonian (3.61).
* `SpinGlasses.shcherbinaTirozziGibbs_comp_perm` and
  `SpinGlasses.integral_shcherbinaTirozziGibbs_comp_perm`: symmetry between sites.
* `SpinGlasses.integral_shcherbinaTirozzi_overlaps_eq_last_spin`: `ρ = ν (ε²)` and
  `q = ν (⟨ε⟩²)`.
* `SpinGlasses.integral_shcherbinaTirozziCavityGibbs_zero_last`: at `t = 0` the last spin has
  density proportional to `exp ((h g_N + y) ε - a ε² / 2)`.
* `SpinGlasses.integral_integral_shcherbinaTirozziCavityGibbs_zero_sq_last` and
  `SpinGlasses.integral_integral_sq_shcherbinaTirozziCavityGibbs_zero_last`: Eqs. (3.78)--(3.80).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace NNReal

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {N M : ℕ}

/-- **The cavity Hamiltonian (3.61)** on `ℝ^(N+1)`: the coupling of the last spin to the
constraints is multiplied by `√t`, and the field `√(1-t) y ε` and the term
`-(1-t) (r - r̄) ε² / 2` are added to `-H`. -/
noncomputable def shcherbinaTirozziCavityHamiltonian (κ h r rBar t y : ℝ) (u : ℝ → ℝ)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) : ℝ :=
  κ * ‖σ‖ ^ 2 -
    ∑ k, u ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
      Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))) -
    h * ∑ i, g₀ i * σ i - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
    (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2

/-- At `t = 1` the cavity Hamiltonian is the Hamiltonian (3.1) of the model with `N + 1`
spins. -/
theorem shcherbinaTirozziCavityHamiltonian_one (κ h r rBar y : ℝ) (u : ℝ → ℝ)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) :
    shcherbinaTirozziCavityHamiltonian κ h r rBar 1 y u g g₀ σ =
      shcherbinaTirozziHamiltonian κ h u g g₀ σ := by
  simp only [shcherbinaTirozziCavityHamiltonian, shcherbinaTirozziHamiltonian, Real.sqrt_one,
    one_mul, sub_self, Real.sqrt_zero, zero_mul, mul_zero, zero_div, sub_zero, add_zero,
    Fin.sum_univ_castSucc (fun i => g _ i * σ i), Nat.cast_add, Nat.cast_one]

/-- At `t = 0` the last spin is decoupled: `-H` is the sum of a function of the first `N` spins
and of `(h g_N + y) ε - (2 κ + r - r̄) ε² / 2`. -/
theorem neg_shcherbinaTirozziCavityHamiltonian_zero (κ h r rBar y : ℝ) (u : ℝ → ℝ)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) :
    -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u g g₀ σ =
      ((∑ k, u ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * σ i.castSucc)) -
          κ * (∑ i : Fin N, σ i.castSucc ^ 2) +
          h * ∑ i : Fin N, g₀ i.castSucc * σ i.castSucc) +
        ((h * g₀ (Fin.last N) + y) * σ (Fin.last N) -
          (2 * κ + r - rBar) * σ (Fin.last N) ^ 2 / 2) := by
  have hnorm : ‖σ‖ ^ 2 = (∑ i : Fin N, σ i.castSucc ^ 2) + σ (Fin.last N) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [shcherbinaTirozziCavityHamiltonian, Real.sqrt_zero, zero_mul, add_zero, sub_zero,
    Real.sqrt_one, one_mul, hnorm, Fin.sum_univ_castSucc (fun i => g₀ i * σ i)]
  ring

/-- **The decoupled last spin** (Talagrand, Eqs. (3.78)--(3.79)): for `κ > 0` and `u ≤ 0`, the
average at `t = 0` of a function of `ε` is its average for the density proportional to
`exp ((h g_N + y) ε - (2 κ + r - r̄) ε² / 2)`. -/
theorem integral_shcherbinaTirozziCavityGibbs_zero_last {κ h : ℝ} (hκ : 0 < κ) (r rBar y : ℝ)
    {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin (N + 1) → ℝ)
    (g₀ : Fin (N + 1) → ℝ) (Φ : ℝ → ℝ) :
    ∫ σ, Φ (σ (Fin.last N)) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u g g₀ σ) =
      ∫ x, Φ x ∂((volume : Measure ℝ).tilted fun x =>
        (h * g₀ (Fin.last N) + y) * x - (2 * κ + r - rBar) * x ^ 2 / 2) := by
  set A : ℝ → ℝ := fun x =>
    (h * g₀ (Fin.last N) + y) * x - (2 * κ + r - rBar) * x ^ 2 / 2 with hA
  set B : (Fin N → ℝ) → ℝ := fun ρ =>
    (∑ k, u ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i)) -
      κ * (∑ i, ρ i ^ 2) + h * ∑ i : Fin N, g₀ i.castSucc * ρ i with hB
  -- split the configuration into the last spin and the others
  set e : ℝ^(N + 1) ≃ᵐ ℝ × (Fin N → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (N + 1) → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last N)) with he
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).comp
      (PiLp.volume_preserving_ofLp (Fin (N + 1)))
  have he1 : ∀ σ, (e σ).1 = σ (Fin.last N) := fun σ => rfl
  have he2 : ∀ σ i, (e σ).2 i = σ i.castSucc := fun σ i => by
    change σ ((Fin.last N).succAbove i) = σ i.castSucc
    rw [Fin.succAbove_last]
  have hH : ∀ σ, -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u g g₀ σ =
      B (e σ).2 + A (e σ).1 := fun σ => by
    rw [neg_shcherbinaTirozziCavityHamiltonian_zero]
    simp only [hA, hB, he1, he2]
  -- the weight of the other spins has a positive finite integral
  have hBi : Integrable fun ρ => Real.exp (B ρ) := by
    have hU : Measurable fun v : ℝ^N =>
        ∑ k, u ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * v i) :=
      Finset.measurable_sum _ fun k _ => hu.comp ((Finset.measurable_sum _ fun i _ =>
        ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable).const_mul _).const_mul _)
    have h1 := integrable_exp_add_neg_mul_sq_norm_add_inner (E := ℝ^N) hU
      (fun v => Finset.sum_nonpos fun k _ => hu0 _) hκ
      (WithLp.toLp 2 fun i : Fin N => h * g₀ i.castSucc)
    have h2 := ((PiLp.volume_preserving_toLp (Fin N)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin N → ℝ)).measurableEmbedding).2 h1
    refine h2.congr (ae_of_all _ fun ρ => ?_)
    simp only [Function.comp_apply, hB, inner_toLp_inv_sqrt_mul_eq,
      EuclideanSpace.real_norm_sq_eq]
  have hBpos : 0 < ∫ ρ, Real.exp (B ρ) := integral_exp_pos hBi
  have htrans : ∀ f : ℝ → ℝ, ∫ σ, Real.exp
        (-shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u g g₀ σ) * f (σ (Fin.last N)) =
      (∫ x, Real.exp (A x) * f x) * ∫ ρ, Real.exp (B ρ) := fun f => by
    rw [← integral_prod_mul, ← hmp.integral_comp e.measurableEmbedding]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only [hH, Real.exp_add, he1]
    ring
  have hZ := htrans fun _ => 1
  simp only [mul_one] at hZ
  rw [integral_tilted, integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div]
  rw [htrans Φ, hZ, mul_div_mul_right _ _ hBpos.ne']

/-- **Symmetry between sites** for one realization of the disorder: permuting the disorder
amounts to permuting the configuration under the Gibbs measure. -/
theorem shcherbinaTirozziGibbs_comp_perm (κ h : ℝ) {u : ℝ → ℝ} (hu : Measurable u)
    (g : Fin M → Fin N → ℝ) (g₀ : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    (volume.tilted fun σ : ℝ^N =>
        -shcherbinaTirozziHamiltonian κ h u (fun k i => g k (π i)) (fun i => g₀ (π i)) σ) =
      (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ π).symm := by
  set T := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ π with hT
  have hTa : ∀ (σ : ℝ^N) i, T σ i = σ (π.symm i) := fun σ i => rfl
  have hH : ∀ σ : ℝ^N,
      shcherbinaTirozziHamiltonian κ h u (fun k i => g k (π i)) (fun i => g₀ (π i)) σ =
        shcherbinaTirozziHamiltonian κ h u g g₀ (T σ) := fun σ => by
    have hsum : ∀ a : Fin N → ℝ, ∑ i, a (π i) * σ i = ∑ i, a i * T σ i := fun a => by
      refine Fintype.sum_equiv π _ _ fun i => ?_
      rw [hTa, π.symm_apply_apply]
    simp only [shcherbinaTirozziHamiltonian, T.norm_map, hsum]
  have hm := map_tilted_measurableEquiv (μ := (volume : Measure (ℝ^N))) (ν := volume)
    T.symm.toHomeomorph.toMeasurableEquiv
    (e := fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) T.symm.measurePreserving
    (measurable_shcherbinaTirozziHamiltonian_apply κ h hu g g₀).neg
  have e1 : ⇑T.symm.toHomeomorph.toMeasurableEquiv = ⇑T.symm := rfl
  have e2 : (fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ∘
        T.symm.toHomeomorph.toMeasurableEquiv.symm =
      fun σ => -shcherbinaTirozziHamiltonian κ h u (fun k i => g k (π i))
        (fun i => g₀ (π i)) σ := funext fun σ => by
    rw [hH]
    rfl
  rw [e1, e2] at hm
  exact hm.symm

/-- **Symmetry between sites** after averaging over the disorder: the law of any quenched average
is unchanged when the observable is composed with a permutation of the sites. -/
theorem integral_shcherbinaTirozziGibbs_comp_perm (κ h : ℝ) {u : ℝ → ℝ} (hu : Measurable u)
    (π : Equiv.Perm (Fin N)) (Φ : ℝ^N → ℝ) (F : ℝ → ℝ) :
    ∀ P : Measure ((Fin M → Fin N → ℝ) × (Fin N → ℝ)),
      P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) →
      ∫ d, F (∫ σ, Φ σ ∂(volume.tilted fun σ =>
          -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ)) ∂P =
        ∫ d, F (∫ σ, Φ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ π).symm σ)
          ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ)) ∂P := by
  intro P hP
  set c : (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) π.symm with hc
  have hca : ∀ (a : Fin N → ℝ) i, c a i = a (π i) := fun a i => by
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin N => ℝ) π.symm a (π i)
    simpa only [hc, π.symm_apply_apply] using this
  have hcmp : MeasurePreserving c (Measure.pi fun _ : Fin N => gaussianReal 0 1)
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft (fun _ : Fin N => gaussianReal 0 1) π.symm
  set C : (Fin M → Fin N → ℝ) × (Fin N → ℝ) ≃ᵐ (Fin M → Fin N → ℝ) × (Fin N → ℝ) :=
    (MeasurableEquiv.piCongrRight fun _ : Fin M => c).prodCongr c with hC
  have hCmp : MeasurePreserving C P P := by
    rw [hP]
    exact (measurePreserving_pi _ _ fun _ => hcmp).prod hcmp
  rw [← hCmp.integral_comp C.measurableEmbedding]
  refine integral_congr_ae (ae_of_all _ fun d => ?_)
  have hCd : C d = (fun k i => d.1 k (π i), fun i => d.2 (π i)) :=
    Prod.ext (funext fun k => funext fun i => hca (d.1 k) i) (funext fun i => hca d.2 i)
  simp only [hCd]
  rw [shcherbinaTirozziGibbs_comp_perm κ h hu d.1 d.2 π]
  exact congrArg F (integral_map_equiv
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ π).symm.toHomeomorph.toMeasurableEquiv Φ)

/-- **The symmetry step of Proposition 3.2.4:** if `𝔼 ⟨‖σ‖²⟩` is finite, then the quenched
self-overlap is `ρ = ν (ε²)` and the quenched overlap is `q = ν (⟨ε⟩²)`, where `ε` is the last
spin. -/
theorem integral_shcherbinaTirozzi_overlaps_eq_last_spin {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) :
    ∀ G : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → Measure (ℝ^(N + 1)),
      (∀ d, G d = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ) →
      ∀ P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
        P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) →
        Integrable (fun d => ∫ σ, ‖σ‖ ^ 2 ∂(G d)) P →
        ∫ d, ∫ σ, ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 ∂(G d) ∂P =
            ∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂(G d) ∂P ∧
          ∫ d, ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G d)) ^ 2 ∂P =
            ∫ d, (∫ σ, σ (Fin.last N) ∂(G d)) ^ 2 ∂P := by
  intro G hG P hP hint
  have hprob : ∀ d, IsProbabilityMeasure (G d) := fun d => by
    rw [hG]; exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ hu hu0 _ _
  have hcoord : ∀ i : Fin (N + 1), Measurable fun σ : ℝ^(N + 1) => σ i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable
  -- every moment needed is finite, since `‖σ‖²` has a finite exponential moment
  have hsq : ∀ d, Integrable (fun σ => ‖σ‖ ^ 2) (G d) := fun d => by
    rw [hG]
    exact (memLp_id_shcherbinaTirozziGibbs hκ hu hu0 d.1 d.2).norm.integrable_sq
  have hmeas : ∀ f : ℝ^(N + 1) → ℝ, Measurable f → Measurable fun d => ∫ σ, f σ ∂(G d) := by
    intro f hf
    simp only [hG]
    exact measurable_integral_tilted
      (e := fun (d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) σ =>
        -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ)
      (measurable_shcherbinaTirozziHamiltonian κ h hu).neg hf
  -- symmetry between sites
  have hsymm : ∀ (i : Fin (N + 1)) (Φ : ℝ → ℝ) (F : ℝ → ℝ),
      ∫ d, F (∫ σ, Φ (σ i) ∂(G d)) ∂P = ∫ d, F (∫ σ, Φ (σ (Fin.last N)) ∂(G d)) ∂P := by
    intro i Φ F
    simp only [hG]
    rw [integral_shcherbinaTirozziGibbs_comp_perm κ h hu (Equiv.swap i (Fin.last N))
      (fun σ => Φ (σ i)) F P hP]
    refine integral_congr_ae (ae_of_all _ fun d => congrArg F (integral_congr_ae
      (ae_of_all _ fun σ => ?_)))
    set T := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i (Fin.last N)) with hT
    obtain ⟨τ, rfl⟩ := T.surjective σ
    have hTa : T τ (Fin.last N) = τ i := by
      change τ ((Equiv.swap i (Fin.last N)).symm (Fin.last N)) = τ i
      rw [Equiv.symm_swap, Equiv.swap_apply_right]
    simp only [T.symm_apply_apply, hTa]
  have h := integral_integral_inv_card_mul_sq_norm_of_exchangeable hmeas hsq hint (Fin.last N)
    hsymm
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using h

/-- The second moment of a Gaussian field built from the two independent sources of the last
spin: `𝔼 (h g + y)² = r + h²`. -/
private theorem integral_integral_sq_field (h : ℝ) (r : ℝ≥0) (n : Fin (N + 1)) :
    ∀ P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
      P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) →
      ∀ c a : ℝ, ∫ y, ∫ d, (c + ((h * d.2 n + y) / a) ^ 2) ∂P ∂(gaussianReal 0 r) =
        c + (r + h ^ 2) / a ^ 2 := by
  intro P hP c a
  have hPprob : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set Q := (gaussianReal 0 r).prod P with hQ
  -- the field `h g + y` is a centred Gaussian of variance `h² + r`
  have hg : HasLaw (fun d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) => d.2 n)
      (gaussianReal 0 1) P := by
    have hmp : MeasurePreserving (fun d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
        d.2 n) P (gaussianReal 0 1) := by
      rw [hP]
      exact (measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) n).comp
        measurePreserving_snd
    exact ⟨hmp.measurable.aemeasurable, hmp.map_eq⟩
  have hsum := gaussianReal_add_gaussianReal_of_indepFun (P := Q)
    (indepFun_prod (μ := gaussianReal 0 r) (ν := P) (X := id)
      (Y := fun d => h * d.2 n) measurable_id (by fun_prop)).symm
    (gaussianReal_const_mul (hg.comp (P := Q)
      ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩) h)
    (X := fun p => h * p.2.2 n) (Y := fun p => p.1)
    ⟨measurable_fst.aemeasurable, measurePreserving_fst.map_eq⟩
  rw [mul_zero, zero_add, mul_one] at hsum
  set v : ℝ≥0 := .mk (h ^ 2) (sq_nonneg h) + r with hv
  have hmp : MeasurePreserving (fun p : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      h * p.2.2 n + p.1) Q (gaussianReal 0 v) := ⟨by fun_prop, hsum⟩
  -- its second moment
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hmom : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
    have h := variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := id) aemeasurable_id
      integral_id_gaussianReal
    rw [variance_id_gaussianReal] at h
    simpa only [id_eq] using h.symm
  have hf : Integrable (fun x : ℝ => c + (x / a) ^ 2) (gaussianReal 0 v) := by
    simp only [div_pow]
    exact (integrable_const c).add (hsq.div_const _)
  have hcomp : Integrable (fun p : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      c + ((h * p.2.2 n + p.1) / a) ^ 2) Q := hmp.integrable_comp_of_integrable hf
  rw [← integral_prod _ hcomp, ← hQ]
  have hmap := integral_map (μ := Q) hmp.measurable.aemeasurable
    (f := fun x : ℝ => c + (x / a) ^ 2) (by fun_prop)
  rw [hmp.map_eq] at hmap
  rw [← hmap]
  simp only [div_pow]
  rw [integral_add (integrable_const c) (hsq.div_const _), integral_div, hmom, integral_const,
    probReal_univ, one_smul, hv]
  push_cast
  ring

/-- **Eq. (3.80):** at `t = 0`, `ν₀ (ε²) = 1 / a + (r + h²) / a²` with `a = 2 κ + r - r̄ > 0`. -/
theorem integral_integral_shcherbinaTirozziCavityGibbs_zero_sq_last {κ h rBar : ℝ} {r : ℝ≥0}
    (hκ : 0 < κ) (ha : 0 < 2 * κ + r - rBar) {u : ℝ → ℝ} (hu : Measurable u)
    (hu0 : ∀ x, u x ≤ 0) :
    ∀ P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
      P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) →
      ∫ y, ∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ) ∂P
          ∂(gaussianReal 0 r) =
        (2 * κ + r - rBar)⁻¹ + (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 := by
  intro P hP
  have h1 : ∀ (y : ℝ) (d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
      ∫ σ, σ (Fin.last N) ^ 2 ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ) =
        (2 * κ + r - rBar)⁻¹ + ((h * d.2 (Fin.last N) + y) / (2 * κ + r - rBar)) ^ 2 :=
    fun y d => by
      rw [integral_shcherbinaTirozziCavityGibbs_zero_last hκ r rBar y hu hu0 d.1 d.2
        (fun x => x ^ 2)]
      exact (integral_id_and_sq_volume_tilted_mul_sub_mul_sq ha _).2
  simp only [h1]
  exact integral_integral_sq_field h r (Fin.last N) P hP _ _

/-- **Eq. (3.79):** at `t = 0`, `ν₀ (ε₁ ε₂) = 𝔼 ⟨ε⟩² = (r + h²) / a²` with
`a = 2 κ + r - r̄ > 0`. -/
theorem integral_integral_sq_shcherbinaTirozziCavityGibbs_zero_last {κ h rBar : ℝ} {r : ℝ≥0}
    (hκ : 0 < κ) (ha : 0 < 2 * κ + r - rBar) {u : ℝ → ℝ} (hu : Measurable u)
    (hu0 : ∀ x, u x ≤ 0) :
    ∀ P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
      P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) →
      ∫ y, ∫ d, (∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ)) ^ 2 ∂P
          ∂(gaussianReal 0 r) =
        (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 := by
  intro P hP
  have h1 : ∀ (y : ℝ) (d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
      (∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ)) ^ 2 =
        0 + ((h * d.2 (Fin.last N) + y) / (2 * κ + r - rBar)) ^ 2 := fun y d => by
    rw [integral_shcherbinaTirozziCavityGibbs_zero_last hκ r rBar y hu hu0 d.1 d.2 (fun x => x),
      (integral_id_and_sq_volume_tilted_mul_sub_mul_sq ha _).1, zero_add]
  simp only [h1]
  rw [integral_integral_sq_field h r (Fin.last N) P hP, zero_add]

end SpinGlasses
