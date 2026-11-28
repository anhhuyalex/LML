/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.InnerProductSpace.EuclideanDrift
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ProductTiltedMarginal
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.ExpSq
public import LeanMachineLearning.ForMathlib.Probability.Moments.LogConcaveConcentration
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityEndpoint
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.OverlapConcentration

/-!
# The Shcherbina--Tirozzi model: the exponential tail of the last spin

For the cavity path (3.61) the last spin `ε` satisfies `ν_t (exp (ε² / K)) ≤ K` uniformly in
`t ∈ [0, 1]` (Talagrand, *Spin Glasses*, Vol. I, Lemma 3.2.6). Maurey's inequality controls
`ε - ⟨ε⟩`; the law of `ε` is log-concave, which bounds `⟨ε⟩` by the external field and by
`f' (0)`, where `f` is the logarithm of the partition function of the other spins; and `f' (0)`
is a Gaussian linear form in the couplings of the last spin.

The internal estimates are proved for constraint-indexed concave potentials `u_k : Fin M → ℝ → ℝ`
(`exists_integral_exp_sq_shcherbinaTirozziCavity_indexed_last_le`), so that both Lemma 3.2.6
(`u_k = u`) and Eq. (3.100) for the smoothed auxiliary cavity Hamiltonian (3.99) follow directly.

## Main declarations

* `SpinGlasses.integral_exp_sq_shcherbinaTirozziCavity_sub_le_four`: Eq. (3.87).
* `SpinGlasses.abs_integral_shcherbinaTirozziCavityGibbs_last_le`: Eq. (3.86).
* `SpinGlasses.exists_integral_exp_sq_shcherbinaTirozziCavity_indexed_last_le`: indexed-potential
  generalization of Lemma 3.2.6 (used for Eq. (3.100)).
* `SpinGlasses.exists_integral_exp_sq_shcherbinaTirozziCavity_last_le`: Lemma 3.2.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {N M : ℕ}

/-- Joint measurability of a cavity Hamiltonian with constraint-indexed potentials `u_k`. -/
private theorem measurable_indexed_cavity (κ h r rBar t : ℝ) {u_k : Fin M → ℝ → ℝ}
    (hu : ∀ k, Measurable (u_k k)) :
    Measurable fun p : (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) =>
      κ * ‖p.2‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
        ((∑ i : Fin N, p.1.2.1 k i.castSucc * p.2 i.castSucc) +
          Real.sqrt t * (p.1.2.1 k (Fin.last N) * p.2 (Fin.last N))))) -
        h * (∑ i, p.1.2.2 i * p.2 i) - p.2 (Fin.last N) * (Real.sqrt (1 - t) * p.1.1) +
        (1 - t) * (r - rBar) * p.2 (Fin.last N) ^ 2 / 2 := by
  have hσ : ∀ i : Fin (N + 1), Measurable fun p :
      (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) => p.2 i := fun i =>
    ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).comp measurable_snd
  have hg : ∀ (k : Fin M) (i : Fin (N + 1)), Measurable fun p :
      (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) => p.1.2.1 k i :=
    fun k i => (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hg₀ : ∀ i : Fin (N + 1), Measurable fun p :
      (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) => p.1.2.2 i :=
    fun i => (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hfield : ∀ k : Fin M, Measurable fun p :
      (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) =>
      u_k k ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, p.1.2.1 k i.castSucc * p.2 i.castSucc) +
        Real.sqrt t * (p.1.2.1 k (Fin.last N) * p.2 (Fin.last N)))) := fun k =>
    (hu k).comp (((Finset.measurable_sum _ fun i _ => (hg k _).mul (hσ _)).add
      (((hg k _).mul (hσ _)).const_mul _)).const_mul _)
  have hsum := Finset.measurable_sum Finset.univ fun k _ => hfield k
  have hlin := (Finset.measurable_sum Finset.univ fun i _ => (hg₀ i).mul (hσ i)).const_mul h
  have hq : Measurable fun p :
      (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) => κ * ‖p.2‖ ^ 2 :=
    (measurable_snd.norm.pow_const 2).const_mul κ
  have hy : Measurable fun p :
      (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) =>
      p.2 (Fin.last N) * (Real.sqrt (1 - t) * p.1.1) :=
    (hσ _).mul ((measurable_fst.comp measurable_fst).const_mul _)
  have hlast : Measurable fun p :
      (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) =>
      (1 - t) * (r - rBar) * p.2 (Fin.last N) ^ 2 / 2 :=
    (((hσ _).pow_const 2).const_mul _).div_const _
  exact (((hq.sub hsum).sub hlin).sub hy).add hlast

/-- The cavity Hamiltonian is jointly measurable in the field `y`, the disorder and the
configuration. -/
theorem measurable_shcherbinaTirozziCavityHamiltonian (κ h r rBar t : ℝ) {u : ℝ → ℝ}
    (hu : Measurable u) :
    Measurable fun p : (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ^(N + 1) =>
      shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1.1 u p.1.2.1 p.1.2.2 p.2 :=
  measurable_indexed_cavity κ h r rBar t (fun _ => hu)

/-- Splitting the indexed cavity exponent into the first `N` spins and the last spin. -/
private theorem neg_indexed_cavity_split (κ h r rBar t y : ℝ) (u_k : Fin M → ℝ → ℝ)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) :
    -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
        ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
        h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
        (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2) =
      ((∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ * (∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
            (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) * σ (Fin.last N))) +
          (h * (∑ i : Fin N, g₀ i.castSucc * σ i.castSucc) -
            κ * ∑ i : Fin N, σ i.castSucc ^ 2)) +
        (-((κ + (1 - t) * (r - rBar) / 2) * σ (Fin.last N) ^ 2) +
          (h * g₀ (Fin.last N) + Real.sqrt (1 - t) * y) * σ (Fin.last N)) := by
  have hnorm : ‖σ‖ ^ 2 = (∑ i : Fin N, σ i.castSucc ^ 2) + σ (Fin.last N) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  have hfield : ∀ k : Fin M,
      (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))) =
        (Real.sqrt (N + 1))⁻¹ * (∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) * σ (Fin.last N) :=
    fun k => by ring
  simp only [hfield, hnorm, Fin.sum_univ_castSucc (fun i => g₀ i * σ i)]
  ring

/-- The cavity Hamiltonian split into the energy of the first `N` spins, at the value `ε` of the
last one, and a one-dimensional quadratic energy. -/
theorem neg_shcherbinaTirozziCavityHamiltonian_split (κ h r rBar t y : ℝ) (u : ℝ → ℝ)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) :
    -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ =
      ((∑ k, u ((Real.sqrt (N + 1))⁻¹ * (∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
            (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) * σ (Fin.last N))) +
          (h * (∑ i : Fin N, g₀ i.castSucc * σ i.castSucc) -
            κ * ∑ i : Fin N, σ i.castSucc ^ 2)) +
        (-((κ + (1 - t) * (r - rBar) / 2) * σ (Fin.last N) ^ 2) +
          (h * g₀ (Fin.last N) + Real.sqrt (1 - t) * y) * σ (Fin.last N)) :=
  neg_indexed_cavity_split κ h r rBar t y (fun _ => u) g g₀ σ

private theorem measurable_indexed_cavity_apply (κ h r rBar t y : ℝ) {u_k : Fin M → ℝ → ℝ}
    (hu : ∀ k, Measurable (u_k k)) (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    Measurable fun σ : ℝ^(N + 1) =>
      κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
        ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
        h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
        (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 := by
  have hσ : ∀ i : Fin (N + 1), Measurable fun σ : ℝ^(N + 1) => σ i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable
  have hfield : ∀ k : Fin M, Measurable fun σ : ℝ^(N + 1) =>
      u_k k ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))) := fun k =>
    (hu k).comp (((Finset.measurable_sum _ fun i _ => (hσ i.castSucc).const_mul
      (g k i.castSucc)).add (((hσ (Fin.last N)).const_mul (g k (Fin.last N))).const_mul
        (Real.sqrt t))).const_mul _)
  have hsum := Finset.measurable_sum Finset.univ fun k _ => hfield k
  have hlin := (Finset.measurable_sum Finset.univ fun i _ =>
    (hσ i).const_mul (g₀ i)).const_mul h
  have hq : Measurable fun σ : ℝ^(N + 1) => κ * ‖σ‖ ^ 2 :=
    (measurable_norm.pow_const 2).const_mul κ
  have hy : Measurable fun σ : ℝ^(N + 1) => σ (Fin.last N) * (Real.sqrt (1 - t) * y) :=
    (hσ (Fin.last N)).mul_const _
  have hlast : Measurable fun σ : ℝ^(N + 1) =>
      (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 :=
    (((hσ (Fin.last N)).pow_const 2).const_mul _).div_const _
  exact (((hq.sub hsum).sub hlin).sub hy).add hlast

/-- The cavity Hamiltonian is measurable in the configuration. -/
theorem measurable_shcherbinaTirozziCavityHamiltonian_apply (κ h r rBar t y : ℝ) {u : ℝ → ℝ}
    (hu : Measurable u) (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    Measurable fun σ : ℝ^(N + 1) =>
      shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ :=
  measurable_indexed_cavity_apply κ h r rBar t y (fun _ => hu) g g₀

private theorem integrable_exp_neg_indexed_cavity {κ h r rBar t y : ℝ} (hκ : 0 < κ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u_k : Fin M → ℝ → ℝ} (hu : ∀ k, Measurable (u_k k))
    (hu0 : ∀ k x, u_k k x ≤ 0) (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    Integrable fun σ : ℝ^(N + 1) => Real.exp
      (-(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
          ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
            Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
          h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
          (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2)) := by
  obtain ⟨U, hU⟩ : ∃ U : ℝ^(N + 1) → ℝ, ∀ σ, U σ =
      (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
        (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 := ⟨_, fun _ => rfl⟩
  have hσ : ∀ i : Fin (N + 1), Measurable fun σ : ℝ^(N + 1) => σ i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable
  have hUm : Measurable U := by
    rw [show U = _ from funext hU]
    exact (Finset.measurable_sum _ fun k _ => (hu k).comp
      (((Finset.measurable_sum _ fun i _ => (hσ i.castSucc).const_mul _).add
        (((hσ (Fin.last N)).const_mul _).const_mul _)).const_mul _)).sub
      ((((hσ (Fin.last N)).pow_const 2).const_mul _).div_const _)
  have hU0 : ∀ σ, U σ ≤ 0 := fun σ => by
    have h1 : 0 ≤ (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 :=
      div_nonneg (mul_nonneg hq (sq_nonneg _)) two_pos.le
    rw [hU]
    exact (sub_le_self _ h1).trans (Finset.sum_nonpos fun k _ => hu0 k _)
  refine (integrable_exp_add_neg_mul_sq_norm_add_inner hUm hU0 hκ
    (WithLp.toLp 2 fun i => h * g₀ i + if i = Fin.last N then Real.sqrt (1 - t) * y else 0)).congr
    (ae_of_all _ fun σ => congrArg Real.exp ?_)
  rw [hU, EuclideanSpace.inner_toLp_mul_add_ite]
  ring

/-- For `κ > 0`, `u ≤ 0` and `(1 - t) (r - r̄) ≥ 0` the cavity Boltzmann weight is
integrable. -/
theorem integrable_exp_neg_shcherbinaTirozziCavityHamiltonian {κ h r rBar t y : ℝ} (hκ : 0 < κ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    Integrable fun σ : ℝ^(N + 1) =>
      Real.exp (-shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ) :=
  integrable_exp_neg_indexed_cavity hκ hq (fun _ => hu) (fun _ => hu0) g g₀

private theorem indexed_cavity_midpoint_gap (κ h : ℝ) {r rBar t : ℝ} (y : ℝ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u_k : Fin M → ℝ → ℝ}
    (hu : ∀ k, ConcaveOn ℝ Set.univ (u_k k)) (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ)
    (x z : ℝ^(N + 1)) :
    let H : ℝ^(N + 1) → ℝ := fun σ =>
      κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
        ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
        h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
        (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2
    κ * ‖(1 / 2 : ℝ) • (x - z)‖ ^ 2 ≤ (H x + H z) / 2 - H ((1 / 2 : ℝ) • (x + z)) := by
  intro H
  obtain ⟨m, hm⟩ : ∃ m : ℝ^(N + 1), m = (1 / 2 : ℝ) • (x + z) := ⟨_, rfl⟩
  rw [← hm]
  have hmi : ∀ i, m i = (x i + z i) / 2 := fun i => by
    rw [hm]; change (1 / 2) * (x i + z i) = _; ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ^(N + 1) → Fin M → ℝ, ∀ σ k, S σ k =
      (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))) := ⟨_, fun _ _ => rfl⟩
  have hH : ∀ σ : ℝ^(N + 1), H σ = κ * ‖σ‖ ^ 2 - (∑ k, u_k k (S σ k)) -
      h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
      (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 := fun σ => by simp only [H, hS]
  have hsum : ∑ i, g₀ i * m i = ((∑ i, g₀ i * x i) + ∑ i, g₀ i * z i) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [hmi]; ring
  have hSm : ∀ k, S m k = (1 / 2) * S x k + (1 / 2) * S z k := fun k => by
    have h1 : ∑ i : Fin N, g k i.castSucc * m i.castSucc =
        ((∑ i : Fin N, g k i.castSucc * x i.castSucc) +
          ∑ i : Fin N, g k i.castSucc * z i.castSucc) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hmi]; ring
    rw [hS, hS, hS, h1, hmi]; ring
  have hconc : ∑ k, (u_k k (S x k) + u_k k (S z k)) / 2 ≤ ∑ k, u_k k (S m k) :=
    Finset.sum_le_sum fun k _ => by
      rw [hSm]
      have := (hu k).2 (Set.mem_univ (S x k)) (Set.mem_univ (S z k))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at this
      linarith
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hconc
  have hpar : ‖(1 / 2 : ℝ) • (x - z)‖ ^ 2 = (‖x‖ ^ 2 + ‖z‖ ^ 2) / 2 - ‖m‖ ^ 2 := by
    have := parallelogram_law_with_norm ℝ x z
    simp only [hm, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_pow]
    nlinarith
  have hsq : m (Fin.last N) ^ 2 ≤ (x (Fin.last N) ^ 2 + z (Fin.last N) ^ 2) / 2 := by
    rw [hmi]; nlinarith [sq_nonneg (x (Fin.last N) - z (Fin.last N))]
  have hquad := mul_le_mul_of_nonneg_left hsq hq
  rw [hH, hH, hH, hpar, hsum, hmi (Fin.last N)]
  rw [hmi (Fin.last N)] at hquad
  linear_combination hconc + hquad / 2

/-- The cavity Hamiltonian is uniformly midpoint convex when `u` is concave and
`(1 - t) (r - r̄) ≥ 0`. -/
theorem shcherbinaTirozziCavityHamiltonian_midpoint_gap (κ h : ℝ) {r rBar t : ℝ} (y : ℝ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (x z : ℝ^(N + 1)) :
    κ * ‖(1 / 2 : ℝ) • (x - z)‖ ^ 2 ≤
      (shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ x +
          shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ z) / 2 -
        shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ ((1 / 2 : ℝ) • (x + z)) :=
  indexed_cavity_midpoint_gap κ h y hq (fun _ => hu) g g₀ x z

private theorem integral_exp_sq_indexed_cavity_sub_le_four {κ h r rBar t y : ℝ} (hκ : 0 < κ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u_k : Fin M → ℝ → ℝ}
    (hu : ∀ k, ConcaveOn ℝ Set.univ (u_k k)) (hu0 : ∀ k x, u_k k x ≤ 0)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    ∀ G : Measure (ℝ^(N + 1)),
      G = volume.tilted (fun σ => -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
        ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
        h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
        (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2)) →
      Integrable (fun σ => Real.exp (κ / 8 * (σ (Fin.last N) -
          ∫ τ, τ (Fin.last N) ∂G) ^ 2)) G ∧
        ∫ σ, Real.exp (κ / 8 * (σ (Fin.last N) - ∫ τ, τ (Fin.last N) ∂G) ^ 2) ∂G ≤ 4 := by
  intro G hG
  have hum : ∀ k, Measurable (u_k k) := fun k => (hu k).measurable_of_univ
  have hlip : ∀ x z : ℝ^(N + 1), |x (Fin.last N) - z (Fin.last N)| ≤ 1 * ‖x - z‖ :=
    fun x z => by rw [one_mul, ← Real.norm_eq_abs]; exact PiLp.norm_apply_le (x - z) (Fin.last N)
  have key := integral_exp_sq_sub_integral_le_four (μ₀ := volume) (C := Set.univ)
    (H := fun σ : ℝ^(N + 1) => κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
      ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
      h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
      (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2)
    convex_univ MeasurableSet.univ (NeZero.ne _)
    (measurable_indexed_cavity_apply κ h r rBar t y hum g g₀)
    (integrableOn_univ.2 (integrable_exp_neg_indexed_cavity hκ hq hum hu0 g g₀))
    (fun x _ z _ => indexed_cavity_midpoint_gap κ h y hq hu g g₀ x z) hκ
    (f := fun σ => σ (Fin.last N)) one_pos (fun x _ z _ => hlip x z)
  simp only [Measure.restrict_univ, one_pow, mul_one] at key
  rw [hG]
  exact key

/-- **Eq. (3.87):** Maurey's inequality for the last spin of the cavity system,
`⟨exp (κ (ε - ⟨ε⟩)² / 8)⟩ ≤ 4`. -/
theorem integral_exp_sq_shcherbinaTirozziCavity_sub_le_four {κ h r rBar t y : ℝ} (hκ : 0 < κ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u)
    (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    ∀ G : Measure (ℝ^(N + 1)),
      G = volume.tilted (fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ) →
      Integrable (fun σ => Real.exp (κ / 8 * (σ (Fin.last N) -
          ∫ τ, τ (Fin.last N) ∂G) ^ 2)) G ∧
        ∫ σ, Real.exp (κ / 8 * (σ (Fin.last N) - ∫ τ, τ (Fin.last N) ∂G) ^ 2) ∂G ≤ 4 :=
  integral_exp_sq_indexed_cavity_sub_le_four hκ hq (fun _ => hu) (fun _ => hu0) g g₀

private theorem abs_integral_indexed_cavity_last_le {κ h r rBar t y D : ℝ} (hκ : 0 < κ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u_k : Fin M → ℝ → ℝ}
    (hu : ∀ k, ConcaveOn ℝ Set.univ (u_k k)) (hu0 : ∀ k x, u_k k x ≤ 0)
    (hud : ∀ k, Differentiable ℝ (u_k k)) (hD : ∀ k x, |deriv (u_k k) x| ≤ D)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    let ν : Measure (Fin N → ℝ) := volume.tilted fun ρ =>
      (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i)) +
        (h * (∑ i : Fin N, g₀ i.castSucc * ρ i) - κ * ∑ i, ρ i ^ 2)
    |∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
            ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
              Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
            h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
            (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2))| ≤
        Real.sqrt (2 * κ)⁻¹ +
          |(∑ k, (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) *
              ∫ ρ, deriv (u_k k) ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i) ∂ν) +
            (h * g₀ (Fin.last N) + Real.sqrt (1 - t) * y)| / (2 * κ) := by
  intro ν
  have hum : ∀ k, Measurable (u_k k) := fun k => (hu k).measurable_of_univ
  set a : Fin M → (Fin N → ℝ) → ℝ := fun k ρ =>
    (Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i with ha
  set c : Fin M → ℝ := fun k =>
    (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) with hc
  set V : (Fin N → ℝ) → ℝ := fun ρ =>
    h * (∑ i : Fin N, g₀ i.castSucc * ρ i) - κ * ∑ i, ρ i ^ 2 with hV
  set κt : ℝ := κ + (1 - t) * (r - rBar) / 2 with hκt
  set d : ℝ := h * g₀ (Fin.last N) + Real.sqrt (1 - t) * y with hd
  have hκκ : κ ≤ κt := le_add_of_nonneg_right (div_nonneg hq two_pos.le)
  have hκt0 : 0 < κt := hκ.trans_le hκκ
  have ham : ∀ k, Measurable (a k) := fun k =>
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _).const_mul _
  have hVm : Measurable V :=
    ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _).const_mul _).sub
      ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2).const_mul _)
  have hVi : Integrable fun ρ => Real.exp (V ρ) := by
    have h1 := integrable_exp_add_neg_mul_sq_norm_add_inner (E := ℝ^N) (U := fun _ => 0)
      measurable_const (fun _ => le_rfl) hκ (WithLp.toLp 2 fun i : Fin N => h * g₀ i.castSucc)
    have h2 := ((PiLp.volume_preserving_toLp (Fin N)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin N → ℝ)).measurableEmbedding).2 h1
    refine h2.congr (ae_of_all _ fun ρ => congrArg Real.exp ?_)
    simp only [hV, inner_toLp_inv_sqrt_mul_eq, EuclideanSpace.real_norm_sq_eq]
    ring
  set f : ℝ → ℝ := fun x =>
    Real.log (∫ ρ, Real.exp ((∑ k, u_k k (a k ρ + c k * x)) + V ρ)) with hf
  have hslice : ∀ x, Integrable fun ρ => Real.exp ((∑ k, u_k k (a k ρ + c k * x)) + V ρ) :=
    fun x => hVi.mono' ((Finset.measurable_sum _ fun k _ =>
      (hum k).comp ((ham k).add_const _)).add hVm).exp.aestronglyMeasurable (ae_of_all _ fun ρ => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.2 (add_le_of_nonpos_left (Finset.sum_nonpos fun k _ => hu0 k _)))
  have hfd : ∀ x, HasDerivAt f (∑ k, c k * ∫ ρ, deriv (u_k k) (a k ρ + c k * x)
      ∂(volume.tilted fun ρ => (∑ k, u_k k (a k ρ + c k * x)) + V ρ)) x := fun x =>
    hasDerivAt_log_integral_exp_sum_comp_add_mul_indexed hud hu0 hD ham c hVm hVi x
  have hfc : ConcaveOn ℝ Set.univ f := by
    refine concaveOn_log_integral_exp volume
      (F := fun p : (Fin N → ℝ) × ℝ => (∑ k, u_k k (a k p.1 + c k * p.2)) + V p.1) ?_ hslice
    obtain ⟨π, hπ⟩ : ∃ π : Fin N → (Fin N → ℝ) × ℝ →ₗ[ℝ] ℝ, ∀ i p, π i p = p.1 i :=
      ⟨fun i => LinearMap.proj i ∘ₗ LinearMap.fst ℝ (Fin N → ℝ) ℝ, fun _ _ => rfl⟩
    set ℓ : Fin M → (Fin N → ℝ) × ℝ →ₗ[ℝ] ℝ := fun k =>
      (Real.sqrt (N + 1))⁻¹ • (∑ i : Fin N, g k i.castSucc • π i) +
        c k • LinearMap.snd ℝ (Fin N → ℝ) ℝ with hℓdef
    have hℓ : ∀ k p, ℓ k p = a k p.1 + c k * p.2 := fun k p => by
      simp [hℓdef, ha, hπ, LinearMap.sum_apply]
    have hfields : ConcaveOn ℝ Set.univ (∑ k, u_k k ∘ ℓ k) :=
      Finset.sum_induction _ (ConcaveOn ℝ Set.univ) (fun _ _ => ConcaveOn.add)
        (concaveOn_const 0 convex_univ) fun k _ => (hu k).comp_linearMap (ℓ k)
    have hsq : ConvexOn ℝ Set.univ (∑ i, (fun x : ℝ => x ^ 2) ∘ π i) :=
      Finset.sum_induction _ (ConvexOn ℝ Set.univ) (fun _ _ => ConvexOn.add)
        (convexOn_const 0 convex_univ) fun i _ => even_two.convexOn_pow.comp_linearMap (π i)
    have hfield := (h • ∑ i : Fin N, g₀ i.castSucc • π i).concaveOn
      (convex_univ (𝕜 := ℝ) (E := (Fin N → ℝ) × ℝ))
    refine ((hfields.add hfield).sub (hsq.smul hκ.le)).congr fun p _ => ?_
    simp [Finset.sum_apply, hℓ, hπ, hV]
    ring
  set e : ℝ^(N + 1) ≃ᵐ ℝ × (Fin N → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (N + 1) → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last N))
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).comp
      (PiLp.volume_preserving_ofLp (Fin (N + 1)))
  have he1 : ∀ σ, (e σ).1 = σ (Fin.last N) := fun σ => rfl
  have he2 : ∀ σ i, (e σ).2 i = σ i.castSucc := fun σ i => by
    change σ ((Fin.last N).succAbove i) = σ i.castSucc
    rw [Fin.succAbove_last]
  set E : ℝ × (Fin N → ℝ) → ℝ := fun p =>
    ((∑ k, u_k k (a k p.2 + c k * p.1)) + V p.2) + (-(κt * p.1 ^ 2) + d * p.1) with hE
  have hHE : ∀ σ : ℝ^(N + 1), -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
      ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
      h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
      (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2) = E (e σ) := fun σ => by
    rw [neg_indexed_cavity_split]
    simp only [hE, ha, hc, hV, hκt, hd, he1, he2]
  have hEm : Measurable E := by
    refine ((Finset.measurable_sum _ fun k _ => (hum k).comp
      (((ham k).comp measurable_snd).add (measurable_fst.const_mul _))).add
        (hVm.comp measurable_snd)).add ?_
    exact (((measurable_fst.pow_const 2).const_mul _).neg).add (measurable_fst.const_mul _)
  have hEi : Integrable (fun p => Real.exp (E p)) (volume.prod volume) := by
    have h1 := integrable_exp_neg_indexed_cavity (h := h) (y := y) hκ hq hum hu0 g g₀
    refine (hmp.integrable_comp_emb e.measurableEmbedding).1
      (h1.congr (ae_of_all _ fun σ => ?_))
    simp only [Function.comp_apply, hHE]
  have hmean : ∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ => E (e σ)) =
      ∫ x, x ∂((volume : Measure ℝ).tilted fun x => f x - κt * x ^ 2 + d * x) := by
    have h1 := map_tilted_measurableEquiv (μ := (volume : Measure (ℝ^(N + 1))))
      (ν := volume.prod volume) e hmp (e := fun σ => E (e σ)) (hEm.comp e.measurable)
    have h2 : (fun σ => E (e σ)) ∘ e.symm = E :=
      funext fun p => congrArg E (e.apply_symm_apply p)
    rw [h2] at h1
    have h3 : ∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ => E (e σ)) =
        ∫ p, p.1 ∂((volume.prod volume).tilted E) := by
      rw [← h1, integral_map_equiv]
      rfl
    have h4 : (fun x => Real.log (∫ ρ, Real.exp (E (x, ρ)))) =
        fun x => f x - κt * x ^ 2 + d * x := funext fun x => by
      have h5 : (fun ρ => Real.exp (E (x, ρ))) = fun ρ =>
          Real.exp ((∑ k, u_k k (a k ρ + c k * x)) + V ρ) * Real.exp (-(κt * x ^ 2) + d * x) :=
        funext fun ρ => Real.exp_add _ _
      rw [h5, integral_mul_const, Real.log_mul (integral_exp_pos (hslice x)).ne'
        (Real.exp_pos _).ne', Real.log_exp]
      simp only [hf]
      ring
    rw [h3, ← h4, ← map_fst_tilted_prod hEi,
      integral_map measurable_fst.aemeasurable (by fun_prop)]
  simp only [hHE]
  rw [hmean]
  refine (abs_integral_volume_tilted_concave_sub_mul_sq_le hfc hfd hκt0 d).trans ?_
  have h0 : (∑ k, c k * ∫ ρ, deriv (u_k k) (a k ρ + c k * 0)
        ∂(volume.tilted fun ρ => (∑ k, u_k k (a k ρ + c k * 0)) + V ρ)) =
      ∑ k, c k * ∫ ρ, deriv (u_k k) (a k ρ) ∂ν := by
    simp only [mul_zero, add_zero, ν, ha, hV]
  rw [h0]
  have h2κ : 2 * κ ≤ 2 * κt := by linarith
  exact add_le_add (Real.sqrt_le_sqrt (inv_anti₀ (by linarith) h2κ))
    (div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) h2κ)

/-- **Eq. (3.86):** the mean of the last spin is controlled by its external field and by the
derivative at `0` of the logarithm of the partition function of the other spins:
`|⟨ε⟩| ≤ (2 κ)^{-1/2} + |f' (0) + h g_N + √(1 - t) y| / (2 κ)`, where
`f' (0) = ∑ k, (N + 1)^{-1/2} √t g_{N k} ⟨u' (S_{k, 0})⟩`. -/
theorem abs_integral_shcherbinaTirozziCavityGibbs_last_le {κ h r rBar t y D : ℝ} (hκ : 0 < κ)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u)
    (hu0 : ∀ x, u x ≤ 0) (hud : Differentiable ℝ u) (hD : ∀ x, |deriv u x| ≤ D)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    let ν : Measure (Fin N → ℝ) := volume.tilted fun ρ =>
      (∑ k, u ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i)) +
        (h * (∑ i : Fin N, g₀ i.castSucc * ρ i) - κ * ∑ i, ρ i ^ 2)
    |∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ)| ≤
        Real.sqrt (2 * κ)⁻¹ +
          |(∑ k, (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) *
              ∫ ρ, deriv u ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i) ∂ν) +
            (h * g₀ (Fin.last N) + Real.sqrt (1 - t) * y)| / (2 * κ) :=
  abs_integral_indexed_cavity_last_le hκ hq (fun _ => hu) (fun _ => hu0) (fun _ => hud)
    (fun _ => hD) g g₀

/-- `𝔼 exp (l (∑ k, w k g_{k, N+1})²) ≤ 2` when the coefficients `w k` depend measurably on the
disorder other than the couplings of the last spin and `l ∑ k, w k² ≤ 1 / 4`. -/
private theorem integral_exp_sq_lastColumn_le_two
    {w : (Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ) → Fin M → ℝ}
    (hwm : ∀ k, Measurable fun q => w q k) {l : ℝ} (hlw : ∀ q, l * ∑ k, w q k ^ 2 ≤ 1 / 4) :
    ∀ P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
      P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) →
      Integrable (fun d => Real.exp (l *
          (∑ k, w (fun k i => d.1 k i.castSucc, d.2) k * d.1 k (Fin.last N)) ^ 2)) P ∧
        ∫ d, Real.exp (l *
          (∑ k, w (fun k i => d.1 k i.castSucc, d.2) k * d.1 k (Fin.last N)) ^ 2) ∂P ≤ 2 := by
  intro P hP
  set γ1 := Measure.pi fun _ : Fin M => gaussianReal 0 1
  set γ2 := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
  set split : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) →
      (Fin M → ℝ) × ((Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) := fun d =>
    (fun k => d.1 k (Fin.last N), (fun k i => d.1 k i.castSucc, d.2))
  set F : (Fin M → ℝ) × ((Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) → ℝ := fun z =>
    Real.exp (l * (∑ k, w z.2 k * z.1 k) ^ 2)
  have hmp : MeasurePreserving split P (γ1.prod γ2) := by
    have h1 : MeasurePreserving
        (fun g : Fin M → Fin (N + 1) → ℝ => fun k =>
          MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last N) (g k))
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Measure.pi fun _ : Fin M => (gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) :=
      measurePreserving_pi _ _ fun _ => measurePreserving_piFinSuccAbove
        (fun _ : Fin (N + 1) => gaussianReal 0 1) (Fin.last N)
    have h2 := measurePreserving_arrowProdEquivProdArrow ℝ (Fin N → ℝ) (Fin M)
      (fun _ => gaussianReal 0 1) (fun _ => Measure.pi fun _ : Fin N => gaussianReal 0 1)
    have h3 := ((h2.comp h1).prod (MeasurePreserving.id
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    have h4 := (measurePreserving_prodAssoc γ1
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1)
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)).comp h3
    rw [hP]
    have e : split = MeasurableEquiv.prodAssoc ∘ Prod.map
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin N → ℝ) (Fin M) ∘ fun g k =>
          MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last N) (g k)) id := by
      funext d
      refine Prod.ext (funext fun k => rfl) (Prod.ext (funext fun k => funext fun i => ?_) rfl)
      change d.1 k i.castSucc = d.1 k ((Fin.last N).succAbove i)
      rw [Fin.succAbove_last]
    rw [e]
    exact h4
  have hFm : Measurable F :=
    (((Finset.measurable_sum _ fun k _ => ((hwm k).comp measurable_snd).mul
      ((measurable_pi_apply k).comp measurable_fst)).pow_const 2).const_mul _).exp
  have hFq : ∀ q, Integrable (fun z => F (z, q)) γ1 ∧ ∫ z, F (z, q) ∂γ1 ≤ 2 := fun q =>
    integral_exp_mul_sq_sum_pi_gaussianReal_le_two (w q) (hlw q)
  have hFi : Integrable F (γ1.prod γ2) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).2
      ⟨ae_of_all _ fun q => (hFq q).1, ?_⟩
    refine Integrable.of_bound
      (hFm.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable) 2
      (ae_of_all _ fun q => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    refine (integral_congr_ae (ae_of_all _ fun z => ?_)).trans_le (hFq q).2
    exact Real.norm_of_nonneg (Real.exp_pos _).le
  have hFle : ∫ z, F z ∂(γ1.prod γ2) ≤ 2 := by
    rw [integral_prod_symm _ hFi]
    refine (integral_mono hFi.integral_prod_right (integrable_const 2) fun q =>
      (hFq q).2).trans_eq ?_
    rw [integral_const, probReal_univ, one_smul]
  refine ⟨hmp.integrable_comp_of_integrable hFi, le_of_eq_of_le ?_ hFle⟩
  rw [← hmp.map_eq]
  exact (integral_map hmp.measurable.aemeasurable hFm.aestronglyMeasurable).symm

/-- The Gibbs average of `exp (ε² / K)` is bounded through `f' (0)` and the external field:
Eqs. (3.86) and (3.87) combined, for indexed potentials `u_k`. -/
private theorem integral_exp_sq_indexed_last_le_of_coeff {κ₀ κ h r rBar t y D K W : ℝ}
    (hκ₀ : 0 < κ₀) (hκ : κ₀ ≤ κ) (hK0 : 0 < K) (hK : 16 ≤ κ₀ * K)
    (hq : 0 ≤ (1 - t) * (r - rBar)) {u_k : Fin M → ℝ → ℝ}
    (hu : ∀ k, ConcaveOn ℝ Set.univ (u_k k)) (hu0 : ∀ k x, u_k k x ≤ 0)
    (hud : ∀ k, Differentiable ℝ (u_k k)) (hD : ∀ k x, |deriv (u_k k) x| ≤ D)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ)
    (hW : ∀ ν : Measure (Fin N → ℝ),
      ν = volume.tilted (fun ρ =>
        (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i)) +
          (h * (∑ i : Fin N, g₀ i.castSucc * ρ i) - κ * ∑ i, ρ i ^ 2)) →
      ∑ k, (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) *
        ∫ ρ, deriv (u_k k) ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i) ∂ν = W) :
    ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
          ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
            Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
          h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
          (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2)) ≤
      4 * Real.exp (3 / (κ₀ * K)) * Real.exp (3 / (2 * κ₀ ^ 2 * K) *
        (W ^ 2 + (h * g₀ (Fin.last N) + Real.sqrt (1 - t) * y) ^ 2)) := by
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  set G := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
    -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
      ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N))))) -
      h * (∑ i, g₀ i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
      (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2) with hG
  set m : ℝ := ∫ τ, τ (Fin.last N) ∂G with hm
  have hmau := integral_exp_sq_indexed_cavity_sub_le_four (h := h) (y := y) hκ0 hq hu hu0 g g₀ G hG
  rw [← hm] at hmau
  have hsq : ∀ σ : ℝ^(N + 1), Real.exp (σ (Fin.last N) ^ 2 / K) ≤
      Real.exp (2 * m ^ 2 / K) * Real.exp (κ / 8 * (σ (Fin.last N) - m) ^ 2) := fun σ => by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : σ (Fin.last N) ^ 2 ≤ 2 * m ^ 2 + 2 * (σ (Fin.last N) - m) ^ 2 := by
      nlinarith [sq_nonneg (σ (Fin.last N) - 2 * m)]
    have h2 : 2 * (σ (Fin.last N) - m) ^ 2 / K ≤ κ / 8 * (σ (Fin.last N) - m) ^ 2 := by
      rw [div_le_iff₀ hK0]
      have h3 : 16 ≤ κ * K := hK.trans (mul_le_mul_of_nonneg_right hκ hK0.le)
      nlinarith [mul_nonneg (sub_nonneg.2 h3) (sq_nonneg (σ (Fin.last N) - m))]
    refine (div_le_div_of_nonneg_right h1 hK0.le).trans ?_
    rw [add_div]
    exact add_le_add le_rfl h2
  have h1 : ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K) ∂G ≤ 4 * Real.exp (2 * m ^ 2 / K) := by
    refine (integral_mono_of_nonneg (ae_of_all _ fun _ => (Real.exp_pos _).le)
      (hmau.1.const_mul _) (ae_of_all _ hsq)).trans ?_
    rw [integral_const_mul, mul_comm 4]
    exact mul_le_mul_of_nonneg_left hmau.2 (Real.exp_pos _).le
  have h386 := abs_integral_indexed_cavity_last_le (h := h) (y := y) hκ0 hq hu hu0 hud hD g g₀
  dsimp only at h386
  rw [hW _ rfl, ← hG, ← hm] at h386
  set b : ℝ := h * g₀ (Fin.last N) + Real.sqrt (1 - t) * y with hb
  have hm2 : m ^ 2 ≤ 3 / (2 * κ₀) + 3 / (4 * κ₀ ^ 2) * (W ^ 2 + b ^ 2) := by
    have h2 : |m| ≤ Real.sqrt (2 * κ₀)⁻¹ + (|W| + |b|) / (2 * κ₀) := by
      refine h386.trans (add_le_add (Real.sqrt_le_sqrt (inv_anti₀ (by positivity)
        (by linarith))) ?_)
      exact (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith)).trans
        (div_le_div_of_nonneg_right (abs_add_le _ _) (by positivity))
    have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at h3
    refine h3.trans ?_
    have h4 : ∀ x y z : ℝ, (x + (y + z)) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := fun x y z => by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    rw [add_div]
    refine (h4 _ _ _).trans_eq ?_
    rw [Real.sq_sqrt (by positivity), div_pow, div_pow, sq_abs, sq_abs]
    field_simp
    ring
  have h2 : 2 * m ^ 2 / K ≤ 3 / (κ₀ * K) + 3 / (2 * κ₀ ^ 2 * K) * (W ^ 2 + b ^ 2) := by
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 two_pos.le)
      hK0.le).trans_eq ?_
    field_simp
    ring
  refine h1.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by norm_num)

/-- `e^{x + z} ≤ (e^{2x} + e^{2z}) / 2`. -/
private theorem exp_add_le_half (x z : ℝ) :
    Real.exp (x + z) ≤ (Real.exp (2 * x) + Real.exp (2 * z)) / 2 := by
  have e1 : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [sq, ← Real.exp_add, two_mul]
  have e2 : Real.exp (2 * z) = Real.exp z ^ 2 := by rw [sq, ← Real.exp_add, two_mul]
  rw [Real.exp_add, e1, e2]
  nlinarith [sq_nonneg (Real.exp x - Real.exp z)]

/-- Separation of the three Gaussian variables in the exponential bound. -/
private theorem exp_mul_sq_add_sq_le {L h₀ h t y g W : ℝ} (hL : 0 ≤ L) (hh : |h| ≤ h₀)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (L * (W ^ 2 + (h * g + Real.sqrt (1 - t) * y) ^ 2)) ≤
      (Real.exp (2 * L * W ^ 2) +
        (Real.exp (8 * L * h₀ ^ 2 * g ^ 2) + Real.exp (8 * L * y ^ 2)) / 2) / 2 := by
  set b : ℝ := h * g + Real.sqrt (1 - t) * y with hb
  have hb2 : b ^ 2 ≤ 2 * h₀ ^ 2 * g ^ 2 + 2 * y ^ 2 := by
    have h3 : b ^ 2 ≤ 2 * (h * g) ^ 2 + 2 * (Real.sqrt (1 - t) * y) ^ 2 := by
      rw [hb]
      nlinarith [sq_nonneg (h * g - Real.sqrt (1 - t) * y)]
    have h4 : h ^ 2 ≤ h₀ ^ 2 := by
      rw [← sq_abs h]
      exact pow_le_pow_left₀ (abs_nonneg _) hh 2
    have h5 : (Real.sqrt (1 - t) * y) ^ 2 ≤ y ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (sub_nonneg.2 ht1)]
      exact mul_le_of_le_one_left (sq_nonneg _) (by linarith)
    have h6 := mul_le_mul_of_nonneg_right h4 (sq_nonneg g)
    rw [mul_pow] at h3
    linarith
  have h5 : Real.exp (2 * (L * b ^ 2)) ≤
      (Real.exp (8 * L * h₀ ^ 2 * g ^ 2) + Real.exp (8 * L * y ^ 2)) / 2 := by
    have h6 := mul_le_mul_of_nonneg_left hb2 (mul_nonneg two_pos.le hL)
    refine (Real.exp_le_exp.2 (show 2 * (L * b ^ 2) ≤
      4 * L * h₀ ^ 2 * g ^ 2 + 4 * L * y ^ 2 by linarith)).trans
      ((exp_add_le_half _ _).trans_eq ?_)
    ring_nf
  rw [mul_add]
  refine (exp_add_le_half _ _).trans (div_le_div_of_nonneg_right
    (add_le_add (le_of_eq (by rw [mul_assoc])) h5) two_pos.le)

/-- The majorant in the proof of Lemma 3.2.6: if the exponential moments `a`, `b`, `c` have
means at most `2`, then `C (a + b) / 4 + C c / 2` has mean at most `2 C` for the product law. -/
private theorem integrable_and_integral_cavity_majorant_le {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a c : β → ℝ} {b : α → ℝ}
    (ha : Integrable a ν ∧ ∫ d, a d ∂ν ≤ 2) (hb : Integrable b μ ∧ ∫ y, b y ∂μ ≤ 2)
    (hc : Integrable c ν ∧ ∫ d, c d ∂ν ≤ 2) {C : ℝ} (hC : 0 ≤ C) :
    Integrable (fun p : α × β => C / 4 * (a p.2 + b p.1) + C / 2 * c p.2) (μ.prod ν) ∧
      ∫ p, (C / 4 * (a p.2 + b p.1) + C / 2 * c p.2) ∂(μ.prod ν) ≤ 2 * C := by
  have hi1 := ha.1.comp_snd μ
  have hi2 := hb.1.comp_fst ν
  have hi3 := hc.1.comp_snd μ
  have h12 : Integrable (fun p : α × β => C / 4 * (a p.2 + b p.1)) (μ.prod ν) :=
    (hi1.add hi2).const_mul _
  refine ⟨h12.add (hi3.const_mul _), ?_⟩
  rw [integral_add h12 (hi3.const_mul _), integral_const_mul, integral_const_mul,
    integral_add hi1 hi2, integral_fun_snd (μ := μ) (ν := ν) a,
    integral_fun_fst (μ := μ) (ν := ν) b, integral_fun_snd (μ := μ) (ν := ν) c]
  simp only [probReal_univ, one_smul]
  have h1 := mul_le_mul_of_nonneg_left (add_le_add ha.2 hb.2)
    (div_nonneg hC (by norm_num : (0 : ℝ) ≤ 4))
  have h2 := mul_le_mul_of_nonneg_left hc.2 (div_nonneg hC two_pos.le)
  linarith

/-- **Indexed-potential version of Lemma 3.2.6:** for constraint-indexed concave potentials
`u_k : Fin M → ℝ → ℝ` with `u_k ≤ 0`, `|(u_k)'| ≤ D` and `M ≤ 11 * (N + 1)`,
`𝔼 ⟨exp (ε² / K)⟩ ≤ K` uniformly in `t ∈ [0, 1]`. -/
theorem exists_integral_exp_sq_shcherbinaTirozziCavity_indexed_last_le (κ₀ h₀ D R : ℝ)
    (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ 16 / κ₀ ≤ K ∧ ∀ (N M : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u_k : Fin M → ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R → M ≤ 11 * (N + 1) →
      (∀ k, ConcaveOn ℝ Set.univ (u_k k)) → (∀ k x, u_k k x ≤ 0) →
      (∀ k, Differentiable ℝ (u_k k)) → (∀ k x, |deriv (u_k k) x| ≤ D) →
      let P : Measure (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :=
        (gaussianReal 0 r).prod
          ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
      let F : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ := fun p =>
        ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K)
          ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
            -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ *
              ((∑ i : Fin N, p.2.1 k i.castSucc * σ i.castSucc) +
                Real.sqrt t * (p.2.1 k (Fin.last N) * σ (Fin.last N))))) -
              h * (∑ i, p.2.2 i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * p.1) +
              (1 - t) * ((r : ℝ) - rBar) * σ (Fin.last N) ^ 2 / 2))
      Integrable F P ∧ ∫ p, F p ∂P ≤ K := by
  set S : ℝ := 1 + h₀ ^ 2 + R + D ^ 2 with hS
  have hS1 : 1 ≤ S := by linarith [sq_nonneg h₀, sq_nonneg D]
  set K : ℝ := 16 + 16 / κ₀ + 132 * S / κ₀ ^ 2 with hK
  have h16 : 0 ≤ 16 / κ₀ := by positivity
  have h132 : 0 ≤ 132 * S / κ₀ ^ 2 := by positivity
  have hK0 : 0 < K := by linarith
  set L : ℝ := 3 / (2 * κ₀ ^ 2 * K) with hL
  have hL0 : 0 < L := by positivity
  have hLS : 88 * L * S ≤ 1 := by
    have h1 : 132 * S ≤ κ₀ ^ 2 * K := by
      have : 132 * S / κ₀ ^ 2 ≤ K := by linarith
      rwa [div_le_iff₀' (pow_pos hκ₀ 2)] at this
    have e : 88 * L * S = 132 * S / (κ₀ ^ 2 * K) := by rw [hL]; field_simp; ring
    rw [e, div_le_one (by positivity)]
    exact h1
  have hκK : 16 ≤ κ₀ * K := by
    have : 16 / κ₀ ≤ K := by linarith
    rwa [div_le_iff₀' hκ₀] at this
  refine ⟨K, hK0, by linarith,
    fun N M κ h t rBar r u_k hκ hh ht0 ht1 hrr hrR hM huc hu0 hud hD => ?_⟩
  intro law F
  obtain ⟨P, hP⟩ : ∃ P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
      P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := ⟨_, rfl⟩
  have hlaw : law = (gaussianReal 0 r).prod P := by rw [hP]
  rw [hlaw]
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hq : 0 ≤ (1 - t) * ((r : ℝ) - rBar) := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have hum : ∀ k, Measurable (u_k k) := fun k => (huc k).measurable_of_univ
  have hD0 : 0 ≤ |D| := abs_nonneg D
  have hD' : ∀ k x, |deriv (u_k k) x| ≤ |D| := fun k x => (hD k x).trans (le_abs_self D)
  have hPprob : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set ν_q : (Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ) → Measure (Fin N → ℝ) := fun q =>
    volume.tilted fun ρ => (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, q.1 k i * ρ i)) +
      (h * (∑ i : Fin N, q.2 i.castSucc * ρ i) - κ * ∑ i, ρ i ^ 2)
  set w : (Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ) → Fin M → ℝ := fun q k =>
    (Real.sqrt (N + 1))⁻¹ * Real.sqrt t *
      ∫ ρ, deriv (u_k k) ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, q.1 k i * ρ i) ∂(ν_q q)
  have hwm : ∀ k, Measurable fun q => w q k := fun k => by
    have hρ : ∀ i : Fin N, Measurable fun p :
        ((Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) × (Fin N → ℝ) => p.2 i := fun i =>
      (measurable_pi_apply i).comp measurable_snd
    have hgq : ∀ (k : Fin M) (i : Fin N), Measurable fun p :
        ((Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) × (Fin N → ℝ) => p.1.1 k i := fun k i =>
      (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
        (measurable_fst.comp measurable_fst))
    have hg0 : ∀ i : Fin (N + 1), Measurable fun p :
        ((Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) × (Fin N → ℝ) => p.1.2 i := fun i =>
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
    have hfield : ∀ j : Fin M, Measurable fun p :
        ((Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) × (Fin N → ℝ) =>
        (Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, p.1.1 j i * p.2 i := fun j =>
      (Finset.measurable_sum _ fun i _ => (hgq j i).mul (hρ i)).const_mul _
    have hE : Measurable fun p :
        ((Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) × (Fin N → ℝ) =>
        (∑ j, u_k j ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, p.1.1 j i * p.2 i)) +
          (h * (∑ i : Fin N, p.1.2 i.castSucc * p.2 i) - κ * ∑ i, p.2 i ^ 2) :=
      (Finset.measurable_sum _ fun j _ => (hum j).comp (hfield j)).add
        (((Finset.measurable_sum _ fun i _ => (hg0 _).mul (hρ i)).const_mul _).sub
          ((Finset.measurable_sum _ fun i _ => (hρ i).pow_const 2).const_mul _))
    exact (measurable_integral_tilted_dep
      (e := fun (q : (Fin M → Fin N → ℝ) × (Fin (N + 1) → ℝ)) (ρ : Fin N → ℝ) =>
        (∑ j, u_k j ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, q.1 j i * ρ i)) +
          (h * (∑ i : Fin N, q.2 i.castSucc * ρ i) - κ * ∑ i, ρ i ^ 2))
      (Y := fun q ρ => deriv (u_k k) ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, q.1 k i * ρ i))
      hE ((measurable_deriv (u_k k)).comp (hfield k))).const_mul _
  have hwsq : ∀ q, ∑ k, w q k ^ 2 ≤ 11 * D ^ 2 := fun q => by
    have hk : ∀ k, w q k ^ 2 ≤ D ^ 2 / (N + 1) := fun k => by
      have hI : |∫ ρ, deriv (u_k k) ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, q.1 k i * ρ i) ∂(ν_q q)|
          ≤ |D| := by
        have h1 : ∀ᵐ ρ ∂(ν_q q),
            ‖deriv (u_k k) ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, q.1 k i * ρ i)‖ ≤ |D| :=
          ae_of_all _ fun ρ => (Real.norm_eq_abs _).trans_le (hD' k _)
        refine (Real.norm_eq_abs _).symm.trans_le ((norm_integral_le_of_norm_le_const h1).trans ?_)
        exact mul_le_of_le_one_right hD0 measureReal_le_one
      have hsq : ((Real.sqrt (N + 1))⁻¹ * Real.sqrt t) ^ 2 ≤ ((N : ℝ) + 1)⁻¹ := by
        rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt ht0]
        exact mul_le_of_le_one_right (by positivity) ht1
      dsimp only [w]
      rw [mul_pow, div_eq_inv_mul, ← sq_abs D]
      exact mul_le_mul hsq (sq_le_sq' (neg_le_of_abs_le hI) (le_of_abs_le hI)) (sq_nonneg _)
        (by positivity)
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc',
      div_le_iff₀ (by positivity)]
    have : (M : ℝ) ≤ 11 * (N + 1) := by exact_mod_cast hM
    nlinarith [sq_nonneg D]
  set W : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → ℝ := fun d =>
    ∑ k, w (fun k i => d.1 k i.castSucc, d.2) k * d.1 k (Fin.last N)
  have hwf : ∀ (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ),
      ∀ μ : Measure (Fin N → ℝ),
        μ = volume.tilted (fun ρ =>
          (∑ k, u_k k ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i)) +
            (h * (∑ i : Fin N, g₀ i.castSucc * ρ i) - κ * ∑ i, ρ i ^ 2)) →
        ∑ k, (Real.sqrt (N + 1))⁻¹ * (Real.sqrt t * g k (Fin.last N)) *
            ∫ ρ, deriv (u_k k) ((Real.sqrt (N + 1))⁻¹ * ∑ i : Fin N, g k i.castSucc * ρ i) ∂μ =
          W (g, g₀) := fun g g₀ μ hμ => by
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ν_q (fun k i => g k i.castSucc, g₀) = μ := hμ ▸ rfl
    dsimp only [w]
    rw [e]
    ring
  have hB := integral_exp_sq_lastColumn_le_two (N := N) (M := M) hwm (l := 2 * L) (fun q => by
    have h1 := mul_le_mul_of_nonneg_left (hwsq q) (mul_nonneg two_pos.le hL0.le)
    have h2 : 88 * L * D ^ 2 ≤ 88 * L * S :=
      mul_le_mul_of_nonneg_left (by linarith [sq_nonneg h₀]) (by positivity)
    linarith) P hP
  have hA1 : Integrable (fun d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
        Real.exp (8 * L * h₀ ^ 2 * d.2 (Fin.last N) ^ 2)) P ∧
      ∫ d, Real.exp (8 * L * h₀ ^ 2 * d.2 (Fin.last N) ^ 2) ∂P ≤ 2 := by
    have hev : MeasurePreserving (fun d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
        d.2 (Fin.last N)) P (gaussianReal 0 1) := by
      rw [hP]
      exact (measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Fin.last N)).comp measurePreserving_snd
    have h1 := integral_exp_mul_sq_gaussianReal_le_two (l := 8 * L * h₀ ^ 2) (v := 1) (by
      rw [NNReal.coe_one, mul_one]
      have h3 : L * h₀ ^ 2 ≤ L * S :=
        mul_le_mul_of_nonneg_left (by linarith [sq_nonneg D]) hL0.le
      have h4 : 0 ≤ L * S := mul_nonneg hL0.le (by linarith)
      linarith)
    refine ⟨hev.integrable_comp_of_integrable h1.1, le_of_eq_of_le ?_ h1.2⟩
    rw [← hev.map_eq]
    exact (integral_map hev.measurable.aemeasurable
      (by fun_prop : Continuous fun x : ℝ => Real.exp (8 * L * h₀ ^ 2 * x ^ 2)
        ).aestronglyMeasurable).symm
  have hA2 := integral_exp_mul_sq_gaussianReal_le_two (l := 8 * L) (v := r) (by
    have h1 : L * r ≤ L * S :=
      mul_le_mul_of_nonneg_left (by linarith [sq_nonneg h₀, sq_nonneg D]) hL0.le
    have h4 : 0 ≤ L * S := mul_nonneg hL0.le (by linarith)
    linarith)
  set C : ℝ := 4 * Real.exp (3 / (κ₀ * K)) with hC
  have hC0 : 0 ≤ C := by positivity
  set H : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ := fun p =>
    C / 4 * (Real.exp (8 * L * h₀ ^ 2 * p.2.2 (Fin.last N) ^ 2) + Real.exp (8 * L * p.1 ^ 2)) +
      C / 2 * Real.exp (2 * L * W p.2 ^ 2) with hH
  obtain ⟨hHi, hHle⟩ := integrable_and_integral_cavity_majorant_le (μ := gaussianReal 0 r)
    (ν := P) hA1 hA2 hB hC0
  have hpt : ∀ p : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)), F p ≤ H p := by
    rintro ⟨y, d⟩
    have h1 := integral_exp_sq_indexed_last_le_of_coeff (h := h) (y := y) (W := W d) hκ₀ hκ hK0
      hκK hq huc hu0 hud hD d.1 d.2 (fun μ hμ => hwf d.1 d.2 μ hμ)
    rw [← hL, ← hC] at h1
    refine h1.trans ((mul_le_mul_of_nonneg_left (exp_mul_sq_add_sq_le (g := d.2 (Fin.last N))
      (y := y) (W := W d) hL0.le hh ht0 ht1) hC0).trans (le_of_sub_nonneg ?_))
    have e : H (y, d) - C * ((Real.exp (2 * L * W d ^ 2) + (Real.exp (8 * L * h₀ ^ 2 *
          d.2 (Fin.last N) ^ 2) + Real.exp (8 * L * y ^ 2)) / 2) / 2) = 0 := by
      simp only [hH]; ring
    exact e.ge
  have hmeas : Measurable F :=
    measurable_integral_tilted (measurable_indexed_cavity κ h r rBar t hum).neg
      ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.pow_const
        2).div_const K).exp)
  have hFi := hHi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun p => by
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)]
    exact hpt p)
  refine ⟨hFi, (integral_mono hFi hHi hpt).trans (hHle.trans ?_)⟩
  have h1 : Real.exp (3 / (κ₀ * K)) ≤ 2 := by
    have h2 : 3 / (κ₀ * K) ≤ Real.log 2 := by
      have h3 : 3 / (κ₀ * K) ≤ 3 / 16 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hκK
      have h4 := Real.log_two_gt_d9
      linarith
    calc Real.exp (3 / (κ₀ * K)) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 h2
      _ = 2 := Real.exp_log two_pos
  have h2 : 16 ≤ K := by linarith
  rw [hC]
  linarith

/-- **Lemma 3.2.6:** `ν_t (exp (ε² / K)) ≤ K` for every `t ∈ [0, 1]`, where `K` depends only on
`κ₀`, `h₀`, `D` and a bound `R` on the variance `r` of the field `y`. -/
theorem exists_integral_exp_sq_shcherbinaTirozziCavity_last_le (κ₀ h₀ D R : ℝ) (hκ₀ : 0 < κ₀)
    (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ), κ₀ ≤ κ → |h| ≤ h₀ →
      0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u → (∀ x, |deriv u x| ≤ D) →
      let P : Measure (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :=
        (gaussianReal 0 r).prod
          ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
      let F : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ := fun p =>
        ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K)
          ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1 u p.2.1 p.2.2 σ)
      Integrable F P ∧ ∫ p, F p ∂P ≤ K := by
  obtain ⟨K, hK0, -, hK⟩ := exists_integral_exp_sq_shcherbinaTirozziCavity_indexed_last_le
    κ₀ h₀ D R hκ₀ hR
  refine ⟨K, hK0, fun N M κ h t rBar r u hκ hh ht0 ht1 hrr hrR hM huc hu0 hud hD =>
    hK N M κ h t rBar r (fun _ => u) hκ hh ht0 ht1 hrr hrR (by omega)
      (fun _ => huc) (fun _ => hu0) (fun _ => hud) (fun _ => hD)⟩

end SpinGlasses
