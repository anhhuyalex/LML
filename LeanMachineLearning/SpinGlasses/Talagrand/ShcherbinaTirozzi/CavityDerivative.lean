/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.LogSmoothing
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaConfinedPair
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.LastSpinTail

/-!
# The Shcherbina--Tirozzi model: the derivative along the cavity path

Along the cavity path `H_{N,M,t}` of Eq. (3.61) on `ℝ^(N+1)`, write `ε` for the last spin and
`S_k = (N + 1)^{-1/2} (∑_{i < N} g_{k,i} σ_i + √t g_{k,N} ε)`. This file differentiates
`ν_t (f) = 𝔼 ⟨f⟩_t` for a replica observable `f` of polynomial growth (Talagrand, *Spin Glasses*,
Vol. I, Proposition 3.2.1). With `U_k = u' (S_k) ε`, `V_k = (u'' + u'²) (S_k) ε²`, `D` the replica
difference and `P` the two-fresh-replica average,
`ν_t' (f) = (N + 1)⁻¹ ∑_k 𝔼 [D (V_k) / 2 + P (U_k ⊗ U_k)] - 𝔼 [r P (ε ⊗ ε) + r̄ D (ε²) / 2]`.

The proof differentiates under the disorder average and integrates by parts in the couplings
`g_{k,N}` of the last spin and in the field `y`.

## Main declarations

* `SpinGlasses.hasDerivAt_neg_shcherbinaTirozziCavityHamiltonian`: the derivative of `-H` in `t`.
* `SpinGlasses.neg_shcherbinaTirozziCavityHamiltonian_le`,
  `SpinGlasses.le_neg_shcherbinaTirozziCavityHamiltonian_of_norm_le_one`: confinement of `-H`
  and its lower bound on the unit ball, uniformly in `t ∈ [0, 1]`.
* `SpinGlasses.hasDerivAt_integral_integral_pi_shcherbinaTirozziCavity`: Proposition 3.2.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal Topology ENNReal

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- The disorder `(y, (g, g₀))` of the cavity path. -/
local notation "Dis" => ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))

variable {N M : ℕ} {R : Type*} [Fintype R]

/-- The derivative in `t` of the exponent `-H_{N,M,t}` of the cavity path. -/
theorem hasDerivAt_neg_shcherbinaTirozziCavityHamiltonian (κ h r rBar y : ℝ) {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ)
    (σ : ℝ^(N + 1)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun s => -shcherbinaTirozziCavityHamiltonian κ h r rBar s y u g g₀ σ)
      ((∑ k, (Real.sqrt (N + 1))⁻¹ * g k (Fin.last N) / (2 * Real.sqrt t) *
          (deriv u ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
            Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))) * σ (Fin.last N))) +
        (-(y / (2 * Real.sqrt (1 - t))) * σ (Fin.last N) +
          (r - rBar) / 2 * σ (Fin.last N) ^ 2)) t := by
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have hfield : ∀ k : Fin M, HasDerivAt
      (fun s => u ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt s * (g k (Fin.last N) * σ (Fin.last N)))))
      ((Real.sqrt (N + 1))⁻¹ * g k (Fin.last N) / (2 * Real.sqrt t) *
        (deriv u ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
          Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))) * σ (Fin.last N))) t := fun k => by
    have h := (((Real.hasDerivAt_sqrt ht0.ne').mul_const
      (g k (Fin.last N) * σ (Fin.last N))).const_add
        (∑ i : Fin N, g k i.castSucc * σ i.castSucc)).const_mul (Real.sqrt (N + 1))⁻¹
    refine ((hu _).hasDerivAt.comp t h).congr_deriv ?_
    ring
  have hy : HasDerivAt (fun s => σ (Fin.last N) * (Real.sqrt (1 - s) * y))
      (σ (Fin.last N) * (-(1 / (2 * Real.sqrt (1 - t))) * y)) t := by
    have h := (Real.hasDerivAt_sqrt h1t.ne').comp t ((hasDerivAt_id t).const_sub 1)
    simp only [Function.comp_def, mul_neg, mul_one] at h
    exact (h.mul_const y).const_mul _
  have hq : HasDerivAt (fun s => (1 - s) * (r - rBar) * σ (Fin.last N) ^ 2 / 2)
      (-(r - rBar) * σ (Fin.last N) ^ 2 / 2) t := by
    have h := ((((hasDerivAt_id t).const_sub 1).mul_const (r - rBar)).mul_const
      (σ (Fin.last N) ^ 2)).div_const 2
    refine h.congr_deriv ?_
    ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hfield k
  have htot := ((((hsum.const_sub (κ * ‖σ‖ ^ 2)).sub_const (h * ∑ i, g₀ i * σ i)).sub hy).add
    hq).neg
  refine htot.congr_deriv ?_
  ring

/-- The exponent of the cavity path is confined, uniformly in `t ∈ [0, 1]`:
`-H ≤ (|h| ‖g₀‖ + |y|) ‖σ‖ - κ ‖σ‖²`. -/
theorem neg_shcherbinaTirozziCavityHamiltonian_le (κ h y : ℝ) {r rBar t : ℝ}
    (hrr : rBar ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {u : ℝ → ℝ} (hu0 : ∀ x, u x ≤ 0)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) :
    -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ ≤
      (|h| * ∑ i, |g₀ i| + |y|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := by
  have hcoord : ∀ i, |σ i| ≤ ‖σ‖ := fun i => by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le σ i
  have hfield : h * ∑ i, g₀ i * σ i ≤ |h| * (∑ i, |g₀ i|) * ‖σ‖ := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, mul_assoc, Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) (abs_nonneg h)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
  have hlast : σ (Fin.last N) * (Real.sqrt (1 - t) * y) ≤ |y| * ‖σ‖ := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm |y|]
    refine mul_le_mul (hcoord _) (mul_le_of_le_one_left (abs_nonneg y) ?_)
      (by positivity) (norm_nonneg _)
    exact Real.sqrt_le_one.2 (by linarith)
  have hq : 0 ≤ (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) (sq_nonneg _))
      zero_le_two
  have hU : ∑ k, u ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
      Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))) ≤ 0 :=
    Finset.sum_nonpos fun k _ => hu0 _
  rw [shcherbinaTirozziCavityHamiltonian, add_mul]
  linarith

/-- On the unit ball the exponent of the cavity path is bounded below by a quantity which grows
linearly in the disorder. -/
theorem le_neg_shcherbinaTirozziCavityHamiltonian_of_norm_le_one (κ h y : ℝ) {r rBar t : ℝ}
    (hrr : rBar ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {u : ℝ → ℝ} {D : ℝ}
    (hu : Differentiable ℝ u) (hD : ∀ x, |deriv u x| ≤ D)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) {σ : ℝ^(N + 1)} (hσ : ‖σ‖ ≤ 1) :
    -(|κ| + (|h| * ∑ i, |g₀ i| + |y|) + (r - rBar) / 2 +
        ∑ k, (|u 0| + D * ∑ i, |g k i|)) ≤
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hcoord : ∀ i, |σ i| ≤ 1 := fun i =>
    le_trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le σ i) hσ
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 ht1
  have hsN : (Real.sqrt (N + 1))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (le_add_of_nonneg_left (Nat.cast_nonneg N)))
  have hlip : ∀ x, -(|u 0| + D * |x|) ≤ u x := fun x => by
    have h1 := Convex.norm_image_sub_le_of_norm_deriv_le (f := u) (s := Set.univ)
      (fun z _ => hu z) (fun z _ => by simpa only [Real.norm_eq_abs] using hD z) convex_univ
      (Set.mem_univ 0) (Set.mem_univ x)
    rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have h2 := (abs_le.1 h1).1
    have h3 := neg_abs_le (u 0)
    linarith
  have hS : ∀ k : Fin M, |(Real.sqrt (N + 1))⁻¹ *
      ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))| ≤ ∑ i, |g k i| := fun k => by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    refine (mul_le_of_le_one_left (abs_nonneg _) hsN).trans ?_
    rw [Fin.sum_univ_castSucc (fun i => |g k i|)]
    refine (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hcoord _)
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul]
      refine (mul_le_of_le_one_left (by positivity) hs1).trans ?_
      exact mul_le_of_le_one_right (abs_nonneg _) (hcoord _)
  have hU : -(∑ k, (|u 0| + D * ∑ i, |g k i|)) ≤
      ∑ k, u ((Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k i.castSucc * σ i.castSucc) +
        Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun k _ => le_trans
      (neg_le_neg (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hS k) hD0))) (hlip _)
  have hκn : κ * ‖σ‖ ^ 2 ≤ |κ| :=
    (mul_le_mul_of_nonneg_right (le_abs_self κ) (sq_nonneg _)).trans
      (mul_le_of_le_one_right (abs_nonneg κ) (pow_le_one₀ (norm_nonneg _) hσ))
  have hfield : -(|h| * ∑ i, |g₀ i|) ≤ h * ∑ i, g₀ i * σ i := by
    refine (neg_le_neg ?_).trans (neg_abs_le _)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) (abs_nonneg h)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hcoord i)
  have hlast : -|y| ≤ σ (Fin.last N) * (Real.sqrt (1 - t) * y) := by
    refine (neg_le_neg ?_).trans (neg_abs_le _)
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine (mul_le_of_le_one_left (by positivity) (hcoord _)).trans ?_
    exact mul_le_of_le_one_left (abs_nonneg y) (Real.sqrt_le_one.2 (by linarith))
  have hq : (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 ≤ (r - rBar) / 2 := by
    refine div_le_div_of_nonneg_right ?_ zero_le_two
    have h1 : σ (Fin.last N) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hcoord _)
    exact (mul_le_of_le_one_right (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) h1).trans
      (mul_le_of_le_one_left (sub_nonneg.2 hrr) (by linarith))
  rw [shcherbinaTirozziCavityHamiltonian]
  linarith

/-- A polynomial in the absolute values of all disorder variables, which dominates every quantity
of the cavity path. -/
local notation "size " p:arg =>
  (1 + |Prod.fst p| + (∑ k, ∑ i, |Prod.fst (Prod.snd p) k i|) +
    ∑ i, |Prod.snd (Prod.snd p) i|)

/-- The law of the disorder, with a field `y` of variance `r`. -/
local notation "law " r:arg =>
  Measure.prod (gaussianReal 0 r)
    (Measure.prod
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

/-- A polynomial in the absolute values of all disorder variables of the cavity path is
integrable. -/
private theorem integrable_cavity_disorder_pow (r : ℝ≥0) (d : ℕ) :
    Integrable (fun p : Dis => size p ^ d) (law r) := by
  set P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :=
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) with hP
  have hid : ∀ v : ℝ≥0, MemLp (fun x : ℝ => x) d (gaussianReal 0 v) := fun v =>
    memLp_id_gaussianReal (μ := 0) (v := v) d
  have hy : MemLp (fun p : Dis => p.1) d ((gaussianReal 0 r).prod P) :=
    (hid r).comp_measurePreserving measurePreserving_fst
  have hg : ∀ k i, MemLp (fun p : Dis => p.2.1 k i) d ((gaussianReal 0 r).prod P) := fun k i =>
    (hid 1).comp_measurePreserving
      (((measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) i).comp
        (measurePreserving_eval
          (fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) k)).comp
        (measurePreserving_fst.comp measurePreserving_snd))
  have hg0 : ∀ i, MemLp (fun p : Dis => p.2.2 i) d ((gaussianReal 0 r).prod P) := fun i =>
    (hid 1).comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) i).comp
        (measurePreserving_snd.comp measurePreserving_snd))
  have hsum : MemLp (fun p : Dis => 1 + |p.1| + (∑ k, ∑ i, |p.2.1 k i|) + ∑ i, |p.2.2 i|)
      d ((gaussianReal 0 r).prod P) :=
    (((memLp_const 1).add hy.abs).add (memLp_finsetSum _ fun k _ =>
      memLp_finsetSum _ fun i _ => (hg k i).abs)).add
        (memLp_finsetSum _ fun i _ => (hg0 i).abs)
  refine hsum.integrable_norm_pow'.congr (ae_of_all _ fun p => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

/-- The size of the disorder is at least `1`, and it bounds each variable used below. -/
private theorem cavity_disorder_size_bounds (p : Dis) :
    1 ≤ size p ∧ |p.1| ≤ size p ∧ (∑ k, ∑ i, |p.2.1 k i|) ≤ size p ∧
      (∑ i, |p.2.2 i|) ≤ size p ∧ ∀ k, |p.2.1 k (Fin.last N)| ≤ size p := by
  have h1 : 0 ≤ ∑ k, ∑ i, |p.2.1 k i| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : 0 ≤ ∑ i, |p.2.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h3 := abs_nonneg p.1
  refine ⟨by linarith, by linarith, by linarith, by linarith, fun k => ?_⟩
  have h4 : |p.2.1 k (Fin.last N)| ≤ ∑ j, ∑ i, |p.2.1 j i| :=
    (Finset.single_le_sum (f := fun i => |p.2.1 k i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ (Fin.last N))).trans
      (Finset.single_le_sum (f := fun j => ∑ i, |p.2.1 j i|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k))
  linarith

/-- A measurable function of the disorder bounded by a power of its size is integrable. -/
private theorem integrable_of_abs_le_cavity_disorder_pow (r : ℝ≥0) {Φ : Dis → ℝ}
    (hΦ : Measurable Φ) {K : ℝ} {d : ℕ} (hΦb : ∀ p, |Φ p| ≤ K * size p ^ d) :
    Integrable Φ (law r) :=
  ((integrable_cavity_disorder_pow r d).const_mul K).mono' hΦ.aestronglyMeasurable
    (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hΦb p)

/-- The cavity field `S_k` at time `t`. -/
local notation "field⟨" t ", " g ", " k ", " σ "⟩" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

private theorem measurable_cavity_coord (i : Fin (N + 1)) :
    Measurable fun σ : ℝ^(N + 1) => σ i :=
  (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable

private theorem measurable_cavity_field (t : ℝ) (k : Fin M) :
    Measurable fun q : Dis × ℝ^(N + 1) => field⟨t, q.1.2.1, k, q.2⟩ := by
  have hg : ∀ i : Fin (N + 1), Measurable fun q : Dis × ℝ^(N + 1) => q.1.2.1 k i :=
    fun i => (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hσ : ∀ i : Fin (N + 1), Measurable fun q : Dis × ℝ^(N + 1) => q.2 i :=
    fun i => (measurable_cavity_coord i).comp measurable_snd
  exact (((Finset.measurable_sum _ fun i _ => (hg i.castSucc).mul (hσ i.castSucc)).add
    (((hg (Fin.last N)).mul (hσ (Fin.last N))).const_mul (Real.sqrt t))).const_mul _)

/-- The last spin and its square grow at most quadratically. -/
private theorem abs_last_spin_le (x : ℝ^(N + 1)) :
    |x (Fin.last N)| ≤ 1 * (1 + ‖x‖) ^ 2 ∧ |x (Fin.last N) ^ 2| ≤ 1 * (1 + ‖x‖) ^ 2 := by
  have h1 : |x (Fin.last N)| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (Fin.last N)
  refine ⟨by nlinarith [norm_nonneg x], ?_⟩
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [abs_pow, one_mul]
  exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) 2)

section Path

variable (κ h : ℝ) (r : ℝ≥0) (rBar : ℝ) (u : ℝ → ℝ)

/-- The Gibbs measure of the cavity path at time `t` for the disorder `p`. -/
local notation "gibbs⟨" t ", " p "⟩" =>
  Measure.tilted (volume : Measure (ℝ^(N + 1))) fun σ : ℝ^(N + 1) =>
    -shcherbinaTirozziCavityHamiltonian κ h (NNReal.toReal r) rBar t (Prod.fst p) u
      (Prod.fst (Prod.snd p)) (Prod.snd (Prod.snd p)) σ

variable {κ h r rBar u}

private theorem measurable_cavity_exponent (hum : Measurable u) (t : ℝ) :
    Measurable fun q : Dis × ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t q.1.1 u q.1.2.1 q.1.2.2 q.2 :=
  (measurable_shcherbinaTirozziCavityHamiltonian κ h r rBar t hum).neg

private theorem measurable_cavity_exponent_apply (hum : Measurable u) (t : ℝ) (p : Dis) :
    Measurable fun σ : ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1 u p.2.1 p.2.2 σ :=
  (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t p.1 hum p.2.1 p.2.2).neg

private theorem cavity_exponent_le (hrr : rBar ≤ r) (hu0 : ∀ x, u x ≤ 0) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (p : Dis) (σ : ℝ^(N + 1)) :
    -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1 u p.2.1 p.2.2 σ ≤
      0 + (|h| * (∑ i, |p.2.2 i|) + |p.1|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := by
  rw [zero_add]
  exact neg_shcherbinaTirozziCavityHamiltonian_le κ h p.1 hrr ht0 ht1 hu0 p.2.1 p.2.2 σ

/-- The moments of the cavity Gibbs measure are polynomial in the disorder, uniformly in
`t ∈ [0, 1]`. -/
private theorem exists_integral_one_add_norm_pow_cavity_le (hκ : 0 < κ) (hrr : rBar ≤ r)
    (hu1 : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ p : Dis,
      ∫ x, (1 + ‖x‖) ^ k ∂(gibbs⟨t, p⟩) ≤ A * size p ^ k := by
  have hum : Measurable u := hu1.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hrr0 : 0 ≤ (r : ℝ) - rBar := sub_nonneg.2 hrr
  obtain ⟨K, hK0, hK⟩ := exists_integral_one_add_norm_pow_tilted_le
    (volume : Measure (ℝ^(N + 1))) hκ k
  set A0 : ℝ := 1 + κ + (2 * |h| + 2) + ((r : ℝ) - rBar) / 2 + (M * |u 0| + D) with hA0
  have hA00 : 0 ≤ A0 := by positivity
  refine ⟨K * A0 ^ k, by positivity, fun t ht0 ht1 p => ?_⟩
  obtain ⟨hs1, hsy, hsg, hsg0, -⟩ := cavity_disorder_size_bounds p
  set B : ℝ := |h| * (∑ i, |p.2.2 i|) + |p.1| with hB
  have hB0 : 0 ≤ B := add_nonneg (mul_nonneg (abs_nonneg h)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (abs_nonneg _)
  set c : ℝ := |κ| + B + ((r : ℝ) - rBar) / 2 +
    ∑ j, (|u 0| + D * ∑ i, |p.2.1 j i|) with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ ∑ j, (|u 0| + D * ∑ i, |p.2.1 j i|) := Finset.sum_nonneg fun j _ =>
      add_nonneg (abs_nonneg _) (mul_nonneg hD0 (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    positivity
  have h1 := hK _ (measurable_cavity_exponent_apply (κ := κ) (h := h) (r := r) (rBar := rBar)
      hum t p) B c hB0 hc0 (fun x => by
      simpa only [zero_add] using cavity_exponent_le hrr hu0 ht0 ht1 p x)
    (fun x hx => le_neg_shcherbinaTirozziCavityHamiltonian_of_norm_le_one κ h p.1 hrr ht0
      ht1 hu1 hD p.2.1 p.2.2 hx)
  have h2 : 1 + B + c ≤ A0 * size p := by
    have e : ∑ j, (|u 0| + D * ∑ i, |p.2.1 j i|) =
        M * |u 0| + D * ∑ j, ∑ i, |p.2.1 j i| := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hBle : B ≤ (|h| + 1) * size p := by
      rw [add_mul, one_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hsg0 (abs_nonneg h)) hsy
    have hgle : D * (∑ j, ∑ i, |p.2.1 j i|) ≤ D * size p :=
      mul_le_mul_of_nonneg_left hsg hD0
    have hconst : (1 + κ + ((r : ℝ) - rBar) / 2 + M * |u 0|) ≤
        (1 + κ + ((r : ℝ) - rBar) / 2 + M * |u 0|) * size p :=
      le_mul_of_one_le_right (by positivity) hs1
    rw [hc, e, abs_of_pos hκ, hA0]
    linarith
  refine h1.trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 k) hK0

/-- **Differentiation under the disorder average** along the cavity path: for `t ∈ (0, 1)` and a
polynomially growing replica observable `f`, `d/dt 𝔼 ⟨f⟩_t = 𝔼 [D (∂_t (-H_t))]`. -/
private theorem hasDerivAt_cavity_disorder_average (hκ : 0 < κ) (hrr : rBar ≤ r)
    (hu1 : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {f : (R → ℝ^(N + 1)) → ℝ} (hf : Measurable f)
    {C : ℝ} {m : ℕ} (hfb : ∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) :
    let e' : ℝ → Dis → ℝ^(N + 1) → ℝ := fun s p σ =>
      (∑ k, (Real.sqrt (N + 1))⁻¹ * p.2.1 k (Fin.last N) / (2 * Real.sqrt s) *
          (deriv u field⟨s, p.2.1, k, σ⟩ * σ (Fin.last N))) +
        (-(p.1 / (2 * Real.sqrt (1 - s))) * σ (Fin.last N) +
          ((r : ℝ) - rBar) / 2 * σ (Fin.last N) ^ 2)
    Integrable (fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (e' t p)) (law r) ∧
      HasDerivAt (fun s => ∫ p, ∫ σ, f σ ∂(Measure.pi fun _ : R => gibbs⟨s, p⟩) ∂(law r))
        (∫ p, replicaDiff (gibbs⟨t, p⟩) f (e' t p) ∂(law r)) t := by
  intro e'
  have hum : Measurable u := hu1.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hfb 0))
    (Finset.prod_pos fun _ _ => by positivity)
  set U : Set ℝ := Set.Icc (t / 2) ((1 + t) / 2) with hU
  have hUmem : U ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hU01 : ∀ s ∈ U, 0 < s ∧ s < 1 ∧ 0 ≤ s ∧ s ≤ 1 := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hs.1], by linarith [hs.2]⟩
  have hst : ∀ s ∈ U, Real.sqrt (t / 2) ≤ Real.sqrt s ∧ Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - s) :=
    fun s hs => ⟨Real.sqrt_le_sqrt hs.1, Real.sqrt_le_sqrt (by linarith [hs.2])⟩
  have hst0 : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 (by linarith)
  have hs1t0 : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 (by linarith)
  -- uniform polynomial growth of `e' s p` on `U`
  set L0 : ℝ := (M * D) / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2)) +
    ((r : ℝ) - rBar) / 2 + 1 with hL0
  have he'b : ∀ s ∈ U, ∀ (p : Dis) (x : ℝ^(N + 1)),
      |e' s p x| ≤ (L0 * size p) * (1 + ‖x‖) ^ 2 := by
    intro s hs p x
    obtain ⟨hs1, hsy, -, -, hsg⟩ := cavity_disorder_size_bounds p
    obtain ⟨hx1, hx2⟩ := abs_last_spin_le x
    rw [one_mul] at hx1 hx2
    obtain ⟨hts, h1ts⟩ := hst s hs
    have hsN : (Real.sqrt (N + 1))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (le_add_of_nonneg_left (Nat.cast_nonneg N)))
    have hsum : |∑ k : Fin M, (Real.sqrt (N + 1))⁻¹ * p.2.1 k (Fin.last N) / (2 * Real.sqrt s) *
        (deriv u field⟨s, p.2.1, k, x⟩ * x (Fin.last N))| ≤
        ((M * D) / (2 * Real.sqrt (t / 2)) * size p) * (1 + ‖x‖) ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hk : ∀ k : Fin M, |(Real.sqrt (N + 1))⁻¹ * p.2.1 k (Fin.last N) / (2 * Real.sqrt s) *
          (deriv u field⟨s, p.2.1, k, x⟩ * x (Fin.last N))| ≤
          (D / (2 * Real.sqrt (t / 2)) * size p) * (1 + ‖x‖) ^ 2 := fun k => by
        rw [abs_mul, abs_div, abs_mul, abs_mul,
          abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)),
          abs_of_pos (mul_pos two_pos (hst0.trans_le hts))]
        have h1 : (Real.sqrt (N + 1))⁻¹ * |p.2.1 k (Fin.last N)| ≤ size p :=
          (mul_le_of_le_one_left (abs_nonneg _) hsN).trans (hsg k)
        have h2 : size p / (2 * Real.sqrt s) ≤ size p / (2 * Real.sqrt (t / 2)) :=
          div_le_div_of_nonneg_left (by linarith) (mul_pos two_pos hst0)
            (mul_le_mul_of_nonneg_left hts zero_le_two)
        have h3 : |deriv u field⟨s, p.2.1, k, x⟩| * |x (Fin.last N)| ≤ D * (1 + ‖x‖) ^ 2 :=
          mul_le_mul (hD _) hx1 (abs_nonneg _) hD0
        have h4 : (Real.sqrt (N + 1))⁻¹ * |p.2.1 k (Fin.last N)| / (2 * Real.sqrt s) ≤
            size p / (2 * Real.sqrt (t / 2)) :=
          (div_le_div_of_nonneg_right h1 (by positivity)).trans h2
        exact (mul_le_mul h4 h3 (by positivity) (by positivity)).trans_eq (by ring)
      refine (Finset.sum_le_sum fun k _ => hk k).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hy : |-(p.1 / (2 * Real.sqrt (1 - s))) * x (Fin.last N)| ≤
        (1 / (2 * Real.sqrt ((1 - t) / 2)) * size p) * (1 + ‖x‖) ^ 2 := by
      rw [abs_mul, abs_neg, abs_div, abs_of_pos (mul_pos two_pos (hs1t0.trans_le h1ts))]
      have h1 : |p.1| / (2 * Real.sqrt (1 - s)) ≤ size p / (2 * Real.sqrt ((1 - t) / 2)) :=
        (div_le_div_of_nonneg_right hsy (by positivity)).trans
          (div_le_div_of_nonneg_left (by linarith) (mul_pos two_pos hs1t0)
            (mul_le_mul_of_nonneg_left h1ts zero_le_two))
      exact (mul_le_mul h1 hx1 (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have hq : |((r : ℝ) - rBar) / 2 * x (Fin.last N) ^ 2| ≤
        (((r : ℝ) - rBar) / 2 * size p) * (1 + ‖x‖) ^ 2 := by
      have hrr0 : 0 ≤ ((r : ℝ) - rBar) / 2 := div_nonneg (sub_nonneg.2 hrr) zero_le_two
      rw [abs_mul, abs_of_nonneg hrr0]
      exact (mul_le_mul_of_nonneg_left hx2 hrr0).trans
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hrr0 hs1) (by positivity))
    refine (abs_add_le _ _).trans ((add_le_add hsum ((abs_add_le _ _).trans
      (add_le_add hy hq))).trans ?_)
    have : 0 ≤ size p * (1 + ‖x‖) ^ 2 := mul_nonneg (by linarith) (by positivity)
    rw [hL0]
    linarith
  have he'm : ∀ s : ℝ, Measurable fun q : Dis × ℝ^(N + 1) => e' s q.1 q.2 := fun s => by
    have hglast : ∀ k : Fin M, Measurable fun q : Dis × ℝ^(N + 1) => q.1.2.1 k (Fin.last N) :=
      fun k => (measurable_pi_apply (Fin.last N)).comp ((measurable_pi_apply k).comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst)))
    have hy : Measurable fun q : Dis × ℝ^(N + 1) => q.1.1 := measurable_fst.comp measurable_fst
    have hε : Measurable fun q : Dis × ℝ^(N + 1) => q.2 (Fin.last N) :=
      (measurable_cavity_coord (Fin.last N)).comp measurable_snd
    have hsum := Finset.measurable_sum Finset.univ fun k _ =>
      ((((hglast k).const_mul (Real.sqrt (N + 1))⁻¹).div_const (2 * Real.sqrt s)).mul
        ((hdu.comp (measurable_cavity_field s k)).mul hε))
    exact hsum.add ((((hy.div_const (2 * Real.sqrt (1 - s))).neg).mul hε).add
      ((hε.pow_const 2).const_mul (((r : ℝ) - rBar) / 2)))
  obtain ⟨A0, hA00, hA0⟩ := exists_integral_one_add_norm_pow_cavity_le (κ := κ) (h := h) (r := r)
    (rBar := rBar) (u := u) hκ hrr hu1 hu0 hD m
  obtain ⟨A1, hA10, hA1⟩ := exists_integral_one_add_norm_pow_cavity_le (κ := κ) (h := h) (r := r)
    (rBar := rBar) (u := u) hκ hrr hu1 hu0 hD (m + 2)
  have hFm : ∀ s : ℝ, Measurable fun p : Dis =>
      ∫ σ, f σ ∂(Measure.pi fun _ : R => gibbs⟨s, p⟩) := fun s =>
    measurable_integral_pi_tilted_of_sigmaFinite
      (measurable_cavity_exponent (κ := κ) (h := h) (r := r) (rBar := rBar) hum s)
      (hf.comp measurable_snd)
  have hF'm : ∀ s : ℝ, Measurable fun p : Dis => replicaDiff (gibbs⟨s, p⟩) f (e' s p) := fun s =>
    measurable_replicaDiff_tilted_of_sigmaFinite
      (measurable_cavity_exponent (κ := κ) (h := h) (r := r) (rBar := rBar) hum s) (he'm s) hf
  have hFi : Integrable (fun p : Dis => ∫ σ, f σ ∂(Measure.pi fun _ : R => gibbs⟨t, p⟩))
      (law r) := by
    refine integrable_of_abs_le_cavity_disorder_pow r (hFm t)
      (K := C * A0 ^ Fintype.card R) (d := m * Fintype.card R) fun p => ?_
    have h1 := abs_integral_pi_tilted_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum t p)
      (cavity_exponent_le hrr hu0 ht0.le ht1.le p) hfb
    refine h1.trans ?_
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity)
      (hA0 t ht0.le ht1.le p) (Fintype.card R)
    rw [mul_pow, ← pow_mul] at h2
    exact (mul_le_mul_of_nonneg_left h2 hC0).trans_eq (by ring)
  set K1 : ℝ := 2 * Fintype.card R * (C * L0 * A1 ^ (Fintype.card R + 1)) with hK1
  set d1 : ℕ := 1 + (m + 2) * (Fintype.card R + 1) with hd1
  have hF'b : ∀ s ∈ U, ∀ p : Dis,
      |replicaDiff (gibbs⟨s, p⟩) f (e' s p)| ≤ K1 * size p ^ d1 := by
    intro s hs p
    obtain ⟨-, -, hs0, hs1⟩ := hU01 s hs
    have h1 := abs_replicaDiff_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum s p)
      (cavity_exponent_le hrr hu0 hs0 hs1 p) hfb (he'b s hs p)
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity)
      (hA1 s hs0 hs1 p) (Fintype.card R + 1)
    have hL0p : 0 ≤ L0 * size p := by
      have := he'b s hs p 0
      simpa using (abs_nonneg _).trans this
    refine h1.trans ?_
    have h3 : 2 * (Fintype.card R : ℝ) * (C * (L0 * size p) *
        (∫ x, (1 + ‖x‖) ^ (m + 2) ∂(gibbs⟨s, p⟩)) ^ (Fintype.card R + 1)) ≤
        2 * Fintype.card R * (C * (L0 * size p) *
          (A1 * size p ^ (m + 2)) ^ (Fintype.card R + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 hL0p))
        (by positivity)
    refine h3.trans_eq ?_
    rw [mul_pow, ← pow_mul, hK1, hd1, pow_add, pow_one]
    ring
  have hdom : Integrable (fun p : Dis => K1 * size p ^ d1) (law r) :=
    (integrable_cavity_disorder_pow r d1).const_mul K1
  have hpt : ∀ p : Dis, ∀ s ∈ U, HasDerivAt
      (fun q => ∫ σ, f σ ∂(Measure.pi fun _ : R => gibbs⟨q, p⟩))
      (replicaDiff (gibbs⟨s, p⟩) f (e' s p)) s := by
    intro p s hs
    obtain ⟨hs_pos, hs_lt1, -, -⟩ := hU01 s hs
    set U' : Set ℝ := Set.Ioo (t / 4) ((3 + t) / 4) with hU'
    have hU's : U' ∈ 𝓝 s := Ioo_mem_nhds (by linarith [hs.1]) (by linarith [hs.2])
    set L' : ℝ := (M * D) / (2 * Real.sqrt (t / 4)) + 1 / (2 * Real.sqrt ((1 - t) / 4)) +
      ((r : ℝ) - rBar) / 2 + 1
    have hst4 : 0 < Real.sqrt (t / 4) := Real.sqrt_pos.2 (by linarith)
    have hs1t4 : 0 < Real.sqrt ((1 - t) / 4) := Real.sqrt_pos.2 (by linarith)
    have he'b' : ∀ q ∈ U', ∀ x : ℝ^(N + 1), |e' q p x| ≤ (L' * size p) * (1 + ‖x‖) ^ 2 := by
      intro q hq x
      obtain ⟨hs1, hsy, -, -, hsg⟩ := cavity_disorder_size_bounds p
      obtain ⟨hx1, hx2⟩ := abs_last_spin_le x
      rw [one_mul] at hx1 hx2
      have hts : Real.sqrt (t / 4) ≤ Real.sqrt q := Real.sqrt_le_sqrt hq.1.le
      have h1ts : Real.sqrt ((1 - t) / 4) ≤ Real.sqrt (1 - q) :=
        Real.sqrt_le_sqrt (by linarith [hq.2])
      have hsN : (Real.sqrt (N + 1))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (le_add_of_nonneg_left (Nat.cast_nonneg N)))
      have hsum : |∑ k : Fin M, (Real.sqrt (N + 1))⁻¹ * p.2.1 k (Fin.last N) / (2 * Real.sqrt q) *
          (deriv u field⟨q, p.2.1, k, x⟩ * x (Fin.last N))| ≤
          ((M * D) / (2 * Real.sqrt (t / 4)) * size p) * (1 + ‖x‖) ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hk : ∀ k : Fin M, |(Real.sqrt (N + 1))⁻¹ * p.2.1 k (Fin.last N) / (2 * Real.sqrt q) *
            (deriv u field⟨q, p.2.1, k, x⟩ * x (Fin.last N))| ≤
            (D / (2 * Real.sqrt (t / 4)) * size p) * (1 + ‖x‖) ^ 2 := fun k => by
          rw [abs_mul, abs_div, abs_mul, abs_mul,
            abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)),
            abs_of_pos (mul_pos two_pos (hst4.trans_le hts))]
          have h1 : (Real.sqrt (N + 1))⁻¹ * |p.2.1 k (Fin.last N)| ≤ size p :=
            (mul_le_of_le_one_left (abs_nonneg _) hsN).trans (hsg k)
          have h2 : size p / (2 * Real.sqrt q) ≤ size p / (2 * Real.sqrt (t / 4)) :=
            div_le_div_of_nonneg_left (by linarith) (mul_pos two_pos hst4)
              (mul_le_mul_of_nonneg_left hts zero_le_two)
          have h3 : |deriv u field⟨q, p.2.1, k, x⟩| * |x (Fin.last N)| ≤ D * (1 + ‖x‖) ^ 2 :=
            mul_le_mul (hD _) hx1 (abs_nonneg _) hD0
          have h4 : (Real.sqrt (N + 1))⁻¹ * |p.2.1 k (Fin.last N)| / (2 * Real.sqrt q) ≤
              size p / (2 * Real.sqrt (t / 4)) :=
            (div_le_div_of_nonneg_right h1 (by positivity)).trans h2
          exact (mul_le_mul h4 h3 (by positivity) (by positivity)).trans_eq (by ring)
        refine (Finset.sum_le_sum fun k _ => hk k).trans_eq ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      have hy : |-(p.1 / (2 * Real.sqrt (1 - q))) * x (Fin.last N)| ≤
          (1 / (2 * Real.sqrt ((1 - t) / 4)) * size p) * (1 + ‖x‖) ^ 2 := by
        rw [abs_mul, abs_neg, abs_div, abs_of_pos (mul_pos two_pos (hs1t4.trans_le h1ts))]
        have h1 : |p.1| / (2 * Real.sqrt (1 - q)) ≤ size p / (2 * Real.sqrt ((1 - t) / 4)) :=
          (div_le_div_of_nonneg_right hsy (by positivity)).trans
            (div_le_div_of_nonneg_left (by linarith) (mul_pos two_pos hs1t4)
              (mul_le_mul_of_nonneg_left h1ts zero_le_two))
        exact (mul_le_mul h1 hx1 (abs_nonneg _) (by positivity)).trans_eq (by ring)
      have hqq : |((r : ℝ) - rBar) / 2 * x (Fin.last N) ^ 2| ≤
          (((r : ℝ) - rBar) / 2 * size p) * (1 + ‖x‖) ^ 2 := by
        have hrr0 : 0 ≤ ((r : ℝ) - rBar) / 2 := div_nonneg (sub_nonneg.2 hrr) zero_le_two
        rw [abs_mul, abs_of_nonneg hrr0]
        exact (mul_le_mul_of_nonneg_left hx2 hrr0).trans
          (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hrr0 hs1) (by positivity))
      refine (abs_add_le _ _).trans ((add_le_add hsum ((abs_add_le _ _).trans
        (add_le_add hy hqq))).trans ?_)
      have : 0 ≤ size p * (1 + ‖x‖) ^ 2 := mul_nonneg (by linarith) (by positivity)
      linarith
    have hmain := hasDerivAt_integral_pi_tilted_of_confining_replicaDiff (μ := volume)
      (R := R) hκ hU's (e := fun q x =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar q p.1 u p.2.1 p.2.2 x)
      (e' := fun q x => e' q p x)
      (fun q _ => measurable_cavity_exponent_apply hum q p)
      ((he'm s).comp (measurable_const.prodMk measurable_id))
      (fun q hq x => cavity_exponent_le hrr hu0 (by linarith [hq.1]) (by linarith [hq.2]) p x)
      he'b' (fun x q hq => hasDerivAt_neg_shcherbinaTirozziCavityHamiltonian κ h r rBar p.1 hu1
        p.2.1 p.2.2 x (by linarith [hq.1]) (by linarith [hq.2]))
      (Ψ := fun _ => f) (Ψ' := fun _ _ => 0) (fun _ _ => hf) measurable_const
      (fun _ _ => hfb) (fun _ _ σ => by rw [abs_zero]; exact mul_nonneg hC0 (by positivity))
      (fun _ q _ => hasDerivAt_const q _)
    simpa only [integral_zero, zero_add] using hmain
  have htU : t ∈ U := mem_of_mem_nhds hUmem
  have hF'i : Integrable (fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (e' t p)) (law r) :=
    hdom.mono' (hF'm t).aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hF'b t htU p)
  refine ⟨hF'i, (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s p => ∫ σ, f σ ∂(Measure.pi fun _ : R => gibbs⟨s, p⟩))
    (F' := fun s p => replicaDiff (gibbs⟨s, p⟩) f (e' s p))
    (bound := fun p => K1 * size p ^ d1) hUmem
    (Filter.eventually_of_mem hUmem fun s _ => (hFm s).aestronglyMeasurable)
    hFi (hF'm t).aestronglyMeasurable
    (ae_of_all _ fun p s hs => by simpa only [Real.norm_eq_abs] using hF'b s hs p)
    hdom (ae_of_all _ hpt)).2⟩

/-- **Integration by parts in the coupling `g_{k,N}`** of the `k`-th constraint to the last spin:
`𝔼 [g_{k,N} D (u'(S_k) ε)] = √t / √(N + 1) · 𝔼 [D ((u'' + u'²)(S_k) ε²) + 2 P (U_k ⊗ U_k)]`. -/
private theorem integral_cavity_coupling_ibp [LinearOrder R] (hκ : 0 < κ) (hrr : rBar ≤ r)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u)) (hu0 : ∀ x, u x ≤ 0)
    {D D₂ : ℝ} (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {f : (R → ℝ^(N + 1)) → ℝ} (hf : Measurable f)
    {C : ℝ} {m : ℕ} (hfb : ∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) (k : Fin M) :
    let U : Dis → ℝ^(N + 1) → ℝ := fun p σ => deriv u field⟨t, p.2.1, k, σ⟩ * σ (Fin.last N)
    let V : Dis → ℝ^(N + 1) → ℝ := fun p σ =>
      (deriv (deriv u) field⟨t, p.2.1, k, σ⟩ + deriv u field⟨t, p.2.1, k, σ⟩ ^ 2) *
        σ (Fin.last N) ^ 2
    Integrable (fun p : Dis => p.2.1 k (Fin.last N) * replicaDiff (gibbs⟨t, p⟩) f (U p)) (law r) ∧
      Integrable (fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (V p)) (law r) ∧
      Integrable (fun p : Dis => replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b))
        (law r) ∧
      ∫ p, p.2.1 k (Fin.last N) * replicaDiff (gibbs⟨t, p⟩) f (U p) ∂(law r) =
        (Real.sqrt (N + 1))⁻¹ * Real.sqrt t *
          ((∫ p, replicaDiff (gibbs⟨t, p⟩) f (V p) ∂(law r)) +
            2 * ∫ p, replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b) ∂(law r)) := by
  intro U V
  have hum : Measurable u := hu1.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hddu : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hD₂0 : 0 ≤ D₂ := (abs_nonneg _).trans (hD₂ 0)
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hfb 0))
    (Finset.prod_pos fun _ _ => by positivity)
  set c : ℝ := (Real.sqrt (N + 1))⁻¹ * Real.sqrt t with hc
  have hεm : Measurable fun q : Dis × ℝ^(N + 1) => q.2 (Fin.last N) :=
    (measurable_cavity_coord (Fin.last N)).comp measurable_snd
  have hUm : Measurable fun q : Dis × ℝ^(N + 1) => U q.1 q.2 :=
    (hdu.comp (measurable_cavity_field t k)).mul hεm
  have hVm : Measurable fun q : Dis × ℝ^(N + 1) => V q.1 q.2 :=
    ((hddu.comp (measurable_cavity_field t k)).add
      ((hdu.comp (measurable_cavity_field t k)).pow_const 2)).mul (hεm.pow_const 2)
  have hUKm : Measurable fun q : Dis × (ℝ^(N + 1) × ℝ^(N + 1)) => U q.1 q.2.1 * U q.1 q.2.2 := by
    have h1 : Measurable fun q : Dis × (ℝ^(N + 1) × ℝ^(N + 1)) => (q.1, q.2.1) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have h2 : Measurable fun q : Dis × (ℝ^(N + 1) × ℝ^(N + 1)) => (q.1, q.2.2) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    exact (hUm.comp h1).mul (hUm.comp h2)
  have hUb : ∀ (p : Dis) (x : ℝ^(N + 1)), |U p x| ≤ D * (1 + ‖x‖) ^ 2 := fun p x => by
    rw [show U p x = _ from rfl, abs_mul]
    exact (mul_le_mul (hD _) (abs_last_spin_le x).1 (abs_nonneg _) hD0).trans_eq (by ring)
  have hVb : ∀ (p : Dis) (x : ℝ^(N + 1)), |V p x| ≤ (D₂ + D ^ 2) * (1 + ‖x‖) ^ 2 := fun p x => by
    rw [show V p x = _ from rfl, abs_mul]
    have h1 : |deriv (deriv u) field⟨t, p.2.1, k, x⟩ + deriv u field⟨t, p.2.1, k, x⟩ ^ 2| ≤
        D₂ + D ^ 2 :=
      (abs_add_le _ _).trans (add_le_add (hD₂ _)
        (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hD _) 2))
    exact (mul_le_mul h1 (abs_last_spin_le x).2 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  obtain ⟨A1, hA10, hA1⟩ := exists_integral_one_add_norm_pow_cavity_le (κ := κ) (h := h) (r := r)
    (rBar := rBar) (u := u) hκ hrr hu1 hu0 hD (m + 2)
  obtain ⟨A2, hA20, hA2⟩ := exists_integral_one_add_norm_pow_cavity_le (κ := κ) (h := h) (r := r)
    (rBar := rBar) (u := u) hκ hrr hu1 hu0 hD (m + (2 + 2))
  have hDUm : Measurable fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (U p) :=
    measurable_replicaDiff_tilted_of_sigmaFinite (measurable_cavity_exponent hum t) hUm hf
  have hDVm : Measurable fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (V p) :=
    measurable_replicaDiff_tilted_of_sigmaFinite (measurable_cavity_exponent hum t) hVm hf
  have hPUm : Measurable fun p : Dis =>
      replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b) :=
    measurable_replicaPairAverage_tilted_of_sigmaFinite (measurable_cavity_exponent hum t) hUKm hf
  have hgkm : Measurable fun p : Dis => p.2.1 k (Fin.last N) :=
    (measurable_pi_apply (Fin.last N)).comp
      ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd))
  have hIgU : Integrable (fun p : Dis => p.2.1 k (Fin.last N) *
      replicaDiff (gibbs⟨t, p⟩) f (U p)) (law r) := by
    refine integrable_of_abs_le_cavity_disorder_pow r (hgkm.mul hDUm)
      (K := 2 * Fintype.card R * (C * D * A1 ^ (Fintype.card R + 1)))
      (d := 1 + (m + 2) * (Fintype.card R + 1)) fun p => ?_
    obtain ⟨-, -, -, -, hsg⟩ := cavity_disorder_size_bounds p
    have h1 := abs_replicaDiff_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum t p) (cavity_exponent_le hrr hu0 ht0 ht1 p) hfb (hUb p)
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) (hA1 t ht0 ht1 p)
      (Fintype.card R + 1)
    rw [abs_mul]
    refine (mul_le_mul (hsg k) (h1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)))
      (abs_nonneg _) (by linarith [abs_nonneg (p.2.1 k (Fin.last N))])).trans_eq ?_
    rw [mul_pow, ← pow_mul, pow_add, pow_one]
    ring
  have hIDV : Integrable (fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (V p)) (law r) := by
    refine integrable_of_abs_le_cavity_disorder_pow r hDVm
      (K := 2 * Fintype.card R * (C * (D₂ + D ^ 2) * A1 ^ (Fintype.card R + 1)))
      (d := (m + 2) * (Fintype.card R + 1)) fun p => ?_
    have h1 := abs_replicaDiff_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum t p) (cavity_exponent_le hrr hu0 ht0 ht1 p) hfb (hVb p)
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) (hA1 t ht0 ht1 p)
      (Fintype.card R + 1)
    refine (h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
      (by positivity))).trans_eq ?_
    rw [mul_pow, ← pow_mul]
    ring
  have hIPU : Integrable (fun p : Dis =>
      replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b)) (law r) := by
    refine integrable_of_abs_le_cavity_disorder_pow r hPUm
      (K := 3 * (Fintype.card R + 1) ^ 2 * (C * D ^ 2 * A2 ^ (Fintype.card R + 2)))
      (d := (m + (2 + 2)) * (Fintype.card R + 2)) fun p => ?_
    have h1 := abs_replicaPairAverage_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum t p) (cavity_exponent_le hrr hu0 ht0 ht1 p) hfb (hUb p)
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) (hA2 t ht0 ht1 p)
      (Fintype.card R + 2)
    refine (h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
      (by positivity))).trans_eq ?_
    rw [mul_pow, ← pow_mul]
    ring
  -- differentiate along `g_{k,N}` for fixed other variables, then apply matrix Stein
  have hder : ∀ (y : ℝ) (g₀ : Fin (N + 1) → ℝ) (g : Fin M → Fin (N + 1) → ℝ),
      HasDerivAt (fun z => replicaDiff (gibbs⟨t, (y, (update g k (update (g k) (Fin.last N) z), g₀))⟩)
        f (U (y, (update g k (update (g k) (Fin.last N) z), g₀))))
      (c * (replicaDiff (gibbs⟨t, (y, (g, g₀))⟩) f (fun x =>
          deriv (deriv u) field⟨t, g, k, x⟩ * x (Fin.last N) ^ 2 + U (y, (g, g₀)) x ^ 2) +
        2 * replicaPairAverage (gibbs⟨t, (y, (g, g₀))⟩) f
          (fun a b => U (y, (g, g₀)) a * U (y, (g, g₀)) b)))
      (g k (Fin.last N)) := by
    intro y g₀ g
    set z0 : ℝ := g k (Fin.last N)
    set g_z : ℝ → Fin M → Fin (N + 1) → ℝ := fun z => update g k (update (g k) (Fin.last N) z)
    have hgz0 : g_z z0 = g := by simp [g_z, z0]
    have hed : ∀ (x : ℝ^(N + 1)) (z : ℝ), HasDerivAt
        (fun q => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u (g_z q) g₀ x)
        (c * U (y, (g_z z, g₀)) x) z := by
      intro x z
      have hterm : ∀ j : Fin M, HasDerivAt
          (fun q => u field⟨t, g_z q, j, x⟩)
          (if j = k then c * U (y, (g_z z, g₀)) x else 0) z := fun j => by
        rcases eq_or_ne j k with rfl | hjk
        · simp only [ite_true]
          have hcast : ∀ q (i : Fin N), g_z q j i.castSucc = g j i.castSucc := fun q i => by
            simp [g_z, Fin.castSucc_ne_last]
          have hlast : ∀ q, g_z q j (Fin.last N) = q := fun q => by simp [g_z]
          simp_rw [hcast, hlast]
          have hlin : HasDerivAt (fun q : ℝ => (Real.sqrt (N + 1))⁻¹ *
              ((∑ i : Fin N, g j i.castSucc * x i.castSucc) + Real.sqrt t * (q * x (Fin.last N))))
              (c * x (Fin.last N)) z := by
            have h1 := (((hasDerivAt_id z).mul_const (x (Fin.last N))).const_mul
              (Real.sqrt t)).const_add (∑ i : Fin N, g j i.castSucc * x i.castSucc)
            refine (h1.const_mul (Real.sqrt (N + 1))⁻¹).congr_deriv ?_
            rw [hc]; ring
          refine ((hu1 _).hasDerivAt.comp z hlin).congr_deriv ?_
          change deriv u _ * (c * x (Fin.last N)) = c * (deriv u _ * x (Fin.last N))
          simp only [hcast, hlast]
          ring
        · simp only [hjk, ite_false]
          have hconst : ∀ q, g_z q j = g j := fun q => by simp [g_z, hjk]
          simp_rw [hconst]
          exact hasDerivAt_const z _
      have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hterm j
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
      have hconst : ∀ q, ∑ i, g₀ i * x i = ∑ i, g₀ i * x i := fun _ => rfl
      have htot := ((((hsum.const_sub (κ * ‖x‖ ^ 2)).sub_const (h * ∑ i, g₀ i * x i)).sub_const
        (x (Fin.last N) * (Real.sqrt (1 - t) * y))).add_const
        ((1 - t) * ((r : ℝ) - rBar) * x (Fin.last N) ^ 2 / 2)).neg
      refine htot.congr_deriv ?_
      ring
    have hhd : ∀ (x : ℝ^(N + 1)) (z : ℝ), HasDerivAt (fun q => U (y, (g_z q, g₀)) x)
        (c * (deriv (deriv u) field⟨t, g_z z, k, x⟩ * x (Fin.last N) ^ 2)) z := by
      intro x z
      have hcast : ∀ q (i : Fin N), g_z q k i.castSucc = g k i.castSucc := fun q i => by
        simp [g_z, Fin.castSucc_ne_last]
      have hlast : ∀ q, g_z q k (Fin.last N) = q := fun q => by simp [g_z]
      change HasDerivAt (fun q => deriv u field⟨t, g_z q, k, x⟩ * x (Fin.last N)) _ z
      simp_rw [hcast, hlast]
      have hlin : HasDerivAt (fun q : ℝ => (Real.sqrt (N + 1))⁻¹ *
          ((∑ i : Fin N, g k i.castSucc * x i.castSucc) + Real.sqrt t * (q * x (Fin.last N))))
          (c * x (Fin.last N)) z := by
        have h1 := (((hasDerivAt_id z).mul_const (x (Fin.last N))).const_mul
          (Real.sqrt t)).const_add (∑ i : Fin N, g k i.castSucc * x i.castSucc)
        refine (h1.const_mul (Real.sqrt (N + 1))⁻¹).congr_deriv ?_
        rw [hc]; ring
      refine (((hu2 _).hasDerivAt.comp z hlin).mul_const (x (Fin.last N))).congr_deriv ?_
      simp only [hcast, hlast]
      ring
    have h2m : Measurable fun x : ℝ^(N + 1) =>
        deriv (deriv u) field⟨t, g_z z0, k, x⟩ * x (Fin.last N) ^ 2 := by
      rw [hgz0]
      exact (hddu.comp ((measurable_cavity_field t k).comp
        ((measurable_const (a := (y, (g, g₀)))).prodMk measurable_id))).mul
        ((measurable_cavity_coord (Fin.last N)).pow_const 2)
    have hmain := hasDerivAt_replicaDiff_tilted_of_confining (μ := volume) (R := R) hκ
      (s := Set.univ) Filter.univ_mem
      (e := fun q x => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u (g_z q) g₀ x)
      (h := fun q x => U (y, (g_z q, g₀)) x)
      (h₂ := fun q x => deriv (deriv u) field⟨t, g_z q, k, x⟩ * x (Fin.last N) ^ 2)
      (c := c) (t := z0)
      (fun q _ => measurable_cavity_exponent_apply hum t (y, (g_z q, g₀)))
      (fun q _ => hUm.comp ((measurable_const (a := (y, (g_z q, g₀)))).prodMk measurable_id))
      h2m (A := 0) (B := |h| * (∑ i, |g₀ i|) + |y|) (L := max D D₂) (n := 2)
      (fun q _ x => cavity_exponent_le hrr hu0 ht0 ht1 (y, (g_z q, g₀)) x)
      (fun q _ x => (hUb (y, (g_z q, g₀)) x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      (fun q _ x => by
        rw [abs_mul]
        exact (mul_le_mul (hD₂ _) (abs_last_spin_le x).2 (abs_nonneg _) hD₂0).trans
          (by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (fun x q _ => hed x q) (fun x q _ => hhd x q) hf hfb
    simpa only [hgz0] using hmain
  have hRHS_eq : ∀ p : Dis, c * (replicaDiff (gibbs⟨t, p⟩) f (fun x =>
      deriv (deriv u) field⟨t, p.2.1, k, x⟩ * x (Fin.last N) ^ 2 + U p x ^ 2) +
        2 * replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b)) =
      c * (replicaDiff (gibbs⟨t, p⟩) f (V p) +
        2 * replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b)) := fun p => by
    have heq : (fun x : ℝ^(N + 1) =>
        deriv (deriv u) field⟨t, p.2.1, k, x⟩ * x (Fin.last N) ^ 2 + U p x ^ 2) = V p := by
      funext x; change _ + (deriv u _ * x (Fin.last N)) ^ 2 = _; ring
    rw [heq]
  have hIRHS : Integrable (fun p : Dis => c * (replicaDiff (gibbs⟨t, p⟩) f (V p) +
      2 * replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b))) (law r) :=
    (hIDV.add (hIPU.const_mul 2)).const_mul c
  refine ⟨hIgU, hIDV, hIPU, ?_⟩
  -- Fubini over `y`, then `g₀`, then Stein in `g`
  set Pg : Measure (Fin M → Fin (N + 1) → ℝ) :=
    Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  set Pg0 : Measure (Fin (N + 1) → ℝ) := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  have hstein : ∫ p, p.2.1 k (Fin.last N) * replicaDiff (gibbs⟨t, p⟩) f (U p) ∂(law r) =
      ∫ p, c * (replicaDiff (gibbs⟨t, p⟩) f (V p) +
        2 * replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => U p a * U p b)) ∂(law r) := by
    rw [integral_prod _ hIgU, integral_prod _ hIRHS]
    refine integral_congr_ae ?_
    filter_upwards [hIgU.prod_right_ae, hIRHS.prod_right_ae] with y hy1 hy2
    rw [integral_prod_symm _ hy1, integral_prod_symm _ hy2]
    refine integral_congr_ae ?_
    filter_upwards [hy1.prod_left_ae, hy2.prod_left_ae] with g₀ hg1 hg2
    have h := integral_apply_apply_mul_pi_pi_gaussianReal_eq
      (fun _ : Fin M => fun _ : Fin (N + 1) => (1 : ℝ≥0)) k (Fin.last N)
      (G := fun g => replicaDiff (gibbs⟨t, (y, (g, g₀))⟩) f (U (y, (g, g₀))))
      (G' := fun g => c * (replicaDiff (gibbs⟨t, (y, (g, g₀))⟩) f (V (y, (g, g₀))) +
        2 * replicaPairAverage (gibbs⟨t, (y, (g, g₀))⟩) f
          (fun a b => U (y, (g, g₀)) a * U (y, (g, g₀)))))
      (fun g => by rw [← hRHS_eq (y, (g, g₀))]; exact hder y g₀ g) hg1 hg2
    simpa only [NNReal.coe_one, one_mul] using h
  rw [hstein, integral_const_mul, integral_add hIDV (hIPU.const_mul 2), integral_const_mul]

/-- **Integration by parts in the field `y`** of variance `r`:
`𝔼 [y D (ε)] = r √(1 - t) 𝔼 [D (ε²) + 2 P (ε ⊗ ε)]`. -/
private theorem integral_cavity_field_ibp [LinearOrder R] (hκ : 0 < κ) (hrr : rBar ≤ r)
    (hu1 : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {f : (R → ℝ^(N + 1)) → ℝ} (hf : Measurable f)
    {C : ℝ} {m : ℕ} (hfb : ∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) :
    Integrable (fun p : Dis => p.1 * replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N)))
      (law r) ∧
      Integrable (fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N) ^ 2))
        (law r) ∧
      Integrable (fun p : Dis => replicaPairAverage (gibbs⟨t, p⟩) f
        (fun a b => a (Fin.last N) * b (Fin.last N))) (law r) ∧
      ∫ p, p.1 * replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N)) ∂(law r) =
        (r : ℝ) * Real.sqrt (1 - t) *
          ((∫ p, replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N) ^ 2) ∂(law r)) +
            2 * ∫ p, replicaPairAverage (gibbs⟨t, p⟩) f
              (fun a b => a (Fin.last N) * b (Fin.last N)) ∂(law r)) := by
  have hum : Measurable u := hu1.continuous.measurable
  set c : ℝ := Real.sqrt (1 - t) with hc
  have hεm : Measurable fun σ : ℝ^(N + 1) => σ (Fin.last N) := measurable_cavity_coord (Fin.last N)
  have hε2m : Measurable fun σ : ℝ^(N + 1) => σ (Fin.last N) ^ 2 := hεm.pow_const 2
  have hεKm : Measurable fun q : Dis × (ℝ^(N + 1) × ℝ^(N + 1)) =>
      q.2.1 (Fin.last N) * q.2.2 (Fin.last N) :=
    (hεm.comp (measurable_fst.comp measurable_snd)).mul
      (hεm.comp (measurable_snd.comp measurable_snd))
  have hεb : ∀ x : ℝ^(N + 1), |x (Fin.last N)| ≤ 1 * (1 + ‖x‖) ^ 2 :=
    fun x => (abs_last_spin_le x).1
  have hε2b : ∀ x : ℝ^(N + 1), |x (Fin.last N) ^ 2| ≤ 1 * (1 + ‖x‖) ^ 2 :=
    fun x => (abs_last_spin_le x).2
  obtain ⟨A1, hA10, hA1⟩ := exists_integral_one_add_norm_pow_cavity_le (κ := κ) (h := h) (r := r)
    (rBar := rBar) (u := u) hκ hrr hu1 hu0 hD (m + 2)
  obtain ⟨A2, hA20, hA2⟩ := exists_integral_one_add_norm_pow_cavity_le (κ := κ) (h := h) (r := r)
    (rBar := rBar) (u := u) hκ hrr hu1 hu0 hD (m + (2 + 2))
  have hDεm : Measurable fun p : Dis => replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N)) :=
    measurable_replicaDiff_tilted_of_sigmaFinite (measurable_cavity_exponent hum t)
      (hεm.comp measurable_snd) hf
  have hDε2m : Measurable fun p : Dis =>
      replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N) ^ 2) :=
    measurable_replicaDiff_tilted_of_sigmaFinite (measurable_cavity_exponent hum t)
      (hε2m.comp measurable_snd) hf
  have hPεm : Measurable fun p : Dis =>
      replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => a (Fin.last N) * b (Fin.last N)) :=
    measurable_replicaPairAverage_tilted_of_sigmaFinite (measurable_cavity_exponent hum t) hεKm hf
  have hIy : Integrable (fun p : Dis => p.1 *
      replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N))) (law r) := by
    refine integrable_of_abs_le_cavity_disorder_pow r (measurable_fst.mul hDεm)
      (K := 2 * Fintype.card R * (C * 1 * A1 ^ (Fintype.card R + 1)))
      (d := 1 + (m + 2) * (Fintype.card R + 1)) fun p => ?_
    obtain ⟨-, hsy, -, -, -⟩ := cavity_disorder_size_bounds p
    have h1 := abs_replicaDiff_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum t p) (cavity_exponent_le hrr hu0 ht0 ht1 p) hfb hεb
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) (hA1 t ht0 ht1 p)
      (Fintype.card R + 1)
    rw [abs_mul]
    refine (mul_le_mul hsy (h1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)))
      (abs_nonneg _) (by linarith [abs_nonneg p.1])).trans_eq ?_
    rw [mul_pow, ← pow_mul, pow_add, pow_one]
    ring
  have hIDε2 : Integrable (fun p : Dis =>
      replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N) ^ 2)) (law r) := by
    refine integrable_of_abs_le_cavity_disorder_pow r hDε2m
      (K := 2 * Fintype.card R * (C * 1 * A1 ^ (Fintype.card R + 1)))
      (d := (m + 2) * (Fintype.card R + 1)) fun p => ?_
    have h1 := abs_replicaDiff_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum t p) (cavity_exponent_le hrr hu0 ht0 ht1 p) hfb hε2b
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) (hA1 t ht0 ht1 p)
      (Fintype.card R + 1)
    refine (h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
      (by positivity))).trans_eq ?_
    rw [mul_pow, ← pow_mul]
    ring
  have hIPε : Integrable (fun p : Dis =>
      replicaPairAverage (gibbs⟨t, p⟩) f (fun a b => a (Fin.last N) * b (Fin.last N))) (law r) := by
    refine integrable_of_abs_le_cavity_disorder_pow r hPεm
      (K := 3 * (Fintype.card R + 1) ^ 2 * (C * 1 ^ 2 * A2 ^ (Fintype.card R + 2)))
      (d := (m + (2 + 2)) * (Fintype.card R + 2)) fun p => ?_
    have h1 := abs_replicaPairAverage_le_of_confining (μ := volume) hκ
      (measurable_cavity_exponent_apply hum t p) (cavity_exponent_le hrr hu0 ht0 ht1 p) hfb hεb
    have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) (hA2 t ht0 ht1 p)
      (Fintype.card R + 2)
    refine (h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
      (by positivity))).trans_eq ?_
    rw [mul_pow, ← pow_mul]
    ring
  -- differentiate in `y` for fixed `(g, g₀)`
  have hder : ∀ (d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) (y : ℝ),
      HasDerivAt (fun q => replicaDiff (gibbs⟨t, (q, d)⟩) f (fun σ => σ (Fin.last N)))
        (c * (replicaDiff (gibbs⟨t, (y, d)⟩) f (fun σ => σ (Fin.last N) ^ 2) +
          2 * replicaPairAverage (gibbs⟨t, (y, d)⟩) f
            (fun a b => a (Fin.last N) * b (Fin.last N)))) y := by
    intro d y
    set U_y : Set ℝ := Set.Ioo (y - 1) (y + 1)
    have hUy : U_y ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
    have hed : ∀ (x : ℝ^(N + 1)) (z : ℝ), HasDerivAt
        (fun q => -shcherbinaTirozziCavityHamiltonian κ h r rBar t q u d.1 d.2 x)
        (c * x (Fin.last N)) z := fun x z => by
      have hy : HasDerivAt (fun q => x (Fin.last N) * (c * q))
          (x (Fin.last N) * (c * 1)) z := ((hasDerivAt_id z).const_mul c).const_mul _
      have htot := (((((hasDerivAt_const z (κ * ‖x‖ ^ 2)).sub_const _).sub_const _).sub hy).add_const
        _).neg
      refine htot.congr_deriv ?_
      ring
    have hmain := hasDerivAt_replicaDiff_tilted_of_confining (μ := volume) (R := R) hκ hUy
      (e := fun q x => -shcherbinaTirozziCavityHamiltonian κ h r rBar t q u d.1 d.2 x)
      (h := fun _ x => x (Fin.last N)) (h₂ := fun _ _ => 0) (c := c)
      (fun q _ => measurable_cavity_exponent_apply hum t (q, d))
      (fun _ _ => hεm) measurable_const
      (A := 0) (B := |h| * (∑ i, |d.2 i|) + (|y| + 1)) (L := 1) (n := 2)
      (fun q hq x => (cavity_exponent_le hrr hu0 ht0 ht1 (q, d) x).trans (by
        have hqy : |q| ≤ |y| + 1 := by
          rw [abs_le]; constructor <;> linarith [hq.1, hq.2, neg_abs_le y, le_abs_self y]
        have := mul_le_mul_of_nonneg_right (add_le_add_left hqy (|h| * ∑ i, |d.2 i|))
          (norm_nonneg x)
        linarith))
      (fun _ _ => hεb) (fun _ _ x => by rw [abs_zero]; positivity)
      (fun x q _ => hed x q) (fun x q _ => by simpa using hasDerivAt_const q (x (Fin.last N)))
      hf hfb
    simpa only [zero_add] using hmain
  have hIRHS : Integrable (fun p : Dis => c *
      (replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N) ^ 2) +
        2 * replicaPairAverage (gibbs⟨t, p⟩) f
          (fun a b => a (Fin.last N) * b (Fin.last N)))) (law r) :=
    (hIDε2.add (hIPε.const_mul 2)).const_mul c
  refine ⟨hIy, hIDε2, hIPε, ?_⟩
  have hstein : ∫ p, p.1 * replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N)) ∂(law r) =
      (r : ℝ) * ∫ p, c * (replicaDiff (gibbs⟨t, p⟩) f (fun σ => σ (Fin.last N) ^ 2) +
        2 * replicaPairAverage (gibbs⟨t, p⟩) f
          (fun a b => a (Fin.last N) * b (Fin.last N))) ∂(law r) := by
    rw [integral_prod_symm _ hIy, integral_prod_symm _ hIRHS, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hIy.prod_left_ae, hIRHS.prod_left_ae] with d hd1 hd2
    exact integral_id_mul_gaussianReal_eq r (hder d) hd1 hd2
  rw [hstein, integral_const_mul, ← mul_assoc, integral_add hIDε2 (hIPε.const_mul 2),
    integral_const_mul]

end Path

/-- **Talagrand, Proposition 3.2.1** (Eqs. (3.62)--(3.66)): for `κ > 0`, `r̄ ≤ r`, `u ≤ 0` with `u`
and `u'` differentiable and `u', u''` bounded, `t ∈ (0, 1)`, and a measurable observable `f` on
`(ℝ^(N+1))^R` of polynomial growth, the derivative of `ν_t (f) = 𝔼 ⟨f⟩_t` along the cavity path is
`(N + 1)⁻¹ ∑_k 𝔼 [D (V_k) / 2 + P (U_k ⊗ U_k)] - 𝔼 [r P (ε ⊗ ε) + r̄ D (ε²) / 2]`, where
`D = replicaDiff G_t f`, `P = replicaPairAverage G_t f`, `ε` is the last spin, `U_k = u' (S_k) ε`
and `V_k = (u'' + u'²) (S_k) ε²`. In the book's notation, Term I is
`(N + 1)⁻¹ ∑_k 𝔼 [D (V_k) / 2]`, Term II is `(N + 1)⁻¹ ∑_k 𝔼 [P (U_k ⊗ U_k)]`, Term III is
`-r 𝔼 [P (ε ⊗ ε)]`, and Terms IV + V combine `-r 𝔼 [D (ε²) / 2] + (r - r̄) 𝔼 [D (ε²) / 2]` into
`-r̄ 𝔼 [D (ε²) / 2]`. -/
theorem hasDerivAt_integral_integral_pi_shcherbinaTirozziCavity [LinearOrder R] {κ h : ℝ}
    (hκ : 0 < κ) (r : ℝ≥0) {rBar : ℝ} (hrr : rBar ≤ r) {u : ℝ → ℝ} (hu0 : ∀ x, u x ≤ 0)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u)) {D D₂ : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {f : (R → ℝ^(N + 1)) → ℝ} (hf : Measurable f) {C : ℝ} {m : ℕ}
    (hfb : ∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) :
    let P : Measure Dis := law r
    let G : ℝ → Dis → Measure (ℝ^(N + 1)) := fun s p =>
      (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar s p.1 u p.2.1 p.2.2 σ
    let U : Fin M → Dis → ℝ^(N + 1) → ℝ := fun k p σ =>
      deriv u field⟨t, p.2.1, k, σ⟩ * σ (Fin.last N)
    let V : Fin M → Dis → ℝ^(N + 1) → ℝ := fun k p σ =>
      (deriv (deriv u) field⟨t, p.2.1, k, σ⟩ + deriv u field⟨t, p.2.1, k, σ⟩ ^ 2) *
        σ (Fin.last N) ^ 2
    (∀ k, Integrable (fun p => replicaDiff (G t p) f (V k p)) P) ∧
      (∀ k, Integrable (fun p => replicaPairAverage (G t p) f (fun a b => U k p a * U k p b)) P) ∧
      Integrable (fun p => replicaPairAverage (G t p) f
        (fun a b => a (Fin.last N) * b (Fin.last N))) P ∧
      Integrable (fun p => replicaDiff (G t p) f (fun σ => σ (Fin.last N) ^ 2)) P ∧
      HasDerivAt (fun s => ∫ p, ∫ σ, f σ ∂(Measure.pi fun _ : R => G s p) ∂P)
        (((N : ℝ) + 1)⁻¹ * (∑ k : Fin M, ∫ p, (replicaDiff (G t p) f (V k p) / 2 +
            replicaPairAverage (G t p) f (fun a b => U k p a * U k p b)) ∂P) -
          ∫ p, ((r : ℝ) * replicaPairAverage (G t p) f
              (fun a b => a (Fin.last N) * b (Fin.last N)) +
            rBar * replicaDiff (G t p) f (fun σ => σ (Fin.last N) ^ 2) / 2) ∂P) t := by
  intro P G U V
  have hum : Measurable u := hu1.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have hst0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
  have hs1t0 : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.2 h1t).ne'
  have hsN0 : Real.sqrt ((N : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  obtain ⟨hdiff_int, hdiff⟩ := hasDerivAt_cavity_disorder_average (κ := κ) (h := h) (r := r)
    (rBar := rBar) hκ hrr hu1 hu0 hD ht0 ht1 hf hfb
  have hcoupl := fun k => integral_cavity_coupling_ibp (κ := κ) (h := h) (r := r) (rBar := rBar)
    hκ hrr hu1 hu2 hu0 hD hD₂ ht0.le ht1.le hf hfb k
  obtain ⟨hIy, hIDε2, hIPε, hy_ibp⟩ := integral_cavity_field_ibp (κ := κ) (h := h) (r := r)
    (rBar := rBar) hκ hrr hu1 hu0 hD ht0.le ht1.le hf hfb
  refine ⟨fun k => (hcoupl k).2.1, fun k => (hcoupl k).2.2.1, hIPε, hIDε2, ?_⟩
  refine hdiff.congr_deriv ?_
  -- split `replicaDiff` pointwise over the three pieces of `∂_t (-H_t)`
  have hsplit : ∀ p : Dis,
      replicaDiff (G t p) f (fun σ =>
        (∑ k : Fin M, (Real.sqrt (N + 1))⁻¹ * p.2.1 k (Fin.last N) / (2 * Real.sqrt t) * U k p σ) +
          (-(p.1 / (2 * Real.sqrt (1 - t))) * σ (Fin.last N) +
            ((r : ℝ) - rBar) / 2 * σ (Fin.last N) ^ 2)) =
      (∑ k : Fin M, ((Real.sqrt (N + 1))⁻¹ / (2 * Real.sqrt t)) *
          (p.2.1 k (Fin.last N) * replicaDiff (G t p) f (U k p))) +
        (-(1 / (2 * Real.sqrt (1 - t))) *
            (p.1 * replicaDiff (G t p) f (fun σ => σ (Fin.last N))) +
          (((r : ℝ) - rBar) / 2) * replicaDiff (G t p) f (fun σ => σ (Fin.last N) ^ 2)) := by
    intro p
    have hem : Measurable fun σ : ℝ^(N + 1) =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1 u p.2.1 p.2.2 σ :=
      measurable_cavity_exponent_apply hum t p
    have hconf := cavity_exponent_le (κ := κ) (h := h) hrr hu0 ht0.le ht1.le p
    have hεm : Measurable fun σ : ℝ^(N + 1) => σ (Fin.last N) :=
      measurable_cavity_coord (Fin.last N)
    have hUm : ∀ k, Measurable (U k p) := fun k =>
      (hdu.comp ((measurable_cavity_field t k).comp
        ((measurable_const (a := p)).prodMk measurable_id))).mul hεm
    have hUb : ∀ k x, |U k p x| ≤ D * (1 + ‖x‖) ^ 2 := fun k x => by
      change |deriv u _ * x (Fin.last N)| ≤ _
      rw [abs_mul]
      exact (mul_le_mul (hD _) (abs_last_spin_le x).1 (abs_nonneg _) hD0).trans_eq (by ring)
    set a_k : Fin M → ℝ := fun k =>
      (Real.sqrt (N + 1))⁻¹ * p.2.1 k (Fin.last N) / (2 * Real.sqrt t)
    set b_y : ℝ := -(p.1 / (2 * Real.sqrt (1 - t)))
    set c_q : ℝ := ((r : ℝ) - rBar) / 2
    have h1m : Measurable fun σ : ℝ^(N + 1) => ∑ k, a_k k * U k p σ :=
      Finset.measurable_sum _ fun k _ => (hUm k).const_mul (a_k k)
    have h1b : ∀ x : ℝ^(N + 1), |∑ k, a_k k * U k p x| ≤
        (∑ k, |a_k k| * D) * (1 + ‖x‖) ^ 2 := fun x => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hUb k x) (abs_nonneg _)
    have h2m : Measurable fun σ : ℝ^(N + 1) => b_y * σ (Fin.last N) := hεm.const_mul b_y
    have h2b : ∀ x : ℝ^(N + 1), |b_y * x (Fin.last N)| ≤ |b_y| * (1 + ‖x‖) ^ 2 := fun x => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_last_spin_le x).1 (abs_nonneg _)).trans_eq (by ring)
    have h3m : Measurable fun σ : ℝ^(N + 1) => c_q * σ (Fin.last N) ^ 2 :=
      (hεm.pow_const 2).const_mul c_q
    have h3b : ∀ x : ℝ^(N + 1), |c_q * x (Fin.last N) ^ 2| ≤ |c_q| * (1 + ‖x‖) ^ 2 := fun x => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_last_spin_le x).2 (abs_nonneg _)).trans_eq (by ring)
    have h23b : ∀ x : ℝ^(N + 1), |b_y * x (Fin.last N) + c_q * x (Fin.last N) ^ 2| ≤
        (|b_y| + |c_q|) * (1 + ‖x‖) ^ 2 := fun x =>
      (abs_add_le _ _).trans ((add_le_add (h2b x) (h3b x)).trans_eq (by ring))
    rw [replicaDiff_add_of_confining hκ hem hconf hf hfb h1m (h2m.add h3m) h1b h23b,
      replicaDiff_add_of_confining hκ hem hconf hf hfb h2m h3m h2b h3b,
      replicaDiff_finsetSum_of_confining hκ hem hconf hf hfb Finset.univ
        (fun k => (hUm k).const_mul (a_k k)) (L := fun k => |a_k k| * D) (n := 2)
        (fun k x => by
          rw [abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hUb k x) (abs_nonneg _)),
      replicaDiff_const_mul, replicaDiff_const_mul]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [replicaDiff_const_mul]
      dsimp only [a_k]
      ring
    · congr 1
      dsimp only [b_y]
      ring
  have h1i : Integrable (fun p : Dis => ∑ k : Fin M, ((Real.sqrt (N + 1))⁻¹ / (2 * Real.sqrt t)) *
      (p.2.1 k (Fin.last N) * replicaDiff (G t p) f (U k p))) P :=
    integrable_finsetSum _ fun k _ => ((hcoupl k).1).const_mul _
  have h2i : Integrable (fun p : Dis => -(1 / (2 * Real.sqrt (1 - t))) *
      (p.1 * replicaDiff (G t p) f (fun σ => σ (Fin.last N)))) P := hIy.const_mul _
  have h3i : Integrable (fun p : Dis => (((r : ℝ) - rBar) / 2) *
      replicaDiff (G t p) f (fun σ => σ (Fin.last N) ^ 2)) P := hIDε2.const_mul _
  simp_rw [hsplit]
  rw [integral_add h1i (h2i.add h3i), integral_add h2i h3i,
    integral_finsetSum _ fun k _ => ((hcoupl k).1).const_mul _,
    integral_const_mul, integral_const_mul, hy_ibp]
  have hsum_eq : (∑ k : Fin M, ∫ p, ((Real.sqrt (N + 1))⁻¹ / (2 * Real.sqrt t)) *
        (p.2.1 k (Fin.last N) * replicaDiff (G t p) f (U k p)) ∂P) =
      ((N : ℝ) + 1)⁻¹ * ∑ k : Fin M, ∫ p, (replicaDiff (G t p) f (V k p) / 2 +
        replicaPairAverage (G t p) f (fun a b => U k p a * U k p b)) ∂P := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (hcoupl k).2.2.2,
      integral_add (((hcoupl k).2.1).div_const 2) ((hcoupl k).2.2.1), integral_div]
    have hsqN : Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) = (N : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    field_simp
    nlinarith [hsqN]
  have hy_eq : -(1 / (2 * Real.sqrt (1 - t))) * ((r : ℝ) * Real.sqrt (1 - t) *
        ((∫ p, replicaDiff (G t p) f (fun σ => σ (Fin.last N) ^ 2) ∂P) +
          2 * ∫ p, replicaPairAverage (G t p) f
            (fun a b => a (Fin.last N) * b (Fin.last N)) ∂P)) +
      ((r : ℝ) - rBar) / 2 * ∫ p, replicaDiff (G t p) f (fun σ => σ (Fin.last N) ^ 2) ∂P =
      -∫ p, ((r : ℝ) * replicaPairAverage (G t p) f
          (fun a b => a (Fin.last N) * b (Fin.last N)) +
        rBar * replicaDiff (G t p) f (fun σ => σ (Fin.last N) ^ 2) / 2) ∂P := by
    rw [integral_add (hIPε.const_mul (r : ℝ)) ((hIDε2.const_mul rBar).div_const 2),
      integral_div, integral_const_mul, integral_const_mul]
    field_simp
    ring
  rw [hsum_eq, hy_eq, sub_eq_add_neg]

end SpinGlasses
