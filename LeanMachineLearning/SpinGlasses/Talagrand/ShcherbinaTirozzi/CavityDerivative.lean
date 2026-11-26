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

open MeasureTheory ProbabilityTheory
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
    memLp_id_gaussianReal' d (ENNReal.natCast_ne_top d)
  have hy : MemLp (fun p : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) => p.1) d
      ((gaussianReal 0 r).prod P) := (hid r).comp_measurePreserving measurePreserving_fst
  have hg : ∀ k i, MemLp (fun p : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      p.2.1 k i) d ((gaussianReal 0 r).prod P) := fun k i =>
    (hid 1).comp_measurePreserving
      (((measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) i).comp
        (measurePreserving_eval
          (fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) k)).comp
        (measurePreserving_fst.comp measurePreserving_snd))
  have hg0 : ∀ i, MemLp (fun p : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      p.2.2 i) d ((gaussianReal 0 r).prod P) := fun i =>
    (hid 1).comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) i).comp
        (measurePreserving_snd.comp measurePreserving_snd))
  have hsum : MemLp (fun p : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      1 + |p.1| + (∑ k, ∑ i, |p.2.1 k i|) + ∑ i, |p.2.2 i|) d ((gaussianReal 0 r).prod P) :=
    (((memLp_const 1).add hy.abs).add (memLp_finsetSum _ fun k _ =>
      memLp_finsetSum _ fun i _ => (hg k i).abs)).add
        (memLp_finsetSum _ fun i _ => (hg0 i).abs)
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  refine (hsum.integrable_norm_pow hd).congr (ae_of_all _ fun p => ?_)
  simp only
  rw [Real.norm_of_nonneg (by positivity)]

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
  exact (((Finset.measurable_sum _ fun i _ => (hg _).mul (hσ _)).add
    (((hg _).mul (hσ _)).const_mul _)).const_mul _)

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
  Measure.tilted volume fun σ : ℝ^(N + 1) =>
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

end Path

end SpinGlasses
