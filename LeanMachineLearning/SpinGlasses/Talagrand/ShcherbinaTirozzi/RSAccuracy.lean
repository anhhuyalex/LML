/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ReplicaOverlaps

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityConcentration
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityLastSpinMoments

/-!
# The Shcherbina--Tirozzi model: RS equation accuracy at rate `K / √N` (Lemma 3.2.11, Prop. 3.2.12)

This file proves:
1. **Lemma 3.2.11** (at rate `K / √(N + 1)`, Eqs. (3.112)): for `q_t = ν_t(R_{1,2})` and
   `ρ_t = ν_t(R_{1,1})` along the cavity path `H_{N,M,t}` on `ℝ^(N+1)` (`M ≤ 10 (N + 1)`),
   `|q_t - q| ≤ K / √(N + 1)` and `|ρ_t - ρ| ≤ K / √(N + 1)` uniformly in `t ∈ [0, 1]`.
   The proof applies Proposition 3.2.1 (`CavityDerivative.lean`) to `f - c` (where the constant
   `c = q_t` or `ρ_t` drops out of the derivative), and bounds each term by Cauchy--Schwarz using
   Eq. (3.111) (`CavityConcentration.lean`) and Lemma 3.2.6 (`LastSpinTail.lean`).
2. **Proposition 3.2.12** (Eq. (3.115)): combining Proposition 3.2.10 (`CavityLastSpinMoments.lean`)
   with Eq. (3.111) and Lemma 3.2.11, the physical overlaps `(q, ρ)` satisfy the replica-symmetric
   equations (3.69), (3.74), (3.75) with accuracy `K / √(N + 1)`:
   ```
   |ρ - (1 / a + (r + h²) / a²)| ≤ K / √(N + 1),
   |q - (r + h²) / a²| ≤ K / √(N + 1),
   ```
   where `a = 2 κ + r - r̄` and `(r, r̄)` are the RS parameters (3.69) at `α = M / (N + 1)`.

## Main declarations

* `SpinGlasses.exists_abs_shcherbinaTirozziCavity_selfOverlap_sub_le`: `|ρ_t - ρ| ≤ K / √(N + 1)`.
* `SpinGlasses.exists_abs_shcherbinaTirozziCavity_overlap_sub_le`: `|q_t - q| ≤ K / √(N + 1)`.
* `SpinGlasses.exists_shcherbinaTirozzi_rsEquations_accuracy`: Proposition 3.2.12 (Eq. (3.115))
  at the physical parameters `(q, ρ, r, r̄)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

local notation "Dis[" N ", " M "]" =>
  ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))

local notation "cavLaw[" N ", " M ", " r "]" =>
  Measure.prod (gaussianReal 0 r)
    (Measure.prod
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

local notation "cfield[" N ", " t ", " g ", " k ", " σ "]" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

section CavityDerivativeBound

/-- Pointwise bound on `|replicaDiff G f g|` when `|g(x)| ≤ B * ε(x)²` under a probability
measure `G`: `|replicaDiff G f g| ≤ 2 * |R| * B * √(⟨f²⟩) * √(⟨ε⁴⟩)`. -/
private lemma abs_replicaDiff_le_of_le_mul_sq {α R : Type*} [MeasurableSpace α] [Fintype R]
    {G : Measure α} [IsProbabilityMeasure G] {f : (R → α) → ℝ} {g : α → ℝ} {ε : α → ℝ} {B : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hB : 0 ≤ B)
    (hgb : ∀ x, |g x| ≤ B * ε x ^ 2)
    (hf2 : Integrable (fun σ : R → α => f σ ^ 2) (Measure.pi fun _ : R => G))
    (hε4 : Integrable (fun x : α => ε x ^ 4) G) :
    |replicaDiff G f g| ≤
      2 * (Fintype.card R : ℝ) * B *
        Real.sqrt (∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G)) *
        Real.sqrt (∫ x : α, ε x ^ 4 ∂G) := by
  set μ_opt : Measure (Option R → α) := Measure.pi fun _ : Option R => G
  have hterm : ∀ o : Option R,
      |∫ σ : Option R → α, f (fun r => σ (some r)) * g (σ o) ∂μ_opt| ≤
        B * Real.sqrt (∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G)) *
          Real.sqrt (∫ x : α, ε x ^ 4 ∂G) := by
    intro o
    have hmp_f : MeasurePreserving (fun σ : Option R → α => fun r : R => σ (some r))
        μ_opt (Measure.pi fun _ : R => G) :=
      measurePreserving_pi_comp_injective G (Option.some_injective R)
    have hmp_o : MeasurePreserving (fun σ : Option R → α => σ o) μ_opt G :=
      measurePreserving_eval (fun _ => G) o
    have hF2 : Integrable (fun σ : Option R → α => f (fun r => σ (some r)) ^ 2) μ_opt :=
      hmp_f.integrable_comp_of_integrable hf2
    have hE4 : Integrable (fun σ : Option R → α => ε (σ o) ^ 4) μ_opt :=
      hmp_o.integrable_comp_of_integrable hε4
    have hG2 : Integrable (fun σ : Option R → α => g (σ o) ^ 2) μ_opt :=
      (hE4.const_mul (B ^ 2)).mono'
        ((hg.comp (measurable_pi_apply o)).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun σ => by
          rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
          exact (pow_le_pow_left₀ (abs_nonneg _) (hgb (σ o)) 2).trans_eq (by ring))
    have hF_mem : MemLp (fun σ : Option R → α => f (fun r => σ (some r))) 2 μ_opt :=
      (memLp_two_iff_integrable_sq (hf.comp hmp_f.measurable).aestronglyMeasurable).2 hF2
    have hG_mem : MemLp (fun σ : Option R → α => g (σ o)) 2 μ_opt :=
      (memLp_two_iff_integrable_sq (hg.comp (measurable_pi_apply o)).aestronglyMeasurable).2 hG2
    have hF2_eq : ∫ σ : Option R → α, f (fun r => σ (some r)) ^ 2 ∂μ_opt =
        ∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G) :=
      integral_pi_comp_injective G (Option.some_injective R) (fun σ : R → α => f σ ^ 2)
        (hf.pow_const 2).aestronglyMeasurable
    have hG2_le : ∫ σ : Option R → α, g (σ o) ^ 2 ∂μ_opt ≤ B ^ 2 * ∫ x : α, ε x ^ 4 ∂G := by
      have h1 : ∫ σ : Option R → α, g (σ o) ^ 2 ∂μ_opt ≤
          ∫ σ : Option R → α, B ^ 2 * ε (σ o) ^ 4 ∂μ_opt :=
        integral_mono hG2 (hE4.const_mul _) fun σ => by
          rw [← sq_abs]
          exact (pow_le_pow_left₀ (abs_nonneg _) (hgb (σ o)) 2).trans_eq (by ring)
      rw [integral_const_mul,
        integral_pi_eval G o (fun x : α => ε x ^ 4) hε4.aestronglyMeasurable] at h1
      exact h1
    have hcs := abs_integral_mul_le_of_integral_sq_le hF_mem hG_mem
      (Real.sqrt_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg (∫ x : α, ε x ^ 4 ∂G)))
      (by rw [hF2_eq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)])
      (hG2_le.trans_eq (by rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ => by positivity)]))
    exact hcs.trans_eq (by ring)
  rw [replicaDiff_eq]
  set M_val : ℝ := B * Real.sqrt (∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G)) *
      Real.sqrt (∫ x : α, ε x ^ 4 ∂G)
  have h1 : |∑ r : R, ∫ σ : Option R → α, f (fun j => σ (some j)) * g (σ (some r)) ∂μ_opt| ≤
      (Fintype.card R : ℝ) * M_val := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun r _ => hterm (some r)).trans_eq ?_
    simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : |(Fintype.card R : ℝ) *
      ∫ σ : Option R → α, f (fun j => σ (some j)) * g (σ none) ∂μ_opt| ≤
      (Fintype.card R : ℝ) * M_val := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hterm none) (Nat.cast_nonneg _)
  exact ((abs_sub _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

/-- Pointwise bound on `|replicaPairAverage G f (fun a b => u a * u b)|` when `|u(x)| ≤ B * |ε(x)|`
under a probability measure `G`:
`|replicaPairAverage G f (u ⊗ u)| ≤ 3 * (|R| + 1)² * B² * √(⟨f²⟩) * √(⟨ε⁴⟩)`. -/
private lemma abs_replicaPairAverage_le_of_le_mul_abs {α R : Type*} [MeasurableSpace α]
    [Fintype R] [LinearOrder R] {G : Measure α} [IsProbabilityMeasure G]
    {f : (R → α) → ℝ} {u ε : α → ℝ} {B : ℝ} (hf : Measurable f) (hu : Measurable u) (hB : 0 ≤ B)
    (hub : ∀ x, |u x| ≤ B * |ε x|)
    (hf2 : Integrable (fun σ : R → α => f σ ^ 2) (Measure.pi fun _ : R => G))
    (hε4 : Integrable (fun x : α => ε x ^ 4) G) :
    |replicaPairAverage G f (fun a b => u a * u b)| ≤
      3 * ((Fintype.card R : ℝ) + 1) ^ 2 * B ^ 2 *
        Real.sqrt (∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G)) *
        Real.sqrt (∫ x : α, ε x ^ 4 ∂G) := by
  set μ_2 : Measure (Option (Option R) → α) := Measure.pi fun _ : Option (Option R) => G
  have hmp_f : MeasurePreserving
      (fun τ : Option (Option R) → α => fun r : R => τ (some (some r)))
      μ_2 (Measure.pi fun _ : R => G) :=
    measurePreserving_pi_comp_injective G
      ((Option.some_injective (Option R)).comp (Option.some_injective R))
  have hF2 : Integrable (fun τ : Option (Option R) → α => f (fun r => τ (some (some r))) ^ 2) μ_2 :=
    hmp_f.integrable_comp_of_integrable hf2
  have hF_mem : MemLp (fun τ : Option (Option R) → α => f (fun r => τ (some (some r)))) 2 μ_2 :=
    (memLp_two_iff_integrable_sq (hf.comp hmp_f.measurable).aestronglyMeasurable).2 hF2
  have hF2_eq : ∫ τ : Option (Option R) → α, f (fun r => τ (some (some r))) ^ 2 ∂μ_2 =
      ∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G) :=
    integral_pi_comp_injective G ((Option.some_injective (Option R)).comp (Option.some_injective R))
      (fun σ : R → α => f σ ^ 2) (hf.pow_const 2).aestronglyMeasurable
  have hpair_int : ∀ a b : Option (Option R),
      Integrable (fun τ : Option (Option R) → α => (u (τ a) * u (τ b)) ^ 2) μ_2 ∧
        ∫ τ : Option (Option R) → α, (u (τ a) * u (τ b)) ^ 2 ∂μ_2 ≤
          B ^ 4 * ∫ x : α, ε x ^ 4 ∂G := fun a b => by
    have hE4 : ∀ o : Option (Option R), Integrable (fun τ => ε (τ o) ^ 4) μ_2 := fun o =>
      (measurePreserving_eval (fun _ => G) o).integrable_comp_of_integrable hε4
    have hpt : ∀ τ : Option (Option R) → α,
        (u (τ a) * u (τ b)) ^ 2 ≤ B ^ 4 * ((ε (τ a) ^ 4 + ε (τ b) ^ 4) / 2) := fun τ => by
      have h1 : |u (τ a) * u (τ b)| ≤ B ^ 2 * (|ε (τ a)| * |ε (τ b)|) := by
        rw [abs_mul]
        exact (mul_le_mul (hub _) (hub _) (abs_nonneg _) (mul_nonneg hB (abs_nonneg _))).trans_eq
          (by ring)
      have h2 : (u (τ a) * u (τ b)) ^ 2 ≤ B ^ 4 * (ε (τ a) ^ 2 * ε (τ b) ^ 2) := by
        rw [← sq_abs]
        refine (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans_eq ?_
        rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
      have ham : ε (τ a) ^ 2 * ε (τ b) ^ 2 ≤ (ε (τ a) ^ 4 + ε (τ b) ^ 4) / 2 := by
        have hsq := sq_nonneg (ε (τ a) ^ 2 - ε (τ b) ^ 2)
        have hid : (ε (τ a) ^ 2 - ε (τ b) ^ 2) ^ 2 =
            ε (τ a) ^ 4 + ε (τ b) ^ 4 - 2 * (ε (τ a) ^ 2 * ε (τ b) ^ 2) := by ring
        linarith only [hsq, hid]
      exact h2.trans (mul_le_mul_of_nonneg_left ham (by positivity))
    have hdom : Integrable (fun τ => B ^ 4 * ((ε (τ a) ^ 4 + ε (τ b) ^ 4) / 2)) μ_2 :=
      (((hE4 a).add (hE4 b)).div_const 2).const_mul (B ^ 4)
    have hi : Integrable (fun τ => (u (τ a) * u (τ b)) ^ 2) μ_2 :=
      hdom.mono' (((hu.comp (measurable_pi_apply a)).mul
        (hu.comp (measurable_pi_apply b))).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun τ => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt τ)
    refine ⟨hi, (integral_mono hi hdom hpt).trans_eq ?_⟩
    rw [integral_const_mul, integral_div, integral_add (hE4 a) (hE4 b),
      integral_pi_eval G a (fun x : α => ε x ^ 4) hε4.aestronglyMeasurable,
      integral_pi_eval G b (fun x : α => ε x ^ 4) hε4.aestronglyMeasurable]
    ring
  -- Bound the L² norm of `replicaPairCombination (u ⊗ u)` via Minkowski / triangle inequality
  set k : ℝ := (Fintype.card R : ℝ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  set K_fn : α → α → ℝ := fun a b => u a * u b
  have hterm_mem : ∀ a b : Option (Option R),
      MemLp (fun τ : Option (Option R) → α => K_fn (τ a) (τ b)) 2 μ_2 := fun a b =>
    (memLp_two_iff_integrable_sq ((hu.comp (measurable_pi_apply a)).mul
      (hu.comp (measurable_pi_apply b))).aestronglyMeasurable).2 (hpair_int a b).1
  have hterm_cs : ∀ a b : Option (Option R),
      |∫ τ : Option (Option R) → α, f (fun r => τ (some (some r))) * K_fn (τ a) (τ b) ∂μ_2| ≤
        B ^ 2 * Real.sqrt (∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G)) *
          Real.sqrt (∫ x : α, ε x ^ 4 ∂G) := fun a b => by
    have hcs := abs_integral_mul_le_of_integral_sq_le hF_mem (hterm_mem a b)
      (Real.sqrt_nonneg _) (mul_nonneg (sq_nonneg B) (Real.sqrt_nonneg (∫ x : α, ε x ^ 4 ∂G)))
      (by rw [hF2_eq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)])
      ((hpair_int a b).2.trans_eq (by
        rw [mul_pow, ← pow_mul, Real.sq_sqrt (integral_nonneg fun _ => by positivity)]))
    exact hcs.trans_eq (by ring)
  have hterm_int : ∀ a b : Option (Option R),
      Integrable (fun τ : Option (Option R) → α =>
        f (fun r => τ (some (some r))) * K_fn (τ a) (τ b)) μ_2 := fun a b =>
    hF_mem.integrable_mul (hterm_mem a b)
  set M_val : ℝ := B ^ 2 * Real.sqrt (∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G)) *
      Real.sqrt (∫ x : α, ε x ^ 4 ∂G)
  have hM0 : 0 ≤ M_val := by positivity
  rw [replicaPairAverage_eq]
  have hexpand : (fun τ : Option (Option R) → α =>
      f (fun r => τ (some (some r))) * replicaPairCombination K_fn τ) =
      fun τ => (∑ p ∈ Finset.univ.filter (fun p : R × R => p.1 < p.2),
          f (fun r => τ (some (some r))) * K_fn (τ (some (some p.1))) (τ (some (some p.2)))) -
        k * (∑ r : R, f (fun j => τ (some (some j))) * K_fn (τ (some (some r))) (τ (some none))) +
        (k * (k + 1) / 2) *
          (f (fun j => τ (some (some j))) * K_fn (τ (some none)) (τ none)) := by
    funext τ
    rw [replicaPairCombination_eq, mul_add, mul_sub, Finset.mul_sum, mul_left_comm _ k,
      Finset.mul_sum, mul_left_comm _ (k * (k + 1) / 2)]
  rw [hexpand]
  set t1 : (Option (Option R) → α) → ℝ := fun τ =>
    ∑ p ∈ Finset.univ.filter (fun p : R × R => p.1 < p.2),
      f (fun r => τ (some (some r))) * K_fn (τ (some (some p.1))) (τ (some (some p.2)))
  set t2 : (Option (Option R) → α) → ℝ := fun τ =>
    k * ∑ r : R, f (fun j => τ (some (some j))) * K_fn (τ (some (some r))) (τ (some none))
  set t3 : (Option (Option R) → α) → ℝ := fun τ =>
    (k * (k + 1) / 2) * (f (fun j => τ (some (some j))) * K_fn (τ (some none)) (τ none))
  have hi1 : Integrable t1 μ_2 := integrable_finsetSum _ fun p _ => hterm_int _ _
  have hi2 : Integrable t2 μ_2 := (integrable_finsetSum _ fun r _ => hterm_int _ _).const_mul k
  have hi3 : Integrable t3 μ_2 := (hterm_int _ _).const_mul _
  have hi12 : Integrable (fun τ => t1 τ - t2 τ) μ_2 := hi1.sub hi2
  change |∫ τ, ((t1 τ - t2 τ) + t3 τ) ∂μ_2| ≤ _
  rw [integral_add hi12 hi3, integral_sub hi1 hi2]
  dsimp only [t1, t2, t3]
  rw [integral_finsetSum _ fun p _ => hterm_int _ _,
    integral_const_mul, integral_finsetSum _ fun r _ => hterm_int _ _, integral_const_mul]
  have hb1 : |∑ p ∈ Finset.univ.filter (fun p : R × R => p.1 < p.2),
      ∫ τ, f (fun r => τ (some (some r))) * K_fn (τ (some (some p.1))) (τ (some (some p.2))) ∂μ_2| ≤
      k ^ 2 * M_val := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => hterm_cs _ _).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hM0
    rw [sq, ← Nat.cast_mul, ← Fintype.card_prod]
    exact_mod_cast Finset.card_filter_le _ _
  have hb2 : |k * ∑ r : R,
      ∫ τ, f (fun j => τ (some (some j))) * K_fn (τ (some (some r))) (τ (some none)) ∂μ_2| ≤
      k ^ 2 * M_val := by
    rw [abs_mul, abs_of_nonneg hk0, sq, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun r _ => hterm_cs _ _).trans_eq ?_)) hk0
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hb3 : |(k * (k + 1) / 2) *
      ∫ τ, f (fun j => τ (some (some j))) * K_fn (τ (some none)) (τ none) ∂μ_2| ≤
      (k + 1) ^ 2 * M_val := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul (by nlinarith) (hterm_cs _ _) (abs_nonneg _) (by positivity)
  have hk_le : k ^ 2 * M_val ≤ (k + 1) ^ 2 * M_val :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hk0 (by linarith) 2) hM0
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((abs_sub _ _).trans (add_le_add hb1 hb2)) hb3).trans ?_
  have : 3 * (k + 1) ^ 2 * B ^ 2 *
      Real.sqrt (∫ σ : R → α, f σ ^ 2 ∂(Measure.pi fun _ : R => G)) *
      Real.sqrt (∫ x : α, ε x ^ 4 ∂G) = 3 * (k + 1) ^ 2 * M_val := by ring
  rw [this]; linarith

/-- Fourth moment of the last spin under `ν_t` from Lemma 3.2.6 (`ν_t(exp(ε² / K)) ≤ K` with
`16 / κ₀ ≤ K`): `ν_t(ε⁴) ≤ 2 K³`. -/
private lemma integrable_and_integral_cavity_last_pow_four_le
    {N M : ℕ} {κ₀ κ h t rBar K : ℝ} {r : ℝ≥0} {u : ℝ → ℝ}
    (hκ₀ : 0 < κ₀) (hκ : κ₀ ≤ κ) (hrr : rBar ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hum : Measurable u) (hu0 : ∀ x, u x ≤ 0) (hK0 : 0 < K) (hKκ : 16 / κ₀ ≤ K)
    (G : Dis[N, M] → Measure (ℝ^(N + 1)))
    (hG : ∀ d, G d = volume.tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ)
    (hexp_i : Integrable (fun d => ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K) ∂(G d))
      cavLaw[N, M, r])
    (hexp_le : ∫ d, ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K) ∂(G d) ∂cavLaw[N, M, r] ≤ K) :
    Integrable (fun d => ∫ σ, σ (Fin.last N) ^ 4 ∂(G d)) cavLaw[N, M, r] ∧
      ∫ d, ∫ σ, σ (Fin.last N) ^ 4 ∂(G d) ∂cavLaw[N, M, r] ≤ 2 * K ^ 3 := by
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have ha : K⁻¹ < κ := by
    refine inv_lt_of_inv_lt₀ hκ0 (lt_of_lt_of_le ?_
      ((div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ).trans hKκ))
    rw [inv_eq_one_div]
    exact div_lt_div_of_pos_right (by norm_num) hκ0
  have hE : Measurable fun p : Dis[N, M] × ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1.1 u p.1.2.1 p.1.2.2 p.2 :=
    (measurable_shcherbinaTirozziCavityHamiltonian κ h r rBar t hum).neg
  have hmeas : Measurable fun d : Dis[N, M] => ∫ σ, σ (Fin.last N) ^ 4 ∂(G d) := by
    simp_rw [hG]
    exact measurable_integral_tilted hE
      (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const 4)
  have hpt_σ : ∀ σ : ℝ^(N + 1),
      σ (Fin.last N) ^ 4 ≤ 2 * K ^ 2 * Real.exp (σ (Fin.last N) ^ 2 / K) := fun σ => by
    have hx : 0 ≤ σ (Fin.last N) ^ 2 / K := by positivity
    have hq := Real.quadratic_le_exp_of_nonneg hx
    have hsq : (σ (Fin.last N) ^ 2 / K) ^ 2 / 2 ≤ Real.exp (σ (Fin.last N) ^ 2 / K) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 2 * K ^ 2 by positivity)
    refine le_trans ?_ hmul
    field_simp
    exact le_rfl
  have hpt : ∀ d : Dis[N, M],
      ∫ σ, σ (Fin.last N) ^ 4 ∂(G d) ≤
        2 * K ^ 2 * ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K) ∂(G d) := fun d => by
    rw [← integral_const_mul]
    have hconf : ∀ σ : ℝ^(N + 1),
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ ≤
          0 + (|h| * ∑ i, |d.2.2 i| + |d.1|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun σ => by
      rw [zero_add]
      exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr ht0 ht1 hu0 d.2.1 d.2.2 σ
    have hem : Measurable fun σ : ℝ^(N + 1) =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ :=
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t d.1 hum d.2.1 d.2.2).neg
    have h4i : Integrable (fun σ : ℝ^(N + 1) => σ (Fin.last N) ^ 4) (G d) := by
      rw [hG d]
      exact (memLp_of_poly_bound_of_confining hκ0 hem hconf
        (f := fun σ : ℝ^(N + 1) => σ (Fin.last N) ^ 4)
        ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const
          4).aestronglyMeasurable) (C := 1) (m := 4) (fun σ => by
          rw [one_mul, Real.norm_of_nonneg (by positivity)]
          have h1 : |σ (Fin.last N)| ≤ 1 + ‖σ‖ := by
            have := PiLp.norm_apply_le σ (Fin.last N)
            rw [Real.norm_eq_abs] at this; linarith
          calc σ (Fin.last N) ^ 4 = |σ (Fin.last N)| ^ 4 := by rw [← Even.pow_abs (by decide)]
            _ ≤ (1 + ‖σ‖) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h1 4) 1).integrable le_rfl
    have he_i : Integrable (fun σ : ℝ^(N + 1) =>
        2 * K ^ 2 * Real.exp (σ (Fin.last N) ^ 2 / K)) (G d) := by
      rw [hG d]
      have hsub_pos : 0 < κ - K⁻¹ := sub_pos.2 ha
      have hZ_i : Integrable (fun σ : ℝ^(N + 1) =>
          Real.exp (-shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ))
          (volume : Measure (ℝ^(N + 1))) :=
        integrable_exp_of_confining (μ := volume) hκ0 hem hconf
      have hprod_i : Integrable (fun σ : ℝ^(N + 1) =>
          Real.exp (σ (Fin.last N) ^ 2 / K +
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ))
          (volume : Measure (ℝ^(N + 1))) := by
        refine integrable_exp_of_confining (μ := volume) hsub_pos
          (((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const
            2).div_const K).add hem)
          (A := 0) (B := |h| * ∑ i, |d.2.2 i| + |d.1|) fun σ => ?_
        have hcoord : σ (Fin.last N) ^ 2 ≤ ‖σ‖ ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le σ (Fin.last N)) 2
        have hdiv : σ (Fin.last N) ^ 2 / K ≤ K⁻¹ * ‖σ‖ ^ 2 := by
          rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left hcoord (inv_nonneg.2 hK0.le)
        linarith [hconf σ]
      have h1 : Integrable (fun σ : ℝ^(N + 1) => Real.exp (σ (Fin.last N) ^ 2 / K))
          ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ) := by
        rw [integrable_tilted_iff (integrable_exp_of_confining (μ := volume) hκ0 hem hconf)]
        exact hprod_i.congr (ae_of_all _ fun σ => by
          dsimp only; rw [Real.exp_add, smul_eq_mul, mul_comm])
      exact h1.const_mul (2 * K ^ 2)
    exact integral_mono h4i he_i hpt_σ
  have hi : Integrable (fun d => ∫ σ, σ (Fin.last N) ^ 4 ∂(G d)) cavLaw[N, M, r] :=
    (hexp_i.const_mul (2 * K ^ 2)).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun d => by
      rw [Real.norm_of_nonneg (integral_nonneg fun σ => by positivity)]
      exact hpt d)
  refine ⟨hi, (integral_mono hi (hexp_i.const_mul _) hpt).trans ?_⟩
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hexp_le (by positivity)).trans_eq (by ring)

/-- **Derivative bound along `ν_t` from L² smallness of `f - c`:**
if `t ∈ (0, 1)` and `ν_t((f - c)²) ≤ A²`, then `|d/dt ν_t(f)| ≤ K * A` where `K` depends only on
`|R_rep|, κ₀, h₀, D, R, R_diff`. This is the `K / √N` proof of Talagrand's Lemma 3.2.11. -/
private theorem exists_hasDerivAt_shcherbinaTirozziCavity_abs_le_of_sub_const_sq_le
    {R_rep : Type} [Fintype R_rep] [LinearOrder R_rep]
    (κ₀ h₀ D R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ)
      {f : (R_rep → ℝ^(N + 1)) → ℝ} {C : ℝ} {m : ℕ} {c A : ℝ},
      κ₀ ≤ κ → |h| ≤ h₀ → 0 < t → t < 1 → rBar ≤ r → (r : ℝ) ≤ R →
      (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      Measurable f → (∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) → 0 ≤ A →
      let G (s : ℝ) (d : Dis[N, M]) : Measure (ℝ^(N + 1)) :=
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar s d.1 u d.2.1 d.2.2 σ
      Integrable (fun d => ∫ σ : R_rep → ℝ^(N + 1), (f σ - c) ^ 2
          ∂(Measure.pi fun _ : R_rep => G t d)) cavLaw[N, M, r] →
      (∫ d, ∫ σ : R_rep → ℝ^(N + 1), (f σ - c) ^ 2
          ∂(Measure.pi fun _ : R_rep => G t d) ∂cavLaw[N, M, r] ≤ A ^ 2) →
      ∃ D_val : ℝ, HasDerivAt
          (fun s => ∫ d, ∫ σ : R_rep → ℝ^(N + 1), f σ
            ∂(Measure.pi fun _ : R_rep => G s d) ∂cavLaw[N, M, r]) D_val t ∧
        |D_val| ≤ K * A := by
  obtain ⟨K_last, hK_last_pos, hK_last_ge, h385⟩ :=
    exists_integral_exp_sq_shcherbinaTirozziCavity_indexed_last_le κ₀ h₀ D R hκ₀ hR
  set n : ℝ := (Fintype.card R_rep : ℝ)
  set S_eps : ℝ := Real.sqrt (2 * K_last ^ 3)
  set B_tot : ℝ := 10 * (n * (|D| + |D| ^ 2) + 3 * (n + 1) ^ 2 * |D| ^ 2) +
    (R * (3 * (n + 1) ^ 2) + (R + R_diff) * n)
  set K : ℝ := B_tot * S_eps + 1
  have hBtot0 : 0 ≤ B_tot := by dsimp only [B_tot]; positivity
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, fun N M κ h t rBar r u f C m c A hκ hh ht0 ht1 hrr hrR hrr_diff hM
    huc hu0 hu1 hu2 hD1 hD2 hf hfb hA => ?_⟩
  intro G hf2_i hf2_le
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hfb 0))
    (Finset.prod_pos fun _ _ => by positivity)
  have hq : 0 ≤ (1 - t) * ((r : ℝ) - rBar) := mul_nonneg (sub_nonneg.2 ht1.le) (sub_nonneg.2 hrr)
  have hprob : ∀ s ∈ Icc (0 : ℝ) 1, ∀ d : Dis[N, M], IsProbabilityMeasure (G s d) := fun s hs d =>
    isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
        (mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hrr)) hum hu0 d.2.1 d.2.2)
  have hfc_m : Measurable fun σ : R_rep → ℝ^(N + 1) => f σ - c := hf.sub_const c
  have hfc_b : ∀ σ : R_rep → ℝ^(N + 1), |f σ - c| ≤ (C + |c|) * ∏ l, (1 + ‖σ l‖) ^ m := fun σ => by
    have hprod1 : (1 : ℝ) ≤ ∏ l : R_rep, (1 + ‖σ l‖) ^ m := by
      have h1 : (∏ _l : R_rep, (1 : ℝ)) ≤ ∏ l : R_rep, (1 + ‖σ l‖) ^ m :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun l _ =>
          one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
      simpa only [Finset.prod_const_one] using h1
    have hc_le : |c| ≤ |c| * ∏ l : R_rep, (1 + ‖σ l‖) ^ m :=
      le_mul_of_one_le_right (abs_nonneg c) hprod1
    refine ((abs_sub _ _).trans (add_le_add (hfb σ) hc_le)).trans_eq ?_
    ring
  -- Apply Proposition 3.2.1 to `f - c`
  obtain ⟨hIV, hIU, hIPε, hIDε, hderiv_fc⟩ :=
    hasDerivAt_integral_integral_pi_shcherbinaTirozziCavity (N := N) (M := M) (R := R_rep)
      (h := h) hκ0 r hrr hu0 hu1 hu2 hD1 hD2 ht0 ht1 hfc_m hfc_b
  -- `ν_s(f - c) = ν_s(f) - c` on `(0, 1)`, so `ν_s(f)` has the same derivative at `t`
  have hfun_eq : (fun s => ∫ d, ∫ σ : R_rep → ℝ^(N + 1), f σ
        ∂(Measure.pi fun _ : R_rep => G s d) ∂cavLaw[N, M, r]) =ᶠ[𝓝 t]
      (fun s => (∫ d, ∫ σ : R_rep → ℝ^(N + 1), (f σ - c)
        ∂(Measure.pi fun _ : R_rep => G s d) ∂cavLaw[N, M, r]) + c) := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    have hprob_s : ∀ d, IsProbabilityMeasure (G s d) := hprob s ⟨hs.1.le, hs.2.le⟩
    have hf_int_s : ∀ d, Integrable f (Measure.pi fun _ : R_rep => G s d) := fun d =>
      integrable_pi_tilted_of_confining hκ0
        (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar s d.1 hum d.2.1 d.2.2).neg
        (fun σ => by
          rw [zero_add]
          exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr hs.1.le hs.2.le hu0
            d.2.1 d.2.2 σ)
        hf.aestronglyMeasurable hfb
    have hpt_s : ∀ d : Dis[N, M],
        ∫ σ : R_rep → ℝ^(N + 1), (f σ - c) ∂(Measure.pi fun _ : R_rep => G s d) =
          (∫ σ : R_rep → ℝ^(N + 1), f σ ∂(Measure.pi fun _ : R_rep => G s d)) - c := fun d => by
      have := hprob_s d
      rw [integral_sub (hf_int_s d) (integrable_const c), integral_const, probReal_univ, one_smul]
    simp_rw [hpt_s]
    obtain ⟨A0, -, hA0⟩ := exists_integral_one_add_norm_pow_cavity_le (N := N) (M := M) (κ := κ)
      (h := h) (r := r) (rBar := rBar) (u := u) hκ0 hrr hu1 hu0 hD1 m
    have hf_dis_int : Integrable (fun d => ∫ σ : R_rep → ℝ^(N + 1), f σ
        ∂(Measure.pi fun _ : R_rep => G s d)) cavLaw[N, M, r] := by
      have hm_s : Measurable fun d : Dis[N, M] =>
          ∫ σ : R_rep → ℝ^(N + 1), f σ ∂(Measure.pi fun _ : R_rep => G s d) :=
        measurable_integral_pi_tilted_of_sigmaFinite
          (measurable_cavity_exponent (κ := κ) (h := h) (r := r) (rBar := rBar) hum s)
          (hf.comp measurable_snd)
      refine integrable_of_abs_le_cavity_disorder_pow r hm_s
        (K := C * A0 ^ Fintype.card R_rep) (d := m * Fintype.card R_rep) fun d => ?_
      have h1 := abs_integral_pi_tilted_le_of_confining (μ := volume) hκ0
        (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar s d.1 hum d.2.1 d.2.2).neg
        (fun σ => by
          rw [zero_add]
          exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr hs.1.le hs.2.le hu0
            d.2.1 d.2.2 σ)
        hfb
      refine h1.trans ?_
      have h2 := pow_le_pow_left₀ (integral_nonneg fun _ => by positivity)
        (hA0 s hs.1.le hs.2.le d) (Fintype.card R_rep)
      rw [mul_pow, ← pow_mul] at h2
      exact (mul_le_mul_of_nonneg_left h2 hC0).trans_eq (by ring)
    rw [integral_sub hf_dis_int (integrable_const c), integral_const, probReal_univ, one_smul]
    ring
  have hderiv : HasDerivAt
      (fun s => ∫ d, ∫ σ : R_rep → ℝ^(N + 1), f σ
        ∂(Measure.pi fun _ : R_rep => G s d) ∂cavLaw[N, M, r]) _ t :=
    (hderiv_fc.add_const c).congr_of_eventuallyEq hfun_eq
  refine ⟨_, hderiv, ?_⟩
  -- Bound the derivative using Cauchy-Schwarz on each term
  obtain ⟨hexp_i, hexp_le⟩ := h385 N M κ h t rBar r (fun _ => u) hκ hh ht0.le ht1.le hrr hrR
    (by omega) (fun _ => huc) (fun _ => hu0) (fun _ => hu1) (fun _ => hD1)
  obtain ⟨hε4_i, hε4_le⟩ := integrable_and_integral_cavity_last_pow_four_le hκ₀ hκ hrr ht0.le ht1.le
    hum hu0 hK_last_pos hK_last_ge (G t) (fun _ => rfl) hexp_i hexp_le
  -- Bound `∫ d, √(⟨(f - c)²⟩) * √(⟨ε⁴⟩) ≤ A * S_eps`
  set sF : Dis[N, M] → ℝ := fun d =>
    Real.sqrt (∫ σ : R_rep → ℝ^(N + 1), (f σ - c) ^ 2 ∂(Measure.pi fun _ : R_rep => G t d))
  set sE : Dis[N, M] → ℝ := fun d => Real.sqrt (∫ x : ℝ^(N + 1), x (Fin.last N) ^ 4 ∂(G t d))
  have hsF_mem : MemLp sF 2 cavLaw[N, M, r] :=
    (memLp_two_iff_integrable_sq (Continuous.comp_aestronglyMeasurable Real.continuous_sqrt
      hf2_i.aestronglyMeasurable)).2 (hf2_i.congr (ae_of_all _ fun d =>
        (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).symm))
  have hsE_mem : MemLp sE 2 cavLaw[N, M, r] :=
    (memLp_two_iff_integrable_sq (Continuous.comp_aestronglyMeasurable Real.continuous_sqrt
      hε4_i.aestronglyMeasurable)).2 (hε4_i.congr (ae_of_all _ fun d =>
        (Real.sq_sqrt (integral_nonneg fun _ => by positivity)).symm))
  have hprod_int : Integrable (fun d => sF d * sE d) cavLaw[N, M, r] :=
    hsF_mem.integrable_mul hsE_mem
  have hprod_le : ∫ d, sF d * sE d ∂cavLaw[N, M, r] ≤ A * S_eps := by
    refine (le_abs_self _).trans (abs_integral_mul_le_of_integral_sq_le hsF_mem hsE_mem hA
      (Real.sqrt_nonneg _) ?_ ?_)
    · exact (integral_congr_ae (ae_of_all _ fun d =>
        Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _))).trans_le hf2_le
    · refine (integral_congr_ae (ae_of_all _ fun d =>
        Real.sq_sqrt (integral_nonneg fun _ => by positivity))).trans_le ?_
      rw [Real.sq_sqrt (by positivity)]; exact hε4_le
  -- Check pointwise L² integrability of `f - c` and `ε⁴` under `G t d`
  have hfc2_d : ∀ d : Dis[N, M], Integrable (fun σ : R_rep → ℝ^(N + 1) => (f σ - c) ^ 2)
      (Measure.pi fun _ : R_rep => G t d) := fun d =>
    integrable_pi_tilted_of_confining hκ0
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t d.1 hum d.2.1 d.2.2).neg
      (fun σ => by
        rw [zero_add]
        exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr ht0.le ht1.le hu0
          d.2.1 d.2.2 σ)
      (hfc_m.pow_const 2).aestronglyMeasurable (C := (C + |c|) ^ 2) (m := 2 * m) fun σ => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        refine (pow_le_pow_left₀ (abs_nonneg _) (hfc_b σ) 2).trans_eq ?_
        rw [mul_pow, ← Finset.prod_pow]; congr 1
        exact Finset.prod_congr rfl fun l _ => by rw [← pow_mul, mul_comm]
  have hε4_d : ∀ d : Dis[N, M], Integrable (fun x : ℝ^(N + 1) => x (Fin.last N) ^ 4) (G t d) :=
    fun d => (memLp_of_poly_bound_of_confining hκ0
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t d.1 hum d.2.1 d.2.2).neg
      (fun σ => by
        rw [zero_add]
        exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr ht0.le ht1.le hu0
          d.2.1 d.2.2 σ)
      ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const
        4).aestronglyMeasurable) (C := 1) (m := 4) (fun σ => by
        rw [one_mul, Real.norm_of_nonneg (by positivity)]
        have h1 : |σ (Fin.last N)| ≤ 1 + ‖σ‖ := by
          have := PiLp.norm_apply_le σ (Fin.last N)
          rw [Real.norm_eq_abs] at this; linarith
        calc σ (Fin.last N) ^ 4 = |σ (Fin.last N)| ^ 4 := by rw [← Even.pow_abs (by decide)]
          _ ≤ (1 + ‖σ‖) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h1 4) 1).integrable le_rfl
  -- Bound each of the four pieces
  have hV_bd : ∀ k : Fin M,
      |∫ d, replicaDiff (G t d) (fun σ => f σ - c)
          (fun σ => (deriv (deriv u) cfield[N, t, d.2.1, k, σ] +
            deriv u cfield[N, t, d.2.1, k, σ] ^ 2) * σ (Fin.last N) ^ 2) ∂cavLaw[N, M, r]| ≤
        2 * n * (|D| + |D| ^ 2) * (A * S_eps) := fun k => by
    have hpt : ∀ d : Dis[N, M],
        |replicaDiff (G t d) (fun σ => f σ - c)
          (fun σ => (deriv (deriv u) cfield[N, t, d.2.1, k, σ] +
            deriv u cfield[N, t, d.2.1, k, σ] ^ 2) * σ (Fin.last N) ^ 2)| ≤
          2 * n * (|D| + |D| ^ 2) * (sF d * sE d) := fun d => by
      have := hprob t ⟨ht0.le, ht1.le⟩ d
      have hgm : Measurable fun σ : ℝ^(N + 1) =>
          (deriv (deriv u) cfield[N, t, d.2.1, k, σ] +
            deriv u cfield[N, t, d.2.1, k, σ] ^ 2) * σ (Fin.last N) ^ 2 := by
        have hc : Continuous fun σ : ℝ^(N + 1) => cfield[N, t, d.2.1, k, σ] := by fun_prop
        exact (((measurable_deriv (deriv u)).comp hc.measurable).add
          (((measurable_deriv u).comp hc.measurable).pow_const 2)).mul
            (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const
              2)
      have hgb : ∀ σ : ℝ^(N + 1),
          |(deriv (deriv u) cfield[N, t, d.2.1, k, σ] +
            deriv u cfield[N, t, d.2.1, k, σ] ^ 2) * σ (Fin.last N) ^ 2| ≤
            (|D| + |D| ^ 2) * σ (Fin.last N) ^ 2 := fun σ => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (σ (Fin.last N)))]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact abs_deriv_deriv_add_sq_deriv_le
          (fun x => (hD1 x).trans (le_abs_self D)) (fun x => (hD2 x).trans (le_abs_self D)) _
      exact (abs_replicaDiff_le_of_le_mul_sq hfc_m hgm (by positivity) hgb (hfc2_d d)
        (hε4_d d)).trans_eq (by ring)
    refine abs_integral_le_integral_abs.trans ((integral_mono (hIV k).abs
      (hprod_int.const_mul _) hpt).trans ?_)
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hprod_le (by positivity)
  have hU_bd : ∀ k : Fin M,
      |∫ d, replicaPairAverage (G t d) (fun σ => f σ - c)
          (fun a b => (deriv u cfield[N, t, d.2.1, k, a] * a (Fin.last N)) *
            (deriv u cfield[N, t, d.2.1, k, b] * b (Fin.last N))) ∂cavLaw[N, M, r]| ≤
        3 * (n + 1) ^ 2 * |D| ^ 2 * (A * S_eps) := fun k => by
    have hpt : ∀ d : Dis[N, M],
        |replicaPairAverage (G t d) (fun σ => f σ - c)
          (fun a b => (deriv u cfield[N, t, d.2.1, k, a] * a (Fin.last N)) *
            (deriv u cfield[N, t, d.2.1, k, b] * b (Fin.last N)))| ≤
          3 * (n + 1) ^ 2 * |D| ^ 2 * (sF d * sE d) := fun d => by
      have := hprob t ⟨ht0.le, ht1.le⟩ d
      have hum_k : Measurable fun σ : ℝ^(N + 1) =>
          deriv u cfield[N, t, d.2.1, k, σ] * σ (Fin.last N) := by
        have hc : Continuous fun σ : ℝ^(N + 1) => cfield[N, t, d.2.1, k, σ] := by fun_prop
        exact ((measurable_deriv u).comp hc.measurable).mul
          (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable
      have hub : ∀ σ : ℝ^(N + 1),
          |deriv u cfield[N, t, d.2.1, k, σ] * σ (Fin.last N)| ≤ |D| * |σ (Fin.last N)| := fun σ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ((hD1 _).trans (le_abs_self _)) (abs_nonneg _)
      exact (abs_replicaPairAverage_le_of_le_mul_abs hfc_m hum_k (abs_nonneg D) hub (hfc2_d d)
        (hε4_d d)).trans_eq (by ring)
    refine abs_integral_le_integral_abs.trans ((integral_mono (hIU k).abs
      (hprod_int.const_mul _) hpt).trans ?_)
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hprod_le (by positivity)
  have hPε_bd :
      |∫ d, replicaPairAverage (G t d) (fun σ => f σ - c)
          (fun a b => a (Fin.last N) * b (Fin.last N)) ∂cavLaw[N, M, r]| ≤
        3 * (n + 1) ^ 2 * (A * S_eps) := by
    have hpt : ∀ d : Dis[N, M],
        |replicaPairAverage (G t d) (fun σ => f σ - c)
          (fun a b => a (Fin.last N) * b (Fin.last N))| ≤
          3 * (n + 1) ^ 2 * (sF d * sE d) := fun d => by
      have := hprob t ⟨ht0.le, ht1.le⟩ d
      have h1 := abs_replicaPairAverage_le_of_le_mul_abs (B := 1) hfc_m
        (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable
        zero_le_one (fun σ => by simp) (hfc2_d d) (hε4_d d)
      exact h1.trans_eq (by ring)
    refine abs_integral_le_integral_abs.trans ((integral_mono hIPε.abs
      (hprod_int.const_mul _) hpt).trans ?_)
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hprod_le (by positivity)
  have hDε_bd :
      |∫ d, replicaDiff (G t d) (fun σ => f σ - c)
          (fun σ => σ (Fin.last N) ^ 2) ∂cavLaw[N, M, r]| ≤
        2 * n * (A * S_eps) := by
    have hpt : ∀ d : Dis[N, M],
        |replicaDiff (G t d) (fun σ => f σ - c) (fun σ => σ (Fin.last N) ^ 2)| ≤
          2 * n * (sF d * sE d) := fun d => by
      have := hprob t ⟨ht0.le, ht1.le⟩ d
      have h1 := abs_replicaDiff_le_of_le_mul_sq (B := 1) hfc_m
        (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const 2)
        zero_le_one (fun σ => by rw [one_mul, abs_of_nonneg (sq_nonneg _)]) (hfc2_d d) (hε4_d d)
      exact h1.trans_eq (by ring)
    refine abs_integral_le_integral_abs.trans ((integral_mono hIDε.abs
      (hprod_int.const_mul _) hpt).trans ?_)
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hprod_le (by positivity)
  -- Combine all four bounds
  have hsum_bd : |((N : ℝ) + 1)⁻¹ * (∑ k : Fin M, ∫ d, (replicaDiff (G t d) (fun σ => f σ - c)
          (fun σ => (deriv (deriv u) cfield[N, t, d.2.1, k, σ] +
            deriv u cfield[N, t, d.2.1, k, σ] ^ 2) * σ (Fin.last N) ^ 2) / 2 +
        replicaPairAverage (G t d) (fun σ => f σ - c)
          (fun a b => (deriv u cfield[N, t, d.2.1, k, a] * a (Fin.last N)) *
            (deriv u cfield[N, t, d.2.1, k, b] * b (Fin.last N)))) ∂cavLaw[N, M, r])| ≤
      10 * (n * (|D| + |D| ^ 2) + 3 * (n + 1) ^ 2 * |D| ^ 2) * (A * S_eps) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hk_bd : ∀ k : Fin M,
        |∫ d, (replicaDiff (G t d) (fun σ => f σ - c)
            (fun σ => (deriv (deriv u) cfield[N, t, d.2.1, k, σ] +
              deriv u cfield[N, t, d.2.1, k, σ] ^ 2) * σ (Fin.last N) ^ 2) / 2 +
          replicaPairAverage (G t d) (fun σ => f σ - c)
            (fun a b => (deriv u cfield[N, t, d.2.1, k, a] * a (Fin.last N)) *
              (deriv u cfield[N, t, d.2.1, k, b] * b (Fin.last N)))) ∂cavLaw[N, M, r]| ≤
          (n * (|D| + |D| ^ 2) + 3 * (n + 1) ^ 2 * |D| ^ 2) * (A * S_eps) := fun k => by
      rw [integral_add ((hIV k).div_const 2) (hIU k), integral_div]
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
      have h1 := div_le_div_of_nonneg_right (hV_bd k) zero_le_two
      have h2 := hU_bd k
      linarith
    have hsum_le := (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun k _ => hk_bd k).trans_eq (by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))
    refine (mul_le_mul_of_nonneg_left hsum_le (by positivity)).trans ?_
    have hα : ((N : ℝ) + 1)⁻¹ * (M : ℝ) ≤ 10 := by
      rw [inv_mul_le_iff₀ (by positivity), mul_comm]
      exact_mod_cast hM
    rw [← mul_assoc, mul_assoc (10 : ℝ)]
    exact mul_le_mul_of_nonneg_right hα (by positivity)
  have hrem_bd : |∫ d, ((r : ℝ) * replicaPairAverage (G t d) (fun σ => f σ - c)
          (fun a b => a (Fin.last N) * b (Fin.last N)) +
        rBar * replicaDiff (G t d) (fun σ => f σ - c) (fun σ => σ (Fin.last N) ^ 2) / 2)
        ∂cavLaw[N, M, r]| ≤
      (R * (3 * (n + 1) ^ 2) + (R + R_diff) * n) * (A * S_eps) := by
    rw [integral_add (hIPε.const_mul _) ((hIDε.const_mul _).div_const 2), integral_const_mul,
      integral_div, integral_const_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg r.coe_nonneg, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), abs_mul]
    have hrBar_abs : |rBar| ≤ R + R_diff := abs_le.2 ⟨by linarith [r.coe_nonneg], by linarith⟩
    have h1 : (r : ℝ) * |∫ d, replicaPairAverage (G t d) (fun σ => f σ - c)
          (fun a b => a (Fin.last N) * b (Fin.last N)) ∂cavLaw[N, M, r]| ≤
        R * (3 * (n + 1) ^ 2 * (A * S_eps)) :=
      mul_le_mul hrR hPε_bd (abs_nonneg _) hR
    have h2 : |rBar| * |∫ d, replicaDiff (G t d) (fun σ => f σ - c)
          (fun σ => σ (Fin.last N) ^ 2) ∂cavLaw[N, M, r]| / 2 ≤
        (R + R_diff) * (2 * n * (A * S_eps)) / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul hrBar_abs hDε_bd (abs_nonneg _) (by linarith))
        zero_le_two
    linarith
  have htot := (abs_sub _ _).trans (add_le_add hsum_bd hrem_bd)
  refine htot.trans ?_
  have heq : 10 * (n * (|D| + |D| ^ 2) + 3 * (n + 1) ^ 2 * |D| ^ 2) * (A * S_eps) +
      (R * (3 * (n + 1) ^ 2) + (R + R_diff) * n) * (A * S_eps) = B_tot * S_eps * A := by
    dsimp only [B_tot]; ring
  rw [heq]
  have : B_tot * S_eps * A ≤ K * A := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hA
  exact this

end CavityDerivativeBound

section Lemma3211

/-- **Talagrand, Lemma 3.2.11 (at rate `K / √N`, Eq. (3.112)) for `ρ_t`:**
uniformly in `t ∈ [0, 1]` and `N ≥ 3` (so `4 ≤ N + 1`),
`|ν_t(R_{1,1}) - ν_1(R_{1,1})| ≤ K / √(N + 1)`, where `K` depends only on
`κ₀, h₀, D, R, R_diff`. -/
theorem exists_abs_shcherbinaTirozziCavity_selfOverlap_sub_le
    (κ₀ h₀ D R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R →
      (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) → 4 ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      let G (s : ℝ) (d : Dis[N, M]) : Measure (ℝ^(N + 1)) :=
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar s d.1 u d.2.1 d.2.2 σ
      |(∫ d, ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(G t d) ∂cavLaw[N, M, r]) -
          ∫ d, ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(G 1 d) ∂cavLaw[N, M, r]| ≤
        K / Real.sqrt ((N : ℝ) + 1) := by
  obtain ⟨K_c, hK_c, hconc⟩ :=
    exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_pow_le κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  obtain ⟨K_d, hK_d, hderiv⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_abs_le_of_sub_const_sq_le (R_rep := Fin 1)
      κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  set K : ℝ := K_d * Real.sqrt K_c + 1
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, fun N M κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM hN4
    huc hu0 hgrow hu1 hu2 hD1 hD2 => ?_⟩
  intro G
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hD_lip : ∀ a b : ℝ, |deriv u a - deriv u b| ≤ D * |a - b| := fun a b => by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := deriv u) (C := D)
      (fun x _ => hu2 x) (fun x _ => by simpa only [Real.norm_eq_abs] using hD2 x)
      (Set.mem_univ b) (Set.mem_univ a)
    simpa only [Real.norm_eq_abs] using h
  set f : (Fin 1 → ℝ^(N + 1)) → ℝ := fun σ => ((N : ℝ) + 1)⁻¹ * ‖σ 0‖ ^ 2
  have hfm : Measurable f := ((measurable_pi_apply (0 : Fin 1)).norm.pow_const 2).const_mul _
  have hfb : ∀ σ : Fin 1 → ℝ^(N + 1), |f σ| ≤ ((N : ℝ) + 1)⁻¹ * ∏ l : Fin 1, (1 + ‖σ l‖) ^ 2 := by
    intro σ
    rw [Fin.prod_univ_one]
    dsimp only [f]
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) 2
  set φ : ℝ → ℝ := fun s => ∫ d, ∫ σ : Fin 1 → ℝ^(N + 1), f σ
      ∂(Measure.pi fun _ : Fin 1 => G s d) ∂cavLaw[N, M, r]
  have hφ_eq : ∀ s ∈ Icc (0 : ℝ) 1,
      φ s = ∫ d, ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(G s d) ∂cavLaw[N, M, r] := by
    intro s hs
    refine integral_congr_ae (ae_of_all _ fun d => ?_)
    have : IsProbabilityMeasure (G s d) := isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
        (mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hrr)) hum hu0 d.2.1 d.2.2)
    exact integral_pi_eval (G s d) (0 : Fin 1) (fun x : ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2)
      ((measurable_norm.pow_const 2).const_mul _).aestronglyMeasurable
  have hcont : ContinuousOn φ (Icc 0 1) :=
    continuousOn_integral_integral_pi_shcherbinaTirozziCavity (R := Fin 1) hκ0 r hrr hu0 hu1 hD1
      hfm hfb
  have hder : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt φ d s ∧
      |d| ≤ K_d * Real.sqrt (K_c / ((N : ℝ) + 1)) := by
    intro s hs
    obtain ⟨hc_i, hc_le⟩ := hconc N M 1 κ h s rBar r u hκ hh hs.1.le hs.2.le hrr hrR hrr_diff hM
      (by omega) huc hu0 hgrow hu1 hD1 hD_lip
    simp only [mul_one, Nat.cast_one, pow_one] at hc_i hc_le
    set c_s : ℝ := ∫ e, ∫ τ : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G s e) ∂cavLaw[N, M, r]
    have hpi_eq : ∀ d : Dis[N, M],
        ∫ σ : Fin 1 → ℝ^(N + 1), (f σ - c_s) ^ 2 ∂(Measure.pi fun _ : Fin 1 => G s d) =
          ∫ x : ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - c_s) ^ 2 ∂(G s d) := fun d => by
      have : IsProbabilityMeasure (G s d) := isProbabilityMeasure_tilted
        (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
          (mul_nonneg (sub_nonneg.2 hs.2.le) (sub_nonneg.2 hrr)) hum hu0 d.2.1 d.2.2)
      exact integral_pi_eval (G s d) (0 : Fin 1)
        (fun x : ℝ^(N + 1) => (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - c_s) ^ 2)
        ((((measurable_norm.pow_const 2).const_mul _).sub_const c_s).pow_const
          2).aestronglyMeasurable
    have hsq_eq : (Real.sqrt (K_c / ((N : ℝ) + 1))) ^ 2 = K_c / ((N : ℝ) + 1) :=
      Real.sq_sqrt (by positivity)
    exact hderiv N M κ h s rBar r u hκ hh hs.1 hs.2 hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD1 hD2
      hfm hfb (Real.sqrt_nonneg _)
      (hc_i.congr (ae_of_all _ fun d => (hpi_eq d).symm))
      ((integral_congr_ae (ae_of_all _ hpi_eq)).trans_le (hc_le.trans_eq hsq_eq.symm))
  have hmv := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hcont hder
    (x := 1) (y := t) ⟨zero_le_one, le_rfl⟩ ⟨ht0, ht1⟩
  rw [hφ_eq t ⟨ht0, ht1⟩, hφ_eq 1 ⟨zero_le_one, le_rfl⟩] at hmv
  have hle1 : |t - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  refine hmv.trans ?_
  calc K_d * Real.sqrt (K_c / ((N : ℝ) + 1)) * |t - 1|
      ≤ K_d * Real.sqrt (K_c / ((N : ℝ) + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hle1 (by positivity)
    _ = K_d * Real.sqrt K_c / Real.sqrt ((N : ℝ) + 1) := by
        rw [mul_one, Real.sqrt_div hK_c, mul_div_assoc]
    _ ≤ K / Real.sqrt ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by dsimp only [K]; linarith) (Real.sqrt_nonneg _)

/-- **Talagrand, Lemma 3.2.11 (at rate `K / √N`, Eq. (3.112)) for `q_t`:**
uniformly in `t ∈ [0, 1]` and `N ≥ 3` (so `4 ≤ N + 1`),
`|ν_t(R_{1,2}) - ν_1(R_{1,2})| ≤ K / √(N + 1)`, where `K` depends only on
`κ₀, h₀, D, R, R_diff`. -/
theorem exists_abs_shcherbinaTirozziCavity_overlap_sub_le
    (κ₀ h₀ D R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R →
      (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) → 4 ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      let G (s : ℝ) (d : Dis[N, M]) : Measure (ℝ^(N + 1)) :=
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar s d.1 u d.2.1 d.2.2 σ
      |(∫ d, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
            ∂(Measure.pi fun _ : Fin 2 => G t d) ∂cavLaw[N, M, r]) -
          ∫ d, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
            ∂(Measure.pi fun _ : Fin 2 => G 1 d) ∂cavLaw[N, M, r]| ≤
        K / Real.sqrt ((N : ℝ) + 1) := by
  obtain ⟨K_c, hK_c, hconc⟩ :=
    exists_integral_shcherbinaTirozziCavity_overlap_sub_pow_le κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  obtain ⟨K_d, hK_d, hderiv⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_abs_le_of_sub_const_sq_le (R_rep := Fin 2)
      κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  set K : ℝ := K_d * Real.sqrt K_c + 1
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, fun N M κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM hN4
    huc hu0 hgrow hu1 hu2 hD1 hD2 => ?_⟩
  intro G
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hD_lip : ∀ a b : ℝ, |deriv u a - deriv u b| ≤ D * |a - b| := fun a b => by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := deriv u) (C := D)
      (fun x _ => hu2 x) (fun x _ => by simpa only [Real.norm_eq_abs] using hD2 x)
      (Set.mem_univ b) (Set.mem_univ a)
    simpa only [Real.norm_eq_abs] using h
  set f : (Fin 2 → ℝ^(N + 1)) → ℝ := fun p => ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
  have hfm : Measurable f :=
    ((measurable_pi_apply (0 : Fin 2)).inner (measurable_pi_apply (1 : Fin 2))).const_mul _
  have hfb : ∀ p : Fin 2 → ℝ^(N + 1), |f p| ≤ ((N : ℝ) + 1)⁻¹ * ∏ l : Fin 2, (1 + ‖p l‖) ^ 1 := by
    intro p
    rw [Fin.prod_univ_two, pow_one, pow_one]
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (abs_real_inner_le_norm (p 0) (p 1)).trans (mul_le_mul
      (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_left zero_le_one)
      (norm_nonneg _) (by positivity))
  set φ : ℝ → ℝ := fun s => ∫ d, ∫ p : Fin 2 → ℝ^(N + 1), f p
      ∂(Measure.pi fun _ : Fin 2 => G s d) ∂cavLaw[N, M, r]
  have hcont : ContinuousOn φ (Icc 0 1) :=
    continuousOn_integral_integral_pi_shcherbinaTirozziCavity (R := Fin 2) hκ0 r hrr hu0 hu1 hD1
      hfm hfb
  have hder : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt φ d s ∧
      |d| ≤ K_d * Real.sqrt (K_c / ((N : ℝ) + 1)) := by
    intro s hs
    obtain ⟨hc_i, hc_le⟩ := hconc N M 1 κ h s rBar r u hκ hh hs.1.le hs.2.le hrr hrR hrr_diff hM
      (by omega) huc hu0 hgrow hu1 hD1 hD_lip
    simp only [mul_one, Nat.cast_one, pow_one] at hc_i hc_le
    -- Identify `Measure.pi (Fin 2)` with `G.prod G`
    have hmp2 : ∀ d : Dis[N, M],
        MeasurePreserving (fun p : Fin 2 → ℝ^(N + 1) => (p 0, p 1))
          (Measure.pi fun _ : Fin 2 => G s d) ((G s d).prod (G s d)) := fun d => by
      have : IsProbabilityMeasure (G s d) := isProbabilityMeasure_tilted
        (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
          (mul_nonneg (sub_nonneg.2 hs.2.le) (sub_nonneg.2 hrr)) hum hu0 d.2.1 d.2.2)
      exact measurePreserving_piFinTwo (fun _ : Fin 2 => G s d)
    set c_s : ℝ := ∫ e, ∫ q : ℝ^(N + 1) × ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫
        ∂((G s e).prod (G s e)) ∂cavLaw[N, M, r]
    have hpi_eq : ∀ d : Dis[N, M],
        ∫ p : Fin 2 → ℝ^(N + 1), (f p - c_s) ^ 2 ∂(Measure.pi fun _ : Fin 2 => G s d) =
          ∫ q : ℝ^(N + 1) × ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ - c_s) ^ 2
            ∂((G s d).prod (G s d)) := fun d => by
      have hc : Continuous fun q : ℝ^(N + 1) × ℝ^(N + 1) =>
          (((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ - c_s) ^ 2 := by fun_prop
      rw [← (hmp2 d).map_eq, integral_map (hmp2 d).measurable.aemeasurable hc.aestronglyMeasurable]
    have hsq_eq : (Real.sqrt (K_c / ((N : ℝ) + 1))) ^ 2 = K_c / ((N : ℝ) + 1) :=
      Real.sq_sqrt (by positivity)
    exact hderiv N M κ h s rBar r u hκ hh hs.1 hs.2 hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD1 hD2
      hfm hfb (Real.sqrt_nonneg _)
      (hc_i.congr (ae_of_all _ fun d => (hpi_eq d).symm))
      ((integral_congr_ae (ae_of_all _ hpi_eq)).trans_le (hc_le.trans_eq hsq_eq.symm))
  have hmv := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hcont hder
    (x := 1) (y := t) ⟨zero_le_one, le_rfl⟩ ⟨ht0, ht1⟩
  have hle1 : |t - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  refine hmv.trans ?_
  calc K_d * Real.sqrt (K_c / ((N : ℝ) + 1)) * |t - 1|
      ≤ K_d * Real.sqrt (K_c / ((N : ℝ) + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hle1 (by positivity)
    _ = K_d * Real.sqrt K_c / Real.sqrt ((N : ℝ) + 1) := by
        rw [mul_one, Real.sqrt_div hK_c, mul_div_assoc]
    _ ≤ K / Real.sqrt ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by dsimp only [K]; linarith) (Real.sqrt_nonneg _)

end Lemma3211

section Proposition3212

/-- Auxiliary quadratic triangle bound: under probability measures `P` and `G d`,
`√(∫ d, ∫ (X - c)² ∂G d ∂P) ≤ √(∫ d, ∫ (X - c_t)² ∂G d ∂P) + |c_t - c|`. -/
private lemma sqrt_integral_integral_sub_sq_le {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → Measure α}
    [∀ d, IsProbabilityMeasure (G d)] {X : α → ℝ} {c c_t : ℝ}
    (hXm : Measurable X)
    (hX_int : ∀ d, Integrable (fun x => (X x - c_t) ^ 2) (G d))
    (h_int : Integrable (fun d => ∫ x, (X x - c_t) ^ 2 ∂(G d)) P) :
    Real.sqrt (∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P) ≤
      Real.sqrt (2 * ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + Real.sqrt 2 * |c_t - c| := by
  have hpt_x : ∀ x, (X x - c) ^ 2 ≤ 2 * (X x - c_t) ^ 2 + 2 * (c_t - c) ^ 2 := fun x => by
    have hsq := sq_nonneg ((X x - c_t) - (c_t - c))
    have hid : (X x - c) ^ 2 = ((X x - c_t) + (c_t - c)) ^ 2 := by ring
    nlinarith [hid, hsq]
  have hpt_d : ∀ d, ∫ x, (X x - c) ^ 2 ∂(G d) ≤
      2 * (∫ x, (X x - c_t) ^ 2 ∂(G d)) + 2 * (c_t - c) ^ 2 := fun d => by
    have hi_c : Integrable (fun x => (X x - c) ^ 2) (G d) :=
      (((hX_int d).const_mul 2).add (integrable_const _)).mono'
        ((hXm.sub_const c).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt_x x)
    refine (integral_mono hi_c (((hX_int d).const_mul 2).add (integrable_const _)) hpt_x).trans_eq ?_
    change ∫ x, (2 * (X x - c_t) ^ 2 + 2 * (c_t - c) ^ 2) ∂(G d) = _
    rw [integral_add ((hX_int d).const_mul 2) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  have htot : ∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P ≤
      2 * (∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + 2 * (c_t - c) ^ 2 := by
    by_cases hi : Integrable (fun d => ∫ x, (X x - c) ^ 2 ∂(G d)) P
    · refine (integral_mono hi ((h_int.const_mul 2).add (integrable_const _)) hpt_d).trans_eq ?_
      change ∫ d, (2 * (∫ x, (X x - c_t) ^ 2 ∂(G d)) + 2 * (c_t - c) ^ 2) ∂P = _
      rw [integral_add (h_int.const_mul 2) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul]
    · rw [integral_undef hi]
      exact add_nonneg (mul_nonneg zero_le_two (integral_nonneg fun d =>
        integral_nonneg fun _ => sq_nonneg _)) (by positivity)
  have hsq_add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    linarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P)
      ≤ Real.sqrt (2 * (∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + 2 * (c_t - c) ^ 2) :=
        Real.sqrt_le_sqrt htot
    _ ≤ Real.sqrt (2 * ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + Real.sqrt (2 * (c_t - c) ^ 2) :=
        hsq_add _ _ (mul_nonneg zero_le_two (integral_nonneg fun _ =>
          integral_nonneg fun _ => sq_nonneg _)) (by positivity)
    _ = Real.sqrt (2 * ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + Real.sqrt 2 * |c_t - c| := by
        congr 1; rw [Real.sqrt_mul zero_le_two, Real.sqrt_sq_eq_abs]

/-- Recenter a second-moment bound when the displacement is bounded at the same scale. -/
private lemma sqrt_integral_integral_sub_sq_le_of_le_div {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → Measure α}
    [∀ d, IsProbabilityMeasure (G d)] {X : α → ℝ} {c c_t n A B : ℝ}
    (hA : 0 ≤ A) (hXm : Measurable X)
    (hX_int : ∀ d, Integrable (fun x => (X x - c_t) ^ 2) (G d))
    (h_int : Integrable (fun d => ∫ x, (X x - c_t) ^ 2 ∂(G d)) P)
    (hvar : ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P ≤ A / n)
    (hmean : |c_t - c| ≤ B / Real.sqrt n) :
    Real.sqrt (∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P) ≤
      (Real.sqrt (2 * A) + Real.sqrt 2 * B) / Real.sqrt n := by
  refine (sqrt_integral_integral_sub_sq_le hXm hX_int h_int).trans ?_
  rw [add_div, ← Real.sqrt_div (mul_nonneg zero_le_two hA), mul_div_assoc, mul_div_assoc]
  exact add_le_add (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar zero_le_two))
    (mul_le_mul_of_nonneg_left hmean (Real.sqrt_nonneg _))

/-- The coordinate expansion of the squared norm of the mean spin. -/
private lemma norm_integral_sq_eq_sum_sq {ι : Type*} [Fintype ι]
    {μ : Measure (EuclideanSpace ℝ ι)} (hi : Integrable (fun x : EuclideanSpace ℝ ι => x) μ) :
    ‖∫ σ, σ ∂μ‖ ^ 2 = ∑ i, (∫ σ, σ i ∂μ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hi]
  rfl

/-- A second norm moment controls the centered square of a scaled replica inner product. -/
private lemma integrable_sq_scaled_inner_sub_pi {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsProbabilityMeasure μ] (s c : ℝ)
    (hnorm : Integrable (fun x : E => ‖x‖ ^ 2) μ) :
    Integrable (fun p : Fin 2 → E => (s * ⟪p 0, p 1⟫ - c) ^ 2)
      (Measure.pi fun _ : Fin 2 => μ) := by
  have hprod := Integrable.fintype_prod (f := fun _ : Fin 2 => fun x : E => ‖x‖ ^ 2)
    (fun _ => hnorm)
  simp only [Fin.prod_univ_two] at hprod
  refine integrable_sub_pow_of_integrable_abs_pow
    (((measurable_pi_apply (0 : Fin 2)).inner (measurable_pi_apply (1 : Fin 2))).const_mul _)
    (c := 0) ((hprod.const_mul (s ^ 2)).mono' (by fun_prop) (ae_of_all _ fun p => ?_)) c
  rw [sub_zero, Real.norm_of_nonneg (sq_nonneg _), abs_mul, mul_pow, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2) (sq_nonneg _)

/-- **Talagrand, Proposition 3.2.12 (Eq. (3.115)):** at the physical parameters `(q, ρ, r, r̄)`
for the Shcherbina--Tirozzi model on `ℝ^(N+1)` with `M` constraints (`M ≤ 10 (N + 1)`,
`4 ≤ N + 1`), the replica-symmetric equations (3.69), (3.74), (3.75) hold with accuracy
`K / √(N + 1)`:
```
|ρ - (1 / a + (r + h²) / a²)| ≤ K / √(N + 1),
|q - (r + h²) / a²| ≤ K / √(N + 1),
```
where `a = 2 κ + r - r̄ > 0`, and `K > 0` depends only on `κ₀, h₀, D`. -/
theorem exists_shcherbinaTirozzi_rsEquations_accuracy (κ₀ h₀ D : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h : ℝ) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → M ≤ 10 * (N + 1) → 4 ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      Differentiable ℝ (deriv (deriv u)) → Differentiable ℝ (deriv (deriv (deriv u))) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) →
      let P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :=
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      let G : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → Measure (ℝ^(N + 1)) := fun d =>
        volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ
      let ρ : ℝ := ∫ d, ∫ σ, ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 ∂(G d) ∂P
      let q : ℝ := ∫ d, ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G d)) ^ 2 ∂P
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := (M / (N + 1)) * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := (M / (N + 1)) * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      let a : ℝ := 2 * κ + r - rBar
      0 < a ∧
        |ρ - (a⁻¹ + (r + h ^ 2) / a ^ 2)| ≤ K / Real.sqrt ((N : ℝ) + 1) ∧
        |q - (r + h ^ 2) / a ^ 2| ≤ K / Real.sqrt ((N : ℝ) + 1) := by
  obtain ⟨Q, hQ0, hphys⟩ := exists_shcherbinaTirozzi_physical_parameter_bounds κ₀ h₀ D hκ₀
  set R : ℝ := 10 * D ^ 2
  set R_diff : ℝ := 10 * (2 * D ^ 2 + |D|)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hRdiff0 : 0 ≤ R_diff := by dsimp only [R_diff]; positivity
  obtain ⟨K_sq, hK_sq, hprop_sq⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_sq_last_abs_le κ₀ h₀ D Q R R_diff hκ₀ hQ0 hR0 hRdiff0
  obtain ⟨K_mul, hK_mul, hprop_mul⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_mul_last_abs_le κ₀ h₀ D Q R R_diff hκ₀ hQ0 hR0
      hRdiff0
  obtain ⟨K_c1, hK_c1, hconc1⟩ :=
    exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_pow_le κ₀ h₀ D R R_diff hκ₀ hR0 hRdiff0
  obtain ⟨K_c2, hK_c2, hconc2⟩ :=
    exists_integral_shcherbinaTirozziCavity_overlap_sub_pow_le κ₀ h₀ D R R_diff hκ₀ hR0 hRdiff0
  obtain ⟨K_l1, hK_l1, hlem1⟩ :=
    exists_abs_shcherbinaTirozziCavity_selfOverlap_sub_le κ₀ h₀ D R R_diff hκ₀ hR0 hRdiff0
  obtain ⟨K_l2, hK_l2, hlem2⟩ :=
    exists_abs_shcherbinaTirozziCavity_overlap_sub_le κ₀ h₀ D R R_diff hκ₀ hR0 hRdiff0
  set E_c : ℝ := Real.sqrt (2 * K_c2) + Real.sqrt 2 * K_l2 +
    (Real.sqrt (2 * K_c1) + Real.sqrt 2 * K_l1) + 1
  set K : ℝ := max K_sq K_mul * E_c + 1
  have hEc0 : 0 ≤ E_c := by dsimp only [E_c]; positivity
  have hK0 : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK0, fun N M κ h u hκ hh hM hN4 huc hu0 hgrow hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 => ?_⟩
  intro P G ρ q c Z V W r rBar a
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have huD : -D ≤ u 0 := by simpa only [abs_zero, add_zero, mul_one] using hgrow 0
  have hD_lip : ∀ x y : ℝ, |deriv u x - deriv u y| ≤ D * |x - y| := fun x y => by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := deriv u) (C := D)
      (fun z _ => hu2 z) (fun z _ => by simpa only [Real.norm_eq_abs] using hD2 z)
      (Set.mem_univ y) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using h
  -- Physical parameter bounds
  obtain ⟨hq0, hqρ, hρQ, hr0, hrR, hrr, hrr_diff0⟩ :=
    hphys N M κ h D u hκ hh hM huc hu0 hgrow hu1 hu2 hD1 hD2
  have hrr_diff : r - rBar ≤ R_diff := hrr_diff0.trans (by
    dsimp only [R_diff]; rw [abs_of_nonneg hD0])
  have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  -- Proposition 3.2.4: express the RS residuals as `ν_1 - ν_0`
  obtain ⟨ha_pos, hres_ρ, hres_q⟩ :=
    shcherbinaTirozzi_overlaps_sub_decoupled (N := N) (M := M) (κ := κ) (h := h) (D := D) (D₂ := D)
      hκ0 hM huc hu0 hgrow hu1 hu2 hD1 hD2
  refine ⟨ha_pos, ?_⟩
  -- Case `M = 0`: the cavity path is constant (`r = rBar = 0`, no constraints), so residual is 0!
  rcases M with _ | M'
  · have hr_zero : r = 0 := by dsimp only [r]; simp
    have hrBar_zero : rBar = 0 := by dsimp only [rBar]; simp
    have hH0 : ∀ (y : ℝ) (d : (Fin 0 → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) (σ : ℝ^(N + 1)),
        shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ =
          shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ - σ (Fin.last N) * y := fun y d σ => by
      simp only [shcherbinaTirozziCavityHamiltonian, shcherbinaTirozziHamiltonian,
        Finset.univ_eq_empty, Finset.sum_empty, sub_zero, hr_zero, hrBar_zero,
        Real.sqrt_one, one_mul, mul_zero, zero_mul, zero_div, add_zero]
    have hy0 : gaussianReal 0 r.toNNReal = Measure.dirac 0 := by
      have : r.toNNReal = 0 := by rw [hr_zero]; simp
      rw [this, gaussianReal_zero_var]
    have hG0 : ∀ d, (volume.tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 0 u d.1 d.2 σ) = G d := fun d => by
      dsimp only [G]; congr 1; funext σ; rw [hH0]; ring
    have hρ0 : ρ - (a⁻¹ + (r + h ^ 2) / a ^ 2) = 0 := by
      rw [hres_ρ, hy0, integral_dirac]
      change (∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂(G d) ∂P) -
        ∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂(volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 0 u d.1 d.2 σ) ∂P = 0
      simp_rw [hG0]; ring
    have hq0_eq : q - (r + h ^ 2) / a ^ 2 = 0 := by
      rw [hres_q, hy0, integral_dirac]
      change (∫ d, (∫ σ, σ (Fin.last N) ∂(G d)) ^ 2 ∂P) -
        ∫ d, (∫ σ, σ (Fin.last N) ∂(volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 0 u d.1 d.2 σ)) ^ 2 ∂P = 0
      simp_rw [hG0]; ring
    rw [hρ0, hq0_eq, abs_zero]
    exact ⟨by positivity, by positivity⟩
  -- Case `M = M' + 1`: apply Proposition 3.2.10 + Lemma 3.2.11 + Eq. (3.111)
  have hM'_le : M' ≤ 10 * (N + 1) := by omega
  set P_full : Measure Dis[N, M' + 1] := cavLaw[N, M' + 1, r.toNNReal]
  set G_full : ℝ → Dis[N, M' + 1] → Measure (ℝ^(N + 1)) := fun s d =>
    volume.tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar s d.1 u d.2.1 d.2.2 σ
  have hprob : ∀ s ∈ Icc (0 : ℝ) 1, ∀ d : Dis[N, M' + 1],
      IsProbabilityMeasure (G_full s d) := fun s hs d =>
    isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
        (mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (by rwa [hr_coe]))) hum hu0 d.2.1 d.2.2)
  have hfour (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (d : Dis[N, M' + 1]) :
      Integrable (fun x : ℝ^(N + 1) => ‖x‖ ^ 4) (G_full s d) :=
    (memLp_of_poly_bound_of_confining hκ0
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r.toNNReal rBar s d.1 hum
        d.2.1 d.2.2).neg
      (fun σ => by
        rw [zero_add]
        exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1
          (by rwa [hr_coe]) hs.1 hs.2 hu0 d.2.1 d.2.2 σ)
      (measurable_norm.pow_const 4).aestronglyMeasurable (C := 1) (m := 4) (fun x => by
        rw [one_mul, Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) 4)
      1).integrable le_rfl
  have hG1 : ∀ d : Dis[N, M' + 1], G_full 1 d = G d.2 := fun d => by
    dsimp only [G_full, G]
    congr 1
    funext σ
    rw [shcherbinaTirozziCavityHamiltonian_one]
  -- Shared bound on the error term `Err(t)` for every `t ∈ (0, 1)`
  have hErr_bd : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
          (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => G_full t d) ∂P_full) +
        Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
          (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full t d) ∂P_full) +
        ((N : ℝ) + 1)⁻¹ ≤ E_c / Real.sqrt ((N : ℝ) + 1) := by
    intro t ht
    letI : ∀ d, IsProbabilityMeasure (G_full t d) := hprob t ⟨ht.1.le, ht.2.le⟩
    have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    -- 1. Self-overlap error `√(ν_t((R_{1,1} - ρ)²))`
    have h_self : Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
          (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full t d) ∂P_full) ≤
        (Real.sqrt (2 * K_c1) + Real.sqrt 2 * K_l1) / Real.sqrt ((N : ℝ) + 1) := by
      obtain ⟨hc_i, hc_le⟩ := hconc1 N (M' + 1) 1 κ h t rBar r.toNNReal u hκ hh ht.1.le ht.2.le
        (by rwa [hr_coe]) (by rwa [hr_coe]) (by rwa [hr_coe]) hM (by omega) huc hu0 hgrow hu1 hD1
        hD_lip
      simp only [mul_one, Nat.cast_one, pow_one] at hc_i hc_le
      set ρ_t : ℝ := ∫ e, ∫ τ : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G_full t e) ∂P_full
      have hρ1_eq : ∫ e, ∫ τ : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G_full 1 e) ∂P_full = ρ := by
        simp_rw [hG1]
        exact integral_prod_fun_snd_of_isProbabilityMeasure (gaussianReal 0 r.toNNReal) P
          (fun d => ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(G d))
      have hdiff1 : |ρ_t - ρ| ≤ K_l1 / Real.sqrt ((N : ℝ) + 1) := by
        rw [← hρ1_eq]
        exact hlem1 N (M' + 1) κ h t rBar r.toNNReal u hκ hh ht.1.le ht.2.le
          (by rwa [hr_coe]) (by rwa [hr_coe]) (by rwa [hr_coe]) hM hN4 huc hu0 hgrow hu1 hu2 hD1
          hD2
      have hX_int (d : Dis[N, M' + 1]) : Integrable (fun x : ℝ^(N + 1) =>
          (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ_t) ^ 2) (G_full t d) :=
        integrable_sub_pow_of_integrable_abs_pow
          ((measurable_norm.pow_const 2).const_mul _)
          (c := 0)
          (by simpa only [sub_zero, abs_mul, abs_of_nonneg (sq_nonneg _), mul_pow, ← pow_mul] using
              (hfour t ⟨ht.1.le, ht.2.le⟩ d).const_mul (|((N : ℝ) + 1)⁻¹| ^ 2))
          ρ_t
      exact sqrt_integral_integral_sub_sq_le_of_le_div (P := P_full) (G := G_full t)
        (X := fun x : ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2) hK_c1
        ((measurable_norm.pow_const 2).const_mul _) hX_int hc_i hc_le hdiff1
    -- 2. Overlap error `√(ν_t((R_{1,2} - q)²))`
    have h_ov : Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
          (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => G_full t d) ∂P_full) ≤
        (Real.sqrt (2 * K_c2) + Real.sqrt 2 * K_l2) / Real.sqrt ((N : ℝ) + 1) := by
      obtain ⟨hc_i, hc_le⟩ := hconc2 N (M' + 1) 1 κ h t rBar r.toNNReal u hκ hh ht.1.le ht.2.le
        (by rwa [hr_coe]) (by rwa [hr_coe]) (by rwa [hr_coe]) hM (by omega) huc hu0 hgrow hu1 hD1
        hD_lip
      simp only [mul_one, Nat.cast_one, pow_one] at hc_i hc_le
      set q_t : ℝ := ∫ e, ∫ p : ℝ^(N + 1) × ℝ^(N + 1),
        ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ ∂((G_full t e).prod (G_full t e)) ∂P_full
      have hqt_pi : q_t = ∫ e, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
          ∂(Measure.pi fun _ : Fin 2 => G_full t e) ∂P_full := by
        refine integral_congr_ae (ae_of_all _ fun e => ?_)
        exact (integral_pi_pair_eq_prod (G_full t e) (show (0 : Fin 2) ≠ 1 by decide)
          (fun x y => ((N : ℝ) + 1)⁻¹ * ⟪x, y⟫) (by fun_prop)).symm
      have hq1_eq : ∫ e, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
            ∂(Measure.pi fun _ : Fin 2 => G_full 1 e) ∂P_full = q := by
        have hpt1 : ∀ d : Dis[N, M' + 1],
            ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
              ∂(Measure.pi fun _ : Fin 2 => G_full 1 d) =
            ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G d.2)) ^ 2 := fun d => by
          have : IsProbabilityMeasure (G d.2) :=
            isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 _ _
          simp only [hG1 d]
          have hi := (memLp_id_shcherbinaTirozziGibbs hκ0 hum hu0 d.2.1 d.2.2).integrable
            one_le_two
          calc
            _ = ((N : ℝ) + 1)⁻¹ * ⟪∫ σ, σ ∂(G d.2), ∫ σ, σ ∂(G d.2)⟫ :=
              integral_pi_overlap_eq_mean_sq_inner (G d.2) hi rfl _
                (show (0 : Fin 2) ≠ 1 by decide)
            _ = _ := by rw [real_inner_self_eq_norm_sq, norm_integral_sq_eq_sum_sq hi]
        simp_rw [hpt1]
        exact integral_prod_fun_snd_of_isProbabilityMeasure (gaussianReal 0 r.toNNReal) P
          (fun d => ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ x, x i ∂(G d)) ^ 2)
      have hdiff2 : |q_t - q| ≤ K_l2 / Real.sqrt ((N : ℝ) + 1) := by
        rw [hqt_pi, ← hq1_eq]
        exact hlem2 N (M' + 1) κ h t rBar r.toNNReal u hκ hh ht.1.le ht.2.le
          (by rwa [hr_coe]) (by rwa [hr_coe]) (by rwa [hr_coe]) hM hN4 huc hu0 hgrow hu1 hu2 hD1
          hD2
      have hpi_sq (c : ℝ) (d : Dis[N, M' + 1]) :
          ∫ p : Fin 2 → ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - c) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => G_full t d) =
          ∫ p : ℝ^(N + 1) × ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - c) ^ 2
            ∂((G_full t d).prod (G_full t d)) :=
        integral_pi_pair_eq_prod (G_full t d) (show (0 : Fin 2) ≠ 1 by decide)
          (fun x y => (((N : ℝ) + 1)⁻¹ * ⟪x, y⟫ - c) ^ 2) (by fun_prop)
      have hpi_int : ∀ d : Dis[N, M' + 1], Integrable (fun p : Fin 2 → ℝ^(N + 1) =>
          (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q_t) ^ 2) (Measure.pi fun _ : Fin 2 => G_full t d) :=
        fun d => integrable_sq_scaled_inner_sub_pi (G_full t d)
          (((N : ℝ) + 1)⁻¹) q_t (integrable_norm_pow_of_le (f := id)
            aestronglyMeasurable_id (by decide : 2 ≤ 4) (hfour t ⟨ht.1.le, ht.2.le⟩ d))
      exact sqrt_integral_integral_sub_sq_le_of_le_div (P := P_full)
        (G := fun d => Measure.pi fun _ : Fin 2 => G_full t d)
        (X := fun p : Fin 2 → ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫) hK_c2
        (((measurable_pi_apply (0 : Fin 2)).inner (measurable_pi_apply (1 : Fin 2))).const_mul _)
        hpi_int (hc_i.congr (ae_of_all _ fun d => (hpi_sq q_t d).symm))
        ((integral_congr_ae (ae_of_all _ (hpi_sq q_t))).trans_le hc_le) hdiff2
    -- 3. `((N : ℝ) + 1)⁻¹ ≤ 1 / √((N : ℝ) + 1)`
    have h_inv : ((N : ℝ) + 1)⁻¹ ≤ 1 / Real.sqrt ((N : ℝ) + 1) := by
      rw [one_div]
      refine inv_anti₀ (Real.sqrt_pos.2 hN0) ?_
      have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
      exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    calc Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
            (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => G_full t d) ∂P_full) +
          Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
            (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full t d) ∂P_full) +
          ((N : ℝ) + 1)⁻¹
        ≤ (Real.sqrt (2 * K_c2) + Real.sqrt 2 * K_l2) / Real.sqrt ((N : ℝ) + 1) +
            (Real.sqrt (2 * K_c1) + Real.sqrt 2 * K_l1) / Real.sqrt ((N : ℝ) + 1) +
            1 / Real.sqrt ((N : ℝ) + 1) := add_le_add (add_le_add h_ov h_self) h_inv
      _ = E_c / Real.sqrt ((N : ℝ) + 1) := by dsimp only [E_c]; ring
  -- Now bound `|ρ - (a⁻¹ + (r + h²) / a²)|` and `|q - (r + h²) / a²|` via MVT on `[0, 1]`
  constructor
  · -- `ρ` residual via `f = ε₁²`
    set f₁ : (Fin 1 → ℝ^(N + 1)) → ℝ := fun σ => (σ 0) (Fin.last N) ^ 2
    have hf₁m : Measurable f₁ :=
      (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
        (measurable_pi_apply (0 : Fin 1))).pow_const 2
    have hf₁b : ∀ σ : Fin 1 → ℝ^(N + 1), |f₁ σ| ≤ 1 * ∏ l : Fin 1, (1 + ‖σ l‖) ^ 2 := fun σ => by
      rw [one_mul, Fin.prod_univ_one]
      dsimp only [f₁]; rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((show |(σ 0) (Fin.last N)| ≤ ‖σ 0‖ by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ 0) (Fin.last N)).trans
          (by linarith)) 2
    set φ₁ : ℝ → ℝ := fun s => ∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G_full s d) ∂P_full
    have hφ₁_cont : ContinuousOn φ₁ (Icc 0 1) := by
      have hc := continuousOn_integral_integral_pi_shcherbinaTirozziCavity (R := Fin 1) hκ0
        r.toNNReal (by rwa [hr_coe]) hu0 hu1 hD1 hf₁m hf₁b
      refine hc.congr fun s hs => ?_
      refine integral_congr_ae (ae_of_all _ fun d => ?_)
      letI := hprob s hs d
      exact (integral_pi_eval (G_full s d) (0 : Fin 1)
        (fun x : ℝ^(N + 1) => x (Fin.last N) ^ 2)
        (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const
          2).aestronglyMeasurable).symm
    have hφ₁_der : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt φ₁ d t ∧
        |d| ≤ K / Real.sqrt ((N : ℝ) + 1) := by
      intro t ht
      obtain ⟨d, hd, hbd⟩ := hprop_sq N M' κ h t q ρ u hκ hh ht.1 ht.2 hq0 hqρ hρQ hM'_le huc
        hu0 hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD (by simpa only [Nat.cast_add, Nat.cast_one] using hrR)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hrr_diff)
      refine ⟨d, by simpa only [Nat.cast_add, Nat.cast_one] using hd, ?_⟩
      have hbd' : |d| ≤ K_sq * (E_c / Real.sqrt ((N : ℝ) + 1)) := by
        refine (by simpa only [Nat.cast_add, Nat.cast_one] using hbd).trans ?_
        exact mul_le_mul_of_nonneg_left (hErr_bd t ht) hK_sq.le
      refine hbd'.trans ?_
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      have hle : K_sq * E_c ≤ max K_sq K_mul * E_c :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hEc0
      dsimp only [K]; linarith
    have hmv := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hφ₁_cont hφ₁_der
      (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    simp only [sub_zero, abs_one, mul_one] at hmv
    -- Identify `φ₁ 1 - φ₁ 0` with `ρ - (a⁻¹ + (r + h²) / a²)`
    have hφ₁_1 : φ₁ 1 = ∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂(G d) ∂P := by
      dsimp only [φ₁]
      simp_rw [hG1]
      exact integral_prod_fun_snd_of_isProbabilityMeasure (gaussianReal 0 r.toNNReal) P
        (fun d => ∫ x, x (Fin.last N) ^ 2 ∂(G d))
    have hφ₁_0 : φ₁ 0 = ∫ y, ∫ d, ∫ σ, σ (Fin.last N) ^ 2
        ∂(volume.tilted fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ)
        ∂P ∂(gaussianReal 0 r.toNNReal) := by
      dsimp only [φ₁, G_full, P_full]
      simp_rw [hr_coe]
      have hA0 := integrable_integral_pi_shcherbinaTirozziCavity (R := Fin 1)
        (N := N) (M := M' + 1) hκ0 r.toNNReal (by rwa [hr_coe]) (t := 0)
        ⟨le_rfl, zero_le_one⟩ hu0 hu1 hD1 (fun _ => hf₁b) (hf₁m.comp measurable_snd)
      have hpt : ∀ d : Dis[N, M' + 1],
          ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G_full 0 d) =
            ∫ x : Fin 1 → ℝ^(N + 1), f₁ x ∂(Measure.pi fun _ : Fin 1 => G_full 0 d) :=
        fun d => by
          letI : IsProbabilityMeasure (G_full 0 d) := hprob 0 ⟨le_rfl, zero_le_one⟩ d
          exact (integral_pi_eval (G_full 0 d) (0 : Fin 1)
            (fun x : ℝ^(N + 1) => x (Fin.last N) ^ 2) (by fun_prop)).symm
      have hi := integral_prod _ (hA0.congr (ae_of_all _ fun d => (hpt d).symm))
      simpa only [G_full, P_full, hr_coe] using hi
    rw [hres_ρ, ← hφ₁_1, ← hφ₁_0]
    exact hmv
  · -- `q` residual via `f = ε₁ ε₂`
    set f₂ : (Fin 2 → ℝ^(N + 1)) → ℝ := fun σ => (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
    have hf₂m : Measurable f₂ :=
      (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
        (measurable_pi_apply (0 : Fin 2))).mul
      (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
        (measurable_pi_apply (1 : Fin 2)))
    have hf₂b : ∀ σ : Fin 2 → ℝ^(N + 1), |f₂ σ| ≤ 1 * ∏ l : Fin 2, (1 + ‖σ l‖) ^ 1 := fun σ => by
      rw [one_mul, Fin.prod_univ_two, pow_one, pow_one]
      dsimp only [f₂]; rw [abs_mul]
      exact mul_le_mul
        ((show |(σ 0) (Fin.last N)| ≤ ‖σ 0‖ by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ 0) (Fin.last N)).trans
          (by linarith))
        ((show |(σ 1) (Fin.last N)| ≤ ‖σ 1‖ by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ 1) (Fin.last N)).trans
          (by linarith))
        (abs_nonneg _) (by positivity)
    set φ₂ : ℝ → ℝ := fun s => ∫ d, ∫ σ : Fin 2 → ℝ^(N + 1),
        (σ 0) (Fin.last N) * (σ 1) (Fin.last N) ∂(Measure.pi fun _ : Fin 2 => G_full s d) ∂P_full
    have hφ₂_cont : ContinuousOn φ₂ (Icc 0 1) :=
      continuousOn_integral_integral_pi_shcherbinaTirozziCavity (R := Fin 2) hκ0
        r.toNNReal (by rwa [hr_coe]) hu0 hu1 hD1 hf₂m hf₂b
    have hφ₂_der : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt φ₂ d t ∧
        |d| ≤ K / Real.sqrt ((N : ℝ) + 1) := by
      intro t ht
      obtain ⟨d, hd, hbd⟩ := hprop_mul N M' κ h t q ρ u hκ hh ht.1 ht.2 hq0 hqρ hρQ hM'_le huc
        hu0 hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD (by simpa only [Nat.cast_add, Nat.cast_one] using hrR)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hrr_diff)
      refine ⟨d, by simpa only [Nat.cast_add, Nat.cast_one] using hd, ?_⟩
      have hbd' : |d| ≤ K_mul * (E_c / Real.sqrt ((N : ℝ) + 1)) := by
        refine (by simpa only [Nat.cast_add, Nat.cast_one] using hbd).trans ?_
        exact mul_le_mul_of_nonneg_left (hErr_bd t ht) hK_mul.le
      refine hbd'.trans ?_
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      have hle : K_mul * E_c ≤ max K_sq K_mul * E_c :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hEc0
      dsimp only [K]; linarith
    have hmv := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hφ₂_cont hφ₂_der
      (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    simp only [sub_zero, abs_one, mul_one] at hmv
    -- Helper: `∫ σ : Fin 2 → ℝ^(N+1), (σ 0)_N * (σ 1)_N d(μ^2) = (∫ x, x_N dμ)²`
    have hpi_sq_last : ∀ (μ : Measure (ℝ^(N + 1))), IsProbabilityMeasure μ →
        ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
          ∂(Measure.pi fun _ : Fin 2 => μ) = (∫ x : ℝ^(N + 1), x (Fin.last N) ∂μ) ^ 2 := by
      intro μ hμ
      letI := hμ
      have h1 := integral_fintype_prod_eq_pow (ι := Fin 2) (μ := μ)
        (fun x : ℝ^(N + 1) => x (Fin.last N))
      simpa only [Fin.prod_univ_two, Fintype.card_fin] using h1
    have hφ₂_1 : φ₂ 1 = ∫ d, (∫ σ, σ (Fin.last N) ∂(G d)) ^ 2 ∂P := by
      dsimp only [φ₂]
      have hpt : ∀ d : Dis[N, M' + 1],
          ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
            ∂(Measure.pi fun _ : Fin 2 => G_full 1 d) = (∫ σ, σ (Fin.last N) ∂(G d.2)) ^ 2 := by
        intro d
        rw [hG1 d]
        exact hpi_sq_last (G d.2) (isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 _ _)
      simp_rw [hpt]
      exact integral_prod_fun_snd_of_isProbabilityMeasure (gaussianReal 0 r.toNNReal) P
        (fun d => (∫ x, x (Fin.last N) ∂(G d)) ^ 2)
    have hφ₂_0 : φ₂ 0 = ∫ y, ∫ d, (∫ σ, σ (Fin.last N)
        ∂(volume.tilted fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ)) ^ 2
        ∂P ∂(gaussianReal 0 r.toNNReal) := by
      dsimp only [φ₂, P_full]
      have hpt : ∀ d : Dis[N, M' + 1],
          ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
            ∂(Measure.pi fun _ : Fin 2 => G_full 0 d) =
          (∫ x : ℝ^(N + 1), x (Fin.last N) ∂(G_full 0 d)) ^ 2 := fun d =>
        hpi_sq_last (G_full 0 d) (hprob 0 ⟨le_rfl, zero_le_one⟩ d)
      simp_rw [hpt]
      have hA0 := integrable_integral_pi_shcherbinaTirozziCavity (R := Fin 2)
        (N := N) (M := M' + 1) hκ0 r.toNNReal (by rwa [hr_coe]) (t := 0)
        ⟨le_rfl, zero_le_one⟩ hu0 hu1 hD1 (fun _ => hf₂b) (hf₂m.comp measurable_snd)
      have hi := integral_prod _ (hA0.congr (ae_of_all _ hpt))
      simpa only [G_full, P_full, hr_coe] using hi
    rw [hres_q, ← hφ₂_1, ← hφ₂_0]
    exact hmv

end Proposition3212

end SpinGlasses
