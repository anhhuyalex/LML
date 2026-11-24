/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.FreeEnergyPathODE

/-!
# A priori Grönwall bounds on the interpolating free energy fluctuations

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.5, proof of Theorem
2.5.3, Eq. (2.110) and the decoupled endpoint bound at `s = 0`.

Combining the centered-moment ODE `hasDerivAt_interpolating_centered_moment_pow` (Eq. (2.108))
with the Hölder remainder bounds `abs_interpolating_term_VII_le` and
`abs_interpolating_term_VIII_le` (Eq. (2.109)) and Young's inequality yields the differential
inequality `ψ'(s) ≤ K(k)((N + 1)^{-k/2} + ψ(s))` for even `k`, where `ψ(s) = 𝔼[V(s)^k]`. Forward
Grönwall comparison (`le_exp_mul_add_of_exists_hasDerivAt_Ioo`) and the uniform centered i.i.d.
moment bound `exists_abs_integral_pow_sum_pi_le` at the decoupled endpoint `s = 0` give
`𝔼[V(s)^{2p}] ≤ C (N + 1)^{-p}`, and Cauchy-Schwarz extends the estimate to
`𝔼[|V(s)|^k] ≤ C (N + 1)^{-k/2}` for all `k : ℕ`, uniformly in `s ∈ [0, 1]`.

## Main declarations

* `SpinGlasses.integral_interpolating_centered_abs_pow_le`: a priori bound
  `𝔼[|A(s) - RS(s)|^k] ≤ C (√(N + 1))⁻¹ ^ k` uniformly in `s ∈ [0, 1]`, with `K, C ≥ 0` chosen
  after `D` and `k` and before `N, M, s, u, q, r`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

/-- Young's inequality step for `VII` in Eq. (2.110):
`L⁻¹ * ψ ^ ((2 * p - 1) / (2 * p)) ≤ (√L)⁻¹ ^ (2 * p) + ψ` for `p ≥ 1`, `L ≥ 1`, `ψ ≥ 0`. -/
private lemma inv_mul_rpow_sub_one_div_two_mul_le
    {L ψ : ℝ} {p : ℕ} (hp : 1 ≤ p) (hL : 1 ≤ L) (hψ : 0 ≤ ψ) :
    L⁻¹ * ψ ^ (((2 * p - 1 : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ)) ≤
      ((Real.sqrt L)⁻¹) ^ (2 * p) + ψ := by
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.2 hp
  have hL_pos : 0 < L := zero_lt_one.trans_le hL
  let τ₁ : ℝ := ((2 * p : ℕ) : ℝ)
  let τ₂ : ℝ := ((2 * p : ℕ) : ℝ) / ((2 * p - 1 : ℕ) : ℝ)
  have hsub : ((2 * p - 1 : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * p), Nat.cast_one]
  have hconj : τ₁.HolderConjugate τ₂ := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · dsimp only [τ₁]; push_cast; linarith
    · dsimp only [τ₁, τ₂]; rw [inv_div, hsub]; field_simp; ring
  have hyoung := rpow_inv_mul_rpow_inv_le_add hconj
    (pow_nonneg (inv_nonneg.2 hL_pos.le) (2 * p)) hψ
  have hx : ((L⁻¹ ^ (2 * p)) ^ (1 / τ₁)) = L⁻¹ := by
    rw [← Real.rpow_natCast _ (2 * p), ← Real.rpow_mul (inv_nonneg.2 hL_pos.le)]
    dsimp only [τ₁]
    rw [mul_one_div_cancel (by positivity), Real.rpow_one]
  have hy : 1 / τ₂ = ((2 * p - 1 : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ) := by
    dsimp only [τ₂]; rw [one_div_div]
  rw [hx, hy] at hyoung
  have hpow_le : L⁻¹ ^ (2 * p) ≤ ((Real.sqrt L)⁻¹) ^ (2 * p) := by
    have hsqrt_eq : ((Real.sqrt L)⁻¹) ^ (2 * p) = L⁻¹ ^ p := by
      rw [pow_mul, inv_pow, Real.sq_sqrt hL_pos.le]
    rw [hsqrt_eq]
    exact pow_le_pow_of_le_one (inv_nonneg.2 hL_pos.le) (inv_le_one_of_one_le₀ hL) (by omega)
  linarith

/-- Young's inequality step for `VIII` and `IX` in Eq. (2.110):
`L⁻¹ * ψ ^ ((2 * p - 2) / (2 * p)) ≤ (√L)⁻¹ ^ (2 * p) + ψ` for `p ≥ 1`, `L ≥ 1`, `ψ ≥ 0`. -/
private lemma inv_mul_rpow_sub_two_div_two_mul_le
    {L ψ : ℝ} {p : ℕ} (hp : 1 ≤ p) (hL : 1 ≤ L) (hψ : 0 ≤ ψ) :
    L⁻¹ * ψ ^ (((2 * p - 2 : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ)) ≤
      ((Real.sqrt L)⁻¹) ^ (2 * p) + ψ := by
  have hL_pos : 0 < L := zero_lt_one.trans_le hL
  have hsqrt_eq : ((Real.sqrt L)⁻¹) ^ (2 * p) = L⁻¹ ^ p := by
    rw [pow_mul, inv_pow, Real.sq_sqrt hL_pos.le]
  rcases eq_or_lt_of_le hp with rfl | hp2
  · simp only [Nat.sub_self, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
    rw [hsqrt_eq, pow_one]
    exact le_add_of_nonneg_right hψ
  · let τ₁ : ℝ := (p : ℝ)
    let τ₂ : ℝ := (p : ℝ) / ((p - 1 : ℕ) : ℝ)
    have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp, Nat.cast_one]
    have hconj : τ₁.HolderConjugate τ₂ := by
      rw [Real.holderConjugate_iff]
      refine ⟨by dsimp only [τ₁]; exact_mod_cast hp2, ?_⟩
      dsimp only [τ₁, τ₂]
      rw [inv_div, hsub]
      have hp_ne : (p : ℝ) ≠ 0 := by positivity
      field_simp; ring
    have hyoung := rpow_inv_mul_rpow_inv_le_add hconj
      (pow_nonneg (inv_nonneg.2 hL_pos.le) p) hψ
    have hx : ((L⁻¹ ^ p) ^ (1 / τ₁)) = L⁻¹ := by
      rw [← Real.rpow_natCast _ p, ← Real.rpow_mul (inv_nonneg.2 hL_pos.le)]
      dsimp only [τ₁]
      rw [mul_one_div_cancel (by positivity), Real.rpow_one]
    have hy : 1 / τ₂ = ((2 * p - 2 : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ) := by
      dsimp only [τ₂]
      rw [one_div_div, show 2 * p - 2 = 2 * (p - 1) by omega]
      push_cast; field_simp
    rw [hx, hy, ← hsqrt_eq] at hyoung
    exact hyoung

/-- Continuity of `s ↦ 𝔼[(A(s) - RS(s))^m]` on `[0, 1]`. -/
lemma continuousOn_interpolating_centered_moment_pow
    {N M : ℕ} {u : ℝ → ℝ} (hu : Continuous u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q r : ℝ) (m : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (s : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A (s : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s s ω x) ∂μ_s)
    let RS (s : ℝ) : ℝ :=
      perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
    ContinuousOn (fun s => ∫ ω, (A s ω - RS s) ^ m ∂P) (Icc (0 : ℝ) 1) := by
  intro P_g P_z P_z' P μ_s E_s A RS
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let M_RS : ℝ := |perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q| +
    (1 / 2) * |r| * |1 - q|
  have hRS_bd {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : |RS s| ≤ M_RS := by
    dsimp only [RS, M_RS]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (sub_nonneg.2 hs.2), abs_of_pos zero_lt_two]
    have h1s : 1 - s ≤ 1 := by linarith [hs.1]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg r)) (abs_nonneg _)
  let dom_base (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ *
      (((N : ℝ) + 1) * Real.log 2 + M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) + M_RS
  have hdom_int : Integrable (fun ω => dom_base ω ^ m) P := by
    have hsum_z' : MemLp
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) ((max m 1 : ℕ) : ℝ≥0) P :=
      memLp_finsetSum Finset.univ fun i _ => by
        have h1 : MemLp (fun z' : Fin (N + 1) → ℝ => |z' i|) ((max m 1 : ℕ) : ℝ≥0) P_z' :=
          (IsGaussian.memLp_id (gaussianReal 0 1) ((max m 1 : ℕ) : ℝ≥0)
            ENNReal.coe_ne_top).norm.comp_measurePreserving
            (measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) i)
        exact (h1.comp_measurePreserving
          (measurePreserving_snd (μ := P_g.prod P_z) (ν := P_z'))).mul_const (Real.sqrt r)
    have hdom_mem : MemLp dom_base ((max m 1 : ℕ) : ℝ≥0) P :=
      (((memLp_const (((N : ℝ) + 1) * Real.log 2 + M * B)).add hsum_z').const_mul _).add
        (memLp_const M_RS)
    rcases m with _ | m
    · simp
    · have hm : max (m + 1) 1 = m + 1 := Nat.max_eq_left (Nat.succ_pos m)
      rw [hm] at hdom_mem
      have hY' : MemLp dom_base (m + 1 : ℕ) P := by simpa using hdom_mem
      have habs := hY'.integrable_norm_pow (Nat.succ_ne_zero m)
      exact habs.mono' (hY'.aestronglyMeasurable.pow (m + 1)) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow])
  have hVm {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
      AEStronglyMeasurable (fun ω => (A s ω - RS s) ^ m) P := by
    obtain ⟨hm_log, -⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
      hu.measurable hB q r hs.1
    exact (((hm_log.const_mul _).sub_const (RS s)).pow_const m).aestronglyMeasurable
  have hVb {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      ‖(A s ω - RS s) ^ m‖ ≤ dom_base ω ^ m := by
    obtain ⟨-, hbd_log⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
      hu.measurable hB q r hs.1
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ m
    dsimp only [A, dom_base]
    refine (abs_sub _ _).trans (add_le_add ?_ (hRS_bd hs))
    rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (N : ℝ) + 1))]
    exact mul_le_mul_of_nonneg_left (hbd_log ω) (by positivity)
  have hV_cont (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Continuous fun s => (A s ω - RS s) ^ m := by
    let E_eff (s : ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
      (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
        ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1)
    have hA_eq (s : ℝ) : A s ω = ((N : ℝ) + 1)⁻¹ * Real.log (∑ τ, Real.exp (E_eff s τ)) := by
      dsimp only [A, E_eff]
      rw [integral_sum_exp_interpolating_eq hu.measurable hB_le s q r ω]
    have hg_cont (τ : Fin (N + 1) → ℤˣ) (k : Fin M) :
        Continuous fun s : ℝ => ∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1 :=
      continuous_of_dominated (bound := fun _ => Real.exp B)
        (fun _ =>
          (Real.continuous_exp.comp (hu.comp (by fun_prop))).measurable.aestronglyMeasurable)
        (fun _ => ae_of_all _ fun _ => by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.2 (hB_le _))
        (integrable_const _)
        (ae_of_all _ fun _ => Real.continuous_exp.comp (hu.comp (by fun_prop)))
    have hg_pos (s : ℝ) (τ : Fin (N + 1) → ℤˣ) (k : Fin M) :
        0 < ∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1 :=
      integral_exp_pos_of_ae_le (hu.measurable.comp (by fun_prop)).aemeasurable
        (ae_of_all _ fun _ => hB_le _)
    have hE_cont (τ : Fin (N + 1) → ℤˣ) : Continuous fun s => E_eff s τ := by
      have h1 : Continuous fun s : ℝ =>
          ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r := by
        fun_prop
      have h2_each (k : Fin M) : Continuous fun s : ℝ =>
          Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
            ∂gaussianReal 0 1) :=
        (hg_cont τ k).log fun s => (hg_pos s τ k).ne'
      have h2 : Continuous fun s : ℝ =>
          ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
            ∂gaussianReal 0 1) := by
        fun_prop
      exact h1.add h2
    have hsum_cont : Continuous fun s : ℝ => ∑ τ, Real.exp (E_eff s τ) := by fun_prop
    have hA_cont : Continuous fun s => A s ω := by
      rw [funext hA_eq]
      exact continuous_const.mul (hsum_cont.log fun _ =>
        (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne')
    have hRS_cont : Continuous RS := by dsimp only [RS]; fun_prop
    exact (hA_cont.sub hRS_cont).pow m
  exact continuousOn_of_dominated (fun _ hs => hVm hs) (fun _ hs => ae_of_all _ (hVb hs))
    hdom_int (ae_of_all _ fun ω => (hV_cont ω).continuousOn)

private lemma integrable_mul_abs_add_one_pow_gaussianReal (D : ℝ) (j : ℕ) :
    Integrable (fun z : ℝ => (|D| * (|z| + 1)) ^ j) (gaussianReal 0 1) := by
  have heq : (fun z : ℝ => (|D| * (|z| + 1)) ^ j) =
      fun z => |D| ^ j * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * |z ^ l| := by
    funext z
    rw [mul_pow, add_pow]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [one_pow, mul_one, abs_pow, mul_comm]
  rw [heq]
  exact (integrable_finsetSum (Finset.range (j + 1)) fun l _ =>
    (integrable_pow_gaussianReal 0 1 l).abs.const_mul (j.choose l : ℝ)).const_mul (|D| ^ j)

/-- Decoupled endpoint `s = 0` bound for even moments `2 * p`: since `A_0 - RS_0` splits into the
sum of `N + 1` centered i.i.d. spin terms `log cosh(z'_i √r) - 𝔼 log cosh` and `M` centered i.i.d.
constraint terms `log 𝔼_ξ exp u(θ_j) - 𝔼 log 𝔼_ξ exp u(θ)`, with `r ≤ |D|²` and `M ≤ N + 1`,
`𝔼[(A_0 - RS_0)^{2p}] ≤ C (√(N + 1))⁻¹ ^ (2p)`. (Corrects the misprint `N^{k/2}` in the book to
`(N + 1)^{-k/2}`.) -/
private lemma integral_interpolating_zero_even_pow_le (D : ℝ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ} (_hu : Measurable u) (_hB : ∀ x, |u x| ≤ |D|)
        (_hMN : (M : ℝ) ≤ (N : ℝ) + 1) {q r : ℝ} (_hr_le : r ≤ |D| ^ 2),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let E_0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt 0 *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - 0) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 0) * ω.2 i * Real.sqrt r
        let A_0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_0 ω x) ∂μ_s)
        let RS_0 : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - 0) / 2) * r * (1 - q)
        ∫ ω, (A_0 ω - RS_0) ^ (2 * p) ∂P ≤
          C * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * p) := by
  rcases p with _ | p
  · refine ⟨1, zero_le_one, ?_⟩
    intro N M u _ _ _ q r _ P_g P_z P_z' P _ _ _ _
    have : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
    simp
  let γ : Measure ℝ := gaussianReal 0 1
  let B_X (j : ℕ) : ℝ := ∫ z : ℝ, (|D| * (|z| + 1)) ^ j ∂γ
  let B_Y (j : ℕ) : ℝ := (2 * |D|) ^ j
  have hBX0 (j : ℕ) : 0 ≤ B_X j := integral_nonneg fun _ => by positivity
  have hBY0 (j : ℕ) : 0 ≤ B_Y j := by positivity
  obtain ⟨C_X, hCX0, hCX⟩ := exists_abs_integral_pow_sum_pi_le B_X hBX0 (2 * (p + 1))
  obtain ⟨C_Y, hCY0, hCY⟩ := exists_abs_integral_pow_sum_pi_le B_Y hBY0 (2 * (p + 1))
  refine ⟨2 ^ (2 * (p + 1) - 1) * (C_X * 2 ^ (p + 1) + C_Y * 2 ^ (p + 1)), by positivity, ?_⟩
  intro N M u hu hB hMN q r hr_le P_g P_z P_z' P μ_s E_0 A_0 RS_0
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hB_le : ∀ x, u x ≤ |D| := fun x => le_of_abs_le (hB x)
  have hsr_le : Real.sqrt r ≤ |D| :=
    (Real.sqrt_le_sqrt hr_le).trans_eq (Real.sqrt_sq (abs_nonneg D))
  let c_X : ℝ := ∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ
  let f_X (z : ℝ) : ℝ := Real.log (Real.cosh (z * Real.sqrt r)) - c_X
  let ψ_u (z : ℝ) : ℝ :=
    Real.log (∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ)
  let c_Y : ℝ := ∫ z : ℝ, ψ_u z ∂γ
  let f_Y (z : ℝ) : ℝ := ψ_u z - c_Y
  have hpt_V (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      A_0 ω - RS_0 =
        ((N : ℝ) + 1)⁻¹ * (∑ i : Fin (N + 1), f_X (ω.2 i)) +
          ((N : ℝ) + 1)⁻¹ * (∑ j : Fin M, f_Y (ω.1.2 j)) := by
    have hlogZ : Real.log (∫ x, Real.exp (E_0 ω x) ∂μ_s) =
        (((N : ℝ) + 1) * Real.log 2 +
            ∑ i : Fin (N + 1), Real.log (Real.cosh (ω.2 i * Real.sqrt r))) +
          ∑ j : Fin M, ψ_u (ω.1.2 j) := by
      rw [integral_sum_exp_interpolating_eq hu hB_le 0 q r ω]
      have hsimp (τ : Fin (N + 1) → ℤˣ) :
          Real.exp ((∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - 0) * ω.2 i * Real.sqrt r) +
            ∑ j : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt 0 *
                ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
              Real.sqrt (1 - 0) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ))) ∂γ)) =
          Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * (ω.2 i * Real.sqrt r)) *
            Real.exp (∑ j : Fin M, ψ_u (ω.1.2 j)) := by
        rw [← Real.exp_add]
        refine congrArg Real.exp (congrArg₂ (· + ·)
          (Finset.sum_congr rfl fun _ _ => by rw [sub_zero, Real.sqrt_one]; ring)
          (Finset.sum_congr rfl fun _ _ => ?_))
        dsimp only [ψ_u, γ]
        exact congrArg Real.log (integral_congr_ae (ae_of_all _ fun ξ => by
          dsimp only; rw [Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul]))
      rw [Finset.sum_congr rfl fun τ _ => hsimp τ, ← Finset.sum_mul]
      have hsum_pos : 0 < ∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * (ω.2 i * Real.sqrt r)) :=
        Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
      rw [Real.log_mul hsum_pos.ne' (Real.exp_pos _).ne', Real.log_exp,
        log_decoupled_partition_function_eq (fun i : Fin (N + 1) => ω.2 i * Real.sqrt r),
        Fintype.card_fin]
      push_cast; rfl
    have hRS0 : RS_0 = Real.log 2 + c_X + ((M : ℝ) / ((N : ℝ) + 1)) * c_Y := by
      dsimp only [RS_0, c_X, c_Y, ψ_u, γ]
      rw [perceptronRSFunctional_eq_log_two_add]
      ring
    dsimp only [A_0, f_X, f_Y]
    rw [hlogZ, hRS0, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    generalize (∑ i : Fin (N + 1), Real.log (Real.cosh (ω.2 i * Real.sqrt r))) = SX_sum
    generalize (∑ j : Fin M, ψ_u (ω.1.2 j)) = SY_sum
    field_simp; ring
  have hlc_m : Measurable fun z : ℝ => Real.log (Real.cosh (z * Real.sqrt r)) :=
    (Real.continuous_cosh.comp (by fun_prop)).log (fun _ => (Real.cosh_pos _).ne') |>.measurable
  have hlc_bd (z : ℝ) : |Real.log (Real.cosh (z * Real.sqrt r))| ≤ |D| * |z| := by
    rw [abs_of_nonneg (Real.log_cosh_nonneg _)]
    refine (Real.log_cosh_le_abs _).trans ?_
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right hsr_le (abs_nonneg z)
  have hz1_int : Integrable (fun z : ℝ => |z|) γ :=
    by simpa [pow_one] using (integrable_pow_gaussianReal 0 1 1).abs
  have hcX_bd : |c_X| ≤ |D| := by
    have hz_int : Integrable (fun z : ℝ => |D| * |z|) γ := hz1_int.const_mul |D|
    have h1 : |c_X| ≤ ∫ z : ℝ, |D| * |z| ∂γ := by
      refine abs_integral_le_integral_abs.trans ?_
      exact integral_mono (f := fun z => |Real.log (Real.cosh (z * Real.sqrt r))|)
        (g := fun z => |D| * |z|)
        (hz_int.mono' hlc_m.norm.aestronglyMeasurable
          (ae_of_all _ fun z => by rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hlc_bd z))
        hz_int hlc_bd
    have h_abs_z_le : ∫ z : ℝ, |z| ∂γ ≤ 1 := by
      have hsq : (∫ z : ℝ, |z| ∂γ) ^ 2 ≤ ∫ z : ℝ, |z| ^ 2 ∂γ :=
        MeasureTheory.sq_integral_le_integral_sq continuous_abs.measurable
          (by simpa only [sq_abs] using integrable_pow_gaussianReal 0 1 2)
      have hvar : ∫ z : ℝ, |z| ^ 2 ∂γ = 1 := by
        simp_rw [sq_abs]
        simpa using integral_pow_add_two_gaussianReal 0
      rw [hvar] at hsq
      nlinarith [integral_nonneg (μ := γ) fun z => abs_nonneg z]
    rw [integral_const_mul] at h1
    nlinarith [abs_nonneg D]
  have hfX_bd (z : ℝ) : |f_X z| ≤ |D| * (|z| + 1) := by
    dsimp only [f_X]
    calc |Real.log (Real.cosh (z * Real.sqrt r)) - c_X|
        ≤ |Real.log (Real.cosh (z * Real.sqrt r))| + |c_X| := abs_sub _ _
      _ ≤ |D| * |z| + |D| := add_le_add (hlc_bd z) hcX_bd
      _ = |D| * (|z| + 1) := by ring
  have hBX_int (j : ℕ) : Integrable (fun z : ℝ => (|D| * (|z| + 1)) ^ j) γ :=
    integrable_mul_abs_add_one_pow_gaussianReal D j
  have hfX_int (j : ℕ) : Integrable (fun z : ℝ => f_X z ^ j) γ :=
    (hBX_int j).mono' ((hlc_m.sub_const c_X).pow_const j).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hfX_bd z) j)
  have hfX_0 : ∫ z, f_X z ∂γ = 0 := by
    have h1 : Integrable (fun z => Real.log (Real.cosh (z * Real.sqrt r))) γ :=
      (hz1_int.const_mul |D|).mono' hlc_m.aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hlc_bd z)
    dsimp only [f_X]
    rw [integral_sub (f := fun z => Real.log (Real.cosh (z * Real.sqrt r))) (g := fun _ => c_X)
      h1 (integrable_const c_X), integral_const, probReal_univ, one_smul, sub_self]
  have hfX_mom (j : ℕ) : |∫ z, f_X z ^ j ∂γ| ≤ B_X j :=
    abs_integral_le_integral_abs.trans (integral_mono (f := fun z => |f_X z ^ j|)
      (g := fun z => (|D| * (|z| + 1)) ^ j) (hfX_int j).abs (hBX_int j) fun z => by
        dsimp only; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfX_bd z) j)
  have hψu_m : Measurable ψ_u := by
    refine Real.measurable_log.comp ?_
    have hj : Measurable fun p : ℝ × ℝ =>
        Real.exp (u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2)) :=
      Real.measurable_exp.comp (hu.comp (by fun_prop))
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
  have hψu_bd (z : ℝ) : |ψ_u z| ≤ |D| :=
    abs_log_integral_exp_le_of_ae_abs_le (hu.comp (by fun_prop)).aemeasurable
      (ae_of_all _ fun _ => hB _)
  have hfY_bd (z : ℝ) : |f_Y z| ≤ 2 * |D| := by
    dsimp only [f_Y]
    have hcY_bd : |c_Y| ≤ |D| := abs_integral_le_of_forall_abs_le _ hψu_bd
    linarith [abs_sub (ψ_u z) c_Y, hψu_bd z]
  have hfY_int (j : ℕ) : Integrable (fun z : ℝ => f_Y z ^ j) γ :=
    Integrable.of_bound ((hψu_m.sub_const c_Y).pow_const j).aestronglyMeasurable
      ((2 * |D|) ^ j) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hfY_bd z) j)
  have hfY_0 : ∫ z, f_Y z ∂γ = 0 := by
    have h1 : Integrable ψ_u γ := Integrable.of_bound hψu_m.aestronglyMeasurable |D|
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hψu_bd z)
    dsimp only [f_Y]
    rw [integral_sub h1 (integrable_const c_Y), integral_const, probReal_univ, one_smul, sub_self]
  have hfY_mom (j : ℕ) : |∫ z, f_Y z ^ j ∂γ| ≤ B_Y j :=
    abs_integral_le_of_forall_abs_le _ fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfY_bd z) j
  let S_X (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), f_X (ω.2 i)
  let S_Y (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, f_Y (ω.1.2 j)
  have hSX_int : Integrable (fun ω => S_X ω ^ (2 * (p + 1))) P := by
    have hpi := (integrable_pow_sum_pi hfX_int (N + 1) (2 * (p + 1))).const_mul
      ((((N : ℝ) + 1)⁻¹) ^ (2 * (p + 1)))
    exact (hpi.comp_snd (P_g.prod P_z)).congr
      (ae_of_all _ fun ω => by dsimp only [S_X]; rw [mul_pow])
  have hSY_int : Integrable (fun ω => S_Y ω ^ (2 * (p + 1))) P := by
    have hpi := (integrable_pow_sum_pi hfY_int M (2 * (p + 1))).const_mul
      ((((N : ℝ) + 1)⁻¹) ^ (2 * (p + 1)))
    exact ((hpi.comp_snd P_g).comp_fst P_z').congr
      (ae_of_all _ fun ω => by dsimp only [S_Y]; rw [mul_pow])
  have hSX_m : Measurable S_X :=
    (Finset.measurable_sum _ fun i _ =>
      (hlc_m.sub_const c_X).comp ((measurable_pi_apply i).comp measurable_snd)).const_mul _
  have hSY_m : Measurable S_Y :=
    (Finset.measurable_sum _ fun j _ =>
      (hψu_m.sub_const c_Y).comp
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst))).const_mul _
  have hsum_le :
      ∫ ω, (A_0 ω - RS_0) ^ (2 * (p + 1)) ∂P ≤
        2 ^ (2 * (p + 1) - 1) *
          (∫ ω, S_X ω ^ (2 * (p + 1)) ∂P + ∫ ω, S_Y ω ^ (2 * (p + 1)) ∂P) := by
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (A_0 ω - RS_0) ^ (2 * (p + 1)) ≤
          2 ^ (2 * (p + 1) - 1) * (S_X ω ^ (2 * (p + 1)) + S_Y ω ^ (2 * (p + 1))) := by
      rw [hpt_V ω]; exact add_pow_two_mul_le (Nat.succ_pos p) (S_X ω) (S_Y ω)
    have hVm : Measurable fun ω => (A_0 ω - RS_0) ^ (2 * (p + 1)) := by
      have heq_V : (fun ω => (A_0 ω - RS_0) ^ (2 * (p + 1))) =
          fun ω => (S_X ω + S_Y ω) ^ (2 * (p + 1)) := funext fun ω => by rw [hpt_V ω]
      rw [heq_V]; exact (hSX_m.add hSY_m).pow_const _
    refine (integral_mono
      (g := fun ω => 2 ^ (2 * (p + 1) - 1) * (S_X ω ^ (2 * (p + 1)) + S_Y ω ^ (2 * (p + 1))))
      (((hSX_int.add hSY_int).const_mul _).mono' hVm.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (Even.pow_nonneg ⟨p + 1, by ring⟩ _)]
          exact hpt ω))
      ((hSX_int.add hSY_int).const_mul _) hpt).trans_eq ?_
    rw [integral_const_mul,
      integral_add (f := fun ω => S_X ω ^ (2 * (p + 1))) (g := fun ω => S_Y ω ^ (2 * (p + 1)))
        hSX_int hSY_int]
  have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hε_eq : ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1)) = (((N : ℝ) + 1)⁻¹) ^ (p + 1) := by
    rw [pow_mul, inv_pow, Real.sq_sqrt hL_pos.le]
  have hIX : ∫ ω, S_X ω ^ (2 * (p + 1)) ∂P ≤
      C_X * 2 ^ (p + 1) * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1)) := by
    have hsnd := integral_prod_fun_snd_of_isProbabilityMeasure (μ := P_g.prod P_z) (ν := P_z')
      (fun z' : Fin (N + 1) → ℝ => (((N : ℝ) + 1)⁻¹ * ∑ i, f_X (z' i)) ^ (2 * (p + 1)))
    dsimp only [P, S_X]
    rw [hsnd]
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hb_raw := (le_abs_self _).trans (hCX γ hfX_int hfX_0 hfX_mom (N + 1))
    have hsq_pow : Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) ^ (2 * (p + 1)) ≤
        2 ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1) := by
      rw [pow_mul, Real.sq_sqrt (by positivity), ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      push_cast; linarith
    calc (((N : ℝ) + 1)⁻¹) ^ (2 * (p + 1)) *
          ∫ y : Fin (N + 1) → ℝ, (∑ i, f_X (y i)) ^ (2 * (p + 1)) ∂P_z'
        ≤ (((N : ℝ) + 1)⁻¹) ^ (2 * (p + 1)) *
            (C_X * (2 ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1))) :=
          mul_le_mul_of_nonneg_left
            (hb_raw.trans (mul_le_mul_of_nonneg_left hsq_pow hCX0)) (by positivity)
      _ = C_X * 2 ^ (p + 1) * (((N : ℝ) + 1)⁻¹) ^ (p + 1) := by
          rw [show 2 * (p + 1) = (p + 1) + (p + 1) by ring, pow_add]
          have h1 : (((N : ℝ) + 1)⁻¹) ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1) = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hL_pos.ne', one_pow]
          calc _ = C_X * 2 ^ (p + 1) * (((N : ℝ) + 1)⁻¹) ^ (p + 1) *
                ((((N : ℝ) + 1)⁻¹) ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1)) := by ring
            _ = _ := by rw [h1, mul_one]
      _ = C_X * 2 ^ (p + 1) * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1)) := by rw [hε_eq]
  have hIY : ∫ ω, S_Y ω ^ (2 * (p + 1)) ∂P ≤
      C_Y * 2 ^ (p + 1) * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1)) := by
    have hfst := integral_prod_fun_fst_of_isProbabilityMeasure (μ := P_g.prod P_z) (ν := P_z')
      (fun gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ) =>
        (((N : ℝ) + 1)⁻¹ * ∑ j, f_Y (gz.2 j)) ^ (2 * (p + 1)))
    have hsnd := integral_prod_fun_snd_of_isProbabilityMeasure (μ := P_g) (ν := P_z)
      (fun z : Fin M → ℝ => (((N : ℝ) + 1)⁻¹ * ∑ j, f_Y (z j)) ^ (2 * (p + 1)))
    dsimp only [P, S_Y]
    rw [hfst, hsnd]
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hb_raw := (le_abs_self _).trans (hCY γ hfY_int hfY_0 hfY_mom M)
    have hsq_pow : Real.sqrt ((M : ℝ) + 1) ^ (2 * (p + 1)) ≤
        2 ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1) := by
      rw [pow_mul, Real.sq_sqrt (by positivity), ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    calc (((N : ℝ) + 1)⁻¹) ^ (2 * (p + 1)) *
          ∫ y : Fin M → ℝ, (∑ j, f_Y (y j)) ^ (2 * (p + 1)) ∂P_z
        ≤ (((N : ℝ) + 1)⁻¹) ^ (2 * (p + 1)) *
            (C_Y * (2 ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1))) :=
          mul_le_mul_of_nonneg_left
            (hb_raw.trans (mul_le_mul_of_nonneg_left hsq_pow hCY0)) (by positivity)
      _ = C_Y * 2 ^ (p + 1) * (((N : ℝ) + 1)⁻¹) ^ (p + 1) := by
          rw [show 2 * (p + 1) = (p + 1) + (p + 1) by ring, pow_add]
          have h1 : (((N : ℝ) + 1)⁻¹) ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1) = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hL_pos.ne', one_pow]
          calc _ = C_Y * 2 ^ (p + 1) * (((N : ℝ) + 1)⁻¹) ^ (p + 1) *
                ((((N : ℝ) + 1)⁻¹) ^ (p + 1) * ((N : ℝ) + 1) ^ (p + 1)) := by ring
            _ = _ := by rw [h1, mul_one]
      _ = C_Y * 2 ^ (p + 1) * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1)) := by rw [hε_eq]
  calc ∫ ω, (A_0 ω - RS_0) ^ (2 * (p + 1)) ∂P
      ≤ 2 ^ (2 * (p + 1) - 1) *
          (C_X * 2 ^ (p + 1) * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1)) +
            C_Y * 2 ^ (p + 1) * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1))) :=
        hsum_le.trans (mul_le_mul_of_nonneg_left (add_le_add hIX hIY) (by positivity))
    _ = 2 ^ (2 * (p + 1) - 1) * (C_X * 2 ^ (p + 1) + C_Y * 2 ^ (p + 1)) *
          ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * (p + 1)) := by ring

/-- Differential inequality Eq. (2.110) and forward Grönwall bound for even moments `k = 2 * p`. -/
private theorem integral_interpolating_centered_even_pow_le (D : ℝ) (p : ℕ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt s *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let RS : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
        ∫ ω, (A ω - RS) ^ (2 * p) ∂P ≤ C * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * p) := by
  rcases p with _ | p
  · refine ⟨1, 1, zero_le_one, zero_le_one, ?_⟩
    intro N M s _ u _ _ _ q r _ _ P_g P_z P_z' P _ _ _ _
    have : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
    simp
  let k : ℕ := 2 * (p + 1)
  have hk_even : Even k := ⟨p + 1, by dsimp only [k]; ring⟩
  obtain ⟨K_VII, C_VII, hK7_0, hC7_0, h_VII⟩ := abs_interpolating_term_VII_le D k
  obtain ⟨K_VIII, C_VIII, hK8_0, hC8_0, h_VIII⟩ := abs_interpolating_term_VIII_le D k
  obtain ⟨C_0, hC0_0, h_zero⟩ := integral_interpolating_zero_even_pow_le D (p + 1)
  let K : ℝ := max (max K_VII K_VIII) 1
  let K_ode : ℝ := C_VII + C_VIII
  let C : ℝ := Real.exp (K_ode + 1) * (C_0 + K_ode)
  refine ⟨K, C, by positivity, by positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr P_g P_z P_z' P μ_s E_s_s A_s RS_s
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα1 : α ≤ 1 := by
    have h1 : α * 1 ≤ α * K := mul_le_mul_of_nonneg_left (le_max_right _ 1) hα0
    linarith [hα]
  have hMN : (M : ℝ) ≤ (N : ℝ) + 1 :=
    (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)).1 hα1
  have hα_VII : α * K_VII ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_left _ _)) hα0).trans hα
  have hα_VIII : α * K_VIII ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_left _ _)) hα0).trans hα
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  have hrhat_mem : perceptronRhat u q ∈ Icc (0 : ℝ) (|D| ^ 2) :=
    rhat_mem_Icc hu.abs_deriv_le_abs q
      (fun z => integrable_exp_cavityPath_new hu.measurable hu.le_abs q z)
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hα0 hrhat_mem.1
  have hr_le : r ≤ |D| ^ 2 := by
    rw [hr]
    calc α * perceptronRhat u q ≤ 1 * |D| ^ 2 :=
          mul_le_mul hα1 hrhat_mem.2 hrhat_mem.1 zero_le_one
      _ = |D| ^ 2 := one_mul _
  let E_path (t : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (∑ j : Fin M, u (Real.sqrt t *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - t) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
    ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 i * Real.sqrt r
  let A_path (t : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_path t ω x) ∂μ_s)
  let RS_path (t : ℝ) : ℝ :=
    perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - t) / 2) * r * (1 - q)
  let ψ (t : ℝ) : ℝ := ∫ ω, (A_path t ω - RS_path t) ^ k ∂P
  have hψ_cont : ContinuousOn ψ (Icc 0 1) :=
    continuousOn_interpolating_centered_moment_pow (N := N) (M := M)
      hu.differentiable.continuous hu.abs_le q r k
  have hψ_nonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t := fun t _ =>
    integral_nonneg fun _ => hk_even.pow_nonneg _
  let L : ℝ := (N : ℝ) + 1
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hL_pos : 0 < L := zero_lt_one.trans_le hL1
  let ε_N : ℝ := ((Real.sqrt L)⁻¹) ^ k
  have hode_step : ∀ t ∈ Ioo (0 : ℝ) 1,
      ∃ d, HasDerivAt ψ d t ∧ d ≤ K_ode * ψ t + K_ode * ε_N := by
    intro t ht
    have ht_cc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hd_ode := hasDerivAt_interpolating_centered_moment_pow (N := N) (M := M)
      hu hq_mem hr0 ht k
    dsimp only at hd_ode
    refine ⟨_, hd_ode, ?_⟩
    have hb7 := (le_abs_self _).trans (h_VII N M ht_cc hd hb hα_VII hq hr)
    have hb8 := (le_abs_self _).trans (h_VIII N M ht_cc hd hb hα_VIII hq hr)
    dsimp only at hb7 hb8
    have habs_eq : (∫ ω, |A_path t ω - RS_path t| ^ k ∂P) = ψ t :=
      integral_congr_ae (ae_of_all _ fun ω => by dsimp only; rw [hk_even.pow_abs])
    rw [habs_eq] at hb7 hb8
    have hIX_nonpos :
        -(r * q / (2 * ((N : ℝ) + 1))) * (k : ℝ) * ((k : ℝ) - 1) *
          ∫ ω, (A_path t ω - RS_path t) ^ (k - 2) ∂P ≤ 0 := by
      have hk_ge1 : (1 : ℝ) ≤ k := by dsimp only [k]; push_cast; linarith
      have hk_sub : 0 ≤ (k : ℝ) - 1 := sub_nonneg.2 hk_ge1
      have hInt0 : 0 ≤ ∫ ω, (A_path t ω - RS_path t) ^ (k - 2) ∂P := by
        have hk2_eq : k - 2 = 2 * p := by dsimp only [k]; omega
        rw [hk2_eq]
        exact integral_nonneg fun _ => Even.pow_nonneg ⟨p, by ring⟩ _
      have hpos_prod : 0 ≤ (r * q / (2 * ((N : ℝ) + 1))) * (k : ℝ) * ((k : ℝ) - 1) *
          ∫ ω, (A_path t ω - RS_path t) ^ (k - 2) ∂P := by
        have hq0 := hq_mem.1
        positivity
      linarith
    have hy7 : C_VII / L * ψ t ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) ≤
        C_VII * (ε_N + ψ t) := by
      have h1 := inv_mul_rpow_sub_one_div_two_mul_le (Nat.succ_pos p) hL1 (hψ_nonneg t ht_cc)
      calc C_VII / L * ψ t ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ))
          = C_VII * (L⁻¹ * ψ t ^ (((2 * (p + 1) - 1 : ℕ) : ℝ) / ((2 * (p + 1) : ℕ) : ℝ))) := by
            dsimp only [k]; ring
        _ ≤ C_VII * (ε_N + ψ t) := mul_le_mul_of_nonneg_left h1 hC7_0
    have hy8 : C_VIII / L ^ 2 * ψ t ^ (((k - 2 : ℕ) : ℝ) / (k : ℝ)) ≤
        C_VIII * (ε_N + ψ t) := by
      have h1 := inv_mul_rpow_sub_two_div_two_mul_le (Nat.succ_pos p) hL1 (hψ_nonneg t ht_cc)
      have hL2 : L⁻¹ ^ 2 ≤ L⁻¹ := by
        rw [sq]
        exact mul_le_of_le_one_left (inv_nonneg.2 hL_pos.le) (inv_le_one_of_one_le₀ hL1)
      have hrp0 : 0 ≤ ψ t ^ (((k - 2 : ℕ) : ℝ) / (k : ℝ)) :=
        Real.rpow_nonneg (hψ_nonneg t ht_cc) _
      calc C_VIII / L ^ 2 * ψ t ^ (((k - 2 : ℕ) : ℝ) / (k : ℝ))
          = C_VIII * (L⁻¹ ^ 2 * ψ t ^ (((k - 2 : ℕ) : ℝ) / (k : ℝ))) := by
            rw [div_eq_mul_inv, inv_pow]; ring
        _ ≤ C_VIII * (L⁻¹ * ψ t ^ (((2 * (p + 1) - 2 : ℕ) : ℝ) / ((2 * (p + 1) : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL2 hrp0) hC8_0
        _ ≤ C_VIII * (ε_N + ψ t) := mul_le_mul_of_nonneg_left h1 hC8_0
    dsimp only [K_ode, L] at *
    linarith [hb7, hb8, hIX_nonpos, hy7, hy8]
  have hgron := le_exp_mul_add_of_exists_hasDerivAt_Ioo (by dsimp only [K_ode]; positivity)
    (by dsimp only [K_ode, ε_N]; positivity) hψ_cont hψ_nonneg hode_step hs
  have hψ0_le : ψ 0 ≤ C_0 * ε_N :=
    h_zero N M hu.measurable (fun x => (hu.abs_le x).trans (le_abs_self D)) hMN hr_le
  calc ψ s ≤ Real.exp (K_ode + 1) * (ψ 0 + K_ode * ε_N) := hgron
    _ ≤ Real.exp (K_ode + 1) * (C_0 * ε_N + K_ode * ε_N) :=
        mul_le_mul_of_nonneg_left (add_le_add hψ0_le le_rfl) (Real.exp_pos _).le
    _ = C * ε_N := by dsimp only [C]; ring

/-- **Talagrand Section 2.5, a priori fluctuation bound via Grönwall:**
Given `D` and `k`, there exist `K, C ≥ 0` (chosen before `N, M, s, u, q, r`) such that under (2.7),
`α K ≤ 1`, `(q, r)` solving (2.68), and `s ∈ [0, 1]`,
`𝔼[|A(s) - RS(s)|^k] ≤ C * (√(N + 1))⁻¹ ^ k`. -/
theorem integral_interpolating_centered_abs_pow_le (D : ℝ) (k : ℕ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt s *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let RS : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
        ∫ ω, |A ω - RS| ^ k ∂P ≤ C * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ k := by
  obtain ⟨K_2k, C_2k, hK0, hC0, h_even⟩ := integral_interpolating_centered_even_pow_le D k
  refine ⟨K_2k, Real.sqrt C_2k, hK0, Real.sqrt_nonneg _, ?_⟩
  intro N M s hs u hd hb hα q r hq hr P_g P_z P_z' P μ_s E_s A RS
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  obtain ⟨hm_log, hbd_log⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
    hu.measurable hu.abs_le q r hs.1
  have hVm : Measurable fun ω => |A ω - RS| ^ k :=
    (continuous_abs.measurable.comp
      ((hm_log.const_mul ((N : ℝ) + 1)⁻¹).sub_const RS)).pow_const k
  have hV2k_int : Integrable (fun ω => (|A ω - RS| ^ k) ^ 2) P := by
    let dom_A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ *
        (((N : ℝ) + 1) * Real.log 2 + M * D + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) + |RS|
    have hsum_z' : MemLp
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) ((max (2 * k) 1 : ℕ) : ℝ≥0) P :=
      memLp_finsetSum Finset.univ fun i _ =>
        ((IsGaussian.memLp_id (gaussianReal 0 1) ((max (2 * k) 1 : ℕ) : ℝ≥0)
          ENNReal.coe_ne_top).norm.comp_measurePreserving
          (measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) i)
          |>.comp_measurePreserving
          (measurePreserving_snd (μ := P_g.prod P_z) (ν := P_z'))).mul_const (Real.sqrt r)
    have hdom_mem : MemLp dom_A ((max (2 * k) 1 : ℕ) : ℝ≥0) P :=
      (((memLp_const (((N : ℝ) + 1) * Real.log 2 + M * D)).add hsum_z').const_mul _).add
        (memLp_const |RS|)
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp
    · have hm : max (2 * k) 1 = 2 * k := Nat.max_eq_left (by omega)
      rw [hm] at hdom_mem
      have hY' : MemLp dom_A (2 * k : ℕ) P := by simpa using hdom_mem
      have habs := hY'.integrable_norm_pow (by omega : 2 * k ≠ 0)
      refine habs.mono' (hVm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, ← pow_mul, mul_comm k 2]
      refine pow_le_pow_left₀ (abs_nonneg _) (?_) (2 * k)
      refine ((abs_sub _ _).trans (add_le_add ?_ le_rfl)).trans (le_abs_self _)
      dsimp only [A]
      rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (N : ℝ) + 1))]
      exact mul_le_mul_of_nonneg_left (hbd_log ω) (by positivity)
  have hsq_le : (∫ ω, |A ω - RS| ^ k ∂P) ^ 2 ≤ ∫ ω, (A ω - RS) ^ (2 * k) ∂P := by
    refine (MeasureTheory.sq_integral_le_integral_sq hVm hV2k_int).trans_eq ?_
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    dsimp only
    rw [← pow_mul, mul_comm k 2, Even.pow_abs ⟨k, by ring⟩]
  have hb_even := h_even N M hs hd hb hα hq hr
  dsimp only at hb_even
  let ε : ℝ := ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ k
  have hε0 : 0 ≤ ε := by dsimp only [ε]; positivity
  have hsq_rhs : C_2k * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (2 * k) = (Real.sqrt C_2k * ε) ^ 2 := by
    dsimp only [ε]
    rw [mul_pow, Real.sq_sqrt hC0, ← pow_mul, mul_comm k 2]
  have hI0 : 0 ≤ ∫ ω, |A ω - RS| ^ k ∂P := integral_nonneg fun _ => by positivity
  have hcomb : (∫ ω, |A ω - RS| ^ k ∂P) ^ 2 ≤ (Real.sqrt C_2k * ε) ^ 2 :=
    hsq_le.trans (hb_even.trans_eq hsq_rhs)
  nlinarith [sq_nonneg (∫ ω, |A ω - RS| ^ k ∂P - Real.sqrt C_2k * ε),
    mul_nonneg (Real.sqrt_nonneg C_2k) hε0]

end SpinGlasses
