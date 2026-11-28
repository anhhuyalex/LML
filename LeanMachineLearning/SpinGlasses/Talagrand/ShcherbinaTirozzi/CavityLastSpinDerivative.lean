/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExpMoment

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IntervalDerivative
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.AuxiliaryCavityGronwall
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityDerivative

/-!
# The Shcherbina--Tirozzi model: Proposition 3.2.10 (cavity derivative of last-spin moments)

This file formalizes **Talagrand, Proposition 3.2.10** (Eqs. (3.107)--(3.110)) in Section 3.2 of
*Spin Glasses: A Challenge for Mathematicians*, Vol. I:

For a system on `ℝ^(N+1)` with `M + 1` constraints (`M + 1 ≤ 10 (N + 1)`), along the cavity path
`ν_t` at the replica-symmetric parameters `r = Ψ(q, ρ)`, `r̄ = Ψ̄(q, ρ)` of Eq. (3.69) (with
`α = (M + 1) / (N + 1)`), and for `f(σ) = ε₁²` or `f(σ) = ε₁ ε₂`,
```
|ν_t'(f)| ≤ K * (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)
```
where `K` depends only on `κ₀, h₀, D, Q, R, R_diff` (uniformly in `N, M, t`).

The proof follows Talagrand's Eq. (3.108)--(3.110):
1. Each of the four types of terms in Proposition 3.2.1 is compared with its `v = 0` decoupled
   counterpart via the auxiliary cavity path `ν_{t,v}`:
   - `ν_{t,1}(B_1 f) - ν_{t,0}(B_0 f)` is bounded by `sup_{v ∈ (0,1)} |d/dv ν_{t,v}(B_v f)|`
     via `abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo`.
   - Lemma 3.2.8 bounds the `v`-derivative by a sum of `ν_{t,v}(|g| |R^t_{a,b} - m_{ab}|)`.
   - Writing `R^t_{a,b} = R_{a,b} - (1 - t) ε_a ε_b / (N + 1)`, Cauchy-Schwarz with Eq. (3.100)
     controls both the `|R_{a,b} - m_{ab}|` part (via `√(ν_{t,v}((R_{a,b} - m_{ab})²))`) and the
     `(N + 1)⁻¹ |ε_a ε_b|` remainder.
   - Lemma 3.2.9 (Eq. (3.106)) and Eq. (3.104) transfer `ν_{t,v}((R_{a,b} - m_{ab})²)` back to
     `ν_t((R_{a,b} - m_{ab})²) + K exp(-(N + 1))`.
2. Combining the four comparisons in Proposition 3.2.1 cancels the `v = 0` leading terms by
   symmetry of the `M + 1` constraints and Lemma 3.2.7 (Eqs. (3.92)--(3.94)), leaving only the
   error `K (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)`.

## Main declarations

* `SpinGlasses.exists_abs_shcherbinaTirozziAuxCavity_one_sub_zero_le`: general `ν_{t,1}(B_1 g) -
  ν_{t,0}(B_0 g)` comparison bound (Eqs. (3.108)--(3.110)) for any observable `g` of polynomial
  growth with bounded `L²` norm along `ν_{t,v}`.
* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziCavity_last_spin_abs_le`: Proposition 3.2.10
  (Eq. (3.107)) for `f = ε₁²` and `f = ε₁ ε₂`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- The disorder `((y, (g, g₀)), z)` of the auxiliary cavity system with `M + 1` constraints and
shared Gaussian `z`. -/
local notation "AuxDis[" N ", " M "]" =>
  (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ

/-- The law of `AuxDis` with `y ~ 𝒩(0, r)` and standard Gaussian `g, g₀, z`. -/
local notation "auxLaw[" N ", " M ", " r "]" =>
  Measure.prod
    (Measure.prod (gaussianReal 0 r)
      (Measure.prod
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    (gaussianReal 0 1)

/-- The cavity field `S_{k,t}` on `ℝ^(N+1)`. -/
local notation "cfield[" N ", " t ", " g ", " k ", " σ "]" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

section Helpers

/-- Under a probability measure `G` on `ℝ^(N+1) × ℝ` with `∫ exp(ε² / K) ≤ M`, the `2k`-th
moment of the last spin `ε = p.1 (Fin.last N)` satisfies
`∫ ε^(2k) ≤ k! * K^k * M`. -/
private lemma integral_last_spin_pow_two_mul_le_of_exp {N : ℕ} {G : Measure (ℝ^(N + 1) × ℝ)}
    {K : ℝ} (hK : 0 < K)
    (hexp : Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (p.1 (Fin.last N) ^ 2 / K)) G)
    (k : ℕ) :
    Integrable (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ (2 * k)) G ∧
      ∫ p, p.1 (Fin.last N) ^ (2 * k) ∂G ≤
        (k.factorial : ℝ) * K ^ k * ∫ p, Real.exp (p.1 (Fin.last N) ^ 2 / K) ∂G := by
  have hm : Measurable fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ (2 * k) :=
    (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
      measurable_fst).pow_const (2 * k)
  have hpt : ∀ p : ℝ^(N + 1) × ℝ,
      p.1 (Fin.last N) ^ (2 * k) ≤
        (k.factorial : ℝ) * K ^ k * Real.exp (p.1 (Fin.last N) ^ 2 / K) := by
    intro p
    have hts := Real.pow_div_factorial_le_exp (p.1 (Fin.last N) ^ 2 / K) (by positivity) k
    rw [div_pow, div_le_iff₀ (by positivity)] at hts
    have hpow : p.1 (Fin.last N) ^ (2 * k) = (p.1 (Fin.last N) ^ 2) ^ k := by rw [pow_mul]
    rw [hpow]
    have hKk : 0 < K ^ k := by positivity
    calc (p.1 (Fin.last N) ^ 2) ^ k
        = K ^ k * ((p.1 (Fin.last N) ^ 2) ^ k / K ^ k) := by field_simp
      _ ≤ K ^ k * (Real.exp (p.1 (Fin.last N) ^ 2 / K) * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hts hKk.le
      _ = (k.factorial : ℝ) * K ^ k * Real.exp (p.1 (Fin.last N) ^ 2 / K) := by ring
  have hint : Integrable (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ (2 * k)) G :=
    (hexp.const_mul ((k.factorial : ℝ) * K ^ k)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg ((even_two_mul k).pow_nonneg _)]
        exact hpt p)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint (hexp.const_mul _) hpt

/-- Elementary bound `exp (-(N + 1)) ≤ (N + 1)⁻¹ ^ 2 * 2` (since `e^x ≥ x² / 2` for `x ≥ 0`),
used to absorb `exp (-(N + 1))` into `(N + 1)⁻¹`. -/
private lemma exp_neg_nat_add_one_le_two_mul_inv_sq (N : ℕ) :
    Real.exp (-((N : ℝ) + 1)) ≤ 2 * ((N : ℝ) + 1)⁻¹ ^ 2 := by
  have hx : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : ((N : ℝ) + 1) ^ 2 / (2 : ℕ).factorial ≤ Real.exp ((N : ℝ) + 1) :=
    Real.pow_div_factorial_le_exp ((N : ℝ) + 1) hx.le 2
  rw [Nat.factorial_two, Nat.cast_ofNat] at h1
  rw [Real.exp_neg, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx 2), inv_mul_eq_div,
    div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- Pointwise bound on `|R^t_{a,b} - R_{a,b}|`: since `t ∈ [0, 1]`, the truncated overlap differs
from the full overlap by at most `(N + 1)⁻¹ * |ε_a * ε_b|`. -/
private lemma abs_truncated_overlap_sub_full_le {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x y : ℝ^(N + 1)) :
    |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, x i.castSucc * y i.castSucc) +
        t * (x (Fin.last N) * y (Fin.last N))) -
      ((N : ℝ) + 1)⁻¹ * ⟪x, y⟫| ≤
      ((N : ℝ) + 1)⁻¹ * |x (Fin.last N) * y (Fin.last N)| := by
  have hinner : ⟪x, y⟫ = (∑ i : Fin N, x i.castSucc * y i.castSucc) +
      x (Fin.last N) * y (Fin.last N) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_castSucc (n := N)]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · ring
  rw [hinner, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : (∑ i : Fin N, x i.castSucc * y i.castSucc) + t * (x (Fin.last N) * y (Fin.last N)) -
      ((∑ i : Fin N, x i.castSucc * y i.castSucc) + x (Fin.last N) * y (Fin.last N)) =
      -(1 - t) * (x (Fin.last N) * y (Fin.last N)) := by ring
  rw [hsub, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.2 ht1)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)

/-- Symmetry of the `M + 1` constraints in the cavity path: permuting the `M + 1` constraint rows
in the disorder leaves the quenched replica average of any spin observable invariant, and for a
single constraint index `k : Fin (M + 1)` turns the `k`-th constraint field into the last
constraint field `Fin.last M`. -/
theorem integral_shcherbinaTirozziCavity_constraint_swap {R_rep : Type*} [Fintype R_rep]
    {N M : ℕ} (κ h : ℝ) (r : ℝ≥0) (rBar t : ℝ) (u : ℝ → ℝ) (k : Fin (M + 1))
    (Φ : (Fin (N + 1) → ℝ) → (R_rep → ℝ^(N + 1)) → ℝ) :
    let P_full := (gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    ∫ d, ∫ σ : R_rep → ℝ^(N + 1), Φ (d.2.1 k) σ
        ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun x =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 x) ∂P_full =
      ∫ d, ∫ σ : R_rep → ℝ^(N + 1), Φ (d.2.1 (Fin.last M)) σ
        ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun x =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 x) ∂P_full := by
  intro P_full
  set perm : Equiv.Perm (Fin (M + 1)) := Equiv.swap k (Fin.last M)
  set γ_row : Measure (Fin (N + 1) → ℝ) := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  set e_g : (Fin (M + 1) → Fin (N + 1) → ℝ) ≃ᵐ (Fin (M + 1) → Fin (N + 1) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (M + 1) => Fin (N + 1) → ℝ) perm
  have he_g : MeasurePreserving e_g (Measure.pi fun _ : Fin (M + 1) => γ_row)
      (Measure.pi fun _ : Fin (M + 1) => γ_row) :=
    measurePreserving_piCongrLeft (fun _ : Fin (M + 1) => γ_row) perm
  set e_d := (MeasurableEquiv.refl ℝ).prodCongr
    (e_g.prodCongr (MeasurableEquiv.refl (Fin (N + 1) → ℝ)))
  have he_d : MeasurePreserving e_d P_full P_full :=
    (MeasurePreserving.id _).prod (he_g.prod (MeasurePreserving.id _))
  rw [← he_d.integral_comp e_d.measurableEmbedding]
  refine integral_congr_ae (ae_of_all _ fun d => ?_)
  have heg_apply : ∀ j : Fin (M + 1), e_g d.2.1 j = d.2.1 (perm.symm j) := fun j => by
    have := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (M + 1) => Fin (N + 1) → ℝ) perm d.2.1 (perm.symm j)
    simpa [e_g] using this
  have hk_eq : e_g d.2.1 k = d.2.1 (Fin.last M) := by
    rw [heg_apply]
    simp [perm]
  have hH : ∀ x : ℝ^(N + 1),
      shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u (e_g d.2.1) d.2.2 x =
        shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 x := fun x => by
    simp only [shcherbinaTirozziCavityHamiltonian]
    congr 4
    refine Fintype.sum_equiv perm.symm _ _ fun j => ?_
    rw [heg_apply]
  change (∫ σ : R_rep → ℝ^(N + 1), Φ (e_g d.2.1 k) σ
      ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun x =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u (e_g d.2.1) d.2.2 x)) = _
  simp_rw [hk_eq, hH]

/-- Under `G_aux w` with `Integrable (exp (‖p.1‖² / K₁)) (G_aux w)`, the full overlap deviation
`|R_{a,b} - m|` is in `L²` under `G_aux w^{⊗ R_big}`. -/
private lemma memLp_two_overlap_of_exp_sq_norm {R_big : Type*} [Fintype R_big] {N : ℕ}
    {G : Measure (ℝ^(N + 1) × ℝ)} [IsProbabilityMeasure G] {K₁ m_val : ℝ} (hK₁ : 0 < K₁)
    (hexp : Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (‖p.1‖ ^ 2 / K₁)) G) (a b : R_big) :
    MemLp (fun σ : R_big → ℝ^(N + 1) × ℝ =>
        |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_val|) 2
      (Measure.pi fun _ : R_big => G) := by
  have hm : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
      |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_val| := by
    have ha : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ a).1 :=
      measurable_fst.comp (measurable_pi_apply a)
    have hb : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ b).1 :=
      measurable_fst.comp (measurable_pi_apply b)
    exact continuous_abs.measurable.comp (((ha.inner hb).const_mul _).sub measurable_const)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h4 : ∀ x : ℝ^(N + 1), ‖x‖ ^ 4 ≤ 2 * K₁ ^ 2 * Real.exp (‖x‖ ^ 2 / K₁) := fun x => by
    have hts := Real.pow_div_factorial_le_exp (‖x‖ ^ 2 / K₁) (by positivity) 2
    rw [div_pow, Nat.factorial_two, Nat.cast_ofNat, div_le_iff₀ two_pos] at hts
    rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring]
    have hK : 0 < K₁ ^ 2 := by positivity
    calc (‖x‖ ^ 2) ^ 2 = K₁ ^ 2 * ((‖x‖ ^ 2) ^ 2 / K₁ ^ 2) := by field_simp
      _ ≤ K₁ ^ 2 * (Real.exp (‖x‖ ^ 2 / K₁) * 2) := mul_le_mul_of_nonneg_left hts hK.le
      _ = 2 * K₁ ^ 2 * Real.exp (‖x‖ ^ 2 / K₁) := by ring
  have hdom : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
      2 * m_val ^ 2 + 2 * K₁ ^ 2 * (Real.exp (‖(σ a).1‖ ^ 2 / K₁) +
        Real.exp (‖(σ b).1‖ ^ 2 / K₁))) (Measure.pi fun _ : R_big => G) :=
    (integrable_const _).add ((((measurePreserving_eval (fun _ : R_big => G)
      a).integrable_comp_of_integrable hexp).add
      ((measurePreserving_eval (fun _ : R_big => G) b).integrable_comp_of_integrable
        hexp)).const_mul _)
  refine hdom.mono' (hm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq_abs]
  have hinv : ((N : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have h1 : (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) ^ 2 ≤
      (‖(σ a).1‖ ^ 4 + ‖(σ b).1‖ ^ 4) / 2 := by
    have h2 : |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫| ≤ ‖(σ a).1‖ * ‖(σ b).1‖ := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hinv).trans (abs_real_inner_le_norm _ _)
    rw [← sq_abs]
    have h3 : |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫| ^ 2 ≤ ‖(σ a).1‖ ^ 2 * ‖(σ b).1‖ ^ 2 := by
      simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) h2 2
    nlinarith [sq_nonneg (‖(σ a).1‖ ^ 2 - ‖(σ b).1‖ ^ 2)]
  have hsq : (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_val) ^ 2 ≤
      2 * (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) ^ 2 + 2 * m_val ^ 2 := by
    nlinarith [sq_nonneg (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ + m_val)]
  linarith [h4 (σ a).1, h4 (σ b).1]

/-- Under `G_aux w` with `Integrable (exp (‖p.1‖² / K₁)) (G_aux w)`, the product of two last spins
`|ε_a * ε_b|` is in `L²` under `G_aux w^{⊗ R_big}`. -/
private lemma memLp_two_last_spin_mul_of_exp_sq_norm {R_big : Type*} [Fintype R_big] {N : ℕ}
    {G : Measure (ℝ^(N + 1) × ℝ)} [IsProbabilityMeasure G] {K₁ : ℝ} (hK₁ : 0 < K₁)
    (hexp : Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (‖p.1‖ ^ 2 / K₁)) G) (a b : R_big) :
    MemLp (fun σ : R_big → ℝ^(N + 1) × ℝ =>
        |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|) 2
      (Measure.pi fun _ : R_big => G) := by
  have hm : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
      |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| := by
    have hc : ∀ i : R_big, Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ i).1 (Fin.last N) :=
      fun i => ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
        (measurable_fst.comp (measurable_pi_apply i))
    exact continuous_abs.measurable.comp ((hc a).mul (hc b))
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h4 : ∀ x : ℝ^(N + 1), x (Fin.last N) ^ 4 ≤ 2 * K₁ ^ 2 * Real.exp (‖x‖ ^ 2 / K₁) := by
    intro x
    have hcoord : |x (Fin.last N)| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (Fin.last N)
    have hle : x (Fin.last N) ^ 4 ≤ ‖x‖ ^ 4 := by
      rw [show x (Fin.last N) ^ 4 = |x (Fin.last N)| ^ 4 by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]]
      exact pow_le_pow_left₀ (abs_nonneg _) hcoord 4
    have hts := Real.pow_div_factorial_le_exp (‖x‖ ^ 2 / K₁) (by positivity) 2
    rw [div_pow, Nat.factorial_two, Nat.cast_ofNat, div_le_iff₀ two_pos] at hts
    rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring] at hle
    have hK : 0 < K₁ ^ 2 := by positivity
    calc x (Fin.last N) ^ 4 ≤ (‖x‖ ^ 2) ^ 2 := hle
      _ = K₁ ^ 2 * ((‖x‖ ^ 2) ^ 2 / K₁ ^ 2) := by field_simp
      _ ≤ K₁ ^ 2 * (Real.exp (‖x‖ ^ 2 / K₁) * 2) := mul_le_mul_of_nonneg_left hts hK.le
      _ = 2 * K₁ ^ 2 * Real.exp (‖x‖ ^ 2 / K₁) := by ring
  have hdom : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
      K₁ ^ 2 * (Real.exp (‖(σ a).1‖ ^ 2 / K₁) + Real.exp (‖(σ b).1‖ ^ 2 / K₁)))
      (Measure.pi fun _ : R_big => G) :=
    (((measurePreserving_eval (fun _ : R_big => G) a).integrable_comp_of_integrable hexp).add
      ((measurePreserving_eval (fun _ : R_big => G) b).integrable_comp_of_integrable
        hexp)).const_mul _
  refine hdom.mono' (hm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq_abs, mul_pow]
  have h1 : (σ a).1 (Fin.last N) ^ 2 * (σ b).1 (Fin.last N) ^ 2 ≤
      ((σ a).1 (Fin.last N) ^ 4 + (σ b).1 (Fin.last N) ^ 4) / 2 := by
    nlinarith [sq_nonneg ((σ a).1 (Fin.last N) ^ 2 - (σ b).1 (Fin.last N) ^ 2)]
  linarith [h4 (σ a).1, h4 (σ b).1]

/-- Elementary polynomial growth bound for `((N + 1)⁻¹ ‖σ 0‖² - ρ)²` on `Fin 1 → ℝ^(N+1)`. -/
private lemma selfOverlap_sub_sq_poly_bound {N : ℕ} {ρ Q : ℝ} (hρ0 : 0 ≤ ρ) (hρQ : ρ ≤ Q)
    (σ : Fin 1 → ℝ^(N + 1)) :
    |(((N : ℝ) + 1)⁻¹ * ‖σ 0‖ ^ 2 - ρ) ^ 2| ≤
      (1 + Q) ^ 2 * ∏ l : Fin 1, (1 + ‖σ l‖) ^ 4 := by
  rw [abs_of_nonneg (sq_nonneg _), Fin.prod_univ_one]
  have hinv : ((N : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have h1 : |((N : ℝ) + 1)⁻¹ * ‖σ 0‖ ^ 2 - ρ| ≤ (1 + Q) * (1 + ‖σ 0‖) ^ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg hρ0]
    have h2 : ((N : ℝ) + 1)⁻¹ * ‖σ 0‖ ^ 2 ≤ (1 + ‖σ 0‖) ^ 2 :=
      (mul_le_of_le_one_left (sq_nonneg _) hinv).trans (by nlinarith [norm_nonneg (σ 0)])
    have h3 : (1 : ℝ) ≤ (1 + ‖σ 0‖) ^ 2 := by nlinarith [norm_nonneg (σ 0)]
    nlinarith [hρQ]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs, mul_pow, ← pow_mul] at hsq
  exact hsq

/-- Elementary polynomial growth bound for `((N + 1)⁻¹ ⟪σ 0, σ 1⟫ - q)²` on `Fin 2 → ℝ^(N+1)`. -/
private lemma overlap_sub_sq_poly_bound {N : ℕ} {q Q : ℝ} (hq0 : 0 ≤ q) (hqQ : q ≤ Q)
    (σ : Fin 2 → ℝ^(N + 1)) :
    |(((N : ℝ) + 1)⁻¹ * ⟪σ 0, σ 1⟫ - q) ^ 2| ≤
      (1 + Q) ^ 2 * ∏ l : Fin 2, (1 + ‖σ l‖) ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _), Fin.prod_univ_two]
  have hinv : ((N : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have h1 : |((N : ℝ) + 1)⁻¹ * ⟪σ 0, σ 1⟫ - q| ≤
      (1 + Q) * ((1 + ‖σ 0‖) * (1 + ‖σ 1‖)) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg hq0]
    have h2 : ((N : ℝ) + 1)⁻¹ * |⟪σ 0, σ 1⟫| ≤ (1 + ‖σ 0‖) * (1 + ‖σ 1‖) :=
      (mul_le_of_le_one_left (abs_nonneg _) hinv).trans
        ((abs_real_inner_le_norm _ _).trans (mul_le_mul (by linarith) (by linarith)
          (norm_nonneg _) (by positivity)))
    have h3 : (1 : ℝ) ≤ (1 + ‖σ 0‖) * (1 + ‖σ 1‖) :=
      one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg (σ 0)])
        (by linarith [norm_nonneg (σ 1)])
    nlinarith [hqQ]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs, mul_pow, mul_pow] at hsq
  exact hsq

/-- Under `G` with `Integrable (exp (‖p.1‖² / K₁)) G`, `|R_{a,b} - m| ^ 4` is integrable under
`G^{⊗ R_big}`. -/
private lemma integrable_overlap_dev_pow_four {R_big : Type*} [Fintype R_big] {N : ℕ}
    {G : Measure (ℝ^(N + 1) × ℝ)} [IsProbabilityMeasure G] {K₁ m_val : ℝ} (hK₁ : 0 < K₁)
    (hexp : Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (‖p.1‖ ^ 2 / K₁)) G) (a b : R_big) :
    Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
        |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_val| ^ 4)
      (Measure.pi fun _ : R_big => G) := by
  have hm : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
      |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_val| := by
    have ha : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ a).1 :=
      measurable_fst.comp (measurable_pi_apply a)
    have hb : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ b).1 :=
      measurable_fst.comp (measurable_pi_apply b)
    exact continuous_abs.measurable.comp (((ha.inner hb).const_mul _).sub measurable_const)
  have h8 : ∀ x : ℝ^(N + 1), ‖x‖ ^ 8 ≤ 24 * K₁ ^ 4 * Real.exp (‖x‖ ^ 2 / K₁) := fun x => by
    have hts := Real.pow_div_factorial_le_exp (‖x‖ ^ 2 / K₁) (by positivity) 4
    rw [div_pow, show (4 : ℕ).factorial = 24 by rfl, Nat.cast_ofNat,
      div_le_iff₀ (by norm_num)] at hts
    rw [show ‖x‖ ^ 8 = (‖x‖ ^ 2) ^ 4 by ring]
    have hK : 0 < K₁ ^ 4 := by positivity
    calc (‖x‖ ^ 2) ^ 4 = K₁ ^ 4 * ((‖x‖ ^ 2) ^ 4 / K₁ ^ 4) := by field_simp
      _ ≤ K₁ ^ 4 * (Real.exp (‖x‖ ^ 2 / K₁) * 24) := mul_le_mul_of_nonneg_left hts hK.le
      _ = 24 * K₁ ^ 4 * Real.exp (‖x‖ ^ 2 / K₁) := by ring
  have hdom : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
      8 * m_val ^ 4 +
        96 * K₁ ^ 4 * (Real.exp (‖(σ a).1‖ ^ 2 / K₁) + Real.exp (‖(σ b).1‖ ^ 2 / K₁)))
      (Measure.pi fun _ : R_big => G) :=
    (integrable_const _).add ((((measurePreserving_eval (fun _ : R_big => G)
      a).integrable_comp_of_integrable hexp).add
      ((measurePreserving_eval (fun _ : R_big => G) b).integrable_comp_of_integrable
        hexp)).const_mul _)
  refine hdom.mono' (hm.pow_const 4).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) 4)]
  have hX4 : |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_val| ^ 4 ≤
      8 * ((((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) ^ 4 + m_val ^ 4) := by
    have hsub := abs_sub (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) m_val
    refine (pow_le_pow_left₀ (abs_nonneg _) hsub 4).trans ?_
    have h := add_pow_le (abs_nonneg (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫)) (abs_nonneg m_val) 4
    simp only [show (2 : ℝ) ^ (4 - 1) = 8 by norm_num,
      show ∀ x : ℝ, |x| ^ 4 = x ^ 4 from fun x => by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]] at h
    exact h
  refine hX4.trans ?_
  have hinv : ((N : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have h1 : (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) ^ 4 ≤
      (‖(σ a).1‖ ^ 8 + ‖(σ b).1‖ ^ 8) / 2 := by
    have habs : |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫| ≤ ‖(σ a).1‖ * ‖(σ b).1‖ := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hinv).trans (abs_real_inner_le_norm _ _)
    have h4' : (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) ^ 4 ≤ ‖(σ a).1‖ ^ 4 * ‖(σ b).1‖ ^ 4 := by
      rw [show (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) ^ 4 =
        |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫| ^ 4 by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]]
      simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) habs 4
    nlinarith [sq_nonneg (‖(σ a).1‖ ^ 4 - ‖(σ b).1‖ ^ 4)]
  linarith [h8 (σ a).1, h8 (σ b).1]

/-- Under `ν_{t,v}`, the `L²` norm of `R_{a,b} - m_{ab}` is bounded by `K` times
`√(ν_t((R_{1,1} - ρ)²)) + (N+1)⁻¹` (if `a = b`) or `√(ν_t((R_{1,2} - q)²)) + (N+1)⁻¹`
(if `a ≠ b`), via Lemma 3.2.9 (Eq. (3.106)) and Eq. (3.104). -/
private lemma exists_integral_shcherbinaTirozziAuxCavity_overlap_sq_le
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t v q ρ rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ)
      {R_big : Type} [Fintype R_big] [DecidableEq R_big] (a b : R_big),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → (r : ℝ) ≤ R → (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D) → -D ≤ u 0 →
      let P_full := ((gaussianReal 0 r).prod
        ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
      let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let S_v : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
        Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
          Real.sqrt (1 - v) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
      let G_aux : AuxDis[N, M] → Measure (ℝ^(N + 1) × ℝ) := fun w =>
        ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
          fun p => E_old w p.1 + u (S_v w p)
      let G_full (d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :
          Measure (ℝ^(N + 1)) :=
        (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ
      Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
          (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q) ^ 2
          ∂(Measure.pi fun _ : R_big => G_aux w)) auxLaw[N, M, r] ∧
        ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
          (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q) ^ 2
          ∂(Measure.pi fun _ : R_big => G_aux w) ∂auxLaw[N, M, r] ≤
          K * ((if a = b then
              ∫ d, ∫ x : ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full d) ∂P_full
            else
              ∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
                (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
                ∂(Measure.pi fun _ : Fin 2 => G_full d) ∂P_full) +
            ((N : ℝ) + 1)⁻¹ ^ 2) := by
  obtain ⟨K_mom, hK_mom_pos, h3104⟩ :=
    exists_shcherbinaTirozziAuxCavity_overlap_tails_and_moments κ₀ h₀ D Q R R_diff
      hκ₀ hQ hR hR_diff
  obtain ⟨K_gr1, hK_gr1_pos, hgr1⟩ :=
    exists_shcherbinaTirozziAuxCavity_le_add_exp (R_rep := Fin 1) κ₀ h₀ D Q R R_diff
      hκ₀ hQ hR hR_diff
  obtain ⟨K_gr2, hK_gr2_pos, hgr2⟩ :=
    exists_shcherbinaTirozziAuxCavity_le_add_exp (R_rep := Fin 2) κ₀ h₀ D Q R R_diff
      hκ₀ hQ hR hR_diff
  obtain ⟨K₁, -, hK₁_pos, -, hK₁_ge₀, -⟩ :=
    exists_integral_exp_sq_norm_shcherbinaTirozziAuxCavity_le_exp κ₀ h₀ D Q R R_diff
      hκ₀ hQ hR hR_diff
  set K : ℝ := max K_gr1 K_gr2 * max 1 (2 * Real.sqrt K_mom)
  have hK_pos : 0 < K := mul_pos (lt_of_lt_of_le hK_gr1_pos (le_max_left _ _))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨K, hK_pos, fun N M κ h t v q ρ rBar r u {R_big} _ _ a b hκ hh ht0 ht1 hv0 hv1 hq0 hqρ
    hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD => ?_⟩
  intro P_full E_old S_v G_aux G_full
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have ha_inv : K₁⁻¹ < κ := by
    refine inv_lt_of_inv_lt₀ hκ0 (lt_of_lt_of_le ?_
      ((div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ).trans hK₁_ge₀))
    rw [inv_eq_one_div]
    exact div_lt_div_of_pos_right (by norm_num) hκ0
  have hstate := shcherbinaTirozziAuxCavity_state_properties (R_rep := R_big) (N := N) (M := M)
    (h := h) hκ0 hrr ht0 ht1 hum hu0 ha_inv (r := r) (v := v) (q := q) (ρ := ρ)
  have : ∀ w, IsProbabilityMeasure (G_aux w) := fun w => hstate.1 w
  -- Integrability of `Dev²` from `Dev⁴` (via `x² ≤ 1 + x⁴`)
  obtain ⟨-, -, h4i, h4le, -, -⟩ := h3104 (R_rep := R_big) N M κ h t v q ρ rBar r u D a b
    hκ hh ht0 ht1 hv0 hv1 hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD
  have h2m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
      (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q) ^ 2 := by
    have ha : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ a).1 :=
      measurable_fst.comp (measurable_pi_apply a)
    have hb : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ b).1 :=
      measurable_fst.comp (measurable_pi_apply b)
    exact (((ha.inner hb).const_mul _).sub measurable_const).pow_const 2
  have h2i : Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
      (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q) ^ 2
      ∂(Measure.pi fun _ : R_big => G_aux w)) auxLaw[N, M, r] := by
    refine ((integrable_const (1 : ℝ)).add h4i).mono' (hstate.2.2 _ h2m).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _), Pi.add_apply]
    have h4w := integrable_overlap_dev_pow_four (R_big := R_big) hK₁_pos (hstate.2.1 w) a b
      (m_val := if a = b then ρ else q)
    have h2w : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
        (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q) ^ 2)
        (Measure.pi fun _ : R_big => G_aux w) := by
      have h := (memLp_two_overlap_of_exp_sq_norm (R_big := R_big) hK₁_pos (hstate.2.1 w) a b
        (m_val := if a = b then ρ else q)).integrable_sq
      simpa only [sq_abs] using h
    calc ∫ σ, (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q) ^ 2
            ∂(Measure.pi fun _ : R_big => G_aux w)
        ≤ ∫ σ, (1 + |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q| ^ 4)
            ∂(Measure.pi fun _ : R_big => G_aux w) := by
          refine integral_mono h2w ((integrable_const 1).add h4w) fun σ => ?_
          set x : ℝ := |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q|
          rw [← sq_abs]
          nlinarith [sq_nonneg (x ^ 2 - 1)]
      _ = 1 + ∫ σ, |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q| ^ 4
            ∂(Measure.pi fun _ : R_big => G_aux w) := by
          rw [integral_add (integrable_const 1) h4w, integral_const, probReal_univ, one_smul]
  refine ⟨h2i, ?_⟩
  -- Marginalize from `R_big` to `Fin 1` (`a = b`) or `Fin 2` (`a ≠ b`), then apply Lemma 3.2.9
  have hexp_le := exp_neg_nat_add_one_le_two_mul_inv_sq N
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    set f₁ : (Fin 1 → ℝ^(N + 1)) → ℝ := fun σ => (((N : ℝ) + 1)⁻¹ * ‖σ 0‖ ^ 2 - ρ) ^ 2
    have hf₁m : Measurable f₁ := by
      have h0 : Measurable fun σ : Fin 1 → ℝ^(N + 1) => σ 0 := measurable_pi_apply 0
      exact (((h0.norm.pow_const 2).const_mul _).sub measurable_const).pow_const 2
    have hf₁0 : ∀ σ, 0 ≤ f₁ σ := fun _ => sq_nonneg _
    have hf₁b : ∀ σ, |f₁ σ| ≤ (1 + Q) ^ 2 * ∏ l : Fin 1, (1 + ‖σ l‖) ^ 4 :=
      selfOverlap_sub_sq_poly_bound (hq0.trans hqρ) hρQ
    -- Apply Lemma 3.2.9 to `f₁` with `A = √K_mom` (before `clear_value G_aux`)
    have hF2_all : ∀ s ∈ Icc (0 : ℝ) 1,
        ∫ w, ∫ σ : Fin 1 → ℝ^(N + 1) × ℝ, f₁ (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : Fin 1 =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              E_old w p.1 + u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)))
          ∂auxLaw[N, M, r] ≤ Real.sqrt K_mom ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hK_mom_pos.le]
      have h4 := (h3104 (R_rep := Fin 1) N M κ h t s q ρ rBar r u D 0 0 hκ hh ht0 ht1 hs.1 hs.2
        hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD).2.2.2.1
      refine le_of_eq_of_le ?_ h4
      refine integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => ?_))
      dsimp only [f₁]
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, ← pow_mul,
        show 2 * 2 = 4 by rfl,
        show |((N : ℝ) + 1)⁻¹ * ‖(σ 0).1‖ ^ 2 - ρ| ^ 4 =
          (((N : ℝ) + 1)⁻¹ * ‖(σ 0).1‖ ^ 2 - ρ) ^ 4 by
          rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]]
    have hgr := hgr1 N M κ h t q ρ rBar r u hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR hrr_diff hM
      huc hu0 hu1 hu2 hD hD₂ huD hf₁m hf₁0 hf₁b (Real.sqrt_nonneg _) ⟨hv0, hv1⟩ hF2_all
    change ∫ w, ∫ σ : Fin 1 → ℝ^(N + 1) × ℝ, f₁ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 1 => G_aux w) ∂auxLaw[N, M, r] ≤
      K_gr1 * ((∫ d, ∫ a : Fin 1 → ℝ^(N + 1), f₁ a ∂(Measure.pi fun _ : Fin 1 => G_full d)
        ∂P_full) + Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom) at hgr
    have hprob_full : ∀ d, IsProbabilityMeasure (G_full d) := fun d => isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
        (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) hum hu0 _ _)
    clear_value G_aux G_full
    clear E_old S_v hstate h3104 hgr1 hgr2 hF2_all
    -- Rewrite LHS via `integral_pi_comp_injective`
    have hm1 : Measurable fun σ : Fin 1 → ℝ^(N + 1) × ℝ =>
        (((N : ℝ) + 1)⁻¹ * ‖(σ 0).1‖ ^ 2 - ρ) ^ 2 :=
      ((((measurable_fst.comp (measurable_pi_apply (0 : Fin 1))).norm.pow_const 2).const_mul
        _).sub measurable_const).pow_const 2
    have hinj : Function.Injective (fun _ : Fin 1 => a) := fun i j _ => Subsingleton.elim i j
    have hlhs : (∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
          (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ a).1⟫ - ρ) ^ 2
          ∂(Measure.pi fun _ : R_big => G_aux w) ∂auxLaw[N, M, r]) =
        ∫ w, ∫ σ : Fin 1 → ℝ^(N + 1) × ℝ, f₁ (fun l => (σ l).1)
          ∂(Measure.pi fun _ : Fin 1 => G_aux w) ∂auxLaw[N, M, r] := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      have hcomp := integral_pi_comp_injective (G_aux w) hinj
        (fun σ : Fin 1 → ℝ^(N + 1) × ℝ => (((N : ℝ) + 1)⁻¹ * ‖(σ 0).1‖ ^ 2 - ρ) ^ 2)
        hm1.aestronglyMeasurable
      refine Eq.trans (integral_congr_ae (ae_of_all _ fun σ => ?_)) hcomp
      dsimp only
      rw [real_inner_self_eq_norm_sq]
    rw [hlhs]
    -- Simplify `Fin 1` integral at `t` back to single-replica integral
    have h1eq : (∫ d, ∫ a : Fin 1 → ℝ^(N + 1), f₁ a ∂(Measure.pi fun _ : Fin 1 => G_full d)
          ∂P_full) =
        ∫ d, ∫ x : ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full d) ∂P_full := by
      refine integral_congr_ae (ae_of_all _ fun d => ?_)
      have := hprob_full d
      exact integral_pi_eval (G_full d) (0 : Fin 1)
        (fun x : ℝ^(N + 1) => (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2)
        ((((continuous_norm.measurable.pow_const 2).const_mul _).sub
          measurable_const).pow_const 2).aestronglyMeasurable
    rw [h1eq] at hgr
    refine hgr.trans ?_
    have h1 : Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom ≤
        (2 * Real.sqrt K_mom) * ((N : ℝ) + 1)⁻¹ ^ 2 := by
      calc Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom
          ≤ (2 * ((N : ℝ) + 1)⁻¹ ^ 2) * Real.sqrt K_mom :=
            mul_le_mul_of_nonneg_right hexp_le (Real.sqrt_nonneg _)
        _ = (2 * Real.sqrt K_mom) * ((N : ℝ) + 1)⁻¹ ^ 2 := by ring
    set I₁ := ∫ d, ∫ x : ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full d) ∂P_full
    have hI₁ : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
    have h2 : I₁ + Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom ≤
        max 1 (2 * Real.sqrt K_mom) * (I₁ + ((N : ℝ) + 1)⁻¹ ^ 2) := by
      rw [mul_add]
      exact add_le_add (le_mul_of_one_le_left hI₁ (le_max_left _ _))
        (h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))
    calc K_gr1 * (I₁ + Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom)
        ≤ max K_gr1 K_gr2 * (max 1 (2 * Real.sqrt K_mom) * (I₁ + ((N : ℝ) + 1)⁻¹ ^ 2)) :=
          mul_le_mul (le_max_left _ _) h2 (by positivity)
            (le_trans hK_gr1_pos.le (le_max_left _ _))
      _ = K * (I₁ + ((N : ℝ) + 1)⁻¹ ^ 2) := by dsimp only [K]; ring
  · simp only [hab, ↓reduceIte]
    set f₂ : (Fin 2 → ℝ^(N + 1)) → ℝ := fun σ => (((N : ℝ) + 1)⁻¹ * ⟪σ 0, σ 1⟫ - q) ^ 2
    have hf₂m : Measurable f₂ := by
      have h0 : Measurable fun σ : Fin 2 → ℝ^(N + 1) => σ 0 := measurable_pi_apply 0
      have h1 : Measurable fun σ : Fin 2 → ℝ^(N + 1) => σ 1 := measurable_pi_apply 1
      exact (((h0.inner h1).const_mul _).sub measurable_const).pow_const 2
    have hf₂0 : ∀ σ, 0 ≤ f₂ σ := fun _ => sq_nonneg _
    have hf₂b : ∀ σ, |f₂ σ| ≤ (1 + Q) ^ 2 * ∏ l : Fin 2, (1 + ‖σ l‖) ^ 2 :=
      overlap_sub_sq_poly_bound hq0 (hqρ.trans hρQ)
    have hF2_all : ∀ s ∈ Icc (0 : ℝ) 1,
        ∫ w, ∫ σ : Fin 2 → ℝ^(N + 1) × ℝ, f₂ (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : Fin 2 =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              E_old w p.1 + u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)))
          ∂auxLaw[N, M, r] ≤ Real.sqrt K_mom ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hK_mom_pos.le]
      have h4 := (h3104 (R_rep := Fin 2) N M κ h t s q ρ rBar r u D (0 : Fin 2) (1 : Fin 2)
        hκ hh ht0 ht1 hs.1 hs.2 hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂
        huD).2.2.2.1
      refine le_of_eq_of_le ?_ h4
      refine integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => ?_))
      have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
      dsimp only [f₂]
      rw [ite_eq_right h01, ← pow_mul, show 2 * 2 = 4 by rfl,
        show |((N : ℝ) + 1)⁻¹ * ⟪(σ 0).1, (σ 1).1⟫ - q| ^ 4 =
          (((N : ℝ) + 1)⁻¹ * ⟪(σ 0).1, (σ 1).1⟫ - q) ^ 4 by
          rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]]
    have hgr := hgr2 N M κ h t q ρ rBar r u hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR hrr_diff hM
      huc hu0 hu1 hu2 hD hD₂ huD hf₂m hf₂0 hf₂b (Real.sqrt_nonneg _) ⟨hv0, hv1⟩ hF2_all
    change ∫ w, ∫ σ : Fin 2 → ℝ^(N + 1) × ℝ, f₂ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 2 => G_aux w) ∂auxLaw[N, M, r] ≤
      K_gr2 * ((∫ d, ∫ a : Fin 2 → ℝ^(N + 1), f₂ a ∂(Measure.pi fun _ : Fin 2 => G_full d)
        ∂P_full) + Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom) at hgr
    clear_value G_aux G_full
    clear E_old S_v hstate h3104 hgr1 hgr2 hF2_all
    have hlhs : (∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
          (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - q) ^ 2
          ∂(Measure.pi fun _ : R_big => G_aux w) ∂auxLaw[N, M, r]) =
        ∫ w, ∫ σ : Fin 2 → ℝ^(N + 1) × ℝ, f₂ (fun l => (σ l).1)
          ∂(Measure.pi fun _ : Fin 2 => G_aux w) ∂auxLaw[N, M, r] := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      set ρ_inj : Fin 2 → R_big := fun i => if i = 0 then a else b
      have hinj : Function.Injective ρ_inj := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso; exact hab (by simpa [ρ_inj] using hij)
        · exfalso; exact hab (by simpa [ρ_inj] using hij.symm)
        · rfl
      have hm2 : Measurable fun σ : Fin 2 → ℝ^(N + 1) × ℝ =>
          (((N : ℝ) + 1)⁻¹ * ⟪(σ 0).1, (σ 1).1⟫ - q) ^ 2 :=
        (((((measurable_fst.comp (measurable_pi_apply (0 : Fin 2))).inner
          (measurable_fst.comp (measurable_pi_apply (1 : Fin 2)))).const_mul _).sub
          measurable_const).pow_const 2)
      have hcomp := integral_pi_comp_injective (G_aux w) hinj
        (fun σ : Fin 2 → ℝ^(N + 1) × ℝ => (((N : ℝ) + 1)⁻¹ * ⟪(σ 0).1, (σ 1).1⟫ - q) ^ 2)
        hm2.aestronglyMeasurable
      refine Eq.trans ?_ hcomp
      exact integral_congr_ae (ae_of_all _ fun σ => by simp [ρ_inj])
    rw [hlhs]
    refine hgr.trans ?_
    have h1 : Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom ≤
        (2 * Real.sqrt K_mom) * ((N : ℝ) + 1)⁻¹ ^ 2 := by
      calc Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom
          ≤ (2 * ((N : ℝ) + 1)⁻¹ ^ 2) * Real.sqrt K_mom :=
            mul_le_mul_of_nonneg_right hexp_le (Real.sqrt_nonneg _)
        _ = (2 * Real.sqrt K_mom) * ((N : ℝ) + 1)⁻¹ ^ 2 := by ring
    set I₂ := ∫ d, ∫ p : Fin 2 → ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
      ∂(Measure.pi fun _ : Fin 2 => G_full d) ∂P_full
    have hI₂ : 0 ≤ I₂ := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
    have h2 : I₂ + Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom ≤
        max 1 (2 * Real.sqrt K_mom) * (I₂ + ((N : ℝ) + 1)⁻¹ ^ 2) := by
      rw [mul_add]
      exact add_le_add (le_mul_of_one_le_left hI₂ (le_max_left _ _))
        (h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))
    calc K_gr2 * (I₂ + Real.exp (-((N : ℝ) + 1)) * Real.sqrt K_mom)
        ≤ max K_gr1 K_gr2 * (max 1 (2 * Real.sqrt K_mom) * (I₂ + ((N : ℝ) + 1)⁻¹ ^ 2)) :=
          mul_le_mul (le_max_right _ _) h2 (by positivity)
            (le_trans hK_gr1_pos.le (le_max_left _ _))
      _ = K * (I₂ + ((N : ℝ) + 1)⁻¹ ^ 2) := by dsimp only [K]; ring

/-- **Core comparison step of Proposition 3.2.10 (Eqs. (3.108)--(3.110)):** for any finite replica
index type `R_rep`, bounded `C²` factors `ψ : R_rep → ℝ → ℝ`, and measurable spin observable `g`
of polynomial growth whose `L²` norm along `ν_{t,v}` is uniformly bounded by `A ≥ 0`, the endpoint
difference `|ν_{t,1}(g ∏ ψ_l(S_1^l)) - ν_{t,0}(g ∏ ψ_l(S_0^l))|` is bounded by
`K * A * (1 + |M₀| + |M₁| + |M₂| + |D| + |D|)^{|R_rep| + 2} *
  (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)`,
where `K > 0` depends only on `|R_rep|`, `κ₀, h₀, D, Q, R, R_diff`. -/
theorem exists_abs_shcherbinaTirozziAuxCavity_one_sub_zero_le
    {R_rep : Type} [Fintype R_rep]
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ)
      (ψ : R_rep → ℝ → ℝ) {M₀ M₁ M₂ : ℝ} {g : (R_rep → ℝ^(N + 1)) → ℝ} {C : ℝ} {m : ℕ} {A : ℝ},
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → (r : ℝ) ≤ R → (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D) → -D ≤ u 0 →
      (∀ l, Differentiable ℝ (ψ l)) → (∀ l, Differentiable ℝ (deriv (ψ l))) →
      (∀ l x, |ψ l x| ≤ M₀) → (∀ l x, |deriv (ψ l) x| ≤ M₁) →
      (∀ l x, |deriv (deriv (ψ l)) x| ≤ M₂) →
      Measurable g → (∀ σ, |g σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) → 0 ≤ A →
      let P_full := ((gaussianReal 0 r).prod
        ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
      let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let S_v (s : ℝ) : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
        Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
          Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
      let G_aux (s : ℝ) : AuxDis[N, M] → Measure (ℝ^(N + 1) × ℝ) := fun w =>
        ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
          fun p => E_old w p.1 + u (S_v s w p)
      let G_full (d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :
          Measure (ℝ^(N + 1)) :=
        (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ
      (∀ s ∈ Ioo (0 : ℝ) 1,
        Integrable (fun w => ∫ σ : R_rep → ℝ^(N + 1) × ℝ, g (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : R_rep => G_aux s w)) auxLaw[N, M, r] ∧
        ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, g (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : R_rep => G_aux s w) ∂auxLaw[N, M, r] ≤ A ^ 2) →
      |(∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          g (fun l => (σ l).1) * ∏ l, ψ l (S_v 1 w (σ l))
          ∂(Measure.pi fun _ : R_rep => G_aux 1 w) ∂auxLaw[N, M, r]) -
        (∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          g (fun l => (σ l).1) * ∏ l, ψ l (S_v 0 w (σ l))
          ∂(Measure.pi fun _ : R_rep => G_aux 0 w) ∂auxLaw[N, M, r])| ≤
        K * A * (1 + |M₀| + |M₁| + |M₂| + |D| + |D|) ^ (Fintype.card R_rep + 2) *
          (Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => G_full d) ∂P_full) +
            Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full d) ∂P_full) +
            ((N : ℝ) + 1)⁻¹) := by
  classical
  obtain ⟨K_ov, hK_ov_pos, hov_sq⟩ :=
    exists_integral_shcherbinaTirozziAuxCavity_overlap_sq_le κ₀ h₀ D Q R R_diff hκ₀ hQ hR hR_diff
  obtain ⟨K_last, hK_last_pos, hK_last_ge, h3100⟩ :=
    exists_integral_exp_sq_shcherbinaTirozziAuxCavity_last_le κ₀ h₀ D R hκ₀ hR
  obtain ⟨K₁, -, hK₁_pos, -, hK₁_ge₀, -⟩ :=
    exists_integral_exp_sq_norm_shcherbinaTirozziAuxCavity_le_exp κ₀ h₀ D Q R R_diff
      hκ₀ hQ hR hR_diff
  set n : ℕ := Fintype.card R_rep
  set K_term : ℝ := max (Real.sqrt K_ov) (Real.sqrt K_ov + Real.sqrt (2 * K_last ^ 3))
  set K : ℝ := ((n : ℝ) + 1) ^ 2 * ((n + 2 : ℝ) ^ 2) * K_term + 1
  have hK_term_pos : 0 < K_term := lt_of_lt_of_le (Real.sqrt_pos.2 hK_ov_pos) (le_max_left _ _)
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, fun N M κ h t q ρ rBar r u ψ M₀ M₁ M₂ g C m A hκ hh ht0 ht1 hq0 hqρ hρQ
    hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD hψd hψ₂d hM₀ hM₁ hM₂ hg hgb hA => ?_⟩
  intro P_full E_old S_v G_aux G_full hg2_all
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hC0 : 0 ≤ C := by
    have h0 := (abs_nonneg (g 0)).trans (hgb 0)
    have hprod : (0 : ℝ) < ∏ _l : R_rep, (1 + ‖(0 : ℝ^(N + 1))‖) ^ m := by simp
    exact nonneg_of_mul_nonneg_left h0 hprod
  have ha_inv : K₁⁻¹ < κ := by
    refine inv_lt_of_inv_lt₀ hκ0 (lt_of_lt_of_le ?_
      ((div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ).trans hK₁_ge₀))
    rw [inv_eq_one_div]
    exact div_lt_div_of_pos_right (by norm_num) hκ0
  let P := (gaussianReal 0 r).prod
    ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
  let γ := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
  let S_sh (s : ℝ) (w : Fin (N + 1) ⊕ Unit → ℝ) (p : ℝ^(N + 1) × ℝ) : ℝ :=
    Real.sqrt s * ((Real.sqrt (N + 1))⁻¹ *
        ((∑ i : Fin N, w (Sum.inl i.castSucc) * p.1 i.castSucc) +
          Real.sqrt t * (w (Sum.inl (Fin.last N)) * p.1 (Fin.last N)))) +
      Real.sqrt (1 - s) * (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (ρ - q) * p.2)
  let G_sh (s : ℝ) (d : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)))
      (w : Fin (N + 1) ⊕ Unit → ℝ) : Measure (ℝ^(N + 1) × ℝ) :=
    ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 p.1 + u (S_sh s w p)
  let φ (s : ℝ) : ℝ :=
    ∫ d, ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
      g (fun l => (σ l).1) * ∏ l, ψ l (S_sh s w (σ l))
      ∂(Measure.pi fun _ : R_rep => G_sh s d w) ∂γ ∂P
  -- Equivalence of `φ s` and the `(d_full, z)` integral at `s ∈ [0, 1]`
  have hφ_eq : ∀ s ∈ Icc (0 : ℝ) 1, φ s =
      ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
        g (fun l => (σ l).1) * ∏ l, ψ l (S_v s w (σ l))
        ∂(Measure.pi fun _ : R_rep => G_aux s w) ∂auxLaw[N, M, r] := fun s hs => by
    have hψc : ∀ l, Continuous (ψ l) := fun l => (hψd l).continuous
    have hG_m : Measurable fun p : (Fin (N + 1) ⊕ Unit → ℝ) × (R_rep → ℝ^(N + 1) × ℝ) =>
        g (fun l => (p.2 l).1) * ∏ l, ψ l (S_sh s p.1 (p.2 l)) := by
      have hg_m : Measurable fun p : (Fin (N + 1) ⊕ Unit → ℝ) × (R_rep → ℝ^(N + 1) × ℝ) =>
          g (fun l => (p.2 l).1) :=
        (hg.comp (Measurable.of_eval fun l => measurable_fst.comp (measurable_pi_apply l))).comp
          measurable_snd
      have hS_m : ∀ l : R_rep,
          Measurable fun p : (Fin (N + 1) ⊕ Unit → ℝ) × (R_rep → ℝ^(N + 1) × ℝ) =>
            S_sh s p.1 (p.2 l) := fun l => by
        have hc : Continuous fun p : (Fin (N + 1) ⊕ Unit → ℝ) × (R_rep → ℝ^(N + 1) × ℝ) =>
            S_sh s p.1 (p.2 l) := by
          dsimp only [S_sh]
          fun_prop
        exact hc.measurable
      exact hg_m.mul (Finset.measurable_prod _ fun l _ => (hψc l).measurable.comp (hS_m l))
    have hG_b : ∀ (w : Fin (N + 1) ⊕ Unit → ℝ) (σ : R_rep → ℝ^(N + 1) × ℝ),
        |g (fun l => (σ l).1) * ∏ l, ψ l (S_sh s w (σ l))| ≤
          (C * |M₀| ^ Fintype.card R_rep) * ∏ l, (1 + ‖σ l‖) ^ m := fun w σ => by
      rw [abs_mul, Finset.abs_prod]
      have hprod_le : ∏ l : R_rep, |ψ l (S_sh s w (σ l))| ≤ |M₀| ^ Fintype.card R_rep := by
        calc ∏ l : R_rep, |ψ l (S_sh s w (σ l))|
            ≤ ∏ _l : R_rep, |M₀| :=
              Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ =>
                (hM₀ l _).trans (le_abs_self M₀)
          _ = |M₀| ^ Fintype.card R_rep := by simp
      have hgb' : |g (fun l => (σ l).1)| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m :=
        (hgb _).trans (mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ =>
            pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (norm_fst_le (σ l))) m) hC0)
      calc |g (fun l => (σ l).1)| * ∏ l, |ψ l (S_sh s w (σ l))|
          ≤ (C * ∏ l, (1 + ‖σ l‖) ^ m) * |M₀| ^ Fintype.card R_rep :=
            mul_le_mul hgb' hprod_le (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
        _ = (C * |M₀| ^ Fintype.card R_rep) * ∏ l, (1 + ‖σ l‖) ^ m := by ring
    have hint := integrable_shcherbinaTirozziAuxCavity_shared (R := R_rep) (N := N) (M := M)
      (h := h) hκ0 r hrr ht0 ht1 hs.1 hs.2 q ρ hu1 hu0 hD hG_m hG_b
    exact integral_shcherbinaTirozziAuxCavity_eq_shared (R := R_rep) (N := N) (M := M)
      (κ := κ) (h := h) r rBar t s q ρ u
      (fun w σ => g (fun l => (σ l).1) * ∏ l, ψ l (S_sh s w (σ l))) hint
  rw [← hφ_eq 1 ⟨zero_le_one, le_rfl⟩, ← hφ_eq 0 ⟨le_rfl, zero_le_one⟩]
  -- Continuity of `φ` on `[0, 1]`
  have hcont : ContinuousOn φ (Icc 0 1) :=
    continuousOn_shcherbinaTirozziAuxCavity (R := R_rep) (N := N) (M := M) (h := h) hκ0 r hrr
      ht0 ht1 q ρ hu1 hu0 hD ψ (fun l => (hψd l).continuous) hM₀ hg hgb
  -- Set up the RHS bound `B_err`
  set I₂ : ℝ := ∫ d, ∫ p : Fin 2 → ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
    ∂(Measure.pi fun _ : Fin 2 => G_full d) ∂P_full
  set I₁ : ℝ := ∫ d, ∫ x : ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2
    ∂(G_full d) ∂P_full
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  set B_err : ℝ := K * A * (1 + |M₀| + |M₁| + |M₂| + |D| + |D|) ^ (n + 2) *
    (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹)
  -- Apply MVT on `[0, 1]`
  have hmvt := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hcont (C := B_err)
    (fun s hs => ?_) (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  · simpa only [sub_zero, abs_one, mul_one] using hmvt
  -- Interior derivative bound at `s ∈ (0, 1)`
  obtain ⟨D_val, hderiv, hD_le⟩ := exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le
    (R := R_rep) hκ0 r hrr ht0 ht1 hq0 hqρ hu1 hu2 hu0 hD hD₂ ψ hψd hψ₂d hM₀ hM₁ hM₂ hg hgb hs
  refine ⟨D_val, hderiv, hD_le.trans ?_⟩
  -- Bound each `(a, b)` term in the sum over `Option (Option R_rep)`
  set R_big := Option (Option R_rep)
  have hstate := shcherbinaTirozziAuxCavity_state_properties (R_rep := R_big) (N := N) (M := M)
    (h := h) hκ0 hrr ht0 ht1 hum hu0 ha_inv (r := r) (v := s) (q := q) (ρ := ρ)
  have hprob : ∀ w, IsProbabilityMeasure (G_aux s w) := fun w => hstate.1 w
  obtain ⟨hlast_i, hlast_le⟩ := h3100 N M κ h t s q ρ rBar r u D hκ hh ht0 ht1 hs.1.le hs.2.le
    hrr hrR hM huc hu0 hu1 hu2 hD hD₂
  -- `L²` bound on `g (fun l => (σ (some (some l))).1)` under `ν_{t,s}`
  have hinj_ss : Function.Injective (fun l : R_rep => (some (some l) : R_big)) :=
    (Option.some_injective _).comp (Option.some_injective _)
  have hg_sq_eq : ∀ w : AuxDis[N, M],
      (∫ σ : R_big → ℝ^(N + 1) × ℝ, |g (fun l => (σ (some (some l))).1)| ^ 2
        ∂(Measure.pi fun _ : R_big => G_aux s w)) =
      ∫ σ : R_rep → ℝ^(N + 1) × ℝ, g (fun l => (σ l).1) ^ 2
        ∂(Measure.pi fun _ : R_rep => G_aux s w) := fun w => by
    have := hprob w
    have hgm : Measurable fun σ : R_rep → ℝ^(N + 1) × ℝ => g (fun l => (σ l).1) ^ 2 :=
      (hg.comp (Measurable.of_eval fun l =>
        measurable_fst.comp (measurable_pi_apply l))).pow_const 2
    have hcomp := integral_pi_comp_injective (G_aux s w) hinj_ss
      (fun σ : R_rep → ℝ^(N + 1) × ℝ => g (fun l => (σ l).1) ^ 2) hgm.aestronglyMeasurable
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun σ => sq_abs _)) hcomp
  have hg_sq_int : Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
      |g (fun l => (σ (some (some l))).1)| ^ 2 ∂(Measure.pi fun _ : R_big => G_aux s w))
      auxLaw[N, M, r] :=
    (hg2_all s hs).1.congr (ae_of_all _ fun w => (hg_sq_eq w).symm)
  have hg_sq_le : ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
      |g (fun l => (σ (some (some l))).1)| ^ 2 ∂(Measure.pi fun _ : R_big => G_aux s w)
      ∂auxLaw[N, M, r] ≤ A ^ 2 := by
    rw [integral_congr_ae (ae_of_all _ hg_sq_eq)]
    exact (hg2_all s hs).2
  -- Bound each pair term `T a b`
  have hterm : ∀ a b : R_big,
      (∫ d, ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        |g (fun l => (σ (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) -
            if a = b then ρ else q|
        ∂(Measure.pi fun _ : R_big => G_sh s d w) ∂γ ∂P) ≤
      K_term * A * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹) := by
    intro a b
    -- Step A: Transfer `(d, w)` to `(d_full, z)` via `..._eq_shared`
    set m_ab : ℝ := if a = b then ρ else q
    have htarget : |m_ab| ≤ Q := by
      dsimp only [m_ab]
      split
      · rw [abs_of_nonneg (hq0.trans hqρ)]; exact hρQ
      · rw [abs_of_nonneg hq0]; exact hqρ.trans hρQ
    have hT_m : Measurable fun p : (Fin (N + 1) ⊕ Unit → ℝ) × (R_big → ℝ^(N + 1) × ℝ) =>
        |g (fun l => (p.2 (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (p.2 a).1 i.castSucc * (p.2 b).1 i.castSucc) +
            t * ((p.2 a).1 (Fin.last N) * (p.2 b).1 (Fin.last N))) - m_ab| := by
      have hg_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |g (fun l => (σ (some (some l))).1)| :=
        continuous_abs.measurable.comp (hg.comp (Measurable.of_eval fun l =>
          measurable_fst.comp (measurable_pi_apply (some (some l)))))
      have hcoord : ∀ (r' : R_big) (i : Fin (N + 1)),
          Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ r').1 i := fun r' i =>
        ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).comp
          (measurable_fst.comp (measurable_pi_apply r'))
      have hR_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
            t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab| :=
        continuous_abs.measurable.comp (((((Finset.measurable_sum _ fun i _ =>
          (hcoord a i.castSucc).mul (hcoord b i.castSucc)).add
          (((hcoord a (Fin.last N)).mul (hcoord b (Fin.last N))).const_mul t)).const_mul _).sub
          measurable_const))
      exact (hg_m.mul hR_m).comp measurable_snd
    have hT_b : ∀ (w : Fin (N + 1) ⊕ Unit → ℝ) (σ : R_big → ℝ^(N + 1) × ℝ),
        |(|g (fun l => (σ (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
            t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|)| ≤
          C * (2 + Q) * ∏ l : R_big, (1 + ‖σ l‖) ^ (m + 2) := fun _ σ => by
      classical
      rw [abs_mul, abs_abs, abs_abs]
      have hinv : ((N : ℝ) + 1)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg N))
      have hR_le : |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
          t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab| ≤
          (2 + Q) * ((1 + ‖σ a‖) * (1 + ‖σ b‖)) := by
        have htri : |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
            t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab| ≤
            |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| +
            ((N : ℝ) + 1)⁻¹ * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| := by
          have hsub := abs_truncated_overlap_sub_full_le ht0 ht1 (σ a).1 (σ b).1
          linarith [abs_sub_le
            (((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))))
            (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) m_ab]
        have h1 : |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| ≤
            (1 + Q) * ((1 + ‖σ a‖) * (1 + ‖σ b‖)) := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_nonneg (by positivity)]
          have h2 : ((N : ℝ) + 1)⁻¹ * |⟪(σ a).1, (σ b).1⟫| ≤ (1 + ‖σ a‖) * (1 + ‖σ b‖) :=
            (mul_le_of_le_one_left (abs_nonneg _) hinv).trans
              ((abs_real_inner_le_norm _ _).trans (mul_le_mul
                (by linarith [norm_fst_le (σ a)]) (by linarith [norm_fst_le (σ b)])
                (norm_nonneg _) (by positivity)))
          have h3 : (1 : ℝ) ≤ (1 + ‖σ a‖) * (1 + ‖σ b‖) :=
            one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg (σ a)])
              (by linarith [norm_nonneg (σ b)])
          nlinarith [htarget]
        have h2 : ((N : ℝ) + 1)⁻¹ * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ≤
            (1 + ‖σ a‖) * (1 + ‖σ b‖) := by
          refine (mul_le_of_le_one_left (abs_nonneg _) hinv).trans ?_
          rw [abs_mul]
          have ha_c : |(σ a).1 (Fin.last N)| ≤ ‖σ a‖ :=
            (show |(σ a).1 (Fin.last N)| ≤ ‖(σ a).1‖ by
              simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ a).1 (Fin.last N)).trans
              (norm_fst_le (σ a))
          have hb_c : |(σ b).1 (Fin.last N)| ≤ ‖σ b‖ :=
            (show |(σ b).1 (Fin.last N)| ≤ ‖(σ b).1‖ by
              simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ b).1 (Fin.last N)).trans
              (norm_fst_le (σ b))
          exact mul_le_mul (by linarith) (by linarith) (abs_nonneg _) (by positivity)
        linarith
      have hg_le : |g (fun l => (σ (some (some l))).1)| ≤
          C * ∏ l : R_big, (1 + ‖σ l‖) ^ m := by
        refine (hgb _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
        calc ∏ l : R_rep, (1 + ‖(σ (some (some l))).1‖) ^ m
            ≤ ∏ l : R_rep, (1 + ‖σ (some (some l))‖) ^ m :=
              Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ =>
                pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (norm_fst_le _)) m
          _ = ∏ l ∈ Finset.univ.image (fun l : R_rep => (some (some l) : R_big)),
                (1 + ‖σ l‖) ^ m :=
              (Finset.prod_image (f := fun l : R_big => (1 + ‖σ l‖) ^ m)
                fun _ _ _ _ h => hinj_ss h).symm
          _ ≤ ∏ l : R_big, (1 + ‖σ l‖) ^ m := by
              rw [← Finset.prod_sdiff (Finset.subset_univ
                (Finset.univ.image (fun l : R_rep => (some (some l) : R_big))))]
              exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity)
                (Finset.one_le_prod₀ fun l _ => one_le_pow₀ (by linarith [norm_nonneg (σ l)]))
      have hpair_le : (1 + ‖σ a‖) * (1 + ‖σ b‖) ≤ ∏ l : R_big, (1 + ‖σ l‖) ^ 2 := by
        by_cases hab : a = b
        · subst hab
          rw [← sq, ← Finset.prod_singleton (f := fun l => (1 + ‖σ l‖) ^ 2) a,
            ← Finset.prod_sdiff (Finset.subset_univ ({a} : Finset _))]
          exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity)
            (Finset.one_le_prod₀ fun l _ => one_le_pow₀ (by linarith [norm_nonneg (σ l)]))
        · have h1 : (1 + ‖σ a‖) * (1 + ‖σ b‖) ≤ (1 + ‖σ a‖) ^ 2 * (1 + ‖σ b‖) ^ 2 :=
            mul_le_mul (le_self_pow₀ (by linarith [norm_nonneg (σ a)]) (by norm_num))
              (le_self_pow₀ (by linarith [norm_nonneg (σ b)]) (by norm_num))
              (by positivity) (by positivity)
          refine h1.trans ?_
          rw [← Finset.prod_pair (f := fun l => (1 + ‖σ l‖) ^ 2) hab,
            ← Finset.prod_sdiff (Finset.subset_univ ({a, b} : Finset _))]
          exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity)
            (Finset.one_le_prod₀ fun l _ => one_le_pow₀ (by linarith [norm_nonneg (σ l)]))
      calc |g (fun l => (σ (some (some l))).1)| *
            |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|
          ≤ (C * ∏ l : R_big, (1 + ‖σ l‖) ^ m) * ((2 + Q) * ((1 + ‖σ a‖) * (1 + ‖σ b‖))) :=
            mul_le_mul hg_le hR_le (abs_nonneg _) (by positivity)
        _ ≤ (C * ∏ l : R_big, (1 + ‖σ l‖) ^ m) *
              ((2 + Q) * ∏ l : R_big, (1 + ‖σ l‖) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair_le (by positivity))
              (by positivity)
        _ = C * (2 + Q) * ∏ l : R_big, (1 + ‖σ l‖) ^ (m + 2) := by
            rw [show C * (∏ l, (1 + ‖σ l‖) ^ m) * ((2 + Q) * ∏ l, (1 + ‖σ l‖) ^ 2) =
              C * (2 + Q) * ((∏ l, (1 + ‖σ l‖) ^ m) * (∏ l, (1 + ‖σ l‖) ^ 2)) by ring,
              ← Finset.prod_mul_distrib]
            congr 1; exact Finset.prod_congr rfl fun l _ => (pow_add _ m 2).symm
    have hT_int := integrable_shcherbinaTirozziAuxCavity_shared (R := R_big) (N := N) (M := M)
      (h := h) hκ0 r hrr ht0 ht1 hs.1.le hs.2.le q ρ hu1 hu0 hD hT_m hT_b
    have hT_eq := integral_shcherbinaTirozziAuxCavity_eq_shared (R := R_big) (N := N) (M := M)
      (κ := κ) (h := h) r rBar t s q ρ u
      (fun _ σ => |g (fun l => (σ (some (some l))).1)| *
        |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
          t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|) hT_int
    rw [hT_eq]
    -- Step B: Split `|R^t - m_ab| ≤ |R - m_ab| + (N + 1)⁻¹ |ε_a ε_b|` and apply Cauchy-Schwarz
    -- to each part
    obtain ⟨hov_i, hov_le⟩ := hov_sq N M κ h t s q ρ rBar r u a b hκ hh ht0 ht1 hs.1.le hs.2.le
      hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ huD
    -- Part 1: `ν_{t,s}(|g| * |R_{a,b} - m_ab|) ≤ A * √(K_ov * (I_{ab} + (N+1)⁻²))`
    set I_ab : ℝ := if a = b then I₁ else I₂
    have hIab0 : 0 ≤ I_ab := by dsimp only [I_ab]; split <;> assumption
    have hU2 : ∀ w : AuxDis[N, M],
        MemLp (fun σ : R_big → ℝ^(N + 1) × ℝ => |g (fun l => (σ (some (some l))).1)|) 2
          (Measure.pi fun _ : R_big => G_aux s w) := fun w => by
      have := hprob w
      exact memLp_two_pi_comp_injective_of_poly_bound _ hinj_ss measurable_fst hg hgb
        (by simpa only [abs_norm] using
          integrable_one_add_abs_pow_of_integrable_exp_sq
            ((measurable_norm.comp measurable_fst).aestronglyMeasurable) hK₁_pos (hstate.2.1 w) _)
    have hV1_2 : ∀ w : AuxDis[N, M],
        MemLp (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab|) 2
          (Measure.pi fun _ : R_big => G_aux s w) := fun w => by
      have := hprob w
      exact memLp_two_overlap_of_exp_sq_norm hK₁_pos (hstate.2.1 w) a b
    have hV2_2 : ∀ w : AuxDis[N, M],
        MemLp (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|) 2
          (Measure.pi fun _ : R_big => G_aux s w) := fun w => by
      have := hprob w
      exact memLp_two_last_spin_mul_of_exp_sq_norm hK₁_pos (hstate.2.1 w) a b
    have hUV1_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
        |g (fun l => (σ (some (some l))).1)| * |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| := by
      have hg_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |g (fun l => (σ (some (some l))).1)| :=
        continuous_abs.measurable.comp (hg.comp (Measurable.of_eval fun l =>
          measurable_fst.comp (measurable_pi_apply (some (some l)))))
      have ha_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ a).1 :=
        measurable_fst.comp (measurable_pi_apply a)
      have hb_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ b).1 :=
        measurable_fst.comp (measurable_pi_apply b)
      exact hg_m.mul (continuous_abs.measurable.comp
        (((ha_m.inner hb_m).const_mul _).sub measurable_const))
    have hUV2_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
        |g (fun l => (σ (some (some l))).1)| * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| := by
      have hg_m : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |g (fun l => (σ (some (some l))).1)| :=
        continuous_abs.measurable.comp (hg.comp (Measurable.of_eval fun l =>
          measurable_fst.comp (measurable_pi_apply (some (some l)))))
      have hc : ∀ r' : R_big, Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ r').1 (Fin.last N) :=
        fun r' => ((PiLp.continuous_apply 2
          (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
          (measurable_fst.comp (measurable_pi_apply r'))
      exact hg_m.mul (continuous_abs.measurable.comp ((hc a).mul (hc b)))
    have hCS1 := abs_integral_integral_mul_le_of_integral_sq_le
      (P := auxLaw[N, M, r]) (μ := fun w => Measure.pi fun _ : R_big => G_aux s w)
      hU2 hV1_2 (hstate.2.2 _ hUV1_m).aestronglyMeasurable hg_sq_int
      (hov_i.congr (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => (sq_abs _).symm)))
      hA (Real.sqrt_nonneg (K_ov * (I_ab + ((N : ℝ) + 1)⁻¹ ^ 2))) hg_sq_le
      (by
        rw [Real.sq_sqrt (mul_nonneg hK_ov_pos.le (by positivity))]
        refine le_of_eq_of_le ?_ hov_le
        exact integral_congr_ae (ae_of_all _ fun w =>
          integral_congr_ae (ae_of_all _ fun σ => sq_abs _)))
    -- Part 2: `ν_{t,s}((ε_a ε_b)²) ≤ ν_{t,s}(ε^4) ≤ 2 K_last^3`
    have ha_last : K_last⁻¹ < κ := by
      refine inv_lt_of_inv_lt₀ hκ0 (lt_of_lt_of_le ?_
        ((div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ).trans hK_last_ge))
      rw [inv_eq_one_div]
      exact div_lt_div_of_pos_right (by norm_num) hκ0
    have hstate_last := shcherbinaTirozziAuxCavity_state_properties (R_rep := R_big) (N := N)
      (M := M) (h := h) hκ0 hrr ht0 ht1 hum hu0 ha_last (r := r) (v := s) (q := q) (ρ := ρ)
    have hε4_i : Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ^ 2
        ∂(Measure.pi fun _ : R_big => G_aux s w)) auxLaw[N, M, r] ∧
        ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
          |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ^ 2
          ∂(Measure.pi fun _ : R_big => G_aux s w) ∂auxLaw[N, M, r] ≤ 2 * K_last ^ 3 := by
      have hm_ε : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ^ 2 := by
        have hc : ∀ r' : R_big,
            Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ r').1 (Fin.last N) := fun r' =>
          ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
            (measurable_fst.comp (measurable_pi_apply r'))
        exact (continuous_abs.measurable.comp ((hc a).mul (hc b))).pow_const 2
      have hpt_w : ∀ w : AuxDis[N, M],
          ∫ σ : R_big → ℝ^(N + 1) × ℝ,
            |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ^ 2
            ∂(Measure.pi fun _ : R_big => G_aux s w) ≤
          2 * K_last ^ 2 * ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
            ∂(G_aux s w) := by
        intro w
        have := hprob w
        have hexp_w : Integrable (fun p : ℝ^(N + 1) × ℝ =>
            Real.exp (p.1 (Fin.last N) ^ 2 / K_last)) (G_aux s w) := by
          refine (hstate_last.2.1 w).mono' ((((PiLp.continuous_apply 2
            (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.comp
            measurable_fst).pow_const 2).div_const K_last).exp.aestronglyMeasurable
            (ae_of_all _ fun p => ?_)
          rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
          refine div_le_div_of_nonneg_right ?_ hK_last_pos.le
          have hcoord : |p.1 (Fin.last N)| ≤ ‖p.1‖ := by
            simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p.1 (Fin.last N)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hcoord 2
        obtain ⟨h4w, h4le_w⟩ := integral_last_spin_pow_two_mul_le_of_exp hK_last_pos hexp_w 2
        simp only [show (2 : ℕ).factorial = 2 by rfl, Nat.cast_ofNat,
          show 2 * 2 = 4 by rfl] at h4w h4le_w
        have hdom_w : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
            ((σ a).1 (Fin.last N) ^ 4 + (σ b).1 (Fin.last N) ^ 4) / 2)
            (Measure.pi fun _ : R_big => G_aux s w) :=
          (((measurePreserving_eval (fun _ : R_big => G_aux s w)
              a).integrable_comp_of_integrable h4w).add
            ((measurePreserving_eval (fun _ : R_big => G_aux s w)
              b).integrable_comp_of_integrable h4w)).div_const 2
        have hle_w : ∫ σ : R_big → ℝ^(N + 1) × ℝ,
            |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ^ 2
            ∂(Measure.pi fun _ : R_big => G_aux s w) ≤
            ∫ σ : R_big → ℝ^(N + 1) × ℝ,
              ((σ a).1 (Fin.last N) ^ 4 + (σ b).1 (Fin.last N) ^ 4) / 2
              ∂(Measure.pi fun _ : R_big => G_aux s w) := by
          refine integral_mono (hV2_2 w).integrable_sq hdom_w fun σ => ?_
          rw [sq_abs, mul_pow, le_div_iff₀ two_pos]
          have hsq := sq_nonneg ((σ a).1 (Fin.last N) ^ 2 - (σ b).1 (Fin.last N) ^ 2)
          have hid : ((σ a).1 (Fin.last N) ^ 2 - (σ b).1 (Fin.last N) ^ 2) ^ 2 =
              (σ a).1 (Fin.last N) ^ 4 + (σ b).1 (Fin.last N) ^ 4 -
                2 * ((σ a).1 (Fin.last N) ^ 2 * (σ b).1 (Fin.last N) ^ 2) := by ring
          linarith only [hsq, hid]
        have heq_dom : ∫ σ : R_big → ℝ^(N + 1) × ℝ,
            ((σ a).1 (Fin.last N) ^ 4 + (σ b).1 (Fin.last N) ^ 4) / 2
            ∂(Measure.pi fun _ : R_big => G_aux s w) =
            ∫ p : ℝ^(N + 1) × ℝ, p.1 (Fin.last N) ^ 4 ∂(G_aux s w) := by
          have ha4 : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ => (σ a).1 (Fin.last N) ^ 4)
              (Measure.pi fun _ : R_big => G_aux s w) :=
            (measurePreserving_eval (fun _ : R_big => G_aux s w)
              a).integrable_comp_of_integrable h4w
          have hb4 : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ => (σ b).1 (Fin.last N) ^ 4)
              (Measure.pi fun _ : R_big => G_aux s w) :=
            (measurePreserving_eval (fun _ : R_big => G_aux s w)
              b).integrable_comp_of_integrable h4w
          rw [integral_div, integral_add ha4 hb4,
            integral_pi_eval (G_aux s w) a (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ 4)
              h4w.aestronglyMeasurable,
            integral_pi_eval (G_aux s w) b (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ 4)
              h4w.aestronglyMeasurable]
          ring
        exact hle_w.trans (heq_dom.le.trans h4le_w)
      have hint : Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
          |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ^ 2
          ∂(Measure.pi fun _ : R_big => G_aux s w)) auxLaw[N, M, r] :=
        (hlast_i.const_mul (2 * K_last ^ 2)).mono' (hstate.2.2 _ hm_ε).aestronglyMeasurable
          (ae_of_all _ fun w => by
            rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
            exact hpt_w w)
      refine ⟨hint, ?_⟩
      calc ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
              |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| ^ 2
              ∂(Measure.pi fun _ : R_big => G_aux s w) ∂auxLaw[N, M, r]
          ≤ ∫ w, 2 * K_last ^ 2 * ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
              ∂(G_aux s w) ∂auxLaw[N, M, r] :=
            integral_mono hint (hlast_i.const_mul _) hpt_w
        _ = 2 * K_last ^ 2 * ∫ w, ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
              ∂(G_aux s w) ∂auxLaw[N, M, r] := integral_const_mul _ _
        _ ≤ 2 * K_last ^ 2 * K_last := mul_le_mul_of_nonneg_left hlast_le (by positivity)
        _ = 2 * K_last ^ 3 := by ring
    have hCS2 := abs_integral_integral_mul_le_of_integral_sq_le
      (P := auxLaw[N, M, r]) (μ := fun w => Measure.pi fun _ : R_big => G_aux s w)
      hU2 hV2_2 (hstate.2.2 _ hUV2_m).aestronglyMeasurable hg_sq_int hε4_i.1
      hA (Real.sqrt_nonneg (2 * K_last ^ 3)) hg_sq_le
      (by rw [Real.sq_sqrt (by positivity)]; exact hε4_i.2)
    -- Combine Part 1 and Part 2 via triangle inequality
    have hpt_split : ∀ w : AuxDis[N, M],
        (∫ σ : R_big → ℝ^(N + 1) × ℝ,
          |g (fun l => (σ (some (some l))).1)| *
            |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|
          ∂(Measure.pi fun _ : R_big => G_aux s w)) ≤
        (∫ σ : R_big → ℝ^(N + 1) × ℝ,
          |g (fun l => (σ (some (some l))).1)| * |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab|
          ∂(Measure.pi fun _ : R_big => G_aux s w)) +
        ((N : ℝ) + 1)⁻¹ * (∫ σ : R_big → ℝ^(N + 1) × ℝ,
          |g (fun l => (σ (some (some l))).1)| * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|
          ∂(Measure.pi fun _ : R_big => G_aux s w)) := fun w => by
      have hi1 : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |g (fun l => (σ (some (some l))).1)| * |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab|)
          (Measure.pi fun _ : R_big => G_aux s w) := (hU2 w).integrable_mul (hV1_2 w)
      have hi2 : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          ((N : ℝ) + 1)⁻¹ * (|g (fun l => (σ (some (some l))).1)| *
            |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|))
          (Measure.pi fun _ : R_big => G_aux s w) :=
        ((hU2 w).integrable_mul (hV2_2 w)).const_mul ((N : ℝ) + 1)⁻¹
      have hdom : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |g (fun l => (σ (some (some l))).1)| * |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| +
          ((N : ℝ) + 1)⁻¹ * (|g (fun l => (σ (some (some l))).1)| *
            |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|))
          (Measure.pi fun _ : R_big => G_aux s w) := hi1.add hi2
      have hle_pt : ∀ σ : R_big → ℝ^(N + 1) × ℝ,
          |g (fun l => (σ (some (some l))).1)| *
            |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab| ≤
          |g (fun l => (σ (some (some l))).1)| * |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| +
          ((N : ℝ) + 1)⁻¹ * (|g (fun l => (σ (some (some l))).1)| *
            |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|) := fun σ => by
        have hsub := abs_truncated_overlap_sub_full_le ht0 ht1 (σ a).1 (σ b).1
        have htri := abs_sub_le
          (((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
            t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))))
          (((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫) m_ab
        have hcomb : |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab| ≤
            |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| +
            ((N : ℝ) + 1)⁻¹ * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)| := by linarith
        calc |g (fun l => (σ (some (some l))).1)| *
              |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
                t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|
            ≤ |g (fun l => (σ (some (some l))).1)| *
              (|((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| +
                ((N : ℝ) + 1)⁻¹ * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|) :=
              mul_le_mul_of_nonneg_left hcomb (abs_nonneg _)
          _ = _ := by ring
      have hTi_w : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          |g (fun l => (σ (some (some l))).1)| *
            |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|)
          (Measure.pi fun _ : R_big => G_aux s w) := by
        refine hdom.mono' (hT_m.comp (measurable_prodMk_left (x := (0 : Fin (N + 1) ⊕ Unit → ℝ)))
          ).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        exact hle_pt σ
      calc ∫ σ, |g (fun l => (σ (some (some l))).1)| *
            |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|
            ∂(Measure.pi fun _ : R_big => G_aux s w)
          ≤ ∫ σ, (|g (fun l => (σ (some (some l))).1)| *
              |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab| +
              ((N : ℝ) + 1)⁻¹ * (|g (fun l => (σ (some (some l))).1)| *
                |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|))
              ∂(Measure.pi fun _ : R_big => G_aux s w) :=
            integral_mono hTi_w hdom hle_pt
        _ = _ := by rw [integral_add hi1 hi2, integral_const_mul]
    have hLHS_i : Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        |g (fun l => (σ (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
            t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|
        ∂(Measure.pi fun _ : R_big => G_aux s w)) auxLaw[N, M, r] :=
      (hCS1.1.add (hCS2.1.const_mul _)).mono'
        (hstate.2.2 _ (hT_m.comp (measurable_prodMk_left (x := (0 : Fin (N + 1) ⊕ Unit → ℝ))))
          ).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_of_nonneg
            (integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
          exact hpt_split w)
    have hcomb_int : ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
          |g (fun l => (σ (some (some l))).1)| *
            |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - m_ab|
          ∂(Measure.pi fun _ : R_big => G_aux s w) ∂auxLaw[N, M, r] ≤
        A * Real.sqrt (K_ov * (I_ab + ((N : ℝ) + 1)⁻¹ ^ 2)) +
        ((N : ℝ) + 1)⁻¹ * (A * Real.sqrt (2 * K_last ^ 3)) := by
      calc _ ≤ ∫ w, ((∫ σ : R_big → ℝ^(N + 1) × ℝ,
              |g (fun l => (σ (some (some l))).1)| * |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab|
              ∂(Measure.pi fun _ : R_big => G_aux s w)) +
            ((N : ℝ) + 1)⁻¹ * (∫ σ : R_big → ℝ^(N + 1) × ℝ,
              |g (fun l => (σ (some (some l))).1)| * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|
              ∂(Measure.pi fun _ : R_big => G_aux s w))) ∂auxLaw[N, M, r] :=
            integral_mono hLHS_i (hCS1.1.add (hCS2.1.const_mul _)) hpt_split
        _ = (∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
              |g (fun l => (σ (some (some l))).1)| * |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - m_ab|
              ∂(Measure.pi fun _ : R_big => G_aux s w) ∂auxLaw[N, M, r]) +
            ((N : ℝ) + 1)⁻¹ * (∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
              |g (fun l => (σ (some (some l))).1)| * |(σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)|
              ∂(Measure.pi fun _ : R_big => G_aux s w) ∂auxLaw[N, M, r]) := by
            rw [integral_add hCS1.1 (hCS2.1.const_mul _), integral_const_mul]
        _ ≤ A * Real.sqrt (K_ov * (I_ab + ((N : ℝ) + 1)⁻¹ ^ 2)) +
            ((N : ℝ) + 1)⁻¹ * (A * Real.sqrt (2 * K_last ^ 3)) :=
            add_le_add ((le_abs_self _).trans hCS1.2)
              (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hCS2.2) (by positivity))
    -- Bound `√(K_ov * (I_ab + (N+1)⁻²)) ≤ √K_ov * (√I_ab + (N+1)⁻¹)`
    have hsqrt_le : Real.sqrt (K_ov * (I_ab + ((N : ℝ) + 1)⁻¹ ^ 2)) ≤
        Real.sqrt K_ov * (Real.sqrt I_ab + ((N : ℝ) + 1)⁻¹) := by
      rw [Real.sqrt_mul hK_ov_pos.le]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      have hsq : I_ab + ((N : ℝ) + 1)⁻¹ ^ 2 ≤ (Real.sqrt I_ab + ((N : ℝ) + 1)⁻¹) ^ 2 := by
        rw [add_sq, Real.sq_sqrt hIab0]
        linarith [mul_nonneg (Real.sqrt_nonneg I_ab) (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹)]
      exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
    have hIab_le : Real.sqrt I_ab ≤ Real.sqrt I₂ + Real.sqrt I₁ := by
      dsimp only [I_ab]
      split
      · linarith [Real.sqrt_nonneg I₂]
      · linarith [Real.sqrt_nonneg I₁]
    refine hcomb_int.trans ?_
    have h1 : A * Real.sqrt (K_ov * (I_ab + ((N : ℝ) + 1)⁻¹ ^ 2)) ≤
        A * (Real.sqrt K_ov * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹)) :=
      mul_le_mul_of_nonneg_left (hsqrt_le.trans (mul_le_mul_of_nonneg_left
        (add_le_add hIab_le le_rfl) (Real.sqrt_nonneg _))) hA
    have h2 : Real.sqrt K_ov ≤ K_term := le_max_left _ _
    have h3 : Real.sqrt K_ov + Real.sqrt (2 * K_last ^ 3) ≤ K_term := le_max_right _ _
    have hinv0 : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹ := by positivity
    have hsq0 : 0 ≤ Real.sqrt I₂ + Real.sqrt I₁ := by positivity
    calc A * Real.sqrt (K_ov * (I_ab + ((N : ℝ) + 1)⁻¹ ^ 2)) +
          ((N : ℝ) + 1)⁻¹ * (A * Real.sqrt (2 * K_last ^ 3))
        ≤ A * (Real.sqrt K_ov * (Real.sqrt I₂ + Real.sqrt I₁) +
            (Real.sqrt K_ov + Real.sqrt (2 * K_last ^ 3)) * ((N : ℝ) + 1)⁻¹) := by linarith
      _ ≤ A * (K_term * (Real.sqrt I₂ + Real.sqrt I₁) + K_term * ((N : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_right h2 hsq0) (mul_le_mul_of_nonneg_right h3 hinv0)) hA
      _ = K_term * A * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹) := by ring
  -- Sum `hterm` over all `(a, b) : R_big × R_big`
  have hsum_le : (∑ a : R_big, ∑ b : R_big,
      ∫ d, ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        |g (fun l => (σ (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) -
            if a = b then ρ else q|
        ∂(Measure.pi fun _ : R_big => G_sh s d w) ∂γ ∂P) ≤
      ((n + 2 : ℝ) ^ 2) * (K_term * A * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹)) := by
    have hcard : (Fintype.card R_big : ℝ) = (n : ℝ) + 2 := by
      dsimp only [R_big, n]
      simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]
      ring
    calc _ ≤ ∑ _a : R_big, ∑ _b : R_big,
            K_term * A * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = ((n + 2 : ℝ) ^ 2) * (K_term * A * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          ring
  set B_pow : ℝ := (1 + |M₀| + |M₁| + |M₂| + |D| + |D|) ^ (n + 2)
  have hBp0 : 0 ≤ B_pow := by dsimp only [B_pow]; positivity
  have hK_le : ((n : ℝ) + 1) ^ 2 * ((n + 2 : ℝ) ^ 2) * K_term ≤ K := by
    dsimp only [K]; linarith
  calc ((n : ℝ) + 1) ^ 2 * B_pow * (∑ a : R_big, ∑ b : R_big,
          ∫ d, ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
            |g (fun l => (σ (some (some l))).1)| *
              |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
                  t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) -
                if a = b then ρ else q|
            ∂(Measure.pi fun _ : R_big => G_sh s d w) ∂γ ∂P)
      ≤ ((n : ℝ) + 1) ^ 2 * B_pow *
          (((n + 2 : ℝ) ^ 2) * (K_term * A * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹))) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = (((n : ℝ) + 1) ^ 2 * ((n + 2 : ℝ) ^ 2) * K_term) * A * B_pow *
          (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹) := by ring
    _ ≤ K * A * B_pow * (Real.sqrt I₂ + Real.sqrt I₁ + ((N : ℝ) + 1)⁻¹) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le hA) hBp0)
          (by positivity)

end Helpers

end SpinGlasses
