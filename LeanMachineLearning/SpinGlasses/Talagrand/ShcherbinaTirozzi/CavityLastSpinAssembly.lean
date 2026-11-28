/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityLastSpinDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.RSEquations

/-!
# The Shcherbina--Tirozzi model: Proposition 3.2.10 (assembly)

This file finishes the proof of **Talagrand, Proposition 3.2.10** (Eq. (3.107)): along the cavity
path `ν_t` on `ℝ^(N+1)` with `M + 1` constraints (`M + 1 ≤ 10 (N + 1)`) at the replica-symmetric
parameters `(r, r̄)` of Eq. (3.69) with `α = (M + 1) / (N + 1)` and `0 ≤ q ≤ ρ ≤ Q`, for
`f = ε₁²` (1 replica) or `f = ε₁ ε₂` (2 replicas),
```
|ν_t'(f)| ≤ K * (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)
```
where `K` depends only on `κ₀, h₀, D, Q, R, R_diff` (uniformly in `N, M, t`).

It uses the four-term cancellation of Proposition 3.2.1 (`CavityDerivative.lean`), the constraint
symmetry `integral_shcherbinaTirozziCavity_constraint_swap`, the endpoint comparison
`exists_abs_shcherbinaTirozziAuxCavity_one_sub_zero_le` (`CavityLastSpinDerivative.lean`), and
Lemma 3.2.7 (`AuxiliaryCavity.lean`).

## Main declarations

* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziCavity_sq_last_abs_le`: Proposition 3.2.10 for
  `f = ε₁²`.
* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziCavity_mul_last_abs_le`: Proposition 3.2.10 for
  `f = ε₁ ε₂`.
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

/-- **Four-term cancellation for a single observable `g` of `R_rep` replicas:**
for `l₁ ≠ l₂` in `R_rep`, if `|g|²` is bounded along `ν_{t,s}` by `A²`, then:
1. `|α ν_t(g * u'(S_last^{l₁}) * u'(S_last^{l₂})) - r_rs * ν_t(g)| ≤ K * A * E`
2. `|α ν_t(g * (u'' + u'²)(S_last^{l₁})) - rBar_rs * ν_t(g)| ≤ K * A * E`
where `E = √(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹`,
`α = (M + 1) / (N + 1)`, and `r_rs, rBar_rs` are the RS parameters (3.69) at `α`. -/
theorem exists_abs_shcherbinaTirozziCavity_constraint_sub_rs_le
    {R_rep : Type} [Fintype R_rep]
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ)
      {g : (R_rep → ℝ^(N + 1)) → ℝ} {C : ℝ} {m : ℕ} {A : ℝ} (l₁ l₂ : R_rep),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → (r : ℝ) ≤ R → (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      Differentiable ℝ (deriv (deriv u)) → Differentiable ℝ (deriv (deriv (deriv u))) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) → -D ≤ u 0 →
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
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r_rs : ℝ := α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar_rs : ℝ := α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      let Err : ℝ := Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
            (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => G_full d) ∂P_full) +
          Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
            (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full d) ∂P_full) +
          ((N : ℝ) + 1)⁻¹
      (∀ s ∈ Ioo (0 : ℝ) 1,
        Integrable (fun w => ∫ σ : R_rep → ℝ^(N + 1) × ℝ, g (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : R_rep => G_aux s w)) auxLaw[N, M, r] ∧
        ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ, g (fun l => (σ l).1) ^ 2
          ∂(Measure.pi fun _ : R_rep => G_aux s w) ∂auxLaw[N, M, r] ≤ A ^ 2) →
      (l₁ ≠ l₂ →
        |α * (∫ d, ∫ σ : R_rep → ℝ^(N + 1),
            g σ * (deriv u cfield[N, t, d.2.1, Fin.last M, σ l₁] *
              deriv u cfield[N, t, d.2.1, Fin.last M, σ l₂])
            ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full) -
          r_rs * (∫ d, ∫ σ : R_rep → ℝ^(N + 1), g σ
            ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full)| ≤ K * A * Err) ∧
      |α * (∫ d, ∫ σ : R_rep → ℝ^(N + 1),
          g σ * (deriv (deriv u) cfield[N, t, d.2.1, Fin.last M, σ l₁] +
            deriv u cfield[N, t, d.2.1, Fin.last M, σ l₁] ^ 2)
          ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full) -
        rBar_rs * (∫ d, ∫ σ : R_rep → ℝ^(N + 1), g σ
          ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full)| ≤ K * A * Err := by
  classical
  obtain ⟨K₀, hK₀_pos, hcomp⟩ :=
    exists_abs_shcherbinaTirozziAuxCavity_one_sub_zero_le (R_rep := R_rep)
      κ₀ h₀ D Q R R_diff hκ₀ hQ hR hR_diff
  set n : ℕ := Fintype.card R_rep
  set B₁ : ℝ := (1 + (1 + |D|) + |D| + |D| + |D| + |D|) ^ (n + 2)
  set B₂ : ℝ := (1 + (|D| + D ^ 2 + 1) + (|D| + 2 * D ^ 2) + (|D| + 2 * D ^ 2 + 2 * D ^ 2) +
    |D| + |D|) ^ (n + 2)
  set B₀ : ℝ := (1 + 1 + 0 + 0 + |D| + |D|) ^ (n + 2)
  set K : ℝ := K₀ * (11 * max B₁ B₂ + 11 * (|D| + D ^ 2) * B₀) + 1
  have hK_pos : 0 < K := by dsimp only [K, B₁, B₂, B₀]; positivity
  refine ⟨K, hK_pos, fun N M κ h t q ρ rBar r u g C m A l₁ l₂ hκ hh ht0 ht1 hq0 hqρ hρQ
    hrr hrR hrr_diff hM huc hu0 hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD hg hgb hA => ?_⟩
  intro P_full E_old S_v G_aux G_full α c Z V W r_rs rBar_rs Err hg2_all
  have hum : Measurable u := hu1.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα11 : α ≤ 11 := by
    dsimp only [α]
    rw [div_le_iff₀ (by positivity)]
    have hM' : (M : ℝ) ≤ 10 * ((N : ℝ) + 1) := by exact_mod_cast hM
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hErr0 : 0 ≤ Err := by dsimp only [Err]; positivity
  -- Bounds on `|r_rs|` and `|rBar_rs|`
  obtain ⟨hr0, hrD, hrr_rs, hrBar_low⟩ :=
    shcherbinaTirozzi_rsParameters_bounds huc hu0 hu1 hu2 hD1 hD2 hα0 q c
  have habs_r : |r_rs| ≤ 11 * (|D| + D ^ 2) := by
    rw [abs_of_nonneg hr0]
    have h1 : r_rs ≤ 11 * D ^ 2 :=
      hrD.trans (mul_le_mul_of_nonneg_right hα11 (sq_nonneg D))
    nlinarith [abs_nonneg D]
  have habs_rBar : |rBar_rs| ≤ 11 * (|D| + D ^ 2) := by
    rw [abs_le]
    have h1 : rBar_rs ≤ 11 * D ^ 2 :=
      hrr_rs.trans (hrD.trans (mul_le_mul_of_nonneg_right hα11 (sq_nonneg D)))
    have h2 : -(11 * (D + D ^ 2)) ≤ rBar_rs :=
      (neg_le_neg (mul_le_mul_of_nonneg_right hα11 (by positivity))).trans hrBar_low
    have hD_le : D ≤ |D| := le_abs_self D
    constructor <;> nlinarith [abs_nonneg D]
  -- Step 1: Compare `ν_{t,1}(g) = ν_t(g)` with `ν_{t,0}(g) = ν_{t,~}(g)` via `ψ = 1`
  have hcmp0 := hcomp N M κ h t q ρ rBar r u (fun _ _ => (1 : ℝ)) (M₀ := 1) (M₁ := 0) (M₂ := 0)
    hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD1 hD2 huD
    (fun _ => differentiable_const 1) (fun _ => by simp)
    (fun _ _ => by norm_num) (fun _ _ => by simp) (fun _ _ => by simp)
    hg hgb hA hg2_all
  simp only [Finset.prod_const_one, mul_one, abs_one, abs_zero] at hcmp0
  rw [integral_pi_shcherbinaTirozziAuxCavity_one κ h r rBar t q ρ u g,
    integral_shcherbinaTirozziAuxCavity_zero κ h r rBar t q ρ hum hu0 g] at hcmp0
  -- Helper: `ν_{t,1}(g * ∏ ψ_l(S_1^l))` equals `ν_t(g * ∏ ψ_l(S_last^l))`
  have hone_eq : ∀ ψ : R_rep → ℝ → ℝ,
      (∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          g (fun l => (σ l).1) * ∏ l, ψ l (S_v 1 w (σ l))
          ∂(Measure.pi fun _ : R_rep => G_aux 1 w) ∂auxLaw[N, M, r]) =
      ∫ d, ∫ σ : R_rep → ℝ^(N + 1),
          g σ * ∏ l, ψ l cfield[N, t, d.2.1, Fin.last M, σ l]
          ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full := by
    intro ψ
    -- At `v = 1`, `S_v 1 w p = cfield[N, t, w.1.2.1, Fin.last M, p.1]` (independent of `p.2, w.2`)
    have hS1 : ∀ (w : AuxDis[N, M]) (p : ℝ^(N + 1) × ℝ),
        S_v 1 w p = cfield[N, t, w.1.2.1, Fin.last M, p.1] := fun w p => by
      dsimp only [S_v]; simp
    have hG1 : ∀ (w : AuxDis[N, M]),
        (fun p : ℝ^(N + 1) × ℝ => E_old w p.1 + u (S_v 1 w p)) =
        fun p => (-shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u w.1.2.1 w.1.2.2 p.1) +
          (0 : ℝ → ℝ) p.2 := fun w => funext fun p => by
      rw [hS1]; dsimp only [E_old]
      rw [neg_shcherbinaTirozziCavityHamiltonian_succ]
      simp only [Pi.zero_apply, add_zero]
    have hpt : ∀ w : AuxDis[N, M],
        (∫ σ : R_rep → ℝ^(N + 1) × ℝ, g (fun l => (σ l).1) * ∏ l, ψ l (S_v 1 w (σ l))
          ∂(Measure.pi fun _ : R_rep => G_aux 1 w)) =
        ∫ a : R_rep → ℝ^(N + 1), g a * ∏ l, ψ l cfield[N, t, w.1.2.1, Fin.last M, a l]
          ∂(Measure.pi fun _ : R_rep => G_full w.1) := fun w => by
      dsimp only [G_aux]
      rw [hG1]
      simp_rw [hS1]
      have h := integral_pi_tilted_prod_add_mul (μ := (volume : Measure (ℝ^(N + 1))))
        (ν := gaussianReal 0 1) (ι := R_rep)
        (fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u w.1.2.1 w.1.2.2 σ)
        (0 : ℝ → ℝ)
        (fun a : R_rep → ℝ^(N + 1) => g a * ∏ l, ψ l cfield[N, t, w.1.2.1, Fin.last M, a l])
        (fun _ => 1)
      simpa using h
    refine Eq.trans (integral_congr_ae (ae_of_all _ hpt)) ?_
    refine Eq.trans (integral_fun_fst (ν := gaussianReal 0 1)
      (fun d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
        ∫ a : R_rep → ℝ^(N + 1), g a * ∏ l, ψ l cfield[N, t, d.2.1, Fin.last M, a l]
          ∂(Measure.pi fun _ : R_rep => G_full d))) ?_
    rw [probReal_univ, one_smul]
  constructor
  · -- Part 1: `u'(S^{l₁}) u'(S^{l₂})` with `l₁ ≠ l₂`
    intro hne
    set ψ₁ : R_rep → ℝ → ℝ := fun l x => if l = l₁ ∨ l = l₂ then deriv u x else 1
    have hψ₁d : ∀ l, Differentiable ℝ (ψ₁ l) := fun l => by
      dsimp only [ψ₁]; split_ifs
      · exact hu2
      · exact differentiable_const 1
    have hψ₁₂d : ∀ l, Differentiable ℝ (deriv (ψ₁ l)) := fun l => by
      dsimp only [ψ₁]; split_ifs
      · exact hu3
      · simp
    have hψ₁_0 : ∀ l x, |ψ₁ l x| ≤ 1 + |D| := fun l x => by
      dsimp only [ψ₁]; split_ifs
      · exact (hD1 x).trans ((le_abs_self D).trans (by linarith))
      · rw [abs_one]; linarith [abs_nonneg D]
    have hψ₁_1 : ∀ l x, |deriv (ψ₁ l) x| ≤ |D| := fun l x => by
      dsimp only [ψ₁]; split_ifs
      · exact (hD2 x).trans (le_abs_self D)
      · simp
    have hψ₁_2 : ∀ l x, |deriv (deriv (ψ₁ l)) x| ≤ |D| := fun l x => by
      dsimp only [ψ₁]; split_ifs
      · exact (hD3 x).trans (le_abs_self D)
      · simp
    have hprod₁ : ∀ (v : R_rep → ℝ),
        (∏ l : R_rep, ψ₁ l (v l)) = deriv u (v l₁) * deriv u (v l₂) := fun v => by
      have hsub : ({l₁, l₂} : Finset R_rep) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.prod_sdiff hsub, Finset.prod_pair hne]
      have hrest : ∏ l ∈ Finset.univ \ ({l₁, l₂} : Finset R_rep), ψ₁ l (v l) = 1 :=
        Finset.prod_eq_one fun l hl => by
          rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hl
          dsimp only [ψ₁]; rw [ite_eq_right hl.2]
      rw [hrest, one_mul]
      dsimp only [ψ₁]; simp
    have hcmp1 := hcomp N M κ h t q ρ rBar r u ψ₁ (M₀ := 1 + |D|) (M₁ := |D|) (M₂ := |D|)
      hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD1 hD2 huD
      hψ₁d hψ₁₂d hψ₁_0 hψ₁_1 hψ₁_2 hg hgb hA hg2_all
    rw [hone_eq ψ₁] at hcmp1
    simp_rw [hprod₁] at hcmp1
    -- Identify `α * ν_{t,0}` via Lemma 3.2.7 (Eq. (3.93))
    have h0_eq := integral_shcherbinaTirozziAuxCavity_zero_deriv_mul (N := N) (M := M)
      (R := R_rep) α κ h r rBar t q ρ hum hu0 hne g
    have h0_comm : (∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          g (fun l => (σ l).1) * (deriv u (S_v 0 w (σ l₁)) * deriv u (S_v 0 w (σ l₂)))
          ∂(Measure.pi fun _ : R_rep => G_aux 0 w) ∂auxLaw[N, M, r]) =
        ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          (deriv u (S_v 0 w (σ l₁)) * deriv u (S_v 0 w (σ l₂))) * g (fun l => (σ l).1)
          ∂(Measure.pi fun _ : R_rep => G_aux 0 w) ∂auxLaw[N, M, r] :=
      integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => mul_comm _ _))
    rw [h0_comm] at hcmp1
    -- Combine via triangle inequality: `|α A₁ - r_rs G₁| ≤ α |A₁ - A₀| + |r_rs| |G₁ - G₀|`
    set A₁ : ℝ := ∫ d, ∫ σ : R_rep → ℝ^(N + 1),
      g σ * (deriv u cfield[N, t, d.2.1, Fin.last M, σ l₁] *
        deriv u cfield[N, t, d.2.1, Fin.last M, σ l₂])
      ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full
    set A₀ : ℝ := ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
      (deriv u (S_v 0 w (σ l₁)) * deriv u (S_v 0 w (σ l₂))) * g (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R_rep => G_aux 0 w) ∂auxLaw[N, M, r]
    set G₁ : ℝ := ∫ d, ∫ σ : R_rep → ℝ^(N + 1), g σ
      ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full
    set G₀ : ℝ := ∫ d₀, ∫ a : R_rep → ℝ^(N + 1), g a
      ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d₀.1 u d₀.2.1 d₀.2.2 σ)
      ∂((gaussianReal 0 r).prod
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    have h0_id : α * A₀ = r_rs * G₀ := h0_eq
    have htri : |α * A₁ - r_rs * G₁| ≤ α * |A₁ - A₀| + |r_rs| * |G₁ - G₀| := by
      have hid : α * A₁ - r_rs * G₁ = α * (A₁ - A₀) + r_rs * (G₀ - G₁) := by linarith [h0_id]
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_sub_comm G₀ G₁]
    have hB1_eq : (1 + |(1 + |D|)| + |(|D|)| + |(|D|)| + |D| + |D|) ^ (n + 2) = B₁ := by
      simp only [abs_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |D|), B₁]
    rw [hB1_eq] at hcmp1
    have h1 : α * |A₁ - A₀| ≤ 11 * (K₀ * A * B₁ * Err) :=
      mul_le_mul hα11 hcmp1 (abs_nonneg _) (by positivity)
    have h2 : |r_rs| * |G₁ - G₀| ≤ (11 * (|D| + D ^ 2)) * (K₀ * A * B₀ * Err) :=
      mul_le_mul habs_r hcmp0 (abs_nonneg _) (by positivity)
    have h3 : B₁ ≤ max B₁ B₂ := le_max_left _ _
    have h4 : K₀ * (11 * B₁ + 11 * (|D| + D ^ 2) * B₀) ≤ K := by
      dsimp only [K]
      have h11 : 11 * B₁ ≤ 11 * max B₁ B₂ := mul_le_mul_of_nonneg_left h3 (by norm_num)
      have hm := mul_le_mul_of_nonneg_left (add_le_add h11 (le_refl (11 * (|D| + D ^ 2) * B₀)))
        hK₀_pos.le
      linarith only [hm]
    calc |α * A₁ - r_rs * G₁|
        ≤ 11 * (K₀ * A * B₁ * Err) + (11 * (|D| + D ^ 2)) * (K₀ * A * B₀ * Err) :=
          htri.trans (add_le_add h1 h2)
      _ = K₀ * (11 * B₁ + 11 * (|D| + D ^ 2) * B₀) * A * Err := by ring
      _ ≤ K * A * Err :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hA) hErr0
  · -- Part 2: `(u'' + u'²)(S^{l₁})`
    set φ₂ : ℝ → ℝ := fun x => deriv (deriv u) x + deriv u x ^ 2
    have hφ₂d : Differentiable ℝ φ₂ := hu3.add (hu2.pow 2)
    have hφ₂_deriv : ∀ x, HasDerivAt φ₂
        (deriv (deriv (deriv u)) x + 2 * deriv u x * deriv (deriv u) x) x := fun x => by
      have h1 := (hu3 x).hasDerivAt
      have h2 := ((hu2 x).hasDerivAt).pow 2
      refine (h1.add h2).congr_deriv ?_
      ring
    have hφ₂_deriv_eq : deriv φ₂ = fun x =>
        deriv (deriv (deriv u)) x + 2 * deriv u x * deriv (deriv u) x :=
      funext fun x => (hφ₂_deriv x).deriv
    have hφ₂₂d : Differentiable ℝ (deriv φ₂) := by
      rw [hφ₂_deriv_eq]
      exact hu4.add ((hu2.const_mul 2).mul hu3)
    have hφ₂_deriv2 : ∀ x, HasDerivAt (deriv φ₂)
        (deriv (deriv (deriv (deriv u))) x +
          2 * (deriv (deriv u) x ^ 2 + deriv u x * deriv (deriv (deriv u)) x)) x := fun x => by
      rw [hφ₂_deriv_eq]
      have h1 := (hu4 x).hasDerivAt
      have h2 := (((hu2 x).hasDerivAt).const_mul 2).mul (hu3 x).hasDerivAt
      refine (h1.add h2).congr_deriv ?_
      ring
    have hφ₂_deriv2_eq : ∀ x, deriv (deriv φ₂) x =
        deriv (deriv (deriv (deriv u))) x +
          2 * (deriv (deriv u) x ^ 2 + deriv u x * deriv (deriv (deriv u)) x) :=
      fun x => (hφ₂_deriv2 x).deriv
    set ψ₂ : R_rep → ℝ → ℝ := fun l x => if l = l₁ then φ₂ x else 1
    have hψ₂d : ∀ l, Differentiable ℝ (ψ₂ l) := fun l => by
      dsimp only [ψ₂]; split_ifs
      · exact hφ₂d
      · exact differentiable_const 1
    have hψ₂₂d : ∀ l, Differentiable ℝ (deriv (ψ₂ l)) := fun l => by
      dsimp only [ψ₂]; split_ifs
      · exact hφ₂₂d
      · simp
    have hψ₂_0 : ∀ l x, |ψ₂ l x| ≤ |D| + D ^ 2 + 1 := fun l x => by
      dsimp only [ψ₂]; split_ifs
      · dsimp only [φ₂]
        have h1 : |deriv (deriv u) x| ≤ |D| := (hD2 x).trans (le_abs_self D)
        have h2 : |deriv u x ^ 2| ≤ D ^ 2 := by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hD1 x) 2
        linarith [abs_add_le (deriv (deriv u) x) (deriv u x ^ 2)]
      · rw [abs_one]; linarith [abs_nonneg D, sq_nonneg D]
    have hψ₂_1 : ∀ l x, |deriv (ψ₂ l) x| ≤ |D| + 2 * D ^ 2 := fun l x => by
      dsimp only [ψ₂]; split_ifs
      · rw [hφ₂_deriv_eq]
        have h1 : |deriv (deriv (deriv u)) x| ≤ |D| := (hD3 x).trans (le_abs_self D)
        have h2 : |2 * deriv u x * deriv (deriv u) x| ≤ 2 * D ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg zero_le_two, sq, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hD1 x) (hD2 x) (abs_nonneg _) hD0)
            zero_le_two
        linarith [abs_add_le (deriv (deriv (deriv u)) x) (2 * deriv u x * deriv (deriv u) x)]
      · simp only [deriv_const', abs_zero]; positivity
    have hψ₂_2 : ∀ l x, |deriv (deriv (ψ₂ l)) x| ≤ |D| + 2 * D ^ 2 + 2 * D ^ 2 := fun l x => by
      dsimp only [ψ₂]; split_ifs
      · rw [hφ₂_deriv2_eq x]
        have h1 : |deriv (deriv (deriv (deriv u))) x| ≤ |D| := (hD4 x).trans (le_abs_self D)
        have h2 : |deriv (deriv u) x ^ 2| ≤ D ^ 2 := by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hD2 x) 2
        have h3 : |deriv u x * deriv (deriv (deriv u)) x| ≤ D ^ 2 := by
          rw [abs_mul, sq]; exact mul_le_mul (hD1 x) (hD3 x) (abs_nonneg _) hD0
        have h4 := abs_add_le (deriv (deriv (deriv (deriv u))) x)
          (2 * (deriv (deriv u) x ^ 2 + deriv u x * deriv (deriv (deriv u)) x))
        rw [abs_mul (2 : ℝ), abs_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)] at h4
        have h5 := abs_add_le (deriv (deriv u) x ^ 2) (deriv u x * deriv (deriv (deriv u)) x)
        linarith
      · simp only [deriv_const', abs_zero]; positivity
    have hprod₂ : ∀ (v : R_rep → ℝ), (∏ l : R_rep, ψ₂ l (v l)) = φ₂ (v l₁) := fun v => by
      have hsub : ({l₁} : Finset R_rep) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.prod_sdiff hsub, Finset.prod_singleton]
      have hrest : ∏ l ∈ Finset.univ \ ({l₁} : Finset R_rep), ψ₂ l (v l) = 1 :=
        Finset.prod_eq_one fun l hl => by
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hl
          dsimp only [ψ₂]; rw [ite_eq_right hl.2]
      rw [hrest, one_mul]
      dsimp only [ψ₂]; simp
    have hcmp2 := hcomp N M κ h t q ρ rBar r u ψ₂
      (M₀ := |D| + D ^ 2 + 1) (M₁ := |D| + 2 * D ^ 2) (M₂ := |D| + 2 * D ^ 2 + 2 * D ^ 2)
      hκ hh ht0 ht1 hq0 hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD1 hD2 huD
      hψ₂d hψ₂₂d hψ₂_0 hψ₂_1 hψ₂_2 hg hgb hA hg2_all
    rw [hone_eq ψ₂] at hcmp2
    simp_rw [hprod₂] at hcmp2
    -- Identify `α * ν_{t,0}` via Lemma 3.2.7 (Eq. (3.94))
    have h0_eq := integral_shcherbinaTirozziAuxCavity_zero_deriv_two (N := N) (M := M)
      (R := R_rep) α κ h r rBar t q ρ hum hu0 l₁ g
    have h0_comm : (∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          g (fun l => (σ l).1) * φ₂ (S_v 0 w (σ l₁))
          ∂(Measure.pi fun _ : R_rep => G_aux 0 w) ∂auxLaw[N, M, r]) =
        ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
          φ₂ (S_v 0 w (σ l₁)) * g (fun l => (σ l).1)
          ∂(Measure.pi fun _ : R_rep => G_aux 0 w) ∂auxLaw[N, M, r] :=
      integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => mul_comm _ _))
    rw [h0_comm] at hcmp2
    set A₁ : ℝ := ∫ d, ∫ σ : R_rep → ℝ^(N + 1),
      g σ * φ₂ cfield[N, t, d.2.1, Fin.last M, σ l₁]
      ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full
    set A₀ : ℝ := ∫ w, ∫ σ : R_rep → ℝ^(N + 1) × ℝ,
      φ₂ (S_v 0 w (σ l₁)) * g (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R_rep => G_aux 0 w) ∂auxLaw[N, M, r]
    set G₁ : ℝ := ∫ d, ∫ σ : R_rep → ℝ^(N + 1), g σ
      ∂(Measure.pi fun _ : R_rep => G_full d) ∂P_full
    set G₀ : ℝ := ∫ d₀, ∫ a : R_rep → ℝ^(N + 1), g a
      ∂(Measure.pi fun _ : R_rep => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d₀.1 u d₀.2.1 d₀.2.2 σ)
      ∂((gaussianReal 0 r).prod
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    have h0_id : α * A₀ = rBar_rs * G₀ := h0_eq
    have htri : |α * A₁ - rBar_rs * G₁| ≤ α * |A₁ - A₀| + |rBar_rs| * |G₁ - G₀| := by
      have hid : α * A₁ - rBar_rs * G₁ = α * (A₁ - A₀) + rBar_rs * (G₀ - G₁) := by linarith [h0_id]
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_sub_comm G₀ G₁]
    have hB2_eq : (1 + |(|D| + D ^ 2 + 1)| + |(|D| + 2 * D ^ 2)| +
        |(|D| + 2 * D ^ 2 + 2 * D ^ 2)| + |D| + |D|) ^ (n + 2) = B₂ := by
      simp only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |D| + D ^ 2 + 1),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ |D| + 2 * D ^ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ |D| + 2 * D ^ 2 + 2 * D ^ 2), B₂]
    rw [hB2_eq] at hcmp2
    have h1 : α * |A₁ - A₀| ≤ 11 * (K₀ * A * B₂ * Err) :=
      mul_le_mul hα11 hcmp2 (abs_nonneg _) (by positivity)
    have h2 : |rBar_rs| * |G₁ - G₀| ≤ (11 * (|D| + D ^ 2)) * (K₀ * A * B₀ * Err) :=
      mul_le_mul habs_rBar hcmp0 (abs_nonneg _) (by positivity)
    have h3 : B₂ ≤ max B₁ B₂ := le_max_right _ _
    have h4 : K₀ * (11 * B₂ + 11 * (|D| + D ^ 2) * B₀) ≤ K := by
      dsimp only [K]
      have h11 : 11 * B₂ ≤ 11 * max B₁ B₂ := mul_le_mul_of_nonneg_left h3 (by norm_num)
      have hm := mul_le_mul_of_nonneg_left (add_le_add h11 (le_refl (11 * (|D| + D ^ 2) * B₀)))
        hK₀_pos.le
      linarith only [hm]
    calc |α * A₁ - rBar_rs * G₁|
        ≤ 11 * (K₀ * A * B₂ * Err) + (11 * (|D| + D ^ 2)) * (K₀ * A * B₀ * Err) :=
          htri.trans (add_le_add h1 h2)
      _ = K₀ * (11 * B₂ + 11 * (|D| + D ^ 2) * B₀) * A * Err := by ring
      _ ≤ K * A * Err :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hA) hErr0

/-- **General Proposition 3.2.10 for any `f : (R_rep → ℝ^(N+1)) → ℝ`** whose products with
`ε_a ε_b` have bounded `L²` norm along `ν_{t,s}`: along the cavity path `ν_t` at the RS parameters
`(r, r̄)` of Eq. (3.69) with `α = (M + 1) / (N + 1)`,
`|ν_t'(f)| ≤ K * A * (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)`.

Specializing to `f = ε₁²` (`R_rep = Fin 1`) and `f = ε₁ ε₂` (`R_rep = Fin 2`) gives
Talagrand's Proposition 3.2.10 (Eq. (3.107)). -/
theorem exists_hasDerivAt_shcherbinaTirozziCavity_abs_le_of_mul_last_sq_le
    {R_rep : Type} [Fintype R_rep] [LinearOrder R_rep]
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ : ℝ) (u : ℝ → ℝ)
      {f : (R_rep → ℝ^(N + 1)) → ℝ} {C : ℝ} {m : ℕ} {A : ℝ},
      κ₀ ≤ κ → |h| ≤ h₀ → 0 < t → t < 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      M ≤ 10 * (N + 1) → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      Differentiable ℝ (deriv (deriv u)) → Differentiable ℝ (deriv (deriv (deriv u))) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) → -D ≤ u 0 →
      Measurable f → (∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) → 0 ≤ A →
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      r ≤ R → r - rBar ≤ R_diff →
      let P_full := ((gaussianReal 0 r.toNNReal).prod
        ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
      let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let S_v (s : ℝ) : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
        Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
          Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
      let G_aux (s : ℝ) : AuxDis[N, M] → Measure (ℝ^(N + 1) × ℝ) := fun w =>
        ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
          fun p => E_old w p.1 + u (S_v s w p)
      let G_full (s : ℝ) (d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :
          Measure (ℝ^(N + 1)) :=
        (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar s d.1 u d.2.1 d.2.2 σ
      (∀ (o : Option R_rep) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
        Integrable (fun w => ∫ σ : Option R_rep → ℝ^(N + 1) × ℝ,
            (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_aux s w)) auxLaw[N, M, r.toNNReal] ∧
          ∫ w, ∫ σ : Option R_rep → ℝ^(N + 1) × ℝ,
            (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_aux s w) ∂auxLaw[N, M, r.toNNReal] ≤ A ^ 2) →
      (∀ (a b : Option (Option R_rep)) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
        Integrable (fun w => ∫ σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ,
            (f (fun l => (σ (some (some l))).1) *
              ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2
            ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux s w)) auxLaw[N, M, r.toNNReal] ∧
          ∫ w, ∫ σ : Option (Option R_rep) → ℝ^(N + 1) × ℝ,
            (f (fun l => (σ (some (some l))).1) *
              ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2
            ∂(Measure.pi fun _ : Option (Option R_rep) => G_aux s w)
            ∂auxLaw[N, M, r.toNNReal] ≤ A ^ 2) →
      ∃ D_val : ℝ, HasDerivAt
          (fun s => ∫ d, ∫ σ : R_rep → ℝ^(N + 1), f σ
            ∂(Measure.pi fun _ : R_rep => G_full s d) ∂P_full) D_val t ∧
        |D_val| ≤ K * A *
          (Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => G_full t d) ∂P_full) +
            Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full t d) ∂P_full) +
            ((N : ℝ) + 1)⁻¹) := by
  obtain ⟨K₁, hK₁_pos, hcancel1⟩ :=
    exists_abs_shcherbinaTirozziCavity_constraint_sub_rs_le (R_rep := Option R_rep)
      κ₀ h₀ D Q R R_diff hκ₀ hQ hR hR_diff
  obtain ⟨K₂, hK₂_pos, hcancel2⟩ :=
    exists_abs_shcherbinaTirozziCavity_constraint_sub_rs_le (R_rep := Option (Option R_rep))
      κ₀ h₀ D Q R R_diff hκ₀ hQ hR hR_diff
  set n : ℕ := Fintype.card R_rep
  set K : ℝ := ((n : ℝ) + 1) * K₁ + (3 * ((n : ℝ) + 1) ^ 2) * K₂ + 1
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, fun N M κ h t q ρ u f C m A hκ hh ht0 ht1 hq0 hqρ hρQ hM huc hu0 hu1 hu2
    hu3 hu4 hD1 hD2 hD3 hD4 huD hf hfb hA => ?_⟩
  intro α c Z V W r rBar hrR hrr_diff P_full E_old S_v G_aux G_full hA1 hA2
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hC0 : 0 ≤ C := by
    have h0 := (abs_nonneg (f 0)).trans (hfb 0)
    have hprod : (0 : ℝ) < ∏ _l : R_rep, (1 + ‖(0 : ℝ^(N + 1))‖) ^ m := by simp
    exact nonneg_of_mul_nonneg_left h0 hprod
  obtain ⟨hr0, -, hrr, -⟩ :=
    shcherbinaTirozzi_rsParameters_bounds huc hu0 hu1 hu2 hD1 hD2 hα0 q c
  have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have hrr' : rBar ≤ (r.toNNReal : ℝ) := by rw [hr_coe]; exact hrr
  have hrR' : (r.toNNReal : ℝ) ≤ R := by rw [hr_coe]; exact hrR
  have hrr_diff' : (r.toNNReal : ℝ) - rBar ≤ R_diff := by rw [hr_coe]; exact hrr_diff
  -- Step 1: Differentiate via Proposition 3.2.1
  obtain ⟨hIV, hIU, hIPε, hIDε, hderiv⟩ :=
    hasDerivAt_integral_integral_pi_shcherbinaTirozziCavity (N := N) (M := M + 1) (R := R_rep)
      (h := h) hκ0 r.toNNReal hrr' hu0 hu1 hu2 hD1 hD2 ht0 ht1 hf hfb
  refine ⟨_, hderiv, ?_⟩
  let Dis := ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))
  set U : Fin (M + 1) → Dis → ℝ^(N + 1) → ℝ := fun k d σ =>
    deriv u cfield[N, t, d.2.1, k, σ] * σ (Fin.last N)
  set V_k : Fin (M + 1) → Dis → ℝ^(N + 1) → ℝ := fun k d σ =>
    (deriv (deriv u) cfield[N, t, d.2.1, k, σ] + deriv u cfield[N, t, d.2.1, k, σ] ^ 2) *
      σ (Fin.last N) ^ 2
  -- Integrability of each replica term under `G_full t d` and `P_full`
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hconf : ∀ (d : Dis) (x : ℝ^(N + 1)),
      -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t d.1 u d.2.1 d.2.2 x ≤
        0 + (|h| * ∑ i, |d.2.2 i| + |d.1|) * ‖x‖ - κ * ‖x‖ ^ 2 := fun d x => by
    rw [zero_add]
    exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr' ht0.le ht1.le hu0 d.2.1 d.2.2 x
  have hem : ∀ d : Dis, Measurable fun x : ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t d.1 u d.2.1 d.2.2 x := fun d =>
    (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r.toNNReal rBar t d.1 hum
      d.2.1 d.2.2).neg
  have hε_m : Measurable fun x : ℝ^(N + 1) => x (Fin.last N) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable
  have hε_b : ∀ x : ℝ^(N + 1), |x (Fin.last N)| ≤ 1 * (1 + ‖x‖) ^ 1 := fun x => by
    rw [one_mul, pow_one]
    exact (show |x (Fin.last N)| ≤ ‖x‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (Fin.last N)).trans (by linarith)
  have hε2_b : ∀ x : ℝ^(N + 1), |x (Fin.last N) ^ 2| ≤ 1 * (1 + ‖x‖) ^ 2 := fun x => by
    rw [one_mul, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((show |x (Fin.last N)| ≤ ‖x‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (Fin.last N)).trans (by linarith))
      2
  have hUm : ∀ k d, Measurable (U k d) := fun k d => by
    have hfm : Measurable fun x : ℝ^(N + 1) => cfield[N, t, d.2.1, k, x] :=
      (((Finset.measurable_sum _ fun i _ =>
        ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i.castSucc).measurable).const_mul
          _).add ((hε_m.const_mul _).const_mul _)).const_mul _)
    exact ((measurable_deriv u).comp hfm).mul hε_m
  have hUb : ∀ k d x, |U k d x| ≤ D * (1 + ‖x‖) ^ 1 := fun k d x => by
    dsimp only [U]
    rw [abs_mul]
    have h1 := hε_b x; rw [one_mul] at h1
    exact mul_le_mul (hD1 _) h1 (abs_nonneg _) hD0
  have hVm : ∀ k d, Measurable (V_k k d) := fun k d => by
    have hfm : Measurable fun x : ℝ^(N + 1) => cfield[N, t, d.2.1, k, x] :=
      (((Finset.measurable_sum _ fun i _ =>
        ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i.castSucc).measurable).const_mul
          _).add ((hε_m.const_mul _).const_mul _)).const_mul _)
    exact (((measurable_deriv (deriv u)).comp hfm).add
      (((measurable_deriv u).comp hfm).pow_const 2)).mul (hε_m.pow_const 2)
  have hVb : ∀ k d x, |V_k k d x| ≤ (D + D ^ 2) * (1 + ‖x‖) ^ 2 := fun k d x => by
    dsimp only [V_k]
    rw [abs_mul]
    have h1 : |deriv (deriv u) cfield[N, t, d.2.1, k, x] +
        deriv u cfield[N, t, d.2.1, k, x] ^ 2| ≤ D + D ^ 2 :=
      abs_deriv_deriv_add_sq_deriv_le hD1 hD2 _
    have h2 := hε2_b x; rw [one_mul] at h2
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  -- Helper: integrability over `P_full` of any polynomially bounded `R'`-replica observable
  have hP_int : ∀ {R' : Type} [Fintype R'] (Φ : Dis → (R' → ℝ^(N + 1)) → ℝ)
      (C' : ℝ) (m' : ℕ),
      (Measurable fun q : Dis × (R' → ℝ^(N + 1)) => Φ q.1 q.2) →
      (∀ d σ, |Φ d σ| ≤ C' * ∏ l, (1 + ‖σ l‖) ^ m') →
      Integrable (fun d => ∫ σ : R' → ℝ^(N + 1), Φ d σ
        ∂(Measure.pi fun _ : R' => G_full t d)) P_full := by
    intro R' _ Φ C' m' hΦm hΦb
    exact integrable_integral_pi_shcherbinaTirozziCavity hκ0 r.toNNReal hrr'
      ⟨ht0.le, ht1.le⟩ hu0 hu1 hD1 hΦb hΦm
  have hswap_V : ∀ k : Fin (M + 1),
      (∫ d, replicaDiff (G_full t d) f (V_k k d) ∂P_full) =
      ∫ d, replicaDiff (G_full t d) f (V_k (Fin.last M) d) ∂P_full := fun k => by
    have hrew : ∀ j : Fin (M + 1), ∀ d,
        replicaDiff (G_full t d) f (V_k j d) =
        ∫ σ : Option R_rep → ℝ^(N + 1), f (fun l => σ (some l)) *
          (∑ i : R_rep, V_k j d (σ (some i)) - (n : ℝ) * V_k j d (σ none))
          ∂(Measure.pi fun _ : Option R_rep => G_full t d) := fun j d =>
      replicaDiff_eq_integral_of_integrable (G_full t d) f (V_k j d) fun o =>
        integrable_replicaDiff_term_of_confining (μ := volume) hκ0 (hem d) (hconf d) hf hfb
          (hVm j d) (hVb j d) o
    simp_rw [hrew]
    exact integral_shcherbinaTirozziCavity_constraint_swap (R_rep := Option R_rep) κ h r.toNNReal
      rBar t u k (fun row σ => f (fun l => σ (some l)) *
        (∑ i : R_rep, (deriv (deriv u) ((Real.sqrt (N + 1))⁻¹ *
            ((∑ j : Fin N, row j.castSucc * (σ (some i)) j.castSucc) +
              Real.sqrt t * (row (Fin.last N) * (σ (some i)) (Fin.last N)))) +
          deriv u ((Real.sqrt (N + 1))⁻¹ *
            ((∑ j : Fin N, row j.castSucc * (σ (some i)) j.castSucc) +
              Real.sqrt t * (row (Fin.last N) * (σ (some i)) (Fin.last N)))) ^ 2) *
          (σ (some i)) (Fin.last N) ^ 2 -
        (n : ℝ) * ((deriv (deriv u) ((Real.sqrt (N + 1))⁻¹ *
            ((∑ j : Fin N, row j.castSucc * (σ none) j.castSucc) +
              Real.sqrt t * (row (Fin.last N) * (σ none) (Fin.last N)))) +
          deriv u ((Real.sqrt (N + 1))⁻¹ *
            ((∑ j : Fin N, row j.castSucc * (σ none) j.castSucc) +
              Real.sqrt t * (row (Fin.last N) * (σ none) (Fin.last N)))) ^ 2) *
          (σ none) (Fin.last N) ^ 2)))
  have hswap_U : ∀ k : Fin (M + 1),
      (∫ d, replicaPairAverage (G_full t d) f (fun a b => U k d a * U k d b) ∂P_full) =
      ∫ d, replicaPairAverage (G_full t d) f
        (fun a b => U (Fin.last M) d a * U (Fin.last M) d b) ∂P_full := fun k => by
    simp only [replicaPairAverage_eq]
    exact integral_shcherbinaTirozziCavity_constraint_swap (R_rep := Option (Option R_rep)) κ h
      r.toNNReal rBar t u k (fun row τ => f (fun l => τ (some (some l))) *
        replicaPairCombination (fun a b =>
          (deriv u ((Real.sqrt (N + 1))⁻¹ *
              ((∑ j : Fin N, row j.castSucc * a j.castSucc) +
                Real.sqrt t * (row (Fin.last N) * a (Fin.last N)))) * a (Fin.last N)) *
          (deriv u ((Real.sqrt (N + 1))⁻¹ *
              ((∑ j : Fin N, row j.castSucc * b j.castSucc) +
                Real.sqrt t * (row (Fin.last N) * b (Fin.last N)))) * b (Fin.last N))) τ)
  -- Step 3: Simplify the derivative expression to
  -- `(α * 𝔼[D(V_last)] - rBar * 𝔼[D(ε²)]) / 2 + (α * 𝔼[P(U_last ⊗ U_last)] - r * 𝔼[P(ε ⊗ ε)])`
  have hD_eq :
      ((N : ℝ) + 1)⁻¹ * (∑ k : Fin (M + 1), ∫ d, (replicaDiff (G_full t d) f (V_k k d) / 2 +
          replicaPairAverage (G_full t d) f (fun a b => U k d a * U k d b)) ∂P_full) -
        ∫ d, ((r.toNNReal : ℝ) * replicaPairAverage (G_full t d) f
            (fun a b => a (Fin.last N) * b (Fin.last N)) +
          rBar * replicaDiff (G_full t d) f (fun σ => σ (Fin.last N) ^ 2) / 2) ∂P_full =
      (α * (∫ d, replicaDiff (G_full t d) f (V_k (Fin.last M) d) ∂P_full) -
        rBar * (∫ d, replicaDiff (G_full t d) f (fun σ => σ (Fin.last N) ^ 2) ∂P_full)) / 2 +
      (α * (∫ d, replicaPairAverage (G_full t d) f
          (fun a b => U (Fin.last M) d a * U (Fin.last M) d b) ∂P_full) -
        r * (∫ d, replicaPairAverage (G_full t d) f
          (fun a b => a (Fin.last N) * b (Fin.last N)) ∂P_full)) := by
    have hsum1 : ∀ k : Fin (M + 1),
        ∫ d, (replicaDiff (G_full t d) f (V_k k d) / 2 +
          replicaPairAverage (G_full t d) f (fun a b => U k d a * U k d b)) ∂P_full =
        (∫ d, replicaDiff (G_full t d) f (V_k (Fin.last M) d) ∂P_full) / 2 +
          ∫ d, replicaPairAverage (G_full t d) f
            (fun a b => U (Fin.last M) d a * U (Fin.last M) d b) ∂P_full := fun k => by
      rw [integral_add ((hIV k).div_const 2) (hIU k), integral_div, hswap_V k, hswap_U k]
    have h2 : ∫ d, ((r.toNNReal : ℝ) * replicaPairAverage (G_full t d) f
            (fun a b => a (Fin.last N) * b (Fin.last N)) +
          rBar * replicaDiff (G_full t d) f (fun σ => σ (Fin.last N) ^ 2) / 2) ∂P_full =
        r * (∫ d, replicaPairAverage (G_full t d) f
            (fun a b => a (Fin.last N) * b (Fin.last N)) ∂P_full) +
          rBar * (∫ d, replicaDiff (G_full t d) f (fun σ => σ (Fin.last N) ^ 2) ∂P_full) / 2 := by
      have hi1 : Integrable (fun d => (r.toNNReal : ℝ) * replicaPairAverage (G_full t d) f
          (fun a b => a (Fin.last N) * b (Fin.last N))) P_full := hIPε.const_mul (r.toNNReal : ℝ)
      have hi2 : Integrable (fun d => rBar * replicaDiff (G_full t d) f
          (fun σ => σ (Fin.last N) ^ 2) / 2) P_full := (hIDε.const_mul rBar).div_const 2
      rw [integral_add hi1 hi2, integral_div, integral_const_mul, integral_const_mul, hr_coe]
    have h1 : ∑ k : Fin (M + 1), ∫ d, (replicaDiff (G_full t d) f (V_k k d) / 2 +
          replicaPairAverage (G_full t d) f (fun a b => U k d a * U k d b)) ∂P_full =
        ((M : ℝ) + 1) * ((∫ d, replicaDiff (G_full t d) f (V_k (Fin.last M) d) ∂P_full) / 2 +
          ∫ d, replicaPairAverage (G_full t d) f
            (fun a b => U (Fin.last M) d a * U (Fin.last M) d b) ∂P_full) := by
      simp_rw [hsum1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
    rw [h1, h2]
    dsimp only [α]
    rw [div_eq_mul_inv ((M : ℝ) + 1)]
    ring
  rw [hD_eq]
  -- Step 4: Bound each of the two differences by decomposing `replicaDiff` and `replicaPairAverage`
  -- into individual replica terms and applying `hcancel1` and `hcancel2`!
  set Err : ℝ := Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
        (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => G_full t d) ∂P_full) +
      Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
        (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full t d) ∂P_full) +
      ((N : ℝ) + 1)⁻¹
  have hErr0 : 0 ≤ Err := by dsimp only [Err]; positivity
  -- Helper: single `Option R_rep` term bound via `hcancel1`
  have hterm1 : ∀ o : Option R_rep,
      |α * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1), f (fun l => σ (some l)) * V_k (Fin.last M) d (σ o)
          ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
        rBar * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
          f (fun l => σ (some l)) * (σ o) (Fin.last N) ^ 2
          ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full)| ≤ K₁ * A * Err := by
    intro o
    set g₁ : (Option R_rep → ℝ^(N + 1)) → ℝ := fun σ =>
      f (fun l => σ (some l)) * (σ o) (Fin.last N) ^ 2
    have hg₁m : Measurable g₁ :=
      (hf.comp (Measurable.of_eval fun l => measurable_pi_apply (some l))).mul
        ((hε_m.comp (measurable_pi_apply o)).pow_const 2)
    have hg₁b : ∀ σ, |g₁ σ| ≤ C * ∏ l : Option R_rep, (1 + ‖σ l‖) ^ (m + 2) := fun σ => by
      dsimp only [g₁]
      have h1 := abs_comp_some_le_prod hfb σ
      have h2 := abs_comp_eval_le_prod hε2_b σ o
      simpa only [mul_one] using abs_mul_le_mul_prod_one_add_norm_pow h1 h2
    have hc1 := (hcancel1 N M κ h t q ρ rBar r.toNNReal u (g := g₁) o o hκ hh ht0.le ht1.le
      hq0 hqρ hρQ hrr' hrR' hrr_diff' hM huc hu0 hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD
      hg₁m hg₁b hA (fun s hs => hA1 o s hs)).2
    refine le_of_eq_of_le (congrArg abs ?_) hc1
    congr 2
    refine integral_congr_ae (ae_of_all _ fun d => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [g₁, V_k]; ring
  -- Helper: single `Option (Option R_rep)` off-diagonal term bound via `hcancel2`
  have hterm2 : ∀ {a b : Option (Option R_rep)}, a ≠ b →
      |α * (∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
          f (fun l => τ (some (some l))) * (U (Fin.last M) d (τ a) * U (Fin.last M) d (τ b))
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) -
        r * (∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
          f (fun l => τ (some (some l))) * ((τ a) (Fin.last N) * (τ b) (Fin.last N))
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full)| ≤ K₂ * A * Err := by
    intro a b hne
    set g₂ : (Option (Option R_rep) → ℝ^(N + 1)) → ℝ := fun τ =>
      f (fun l => τ (some (some l))) * ((τ a) (Fin.last N) * (τ b) (Fin.last N))
    have hg₂m : Measurable g₂ :=
      (hf.comp (Measurable.of_eval fun l => measurable_pi_apply (some (some l)))).mul
        ((hε_m.comp (measurable_pi_apply a)).mul (hε_m.comp (measurable_pi_apply b)))
    have hg₂b : ∀ τ, |g₂ τ| ≤ C * ∏ l : Option (Option R_rep), (1 + ‖τ l‖) ^ (m + 2) := fun τ => by
      dsimp only [g₂]
      have h1 : |f (fun l => τ (some (some l)))| ≤
          C * ∏ l : Option (Option R_rep), (1 + ‖τ l‖) ^ m :=
        abs_comp_some_le_prod (fun o => abs_comp_some_le_prod hfb o) τ
      have h2 := abs_comp_eval_le_prod hε_b τ a
      have h3 := abs_comp_eval_le_prod hε_b τ b
      have h23 := abs_mul_le_mul_prod_one_add_norm_pow h2 h3
      rw [mul_one] at h23
      simpa only [mul_one] using abs_mul_le_mul_prod_one_add_norm_pow h1 h23
    have hc2 := (hcancel2 N M κ h t q ρ rBar r.toNNReal u (g := g₂) a b hκ hh ht0.le ht1.le
      hq0 hqρ hρQ hrr' hrR' hrr_diff' hM huc hu0 hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD
      hg₂m hg₂b hA (fun s hs => hA2 a b s hs)).1 hne
    refine le_of_eq_of_le (congrArg abs ?_) hc2
    congr 2
    refine integral_congr_ae (ae_of_all _ fun d => integral_congr_ae (ae_of_all _ fun τ => ?_))
    dsimp only [g₂, U]; ring
  -- Expand `replicaDiff` over `P_full`
  have hDiff_bd :
      |α * (∫ d, replicaDiff (G_full t d) f (V_k (Fin.last M) d) ∂P_full) -
        rBar * (∫ d, replicaDiff (G_full t d) f (fun σ => σ (Fin.last N) ^ 2) ∂P_full)| ≤
      2 * (n : ℝ) * (K₁ * A * Err) := by
    have hV_term_i : ∀ o : Option R_rep, Integrable (fun d => ∫ σ : Option R_rep → ℝ^(N + 1),
        f (fun l => σ (some l)) * V_k (Fin.last M) d (σ o)
        ∂(Measure.pi fun _ : Option R_rep => G_full t d)) P_full := fun o => by
      refine hP_int (fun d σ => f (fun l => σ (some l)) * V_k (Fin.last M) d (σ o))
        (C * (D + D ^ 2)) (m + 2) ?_ fun d σ => ?_
      · have hfm : Measurable fun q :
            (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
              (Option R_rep → ℝ^(N + 1)) =>
            cfield[N, t, q.1.2.1, Fin.last M, q.2 o] := by
          have hg_m : ∀ i : Fin (N + 1), Measurable fun q :
              (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
                (Option R_rep → ℝ^(N + 1)) => q.1.2.1 (Fin.last M) i := fun i =>
            (measurable_pi_apply i).comp ((measurable_pi_apply (Fin.last M)).comp
              (measurable_fst.comp (measurable_snd.comp measurable_fst)))
          have hσ_m : ∀ i : Fin (N + 1), Measurable fun q :
              (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
                (Option R_rep → ℝ^(N + 1)) => (q.2 o) i := fun i =>
            ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).comp
              ((measurable_pi_apply o).comp measurable_snd)
          exact (((Finset.measurable_sum _ fun i _ =>
            (hg_m i.castSucc).mul (hσ_m i.castSucc)).add
            (((hg_m (Fin.last N)).mul (hσ_m (Fin.last N))).const_mul _)).const_mul _)
        have hfo : Measurable fun q : Dis × (Option R_rep → ℝ^(N + 1)) =>
            f (fun l => q.2 (some l)) :=
          hf.comp (Measurable.of_eval fun l =>
            (measurable_pi_apply (some l)).comp measurable_snd)
        exact hfo.mul ((((measurable_deriv (deriv u)).comp hfm).add
          (((measurable_deriv u).comp hfm).pow_const 2)).mul
          ((hε_m.comp ((measurable_pi_apply o).comp measurable_snd)).pow_const 2))
      · exact abs_mul_le_mul_prod_one_add_norm_pow (abs_comp_some_le_prod hfb σ)
          (abs_comp_eval_le_prod (hVb (Fin.last M) d) σ o)
    have hε_term_i : ∀ o : Option R_rep, Integrable (fun d => ∫ σ : Option R_rep → ℝ^(N + 1),
        f (fun l => σ (some l)) * (σ o) (Fin.last N) ^ 2
        ∂(Measure.pi fun _ : Option R_rep => G_full t d)) P_full := fun o => by
      refine hP_int (fun _ σ => f (fun l => σ (some l)) * (σ o) (Fin.last N) ^ 2) C (m + 2)
        ((hf.comp (Measurable.of_eval fun l =>
          (measurable_pi_apply (some l)).comp measurable_snd)).mul
          ((hε_m.comp ((measurable_pi_apply o).comp measurable_snd)).pow_const 2)) fun _ σ => ?_
      simpa only [mul_one] using abs_mul_le_mul_prod_one_add_norm_pow
        (abs_comp_some_le_prod hfb σ) (abs_comp_eval_le_prod hε2_b σ o)
    have hV_split : (∫ d, replicaDiff (G_full t d) f (V_k (Fin.last M) d) ∂P_full) =
        (∑ i : R_rep, ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
          f (fun l => σ (some l)) * V_k (Fin.last M) d (σ (some i))
          ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
        (n : ℝ) * ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
          f (fun l => σ (some l)) * V_k (Fin.last M) d (σ none)
          ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full := by
      simp only [replicaDiff_eq]
      rw [integral_sub (integrable_finsetSum _ fun i _ => hV_term_i (some i))
        ((hV_term_i none).const_mul _),
        integral_finsetSum _ fun i _ => hV_term_i (some i), integral_const_mul]
    have hε_split : (∫ d, replicaDiff (G_full t d) f (fun σ => σ (Fin.last N) ^ 2) ∂P_full) =
        (∑ i : R_rep, ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
          f (fun l => σ (some l)) * (σ (some i)) (Fin.last N) ^ 2
          ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
        (n : ℝ) * ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
          f (fun l => σ (some l)) * (σ none) (Fin.last N) ^ 2
          ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full := by
      simp only [replicaDiff_eq]
      rw [integral_sub (integrable_finsetSum _ fun i _ => hε_term_i (some i))
        ((hε_term_i none).const_mul _),
        integral_finsetSum _ fun i _ => hε_term_i (some i), integral_const_mul]
    rw [hV_split, hε_split]
    have hcomb :
        α * ((∑ i : R_rep, ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * V_k (Fin.last M) d (σ (some i))
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
          (n : ℝ) * ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * V_k (Fin.last M) d (σ none)
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
        rBar * ((∑ i : R_rep, ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * (σ (some i)) (Fin.last N) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
          (n : ℝ) * ∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * (σ none) (Fin.last N) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) =
        (∑ i : R_rep, (α * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * V_k (Fin.last M) d (σ (some i))
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
          rBar * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * (σ (some i)) (Fin.last N) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full))) -
        (n : ℝ) * (α * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * V_k (Fin.last M) d (σ none)
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
          rBar * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * (σ none) (Fin.last N) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    rw [hcomb]
    refine (abs_sub _ _).trans ?_
    have hsum_bd : |∑ i : R_rep, (α * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * V_k (Fin.last M) d (σ (some i))
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
          rBar * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * (σ (some i)) (Fin.last N) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full))| ≤
        (n : ℝ) * (K₁ * A * Err) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _i : R_rep, K₁ * A * Err := Finset.sum_le_sum fun i _ => hterm1 (some i)
        _ = (n : ℝ) * (K₁ * A * Err) := by simp [n]
    have hnone_bd : |(n : ℝ) * (α * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * V_k (Fin.last M) d (σ none)
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full) -
          rBar * (∫ d, ∫ σ : Option R_rep → ℝ^(N + 1),
            f (fun l => σ (some l)) * (σ none) (Fin.last N) ^ 2
            ∂(Measure.pi fun _ : Option R_rep => G_full t d) ∂P_full))| ≤
        (n : ℝ) * (K₁ * A * Err) := by
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hterm1 none) (Nat.cast_nonneg _)
    linarith
  -- Expand `replicaPairAverage` over `P_full`
  have hPair_bd :
      |α * (∫ d, replicaPairAverage (G_full t d) f
          (fun a b => U (Fin.last M) d a * U (Fin.last M) d b) ∂P_full) -
        r * (∫ d, replicaPairAverage (G_full t d) f
          (fun a b => a (Fin.last N) * b (Fin.last N)) ∂P_full)| ≤
      (3 * ((n : ℝ) + 1) ^ 2) * (K₂ * A * Err) := by
    -- Helper: integrability of one pair term over `G_full t d` and `P_full`
    have hU_term_i : ∀ a b : Option (Option R_rep),
        Integrable (fun d => ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
          f (fun l => τ (some (some l))) * (U (Fin.last M) d (τ a) * U (Fin.last M) d (τ b))
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) P_full := fun a b => by
      refine hP_int (fun d τ =>
          f (fun l => τ (some (some l))) * (U (Fin.last M) d (τ a) * U (Fin.last M) d (τ b)))
        (C * D ^ 2) (m + 2) ?_ fun d τ => ?_
      · have hfm : ∀ o : Option (Option R_rep), Measurable fun q :
            (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
              (Option (Option R_rep) → ℝ^(N + 1)) =>
            cfield[N, t, q.1.2.1, Fin.last M, q.2 o] := fun o => by
          have hg_m : ∀ i : Fin (N + 1), Measurable fun q :
              (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
                (Option (Option R_rep) → ℝ^(N + 1)) => q.1.2.1 (Fin.last M) i := fun i =>
            (measurable_pi_apply i).comp ((measurable_pi_apply (Fin.last M)).comp
              (measurable_fst.comp (measurable_snd.comp measurable_fst)))
          have hσ_m : ∀ i : Fin (N + 1), Measurable fun q :
              (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
                (Option (Option R_rep) → ℝ^(N + 1)) => (q.2 o) i := fun i =>
            ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).comp
              ((measurable_pi_apply o).comp measurable_snd)
          exact (((Finset.measurable_sum _ fun i _ =>
            (hg_m i.castSucc).mul (hσ_m i.castSucc)).add
            (((hg_m (Fin.last N)).mul (hσ_m (Fin.last N))).const_mul _)).const_mul _)
        have hfo : Measurable fun q : Dis × (Option (Option R_rep) → ℝ^(N + 1)) =>
            f (fun l => q.2 (some (some l))) :=
          hf.comp (Measurable.of_eval fun l =>
            (measurable_pi_apply (some (some l))).comp measurable_snd)
        have hUm_o : ∀ o : Option (Option R_rep), Measurable fun q :
            Dis × (Option (Option R_rep) → ℝ^(N + 1)) => U (Fin.last M) q.1 (q.2 o) := fun o =>
          ((measurable_deriv u).comp (hfm o)).mul
            (hε_m.comp ((measurable_pi_apply o).comp measurable_snd))
        exact hfo.mul ((hUm_o a).mul (hUm_o b))
      · have h1 : |f (fun l => τ (some (some l)))| ≤
            C * ∏ l : Option (Option R_rep), (1 + ‖τ l‖) ^ m :=
          abs_comp_some_le_prod (fun o => abs_comp_some_le_prod hfb o) τ
        have h2 := abs_comp_eval_le_prod (hUb (Fin.last M) d) τ a
        have h3 := abs_comp_eval_le_prod (hUb (Fin.last M) d) τ b
        have h23 := abs_mul_le_mul_prod_one_add_norm_pow h2 h3
        rw [← sq] at h23
        exact abs_mul_le_mul_prod_one_add_norm_pow h1 h23
    have hεp_term_i : ∀ a b : Option (Option R_rep),
        Integrable (fun d => ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
          f (fun l => τ (some (some l))) * ((τ a) (Fin.last N) * (τ b) (Fin.last N))
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) P_full := fun a b => by
      refine hP_int (fun _ τ =>
          f (fun l => τ (some (some l))) * ((τ a) (Fin.last N) * (τ b) (Fin.last N)))
        C (m + 2)
        ((hf.comp (Measurable.of_eval fun l =>
          (measurable_pi_apply (some (some l))).comp measurable_snd)).mul
          ((hε_m.comp ((measurable_pi_apply a).comp measurable_snd)).mul
            (hε_m.comp ((measurable_pi_apply b).comp measurable_snd)))) fun _ τ => ?_
      have h1 : |f (fun l => τ (some (some l)))| ≤
          C * ∏ l : Option (Option R_rep), (1 + ‖τ l‖) ^ m :=
        abs_comp_some_le_prod (fun o => abs_comp_some_le_prod hfb o) τ
      have h2 := abs_comp_eval_le_prod hε_b τ a
      have h3 := abs_comp_eval_le_prod hε_b τ b
      have h23 := abs_mul_le_mul_prod_one_add_norm_pow h2 h3
      rw [mul_one] at h23
      simpa only [mul_one] using abs_mul_le_mul_prod_one_add_norm_pow h1 h23
    -- Expand `replicaPairAverage` for any kernel `K_ker` with integrable terms
    have hpair_expand : ∀ (K_ker : Dis → ℝ^(N + 1) → ℝ^(N + 1) → ℝ),
        (∀ d a b, Integrable (fun τ : Option (Option R_rep) → ℝ^(N + 1) =>
            f (fun l => τ (some (some l))) * K_ker d (τ a) (τ b))
          (Measure.pi fun _ : Option (Option R_rep) => G_full t d)) →
        (∀ a b, Integrable (fun d => ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
            f (fun l => τ (some (some l))) * K_ker d (τ a) (τ b)
            ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) P_full) →
        (∫ d, replicaPairAverage (G_full t d) f (K_ker d) ∂P_full) =
          (∑ p : R_rep × R_rep with p.1 < p.2,
            ∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l => τ (some (some l))) * K_ker d (τ (some (some p.1))) (τ (some (some p.2)))
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) -
          (n : ℝ) * (∑ l : R_rep,
            ∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l' => τ (some (some l'))) * K_ker d (τ (some (some l))) (τ (some none))
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 *
            (∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l' => τ (some (some l'))) * K_ker d (τ (some none)) (τ none)
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) := by
      intro K_ker hKi_d hKi_P
      have hpt_d : ∀ d, replicaPairAverage (G_full t d) f (K_ker d) =
          (∑ p : R_rep × R_rep with p.1 < p.2,
            ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l => τ (some (some l))) * K_ker d (τ (some (some p.1))) (τ (some (some p.2)))
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) -
          (n : ℝ) * (∑ l : R_rep,
            ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l' => τ (some (some l'))) * K_ker d (τ (some (some l))) (τ (some none))
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 *
            (∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l' => τ (some (some l'))) * K_ker d (τ (some none)) (τ none)
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) := fun d => by
        rw [replicaPairAverage_eq]
        have h1 : Integrable (fun τ : Option (Option R_rep) → ℝ^(N + 1) =>
            ∑ p : R_rep × R_rep with p.1 < p.2,
              f (fun l => τ (some (some l))) *
                K_ker d (τ (some (some p.1))) (τ (some (some p.2))))
            (Measure.pi fun _ : Option (Option R_rep) => G_full t d) :=
          integrable_finsetSum _ fun p _ => hKi_d d (some (some p.1)) (some (some p.2))
        have h2 : Integrable (fun τ : Option (Option R_rep) → ℝ^(N + 1) =>
            (n : ℝ) * ∑ l : R_rep,
              f (fun l' => τ (some (some l'))) * K_ker d (τ (some (some l))) (τ (some none)))
            (Measure.pi fun _ : Option (Option R_rep) => G_full t d) :=
          (integrable_finsetSum _ fun l _ => hKi_d d (some (some l)) (some none)).const_mul _
        have h3 : Integrable (fun τ : Option (Option R_rep) → ℝ^(N + 1) =>
            (n : ℝ) * ((n : ℝ) + 1) / 2 *
              (f (fun l' => τ (some (some l'))) * K_ker d (τ (some none)) (τ none)))
            (Measure.pi fun _ : Option (Option R_rep) => G_full t d) :=
          (hKi_d d (some none) none).const_mul _
        have h12 : Integrable (fun τ : Option (Option R_rep) → ℝ^(N + 1) =>
            (∑ p : R_rep × R_rep with p.1 < p.2,
              f (fun l => τ (some (some l))) *
                K_ker d (τ (some (some p.1))) (τ (some (some p.2)))) -
            (n : ℝ) * ∑ l : R_rep,
              f (fun l' => τ (some (some l'))) * K_ker d (τ (some (some l))) (τ (some none)))
            (Measure.pi fun _ : Option (Option R_rep) => G_full t d) := h1.sub h2
        have hrew : (fun τ : Option (Option R_rep) → ℝ^(N + 1) =>
            f (fun r => τ (some (some r))) * replicaPairCombination (K_ker d) τ) =
            fun τ =>
              ((∑ x ∈ Finset.filter (fun p : R_rep × R_rep => p.1 < p.2) Finset.univ,
                  f (fun l => τ (some (some l))) *
                    K_ker d (τ (some (some x.1))) (τ (some (some x.2)))) -
                (n : ℝ) * (∑ l : R_rep,
                  f (fun l' => τ (some (some l'))) *
                    K_ker d (τ (some (some l))) (τ (some none)))) +
                (n : ℝ) * ((n : ℝ) + 1) / 2 *
                  (f (fun l' => τ (some (some l'))) * K_ker d (τ (some none)) (τ none)) :=
          funext fun τ => by
            dsimp only [replicaPairCombination, n]
            rw [mul_add, mul_sub, Finset.mul_sum,
              ← Finset.mul_sum (s := Finset.univ) (a := f (fun l' => τ (some (some l'))))]
            ring
        rw [hrew, integral_add h12 h3, integral_sub h1 h2,
          integral_finsetSum _ fun p _ => hKi_d d (some (some p.1)) (some (some p.2)),
          integral_const_mul, integral_finsetSum _ fun l _ => hKi_d d (some (some l)) (some none),
          integral_const_mul]
      simp_rw [hpt_d]
      have hP1 : Integrable (fun d => ∑ p : R_rep × R_rep with p.1 < p.2,
          ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
            f (fun l => τ (some (some l))) * K_ker d (τ (some (some p.1))) (τ (some (some p.2)))
            ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) P_full :=
        integrable_finsetSum _ fun p _ => hKi_P (some (some p.1)) (some (some p.2))
      have hP2 : Integrable (fun d => (n : ℝ) * ∑ l : R_rep,
          ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
            f (fun l' => τ (some (some l'))) * K_ker d (τ (some (some l))) (τ (some none))
            ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) P_full :=
        (integrable_finsetSum _ fun l _ => hKi_P (some (some l)) (some none)).const_mul _
      have hP3 : Integrable (fun d => (n : ℝ) * ((n : ℝ) + 1) / 2 *
          ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
            f (fun l' => τ (some (some l'))) * K_ker d (τ (some none)) (τ none)
            ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) P_full :=
        (hKi_P (some none) none).const_mul _
      have hP12 : Integrable (fun d =>
          (∑ p : R_rep × R_rep with p.1 < p.2,
            ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l => τ (some (some l))) * K_ker d (τ (some (some p.1))) (τ (some (some p.2)))
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) -
          (n : ℝ) * ∑ l : R_rep,
            ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
              f (fun l' => τ (some (some l'))) * K_ker d (τ (some (some l))) (τ (some none))
              ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d)) P_full := hP1.sub hP2
      rw [integral_add hP12 hP3, integral_sub hP1 hP2,
        integral_finsetSum _ fun p _ => hKi_P (some (some p.1)) (some (some p.2)),
        integral_const_mul, integral_finsetSum _ fun l _ => hKi_P (some (some l)) (some none),
        integral_const_mul]
    have hU_exp := hpair_expand (fun d a b => U (Fin.last M) d a * U (Fin.last M) d b)
      (fun d a b => integrable_pi_tilted_of_confining hκ0 (hem d) (hconf d)
        (((hf.comp (Measurable.of_eval fun l => measurable_pi_apply (some (some l)))).mul
          (((hUm (Fin.last M) d).comp (measurable_pi_apply a)).mul
            ((hUm (Fin.last M) d).comp (measurable_pi_apply b)))).aestronglyMeasurable)
        fun τ => by
          rw [Real.norm_eq_abs]
          have h1 := abs_comp_some_le_prod (fun o => abs_comp_some_le_prod hfb o) τ
          have h23 := abs_mul_le_mul_prod_one_add_norm_pow
            (abs_comp_eval_le_prod (hUb (Fin.last M) d) τ a)
            (abs_comp_eval_le_prod (hUb (Fin.last M) d) τ b)
          exact abs_mul_le_mul_prod_one_add_norm_pow h1 h23)
      hU_term_i
    have hε_exp := hpair_expand (fun _ a b => a (Fin.last N) * b (Fin.last N))
      (fun d a b => integrable_pi_tilted_of_confining hκ0 (hem d) (hconf d)
        (((hf.comp (Measurable.of_eval fun l => measurable_pi_apply (some (some l)))).mul
          ((hε_m.comp (measurable_pi_apply a)).mul
            (hε_m.comp (measurable_pi_apply b)))).aestronglyMeasurable)
        fun τ => by
          rw [Real.norm_eq_abs]
          have h1 := abs_comp_some_le_prod (fun o => abs_comp_some_le_prod hfb o) τ
          have h23 := abs_mul_le_mul_prod_one_add_norm_pow
            (abs_comp_eval_le_prod hε_b τ a) (abs_comp_eval_le_prod hε_b τ b)
          exact abs_mul_le_mul_prod_one_add_norm_pow h1 h23)
      hεp_term_i
    rw [hU_exp, hε_exp]
    -- Group matching terms and apply `hterm2`
    set Δ : Option (Option R_rep) → Option (Option R_rep) → ℝ := fun a b =>
      α * (∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
          f (fun l => τ (some (some l))) * (U (Fin.last M) d (τ a) * U (Fin.last M) d (τ b))
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) -
        r * (∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
          f (fun l => τ (some (some l))) * ((τ a) (Fin.last N) * (τ b) (Fin.last N))
          ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full)
    have hcomb2 :
        α * ((∑ p : R_rep × R_rep with p.1 < p.2,
              ∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
                f (fun l => τ (some (some l))) *
                  (U (Fin.last M) d (τ (some (some p.1))) * U (Fin.last M) d (τ (some (some p.2))))
                ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) -
            (n : ℝ) * (∑ l : R_rep,
              ∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
                f (fun l' => τ (some (some l'))) *
                  (U (Fin.last M) d (τ (some (some l))) * U (Fin.last M) d (τ (some none)))
                ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 *
              (∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
                f (fun l' => τ (some (some l'))) *
                  (U (Fin.last M) d (τ (some none)) * U (Fin.last M) d (τ none))
                ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full)) -
        r * ((∑ p : R_rep × R_rep with p.1 < p.2,
              ∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
                f (fun l => τ (some (some l))) *
                  ((τ (some (some p.1))) (Fin.last N) * (τ (some (some p.2))) (Fin.last N))
                ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) -
            (n : ℝ) * (∑ l : R_rep,
              ∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
                f (fun l' => τ (some (some l'))) *
                  ((τ (some (some l))) (Fin.last N) * (τ (some none)) (Fin.last N))
                ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full) +
            (n : ℝ) * ((n : ℝ) + 1) / 2 *
              (∫ d, ∫ τ : Option (Option R_rep) → ℝ^(N + 1),
                f (fun l' => τ (some (some l'))) *
                  ((τ (some none)) (Fin.last N) * (τ none) (Fin.last N))
                ∂(Measure.pi fun _ : Option (Option R_rep) => G_full t d) ∂P_full)) =
        (∑ p : R_rep × R_rep with p.1 < p.2, Δ (some (some p.1)) (some (some p.2))) -
          (n : ℝ) * (∑ l : R_rep, Δ (some (some l)) (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 * Δ (some none) none := by
      dsimp only [Δ]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [hcomb2]
    have h1 : |∑ p : R_rep × R_rep with p.1 < p.2, Δ (some (some p.1)) (some (some p.2))| ≤
        (n : ℝ) ^ 2 * (K₂ * A * Err) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hle : ∑ p : R_rep × R_rep with p.1 < p.2, |Δ (some (some p.1)) (some (some p.2))| ≤
          ∑ _p : R_rep × R_rep with _p.1 < _p.2, K₂ * A * Err :=
        Finset.sum_le_sum fun p hp => hterm2 (by
          intro h
          have h12 : p.1 = p.2 := Option.some_injective _ (Option.some_injective _ h)
          exact ne_of_lt (Finset.mem_filter.1 hp).2 h12)
      refine hle.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hcard : (Finset.filter (fun p : R_rep × R_rep => p.1 < p.2) Finset.univ).card ≤
          Fintype.card (R_rep × R_rep) := Finset.card_filter_le _ _
      rw [Fintype.card_prod] at hcard
      have hcard' : ((Finset.filter (fun p : R_rep × R_rep => p.1 < p.2) Finset.univ).card : ℝ) ≤
          (n : ℝ) * (n : ℝ) := by exact_mod_cast hcard
      linarith [sq (n : ℝ)]
    have h2 : |(n : ℝ) * ∑ l : R_rep, Δ (some (some l)) (some none)| ≤
        (n : ℝ) ^ 2 * (K₂ * A * Err) := by
      rw [abs_mul, Nat.abs_cast]
      refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun l _ => hterm2 (by simp))) (Nat.cast_nonneg _)).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ← sq]
    have h3 : |(n : ℝ) * ((n : ℝ) + 1) / 2 * Δ (some none) none| ≤
        ((n : ℝ) + 1) ^ 2 * (K₂ * A * Err) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine (mul_le_mul_of_nonneg_left (hterm2 (by simp)) (by positivity)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hsq : ((n : ℝ) + 1) ^ 2 = (n : ℝ) * (n : ℝ) + 2 * (n : ℝ) + 1 := by ring
      have hlhs : (n : ℝ) * ((n : ℝ) + 1) = (n : ℝ) * (n : ℝ) + (n : ℝ) := by ring
      have hnn : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) := mul_nonneg hn0 hn0
      linarith only [hn0, hsq, hlhs, hnn]
    have htri : |(∑ p : R_rep × R_rep with p.1 < p.2, Δ (some (some p.1)) (some (some p.2))) -
          (n : ℝ) * (∑ l : R_rep, Δ (some (some l)) (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 * Δ (some none) none| ≤
        |∑ p : R_rep × R_rep with p.1 < p.2, Δ (some (some p.1)) (some (some p.2))| +
          |(n : ℝ) * (∑ l : R_rep, Δ (some (some l)) (some none))| +
          |(n : ℝ) * ((n : ℝ) + 1) / 2 * Δ (some none) none| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    have hnsq : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)) 2
    have hKAE : 0 ≤ K₂ * A * Err := by positivity
    calc _ ≤ (n : ℝ) ^ 2 * (K₂ * A * Err) + (n : ℝ) ^ 2 * (K₂ * A * Err) +
              ((n : ℝ) + 1) ^ 2 * (K₂ * A * Err) := htri.trans (add_le_add (add_le_add h1 h2) h3)
      _ ≤ ((n : ℝ) + 1) ^ 2 * (K₂ * A * Err) + ((n : ℝ) + 1) ^ 2 * (K₂ * A * Err) +
            ((n : ℝ) + 1) ^ 2 * (K₂ * A * Err) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_right hnsq hKAE)
            (mul_le_mul_of_nonneg_right hnsq hKAE)) le_rfl
      _ = (3 * ((n : ℝ) + 1) ^ 2) * (K₂ * A * Err) := by ring
  -- Combine `hDiff_bd` and `hPair_bd`
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)]
  have h1 : |α * (∫ d, replicaDiff (G_full t d) f (V_k (Fin.last M) d) ∂P_full) -
      rBar * (∫ d, replicaDiff (G_full t d) f (fun σ => σ (Fin.last N) ^ 2) ∂P_full)| / 2 ≤
      ((n : ℝ) + 1) * (K₁ * A * Err) := by
    have hle := div_le_div_of_nonneg_right hDiff_bd zero_le_two
    have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hK1 : 0 ≤ K₁ * A * Err := by positivity
    calc _ ≤ 2 * (n : ℝ) * (K₁ * A * Err) / 2 := hle
      _ = (n : ℝ) * (K₁ * A * Err) := by ring
      _ ≤ ((n : ℝ) + 1) * (K₁ * A * Err) := mul_le_mul_of_nonneg_right hn hK1
  have hK_le : ((n : ℝ) + 1) * K₁ + (3 * ((n : ℝ) + 1) ^ 2) * K₂ ≤ K := by dsimp only [K]; linarith
  calc _ ≤ ((n : ℝ) + 1) * (K₁ * A * Err) + (3 * ((n : ℝ) + 1) ^ 2) * (K₂ * A * Err) :=
        add_le_add h1 hPair_bd
    _ = (((n : ℝ) + 1) * K₁ + (3 * ((n : ℝ) + 1) ^ 2) * K₂) * A * Err := by ring
    _ ≤ K * A * Err := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le hA) hErr0

end SpinGlasses
