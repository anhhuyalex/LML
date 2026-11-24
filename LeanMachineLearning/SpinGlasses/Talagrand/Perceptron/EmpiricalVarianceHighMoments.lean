/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.EmpiricalVariance
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.OverlapHighMoments

/-!
# Higher moments of the empirical variance of `u'` (Talagrand Section 2.5, Theorem 2.5.2)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.5, Theorem 2.5.2,
Eqs. (2.99)--(2.106).

For the `s`-interpolating Hamiltonian (2.76) on `N + 1` spins and `M` constraints at any
`s ∈ [0, 1]`, under assumption (2.7) and small load `α K(D) ≤ 1`, any solution `(q, r)` of (2.68)
satisfies
$$\forall k \ge 0, \quad
  \nu_s\!\left(\left(\frac{1}{N + 1} \sum_{j < M}
    u'(S_{j, s}^1) u'(S_{j, s}^2) - r\right)^{2k}\right)
  \le \left(\frac{\alpha k L}{N + 1}\right)^k$$
(with the `k = 0` power understood as `1`).

The proof inducts on `k` over the normalized constraint partial sums (`M + 1` constraints):
$$C_n(\sigma) = \frac{1}{M + 1} \sum_{j \ge n}
  \left(u'(S_{j, s}(\sigma^0))\,u'(S_{j, s}(\sigma^1)) - \widehat{r}\right),
  \quad n : \mathrm{Fin}(M + 1),$$
showing $\nu_s(C_n^{2k}) \le (k L / (M + 1))^k$, then scales by $\alpha^{2k}$ via the identity
$$\alpha^{2k} \left(\frac{k L}{M + 1}\right)^k
  = \left(\frac{\alpha k L}{N + 1}\right)^k, \quad \alpha = \frac{M + 1}{N + 1}.$$
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

/-! ### Pointwise partial-constraint bounds and row-swap symmetry -/

/-- Each constraint-derivative deviation `u'(S₀) u'(S₁) - r̂` has modulus at most `2 |D|²` when
`|u'| ≤ |D|` and `0 ≤ r̂ ≤ |D|²`. -/
private lemma abs_deriv_mul_sub_rhat_le {u : ℝ → ℝ} {D rhat : ℝ}
    (hD₁ : ∀ x, |deriv u x| ≤ |D|) (hrhat : rhat ∈ Icc (0 : ℝ) (|D| ^ 2)) (x₀ x₁ : ℝ) :
    |deriv u x₀ * deriv u x₁ - rhat| ≤ 2 * |D| ^ 2 := by
  have hprod : |deriv u x₀ * deriv u x₁| ≤ |D| ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (hD₁ x₀) (hD₁ x₁) (abs_nonneg _) (abs_nonneg D)
  have hsub := abs_sub (deriv u x₀ * deriv u x₁) rhat
  rw [abs_of_nonneg hrhat.1] at hsub
  linarith [hrhat.2]

/-- Any normalized partial sum `(M + 1)⁻¹ ∑ j ∈ S, (u'(S^0_j) u'(S^1_j) - r̂)` over a subset
`S ⊆ Finset.univ` of `Fin (M + 1)` has modulus at most `2 |D|²`. -/
private lemma abs_partial_constraint_sub_le {M : ℕ} {u : ℝ → ℝ} {D rhat : ℝ}
    (hD₁ : ∀ x, |deriv u x| ≤ |D|) (hrhat : rhat ∈ Icc (0 : ℝ) (|D| ^ 2))
    (S : Finset (Fin (M + 1))) (v₀ v₁ : Fin (M + 1) → ℝ) :
    |((M + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ S, (deriv u (v₀ j) * deriv u (v₁ j) - rhat)| ≤ 2 * |D| ^ 2 := by
  have hM_pos : (0 : ℝ) < (M + 1 : ℕ) := by positivity
  have hcard : (S.card : ℝ) ≤ (M + 1 : ℕ) := by
    have hc : S.card ≤ Fintype.card (Fin (M + 1)) := S.card_le_univ
    rw [Fintype.card_fin] at hc
    exact_mod_cast hc
  rw [abs_mul, abs_of_pos (inv_pos.2 hM_pos)]
  calc ((M + 1 : ℕ) : ℝ)⁻¹ * |∑ j ∈ S, (deriv u (v₀ j) * deriv u (v₁ j) - rhat)|
      ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ S, |deriv u (v₀ j) * deriv u (v₁ j) - rhat| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hM_pos).le
    _ ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ _j ∈ S, (2 * |D| ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          abs_deriv_mul_sub_rhat_le hD₁ hrhat (v₀ j) (v₁ j)) (inv_pos.2 hM_pos).le
    _ = ((M + 1 : ℕ) : ℝ)⁻¹ * ((S.card : ℝ) * (2 * |D| ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * (((M + 1 : ℕ) : ℝ) * (2 * |D| ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcard (by positivity)) (inv_pos.2 hM_pos).le
    _ = 2 * |D| ^ 2 := by field_simp

/-- Swapping `n` (`n < M`) with `Fin.last M` bijects `(Finset.Ici n).erase (Fin.last M)` onto
`Finset.Ici ⟨n.1 + 1, ...⟩`. -/
private lemma sum_Ici_erase_last_constraint_eq_swap {M : ℕ} (n : Fin (M + 1)) (hn : n.1 < M)
    (g : Fin (M + 1) → ℝ) :
    ∑ j ∈ (Finset.Ici n).erase (Fin.last M), g j =
      ∑ l ∈ Finset.Ici (⟨n.1 + 1, by omega⟩ : Fin (M + 1)),
        g (Equiv.swap n (Fin.last M) l) := by
  symm
  refine Finset.sum_bij (fun l _ => Equiv.swap n (Fin.last M) l) ?_ ?_ ?_ ?_
  · intro l hl
    rw [Finset.mem_Ici] at hl
    have hl_val : n.1 + 1 ≤ l.1 := hl
    have hl_ne_n : l ≠ n := fun h => by subst h; omega
    rw [Finset.mem_erase, Finset.mem_Ici]
    refine ⟨?_, ?_⟩
    · intro hswap
      have hln : l = n := by
        have := congrArg (Equiv.swap n (Fin.last M)) hswap
        simpa [Equiv.swap_apply_right] using this
      exact hl_ne_n hln
    · by_cases hll : l = Fin.last M
      · subst hll; simp
      · rw [Equiv.swap_apply_of_ne_of_ne hl_ne_n hll]
        exact Fin.le_def.2 (by omega)
  · intro l₁ _ l₂ _ h
    exact (Equiv.swap n (Fin.last M)).injective h
  · intro j hj
    rw [Finset.mem_erase, Finset.mem_Ici] at hj
    rcases hj with ⟨hj_ne_last, hj_ge⟩
    refine ⟨Equiv.swap n (Fin.last M) j, ?_, by simp⟩
    rw [Finset.mem_Ici]
    by_cases hjn : j = n
    · subst hjn
      rw [Equiv.swap_apply_left]
      exact Fin.le_def.2 (by simp [Fin.last]; omega)
    · rw [Equiv.swap_apply_of_ne_of_ne hjn hj_ne_last]
      have hj_val : n.1 ≤ j.1 := hj_ge
      have hlt : n.1 < j.1 := lt_of_le_of_ne hj_val (fun h => hjn (Fin.ext h.symm))
      exact Fin.le_def.2 (show n.1 + 1 ≤ j.1 by omega)
  · intros; rfl

/-- **Row-swap invariance of any measurable constraint-field observable** under
`(interpConstraintDisorderSwap j₁ j₂, interpConstraintStateSwap j₁ j₂)`. -/
private lemma integral_interpolating_constraint_swap
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (j₁ j₂ : Fin (M + 1))
    {Ψ : (Fin 2 → Fin (M + 1) → ℝ) → ℝ} (hΨ_m : Measurable Ψ) :
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (j : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ j : Fin (M + 1), u (S_fn ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let ν_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
      μ_s.tilted (E_s ω)
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        Ψ (fun l j => S_fn ω (σ l) (Equiv.swap j₁ j₂ j))
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        Ψ (fun l j => S_fn ω (σ l) j)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
  intro P_g P_z P_z' P μ_s S_fn E_s ν_s
  let Ω := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu s q r
  have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * B + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν_prob (ω : Ω) : IsProbabilityMeasure (ν_s ω) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable (ae_of_all _ (hEb ω))
  have htilted_swap (ω : Ω) :
      ν_s (interpConstraintDisorderSwap j₁ j₂ ω) =
        (ν_s ω).map (interpConstraintStateSwap j₁ j₂) := by
    dsimp only [ν_s]
    rw [map_tilted_measurableEquiv (interpConstraintStateSwap j₁ j₂)
      (measurePreserving_interpConstraintStateSwap j₁ j₂) (Measurable.of_uncurry_left hEm_joint)]
    congr 1; funext x
    dsimp only [Function.comp_apply]
    rw [interpConstraintStateSwap_symm_apply]
    dsimp only [E_s, S_fn, interpConstraintDisorderSwap]
    congr 1
    rw [← Equiv.sum_comp (Equiv.swap j₁ j₂)]
    exact Finset.sum_congr rfl fun _ _ => by simp
  let G_id (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    Ψ (fun l j => S_fn ω (σ l) j)
  have hG_m : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
      G_id p.1 p.2 :=
    hΨ_m.comp (measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun j =>
      measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q j l)
  let I_id (ω : Ω) : ℝ := ∫ σ, G_id ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)
  have hI_m : Measurable I_id :=
    measurable_integral_pi_tilted (μ := μ_s) hEm_joint hG_m
  have hpt_sw (ω : Ω) :
      I_id (interpConstraintDisorderSwap j₁ j₂ ω) =
        ∫ σ, Ψ (fun l j => S_fn ω (σ l) (Equiv.swap j₁ j₂ j))
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) := by
    dsimp only [I_id, G_id]
    rw [htilted_swap ω, integral_pi_map_equiv (ν_s ω) (interpConstraintStateSwap j₁ j₂)]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    have hS_sw (l : Fin 2) (j : Fin (M + 1)) :
        S_fn (interpConstraintDisorderSwap j₁ j₂ ω)
          (interpConstraintStateSwap j₁ j₂ (σ l)) j =
        S_fn ω (σ l) (Equiv.swap j₁ j₂ j) := by
      dsimp only [S_fn, interpConstraintDisorderSwap]
      simp [interpConstraintStateSwap_apply]
    dsimp only
    simp_rw [hS_sw]
  have hmp := measurePreserving_interpConstraintDisorderSwap (L := N + 1) j₁ j₂
  exact (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans
    (hmp.integral_comp_of_aestronglyMeasurable (g := I_id) hI_m.aestronglyMeasurable)

/-- **Constraint-symmetry identity Eq. (2.101) on `Finset.Ici n`:**
`ν_s(C_n^{2k+2}) = (|Ici n| / (M + 1)) * ν_s((u'(S^0_M) u'(S^1_M) - r̂) C_n^{2k+1})`. -/
private lemma integral_partial_constraint_succ_eq_last
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B D₁ : ℝ}
    (hB : ∀ x, u x ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (s q r rhat : ℝ) (n : Fin (M + 1)) (k : ℕ) :
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (j : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ j : Fin (M + 1), u (S_fn ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let ν_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
      μ_s.tilted (E_s ω)
    let C_fn (v₀ v₁ : Fin (M + 1) → ℝ) : ℝ :=
      ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.Ici n, (deriv u (v₀ j) * deriv u (v₁ j) - rhat)
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        C_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P =
      (((Finset.Ici n).card : ℝ) / ((M + 1 : ℕ) : ℝ)) *
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat) *
            C_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
  intro P_g P_z P_z' P μ_s S_fn E_s ν_s C_fn
  let Ω := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu s q r
  have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * B + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν_prob (ω : Ω) : IsProbabilityMeasure (ν_s ω) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable (ae_of_all _ (hEb ω))
  let C_bnd : ℝ := |D₁| ^ 2 + |rhat|
  have hCbnd0 : 0 ≤ C_bnd := by dsimp only [C_bnd]; positivity
  have hterm_b (v₀ v₁ : Fin (M + 1) → ℝ) (j : Fin (M + 1)) :
      |deriv u (v₀ j) * deriv u (v₁ j) - rhat| ≤ C_bnd := by
    have hp : |deriv u (v₀ j) * deriv u (v₁ j)| ≤ |D₁| ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul ((hD₁ _).trans (le_abs_self D₁)) ((hD₁ _).trans (le_abs_self D₁))
        (abs_nonneg _) (abs_nonneg D₁)
    exact (abs_sub _ _).trans (add_le_add hp le_rfl)
  have hC_b (v₀ v₁ : Fin (M + 1) → ℝ) : |C_fn v₀ v₁| ≤ C_bnd := by
    dsimp only [C_fn]
    have hM_pos : (0 : ℝ) < (M + 1 : ℕ) := by positivity
    have hcard : ((Finset.Ici n).card : ℝ) ≤ (M + 1 : ℕ) := by
      have hc : (Finset.Ici n).card ≤ Fintype.card (Fin (M + 1)) := (Finset.Ici n).card_le_univ
      rw [Fintype.card_fin] at hc; exact_mod_cast hc
    rw [abs_mul, abs_of_pos (inv_pos.2 hM_pos)]
    calc ((M + 1 : ℕ) : ℝ)⁻¹ * |∑ j ∈ Finset.Ici n, (deriv u (v₀ j) * deriv u (v₁ j) - rhat)|
        ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.Ici n, |deriv u (v₀ j) * deriv u (v₁ j) - rhat| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hM_pos).le
      _ ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ _j ∈ Finset.Ici n, C_bnd :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm_b v₀ v₁ j)
            (inv_pos.2 hM_pos).le
      _ = ((M + 1 : ℕ) : ℝ)⁻¹ * (((Finset.Ici n).card : ℝ) * C_bnd) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * (((M + 1 : ℕ) : ℝ) * C_bnd) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hCbnd0)
            (inv_pos.2 hM_pos).le
      _ = C_bnd := by field_simp
  let Ψ_j (j : Fin (M + 1)) (v : Fin 2 → Fin (M + 1) → ℝ) : ℝ :=
    (deriv u (v 0 j) * deriv u (v 1 j) - rhat) * C_fn (v 0) (v 1) ^ (2 * k + 1)
  have hΨ_m (j : Fin (M + 1)) : Measurable (Ψ_j j) := by
    have hdu (l : Fin 2) (m : Fin (M + 1)) :
        Measurable fun v : Fin 2 → Fin (M + 1) → ℝ => deriv u (v l m) :=
      (measurable_deriv u).comp ((measurable_pi_apply m).comp (measurable_pi_apply l))
    have hCm : Measurable fun v : Fin 2 → Fin (M + 1) → ℝ => C_fn (v 0) (v 1) :=
      (Finset.measurable_sum _ fun m _ =>
        ((hdu 0 m).mul (hdu 1 m)).sub_const rhat).const_mul _
    exact (((hdu 0 j).mul (hdu 1 j)).sub_const rhat).mul (hCm.pow_const (2 * k + 1))
  have hΨ_b (j : Fin (M + 1)) (v : Fin 2 → Fin (M + 1) → ℝ) :
      |Ψ_j j v| ≤ C_bnd ^ (2 * k + 2) := by
    dsimp only [Ψ_j]
    rw [abs_mul, abs_pow]
    calc |deriv u (v 0 j) * deriv u (v 1 j) - rhat| * |C_fn (v 0) (v 1)| ^ (2 * k + 1)
        ≤ C_bnd * C_bnd ^ (2 * k + 1) :=
          mul_le_mul (hterm_b (v 0) (v 1) j)
            (pow_le_pow_left₀ (abs_nonneg _) (hC_b (v 0) (v 1)) (2 * k + 1))
            (pow_nonneg (abs_nonneg _) _) hCbnd0
      _ = C_bnd ^ (2 * k + 2) := (pow_succ' C_bnd (2 * k + 1)).symm
  have hlast_mem : Fin.last M ∈ Finset.Ici n := Finset.mem_Ici.2 (Fin.le_last n)
  have hC_swap {j : Fin (M + 1)} (hj : j ∈ Finset.Ici n) (v₀ v₁ : Fin (M + 1) → ℝ) :
      C_fn (fun m => v₀ (Equiv.swap j (Fin.last M) m))
        (fun m => v₁ (Equiv.swap j (Fin.last M) m)) = C_fn v₀ v₁ := by
    dsimp only [C_fn]; congr 1
    refine Finset.sum_bij (fun m _ => Equiv.swap j (Fin.last M) m) ?_ ?_ ?_ ?_
    · intro m hm
      by_cases hmj : m = j
      · subst hmj; simpa using hlast_mem
      · by_cases hml : m = Fin.last M
        · subst hml; simpa using hj
        · rwa [Equiv.swap_apply_of_ne_of_ne hmj hml]
    · intro m₁ _ m₂ _ h
      exact (Equiv.swap j (Fin.last M)).injective h
    · intro m hm
      refine ⟨Equiv.swap j (Fin.last M) m, ?_, by simp⟩
      by_cases hmj : m = j
      · subst hmj; simpa using hlast_mem
      · by_cases hml : m = Fin.last M
        · subst hml; simpa using hj
        · rwa [Equiv.swap_apply_of_ne_of_ne hmj hml]
    · intros; rfl
  have hsym_j {j : Fin (M + 1)} (hj : j ∈ Finset.Ici n) :
      (∫ ω, ∫ σ, Ψ_j j (fun l m => S_fn ω (σ l) m) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
        ∫ ω, ∫ σ, Ψ_j (Fin.last M) (fun l m => S_fn ω (σ l) m)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
    have hsw := integral_interpolating_constraint_swap (N := N) (M := M) hu hB s q r
      j (Fin.last M) (hΨ_m (Fin.last M))
    rw [← hsw]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [Ψ_j]
    rw [hC_swap hj (S_fn ω (σ 0)) (S_fn ω (σ 1)), Equiv.swap_apply_right]
  let G_j (j : Fin (M + 1)) (ω : Ω)
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    Ψ_j j (fun l m => S_fn ω (σ l) m)
  have hGj_m (j : Fin (M + 1)) :
      Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => G_j j p.1 p.2 :=
    (hΨ_m j).comp (measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun m =>
      measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q m l)
  have hint_j (j : Fin (M + 1)) :
      Integrable (fun ω : Ω => ∫ σ, G_j j ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P :=
    integrable_integral_pi_tilted (P := P) (μ := μ_s) hEm_joint hν_prob
      (G := G_j j) (hGj_m j) (M := C_bnd ^ (2 * k + 2))
      (fun ω σ => hΨ_b j (fun l m => S_fn ω (σ l) m))
  have hin_j (j : Fin (M + 1)) (ω : Ω) :
      Integrable (G_j j ω) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
    Integrable.of_bound (Measurable.of_uncurry_left (hGj_m j)).aestronglyMeasurable
      (C_bnd ^ (2 * k + 2))
      (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hΨ_b j (fun l m => S_fn ω (σ l) m))
  have hsum := integral_integral_finset_sum_dep P
    (fun ω => Measure.pi fun _ : Fin 2 => ν_s ω) (Finset.Ici n) G_j
    (fun j _ ω => hin_j j ω) (fun j _ => hint_j j)
  have hpt_σ (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      ∑ j ∈ Finset.Ici n, G_j j ω σ =
        ((M + 1 : ℕ) : ℝ) * C_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2) := by
    dsimp only [G_j, Ψ_j]
    rw [← Finset.sum_mul]
    have hsum_c : ∑ j ∈ Finset.Ici n,
        (deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j) - rhat) =
        ((M + 1 : ℕ) : ℝ) * C_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) := by
      dsimp only [C_fn]
      have hM_ne : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hsum_c, pow_succ']; ring
  have hlhs :
      (∫ ω, ∫ σ, (∑ j ∈ Finset.Ici n, G_j j ω σ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
        ((M + 1 : ℕ) : ℝ) * ∫ ω, ∫ σ, C_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
    simp_rw [hpt_σ, integral_const_mul]
  have hrhs :
      (∑ j ∈ Finset.Ici n, ∫ ω, ∫ σ, G_j j ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
        ((Finset.Ici n).card : ℝ) *
          ∫ ω, ∫ σ, G_j (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
    rw [Finset.sum_congr rfl fun j hj => hsym_j hj, Finset.sum_const, nsmul_eq_mul]
  rw [hlhs, hrhs] at hsum
  have hM_pos : (0 : ℝ) < (M + 1 : ℕ) := by positivity
  have hmul : (((Finset.Ici n).card : ℝ) / ((M + 1 : ℕ) : ℝ)) *
      (∫ ω, ∫ σ, G_j (Fin.last M) ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) =
      (((Finset.Ici n).card : ℝ) *
        ∫ ω, ∫ σ, G_j (Fin.last M) ω σ
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P) / ((M + 1 : ℕ) : ℝ) :=
    div_mul_eq_mul_div _ _ _
  dsimp only [G_j, Ψ_j] at hsum hmul
  rw [hmul, ← hsum, mul_div_cancel_left₀ _ hM_pos.ne']

/-- Symmetry identity `ν_s(C'^{2k}) = ν_s(C_{n+1}^{2k})` when `n < M`. -/
private lemma integral_partial_constraint_erase_last_eq_succ
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r rhat : ℝ) (n : Fin (M + 1)) (hn : n.1 < M) (k : ℕ) :
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (j : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ j : Fin (M + 1), u (S_fn ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let ν_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
      μ_s.tilted (E_s ω)
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        (((M + 1 : ℕ) : ℝ)⁻¹ *
          ∑ j ∈ (Finset.Ici n).erase (Fin.last M),
            (deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j) - rhat)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        (((M + 1 : ℕ) : ℝ)⁻¹ *
          ∑ j ∈ Finset.Ici (⟨n.1 + 1, by omega⟩ : Fin (M + 1)),
            (deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j) - rhat)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P := by
  intro P_g P_z P_z' P μ_s S_fn E_s ν_s
  let n' : Fin (M + 1) := ⟨n.1 + 1, by omega⟩
  let Ψ (v : Fin 2 → Fin (M + 1) → ℝ) : ℝ :=
    (((M + 1 : ℕ) : ℝ)⁻¹ *
      ∑ l ∈ Finset.Ici n', (deriv u (v 0 l) * deriv u (v 1 l) - rhat)) ^ (2 * k)
  have hΨ_m : Measurable Ψ := by
    have hdu (i : Fin 2) (l : Fin (M + 1)) :
        Measurable fun v : Fin 2 → Fin (M + 1) → ℝ => deriv u (v i l) :=
      (measurable_deriv u).comp ((measurable_pi_apply l).comp (measurable_pi_apply i))
    exact ((Finset.measurable_sum _ fun l _ =>
      ((hdu 0 l).mul (hdu 1 l)).sub_const rhat).const_mul _).pow_const (2 * k)
  have hsw := integral_interpolating_constraint_swap (N := N) (M := M) hu hB s q r
    n (Fin.last M) hΨ_m
  rw [← hsw]
  refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
  dsimp only [Ψ]
  rw [← sum_Ici_erase_last_constraint_eq_swap n hn
    (fun j => deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j) - rhat)]

/-! ### Cavity-in-`M` step Eq. (2.106), induction Eq. (2.100), and Theorem 2.5.2 -/

/-- **Cavity-in-`M` bound Eq. (2.106) on `|ν_s((u'(S^0_M) u'(S^1_M) - r̂) C'^{2k+1})|`:**
applying `abs_integral_interp_deriv_mul_sub_rhat_le_holder` at `t = 1` with conjugate exponents
`τ₁ = (2k + 2)/(2k + 1)` and `τ₂ = 2k + 2` and weighted Young's inequality with parameter
`A = 2 (K_cav + 1) > 0` yields
`|ν_s(f*)| ≤ (1 / 2) ν_s(C'^{2k+2}) + (K_cav + 1) (2 (K_cav + 1))^{2k+1} ν_s((R_{1,2} - q)^{2k+2}) +
  K_cav / (N + 1) ν_s(|C'|^{2k+1})`. -/
private lemma exists_abs_integral_constraint_last_cavity_le (D : ℝ) :
    ∃ K_cav : ℝ, 0 ≤ K_cav ∧
      ∀ (N M : ℕ) {s q r : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1) (_hq_mem : q ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (k : ℕ) (n : Fin (M + 1)) (_hn : n.1 < M),
        let γ : Measure ℝ := gaussianReal 0 1
        let P₁ := ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ).prod
          (Measure.pi fun _ : Fin (M + 1) => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin (M + 1) => γ)
        let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (j : Fin (M + 1)) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
        let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
          (∑ j : Fin (M + 1), u (S_fn ω x j)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let ν_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
          μ_s.tilted (E_s ω)
        let rhat := perceptronRhat u q
        let C'_fn (v₀ v₁ : Fin (M + 1) → ℝ) : ℝ :=
          ((M + 1 : ℕ) : ℝ)⁻¹ *
            ∑ j ∈ (Finset.Ici n).erase (Fin.last M), (deriv u (v₀ j) * deriv u (v₁ j) - rhat)
        let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
        |∫ ω, ∫ σ, (deriv u (S_fn ω (σ 0) (Fin.last M)) *
              deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat) *
            C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
            ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁| ≤
          (1 / 2) * (∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
            ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) +
          (K_cav + 1) * (2 * (K_cav + 1)) ^ (2 * k + 1) *
            (∫ ω, ∫ σ, (R_obs σ - q) ^ (2 * k + 2) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) +
          (K_cav / ((N : ℝ) + 1)) *
            (∫ ω, ∫ σ, |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
              ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) := by
  obtain ⟨K_cav, hKcav0, h_cav⟩ := abs_integral_interp_deriv_mul_sub_rhat_le_holder (Fin 2) D
  refine ⟨K_cav, hKcav0, ?_⟩
  intro N M s q r hs hq_mem u hd hb k n hn γ P₁ μ_s S_fn E_s ν_s rhat C'_fn R_obs
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_le : ∀ x, u x ≤ |D| := hu.le_abs
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := hu.abs_deriv_le_abs
  have hrhat_mem : rhat ∈ Icc (0 : ℝ) (|D| ^ 2) :=
    rhat_mem_Icc hD₁ q (fun z => integrable_exp_cavityPath_new hu.measurable hD_le q z)
  let P₀ := ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ).prod
    (Measure.pi fun _ : Fin M => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
  let μ_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod (Measure.pi fun _ : Fin M => γ)
  let E₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (∑ j : Fin M, u (Real.sqrt s *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 j i * ((x₀.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 j + Real.sqrt (1 - q) * x₀.2 j))) +
    ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r
  let π_sp (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : PerceptronSpin N :=
    (Fin.init x₀.1, x₀.1 (Fin.last N))
  have hπ_m : Measurable π_sp :=
    (measurable_pi_iff.2 fun i => (measurable_pi_apply i.castSucc).comp measurable_fst).prodMk
      ((measurable_pi_apply (Fin.last N)).comp measurable_fst)
  have hE₀_m := measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hE₀_i (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x₀ => Real.exp (E₀ ω₀ x₀)) μ_base := by
    have hm : Measurable (E₀ ω₀) := Measurable.of_uncurry_left hE₀_m
    have hbd_0 (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E₀ ω₀ x₀ ≤ M * |D| + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r| := by
      refine add_le_add ((Finset.sum_le_sum fun _ _ => hD_le _).trans_eq (by simp))
        (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
    exact integrable_exp_of_ae_le hm.aemeasurable (ae_of_all _ hbd_0)
  let C'₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ((M + 1 : ℕ) : ℝ)⁻¹ *
      ∑ j ∈ Finset.Ici (⟨n.1, hn⟩ : Fin M),
        (deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 j i * (((a 0).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 j + Real.sqrt (1 - q) * (a 0).2 j)) *
        deriv u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 j i * (((a 1).1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 j + Real.sqrt (1 - q) * (a 1).2 j)) - rhat)
  let f₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    C'₀ ω₀ a ^ (2 * k + 1)
  have hC'₀_m : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => C'₀ p.1 p.2 :=
    (Finset.measurable_sum _ fun j _ =>
      (((measurable_deriv u).comp
        (measurable_interpField_replica_joint (L := N + 1) (M := M) s q j 0)).mul
        ((measurable_deriv u).comp
          (measurable_interpField_replica_joint (L := N + 1) (M := M) s q j 1))).sub_const
        rhat).const_mul _
  have hf₀_m : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => f₀ p.1 p.2 :=
    hC'₀_m.pow_const (2 * k + 1)
  have hC'₀_b (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |C'₀ ω₀ a| ≤ 2 * |D| ^ 2 := by
    dsimp only [C'₀]
    have hM_pos : (0 : ℝ) < (M + 1 : ℕ) := by positivity
    have hcard : ((Finset.Ici (⟨n.1, hn⟩ : Fin M)).card : ℝ) ≤ (M + 1 : ℕ) := by
      have hc : (Finset.Ici (⟨n.1, hn⟩ : Fin M)).card ≤ M := by
        simpa only [Fintype.card_fin] using (Finset.Ici (⟨n.1, hn⟩ : Fin M)).card_le_univ
      have hc' : (Finset.Ici (⟨n.1, hn⟩ : Fin M)).card ≤ M + 1 := by omega
      exact_mod_cast hc'
    rw [abs_mul, abs_of_pos (inv_pos.2 hM_pos)]
    calc ((M + 1 : ℕ) : ℝ)⁻¹ * |∑ j ∈ Finset.Ici (⟨n.1, hn⟩ : Fin M), _|
        ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.Ici (⟨n.1, hn⟩ : Fin M), |_| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hM_pos).le
      _ ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ _j ∈ Finset.Ici (⟨n.1, hn⟩ : Fin M), (2 * |D| ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
            abs_deriv_mul_sub_rhat_le hD₁ hrhat_mem _ _) (inv_pos.2 hM_pos).le
      _ = ((M + 1 : ℕ) : ℝ)⁻¹ * (((Finset.Ici (⟨n.1, hn⟩ : Fin M)).card : ℝ) * (2 * |D| ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * (((M + 1 : ℕ) : ℝ) * (2 * |D| ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcard (by positivity)) (inv_pos.2 hM_pos).le
      _ = 2 * |D| ^ 2 := by field_simp
  have hf₀_b (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (a : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      |f₀ ω₀ a| ≤ (2 * |D| ^ 2) ^ (2 * k + 1) := by
    dsimp only [f₀]; rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC'₀_b ω₀ a) (2 * k + 1)
  let τ₁ : ℝ := (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 1)
  let τ₂ : ℝ := 2 * (k : ℝ) + 2
  have hτ_conj : τ₁.HolderConjugate τ₂ := by
    have hm_pos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    simpa only [τ₁, τ₂, show (2 * (k : ℝ) + 1) + 1 = 2 * (k : ℝ) + 2 by ring] using
      Real.HolderConjugate.succ_div_self hm_pos
  have hP₀_prob : IsProbabilityMeasure P₀ := by dsimp only [P₀, γ]; infer_instance
  have hμb_fin : IsFiniteMeasure μ_base := inferInstance
  have hμb_ne : NeZero μ_base := inferInstance
  have hcav_raw := h_cav N P₀ μ_base hE₀_m hE₀_i π_sp hπ_m (by decide : (0 : Fin 2) ≠ 1)
    hs ⟨zero_le_one, le_rfl⟩ hq_mem hd hb hf₀_m hf₀_b hτ_conj
  dsimp only at hcav_raw
  -- Transport each integral in `hcav_raw` via `integral_pi_interpVar_last_split_eq`
  let splitΩ (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) :=
    (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
      Sum.elim (Sum.elim (Fin.init (ω.1.1 (Fin.last M)))
          (fun _ : Unit => ω.1.1 (Fin.last M) (Fin.last N)))
        (fun _ : Unit => ω.1.2 (Fin.last M)))
  let X₁ (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)
      (z : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp z.1))
      (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      Real.sqrt (1 - s) * Real.sqrt (1 - q) * z.2
  have hX_fn_eq (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)
      (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ)) :
      Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp y.1))
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ y.2 = X₁ w₁ (y.1, y.2 1) := by
    dsimp only [X₁]; simp [dotProduct, Fin.sum_univ_two]
  have hX₁_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      X₁ (splitΩ ω).2 (interpStateLastSplit (N + 1) M x) = S_fn ω x (Fin.last M) := by
    rw [interpStateLastSplit_apply]
    dsimp only [X₁, splitΩ, π_sp, cavityCoef, S_fn]
    rw [sumElim_dotProduct_sumElim, smul_dotProduct, smul_eq_mul, sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h_sqrt1 : Real.sqrt (1 / ((N : ℝ) + 1)) = (Real.sqrt (N + 1 : ℕ))⁻¹ := by
      rw [one_div, Real.sqrt_inv]; push_cast; rfl
    rw [h_sqrt1, Fin.sum_univ_castSucc]
    simp only [Fin.init_def]
    have hsum_i :
        (∑ i : Fin N, (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i.castSucc : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i.castSucc) =
        (Real.sqrt (N + 1 : ℕ))⁻¹ *
          ∑ i : Fin N, ω.1.1 (Fin.last M) i.castSucc * ((x.1 i.castSucc : ℤ) : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum_i]; ring
  have hC'₀_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      C'₀ (splitΩ ω).1 (fun l => (interpStateLastSplit (N + 1) M (σ l)).1) =
        C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) := by
    simp only [interpStateLastSplit_apply, C'₀, C'_fn, splitΩ, S_fn, Fin.init_def]
    congr 1
    refine Finset.sum_bij (fun j _ => j.castSucc) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Ici] at hj
      rw [Finset.mem_erase, Finset.mem_Ici]
      exact ⟨Fin.castSucc_ne_last j, hj⟩
    · intro j₁ _ j₂ _ h
      exact Fin.castSucc_injective M h
    · intro m hm
      rw [Finset.mem_erase, Finset.mem_Ici] at hm
      rcases Fin.eq_castSucc_of_ne_last hm.1 with ⟨j, rfl⟩
      exact ⟨j, Finset.mem_Ici.2 hm.2, rfl⟩
    · intros; rfl
  have hf₀_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      f₀ (splitΩ ω).1 (fun l => (interpStateLastSplit (N + 1) M (σ l)).1) =
        C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1) := by
    dsimp only [f₀]; rw [hC'₀_split]
  have hcoef_idx (idx : (Fin N ⊕ Unit) ⊕ Unit) :
      Measurable fun τ : Fin (N + 1) → ℤˣ =>
        (Sum.elim (Real.sqrt s • cavityCoef N 1 (Fin.init τ, τ (Fin.last N)))
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) idx := by
    rcases idx with (i | _) | _
    · dsimp only [cavityCoef, Sum.elim_inl, Pi.smul_apply, smul_eq_mul, Fin.init_def]
      exact measurable_const.mul
        (measurable_const.mul (measurable_units_cast.comp (measurable_pi_apply i.castSucc)))
    · dsimp only [cavityCoef, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
      exact measurable_const.mul
        (measurable_const.mul (measurable_units_cast.comp (measurable_pi_apply (Fin.last N))))
    · exact measurable_const
  have hf₀_lift_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
      f₀ q_p.1.1 (fun l => (q_p.2 l).1) := by
    have hl (l : Fin 2) (j : Fin M) : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
        Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, q_p.1.1.1.1 j i * ((((q_p.2 l).1.1 i : ℤ) : ℝ))) +
          Real.sqrt (1 - s) *
            (Real.sqrt q * q_p.1.1.1.2 j + Real.sqrt (1 - q) * (q_p.2 l).1.2 j) := by
      have hg_sum : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
          ∑ i : Fin (N + 1), q_p.1.1.1.1 j i * ((((q_p.2 l).1.1 i : ℤ) : ℝ)) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hgi : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
            (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => q_p.1.1.1.1 j i :=
          (measurable_pi_apply i).comp ((measurable_pi_apply j).comp
            (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))))
        have hσi : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
            (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => (((q_p.2 l).1.1 i : ℤ) : ℝ) :=
          measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp
              (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd))))
        exact hgi.mul hσi
      have hzj : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => q_p.1.1.1.2 j :=
        (measurable_pi_apply j).comp
          (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      have hξj : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => (q_p.2 l).1.2 j :=
        (measurable_pi_apply j).comp
          (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd)))
      exact ((hg_sum.const_mul _).const_mul _).add
        (((hzj.const_mul _).add (hξj.const_mul _)).const_mul _)
    exact ((Finset.measurable_sum _ fun j _ =>
      (((measurable_deriv u).comp (hl 0 j)).mul
        ((measurable_deriv u).comp (hl 1 j))).sub_const rhat).const_mul _).pow_const (2 * k + 1)
  let H_w (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    f₀ p.1 (fun l => (z l).1) * (deriv u (X₁ p.2 (z 0)) * deriv u (X₁ p.2 (z 1)))
  have hHw_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => H_w q_p.1 q_p.2 := by
    have hzl (l : Fin 2) : Measurable fun q_p :
        ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => deriv u (X₁ q_p.1.2 (q_p.2 l)) := by
      have hd1 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
          Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (q_p.2 l).1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ q_p.1.2 := by
        simp only [dotProduct]
        refine Finset.measurable_sum _ fun idx _ => ?_
        have ha : Measurable fun q_p :
            ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
              (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
            (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
            (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (q_p.2 l).1))
              (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) idx :=
          (hcoef_idx idx).comp (measurable_fst.comp
            (measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd)))
        exact ha.mul ((measurable_pi_apply idx).comp (measurable_snd.comp measurable_fst))
      have hd2 : Measurable fun q_p :
          ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) =>
          Real.sqrt (1 - s) * Real.sqrt (1 - q) * (q_p.2 l).2 :=
        measurable_const.mul (measurable_snd.comp ((measurable_pi_apply l).comp measurable_snd))
      exact (measurable_deriv u).comp (hd1.add hd2)
    exact hf₀_lift_m.mul ((hzl 0).mul (hzl 1))
  have htr_w := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_w) hHw_m
  let H_u (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    f₀ p.1 (fun l => (z l).1)
  have htr_u := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_u) hf₀_lift_m
  let H_1 (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    |f₀ p.1 (fun l => (z l).1)|
  have hH1_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => H_1 q_p.1 q_p.2 :=
    continuous_abs.measurable.comp hf₀_lift_m
  have htr_1 := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_1) hH1_m
  let H_p (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    |f₀ p.1 (fun l => (z l).1)| ^ τ₁
  have htr_p := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_p) (hH1_m.pow_const τ₁)
  let d_spin (σ τ : PerceptronSpin N) : ℝ :=
    |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
      ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
  let H_ov (_p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) : ℝ :=
    d_spin (π_sp (z 0).1) (π_sp (z 1).1) ^ τ₂
  have hHov_m : Measurable fun q_p :
      ((((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ) => H_ov q_p.1 q_p.2 := by
    have hsum_sp : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
        ((∑ i : Fin N,
            ((((z 0).1.1 i.castSucc : ℤ) : ℝ) * (((z 1).1.1 i.castSucc : ℤ) : ℝ))) +
          ((((z 0).1.1 (Fin.last N) : ℤ) : ℝ) * (((z 1).1.1 (Fin.last N) : ℤ) : ℝ))) /
          (N + 1) - q := by
      have hs1 : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
          ∑ i : Fin N, ((((z 0).1.1 i.castSucc : ℤ) : ℝ) * (((z 1).1.1 i.castSucc : ℤ) : ℝ)) :=
        Finset.measurable_sum _ fun i _ =>
          (measurable_units_cast.comp ((measurable_pi_apply i.castSucc).comp
            (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 0))))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i.castSucc).comp
            (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 1)))))
      have hs2 : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
          ((((z 0).1.1 (Fin.last N) : ℤ) : ℝ) * (((z 1).1.1 (Fin.last N) : ℤ) : ℝ)) :=
        (measurable_units_cast.comp ((measurable_pi_apply (Fin.last N)).comp
          (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 0))))).mul
        (measurable_units_cast.comp ((measurable_pi_apply (Fin.last N)).comp
          (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply 1)))))
      exact ((hs1.add hs2).div_const _).sub_const q
    have habs_z : Measurable fun z : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × ℝ =>
        d_spin (π_sp (z 0).1) (π_sp (z 1).1) := by
      simpa only [d_spin, π_sp, Fin.init_def, Real.norm_eq_abs] using hsum_sp.norm
    exact (habs_z.pow_const τ₂).comp measurable_snd
  have htr_ov := integral_pi_interpVar_last_split_eq (N := N) (M := M) (R := Fin 2)
    hu.measurable hD_le s q r (H := H_ov) hHov_m
  dsimp only at htr_w htr_u htr_1 htr_p htr_ov
  -- Identify the transported integrals
  have hw_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        f₀ p.1 (fun l => (a l).1) *
          (deriv u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (a 0).1))
              (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
            ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
              Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ (a 0).2) *
          deriv u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp (a 1).1))
              (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
            ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
              Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ (a 1).2))
        ∂(Measure.pi fun _ : Fin 2 =>
          (((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted fun x =>
            u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1) *
          (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
    refine (integral_congr_ae (ae_of_all _ fun p =>
      integral_congr_ae (ae_of_all _ fun a => ?_))).trans
      (htr_w.trans (integral_congr_ae (ae_of_all _ fun ω =>
        integral_congr_ae (ae_of_all _ fun σ => ?_))))
    · dsimp only [H_w]; rw [hX_fn_eq, hX_fn_eq]
    · dsimp only [H_w]; rw [hf₀_split, hX₁_split, hX₁_split]
  have hu_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        f₀ p.1 (fun l => (a l).1)
        ∂(Measure.pi fun _ : Fin 2 =>
          (((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted fun x =>
            u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
    refine htr_u.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => ?_)))
    dsimp only [H_u]; exact hf₀_split ω σ
  have h1_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        |f₀ p.1 (fun l => (a l).1)|
        ∂(Measure.pi fun _ : Fin 2 =>
          (((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted fun x =>
            u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ, |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
    refine htr_1.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => ?_)))
    dsimp only [H_1]; rw [hf₀_split ω σ, abs_pow]
  have hp_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        |f₀ p.1 (fun l => (a l).1)| ^ τ₁
        ∂(Measure.pi fun _ : Fin 2 =>
          (((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted fun x =>
            u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
    refine htr_p.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => ?_)))
    dsimp only [H_p]
    rw [hf₀_split ω σ, abs_pow, ← Real.rpow_natCast _ (2 * k + 1), ← Real.rpow_mul (abs_nonneg _)]
    have hexp : ((2 * k + 1 : ℕ) : ℝ) * τ₁ = ((2 * k + 2 : ℕ) : ℝ) := by
      dsimp only [τ₁]
      have hne : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      push_cast; field_simp
    rw [hexp, Real.rpow_natCast, Even.pow_abs ⟨k + 1, by ring⟩]
  have hov_eq :
      (∫ p, ∫ a : Fin 2 → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Fin 2 → ℝ),
        d_spin (π_sp (a 0).1) (π_sp (a 1).1) ^ τ₂
        ∂(Measure.pi fun _ : Fin 2 =>
          (((μ_base.tilted (E₀ p.1)).prod (Measure.pi fun _ : Fin 2 => γ)).tilted fun x =>
            u (Sum.elim (Real.sqrt s • cavityCoef N 1 (π_sp x.1))
                (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.2 +
              ![Real.sqrt s * Real.sqrt ((1 - (1 : ℝ)) / (N + 1)),
                Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => γ))) =
      ∫ ω, ∫ σ, (R_obs σ - q) ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
    refine htr_ov.trans (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun σ => ?_)))
    dsimp only [H_ov]
    have hτ2_nat : τ₂ = ((2 * k + 2 : ℕ) : ℝ) := by dsimp only [τ₂]; push_cast; ring
    rw [hτ2_nat, Real.rpow_natCast]
    dsimp only [d_spin, π_sp, R_obs]
    simp only [interpStateLastSplit_apply, Fin.init_def]
    rw [Even.pow_abs ⟨k + 1, by ring⟩]
    congr 1
    rw [Fin.sum_univ_castSucc, div_eq_inv_mul]
  rw [hw_eq, hu_eq, h1_eq, hp_eq, hov_eq] at hcav_raw
  -- Combine `weighted - rhat * unweighted` into a single integral
  let Ω₁ := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
  have hP₁_prob : IsProbabilityMeasure P₁ := by dsimp only [P₁, γ]; infer_instance
  have hEm₁ := measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu.measurable s q r
  have hEb₁ (ω : Ω₁) (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * |D| +
        ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hD_le _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν₁_prob (ω : Ω₁) : IsProbabilityMeasure (ν_s ω) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm₁).aemeasurable (ae_of_all _ (hEb₁ ω))
  let F_w (ω : Ω₁) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1) *
      (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)))
  let F_u (ω : Ω₁) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
  have hFu_m : Measurable fun p : Ω₁ × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
      F_u p.1 p.2 :=
    ((Finset.measurable_sum _ fun j _ =>
      (((measurable_deriv u).comp
        (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q j 0)).mul
        ((measurable_deriv u).comp
          (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q j 1))).sub_const
        rhat).const_mul _).pow_const (2 * k + 1)
  have hFw_m : Measurable fun p : Ω₁ × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
      F_w p.1 p.2 :=
    hFu_m.mul (((measurable_deriv u).comp
      (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q (Fin.last M) 0)).mul
      ((measurable_deriv u).comp
        (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q (Fin.last M) 1)))
  have hFu_b (ω : Ω₁) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      |F_u ω σ| ≤ (2 * |D| ^ 2) ^ (2 * k + 1) := by
    dsimp only [F_u]; rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_partial_constraint_sub_le hD₁ hrhat_mem _ _ _) (2 * k + 1)
  have hFw_b (ω : Ω₁) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      |F_w ω σ| ≤ (2 * |D| ^ 2) ^ (2 * k + 1) * |D| ^ 2 := by
    dsimp only [F_w]; rw [abs_mul, abs_mul]
    exact mul_le_mul (hFu_b ω σ)
      (by rw [sq]; exact mul_le_mul (hD₁ _) (hD₁ _) (abs_nonneg _) (abs_nonneg D))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
  have hint_w := integrable_integral_pi_tilted (P := P₁) (μ := μ_s) hEm₁ hν₁_prob
    (G := F_w) hFw_m (M := (2 * |D| ^ 2) ^ (2 * k + 1) * |D| ^ 2) hFw_b
  have hint_u := integrable_integral_pi_tilted (P := P₁) (μ := μ_s) hEm₁ hν₁_prob
    (G := F_u) hFu_m (M := (2 * |D| ^ 2) ^ (2 * k + 1)) hFu_b
  have hlhs_comb :
      (∫ ω, ∫ σ, (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) -
          rhat) * C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) =
      (∫ ω, ∫ σ, F_w ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) -
        rhat * (∫ ω, ∫ σ, F_u ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) := by
    have hpt (ω : Ω₁) :
        (∫ σ, (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) -
            rhat) * C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) =
        (∫ σ, F_w ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) -
          rhat * (∫ σ, F_u ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) := by
      have hin_w : Integrable (F_w ω) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
        Integrable.of_bound (Measurable.of_uncurry_left hFw_m).aestronglyMeasurable _
          (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hFw_b ω σ)
      have hin_u : Integrable (F_u ω) (Measure.pi fun _ : Fin 2 => ν_s ω) :=
        Integrable.of_bound (Measurable.of_uncurry_left hFu_m).aestronglyMeasurable _
          (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hFu_b ω σ)
      have heq (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
          (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat) *
            C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1) =
          F_w ω σ - rhat * F_u ω σ := by
        dsimp only [F_w, F_u]; ring
      simp_rw [heq]
      rw [integral_sub hin_w (hin_u.const_mul rhat), integral_const_mul]
    simp_rw [hpt]
    rw [integral_sub hint_w (hint_u.const_mul rhat), integral_const_mul]
  rw [hlhs_comb]
  refine hcav_raw.trans ?_
  -- Apply weighted Young's inequality with `A = 2 * (K_cav + 1) > 0`
  let X_m : ℝ := ∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
    ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  let Y_m : ℝ := ∫ ω, ∫ σ, (R_obs σ - q) ^ (2 * k + 2)
    ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  let I_m : ℝ := ∫ ω, ∫ σ, |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
    ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  have hXm0 : 0 ≤ X_m :=
    integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k + 1, by ring⟩ _
  have hYm0 : 0 ≤ Y_m :=
    integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k + 1, by ring⟩ _
  have hIm0 : 0 ≤ I_m :=
    integral_nonneg fun _ => integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  let A : ℝ := 2 * (K_cav + 1)
  have hA_pos : 0 < A := by dsimp only [A]; positivity
  have hyoung := rpow_inv_mul_rpow_inv_le_div_add_mul hτ_conj hA_pos hXm0 hYm0
  have hquot : τ₂ / τ₁ = ((2 * k + 1 : ℕ) : ℝ) := by
    dsimp only [τ₁, τ₂]
    have hne : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    push_cast; field_simp
  rw [hquot, Real.rpow_natCast] at hyoung
  have hK_le : K_cav ≤ K_cav + 1 := by linarith
  have hKA_le : K_cav * (X_m / A) ≤ (1 / 2) * X_m := by
    have h1 : K_cav / A ≤ 1 / 2 := by
      dsimp only [A]
      rw [div_le_div_iff₀ hA_pos zero_lt_two]
      linarith
    calc K_cav * (X_m / A) = (K_cav / A) * X_m := by ring
      _ ≤ (1 / 2) * X_m := mul_le_mul_of_nonneg_right h1 hXm0
  calc K_cav * (X_m ^ (1 / τ₁) * Y_m ^ (1 / τ₂) + 1 / ((N : ℝ) + 1) * I_m)
      ≤ K_cav * ((X_m / A + A ^ (2 * k + 1) * Y_m) + 1 / ((N : ℝ) + 1) * I_m) :=
        mul_le_mul_of_nonneg_left (add_le_add hyoung le_rfl) hKcav0
    _ = K_cav * (X_m / A) + K_cav * (A ^ (2 * k + 1) * Y_m) +
          (K_cav / ((N : ℝ) + 1)) * I_m := by ring
    _ ≤ (1 / 2) * X_m + (K_cav + 1) * A ^ (2 * k + 1) * Y_m +
          (K_cav / ((N : ℝ) + 1)) * I_m := by
        refine add_le_add (add_le_add hKA_le ?_) le_rfl
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hK_le (mul_nonneg (by positivity) hYm0)

/-- **One-step induction estimate for `ν_s(C_n^{2k+2})` (`n < M`) in Theorem 2.5.2:**
under `M + 1 ≤ N + 1`, `ν_s((R_{1,2} - q)^{2k+2}) ≤ (64 (k + 1) / (N + 1))^{k+1}`, and the
induction hypothesis `ν_s(C_m^{2k}) ≤ (k L / (M + 1))^k` for all `m : Fin (M + 1)` with
`L = 512 (K_cav + 1)² + 64 |D|² + 64`, we have `ν_s(C_n^{2k+2}) ≤ ((k + 1) L / (M + 1))^{k+1}`. -/
private lemma integral_partial_constraint_step_lt
    {D K_cav : ℝ} (hKcav0 : 0 ≤ K_cav)
    (h_cav_step : ∀ (N M : ℕ) {s q r : ℝ}, s ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
      ∀ {u : ℝ → ℝ}, (∀ j < 3, Differentiable ℝ (iteratedDeriv j u)) →
      (∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D) →
      ∀ (k : ℕ) (n : Fin (M + 1)), n.1 < M →
      let γ : Measure ℝ := gaussianReal 0 1
      let P₁ := ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ).prod
        (Measure.pi fun _ : Fin (M + 1) => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
      let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
        (Measure.pi fun _ : Fin (M + 1) => γ)
      let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
          (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (j : Fin (M + 1)) : ℝ :=
        Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
      let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
          (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
        (∑ j : Fin (M + 1), u (S_fn ω x j)) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
      let ν_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
        μ_s.tilted (E_s ω)
      let rhat := perceptronRhat u q
      let C'_fn (v₀ v₁ : Fin (M + 1) → ℝ) : ℝ :=
        ((M + 1 : ℕ) : ℝ)⁻¹ *
          ∑ j ∈ (Finset.Ici n).erase (Fin.last M), (deriv u (v₀ j) * deriv u (v₁ j) - rhat)
      let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
        ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
      |∫ ω, ∫ σ, (deriv u (S_fn ω (σ 0) (Fin.last M)) *
            deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat) *
          C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁| ≤
        (1 / 2) * (∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) +
        (K_cav + 1) * (2 * (K_cav + 1)) ^ (2 * k + 1) *
          (∫ ω, ∫ σ, (R_obs σ - q) ^ (2 * k + 2) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) +
        (K_cav / ((N : ℝ) + 1)) *
          (∫ ω, ∫ σ, |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
            ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁))
    {N M : ℕ} {s q r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hq_mem : q ∈ Icc (0 : ℝ) 1)
    {u : ℝ → ℝ} (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
    (hMN : ((M + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1)
    {k : ℕ} (n : Fin (M + 1)) (hn : n.1 < M) :
    let L : ℝ := 512 * (K_cav + 1) ^ 2 + 64 * |D| ^ 2 * (K_cav + 1) + 128 * |D| ^ 4 + 64
    let γ : Measure ℝ := gaussianReal 0 1
    let P₁ := ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => γ).prod
      (Measure.pi fun _ : Fin (M + 1) => γ)).prod (Measure.pi fun _ : Fin (N + 1) => γ)
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => γ)
    let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (j : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ j : Fin (M + 1), u (S_fn ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let ν_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :=
      μ_s.tilted (E_s ω)
    let rhat := perceptronRhat u q
    let C_fn (m : Fin (M + 1)) (v₀ v₁ : Fin (M + 1) → ℝ) : ℝ :=
      ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.Ici m, (deriv u (v₀ j) * deriv u (v₁ j) - rhat)
    let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
    (∫ ω, ∫ σ, (R_obs σ - q) ^ (2 * k + 2) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ ≤
        (64 * ((k : ℝ) + 1) / ((N : ℝ) + 1)) ^ (k + 1)) →
    (∀ m : Fin (M + 1),
      ∫ ω, ∫ σ, C_fn m (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ ≤
        ((k : ℝ) * L / ((M + 1 : ℕ) : ℝ)) ^ k) →
    ∫ ω, ∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ ≤
      (((k : ℝ) + 1) * L / ((M + 1 : ℕ) : ℝ)) ^ (k + 1) := by
  intro L γ P₁ μ_s S_fn E_s ν_s rhat C_fn R_obs hR_ov ih
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_le : ∀ x, u x ≤ |D| := hu.le_abs
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := hu.abs_deriv_le_abs
  have hrhat_mem : rhat ∈ Icc (0 : ℝ) (|D| ^ 2) :=
    rhat_mem_Icc hD₁ q (fun z => integrable_exp_cavityPath_new hu.measurable hD_le q z)
  let M₁ : ℝ := (M + 1 : ℕ)
  have hM₁ : 0 < M₁ := by dsimp only [M₁]; positivity
  have hL0 : 0 < L := by dsimp only [L]; positivity
  let Ω := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
  have hP₁_prob : IsProbabilityMeasure P₁ := by dsimp only [P₁, γ]; infer_instance
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu.measurable s q r
  have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * |D| +
        ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hD_le _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν_prob (ω : Ω) : IsProbabilityMeasure (ν_s ω) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable (ae_of_all _ (hEb ω))
  let C'_fn (v₀ v₁ : Fin (M + 1) → ℝ) : ℝ :=
    M₁⁻¹ * ∑ j ∈ (Finset.Ici n).erase (Fin.last M), (deriv u (v₀ j) * deriv u (v₁ j) - rhat)
  let V_n : ℝ := ∫ ω, ∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
    ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  let V' : ℝ := ∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
    ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  let W_n : ℝ := ∫ ω, ∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
    ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  let W' : ℝ := ∫ ω, ∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
    ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁
  have hVn0 : 0 ≤ V_n :=
    integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k + 1, by ring⟩ _
  have hWn0 : 0 ≤ W_n :=
    integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k, by ring⟩ _
  have hW'0 : 0 ≤ W' :=
    integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k, by ring⟩ _
  -- Helper for integrability of any bounded measurable constraint observable
  have hint_obs {G : Ω → (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) → ℝ}
      (hGm : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => G p.1 p.2)
      {C_G : ℝ} (hGb : ∀ ω σ, |G ω σ| ≤ C_G) :
      (∀ ω, Integrable (G ω) (Measure.pi fun _ : Fin 2 => ν_s ω)) ∧
        Integrable (fun ω => ∫ σ, G ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) P₁ :=
    ⟨fun ω => Integrable.of_bound (Measurable.of_uncurry_left hGm).aestronglyMeasurable C_G
        (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hGb ω σ),
     integrable_integral_pi_tilted (P := P₁) (μ := μ_s) hEm_joint hν_prob
        (G := G) hGm (M := C_G) hGb⟩
  have hmono_obs {G₁ G₂ : Ω → (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) → ℝ}
      (hGm₁ : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => G₁ p.1 p.2)
      {C₁ : ℝ} (hGb₁ : ∀ ω σ, |G₁ ω σ| ≤ C₁)
      (hGm₂ : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => G₂ p.1 p.2)
      {C₂ : ℝ} (hGb₂ : ∀ ω σ, |G₂ ω σ| ≤ C₂)
      (hle : ∀ ω σ, G₁ ω σ ≤ G₂ ω σ) :
      (∫ ω, ∫ σ, G₁ ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤
        ∫ ω, ∫ σ, G₂ ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ :=
    integral_mono (hint_obs hGm₁ hGb₁).2 (hint_obs hGm₂ hGb₂).2 fun ω =>
      integral_mono ((hint_obs hGm₁ hGb₁).1 ω) ((hint_obs hGm₂ hGb₂).1 ω) (hle ω)
  have hCn_m : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
      C_fn n (S_fn p.1 (p.2 0)) (S_fn p.1 (p.2 1)) :=
    (Finset.measurable_sum _ fun j _ =>
      (((measurable_deriv u).comp
        (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q j 0)).mul
        ((measurable_deriv u).comp
          (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q j 1))).sub_const
        rhat).const_mul _
  have hC'_m : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
      C'_fn (S_fn p.1 (p.2 0)) (S_fn p.1 (p.2 1)) :=
    (Finset.measurable_sum _ fun j _ =>
      (((measurable_deriv u).comp
        (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q j 0)).mul
        ((measurable_deriv u).comp
          (measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q j 1))).sub_const
        rhat).const_mul _
  have hUL_m : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
      deriv u (S_fn p.1 (p.2 0) (Fin.last M)) * deriv u (S_fn p.1 (p.2 1) (Fin.last M)) - rhat := by
    have hm0 := measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q (Fin.last M) 0
    have hm1 := measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q (Fin.last M) 1
    exact (((measurable_deriv u).comp hm0).mul ((measurable_deriv u).comp hm1)).sub_const rhat
  -- Pointwise bounds on `C_n`, `C'`, and `C_n - C'`
  have hCn_b (v₀ v₁ : Fin (M + 1) → ℝ) : |C_fn n v₀ v₁| ≤ 2 * |D| ^ 2 :=
    abs_partial_constraint_sub_le hD₁ hrhat_mem (Finset.Ici n) v₀ v₁
  have hC'_b (v₀ v₁ : Fin (M + 1) → ℝ) : |C'_fn v₀ v₁| ≤ 2 * |D| ^ 2 :=
    abs_partial_constraint_sub_le hD₁ hrhat_mem ((Finset.Ici n).erase (Fin.last M)) v₀ v₁
  have hC_diff (v₀ v₁ : Fin (M + 1) → ℝ) :
      |C_fn n v₀ v₁ - C'_fn v₀ v₁| ≤ 2 * |D| ^ 2 / M₁ := by
    have hlast_in : Fin.last M ∈ Finset.Ici n := Finset.mem_Ici.2 (Fin.le_last n)
    have hsub : C_fn n v₀ v₁ - C'_fn v₀ v₁ =
        M₁⁻¹ * (deriv u (v₀ (Fin.last M)) * deriv u (v₁ (Fin.last M)) - rhat) := by
      dsimp only [C_fn, C'_fn, M₁]
      rw [← mul_sub, ← Finset.sum_erase_add (Finset.Ici n) _ hlast_in]
      ring
    rw [hsub, abs_mul, abs_of_pos (inv_pos.2 hM₁)]
    calc M₁⁻¹ * |deriv u (v₀ (Fin.last M)) * deriv u (v₁ (Fin.last M)) - rhat|
        ≤ M₁⁻¹ * (2 * |D| ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_deriv_mul_sub_rhat_le hD₁ hrhat_mem _ _) (inv_pos.2 hM₁).le
      _ = 2 * |D| ^ 2 / M₁ := by ring
  -- Induction bounds on `W_n` and `W'`
  let B_prev : ℝ := ((k : ℝ) * L / M₁) ^ k
  have hBprev0 : 0 ≤ B_prev := by dsimp only [B_prev]; positivity
  have hWn_le : W_n ≤ B_prev := ih n
  have hW'_le : W' ≤ B_prev := by
    have heq := integral_partial_constraint_erase_last_eq_succ (N := N) (M := M)
      hu.measurable hD_le s q r rhat n hn k
    dsimp only [W', C'_fn, M₁]
    rw [heq]
    exact ih ⟨n.1 + 1, by omega⟩
  -- Step 1: V_n ≤ ν_s(f_tilde) via `integral_partial_constraint_succ_eq_last`
  let f_tilde (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat) *
      C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
  let f_star (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
    (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat) *
      C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)
  have hVn_le_ftilde : V_n ≤ ∫ ω, ∫ σ, f_tilde ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
    have hsym := integral_partial_constraint_succ_eq_last (N := N) (M := M)
      hu.measurable hD_le hD₁ s q r rhat n k
    have hVn_eq : V_n = (((Finset.Ici n).card : ℝ) / M₁) *
        ∫ ω, ∫ σ, f_tilde ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := hsym
    rw [hVn_eq]
    have hcard_pos : 0 < ((Finset.Ici n).card : ℝ) / M₁ := by
      have hne : (Finset.Ici n).Nonempty := ⟨n, Finset.mem_Ici.2 le_rfl⟩
      have hcp : (0 : ℝ) < (Finset.Ici n).card := by exact_mod_cast hne.card_pos
      exact div_pos hcp hM₁
    have hcard_le : ((Finset.Ici n).card : ℝ) / M₁ ≤ 1 := by
      rw [div_le_one hM₁]
      have hc : (Finset.Ici n).card ≤ Fintype.card (Fin (M + 1)) := (Finset.Ici n).card_le_univ
      rw [Fintype.card_fin] at hc; dsimp only [M₁]; exact_mod_cast hc
    have hft_nn : 0 ≤ ∫ ω, ∫ σ, f_tilde ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
      have : 0 ≤ (((Finset.Ici n).card : ℝ) / M₁) *
          ∫ ω, ∫ σ, f_tilde ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := by
        rw [← hVn_eq]; exact hVn0
      exact nonneg_of_mul_nonneg_right this hcard_pos
    exact mul_le_of_le_one_left hft_nn hcard_le
  -- Step 2: Eq. (2.103)-(2.104): ν_s(f_tilde) ≤ |ν_s(f_star)| + (8 (2k + 1) |D|⁴ / M₁) * B_prev
  have hftilde_le :
      (∫ ω, ∫ σ, f_tilde ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤
        |∫ ω, ∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁| +
          (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev := by
    let Err₁ (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (4 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) *
        (C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k) +
          C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))
    have hpt_split (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        f_tilde ω σ ≤ f_star ω σ + Err₁ ω σ := by
      have hdiff : f_tilde ω σ - f_star ω σ ≤ |f_tilde ω σ - f_star ω σ| := le_abs_self _
      have habs_diff : |f_tilde ω σ - f_star ω σ| ≤ Err₁ ω σ := by
        have hfac : f_tilde ω σ - f_star ω σ =
            (deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat) *
              (C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1) -
                C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)) := by
          dsimp only [f_tilde, f_star]; ring
        rw [hfac, abs_mul]
        have hu_last := abs_deriv_mul_sub_rhat_le hD₁ hrhat_mem
          (S_fn ω (σ 0) (Fin.last M)) (S_fn ω (σ 1) (Fin.last M))
        have hodd := abs_pow_odd_sub_pow_odd_le k
          (C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1))) (C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)))
        have hc_sub := hC_diff (S_fn ω (σ 0)) (S_fn ω (σ 1))
        calc |deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat| *
              |C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1) -
                C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 1)|
            ≤ (2 * |D| ^ 2) * ((2 * (k : ℝ) + 1) * (2 * |D| ^ 2 / M₁) *
                (C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k) +
                  C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))) := by
              refine mul_le_mul hu_last ?_ (abs_nonneg _) (by positivity)
              exact hodd.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hc_sub (by positivity))
                (add_nonneg (Even.pow_nonneg ⟨k, by ring⟩ _) (Even.pow_nonneg ⟨k, by ring⟩ _)))
          _ = Err₁ ω σ := by dsimp only [Err₁]; ring
      linarith
    have hft_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |f_tilde ω σ| ≤ (2 * |D| ^ 2) ^ (2 * k + 2) := by
      dsimp only [f_tilde]; rw [abs_mul, abs_pow]
      calc |deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat| *
            |C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
          ≤ (2 * |D| ^ 2) * (2 * |D| ^ 2) ^ (2 * k + 1) :=
            mul_le_mul (abs_deriv_mul_sub_rhat_le hD₁ hrhat_mem _ _)
              (pow_le_pow_left₀ (abs_nonneg _) (hCn_b _ _) (2 * k + 1))
              (pow_nonneg (abs_nonneg _) _) (by positivity)
        _ = (2 * |D| ^ 2) ^ (2 * k + 2) := (pow_succ' _ (2 * k + 1)).symm
    have hfs_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |f_star ω σ| ≤ (2 * |D| ^ 2) ^ (2 * k + 2) := by
      dsimp only [f_star]; rw [abs_mul, abs_pow]
      calc |deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M)) - rhat| *
            |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
          ≤ (2 * |D| ^ 2) * (2 * |D| ^ 2) ^ (2 * k + 1) :=
            mul_le_mul (abs_deriv_mul_sub_rhat_le hD₁ hrhat_mem _ _)
              (pow_le_pow_left₀ (abs_nonneg _) (hC'_b _ _) (2 * k + 1))
              (pow_nonneg (abs_nonneg _) _) (by positivity)
        _ = (2 * |D| ^ 2) ^ (2 * k + 2) := (pow_succ' _ (2 * k + 1)).symm
    let C_err1 : ℝ := (4 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * (2 * (2 * |D| ^ 2) ^ (2 * k))
    have hCn2k_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)| ≤ (2 * |D| ^ 2) ^ (2 * k) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCn_b _ _) (2 * k)
    have hC'2k_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)| ≤ (2 * |D| ^ 2) ^ (2 * k) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC'_b _ _) (2 * k)
    have hErr1_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |Err₁ ω σ| ≤ C_err1 := by
      dsimp only [Err₁, C_err1]
      rw [abs_of_nonneg (mul_nonneg (by positivity)
        (add_nonneg (Even.pow_nonneg ⟨k, by ring⟩ _) (Even.pow_nonneg ⟨k, by ring⟩ _)))]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 := (le_abs_self _).trans (hCn2k_b ω σ)
      have h2 := (le_abs_self _).trans (hC'2k_b ω σ)
      linarith
    have hErr1_m : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        Err₁ p.1 p.2 :=
      ((hCn_m.pow_const (2 * k)).add (hC'_m.pow_const (2 * k))).const_mul _
    have hm := hmono_obs (G₁ := f_tilde) (hUL_m.mul (hCn_m.pow_const (2 * k + 1))) hft_b
      (G₂ := fun ω σ => f_star ω σ + Err₁ ω σ)
      ((hUL_m.mul (hC'_m.pow_const (2 * k + 1))).add hErr1_m)
      (fun ω σ => (abs_add_le _ _).trans (add_le_add (hfs_b ω σ) (hErr1_b ω σ))) hpt_split
    have hfs_int := hint_obs (G := f_star) (hUL_m.mul (hC'_m.pow_const (2 * k + 1))) hfs_b
    have hCn2k_int := hint_obs (G := fun ω σ => C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))
      (hCn_m.pow_const (2 * k)) hCn2k_b
    have hC'2k_int := hint_obs (G := fun ω σ => C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))
      (hC'_m.pow_const (2 * k)) hC'2k_b
    have hErr1_int := hint_obs hErr1_m hErr1_b
    have hrhs_add :
        (∫ ω, ∫ σ, (f_star ω σ + Err₁ ω σ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) =
          (∫ ω, ∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) +
          (4 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * (W_n + W') := by
      have hpt_add (ω : Ω) :
          (∫ σ, (f_star ω σ + Err₁ ω σ) ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) =
            (∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) +
              (4 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) *
                ((∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
                    ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) +
                  (∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
                    ∂(Measure.pi fun _ : Fin 2 => ν_s ω))) := by
        rw [integral_add (hfs_int.1 ω) (hErr1_int.1 ω)]
        congr 1
        dsimp only [Err₁]
        rw [integral_const_mul, integral_add (hCn2k_int.1 ω) (hC'2k_int.1 ω)]
      simp_rw [hpt_add]
      have hadd_int : Integrable
          (fun ω => (∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
              ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) +
            (∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
              ∂(Measure.pi fun _ : Fin 2 => ν_s ω))) P₁ :=
        hCn2k_int.2.add hC'2k_int.2
      rw [integral_add hfs_int.2 (hadd_int.const_mul _),
        integral_const_mul, integral_add hCn2k_int.2 hC'2k_int.2]
    rw [hrhs_add] at hm
    calc (∫ ω, ∫ σ, f_tilde ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁)
        ≤ |∫ ω, ∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁| +
            (4 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * (B_prev + B_prev) :=
          hm.trans (add_le_add (le_abs_self _)
            (mul_le_mul_of_nonneg_left (add_le_add hWn_le hW'_le) (by positivity)))
      _ = |∫ ω, ∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁| +
            (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev := by ring
  -- Step 3: Compare `V'` back to `V_n` via `abs_pow_even_sub_pow_even_le`
  have hV'_le : V' ≤ V_n + (8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev := by
    let Err₂ (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (4 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) *
        (C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k) +
          C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))
    have hpt_v (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2) ≤
          C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2) + Err₂ ω σ := by
      let x := C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))
      let y := C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1))
      have hev := abs_pow_even_sub_pow_even_le k x y
      have hxy : |x - y| ≤ 2 * |D| ^ 2 / M₁ := by
        rw [abs_sub_comm]; exact hC_diff (S_fn ω (σ 0)) (S_fn ω (σ 1))
      have hx2k1 : |x| ^ (2 * k + 1) ≤ (2 * |D| ^ 2) * x ^ (2 * k) := by
        rw [pow_succ', Even.pow_abs ⟨k, by ring⟩]
        exact mul_le_mul_of_nonneg_right (hC'_b _ _) (Even.pow_nonneg ⟨k, by ring⟩ _)
      have hy2k1 : |y| ^ (2 * k + 1) ≤ (2 * |D| ^ 2) * y ^ (2 * k) := by
        rw [pow_succ', Even.pow_abs ⟨k, by ring⟩]
        exact mul_le_mul_of_nonneg_right (hCn_b _ _) (Even.pow_nonneg ⟨k, by ring⟩ _)
      have habs_le : |x ^ (2 * k + 2) - y ^ (2 * k + 2)| ≤ Err₂ ω σ := by
        calc |x ^ (2 * k + 2) - y ^ (2 * k + 2)|
            ≤ (2 * (k : ℝ) + 2) * |x - y| * (|x| ^ (2 * k + 1) + |y| ^ (2 * k + 1)) := hev
          _ ≤ (2 * (k : ℝ) + 2) * (2 * |D| ^ 2 / M₁) *
                ((2 * |D| ^ 2) * x ^ (2 * k) + (2 * |D| ^ 2) * y ^ (2 * k)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hxy (by positivity))
                (add_le_add hx2k1 hy2k1) (by positivity) (by positivity)
          _ = Err₂ ω σ := by dsimp only [Err₂, x, y]; ring
      have h1 := (le_abs_self (x ^ (2 * k + 2) - y ^ (2 * k + 2))).trans habs_le
      linarith
    have hV'b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)| ≤ (2 * |D| ^ 2) ^ (2 * k + 2) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC'_b _ _) (2 * k + 2)
    have hVnb (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)| ≤ (2 * |D| ^ 2) ^ (2 * k + 2) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCn_b _ _) (2 * k + 2)
    let C_err2 : ℝ := (4 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * (2 * (2 * |D| ^ 2) ^ (2 * k))
    have hErr2_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |Err₂ ω σ| ≤ C_err2 := by
      dsimp only [Err₂, C_err2]
      rw [abs_of_nonneg (mul_nonneg (by positivity)
        (add_nonneg (Even.pow_nonneg ⟨k, by ring⟩ _) (Even.pow_nonneg ⟨k, by ring⟩ _)))]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k) ≤ (2 * |D| ^ 2) ^ (2 * k) :=
        (le_abs_self _).trans (by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC'_b _ _) (2 * k))
      have h2 : C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k) ≤ (2 * |D| ^ 2) ^ (2 * k) :=
        (le_abs_self _).trans (by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCn_b _ _) (2 * k))
      linarith
    have hCn2k_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)| ≤ (2 * |D| ^ 2) ^ (2 * k) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCn_b _ _) (2 * k)
    have hC'2k_b (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)| ≤ (2 * |D| ^ 2) ^ (2 * k) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC'_b _ _) (2 * k)
    have hErr2_m : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
        Err₂ p.1 p.2 :=
      ((hC'_m.pow_const (2 * k)).add (hCn_m.pow_const (2 * k))).const_mul _
    have hm := hmono_obs (G₁ := fun ω σ => C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2))
      (hC'_m.pow_const (2 * k + 2)) hV'b
      (G₂ := fun ω σ => C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2) + Err₂ ω σ)
      ((hCn_m.pow_const (2 * k + 2)).add hErr2_m)
      (fun ω σ => (abs_add_le _ _).trans (add_le_add (hVnb ω σ) (hErr2_b ω σ))) hpt_v
    have hVn_int := hint_obs
      (G := fun ω σ => C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2))
      (hCn_m.pow_const (2 * k + 2)) hVnb
    have hC'2k_int := hint_obs (G := fun ω σ => C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))
      (hC'_m.pow_const (2 * k)) hC'2k_b
    have hCn2k_int := hint_obs (G := fun ω σ => C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))
      (hCn_m.pow_const (2 * k)) hCn2k_b
    have hErr2_int := hint_obs hErr2_m hErr2_b
    have hrhs_add :
        (∫ ω, ∫ σ, (C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2) + Err₂ ω σ)
          ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) =
          V_n + (4 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * (W' + W_n) := by
      have hpt_add (ω : Ω) :
          (∫ σ, (C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2) + Err₂ ω σ)
            ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) =
            (∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k + 2)
              ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) +
              (4 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) *
                ((∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
                    ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) +
                  (∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
                    ∂(Measure.pi fun _ : Fin 2 => ν_s ω))) := by
        rw [integral_add (hVn_int.1 ω) (hErr2_int.1 ω)]
        congr 1
        dsimp only [Err₂]
        rw [integral_const_mul, integral_add (hC'2k_int.1 ω) (hCn2k_int.1 ω)]
      simp_rw [hpt_add]
      have hadd_int : Integrable
          (fun ω => (∫ σ, C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
              ∂(Measure.pi fun _ : Fin 2 => ν_s ω)) +
            (∫ σ, C_fn n (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
              ∂(Measure.pi fun _ : Fin 2 => ν_s ω))) P₁ :=
        hC'2k_int.2.add hCn2k_int.2
      rw [integral_add hVn_int.2 (hadd_int.const_mul _),
        integral_const_mul, integral_add hC'2k_int.2 hCn2k_int.2]
    rw [hrhs_add] at hm
    calc V' ≤ V_n + (4 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * (B_prev + B_prev) :=
          hm.trans (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (add_le_add hW'_le hWn_le) (by positivity)))
      _ = V_n + (8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev := by ring
  -- Step 4: Bound `ν_s(|C'|^{2k+1}) ≤ 2 |D|² B_prev` and `|ν_s(f_star)|`
  have hI_C'_le :
      (∫ ω, ∫ σ, |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤
      2 * |D| ^ 2 * B_prev := by
    have hpt_2k1 (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
        |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1) ≤
          (2 * |D| ^ 2) * C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k) := by
      rw [pow_succ', Even.pow_abs ⟨k, by ring⟩]
      exact mul_le_mul_of_nonneg_right (hC'_b _ _) (Even.pow_nonneg ⟨k, by ring⟩ _)
    have hm := hmono_obs
      (G₁ := fun ω σ => |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1))
      ((continuous_abs.measurable.comp hC'_m).pow_const (2 * k + 1))
      (C₁ := (2 * |D| ^ 2) ^ (2 * k + 1))
      (fun ω σ => by
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC'_b _ _) (2 * k + 1))
      (G₂ := fun ω σ => (2 * |D| ^ 2) * C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k))
      ((hC'_m.pow_const (2 * k)).const_mul (2 * |D| ^ 2))
      (C₂ := (2 * |D| ^ 2) * (2 * |D| ^ 2) ^ (2 * k))
      (fun ω σ => by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |D| ^ 2), abs_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (hC'_b _ _) (2 * k)) (by positivity))
      hpt_2k1
    have hpull : (∫ ω, ∫ σ, (2 * |D| ^ 2) * C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) = (2 * |D| ^ 2) * W' := by
      dsimp only [W']
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun _ => by dsimp only; rw [integral_const_mul])
    exact (hm.trans_eq hpull).trans (mul_le_mul_of_nonneg_left hW'_le (by positivity))
  have hcav_app := h_cav_step N M (r := r) hs hq_mem hd hb k n hn
  dsimp only at hcav_app
  -- Use `M + 1 ≤ N + 1` to bound `1 / (N + 1) ≤ 1 / M₁` and the overlap power
  have hinv_le : 1 / ((N : ℝ) + 1) ≤ 1 / M₁ :=
    one_div_le_one_div_of_le hM₁ hMN
  have hR_M :
      (∫ ω, ∫ σ, (R_obs σ - q) ^ (2 * k + 2) ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) ≤
        (64 * ((k : ℝ) + 1) / M₁) ^ (k + 1) := by
    refine hR_ov.trans (pow_le_pow_left₀ (by positivity) ?_ (k + 1))
    have h1 : 64 * ((k : ℝ) + 1) / ((N : ℝ) + 1) = 64 * ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1)) :=
      div_eq_mul_one_div _ _
    have h2 : 64 * ((k : ℝ) + 1) / M₁ = 64 * ((k : ℝ) + 1) * (1 / M₁) :=
      div_eq_mul_one_div _ _
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hinv_le (by positivity)
  -- Assemble the step!
  let B_next : ℝ := (((k : ℝ) + 1) * L / M₁) ^ (k + 1)
  have hB_prev_le_next : B_prev ≤ (((k : ℝ) + 1) * L / M₁) ^ k :=
    pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hL0.le) hM₁.le) k
  -- Bound the overlap contribution by `(1 / 4) * B_next`
  have hov_term_le :
      (K_cav + 1) * (2 * (K_cav + 1)) ^ (2 * k + 1) * (64 * ((k : ℝ) + 1) / M₁) ^ (k + 1) ≤
        (1 / 4) * B_next := by
    have h1 : (K_cav + 1) * (2 * (K_cav + 1)) ^ (2 * k + 1) =
        (1 / 2) * (4 * (K_cav + 1) ^ 2) ^ (k + 1) := by
      have hexp : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      calc (K_cav + 1) * (2 * (K_cav + 1)) ^ (2 * k + 1)
          = (1 / 2) * ((2 * (K_cav + 1)) * (2 * (K_cav + 1)) ^ (2 * k + 1)) := by ring
        _ = (1 / 2) * (2 * (K_cav + 1)) ^ (2 * k + 1 + 1) := by rw [← pow_succ']
        _ = (1 / 2) * ((2 * (K_cav + 1)) ^ 2) ^ (k + 1) := by rw [hexp, pow_mul]
        _ = (1 / 2) * (4 * (K_cav + 1) ^ 2) ^ (k + 1) := by congr 2; ring
    have h2 : 256 * (K_cav + 1) ^ 2 ≤ (1 / 2) * L := by
      dsimp only [L]
      nlinarith [sq_nonneg (K_cav + 1), mul_nonneg (sq_nonneg |D|) (by positivity : 0 ≤ K_cav + 1),
        pow_nonneg (abs_nonneg D) 4]
    calc (K_cav + 1) * (2 * (K_cav + 1)) ^ (2 * k + 1) * (64 * ((k : ℝ) + 1) / M₁) ^ (k + 1)
        = (1 / 2) * ((4 * (K_cav + 1) ^ 2) * (64 * ((k : ℝ) + 1) / M₁)) ^ (k + 1) := by
          rw [h1, mul_assoc, ← mul_pow]
      _ = (1 / 2) * (((k : ℝ) + 1) * (256 * (K_cav + 1) ^ 2) / M₁) ^ (k + 1) := by
          congr 2; ring
      _ ≤ (1 / 2) * (((k : ℝ) + 1) * ((1 / 2) * L) / M₁) ^ (k + 1) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ (k + 1))
            (by norm_num)
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (by positivity)) hM₁.le
      _ = (1 / 2) * ((1 / 2) ^ (k + 1) * B_next) := by
          dsimp only [B_next]
          congr 1
          rw [← mul_pow]
          congr 1; ring
      _ ≤ (1 / 2) * ((1 / 2) * B_next) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by norm_num)
          calc ((1 : ℝ) / 2) ^ (k + 1)
              ≤ ((1 : ℝ) / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 2 := pow_one _
      _ = (1 / 4) * B_next := by ring
  -- Bound the sum of the remaining `B_prev / M₁` terms by `(1 / 4) B_next`
  have hrem_terms_le :
      (1 / 2) * ((8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev) +
        (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev) +
        (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev ≤
      (1 / 4) * B_next := by
    have hKcav_M : (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev) ≤
        (2 * K_cav * |D| ^ 2 / M₁) * B_prev := by
      have h1 : K_cav / ((N : ℝ) + 1) ≤ K_cav / M₁ := by
        have hd1 : K_cav / ((N : ℝ) + 1) = K_cav * (1 / ((N : ℝ) + 1)) := div_eq_mul_one_div _ _
        have hd2 : K_cav / M₁ = K_cav * (1 / M₁) := div_eq_mul_one_div _ _
        rw [hd1, hd2]
        exact mul_le_mul_of_nonneg_left hinv_le hKcav0
      calc (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev)
          ≤ (K_cav / M₁) * (2 * |D| ^ 2 * B_prev) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (2 * K_cav * |D| ^ 2 / M₁) * B_prev := by ring
    have hcoef_le :
        8 * ((k : ℝ) + 1) * |D| ^ 4 + 2 * K_cav * |D| ^ 2 + 8 * (2 * (k : ℝ) + 1) * |D| ^ 4 ≤
          (1 / 4) * (((k : ℝ) + 1) * L) := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hk1_pos : (0 : ℝ) ≤ (k : ℝ) + 1 := by linarith
      have ht1 : 8 * ((k : ℝ) + 1) * |D| ^ 4 + 8 * (2 * (k : ℝ) + 1) * |D| ^ 4 ≤
          24 * ((k : ℝ) + 1) * |D| ^ 4 := by
        have h2k : 2 * (k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by linarith
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h2k (by norm_num : (0 : ℝ) ≤ 8))
          (pow_nonneg (abs_nonneg D) 4)
        linarith
      have ht2 : 2 * K_cav * |D| ^ 2 ≤ 2 * ((k : ℝ) + 1) * (|D| ^ 2 * (K_cav + 1)) := by
        calc 2 * K_cav * |D| ^ 2
            ≤ 2 * (K_cav + 1) * |D| ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg |D|)
          _ = 2 * 1 * (|D| ^ 2 * (K_cav + 1)) := by ring
          _ ≤ 2 * ((k : ℝ) + 1) * (|D| ^ 2 * (K_cav + 1)) :=
              mul_le_mul_of_nonneg_right (by linarith)
                (mul_nonneg (sq_nonneg |D|) (by linarith))
      have hsum_coef : 24 * |D| ^ 4 + 2 * (|D| ^ 2 * (K_cav + 1)) ≤ (1 / 4) * L := by
        dsimp only [L]
        have hA : 0 ≤ (K_cav + 1) ^ 2 := sq_nonneg _
        have hB : 0 ≤ |D| ^ 2 * (K_cav + 1) := mul_nonneg (sq_nonneg _) (by linarith)
        have hC : 0 ≤ |D| ^ 4 := pow_nonneg (abs_nonneg D) 4
        linarith
      calc 8 * ((k : ℝ) + 1) * |D| ^ 4 + 2 * K_cav * |D| ^ 2 + 8 * (2 * (k : ℝ) + 1) * |D| ^ 4
          ≤ 24 * ((k : ℝ) + 1) * |D| ^ 4 + 2 * ((k : ℝ) + 1) * (|D| ^ 2 * (K_cav + 1)) := by
            linarith
        _ = ((k : ℝ) + 1) * (24 * |D| ^ 4 + 2 * (|D| ^ 2 * (K_cav + 1))) := by ring
        _ ≤ ((k : ℝ) + 1) * ((1 / 4) * L) := mul_le_mul_of_nonneg_left hsum_coef hk1_pos
        _ = (1 / 4) * (((k : ℝ) + 1) * L) := by ring
    calc (1 / 2) * ((8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev) +
          (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev) +
          (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev
        ≤ (1 / 2) * ((8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev) +
            (2 * K_cav * |D| ^ 2 / M₁) * B_prev +
            (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev :=
          add_le_add (add_le_add le_rfl hKcav_M) le_rfl
      _ = ((8 * ((k : ℝ) + 1) * |D| ^ 4 + 2 * K_cav * |D| ^ 2 +
            8 * (2 * (k : ℝ) + 1) * |D| ^ 4) / M₁) * B_prev := by ring
      _ ≤ (((1 / 4) * (((k : ℝ) + 1) * L)) / M₁) * (((k : ℝ) + 1) * L / M₁) ^ k :=
          mul_le_mul (div_le_div_of_nonneg_right hcoef_le hM₁.le) hB_prev_le_next
            hBprev0 (by positivity)
      _ = (1 / 4) * B_next := by
          dsimp only [B_next]; rw [pow_succ']; ring
  -- Combine everything: V_n ≤ (1/2) V_n + (1/4) B_next + (1/4) B_next, so (1/2) V_n ≤ (1/2) B_next!
  have hVn_rec : V_n ≤ (1 / 2) * V_n + (1 / 2) * B_next := by
    have hfstar_le :
        |∫ ω, ∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁| ≤
          (1 / 2) * (V_n + (8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev) +
          (1 / 4) * B_next +
          (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev) := by
      calc |∫ ω, ∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁|
          ≤ (1 / 2) * V' +
              (K_cav + 1) * (2 * (K_cav + 1)) ^ (2 * k + 1) *
                (∫ ω, ∫ σ, (R_obs σ - q) ^ (2 * k + 2)
                  ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) +
              (K_cav / ((N : ℝ) + 1)) *
                (∫ ω, ∫ σ, |C'_fn (S_fn ω (σ 0)) (S_fn ω (σ 1))| ^ (2 * k + 1)
                  ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁) := hcav_app
        _ ≤ (1 / 2) * (V_n + (8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev) +
              (1 / 4) * B_next +
              (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev) :=
            add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left hV'_le (by norm_num))
                ((mul_le_mul_of_nonneg_left hR_M (by positivity)).trans hov_term_le))
              (mul_le_mul_of_nonneg_left hI_C'_le (by positivity))
    calc V_n ≤ ∫ ω, ∫ σ, f_tilde ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁ := hVn_le_ftilde
      _ ≤ |∫ ω, ∫ σ, f_star ω σ ∂(Measure.pi fun _ : Fin 2 => ν_s ω) ∂P₁| +
            (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev := hftilde_le
      _ ≤ ((1 / 2) * (V_n + (8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev) +
            (1 / 4) * B_next +
            (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev)) +
            (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev := add_le_add hfstar_le le_rfl
      _ = (1 / 2) * V_n + (1 / 4) * B_next +
            ((1 / 2) * ((8 * (2 * (k : ℝ) + 2) * |D| ^ 4 / M₁) * B_prev) +
              (K_cav / ((N : ℝ) + 1)) * (2 * |D| ^ 2 * B_prev) +
              (8 * (2 * (k : ℝ) + 1) * |D| ^ 4 / M₁) * B_prev) := by ring
      _ ≤ (1 / 2) * V_n + (1 / 4) * B_next + (1 / 4) * B_next :=
          add_le_add le_rfl hrem_terms_le
      _ = (1 / 2) * V_n + (1 / 2) * B_next := by ring
  linarith

/-- **Talagrand Theorem 2.5.2 (Eq. (2.99)), uniformly along the `s`-interpolating path:**
Given `D ∈ ℝ`, there exist constants `K, L ≥ 0` (chosen before `N, M, s, u, q, r, k`) such that
whenever `u` satisfies (2.7), `(M / (N + 1)) * K ≤ 1`, `(q, r)` solves (2.68), and `s ∈ [0, 1]`,
for every `k : ℕ`:
$$\nu_s\!\left(\left(\frac{1}{N + 1} \sum_{j < M}
    u'(S_{j, s}^1) u'(S_{j, s}^2) - r\right)^{2k}\right)
  \le \left(\frac{\alpha k L}{N + 1}\right)^k, \quad \alpha = \frac{M}{N + 1}$$
(with the `k = 0` power equal to `1`). -/
theorem integral_interpolating_empirical_variance_pow_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        (k : ℕ),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_s := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (S_fn ω x j)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            (((N : ℝ) + 1)⁻¹ *
              ∑ j : Fin M, deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j) - r) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
          ((M : ℝ) / ((N : ℝ) + 1) * (k : ℝ) * L / ((N : ℝ) + 1)) ^ k := by
  obtain ⟨K_ov, hKov0, h_ov⟩ := integral_interpolating_overlap_pow_le D
  obtain ⟨K_cav, hKcav0, h_cav_step⟩ := exists_abs_integral_constraint_last_cavity_le D
  obtain ⟨K_k1, L_k1, hKk10, hLk10, h_k1⟩ := integral_interpolating_deriv_empirical_variance_le D
  let K : ℝ := max (max K_ov K_k1) 1
  let L_ind : ℝ := 512 * (K_cav + 1) ^ 2 + 64 * |D| ^ 2 * (K_cav + 1) + 128 * |D| ^ 4 + 64
  let L : ℝ := max L_ind L_k1
  refine ⟨K, L, by positivity, by positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr k
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_le : ∀ x, u x ≤ |D| := hu.le_abs
  have hD₁ : ∀ x, |deriv u x| ≤ |D| := hu.abs_deriv_le_abs
  -- Case 1: k = 0 (`x^0 = 1 ≤ 1`)
  rcases k with _ | k
  · intro P_g P_z P_z' P_s μ_s S_fn E_s
    let Ω := ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)
    have hP_prob : IsProbabilityMeasure P_s := by dsimp only [P_s, P_g, P_z, P_z']; infer_instance
    have hEm := measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
    have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E_s ω x ≤ M * |D| + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
      refine add_le_add ((Finset.sum_le_sum fun _ _ => hD_le _).trans_eq (by simp))
        (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
    have hν_prob (ω : Ω) : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
      isProbabilityMeasure_tilted_of_ae_le
        (Measurable.of_uncurry_left hEm).aemeasurable (ae_of_all _ (hEb ω))
    simp
  -- Case 2: M = 0 (`r = 0`, empty sum is `0`, `0^{2(k+1)} = 0 ≤ 0`)
  rcases M with _ | M
  · intro P_g P_z P_z' P_s μ_s S_fn E_s
    have hr0 : r = 0 := by simp [hr]
    simp [hr0]
  -- Case 3: M + 1 ≥ 1 and k + 1 ≥ 1: run induction on `k'` over `C_m` with `L_ind`
  intro P_g P_z P_z' P_s μ_s S_fn E_s
  let α : ℝ := ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hK_ge1 : 1 ≤ K := le_max_right _ 1
  have hα_le1 : α ≤ 1 := by
    have h1 : α * 1 ≤ α * K := mul_le_mul_of_nonneg_left hK_ge1 hα0
    linarith [hα]
  have hMN : ((M + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
    exact (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)).1 hα_le1
  have hα_ov : ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) * K_ov ≤ 1 := by
    have hle : K_ov ≤ K := (le_max_left K_ov K_k1).trans (le_max_left _ 1)
    exact (mul_le_mul_of_nonneg_left hle hα0).trans hα
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
    rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  let rhat := perceptronRhat u q
  have hrhat_mem : rhat ∈ Icc (0 : ℝ) (|D| ^ 2) :=
    rhat_mem_Icc hD₁ q (fun z => integrable_exp_cavityPath_new hu.measurable hD_le q z)
  let Ω := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
  have hP_prob : IsProbabilityMeasure P_s := by dsimp only [P_s, P_g, P_z, P_z']; infer_instance
  have hEm := measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu.measurable s q r
  have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * |D| +
        ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hD_le _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν_prob (ω : Ω) : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm).aemeasurable (ae_of_all _ (hEb ω))
  let C_fn (m : Fin (M + 1)) (v₀ v₁ : Fin (M + 1) → ℝ) : ℝ :=
    ((M + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.Ici m, (deriv u (v₀ j) * deriv u (v₁ j) - rhat)
  -- Prove by induction on `k'` for ALL `k' : ℕ` and ALL `m : Fin (M + 1)` that
  -- `ν_s(C_m^{2 k'}) ≤ (k' * L_ind / (M + 1))^{k'}`!
  have hall : ∀ k' : ℕ, ∀ m : Fin (M + 1),
      ∫ ω, ∫ σ, C_fn m (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * k')
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
      ((k' : ℝ) * L_ind / ((M + 1 : ℕ) : ℝ)) ^ k' := by
    intro k'
    induction k' with
    | zero =>
      intro m; simp
    | succ k' ih =>
      intro m
      by_cases hm_lt : m.1 < M
      · -- `m < M`: apply `integral_partial_constraint_step_lt`!
        -- Wait: when `M + 1 > (k' + 1) L_ind` or not, `integral_partial_constraint_step_lt` works
        -- unconditionally for ALL `M, N, k'`! Let's check!
        have hR_ov := h_ov N (M + 1) hs hd hb hα_ov hq hr (k' + 1)
        dsimp only at hR_ov
        have hstep := integral_partial_constraint_step_lt hKcav0 h_cav_step
          hs hq_mem hd hb hMN m hm_lt
          (by simpa only [show 2 * (k' + 1) = 2 * k' + 2 by ring,
            show ((k' + 1 : ℕ) : ℝ) = (k' : ℝ) + 1 by push_cast; ring] using hR_ov)
          ih
        simpa only [show 2 * (k' + 1) = 2 * k' + 2 by ring,
          show ((k' + 1 : ℕ) : ℝ) = (k' : ℝ) + 1 by push_cast; ring] using hstep
      · -- `m = Fin.last M`: `|C_{last}| ≤ 2 |D|² / (M + 1)`, so
        -- `C_{last}^{2(k'+1)} ≤ (4 |D|⁴ / (M + 1)²)^{k'+1} ≤ ((k'+1) L_ind / (M + 1))^{k'+1}`!
        have hm_last : m = Fin.last M := by
          ext; have := m.2; simp [Fin.last]; omega
        rw [hm_last]
        have hpt_last (v₀ v₁ : Fin (M + 1) → ℝ) :
            C_fn (Fin.last M) v₀ v₁ ^ (2 * (k' + 1)) ≤
              (((k' + 1 : ℕ) : ℝ) * L_ind / ((M + 1 : ℕ) : ℝ)) ^ (k' + 1) := by
          have hIci_last : Finset.Ici (Fin.last M) = {Fin.last M} := by
            ext j
            simp only [Finset.mem_Ici, Finset.mem_singleton]
            exact ⟨fun h => le_antisymm (Fin.le_last j) h, fun h => by rw [h]⟩
          have habs_last : |C_fn (Fin.last M) v₀ v₁| ≤ 2 * |D| ^ 2 / ((M + 1 : ℕ) : ℝ) := by
            dsimp only [C_fn]
            rw [hIci_last, Finset.sum_singleton, abs_mul,
              abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (M + 1 : ℕ)))]
            calc ((M + 1 : ℕ) : ℝ)⁻¹ *
                  |deriv u (v₀ (Fin.last M)) * deriv u (v₁ (Fin.last M)) - rhat|
                ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * (2 * |D| ^ 2) :=
                  mul_le_mul_of_nonneg_left (abs_deriv_mul_sub_rhat_le hD₁ hrhat_mem _ _)
                    (by positivity)
              _ = 2 * |D| ^ 2 / ((M + 1 : ℕ) : ℝ) := by ring
          have hsq : C_fn (Fin.last M) v₀ v₁ ^ 2 ≤
              ((k' + 1 : ℕ) : ℝ) * L_ind / ((M + 1 : ℕ) : ℝ) := by
            rw [← sq_abs]
            calc |C_fn (Fin.last M) v₀ v₁| ^ 2
                ≤ (2 * |D| ^ 2 / ((M + 1 : ℕ) : ℝ)) ^ 2 :=
                  pow_le_pow_left₀ (abs_nonneg _) habs_last 2
              _ = 4 * |D| ^ 4 / (((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ)) := by
                  rw [div_pow]; ring
              _ ≤ 4 * |D| ^ 4 / ((M + 1 : ℕ) : ℝ) := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  have hM1 : (1 : ℝ) ≤ (M + 1 : ℕ) := by
                    exact_mod_cast Nat.succ_pos M
                  have hM_sq : ((M + 1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) := by
                    calc ((M + 1 : ℕ) : ℝ) = 1 * ((M + 1 : ℕ) : ℝ) := (one_mul _).symm
                      _ ≤ ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) :=
                          mul_le_mul_of_nonneg_right hM1 (by positivity)
                  exact mul_le_mul_of_nonneg_left hM_sq (by positivity)
              _ ≤ ((k' + 1 : ℕ) : ℝ) * L_ind / ((M + 1 : ℕ) : ℝ) := by
                  refine div_le_div_of_nonneg_right ?_ (by positivity)
                  have hk1 : (1 : ℝ) ≤ (k' + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k'
                  have hL_ge : 4 * |D| ^ 4 ≤ L_ind := by
                    dsimp only [L_ind]
                    nlinarith [sq_nonneg (K_cav + 1),
                      mul_nonneg (sq_nonneg |D|) (by positivity : 0 ≤ K_cav + 1),
                      pow_nonneg (abs_nonneg D) 4]
                  calc 4 * |D| ^ 4 ≤ 1 * L_ind := by linarith
                    _ ≤ ((k' + 1 : ℕ) : ℝ) * L_ind :=
                        mul_le_mul_of_nonneg_right hk1 (by positivity)
          calc C_fn (Fin.last M) v₀ v₁ ^ (2 * (k' + 1))
              = (C_fn (Fin.last M) v₀ v₁ ^ 2) ^ (k' + 1) := pow_mul _ 2 (k' + 1)
            _ ≤ (((k' + 1 : ℕ) : ℝ) * L_ind / ((M + 1 : ℕ) : ℝ)) ^ (k' + 1) :=
                pow_le_pow_left₀ (sq_nonneg _) hsq (k' + 1)
        refine (le_abs_self _).trans ?_
        exact abs_integral_le_of_forall_abs_le P_s fun ω =>
          abs_integral_le_of_forall_abs_le _ fun σ => by
            rw [abs_of_nonneg (Even.pow_nonneg ⟨k' + 1, by ring⟩ _)]
            exact hpt_last (S_fn ω (σ 0)) (S_fn ω (σ 1))
  -- Now specialize `hall (k + 1) 0` and scale by `α^{2(k + 1)}`!
  have hC0 := hall (k + 1) 0
  have hpt_scale (ω : Ω) (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      (((N : ℝ) + 1)⁻¹ *
        ∑ j : Fin (M + 1), deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j) - r) ^
          (2 * (k + 1)) =
      α ^ (2 * (k + 1)) * C_fn 0 (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * (k + 1)) := by
    rw [← mul_pow]
    congr 1
    dsimp only [C_fn, α]
    have hIci0 : (Finset.Ici (0 : Fin (M + 1))) = Finset.univ := by ext j; simp
    rw [hIci0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hr]
    have hM_ne : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hN_ne : ((N : ℝ) + 1) ≠ 0 := by positivity
    dsimp only [rhat]
    field_simp
  simp_rw [hpt_scale, integral_const_mul]
  have hL_le : L_ind ≤ L := le_max_left L_ind L_k1
  calc α ^ (2 * (k + 1)) *
        (∫ ω, ∫ σ, C_fn 0 (S_fn ω (σ 0)) (S_fn ω (σ 1)) ^ (2 * (k + 1))
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s)
      ≤ α ^ (2 * (k + 1)) *
          (((k + 1 : ℕ) : ℝ) * L_ind / ((M + 1 : ℕ) : ℝ)) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hC0 (by positivity)
    _ ≤ α ^ (2 * (k + 1)) *
          (((k + 1 : ℕ) : ℝ) * L / ((M + 1 : ℕ) : ℝ)) ^ (k + 1) := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ (k + 1))
          (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL_le (by positivity)) (by positivity)
    _ = (((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) * ((k + 1 : ℕ) : ℝ) * L / ((N : ℝ) + 1)) ^ (k + 1) := by
        rw [pow_mul, ← mul_pow]
        congr 1
        dsimp only [α]
        have hM_ne : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hN_ne : ((N : ℝ) + 1) ≠ 0 := by positivity
        field_simp

/-- **Talagrand Theorem 2.5.2 (Eq. (2.99)) for the original perceptron (`s = 1`):**
under (2.7), `(M / (N + 1)) * K ≤ 1`, and `(q, r)` solving (2.68), for every `k : ℕ`:
$$\nu\!\left(\left(\frac{1}{N + 1} \sum_{j < M} u'(S_j^1) u'(S_j^2) - r\right)^{2k}\right)
  \le \left(\frac{\alpha k L}{N + 1}\right)^k.$$ -/
theorem integral_perceptron_empirical_variance_pow_le (D : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        (k : ℕ),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let S_perc (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) (j : Fin M) : ℝ :=
          (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)
        ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            (((N : ℝ) + 1)⁻¹ *
              ∑ j : Fin M, deriv u (S_perc g (σ 0) j) * deriv u (S_perc g (σ 1) j) - r) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                fun τ : Fin (N + 1) → ℤˣ => ∑ j, u (S_perc g τ j))
            ∂P_g ≤
          ((M : ℝ) / ((N : ℝ) + 1) * (k : ℝ) * L / ((N : ℝ) + 1)) ^ k := by
  obtain ⟨K, L, hK0, hL0, h_interp⟩ := integral_interpolating_empirical_variance_pow_le D
  refine ⟨K, L, hK0, hL0, ?_⟩
  intro N M u hd hb hα q r hq hr k P_g S_perc
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hs1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h := h_interp N M hs1 hd hb hα hq hr k
  dsimp only at h
  refine le_trans (le_of_eq ?_) h
  symm
  let Φ (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    (((N : ℝ) + 1)⁻¹ *
      ∑ j : Fin M, deriv u (S_perc g (τ 0) j) * deriv u (S_perc g (τ 1) j) - r) ^ (2 * k)
  let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
  let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  let μ_1 := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)
  let E_perc (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ j : Fin M, u (S_perc g τ j)
  have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((N : ℝ) + 1)⁻¹ *
          ∑ j : Fin M,
            deriv u (Real.sqrt 1 * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
                ∑ i, ω.1.1 j i * (((σ 0).1 i : ℤ) : ℝ)) +
              Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * (σ 0).2 j)) *
            deriv u (Real.sqrt 1 * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
                ∑ i, ω.1.1 j i * (((σ 1).1 i : ℤ) : ℝ)) +
              Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * (σ 1).2 j)) - r) ^
          (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => μ_1.tilted (fun x =>
          (∑ j : Fin M, u (Real.sqrt 1 *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 1) * ω.2 i * Real.sqrt r)) =
      ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ ω.1.1 τ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_perc ω.1.1)) := by
    have hE_simp (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        (∑ j : Fin M, u (Real.sqrt 1 *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 1) * ω.2 i * Real.sqrt r) =
        E_perc ω.1.1 x.1 + ∑ _j : Fin M, (0 : ℝ) := by
      simp [E_perc, S_perc]
    have hobs_simp (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        (((N : ℝ) + 1)⁻¹ *
          ∑ j : Fin M,
            deriv u (Real.sqrt 1 * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
                ∑ i, ω.1.1 j i * (((σ 0).1 i : ℤ) : ℝ)) +
              Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * (σ 0).2 j)) *
            deriv u (Real.sqrt 1 * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
                ∑ i, ω.1.1 j i * (((σ 1).1 i : ℤ) : ℝ)) +
              Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * (σ 1).2 j)) - r) ^
          (2 * k) =
        Φ ω.1.1 (fun l => (σ l).1) := by
      simp [Φ, S_perc]
    simp_rw [hE_simp, hobs_simp]
    simpa using integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
      (E_perc ω.1.1) (fun _ _ _ => (0 : ℝ))
      (fun _ _ => measurable_const) (fun _ => (0 : ℝ)) (fun _ _ _ => le_rfl) (Φ ω.1.1)
  change (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      (((N : ℝ) + 1)⁻¹ *
        ∑ j : Fin M,
          deriv u (Real.sqrt 1 * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
              ∑ i, ω.1.1 j i * (((σ 0).1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * (σ 0).2 j)) *
          deriv u (Real.sqrt 1 * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
              ∑ i, ω.1.1 j i * (((σ 1).1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * (σ 1).2 j)) - r) ^
        (2 * k)
      ∂(Measure.pi fun _ : Fin 2 => μ_1.tilted _) ∂((P_g.prod P_z).prod P_z')) =
    ∫ g, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ g τ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_perc g)) ∂P_g
  simp_rw [hpt]
  have hP_z : IsProbabilityMeasure P_z := by dsimp [P_z]; infer_instance
  have hP_z' : IsProbabilityMeasure P_z' := by dsimp [P_z']; infer_instance
  let I_g (g : Fin M → Fin (N + 1) → ℝ) : ℝ :=
    ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ g τ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_perc g))
  have hIg_int : Integrable I_g P_g := by
    have hD₁ : ∀ x, |deriv u x| ≤ |D| := hu.abs_deriv_le_abs
    let C_Φ : ℝ := ((M : ℝ) / ((N : ℝ) + 1) * |D| ^ 2 + |r|) ^ (2 * k)
    have hΦ_b (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin 2 → Fin (N + 1) → ℤˣ) :
        |Φ g τ| ≤ C_Φ := by
      dsimp only [Φ, C_Φ]; rw [abs_pow]
      have hob := abs_empVar_obs_le (N := N) hD₁ r (S_perc g (τ 0)) (S_perc g (τ 1))
      rw [abs_abs] at hob
      exact pow_le_pow_left₀ (abs_nonneg _) hob (2 * k)
    have hΦ_m (τ : Fin 2 → Fin (N + 1) → ℤˣ) : Measurable fun g : Fin M → Fin (N + 1) → ℝ =>
        Φ g τ := by
      refine ((Finset.measurable_sum _ fun j _ => ?_).const_mul _ |>.sub_const r).pow_const (2 * k)
      have hs_m (l : Fin 2) : Measurable fun g : Fin M → Fin (N + 1) → ℝ => S_perc g (τ l) j :=
        (Finset.measurable_sum _ fun i _ =>
          ((measurable_pi_apply i).comp (measurable_pi_apply j)).mul_const _).const_mul _
      exact ((measurable_deriv u).comp (hs_m 0)).mul ((measurable_deriv u).comp (hs_m 1))
    exact integrable_integral_pi_count_tilted_sum_potential hu.measurable
      Φ hΦ_m hΦ_b
  have hfub1 : ∫ ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ),
      I_g ω.1.1 ∂((P_g.prod P_z).prod P_z') =
    ∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ), I_g p.1 ∂(P_g.prod P_z) := by
    rw [integral_prod _ ((hIg_int.comp_fst P_z).comp_fst P_z')]
    simp
  rw [hfub1, integral_prod _ (hIg_int.comp_fst P_z)]
  simp only [integral_const, probReal_univ, one_smul]
  rfl

end SpinGlasses

