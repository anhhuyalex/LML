/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Decoupling

/-!
# The `t = 0` bound `ν₀(f) ≤ K(d)/N` (Talagrand, proof of Theorem 1.12.1)

The full overlap of `N + 1` sites splits as the cavity overlap plus the contribution of the last
site, `R_{1,2}^{u,v} = R^{-,u,v}_{1,2} + (N+1)⁻¹ ε¹ᵤ ε²ᵥ`.  By the decoupling theorem
`skVectorCavityAverage_zero_pair_mul_eq_zero` the cavity part of `ν₀((ε¹ᵤ ε²ᵥ - qᵤᵥ)(R^{u,v}_{1,2}
  - qᵤᵥ))` vanishes, and
the last-site part is `O(1/N)` because all spin coordinates are bounded.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- **A mean-zero part plus a bounded part.**  If the family of probability measures `Q ω` has
integrable bounded-observable averages and `∫ A d(Q ω)` averages to zero, then the average of
`A + c B` is at most `c M_B`, where `|B| ≤ M_B`. -/
theorem abs_integral_add_const_mul_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} [IsProbabilityMeasure P] (Q : Ω → Measure X) [∀ ω, IsProbabilityMeasure (Q ω)]
    (hI : ∀ G : X → ℝ, Measurable G → (∃ M, ∀ x, |G x| ≤ M) →
      Integrable (fun ω => ∫ x, G x ∂(Q ω)) P)
    {A B : X → ℝ} (hAm : Measurable A) (hBm : Measurable B) {MA MB : ℝ}
    (hAb : ∀ x, |A x| ≤ MA) (hBb : ∀ x, |B x| ≤ MB) {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∫ ω, ∫ x, A x ∂(Q ω) ∂P = 0) :
    |∫ ω, ∫ x, (A x + c * B x) ∂(Q ω) ∂P| ≤ c * MB := by
  have hint : ∀ ω, ∫ x, (A x + c * B x) ∂(Q ω) = ∫ x, A x ∂(Q ω) + c * ∫ x, B x ∂(Q ω) := by
    intro ω
    rw [integral_add, integral_const_mul]
    · exact integrable_of_measurable_bound hAm hAb
    · exact (integrable_of_measurable_bound hBm hBb).const_mul c
  simp_rw [hint]
  rw [integral_add (hI A hAm ⟨MA, hAb⟩) ((hI B hBm ⟨MB, hBb⟩).const_mul c), h0, zero_add,
    integral_const_mul]
  have hB : |∫ ω, ∫ x, B x ∂(Q ω) ∂P| ≤ MB := by
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => ∫ x, B x ∂(Q ω)) (C := MB) (Filter.Eventually.of_forall fun ω => by
        have := norm_integral_le_of_norm_le_const (μ := Q ω) (f := B) (C := MB)
          (Filter.Eventually.of_forall fun x => by simpa using hBb x)
        simpa using this)
    simpa using this
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hB hc


/-- **`ν₀(f) = O(1/N)`**, abstract form: for replicas `a, b` and a target `T` with `|T| ≤ d`
whose centered last-site observable `ε^a_u ε^b_v - T` decouples from all bounded measurable
functions of the old sites at `t = 0` (hypothesis `hdec`), the Gibbs average of
`f = (ε^a_u ε^b_v - T)(R^{u,v}_{a,b} - T)` over two replicas of the `N + 1` site system is at most
`2 d² / (N + 1)` in absolute value, where `R^{u,v}_{a,b} = (N+1)⁻¹ ∑_{i ≤ N} ξ(σᵃᵢ)ᵤ ξ(σᵇᵢ)ᵥ`. -/
theorem abs_skVectorCavityAverage_zero_overlap_le {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (a b : Fin 2) (u v : Fin d) (T : ℝ) (hTb : |T| ≤ d)
    (hdec : ∀ Ψ : (Fin 2 → Fin N → α) → ℝ, Measurable Ψ →
      ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, Ψ (fun i j => σ i j.castSucc) *
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) ∂P = 0) :
    |∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α,
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T) *
          (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) ∂P| ≤ 2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1) := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc0 : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹ := by positivity
  have hcN : ((N : ℝ) + 1)⁻¹ * N ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have hsp := abs_spin_mul_le ξ hr hbound
  have hΨm : Measurable fun τ : Fin 2 → Fin N → α =>
      ((N : ℝ) + 1)⁻¹ * ∑ i : Fin N, ξ (τ a i) u * ξ (τ b i) v - T := by
    refine (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)).sub measurable_const
    exact ((hξ u).comp ((measurable_pi_apply i).comp (measurable_pi_apply a))).mul
      ((hξ v).comp ((measurable_pi_apply i).comp (measurable_pi_apply b)))
  have hΨb : ∀ τ : Fin 2 → Fin N → α,
      |((N : ℝ) + 1)⁻¹ * ∑ i : Fin N, ξ (τ a i) u * ξ (τ b i) v - T| ≤ d + d := fun τ => by
    refine (abs_sub _ _).trans (add_le_add ?_ hTb)
    rw [abs_mul, abs_of_nonneg hc0]
    calc ((N : ℝ) + 1)⁻¹ * |∑ i : Fin N, ξ (τ a i) u * ξ (τ b i) v| ≤
          ((N : ℝ) + 1)⁻¹ * (N * d) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine (Finset.sum_le_sum fun i _ => hsp (τ a i) (τ b i) u v).trans ?_
          simp
      _ = (((N : ℝ) + 1)⁻¹ * N) * d := by ring
      _ ≤ 1 * d := mul_le_mul_of_nonneg_right hcN hr
      _ = d := one_mul _
  have hEm : Measurable fun σ : Fin 2 → Fin (N + 1) → α =>
      ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v :=
    ((hξ u).comp ((measurable_pi_apply _).comp (measurable_pi_apply a))).mul
      ((hξ v).comp ((measurable_pi_apply _).comp (measurable_pi_apply b)))
  have hWm : Measurable fun σ : Fin 2 → Fin (N + 1) → α =>
      ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T := hEm.sub measurable_const
  have hWb : ∀ σ : Fin 2 → Fin (N + 1) → α,
      |ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T| ≤ d + d := fun σ =>
    (abs_sub _ _).trans (add_le_add (hsp _ _ u v) hTb)
  have hrestr : Measurable fun (σ : Fin 2 → Fin (N + 1) → α) (i : Fin 2) (j : Fin N) =>
      σ i j.castSucc :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      (measurable_pi_apply _).comp (measurable_pi_apply i)
  have hEnm := measurable_skVectorCavityEnergy_joint ξ hξ N β ρ q hgm hg'm hYm 0
  have hprob := fun ω => isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q
    (fun p => g p ω) (fun i => g' i ω) (fun w => Y w ω) 0
  have hpt : ∀ σ : Fin 2 → Fin (N + 1) → α,
      (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T) *
          (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) =
        (((N : ℝ) + 1)⁻¹ * ∑ i : Fin N, ξ (σ a i.castSucc) u * ξ (σ b i.castSucc) v - T) *
          (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T) +
        ((N : ℝ) + 1)⁻¹ * ((ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) *
          (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T)) := by
    intro σ
    rw [Fin.sum_univ_castSucc]
    ring
  simp_rw [hpt]
  refine (abs_integral_add_const_mul_le (P := P) (fun ω => Measure.pi fun _ : Fin 2 =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
      (fun p => g p ω) (fun i => g' i ω) (fun w => Y w ω) 0)) ?_ ?_ ?_ (MA := (d + d) * (d + d))
    (MB := d * (d + d)) ?_ ?_ hc0 ?_).trans ?_
  · intro G hG hGb
    exact integrable_integral_pi_tilted (ι := Fin 2) (P := P)
      (μ := Measure.pi fun _ : Fin (N + 1) => μ) hEnm hprob hG hGb.choose_spec
  · exact (hΨm.comp hrestr).mul hWm
  · exact hEm.mul hWm
  · intro σ
    rw [abs_mul]
    exact mul_le_mul (hΨb fun i j => σ i j.castSucc) (hWb σ) (abs_nonneg _) (add_nonneg hr hr)
  · intro σ
    rw [abs_mul]
    exact mul_le_mul (hsp _ _ u v) (hWb σ) (abs_nonneg _) hr
  · exact hdec _ hΨm
  · rw [div_eq_inv_mul]
    nlinarith [hc0, sq_nonneg (d : ℝ)]

end SpinGlasses
