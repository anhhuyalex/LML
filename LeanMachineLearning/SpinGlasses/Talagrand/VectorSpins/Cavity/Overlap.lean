/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.OverlapComparison
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Decoupling

/-!
# The overlap functions of Theorem 1.12.1

For replicas `a`, `b` of the `N + 1` site system and a target matrix `T`, the centered overlap is
`R^{u,v}_{a,b} - T_{u,v}` with `R^{u,v}_{a,b} = (N+1)⁻¹ ∑_{i ≤ N} ξ(σᵃᵢ)ᵤ ξ(σᵇᵢ)ᵥ`, and the
centered last-site product is `ε^a_u ε^b_v - T_{u,v}`.  This file collects the pointwise
facts (measurability, bounds, Cauchy--Schwarz (1.384), the split `R = R⁻ + (N+1)⁻¹ ε^a ε^b`) used
in the closing inequality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- The centered overlap `R^{u,v}_{a,b} - T_{u,v}` of the replicas `a`, `b` of the `N + 1` site
system. -/
noncomputable def skVectorOverlapDeviation {d : ℕ} (ξ : α → Fin d → ℝ) (N : ℕ) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (u v : Fin d) (σ : Fin 2 → Fin (N + 1) → α) : ℝ :=
  ((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T u v

/-- The centered product `ε^a_u ε^b_v - T_{u,v}` of the last spins of the replicas `a`, `b`. -/
noncomputable def skVectorLastSpinDeviation {d : ℕ} (ξ : α → Fin d → ℝ) (N : ℕ) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (u v : Fin d) (σ : Fin 2 → Fin (N + 1) → α) : ℝ :=
  ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T u v

variable {d N : ℕ} (ξ : α → Fin d → ℝ)

omit [MeasurableSpace α] in
/-- Eq. (1.384), first half: `∑ᵤᵥ (ε^a_u ε^b_v - Tᵤᵥ)² ≤ 4 d²` when `‖T‖_F ≤ d`. -/
theorem sum_sq_skVectorLastSpinDeviation_le (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (hT : ∑ u, ∑ v, T u v ^ 2 ≤ (d : ℝ) ^ 2)
    (σ : Fin 2 → Fin (N + 1) → α) :
    ∑ u, ∑ v, skVectorLastSpinDeviation ξ N a b T u v σ ^ 2 ≤ 4 * (d : ℝ) ^ 2 := by
  have hprod : ∑ u, ∑ v, (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) ^ 2 ≤
      (d : ℝ) ^ 2 := by
    have h : ∑ u, ∑ v, (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) ^ 2 =
        (∑ u, ξ (σ a (Fin.last N)) u ^ 2) * ∑ v, ξ (σ b (Fin.last N)) v ^ 2 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [h, sq]
    exact mul_le_mul (hbound _) (hbound _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Nat.cast_nonneg d)
  calc ∑ u, ∑ v, skVectorLastSpinDeviation ξ N a b T u v σ ^ 2 ≤
        ∑ u, ∑ v, (2 * (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) ^ 2 + 2 * T u v ^ 2) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
          unfold skVectorLastSpinDeviation
          nlinarith [sq_nonneg (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v + T u v)]
    _ = 2 * ∑ u, ∑ v, (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) ^ 2 +
          2 * ∑ u, ∑ v, T u v ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 * (d : ℝ) ^ 2 := by linarith

omit [MeasurableSpace α] in
/-- **Eq. (1.384)**:
`(∑ᵤᵥ (ε^a_u ε^b_v - Tᵤᵥ)(R^{u,v}_{a,b} - Tᵤᵥ))² ≤ 4 d² ∑ᵤᵥ (R^{u,v}_{a,b} - Tᵤᵥ)²`. -/
theorem sq_sum_lastSpinDeviation_mul_overlapDeviation_le (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (a b :
  Fin 2)
    (T : Fin d → Fin d → ℝ) (hT : ∑ u, ∑ v, T u v ^ 2 ≤ (d : ℝ) ^ 2)
    (σ : Fin 2 → Fin (N + 1) → α) :
    (∑ u, ∑ v, skVectorLastSpinDeviation ξ N a b T u v σ * skVectorOverlapDeviation ξ N a b T u v
      σ) ^ 2 ≤
      4 * (d : ℝ) ^ 2 * ∑ u, ∑ v, skVectorOverlapDeviation ξ N a b T u v σ ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
    (fun p => skVectorLastSpinDeviation ξ N a b T p.1 p.2 σ) (fun p => skVectorOverlapDeviation ξ
      N a b T p.1 p.2 σ)
  simp only [Fintype.sum_prod_type] at hcs
  calc _ ≤ _ := hcs
    _ ≤ (4 * (d : ℝ) ^ 2) * ∑ u, ∑ v, skVectorOverlapDeviation ξ N a b T u v σ ^ 2 :=
      mul_le_mul_of_nonneg_right (sum_sq_skVectorLastSpinDeviation_le ξ hbound a b T hT σ)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [MeasurableSpace α] in
/-- A matrix with `‖T‖_F ≤ d` has all entries of absolute value at most `d`. -/
theorem abs_entry_le_of_sum_sq_le (T : Fin d → Fin d → ℝ) (hT : ∑ u, ∑ v, T u v ^ 2 ≤ (d : ℝ) ^ 2)
    (u v : Fin d) : |T u v| ≤ d := by
  have h1 : T u v ^ 2 ≤ ∑ u, ∑ v, T u v ^ 2 :=
    (Finset.single_le_sum (f := fun v => T u v ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ v)).trans
      (Finset.single_le_sum (f := fun u => ∑ v, T u v ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ u))
  exact abs_le_of_sq_le_sq' (h1.trans hT) (Nat.cast_nonneg d) |> fun h => abs_le.2 h

omit [MeasurableSpace α] in
/-- The centered overlap is the cavity overlap error plus the contribution of the last site:
`R - T = (R⁻ - T) + (N+1)⁻¹ ε^a_u ε^b_v`. -/
theorem skVectorOverlapDeviation_eq (a b : Fin 2) (T : Fin d → Fin d → ℝ) (u v : Fin d)
    (σ : Fin 2 → Fin (N + 1) → α) :
    skVectorOverlapDeviation ξ N a b T u v σ =
      (skVectorCavityOverlap ξ N (σ a) (σ b) u v - T u v) +
        ((N : ℝ) + 1)⁻¹ * (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) := by
  unfold skVectorOverlapDeviation skVectorCavityOverlap
  rw [Fin.sum_univ_castSucc]
  ring

omit [MeasurableSpace α] in
/-- The cavity overlap error is at most twice the full overlap error plus `2 d²/(N+1)²`. -/
theorem sum_sq_cavityOverlap_deviation_le (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (σ : Fin 2 → Fin (N + 1) → α) :
    ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ a) (σ b) u v - T u v) ^ 2 ≤
      2 * ∑ u, ∑ v, skVectorOverlapDeviation ξ N a b T u v σ ^ 2 +
        2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1) ^ 2 := by
  have hprod : ∑ u, ∑ v, (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) ^ 2 ≤
      (d : ℝ) ^ 2 := by
    have h : ∑ u, ∑ v, (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) ^ 2 =
        (∑ u, ξ (σ a (Fin.last N)) u ^ 2) * ∑ v, ξ (σ b (Fin.last N)) v ^ 2 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [h, sq]
    exact mul_le_mul (hbound _) (hbound _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Nat.cast_nonneg d)
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ a) (σ b) u v - T u v) ^ 2 ≤
        ∑ u, ∑ v, (2 * skVectorOverlapDeviation ξ N a b T u v σ ^ 2 +
          2 * (((N : ℝ) + 1)⁻¹ * (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v)) ^ 2) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
          rw [skVectorOverlapDeviation_eq ξ a b T u v σ]
          nlinarith [sq_nonneg (skVectorCavityOverlap ξ N (σ a) (σ b) u v - T u v +
            2 * (((N : ℝ) + 1)⁻¹ * (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v)))]
    _ = 2 * ∑ u, ∑ v, skVectorOverlapDeviation ξ N a b T u v σ ^ 2 +
          2 * (((N : ℝ) + 1)⁻¹) ^ 2 * ∑ u, ∑ v,
            (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_pow]
        congr 1
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ 2 * ∑ u, ∑ v, skVectorOverlapDeviation ξ N a b T u v σ ^ 2 +
          2 * (((N : ℝ) + 1)⁻¹) ^ 2 * (d : ℝ) ^ 2 := by
        gcongr
    _ = _ := by
        rw [inv_pow]
        field_simp

/-- The centered last-site product is measurable. -/
theorem measurable_skVectorLastSpinDeviation (hξ : ∀ u, Measurable (fun a => ξ a u)) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (u v : Fin d) :
    Measurable (skVectorLastSpinDeviation ξ N a b T u v) :=
  (((hξ u).comp ((measurable_pi_apply _).comp (measurable_pi_apply a))).mul
    ((hξ v).comp ((measurable_pi_apply _).comp (measurable_pi_apply b)))).sub measurable_const

/-- The centered overlap is measurable. -/
theorem measurable_skVectorOverlapDeviation (hξ : ∀ u, Measurable (fun a => ξ a u)) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (u v : Fin d) :
    Measurable (skVectorOverlapDeviation ξ N a b T u v) :=
  (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    ((hξ u).comp ((measurable_pi_apply i).comp (measurable_pi_apply a))).mul
      ((hξ v).comp ((measurable_pi_apply i).comp (measurable_pi_apply b))))).sub measurable_const

omit [MeasurableSpace α] in
/-- The centered last-site product is at most `2 d` in absolute value. -/
theorem abs_skVectorLastSpinDeviation_le (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (u v : Fin d) (hT : |T u v| ≤ d) (σ : Fin 2 → Fin (N + 1) → α) :
    |skVectorLastSpinDeviation ξ N a b T u v σ| ≤ d + d :=
  (abs_sub _ _).trans (add_le_add (abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound _ _ u v) hT)

omit [MeasurableSpace α] in
/-- The centered overlap is at most `2 d` in absolute value. -/
theorem abs_skVectorOverlapDeviation_le (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (u v : Fin d) (hT : |T u v| ≤ d) (σ : Fin 2 → Fin (N + 1) → α) :
    |skVectorOverlapDeviation ξ N a b T u v σ| ≤ d + d := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine (abs_sub _ _).trans (add_le_add ?_ hT)
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1))]
  calc ((N : ℝ) + 1)⁻¹ * |∑ i, ξ (σ a i) u * ξ (σ b i) v| ≤
        ((N : ℝ) + 1)⁻¹ * (((N : ℝ) + 1) * d) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (by positivity))
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => abs_spin_mul_le ξ hr hbound _ _ u v).trans ?_
        simp
    _ = d := by field_simp

omit [MeasurableSpace α] in
/-- A double sum over `Fin d` of terms bounded by `C` is at most `d² C` in absolute value. -/
theorem abs_double_sum_le (f : Fin d → Fin d → ℝ) {C : ℝ} (h : ∀ u v, |f u v| ≤ C) :
    |∑ u, ∑ v, f u v| ≤ (d : ℝ) * d * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun u _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun v _ => h u v)).trans ?_
  simp [mul_assoc]

/-- The squared overlap error summed over the matrix entries is measurable. -/
theorem measurable_sum_sq_skVectorOverlapDeviation (hξ : ∀ u, Measurable (fun a => ξ a u))
    (a b : Fin 2) (T : Fin d → Fin d → ℝ) :
    Measurable fun τ : Fin 2 → Fin (N + 1) → α => ∑ u, ∑ v,
      skVectorOverlapDeviation ξ N a b T u v τ ^ 2 :=
  Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
    (measurable_skVectorOverlapDeviation ξ hξ a b T u v).pow_const 2

omit [MeasurableSpace α] in
/-- The squared overlap error summed over the matrix entries is at most `d² (2d)²`. -/
theorem abs_sum_sq_skVectorOverlapDeviation_le (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (a b : Fin 2)
    (T : Fin d → Fin d → ℝ) (hT : ∀ u v, |T u v| ≤ d) (τ : Fin 2 → Fin (N + 1) → α) :
    |∑ u, ∑ v, skVectorOverlapDeviation ξ N a b T u v τ ^ 2| ≤ (d : ℝ) * d * ((d + d) * (d + d)) :=
  abs_double_sum_le _ fun u v => by
    rw [abs_of_nonneg (sq_nonneg _), sq]
    have h := abs_skVectorOverlapDeviation_le ξ hbound a b T u v (hT u v) τ
    calc
      _ = |skVectorOverlapDeviation ξ N a b T u v τ| *
          |skVectorOverlapDeviation ξ N a b T u v τ| := (abs_mul_abs_self _).symm
      _ ≤ _ := mul_le_mul h h (abs_nonneg _) (add_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d))

end SpinGlasses
