/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.ReplicaAverage
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Overlap
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Disorder

/-!
# `∂p_N/∂β` is close to `(β/2) ∑ (ρ² - q²)` (proof of Theorem 1.12.3)

Combining the overlap form of `∂p_{N+1}/∂β` with the overlap bound of Theorem 1.12.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- Cauchy-Schwarz plus AM-GM for a pairing with a vector of Frobenius norm at most `d`. -/
theorem abs_sum_mul_le_sq_div_add {ι : Type*} [Fintype ι] (r a : ι → ℝ) {d s : ℝ}
    (hd : 0 ≤ d) (hs : 0 < s) (hr : ∑ i, r i ^ 2 ≤ d ^ 2) :
    |∑ i, r i * a i| ≤ d * ((∑ i, a i ^ 2) / s + s) / 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) r a
  set W := ∑ i, a i ^ 2 with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : (∑ i, r i * a i) ^ 2 ≤ d ^ 2 * W := hcs.trans
    (mul_le_mul_of_nonneg_right hr hW0)
  have h2 : |∑ i, r i * a i| ≤ d * Real.sqrt W := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hd, ← Real.sqrt_mul (sq_nonneg d)]
    exact Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt W ≤ (W / s + s) / 2 := by
    have : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW0
    rw [div_add' _ _ _ hs.ne', div_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt W - s)]
  calc |∑ i, r i * a i| ≤ d * Real.sqrt W := h2
    _ ≤ d * ((W / s + s) / 2) := mul_le_mul_of_nonneg_left h3 hd
    _ = d * (W / s + s) / 2 := by ring

/-- **Pointwise algebra of the derivative of `p_N`**: the overlap form of the integrand differs from
`(β/2)(‖ρ‖² - ‖q‖²)` by an amount controlled by the squared overlap errors. -/
theorem abs_overlap_deriv_sub_quadratic_le {ι : Type*} [Fintype ι] {M β d s : ℝ} (hM : 0 < M) (hd
  : 0 ≤ d)
    (hs : 0 < s) (r q a b : ι → ℝ) (D0 D1 : ℝ) (hr : ∑ i, r i ^ 2 ≤ d ^ 2)
    (hq : ∑ i, q i ^ 2 ≤ d ^ 2) (hD : |D0 - D1| ≤ M * d ^ 2) :
    |M⁻¹ * (β * ((2 * M)⁻¹ * ((M ^ 2 * ∑ i, (a i + r i) ^ 2 - D0) -
        (M ^ 2 * ∑ i, (b i + q i) ^ 2 - D1)))) - β / 2 * (∑ i, r i ^ 2 - ∑ i, q i ^ 2)| ≤
      |β| / 2 * ((∑ i, a i ^ 2 + ∑ i, b i ^ 2) +
        d * (∑ i, a i ^ 2 + ∑ i, b i ^ 2) / s + 2 * d * s) + |β| * d ^ 2 / (2 * M) := by
  have h1 := abs_sum_mul_le_sq_div_add r a hd hs hr
  have h2 := abs_sum_mul_le_sq_div_add q b hd hs hq
  have hex : ∀ (c : ι → ℝ) (e : ι → ℝ), ∑ i, (c i + e i) ^ 2 =
      ∑ i, c i ^ 2 + 2 * ∑ i, e i * c i + ∑ i, e i ^ 2 := fun c e => by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hM2 : M ^ 2 ≠ 0 := by positivity
  have key : M⁻¹ * (β * ((2 * M)⁻¹ * ((M ^ 2 * ∑ i, (a i + r i) ^ 2 - D0) -
        (M ^ 2 * ∑ i, (b i + q i) ^ 2 - D1)))) - β / 2 * (∑ i, r i ^ 2 - ∑ i, q i ^ 2) =
      β / 2 * ((∑ i, a i ^ 2 + 2 * ∑ i, r i * a i) - (∑ i, b i ^ 2 + 2 * ∑ i, q i * b i)) -
        β * (2 * M ^ 2)⁻¹ * (D0 - D1) := by
    rw [hex a r, hex b q]
    field_simp
    ring
  rw [key]
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD' : |β * (2 * M ^ 2)⁻¹ * (D0 - D1)| ≤ |β| * d ^ 2 / (2 * M) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 * M ^ 2))]
    calc |β| * (2 * M ^ 2)⁻¹ * |D0 - D1| ≤ |β| * (2 * M ^ 2)⁻¹ * (M * d ^ 2) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = |β| * d ^ 2 / (2 * M) := by field_simp
  refine (abs_sub _ _).trans (add_le_add ?_ hD')
  rw [abs_mul, show |β / 2| = |β| / 2 by rw [abs_div, abs_two]]
  have h3 : |(∑ i, a i ^ 2 + 2 * ∑ i, r i * a i) - (∑ i, b i ^ 2 + 2 * ∑ i, q i * b i)| ≤
      (∑ i, a i ^ 2 + ∑ i, b i ^ 2) + d * (∑ i, a i ^ 2 + ∑ i, b i ^ 2) / s + 2 * d * s := by
    have e1 := (abs_le.1 h1)
    have e2 := (abs_le.1 h2)
    have f1 : d * ((∑ i, a i ^ 2) / s + s) / 2 = d * (∑ i, a i ^ 2 / s) / 2 + d * s / 2 := by
      rw [← Finset.sum_div]; ring
    have f2 : d * ((∑ i, b i ^ 2) / s + s) / 2 = d * (∑ i, b i ^ 2 / s) / 2 + d * s / 2 := by
      rw [← Finset.sum_div]; ring
    have f3 : d * (∑ i, a i ^ 2 + ∑ i, b i ^ 2) / s =
        d * (∑ i, a i ^ 2 / s) + d * (∑ i, b i ^ 2 / s) := by
      rw [← Finset.sum_div, ← Finset.sum_div]; ring
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The integrand of `∂p_{N+1}/∂β` in terms of the squared overlap errors, pointwise. -/
noncomputable def skVectorFreeEnergyDerivIntegrand {d : ℕ} (ξ : α → Fin d → ℝ) (N : ℕ)
    (σ : Fin 2 → Fin (N + 1) → α) : ℝ :=
  (2 * ((N : ℝ) + 1))⁻¹ * ∑ u, ∑ v,
    (((∑ i, ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2 - ∑ i, (ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2) -
      ((∑ i, ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2 - ∑ i, (ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2))

omit [MeasurableSpace α] in
/-- The diagonal terms `∑ᵤᵥ ∑ᵢ (ξ(σᵢ)ᵤ ξ(τᵢ)ᵥ)²` lie in `[0, M d²]`. -/
theorem sum_sq_spin_products_nonneg_le {d : ℕ} (ξ : α → Fin d → ℝ) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤
  d) (N : ℕ)
    (σ τ : Fin (N + 1) → α) :
    0 ≤ ∑ u, ∑ v, ∑ i, (ξ (σ i) u * ξ (τ i) v) ^ 2 ∧
      ∑ u, ∑ v, ∑ i, (ξ (σ i) u * ξ (τ i) v) ^ 2 ≤ ((N : ℝ) + 1) * (d : ℝ) ^ 2 := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => Finset.sum_nonneg
    fun i _ => sq_nonneg _, ?_⟩
  have hi : ∀ i, ∑ u, ∑ v, (ξ (σ i) u * ξ (τ i) v) ^ 2 ≤ (d : ℝ) ^ 2 := fun i => by
    have : ∑ u, ∑ v, (ξ (σ i) u * ξ (τ i) v) ^ 2 =
        (∑ u, ξ (σ i) u ^ 2) * ∑ v, ξ (τ i) v ^ 2 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [this, sq]
    exact mul_le_mul (hbound _) (hbound _) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hr
  calc ∑ u, ∑ v, ∑ i, (ξ (σ i) u * ξ (τ i) v) ^ 2 =
        ∑ u, ∑ i, ∑ v, (ξ (σ i) u * ξ (τ i) v) ^ 2 :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ i, ∑ u, ∑ v, (ξ (σ i) u * ξ (τ i) v) ^ 2 := Finset.sum_comm
    _ ≤ ∑ _i : Fin (N + 1), (d : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = ((N : ℝ) + 1) * (d : ℝ) ^ 2 := by simp

omit [MeasurableSpace α] in
/-- Pointwise bound for the integrand of `∂p_{N+1}/∂β` against `(β/2)(‖ρ‖²_F - ‖q‖²_F)`. -/
theorem abs_skVectorFreeEnergyDerivIntegrand_sub_le {d : ℕ} (ξ : α → Fin d → ℝ)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (N : ℕ) {β s : ℝ} (hs : 0 < s)
    (r q : Fin d → Fin d → ℝ) (hr : ∑ u, ∑ v, r u v ^ 2 ≤ (d : ℝ) ^ 2)
    (hq : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) (σ : Fin 2 → Fin (N + 1) → α) :
    |((N : ℝ) + 1)⁻¹ * (β * skVectorFreeEnergyDerivIntegrand ξ N σ) -
        β / 2 * (∑ u, ∑ v, r u v ^ 2 - ∑ u, ∑ v, q u v ^ 2)| ≤
      |β| / 2 * ((∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 0 r u v σ ^ 2 +
          ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 1 q u v σ ^ 2) +
        d * (∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 0 r u v σ ^ 2 +
          ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 1 q u v σ ^ 2) / s + 2 * d * s) +
        |β| * d ^ 2 / (2 * ((N : ℝ) + 1)) := by
  classical
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hS : ∀ (a b : Fin 2) (T : Fin d → Fin d → ℝ) (u v : Fin d),
      ∑ i, ξ (σ a i) u * ξ (σ b i) v =
        ((N : ℝ) + 1) * (skVectorOverlapDeviation ξ N a b T u v σ + T u v) := fun a b T u v => by
    unfold skVectorOverlapDeviation
    field_simp
    ring
  have h := abs_overlap_deriv_sub_quadratic_le (M := (N : ℝ) + 1) (β := β) (d := d) (s := s) hM hd
    hs
    (fun p : Fin d × Fin d => r p.1 p.2) (fun p => q p.1 p.2)
    (fun p => skVectorOverlapDeviation ξ N 0 0 r p.1 p.2 σ) (fun p => skVectorOverlapDeviation ξ N
      0 1 q p.1
        p.2 σ)
    (∑ u, ∑ v, ∑ i, (ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2)
    (∑ u, ∑ v, ∑ i, (ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2)
    (by simpa [Fintype.sum_prod_type] using hr) (by simpa [Fintype.sum_prod_type] using hq)
    (by
      have h0 := sum_sq_spin_products_nonneg_le ξ hbound N (σ 0) (σ 0)
      have h1 := sum_sq_spin_products_nonneg_le ξ hbound N (σ 0) (σ 1)
      rw [abs_le]
      constructor <;> linarith [h0.1, h0.2, h1.1, h1.2])
  simp only [Fintype.sum_prod_type] at h
  convert h using 3
  unfold skVectorFreeEnergyDerivIntegrand
  congr 3
  simp_rw [hS 0 0 r, hS 0 1 q]
  simp only [Finset.sum_sub_distrib, mul_pow, ← Finset.mul_sum]

theorem measurable_skVectorFreeEnergyDerivIntegrand {d : ℕ} (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (N : ℕ) :
    Measurable (skVectorFreeEnergyDerivIntegrand ξ N) := by
  unfold skVectorFreeEnergyDerivIntegrand
  have hc : ∀ (i : Fin (N + 1)) (a b : Fin 2) (u v : Fin d), Measurable fun σ : Fin 2 →
      Fin (N + 1) → α => ξ (σ a i) u * ξ (σ b i) v := fun i a b u v =>
    ((hξ u).comp ((measurable_pi_apply i).comp (measurable_pi_apply a))).mul
      ((hξ v).comp ((measurable_pi_apply i).comp (measurable_pi_apply b)))
  refine measurable_const.mul (Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _
      => ?_)
  refine ((Finset.measurable_sum _ fun i _ => hc i 0 0 u v).pow_const 2 |>.sub
    (Finset.measurable_sum _ fun i _ => (hc i 0 0 u v).pow_const 2)).sub
    ((Finset.measurable_sum _ fun i _ => hc i 0 1 u v).pow_const 2 |>.sub
    (Finset.measurable_sum _ fun i _ => (hc i 0 1 u v).pow_const 2))

omit [MeasurableSpace α] in
/-- The integrand of `∂p_{N+1}/∂β` is bounded. -/
theorem exists_abs_skVectorFreeEnergyDerivIntegrand_le {d : ℕ} (ξ : α → Fin d → ℝ)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (N : ℕ) : ∃ C : ℝ, ∀ σ, |skVectorFreeEnergyDerivIntegrand ξ
      N σ| ≤ C
        := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxx : ∀ a b u v, |ξ a u * ξ b v| ≤ d := abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound
  set M : ℝ := (N : ℝ) + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  have hS : ∀ (a b : Fin 2) (σ : Fin 2 → Fin (N + 1) → α) (u v : Fin d),
      |∑ i, ξ (σ a i) u * ξ (σ b i) v| ≤ M * d := fun a b σ u v =>
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ i, |ξ (σ a i) u * ξ (σ b i) v| ≤ ∑ _i : Fin (N + 1), (d : ℝ) :=
            Finset.sum_le_sum fun i _ => hxx _ _ u v
        _ = M * d := by simp [hM])
  have hD : ∀ (a b : Fin 2) (σ : Fin 2 → Fin (N + 1) → α) (u v : Fin d),
      |∑ i, (ξ (σ a i) u * ξ (σ b i) v) ^ 2| ≤ M * d ^ 2 := fun a b σ u v =>
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc ∑ i, |(ξ (σ a i) u * ξ (σ b i) v) ^ 2| ≤ ∑ _i : Fin (N + 1), (d : ℝ) ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hxx _ _ u v) 2
        _ = M * d ^ 2 := by simp [hM])
  refine ⟨(2 * M)⁻¹ * ((d : ℝ) * d * (((M * d) ^ 2 + M * d ^ 2) + ((M * d) ^ 2 + M * d ^ 2))), fun
      σ => ?_⟩
  unfold skVectorFreeEnergyDerivIntegrand
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 * M))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (by positivity))
  have hterm : ∀ u v : Fin d, |((∑ i, ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2 -
      ∑ i, (ξ (σ 0 i) u * ξ (σ 0 i) v) ^ 2) -
      ((∑ i, ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2 - ∑ i, (ξ (σ 0 i) u * ξ (σ 1 i) v) ^ 2)| ≤
      ((M * d) ^ 2 + M * d ^ 2) + ((M * d) ^ 2 + M * d ^ 2) := fun u v => by
    have sq1 : ∀ a b : Fin 2, |(∑ i, ξ (σ a i) u * ξ (σ b i) v) ^ 2 -
        ∑ i, (ξ (σ a i) u * ξ (σ b i) v) ^ 2| ≤ (M * d) ^ 2 + M * d ^ 2 := fun a b =>
      (abs_sub _ _).trans (add_le_add (by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hS a b σ u v) 2) (hD a b σ u v))
    exact (abs_sub _ _).trans (add_le_add (sq1 0 0) (sq1 0 1))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun u _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun v _ => hterm u v)).trans ?_
  simp [mul_assoc]
  nlinarith

/-- **`∂p_{N+1}/∂β` is close to `(β/2) ∑ (ρ² - q²)`** (the estimate in the proof of Theorem 1.12.3):
for a fixed point `(q, ρ)` of `T` and `β² d² ≤ 1/200`, with `ε = (8 d⁴ + 2 d²)/(N+1)` and any `s >
0`,
the derivative of the free energy of the vector SK model with `N + 1` sites is within
`|β|/2 (ε + d ε/s + 2 d s) + |β| d²/(2(N+1))` of `(β/2) ∑ (ρ² - q²)`. -/
theorem exists_hasDerivAt_skVectorFreeEnergy_abs_sub_le {d : ℕ} (μ : Measure α)
  [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (hβ' : β ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200) (N : ℕ)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedPointCone d)
    (hxf : skVectorFixedPointMap μ ξ β x = x) {s : ℝ} (hs : 0 < s) :
    ∃ V : ℝ, HasDerivAt (skVectorFreeEnergy μ ξ (N + 1)) V β ∧
      |V - β / 2 * (∑ u, ∑ v, x.2 u v ^ 2 - ∑ u, ∑ v, x.1 u v ^ 2)| ≤
        |β| / 2 * ((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1) +
          d * ((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1)) / s + 2 * d * s) +
          |β| * d ^ 2 / (2 * ((N : ℝ) + 1)) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨hq2, hρ2⟩ := skVectorFixedPoint_sum_sq_le μ ξ hξ hbound β hx hxf
  have hW01m := measurable_sum_sq_skVectorOverlapDeviation (N := N) ξ hξ 0 1 x.1
  have hW00m := measurable_sum_sq_skVectorOverlapDeviation (N := N) ξ hξ 0 0 x.2
  have hqb : ∀ u v, |x.1 u v| ≤ d := abs_entry_le_of_sum_sq_le x.1 hq2
  have hρb : ∀ u v, |x.2 u v| ≤ d := abs_entry_le_of_sum_sq_le x.2 hρ2
  have hW01b : ∃ C, ∀ τ, |∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 1 x.1 u v τ ^ 2| ≤ C :=
    ⟨_, abs_sum_sq_skVectorOverlapDeviation_le ξ hbound 0 1 x.1 hqb⟩
  have hW00b : ∃ C, ∀ τ, |∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 0 x.2 u v τ ^ 2| ≤ C :=
    ⟨_, abs_sum_sq_skVectorOverlapDeviation_le ξ hbound 0 0 x.2 hρb⟩
  have hAB' := sum_sq_skVectorOverlapDeviation_average_le μ ξ hξ hbound N β hβ' hx hxf
  refine ⟨_, hasDerivAt_skVectorFreeEnergy μ ξ hξ hbound N β, ?_⟩
  set ε : ℝ := (8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1) with hε
  set c0 : ℝ := β / 2 * (∑ u, ∑ v, x.2 u v ^ 2 - ∑ u, ∑ v, x.1 u v ^ 2) with hc0
  set W00 : (Fin 2 → Fin (N + 1) → α) → ℝ := fun τ =>
    ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 0 x.2 u v τ ^ 2 with hW00
  set W01 : (Fin 2 → Fin (N + 1) → α) → ℝ := fun τ =>
    ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 1 x.1 u v τ ^ 2 with hW01
  have hΦm := measurable_skVectorFreeEnergyDerivIntegrand ξ hξ N
  obtain ⟨CΦ, hCΦ⟩ := exists_abs_skVectorFreeEnergyDerivIntegrand_le ξ hbound N
  have hWm : Measurable fun τ => W00 τ + W01 τ := hW00m.add hW01m
  obtain ⟨C0, hC0⟩ := hW00b
  obtain ⟨C1, hC1⟩ := hW01b
  have hWb : ∃ C, ∀ τ, |W00 τ + W01 τ| ≤ C := ⟨C0 + C1, fun τ => (abs_add_le _ _).trans
    (add_le_add (hC0 τ) (hC1 τ))⟩
  set κ : ℝ := |β| / 2 * (1 + d / s) with hκ
  set c1 : ℝ := |β| / 2 * (2 * d * s) + |β| * d ^ 2 / (2 * ((N : ℝ) + 1)) with hc1
  have hκ0 : 0 ≤ κ := by positivity
  -- the dominating function
  have hν_dom : skVectorReplicaAverage μ ξ N β (fun τ => κ * (W00 τ + W01 τ) + c1) ≤ κ * ε + c1 :=
    by
    rw [skVectorReplicaAverage_add μ ξ hξ hbound N β _ _ (hWm.const_mul κ) measurable_const
      (by obtain ⟨C, hC⟩ := hWb; exact ⟨|κ| * C, fun τ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC τ) (abs_nonneg _)⟩) ⟨|c1|, fun _ =>
            le_rfl⟩,
      skVectorReplicaAverage_const_mul μ ξ N β κ, skVectorReplicaAverage_const μ ξ hξ hbound N β c1,
      skVectorReplicaAverage_add μ ξ hξ hbound N β _ _ hW00m hW01m ⟨C0, hC0⟩ ⟨C1, hC1⟩]
    have : skVectorReplicaAverage μ ξ N β W00 + skVectorReplicaAverage μ ξ N β W01 ≤ ε := by
      linarith [hAB']
    nlinarith
  -- the integrand minus the constant
  set Ψ : (Fin 2 → Fin (N + 1) → α) → ℝ := fun τ =>
    ((N : ℝ) + 1)⁻¹ * (β * skVectorFreeEnergyDerivIntegrand ξ N τ) - c0 with hΨ
  have hΨν : skVectorReplicaAverage μ ξ N β Ψ =
      ((N : ℝ) + 1)⁻¹ * (β * skVectorReplicaAverage μ ξ N β (skVectorFreeEnergyDerivIntegrand ξ
        N)) - c0 := by
    have h1 : skVectorReplicaAverage μ ξ N β Ψ = skVectorReplicaAverage μ ξ N β
        (fun τ => (((N : ℝ) + 1)⁻¹ * β) * skVectorFreeEnergyDerivIntegrand ξ N τ + (-c0)) := by
      unfold skVectorReplicaAverage
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      simp only [hΨ]; ring
    rw [h1, skVectorReplicaAverage_add μ ξ hξ hbound N β _ _ (hΦm.const_mul _) measurable_const
      ⟨|((N : ℝ) + 1)⁻¹ * β| * CΦ, fun τ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCΦ τ) (abs_nonneg _)⟩ ⟨|c0|, fun _ => by
            simp⟩,
      skVectorReplicaAverage_const_mul μ ξ N β _ _, skVectorReplicaAverage_const μ ξ hξ hbound N β]
    ring
  have hbd : |skVectorReplicaAverage μ ξ N β Ψ| ≤ skVectorReplicaAverage μ ξ N β (fun τ => κ *
    (W00 τ + W01 τ) + c1) := by
    refine abs_skVectorReplicaAverage_le μ ξ hξ hbound N β Ψ _ ((hWm.const_mul κ).add
      measurable_const)
      (by obtain ⟨C, hC⟩ := hWb; exact ⟨|κ| * C + |c1|, fun τ => (abs_add_le _ _).trans
        (add_le_add (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC τ) (abs_nonneg _))
          le_rfl)⟩) fun τ => ?_
    have := abs_skVectorFreeEnergyDerivIntegrand_sub_le ξ hbound N (β := β) hs x.2 x.1 hρ2 hq2 τ
    refine this.trans (le_of_eq ?_)
    simp only [hκ, hc1, hW00, hW01]
    ring
  rw [hΨν] at hbd
  refine hbd.trans (hν_dom.trans (le_of_eq ?_))
  simp only [hκ, hc1]
  ring

end SpinGlasses
