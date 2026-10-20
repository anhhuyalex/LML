/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.PiFinSucc
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.Weights
public import LeanMachineLearning.ForMathlib.Combinatorics.DescFactorial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Tactic.Ring

/-!
# Spin decorrelation from overlap concentration (Talagrand, Proposition 1.4.14)

For a Gibbs state `w` on a finite configuration space `α` carrying `N` site observables
`ξ i : α → [-1, 1]`, write `R(a, b) = N⁻¹ ∑ᵢ ξᵢ(a) ξᵢ(b)` for the overlap.  This file proves the
*deterministic* half of Proposition 1.4.14: the sum over all `(k + 1)`-tuples of sites of the
squared centred correlation `⟨(ξ_{u₀} - ⟨ξ_{u₀}⟩) ξ_{u₁} ⋯ ξ_{u_k}⟩²` is at most
`4 k N^{k+1} ⟨(R₁,₂ - q)²⟩`, for every `|q| ≤ 1`.

The proof is the replica computation of the book: the sum over tuples is the two-replica average of
`(N R)^k ∑ⱼ ξ̇ⱼ¹ ξ̇ⱼ²`, which is unchanged when `(N q)^k` replaces `(N R)^k` because
`⟨∑ⱼ ξ̇ⱼ¹ ξ̇ⱼ²⟩ = 0`; then `|x^k - y^k| ≤ k |x - y|` and the elementary inequality
`|a b| ≤ 2 a² + b² / 8` reduce the claim to the bound `⟨(ξ̇¹ ⋅ ξ̇² / N)²⟩ ≤ 16 ⟨(R₁,₂ - q)²⟩`, which
is Jensen's inequality for the two averaged replicas.

## Main declarations

* `SpinGlasses.sum_sq_avg_centered_monomial_le`: the deterministic bound above.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.4.14.
-/

@[expose] public section

open Finset MeasureTheory Weights

namespace SpinGlasses

section Tuples

variable {N : ℕ}

variable {α : Type*} [Fintype α]

/-- **The replica identity of Proposition 1.4.14:** the sum over tuples of sites of the squared
centred correlation is the two-replica average of `(∑ᵢ ξᵢ¹ ξᵢ²)^k ∑ⱼ ξ̇ⱼ¹ ξ̇ⱼ²`. -/
theorem sum_sq_avg_tuple (ξ : Fin N → α → ℝ) (w : α → ℝ) (m : Fin N → ℝ) (k : ℕ) :
    ∑ u : Fin (k + 1) → Fin N,
        (∑ a, w a * ((ξ (u 0) a - m (u 0)) * ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 =
      ∑ a, ∑ b, w a * w b * ((∑ j, (ξ j a - m j) * (ξ j b - m j)) *
        (∑ i, ξ i a * ξ i b) ^ k) := by
  simp_rw [sq_sum_mul_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have key : ∀ u : Fin (k + 1) → Fin N,
      ((ξ (u 0) a - m (u 0)) * ∏ l : Fin k, ξ (u l.succ) a) *
        ((ξ (u 0) b - m (u 0)) * ∏ l : Fin k, ξ (u l.succ) b) =
      ((ξ (u 0) a - m (u 0)) * (ξ (u 0) b - m (u 0))) *
        ∏ l : Fin k, (ξ (u l.succ) a * ξ (u l.succ) b) := fun u => by
    rw [Finset.prod_mul_distrib]; ring
  rw [← Finset.mul_sum]
  simp_rw [key]
  rw [sum_piFinSucc_mul_prod k (fun j => (ξ j a - m j) * (ξ j b - m j)) (fun i => ξ i a * ξ i b)]

/-- Pulling the weighted sum over one replica inside the overlap. -/
theorem sum_mul_inv_mul_sum (w : α → ℝ) (f : Fin N → ℝ) (g : Fin N → α → ℝ) :
    ∑ t, w t * ((N : ℝ)⁻¹ * ∑ i, f i * g i t) = (N : ℝ)⁻¹ * ∑ i, f i * ∑ t, w t * g i t := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The Gibbs average of `R(z, ·) - q` against a fixed vector `f`, with `R = N⁻¹ ∑ᵢ ξᵢ ξᵢ`. -/
theorem sum_mul_overlap_sub (ξ : Fin N → α → ℝ) {w : α → ℝ} (hw1 : ∑ a, w a = 1)
    (f : Fin N → ℝ) (q : ℝ) :
    ∑ z, w z * ((N : ℝ)⁻¹ * ∑ i, f i * ξ i z - q) =
      (N : ℝ)⁻¹ * ∑ i, f i * ∑ z, w z * ξ i z - q := by
  simp only [mul_sub, Finset.sum_sub_distrib, sum_mul_const_of_sum_eq_one hw1]
  rw [sum_mul_inv_mul_sum]

/-- **The centred overlap in terms of the plain overlap `R = N⁻¹ ∑ᵢ ξᵢ ξᵢ`:** for a probability
vector `w` and every `q`, `ξ̇¹ ⋅ ξ̇² / N` is the signed sum
`(R₁,₂ - q) - ⟨R₁,₃ - q⟩ - ⟨R₃,₂ - q⟩ + ⟨R₃,₄ - q⟩`, where `⟨⋅⟩` averages the extra replicas. -/
theorem centered_overlap_eq (ξ : Fin N → α → ℝ) {w : α → ℝ} (hw1 : ∑ a, w a = 1) (q : ℝ)
    (x y : α) :
    (N : ℝ)⁻¹ * ∑ j, (ξ j x - ∑ b, w b * ξ j b) * (ξ j y - ∑ b, w b * ξ j b) =
      ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q)
        - ∑ t, w t * ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i t - q)
        - ∑ z, w z * ((N : ℝ)⁻¹ * ∑ i, ξ i z * ξ i y - q)
        + ∑ z, ∑ t, w z * w t * ((N : ℝ)⁻¹ * ∑ i, ξ i z * ξ i t - q) := by
  have h1 : ∀ x : α, ∑ t, w t * ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i t - q) =
      (N : ℝ)⁻¹ * ∑ i, ξ i x * ∑ t, w t * ξ i t - q := fun x =>
    sum_mul_overlap_sub ξ hw1 (fun i => ξ i x) q
  have h2 : ∀ y : α, ∑ z, w z * ((N : ℝ)⁻¹ * ∑ i, ξ i z * ξ i y - q) =
      (N : ℝ)⁻¹ * ∑ i, ξ i y * ∑ z, w z * ξ i z - q := fun y => by
    simp_rw [mul_comm (ξ _ _) (ξ _ y)]
    exact sum_mul_overlap_sub ξ hw1 (fun i => ξ i y) q
  have h3 : ∑ z, ∑ t, w z * w t * ((N : ℝ)⁻¹ * ∑ i, ξ i z * ξ i t - q) =
      (N : ℝ)⁻¹ * ∑ i, (∑ z, w z * ξ i z) * ∑ t, w t * ξ i t - q := by
    simp_rw [mul_assoc, ← Finset.mul_sum, h1]
    simp_rw [mul_comm (ξ _ _) (∑ t, w t * ξ _ t)]
    rw [sum_mul_overlap_sub ξ hw1 (fun i => ∑ t, w t * ξ i t) q]
  have e : ∑ j, (ξ j x - ∑ b, w b * ξ j b) * (ξ j y - ∑ b, w b * ξ j b) =
      ∑ j, ξ j x * ξ j y - ∑ j, ξ j x * ∑ b, w b * ξ j b - ∑ j, ξ j y * ∑ b, w b * ξ j b +
        ∑ j, (∑ b, w b * ξ j b) * ∑ b, w b * ξ j b := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, h1, h2, h3]
  ring

end Tuples

section Decoupling

variable {α : Type*} [Fintype α]

/-- Averaging a function of one replica over a second, independent replica changes nothing. -/
theorem sum_mul_mul_const {w : α → ℝ} (hw1 : ∑ a, w a = 1) (u c : ℝ) :
    ∑ y, u * w y * c = u * c := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, hw1, mul_one]

/-- Averaging a function of one replica over a second, independent replica changes nothing
(the averaged replica comes first). -/
theorem sum_mul_mul_const_left {w : α → ℝ} (hw1 : ∑ a, w a = 1) (u c : ℝ) :
    ∑ x, w x * u * c = u * c := by
  rw [← Finset.sum_mul, ← Finset.sum_mul, hw1, one_mul]

/-- **Jensen for the four-replica decoupling (Proposition 1.4.14).**  For a probability vector `w`
and any `e`, the two-replica average of `(e₁,₂ - ⟨e₁,₃⟩ - ⟨e₃,₂⟩ + ⟨e₃,₄⟩)²` is at most sixteen
times that of `e₁,₂²`, since each of the four terms has a mean square at most that of `e₁,₂`. -/
theorem sum_sum_sq_decoupled_le {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (e : α → α → ℝ) :
    ∑ x, ∑ y, w x * w y *
        (e x y - ∑ t, w t * e x t - ∑ z, w z * e z y + ∑ z, ∑ t, w z * w t * e z t) ^ 2 ≤
      16 * ∑ x, ∑ y, w x * w y * e x y ^ 2 := by
  have key : ∀ a b c d : ℝ, (a - b - c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) :=
    fun a b c d => by
      nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a - d), sq_nonneg (b - c),
        sq_nonneg (b + d), sq_nonneg (c + d)]
  have hww : ∀ x y, 0 ≤ w x * w y := fun x y => mul_nonneg (hw x) (hw y)
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ x, ∑ y, w x * w y * e x y ^ 2 := ⟨_, rfl⟩
  have hQ : ∑ x, ∑ y, w x * w y * (∑ t, w t * e x t) ^ 2 ≤ A := by
    calc _ ≤ ∑ x, ∑ y, w x * w y * ∑ t, w t * e x t ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (sq_sum_mul_le_sum_mul_sq hw hw1) (hww x y)
      _ = A := by
          simp_rw [sum_mul_mul_const hw1, hA, Finset.mul_sum, mul_assoc]
  have hR : ∑ x, ∑ y, w x * w y * (∑ z, w z * e z y) ^ 2 ≤ A := by
    calc _ ≤ ∑ x, ∑ y, w x * w y * ∑ z, w z * e z y ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (sq_sum_mul_le_sum_mul_sq hw hw1) (hww x y)
      _ = ∑ y, ∑ z, w y * w z * e z y ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          simp_rw [sum_mul_mul_const_left hw1, Finset.mul_sum, mul_assoc]
      _ = A := by
          rw [hA, Finset.sum_comm]
          simp_rw [mul_comm (w _) (w _)]
  have hS : ∑ x, ∑ y, w x * w y * (∑ z, ∑ t, w z * w t * e z t) ^ 2 ≤ A := by
    simp_rw [sum_mul_mul_const hw1, sum_mul_const_of_sum_eq_one hw1]
    exact (sq_sum_sum_mul_le hw hw1 e).trans_eq hA.symm
  calc _ ≤ ∑ x, ∑ y, w x * w y * (4 * (e x y ^ 2 + (∑ t, w t * e x t) ^ 2 +
          (∑ z, w z * e z y) ^ 2 + (∑ z, ∑ t, w z * w t * e z t) ^ 2)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (key _ _ _ _) (hww x y)
    _ = 4 * (A + ∑ x, ∑ y, w x * w y * (∑ t, w t * e x t) ^ 2 +
          ∑ x, ∑ y, w x * w y * (∑ z, w z * e z y) ^ 2 +
          ∑ x, ∑ y, w x * w y * (∑ z, ∑ t, w z * w t * e z t) ^ 2) := by
        rw [hA]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    _ ≤ 16 * A := by linarith
    _ = _ := by rw [hA]

end Decoupling

section Main

variable {N : ℕ} {α : Type*} [Fintype α]

/-- The centred overlap is controlled by the overlap: `⟨(ξ̇¹ ⋅ ξ̇² / N)²⟩ ≤ 16 ⟨(R₁,₂ - q)²⟩`. -/
theorem sum_sum_sq_centered_overlap_le (ξ : Fin N → α → ℝ) {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (q : ℝ) :
    ∑ x, ∑ y, w x * w y * ((N : ℝ)⁻¹ * ∑ j, (ξ j x - ∑ b, w b * ξ j b) *
        (ξ j y - ∑ b, w b * ξ j b)) ^ 2 ≤
      16 * ∑ x, ∑ y, w x * w y * ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 := by
  simp_rw [centered_overlap_eq ξ hw1 q]
  exact sum_sum_sq_decoupled_le hw hw1 fun z t => (N : ℝ)⁻¹ * ∑ i, ξ i z * ξ i t - q

omit [Fintype α] in
/-- The overlap of two configurations lies in `[-1, 1]` when the observables do. -/
theorem abs_inv_mul_sum_mul_le_one (hN : 0 < N) (ξ : Fin N → α → ℝ) (hξ : ∀ i a, |ξ i a| ≤ 1)
    (x y : α) : |(N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y| ≤ 1 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [abs_mul, abs_inv, Nat.abs_cast, inv_mul_le_iff₀ hNpos, mul_one]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |ξ i x * ξ i y| ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        nlinarith [hξ i x, hξ i y, abs_nonneg (ξ i x), abs_nonneg (ξ i y)]
    _ = N := by simp

/-- **The deterministic half of Proposition 1.4.14.**  For a probability vector `w` on a finite
configuration space with `N` observables of modulus at most one, every `|q| ≤ 1` and `k : ℕ`,
the sum over `(k + 1)`-tuples `u` of sites of the squared centred correlation
`⟨(ξ_{u₀} - ⟨ξ_{u₀}⟩) ξ_{u₁} ⋯ ξ_{u_k}⟩²` is at most `4 k N^{k+1} ⟨(R₁,₂ - q)²⟩`. -/
theorem sum_sq_avg_centered_monomial_le (hN : 0 < N) (ξ : Fin N → α → ℝ)
    (hξ : ∀ i a, |ξ i a| ≤ 1) {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) {q : ℝ}
    (hq : |q| ≤ 1) (k : ℕ) :
    ∑ u : Fin (k + 1) → Fin N,
        (∑ a, w a * ((ξ (u 0) a - ∑ b, w b * ξ (u 0) b) * ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 ≤
      4 * k * N ^ (k + 1) * ∑ x, ∑ y, w x * w y *
        ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hww : ∀ x y, 0 ≤ w x * w y := fun x y => mul_nonneg (hw x) (hw y)
  have h16 := sum_sum_sq_centered_overlap_le ξ hw hw1 q
  obtain ⟨m, hm⟩ : ∃ m : Fin N → ℝ, ∀ j, m j = ∑ b, w b * ξ j b := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : α → α → ℝ, ∀ x y, R x y = (N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : α → α → ℝ, ∀ x y,
      C x y = (N : ℝ)⁻¹ * ∑ j, (ξ j x - m j) * (ξ j y - m j) := ⟨_, fun _ _ => rfl⟩
  simp only [← hm] at h16 ⊢
  simp only [← hR] at h16 ⊢
  simp only [← hC] at h16
  rw [sum_sq_avg_tuple ξ w m k]
  have hterm : ∀ x y, (∑ j, (ξ j x - m j) * (ξ j y - m j)) * (∑ i, ξ i x * ξ i y) ^ k =
      (N : ℝ) ^ (k + 1) * (C x y * R x y ^ k) := fun x y => by
    rw [hC, hR, mul_pow, inv_pow, pow_succ]
    field_simp
  have hzero : ∑ x, ∑ y, w x * w y * C x y = 0 := by
    have h0 : ∀ j, ∑ x, ∑ y, w x * w y * ((ξ j x - m j) * (ξ j y - m j)) = 0 := fun j => by
      rw [hm]; exact sum_sum_mul_centered hw1 (fun a => ξ j a)
    have hxyj : ∀ x y, w x * w y * C x y =
        (N : ℝ)⁻¹ * ∑ j, w x * w y * ((ξ j x - m j) * (ξ j y - m j)) := fun x y => by
      rw [hC, mul_left_comm, Finset.mul_sum]
    have hcomm : ∑ x, ∑ y, ∑ j, w x * w y * ((ξ j x - m j) * (ξ j y - m j)) =
        ∑ j, ∑ x, ∑ y, w x * w y * ((ξ j x - m j) * (ξ j y - m j)) :=
      (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
    have hpull : ∑ x, ∑ y, w x * w y * C x y = (N : ℝ)⁻¹ * ∑ x, ∑ y, ∑ j,
        w x * w y * ((ξ j x - m j) * (ξ j y - m j)) := by
      simp only [hxyj, Finset.mul_sum]
    rw [hpull, hcomm]
    simp [h0]
  have hshift : ∑ x, ∑ y, w x * w y * (C x y * R x y ^ k) =
      ∑ x, ∑ y, w x * w y * (C x y * (R x y ^ k - q ^ k)) := by
    have : ∀ x y, w x * w y * (C x y * R x y ^ k) =
        w x * w y * (C x y * (R x y ^ k - q ^ k)) + q ^ k * (w x * w y * C x y) := fun x y => by
      ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hzero]
    ring
  have hbd : ∀ x y, C x y * (R x y ^ k - q ^ k) ≤
      k * (2 * (R x y - q) ^ 2 + C x y ^ 2 / 8) := fun x y => by
    have hR1 : |R x y| ≤ 1 := by rw [hR]; exact abs_inv_mul_sum_mul_le_one hN ξ hξ x y
    have hpow := abs_pow_sub_pow_le (R x y) q k
    have hmax : max |R x y| |q| ^ (k - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
      (max_le hR1 hq)
    have h1 : |R x y ^ k - q ^ k| ≤ |R x y - q| * k := by
      calc _ ≤ |R x y - q| * k * max |R x y| |q| ^ (k - 1) := hpow
        _ ≤ |R x y - q| * k * 1 := mul_le_mul_of_nonneg_left hmax
            (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg k))
        _ = _ := mul_one _
    calc C x y * (R x y ^ k - q ^ k) ≤ |C x y * (R x y ^ k - q ^ k)| := le_abs_self _
      _ = |C x y| * |R x y ^ k - q ^ k| := abs_mul _ _
      _ ≤ |C x y| * (|R x y - q| * k) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = k * (|C x y| * |R x y - q|) := by ring
      _ ≤ k * (2 * (R x y - q) ^ 2 + C x y ^ 2 / 8) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg k)
          linarith [two_mul_le_add_mul_sq (a := |R x y - q|) (b := |C x y|)
            (by norm_num : (0 : ℝ) < 4), sq_abs (R x y - q), sq_abs (C x y)]
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ x, ∑ y, w x * w y * (R x y - q) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ x, ∑ y, w x * w y * C x y ^ 2 := ⟨_, rfl⟩
  have hsplit : ∑ x, ∑ y, w x * w y * (C x y * (R x y ^ k - q ^ k)) ≤ k * (2 * A + B / 8) := by
    calc _ ≤ ∑ x, ∑ y, w x * w y * (k * (2 * (R x y - q) ^ 2 + C x y ^ 2 / 8)) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hbd x y) (hww x y)
      _ = k * (2 * A + B / 8) := by
          have e : ∀ x y, w x * w y * (k * (2 * (R x y - q) ^ 2 + C x y ^ 2 / 8)) =
              k * (2 * (w x * w y * (R x y - q) ^ 2) + (w x * w y * C x y ^ 2) / 8) :=
            fun x y => by ring
          rw [hA, hB]
          simp_rw [e, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.sum_div]
  have hLHS : ∑ x, ∑ y, w x * w y * ((∑ j, (ξ j x - m j) * (ξ j y - m j)) *
      (∑ i, ξ i x * ξ i y) ^ k) =
      (N : ℝ) ^ (k + 1) * ∑ x, ∑ y, w x * w y * (C x y * R x y ^ k) := by
    simp only [hterm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hLHS, hshift]
  have hNk : (0 : ℝ) ≤ (N : ℝ) ^ (k + 1) := by positivity
  have hB16 : B ≤ 16 * A := by rw [hA, hB]; exact h16
  rw [← hA]
  calc (N : ℝ) ^ (k + 1) * _ ≤ (N : ℝ) ^ (k + 1) * (k * (2 * A + B / 8)) :=
        mul_le_mul_of_nonneg_left hsplit hNk
    _ ≤ (N : ℝ) ^ (k + 1) * (k * (2 * A + 16 * A / 8)) := by
        gcongr
    _ = 4 * k * N ^ (k + 1) * A := by ring

end Main

section Disorder

variable {N : ℕ} {Ω α : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A continuous function of random Gibbs weights is integrable: the weights stay in the compact
cube `[0, 1]^α`. -/
theorem integrable_comp_weights [Fintype α] [IsFiniteMeasure P] {w : Ω → α → ℝ}
    (hw0 : ∀ ω a, 0 ≤ w ω a) (hw1 : ∀ ω, ∑ a, w ω a = 1) (hwm : ∀ a, Measurable fun ω => w ω a)
    {Ψ : (α → ℝ) → ℝ} (hΨ : Continuous Ψ) : Integrable (fun ω => Ψ (w ω)) P := by
  have hK : IsCompact (Set.pi Set.univ fun _ : α => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΨ.continuousOn
  refine Integrable.of_bound (hΨ.measurable.comp (measurable_pi_iff.2 hwm)).aestronglyMeasurable C
    (ae_of_all _ fun ω => hC _ fun a _ => ⟨hw0 ω a, ?_⟩)
  calc w ω a ≤ ∑ b, w ω b := Finset.single_le_sum (f := w ω) (fun b _ => hw0 ω b) (mem_univ a)
    _ = 1 := hw1 ω

/-- **Invariance of the disorder average under a relabelling of the configurations:** if a
measure-preserving map `φ` of the disorder turns the random weights into their relabelling
`a ↦ w ω (σ a)`, the average of every continuous functional of the weights is unchanged by the
relabelling. -/
theorem integral_comp_weights_equiv [Finite α] {w : Ω → α → ℝ}
    (hwm : ∀ a, Measurable fun ω => w ω a) (σ : α ≃ α) {φ : Ω → Ω} (hφ : MeasurePreserving φ P P)
    (hφw : ∀ ω a, w (φ ω) a = w ω (σ a)) {Ψ : (α → ℝ) → ℝ} (hΨ : Continuous Ψ) :
    ∫ ω, Ψ (fun a => w ω (σ a)) ∂P = ∫ ω, Ψ (w ω) ∂P := by
  have hf : Measurable fun ω => Ψ (w ω) := hΨ.measurable.comp (measurable_pi_iff.2 hwm)
  have h := integral_map (μ := P) (φ := φ) (f := fun ω => Ψ (w ω)) hφ.measurable.aemeasurable
    (by rw [hφ.map_eq]; exact hf.aestronglyMeasurable)
  rw [hφ.map_eq] at h
  rw [h]
  exact integral_congr_ae (ae_of_all _ fun ω => by
    simp only [show w (φ ω) = fun a => w ω (σ a) from funext (hφw ω)])

end Disorder

section Symmetry

variable {N : ℕ} {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] {P : Measure Ω}
  {ξ : Fin N → α → ℝ} {w : Ω → α → ℝ}

/-- Relabelling the sites by `π` is the same as relabelling the configurations by `act π.symm`. -/
theorem sq_sum_comp_equiv (act : Equiv.Perm (Fin N) → α ≃ α)
    (hact : ∀ π i a, ξ i (act π a) = ξ (π i) a) (π : Equiv.Perm (Fin N)) {k : ℕ}
    (u : Fin (k + 1) → Fin N) (v : α → ℝ) :
    (∑ a, v (act π.symm a) * ((ξ (u 0) a - ∑ b, v (act π.symm b) * ξ (u 0) b) *
        ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 =
      (∑ a, v a * ((ξ (π (u 0)) a - ∑ b, v b * ξ (π (u 0)) b) *
        ∏ l : Fin k, ξ (π (u l.succ)) a)) ^ 2 := by
  have hσ : ∀ i a, ξ (π i) (act π.symm a) = ξ i a := fun i a => by
    rw [hact π.symm]; simp
  congr 1
  rw [← Equiv.sum_comp (act π.symm) (fun a => v a * ((ξ (π (u 0)) a -
    ∑ b, v b * ξ (π (u 0)) b) * ∏ l : Fin k, ξ (π (u l.succ)) a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (act π.symm) (fun b => v b * ξ (π (u 0)) b)]
  simp only [hσ]

/-- **Site symmetry of the squared centred correlation.**  If the law of the random Gibbs weights
is invariant under the relabellings `act π` of the configurations induced by permutations `π` of
the sites, then `𝔼 ⟨(ξ_{u₀} - ⟨ξ_{u₀}⟩) ξ_{u₁} ⋯ ξ_{u_k}⟩²` does not change when the tuple of
sites `u` is replaced by `π ∘ u`. -/
theorem integral_sq_centered_perm (hwm : ∀ a, Measurable fun ω => w ω a)
    (act : Equiv.Perm (Fin N) → α ≃ α) (hact : ∀ π i a, ξ i (act π a) = ξ (π i) a)
    (hsym : ∀ π : Equiv.Perm (Fin N), ∃ φ : Ω → Ω, MeasurePreserving φ P P ∧
      ∀ ω a, w (φ ω) a = w ω (act π a))
    (π : Equiv.Perm (Fin N)) {k : ℕ} (u : Fin (k + 1) → Fin N) :
    ∫ ω, (∑ a, w ω a * ((ξ (π (u 0)) a - ∑ b, w ω b * ξ (π (u 0)) b) *
        ∏ l : Fin k, ξ (π (u l.succ)) a)) ^ 2 ∂P =
      ∫ ω, (∑ a, w ω a * ((ξ (u 0) a - ∑ b, w ω b * ξ (u 0) b) *
        ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 ∂P := by
  have hc : Continuous fun v : α → ℝ => (∑ a, v a * ((ξ (u 0) a - ∑ b, v b * ξ (u 0) b) *
      ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 := by fun_prop
  obtain ⟨φ, hφ, hφw⟩ := hsym π.symm
  have h := integral_comp_weights_equiv hwm (act π.symm) hφ hφw hc
  simp_rw [sq_sum_comp_equiv act hact π u] at h
  exact h

end Symmetry

section Proposition

variable {N : ℕ} {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] {P : Measure Ω}
  [IsProbabilityMeasure P] {ξ : Fin N → α → ℝ} {w : Ω → α → ℝ}

/-- **The step of Proposition 1.4.14.**  In a site-symmetric random Gibbs state, for every tuple
of `k + 1` distinct sites `u`,
`𝔼 ⟨(ξ_{u₀} - ⟨ξ_{u₀}⟩) ξ_{u₁} ⋯ ξ_{u_k}⟩² ≤ 4 k (k + 1)^{k+1} ν((R₁,₂ - q)²)`
for every `|q| ≤ 1`, where `ν = 𝔼 ⟨⋅⟩^{⊗2}`.  The constant is the book's
`N^k / (N (N - 1) ⋯ (N - k))` bound times the deterministic constant `4 k`. -/
theorem integral_sq_centered_le (hN : 0 < N) (hξ : ∀ i a, |ξ i a| ≤ 1)
    (hw0 : ∀ ω a, 0 ≤ w ω a) (hw1 : ∀ ω, ∑ a, w ω a = 1) (hwm : ∀ a, Measurable fun ω => w ω a)
    (act : Equiv.Perm (Fin N) → α ≃ α) (hact : ∀ π i a, ξ i (act π a) = ξ (π i) a)
    (hsym : ∀ π : Equiv.Perm (Fin N), ∃ φ : Ω → Ω, MeasurePreserving φ P P ∧
      ∀ ω a, w (φ ω) a = w ω (act π a)) {q : ℝ}
    (hq : |q| ≤ 1) {k : ℕ} {u : Fin (k + 1) → Fin N} (hu : Function.Injective u) :
    ∫ ω, (∑ a, w ω a * ((ξ (u 0) a - ∑ b, w ω b * ξ (u 0) b) *
        ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 ∂P ≤
      4 * k * (k + 1) ^ (k + 1) * ∫ ω, ∑ x, ∑ y, w ω x * w ω y *
        ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 ∂P := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin (k + 1) → Fin N) → Ω → ℝ, ∀ u ω, Φ u ω = (∑ a, w ω a *
      ((ξ (u 0) a - ∑ b, w ω b * ξ (u 0) b) * ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Aw, hAw⟩ : ∃ Aw : Ω → ℝ, ∀ ω, Aw ω = ∑ x, ∑ y, w ω x * w ω y *
      ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 := ⟨_, fun _ => rfl⟩
  have hint : ∀ u, Integrable (Φ u) P := fun u => by
    have h : Φ u = fun ω => (fun v : α → ℝ => (∑ a, v a * ((ξ (u 0) a - ∑ b, v b * ξ (u 0) b) *
        ∏ l : Fin k, ξ (u l.succ) a)) ^ 2) (w ω) := funext (hΦ u)
    rw [h]
    exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : α → ℝ => (∑ a, v a *
      ((ξ (u 0) a - ∑ b, v b * ξ (u 0) b) * ∏ l : Fin k, ξ (u l.succ) a)) ^ 2) (by fun_prop)
  have hA : Integrable Aw P := by
    have h : Aw = fun ω => (fun v : α → ℝ => ∑ x, ∑ y, v x * v y *
        ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2) (w ω) := funext hAw
    rw [h]
    exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : α → ℝ => ∑ x, ∑ y, v x * v y *
      ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2) (by fun_prop)
  have hT0 : ∀ u, 0 ≤ ∫ ω, Φ u ω ∂P := fun u =>
    integral_nonneg fun ω => by rw [hΦ]; exact sq_nonneg _
  have hTperm : ∀ (π : Equiv.Perm (Fin N)) u, ∫ ω, Φ (π ∘ u) ω ∂P = ∫ ω, Φ u ω ∂P :=
    fun π u => by
      simp only [hΦ]
      exact integral_sq_centered_perm hwm act hact hsym π u
  have hdesc := Fin.descFactorial_mul_le_sum hT0 hTperm hu
  have hdet : ∀ ω, ∑ u', Φ u' ω ≤ 4 * k * (N : ℝ) ^ (k + 1) * Aw ω := fun ω => by
    simp only [hΦ, hAw]
    exact sum_sq_avg_centered_monomial_le hN ξ hξ (hw0 ω) (hw1 ω) hq k
  have hsum : ∑ u', ∫ ω, Φ u' ω ∂P ≤ 4 * k * (N : ℝ) ^ (k + 1) * ∫ ω, Aw ω ∂P := by
    rw [← integral_finsetSum _ fun u' _ => hint u', ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun u' _ => hint u') (hA.const_mul _) hdet
  have hX : 0 ≤ ∫ ω, Aw ω ∂P := integral_nonneg fun ω => by
    rw [hAw]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (hw0 ω x) (hw0 ω y)) (sq_nonneg _)
  have hkN : k + 1 ≤ N := by simpa using Fintype.card_le_of_injective u hu
  have hpow : (N : ℝ) ^ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) * (N.descFactorial (k + 1) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_mul_descFactorial hkN
  have hdpos : (0 : ℝ) < N.descFactorial (k + 1) := by exact_mod_cast Nat.descFactorial_pos.2 hkN
  have e1 : ∫ ω, (∑ a, w ω a * ((ξ (u 0) a - ∑ b, w ω b * ξ (u 0) b) *
      ∏ l : Fin k, ξ (u l.succ) a)) ^ 2 ∂P = ∫ ω, Φ u ω ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => (hΦ u ω).symm)
  have e2 : ∫ ω, ∑ x, ∑ y, w ω x * w ω y * ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 ∂P =
      ∫ ω, Aw ω ∂P := integral_congr_ae (ae_of_all _ fun ω => (hAw ω).symm)
  rw [e1, e2]
  refine le_of_mul_le_mul_left ?_ hdpos
  calc (N.descFactorial (k + 1) : ℝ) * ∫ ω, Φ u ω ∂P ≤ 4 * k * (N : ℝ) ^ (k + 1) * _ :=
        hdesc.trans hsum
    _ ≤ 4 * k * (((k + 1 : ℕ) : ℝ) ^ (k + 1) * (N.descFactorial (k + 1) : ℝ)) * _ := by
        gcongr
    _ = _ := by push_cast; ring

/-- The constant `K(p)` of Proposition 1.4.14: `K(0) = 0` and
`K(p + 1) = 8 p (p + 1)^{p+1} + 2 K(p)`. -/
def spinDecorrConst : ℕ → ℝ
  | 0 => 0
  | p + 1 => 8 * p * (p + 1) ^ (p + 1) + 2 * spinDecorrConst p

theorem spinDecorrConst_nonneg (p : ℕ) : 0 ≤ spinDecorrConst p := by
  induction p with
  | zero => simp [spinDecorrConst]
  | succ p ih => simp only [spinDecorrConst]; positivity

theorem spinDecorrConst_mono : Monotone spinDecorrConst :=
  monotone_nat_of_le_succ fun p => by
    have := spinDecorrConst_nonneg p
    simp only [spinDecorrConst]
    have : (0 : ℝ) ≤ 8 * p * (p + 1) ^ (p + 1) := by positivity
    linarith

/-- **Proposition 1.4.14 for distinct sites (Talagrand).**  In a site-symmetric random Gibbs state
with `[-1, 1]`-valued observables, for every `|q| ≤ 1` and every tuple `u` of `p` distinct sites,
`𝔼 (⟨ξ_{u₁} ⋯ ξ_{u_p}⟩ - ⟨ξ_{u₁}⟩ ⋯ ⟨ξ_{u_p}⟩)² ≤ K(p) ν((R₁,₂ - q)²)`, where
`ν = 𝔼 ⟨⋅⟩^{⊗2}` and `R₁,₂ = N⁻¹ ∑ᵢ ξᵢ¹ ξᵢ²`.  The only property of the model used is the symmetry
between sites. -/
theorem integral_sq_prod_sub_prod_le (hN : 0 < N) (hξ : ∀ i a, |ξ i a| ≤ 1)
    (hw0 : ∀ ω a, 0 ≤ w ω a) (hw1 : ∀ ω, ∑ a, w ω a = 1) (hwm : ∀ a, Measurable fun ω => w ω a)
    (act : Equiv.Perm (Fin N) → α ≃ α) (hact : ∀ π i a, ξ i (act π a) = ξ (π i) a)
    (hsym : ∀ π : Equiv.Perm (Fin N), ∃ φ : Ω → Ω, MeasurePreserving φ P P ∧
      ∀ ω a, w (φ ω) a = w ω (act π a)) {q : ℝ}
    (hq : |q| ≤ 1) {p : ℕ} {u : Fin p → Fin N} (hu : Function.Injective u) :
    ∫ ω, (∑ a, w ω a * ∏ l, ξ (u l) a - ∏ l, ∑ a, w ω a * ξ (u l) a) ^ 2 ∂P ≤
      spinDecorrConst p * ∫ ω, ∑ x, ∑ y, w ω x * w ω y *
        ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 ∂P := by
  induction p with
  | zero =>
    have h0 : ∀ ω, ∑ a, w ω a * ∏ l : Fin 0, ξ (u l) a - ∏ l : Fin 0, ∑ a, w ω a * ξ (u l) a
        = 0 := fun ω => by simp [hw1 ω]
    simp only [h0]
    simp [spinDecorrConst]
  | succ p ih =>
    obtain ⟨m, hm⟩ : ∃ m : Ω → Fin N → ℝ, ∀ ω i, m ω i = ∑ a, w ω a * ξ i a :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∫ ω, ∑ x, ∑ y, w ω x * w ω y *
        ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 ∂P := ⟨_, rfl⟩
    rw [← hX]
    simp only [← hm]
    have hm1 : ∀ ω i, |m ω i| ≤ 1 := fun ω i => by
      rw [hm]; exact abs_sum_mul_le (hw0 ω) (hw1 ω) fun a => hξ i a
    -- the tail tuple
    have hutail : Function.Injective fun l : Fin p => u l.succ := hu.comp (Fin.succ_injective p)
    have ih' := ih hutail
    rw [← hX] at ih'
    simp only [← hm] at ih'
    -- the centred step
    have hstep := integral_sq_centered_le hN hξ hw0 hw1 hwm act hact hsym hq hu
    rw [← hX] at hstep
    simp only [← hm] at hstep
    have hint_a : Integrable (fun ω => (∑ a, w ω a * ∏ l : Fin (p + 1), ξ (u l) a -
        ∏ l : Fin (p + 1), m ω (u l)) ^ 2) P := by
      simp only [hm]
      exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : α → ℝ => (∑ a, v a *
        ∏ l : Fin (p + 1), ξ (u l) a - ∏ l : Fin (p + 1), ∑ a, v a * ξ (u l) a) ^ 2)
        (by fun_prop)
    have hint_b : Integrable (fun ω => (∑ a, w ω a * ∏ l : Fin p, ξ (u l.succ) a -
        ∏ l : Fin p, m ω (u l.succ)) ^ 2) P := by
      simp only [hm]
      exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : α → ℝ => (∑ a, v a *
        ∏ l : Fin p, ξ (u l.succ) a - ∏ l : Fin p, ∑ a, v a * ξ (u l.succ) a) ^ 2)
        (by fun_prop)
    have hint_c : Integrable (fun ω => (∑ a, w ω a * ((ξ (u 0) a - m ω (u 0)) *
        ∏ l : Fin p, ξ (u l.succ) a)) ^ 2) P := by
      simp only [hm]
      exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : α → ℝ => (∑ a, v a *
        ((ξ (u 0) a - ∑ b, v b * ξ (u 0) b) * ∏ l : Fin p, ξ (u l.succ) a)) ^ 2)
        (by fun_prop)
    have key : ∀ S1 S2 mm Pm : ℝ, |mm| ≤ 1 →
        (S1 - mm * Pm) ^ 2 ≤ 2 * (S1 - mm * S2) ^ 2 + 2 * (S2 - Pm) ^ 2 := fun S1 S2 mm Pm hmm => by
      have h1 : mm ^ 2 ≤ 1 := by
        have := abs_le.1 hmm
        nlinarith
      nlinarith [sq_nonneg (S1 - mm * S2 - mm * (S2 - Pm)), mul_nonneg (sub_nonneg.2 h1)
        (sq_nonneg (S2 - Pm))]
    have hpt : ∀ ω, (∑ a, w ω a * ∏ l : Fin (p + 1), ξ (u l) a -
        ∏ l : Fin (p + 1), m ω (u l)) ^ 2 ≤
        2 * (∑ a, w ω a * ((ξ (u 0) a - m ω (u 0)) * ∏ l : Fin p, ξ (u l.succ) a)) ^ 2 +
        2 * (∑ a, w ω a * ∏ l : Fin p, ξ (u l.succ) a - ∏ l : Fin p, m ω (u l.succ)) ^ 2 :=
      fun ω => by
        have hc : ∑ a, w ω a * ((ξ (u 0) a - m ω (u 0)) * ∏ l : Fin p, ξ (u l.succ) a) =
            ∑ a, w ω a * (ξ (u 0) a * ∏ l : Fin p, ξ (u l.succ) a) -
              m ω (u 0) * ∑ a, w ω a * ∏ l : Fin p, ξ (u l.succ) a := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun a _ => by ring
        rw [hc]
        simp only [Fin.prod_univ_succ]
        exact key _ _ _ _ (hm1 ω (u 0))
    calc _ ≤ ∫ ω, (2 * (∑ a, w ω a * ((ξ (u 0) a - m ω (u 0)) *
            ∏ l : Fin p, ξ (u l.succ) a)) ^ 2 +
          2 * (∑ a, w ω a * ∏ l : Fin p, ξ (u l.succ) a - ∏ l : Fin p, m ω (u l.succ)) ^ 2) ∂P :=
          integral_mono hint_a ((hint_c.const_mul 2).add (hint_b.const_mul 2)) hpt
      _ = 2 * ∫ ω, (∑ a, w ω a * ((ξ (u 0) a - m ω (u 0)) * ∏ l : Fin p, ξ (u l.succ) a)) ^ 2 ∂P +
          2 * ∫ ω, (∑ a, w ω a * ∏ l : Fin p, ξ (u l.succ) a -
            ∏ l : Fin p, m ω (u l.succ)) ^ 2 ∂P := by
          rw [integral_add (hint_c.const_mul 2) (hint_b.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * (4 * p * (p + 1) ^ (p + 1) * X) + 2 * (spinDecorrConst p * X) := by
          gcongr
      _ = _ := by simp only [spinDecorrConst]; ring

/-- **Proposition 1.4.14 for a set of sites (Talagrand).**  The same bound for the product over a
set `S` of sites, with constant `K(|S|)`:
`𝔼 (⟨∏_{i ∈ S} ξᵢ⟩ - ∏_{i ∈ S} ⟨ξᵢ⟩)² ≤ K(|S|) ν((R₁,₂ - q)²)`. -/
theorem integral_sq_prod_sub_prod_le_finset (hN : 0 < N) (hξ : ∀ i a, |ξ i a| ≤ 1)
    (hw0 : ∀ ω a, 0 ≤ w ω a) (hw1 : ∀ ω, ∑ a, w ω a = 1) (hwm : ∀ a, Measurable fun ω => w ω a)
    (act : Equiv.Perm (Fin N) → α ≃ α) (hact : ∀ π i a, ξ i (act π a) = ξ (π i) a)
    (hsym : ∀ π : Equiv.Perm (Fin N), ∃ φ : Ω → Ω, MeasurePreserving φ P P ∧
      ∀ ω a, w (φ ω) a = w ω (act π a)) {q : ℝ}
    (hq : |q| ≤ 1) (S : Finset (Fin N)) :
    ∫ ω, (∑ a, w ω a * ∏ i ∈ S, ξ i a - ∏ i ∈ S, ∑ a, w ω a * ξ i a) ^ 2 ∂P ≤
      spinDecorrConst S.card * ∫ ω, ∑ x, ∑ y, w ω x * w ω y *
        ((N : ℝ)⁻¹ * ∑ i, ξ i x * ξ i y - q) ^ 2 ∂P := by
  have hu : Function.Injective fun l : Fin S.card => (S.equivFin.symm l : Fin N) :=
    Subtype.val_injective.comp S.equivFin.symm.injective
  have hprod : ∀ g : Fin N → ℝ, ∏ l : Fin S.card, g (S.equivFin.symm l : Fin N) = ∏ i ∈ S, g i :=
    fun g => by
      rw [← Finset.prod_coe_sort S g]
      exact Fintype.prod_equiv S.equivFin.symm _ _ fun _ => rfl
  refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ω => ?_))
    (integral_sq_prod_sub_prod_le hN hξ hw0 hw1 hwm act hact hsym hq hu)
  have h1 : ∀ a, ∏ l : Fin S.card, ξ (S.equivFin.symm l : Fin N) a = ∏ i ∈ S, ξ i a :=
    fun a => hprod (fun i => ξ i a)
  simp only [h1, hprod (fun i => ∑ a, w ω a * ξ i a)]

end Proposition

end SpinGlasses
