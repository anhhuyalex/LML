/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.PosSemidef
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Cholesky factorization of an infinite positive semidefinite array

For an array `A : ℕ → ℕ → ℝ` all of whose finite principal submatrices are positive semidefinite,
`Matrix.cholInf A` is a lower triangular array `L` with `A l l' = ∑_k L l k * L l' k`, where only
the finitely many `k ≤ min l l'` contribute.  Every entry of `L` is an explicit measurable
function of `A` (`Matrix.measurable_cholInf`), which makes `L` usable to build Gaussian arrays with
a random covariance without any Kolmogorov extension: `g l i = ∑_{k ≤ l} L l k ξ k i` is a finite
sum of i.i.d. Gaussians.

## Main declarations

* `Matrix.cholInf`: the factor, defined by well-founded recursion on `(l, k)`.
* `Matrix.measurable_cholInf`: `A ↦ cholInf A l k` is measurable (product σ-algebra).
* `Matrix.sum_cholInf_mul_eq`: `∑_{j<K} L l j * L l' j = A l l'` for `K > max l l'` when every
  finite principal submatrix of `A` is positive semidefinite.
* `Matrix.sum_cholInf_mul_eq_dotProduct`: the finite sum `∑_{k ≤ m} L m k c k` is the dot product
  of the first `N > m` coordinates of row `m` of `L` with those of `c`.
* `Matrix.inner_cholInf_realization`: the rows of `L`, placed along an orthonormal sequence of an
  inner product space, realize `A` as a Gram matrix.

## Implementation notes

Zero pivots are handled by setting `L l k = 0` below a zero pivot.  Correctness rests on the
positive semidefiniteness of every Schur complement (`psd_residual`), proved by induction on the
number of eliminated indices: eliminating a positive pivot is a rank one downdate of a positive
semidefinite form, and below a zero pivot the whole column of the residual vanishes by
Cauchy–Schwarz (`residual_offdiag_eq_zero`).
-/

@[expose] public section

open Finset
open scoped Matrix RealInnerProductSpace

namespace Matrix

/-- The lower triangular Cholesky factor `L` of an infinite array `A : ℕ → ℕ → ℝ`, computed row by
row: for `k < l`, `L l k = (A l k - ∑_{j<k} L l j L k j) / L k k` (and `0` if the pivot `L k k` is
zero), `L l l = √(A l l - ∑_{j<l} (L l j)²)`, and `L l k = 0` for `k > l`.  The formulas make sense
for every array and are measurable in `A` (`measurable_cholInf`); when all finite principal
submatrices of `A` are positive semidefinite, `L Lᵀ = A` (`sum_cholInf_mul_eq`).  Unlike the
Cholesky decomposition of `Matrix.PosDef` matrices, zero pivots are allowed. -/
noncomputable def cholInf (A : ℕ → ℕ → ℝ) (l k : ℕ) : ℝ :=
  if hk : k < l then
    if cholInf A k k = 0 then 0
    else (A l k - ∑ j : Fin k, cholInf A l j * cholInf A k j) / cholInf A k k
  else if hkl : k = l then √(A l l - ∑ j : Fin l, cholInf A l j ^ 2)
  else 0
termination_by (l, k)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ hk
    | exact Prod.Lex.right _ j.2
    | exact Prod.Lex.right _ (hkl ▸ j.2)

section
variable (A : ℕ → ℕ → ℝ)

lemma cholInf_of_gt {l k : ℕ} (h : l < k) : cholInf A l k = 0 := by
  rw [cholInf]; simp [h.not_gt, h.ne']

lemma cholInf_self (l : ℕ) :
    cholInf A l l = √(A l l - ∑ j ∈ range l, cholInf A l j * cholInf A l j) := by
  rw [cholInf]
  simp only [lt_irrefl, dite_false, dite_true, sq]
  rw [Fin.sum_univ_eq_sum_range (fun j => cholInf A l j * cholInf A l j) l]

lemma cholInf_of_lt {l k : ℕ} (h : k < l) : cholInf A l k =
    if cholInf A k k = 0 then 0
    else (A l k - ∑ j ∈ range k, cholInf A l j * cholInf A k j) / cholInf A k k := by
  rw [cholInf]
  simp only [h, dite_true, Fin.sum_univ_eq_sum_range (fun j => cholInf A l j * cholInf A k j) k]

private lemma quad_add_single {E : ℕ → ℕ → ℝ} (hE : ∀ l l', E l l' = E l' l) {N m : ℕ} (hm : m < N)
    (x : ℕ → ℝ) (t : ℝ) :
    ∑ l ∈ range N, ∑ l' ∈ range N, (x l + if l = m then t else 0) *
        (x l' + if l' = m then t else 0) * E l l' =
      ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' * E l l' +
        2 * t * ∑ l ∈ range N, x l * E l m + t ^ 2 * E m m := by
  have hm' : m ∈ range N := mem_range.2 hm
  have h1 : ∀ l, ∑ l' ∈ range N, (x l + if l = m then t else 0) *
      (x l' + if l' = m then t else 0) * E l l' =
      ∑ l' ∈ range N, x l * x l' * E l l' + x l * t * E l m +
        (if l = m then t * ∑ l' ∈ range N, x l' * E l l' + t ^ 2 * E l m else 0) := by
    intro l
    have : ∀ l', (x l + if l = m then t else 0) * (x l' + if l' = m then t else 0) * E l l' =
        x l * x l' * E l l' + (if l' = m then x l * t * E l l' else 0) +
        (if l = m then t * (x l' * E l l') else 0) +
        (if l = m ∧ l' = m then t ^ 2 * E l l' else 0) := by
      intro l'
      by_cases h1 : l = m <;> by_cases h2 : l' = m <;> simp [h1, h2] <;> ring
    simp_rw [this, sum_add_distrib]
    by_cases hl : l = m
    · subst hl
      simp [hm', mul_sum, add_assoc]
    · simp [hl, hm']
  rw [sum_congr rfl fun l _ => h1 l]
  simp only [sum_add_distrib, sum_ite_eq', hm', ite_true]
  have h2 : ∑ l' ∈ range N, x l' * E m l' = ∑ l ∈ range N, x l * E l m :=
    sum_congr rfl fun l _ => by rw [hE m l]
  rw [h2]
  have h3 : ∑ l ∈ range N, x l * t * E l m = t * ∑ l ∈ range N, x l * E l m := by
    rw [mul_sum]; exact sum_congr rfl fun l _ => by ring
  rw [h3]
  ring


variable {A}

private lemma cholInf_self_sq {m : ℕ}
    (h : 0 ≤ A m m - ∑ j ∈ range m, cholInf A m j * cholInf A m j) :
    cholInf A m m ^ 2 = A m m - ∑ j ∈ range m, cholInf A m j * cholInf A m j := by
  rw [cholInf_self A m]; exact Real.sq_sqrt h

private lemma cholInf_mul_pivot {l m : ℕ} (hlt : m < l) (hp : cholInf A m m ≠ 0) :
    cholInf A l m * cholInf A m m = A l m - ∑ j ∈ range m, cholInf A l j * cholInf A m j := by
  rw [cholInf_of_lt A hlt]
  simp only [hp, ite_false]
  field_simp

private lemma cholInf_eq_zero_of_pivot {l m : ℕ} (hlt : m < l) (hp : cholInf A m m = 0) :
    cholInf A l m = 0 := by
  rw [cholInf_of_lt A hlt]
  simp only [hp, ite_true]

/-- Every Schur complement `A l l' - ∑_{j<m} L l j L l' j` of a positive semidefinite array is
positive semidefinite on the indices `≥ m`. -/
private lemma psd_residual (hA : ∀ l l', A l l' = A l' l)
    (hP : ∀ (N : ℕ) (x : ℕ → ℝ), 0 ≤ ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' * A l l') (m : ℕ) :
    ∀ (N : ℕ) (x : ℕ → ℝ), (∀ l < m, x l = 0) →
      0 ≤ ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' *
        (A l l' - ∑ j ∈ range m, cholInf A l j * cholInf A l' j) := by
  induction m with
  | zero => intro N x _; simpa using hP N x
  | succ m ih =>
    intro N x hx
    have hE1 : ∀ l l', (A l l' - ∑ j ∈ range (m + 1), cholInf A l j * cholInf A l' j) =
        (A l l' - ∑ j ∈ range m, cholInf A l j * cholInf A l' j) -
          cholInf A l m * cholInf A l' m := by
      intro l l'; rw [sum_range_succ]; ring
    simp_rw [hE1]
    set E : ℕ → ℕ → ℝ := fun l l' => A l l' - ∑ j ∈ range m, cholInf A l j * cholInf A l' j
      with hEdef
    have hEs : ∀ l l', E l l' = E l' l := by
      intro l l'
      simp only [hEdef]
      rw [hA l l']
      exact congrArg _ (sum_congr rfl fun j _ => mul_comm _ _)
    have hrank : ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' *
          (E l l' - cholInf A l m * cholInf A l' m) =
        ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' * E l l' -
          (∑ l ∈ range N, x l * cholInf A l m) ^ 2 := by
      simp only [mul_sub, sum_sub_distrib]
      congr 1
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun l _ => sum_congr rfl fun l' _ => by ring
    rw [hrank]
    by_cases hN : N ≤ m
    · have h0 : ∀ l ∈ range N, x l = 0 := fun l hl => hx l (by have := mem_range.1 hl; omega)
      have h1 : ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' * E l l' = 0 :=
        sum_eq_zero fun l hl => by simp [h0 l hl]
      have h2 : ∑ l ∈ range N, x l * cholInf A l m = 0 :=
        sum_eq_zero fun l hl => by simp [h0 l hl]
      simp [h1, h2]
    replace hN : m < N := not_le.1 hN
    have hmN : m ∈ range N := mem_range.2 hN
    have hEmm : 0 ≤ E m m := by
      have h := ih N (fun l => if l = m then 1 else 0) (fun l hl => by simp [hl.ne])
      have h' : (∑ l ∈ range N, ∑ l' ∈ range N, (if l = m then (1 : ℝ) else 0) *
          (if l' = m then (1 : ℝ) else 0) *
          (A l l' - ∑ j ∈ range m, cholInf A l j * cholInf A l' j)) = E m m := by
        simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', hmN,
          ite_true]
        rfl
      rwa [h'] at h
    by_cases hp : cholInf A m m = 0
    · have hS : ∑ l ∈ range N, x l * cholInf A l m = 0 := by
        refine sum_eq_zero fun l _ => ?_
        rcases lt_trichotomy l m with h | h | h
        · rw [cholInf_of_gt A h]; ring
        · subst h; rw [hp]; ring
        · rw [cholInf_eq_zero_of_pivot h hp]; ring
      rw [hS]
      simpa using ih N x fun l hl => hx l (by omega)
    · have hsq : cholInf A m m ^ 2 = E m m := cholInf_self_sq hEmm
      set S := ∑ l ∈ range N, x l * cholInf A l m with hS
      set t := -S / cholInf A m m with ht
      have hx' : ∀ l < m, (x l + if l = m then t else 0) = 0 := fun l hl => by
        simp [hx l (by omega), hl.ne]
      have h := ih N (fun l => x l + if l = m then t else 0) hx'
      rw [quad_add_single hEs hN x t] at h
      have hcross : ∑ l ∈ range N, x l * E l m = S * cholInf A m m := by
        rw [hS, sum_mul]
        refine sum_congr rfl fun l _ => ?_
        rcases lt_trichotomy l m with h | h | h
        · rw [hx l (by omega)]; ring
        · subst h; rw [hx l (by omega)]; ring
        · rw [mul_assoc, cholInf_mul_pivot h hp]
      rw [hcross] at h
      have e1 : 2 * t * (S * cholInf A m m) = -2 * S ^ 2 := by
        rw [ht]; field_simp
      have e2 : t ^ 2 * E m m = S ^ 2 := by
        rw [← hsq, ht]; field_simp
      linarith


section Gram

variable (hA : ∀ l l', A l l' = A l' l)
  (hP : ∀ (N : ℕ) (x : ℕ → ℝ), 0 ≤ ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' * A l l')
include hA hP

private lemma residual_diag_nonneg {m l : ℕ} (hml : m ≤ l) :
    0 ≤ A l l - ∑ j ∈ range m, cholInf A l j * cholInf A l j := by
  have h := psd_residual hA hP m (l + 1) (fun l' => if l' = l then 1 else 0)
    fun l' hl' => by simp [(show l' ≠ l by omega)]
  have hl : l ∈ range (l + 1) := mem_range.2 (Nat.lt_succ_self l)
  simpa [ite_mul, mul_ite, sum_ite_eq', hl] using h

private lemma residual_offdiag_eq_zero {l m : ℕ} (hlt : m < l) (hp : cholInf A m m = 0) :
    A l m - ∑ j ∈ range m, cholInf A l j * cholInf A m j = 0 := by
  set E : ℕ → ℕ → ℝ := fun l l' => A l l' - ∑ j ∈ range m, cholInf A l j * cholInf A l' j
    with hEdef
  have hEs : ∀ l l', E l l' = E l' l := by
    intro l l'
    simp only [hEdef]
    rw [hA l l']
    exact congrArg _ (sum_congr rfl fun j _ => mul_comm _ _)
  have hEmm : E m m = 0 := by
    have h2 := cholInf_self_sq (residual_diag_nonneg hA hP (le_refl m))
    rw [hp] at h2
    simpa using h2.symm
  have hEll : 0 ≤ E l l := residual_diag_nonneg hA hP hlt.le
  by_contra he
  have he' : E l m ≠ 0 := he
  set a := -(E l l + 1) / E l m with ha
  have h := psd_residual hA hP m (l + 1) (fun l' => (if l' = l then 1 else 0) +
    if l' = m then a else 0) fun l' hl' => by simp [(show l' ≠ l by omega), (show l' ≠ m by omega)]
  have hlN : m < l + 1 := by omega
  rw [quad_add_single hEs hlN] at h
  have hl : l ∈ range (l + 1) := mem_range.2 (Nat.lt_succ_self l)
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, sum_ite_eq', hl, ite_true] at h
  have e : 2 * a * E l m = -2 * (E l l + 1) := by rw [ha]; field_simp
  rw [hEmm] at h
  linarith

/-- The Gram identity, for `m ≤ l`. -/
private lemma sum_cholInf_mul_le {l m : ℕ} (hml : m ≤ l) :
    ∑ j ∈ range (m + 1), cholInf A l j * cholInf A m j = A l m := by
  rw [sum_range_succ]
  rcases hml.eq_or_lt with h | h
  · subst h
    have := cholInf_self_sq (residual_diag_nonneg hA hP (le_refl m))
    linarith
  · by_cases hp : cholInf A m m = 0
    · rw [cholInf_eq_zero_of_pivot h hp, hp]
      linarith [residual_offdiag_eq_zero hA hP h hp]
    · linarith [cholInf_mul_pivot h hp]

private theorem sum_cholInf_mul (l l' : ℕ) :
    ∑ j ∈ range (min l l' + 1), cholInf A l j * cholInf A l' j = A l l' := by
  rcases le_total l' l with h | h
  · rw [min_eq_right h]; exact sum_cholInf_mul_le hA hP h
  · rw [min_eq_left h, hA l l']
    rw [← sum_cholInf_mul_le hA hP h]
    exact sum_congr rfl fun j _ => mul_comm _ _

end Gram

end

variable {A}

/-- Every entry of the Cholesky factor is a measurable function of the array. -/
theorem measurable_cholInf (l k : ℕ) : Measurable fun A : ℕ → ℕ → ℝ => cholInf A l k := by
  induction l using Nat.strong_induction_on generalizing k with
  | _ l ihl =>
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      have hA : ∀ a b : ℕ, Measurable fun A : ℕ → ℕ → ℝ => A a b := fun a b =>
        (measurable_pi_apply b).comp (measurable_pi_apply a)
      rcases lt_trichotomy k l with h | h | h
      · have hk : (fun A : ℕ → ℕ → ℝ => cholInf A l k) = fun A =>
            if cholInf A k k = 0 then 0
            else (A l k - ∑ j ∈ range k, cholInf A l j * cholInf A k j) / cholInf A k k :=
          funext fun A => cholInf_of_lt A h
        rw [hk]
        exact Measurable.ite (measurableSet_eq_fun (ihl k h k) measurable_const) measurable_const
          (((hA l k).sub (Finset.measurable_sum _ fun j hj =>
            (ihk j (mem_range.1 hj)).mul (ihl k h j))).div (ihl k h k))
      · subst h
        have hk : (fun A : ℕ → ℕ → ℝ => cholInf A k k) = fun A =>
            √(A k k - ∑ j ∈ range k, cholInf A k j * cholInf A k j) :=
          funext fun A => cholInf_self A k
        rw [hk]
        exact Real.continuous_sqrt.measurable.comp ((hA k k).sub
          (Finset.measurable_sum _ fun j hj => (ihk j (mem_range.1 hj)).mul
            (ihk j (mem_range.1 hj))))
      · have hk : (fun A : ℕ → ℕ → ℝ => cholInf A l k) = fun _ => 0 :=
          funext fun A => cholInf_of_gt A h
        rw [hk]
        exact measurable_const

/-- **Cholesky factorization of an infinite positive semidefinite array.**  If every finite
principal submatrix of `A` is positive semidefinite, then the rows of the lower triangular array
`cholInf A` have Gram matrix `A`: `∑_{j<K} L l j * L l' j = A l l'` for `K > max l l'`. -/
theorem sum_cholInf_mul_eq
    (hA : ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef) (l l' K : ℕ)
    (hK : max l l' < K) :
    ∑ j ∈ range K, cholInf A l j * cholInf A l' j = A l l' := by
  have hsymm := posSemidef_symm hA
  have hP : ∀ (N : ℕ) (x : ℕ → ℝ),
      0 ≤ ∑ l ∈ range N, ∑ l' ∈ range N, x l * x l' * A l l' := fun N x => by
    have h := (hA N).sum_mul_mul_nonneg (fun i : Fin N => x i)
    simp only [Matrix.of_apply] at h
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, x i * x j * A i j) N] at h
    refine h.trans_eq (sum_congr rfl fun i _ => ?_)
    exact Fin.sum_univ_eq_sum_range (fun j => x i * x j * A i j) N
  have hsub : range (min l l' + 1) ⊆ range K := range_mono (by omega)
  rw [← sum_cholInf_mul hsymm hP l l', ← sum_subset hsub]
  intro j _ hj
  have hj' : min l l' + 1 ≤ j := not_lt.1 (mem_range.not.1 hj)
  rcases le_total l l' with h | h
  · rw [min_eq_left h] at hj'; rw [cholInf_of_gt A (by omega : l < j), zero_mul]
  · rw [min_eq_right h] at hj'; rw [cholInf_of_gt A (by omega : l' < j), mul_zero]

/-- A row of `cholInf A` is supported on `k ≤ l`, so the finite sum `∑_{k ≤ m} L m k c k` is the
dot product of the first `N` coordinates of `L m` and `c`, for any `N > m`. -/
theorem sum_cholInf_mul_eq_dotProduct (A : ℕ → ℕ → ℝ) {m N : ℕ} (hm : m < N) (c : ℕ → ℝ) :
    ∑ k ∈ range (m + 1), cholInf A m k * c k =
      (fun j : Fin N => cholInf A m j) ⬝ᵥ (fun j : Fin N => c j) := by
  simp only [dotProduct]
  rw [Fin.sum_univ_eq_sum_range (fun j => cholInf A m j * c j) N]
  refine sum_subset (range_mono (by omega)) fun k _ hk => ?_
  rw [cholInf_of_gt A (by simpa using hk), zero_mul]

/-- **Realization of a positive semidefinite array as a Gram matrix.**  The rows of the Cholesky
factor of `Γ`, placed along an orthonormal sequence `ε`, have Gram matrix `Γ`:
`⟪x_l, x_l'⟫ = Γ l l'` for `x_l = ∑_{k ≤ l} L_{l,k} ε_k`. -/
theorem inner_cholInf_realization {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ε : ℕ → H) (hε : Orthonormal ℝ ε) {Γ : ℕ → ℕ → ℝ}
    (hΓ : ∀ k : ℕ, (Matrix.of fun l l' : Fin k => Γ l l').PosSemidef) (l l' : ℕ) :
    ⟪∑ k ∈ range (l + 1), cholInf Γ l k • ε k,
        ∑ k ∈ range (l' + 1), cholInf Γ l' k • ε k⟫ = Γ l l' := by
  set K := max l l' + 1 with hK
  have hext : ∀ m : ℕ, m < K → ∑ k ∈ range (m + 1), cholInf Γ m k • ε k =
      ∑ k ∈ range K, cholInf Γ m k • ε k := fun m hm =>
    sum_subset (range_mono (by omega)) fun k _ hk => by
      rw [cholInf_of_gt Γ (by simpa using hk), zero_smul]
  rw [hext l (by omega), hext l' (by omega), ← sum_cholInf_mul_eq hΓ l l' K (by omega),
    sum_inner]
  refine sum_congr rfl fun k hk => ?_
  rw [inner_sum]
  simp only [real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.1 hε, mul_ite,
    mul_one, mul_zero, sum_ite_eq]
  simp [hk]
  ring

end Matrix
