/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.SKVectorPathFrobenius
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaCavity

/-!
# The interpolation behind the contraction (Talagrand, existence part of Theorem 1.12.2)

To move from one pair of matrices `(q, ρ)` to another `(q̂, ρ̂)` the book uses the path (1.386)
together with the Gaussian field `Y(t) = √t Y¹ + √(1-t) Y²`.  This file proves the Lipschitz
estimate for the expected replica Gibbs average of the field model: the derivative is bounded by
`2 (n+1)² β² M d ε` along the path, where `ε` bounds the Frobenius distance between the pairs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- The `R`-replica Gibbs average of `F` for the field model (1.371) with Gaussian field `y`:
`∫ F d(μ_{y})^{⊗R}`, where `μ_y` is `μ` tilted by `skVectorFieldExponent`.  The fixed-point maps of
(1.372)--(1.373) are the disorder averages of these quantities for `F = ξᵤ(σ¹) ξᵥ(σ²)` and
`F = ξᵤ(σ¹) ξᵥ(σ¹)`. -/
noncomputable def skVectorFieldAvg {d : ℕ} {R : Type*} [Fintype R] (μ : Measure α)
    (ξ : α → Fin d → ℝ) (β : ℝ) (ρ q : Fin d → Fin d → ℝ) (F : (R → α) → ℝ)
    (y : Fin d → ℝ) : ℝ :=
  ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted (skVectorFieldExponent ξ β ρ q y))

omit [MeasurableSpace α] in
/-- The energy of the interpolation path (1.386) between the field models `(ρ, q, Z¹)` and
`(ρ', q', Z²)`, in the coefficient form used by the replica derivative theorem. -/
theorem skVectorPathEnergy_eq {d : ℕ} (ξ : α → Fin d → ℝ) (β : ℝ) (ρ q ρ' q' : Fin d → Fin d → ℝ)
    (z : Fin d ⊕ Fin d → ℝ) (r : ℝ) (a : α) :
    0 + ∑ k : Fin d ⊕ Fin d, Sum.elim (fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k *
        z k * ξ a (Sum.elim id id k) +
      ∑ j : Fin d × Fin d, (β ^ 2 / 2 * ((r * ρ j.1 j.2 + (1 - r) * ρ' j.1 j.2) -
        (r * q j.1 j.2 + (1 - r) * q' j.1 j.2))) * (ξ a j.1 * ξ a j.2) =
      Real.sqrt r * ∑ x, z (Sum.inl x) * ξ a x + Real.sqrt (1 - r) * ∑ x, z (Sum.inr x) * ξ a x +
        β ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * ((r * ρ u v + (1 - r) * ρ' u v) -
          (r * q u v + (1 - r) * q' u v)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq, zero_add, Finset.mul_sum]
  congr 1
  · congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [MeasurableSpace α] in
/-- The path energy is the field exponent (1.371) of the interpolated parameters. -/
theorem skVectorPathEnergy_eq_fieldExponent {d : ℕ} (ξ : α → Fin d → ℝ) (β : ℝ)
    (ρ q ρ' q' : Fin d → Fin d → ℝ) (z : Fin d ⊕ Fin d → ℝ) (r : ℝ) (a : α) :
    0 + ∑ k : Fin d ⊕ Fin d, Sum.elim (fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k *
        z k * ξ a (Sum.elim id id k) +
      ∑ j : Fin d × Fin d, (β ^ 2 / 2 * ((r * ρ j.1 j.2 + (1 - r) * ρ' j.1 j.2) -
        (r * q j.1 j.2 + (1 - r) * q' j.1 j.2))) * (ξ a j.1 * ξ a j.2) =
      skVectorFieldExponent ξ β (fun u v => r * ρ u v + (1 - r) * ρ' u v)
        (fun u v => r * q u v + (1 - r) * q' u v)
        (fun x => Real.sqrt r * z (Sum.inl x) + Real.sqrt (1 - r) * z (Sum.inr x)) a := by
  rw [skVectorPathEnergy_eq]
  unfold skVectorFieldExponent
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

omit [MeasurableSpace α] in
/-- At `r = 1` the path energy is the field exponent of `(ρ, q, Z¹)`. -/
theorem skVectorPathEnergy_one {d : ℕ} (ξ : α → Fin d → ℝ) (β : ℝ)
    (ρ q ρ' q' : Fin d → Fin d → ℝ) (z : Fin d ⊕ Fin d → ℝ) (a : α) :
    0 + ∑ k : Fin d ⊕ Fin d, Sum.elim (fun _ => Real.sqrt 1) (fun _ => Real.sqrt (1 - 1)) k *
        z k * ξ a (Sum.elim id id k) +
      ∑ j : Fin d × Fin d, (β ^ 2 / 2 * ((1 * ρ j.1 j.2 + (1 - 1) * ρ' j.1 j.2) -
        (1 * q j.1 j.2 + (1 - 1) * q' j.1 j.2))) * (ξ a j.1 * ξ a j.2) =
      skVectorFieldExponent ξ β ρ q (fun x => z (Sum.inl x)) a := by
  rw [skVectorPathEnergy_eq]
  simp [skVectorFieldExponent]

omit [MeasurableSpace α] in
/-- At `r = 0` the path energy is the field exponent of `(ρ', q', Z²)`. -/
theorem skVectorPathEnergy_zero {d : ℕ} (ξ : α → Fin d → ℝ) (β : ℝ)
    (ρ q ρ' q' : Fin d → Fin d → ℝ) (z : Fin d ⊕ Fin d → ℝ) (a : α) :
    0 + ∑ k : Fin d ⊕ Fin d, Sum.elim (fun _ => Real.sqrt 0) (fun _ => Real.sqrt (1 - 0)) k *
        z k * ξ a (Sum.elim id id k) +
      ∑ j : Fin d × Fin d, (β ^ 2 / 2 * ((0 * ρ j.1 j.2 + (1 - 0) * ρ' j.1 j.2) -
        (0 * q j.1 j.2 + (1 - 0) * q' j.1 j.2))) * (ξ a j.1 * ξ a j.2) =
      skVectorFieldExponent ξ β ρ' q' (fun x => z (Sum.inr x)) a := by
  rw [skVectorPathEnergy_eq]
  simp [skVectorFieldExponent]

/-- **The derivative along the path (1.386)** (first step of the contraction): at every interior
time the expected replica Gibbs average has a derivative of absolute value at most
`2 (n+1)² β² M d ε`, where `ε` bounds the Frobenius distance of the two pairs of matrices. -/
theorem skVectorField_path_hasDerivAt {d : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q ρ' q' : Fin d → Fin d → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hρε : ∑ u, ∑ v, (ρ u v - ρ' u v) ^ 2 ≤ ε ^ 2)
    (hqε : ∑ u, ∑ v, (q u v - q' u v) ^ 2 ≤ ε ^ 2)
    (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M)
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Fin d ⊕ Fin d → Ω → ℝ}
    (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hZm : ∀ k, Measurable (Z k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0)
    (hcov1 : ∀ x y, ∫ ω, Z (Sum.inl x) ω * Z (Sum.inl y) ω ∂P = β ^ 2 * q x y)
    (hcov2 : ∀ x y, ∫ ω, Z (Sum.inr x) ω * Z (Sum.inr y) ω ∂P = β ^ 2 * q' x y)
    (hcov12 : ∀ x y, ∫ ω, Z (Sum.inl x) ω * Z (Sum.inr y) ω ∂P = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ V : ℝ, HasDerivAt (fun r => ∫ ω, ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted
      fun a => 0 + ∑ k : Fin d ⊕ Fin d,
        Sum.elim (fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k * Z k ω *
          ξ a (Sum.elim id id k) +
        ∑ j : Fin d × Fin d, (β ^ 2 / 2 * ((r * ρ j.1 j.2 + (1 - r) * ρ' j.1 j.2) -
          (r * q j.1 j.2 + (1 - r) * q' j.1 j.2))) * (ξ a j.1 * ξ a j.2)) ∂P) V t ∧
      |V| ≤ 2 * ((Fintype.card R : ℝ) + 1) ^ 2 * β ^ 2 * M * (d : ℝ) * ε := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxs : ∀ a u v, |ξ a u * ξ a v| ≤ d := fun a u v =>
    abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound a a u v
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set m : ℝ := min t (1 - t) / 2 with hm
  have hm0 : 0 < m := by
    have : 0 < min t (1 - t) := lt_min ht0 (by linarith)
    positivity
  have hmt : m ≤ t / 2 := by
    have := min_le_left t (1 - t); rw [hm]; linarith
  have hm1 : m ≤ (1 - t) / 2 := by
    have := min_le_right t (1 - t); rw [hm]; linarith
  have hball : ∀ r ∈ Metric.ball t m, m ≤ r ∧ m ≤ 1 - r := fun r hr' => by
    rw [Metric.mem_ball, Real.dist_eq] at hr'
    have := (abs_lt.1 hr')
    constructor <;> linarith [this.1, this.2]
  have hsd' : ∀ k : Fin d ⊕ Fin d, ∀ r ∈ Metric.ball t m, HasDerivAt
      (fun r => Sum.elim (fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k)
      (Sum.elim (fun _ => 1 / (2 * Real.sqrt r))
        (fun _ => -(1 / (2 * Real.sqrt (1 - r)))) k) r := by
    intro k r hr'
    obtain ⟨h1, h2⟩ := hball r hr'
    rcases k with x | x
    · exact Real.hasDerivAt_sqrt (by linarith)
    · exact ((Real.hasDerivAt_sqrt (x := 1 - r) (by linarith)).comp r
        ((hasDerivAt_id r).const_sub 1)).congr_deriv (by simp)
  have hcd' : ∀ j : Fin d × Fin d, ∀ r ∈ Metric.ball t m, HasDerivAt
      (fun r => β ^ 2 / 2 * ((r * ρ j.1 j.2 + (1 - r) * ρ' j.1 j.2) -
        (r * q j.1 j.2 + (1 - r) * q' j.1 j.2)))
      (β ^ 2 / 2 * ((ρ j.1 j.2 - ρ' j.1 j.2) - (q j.1 j.2 - q' j.1 j.2))) r := by
    intro j r _
    have h1 := (((hasDerivAt_id r).mul_const (ρ j.1 j.2)).add
      (((hasDerivAt_id r).const_sub 1).mul_const (ρ' j.1 j.2))).sub
      (((hasDerivAt_id r).mul_const (q j.1 j.2)).add
      (((hasDerivAt_id r).const_sub 1).mul_const (q' j.1 j.2)))
    exact (h1.const_mul (β ^ 2 / 2)).congr_deriv (by ring)
  set C : ℝ := 1 / (2 * Real.sqrt m) +
    ∑ j : Fin d × Fin d, |β ^ 2 / 2 * ((ρ j.1 j.2 - ρ' j.1 j.2) - (q j.1 j.2 - q' j.1 j.2))|
    with hC
  have hsC : ∀ k : Fin d ⊕ Fin d, ∀ r ∈ Metric.ball t m,
      |Sum.elim (fun _ => 1 / (2 * Real.sqrt r))
        (fun _ => -(1 / (2 * Real.sqrt (1 - r)))) k| ≤ C := by
    intro k r hr'
    obtain ⟨h1, h2⟩ := hball r hr'
    have hsum : 0 ≤ ∑ j : Fin d × Fin d,
        |β ^ 2 / 2 * ((ρ j.1 j.2 - ρ' j.1 j.2) - (q j.1 j.2 - q' j.1 j.2))| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hs0 : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
    rcases k with x | x
    · simp only [Sum.elim_inl]
      rw [abs_of_nonneg (by positivity)]
      have : 1 / (2 * Real.sqrt r) ≤ 1 / (2 * Real.sqrt m) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (by norm_num))
      linarith
    · simp only [Sum.elim_inr]
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have : 1 / (2 * Real.sqrt (1 - r)) ≤ 1 / (2 * Real.sqrt m) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (by norm_num))
      linarith
  have hcC : ∀ j : Fin d × Fin d, ∀ r ∈ Metric.ball t m,
      |β ^ 2 / 2 * ((ρ j.1 j.2 - ρ' j.1 j.2) - (q j.1 j.2 - q' j.1 j.2))| ≤ C := by
    intro j r _
    have hs0 : 0 ≤ 1 / (2 * Real.sqrt m) := by positivity
    have := Finset.single_le_sum (f := fun j : Fin d × Fin d =>
      |β ^ 2 / 2 * ((ρ j.1 j.2 - ρ' j.1 j.2) - (q j.1 j.2 - q' j.1 j.2))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  have hd := hasDerivAt_integral_gibbs_replica_cavity_path (μ := μ) (R := R) (P := P)
    (D := fun _ => (0 : ℝ)) (X := fun (k : Fin d ⊕ Fin d) a => ξ a (Sum.elim id id k))
    (Xs := fun (j : Fin d × Fin d) a => ξ a j.1 * ξ a j.2) (F := F) (Eb := 0)
    (B := Real.sqrt d + d) (M := M) measurable_const
    (fun k => by rcases k with x | x <;> exact hξ x) (fun j => (hξ j.1).mul (hξ j.2)) hF
    (by positivity) hM (fun _ => by simp)
    (fun k a => by
      rcases k with x | x <;> exact (hxb a x).trans (by linarith))
    (fun j a => (hxs a j.1 j.2).trans (by linarith)) hFb hZ hZm hmean
    (s := fun k r => Sum.elim (fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k)
    (c := fun j r => β ^ 2 / 2 * ((r * ρ j.1 j.2 + (1 - r) * ρ' j.1 j.2) -
        (r * q j.1 j.2 + (1 - r) * q' j.1 j.2)))
    (s' := fun k r => Sum.elim (fun _ => 1 / (2 * Real.sqrt r))
      (fun _ => -(1 / (2 * Real.sqrt (1 - r)))) k)
    (c' := fun j _ => β ^ 2 / 2 * ((ρ j.1 j.2 - ρ' j.1 j.2) - (q j.1 j.2 - q' j.1 j.2)))
    (t := t) (δ := m) (C := C) hm0 hsd' hcd' hsC hcC (fun k => Or.inr (by
      rcases k with x | x
      · exact (Real.sqrt_pos.2 ht0).ne'
      · exact (Real.sqrt_pos.2 (by linarith)).ne'))
  refine ⟨_, hd, ?_⟩
  have hsq0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
  have hsq1 : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  obtain ⟨en, hen⟩ : ∃ en : Ω → α → ℝ, ∀ ω, en ω = fun a => 0 + ∑ k' : Fin d ⊕ Fin d,
      Sum.elim (fun _ => Real.sqrt t) (fun _ => Real.sqrt (1 - t)) k' * Z k' ω *
        ξ a (Sum.elim id id k') +
      ∑ j' : Fin d × Fin d, (β ^ 2 / 2 * ((t * ρ j'.1 j'.2 + (1 - t) * ρ' j'.1 j'.2) -
        (t * q j'.1 j'.2 + (1 - t) * q' j'.1 j'.2))) * (ξ a j'.1 * ξ a j'.2) := ⟨_, fun _ => rfl⟩
  simp only [← hen]
  obtain ⟨E1, hE1⟩ : ∃ E1 : Fin d ⊕ Fin d → Fin d ⊕ Fin d → ℝ, ∀ k l, E1 k l =
      ∫ ω, ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
        (∑ a, ξ (σ (some (some a))) (Sum.elim id id k) -
          (Fintype.card R : ℝ) * ξ (σ (some none)) (Sum.elim id id k)) *
        (∑ o, ξ (σ (some o)) (Sum.elim id id l) -
          ((Fintype.card R : ℝ) + 1) * ξ (σ none) (Sum.elim id id l))
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P := ⟨_, fun _ _ => rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : Fin d × Fin d → ℝ, ∀ j, E2 j =
      ∫ ω, ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
        (∑ o, ξ (σ (some o)) j.1 * ξ (σ (some o)) j.2 -
          ((Fintype.card R : ℝ) + 1) * (ξ (σ none) j.1 * ξ (σ none) j.2))
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P := ⟨_, fun _ => rfl⟩
  simp only [← hE1, ← hE2]
  -- probability of the Gibbs measures
  have hen' : ∀ ω, en ω = skVectorFieldExponent ξ β (fun u v => t * ρ u v + (1 - t) * ρ' u v)
      (fun u v => t * q u v + (1 - t) * q' u v)
      (fun x => Real.sqrt t * Z (Sum.inl x) ω + Real.sqrt (1 - t) * Z (Sum.inr x) ω) := fun ω =>
    funext fun a => by rw [hen]; exact skVectorPathEnergy_eq_fieldExponent ξ β ρ q ρ' q' _ t a
  have hprob : ∀ ω, IsProbabilityMeasure (μ.tilted (en ω)) := fun ω => by
    rw [hen']
    exact isProbabilityMeasure_tilted (skVectorFieldExponent_integrable μ ξ hξ hr hbound β _ _ _)
  set n : ℝ := (Fintype.card R : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hE : Measurable fun p : Ω × α => en p.1 p.2 := by
    have : (fun p : Ω × α => en p.1 p.2) = fun p => 0 + ∑ k' : Fin d ⊕ Fin d,
        Sum.elim (fun _ => Real.sqrt t) (fun _ => Real.sqrt (1 - t)) k' * Z k' p.1 *
          ξ p.2 (Sum.elim id id k') +
        ∑ j' : Fin d × Fin d, (β ^ 2 / 2 * ((t * ρ j'.1 j'.2 + (1 - t) * ρ' j'.1 j'.2) -
          (t * q j'.1 j'.2 + (1 - t) * q' j'.1 j'.2))) * (ξ p.2 j'.1 * ξ p.2 j'.2) := by
      funext p; rw [hen]
    rw [this]
    refine (measurable_const.add (Finset.measurable_sum _ fun k' _ => ?_)).add
      (Finset.measurable_sum _ fun j' _ => measurable_const.mul
        (((hξ j'.1).comp measurable_snd).mul ((hξ j'.2).comp measurable_snd)))
    refine (measurable_const.mul ((hZm k').comp measurable_fst)).mul ?_
    rcases k' with x | x <;> exact (hξ x).comp measurable_snd
  have hsame : ∀ x y, E1 (Sum.inr x) (Sum.inr y) = E1 (Sum.inl x) (Sum.inl y) := by
    intro x y
    rw [hE1, hE1]
    rfl
  have hcl : ∀ k l : Fin d ⊕ Fin d, ∫ ω, Z k ω * Z l ω ∂P =
      Sum.elim (fun x => Sum.elim (fun y => β ^ 2 * q x y) (fun _ => 0) l)
        (fun x => Sum.elim (fun _ => 0) (fun y => β ^ 2 * q' x y) l) k := by
    intro k l
    rcases k with x | x <;> rcases l with y | y
    · exact hcov1 x y
    · exact hcov12 x y
    · simp only [Sum.elim_inr, Sum.elim_inl]
      rw [← hcov12 y x]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    · exact hcov2 x y
  have e1 : 1 / (2 * Real.sqrt t) * Real.sqrt t = 1 / 2 := by field_simp
  have e2 : -(1 / (2 * Real.sqrt (1 - t))) * Real.sqrt (1 - t) = -(1 / 2) := by field_simp
  have hV1 : ∑ k : Fin d ⊕ Fin d, ∑ l : Fin d ⊕ Fin d,
      (Sum.elim (fun _ => 1 / (2 * Real.sqrt t)) (fun _ => -(1 / (2 * Real.sqrt (1 - t)))) k *
        Sum.elim (fun _ => Real.sqrt t) (fun _ => Real.sqrt (1 - t)) l *
          ∫ ω, Z k ω * Z l ω ∂P) * E1 k l =
      β ^ 2 / 2 * ∑ u, ∑ v, (q u v - q' u v) * E1 (Sum.inl u) (Sum.inl v) := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hcl, hsame, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add]
    simp only [mul_assoc, e1, e2]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hV1]
  have hsq2 : ∑ u, ∑ v, (ρ u v - ρ' u v - (q u v - q' u v)) ^ 2 ≤ (2 * ε) ^ 2 := by
    calc _ ≤ ∑ u, ∑ v, (2 * (ρ u v - ρ' u v) ^ 2 + 2 * (q u v - q' u v) ^ 2) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
            nlinarith [sq_nonneg (ρ u v - ρ' u v + (q u v - q' u v))]
      _ = 2 * ∑ u, ∑ v, (ρ u v - ρ' u v) ^ 2 + 2 * ∑ u, ∑ v, (q u v - q' u v) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (2 * ε) ^ 2 := by nlinarith
  have hA : |β ^ 2 / 2 * ∑ u, ∑ v, (q u v - q' u v) * E1 (Sum.inl u) (Sum.inl v)| ≤
      β ^ 2 / 2 * (M * (4 * n * (n + 1) * d * ε)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_sum_integral_pair_le (μ := μ) (en := en) (P := P) ξ hξ hbound hE hprob F hF hM hFb
      (fun u v => q u v - q' u v) hε hqε
    simpa only [hE1, Sum.elim_inl, id_eq] using this
  have hB : |∑ j : Fin d × Fin d, β ^ 2 / 2 *
      (ρ j.1 j.2 - ρ' j.1 j.2 - (q j.1 j.2 - q' j.1 j.2)) * E2 j| ≤
      β ^ 2 / 2 * (M * (2 * (n + 1) * (d * (2 * ε)))) := by
    have h1 := abs_sum_integral_single_le (μ := μ) (en := en) (P := P) ξ hξ hbound hE hprob F hF
      hM hFb (fun u v => ρ u v - ρ' u v - (q u v - q' u v)) (by positivity) hsq2
    have h2 : ∑ j : Fin d × Fin d, β ^ 2 / 2 *
        (ρ j.1 j.2 - ρ' j.1 j.2 - (q j.1 j.2 - q' j.1 j.2)) * E2 j =
        β ^ 2 / 2 * ∑ j : Fin d × Fin d,
          (ρ j.1 j.2 - ρ' j.1 j.2 - (q j.1 j.2 - q' j.1 j.2)) * E2 j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    simpa only [hE2] using h1
  refine (abs_add_le _ _).trans ((add_le_add hA hB).trans (le_of_eq ?_))
  ring

/-- **The Lipschitz estimate along the path (1.386).**  The expected `R`-replica Gibbs averages of
the field models `(ρ, q)` and `(ρ', q')` (driven by the Gaussian fields `Z¹`, `Z²` of covariances
`β² q`, `β² q'`) differ by at most `2 (n+1)² β² M d ε` when the matrices differ by at most `ε` in
Frobenius norm. -/
theorem skVectorField_path_lipschitz {d : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q ρ' q' : Fin d → Fin d → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hρε : ∑ u, ∑ v, (ρ u v - ρ' u v) ^ 2 ≤ ε ^ 2)
    (hqε : ∑ u, ∑ v, (q u v - q' u v) ^ 2 ≤ ε ^ 2)
    (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M)
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Fin d ⊕ Fin d → Ω → ℝ}
    (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hZm : ∀ k, Measurable (Z k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0)
    (hcov1 : ∀ x y, ∫ ω, Z (Sum.inl x) ω * Z (Sum.inl y) ω ∂P = β ^ 2 * q x y)
    (hcov2 : ∀ x y, ∫ ω, Z (Sum.inr x) ω * Z (Sum.inr y) ω ∂P = β ^ 2 * q' x y)
    (hcov12 : ∀ x y, ∫ ω, Z (Sum.inl x) ω * Z (Sum.inr y) ω ∂P = 0) :
    |(∫ ω, skVectorFieldAvg μ ξ β ρ q F (fun x => Z (Sum.inl x) ω) ∂P) -
      ∫ ω, skVectorFieldAvg μ ξ β ρ' q' F (fun x => Z (Sum.inr x) ω) ∂P| ≤
      2 * ((Fintype.card R : ℝ) + 1) ^ 2 * β ^ 2 * M * (d : ℝ) * ε := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxs : ∀ a u v, |ξ a u * ξ a v| ≤ d := fun a u v =>
    abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound a a u v
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set φ : ℝ → ℝ := fun r => ∫ ω, ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted
      fun a => 0 + ∑ k : Fin d ⊕ Fin d,
        Sum.elim (fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k * Z k ω *
          ξ a (Sum.elim id id k) +
        ∑ j : Fin d × Fin d, (β ^ 2 / 2 * ((r * ρ j.1 j.2 + (1 - r) * ρ' j.1 j.2) -
          (r * q j.1 j.2 + (1 - r) * q' j.1 j.2))) * (ξ a j.1 * ξ a j.2)) ∂P with hφ
  have hcont : Continuous φ := by
    refine continuous_integral_gibbs_replica_path (μ := μ) (R := R) (P := P)
      (D := fun _ => (0 : ℝ)) (X := fun (k : Fin d ⊕ Fin d) a => ξ a (Sum.elim id id k))
      (Xs := fun (j : Fin d × Fin d) a => ξ a j.1 * ξ a j.2) (F := F) (Eb := 0)
      (B := Real.sqrt d + d) (M := M) measurable_const
      (fun k => by rcases k with x | x <;> exact hξ x) (fun j => (hξ j.1).mul (hξ j.2)) hF
      (by positivity) hM (fun _ => by simp)
      (fun k a => by
        rcases k with x | x <;> exact (hxb a x).trans (by linarith))
      (fun j a => (hxs a j.1 j.2).trans (by linarith)) hFb hZm
      (s := fun k r => Sum.elim (fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k)
      (c := fun j r => β ^ 2 / 2 * ((r * ρ j.1 j.2 + (1 - r) * ρ' j.1 j.2) -
        (r * q j.1 j.2 + (1 - r) * q' j.1 j.2))) ?_ ?_
    · intro k
      rcases k with x | x
      · exact Real.continuous_sqrt
      · exact Real.continuous_sqrt.comp (continuous_const.sub continuous_id)
    · intro j
      fun_prop
  have hder : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ V, HasDerivAt φ V t ∧
      |V| ≤ 2 * ((Fintype.card R : ℝ) + 1) ^ 2 * β ^ 2 * M * (d : ℝ) * ε := fun t ht =>
    skVectorField_path_hasDerivAt μ ξ hξ hbound β ρ q ρ' q' hε hρε hqε F hF hM hFb hZ hZm hmean
      hcov1 hcov2 hcov12 ht.1 ht.2
  have hdiff : DifferentiableOn ℝ φ (Set.Ioo 0 1) := fun t ht =>
    (hder t ht).choose_spec.1.differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope φ zero_lt_one hcont.continuousOn hdiff
  obtain ⟨V, hV, hVb⟩ := hder c hc
  have h1 : φ 1 - φ 0 = V := by
    rw [hV.deriv] at hcd
    rw [hcd]; ring
  have e1 : φ 1 = ∫ ω, skVectorFieldAvg μ ξ β ρ q F (fun x => Z (Sum.inl x) ω) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    unfold skVectorFieldAvg
    simp only [skVectorPathEnergy_one]
  have e0 : φ 0 = ∫ ω, skVectorFieldAvg μ ξ β ρ' q' F (fun x => Z (Sum.inr x) ω) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    unfold skVectorFieldAvg
    simp only [skVectorPathEnergy_zero]
  rw [← e1, ← e0, h1]
  exact hVb

end SpinGlasses
