/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Derivative
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Geometry

/-!
# Bounds for the cavity derivative (Talagrand Corollary 1.12.5)

The pointwise estimate behind (1.378) and (1.379): the contraction of the error matrix against two
spin vectors of squared length at most `d` costs the factor `d`, and the error matrix
`R⁻ - q(ℓ, ℓ')` has squared Frobenius norm at most `4 d²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*}

/-- The squared Frobenius norm of the overlap error `R⁻ - Q` is at most `4 d²` when `‖Q‖_F ≤ d`
(the two estimates of Eq. (1.382)). -/
theorem sum_sq_overlap_error_le {d N : ℕ} (ξ : α → Fin d → ℝ)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (Q : Fin d → Fin d → ℝ)
    (hQ : ∑ u, ∑ v, Q u v ^ 2 ≤ (d : ℝ) ^ 2) (x y : Fin (N + 1) → α) :
    ∑ u, ∑ v, (skVectorCavityOverlap ξ N x y u v - Q u v) ^ 2 ≤ 4 * (d : ℝ) ^ 2 := by
  have hR : ∑ u, ∑ v, skVectorCavityOverlap ξ N x y u v ^ 2 ≤ (d : ℝ) ^ 2 := by
    have := sum_sq_sk_vector_trunc_overlap_le N d (fun i u => ξ (x i.castSucc) u)
      (fun i u => ξ (y i.castSucc) u) (fun i => hbound _) (fun i => hbound _)
    simpa only [skVectorCavityOverlap] using this
  calc ∑ u, ∑ v, (skVectorCavityOverlap ξ N x y u v - Q u v) ^ 2
      ≤ ∑ u, ∑ v, (2 * skVectorCavityOverlap ξ N x y u v ^ 2 + 2 * Q u v ^ 2) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
          nlinarith [sq_nonneg (skVectorCavityOverlap ξ N x y u v + Q u v)]
    _ = 2 * ∑ u, ∑ v, skVectorCavityOverlap ξ N x y u v ^ 2 + 2 * ∑ u, ∑ v, Q u v ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 * (d : ℝ) ^ 2 := by linarith

/-- **The pointwise estimate of Corollary 1.12.5.** For spins `ε`, `ε'` with squared length at most
`d`, the contraction of the cavity overlap error `R⁻ - Q` against `ε ⊗ ε'` is at most
`d · ‖R⁻ - Q‖_F`. -/
theorem abs_sum_spin_overlap_error_le_sqrt {d N : ℕ} (ξ : α → Fin d → ℝ)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (Q : Fin d → Fin d → ℝ) (x y : Fin (N + 1) → α) :
    |∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
        (skVectorCavityOverlap ξ N x y u v - Q u v)| ≤
      d * Real.sqrt (∑ u, ∑ v, (skVectorCavityOverlap ξ N x y u v - Q u v) ^ 2) := by
  have hc := sq_vector_overlap_contraction_le (fun u => ξ (x (Fin.last N)) u)
    (fun v => ξ (y (Fin.last N)) v)
    (Matrix.of fun u v => skVectorCavityOverlap ξ N x y u v - Q u v) d d (hbound _) (hbound _)
  simp only [Matrix.of_apply] at hc
  have hS : 0 ≤ ∑ u, ∑ v, (skVectorCavityOverlap ξ N x y u v - Q u v) ^ 2 :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [← Real.sqrt_sq hd, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.abs_le_sqrt ?_
  calc _ ≤ (d : ℝ) * d * ∑ u, ∑ v, (skVectorCavityOverlap ξ N x y u v - Q u v) ^ 2 := hc
    _ = _ := by ring

/-- **The pointwise estimate of Corollary 1.12.5 (1.379).** The contraction of the cavity overlap
error is at most `2 d²` when `‖Q‖_F ≤ d`. -/
theorem abs_sum_spin_overlap_error_le {d N : ℕ} (ξ : α → Fin d → ℝ)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (Q : Fin d → Fin d → ℝ)
    (hQ : ∑ u, ∑ v, Q u v ^ 2 ≤ (d : ℝ) ^ 2) (x y : Fin (N + 1) → α) :
    |∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
        (skVectorCavityOverlap ξ N x y u v - Q u v)| ≤ 2 * (d : ℝ) ^ 2 := by
  refine (abs_sum_spin_overlap_error_le_sqrt ξ hbound Q x y).trans ?_
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc (d : ℝ) * Real.sqrt (∑ u, ∑ v, (skVectorCavityOverlap ξ N x y u v - Q u v) ^ 2)
      ≤ d * Real.sqrt (4 * (d : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sum_sq_overlap_error_le ξ hbound Q hQ x y)) hd
    _ = 2 * (d : ℝ) ^ 2 := by
        rw [show 4 * (d : ℝ) ^ 2 = (2 * d) ^ 2 by ring, Real.sqrt_sq (by positivity)]
        ring

section Avg

variable {D : Type*} [Fintype D] [MeasurableSpace α] {Ω R : Type*} [MeasurableSpace Ω]
  [Fintype R] (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → D → ℝ)
  (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
  (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
  {P : Measure Ω} [IsProbabilityMeasure P]
  {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : D → Ω → ℝ}
  (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
  (t : ℝ)
include hξ hr hbound hgm hg'm hYm

/-- The Gibbs expectation `ν_t` of a finite sum of bounded measurable functions is the sum of the
expectations. -/
theorem skVectorCavityAverage_sum {ι : Type*} [Fintype ι]
    (G : ι → (Option (Option R) → Fin (N + 1) → α) → ℝ) (hG : ∀ i, Measurable (G i))
    (hGb : ∀ i, ∃ B, ∀ σ, |G i σ| ≤ B) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => ∑ i, G i σ) =
      ∑ i, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (G i) := by
  have hint := fun i => integrable_integral_skVectorCavityAverage (R := R) (P := P) μ ξ hξ hr
    hbound N β ρ q
    hgm hg'm
    hYm t (G i) (hG i) (hGb i)
  unfold skVectorCavityAverage
  rw [← integral_finsetSum _ fun i _ => hint i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have := isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q
    (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t
  refine integral_finsetSum _ fun i _ => ?_
  obtain ⟨B, hB⟩ := hGb i
  exact integrable_of_measurable_bound (m := Measure.pi fun _ : Option (Option R) =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
      (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t)) (hG i) hB

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] hξ hr hbound hgm hg'm hYm in
/-- Scaling the observable scales the expectation. -/
theorem skVectorCavityAverage_const_mul (c : ℝ)
    (G : (Option (Option R) → Fin (N + 1) → α) → ℝ) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => c * G σ) =
      c * skVectorCavityAverage μ ξ N β ρ q P g g' Y t G := by
  unfold skVectorCavityAverage
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => integral_const_mul _ _)

/-- **Monotonicity of `ν_t`**: if `|G| ≤ H` pointwise and `H` is bounded and measurable then
`|ν_t(G)| ≤ ν_t(H)`. -/
theorem abs_skVectorCavityAverage_le
    (G H : (Option (Option R) → Fin (N + 1) → α) → ℝ) (hH : Measurable H)
    (hHb : ∃ B, ∀ σ, |H σ| ≤ B) (hGH : ∀ σ, |G σ| ≤ H σ) :
    |skVectorCavityAverage μ ξ N β ρ q P g g' Y t G| ≤ skVectorCavityAverage μ ξ N β ρ q P g g' Y
      t H := by
  have hint := integrable_integral_skVectorCavityAverage (R := R) (P := P) μ ξ hξ hr hbound N β ρ
    q hgm hg'm
    hYm t H hH hHb
  unfold skVectorCavityAverage
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun ω => ?_)
  have := isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q
    (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t
  obtain ⟨B, hB⟩ := hHb
  exact norm_integral_le_of_norm_le (integrable_of_measurable_bound (m := Measure.pi
    fun _ : Option (Option R) => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t))
    hH hB)
    (Filter.Eventually.of_forall fun σ => by simpa [Real.norm_eq_abs] using hGH σ)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] hξ hr hbound hgm hg'm hYm in
/-- `ν_t` is a positive functional. -/
theorem skVectorCavityAverage_nonneg (G : (Option (Option R) → Fin (N + 1) → α) → ℝ)
    (hG : ∀ σ, 0 ≤ G σ) : 0 ≤ skVectorCavityAverage μ ξ N β ρ q P g g' Y t G :=
  integral_nonneg fun _ => integral_nonneg fun σ => hG σ

/-- **Cauchy--Schwarz for `ν_t`**: `|ν_t(G H)| ≤ ν_t(G²)^{1/2} ν_t(H²)^{1/2}` for bounded measurable
`G`, `H`. -/
theorem abs_skVectorCavityAverage_mul_le
    (G H : (Option (Option R) → Fin (N + 1) → α) → ℝ) (hG : Measurable G) (hH : Measurable H)
    (hGb : ∃ B, ∀ σ, |G σ| ≤ B) (hHb : ∃ B, ∀ σ, |H σ| ≤ B) :
    |skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => G σ * H σ)| ≤
      Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => G σ ^ 2)) *
        Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => H σ ^ 2)) := by
  set A := skVectorCavityAverage (R := R) μ ξ N β ρ q P g g' Y t with hAdef
  simp only [sq]
  have hexp : ∀ s : ℝ, A (fun σ => (G σ + s * H σ) * (G σ + s * H σ)) =
      A (fun σ => G σ * G σ) + 2 * s * A (fun σ => G σ * H σ) +
        s ^ 2 * A (fun σ => H σ * H σ) := by
    intro s
    have hGG := exists_abs_le_mul hGb hGb
    have hGH := exists_abs_le_mul hGb hHb
    have hHH := exists_abs_le_mul hHb hHb
    have h3 := skVectorCavityAverage_sum (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ hξ hr
      hbound N β ρ q hgm hg'm hYm t (ι := Fin 3)
      (fun i σ => ![G σ * G σ, 2 * s * (G σ * H σ), s ^ 2 * (H σ * H σ)] i)
      (by
        intro i; fin_cases i
        · exact hG.mul hG
        · exact measurable_const.mul (hG.mul hH)
        · exact measurable_const.mul (hH.mul hH))
      (by
        intro i; fin_cases i
        · exact hGG
        · exact exists_abs_le_mul (exists_abs_le_const _) hGH
        · exact exists_abs_le_mul (exists_abs_le_const _) hHH)
    simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h3
    have e : (fun σ => (G σ + s * H σ) * (G σ + s * H σ)) = fun σ => G σ * G σ +
        2 * s * (G σ * H σ) + s ^ 2 * (H σ * H σ) := funext fun σ => by ring
    rw [e, hAdef, h3]
    rw [skVectorCavityAverage_const_mul (R := R) μ ξ N β ρ q t, skVectorCavityAverage_const_mul]
  have hnn : ∀ s : ℝ, 0 ≤ A (fun σ => G σ * G σ) + 2 * s * A (fun σ => G σ * H σ) +
      s ^ 2 * A (fun σ => H σ * H σ) := fun s => by
    rw [← hexp s]
    exact skVectorCavityAverage_nonneg (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ N β ρ q
      t _
      fun σ => mul_self_nonneg _
  have hdis := discrim_le_zero (a := A (fun σ => H σ * H σ)) (b := 2 * A (fun σ => G σ * H σ))
    (c := A (fun σ => G σ * G σ)) fun s => by nlinarith [hnn s]
  have hG2 := skVectorCavityAverage_nonneg (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ N β
    ρ q
    t (fun σ => G σ * G σ)
    fun σ => mul_self_nonneg _
  have hH2 := skVectorCavityAverage_nonneg (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ N β
    ρ q
    t (fun σ => H σ * H σ)
    fun σ => mul_self_nonneg _
  rw [← Real.sqrt_mul hG2]
  refine Real.abs_le_sqrt ?_
  unfold discrim at hdis
  nlinarith [hdis]

omit [IsProbabilityMeasure P] hgm hg'm hYm in
/-- **Replica exchangeability of `ν_t`**: a function of two distinct replicas has the same
expectation for any two distinct replicas. -/
theorem skVectorCavityAverage_pair_eq {x y x' y' : Option (Option R)} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (φ : (Fin (N + 1) → α) → (Fin (N + 1) → α) → ℝ)
    (hφ : Measurable fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) => φ p.1 p.2) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => φ (σ x) (σ y)) =
      skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => φ (σ x') (σ y')) := by
  unfold skVectorCavityAverage
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have := isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q
    (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t
  exact integral_pi_pair_eq _ hxy hxy' φ hφ

omit [IsProbabilityMeasure P] hgm hg'm hYm in
/-- **Replica exchangeability of `ν_t` for a single replica.** -/
theorem skVectorCavityAverage_diag_eq {x x' : Option (Option R)}
    (φ : (Fin (N + 1) → α) → (Fin (N + 1) → α) → ℝ)
    (hφ : Measurable fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) => φ p.1 p.2) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => φ (σ x) (σ x)) =
      skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => φ (σ x') (σ x')) := by
  unfold skVectorCavityAverage
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have := isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q
    (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t
  exact integral_pi_diag_eq _ φ hφ

end Avg

section Book

variable {d N : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
  (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
  (ρ q : Fin d → Fin d → ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
  {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
  (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
  (t : ℝ) (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hFb : ∀ σ, |F σ| ≤ M)

omit [MeasurableSpace α] [Fintype R] in
theorem sum_skVectorCavityKernel_eq (x y : Option (Option R)) (Q : Fin d → Fin d → ℝ)
    (σ : Option (Option R) → Fin (N + 1) → α) :
    ∑ u, ∑ v, (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u *
        ξ (σ y (Fin.last N)) v * (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v) =
      (F fun c => σ (some (some c))) * ∑ u, ∑ v, ξ (σ x (Fin.last N)) u *
        ξ (σ y (Fin.last N)) v * (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v) := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

include hξ hbound hgm hg'm hYm hF hFb

/-- The sum over the component indices of the book expectations of Eq. (1.376) is the expectation
of `f` times the contraction of the overlap error against the two spins. -/
theorem skVectorCavityAverage_sum_kernel_eq (x y : Option (Option R)) (Q : Fin d → Fin d → ℝ) :
    ∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
        (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)) =
      skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
        (F fun c => σ (some (some c))) * ∑ u, ∑ v, ξ (σ x (Fin.last N)) u *
          ξ (σ y (Fin.last N)) v * (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)) := by
  have hbook := fun (u v : Fin d) =>
    skVectorCavity_replica_term_eq (R := R) hξ (Nat.cast_nonneg d) hbound hF hFb x y Q u v
  have hfun : (fun σ : Option (Option R) → Fin (N + 1) → α =>
      (F fun c => σ (some (some c))) * ∑ u, ∑ v, ξ (σ x (Fin.last N)) u *
        ξ (σ y (Fin.last N)) v * (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)) =
      fun σ => ∑ u, ∑ v, (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u *
        ξ (σ y (Fin.last N)) v * (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v) :=
    funext fun σ => (sum_skVectorCavityKernel_eq ξ F x y Q σ).symm
  rw [hfun, skVectorCavityAverage_sum (R := R) (P := P) μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q
    hgm hg'm hYm t (fun u σ => ∑ v,
      (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v))
    (fun u => Finset.measurable_sum _ fun v _ => (hbook u v).1)
    (fun u => exists_abs_le_sum _ fun v _ => (hbook u v).2)]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact (skVectorCavityAverage_sum (R := R) (P := P) μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q hgm
    hg'm hYm t (fun v σ =>
      (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v))
    (fun v => (hbook u v).1) (fun v => (hbook u v).2)).symm

/-- **One term of Eq. (1.378)**: Cauchy--Schwarz in the spins and then for `ν_t`. -/
theorem abs_skVectorCavityAverage_sum_kernel_le_sqrt (x y : Option (Option R)) (Q : Fin d → Fin d
  → ℝ)
    (hQ : ∑ u, ∑ v, Q u v ^ 2 ≤ (d : ℝ) ^ 2) :
    |∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
        (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v))| ≤
      d * Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t
          (fun σ => (F fun c => σ (some (some c))) ^ 2)) *
        Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => ∑ u, ∑ v,
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v) ^ 2)) := by
  classical
  rw [skVectorCavityAverage_sum_kernel_eq (R := R) (P := P) μ ξ hξ hbound β ρ q hgm hg'm hYm t F
    hF hFb
    x y Q]
  set S : (Option (Option R) → Fin (N + 1) → α) → ℝ := fun σ => ∑ u, ∑ v,
    (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v) ^ 2 with hS
  have hfm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      F fun c => σ (some (some c)) := hF.comp (measurable_pi_iff.2 fun c => measurable_pi_apply _)
  have hSm : Measurable S := by
    refine Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ => ?_
    refine Measurable.pow_const (Measurable.sub ?_ measurable_const) 2
    exact Measurable.comp (g := fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) =>
      skVectorCavityOverlap ξ N p.1 p.2 u v)
      (f := fun σ : Option (Option R) → Fin (N + 1) → α => (σ x, σ y))
      (measurable_skVectorCavityOverlap hξ N u v)
      ((measurable_pi_apply x).prodMk (measurable_pi_apply y))
  have hS0 : ∀ σ, 0 ≤ S σ := fun σ =>
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hSb : ∀ σ, S σ ≤ 4 * (d : ℝ) ^ 2 := fun σ =>
    sum_sq_overlap_error_le ξ hbound Q hQ (σ x) (σ y)
  have hsqm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α => Real.sqrt (S σ) :=
    Real.continuous_sqrt.measurable.comp hSm
  have hsqb : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α, |Real.sqrt (S σ)| ≤ B :=
    ⟨Real.sqrt (4 * (d : ℝ) ^ 2), fun σ => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hSb σ)⟩
  have hfa : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      |F fun c => σ (some (some c))| := continuous_abs.measurable.comp hfm
  have hfab : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |(|F fun c => σ (some (some c))|)| ≤ B :=
    ⟨M, fun σ => by simpa using hFb _⟩
  -- step 1: pointwise bound by `d |f| √S`
  have hmono := abs_skVectorCavityAverage_le (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ hξ
    (Nat.cast_nonneg d) hbound N β ρ q hgm hg'm hYm t
    (fun σ => (F fun c => σ (some (some c))) * ∑ u, ∑ v, ξ (σ x (Fin.last N)) u *
      ξ (σ y (Fin.last N)) v * (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v))
    (fun σ => d * (|F fun c => σ (some (some c))| * Real.sqrt (S σ)))
    (measurable_const.mul (hfa.mul hsqm))
    (exists_abs_le_mul (exists_abs_le_const _) (exists_abs_le_mul hfab hsqb))
    (fun σ => by
      rw [abs_mul]
      calc |F fun c => σ (some (some c))| * |∑ u, ∑ v, ξ (σ x (Fin.last N)) u *
            ξ (σ y (Fin.last N)) v * (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)|
          ≤ |F fun c => σ (some (some c))| * (d * Real.sqrt (S σ)) :=
            mul_le_mul_of_nonneg_left (abs_sum_spin_overlap_error_le_sqrt ξ hbound Q (σ x) (σ y))
              (abs_nonneg _)
        _ = _ := by ring)
  refine hmono.trans ?_
  rw [skVectorCavityAverage_const_mul (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ N β ρ q t]
  have hcs := abs_skVectorCavityAverage_mul_le (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ hξ
    (Nat.cast_nonneg d) hbound N β ρ q hgm hg'm hYm t
    (fun σ => |F fun c => σ (some (some c))|) (fun σ => Real.sqrt (S σ)) hfa hsqm hfab hsqb
  have e1 : (fun σ : Option (Option R) → Fin (N + 1) → α => |F fun c => σ (some (some c))| ^ 2) =
      fun σ => (F fun c => σ (some (some c))) ^ 2 := funext fun σ => sq_abs _
  have e2 : (fun σ : Option (Option R) → Fin (N + 1) → α => Real.sqrt (S σ) ^ 2) = S :=
    funext fun σ => Real.sq_sqrt (hS0 σ)
  rw [e1, e2] at hcs
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc (d : ℝ) * skVectorCavityAverage μ ξ N β ρ q P g g' Y t
        (fun σ => |F fun c => σ (some (some c))| * Real.sqrt (S σ))
      ≤ d * |skVectorCavityAverage μ ξ N β ρ q P g g' Y t
        (fun σ => |F fun c => σ (some (some c))| * Real.sqrt (S σ))| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hd
    _ ≤ d * (Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t
          (fun σ => (F fun c => σ (some (some c))) ^ 2)) *
        Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t S)) :=
        mul_le_mul_of_nonneg_left hcs hd
    _ = _ := by ring

end Book

/-- **Corollary 1.12.5, Eq. (1.379)**, for any number `n` of replicas.  If the matrices `q`, `ρ`
satisfy `‖q‖_F, ‖ρ‖_F ≤ d` (as the fixed point of Eqs. (1.372)--(1.373) does), the derivative of the
cavity path is bounded by `2 n (2 n + 1) β² d² ν_t(|f|)`. -/
theorem abs_deriv_skVectorCavityAverage_le {d N : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (ρ q : Fin d → Fin d → ℝ)
    (hq : ∀ u v, q u v = q v u) (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2)
    (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ σ, |F σ| ≤ M)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hG : HasGaussianLaw (fun ω (k : (FinPairs N ⊕ Fin N) ⊕ Fin d) =>
      Sum.elim (Sum.elim (fun p => g p ω) fun i => g' i ω) (fun u => Y u ω) k) P)
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (hgg : ∀ k l : FinPairs N ⊕ Fin N,
      ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k *
        Sum.elim (fun p => g p ω) (fun i => g' i ω) l ∂P = if k = l then 1 else 0)
    (hYY : ∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * q u v)
    (hgY : ∀ (k : FinPairs N ⊕ Fin N) u,
      ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k * Y u ω ∂P = 0)
    (hg0 : ∀ p, ∫ ω, g p ω ∂P = 0) (hg'0 : ∀ i, ∫ ω, g' i ω ∂P = 0)
    (hY0 : ∀ u, ∫ ω, Y u ω ∂P = 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    |deriv (fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P) t| ≤
      2 * Fintype.card R * (2 * Fintype.card R + 1) * β ^ 2 * (d : ℝ) ^ 2 *
        skVectorCavityAverage μ ξ N β ρ q P g g' Y t
          (fun σ => |F fun c => σ (some (some c))|) := by
  classical
  rw [(hasDerivAt_skVectorCavityAverage μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q hq F hF hM hFb
    hG hgm
    hg'm hYm hgg hYY hgY hg0 hg'0 hY0 ht0 ht1).deriv]
  set J := Option (Option R) with hJ
  have hfm : Measurable fun σ : J → Fin (N + 1) → α => F fun c => σ (some (some c)) :=
    hF.comp (measurable_pi_iff.2 fun c => measurable_pi_apply _)
  have hbook := fun (x y : J) (Q : Fin d → Fin d → ℝ) (u v : Fin d) =>
    skVectorCavity_replica_term_eq (R := R) hξ (Nat.cast_nonneg d) hbound hF hFb x y Q u v
  -- the key bound for one pair of replicas
  have hT : ∀ (x y : J) (Q : Fin d → Fin d → ℝ), ∑ u, ∑ v, Q u v ^ 2 ≤ (d : ℝ) ^ 2 →
      |∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
        (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v))| ≤
        2 * (d : ℝ) ^ 2 * skVectorCavityAverage μ ξ N β ρ q P g g' Y t
          (fun σ => |F fun c => σ (some (some c))|) := by
    intro x y Q hQ
    rw [skVectorCavityAverage_sum_kernel_eq (R := R) (P := P) μ ξ hξ hbound β ρ q hgm hg'm hYm t F
      hF hFb x
      y Q,
      ← skVectorCavityAverage_const_mul (R := R) (P := P) (g := g) (g' := g') (Y := Y) μ ξ N
      β ρ q t (2 * (d : ℝ) ^ 2) (fun σ : J → Fin (N + 1) → α => |F fun c => σ (some (some c))|)]
    refine abs_skVectorCavityAverage_le μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q hgm hg'm hYm t _ _
      ((continuous_abs.measurable.comp hfm).const_mul _) ⟨2 * (d : ℝ) ^ 2 * M, fun σ => ?_⟩
      fun σ => ?_
    · rw [abs_mul, abs_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ) ^ 2)]
      exact mul_le_mul_of_nonneg_left (hFb _) (by positivity)
    · rw [abs_mul, mul_comm (2 * (d : ℝ) ^ 2)]
      exact mul_le_mul_of_nonneg_left
        (abs_sum_spin_overlap_error_le ξ hbound Q hQ (σ x) (σ y)) (abs_nonneg _)
  set K : ℝ := 2 * (d : ℝ) ^ 2 * skVectorCavityAverage μ ξ N β ρ q P g g' Y t
    (fun σ => |F fun c => σ (some (some c))|) with hK
  have hQ1 : ∀ a b : R, ∑ u, ∑ v, (if a = b then ρ u v else q u v) ^ 2 ≤ (d : ℝ) ^ 2 := by
    intro a b
    by_cases h : a = b
    · simpa only [h, ite_true] using hρ2
    · simpa only [h, ite_false] using hq2
  have hn : (0 : ℝ) ≤ Fintype.card R := Nat.cast_nonneg _
  have hK0 : 0 ≤ K := by
    rw [hK]
    refine mul_nonneg (by positivity) ?_
    have := abs_skVectorCavityAverage_le (R := R) (P := P) μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q
      hgm hg'm hYm t
      (fun σ : J → Fin (N + 1) → α => |F fun c => σ (some (some c))|)
      (fun σ : J → Fin (N + 1) → α => |F fun c => σ (some (some c))|)
      (continuous_abs.measurable.comp hfm) ⟨M, fun σ => by simpa using hFb _⟩
      fun σ => (abs_abs _).le
    exact (abs_nonneg _).trans this
  have hflat : ∀ (a b : R), |∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
      (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
        ξ (σ (some (some b)) (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
          if a = b then ρ u v else q u v))| ≤ K := fun a b =>
    hT (some (some a)) (some (some b)) _ (hQ1 a b)
  have hA : |∑ a : R, ∑ b : R, ∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
      (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
        ξ (σ (some (some b)) (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
          if a = b then ρ u v else q u v))| ≤ Fintype.card R * Fintype.card R * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a : R, |∑ b : R, ∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
          (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
            ξ (σ (some (some b)) (Fin.last N)) v *
            (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
              if a = b then ρ u v else q u v))| ≤ ∑ a : R, (Fintype.card R : ℝ) * K :=
          Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans
            ((Finset.sum_le_sum fun b _ => hflat a b).trans (by simp))
      _ = Fintype.card R * Fintype.card R * K := by simp [mul_assoc]
  have hB : |∑ a : R, ∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
      (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
        ξ (σ (some none) (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some none)) u v - q u v))| ≤
      Fintype.card R * K :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun a _ => hT (some (some a)) (some none) q hq2).trans (by simp))
  have hC := hT (some none) (some none) ρ hρ2
  have hD := hT (some none) none q hq2
  have key : ∀ a b c e : ℝ, |a - b - c + e| ≤ |a| + |b| + |c| + |e| := fun a b c e => by
    have h1 := abs_add_le (a - b - c) e
    have h2 := abs_sub (a - b) c
    have h3 := abs_sub a b
    linarith
  refine (key _ _ _ _).trans ?_
  rw [abs_mul (β ^ 2 / 2), abs_mul ((Fintype.card R : ℝ) * β ^ 2),
    abs_mul ((Fintype.card R : ℝ) * (β ^ 2 / 2)),
    abs_mul ((Fintype.card R : ℝ) * (Fintype.card R + 1) / 2 * β ^ 2)]
  have e1 : |β ^ 2 / 2| = β ^ 2 / 2 := abs_of_nonneg (by positivity)
  have e2 : |(Fintype.card R : ℝ) * β ^ 2| = Fintype.card R * β ^ 2 :=
    abs_of_nonneg (by positivity)
  have e3 : |(Fintype.card R : ℝ) * (β ^ 2 / 2)| = Fintype.card R * (β ^ 2 / 2) :=
    abs_of_nonneg (by positivity)
  have e4 : |(Fintype.card R : ℝ) * (Fintype.card R + 1) / 2 * β ^ 2| =
      Fintype.card R * (Fintype.card R + 1) / 2 * β ^ 2 := abs_of_nonneg (by positivity)
  rw [e1, e2, e3, e4]
  have h1 := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ β ^ 2 / 2)
  have h2 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ Fintype.card R * β ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ Fintype.card R * (β ^ 2 / 2))
  have h4 := mul_le_mul_of_nonneg_left hD
    (by positivity : (0 : ℝ) ≤ Fintype.card R * (Fintype.card R + 1) / 2 * β ^ 2)
  refine (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans (le_of_eq ?_)
  rw [hK]
  ring

/-- **Corollary 1.12.5, Eq. (1.378)**, for `n = 2` replicas.  Here `ν_t(f²)`, the diagonal error
`ν_t(‖R⁻_{1,1} - ρ‖_F²)` and the off-diagonal error `ν_t(‖R⁻_{1,2} - q‖_F²)` are the averages of
the function `F` of the first two replicas and of the matrix overlaps of the replicas `1`, `2`. -/
theorem abs_deriv_skVectorCavityAverage_le_sqrt {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (ρ q : Fin d → Fin d → ℝ)
    (hq : ∀ u v, q u v = q v u) (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2)
    (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    (F : (Fin 2 → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ σ, |F σ| ≤ M)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hG : HasGaussianLaw (fun ω (k : (FinPairs N ⊕ Fin N) ⊕ Fin d) =>
      Sum.elim (Sum.elim (fun p => g p ω) fun i => g' i ω) (fun u => Y u ω) k) P)
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (hgg : ∀ k l : FinPairs N ⊕ Fin N,
      ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k *
        Sum.elim (fun p => g p ω) (fun i => g' i ω) l ∂P = if k = l then 1 else 0)
    (hYY : ∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * q u v)
    (hgY : ∀ (k : FinPairs N ⊕ Fin N) u,
      ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k * Y u ω ∂P = 0)
    (hg0 : ∀ p, ∫ ω, g p ω ∂P = 0) (hg'0 : ∀ i, ∫ ω, g' i ω ∂P = 0)
    (hY0 : ∀ u, ∫ ω, Y u ω ∂P = 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    |deriv (fun s => ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P) t| ≤
      8 * β ^ 2 * d * Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t
          (fun σ => (F fun c => σ (some (some c))) ^ 2)) *
        (Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => ∑ u, ∑ v,
            (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2))))
              (σ (some (some (0 : Fin 2)))) u v - ρ u v) ^ 2)) +
          Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => ∑ u, ∑ v,
            (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2))))
              (σ (some (some (1 : Fin 2)))) u v - q u v) ^ 2))) := by
  rw [(hasDerivAt_skVectorCavityAverage μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q hq F hF hM hFb
    hG hgm
    hg'm hYm hgg hYY hgY hg0 hg'0 hY0 ht0 ht1).deriv]
  classical
  have hφ : ∀ Q : Fin d → Fin d → ℝ, Measurable fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) =>
      ∑ u, ∑ v, (skVectorCavityOverlap ξ N p.1 p.2 u v - Q u v) ^ 2 := fun Q =>
    Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
      Measurable.pow_const (Measurable.sub (measurable_skVectorCavityOverlap hξ N u v)
        measurable_const) 2
  set AF := skVectorCavityAverage μ ξ N β ρ q P g g' Y t
    (fun σ => (F fun c => σ (some (some c))) ^ 2) with hAF
  set Ad := skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => ∑ u, ∑ v,
    (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2)))) (σ (some (some (0 : Fin 2)))) u v -
      ρ u v) ^ 2) with hAd
  set Ao := skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ => ∑ u, ∑ v,
    (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2)))) (σ (some (some (1 : Fin 2)))) u v -
      q u v) ^ 2) with hAo
  have hdiag : ∀ x : Option (Option (Fin 2)), skVectorCavityAverage μ ξ N β ρ q P g g' Y t
      (fun σ => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ x) (σ x) u v - ρ u v) ^ 2) = Ad :=
    fun x => skVectorCavityAverage_diag_eq (R := Fin 2) (P := P) (g := g) (g' := g') (Y := Y) μ ξ hξ
      (Nat.cast_nonneg d) hbound N β ρ q t (φ := fun a b => ∑ u, ∑ v,
        (skVectorCavityOverlap ξ N a b u v - ρ u v) ^ 2) (hφ ρ)
  have hoff : ∀ x y : Option (Option (Fin 2)), x ≠ y → skVectorCavityAverage μ ξ N β ρ q P g g' Y t
      (fun σ => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ x) (σ y) u v - q u v) ^ 2) = Ao :=
    fun x y hxy => skVectorCavityAverage_pair_eq (R := Fin 2) (P := P) (g := g) (g' := g') (Y :=
      Y) μ
      ξ hξ (Nat.cast_nonneg d) hbound N β ρ q t hxy (by simp) (φ := fun a b => ∑ u, ∑ v,
        (skVectorCavityOverlap ξ N a b u v - q u v) ^ 2) (hφ q)
  set Td := d * Real.sqrt AF * Real.sqrt Ad with hTd
  set To := d * Real.sqrt AF * Real.sqrt Ao with hTo
  have term := fun (x y : Option (Option (Fin 2))) (Q : Fin d → Fin d → ℝ)
    (hQ : ∑ u, ∑ v, Q u v ^ 2 ≤ (d : ℝ) ^ 2) =>
    abs_skVectorCavityAverage_sum_kernel_le_sqrt (R := Fin 2) (P := P) μ ξ hξ hbound β ρ q hgm
      hg'm hYm t F hF hFb
      x y Q hQ
  have tX : ∀ a b : Fin 2, |∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
      (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
        ξ (σ (some (some b)) (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
          if a = b then ρ u v else q u v))| ≤ if a = b then Td else To := by
    intro a b
    by_cases h : a = b
    · subst h
      simpa only [ite_true, hdiag] using term (some (some a)) (some (some a)) ρ hρ2
    · have := term (some (some a)) (some (some b)) q hq2
      rw [hoff _ _ (by simpa using h)] at this
      simpa only [h, ite_false] using this
  have tY : ∀ a : Fin 2, |∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ =>
      (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
        ξ (σ (some none) (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some none)) u v - q u v))| ≤ To := by
    intro a
    have := term (some (some a)) (some none) q hq2
    rwa [hoff _ _ (by simp)] at this
  have tZ := term (some none) (some none) ρ hρ2
  rw [hdiag] at tZ
  have tW := term (some none) none q hq2
  rw [hoff _ _ (by simp)] at tW
  have hTd0 : 0 ≤ Td := by positivity
  have hTo0 : 0 ≤ To := by positivity
  have hsumA : |∑ a : Fin 2, ∑ b : Fin 2, ∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t
      (fun σ => (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
        ξ (σ (some (some b)) (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
          if a = b then ρ u v else q u v))| ≤ 2 * Td + 2 * To := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun b _ => tX a b)).trans (le_of_eq ?_)
    simp [Fin.sum_univ_two]
    ring
  have hsumB : |∑ a : Fin 2, ∑ u, ∑ v, skVectorCavityAverage μ ξ N β ρ q P g g' Y t
      (fun σ => (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
        ξ (σ (some none) (Fin.last N)) v *
        (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some none)) u v - q u v))| ≤
      2 * To :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun a _ => tY a).trans (by simp))
  have key : ∀ a b c e : ℝ, |a - b - c + e| ≤ |a| + |b| + |c| + |e| := fun a b c e => by
    have h1 := abs_add_le (a - b - c) e
    have h2 := abs_sub (a - b) c
    have h3 := abs_sub a b
    linarith
  refine (key _ _ _ _).trans ?_
  rw [abs_mul (β ^ 2 / 2), abs_mul ((Fintype.card (Fin 2) : ℝ) * β ^ 2),
    abs_mul ((Fintype.card (Fin 2) : ℝ) * (β ^ 2 / 2)),
    abs_mul ((Fintype.card (Fin 2) : ℝ) * (Fintype.card (Fin 2) + 1) / 2 * β ^ 2)]
  simp only [Fintype.card_fin]
  have e1 : |β ^ 2 / 2| = β ^ 2 / 2 := abs_of_nonneg (by positivity)
  have e2 : |((2 : ℕ) : ℝ) * β ^ 2| = 2 * β ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; norm_num
  have e3 : |((2 : ℕ) : ℝ) * (β ^ 2 / 2)| = β ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; norm_num; ring
  have e4 : |((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) + 1) / 2 * β ^ 2| = 3 * β ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; norm_num
  rw [e1, e2, e3, e4]
  have hβ : 0 ≤ β ^ 2 := sq_nonneg β
  have h1 := mul_le_mul_of_nonneg_left hsumA (by positivity : (0 : ℝ) ≤ β ^ 2 / 2)
  have h2 := mul_le_mul_of_nonneg_left hsumB (by positivity : (0 : ℝ) ≤ 2 * β ^ 2)
  have h3 := mul_le_mul_of_nonneg_left tZ hβ
  have h4 := mul_le_mul_of_nonneg_left tW (by positivity : (0 : ℝ) ≤ 3 * β ^ 2)
  have : 8 * β ^ 2 * d * Real.sqrt AF * (Real.sqrt Ad + Real.sqrt Ao) = 8 * β ^ 2 * (Td + To) := by
    rw [hTd, hTo]; ring
  rw [this]
  nlinarith [h1, h2, h3, h4, mul_nonneg hβ hTd0, mul_nonneg hβ hTo0]

end SpinGlasses
