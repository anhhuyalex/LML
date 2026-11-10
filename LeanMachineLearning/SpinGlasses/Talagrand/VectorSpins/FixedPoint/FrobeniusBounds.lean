/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FixedPoint.Bounds
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IntegrableOfBound

/-!
# Frobenius-norm bounds for the replica combinations of the smart path

The derivative along the interpolation path (1.386) involves the matrix-weighted sums
`∑ᵤᵥ Δᵤᵥ 𝔼⟨(ξᵤ(σ¹) - n ξᵤ(σ'))(ξᵥ(σ²) - (n+1) ξᵥ(σ³))⟩` and `∑ⱼ Cⱼ 𝔼⟨… ξᵤξᵥ …⟩`. Bounding
them through the Frobenius norm of `Δ` and `C` (instead of entrywise) gains a factor `d`, which
gives the contraction condition `β d ≲ 1` of the book.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

/-- A replica combination `∑ₐ f(σₐ) - c g` of bounded terms, with `c` the number of terms, is at
most
`2 c b` in absolute value. -/
theorem abs_replica_combination_le {J : Type*} [Fintype J] (f : J → ℝ) (g b : ℝ)
    (hf : ∀ j, |f j| ≤ b) (hg : |g| ≤ b) {c : ℝ} (hc : (Fintype.card J : ℝ) = c) :
    |∑ j, f j - c * g| ≤ 2 * c * b := by
  have hc0 : 0 ≤ c := hc ▸ Nat.cast_nonneg _
  have h1 : |∑ j, f j| ≤ c * b := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |f j| ≤ ∑ _j : J, b := Finset.sum_le_sum fun j _ => hf j
      _ = c * b := by simp [hc]
  calc |∑ j, f j - c * g| ≤ |∑ j, f j| + |c * g| := abs_sub _ _
    _ ≤ c * b + c * b := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_of_nonneg hc0]
        exact mul_le_mul_of_nonneg_left hg hc0
    _ = 2 * c * b := by ring

section Algebra

variable {d : ℕ}

theorem sum_sum_sum_comm {J : Type*} [Fintype J] (h : J → Fin d → Fin d → ℝ) :
    ∑ u, ∑ v, ∑ j, h j u v = ∑ j, ∑ u, ∑ v, h j u v :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/-- Linearity of a bilinear form in the first argument. -/
theorem sum_bilinear_left {J : Type*} [Fintype J] (Δ : Fin d → Fin d → ℝ) (f : J → Fin d → ℝ)
    (g w : Fin d → ℝ) (c : ℝ) :
    ∑ u, ∑ v, Δ u v * ((∑ j, f j u - c * g u) * w v) =
      ∑ j, ∑ u, ∑ v, Δ u v * (f j u * w v) - c * ∑ u, ∑ v, Δ u v * (g u * w v) := by
  have pt : ∀ u v, Δ u v * ((∑ j, f j u - c * g u) * w v) =
      ∑ j, Δ u v * (f j u * w v) - c * (Δ u v * (g u * w v)) := fun u v => by
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
    congr 1
    ring
  simp only [pt, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [sum_sum_sum_comm (fun j u v => Δ u v * (f j u * w v))]

/-- Linearity of a bilinear form in the second argument. -/
theorem sum_bilinear_right {J : Type*} [Fintype J] (Δ : Fin d → Fin d → ℝ) (f : J → Fin d → ℝ)
    (g x : Fin d → ℝ) (c : ℝ) :
    ∑ u, ∑ v, Δ u v * (x u * (∑ j, f j v - c * g v)) =
      ∑ j, ∑ u, ∑ v, Δ u v * (x u * f j v) - c * ∑ u, ∑ v, Δ u v * (x u * g v) := by
  have pt : ∀ u v, Δ u v * (x u * (∑ j, f j v - c * g v)) =
      ∑ j, Δ u v * (x u * f j v) - c * (Δ u v * (x u * g v)) := fun u v => by
    rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    ring
  simp only [pt, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [sum_sum_sum_comm (fun j u v => Δ u v * (x u * f j v))]

end Algebra


section Bounds

variable {d : ℕ} {α : Type*} [MeasurableSpace α]

/-- **The replica combinations are bounded by the Frobenius norm.**  For `Δ` with `‖Δ‖_F ≤ ε`,
spins of squared radius at most `d`, the bilinear form of `Δ` on
`(∑_{j∈J} f_j - c g, ∑_{k∈K} h_k - c' k₀)` is at most `4 c c' d ε`. -/
theorem abs_bilinear_combination_le {J K : Type*} [Fintype J] [Fintype K]
    (Δ : Fin d → Fin d → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hΔ : ∑ u, ∑ v, Δ u v ^ 2 ≤ ε ^ 2)
    (f : J → Fin d → ℝ) (g : Fin d → ℝ) (h : K → Fin d → ℝ) (k₀ : Fin d → ℝ)
    (hf : ∀ j, ∑ u, f j u ^ 2 ≤ d) (hg : ∑ u, g u ^ 2 ≤ d) (hh : ∀ k, ∑ v, h k v ^ 2 ≤ d)
    (hk : ∑ v, k₀ v ^ 2 ≤ d) {c c' : ℝ} (hc : (Fintype.card J : ℝ) = c)
    (hc' : (Fintype.card K : ℝ) = c') :
    |∑ u, ∑ v, Δ u v * ((∑ j, f j u - c * g u) * (∑ k, h k v - c' * k₀ v))| ≤
      2 * c * (2 * c' * (d * ε)) := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hbil : ∀ x w : Fin d → ℝ, ∑ u, x u ^ 2 ≤ d → ∑ v, w v ^ 2 ≤ d →
      |∑ u, ∑ v, Δ u v * (x u * w v)| ≤ d * ε := fun x w hx hw => by
    have := abs_sum_bilinear_le Δ x w hε hsd hsd hΔ (by rw [hsq]; exact hx) (by rw [hsq]; exact hw)
    calc _ ≤ ε * Real.sqrt d * Real.sqrt d := this
      _ = d * ε := by rw [mul_assoc, Real.mul_self_sqrt hd]; ring
  have hrow : ∀ x : Fin d → ℝ, ∑ u, x u ^ 2 ≤ d →
      |∑ u, ∑ v, Δ u v * (x u * (∑ k, h k v - c' * k₀ v))| ≤ 2 * c' * (d * ε) := fun x hx => by
    rw [sum_bilinear_right]
    exact abs_replica_combination_le (fun k => ∑ u, ∑ v, Δ u v * (x u * h k v)) _ (d * ε)
      (fun k => hbil _ _ hx (hh k)) (hbil _ _ hx hk) hc'
  rw [sum_bilinear_left]
  exact abs_replica_combination_le (fun j => ∑ u, ∑ v, Δ u v * (f j u * (∑ k, h k v - c' * k₀ v)))
    _ (2 * c' * (d * ε)) (fun j => hrow (f j) (hf j)) (hrow g hg) hc

/-- The first replica combination is measurable in the replicas. -/
theorem measurable_replica_combination {R : Type*} [Fintype R] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (c : ℝ) (u : Fin d) :
    Measurable fun σ : Option (Option R) → α =>
      ∑ a, ξ (σ (some (some a))) u - c * ξ (σ (some none)) u :=
  (Finset.measurable_sum _ fun _ _ => (hξ u).comp (measurable_pi_apply _)).sub
    (measurable_const.mul ((hξ u).comp (measurable_pi_apply _)))

/-- The second replica combination is measurable in the replicas. -/
theorem measurable_replica_combination' {R : Type*} [Fintype R] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (c : ℝ) (u : Fin d) :
    Measurable fun σ : Option (Option R) → α =>
      ∑ o, ξ (σ (some o)) u - c * ξ (σ none) u :=
  (Finset.measurable_sum _ fun _ _ => (hξ u).comp (measurable_pi_apply _)).sub
    (measurable_const.mul ((hξ u).comp (measurable_pi_apply _)))

/-- **The `(ξᵤ, ξᵥ)` replica integrals against a matrix `Δ`** (Frobenius form).  For
`∑ Δ² ≤ ε²`, the matrix-weighted sum of the disorder-averaged replica Gibbs averages
`𝔼⟨F (∑ₐ ξᵤ(σₐ) - n ξᵤ(σ')) (∑ₒ ξᵥ(σₒ) - (n+1) ξᵥ(σ''))⟩` is at most `4 n (n+1) M d ε`. -/
theorem abs_sum_integral_pair_le {Ω R : Type*} [MeasurableSpace Ω] [Fintype R] {μ : Measure α}
    [IsFiniteMeasure μ] (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {en : Ω → α → ℝ}
    (hE : Measurable fun p : Ω × α => en p.1 p.2)
    (hprob : ∀ ω, IsProbabilityMeasure (μ.tilted (en ω))) {P : Measure Ω} [IsProbabilityMeasure P]
    (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M)
    (Δ : Fin d → Fin d → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hΔ : ∑ u, ∑ v, Δ u v ^ 2 ≤ ε ^ 2) :
    |∑ u, ∑ v, Δ u v * ∫ ω, ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
        (∑ a, ξ (σ (some (some a))) u - (Fintype.card R : ℝ) * ξ (σ (some none)) u) *
        (∑ o, ξ (σ (some o)) v - ((Fintype.card R : ℝ) + 1) * ξ (σ none) v)
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P| ≤
      M * (4 * (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) * d * ε) := by
  classical
  set n : ℝ := (Fintype.card R : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hcardo : (Fintype.card (Option R) : ℝ) = n + 1 := by simp [hn]
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  set G : Fin d × Fin d → (Option (Option R) → α) → ℝ := fun j σ =>
    (F fun a => σ (some (some a))) *
      (∑ a, ξ (σ (some (some a))) j.1 - n * ξ (σ (some none)) j.1) *
      (∑ o, ξ (σ (some o)) j.2 - (n + 1) * ξ (σ none) j.2) with hG
  have hFm : Measurable fun σ : Option (Option R) → α => F fun a => σ (some (some a)) :=
    hF.comp (Measurable.of_eval fun a => measurable_pi_apply _)
  have hGm : ∀ j, Measurable (G j) := fun j =>
    (hFm.mul (measurable_replica_combination ξ hξ n j.1)).mul
      (measurable_replica_combination' ξ hξ (n + 1) j.2)
  have hGb : ∀ j σ, |G j σ| ≤ M * (2 * n * Real.sqrt d) * (2 * (n + 1) * Real.sqrt d) := by
    intro j σ
    simp only [hG]
    rw [abs_mul, abs_mul]
    have h1 := abs_replica_combination_le (fun a : R => ξ (σ (some (some a))) j.1)
      (ξ (σ (some none)) j.1) (Real.sqrt d) (fun a => hxb _ _) (hxb _ _) (c := n) rfl
    have h2 := abs_replica_combination_le (fun o : Option R => ξ (σ (some o)) j.2)
      (ξ (σ none) j.2) (Real.sqrt d) (fun a => hxb _ _) (hxb _ _) hcardo
    exact mul_le_mul (mul_le_mul (hFb _) h1 (abs_nonneg _) hM) h2 (abs_nonneg _)
      (by positivity)
  have hsum : ∫ ω, ∫ σ, ∑ j, Δ j.1 j.2 * G j σ
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P =
      ∑ j : Fin d × Fin d, Δ j.1 j.2 * ∫ ω, ∫ σ, G j σ
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P := by
    have hlin := integral_integral_finset_sum P
      (fun ω => Measure.pi fun _ : Option (Option R) => μ.tilted (en ω))
      (Finset.univ : Finset (Fin d × Fin d)) (fun j σ => Δ j.1 j.2 * G j σ)
      (fun j _ ω => by
        have := hprob ω
        exact integrable_of_measurable_bound ((hGm j).const_mul _) fun σ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hGb j σ) (abs_nonneg _))
      (fun j _ => by
        simp_rw [integral_const_mul]
        exact (integrable_integral_pi_tilted hE hprob (hGm j) (hGb j)).const_mul _)
    simp_rw [integral_const_mul] at hlin
    exact hlin
  have hconv : (∑ u, ∑ v, Δ u v * ∫ ω, ∫ σ : Option (Option R) → α,
      (F fun a => σ (some (some a))) *
        (∑ a, ξ (σ (some (some a))) u - n * ξ (σ (some none)) u) *
        (∑ o, ξ (σ (some o)) v - (n + 1) * ξ (σ none) v)
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P) =
      ∑ j : Fin d × Fin d, Δ j.1 j.2 * ∫ ω, ∫ σ, G j σ
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P := by
    rw [Fintype.sum_prod_type]
  rw [hconv, ← hsum]
  refine abs_integral_integral_pi_tilted_le hprob fun σ => ?_
  have hF1 : ∑ j : Fin d × Fin d, Δ j.1 j.2 * G j σ = F (fun a => σ (some (some a))) *
      ∑ u, ∑ v, Δ u v * ((∑ a, ξ (σ (some (some a))) u - n * ξ (σ (some none)) u) *
        (∑ o, ξ (σ (some o)) v - (n + 1) * ξ (σ none) v)) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by simp only [hG]; ring
  rw [hF1, abs_mul]
  have hQ := abs_bilinear_combination_le Δ hε hΔ (fun a : R => ξ (σ (some (some a))))
    (ξ (σ (some none))) (fun o : Option R => ξ (σ (some o))) (ξ (σ none))
    (fun a => hbound _) (hbound _) (fun o => hbound _) (hbound _) (c := n) (c' := n + 1) rfl
    hcardo
  calc |F fun a => σ (some (some a))| * _ ≤ M * (2 * n * (2 * (n + 1) * (d * ε))) :=
        mul_le_mul (hFb _) hQ (abs_nonneg _) hM
    _ = _ := by ring

/-- **The single-spin replica integrals against a matrix `C`** (Frobenius form).  For
`∑ C² ≤ ε²` the matrix-weighted sum of
`𝔼⟨F (∑ₒ ξᵤ(σₒ) ξᵥ(σₒ) - (n+1) ξᵤ(σ'') ξᵥ(σ''))⟩` is at most `2 (n+1) M d ε`. -/
theorem abs_sum_integral_single_le {Ω R : Type*} [MeasurableSpace Ω] [Fintype R] {μ : Measure α}
    [IsFiniteMeasure μ] (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {en : Ω → α → ℝ}
    (hE : Measurable fun p : Ω × α => en p.1 p.2)
    (hprob : ∀ ω, IsProbabilityMeasure (μ.tilted (en ω))) {P : Measure Ω} [IsProbabilityMeasure P]
    (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M)
    (C : Fin d → Fin d → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hC : ∑ u, ∑ v, C u v ^ 2 ≤ ε ^ 2) :
    |∑ j : Fin d × Fin d, C j.1 j.2 * ∫ ω, ∫ σ : Option (Option R) → α,
        (F fun a => σ (some (some a))) *
          (∑ o : Option R, ξ (σ (some o)) j.1 * ξ (σ (some o)) j.2 -
            ((Fintype.card R : ℝ) + 1) * (ξ (σ none) j.1 * ξ (σ none) j.2))
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P| ≤
      M * (2 * ((Fintype.card R : ℝ) + 1) * (d * ε)) := by
  classical
  set n : ℝ := (Fintype.card R : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hcardo : (Fintype.card (Option R) : ℝ) = n + 1 := by simp [hn]
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hxs : ∀ a u v, |ξ a u * ξ a v| ≤ d := fun a u v =>
    abs_spin_mul_le ξ hd hbound a a u v
  set G : Fin d × Fin d → (Option (Option R) → α) → ℝ := fun j σ =>
    (F fun a => σ (some (some a))) *
      (∑ o : Option R, ξ (σ (some o)) j.1 * ξ (σ (some o)) j.2 -
        (n + 1) * (ξ (σ none) j.1 * ξ (σ none) j.2)) with hG
  have hFm : Measurable fun σ : Option (Option R) → α => F fun a => σ (some (some a)) :=
    hF.comp (Measurable.of_eval fun a => measurable_pi_apply _)
  have hGm : ∀ j, Measurable (G j) := fun j =>
    hFm.mul ((Finset.measurable_sum _ fun o _ => ((hξ j.1).comp (measurable_pi_apply _)).mul
      ((hξ j.2).comp (measurable_pi_apply _))).sub (measurable_const.mul
      (((hξ j.1).comp (measurable_pi_apply _)).mul ((hξ j.2).comp (measurable_pi_apply _)))))
  have hGb : ∀ j σ, |G j σ| ≤ M * (2 * (n + 1) * d) := by
    intro j σ
    simp only [hG]
    rw [abs_mul]
    have h2 := abs_replica_combination_le
      (fun o : Option R => ξ (σ (some o)) j.1 * ξ (σ (some o)) j.2)
      (ξ (σ none) j.1 * ξ (σ none) j.2) (d : ℝ) (fun a => hxs _ _ _) (hxs _ _ _) hcardo
    exact mul_le_mul (hFb _) h2 (abs_nonneg _) hM
  have hsum : ∫ ω, ∫ σ, ∑ j, C j.1 j.2 * G j σ
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P =
      ∑ j : Fin d × Fin d, C j.1 j.2 * ∫ ω, ∫ σ, G j σ
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P := by
    have hlin := integral_integral_finset_sum P
      (fun ω => Measure.pi fun _ : Option (Option R) => μ.tilted (en ω))
      (Finset.univ : Finset (Fin d × Fin d)) (fun j σ => C j.1 j.2 * G j σ)
      (fun j _ ω => by
        have := hprob ω
        exact integrable_of_measurable_bound ((hGm j).const_mul _) fun σ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hGb j σ) (abs_nonneg _))
      (fun j _ => by
        simp_rw [integral_const_mul]
        exact (integrable_integral_pi_tilted hE hprob (hGm j) (hGb j)).const_mul _)
    simp_rw [integral_const_mul] at hlin
    exact hlin
  rw [← hsum]
  refine abs_integral_integral_pi_tilted_le hprob fun σ => ?_
  have hq : ∀ a, |∑ u, ∑ v, C u v * (ξ a u * ξ a v)| ≤ d * ε := fun a => by
    have := abs_sum_bilinear_le C (ξ a) (ξ a) hε (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC
      (by rw [Real.sq_sqrt hd]; exact hbound a) (by rw [Real.sq_sqrt hd]; exact hbound a)
    calc _ ≤ ε * Real.sqrt d * Real.sqrt d := this
      _ = d * ε := by rw [mul_assoc, Real.mul_self_sqrt hd]; ring
  have hF1 : ∑ j : Fin d × Fin d, C j.1 j.2 * G j σ = F (fun a => σ (some (some a))) *
      (∑ o : Option R, ∑ u, ∑ v, C u v * (ξ (σ (some o)) u * ξ (σ (some o)) v) -
        (n + 1) * ∑ u, ∑ v, C u v * (ξ (σ none) u * ξ (σ none) v)) := by
    have pt : ∀ u v, C u v * G (u, v) σ = F (fun a => σ (some (some a))) *
        (∑ o : Option R, C u v * (ξ (σ (some o)) u * ξ (σ (some o)) v) -
          (n + 1) * (C u v * (ξ (σ none) u * ξ (σ none) v))) := fun u v => by
      simp only [hG]
      rw [mul_left_comm]
      congr 1
      rw [mul_sub, Finset.mul_sum]
      ring
    rw [Fintype.sum_prod_type]
    simp only [pt]
    have hF : ∀ X : Fin d → Fin d → ℝ, ∑ u, ∑ v, F (fun a => σ (some (some a))) * X u v =
        F (fun a => σ (some (some a))) * ∑ u, ∑ v, X u v := fun X => by
      simp only [Finset.mul_sum]
    rw [hF]
    congr 1
    simp only [Finset.sum_sub_distrib]
    congr 1
    · exact sum_sum_sum_comm (fun o u v => C u v * (ξ (σ (some o)) u * ξ (σ (some o)) v))
    · simp only [Finset.mul_sum]
  rw [hF1, abs_mul]
  have h3 := abs_replica_combination_le
    (fun o : Option R => ∑ u, ∑ v, C u v * (ξ (σ (some o)) u * ξ (σ (some o)) v))
    (∑ u, ∑ v, C u v * (ξ (σ none) u * ξ (σ none) v)) (d * ε) (fun o => hq _) (hq _) hcardo
  calc |F fun a => σ (some (some a))| * _ ≤ M * (2 * (n + 1) * (d * ε)) :=
        mul_le_mul (hFb _) h3 (abs_nonneg _) hM
    _ = _ := by ring

end Bounds

end SpinGlasses
