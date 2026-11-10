/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FixedPoint.PosSemidef
public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.PosSemidef
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Existence of the fixed point of (1.372)--(1.373) (Talagrand, Theorem 1.12.2)

If `18 β² d² < 1` the map `T` of the right-hand sides of (1.372)--(1.373) is a contraction on the
closed cone `{q ⪰ 0, ρ - q ⪰ 0}` for the Frobenius distance (Lipschitz estimate along the
path (1.386), measured in Frobenius norm, which gains a factor `d` over the entrywise estimate),
and the cone is invariant. The iterates of `T` are Cauchy in the supremum distance, which is
dominated by the Frobenius distance, so they converge to a fixed point.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix NNReal
universe u

namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- The cone `{(q, ρ) | q ⪰ 0, ρ - q ⪰ 0}` of admissible pairs of matrices. -/
def skVectorFixedPointCone (d : ℕ) : Set ((Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :=
  {x | (Matrix.of x.1).PosSemidef ∧ (Matrix.of x.2 - Matrix.of x.1).PosSemidef}

theorem isClosed_skVectorFixedPointCone (d : ℕ) : IsClosed (skVectorFixedPointCone d) := by
  have h1 : Continuous fun x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) =>
      (Matrix.of x.1 : Matrix (Fin d) (Fin d) ℝ) := continuous_fst
  have h2 : Continuous fun x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) =>
      (Matrix.of x.2 - Matrix.of x.1 : Matrix (Fin d) (Fin d) ℝ) :=
    (continuous_snd : Continuous fun x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) =>
      (Matrix.of x.2 : Matrix (Fin d) (Fin d) ℝ)).sub h1
  exact (Matrix.isClosed_setOf_posSemidef.preimage h1).inter
    (Matrix.isClosed_setOf_posSemidef.preimage h2)

/-- The Frobenius distance of two pairs of matrices: the larger of the Frobenius distances of the
two blocks.  The fixed-point map contracts it with constant `18 β² d²`, which is what gives the
book's range `β d ≲ 1` (the entrywise supremum distance would give `β d²`). -/
noncomputable def skVectorFrobeniusDist {d : ℕ} (x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ))
  : ℝ :=
  max (Real.sqrt (∑ u, ∑ v, (x.1 u v - y.1 u v) ^ 2))
    (Real.sqrt (∑ u, ∑ v, (x.2 u v - y.2 u v) ^ 2))

theorem skVectorFrobeniusDist_nonneg {d : ℕ} (x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    0 ≤ skVectorFrobeniusDist x y :=
  (Real.sqrt_nonneg _).trans (le_max_left _ _)

theorem sum_sq_le_skVectorFrobeniusDist_sq {d : ℕ} (x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d →
  ℝ)) :
    (∑ u, ∑ v, (x.1 u v - y.1 u v) ^ 2 ≤ skVectorFrobeniusDist x y ^ 2) ∧
      ∑ u, ∑ v, (x.2 u v - y.2 u v) ^ 2 ≤ skVectorFrobeniusDist x y ^ 2 := by
  have h0 : ∀ M : Fin d → Fin d → ℝ, 0 ≤ ∑ u, ∑ v, M u v ^ 2 := fun M =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · calc _ = Real.sqrt (∑ u, ∑ v, (x.1 u v - y.1 u v) ^ 2) ^ 2 :=
          (Real.sq_sqrt (h0 fun u v => x.1 u v - y.1 u v)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2
  · calc _ = Real.sqrt (∑ u, ∑ v, (x.2 u v - y.2 u v) ^ 2) ^ 2 :=
          (Real.sq_sqrt (h0 fun u v => x.2 u v - y.2 u v)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2

theorem skVectorFrobeniusDist_le_of_sum_sq_le {d : ℕ}
    (x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) {K : ℝ} (hK : 0 ≤ K)
    (h1 : ∑ u, ∑ v, (x.1 u v - y.1 u v) ^ 2 ≤ K ^ 2)
    (h2 : ∑ u, ∑ v, (x.2 u v - y.2 u v) ^ 2 ≤ K ^ 2) : skVectorFrobeniusDist x y ≤ K :=
  max_le (Real.sqrt_le_iff.2 ⟨hK, h1⟩) (Real.sqrt_le_iff.2 ⟨hK, h2⟩)

/-- The supremum distance is at most the Frobenius distance. -/
theorem dist_le_skVectorFrobeniusDist {d : ℕ} (x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    dist x y ≤ skVectorFrobeniusDist x y := by
  have hent : ∀ M : Fin d → Fin d → ℝ, ∀ u v, |M u v| ≤ Real.sqrt (∑ u, ∑ v, M u v ^ 2) :=
    fun M u v => by
      refine Real.abs_le_sqrt ?_
      exact (Finset.single_le_sum (f := fun v => M u v ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ v)).trans
        (Finset.single_le_sum (f := fun u => ∑ v, M u v ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ u))
  rw [Prod.dist_eq]
  refine max_le_max ?_ ?_
  · refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun u => (dist_pi_le_iff
      (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.dist_eq]; exact hent (fun u v => x.1 u v - y.1 u v) u v
  · refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun u => (dist_pi_le_iff
      (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.dist_eq]; exact hent (fun u v => x.2 u v - y.2 u v) u v

/-- The Frobenius distance is at most `d` times the supremum distance. -/
theorem skVectorFrobeniusDist_le_mul_dist {d : ℕ} (x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d →
  ℝ)) :
    skVectorFrobeniusDist x y ≤ d * dist x y := by
  have hd : 0 ≤ (d : ℝ) * dist x y := mul_nonneg (Nat.cast_nonneg d) dist_nonneg
  have hblock : ∀ M N : Fin d → Fin d → ℝ, dist M N ≤ dist x y →
      ∑ u, ∑ v, (M u v - N u v) ^ 2 ≤ (d * dist x y) ^ 2 := fun M N hMN => by
    have h1 : ∀ u v, (M u v - N u v) ^ 2 ≤ dist x y ^ 2 := fun u v => by
      have : |M u v - N u v| ≤ dist x y := by
        rw [← Real.dist_eq]
        exact (dist_le_pi_dist (M u) (N u) v).trans ((dist_le_pi_dist M N u).trans hMN)
      calc _ = |M u v - N u v| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
    calc _ ≤ ∑ _u : Fin d, ∑ _v : Fin d, dist x y ^ 2 :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h1 u v
      _ = (d * dist x y) ^ 2 := by simp [mul_pow]; ring
  refine skVectorFrobeniusDist_le_of_sum_sq_le x y hd (hblock _ _ ?_) (hblock _ _ ?_)
  · rw [Prod.dist_eq]; exact le_max_left _ _
  · rw [Prod.dist_eq]; exact le_max_right _ _

/-- The Frobenius distance satisfies the triangle inequality. -/
theorem skVectorFrobeniusDist_triangle {d : ℕ}
    (x y z : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    skVectorFrobeniusDist x z ≤ skVectorFrobeniusDist x y + skVectorFrobeniusDist y z := by
  have hblock : ∀ a b c : Fin d → Fin d → ℝ,
      Real.sqrt (∑ u, ∑ v, (a u v - c u v) ^ 2) ≤
        Real.sqrt (∑ u, ∑ v, (a u v - b u v) ^ 2) + Real.sqrt (∑ u, ∑ v, (b u v - c u v) ^ 2) :=
    fun a b c => by
    let E : (Fin d → Fin d → ℝ) → EuclideanSpace ℝ (Fin d × Fin d) := fun M =>
      WithLp.toLp 2 fun p => M p.1 p.2
    have hE : ∀ M : Fin d → Fin d → ℝ, ‖E M‖ = Real.sqrt (∑ u, ∑ v, M u v ^ 2) := fun M => by
      rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
      simp only [E, Real.norm_eq_abs, sq_abs]
    rw [← hE, ← hE, ← hE]
    have : E (fun u v => a u v - c u v) = E (fun u v => a u v - b u v) +
        E (fun u v => b u v - c u v) := by
      ext p; simp [E]
    rw [this]
    exact norm_add_le _ _
  refine max_le ?_ ?_
  · exact (hblock x.1 y.1 z.1).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (hblock x.2 y.2 z.2).trans (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- **The contraction estimate for the fixed-point map** on the cone, in the Frobenius distance. -/
theorem skVectorFrobeniusDist_fixedPointMap_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedPointCone d)
    (hy : y ∈ skVectorFixedPointCone d) :
    skVectorFrobeniusDist (skVectorFixedPointMap μ ξ β x) (skVectorFixedPointMap μ ξ β y) ≤
      18 * β ^ 2 * (d : ℝ) ^ 2 * skVectorFrobeniusDist x y := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hε := skVectorFrobeniusDist_nonneg x y
  obtain ⟨h1, h2⟩ := sum_sq_le_skVectorFrobeniusDist_sq x y
  refine skVectorFrobeniusDist_le_of_sum_sq_le _ _ (by positivity) ?_ ?_
  · exact sum_sq_skVectorFieldAverage_sub_le μ ξ hξ hbound β hx.1 hy.1 hε h1 h2
      (fun σ u v => ξ (σ 0) u * ξ (σ 1) v)
      (fun u v => ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 1)))
      (fun σ => ⟨ξ (σ 0), ξ (σ 1), hbound _, hbound _, fun _ _ => rfl⟩)
      (fun σ u v => abs_spin_mul_le ξ hd hbound (σ 0) (σ 1) u v)
  · exact sum_sq_skVectorFieldAverage_sub_le μ ξ hξ hbound β hx.1 hy.1 hε h1 h2
      (fun σ u v => ξ (σ 0) u * ξ (σ 0) v)
      (fun u v => ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 0)))
      (fun σ => ⟨ξ (σ 0), ξ (σ 0), hbound _, hbound _, fun _ _ => rfl⟩)
      (fun σ u v => abs_spin_mul_le ξ hd hbound (σ 0) (σ 0) u v)

/-- **The contraction estimate for the fixed-point map** on the cone, in the supremum distance
(a consequence of the Frobenius estimate, with the worse constant `18 β² d³`). -/
theorem dist_skVectorFixedPointMap_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedPointCone d)
    (hy : y ∈ skVectorFixedPointCone d) :
    dist (skVectorFixedPointMap μ ξ β x) (skVectorFixedPointMap μ ξ β y) ≤
      18 * β ^ 2 * (d : ℝ) ^ 3 * dist x y := by
  have h := skVectorFrobeniusDist_fixedPointMap_le μ ξ hξ hbound β hx hy
  have h2 := skVectorFrobeniusDist_le_mul_dist x y
  have hK : 0 ≤ 18 * β ^ 2 * (d : ℝ) ^ 2 := by positivity
  calc _ ≤ _ := dist_le_skVectorFrobeniusDist _ _
    _ ≤ _ := h
    _ ≤ 18 * β ^ 2 * (d : ℝ) ^ 2 * (d * dist x y) := mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

/-- **Existence of a solution of the fixed-point equations (1.372)--(1.373)** for
`18 β² d² < 1`: there is a pair `(q, ρ)` with `q ⪰ 0`, `ρ - q ⪰ 0` and `T(q, ρ) = (q, ρ)`. -/
theorem exists_skVectorFixedPoint {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (hβ : 18 * β ^ 2 * (d : ℝ) ^ 2 < 1) :
    ∃ x ∈ skVectorFixedPointCone d, skVectorFixedPointMap μ ξ β x = x := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  set κ : ℝ := 18 * β ^ 2 * (d : ℝ) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set T := skVectorFixedPointMap μ ξ β with hT
  have hsf : Set.MapsTo T (skVectorFixedPointCone d) (skVectorFixedPointCone d) :=
    fun x _ => ⟨skVectorFixedPointMap_fst_posSemidef μ ξ hξ hbound β x,
      skVectorFixedPointMap_sub_posSemidef μ ξ hξ hbound β x⟩
  have h0 : ((0, 0) : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) ∈ skVectorFixedPointCone d :=
    ⟨Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.zero⟩
  set u : ℕ → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) := fun n => T^[n] (0, 0) with hu
  have hu_succ : ∀ n, u (n + 1) = T (u n) := fun n => by
    simp only [hu]; rw [Function.iterate_succ_apply']
  have hu_cone : ∀ n, u n ∈ skVectorFixedPointCone d := fun n => by
    induction n with
    | zero => exact h0
    | succ n ih => rw [hu_succ]; exact hsf ih
  have hfd : ∀ n, skVectorFrobeniusDist (u (n + 1)) (u n) ≤ skVectorFrobeniusDist (u 1) (u 0) * κ
    ^ n :=
    fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      calc skVectorFrobeniusDist (u (n + 1 + 1)) (u (n + 1)) =
            skVectorFrobeniusDist (T (u (n + 1))) (T (u n)) := by
            rw [← hu_succ (n + 1), ← hu_succ n]
        _ ≤ κ * skVectorFrobeniusDist (u (n + 1)) (u n) :=
            skVectorFrobeniusDist_fixedPointMap_le μ ξ hξ hbound β (hu_cone _) (hu_cone _)
        _ ≤ κ * (skVectorFrobeniusDist (u 1) (u 0) * κ ^ n) := mul_le_mul_of_nonneg_left ih hκ0
        _ = _ := by ring
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric κ (skVectorFrobeniusDist (u 1) (u 0)) hβ
    fun n => by
      rw [dist_comm]
      exact (dist_le_skVectorFrobeniusDist _ _).trans (hfd n)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hycone : y ∈ skVectorFixedPointCone d :=
    (isClosed_skVectorFixedPointCone d).mem_of_tendsto hy (Filter.Eventually.of_forall hu_cone)
  refine ⟨y, hycone, ?_⟩
  have hTcont : Filter.Tendsto (fun n => T (u n)) Filter.atTop (nhds (T y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Filter.Tendsto (fun n => dist (u n) y) Filter.atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.1 hy
    have hlim2 : Filter.Tendsto (fun n => 18 * β ^ 2 * (d : ℝ) ^ 3 * dist (u n) y)
        Filter.atTop (nhds 0) := by
      simpa using hlim.const_mul (18 * β ^ 2 * (d : ℝ) ^ 3)
    exact squeeze_zero (fun n => dist_nonneg) (fun n =>
      dist_skVectorFixedPointMap_le μ ξ hξ hbound β (hu_cone n) hycone) hlim2
  have hshift : Filter.Tendsto (fun n => u (n + 1)) Filter.atTop (nhds y) :=
    hy.comp (Filter.tendsto_add_atTop_nat 1)
  have : (fun n => u (n + 1)) = fun n => T (u n) := funext hu_succ
  rw [this] at hshift
  exact tendsto_nhds_unique hTcont hshift

/-- The law of a centered Gaussian field of covariance `β² Q` is `skVectorGaussianLaw β Q`. -/
theorem map_eq_skVectorGaussianLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (β : ℝ) (Q : Fin d → Fin d → ℝ) {Y : Fin d → Ω → ℝ}
    (hYg : HasGaussianLaw (fun ω u => Y u ω) P) (hY0 : ∀ u, ∫ ω, Y u ω ∂P = 0)
    (hYc : ∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * Q u v) :
    P.map (fun ω u => Y u ω) = skVectorGaussianLaw β Q := by
  rw [map_eq_map_multivariateGaussian hYg hY0]
  unfold skVectorGaussianLaw
  congr 2
  ext u v
  have hmem : ∀ i, MemLp (Y i) 2 P := fun i => (hYg.eval i).memLp_two
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [covariance_eq_sub (hmem u) (hmem v), hY0, hY0]
  have := hYc u v
  simp only [Pi.mul_apply]
  linarith

/-- Disorder averages of field-model Gibbs averages only depend on the law of the field. -/
theorem integral_skVectorFieldAverage_realization {d : ℕ} {Ω R : Type*} [MeasurableSpace Ω]
    [Fintype R] (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (β : ℝ) (ρ Q : Fin d → Fin d → ℝ)
    (F : (R → α) → ℝ) (hF : Measurable F) {P : Measure Ω} {Y : Fin d → Ω → ℝ}
    (hYm : ∀ u, Measurable (Y u))
    (hlaw : P.map (fun ω u => Y u ω) = skVectorGaussianLaw β Q) :
    ∫ ω, skVectorFieldAverage μ ξ β ρ Q F (fun w => Y w ω) ∂P =
      ∫ y, skVectorFieldAverage μ ξ β ρ Q F y ∂(skVectorGaussianLaw β Q) := by
  rw [← hlaw, integral_map (measurable_pi_iff.2 hYm).aemeasurable
    (measurable_skVectorFieldAverage μ ξ hξ β ρ Q F hF).aestronglyMeasurable]

/-- **The fixed-point equations (1.372)--(1.373) for a realization of the Gaussian field are
equivalent to `T(q, ρ) = (q, ρ)`.** -/
theorem skVectorFixedPointMap_eq_iff_equations {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Fin d → Ω → ℝ} (hYg : HasGaussianLaw (fun ω u => Y u ω) P)
    (hYm : ∀ u, Measurable (Y u)) (hY0 : ∀ u, ∫ ω, Y u ω ∂P = 0)
    (hYc : ∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * x.1 u v) :
    skVectorFixedPointMap μ ξ β x = x ↔
      (∀ u v, x.1 u v = ∫ ω,
        (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω)))) *
        (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω)))) ∂P) ∧
      (∀ u v, x.2 u v = ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
        (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω))) ∂P) := by
  have hlaw := map_eq_skVectorGaussianLaw β x.1 hYg hY0 hYc
  have hF1 : ∀ u v, Measurable fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 1) v := fun u v =>
    ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 1))
  have hF2 : ∀ u v, Measurable fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 0) v := fun u v =>
    ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 0))
  have e1 : ∀ u v, ∫ ω,
      (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω)))) *
      (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω)))) ∂P =
      (skVectorFixedPointMap μ ξ β x).1 u v := fun u v => by
    simp only [skVectorFixedPointMap]
    rw [← integral_skVectorFieldAverage_realization μ ξ hξ β x.2 x.1 _ (hF1 u v) hYm hlaw]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (skVectorFieldAverage_pair μ ξ β x.2 x.1 u v _).symm)
  have e2 : ∀ u v, ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
      (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω))) ∂P =
      (skVectorFixedPointMap μ ξ β x).2 u v := fun u v => by
    simp only [skVectorFixedPointMap]
    rw [← integral_skVectorFieldAverage_realization μ ξ hξ β x.2 x.1 _ (hF2 u v) hYm hlaw]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (skVectorFieldAverage_diag μ ξ hξ hbound β x.2 x.1 u v _).symm)
  simp only [e1, e2]
  constructor
  · intro h
    exact ⟨fun u v => by rw [h], fun u v => by rw [h]⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext (funext fun u => funext fun v => (h1 u v).symm)
      (funext fun u => funext fun v => (h2 u v).symm)

/-- **Uniqueness of the fixed point in the cone** (for `18 β² d² < 1`). -/
theorem skVectorFixedPoint_unique {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (hβ : 18 * β ^ 2 * (d : ℝ) ^ 2 < 1)
    {x y : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedPointCone d)
    (hy : y ∈ skVectorFixedPointCone d) (hxf : skVectorFixedPointMap μ ξ β x = x)
    (hyf : skVectorFixedPointMap μ ξ β y = y) : x = y := by
  have h := skVectorFrobeniusDist_fixedPointMap_le μ ξ hξ hbound β hx hy
  rw [hxf, hyf] at h
  have hd : 0 ≤ skVectorFrobeniusDist x y := skVectorFrobeniusDist_nonneg x y
  have : skVectorFrobeniusDist x y ≤ 0 := by nlinarith
  exact dist_le_zero.1 ((dist_le_skVectorFrobeniusDist x y).trans this)

/-- **Theorem 1.12.2 (Talagrand): existence and uniqueness of the solution of (1.372)--(1.373)**,
for `18 β² d² < 1`.  There is a pair `(q, ρ)` with `q ⪰ 0` solving the equations for every
realization of the Gaussian field `Y` of covariance `β² q`; any other pair `(q', ρ')` with
`q' ⪰ 0` solving the equations for some realization `Y'` of covariance `β² q'` equals it. -/
theorem exists_skVectorFixedPoint_equations_unique {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (hβ : 18 * β ^ 2 * (d : ℝ) ^ 2 < 1) :
    ∃ x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ), (Matrix.of x.1).PosSemidef ∧
      (Matrix.of x.2 - Matrix.of x.1).PosSemidef ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {Y : Fin d → Ω → ℝ}, HasGaussianLaw (fun ω u => Y u ω) P → (∀ u, Measurable (Y u)) →
        (∀ u, ∫ ω, Y u ω ∂P = 0) → (∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * x.1 u v) →
        (∀ u v, x.1 u v = ∫ ω,
          (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω)))) *
          (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω)))) ∂P) ∧
        (∀ u v, x.2 u v = ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
          (skVectorFieldExponent ξ β x.2 x.1 (fun w => Y w ω))) ∂P)) ∧
      ∀ x' : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ), (Matrix.of x'.1).PosSemidef →
        ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
          {Y : Fin d → Ω → ℝ}, HasGaussianLaw (fun ω u => Y u ω) P → (∀ u, Measurable (Y u)) →
          (∀ u, ∫ ω, Y u ω ∂P = 0) → (∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * x'.1 u v) →
          (∀ u v, x'.1 u v = ∫ ω,
            (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β x'.2 x'.1 (fun w => Y w ω)))) *
            (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β x'.2 x'.1 (fun w => Y w ω)))) ∂P) →
          (∀ u v, x'.2 u v = ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
            (skVectorFieldExponent ξ β x'.2 x'.1 (fun w => Y w ω))) ∂P) → x' = x := by
  obtain ⟨x, hx, hxf⟩ := exists_skVectorFixedPoint μ ξ hξ hbound β hβ
  refine ⟨x, hx.1, hx.2, ?_, ?_⟩
  · intro Ω _ P _ Y hYg hYm hY0 hYc
    exact (skVectorFixedPointMap_eq_iff_equations μ ξ hξ hbound β x hYg hYm hY0 hYc).1 hxf
  · intro x' hx' Ω _ P _ Y hYg hYm hY0 hYc h1 h2
    have hfix := (skVectorFixedPointMap_eq_iff_equations μ ξ hξ hbound β x' hYg hYm hY0 hYc).2
      ⟨h1, h2⟩
    have hcone : x' ∈ skVectorFixedPointCone d := by
      rw [← hfix]
      exact ⟨skVectorFixedPointMap_fst_posSemidef μ ξ hξ hbound β x',
        skVectorFixedPointMap_sub_posSemidef μ ξ hξ hbound β x'⟩
    exact skVectorFixedPoint_unique μ ξ hξ hbound β hβ hcone hx hfix hxf

end SpinGlasses
