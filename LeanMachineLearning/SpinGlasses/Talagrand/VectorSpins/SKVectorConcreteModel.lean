/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.SKVectorTheorem1121
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.SKVectorFixedPointExistence
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm

/-!
# The concrete probability space of Theorem 1.12.1

The vector SK model with `N + 1` sites lives on `Ω = (FinPairs (N+1) → ℝ) × (Fin d → ℝ)` with the
product of i.i.d. standard Gaussian couplings and the Gaussian field `Y` of covariance `β² q`.  On
this space the hypotheses of `skVector_theorem_1_12_1` (joint Gaussianity with the right
covariances, independence of `Y` from the couplings, site-invariance of the coupling law) hold.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- The embedding of the pairs of the old sites and of the pairs with the last site into the pairs
of `N + 1` sites. -/
def finPairsSplit (N : ℕ) : FinPairs N ⊕ Fin N → FinPairs (N + 1) :=
  Sum.elim (fun p => ⟨(p.val.1.castSucc, p.val.2.castSucc),
    Fin.castSucc_lt_castSucc_iff.mpr p.property⟩)
    (fun i => ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩)

theorem finPairsSplit_injective (N : ℕ) : Function.Injective (finPairsSplit N) := by
  rintro (p | i) (p' | i') h
  · simp only [finPairsSplit, Sum.elim_inl] at h
    have := congrArg Subtype.val h
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
    exact congrArg Sum.inl (Subtype.ext (Prod.ext this.1 this.2))
  · simp only [finPairsSplit, Sum.elim_inl, Sum.elim_inr] at h
    have := congrArg Subtype.val h
    simp only [Prod.mk.injEq] at this
    exact absurd this.2 (Fin.castSucc_ne_last _)
  · simp only [finPairsSplit, Sum.elim_inl, Sum.elim_inr] at h
    have := congrArg Subtype.val h
    simp only [Prod.mk.injEq] at this
    exact absurd this.2.symm (Fin.castSucc_ne_last _)
  · simp only [finPairsSplit, Sum.elim_inr] at h
    have := congrArg Subtype.val h
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
    exact congrArg Sum.inr this.1

/-- Covariance of the i.i.d. standard Gaussian couplings. -/
theorem integral_pi_gaussianReal_coord_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (p p' : κ) :
    ∫ g : κ → ℝ, g p * g p' ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
      if p = p' then 1 else 0 := by
  have := integral_dotProduct_mul_dotProduct_pi_gaussianReal (Pi.single p (1 : ℝ))
    (Pi.single p' (1 : ℝ))
  simpa [dotProduct_single, single_dotProduct, Pi.single_apply, eq_comm] using this

/-- The i.i.d. standard Gaussian couplings are centered. -/
theorem integral_pi_gaussianReal_coord {κ : Type*} [Fintype κ] (p : κ) :
    ∫ g : κ → ℝ, g p ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = 0 := by
  have := integral_pi_eval (gaussianReal 0 1) (J := κ) p (fun x : ℝ => x)
    aestronglyMeasurable_id
  simpa using this

/-- The Gaussian field of covariance `β² q` is centered. -/
theorem integral_skVectorGaussLaw_coord {d : ℕ} (β : ℝ) (Q : Fin d → Fin d → ℝ) (u : Fin d) :
    ∫ y, y u ∂(skVectorGaussLaw β Q) = 0 := by
  unfold skVectorGaussLaw
  have h := integral_map (μ := multivariateGaussian 0 (β ^ 2 • Matrix.of Q))
    (φ := fun z : EuclideanSpace ℝ (Fin d) => z.ofLp) (f := fun y : Fin d → ℝ => y u)
    (by fun_prop) (measurable_pi_apply u).aestronglyMeasurable
  rw [h]
  exact integral_eval_multivariateGaussian _ u

/-- Second moments of the Gaussian field of covariance `β² q`. -/
theorem integral_skVectorGaussLaw_mul {d : ℕ} (β : ℝ) (Q : Fin d → Fin d → ℝ)
    (hQ : (Matrix.of Q).PosSemidef) (u v : Fin d) :
    ∫ y, y u * y v ∂(skVectorGaussLaw β Q) = β ^ 2 * Q u v := by
  unfold skVectorGaussLaw
  have h := integral_map (μ := multivariateGaussian 0 (β ^ 2 • Matrix.of Q))
    (φ := fun z : EuclideanSpace ℝ (Fin d) => z.ofLp) (f := fun y : Fin d → ℝ => y u * y v)
    (by fun_prop) (((measurable_pi_apply u).mul (measurable_pi_apply v)).aestronglyMeasurable)
  rw [h]
  have := integral_mul_eval_multivariateGaussian (hQ.smul (sq_nonneg β)) u v
  simpa using this

/-- The probability law of the concrete model: i.i.d. standard Gaussian couplings on the pairs of
`N + 1` sites, independent of the Gaussian field of covariance `β² q`. -/
noncomputable def skVectorConcreteLaw (N : ℕ) {d : ℕ} (β : ℝ) (q : Fin d → Fin d → ℝ) :
    Measure ((FinPairs (N + 1) → ℝ) × (Fin d → ℝ)) :=
  (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (skVectorGaussLaw β q)

instance (N : ℕ) {d : ℕ} (β : ℝ) (q : Fin d → Fin d → ℝ) :
    IsProbabilityMeasure (skVectorConcreteLaw N β q) := by
  unfold skVectorConcreteLaw; infer_instance

/-- **The concrete model satisfies the Gaussian-noise hypotheses of the cavity path.** -/
theorem skVectorConcreteNoise (N : ℕ) {d : ℕ} (β : ℝ) (q : Fin d → Fin d → ℝ)
    (hq : (Matrix.of q).PosSemidef) :
    SKVectorCavityNoise (skVectorConcreteLaw N β q) N d β q
      (fun p ω => ω.1 (finPairsSplit N (Sum.inl p)))
      (fun i ω => ω.1 (finPairsSplit N (Sum.inr i))) (fun u ω => ω.2 u) := by
  classical
  have hG1 : IsGaussian (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    isGaussian_pi_gaussianReal
  have hG2 := isGaussian_skVectorGaussLaw β q
  have h1 : HasGaussianLaw (fun x : FinPairs (N + 1) → ℝ => x)
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := IsGaussian.hasGaussianLaw_id
  have h2 : HasGaussianLaw (fun y : Fin d → ℝ => y) (skVectorGaussLaw β q) :=
    IsGaussian.hasGaussianLaw_id
  have hjoint := HasGaussianLaw.sumElim_prod_of_independent h1 h2 measurable_id measurable_id
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hjoint.reindex (Sum.map (finPairsSplit N) (id : Fin d → Fin d))
    have e : (fun (ω : (FinPairs (N + 1) → ℝ) × (Fin d → ℝ)) (k : (FinPairs N ⊕ Fin N) ⊕ Fin d) =>
        Sum.elim (Sum.elim (fun p => ω.1 (finPairsSplit N (Sum.inl p)))
          fun i => ω.1 (finPairsSplit N (Sum.inr i))) (fun u => ω.2 u) k) =
        fun ω k => Sum.elim (fun a => ω.1 a) (fun b => ω.2 b)
          (Sum.map (finPairsSplit N) (id : Fin d → Fin d) k) := by
      funext ω k
      rcases k with (p | i) | u <;> rfl
    rw [e]
    exact this
  · exact fun p => by fun_prop
  · exact fun i => by fun_prop
  · exact fun u => by fun_prop
  · intro k l
    have hel : ∀ (ω : (FinPairs (N + 1) → ℝ) × (Fin d → ℝ)) (k : FinPairs N ⊕ Fin N),
        Sum.elim (fun p => ω.1 (finPairsSplit N (Sum.inl p)))
          (fun i => ω.1 (finPairsSplit N (Sum.inr i))) k = ω.1 (finPairsSplit N k) :=
      fun ω k => by rcases k with p | i <;> rfl
    simp only [hel]
    have := integral_prod_mul (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      (ν := skVectorGaussLaw β q) (fun g => g (finPairsSplit N k) * g (finPairsSplit N l))
      (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    unfold skVectorConcreteLaw
    rw [this, integral_pi_gaussianReal_coord_mul]
    simp [(finPairsSplit_injective N).eq_iff]
  · intro u v
    have := integral_prod_mul (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      (ν := skVectorGaussLaw β q) (fun _ => (1 : ℝ)) (fun y => y u * y v)
    simp only [one_mul, integral_const, probReal_univ, smul_eq_mul] at this
    unfold skVectorConcreteLaw
    rw [this, integral_skVectorGaussLaw_mul β q hq]
  · intro k u
    have hel : ∀ (ω : (FinPairs (N + 1) → ℝ) × (Fin d → ℝ)) (k : FinPairs N ⊕ Fin N),
        Sum.elim (fun p => ω.1 (finPairsSplit N (Sum.inl p)))
          (fun i => ω.1 (finPairsSplit N (Sum.inr i))) k = ω.1 (finPairsSplit N k) :=
      fun ω k => by rcases k with p | i <;> rfl
    simp only [hel]
    have := integral_prod_mul (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      (ν := skVectorGaussLaw β q) (fun g => g (finPairsSplit N k)) (fun y => y u)
    unfold skVectorConcreteLaw
    rw [this, integral_pi_gaussianReal_coord, zero_mul]
  · intro p
    have := integral_prod_mul (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      (ν := skVectorGaussLaw β q) (fun g => g (finPairsSplit N (Sum.inl p))) (fun _ => (1 : ℝ))
    simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at this
    unfold skVectorConcreteLaw
    rw [this, integral_pi_gaussianReal_coord]
  · intro i
    have := integral_prod_mul (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      (ν := skVectorGaussLaw β q) (fun g => g (finPairsSplit N (Sum.inr i))) (fun _ => (1 : ℝ))
    simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at this
    unfold skVectorConcreteLaw
    rw [this, integral_pi_gaussianReal_coord]
  · intro u
    have := integral_prod_mul (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      (ν := skVectorGaussLaw β q) (fun _ => (1 : ℝ)) (fun y => y u)
    simp only [one_mul, integral_const, probReal_univ, smul_eq_mul] at this
    unfold skVectorConcreteLaw
    rw [this, integral_skVectorGaussLaw_coord]

/-- **Theorem 1.12.1 on the concrete model for a given fixed point.**  If `x = (q, ρ)` lies in the
cone and satisfies `T x = x`, and `β² d² ≤ 1/200`, the overlap bound
`A + B ≤ (8 d⁴ + 2 d²)/(N + 1)` holds for the vector SK model with i.i.d. standard Gaussian
couplings. -/
theorem skVector_theorem_1_12_1_of_fixed {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (hβ' : β ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200) (N : ℕ)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedCone d)
    (hxf : skVectorFixedMap μ ξ β x = x) :
    skVectorCavityAvg μ ξ N β x.2 x.1 (skVectorConcreteLaw N β x.1)
          (fun p ω => ω.1 (finPairsSplit N (Sum.inl p)))
          (fun i ω => ω.1 (finPairsSplit N (Sum.inr i))) (fun u ω => ω.2 u) 1
          (fun σ : Option (Option (Fin 2)) → Fin (N + 1) → α => ∑ u, ∑ v,
            skVectorOverlapDev ξ N 0 1 x.1 u v (fun c => σ (some (some c))) ^ 2) +
        skVectorCavityAvg μ ξ N β x.2 x.1 (skVectorConcreteLaw N β x.1)
          (fun p ω => ω.1 (finPairsSplit N (Sum.inl p)))
          (fun i ω => ω.1 (finPairsSplit N (Sum.inr i))) (fun u ω => ω.2 u) 1
          (fun σ : Option (Option (Fin 2)) → Fin (N + 1) → α => ∑ u, ∑ v,
            skVectorOverlapDev ξ N 0 0 x.2 u v (fun c => σ (some (some c))) ^ 2) ≤
        (8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1) := by
  have hn := skVectorConcreteNoise N β x.1 hx.1
  have hgt : ∀ p : FinPairs (N + 1), Measurable fun ω : (FinPairs (N + 1) → ℝ) × (Fin d → ℝ) =>
      ω.1 p := fun p => by fun_prop
  have hlaw : Measure.map (fun ω : (FinPairs (N + 1) → ℝ) × (Fin d → ℝ) =>
      fun p => ω.1 p) (skVectorConcreteLaw N β x.1) =
      Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1 := by
    unfold skVectorConcreteLaw
    exact Measure.map_fst_prod.trans (by simp)
  have hind : IndepFun (fun (ω : (FinPairs (N + 1) → ℝ) × (Fin d → ℝ)) (p : FinPairs N) =>
      ω.1 (finPairsSplit N (Sum.inl p))) (fun ω u => ω.2 u) (skVectorConcreteLaw N β x.1) :=
    indepFun_prod (X := fun g : FinPairs (N + 1) → ℝ => fun p : FinPairs N =>
      g (finPairsSplit N (Sum.inl p))) (Y := fun y : Fin d → ℝ => y) (by fun_prop) measurable_id
  have hYg : HasGaussianLaw (fun (ω : (FinPairs (N + 1) → ℝ) × (Fin d → ℝ)) (u : Fin d) =>
      ω.2 u) (skVectorConcreteLaw N β x.1) := hn.gaussian.reindex Sum.inr
  obtain ⟨hq, hρ⟩ := (skVectorFixedMap_eq_iff_equations μ ξ hξ hbound β x hYg hn.meas_Y
    hn.mean_Y hn.cov_YY).1 hxf
  exact skVector_theorem_1_12_1 μ ξ hξ hbound β x.2 x.1 hβ' hq hρ hn (fun _ _ => rfl)
    (fun _ _ => rfl) hgt (fun π => map_comp_pairPerm_eq_of_iid hgt hlaw π) hind

/-- **Theorem 1.12.1 on the concrete model** (unconditional apart from the smallness): for
`18 β² d² < 1` and `β² d² ≤ 1/200` the fixed point `(q, ρ)` of Theorem 1.12.2 satisfies the overlap
bound `A + B ≤ (8 d⁴ + 2 d²)/(N + 1)` for the vector SK model with i.i.d. standard Gaussian
couplings. -/
theorem skVector_theorem_1_12_1_concrete {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (hβ : 18 * β ^ 2 * (d : ℝ) ^ 2 < 1)
    (hβ' : β ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200) (N : ℕ) :
    ∃ x ∈ skVectorFixedCone d, skVectorFixedMap μ ξ β x = x ∧
      skVectorCavityAvg μ ξ N β x.2 x.1 (skVectorConcreteLaw N β x.1)
          (fun p ω => ω.1 (finPairsSplit N (Sum.inl p)))
          (fun i ω => ω.1 (finPairsSplit N (Sum.inr i))) (fun u ω => ω.2 u) 1
          (fun σ : Option (Option (Fin 2)) → Fin (N + 1) → α => ∑ u, ∑ v,
            skVectorOverlapDev ξ N 0 1 x.1 u v (fun c => σ (some (some c))) ^ 2) +
        skVectorCavityAvg μ ξ N β x.2 x.1 (skVectorConcreteLaw N β x.1)
          (fun p ω => ω.1 (finPairsSplit N (Sum.inl p)))
          (fun i ω => ω.1 (finPairsSplit N (Sum.inr i))) (fun u ω => ω.2 u) 1
          (fun σ : Option (Option (Fin 2)) → Fin (N + 1) → α => ∑ u, ∑ v,
            skVectorOverlapDev ξ N 0 0 x.2 u v (fun c => σ (some (some c))) ^ 2) ≤
        (8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1) := by
  obtain ⟨x, hx, hxf⟩ := exists_skVectorFixedPoint μ ξ hξ hbound β hβ
  exact ⟨x, hx, hxf, skVector_theorem_1_12_1_of_fixed μ ξ hξ hbound β hβ' N hx hxf⟩

/-- **The fixed point has Frobenius norm at most `d`** (Eq. (1.382)): `‖q‖_F² ≤ d²` and
`‖ρ‖_F² ≤ d²` for every fixed point of `T` in the cone. -/
theorem skVectorFixedPoint_sum_sq_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedCone d)
    (hxf : skVectorFixedMap μ ξ β x = x) :
    (∑ u, ∑ v, x.1 u v ^ 2 ≤ (d : ℝ) ^ 2) ∧ (∑ u, ∑ v, x.2 u v ^ 2 ≤ (d : ℝ) ^ 2) := by
  have hn := skVectorConcreteNoise 0 β x.1 hx.1
  have hYg : HasGaussianLaw (fun (ω : (FinPairs (0 + 1) → ℝ) × (Fin d → ℝ)) (u : Fin d) =>
      ω.2 u) (skVectorConcreteLaw 0 β x.1) := hn.gaussian.reindex Sum.inr
  obtain ⟨hq, hρ⟩ := (skVectorFixedMap_eq_iff_equations μ ξ hξ hbound β x hYg hn.meas_Y
    hn.mean_Y hn.cov_YY).1 hxf
  have := sum_sq_fixedPoint_field_le μ ξ hξ hbound β x.1 x.2 hn.meas_Y hρ hq
  exact ⟨this.1, this.2⟩

end SpinGlasses
