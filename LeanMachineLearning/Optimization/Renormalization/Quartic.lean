/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Gaussian
public import LeanMachineLearning.Optimization.Renormalization.Perturbation

/-!
# Symmetric quartic Gaussian perturbations

This file represents a quartic interaction by a coefficient function on ordered four-tuples plus
an explicit total-symmetry proof.  Positivity is deliberately separate from symmetry: symmetry
drives contraction identities, whereas nonnegativity supplies right-hand normalizability.

The contraction statements use finite sums over tuples and Wick sums over pairings.  Their proofs
must derive numerical multiplicities from pairing orbits and finite-sum equivalences; no proof in
this module should enumerate the fifteen sixth-order or 105 eighth-order pairings by hand.

Deferred proof references:

* L. Isserlis, *On a Formula for the Product-Moment Coefficient of any Order of a Normal Frequency
  Distribution in any Number of Variables*: <https://doi.org/10.1093/biomet/12.1-2.134>.
* The orbit classifications and response formulas are recorded in
  `LML/blueprint/src/chapters/renormalization.tex`, Section "Quartic Gaussian deformation".

Every deferred theorem below includes its own informal proof.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Renormalization

/-- A totally symmetric coefficient tensor with four finite-index slots. -/
structure QuarticCoupling (ι : Type*) where
  /-- Coefficient of an ordered four-tuple. -/
  coeff : (Fin 4 → ι) → ℝ
  /-- Coefficients are invariant under every permutation of the four slots. -/
  coeff_perm : ∀ (σ : Equiv.Perm (Fin 4)) (q : Fin 4 → ι), coeff (q ∘ σ) = coeff q

namespace QuarticCoupling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quartic potential with the conventional `1 / 4!` symmetry factor. -/
def potential (A : QuarticCoupling ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  (((4 : ℕ).factorial : ℝ)⁻¹) * ∑ q : Fin 4 → ι, A.coeff q * ∏ r, z (q r)

/-- Pointwise nonnegativity of a quartic potential.  This is not implied by total symmetry. -/
def Nonnegative (A : QuarticCoupling ι) : Prop :=
  ∀ z, 0 ≤ A.potential z

/-- A product of coordinates, allowing repetitions through the index map. -/
def coordinateProduct {n : ℕ} (index : Fin n → ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  ∏ r, z (index r)

/-- Vacuum contraction appearing in the first-order relative partition function. -/
def quarticContraction (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) : ℝ :=
  ∑ q : Fin 4 → ι,
    A.coeff q * K (q 0) (q 1) * K (q 2) (q 3)

/-- Contraction with two external coordinate legs. -/
def twoPointContraction (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  ∑ q : Fin 4 → ι,
    A.coeff q * K i (q 0) * K j (q 1) * K (q 2) (q 3)

/-- Fully connected contraction with four external coordinate legs. -/
def fourPointContraction (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (index : Fin 4 → ι) : ℝ :=
  ∑ q : Fin 4 → ι, A.coeff q * ∏ r, K (index r) (q r)

omit [DecidableEq ι] in
/-- The quartic potential is continuous.

Informal proof: coordinate evaluation is continuous on Euclidean space; finite products, scalar
multiples, and finite sums of continuous real-valued functions remain continuous. -/
theorem continuous_potential (A : QuarticCoupling ι) : Continuous A.potential := by
  unfold potential
  fun_prop

omit [DecidableEq ι] in
/-- A quartic potential is invariant under the global sign flip. -/
theorem potential_neg (A : QuarticCoupling ι) (z : EuclideanSpace ℝ ι) :
    A.potential (-z) = A.potential z := by
  unfold potential
  congr 1
  exact Finset.sum_congr rfl (fun q _hq ↦ by
    congr 1
    rw [Fin.prod_univ_four, Fin.prod_univ_four]
    simp)

/-- Nonnegative quartic potentials are normalizable at every nonnegative coupling.

Informal proof: `continuous_potential` supplies measurability, and `A.Nonnegative` gives the
pointwise bound `exp (-ε V_A) ≤ 1` for `ε ≥ 0`.  Apply
`Renormalization.normalizable_of_nonnegative` to the Gaussian probability measure. -/
theorem normalizable (A : QuarticCoupling ι) {K : Matrix ι ι ℝ}
    (hA : A.Nonnegative) {ε : ℝ} (hε : 0 ≤ ε) :
    Normalizable (multivariateGaussian 0 K) A.potential ε :=
  normalizable_of_nonnegative A.continuous_potential.aestronglyMeasurable hA hε

/-- Every coordinate remains centered under an even quartic deformation of a centered Gaussian. -/
theorem integral_coordinate_deform_eq_zero (A : QuarticCoupling ι)
    (K : Matrix ι ι ℝ) (ε : ℝ) (i : ι) :
    ∫ z, z i ∂deform (multivariateGaussian 0 K) A.potential ε = 0 := by
  rw [integral_deform]
  let F : EuclideanSpace ℝ ι → ℝ := fun z ↦
    (Real.exp (-ε * A.potential z) /
      partitionFunction (multivariateGaussian 0 K) A.potential ε) * z i
  have hF : AEStronglyMeasurable F (multivariateGaussian 0 K) := by
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    exact
      (((Real.continuous_exp.comp (continuous_const.mul A.continuous_potential)).div_const _).mul
        ((continuous_apply i).comp
          (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous))
  have hodd : ∀ z, F (-z) = -F z := by
    intro z
    simp [F, A.potential_neg]
  simpa only [F, smul_eq_mul] using
    (integral_eq_zero_of_odd_of_aestronglyMeasurable
      (multivariateGaussian 0 K) hF hodd)

omit [DecidableEq ι] in
/-- Square-integrability of a nonnegative quartic potential implies integrability. -/
theorem integrable_potential_of_sq (A : QuarticCoupling ι) (hA : A.Nonnegative)
    {μ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasure μ]
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) μ) : Integrable A.potential μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hV2)
    A.continuous_potential.aestronglyMeasurable ?_
  filter_upwards with z
  dsimp
  rw [abs_of_nonneg (hA z)]
  nlinarith [sq_nonneg (A.potential z - (1 / 2 : ℝ))]

/-! ## Pairing-orbit moment formulae -/

/-- Expanding the quartic potential inside a Gaussian integral.

Informal proof: unfold `coordinateProduct` and `potential`, distribute multiplication over the
finite sum over quartic labels, and use finite linearity of the Bochner integral.  The required
integrability statements are polynomial-moment bounds for a finite-dimensional Gaussian. -/
theorem integrable_coordinateProduct_mul_potential
    {n : ℕ} (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (index : Fin n → ι) :
    Integrable (fun z : EuclideanSpace ℝ ι ↦ coordinateProduct index z * A.potential z)
      (multivariateGaussian 0 K) := by
  let μ : Measure (EuclideanSpace ℝ ι) := multivariateGaussian 0 K
  have hmono : ∀ q : Fin 4 → ι, Integrable (fun z : EuclideanSpace ℝ ι ↦
      coordinateProduct index z * ∏ r : Fin 4, z (q r)) μ := fun q ↦ by
    simpa [coordinateProduct, Fintype.prod_sum_type] using
      (integrable_finset_prod_gaussian_coordinate (μ := μ)
        (s := (Finset.univ : Finset (Sum (Fin n) (Fin 4)))) (coord := Sum.elim index q))
  have hsum : Integrable (fun z : EuclideanSpace ℝ ι ↦
      ∑ q : Fin 4 → ι, A.coeff q *
        (coordinateProduct index z * ∏ r : Fin 4, z (q r))) μ :=
    integrable_finsetSum Finset.univ (fun q _hq ↦ (hmono q).const_mul (A.coeff q))
  have hfun : (fun z : EuclideanSpace ℝ ι ↦ coordinateProduct index z * A.potential z) =
      fun z ↦ (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          (coordinateProduct index z * ∏ r : Fin 4, z (q r)) := by
    funext z
    unfold potential
    calc
      coordinateProduct index z *
          ((((4 : ℕ).factorial : ℝ)⁻¹) *
            ∑ q : Fin 4 → ι, A.coeff q * ∏ r : Fin 4, z (q r)) =
          (((4 : ℕ).factorial : ℝ)⁻¹) *
            (coordinateProduct index z *
              ∑ q : Fin 4 → ι, A.coeff q * ∏ r : Fin 4, z (q r)) := by ring
      _ = (((4 : ℕ).factorial : ℝ)⁻¹) *
            ∑ q : Fin 4 → ι,
              coordinateProduct index z * (A.coeff q * ∏ r : Fin 4, z (q r)) := by
        rw [Finset.mul_sum]
      _ = (((4 : ℕ).factorial : ℝ)⁻¹) *
            ∑ q : Fin 4 → ι, A.coeff q *
              (coordinateProduct index z * ∏ r : Fin 4, z (q r)) := by
        congr 1
        exact Finset.sum_congr rfl (fun q _hq ↦ by ring)
  rw [hfun]
  exact hsum.const_mul _

theorem integral_coordinateProduct_mul_potential_eq_sum_integral
    {n : ℕ} (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (index : Fin n → ι) :
    ∫ z, coordinateProduct index z * A.potential z ∂multivariateGaussian 0 K =
      (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          ∫ z, coordinateProduct index z * ∏ r, z (q r) ∂multivariateGaussian 0 K := by
  let μ : Measure (EuclideanSpace ℝ ι) := multivariateGaussian 0 K
  let c : ℝ := (((4 : ℕ).factorial : ℝ)⁻¹)
  let monomial (q : Fin 4 → ι) (z : EuclideanSpace ℝ ι) : ℝ :=
    coordinateProduct index z * ∏ r, z (q r)
  have h_integrable_monomial : ∀ q : Fin 4 → ι, Integrable (monomial q) μ := fun q => by
    simpa [monomial, coordinateProduct, Fintype.prod_sum_type] using
      (integrable_finset_prod_gaussian_coordinate (μ := μ)
        (s := (Finset.univ : Finset (Sum (Fin n) (Fin 4)))) (coord := Sum.elim index q))
  have h_integrable_summand :
      ∀ q ∈ (Finset.univ : Finset (Fin 4 → ι)),
        Integrable (fun z : EuclideanSpace ℝ ι ↦ A.coeff q * monomial q z) μ :=
    fun q _ => (h_integrable_monomial q).const_mul _
  calc
    ∫ z, coordinateProduct index z * A.potential z ∂multivariateGaussian 0 K =
        ∫ z, c * ∑ q : Fin 4 → ι, A.coeff q * monomial q z ∂μ := by
      congr with z
      simp [c, monomial, coordinateProduct, potential, Finset.mul_sum]
      ring_nf
    _ = c * ∫ z, ∑ q : Fin 4 → ι, A.coeff q * monomial q z ∂μ := by
      rw [MeasureTheory.integral_const_mul]
    _ = c * ∑ q : Fin 4 → ι, ∫ z, A.coeff q * monomial q z ∂μ := by
      rwa [MeasureTheory.integral_finsetSum]
    _ = (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          ∫ z, coordinateProduct index z * ∏ r, z (q r) ∂multivariateGaussian 0 K := by
      simp [μ, c, monomial, MeasureTheory.integral_const_mul]

/-! ### Reindexing pairing sums along equivalences -/

private lemma mapEquiv_isPairing_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {s : Finset α} (P : Finpartition s) :
    (∀ B ∈ P.parts, B.card = 2) ↔
      (∀ B ∈ (Finpartition.mapEquiv e P).parts, B.card = 2) := by
  rw [Finpartition.parts_mapEquiv]
  constructor
  · intro hP B hB
    rcases Finset.mem_map.mp hB with ⟨C, hC, rfl⟩
    exact (Finset.card_map e.toEmbedding).trans (hP C hC)
  · intro hQ B hB
    simpa [Finset.card_map] using
      hQ (B.map e.toEmbedding) (Finset.mem_map.mpr ⟨B, hB, rfl⟩)

private def pairingMapEquivEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Finset α) :
    Finpartition.Pairing s ≃ Finpartition.Pairing (s.map e.toEmbedding) :=
  (Finpartition.mapEquivEquiv e s).subtypeEquiv (mapEquiv_isPairing_iff e)

private lemma pairingSum_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R : Type*} [CommSemiring R] (e : α ≃ β) (f : Finset β → R) (s : Finset α) :
    Finpartition.pairingSum f (s.map e.toEmbedding) =
      Finpartition.pairingSum (fun B : Finset α ↦ f (B.map e.toEmbedding)) s := by
  unfold Finpartition.pairingSum
  exact (((pairingMapEquivEquiv e s).sum_comp
    (fun Q : Finpartition.Pairing (s.map e.toEmbedding) ↦ Q.blockProduct f)).symm.trans
    (Finset.sum_congr rfl (fun P _hP ↦ Finpartition.blockProduct_mapEquiv e P.1 f)))

private lemma pairWeight_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : β → β → ℝ) (B : Finset α) :
    Renormalization.pairWeight C (B.map e.toEmbedding) =
      Renormalization.pairWeight (fun a b : α ↦ C (e a) (e b)) B := by
  unfold Renormalization.pairWeight
  congr 1
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl (fun a _ha ↦ by
    rw [← Finset.map_erase e.toEmbedding B a, Finset.sum_map]
    simp [Equiv.toEmbedding_apply])

private lemma wick_univ_perm {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (C : β → β → ℝ) :
    Renormalization.wick (fun a b : α ↦ C (e a) (e b)) (Finset.univ : Finset α) =
      Renormalization.wick C (Finset.univ : Finset β) := by
  unfold Renormalization.wick
  rw [← Finset.map_univ_equiv e, pairingSum_map]
  simp [pairWeight_map]

/-- Arbitrary-finite-position version of the coordinate Wick theorem.

Informal proof: choose an equivalence `e : Fin (Fintype.card α) ≃ α`.  Apply
`integral_prod_multivariateGaussian_centered_eq_wick` from `Gaussian.lean` to the finite sequence
`index ∘ e`.  The left hand side is transported to the `α`-indexed joint moment by
`jointMoment_perm`; the right hand side is transported along the same equivalence by reindexing
`Finpartition.Pairing` in the definition of `wick`.  This is exactly Isserlis' theorem for an
arbitrary finite set of positions; see L. Isserlis, Biometrika 12 (1918), 134--139,
<https://doi.org/10.1093/biomet/12.1-2.134>. -/
theorem integral_prod_multivariateGaussian_centered_eq_wick_fintype
    {κ α : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (m : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (hS : S.PosSemidef)
    (index : α → κ) :
    jointMoment (multivariateGaussian m S)
        (fun a z ↦ z (index a) - m (index a)) =
      wick (fun a b ↦ S (index a) (index b)) Finset.univ := by
  let e := Fintype.equivFin α
  exact ((jointMoment_perm (μ := multivariateGaussian m S) e
    (X := fun a z ↦ z (index a) - m (index a))).symm.trans
    (integral_prod_multivariateGaussian_centered_eq_wick (m := m) (S := S) (hS := hS)
      (fun r : Fin (Fintype.card α) ↦ index (e.symm r)))).trans
    (wick_univ_perm e.symm (fun a b : α ↦ S (index a) (index b)))

/-- A finite product of coordinates of a centered multivariate Gaussian is its Wick sum. -/
theorem integral_coordinateProduct_eq_wick {n : ℕ} (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (index : Fin n → ι) :
    ∫ z, coordinateProduct index z ∂multivariateGaussian 0 K =
      wick (fun r s : Fin n ↦ K (index r) (index s)) Finset.univ := by
  calc
    (∫ z, coordinateProduct index z ∂multivariateGaussian 0 K) =
        jointMoment (multivariateGaussian 0 K)
          (fun r : Fin n ↦ fun z ↦ z (index r) -
            (0 : EuclideanSpace ℝ ι) (index r)) := by
      simp [jointMoment, blockMoment, coordinateProduct]
    _ = wick (fun r s : Fin n ↦ K (index r) (index s)) Finset.univ :=
      integral_prod_multivariateGaussian_centered_eq_wick_fintype
        (m := (0 : EuclideanSpace ℝ ι)) (S := K) hK index

omit [Fintype ι] [DecidableEq ι] in
-- Notation conversion: a coordinate product times the quartic monomial `∏ r, z (q r)` is the
-- zero-centered joint moment of the coordinate family `Sum.elim index q` indexed by the disjoint
-- union `Sum (Fin n) (Fin 4)`.  This puts integrals of the shape needed by the centered Wick
-- theorem, and holds for any measure (no Gaussian hypothesis is required).
private lemma integral_coordinateProduct_mul_prod_eq_jointMoment
    {n : ℕ} (μ : Measure (EuclideanSpace ℝ ι))
    (index : Fin n → ι) (q : Fin 4 → ι) :
    ∫ z, coordinateProduct index z * ∏ r, z (q r) ∂μ =
      jointMoment μ
        (fun a : Sum (Fin n) (Fin 4) ↦ fun z ↦
          z (Sum.elim index q a) - (0 : EuclideanSpace ℝ ι) (Sum.elim index q a)) := by
  simp [jointMoment, blockMoment, coordinateProduct, Fintype.prod_sum_type]

/-- Wick evaluation of the monomial obtained by adjoining a quartic tuple to external
coordinates.

Informal proof: identify
`(coordinateProduct index z) * (∏ r, z (q r))` with the product over the disjoint union
`Sum (Fin n) (Fin 4)` of the coordinate family `Sum.elim index q`.  Then apply the centered
multivariate Wick theorem/Isserlis formula to the Gaussian `multivariateGaussian 0 K`; its
covariance entries are `K`, by `covariance_eval_multivariateGaussian hK`. -/
theorem integral_coordinateProduct_mul_quarticMonomial_eq_wick
    {n : ℕ} (K : Matrix ι ι ℝ) (hK : K.PosSemidef)
    (index : Fin n → ι) (q : Fin 4 → ι) :
    ∫ z, coordinateProduct index z * ∏ r, z (q r) ∂multivariateGaussian 0 K =
      wick (fun r s : Sum (Fin n) (Fin 4) ↦
        K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ :=
  (integral_coordinateProduct_mul_prod_eq_jointMoment (μ := multivariateGaussian 0 K) index q).trans
    (integral_prod_multivariateGaussian_centered_eq_wick_fintype
      (m := (0 : EuclideanSpace ℝ ι)) (S := K) hK (Sum.elim index q))

/-- A coordinate product times the quartic potential reduces to one Wick sum per coefficient
tuple.

Informal proof: distribute the finite tuple sum in `potential` through the integral.  For each
tuple `q`, apply the multivariate-coordinate Wick theorem to the family indexed by
`Sum (Fin n) (Fin 4)`, with the external indices on the left and `q` on the right. -/
theorem integral_coordinateProduct_mul_potential_eq_sum_wick
    {n : ℕ} (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (hK : K.PosSemidef)
    (index : Fin n → ι) :
    ∫ z, coordinateProduct index z * A.potential z ∂multivariateGaussian 0 K =
      (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          wick (fun r s : Sum (Fin n) (Fin 4) ↦
            K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ :=
  (integral_coordinateProduct_mul_potential_eq_sum_integral A K index).trans (by
    simp [integral_coordinateProduct_mul_quarticMonomial_eq_wick K hK index])

/-- Vacuum version of the quartic Wick reduction, with the empty external product removed
and the indexing type `Sum (Fin 0) (Fin 4)` transported to `Fin 4`.

Informal proof: apply `integral_coordinateProduct_mul_potential_eq_sum_wick` with `n = 0` and the
unique empty index map.  The factor `coordinateProduct` is an empty product, hence `1`.  On the
right-hand side, the equivalence `Sum (Fin 0) (Fin 4) ≃ Fin 4` identifies the Wick sum over the
coproduct with the Wick sum over the quartic slots; this is exactly the reindexing lemma
`wick_univ_perm` proved above. -/
private lemma integral_potential_eq_sum_wick_fin_four
    (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (hK : K.PosSemidef) :
    ∫ z, A.potential z ∂multivariateGaussian 0 K =
      (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          wick (fun r s : Fin 4 ↦ K (q r) (q s)) Finset.univ := by
  let index : Fin 0 → ι := Fin.elim0
  let e : Sum (Fin 0) (Fin 4) ≃ Fin 4 :=
    (Equiv.sumComm (Fin 0) (Fin 4)).trans (Equiv.sumEmpty (Fin 4) (Fin 0))
  have hstep : ∀ q : Fin 4 → ι,
      wick (fun r s : Sum (Fin 0) (Fin 4) ↦
        K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ =
        wick (fun r s : Fin 4 ↦ K (q r) (q s)) Finset.univ := fun q => by
    have hfun' : Sum.elim index q = q ∘ e := by
      funext a
      rcases a with r | r
      · exact Fin.elim0 r
      · rfl
    simpa [hfun'] using wick_univ_perm e (fun r s : Fin 4 ↦ K (q r) (q s))
  simp_rw [← hstep, ← integral_coordinateProduct_mul_potential_eq_sum_wick A K hK (index := index)]
  simp [coordinateProduct]

-- Isserlis' fourth-moment formula on four slots: the Wick sum of a symmetric covariance
-- `C : Fin 4 → Fin 4 → ℝ` is the sum over the three pairings `01|23`, `02|13`, `03|12`.
-- This is the `Fin 4` instance of the general recurrence `wick_erase` specialized to a
-- symmetric covariance.  It is generic in `C` so that it applies to `C r s = K (q r) (q s)`
-- for every quartic tuple `q` in the contraction proofs below.
private lemma wick_quartic_slots (C : Fin 4 → Fin 4 → ℝ) (hC : ∀ r s, C r s = C s r) :
    wick C Finset.univ = C 0 1 * C 2 3 + C 0 2 * C 1 3 + C 0 3 * C 1 2 := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  exact wick_four C hC (a := (0 : Fin 4)) (b := (1 : Fin 4))
    (c := (2 : Fin 4)) (d := (3 : Fin 4))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Pull a coefficient-weighted tuple sum back along a slot permutation `σ`:
-- `∑ q, A.coeff q * g (q ∘ σ) = ∑ q, A.coeff q * g q`.  This packages the two ingredients used
-- by both the `(1 2)` and `(1 3)` reindexings below: total symmetry of `A` (`coeff_perm`) and
-- equivariance of `∑` under `Equiv.arrowCongr`.
omit [DecidableEq ι] in
private lemma coeff_sum_perm (A : QuarticCoupling ι) (σ : Equiv.Perm (Fin 4))
    (g : (Fin 4 → ι) → ℝ) :
    (∑ q : Fin 4 → ι, A.coeff q * g (q ∘ σ)) = ∑ q : Fin 4 → ι, A.coeff q * g q := by
  simpa [A.coeff_perm, Equiv.arrowCongr, Equiv.symm_symm] using
    (Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl ι)) (fun q : Fin 4 → ι ↦ A.coeff q * g q))

omit [DecidableEq ι] in
/-- Every ordering of the four vertex legs gives the same two-point contraction. -/
private lemma twoPointContraction_sum_perm (A : QuarticCoupling ι)
    (K : Matrix ι ι ℝ) (i j : ι) (σ : Equiv.Perm (Fin 4)) :
    (∑ q : Fin 4 → ι, A.coeff q *
      (K i (q (σ 0)) * (K j (q (σ 1)) * K (q (σ 2)) (q (σ 3))))) =
        A.twoPointContraction K i j := by
  simpa [twoPointContraction, Function.comp_apply, mul_assoc] using
    coeff_sum_perm A σ
      (fun q : Fin 4 → ι ↦ K i (q 0) * (K j (q 1) * K (q 2) (q 3)))

omit [DecidableEq ι] in
/-- The quartic Wick sum collapses to three copies of the vacuum contraction.

Informal proof: for each ordered tuple `q`, Isserlis' fourth-moment formula gives the three pairings
`01|23`, `02|13`, and `03|12`.  The first sum is exactly `A.quarticContraction K`.  The other two
are reindexed by the transpositions of the four slots sending their pairings to `01|23`; the
coefficient tensor is invariant under all such permutations by `A.coeff_perm`. -/
private lemma quartic_wick_sum_eq_three_quarticContraction
    (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (hKsymm : ∀ i j, K i j = K j i) :
    (∑ q : Fin 4 → ι, A.coeff q *
      wick (fun r s : Fin 4 ↦ K (q r) (q s)) Finset.univ) =
        3 * A.quarticContraction K := by
  classical
  -- The second and third pairing sums are reindexed to the first by the transpositions
  -- `(1 2)` and `(1 3)` of the four slots, using `A.coeff_perm`.
  have hT2 :
      (∑ q : Fin 4 → ι, A.coeff q * (K (q 0) (q 2) * K (q 1) (q 3))) =
        (∑ q : Fin 4 → ι, A.coeff q * (K (q 0) (q 1) * K (q 2) (q 3))) := by
    let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 2
    have hσ : ∀ q : Fin 4 → ι,
        K (q (σ 0)) (q (σ 1)) * K (q (σ 2)) (q (σ 3)) =
          K (q 0) (q 2) * K (q 1) (q 3) := by
      intro q
      simp [σ, Equiv.swap_apply_of_ne_of_ne]
    simpa [hσ] using coeff_sum_perm A σ (fun q : Fin 4 → ι ↦ K (q 0) (q 1) * K (q 2) (q 3))
  have hT3 :
      (∑ q : Fin 4 → ι, A.coeff q * (K (q 0) (q 3) * K (q 1) (q 2))) =
        (∑ q : Fin 4 → ι, A.coeff q * (K (q 0) (q 1) * K (q 2) (q 3))) := by
    let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 3
    have hσ : ∀ q : Fin 4 → ι,
        K (q (σ 0)) (q (σ 1)) * K (q (σ 2)) (q (σ 3)) =
          K (q 0) (q 3) * K (q 1) (q 2) := by
      intro q
      simp [σ, Equiv.swap_apply_of_ne_of_ne, hKsymm (q 2) (q 1)]
    simpa [hσ] using coeff_sum_perm A σ (fun q : Fin 4 → ι ↦ K (q 0) (q 1) * K (q 2) (q 3))
  calc
    (∑ q : Fin 4 → ι, A.coeff q *
        wick (fun r s : Fin 4 ↦ K (q r) (q s)) Finset.univ)
        = ∑ q : Fin 4 → ι, A.coeff q *
            (K (q 0) (q 1) * K (q 2) (q 3) + K (q 0) (q 2) * K (q 1) (q 3) +
              K (q 0) (q 3) * K (q 1) (q 2)) := by
            exact Finset.sum_congr rfl (fun q _hq => by
              rw [wick_quartic_slots (fun r s ↦ K (q r) (q s)) (fun r s ↦ hKsymm (q r) (q s))])
    _ = 3 * (∑ q : Fin 4 → ι, A.coeff q * (K (q 0) (q 1) * K (q 2) (q 3))) := by
            simp [Finset.sum_add_distrib, mul_add, hT2, hT3]
            ring
    _ = 3 * A.quarticContraction K := by
            simp [quarticContraction, mul_assoc]

/-- Gaussian expectation of a symmetric quartic potential.

Informal proof: specialize the preceding Wick reduction to no external legs.  The three pairings
of four slots form one orbit under slot permutations; symmetry of `A` identifies their sums, so
the multiplicity `3 / 4! = 1 / 8` is derived from the orbit equivalence. -/
theorem integral_potential (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) :
    ∫ z, A.potential z ∂multivariateGaussian 0 K =
      (1 / 8 : ℝ) * A.quarticContraction K := by
  rw [integral_potential_eq_sum_wick_fin_four A K hK,
    quartic_wick_sum_eq_three_quarticContraction A K (fun i j => (hK.isHermitian.apply j i))]
  ring_nf

omit [DecidableEq ι] in
/-- Sixth-order Wick orbit collapse for two external legs and one symmetric quartic vertex.

Informal proof: apply `wick_erase` to the first external leg in
`Sum (Fin 2) (Fin 4)`.  The partner is either the second external leg, leaving the three quartic
pairings already computed by `wick_quartic_slots`, or one of the four quartic legs.  In the latter
case the second external leg pairs with one of the three remaining quartic legs, and the last two
quartic legs pair with each other, giving `4 * 3 = 12` pairings.  Reindex the four quartic slots by
permutations and use `A.coeff_perm` (plus `hKsymm`) to identify the three internal-pairing sums
with `A.quarticContraction K` and all twelve mixed sums with
`A.twoPointContraction K i j`.  This is the sixth-order Isserlis orbit count described in
`docs/Renormalization.md`, equation `eq:second-moment-interaction`, and in Isserlis' theorem
<https://doi.org/10.1093/biomet/12.1-2.134>. -/
private lemma two_external_wick_sum_eq_three_twelve_contractions
    (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (hKsymm : ∀ i j, K i j = K j i)
    (i j : ι) :
    (∑ q : Fin 4 → ι, A.coeff q *
      wick (fun r s : Sum (Fin 2) (Fin 4) ↦
        K (Sum.elim (fun t : Fin 2 ↦ if t = 0 then i else j) q r)
          (Sum.elim (fun t : Fin 2 ↦ if t = 0 then i else j) q s)) Finset.univ) =
        3 * (K i j * A.quarticContraction K) +
          12 * A.twoPointContraction K i j := by
  classical
  let ext : Fin 2 → ι := fun t ↦ if t = 0 then i else j
  have hC : ∀ q : Fin 4 → ι, ∀ r s : Sum (Fin 2) (Fin 4),
      K (Sum.elim ext q r) (Sum.elim ext q s) =
        K (Sum.elim ext q s) (Sum.elim ext q r) := by
    intro q r s
    exact hKsymm _ _
  -- First genuine subgoal: enumerate the fifteen sixth-order Wick pairings.  This is obtained
  -- by applying `wick_erase` to `Sum.inl 0`; the residual four-quartic term is evaluated by
  -- `wick_quartic_slots`, while each mixed residual is evaluated by a second `wick_erase`.
  have hWick : ∀ q : Fin 4 → ι,
      wick (fun r s : Sum (Fin 2) (Fin 4) ↦
        K (Sum.elim ext q r) (Sum.elim ext q s)) Finset.univ =
        K i j * (K (q 0) (q 1) * K (q 2) (q 3) +
          K (q 0) (q 2) * K (q 1) (q 3) +
          K (q 0) (q 3) * K (q 1) (q 2)) +
        K i (q 0) * (K j (q 1) * K (q 2) (q 3) +
          K j (q 2) * K (q 1) (q 3) +
          K j (q 3) * K (q 1) (q 2)) +
        K i (q 1) * (K j (q 0) * K (q 2) (q 3) +
          K j (q 2) * K (q 0) (q 3) +
          K j (q 3) * K (q 0) (q 2)) +
        K i (q 2) * (K j (q 0) * K (q 1) (q 3) +
          K j (q 1) * K (q 0) (q 3) +
          K j (q 3) * K (q 0) (q 1)) +
        K i (q 3) * (K j (q 0) * K (q 1) (q 2) +
          K j (q 1) * K (q 0) (q 2) +
          K j (q 2) * K (q 0) (q 1)) := by
    intro q
    -- Informal proof: use `wick_erase _ (hC q) Finset.univ` at `Sum.inl 0`, then simplify the
    -- five possible partners (`Sum.inl 1` and `Sum.inr k`, `k : Fin 4`).
    -- The two-element residual Wick sums are closed by `wick_empty`/`pairWeight_pair` through
    -- `wick_erase`; the four-quartic residual is `wick_quartic_slots`.
    let C : Sum (Fin 2) (Fin 4) → Sum (Fin 2) (Fin 4) → ℝ := fun r s ↦
      K (Sum.elim ext q r) (Sum.elim ext q s)
    let e₀ : Sum (Fin 2) (Fin 4) := Sum.inl 0
    let e₁ : Sum (Fin 2) (Fin 4) := Sum.inl 1
    let v₀ : Sum (Fin 2) (Fin 4) := Sum.inr 0
    let v₁ : Sum (Fin 2) (Fin 4) := Sum.inr 1
    let v₂ : Sum (Fin 2) (Fin 4) := Sum.inr 2
    let v₃ : Sum (Fin 2) (Fin 4) := Sum.inr 3
    have hresE : wick C ({v₀, v₁, v₂, v₃} : Finset _) =
        K (q 0) (q 1) * K (q 2) (q 3) +
          K (q 0) (q 2) * K (q 1) (q 3) +
          K (q 0) (q 3) * K (q 1) (q 2) := by
      simpa [C, v₀, v₁, v₂, v₃] using
        wick_four C (hC q) (a := v₀) (b := v₁) (c := v₂) (d := v₃)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hres0 : wick C ({e₁, v₁, v₂, v₃} : Finset _) =
        K j (q 1) * K (q 2) (q 3) + K j (q 2) * K (q 1) (q 3) +
          K j (q 3) * K (q 1) (q 2) := by
      simpa [C, ext, e₁, v₁, v₂, v₃] using
        wick_four C (hC q) (a := e₁) (b := v₁) (c := v₂) (d := v₃)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hres1 : wick C ({e₁, v₀, v₂, v₃} : Finset _) =
        K j (q 0) * K (q 2) (q 3) + K j (q 2) * K (q 0) (q 3) +
          K j (q 3) * K (q 0) (q 2) := by
      simpa [C, ext, e₁, v₀, v₂, v₃] using
        wick_four C (hC q) (a := e₁) (b := v₀) (c := v₂) (d := v₃)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hres2 : wick C ({e₁, v₀, v₁, v₃} : Finset _) =
        K j (q 0) * K (q 1) (q 3) + K j (q 1) * K (q 0) (q 3) +
          K j (q 3) * K (q 0) (q 1) := by
      simpa [C, ext, e₁, v₀, v₁, v₃] using
        wick_four C (hC q) (a := e₁) (b := v₀) (c := v₁) (d := v₃)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hres3 : wick C ({e₁, v₀, v₁, v₂} : Finset _) =
        K j (q 0) * K (q 1) (q 2) + K j (q 1) * K (q 0) (q 2) +
          K j (q 2) * K (q 0) (q 1) := by
      simpa [C, ext, e₁, v₀, v₁, v₂] using
        wick_four C (hC q) (a := e₁) (b := v₀) (c := v₁) (d := v₂)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have herase : (Finset.univ : Finset (Sum (Fin 2) (Fin 4))).erase e₀ =
        {e₁, v₀, v₁, v₂, v₃} := by decide
    rw [show (fun r s : Sum (Fin 2) (Fin 4) ↦
      K (Sum.elim ext q r) (Sum.elim ext q s)) = C by rfl,
      wick_erase C (hC q) Finset.univ
        (show e₀ ∈ (Finset.univ : Finset (Sum (Fin 2) (Fin 4))) by simp), herase]
    rw [Finset.sum_insert
        (by decide : e₁ ∉ ({v₀, v₁, v₂, v₃} : Finset (Sum (Fin 2) (Fin 4)))),
      Finset.sum_insert
        (by decide : v₀ ∉ ({v₁, v₂, v₃} : Finset (Sum (Fin 2) (Fin 4)))),
      Finset.sum_insert
        (by decide : v₁ ∉ ({v₂, v₃} : Finset (Sum (Fin 2) (Fin 4)))),
      Finset.sum_insert
        (by decide : v₂ ∉ ({v₃} : Finset (Sum (Fin 2) (Fin 4)))),
      Finset.sum_singleton]
    rw [show ({e₁, v₀, v₁, v₂, v₃} : Finset _).erase e₁ = {v₀, v₁, v₂, v₃}
        by decide,
      show ({e₁, v₀, v₁, v₂, v₃} : Finset _).erase v₀ = {e₁, v₁, v₂, v₃}
        by decide,
      show ({e₁, v₀, v₁, v₂, v₃} : Finset _).erase v₁ = {e₁, v₀, v₂, v₃}
        by decide,
      show ({e₁, v₀, v₁, v₂, v₃} : Finset _).erase v₂ = {e₁, v₀, v₁, v₃}
        by decide,
      show ({e₁, v₀, v₁, v₂, v₃} : Finset _).erase v₃ = {e₁, v₀, v₁, v₂}
        by decide,
      hresE, hres0, hres1, hres2, hres3]
    simp [C, ext, e₀, e₁, v₀, v₁, v₂, v₃]
    ring
  have hVac :
      (∑ q : Fin 4 → ι, A.coeff q *
        (K i j * (K (q 0) (q 1) * K (q 2) (q 3) +
          K (q 0) (q 2) * K (q 1) (q 3) +
          K (q 0) (q 3) * K (q 1) (q 2)))) =
        3 * (K i j * A.quarticContraction K) := by
    -- This is the already-proved vacuum orbit collapse, multiplied by the external covariance
    -- `K i j`; formally, rewrite the parenthesized quartic Wick expansion with
    -- `wick_quartic_slots`, apply `quartic_wick_sum_eq_three_quarticContraction`, and normalize.
    have hquartic : ∀ q : Fin 4 → ι,
        wick (fun r s : Fin 4 ↦ K (q r) (q s)) Finset.univ =
          K (q 0) (q 1) * K (q 2) (q 3) + K (q 0) (q 2) * K (q 1) (q 3) +
            K (q 0) (q 3) * K (q 1) (q 2) := fun q ↦
      wick_quartic_slots (fun r s : Fin 4 ↦ K (q r) (q s))
        (fun r s ↦ hKsymm (q r) (q s))
    calc
      _ = K i j * (∑ q : Fin 4 → ι, A.coeff q *
          wick (fun r s : Fin 4 ↦ K (q r) (q s)) Finset.univ) := by
        simp_rw [hquartic]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _hq ↦ by ring)
      _ = K i j * (3 * A.quarticContraction K) := by
        rw [quartic_wick_sum_eq_three_quarticContraction A K hKsymm]
      _ = 3 * (K i j * A.quarticContraction K) := by ring
  have hMixed :
      (∑ q : Fin 4 → ι, A.coeff q *
        (K i (q 0) * (K j (q 1) * K (q 2) (q 3)) +
          K i (q 0) * (K j (q 2) * K (q 1) (q 3)) +
          K i (q 0) * (K j (q 3) * K (q 1) (q 2)) +
          K i (q 1) * (K j (q 0) * K (q 2) (q 3)) +
          K i (q 1) * (K j (q 2) * K (q 0) (q 3)) +
          K i (q 1) * (K j (q 3) * K (q 0) (q 2)) +
          K i (q 2) * (K j (q 0) * K (q 1) (q 3)) +
          K i (q 2) * (K j (q 1) * K (q 0) (q 3)) +
          K i (q 2) * (K j (q 3) * K (q 0) (q 1)) +
          K i (q 3) * (K j (q 0) * K (q 1) (q 2)) +
          K i (q 3) * (K j (q 1) * K (q 0) (q 2)) +
          K i (q 3) * (K j (q 2) * K (q 0) (q 1)))) =
        12 * A.twoPointContraction K i j := by
    -- Each of these twelve sums is the canonical `twoPointContraction`, after reindexing the
    -- four quartic slots by a suitable permutation.  The reindexing API is `coeff_sum_perm A σ`;
    -- `hKsymm` handles the orientation of the final internal pair.
    let perm (a b c d : Fin 4) (h : Function.Bijective ![a, b, c, d]) :
        Equiv.Perm (Fin 4) := Equiv.ofBijective ![a, b, c, d] h
    let σ01 : Equiv.Perm (Fin 4) := perm 0 1 2 3 (by decide)
    let σ02 : Equiv.Perm (Fin 4) := perm 0 2 1 3 (by decide)
    let σ03 : Equiv.Perm (Fin 4) := perm 0 3 1 2 (by decide)
    let σ10 : Equiv.Perm (Fin 4) := perm 1 0 2 3 (by decide)
    let σ12 : Equiv.Perm (Fin 4) := perm 1 2 0 3 (by decide)
    let σ13 : Equiv.Perm (Fin 4) := perm 1 3 0 2 (by decide)
    let σ20 : Equiv.Perm (Fin 4) := perm 2 0 1 3 (by decide)
    let σ21 : Equiv.Perm (Fin 4) := perm 2 1 0 3 (by decide)
    let σ23 : Equiv.Perm (Fin 4) := perm 2 3 0 1 (by decide)
    let σ30 : Equiv.Perm (Fin 4) := perm 3 0 1 2 (by decide)
    let σ31 : Equiv.Perm (Fin 4) := perm 3 1 0 2 (by decide)
    let σ32 : Equiv.Perm (Fin 4) := perm 3 2 0 1 (by decide)
    have h01 := twoPointContraction_sum_perm A K i j σ01
    have h02 := twoPointContraction_sum_perm A K i j σ02
    have h03 := twoPointContraction_sum_perm A K i j σ03
    have h10 := twoPointContraction_sum_perm A K i j σ10
    have h12 := twoPointContraction_sum_perm A K i j σ12
    have h13 := twoPointContraction_sum_perm A K i j σ13
    have h20 := twoPointContraction_sum_perm A K i j σ20
    have h21 := twoPointContraction_sum_perm A K i j σ21
    have h23 := twoPointContraction_sum_perm A K i j σ23
    have h30 := twoPointContraction_sum_perm A K i j σ30
    have h31 := twoPointContraction_sum_perm A K i j σ31
    have h32 := twoPointContraction_sum_perm A K i j σ32
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Equiv.ofBijective_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, σ01, perm, σ02, σ03, σ10,
      σ12, σ13, σ20, σ21, σ23, σ30, σ31, σ32]
        at h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32
    simp only [mul_add, Finset.sum_add_distrib]
    rw [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32]
    ring
  have hAssemble :
      (∑ q : Fin 4 → ι, A.coeff q *
        wick (fun r s : Sum (Fin 2) (Fin 4) ↦
          K (Sum.elim (fun t : Fin 2 ↦ if t = 0 then i else j) q r)
            (Sum.elim (fun t : Fin 2 ↦ if t = 0 then i else j) q s)) Finset.univ) =
        3 * (K i j * A.quarticContraction K) +
          12 * A.twoPointContraction K i j := by
    -- Rewrite each Wick sum using `hWick`, split the finite sum into the vacuum and mixed
    -- contributions, and finish with `hVac`, `hMixed`, and `ring`.
    change (∑ q : Fin 4 → ι, A.coeff q *
      wick (fun r s : Sum (Fin 2) (Fin 4) ↦
        K (Sum.elim ext q r) (Sum.elim ext q s)) Finset.univ) = _
    simp_rw [hWick]
    simp only [mul_add, Finset.sum_add_distrib] at hVac hMixed ⊢
    linear_combination hVac + hMixed
  exact hAssemble

-- Two-coordinate specialization of the quartic Wick reduction: `z i * z j * V_A` expands into
-- one Wick sum per coefficient tuple `q` over the disjoint union `Sum (Fin 2) (Fin 4)`.  The
-- coordinate product over the family `t ↦ if t = 0 then i else j` is exactly `z i * z j`, so the
-- generic `integral_coordinateProduct_mul_potential_eq_sum_wick` applies verbatim.
private lemma integral_coord_mul_potential_eq_sum_wick
    (A : QuarticCoupling ι) (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (i j : ι) :
    ∫ z, z i * z j * A.potential z ∂multivariateGaussian 0 K =
      (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          wick (fun r s : Sum (Fin 2) (Fin 4) ↦
            K (Sum.elim (fun t : Fin 2 ↦ if t = 0 then i else j) q r)
              (Sum.elim (fun t : Fin 2 ↦ if t = 0 then i else j) q s)) Finset.univ := by
  rw [← integral_coordinateProduct_mul_potential_eq_sum_wick A K hK
    (index := (fun t : Fin 2 ↦ if t = 0 then i else j))]
  simp [coordinateProduct]

/-- Gaussian moment of two coordinates times a symmetric quartic potential.

Informal proof: the sixth-order pairings split equivariantly into three pairings where the two
external legs pair together and twelve where they pair to distinct quartic legs.  Symmetry of `A`
identifies each orbit, producing coefficients `3 / 4! = 1 / 8` and `12 / 4! = 1 / 2`. -/
theorem integral_coord_mul_potential (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (i j : ι) :
    ∫ z, z i * z j * A.potential z ∂multivariateGaussian 0 K =
      K i j * ((1 / 8 : ℝ) * A.quarticContraction K) +
        (1 / 2 : ℝ) * A.twoPointContraction K i j := by
  rw [integral_coord_mul_potential_eq_sum_wick A K hK i j,
    two_external_wick_sum_eq_three_twelve_contractions A K
      (fun i j ↦ hK.isHermitian.apply j i) i j]
  ring_nf

/-- Gaussian moment of four coordinates times the potential, retained as an eighth-order Wick
sum rather than a list of 105 terms.

Informal proof: this is `integral_coordinateProduct_mul_potential_eq_sum_wick` at `n=4`.  Keeping
the result as a pairing sum is the reusable form from which orbit cancellations in the connected
four-point theorem are derived. -/
theorem integral_fourCoords_mul_potential (A : QuarticCoupling ι)
    (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (index : Fin 4 → ι) :
    ∫ z, coordinateProduct index z * A.potential z ∂multivariateGaussian 0 K =
      (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          wick (fun r s : Sum (Fin 4) (Fin 4) ↦
            K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ :=
  integral_coordinateProduct_mul_potential_eq_sum_wick A K hK index

/-- Covariance of a four-coordinate observable with a symmetric quartic potential.

Informal proof: expand the eighth Gaussian moment by Isserlis' theorem.  Its 105 pairings split
into three equivariant classes.  There are nine pairings with no external-to-vertex edge; these
are exactly the product of the four-point Gaussian moment and `integral_potential`, so they cancel
in `covarianceWith`.  There are 72 pairings with exactly two external-to-vertex edges: for each of
the six choices of an external pair, the remaining two external legs can be attached to ordered
distinct vertex legs in `4 * 3 = 12` ways.  After the `1 / 4!` symmetry factor these give the six
terms below with coefficient `1 / 2`.  The remaining `4! = 24` pairings biject all four external
legs with the vertex legs, giving `fourPointContraction` with coefficient one.  Reindexing each
orbit uses `coeff_sum_perm` and total symmetry of `A`; no list of 105 pairings is required.

This is the orbit calculation in `docs/Renormalization.md`, equation
`eq:full-four-point-intro`, and is an instance of Isserlis' formula
<https://doi.org/10.1093/biomet/12.1-2.134>. -/
theorem covarianceWith_coordinateProduct_potential (A : QuarticCoupling ι)
    (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (index : Fin 4 → ι) :
    covarianceWith (multivariateGaussian 0 K) (coordinateProduct index) A.potential =
      (1 / 2 : ℝ) *
        (K (index 0) (index 1) * A.twoPointContraction K (index 2) (index 3) +
          K (index 0) (index 2) * A.twoPointContraction K (index 1) (index 3) +
          K (index 0) (index 3) * A.twoPointContraction K (index 1) (index 2) +
          K (index 1) (index 2) * A.twoPointContraction K (index 0) (index 3) +
          K (index 1) (index 3) * A.twoPointContraction K (index 0) (index 2) +
          K (index 2) (index 3) * A.twoPointContraction K (index 0) (index 1)) +
        A.fourPointContraction K index := by
  sorry

/-! ## First-order quartic response -/

/-- First-order relative partition-function formula with a quadratic right-hand remainder.

The explicit `hnorm` argument records that every nonnegative coupling gives a probability tilt;
`hV2` is the second-moment hypothesis used by the generic remainder theorem.

Informal proof: apply `partitionFunction_sub_linear_isBigO` and rewrite `∫ V_A` using
`integral_potential`.  The coefficient is `3 / 4! = 1 / 8`, obtained from the pairing orbit rather
than a manual list. -/
theorem partitionFunction_isBigO (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (hA : A.Nonnegative)
    (_hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K)) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ partitionFunction (multivariateGaussian 0 K) A.potential ε -
        (1 - (ε / 8) * A.quarticContraction K))
      (fun ε : ℝ ↦ ε ^ 2) := by
  have hVnonneg : 0 ≤ A.potential := by
    intro z
    exact hA z
  have hV : Integrable (fun z ↦ A.potential z) (multivariateGaussian 0 K) :=
    A.integrable_potential_of_sq hA hV2
  -- The generic quadratic remainder of the partition function, with the linear term rewritten
  -- by `integral_potential`.
  have hbase : Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ partitionFunction (multivariateGaussian 0 K) A.potential ε - 1 +
        ε * ∫ z, A.potential z ∂multivariateGaussian 0 K)
      (fun ε : ℝ ↦ ε ^ 2) :=
    partitionFunction_sub_linear_isBigO (μ := multivariateGaussian 0 K)
      (V := A.potential) hVnonneg hV hV2
  have hint : (∫ z, A.potential z ∂multivariateGaussian 0 K) =
      (1 / 8 : ℝ) * A.quarticContraction K :=
    integral_potential A K hK
  -- `1 - (ε / 8) * C = 1 - ε * ∫ V`, so the displayed remainder is exactly the generic one.
  refine hbase.congr_left ?_
  intro ε
  rw [hint]
  ring

/-- First-order two-point function with a quadratic right-hand remainder.

The hypotheses expose both normalizability and the exact second-moment integrability needed for
the observable `z_i z_j`.

Informal proof: apply `integral_deform_sub_linear_isBigO` to `O(z)=z_i z_j`.  Substitute
`integral_coord_mul_potential` and `integral_potential`; the disconnected `K i j` term cancels in
the covariance, leaving the twelve-element pairing orbit and hence the coefficient `1 / 2`. -/
theorem twoPoint_isBigO (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (hA : A.Nonnegative) (i j : ι)
    (_hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K))
    (hV2O : Integrable (fun z ↦ A.potential z ^ 2 * (z i * z j))
      (multivariateGaussian 0 K)) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ (∫ z, z i * z j ∂deform (multivariateGaussian 0 K) A.potential ε) -
        (K i j - (ε / 2) * A.twoPointContraction K i j))
      (fun ε : ℝ ↦ ε ^ 2) := by
  let μ : Measure (EuclideanSpace ℝ ι) := multivariateGaussian 0 K
  let O : EuclideanSpace ℝ ι → ℝ := fun z ↦ z i * z j
  let index : Fin 2 → ι := fun t ↦ if t = 0 then i else j
  have hindex0 : index 0 = i := by simp [index]
  have hindex1 : index 1 = j := by simp [index]
  have hVnonneg : 0 ≤ A.potential := by
    intro z
    exact hA z
  have hV : Integrable (fun z ↦ A.potential z) μ :=
    A.integrable_potential_of_sq hA hV2
  -- `z i * z j` is a finite Gaussian coordinate product, hence integrable.
  have hO : Integrable O μ := by
    dsimp [O]
    simpa [Fin.prod_univ_two] using
      (integrable_finset_prod_gaussian_coordinate (μ := μ)
        (s := (Finset.univ : Finset (Fin 2)))
        (coord := fun t : Fin 2 ↦ if t = 0 then i else j))
  have hVO' : Integrable (fun z : EuclideanSpace ℝ ι ↦ (z i * z j) * A.potential z) μ := by
    simpa [coordinateProduct, Fin.prod_univ_two, index] using
      A.integrable_coordinateProduct_mul_potential K index
  have hVO : Integrable (fun z : EuclideanSpace ℝ ι ↦ A.potential z * (z i * z j)) μ := by
    convert hVO' using 1
    ext z
    ring
  -- Gaussian two-point moment: `∫ z i * z j` is the covariance entry `K i j`.
  have hW : jointMoment μ
      (fun a : Fin 2 ↦ fun z ↦ z (index a) - (0 : EuclideanSpace ℝ ι) (index a)) =
      wick (fun a b : Fin 2 ↦ K (index a) (index b)) Finset.univ :=
    integral_prod_multivariateGaussian_centered_eq_wick_fintype (m := (0 : EuclideanSpace ℝ ι))
      (S := K) hK index
  have hC : ∀ a b : Fin 2, K (index a) (index b) = K (index b) (index a) := fun a b =>
    hK.isHermitian.apply (index b) (index a)
  have hwick2 : wick (fun a b : Fin 2 ↦ K (index a) (index b)) Finset.univ = K i j := by
    rw [wick_erase (fun a b : Fin 2 ↦ K (index a) (index b)) hC Finset.univ
      (by simp : (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)))]
    rw [show (Finset.univ : Finset (Fin 2)).erase (0 : Fin 2) = ({1} : Finset (Fin 2)) by decide]
    simp [hindex0, hindex1, wick_empty]
  have hintO : (∫ z, z i * z j ∂μ) = K i j := by
    calc
      (∫ z, z i * z j ∂μ) = jointMoment μ
          (fun a : Fin 2 ↦ fun z ↦ z (index a) - (0 : EuclideanSpace ℝ ι) (index a)) := by
        simp [jointMoment, blockMoment, index, Fin.prod_univ_two]
      _ = wick (fun a b : Fin 2 ↦ K (index a) (index b)) Finset.univ := hW
      _ = K i j := hwick2
  have hintV : (∫ z, A.potential z ∂μ) = (1 / 8 : ℝ) * A.quarticContraction K :=
    integral_potential A K hK
  have hintVO : (∫ z, A.potential z * (z i * z j) ∂μ) =
      K i j * ((1 / 8 : ℝ) * A.quarticContraction K) +
        (1 / 2 : ℝ) * A.twoPointContraction K i j := by
    rw [show (fun z : EuclideanSpace ℝ ι ↦ A.potential z * (z i * z j)) =
        fun z ↦ z i * z j * A.potential z by
      funext z
      ring]
    exact integral_coord_mul_potential A K hK i j
  -- The covariance term collapses: `∫ V O - (∫ V)(∫ O) = (1/2) * T`.
  have hcovWith : covarianceWith μ O A.potential =
      (1 / 2 : ℝ) * A.twoPointContraction K i j := by
    unfold covarianceWith
    simp only [O, smul_eq_mul]
    rw [hintVO, hintV, hintO]
    ring
  -- Generic quadratic response of the deformed two-point expectation.
  have hbase : Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ (∫ z, O z ∂deform μ A.potential ε) - (∫ z, O z ∂μ) +
        ε • covarianceWith μ O A.potential)
      (fun ε : ℝ ↦ ε ^ 2) :=
    integral_deform_sub_linear_isBigO (μ := μ) (V := A.potential) (O := O)
      hVnonneg hV hO hVO hV2 hV2O
  -- `1 - (ε/2) * T = ...`; the disconnected `K i j` term cancels in the covariance.
  refine hbase.congr_left ?_
  intro ε
  rw [hcovWith]
  simp only [O, smul_eq_mul]
  rw [hintO]
  dsimp [μ]
  ring

/-- First-order connected four-point function with a quadratic right-hand remainder.

Nonnegativity and `hnorm` make every right-hand deformation a probability measure.  The hypotheses
`hV2`, `hV2two`, and `hV2four` explicitly state the second-moment bounds needed for the partition,
all two-point subtractions, and the four-point observable.

Informal proof: expand the centered fourth cumulant with the generic low-order theorem, apply the
quadratic response theorem to the four-point and each two-point observable, and rewrite all Gaussian
moments by Wick.  Pairing orbits containing an internal or disconnected external pair cancel via
finite-sum equivalences.  The remaining orbit bijects the four external legs with the four coupling
legs; its cardinality is `4!`, cancelling the potential's symmetry factor. -/
theorem fourthCumulant_isBigO (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (hA : A.Nonnegative)
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K))
    (index : Fin 4 → ι)
    (hV2two : ∀ r s : Fin 4,
      Integrable (fun z ↦ A.potential z ^ 2 * (z (index r) * z (index s)))
        (multivariateGaussian 0 K))
    (hV2four : Integrable
      (fun z ↦ A.potential z ^ 2 * coordinateProduct index z)
      (multivariateGaussian 0 K)) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ jointCumulant (deform (multivariateGaussian 0 K) A.potential ε)
        (fun r : Fin 4 ↦ fun z ↦ z (index r)) + ε * A.fourPointContraction K index)
      (fun ε : ℝ ↦ ε ^ 2) := by
  let μ : Measure (EuclideanSpace ℝ ι) := multivariateGaussian 0 K
  let V : EuclideanSpace ℝ ι → ℝ := A.potential
  let O₄ : EuclideanSpace ℝ ι → ℝ := coordinateProduct index
  let P : Fin 4 → Fin 4 → ℝ → ℝ := fun r s ε ↦
    ∫ z, z (index r) * z (index s) ∂deform μ V ε
  let k : Fin 4 → Fin 4 → ℝ := fun r s ↦ K (index r) (index s)
  let t : Fin 4 → Fin 4 → ℝ := fun r s ↦ A.twoPointContraction K (index r) (index s)
  let M₄ : ℝ := k 0 1 * k 2 3 + k 0 2 * k 1 3 + k 0 3 * k 1 2
  let C₄ : ℝ := covarianceWith μ O₄ V
  let l : Filter ℝ := nhdsWithin 0 (Set.Ici 0)
  have hl : Tendsto (fun ε : ℝ ↦ ε) l (𝓝 0) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hVnonneg : 0 ≤ V := by
    intro z
    exact hA z
  have hV : Integrable V μ := by
    exact A.integrable_potential_of_sq hA hV2
  have hO₄ : Integrable O₄ μ := by
    change Integrable (fun z : EuclideanSpace ℝ ι ↦ ∏ r : Fin 4, z (index r)) μ
    simpa using
      (integrable_finset_prod_gaussian_coordinate (μ := μ)
        (s := (Finset.univ : Finset (Fin 4))) (coord := index))
  have hVO₄ : Integrable (fun z ↦ V z • O₄ z) μ := by
    have h := A.integrable_coordinateProduct_mul_potential K index
    simpa only [V, O₄, smul_eq_mul, mul_comm] using h
  have hM₄ : (∫ z, O₄ z ∂μ) = M₄ := by
    rw [show (∫ z, O₄ z ∂μ) =
        ∫ z, coordinateProduct index z ∂multivariateGaussian 0 K by rfl,
      integral_coordinateProduct_eq_wick K hK index,
      wick_quartic_slots (fun r s : Fin 4 ↦ K (index r) (index s))
        (fun r s ↦ hK.isHermitian.apply (index s) (index r))]
  have hC₄ : C₄ =
      (1 / 2 : ℝ) *
        (k 0 1 * t 2 3 + k 0 2 * t 1 3 + k 0 3 * t 1 2 +
          k 1 2 * t 0 3 + k 1 3 * t 0 2 + k 2 3 * t 0 1) +
        A.fourPointContraction K index := by
    exact A.covarianceWith_coordinateProduct_potential K hK index
  have hfourBase : Asymptotics.IsBigO l
      (fun ε ↦ (∫ z, O₄ z ∂deform μ V ε) - (∫ z, O₄ z ∂μ) + ε • C₄)
      (fun ε : ℝ ↦ ε ^ 2) :=
    integral_deform_sub_linear_isBigO (μ := μ) (V := V) (O := O₄)
      hVnonneg hV hO₄ hVO₄ hV2 hV2four
  have hfour : Asymptotics.IsBigO l
      (fun ε ↦ (∫ z, O₄ z ∂deform μ V ε) - (M₄ + ε * (-C₄)))
      (fun ε : ℝ ↦ ε ^ 2) := by
    refine hfourBase.congr_left ?_
    intro ε
    rw [hM₄]
    simp only [smul_eq_mul]
    ring
  have hpair (r s : Fin 4) : Asymptotics.IsBigO l
      (fun ε ↦ P r s ε - (k r s + ε * (-(1 / 2 : ℝ) * t r s)))
      (fun ε : ℝ ↦ ε ^ 2) := by
    have h := A.twoPoint_isBigO K hK hA (index r) (index s) hnorm hV2 (hV2two r s)
    refine h.congr_left ?_
    intro ε
    dsimp [l, P, k, t, μ, V]
    ring
  have hp01 := mul_sub_linear_isBigO hl (hpair 0 1) (hpair 2 3)
  have hp02 := mul_sub_linear_isBigO hl (hpair 0 2) (hpair 1 3)
  have hp03 := mul_sub_linear_isBigO hl (hpair 0 3) (hpair 1 2)
  have hcumul (ε : ℝ) :
      jointCumulant (deform μ V ε) (fun r : Fin 4 ↦ fun z ↦ z (index r)) =
        (∫ z, O₄ z ∂deform μ V ε) - P 0 1 ε * P 2 3 ε -
          P 0 2 ε * P 1 3 ε - P 0 3 ε * P 1 2 ε := by
    have hcenter : ∀ r : Fin 4,
        ∫ z, z (index r) ∂deform μ V ε = 0 := by
      intro r
      exact A.integral_coordinate_deform_eq_zero K ε (index r)
    simpa [O₄, P, coordinateProduct, Fin.prod_univ_four] using
      (jointCumulant_four_of_centered
        (μ := deform μ V ε) (fun r : Fin 4 ↦ fun z ↦ z (index r)) hcenter)
  have hrem := hfour.sub hp01 |>.sub hp02 |>.sub hp03
  refine hrem.congr_left ?_
  intro ε
  rw [hcumul ε, hC₄]
  dsimp [M₄]
  ring

/-- Two-point function of the quartically deformed Gaussian law. -/
def deformedTwoPoint (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (ε : ℝ) (i j : ι) : ℝ :=
  ∫ z, z i * z j ∂deform (multivariateGaussian 0 K) A.potential ε

/-- Full, non-connected four-point function of the quartically deformed Gaussian law. -/
def deformedFourPoint (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (ε : ℝ) (index : Fin 4 → ι) : ℝ :=
  ∫ z, coordinateProduct index z ∂deform (multivariateGaussian 0 K) A.potential ε

/-- First-order formula for the full, rather than connected, four-point correlator.

The leading expression is written in terms of the deformed two-point functions, exactly as in the
source: the three disconnected products are retained, and the connected contraction is subtracted
at order `ε`.

Informal proof: use `jointCumulant_four_of_centered` to express the full four-point moment as the
connected fourth cumulant plus the three products of two-point functions.  Apply
`fourthCumulant_isBigO`; its `O(ε²)` remainder is unchanged.  Source: equation
`eq:full-four-point-intro` and its simplified display immediately before
`eq:single-variable-connected-four-point` in `docs/Renormalization.md`.
-/
theorem fullFourPoint_isBigO (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (hA : A.Nonnegative)
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K))
    (index : Fin 4 → ι)
    (hV2two : ∀ r s : Fin 4,
      Integrable (fun z ↦ A.potential z ^ 2 * (z (index r) * z (index s)))
        (multivariateGaussian 0 K))
    (hV2four : Integrable
      (fun z ↦ A.potential z ^ 2 * coordinateProduct index z)
      (multivariateGaussian 0 K)) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ A.deformedFourPoint K ε index -
        (A.deformedTwoPoint K ε (index 0) (index 1) *
            A.deformedTwoPoint K ε (index 2) (index 3) +
          A.deformedTwoPoint K ε (index 0) (index 2) *
            A.deformedTwoPoint K ε (index 1) (index 3) +
          A.deformedTwoPoint K ε (index 0) (index 3) *
            A.deformedTwoPoint K ε (index 1) (index 2) -
          ε * A.fourPointContraction K index))
      (fun ε : ℝ ↦ ε ^ 2) := by
  have hconnected := A.fourthCumulant_isBigO K hK hA hnorm hV2 index hV2two hV2four
  refine hconnected.congr_left ?_
  intro ε
  have hcenter : ∀ r : Fin 4,
      ∫ z, z (index r) ∂deform (multivariateGaussian 0 K) A.potential ε = 0 := by
    intro r
    exact A.integral_coordinate_deform_eq_zero K ε (index r)
  rw [jointCumulant_four_of_centered
    (μ := deform (multivariateGaussian 0 K) A.potential ε)
    (fun r : Fin 4 ↦ fun z ↦ z (index r)) hcenter]
  simp only [deformedFourPoint, deformedTwoPoint, coordinateProduct, Fin.prod_univ_four]
  ring

/-- One-dimensional specialization exhibiting quartic self-interaction.

Even though there are no distinct coordinates to couple, the two-point function is shifted from
its Gaussian value by the quartic contraction.

Informal proof: specialize `twoPoint_isBigO` to the unique coordinate `0 : Fin 1`.  Source: the
`n=1` self-interaction footnote following equation `eq:gaussian-statistical-independence-day` in
`docs/Renormalization.md`.
-/
theorem oneDimensional_selfInteraction_isBigO
    (A : QuarticCoupling (Fin 1)) (K : Matrix (Fin 1) (Fin 1) ℝ)
    (hK : K.PosSemidef) (hA : A.Nonnegative)
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K))
    (hV2O : Integrable (fun z ↦ A.potential z ^ 2 * (z 0 * z 0))
      (multivariateGaussian 0 K)) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ A.deformedTwoPoint K ε 0 0 -
        (K 0 0 - (ε / 2) * A.twoPointContraction K 0 0))
      (fun ε : ℝ ↦ ε ^ 2) := by
  simpa only [deformedTwoPoint] using
    A.twoPoint_isBigO K hK hA 0 0 hnorm hV2 hV2O

end QuarticCoupling

end Renormalization

end

end
