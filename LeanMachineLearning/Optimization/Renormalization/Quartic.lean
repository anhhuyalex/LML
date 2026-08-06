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

open MeasureTheory ProbabilityTheory
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

/-- Nonnegative quartic potentials are normalizable at every nonnegative coupling.

Informal proof: `continuous_potential` supplies measurability, and `A.Nonnegative` gives the
pointwise bound `exp (-ε V_A) ≤ 1` for `ε ≥ 0`.  Apply
`Renormalization.normalizable_of_nonnegative` to the Gaussian probability measure. -/
theorem normalizable (A : QuarticCoupling ι) {K : Matrix ι ι ℝ}
    (hA : A.Nonnegative) {ε : ℝ} (hε : 0 ≤ ε) :
    Normalizable (multivariateGaussian 0 K) A.potential ε :=
  normalizable_of_nonnegative A.continuous_potential.aestronglyMeasurable hA hε

/-! ## Pairing-orbit moment formulae -/

omit [DecidableEq ι] in
/-- Finite products of coordinate projections are integrable under any Gaussian measure.

This is the coordinate-projection specialization of the finite Hölder argument used in
`Gaussian.lean` for products of centered linear observables: each coordinate is a continuous
linear functional, hence has all finite Gaussian moments, and Hölder turns finitely many such
bounds into an `L¹` bound for the product. -/
private lemma integrable_finset_prod_gaussian_coordinate
    (μ : Measure (EuclideanSpace ℝ ι)) [ProbabilityTheory.IsGaussian μ]
    {α : Type*} (s : Finset α) (coord : α → ι) :
    Integrable (fun z : EuclideanSpace ℝ ι ↦ ∏ a ∈ s, z (coord a)) μ := by
  by_cases hs : s.Nonempty
  · have h_coord_memLp : ∀ a ∈ s,
        MemLp (fun z : EuclideanSpace ℝ ι ↦ z (coord a))
          (((s.card : ℕ) : ℝ≥0∞)) μ := fun a _ha ↦ by
      simpa [EuclideanSpace.coe_proj] using
        (ProbabilityTheory.IsGaussian.memLp_dual μ (EuclideanSpace.proj (coord a))
          (((s.card : ℕ) : ℝ≥0∞)) (ENNReal.natCast_ne_top _))
    have h_holder_product :
        MemLp (fun z : EuclideanSpace ℝ ι ↦ ∏ a ∈ s, z (coord a))
          ((∑ a ∈ s, (((s.card : ℕ) : ℝ≥0∞))⁻¹)⁻¹) μ := by
      convert
        (MeasureTheory.MemLp.prod
          (μ := μ)
          (f := fun a z : EuclideanSpace ℝ ι ↦ z (coord a))
          (p := fun _ : α ↦ (((s.card : ℕ) : ℝ≥0∞)))
          (s := s)
          h_coord_memLp) using 1
      ext z
      simp
    have h_exponent :
        ((∑ a ∈ s, (((s.card : ℕ) : ℝ≥0∞))⁻¹)⁻¹) =
          (1 : ℝ≥0∞) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      have hcard_pos : 0 < s.card := Finset.card_pos.mpr hs
      have hcard_ne_zero : s.card ≠ 0 := Nat.ne_of_gt hcard_pos
      have h0 : (((s.card : ℕ) : ℝ≥0∞) ≠ 0) := by
        norm_num [hcard_ne_zero]
      have htop : (((s.card : ℕ) : ℝ≥0∞) ≠ ∞) := ENNReal.natCast_ne_top _
      have hmul :
          (((s.card : ℕ) : ℝ≥0∞) * (((s.card : ℕ) : ℝ≥0∞)⁻¹)) =
            (1 : ℝ≥0∞) :=
        ENNReal.mul_inv_cancel h0 htop
      change ((((s.card : ℕ) : ℝ≥0∞) *
        (((s.card : ℕ) : ℝ≥0∞)⁻¹))⁻¹) = (1 : ℝ≥0∞)
      rw [hmul]
      simp
    exact (h_exponent ▸ h_holder_product :
      MemLp (fun z : EuclideanSpace ℝ ι ↦ ∏ a ∈ s, z (coord a)) 1 μ).integrable
        (by norm_num)
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs_empty]

/-- Expanding the quartic potential inside a Gaussian integral.

Informal proof: unfold `coordinateProduct` and `potential`, distribute multiplication over the
finite sum over quartic labels, and use finite linearity of the Bochner integral.  The required
integrability statements are polynomial-moment bounds for a finite-dimensional Gaussian. -/
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
  have h_integrable_monomial : ∀ q : Fin 4 → ι, Integrable (monomial q) μ := by
    intro q
    let coord : Sum (Fin n) (Fin 4) → ι := Sum.elim index q
    have hprod := integrable_finset_prod_gaussian_coordinate
      (μ := μ) (s := (Finset.univ : Finset (Sum (Fin n) (Fin 4)))) (coord := coord)
    have h_eq : (fun z : EuclideanSpace ℝ ι ↦ ∏ a : Sum (Fin n) (Fin 4), z (coord a)) =
        monomial q := by
      funext z
      simp [monomial, coordinateProduct, coord, Fintype.prod_sum_type]
    simpa [h_eq] using hprod
  have h_integrable_summand :
      ∀ q ∈ (Finset.univ : Finset (Fin 4 → ι)),
        Integrable (fun z : EuclideanSpace ℝ ι ↦ A.coeff q * monomial q z) μ := by
    intro q _hq
    exact (h_integrable_monomial q).const_mul _
  calc
    ∫ z, coordinateProduct index z * A.potential z ∂multivariateGaussian 0 K =
        ∫ z, c * ∑ q : Fin 4 → ι, A.coeff q * monomial q z ∂μ := by
      simp [μ, c, monomial, coordinateProduct, potential, mul_sum, mul_assoc]
    _ = c * ∫ z, ∑ q : Fin 4 → ι, A.coeff q * monomial q z ∂μ := by
      rw [MeasureTheory.integral_const_mul]
    _ = c * ∑ q : Fin 4 → ι, ∫ z, A.coeff q * monomial q z ∂μ := by
      rw [MeasureTheory.integral_finsetSum]
      exact h_integrable_summand
    _ = c * ∑ q : Fin 4 → ι, A.coeff q * ∫ z, monomial q z ∂μ := by
      simp [MeasureTheory.integral_const_mul]
    _ = (((4 : ℕ).factorial : ℝ)⁻¹) *
        ∑ q : Fin 4 → ι, A.coeff q *
          ∫ z, coordinateProduct index z * ∏ r, z (q r) ∂multivariateGaussian 0 K := by
      simp [μ, c, monomial]

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
        K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ := by
  sorry

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
            K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ := by
  calc
    ∫ z, coordinateProduct index z * A.potential z ∂multivariateGaussian 0 K =
        (((4 : ℕ).factorial : ℝ)⁻¹) *
          ∑ q : Fin 4 → ι, A.coeff q *
            ∫ z, coordinateProduct index z * ∏ r, z (q r) ∂multivariateGaussian 0 K :=
      integral_coordinateProduct_mul_potential_eq_sum_integral A K index
    _ = (((4 : ℕ).factorial : ℝ)⁻¹) *
          ∑ q : Fin 4 → ι, A.coeff q *
            wick (fun r s : Sum (Fin n) (Fin 4) ↦
              K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ := by
      simp_rw [integral_coordinateProduct_mul_quarticMonomial_eq_wick K hK index]

/-- Gaussian expectation of a symmetric quartic potential.

Informal proof: specialize the preceding Wick reduction to no external legs.  The three pairings
of four slots form one orbit under slot permutations; symmetry of `A` identifies their sums, so
the multiplicity `3 / 4! = 1 / 8` is derived from the orbit equivalence. -/
theorem integral_potential (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) :
    ∫ z, A.potential z ∂multivariateGaussian 0 K =
      (1 / 8 : ℝ) * A.quarticContraction K := by
  sorry

/-- Gaussian moment of two coordinates times a symmetric quartic potential.

Informal proof: the sixth-order pairings split equivariantly into three pairings where the two
external legs pair together and twelve where they pair to distinct quartic legs.  Symmetry of `A`
identifies each orbit, producing coefficients `3 / 4! = 1 / 8` and `12 / 4! = 1 / 2`. -/
theorem integral_coord_mul_potential (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (i j : ι) :
    ∫ z, z i * z j * A.potential z ∂multivariateGaussian 0 K =
      K i j * ((1 / 8 : ℝ) * A.quarticContraction K) +
        (1 / 2 : ℝ) * A.twoPointContraction K i j := by
  sorry

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
            K (Sum.elim index q r) (Sum.elim index q s)) Finset.univ := by
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
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K)) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ partitionFunction (multivariateGaussian 0 K) A.potential ε -
        (1 - (ε / 8) * A.quarticContraction K))
      (fun ε : ℝ ↦ ε ^ 2) := by
  sorry

/-- First-order two-point function with a quadratic right-hand remainder.

The hypotheses expose both normalizability and the exact second-moment integrability needed for
the observable `z_i z_j`.

Informal proof: apply `integral_deform_sub_linear_isBigO` to `O(z)=z_i z_j`.  Substitute
`integral_coord_mul_potential` and `integral_potential`; the disconnected `K i j` term cancels in
the covariance, leaving the twelve-element pairing orbit and hence the coefficient `1 / 2`. -/
theorem twoPoint_isBigO (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (hA : A.Nonnegative) (i j : ι)
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K))
    (hV2O : Integrable (fun z ↦ A.potential z ^ 2 * (z i * z j))
      (multivariateGaussian 0 K)) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun ε ↦ (∫ z, z i * z j ∂deform (multivariateGaussian 0 K) A.potential ε) -
        (K i j - (ε / 2) * A.twoPointContraction K i j))
      (fun ε : ℝ ↦ ε ^ 2) := by
  sorry

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
  sorry

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
  sorry

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
