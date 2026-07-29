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
  sorry

/-- Nonnegative quartic potentials are normalizable at every nonnegative coupling.

Informal proof: `continuous_potential` supplies measurability, and `A.Nonnegative` gives the
pointwise bound `exp (-ε V_A) ≤ 1` for `ε ≥ 0`.  Apply
`Renormalization.normalizable_of_nonnegative` to the Gaussian probability measure. -/
theorem normalizable (A : QuarticCoupling ι) {K : Matrix ι ι ℝ}
    (hA : A.Nonnegative) {ε : ℝ} (hε : 0 ≤ ε) :
    Normalizable (multivariateGaussian 0 K) A.potential ε := by
  sorry

/-! ## Pairing-orbit moment formulae -/

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
  sorry

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

end QuarticCoupling

end Renormalization

end

end
