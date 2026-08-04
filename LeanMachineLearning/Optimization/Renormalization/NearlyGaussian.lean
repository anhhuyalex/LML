/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Action
public import LeanMachineLearning.Optimization.Renormalization.Quartic
public import Mathlib.Probability.Independence.Basic

/-!
# Nearly-Gaussian laws and even interaction hierarchies

This file separates three notions that are easy to conflate informally:

* `NearlyGaussian` says all cumulants above order two vanish at least linearly in a small
  parameter;
* `HierarchicallyNearlyGaussian` records the stronger `2m`-point order `ε^(m-1)`;
* `EvenAction` is an action ansatz whose order-`2m` coupling is assigned that same scaling.

The linked-cluster theorem connects the third notion to the second.  It is not mathematically true
that arbitrary small non-Gaussian couplings automatically obey the hierarchy.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal Topology

namespace Renormalization

universe uΩ uI

/-- A totally symmetric coefficient tensor with `2m` finite-index slots. -/
structure EvenCoupling (ι : Type uI) (m : ℕ) where
  /-- Coefficient of an ordered `2m`-tuple. -/
  coeff : (Fin (2 * m) → ι) → ℝ
  /-- Invariance under every permutation of the slots. -/
  coeff_perm : ∀ (σ : Equiv.Perm (Fin (2 * m))) (q : Fin (2 * m) → ι),
    coeff (q ∘ σ) = coeff q

namespace EvenCoupling

/-- The zero coupling at any even order. -/
def zero (ι : Type uI) (m : ℕ) : EvenCoupling ι m where
  coeff := 0
  coeff_perm := by simp

/-- Regard an existing quartic coupling as the general even coupling at half-degree two. -/
def ofQuartic (A : QuarticCoupling ι) : EvenCoupling ι 2 where
  coeff := A.coeff
  coeff_perm := A.coeff_perm

/-- Even homogeneous potential with the conventional `1 / (2m)!` symmetry factor. -/
def potential {ι : Type uI} [Fintype ι] (s : EvenCoupling ι m)
    (z : EuclideanSpace ℝ ι) : ℝ :=
  (((2 * m).factorial : ℝ)⁻¹) *
    ∑ q : Fin (2 * m) → ι, s.coeff q * coordinateMonomial q z

/-- Pointwise nonnegativity, used as a sufficient normalizability hypothesis. -/
def Nonnegative {ι : Type uI} [Fintype ι] (s : EvenCoupling ι m) : Prop :=
  ∀ z, 0 ≤ s.potential z

end EvenCoupling

/-- A parity-even polynomial action with interactions through a finite cutoff.  Couplings below
order two and above `cutoff` are ignored by `interactionPotential`. -/
structure EvenAction (ι : Type uI) where
  /-- Quadratic precision matrix. -/
  precision : Matrix ι ι ℝ
  /-- Largest interaction half-degree retained in the action. -/
  cutoff : ℕ
  /-- Symmetric coupling at every even half-degree. -/
  coupling : (m : ℕ) → EvenCoupling ι m

namespace EvenAction

variable {ι : Type uI} [Fintype ι]

/-- Embed the existing quartic action into the general even-action hierarchy. -/
def ofQuartic (P : Matrix ι ι ℝ) (A : QuarticCoupling ι) : EvenAction ι where
  precision := P
  cutoff := 2
  coupling := fun m => if h : m = 2 then h ▸ EvenCoupling.ofQuartic A else EvenCoupling.zero ι m

/-- The interaction part of the action, with the order-`2m` coupling weighted by `ε^(m-1)`. -/
def interactionPotential (A : EvenAction ι) (ε : ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  ∑ m ∈ Finset.Icc 2 A.cutoff, ε ^ (m - 1) * (A.coupling m).potential z

/-- The full hierarchical even action. -/
def potential (A : EvenAction ι) (ε : ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  quadraticAction A.precision z + A.interactionPotential ε z

/-- The normalized deformation of a Gaussian base law by the interaction part of `A`. -/
def measure (A : EvenAction ι) (K : Matrix ι ι ℝ) (ε : ℝ) : Measure (EuclideanSpace ℝ ι) :=
  by
    classical
    exact Action.measure (multivariateGaussian 0 K) (A.interactionPotential ε)

/-- Truncate an even action by lowering its interaction cutoff. -/
def truncate (A : EvenAction ι) (k : ℕ) : EvenAction ι where
  precision := A.precision
  cutoff := min A.cutoff k
  coupling := A.coupling

/-- The general interaction potential specializes to the existing quartic potential.

Informal proof: `Finset.Icc 2 2` contains only two, the assigned scaling is `ε^(2-1)=ε`, and
`(2*2)!` is `4!`.  All definitions then agree term by term.  Source: comparison of
`eq:quartic-action-intro` with `eq:schematic-action-decomposition` in
`docs/Renormalization.md`.
-/
theorem interactionPotential_ofQuartic (P : Matrix ι ι ℝ) (A : QuarticCoupling ι)
    (ε : ℝ) (z : EuclideanSpace ℝ ι) :
    (ofQuartic P A).interactionPotential ε z = ε * A.potential z := by
  sorry

/-- The full action is invariant under the global sign flip.

Informal proof: the quadratic term has degree two and each interaction monomial has degree `2m`;
replacing every coordinate by its negative contributes the factor `(-1)^(2m)=1`.  Finite sums
preserve the equality.  Source: the parity discussion preceding
`eq:schematic-action-decomposition` in `docs/Renormalization.md`.
-/
theorem potential_neg (A : EvenAction ι) (ε : ℝ) (z : EuclideanSpace ℝ ι) :
    A.potential ε (-z) = A.potential ε z := by
  sorry

/-- The interaction-deformed Gaussian law is sign-flip invariant.

Informal proof: the centered Gaussian base measure is invariant under negation and
`interactionPotential` is even by the same monomial-parity argument as `potential_neg`.  Changing
variables `z ↦ -z` in the tilted density leaves the measure unchanged.  Source: parity discussion
in `docs/Renormalization.md`, lines 457--459 and the nearly-Gaussian action subsection.
-/
theorem measure_isNegInvariant (A : EvenAction ι) (K : Matrix ι ι ℝ) (ε : ℝ) :
    (A.measure K ε).IsNegInvariant := by
  sorry

end EvenAction

/-- `f(ε)` is parametrically of order `ε^order` along `l`. -/
def ParametricallySmall (l : Filter ℝ) (order : ℕ) (f : ℝ → ℝ) : Prop :=
  f =O[l] fun ε => ε ^ order

/-- A family of laws is nearly Gaussian when every cumulant above degree two is at least first
order in the small parameter. -/
def NearlyGaussian {Ω : Type uΩ} {ι : Type uI} [MeasurableSpace Ω]
    (law : ℝ → Measure Ω) (X : ι → Ω → ℝ) (l : Filter ℝ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ index : Fin n → ι,
    ParametricallySmall l 1
      (fun ε => jointCumulant (law ε) (fun r : Fin n => X (index r)))

/-- The stronger hierarchy occurring in wide-network effective theories. -/
def HierarchicallyNearlyGaussian {Ω : Type uΩ} {ι : Type uI} [MeasurableSpace Ω]
    (law : ℝ → Measure Ω) (X : ι → Ω → ℝ) (l : Filter ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ index : Fin (2 * m) → ι,
    ParametricallySmall l (m - 1)
      (fun ε => jointCumulant (law ε) (fun r : Fin (2 * m) => X (index r)))

/-- A hierarchical family is nearly Gaussian on a neighborhood of zero.

Informal proof: for `m≥2`, `ε^(m-1)=O(ε)` near zero.  Odd cumulants vanish for the even-action
families of interest; after splitting an order `n≥3` by parity, the even case follows from the
hierarchy and the odd case is zero.  Source: definition of nearly-Gaussianity and equation
`eq:connected-correlator-hierarchy` in `docs/Renormalization.md`.
-/
theorem HierarchicallyNearlyGaussian.nearlyGaussian_of_odd_eq_zero
    {Ω : Type uΩ} {ι : Type uI} [MeasurableSpace Ω]
    {law : ℝ → Measure Ω} {X : ι → Ω → ℝ}
    (h : HierarchicallyNearlyGaussian law X (nhdsWithin 0 (Set.Ici 0)))
    (hodd : ∀ n : ℕ, Odd n → ∀ index : Fin n → ι,
      (fun ε => jointCumulant (law ε) (fun r : Fin n => X (index r))) = 0) :
    NearlyGaussian law X (nhdsWithin 0 (Set.Ici 0)) := by
  sorry

/-- Linked-cluster hierarchy for the explicitly scaled even action.

Informal proof: expand normalized expectations in the interaction vertices.  In a connected
diagram with `2m` external legs, a collection of vertices of half-degrees `d₁,...,dᵣ` can be
connected only if `Σ(dᵢ-1) ≥ m-1`.  Its coupling weight is exactly
`ε^Σ(dᵢ-1)`, so every connected contribution is `O(ε^(m-1))`.  Disconnected diagrams cancel in
the cumulant Möbius transform.  Nonnegativity supplies domination of every right-hand Taylor
remainder by Gaussian polynomial moments.  This is the linked-cluster theorem; see
<https://en.wikipedia.org/wiki/Linked-cluster_theorem> and equation
`eq:connected-correlator-hierarchy` in `docs/Renormalization.md`.
-/
theorem EvenAction.connectedCorrelatorHierarchy
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (A : EvenAction ι) (K : Matrix ι ι ℝ) (hK : K.PosSemidef)
    (hnonneg : ∀ m ∈ Finset.Icc 2 A.cutoff, (A.coupling m).Nonnegative) :
    HierarchicallyNearlyGaussian (A.measure K) (fun i z => z i)
      (nhdsWithin 0 (Set.Ici 0)) := by
  sorry

/-- The hierarchically scaled even action is, in particular, nearly Gaussian.

Informal proof: apply `EvenAction.connectedCorrelatorHierarchy` to even orders.  Odd connected
correlators vanish because `EvenAction.measure_isNegInvariant` and coordinate products have odd
parity.  Finally use `HierarchicallyNearlyGaussian.nearlyGaussian_of_odd_eq_zero`.  Source:
definition of nearly-Gaussianity and equation `eq:connected-correlator-hierarchy` in
`docs/Renormalization.md`.
-/
theorem EvenAction.nearlyGaussian
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (A : EvenAction ι) (K : Matrix ι ι ℝ) (hK : K.PosSemidef)
    (hnonneg : ∀ m ∈ Finset.Icc 2 A.cutoff, (A.coupling m).Nonnegative) :
    NearlyGaussian (A.measure K) (fun i z => z i) (nhdsWithin 0 (Set.Ici 0)) := by
  sorry

/-- Formal truncation consequence of hierarchical connected-correlator scaling. -/
def TruncationAccurateTo {Ω : Type uΩ} {ι : Type uI} [MeasurableSpace Ω]
    (law : ℝ → Measure Ω) (X : ι → Ω → ℝ) (k : ℕ) (l : Filter ℝ) : Prop :=
  ∀ m : ℕ, k < m → ∀ index : Fin (2 * m) → ι,
    ParametricallySmall l k
      (fun ε => jointCumulant (law ε) (fun r : Fin (2 * m) => X (index r)))

/-- Hierarchical scaling licenses neglecting connected correlators above a fixed cutoff.

Informal proof: if `k<m`, then `m-1≥k`; on a neighborhood of zero,
`ε^(m-1)=O(ε^k)`.  Compose this elementary power estimate with the hierarchy's `IsBigO` bound.
This is the precise cumulant-level content of the truncation discussion following
`eq:connected-correlator-hierarchy` in `docs/Renormalization.md`.
-/
theorem HierarchicallyNearlyGaussian.truncationAccurateTo
    {Ω : Type uΩ} {ι : Type uI} [MeasurableSpace Ω]
    {law : ℝ → Measure Ω} {X : ι → Ω → ℝ} {k : ℕ}
    (h : HierarchicallyNearlyGaussian law X (nhdsWithin 0 (Set.Ici 0))) :
    TruncationAccurateTo law X k (nhdsWithin 0 (Set.Ici 0)) := by
  sorry

/-! ## Parity consequences -/

/-- Every odd coordinate moment vanishes under a sign-flip-invariant law.

Informal proof: a product of `n` coordinates changes by `(-1)^n=-1` under global negation when
`n` is odd.  Apply `integral_eq_zero_of_odd`.  Source: `docs/Renormalization.md`, lines 457--459.
-/
theorem jointMoment_coordinates_eq_zero_of_odd
    {ι : Type uI} [Fintype ι] (ν : Measure (EuclideanSpace ℝ ι)) [ν.IsNegInvariant]
    (n : ℕ) (hn : Odd n) (index : Fin n → ι)
    (hint : Integrable (coordinateMonomial index) ν) :
    jointMoment ν (fun r : Fin n => fun z => z (index r)) = 0 := by
  sorry

/-- Every odd connected coordinate correlator vanishes under parity symmetry.

Informal proof: expand `jointCumulant` as its partition Möbius sum.  Since the total cardinality
is odd, every partition has an odd-cardinality block.  Its block moment is zero by
`jointMoment_coordinates_eq_zero_of_odd`, so every block product vanishes.  Source:
`docs/Renormalization.md`, lines 457--459 and the paragraph before
`eq:schematic-action-decomposition`.
-/
theorem jointCumulant_coordinates_eq_zero_of_odd
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (ν : Measure (EuclideanSpace ℝ ι)) [ν.IsNegInvariant]
    (n : ℕ) (hn : Odd n) (index : Fin n → ι)
    (hfinite : HasFiniteJointMoments ν (fun r : Fin n => fun z => z (index r))) :
    jointCumulant ν (fun r : Fin n => fun z => z (index r)) = 0 := by
  sorry

/-! ## The six-point worked example -/

/-- Partitions of six positions with block sizes four and two. -/
def IsFourTwoPartition
    (P : Finpartition (Finset.univ : Finset (Fin 6))) : Prop :=
  P.parts.card = 2 ∧ ∀ B ∈ P.parts, B.card = 2 ∨ B.card = 4

/-- The finite set of all `(4,2)` partitions of six labelled positions. -/
noncomputable def fourTwoPartitions :
    Finset (Finpartition (Finset.univ : Finset (Fin 6))) := by
  classical
  exact Finset.univ.filter IsFourTwoPartition

/-- Sum of the fifteen `(4,2)` products of connected correlators. -/
def sixPointFourTwoCumulantSum
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) (X : Fin 6 → Ω → ℝ) : ℝ :=
  ∑ P ∈ fourTwoPartitions, P.blockProduct (blockCumulant μ X)

/-- Sum of the fifteen `(2,2,2)` products of connected two-point correlators. -/
def sixPointPairingCumulantSum
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) (X : Fin 6 → Ω → ℝ) : ℝ :=
  Finpartition.pairingSum (blockCumulant μ X) Finset.univ

/-- The six-point moment decomposes into connected `6`, `(4,2)`, and `(2,2,2)` pieces.

Informal proof: specialize `jointMoment_eq_sum_partition_jointCumulant` to `Fin 6`.  Odd block
cumulants remove every partition containing an odd block.  The remaining partitions have block
sizes `6`, `(4,2)`, or `(2,2,2)`; separate these three disjoint cases.  Source: equation
`eq:six-point-moment-in-terms-of-connected` in `docs/Renormalization.md`.
-/
theorem jointMoment_six_eq_connected_decomposition
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 6 → Ω → ℝ)
    (hodd : ∀ B : Finset (Fin 6), Odd B.card → blockCumulant μ X B = 0) :
    jointMoment μ X = jointCumulant μ X + sixPointFourTwoCumulantSum μ X +
      sixPointPairingCumulantSum μ X := by
  sorry

/-- Sum of the fifteen `(4,2)` products of raw moments. -/
def sixPointFourTwoMomentSum
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) (X : Fin 6 → Ω → ℝ) : ℝ :=
  ∑ P ∈ fourTwoPartitions, P.blockProduct (blockMoment μ X)

/-- Sum of the fifteen `(2,2,2)` products of raw second moments. -/
def sixPointPairingMomentSum
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) (X : Fin 6 → Ω → ℝ) : ℝ :=
  Finpartition.pairingSum (blockMoment μ X) Finset.univ

/-- Explicit sixth-cumulant formula for a parity-symmetric law.

Informal proof: substitute the two- and four-point moment--cumulant relations into
`jointMoment_six_eq_connected_decomposition` and collect coefficients.  Each of the fifteen
pairings occurs once in the six-point moment, three times through the `(4,2)` subtraction, and
hence with final coefficient `+2`.  Source: equation `eq:C6` in `docs/Renormalization.md`.
-/
theorem jointCumulant_six_eq_moments
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 6 → Ω → ℝ)
    (hodd : ∀ B : Finset (Fin 6), Odd B.card → blockMoment μ X B = 0) :
    jointCumulant μ X = jointMoment μ X - sixPointFourTwoMomentSum μ X +
      2 * sixPointPairingMomentSum μ X := by
  sorry

/-- There are fifteen pairings of six labelled positions. -/
theorem card_pairing_fin_six :
    Fintype.card (Finpartition.Pairing (Finset.univ : Finset (Fin 6))) = 15 := by
  sorry

/-- There are fifteen partitions of type `(4,2)` on six labelled positions. -/
theorem card_fourTwoPartition_fin_six :
    fourTwoPartitions.card = 15 := by
  sorry

/-! ## Gaussian diagonalization and interaction versus independence -/

/-- A diagonal multivariate Gaussian is exactly a product of one-dimensional Gaussian laws.

Informal proof: compare characteristic functions.  Both sides have mean zero and characteristic
function `exp (-1/2 * Σ i, v i * t i^2)`; uniqueness of characteristic functions gives equality.
Source: equation `eq:gaussian-statistical-independence-day` in `docs/Renormalization.md` and
Mathlib's Gaussian characteristic-function API.
-/
theorem multivariateGaussian_diagonal_eq_map_pi_gaussianReal
    {ι : Type uI} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) :
    Measure.map (EuclideanSpace.equiv ι ℝ)
        (multivariateGaussian 0 (Matrix.diagonal fun i => (v i : ℝ))) =
      Measure.pi fun i : ι => gaussianReal 0 (v i) := by
  sorry

/-- Coordinates of a centered Gaussian with diagonal covariance are mutually independent.

Informal proof: rewrite the law using
`multivariateGaussian_diagonal_eq_map_pi_gaussianReal`; coordinate evaluation after the inverse
Euclidean equivalence is ordinary product-space evaluation, and `iIndepFun_pi` supplies mutual
independence.  Source: equation `eq:gaussian-statistical-independence-day`.
-/
theorem iIndepFun_coordinate_multivariateGaussian_diagonal
    {ι : Type uI} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) :
    iIndepFun (fun i (z : EuclideanSpace ℝ ι) => z i)
      (multivariateGaussian 0 (Matrix.diagonal fun i => (v i : ℝ))) := by
  sorry

/-- Orthogonal diagonalization transports a Gaussian to independent one-dimensional coordinates.

Informal proof: a linear image of a centered Gaussian has covariance `O K Oᵀ`.  Under the stated
diagonalization hypothesis this is `diagonal v`; apply the preceding product-law equality.  This
formalizes the basis-change argument in equation `eq:gaussian-statistical-independence-day`.
-/
theorem map_multivariateGaussian_eq_pi_of_orthogonal_diagonalization
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K O : Matrix ι ι ℝ) (v : ι → ℝ≥0)
    (hO : O.transpose * O = 1)
    (hdiag : O * K * O.transpose = Matrix.diagonal fun i => (v i : ℝ)) :
    Measure.map
        (fun z : EuclideanSpace ℝ ι => O *ᵥ (EuclideanSpace.equiv ι ℝ z))
        (multivariateGaussian 0 K) =
      Measure.pi fun i : ι => gaussianReal 0 (v i) := by
  sorry

/-- A nonzero mixed cumulant rules out independence across that split. -/
theorem not_indepAcross_of_jointCumulant_ne_zero
    {Ω : Type uΩ} {ι : Type uI} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (A : Finset ι)
    (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hX : HasFiniteJointMoments μ X) (hmeas : ∀ i, Measurable (X i))
    (hne : jointCumulant μ X ≠ 0) :
    ¬ IndepAcross μ X A := by
  intro hindep
  exact hne (jointCumulant_eq_zero_of_indepFun_split X A hA hAc hX hmeas hindep)

/-- A nonzero mixed quartic contraction eventually obstructs factorization across every nontrivial
split of its four external positions.

This is the correct qualified version of “a quartic interaction breaks independence.”  Merely
assuming that the coefficient tensor is nonzero would be false: a sum of separate one-coordinate
quartic potentials can still define a product law.

Informal proof: `fourthCumulant_isBigO` says the mixed fourth cumulant is
`-ε * fourPointContraction + O(ε²)`.  If the contraction is nonzero, division by `ε` shows that
the cumulant is nonzero for all sufficiently small positive `ε`.  Independence across `B` would
force it to vanish by `jointCumulant_eq_zero_of_indepFun_split`, a contradiction.  Source: the
interaction/independence discussion after equation `eq:gaussian-statistical-independence-day` in
`docs/Renormalization.md`.
-/
theorem QuarticCoupling.eventually_not_indepAcross_of_fourPointContraction_ne_zero
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (A : QuarticCoupling ι) (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (hA : A.Nonnegative)
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ), Normalizable (multivariateGaussian 0 K) A.potential ε)
    (hV2 : Integrable (fun z ↦ A.potential z ^ 2) (multivariateGaussian 0 K))
    (index : Fin 4 → ι)
    (hV2two : ∀ r s : Fin 4,
      Integrable (fun z ↦ A.potential z ^ 2 * (z (index r) * z (index s)))
        (multivariateGaussian 0 K))
    (hV2four : Integrable
      (fun z ↦ A.potential z ^ 2 * QuarticCoupling.coordinateProduct index z)
      (multivariateGaussian 0 K))
    (B : Finset (Fin 4)) (hB : B.Nonempty) (hBc : (Finset.univ \ B).Nonempty)
    (hcontract : A.fourPointContraction K index ≠ 0) :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ¬ IndepAcross (deform (multivariateGaussian 0 K) A.potential ε)
        (fun r : Fin 4 => fun z => z (index r)) B := by
  sorry

end Renormalization

end

end
