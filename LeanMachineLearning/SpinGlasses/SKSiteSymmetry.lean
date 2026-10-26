/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKFirstMoment
public import LeanMachineLearning.SpinGlasses.SKSpinDecorrelation

/-!
# Symmetry between the sites of the Sherrington-Kirkpatrick model

A permutation `π` of the sites `Fin N` relabels the pairs `i < j` of the interaction couplings by
sorting `{π i, π j}`.  This relabelling `SpinGlasses.pairPerm π` is a permutation of
`FinPairs N`, hence preserves the i.i.d. Gaussian law of the couplings; together with the
invariance of the field term, this is the symmetry between sites used in Proposition 1.4.14.

## Main declarations

* `SpinGlasses.pairPerm`: the permutation of the pairs `i < j` induced by a permutation of sites.
* `SpinGlasses.sum_pairs_pairPerm`: the pair sum `∑_{i<j} gᵢⱼ sπ(i) sπ(j)` is the pair sum of
  the relabelled couplings.
* `SpinGlasses.measurePreserving_pairPerm`: relabelling the couplings preserves the Gaussian law.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

variable {N : ℕ}

/-- Sorting the image of a pair `i < j` under a permutation recovers the pair after sorting the
image under the inverse permutation. -/
theorem min_max_sort_sort (e : Equiv.Perm (Fin N)) {i j : Fin N} (hij : i < j) :
    min (e.symm (min (e i) (e j))) (e.symm (max (e i) (e j))) = i ∧
      max (e.symm (min (e i) (e j))) (e.symm (max (e i) (e j))) = j := by
  rcases lt_or_gt_of_ne (e.injective.ne hij.ne) with h | h
  · simp [min_eq_left h.le, max_eq_right h.le, min_eq_left hij.le, max_eq_right hij.le]
  · simp [min_eq_right h.le, max_eq_left h.le, min_eq_right hij.le, max_eq_left hij.le]

/-- **The permutation of the pairs `i < j` induced by a permutation of the sites:** the pair
`(i, j)` goes to the sorted pair `{π i, π j}`. -/
def pairPerm (π : Equiv.Perm (Fin N)) : Equiv.Perm (FinPairs N) where
  toFun p := ⟨(min (π p.1.1) (π p.1.2), max (π p.1.1) (π p.1.2)),
    min_lt_max.2 fun h => p.2.ne (π.injective h)⟩
  invFun p := ⟨(min (π.symm p.1.1) (π.symm p.1.2), max (π.symm p.1.1) (π.symm p.1.2)),
    min_lt_max.2 fun h => p.2.ne (π.symm.injective h)⟩
  left_inv p := Subtype.ext (Prod.ext (min_max_sort_sort π p.2).1 (min_max_sort_sort π p.2).2)
  right_inv p := Subtype.ext (by
    simpa using Prod.ext (min_max_sort_sort π.symm p.2).1 (min_max_sort_sort π.symm p.2).2)

/-- **The pair sum under a relabelling of the sites.**  Summing the couplings against the spins
at the images `π i`, `π j` of the sites of each pair is the pair sum of the relabelled couplings
`g ∘ (pairPerm π).symm` against the original spins. -/
theorem sum_pairs_pairPerm (π : Equiv.Perm (Fin N)) (g : FinPairs N → ℝ) (s : Fin N → ℝ) :
    ∑ p : FinPairs N, g p * s (π p.1.1) * s (π p.1.2) =
      ∑ p : FinPairs N, g ((pairPerm π).symm p) * s p.1.1 * s p.1.2 := by
  have hp : ∀ p : FinPairs N, s (π p.1.1) * s (π p.1.2) =
      s (pairPerm π p).1.1 * s (pairPerm π p).1.2 := fun p => by
    rcases lt_or_gt_of_ne (π.injective.ne p.2.ne) with h | h
    · simp [pairPerm, min_eq_left h.le, max_eq_right h.le]
    · simp [pairPerm, min_eq_right h.le, max_eq_left h.le, mul_comm]
  calc ∑ p : FinPairs N, g p * s (π p.1.1) * s (π p.1.2)
      = ∑ p : FinPairs N, (fun q => g ((pairPerm π).symm q) * s q.1.1 * s q.1.2) (pairPerm π p) :=
        Finset.sum_congr rfl fun p _ => by
          simp only [Equiv.symm_apply_apply, mul_assoc, hp]
    _ = _ := Equiv.sum_comp (pairPerm π) fun q => g ((pairPerm π).symm q) * s q.1.1 * s q.1.2

/-- **Relabelling the Gaussian couplings preserves their law.** -/
theorem measurePreserving_comp_pairPerm (μ : Measure ℝ) [SigmaFinite μ]
    (π : Equiv.Perm (Fin N)) :
    MeasurePreserving (fun g : FinPairs N → ℝ => g ∘ (pairPerm π).symm)
      (Measure.pi fun _ : FinPairs N => μ) (Measure.pi fun _ : FinPairs N => μ) := by
  have h := measurePreserving_piCongrLeft (fun _ : FinPairs N => μ) (pairPerm π)
  convert h using 1
  ext g a
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- **The symmetric coupling field.**  The symmetric extension of the couplings
`g : FinPairs N → ℝ`: `g_{ij}` for `i < j`, `g_{ji}` for `j < i`, and `0` on the diagonal. -/
def skSymmCoupling (g : FinPairs N → ℝ) (i j : Fin N) : ℝ :=
  if hij : i < j then g ⟨(i, j), hij⟩
  else if hji : j < i then g ⟨(j, i), hji⟩ else 0

/-- The symmetric coupling field is symmetric in its site arguments. -/
theorem skSymmCoupling_comm (g : FinPairs N → ℝ) (i j : Fin N) :
    skSymmCoupling g i j = skSymmCoupling g j i := by
  dsimp [skSymmCoupling]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le]
  · simp
  · simp [h, not_lt.mpr h.le]

/-- **The symmetric coupling field under a relabelling of the sites.** -/
theorem skSymmCoupling_comp_pairPerm (π : Equiv.Perm (Fin N)) (g : FinPairs N → ℝ)
    (i j : Fin N) :
    skSymmCoupling (g ∘ (pairPerm π).symm) i j = skSymmCoupling g (π.symm i) (π.symm j) := by
  dsimp [skSymmCoupling]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hne : π.symm i ≠ π.symm j := π.symm.injective.ne hij.ne
    simp only [hij, ↓reduceDIte]
    rcases lt_or_gt_of_ne hne with h | h
    · simp only [h, ↓reduceDIte]
      simp [pairPerm, min_eq_left h.le, max_eq_right h.le]
    · simp only [not_lt.mpr h.le, h, ↓reduceDIte]
      simp [pairPerm, min_eq_right h.le, max_eq_left h.le]
  · simp
  · have hne : π.symm j ≠ π.symm i := π.symm.injective.ne hji.ne
    simp only [not_lt.mpr hji.le, hji, ↓reduceDIte]
    rcases lt_or_gt_of_ne hne with h | h
    · simp only [not_lt.mpr h.le, h, ↓reduceDIte]
      simp [pairPerm, min_eq_left h.le, max_eq_right h.le]
    · simp only [h, ↓reduceDIte]
      simp [pairPerm, min_eq_right h.le, max_eq_left h.le]

/-- **Relabelling the couplings relabels the Gibbs weights.**  With the SK energy `E` (pair
couplings `g`, external field `h`), the Gibbs weight of `σ` under the relabelled couplings
`g ∘ (pairPerm π).symm` is the weight of `σ ∘ π` under `g`: `G_{g ∘ (pairPerm π).symm}(σ) =
G_g(σ ∘ π)`; the configuration relabelling is `Equiv.arrowCongr π.symm (Equiv.refl _)`. -/
theorem gibbsWeight_comp_pairPerm (β h : ℝ) (π : Equiv.Perm (Fin N))
    (E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hE : ∀ g a, E g a = (Real.sqrt N)⁻¹ * β *
      (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ))
    (g : FinPairs N → ℝ) (σ : Fin N → ℤˣ) :
    Real.exp (E (g ∘ (pairPerm π).symm) σ) / ∑ b, Real.exp (E (g ∘ (pairPerm π).symm) b) =
      Real.exp (E g (Equiv.arrowCongr π.symm (Equiv.refl _) σ)) / ∑ b, Real.exp (E g b) := by
  have hact : ∀ τ : Fin N → ℤˣ, Equiv.arrowCongr π.symm (Equiv.refl (ℤˣ)) τ = τ ∘ π := fun τ => by
    ext i; simp
  have hEc : ∀ τ : Fin N → ℤˣ, E (g ∘ (pairPerm π).symm) τ = E g (τ ∘ π) := fun τ => by
    rw [hE, hE]
    have h1 := sum_pairs_pairPerm π g (fun i => ((τ i : ℤ) : ℝ))
    have h2 : ∑ i, ((τ (π i) : ℤ) : ℝ) = ∑ i, ((τ i : ℤ) : ℝ) :=
      Equiv.sum_comp π fun i => ((τ i : ℤ) : ℝ)
    simp only [Function.comp_apply]
    rw [h2, ← h1]
  simp only [hEc, hact]
  congr 1
  have := Equiv.sum_comp (Equiv.arrowCongr π.symm (Equiv.refl (ℤˣ))) fun b => Real.exp (E g b)
  simp only [hact] at this
  exact this

/-- **The Gibbs weights of the SK model are site-symmetric in law.**  For every permutation `π` of
the sites there is a measure-preserving relabelling `φ` of the Gaussian couplings under which the
Gibbs weight of the relabelled configuration is the weight of the original one
(`gibbsWeight_comp_pairPerm`, with `φ g = g ∘ (pairPerm π).symm`). -/
theorem exists_measurePreserving_sk_gibbsWeight (β h : ℝ) (π : Equiv.Perm (Fin N))
    (E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hE : ∀ g a, E g a = (Real.sqrt N)⁻¹ * β *
      (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ)) :
    ∃ φ : (FinPairs N → ℝ) → (FinPairs N → ℝ),
      MeasurePreserving φ (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
      ∀ g σ, Real.exp (E (φ g) σ) / ∑ b, Real.exp (E (φ g) b) =
        Real.exp (E g (Equiv.arrowCongr π.symm (Equiv.refl _) σ)) / ∑ b, Real.exp (E g b) :=
  ⟨fun g => g ∘ (pairPerm π).symm, measurePreserving_comp_pairPerm (gaussianReal 0 1) π,
    gibbsWeight_comp_pairPerm β h π E hE⟩

end SpinGlasses
