/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.PairingWick
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.PiDisjointSupports
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm

/-!
# Two pairings of Gaussian linear forms with disjoint block supports

Let `V a b` be the coefficient vector of the linear form `z ↦ V a b ⬝ᵥ z` of i.i.d. standard
Gaussians, symmetric in `(a, b)`, supported on pairwise disjoint sets of coordinates for
distinct unordered pairs `{a, b}`, with squared norm `s`. For two pairings `P₀`, `P` of the
labels, the Gaussian mean of the product of the block products of the two pairings is `s` to
the number of blocks if `P = P₀`, and `0` otherwise: a block that occurs in only one pairing
appears to the first power and is independent of everything else.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix

namespace Renormalization

variable {D L : Type*} [Fintype D] [DecidableEq L]

/-- **Gaussian mean of two pairings with disjoint block supports.** See the module docstring. -/
theorem integral_pi_gaussian_two_pairings_eq_prod [Fintype L] (V : L → L → D → ℝ)
    (hVs : ∀ a b, V a b = V b a)
    (hdisj : ∀ a b a' b' : L, a ≠ b → a' ≠ b' → ({a, b} : Finset L) ≠ {a', b'} →
      ∀ k, V a b k = 0 ∨ V a' b' k = 0)
    (s : ℝ) (hnorm : ∀ a b : L, a ≠ b → V a b ⬝ᵥ V a b = s)
    (P₀ P : Finpartition.Pairing (Finset.univ : Finset L)) :
    ∫ z : D → ℝ, P₀.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z) *
        P.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z)
      ∂(Measure.pi fun _ : D => gaussianReal 0 1) =
      ∏ B ∈ P₀.1.parts ∪ P.1.parts, if B ∈ P₀.1.parts ∧ B ∈ P.1.parts then s else 0 := by
  classical
  let W : Finset (Finset L) := P₀.1.parts ∪ P.1.parts
  let mult : Finset L → ℕ := fun B =>
    (if B ∈ P₀.1.parts then 1 else 0) + (if B ∈ P.1.parts then 1 else 0)
  let Cz : (D → ℝ) → L → L → ℝ := fun z a b => V a b ⬝ᵥ z
  have hCsymm (z : D → ℝ) (a b : L) : Cz z a b = Cz z b a := by simp only [Cz, hVs a b]
  have hblock (B : Finset L) (hB : B ∈ W) : ∃ a b, a ≠ b ∧ B = {a, b} := by
    rcases Finset.mem_union.1 hB with h | h
    · exact Finset.card_eq_two.1 (P₀.2 B h)
    · exact Finset.card_eq_two.1 (P.2 B h)
  let Y : Finset L → (D → ℝ) → ℝ := fun B z => pairWeight (Cz z) B ^ mult B
  -- product over a sub-collection of the blocks of `W`
  have hsub (A : Finset (Finset L)) (hA : A ⊆ W) (f : Finset L → ℝ) :
      ∏ B ∈ W, f B ^ (if B ∈ A then 1 else 0) = ∏ B ∈ A, f B := by
    have h1 : ∏ B ∈ W, f B ^ (if B ∈ A then 1 else 0) = ∏ B ∈ W, if B ∈ A then f B else 1 :=
      Finset.prod_congr rfl fun B _ => by split_ifs <;> simp
    rw [h1, ← Finset.prod_filter]
    congr 1
    ext B
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
  have hint (z : D → ℝ) :
      P₀.blockProduct (pairWeight (Cz z)) * P.blockProduct (pairWeight (Cz z)) =
        ∏ B ∈ W, Y B z := by
    have h1 : ∏ B ∈ W, Y B z =
        (∏ B ∈ W, pairWeight (Cz z) B ^ (if B ∈ P₀.1.parts then 1 else 0)) *
        ∏ B ∈ W, pairWeight (Cz z) B ^ (if B ∈ P.1.parts then 1 else 0) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun B _ => by simp only [Y, mult, pow_add]
    rw [h1, hsub P₀.1.parts Finset.subset_union_left, hsub P.1.parts Finset.subset_union_right]
    rfl
  have hYB (B : Finset L) (hB : B ∈ W) :
      ∃ a b, a ≠ b ∧ B = {a, b} ∧ ∀ z, Y B z = (V a b ⬝ᵥ z) ^ mult B := by
    obtain ⟨a, b, hab, rfl⟩ := hblock B hB
    refine ⟨a, b, hab, rfl, fun z => ?_⟩
    simp only [Y]
    rw [pairWeight_pair (Cz z) (hCsymm z) hab]
  have hmult0 (B : Finset L) (hB : B ∉ W) : mult B = 0 := by
    have h1 : B ∉ P₀.1.parts := fun h => hB (Finset.mem_union_left _ h)
    have h2 : B ∉ P.1.parts := fun h => hB (Finset.mem_union_right _ h)
    simp [mult, h1, h2]
  let S : Finset L → Finset D := fun B =>
    if B ∈ W then Finset.univ.filter fun k => ∃ a b, a ≠ b ∧ B = {a, b} ∧ V a b k ≠ 0 else ∅
  have hS : ∀ v w, v ≠ w → Disjoint (S v) (S w) := by
    intro v w hvw
    by_cases hv : v ∈ W
    · by_cases hw : w ∈ W
      · simp only [S, hv, hw, ite_true]
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
        obtain ⟨a, b, hab, rfl, hk1⟩ := hk1
        obtain ⟨a', b', hab', rfl, hk2⟩ := hk2
        rcases hdisj a b a' b' hab hab' hvw k with h | h
        · exact hk1 h
        · exact hk2 h
      · simp [S, hw]
    · simp [S, hv]
  have hYm : ∀ B, Measurable (Y B) := by
    intro B
    by_cases hB : B ∈ W
    · obtain ⟨a, b, hab, hBe, hform⟩ := hYB B hB
      have : Y B = fun z => (V a b ⬝ᵥ z) ^ mult B := funext hform
      rw [this]
      exact (Finset.measurable_sum _ fun i _ =>
        measurable_const.mul (measurable_pi_apply i)).pow_const _
    · have : Y B = fun _ => 1 := funext fun z => by simp [Y, hmult0 B hB]
      rw [this]
      exact measurable_const
  have hY : ∀ B (z z' : D → ℝ), (∀ d ∈ S B, z d = z' d) → Y B z = Y B z' := by
    intro B z z' hzz
    by_cases hB : B ∈ W
    · obtain ⟨a, b, hab, hBe, hform⟩ := hYB B hB
      rw [hform, hform]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : V a b k = 0
      · simp [hk]
      · have hkS : k ∈ S B := by
          simp only [S, hB, ite_true, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨a, b, hab, hBe, hk⟩
        rw [hzz k hkS]
    · simp [Y, hmult0 B hB]
  have hmain := integral_pi_prod_of_disjoint_supports (gaussianReal 0 1) S hS Y hYm hY W
  have hval (B : Finset L) (hB : B ∈ W) :
      ∫ z, Y B z ∂(Measure.pi fun _ : D => gaussianReal 0 1) =
        if B ∈ P₀.1.parts ∧ B ∈ P.1.parts then s else 0 := by
    obtain ⟨a, b, hab, hBe, hform⟩ := hYB B hB
    have h0 : (fun z => Y B z) = fun z => (V a b ⬝ᵥ z) ^ mult B := funext hform
    rw [h0]
    by_cases hc : B ∈ P₀.1.parts ∧ B ∈ P.1.parts
    · have hm : mult B = 2 := by simp [mult, hc.1, hc.2]
      simp only [hc, hm, pow_two]
      rw [ProbabilityTheory.integral_dotProduct_mul_dotProduct_pi_gaussianReal, hnorm a b hab]
      simp
    · have hm : mult B = 1 := by
        rcases Finset.mem_union.1 hB with h | h
        · have h2 : B ∉ P.1.parts := fun h2 => hc ⟨h, h2⟩
          simp [mult, h, h2]
        · have h1 : B ∉ P₀.1.parts := fun h1 => hc ⟨h1, h⟩
          simp [mult, h, h1]
      simp only [hc, hm, ↓reduceIte, pow_one]
      exact ProbabilityTheory.integral_dotProduct_pi_gaussianReal _
  simp_rw [show ∀ z, P₀.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z) *
      P.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z) = ∏ B ∈ W, Y B z from hint]
  rw [hmain]
  exact Finset.prod_congr rfl hval

/-- **Same pairing.** The Gaussian mean of the square of a pairing's block product is `s` to the
number of blocks. -/
theorem integral_pi_gaussian_pairing_sq [Fintype L] (V : L → L → D → ℝ)
    (hVs : ∀ a b, V a b = V b a)
    (hdisj : ∀ a b a' b' : L, a ≠ b → a' ≠ b' → ({a, b} : Finset L) ≠ {a', b'} →
      ∀ k, V a b k = 0 ∨ V a' b' k = 0)
    (s : ℝ) (hnorm : ∀ a b : L, a ≠ b → V a b ⬝ᵥ V a b = s)
    (P : Finpartition.Pairing (Finset.univ : Finset L)) :
    ∫ z : D → ℝ, P.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z) *
        P.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z)
      ∂(Measure.pi fun _ : D => gaussianReal 0 1) = s ^ P.1.parts.card := by
  rw [integral_pi_gaussian_two_pairings_eq_prod V hVs hdisj s hnorm P P, Finset.union_self]
  rw [Finset.prod_congr rfl (g := fun _ => s) (fun B hB => by simp [hB]), Finset.prod_const]

/-- **Different pairings.** The Gaussian mean vanishes: a block of one pairing that is not a
block of the other occurs once, and its linear form is centered and independent of the rest. -/
theorem integral_pi_gaussian_two_pairings_of_ne [Fintype L] (V : L → L → D → ℝ)
    (hVs : ∀ a b, V a b = V b a)
    (hdisj : ∀ a b a' b' : L, a ≠ b → a' ≠ b' → ({a, b} : Finset L) ≠ {a', b'} →
      ∀ k, V a b k = 0 ∨ V a' b' k = 0)
    (s : ℝ) (hnorm : ∀ a b : L, a ≠ b → V a b ⬝ᵥ V a b = s)
    (P₀ P : Finpartition.Pairing (Finset.univ : Finset L)) (hne : P ≠ P₀) :
    ∫ z : D → ℝ, P₀.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z) *
        P.blockProduct (pairWeight fun a b => V a b ⬝ᵥ z)
      ∂(Measure.pi fun _ : D => gaussianReal 0 1) = 0 := by
  rw [integral_pi_gaussian_two_pairings_eq_prod V hVs hdisj s hnorm P₀ P]
  have hne' : P.1.parts ≠ P₀.1.parts := fun h => hne (Subtype.ext (Finpartition.ext h))
  obtain ⟨B, hBW, hB⟩ : ∃ B ∈ P₀.1.parts ∪ P.1.parts,
      ¬(B ∈ P₀.1.parts ∧ B ∈ P.1.parts) := by
    by_contra hcon
    push Not at hcon
    exact hne' (Finset.ext fun B => ⟨fun hB => (hcon B (Finset.mem_union_right _ hB)).1,
      fun hB => (hcon B (Finset.mem_union_left _ hB)).2⟩)
  exact Finset.prod_eq_zero hBW (by simp [hB])

end Renormalization
