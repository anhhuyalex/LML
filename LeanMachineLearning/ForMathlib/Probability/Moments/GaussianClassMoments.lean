/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.FiniteRecurrence
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# Gaussian class products and uniform finite-factor moment asymptotics

The scalar Gaussian recurrence determines the product of moments in each selected label
class. Combining that exact recurrence with the shared finite-factor error induction
leaves the actual moment of all unselected factors untouched. This is the algebraic
induction common to Talagrand's pair, single and global overlap stages.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace ProbabilityTheory

/-- Rescaling the standard Gaussian moments by powers of a variance coefficient preserves
its two-factor recurrence. No square root or sign assumption on the coefficient is needed. -/
theorem scaled_gaussian_moment_add_two (z : ℝ) (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 2) ∂gaussianReal 0 1) * z ^ ((n + 2) / 2) =
      (n + 1 : ℝ) * z * ((∫ x : ℝ, x ^ n ∂gaussianReal 0 1) * z ^ (n / 2)) := by
  have hd : (n + 2) / 2 = n / 2 + 1 := by omega
  rw [integral_pow_add_two_gaussianReal, hd, pow_succ]
  ring

/-- Deleting two positions in the same selected label class removes one variance factor
and multiplies by the number of possible partners. A singleton class gives zero. -/
theorem prod_gaussian_class_moments_erase_pair
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    (s : Finset J) (t : Finset K) (P : J → Prop) [DecidablePred P]
    (label : J → K) (z : K → ℝ)
    {p u : J} (hp : p ∈ s) (hP : P p) (ht : label p ∈ t)
    (hu : ((s.filter fun j => P j ∧ label j = label p).erase p).Nonempty →
      u ∈ (s.filter fun j => P j ∧ label j = label p).erase p) :
    (∏ k ∈ t, (∫ x : ℝ, x ^ ((s.filter fun j => P j ∧ label j = k).card)
      ∂gaussianReal 0 1) * z k ^ ((s.filter fun j => P j ∧ label j = k).card / 2)) =
      (((s.filter fun j => P j ∧ label j = label p).card - 1 : ℕ) : ℝ) *
        z (label p) *
          ∏ k ∈ t, (∫ x : ℝ,
            x ^ ((((s.erase p).erase u).filter fun j => P j ∧ label j = k).card)
            ∂gaussianReal 0 1) *
              z k ^ ((((s.erase p).erase u).filter fun j => P j ∧ label j = k).card / 2) := by
  apply prod_class_moments_erase_pair s t P label
    (fun k n => (∫ x : ℝ, x ^ n ∂gaussianReal 0 1) * z k ^ (n / 2)) z
    (fun k => by simp) (fun k n => ?_) hp hP ht hu
  simpa only [Nat.cast_add, Nat.cast_one] using scaled_gaussian_moment_add_two (z k) n


/-- A uniform two-factor recurrence gives the Gaussian class product times the actual
unselected moment, with the correct degree-dependent error. The reference is explicit:
no Gaussian assumption is imposed on the unselected factors. A matching partner is needed
only when another selected position has the same label. All constants precede parameters
and system sizes. -/
theorem exists_finset_gaussian_class_moment_error
    {J K Θ : Type*} [DecidableEq J] [Fintype K] [DecidableEq K]
    (P : J → Prop) [DecidablePred P] (label : J → K)
    (valid : Θ → Prop) (F : Θ → ℕ → Finset J → ℝ)
    (c : Θ → ℝ) (B : ℝ) (hc : ∀ θ, valid θ → |c θ| ≤ B)
    (partner : Finset J → J → J)
    (hpartner : ∀ s p, p ∈ s → P p →
      ((s.filter fun j => P j ∧ label j = label p).erase p).Nonempty →
        partner s p ∈ (s.filter fun j => P j ∧ label j = label p).erase p)
    (hF : ∀ s p, p ∈ s → P p → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ, valid θ → ∀ N,
      |F θ N s -
        ((((s.filter fun j => P j ∧ label j = label p).card - 1 : ℕ) : ℝ) *
          c θ / (N + 1 : ℝ)) * F θ N ((s.erase p).erase (partner s p))| ≤
        C / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2)) :
    ∀ s, ∃ C : ℝ, 0 < C ∧ ∀ θ, valid θ → ∀ N,
      |F θ N s -
        (∏ k : K, (∫ x : ℝ, x ^ ((s.filter fun j => P j ∧ label j = k).card)
          ∂gaussianReal 0 1) *
            (c θ / (N + 1 : ℝ)) ^ ((s.filter fun j => P j ∧ label j = k).card / 2)) *
              F θ N (s.filter fun j => ¬P j)| ≤
        C / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  let D : Finset J → J → Finset J := fun s p => (s.erase p).erase (partner s p)
  let w : Finset J → J → ℝ := fun s p =>
    ((s.filter fun j => P j ∧ label j = label p).card - 1 : ℕ)
  let G : Θ → ℕ → Finset J → ℝ := fun θ N s =>
    (∏ k : K, (∫ x : ℝ, x ^ ((s.filter fun j => P j ∧ label j = k).card)
      ∂gaussianReal 0 1) *
        (c θ / (N + 1 : ℝ)) ^ ((s.filter fun j => P j ∧ label j = k).card / 2)) *
          F θ N (s.filter fun j => ¬P j)
  have hdata : ∀ s p, p ∈ s → P p → w s p = 0 ∨
      ((D s p).card + 2 = s.card ∧
        s.filter (fun j => ¬P j) = (D s p).filter (fun j => ¬P j)) := by
    intro s p hp hP
    let cls := s.filter fun j => P j ∧ label j = label p
    have hpc : p ∈ cls := Finset.mem_filter.mpr ⟨hp, hP, rfl⟩
    by_cases hne : (cls.erase p).Nonempty
    · have hu := hpartner s p hp hP hne
      have hus := (Finset.mem_filter.mp (Finset.mem_erase.mp hu).2).1
      have hPu := (Finset.mem_filter.mp (Finset.mem_erase.mp hu).2).2.1
      have hup := (Finset.mem_erase.mp hu).1
      refine Or.inr ⟨?_, ?_⟩
      · change ((s.erase p).erase (partner s p)).card + 2 = s.card
        have h₁ := Finset.card_erase_add_one hp
        have h₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hup, hus⟩)
        omega
      · have hpn : p ∉ s.filter (fun j => ¬P j) := by simp [hP]
        have hun : partner s p ∉ s.filter (fun j => ¬P j) := by simp [hPu]
        dsimp only [D]
        rw [Finset.filter_erase, Finset.filter_erase,
          Finset.erase_eq_of_notMem hpn, Finset.erase_eq_of_notMem hun]
    · apply Or.inl
      change ((cls.card - 1 : ℕ) : ℝ) = 0
      have h := Finset.card_erase_add_one hpc
      rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty] at h
      have he : cls.card - 1 = 0 := by omega
      rw [he, Nat.cast_zero]
  apply exists_finset_moment_error_of_two_factor_recurrence P valid F G c B hc D w
    (fun s p hp hP => (hdata s p hp hP).imp_right And.left) ?_ ?_ hF
  · intro s hnone θ _ N
    have hcounts : ∀ k : K, (s.filter fun j => P j ∧ label j = k).card = 0 := by
      intro k
      apply Finset.card_eq_zero.mpr
      exact Finset.filter_eq_empty_iff.mpr fun j hj h => hnone j hj h.1
    have hs : s.filter (fun j => ¬P j) = s :=
      Finset.filter_eq_self.mpr fun j hj => hnone j hj
    dsimp only [G]
    simp [hcounts, hs]
  · intro s p hp hP θ _ N
    have he := prod_gaussian_class_moments_erase_pair s Finset.univ P label
      (fun _ => c θ / (N + 1 : ℝ)) hp hP (Finset.mem_univ _) (hpartner s p hp hP)
    change _ = (w s p * c θ / (N + 1 : ℝ)) * _
    dsimp only [G]
    rw [he]
    rcases hdata s p hp hP with hw | ⟨_, hr⟩
    · change w s p * _ * _ * _ = _
      rw [hw]
      simp
    · change w s p * _ * _ * _ = _
      rw [hr]
      dsimp only [D]
      ring

end ProbabilityTheory
