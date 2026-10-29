/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Uniform error propagation through a two-factor moment recurrence

An approximate recurrence removes two selected factors, with one inverse system-size
factor. If a reference family satisfies the same recurrence exactly, the error retains
its degree-dependent scale. This abstracts the three moment inductions in Talagrand 1.10.
-/

@[expose] public section

open scoped BigOperators

namespace ProbabilityTheory

/-- Rescaling a degree-dependent moment error leaves an inverse-square-root error.
The degree parameter may be any real number, and the scale may be any positive real. -/
theorem abs_normalized_moment_sub_le {m r X G C : ℝ} (hm : 0 < m)
    (h : |X - G / m ^ r| ≤ C / m ^ (r + 1 / 2)) :
    |m ^ r * X - G| ≤ C / Real.sqrt m := by
  have hp : 0 < m ^ r := Real.rpow_pos_of_pos hm r
  have hs : m ^ (r + 1 / 2) = m ^ r * Real.sqrt m := by
    rw [Real.rpow_add hm, ← Real.sqrt_eq_rpow]
  have he : m ^ r * X - G = m ^ r * (X - G / m ^ r) := by
    field_simp
  rw [he, abs_mul, abs_of_pos hp]
  calc m ^ r * |X - G / m ^ r| ≤ m ^ r * (C / m ^ (r + 1 / 2)) :=
      mul_le_mul_of_nonneg_left h hp.le
    _ = C / Real.sqrt m := by rw [hs]; field_simp

/-- A product of class moments satisfies the same two-factor recurrence as each class.
The class index set is any finite set, and the coefficient may depend on the class.
Singleton classes vanish; no partner is required in that case. No cancellation or
nonvanishing moment hypothesis is needed, and the identity holds over a commutative semiring. -/
theorem prod_class_moments_erase_pair
    {J K A : Type*} [DecidableEq J] [DecidableEq K] [CommSemiring A]
    (s : Finset J) (t : Finset K) (P : J → Prop) [DecidablePred P]
    (label : J → K) (f : K → ℕ → A) (z : K → A)
    (hfirst : ∀ k, f k 1 = 0)
    (hrec : ∀ k n, f k (n + 2) = (n + 1 : ℕ) * z k * f k n)
    {p u : J} (hp : p ∈ s) (hP : P p) (ht : label p ∈ t)
    (hu : ((s.filter fun j => P j ∧ label j = label p).erase p).Nonempty →
      u ∈ (s.filter fun j => P j ∧ label j = label p).erase p) :
    (∏ k ∈ t, f k ((s.filter fun j => P j ∧ label j = k).card)) =
      (((s.filter fun j => P j ∧ label j = label p).card - 1 : ℕ) : A) *
        z (label p) *
          ∏ k ∈ t, f k (((s.erase p).erase u).filter fun j => P j ∧ label j = k).card := by
  let cls := s.filter fun j => P j ∧ label j = label p
  have hpc : p ∈ cls := Finset.mem_filter.mpr ⟨hp, hP, rfl⟩
  by_cases hc : (cls.erase p).Nonempty
  · have huc := hu hc
    have hPu := (Finset.mem_filter.mp (Finset.mem_erase.mp huc).2).2
    have hcount :
        ((((s.erase p).erase u).filter fun j => P j ∧ label j = label p).card) + 2 =
          cls.card := by
      have hpos := Finset.card_pos.mpr ⟨u, huc⟩
      rw [Finset.filter_erase, Finset.filter_erase,
        Finset.card_erase_of_mem huc, Finset.card_erase_of_mem hpc]
      rw [Finset.card_erase_of_mem hpc] at hpos
      omega
    have hother : ∀ k ∈ t.erase (label p),
        (((s.erase p).erase u).filter fun j => P j ∧ label j = k) =
          s.filter fun j => P j ∧ label j = k := by
      intro k hk
      have hkne := (Finset.mem_erase.mp hk).1
      have hpn : p ∉ s.filter (fun j => P j ∧ label j = k) := by
        intro hj
        exact hkne (Finset.mem_filter.mp hj).2.2.symm
      have hun : u ∉ s.filter (fun j => P j ∧ label j = k) := by
        intro hj
        exact hkne (hPu.2.symm.trans (Finset.mem_filter.mp hj).2.2).symm
      rw [Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem hpn, Finset.erase_eq_of_notMem hun]
    have hw : cls.card - 1 =
        (((s.erase p).erase u).filter fun j => P j ∧ label j = label p).card + 1 := by
      omega
    have hprod : (∏ k ∈ t.erase (label p), f k (s.filter fun j => P j ∧ label j = k).card) =
        ∏ k ∈ t.erase (label p),
          f k (((s.erase p).erase u).filter fun j => P j ∧ label j = k).card := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [hother k hk]
    rw [← Finset.mul_prod_erase t _ ht, ← Finset.mul_prod_erase t
      (fun k => f k (((s.erase p).erase u).filter fun j => P j ∧ label j = k).card) ht]
    change f (label p) cls.card * _ = ((cls.card - 1 : ℕ) : A) * _ * _
    rw [hw, ← hcount, hrec, hprod]
    ring
  · have he : cls.erase p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
    have hcard : cls.card = 1 := by
      have h := Finset.card_erase_add_one hpc
      rw [he, Finset.card_empty] at h
      omega
    have hzero : (∏ k ∈ t, f k (s.filter fun j => P j ∧ label j = k).card) = 0 := by
      apply Finset.prod_eq_zero ht
      change f (label p) cls.card = 0
      rw [hcard, hfirst]
    change _ = ((cls.card - 1 : ℕ) : A) * _ * _
    rw [hzero, hcard]
    simp

/-- An approximate two-factor recurrence has the same leading term as an exact reference
recurrence. The reference agrees on the unselected base family. All constants precede the
parameter and system size; the coefficient may vary with the parameter but is bounded.
A zero recurrence weight needs no lower-degree hypothesis, covering odd singleton classes. -/
theorem exists_finset_moment_error_of_two_factor_recurrence
    {J Θ : Type*} (P : J → Prop)
    (valid : Θ → Prop) (F G : Θ → ℕ → Finset J → ℝ)
    (c : Θ → ℝ) (B : ℝ) (hc : ∀ θ, valid θ → |c θ| ≤ B)
    (D : Finset J → J → Finset J) (w : Finset J → J → ℝ)
    (hD : ∀ s p, p ∈ s → P p → w s p = 0 ∨ (D s p).card + 2 = s.card)
    (hbase : ∀ s, (∀ p ∈ s, ¬P p) → ∀ θ, valid θ → ∀ N, F θ N s = G θ N s)
    (hG : ∀ s p, p ∈ s → P p → ∀ θ, valid θ → ∀ N,
      G θ N s = (w s p * c θ / (N + 1 : ℝ)) * G θ N (D s p))
    (hF : ∀ s p, p ∈ s → P p → ∃ K : ℝ, 0 ≤ K ∧ ∀ θ, valid θ → ∀ N,
      |F θ N s - (w s p * c θ / (N + 1 : ℝ)) * F θ N (D s p)| ≤
        K / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2)) :
    ∀ s, ∃ K : ℝ, 0 < K ∧ ∀ θ, valid θ → ∀ N,
      |F θ N s - G θ N s| ≤ K / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  classical
  intro s
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
    rw [← hn]
    by_cases hp : (s.filter P).Nonempty
    · obtain ⟨p, hp⟩ := hp
      obtain ⟨hps, hP⟩ := Finset.mem_filter.mp hp
      obtain ⟨K₀, hK₀, hrem⟩ := hF s p hps hP
      rcases hD s p hps hP with hw | hcard
      · refine ⟨K₀ + 1, by positivity, fun θ hθ N => ?_⟩
        rw [hG s p hps hP θ hθ N, hw, zero_mul, zero_div, zero_mul]
        have h := hrem θ hθ N
        rw [hw, zero_mul, zero_div, zero_mul] at h
        exact h.trans (div_le_div_of_nonneg_right
          (le_add_of_nonneg_right zero_le_one) (by positivity))
      · obtain ⟨K₁, hK₁, hprev⟩ := ih (D s p).card (by omega) (D s p) rfl
        refine ⟨K₀ + |w s p| * |B| * K₁ + 1, by positivity, fun θ hθ N => ?_⟩
        have hm : (0 : ℝ) < N + 1 := by positivity
        have hcoeff : |w s p * c θ / (N + 1 : ℝ)| ≤
            |w s p| * |B| / (N + 1 : ℝ) := by
          rw [abs_div, abs_mul, abs_of_pos hm]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left ((hc θ hθ).trans (le_abs_self B)) (abs_nonneg _)) hm.le
        have hscale : (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2) =
            (N + 1 : ℝ) * (N + 1 : ℝ) ^ ((((D s p).card + 1 : ℕ) : ℝ) / 2) := by
          have hexp : ((s.card + 1 : ℕ) : ℝ) / 2 =
              1 + (((D s p).card + 1 : ℕ) : ℝ) / 2 := by
            rw [← hcard]
            push_cast
            ring
          rw [hexp, Real.rpow_add hm, Real.rpow_one]
        rw [hG s p hps hP θ hθ N]
        calc
          _ ≤ |F θ N s - (w s p * c θ / (N + 1 : ℝ)) * F θ N (D s p)| +
              |(w s p * c θ / (N + 1 : ℝ)) * F θ N (D s p) -
                (w s p * c θ / (N + 1 : ℝ)) * G θ N (D s p)| := abs_sub_le _ _ _
          _ = |F θ N s - (w s p * c θ / (N + 1 : ℝ)) * F θ N (D s p)| +
              |w s p * c θ / (N + 1 : ℝ)| * |F θ N (D s p) - G θ N (D s p)| := by
            rw [← mul_sub, abs_mul]
          _ ≤ K₀ / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2) +
              (|w s p| * |B| / (N + 1 : ℝ)) *
                (K₁ / (N + 1 : ℝ) ^ ((((D s p).card + 1 : ℕ) : ℝ) / 2)) :=
            add_le_add (hrem θ hθ N)
              (mul_le_mul hcoeff (hprev θ hθ N) (abs_nonneg _) (by positivity))
          _ = (K₀ + |w s p| * |B| * K₁) /
              (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
            rw [div_mul_div_comm, ← hscale, add_div]
          _ ≤ _ := div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
            (by positivity)
    · refine ⟨1, by norm_num, fun θ hθ N => ?_⟩
      have hnone : ∀ p ∈ s, ¬P p := by
        intro p hps hP
        exact hp ⟨p, Finset.mem_filter.mpr ⟨hps, hP⟩⟩
      rw [hbase s hnone θ hθ N, sub_self, abs_zero]
      positivity

end ProbabilityTheory
