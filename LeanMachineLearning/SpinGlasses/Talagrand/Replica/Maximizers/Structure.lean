/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaCavity

/-!
# The maximizers of `B` (Talagrand, Proposition 1.13.2 and Corollary 1.13.3)

For `β > 0`, a maximizer of `B(G) = A(G) - ¼ ∑ G²` over symmetric matrices with zero diagonal has
all off-diagonal entries equal in absolute value, with the sign pattern `u_ℓ u_ℓ'` of a gauge
transformation (and all entries nonnegative if `h ≠ 0`). Hence the maximum of `B` is attained
at a constant matrix.
-/

@[expose] public section

open Finset Real
open scoped BigOperators

namespace SpinGlasses

variable {n : ℕ}

/-- **Talagrand's `B`, in matrix form:** `B(G) = A(G) - ¼ ∑_{ℓ,ℓ'} G_{ℓℓ'}²`. For a symmetric
matrix with zero diagonal this is `A(g) - ½ ∑_{ℓ<ℓ'} g²`. -/
noncomputable def skReplicaMatObjective (n : ℕ) (β h : ℝ) (G : Fin n → Fin n → ℝ) : ℝ :=
  skReplicaMatLogPartition n β h G - (∑ l, ∑ l', G l l' ^ 2) / 4

theorem skReplicaMatObjective_def (n : ℕ) (β h : ℝ) (G : Fin n → Fin n → ℝ) :
    skReplicaMatObjective n β h G =
      skReplicaMatLogPartition n β h G - (∑ l, ∑ l', G l l' ^ 2) / 4 := rfl

/-- If `|G_ab|`'s neighbour `G_bc` is nonzero at a maximizer, then `|G_ab| = |G_bc|`: the first
step of the proof of Proposition 1.13.2. -/
theorem skReplica_abs_eq_of_ne_zero (β h : ℝ) (hβ : 0 < β) (G : Fin n → Fin n → ℝ)
    (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0)
    (hmax : ∀ H : Fin n → Fin n → ℝ, (∀ l l', H l l' = H l' l) → (∀ l, H l l = 0) →
      skReplicaMatObjective n β h H ≤ skReplicaMatObjective n β h G)
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hne : G b c ≠ 0) :
    |G a b| = |G b c| := by
  have h1 := skReplica_lemma_1_13_5 β h hβ a b hab G hs hd hmax
  obtain ⟨-, h2, -, -⟩ := h1
  -- `G'' = collapse G b a` is again a maximizer
  have hmax'' : ∀ H : Fin n → Fin n → ℝ, (∀ l l', H l l' = H l' l) → (∀ l, H l l = 0) →
      skReplicaMatObjective n β h H ≤ skReplicaMatObjective n β h (skReplicaCollapse G b a) := by
    intro H hHs hHd
    have := hmax H hHs hHd
    simp only [skReplicaMatObjective_def] at this ⊢
    linarith
  have hs'' := skReplicaCollapse_symm G b a hs
  have hd'' := skReplicaCollapse_diag G b a hab.symm hd
  have hgac : skReplicaCollapse G b a a c = G b c :=
    skReplicaCollapse_b_rest G b a hab.symm c ⟨hbc.symm, hac.symm⟩
  have hne'' : skReplicaCollapse G b a a c ≠ 0 := by rw [hgac]; exact hne
  have h3 := skReplica_lemma_1_13_5 β h hβ a c hac (skReplicaCollapse G b a) hs'' hd'' hmax''
  obtain ⟨-, -, hpos, hneg⟩ := h3
  have hga_b : skReplicaCollapse G b a a b = |G a b| := by
    rw [skReplicaCollapse_symm G b a hs a b, skReplicaCollapse_ab G b a hab.symm hd, hs b a]
  have hgc_b : skReplicaCollapse G b a c b = G b c := by
    rw [skReplicaCollapse_symm G b a hs c b]
    exact skReplicaCollapse_a_rest G b a hab.symm c ⟨hbc.symm, hac.symm⟩
  rcases lt_or_gt_of_ne hne'' with hlt | hgt
  · have := (hneg hlt).2 b hab.symm hbc
    rw [hga_b, hgc_b] at this
    rw [hgac] at hlt
    rw [abs_of_neg hlt, this]
  · have := hpos hgt b hab.symm hbc
    rw [hga_b, hgc_b] at this
    rw [hgac] at hgt
    rw [abs_of_pos hgt, this]

/-- **First half of Proposition 1.13.2.** At a maximizer all off-diagonal entries have the same
absolute value `|G_xy|`, where `G_xy` is any nonzero entry. -/
theorem skReplica_abs_const (β h : ℝ) (hβ : 0 < β) (G : Fin n → Fin n → ℝ)
    (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0)
    (hmax : ∀ H : Fin n → Fin n → ℝ, (∀ l l', H l l' = H l' l) → (∀ l, H l l = 0) →
      skReplicaMatObjective n β h H ≤ skReplicaMatObjective n β h G)
    {x y : Fin n} (hxy : G x y ≠ 0) (u v : Fin n) (huv : u ≠ v) : |G u v| = |G x y| := by
  have hxy' : x ≠ y := fun h => hxy (h ▸ hd x)
  -- pairs sharing a vertex with a nonzero pair
  have hshare : ∀ {b c : Fin n}, G b c ≠ 0 → ∀ a, a ≠ b → a ≠ c →
      |G a b| = |G b c| ∧ |G a c| = |G b c| := by
    intro b c hbc a hab hac
    have hbc' : b ≠ c := fun h => hbc (h ▸ hd b)
    refine ⟨skReplica_abs_eq_of_ne_zero β h hβ G hs hd hmax hab hac hbc' hbc, ?_⟩
    have := skReplica_abs_eq_of_ne_zero β h hβ G hs hd hmax (a := a) (b := c) (c := b) hac hab
      hbc'.symm (by rwa [hs c b])
    rw [this, hs c b]
  have hS1 : ∀ a, a ≠ x → a ≠ y → |G a x| = |G x y| ∧ |G a y| = |G x y| :=
    fun a hax hay => hshare hxy a hax hay
  have hV : 0 < |G x y| := abs_pos.2 hxy
  by_cases hux : u = x
  · subst hux
    by_cases hvy : v = y
    · subst hvy; rfl
    · rw [hs]
      exact (hS1 v (Ne.symm huv) hvy).1
  · by_cases huy : u = y
    · subst huy
      by_cases hvx : v = x
      · subst hvx; rw [hs]
      · rw [hs]
        exact (hS1 v hvx (Ne.symm huv)).2
    · by_cases hvx : v = x
      · subst hvx
        exact (hS1 u hux huy).1
      · by_cases hvy : v = y
        · subst hvy
          exact (hS1 u hux huy).2
        · have h1 := (hS1 u hux huy).1
          have hne : G u x ≠ 0 := fun h0 => by rw [h0, abs_zero] at h1; exact hV.ne h1
          have := (hshare hne v huv.symm hvx).1
          rw [hs u v, this, h1]

/-- **Proposition 1.13.2, for `β > 0`.** A maximizer `G` of `B` is either zero or has the form
`G_ℓℓ' = V u_ℓ u_ℓ'` (`ℓ ≠ ℓ'`) with `V > 0` and signs `u_ℓ`; if `h ≠ 0` all entries equal `V`. -/
theorem skReplica_maximizer_structure (β h : ℝ) (hβ : 0 < β) (G : Fin n → Fin n → ℝ)
    (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0)
    (hmax : ∀ H : Fin n → Fin n → ℝ, (∀ l l', H l l' = H l' l) → (∀ l, H l l = 0) →
      skReplicaMatObjective n β h H ≤ skReplicaMatObjective n β h G) :
    (∀ l l', G l l' = 0) ∨ ∃ V : ℝ, 0 < V ∧ ∃ u : Fin n → ℤˣ,
      (∀ l l', l ≠ l' → G l l' = V * ((u l : ℤ) : ℝ) * ((u l' : ℤ) : ℝ)) ∧
      (h ≠ 0 → ∀ l l', l ≠ l' → G l l' = V) := by
  by_cases hall : ∀ l l', G l l' = 0
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨x, y, hxy⟩ := hall
  set V : ℝ := |G x y| with hVdef
  have hV : 0 < V := abs_pos.2 hxy
  have habs : ∀ a b, a ≠ b → |G a b| = V := fun a b hab =>
    skReplica_abs_const β h hβ G hs hd hmax hxy a b hab
  have hsgn : ∀ a b, a ≠ b → G a b = V ∨ G a b = -V := fun a b hab => by
    rcases abs_eq (le_of_lt hV) |>.1 (habs a b hab) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  -- the relations of Lemma 1.13.5
  have hrel : ∀ a b l, a ≠ b → l ≠ a → l ≠ b →
      (G a b = V → G a l = G b l) ∧ (G a b = -V → h = 0 ∧ G a l = -G b l) := by
    intro a b l hab hla hlb
    obtain ⟨-, -, hpos, hneg⟩ := skReplica_lemma_1_13_5 β h hβ a b hab G hs hd hmax
    exact ⟨fun hp => hpos (by rw [hp]; exact hV) l hla hlb,
      fun hn => hneg (by rw [hn]; linarith) |> fun t => ⟨t.1, t.2 l hla hlb⟩⟩
  have hx_ne : x ≠ y := fun h' => hxy (h' ▸ hd x)
  classical
  let u : Fin n → ℤˣ := fun l => if l = x then 1 else if 0 < G x l then 1 else -1
  have hu_x : ((u x : ℤˣ) : ℤ) = 1 := by simp [u]
  have hu : ∀ l, l ≠ x → G x l = V * ((u l : ℤ) : ℝ) := by
    intro l hl
    rcases hsgn x l (Ne.symm hl) with h1 | h1
    · have hpos : 0 < G x l := by rw [h1]; exact hV
      have hul : u l = 1 := by simp [u, hl, hpos]
      rw [hul, h1]
      simp
    · have hnpos : ¬ 0 < G x l := by rw [h1]; linarith
      have hul : u l = -1 := by simp [u, hl, hnpos]
      rw [hul, h1]
      simp
  have hh0 : ∀ a b, a ≠ b → G a b = -V → h = 0 := by
    intro a b hab hn
    obtain ⟨-, -, -, hneg⟩ := skReplica_lemma_1_13_5 β h hβ a b hab G hs hd hmax
    exact (hneg (by rw [hn]; linarith)).1
  refine ⟨V, hV, u, fun l l' hll' => ?_, fun hh l l' hll' => ?_⟩
  · by_cases hlx : l = x
    · subst hlx
      rw [hu l' (Ne.symm hll'), hu_x]
      simp
    · by_cases hl'x : l' = x
      · subst hl'x
        rw [hs, hu l hlx, hu_x]
        simp
      · -- both differ from `x`
        have h3 := hu l' hl'x
        have h2 := hu l hlx
        rcases hsgn x l (Ne.symm hlx) with h1 | h1
        · have := (hrel x l l' (Ne.symm hlx) hl'x hll'.symm).1 h1
          have hul : ((u l : ℤ) : ℝ) = 1 := by
            rw [h1] at h2
            have h4 : V * 1 = V * ((u l : ℤ) : ℝ) := by rw [mul_one]; exact h2
            exact (mul_left_cancel₀ hV.ne' h4).symm
          rw [← this, h3, hul]
          ring
        · have := ((hrel x l l' (Ne.symm hlx) hl'x hll'.symm).2 h1).2
          have hul : ((u l : ℤ) : ℝ) = -1 := by
            rw [h1] at h2
            have h4 : V * (-1) = V * ((u l : ℤ) : ℝ) := by rw [mul_neg_one]; exact h2
            exact (mul_left_cancel₀ hV.ne' h4).symm
          rw [hul]
          linarith
  · rcases hsgn l l' hll' with h1 | h1
    · exact h1
    · exact absurd (hh0 l l' hll' h1) hh

/-- The gauge transformation `ε_ℓ ↦ u_ℓ ε_ℓ` leaves `A` unchanged when `h = 0` and the couplings
are `V u_ℓ u_ℓ'`. -/
theorem skReplicaMatLogPartition_gauge (β V : ℝ) (G : Fin n → Fin n → ℝ) (u : Fin n → ℤˣ)
    (hG : ∀ l l', l ≠ l' → G l l' = V * ((u l : ℤ) : ℝ) * ((u l' : ℤ) : ℝ))
    (hd : ∀ l, G l l = 0) :
    skReplicaMatLogPartition n β 0 G =
      skReplicaMatLogPartition n β 0 (fun l l' => if l = l' then 0 else V) := by
  simp only [skReplicaMatLogPartition_def]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun ε => ?_
  simp only [zero_mul, add_zero]
  congr 2
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  by_cases hll : l = l'
  · subst hll
    simp [hd]
  · simp only [Equiv.coe_mulLeft, Pi.mul_apply, Units.val_mul, Int.cast_mul, hll, ite_false,
      hG l l' hll]
    ring

/-- **Corollary 1.13.3, for `β > 0`.** The maximum of `B` is attained at a matrix whose
off-diagonal entries are all equal to some `V ≥ 0`: every maximizer has the same value of `B` as
such a constant matrix. -/
theorem skReplica_maximizer_const (β h : ℝ) (hβ : 0 < β) (G : Fin n → Fin n → ℝ)
    (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0)
    (hmax : ∀ H : Fin n → Fin n → ℝ, (∀ l l', H l l' = H l' l) → (∀ l, H l l = 0) →
      skReplicaMatObjective n β h H ≤ skReplicaMatObjective n β h G) :
    ∃ V : ℝ, 0 ≤ V ∧ skReplicaMatObjective n β h G =
      skReplicaMatObjective n β h (fun l l' => if l = l' then 0 else V) := by
  rcases skReplica_maximizer_structure β h hβ G hs hd hmax with hzero | ⟨V, hV, u, hG, hpos⟩
  · refine ⟨0, le_rfl, ?_⟩
    congr 2
    funext l l'
    simp [hzero]
  · by_cases hh : h = 0
    · subst hh
      refine ⟨V, hV.le, ?_⟩
      simp only [skReplicaMatObjective_def]
      rw [skReplicaMatLogPartition_gauge β V G u hG hd]
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
      by_cases hll : l = l'
      · subst hll; simp [hd]
      · simp only [hll, ite_false, hG l l' hll]
        have h1 : ((u l : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
        have h2 : ((u l' : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
        calc (V * ((u l : ℤ) : ℝ) * ((u l' : ℤ) : ℝ)) ^ 2
            = V ^ 2 * (((u l : ℤ) : ℝ) ^ 2) * (((u l' : ℤ) : ℝ) ^ 2) := by ring
          _ = V ^ 2 := by rw [h1, h2]; ring
    · refine ⟨V, hV.le, ?_⟩
      congr 2
      funext l l'
      by_cases hll : l = l'
      · subst hll; simp [hd]
      · simp [hll, hpos hh l l' hll]

end SpinGlasses
