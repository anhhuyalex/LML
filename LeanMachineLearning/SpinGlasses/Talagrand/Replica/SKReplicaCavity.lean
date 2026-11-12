/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaMoment
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaHyperbolic

/-!
# The two-replica decomposition of `exp A(g)` (Talagrand, proof of Lemma 1.13.5)

For a symmetric coupling matrix `G` with zero diagonal and two distinct replicas `a, b`,
summing over the signs `ε_a, ε_b` first gives
`exp A(G) = 4 ∑_α w(α) (ch A₁ ch A₂ ch (β G_ab) + sh A₁ sh A₂ sh (β G_ab))`,
where `α` ranges over the signs of the other replicas.
-/

@[expose] public section

open Finset Real
open scoped BigOperators

namespace SpinGlasses

variable {n : ℕ}

/-- The logarithm of the one-site partition function of `n` replicas, for a symmetric coupling
matrix `G` (the diagonal is ignored). It equals `A(g)` for `G = Gext g`; the matrix form makes the
relabelling of replicas in the proof of Lemma 1.13.5 transparent. -/
noncomputable def skReplicaMatLogPartition (n : ℕ) (β h : ℝ) (G : Fin n → Fin n → ℝ) : ℝ :=
  Real.log (∑ ε : Fin n → ℤˣ, Real.exp (β / 2 * ∑ l, ∑ l', G l l' * ((ε l : ℤ) : ℝ) *
    ((ε l' : ℤ) : ℝ) + h * ∑ l, ((ε l : ℤ) : ℝ)))

/-- Definitional equality for `skReplicaMatLogPartition`. -/
theorem skReplicaMatLogPartition_def (n : ℕ) (β h : ℝ) (G : Fin n → Fin n → ℝ) :
    skReplicaMatLogPartition n β h G =
      Real.log (∑ ε : Fin n → ℤˣ, Real.exp (β / 2 * ∑ l, ∑ l', G l l' * ((ε l : ℤ) : ℝ) *
        ((ε l' : ℤ) : ℝ) + h * ∑ l, ((ε l : ℤ) : ℝ))) := rfl

/-- The exponential of `skReplicaMatLogPartition` is the partition sum. -/
@[simp]
theorem exp_skReplicaMatLogPartition (n : ℕ) (β h : ℝ) (G : Fin n → Fin n → ℝ) :
    Real.exp (skReplicaMatLogPartition n β h G) =
      ∑ ε : Fin n → ℤˣ, Real.exp (β / 2 * ∑ l, ∑ l', G l l' * ((ε l : ℤ) : ℝ) *
        ((ε l' : ℤ) : ℝ) + h * ∑ l, ((ε l : ℤ) : ℝ)) := by
  rw [skReplicaMatLogPartition_def]
  exact Real.exp_log (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)

/-- The signs of the replicas other than `a` and `b` determine, together with `ε_a` and `ε_b`,
a sign configuration of all replicas. -/
def epsSplit (a b : Fin n) (hab : a ≠ b) :
    (Fin n → ℤˣ) ≃ ℤˣ × ℤˣ × ({l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) where
  toFun ε := (ε a, ε b, fun l => ε l.val)
  invFun t l := if h : l = a then t.1 else if h' : l = b then t.2.1 else t.2.2 ⟨l, h, h'⟩
  left_inv ε := by
    funext l
    by_cases h : l = a
    · subst h; simp
    · by_cases h' : l = b
      · subst h'; simp [h]
      · simp [h, h']
  right_inv t := by
    obtain ⟨x, y, α⟩ := t
    refine Prod.ext (by simp) (Prod.ext ?_ ?_)
    · simp [hab.symm]
    · funext l
      simp [l.property.1, l.property.2]

theorem epsSplit_symm_a (a b : Fin n) (hab : a ≠ b) (x y : ℤˣ)
    (α : {l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) : (epsSplit a b hab).symm (x, y, α) a = x := by
  simp [epsSplit]

theorem epsSplit_symm_b (a b : Fin n) (hab : a ≠ b) (x y : ℤˣ)
    (α : {l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) : (epsSplit a b hab).symm (x, y, α) b = y := by
  simp [epsSplit, hab.symm]

theorem epsSplit_symm_rest (a b : Fin n) (hab : a ≠ b) (x y : ℤˣ)
    (α : {l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) (l : {l : Fin n // l ≠ a ∧ l ≠ b}) :
    (epsSplit a b hab).symm (x, y, α) l.val = α l := by
  simp [epsSplit, l.property.1, l.property.2]

/-- A sum over `Fin n` splits into the terms `a`, `b` and the sum over the other indices. -/
theorem sum_fin_split (a b : Fin n) (hab : a ≠ b) (f : Fin n → ℝ) :
    ∑ l, f l = f a + f b + ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, f l.val := by
  have h1 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, f l.val =
      ∑ l ∈ (univ.erase a).erase b, f l := by
    refine (Finset.sum_subtype ((univ.erase a).erase b) (p := fun l : Fin n => l ≠ a ∧ l ≠ b)
      (fun l => ?_) f).symm
    simp only [mem_erase, mem_univ, and_true]
    tauto
  rw [h1, add_assoc, Finset.add_sum_erase _ _ (mem_erase.2 ⟨hab.symm, mem_univ b⟩),
    Finset.add_sum_erase _ _ (mem_univ a)]

/-- The quadratic form of a symmetric matrix with zero diagonal, split along two indices. -/
theorem quad_split (a b : Fin n) (hab : a ≠ b) (G : Fin n → Fin n → ℝ)
    (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0) (e : Fin n → ℝ) :
    ∑ l, ∑ l', G l l' * e l * e l' =
      2 * G a b * e a * e b + 2 * e a * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * e l.val +
        2 * e b * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * e l.val +
        ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
          G l.val l'.val * e l.val * e l'.val := by
  have hin (l : Fin n) : ∑ l', G l l' * e l * e l' = G l a * e l * e a + G l b * e l * e b +
      ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b}, G l l'.val * e l * e l'.val :=
    sum_fin_split a b hab (fun l' => G l l' * e l * e l')
  simp_rw [hin]
  rw [sum_fin_split a b hab]
  simp only [Finset.sum_add_distrib, hd, hs b a, zero_mul]
  have h1 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G l.val a * e l.val * e a =
      e a * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * e l.val := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hs l.val a]; ring
  have h2 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G l.val b * e l.val * e b =
      e b * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * e l.val := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hs l.val b]; ring
  have h3 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
      G l.val l'.val * e l.val * e l'.val = ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
        ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b}, G l.val l'.val * e l.val * e l'.val := rfl
  have h4 : ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l'.val * e a * e l'.val =
      e a * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * e l.val := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h5 : ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l'.val * e b * e l'.val =
      e b * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * e l.val := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h1, h2, h4, h5]
  ring

/-- The four-term identity behind Eq. (1.407): summing over two signs gives hyperbolic
functions. -/
theorem sum_units_exp_four (A₁ A₂ γ : ℝ) :
    ∑ x : ℤˣ, ∑ y : ℤˣ, Real.exp (((x : ℤ) : ℝ) * A₁ + ((y : ℤ) : ℝ) * A₂ +
        γ * ((x : ℤ) : ℝ) * ((y : ℤ) : ℝ)) =
      4 * (cosh A₁ * cosh A₂ * cosh γ + sinh A₁ * sinh A₂ * sinh γ) := by
  simp only [sum_units_int]
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_mul, mul_one,
    mul_neg, neg_neg, Real.cosh_eq, Real.sinh_eq]
  simp only [Real.exp_add, Real.exp_neg]
  have h1 := Real.exp_pos A₁
  have h2 := Real.exp_pos A₂
  have h3 := Real.exp_pos γ
  field_simp
  ring

/-- **The decomposition (1.407).** For two distinct replicas `a, b`, `exp A(G)` is the sum over
the signs `α` of the other replicas of the weight `w(α)` times
`4 (ch A₁ ch A₂ ch (β G_ab) + sh A₁ sh A₂ sh (β G_ab))`. -/
theorem exp_skReplicaMatLogPartition_split (a b : Fin n) (hab : a ≠ b) (β h : ℝ)
    (G : Fin n → Fin n → ℝ) (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0) :
    Real.exp (skReplicaMatLogPartition n β h G) =
      ∑ α : {l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ,
        Real.exp (β / 2 * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
            ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
            G l.val l'.val * ((α l : ℤ) : ℝ) * ((α l' : ℤ) : ℝ) +
          h * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ((α l : ℤ) : ℝ)) *
        (4 * (cosh (β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * ((α l : ℤ) : ℝ) + h) *
              cosh (β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * ((α l : ℤ) : ℝ) + h) *
              cosh (β * G a b) +
            sinh (β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * ((α l : ℤ) : ℝ) + h) *
              sinh (β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * ((α l : ℤ) : ℝ) + h) *
              sinh (β * G a b))) := by
  rw [exp_skReplicaMatLogPartition]
  rw [← Fintype.sum_equiv (epsSplit a b hab).symm (fun t => Real.exp (β / 2 * ∑ l, ∑ l',
      G l l' * (((epsSplit a b hab).symm t l : ℤˣ) : ℝ) *
        (((epsSplit a b hab).symm t l' : ℤˣ) : ℝ) +
      h * ∑ l, (((epsSplit a b hab).symm t l : ℤˣ) : ℝ)))
    (fun ε => Real.exp (β / 2 * ∑ l, ∑ l', G l l' * ((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ) +
      h * ∑ l, ((ε l : ℤ) : ℝ))) (fun t => rfl)]
  have hterm (x y : ℤˣ) (α : {l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) :
      Real.exp (β / 2 * ∑ l, ∑ l', G l l' * (((epsSplit a b hab).symm (x, y, α) l : ℤˣ) : ℝ) *
        (((epsSplit a b hab).symm (x, y, α) l' : ℤˣ) : ℝ) +
        h * ∑ l, (((epsSplit a b hab).symm (x, y, α) l : ℤˣ) : ℝ)) =
      Real.exp (β / 2 * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
            ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
            G l.val l'.val * ((α l : ℤ) : ℝ) * ((α l' : ℤ) : ℝ) +
          h * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ((α l : ℤ) : ℝ)) *
        Real.exp (((x : ℤ) : ℝ) * (β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
              G a l.val * ((α l : ℤ) : ℝ) + h) +
          ((y : ℤ) : ℝ) * (β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
              G b l.val * ((α l : ℤ) : ℝ) + h) +
          (β * G a b) * ((x : ℤ) : ℝ) * ((y : ℤ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    have hq := quad_split a b hab G hs hd
      (fun l => (((epsSplit a b hab).symm (x, y, α) l : ℤˣ) : ℝ))
    simp only [epsSplit_symm_a, epsSplit_symm_b, epsSplit_symm_rest] at hq
    rw [hq]
    rw [sum_fin_split a b hab (fun l => (((epsSplit a b hab).symm (x, y, α) l : ℤˣ) : ℝ))]
    simp only [epsSplit_symm_a, epsSplit_symm_b, epsSplit_symm_rest]
    ring
  simp_rw [Fintype.sum_prod_type, hterm]
  have hreorder (f : ℤˣ → ℤˣ → ({l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) → ℝ) :
      ∑ x, ∑ y, ∑ α, f x y α = ∑ α, ∑ x, ∑ y, f x y α := by
    calc ∑ x, ∑ y, ∑ α, f x y α = ∑ x, ∑ α, ∑ y, f x y α :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ α, ∑ x, ∑ y, f x y α := Finset.sum_comm
  refine (hreorder _).trans (Finset.sum_congr rfl fun α _ => ?_)
  simp_rw [← Finset.mul_sum]
  rw [sum_units_exp_four]

/-- **The coupling `g′` of Lemma 1.13.5, in matrix form:** replica `b` takes over the couplings of
replica `a`, and the coupling between `a` and `b` becomes `|G_ab|`. The coupling `g″` is
`skReplicaCollapse G b a`. -/
def skReplicaCollapse (G : Fin n → Fin n → ℝ) (a b : Fin n) : Fin n → Fin n → ℝ :=
  fun l l' => G (Function.update id b a l) (Function.update id b a l') +
    if (l = a ∧ l' = b) ∨ (l = b ∧ l' = a) then |G a b| else 0

/-- Evaluation lemma for `skReplicaCollapse`. -/
@[simp]
theorem skReplicaCollapse_apply (G : Fin n → Fin n → ℝ) (a b : Fin n) (l l' : Fin n) :
    skReplicaCollapse G a b l l' =
      G (Function.update id b a l) (Function.update id b a l') +
        if (l = a ∧ l' = b) ∨ (l = b ∧ l' = a) then |G a b| else 0 := rfl

section Collapse

variable (G : Fin n → Fin n → ℝ) (a b : Fin n)

theorem skReplicaCollapse_symm (hs : ∀ l l', G l l' = G l' l) (l l' : Fin n) :
    skReplicaCollapse G a b l l' = skReplicaCollapse G a b l' l := by
  simp only [skReplicaCollapse_apply]
  rw [hs (Function.update id b a l) (Function.update id b a l')]
  congr 1
  by_cases h : (l = a ∧ l' = b) ∨ (l = b ∧ l' = a)
  · have h' : (l' = a ∧ l = b) ∨ (l' = b ∧ l = a) := by tauto
    simp [h, h']
  · have h' : ¬ ((l' = a ∧ l = b) ∨ (l' = b ∧ l = a)) := by tauto
    simp [h, h']

theorem skReplicaCollapse_diag (hab : a ≠ b) (hd : ∀ l, G l l = 0) (l : Fin n) :
    skReplicaCollapse G a b l l = 0 := by
  have h : ¬ ((l = a ∧ l = b) ∨ (l = b ∧ l = a)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hab (h1.symm.trans h2)
    · exact hab (h2.symm.trans h1)
  simp [skReplicaCollapse_apply, hd, h]

theorem skReplicaCollapse_rest (l l' : Fin n) (hl : l ≠ a ∧ l ≠ b) (hl' : l' ≠ a ∧ l' ≠ b) :
    skReplicaCollapse G a b l l' = G l l' := by
  simp [skReplicaCollapse_apply, hl.1, hl.2, hl'.1, hl'.2]

theorem skReplicaCollapse_a_rest (hab : a ≠ b) (l : Fin n) (hl : l ≠ a ∧ l ≠ b) :
    skReplicaCollapse G a b a l = G a l := by
  simp [skReplicaCollapse_apply, Function.update_of_ne hab, hl.1, hl.2]

theorem skReplicaCollapse_b_rest (hab : a ≠ b) (l : Fin n) (hl : l ≠ a ∧ l ≠ b) :
    skReplicaCollapse G a b b l = G a l := by
  simp [skReplicaCollapse_apply, hl.1, hl.2, Ne.symm hab]

theorem skReplicaCollapse_ab (hab : a ≠ b) (hd : ∀ l, G l l = 0) :
    skReplicaCollapse G a b a b = |G a b| := by
  simp [skReplicaCollapse_apply, hd, hab]

end Collapse

/-- The sum of squares of a symmetric matrix with zero diagonal, split along two indices. -/
theorem sum_sq_split (a b : Fin n) (hab : a ≠ b) (M : Fin n → Fin n → ℝ)
    (hs : ∀ l l', M l l' = M l' l) (hd : ∀ l, M l l = 0) :
    ∑ l, ∑ l', M l l' ^ 2 =
      2 * M a b ^ 2 + 2 * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, M a l.val ^ 2 +
        2 * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, M b l.val ^ 2 +
        ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
          M l.val l'.val ^ 2 := by
  have := quad_split a b hab (fun l l' => M l l' ^ 2) (fun l l' => by simp only [hs l l'])
    (fun l => by simp only [hd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
    (fun _ => 1)
  simp only [mul_one] at this
  rw [this]

/-- The averaging identity `∑ g² = (∑ g′² + ∑ g″²) / 2` of Lemma 1.13.5, in matrix form. -/
theorem sum_sq_collapse (a b : Fin n) (hab : a ≠ b) (G : Fin n → Fin n → ℝ)
    (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0) :
    ∑ l, ∑ l', skReplicaCollapse G a b l l' ^ 2 + ∑ l, ∑ l', skReplicaCollapse G b a l l' ^ 2 =
      2 * ∑ l, ∑ l', G l l' ^ 2 := by
  have h1 := sum_sq_split a b hab (skReplicaCollapse G a b)
    (skReplicaCollapse_symm G a b hs) (skReplicaCollapse_diag G a b hab hd)
  have h2 := sum_sq_split a b hab (skReplicaCollapse G b a)
    (skReplicaCollapse_symm G b a hs) (skReplicaCollapse_diag G b a hab.symm hd)
  have h3 := sum_sq_split a b hab G hs hd
  rw [h1, h2, h3]
  have e1 : skReplicaCollapse G a b a b = |G a b| := skReplicaCollapse_ab G a b hab hd
  have e2 : skReplicaCollapse G b a a b = |G a b| := by
    rw [skReplicaCollapse_symm G b a hs a b, skReplicaCollapse_ab G b a hab.symm hd, hs b a]
  have e3 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G a b a l.val ^ 2 =
      ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [skReplicaCollapse_a_rest G a b hab l.val l.property]
  have e4 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G a b b l.val ^ 2 =
      ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [skReplicaCollapse_b_rest G a b hab l.val l.property]
  have e5 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G b a a l.val ^ 2 =
      ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val ^ 2 :=
    Finset.sum_congr rfl fun l _ => by
      rw [skReplicaCollapse_b_rest G b a hab.symm l.val ⟨l.property.2, l.property.1⟩]
  have e6 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G b a b l.val ^ 2 =
      ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val ^ 2 :=
    Finset.sum_congr rfl fun l _ => by
      rw [skReplicaCollapse_a_rest G b a hab.symm l.val ⟨l.property.2, l.property.1⟩]
  have e7 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
      skReplicaCollapse G a b l.val l'.val ^ 2 = ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
        ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b}, G l.val l'.val ^ 2 :=
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by
      rw [skReplicaCollapse_rest G a b l.val l'.val l.property l'.property]
  have e8 : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
      skReplicaCollapse G b a l.val l'.val ^ 2 = ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
        ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b}, G l.val l'.val ^ 2 :=
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by
      rw [skReplicaCollapse_rest G b a l.val l'.val ⟨l.property.2, l.property.1⟩
        ⟨l'.property.2, l'.property.1⟩]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, sq_abs]
  ring

/-- The three partition functions of Lemma 1.13.5 share the weights `w(α)` and differ only in the
pair of local fields `A₁, A₂` and the coupling `γ` of the two special replicas. -/
theorem skReplicaCollapse_split_data (β h : ℝ) (hβ : 0 < β) (a b : Fin n) (hab : a ≠ b)
    (G : Fin n → Fin n → ℝ) (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0) :
    ∃ (w A₁ A₂ : ({l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) → ℝ), (∀ α, 0 < w α) ∧
      (∀ α, A₁ α = β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * ((α l : ℤ) : ℝ) + h) ∧
      (∀ α, A₂ α = β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * ((α l : ℤ) : ℝ) + h) ∧
      Real.exp (skReplicaMatLogPartition n β h G) =
        ∑ α, w α * (cosh (A₁ α) * cosh (A₂ α) * cosh (β * G a b) +
          sinh (A₁ α) * sinh (A₂ α) * sinh (β * G a b)) ∧
      Real.exp (skReplicaMatLogPartition n β h (skReplicaCollapse G a b)) =
        ∑ α, w α * (cosh (A₁ α) ^ 2 * cosh |β * G a b| + sinh (A₁ α) ^ 2 * sinh |β * G a b|) ∧
      Real.exp (skReplicaMatLogPartition n β h (skReplicaCollapse G b a)) =
        ∑ α, w α * (cosh (A₂ α) ^ 2 * cosh |β * G a b| + sinh (A₂ α) ^ 2 * sinh |β * G a b|) := by
  refine ⟨fun α => 4 * Real.exp (β / 2 * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b},
            ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
            G l.val l'.val * ((α l : ℤ) : ℝ) * ((α l' : ℤ) : ℝ) +
          h * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ((α l : ℤ) : ℝ)),
    fun α => β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * ((α l : ℤ) : ℝ) + h,
    fun α => β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * ((α l : ℤ) : ℝ) + h,
    fun α => by positivity, fun α => rfl, fun α => rfl, ?_, ?_, ?_⟩
  · rw [exp_skReplicaMatLogPartition_split a b hab β h G hs hd]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  · rw [exp_skReplicaMatLogPartition_split a b hab β h _
      (skReplicaCollapse_symm G a b hs) (skReplicaCollapse_diag G a b hab hd)]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hr : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
        skReplicaCollapse G a b l.val l'.val * ((α l : ℤ) : ℝ) * ((α l' : ℤ) : ℝ) =
        ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
          G l.val l'.val * ((α l : ℤ) : ℝ) * ((α l' : ℤ) : ℝ) :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by
        rw [skReplicaCollapse_rest G a b l.val l'.val l.property l'.property]
    have ha : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G a b a l.val *
        ((α l : ℤ) : ℝ) = ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * ((α l : ℤ) : ℝ) :=
      Finset.sum_congr rfl fun l _ => by rw [skReplicaCollapse_a_rest G a b hab l.val l.property]
    have hb : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G a b b l.val *
        ((α l : ℤ) : ℝ) = ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G a l.val * ((α l : ℤ) : ℝ) :=
      Finset.sum_congr rfl fun l _ => by rw [skReplicaCollapse_b_rest G a b hab l.val l.property]
    rw [hr, ha, hb, skReplicaCollapse_ab G a b hab hd]
    beta_reduce
    rw [abs_mul, abs_of_pos hβ]
    ring
  · rw [exp_skReplicaMatLogPartition_split a b hab β h _
      (skReplicaCollapse_symm G b a hs) (skReplicaCollapse_diag G b a hab.symm hd)]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hr : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
        skReplicaCollapse G b a l.val l'.val * ((α l : ℤ) : ℝ) * ((α l' : ℤ) : ℝ) =
        ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, ∑ l' : {l : Fin n // l ≠ a ∧ l ≠ b},
          G l.val l'.val * ((α l : ℤ) : ℝ) * ((α l' : ℤ) : ℝ) :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by
        rw [skReplicaCollapse_rest G b a l.val l'.val ⟨l.property.2, l.property.1⟩
          ⟨l'.property.2, l'.property.1⟩]
    have ha : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G b a a l.val *
        ((α l : ℤ) : ℝ) = ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * ((α l : ℤ) : ℝ) :=
      Finset.sum_congr rfl fun l _ => by
        rw [skReplicaCollapse_b_rest G b a hab.symm l.val ⟨l.property.2, l.property.1⟩]
    have hb : ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, skReplicaCollapse G b a b l.val *
        ((α l : ℤ) : ℝ) = ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, G b l.val * ((α l : ℤ) : ℝ) :=
      Finset.sum_congr rfl fun l _ => by
        rw [skReplicaCollapse_a_rest G b a hab.symm l.val ⟨l.property.2, l.property.1⟩]
    have hab' : skReplicaCollapse G b a a b = |G a b| := by
      rw [skReplicaCollapse_symm G b a hs a b, skReplicaCollapse_ab G b a hab.symm hd, hs b a]
    rw [hr, ha, hb, hab']
    beta_reduce
    rw [abs_mul, abs_of_pos hβ]
    ring

/-- Two linear forms in signs that agree on every sign vector have the same coefficients. -/
theorem coeff_eq_of_forall_signs {ι : Type*} [Fintype ι] (U V : ι → ℝ)
    (h : ∀ α : ι → ℤˣ, ∑ l, U l * ((α l : ℤ) : ℝ) = ∑ l, V l * ((α l : ℤ) : ℝ)) : U = V := by
  classical
  funext l0
  have h0 := h (fun _ => 1)
  have h1 := h (Function.update (fun _ => 1) l0 (-1))
  have hd (W : ι → ℝ) : ∑ l, W l * ((((fun _ => 1 : ι → ℤˣ) l : ℤˣ) : ℤ) : ℝ) -
      ∑ l, W l * (((Function.update (fun _ => 1 : ι → ℤˣ) l0 (-1) l : ℤˣ) : ℤ) : ℝ) =
      2 * W l0 := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ l, W l * ((((fun _ => 1 : ι → ℤˣ) l : ℤˣ) : ℤ) : ℝ) -
        W l * (((Function.update (fun _ => 1 : ι → ℤˣ) l0 (-1) l : ℤˣ) : ℤ) : ℝ) =
        if l = l0 then 2 * W l else 0 := by
      intro l
      by_cases hl : l = l0
      · subst hl; simp; ring
      · simp [hl]
    simp_rw [this]
    simp
  have := hd U
  have := hd V
  linarith

/-- **Lemma 1.13.5**, in matrix form. Let `G` be a maximizer of `B(G) = A(G) - ¼ ∑ G²` among
symmetric matrices with zero diagonal, and let `a ≠ b` be two replicas. Then `g′` and `g″` have
the same value of `B`, and the other couplings of `a` and `b` agree if `G_ab > 0` and are opposite
(with `h = 0`) if `G_ab < 0`. -/
theorem skReplica_lemma_1_13_5 (β h : ℝ) (hβ : 0 < β) (a b : Fin n) (hab : a ≠ b)
    (G : Fin n → Fin n → ℝ) (hs : ∀ l l', G l l' = G l' l) (hd : ∀ l, G l l = 0)
    (hmax : ∀ H : Fin n → Fin n → ℝ, (∀ l l', H l l' = H l' l) → (∀ l, H l l = 0) →
      skReplicaMatLogPartition n β h H - (∑ l, ∑ l', H l l' ^ 2) / 4 ≤
        skReplicaMatLogPartition n β h G - (∑ l, ∑ l', G l l' ^ 2) / 4) :
    skReplicaMatLogPartition n β h (skReplicaCollapse G a b) -
        (∑ l, ∑ l', skReplicaCollapse G a b l l' ^ 2) / 4 =
      skReplicaMatLogPartition n β h G - (∑ l, ∑ l', G l l' ^ 2) / 4 ∧
    skReplicaMatLogPartition n β h (skReplicaCollapse G b a) -
        (∑ l, ∑ l', skReplicaCollapse G b a l l' ^ 2) / 4 =
      skReplicaMatLogPartition n β h G - (∑ l, ∑ l', G l l' ^ 2) / 4 ∧
    (0 < G a b → ∀ l, l ≠ a → l ≠ b → G a l = G b l) ∧
    (G a b < 0 → h = 0 ∧ ∀ l, l ≠ a → l ≠ b → G a l = -G b l) := by
  obtain ⟨w, A₁, A₂, hw, hA₁, hA₂, hG, hG', hG''⟩ :=
    skReplicaCollapse_split_data β h hβ a b hab G hs hd
  set A := skReplicaMatLogPartition n β h G with hA
  set A' := skReplicaMatLogPartition n β h (skReplicaCollapse G a b) with hA'
  set A'' := skReplicaMatLogPartition n β h (skReplicaCollapse G b a) with hA''
  have hsqrt (x : ℝ) : √(Real.exp x) = Real.exp (x / 2) := by
    rw [show x = x / 2 + x / 2 by ring, Real.exp_add]
    simp only [add_halves]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  have hcs := hyp_sum_cs_le w hw A₁ A₂ (β * G a b)
  rw [← hG, ← hG', ← hG'', hsqrt, hsqrt, ← Real.exp_add] at hcs
  have hlin : A ≤ (A' + A'') / 2 := by
    have := Real.exp_le_exp.1 hcs
    linarith
  have hq := sum_sq_collapse a b hab G hs hd
  have hB' := hmax _ (skReplicaCollapse_symm G a b hs) (skReplicaCollapse_diag G a b hab hd)
  have hB'' := hmax _ (skReplicaCollapse_symm G b a hs) (skReplicaCollapse_diag G b a hab.symm hd)
  have hq' : (∑ l, ∑ l', skReplicaCollapse G a b l l' ^ 2) +
      (∑ l, ∑ l', skReplicaCollapse G b a l l' ^ 2) = 2 * ∑ l, ∑ l', G l l' ^ 2 := hq
  have e1 : A' - (∑ l, ∑ l', skReplicaCollapse G a b l l' ^ 2) / 4 =
      A - (∑ l, ∑ l', G l l' ^ 2) / 4 := by linarith
  have e2 : A'' - (∑ l, ∑ l', skReplicaCollapse G b a l l' ^ 2) / 4 =
      A - (∑ l, ∑ l', G l l' ^ 2) / 4 := by linarith
  have hAeq : A = (A' + A'') / 2 := by linarith
  have heq : ∑ α, w α * (cosh (A₁ α) * cosh (A₂ α) * cosh (β * G a b) +
        sinh (A₁ α) * sinh (A₂ α) * sinh (β * G a b)) =
      √(∑ α, w α * (cosh (A₁ α) ^ 2 * cosh |β * G a b| + sinh (A₁ α) ^ 2 * sinh |β * G a b|)) *
        √(∑ α, w α * (cosh (A₂ α) ^ 2 * cosh |β * G a b| +
          sinh (A₂ α) ^ 2 * sinh |β * G a b|)) := by
    rw [← hG, ← hG', ← hG'', hsqrt, hsqrt, ← Real.exp_add, hAeq]
    congr 1
    ring
  obtain ⟨hpos, hneg⟩ := hyp_sum_cs_eq w hw A₁ A₂ (β * G a b) heq
  refine ⟨e1, e2, fun hc l hla hlb => ?_, fun hc => ?_⟩
  · have hall := hpos (mul_pos hβ hc)
    let l' : {l : Fin n // l ≠ a ∧ l ≠ b} := ⟨l, hla, hlb⟩
    have hcoef : (fun l : {l : Fin n // l ≠ a ∧ l ≠ b} => β * G a l.val) =
        fun l => β * G b l.val := by
      refine coeff_eq_of_forall_signs _ _ fun α => ?_
      have := hall α
      rw [hA₁, hA₂] at this
      simp only [mul_sum, mul_assoc] at this ⊢
      linarith
    have := congrFun hcoef l'
    exact mul_left_cancel₀ hβ.ne' this
  · have hall := hneg (mul_neg_of_pos_of_neg hβ hc)
    have hsum (α : {l : Fin n // l ≠ a ∧ l ≠ b} → ℤˣ) :
        β * ∑ l : {l : Fin n // l ≠ a ∧ l ≠ b}, (G a l.val + G b l.val) * ((α l : ℤ) : ℝ) + 2 * h
          = 0 := by
      have := hall α
      rw [hA₁, hA₂] at this
      simp only [add_mul, Finset.sum_add_distrib]
      linarith
    have h1 := hsum (fun _ => 1)
    have h2 := hsum (fun _ => -1)
    simp only [Units.val_one, Int.cast_one, mul_one, Units.val_neg, Int.cast_neg, mul_neg,
      Finset.sum_neg_distrib] at h1 h2
    have hh : h = 0 := by linarith
    refine ⟨hh, fun l hla hlb => ?_⟩
    let l' : {l : Fin n // l ≠ a ∧ l ≠ b} := ⟨l, hla, hlb⟩
    have hcoef : (fun l : {l : Fin n // l ≠ a ∧ l ≠ b} => β * (G a l.val + G b l.val)) =
        fun _ => 0 := by
      refine coeff_eq_of_forall_signs _ _ fun α => ?_
      have := hsum α
      simp only [zero_mul, Finset.sum_const_zero, mul_sum, mul_assoc] at this ⊢
      linarith
    have := congrFun hcoef l'
    have h3 : β * (G a l + G b l) = 0 := this
    have := (mul_eq_zero.1 h3).resolve_left hβ.ne'
    linarith

end SpinGlasses
