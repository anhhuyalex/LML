/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.PairingGaussianBlocks
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingBasic

/-!
# The Gaussian reference for products of rectangles (Talagrand, Eq. (1.345)-(1.346))

Spin-free part of step E3d of Proposition 1.11.10. The `2m` difference labels carry pairwise
disjoint replica pairs `(x v, y v)`. For two labels `a ≠ b` the rectangle of the pair map is the
signed sum, over the four choices of one replica in each difference, of the pair variable of the
chosen replicas (ordered by `min`/`max`, as the pair Gaussian moment theorem requires).
Distinct unordered label pairs use disjoint sets of pair variables, because a pair of replicas
determines the labels of its two replicas. Hence the Gaussian reference of the product of the
rectangles of two pairings is `(4 A²)^m` if the pairings agree and `0` otherwise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- A sorted pair of numbers determines the unordered pair. -/
theorem min_max_eq_iff {α : Type*} [LinearOrder α] (x y x' y' : α) :
    (min x y = min x' y' ∧ max x y = max x' y') ↔
      ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total x y with h | h <;> rcases le_total x' y' with h' | h'
    · left
      rw [min_eq_left h, min_eq_left h'] at h1
      rw [max_eq_right h, max_eq_right h'] at h2
      exact ⟨h1, h2⟩
    · right
      rw [min_eq_left h, min_eq_right h'] at h1
      rw [max_eq_right h, max_eq_left h'] at h2
      exact ⟨h1, h2⟩
    · right
      rw [min_eq_right h, min_eq_left h'] at h1
      rw [max_eq_left h, max_eq_right h'] at h2
      exact ⟨h2, h1⟩
    · left
      rw [min_eq_right h, min_eq_right h'] at h1
      rw [max_eq_left h, max_eq_left h'] at h2
      exact ⟨h2, h1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨rfl, rfl⟩
    · exact ⟨min_comm _ _, max_comm _ _⟩

/-- Replicas of different difference labels, or of the two sides of one label, are different
replicas: the replica `(pairMap v).1` or `(pairMap v).2` determines `v` and the side. -/
theorem hanen_replica_injective {m n : ℕ} (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (v v' : Fin (2 * m)) (e e' : Bool)
    (h : (if e then (pairMap v).2 else (pairMap v).1) =
      (if e' then (pairMap v').2 else (pairMap v').1)) : v = v' ∧ e = e' := by
  by_cases hv : v = v'
  · subst hv
    refine ⟨rfl, ?_⟩
    cases e <;> cases e' <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h ⊢
    · exact (hxy v h).elim
    · exact (hxy v h.symm).elim
  · exfalso
    have hd := hdisj v v' hv
    cases e <;> cases e' <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h
    · exact hd.1 h
    · exact hd.2.1 h
    · exact hd.2.2.1 h
    · exact hd.2.2.2 h

/-- Properties of the coefficient vectors of the Gaussian rectangles: they are symmetric in the
two labels, supported on pairwise disjoint sets of pair variables for different unordered pairs
of labels, and have squared norm `4 A²` (four distinct pair variables with coefficients `±A`). -/
theorem hanen_rect_coeff {m n : ℕ} (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) (A : ℝ) :
    let rep := fun (v : Fin (2 * m)) (e : Bool) => if e then (pairMap v).2 else (pairMap v).1
    let c := fun e : Bool × Bool => (if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)
    let κ := fun (a b : Fin (2 * m)) (e : Bool × Bool) =>
      (Sum.inl (min (rep a e.1) (rep b e.2), max (rep a e.1) (rep b e.2)) :
        (Fin n × Fin n) ⊕ Fin n)
    let V := fun (a b : Fin (2 * m)) (k : (Fin n × Fin n) ⊕ Fin n) =>
      A * ∑ e : Bool × Bool, c e * (if k = κ a b e then (1 : ℝ) else 0)
    (∀ a b, V a b = V b a) ∧
    (∀ a b a' b' : Fin (2 * m), a ≠ b → a' ≠ b' → ({a, b} : Finset (Fin (2 * m))) ≠ {a', b'} →
      ∀ k, V a b k = 0 ∨ V a' b' k = 0) ∧
    (∀ a b : Fin (2 * m), a ≠ b → V a b ⬝ᵥ V a b = 4 * A ^ 2) ∧
    (∀ (a b : Fin (2 * m)) (z : (Fin n × Fin n) ⊕ Fin n → ℝ), V a b ⬝ᵥ z =
      ∑ e : Bool × Bool, c e * (A * z (κ a b e))) := by
  intro rep c κ V
  have hkey (a b a' b' : Fin (2 * m)) (e e' : Bool × Bool) (h : κ a b e = κ a' b' e') :
      (a = a' ∧ e.1 = e'.1 ∧ b = b' ∧ e.2 = e'.2) ∨ (a = b' ∧ e.1 = e'.2 ∧ b = a' ∧ e.2 = e'.1) := by
    simp only [κ, Sum.inl.injEq, Prod.mk.injEq] at h
    rcases (min_max_eq_iff _ _ _ _).1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      obtain ⟨ha, he1⟩ := hanen_replica_injective pairMap hxy hdisj _ _ _ _ h1
      obtain ⟨hb, he2⟩ := hanen_replica_injective pairMap hxy hdisj _ _ _ _ h2
      exact ⟨ha, he1, hb, he2⟩
    · right
      obtain ⟨ha, he1⟩ := hanen_replica_injective pairMap hxy hdisj _ _ _ _ h1
      obtain ⟨hb, he2⟩ := hanen_replica_injective pairMap hxy hdisj _ _ _ _ h2
      exact ⟨ha, he1, hb, he2⟩
  have hinj (a b : Fin (2 * m)) (hab : a ≠ b) : Function.Injective (κ a b) := by
    intro e e' h
    rcases hkey a b a b e e' h with ⟨-, h1, -, h2⟩ | ⟨h1, -, h2, -⟩
    · exact Prod.ext h1 h2
    · exact absurd h1 hab
  have hc2 (e : Bool × Bool) : c e ^ 2 = 1 := by
    rcases e with ⟨e₁, e₂⟩
    cases e₁ <;> cases e₂ <;> simp [c]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    funext k
    simp only [V]
    congr 1
    refine Fintype.sum_equiv (Equiv.prodComm Bool Bool) _ _ fun e => ?_
    rcases e with ⟨e₁, e₂⟩
    have hκ : κ a b (e₁, e₂) = κ b a (e₂, e₁) := by
      simp only [κ, min_comm, max_comm]
    have hcc : c (e₁, e₂) = c (e₂, e₁) := by simp only [c]; ring
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hκ, hcc]
    by_cases hk : k = κ b a (e₂, e₁) <;> simp [hk]
  · intro a b a' b' hab hab' hne k
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hex (a b : Fin (2 * m)) (h : V a b k ≠ 0) : ∃ e, k = κ a b e := by
      by_contra hno
      push Not at hno
      apply h
      simp only [V]
      rw [Finset.sum_eq_zero (fun e _ => by simp [(hno e)]), mul_zero]
    obtain ⟨e, he⟩ := hex a b h1
    obtain ⟨e', he'⟩ := hex a' b' h2
    rcases hkey a b a' b' e e' (he.symm.trans he') with ⟨ha, -, hb, -⟩ | ⟨ha, -, hb, -⟩
    · exact hne (by rw [ha, hb])
    · exact hne (by rw [ha, hb, Finset.pair_comm])
  · intro a b hab
    have hsq (k : (Fin n × Fin n) ⊕ Fin n) : V a b k ^ 2 =
        A ^ 2 * ∑ e : Bool × Bool, c e ^ 2 * (if k = κ a b e then (1 : ℝ) else 0) := by
      simp only [V]
      rw [mul_pow, sq (∑ e : Bool × Bool, c e * _), Finset.sum_mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_eq_single e]
      · by_cases hk : k = κ a b e
        · simp [hk, sq]
        · simp [hk]
      · intro e' _ hne
        by_cases hk : k = κ a b e
        · have : k ≠ κ a b e' := fun h => hne (hinj a b hab (hk.symm.trans h)).symm
          simp [this]
        · simp [hk]
      · simp
    calc V a b ⬝ᵥ V a b = ∑ k, V a b k ^ 2 := by simp [dotProduct, sq]
      _ = ∑ k, A ^ 2 * ∑ e : Bool × Bool, c e ^ 2 * (if k = κ a b e then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun k _ => hsq k
      _ = A ^ 2 * ∑ e : Bool × Bool, c e ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp [Finset.sum_ite_eq']
      _ = 4 * A ^ 2 := by
          simp only [hc2, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
          norm_num
          ring
  · intro a b z
    simp only [dotProduct, V]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp
    ring

/-- **Gaussian reference, same pairing.** For the signed pair-variable rectangle kernel
`K z a b = ∑_e c_e A z(κ(a,b,e))` of the labels `a, b`, the mean over i.i.d. standard Gaussian
pair variables of the square of the block product of any pairing is `(4 A²)^m`. -/
theorem hanen_gaussian_rect_pairing_sq {m n : ℕ} (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) (A : ℝ)
    (P : Finpartition.Pairing (Finset.univ : Finset (Fin (2 * m)))) :
    ∫ z : (Fin n × Fin n) ⊕ Fin n → ℝ,
        P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
          ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) * (A * z (Sum.inl
            (min (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1),
             max (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
        P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
          ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) * (A * z (Sum.inl
            (min (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1),
             max (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1)))))
      ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1) =
      (4 * A ^ 2) ^ m := by
  obtain ⟨hs, hd, hn, hz⟩ := hanen_rect_coeff pairMap hxy hdisj A
  have h := Renormalization.integral_pi_gaussian_pairing_sq _ hs hd (4 * A ^ 2) hn P
  simp only [hz] at h
  rw [h, P.card_parts_of_card_eq (m := m) (by simp)]

/-- **Gaussian reference, different pairings.** The mean vanishes. -/
theorem hanen_gaussian_rect_pairings_of_ne {m n : ℕ} (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) (A : ℝ)
    (P₀ P : Finpartition.Pairing (Finset.univ : Finset (Fin (2 * m)))) (hne : P ≠ P₀) :
    ∫ z : (Fin n × Fin n) ⊕ Fin n → ℝ,
        P₀.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
          ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) * (A * z (Sum.inl
            (min (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1),
             max (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
        P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
          ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) * (A * z (Sum.inl
            (min (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1),
             max (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1)))))
      ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1) = 0 := by
  obtain ⟨hs, hd, hn, hz⟩ := hanen_rect_coeff pairMap hxy hdisj A
  have h := Renormalization.integral_pi_gaussian_two_pairings_of_ne _ hs hd (4 * A ^ 2) hn P₀ P hne
  simpa only [hz] using h

end SpinGlasses
