/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalInterface
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTComparison
public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal

/-!
# The feedback term of the global recurrence (Talagrand, Eqs. (1.327)-(1.328))

Lemma 1.10.2 expresses the leading cavity term as a signed sum over the replica pairs `j` of the
averages `ν₂(F⁻ (R⁻_j - q))` of the product `F⁻` of the truncated block overlaps against one
truncated overlap. This file replaces the truncated overlaps by full overlaps (`O(k+1)`),
classifies each average with `SKOverlapCLTGlobalClassify.lean` and sums the classification with the
counts of `SKOverlapCLTGlobalCounting.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Truncated to full overlaps for a product of blocks and one more overlap.** The average of
the product of the block overlaps against the overlap `(x, y)`, computed with the first `N` sites,
differs from the full average by `O(m+2)` for `m` blocks. -/
theorem sk_global_trunc_to_full_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R B : Type*} [Fintype R] [Fintype B] (ca da : B → R) (hca : ∀ u, ca u ≠ da u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (x y : R), x ≠ y →
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let ν₂ : ((R → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : R => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |ν₂ (fun σ => (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
          (σ (ca u) v.castSucc : ℝ) * (σ (da u) v.castSucc : ℝ) - q)) *
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ x v.castSucc : ℝ) * (σ y v.castSucc : ℝ) - q)) -
      ν₂ (fun σ => (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (ca u) v : ℝ) * (σ (da u) v : ℝ) - q)) *
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), (σ x v : ℝ) * (σ y v : ℝ) - q))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card B + 2 : ℕ) : ℝ) / 2) := by
  classical
  let n₂ := Fintype.card R
  let e₂ : R ≃ Fin n₂ := Fintype.equivFin R
  obtain ⟨C, hC0, hC⟩ := sk_overlap_prod_sub_truncated_le β₀ hβ₀ (κ := B ⊕ Unit)
    (ι := fun _ => Unit) (fun _ _ => (1 : ℝ)) 1
  refine ⟨C, hC0, fun β h q hfix hb N x y hxy => ?_⟩
  intro Esk ν₂
  let a : B ⊕ Unit → Unit → Fin n₂ := fun w _ => Sum.elim (fun u => e₂ (ca u)) (fun _ => e₂ x) w
  let b : B ⊕ Unit → Unit → Fin n₂ := fun w _ => Sum.elim (fun u => e₂ (da u)) (fun _ => e₂ y) w
  have hab : ∀ j i, a j i ≠ b j i := fun j i => by
    rcases j with u | u
    · exact e₂.injective.ne (hca u)
    · exact e₂.injective.ne hxy
  let νF : ((Fin n₂ → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
    ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n₂ => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have havg (H : (R → Fin (N + 1) → ℤˣ) → ℝ) :
      ν₂ H = νF (fun σ => H (fun r => σ (e₂ r))) := by
    dsimp only [ν₂, νF]
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    exact integral_pi_count_tilted_reindex e₂ (Esk g) H
  let Uf : B ⊕ Unit → (Fin n₂ → Fin (N + 1) → ℤˣ) → ℝ := fun w σ => ∑ i : Unit, (1 : ℝ) *
    ((N + 1 : ℝ)⁻¹ * ((fun v : Fin (N + 1) => (σ (a w i) v : ℝ)) ⬝ᵥ
      fun v : Fin (N + 1) => (σ (b w i) v : ℝ)) - q)
  let Um : B ⊕ Unit → (Fin n₂ → Fin (N + 1) → ℤˣ) → ℝ := fun w σ => ∑ i : Unit, (1 : ℝ) *
    ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ (a w i) v.castSucc : ℝ)) ⬝ᵥ
      fun v : Fin N => (σ (b w i) v.castSucc : ℝ)) - q)
  have hcmp := hC β h q hfix hb N n₂ a b hab νF (fun _ => rfl) Uf Um
    (fun w σ => ∑ i : Unit, (1 : ℝ) * ((σ (a w i) (Fin.last N) : ℝ) * (σ (b w i) (Fin.last N) : ℝ)))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => 1) (fun _ => by norm_num)
  obtain ⟨hadd, hsmul, hmono, -⟩ := sk_replica_avg_calculus N n₂ β h νF (fun _ => rfl)
  let Λ : ((Fin n₂ → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ := ⟨⟨νF, hadd⟩, hsmul⟩
  have hdiff : |νF (fun σ => ∏ j, Uf j σ) - νF (fun σ => ∏ j, Um j σ)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card B + 2 : ℕ) : ℝ) / 2) := by
    change |Λ (fun σ => ∏ j, Uf j σ) - Λ (fun σ => ∏ j, Um j σ)| ≤ _
    rw [← map_sub]
    refine (Λ.abs_apply_le_apply_abs hmono _).trans ?_
    simpa only [one_mul, Pi.sub_apply, Λ, LinearMap.coe_mk, AddHom.coe_mk, Fintype.card_sum,
      Fintype.card_unit, add_assoc] using hcmp
  have hUf : ∀ σ : Fin n₂ → Fin (N + 1) → ℤˣ, ∏ j, Uf j σ =
      (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e₂ (ca u)) v : ℝ) * (σ (e₂ (da u)) v : ℝ) - q)) *
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), (σ (e₂ x) v : ℝ) * (σ (e₂ y) v : ℝ) - q) :=
    fun σ => by
    simp [Fintype.prod_sum_type, Uf, a, b, dotProduct]
  have hUm : ∀ σ : Fin n₂ → Fin (N + 1) → ℤˣ, ∏ j, Um j σ =
      (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
          (σ (e₂ (ca u)) v.castSucc : ℝ) * (σ (e₂ (da u)) v.castSucc : ℝ) - q)) *
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e₂ x) v.castSucc : ℝ) * (σ (e₂ y) v.castSucc : ℝ) - q) :=
    fun σ => by
    simp [Fintype.prod_sum_type, Um, a, b, dotProduct]
  simp only [hUf, hUm] at hdiff
  rw [havg, havg]
  beta_reduce
  rw [abs_sub_comm]
  exact hdiff

/-- **The feedback sum of the global recurrence** (Eqs. (1.327)-(1.328)): the signed sum over the
replica pairs of Lemma 1.10.2 equals
`β²(1-4q+3q̂) ν_k + (k-1)(β²(q̂-q²) A² + 2β²(2q+q²-3q̂) B²) ν_{k-2}/(N+1)` up to `O(k+1)`, where
`ν_j = 𝔼 T^j`. -/
theorem sk_global_feedback_eval_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (e : V ⊕ V ≃ Fin n) (p : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (Esk g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let ν₂ : ((Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
      (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)
    let A2 : ℝ := α / (1 - β ^ 2 * α) / (N + 1 : ℝ)
    |∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qh (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
          ν₂ (fun σ => (∏ u : {u // u ≠ p}, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
                (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (skCavityReplicaPairMap j).1 v.castSucc : ℝ) *
                (σ (skCavityReplicaPairMap j).2 v.castSucc : ℝ) - q))) -
      (β ^ 2 * (1 - 4 * q + 3 * qh) * ν (Fintype.card V) +
        ((Fintype.card V - 1 : ℕ) : ℝ) * (β ^ 2 * (qh - q ^ 2) * A2 +
          2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2) * ν (Fintype.card V - 2))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := by
  classical
  let R₂ := Option (Option (Fin n))
  let f : R₂ → ℕ := fun z => match z with
    | none => 0
    | some none => 1
    | some (some i) => i.1 + 2
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp only [f] at hab ⊢ <;>
      first | omega | exact congrArg (fun i => some (some i)) (Fin.ext (by omega))
  let _ : LinearOrder R₂ := LinearOrder.lift' f hf
  let B := {u : V // u ≠ p}
  let ca : B → R₂ := fun u => some (some (e (.inl u.1)))
  let da : B → R₂ := fun u => some (some (e (.inr u.1)))
  have hinj : Function.Injective (Sum.elim ca da : B ⊕ B → R₂) := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr, ca, da]
      at hab
    · have := e.injective (Option.some.inj (Option.some.inj hab))
      simp only [Sum.inl.injEq] at this
      exact congrArg Sum.inl (Subtype.ext this)
    · exact absurd (e.injective (Option.some.inj (Option.some.inj hab))) (by simp)
    · exact absurd (e.injective (Option.some.inj (Option.some.inj hab))) (by simp)
    · have := e.injective (Option.some.inj (Option.some.inj hab))
      simp only [Sum.inr.injEq] at this
      exact congrArg Sum.inr (Subtype.ext this)
  have hca : ∀ u, ca u ≠ da u := fun u h =>
    Sum.inl_ne_inr (hinj (a₁ := Sum.inl u) (a₂ := Sum.inr u) h)
  have hcardB : Fintype.card B = Fintype.card V - 1 := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
  have hV1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨p⟩
  obtain ⟨C₃, hC₃0, hC₃⟩ := sk_global_trunc_to_full_uniform β₀ hβ₀ ca da hca
  choose Cc hCc0 hCc using fun j : SKCavityReplicaPair n =>
    sk_overlap_blocks_uniform β₀ hβ₀ ca da hinj (x := (skCavityReplicaPairMap j).1)
      (y := (skCavityReplicaPairMap j).2) (skCavityReplicaPair_ne j)
  refine ⟨(∑ j, |skCavityReplicaPairWeight n j| * β₀ ^ 2 * (C₃ + Cc j)) + 1, by
    have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (SKCavityReplicaPair n))) =>
      mul_nonneg (mul_nonneg (abs_nonneg (skCavityReplicaPairWeight n j)) (sq_nonneg β₀))
        (add_pos hC₃0 (hCc0 j)).le)
    linarith, ?_⟩
  intro β h q hfix hb N Esk bmean Tg qh α ν₂ ν B2 A2
  let tchf : R₂ → ℝ := fun z => match z with
    | some (some r) => 1 - (if r = e (.inl p) ∨ r = e (.inr p) then 1 else 0)
    | _ => 0
  let blkf : R₂ → R₂ → ℝ := fun z z' => match z, z' with
    | some (some r), some (some s) =>
        if r ≠ e (.inl p) ∧ r ≠ e (.inr p) ∧ s = blockPartner e r then 1 else 0
    | _, _ => 0
  have hnone : ∀ u : B, none ≠ ca u ∧ none ≠ da u ∧ some none ≠ ca u ∧ some none ≠ da u :=
    fun u => by simp [ca, da]
  have htch_eq : ∀ (z : R₂) (d : Decidable (∃ u : B, z = ca u ∨ z = da u)),
      (@ite ℝ (∃ u : B, z = ca u ∨ z = da u) d 1 0) = tchf z := fun z d => by
    rcases z with _ | _ | r
    · rw [ite_eq_right (by
        rintro ⟨u, h | h⟩
        · exact (hnone u).1 h
        · exact (hnone u).2.1 h)]
    · rw [ite_eq_right (by
        rintro ⟨u, h | h⟩
        · exact (hnone u).2.2.1 h
        · exact (hnone u).2.2.2 h)]
    · have hP : (∃ u : B, some (some r) = ca u ∨ some (some r) = da u) ↔
          ¬(r = e (.inl p) ∨ r = e (.inr p)) := by
        rw [← exists_block_iff e p r]
        simp only [ca, da, Option.some.injEq]
        exact Iff.rfl
      by_cases hr : r = e (.inl p) ∨ r = e (.inr p)
      · rw [ite_eq_right (fun hp => (hP.mp hp) hr)]
        simp [tchf, hr]
      · rw [ite_eq_left (hP.mpr hr)]
        simp [tchf, hr]
  have hblk_eq : ∀ (z z' : R₂)
      (d : Decidable (∃ u : B, (z = ca u ∧ z' = da u) ∨ (z = da u ∧ z' = ca u))),
      (@ite ℝ (∃ u : B, (z = ca u ∧ z' = da u) ∨ (z = da u ∧ z' = ca u)) d 1 0) = blkf z z' := by
    intro z z' d
    have hfalse : ∀ (P : Prop) [Decidable P] (hP : ¬P), (if P then (1 : ℝ) else 0) = 0 :=
      fun P _ hP => ite_eq_right hP
    rcases z with _ | _ | r
    · rw [hfalse _ (by
        rintro ⟨u, ⟨h, -⟩ | ⟨h, -⟩⟩
        · exact (hnone u).1 h
        · exact (hnone u).2.1 h)]
    · rw [hfalse _ (by
        rintro ⟨u, ⟨h, -⟩ | ⟨h, -⟩⟩
        · exact (hnone u).2.2.1 h
        · exact (hnone u).2.2.2 h)]
    rcases z' with _ | _ | s
    · rw [hfalse _ (by
        rintro ⟨u, ⟨-, h⟩ | ⟨-, h⟩⟩
        · exact (hnone u).2.1 h
        · exact (hnone u).1 h)]
    · rw [hfalse _ (by
        rintro ⟨u, ⟨-, h⟩ | ⟨-, h⟩⟩
        · exact (hnone u).2.2.2 h
        · exact (hnone u).2.2.1 h)]
    · have hP : (∃ u : B, (some (some r) = ca u ∧ some (some s) = da u) ∨
          (some (some r) = da u ∧ some (some s) = ca u)) ↔
          (r ≠ e (.inl p) ∧ r ≠ e (.inr p) ∧ s = blockPartner e r) := by
        rw [← exists_block_pair_iff e p r s]
        simp only [ca, da, Option.some.injEq]
        exact Iff.rfl
      by_cases hr : r ≠ e (.inl p) ∧ r ≠ e (.inr p) ∧ s = blockPartner e r
      · rw [ite_eq_left (hP.mpr hr)]
        simp [blkf, hr]
      · rw [ite_eq_right (fun hp => hr (hP.mp hp))]
        simp [blkf, hr]
  have hB1 : Fintype.card B + 1 = Fintype.card V := by omega
  have hB2 : Fintype.card B - 1 = Fintype.card V - 2 := by omega
  have hexp : Fintype.card B + 2 = Fintype.card V + 1 := by omega
  have hj : ∀ j : SKCavityReplicaPair n,
      |ν₂ (fun σ => (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
                (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (skCavityReplicaPairMap j).1 v.castSucc : ℝ) *
                (σ (skCavityReplicaPairMap j).2 v.castSucc : ℝ) - q)) -
        (ν (Fintype.card V) + ((tchf (skCavityReplicaPairMap j).1 +
          tchf (skCavityReplicaPairMap j).2) * B2 +
          blkf (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2 * A2) *
          ν (Fintype.card V - 2))| ≤
        (C₃ + Cc j) / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := fun j => by
    have h3 := hC₃ β h q hfix hb N (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2
      (skCavityReplicaPair_ne j)
    have h4 := hCc j β h q hfix hb N
    dsimp only at h4
    simp only [htch_eq, hblk_eq] at h4
    set x := (skCavityReplicaPairMap j).1 with hx
    set y := (skCavityReplicaPairMap j).2 with hy
    have h3' : |ν₂ (fun σ => (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
                (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ x v.castSucc : ℝ) * (σ y v.castSucc : ℝ) - q)) -
        ν₂ (fun σ => (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
              (σ (some (some (e (.inl u.1)))) v : ℝ) *
                (σ (some (some (e (.inr u.1)))) v : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), (σ x v : ℝ) * (σ y v : ℝ) - q))| ≤
        C₃ / ((N : ℝ) + 1) ^ (((Fintype.card B + 2 : ℕ) : ℝ) / 2) := h3
    have h4' : |ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
              (σ x v : ℝ) * (σ y v : ℝ) - q) *
            ∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
              (σ (some (some (e (.inl u.1)))) v : ℝ) *
                (σ (some (some (e (.inr u.1)))) v : ℝ) - q)) -
        (ν (Fintype.card B + 1) + ((tchf x + tchf y) * B2 + blkf x y * A2) *
          ν (Fintype.card B - 1))| ≤
        Cc j / ((N : ℝ) + 1) ^ (((Fintype.card B + 2 : ℕ) : ℝ) / 2) := h4
    have hmc : ν₂ (fun σ => (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
              (σ (some (some (e (.inl u.1)))) v : ℝ) *
                (σ (some (some (e (.inr u.1)))) v : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), (σ x v : ℝ) * (σ y v : ℝ) - q)) =
        ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
              (σ x v : ℝ) * (σ y v : ℝ) - q) *
            ∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
              (σ (some (some (e (.inl u.1)))) v : ℝ) *
                (σ (some (some (e (.inr u.1)))) v : ℝ) - q)) := by
      congr 1
      funext σ
      exact mul_comm _ _
    rw [hmc, hexp] at h3'
    rw [hexp, hB1, hB2] at h4'
    calc _ ≤ _ := abs_sub_le _ _ _
      _ ≤ C₃ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) +
          Cc j / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := add_le_add h3' h4'
      _ = _ := by ring
  -- the counting
  have hn : n = 2 * Fintype.card V := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hxy0 : e (.inl p) ≠ e (.inr p) := e.injective.ne (by simp)
  let b : ℕ → ℝ := skCavityBCoef β q qh
  have hA := sk_count_plain hxy0 b
  have hB := sk_count_touched hxy0 b tchf (fun r => rfl) rfl rfl
  have hC := sk_count_blocks hxy0 b (blockPartner e) (blockPartner_spec e p) blkf
    (fun r s => rfl) (fun r => rfl) rfl
  have hcount : ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
      (b (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
        (ν (Fintype.card V) + ((tchf (skCavityReplicaPairMap j).1 +
          tchf (skCavityReplicaPairMap j).2) * B2 +
          blkf (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2 * A2) *
          ν (Fintype.card V - 2))) =
      β ^ 2 * (1 - 4 * q + 3 * qh) * ν (Fintype.card V) +
        ((Fintype.card V - 1 : ℕ) : ℝ) * (β ^ 2 * (qh - q ^ 2) * A2 +
          2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2) * ν (Fintype.card V - 2) := by
    have hsplit : ∀ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (b (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
          (ν (Fintype.card V) + ((tchf (skCavityReplicaPairMap j).1 +
            tchf (skCavityReplicaPairMap j).2) * B2 +
            blkf (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2 * A2) *
            ν (Fintype.card V - 2))) =
        ν (Fintype.card V) * (skCavityReplicaPairWeight n j *
            (b (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) * 1)) +
        (B2 * ν (Fintype.card V - 2)) * (skCavityReplicaPairWeight n j *
            (b (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
              (tchf (skCavityReplicaPairMap j).1 + tchf (skCavityReplicaPairMap j).2))) +
        (A2 * ν (Fintype.card V - 2)) * (skCavityReplicaPairWeight n j *
            (b (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
              blkf (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2)) := fun j => by
      ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB, hC]
    have h2 := sk_at_eigenvalue_two_eq β q qh
    have hn' : (n : ℝ) = 2 * (Fintype.card V : ℝ) := by rw [hn]; push_cast; ring
    have hcV : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
      rw [Nat.cast_sub hV1]; simp
    simp only [b, skCavityBCoef, skCavityBUnscaled] at *
    rw [hn', hcV]
    norm_num
    ring
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  obtain ⟨hdq, -, -, -⟩ := single_coeff_facts β₀ hβ₀ β h q hfix hb
  have hqh0 : 0 ≤ qh := integral_nonneg fun t => by positivity
  have hqh : qh ∈ Set.Icc (0 : ℝ) 1 := ⟨hqh0, by linarith [hq.2]⟩
  have hbj : ∀ c : ℕ, |b c| ≤ β₀ ^ 2 := fun c => by
    dsimp only [b, skCavityBCoef]
    rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
    calc β ^ 2 * |skCavityBUnscaled q qh c| ≤ β ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (abs_skCavityBUnscaled_le hq hqh c) (sq_nonneg β)
      _ ≤ β₀ ^ 2 := by linarith
  rw [← hcount, ← Finset.sum_sub_distrib]
  have hterm : ∀ j : SKCavityReplicaPair n, |skCavityReplicaPairWeight n j *
        (b (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
          ν₂ (fun σ => (∏ u : B, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
                (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (skCavityReplicaPairMap j).1 v.castSucc : ℝ) *
                (σ (skCavityReplicaPairMap j).2 v.castSucc : ℝ) - q))) -
      skCavityReplicaPairWeight n j *
        (b (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
          (ν (Fintype.card V) + ((tchf (skCavityReplicaPairMap j).1 +
            tchf (skCavityReplicaPairMap j).2) * B2 +
            blkf (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2 * A2) *
            ν (Fintype.card V - 2)))| ≤
      |skCavityReplicaPairWeight n j| * β₀ ^ 2 * (C₃ + Cc j) /
        ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := fun j => by
    rw [← mul_sub, ← mul_sub, abs_mul, abs_mul]
    have := hj j
    calc |skCavityReplicaPairWeight n j| * (|b (skCavityReplicaPairCoincidences (e (.inl p))
          (e (.inr p)) j)| * _) ≤ |skCavityReplicaPairWeight n j| * (β₀ ^ 2 *
            ((C₃ + Cc j) / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hbj _) this (abs_nonneg _) (sq_nonneg _))
            (abs_nonneg _)
      _ = _ := by ring
  refine (Finset.abs_sum_le_sum_abs _ Finset.univ).trans ?_
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  linarith

end SpinGlasses
