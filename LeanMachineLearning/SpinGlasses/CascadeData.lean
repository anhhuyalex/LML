/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeMoment
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi

/-!
# Vertex data of a Ruelle cascade

The data at the vertex `(p, γ)` of the tree is one random element `D (p, γ)` of a fixed space,
for example the Poisson blocks of the vertex together with the labels of its children.
Independence of the vertex data gives: the data at the root, and the data below the different
root children, are independent, the latter being i.i.d. copies of the shifted cascade.
-/

@[expose] public section

namespace SpinGlasses

open MeasureTheory ProbabilityTheory

variable {Ω 𝒟 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒟] {P : Measure Ω}

/-- The vertex of the whole tree that is the vertex `v` of the subtree below the child `n` of
the root. -/
theorem cascadeSubtreeVertex_injective :
    Function.Injective (fun nv : ℕ × (Σ p : ℕ, Fin p → ℕ) =>
      (⟨nv.2.1 + 1, Fin.cons nv.1 nv.2.2⟩ : Σ p : ℕ, Fin p → ℕ)) := by
  rintro ⟨n, ⟨p, γ⟩⟩ ⟨m, ⟨q, δ⟩⟩ h
  have hp : p = q := Nat.succ.inj (congrArg Sigma.fst h)
  subst hp
  have hcons : (Fin.cons n γ : Fin (p + 1) → ℕ) = Fin.cons m δ := eq_of_heq (Sigma.mk.inj h).2
  have hn : n = m := congrArg (fun f => f 0) hcons
  have hg : γ = δ := (Fin.cons_inj.mp hcons).2
  subst hn hg
  rfl

/-- The data below distinct children of the root are independent. -/
theorem iIndepFun_cascadeSubtreeData
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → 𝒟) (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) :
    iIndepFun (fun n ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) P := by
  let X : ℕ → (Σ p : ℕ, Fin p → ℕ) → Ω → 𝒟 := fun n v => D ⟨v.1 + 1, Fin.cons n v.2⟩
  change iIndepFun (fun n ω v => X n v ω) P
  apply iIndepFun.curry' (X := X) (fun n v => hDm _)
  exact hD.precomp (g := fun x : ℕ × (Σ p : ℕ, Fin p → ℕ) =>
    (⟨x.2.1 + 1, Fin.cons x.1 x.2.2⟩ : Σ p : ℕ, Fin p → ℕ)) cascadeSubtreeVertex_injective

/-- The data at the root is independent of the data below all root children. -/
theorem indepFun_cascadeRoot_subtreeData
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → 𝒟) (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) :
    IndepFun (D ⟨0, fun i => i.elim0⟩)
      (fun ω n (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) P := by
  let root : Set (Σ p : ℕ, Fin p → ℕ) := {⟨0, fun i => i.elim0⟩}
  let below : Set (Σ p : ℕ, Fin p → ℕ) := {v | 0 < v.1}
  have hd : Disjoint root below := Set.disjoint_left.2 fun v hr hb => by
    have h0 : v = ⟨0, fun i => i.elim0⟩ := hr
    have : 0 < v.1 := hb
    rw [h0] at this
    exact lt_irrefl _ this
  have h := hD.indepFun_set_of_disjoint hDm root below hd
  have hmem : (⟨0, fun i => i.elim0⟩ : Σ p : ℕ, Fin p → ℕ) ∈ root := rfl
  have f1 : Measurable fun x : root → 𝒟 => x ⟨⟨0, fun i => i.elim0⟩, hmem⟩ :=
    measurable_pi_apply _
  have f2 : Measurable fun y : below → 𝒟 => fun (n : ℕ) (v : Σ p : ℕ, Fin p → ℕ) =>
      y ⟨⟨v.1 + 1, Fin.cons n v.2⟩, Nat.succ_pos _⟩ :=
    measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun v => measurable_pi_apply _
  exact h.comp f1 f2

/-- The data below one child of the root has the law of the shifted cascade. -/
theorem hasLaw_cascadeSubtreeData [IsProbabilityMeasure P]
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → 𝒟) (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P)
    (𝔡 : ℕ → Measure 𝒟) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P) (n : ℕ) :
    HasLaw (fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω)
      (Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)) P := by
  have hinj : Function.Injective fun v : Σ p : ℕ, Fin p → ℕ =>
      (⟨v.1 + 1, Fin.cons n v.2⟩ : Σ p : ℕ, Fin p → ℕ) :=
    fun a b h => by simpa using cascadeSubtreeVertex_injective (a₁ := (n, a)) (a₂ := (n, b)) h
  exact HasLaw.infinitePi (fun v => hDm _) (hD.precomp hinj) fun v => hDlaw _

/-- Joint law of the root data and the vector of subtree data. -/
theorem hasLaw_cascadeRoot_subtreeData [IsProbabilityMeasure P]
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → 𝒟) (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P)
    (𝔡 : ℕ → Measure 𝒟) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P) :
    HasLaw (fun ω => (D ⟨0, fun i => i.elim0⟩ ω,
        fun n (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω))
      ((𝔡 0).prod (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1))) P := by
  have hSm : Measurable fun ω n (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω :=
    measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun v => hDm _
  have hS := HasLaw.infinitePi (fun n => measurable_pi_iff.2 fun v => hDm _)
    (iIndepFun_cascadeSubtreeData D hDm hD) (fun n => hasLaw_cascadeSubtreeData D hDm hD 𝔡 hDlaw n)
  have hind := indepFun_cascadeRoot_subtreeData D hDm hD
  refine ⟨((hDm _).prodMk hSm).aemeasurable, ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hDm _).aemeasurable hSm.aemeasurable).1 hind,
    hS.map_eq, (hDlaw ⟨0, fun i => i.elim0⟩).map_eq]

/-- The data of the subtree below one child of the root is again an independent family. -/
theorem iIndepFun_cascadeChildData
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → 𝒟) (hD : iIndepFun D P) (n : ℕ) :
    iIndepFun (fun (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩) P :=
  hD.precomp (g := fun v : Σ p : ℕ, Fin p → ℕ =>
    (⟨v.1 + 1, Fin.cons n v.2⟩ : Σ p : ℕ, Fin p → ℕ))
    fun a b h => by simpa using cascadeSubtreeVertex_injective (a₁ := (n, a)) (a₂ := (n, b)) h

end SpinGlasses
