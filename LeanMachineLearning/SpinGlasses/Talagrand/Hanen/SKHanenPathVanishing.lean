/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPathCalculus
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenVanishing
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIterStructure

/-!
# Vanishing of the iterated cavity derivatives at the decoupled endpoint
(Talagrand, Lemmas 1.11.4 and 1.11.5)

At `u = 0` the cavity path is the decoupled system: the `N` old spins form an `N`-spin system and
the last spins `ε_r` of the replicas are independent given the Gaussian `ω`.  This module
identifies `skCavityPathMean N R β q h 0` with the decoupled replica average on
`(Fin N → ℤˣ) × ℤˣ` (`integral_skCavityPath_zero_decoupled`), so the abstract vanishing lemma
`sk_cavity_deriv_zero_vanishing` applies to it.

## Main declarations

* `SpinGlasses.skCavityPathMean_zero_vanishing`: `ν_0` of an observable
  `F(old spins) · η_V · ε_J · ∏ ε ε' · f̂(last spins)` vanishes when `2 m + r < |V|`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The old-spin energy of the decoupled cavity system. -/
noncomputable def skCavityOldEnergy (N : ℕ) (β h : ℝ) (g' : FinPairs N → ℝ)
    (r : Fin N → ℤˣ) : ℝ :=
  (Real.sqrt (N + 1))⁻¹ * β *
    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) + h * ∑ i : Fin N, (r i : ℝ)

/-- **The decoupled endpoint of the cavity path** (Talagrand, Lemma 1.6.2): at `u = 0` the
`R`-replica Gibbs average is the average over old spins and independent last spins with
energy `A(σ⁻) + ε Y`, `Y = β ω₂ √q + h`. -/
theorem integral_skCavityPath_zero_decoupled (N R : ℕ) (β q h : ℝ) (g' : FinPairs N → ℝ)
    (ω : (Fin N → ℝ) × ℝ) (G : (Fin R → Fin (N + 1) → ℤˣ) → ℝ) :
    ∫ σ : Fin R → Fin (N + 1) → ℤˣ, G σ
        ∂(Measure.pi fun _ : Fin R => Measure.count.tilted (skCavityPathEnergy N β q h 0 g' ω)) =
      ∫ x : Fin R → (Fin N → ℤˣ) × ℤˣ, G (fun r => Fin.snoc (x r).1 (x r).2)
        ∂(Measure.pi fun _ : Fin R => Measure.count.tilted
          fun y : (Fin N → ℤˣ) × ℤˣ =>
            skCavityOldEnergy N β h g' y.1 + ((y.2 : ℤˣ) : ℝ) * (β * ω.2 * Real.sqrt q + h)) := by
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (Equiv.prodComm (Fin N → ℤˣ) ℤˣ).trans (Fin.snocEquiv fun _ => ℤˣ)
  have he (x : (Fin N → ℤˣ) × ℤˣ) : e x = Fin.snoc x.1 x.2 := rfl
  rw [integral_pi_count_tilted_equiv (R := Fin R) e (skCavityPathEnergy N β q h 0 g' ω)]
  have hE : (fun x : (Fin N → ℤˣ) × ℤˣ => skCavityPathEnergy N β q h 0 g' ω (e x)) =
      fun x => skCavityOldEnergy N β h g' x.1 + ((x.2 : ℤˣ) : ℝ) * (β * ω.2 * Real.sqrt q + h) := by
    funext x
    simp only [skCavityPathEnergy, skCavityOldEnergy, he, Real.sqrt_zero, Real.arccos_zero,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.sum_univ_castSucc, zero_mul, one_mul, zero_add]
    ring
  rw [hE]
  simp only [he]

/-- At the decoupled endpoint, old-spin and last-spin observables factor after averaging
over their independent disorders. The old replicas still share the same old disorder. -/
theorem skCavityPathMean_zero_mul (N n : ℕ) (β q h : ℝ)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ) :
    skCavityPathMean N n β q h 0 (fun σ =>
      F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N))) =
      (∫ z : ℝ, ∫ ε : Fin n → ℤˣ, fhat ε
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h)) ∂gaussianReal 0 1) *
      (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  rw [skCavityPathMean_eq]
  have hinner (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ) :
      (∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          F (fun k i => σ k i.castSucc) * fhat (fun k => σ k (Fin.last N))
        ∂(Measure.pi fun _ : Fin n =>
          Measure.count.tilted (skCavityPathEnergy N β q h 0 g' ω))) =
      (∫ ε : Fin n → ℤˣ, fhat ε
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * ω.2 * Real.sqrt q + h))) *
      ∫ ρ : Fin n → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (skCavityOldEnergy N β h g')) := by
    rw [integral_skCavityPath_zero_decoupled]
    have hprod := integral_pi_count_tilted_decoupled_prod
      (skCavityOldEnergy N β h g') (β * ω.2 * Real.sqrt q + h) F fhat
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hprod, mul_comm]
  simp_rw [hinner, integral_mul_const]
  have hz : (∫ ω : (Fin N → ℝ) × ℝ,
        ∫ ε : Fin n → ℤˣ, fhat ε
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * ω.2 * Real.sqrt q + h))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      ∫ z : ℝ, ∫ ε : Fin n → ℤˣ, fhat ε
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h))
        ∂gaussianReal 0 1 :=
    integral_prod_fun_snd_of_isProbabilityMeasure
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) (gaussianReal 0 1)
      (fun z : ℝ => ∫ ε : Fin n → ℤˣ, fhat ε
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h)))
  simp_rw [hz]
  exact integral_const_mul _ _


/-- **Vanishing at the decoupled endpoint, replica form** (Talagrand, Lemmas 1.11.4, 1.11.5).
Let `F` be an observable of the old spins, `η_V = ∏_{w ∈ V} (ε_{a_w} - ε_{b_w})` a product of
spin differences over pairwise disjoint replica pairs, `ε_J` a product of last spins, `m` further
pairs `ε_a ε_b`, and `f̂` an observable of the last spins that does not depend on the replicas of
`V*`.  If `2 m + r < |V|` and `|V* ∩ J| ≤ r`, then `ν_0` of the product is `0`. -/
theorem skCavityPathMean_zero_vanishing (N R : ℕ) (β q h : ℝ) {κ : Type*}
    (V : Finset κ) (pairMap : κ → Fin R × Fin R)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (J : Finset (Fin R)) {m r : ℕ} (p : Fin m → Fin R × Fin R)
    (hcard : (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card ≤ r)
    (hr : 2 * m + r < V.card)
    (F : (Fin R → Fin N → ℤˣ) → ℝ) (fhat : (Fin R → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin R → ℤˣ) (i : Fin R) (t : ℤˣ),
      i ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    skCavityPathMean N R β q h 0 (fun σ => F (fun r i => σ r i.castSucc) *
      (∏ w ∈ V, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
        ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
      (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)) *
      (∏ j : Fin m, ((σ (p j).1 (Fin.last N) : ℤˣ) : ℝ) * ((σ (p j).2 (Fin.last N) : ℤˣ) : ℝ)) *
      fhat (fun r => σ r (Fin.last N))) = 0 := by
  rw [skCavityPathMean_eq]
  have h0 : ∀ (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ),
      ∫ σ : Fin R → Fin (N + 1) → ℤˣ, F (fun r i => σ r i.castSucc) *
        (∏ w ∈ V, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
          ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
        (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)) *
        (∏ j : Fin m, ((σ (p j).1 (Fin.last N) : ℤˣ) : ℝ) *
          ((σ (p j).2 (Fin.last N) : ℤˣ) : ℝ)) * fhat (fun r => σ r (Fin.last N))
        ∂(Measure.pi fun _ : Fin R => Measure.count.tilted (skCavityPathEnergy N β q h 0 g' ω))
        = 0 := fun g' ω => by
    rw [integral_skCavityPath_zero_decoupled]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact sk_cavity_deriv_zero_vanishing (skCavityOldEnergy N β h g') (β * ω.2 * Real.sqrt q + h)
      V pairMap hdisj J p hcard hr F fhat hfhat
  simp only [h0, integral_zero]

/-- **Talagrand's Lemma 1.11.5.**  The `m`-th derivative of `u ↦ ν_u(g)` at the decoupled
endpoint `u = 0` vanishes for `g = F(old spins) · η_V · ε_J · f̂(last spins)` when
`2 m + r < |V|` and `|V* ∩ J| ≤ r`: each derivative contributes one factor
`β² ε_a ε_b (R⁻_{ab} - q)`, which adds at most two replicas to `J` and leaves a function of the
old spins. -/
theorem iteratedDerivWithin_skCavityPathMean_zero_vanishing (N m n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {κ : Type*}
    (V : Finset κ) (pairMap : κ → Fin n × Fin n)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (J : Finset (Fin n)) {r : ℕ}
    (hcard : (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card ≤ r)
    (hr : 2 * m + r < V.card)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t
      (fun σ => F (fun k i => σ k i.castSucc) *
        (∏ w ∈ V, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
          ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
        (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)) * fhat (fun k => σ k (Fin.last N))))
      (Set.Icc 0 1) 0 = 0 := by
  rw [iteratedDerivWithin_skCavityPathMean N m β q h hq n _ 0 ⟨le_rfl, zero_le_one⟩]
  obtain ⟨T, hT, w, ι, a, b, hι, hab, hw, hiter⟩ := skCavityIterKernel_structure m n
  let ιe : Fin n ↪ Fin (skCavityIterReplicaCount m n) := ⟨ι, hι⟩
  have hfun : (skCavityIterKernel N β q m n (fun σ => F (fun k i => σ k i.castSucc) *
        (∏ w ∈ V, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
          ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
        (∏ j ∈ J, ((σ j (Fin.last N) : ℤˣ) : ℝ)) * fhat (fun k => σ k (Fin.last N)))) =
      fun τ => ∑ t, w t * (F (fun k i => τ (ι k) i.castSucc) *
        (∏ w ∈ V, (((τ (ι (pairMap w).1) (Fin.last N) : ℤˣ) : ℝ) -
          ((τ (ι (pairMap w).2) (Fin.last N) : ℤˣ) : ℝ))) *
        (∏ j ∈ J, ((τ (ι j) (Fin.last N) : ℤˣ) : ℝ)) * fhat (fun k => τ (ι k) (Fin.last N)) *
        ∏ j : Fin m, skCavityPathKernel N β q (τ (a t j)) (τ (b t j))) := by
    funext τ
    rw [hiter N β q _ τ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hfun, skCavityPathMean_finset_sum N _ β q h 0 Finset.univ w]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [mul_eq_zero]
  right
  have hdisj' : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (ι (pairMap u).1, ι (pairMap u).2).1 ≠ (ι (pairMap v).1, ι (pairMap v).2).1 ∧
      (ι (pairMap u).1, ι (pairMap u).2).1 ≠ (ι (pairMap v).1, ι (pairMap v).2).2 ∧
      (ι (pairMap u).1, ι (pairMap u).2).2 ≠ (ι (pairMap v).1, ι (pairMap v).2).1 ∧
      (ι (pairMap u).1, ι (pairMap u).2).2 ≠ (ι (pairMap v).1, ι (pairMap v).2).2 := by
    intro u hu v hv huv
    obtain ⟨h1, h2, h3, h4⟩ := hdisj u hu v hv huv
    exact ⟨hι.ne h1, hι.ne h2, hι.ne h3, hι.ne h4⟩
  have hbi : V.biUnion (fun v => {(ι (pairMap v).1, ι (pairMap v).2).1,
      (ι (pairMap v).1, ι (pairMap v).2).2}) =
      (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2})).map ιe := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_map,
      ιe, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨v, hv, hx | hx⟩
      · exact ⟨_, ⟨v, hv, Or.inl rfl⟩, hx.symm⟩
      · exact ⟨_, ⟨v, hv, Or.inr rfl⟩, hx.symm⟩
    · rintro ⟨y, ⟨v, hv, hy | hy⟩, rfl⟩
      · exact ⟨v, hv, Or.inl (by rw [hy])⟩
      · exact ⟨v, hv, Or.inr (by rw [hy])⟩
  have hcard' : (V.biUnion (fun v => {(ι (pairMap v).1, ι (pairMap v).2).1,
      (ι (pairMap v).1, ι (pairMap v).2).2}) ∩ J.map ιe).card ≤ r := by
    rw [hbi, ← Finset.map_inter, Finset.card_map]
    exact hcard
  have hfhat' : ∀ (ε : Fin (skCavityIterReplicaCount m n) → ℤˣ)
      (i : Fin (skCavityIterReplicaCount m n)) (t : ℤˣ),
      i ∈ V.biUnion (fun v => {(ι (pairMap v).1, ι (pairMap v).2).1,
        (ι (pairMap v).1, ι (pairMap v).2).2}) →
      (fun ε' : Fin (skCavityIterReplicaCount m n) → ℤˣ => fhat (fun k => ε' (ι k)))
        (Function.update ε i t) = fhat (fun k => ε (ι k)) := by
    intro ε i t hi
    rw [hbi, Finset.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    have := Function.update_comp_eq_of_injective ε hι k t
    simp only [ιe, Function.Embedding.coeFn_mk] at this ⊢
    simp only [Function.comp_def] at this
    rw [this]
    exact hfhat _ k t hk
  have key := skCavityPathMean_zero_vanishing N (skCavityIterReplicaCount m n) β q h V
    (fun v => (ι (pairMap v).1, ι (pairMap v).2)) hdisj' (J.map ιe) (fun j => (a t j, b t j))
    hcard' (by simpa using hr)
    (fun ρ => F (fun k => ρ (ι k)) * ∏ j : Fin m, (β ^ 2 * ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (ρ (a t j) i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ (b t j) i : ℝ)) - q)))
    (fun ε => fhat (fun k => ε (ι k))) hfhat'
  refine Eq.trans (congrArg (skCavityPathMean N _ β q h 0) ?_) key
  funext τ
  simp only [skCavityPathKernel, Finset.prod_map, Finset.prod_mul_distrib, ιe,
    Function.Embedding.coeFn_mk]
  ring

end SpinGlasses
