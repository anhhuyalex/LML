/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.ProductExpansion
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.MeasurePreservingSymmetry
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ReplicaOverlaps

/-!
# Integrating fresh replica pairs in products

A disjoint sum of index types separates the original replicas from two fresh replicas per
factor. Each fresh replica is integrated exactly once; the factors may share original
replicas. The identities are independent of Gibbs energies and of any spin model.

The general statements concern vector-valued observables, jointly integrable products on a
σ-finite space (`_of_integrable`), and overlaps `c ⟪v x, v y⟫` of an a.e. bounded map `v` into
a real Hilbert space (`_inner`). The statements for finite configuration spaces and coordinate
vectors are special cases.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace MeasureTheory

section Marginals

variable {R R' S X E : Type*} [Fintype R] [Fintype R'] [Fintype S] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Marginal along an injection of the replicas, for any replica law.** An observable of the
replicas `ρ r` (`ρ : R → R'` injective) has the same average under `R'` i.i.d. replicas as under
`R` i.i.d. replicas. Only a.e. strong measurability is needed. -/
theorem integral_pi_comp_injective (ν : Measure X) [IsProbabilityMeasure ν] {ρ : R → R'}
    (hρ : Function.Injective ρ) (G : (R → X) → E)
    (hG : AEStronglyMeasurable G (Measure.pi fun _ : R => ν)) :
    ∫ τ : R' → X, G (fun r => τ (ρ r)) ∂(Measure.pi fun _ : R' => ν) =
      ∫ σ : R → X, G σ ∂(Measure.pi fun _ : R => ν) :=
  (measurePreserving_pi_comp_injective ν hρ).integral_comp_of_aestronglyMeasurable hG

/-- **Moving one replica to a fresh one, general form.** If `F` does not depend on the replica
`k`, then the average of `Φ (F σ) (σ i) (σ k)` equals that of `Φ (F σ) (σ i) (σ x₀)`, where `x₀`
is a replica outside the range of the injection `e` and `i ≠ k`. Products, scalar multiples and
bilinear expressions are all of this form. -/
theorem integral_pi_replace_replica_apply [DecidableEq R] {α : Type*} (ν : Measure X)
    [IsProbabilityMeasure ν] {e : R → R'} (he : Function.Injective e) {x₀ : R'}
    (hx₀ : ∀ r, e r ≠ x₀) {i k : R} (hik : i ≠ k) (F : (R → X) → α)
    (hF : ∀ σ x, F (Function.update σ k x) = F σ) (Φ : α → X → X → E)
    (hm : AEStronglyMeasurable (fun σ : R → X => Φ (F σ) (σ i) (σ k))
      (Measure.pi fun _ : R => ν)) :
    ∫ τ : R' → X, Φ (F (fun r => τ (e r))) (τ (e i)) (τ (e k)) ∂(Measure.pi fun _ : R' => ν) =
      ∫ τ : R' → X, Φ (F (fun r => τ (e r))) (τ (e i)) (τ x₀) ∂(Measure.pi fun _ : R' => ν) := by
  have he' : Function.Injective (Function.update e k x₀) := by
    intro r r' h
    by_cases hr : r = k <;> by_cases hr' : r' = k
    · rw [hr, hr']
    · subst hr
      simp only [Function.update_self, Function.update_of_ne hr'] at h
      exact absurd h.symm (hx₀ r')
    · subst hr'
      simp only [Function.update_self, Function.update_of_ne hr] at h
      exact absurd h (hx₀ r)
    · simp only [Function.update_of_ne hr, Function.update_of_ne hr'] at h
      exact he h
  have h1 := integral_pi_comp_injective ν he (fun σ : R → X => Φ (F σ) (σ i) (σ k)) hm
  have h2 := integral_pi_comp_injective ν he' (fun σ : R → X => Φ (F σ) (σ i) (σ k)) hm
  refine h1.trans (h2.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)))
  have hc : (fun r => τ (Function.update e k x₀ r)) =
      Function.update (fun r => τ (e r)) k (τ x₀) := Function.comp_update τ e k x₀
  simp only [hc, hF, Function.update_self, Function.update_of_ne hik]

/-- **Moving one replica to a fresh one, for any replica law.** If `F` does not depend on the
replica `k`, then the average of `F · K(σ_i, σ_k)` equals that of `F · K(σ_i, σ_{x₀})`, where `x₀`
is a replica outside the range of the injection `e` and `i ≠ k`. -/
theorem integral_pi_replace_replica [DecidableEq R] (ν : Measure X) [IsProbabilityMeasure ν]
    {e : R → R'} (he : Function.Injective e) {x₀ : R'} (hx₀ : ∀ r, e r ≠ x₀) {i k : R}
    (hik : i ≠ k) (F : (R → X) → ℝ) (hF : ∀ σ x, F (Function.update σ k x) = F σ)
    (K : X → X → ℝ)
    (hm : AEStronglyMeasurable (fun σ : R → X => F σ * K (σ i) (σ k))
      (Measure.pi fun _ : R => ν)) :
    ∫ τ : R' → X, F (fun r => τ (e r)) * K (τ (e i)) (τ (e k)) ∂(Measure.pi fun _ : R' => ν) =
      ∫ τ : R' → X, F (fun r => τ (e r)) * K (τ (e i)) (τ x₀) ∂(Measure.pi fun _ : R' => ν) :=
  integral_pi_replace_replica_apply ν he hx₀ hik F hF (fun a x y => a * K x y) hm

/-- Split a finite replica family into two independent blocks on a sigma-finite space.
The integrability hypothesis is automatic for finite configuration spaces. -/
theorem integral_pi_sum_type (μ : Measure X) [SigmaFinite μ]
    (F : (R → X) → (S → X) → E)
    (hF : Integrable (fun p : (R → X) × (S → X) => F p.1 p.2)
      ((Measure.pi fun _ : R => μ).prod (Measure.pi fun _ : S => μ))) :
    (∫ σ : R ⊕ S → X, F (fun r => σ (.inl r)) (fun s => σ (.inr s))
      ∂(Measure.pi fun _ => μ)) =
    ∫ ρ : R → X, ∫ τ : S → X, F ρ τ ∂(Measure.pi fun _ => μ)
      ∂(Measure.pi fun _ => μ) := by
  have he := measurePreserving_sumPiEquivProdPi (X := fun _ : R ⊕ S => X) (fun _ => μ)
  exact (he.integral_comp' (g := fun p : (R → X) × (S → X) => F p.1 p.2)).trans
    (integral_prod _ hF)

/-- Functions of two disjoint replica blocks have a factorized average, for a scalar and a
vector observable. Neither measurability nor integrability is needed. -/
theorem integral_pi_sum_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (μ : Measure X)
    [SigmaFinite μ] (F : (R → X) → 𝕜) (G : (S → X) → E) :
    (∫ σ : R ⊕ S → X, F (fun r => σ (.inl r)) • G (fun s => σ (.inr s))
      ∂(Measure.pi fun _ => μ)) =
      (∫ ρ : R → X, F ρ ∂(Measure.pi fun _ => μ)) •
        ∫ τ : S → X, G τ ∂(Measure.pi fun _ => μ) := by
  have he := measurePreserving_sumPiEquivProdPi (X := fun _ : R ⊕ S => X) (fun _ => μ)
  exact (he.integral_comp' (g := fun p : (R → X) × (S → X) => F p.1 • G p.2)).trans
    (integral_prod_smul F G)

/-- Functions of two disjoint replica blocks have a factorized average. Neither measurability
nor integrability is needed. -/
theorem integral_pi_sum_mul {𝕜 : Type*} [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (F : (R → X) → 𝕜) (G : (S → X) → 𝕜) :
    (∫ σ : R ⊕ S → X, F (fun r => σ (.inl r)) * G (fun s => σ (.inr s))
      ∂(Measure.pi fun _ => μ)) =
      (∫ ρ : R → X, F ρ ∂(Measure.pi fun _ => μ)) *
        ∫ τ : S → X, G τ ∂(Measure.pi fun _ => μ) :=
  integral_pi_sum_smul μ F G

end Marginals

section FreshPairs

variable {R J X 𝕜 : Type*} [Fintype R] [Fintype J] [MeasurableSpace X] [RCLike 𝕜]

/-- **Integrating a distinct fresh pair for every factor** replaces each factor by its pair
average, even when all factors depend on shared original replicas. Only the integrability of the
whole product on a σ-finite space is needed. -/
theorem integral_pi_prod_fresh_pairs_of_integrable (μ : Measure X) [SigmaFinite μ]
    (K : J → (R → X) → X → X → 𝕜)
    (hK : Integrable (fun σ : R ⊕ (J ⊕ J) → X =>
      ∏ j, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j))))
      (Measure.pi fun _ => μ)) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))
      ∂(Measure.pi fun _ => μ)) =
    ∫ ρ : R → X, ∏ j, ∫ x, ∫ y, K j ρ x y ∂μ ∂μ
      ∂(Measure.pi fun _ => μ) := by
  have he := measurePreserving_sumPiEquivProdPi (X := fun _ : R ⊕ (J ⊕ J) => X) (fun _ => μ)
  have h2 : Integrable (fun p : (R → X) × (J ⊕ J → X) =>
      ∏ j, K j p.1 (p.2 (.inl j)) (p.2 (.inr j)))
      ((Measure.pi fun _ : R => μ).prod (Measure.pi fun _ : J ⊕ J => μ)) :=
    (he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 hK
  rw [integral_pi_sum_type μ (fun (ρ : R → X) (τ : J ⊕ J → X) =>
    ∏ j, K j ρ (τ (.inl j)) (τ (.inr j))) h2]
  refine integral_congr_ae ?_
  filter_upwards [h2.prod_right_ae] with ρ hρ
  have he' := measurePreserving_sumPiEquivProdPi (X := fun _ : J ⊕ J => X) (fun _ => μ)
  have h3 : Integrable (fun p : (J → X) × (J → X) => ∏ j, K j ρ (p.1 j) (p.2 j))
      ((Measure.pi fun _ : J => μ).prod (Measure.pi fun _ : J => μ)) :=
    (he'.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 hρ
  rw [integral_pi_sum_type μ (fun (x y : J → X) => ∏ j, K j ρ (x j) (y j)) h3]
  have hy (x : J → X) : (∫ y : J → X, ∏ j, K j ρ (x j) (y j) ∂(Measure.pi fun _ => μ)) =
      ∏ j, ∫ y, K j ρ (x j) y ∂μ :=
    integral_fintype_prod_eq_prod (μ := fun _ : J => μ) (fun j y => K j ρ (x j) y)
  simp_rw [hy]
  exact integral_fintype_prod_eq_prod (μ := fun _ : J => μ)
    (fun j x => ∫ y, K j ρ x y ∂μ)

/-- Integrating a distinct fresh pair for every factor, on a finite configuration space. -/
theorem integral_pi_prod_fresh_pairs [Finite X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (K : J → (R → X) → X → X → ℝ) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))
      ∂(Measure.pi fun _ => μ)) =
    ∫ ρ : R → X, ∏ j, ∫ x, ∫ y, K j ρ x y ∂μ ∂μ
      ∂(Measure.pi fun _ => μ) :=
  integral_pi_prod_fresh_pairs_of_integrable μ K Integrable.of_finite

/-- Integrate any finite subfamily of fresh-pair factors whose product is integrable. Unused
fresh replicas integrate to one because the reference measure is a probability measure. -/
theorem integral_pi_finset_prod_fresh_pairs_of_integrable (μ : Measure X)
    [IsProbabilityMeasure μ] (s : Finset J) (K : J → (R → X) → X → X → 𝕜)
    (hK : Integrable (fun σ : R ⊕ (J ⊕ J) → X =>
      ∏ j ∈ s, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j))))
      (Measure.pi fun _ => μ)) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))
      ∂(Measure.pi fun _ => μ)) =
      ∫ ρ : R → X, ∏ j ∈ s, ∫ x, ∫ y, K j ρ x y ∂μ ∂μ
        ∂(Measure.pi fun _ => μ) := by
  classical
  have hprod (f : J → 𝕜) : (∏ j, if j ∈ s then f j else 1) = ∏ j ∈ s, f j := by
    simp only [Finset.prod_ite_mem, Finset.univ_inter]
  have hh := integral_pi_prod_fresh_pairs_of_integrable μ
    (fun j ρ x y => if j ∈ s then K j ρ x y else 1)
    (hK.congr (ae_of_all _ fun σ => (hprod _).symm))
  have havg (j : J) (ρ : R → X) :
      (∫ x, ∫ y, (if j ∈ s then K j ρ x y else 1) ∂μ ∂μ) =
        if j ∈ s then ∫ x, ∫ y, K j ρ x y ∂μ ∂μ else 1 := by
    by_cases hj : j ∈ s <;> simp [hj]
  simpa only [havg, hprod] using hh

/-- Integrate any finite subfamily of fresh-pair factors on a finite configuration space. -/
theorem integral_pi_finset_prod_fresh_pairs [Finite X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset J)
    (K : J → (R → X) → X → X → ℝ) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))
      ∂(Measure.pi fun _ => μ)) =
      ∫ ρ : R → X, ∏ j ∈ s, ∫ x, ∫ y, K j ρ x y ∂μ ∂μ
        ∂(Measure.pi fun _ => μ) :=
  integral_pi_finset_prod_fresh_pairs_of_integrable μ s K Integrable.of_finite

/-- If two fresh-pair factors have the same conditional average, deleting either has the same
expectation, for integrable products on a probability space. -/
theorem integral_pi_prod_fresh_pairs_erase_eq_of_integrable [DecidableEq J] (μ : Measure X)
    [IsProbabilityMeasure μ] (s : Finset J) (K : J → (R → X) → X → X → 𝕜) {u v : J}
    (hu : u ∈ s) (hv : v ∈ s)
    (he : ∀ ρ, (∫ x, ∫ y, K u ρ x y ∂μ ∂μ) = ∫ x, ∫ y, K v ρ x y ∂μ ∂μ)
    (hiu : Integrable (fun σ : R ⊕ (J ⊕ J) → X => ∏ j ∈ s.erase u,
      K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j))))
      (Measure.pi fun _ => μ))
    (hiv : Integrable (fun σ : R ⊕ (J ⊕ J) → X => ∏ j ∈ s.erase v,
      K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j))))
      (Measure.pi fun _ => μ)) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase u, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ)) =
    ∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase v, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ) := by
  rw [integral_pi_finset_prod_fresh_pairs_of_integrable μ _ K hiu,
    integral_pi_finset_prod_fresh_pairs_of_integrable μ _ K hiv]
  apply integral_congr_ae (ae_of_all _ fun ρ => ?_)
  apply Finset.prod_erase_eq_of_eq _ _ hu hv
  exact he ρ

/-- If two fresh-pair factors have the same conditional average, deleting either has
the same expectation. This identifies the surviving moments in Talagrand's Eq. (1.312)
without constructing replica permutations. -/
theorem integral_pi_prod_fresh_pairs_erase_eq [DecidableEq J]
    [Finite X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset J)
    (K : J → (R → X) → X → X → ℝ) {u v : J} (hu : u ∈ s) (hv : v ∈ s)
    (he : ∀ ρ, (∫ x, ∫ y, K u ρ x y ∂μ ∂μ) = ∫ x, ∫ y, K v ρ x y ∂μ ∂μ) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase u, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ)) =
    ∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase v, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ) :=
  integral_pi_prod_fresh_pairs_erase_eq_of_integrable μ s K hu hv he
    Integrable.of_finite Integrable.of_finite

end FreshPairs

section Inner

variable {R J X H : Type*} [Fintype R] [Fintype J] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A product of flagged overlaps of an a.e. bounded observable is integrable over the original
and fresh replicas. -/
theorem integrable_finset_prod_flagged_inner (μ : Measure X) [IsProbabilityMeasure μ]
    {v : X → H} (hv : MemLp v ∞ μ) (c : ℝ) (k : J → ℝ) (a a' : J → R) (L S : J → Bool)
    (s : Finset J) :
    Integrable (fun σ : R ⊕ (J ⊕ J) → X => ∏ j ∈ s,
      (c * inner ℝ
        (if L j then v (σ (.inl (a j))) - v (σ (.inr (.inl j))) else v (σ (.inr (.inl j))))
        (if S j then v (σ (.inl (a' j))) - v (σ (.inr (.inr j))) else v (σ (.inr (.inr j))))
        - k j)) (Measure.pi fun _ => μ) := by
  classical
  have hev (x : R ⊕ (J ⊕ J)) :
      MemLp (fun σ : R ⊕ (J ⊕ J) → X => v (σ x)) ∞ (Measure.pi fun _ => μ) :=
    memLp_top_comp_eval μ hv x
  have hflag (P : Bool) (x y : R ⊕ (J ⊕ J)) :
      MemLp (fun σ : R ⊕ (J ⊕ J) → X => if P then v (σ x) - v (σ y) else v (σ y)) ∞
        (Measure.pi fun _ => μ) := by
    cases P
    · simpa using hev y
    · simp only [ite_true]
      exact (hev x).sub (hev y)
  have hfac (j : J) := memLp_top_const_mul_inner_sub c (k j)
    (hflag (L j) (.inl (a j)) (.inr (.inl j))) (hflag (S j) (.inl (a' j)) (.inr (.inr j)))
  have hmem : MemLp (∏ j ∈ s, fun σ : R ⊕ (J ⊕ J) → X => c * inner ℝ
      (if L j then v (σ (.inl (a j))) - v (σ (.inr (.inl j))) else v (σ (.inr (.inl j))))
      (if S j then v (σ (.inl (a' j))) - v (σ (.inr (.inr j))) else v (σ (.inr (.inr j))))
      - k j) ∞ (Measure.pi fun _ => μ) :=
    Finset.prod_induction _ (fun g => MemLp g ∞ (Measure.pi fun _ : R ⊕ (J ⊕ J) => μ))
      (fun f g hf hg => hf.mul hg) (memLp_const 1) fun j _ => hfac j
  refine (hmem.integrable le_top).congr (ae_of_all _ fun σ => ?_)
  simp only [Finset.prod_apply]

variable [CompleteSpace H]

/-- The double average of a flagged overlap kernel replaces both fresh observations
by their common mean. The two fixed vectors are arbitrary; no replica labels are needed. -/
theorem integral_flagged_inner_eq (μ : Measure X) [IsProbabilityMeasure μ] {v : X → H}
    (hv : Integrable v μ) {b : H} (hb : ∫ x, v x ∂μ = b) (c q : ℝ) (u w : H) (L S : Bool) :
    (∫ x, ∫ y, (c * inner ℝ (if L then u - v x else v x) (if S then w - v y else v y)) -
        (if L || S then 0 else q) ∂μ ∂μ) =
      c * inner ℝ (if L then u - b else b) (if S then w - b else b) -
        (if L || S then 0 else q) := by
  have hflag (P : Bool) (z : H) : Integrable (fun x => if P then z - v x else v x) μ ∧
      ∫ x, (if P then z - v x else v x) ∂μ = if P then z - b else b := by
    cases P
    · simpa using And.intro hv hb
    · simp only [ite_true]
      refine ⟨(integrable_const z).sub hv, ?_⟩
      rw [integral_sub (integrable_const z) hv, hb, integral_const, probReal_univ, one_smul]
  obtain ⟨hA, hAm⟩ := hflag L u
  obtain ⟨hB, hBm⟩ := hflag S w
  set k : ℝ := if L || S then 0 else q
  have hy (z : H) : (∫ y, (c * inner ℝ z (if S then w - v y else v y)) - k ∂μ) =
      c * inner ℝ z (if S then w - b else b) - k := by
    rw [integral_sub ((hB.const_inner (𝕜 := ℝ) z).const_mul c) (integrable_const _),
      integral_const_mul, integral_inner hB, hBm, integral_const, probReal_univ, one_smul]
  simp_rw [hy]
  rw [integral_sub ((hA.inner_const (𝕜 := ℝ) _).const_mul c) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  simp_rw [real_inner_comm (if S then w - b else b)]
  rw [integral_inner hA, hAm]

/-- **Fresh-mean substitution on any finite subset of flagged factors,** for an a.e. bounded
observable with values in a Hilbert space. The fresh replica family stays fixed when factors are
deleted, which is useful for moment induction on subsets. -/
theorem integral_finset_prod_flagged_inner_fresh_eq (μ : Measure X) [IsProbabilityMeasure μ]
    {v : X → H} (hv : MemLp v ∞ μ) {b : H} (hb : ∫ x, v x ∂μ = b) (c q : ℝ)
    (a a' : J → R) (L S : J → Bool) (s : Finset J) :
    (∫ σ : R ⊕ (J ⊕ J) → X, ∏ j ∈ s,
      (c * inner ℝ
        (if L j then v (σ (.inl (a j))) - v (σ (.inr (.inl j))) else v (σ (.inr (.inl j))))
        (if S j then v (σ (.inl (a' j))) - v (σ (.inr (.inr j))) else v (σ (.inr (.inr j))))
        - (if L j || S j then 0 else q)) ∂(Measure.pi fun _ => μ)) =
      ∫ ρ : R → X, ∏ j ∈ s,
        (c * inner ℝ (if L j then v (ρ (a j)) - b else b)
          (if S j then v (ρ (a' j)) - b else b) - (if L j || S j then 0 else q))
        ∂(Measure.pi fun _ => μ) := by
  let K : J → (R → X) → X → X → ℝ := fun j ρ x y =>
    c * inner ℝ (if L j then v (ρ (a j)) - v x else v x)
      (if S j then v (ρ (a' j)) - v y else v y) - (if L j || S j then 0 else q)
  refine (integral_pi_finset_prod_fresh_pairs_of_integrable μ s K
    (integrable_finset_prod_flagged_inner μ hv c (fun j => if L j || S j then 0 else q)
      a a' L S s)).trans (integral_congr_ae (ae_of_all _ fun ρ => ?_))
  refine Finset.prod_congr rfl fun j _ => ?_
  exact integral_flagged_inner_eq μ (hv.integrable le_top) hb c q (v (ρ (a j))) (v (ρ (a' j)))
    (L j) (S j)

omit [CompleteSpace H] in
/-- **Identifying deleted fresh-overlap products in Eq. (1.312),** for an a.e. bounded
observable with values in a Hilbert space. Matching factor classes and the original labels they
actually use suffice; unused labels need not match. -/
theorem integral_fresh_inner_prod_erase_eq [DecidableEq J] (μ : Measure X)
    [IsProbabilityMeasure μ] {v : X → H} (hv : MemLp v ∞ μ) (c q : ℝ) (a a' : J → R)
    (L S : J → Bool) (s : Finset J) {u w : J} (hu : u ∈ s) (hw : w ∈ s) (hL : L u = L w)
    (hS : S u = S w) (ha : L u = true → a u = a w) (ha' : S u = true → a' u = a' w) :
    let K : J → (R → X) → X → X → ℝ := fun j ρ x y =>
      c * inner ℝ (if L j then v (ρ (a j)) - v x else v x)
        (if S j then v (ρ (a' j)) - v y else v y) - (if L j || S j then 0 else q)
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase u, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ)) =
    ∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase w, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ) := by
  intro K
  have hi (t : Finset J) := integrable_finset_prod_flagged_inner μ hv c
    (fun j => if L j || S j then 0 else q) a a' L S t
  refine integral_pi_prod_fresh_pairs_erase_eq_of_integrable μ s K hu hw (fun ρ => ?_)
    (hi _) (hi _)
  have he (x y : X) : K u ρ x y = K w ρ x y := by
    cases hLu : L u <;> cases hSu : S u <;> simp_all [K]
  simp_rw [he]

/-- **The replica-mean substitution for arbitrary mixed products (Talagrand (1.305)),** for an
a.e. bounded observable with values in a Hilbert space. The three finite factor classes
correspond to centered pair overlaps, a centered replica against the mean, and the squared mean
minus `q`. Distinct sum-type labels supply a fresh pair for every factor, including repeated
original labels. -/
theorem integral_replica_centered_products_inner {P S G : Type*} [Fintype P] [Fintype S]
    [Fintype G] (μ : Measure X) [IsProbabilityMeasure μ] {v : X → H} (hv : MemLp v ∞ μ)
    {b : H} (hb : ∫ x, v x ∂μ = b) (c q : ℝ) (a a' : P → R) (d : S → R) :
    let J := P ⊕ (S ⊕ G)
    (∫ σ : R ⊕ (J ⊕ J) → X,
      (∏ p : P, c * inner ℝ (v (σ (.inl (a p))) - v (σ (.inr (.inl (.inl p)))))
        (v (σ (.inl (a' p))) - v (σ (.inr (.inr (.inl p)))))) *
      (∏ s : S, c * inner ℝ (v (σ (.inl (d s))) - v (σ (.inr (.inl (.inr (.inl s))))))
        (v (σ (.inr (.inr (.inr (.inl s))))))) *
      (∏ g : G, (c * inner ℝ (v (σ (.inr (.inl (.inr (.inr g))))))
        (v (σ (.inr (.inr (.inr (.inr g)))))) - q))
      ∂(Measure.pi fun _ => μ)) =
    ∫ ρ : R → X,
      (∏ p : P, c * inner ℝ (v (ρ (a p)) - b) (v (ρ (a' p)) - b)) *
      (∏ s : S, c * inner ℝ (v (ρ (d s)) - b) b) *
      (∏ _ : G, (c * inner ℝ b b - q))
      ∂(Measure.pi fun _ => μ) := by
  intro J
  let K : J → (R → X) → X → X → ℝ := fun j ρ x y =>
    Sum.elim
      (fun p => c * inner ℝ (v (ρ (a p)) - v x) (v (ρ (a' p)) - v y))
      (Sum.elim
        (fun s => c * inner ℝ (v (ρ (d s)) - v x) (v y))
        (fun _ : G => c * inner ℝ (v x) (v y) - q)) j
  have hprod (σ : R ⊕ (J ⊕ J) → X) :
      (∏ j, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))) =
      (∏ p : P, c * inner ℝ (v (σ (.inl (a p))) - v (σ (.inr (.inl (.inl p)))))
        (v (σ (.inl (a' p))) - v (σ (.inr (.inr (.inl p)))))) *
      (∏ s : S, c * inner ℝ (v (σ (.inl (d s))) - v (σ (.inr (.inl (.inr (.inl s))))))
        (v (σ (.inr (.inr (.inr (.inl s))))))) *
      (∏ g : G, (c * inner ℝ (v (σ (.inr (.inl (.inr (.inr g))))))
        (v (σ (.inr (.inr (.inr (.inr g)))))) - q)) := by
    simp only [J, Fintype.prod_sum_type, K, Sum.elim_inl, Sum.elim_inr]
    ring
  have hev (x : R ⊕ (J ⊕ J)) :
      MemLp (fun σ : R ⊕ (J ⊕ J) → X => v (σ x)) ∞ (Measure.pi fun _ => μ) := by
    classical
    exact memLp_top_comp_eval μ hv x
  have hfac (j : J) : MemLp (fun σ : R ⊕ (J ⊕ J) → X =>
      K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))) ∞
      (Measure.pi fun _ => μ) := by
    rcases j with p | s | g
    · simpa only [K, Sum.elim_inl, sub_zero, Pi.sub_apply] using
        memLp_top_const_mul_inner_sub c 0 ((hev (.inl (a p))).sub (hev (.inr (.inl (.inl p)))))
          ((hev (.inl (a' p))).sub (hev (.inr (.inr (.inl p)))))
    · simpa only [K, Sum.elim_inr, Sum.elim_inl, sub_zero, Pi.sub_apply] using
        memLp_top_const_mul_inner_sub c 0
          ((hev (.inl (d s))).sub (hev (.inr (.inl (.inr (.inl s))))))
          (hev (.inr (.inr (.inr (.inl s)))))
    · simpa only [K, Sum.elim_inr] using
        memLp_top_const_mul_inner_sub c q (hev (.inr (.inl (.inr (.inr g)))))
          (hev (.inr (.inr (.inr (.inr g)))))
  have hK : Integrable (fun σ : R ⊕ (J ⊕ J) → X =>
      ∏ j, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j))))
      (Measure.pi fun _ => μ) := by
    have hmem : MemLp (∏ j : J, fun σ : R ⊕ (J ⊕ J) → X =>
        K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))) ∞
        (Measure.pi fun _ => μ) :=
      Finset.prod_induction _ (fun g => MemLp g ∞ (Measure.pi fun _ : R ⊕ (J ⊕ J) => μ))
        (fun f g hf hg => hf.mul hg) (memLp_const 1) fun j _ => hfac j
    refine (hmem.integrable le_top).congr (ae_of_all _ fun σ => ?_)
    simp only [Finset.prod_apply]
  rw [← integral_congr_ae (ae_of_all _ hprod), integral_pi_prod_fresh_pairs_of_integrable μ K hK]
  apply integral_congr_ae (ae_of_all _ fun ρ => ?_)
  have hvi : Integrable v μ := hv.integrable le_top
  have hpair (p : P) : (∫ x, ∫ y, K (.inl p) ρ x y ∂μ ∂μ) =
      c * inner ℝ (v (ρ (a p)) - b) (v (ρ (a' p)) - b) := by
    simpa only [K, Sum.elim_inl, ite_true, Bool.true_or, sub_zero] using
      integral_flagged_inner_eq μ hvi hb c q (v (ρ (a p))) (v (ρ (a' p))) true true
  have hone (s : S) : (∫ x, ∫ y, K (.inr (.inl s)) ρ x y ∂μ ∂μ) =
      c * inner ℝ (v (ρ (d s)) - b) b := by
    simpa only [K, Sum.elim_inr, Sum.elim_inl, Bool.false_eq_true, ite_true, ite_false,
      Bool.true_or, sub_zero] using
      integral_flagged_inner_eq μ hvi hb c q (v (ρ (d s))) 0 true false
  have hglobal (g : G) : (∫ x, ∫ y, K (.inr (.inr g)) ρ x y ∂μ ∂μ) =
      c * inner ℝ b b - q := by
    simpa only [K, Sum.elim_inr, Bool.false_eq_true, ite_false, Bool.false_or] using
      integral_flagged_inner_eq μ hvi hb c q 0 0 false false
  simp only [J, Fintype.prod_sum_type, hpair, hone, hglobal]
  ring

end Inner

section Coordinates

variable {R J I X : Type*} [Fintype R] [Fintype J] [Fintype I] [Finite X]
  [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The flagged overlap of two coordinate vectors is the sum over the coordinates. -/
theorem inner_flagged_toLp_two_eq_sum (u w x y : I → ℝ) (L S : Bool) :
    inner ℝ (if L then WithLp.toLp 2 u - WithLp.toLp 2 x else WithLp.toLp 2 x)
        (if S then WithLp.toLp 2 w - WithLp.toLp 2 y else WithLp.toLp 2 y) =
      ∑ i, (if L then u i - x i else x i) * (if S then w i - y i else y i) := by
  cases L <;> cases S <;>
    simp only [Bool.false_eq_true, ite_true, ite_false, ← WithLp.toLp_sub,
      inner_toLp_two_eq_sum, Pi.sub_apply]

/-- The double average of a flagged overlap kernel of coordinate vectors replaces both fresh
observations by their common mean. -/
theorem integral_flagged_overlap_eq (μ : Measure X) [IsProbabilityMeasure μ] (v : X → I → ℝ)
    (b : I → ℝ) (hb : ∀ i, ∫ x, v x i ∂μ = b i) (c q : ℝ) (u w : I → ℝ) (L S : Bool) :
    (∫ x, ∫ y, (c * ∑ i,
      (if L then u i - v x i else v x i) * (if S then w i - v y i else v y i)) -
        (if L || S then 0 else q) ∂μ ∂μ) =
      (c * ∑ i, (if L then u i - b i else b i) * (if S then w i - b i else b i)) -
        (if L || S then 0 else q) := by
  simpa only [inner_flagged_toLp_two_eq_sum] using
    integral_flagged_inner_eq μ (v := fun x => WithLp.toLp 2 (v x)) Integrable.of_finite
      (integral_toLp_two_eq_of_finite μ v hb) c q (WithLp.toLp 2 u) (WithLp.toLp 2 w) L S

/-- **Fresh-mean substitution on any finite subset of flagged factors** of coordinate vectors on
a finite space. -/
theorem integral_finset_prod_flagged_fresh_eq (μ : Measure X) [IsProbabilityMeasure μ]
    (v : X → I → ℝ) (b : I → ℝ) (hb : ∀ i, ∫ x, v x i ∂μ = b i) (c q : ℝ)
    (a a' : J → R) (L S : J → Bool) (s : Finset J) :
    (∫ σ : R ⊕ (J ⊕ J) → X, ∏ j ∈ s,
      ((c * ∑ i,
        (if L j then v (σ (.inl (a j))) i - v (σ (.inr (.inl j))) i
          else v (σ (.inr (.inl j))) i) *
        (if S j then v (σ (.inl (a' j))) i - v (σ (.inr (.inr j))) i
          else v (σ (.inr (.inr j))) i)) - (if L j || S j then 0 else q))
      ∂(Measure.pi fun _ => μ)) =
      ∫ ρ : R → X, ∏ j ∈ s,
        ((c * ∑ i, (if L j then v (ρ (a j)) i - b i else b i) *
          (if S j then v (ρ (a' j)) i - b i else b i)) -
            (if L j || S j then 0 else q)) ∂(Measure.pi fun _ => μ) := by
  have h := integral_finset_prod_flagged_inner_fresh_eq μ
    (v := fun x => WithLp.toLp 2 (v x)) MemLp.of_discrete
    (integral_toLp_two_eq_of_finite μ v hb) c q a a' L S s
  have hmean (u : I → ℝ) (P : Bool) :
      (if P then WithLp.toLp 2 u - WithLp.toLp 2 b else WithLp.toLp 2 b) =
        WithLp.toLp 2 fun i => if P then u i - b i else b i := by
    cases P <;> rfl
  simpa only [inner_flagged_toLp_two_eq_sum, hmean, inner_toLp_two_eq_sum] using h

/-- **Identifying deleted fresh-overlap products in Eq. (1.312)** for coordinate vectors on a
finite space. -/
theorem integral_fresh_overlap_prod_erase_eq [DecidableEq J]
    (μ : Measure X) [IsProbabilityMeasure μ] (v : X → I → ℝ) (c q : ℝ)
    (a b : J → R) (L S : J → Bool) (s : Finset J) {u w : J}
    (hu : u ∈ s) (hw : w ∈ s) (hL : L u = L w) (hS : S u = S w)
    (ha : L u = true → a u = a w) (hb : S u = true → b u = b w) :
    let K : J → (R → X) → X → X → ℝ := fun j ρ x y =>
      (c * ∑ i, (if L j then v (ρ (a j)) i - v x i else v x i) *
        (if S j then v (ρ (b j)) i - v y i else v y i)) -
        (if L j || S j then 0 else q)
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase u, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ)) =
    ∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase w, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ) := by
  intro K
  simpa only [inner_flagged_toLp_two_eq_sum] using
    integral_fresh_inner_prod_erase_eq μ (v := fun x => WithLp.toLp 2 (v x)) MemLp.of_discrete
      c q a b L S s hu hw hL hS ha hb

/-- **The replica-mean substitution for arbitrary mixed products (Talagrand (1.305))** for
coordinate vectors on a finite space. -/
theorem integral_replica_centered_products {P S G : Type*} [Fintype P] [Fintype S] [Fintype G]
    (μ : Measure X) [IsProbabilityMeasure μ] (v : X → I → ℝ) (b : I → ℝ)
    (hb : ∀ i, ∫ x, v x i ∂μ = b i) (c q : ℝ) (a a' : P → R) (d : S → R) :
    let J := P ⊕ (S ⊕ G)
    (∫ σ : R ⊕ (J ⊕ J) → X,
      (∏ p : P, c * ∑ i, (v (σ (.inl (a p))) i - v (σ (.inr (.inl (.inl p)))) i) *
        (v (σ (.inl (a' p))) i - v (σ (.inr (.inr (.inl p)))) i)) *
      (∏ s : S, c * ∑ i, (v (σ (.inl (d s))) i - v (σ (.inr (.inl (.inr (.inl s))))) i) *
        v (σ (.inr (.inr (.inr (.inl s))))) i) *
      (∏ g : G, ((c * ∑ i, v (σ (.inr (.inl (.inr (.inr g))))) i *
        v (σ (.inr (.inr (.inr (.inr g))))) i) - q))
      ∂(Measure.pi fun _ => μ)) =
    ∫ ρ : R → X,
      (∏ p : P, c * ∑ i, (v (ρ (a p)) i - b i) * (v (ρ (a' p)) i - b i)) *
      (∏ s : S, c * ∑ i, (v (ρ (d s)) i - b i) * b i) *
      (∏ _ : G, ((c * ∑ i, b i * b i) - q))
      ∂(Measure.pi fun _ => μ) := by
  intro J
  have h := integral_replica_centered_products_inner (G := G) μ
    (v := fun x => WithLp.toLp 2 (v x)) MemLp.of_discrete
    (integral_toLp_two_eq_of_finite μ v hb) c q a a' d
  simpa only [← WithLp.toLp_sub, inner_toLp_two_eq_sum, Pi.sub_apply] using h

end Coordinates

end MeasureTheory
