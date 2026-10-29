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

/-!
# Integrating fresh replica pairs in products

A disjoint sum of index types separates the original replicas from two fresh replicas per
factor. Each fresh replica is integrated exactly once; the factors may share original
replicas. The identities are independent of Gibbs energies and of any spin model.
-/

@[expose] public section

open scoped BigOperators

namespace MeasureTheory

/-- Split a finite replica family into two independent blocks on a sigma-finite space.
The integrability hypothesis is automatic for finite configuration spaces. -/
theorem integral_pi_sum_type {R S X : Type*} [Fintype R] [Fintype S]
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (F : (R → X) → (S → X) → ℝ)
    (hF : Integrable (fun p : (R → X) × (S → X) => F p.1 p.2)
      ((Measure.pi fun _ : R => μ).prod (Measure.pi fun _ : S => μ))) :
    (∫ σ : R ⊕ S → X, F (fun r => σ (.inl r)) (fun s => σ (.inr s))
      ∂(Measure.pi fun _ => μ)) =
    ∫ ρ : R → X, ∫ τ : S → X, F ρ τ ∂(Measure.pi fun _ => μ)
      ∂(Measure.pi fun _ => μ) := by
  have he := measurePreserving_sumPiEquivProdPi (X := fun _ : R ⊕ S => X) (fun _ => μ)
  have hi := he.integral_comp_of_aestronglyMeasurable
    (g := fun p : (R → X) × (S → X) => F p.1 p.2)
    hF.aestronglyMeasurable
  exact hi.trans (integral_prod _ hF)

/-- Integrating a distinct fresh pair for every factor replaces each factor by its
pair average, even when all factors depend on shared original replicas. -/
theorem integral_pi_prod_fresh_pairs {R J X : Type*} [Fintype R] [Fintype J]
    [Finite X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (K : J → (R → X) → X → X → ℝ) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))
      ∂(Measure.pi fun _ => μ)) =
    ∫ ρ : R → X, ∏ j, ∫ x, ∫ y, K j ρ x y ∂μ ∂μ
      ∂(Measure.pi fun _ => μ) := by
  rw [integral_pi_sum_type μ (fun (ρ : R → X) (τ : J ⊕ J → X) =>
    ∏ j, K j ρ (τ (.inl j)) (τ (.inr j))) Integrable.of_finite]
  apply integral_congr_ae (ae_of_all _ fun ρ => ?_)
  rw [integral_pi_sum_type μ (fun (x y : J → X) => ∏ j, K j ρ (x j) (y j))
    Integrable.of_finite]
  simp_rw [integral_fintype_prod_eq_prod]
  exact integral_fintype_prod_eq_prod (μ := fun _ : J => μ)
    (fun j x => ∫ y, K j ρ x y ∂μ)

/-- Integrate any finite subfamily of fresh-pair factors. Unused fresh replicas integrate
to one because the reference measure is a probability measure. -/
theorem integral_pi_finset_prod_fresh_pairs {R J X : Type*} [Fintype R] [Fintype J]
    [Finite X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset J)
    (K : J → (R → X) → X → X → ℝ) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))
      ∂(Measure.pi fun _ => μ)) =
      ∫ ρ : R → X, ∏ j ∈ s, ∫ x, ∫ y, K j ρ x y ∂μ ∂μ
        ∂(Measure.pi fun _ => μ) := by
  classical
  have hprod (f : J → ℝ) : (∏ j, if j ∈ s then f j else 1) = ∏ j ∈ s, f j := by
    simp only [Finset.prod_ite_mem, Finset.univ_inter]
  have hh := integral_pi_prod_fresh_pairs μ
    (fun j ρ x y => if j ∈ s then K j ρ x y else 1)
  have havg (j : J) (ρ : R → X) :
      (∫ x, ∫ y, (if j ∈ s then K j ρ x y else 1) ∂μ ∂μ) =
        if j ∈ s then ∫ x, ∫ y, K j ρ x y ∂μ ∂μ else 1 := by
    by_cases hj : j ∈ s <;> simp [hj]
  simpa only [havg, hprod] using hh

/-- If two fresh-pair factors have the same conditional average, deleting either has
the same expectation. This identifies the surviving moments in Talagrand's Eq. (1.312)
without constructing replica permutations. -/
theorem integral_pi_prod_fresh_pairs_erase_eq {R J X : Type*}
    [Fintype R] [Fintype J] [DecidableEq J]
    [Finite X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset J)
    (K : J → (R → X) → X → X → ℝ) {u v : J} (hu : u ∈ s) (hv : v ∈ s)
    (he : ∀ ρ, (∫ x, ∫ y, K u ρ x y ∂μ ∂μ) = ∫ x, ∫ y, K v ρ x y ∂μ ∂μ) :
    (∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase u, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ)) =
    ∫ σ : R ⊕ (J ⊕ J) → X,
      ∏ j ∈ s.erase v, K j (fun r => σ (.inl r))
        (σ (.inr (.inl j))) (σ (.inr (.inr j))) ∂(Measure.pi fun _ => μ) := by
  classical
  rw [integral_pi_finset_prod_fresh_pairs, integral_pi_finset_prod_fresh_pairs]
  apply integral_congr_ae (ae_of_all _ fun ρ => ?_)
  apply Finset.prod_erase_eq_of_eq _ _ hu hv
  exact he ρ

/-- **Identifying deleted fresh-overlap products in Eq. (1.312).** Matching factor classes
and the original labels they actually use suffice. Unused labels need not match. This
applies to the pair, single and global classes on any finite probability space. -/
theorem integral_fresh_overlap_prod_erase_eq {R J I X : Type*}
    [Fintype R] [Fintype J] [Fintype I] [DecidableEq J]
    [Finite X] [MeasurableSpace X] [MeasurableSingletonClass X]
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
  apply integral_pi_prod_fresh_pairs_erase_eq μ s K hu hw
  intro ρ
  have he (x y : X) : K u ρ x y = K w ρ x y := by
    cases hLu : L u <;> cases hSu : S u <;> simp_all [K]
  simp_rw [he]

/-- **The replica-mean substitution for arbitrary mixed products (Talagrand (1.305)).**
The three finite factor classes correspond to centered pair overlaps, a centered replica
against the mean, and the squared mean minus `q`. Distinct sum-type labels supply a fresh
pair for every factor, including repeated original labels. No model assumptions are needed. -/
theorem integral_replica_centered_products {R P S G I X : Type*}
    [Fintype R] [Fintype P] [Fintype S] [Fintype G] [Fintype I]
    [Finite X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (v : X → I → ℝ) (b : I → ℝ)
    (hb : ∀ i, ∫ x, v x i ∂μ = b i) (c q : ℝ)
    (a a' : P → R) (d : S → R) :
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
  let K : J → (R → X) → X → X → ℝ := fun j ρ x y =>
    Sum.elim
      (fun p => c * ∑ i, (v (ρ (a p)) i - v x i) * (v (ρ (a' p)) i - v y i))
      (Sum.elim
        (fun s => c * ∑ i, (v (ρ (d s)) i - v x i) * v y i)
        (fun _ : G => (c * ∑ i, v x i * v y i) - q)) j
  have hprod (σ : R ⊕ (J ⊕ J) → X) :
      (∏ j, K j (fun r => σ (.inl r)) (σ (.inr (.inl j))) (σ (.inr (.inr j)))) =
      (∏ p : P, c * ∑ i, (v (σ (.inl (a p))) i - v (σ (.inr (.inl (.inl p)))) i) *
        (v (σ (.inl (a' p))) i - v (σ (.inr (.inr (.inl p)))) i)) *
      (∏ s : S, c * ∑ i, (v (σ (.inl (d s))) i - v (σ (.inr (.inl (.inr (.inl s))))) i) *
        v (σ (.inr (.inr (.inr (.inl s))))) i) *
      (∏ g : G, ((c * ∑ i, v (σ (.inr (.inl (.inr (.inr g))))) i *
        v (σ (.inr (.inr (.inr (.inr g))))) i) - q)) := by
    simp only [J, Fintype.prod_sum_type, K, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [← integral_congr_ae (ae_of_all _ hprod), integral_pi_prod_fresh_pairs μ K]
  apply integral_congr_ae (ae_of_all _ fun ρ => ?_)
  have hpair (p : P) : (∫ x, ∫ y, K (.inl p) ρ x y ∂μ ∂μ) =
      c * ∑ i, (v (ρ (a p)) i - b i) * (v (ρ (a' p)) i - b i) := by
    simp only [K, Sum.elim_inl]
    simp only [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite),
      integral_sub (integrable_const _) Integrable.of_finite, integral_const,
      probReal_univ, one_smul, integral_mul_const, hb]
  have hone (s : S) : (∫ x, ∫ y, K (.inr (.inl s)) ρ x y ∂μ ∂μ) =
      c * ∑ i, (v (ρ (d s)) i - b i) * b i := by
    simp only [K, Sum.elim_inr, Sum.elim_inl]
    simp only [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite),
      hb, integral_mul_const, integral_sub (integrable_const _) Integrable.of_finite,
      integral_const,
      probReal_univ, one_smul]
  have hglobal (g : G) : (∫ x, ∫ y, K (.inr (.inr g)) ρ x y ∂μ ∂μ) =
      (c * ∑ i, b i * b i) - q := by
    simp only [K, Sum.elim_inr]
    simp only [integral_sub Integrable.of_finite (integrable_const _),
      integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite),
      hb, integral_mul_const, integral_const, probReal_univ, one_smul]
  simp only [J, Fintype.prod_sum_type, hpair, hone, hglobal]
  ring

end MeasureTheory
