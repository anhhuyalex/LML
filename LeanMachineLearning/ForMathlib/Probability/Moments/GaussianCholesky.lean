/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.CholeskyInfinite
public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Gaussian sequences with a prescribed (infinite) covariance

Let `A : ℕ → ℕ → ℝ` have positive semidefinite finite principal submatrices and let `c` be an
i.i.d. sequence of standard Gaussians.  Then
`l ↦ ∑_{k ≤ l} (cholInf A) l k * c k` is a centered Gaussian sequence with covariance `A`: each
coordinate is a *finite* sum, so no Kolmogorov extension theorem is needed, and the construction
is measurable in `A` (`Matrix.measurable_cholInf`).

## Main declarations

* `ProbabilityTheory.map_dotProduct_eq_of_gram_eq`: linear forms of an i.i.d. Gaussian vector
  with the same Gram matrix have the same law.
* `ProbabilityTheory.map_cholInf_comp_equiv`: the law of the Gaussian sequence with covariance
  `A` composed with a permutation `e` of the coordinates is the law of the sequence with
  covariance `(A (e l) (e l'))`: the law depends on `A` only, not on the chosen factorization.
-/

@[expose] public section

open MeasureTheory Matrix Finset
open scoped Matrix

namespace ProbabilityTheory

section Finite

variable {I K : Type*} [Finite I] [Fintype K]

/-- **Linear forms of i.i.d. Gaussians with the same Gram matrix have the same law.** -/
theorem map_dotProduct_eq_of_gram_eq (a b : I → K → ℝ) (h : ∀ p q, a p ⬝ᵥ a q = b p ⬝ᵥ b q) :
    (Measure.pi fun _ : K => gaussianReal 0 1).map (fun ζ p => a p ⬝ᵥ ζ) =
      (Measure.pi fun _ : K => gaussianReal 0 1).map (fun ζ p => b p ⬝ᵥ ζ) :=
  (map_eq_map_dotProduct_family (X := fun p ζ => b p ⬝ᵥ ζ) a (hasGaussianLaw_dotProduct_family b)
    (fun p => integral_dotProduct_pi_gaussianReal (b p))
    fun p q => (integral_dotProduct_mul_dotProduct_pi_gaussianReal (b p) (b q)).trans
      (h p q).symm).symm

end Finite

/-- **The Gaussian sequence with covariance `A` composed with a permutation `e`** has the law
of the Gaussian sequence with covariance `(A (e l) (e l'))`, although the Cholesky factors of the
two covariances differ. -/
theorem map_cholInf_comp_equiv {A : ℕ → ℕ → ℝ}
    (hA : ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef) (e : ℕ ≃ ℕ) :
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map
        (fun c (l : ℕ) => ∑ k ∈ range (e l + 1), cholInf A (e l) k * c k) =
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map
        (fun c (l : ℕ) => ∑ k ∈ range (l + 1), cholInf (fun a b => A (e a) (e b)) l k * c k) := by
  classical
  set ν := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hν
  have hA' := posSemidef_comp hA e
  refine IsProjectiveLimit.unique (P := fun I => (ν.map fun c (l : ℕ) =>
    ∑ k ∈ range (e l + 1), cholInf A (e l) k * c k).map I.restrict) (fun I => rfl)
    fun I => ?_
  set N := (I.sup fun l => max l (e l)) + 1 with hN
  have hlt : ∀ l ∈ I, l < N ∧ e l < N := fun l hl => by
    have := Finset.le_sup (f := fun l => max l (e l)) hl
    simp only [hN]
    exact ⟨by have := le_max_left l (e l); omega, by have := le_max_right l (e l); omega⟩
  have hr : MeasurePreserving (fun (c : ℕ → ℝ) (j : Fin N) => c j) ν
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
    Measure.measurePreserving_restrict_infinitePi (gaussianReal 0 1) (f := Fin.val)
      Fin.val_injective
  have hfac : ∀ (B : ℕ → ℕ → ℝ) (σ : ℕ → ℕ), (∀ l ∈ I, σ l < N) →
      (I.restrict ∘ fun c (l : ℕ) => ∑ k ∈ range (σ l + 1), cholInf B (σ l) k * c k) =
        (fun ζ (l : I) => (fun j : Fin N => cholInf B (σ l) j) ⬝ᵥ ζ) ∘
          fun (c : ℕ → ℝ) (j : Fin N) => c j := by
    intro B σ hσ
    funext c l
    simp only [Function.comp_apply, Finset.restrict, dotProduct]
    rw [Fin.sum_univ_eq_sum_range (fun j => cholInf B (σ l) j * c j) N]
    refine sum_subset (range_mono (by have := hσ l l.2; omega)) fun k _ hk => ?_
    rw [cholInf_of_gt B (by simpa using hk), zero_mul]
  have hF1 : Measurable fun (c : ℕ → ℝ) (l : ℕ) =>
      ∑ k ∈ range (e l + 1), cholInf A (e l) k * c k :=
    measurable_pi_iff.2 fun l => Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (measurable_pi_apply k)
  have hF2 : Measurable fun (c : ℕ → ℝ) (l : ℕ) =>
      ∑ k ∈ range (l + 1), cholInf (fun a b => A (e a) (e b)) l k * c k :=
    measurable_pi_iff.2 fun l => Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (measurable_pi_apply k)
  have hrI : Measurable (I.restrict : (ℕ → ℝ) → (I → ℝ)) := by fun_prop
  have hG : ∀ a : I → Fin N → ℝ, Measurable fun (ζ : Fin N → ℝ) (l : I) => a l ⬝ᵥ ζ := fun a =>
    measurable_pi_iff.2 fun l => by simp only [dotProduct]; fun_prop
  have h2 : (I.restrict ∘ fun (c : ℕ → ℝ) (l : ℕ) =>
        ∑ k ∈ range (l + 1), cholInf (fun a b => A (e a) (e b)) l k * c k) =
      (fun ζ (l : I) => (fun j : Fin N => cholInf (fun a b => A (e a) (e b)) l j) ⬝ᵥ ζ) ∘
        fun (c : ℕ → ℝ) (j : Fin N) => c j :=
    hfac (fun a b => A (e a) (e b)) id (fun l hl => (hlt l hl).1)
  beta_reduce
  rw [Measure.map_map hrI hF2, Measure.map_map hrI hF1, h2,
    hfac A e (fun l hl => (hlt l hl).2),
    ← Measure.map_map (hG _) hr.measurable, ← Measure.map_map (hG _) hr.measurable, hr.map_eq]
  refine (map_dotProduct_eq_of_gram_eq _ _ fun p q => ?_).symm
  have h1 := sum_cholInf_mul_eq hA (e p) (e q) N (max_lt (hlt p p.2).2 (hlt q q.2).2)
  have h2 := sum_cholInf_mul_eq (A := fun a b => A (e a) (e b)) hA' p q N
    (max_lt (hlt p p.2).1 (hlt q q.2).1)
  simp only [dotProduct]
  rw [Fin.sum_univ_eq_sum_range (fun j => cholInf A (e p) j * cholInf A (e q) j) N,
    Fin.sum_univ_eq_sum_range (fun j => cholInf (fun a b => A (e a) (e b)) p j *
      cholInf (fun a b => A (e a) (e b)) q j) N, h1, h2]

/-- **Second moments of the Gaussian sequence with covariance `A`:** the products of two
coordinates are integrable, with mean `A l l'`. -/
theorem integrable_integral_cholInf_mul {A : ℕ → ℕ → ℝ}
    (hA : ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef) (l l' : ℕ) :
    Integrable (fun c : ℕ → ℝ => (∑ k ∈ range (l + 1), cholInf A l k * c k) *
        ∑ k ∈ range (l' + 1), cholInf A l' k * c k)
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) ∧
    ∫ c : ℕ → ℝ, (∑ k ∈ range (l + 1), cholInf A l k * c k) *
        ∑ k ∈ range (l' + 1), cholInf A l' k * c k
      ∂(Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) = A l l' := by
  set ν := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hν
  set N := max l l' + 1 with hN
  have hr : MeasurePreserving (fun (c : ℕ → ℝ) (j : Fin N) => c j) ν
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
    Measure.measurePreserving_restrict_infinitePi (gaussianReal 0 1) (f := Fin.val)
      Fin.val_injective
  have hfac : ∀ m, m < N → ∀ c : ℕ → ℝ, ∑ k ∈ range (m + 1), cholInf A m k * c k =
      (fun j : Fin N => cholInf A m j) ⬝ᵥ (fun j : Fin N => c j) := fun m hm c => by
    simp only [dotProduct]
    rw [Fin.sum_univ_eq_sum_range (fun j => cholInf A m j * c j) N]
    refine sum_subset (range_mono (by omega)) fun k _ hk => ?_
    rw [cholInf_of_gt A (by simpa using hk), zero_mul]
  have hl : l < N := by omega
  have hl' : l' < N := by omega
  have hrewrite : (fun c : ℕ → ℝ => (∑ k ∈ range (l + 1), cholInf A l k * c k) *
      ∑ k ∈ range (l' + 1), cholInf A l' k * c k) =
      (fun ζ : Fin N → ℝ => ((fun j : Fin N => cholInf A l j) ⬝ᵥ ζ) *
        ((fun j : Fin N => cholInf A l' j) ⬝ᵥ ζ)) ∘ fun (c : ℕ → ℝ) (j : Fin N) => c j := by
    funext c
    simp only [Function.comp_apply, hfac l hl c, hfac l' hl' c]
  have hF : Measurable fun ζ : Fin N → ℝ => ((fun j : Fin N => cholInf A l j) ⬝ᵥ ζ) *
      ((fun j : Fin N => cholInf A l' j) ⬝ᵥ ζ) := by
    simp only [dotProduct]; fun_prop
  rw [hrewrite]
  refine ⟨hr.hasLaw.integrable_comp ?_, ?_⟩
  · exact (memLp_dotProduct_pi_gaussianReal _).integrable_mul (memLp_dotProduct_pi_gaussianReal _)
  · rw [hr.hasLaw.integral_comp hF.aestronglyMeasurable,
      integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    simp only [dotProduct]
    rw [Fin.sum_univ_eq_sum_range (fun j => cholInf A l j * cholInf A l' j) N]
    exact sum_cholInf_mul_eq hA l l' N (by omega)

end ProbabilityTheory
