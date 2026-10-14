/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.ProbabilityMeasureLimit
public import LeanMachineLearning.SpinGlasses.OverlapExchangeability
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Asymptotic overlap laws (Panchenko §1.3, the input of the Dovbysh–Sudakov theorem)

By `SpinGlasses.sk_annealed_gram_array` the annealed law `Λ_N` of the overlap array of the Gibbs
measure `G_N` is a probability measure on the compact set `𝒦` of Gram-type arrays
(symmetric, unit diagonal, entries in `[-1, 1]`, positive semidefinite finite principal
submatrices) and is exchangeable.  Since `𝒦` is compact, Prokhorov's theorem gives a
subsequence `N_k` along which `Λ_{N_k}` converges weakly, and the limit `μ` inherits both
properties: it is concentrated on `𝒦` (closed) and exchangeable (the permutations act continuously
on arrays).  This is exactly the hypothesis of the **Dovbysh–Sudakov representation theorem**
(Thm 1.7 of the book): `μ` is the law of the Gram array `(σˡ ⬝ σˡ')_{l ≠ l'}` of an i.i.d.
sample from a random probability measure `G` on the unit ball of a separable Hilbert space; `G` is
the *asymptotic Gibbs measure*.  The representation theorem itself (Aldous–Hoover, §1.4–1.5) is not
formalized here.

## Main declarations

* `SpinGlasses.exists_tendsto_exchangeable_gram_arrays`: any sequence of exchangeable probability
  measures on Gram-type arrays has a weakly convergent subsequence whose limit is again an
  exchangeable probability measure on Gram-type arrays.
* `SpinGlasses.exists_sk_asymptotic_overlap_law`: the same for the annealed overlap laws
  `𝔼 G_N^{⊗∞}` of the SK model.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.3, Eq. (1.75).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Matrix BoundedContinuousFunction

namespace SpinGlasses

/-- **Subsequential limits of exchangeable Gram-type arrays.**  If every `Λ n` is a probability
measure on arrays concentrated on Gram-type arrays and invariant under all permutations of the
indices, then a subsequence converges weakly to a probability measure with the same two
properties. -/
theorem exists_tendsto_exchangeable_gram_arrays (Λ : ℕ → ProbabilityMeasure (ℕ → ℕ → ℝ))
    (hK : ∀ n, (Λ n : Measure (ℕ → ℕ → ℝ))
      {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
        (∀ l l', |A l l'| ≤ 1) ∧ ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} = 1)
    (hexch : ∀ (n : ℕ) (e : ℕ ≃ ℕ),
      (Λ n : Measure (ℕ → ℕ → ℝ)).map (fun A l l' => A (e l) (e l')) = Λ n) :
    ∃ (φ : ℕ → ℕ) (μ : ProbabilityMeasure (ℕ → ℕ → ℝ)), StrictMono φ ∧
      Tendsto (Λ ∘ φ) atTop (𝓝 μ) ∧
      (μ : Measure (ℕ → ℕ → ℝ))
        {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
          (∀ l l', |A l l'| ≤ 1) ∧
          ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} = 1 ∧
      ∀ e : ℕ ≃ ℕ, (μ : Measure (ℕ → ℕ → ℝ)).map (fun A l l' => A (e l) (e l')) = μ := by
  obtain ⟨φ, μ, hφ, hμK, hlim⟩ :=
    ProbabilityMeasure.exists_tendsto_subseq_of_measure_eq_one isCompact_setOf_gram_array Λ hK
  refine ⟨φ, μ, hφ, hlim, hμK, fun e => ?_⟩
  have hT : Continuous fun (A : ℕ → ℕ → ℝ) (l l' : ℕ) => A (e l) (e l') :=
    continuous_pi fun l => continuous_pi fun l' =>
      (continuous_apply (e l')).comp (continuous_apply (e l))
  have h := ProbabilityMeasure.map_eq_of_tendsto (μ := Λ ∘ φ) hT
    (fun n => ProbabilityMeasure.toMeasure_injective (hexch (φ n) e)) hlim
  exact congrArg ProbabilityMeasure.toMeasure h

/-- **The asymptotic overlap law of the SK model** (Panchenko §1.3).  Let `Λ_N` be the annealed law
`𝔼 G_N^{⊗∞}` of the overlap array `(N⁻¹ σˡ ⬝ σˡ')` of i.i.d. replicas from the Gibbs measure `G_N`
of `H_N` (`Measure.count.tilted (β H_N)`), the disorder `G` being a standard Gaussian matrix.  Then
along a subsequence `N_k + 1`, `Λ_{N_k + 1}` converges weakly to a probability measure `μ` on arrays
which is concentrated on Gram-type arrays (symmetric, unit diagonal, entries in `[-1, 1]`, positive
semidefinite) and exchangeable.  By the Dovbysh–Sudakov theorem, `μ` is the law of the Gram array
of an i.i.d. sample from the *asymptotic Gibbs measure*. -/
theorem exists_sk_asymptotic_overlap_law {β : ℝ}
    (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))
    (R : ∀ N : ℕ, (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
    (hR : ∀ N σ τ, R N σ τ = (N : ℝ)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ)))
    (Λ : ℕ → Measure (ℕ → ℕ → ℝ))
    (hΛ : ∀ N, 0 < N → Λ N =
      ((Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1).bind fun G =>
        Measure.infinitePi fun _ : ℕ =>
          (Measure.count : Measure (Fin N → ℤˣ)).tilted fun σ => β * H N G σ).map
        fun σ l l' => R N (σ l) (σ l')) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (ℕ → ℕ → ℝ)), StrictMono φ ∧ IsProbabilityMeasure μ ∧
      (∀ g : (ℕ → ℕ → ℝ) →ᵇ ℝ,
        Tendsto (fun n => ∫ A, g A ∂(Λ (φ n + 1))) atTop (𝓝 (∫ A, g A ∂μ))) ∧
      μ {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
        (∀ l l', |A l l'| ≤ 1) ∧ ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} =
        1 ∧
      ∀ e : ℕ ≃ ℕ, μ.map (fun A l l' => A (e l) (e l')) = μ := by
  have hsk : ∀ N : ℕ, 0 < N →
      IsProbabilityMeasure (Λ N) ∧
        Λ N {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
          (∀ l l', |A l l'| ≤ 1) ∧
          ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} = 1 ∧
        ∀ e : ℕ ≃ ℕ, (Λ N).map (fun A l l' => A (e l) (e l')) = Λ N := fun N hN => by
    refine sk_annealed_gram_array hN (fun G σ => β * H N G σ) (fun σ => ?_) (R N) (hR N)
      (hΛ N hN)
    have hc : Continuous fun G : Fin N → Fin N → ℝ => β * H N G σ := by
      simp only [hH, dotProduct, Matrix.mulVec]
      fun_prop
    exact hc.measurable
  let Λ' : ℕ → ProbabilityMeasure (ℕ → ℕ → ℝ) := fun n =>
    ⟨Λ (n + 1), (hsk (n + 1) n.succ_pos).1⟩
  obtain ⟨φ, μ, hφ, hlim, hμK, hμe⟩ := exists_tendsto_exchangeable_gram_arrays Λ'
    (fun n => (hsk (n + 1) n.succ_pos).2.1) fun n e => (hsk (n + 1) n.succ_pos).2.2 e
  refine ⟨φ, μ, hφ, inferInstance, fun g => ?_, hμK, hμe⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) g

end SpinGlasses
