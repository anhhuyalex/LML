/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Function.LpSectionMeasurable
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.ProbabilityMeasureLimit
public import LeanMachineLearning.SpinGlasses.DovbyshSudakov
public import LeanMachineLearning.SpinGlasses.OverlapExchangeability
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
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
the *asymptotic Gibbs measure*.  The representation theorem itself is
`SpinGlasses.exists_dovbysh_sudakov_representation_of_gram_set`; the last section of this file
chains it with the overlap law to produce the asymptotic Gibbs measure as a measurable family of
probability measures on the unit ball of `L²(0, 1)`.

## Main declarations

* `SpinGlasses.exists_tendsto_exchangeable_gram_arrays`: any sequence of exchangeable probability
  measures on Gram-type arrays has a weakly convergent subsequence whose limit is again an
  exchangeable probability measure on Gram-type arrays.
* `SpinGlasses.exists_sk_asymptotic_overlap_law`: the same for the annealed overlap laws
  `𝔼 G_N^{⊗∞}` of the SK model.
* `SpinGlasses.exists_gibbs_measure_of_representation`: a measurable `h : [0, 1]³ → ℝ` with
  `∫ h (w, u, v)² dv ≤ 1` gives a measurable `G : [0, 1] → 𝒫(L²(0, 1))` carried by the unit ball
  whose i.i.d. Gram arrays reproduce the law of `(∫ h (w, u_l, ·) h (w, u_{l'}, ·))`.
* `SpinGlasses.exists_sk_asymptotic_gibbs_measure`: the asymptotic Gibbs measure of the SK model.

## Implementation notes

Mathlib has no `MeasurableSpace` on `Lp`, so the last two theorems take an arbitrary Borel
structure on `L²(0, 1)` as instance arguments.  The measurability of
`(w, u) ↦ [h (w, u, ·)] ∈ L²` is `MeasureTheory.measurable_toLp_section` (Fubini and separability
of `L²`); it does not use the measurable reconstruction of Lemma 1.7, which only makes the random
measure canonical.  The diagonal of the limit array is `1`, not `‖x_l‖²`.

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

section Gibbs

open unitInterval
open scoped ENNReal RealInnerProductSpace

variable [MeasurableSpace (Lp ℝ 2 (volume : Measure I))] [BorelSpace (Lp ℝ 2 (volume : Measure I))]

/-- **From the Dovbysh–Sudakov representation to a random measure on `L²(0, 1)`.**  Let
`h : [0, 1]³ → ℝ` be measurable with `∫ h (w, u, v)² dv ≤ 1` for all `(w, u)`.  Then
`G w = Law_u [h (w, u, ·)]` is a probability measure on the closed unit ball of `L²(0, 1)`, it
depends measurably on `w`, and the law of the array `(⟪h (w, u_l, ·), h (w, u_{l'}, ·)⟫)_{l ≠ l'}`
(with ones on the diagonal), for `w` and `(u_l)` i.i.d. uniform, is the mixture over `w` of the laws
of the Gram arrays of i.i.d. samples from `G w`.  The `MeasurableSpace` on `L²(0, 1)` is an
arbitrary Borel structure (Mathlib has no instance). -/
theorem exists_gibbs_measure_of_representation {h : I × I × I → ℝ} (hm : Measurable h)
    (hint : ∀ q : I × I, Integrable (fun v => h (q.1, q.2, v) ^ 2))
    (hle : ∀ q : I × I, ∫ v, h (q.1, q.2, v) ^ 2 ≤ 1) :
    ∃ G : I → ProbabilityMeasure (Lp ℝ 2 (volume : Measure I)), Measurable G ∧
      (∀ w, (G w : Measure (Lp ℝ 2 (volume : Measure I))) (Metric.closedBall 0 1) = 1) ∧
      ∀ g : (ℕ → ℕ → ℝ) →ᵇ ℝ,
        ∫ A, g A ∂(Measure.map (fun (η : I × (ℕ → I)) (l l' : ℕ) =>
            if l = l' then (1 : ℝ) else ∫ v, h (η.1, η.2 l, v) * h (η.1, η.2 l', v))
          ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))) =
        ∫ w, ∫ x : ℕ → Lp ℝ 2 (volume : Measure I),
          g (fun l l' => if l = l' then 1 else ⟪x l, x l'⟫)
            ∂(Measure.infinitePi fun _ : ℕ =>
              (G w : Measure (Lp ℝ 2 (volume : Measure I)))) ∂(volume : Measure I) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have : TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume : Measure I)) := inferInstance
  have hF : Measurable fun p : (I × I) × I => h (p.1.1, p.1.2, p.2) := hm.comp (by fun_prop)
  have hmem : ∀ q : I × I, MemLp (fun v => h (q.1, q.2, v)) 2 volume := fun q =>
    (memLp_two_iff_integrable_sq (hF.comp measurable_prodMk_left).aestronglyMeasurable).2 (hint q)
  set Φ : I × I → Lp ℝ 2 (volume : Measure I) := fun q =>
    (hmem q).toLp (fun v => h (q.1, q.2, v)) with hΦdef
  have hΦ : Measurable Φ := measurable_toLp_section (by norm_num) ENNReal.ofNat_ne_top hF hmem
  have hΦ' : ∀ w : I, Measurable fun u => Φ (w, u) := fun w => hΦ.comp measurable_prodMk_left
  have hnorm : ∀ q, ‖Φ q‖ ≤ 1 := fun q => by
    refine (sq_le_one_iff₀ (norm_nonneg _)).1 ?_
    rw [hΦdef]
    dsimp only
    rw [norm_sq_toLp_two]
    exact hle q
  have hinner : ∀ q q' : I × I, ⟪Φ q, Φ q'⟫ = ∫ v, h (q.1, q.2, v) * h (q'.1, q'.2, v) :=
    fun q q' => inner_toLp_two _ _
  let G : I → ProbabilityMeasure (Lp ℝ 2 (volume : Measure I)) := fun w =>
    ⟨(volume : Measure I).map fun u => Φ (w, u), inferInstance⟩
  refine ⟨G, (Measure.measurable_map_curry hΦ volume).subtype_mk, fun w => ?_, fun g => ?_⟩
  · change ((volume : Measure I).map fun u => Φ (w, u)) (Metric.closedBall 0 1) = 1
    rw [Measure.map_apply (hΦ' w) Metric.isClosed_closedBall.measurableSet,
      eq_univ_of_forall (s := (fun u => Φ (w, u)) ⁻¹' Metric.closedBall 0 1) fun u => by
        simpa using hnorm (w, u), measure_univ]
  set Ψ : (ℕ → Lp ℝ 2 (volume : Measure I)) → ℕ → ℕ → ℝ := fun x l l' =>
    if l = l' then 1 else ⟪x l, x l'⟫ with hΨdef
  have hΨ : Measurable Ψ := by
    refine measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun l' => ?_
    by_cases hll : l = l'
    · simp only [hΨdef, hll, ↓reduceIte]
      exact measurable_const
    · simp only [hΨdef, hll, ↓reduceIte]
      exact Measurable.inner (measurable_pi_apply l) (measurable_pi_apply l')
  set P : Measure (I × (ℕ → I)) :=
    (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I)) with hP
  have hT : Measurable fun η : I × (ℕ → I) => fun l => Φ (η.1, η.2 l) :=
    measurable_pi_iff.2 fun l =>
      hΦ.comp (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
  have hpt : ∀ η : I × (ℕ → I), (fun l l' : ℕ =>
      if l = l' then (1 : ℝ) else ∫ v, h (η.1, η.2 l, v) * h (η.1, η.2 l', v)) =
        Ψ fun l => Φ (η.1, η.2 l) := fun η => by
    funext l l'
    simp only [hΨdef]
    split_ifs
    · rfl
    · exact (hinner (η.1, η.2 l) (η.1, η.2 l')).symm
  have hΞ : Measurable fun η : I × (ℕ → I) => fun l l' : ℕ =>
      if l = l' then (1 : ℝ) else ∫ v, h (η.1, η.2 l, v) * h (η.1, η.2 l', v) := by
    rw [show (fun η : I × (ℕ → I) => fun l l' : ℕ =>
      if l = l' then (1 : ℝ) else ∫ v, h (η.1, η.2 l, v) * h (η.1, η.2 l', v)) =
        fun η => Ψ fun l => Φ (η.1, η.2 l) from funext hpt]
    exact hΨ.comp hT
  rw [integral_map hΞ.aemeasurable g.continuous.measurable.aestronglyMeasurable]
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun η => congrArg g (hpt η))) ?_
  have hint' : Integrable (fun η : I × (ℕ → I) => g (Ψ fun l => Φ (η.1, η.2 l))) P :=
    (integrable_const ‖g‖).mono' (g.continuous.measurable.comp (hΨ.comp hT)).aestronglyMeasurable
      (ae_of_all _ fun η => g.norm_coe_le_norm _)
  rw [hP, integral_prod _ hint']
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  beta_reduce
  have hK : Measure.infinitePi (fun _ : ℕ => (G w : Measure (Lp ℝ 2 (volume : Measure I)))) =
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map fun u l => Φ (w, u l) :=
    (Measure.infinitePi_map_pi (μ := fun _ : ℕ => (volume : Measure I)) (f := fun _ u => Φ (w, u))
      fun _ => hΦ' w).symm
  rw [hK]
  exact (integral_map (f := fun x => g (Ψ x))
    (measurable_pi_iff.2 fun l => (hΦ' w).comp (measurable_pi_apply l)).aemeasurable
    (g.continuous.measurable.comp hΨ).aestronglyMeasurable).symm

/-- **The asymptotic Gibbs measure of the SK model** (Panchenko §1.5).  Along a subsequence
`N_k + 1`, the annealed overlap laws `Λ_{N_k + 1}` converge weakly to the law of the overlap array
of an i.i.d. sample from a *random* probability measure `G w` on the closed unit ball of
`L²(0, 1)`, `w` uniform: for every bounded continuous test function `g` of the array,
`∫ g dΛ_{N_k + 1} → ∫ 𝔼_{x ~ G w^{⊗ ∞}} g ((⟪x_l, x_{l'}⟫)_{l ≠ l'}) dw`.  The diagonal of the limit
array is `1`, since the overlap of a configuration with itself is `1` (the self-overlap
`⟪x_l, x_l⟫ = ‖x_l‖² ≤ 1` is not the diagonal).  The `MeasurableSpace` on `L²(0, 1)` is an arbitrary
Borel structure (Mathlib has no instance). -/
theorem exists_sk_asymptotic_gibbs_measure {β : ℝ}
    (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hH : ∀ N G ξ, H N G ξ = (Real.sqrt N)⁻¹ *
      ((fun i => ((ξ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((ξ i : ℤ) : ℝ))))
    (R : ∀ N : ℕ, (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
    (hR : ∀ N ξ ζ, R N ξ ζ = (N : ℝ)⁻¹ *
      ((fun i => ((ξ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((ζ i : ℤ) : ℝ)))
    (Λ : ℕ → Measure (ℕ → ℕ → ℝ))
    (hΛ : ∀ N, 0 < N → Λ N =
      ((Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1).bind fun G =>
        Measure.infinitePi fun _ : ℕ =>
          (Measure.count : Measure (Fin N → ℤˣ)).tilted fun ξ => β * H N G ξ).map
        fun ξ l l' => R N (ξ l) (ξ l')) :
    ∃ (φ : ℕ → ℕ) (G : I → ProbabilityMeasure (Lp ℝ 2 (volume : Measure I))),
      StrictMono φ ∧ Measurable G ∧
      (∀ w, (G w : Measure (Lp ℝ 2 (volume : Measure I))) (Metric.closedBall 0 1) = 1) ∧
      ∀ g : (ℕ → ℕ → ℝ) →ᵇ ℝ,
        Tendsto (fun n => ∫ A, g A ∂(Λ (φ n + 1))) atTop
          (𝓝 (∫ w, ∫ x : ℕ → Lp ℝ 2 (volume : Measure I),
              g (fun l l' => if l = l' then 1 else ⟪x l, x l'⟫)
              ∂(Measure.infinitePi fun _ : ℕ =>
                (G w : Measure (Lp ℝ 2 (volume : Measure I)))) ∂(volume : Measure I))) := by
  obtain ⟨φ, μ, hφ, hprob, hlim, hK, hexch⟩ := exists_sk_asymptotic_overlap_law H hH R hR Λ hΛ
  have := hprob
  obtain ⟨h, hm, hint, hle, hμ⟩ := exists_dovbysh_sudakov_representation_of_gram_set hK hexch
  obtain ⟨G, hGm, hG1, hG⟩ := exists_gibbs_measure_of_representation hm hint hle
  refine ⟨φ, G, hφ, hGm, hG1, fun g => ?_⟩
  have hg := hlim g
  rwa [hμ, hG g] at hg

end Gibbs

end SpinGlasses
