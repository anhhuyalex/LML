/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.AldousHooverArray
public import LeanMachineLearning.SpinGlasses.AldousHooverOverlap
public import LeanMachineLearning.SpinGlasses.DovbyshSudakovGaussian
public import LeanMachineLearning.SpinGlasses.DovbyshSudakovLimit
public import LeanMachineLearning.SpinGlasses.OverlapExchangeability

/-!
# The Dovbysh–Sudakov representation (Panchenko §1.5, Theorem 1.7)

Let `R = (R_{l, l'})` be a symmetric random array whose finite principal submatrices are almost
surely positive semidefinite and whose law is invariant under simultaneous permutations of rows
and columns.  Then, as an array indexed by `ℕ × ℕ`,
`R_{l, l'} =_d ⟨h (w, u_l, ·), h (w, u_{l'}, ·)⟩_{L²(0, 1)} + δ_{l, l'} a (w, u_l)`
for measurable `h : [0, 1]³ → ℝ` and `a : [0, 1]² → ℝ ≥ 0`, with `w` and `(u_l)` i.i.d. uniform.
Conditionally on `w` the pairs `(h (w, u_l, ·), a (w, u_l))` are i.i.d., with a law `η (w)` on
`L²(0, 1) × [0, ∞)`: the array is the Gram array of an i.i.d. sample of a random measure plus an
independent nonnegative diagonal.

## Proof (as in the book)

Given `R`, build the Gaussian array `g_{l, i}` with i.i.d. columns of covariance `R`
(`SpinGlasses.DovbyshSudakovGaussian`); it is separately exchangeable, so by Theorem 1.4
`g_{l, i} = τ (w, u_l, v_i, x_{l, i})` in law.  By the strong law of large numbers
`R_{l, l'} = lim n⁻¹ ∑_{i<n} g_{l, i} g_{l', i}`, and the same limit computed on the
Aldous–Hoover side (`SpinGlasses.DovbyshSudakovLimit`) is
`∫ h (w, u_l, v) h (w, u_{l'}, v) dv` for `l ≠ l'` and `∫∫ τ (w, u_l, v, x)² dx dv` for `l = l'`.
The difference of the latter and `∫ h (w, u_l, v)² dv` is `a (w, u_l) ≥ 0` (Jensen).

## Main declarations

* `SpinGlasses.exists_dovbysh_sudakov_representation`: Theorem 1.7.
* `SpinGlasses.exists_dovbysh_sudakov_representation_of_gram`: Theorem 1.7 for a law concentrated
  on positive semidefinite arrays with unit diagonal: then `a = 1 - ∫ h²` and every
  `h (w, u, ·)` lies in the unit ball of `L²(0, 1)`.
* `SpinGlasses.exists_dovbysh_sudakov_representation_of_gram_set`: the same for a law
  concentrated on the Gram set, the form of `SpinGlasses.exists_sk_asymptotic_overlap_law`.

## Implementation notes

* No integrability of `R` is assumed (as in the book).  Square-integrability of the sections
  `τ (w, a, ·, ·)` is *derived*: the empirical second moments of `g` converge, hence so do those
  of `τ`, and given `(w, u_0)` they are an i.i.d. nonnegative sequence, whose averages tend to
  `∞` if the section were not square-integrable
  (`ProbabilityTheory.ae_tendsto_atTop_mean_infinitePi_blocks`).  The function `h` is the partial
  integral of `τ`, modified on the null set where the section is not square-integrable, so that
  `h (w, a, ·) ∈ L²(0, 1)` for *every* `(w, a)`.
* `h (w, a, ·)` is stated as a measurable function with square-integrable sections rather than as
  an `Lp` element; the measurability of `(w, a) ↦ h (w, a, ·) ∈ L²(0, 1)` is not needed for the
  representation (it is needed for Lemma 1.7, the next milestone).
* The Gaussian array is built from the Cholesky factor of `R` (`Matrix.cholInf`), so every entry
  is a finite sum of i.i.d. Gaussians and no Kolmogorov extension is needed.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.5, Theorem 1.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter Set Function
open scoped unitInterval Topology

namespace SpinGlasses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {R : Ω → ℕ → ℕ → ℝ}

/-- **Theorem 1.7 (Dovbysh–Sudakov representation).** -/
theorem exists_dovbysh_sudakov_representation (hR : ∀ l l', Measurable fun ω => R ω l l')
    (hpsd : ∀ᵐ ω ∂P, ∀ k : ℕ, (Matrix.of fun l l' : Fin k => R ω l l').PosSemidef)
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω l l' => R ω (e l) (e l')) R P P) :
    ∃ (h : I × I × I → ℝ) (a : I × I → ℝ), Measurable h ∧ Measurable a ∧ (∀ q : I × I, 0 ≤ a q) ∧
      (∀ q : I × I, Integrable (fun v => h (q.1, q.2, v) ^ 2)) ∧
      IdentDistrib (fun ω (p : ℕ × ℕ) => R ω p.1 p.2)
        (fun (η : I × (ℕ → I)) (p : ℕ × ℕ) =>
          (∫ v, h (η.1, η.2 p.1, v) * h (η.1, η.2 p.2, v)) +
            if p.1 = p.2 then a (η.1, η.2 p.1) else 0) P
        ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) := by
  set ν := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hν
  set γ := Measure.infinitePi fun _ : ℕ => ν with hγ
  have hRm : Measurable R := measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun l' => hR l l'
  obtain ⟨s, hs⟩ : ∃ s : ℕ × ℕ → Ω × (ℕ → ℕ → ℝ) → ℝ, ∀ p z,
      s p z = ∑ k ∈ range (p.1 + 1), cholInf (R z.1) p.1 k * z.2 p.2 k := ⟨_, fun _ _ => rfl⟩
  have hsm : ∀ p, Measurable (s p) := fun p => by
    have : s p = fun z => ∑ k ∈ range (p.1 + 1), cholInf (R z.1) p.1 k * z.2 p.2 k :=
      funext (hs p)
    rw [this]
    exact Finset.measurable_sum _ fun k _ => ((measurable_cholInf p.1 k).comp
      (hRm.comp measurable_fst)).mul ((measurable_pi_apply k).comp
        ((measurable_pi_apply p.2).comp measurable_snd))
  have hexchG := identDistrib_gaussianArray_separately hR hpsd hexch hs
  obtain ⟨τ, hτ, hid⟩ := exists_aldousHoover_representation_separately (P := P.prod γ) hsm
    hexchG
  -- the Aldous–Hoover noise realized on one i.i.d. family
  have hT := measurePreserving_aldousHooverNoise (volume : Measure I)
  set T := fun m : (I × (ℕ → I)) × (ℕ ⊕ ℕ × ℕ → I) =>
    ((m.1.1, (m.1.2, fun i => m.2 (Sum.inl i))), fun p : ℕ × ℕ => m.2 (Sum.inr p)) with hTdef
  set M := ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
    (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => (volume : Measure I)) with hM
  set arr : (I × (ℕ → I)) × (ℕ ⊕ ℕ × ℕ → I) → ℕ × ℕ → ℝ := fun m p =>
    τ (m.1.1, m.1.2 p.1, m.2 (Sum.inl p.2), m.2 (Sum.inr p)) with harr
  have harrm : Measurable arr := measurable_pi_iff.2 fun p => hτ.comp (by fun_prop)
  have hid' : IdentDistrib (fun z (p : ℕ × ℕ) => s p z) arr (P.prod γ) M := by
    refine hid.trans ?_
    have hg𝒩 : Measurable fun (η : (I × ((ℕ → I) × (ℕ → I))) × (ℕ × ℕ → I)) (p : ℕ × ℕ) =>
        τ (η.1.1, η.1.2.1 p.1, η.1.2.2 p.2, η.2 p) := measurable_pi_iff.2 fun p =>
      hτ.comp (by fun_prop)
    exact ((hg𝒩.hasLaw_map _).identDistrib ((hg𝒩.hasLaw_map _).comp hT.hasLaw))
  -- the empirical second moments of `τ` converge: this is true for `g`, hence for `τ`
  have hEg : MeasurableSet {y : ℕ × ℕ → ℝ | ∃ c : ℝ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i ∈ range n, y (0, i) * y (0, i)) atTop (𝓝 c)} :=
    measurableSet_exists_tendsto fun n => measurable_const.mul (Finset.measurable_sum _
      fun i _ => (measurable_pi_apply (0, i)).mul (measurable_pi_apply (0, i)))
  have hfin : ∀ᵐ m ∂M, ∃ c : ℝ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
      τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i))) *
        τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i)))) atTop (𝓝 c) := by
    have h1 : ∀ᵐ z ∂(P.prod γ), ∃ c : ℝ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ range n, s (0, i) z * s (0, i) z) atTop (𝓝 c) :=
      (ae_tendsto_gaussianArray_mean hR hpsd hs 0 0).mono fun z hz => ⟨_, hz⟩
    have h2 := hid'.measure_mem_eq hEg.compl
    exact ae_iff.2 (h2.symm.trans (ae_iff.1 h1))
  have hint4 := ae_integrable_section_of_ae_exists_tendsto (volume : Measure I) hτ hfin
  obtain ⟨h, a, hhm, ham, ha0, hhint, hae⟩ :=
    exists_ae_tendsto_mean_aldousHoover (volume : Measure I) hτ hint4
  refine ⟨h, a, hhm, ham, ha0, hhint, ?_⟩
  -- the limit functional
  set Lim : (ℕ × ℕ → ℝ) → ℕ × ℕ → ℝ := fun y p =>
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, y (p.1, i) * y (p.2, i)) atTop with hLim
  have hLimm : Measurable Lim := measurable_pi_iff.2 fun p => Measurable.limsup fun n =>
    measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply (p.1, i)).mul (measurable_pi_apply (p.2, i)))
  set Fn : (I × (ℕ → I)) → ℕ × ℕ → ℝ := fun η p =>
    (∫ v, h (η.1, η.2 p.1, v) * h (η.1, η.2 p.2, v)) +
      if p.1 = p.2 then a (η.1, η.2 p.1) else 0 with hFn
  have hFnm : Measurable Fn := by
    refine measurable_pi_iff.2 fun p => ?_
    have h1 : Measurable fun x : (I × (ℕ → I)) × I =>
        h (x.1.1, x.1.2 p.1, x.2) * h (x.1.1, x.1.2 p.2, x.2) :=
      (hhm.comp (by fun_prop)).mul (hhm.comp (by fun_prop))
    refine h1.integral_prod_right'.add ?_
    by_cases hp : p.1 = p.2
    · simp only [hp, ite_true]
      exact ham.comp (by fun_prop)
    · simp only [hp, ite_false]
      exact measurable_const
  -- Gaussian side: `R` is the limit of the empirical covariances of `g`
  have hE1 : (fun (z : Ω × (ℕ → ℕ → ℝ)) (p : ℕ × ℕ) => R z.1 p.1 p.2) =ᵐ[P.prod γ]
      fun z => Lim (fun p => s p z) := by
    have : ∀ p : ℕ × ℕ, ∀ᵐ z ∂(P.prod γ), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ range n, s (p.1, i) z * s (p.2, i) z) atTop (𝓝 (R z.1 p.1 p.2)) := fun p =>
      ae_tendsto_gaussianArray_mean hR hpsd hs p.1 p.2
    filter_upwards [ae_all_iff.2 this] with z hz
    funext p
    exact ((hz p).limsup_eq).symm
  have hRFm : Measurable fun (ω : Ω) (p : ℕ × ℕ) => R ω p.1 p.2 :=
    measurable_pi_iff.2 fun p => hR p.1 p.2
  have hRz : IdentDistrib (fun ω (p : ℕ × ℕ) => R ω p.1 p.2)
      (fun (z : Ω × (ℕ → ℕ → ℝ)) (p : ℕ × ℕ) => R z.1 p.1 p.2) P (P.prod γ) :=
    (hRFm.hasLaw_map P).identDistrib ((hRFm.hasLaw_map P).comp
      (measurePreserving_fst (μ := P) (ν := γ)).hasLaw)
  have hE1' : IdentDistrib (fun (z : Ω × (ℕ → ℕ → ℝ)) (p : ℕ × ℕ) => R z.1 p.1 p.2)
      (fun z => Lim (fun p => s p z)) (P.prod γ) (P.prod γ) :=
    IdentDistrib.of_ae_eq (hRFm.comp measurable_fst).aemeasurable hE1
  have hE2 : IdentDistrib (fun z => Lim (fun p => s p z)) (fun m => Lim (arr m)) (P.prod γ) M :=
    hid'.comp hLimm
  -- Aldous–Hoover side: the same limit is `Fn`
  have hE3 : (fun m => Lim (arr m)) =ᵐ[M] fun m p => Fn m.1 p := by
    filter_upwards [hae] with m hm
    funext p
    exact (hm p.1 p.2).limsup_eq
  have hE3' : IdentDistrib (fun m => Lim (arr m)) (fun m p => Fn m.1 p) M M :=
    IdentDistrib.of_ae_eq (hLimm.comp harrm).aemeasurable hE3
  have hE4 : IdentDistrib (fun m p => Fn m.1 p) (fun η p => Fn η p) M
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) :=
    ((hFnm.hasLaw_map _).comp measurePreserving_fst.hasLaw).identDistrib
      (hFnm.hasLaw_map _)
  exact hRz.trans (hE1'.trans (hE2.trans (hE3'.trans hE4)))

/-- **Dovbysh–Sudakov representation of an exchangeable Gram-type law.**  Let `Λ` be a probability
measure on arrays, concentrated on arrays with positive semidefinite finite principal submatrices
and unit diagonal, and invariant under the diagonal action of `ℕ ≃ ℕ`.  Then `Λ` is the law of
the off-diagonal Gram array `(∫ h (w, u_l, v) h (w, u_{l'}, v) dv)_{l ≠ l'}` (with unit diagonal)
of an i.i.d. sample `h (w, u_l, ·)` from a random probability measure `η (w)` on the unit ball of
`L²(0, 1)`: the parameter `w` is the randomness of the asymptotic Gibbs measure.  Every
`h (w, u, ·)` lies in the unit ball, `∫ h (w, u, v)² dv ≤ 1`, because the diagonal residual
`a = 1 - ∫ h²` is nonnegative. -/
theorem exists_dovbysh_sudakov_representation_of_gram {Λ : Measure (ℕ → ℕ → ℝ)}
    [IsProbabilityMeasure Λ]
    (hK : ∀ᵐ A ∂Λ, (∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef) ∧ ∀ l, A l l = 1)
    (hexch : ∀ e : ℕ ≃ ℕ, Λ.map (fun A l l' => A (e l) (e l')) = Λ) :
    ∃ h : I × I × I → ℝ, Measurable h ∧ (∀ q : I × I, Integrable (fun v => h (q.1, q.2, v) ^ 2)) ∧
      (∀ q : I × I, ∫ v, h (q.1, q.2, v) ^ 2 ≤ 1) ∧
      Λ = Measure.map (fun (η : I × (ℕ → I)) (l l' : ℕ) =>
          if l = l' then (1 : ℝ) else ∫ v, h (η.1, η.2 l, v) * h (η.1, η.2 l', v))
        ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) := by
  have hR : ∀ l l', Measurable fun A : ℕ → ℕ → ℝ => A l l' := fun l l' =>
    (measurable_pi_apply l').comp (measurable_pi_apply l)
  have hm : ∀ e : ℕ ≃ ℕ, Measurable fun (A : ℕ → ℕ → ℝ) l l' => A (e l) (e l') := fun e =>
    measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun l' =>
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  obtain ⟨h, a, hhm, ham, ha0, hhint, hid⟩ := exists_dovbysh_sudakov_representation
    (P := Λ) (R := fun A => A) hR (hK.mono fun A hA => hA.1)
    (fun e => ⟨(hm e).aemeasurable, aemeasurable_id, (hexch e).trans Measure.map_id.symm⟩)
  set A0 := (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))
    with hA0
  set Fn : (I × (ℕ → I)) → ℕ × ℕ → ℝ := fun η p =>
    (∫ v, h (η.1, η.2 p.1, v) * h (η.1, η.2 p.2, v)) +
      if p.1 = p.2 then a (η.1, η.2 p.1) else 0 with hFn
  -- the diagonal is `1`
  have hD : MeasurableSet {x : ℕ × ℕ → ℝ | ∀ l, x (l, l) = 1} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun l => measurableSet_eq_fun (measurable_pi_apply _)
      measurable_const
  have hdiag : ∀ᵐ η ∂A0, ∀ l, Fn η (l, l) = 1 := by
    have := hid.ae_snd hD (by filter_upwards [hK] with A hA l using hA.2 l)
    filter_upwards [this] with η hη l using hη l
  -- hence `h (w, u_l, ·)` is in the unit ball
  set Gd : Set (I × I) := {q | ∫ v, h (q.1, q.2, v) ^ 2 ≤ 1} with hGd
  have hhsq : Measurable fun p : (I × I) × I => h (p.1.1, p.1.2, p.2) ^ 2 :=
    (hhm.comp (by fun_prop)).pow_const 2
  have hGdm : MeasurableSet Gd :=
    measurableSet_le hhsq.integral_prod_right' measurable_const
  have hgood : ∀ᵐ η ∂A0, ∀ l, (η.1, η.2 l) ∈ Gd := by
    filter_upwards [hdiag] with η hη l
    have h1 := hη l
    have h2 := ha0 (η.1, η.2 l)
    simp only [hFn, ite_true] at h1
    have : (fun v => h (η.1, η.2 l, v) * h (η.1, η.2 l, v)) =
        fun v => h (η.1, η.2 l, v) ^ 2 := funext fun v => (sq _).symm
    rw [this] at h1
    exact le_of_sub_nonneg (by linarith : 0 ≤ 1 - ∫ v, h (η.1, η.2 l, v) ^ 2)
  set h' : I × I × I → ℝ := fun q => if (q.1, q.2.1) ∈ Gd then h q else 0 with hh'
  have hh'm : Measurable h' :=
    Measurable.ite (hGdm.preimage (by fun_prop)) hhm measurable_const
  have hh'eq : ∀ q : I × I, q ∈ Gd → ∀ v, h' (q.1, q.2, v) = h (q.1, q.2, v) := fun q hq v => by
    simp [hh', hq]
  refine ⟨h', hh'm, fun q => ?_, fun q => ?_, ?_⟩
  · by_cases hq : q ∈ Gd
    · simpa only [hh'eq q hq] using hhint q
    · simp [hh', hq]
  · by_cases hq : q ∈ Gd
    · have : (fun v => h' (q.1, q.2, v) ^ 2) = fun v => h (q.1, q.2, v) ^ 2 :=
        funext fun v => by rw [hh'eq q hq]
      rw [this]
      exact hq
    · simp [hh', hq]
  · have hc : Measurable fun (x : ℕ × ℕ → ℝ) (l l' : ℕ) => x (l, l') :=
      measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun l' => measurable_pi_apply _
    calc Λ = (Λ.map fun A p => A p.1 p.2).map fun x l l' => x (l, l') :=
          (map_map_curry_array Λ).symm
      _ = _ := by
          rw [hid.map_eq, AEMeasurable.map_map_of_aemeasurable hc.aemeasurable
            hid.aemeasurable_snd]
          refine Measure.map_congr ?_
          filter_upwards [hdiag, hgood] with η hd hg
          funext l l'
          by_cases hll' : l = l'
          · subst hll'
            simpa using hd l
          · simp only [Function.comp_apply, hFn, hll', ite_false, add_zero]
            have e1 : (fun v => h' (η.1, η.2 l, v) * h' (η.1, η.2 l', v)) =
                fun v => h (η.1, η.2 l, v) * h (η.1, η.2 l', v) :=
              funext fun v => by rw [hh'eq _ (hg l), hh'eq _ (hg l')]
            rw [e1]

/-- **Dovbysh–Sudakov representation of an exchangeable law on the Gram set.**  This is the form
of the limits of `SpinGlasses.exists_tendsto_exchangeable_gram_arrays` and of the asymptotic
overlap law `SpinGlasses.exists_sk_asymptotic_overlap_law`: a probability measure `μ` concentrated
on the (closed) set of Gram-type arrays and invariant under the diagonal action of `ℕ ≃ ℕ` is the
law of the Gram array of an i.i.d. sample from a random probability measure on the unit ball of
`L²(0, 1)`. -/
theorem exists_dovbysh_sudakov_representation_of_gram_set {μ : Measure (ℕ → ℕ → ℝ)}
    [IsProbabilityMeasure μ]
    (hK : μ {A : ℕ → ℕ → ℝ | (∀ l l', A l l' = A l' l) ∧ (∀ l, A l l = 1) ∧
      (∀ l l', |A l l'| ≤ 1) ∧ ∀ k : ℕ, (Matrix.of fun l l' : Fin k => A l l').PosSemidef} = 1)
    (hexch : ∀ e : ℕ ≃ ℕ, μ.map (fun A l l' => A (e l) (e l')) = μ) :
    ∃ h : I × I × I → ℝ, Measurable h ∧ (∀ q : I × I, Integrable (fun v => h (q.1, q.2, v) ^ 2)) ∧
      (∀ q : I × I, ∫ v, h (q.1, q.2, v) ^ 2 ≤ 1) ∧
      μ = Measure.map (fun (η : I × (ℕ → I)) (l l' : ℕ) =>
          if l = l' then (1 : ℝ) else ∫ v, h (η.1, η.2 l, v) * h (η.1, η.2 l', v))
        ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) :=
  exists_dovbysh_sudakov_representation_of_gram
    (Filter.Eventually.mono ((mem_ae_iff_prob_eq_one
      isCompact_setOf_gram_array.isClosed.measurableSet).2 hK) fun _ h => ⟨h.2.2.2, h.2.1⟩) hexch

end SpinGlasses
