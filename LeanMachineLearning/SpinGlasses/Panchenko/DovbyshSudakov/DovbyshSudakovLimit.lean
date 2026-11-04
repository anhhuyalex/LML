/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ParametrizedL2
public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import LeanMachineLearning.ForMathlib.Probability.StrongLawMixture

/-!
# Empirical covariances of an Aldous–Hoover array

Let `s_{l, i} = τ (w, u_l, v_i, x_{l, i})` be a separately exchangeable array in its
Aldous–Hoover representation (Theorem 1.4).  The noise `(w, (u_l), (v_i), (x_{l, i}))` is realized
on `((w, u), σ)` with `(w, u) ~ λ ⊗ λ^{⊗ℕ}` and `σ` an i.i.d. uniform family indexed by
`ℕ ⊕ ℕ × ℕ`, where `v_i = σ (inl i)` and `x_{l, i} = σ (inr (l, i))`
(`SpinGlasses.measurePreserving_aldousHooverNoise`): all the randomness other than `(w, u)` is one
i.i.d. family, so the strong law applies along disjoint blocks.

Given `(w, u)`, the products `s_{l, i} s_{l', i}` over `i` are i.i.d., and the strong law of
large numbers identifies the limit of their averages with the conditional mean.  Writing
`h (w, a, v) = ∫ τ (w, a, v, x) dx`:

* for `l ≠ l'` the limit is `∫ h (w, u_l, v) h (w, u_{l'}, v) dv`
  (`SpinGlasses.ae_tendsto_mean_aldousHoover_offDiag`);
* for `l = l'` the limit is `∫∫ τ (w, u_l, v, x)² dx dv`
  (`SpinGlasses.ae_tendsto_mean_aldousHoover_diag`).

This is the identification of the empirical covariance in the proof of the Dovbysh–Sudakov
theorem (Panchenko §1.5, Eq. (1.99)): the cell noise `x_{l, i}` of the two rows is independent
for `l ≠ l'` and is integrated out separately, which is why only the inner products of
`h (w, u_l, ·)` survive off the diagonal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function Finset Filter
open scoped Topology unitInterval

namespace SpinGlasses

/-- The Aldous–Hoover noise as one i.i.d. family: the map
`((w, u), σ) ↦ ((w, (u, v)), x)` with `v i = σ (inl i)` and `x p = σ (inr p)` sends
`ν ⊗ ν^{⊗ℕ} ⊗ ν^{⊗(ℕ ⊕ ℕ × ℕ)}` to the noise measure of
`SpinGlasses.exists_aldousHoover_representation_separately` (for `ν` the uniform measure). -/
theorem measurePreserving_aldousHooverNoise {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] :
    MeasurePreserving
      (fun m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X) =>
        ((m.1.1, (m.1.2, fun i => m.2 (Sum.inl i))), fun p : ℕ × ℕ => m.2 (Sum.inr p)))
      ((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
        (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν))
      ((ν.prod ((Measure.infinitePi fun _ : ℕ => ν).prod
        (Measure.infinitePi fun _ : ℕ => ν))).prod (Measure.infinitePi fun _ : ℕ × ℕ => ν)) := by
  have hsplit : MeasurePreserving
      (fun z : ℕ ⊕ ℕ × ℕ → X => (fun i => z (Sum.inl i), fun p : ℕ × ℕ => z (Sum.inr p)))
      (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)
      ((Measure.infinitePi fun _ : ℕ => ν).prod (Measure.infinitePi fun _ : ℕ × ℕ => ν)) :=
    ⟨by fun_prop, Measure.map_infinitePi_pair_of_disjoint ν
      Sum.inl_injective Sum.inr_injective (by
        rw [Set.disjoint_left]; rintro _ ⟨a, rfl⟩ ⟨b, hb⟩; exact Sum.inr_ne_inl hb)⟩
  exact (measurePreserving_prod_regroup _ _ _ _).comp ((MeasurePreserving.id _).prod hsplit)


section Limit

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
  {τ : X × X × X × X → ℝ}

/-- The two cell indices `(inl i, inr (l, i))` of the Aldous–Hoover noise family are distinct,
and the pairs for distinct `i` are disjoint. -/
private theorem aldousHooverBlock_two (l : ℕ) :
    (∀ i : ℕ, Function.Injective (![Sum.inl i, Sum.inr (l, i)] : Fin 2 → ℕ ⊕ ℕ × ℕ)) ∧
      ∀ i j : ℕ, i ≠ j → Disjoint
        (Set.range (![Sum.inl i, Sum.inr (l, i)] : Fin 2 → ℕ ⊕ ℕ × ℕ))
        (Set.range (![Sum.inl j, Sum.inr (l, j)] : Fin 2 → ℕ ⊕ ℕ × ℕ)) :=
  ⟨fun i x y hxy => by fin_cases x <;> fin_cases y <;> simp_all, fun i j hij => by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    fin_cases x <;> fin_cases y <;> simp_all⟩

/-- The three cell indices `(inl i, inr (l, i), inr (l', i))` for `l ≠ l'` are distinct, and the
triples for distinct `i` are disjoint. -/
private theorem aldousHooverBlock_three {l l' : ℕ} (hll' : l ≠ l') :
    (∀ i : ℕ, Function.Injective
      (![Sum.inl i, Sum.inr (l, i), Sum.inr (l', i)] : Fin 3 → ℕ ⊕ ℕ × ℕ)) ∧
      ∀ i j : ℕ, i ≠ j → Disjoint
        (Set.range (![Sum.inl i, Sum.inr (l, i), Sum.inr (l', i)] : Fin 3 → ℕ ⊕ ℕ × ℕ))
        (Set.range (![Sum.inl j, Sum.inr (l, j), Sum.inr (l', j)] : Fin 3 → ℕ ⊕ ℕ × ℕ)) :=
  ⟨fun i x y hxy => by fin_cases x <;> fin_cases y <;> simp_all, fun i j hij => by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    fin_cases x <;> fin_cases y <;> simp_all⟩

/-- **Off-diagonal empirical covariance of an Aldous–Hoover array.**  For `l ≠ l'`, almost surely
`n⁻¹ ∑_{i<n} τ (w, u_l, v_i, x_{l, i}) τ (w, u_{l'}, v_i, x_{l', i})` converges to
`∫ h (w, u_l, v) h (w, u_{l'}, v) dv`, where `h (w, a, v) = ∫ τ (w, a, v, x) dx`.  The sections
`τ (w, a, ·, ·)` are assumed square-integrable for almost every `(w, a)`. -/
theorem ae_tendsto_mean_aldousHoover_offDiag (hτ : Measurable τ)
    (hint : ∀ᵐ q ∂(ν.prod ν),
      Integrable (fun p : X × X => τ (q.1, q.2, p.1, p.2) ^ 2) (ν.prod ν)) {l l' : ℕ}
    (hll' : l ≠ l') :
    ∀ᵐ m ∂((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
        (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
          τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
            τ (m.1.1, m.1.2 l', m.2 (Sum.inl i), m.2 (Sum.inr (l', i)))) atTop
        (𝓝 (∫ v, (∫ x, τ (m.1.1, m.1.2 l, v, x) ∂ν) * ∫ x, τ (m.1.1, m.1.2 l', v, x) ∂ν ∂ν)) := by
  have hH : Measurable fun q : X × X × X => ∫ x, τ (q.1, q.2.1, q.2.2, x) ∂ν := by
    have : Measurable fun p : (X × X × X) × X => τ (p.1.1, p.1.2.1, p.1.2.2, p.2) :=
      hτ.comp (by fun_prop)
    exact this.integral_prod_right'
  have hg : Measurable fun m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X) =>
      ∫ v, (∫ x, τ (m.1.1, m.1.2 l, v, x) ∂ν) * ∫ x, τ (m.1.1, m.1.2 l', v, x) ∂ν ∂ν := by
    have hh : Measurable fun p : ((X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X)) × X =>
        (∫ x, τ (p.1.1.1, p.1.1.2 l, p.2, x) ∂ν) * ∫ x, τ (p.1.1.1, p.1.1.2 l', p.2, x) ∂ν :=
      (hH.comp (show Measurable fun p : ((X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X)) × X =>
        (p.1.1.1, p.1.1.2 l, p.2) by fun_prop)).mul
      (hH.comp (show Measurable fun p : ((X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X)) × X =>
        (p.1.1.1, p.1.1.2 l', p.2) by fun_prop))
    exact hh.integral_prod_right'
  have hterm : ∀ i : ℕ, Measurable fun m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X) =>
      τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
        τ (m.1.1, m.1.2 l', m.2 (Sum.inl i), m.2 (Sum.inr (l', i))) := fun i =>
    (hτ.comp (by fun_prop)).mul (hτ.comp (by fun_prop))
  have hset := measurableSet_tendsto_fun (l := atTop)
    (f := fun (n : ℕ) (m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X)) => (n : ℝ)⁻¹ * ∑ i ∈ range n,
      τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
        τ (m.1.1, m.1.2 l', m.2 (Sum.inl i), m.2 (Sum.inr (l', i))))
    (fun n => measurable_const.mul (Finset.measurable_sum _ fun i _ => hterm i)) hg
  rw [Measure.ae_prod_iff_ae_ae hset]
  have hq : ∀ k : ℕ, ∀ᵐ a ∂(ν.prod (Measure.infinitePi fun _ : ℕ => ν)),
      Integrable (fun p : X × X => τ (a.1, a.2 k, p.1, p.2) ^ 2) (ν.prod ν) := fun k => by
    have hmp : MeasurePreserving (fun a : X × (ℕ → X) => (a.1, a.2 k))
        (ν.prod (Measure.infinitePi fun _ : ℕ => ν)) (ν.prod ν) :=
      (MeasurePreserving.id ν).prod (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) k)
    exact hmp.quasiMeasurePreserving.ae hint
  filter_upwards [hq l, hq l'] with a hl hl'
  have hf1 : Measurable fun z : X × X => τ (a.1, a.2 l, z.1, z.2) := hτ.comp (by fun_prop)
  have hf2 : Measurable fun z : X × X => τ (a.1, a.2 l', z.1, z.2) := hτ.comp (by fun_prop)
  obtain ⟨hGi, hGint⟩ := integral_prod_mul_prod (μV := ν) (μX := ν) hf1 hl hf2 hl'
  set G : X × X × X → ℝ := fun p => τ (a.1, a.2 l, p.1, p.2.1) * τ (a.1, a.2 l', p.1, p.2.2)
    with hG
  have hGm : Measurable G := (hτ.comp (by fun_prop)).mul (hτ.comp (by fun_prop))
  have hmp3 := measurePreserving_finThreeArrow ν
  obtain ⟨hf, hdisj⟩ := aldousHooverBlock_three hll'
  have hΦint : Integrable (fun y : Fin 3 → X => G (y 0, y 1, y 2)) (Measure.pi fun _ => ν) :=
    hmp3.hasLaw.integrable_comp (f := G) hGi
  have hblock := ae_tendsto_mean_infinitePi_blocks ν (J := ℕ ⊕ ℕ × ℕ) (F := Fin 3)
    (f := fun i => ![Sum.inl i, Sum.inr (l, i), Sum.inr (l', i)]) hf hdisj
    (Φ := fun y => G (y 0, y 1, y 2)) (hGm.comp (by fun_prop)) hΦint
  have hlim : ∫ y : Fin 3 → X, G (y 0, y 1, y 2) ∂(Measure.pi fun _ : Fin 3 => ν) =
      ∫ v, (∫ x, τ (a.1, a.2 l, v, x) ∂ν) * ∫ x, τ (a.1, a.2 l', v, x) ∂ν ∂ν := by
    rw [← hGint]
    exact hmp3.hasLaw.integral_comp (f := G) hGm.aestronglyMeasurable
  rw [hlim] at hblock
  filter_upwards [hblock] with z hz
  simpa [hG] using hz

/-- **Diagonal empirical covariance of an Aldous–Hoover array.**  Almost surely
`n⁻¹ ∑_{i<n} τ (w, u_l, v_i, x_{l, i})²` converges to `∫∫ τ (w, u_l, v, x)² dx dv`. -/
theorem ae_tendsto_mean_aldousHoover_diag (hτ : Measurable τ)
    (hint : ∀ᵐ q ∂(ν.prod ν),
      Integrable (fun p : X × X => τ (q.1, q.2, p.1, p.2) ^ 2) (ν.prod ν)) (l : ℕ) :
    ∀ᵐ m ∂((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
        (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
          τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
            τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i)))) atTop
        (𝓝 (∫ z : X × X, τ (m.1.1, m.1.2 l, z.1, z.2) ^ 2 ∂(ν.prod ν))) := by
  have hg : Measurable fun m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X) =>
      ∫ z : X × X, τ (m.1.1, m.1.2 l, z.1, z.2) ^ 2 ∂(ν.prod ν) := by
    have hh : Measurable fun p : ((X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X)) × (X × X) =>
        τ (p.1.1.1, p.1.1.2 l, p.2.1, p.2.2) ^ 2 := (hτ.comp (by fun_prop)).pow_const 2
    exact hh.integral_prod_right'
  have hterm : ∀ i : ℕ, Measurable fun m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X) =>
      τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
        τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) := fun i =>
    (hτ.comp (by fun_prop)).mul (hτ.comp (by fun_prop))
  have hset := measurableSet_tendsto_fun (l := atTop)
    (f := fun (n : ℕ) (m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X)) => (n : ℝ)⁻¹ * ∑ i ∈ range n,
      τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
        τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))))
    (fun n => measurable_const.mul (Finset.measurable_sum _ fun i _ => hterm i)) hg
  rw [Measure.ae_prod_iff_ae_ae hset]
  have hq : ∀ᵐ a ∂(ν.prod (Measure.infinitePi fun _ : ℕ => ν)),
      Integrable (fun p : X × X => τ (a.1, a.2 l, p.1, p.2) ^ 2) (ν.prod ν) := by
    have hmp : MeasurePreserving (fun a : X × (ℕ → X) => (a.1, a.2 l))
        (ν.prod (Measure.infinitePi fun _ : ℕ => ν)) (ν.prod ν) :=
      (MeasurePreserving.id ν).prod (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) l)
    exact hmp.quasiMeasurePreserving.ae hint
  filter_upwards [hq] with a ha
  set G : X × X → ℝ := fun p => τ (a.1, a.2 l, p.1, p.2) ^ 2 with hG
  have hGm : Measurable G := (hτ.comp (by fun_prop)).pow_const 2
  have hmp2 := measurePreserving_finTwoArrow ν
  obtain ⟨hf, hdisj⟩ := aldousHooverBlock_two l
  have hΦint : Integrable (fun y : Fin 2 → X => G (y 0, y 1)) (Measure.pi fun _ => ν) :=
    hmp2.hasLaw.integrable_comp (f := G) ha
  have hblock := ae_tendsto_mean_infinitePi_blocks ν (J := ℕ ⊕ ℕ × ℕ) (F := Fin 2)
    (f := fun i => ![Sum.inl i, Sum.inr (l, i)]) hf hdisj
    (Φ := fun y => G (y 0, y 1)) (hGm.comp (by fun_prop)) hΦint
  have hlim : ∫ y : Fin 2 → X, G (y 0, y 1) ∂(Measure.pi fun _ : Fin 2 => ν) =
      ∫ z : X × X, τ (a.1, a.2 l, z.1, z.2) ^ 2 ∂(ν.prod ν) :=
    hmp2.hasLaw.integral_comp (f := G) hGm.aestronglyMeasurable
  rw [hlim] at hblock
  filter_upwards [hblock] with z hz
  simpa [hG, sq] using hz

/-- **The empirical covariance of an Aldous–Hoover array with square-integrable `τ`.**  Let
`τ` be measurable such that `τ (w, a, ·, ·)` is square-integrable for almost every `(w, a)`.
There are measurable `h : X³ → ℝ` (the partial integral
of `τ` over the last variable, off a null set where `τ (w, a, ·, ·)` is not square-integrable) and
`a : X² → ℝ ≥ 0` (the Jensen gap) such that, almost surely and for all `l, l'`,
`n⁻¹ ∑_{i<n} τ (w, u_l, v_i, x_{l, i}) τ (w, u_{l'}, v_i, x_{l', i})` converges to
`∫ h (w, u_l, v) h (w, u_{l'}, v) dv + δ_{l, l'} a (w, u_l)`. -/
theorem exists_ae_tendsto_mean_aldousHoover (hτ : Measurable τ)
    (hint : ∀ᵐ q ∂(ν.prod ν),
      Integrable (fun p : X × X => τ (q.1, q.2, p.1, p.2) ^ 2) (ν.prod ν)) :
    ∃ (h : X × X × X → ℝ) (a : X × X → ℝ), Measurable h ∧ Measurable a ∧ (∀ q, 0 ≤ a q) ∧
      (∀ q : X × X, Integrable (fun v => h (q.1, q.2, v) ^ 2) ν) ∧
      ∀ᵐ m ∂((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
          (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)), ∀ l l' : ℕ,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
            τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
              τ (m.1.1, m.1.2 l', m.2 (Sum.inl i), m.2 (Sum.inr (l', i)))) atTop
          (𝓝 ((∫ v, h (m.1.1, m.1.2 l, v) * h (m.1.1, m.1.2 l', v) ∂ν) +
            if l = l' then a (m.1.1, m.1.2 l) else 0)) := by
  classical
  set Gd : Set (X × X) := {q | Integrable (fun p : X × X => τ (q.1, q.2, p.1, p.2) ^ 2)
    (ν.prod ν)} with hGd
  have hτ2 : Measurable fun y : (X × X) × (X × X) => τ (y.1.1, y.1.2, y.2.1, y.2.2) ^ 2 :=
    (hτ.comp (by fun_prop)).pow_const 2
  have hGdm : MeasurableSet Gd :=
    measurableSet_integrable (μ := ν.prod ν) (f := fun (q p : X × X) => τ (q.1, q.2, p.1, p.2) ^ 2)
      hτ2.stronglyMeasurable
  have hGd_ae : ∀ᵐ q ∂(ν.prod ν), q ∈ Gd := hint
  -- truncate `τ` off the bad set
  set τ' : X × X × X × X → ℝ := fun y => if (y.1, y.2.1) ∈ Gd then τ y else 0 with hτ'
  have hτ'm : Measurable τ' :=
    Measurable.ite (hGdm.preimage (by fun_prop)) hτ measurable_const
  have hslice : ∀ q : X × X, Integrable (fun p : X × X => τ' (q.1, q.2, p.1, p.2) ^ 2) (ν.prod ν) :=
    fun q => by
      by_cases hq : q ∈ Gd
      · have : (fun p : X × X => τ' (q.1, q.2, p.1, p.2) ^ 2) =
            fun p => τ (q.1, q.2, p.1, p.2) ^ 2 := by
          funext p; simp [hτ', hq]
        rw [this]
        exact hq
      · have : (fun p : X × X => τ' (q.1, q.2, p.1, p.2) ^ 2) = fun _ => 0 := by
          funext p; simp [hτ', hq]
        rw [this]; exact integrable_zero _ _ _
  set h : X × X × X → ℝ := fun q => ∫ x, τ' (q.1, q.2.1, q.2.2, x) ∂ν with hh
  set D : X × X → ℝ := fun q => ∫ z : X × X, τ' (q.1, q.2, z.1, z.2) ^ 2 ∂(ν.prod ν) with hD
  set a : X × X → ℝ := fun q => D q - ∫ v, h (q.1, q.2, v) ^ 2 ∂ν with ha
  have hhm : Measurable h := by
    have : Measurable fun p : (X × X × X) × X => τ' (p.1.1, p.1.2.1, p.1.2.2, p.2) :=
      hτ'm.comp (by fun_prop)
    exact this.integral_prod_right'
  have hDm : Measurable D := by
    have : Measurable fun p : (X × X) × (X × X) => τ' (p.1.1, p.1.2, p.2.1, p.2.2) ^ 2 :=
      (hτ'm.comp (by fun_prop)).pow_const 2
    exact this.integral_prod_right'
  have hjens : ∀ q : X × X, Integrable (fun v => h (q.1, q.2, v) ^ 2) ν ∧
      ∫ v, h (q.1, q.2, v) ^ 2 ∂ν ≤ D q := fun q =>
    integrable_sq_integral_prod (μV := ν) (μX := ν)
      (f := fun z : X × X => τ' (q.1, q.2, z.1, z.2)) (hτ'm.comp (by fun_prop)) (hslice q)
  have ham : Measurable a := by
    have : Measurable fun p : (X × X) × X => h (p.1.1, p.1.2, p.2) ^ 2 :=
      (hhm.comp (by fun_prop)).pow_const 2
    exact hDm.sub this.integral_prod_right'
  have hG_ae : ∀ᵐ m ∂((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
      (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)), ∀ l : ℕ, (m.1.1, m.1.2 l) ∈ Gd := by
    rw [ae_all_iff]
    intro l
    have hmp : MeasurePreserving (fun m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X) => (m.1.1, m.1.2 l))
        ((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
          (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)) (ν.prod ν) :=
      ((MeasurePreserving.id ν).prod (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) l)).comp
        measurePreserving_fst
    exact hmp.quasiMeasurePreserving.ae hGd_ae
  have hoff : ∀ l l' : ℕ, ∀ᵐ m ∂((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
      (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)), l ≠ l' → Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ i ∈ range n,
          τ' (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
            τ' (m.1.1, m.1.2 l', m.2 (Sum.inl i), m.2 (Sum.inr (l', i)))) atTop
        (𝓝 (∫ v, (∫ x, τ' (m.1.1, m.1.2 l, v, x) ∂ν) * ∫ x, τ' (m.1.1, m.1.2 l', v, x) ∂ν ∂ν)) :=
    fun l l' => by
      by_cases hll' : l = l'
      · exact Filter.Eventually.of_forall fun m h => absurd hll' h
      · exact (ae_tendsto_mean_aldousHoover_offDiag ν hτ'm (Filter.Eventually.of_forall hslice)
          hll').mono fun m hm _ => hm
  have hdg := fun l => ae_tendsto_mean_aldousHoover_diag ν hτ'm
    (Filter.Eventually.of_forall hslice) l
  refine ⟨h, a, hhm, ham, fun q => ?_, fun q => (hjens q).1, ?_⟩
  · have := (hjens q).2
    simp only [ha]
    linarith
  · have h1 := ae_all_iff.2 fun l => ae_all_iff.2 fun l' => hoff l l'
    have h2 := ae_all_iff.2 hdg
    filter_upwards [hG_ae, h1, h2] with m hG hm1 hm2 l l'
    have hsum : (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
          τ (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
            τ (m.1.1, m.1.2 l', m.2 (Sum.inl i), m.2 (Sum.inr (l', i)))) =
        fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
          τ' (m.1.1, m.1.2 l, m.2 (Sum.inl i), m.2 (Sum.inr (l, i))) *
            τ' (m.1.1, m.1.2 l', m.2 (Sum.inl i), m.2 (Sum.inr (l', i))) := by
      funext n
      simp [hτ', hG l, hG l']
    rw [hsum]
    by_cases hll' : l = l'
    · subst hll'
      have hv : (∫ v, h (m.1.1, m.1.2 l, v) * h (m.1.1, m.1.2 l, v) ∂ν) +
          (if l = l then a (m.1.1, m.1.2 l) else 0) = D (m.1.1, m.1.2 l) := by
        have : (fun v => h (m.1.1, m.1.2 l, v) * h (m.1.1, m.1.2 l, v)) =
            fun v => h (m.1.1, m.1.2 l, v) ^ 2 := funext fun v => (sq _).symm
        simp only [ite_true, ha, this]
        ring
      rw [hv]
      exact hm2 l
    · simp only [hll', ite_false, add_zero]
      exact hm1 l l' hll'

/-- **Square-integrable sections from a finite empirical limit.**  If the empirical second moments
`n⁻¹ ∑_{i<n} τ (w, u_0, v_i, x_{0, i})²` converge to a finite limit almost surely, then
`τ (w, a, ·, ·)` is square-integrable for almost every `(w, a)`: given `(w, u_0)`, the terms are
i.i.d. and nonnegative, so a nonintegrable section would force the averages to tend to `∞`. -/
theorem ae_integrable_section_of_ae_exists_tendsto (hτ : Measurable τ)
    (hfin : ∀ᵐ m ∂((ν.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
        (Measure.infinitePi fun _ : ℕ ⊕ ℕ × ℕ => ν)), ∃ c : ℝ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i))) *
          τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i)))) atTop (𝓝 c)) :
    ∀ᵐ q ∂(ν.prod ν), Integrable (fun p : X × X => τ (q.1, q.2, p.1, p.2) ^ 2) (ν.prod ν) := by
  have hτ2 : Measurable fun y : (X × X) × (X × X) => τ (y.1.1, y.1.2, y.2.1, y.2.2) ^ 2 :=
    (hτ.comp (by fun_prop)).pow_const 2
  set Gd : Set (X × X) := {q | Integrable (fun p : X × X => τ (q.1, q.2, p.1, p.2) ^ 2)
    (ν.prod ν)} with hGd
  have hGdm : MeasurableSet Gd :=
    measurableSet_integrable (μ := ν.prod ν) (f := fun (q p : X × X) => τ (q.1, q.2, p.1, p.2) ^ 2)
      hτ2.stronglyMeasurable
  have hterm : ∀ i : ℕ, Measurable fun m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X) =>
      τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i))) *
        τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i))) := fun i =>
    (hτ.comp (by fun_prop)).mul (hτ.comp (by fun_prop))
  have hEm := measurableSet_exists_tendsto (l := atTop)
    (f := fun (n : ℕ) (m : (X × (ℕ → X)) × (ℕ ⊕ ℕ × ℕ → X)) => (n : ℝ)⁻¹ * ∑ i ∈ range n,
      τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i))) *
        τ (m.1.1, m.1.2 0, m.2 (Sum.inl i), m.2 (Sum.inr (0, i))))
    (fun n => measurable_const.mul (Finset.measurable_sum _ fun i _ => hterm i))
  have hA := (Measure.ae_prod_iff_ae_ae hEm).1 hfin
  have hmp0 : MeasurePreserving (fun a : X × (ℕ → X) => (a.1, a.2 0))
      (ν.prod (Measure.infinitePi fun _ : ℕ => ν)) (ν.prod ν) :=
    (MeasurePreserving.id ν).prod (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0)
  have hGa : ∀ᵐ a ∂(ν.prod (Measure.infinitePi fun _ : ℕ => ν)), (a.1, a.2 0) ∈ Gd := by
    filter_upwards [hA] with a ha
    by_contra hnot
    set G : X × X → ℝ := fun p => τ (a.1, a.2 0, p.1, p.2) ^ 2 with hG
    have hGm : Measurable G := (hτ.comp (by fun_prop)).pow_const 2
    have hmp2 := measurePreserving_finTwoArrow ν
    have hΦnot : ¬ Integrable (fun y : Fin 2 → X => G (y 0, y 1)) (Measure.pi fun _ => ν) :=
      fun hi => hnot ((hmp2.integrable_comp (g := G) hGm.aestronglyMeasurable).1 hi)
    obtain ⟨hf, hdisj⟩ := aldousHooverBlock_two 0
    have hNN := ae_tendsto_atTop_mean_infinitePi_blocks ν (J := ℕ ⊕ ℕ × ℕ) (F := Fin 2)
      (f := fun i => ![Sum.inl i, Sum.inr (0, i)]) hf hdisj (Φ := fun y => G (y 0, y 1))
      (hGm.comp (by fun_prop)) (fun y => sq_nonneg _) hΦnot
    obtain ⟨z, ⟨c, hc⟩, hz⟩ := (ha.and hNN).exists
    refine not_tendsto_nhds_of_tendsto_atTop ?_ c hc
    simpa [hG, sq] using hz
  have hnull : (ν.prod ν) Gdᶜ = 0 := by
    rw [← hmp0.measure_preimage hGdm.compl.nullMeasurableSet]
    exact hGa
  exact hnull

end Limit

end SpinGlasses
