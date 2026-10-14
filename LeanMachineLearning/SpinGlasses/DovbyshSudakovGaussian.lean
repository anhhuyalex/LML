/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import LeanMachineLearning.ForMathlib.Probability.IdentDistribProd
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianCholesky
public import LeanMachineLearning.ForMathlib.Probability.StrongLawMixture

/-!
# The Gaussian array attached to a positive semidefinite exchangeable array

This is the first step of the proof of the Dovbysh–Sudakov theorem (Panchenko §1.5).  Let `R` be
a random array whose finite principal submatrices are almost surely positive semidefinite, and
whose law is invariant under simultaneous permutations of rows and columns.  Conditionally on
`R`, the columns `(g_{l, i})_l`, `i ≥ 1`, of the Gaussian array are i.i.d. centered Gaussian
sequences with covariance `R`.  We realize them as
`g_{l, i} = ∑_{k ≤ l} (cholInf R) l k ξ_{i, k}` for an array `ξ` of i.i.d. standard Gaussians
(independent of `R`), so every entry is a finite sum.

## Main declarations

* `SpinGlasses.identDistrib_gaussianArray_separately`: `g` is separately exchangeable.  Columns
  are exchangeable because they are conditionally i.i.d.; rows are exchangeable because `R` is
  and the conditional law depends on `R` only through its covariance
  (`ProbabilityTheory.map_cholInf_comp_equiv`).
* `SpinGlasses.ae_tendsto_gaussianArray_mean`: almost surely,
  `n⁻¹ ∑_{i<n} g_{l, i} g_{l', i} → R_{l, l'}` (the strong law of large numbers).

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.5, proof of Theorem 1.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology

namespace SpinGlasses

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
  {R : Ω → ℕ → ℕ → ℝ}

/-- **Separate exchangeability of the Gaussian array of an exchangeable positive semidefinite
array.**  Here `s (l, i) (ω, ξ) = ∑_{k ≤ l} (cholInf (R ω)) l k * ξ i k` with `ξ` an array of
i.i.d. standard Gaussians, and the probability space is `P ⊗ γ`. -/
theorem identDistrib_gaussianArray_separately (hR : ∀ l l', Measurable fun ω => R ω l l')
    (hpsd : ∀ᵐ ω ∂P, ∀ k : ℕ, (Matrix.of fun l l' : Fin k => R ω l l').PosSemidef)
    (hexch : ∀ e : ℕ ≃ ℕ, IdentDistrib (fun ω l l' => R ω (e l) (e l')) R P P)
    {s : ℕ × ℕ → Ω × (ℕ → ℕ → ℝ) → ℝ}
    (hs : ∀ p z, s p z = ∑ k ∈ range (p.1 + 1), cholInf (R z.1) p.1 k * z.2 p.2 k)
    (e₁ e₂ : ℕ ≃ ℕ) :
    IdentDistrib (fun z (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) z) (fun z p => s p z)
      (P.prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (P.prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    := by
  set ν := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hν
  set γ := Measure.infinitePi fun _ : ℕ => ν with hγ
  have hRm : Measurable R := by fun_prop
  set G : (ℕ → ℕ → ℝ) × (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ :=
    fun w i l => ∑ k ∈ range (l + 1), cholInf w.1 l k * w.2 i k with hG
  have hGm : Measurable G := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun l =>
    Finset.measurable_sum _ fun k _ => ((measurable_cholInf l k).comp measurable_fst).mul
      ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd))
  set Arr : (ℕ → ℕ → ℝ) → ℕ × ℕ → ℝ := fun C p => C p.2 p.1 with hArr
  have hArrm : Measurable Arr :=
    measurable_pi_iff.2 fun p => (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)
  have hsA : ∀ z p, s p z = Arr (G (R z.1, z.2)) p := fun z p => hs p z
  -- row permutation
  have hrow : IdentDistrib (fun z : Ω × (ℕ → ℕ → ℝ) =>
      (fun i l => G (R z.1, z.2) i (e₁ l))) (fun z => G (R z.1, z.2)) (P.prod γ) (P.prod γ) := by
    refine identDistrib_prod_comp_of_ae_map_eq (P := P) (γ := γ) (R := R) hRm (F := G) hGm
      (ρ := fun C i l => C i (e₁ l)) ?_ (φ := fun A l l' => A (e₁ l) (e₁ l')) ?_ ?_ (hexch e₁)
    · fun_prop
    · fun_prop
    · filter_upwards [hpsd] with ω hω
      have hm1 : ∀ _ : ℕ, Measurable fun c : ℕ → ℝ => fun l => ∑ k ∈ range (e₁ l + 1),
          cholInf (R ω) (e₁ l) k * c k := fun _ => measurable_pi_iff.2 fun l =>
        Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_pi_apply k)
      have hm2 : ∀ _ : ℕ, Measurable fun c : ℕ → ℝ => fun l => ∑ k ∈ range (l + 1),
          cholInf (fun a b => R ω (e₁ a) (e₁ b)) l k * c k := fun _ => measurable_pi_iff.2 fun l =>
        Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_pi_apply k)
      have h1 := Measure.infinitePi_map_pi (μ := fun _ : ℕ => ν)
        (f := fun _ (c : ℕ → ℝ) (l : ℕ) => ∑ k ∈ range (e₁ l + 1), cholInf (R ω) (e₁ l) k * c k)
        hm1
      have h2 := Measure.infinitePi_map_pi (μ := fun _ : ℕ => ν)
        (f := fun _ (c : ℕ → ℝ) (l : ℕ) => ∑ k ∈ range (l + 1),
          cholInf (fun a b => R ω (e₁ a) (e₁ b)) l k * c k) hm2
      simp only [hG]
      rw [h1, h2, map_cholInf_comp_equiv hω e₁]
  -- column permutation
  set X : Ω × (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ := fun z i l => G (R z.1, z.2) i (e₁ l) with hX
  have hXm : Measurable X := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun l =>
    (measurable_pi_apply (e₁ l)).comp ((measurable_pi_apply i).comp (hGm.comp
      ((hRm.comp measurable_fst).prodMk measurable_snd)))
  set T : Ω × (ℕ → ℕ → ℝ) → Ω × (ℕ → ℕ → ℝ) := fun z => (z.1, z.2 ∘ e₂) with hT
  have hTmp : MeasurePreserving T (P.prod γ) (P.prod γ) :=
    (MeasurePreserving.id P).prod (Measure.measurePreserving_comp_equiv_infinitePi ν e₂)
  have hXT : IdentDistrib (X ∘ T) X (P.prod γ) (P.prod γ) := by
    refine ⟨(hXm.comp hTmp.measurable).aemeasurable, hXm.aemeasurable, ?_⟩
    rw [← Measure.map_map hXm hTmp.measurable, hTmp.map_eq]
  have hcomp : (fun z (p : ℕ × ℕ) => s (e₁ p.1, e₂ p.2) z) = Arr ∘ (X ∘ T) := by
    funext z p
    simp only [hsA, Function.comp_apply, hArr, hX, hT]
    rfl
  have hcomp' : (fun z (p : ℕ × ℕ) => s p z) = Arr ∘ fun z => G (R z.1, z.2) := by
    funext z p
    simp only [hsA, Function.comp_apply]
  rw [hcomp, hcomp']
  exact (hXT.trans hrow).comp hArrm

omit [SFinite P] in
/-- **Strong law of large numbers for the Gaussian array.**  Almost surely,
`n⁻¹ ∑_{i<n} g_{l, i} g_{l', i}` converges to the covariance entry `R_{l, l'}`: given `R`, the
columns of the array are i.i.d. centered Gaussian sequences with covariance `R`. -/
theorem ae_tendsto_gaussianArray_mean (hR : ∀ l l', Measurable fun ω => R ω l l')
    (hpsd : ∀ᵐ ω ∂P, ∀ k : ℕ, (Matrix.of fun l l' : Fin k => R ω l l').PosSemidef)
    {s : ℕ × ℕ → Ω × (ℕ → ℕ → ℝ) → ℝ}
    (hs : ∀ p z, s p z = ∑ k ∈ range (p.1 + 1), cholInf (R z.1) p.1 k * z.2 p.2 k) (l l' : ℕ) :
    ∀ᵐ z ∂(P.prod (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, s (l, i) z * s (l', i) z) atTop
        (𝓝 (R z.1 l l')) := by
  set ν := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hν
  have hRm : Measurable R := by fun_prop
  set Ψ : Ω → (ℕ → ℝ) → ℝ := fun ω c => (∑ k ∈ range (l + 1), cholInf (R ω) l k * c k) *
    ∑ k ∈ range (l' + 1), cholInf (R ω) l' k * c k with hΨ
  have hΨm : Measurable (Function.uncurry Ψ) := by
    have hcol : ∀ m : ℕ, Measurable fun x : Ω × (ℕ → ℝ) =>
        ∑ k ∈ range (m + 1), cholInf (R x.1) m k * x.2 k := fun m =>
      Finset.measurable_sum _ fun k _ =>
        ((measurable_cholInf m k).comp (hRm.comp measurable_fst)).mul
          ((measurable_pi_apply k).comp measurable_snd)
    exact (hcol l).mul (hcol l')
  have hint : ∀ᵐ ω ∂P, Integrable (Ψ ω) ν ∧ ∫ c, Ψ ω c ∂ν = R ω l l' := by
    filter_upwards [hpsd] with ω hω
    exact integrable_integral_cholInf_mul hω l l'
  have h := ae_tendsto_mean_prod_infinitePi P ν hΨm (hint.mono fun ω hω => hω.1)
  have hfst : ∀ᵐ z ∂(P.prod (Measure.infinitePi fun _ : ℕ => ν)),
      Integrable (Ψ z.1) ν ∧ ∫ c, Ψ z.1 c ∂ν = R z.1 l l' :=
    (Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := Measure.infinitePi fun _ : ℕ => ν)).ae hint
  filter_upwards [h, hfst] with z hz hz'
  rw [← hz'.2]
  simpa [hs, hΨ] using hz

end SpinGlasses
