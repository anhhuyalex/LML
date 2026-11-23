/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianTiltedRotationBound
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavitySpecialization

/-!
# Gaussian rotation derivative in the split constraint cavity

Apply Gaussian integration by parts to the old Gibbs law with the removed constraint's two
auxiliary coordinates attached. An observable can use all the old auxiliary coordinates and the
old disorder. The four groups are the inputs for the overlap-moment estimate in Lemma 2.3.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

/-- Measurability of a replica average after attaching independent coordinates to a tilted law,
and adding a second tilt. -/
private theorem measurable_integral_pi_tilted_prod_tilted
    {Ω W α β R : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace α]
    [MeasurableSpace β] [Fintype R]
    (μ : Measure α) [IsFiniteMeasure μ] (γ : Measure β) [IsProbabilityMeasure γ]
    {E : Ω → α → ℝ}
    (hE : Measurable fun p : Ω × α => E p.1 p.2)
    (hEi : ∀ ω, Integrable (fun a => Real.exp (E ω a)) μ)
    {V : Ω × W → α × β → ℝ}
    (hV : Measurable fun p : (Ω × W) × (α × β) => V p.1 p.2)
    {F : Ω × W → (R → α × β) → ℝ}
    (hF : Measurable fun p : (Ω × W) × (R → α × β) => F p.1 p.2) :
    Measurable fun p => ∫ σ : R → α × β, F p σ
      ∂(Measure.pi fun _ : R => ((μ.tilted (E p.1)).prod γ).tilted (V p)) := by
  let H (p : Ω × W) (a : α × β) := E p.1 a.1 + V p a
  have hH : Measurable fun p : (Ω × W) × (α × β) => H p.1 p.2 :=
    (hE.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))).add hV
  have hν (p : Ω × W) : ((μ.tilted (E p.1)).prod γ).tilted (V p) =
      (μ.prod γ).tilted (H p) := by
    rw [← tilted_prod_comp_fst, tilted_tilted ((hEi p.1).comp_fst γ)]
    rfl
  simp_rw [hν]
  exact measurable_integral_pi_tilted hH hF

/-- Joint measurability of the last-row rotated field in the split cavity coordinates. -/
theorem measurable_cavity_rotation_field {N M : ℕ} (t q s : ℝ) :
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    Measurable fun p : ((Fin N ⊕ Unit) ⊕ Unit → ℝ) ×
        (SmartPathState N M × (Fin 2 → ℝ)) =>
      Real.cos s * (X p.2.1.1 ⬝ᵥ p.1 + A ⬝ᵥ p.2.2) +
        Real.sin s * (Y ⬝ᵥ p.1 + E ⬝ᵥ p.2.2) := by
  intro X Y A E
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let T := SmartPathState N M × (Fin 2 → ℝ)
  have hX (j : (Fin N ⊕ Unit) ⊕ Unit) :
      Measurable fun p : W × T => X p.2.1.1 j :=
    (measurable_of_finite fun a => X a j).comp
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hdot : Measurable fun p : W × T => X p.2.1.1 ⬝ᵥ p.1 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ => (hX j).mul
      ((measurable_pi_apply j).comp measurable_fst)
  have hdotY : Measurable fun p : W × T => Y ⬝ᵥ p.1 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul
      ((measurable_pi_apply j).comp measurable_fst)
  have hdotA : Measurable fun p : W × T => A ⬝ᵥ p.2.2 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  have hdotE : Measurable fun p : W × T => E ⬝ᵥ p.2.2 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  exact ((hdot.add hdotA).const_mul _).add ((hdotY.add hdotE).const_mul _)

/-- A split-cavity replica average is jointly measurable in the old disorder and the
fresh shared coordinates. The observable may depend on both. -/
theorem measurable_integral_pi_cavity_rotation
    {N M : ℕ} {R : Type*} [Fintype R] (t q s : ℝ)
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    {F : (SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) →
      (R → SmartPathState N M × (Fin 2 → ℝ)) → ℝ}
    (hF : Measurable fun p : (SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) ×
      (R → SmartPathState N M × (Fin 2 → ℝ)) => F p.1 p.2) :
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (s : ℝ) (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    Measurable fun p => ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ), F p σ
      ∂(Measure.pi fun _ : R => ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S s p.2 x))) := by
  intro μ₀ γ_aux X Y A E S
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let T := SmartPathState N M × (Fin 2 → ℝ)
  let Ω := SmartPathDisorder N M
  have hs : Measurable fun p : W × T => S s p.1 p.2 :=
    measurable_cavity_rotation_field (N := N) (M := M) t q s
  let V (p : Ω × W) (x : T) := u (S s p.2 x)
  have hp : Measurable (fun p : (Ω × W) × T => (p.1.2, p.2)) :=
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hV₀ := (hu.comp hs).comp hp
  have hV : Measurable fun p : (Ω × W) × T => V p.1 p.2 := hV₀
  exact measurable_integral_pi_tilted_prod_tilted (smartPathBase N M) γ_aux
    (E := smartPathEnergy u t) (V := V) (F := F)
    (measurable_smartPathEnergy hu t) (fun ω =>
      integrable_exp_perceptron_smart_path_energy hu hD ω t) hV hF

/-- Joint measurability of the rotated cavity Gibbs average after integrating the fresh
shared Gaussian coordinates. The observable can use the full old Gibbs state. -/
theorem measurable_integral_integral_pi_cavity_rotation
    {N M : ℕ} {R : Type*} [Fintype R] (t q s : ℝ)
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (ψ : R → ℝ → ℝ) (hψ : ∀ r, Measurable (ψ r))
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2) :
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_sh := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (s : ℝ) (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    Measurable fun ω =>
      ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
        f ω (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
      ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S s w x)))
      ∂γ_sh := by
  intro μ₀ γ_sh γ_aux X Y A E S
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let T := SmartPathState N M × (Fin 2 → ℝ)
  let Ω := SmartPathDisorder N M
  let ν (s : ℝ) (p : Ω × W) : Measure T :=
    ((μ₀ p.1).prod γ_aux).tilted (fun x => u (S s p.2 x))
  have hs (s : ℝ) : Measurable fun p : W × T => S s p.1 p.2 :=
    measurable_cavity_rotation_field (N := N) (M := M) t q s
  let F (s : ℝ) (p : Ω × W) (σ : R → T) :=
    f p.1 (fun r => (σ r).1) * ∏ r, ψ r (S s p.2 (σ r))
  have hFm (s : ℝ) : Measurable fun p : (Ω × W) × (R → T) => F s p.1 p.2 := by
    have hproj : Measurable fun p : (Ω × W) × (R → T) =>
        ((p.1.1, fun r => (p.2 r).1) : Ω × (R → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have h10 := hf.comp hproj
    have h1 : Measurable fun p : (Ω × W) × (R → T) => f p.1.1 (fun r => (p.2 r).1) := h10
    have hpair (r : R) : Measurable fun p : (Ω × W) × (R → T) => (p.1.2, p.2 r) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)
    have h2 (r : R) := (hs s).comp (hpair r)
    have h3 : Measurable fun p : (Ω × W) × (R → T) => ∏ r, ψ r (S s p.1.2 (p.2 r)) := by
      refine Finset.measurable_prod _ fun r _ => ?_
      have hm := (hψ r).comp (h2 r)
      exact hm
    exact h1.mul h3
  change Measurable fun ω : Ω => ∫ w : W, ∫ σ : R → T, F s (ω, w) σ
    ∂(Measure.pi fun _ : R => ν s (ω, w)) ∂γ_sh
  have hm := measurable_integral_pi_cavity_rotation t q s hu hD (F := F s) (hFm s)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := γ_sh)).measurable

/-- The four-group derivative for the Gaussian perceptron in the split cavity coordinates.
The observable may depend on the old disorder and all old auxiliary coordinates. The shared
covariance difference equals `q - R^t` by `cavity_rotation_dotProducts`. The field variance
`variance` belongs to the smart path; the angle parameter is `s`. -/
theorem hasDerivAt_integral_integral_pi_cavity_rotation_ibp
    {N M : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {t q : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : R → ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀ r)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁ r)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂ r)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
    (s₀ : ℝ) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_sh := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (s : ℝ) (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let C_cov (σ τ : PerceptronSpin N) : ℝ :=
      Y ⬝ᵥ Y - X σ ⬝ᵥ X τ
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    let D_ω (s : ℝ) (ω₀ : SmartPathDisorder N M) : ℝ :=
      (∑ i : R, ∑ j ∈ Finset.univ.erase i,
        ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * C_cov (σ i).1.1 (σ j).1.1 *
            (ψ_d i (S s w (σ i)) * ψ_d j (S s w (σ j)) *
              ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s w (σ r)))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh) -
      (Fintype.card R : ℝ) * ∑ i : R,
        ∫ w, ∫ σ : Option R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ (some r)).1) * C_cov (σ (some i)).1.1 (σ none).1.1 *
            (ψ_d i (S s w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s w (σ (some r)))) *
            deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option R =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh -
      (Fintype.card R : ℝ) * ∑ j : R,
        ∫ w, ∫ σ : Option R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ (some r)).1) * C_cov (σ none).1.1 (σ (some j)).1.1 *
            (ψ_d j (S s w (σ (some j))) *
              ∏ r ∈ Finset.univ.erase j, ψ r (S s w (σ (some r)))) *
            deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option R =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
        ∫ w, ∫ σ : Option (Option R) → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ (some (some r))).1) * C_cov (σ (some none)).1.1 (σ none).1.1 *
            (∏ r : R, ψ r (S s w (σ (some (some r))))) *
            deriv u (S s w (σ (some none))) * deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option (Option R) =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh
    (∀ᵐ ω₀ ∂P₀, Integrable (f ω₀) (Measure.pi fun _ : R => μ₀ ω₀)) →
    Integrable (fun ω₀ => ∫ a, |f ω₀ a| ∂(Measure.pi fun _ : R => μ₀ ω₀)) P₀ →
    HasDerivAt
      (fun s => ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))
          ∂γ_sh ∂P₀)
      (Real.sin s₀ * Real.cos s₀ * ∫ ω₀, D_ω s₀ ω₀ ∂P₀)
      s₀ := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S C_cov ψ_d D_ω hfi hfi'
  have : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have hGm (s : ℝ) :=
    (measurable_integral_integral_pi_cavity_rotation t q s hu.measurable (fun x => hu.le x)
      ψ (fun r => (hψd r).continuous.measurable) hf).aestronglyMeasurable (μ := P₀)
  obtain ⟨hX, hA, hVX, hVY, _⟩ := cavity_rotation_dotProducts (N := N) ht hq
  have h := hasDerivAt_integral_integral_gaussian_tilted_rotation_ibp P₀ μ₀
    (fun x : SmartPathState N M => x.1) measurable_fst X (fun _ => Y)
    (fun _ => A) (fun _ => E) (fun m _ => hX m) (fun _ _ => hA)
    (fun m => (hVX m).trans hVY.symm)
    hu.differentiable hu.differentiable_deriv hu.abs_le hu.abs_deriv_le hu.abs_deriv₂_le
    ψ hψd hψ₂d hM₀ hM₁ hM₂ hfi hfi' hGm s₀
  exact h

/-- The state split followed by the disorder split transports the full cavity average,
including observables of both the original and the fresh coordinates. -/
theorem integral_pi_cavity_rotation_eq_integral_cavity_extended
    {N M : ℕ} {R : Type*} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t q s : ℝ) (variance : ℝ≥0)
    {G : (SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) →
        (R → SmartPathState N M × (Fin 2 → ℝ)) → ℝ}
    (hG : Measurable fun p : (SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) ×
          (R → SmartPathState N M × (Fin 2 → ℝ)) => G p.1 p.2) :
    let Ω := SmartPathDisorder N M
    let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
    let T := SmartPathState N M × (Fin 2 → ℝ)
    let Ωfull := SmartPathDisorder N (M + 1) × ℝ
    let Tfull := SmartPathState N (M + 1) × ℝ
    let splitΩ (p : Ωfull) : Ω × W :=
      (((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2),
        Sum.elim (Sum.elim (p.1.1.1 (Fin.last M)) (fun _ => p.1.1.2 (Fin.last M)))
          (fun _ => p.2))
    let splitT (x : Tfull) : T :=
      ((x.1.1, Fin.init x.1.2), ![x.1.2 (Fin.last M), x.2])
    let P₀ : Measure Ω := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let Pfull : Measure Ωfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let γ_sh : Measure W := Measure.pi fun _ => gaussianReal 0 1
    let γ_aux : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 1
    let μ₀ (ω : Ω) := (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let X : PerceptronSpin N → W := fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : W := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (w : W) (x : T) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted fun x => u (S p.2 x)
    let νfull (p : Ωfull) := ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
      fun x : Tfull => smartPathEnergy u t (splitΩ p).1 (splitT x).1 +
        u (Real.cos s * smartPathField t p.1 x.1 (Fin.last M) +
          Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))
    ∫ p, ∫ a, G p a ∂(Measure.pi fun _ : R => ν p) ∂(P₀.prod γ_sh) =
      ∫ p, ∫ a, G (splitΩ p) (fun r => splitT (a r))
        ∂(Measure.pi fun _ : R => νfull p) ∂Pfull := by
  intro Ω W T Ωfull Tfull splitΩ splitT P₀ Pfull γ_sh γ_aux μ₀ X Y A E S ν νfull
  let J (p : Ω × W) := ∫ a, G p a ∂(Measure.pi fun _ : R => ν p)
  have hJ : Measurable J := measurable_integral_pi_cavity_rotation t q s hu hD (F := G) hG
  have hmp : MeasurePreserving splitΩ Pfull (P₀.prod γ_sh) :=
    measurePreserving_smartPathDisorder_cavitySplit N M variance
  have htransport : ∫ p, J (splitΩ p) ∂Pfull = ∫ p, J p ∂(P₀.prod γ_sh) :=
    hmp.integral_comp_of_aestronglyMeasurable hJ.aestronglyMeasurable
  rw [← htransport]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hs (x : T) : S (splitΩ p).2 x = Real.cos s *
        (cavityCoef N t x.1.1 ⬝ᵥ
          Sum.elim (p.1.1.1 (Fin.last M)) (fun _ : Unit => p.1.1.2 (Fin.last M)) +
          Real.sqrt ((1 - t) / (N + 1)) * x.2 0) +
        Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2 1) := by
    simp [S, X, Y, A, E, splitΩ, dotProduct]
  have hν : ν (splitΩ p) = (((μ₀ (splitΩ p).1).prod γ_aux).tilted
      fun x : T => u (Real.cos s *
        (cavityCoef N t x.1.1 ⬝ᵥ
          Sum.elim (p.1.1.1 (Fin.last M)) (fun _ : Unit => p.1.1.2 (Fin.last M)) +
          Real.sqrt ((1 - t) / (N + 1)) * x.2 0) +
        Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2 1))) := by
    change (((μ₀ (splitΩ p).1).prod γ_aux).tilted fun x => u (S (splitΩ p).2 x)) = _
    simp only [hs]
    rfl
  change (∫ a, G (splitΩ p) a ∂(Measure.pi fun _ : R => ν (splitΩ p))) =
    ∫ a, G (splitΩ p) (fun r => splitT (a r)) ∂(Measure.pi fun _ : R => νfull p)
  rw [hν]
  exact (cavity_extended_replica_split_eq hu hD t q s p.1 p.2 (G (splitΩ p))).symm

end SpinGlasses
