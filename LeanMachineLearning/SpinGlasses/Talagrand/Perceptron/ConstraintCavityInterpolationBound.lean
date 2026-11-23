/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityOverlapBound

/-!
# Derivative bounds for the cavity in `M` in the book's coordinates (Lemma 2.3.2)

Talagrand Section 2.3, Lemma 2.3.2, Eq. (2.40). `ConstraintCavityOverlapBound.lean` bounds the
angle derivative `d/ds` of the split-disorder cavity average by `(4 n² + n) L^{n+2}` times the
Hölder pair moment plus the `1/(N + 1)` first-moment correction. Here we:

1. apply Fubini (`integral_prod`) and `integral_pi_cavity_rotation_eq_integral_cavity_extended` to
   identify the iterated split-disorder average and moments with the full extended-cavity average
   `ν_{t,v}`;
2. compose with `v ↦ arccos √v` on `(0, 1)` via `HasDerivAt.comp_arccos_sqrt_of_sin_cos`, cancelling
   the singular chain-rule factor against `sin s * cos s` to obtain `-z / 2`;
3. specialize the moving replica factors `ψ_r` to `1` (`B_v ≡ 1`) and to two copies of `deriv u` on
   distinct replicas (`B_v = u'(S_v^{r₁}) u'(S_v^{r₂})`), using Talagrand's hypothesis (2.7)
   (`∀ j < 3, Differentiable ℝ (iteratedDeriv j u)` and `∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D`),
   with an explicit constant `K(n, D)` chosen before `N, M, t, q, v, variance, f`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

universe uR

/-- Unpack Talagrand's chapter assumption (2.7) into `SmartPathPotential₂ u D D D` together with
differentiability of `u''` and the uniform bound `|u'''| ≤ D`. -/
theorem smartPathPotential_two_of_iteratedDeriv {u : ℝ → ℝ} {D : ℝ}
    (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D) :
    SmartPathPotential₂ u D D D ∧
      Differentiable ℝ (deriv (deriv u)) ∧
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) := by
  have h0 : Differentiable ℝ u := by simpa using hd 0 (by omega)
  have h1 : Differentiable ℝ (deriv u) := by simpa [iteratedDeriv_one] using hd 1 (by omega)
  have h2 : Differentiable ℝ (deriv (deriv u)) := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hd 2 (by omega)
  have hb0 : ∀ x, |u x| ≤ D := fun x => by simpa using hb 0 (by omega) x
  have hb1 : ∀ x, |deriv u x| ≤ D := fun x => by
    simpa [iteratedDeriv_one] using hb 1 (by omega) x
  have hb2 : ∀ x, |deriv (deriv u) x| ≤ D := fun x => by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hb 2 (by omega) x
  have hb3 : ∀ x, |deriv (deriv (deriv u)) x| ≤ D := fun x => by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hb 3 (by omega) x
  exact ⟨⟨⟨h0, hb0, hb1⟩, h1, hb2⟩, h2, hb3⟩

/-- **Fubini and split-to-full transport for the weighted cavity average.** When `f` has
almost-everywhere integrable old-Gibbs sections and integrable old-disorder `L¹` moment, and each
`ψ r` is measurable and bounded, the iterated integral over `(ω₀, w)` equals the full extended
cavity average over `(ω, z)`. -/
theorem integral_integral_pi_cavity_rotation_eq_extended
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (t q s : ℝ) (variance : ℝ≥0)
    (ψ : R → ℝ → ℝ) (hψm : ∀ r, Measurable (ψ r))
    {M₀ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2) :
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
    let S (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let νfull (p : SmartPathDisorder N (M + 1) × ℝ) :=
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) +
            u (Real.cos s * smartPathField t p.1 x.1 (Fin.last M) +
              Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
        f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r))
        ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S w x)))
        ∂γ_sh ∂P₀ =
      ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
        f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
          (fun r => ((a r).1.1, Fin.init (a r).1.2)) *
          ∏ r, ψ r (Real.cos s * smartPathField t p.1 (a r).1 (Fin.last M) +
            Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (a r).2))
        ∂(Measure.pi fun _ : R => νfull p) ∂Pfull := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S Pfull νfull hfi hfi₁
  let Ω := SmartPathDisorder N M
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let T := SmartPathState N M × (Fin 2 → ℝ)
  let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted fun x => u (S p.2 x)
  let G (p : Ω × W) (σ : R → T) := f p.1 (fun r => (σ r).1) * ∏ r, ψ r (S p.2 (σ r))
  have hs : Measurable fun p : W × T => S p.1 p.2 :=
    measurable_cavity_rotation_field (N := N) (M := M) t q s
  have hGm : Measurable fun p : (Ω × W) × (R → T) => G p.1 p.2 := by
    have hproj : Measurable fun p : (Ω × W) × (R → T) =>
        ((p.1.1, fun r => (p.2 r).1) : Ω × (R → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have h1 : Measurable fun p : (Ω × W) × (R → T) => f p.1.1 (fun r => (p.2 r).1) :=
      hf.comp hproj
    have hpair (r : R) : Measurable fun p : (Ω × W) × (R → T) => (p.1.2, p.2 r) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)
    have h2 (r : R) := hs.comp (hpair r)
    have h3 : Measurable fun p : (Ω × W) × (R → T) => ∏ r, ψ r (S p.1.2 (p.2 r)) := by
      refine Finset.measurable_prod _ fun r _ => ?_
      have hm := (hψm r).comp (h2 r)
      exact hm
    exact h1.mul h3
  let J (p : Ω × W) := ∫ σ : R → T, G p σ ∂(Measure.pi fun _ : R => ν p)
  have hJm : Measurable J :=
    measurable_integral_pi_cavity_rotation t q s hu.measurable (fun x => hu.le x) (F := G) hGm
  obtain ⟨hFI, hF₁⟩ :=
    integrable_integral_pi_cavity_rotation_abs t q s variance hu hf hfi hfi₁
  let C : ℝ := |M₀| ^ Fintype.card R
  have hprod_le (w : W) (σ : R → T) : |∏ r, ψ r (S w (σ r))| ≤ C := by
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _r : R, |M₀| :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
            fun r _ => (hM₀ r _).trans (le_abs_self _)
      _ = C := by simp [C]
  have : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have hV (p : Ω × W) : Measurable fun x : T => u (S p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have h := hu.measurable.comp (hs.comp hp)
    exact h
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hu.le _)
  have hJi : Integrable J (P₀.prod γ_sh) := by
    refine (hF₁.mul_const C).mono' hJm.aestronglyMeasurable (hFI.mono fun p hp => ?_)
    rw [Real.norm_eq_abs]
    calc |J p| ≤ ∫ σ : R → T, |G p σ| ∂(Measure.pi fun _ : R => ν p) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ σ : R → T, |f p.1 (fun r => (σ r).1)| * C ∂(Measure.pi fun _ : R => ν p) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (hp.abs.mul_const C) (ae_of_all _ fun σ => ?_)
          change |f p.1 (fun r => (σ r).1) * ∏ r, ψ r (S p.2 (σ r))| ≤
            |f p.1 (fun r => (σ r).1)| * C
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hprod_le _ _) (abs_nonneg _)
      _ = (∫ σ : R → T, |f p.1 (fun r => (σ r).1)| ∂(Measure.pi fun _ : R => ν p)) * C :=
          integral_mul_const _ _
  have hfub : ∫ ω₀, ∫ w, J (ω₀, w) ∂γ_sh ∂P₀ = ∫ p, J p ∂(P₀.prod γ_sh) :=
    (integral_prod J hJi).symm
  have htrans := integral_pi_cavity_rotation_eq_integral_cavity_extended
    hu.measurable (fun x => hu.le x) t q s variance (G := G) hGm
  change (∫ ω₀, ∫ w, J (ω₀, w) ∂γ_sh ∂P₀) = _
  rw [hfub, htrans]
  refine integral_congr_ae (ae_of_all _ fun p => integral_congr_ae (ae_of_all _ fun a => ?_))
  change f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
      (fun r => ((a r).1.1, Fin.init (a r).1.2)) * _ = _
  congr 1
  refine Finset.prod_congr rfl fun r _ => congrArg (ψ r) ?_
  have hfl := smartPathField_last_eq_dotProduct (t := t) p.1 (a r).1
  have hs_eq : S (Sum.elim (Sum.elim (p.1.1.1 (Fin.last M)) (fun _ : Unit => p.1.1.2 (Fin.last M)))
        (fun _ : Unit => p.2))
      (((a r).1.1, Fin.init (a r).1.2), ![(a r).1.2 (Fin.last M), (a r).2]) =
      Real.cos s *
        (cavityCoef N t (a r).1.1 ⬝ᵥ
          Sum.elim (p.1.1.1 (Fin.last M)) (fun _ : Unit => p.1.1.2 (Fin.last M)) +
          Real.sqrt ((1 - t) / (N + 1)) * (a r).1.2 (Fin.last M)) +
        Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (a r).2) := by
    simp [S, X, Y, A, E, dotProduct]
  rw [hs_eq, ← hfl]

private lemma cavity_moment_split_eq_s
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t q s : ℝ) (variance : ℝ≥0)
    {g : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hg : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => g p.1 p.2) :
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
    let S (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ) (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) + Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let ν (p : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) :=
      ((μ₀ p.1).prod γ_aux).tilted fun x => u (S p.2 x)
    let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let νfull (p : SmartPathDisorder N (M + 1) × ℝ) :=
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) +
            u (Real.cos s * smartPathField t p.1 x.1 (Fin.last M) +
              Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))
    ∫ p, ∫ a : R → SmartPathState N M × (Fin 2 → ℝ),
        g p.1 (fun r => (a r).1) ∂(Measure.pi fun _ : R => ν p) ∂(P₀.prod γ_sh) =
      ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
        g ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
          (fun r => ((a r).1.1, Fin.init (a r).1.2))
        ∂(Measure.pi fun _ : R => νfull p) ∂Pfull := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S ν Pfull νfull
  let Ω := SmartPathDisorder N M
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let T := SmartPathState N M × (Fin 2 → ℝ)
  let G (p : Ω × W) (a : R → T) := g p.1 (fun r => (a r).1)
  have hGm : Measurable fun p : (Ω × W) × (R → T) => G p.1 p.2 := by
    have hp : Measurable fun p : (Ω × W) × (R → T) =>
        ((p.1.1, fun r => (p.2 r).1) : Ω × (R → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have h := hg.comp hp
    exact h
  exact integral_pi_cavity_rotation_eq_integral_cavity_extended hu hD t q s variance hGm

private lemma cavity_overlap_moment_split_eq_s
    {N M : ℕ}
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t q s p₂ : ℝ) (variance : ℝ≥0) :
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
    let S (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ) (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) + Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let ν (p : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) :=
      ((μ₀ p.1).prod γ_aux).tilted fun x => u (S p.2 x)
    let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let νfull (p : SmartPathDisorder N (M + 1) × ℝ) :=
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) +
            u (Real.cos s * smartPathField t p.1 x.1 (Fin.last M) +
              Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))
    let d_spin (σ τ : PerceptronSpin N) : ℝ :=
      |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
    ∫ p, ∫ a : Fin 2 → SmartPathState N M × (Fin 2 → ℝ),
        d_spin (a 0).1.1 (a 1).1.1 ^ p₂ ∂(Measure.pi fun _ => ν p) ∂(P₀.prod γ_sh) =
      ∫ p, ∫ a : Fin 2 → SmartPathState N (M + 1) × ℝ,
        d_spin (a 0).1.1 (a 1).1.1 ^ p₂ ∂(Measure.pi fun _ => νfull p) ∂Pfull := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S ν Pfull νfull d_spin
  let g (_ : SmartPathDisorder N M) (a : Fin 2 → SmartPathState N M) : ℝ :=
    d_spin (a 0).1 (a 1).1 ^ p₂
  have hg :
      Measurable fun p : SmartPathDisorder N M × (Fin 2 → SmartPathState N M) => g p.1 p.2 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2 ^ p₂
    have hproj : Measurable fun p : SmartPathDisorder N M × (Fin 2 → SmartPathState N M) =>
        ((p.2 0).1, (p.2 1).1) :=
      (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
        (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))
    have hb := (measurable_of_finite b).comp hproj
    exact hb
  have h := cavity_moment_split_eq_s (R := Fin 2) hu hD t q s variance (g := g) hg
  exact h

/-- **Change of variables from angle `s` to `v = cos² s` on `(0, 1)`.** -/
theorem hasDerivAt_cavity_v_of_angle
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (t q : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) (variance : ℝ≥0)
    (ψ : R → ℝ → ℝ) (hψm : ∀ r, Measurable (ψ r))
    {M₀ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2) :
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
    let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
        (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
      Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
        Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
    let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∀ {z : ℝ},
    HasDerivAt
      (fun s => ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S s w x)))
          ∂γ_sh ∂P₀)
      (Real.sin (Real.arccos (Real.sqrt v)) * Real.cos (Real.arccos (Real.sqrt v)) * z)
      (Real.arccos (Real.sqrt v)) →
    HasDerivAt
      (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2)) * ∏ r, ψ r (S_v v' p (a r))
        ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
      (-z / 2) v := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S Pfull S_v νfull hfi hfi₁ z hderiv
  have hcomp := HasDerivAt.comp_arccos_sqrt_of_sin_cos hv.1 hv.2 hderiv
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hv] with v' hv'
  rw [integral_integral_pi_cavity_rotation_eq_extended hu t q (Real.arccos (Real.sqrt v'))
    variance ψ hψm hM₀ hf hfi hfi₁]
  have hsq_le : Real.sqrt v' ≤ 1 := Real.sqrt_le_one.2 hv'.2.le
  have hcos : Real.cos (Real.arccos (Real.sqrt v')) = Real.sqrt v' :=
    Real.cos_arccos (by linarith [Real.sqrt_nonneg v']) hsq_le
  have hsin : Real.sin (Real.arccos (Real.sqrt v')) = Real.sqrt (1 - v') := by
    rw [Real.sin_arccos, Real.sq_sqrt hv'.1.le]
  simp only [S_v, νfull, hcos, hsin]
  rfl

/-- **General factor bound in `v`-coordinates (interior Hölder exponents).** -/
theorem exists_hasDerivAt_cavity_v_abs_le_holder_psi
    {N M : ℕ} {R : Type uR} [Fintype R]
    {t q v : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
    {p₁ p₂ : ℝ} (hp : p₁.HolderConjugate p₂) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
        (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
      Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
        Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
    let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
    let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
        (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
      f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
        (fun r => ((a r).1.1, Fin.init (a r).1.2))
    let d_spin (σ τ : PerceptronSpin N) : ℝ :=
      |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ᵐ ω ∂P₀, Integrable (fun a => |f ω a| ^ p₁) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ^ p₁ ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∃ d',
      HasDerivAt
        (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
            f_ext p a * ∏ r, ψ r (S_v v' p (a r))
          ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
        d' v ∧
      |d'| ≤ (1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)) *
        ((∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
            |f_ext p a| ^ p₁ ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) ^ (1 / p₁) *
          (∫ p, ∫ a : Fin 2 → SmartPathState N (M + 1) × ℝ,
            d_spin (a 0).1.1 (a 1).1.1 ^ p₂
            ∂(Measure.pi fun _ : Fin 2 => νfull v p) ∂Pfull) ^ (1 / p₂) +
          1 / (N + 1) *
            ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
              |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  intro P₀ μ₀ Pfull S_v νfull f_ext d_spin n L hfp hfp₁
  have hP₀ : IsProbabilityMeasure P₀ := by
    dsimp [P₀]
    rw [smartPathDisorder_eq]
    infer_instance
  have hμ₀ (ω : SmartPathDisorder N M) : IsProbabilityMeasure (μ₀ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  obtain ⟨hfi, hfi₁⟩ := integrable_pi_tilted_and_integrable_integral_abs_of_rpow P₀
    (μ := smartPathBase N M) (measurable_smartPathEnergy hu.measurable t) hf hp.lt.le hfp hfp₁
  let s₀ := Real.arccos (Real.sqrt v)
  obtain ⟨z, hz, hb⟩ := exists_hasDerivAt_cavity_rotation_abs_le_holder ht hq variance hu ψ
    hψd hψ₂d hM₀ hM₁ hM₂ hf s₀ hp hfp hfp₁
  have hv_deriv := hasDerivAt_cavity_v_of_angle hu.toSmartPathPotential t q hv variance ψ
    (fun r => (hψd r).continuous.measurable) hM₀ hf hfi hfi₁ hz
  have hcos : Real.cos s₀ = Real.sqrt v :=
    Real.cos_arccos (by linarith [Real.sqrt_nonneg v]) (Real.sqrt_le_one.2 hv.2.le)
  have hsin : Real.sin s₀ = Real.sqrt (1 - v) := by
    rw [Real.sin_arccos, Real.sq_sqrt hv.1.le]
  have hf_abs_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| := by simpa only [Real.norm_eq_abs] using hf.norm
  have hf_pow_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| ^ p₁ := hf_abs_m.pow_const p₁
  have hm1 := cavity_moment_split_eq_s hu.measurable (fun x => hu.le x) t q s₀ variance
    (g := fun ω a => |f ω a|) hf_abs_m
  have hmp := cavity_moment_split_eq_s hu.measurable (fun x => hu.le x) t q s₀ variance
    (g := fun ω a => |f ω a| ^ p₁) hf_pow_m
  have hmo := cavity_overlap_moment_split_eq_s (N := N) (M := M) hu.measurable (fun x => hu.le x)
    t q s₀ p₂ variance
  dsimp only at hm1 hmp hmo
  dsimp only at hb
  simp only [hcos, hsin] at hm1 hmp hmo hb
  refine ⟨-z / 2, hv_deriv, ?_⟩
  rw [abs_div, abs_neg, abs_two]
  have hb' := div_le_div_of_nonneg_right hb zero_le_two
  rw [hmp, hmo, hm1] at hb'
  exact hb'.trans_eq (by ring)

/-- **General factor bound in `v`-coordinates (`(1, ∞)` endpoint).** -/
theorem exists_hasDerivAt_cavity_v_abs_le_first_moment_psi
    {N M : ℕ} {R : Type uR} [Fintype R]
    {t q v : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
        (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
      Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
        Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
    let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
    let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
        (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
      f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
        (fun r => ((a r).1.1, Fin.init (a r).1.2))
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∃ d',
      HasDerivAt
        (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
            f_ext p a * ∏ r, ψ r (S_v v' p (a r))
          ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
        d' v ∧
      |d'| ≤ (1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)) *
        ((2 + 1 / (N + 1)) *
          ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
            |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  intro P₀ μ₀ Pfull S_v νfull f_ext n L hfi hfi₁
  let s₀ := Real.arccos (Real.sqrt v)
  obtain ⟨z, hz, hb⟩ := exists_hasDerivAt_cavity_rotation_abs_le_first_moment ht hq variance hu ψ
    hψd hψ₂d hM₀ hM₁ hM₂ hf s₀ hfi hfi₁
  have hv_deriv := hasDerivAt_cavity_v_of_angle hu.toSmartPathPotential t q hv variance ψ
    (fun r => (hψd r).continuous.measurable) hM₀ hf hfi hfi₁ hz
  have hcos : Real.cos s₀ = Real.sqrt v :=
    Real.cos_arccos (by linarith [Real.sqrt_nonneg v]) (Real.sqrt_le_one.2 hv.2.le)
  have hsin : Real.sin s₀ = Real.sqrt (1 - v) := by
    rw [Real.sin_arccos, Real.sq_sqrt hv.1.le]
  have hf_abs_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| := by simpa only [Real.norm_eq_abs] using hf.norm
  have hm1 := cavity_moment_split_eq_s hu.measurable (fun x => hu.le x) t q s₀ variance
    (g := fun ω a => |f ω a|) hf_abs_m
  dsimp only at hm1
  dsimp only at hb
  simp only [hcos, hsin] at hm1 hb
  refine ⟨-z / 2, hv_deriv, ?_⟩
  rw [abs_div, abs_neg, abs_two]
  have hb' := div_le_div_of_nonneg_right hb zero_le_two
  rw [hm1] at hb'
  exact hb'.trans_eq (by ring)

/-- **General factor bound in `v`-coordinates (`(∞, 1)` endpoint).** -/
theorem exists_hasDerivAt_cavity_v_abs_le_of_ae_abs_le_psi
    {N M : ℕ} {R : Type uR} [Fintype R]
    {t q v : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
    {M_f : ℝ} (hMf : 0 ≤ M_f) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
    let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
        (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
      Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
        Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
    let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
    let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
        (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
      f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
        (fun r => ((a r).1.1, Fin.init (a r).1.2))
    let d_spin (σ τ : PerceptronSpin N) : ℝ :=
      |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ᵐ ω ∂P₀, ∀ᵐ a ∂(Measure.pi fun _ : R => μ₀ ω), |f ω a| ≤ M_f) →
    ∃ d',
      HasDerivAt
        (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
            f_ext p a * ∏ r, ψ r (S_v v' p (a r))
          ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
        d' v ∧
      |d'| ≤ (1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)) *
        (M_f * (∫ p, ∫ a : Fin 2 → SmartPathState N (M + 1) × ℝ,
            d_spin (a 0).1.1 (a 1).1.1 ∂(Measure.pi fun _ : Fin 2 => νfull v p) ∂Pfull) +
          1 / (N + 1) *
            ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
              |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  intro P₀ μ₀ Pfull S_v νfull f_ext d_spin n L hOld
  let s₀ := Real.arccos (Real.sqrt v)
  have hP₀ : IsProbabilityMeasure P₀ := by
    dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  have hμ : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have hfωm (ω : SmartPathDisorder N M) : Measurable (f ω) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hfi : ∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω) := by
    filter_upwards [hOld] with ω hω
    exact Integrable.of_bound (hfωm ω).aestronglyMeasurable M_f (by simpa using hω)
  have hf_abs_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| := by simpa only [Real.norm_eq_abs] using hf.norm
  have hOld₁ := measurable_integral_pi_tilted (μ := smartPathBase N M)
    (E := fun ω => smartPathEnergy u t ω) (G := fun ω a => |f ω a|)
    (measurable_smartPathEnergy hu.measurable t) hf_abs_m
  have hfi₁ : Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ := by
    refine Integrable.of_bound hOld₁.aestronglyMeasurable M_f ?_
    filter_upwards [hOld] with ω hω
    have hω' : ∀ᵐ a ∂(Measure.pi fun _ : R => μ₀ ω), ‖|f ω a|‖ ≤ M_f := by
      simpa only [Real.norm_eq_abs, abs_abs] using hω
    simpa using norm_integral_le_of_norm_le_const hω'
  obtain ⟨z, hz, hb⟩ := exists_hasDerivAt_cavity_rotation_abs_le_of_ae_abs_le ht hq variance hu ψ
    hψd hψ₂d hM₀ hM₁ hM₂ hf s₀ hMf hOld
  have hv_deriv := hasDerivAt_cavity_v_of_angle hu.toSmartPathPotential t q hv variance ψ
    (fun r => (hψd r).continuous.measurable) hM₀ hf hfi hfi₁ hz
  have hcos : Real.cos s₀ = Real.sqrt v :=
    Real.cos_arccos (by linarith [Real.sqrt_nonneg v]) (Real.sqrt_le_one.2 hv.2.le)
  have hsin : Real.sin s₀ = Real.sqrt (1 - v) := by
    rw [Real.sin_arccos, Real.sq_sqrt hv.1.le]
  have hm1 := cavity_moment_split_eq_s hu.measurable (fun x => hu.le x) t q s₀ variance
    (g := fun ω a => |f ω a|) hf_abs_m
  have hmo := cavity_overlap_moment_split_eq_s (N := N) (M := M) hu.measurable (fun x => hu.le x)
    t q s₀ 1 variance
  dsimp only at hm1 hmo
  dsimp only at hb
  simp only [hcos, hsin, Real.rpow_one] at hm1 hmo hb
  refine ⟨-z / 2, hv_deriv, ?_⟩
  rw [abs_div, abs_neg, abs_two]
  have hb' := div_le_div_of_nonneg_right hb zero_le_two
  rw [hmo, hm1] at hb'
  exact hb'.trans_eq (by ring)

/-! ### Source-facing Lemma 2.3.2, Eq. (2.40) -/

/-- **Lemma 2.3.2, Eq. (2.40), unweighted (`B_v ≡ 1`), interior Hölder exponents.**
Under (2.7), there exists a constant `K ≥ 0` depending only on `|R|` and `D` (chosen before
`N, M, t, q, v, variance, u, f, p₁, p₂`) such that for every `t, q ∈ [0, 1]`, `v ∈ (0, 1)` and
conjugate `p₁, p₂`, `|d/dv ν_{t,v}(f)|` is bounded by `K` times the Hölder pair moment plus the
`1/(N + 1)` first-moment term. -/
theorem exists_hasDerivAt_cavity_v_unweighted_holder
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q v : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (_hv : v ∈ Set.Ioo (0 : ℝ) 1) (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
        {p₁ p₂ : ℝ} (_hp : p₁.HolderConjugate p₂),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
        let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
            (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
          Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
            Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
        let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
          ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
            fun x : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
                (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
        let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
            (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2))
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        (∀ᵐ ω ∂P₀, Integrable (fun a => |f ω a| ^ p₁) (Measure.pi fun _ : R => μ₀ ω)) →
        Integrable (fun ω => ∫ a, |f ω a| ^ p₁ ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
        ∃ d',
          HasDerivAt
            (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ, f_ext p a
              ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
            d' v ∧
          |d'| ≤ K *
            ((∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                |f_ext p a| ^ p₁ ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) ^ (1 / p₁) *
              (∫ p, ∫ a : Fin 2 → SmartPathState N (M + 1) × ℝ,
                d_spin (a 0).1.1 (a 1).1.1 ^ p₂
                ∂(Measure.pi fun _ : Fin 2 => νfull v p) ∂Pfull) ^ (1 / p₂) +
              1 / (N + 1) *
                ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                  |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  let n : ℝ := Fintype.card R
  let L : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  refine ⟨(1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)), by positivity, ?_⟩
  intro N M t q v ht hq hv variance u hd hb f hf p₁ p₂ hp P₀ μ₀ Pfull S_v νfull f_ext d_spin
    hfp hfp₁
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨d', hd', hbd⟩ := exists_hasDerivAt_cavity_v_abs_le_holder_psi ht hq hv variance hu
    (fun _ => fun _ => 1) (fun _ => differentiable_const 1)
    (fun _ => by simp) (M₀ := 1) (M₁ := 0) (M₂ := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    hf hp hfp hfp₁
  refine ⟨d', ?_, hbd⟩
  simpa only [Finset.prod_const_one, mul_one] using hd'

/-- **Lemma 2.3.2, Eq. (2.40), unweighted (`B_v ≡ 1`), `(1, ∞)` endpoint.** -/
theorem exists_hasDerivAt_cavity_v_unweighted_first_moment
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q v : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (_hv : v ∈ Set.Ioo (0 : ℝ) 1) (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
        let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
            (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
          Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
            Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
        let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
          ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
            fun x : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
                (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
        let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
            (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2))
        (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
        Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
        ∃ d',
          HasDerivAt
            (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ, f_ext p a
              ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
            d' v ∧
          |d'| ≤ K * ((2 + 1 / (N + 1)) *
            ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
              |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  let n : ℝ := Fintype.card R
  let L : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  refine ⟨(1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)), by positivity, ?_⟩
  intro N M t q v ht hq hv variance u hd hb f hf P₀ μ₀ Pfull S_v νfull f_ext hfi hfi₁
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨d', hd', hbd⟩ := exists_hasDerivAt_cavity_v_abs_le_first_moment_psi ht hq hv variance hu
    (fun _ => fun _ => 1) (fun _ => differentiable_const 1)
    (fun _ => by simp) (M₀ := 1) (M₁ := 0) (M₂ := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    hf hfi hfi₁
  refine ⟨d', ?_, hbd⟩
  simpa only [Finset.prod_const_one, mul_one] using hd'

/-- **Lemma 2.3.2, Eq. (2.40), unweighted (`B_v ≡ 1`), `(∞, 1)` endpoint.** -/
theorem exists_hasDerivAt_cavity_v_unweighted_of_ae_abs_le
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {t q v : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (_hv : v ∈ Set.Ioo (0 : ℝ) 1) (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
        {M_f : ℝ} (_hMf : 0 ≤ M_f),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
        let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
            (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
          Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
            Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
        let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
          ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
            fun x : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
                (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
        let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
            (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2))
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        (∀ᵐ ω ∂P₀, ∀ᵐ a ∂(Measure.pi fun _ : R => μ₀ ω), |f ω a| ≤ M_f) →
        ∃ d',
          HasDerivAt
            (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ, f_ext p a
              ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
            d' v ∧
          |d'| ≤ K *
            (M_f * (∫ p, ∫ a : Fin 2 → SmartPathState N (M + 1) × ℝ,
                d_spin (a 0).1.1 (a 1).1.1 ∂(Measure.pi fun _ : Fin 2 => νfull v p) ∂Pfull) +
              1 / (N + 1) *
                ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                  |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  let n : ℝ := Fintype.card R
  let L : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  refine ⟨(1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)), by positivity, ?_⟩
  intro N M t q v ht hq hv variance u hd hb f hf M_f hMf P₀ μ₀ Pfull S_v νfull f_ext d_spin hOld
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  obtain ⟨d', hd', hbd⟩ := exists_hasDerivAt_cavity_v_abs_le_of_ae_abs_le_psi ht hq hv variance hu
    (fun _ => fun _ => 1) (fun _ => differentiable_const 1)
    (fun _ => by simp) (M₀ := 1) (M₁ := 0) (M₂ := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    hf hMf hOld
  refine ⟨d', ?_, hbd⟩
  simpa only [Finset.prod_const_one, mul_one] using hd'

private lemma prod_two_marked_eq
    {R : Type uR} [Fintype R] [DecidableEq R] {r₁ r₂ : R} (hr : r₁ ≠ r₂)
    (g : ℝ → ℝ) (x : R → ℝ) :
    (∏ r : R, (if r = r₁ ∨ r = r₂ then g (x r) else 1)) = g (x r₁) * g (x r₂) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r₁)]
  have hmem : r₂ ∈ Finset.univ.erase r₁ := Finset.mem_erase.2 ⟨hr.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ hmem]
  have her : ∏ r ∈ (Finset.univ.erase r₁).erase r₂, (if r = r₁ ∨ r = r₂ then g (x r) else 1) = 1 :=
    Finset.prod_eq_one fun r hr' => by
      have hne2 : r ≠ r₂ := Finset.ne_of_mem_erase hr'
      have hne1 : r ≠ r₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr')
      simp [hne1, hne2]
  rw [her, mul_one]
  simp

/-- **Lemma 2.3.2, Eq. (2.40), weighted (`B_v = u'(S_v^{r₁}) u'(S_v^{r₂})`), interior Hölder
exponents.** For two distinct replicas `r₁ ≠ r₂`, existence and boundedness of `u'''` from (2.7)
supply the bounds on the moving factors `ψ_{r₁} = ψ_{r₂} = u'`, and `K` is chosen from `|R|` and
`D` alone. -/
theorem exists_hasDerivAt_cavity_v_deriv_mul_holder
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {t q v : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (_hv : v ∈ Set.Ioo (0 : ℝ) 1) (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
        {p₁ p₂ : ℝ} (_hp : p₁.HolderConjugate p₂),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
        let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
            (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
          Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
            Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
        let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
          ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
            fun x : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
                (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
        let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
            (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2))
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        (∀ᵐ ω ∂P₀, Integrable (fun a => |f ω a| ^ p₁) (Measure.pi fun _ : R => μ₀ ω)) →
        Integrable (fun ω => ∫ a, |f ω a| ^ p₁ ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
        ∃ d',
          HasDerivAt
            (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                f_ext p a * (deriv u (S_v v' p (a r₁)) * deriv u (S_v v' p (a r₂)))
              ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
            d' v ∧
          |d'| ≤ K *
            ((∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                |f_ext p a| ^ p₁ ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) ^ (1 / p₁) *
              (∫ p, ∫ a : Fin 2 → SmartPathState N (M + 1) × ℝ,
                d_spin (a 0).1.1 (a 1).1.1 ^ p₂
                ∂(Measure.pi fun _ : Fin 2 => νfull v p) ∂Pfull) ^ (1 / p₂) +
              1 / (N + 1) *
                ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                  |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  classical
  let n : ℝ := Fintype.card R
  let M₀ : ℝ := 1 + |D|
  let M₁ : ℝ := |D|
  let L : ℝ := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
  refine ⟨(1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)), by positivity, ?_⟩
  intro N M r₁ r₂ hr t q v ht hq hv variance u hd hb f hf p₁ p₂ hp P₀ μ₀ Pfull S_v νfull
    f_ext d_spin hfp hfp₁
  obtain ⟨hu, h2d, hb3⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let ψ (r : R) (x : ℝ) : ℝ := if r = r₁ ∨ r = r₂ then deriv u x else 1
  have hψd (r : R) : Differentiable ℝ (ψ r) := by
    dsimp only [ψ]; split_ifs; exacts [hu.differentiable_deriv, differentiable_const 1]
  have hψ₂d (r : R) : Differentiable ℝ (deriv (ψ r)) := by
    dsimp only [ψ]; split_ifs
    · exact h2d
    · simp
  have hM₀ (r : R) (x : ℝ) : |ψ r x| ≤ M₀ := by
    dsimp only [ψ, M₀]; split_ifs
    · linarith [hu.abs_deriv_le x, le_abs_self D, abs_nonneg D]
    · rw [abs_one]; linarith [abs_nonneg D]
  have hM₁ (r : R) (x : ℝ) : |deriv (ψ r) x| ≤ M₁ := by
    dsimp only [ψ, M₁]; split_ifs
    · exact (hu.abs_deriv₂_le x).trans (le_abs_self D)
    · simp [abs_nonneg D]
  have hM₂ (r : R) (x : ℝ) : |deriv (deriv (ψ r)) x| ≤ |D| := by
    dsimp only [ψ]; split_ifs
    · exact (hb3 x).trans (le_abs_self D)
    · simp [abs_nonneg D]
  obtain ⟨d', hd', hbd⟩ := exists_hasDerivAt_cavity_v_abs_le_holder_psi ht hq hv variance hu
    ψ hψd hψ₂d hM₀ hM₁ hM₂ hf hp hfp hfp₁
  refine ⟨d', hd'.congr_of_eventuallyEq (Eventually.of_forall fun v' => ?_), hbd⟩
  refine integral_congr_ae (ae_of_all _ fun p => integral_congr_ae (ae_of_all _ fun a => ?_))
  change f_ext p a * (deriv u (S_v v' p (a r₁)) * deriv u (S_v v' p (a r₂))) =
    f_ext p a * ∏ r : R, ψ r (S_v v' p (a r))
  symm
  congr 1
  have := prod_two_marked_eq hr (deriv u) (fun r => S_v v' p (a r))
  simpa only [ψ, apply_ite] using this

/-- **Lemma 2.3.2, Eq. (2.40), weighted (`B_v = u'(S_v^{r₁}) u'(S_v^{r₂})`), `(1, ∞)` endpoint.** -/
theorem exists_hasDerivAt_cavity_v_deriv_mul_first_moment
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {t q v : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (_hv : v ∈ Set.Ioo (0 : ℝ) 1) (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
        let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
            (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
          Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
            Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
        let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
          ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
            fun x : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
                (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
        let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
            (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2))
        (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
        Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
        ∃ d',
          HasDerivAt
            (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                f_ext p a * (deriv u (S_v v' p (a r₁)) * deriv u (S_v v' p (a r₂)))
              ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
            d' v ∧
          |d'| ≤ K * ((2 + 1 / (N + 1)) *
            ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
              |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  classical
  let n : ℝ := Fintype.card R
  let M₀ : ℝ := 1 + |D|
  let M₁ : ℝ := |D|
  let L : ℝ := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
  refine ⟨(1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)), by positivity, ?_⟩
  intro N M r₁ r₂ hr t q v ht hq hv variance u hd hb f hf P₀ μ₀ Pfull S_v νfull f_ext hfi hfi₁
  obtain ⟨hu, h2d, hb3⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let ψ (r : R) (x : ℝ) : ℝ := if r = r₁ ∨ r = r₂ then deriv u x else 1
  have hψd (r : R) : Differentiable ℝ (ψ r) := by
    dsimp only [ψ]; split_ifs; exacts [hu.differentiable_deriv, differentiable_const 1]
  have hψ₂d (r : R) : Differentiable ℝ (deriv (ψ r)) := by
    dsimp only [ψ]; split_ifs
    · exact h2d
    · simp
  have hM₀ (r : R) (x : ℝ) : |ψ r x| ≤ M₀ := by
    dsimp only [ψ, M₀]; split_ifs
    · linarith [hu.abs_deriv_le x, le_abs_self D, abs_nonneg D]
    · rw [abs_one]; linarith [abs_nonneg D]
  have hM₁ (r : R) (x : ℝ) : |deriv (ψ r) x| ≤ M₁ := by
    dsimp only [ψ, M₁]; split_ifs
    · exact (hu.abs_deriv₂_le x).trans (le_abs_self D)
    · simp [abs_nonneg D]
  have hM₂ (r : R) (x : ℝ) : |deriv (deriv (ψ r)) x| ≤ |D| := by
    dsimp only [ψ]; split_ifs
    · exact (hb3 x).trans (le_abs_self D)
    · simp [abs_nonneg D]
  obtain ⟨d', hd', hbd⟩ := exists_hasDerivAt_cavity_v_abs_le_first_moment_psi ht hq hv variance hu
    ψ hψd hψ₂d hM₀ hM₁ hM₂ hf hfi hfi₁
  refine ⟨d', hd'.congr_of_eventuallyEq (Eventually.of_forall fun v' => ?_), hbd⟩
  refine integral_congr_ae (ae_of_all _ fun p => integral_congr_ae (ae_of_all _ fun a => ?_))
  change f_ext p a * (deriv u (S_v v' p (a r₁)) * deriv u (S_v v' p (a r₂))) =
    f_ext p a * ∏ r : R, ψ r (S_v v' p (a r))
  symm
  congr 1
  have := prod_two_marked_eq hr (deriv u) (fun r => S_v v' p (a r))
  simpa only [ψ, apply_ite] using this

/-- **Lemma 2.3.2, Eq. (2.40), weighted (`B_v = u'(S_v^{r₁}) u'(S_v^{r₂})`), `(∞, 1)` endpoint.** -/
theorem exists_hasDerivAt_cavity_v_deriv_mul_of_ae_abs_le
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {t q v : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (_hv : v ∈ Set.Ioo (0 : ℝ) 1) (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
        {M_f : ℝ} (_hMf : 0 ≤ M_f),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let Pfull := (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance).prod (gaussianReal 0 1)
        let S_v (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ)
            (x : SmartPathState N (M + 1) × ℝ) : ℝ :=
          Real.sqrt v' * smartPathField t p.1 x.1 (Fin.last M) +
            Real.sqrt (1 - v') * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)
        let νfull (v' : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) :=
          ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
            fun x : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
                (x.1.1, Fin.init x.1.2) + u (S_v v' p x)
        let f_ext (p : SmartPathDisorder N (M + 1) × ℝ)
            (a : R → SmartPathState N (M + 1) × ℝ) : ℝ :=
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2))
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        (∀ᵐ ω ∂P₀, ∀ᵐ a ∂(Measure.pi fun _ : R => μ₀ ω), |f ω a| ≤ M_f) →
        ∃ d',
          HasDerivAt
            (fun v' => ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                f_ext p a * (deriv u (S_v v' p (a r₁)) * deriv u (S_v v' p (a r₂)))
              ∂(Measure.pi fun _ : R => νfull v' p) ∂Pfull)
            d' v ∧
          |d'| ≤ K *
            (M_f * (∫ p, ∫ a : Fin 2 → SmartPathState N (M + 1) × ℝ,
                d_spin (a 0).1.1 (a 1).1.1 ∂(Measure.pi fun _ : Fin 2 => νfull v p) ∂Pfull) +
              1 / (N + 1) *
                ∫ p, ∫ a : R → SmartPathState N (M + 1) × ℝ,
                  |f_ext p a| ∂(Measure.pi fun _ : R => νfull v p) ∂Pfull) := by
  classical
  let n : ℝ := Fintype.card R
  let M₀ : ℝ := 1 + |D|
  let M₁ : ℝ := |D|
  let L : ℝ := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
  refine ⟨(1 / 2) * ((4 * n ^ 2 + n) * L ^ (Fintype.card R + 2)), by positivity, ?_⟩
  intro N M r₁ r₂ hr t q v ht hq hv variance u hd hb f hf M_f hMf P₀ μ₀ Pfull S_v νfull
    f_ext d_spin hOld
  obtain ⟨hu, h2d, hb3⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let ψ (r : R) (x : ℝ) : ℝ := if r = r₁ ∨ r = r₂ then deriv u x else 1
  have hψd (r : R) : Differentiable ℝ (ψ r) := by
    dsimp only [ψ]; split_ifs; exacts [hu.differentiable_deriv, differentiable_const 1]
  have hψ₂d (r : R) : Differentiable ℝ (deriv (ψ r)) := by
    dsimp only [ψ]; split_ifs
    · exact h2d
    · simp
  have hM₀ (r : R) (x : ℝ) : |ψ r x| ≤ M₀ := by
    dsimp only [ψ, M₀]; split_ifs
    · linarith [hu.abs_deriv_le x, le_abs_self D, abs_nonneg D]
    · rw [abs_one]; linarith [abs_nonneg D]
  have hM₁ (r : R) (x : ℝ) : |deriv (ψ r) x| ≤ M₁ := by
    dsimp only [ψ, M₁]; split_ifs
    · exact (hu.abs_deriv₂_le x).trans (le_abs_self D)
    · simp [abs_nonneg D]
  have hM₂ (r : R) (x : ℝ) : |deriv (deriv (ψ r)) x| ≤ |D| := by
    dsimp only [ψ]; split_ifs
    · exact (hb3 x).trans (le_abs_self D)
    · simp [abs_nonneg D]
  obtain ⟨d', hd', hbd⟩ := exists_hasDerivAt_cavity_v_abs_le_of_ae_abs_le_psi ht hq hv variance hu
    ψ hψd hψ₂d hM₀ hM₁ hM₂ hf hMf hOld
  refine ⟨d', hd'.congr_of_eventuallyEq (Eventually.of_forall fun v' => ?_), hbd⟩
  refine integral_congr_ae (ae_of_all _ fun p => integral_congr_ae (ae_of_all _ fun a => ?_))
  change f_ext p a * (deriv u (S_v v' p (a r₁)) * deriv u (S_v v' p (a r₂))) =
    f_ext p a * ∏ r : R, ψ r (S_v v' p (a r))
  symm
  congr 1
  have := prod_two_marked_eq hr (deriv u) (fun r => S_v v' p (a r))
  simpa only [ψ, apply_ite] using this

end SpinGlasses
