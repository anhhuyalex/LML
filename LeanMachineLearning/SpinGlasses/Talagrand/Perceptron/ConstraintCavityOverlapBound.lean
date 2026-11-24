/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import
  LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityRotationDerivative
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaPairBound

/-!
# Pair-moment bound for the split constraint cavity rotation

The four derivative groups have a common bound in terms of the mixed overlap moment and the
first moment. The moment bound comes from Hölder after combining the two disorder averages.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace SpinGlasses

universe v

private theorem measurable_pair_comp {α L : Type*} [MeasurableSpace α] [MeasurableSpace L]
    [Finite L] [MeasurableSingletonClass L] {π : α → L} (hπ : Measurable π) (d : L → L → ℝ) :
    Measurable (fun p : α × α => d (π p.1) (π p.2)) :=
  (measurable_of_finite (fun p : L × L => d p.1 p.2)).comp
    ((hπ.comp measurable_fst).prodMk (hπ.comp measurable_snd))

/-- A bounded change of the cavity energy preserves an old observable's integrable
sections and disorder-averaged absolute first moment. Applying it to a power of the
observable gives the corresponding moment transfer. -/
theorem integrable_integral_pi_cavity_rotation_abs
    {N M : ℕ} {R : Type v} [Fintype R] (t q s₀ : ℝ)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
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
    let Ω := SmartPathDisorder N M
    let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
    let T := SmartPathState N M × (Fin 2 → ℝ)
    let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted fun x => u (S s₀ p.2 x)
    let F (p : Ω × W) (a : R → T) := f p.1 (fun r => (a r).1)
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    (∀ᵐ p ∂P₀.prod γ_sh, Integrable (F p) (Measure.pi fun _ : R => ν p)) ∧
      Integrable (fun p => ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p)) (P₀.prod γ_sh) := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S Ω W T ν F hfi hfi₁
  let n : ℝ := Fintype.card R
  have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s₀
  have hV (p : Ω × W) : Measurable fun x : T => u (S s₀ p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have hs := hS.comp hp
    have h := hu.measurable.comp hs
    exact h
  have hμ : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hu.le _)
  let P := P₀.prod γ_sh
  have hfm :
      Measurable fun x : (Ω × W) × (R → T) => F x.1 x.2 := by
    have hp : Measurable fun x : (Ω × W) × (R → T) =>
        ((x.1.1, fun r => (x.2 r).1) : Ω × (R → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have h := hf.comp hp
    exact h
  have hfm_abs : Measurable fun x : (Ω × W) × (R → T) => |F x.1 x.2| := by
    simpa only [Real.norm_eq_abs] using hfm.norm
  have hlift : ∀ᵐ p ∂P,
      Integrable (fun a => |F p a|) (Measure.pi fun _ : R => ν p) ∧
        (∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p)) ≤
          Real.exp (2 * n * B) * ∫ a, |f p.1 a| ∂(Measure.pi fun _ : R => μ₀ p.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := P₀) (ν := γ_sh)).ae hfi |>.mono fun p hp =>
      integrable_pi_tilted_prod_fst_abs_and_le (μ₀ p.1) γ_aux (hV p) (fun x => hu.abs_le _)
        Function.injective_id hp
  have hFI : ∀ᵐ p ∂P, Integrable (F p) (Measure.pi fun _ : R => ν p) := hlift.mono fun p hp => by
    have hm : Measurable fun a : R → T => (p, a) := measurable_const.prodMk measurable_id
    have hpF : Measurable (F p) := hfm.comp hm
    exact (integrable_norm_iff hpF.aestronglyMeasurable).1
      (by simpa only [Real.norm_eq_abs] using hp.1)
  have hF₁ : Integrable (fun p => ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p)) P := by
    have hI := (hfi₁.comp_fst γ_sh).const_mul (Real.exp (2 * n * B))
    have hAm := measurable_integral_pi_cavity_rotation t q s₀ hu.measurable (fun x => hu.le x)
      (F := fun p a => |F p a|) hfm_abs
    refine hI.mono' hAm.aestronglyMeasurable (hlift.mono fun p hp => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun a => abs_nonneg _)]
    exact hp.2
  exact ⟨hFI, hF₁⟩

/-- The split-cavity angle derivative is bounded by a uniform mixed pair moment and a first
moment correction. The finite-replica multiplier is independent of the spin and row counts. -/
theorem exists_hasDerivAt_cavity_rotation_abs_le_of_pair_bound
    {N M : ℕ} {R : Type v} [Fintype R]
    {t q : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
    (s₀ : ℝ) {m : ℝ} (hm : 0 ≤ m) :
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
    let Ω := SmartPathDisorder N M
    let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
    let T := SmartPathState N M × (Fin 2 → ℝ)
    let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted fun x => u (S s₀ p.2 x)
    let F (p : Ω × W) (a : R → T) := f p.1 (fun r => (a r).1)
    let d (a b : T) :=
      |((∑ i, ((a.1.1.1 i : ℤ) : ℝ) * ((b.1.1.1 i : ℤ) : ℝ)) +
        ((a.1.1.2 : ℤ) : ℝ) * ((b.1.1.2 : ℤ) : ℝ)) / (N + 1) - q|
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    (∀ (ι : Type v) [Fintype ι] (e : R → ι), Function.Injective e → ∀ i j, i ≠ j →
      ∫ p, ∫ a : ι → T, |F p (a ∘ e)| * d (a i) (a j)
        ∂(Measure.pi fun _ : ι => ν p) ∂(P₀.prod γ_sh) ≤ m) →
    ∃ z,
      HasDerivAt
      (fun s => ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))
          ∂γ_sh ∂P₀)
        (Real.sin s₀ * Real.cos s₀ * z) s₀ ∧
      |z| ≤ (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) *
        (m + 1 / (N + 1) *
          ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂(P₀.prod γ_sh)) := by
  classical
  intro P₀ μ₀ γ_sh γ_aux X Y A E S Ω W T ν F d n L hfi hfi₁ hpair
  let C_cov (σ τ : PerceptronSpin N) := Y ⬝ᵥ Y - X σ ⬝ᵥ X τ
  have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s₀
  have hV (p : Ω × W) : Measurable fun x : T => u (S s₀ p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have hs := hS.comp hp
    have h := hu.measurable.comp hs
    exact h
  have hμ : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hu.le _)
  let P := P₀.prod γ_sh
  have hfm {ι : Type v} (e : R → ι) :
      Measurable fun x : (Ω × W) × (ι → T) => F x.1 (x.2 ∘ e) := by
    have hp : Measurable fun x : (Ω × W) × (ι → T) =>
        ((x.1.1, fun r => (x.2 (e r)).1) : Ω × (R → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply (e r)).comp measurable_snd))
    have h := hf.comp hp
    exact h
  have hfm_abs {ι : Type v} (e : R → ι) :
      Measurable fun x : (Ω × W) × (ι → T) => |F x.1 (x.2 ∘ e)| := by
    simpa only [Real.norm_eq_abs] using (hfm e).norm
  have hmν {ι : Type v} [Fintype ι] {G : Ω × W → (ι → T) → ℝ}
      (hG : Measurable fun p : (Ω × W) × (ι → T) => G p.1 p.2) :
      Measurable fun p => ∫ a, G p a ∂(Measure.pi fun _ : ι => ν p) :=
    measurable_integral_pi_cavity_rotation t q s₀ hu.measurable (fun x => hu.le x) hG
  obtain ⟨hFI, hF₁⟩ :=
    integrable_integral_pi_cavity_rotation_abs t q s₀ variance hu.toSmartPathPotential hf hfi hfi₁
  let ε : ℝ := 1 / (N + 1)
  let c (a b : T) := C_cov a.1.1 b.1.1
  obtain ⟨_, _, _, _, hcov⟩ := cavity_rotation_dotProducts (N := N) ht hq
  have hc (a b : T) : |c a b| ≤ d a b + ε := by
    change |C_cov a.1.1 b.1.1| ≤ d a b + ε
    rw [show C_cov a.1.1 b.1.1 = q - cavityCoef N t a.1.1 ⬝ᵥ cavityCoef N t b.1.1
      from hcov _ _]
    exact abs_sub_cavityCoef_dotProduct_le ht q _ _
  have hd (a b : T) : d a b ≤ 2 := abs_perceptron_overlap_sub_le_two hq _ _
  have hdm : Measurable fun p : T × T => d p.1 p.2 :=
    measurable_pair_comp (π := fun a : T => a.1.1) (measurable_fst.comp measurable_fst)
      (fun a b => d ((a, 0), 0) ((b, 0), 0))
  have hcm : Measurable fun p : T × T => c p.1 p.2 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ :=
      fun p => C_cov p.1 p.2
    have hproj : Measurable fun p : T × T => (p.1.1.1, p.2.1.1) :=
      (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  let A₁ := ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂P
  let K := L ^ (Fintype.card R + 2)
  have hpos := mul_nonneg (abs_nonneg M₀) (abs_nonneg D)
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D]
  have hK : 0 ≤ K := pow_nonneg (zero_le_one.trans hL) _
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hA₁ : 0 ≤ A₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hTerm {ι : Type v} [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) (H : Ω × W → (ι → T) → ℝ)
      (hHm : Measurable fun x : (Ω × W) × (ι → T) => H x.1 x.2)
      (hHb : ∀ p a, |H p a| ≤ K) :
      let J (ω : Ω) := ∫ w, ∫ a : ι → T, F (ω, w) (a ∘ e) * c (a i) (a j) * H (ω, w) a
        ∂(Measure.pi fun _ : ι => ν (ω, w)) ∂γ_sh
      Integrable J P₀ ∧ |∫ ω, J ω ∂P₀| ≤ K * (m + ε * A₁) := by
    have hp : Measurable fun x : (Ω × W) × (ι → T) => (x.2 i, x.2 j) :=
      ((measurable_pi_apply i).comp measurable_snd).prodMk
        ((measurable_pi_apply j).comp measurable_snd)
    have hMm := (hfm_abs e).mul (hdm.comp hp)
    have hTm := ((hfm e).mul (hcm.comp hp)).mul hHm
    have hM := hmν (G := fun p a => |F p (a ∘ e)| * d (a i) (a j)) hMm
    have hT := hmν (G := fun p a => F p (a ∘ e) * c (a i) (a j) * H p a) hTm
    exact integrable_integral_pi_pair_mul_and_abs_le P₀ γ_sh ν he i j hFI hF₁ hdm
      (fun _ _ => abs_nonneg _) hd hε c hc H hK hHb hM.aestronglyMeasurable
      hT.aestronglyMeasurable (hpair ι e he i j hij)
  let ψ_d (r : R) (x : ℝ) := deriv (ψ r) x + ψ r x * deriv u x
  have hψm (r : R) : Measurable (ψ r) := (hψd r).continuous.measurable
  have hψdm (r : R) : Measurable (ψ_d r) :=
    (measurable_deriv _).add ((hψm r).mul (measurable_deriv _))
  have hψb (r : R) (x : ℝ) : |ψ r x| ≤ L :=
    (hM₀ r x).trans ((le_abs_self _).trans (by
      dsimp only [L]
      linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D]))
  have hbDu (x : ℝ) : |deriv u x| ≤ L :=
    (hu.abs_deriv_le x).trans ((le_abs_self _).trans (by
      dsimp only [L]
      linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D]))
  have hψdb (r : R) (x : ℝ) : |ψ_d r x| ≤ L := by
    have hh : |ψ r x * deriv u x| ≤ |M₀| * |D| := by
      rw [abs_mul]
      exact mul_le_mul ((hM₀ _ _).trans (le_abs_self _))
        ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
    exact (abs_add_le _ _).trans ((add_le_add ((hM₁ _ _).trans (le_abs_self _)) hh).trans
      (by
      dsimp only [L]
      linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D]))
  have hfield {ι : Type v} (i : ι) :
      Measurable fun x : (Ω × W) × (ι → T) => S s₀ x.1.2 (x.2 i) := by
    have hp : Measurable fun x : (Ω × W) × (ι → T) => (x.1.2, x.2 i) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
    have h := hS.comp hp
    exact h
  have hprod {ι : Type v} (e : R → ι) (U : Finset R) (p : Ω × W) (a : ι → T) :
      |∏ r ∈ U, ψ r (S s₀ p.2 (a (e r)))| ≤ L ^ Fintype.card R := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _r ∈ U, L :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψb r _
      _ = L ^ U.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ hL (Finset.card_le_univ U)
  have hprod_m {ι : Type v} (e : R → ι) (U : Finset R) :
      Measurable fun x : (Ω × W) × (ι → T) => ∏ r ∈ U, ψ r (S s₀ x.1.2 (x.2 (e r))) := by
    refine Finset.measurable_prod _ fun r _ => ?_
    have h := (hψm r).comp (hfield (e r))
    exact h
  have hthree (a b g : ℝ) (ha : |a| ≤ L) (hb : |b| ≤ L)
      (hg : |g| ≤ L ^ Fintype.card R) : |a * b * g| ≤ K := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ L * L * L ^ Fintype.card R :=
        mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (zero_le_one.trans hL)) hg
          (abs_nonneg _) (mul_nonneg (zero_le_one.trans hL) (zero_le_one.trans hL))
      _ = K := by dsimp only [K]; rw [pow_add, pow_two]; ring
  let e₁ : R → Option R := some
  let e₂ : R → Option (Option R) := fun i => some (some i)
  have he₁ : Function.Injective e₁ := Option.some_injective _
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp he₁
  let G₀ (i j : R) (p : Ω × W) (a : R → T) :=
    ψ_d i (S s₀ p.2 (a i)) * ψ_d j (S s₀ p.2 (a j)) *
      ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s₀ p.2 (a r))
  let G₁ (i : R) (p : Ω × W) (a : Option R → T) :=
    (ψ_d i (S s₀ p.2 (a (some i))) *
      ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ p.2 (a (some r)))) *
      deriv u (S s₀ p.2 (a none))
  let G₂ (p : Ω × W) (a : Option (Option R) → T) :=
    (∏ r, ψ r (S s₀ p.2 (a (some (some r))))) *
      deriv u (S s₀ p.2 (a (some none))) * deriv u (S s₀ p.2 (a none))
  have hm₀ (i j : R) : Measurable fun x : (Ω × W) × (R → T) => G₀ i j x.1 x.2 := by
    have hi := (hψdm i).comp (hfield i)
    have hj := (hψdm j).comp (hfield j)
    exact (hi.mul hj).mul (hprod_m id _)
  have hm₁ (i : R) : Measurable fun x : (Ω × W) × (Option R → T) => G₁ i x.1 x.2 := by
    have hi := (hψdm i).comp (hfield (some i))
    have hnew := (measurable_deriv u).comp (hfield (none : Option R))
    exact (hi.mul (hprod_m e₁ _)).mul hnew
  have hm₂ : Measurable fun x : (Ω × W) × (Option (Option R) → T) => G₂ x.1 x.2 := by
    have hi := (measurable_deriv u).comp (hfield (some (none : Option R)))
    have hj := (measurable_deriv u).comp (hfield (none : Option (Option R)))
    exact ((hprod_m e₂ Finset.univ).mul hi).mul hj
  have hb₀ (i j : R) (p : Ω × W) (a : R → T) : |G₀ i j p a| ≤ K :=
    hthree _ _ _ (hψdb _ _) (hψdb _ _) (hprod id _ p a)
  have hb₁ (i : R) (p : Ω × W) (a : Option R → T) : |G₁ i p a| ≤ K := by
    dsimp only [G₁]
    rw [mul_right_comm]
    exact hthree _ _ _ (hψdb _ _) (hbDu _) (hprod e₁ _ p a)
  have hb₂ (p : Ω × W) (a : Option (Option R) → T) : |G₂ p a| ≤ K := by
    let g := ∏ r, ψ r (S s₀ p.2 (a (some (some r))))
    let b := deriv u (S s₀ p.2 (a (some none)))
    let c' := deriv u (S s₀ p.2 (a none))
    change |g * b * c'| ≤ K
    rw [show g * b * c' = b * c' * g by ring]
    exact hthree _ _ _ (hbDu _) (hbDu _) (hprod e₂ Finset.univ p a)
  let J₀ (i j : R) (ω : Ω) :=
    ∫ w, ∫ a : R → T, F (ω,w) a * c (a i) (a j) * G₀ i j (ω,w) a
      ∂(Measure.pi fun _ : R => ν (ω,w)) ∂γ_sh
  let J₁ (i : R) (ω : Ω) :=
    ∫ w, ∫ a : Option R → T, F (ω,w) (a ∘ e₁) * c (a (some i)) (a none) * G₁ i (ω,w) a
      ∂(Measure.pi fun _ : Option R => ν (ω,w)) ∂γ_sh
  let J₁' (i : R) (ω : Ω) :=
    ∫ w, ∫ a : Option R → T, F (ω,w) (a ∘ e₁) * c (a none) (a (some i)) * G₁ i (ω,w) a
      ∂(Measure.pi fun _ : Option R => ν (ω,w)) ∂γ_sh
  let J₂ (ω : Ω) :=
    ∫ w, ∫ a : Option (Option R) → T,
      F (ω,w) (a ∘ e₂) * c (a (some none)) (a none) * G₂ (ω,w) a
      ∂(Measure.pi fun _ : Option (Option R) => ν (ω,w)) ∂γ_sh
  have hj₀ (i j : R) (h : i ≠ j) :
      Integrable (J₀ i j) P₀ ∧ |∫ ω, J₀ i j ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm id Function.injective_id i j h (G₀ i j) (hm₀ i j) (hb₀ i j)
  have hj₁ (i : R) : Integrable (J₁ i) P₀ ∧ |∫ ω, J₁ i ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm e₁ he₁ (some i) none (by simp) (G₁ i) (hm₁ i) (hb₁ i)
  have hj₁' (i : R) : Integrable (J₁' i) P₀ ∧ |∫ ω, J₁' i ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm e₁ he₁ none (some i) (by simp) (G₁ i) (hm₁ i) (hb₁ i)
  have hj₂ : Integrable J₂ P₀ ∧ |∫ ω, J₂ ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm e₂ he₂ (some none) none (by simp) G₂ hm₂ hb₂
  have hcomb := abs_integral_replica_groups_le P₀ J₀ J₁ J₁' J₂
    (fun i j h => (hj₀ i j h).1) (fun i => (hj₁ i).1) (fun i => (hj₁' i).1) hj₂.1
    (mul_nonneg hK (add_nonneg hm (mul_nonneg hε hA₁)))
    (fun i j h => (hj₀ i j h).2) (fun i => (hj₁ i).2) (fun i => (hj₁' i).2) hj₂.2
  have hdRot := hasDerivAt_integral_integral_pi_cavity_rotation_ibp ht hq variance hu ψ
    hψd hψ₂d hM₀ hM₁ hM₂ hf s₀ hfi hfi₁
  have hbound := hcomb.trans_eq
    (show n ^ 2 * (K * (m + ε * A₁)) + n ^ 2 * (K * (m + ε * A₁)) +
      n ^ 2 * (K * (m + ε * A₁)) + n * (n + 1) * (K * (m + ε * A₁)) =
        (4 * n ^ 2 + n) * K * (m + ε * A₁) by ring)
  refine ⟨_, hdRot, ?_⟩
  simpa only [J₀, J₁, J₁', J₂, F, c, G₀, G₁, G₂, e₁, e₂, ν, Function.comp_apply,
    id_eq, ← mul_assoc] using hbound

/-- First-moment endpoint of the split angle estimate. The bounded overlap deviation
supplies the `(1, ∞)` pair bound independently of the system size. -/
theorem exists_hasDerivAt_cavity_rotation_abs_le_first_moment
    {N M : ℕ} {R : Type v} [Fintype R]
    {t q : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
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
    let Ω := SmartPathDisorder N M
    let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
    let T := SmartPathState N M × (Fin 2 → ℝ)
    let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted fun x => u (S s₀ p.2 x)
    let F (p : Ω × W) (a : R → T) := f p.1 (fun r => (a r).1)
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∃ z,
      HasDerivAt
      (fun s => ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))
          ∂γ_sh ∂P₀)
        (Real.sin s₀ * Real.cos s₀ * z) s₀ ∧
      |z| ≤ (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) *
        ((2 + 1 / (N + 1)) *
          ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂(P₀.prod γ_sh)) := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S Ω W T ν F n L hfi hfi₁
  let d (a b : T) :=
    |((∑ i, ((a.1.1.1 i : ℤ) : ℝ) * ((b.1.1.1 i : ℤ) : ℝ)) +
      ((a.1.1.2 : ℤ) : ℝ) * ((b.1.1.2 : ℤ) : ℝ)) / (N + 1) - q|
  have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s₀
  have hV (p : Ω × W) : Measurable fun x : T => u (S s₀ p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have hs := hS.comp hp
    have h := hu.measurable.comp hs
    exact h
  have hμ : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hu.le _)
  let P := P₀.prod γ_sh
  obtain ⟨hFI, hF₁⟩ :=
    integrable_integral_pi_cavity_rotation_abs t q s₀ variance hu.toSmartPathPotential hf hfi hfi₁
  have hd (a b : T) : d a b ≤ 2 := abs_perceptron_overlap_sub_le_two hq _ _
  have hdm : Measurable fun p : T × T => d p.1 p.2 :=
    measurable_pair_comp (π := fun a : T => a.1.1) (measurable_fst.comp measurable_fst)
      (fun a b => d ((a, 0), 0) ((b, 0), 0))
  let I := ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂P
  have hI₀ : 0 ≤ I := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hpair (ι : Type v) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ p, ∫ a : ι → T, |F p (a ∘ e)| * d (a i) (a j)
        ∂(Measure.pi fun _ : ι => ν p) ∂P ≤ 2 * I := by
    have hh := integral_integral_pair_holder_one_top P ν he hij
      (f := F) (d := d) (fun _ _ => abs_nonneg _) hdm (Md := 2)
      (ae_of_all _ fun _ => ae_of_all _ fun a => hd (a 0) (a 1)) hFI hF₁
    exact hh.trans_eq (mul_comm I 2)
  obtain ⟨z, hz, hb⟩ := exists_hasDerivAt_cavity_rotation_abs_le_of_pair_bound ht hq variance
    hu ψ hψd hψ₂d hM₀ hM₁ hM₂ hf s₀ (mul_nonneg zero_le_two hI₀) hfi hfi₁ hpair
  refine ⟨z, hz, hb.trans_eq ?_⟩
  change (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) * (2 * I + 1 / (N + 1) * I) =
    (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) * ((2 + 1 / (N + 1)) * I)
  ring

/-- Interior Hölder exponents for the split angle estimate. The input power moment is
taken in the old Gibbs law, and the bound uses the two moments at the current angle. -/
theorem exists_hasDerivAt_cavity_rotation_abs_le_holder
    {N M : ℕ} {R : Type v} [Fintype R]
    {t q : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
    (s₀ : ℝ) {p₁ p₂ : ℝ} (hp : p₁.HolderConjugate p₂) :
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
    let Ω := SmartPathDisorder N M
    let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
    let T := SmartPathState N M × (Fin 2 → ℝ)
    let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted fun x => u (S s₀ p.2 x)
    let F (p : Ω × W) (a : R → T) := f p.1 (fun r => (a r).1)
    let d (a b : T) :=
      |((∑ i, ((a.1.1.1 i : ℤ) : ℝ) * ((b.1.1.1 i : ℤ) : ℝ)) +
        ((a.1.1.2 : ℤ) : ℝ) * ((b.1.1.2 : ℤ) : ℝ)) / (N + 1) - q|
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ᵐ ω ∂P₀, Integrable (fun a => |f ω a| ^ p₁) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ^ p₁ ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    let P := P₀.prod γ_sh
    let Aₚ := ∫ p, ∫ a, |F p a| ^ p₁ ∂(Measure.pi fun _ : R => ν p) ∂P
    let Bₚ := ∫ p, ∫ a : Fin 2 → T, d (a 0) (a 1) ^ p₂ ∂(Measure.pi fun _ => ν p) ∂P
    ∃ z,
      HasDerivAt
      (fun s => ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))
          ∂γ_sh ∂P₀)
        (Real.sin s₀ * Real.cos s₀ * z) s₀ ∧
      |z| ≤ (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) *
        (Aₚ ^ (1 / p₁) * Bₚ ^ (1 / p₂) + 1 / (N + 1) *
          ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂P) := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S Ω W T ν F d n L hfp hfp₁ P Aₚ Bₚ
  have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s₀
  have hV (p : Ω × W) : Measurable fun x : T => u (S s₀ p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have hs := hS.comp hp
    have h := hu.measurable.comp hs
    exact h
  have hμ : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hu.le _)
  have hP₀ : IsProbabilityMeasure P₀ := by
    dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  obtain ⟨hfi, hfi₁⟩ := integrable_pi_tilted_and_integrable_integral_abs_of_rpow P₀
    (μ := smartPathBase N M) (measurable_smartPathEnergy hu.measurable t) hf hp.lt.le hfp hfp₁
  obtain ⟨hFI, hF₁⟩ :=
    integrable_integral_pi_cavity_rotation_abs t q s₀ variance hu.toSmartPathPotential hf hfi hfi₁
  have hd (a b : T) : d a b ≤ 2 := abs_perceptron_overlap_sub_le_two hq _ _
  have hdm : Measurable fun p : T × T => d p.1 p.2 :=
    measurable_pair_comp (π := fun a : T => a.1.1) (measurable_fst.comp measurable_fst)
      (fun a b => d ((a, 0), 0) ((b, 0), 0))
  let fₚ (ω : Ω) (a : R → SmartPathState N M) := |f ω a| ^ p₁
  have hfm₀ : Measurable fun x : Ω × (R → SmartPathState N M) => |f x.1 x.2| := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hfmₚ : Measurable fun x : Ω × (R → SmartPathState N M) => fₚ x.1 x.2 :=
    hfm₀.pow_const p₁
  have habs (ω : Ω) (a : R → SmartPathState N M) : |fₚ ω a| = fₚ ω a :=
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
  have hfp₁' : Integrable (fun ω => ∫ a, |fₚ ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ := by
    simpa only [habs] using hfp₁
  obtain ⟨hFn, hFnI⟩ :=
    integrable_integral_pi_cavity_rotation_abs t q s₀ variance hu.toSmartPathPotential
      hfmₚ hfp hfp₁'
  have hfp_mem : ∀ᵐ z ∂P, MemLp (F z) (ENNReal.ofReal p₁) (Measure.pi fun _ : R => ν z) := by
    filter_upwards [hFI, hFn] with z hzi hzn
    refine (integrable_norm_rpow_iff hzi.aestronglyMeasurable
      (by simp [hp.pos]) ENNReal.ofReal_ne_top).mp ?_
    rw [ENNReal.toReal_ofReal hp.pos.le]
    change Integrable (fun a : R → T => |F z a| ^ p₁) (Measure.pi fun _ : R => ν z) at hzn
    simpa only [Real.norm_eq_abs] using hzn
  have hfp_int : Integrable (fun z => ∫ a, |F z a| ^ p₁ ∂(Measure.pi fun _ : R => ν z)) P := by
    change Integrable (fun z => ∫ a : R → T, |fₚ z.1 (fun r => (a r).1)|
      ∂(Measure.pi fun _ : R => ν z)) P at hFnI
    simpa only [habs] using hFnI
  have hd₂m : Measurable fun a : Fin 2 → T => d (a 0) (a 1) := by
    have hpair : Measurable fun a : Fin 2 → T => (a 0, a 1) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have h := hdm.comp hpair
    exact h
  have hdq_mem : ∀ᵐ z ∂P, MemLp (fun a : Fin 2 → T => d (a 0) (a 1))
      (ENNReal.ofReal p₂) (Measure.pi fun _ : Fin 2 => ν z) := by
    exact ae_of_all _ fun z => MemLp.of_bound hd₂m.aestronglyMeasurable 2
      (ae_of_all _ fun a => by rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hd _ _)
  let G (_ : Ω × W) (a : Fin 2 → T) := d (a 0) (a 1) ^ p₂
  have hGm : Measurable fun z : (Ω × W) × (Fin 2 → T) => G z.1 z.2 :=
    (hd₂m.pow_const p₂).comp measurable_snd
  have hZ := measurable_integral_pi_cavity_rotation t q s₀ hu.measurable (fun x => hu.le x)
    (F := G) hGm
  have hdq_int : Integrable (fun z => ∫ a : Fin 2 → T, d (a 0) (a 1) ^ p₂
      ∂(Measure.pi fun _ : Fin 2 => ν z)) P := by
    refine Integrable.of_bound hZ.aestronglyMeasurable (2 ^ p₂) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun a => by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hd _ _) hp.symm.pos.le
  have hAₚ : 0 ≤ Aₚ := integral_nonneg fun _ => integral_nonneg fun _ =>
    Real.rpow_nonneg (abs_nonneg _) _
  have hBₚ : 0 ≤ Bₚ := integral_nonneg fun _ => integral_nonneg fun _ =>
    Real.rpow_nonneg (abs_nonneg _) _
  have hpair (ι : Type v) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ z, ∫ a : ι → T, |F z (a ∘ e)| * d (a i) (a j)
        ∂(Measure.pi fun _ : ι => ν z) ∂P ≤ Aₚ ^ (1 / p₁) * Bₚ ^ (1 / p₂) :=
    integral_integral_pair_holder_prob P ν he hij (f := F) (d := d) (fun _ _ => abs_nonneg _) hp
      hfp_mem hfp_int hdq_mem hdq_int
  exact exists_hasDerivAt_cavity_rotation_abs_le_of_pair_bound ht hq variance hu ψ
    hψd hψ₂d hM₀ hM₁ hM₂ hf s₀
    (mul_nonneg (Real.rpow_nonneg hAₚ _) (Real.rpow_nonneg hBₚ _)) hfi hfi₁ hpair

/-- The split angle bound when the observable is essentially bounded. -/
theorem exists_hasDerivAt_cavity_rotation_abs_le_of_ae_abs_le
    {N M : ℕ} {R : Type v} [Fintype R]
    {t q : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (variance : ℝ≥0) {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
    (s₀ : ℝ) {M_f : ℝ} :
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
    let Ω := SmartPathDisorder N M
    let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
    let T := SmartPathState N M × (Fin 2 → ℝ)
    let ν (p : Ω × W) := ((μ₀ p.1).prod γ_aux).tilted fun x => u (S s₀ p.2 x)
    let F (p : Ω × W) (a : R → T) := f p.1 (fun r => (a r).1)
    let d (a b : T) :=
      |((∑ i, ((a.1.1.1 i : ℤ) : ℝ) * ((b.1.1.1 i : ℤ) : ℝ)) +
        ((a.1.1.2 : ℤ) : ℝ) * ((b.1.1.2 : ℤ) : ℝ)) / (N + 1) - q|
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ᵐ ω ∂P₀, ∀ᵐ a ∂(Measure.pi fun _ : R => μ₀ ω), |f ω a| ≤ M_f) →
    let P := P₀.prod γ_sh
    let J := ∫ p, ∫ a : Fin 2 → T, d (a 0) (a 1) ∂(Measure.pi fun _ => ν p) ∂P
    ∃ z,
      HasDerivAt
      (fun s => ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))
          ∂γ_sh ∂P₀)
        (Real.sin s₀ * Real.cos s₀ * z) s₀ ∧
      |z| ≤ (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) *
        (M_f * J + 1 / (N + 1) *
          ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂P) := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S Ω W T ν F d n L hOld P J
  have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s₀
  have hV (p : Ω × W) : Measurable fun x : T => u (S s₀ p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have hs := hS.comp hp
    have h := hu.measurable.comp hs
    exact h
  have hμ : ∀ ω, IsProbabilityMeasure (μ₀ ω) := fun ω =>
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu.measurable (fun x => hu.le x) ω t
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hu.le _)
  have hd (a b : T) : d a b ≤ 2 := abs_perceptron_overlap_sub_le_two hq _ _
  have hdm : Measurable fun p : T × T => d p.1 p.2 :=
    measurable_pair_comp (π := fun a : T => a.1.1) (measurable_fst.comp measurable_fst)
      (fun a b => d ((a, 0), 0) ((b, 0), 0))
  have hd₂m : Measurable fun a : Fin 2 → T => d (a 0) (a 1) := by
    have hpair : Measurable fun a : Fin 2 → T => (a 0, a 1) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have h := hdm.comp hpair
    exact h
  let G (_ : Ω × W) (a : Fin 2 → T) := d (a 0) (a 1)
  have hGm : Measurable fun z : (Ω × W) × (Fin 2 → T) => G z.1 z.2 :=
    hd₂m.comp measurable_snd
  have hZ := measurable_integral_pi_cavity_rotation t q s₀ hu.measurable (fun x => hu.le x)
    (F := G) hGm
  have hJ₀ : 0 ≤ J := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hP₀ : IsProbabilityMeasure P₀ := by
    dsimp [P₀]
    rw [smartPathDisorder_eq]
    infer_instance
  have hMf : 0 ≤ M_f := by
    obtain ⟨ω₀, hω₀⟩ := hOld.exists
    have := hμ ω₀
    obtain ⟨a₀, ha₀⟩ := hω₀.exists
    exact (abs_nonneg _).trans ha₀
  have : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (P₀.prod γ_sh)
    infer_instance
  obtain ⟨hfi, hfi₁⟩ := integrable_pi_tilted_and_integrable_integral_abs_of_ae_abs_le
    (measurable_smartPathEnergy hu.measurable t) (ae_of_all P₀ hμ) hf hOld
  have hFa : ∀ᵐ p ∂P, ∀ᵐ a ∂(Measure.pi fun _ : R => ν p), |F p a| ≤ M_f :=
    ae_pi_tilted_prod_fst P₀ γ_sh μ₀ γ_aux (fun p x => u (S s₀ p.2 x)) hOld
  have hFm (p : Ω × W) :
      AEStronglyMeasurable (F p) (Measure.pi fun _ : R => ν p) := by
    have ha : Measurable fun a : R → T => (p.1, fun r : R => (a r).1) :=
      measurable_const.prodMk (Measurable.of_eval fun r =>
        measurable_fst.comp (measurable_pi_apply r))
    exact (hf.comp ha).aestronglyMeasurable
  have hd_bound (a : Fin 2 → T) : ‖d (a 0) (a 1)‖ ≤ 2 := by
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact hd _ _
  have hd_mem : ∀ᵐ p ∂P, Integrable (fun a : Fin 2 → T => d (a 0) (a 1))
      (Measure.pi fun _ : Fin 2 => ν p) :=
    ae_of_all _ fun _ => Integrable.of_bound hd₂m.aestronglyMeasurable 2 (ae_of_all _ hd_bound)
  have hd_int : Integrable (fun p => ∫ a : Fin 2 → T, d (a 0) (a 1)
      ∂(Measure.pi fun _ : Fin 2 => ν p)) P := by
    refine Integrable.of_bound hZ.aestronglyMeasurable 2 (ae_of_all _ fun p => ?_)
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all (Measure.pi fun _ : Fin 2 => ν p) hd_bound)
  have hpair (ι : Type v) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ p, ∫ a : ι → T, |F p (a ∘ e)| * d (a i) (a j)
        ∂(Measure.pi fun _ : ι => ν p) ∂P ≤ M_f * J :=
    integral_integral_pair_holder_top_one P ν he hij (f := F) (ae_of_all _ hFm) hFa
      (d := d) (fun _ _ => abs_nonneg _) hd_mem hd_int
  exact exists_hasDerivAt_cavity_rotation_abs_le_of_pair_bound ht hq variance hu ψ
    hψd hψ₂d hM₀ hM₁ hM₂ hf s₀ (mul_nonneg hMf hJ₀) hfi hfi₁ hpair

end SpinGlasses
