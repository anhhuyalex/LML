/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingOverlap
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityTimeCovariance

/-!
# The `(s, t)`-smart path for the `s`-interpolating Hamiltonian (Talagrand Section 2.4, Eq. (2.80))

Generalizes the Section 2.2--2.3 smart path (`SmartPathModel.lean`, `SmartPathDecoupling.lean`,
`SmartPathCavityBound.lean`) to the `s`-interpolating Hamiltonian (2.76) for any `s ∈ [0, 1]`.

At parameters `(s, t, q, r)`:
* Quenched disorder: `ω = ((((g_old, a), z), z'_old), (y, z'_last))`, where
  `g_old : Fin M → Fin N → ℝ`, `a : Fin M → ℝ`, `z : Fin M → ℝ`, `z'_old : Fin N → ℝ` are i.i.d.
  standard Gaussians, `y ~ 𝒩(0, v)` (`v = (s * r).toNNReal`), and `z'_last ~ 𝒩(0, 1)`.
* Replica configuration: `(σ, ξ) ∈ PerceptronSpin N × (Fin M → Fin 2 → ℝ)`, where for each
  constraint `k`, `ξ k 0` is the Section 2.2 smart-path auxiliary Gaussian and `ξ k 1` is the
  Section 2.4 auxiliary Gaussian ("new spin").
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

universe uR

section DefinitionsAndBasic

/-- Type of quenched disorders for the `(s, t)`-interpolating smart path on `N` old spins + `1`
last spin and `M` constraints: `(((g_old, a), z), z'_old)` paired with `(y, z'_last)`. -/
private abbrev InterpSPDisorder (N M : ℕ) :=
  (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × (ℝ × ℝ))

/-- Type of per-replica states for the `(s, t)`-interpolating smart path. -/
private abbrev InterpSPState (N M : ℕ) :=
  PerceptronSpin N × (Fin M → Fin 2 → ℝ)

/-- Base measure on `InterpSPState N M`: counting measure on `PerceptronSpin N` times standard
Gaussian measure on `Fin M → Fin 2 → ℝ`. -/
private noncomputable def interpSPBase (N M : ℕ) : Measure (InterpSPState N M) :=
  (Measure.count : Measure (PerceptronSpin N)).prod
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)

private instance (N M : ℕ) : IsFiniteMeasure (interpSPBase N M) := by
  unfold interpSPBase; infer_instance

private instance (N M : ℕ) : NeZero (interpSPBase N M) := by
  unfold interpSPBase
  have : NeZero (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
    inferInstance
  infer_instance

/-- Quenched disorder measure on `InterpSPDisorder N M` with last-field variance `v : ℝ≥0`. -/
private noncomputable def interpSPDisorder (N M : ℕ) (v : ℝ≥0) : Measure (InterpSPDisorder N M) :=
  (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
      ((gaussianReal 0 v).prod (gaussianReal 0 1)))

private instance (N M : ℕ) (v : ℝ≥0) : IsProbabilityMeasure (interpSPDisorder N M v) := by
  unfold interpSPDisorder; infer_instance

/-- Constraint field `S_{k, s, t}` of the `(s, t)`-interpolating smart path. -/
private noncomputable def interpSPField {N M : ℕ} (s t q : ℝ)
    (ω : InterpSPDisorder N M) (x : InterpSPState N M) (k : Fin M) : ℝ :=
  Real.sqrt s * (smartPathFieldNoAux t (ω.1.1, ω.2.2.1) (x.1, 0) k +
      Real.sqrt ((1 - t) / (N + 1)) * x.2 k 0) +
    Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k 1)

/-- Energy `E_{s, t}` of the `(s, t)`-interpolating smart path. -/
private noncomputable def interpSPEnergy {N M : ℕ} (u : ℝ → ℝ) (s t q r : ℝ)
    (ω : InterpSPDisorder N M) (x : InterpSPState N M) : ℝ :=
  (∑ k : Fin M, u (interpSPField s t q ω x k)) +
    (∑ i : Fin N, ((x.1.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r) +
    ((x.1.2 : ℤ) : ℝ) * (Real.sqrt (1 - t) * ω.2.2.1 + Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r)

private lemma measurable_interpSPField {N M : ℕ} (s t q : ℝ) (k : Fin M) :
    Measurable fun p : InterpSPDisorder N M × InterpSPState N M =>
      interpSPField s t q p.1 p.2 k := by
  simp only [interpSPField, smartPathFieldNoAux_eq]
  fun_prop

private lemma measurable_interpSPEnergy {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (s t q r : ℝ) :
    Measurable fun p : InterpSPDisorder N M × InterpSPState N M =>
      interpSPEnergy u s t q r p.1 p.2 := by
  unfold interpSPEnergy
  refine ((Finset.measurable_sum _ fun k _ =>
    hu.comp (measurable_interpSPField s t q k)).add ?_).add ?_
  · fun_prop
  · fun_prop

private lemma measurable_interpSPEnergy_slice {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (s t q r : ℝ) (ω : InterpSPDisorder N M) :
    Measurable (interpSPEnergy u s t q r ω) :=
  Measurable.of_uncurry_left (measurable_interpSPEnergy hu s t q r)

private lemma interpSPEnergy_le {N M : ℕ} {u : ℝ → ℝ} {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s t q r : ℝ) (ω : InterpSPDisorder N M) (x : InterpSPState N M) :
    interpSPEnergy u s t q r ω x ≤
      M * B + (∑ i : Fin N, |Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r|) +
        (|Real.sqrt (1 - t)| * |ω.2.2.1| + |Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r|) := by
  unfold interpSPEnergy
  refine add_le_add (add_le_add ((Finset.sum_le_sum fun _ _ => hB _).trans_eq (by simp)) ?_) ?_
  · refine Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  · refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_units_cast_eq_one, one_mul]
    exact (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]) le_rfl)

private lemma integrable_exp_interpSPEnergy {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (s t q r : ℝ) (ω : InterpSPDisorder N M) :
    Integrable (fun x => Real.exp (interpSPEnergy u s t q r ω x)) (interpSPBase N M) :=
  integrable_exp_of_ae_le (measurable_interpSPEnergy_slice hu s t q r ω).aemeasurable
    (ae_of_all _ (interpSPEnergy_le hB s t q r ω))

private lemma isProbabilityMeasure_tilted_interpSPEnergy {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (s t q r : ℝ) (ω : InterpSPDisorder N M) :
    IsProbabilityMeasure ((interpSPBase N M).tilted (interpSPEnergy u s t q r ω)) :=
  isProbabilityMeasure_tilted (integrable_exp_interpSPEnergy hu hB s t q r ω)

/-! ### Auxiliary marginalization and continuity on `t ∈ [0, 1]` -/

/-- Integrating out the two auxiliary coordinates `ξ_{k, 0}, ξ_{k, 1}` per constraint reduces any
spin-only replica average under `interpSPBase` to a finite `Measure.count.tilted` average. -/
private lemma integral_pi_interpSP_auxiliary {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s t q r : ℝ) (ω : InterpSPDisorder N M) (F : (R → PerceptronSpin N) → ℝ) :
    ∫ x : R → InterpSPState N M, F (fun l => (x l).1)
      ∂(Measure.pi fun _ : R => (interpSPBase N M).tilted (interpSPEnergy u s t q r ω)) =
    ∫ σ : R → PerceptronSpin N, F σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (fun σ : PerceptronSpin N =>
        ((∑ i : Fin N, ((σ.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r) +
          ((σ.2 : ℤ) : ℝ) *
            (Real.sqrt (1 - t) * ω.2.2.1 + Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r)) +
        ∑ k : Fin M, Real.log (∫ ξ : Fin 2 → ℝ,
          Real.exp (u (Real.sqrt s * (smartPathFieldNoAux t (ω.1.1, ω.2.2.1) (σ, 0) k +
              Real.sqrt ((1 - t) / (N + 1)) * ξ 0) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ 1)))
          ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1)))) := by
  have hE_eq : interpSPEnergy u s t q r ω = fun p : PerceptronSpin N × (Fin M → Fin 2 → ℝ) =>
      ((∑ i : Fin N, ((p.1.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r) +
        ((p.1.2 : ℤ) : ℝ) *
          (Real.sqrt (1 - t) * ω.2.2.1 + Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r)) +
      ∑ k : Fin M, u (interpSPField s t q ω p k) := by
    funext p; unfold interpSPEnergy; ring
  rw [hE_eq, interpSPBase]
  exact integral_pi_tilted_count_prod_sum
    (fun _ : Fin M => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
    (fun σ : PerceptronSpin N =>
      (∑ i : Fin N, ((σ.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r) +
        ((σ.2 : ℤ) : ℝ) *
          (Real.sqrt (1 - t) * ω.2.2.1 + Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r))
    (fun σ k ξ => u (Real.sqrt s * (smartPathFieldNoAux t (ω.1.1, ω.2.2.1) (σ, 0) k +
        Real.sqrt ((1 - t) / (N + 1)) * ξ 0) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ 1)))
    (fun σ k => hu.comp (by fun_prop)) (fun _ => B) (fun _ _ _ => hB _) F

/-- Continuity of `t ↦ ν_{t, s}(f)` on `[0, 1]`. -/
private lemma continuousOn_integral_interpSP {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Continuous u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (s q r : ℝ) (v : ℝ≥0) (f : (R → PerceptronSpin N) → ℝ) :
    ContinuousOn
      (fun t => ∫ ω, ∫ x : R → InterpSPState N M, f (fun l => (x l).1)
        ∂(Measure.pi fun _ : R => (interpSPBase N M).tilted (interpSPEnergy u s t q r ω))
        ∂(interpSPDisorder N M v))
      (Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let P := interpSPDisorder N M v
  let Φ (t : ℝ) (ω : InterpSPDisorder N M) : ℝ :=
    ∫ x : R → InterpSPState N M, f (fun l => (x l).1)
      ∂(Measure.pi fun _ : R => (interpSPBase N M).tilted (interpSPEnergy u s t q r ω))
  have hΦm (t : ℝ) : AEStronglyMeasurable (Φ t) P := by
    let F_obs (_ω : InterpSPDisorder N M) (x : R → InterpSPState N M) : ℝ := f (fun l => (x l).1)
    have hFm : Measurable fun p : InterpSPDisorder N M × (R → InterpSPState N M) => F_obs p.1 p.2 :=
      (measurable_of_finite f).comp (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd))
    exact (measurable_integral_pi_tilted (μ := interpSPBase N M)
      (measurable_interpSPEnergy hu.measurable s t q r) hFm).aestronglyMeasurable
  have hΦb (t : ℝ) (ω : InterpSPDisorder N M) : ‖Φ t ω‖ ≤ |C_f| := by
    have := isProbabilityMeasure_tilted_interpSPEnergy hu.measurable hB_le s t q r ω
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ fun x => (hCf _).trans (le_abs_self _)
  have hΦ_cont (ω : InterpSPDisorder N M) : Continuous (fun t => Φ t ω) := by
    let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let g_pot (t : ℝ) (a : PerceptronSpin N) (k : Fin M) : ℝ :=
      ∫ ξ : Fin 2 → ℝ,
        Real.exp (u (Real.sqrt s * (smartPathFieldNoAux t (ω.1.1, ω.2.2.1) (a, 0) k +
            Real.sqrt ((1 - t) / (N + 1)) * ξ 0) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ 1))) ∂γ₂
    have hg_pos (t : ℝ) (a : PerceptronSpin N) (k : Fin M) : 0 < g_pot t a k := by
      have hm : Measurable fun ξ : Fin 2 → ℝ =>
          u (Real.sqrt s * (smartPathFieldNoAux t (ω.1.1, ω.2.2.1) (a, 0) k +
              Real.sqrt ((1 - t) / (N + 1)) * ξ 0) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ 1)) :=
        hu.measurable.comp (by fun_prop)
      exact integral_exp_pos_of_ae_le hm.aemeasurable (ae_of_all _ fun _ => hB_le _)
    have hg_cont (a : PerceptronSpin N) (k : Fin M) : Continuous (fun t => g_pot t a k) := by
      refine continuous_of_dominated (bound := fun _ => Real.exp B)
        (fun t => ?_) (fun t => ae_of_all _ fun ξ => ?_) (integrable_const _)
        (ae_of_all _ fun ξ => ?_)
      · exact (Real.continuous_exp.comp (hu.comp (by fun_prop))).measurable.aestronglyMeasurable
      · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.2 (hB_le _)
      · simp only [smartPathFieldNoAux_eq]; fun_prop
    let w_spin (t : ℝ) (a : PerceptronSpin N) : ℝ :=
      Real.exp ((∑ i : Fin N, ((a.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r) +
        ((a.2 : ℤ) : ℝ) * (Real.sqrt (1 - t) * ω.2.2.1 + Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r))
    have hw_cont (a : PerceptronSpin N) : Continuous (fun t => w_spin t a) := by
      dsimp only [w_spin]; fun_prop
    let ψ_spin (t : ℝ) (a : PerceptronSpin N) : ℝ := ∏ k : Fin M, g_pot t a k
    have hψ_cont (a : PerceptronSpin N) : Continuous (fun t => ψ_spin t a) := by
      dsimp only [ψ_spin]; fun_prop
    have hw_pos (t : ℝ) (a : PerceptronSpin N) : 0 < w_spin t a := Real.exp_pos _
    have hψ_pos (t : ℝ) (a : PerceptronSpin N) : 0 < ψ_spin t a :=
      Finset.prod_pos fun k _ => hg_pos t a k
    have hden_ne (t : ℝ) : (∑ a : PerceptronSpin N, w_spin t a * ψ_spin t a) ^ Fintype.card R ≠ 0 :=
      pow_ne_zero _ (Finset.sum_pos (fun a _ => mul_pos (hw_pos t a) (hψ_pos t a))
        Finset.univ_nonempty).ne'
    have hΦ_eq (t : ℝ) : Φ t ω =
        (∑ σ : R → PerceptronSpin N, f σ * ∏ l, (w_spin t (σ l) * ψ_spin t (σ l))) /
          (∑ a : PerceptronSpin N, w_spin t a * ψ_spin t a) ^ Fintype.card R := by
      dsimp only [Φ]
      rw [integral_pi_interpSP_auxiliary hu.measurable hB_le s t q r ω f]
      refine integral_pi_count_tilted_eq_sum_div (fun a => ?_) f
      rw [Real.exp_add]
      congr 1
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun k _ => Real.exp_log (hg_pos t a k)
    simp_rw [hΦ_eq]
    have hnum_cont : Continuous (fun t =>
        ∑ σ : R → PerceptronSpin N, f σ * ∏ l, (w_spin t (σ l) * ψ_spin t (σ l))) := by fun_prop
    have hden_cont : Continuous (fun t =>
        (∑ a : PerceptronSpin N, w_spin t a * ψ_spin t a) ^ Fintype.card R) := by fun_prop
    exact hnum_cont.div hden_cont hden_ne
  exact (continuous_of_dominated (bound := fun _ => |C_f|) hΦm
    (fun t => ae_of_all _ (hΦb t)) (integrable_const _) (ae_of_all _ hΦ_cont)).continuousOn

/-! ### Terminal identity `t = 1` and decoupled endpoint `t = 0` -/

/-- **Terminal identity at `t = 1`:** the `(s, t = 1)` smart-path average of any spin-only
observable equals the `s`-interpolating Gibbs average (2.76). -/
private lemma integral_interpSP_one_eq {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (v : ℝ≥0) (F : (R → Fin (N + 1) → ℤˣ) → ℝ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_s := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ∫ ω, ∫ x : R → InterpSPState N M,
        F (fun l => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x l).1.1 (x l).1.2)
        ∂(Measure.pi fun _ : R => (interpSPBase N M).tilted (interpSPEnergy u s 1 q r ω))
        ∂(interpSPDisorder N M v) =
      ∫ ω, ∫ σ : R → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), F (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => μ_s.tilted (E_s ω)) ∂P_s := by
  intro P_g P_z P_z' P_s μ_s E_s
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let e_spin : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (MeasurableEquiv.finSuccProd ℤˣ N).symm.toEquiv
  have he_spin (σ : PerceptronSpin N) : e_spin σ = Fin.snoc σ.1 σ.2 :=
    MeasurableEquiv.finSuccProd_symm_apply N σ
  have hlhs_pt (ω : InterpSPDisorder N M) :
      ∫ x : R → InterpSPState N M,
        F (fun l => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x l).1.1 (x l).1.2)
        ∂(Measure.pi fun _ : R => (interpSPBase N M).tilted (interpSPEnergy u s 1 q r ω)) =
      ∫ σ : R → PerceptronSpin N, F (fun l => e_spin (σ l))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (fun σ : PerceptronSpin N =>
          ((∑ i : Fin N, ((σ.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r) +
            ((σ.2 : ℤ) : ℝ) * (Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r)) +
          ∑ k : Fin M, Real.log (∫ ξ₁ : ℝ,
            Real.exp (u (Real.sqrt s * smartPathFieldNoAux 1 (ω.1.1, 0) (σ, 0) k +
              Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ₁)))
            ∂γ₁))) := by
    simp_rw [← he_spin]
    rw [integral_pi_interpSP_auxiliary hu hB s 1 q r ω (fun σ => F (fun l => e_spin (σ l)))]
    congr 1; congr 1; funext _; congr 1; funext σ
    simp only [sub_self, Real.sqrt_zero, zero_mul, zero_add, zero_div]
    congr 1
    refine Finset.sum_congr rfl fun k _ => congrArg Real.log ?_
    have he_2 : MeasurePreserving (MeasurableEquiv.piFinTwo fun _ => ℝ)
        (Measure.pi fun _ : Fin 2 => γ₁) (γ₁.prod γ₁) :=
      measurePreserving_piFinTwo fun _ => γ₁
    let g_ξ (ξ₁ : ℝ) : ℝ :=
      Real.exp (u (Real.sqrt s * smartPathFieldNoAux 1 (ω.1.1, 0) (σ, 0) k +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ₁)))
    have hm_ξ₁ : Measurable g_ξ := Real.measurable_exp.comp (hu.comp (by fun_prop))
    have h1 := he_2.integral_comp_of_aestronglyMeasurable
      (g := fun p : ℝ × ℝ => g_ξ p.2) (hm_ξ₁.comp measurable_snd).aestronglyMeasurable
    have h2 : ∫ p : ℝ × ℝ, g_ξ p.2 ∂(γ₁.prod γ₁) = ∫ ξ₁ : ℝ, g_ξ ξ₁ ∂γ₁ := by
      have hp := integral_prod_mul (μ := γ₁) (ν := γ₁) (fun _ => (1 : ℝ)) g_ξ
      simpa using hp
    refine (integral_congr_ae (ae_of_all _ fun ξ => ?_)).trans (h1.trans h2)
    dsimp only [g_ξ, smartPathFieldNoAux_eq, MeasurableEquiv.piFinTwo_apply]
    simp
  simp_rw [hlhs_pt]
  let e_row : (Fin (N + 1) → ℝ) ≃ᵐ (Fin N → ℝ) × ℝ := MeasurableEquiv.finSuccProd ℝ N
  have hmp_row : MeasurePreserving ⇑e_row (Measure.pi fun _ : Fin (N + 1) => γ₁)
      ((Measure.pi fun _ : Fin N => γ₁).prod γ₁) :=
    measurePreserving_finSuccProd γ₁ N
  let e_rows : (Fin M → Fin (N + 1) → ℝ) ≃ᵐ (Fin M → (Fin N → ℝ) × ℝ) :=
    MeasurableEquiv.piCongrRight fun _ => e_row
  have hmp_rows : MeasurePreserving ⇑e_rows P_g
      (Measure.pi fun _ : Fin M => (Measure.pi fun _ : Fin N => γ₁).prod γ₁) :=
    measurePreserving_pi _ _ fun _ => hmp_row
  let e_split : (Fin M → Fin (N + 1) → ℝ) ≃ᵐ (Fin M → Fin N → ℝ) × (Fin M → ℝ) :=
    e_rows.trans (MeasurableEquiv.arrowProdEquivProdArrow _ _ _)
  have hmp_split : MeasurePreserving ⇑e_split P_g
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ₁).prod
        (Measure.pi fun _ : Fin M => γ₁)) :=
    (measurePreserving_arrowProdEquivProdArrow (Fin N → ℝ) ℝ (Fin M)
      (fun _ => Measure.pi fun _ : Fin N => γ₁) (fun _ => γ₁)).comp hmp_rows
  let e_dis : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ≃ᵐ
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr e_split (MeasurableEquiv.refl _)) e_row
  have hmp_dis : MeasurePreserving ⇑e_dis P_s
      ((((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ₁).prod
        (Measure.pi fun _ : Fin M => γ₁)).prod P_z).prod
        ((Measure.pi fun _ : Fin N => γ₁).prod γ₁)) :=
    (hmp_split.prod (MeasurePreserving.id P_z)).prod hmp_row
  let proj_no_y (ω : InterpSPDisorder N M) :
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ) :=
    (ω.1, (ω.2.1, ω.2.2.2))
  have hmp_proj : MeasurePreserving proj_no_y (interpSPDisorder N M v)
      ((((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ₁).prod
        (Measure.pi fun _ : Fin M => γ₁)).prod P_z).prod
        ((Measure.pi fun _ : Fin N => γ₁).prod γ₁)) := by
    unfold interpSPDisorder
    have hmp_yz : MeasurePreserving (fun p : ℝ × ℝ => p.2)
        ((gaussianReal 0 v).prod γ₁) γ₁ := measurePreserving_snd
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hmp_yz)
  let Ψ (q_no_y : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ)) : ℝ :=
    ∫ σ : R → PerceptronSpin N, F (fun l => e_spin (σ l))
      ∂(Measure.pi fun _ : R => Measure.count.tilted (fun σ : PerceptronSpin N =>
        ((∑ i : Fin N, ((σ.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * q_no_y.2.1 i * Real.sqrt r) +
          ((σ.2 : ℤ) : ℝ) * (Real.sqrt (1 - s) * q_no_y.2.2 * Real.sqrt r)) +
        ∑ k : Fin M, Real.log (∫ ξ₁ : ℝ,
          Real.exp (u (Real.sqrt s * smartPathFieldNoAux 1 (q_no_y.1.1, 0) (σ, 0) k +
            Real.sqrt (1 - s) * (Real.sqrt q * q_no_y.1.2 k + Real.sqrt (1 - q) * ξ₁)))
          ∂γ₁)))
  have hΨ_m : Measurable Ψ := by
    have hEm : ∀ σ : PerceptronSpin N, Measurable fun q_no_y :
        (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ) =>
        ((∑ i : Fin N, ((σ.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * q_no_y.2.1 i * Real.sqrt r) +
          ((σ.2 : ℤ) : ℝ) * (Real.sqrt (1 - s) * q_no_y.2.2 * Real.sqrt r)) +
        ∑ k : Fin M, Real.log (∫ ξ₁ : ℝ,
          Real.exp (u (Real.sqrt s * smartPathFieldNoAux 1 (q_no_y.1.1, 0) (σ, 0) k +
            Real.sqrt (1 - s) * (Real.sqrt q * q_no_y.1.2 k + Real.sqrt (1 - q) * ξ₁)))
          ∂γ₁) := fun σ => by
      have hm1 : Measurable fun q_no_y :
          (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ) =>
          (∑ i : Fin N, ((σ.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * q_no_y.2.1 i * Real.sqrt r) +
            ((σ.2 : ℤ) : ℝ) * (Real.sqrt (1 - s) * q_no_y.2.2 * Real.sqrt r) := by fun_prop
      have hm2 : Measurable fun q_no_y :
          (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ) =>
          ∑ k : Fin M, Real.log (∫ ξ₁ : ℝ,
            Real.exp (u (Real.sqrt s * smartPathFieldNoAux 1 (q_no_y.1.1, 0) (σ, 0) k +
              Real.sqrt (1 - s) * (Real.sqrt q * q_no_y.1.2 k + Real.sqrt (1 - q) * ξ₁)))
            ∂γ₁) := by
        refine Finset.measurable_sum _ fun k _ => Real.measurable_log.comp ?_
        have hj : Measurable fun p :
            ((((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ)) × ℝ =>
            Real.exp (u (Real.sqrt s * smartPathFieldNoAux 1 (p.1.1.1, 0) (σ, 0) k +
              Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2))) := by
          simp only [smartPathFieldNoAux_eq]
          exact Real.measurable_exp.comp (hu.comp (by fun_prop))
        exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ₁)).measurable
      exact hm1.add hm2
    have hE_joint : Measurable fun p :
        ((((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ)) ×
          PerceptronSpin N =>
        ((∑ i : Fin N, ((p.2.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * p.1.2.1 i * Real.sqrt r) +
          ((p.2.2 : ℤ) : ℝ) * (Real.sqrt (1 - s) * p.1.2.2 * Real.sqrt r)) +
        ∑ k : Fin M, Real.log (∫ ξ₁ : ℝ,
          Real.exp (u (Real.sqrt s * smartPathFieldNoAux 1 (p.1.1.1, 0) (p.2, 0) k +
            Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * ξ₁)))
          ∂γ₁) := measurable_from_prod_countable_left hEm
    let G_obs (_q : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ))
        (σ : R → PerceptronSpin N) : ℝ := F (fun l => e_spin (σ l))
    have hGm : Measurable fun p :
        ((((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × ((Fin N → ℝ) × ℝ)) ×
          (R → PerceptronSpin N) => G_obs p.1 p.2 :=
      (measurable_of_finite fun σ : R → PerceptronSpin N => F (fun l => e_spin (σ l))).comp
        measurable_snd
    exact measurable_integral_pi_tilted (μ := Measure.count) hE_joint hGm
  change (∫ ω, Ψ (proj_no_y ω) ∂(interpSPDisorder N M v)) = _
  rw [hmp_proj.integral_comp_of_aestronglyMeasurable hΨ_m.aestronglyMeasurable,
    ← hmp_dis.integral_comp_of_aestronglyMeasurable hΨ_m.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only [Ψ]
  have haux_rhs : ∫ σ : R → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), F (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R => μ_s.tilted (E_s ω)) =
    ∫ τ : R → Fin (N + 1) → ℤˣ, F τ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (fun τ : Fin (N + 1) → ℤˣ =>
        (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
        ∑ k : Fin M, Real.log (∫ ξ₁ : ℝ,
          Real.exp (u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
            ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ₁)))
          ∂γ₁))) := by
    have hE_swap (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E_s ω x = (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
          ∑ k : Fin M, u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
            ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)) := add_comm _ _
    simp_rw [show E_s ω = _ from funext hE_swap]
    exact integral_pi_tilted_count_prod_sum (fun _ : Fin M => γ₁)
      (fun τ : Fin (N + 1) → ℤˣ =>
        ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
      (fun τ k ξ₁ => u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
        ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ₁)))
      (fun τ k => hu.comp (by fun_prop)) (fun _ => B) (fun _ _ _ => hB _) F
  rw [haux_rhs, integral_pi_count_tilted_equiv e_spin _ F]
  congr 1; congr 1; funext _; congr 1; funext σ
  have he_g : e_split ω.1.1 =
      (fun k i => ω.1.1 k i.castSucc, fun k => ω.1.1 k (Fin.last N)) := by
    refine Prod.ext (funext fun k => funext fun i => ?_) (funext fun k => ?_)
    · change (MeasurableEquiv.finSuccProd ℝ N (ω.1.1 k)).1 i = ω.1.1 k i.castSucc
      rw [MeasurableEquiv.finSuccProd_apply]
    · change (MeasurableEquiv.finSuccProd ℝ N (ω.1.1 k)).2 = ω.1.1 k (Fin.last N)
      rw [MeasurableEquiv.finSuccProd_apply]
  have he_z' : e_row ω.2 = (fun i => ω.2 i.castSucc, ω.2 (Fin.last N)) :=
    MeasurableEquiv.finSuccProd_apply N ω.2
  have hd_dis : e_dis ω = ((e_split ω.1.1, ω.1.2), e_row ω.2) := rfl
  rw [hd_dis, he_g, he_z', he_spin σ]
  congr 1
  · rw [Fin.sum_univ_castSucc]
    simp [mul_assoc]
  · refine Finset.sum_congr rfl fun k _ => congrArg Real.log ?_
    refine integral_congr_ae (ae_of_all _ fun ξ₁ => ?_)
    dsimp only
    congr 2; congr 1; congr 1
    simpa only [smartPathFieldNoAux, div_one, one_div, Real.sqrt_inv, Nat.cast_add,
      Nat.cast_one] using (normalized_constraint_field_snoc σ.1 σ.2 (ω.1.1 k)).symm

/-- **Decoupled endpoint `t = 0` for the `(s, t)`-interpolating smart path:**
when `s ∈ [0, 1]`, `r ≥ 0`, `v = (s * r).toNNReal`, and `q = 𝔼 tanh²(z √r)`, the `t = 0` average of
`f = (ε₁ ε₂ - q)(R_{1,2} - q)` equals `(1 - q²) / (N + 1)`. -/
private lemma integral_interpSP_zero_last_spin_eq {N M : ℕ}
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr0 : 0 ≤ r)
    {q : ℝ} (hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1) :
    let v : ℝ≥0 := (s * r).toNNReal
    let R_spin (a b : PerceptronSpin N) : ℝ :=
      ((∑ i, ((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ)) +
        ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) / (N + 1)
    ∫ ω, ∫ x : Fin 2 → InterpSPState N M,
        ((((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ) - q) *
          (R_spin (x 0).1 (x 1).1 - q)
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
        ∂(interpSPDisorder N M v) =
      (1 - q ^ 2) / (N + 1) := by
  intro v R_spin
  let γ₁ : Measure ℝ := gaussianReal 0 1
  have h_tanh_yz : ∫ p : ℝ × ℝ,
      Real.tanh (p.1 + Real.sqrt (1 - s) * p.2 * Real.sqrt r) ^ 2
      ∂((gaussianReal 0 v).prod γ₁) = q := by
    have hv_coe : (v : ℝ) = s * r := Real.coe_toNNReal _ (mul_nonneg hs.1 hr0)
    have hmap_v : gaussianReal 0 v = γ₁.map (fun z₁ : ℝ => Real.sqrt (s * r) * z₁) := by
      rw [NeuralNetwork.DeepLinear.gaussianReal_scaling v, hv_coe]
    have hmp_prod : MeasurePreserving
        (fun p : ℝ × ℝ => (Real.sqrt (s * r) * p.1, p.2))
        (γ₁.prod γ₁) ((gaussianReal 0 v).prod γ₁) := by
      refine MeasurePreserving.prod ?_ (MeasurePreserving.id γ₁)
      exact ⟨by fun_prop, hmap_v.symm⟩
    have hm_t : Measurable fun p : ℝ × ℝ =>
        Real.tanh (p.1 + Real.sqrt (1 - s) * p.2 * Real.sqrt r) ^ 2 :=
      ((continuous_pow 2).comp (Real.continuous_tanh.comp (by fun_prop))).measurable
    rw [← hmp_prod.integral_comp_of_aestronglyMeasurable hm_t.aestronglyMeasurable]
    let e_u : (Unit → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique Unit ℝ
    have hmp_u : MeasurePreserving ⇑e_u (Measure.pi fun _ : Unit => γ₁) γ₁ :=
      measurePreserving_funUnique γ₁ Unit
    have hmp_uu : MeasurePreserving (fun q' : (Unit → ℝ) × (Unit → ℝ) => (q'.1 (), q'.2 ()))
        ((Measure.pi fun _ : Unit => γ₁).prod (Measure.pi fun _ : Unit => γ₁)) (γ₁.prod γ₁) :=
      hmp_u.prod hmp_u
    have hm_t2 : Measurable fun p : ℝ × ℝ =>
        Real.tanh (Real.sqrt (s * r) * p.1 + Real.sqrt (1 - s) * p.2 * Real.sqrt r) ^ 2 :=
      ((continuous_pow 2).comp (Real.continuous_tanh.comp (by fun_prop))).measurable
    rw [← hmp_uu.integral_comp_of_aestronglyMeasurable hm_t2.aestronglyMeasurable]
    have hsq_sum : Real.sqrt r ^ 2 = Real.sqrt (s * r) ^ 2 + (Real.sqrt (1 - s) * Real.sqrt r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hr0, Real.sq_sqrt (mul_nonneg hs.1 hr0),
        Real.sq_sqrt (sub_nonneg.2 hs.2)]
      ring
    have hrot := (integral_pi_gaussianReal_scale_eq_prod_linear_combo (ι := Unit)
      (Real.sqrt (s * r)) (Real.sqrt (1 - s) * Real.sqrt r) (Real.sqrt r) hsq_sum
      (f := fun u_fn : Unit → ℝ => Real.tanh (u_fn ()) ^ 2)
      (((continuous_pow 2).comp Real.continuous_tanh).measurable.comp (measurable_pi_apply ()))).symm
    have hlhs_eq : (∫ q' : (Unit → ℝ) × (Unit → ℝ),
        Real.tanh (Real.sqrt (s * r) * q'.1 () + Real.sqrt (1 - s) * q'.2 () * Real.sqrt r) ^ 2
        ∂((Measure.pi fun _ : Unit => γ₁).prod (Measure.pi fun _ : Unit => γ₁))) =
      ∫ q' : (Unit → ℝ) × (Unit → ℝ),
        Real.tanh (Real.sqrt (s * r) * q'.1 () +
          (Real.sqrt (1 - s) * Real.sqrt r) * q'.2 ()) ^ 2
        ∂((Measure.pi fun _ : Unit => γ₁).prod (Measure.pi fun _ : Unit => γ₁)) :=
      integral_congr_ae (ae_of_all _ fun q' => by dsimp only; congr 2; ring)
    rw [hlhs_eq, hrot]
    have hrhs_eq := hmp_u.integral_comp_of_aestronglyMeasurable
      (g := fun z : ℝ => Real.tanh (Real.sqrt r * z) ^ 2)
      ((continuous_pow 2).comp (Real.continuous_tanh.comp (by fun_prop))).aestronglyMeasurable
    refine hrhs_eq.trans ?_
    rw [hq]
    exact integral_congr_ae (ae_of_all _ fun z => by dsimp only; congr 2; ring)
  let P₀ := (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ₁).prod
      (Measure.pi fun _ : Fin M => γ₁)).prod
      (Measure.pi fun _ : Fin M => γ₁)).prod (Measure.pi fun _ : Fin N => γ₁)
  let P₁ := (gaussianReal 0 v).prod γ₁
  let e_reassoc : InterpSPDisorder N M ≃ᵐ
      ((((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × (Fin N → ℝ)) × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc.symm
  have hmp_reassoc : MeasurePreserving ⇑e_reassoc (interpSPDisorder N M v) (P₀.prod P₁) :=
    (measurePreserving_prodAssoc _ _ _).symm
  let A_old (ω₀ : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × (Fin N → ℝ))
      (ρ : Fin N → ℤˣ) : ℝ :=
    (∑ i : Fin N, ((ρ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r) +
    ∑ k : Fin M, Real.log (∫ ξ : Fin 2 → ℝ,
      Real.exp (u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          (∑ i : Fin N, ω₀.1.1.1 k i * ((ρ i : ℤ) : ℝ)) +
          Real.sqrt (1 / (N + 1)) * ξ 0) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k + Real.sqrt (1 - q) * ξ 1)))
      ∂(Measure.pi fun _ : Fin 2 => γ₁))
  let Y_last (ω₁ : ℝ × ℝ) : ℝ := ω₁.1 + Real.sqrt (1 - s) * ω₁.2 * Real.sqrt r
  have hpt_aux (ω : InterpSPDisorder N M) (G : (Fin 2 → PerceptronSpin N) → ℝ) :
      ∫ x : Fin 2 → InterpSPState N M, G (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω)) =
      ∫ σ : Fin 2 → PerceptronSpin N, G σ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
          fun x : PerceptronSpin N =>
            A_old (e_reassoc ω).1 x.1 + ((x.2 : ℤˣ) : ℝ) * Y_last (e_reassoc ω).2) := by
    rw [integral_pi_interpSP_auxiliary hu hB s 0 q r ω G]
    congr 1; congr 1; funext _; congr 1; funext σ
    have he1 : (e_reassoc ω).1 = (ω.1, ω.2.1) := rfl
    have he2 : (e_reassoc ω).2 = ω.2.2 := rfl
    rw [he1, he2]
    dsimp only [A_old, Y_last]
    have hfl (k : Fin M) : smartPathFieldNoAux 0 (ω.1.1, ω.2.2.1) (σ, 0) k =
        (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin N, ω.1.1.1 k i * ((σ.1 i : ℤ) : ℝ) := by
      simp [smartPathFieldNoAux]
    have hsub0 : (1 : ℝ) - 0 = 1 := sub_zero 1
    simp only [hsub0, Real.sqrt_one, one_mul, hfl]
    ring
  have hint_Ip (G : (Fin 2 → PerceptronSpin N) → ℝ) :
      Integrable (fun p : ((((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × (Fin N → ℝ)) ×
        (ℝ × ℝ) => ∫ σ : Fin 2 → PerceptronSpin N, G σ
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
            fun x : PerceptronSpin N => A_old p.1 x.1 + ((x.2 : ℤˣ) : ℝ) * Y_last p.2))
        (P₀.prod P₁) := by
    obtain ⟨C, hC⟩ := exists_abs_le_of_finite G
    let F_obs (_ω : InterpSPDisorder N M) (x : Fin 2 → InterpSPState N M) : ℝ :=
      G (fun l => (x l).1)
    have hFm : Measurable fun p : InterpSPDisorder N M × (Fin 2 → InterpSPState N M) =>
        F_obs p.1 p.2 :=
      (measurable_of_finite G).comp (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd))
    have hm_sp := measurable_integral_pi_tilted (μ := interpSPBase N M)
      (measurable_interpSPEnergy hu s 0 q r) hFm
    have hi_sp : Integrable (fun ω => ∫ x : Fin 2 → InterpSPState N M, G (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω)))
        (interpSPDisorder N M v) :=
      Integrable.of_bound hm_sp.aestronglyMeasurable |C| (ae_of_all _ fun ω => by
        have := isProbabilityMeasure_tilted_interpSPEnergy hu hB s 0 q r ω
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_forall_abs_le _ fun _ => (hC _).trans (le_abs_self _))
    have hi_comp := hmp_reassoc.symm.integrable_comp_of_integrable hi_sp
    refine hi_comp.congr (ae_of_all _ fun p => ?_)
    dsimp only [Function.comp_apply]
    rw [hpt_aux (e_reassoc.symm p) G, MeasurableEquiv.apply_symm_apply]
  have hν_zero (G : (Fin 2 → PerceptronSpin N) → ℝ) :
      ∫ ω, ∫ x : Fin 2 → InterpSPState N M, G (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
        ∂(interpSPDisorder N M v) =
      ∫ ω₀, ∫ ω₁, ∫ σ : Fin 2 → PerceptronSpin N, G σ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
          fun x : PerceptronSpin N => A_old ω₀ x.1 + ((x.2 : ℤˣ) : ℝ) * Y_last ω₁)
        ∂P₁ ∂P₀ := by
    simp_rw [hpt_aux _ G]
    let I_p (p : ((((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × (Fin N → ℝ)) × (ℝ × ℝ)) :=
      ∫ σ : Fin 2 → PerceptronSpin N, G σ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
          fun x : PerceptronSpin N => A_old p.1 x.1 + ((x.2 : ℤˣ) : ℝ) * Y_last p.2)
    change (∫ ω, I_p (e_reassoc ω) ∂(interpSPDisorder N M v)) = ∫ ω₀, ∫ ω₁, I_p (ω₀, ω₁) ∂P₁ ∂P₀
    have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; infer_instance
    have hP₁ : IsProbabilityMeasure P₁ := by dsimp [P₁]; infer_instance
    rw [hmp_reassoc.integral_comp_of_aestronglyMeasurable (hint_Ip G).aestronglyMeasurable,
      integral_prod I_p (hint_Ip G)]
  let R_old (ρ : Fin 2 → Fin N → ℤˣ) : ℝ :=
    ((∑ i, ((ρ 0 i : ℤ) : ℝ) * ((ρ 1 i : ℤ) : ℝ)) / (N + 1)) - q
  have hdec (F_old : (Fin 2 → Fin N → ℤˣ) → ℝ) :
      ∫ ω, ∫ x : Fin 2 → InterpSPState N M,
        (F_old (fun l => (x l).1.1) * ((((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
        ∂(interpSPDisorder N M v) =
      q * ∫ ω, ∫ x : Fin 2 → InterpSPState N M, F_old (fun l => (x l).1.1)
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
        ∂(interpSPDisorder N M v) := by
    rw [hν_zero (fun σ => F_old (fun l => (σ l).1) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))),
      hν_zero (fun σ => F_old (fun l => (σ l).1))]
    have h1 := integral_integral_pi_count_tilted_decoupled_spin (n := 2) P₀ P₁ A_old Y_last
      F_old Finset.univ
    have h2 := integral_integral_pi_count_tilted_decoupled_spin (n := 2) P₀ P₁ A_old Y_last
      F_old ∅
    have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
    have hprod2 (σ : Fin 2 → PerceptronSpin N) :
        ∏ l ∈ (Finset.univ : Finset (Fin 2)), (((σ l).2 : ℤˣ) : ℝ) =
          (((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ) := Fin.prod_univ_two _
    simp only [hcard, hprod2] at h1
    have hP₁ : IsProbabilityMeasure P₁ := by dsimp [P₁]; infer_instance
    simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one, integral_const,
      probReal_univ, one_smul, one_mul] at h2
    have hyz_q : ∫ ω₁, Real.tanh (Y_last ω₁) ^ 2 ∂P₁ = q := h_tanh_yz
    rw [hyz_q] at h1
    rw [h1, h2]
  have h_alg (σ : Fin 2 → PerceptronSpin N) :
      ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ) - q) * (R_spin (σ 0) (σ 1) - q) =
      (R_old (fun l => (σ l).1) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ)) -
        q * R_old (fun l => (σ l).1)) +
      ((1 / (N + 1)) - (q / (N + 1)) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))) := by
    have hε0 : (((σ 0).2 : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
    have hε1 : (((σ 1).2 : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
    dsimp only [R_spin, R_old]
    have hprod : ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ)) ^ 2 = 1 := by
      rw [mul_pow, hε0, hε1, mul_one]
    linear_combination (1 / ((N : ℝ) + 1)) * hprod
  have hlin (G₁ G₂ : (Fin 2 → PerceptronSpin N) → ℝ) (c₁ c₂ : ℝ) :
      (∫ ω, ∫ x : Fin 2 → InterpSPState N M,
        (c₁ * G₁ (fun l => (x l).1) + c₂ * G₂ (fun l => (x l).1))
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
        ∂(interpSPDisorder N M v)) =
      c₁ * (∫ ω, ∫ x : Fin 2 → InterpSPState N M, G₁ (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
        ∂(interpSPDisorder N M v)) +
      c₂ * (∫ ω, ∫ x : Fin 2 → InterpSPState N M, G₂ (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
        ∂(interpSPDisorder N M v)) := by
    rw [hν_zero (fun σ => c₁ * G₁ σ + c₂ * G₂ σ), hν_zero G₁, hν_zero G₂]
    have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; infer_instance
    have hP₁ : IsProbabilityMeasure P₁ := by dsimp [P₁]; infer_instance
    have hpt1 (ω₀ : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ)) × (Fin N → ℝ))
        (ω₁ : ℝ × ℝ) :
        (∫ σ : Fin 2 → PerceptronSpin N, (c₁ * G₁ σ + c₂ * G₂ σ)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
            fun x : PerceptronSpin N => A_old ω₀ x.1 + ((x.2 : ℤˣ) : ℝ) * Y_last ω₁)) =
        c₁ * (∫ σ : Fin 2 → PerceptronSpin N, G₁ σ
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
            fun x : PerceptronSpin N => A_old ω₀ x.1 + ((x.2 : ℤˣ) : ℝ) * Y_last ω₁)) +
        c₂ * (∫ σ : Fin 2 → PerceptronSpin N, G₂ σ
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
            fun x : PerceptronSpin N => A_old ω₀ x.1 + ((x.2 : ℤˣ) : ℝ) * Y_last ω₁)) := by
      have heq : (fun σ : Fin 2 → PerceptronSpin N => c₁ * G₁ σ + c₂ * G₂ σ) =
          (fun σ => c₁ * G₁ σ) + (fun σ => c₂ * G₂ σ) := rfl
      rw [heq, integral_add' Integrable.of_finite Integrable.of_finite,
        integral_const_mul, integral_const_mul]
    simp_rw [hpt1]
    have hi1 := hint_Ip G₁
    have hi2 := hint_Ip G₂
    have hfub1 := (integral_prod _ ((hi1.const_mul c₁).add (hi2.const_mul c₂))).symm
    dsimp only [Pi.add_apply] at hfub1
    rw [hfub1, integral_add (hi1.const_mul c₁) (hi2.const_mul c₂),
      integral_const_mul, integral_const_mul,
      integral_prod _ hi1, integral_prod _ hi2]
  have hone : ∫ ω, ∫ _x : Fin 2 → InterpSPState N M, (1 : ℝ)
      ∂(Measure.pi fun _ : Fin 2 => (interpSPBase N M).tilted (interpSPEnergy u s 0 q r ω))
      ∂(interpSPDisorder N M v) = 1 := by
    have (ω : InterpSPDisorder N M) := isProbabilityMeasure_tilted_interpSPEnergy hu hB s 0 q r ω
    simp
  let G_A1 (σ : Fin 2 → PerceptronSpin N) : ℝ :=
    R_old (fun l => (σ l).1) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))
  let G_A2 (σ : Fin 2 → PerceptronSpin N) : ℝ := R_old (fun l => (σ l).1)
  let G_B2 (σ : Fin 2 → PerceptronSpin N) : ℝ :=
    (1 : ℝ) * ((((σ 0).2 : ℤ) : ℝ) * (((σ 1).2 : ℤ) : ℝ))
  let A_tot (σ : Fin 2 → PerceptronSpin N) : ℝ := 1 * G_A1 σ + (-q) * G_A2 σ
  let B_tot (σ : Fin 2 → PerceptronSpin N) : ℝ :=
    (1 / ((N : ℝ) + 1)) * (fun _ : Fin 2 → PerceptronSpin N => (1 : ℝ)) σ +
      (-(q / ((N : ℝ) + 1))) * G_B2 σ
  have hf_eq (x : Fin 2 → InterpSPState N M) :
      ((((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ) - q) *
        (R_spin (x 0).1 (x 1).1 - q) =
      1 * A_tot (fun l => (x l).1) + 1 * B_tot (fun l => (x l).1) := by
    rw [h_alg (fun l => (x l).1)]
    dsimp only [A_tot, B_tot, G_A1, G_A2, G_B2]
    ring
  simp_rw [hf_eq]
  rw [hlin A_tot B_tot 1 1,
    show A_tot = fun σ => 1 * G_A1 σ + (-q) * G_A2 σ from rfl,
    show B_tot = fun σ => (1 / ((N : ℝ) + 1)) * (fun _ => (1 : ℝ)) σ +
      (-(q / ((N : ℝ) + 1))) * G_B2 σ from rfl,
    hlin G_A1 G_A2 1 (-q), hlin (fun _ => (1 : ℝ)) G_B2 _ _,
    hdec R_old, hdec (fun _ => (1 : ℝ)), hone]
  ring

end DefinitionsAndBasic

section SplitAndSymmetry

/-- Measurable equivalence splitting `InterpSPState N (M + 1)` into `InterpSPState N M × (Fin 2 → ℝ)`. -/
private def interpSPStateSplit (N M : ℕ) :
    InterpSPState N (M + 1) ≃ᵐ InterpSPState N M × (Fin 2 → ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (PerceptronSpin N))
    (MeasurableEquiv.finSuccProd (Fin 2 → ℝ) M)).trans MeasurableEquiv.prodAssoc.symm

private lemma interpSPStateSplit_apply {N M : ℕ} (x : InterpSPState N (M + 1)) :
    interpSPStateSplit N M x = ((x.1, Fin.init x.2), x.2 (Fin.last M)) := by
  simp [interpSPStateSplit, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_prodCongr,
    MeasurableEquiv.coe_refl, Fin.init_def]

private lemma measurePreserving_interpSPStateSplit (N M : ℕ) :
    MeasurePreserving ⇑(interpSPStateSplit N M)
      (interpSPBase N (M + 1))
      ((interpSPBase N M).prod (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) := by
  unfold interpSPBase interpSPStateSplit
  exact (measurePreserving_prodAssoc _ _ _).symm.comp
    ((MeasurePreserving.id _).prod (measurePreserving_finSuccProd _ M))

/-- Splitting the `(M + 1)`-constraint disorder `InterpSPDisorder N (M + 1)` into the `M`-constraint
disorder `InterpSPDisorder N M` and the independent standard Gaussian block `((g_M, a_M), z_M)`
indexed by `(Fin N ⊕ Unit) ⊕ Unit` is measure-preserving. -/
private lemma measurePreserving_interpSPDisorder_lastSplit (N M : ℕ) (v : ℝ≥0) :
    MeasurePreserving
      (fun ω : InterpSPDisorder N (M + 1) =>
        (((((Fin.init ω.1.1.1, Fin.init ω.1.1.2), Fin.init ω.1.2), ω.2) : InterpSPDisorder N M),
          (Sum.elim (Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)))
            (fun _ : Unit => ω.1.2 (Fin.last M)) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ)))
      (interpSPDisorder N (M + 1) v)
      ((interpSPDisorder N M v).prod
        (Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1)) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let G₀ := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ
  let gM := Measure.pi fun _ : Fin N => γ
  let A₀ := Measure.pi fun _ : Fin M => γ
  let Z₀ := Measure.pi fun _ : Fin M => γ
  let Rest := (Measure.pi fun _ : Fin N => γ).prod ((gaussianReal 0 v).prod γ)
  have hg := measurePreserving_finSuccProd gM M
  have ha := measurePreserving_finSuccProd γ M
  have hz := measurePreserving_finSuccProd γ M
  have hunit := (measurePreserving_funUnique γ Unit).symm
  have hsum1 := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin N ⊕ Unit => ℝ)
    (fun _ => γ)).comp ((MeasurePreserving.id gM).prod hunit)
  have hsum2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : (Fin N ⊕ Unit) ⊕ Unit => ℝ) (fun _ => γ)).comp
    (hsum1.prod hunit)
  have step1 : MeasurePreserving
      (Prod.map (Prod.map (Prod.map (MeasurableEquiv.finSuccProd (Fin N → ℝ) M)
        (MeasurableEquiv.finSuccProd ℝ M)) (MeasurableEquiv.finSuccProd ℝ M)) id)
      (interpSPDisorder N (M + 1) v)
      ((((G₀.prod gM).prod (A₀.prod γ)).prod (Z₀.prod γ)).prod Rest) := by
    unfold interpSPDisorder
    exact ((hg.prod ha).prod hz).prod (MeasurePreserving.id Rest)
  have step2 := ((measurePreserving_prodProdProdComm G₀ gM A₀ γ).prod
    (MeasurePreserving.id (Z₀.prod γ))).prod (MeasurePreserving.id Rest)
  have step3 := (measurePreserving_prodProdProdComm (G₀.prod A₀) (gM.prod γ) Z₀ γ).prod
    (MeasurePreserving.id Rest)
  have step4 := measurePreserving_prodAssoc ((G₀.prod A₀).prod Z₀) ((gM.prod γ).prod γ) Rest
  have step5 := (MeasurePreserving.id ((G₀.prod A₀).prod Z₀)).prod
    (Measure.measurePreserving_swap (μ := (gM.prod γ).prod γ) (ν := Rest))
  have step6 := (measurePreserving_prodAssoc ((G₀.prod A₀).prod Z₀) Rest ((gM.prod γ).prod γ)).symm
  have step7 := (MeasurePreserving.id (((G₀.prod A₀).prod Z₀).prod Rest)).prod hsum2
  have full := step7.comp (step6.comp (step5.comp (step4.comp (step3.comp (step2.comp step1)))))
  have hcod : ((((G₀.prod A₀).prod Z₀).prod Rest).prod
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => γ)) =
      (interpSPDisorder N M v).prod
        (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := rfl
  rw [hcod] at full
  convert full using 1
  ext ω : 1
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.prodAssoc, Fin.init_def]
  · ext idx
    rcases idx with (i | _) | _ <;>
      simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]

/-- Energy split of `interpSPEnergy` at `Fin.last M`, matching `X_fn` of `InterpolatingCavityBound`. -/
private lemma interpSPEnergy_eq_init_add {N M : ℕ} (u : ℝ → ℝ) (s t q r : ℝ)
    (ω : InterpSPDisorder N (M + 1)) (x : InterpSPState N (M + 1)) :
    let ω₀ : InterpSPDisorder N M :=
      (((Fin.init ω.1.1.1, Fin.init ω.1.1.2), Fin.init ω.1.2), ω.2)
    let w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ :=
      Sum.elim (Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)))
        (fun _ : Unit => ω.1.2 (Fin.last M))
    let x₀ : InterpSPState N M := (x.1, Fin.init x.2)
    let η : Fin 2 → ℝ := x.2 (Fin.last M)
    interpSPEnergy u s t q r ω x =
      interpSPEnergy u s t q r ω₀ x₀ +
      u (Sum.elim (Real.sqrt s • cavityCoef N t x.1)
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
        ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
          Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ η) := by
  intro ω₀ w₁ x₀ η
  unfold interpSPEnergy
  rw [Fin.sum_univ_castSucc]
  have hinit (k : Fin M) : interpSPField s t q ω x k.castSucc = interpSPField s t q ω₀ x₀ k := rfl
  have hlast : interpSPField s t q ω x (Fin.last M) =
      Sum.elim (Real.sqrt s • cavityCoef N t x.1)
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ η := by
    unfold interpSPField
    have hnoaux : smartPathFieldNoAux t (ω.1.1, ω.2.2.1) (x.1, 0) (Fin.last M) =
        cavityCoef N t x.1 ⬝ᵥ
          Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)) := by
      simp only [smartPathFieldNoAux_eq, cavityCoef, dotProduct, Fintype.sum_sum_type,
        Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) (by ring)
      push_cast; ring
    rw [hnoaux]
    dsimp only [w₁, η]
    rw [sumElim_dotProduct_sumElim, smul_dotProduct, smul_eq_mul]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp_rw [hinit, hlast]
  ring

/-- **Transport of a jointly measurable split last-constraint replica average to the full
`(M + 1)`-constraint `(s, t)`-interpolating smart path.** -/
private lemma integral_pi_interpSP_last_split_eq
    {N M : ℕ} {J : Type uR} [Fintype J]
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s t q r : ℝ) (v : ℝ≥0)
    {G : (InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) →
      (J → InterpSPState N M × (Fin 2 → ℝ)) → ℝ}
    (hGm : Measurable fun p : (InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (J → InterpSPState N M × (Fin 2 → ℝ)) => G p.1 p.2) :
    let P₀ := interpSPDisorder N M v
    let P₁ := interpSPDisorder N (M + 1) v
    let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
    let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let μ₀ (ω₀ : InterpSPDisorder N M) :=
      (interpSPBase N M).tilted (interpSPEnergy u s t q r ω₀)
    let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
      Sum.elim (Real.sqrt s • cavityCoef N t y.1.1)
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ y.2
    let splitΩ (ω : InterpSPDisorder N (M + 1)) :
        InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) :=
      ((((Fin.init ω.1.1.1, Fin.init ω.1.1.2), Fin.init ω.1.2), ω.2),
        Sum.elim (Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)))
          (fun _ : Unit => ω.1.2 (Fin.last M)))
    ∫ p, ∫ a : J → InterpSPState N M × (Fin 2 → ℝ), G p a
        ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y)))
        ∂(P₀.prod γ₁) =
      ∫ ω, ∫ x : J → InterpSPState N (M + 1),
        G (splitΩ ω) (fun j => interpSPStateSplit N M (x j))
        ∂(Measure.pi fun _ : J => (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω))
        ∂P₁ := by
  intro P₀ P₁ γ₁ γ₂ μ₀ X_fn splitΩ
  -- Measurability of `I p` on `P₀.prod γ₁`!
  let H_comb (p : InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ))
      (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
    interpSPEnergy u s t q r p.1 y.1 + u (X_fn p.2 y)
  have hHm : Measurable fun p : (InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (InterpSPState N M × (Fin 2 → ℝ)) => H_comb p.1 p.2 := by
    have hp1 : Measurable fun p : (InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (InterpSPState N M × (Fin 2 → ℝ)) => (p.1.1, p.2.1) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    have hE0 := (measurable_interpSPEnergy (N := N) (M := M) hu s t q r).comp hp1
    have hX1 (j : (Fin N ⊕ Unit) ⊕ Unit) :
        Measurable fun p : (InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (InterpSPState N M × (Fin 2 → ℝ)) =>
          (Sum.elim (Real.sqrt s • cavityCoef N t p.2.1.1)
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j :=
      (measurable_of_finite fun σ =>
        (Sum.elim (Real.sqrt s • cavityCoef N t σ)
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : (InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (InterpSPState N M × (Fin 2 → ℝ)) =>
        Sum.elim (Real.sqrt s • cavityCoef N t p.2.1.1)
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.1.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hX1 j).mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst))
    have hd2 : Measurable fun p : (InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (InterpSPState N M × (Fin 2 → ℝ)) =>
        ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
          Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hE0.add (hu.comp (hd1.add hd2))
  have hν_eq (p : InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) :
      ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y)) =
      ((interpSPBase N M).prod γ₂).tilted (H_comb p) := by
    rw [← tilted_prod_comp_fst, tilted_tilted
      ((integrable_exp_interpSPEnergy hu hB s t q r p.1).comp_fst γ₂)]
    rfl
  let I_fn (p : InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ a : J → InterpSPState N M × (Fin 2 → ℝ), G p a
      ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y)))
  have hIm : Measurable I_fn := by
    have heq_I : I_fn = fun p => ∫ a, G p a
        ∂(Measure.pi fun _ : J => ((interpSPBase N M).prod γ₂).tilted (H_comb p)) := by
      funext p; dsimp only [I_fn]; simp_rw [hν_eq p]
    rw [heq_I]
    have : IsFiniteMeasure ((interpSPBase N M).prod γ₂) := inferInstance
    exact measurable_integral_pi_tilted (μ := (interpSPBase N M).prod γ₂) hHm hGm
  have hmp_dis := measurePreserving_interpSPDisorder_lastSplit N M v
  rw [← hmp_dis.integral_comp_of_aestronglyMeasurable hIm.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only [I_fn]
  rw [hν_eq (splitΩ ω)]
  have : IsProbabilityMeasure ((interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)) :=
    isProbabilityMeasure_tilted_interpSPEnergy hu hB s t q r ω
  have hmap_st : ((interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)).map
      (interpSPStateSplit N M) = ((interpSPBase N M).prod γ₂).tilted (H_comb (splitΩ ω)) := by
    rw [map_tilted_measurableEquiv (interpSPStateSplit N M)
      (measurePreserving_interpSPStateSplit N M)
      (measurable_interpSPEnergy_slice hu s t q r ω)]
    congr 1; funext y
    obtain ⟨x, rfl⟩ := (interpSPStateSplit N M).surjective y
    change interpSPEnergy u s t q r ω ((interpSPStateSplit N M).symm (interpSPStateSplit N M x)) = _
    rw [MeasurableEquiv.symm_apply_apply, interpSPEnergy_eq_init_add u s t q r ω x,
      interpSPStateSplit_apply]
  rw [← hmap_st]
  exact integral_pi_map_equiv _ (interpSPStateSplit N M) (G (splitΩ ω))

/-- Swap constraints `k₁ ↔ k₂` on `InterpSPState N M`. -/
private def interpSPStateSwap {N M : ℕ} (k₁ k₂ : Fin M) :
    InterpSPState N M ≃ᵐ InterpSPState N M where
  toFun x := (x.1, fun k => x.2 (Equiv.swap k₁ k₂ k))
  invFun x := (x.1, fun k => x.2 (Equiv.swap k₁ k₂ k))
  left_inv x := Prod.ext rfl (funext fun k => by simp)
  right_inv x := Prod.ext rfl (funext fun k => by simp)
  measurable_toFun := measurable_fst.prodMk (measurable_pi_iff.2 fun k =>
    (measurable_pi_apply (Equiv.swap k₁ k₂ k)).comp measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_pi_iff.2 fun k =>
    (measurable_pi_apply (Equiv.swap k₁ k₂ k)).comp measurable_snd)

private lemma measurePreserving_interpSPStateSwap {N M : ℕ} (k₁ k₂ : Fin M) :
    MeasurePreserving ⇑(interpSPStateSwap (N := N) k₁ k₂) (interpSPBase N M) (interpSPBase N M) := by
  unfold interpSPBase
  have h : MeasurePreserving (fun ξ : Fin M → Fin 2 → ℝ => fun k => ξ (Equiv.swap k₁ k₂ k))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
    measurePreserving_pi_comp_injective _ (Equiv.injective _)
  exact (MeasurePreserving.id _).prod h

/-- Swap constraints `k₁ ↔ k₂` on `InterpSPDisorder N M`. -/
private def interpSPDisorderSwap {N M : ℕ} (k₁ k₂ : Fin M) (ω : InterpSPDisorder N M) :
    InterpSPDisorder N M :=
  (((fun k => ω.1.1.1 (Equiv.swap k₁ k₂ k), fun k => ω.1.1.2 (Equiv.swap k₁ k₂ k)),
    fun k => ω.1.2 (Equiv.swap k₁ k₂ k)), ω.2)

private lemma measurePreserving_interpSPDisorderSwap {N M : ℕ} (v : ℝ≥0) (k₁ k₂ : Fin M) :
    MeasurePreserving (interpSPDisorderSwap (N := N) k₁ k₂)
      (interpSPDisorder N M v) (interpSPDisorder N M v) := by
  unfold interpSPDisorder
  have h1 := measurePreserving_pi_comp_injective
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) (Equiv.swap k₁ k₂).injective
  have h2 := measurePreserving_pi_comp_injective (gaussianReal 0 1) (Equiv.swap k₁ k₂).injective
  exact ((h1.prod h2).prod h2).prod (MeasurePreserving.id _)

private lemma interpSPField_swap {N M : ℕ} (s t q : ℝ) (k₁ k₂ : Fin M)
    (ω : InterpSPDisorder N M) (x : InterpSPState N M) (k : Fin M) :
    interpSPField s t q (interpSPDisorderSwap k₁ k₂ ω) x k =
      interpSPField s t q ω (interpSPStateSwap k₁ k₂ x) (Equiv.swap k₁ k₂ k) := by
  simp [interpSPField, smartPathFieldNoAux_eq, interpSPDisorderSwap, interpSPStateSwap]

private lemma interpSPEnergy_swap {N M : ℕ} (u : ℝ → ℝ) (s t q r : ℝ) (k₁ k₂ : Fin M)
    (ω : InterpSPDisorder N M) (x : InterpSPState N M) :
    interpSPEnergy u s t q r (interpSPDisorderSwap k₁ k₂ ω) x =
      interpSPEnergy u s t q r ω (interpSPStateSwap k₁ k₂ x) := by
  unfold interpSPEnergy
  have h := Equiv.sum_comp (Equiv.swap k₁ k₂)
    (fun k => u (interpSPField s t q ω (interpSPStateSwap k₁ k₂ x) k))
  simp_rw [interpSPField_swap]
  rw [h]
  rfl

private lemma tilted_interpSP_swap {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (s t q r : ℝ) (k₁ k₂ : Fin M) (ω : InterpSPDisorder N M) :
    (interpSPBase N M).tilted (interpSPEnergy u s t q r (interpSPDisorderSwap k₁ k₂ ω)) =
      ((interpSPBase N M).tilted (interpSPEnergy u s t q r ω)).map (interpSPStateSwap k₁ k₂) := by
  rw [map_tilted_measurableEquiv (interpSPStateSwap k₁ k₂)
    (measurePreserving_interpSPStateSwap k₁ k₂)
    (measurable_interpSPEnergy_slice hu s t q r ω)]
  congr 1; funext x
  exact interpSPEnergy_swap u s t q r k₁ k₂ ω x

end SplitAndSymmetry

section TimeDerivative

/-- Derivative of `interpSPEnergy` in `t ∈ (0, 1)`. -/
private noncomputable def interpSPEnergyDeriv {N M : ℕ} (u : ℝ → ℝ) (s t q : ℝ)
    (ω : InterpSPDisorder N M) (x : InterpSPState N M) : ℝ :=
  (∑ k : Fin M, deriv u (interpSPField s t q ω x k) *
    (Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
      (ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t - x.2 k 0 / Real.sqrt (1 - t))))) -
    ((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * Real.sqrt (1 - t))

private lemma measurable_interpSPEnergyDeriv {N M : ℕ} (u : ℝ → ℝ) (s t q : ℝ) :
    Measurable fun p : InterpSPDisorder N M × InterpSPState N M =>
      interpSPEnergyDeriv u s t q p.1 p.2 := by
  have hdu := measurable_deriv u
  unfold interpSPEnergyDeriv
  refine (Finset.measurable_sum _ fun k _ =>
    (hdu.comp (measurable_interpSPField s t q k)).mul ?_).sub ?_
  · fun_prop
  · fun_prop

private lemma hasDerivAt_interpSPEnergy {N M : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (s q r : ℝ)
    (ω : InterpSPDisorder N M) (x : InterpSPState N M) :
    HasDerivAt (fun t' => interpSPEnergy u s t' q r ω x)
      (interpSPEnergyDeriv u s t q ω x) t := by
  have hY := ((hasDerivAt_id t).const_sub 1).sqrt (sub_pos.2 ht.2).ne'
  have hlast : HasDerivAt
      (fun t' => ((x.1.2 : ℤ) : ℝ) *
        (Real.sqrt (1 - t') * ω.2.2.1 + Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r))
      (-((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * Real.sqrt (1 - t))) t := by
    have h1 := ((hY.mul_const ω.2.2.1).add_const
      (Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r)).const_mul ((x.1.2 : ℤ) : ℝ)
    refine h1.congr_deriv ?_
    simp only [id_eq]; ring
  have hS (k : Fin M) : HasDerivAt (fun t' => interpSPField s t' q ω x k)
      (Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t - x.2 k 0 / Real.sqrt (1 - t)))) t := by
    have hf0 := hasDerivAt_perceptron_smart_path_field ht (ω.1.1.1 k) (ω.1.1.2 k)
      x.1.1 x.1.2 (x.2 k 0)
    have hf1 := (hf0.const_mul (Real.sqrt s)).add_const
      (Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k 1))
    exact hf1
  have hsum : HasDerivAt (fun t' => ∑ k : Fin M, u (interpSPField s t' q ω x k))
      (∑ k : Fin M, deriv u (interpSPField s t q ω x k) *
        (Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
          (ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t - x.2 k 0 / Real.sqrt (1 - t))))) t :=
    HasDerivAt.fun_sum fun k _ => (hu _).hasDerivAt.comp t (hS k)
  have htot := (hsum.add_const
    (∑ i : Fin N, ((x.1.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r)).add hlast
  refine htot.congr_deriv ?_
  unfold interpSPEnergyDeriv; ring

/-- Dominated differentiation of `t ↦ ν_{t, s}(f)` on `t ∈ (0, 1)`. -/
private lemma hasDerivAt_integral_interpSP {N M : ℕ} {R : Type uR} [Fintype R]
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q r : ℝ) (v : ℝ≥0)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D)
    (f : (R → PerceptronSpin N) → ℝ) :
    let P := interpSPDisorder N M v
    let μ (t' : ℝ) (ω : InterpSPDisorder N M) :=
      (interpSPBase N M).tilted (interpSPEnergy u s t' q r ω)
    HasDerivAt
      (fun t' => ∫ ω, ∫ x : R → InterpSPState N M, f (fun l => (x l).1)
        ∂(Measure.pi fun _ : R => μ t' ω) ∂P)
      (∫ ω, (∑ i : R, ∫ σ : Option R → InterpSPState N M,
            f (fun j => (σ (some j)).1) * interpSPEnergyDeriv u s t q ω (σ (some i))
            ∂(Measure.pi fun _ : Option R => μ t ω)) -
          (Fintype.card R : ℝ) * ∫ σ : Option R → InterpSPState N M,
            f (fun j => (σ (some j)).1) * interpSPEnergyDeriv u s t q ω (σ none)
            ∂(Measure.pi fun _ : Option R => μ t ω) ∂P) t := by
  intro P μ
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  obtain ⟨δ, hδ, hδt, hδ1⟩ := exists_pos_lt_of_mem_Ioo ht
  let V_set := Ioo δ (1 - δ)
  have htV : t ∈ V_set := ⟨hδt, by linarith⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hs_sqrt : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs.2
  have hs1_sqrt : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.2 (by linarith [hs.1])
  let A_env (ω : InterpSPDisorder N M) : ℝ :=
    M * B + |Real.sqrt r| * (∑ i : Fin N, |ω.2.1 i|) +
      (|ω.2.2.1| + |Real.sqrt r| * |ω.2.2.2|)
  have hEb (t' : ℝ) (ht' : t' ∈ V_set) (ω : InterpSPDisorder N M) (x : InterpSPState N M) :
      |interpSPEnergy u s t' q r ω x| ≤ A_env ω := by
    unfold interpSPEnergy
    have h1 : |∑ k : Fin M, u (interpSPField s t' q ω x k)| ≤ M * B :=
      (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ => hB _).trans_eq (by simp)
    have h2 : |∑ i : Fin N, ((x.1.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2.1 i * Real.sqrt r| ≤
        |Real.sqrt r| * ∑ i : Fin N, |ω.2.1 i| := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have : Real.sqrt (1 - s) * |ω.2.1 i| ≤ 1 * |ω.2.1 i| :=
        mul_le_mul_of_nonneg_right hs1_sqrt (abs_nonneg _)
      linarith [mul_le_mul_of_nonneg_right this (abs_nonneg (Real.sqrt r))]
    have h3 : |((x.1.2 : ℤ) : ℝ) *
        (Real.sqrt (1 - t') * ω.2.2.1 + Real.sqrt (1 - s) * ω.2.2.2 * Real.sqrt r)| ≤
        |ω.2.2.1| + |Real.sqrt r| * |ω.2.2.2| := by
      rw [abs_mul, abs_units_cast_eq_one, one_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        have ht'_le : Real.sqrt (1 - t') ≤ 1 :=
          Real.sqrt_le_one.2 (by linarith [hδ.trans ht'.1])
        calc Real.sqrt (1 - t') * |ω.2.2.1| ≤ 1 * |ω.2.2.1| :=
              mul_le_mul_of_nonneg_right ht'_le (abs_nonneg _)
          _ = |ω.2.2.1| := one_mul _
      · rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (1 - s) * |ω.2.2.2| * |Real.sqrt r|
            ≤ 1 * |ω.2.2.2| * |Real.sqrt r| :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hs1_sqrt (abs_nonneg _)) (abs_nonneg _)
          _ = |Real.sqrt r| * |ω.2.2.2| := by ring
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add h1 h2) h3)
  let K_c : ℝ := 1 / (2 * Real.sqrt δ) + D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ
  have hKc0 : 0 ≤ K_c := by dsimp only [K_c]; positivity
  let Q_env (ω : InterpSPDisorder N M) : ℝ :=
    K_c * Real.exp (|ω.2.2.1| + ∑ k : Fin M, |ω.1.1.2 k|)
  let b_env (x : InterpSPState N M) : ℝ := 1 + ∑ k : Fin M, |x.2 k 0|
  have hb_int : Integrable b_env (interpSPBase N M) := by
    refine (integrable_const (1 : ℝ)).add (integrable_finsetSum _ fun k _ => ?_)
    unfold interpSPBase
    have h0 : Integrable (fun v2 : Fin 2 → ℝ => |v2 0|)
        (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
      (integrable_comp_eval (μ := fun _ : Fin 2 => gaussianReal 0 1) (i := 0)
        IsGaussian.integrable_id).abs
    have hk : Integrable (fun ξ : Fin M → Fin 2 → ℝ => |ξ k 0|)
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
      integrable_comp_eval (μ := fun _ : Fin M => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
        (i := k) h0
    exact hk.comp_snd _
  have hdb (t' : ℝ) (ht' : t' ∈ V_set) (ω : InterpSPDisorder N M) (x : InterpSPState N M) :
      |interpSPEnergyDeriv u s t' q ω x| ≤ Q_env ω * b_env x := by
    unfold interpSPEnergyDeriv
    have hδ0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hst' : Real.sqrt δ ≤ Real.sqrt t' := Real.sqrt_le_sqrt ht'.1.le
    have hs1t' : Real.sqrt δ ≤ Real.sqrt (1 - t') := Real.sqrt_le_sqrt (by linarith [ht'.2])
    have hy_bd : |((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * Real.sqrt (1 - t'))| ≤
        |ω.2.2.1| / (2 * Real.sqrt δ) := by
      rw [abs_div, abs_mul, abs_units_cast_eq_one, one_mul,
        abs_of_pos (mul_pos zero_lt_two (Real.sqrt_pos.2 (sub_pos.2 (ht'.2.trans_le (by linarith)))))]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos zero_lt_two hδ0)
        (mul_le_mul_of_nonneg_left hs1t' zero_le_two)
    have hsum_bd : |∑ k : Fin M, deriv u (interpSPField s t' q ω x k) *
        (Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
          (ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t' - x.2 k 0 / Real.sqrt (1 - t'))))| ≤
        D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ *
          ((∑ k, |ω.1.1.2 k|) + ∑ k, |x.2 k 0|) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm (k : Fin M) :
          |deriv u (interpSPField s t' q ω x k) *
            (Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
              (ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t' - x.2 k 0 / Real.sqrt (1 - t'))))| ≤
          (D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ) *
            (|ω.1.1.2 k| + |x.2 k 0|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg s),
          abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ)))]
        have ht1 : |ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t'| ≤
            |ω.1.1.2 k| / Real.sqrt δ := by
          rw [abs_div, abs_mul, abs_units_cast_eq_one, mul_one,
            abs_of_pos (Real.sqrt_pos.2 (hδ.trans ht'.1))]
          exact div_le_div_of_nonneg_left (abs_nonneg _) hδ0 hst'
        have ht2 : |x.2 k 0 / Real.sqrt (1 - t')| ≤ |x.2 k 0| / Real.sqrt δ := by
          rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (sub_pos.2 (ht'.2.trans_le (by linarith))))]
          exact div_le_div_of_nonneg_left (abs_nonneg _) hδ0 hs1t'
        have hdiff_k : |ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t' -
            x.2 k 0 / Real.sqrt (1 - t')| ≤ (|ω.1.1.2 k| + |x.2 k 0|) / Real.sqrt δ := by
          refine (abs_sub _ _).trans ((add_le_add ht1 ht2).trans_eq (by ring))
        have hs_mul : Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            |ω.1.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t' - x.2 k 0 / Real.sqrt (1 - t')|) ≤
            1 * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
              ((|ω.1.1.2 k| + |x.2 k 0|) / Real.sqrt δ)) :=
          mul_le_mul hs_sqrt
            (mul_le_mul_of_nonneg_left hdiff_k (by positivity)) (by positivity) zero_le_one
        calc _ ≤ D * (1 * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
              ((|ω.1.1.2 k| + |x.2 k 0|) / Real.sqrt δ))) :=
              mul_le_mul (hD _) hs_mul (by positivity) hD0
          _ = _ := by ring
      calc _ ≤ ∑ k : Fin M, (D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ) *
              (|ω.1.1.2 k| + |x.2 k 0|) := Finset.sum_le_sum fun k _ => hterm k
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hY0 := abs_nonneg ω.2.2.1
    have hA0 : 0 ≤ ∑ k, |ω.1.1.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hX0 : 0 ≤ ∑ k, |x.2 k 0| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hp : 0 ≤ 1 / (2 * Real.sqrt δ) := by positivity
    have hr_c : 0 ≤ D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ := by positivity
    have e1 : |ω.2.2.1| + (∑ k, |ω.1.1.2 k|) + ∑ k, |x.2 k 0| ≤
        (1 + (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|)) * (1 + ∑ k, |x.2 k 0|) := by
      nlinarith [mul_nonneg (add_nonneg hY0 hA0) hX0]
    have e2 : 1 + (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|) ≤
        Real.exp (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|) := by
      linarith [Real.add_one_le_exp (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|)]
    calc _ ≤ |∑ k : Fin M, _| + |((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * Real.sqrt (1 - t'))| :=
          abs_sub _ _
      _ ≤ D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ *
            ((∑ k, |ω.1.1.2 k|) + ∑ k, |x.2 k 0|) + |ω.2.2.1| / (2 * Real.sqrt δ) :=
          add_le_add hsum_bd hy_bd
      _ ≤ K_c * (|ω.2.2.1| + (∑ k, |ω.1.1.2 k|) + ∑ k, |x.2 k 0|) := by
          dsimp only [K_c]
          have hdiv : |ω.2.2.1| / (2 * Real.sqrt δ) = 1 / (2 * Real.sqrt δ) * |ω.2.2.1| := by ring
          rw [hdiv]
          nlinarith [mul_nonneg hr_c hY0, mul_nonneg hp (add_nonneg hA0 hX0)]
      _ ≤ K_c * ((1 + (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|)) * (1 + ∑ k, |x.2 k 0|)) :=
          mul_le_mul_of_nonneg_left e1 hKc0
      _ ≤ K_c * (Real.exp (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|) * (1 + ∑ k, |x.2 k 0|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (by positivity)) hKc0
      _ = Q_env ω * b_env x := by dsimp only [Q_env, b_env]; ring
  have houter : Integrable (fun ω => Real.exp (2 * ((Fintype.card R : ℝ) * A_env ω)) * Q_env ω) P := by
    let nR : ℝ := Fintype.card R
    have ha_exp : Integrable (fun a : Fin M → ℝ => Real.exp (∑ k, |a k|))
        (Measure.pi fun _ : Fin M => gaussianReal 0 1) := by
      simpa only [one_mul] using integrable_exp_sum_mul_abs_pi (fun _ : Fin M => (1 : ℝ))
    have hz'_exp : Integrable
        (fun z' : Fin N → ℝ => Real.exp (∑ i, (2 * nR * |Real.sqrt r|) * |z' i|))
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
      integrable_exp_sum_mul_abs_pi (fun _ : Fin N => 2 * nR * |Real.sqrt r|)
    have hy_exp : Integrable (fun y : ℝ => Real.exp ((2 * nR + 1) * |y|)) (gaussianReal 0 v) :=
      integrable_exp_mul_abs_gaussianReal _
    have hzl_exp : Integrable (fun zl : ℝ => Real.exp ((2 * nR * |Real.sqrt r|) * |zl|))
        (gaussianReal 0 1) :=
      integrable_exp_mul_abs_gaussianReal _
    have h12 : Integrable (fun ga : (Fin M → Fin N → ℝ) × (Fin M → ℝ) =>
        Real.exp (∑ k, |ga.2 k|))
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := ha_exp.comp_snd _
    have h123 : Integrable (fun gaz : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ) =>
        Real.exp (∑ k, |gaz.1.2 k|))
        (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := h12.comp_fst _
    have hyz_exp : Integrable (fun yz : ℝ × ℝ =>
        Real.exp ((2 * nR + 1) * |yz.1|) * Real.exp ((2 * nR * |Real.sqrt r|) * |yz.2|))
        ((gaussianReal 0 v).prod (gaussianReal 0 1)) := hy_exp.mul_prod hzl_exp
    have hrest_exp : Integrable (fun r_p : (Fin N → ℝ) × (ℝ × ℝ) =>
        Real.exp (∑ i, (2 * nR * |Real.sqrt r|) * |r_p.1 i|) *
          (Real.exp ((2 * nR + 1) * |r_p.2.1|) * Real.exp ((2 * nR * |Real.sqrt r|) * |r_p.2.2|)))
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          ((gaussianReal 0 v).prod (gaussianReal 0 1))) := hz'_exp.mul_prod hyz_exp
    have hprod_all := (h123.mul_prod hrest_exp).const_mul (K_c * Real.exp (2 * nR * M * B))
    refine hprod_all.congr (ae_of_all _ fun ω => ?_)
    dsimp only [A_env, Q_env, nR]
    have hsum_z' : 2 * ((Fintype.card R : ℝ) * (|Real.sqrt r| * ∑ i : Fin N, |ω.2.1 i|)) =
        ∑ i : Fin N, (2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.1 i| := by
      rw [← Finset.mul_sum]; ring
    have hexp_eq :
        2 * ((Fintype.card R : ℝ) * A_env ω) + (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|) =
        (2 * (Fintype.card R : ℝ) * M * B) +
          (∑ k, |ω.1.1.2 k|) +
          (∑ i : Fin N, (2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.1 i|) +
          ((2 * (Fintype.card R : ℝ) + 1) * |ω.2.2.1|) +
          ((2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.2.2|) := by
      dsimp only [A_env]
      linear_combination hsum_z'
    calc K_c * Real.exp (2 * (Fintype.card R : ℝ) * M * B) *
          (Real.exp (∑ k, |ω.1.1.2 k|) *
            (Real.exp (∑ i, (2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.1 i|) *
              (Real.exp ((2 * (Fintype.card R : ℝ) + 1) * |ω.2.2.1|) *
                Real.exp ((2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.2.2|))))
        = K_c * (Real.exp (2 * (Fintype.card R : ℝ) * M * B) *
            Real.exp (∑ k, |ω.1.1.2 k|) *
            Real.exp (∑ i, (2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.1 i|) *
            Real.exp ((2 * (Fintype.card R : ℝ) + 1) * |ω.2.2.1|) *
            Real.exp ((2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.2.2|)) := by ring
      _ = K_c * Real.exp ((2 * (Fintype.card R : ℝ) * M * B) +
            (∑ k, |ω.1.1.2 k|) +
            (∑ i : Fin N, (2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.1 i|) +
            ((2 * (Fintype.card R : ℝ) + 1) * |ω.2.2.1|) +
            ((2 * (Fintype.card R : ℝ) * |Real.sqrt r|) * |ω.2.2.2|)) := by
          simp only [Real.exp_add]
      _ = Real.exp (2 * ((Fintype.card R : ℝ) * A_env ω)) *
            (K_c * Real.exp (|ω.2.2.1| + ∑ k, |ω.1.1.2 k|)) := by
          rw [← hexp_eq, Real.exp_add]; ring
  have hFm : Measurable fun x : R → InterpSPState N M => f (fun l => (x l).1) :=
    (measurable_of_finite f).comp (measurable_pi_iff.2 fun l =>
      measurable_fst.comp (measurable_pi_apply l))
  exact hasDerivAt_integral_integral_pi_tilted_of_dominated (P := P) (μ := interpSPBase N M)
    (E := fun t' ω x => interpSPEnergy u s t' q r ω x)
    (E' := fun t' ω x => interpSPEnergyDeriv u s t' q ω x)
    (s := V_set) isOpen_Ioo htV
    (fun t' _ => measurable_interpSPEnergy hu.continuous.measurable s t' q r)
    (fun t' _ => measurable_interpSPEnergyDeriv u s t' q)
    hEb hb_int hdb houter
    (fun ω x t' ht' => hasDerivAt_interpSPEnergy ⟨hδ.trans ht'.1, by linarith [ht'.2]⟩ hu s q r ω x)
    hFm (fun _ => hCf _)

/-- **Gaussian IBP for the `y` term of `interpSPEnergyDeriv` (`y ~ 𝒩(0, v)`).** -/
private lemma integral_replicaDiff_interpSP_lastField {N M : ℕ} {R : Type uR}
    [Fintype R] [LinearOrder R]
    {t : ℝ} (ht : t < 1) {s q r : ℝ} (v : ℝ≥0)
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (f : (R → PerceptronSpin N) → ℝ) :
    let P := interpSPDisorder N M v
    let μ (ω : InterpSPDisorder N M) := (interpSPBase N M).tilted (interpSPEnergy u s t q r ω)
    ∫ ω, replicaDiff (μ ω) (fun x => f (fun l => (x l).1))
        (fun x => -((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * Real.sqrt (1 - t))) ∂P =
      -(v : ℝ) * ∫ ω, replicaPairAverage (μ ω) (fun x => f (fun l => (x l).1))
        (fun a b => ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ)) ∂P := by
  intro P μ
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let q_t := Real.sqrt (1 - t)
  have hqt0 : 0 < q_t := Real.sqrt_pos.2 (sub_pos.2 ht)
  let F_st (x : R → InterpSPState N M) : ℝ := f (fun l => (x l).1)
  have hFm : Measurable F_st :=
    (measurable_of_finite f).comp (measurable_pi_iff.2 fun l =>
      measurable_fst.comp (measurable_pi_apply l))
  have hεm : Measurable fun x : InterpSPState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  -- Pointwise Stein identity in `y` for fixed `ω_rest = (ω.1, ω.2.1, ω.2.2.2)`!
  let mkΩ ( gaz : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ))
      (z' : Fin N → ℝ) (zl : ℝ) (y : ℝ) : InterpSPDisorder N M :=
    (gaz, (z', (y, zl)))
  have hstein_y (gaz : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × (Fin M → ℝ))
      (z' : Fin N → ℝ) (zl : ℝ) :
      ∫ y, replicaDiff (μ (mkΩ gaz z' zl y)) F_st
        (fun x => -((x.1.2 : ℤ) : ℝ) * y / (2 * q_t)) ∂gaussianReal 0 v =
      -(v : ℝ) * ∫ y, replicaPairAverage (μ (mkΩ gaz z' zl y)) F_st
        (fun a b => ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ)) ∂gaussianReal 0 v := by
    let Gf (y : ℝ) : ℝ := replicaDiff (μ (mkΩ gaz z' zl y)) F_st (fun x => ((x.1.2 : ℤ) : ℝ))
    let PA (y : ℝ) : ℝ := replicaPairAverage (μ (mkΩ gaz z' zl y)) F_st
      (fun a b => ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ))
    have hν (y : ℝ) : IsProbabilityMeasure (μ (mkΩ gaz z' zl y)) :=
      isProbabilityMeasure_tilted_interpSPEnergy hu hB_le s t q r _
    have hderiv (y : ℝ) : HasDerivAt Gf (2 * q_t * PA y) y := by
      have hEb_loc : ∀ y' ∈ Metric.ball y 1, ∀ x : InterpSPState N M,
          interpSPEnergy u s t q r (mkΩ gaz z' zl y') x ≤
          M * B + (∑ i : Fin N, |Real.sqrt (1 - s) * z' i * Real.sqrt r|) +
            (|q_t| * (|y| + 1) + |Real.sqrt (1 - s) * zl * Real.sqrt r|) := by
        intro y' hy' x
        refine (interpSPEnergy_le hB_le s t q r (mkΩ gaz z' zl y') x).trans ?_
        have hy_le : |y'| ≤ |y| + 1 := by
          have h1 := abs_sub_abs_le_abs_sub y' y
          have h2 := Metric.mem_ball.1 hy'
          rw [Real.dist_eq] at h2
          linarith
        gcongr
      have hE'_le (x : InterpSPState N M) : |q_t * ((x.1.2 : ℤ) : ℝ)| ≤ q_t := by
        rw [abs_mul, abs_units_cast_eq_one, mul_one, abs_of_pos hqt0]
      have hd_y (x : InterpSPState N M) (y' : ℝ) (_ : y' ∈ Metric.ball y 1) :
          HasDerivAt (fun y'' => interpSPEnergy u s t q r (mkΩ gaz z' zl y'') x)
            (q_t * ((x.1.2 : ℤ) : ℝ)) y' := by
        unfold interpSPEnergy
        have hf_indep (y'' : ℝ) (k : Fin M) :
            interpSPField s t q (mkΩ gaz z' zl y'') x k =
            interpSPField s t q (mkΩ gaz z' zl 0) x k := rfl
        simp_rw [hf_indep]
        have h1 := ((((hasDerivAt_id y').const_mul q_t).add_const
          (Real.sqrt (1 - s) * zl * Real.sqrt r)).const_mul ((x.1.2 : ℤ) : ℝ)).const_add
          ((∑ k : Fin M, u (interpSPField s t q (mkΩ gaz z' zl 0) x k)) +
            ∑ i : Fin N, ((x.1.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * z' i * Real.sqrt r)
        refine h1.congr_deriv ?_
        ring
      have := hν y
      have hbd := hasDerivAt_replicaDiff_tilted_replicaDiff
        (μ := interpSPBase N M)
        (E := fun y' => interpSPEnergy u s t q r (mkΩ gaz z' zl y'))
        (E' := fun _ x => q_t * ((x.1.2 : ℤ) : ℝ))
        (t := y) (s := Metric.ball y 1) (Metric.ball_mem_nhds y one_pos)
        (fun y' _ => measurable_interpSPEnergy_slice hu s t q r _)
        (hεm.const_mul q_t) hEb_loc (integrable_const q_t) (fun _ _ x => hE'_le x)
        hd_y hFm (fun _ => hCf _) hεm (fun _ => (abs_units_cast_eq_one _).le)
        (integrable_of_measurable_bound (hεm.const_mul q_t) hE'_le)
      have hbr := replicaDiffWith_replicaDiff_eq_two_mul_replicaPairAverage
        (μ (mkΩ gaz z' zl y)) F_st hFm (fun _ => hCf _)
        (fun x : InterpSPState N M => ((x.1.2 : ℤ) : ℝ)) hεm
        (fun _ => (abs_units_cast_eq_one _).le) 1 q_t
        (fun x => by rw [← sq]; exact units_cast_sq _)
      exact hbr ▸ hbd
    have hGc : Continuous Gf := continuous_iff_continuousAt.2 fun y => (hderiv y).continuousAt
    have hPAm : Measurable fun y => 2 * q_t * PA y := by
      have : (fun y => 2 * q_t * PA y) = deriv Gf := funext fun y => (hderiv y).deriv.symm
      rw [this]; exact measurable_deriv Gf
    have hGb (y : ℝ) : |Gf y| ≤ |C_f| * ((Fintype.card R : ℝ) * 1 + (Fintype.card R : ℝ) * 1) := by
      have := hν y
      exact abs_replicaDiff_le _ F_st hFm (fun _ => (hCf _).trans (le_abs_self _)) _ hεm
        (fun _ => (abs_units_cast_eq_one _).le)
    obtain ⟨K₀, hK₀⟩ := exists_abs_replicaPairCombination_le (R := R)
      (U := fun a b : InterpSPState N M => ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ))
      ⟨1, fun a b => by rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]⟩
    have hPAb (y : ℝ) : |2 * q_t * PA y| ≤ 2 * q_t * (|C_f| * K₀) := by
      have := hν y
      rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (abs_replicaPairAverage_le _ F_st (fun _ => (hCf _).trans (le_abs_self _)) hK₀)
        (by positivity)
    have hxF : Integrable (fun y => y * Gf y) (gaussianReal 0 v) := by
      have := (IsGaussian.integrable_id (μ := gaussianReal 0 v)).bdd_mul_of_abs_le
        hGc.aestronglyMeasurable (ae_of_all _ hGb)
      simpa only [mul_comm, id] using this
    have hF' : Integrable (fun y => 2 * q_t * PA y) (gaussianReal 0 v) :=
      integrable_of_measurable_bound hPAm hPAb
    have hStein := integral_id_mul_gaussianReal_eq v hderiv hxF hF'
    have hpt (y : ℝ) : replicaDiff (μ (mkΩ gaz z' zl y)) F_st
        (fun x => -((x.1.2 : ℤ) : ℝ) * y / (2 * q_t)) = (-(1 / (2 * q_t)) * y) * Gf y := by
      have hfun : (fun x : InterpSPState N M => -((x.1.2 : ℤ) : ℝ) * y / (2 * q_t)) =
          fun x => (-(1 / (2 * q_t)) * y) * ((x.1.2 : ℤ) : ℝ) := by funext x; ring
      rw [hfun]; exact replicaDiff_const_mul _ F_st _ _
    simp_rw [hpt]
    have hmul : ∫ y, (-(1 / (2 * q_t)) * y) * Gf y ∂gaussianReal 0 v =
        -(1 / (2 * q_t)) * ∫ y, y * Gf y ∂gaussianReal 0 v := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun y => by ring)
    rw [hmul, hStein, integral_const_mul]
    dsimp only [PA]
    have hq_ne : q_t ≠ 0 := hqt0.ne'
    field_simp
  -- Integrate `hstein_y` over `(gaz, z', zl)` via Fubini!
  let L_fn (ω : InterpSPDisorder N M) : ℝ :=
    replicaDiff (μ ω) F_st (fun x => -((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * q_t))
  let R_fn (ω : InterpSPDisorder N M) : ℝ :=
    replicaPairAverage (μ ω) F_st (fun a b => ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ))
  have hLm : Measurable L_fn := by
    have hpt : L_fn = fun ω =>
        (-(ω.2.2.1 / (2 * q_t))) * replicaDiff (μ ω) F_st (fun x => ((x.1.2 : ℤ) : ℝ)) := by
      funext ω; dsimp only [L_fn]
      have hfun : (fun x : InterpSPState N M => -((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * q_t)) =
          fun x => (-(ω.2.2.1 / (2 * q_t))) * ((x.1.2 : ℤ) : ℝ) := by funext x; ring
      rw [hfun]; exact replicaDiff_const_mul _ F_st _ _
    rw [hpt]
    have hm_rd : Measurable fun ω : InterpSPDisorder N M =>
        replicaDiff (μ ω) F_st (fun x => ((x.1.2 : ℤ) : ℝ)) := by
      have hm_i (i : Option R) : Measurable fun ω : InterpSPDisorder N M =>
          ∫ σ : Option R → InterpSPState N M,
            F_st (fun j => σ (some j)) * (((σ i).1.2 : ℤ) : ℝ)
            ∂(Measure.pi fun _ : Option R => μ ω) := by
        let G_i (_ω : InterpSPDisorder N M) (σ : Option R → InterpSPState N M) : ℝ :=
          F_st (fun j => σ (some j)) * (((σ i).1.2 : ℤ) : ℝ)
        have hGi : Measurable fun p : InterpSPDisorder N M × (Option R → InterpSPState N M) =>
            G_i p.1 p.2 :=
          (hFm.comp (measurable_pi_iff.2 fun j =>
            (measurable_pi_apply (some j)).comp measurable_snd)).mul
            (hεm.comp ((measurable_pi_apply i).comp measurable_snd))
        exact measurable_integral_pi_tilted (μ := interpSPBase N M)
          (measurable_interpSPEnergy hu s t q r) hGi
      have heq_rd : (fun ω => replicaDiff (μ ω) F_st (fun x => ((x.1.2 : ℤ) : ℝ))) =
          fun ω => (∑ j : R, ∫ σ : Option R → InterpSPState N M,
              F_st (fun k => σ (some k)) * (((σ (some j)).1.2 : ℤ) : ℝ)
              ∂(Measure.pi fun _ : Option R => μ ω)) -
            (Fintype.card R : ℝ) * ∫ σ : Option R → InterpSPState N M,
              F_st (fun k => σ (some k)) * (((σ none).1.2 : ℤ) : ℝ)
              ∂(Measure.pi fun _ : Option R => μ ω) := rfl
      rw [heq_rd]
      exact (Finset.measurable_sum _ fun j _ => hm_i (some j)).sub ((hm_i none).const_mul _)
    have hm_y : Measurable fun ω : InterpSPDisorder N M => -(ω.2.2.1 / (2 * q_t)) := by fun_prop
    exact hm_y.mul hm_rd
  have hLi : Integrable L_fn P := by
    let C_rd : ℝ := |C_f| * ((Fintype.card R : ℝ) * 1 + (Fintype.card R : ℝ) * 1) / (2 * q_t)
    have hy_int : Integrable (fun ω : InterpSPDisorder N M => C_rd * |ω.2.2.1|) P := by
      unfold P interpSPDisorder
      have hy1 : Integrable (fun y : ℝ => |y|) (gaussianReal 0 v) :=
        IsGaussian.integrable_id.abs
      exact (((hy1.comp_fst _).comp_snd _).comp_snd _).const_mul C_rd
    refine hy_int.mono' hLm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := isProbabilityMeasure_tilted_interpSPEnergy hu hB_le s t q r ω
    rw [Real.norm_eq_abs]
    dsimp only [L_fn]
    have hfun : (fun x : InterpSPState N M => -((x.1.2 : ℤ) : ℝ) * ω.2.2.1 / (2 * q_t)) =
        fun x => (-(ω.2.2.1 / (2 * q_t))) * ((x.1.2 : ℤ) : ℝ) := by funext x; ring
    rw [hfun, replicaDiff_const_mul, abs_mul, abs_neg, abs_div, abs_of_pos (mul_pos zero_lt_two hqt0)]
    have hb_rd := abs_replicaDiff_le (μ ω) F_st hFm
      (fun _ => (hCf _).trans (le_abs_self _)) _ hεm (fun _ => (abs_units_cast_eq_one _).le)
    calc |ω.2.2.1| / (2 * q_t) * |replicaDiff (μ ω) F_st (fun x => ((x.1.2 : ℤ) : ℝ))|
        ≤ |ω.2.2.1| / (2 * q_t) * (|C_f| * ((Fintype.card R : ℝ) * 1 + (Fintype.card R : ℝ) * 1)) :=
          mul_le_mul_of_nonneg_left hb_rd (by positivity)
      _ = C_rd * |ω.2.2.1| := by dsimp only [C_rd]; ring
  have hRi : Integrable R_fn P := by
    have hU_m : Measurable fun p : InterpSPState N M × InterpSPState N M =>
        ((p.1.1.2 : ℤ) : ℝ) * ((p.2.1.2 : ℤ) : ℝ) :=
      (hεm.comp measurable_fst).mul (hεm.comp measurable_snd)
    exact integrable_replicaPairAverage_tilted_of_bound (μ := interpSPBase N M)
      (E := fun ω x => interpSPEnergy u s t q r ω x)
      (measurable_interpSPEnergy hu s t q r)
      (fun ω => isProbabilityMeasure_tilted_interpSPEnergy hu hB_le s t q r ω)
      (U := fun _ a b => ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ))
      (hU_m.comp measurable_snd)
      (fun _ a b => by rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one])
      hFm (fun _ => hCf _)
  unfold P interpSPDisorder at hLi hRi ⊢
  rw [integral_prod _ hLi, integral_prod _ hRi, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hLi.prod_right_ae, hRi.prod_right_ae] with gaz hLi1 hRi1
  rw [integral_prod _ hLi1, integral_prod _ hRi1, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hLi1.prod_right_ae, hRi1.prod_right_ae] with z' hLi2 hRi2
  rw [integral_prod_symm _ hLi2, integral_prod_symm _ hRi2, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun zl => hstein_y gaz z' zl)

/-- **One-step Stein identity on the split last constraint of the `(s, t)`-interpolating smart path**
(pointwise in old disorder `ω₀`). Instantiates `stein_tilted_replica_ratio` on `K_sh = ((Fin N ⊕ Unit) ⊕ Unit)`
and `K_aux = Fin 2`, where `W_sh ⬝ᵥ α_sh + W_aux ⬝ᵥ α_aux = 0` kills the diagonal term `j = ℓ`. -/
private lemma stein_interpSP_last_constraint_split
    {N M : ℕ} {J : Type uR} [Fintype J] [DecidableEq J]
    {s : ℝ} (hs0 : 0 ≤ s) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (q r : ℝ)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ω₀ : InterpSPDisorder N M) (ℓ : J)
    {g : (J → InterpSPState N M) → ℝ}
    (hgi : Integrable g (Measure.pi fun _ : J =>
      (interpSPBase N M).tilted (interpSPEnergy u s t q r ω₀))) :
    let μ₀ := (interpSPBase N M).tilted (interpSPEnergy u s t q r ω₀)
    let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
    let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let α_sh (σ : PerceptronSpin N) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ :=
      Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
    let W_sh (σ : PerceptronSpin N) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ :=
      Sum.elim (Sum.elim 0 (fun _ =>
        Real.sqrt s * (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))) 0
    let α_aux : Fin 2 → ℝ :=
      ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)), Real.sqrt (1 - s) * Real.sqrt (1 - q)]
    let W_aux : Fin 2 → ℝ :=
      ![-Real.sqrt s / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)), 0]
    let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
      α_sh y.1.1 ⬝ᵥ w₁ + α_aux ⬝ᵥ y.2
    let Wt (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
      W_sh y.1.1 ⬝ᵥ w₁ + W_aux ⬝ᵥ y.2
    ∫ w₁, ∫ σ : J → InterpSPState N M × (Fin 2 → ℝ),
        g (fun j => (σ j).1) * Wt w₁ (σ ℓ) * deriv u (X_fn w₁ (σ ℓ))
        ∂(Measure.pi fun _ : J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁ =
      (s / (2 * (N + 1))) *
        ((∑ j ∈ Finset.univ.erase ℓ,
          ∫ w₁, ∫ σ : J → InterpSPState N M × (Fin 2 → ℝ),
            g (fun k => (σ k).1) * (((σ ℓ).1.1.2 : ℤ) : ℝ) * (((σ j).1.1.2 : ℤ) : ℝ) *
              deriv u (X_fn w₁ (σ ℓ)) * deriv u (X_fn w₁ (σ j))
            ∂(Measure.pi fun _ : J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁) -
        (Fintype.card J : ℝ) *
          ∫ w₁, ∫ σ : Option J → InterpSPState N M × (Fin 2 → ℝ),
            g (fun k => (σ (some k)).1) *
              (((σ (some ℓ)).1.1.2 : ℤ) : ℝ) * (((σ none).1.1.2 : ℤ) : ℝ) *
              deriv u (X_fn w₁ (σ (some ℓ))) * deriv u (X_fn w₁ (σ none))
            ∂(Measure.pi fun _ : Option J =>
              (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁) := by
  intro μ₀ γ₁ γ₂ α_sh W_sh α_aux W_aux X_fn Wt
  have : IsProbabilityMeasure μ₀ :=
    isProbabilityMeasure_tilted_interpSPEnergy hu.measurable (fun x => hu.le x) s t q r ω₀
  let ψ : J → ℝ → ℝ := fun j x => if j = ℓ then deriv u x else 1
  let ψ' : J → ℝ → ℝ := fun j x =>
    if j = ℓ then deriv (deriv u) x + deriv u x ^ 2 else deriv u x
  have hψd : ∀ j, Differentiable ℝ fun x => ψ j x * Real.exp (u x) := fun j => by
    dsimp only [ψ]; split_ifs
    · exact hu.differentiable_deriv.mul hu.differentiable.exp
    · simpa using hu.differentiable.exp
  have hψ_deriv : ∀ j x, deriv (fun y => ψ j y * Real.exp (u y)) x = ψ' j x * Real.exp (u x) := by
    intro j x; dsimp only [ψ, ψ']; split_ifs
    · have h1 : HasDerivAt (fun y => deriv u y * Real.exp (u y))
          (deriv (deriv u) x * Real.exp (u x) + deriv u x * (Real.exp (u x) * deriv u x)) x :=
        (hu.differentiable_deriv x).hasDerivAt.mul ((hu.differentiable x).hasDerivAt.exp)
      rw [h1.deriv]; ring
    · have h1 := (hu.differentiable x).hasDerivAt.exp
      simpa [one_mul, mul_comm] using h1.deriv
  let M₀ : J → ℝ := fun _ => 1 + |D|
  let M' : J → ℝ := fun _ => (1 + |D₂| + |D| ^ 2 + |D|) * Real.exp |B|
  have hM₀ : ∀ j x, |ψ j x| ≤ M₀ j := fun j x => by
    dsimp only [ψ, M₀]; split_ifs
    · linarith [hu.abs_deriv_le x, le_abs_self D, abs_nonneg D]
    · rw [abs_one]; linarith [abs_nonneg D]
  have hM' : ∀ j x, |deriv (fun y => ψ j y * Real.exp (u y)) x| ≤ M' j := fun j x => by
    rw [hψ_deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul ?_ (Real.exp_le_exp.2 ((hu.le x).trans (le_abs_self B)))
      (Real.exp_pos _).le (by positivity)
    dsimp only [ψ']; split_ifs
    · have h2 := (hu.abs_deriv₂_le x).trans (le_abs_self D₂)
      have h1 : |deriv u x ^ 2| ≤ |D| ^ 2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hu.abs_deriv_le x).trans (le_abs_self D)) 2
      exact (abs_add_le _ _).trans (by linarith [abs_nonneg D, abs_nonneg D₂])
    · exact (hu.abs_deriv_le x).trans (by linarith [le_abs_self D, abs_nonneg D₂, sq_nonneg |D|])
  have hstein := stein_tilted_replica_ratio μ₀ (fun x : InterpSPState N M => x.1) measurable_fst
    α_sh W_sh (fun _ => α_aux) (fun _ => W_aux) hu.differentiable hu.abs_le hu.abs_deriv_le
    ψ hψd hM₀ hM' ψ' hψ_deriv ℓ hgi
  dsimp only at hstein
  have hprod_J (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (f_σ : J → InterpSPState N M × (Fin 2 → ℝ)) :
      ∏ j : J, ψ j (X_fn w₁ (f_σ j)) = deriv u (X_fn w₁ (f_σ ℓ)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ψ j (X_fn w₁ (f_σ j))) (Finset.mem_univ ℓ)]
    have her : ∏ j ∈ Finset.univ.erase ℓ, ψ j (X_fn w₁ (f_σ j)) = 1 :=
      Finset.prod_eq_one fun j hj => by simp [ψ, Finset.ne_of_mem_erase hj]
    rw [her, mul_one]; simp [ψ]
  simp only [show ∀ w₁ y, α_sh y.1.1 ⬝ᵥ w₁ + α_aux ⬝ᵥ y.2 = X_fn w₁ y from fun _ _ => rfl,
    show ∀ w₁ y, W_sh y.1.1 ⬝ᵥ w₁ + W_aux ⬝ᵥ y.2 = Wt w₁ y from fun _ _ => rfl, hprod_J] at hstein
  change (∫ w₁, ∫ σ : J → InterpSPState N M × (Fin 2 → ℝ),
      g (fun j => (σ j).1) * Wt w₁ (σ ℓ) * deriv u (X_fn w₁ (σ ℓ))
      ∂(Measure.pi fun _ : J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁) = _ at hstein
  rw [hstein]
  have hs_sq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0
  have hcov_diff (σ τ : PerceptronSpin N) :
      W_sh σ ⬝ᵥ α_sh τ = s * ((((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (2 * (N + 1))) := by
    have h0 := cavityTimeCoef_dotProduct_of_ne (R := Fin 2) ht σ τ (by decide : (0 : Fin 2) ≠ 1)
    dsimp only [W_sh, α_sh]
    rw [sumElim_dotProduct_sumElim, zero_dotProduct, add_zero, dotProduct_smul, smul_eq_mul]
    have h1 : (Sum.elim (0 : Fin N → ℝ) (fun _ : Unit =>
        Real.sqrt s * (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))) =
        Real.sqrt s • Sum.elim (0 : Fin N → ℝ) (fun _ : Unit =>
          (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t))) := by
      ext idx; rcases idx with i | _ <;> simp
    rw [h1, smul_dotProduct, smul_eq_mul, ← mul_assoc, hs_sq]
    congr 1
    simpa [sumElim_dotProduct_sumElim, dotProduct, Pi.single_apply] using h0
  have hcov_same (σ : PerceptronSpin N) : W_sh σ ⬝ᵥ α_sh σ + W_aux ⬝ᵥ α_aux = 0 := by
    have h0 := cavityTimeCoef_dotProduct_self (R := Unit) ht σ ()
    rw [hcov_diff σ σ]
    have haux_dot : W_aux ⬝ᵥ α_aux =
        s * ((-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) *
          Real.sqrt ((1 - t) / (N + 1))) := by
      dsimp only [W_aux, α_aux]
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul,
        add_zero]
      linear_combination ((-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) *
        Real.sqrt ((1 - t) / (N + 1))) * hs_sq
    rw [haux_dot, ← mul_add]
    have h0' : (((σ.2 : ℤ) : ℝ) * ((σ.2 : ℤ) : ℝ)) / (2 * (N + 1)) +
        (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) *
          Real.sqrt ((1 - t) / (N + 1)) = 0 := by
      -- Extract from `h0` directly:
      have h0_exp : ((((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)) *
          (Real.sqrt (t / (N + 1)) * ((σ.2 : ℤ) : ℝ))) +
          (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) *
            Real.sqrt ((1 - t) / (N + 1)) = 0 := by
        simpa [sumElim_dotProduct_sumElim, dotProduct, cavityCoef] using h0
      have h_first : (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)) *
          (Real.sqrt (t / (N + 1)) * ((σ.2 : ℤ) : ℝ)) =
          (((σ.2 : ℤ) : ℝ) * ((σ.2 : ℤ) : ℝ)) / (2 * (N + 1)) := by
        have h0_ne := cavityTimeCoef_dotProduct_of_ne (R := Fin 2) ht σ σ (by decide : (0 : Fin 2) ≠ 1)
        simpa [sumElim_dotProduct_sumElim, dotProduct, cavityCoef, Pi.single_apply] using h0_ne
      rwa [h_first] at h0_exp
    rw [h0', mul_zero]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]
  have hdiag : ∫ w₁, ∫ σ : J → InterpSPState N M × (Fin 2 → ℝ),
      g (fun j => (σ j).1) *
        (W_sh (σ ℓ).1.1 ⬝ᵥ α_sh (σ ℓ).1.1 + if ℓ = ℓ then W_aux ⬝ᵥ α_aux else 0) *
        (ψ' ℓ (X_fn w₁ (σ ℓ)) * ∏ j ∈ Finset.univ.erase ℓ, ψ j (X_fn w₁ (σ j)))
      ∂(Measure.pi fun _ : J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁ = 0 := by
    simp only [↓reduceIte, hcov_same, mul_zero, zero_mul, integral_zero]
  rw [hdiag, zero_add]
  have hoff : ∀ j ∈ Finset.univ.erase ℓ,
      ∫ w₁, ∫ σ : J → InterpSPState N M × (Fin 2 → ℝ),
        g (fun k => (σ k).1) *
          (W_sh (σ ℓ).1.1 ⬝ᵥ α_sh (σ j).1.1 + if ℓ = j then W_aux ⬝ᵥ α_aux else 0) *
          (ψ' j (X_fn w₁ (σ j)) * ∏ k ∈ Finset.univ.erase j, ψ k (X_fn w₁ (σ k)))
        ∂(Measure.pi fun _ : J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁ =
      (s / (2 * (N + 1))) *
        ∫ w₁, ∫ σ : J → InterpSPState N M × (Fin 2 → ℝ),
          g (fun k => (σ k).1) * (((σ ℓ).1.1.2 : ℤ) : ℝ) * (((σ j).1.1.2 : ℤ) : ℝ) *
            deriv u (X_fn w₁ (σ ℓ)) * deriv u (X_fn w₁ (σ j))
          ∂(Measure.pi fun _ : J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁ := by
    intro j hj
    have hne : j ≠ ℓ := Finset.ne_of_mem_erase hj
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w₁ => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp only
    have hprod_j : ∏ k ∈ Finset.univ.erase j, ψ k (X_fn w₁ (σ k)) = deriv u (X_fn w₁ (σ ℓ)) := by
      have hmem : ℓ ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase _ _ hmem]
      have her2 : ∏ k ∈ (Finset.univ.erase j).erase ℓ, ψ k (X_fn w₁ (σ k)) = 1 :=
        Finset.prod_eq_one fun k hk => by simp [ψ, Finset.ne_of_mem_erase hk]
      rw [her2, mul_one]; simp [ψ]
    simp only [hne.symm, ↓reduceIte, add_zero, hcov_diff, ψ', hne, hprod_j]
    ring
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum]
  have hfresh : ∫ w₁, ∫ σ : Option J → InterpSPState N M × (Fin 2 → ℝ),
      g (fun k => (σ (some k)).1) *
        (W_sh (σ (some ℓ)).1.1 ⬝ᵥ α_sh (σ none).1.1) *
        deriv u (X_fn w₁ (σ (some ℓ))) * deriv u (X_fn w₁ (σ none))
      ∂(Measure.pi fun _ : Option J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁ =
    (s / (2 * (N + 1))) *
      ∫ w₁, ∫ σ : Option J → InterpSPState N M × (Fin 2 → ℝ),
        g (fun k => (σ (some k)).1) *
          (((σ (some ℓ)).1.1.2 : ℤ) : ℝ) * (((σ none).1.1.2 : ℤ) : ℝ) *
          deriv u (X_fn w₁ (σ (some ℓ))) * deriv u (X_fn w₁ (σ none))
        ∂(Measure.pi fun _ : Option J => (μ₀.prod γ₂).tilted (fun y => u (X_fn w₁ y))) ∂γ₁ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w₁ => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp only
    rw [hcov_diff]
    ring
  rw [hfresh]
  ring

/-- Integrability of the split `Wt * deriv u` term on `P₀.prod γ₁`. -/
private lemma integrable_integral_pi_interpSP_last_split_deriv
    {N M : ℕ} {J : Type uR} [Fintype J]
    (s : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (q r : ℝ) (v : ℝ≥0)
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (ℓ : J)
    {f : InterpSPDisorder N M → (J → InterpSPState N M) → ℝ}
    (hf : Measurable fun p : InterpSPDisorder N M × (J → InterpSPState N M) => f p.1 p.2)
    {C_f : ℝ} (hfb : ∀ ω a, |f ω a| ≤ C_f) :
    let P₀ := interpSPDisorder N M v
    let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
    let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let μ₀ (ω₀ : InterpSPDisorder N M) :=
      (interpSPBase N M).tilted (interpSPEnergy u s t q r ω₀)
    let α_sh (σ : PerceptronSpin N) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ :=
      Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
    let W_sh (σ : PerceptronSpin N) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ :=
      Sum.elim (Sum.elim 0 (fun _ =>
        Real.sqrt s * (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))) 0
    let α_aux : Fin 2 → ℝ :=
      ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)), Real.sqrt (1 - s) * Real.sqrt (1 - q)]
    let W_aux : Fin 2 → ℝ :=
      ![-Real.sqrt s / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)), 0]
    let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
      α_sh y.1.1 ⬝ᵥ w₁ + α_aux ⬝ᵥ y.2
    let Wt (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
      W_sh y.1.1 ⬝ᵥ w₁ + W_aux ⬝ᵥ y.2
    Integrable
      (fun p : InterpSPDisorder N M × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) =>
        ∫ σ : J → InterpSPState N M × (Fin 2 → ℝ),
          f p.1 (fun j => (σ j).1) * Wt p.2 (σ ℓ) * deriv u (X_fn p.2 (σ ℓ))
          ∂(Measure.pi fun _ : J => ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))))
      (P₀.prod γ₁) := by
  intro P₀ γ₁ γ₂ μ₀ α_sh W_sh α_aux W_aux X_fn Wt
  let Ω := InterpSPDisorder N M
  let W := ((Fin N ⊕ Unit) ⊕ Unit) → ℝ
  let T := InterpSPState N M × (Fin 2 → ℝ)
  let ν (p : Ω × W) := ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))
  let G_lhs (p : Ω × W) (σ : J → T) : ℝ :=
    f p.1 (fun j => (σ j).1) * Wt p.2 (σ ℓ) * deriv u (X_fn p.2 (σ ℓ))
  have hμ₀ (ω₀ : Ω) : IsProbabilityMeasure (μ₀ ω₀) :=
    isProbabilityMeasure_tilted_interpSPEnergy hu.measurable (fun x => hu.le x) s t q r ω₀
  have hXm : Measurable fun p : W × T => X_fn p.1 p.2 := by
    have hX1 (j : (Fin N ⊕ Unit) ⊕ Unit) : Measurable fun p : W × T => α_sh p.2.1.1 j :=
      (measurable_of_finite fun σ => α_sh σ j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : W × T => α_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hX1 j).mul ((measurable_pi_apply j).comp measurable_fst)
    have hd2 : Measurable fun p : W × T => α_aux ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hd1.add hd2
  have hWtm : Measurable fun p : W × T => Wt p.1 p.2 := by
    have hW1 (j : (Fin N ⊕ Unit) ⊕ Unit) : Measurable fun p : W × T => W_sh p.2.1.1 j :=
      (measurable_of_finite fun σ => W_sh σ j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : W × T => W_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hW1 j).mul ((measurable_pi_apply j).comp measurable_fst)
    have hd2 : Measurable fun p : W × T => W_aux ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hd1.add hd2
  have hGm_lhs : Measurable fun p : (Ω × W) × (J → T) => G_lhs p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (J → T) =>
        ((p.1.1, fun j => (p.2 j).1) : Ω × (J → InterpSPState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun j =>
        measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd))
    have hp2 : Measurable fun p : (Ω × W) × (J → T) => (p.1.2, p.2 ℓ) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply ℓ).comp measurable_snd)
    have m1 := hf.comp hp1
    have m2 := hWtm.comp hp2
    have mx2 := hXm.comp hp2
    have m3 := (measurable_deriv u).comp mx2
    exact (m1.mul m2).mul m3
  -- Joint measurability of `p ↦ ∫ σ, G_lhs p σ`!
  let H_comb (p : Ω × W) (y : T) : ℝ := interpSPEnergy u s t q r p.1 y.1 + u (X_fn p.2 y)
  have hHm : Measurable fun p : (Ω × W) × T => H_comb p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × T => (p.1.1, p.2.1) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    have hp2 : Measurable fun p : (Ω × W) × T => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have he1 := (measurable_interpSPEnergy hu.measurable s t q r).comp hp1
    have hx2 := hXm.comp hp2
    have hu2 := hu.measurable.comp hx2
    exact he1.add hu2
  have hν_eq (p : Ω × W) : ν p = ((interpSPBase N M).prod γ₂).tilted (H_comb p) := by
    dsimp only [ν, μ₀]
    rw [← tilted_prod_comp_fst, tilted_tilted
      ((integrable_exp_interpSPEnergy hu.measurable (fun x => hu.le x) s t q r p.1).comp_fst γ₂)]
    rfl
  let J_lhs (p : Ω × W) : ℝ := ∫ σ : J → T, G_lhs p σ ∂(Measure.pi fun _ : J => ν p)
  have hJm : Measurable J_lhs := by
    have heq : J_lhs = fun p => ∫ σ : J → T, G_lhs p σ
        ∂(Measure.pi fun _ : J => ((interpSPBase N M).prod γ₂).tilted (H_comb p)) := by
      funext p; dsimp only [J_lhs]; simp_rw [hν_eq p]
    rw [heq]
    exact measurable_integral_pi_tilted (μ := (interpSPBase N M).prod γ₂) hHm hGm_lhs
  let c1 : ℝ := |Real.sqrt s| / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)
  let c2 : ℝ := |Real.sqrt s| / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))
  have hc1 : 0 ≤ c1 := by dsimp only [c1]; positivity
  have hc2 : 0 ≤ c2 := by dsimp only [c2]; positivity
  have hw_int : Integrable (fun w : W => |w (Sum.inl (Sum.inr ()))|) γ₁ :=
    (integrable_comp_eval (μ := fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      (i := Sum.inl (Sum.inr ())) IsGaussian.integrable_id).abs
  have hη_int : Integrable (fun η : Fin 2 → ℝ => |η 0|) γ₂ :=
    (integrable_comp_eval (μ := fun _ : Fin 2 => gaussianReal 0 1)
      (i := 0) IsGaussian.integrable_id).abs
  let M_η : ℝ := ∫ η : Fin 2 → ℝ, |η 0| ∂γ₂
  let dom_w (w : W) : ℝ :=
    |C_f| * |D| * (c1 * |w (Sum.inl (Sum.inr ()))| + c2 * (Real.exp (2 * |B|) * M_η))
  have hdom_w : Integrable dom_w γ₁ :=
    ((hw_int.const_mul c1).add (integrable_const _)).const_mul (|C_f| * |D|)
  have hdom_int : Integrable (fun p : Ω × W => dom_w p.2) (P₀.prod γ₁) := hdom_w.comp_snd P₀
  change Integrable J_lhs (P₀.prod γ₁)
  refine Integrable.mono' hdom_int hJm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  have hp_id : Measurable fun y : T => (p.2, y) := measurable_const.prodMk measurable_id
  have hx_id := hXm.comp hp_id
  have hVp : Measurable fun y : T => u (X_fn p.2 y) := hu.measurable.comp hx_id
  have hν_prob : IsProbabilityMeasure (ν p) :=
    isProbabilityMeasure_tilted_of_ae_le hVp.aemeasurable (ae_of_all _ fun _ => hu.le _)
  have hWt_le (y : T) : |Wt p.2 y| ≤ c1 * |p.2 (Sum.inl (Sum.inr ()))| + c2 * |y.2 0| := by
    dsimp only [Wt, W_sh, W_aux]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, zero_add, Finset.univ_unique,
      Finset.sum_singleton, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_div, abs_units_cast_eq_one,
        abs_of_pos (mul_pos (mul_pos zero_lt_two (Real.sqrt_pos.2 (by positivity)))
          (Real.sqrt_pos.2 ht.1))]
      dsimp only [c1]; exact le_of_eq (by ring)
    · rw [abs_mul, abs_div, abs_neg,
        abs_of_pos (mul_pos (mul_pos zero_lt_two (Real.sqrt_pos.2 (by positivity)))
          (Real.sqrt_pos.2 (sub_pos.2 ht.2)))]
  have hη_tilt : Integrable (fun y : T => |y.2 0|) (ν p) := by
    have hη_prod : Integrable (fun y : T => |y.2 0|) ((μ₀ p.1).prod γ₂) := hη_int.comp_snd _
    exact integrable_tilted_of_ae_le hVp.aemeasurable (ae_of_all _ fun _ => hu.le _) hη_prod
  have hη_comp : ∫ y : T, |y.2 0| ∂(ν p) ≤ Real.exp (2 * |B|) * M_η := by
    have hη_prod : Integrable (fun y : T => |y.2 0|) ((μ₀ p.1).prod γ₂) := hη_int.comp_snd _
    have hc := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := Unit) (μ := (μ₀ p.1).prod γ₂)
      (E₀ := 0) (E₁ := fun y => u (X_fn p.2 y)) (by simp) (by simpa using hVp)
      (C := |B|) (fun _ => by simpa using (hu.abs_le _).trans (le_abs_self B))
      (Y := fun f_u : Unit → T => |(f_u ()).2 0|) (fun _ => abs_nonneg _)
      (by
        rw [tilted_zero]
        exact (measurePreserving_funUnique ((μ₀ p.1).prod γ₂) Unit).integrable_comp_of_integrable
          hη_prod)
    simp only [Fintype.card_unit, Nat.cast_one, mul_one, tilted_zero] at hc
    have h1 := (measurePreserving_funUnique (ν p) Unit).integral_comp_of_aestronglyMeasurable
      (g := fun y : T => |y.2 0|) hη_tilt.aestronglyMeasurable
    have h2 := (measurePreserving_funUnique ((μ₀ p.1).prod γ₂) Unit).integral_comp_of_aestronglyMeasurable
      (g := fun y : T => |y.2 0|) hη_prod.aestronglyMeasurable
    have h3 : ∫ y : T, |y.2 0| ∂((μ₀ p.1).prod γ₂) = M_η := by
      have hp_eq := integral_prod_mul (μ := μ₀ p.1) (ν := γ₂) (fun _ => (1 : ℝ)) (fun η => |η 0|)
      simpa [M_η] using hp_eq
    have h1' : (∫ x : Unit → T, |(x ()).2 0| ∂(Measure.pi fun _ : Unit => ν p)) =
        ∫ y : T, |y.2 0| ∂(ν p) := h1
    have h2' : (∫ x : Unit → T, |(x ()).2 0| ∂(Measure.pi fun _ : Unit => (μ₀ p.1).prod γ₂)) =
        ∫ y : T, |y.2 0| ∂((μ₀ p.1).prod γ₂) := h2
    rw [h1', h2', h3] at hc
    exact hc
  have hη_pi : Integrable (fun σ : J → T => |(σ ℓ).2 0|) (Measure.pi fun _ : J => ν p) :=
    integrable_comp_eval (μ := fun _ : J => ν p) (i := ℓ) hη_tilt
  have hη_pi_int : ∫ σ : J → T, |(σ ℓ).2 0| ∂(Measure.pi fun _ : J => ν p) =
      ∫ y : T, |y.2 0| ∂(ν p) := by
    have hmp_ev : MeasurePreserving (fun σ : J → T => σ ℓ) (Measure.pi fun _ : J => ν p) (ν p) :=
      MeasureTheory.measurePreserving_eval (fun _ : J => ν p) ℓ
    exact hmp_ev.integral_comp_of_aestronglyMeasurable hη_tilt.aestronglyMeasurable
  let dom_σ (σ : J → T) : ℝ :=
    |C_f| * |D| * (c1 * |p.2 (Sum.inl (Sum.inr ()))| + c2 * |(σ ℓ).2 0|)
  have hdom_σ : Integrable dom_σ (Measure.pi fun _ : J => ν p) :=
    ((integrable_const _).add (hη_pi.const_mul c2)).const_mul (|C_f| * |D|)
  have hG_pt (σ : J → T) : ‖G_lhs p σ‖ ≤ dom_σ σ := by
    dsimp only [G_lhs, dom_σ]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 := (hfb p.1 (fun j => (σ j).1)).trans (le_abs_self C_f)
    have h2 := hWt_le (σ ℓ)
    have h3 := (hu.abs_deriv_le (X_fn p.2 (σ ℓ))).trans (le_abs_self D)
    calc |f p.1 (fun j => (σ j).1)| * |Wt p.2 (σ ℓ)| * |deriv u (X_fn p.2 (σ ℓ))|
        = (|f p.1 (fun j => (σ j).1)| * |deriv u (X_fn p.2 (σ ℓ))|) * |Wt p.2 (σ ℓ)| := by ring
      _ ≤ (|C_f| * |D|) * (c1 * |p.2 (Sum.inl (Sum.inr ()))| + c2 * |(σ ℓ).2 0|) :=
          mul_le_mul (mul_le_mul h1 h3 (abs_nonneg _) (abs_nonneg _)) h2 (abs_nonneg _)
            (by positivity)
  have hG_int : Integrable (G_lhs p) (Measure.pi fun _ : J => ν p) :=
    hdom_σ.mono' (hGm_lhs.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ hG_pt)
  rw [Real.norm_eq_abs]
  calc |∫ σ : J → T, G_lhs p σ ∂(Measure.pi fun _ : J => ν p)|
      ≤ ∫ σ : J → T, |G_lhs p σ| ∂(Measure.pi fun _ : J => ν p) := abs_integral_le_integral_abs
    _ ≤ ∫ σ : J → T, dom_σ σ ∂(Measure.pi fun _ : J => ν p) :=
        integral_mono hG_int.abs hdom_σ fun σ => by simpa only [Real.norm_eq_abs] using hG_pt σ
    _ = |C_f| * |D| *
          (c1 * |p.2 (Sum.inl (Sum.inr ()))| + c2 * ∫ y : T, |y.2 0| ∂(ν p)) := by
        dsimp only [dom_σ]
        rw [integral_const_mul, integral_add (integrable_const _) (hη_pi.const_mul c2),
          integral_const, probReal_univ, one_smul, integral_const_mul, hη_pi_int]
    _ ≤ dom_w p.2 :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hη_comp hc2)) (by positivity)

/-- **Disorder-averaged one-step Stein formula for the last constraint of the `(s, t)`-smart path.** -/
private lemma integral_interpSPFieldDeriv_mul_deriv_last
    {N M : ℕ} {J : Type uR} [Fintype J] [DecidableEq J]
    {s : ℝ} (hs0 : 0 ≤ s) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (q r : ℝ) (v : ℝ≥0)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ℓ : J) (f : (J → PerceptronSpin N) → ℝ) :
    let P := interpSPDisorder N (M + 1) v
    let μ (ω : InterpSPDisorder N (M + 1)) :=
      (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)
    let S' (ω : InterpSPDisorder N (M + 1)) (x : InterpSPState N (M + 1)) : ℝ :=
      Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.1.2 (Fin.last M) * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t -
          x.2 (Fin.last M) 0 / Real.sqrt (1 - t)))
    ∫ ω, ∫ σ : J → InterpSPState N (M + 1),
        f (fun j => (σ j).1) * S' ω (σ ℓ) * deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : J => μ ω) ∂P =
      (s / (2 * (N + 1))) *
        ((∑ j ∈ Finset.univ.erase ℓ,
          ∫ ω, ∫ σ : J → InterpSPState N (M + 1),
            f (fun k => (σ k).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
              deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M)) *
              deriv u (interpSPField s t q ω (σ j) (Fin.last M))
            ∂(Measure.pi fun _ : J => μ ω) ∂P) -
        (Fintype.card J : ℝ) *
          ∫ ω, ∫ σ : Option J → InterpSPState N (M + 1),
            f (fun k => (σ (some k)).1) *
              (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
              deriv u (interpSPField s t q ω (σ (some ℓ)) (Fin.last M)) *
              deriv u (interpSPField s t q ω (σ none) (Fin.last M))
            ∂(Measure.pi fun _ : Option J => μ ω) ∂P) := by
  intro P μ S'
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  let P₀ := interpSPDisorder N M v
  let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
  let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
  let μ₀ (ω₀ : InterpSPDisorder N M) :=
    (interpSPBase N M).tilted (interpSPEnergy u s t q r ω₀)
  let α_sh (σ : PerceptronSpin N) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ :=
    Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
  let W_sh (σ : PerceptronSpin N) : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ :=
    Sum.elim (Sum.elim 0 (fun _ =>
      Real.sqrt s * (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))) 0
  let α_aux : Fin 2 → ℝ :=
    ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)), Real.sqrt (1 - s) * Real.sqrt (1 - q)]
  let W_aux : Fin 2 → ℝ :=
    ![-Real.sqrt s / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)), 0]
  let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
    α_sh y.1.1 ⬝ᵥ w₁ + α_aux ⬝ᵥ y.2
  let Wt (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (y : InterpSPState N M × (Fin 2 → ℝ)) : ℝ :=
    W_sh y.1.1 ⬝ᵥ w₁ + W_aux ⬝ᵥ y.2
  let Ω := InterpSPDisorder N M
  let W := ((Fin N ⊕ Unit) ⊕ Unit) → ℝ
  let T := InterpSPState N M × (Fin 2 → ℝ)
  let ν (p : Ω × W) := ((μ₀ p.1).prod γ₂).tilted (fun y => u (X_fn p.2 y))
  have hμ₀ (ω₀ : Ω) : IsProbabilityMeasure (μ₀ ω₀) :=
    isProbabilityMeasure_tilted_interpSPEnergy hu.measurable (fun x => hu.le x) s t q r ω₀
  have hXm : Measurable fun p : W × T => X_fn p.1 p.2 := by
    have hX1 (j : (Fin N ⊕ Unit) ⊕ Unit) : Measurable fun p : W × T => α_sh p.2.1.1 j :=
      (measurable_of_finite fun σ => α_sh σ j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : W × T => α_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hX1 j).mul ((measurable_pi_apply j).comp measurable_fst)
    have hd2 : Measurable fun p : W × T => α_aux ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hd1.add hd2
  have hWtm : Measurable fun p : W × T => Wt p.1 p.2 := by
    have hW1 (j : (Fin N ⊕ Unit) ⊕ Unit) : Measurable fun p : W × T => W_sh p.2.1.1 j :=
      (measurable_of_finite fun σ => W_sh σ j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : W × T => W_sh p.2.1.1 ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hW1 j).mul ((measurable_pi_apply j).comp measurable_fst)
    have hd2 : Measurable fun p : W × T => W_aux ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hd1.add hd2
  let f_old (_ : Ω) (a : J → InterpSPState N M) : ℝ := f (fun j => (a j).1)
  have hf_old_m : Measurable fun p : Ω × (J → InterpSPState N M) => f_old p.1 p.2 :=
    (measurable_of_finite f).comp (measurable_pi_iff.2 fun j =>
      measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd))
  have hfi (ω₀ : Ω) : Integrable (f_old ω₀) (Measure.pi fun _ : J => μ₀ ω₀) := by
    have hp : Measurable fun a : J → InterpSPState N M => (ω₀, a) :=
      measurable_const.prodMk measurable_id
    have hm := hf_old_m.comp hp
    exact Integrable.of_bound hm.aestronglyMeasurable |C_f|
      (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact (hCf _).trans (le_abs_self _))
  let G_lhs (p : Ω × W) (σ : J → T) : ℝ :=
    f (fun j => (σ j).1.1) * Wt p.2 (σ ℓ) * deriv u (X_fn p.2 (σ ℓ))
  let G_off (j : J) (p : Ω × W) (σ : J → T) : ℝ :=
    f (fun k => (σ k).1.1) * (((σ ℓ).1.1.2 : ℤ) : ℝ) * (((σ j).1.1.2 : ℤ) : ℝ) *
      deriv u (X_fn p.2 (σ ℓ)) * deriv u (X_fn p.2 (σ j))
  let G_fresh (p : Ω × W) (σ : Option J → T) : ℝ :=
    f (fun k => (σ (some k)).1.1) *
      (((σ (some ℓ)).1.1.2 : ℤ) : ℝ) * (((σ none).1.1.2 : ℤ) : ℝ) *
      deriv u (X_fn p.2 (σ (some ℓ))) * deriv u (X_fn p.2 (σ none))
  have hGm_lhs : Measurable fun p : (Ω × W) × (J → T) => G_lhs p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (J → T) => (fun j => (p.2 j).1.1) :=
      measurable_pi_iff.2 fun j =>
        measurable_fst.comp (measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd))
    have hp2 : Measurable fun p : (Ω × W) × (J → T) => (p.1.2, p.2 ℓ) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply ℓ).comp measurable_snd)
    have m1 := (measurable_of_finite f).comp hp1
    have m2 := hWtm.comp hp2
    have mx2 := hXm.comp hp2
    have m3 := (measurable_deriv u).comp mx2
    exact (m1.mul m2).mul m3
  have hGm_off (j : J) : Measurable fun p : (Ω × W) × (J → T) => G_off j p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (J → T) => (fun k => (p.2 k).1.1) :=
      measurable_pi_iff.2 fun k =>
        measurable_fst.comp (measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd))
    have m1 := (measurable_of_finite f).comp hp1
    have mS (k : J) : Measurable fun p : (Ω × W) × (J → T) => deriv u (X_fn p.1.2 (p.2 k)) := by
      have hp_k : Measurable fun p : (Ω × W) × (J → T) => (p.1.2, p.2 k) :=
        (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply k).comp measurable_snd)
      have hx_k := hXm.comp hp_k
      exact (measurable_deriv u).comp hx_k
    have hε (k : J) : Measurable fun p : (Ω × W) × (J → T) => (((p.2 k).1.1.2 : ℤ) : ℝ) :=
      measurable_units_cast.comp
        (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
          ((measurable_pi_apply k).comp measurable_snd))))
    exact (((m1.mul (hε ℓ)).mul (hε j)).mul (mS ℓ)).mul (mS j)
  have hGm_fresh : Measurable fun p : (Ω × W) × (Option J → T) => G_fresh p.1 p.2 := by
    have hp1 : Measurable fun p : (Ω × W) × (Option J → T) => (fun k => (p.2 (some k)).1.1) :=
      measurable_pi_iff.2 fun k =>
        measurable_fst.comp (measurable_fst.comp
          ((measurable_pi_apply (some k)).comp measurable_snd))
    have m1 := (measurable_of_finite f).comp hp1
    have mS (k : Option J) :
        Measurable fun p : (Ω × W) × (Option J → T) => deriv u (X_fn p.1.2 (p.2 k)) := by
      have hp_k : Measurable fun p : (Ω × W) × (Option J → T) => (p.1.2, p.2 k) :=
        (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply k).comp measurable_snd)
      have hx_k := hXm.comp hp_k
      exact (measurable_deriv u).comp hx_k
    have hε (k : Option J) :
        Measurable fun p : (Ω × W) × (Option J → T) => (((p.2 k).1.1.2 : ℤ) : ℝ) :=
      measurable_units_cast.comp
        (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
          ((measurable_pi_apply k).comp measurable_snd))))
    exact (((m1.mul (hε (some ℓ))).mul (hε none)).mul (mS (some ℓ))).mul (mS none)
  -- Helper for integrability of bounded `G` on `P₀.prod γ₁`:
  have hint_bdd {ι : Type uR} [Fintype ι] {G : (Ω × W) → (ι → T) → ℝ}
      (hGm : Measurable fun p : (Ω × W) × (ι → T) => G p.1 p.2)
      {K_b : ℝ} (hGb : ∀ p σ, |G p σ| ≤ K_b) :
      Integrable (fun p : Ω × W => ∫ σ : ι → T, G p σ ∂(Measure.pi fun _ : ι => ν p))
        (P₀.prod γ₁) := by
    let H_comb (p : Ω × W) (y : T) : ℝ := interpSPEnergy u s t q r p.1 y.1 + u (X_fn p.2 y)
    have hHm : Measurable fun p : (Ω × W) × T => H_comb p.1 p.2 := by
      have hp1 : Measurable fun p : (Ω × W) × T => (p.1.1, p.2.1) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
      have hp2 : Measurable fun p : (Ω × W) × T => (p.1.2, p.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have he1 := (measurable_interpSPEnergy hu.measurable s t q r).comp hp1
      have hx2 := hXm.comp hp2
      exact he1.add (hu.measurable.comp hx2)
    have hν_eq (p : Ω × W) : ν p = ((interpSPBase N M).prod γ₂).tilted (H_comb p) := by
      dsimp only [ν, μ₀]
      rw [← tilted_prod_comp_fst, tilted_tilted
        ((integrable_exp_interpSPEnergy hu.measurable (fun x => hu.le x) s t q r p.1).comp_fst γ₂)]
      rfl
    have hm_int : Measurable fun p : Ω × W => ∫ σ : ι → T, G p σ ∂(Measure.pi fun _ : ι => ν p) := by
      have heq : (fun p : Ω × W => ∫ σ : ι → T, G p σ ∂(Measure.pi fun _ : ι => ν p)) =
          fun p => ∫ σ : ι → T, G p σ
            ∂(Measure.pi fun _ : ι => ((interpSPBase N M).prod γ₂).tilted (H_comb p)) := by
        funext p; simp_rw [hν_eq p]
      rw [heq]
      exact measurable_integral_pi_tilted (μ := (interpSPBase N M).prod γ₂) hHm hGm
    refine Integrable.of_bound hm_int.aestronglyMeasurable K_b (ae_of_all _ fun p => ?_)
    have hp_id : Measurable fun y : T => (p.2, y) := measurable_const.prodMk measurable_id
    have hx_id := hXm.comp hp_id
    have : IsProbabilityMeasure (ν p) :=
      isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp hx_id).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_forall_abs_le _ (hGb p)
  have hI_lhs : Integrable
      (fun p : Ω × W => ∫ σ : J → T, G_lhs p σ ∂(Measure.pi fun _ : J => ν p)) (P₀.prod γ₁) :=
    integrable_integral_pi_interpSP_last_split_deriv s ht q r v hu.toSmartPathPotential ℓ
      hf_old_m (fun _ _ => hCf _)
  have hI_off (j : J) : Integrable
      (fun p : Ω × W => ∫ σ : J → T, G_off j p σ ∂(Measure.pi fun _ : J => ν p)) (P₀.prod γ₁) :=
    hint_bdd (hGm_off j) (K_b := |C_f| * |D| ^ 2) fun p σ => by
      dsimp only [G_off]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one,
        mul_one, mul_one, sq, mul_assoc]
      exact mul_le_mul ((hCf _).trans (le_abs_self _))
        (mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self _))
          ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hI_fresh : Integrable
      (fun p : Ω × W => ∫ σ : Option J → T, G_fresh p σ ∂(Measure.pi fun _ : Option J => ν p))
      (P₀.prod γ₁) :=
    hint_bdd hGm_fresh (K_b := |C_f| * |D| ^ 2) fun p σ => by
      dsimp only [G_fresh]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one,
        mul_one, mul_one, sq, mul_assoc]
      exact mul_le_mul ((hCf _).trans (le_abs_self _))
        (mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self _))
          ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  let L₀ (ω₀ : Ω) : ℝ := ∫ w₁, ∫ σ : J → T, G_lhs (ω₀, w₁) σ ∂(Measure.pi fun _ : J => ν (ω₀, w₁)) ∂γ₁
  let O₀ (j : J) (ω₀ : Ω) : ℝ :=
    ∫ w₁, ∫ σ : J → T, G_off j (ω₀, w₁) σ ∂(Measure.pi fun _ : J => ν (ω₀, w₁)) ∂γ₁
  let F₀ (ω₀ : Ω) : ℝ :=
    ∫ w₁, ∫ σ : Option J → T, G_fresh (ω₀, w₁) σ ∂(Measure.pi fun _ : Option J => ν (ω₀, w₁)) ∂γ₁
  have hO_int (j : J) : Integrable (O₀ j) P₀ := (hI_off j).integral_prod_left
  have hF_int : Integrable F₀ P₀ := hI_fresh.integral_prod_left
  have ht_lhs := integral_pi_interpSP_last_split_eq hu.measurable (fun x => hu.le x) s t q r v hGm_lhs
  have ht_off (j : J) := integral_pi_interpSP_last_split_eq hu.measurable (fun x => hu.le x) s t q r v (hGm_off j)
  have ht_fresh := integral_pi_interpSP_last_split_eq hu.measurable (fun x => hu.le x) s t q r v hGm_fresh
  have hX_split_eq (ω : InterpSPDisorder N (M + 1)) (x : InterpSPState N (M + 1)) :
      X_fn (Sum.elim (Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)))
          (fun _ : Unit => ω.1.2 (Fin.last M)))
        (interpSPStateSplit N M x) = interpSPField s t q ω x (Fin.last M) := by
    rw [interpSPStateSplit_apply]
    dsimp only [X_fn, α_sh, α_aux]
    unfold interpSPField
    have hnoaux : smartPathFieldNoAux t (ω.1.1, ω.2.2.1) (x.1, 0) (Fin.last M) =
        cavityCoef N t x.1 ⬝ᵥ
          Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)) := by
      simp only [smartPathFieldNoAux_eq, cavityCoef, dotProduct, Fintype.sum_sum_type,
        Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) (by ring)
      push_cast; ring
    rw [hnoaux, sumElim_dotProduct_sumElim, smul_dotProduct, smul_eq_mul]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hWt_split_eq (ω : InterpSPDisorder N (M + 1)) (x : InterpSPState N (M + 1)) :
      Wt (Sum.elim (Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)))
          (fun _ : Unit => ω.1.2 (Fin.last M)))
        (interpSPStateSplit N M x) = S' ω x := by
    rw [interpSPStateSplit_apply]
    dsimp only [Wt, W_sh, W_aux, S']
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, zero_add, Finset.univ_unique,
      Finset.sum_singleton, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have heq_lhs :
      (∫ ω, ∫ σ : J → InterpSPState N (M + 1),
        f (fun j => (σ j).1) * S' ω (σ ℓ) * deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : J => μ ω) ∂P) = ∫ ω₀, L₀ ω₀ ∂P₀ := by
    dsimp only [L₀]
    rw [← integral_prod _ hI_lhs, ht_lhs]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [G_lhs]
    rw [hWt_split_eq, hX_split_eq]
    simp only [interpSPStateSplit_apply]
  have heq_off (j : J) :
      (∫ ω, ∫ σ : J → InterpSPState N (M + 1),
        f (fun k => (σ k).1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ j) (Fin.last M))
        ∂(Measure.pi fun _ : J => μ ω) ∂P) = ∫ ω₀, O₀ j ω₀ ∂P₀ := by
    dsimp only [O₀]
    rw [← integral_prod _ (hI_off j), ht_off j]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [G_off]
    rw [hX_split_eq, hX_split_eq]
    simp only [interpSPStateSplit_apply]
  have heq_fresh :
      (∫ ω, ∫ σ : Option J → InterpSPState N (M + 1),
        f (fun k => (σ (some k)).1) *
          (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option J => μ ω) ∂P) = ∫ ω₀, F₀ ω₀ ∂P₀ := by
    dsimp only [F₀]
    rw [← integral_prod _ hI_fresh, ht_fresh]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun σ => ?_))
    dsimp only [G_fresh]
    rw [hX_split_eq, hX_split_eq]
    simp only [interpSPStateSplit_apply]
  rw [heq_lhs, Finset.sum_congr rfl fun j _ => heq_off j, heq_fresh]
  have hpt (ω₀ : Ω) : L₀ ω₀ =
      (s / (2 * (N + 1))) *
        ((∑ j ∈ Finset.univ.erase ℓ, O₀ j ω₀) - (Fintype.card J : ℝ) * F₀ ω₀) :=
    stein_interpSP_last_constraint_split hs0 ht q r hu ω₀ ℓ (hfi ω₀)
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrable_finsetSum _ fun j _ => hO_int j)
    (hF_int.const_mul _), integral_finsetSum _ fun j _ => hO_int j, integral_const_mul]

/-- **One-step recovery of term I of `∂_t ν_{t, s}(f)` at `Fin.last M`.** -/
private lemma interpSP_one_step_recovery_last
    {N M : ℕ} {R : Type uR} [Fintype R] [LinearOrder R]
    {s : ℝ} (hs0 : 0 ≤ s) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (q r : ℝ) (v : ℝ≥0)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (f : (R → PerceptronSpin N) → ℝ) :
    let P := interpSPDisorder N (M + 1) v
    let μ (ω : InterpSPDisorder N (M + 1)) :=
      (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)
    let S' (ω : InterpSPDisorder N (M + 1)) (x : InterpSPState N (M + 1)) : ℝ :=
      Real.sqrt s * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.1.2 (Fin.last M) * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t -
          x.2 (Fin.last M) 0 / Real.sqrt (1 - t)))
    let U (ω : InterpSPDisorder N (M + 1)) (a b : InterpSPState N (M + 1)) : ℝ :=
      ((a.1.2 : ℤ) : ℝ) * ((b.1.2 : ℤ) : ℝ) *
        deriv u (interpSPField s t q ω a (Fin.last M)) *
        deriv u (interpSPField s t q ω b (Fin.last M))
    (∑ ℓ : R, ∫ ω, ∫ σ : R → InterpSPState N (M + 1),
        f (fun r' => (σ r').1) * S' ω (σ ℓ) *
          deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω) ∂P) -
      (Fintype.card R : ℝ) *
        ∫ ω, ∫ σ : Option R → InterpSPState N (M + 1),
          f (fun r' => (σ (some r')).1) * S' ω (σ none) *
            deriv u (interpSPField s t q ω (σ none) (Fin.last M))
          ∂(Measure.pi fun _ : Option R => μ ω) ∂P =
      (s / (N + 1)) * ∫ ω, replicaPairAverage (μ ω)
        (fun σ : R → InterpSPState N (M + 1) => f (fun r' => (σ r').1)) (U ω) ∂P := by
  intro P μ S' U
  obtain ⟨C_f, hCf⟩ := exists_abs_le_of_finite f
  have h1 (ℓ : R) := integral_interpSPFieldDeriv_mul_deriv_last (M := M) hs0 ht q r v hu ℓ f
  have h2 := integral_interpSPFieldDeriv_mul_deriv_last (M := M) hs0 ht q r v hu
    (none : Option R) (fun a => f (fun r' => a (some r')))
  change (∑ ℓ : R, ∫ ω, ∫ σ : R → InterpSPState N (M + 1),
        f (fun j => (σ j).1) * S' ω (σ ℓ) *
          deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω) ∂P) -
      (Fintype.card R : ℝ) *
        ∫ ω, ∫ σ : Option R → InterpSPState N (M + 1),
          f (fun r' => (fun j => (σ j).1) (some r')) * S' ω (σ none) *
            deriv u (interpSPField s t q ω (σ none) (Fin.last M))
          ∂(Measure.pi fun _ : Option R => μ ω) ∂P = _
  rw [Finset.sum_congr rfl fun ℓ _ => h1 ℓ, h2]
  dsimp only
  have hU_symm (ω : InterpSPDisorder N (M + 1)) (a b : InterpSPState N (M + 1)) :
      U ω a b = U ω b a := by dsimp only [U]; ring
  have hμ_prob (ω : InterpSPDisorder N (M + 1)) : IsProbabilityMeasure (μ ω) :=
    isProbabilityMeasure_tilted_interpSPEnergy hu.measurable (fun x => hu.le x) s t q r ω
  let e₂ : R → Option (Option R) := fun r' => some (some r')
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp (Option.some_injective _)
  let e₁ : Option R → Option (Option R) := some
  have he₁ : Function.Injective e₁ := Option.some_injective _
  let Φ (i j : Option (Option R)) (ω : InterpSPDisorder N (M + 1))
      (τ : Option (Option R) → InterpSPState N (M + 1)) : ℝ :=
    f (fun r' => (τ (some (some r'))).1) * U ω (τ i) (τ j)
  let T_pair (i j : Option (Option R)) (ω : InterpSPDisorder N (M + 1)) : ℝ :=
    ∫ τ : Option (Option R) → InterpSPState N (M + 1), Φ i j ω τ
      ∂(Measure.pi fun _ : Option (Option R) => μ ω)
  have hΦm (i j : Option (Option R)) : Measurable fun p : InterpSPDisorder N (M + 1) ×
      (Option (Option R) → InterpSPState N (M + 1)) => Φ i j p.1 p.2 := by
    have hf2 : Measurable fun p : InterpSPDisorder N (M + 1) ×
        (Option (Option R) → InterpSPState N (M + 1)) =>
        f (fun r' => (p.2 (some (some r'))).1) :=
      (measurable_of_finite f).comp (measurable_pi_iff.2 fun r' =>
        measurable_fst.comp ((measurable_pi_apply (some (some r'))).comp measurable_snd))
    have hfl (k : Option (Option R)) : Measurable fun p : InterpSPDisorder N (M + 1) ×
        (Option (Option R) → InterpSPState N (M + 1)) =>
        deriv u (interpSPField s t q p.1 (p.2 k) (Fin.last M)) := by
      have hp_k : Measurable fun p : InterpSPDisorder N (M + 1) ×
          (Option (Option R) → InterpSPState N (M + 1)) => (p.1, p.2 k) :=
        measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd)
      have hf_k := (measurable_interpSPField s t q (Fin.last M)).comp hp_k
      exact (measurable_deriv u).comp hf_k
    have hε (k : Option (Option R)) : Measurable fun p : InterpSPDisorder N (M + 1) ×
        (Option (Option R) → InterpSPState N (M + 1)) => (((p.2 k).1.2 : ℤ) : ℝ) :=
      measurable_units_cast.comp
        (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)))
    exact hf2.mul ((((hε i).mul (hε j)).mul (hfl i)).mul (hfl j))
  have hΦb (i j : Option (Option R)) (ω : InterpSPDisorder N (M + 1))
      (τ : Option (Option R) → InterpSPState N (M + 1)) : |Φ i j ω τ| ≤ |C_f| * |D| ^ 2 := by
    dsimp only [Φ, U]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one,
      one_mul, one_mul, sq]
    exact mul_le_mul ((hCf _).trans (le_abs_self _))
      (mul_le_mul ((hu.abs_deriv_le _).trans (le_abs_self _))
        ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hT_int (i j : Option (Option R)) : Integrable (T_pair i j) P := by
    have hm := measurable_integral_pi_tilted (μ := interpSPBase N (M + 1))
      (measurable_interpSPEnergy hu.measurable s t q r) (hΦm i j)
    exact Integrable.of_bound hm.aestronglyMeasurable (|C_f| * |D| ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_forall_abs_le _ (hΦb i j ω))
  have hΦ_int (i j : Option (Option R)) (ω : InterpSPDisorder N (M + 1)) :
      Integrable (Φ i j ω) (Measure.pi fun _ : Option (Option R) => μ ω) :=
    Integrable.of_bound
      ((hΦm i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (|C_f| * |D| ^ 2) (ae_of_all _ fun τ => by simpa using hΦb i j ω τ)
  have hlift_0 (ℓ j : R) (ω : InterpSPDisorder N (M + 1)) :
      (∫ σ : R → InterpSPState N (M + 1),
        f (fun r' => (σ r').1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ j) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω)) =
      T_pair (some (some ℓ)) (some (some j)) ω := by
    have hm : Measurable fun σ : R → InterpSPState N (M + 1) =>
        f (fun r' => (σ r').1) * U ω (σ ℓ) (σ j) := by
      have hfm : Measurable fun σ : R → InterpSPState N (M + 1) => f (fun r' => (σ r').1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r' =>
          measurable_fst.comp (measurable_pi_apply r'))
      have hfl (k : R) : Measurable fun σ : R → InterpSPState N (M + 1) =>
          deriv u (interpSPField s t q ω (σ k) (Fin.last M)) := by
        have hp_k : Measurable fun σ : R → InterpSPState N (M + 1) => (ω, σ k) :=
          measurable_const.prodMk (measurable_pi_apply k)
        have h1 := (measurable_interpSPField s t q (Fin.last M)).comp hp_k
        exact (measurable_deriv u).comp h1
      have hε (k : R) : Measurable fun σ : R → InterpSPState N (M + 1) =>
          (((σ k).1.2 : ℤ) : ℝ) :=
        measurable_units_cast.comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply k)))
      exact hfm.mul ((((hε ℓ).mul (hε j)).mul (hfl ℓ)).mul (hfl j))
    have hpt (σ : R → InterpSPState N (M + 1)) :
        f (fun r' => (σ r').1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ j) (Fin.last M)) =
        f (fun r' => (σ r').1) * U ω (σ ℓ) (σ j) := by dsimp only [U]; ring
    simp_rw [hpt]
    exact (integral_pi_comp_injective (μ ω) he₂ _ hm.aestronglyMeasurable).symm
  have hlift_1 (ℓ : R) (ω : InterpSPDisorder N (M + 1)) :
      (∫ σ : Option R → InterpSPState N (M + 1),
        f (fun r' => (σ (some r')).1) * (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option R => μ ω)) =
      T_pair (some (some ℓ)) (some none) ω := by
    have hm : Measurable fun σ : Option R → InterpSPState N (M + 1) =>
        f (fun r' => (σ (some r')).1) * U ω (σ (some ℓ)) (σ none) := by
      have hfm : Measurable fun σ : Option R → InterpSPState N (M + 1) =>
          f (fun r' => (σ (some r')).1) :=
        (measurable_of_finite f).comp (measurable_pi_iff.2 fun r' =>
          measurable_fst.comp (measurable_pi_apply (some r')))
      have hfl (k : Option R) : Measurable fun σ : Option R → InterpSPState N (M + 1) =>
          deriv u (interpSPField s t q ω (σ k) (Fin.last M)) := by
        have hp_k : Measurable fun σ : Option R → InterpSPState N (M + 1) => (ω, σ k) :=
          measurable_const.prodMk (measurable_pi_apply k)
        have h1 := (measurable_interpSPField s t q (Fin.last M)).comp hp_k
        exact (measurable_deriv u).comp h1
      have hε (k : Option R) : Measurable fun σ : Option R → InterpSPState N (M + 1) =>
          (((σ k).1.2 : ℤ) : ℝ) :=
        measurable_units_cast.comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply k)))
      exact hfm.mul ((((hε (some ℓ)).mul (hε none)).mul (hfl (some ℓ))).mul (hfl none))
    have hpt (σ : Option R → InterpSPState N (M + 1)) :
        f (fun r' => (σ (some r')).1) * (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ none) (Fin.last M)) =
        f (fun r' => (σ (some r')).1) * U ω (σ (some ℓ)) (σ none) := by dsimp only [U]; ring
    simp_rw [hpt]
    exact (integral_pi_comp_injective (μ ω) he₁ _ hm.aestronglyMeasurable).symm
  have hlift_1' (j : R) (ω : InterpSPDisorder N (M + 1)) :
      (∫ σ : Option R → InterpSPState N (M + 1),
        f (fun r' => (σ (some r')).1) * (((σ none).1.2 : ℤ) : ℝ) * (((σ (some j)).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ none) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ (some j)) (Fin.last M))
        ∂(Measure.pi fun _ : Option R => μ ω)) =
      T_pair (some (some j)) (some none) ω := by
    rw [← hlift_1 j ω]
    exact integral_congr_ae (ae_of_all _ fun _ => by ring)
  have hlift_2 (ω : InterpSPDisorder N (M + 1)) :
      (∫ σ : Option (Option R) → InterpSPState N (M + 1),
        f (fun r' => (σ (some (some r'))).1) *
          (((σ (some none)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ (some none)) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω)) =
      T_pair (some none) none ω :=
    integral_congr_ae (ae_of_all _ fun _ => by dsimp only [Φ, U]; ring)
  have hs0_eq (ℓ j : R) :
      (∫ ω, ∫ σ : R → InterpSPState N (M + 1),
        f (fun r' => (σ r').1) * (((σ ℓ).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ ℓ) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ j) (Fin.last M))
        ∂(Measure.pi fun _ : R => μ ω) ∂P) =
      ∫ ω, T_pair (some (some ℓ)) (some (some j)) ω ∂P :=
    integral_congr_ae (ae_of_all _ (hlift_0 ℓ j))
  have hs1_eq (ℓ : R) :
      (∫ ω, ∫ σ : Option R → InterpSPState N (M + 1),
        f (fun r' => (σ (some r')).1) * (((σ (some ℓ)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ (some ℓ)) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option R => μ ω) ∂P) =
      ∫ ω, T_pair (some (some ℓ)) (some none) ω ∂P :=
    integral_congr_ae (ae_of_all _ (hlift_1 ℓ))
  have hs2_eq :
      (∫ ω, ∫ σ : Option (Option R) → InterpSPState N (M + 1),
        f (fun r' => (σ (some (some r'))).1) *
          (((σ (some none)).1.2 : ℤ) : ℝ) * (((σ none).1.2 : ℤ) : ℝ) *
          deriv u (interpSPField s t q ω (σ (some none)) (Fin.last M)) *
          deriv u (interpSPField s t q ω (σ none) (Fin.last M))
        ∂(Measure.pi fun _ : Option (Option R) => μ ω) ∂P) =
      ∫ ω, T_pair (some none) none ω ∂P :=
    integral_congr_ae (ae_of_all _ hlift_2)
  have herase_opt :
      (∑ j ∈ (Finset.univ : Finset (Option R)).erase none,
        ∫ ω, ∫ σ : Option R → InterpSPState N (M + 1),
          f (fun r' => (σ (some r')).1) * (((σ none).1.2 : ℤ) : ℝ) * (((σ j).1.2 : ℤ) : ℝ) *
            deriv u (interpSPField s t q ω (σ none) (Fin.last M)) *
            deriv u (interpSPField s t q ω (σ j) (Fin.last M))
          ∂(Measure.pi fun _ : Option R => μ ω) ∂P) =
      ∑ r' : R, ∫ ω, T_pair (some (some r')) (some none) ω ∂P := by
    have hmap : ((Finset.univ : Finset (Option R)).erase none) =
        Finset.univ.map ⟨Option.some, Option.some_injective R⟩ := by
      ext x; cases x <;> simp
    rw [hmap, Finset.sum_map]
    exact Finset.sum_congr rfl fun r' _ => integral_congr_ae (ae_of_all _ (hlift_1' r'))
  dsimp only [μ, P] at hs0_eq hs1_eq herase_opt hs2_eq
  simp_rw [hs0_eq, hs1_eq, herase_opt, hs2_eq]
  have hpull_ω (ℓ : R) :
      (∑ j ∈ Finset.univ.erase ℓ, ∫ ω, T_pair (some (some ℓ)) (some (some j)) ω ∂P) -
        (Fintype.card R : ℝ) * ∫ ω, T_pair (some (some ℓ)) (some none) ω ∂P =
      ∫ ω, ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
        (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω) ∂P := by
    rw [integral_sub (integrable_finsetSum _ fun j _ => hT_int _ _)
      ((hT_int _ _).const_mul _), integral_finsetSum _ fun j _ => hT_int _ _, integral_const_mul]
  have hpull_opt :
      (∑ r' : R, ∫ ω, T_pair (some (some r')) (some none) ω ∂P) -
        (Fintype.card (Option R) : ℝ) * ∫ ω, T_pair (some none) none ω ∂P =
      ∫ ω, ((∑ r' : R, T_pair (some (some r')) (some none) ω) -
        (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) ∂P := by
    rw [integral_sub (integrable_finsetSum _ fun r' _ => hT_int _ _)
      ((hT_int _ _).const_mul _), integral_finsetSum _ fun r' _ => hT_int _ _, integral_const_mul]
  dsimp only [P] at hpull_ω hpull_opt hT_int ⊢
  simp_rw [hpull_ω, hpull_opt, ← Finset.mul_sum]
  have hI_sum : Integrable (fun ω => ∑ ℓ : R,
      ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
        (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω)) P :=
    integrable_finsetSum _ fun ℓ _ =>
      (integrable_finsetSum _ fun j _ => hT_int _ _).sub ((hT_int _ _).const_mul _)
  have hI_opt2 : Integrable (fun ω =>
      (∑ r' : R, T_pair (some (some r')) (some none) ω) -
        (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) P :=
    (integrable_finsetSum _ fun r' _ => hT_int _ _).sub ((hT_int _ _).const_mul _)
  rw [← integral_finsetSum Finset.univ (f := fun (ℓ : R) (ω : InterpSPDisorder N (M + 1)) =>
    (∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
      (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω) fun ℓ _ =>
    (integrable_finsetSum _ fun j _ => hT_int _ _).sub ((hT_int _ _).const_mul _)]
  have hcomb_outer :
      (s / (2 * ((N : ℝ) + 1))) * ∫ ω, (∑ ℓ : R,
        ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
          (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω)) ∂P -
      (Fintype.card R : ℝ) * ((s / (2 * ((N : ℝ) + 1))) * ∫ ω,
        ((∑ r' : R, T_pair (some (some r')) (some none) ω) -
          (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) ∂P) =
      (s / ((N : ℝ) + 1)) * ∫ ω, (1 / 2) *
        ((∑ ℓ : R, ((∑ j ∈ Finset.univ.erase ℓ, T_pair (some (some ℓ)) (some (some j)) ω) -
          (Fintype.card R : ℝ) * T_pair (some (some ℓ)) (some none) ω)) -
        (Fintype.card R : ℝ) * ((∑ r' : R, T_pair (some (some r')) (some none) ω) -
          (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω)) ∂P := by
    have hsub_eq := integral_sub hI_sum (hI_opt2.const_mul (Fintype.card R : ℝ))
    have hmul_eq := integral_const_mul (Fintype.card R : ℝ)
      (fun ω => (∑ r' : R, T_pair (some (some r')) (some none) ω) -
        (Fintype.card (Option R) : ℝ) * T_pair (some none) none ω) (μ := P)
    rw [integral_const_mul (1 / 2), hsub_eq, hmul_eq]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    field_simp
  rw [hcomb_outer]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only [T_pair]
  have hp_in1 (ℓ : R) :
      (∑ j ∈ Finset.univ.erase ℓ,
        ∫ τ, Φ (some (some ℓ)) (some (some j)) ω τ ∂(Measure.pi fun _ => μ ω)) -
      (Fintype.card R : ℝ) *
        ∫ τ, Φ (some (some ℓ)) (some none) ω τ ∂(Measure.pi fun _ => μ ω) =
      ∫ τ, ((∑ j ∈ Finset.univ.erase ℓ, Φ (some (some ℓ)) (some (some j)) ω τ) -
        (Fintype.card R : ℝ) * Φ (some (some ℓ)) (some none) ω τ) ∂(Measure.pi fun _ => μ ω) := by
    rw [integral_sub (integrable_finsetSum _ fun j _ => hΦ_int _ _ ω)
      ((hΦ_int _ _ ω).const_mul _), integral_finsetSum _ fun j _ => hΦ_int _ _ ω,
      integral_const_mul]
  have hp_in2 :
      (∑ r' : R, ∫ τ, Φ (some (some r')) (some none) ω τ ∂(Measure.pi fun _ => μ ω)) -
      (Fintype.card (Option R) : ℝ) *
        ∫ τ, Φ (some none) none ω τ ∂(Measure.pi fun _ => μ ω) =
      ∫ τ, ((∑ r' : R, Φ (some (some r')) (some none) ω τ) -
        (Fintype.card (Option R) : ℝ) * Φ (some none) none ω τ) ∂(Measure.pi fun _ => μ ω) := by
    rw [integral_sub (integrable_finsetSum _ fun r' _ => hΦ_int _ _ ω)
      ((hΦ_int _ _ ω).const_mul _), integral_finsetSum _ fun r' _ => hΦ_int _ _ ω,
      integral_const_mul]
  simp_rw [hp_in1, hp_in2]
  have hΦ_sum : Integrable (fun τ => ∑ ℓ : R,
      ((∑ j ∈ Finset.univ.erase ℓ, Φ (some (some ℓ)) (some (some j)) ω τ) -
        (Fintype.card R : ℝ) * Φ (some (some ℓ)) (some none) ω τ))
      (Measure.pi fun _ => μ ω) :=
    integrable_finsetSum _ fun ℓ _ =>
      (integrable_finsetSum _ fun j _ => hΦ_int _ _ ω).sub ((hΦ_int _ _ ω).const_mul _)
  have hΦ_opt2 : Integrable (fun τ =>
      (∑ r' : R, Φ (some (some r')) (some none) ω τ) -
        (Fintype.card (Option R) : ℝ) * Φ (some none) none ω τ)
      (Measure.pi fun _ => μ ω) :=
    (integrable_finsetSum _ fun r' _ => hΦ_int _ _ ω).sub ((hΦ_int _ _ ω).const_mul _)
  rw [← integral_finsetSum Finset.univ (f := fun (ℓ : R) τ =>
    (∑ j ∈ Finset.univ.erase ℓ, Φ (some (some ℓ)) (some (some j)) ω τ) -
      (Fintype.card R : ℝ) * Φ (some (some ℓ)) (some none) ω τ) fun ℓ _ =>
    (integrable_finsetSum _ fun j _ => hΦ_int _ _ ω).sub ((hΦ_int _ _ ω).const_mul _)]
  rw [← integral_const_mul (Fintype.card R : ℝ),
    ← integral_sub hΦ_sum (hΦ_opt2.const_mul _),
    ← integral_const_mul (1 / 2), replicaPairAverage_eq]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  dsimp only [Φ]
  have hoff_sum :
      ∑ ℓ : R, ∑ j ∈ Finset.univ.erase ℓ, U ω (τ (some (some ℓ))) (τ (some (some j))) =
      2 * ∑ p : R × R with p.1 < p.2, U ω (τ (some (some p.1))) (τ (some (some p.2))) := by
    have h1_eq :
        (∑ ℓ : R, ∑ j ∈ Finset.univ.erase ℓ, U ω (τ (some (some ℓ))) (τ (some (some j)))) =
        ∑ ℓ : R, ∑ j : R, if ℓ = j then 0 else U ω (τ (some (some ℓ))) (τ (some (some j))) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [← Finset.add_sum_erase Finset.univ
        (fun j => if ℓ = j then 0 else U ω (τ (some (some ℓ))) (τ (some (some j))))
        (Finset.mem_univ ℓ)]
      simp only [↓reduceIte, zero_add]
      exact Finset.sum_congr rfl fun j hj => by simp [(Finset.ne_of_mem_erase hj).symm]
    rw [h1_eq]
    exact sum_sum_offDiag_eq_two_sum_lt
      (fun r₁ r₂ => U ω (τ (some (some r₁))) (τ (some (some r₂)))) (fun _ _ => hU_symm ω _ _)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Fintype.card_option,
    Nat.cast_succ, replicaPairCombination_eq, hoff_sum]
  ring

end TimeDerivative

end SpinGlasses
