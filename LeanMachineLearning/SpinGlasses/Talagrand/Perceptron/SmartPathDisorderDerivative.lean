/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathGibbsDerivative
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExpectedTilted
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# The quenched-disorder derivative of the perceptron smart path

This file justifies averaging the fixed-disorder derivative in Talagrand (2.26)--(2.27).
The two-sided bound on the potential controls the normalized density. Gaussian absolute
exponential moments give a common integrable disorder envelope on an interior interval.

The old disorder can have any finite law: the bound does not depend on its coordinates.
The last field has any nonnegative Gaussian variance, including zero. Replicas have
independent auxiliary coordinates and shared disorder. The three-term expansion (2.28)
is formalized as `hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace SpinGlasses

/-- **Disorder-averaged Talagrand (2.26), with (2.27) substituted.** A differentiable potential
with bounded value and first derivative suffices to pass the derivative through the auxiliary,
replica and disorder integrals. The observable is bounded, measurable and independent of `t`.
The full number of spins is `N + 1`; empty replica/constraint types and zero variance are allowed.
No Gaussian integration-by-parts identity is assumed or asserted. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path {N M : ℕ}
    {R : Type*} [Fintype R] {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D : ℝ} (hB : ∀ z, |u z| ≤ B) (hD : ∀ z, |deriv u z| ≤ D)
    (v : NNReal) {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    let S := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let E' := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s)) +
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s - x.2 k / Real.sqrt (1 - s)))
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let P := (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)
    HasDerivAt (fun s => ∫ ω, ∫ σ, F σ ∂(Measure.pi fun _ : R => μ.tilted (E s ω)) ∂P)
      (∫ ω, (∑ i, ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * E' t ω (σ (some i))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω))) -
        (Fintype.card R : ℝ) * ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * E' t ω (σ none)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω)) ∂P) t := by
  intro S E E' μ P
  obtain ⟨δ, hδ, hδt, hδ1⟩ := exists_pos_lt_of_mem_Ioo ht
  let V := Set.Ioo δ (1 - δ)
  have htV : t ∈ V := ⟨hδt, by linarith⟩
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  let K := 1 / (2 * Real.sqrt δ) +
    (M : ℝ) * (D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (2 / Real.sqrt δ))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let A := fun ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ =>
    (M : ℝ) * B + |ω.2|
  let Q := fun ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ =>
    K * Real.exp (|ω.2| + ∑ k, |ω.1.2 k|)
  let b := fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
    Real.exp (∑ k, |x.2 k|)
  have hmE (s : ℝ) : Measurable fun p :
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) ×
        (((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => E s p.1 p.2 :=
    measurable_perceptron_smart_path_energy (N := N) (M := M) hu.continuous.measurable s
  have hmE' (s : ℝ) : Measurable fun p :
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) ×
        (((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => E' s p.1 p.2 := by
    have hdu := measurable_deriv u
    dsimp only [E', S]
    fun_prop
  have hEb (s : ℝ) (hs : s ∈ V) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) : |E s ω x| ≤ A ω :=
    abs_perceptron_smart_path_energy_le_of_nonneg hB ω.1.1 ω.1.2 ω.2 s (hδ.trans hs.1).le x
  have hcalc (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (s : ℝ) (hs : s ∈ V) :
      HasDerivAt (fun q => E q ω x) (E' s ω x) s :=
    hasDerivAt_perceptron_smart_path_energy ⟨hδ.trans hs.1, by linarith [hs.2]⟩ hu
      ω.1.1 ω.1.2 x.2 x.1.1 x.1.2 ω.2
  have hdb (s : ℝ) (hs : s ∈ V) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E' s ω x| ≤ Q ω * b x := by
    let T := |ω.2| + (∑ k, |ω.1.2 k|) + ∑ k, |x.2 k|
    have htotal : T ≤ Real.exp T :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp T)
    have hA0 : 0 ≤ ∑ k, |ω.1.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hX0 : 0 ≤ ∑ k, |x.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hyT : |ω.2| ≤ T := by dsimp only [T]; linarith
    have hy : |ω.2| ≤ Real.exp T := hyT.trans htotal
    have ha (k : Fin M) : |ω.1.2 k| ≤ Real.exp T :=
      (abs_apply_le_exp_sum_abs ω.1.2 k).trans
        (Real.exp_le_exp.mpr (by dsimp only [T]; linarith [hX0, abs_nonneg ω.2]))
    have hx (k : Fin M) : |x.2 k| ≤ Real.exp T :=
      (abs_apply_le_exp_sum_abs x.2 k).trans
        (Real.exp_le_exp.mpr (by dsimp only [T]; linarith [hA0, abs_nonneg ω.2]))
    have hcoef : 0 ≤ D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) := by positivity
    have hlin := abs_deriv_perceptron_smart_path_energy_le hδ ⟨hs.1.le, hs.2.le⟩ hD
      ω.1.1 ω.1.2 x.2 x.1.1 x.1.2 ω.2
    calc _ ≤ |ω.2| / (2 * Real.sqrt δ) + ∑ k,
          D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ) := hlin
      _ ≤ Real.exp T / (2 * Real.sqrt δ) + ∑ _k : Fin M,
          D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            ((Real.exp T + Real.exp T) / Real.sqrt δ) :=
        add_le_add (div_le_div_of_nonneg_right hy (by positivity))
          (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (add_le_add (ha k) (hx k)) (by positivity)) hcoef)
      _ = K * Real.exp T := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp only [K]
        ring
      _ = _ := by
        rw [show T = (|ω.2| + ∑ k, |ω.1.2 k|) + ∑ k, |x.2 k| from rfl, Real.exp_add]
        dsimp only [Q, b]
        ring
  have hξ : Integrable (fun ξ : Fin M → ℝ => Real.exp (∑ k, |ξ k|))
      (Measure.pi fun _ : Fin M => gaussianReal 0 1) := by
    simpa only [one_mul] using integrable_exp_sum_mul_abs_pi (fun _ : Fin M => (1 : ℝ))
  have hb : Integrable b μ :=
    hξ.comp_snd (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ))
  have houter : Integrable (fun ω => Real.exp (2 * ((Fintype.card R : ℝ) * A ω)) * Q ω) P := by
    have hyexp : Integrable (fun y : ℝ =>
        Real.exp ((2 * (Fintype.card R : ℝ) + 1) * |y|)) (gaussianReal 0 v) :=
      integrable_exp_mul_abs_gaussianReal _
    have hi := ((hξ.comp_snd Pold).mul_prod hyexp).const_mul
      (K * Real.exp (2 * (Fintype.card R : ℝ) * M * B))
    apply hi.congr (ae_of_all _ fun ω => ?_)
    dsimp only [A, Q]
    rw [show 2 * ((Fintype.card R : ℝ) * ((M : ℝ) * B + |ω.2|)) =
      2 * (Fintype.card R : ℝ) * M * B + 2 * (Fintype.card R : ℝ) * |ω.2| by ring,
      show (2 * (Fintype.card R : ℝ) + 1) * |ω.2| =
        2 * (Fintype.card R : ℝ) * |ω.2| + |ω.2| by ring]
    simp only [Real.exp_add]
    ring
  exact hasDerivAt_integral_integral_pi_tilted_of_dominated (P := P) (μ := μ)
    (E := E) (E' := E') (A := A) (B := Q) (b := b) (s := V)
    isOpen_Ioo htV (fun s _ => hmE s) (fun s _ => hmE' s)
    hEb hb hdb houter (fun ω x s hs => hcalc ω x s hs) hF hFb

/-- The parameter derivative of the perceptron smart path energy splits algebraically into
three terms: the quenched disorder term in `a`, the auxiliary spin term in `ξ`, and the
quenched last-field term in `Y`. -/
theorem perceptron_smart_path_E'_eq_three_terms {N M : ℕ} {u : ℝ → ℝ} {t : ℝ}
    (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
    (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
    let S := fun (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - t) / (N + 1)) * x.2 k
    let E' := -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - t)) +
      ∑ k, deriv u (S k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t - x.2 k / Real.sqrt (1 - t)))
    let E'_a := ∑ k, deriv u (S k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
      (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t))
    let E'_ξ := ∑ k, deriv u (S k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
      (- x.2 k / Real.sqrt (1 - t)))
    let E'_Y := -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - t))
    E' = E'_a + E'_ξ + E'_Y := by
  intro S E' E'_a E'_ξ E'_Y
  dsimp only [E', E'_a, E'_ξ, E'_Y]
  rw [← Finset.sum_add_distrib, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Splitting of the replica difference operator for the perceptron smart path energy into
three terms: the quenched disorder term, the auxiliary spin term, and the last-field term. -/
theorem perceptron_smart_path_diff_eq_three_terms {N M : ℕ} {u : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
    {R : Type*} [Fintype R] (F : (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    let S := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let E' := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s)) +
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s - x.2 k / Real.sqrt (1 - s)))
    let E'_a := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s))
    let E'_ξ := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (- x.2 k / Real.sqrt (1 - s)))
    let E'_Y := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s))
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let diff := fun (H : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ) =>
      (∑ i, ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * H (σ (some i))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω))) -
        (Fintype.card R : ℝ) * ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * H (σ none)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω))
    diff (E' t ω) = diff (E'_a t ω) + diff (E'_ξ t ω) + diff (E'_Y t ω) := by
  intro S E E' E'_a E'_ξ E'_Y μ diff
  have hC := hFb
  have hν : IsProbabilityMeasure (μ.tilted (E t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.continuous.measurable
      (fun x => le_of_abs_le (hB x)) ω.1.1 ω.1.2 ω.2 t
  have hmE'_Y : Measurable (E'_Y t ω) := by dsimp only [E'_Y]; fun_prop
  have hbY (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E'_Y t ω x| ≤ |ω.2| / (2 * Real.sqrt (1 - t)) := by
    dsimp only [E'_Y]
    have hpos : 0 ≤ 2 * Real.sqrt (1 - t) := by positivity
    rw [abs_div, abs_of_nonneg hpos, neg_mul, abs_neg, abs_mul, abs_units_cast_eq_one, one_mul]
  have hIY : Integrable (E'_Y t ω) (μ.tilted (E t ω)) :=
    integrable_of_measurable_bound hmE'_Y (M := |ω.2| / (2 * Real.sqrt (1 - t))) hbY
  have hmE'_a : Measurable (E'_a t ω) := by
    have hdu := measurable_deriv u
    dsimp only [E'_a, S]
    fun_prop
  have hb_a (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E'_a t ω x| ≤ ∑ k, D * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt t)) := by
    dsimp only [E'_a]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have h1 : 0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ)) := by positivity
    have h2 : 0 ≤ Real.sqrt t := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_div, abs_of_nonneg h2,
      abs_mul, abs_units_cast_eq_one, mul_one]
    exact mul_le_mul (hD _) le_rfl (by positivity) ((abs_nonneg _).trans (hD 0))
  have hIa : Integrable (E'_a t ω) (μ.tilted (E t ω)) :=
    integrable_of_measurable_bound hmE'_a
      (M := ∑ k, D * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt t))) hb_a
  have hIE' : Integrable (E' t ω) (μ.tilted (E t ω)) :=
    integrable_tilted_perceptron_smart_path_energy_deriv hu
      (fun x => le_of_abs_le (hB x)) hD ω.1.1 ω.1.2 ω.2 t ht
  have hI_aξ : Integrable (fun x => E'_a t ω x + E'_ξ t ω x) (μ.tilted (E t ω)) := by
    have heq : (fun x => E'_a t ω x + E'_ξ t ω x) = E' t ω - E'_Y t ω := by
      ext x
      simp only [Pi.sub_apply]
      have h3 := perceptron_smart_path_E'_eq_three_terms (N := N) (M := M) (u := u) (t := t) ω x
      dsimp only [E', E'_a, E'_ξ, E'_Y, S] at h3 ⊢
      linarith
    rw [heq]
    exact hIE'.sub hIY
  have hIξ : Integrable (E'_ξ t ω) (μ.tilted (E t ω)) := by
    have heq : E'_ξ t ω = (fun x => E'_a t ω x + E'_ξ t ω x) - E'_a t ω := by
      ext x
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact hI_aξ.sub hIa
  have hstep1 := replicaDiff_add (μ.tilted (E t ω)) F hF.aestronglyMeasurable hC hIa hIξ
  have hstep2 := replicaDiff_add (μ.tilted (E t ω)) F hF.aestronglyMeasurable hC hI_aξ hIY
  have heq : (fun x => E'_a t ω x + E'_ξ t ω x + E'_Y t ω x) = E' t ω := by
    ext x
    have h3 := perceptron_smart_path_E'_eq_three_terms (N := N) (M := M) (u := u) (t := t) ω x
    dsimp only [E', E'_a, E'_ξ, E'_Y, S] at h3 ⊢
    rw [h3]
  change replicaDiff (μ.tilted (E t ω)) F (E' t ω) =
    replicaDiff (μ.tilted (E t ω)) F (E'_a t ω) +
    replicaDiff (μ.tilted (E t ω)) F (E'_ξ t ω) +
    replicaDiff (μ.tilted (E t ω)) F (E'_Y t ω)
  rw [← heq, hstep2, hstep1]

/-- **(2.26)--(2.27) with the three groups of (2.28), before constraint symmetry.**
Differentiates the quenched replica average and splits the energy derivative into the
quenched-disorder term `E'_a`, the auxiliary-spin term `E'_ξ`, and the last-field term `E'_Y`.
This is the three-group split before the permutation symmetry in `k` that reduces the `k`-sum
to `α√N` times the last constraint. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms {N M : ℕ}
    {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D) (v : NNReal)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    let S := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let E'_a := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s))
    let E'_ξ := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (- x.2 k / Real.sqrt (1 - s)))
    let E'_Y := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s))
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let J := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) =>
      ∫ σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ), F σ ∂(Measure.pi fun _ : R => μ.tilted (E s ω))
    let P := (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)
    let diff := fun (H : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
        (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) =>
      (∑ i, ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * H (σ (some i))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω))) -
        (Fintype.card R : ℝ) * ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * H (σ none)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω))
    HasDerivAt (fun s => ∫ ω, J s ω ∂P)
      (∫ ω, diff (E'_a t ω) ω + diff (E'_ξ t ω) ω + diff (E'_Y t ω) ω ∂P) t := by
  intro S E E'_a E'_ξ E'_Y μ J P diff
  have h := hasDerivAt_integral_integral_pi_perceptron_smart_path (Pold := Pold)
    ht hu hB hD v F hF hFb
  dsimp only [S, E, μ, P, diff] at h ⊢
  refine h.congr_deriv ?_
  refine integral_congr_ae (ae_of_all P fun ω => ?_)
  have h3 := perceptron_smart_path_diff_eq_three_terms ht hu hB hD ω F hF hFb
  dsimp only [diff] at h3 ⊢
  exact h3

/-- A spin-only replica observable is automatically measurable on the configuration space. -/
theorem measurable_spin_only {N M : ℕ} {R : Type*} [Finite R]
    (f : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ) :
    Measurable (fun x : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) => f (fun r => (x r).1)) := by
  have hm : Measurable (fun x : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
      fun r => (x r).1) := by
    refine measurable_pi_iff.mpr fun r => ?_
    exact measurable_fst.comp (measurable_pi_apply r)
  have hf : Measurable f := measurable_of_countable f
  exact hf.comp hm

/-- A spin-only replica observable is automatically bounded. -/
theorem exists_abs_le_spin_only {N M : ℕ} {R : Type*} [Finite R]
    (f : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ) :
    ∃ C : ℝ, ∀ x : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
      |f (fun r => (x r).1)| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  exact ⟨C, fun x => hC (fun r => (x r).1)⟩

/-- **Spin-only derivative of the quenched replica average.** A spin-only observable
requires no separate measurability or boundedness hypothesis. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_spin_only {N M : ℕ}
    {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ z, |u z| ≤ B)
    (hD : ∀ z, |deriv u z| ≤ D) (v : NNReal)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ) :
    let S := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let E' := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s)) +
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s - x.2 k / Real.sqrt (1 - s)))
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let P := (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)
    HasDerivAt (fun s => ∫ ω, ∫ σ, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => μ.tilted (E s ω)) ∂P)
      (∫ ω, replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) (E' t ω) ∂P) t := by
  intro S E E' μ P
  obtain ⟨C, hC⟩ := exists_abs_le_spin_only (N := N) (M := M) f
  have hm := measurable_spin_only (N := N) (M := M) f
  exact hasDerivAt_integral_integral_pi_perceptron_smart_path ht hu hB hD v
    (fun σ => f (fun r => (σ r).1)) hm hC

/-- **Spin-only three-term expansion of the quenched replica derivative.** -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms_spin_only {N M : ℕ}
    {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D) (v : NNReal)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ) :
    let S := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (S s ω x k)
    let E'_a := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s))
    let E'_ξ := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ∑ k, deriv u (S s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (- x.2 k / Real.sqrt (1 - s)))
    let E'_Y := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s))
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let J := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) =>
      ∫ σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ), f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => μ.tilted (E s ω))
    let P := (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)
    let diff := fun (H : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) → ℝ)
        (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) =>
      replicaDiff (μ.tilted (E t ω)) (fun σ => f (fun r => (σ r).1)) H
    HasDerivAt (fun s => ∫ ω, J s ω ∂P)
      (∫ ω, diff (E'_a t ω) ω + diff (E'_ξ t ω) ω + diff (E'_Y t ω) ω ∂P) t := by
  intro S E E'_a E'_ξ E'_Y μ J P diff
  obtain ⟨C, hC⟩ := exists_abs_le_spin_only (N := N) (M := M) f
  have hm := measurable_spin_only (N := N) (M := M) f
  have h := hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms
    (Pold := Pold) ht hu hB hD v (fun σ => f (fun r => (σ r).1)) hm hC
  dsimp only [S, E, E'_a, E'_ξ, E'_Y, μ, J, P] at h ⊢
  exact h

end SpinGlasses
