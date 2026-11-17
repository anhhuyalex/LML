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
and the Gaussian integration-by-parts cancellation are further steps.
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
  obtain ⟨δ, hδ, hδmin⟩ := exists_between (lt_min ht.1 (sub_pos.mpr ht.2))
  have hδt : δ < t := hδmin.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 - t := hδmin.trans_le (min_le_right _ _)
  let V := Set.Ioo δ (1 - δ)
  have htV : t ∈ V := ⟨hδt, by linarith⟩
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  let K := 1 / (2 * Real.sqrt δ) +
    (M : ℝ) * (D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (2 / Real.sqrt δ))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let A := fun ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ =>
    (Fintype.card R : ℝ) * ((M : ℝ) * B + |ω.2|)
  let Q := fun ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ =>
    K * Real.exp (|ω.2| + ∑ k, |ω.1.2 k|)
  let b := fun σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
    ∑ i, Real.exp (∑ k, |(σ i).2 k|)
  let J := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
    (σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => ∑ i, E s ω (σ i)
  let J' := fun (s : ℝ) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
    (σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => ∑ i, E' s ω (σ i)
  let μR := Measure.pi fun _ : R => μ
  have : NeZero μR := neZero_measure_pi μ
  have hcast : Measurable (fun ε : ℤˣ => ((ε : ℤ) : ℝ)) := measurable_of_countable _
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
  have hmap (i : R) : Measurable (fun p :
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) × (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      (p.1, p.2 i)) := by fun_prop
  have hmJ (s : ℝ) : Measurable fun p :
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) ×
        (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => J s p.1 p.2 := by
    dsimp only [J]
    apply Finset.measurable_sum
    intro i _
    simpa only [Function.comp_def] using (hmE s).comp (hmap i)
  have hmJ' (s : ℝ) : Measurable fun p :
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) ×
        (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => J' s p.1 p.2 := by
    dsimp only [J']
    apply Finset.measurable_sum
    intro i _
    simpa only [Function.comp_def] using (hmE' s).comp (hmap i)
  have hEb (s : ℝ) (hs : s ∈ V) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) : |E s ω x| ≤ M * B + |ω.2| := by
    have hsq : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [hs.1])
    exact (abs_perceptron_smart_path_energy_le hB ω.1.1 ω.1.2 ω.2 s x).trans
      (add_le_add le_rfl (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hsq (abs_nonneg ω.2)))
  have hJb (s : ℝ) (hs : s ∈ V) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) : |J s ω σ| ≤ A ω := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hEb s hs ω (σ i)))
  have hcalc (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (s : ℝ) (hs : s ∈ V) :
      HasDerivAt (fun q => E q ω x) (E' s ω x) s :=
    hasDerivAt_perceptron_smart_path_energy ⟨hδ.trans hs.1, by linarith [hs.2]⟩ hu
      ω.1.1 ω.1.2 x.2 x.1.1 x.1.2 ω.2
  have hdb (s : ℝ) (hs : s ∈ V) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E' s ω x| ≤ Q ω * Real.exp (∑ k, |x.2 k|) := by
    let T := |ω.2| + (∑ k, |ω.1.2 k|) + ∑ k, |x.2 k|
    have htotal : T ≤ Real.exp T :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp T)
    have hA0 : 0 ≤ ∑ k, |ω.1.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hX0 : 0 ≤ ∑ k, |x.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hyT : |ω.2| ≤ T := by dsimp only [T]; linarith
    have hy : |ω.2| ≤ Real.exp T := hyT.trans htotal
    have ha (k : Fin M) : |ω.1.2 k| ≤ Real.exp T := by
      have hk : |ω.1.2 k| ≤ ∑ k, |ω.1.2 k| :=
        Finset.single_le_sum (fun k _ => abs_nonneg (ω.1.2 k)) (Finset.mem_univ k)
      have hAT : (∑ k, |ω.1.2 k|) ≤ T := by dsimp only [T]; linarith [abs_nonneg ω.2]
      exact hk.trans (hAT.trans htotal)
    have hx (k : Fin M) : |x.2 k| ≤ Real.exp T := by
      have hk : |x.2 k| ≤ ∑ k, |x.2 k| :=
        Finset.single_le_sum (fun k _ => abs_nonneg (x.2 k)) (Finset.mem_univ k)
      have hXT : (∑ k, |x.2 k|) ≤ T := by dsimp only [T]; linarith [abs_nonneg ω.2]
      exact hk.trans (hXT.trans htotal)
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
        dsimp only [Q]
        ring
  have hJdb (s : ℝ) (hs : s ∈ V) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (σ : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) : |J' s ω σ| ≤ Q ω * b σ := by
    calc _ ≤ ∑ i, |E' s ω (σ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, Q ω * Real.exp (∑ k, |(σ i).2 k|) :=
        Finset.sum_le_sum fun i _ => hdb s hs ω (σ i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hξ : Integrable (fun ξ : Fin M → ℝ => Real.exp (∑ k, |ξ k|))
      (Measure.pi fun _ : Fin M => gaussianReal 0 1) := by
    simpa only [one_mul] using integrable_exp_sum_mul_abs_pi (fun _ : Fin M => (1 : ℝ))
  have hbase : Integrable (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
      Real.exp (∑ k, |x.2 k|)) μ :=
    hξ.comp_snd (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ))
  have hb : Integrable b μR := by
    dsimp only [b, μR]
    apply integrable_finsetSum
    intro i _
    exact integrable_comp_eval (μ := fun _ : R => μ) (i := i) hbase
  have houter : Integrable (fun ω => Real.exp (2 * A ω) * Q ω) P := by
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
  have hres := hasDerivAt_integral_integral_tilted_of_dominated (P := P) (μ := μR)
    (E := J) (E' := J') (A := A) (B := Q) (b := b) (F := F)
    (s := V) isOpen_Ioo htV (fun s _ => hmJ s) (fun s _ => hmJ' s)
    hJb (fun ω => mul_nonneg hK (Real.exp_pos _).le)
    (fun σ => Finset.sum_nonneg fun i _ => (Real.exp_pos _).le) hb hJdb houter
    (fun ω σ s hs => HasDerivAt.fun_sum fun i _ => hcalc ω (σ i) s hs) hF hFb
  have heq (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) :
      (∫ σ, F σ * J' t ω σ ∂μR.tilted (J t ω)) -
        (∫ σ, F σ ∂μR.tilted (J t ω)) *
          (∫ σ, J' t ω σ ∂μR.tilted (J t ω)) =
      (∑ i, ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * E' t ω (σ (some i))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω))) -
        (Fintype.card R : ℝ) * ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * E' t ω (σ none)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t ω)) := by
    have hmSlice (s : ℝ) : Measurable (J s ω) := by
      simpa only [Function.comp_def, id_eq] using
        (hmJ s).comp ((measurable_const (a := ω)).prodMk measurable_id)
    have hmSlice' : Measurable (J' t ω) := by
      simpa only [Function.comp_def, id_eq] using
        (hmJ' t).comp ((measurable_const (a := ω)).prodMk measurable_id)
    have hd1 := hasDerivAt_integral_tilted_of_bounded (μ := μR) (E := fun s => J s ω)
      (E' := fun s => J' s ω) (A := A ω)
      (b := fun σ => Q ω * b σ) (F := F) (s := V) (isOpen_Ioo.mem_nhds htV)
      (fun s _ => hmSlice s) hmSlice'
      (fun s hs σ => le_of_abs_le (hJb s hs ω σ)) (hb.const_mul (Q ω))
      (fun σ => mul_nonneg (mul_nonneg hK (Real.exp_pos _).le)
        (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le))
      (fun s hs σ => hJdb s hs ω σ)
      (fun σ s hs => HasDerivAt.fun_sum fun i _ => hcalc ω (σ i) s hs) hF hFb
    have hd2 := hasDerivAt_integral_pi_perceptron_smart_path ht hu
      (fun z => le_of_abs_le (hB z)) hD ω.1.1 ω.1.2 ω.2 F hF hFb
    simp only [J, μR, ← pi_tilted_eq_tilted_pi] at hd1 ⊢
    exact hd1.unique hd2
  simp only [J, μR, ← pi_tilted_eq_tilted_pi] at hres
  convert hres using 1
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    simpa only [J, μR, ← pi_tilted_eq_tilted_pi] using (heq ω).symm

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
  rw [← Finset.sum_add_distrib]
  have h (k : Fin M) : deriv u (S k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t - x.2 k / Real.sqrt (1 - t))) =
      deriv u (S k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t)) +
      deriv u (S k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (- x.2 k / Real.sqrt (1 - t))) := by
    ring
  simp_rw [h]
  ring

theorem perceptron_smart_path_diff_eq_three_terms {N M : ℕ} {u : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
    {R : Type*} [Fintype R] (F : (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) → ℝ)
    (hF : Measurable F) (hFb : ∃ C, ∀ σ, |F σ| ≤ C) :
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
  obtain ⟨C, hC⟩ := hFb
  have hν : IsProbabilityMeasure (μ.tilted (E t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.continuous.measurable
      (fun x => le_of_abs_le (hB x)) ω.1.1 ω.1.2 ω.2 t
  have hμR : IsProbabilityMeasure (Measure.pi fun _ : Option R => μ.tilted (E t ω)) :=
    inferInstance
  have hmE' : Measurable (E' t ω) := by
    have hdu := measurable_deriv u
    dsimp only [E', S]
    fun_prop
  have hmE'_a : Measurable (E'_a t ω) := by
    have hdu := measurable_deriv u
    dsimp only [E'_a, S]
    fun_prop
  have hmE'_ξ : Measurable (E'_ξ t ω) := by
    have hdu := measurable_deriv u
    dsimp only [E'_ξ, S]
    fun_prop
  have hmE'_Y : Measurable (E'_Y t ω) := by
    dsimp only [E'_Y]
    fun_prop
  have hmF_opt : Measurable (fun σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
      F (fun j => σ (some j))) :=
    hF.comp (measurable_pi_iff.2 fun j => measurable_pi_apply (some j))
  -- Boundedness of E'_Y
  have hbY (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E'_Y t ω x| ≤ |ω.2| / (2 * Real.sqrt (1 - t)) := by
    dsimp only [E'_Y]
    have hpos : 0 ≤ 2 * Real.sqrt (1 - t) := by positivity
    rw [abs_div, abs_of_nonneg hpos]
    have h1 : |(-((x.1.2 : ℤ) : ℝ) * ω.2)| = |ω.2| := by
      rw [neg_mul, abs_neg, abs_mul, abs_units_cast_eq_one, one_mul]
    rw [h1]
  -- Boundedness of E'_a
  have hb_a (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E'_a t ω x| ≤ ∑ k, D * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (|ω.1.2 k| / Real.sqrt t)) := by
    dsimp only [E'_a]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 : 0 ≤ 1 / (2 * Real.sqrt (N + 1 : ℕ)) := by positivity
    have h2 : 0 ≤ Real.sqrt t := by positivity
    calc |deriv u (S t ω x k) *
          ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t))|
      _ = |deriv u (S t ω x k)| *
          |(1 / (2 * Real.sqrt (N + 1 : ℕ))) * (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t)| :=
        abs_mul _ _
      _ = |deriv u (S t ω x k)| *
          ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * |ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt t|) := by
        rw [abs_mul, abs_of_nonneg h1]
      _ = |deriv u (S t ω x k)| *
          ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k * ((x.1.2 : ℤ) : ℝ)| / Real.sqrt t)) := by
        rw [abs_div, abs_of_nonneg h2]
      _ = |deriv u (S t ω x k)| *
          ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt t)) := by
        rw [abs_mul, abs_units_cast_eq_one, mul_one]
      _ ≤ D * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt t)) := by
        have hDpos : 0 ≤ D := (abs_nonneg _).trans (hD 0)
        exact mul_le_mul (hD _) le_rfl (by positivity) hDpos
  have hIY (j : Option R) : Integrable (fun σ => F (fun i => σ (some i)) * E'_Y t ω (σ j))
      (Measure.pi fun _ : Option R => μ.tilted (E t ω)) := by
    refine integrable_of_measurable_bound (hmF_opt.mul (hmE'_Y.comp (measurable_pi_apply j)))
      (M := |C| * (|ω.2| / (2 * Real.sqrt (1 - t)))) (fun σ => ?_)
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self _)) (hbY _) (abs_nonneg _) (abs_nonneg _)
  have hIa (j : Option R) : Integrable (fun σ => F (fun i => σ (some i)) * E'_a t ω (σ j))
      (Measure.pi fun _ : Option R => μ.tilted (E t ω)) := by
    refine integrable_of_measurable_bound (hmF_opt.mul (hmE'_a.comp (measurable_pi_apply j)))
      (M := |C| * (∑ k, D * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt t))))
      (fun σ => ?_)
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self _)) (hb_a _) (abs_nonneg _) (abs_nonneg _)
  obtain ⟨δ, hδ, hδmin⟩ := exists_between (lt_min ht.1 (sub_pos.mpr ht.2))
  have hδt : δ < t := hδmin.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 - t := hδmin.trans_le (min_le_right _ _)
  let s := Set.Ioo δ (1 - δ)
  have hs : s ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hδt, by linarith⟩
  have hts : t ∈ s := mem_of_mem_nhds hs
  have hmE (r : ℝ) : Measurable (E r ω) :=
    measurable_perceptron_smart_path_energy_slice hu.continuous.measurable ω.1.1 ω.1.2 ω.2 r
  have hEb (r : ℝ) (hr : r ∈ s) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      E r ω x ≤ M * B + |ω.2| :=
    perceptron_smart_path_energy_le_of_nonneg (fun x => le_of_abs_le (hB x))
      ω.1.1 ω.1.2 ω.2 r (hδ.trans hr.1).le x
  let b := fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
    |ω.2| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
      ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ)
  have hG : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := by
    have h : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 1) := memLp_id_gaussianReal 1
    exact h.integrable le_rfl
  have hξ (k : Fin M) : Integrable
      (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) => |x.2 k|) μ :=
    (integrable_comp_eval hG.abs).comp_snd (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ))
  have hterms (k : Fin M) : Integrable
      (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
        D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ)) μ := by
    simpa only [Pi.add_apply] using
      (((integrable_const |ω.1.2 k|).add (hξ k)).div_const (Real.sqrt δ)).const_mul
        (D * (1 / (2 * Real.sqrt (N + 1 : ℕ))))
  have hib : Integrable b μ := by
    have hraw := (integrable_const (|ω.2| / (2 * Real.sqrt δ))).add
      (integrable_finsetSum Finset.univ fun k _ => hterms k)
    exact hraw.congr (ae_of_all _ fun x => rfl)
  have hdb (r : ℝ) (hr : r ∈ s) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E' r ω x| ≤ b x :=
    abs_deriv_perceptron_smart_path_energy_le hδ ⟨hr.1.le, hr.2.le⟩ hD
      ω.1.1 ω.1.2 x.2 x.1.1 x.1.2 ω.2
  have hiE' : Integrable (E' t ω) μ := hib.mono' hmE'.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hdb t hts x)
  have hiTilted : Integrable (E' t ω) (μ.tilted (E t ω)) :=
    integrable_tilted_of_ae_le (hmE t).aemeasurable (ae_of_all _ (hEb t hts)) hiE'
  have hIE' (j : Option R) : Integrable (fun σ => F (fun i => σ (some i)) * E' t ω (σ j))
      (Measure.pi fun _ : Option R => μ.tilted (E t ω)) := by
    have hE'proj : Integrable (fun σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
        E' t ω (σ j)) (Measure.pi fun _ : Option R => μ.tilted (E t ω)) :=
      integrable_comp_eval hiTilted
    exact hE'proj.bdd_mul hmF_opt.aestronglyMeasurable
      (ae_of_all _ fun σ => by simpa using (hC _).trans (le_abs_self _))
  have hIξ (j : Option R) : Integrable (fun σ => F (fun i => σ (some i)) * E'_ξ t ω (σ j))
      (Measure.pi fun _ : Option R => μ.tilted (E t ω)) := by
    have heq : (fun σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
        F (fun i => σ (some i)) * E'_ξ t ω (σ j)) =
        (fun σ => F (fun i => σ (some i)) * E' t ω (σ j)) -
        (fun σ => F (fun i => σ (some i)) * E'_a t ω (σ j)) -
        (fun σ => F (fun i => σ (some i)) * E'_Y t ω (σ j)) := by
      ext σ
      simp only [Pi.sub_apply]
      have h3 := perceptron_smart_path_E'_eq_three_terms (N := N) (M := M) (u := u) (t := t) ω (σ j)
      dsimp only [E', E'_a, E'_ξ, E'_Y, S] at h3 ⊢
      rw [h3]
      ring
    rw [heq]
    exact ((hIE' j).sub (hIa j)).sub (hIY j)
  have hI_aξ (j : Option R) : Integrable (fun σ => F (fun i => σ (some i)) *
      (E'_a t ω (σ j) + E'_ξ t ω (σ j))) (Measure.pi fun _ : Option R => μ.tilted (E t ω)) := by
    have heq : (fun σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
        F (fun i => σ (some i)) * (E'_a t ω (σ j) + E'_ξ t ω (σ j))) =
        (fun σ => F (fun i => σ (some i)) * E'_a t ω (σ j)) +
        (fun σ => F (fun i => σ (some i)) * E'_ξ t ω (σ j)) := by
      ext σ
      simp only [Pi.add_apply]
      ring
    rw [heq]
    exact (hIa j).add (hIξ j)
  have hstep1 := integral_pi_replica_diff_add (μ.tilted (E t ω)) F (E'_a t ω) (E'_ξ t ω) hIa hIξ
  have hstep2 := integral_pi_replica_diff_add (μ.tilted (E t ω)) F
    (fun x => E'_a t ω x + E'_ξ t ω x) (E'_Y t ω) hI_aξ hIY
  dsimp only [diff] at hstep1 hstep2 ⊢
  have heq : (fun x => E'_a t ω x + E'_ξ t ω x + E'_Y t ω x) = E' t ω := by
    ext x
    have h3 := perceptron_smart_path_E'_eq_three_terms (N := N) (M := M) (u := u) (t := t) ω x
    dsimp only [E', E'_a, E'_ξ, E'_Y, S] at h3 ⊢
    rw [h3]
  rw [← heq, hstep2, hstep1]

/-- **Equation (2.28): derivative of the quenched replica average as three terms.** -/
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
  have h3 := perceptron_smart_path_diff_eq_three_terms ht hu hB hD ω F hF ⟨C, hFb⟩
  dsimp only [diff] at h3 ⊢
  exact h3

end SpinGlasses
