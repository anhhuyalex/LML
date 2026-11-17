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
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path {N M : ℕ} {R : Type*} [Fintype R] {t : ℝ}
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
  have hmE (s : ℝ) : Measurable fun p : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) × (((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => E s p.1 p.2 :=
    measurable_perceptron_smart_path_energy (N := N) (M := M) hu.continuous.measurable s
  have hmE' (s : ℝ) : Measurable fun p : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) × (((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => E' s p.1 p.2 := by
    have hdu := measurable_deriv u
    dsimp only [E', S]
    fun_prop
  have hmap (i : R) : Measurable (fun p : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) × (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      (p.1, p.2 i)) := by fun_prop
  have hmJ (s : ℝ) : Measurable fun p : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) × (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => J s p.1 p.2 := by
    dsimp only [J]
    apply Finset.measurable_sum
    intro i _
    simpa only [Function.comp_def] using (hmE s).comp (hmap i)
  have hmJ' (s : ℝ) : Measurable fun p : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) × (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => J' s p.1 p.2 := by
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
  have hcalc (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (s : ℝ) (hs : s ∈ V) :
      HasDerivAt (fun q => E q ω x) (E' s ω x) s :=
    hasDerivAt_perceptron_smart_path_energy ⟨hδ.trans hs.1, by linarith [hs.2]⟩ hu
      ω.1.1 ω.1.2 x.2 x.1.1 x.1.2 ω.2
  have hdb (s : ℝ) (hs : s ∈ V) (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E' s ω x| ≤ Q ω * Real.exp (∑ k, |x.2 k|) := by
    let T := |ω.2| + (∑ k, |ω.1.2 k|) + ∑ k, |x.2 k|
    have htotal : T ≤ Real.exp T := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp T)
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
    have hlin := abs_deriv_perceptron_smart_path_energy_le hδ ⟨hs.1.le, hs.2.le⟩ hu hD
      ω.1.1 ω.1.2 x.2 x.1.1 x.1.2 ω.2
    change |deriv (fun q => E q ω x) s| ≤
      |ω.2| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ) at hlin
    rw [(hcalc ω x s hs).deriv] at hlin
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
end SpinGlasses
