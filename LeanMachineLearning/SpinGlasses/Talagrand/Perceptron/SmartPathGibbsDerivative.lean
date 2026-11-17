/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathBounds
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDifferentiation

/-!
# Differentiating replica Gibbs averages of the perceptron smart path

The auxiliary Gaussian coordinates belong to each replica's configuration. At fixed
quenched disorder the derivative of a bounded replica average is the sum of the energy
derivative terms at the observed replicas, minus their number times a fresh-replica term.

The proof supplies the integrable Gaussian envelope needed to differentiate the numerator
and normalizer. It reuses arbitrary-base exponential-tilt and replica differentiation lemmas.
No passage through the quenched-disorder integral or Gaussian integration by parts is
asserted in this file yet. Empty constraint and replica types and one full spin are allowed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace SpinGlasses

/-- **Talagrand (2.26), at fixed disorder.** Differentiation through all replica and auxiliary
integrals is justified by Gaussian first moments. A measurable upper-bounded potential with
bounded first derivative suffices; the replica observable is bounded and independent of `t`.
The observed replicas are indexed by `R`, and `none : Option R` is one fresh replica. -/
theorem hasDerivAt_integral_pi_perceptron_smart_path {N M : ℕ} {R : Type*} [Fintype R] {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D : ℝ} (hB : ∀ z, u z ≤ B) (hD : ∀ z, |deriv u z| ≤ D)
    (g : Fin M → Fin N → ℝ) (a : Fin M → ℝ) (y : ℝ)
    (F : (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    let S := fun (s : ℝ) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (k : Fin M) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (s / (N + 1)) * a k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - s) / (N + 1)) * x.2 k
    let E := fun (s : ℝ) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * y + ∑ k, u (S s x k)
    let E' := fun (s : ℝ) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      -((x.1.2 : ℤ) : ℝ) * y / (2 * Real.sqrt (1 - s)) +
      ∑ k, deriv u (S s x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        (a k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s - x.2 k / Real.sqrt (1 - s)))
    let μ := (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    HasDerivAt (fun s => ∫ σ, F σ ∂(Measure.pi fun _ : R => μ.tilted (E s)))
      ((∑ i, ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * E' t (σ (some i))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) -
        (Fintype.card R : ℝ) * ∫ σ : Option R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
          F (fun j => σ (some j)) * E' t (σ none)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) t := by
  intro S E E' μ
  let δ := min t (1 - t) / 2
  have hmin : 0 < min t (1 - t) := lt_min ht.1 (sub_pos.mpr ht.2)
  have hδ : 0 < δ := div_pos hmin (by norm_num)
  have hδt : δ < t := by
    have := min_le_left t (1 - t)
    dsimp only [δ]
    linarith
  have hδ1 : δ < 1 - t := by
    have := min_le_right t (1 - t)
    dsimp only [δ]
    linarith
  let s := Set.Ioo δ (1 - δ)
  have hs : s ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hδt, by linarith⟩
  have hmE (r : ℝ) : Measurable (E r) := by
    simpa only [E, S, Function.comp_def, id_eq] using
      (measurable_perceptron_smart_path_energy (N := N) (M := M) hu.continuous.measurable r).comp
        ((measurable_const (a := ((g, a), y))).prodMk measurable_id)
  have hmE' (r : ℝ) : Measurable (E' r) := by
    have hdu := measurable_deriv u
    have hcast : Measurable (fun ε : ℤˣ => ((ε : ℤ) : ℝ)) := measurable_of_countable _
    dsimp only [E', S]
    fun_prop
  have hEb (r : ℝ) (hr : r ∈ s) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      E r x ≤ M * B + |y| :=
    perceptron_smart_path_energy_le_of_nonneg hB g a y r (hδ.trans hr.1).le x
  let b := fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
    |y| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
      ((|a k| + |x.2 k|) / Real.sqrt δ)
  have hG : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := by
    have h : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 1) := memLp_id_gaussianReal 1
    exact h.integrable le_rfl
  have hξ (k : Fin M) : Integrable
      (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) => |x.2 k|) μ :=
    (integrable_comp_eval hG.abs).comp_snd (Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ))
  have hterms (k : Fin M) : Integrable
      (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
        D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * ((|a k| + |x.2 k|) / Real.sqrt δ)) μ := by
    simpa only [Pi.add_apply] using
      (((integrable_const |a k|).add (hξ k)).div_const (Real.sqrt δ)).const_mul
        (D * (1 / (2 * Real.sqrt (N + 1 : ℕ))))
  have hib : Integrable b μ := by
    have hraw := (integrable_const (|y| / (2 * Real.sqrt δ))).add
      (integrable_finsetSum Finset.univ fun k _ => hterms k)
    exact hraw.congr (ae_of_all _ fun x => rfl)
  have hcalc (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) (r : ℝ) (hr : r ∈ s) :
      HasDerivAt (fun q => E q x) (E' r x) r := by
    have hr0 : 0 < r := hδ.trans hr.1
    have hr1 : r < 1 := by linarith [hr.2, hδ]
    exact hasDerivAt_perceptron_smart_path_energy ⟨hr0, hr1⟩ hu g a x.2 x.1.1 x.1.2 y
  have hdb (r : ℝ) (hr : r ∈ s) (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
      |E' r x| ≤ b x := by
    rw [← (hcalc x r hr).deriv]
    exact abs_deriv_perceptron_smart_path_energy_le hδ ⟨hr.1.le, hr.2.le⟩ hu hD
      g a x.2 x.1.1 x.1.2 y
  have hres := hasDerivAt_integral_pi_tilted_of_dominated (μ := μ) (E := E) (E' := E') hs
    (fun r _ => hmE r) (hmE' t) hEb hib hdb hcalc hF hFb
  have hts : t ∈ s := mem_of_mem_nhds hs
  have hiE' : Integrable (E' t) μ := hib.mono' (hmE' t).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hdb t hts x)
  have hiExp : Integrable (fun x => Real.exp (E t x)) μ :=
    integrable_exp_perceptron_smart_path_energy hu.continuous.measurable hB g a y t
  have hν : IsProbabilityMeasure (μ.tilted (E t)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.continuous.measurable hB g a y t
  have hiWeighted := hiE'.bdd_mul (hmE t).exp.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (hEb t hts x))
  have hiTilted : Integrable (E' t) (μ.tilted (E t)) :=
    (integrable_tilted_iff hiExp (E' t)).mpr (by
      simpa only [smul_eq_mul] using hiWeighted)
  convert hres using 1
  exact (integral_pi_cov_sum_eq_sum_sub_fresh (μ.tilted (E t)) F
    hF.aestronglyMeasurable hFb (E' t) hiTilted).symm
end SpinGlasses
