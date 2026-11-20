/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.DecoupledSpinDisorderAverage
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.AuxiliaryMarginal
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathModel

/-!
# The decoupled endpoint of the perceptron smart path

Talagrand, *Spin Glasses* Vol. I, Lemma 2.2.2.  At `t = 0` the last spin of the full system of
`N + 1` spins is decoupled from the first `N` spins and the auxiliary Gaussian variables: the
energy is `A(old spins) + ε y`.  Integrating the auxiliary coordinates
(`integral_pi_perceptron_smart_path_auxiliary`) puts the replica average in the form handled by
`integral_integral_pi_count_tilted_decoupled_spin`, and the independent disorders `(g, a)` and `y`
are then integrated.  The result holds for every variance `r` of `y`, including `r = 0`, every
`M` (also `M = 0`) and every `N` (`N = 0` is one full spin).

## Main declaration

* `SpinGlasses.integral_perceptron_smart_path_decoupled_endpoint`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

/-- **Lemma 2.2.2.**  Let `ν₀ G` be the `t = 0` smart-path average of a replica observable `G`
of the spin coordinates: the replicas are independent under the counting-times-Gaussian base law
tilted by the energy of the path at `t = 0`, with the auxiliary vector integrated per replica, and
the quenched `(g, a)` (independent standard Gaussians) and `y ∼ 𝒩(0, r)` are averaged.  For a
function `F` of the first `N` spins of `n` replicas and a set `I` of replicas,
`ν₀ (F ∏_{l ∈ I} ε_l) = 𝔼 (tanh Y)^|I| · ν₀ F = ν₀ (∏_{l ∈ I} ε_l) · ν₀ F`.
No positivity of `r` and no differentiability of `u` is used; `u` is measurable and bounded
above. -/
theorem integral_perceptron_smart_path_decoupled_endpoint {N M n : ℕ} {u : ℝ → ℝ}
    (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D) (r : ℝ≥0) (I : Finset (Fin n))
    (F : (Fin n → Fin N → ℤˣ) → ℝ) :
    let ν₀ : ((Fin n → PerceptronSpin N) → ℝ) → ℝ := fun G =>
      ∫ ω : (Fin M → Fin N → ℝ) × (Fin M → ℝ), ∫ y,
        ∫ x : Fin n → SmartPathState N M, G (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin n =>
            (smartPathBase N M).tilted (smartPathEnergy u 0 (ω, y)))
        ∂(gaussianReal 0 r)
        ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1))
    ν₀ (fun σ => F (fun l => (σ l).1) * ∏ l ∈ I, (((σ l).2 : ℤˣ) : ℝ)) =
        (∫ y, Real.tanh y ^ I.card ∂gaussianReal 0 r) * ν₀ (fun σ => F (fun l => (σ l).1)) ∧
      ν₀ (fun σ => F (fun l => (σ l).1) * ∏ l ∈ I, (((σ l).2 : ℤˣ) : ℝ)) =
        ν₀ (fun σ => ∏ l ∈ I, (((σ l).2 : ℤˣ) : ℝ)) * ν₀ (fun σ => F (fun l => (σ l).1)) := by
  intro ν₀
  -- the effective energy of the old spins, independent of `a`
  set A : (Fin M → Fin N → ℝ) × (Fin M → ℝ) → (Fin N → ℤˣ) → ℝ := fun ω σ =>
    ∑ k, Real.log (∫ z, Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ *
      (∑ i, ω.1 k i * ((σ i : ℤ) : ℝ)) + Real.sqrt ((1 - 0) / (N + 1)) * z))
      ∂gaussianReal 0 1) with hA
  have hν : ∀ G : (Fin n → (Fin N → ℤˣ) × ℤˣ) → ℝ, ν₀ G =
      ∫ ω, ∫ y, ∫ σ : Fin n → (Fin N → ℤˣ) × ℤˣ, G σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun x : (Fin N → ℤˣ) × ℤˣ => A ω x.1 + ((x.2 : ℤˣ) : ℝ) * y) ∂(gaussianReal 0 r)
        ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
    intro G
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun y => ?_))
    refine (integral_pi_perceptron_smart_path_auxiliary (R := Fin n) hu hD (ω, y) 0 G).trans ?_
    have hfun : (fun σ : PerceptronSpin N => ((σ.2 : ℤ) : ℝ) * Real.sqrt (1 - 0) * y +
        ∑ k, Real.log (∫ z, Real.exp (u (smartPathFieldNoAux 0 (ω, y) (σ, 0) k +
          Real.sqrt ((1 - 0) / (N + 1)) * z)) ∂gaussianReal 0 1)) =
        fun x => A ω x.1 + ((x.2 : ℤˣ) : ℝ) * y := by
      funext σ
      simp only [smartPathFieldNoAux, A, zero_div, Real.sqrt_zero, zero_mul, add_zero, sub_zero,
        mul_one, Real.sqrt_one]
      ring
    rw [hfun]
  have hfactor (G : (Fin n → Fin N → ℤˣ) → ℝ) (J : Finset (Fin n)) :
      ν₀ (fun σ => G (fun l => (σ l).1) * ∏ l ∈ J, (((σ l).2 : ℤˣ) : ℝ)) =
        (∫ y, Real.tanh y ^ J.card ∂gaussianReal 0 r) *
          ∫ ω, ∫ ρ, G ρ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (A ω))
            ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
    exact (hν _).trans
      (integral_integral_pi_count_tilted_decoupled_spin _ (gaussianReal 0 r) A id G J)
  have hbase (G : (Fin n → Fin N → ℤˣ) → ℝ) :
      ν₀ (fun σ => G (fun l => (σ l).1)) =
        ∫ ω, ∫ ρ, G ρ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (A ω))
          ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
    simpa using hfactor G ∅
  have key (G : (Fin n → Fin N → ℤˣ) → ℝ) (J : Finset (Fin n)) :
      ν₀ (fun σ => G (fun l => (σ l).1) * ∏ l ∈ J, (((σ l).2 : ℤˣ) : ℝ)) =
        (∫ y, Real.tanh y ^ J.card ∂gaussianReal 0 r) * ν₀ (fun σ => G (fun l => (σ l).1)) :=
    (hfactor G J).trans (congrArg (fun z => (∫ y, Real.tanh y ^ J.card ∂gaussianReal 0 r) * z)
      (hbase G).symm)
  have hone : ν₀ (fun _ => (1 : ℝ)) = 1 := by
    simpa using hbase (fun _ => 1)
  refine ⟨key F I, ?_⟩
  have h1 := key F I
  have h2 := key (fun _ => 1) I
  simp only [one_mul, hone, mul_one] at h2
  rw [h1, h2]

end SpinGlasses
