/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathAssembly
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaEquivariance

/-!
# Exchangeable constraints on the perceptron smart path

Talagrand, Section 2.2, Proposition 2.2.3, Step 6. If the old rows are exchangeable, swapping the
constraints `i ↔ j` (rows and quenched couplings of the disorder, together with the auxiliary
coordinates `ξ_i ↔ ξ_j` of the states) preserves the disorder law and the base law, transforms the
energy and the potential kernel accordingly, and so leaves the expected pair average of every
constraint equal. The sum over `k` in `hasDerivAt_integral_integral_pi_perceptron_smart_path_ibp`
is then `M` times the term of one fixed constraint (the book's `α` times the last constraint).

* `smartPathStateSwap`, `smartPathDisorderSwap`: the two involutions;
* `smartPathEnergy_swap`, `smartPathPotentialKernel_swap`: the transformation rules;
* `replicaPairAverage_swap`: the pair average is equivariant (`map_tilted_equiv`,
  `replicaPairAverage_map_equiv`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace SpinGlasses

variable {N M : ℕ}

/-- Swap the auxiliary coordinates `ξ_i ↔ ξ_j` of a state (an involution). -/
def smartPathStateSwap (i j : Fin M) : SmartPathState N M ≃ᵐ SmartPathState N M where
  toFun x := (x.1, fun l => x.2 (Equiv.swap i j l))
  invFun x := (x.1, fun l => x.2 (Equiv.swap i j l))
  left_inv x := Prod.ext rfl (funext fun l => by simp)
  right_inv x := Prod.ext rfl (funext fun l => by simp)
  measurable_toFun := measurable_fst.prodMk (measurable_pi_iff.2 fun l =>
    (measurable_pi_apply (Equiv.swap i j l)).comp measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_pi_iff.2 fun l =>
    (measurable_pi_apply (Equiv.swap i j l)).comp measurable_snd)

theorem smartPathStateSwap_apply (i j : Fin M) (x : SmartPathState N M) :
    smartPathStateSwap i j x = (x.1, fun l => x.2 (Equiv.swap i j l)) := rfl

theorem smartPathStateSwap_symm (i j : Fin M) :
    (smartPathStateSwap (N := N) i j).symm = smartPathStateSwap i j := rfl

/-- Swap the constraints `i ↔ j` of the disorder (rows and couplings). -/
def smartPathDisorderSwap (i j : Fin M) (ω : SmartPathDisorder N M) : SmartPathDisorder N M :=
  ((fun l => ω.1.1 (Equiv.swap i j l), fun l => ω.1.2 (Equiv.swap i j l)), ω.2)

theorem smartPathField_swap (t : ℝ) (i j : Fin M) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) (l : Fin M) :
    smartPathField t (smartPathDisorderSwap i j ω) x l =
      smartPathField t ω (smartPathStateSwap i j x) (Equiv.swap i j l) := by
  simp [smartPathField, smartPathFieldNoAux, smartPathDisorderSwap, smartPathStateSwap_apply]

theorem smartPathEnergy_swap (u : ℝ → ℝ) (t : ℝ) (i j : Fin M) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) :
    smartPathEnergy u t (smartPathDisorderSwap i j ω) x =
      smartPathEnergy u t ω (smartPathStateSwap i j x) := by
  simp only [smartPathEnergy_eq]
  have h := Equiv.sum_comp (Equiv.swap i j)
    (fun l => u (smartPathField t ω (smartPathStateSwap i j x) l))
  simp only [smartPathField_swap]
  rw [h, smartPathStateSwap_apply, smartPathDisorderSwap]

theorem smartPathPotentialKernel_swap (u : ℝ → ℝ) (t : ℝ) (i j : Fin M)
    (ω : SmartPathDisorder N M) (k : Fin M) (a b : SmartPathState N M) :
    smartPathPotentialKernel u t (smartPathDisorderSwap i j ω) k a b =
      smartPathPotentialKernel u t ω (Equiv.swap i j k) (smartPathStateSwap i j a)
        (smartPathStateSwap i j b) := by
  simp only [smartPathPotentialKernel_eq_mul, smartPathField_swap]
  rfl

/-- The auxiliary-coordinate swap preserves the smart-path base law. -/
theorem measurePreserving_smartPathStateSwap (i j : Fin M) :
    MeasurePreserving (smartPathStateSwap (N := N) i j) (smartPathBase N M)
      (smartPathBase N M) := by
  have h : MeasurePreserving (fun ξ : Fin M → ℝ => fun l => ξ (Equiv.swap i j l))
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
      (Measure.pi fun _ : Fin M => gaussianReal 0 1) :=
    measurePreserving_pi_comp_injective (gaussianReal 0 1) (Equiv.injective (Equiv.swap i j))
  exact (MeasurePreserving.id (Measure.count : Measure (PerceptronSpin N))).prod h

/-- The constraint swap preserves the disorder law when the old rows are exchangeable. -/
theorem measurePreserving_smartPathDisorderSwap {Pold : Measure (Fin M → Fin N → ℝ)}
    [IsFiniteMeasure Pold] (v : ℝ≥0) (i j : Fin M)
    (hP : Pold.map (fun g : Fin M → Fin N → ℝ => fun l => g (Equiv.swap i j l)) = Pold) :
    MeasurePreserving (smartPathDisorderSwap (N := N) i j) (smartPathDisorder Pold v)
      (smartPathDisorder Pold v) := by
  have h1 : MeasurePreserving (fun g : Fin M → Fin N → ℝ => fun l => g (Equiv.swap i j l))
      Pold Pold := ⟨measurable_pi_iff.2 fun l => measurable_pi_apply _, hP⟩
  have h2 : MeasurePreserving (fun ξ : Fin M → ℝ => fun l => ξ (Equiv.swap i j l))
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
      (Measure.pi fun _ : Fin M => gaussianReal 0 1) :=
    measurePreserving_pi_comp_injective (gaussianReal 0 1) (Equiv.injective (Equiv.swap i j))
  exact (h1.prod h2).prod (MeasurePreserving.id (gaussianReal 0 v))

theorem smartPathStateSwap_swap (i j : Fin M) (x : SmartPathState N M) :
    smartPathStateSwap i j (smartPathStateSwap i j x) = x := by
  refine Prod.ext rfl (funext fun l => ?_)
  simp [smartPathStateSwap_apply]

/-- The Gibbs measure of the swapped disorder is the push-forward of the original one, for any
base law preserved by the swap of the auxiliary coordinates. -/
theorem tilted_swap {μ : Measure (SmartPathState N M)} {u : ℝ → ℝ} (hu : Measurable u) (t : ℝ)
    (i j : Fin M) (hμ : MeasurePreserving (smartPathStateSwap (N := N) i j) μ μ)
    (ω : SmartPathDisorder N M) :
    μ.tilted (smartPathEnergy u t (smartPathDisorderSwap i j ω)) =
      (μ.tilted (smartPathEnergy u t ω)).map (smartPathStateSwap i j) := by
  rw [map_tilted_equiv (smartPathStateSwap i j) hμ (measurable_smartPathEnergy_slice hu t ω)]
  congr 1
  funext x
  exact smartPathEnergy_swap u t i j ω x

/-- **Constraint swap symmetry of the pair average.** For a spin-only observable, the pair average
of the `k`-th potential kernel at the swapped disorder is the pair average of the kernel of the
swapped constraint at the original disorder. -/
theorem replicaPairAverage_swap {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] [LinearOrder R] {u : ℝ → ℝ} {B D : ℝ}
    (hu : SmartPathPotential u B D) (t : ℝ) (i j : Fin M)
    (hμ : MeasurePreserving (smartPathStateSwap (N := N) i j) μ μ) (ω : SmartPathDisorder N M)
    (f : (R → PerceptronSpin N) → ℝ) (k : Fin M) :
    replicaPairAverage (μ.tilted (smartPathEnergy u t (smartPathDisorderSwap i j ω)))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
      (smartPathPotentialKernel u t (smartPathDisorderSwap i j ω) k) =
    replicaPairAverage (μ.tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
      (smartPathPotentialKernel u t ω (Equiv.swap i j k)) := by
  have hprob : IsProbabilityMeasure (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable
      (fun x => hu.le x) ω t
  rw [tilted_swap hu.measurable t i j hμ, replicaPairAverage_map_equiv]
  congr 1

/-- **Constraint swap symmetry of the diagonal term.** -/
theorem replicaDiff_diag_swap {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    {R : Type*} [Fintype R] {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (t : ℝ)
    (i j : Fin M) (hμ : MeasurePreserving (smartPathStateSwap (N := N) i j) μ μ)
    (ω : SmartPathDisorder N M) (f : (R → PerceptronSpin N) → ℝ) (k : Fin M) :
    replicaDiff (μ.tilted (smartPathEnergy u t (smartPathDisorderSwap i j ω)))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
      (fun x => deriv (deriv u) (smartPathField t (smartPathDisorderSwap i j ω) x k) +
        deriv u (smartPathField t (smartPathDisorderSwap i j ω) x k) ^ 2) =
    replicaDiff (μ.tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
      (fun x => deriv (deriv u) (smartPathField t ω x (Equiv.swap i j k)) +
        deriv u (smartPathField t ω x (Equiv.swap i j k)) ^ 2) := by
  have hprob : IsProbabilityMeasure (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable
      (fun x => hu.le x) ω t
  rw [tilted_swap hu.measurable t i j hμ, replicaDiff_map_equiv]
  congr 1

/-- **Equal expected pair averages for exchangeable constraints.** If the old rows are invariant
under swapping `i ↔ j`, then the swapped constraints have the same expected pair average of the
potential kernel. -/
theorem integral_replicaPairAverage_swap {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ]
    [NeZero μ] {R : Type*} [Fintype R] [LinearOrder R] {t : ℝ}
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold] (i j : Fin M)
    (hμ : MeasurePreserving (smartPathStateSwap (N := N) i j) μ μ)
    (hP : Pold.map (fun g : Fin M → Fin N → ℝ => fun l => g (Equiv.swap i j l)) = Pold)
    (f : (R → PerceptronSpin N) → ℝ) (k : Fin M) :
    ∫ ω, replicaPairAverage (μ.tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (smartPathPotentialKernel u t ω (Equiv.swap i j k)) ∂(smartPathDisorder Pold v) =
      ∫ ω, replicaPairAverage (μ.tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (smartPathPotentialKernel u t ω k) ∂(smartPathDisorder Pold v) := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  have hFm := measurable_spin_only (N := N) (M := M) f
  have hFb : ∀ σ : R → SmartPathState N M, |f (fun r => (σ r).1)| ≤ C := fun σ => hC _
  have hmeas := (integrable_replicaPairAverage_kernel (μ := μ) (t := t) hu _
    hFm hFb k (smartPathDisorder Pold v)).aestronglyMeasurable
  have h := (measurePreserving_smartPathDisorderSwap v i j hP).integral_comp_of_aestronglyMeasurable
    hmeas
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun ω => (replicaPairAverage_swap hu
    t i j hμ ω f k).symm)

/-- **Equal expected diagonal terms for exchangeable constraints.** -/
theorem integral_replicaDiff_diag_swap {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ]
    [NeZero μ] {R : Type*} [Fintype R] {t : ℝ}
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold] (i j : Fin M)
    (hμ : MeasurePreserving (smartPathStateSwap (N := N) i j) μ μ)
    (hP : Pold.map (fun g : Fin M → Fin N → ℝ => fun l => g (Equiv.swap i j l)) = Pold)
    (f : (R → PerceptronSpin N) → ℝ) (k : Fin M) :
    ∫ ω, replicaDiff (μ.tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (fun x => deriv (deriv u) (smartPathField t ω x (Equiv.swap i j k)) +
          deriv u (smartPathField t ω x (Equiv.swap i j k)) ^ 2) ∂(smartPathDisorder Pold v) =
      ∫ ω, replicaDiff (μ.tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (fun x => deriv (deriv u) (smartPathField t ω x k) +
          deriv u (smartPathField t ω x k) ^ 2) ∂(smartPathDisorder Pold v) := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  have hFm := measurable_spin_only (N := N) (M := M) f
  have hFb : ∀ σ : R → SmartPathState N M, |f (fun r => (σ r).1)| ≤ C := fun σ => hC _
  have hmeas := (integrable_replicaDiff_diag (μ := μ) (t := t) hu _ hFm hFb k
    (smartPathDisorder Pold v)).aestronglyMeasurable
  have h := (measurePreserving_smartPathDisorderSwap v i j hP).integral_comp_of_aestronglyMeasurable
    hmeas
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun ω => (replicaDiff_diag_swap hu.toSmartPathPotential
    t i j hμ ω f k).symm)

/-- **Proposition 2.2.3, exchangeable form (Step 6).** If the old rows are exchangeable, i.e. their
law is invariant under swapping any constraint `k` with a fixed constraint `j₀` (the book's last
one), the sum over the constraints in the derivative is `M` times the term of `j₀`: the printed
`α = M/(N+1)` form `(M/(N+1)) 𝔼⟨f pd(U_{j₀})⟩_t − v 𝔼⟨f pd(ε ε')⟩_t`. Exchangeability is a
hypothesis on the law of the rows (the book derives it from independence); it is never assumed
for the observable or the expectation. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_exchangeable {R : Type*}
    [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ}
    {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold] (j₀ : Fin M)
    (hPold : ∀ k : Fin M,
      Pold.map (fun g : Fin M → Fin N → ℝ => fun l => g (Equiv.swap k j₀ l)) = Pold)
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      ((M : ℝ) / ((N : ℝ) + 1) * ∫ ω, replicaPairAverage
          ((smartPathBase N M).tilted (smartPathEnergy u t ω))
          (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
          (smartPathPotentialKernel u t ω j₀) ∂(smartPathDisorder Pold v) -
        (v : ℝ) * ∫ ω, replicaPairAverage ((smartPathBase N M).tilted (smartPathEnergy u t ω))
          (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) lastSpinKernel
          ∂(smartPathDisorder Pold v)) t := by
  have h := hasDerivAt_integral_integral_pi_perceptron_smart_path_ibp (t := t) ht hu v
    (Pold := Pold) f
  refine h.congr_deriv ?_
  have hk (k : Fin M) : ∫ ω, replicaPairAverage ((smartPathBase N M).tilted
      (smartPathEnergy u t ω)) (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
      (smartPathPotentialKernel u t ω k) ∂(smartPathDisorder Pold v) =
      ∫ ω, replicaPairAverage ((smartPathBase N M).tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
      (smartPathPotentialKernel u t ω j₀) ∂(smartPathDisorder Pold v) := by
    have := integral_replicaPairAverage_swap (μ := smartPathBase N M) (t := t)
      hu.toSmartPathPotential v k j₀
      (measurePreserving_smartPathStateSwap k j₀) (hPold k) f j₀
    simpa using this
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SpinGlasses
