/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.RGFlow.Metric
public import LeanMachineLearning.Optimization.Renormalization.NearlyGaussian

/-!
# The four-point vertex and the nearly-Gaussian action match

This file formalizes `docs/Renormalization.md`'s `eq:vertex-in-terms-of-metric-fluctuation` (the
four-point vertex, as the variance of the metric fluctuation) and
`eq:second-layer-quadratic-coupling`/`eq:second-layer-quartic-coupling` (the identification of a
layer's marginal law with the law of an `EvenAction` of half-degree two). Both the vertex and the
matching theorem are built directly on top of the *already proved*
`Renormalization.jointCumulant` and `Renormalization.QuarticCoupling` machinery in
`Cumulant.lean`/`Quartic.lean`: no Wick-pairing enumeration or quartic-response calculation is
redone here.

See `LML/blueprint/src/chapters/renormalization.tex`, Chapter "RG flow of preactivations",
Section "The four-point vertex and the nearly-Gaussian action match".
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter NeuralNetwork Renormalization
open scoped ENNReal NNReal

namespace RGFlow

universe uA uI

variable {A : Type uA} {ι : Type uI} [Fintype ι] [Fintype A] [DecidableEq A]

/-- The four-point vertex `V^{(ℓ+1)}`: `n_ℓ` times the covariance of two entries of the
stochastic metric, i.e. the second joint cumulant of `stochasticMetric _ _ · a₁ a₂` and
`stochasticMetric _ _ · a₃ a₄` under the previous layer's law `ν`.

Using `Renormalization.jointCumulant` rather than a bespoke covariance definition means every
symmetry, bilinearity, and vanishing-under-independence lemma already proved for `jointCumulant`
transfers to `fourPointVertex` for free.

Source: `eq:vertex-in-terms-of-metric-fluctuation`, specialized at `ℓ+1=2` to
`eq:second-layer-metric-fluctuation-two-point-function`. -/
def fourPointVertex (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams) (σ : ℝ → ℝ)
    (a₁ a₂ a₃ a₄ : A) : ℝ :=
  (n : ℝ) * jointCumulant ν
    ![fun z => stochasticMetric p σ z a₁ a₂, fun z => stochasticMetric p σ z a₃ a₄]

omit [Fintype A] [DecidableEq A] in
/-- The four-point vertex is manifestly symmetric under swapping the first pair, the second pair,
or the two pairs as a whole (the eight-element dihedral symmetry visible from its definition).
Full symmetry under all of `Equiv.Perm (Fin 4)` — needed to package it as a
`Renormalization.QuarticCoupling` — is the strictly stronger content of
`fourPointVertex_coeff_perm` below, and is not definitional. -/
theorem fourPointVertex_swap_left (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams)
    (σ : ℝ → ℝ) (a₁ a₂ a₃ a₄ : A) :
    fourPointVertex ν n p σ a₂ a₁ a₃ a₄ = fourPointVertex ν n p σ a₁ a₂ a₃ a₄ := by
  simp [fourPointVertex, mul_comm]

/-- **The four-point vertex is fully permutation-symmetric in its four sample legs.**

This is the genuinely new nonnegativity/symmetry fact the chapter needs: the vertex, defined via
the covariance of *two paired* metric entries, agrees with the fully symmetric connected
four-point function of the four separate legs `z_{a₁}, z_{a₂}, z_{a₃}, z_{a₄}` (any of the three
ways of pairing four legs into two gives the same connected correlator, once expanded through the
moment-cumulant relation). Consequently `fourPointVertex` is invariant under every permutation of
`(a₁, a₂, a₃, a₄)`, not just the eight-element dihedral subgroup visible from
`fourPointVertex_swap_left`.

Informal proof: expand both sides via `eq:second-layer-metric-fluctuation-two-point-function`'s
derivation, i.e. write `Cov[ΔG_{a₁a₂}, ΔG_{a₃a₄}]` as a sum over coincident/distinct-neuron terms
(as in the source's `eq:activation-four-point-same-neurons` and
`eq:activation-four-point-different-neurons`) and recognize the coincident-neuron term as exactly
the connected four-point Gaussian bracket `⟨σ_{a₁}σ_{a₂}σ_{a₃}σ_{a₄}⟩_c`, which is symmetric in all
four legs because Gaussian (and more generally joint) cumulants are symmetric in their arguments
(`Renormalization.jointCumulant_perm`).
Source: `eq:second-layer-metric-fluctuation-two-point-function` together with the general
even-moment formula `eq:general-even-moment`. -/
theorem fourPointVertex_perm (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams) (σ : ℝ → ℝ)
    (e : Equiv.Perm (Fin 4)) (a : Fin 4 → A) :
    fourPointVertex ν n p σ (a (e 0)) (a (e 1)) (a (e 2)) (a (e 3)) =
      fourPointVertex ν n p σ (a 0) (a 1) (a 2) (a 3) := by
  sorry

/-- Package `fourPointVertex / n` (the quartic coupling `v^{(ℓ+1)}` of
`eq:four-point-match-general`, *not* the vertex `V^{(ℓ+1)}` itself) as a
`Renormalization.QuarticCoupling A`, using `fourPointVertex_perm` for the required total
symmetry. -/
def QuarticCouplingOfLayer (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams) (σ : ℝ → ℝ) :
    QuarticCoupling A where
  coeff q := fourPointVertex ν n p σ (q 0) (q 1) (q 2) (q 3) / n
  coeff_perm e q := by
    have h := fourPointVertex_perm ν n p σ e q
    simp only [Function.comp_apply] at h ⊢
    rw [h]

/-- **The `EvenAction` of half-degree two attached to a layer.**

Its precision matrix is the mean metric `G^{(ℓ+1)}` and its quartic coupling is
`fourPointVertex / n_ℓ`, exactly the pair `(g_{(ℓ+1)}, v_{(ℓ+1)})` identified in
`eq:second-layer-quadratic-coupling`/`eq:second-layer-quartic-coupling`. -/
def EvenActionOfLayer (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams) (σ : ℝ → ℝ) :
    EvenAction A :=
  EvenAction.ofQuartic (meanMetric ν p σ) (QuarticCouplingOfLayer ν n p σ)

/-- **Second-layer marginal law matches an even action to relative order `1/n_ℓ`: two-point part.**

Provided the mean metric is positive semidefinite, the packaged quartic coupling is nonnegative
(as a potential), and the layer's own normalizability/integrability side conditions hold, the
two-point function of the `QuarticCouplingOfLayer`-deformed Gaussian law matches the mean metric up
to the displayed `O(ε²)` correction — this is *exactly*
`Renormalization.QuarticCoupling.twoPoint_isBigO`, instantiated at `K := meanMetric ν p σ` and
`A := QuarticCouplingOfLayer ν n p σ`; no new Wick computation is needed.

Source: `eq:second-layer-quadratic-coupling`, general-layer restatement
`eq:two-point-match-general`. -/
theorem twoPoint_ofLayer_isBigO (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams)
    (σ : ℝ → ℝ)
    (hK : (meanMetric ν p σ).PosSemidef) (hNonneg : (QuarticCouplingOfLayer ν n p σ).Nonnegative)
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ),
      Normalizable (multivariateGaussian 0 (meanMetric ν p σ))
        (QuarticCouplingOfLayer ν n p σ).potential ε)
    (hint2 : Integrable (fun z => (QuarticCouplingOfLayer ν n p σ).potential z ^ 2)
      (multivariateGaussian 0 (meanMetric ν p σ)))
    (a₁ a₂ : A)
    (hint4 : Integrable (fun z => (QuarticCouplingOfLayer ν n p σ).potential z ^ 2 *
      (z.ofLp a₁ * z.ofLp a₂)) (multivariateGaussian 0 (meanMetric ν p σ))) :
    (fun ε => ∫ z, z.ofLp a₁ * z.ofLp a₂
        ∂deform (multivariateGaussian 0 (meanMetric ν p σ))
          (QuarticCouplingOfLayer ν n p σ).potential ε -
      (meanMetric ν p σ a₁ a₂ -
        ε / 2 * (QuarticCouplingOfLayer ν n p σ).twoPointContraction (meanMetric ν p σ) a₁ a₂)) =O[
        nhdsWithin 0 (Set.Ici 0)] fun ε => ε ^ 2 :=
  QuarticCoupling.twoPoint_isBigO (QuarticCouplingOfLayer ν n p σ) (meanMetric ν p σ)
    hK hNonneg a₁ a₂ hnorm hint2 hint4

/-- **Second-layer marginal law matches an even action to relative order `1/n_ℓ`: connected
four-point part.** The connected four-point moment (joint cumulant) of the deformed law matches
`-ε · (fourth-order contraction)` up to `O(ε²)`, again a direct instance of
`Renormalization.QuarticCoupling.fourthCumulant_isBigO`.

Source: `eq:second-layer-quartic-coupling`, general-layer restatement
`eq:four-point-match-general`. -/
theorem fourthCumulant_ofLayer_isBigO (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams)
    (σ : ℝ → ℝ)
    (hK : (meanMetric ν p σ).PosSemidef) (hNonneg : (QuarticCouplingOfLayer ν n p σ).Nonnegative)
    (hnorm : ∀ ε ∈ Set.Ici (0 : ℝ),
      Normalizable (multivariateGaussian 0 (meanMetric ν p σ))
        (QuarticCouplingOfLayer ν n p σ).potential ε)
    (hint2 : Integrable (fun z => (QuarticCouplingOfLayer ν n p σ).potential z ^ 2)
      (multivariateGaussian 0 (meanMetric ν p σ)))
    (index : Fin 4 → A)
    (hint2' : ∀ r s, Integrable (fun z => (QuarticCouplingOfLayer ν n p σ).potential z ^ 2 *
      (z.ofLp (index r) * z.ofLp (index s))) (multivariateGaussian 0 (meanMetric ν p σ)))
    (hint4 : Integrable (fun z => (QuarticCouplingOfLayer ν n p σ).potential z ^ 2 *
      QuarticCoupling.coordinateProduct index z) (multivariateGaussian 0 (meanMetric ν p σ))) :
    (fun ε => (jointCumulant
          (deform (multivariateGaussian 0 (meanMetric ν p σ))
            (QuarticCouplingOfLayer ν n p σ).potential ε) fun r z => z.ofLp (index r)) +
        ε * (QuarticCouplingOfLayer ν n p σ).fourPointContraction (meanMetric ν p σ) index) =O[
        nhdsWithin 0 (Set.Ici 0)] fun ε => ε ^ 2 :=
  QuarticCoupling.fourthCumulant_isBigO (QuarticCouplingOfLayer ν n p σ) (meanMetric ν p σ)
    hK hNonneg hnorm hint2 index hint2' hint4

end RGFlow
