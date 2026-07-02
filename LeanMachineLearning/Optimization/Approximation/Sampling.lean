/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.BarronNorm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Sampling from infinite-width networks: Maurey's lemma

This file formalizes Section 3.3 of the deep learning theory notes (Telgarsky 2021),
which develops the technique for converting an *infinite-width* representation into a
*finite-width* approximation by random sampling.

The core tool is **Maurey's sampling lemma** (attributed to Maurey; stated in Pisier 1980),
which in a Hilbert space H says:

  If X = 𝔼[V] and V is supported on S, then
  𝔼[‖X - (1/k) ∑ᵢ Vᵢ‖²] ≤ (sup_{U ∈ S} ‖U‖²) / k,

and therefore there *exist* deterministic u₁, …, uₖ in S achieving the same bound.

For signed measures this is extended via Jordan decomposition: given
  g(x) = ∫ g(x;w) dμ(w),
one normalizes μ into a probability by folding in the mass and a sign, samples k iid
weight vectors, and obtains:

  ‖g - (1/k) ∑ᵢ g̃(·; wᵢ, sᵢ)‖²_{L₂(P)} ≤ (‖μ‖₁² · sup_w ‖g(·;w)‖²_{L₂(P)}) / k.

## Main results

* `maureySampling` : Lemma 3.1 — Maurey's inequality in a Hilbert space.
* `maureySamplingExistence` : the deterministic version (existence of good uᵢ's).
* `MaureySignedMeasure` : Lemma 3.2 — Maurey's inequality for signed measures.
* `barronSamplingBound` : combining Theorem 3.1 + Lemma 3.2 to get Barron's full result:
  a function with barronNorm ≤ C can be approximated to L₂(P) error ε by a threshold
  network with ≤ ⌈4C²/ε²⌉ nodes.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace Approximation.Sampling

/-! ### Maurey's lemma in Hilbert spaces (Lemma 3.1) -/

/-- **Lemma 3.1** (Maurey; Pisier 1980).
In a Hilbert space H, if X = 𝔼[V] where V is supported on S, and (V₁, …, Vₖ) are
iid draws from the same distribution, then

  𝔼[‖X - (1/k) ∑ᵢ Vᵢ‖²] ≤ 𝔼[‖V‖²] / k  ≤  (sup_{U ∈ S} ‖U‖²) / k.

**Proof.** Expand ‖(1/k) ∑ᵢ (Vᵢ - X)‖². By iid and zero-mean:
  cross terms vanish, diagonal gives 𝔼[‖V - X‖²]/k ≤ 𝔼[‖V‖²]/k. -/
theorem maureySampling
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    {μ_prob : Measure Ω} [IsProbabilityMeasure μ_prob]
    {V : Ω → H}
    (hV_int : Integrable V μ_prob)
    {k : ℕ} (hk : 0 < k)
    {Vᵢ : Fin k → Ω → H}
    (hVi_iid : ∀ i, Integrable (Vᵢ i) μ_prob)
    (hVi_mean : ∀ i, ∫ ω, Vᵢ i ω ∂μ_prob = ∫ ω, V ω ∂μ_prob)
    (hVi_indep : iIndepFun (m := fun _ => inferInstance) Vᵢ μ_prob)
    (hVi_dist : ∀ i, ∀ s, μ_prob (Vᵢ i ⁻¹' s) = μ_prob (V ⁻¹' s)) :
    let X := ∫ ω, V ω ∂μ_prob
    ∫ ω, ‖X - (1 / k : ℝ) • ∑ i, Vᵢ i ω‖ ^ 2 ∂μ_prob ≤
      (∫ ω, ‖V ω‖ ^ 2 ∂μ_prob) / k := by
  sorry

/-- The deterministic Maurey bound: there *exist* u₁, …, uₖ in S such that
  ‖X - (1/k) ∑ᵢ uᵢ‖² ≤ (sup_{u ∈ S} ‖u‖²) / k.
(Lemma 3.1, second part; Pisier 1980.) -/
theorem maureySamplingExistence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Set H} (hS_ne : S.Nonempty)
    {X : H} (hX : X ∈ closure (convexHull ℝ S))
    {k : ℕ} (hk : 0 < k) :
    ∃ u : Fin k → H, (∀ i, u i ∈ S) ∧
      ‖X - (1 / k : ℝ) • ∑ i, u i‖ ^ 2 ≤
        (⨆ u ∈ S, ‖u‖ ^ 2) / k := by
  sorry

/-! ### Maurey for signed measures (Lemma 3.2) -/

/-- A sample from a normalized signed measure: a weight vector w together with a sign s ∈ {±1}.
The sign s = +1 (resp. -1) indicates the positive (resp. negative) part of the Jordan
decomposition. -/
structure SignedSample (p : ℕ) where
  weight : Fin p → ℝ
  sign   : Bool  -- true = +1, false = -1

variable {p : ℕ}

/-- Reconstruct a signed real from a `SignedSample`. -/
def SignedSample.toReal (s : SignedSample p) : ℝ := if s.sign then 1 else -1

/-- The rescaled function evaluated at a signed sample:
  g̃(x; (w, s)) = s · ‖μ‖₁ · g(x; w). -/
noncomputable def rescaledEval
    (g : (Fin p → ℝ) → ℝ) (mass : ℝ) (s : SignedSample p) : ℝ :=
  s.toReal * mass * g s.weight

/-- **Lemma 3.2** (Maurey for signed measures; Telgarsky 2021).
Let μ be a nonzero signed measure on S ⊆ ℝᵖ and write
  g(x) := ∫ g(x;w) dμ(w).
Let P be a probability measure on x and (w̃₁, …, w̃ₖ) be iid draws from the
normalized distribution derived from the Jordan decomposition of μ. Then

  𝔼[‖g - (1/k) ∑ᵢ g̃(·; w̃ᵢ)‖²_{L₂(P)}] ≤ ‖μ‖₁² · sup_{w ∈ S} ‖g(·;w)‖²_{L₂(P)} / k.

**Proof sketch.** The Jordan decomposition gives μ = μ₊ - μ₋. We define a probability
distribution on pairs (s, w) with s ∈ {±1} by:
  P[s = +1] = ‖μ₊‖₁ / ‖μ‖₁, then sample w ~ μ_s/‖μ_s‖₁.
Then g̃(x;(s,w)) = s‖μ‖₁g(x;w) has the correct mean 𝔼[g̃(x;(s,w))] = g(x),
and ‖g̃‖²_{L₂(P)} ≤ ‖μ‖₁² sup_w ‖g(·;w)‖²_{L₂(P)}.
Apply the standard Maurey lemma to the Hilbert space L₂(P). -/
theorem maureySamplingSignedMeasure
    {p : ℕ}
    {Ω_x : Type*} {mΩ_x : MeasurableSpace Ω_x}
    (P : Measure Ω_x) [IsProbabilityMeasure P]
    {S : Set (Fin p → ℝ)}
    (g : (Fin p → ℝ) → Ω_x → ℝ)
    (μ : SignedMeasure (Fin p → ℝ))
    (hμ_ne : μ ≠ 0)
    (mass : ℝ) (hmass : mass =
      (μ.toJordanDecomposition.posPart Set.univ).toReal +
      (μ.toJordanDecomposition.negPart Set.univ).toReal)
    (g_int : ∀ w ∈ S, Integrable (g w) P)
    (g_agg : ∀ (x : Ω_x),
        ∫ w : Fin p → ℝ, g w x ∂μ.toJordanDecomposition.posPart -
        ∫ w : Fin p → ℝ, g w x ∂μ.toJordanDecomposition.negPart = 0)
    {k : ℕ} (hk : 0 < k)
    (gFun : Ω_x → ℝ) -- g(x) = ∫ g(x;w) dμ(w)
    (hgFun : ∀ x, gFun x = ∫ w : Fin p → ℝ, g w x ∂μ.toJordanDecomposition.posPart -
                             ∫ w : Fin p → ℝ, g w x ∂μ.toJordanDecomposition.negPart) :
    ∃ (ws : Fin k → SignedSample p),
      (∀ i, ws i ∈ (fun w => SignedSample.mk w true) '' S ∪
                   (fun w => SignedSample.mk w false) '' S → True) ∧
      ∫ x, (gFun x - (1 / k : ℝ) * ∑ i, rescaledEval (g · x) mass (ws i)) ^ 2 ∂P ≤
        mass ^ 2 * (⨆ w ∈ S, ∫ x, (g w x) ^ 2 ∂P) / k := by
  sorry

/-! ### Barron's full sampling bound -/

/-- **Barron's sampling bound** (combining Theorem 3.1 + Lemma 3.2).
If f has barronNorm f ≤ C and P is a probability measure supported on ‖x‖ ≤ 1, then
for any k ≥ 1 there exist (w₁, b₁, s₁), …, (wₖ, bₖ, sₖ) such that the threshold net

  f̂(x) := f(0) + (2C/k) ∑ᵢ sᵢ · 1[wᵢᵀx ≥ bᵢ]

satisfies the L₂(P) error bound

  ‖f - f̂‖²_{L₂(P)} ≤ 4C² / k.

In particular, to achieve error ε, it suffices to take k ≥ 4C²/ε². -/
theorem barronSamplingBound
    {d : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    {C : ℝ} (hC : 0 < C)
    (hf : f ∈ BarronNorm.BarronClass C d)
    (hf_L1 : Integrable f volume)
    (hfhat_L1 : Integrable (BarronNorm.fourierTransform f) volume)
    {Ω_x : Type*} {mΩ_x : MeasurableSpace Ω_x}
    (P : Measure Ω_x) [IsProbabilityMeasure P]
    (x_embed : Ω_x → Fin d → ℝ) (hx_unit : ∀ ω, ‖x_embed ω‖ ≤ 1)
    {k : ℕ} (hk : 0 < k) :
    ∃ (weights : Fin k → Fin d → ℝ)
      (biases : Fin k → ℝ)
      (signs : Fin k → ℝ),
      ∀ ω : Ω_x,
        let x := x_embed ω
        let fhat := f 0 + (2 * C / k) * ∑ i, signs i *
          thresholdActivation (BarronNorm.innerProd (weights i) x - biases i)
        (f x - fhat) ^ 2 ≤ 4 * C ^ 2 / k := by
  sorry

end Approximation.Sampling

end
