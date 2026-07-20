/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.BarronNorm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Analysis.Convex.Integral

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
* `maureySamplingExistence` : the deterministic version (existence of good uᵢ's), for a point of
  the *convex hull* of `S`.  Proved by an elementary greedy argument, with no measure theory.
* `maureySamplingExistence_iSup` : the same, phrased with `⨆ u ∈ S, ‖u‖ ^ 2` as in the notes.
* `maureySamplingExistence_of_iid` : the deterministic version for a point which is the *Bochner
  mean* `X = 𝔼 V` of an `S`-valued random variable (the form actually needed by Barron's theorem,
  where the representing measure is continuous and `X` need not lie in `convexHull ℝ S`).
* `maureySamplingSignedMeasure` : Lemma 3.2 — Maurey's inequality for signed measures.
* `barronSamplingBound` : combining Theorem 3.1 + Lemma 3.2 to get Barron's full result:
  a function with barronNorm ≤ C can be approximated to L₂(P) error ε by a threshold
  network with ≤ ⌈4C²/ε²⌉ nodes.

## Implementation notes

**Upper bounds are passed explicitly, not as `⨆`.**  The hypothesis carried around is
`hB : ∀ u ∈ S, ‖u‖ ^ 2 ≤ B` rather than `B = ⨆ u ∈ S, ‖u‖ ^ 2`.  This is both more general
(any upper bound will do) and safer: `Real.sSup` returns the junk value `0` on sets that are
unbounded above, so a statement phrased directly with `⨆` is *false* for unbounded `S`.
`maureySamplingExistence_iSup` recovers the `⨆`-form under an explicit `BddAbove` hypothesis.

**`convexHull`, not `closure (convexHull …)`.**  See the warning attached to
`maureySamplingExistence`: the closure version of the statement is genuinely false.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace Approximation.Sampling

/-! ### Maurey's lemma in Hilbert spaces (Lemma 3.1) -/

private lemma integral_norm_sq_eq_of_map_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    {μ : Measure Ω} {X Y : Ω → H}
    (hX_L2 : MemLp X 2 μ) (hY_L2 : MemLp Y 2 μ)
    (hmap : Measure.map X μ = Measure.map Y μ) :
    ∫ ω, ‖X ω‖ ^ 2 ∂μ = ∫ ω, ‖Y ω‖ ^ 2 ∂μ := by
  calc
    ∫ ω, ‖X ω‖ ^ 2 ∂μ = ∫ y, ‖y‖ ^ 2 ∂Measure.map X μ := by
      symm
      exact MeasureTheory.integral_map hX_L2.aestronglyMeasurable.aemeasurable (by fun_prop)
    _ = ∫ y, ‖y‖ ^ 2 ∂Measure.map Y μ := by rw [hmap]
    _ = ∫ ω, ‖Y ω‖ ^ 2 ∂μ := by
      exact MeasureTheory.integral_map hY_L2.aestronglyMeasurable.aemeasurable (by fun_prop)

private lemma integral_centered_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSub₂ H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V W : Ω → H}
    (hV_L2 : MemLp V 2 μ)
    (hmean : ∫ ω, V ω ∂μ = ∫ ω, W ω ∂μ) :
    ∫ ω, (V ω - ∫ t, W t ∂μ) ∂μ = 0 := by
  have hV_int : Integrable V μ := hV_L2.integrable (by norm_num)
  have hconst_int : Integrable (fun _ : Ω => ∫ t, W t ∂μ) μ := by
    simp
  rw [MeasureTheory.integral_sub hV_int hconst_int]
  simpa [MeasureTheory.integral_const] using sub_eq_zero.mpr hmean

/-- Cross-term factorization for independent Hilbert-valued variables.

Informal proof:
1. Apply `ProbabilityTheory.IndepFun.integral_bilin` to the continuous bilinear map
   `(x, y) ↦ ⟪x, y⟫`.
2. The result is exactly
   `E[⟪X, Y⟫] = ⟪E[X], E[Y]⟫`.
3. We use this later with centered variables `X := Vᵢ - E[V]` and `Y := Vⱼ - E[V]`.

Lean plan:
* use `innerₗ H` as the bilinear map;
* discharge the integrability hypotheses from `MemLp ... 2`;
* `simpa` to rewrite the bilinear-map application as `inner`.
-/
private lemma integral_inner_eq_inner_integral
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSub₂ H]
    {μ : Measure Ω}
    {X Y : Ω → H}
    (hXY : X ⟂ᵢ[μ] Y)
    (hX_int : Integrable X μ)
    (hY_int : Integrable Y μ) :
    ∫ ω, inner ℝ (X ω) (Y ω) ∂μ = inner ℝ (∫ ω, X ω ∂μ) (∫ ω, Y ω ∂μ) := by
  have h := ProbabilityTheory.IndepFun.integral_bilin hXY hX_int hY_int (innerSL ℝ)
  convert h using 1
  · apply MeasureTheory.integral_congr_ae
    exact ae_of_all μ (fun ω => innerSL_apply_apply ℝ (X ω) (Y ω))
  · exact innerSL_apply_apply ℝ (∫ ω, X ω ∂μ) (∫ ω, Y ω ∂μ)

/-- For distinct indices, the centered cross term has zero integral.

Informal proof:
1. Set `X := ∫ ω, V ω ∂μ`.
2. Replace `Vᵢ i` and `Vᵢ j` by the centered variables
   `Yᵢ := Vᵢ i - X`, `Yⱼ := Vᵢ j - X`.
3. Independence is preserved under measurable postcomposition, so `Yᵢ` and `Yⱼ`
   are still independent.
   This is where Lean needs the technical hypothesis `[MeasurableSub₂ H]`: the map
   `z ↦ z - X` must be measurable in order to apply `ProbabilityTheory.IndepFun.comp`.
4. Apply `integral_inner_eq_inner_integral` to get
   `E[⟪Yᵢ, Yⱼ⟫] = ⟪E[Yᵢ], E[Yⱼ]⟫`.
5. Each centered expectation is zero by `integral_centered_eq_zero`, hence the
   right-hand side vanishes.

This is the key step making all off-diagonal terms disappear in Maurey's lemma.
-/
private lemma integral_centered_inner_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSub₂ H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ}
    {V : Ω → H}
    {Vᵢ : Fin k → Ω → H}
    (_hV_L2 : MemLp V 2 μ)
    (hVi_L2 : ∀ i, MemLp (Vᵢ i) 2 μ)
    (hVi_mean : ∀ i, ∫ ω, Vᵢ i ω ∂μ = ∫ ω, V ω ∂μ)
    (hVi_indep : iIndepFun (m := fun _ => inferInstance) Vᵢ μ)
    {i j : Fin k} (hij : i ≠ j) :
    ∫ ω, inner ℝ (Vᵢ i ω - ∫ t, V t ∂μ) (Vᵢ j ω - ∫ t, V t ∂μ) ∂μ = 0 := by
  let X := ∫ t, V t ∂μ
  let Yᵢ := Vᵢ i - fun _ : Ω => X
  let Yⱼ := Vᵢ j - fun _ : Ω => X
  have hYij_indep : Yᵢ ⟂ᵢ[μ] Yⱼ := by
    have hXi_indep : Vᵢ i ⟂ᵢ[μ] Vᵢ j := hVi_indep.indepFun hij
    have h_meas : Measurable (fun x : H => x - X) := measurable_sub_const X
    have hYi : Yᵢ = (fun x : H => x - X) ∘ Vᵢ i := by ext ω; simp [Yᵢ]
    have hYj : Yⱼ = (fun x : H => x - X) ∘ Vᵢ j := by ext ω; simp [Yⱼ]
    rw [hYi, hYj]
    exact hXi_indep.comp h_meas h_meas
  have hYᵢ_int : Integrable Yᵢ μ := by
    simpa [Yᵢ] using (hVi_L2 i).integrable (by norm_num) |>.sub (integrable_const X)
  have hYⱼ_int : Integrable Yⱼ μ := by
    simpa [Yⱼ] using (hVi_L2 j).integrable (by norm_num) |>.sub (integrable_const X)
  have h := integral_inner_eq_inner_integral hYij_indep hYᵢ_int hYⱼ_int
  have hYi_zero : ∫ ω, Yᵢ ω ∂μ = 0 := integral_centered_eq_zero (hVi_L2 i) (hVi_mean i)
  have hYj_zero : ∫ ω, Yⱼ ω ∂μ = 0 := integral_centered_eq_zero (hVi_L2 j) (hVi_mean j)
  have h_eq : ∀ ω, inner ℝ (Vᵢ i ω - X) (Vᵢ j ω - X) = inner ℝ (Yᵢ ω) (Yⱼ ω) := by
    intro ω
    simp [Yᵢ, Yⱼ]
  rw [integral_congr_ae (ae_of_all μ h_eq), h, hYi_zero, hYj_zero]
  simp

/-- Diagonal second-moment identity for centered samples.

Informal proof:
1. Expand `‖v - X‖²` using `norm_sub_sq_real`:
   `‖v‖² - 2⟪v, X⟫ + ‖X‖²`.
2. Integrate termwise.
3. Use `integral_inner` to rewrite `∫ ⟪Vᵢ, X⟫ = ⟪∫ Vᵢ, X⟫`.
4. Substitute `∫ Vᵢ = ∫ V = X`, so the middle term becomes `2‖X‖²`.
5. What remains is `E[‖Vᵢ - X‖²] = E[‖Vᵢ‖²] - ‖X‖²`.

This is the diagonal term in the Maurey expansion.
-/
private lemma integral_centered_norm_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSub₂ H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V W : Ω → H}
    (hV_L2 : MemLp V 2 μ)
    (hmean : ∫ ω, V ω ∂μ = ∫ ω, W ω ∂μ) :
    let X := ∫ ω, W ω ∂μ
    ∫ ω, ‖V ω - X‖ ^ 2 ∂μ = ∫ ω, ‖V ω‖ ^ 2 ∂μ - ‖X‖ ^ 2 := by
  intro X
  have hV_int : Integrable V μ := hV_L2.integrable (by norm_num)
  have h1 (ω : Ω) : ‖V ω - X‖ ^ 2 = ‖V ω‖ ^ 2 - 2 * inner ℝ (V ω) X + ‖X‖ ^ 2 := by
    rw [norm_sub_sq_real (V ω) X]
  have h2 : ∫ ω, ‖V ω - X‖ ^ 2 ∂μ = ∫ ω, (‖V ω‖ ^ 2 - 2 * inner ℝ (V ω) X + ‖X‖ ^ 2) ∂μ := by
    congr 1
    ext ω
    exact h1 ω
  have h3 : Integrable (fun ω => ‖V ω‖ ^ 2) μ :=
    hV_L2.integrable_norm_pow (by norm_num)
  have h4 : Integrable (fun ω => inner ℝ (V ω) X) μ := by
    have h : Integrable ((innerSL ℝ X) ∘ V) μ :=
      ContinuousLinearMap.integrable_comp (innerSL ℝ X) hV_int
    have h_eq : (fun ω => inner ℝ (V ω) X) = (innerSL ℝ X) ∘ V := by
      ext ω
      calc inner ℝ (V ω) X
          = inner ℝ X (V ω) := (real_inner_comm (V ω) X).symm
        _ = (innerSL ℝ X) (V ω) := by rw [innerSL_apply_apply ℝ X (V ω)]
        _ = ((innerSL ℝ X) ∘ V) ω := rfl
    rwa [h_eq]
  have h5 : Integrable (fun _ : Ω => ‖X‖ ^ 2) μ := by simp
  have h6 : ∫ ω, inner ℝ (V ω) X ∂μ = inner ℝ (∫ ω, V ω ∂μ) X := by
    calc ∫ ω, inner ℝ (V ω) X ∂μ
        = ∫ ω, inner ℝ X (V ω) ∂μ := by congr 1; ext ω; exact (real_inner_comm (V ω) X).symm
      _ = inner ℝ X (∫ ω, V ω ∂μ) := integral_inner hV_int X
      _ = inner ℝ (∫ ω, V ω ∂μ) X := (real_inner_comm X (∫ ω, V ω ∂μ)).symm
  have h7 : ∫ ω, (‖V ω‖ ^ 2 - 2 * inner ℝ (V ω) X + ‖X‖ ^ 2) ∂μ
      = (∫ ω, ‖V ω‖ ^ 2 ∂μ) - 2 * (∫ ω, inner ℝ (V ω) X ∂μ) + ‖X‖ ^ 2 := by
    rw [integral_add]
    · rw [integral_sub]
      · rw [integral_const_mul]
        rw [MeasureTheory.integral_const]
        all_goals simp
      · exact h3
      · exact h4.const_mul 2
    · exact h3.sub (h4.const_mul 2)
    · exact h5
  calc ∫ ω, ‖V ω - X‖ ^ 2 ∂μ
      = ∫ ω, (‖V ω‖ ^ 2 - 2 * inner ℝ (V ω) X + ‖X‖ ^ 2) ∂μ := h2
    _ = (∫ ω, ‖V ω‖ ^ 2 ∂μ) - 2 * (∫ ω, inner ℝ (V ω) X ∂μ) + ‖X‖ ^ 2 := h7
    _ = (∫ ω, ‖V ω‖ ^ 2 ∂μ) - ‖X‖ ^ 2 := by
      rw [h6, hmean]
      rw [real_inner_self_eq_norm_sq X]
      ring

/- Proof roadmap for `maureySampling`.

Informal proof:
1. Let `X := E[V]` and `Yᵢ := Vᵢ - X`.
2. Rewrite the target as `E[‖(1/k) • ∑ i, Yᵢ‖²]`.
3. Expand the square using the Hilbert inner product:
   `‖∑ i Yᵢ‖² = ∑ i ∑ j ⟪Yᵢ, Yⱼ⟫`.
4. Off-diagonal terms vanish by `integral_centered_inner_eq_zero`.
5. Each diagonal term equals `E[‖Vᵢ‖²] - ‖X‖²` by `integral_centered_norm_sq`.
6. Equality of laws (`hVi_map`) turns every `E[‖Vᵢ‖²]` into `E[‖V‖²]`.
7. Drop the nonnegative term `‖X‖²` to obtain the upper bound
   `E[‖X - (1/k) ∑ i Vᵢ‖²] ≤ E[‖V‖²] / k`.

Lean plan:
* prove the centered helper lemmas above;
* represent centered variables as named local definitions `Yᵢ := Vᵢ i - fun _ => X`
  rather than raw lambdas, so that `MemLp.sub` and `ProbabilityTheory.IndepFun.comp`
  match Mathlib's function expressions without extra coercion noise;
* expand the finite sum with `sum_inner` and `inner_sum`;
* use `Finset.sum_eq_zero` for the off-diagonal part;
* simplify the scalar factor via `(1 / k)^2 * k = 1 / k` using `hk : 0 < k`.
-/

/-- **Lemma 3.1** (Maurey; Pisier 1980).
In a Hilbert space H, if X = 𝔼[V] where V is supported on S, and (V₁, …, Vₖ) are
iid draws from the same distribution, then

  𝔼[‖X - (1/k) ∑ᵢ Vᵢ‖²] ≤ 𝔼[‖V‖²] / k  ≤  (sup_{U ∈ S} ‖U‖²) / k.

**Proof.** Expand ‖(1/k) ∑ᵢ (Vᵢ - X)‖². By iid and zero-mean:
  cross terms vanish, diagonal gives 𝔼[‖V - X‖²]/k ≤ 𝔼[‖V‖²]/k. -/
-- Pointwise norm identity for the centered representation in Maurey's lemma.
private lemma maurey_norm_algebra_rewrite {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    {k : ℕ} (hk : 0 < k) (X : H) (Vᵢ : Fin k → H) :
    ‖X - (1 / (k : ℝ)) • ∑ i, Vᵢ i‖ = ‖(1 / (k : ℝ)) • ∑ i, (Vᵢ i - X)‖ := by
  have h_alg : (1 / (k : ℝ)) • ∑ i, (Vᵢ i - X) = - (X - (1 / (k : ℝ)) • ∑ i, Vᵢ i) := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have step2 : (1 / (k:ℝ)) • (k • X) = X := by
      rw [← Nat.cast_smul_eq_nsmul ℝ k X]
      rw [← mul_smul]
      have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      rw [div_mul_cancel₀ 1 hk_ne]
      exact one_smul ℝ X
    rw [step2]
    abel
  rw [h_alg, norm_neg]

-- Final real algebra calculation for Maurey sampling.
private lemma maurey_final_algebraic_step (k : ℕ) (hk : 0 < k) (int_V2 : ℝ) (norm_X2 : ℝ)
    (hnX2 : 0 ≤ norm_X2) :
    (1 / (k : ℝ)) ^ 2 * ((k : ℝ) * (int_V2 - norm_X2)) ≤ int_V2 / (k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (k : ℝ) > 0 := by
      exact_mod_cast hk
    exact this.ne'
  have h_nonneg : (0 : ℝ) ≤ norm_X2 / (k : ℝ) := by
    have h_den : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.le
    exact div_nonneg hnX2 h_den
  have h_sub : (1 / (k : ℝ)) ^ 2 * ((k : ℝ) * (int_V2 - norm_X2)) =
    int_V2 / (k : ℝ) - norm_X2 / (k : ℝ) := by
    calc
      (1 / (k : ℝ)) ^ 2 * ((k : ℝ) * (int_V2 - norm_X2))
        = ((1 / (k : ℝ)) * (1 / (k : ℝ))) * ((k : ℝ) * (int_V2 - norm_X2)) := by ring
      _ = (1 / (k : ℝ)) * ((1 / (k : ℝ)) * (k : ℝ)) * (int_V2 - norm_X2) := by ring
      _ = (1 / (k : ℝ)) * 1 * (int_V2 - norm_X2) := by rw [one_div_mul_cancel hk0]
      _ = (1 / (k : ℝ)) * (int_V2 - norm_X2) := by ring
      _ = int_V2 / (k : ℝ) - norm_X2 / (k : ℝ) := by ring
  rw [h_sub]
  linarith

private lemma integral_norm_smul_sum_centered_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSub₂ H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {V : Ω → H} {Vᵢ : Fin k → Ω → H}
    (hV_L2 : MemLp V 2 μ)
    (hVi_L2 : ∀ i, MemLp (Vᵢ i) 2 μ)
    (hVi_mean : ∀ i, ∫ ω, Vᵢ i ω ∂μ = ∫ ω, V ω ∂μ)
    (hVi_indep : iIndepFun (m := fun _ => inferInstance) Vᵢ μ) :
    let X := ∫ ω, V ω ∂μ
    let Y : Fin k → Ω → H := fun i => Vᵢ i - fun _ => X
    ∫ ω, ‖(1 / k : ℝ) • ∑ i, Y i ω‖ ^ 2 ∂μ =
      (1 / k : ℝ) ^ 2 * ∑ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂μ := by
  intro X Y
  have hY_L2 : ∀ i, MemLp (Y i) 2 μ := fun i =>
    by simpa [Y, X] using (hVi_L2 i).sub (MeasureTheory.memLp_const X)
  -- Pull out scalar from norm
  rw [show (fun ω => ‖(1 / k : ℝ) • ∑ i, Y i ω‖ ^ 2) =
    fun ω => (1 / k : ℝ) ^ 2 * ‖∑ i, Y i ω‖ ^ 2 by
    ext ω
    rw [norm_smul, mul_pow]
    have : ‖(1 / k : ℝ)‖ ^ 2 = (1 / k : ℝ) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [this]]
  -- Pull out scalar from integral
  rw [integral_const_mul]
  -- Expand squared norm into sum of inner products
  rw [show (fun ω => ‖∑ i, Y i ω‖ ^ 2) = fun ω => ∑ i, ∑ j, @inner ℝ H _ (Y i ω) (Y j ω) by
    ext ω
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum]]
  -- Bring integral inside the double sum
  have h_integral_sum : ∫ (ω : Ω), (∑ i, ∑ j, @inner ℝ H _ (Y i ω) (Y j ω)) ∂μ =
    ∑ i, ∑ j, ∫ (ω : Ω), @inner ℝ H _ (Y i ω) (Y j ω) ∂μ := by
    rw [integral_finsetSum]
    · congr 1
      ext i
      rw [integral_finsetSum]
      intro j _
      have h_prod : Integrable (fun a => ‖Y i a‖ * ‖Y j a‖) μ := by
        exact (hY_L2 i).norm.integrable_mul (hY_L2 j).norm
      refine Integrable.mono h_prod ?_ ?_
      · exact AEStronglyMeasurable.inner (hY_L2 i).aestronglyMeasurable
          (hY_L2 j).aestronglyMeasurable
      · filter_upwards [] with a
        have h1 : ‖inner ℝ (Y i a) (Y j a)‖ ≤ ‖Y i a‖ * ‖Y j a‖ :=
          norm_inner_le_norm (Y i a) (Y j a)
        have h2 : ‖‖Y i a‖ * ‖Y j a‖‖ = ‖Y i a‖ * ‖Y j a‖ := by
          exact Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        rw [h2]
        exact h1
    · intro j _
      apply integrable_finsetSum
      intro k _
      have h_prod : Integrable (fun a => ‖Y j a‖ * ‖Y k a‖) μ := by
        exact (hY_L2 j).norm.integrable_mul (hY_L2 k).norm
      refine Integrable.mono h_prod ?_ ?_
      · exact AEStronglyMeasurable.inner (hY_L2 j).aestronglyMeasurable
          (hY_L2 k).aestronglyMeasurable
      · filter_upwards [] with a
        have h1 : ‖inner ℝ (Y j a) (Y k a)‖ ≤ ‖Y j a‖ * ‖Y k a‖ :=
          norm_inner_le_norm (Y j a) (Y k a)
        have h2 : ‖‖Y j a‖ * ‖Y k a‖‖ = ‖Y j a‖ * ‖Y k a‖ := by
          exact Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        rw [h2]
        exact h1
  rw [h_integral_sum]
  -- Cancel off-diagonal terms using integral_centered_inner_eq_zero
  have h_off_diag : ∑ i, ∑ j, ∫ (ω : Ω), @inner ℝ H _ (Y i ω) (Y j ω) ∂μ =
    ∑ i, ∫ (ω : Ω), @inner ℝ H _ (Y i ω) (Y i ω) ∂μ := by
    calc
      ∑ i, ∑ j, ∫ (ω : Ω), inner ℝ (Y i ω) (Y j ω) ∂μ =
        ∑ i, (∫ (ω : Ω), inner ℝ (Y i ω) (Y i ω) ∂μ +
          ∑ j ∈ Finset.univ.erase i, ∫ (ω : Ω), inner ℝ (Y i ω) (Y j ω) ∂μ) := by
        apply Finset.sum_congr rfl
        intro i _
        symm
        exact Finset.add_sum_erase Finset.univ (fun j ↦ ∫ (ω : Ω), inner ℝ (Y i ω) (Y j ω) ∂μ)
          (Finset.mem_univ i)
      _ = ∑ i, ∫ (ω : Ω), inner ℝ (Y i ω) (Y i ω) ∂μ := by
        rw [Finset.sum_add_distrib]
        rw [show ∑ i, ∑ j ∈ Finset.univ.erase i, ∫ (ω : Ω), inner ℝ (Y i ω) (Y j ω) ∂μ = 0 by
          apply Finset.sum_eq_zero
          intro i _
          apply Finset.sum_eq_zero
          intro j hj
          exact integral_centered_inner_eq_zero hV_L2 hVi_L2 hVi_mean hVi_indep
            (Finset.mem_erase.mp hj).1.symm, add_zero]
  rw [h_off_diag]
  -- Rewrite diagonal inner products back to squared norms
  rw [show ∑ i, ∫ (ω : Ω), @inner ℝ H _ (Y i ω) (Y i ω) ∂μ = ∑ i, ∫ (ω : Ω), ‖Y i ω‖ ^ 2 ∂μ by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext ω
    exact real_inner_self_eq_norm_sq (Y i ω)]

theorem maureySampling
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSub₂ H]
    {μ_prob : Measure Ω} [IsProbabilityMeasure μ_prob]
    {V : Ω → H}
    (hV_L2 : MemLp V 2 μ_prob)
    {k : ℕ} (hk : 0 < k)
    {Vᵢ : Fin k → Ω → H}
    (hVi_L2 : ∀ i, MemLp (Vᵢ i) 2 μ_prob)
    (hVi_mean : ∀ i, ∫ ω, Vᵢ i ω ∂μ_prob = ∫ ω, V ω ∂μ_prob)
    (hVi_indep : iIndepFun (m := fun _ => inferInstance) Vᵢ μ_prob)
    (hVi_map : ∀ i, Measure.map (Vᵢ i) μ_prob = Measure.map V μ_prob) :
    let X := ∫ ω, V ω ∂μ_prob
    ∫ ω, ‖X - (1 / k : ℝ) • ∑ i, Vᵢ i ω‖ ^ 2 ∂μ_prob ≤
      (∫ ω, ‖V ω‖ ^ 2 ∂μ_prob) / k := by
  intro X
  classical
  let Y : Fin k → Ω → H := fun i => Vᵢ i - fun _ => X
  /-
  Step 1: rewrite the target using the centered variables `Y i = Vᵢ i - X`.

  The algebra is:
    X - (1/k) • ∑ i Vᵢ i
      = -(1/k) • ∑ i (Vᵢ i - X)
      = -(1/k) • ∑ i Y i.
  Since the norm square is unchanged by negation, the left-hand side becomes
    E[‖(1/k) • ∑ i Yᵢ‖²].

  In Lean, this should be done by:
  * expanding `Y` and `X`;
  * using `Finset.smul_sum`, `smul_sub`, and `Finset.sum_const`;
  * simplifying `(∑ i, X) = k • X`;
  * using `norm_neg`.
  -/
  have hrewrite :
      ∫ ω, ‖X - (1 / k : ℝ) • ∑ i, Vᵢ i ω‖ ^ 2 ∂μ_prob =
        ∫ ω, ‖(1 / k : ℝ) • ∑ i, Y i ω‖ ^ 2 ∂μ_prob := by
    congr 1; ext ω; congr 1; exact maurey_norm_algebra_rewrite hk X (fun i => Vᵢ i ω)
  /-
  Step 2: expand the squared norm of the finite sum.

  For each `ω`,
    ‖∑ i Yᵢ ω‖² = ⟪∑ i Yᵢ ω, ∑ j Yⱼ ω⟫
                = ∑ i ∑ j ⟪Yᵢ ω, Yⱼ ω⟫.
  After multiplying by `(1/k)^2` and integrating, the off-diagonal terms
  (`i ≠ j`) vanish by `integral_centered_inner_eq_zero`.

  The intended Lean implementation is:
  * rewrite `‖z‖²` as `inner ℝ z z` using `real_inner_self_eq_norm_sq`;
  * expand with `sum_inner` and `inner_sum`;
  * use `MeasureTheory.integral_finset_sum` twice;
  * split the resulting double sum into diagonal and off-diagonal parts;
  * kill the off-diagonal part with `integral_centered_inner_eq_zero`.
  -/
  have hexpand :
      ∫ ω, ‖(1 / k : ℝ) • ∑ i, Y i ω‖ ^ 2 ∂μ_prob =
        (1 / k : ℝ) ^ 2 *
          ∑ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂μ_prob :=
    integral_norm_smul_sum_centered_eq hV_L2 hVi_L2 hVi_mean hVi_indep
  /-
  Step 3: compute each diagonal term.

  For every `i`,
    E[‖Yᵢ‖²] = E[‖Vᵢ - X‖²]
             = E[‖Vᵢ‖²] - ‖X‖²
  by `integral_centered_norm_sq`, since `E[Vᵢ] = X`.
  -/
  have hdiag :
      ∀ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂μ_prob =
        ∫ ω, ‖Vᵢ i ω‖ ^ 2 ∂μ_prob - ‖X‖ ^ 2 := fun i =>
    by simpa [Y, X] using integral_centered_norm_sq (hVi_L2 i) (hVi_mean i)
  /-
  Step 4: transport second moments from each `Vᵢ` back to `V` using equality of laws.

  Since `Measure.map (Vᵢ i) μ_prob = Measure.map V μ_prob`, we have
    E[‖Vᵢ i‖²] = E[‖V‖²].
  This is exactly `integral_norm_sq_eq_of_map_eq`.
  -/
  have hmoment :
      ∀ i, ∫ ω, ‖Vᵢ i ω‖ ^ 2 ∂μ_prob = ∫ ω, ‖V ω‖ ^ 2 ∂μ_prob := fun i =>
    integral_norm_sq_eq_of_map_eq (hVi_L2 i) hV_L2 (hVi_map i)
  /-
  Final algebraic collapse.

  Substituting `hdiag` and `hmoment` into `hexpand` yields
    E[‖(1/k) • ∑ i Yᵢ‖²]
      = (1/k)^2 * ∑ i (E[‖V‖²] - ‖X‖²)
      = (1/k)^2 * k * (E[‖V‖²] - ‖X‖²).
  Since `‖X‖² ≥ 0`, we may drop the subtractive term and obtain
    ≤ (1/k)^2 * k * E[‖V‖²] = E[‖V‖²] / k.

  The remaining Lean work is a finite-sum simplification plus the elementary real
  arithmetic identity `(1 / k : ℝ)^2 * k = 1 / k`, using `hk : 0 < k`.
  -/
  have hfinal :
      ∫ ω, ‖X - (1 / k : ℝ) • ∑ i, Vᵢ i ω‖ ^ 2 ∂μ_prob ≤
        (∫ ω, ‖V ω‖ ^ 2 ∂μ_prob) / k := by
    rw [hrewrite, hexpand]
    simp_rw [hdiag, hmoment]
    rw [show ∑ i : Fin k, (∫ (ω : Ω), ‖V ω‖ ^ 2 ∂μ_prob - ‖X‖ ^ 2) =
      (k : ℝ) * (∫ (ω : Ω), ‖V ω‖ ^ 2 ∂μ_prob - ‖X‖ ^ 2) by simp; ring]
    exact maurey_final_algebraic_step k hk (∫ (ω : Ω), ‖V ω‖ ^ 2 ∂μ_prob) (‖X‖ ^ 2) (sq_nonneg _)
  simpa [X] using hfinal

/-! ### The deterministic (existence) form of Maurey's lemma

The "moreover" clause of Lemma 3.1 says: *there exist* `(U₁, …, U_k)` in `S` with
`‖X - k⁻¹ ∑ᵢ Uᵢ‖² ≤ 𝔼‖X - k⁻¹ ∑ᵢ Vᵢ‖²`.  Telgarsky proves it by the probabilistic method.

We give two developments.

1. `maureySamplingExistence`, for `X ∈ convexHull ℝ S`.  Here the representing law is finitely
   supported, so *no measure theory is needed at all*: the whole statement follows from a single
   finite averaging step, iterated.  This is the Jones (1992) / Barron (1993) greedy argument, and
   it is the form used, e.g., for the matrix-sketching bound in §16 of the notes, where `S` is a
   finite set of rank-one matrices.

2. `maureySamplingExistence_of_iid`, for `X = ∫ V dμ` the Bochner mean of an `S`-valued random
   variable.  This is the form Barron's theorem needs (the representing measure there is
   absolutely continuous, so `X` need not be a *finite* convex combination of points of `S`), and
   it is obtained from `maureySampling` by `MeasureTheory.exists_le_integral`.

Both are strictly stronger than a `closure (convexHull ℝ S)` statement would be — see the
counterexample recorded on `maureySamplingExistence`.
-/

section Maurey

variable {ι : Type*} {t : Finset ι} {w : ι → ℝ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Weighted first-moment method.**  If `w` is a probability vector on a finite index set `t`
and the `w`-average of `a` is at most `c`, then `a i ≤ c` for some `i ∈ t`.

This is the elementary, finitely-supported counterpart of `MeasureTheory.exists_le_integral`;
it is the only "probabilistic" ingredient of the greedy proof of Maurey's lemma. -/
theorem exists_le_of_weighted_sum_le {a : ι → ℝ} {c : ℝ}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1)
    (h : ∑ i ∈ t, w i * a i ≤ c) : ∃ i ∈ t, a i ≤ c := by
  by_contra hcon
  push Not at hcon
  -- The weights sum to `1`, so at least one of them is strictly positive.
  obtain ⟨j, hjt, hj⟩ : ∃ j ∈ t, 0 < w j := by
    by_contra hall
    push Not at hall
    have := Finset.sum_nonpos hall
    rw [hw₁] at this
    linarith
  have hlt : ∑ i ∈ t, w i * c < ∑ i ∈ t, w i * a i :=
    Finset.sum_lt_sum (fun i hi => mul_le_mul_of_nonneg_left (hcon i hi).le (hw₀ i hi))
      ⟨j, hjt, mul_lt_mul_of_pos_left (hcon j hjt) hj⟩
  rw [← Finset.sum_mul, hw₁, one_mul] at hlt
  linarith

/-- The `w`-average of `⟪g, X - zᵢ⟫` vanishes when `X` is the `w`-barycentre of the `zᵢ`.

This is the statement that the centred variable `V - 𝔼 V` has mean zero, and it is what makes
the linear term of the greedy step free of charge. -/
theorem sum_weight_inner_barycenter_sub_eq_zero {z : ι → H} {X : H}
    (hw₁ : ∑ i ∈ t, w i = 1) (hX : X = ∑ i ∈ t, w i • z i) (g : H) :
    ∑ i ∈ t, w i * inner ℝ g (X - z i) = 0 := by
  calc ∑ i ∈ t, w i * inner ℝ g (X - z i)
      = ∑ i ∈ t, (w i * inner ℝ g X - inner ℝ g (w i • z i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_sub_right, real_inner_smul_right]
        ring
    _ = (∑ i ∈ t, w i) * inner ℝ g X - inner ℝ g (∑ i ∈ t, w i • z i) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← inner_sum]
    _ = 0 := by rw [hw₁, ← hX, one_mul, sub_self]

/-- **Bias–variance (parallel axis) identity.**  If `X` is the `w`-barycentre of the `zᵢ`, then

  `∑ᵢ wᵢ ‖zᵢ - X‖² = ∑ᵢ wᵢ ‖zᵢ‖² - ‖X‖²`,

i.e. `𝔼‖V - 𝔼 V‖² = 𝔼‖V‖² - ‖𝔼 V‖²`, for a finitely supported law `w`. -/
theorem sum_weight_norm_sub_barycenter_sq {z : ι → H} {X : H}
    (hw₁ : ∑ i ∈ t, w i = 1) (hX : X = ∑ i ∈ t, w i • z i) :
    ∑ i ∈ t, w i * ‖z i - X‖ ^ 2 = (∑ i ∈ t, w i * ‖z i‖ ^ 2) - ‖X‖ ^ 2 := by
  have hinner : ∑ i ∈ t, w i * inner ℝ (z i) X = ‖X‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 2 [hX]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => (real_inner_smul_left _ _ _).symm
  calc ∑ i ∈ t, w i * ‖z i - X‖ ^ 2
      = ∑ i ∈ t, (w i * ‖z i‖ ^ 2 - 2 * (w i * inner ℝ (z i) X) + w i * ‖X‖ ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_sub_sq_real]
        ring
    _ = (∑ i ∈ t, w i * ‖z i‖ ^ 2) - 2 * (∑ i ∈ t, w i * inner ℝ (z i) X)
          + (∑ i ∈ t, w i) * ‖X‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = (∑ i ∈ t, w i * ‖z i‖ ^ 2) - ‖X‖ ^ 2 := by rw [hinner, hw₁]; ring

/-- **Maurey's greedy step.**  Let `X` lie in the convex hull of `S`, with `‖u‖ ^ 2 ≤ B` on `S`,
and let `g : H` be arbitrary (in the application, `g` is the current approximation error).  Then
there is a *single* `u ∈ S` which simultaneously controls the linear and the quadratic term:

  `2 ⟪g, X - u⟫ + ‖X - u‖ ^ 2 ≤ B - ‖X‖ ^ 2`.

**Proof.**  Write `X = ∑ᵢ wᵢ zᵢ` as a finite convex combination of points `zᵢ ∈ S`.  The
`w`-average of the left-hand side is
  `2 · 0 + (∑ᵢ wᵢ‖zᵢ‖² - ‖X‖²) ≤ B - ‖X‖²`
by `sum_weight_inner_barycenter_sub_eq_zero` and `sum_weight_norm_sub_barycenter_sq`; now apply
`exists_le_of_weighted_sum_le`.

This one lemma is the entire content of Maurey's lemma: iterating it `k` times gives the
`O(1/k)` rate, because the linear term absorbs exactly the accumulated error. -/
theorem exists_mem_maurey_step {S : Set H} {X : H} (hX : X ∈ convexHull ℝ S)
    {B : ℝ} (hB : ∀ u ∈ S, ‖u‖ ^ 2 ≤ B) (g : H) :
    ∃ u ∈ S, 2 * inner ℝ g (X - u) + ‖X - u‖ ^ 2 ≤ B - ‖X‖ ^ 2 := by
  rw [convexHull_eq] at hX
  obtain ⟨ι', t, w, z, hw₀, hw₁, hz, hcm⟩ := hX
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁] at hcm
  have hXeq : X = ∑ i ∈ t, w i • z i := hcm.symm
  have key : ∑ i ∈ t, w i * (2 * inner ℝ g (X - z i) + ‖X - z i‖ ^ 2) ≤ B - ‖X‖ ^ 2 := by
    have hsplit : ∑ i ∈ t, w i * (2 * inner ℝ g (X - z i) + ‖X - z i‖ ^ 2)
        = 2 * (∑ i ∈ t, w i * inner ℝ g (X - z i)) + ∑ i ∈ t, w i * ‖z i - X‖ ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_sub_rev]
      ring
    rw [hsplit, sum_weight_inner_barycenter_sub_eq_zero hw₁ hXeq g,
      sum_weight_norm_sub_barycenter_sq hw₁ hXeq]
    have hmoment : ∑ i ∈ t, w i * ‖z i‖ ^ 2 ≤ B := by
      calc ∑ i ∈ t, w i * ‖z i‖ ^ 2
          ≤ ∑ i ∈ t, w i * B :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hB _ (hz i hi)) (hw₀ i hi)
        _ = B := by rw [← Finset.sum_mul, hw₁, one_mul]
    linarith
  obtain ⟨i, hit, hi⟩ := exists_le_of_weighted_sum_le hw₀ hw₁ key
  exact ⟨z i, hz i hit, hi⟩

/-- Maurey's lemma in *unnormalised* form: there are `u₁, …, u_k ∈ S` with

  `‖k • X - ∑ᵢ uᵢ‖² ≤ k (B - ‖X‖²)`.

Stated this way it is division-free and holds for every `k : ℕ`, including `k = 0`, which makes
it a clean target for induction.  `maureySamplingExistence` is the normalised corollary.

**Proof.**  Induction on `k`.  For `k = 0` both sides are `0`.  For the step, let
`g := k • X - ∑ᵢ≤k uᵢ` be the current (unnormalised) error and pick `v ∈ S` from
`exists_mem_maurey_step` applied to this `g`.  Then

  `‖(k+1) • X - (∑ᵢ uᵢ + v)‖² = ‖g + (X - v)‖²`
      `= ‖g‖² + 2⟪g, X - v⟫ + ‖X - v‖²`
      `≤ k (B - ‖X‖²) + (B - ‖X‖²) = (k+1)(B - ‖X‖²)`,

the inequality being the induction hypothesis plus the greedy step.  Note how the cross term
`2⟪g, X - v⟫` — which is exactly the term that vanishes *in expectation* in the probabilistic
proof — is here absorbed by the greedy choice of `v`. -/
theorem exists_mem_norm_nsmul_sub_sum_sq_le {S : Set H} {X : H} (hX : X ∈ convexHull ℝ S)
    {B : ℝ} (hB : ∀ u ∈ S, ‖u‖ ^ 2 ≤ B) (k : ℕ) :
    ∃ u : Fin k → H, (∀ i, u i ∈ S) ∧
      ‖(k : ℝ) • X - ∑ i, u i‖ ^ 2 ≤ k * (B - ‖X‖ ^ 2) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩
  | succ k ih =>
      obtain ⟨u, hu, hbound⟩ := ih
      obtain ⟨v, hv, hstep⟩ :=
        exists_mem_maurey_step hX hB ((k : ℝ) • X - ∑ i, u i)
      refine ⟨Fin.snoc u v, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hv
        | cast i => simpa using hu i
      · have hsum : ∑ i, (Fin.snoc u v : Fin (k + 1) → H) i = (∑ i, u i) + v := by
          rw [Fin.sum_univ_castSucc]
          simp
        have hsplit : ((k : ℕ) + 1 : ℝ) • X - ∑ i, (Fin.snoc u v : Fin (k + 1) → H) i
            = ((k : ℝ) • X - ∑ i, u i) + (X - v) := by
          rw [hsum, add_smul, one_smul]
          abel
        rw [Nat.cast_succ, hsplit, norm_add_sq_real]
        linarith
end Maurey

section MaureyExistence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Lemma 3.1, existence form** (Maurey; Pisier 1980).
If `X` lies in the convex hull of `S` and `‖u‖ ^ 2 ≤ B` for every `u ∈ S`, then for every `k ≥ 1`
there exist `u₁, …, u_k ∈ S` with

  `‖X - (1/k) ∑ᵢ uᵢ‖² ≤ (B - ‖X‖²) / k ≤ B / k`.

The bound `(B - ‖X‖²)/k` is the sharp one produced by the proof (it is `𝔼‖V - X‖²/k`, cf. the
computation in the notes); `‖X‖² ≥ 0` gives the advertised `B/k`.

**Warning (do not weaken `convexHull` to `closure (convexHull …)`).**  The statement becomes
*false*.  In `ℓ²` with orthonormal basis `(eₙ)`, put `vₙ := (1/n) • e₀ + √(1 - 1/n²) • eₙ` for
`n ≥ 1` and `S := {vₙ}`.  Every `‖vₙ‖ = 1`, so `B = 1` is optimal.  The averages
`m⁻¹ ∑_{n ≤ m} vₙ` have squared norm `m⁻²(m + O(log² m)) → 0`, so `0 ∈ closure (convexHull ℝ S)`.
Yet `⟪vₙ, vₘ⟫ = 1/(nm) > 0` for all `n, m`, so for `k = 2` *every* choice gives
`‖2⁻¹(vₙ + vₘ)‖² = 1/2 + 1/(2nm) > 1/2 = B/k`.  (What is true for the closure is the same bound
with an arbitrary `ε > 0` slack, or the exact bound when `X` is a genuine Bochner mean of an
`S`-valued random variable — see `maureySamplingExistence_of_iid`.) -/
theorem maureySamplingExistence {S : Set H} {X : H} (hX : X ∈ convexHull ℝ S)
    {B : ℝ} (hB : ∀ u ∈ S, ‖u‖ ^ 2 ≤ B) {k : ℕ} (hk : 0 < k) :
    ∃ u : Fin k → H, (∀ i, u i ∈ S) ∧
      ‖X - (1 / k : ℝ) • ∑ i, u i‖ ^ 2 ≤ (B - ‖X‖ ^ 2) / k := by
  obtain ⟨u, hu, hbound⟩ := exists_mem_norm_nsmul_sub_sum_sq_le hX hB k
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  refine ⟨u, hu, ?_⟩
  have hfactor : X - (1 / k : ℝ) • ∑ i, u i = (1 / k : ℝ) • ((k : ℝ) • X - ∑ i, u i) := by
    rw [smul_sub, smul_smul, one_div, inv_mul_cancel₀ hkpos.ne', one_smul]
  rw [hfactor, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow, one_pow,
    div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hkpos]
  nlinarith [mul_le_mul_of_nonneg_right hbound hkpos.le, hkpos]

/-- The version of `maureySamplingExistence` advertised in the notes: the bound is `B / k` with
`B = sup_{u ∈ S} ‖u‖²`. -/
theorem maureySamplingExistence_le_div {S : Set H} {X : H} (hX : X ∈ convexHull ℝ S)
    {B : ℝ} (hB : ∀ u ∈ S, ‖u‖ ^ 2 ≤ B) {k : ℕ} (hk : 0 < k) :
    ∃ u : Fin k → H, (∀ i, u i ∈ S) ∧ ‖X - (1 / k : ℝ) • ∑ i, u i‖ ^ 2 ≤ B / k := by
  obtain ⟨u, hu, hbound⟩ := maureySamplingExistence hX hB hk
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  refine ⟨u, hu, hbound.trans ?_⟩
  rw [div_le_div_iff₀ hkpos hkpos]
  nlinarith [sq_nonneg ‖X‖, hkpos]

omit [InnerProductSpace ℝ H] in
/-- `‖u‖ ^ 2 ≤ ⨆ v ∈ S, ‖v‖ ^ 2` for `u ∈ S`, provided the squared norms on `S` are bounded above.

The `BddAbove` hypothesis is genuinely needed: `Real.sSup` of a set unbounded above is the junk
value `0`. -/
theorem norm_sq_le_biSup {S : Set H} (hbdd : BddAbove ((fun u => ‖u‖ ^ 2) '' S))
    {u : H} (hu : u ∈ S) : ‖u‖ ^ 2 ≤ ⨆ v ∈ S, ‖v‖ ^ 2 := by
  obtain ⟨b, hb⟩ := hbdd
  have hbdd' : BddAbove (Set.range fun v : H => ⨆ _ : v ∈ S, ‖v‖ ^ 2) := by
    refine ⟨max b 0, ?_⟩
    rintro x ⟨v, rfl⟩
    dsimp only
    by_cases hv : v ∈ S
    · rw [ciSup_pos (f := fun _ : v ∈ S => ‖v‖ ^ 2) hv]
      exact le_max_of_le_left (hb ⟨v, hv, rfl⟩)
    · haveI : IsEmpty (v ∈ S) := ⟨hv⟩
      rw [Real.iSup_of_isEmpty (f := fun _ : v ∈ S => ‖v‖ ^ 2)]
      exact le_max_right _ _
  calc ‖u‖ ^ 2 = ⨆ _ : u ∈ S, ‖u‖ ^ 2 := (ciSup_pos (f := fun _ : u ∈ S => ‖u‖ ^ 2) hu).symm
    _ ≤ ⨆ v, ⨆ _ : v ∈ S, ‖v‖ ^ 2 := le_ciSup hbdd' u

/-- **Lemma 3.1, existence form, with the supremum spelled out** — the literal statement of the
"moreover" clause of Lemma 3.1 in Telgarsky's notes, for `X ∈ convexHull ℝ S`. -/
theorem maureySamplingExistence_iSup {S : Set H} {X : H} (hX : X ∈ convexHull ℝ S)
    (hbdd : BddAbove ((fun u => ‖u‖ ^ 2) '' S)) {k : ℕ} (hk : 0 < k) :
    ∃ u : Fin k → H, (∀ i, u i ∈ S) ∧
      ‖X - (1 / k : ℝ) • ∑ i, u i‖ ^ 2 ≤ (⨆ u ∈ S, ‖u‖ ^ 2) / k :=
  maureySamplingExistence_le_div hX (fun _ hu => norm_sq_le_biSup hbdd hu) hk

/-- **Lemma 3.1, existence form, for a Bochner mean.**
This is the form used by Barron's theorem: `X = 𝔼 V` where `V` is an `S`-valued random variable
whose law need not be finitely supported (so `X` need not lie in `convexHull ℝ S`, only in its
closure).  Here the probabilistic method really is needed, and it is exactly
`MeasureTheory.exists_le_integral`: an integrable function is `≤` its own mean somewhere.

**Proof.**  `maureySampling` bounds `𝔼‖X - k⁻¹ ∑ᵢ Vᵢ‖²` by `𝔼‖V‖² / k`.  The integrand is
integrable (it is `‖F‖²` for `F ∈ L²`), so some sample point `ω₀` realises a value at most the
mean; take `uᵢ := Vᵢ(ω₀)`, which lies in `S` by `hVi_mem`. -/
theorem maureySamplingExistence_of_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [MeasurableSub₂ H]
    {μ_prob : Measure Ω} [IsProbabilityMeasure μ_prob]
    {S : Set H} {V : Ω → H} (hV_L2 : MemLp V 2 μ_prob)
    {k : ℕ} (hk : 0 < k)
    {Vᵢ : Fin k → Ω → H}
    (hVi_mem : ∀ i ω, Vᵢ i ω ∈ S)
    (hVi_L2 : ∀ i, MemLp (Vᵢ i) 2 μ_prob)
    (hVi_mean : ∀ i, ∫ ω, Vᵢ i ω ∂μ_prob = ∫ ω, V ω ∂μ_prob)
    (hVi_indep : iIndepFun (m := fun _ => inferInstance) Vᵢ μ_prob)
    (hVi_map : ∀ i, Measure.map (Vᵢ i) μ_prob = Measure.map V μ_prob) :
    ∃ u : Fin k → H, (∀ i, u i ∈ S) ∧
      ‖(∫ ω, V ω ∂μ_prob) - (1 / k : ℝ) • ∑ i, u i‖ ^ 2 ≤ (∫ ω, ‖V ω‖ ^ 2 ∂μ_prob) / k := by
  set X : H := ∫ ω, V ω ∂μ_prob with hXdef
  -- The error process `ω ↦ X - k⁻¹ ∑ᵢ Vᵢ ω` lies in `L²`, hence its squared norm is integrable.
  have hF_L2 : MemLp (fun ω => X - (1 / k : ℝ) • ∑ i, Vᵢ i ω) 2 μ_prob := by
    have hsum : MemLp (fun ω => ∑ i, Vᵢ i ω) 2 μ_prob := by
      have hfun : (fun ω => ∑ i, Vᵢ i ω) = ∑ i, Vᵢ i := by ext ω; simp
      rw [hfun]
      exact memLp_finsetSum' Finset.univ fun i _ => hVi_L2 i
    exact (MeasureTheory.memLp_const X).sub (hsum.const_smul _)
  have hint : Integrable (fun ω => ‖X - (1 / k : ℝ) • ∑ i, Vᵢ i ω‖ ^ 2) μ_prob :=
    (memLp_two_iff_integrable_sq_norm hF_L2.aestronglyMeasurable).mp hF_L2
  obtain ⟨ω₀, hω₀⟩ := MeasureTheory.exists_le_integral hint
  exact ⟨fun i => Vᵢ i ω₀, fun i => hVi_mem i ω₀,
    hω₀.trans (maureySampling hV_L2 hk hVi_L2 hVi_mean hVi_indep hVi_map)⟩

end MaureyExistence

/-! ### Maurey in `L₂(P)`, stated with integrals

Issue 1 of the notes: "what is the appropriate Hilbert space?  We'll use `⟪f, g⟫ = ∫ f g dP`."

Formally one could take `H := MeasureTheory.Lp ℝ 2 P` and feed it to `maureySampling`.  We
deliberately do *not*: `Lp` elements are a.e.-equivalence classes, and turning a family
`F : Ω_w → Ω_x → ℝ` into a *measurable* map `Ω_w → Lp ℝ 2 P` is a substantial amount of
bookkeeping that contributes nothing mathematically.

Instead we state Maurey's lemma for `L₂(P)` directly in terms of integrals.  Fubini reduces the
whole statement to the *scalar* variance-of-the-sample-mean identity, applied separately at each
`x`, which is much cheaper: for fixed `x` the samples `F(wᵢ)(x)` are iid reals with mean `f x`.
-/

section L2Maurey

variable {Ω_w : Type*} [MeasurableSpace Ω_w] {Ω_x : Type*} [MeasurableSpace Ω_x]

lemma iid_pi (ν : Measure Ω_w) [IsProbabilityMeasure ν]
    {k : ℕ} {H : Type*} [MeasurableSpace H] (V : Ω_w → H) (hV : Measurable V) :
    let Vᵢ := fun (i : Fin k) (ω : Fin k → Ω_w) => V (ω i)
    iIndepFun (m := fun _ => inferInstance) Vᵢ (Measure.pi fun _ => ν) ∧
    ∀ i, Measure.map (Vᵢ i) (Measure.pi fun _ => ν) = Measure.map V ν := by
  intro Vᵢ
  constructor
  · have h_meas : ∀ i : Fin k, Measurable (fun (ω : Ω_w) => ω) := fun _ => measurable_id
    have h_aemeas : ∀ i : Fin k, AEMeasurable (fun (ω : Ω_w) => ω) ν :=
      fun i => (h_meas i).aemeasurable
    have h_indep := iIndepFun_pi (μ := fun _ : Fin k => ν) (X := fun i ω => ω) h_aemeas
    have h_comp := iIndepFun.comp h_indep (fun _ => V) (fun _ => hV)
    exact h_comp
  · intro i
    have h : Vᵢ i = V ∘ (fun ω => ω i) := rfl
    rw [h, ← Measure.map_map hV (measurable_pi_apply i), Measure.pi_map_eval]
    simp [measure_univ, one_smul]


/-- **Maurey's lemma in `L₂(P)`, existence form.**
Let `ν` be a probability measure on a parameter space `Ω_w`, let `P` be a probability measure on
`Ω_x`, let `F w : Ω_x → ℝ` be an `L₂(P)` "atom" for each `w`, and suppose `f` is the mean of the
atoms, `f x = ∫ F w x dν(w)`.  If every atom has `L₂(P)` energy at most `C`, then for each `k ≥ 1`
there are `k` parameters `w₁, …, w_k`, all avoiding a prescribed `ν`-null set `N`, with

  `‖f - k⁻¹ ∑ᵢ F(wᵢ)‖²_{L₂(P)} ≤ C / k`.

**Informal proof.**  Work on the product space `Ω_w^k` with the product measure `ν^k`; write
`ω = (w₁, …, w_k)`.
1. *Fubini.*
     `𝔼_ω ∫_x (f x - k⁻¹ ∑ᵢ F(ωᵢ)(x))² dP(x) = ∫_x 𝔼_ω (f x - k⁻¹ ∑ᵢ F(ωᵢ)(x))² dP(x)`.
   The integrand is nonnegative and jointly measurable, so `MeasureTheory.integral_integral_swap`
   applies once integrability is known (it follows from the `L²` bound `hC`).
2. *Scalar Maurey, pointwise in `x`.*  Fix `x`.  Under `ν^k` the reals `Yᵢ := F(ωᵢ)(x)` are iid
   with mean `f x`, so the classical variance-of-the-sample-mean identity gives
     `𝔼_ω (f x - k⁻¹ ∑ᵢ Yᵢ)² = k⁻¹ (𝔼 Y² - (f x)²) ≤ k⁻¹ 𝔼_w F(w)(x)²`.
   This is `maureySampling` specialized to the one-dimensional Hilbert space `H := ℝ`, with
   `V := fun w => F w x` and `Vᵢ := fun ω => F (ω i) x`; the coordinate maps on a product measure
   are iid (`ProbabilityTheory.iIndepFun` for `Measure.pi`, plus `Measure.map_eval_pi`).
3. *Fubini again, and the energy bound.*
     `∫_x k⁻¹ ∫_w F(w)(x)² dν dP = k⁻¹ ∫_w (∫_x F(w)(x)² dP) dν ≤ k⁻¹ ∫_w C dν = C / k`,
   using `hC` and `ν` a probability measure.
4. *Probabilistic method, avoiding a null set.*  The map
     `ω ↦ ∫_x (f x - k⁻¹ ∑ᵢ F(ωᵢ)(x))² dP(x)`
   is `ν^k`-integrable, and the set `Ñ := ⋃ᵢ {ω | ωᵢ ∈ N}` is `ν^k`-null (finite union of null
   sets).  `MeasureTheory.exists_notMem_null_le_integral` then produces `ω ∉ Ñ` whose value is at
   most the mean, i.e. at most `C / k`.  Take `wᵢ := ωᵢ`; these avoid `N` by construction.

**Missing infrastructure.**  The only genuinely new ingredient is step 2's "coordinates of a
product measure are iid".  Mathlib has `MeasureTheory.Measure.pi`, `Measure.pi_pi`, and
`ProbabilityTheory.iIndepFun_pi`; wiring those into the hypotheses of `maureySampling` is the
main task, and is worth extracting as its own lemma
(`iid coordinates on `Measure.pi` satisfy `hVi_indep`, `hVi_mean`, `hVi_map``), since
`maureySamplingExistence_of_iid` currently takes those four hypotheses on faith. -/
private lemma memLp_pi_eval {Ω_w : Type*} [MeasurableSpace Ω_w] {ν : Measure Ω_w}
    [IsProbabilityMeasure ν]
    {k : ℕ} (i : Fin k) {g : Ω_w → ℝ} (hg : MemLp g 2 ν) :
    MemLp (fun ω : Fin k → Ω_w => g (ω i)) 2 (Measure.pi (fun _ : Fin k => ν)) := by
  have : (fun ω : Fin k → Ω_w => g (ω i)) = g ∘ (fun ω => ω i) := rfl
  rw [this]
  have hmap_i : Measure.map (fun ω : Fin k → Ω_w => ω i) (Measure.pi (fun _ : Fin k => ν)) =
    ν := by
    have h_eval : (fun ω : Fin k → Ω_w => ω i) = Function.eval i := rfl
    rw [h_eval, Measure.pi_map_eval]
    simp
  have hg_meas : AEStronglyMeasurable g (Measure.map (fun ω : Fin k → Ω_w => ω i)
        (Measure.pi (fun _ : Fin k => ν))) := by
    rw [hmap_i]
    exact hg.1
  have h_meas_map : AEMeasurable (fun ω : Fin k → Ω_w => ω i) (Measure.pi (fun _ : Fin k => ν)) :=
        (measurable_pi_apply i).aemeasurable
  have h_mem : MemLp g 2 (Measure.map (fun ω => ω i) (Measure.pi (fun _ : Fin k => ν))) := by
    rw [hmap_i]
    exact hg
  exact (memLp_map_measure_iff hg_meas h_meas_map).mp h_mem

private lemma integral_pi_eval {Ω_w : Type*} [MeasurableSpace Ω_w] {ν : Measure Ω_w}
    [IsProbabilityMeasure ν]
    {k : ℕ} (i : Fin k) {g : Ω_w → ℝ} (hg : AEStronglyMeasurable g ν) :
    ∫ ω : Fin k → Ω_w, g (ω i) ∂(Measure.pi (fun _ : Fin k => ν)) = ∫ w, g w ∂ν := by
  have hmap_i : Measure.map (fun ω : Fin k → Ω_w => ω i) (Measure.pi (fun _ : Fin k => ν)) =
    ν := by
    have h_eval : (fun ω : Fin k → Ω_w => ω i) = Function.eval i := rfl
    rw [h_eval, Measure.pi_map_eval]
    simp
  have hg_meas : AEStronglyMeasurable g (Measure.map (fun ω : Fin k → Ω_w => ω i)
        (Measure.pi (fun _ : Fin k => ν))) := by
    rw [hmap_i]
    exact hg
  change ∫ ω, g (ω i) ∂(Measure.pi (fun _ : Fin k => ν)) = ∫ w, g w ∂ν
  rw [← integral_map (measurable_pi_apply i : Measurable (fun ω : Fin k → Ω_w => ω i)).aemeasurable
        hg_meas]
  rw [hmap_i]

private lemma map_pi_eval_eq {Ω_w : Type*} [MeasurableSpace Ω_w] {ν : Measure Ω_w}
    [IsProbabilityMeasure ν]
    {k : ℕ} (i j : Fin k) {g : Ω_w → ℝ} (hg : Measurable g) :
    Measure.map (fun ω : Fin k → Ω_w => g (ω i)) (Measure.pi (fun _ : Fin k => ν)) =
    Measure.map (fun ω : Fin k → Ω_w => g (ω j)) (Measure.pi (fun _ : Fin k => ν)) := by
  have hi : (fun ω : Fin k → Ω_w => g (ω i)) = g ∘ (fun ω => ω i) := rfl
  have hj : (fun ω : Fin k → Ω_w => g (ω j)) = g ∘ (fun ω => ω j) := rfl
  rw [hi, hj]
  have hmap_i : Measure.map (fun ω : Fin k → Ω_w => ω i) (Measure.pi (fun _ : Fin k => ν)) =
    ν := by
    have h_eval : (fun ω : Fin k → Ω_w => ω i) = Function.eval i := rfl
    rw [h_eval, Measure.pi_map_eval]
    simp
  have hmap_j : Measure.map (fun ω : Fin k → Ω_w => ω j) (Measure.pi (fun _ : Fin k => ν)) =
    ν := by
    have h_eval : (fun ω : Fin k → Ω_w => ω j) = Function.eval j := rfl
    rw [h_eval, Measure.pi_map_eval]
    simp
  rw [← Measure.map_map hg (measurable_pi_apply i : Measurable (fun ω : Fin k → Ω_w => ω i))]
  rw [← Measure.map_map hg (measurable_pi_apply j : Measurable (fun ω : Fin k → Ω_w => ω j))]
  rw [hmap_i, hmap_j]

private lemma memLp_uncurry_and_ae_memLp {Ω_w Ω_x : Type*} [MeasurableSpace Ω_w]
    [MeasurableSpace Ω_x]
    (ν : Measure Ω_w) [IsProbabilityMeasure ν] (P : Measure Ω_x) [IsProbabilityMeasure P]
    (F : Ω_w → Ω_x → ℝ)
    (hF_meas : Measurable (Function.uncurry F))
    (hF_L2 : ∀ w, MemLp (F w) 2 P)
    {C : ℝ} (hC : ∀ᵐ w ∂ν, ∫ x, F w x ^ 2 ∂P ≤ C) :
    MemLp (Function.uncurry F) 2 (ν.prod P) ∧
    (∫⁻ x, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν ∂P ≤ ENNReal.ofReal C) ∧
    (∀ᵐ x ∂P, MemLp (fun w => F w x) 2 ν) := by
  have hF2_int (w : Ω_w) : Integrable (fun x => F w x ^ 2) P :=
    (memLp_two_iff_integrable_sq (hF_L2 w).1).mp (hF_L2 w)
  have hF2_lintegral (w : Ω_w) : ∫⁻ x, ENNReal.ofReal (F w x ^ 2) ∂P =
    ENNReal.ofReal (∫ x, F w x ^ 2 ∂P) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hF2_int w)
        (ae_of_all P (fun x => sq_nonneg (F w x)))]
  have hC_ofReal : ∀ᵐ w ∂ν, ENNReal.ofReal (∫ x, F w x ^ 2 ∂P) ≤ ENNReal.ofReal C := by
    filter_upwards [hC] with w hw using ENNReal.ofReal_le_ofReal hw
  have hF_uncurry_L2 : MemLp (Function.uncurry F) 2 (ν.prod P) := by
    constructor
    · exact hF_meas.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      have h_enorm : (fun p : Ω_w × Ω_x => enorm (Function.uncurry F p) ^ ENNReal.toReal 2) =
        fun p => ENNReal.ofReal (F p.1 p.2 ^ 2) := by
        ext ⟨w, x⟩
        dsimp [Function.uncurry]
        rw [enorm_eq_ofReal_abs]
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg]
        congr 1
        have h2 : ENNReal.toReal 2 = 2 := rfl
        rw [h2, Real.rpow_two, sq_abs]
      rw [h_enorm]
      rw [lintegral_prod _ (by fun_prop)]
      simp_rw [hF2_lintegral]
      have h_le := lintegral_mono_ae hC_ofReal
      refine h_le.trans_lt ?_
      simp [measure_univ]
  have hF_sec_meas (x : Ω_x) : Measurable (fun w => F w x) := by
    have : (fun w => F w x) = (Function.uncurry F) ∘ (fun w => (w, x)) := rfl
    rw [this]
    exact hF_meas.comp (Measurable.prodMk measurable_id measurable_const)
  have h_swap : ∫⁻ x, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν ∂P =
    ∫⁻ w, ∫⁻ x, ENNReal.ofReal (F w x ^ 2) ∂P ∂ν := by
    exact lintegral_lintegral_swap (by fun_prop : AEMeasurable
        (fun p : Ω_x × Ω_w => ENNReal.ofReal (F p.2 p.1 ^ 2)) (P.prod ν))
  have h_swap_le : ∫⁻ x, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν ∂P ≤ ENNReal.ofReal C := by
    rw [h_swap]
    simp_rw [hF2_lintegral]
    have h_le := lintegral_mono_ae hC_ofReal
    refine h_le.trans ?_
    simp [measure_univ]
  have h_ae_L2 : ∀ᵐ x ∂P, MemLp (fun w => F w x) 2 ν := by
    have h_lt : (∫⁻ x, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν ∂P) < ⊤ := h_swap_le.trans_lt (by simp)
    have h_ae_lt : ∀ᵐ x ∂P, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν < ⊤ := by
      exact ae_lt_top (by fun_prop) h_lt.ne
    filter_upwards [h_ae_lt] with x hx
    constructor
    · exact (hF_sec_meas x).aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      have h_enorm : (fun w => enorm (F w x) ^ ENNReal.toReal 2) =
        fun w => ENNReal.ofReal (F w x ^ 2) := by
        ext w
        rw [enorm_eq_ofReal_abs]
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg]
        congr 1
        have h2 : ENNReal.toReal 2 = 2 := rfl
        rw [h2, Real.rpow_two, sq_abs]
      rw [h_enorm]
      exact hx
  exact ⟨hF_uncurry_L2, h_swap_le, h_ae_L2⟩

lemma L2_mean_of_L2 {Ω_w Ω_x : Type*} [MeasurableSpace Ω_w] [MeasurableSpace Ω_x]
    (ν : Measure Ω_w) [IsProbabilityMeasure ν] (P : Measure Ω_x) [IsProbabilityMeasure P]
    (F : Ω_w → Ω_x → ℝ) (f : Ω_x → ℝ)
    (hF_meas : Measurable (Function.uncurry F))
    (hF_L2 : ∀ w, MemLp (F w) 2 P)
    (hmean : ∀ x, ∫ w, F w x ∂ν = f x)
    {C : ℝ} (hC : ∀ᵐ w ∂ν, ∫ x, F w x ^ 2 ∂P ≤ C) :
    MemLp f 2 P := by
  have ⟨hF_uncurry_L2, h_swap_le, h_ae_L2⟩ := memLp_uncurry_and_ae_memLp ν P F hF_meas hF_L2 hC
  have hF_sec_meas (x : Ω_x) : Measurable (fun w => F w x) := by
    have : (fun w => F w x) = (Function.uncurry F) ∘ (fun w => (w, x)) := rfl
    rw [this]
    exact hF_meas.comp (Measurable.prodMk measurable_id measurable_const)
  have h_convex : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) :=
    Even.convexOn_pow even_two
  have h_jensen_ae : ∀ᵐ x ∂P, (∫ w, F w x ∂ν) ^ 2 ≤ ∫ w, F w x ^ 2 ∂ν := by
    filter_upwards [h_ae_L2] with x hx
    have hfi : Integrable (fun w => F w x) ν := hx.integrable (by norm_num)
    have hgi : Integrable (fun w => (F w x) ^ 2) ν := by
      rw [← memLp_two_iff_integrable_sq (hF_sec_meas x).aestronglyMeasurable]
      exact hx
    have h_le :=
      ConvexOn.map_integral_le h_convex (continuous_pow 2).continuousOn (isClosed_univ)
        (ae_of_all ν (fun _ => Set.mem_univ _)) hfi hgi
    exact h_le
  have hf2_le_F2 : ∀ᵐ x ∂P, (f x) ^ 2 ≤ ∫ w, F w x ^ 2 ∂ν := by
    filter_upwards [h_jensen_ae] with x hx
    rw [← hmean x]
    exact hx
  constructor
  · have hf_eq : f = fun x => ∫ w, F w x ∂ν := by ext x; rw [← hmean x]
    rw [hf_eq]
    have h_int : Integrable (fun x => ∫ w, F w x ∂ν) P :=
      Integrable.integral_prod_right (hF_uncurry_L2.integrable (show (1 : ENNReal) ≤
        2 by norm_num))
    exact h_int.aestronglyMeasurable
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    have h_enorm : (fun x => enorm (f x) ^ ENNReal.toReal 2) =
      fun x => ENNReal.ofReal (f x ^ 2) := by
      ext x
      rw [enorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg]
      congr 1
      have h2 : ENNReal.toReal 2 = 2 := rfl
      rw [h2, Real.rpow_two, sq_abs]
    rw [h_enorm]
    have h_le := lintegral_mono_ae (μ := P) (by
      filter_upwards [hf2_le_F2] with x hx
      exact ENNReal.ofReal_le_ofReal hx
    )
    refine h_le.trans_lt ?_
    have h_eq : (fun x => ENNReal.ofReal (∫ w, F w x ^ 2 ∂ν)) =ᵐ[P]
        fun x => ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν := by
      filter_upwards [h_ae_L2] with x hx
      have hgi : Integrable (fun w => (F w x) ^ 2) ν := by
        rw [← memLp_two_iff_integrable_sq (hF_sec_meas x).aestronglyMeasurable]
        exact hx
      rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all ν (fun _ => sq_nonneg _))]
    rw [lintegral_congr_ae h_eq]
    have h_lt : (∫⁻ x, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν ∂P) < ⊤ := h_swap_le.trans_lt (by simp)
    exact h_lt

lemma pointwise_maurey_bound {Ω_w Ω_x : Type*} [MeasurableSpace Ω_w] [MeasurableSpace Ω_x]
    (ν : Measure Ω_w) [IsProbabilityMeasure ν] (F : Ω_w → Ω_x → ℝ) (f : Ω_x → ℝ)
    (x : Ω_x) (hx : MemLp (fun w => F w x) 2 ν)
    (hF_sec_meas : Measurable (fun w => F w x))
    (hmean : ∫ w, F w x ∂ν = f x)
    {k : ℕ} (hk : 0 < k) :
    let μ_prob := Measure.pi (fun _ : Fin k => ν)
    ∫ ω : Fin k → Ω_w, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂μ_prob ≤
      (∫ w, F w x ^ 2 ∂ν) / k := by
  intro μ_prob
  have ⟨hindep, hmap⟩ := iid_pi (k := k) ν (fun w => w) measurable_id
  let V : (Fin k → Ω_w) → ℝ := fun ω => F (ω (⟨0, hk⟩ : Fin k)) x
  have hV_L2 : MemLp V 2 μ_prob := memLp_pi_eval ⟨0, hk⟩ hx
  have hVi_L2 (i : Fin k) : MemLp (fun ω : Fin k → Ω_w => F (ω i) x) 2 μ_prob := memLp_pi_eval i hx
  have hVi_mean (i : Fin k) : ∫ ω : Fin k → Ω_w, F (ω i) x ∂μ_prob =
    ∫ ω : Fin k → Ω_w, V ω ∂μ_prob := by
    rw [integral_pi_eval i hx.1, integral_pi_eval ⟨0, hk⟩ hx.1]
  let h_fam : Fin k → (Fin k → Ω_w) → ℝ := fun i ω => F (ω i) x
  have hVi_indep : iIndepFun (m := fun _ => inferInstance) h_fam μ_prob := by
    have h_comp : h_fam = (fun i => (fun w => F w x) ∘ (fun ω => ω i)) := by ext i ω; rfl
    rw [h_comp]
    refine iIndepFun.comp hindep (fun _ => fun w => F w x) (fun _ => hF_sec_meas)
  have hVi_map (i : Fin k) : Measure.map (fun ω : Fin k → Ω_w => F (ω i) x) μ_prob =
    Measure.map V μ_prob := by
    exact map_pi_eval_eq i ⟨0, hk⟩ hF_sec_meas
  have h_ms := maureySampling hV_L2 hk hVi_L2 hVi_mean hVi_indep hVi_map
  have h_mean_eq : ∫ ω : Fin k → Ω_w, V ω ∂μ_prob = f x := by
    rw [integral_pi_eval ⟨0, hk⟩ hx.1, hmean]
  have h_norm_V : ∫ ω : Fin k → Ω_w, ‖V ω‖ ^ 2 ∂μ_prob = ∫ w, F w x ^ 2 ∂ν := by
    have h_int_eq : ∫ ω : Fin k → Ω_w, ‖V ω‖ ^ 2 ∂μ_prob = ∫ ω : Fin k → Ω_w, V ω ^ 2 ∂μ_prob := by
      congr 1; ext omega; rw [Real.norm_eq_abs, sq_abs]
    rw [h_int_eq]
    exact integral_pi_eval ⟨0, hk⟩ (hF_sec_meas.pow_const 2).aestronglyMeasurable
  have h_eq1 (omega : Fin k → Ω_w) :
      ‖(∫ ω : Fin k → Ω_w, V ω ∂μ_prob) - (1 / k : ℝ) • ∑ i, F (omega i) x‖ ^ 2 =
        (f x - (1 / k : ℝ) * ∑ i, F (omega i) x) ^ 2 := by
    rw [h_mean_eq, smul_eq_mul]
    rw [Real.norm_eq_abs, sq_abs]
  have h_int_eq1 :
      ∫ ω : Fin k → Ω_w, ‖(∫ ω : Fin k → Ω_w, V ω ∂μ_prob) -
          (1 / k : ℝ) • ∑ i, F (ω i) x‖ ^ 2 ∂μ_prob =
        ∫ ω : Fin k → Ω_w, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂μ_prob := by
    congr 1; ext ω; exact h_eq1 ω
  change (∫ ω : Fin k → Ω_w,
      ‖(∫ ω : Fin k → Ω_w, V ω ∂μ_prob) - (1 / k : ℝ) • ∑ i, F (ω i) x‖ ^ 2 ∂μ_prob
        ≤ (∫ ω : Fin k → Ω_w, ‖V ω‖ ^ 2 ∂μ_prob) / k) at h_ms
  rw [h_int_eq1, h_norm_V] at h_ms
  exact h_ms

theorem exists_le_integral_sq_of_mean
    (ν : Measure Ω_w) [IsProbabilityMeasure ν] (P : Measure Ω_x) [IsProbabilityMeasure P]
    (F : Ω_w → Ω_x → ℝ) (f : Ω_x → ℝ)
    (hF_meas : Measurable (Function.uncurry F))
    (hF_L2 : ∀ w, MemLp (F w) 2 P)
    (hmean : ∀ x, ∫ w, F w x ∂ν = f x)
    {C : ℝ} (hC : ∀ᵐ w ∂ν, ∫ x, F w x ^ 2 ∂P ≤ C)
    {N : Set Ω_w} (hN : ν N = 0)
    {k : ℕ} (hk : 0 < k) :
    ∃ w : Fin k → Ω_w, (∀ i, w i ∉ N) ∧
      ∫ x, (f x - (1 / k : ℝ) * ∑ i, F (w i) x) ^ 2 ∂P ≤ C / k := by
  let μ_prob := Measure.pi (fun _ : Fin k => ν)
  have hf_L2 : MemLp f 2 P := L2_mean_of_L2 ν P F f hF_meas hF_L2 hmean hC
  have hf_meas : Measurable f := by
    have hf_eq : f = fun x => ∫ w, F w x ∂ν := by ext x; rw [← hmean x]
    rw [hf_eq]
    exact (StronglyMeasurable.integral_prod_left' (μ := ν) hF_meas.stronglyMeasurable).measurable
  have ⟨_, h_swap_le, h_ae_L2⟩ := memLp_uncurry_and_ae_memLp ν P F hF_meas hF_L2 hC
  have hF_sec_meas (x : Ω_x) : Measurable (fun w => F w x) := by
    have : (fun w => F w x) = (Function.uncurry F) ∘ (fun w => (w, x)) := rfl
    rw [this]
    exact hF_meas.comp (Measurable.prodMk measurable_id measurable_const)
  have h_int_P (w : Fin k → Ω_w) :
      Integrable (fun x => (f x - (1 / k : ℝ) * ∑ i, F (w i) x) ^ 2) P := by
    have h_meas : Measurable (fun x => f x - (1 / k : ℝ) * ∑ i, F (w i) x) := by
      have h_sec (i : Fin k) : Measurable (F (w i)) := by
        have : F (w i) = (Function.uncurry F) ∘ (fun x => (w i, x)) := rfl
        rw [this]
        exact hF_meas.comp (Measurable.prodMk measurable_const measurable_id)
      have h_sum_meas : Measurable (fun x => ∑ i, F (w i) x) :=
        Finset.measurable_sum Finset.univ (fun i _ => h_sec i)
      exact hf_meas.sub (measurable_const.mul h_sum_meas)
    rw [← memLp_two_iff_integrable_sq h_meas.aestronglyMeasurable]
    have h_sum : MemLp (fun x => ∑ i, F (w i) x) 2 P := by
      have h_sum_eq : (fun x => ∑ i, F (w i) x) = ∑ i, F (w i) := by ext x; simp
      rw [h_sum_eq]
      exact memLp_finsetSum' Finset.univ (fun i _ => hF_L2 (w i))
    have h_smul : MemLp (fun x => (1 / k : ℝ) * ∑ i, F (w i) x) 2 P := by
      have h_eq : (fun x => (1 / k : ℝ) * ∑ i, F (w i) x) =
        (1 / k : ℝ) • (fun x => ∑ i, F (w i) x) := by ext x; rfl
      rw [h_eq]
      exact h_sum.const_smul _
    exact hf_L2.sub h_smul
  have h_ofReal_eq (w : Fin k → Ω_w) :
      ENNReal.ofReal (∫ x, (f x - (1 / k : ℝ) * ∑ i, F (w i) x) ^ 2 ∂P) =
      ∫⁻ x, ENNReal.ofReal ((f x - (1 / k : ℝ) * ∑ i, F (w i) x) ^ 2) ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal (h_int_P w) (ae_of_all P (fun _ => sq_nonneg _))]
  have h_meas_curry : Measurable (fun p : (Fin k → Ω_w) × Ω_x =>
      ENNReal.ofReal ((f p.2 - (1 / k : ℝ) * ∑ i, F (p.1 i) p.2) ^ 2)) := by
    have h1 : Measurable (fun p : (Fin k → Ω_w) × Ω_x => f p.2) := hf_meas.comp measurable_snd
    have h2 (i : Fin k) : Measurable (fun p : (Fin k → Ω_w) × Ω_x => F (p.1 i) p.2) := by
      have : (fun p : (Fin k → Ω_w) × Ω_x => F (p.1 i) p.2) =
        (Function.uncurry F) ∘ (fun p : (Fin k → Ω_w) × Ω_x => (p.1 i, p.2)) := rfl
      rw [this]
      refine hF_meas.comp ?_
      exact Measurable.prodMk ((measurable_pi_apply i).comp measurable_fst) measurable_snd
    have h3 : Measurable (fun p : (Fin k → Ω_w) × Ω_x => ∑ i, F (p.1 i) p.2) :=
      Finset.measurable_sum Finset.univ (fun i _ => h2 i)
    have h4 : Measurable (fun p : (Fin k → Ω_w) × Ω_x =>
        f p.2 - (1 / k : ℝ) * ∑ i, F (p.1 i) p.2) :=
      h1.sub (measurable_const.mul h3)
    exact Measurable.ennreal_ofReal (h4.pow_const 2)
  have h_lintegral_le : ∫⁻ ω : Fin k → Ω_w, ENNReal.ofReal (∫ x,
      (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P) ∂μ_prob ≤ ENNReal.ofReal C / k := by
    simp_rw [h_ofReal_eq]
    rw [lintegral_lintegral_swap h_meas_curry.aemeasurable]
    have h_le : (∫⁻ x, ∫⁻ ω : Fin k → Ω_w,
        ENNReal.ofReal ((f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2)
        ∂μ_prob ∂P) ≤ ∫⁻ x, ENNReal.ofReal ((∫ w, F w x ^ 2 ∂ν) / k) ∂P := by
      refine lintegral_mono_ae ?_
      filter_upwards [h_ae_L2] with x hx
      have h_L2 (i : Fin k) : MemLp (fun ω : Fin k → Ω_w => F (ω i) x) 2 μ_prob :=
        memLp_pi_eval i hx
      have h_int_pointwise : Integrable (fun ω : Fin k → Ω_w =>
          (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2) μ_prob := by
        have h_meas_comp (i : Fin k) : Measurable (fun ω : Fin k → Ω_w => F (ω i) x) :=
          (hF_sec_meas x).comp (measurable_pi_apply i)
        have h_sum_meas : Measurable (fun ω : Fin k → Ω_w => ∑ i, F (ω i) x) := by
          exact Finset.measurable_sum Finset.univ (fun i _ => h_meas_comp i)
        have h_meas : Measurable (fun ω : Fin k → Ω_w => f x - (1 / k : ℝ) * ∑ i, F (ω i) x) := by
          exact measurable_const.sub (measurable_const.mul h_sum_meas)
        rw [← memLp_two_iff_integrable_sq h_meas.aestronglyMeasurable]
        have h_sum : MemLp (fun ω : Fin k → Ω_w => ∑ i, F (ω i) x) 2 μ_prob := by
          have h_eq : (fun ω : Fin k → Ω_w => ∑ i, F (ω i) x) =
          ∑ i : Fin k, (fun ω => F (ω i) x) := by ext ω; simp
          rw [h_eq]
          exact memLp_finsetSum' Finset.univ (fun i _ => h_L2 i)
        have h_smul : MemLp (fun ω : Fin k → Ω_w => (1 / k : ℝ) * ∑ i, F (ω i) x) 2 μ_prob := by
          have h_eq : (fun ω : Fin k → Ω_w => (1 / k : ℝ) * ∑ i, F (ω i) x) =
          (1 / k : ℝ) • (fun ω => ∑ i, F (ω i) x) := by ext ω; rfl
          rw [h_eq]
          exact h_sum.const_smul _
        exact (memLp_const (f x)).sub h_smul
      rw [← ofReal_integral_eq_lintegral_ofReal h_int_pointwise
        (ae_of_all μ_prob (fun _ => sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal
        (pointwise_maurey_bound ν F f x hx (hF_sec_meas x) (hmean x) hk)
    have h_div_eq : (fun x => ENNReal.ofReal ((∫ w, F w x ^ 2 ∂ν) / k)) =
      fun x => (1 / (k : ENNReal)) * ENNReal.ofReal (∫ w, F w x ^ 2 ∂ν) := by
      ext x
      have hk_pos : 0 < (k : ℝ) := by positivity
      rw [ENNReal.ofReal_div_of_pos hk_pos]
      rw [ENNReal.ofReal_natCast]
      rw [div_eq_mul_inv]
      rw [← one_div]
      rw [mul_comm]
    refine h_le.trans ?_
    simp_rw [h_div_eq]
    rw [lintegral_const_mul' (1 / (k : ENNReal)) _ (ENNReal.div_ne_top (by simp) (by positivity))]
    have h_int_eq : (∫⁻ x, ENNReal.ofReal (∫ w, F w x ^ 2 ∂ν) ∂P) =
      ∫⁻ x, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν ∂P := by
      apply lintegral_congr_ae
      filter_upwards [h_ae_L2] with x hx
      have hgi : Integrable (fun w => (F w x) ^ 2) ν := by
        rw [← memLp_two_iff_integrable_sq (hF_sec_meas x).aestronglyMeasurable]
        exact hx
      rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all ν (fun _ => sq_nonneg _))]
    rw [h_int_eq]
    have h_le2 : (1 / (k : ENNReal)) * ∫⁻ x, ∫⁻ w, ENNReal.ofReal (F w x ^ 2) ∂ν ∂P ≤
      (1 / (k : ENNReal)) * ENNReal.ofReal C := by
      gcongr
    refine h_le2.trans (le_of_eq ?_)
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
  have h_int_all : Integrable (fun ω : Fin k → Ω_w =>
      ∫ x, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P) μ_prob := by
    constructor
    · have h_meas_joint : AEStronglyMeasurable (fun p : (Fin k → Ω_w) × Ω_x =>
          (f p.2 - (1 / k : ℝ) * ∑ i, F (p.1 i) p.2) ^ 2) (μ_prob.prod P) := by
        have h_meas : Measurable (fun p : (Fin k → Ω_w) × Ω_x =>
            (f p.2 - (1 / k : ℝ) * ∑ i, F (p.1 i) p.2) ^ 2) := by
          have h1 : Measurable (fun p : (Fin k → Ω_w) × Ω_x => f p.2) :=
            hf_meas.comp measurable_snd
          have h2 (i : Fin k) : Measurable (fun p : (Fin k → Ω_w) × Ω_x => F (p.1 i) p.2) := by
            have : (fun p : (Fin k → Ω_w) × Ω_x => F (p.1 i) p.2) =
        (Function.uncurry F) ∘ (fun p : (Fin k → Ω_w) × Ω_x => (p.1 i, p.2)) := rfl
            rw [this]
            refine hF_meas.comp ?_
            exact Measurable.prodMk ((measurable_pi_apply i).comp measurable_fst) measurable_snd
          have h3 : Measurable (fun p : (Fin k → Ω_w) × Ω_x => ∑ i, F (p.1 i) p.2) :=
            Finset.measurable_sum Finset.univ (fun i _ => h2 i)
          have h4 : Measurable (fun p : (Fin k → Ω_w) × Ω_x =>
        f p.2 - (1 / k : ℝ) * ∑ i, F (p.1 i) p.2) :=
            h1.sub (measurable_const.mul h3)
          exact h4.pow_const 2
        exact h_meas.aestronglyMeasurable
      exact h_meas_joint.integral_prod_right'
    · dsimp [HasFiniteIntegral]
      have h_lintegral_eq : (∫⁻ ω : Fin k → Ω_w,
          enorm (∫ x, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P) ∂μ_prob) =
          ∫⁻ ω : Fin k → Ω_w,
          ENNReal.ofReal (∫ x, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P) ∂μ_prob := by
        congr 1; ext ω
        rw [enorm_eq_ofReal_abs]
        have : 0 ≤ ∫ x, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P :=
          integral_nonneg (fun x => sq_nonneg _)
        rw [abs_of_nonneg this]
      rw [h_lintegral_eq]
      exact h_lintegral_le.trans_lt (ENNReal.div_lt_top ENNReal.ofReal_ne_top (by simp [hk.ne']))
  let N_bad : Set (Fin k → Ω_w) := { ω | ∃ i, ω i ∈ N }
  have h_null (i : Fin k) : μ_prob ((fun ω : Fin k → Ω_w => ω i) ⁻¹' N) = 0 := by
    obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
    have h_sub : (fun ω : Fin k → Ω_w => ω i) ⁻¹' N ⊆ (fun ω => ω i) ⁻¹' N' :=
      Set.preimage_mono hNN'
    refine measure_mono_null h_sub ?_
    have h_map_eq : μ_prob ((fun ω : Fin k → Ω_w => ω i) ⁻¹' N') =
        Measure.map (fun ω : Fin k → Ω_w => ω i) μ_prob N' := by
      rw [Measure.map_apply (measurable_pi_apply i) hN'm]
    rw [h_map_eq]
    have hmap_i : Measure.map (fun ω : Fin k → Ω_w => ω i) μ_prob = ν := by
      have h_eval : (fun ω : Fin k → Ω_w => ω i) = Function.eval i := rfl
      rw [h_eval, Measure.pi_map_eval]
      simp
    rw [hmap_i, hN'0]
  have hN_bad_null : μ_prob N_bad = 0 := by
    have h_eq : N_bad = ⋃ i, (fun ω : Fin k → Ω_w => ω i) ⁻¹' N := by
      ext ω; dsimp [N_bad]; simp
    rw [h_eq]
    exact measure_iUnion_null (fun i => h_null i)
  obtain ⟨w, hw_bad, hw_le⟩ := exists_notMem_null_le_integral h_int_all hN_bad_null
  refine ⟨w, ?_, ?_⟩
  · intro i
    have : w ∉ N_bad := hw_bad
    simp only [N_bad, Set.mem_setOf_eq, not_exists] at this
    exact this i
  · have h_int_eq_toReal : ∫ ω : Fin k → Ω_w, ∫ x,
        (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P ∂μ_prob =
        (∫⁻ ω : Fin k → Ω_w, ENNReal.ofReal (∫ x,
          (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P) ∂μ_prob).toReal := by
      have h_int_eq' : ENNReal.ofReal (∫ ω : Fin k → Ω_w, ∫ x,
          (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P ∂μ_prob) =
          ∫⁻ ω : Fin k → Ω_w,
          ENNReal.ofReal (∫ x, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P) ∂μ_prob := by
        refine ofReal_integral_eq_lintegral_ofReal h_int_all (ae_of_all μ_prob ?_)
        intro ω
        exact integral_nonneg (fun x => sq_nonneg (f x - (1 / k : ℝ) * ∑ i, F (ω i) x))
      rw [← h_int_eq']
      rw [ENNReal.toReal_ofReal]
      exact integral_nonneg (fun ω => integral_nonneg
        (fun x => sq_nonneg (f x - (1 / k : ℝ) * ∑ i, F (ω i) x)))
    rw [h_int_eq_toReal] at hw_le
    have h_ae : ∀ᶠ w' in ae ν, 0 ≤ C := by
      filter_upwards [hC] with w' hw'
      have : 0 ≤ ∫ x, F w' x ^ 2 ∂P := integral_nonneg (fun x => sq_nonneg _)
      exact this.trans hw'
    have h_exists := Filter.Eventually.exists (f := ae ν) h_ae
    have hC_nonneg : 0 ≤ C := by
      rcases h_exists with ⟨w', hw'⟩
      exact hw'
    have h_eq : (ENNReal.ofReal C / (k : ENNReal)).toReal = C / k := by
      rw [ENNReal.toReal_div]
      · rw [ENNReal.toReal_ofReal hC_nonneg]
        rw [ENNReal.toReal_natCast]
    have h_le_toReal : (∫⁻ ω, ENNReal.ofReal (∫ x, (f x - (1 / k : ℝ) * ∑ i, F (ω i) x) ^ 2 ∂P)
        ∂μ_prob).toReal ≤ (ENNReal.ofReal C / (k : ENNReal)).toReal :=
      ENNReal.toReal_mono (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by positivity)) h_lintegral_le
    exact hw_le.trans (h_le_toReal.trans (le_of_eq h_eq))

end L2Maurey

/-! ### Maurey for signed measures (Lemma 3.2)

Following the notes, a *signed sample* is a pair `(w, s)` consisting of a parameter `w` and a
sign `s ∈ {±1}`, drawn from the normalized measure `μ̃` built out of the Jordan decomposition
`μ = μ₊ - μ₋`:

  `Pr[s = +1] = ‖μ₊‖₁ / ‖μ‖₁`,  then  `w ∼ μ_s / ‖μ_s‖₁`,  output  `g̃(·; w, s) = s ‖μ‖₁ g(·; w)`.

**Refactor note.**  The signed sample used to be a bespoke `structure SignedSample (p : ℕ)` with
`weight : Fin p → ℝ`.  It is replaced here by the plain product `W × Bool` over an *abstract*
measurable parameter space `W`, for three reasons.
* A bespoke structure carries no `MeasurableSpace` instance, so it cannot be the codomain of a
  `Measure.map` — and the whole construction of `μ̃` is a pushforward.  (This is also the trap
  recorded in `docs/lessons_learned.md` §12, "Set Mapping with Custom Structures".)
* `W × Bool` gets `MeasurableSpace`, `BorelSpace`, … for free by instance inference.
* Abstracting `Fin p → ℝ` to `W` costs nothing and matches the notes, which remark that the
  parameter space is `ℝᵖ` only "since we might bake in biases and other feature mappings".
-/

section SignedMaurey

open MeasureTheory.SignedMeasure

variable {W : Type*} [MeasurableSpace W]

/-- The `±1` value attached to the `Bool` half of a signed sample: `true ↦ 1`, `false ↦ -1`. -/
def signWeight (s : Bool) : ℝ := if s then 1 else -1

@[simp] lemma signWeight_true : signWeight true = 1 := rfl

@[simp] lemma signWeight_false : signWeight false = -1 := rfl

@[simp] lemma signWeight_sq (s : Bool) : signWeight s ^ 2 = 1 := by
  cases s <;> norm_num [signWeight]

lemma measurable_signWeight : Measurable signWeight := measurable_of_countable _

/-- The total mass `‖μ‖₁ = ‖μ₊‖₁ + ‖μ₋‖₁` of a signed measure, as a real number.

This is `μ.totalVariation Set.univ`, pushed to `ℝ`; `SignedMeasure.totalVariation` is by
definition `μ₊ + μ₋`, so this agrees with the notes' `‖μ‖₁`. -/
noncomputable def totalMass (μ : SignedMeasure W) : ℝ := (μ.totalVariation Set.univ).toReal

/-- `‖μ‖₁ = ‖μ₊‖₁ + ‖μ₋‖₁`: the notes' formula for the total mass. -/
lemma totalMass_eq_add (μ : SignedMeasure W) :
    totalMass μ = (μ.toJordanDecomposition.posPart Set.univ).toReal
      + (μ.toJordanDecomposition.negPart Set.univ).toReal := by
  classical
  have h := μ.toJordanDecomposition.posPart_finite
  have h' := μ.toJordanDecomposition.negPart_finite
  rw [totalMass, SignedMeasure.totalVariation, Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

lemma totalMass_nonneg (μ : SignedMeasure W) : 0 ≤ totalMass μ := ENNReal.toReal_nonneg

/-- A nonzero signed measure has strictly positive total mass.

Proof: if `‖μ‖₁ = 0`, then by monotonicity `μ.totalVariation i = 0` for *every* measurable `i`,
so `μ i = 0` by `SignedMeasure.null_of_totalVariation_zero`, so `μ = 0`. -/
lemma totalMass_pos {μ : SignedMeasure W} (hμ : μ ≠ 0) : 0 < totalMass μ := by
  haveI := μ.toJordanDecomposition.posPart_finite
  haveI := μ.toJordanDecomposition.negPart_finite
  have hfin : μ.totalVariation Set.univ ≠ ⊤ := by
    rw [SignedMeasure.totalVariation]
    exact measure_ne_top _ _
  rw [totalMass, ENNReal.toReal_pos_iff]
  refine ⟨pos_iff_ne_zero.mpr ?_, lt_top_iff_ne_top.mpr hfin⟩
  intro h
  refine hμ (MeasureTheory.VectorMeasure.ext fun i hi => ?_)
  have hle : μ.totalVariation i ≤ μ.totalVariation Set.univ := measure_mono (Set.subset_univ i)
  have hzero : μ.totalVariation i = 0 := le_antisymm (h ▸ hle) zero_le
  simpa using SignedMeasure.null_of_totalVariation_zero μ hzero

/-- The normalized sampling distribution `μ̃` on signed samples `W × Bool`, obtained by pushing
`μ₊` forward along `w ↦ (w, true)`, `μ₋` forward along `w ↦ (w, false)`, and normalizing by the
total mass.

Marginalizing out the sign recovers `Pr[s = +1] = ‖μ₊‖₁ / ‖μ‖₁` and, conditionally on the sign,
`w ∼ μ_s / ‖μ_s‖₁`, exactly as in the notes. -/
noncomputable def jordanSample (μ : SignedMeasure W) : Measure (W × Bool) :=
  (μ.totalVariation Set.univ)⁻¹ •
    (μ.toJordanDecomposition.posPart.map (fun w => (w, true))
      + μ.toJordanDecomposition.negPart.map (fun w => (w, false)))

/-- `μ̃` is a probability measure (for `μ ≠ 0`).

Informal proof: the two pushforwards have total masses `‖μ₊‖₁` and `‖μ₋‖₁` (pushforward along a
measurable map preserves the mass of the whole space), so the unnormalized measure has mass
`‖μ‖₁ = μ.totalVariation univ`, which is nonzero (`totalMass_pos`) and finite; scaling by its
inverse gives mass `1`. -/
instance isProbabilityMeasure_jordanSample {μ : SignedMeasure W} [NeZero μ] :
    IsProbabilityMeasure (jordanSample μ) := by
  constructor
  haveI := μ.toJordanDecomposition.posPart_finite
  haveI := μ.toJordanDecomposition.negPart_finite
  have h_meas_true : Measurable (fun w : W => (w, true)) :=
    Measurable.prodMk measurable_id measurable_const
  have h_meas_false : Measurable (fun w : W => (w, false)) :=
    Measurable.prodMk measurable_id measurable_const
  have h_pos := μ.toJordanDecomposition.posPart.map_apply h_meas_true
    (MeasurableSet.univ : MeasurableSet Set.univ)
  have h_neg := μ.toJordanDecomposition.negPart.map_apply h_meas_false
    (MeasurableSet.univ : MeasurableSet Set.univ)
  dsimp [jordanSample]
  rw [h_pos, h_neg]
  simp only [Set.preimage_univ]
  change (μ.totalVariation Set.univ)⁻¹ * (μ.totalVariation Set.univ) = 1
  rw [ENNReal.inv_mul_cancel]
  · intro h_zero
    have hne : μ ≠ 0 := NeZero.ne μ
    have hpos : 0 < (μ.totalVariation Set.univ).toReal := totalMass_pos hne
    revert hpos
    rw [h_zero]
    simp
  · change μ.toJordanDecomposition.posPart Set.univ + μ.toJordanDecomposition.negPart Set.univ ≠ ⊤
    have h1 := measure_ne_top μ.toJordanDecomposition.posPart Set.univ
    have h2 := measure_ne_top μ.toJordanDecomposition.negPart Set.univ
    exact ENNReal.add_ne_top.mpr ⟨h1, h2⟩

/-- The `μ̃`-integral splits over the two parts of the Jordan decomposition:

  `∫ f dμ̃ = ‖μ‖₁⁻¹ ( ∫ f(w, +1) dμ₊(w) + ∫ f(w, -1) dμ₋(w) )`.

Informal proof: `MeasureTheory.integral_smul_measure` peels off the scalar,
`MeasureTheory.integral_add_measure` splits the sum, and `MeasureTheory.integral_map` (with the
measurable embeddings `w ↦ (w, true)` and `w ↦ (w, false)`) rewrites each pushforward integral.
Note `ENNReal.toReal_inv` is needed to turn the `ℝ≥0∞` scalar into `(totalMass μ)⁻¹`. -/
lemma integral_jordanSample {μ : SignedMeasure W} (f : W × Bool → ℝ)
    (hf_pos : Integrable (fun w => f (w, true)) μ.toJordanDecomposition.posPart)
    (hf_neg : Integrable (fun w => f (w, false)) μ.toJordanDecomposition.negPart) :
    ∫ z, f z ∂(jordanSample μ)
      = (totalMass μ)⁻¹ * ((∫ w, f (w, true) ∂μ.toJordanDecomposition.posPart)
          + ∫ w, f (w, false) ∂μ.toJordanDecomposition.negPart) := by
  dsimp [jordanSample]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_add_measure]
  · congr 1
    · exact ENNReal.toReal_inv (μ.totalVariation Set.univ)
    · congr 1
      · exact (measurableEmbedding_prod_mk_right true).integral_map f
      · exact (measurableEmbedding_prod_mk_right false).integral_map f
  · exact ((measurableEmbedding_prod_mk_right true).integrable_map_iff).mpr hf_pos
  · exact ((measurableEmbedding_prod_mk_right false).integrable_map_iff).mpr hf_neg

/-- The integral of `g` against a *signed* measure, defined through the Jordan decomposition:
`∫ g dμ := ∫ g dμ₊ - ∫ g dμ₋`.

Mathlib has no Bochner integral against a `SignedMeasure` (only `VectorMeasure.withDensityᵥ`),
so we introduce it here.  Everything downstream is stated in terms of this. -/
noncomputable def signedIntegral (μ : SignedMeasure W) (g : W → ℝ) : ℝ :=
  (∫ w, g w ∂μ.toJordanDecomposition.posPart) - ∫ w, g w ∂μ.toJordanDecomposition.negPart

/-- The rescaled atom `g̃(·; w, s) = s · ‖μ‖₁ · g(w)` attached to a signed sample `z = (w, s)`.
This is the random element of `L₂(P)` that Maurey's lemma is applied to. -/
noncomputable def rescaled (μ : SignedMeasure W) (g : W → ℝ) (z : W × Bool) : ℝ :=
  signWeight z.2 * totalMass μ * g z.1

/-- **"This sampling procedure has the correct mean"** (the display just before Lemma 3.2).

  `𝔼_{(w,s) ∼ μ̃} [ s ‖μ‖₁ g(w) ] = ∫ g dμ₊ - ∫ g dμ₋ = ∫ g dμ`.

Informal proof.  By `integral_jordanSample` applied to `f = rescaled μ g`,

  `𝔼 g̃ = ‖μ‖₁⁻¹ ( ∫ (+1)·‖μ‖₁·g dμ₊ + ∫ (-1)·‖μ‖₁·g dμ₋ )`
       `= ‖μ‖₁⁻¹ · ‖μ‖₁ · ( ∫ g dμ₊ - ∫ g dμ₋ )`
       `= signedIntegral μ g`,

using `integral_const_mul` on each piece and `‖μ‖₁ ≠ 0` (`totalMass_pos`) to cancel.
This is the *only* place the specific normalization of `μ̃` is used. -/
lemma integral_rescaled {μ : SignedMeasure W} (hμ : μ ≠ 0) (g : W → ℝ)
    (hg_pos : Integrable g μ.toJordanDecomposition.posPart)
    (hg_neg : Integrable g μ.toJordanDecomposition.negPart) :
    ∫ z, rescaled μ g z ∂(jordanSample μ) = signedIntegral μ g := by
  have Hpos : Integrable (fun w => rescaled μ g (w, true)) μ.toJordanDecomposition.posPart := by
    simp_rw [rescaled, signWeight_true, one_mul]
    exact hg_pos.const_mul (totalMass μ)
  have Hneg : Integrable (fun w => rescaled μ g (w, false)) μ.toJordanDecomposition.negPart := by
    simp_rw [rescaled, signWeight_false, neg_mul, one_mul]
    exact (hg_neg.const_mul (totalMass μ)).neg
  rw [integral_jordanSample (rescaled μ g) Hpos Hneg]
  simp_rw [rescaled, signWeight_true, signWeight_false, one_mul, neg_one_mul, neg_mul]
  rw [MeasureTheory.integral_neg]
  simp_rw [← smul_eq_mul]
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul]
  simp_rw [smul_eq_mul]
  rw [← sub_eq_add_neg, ← mul_sub, ← mul_assoc]
  have Hmass : totalMass μ ≠ 0 := (totalMass_pos hμ).ne'
  rw [inv_mul_cancel₀ Hmass, one_mul]
  rfl

/-- The second moment of an atom is `‖μ‖₁²` times that of `g(w)`:
`(g̃(x; w, s))² = ‖μ‖₁² · g(w)(x)²`, since `s² = 1`. -/
lemma rescaled_sq (μ : SignedMeasure W) (g : W → ℝ) (z : W × Bool) :
    rescaled μ g z ^ 2 = totalMass μ ^ 2 * g z.1 ^ 2 := by
  simp only [rescaled, mul_pow, signWeight_sq]
  ring

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
    {Ω_x : Type*} {mΩ_x : MeasurableSpace Ω_x}
    (P : Measure Ω_x) [IsProbabilityMeasure P]
    {μ : SignedMeasure W} (hμ : μ ≠ 0)
    {S : Set W} (hS : MeasurableSet S) (hS_supp : μ.totalVariation Sᶜ = 0)
    (g : W → Ω_x → ℝ)
    (hg_meas : Measurable (Function.uncurry g))
    (hg_L2 : ∀ w, MemLp (g w) 2 P)
    (hg_int_pos : ∀ x, Integrable (fun w => g w x) μ.toJordanDecomposition.posPart)
    (hg_int_neg : ∀ x, Integrable (fun w => g w x) μ.toJordanDecomposition.negPart)
    {B : ℝ} (hB : ∀ w ∈ S, ∫ x, g w x ^ 2 ∂P ≤ B)
    {k : ℕ} (hk : 0 < k) :
    ∃ ws : Fin k → W × Bool, (∀ i, (ws i).1 ∈ S) ∧
      ∫ x, (signedIntegral μ (fun w => g w x)
              - (1 / k : ℝ) * ∑ i, rescaled μ (fun w => g w x) (ws i)) ^ 2 ∂P
        ≤ totalMass μ ^ 2 * B / k := by
  /-
  Lean plan (all the mathematical content is already isolated in the lemmas above):

  1. `haveI : NeZero μ := ⟨hμ⟩`, so `jordanSample μ` is a probability measure.
  2. Apply `exists_le_integral_sq_of_mean` with
       `ν := jordanSample μ`,
       `F := fun z x => rescaled μ (fun w => g w x) z`,
       `f := fun x => signedIntegral μ (fun w => g w x)`,
       `C := totalMass μ ^ 2 * B`,
       `N := (fun z => z.1) ⁻¹' Sᶜ`   (the samples landing outside `S`).
  3. Discharge its hypotheses:
     * `hmean` is `integral_rescaled hμ (fun w => g w x) (hg_int_pos x) (hg_int_neg x)`,
       applied for *every* `x` (so the `∀ᵐ` is trivial).
     * `hC`: for `ν`-a.e. `z = (w, s)` we have `w ∈ S` (that is exactly `hν_N` below), and then
         `∫ x, F z x ^ 2 ∂P = totalMass μ ^ 2 * ∫ x, g w x ^ 2 ∂P ≤ totalMass μ ^ 2 * B`
       by `rescaled_sq`, `integral_const_mul`, `hB`, and `sq_nonneg (totalMass μ)`.
     * `hν_N : jordanSample μ N = 0`.  Unfolding `jordanSample`, `N` pulls back to `Sᶜ` under
       both pushforwards, and `μ.totalVariation Sᶜ = 0` says exactly that `μ₊ Sᶜ = μ₋ Sᶜ = 0`
       (`SignedMeasure.totalVariation` is `μ₊ + μ₋`, and a sum of measures vanishes on a set iff
       both do).  Scaling by `‖μ‖₁⁻¹` preserves nullity.
  4. The returned `ws : Fin k → W × Bool` avoids `N`, i.e. `(ws i).1 ∈ S`, which is the first
     conjunct; the second is the returned bound.
  -/
  haveI : NeZero μ := ⟨hμ⟩
  let ν := jordanSample μ
  let F : W × Bool → Ω_x → ℝ := fun z x => rescaled μ (fun w => g w x) z
  let f_mean : Ω_x → ℝ := fun x => signedIntegral μ (fun w => g w x)
  let C := totalMass μ ^ 2 * B
  let N : Set (W × Bool) := (fun z => z.1) ⁻¹' Sᶜ
  have hmean : ∀ x, ∫ w, F w x ∂ν = f_mean x := by
    intro x
    exact integral_rescaled hμ (fun w => g w x) (hg_int_pos x) (hg_int_neg x)
  have hN : ν N = 0 := by
    change (μ.totalVariation Set.univ)⁻¹ *
      ((Measure.map (fun w ↦ (w, true)) μ.toJordanDecomposition.posPart) ((fun z ↦ z.1) ⁻¹' Sᶜ) +
      (Measure.map (fun w ↦ (w, false)) μ.toJordanDecomposition.negPart) ((fun z ↦ z.1) ⁻¹' Sᶜ)) = 0
    have hN_meas : MeasurableSet ((fun z : W × Bool ↦ z.1) ⁻¹' Sᶜ) := measurable_fst hS.compl
    rw [Measure.map_apply (measurableEmbedding_prod_mk_right true).measurable hN_meas]
    rw [Measure.map_apply (measurableEmbedding_prod_mk_right false).measurable hN_meas]
    have h_pre1 : (fun (w : W) ↦ (w, true)) ⁻¹' ((fun z : W × Bool ↦ z.1) ⁻¹' Sᶜ) = Sᶜ := rfl
    have h_pre2 : (fun (w : W) ↦ (w, false)) ⁻¹' ((fun z : W × Bool ↦ z.1) ⁻¹' Sᶜ) = Sᶜ := rfl
    rw [h_pre1, h_pre2]
    have h_tot : μ.toJordanDecomposition.posPart Sᶜ + μ.toJordanDecomposition.negPart Sᶜ = 0 := by
      exact hS_supp
    rw [h_tot, mul_zero]
  have hC : ∀ᵐ z ∂ν, ∫ x, F z x ^ 2 ∂P ≤ C := by
    have H1 : ∀ z : W × Bool, z.1 ∈ S → ∫ x, F z x ^ 2 ∂P ≤ C := by
      intro z hz_S
      simp_rw [F, rescaled_sq]
      simp_rw [← smul_eq_mul, MeasureTheory.integral_smul, smul_eq_mul]
      have h_le := hB z.1 hz_S
      have h_pos : 0 ≤ totalMass μ ^ 2 := sq_nonneg (totalMass μ)
      exact mul_le_mul_of_nonneg_left h_le h_pos
    exact (MeasureTheory.ae_iff.mpr hN).mono H1
  have hF_meas : Measurable (Function.uncurry F) := by
    dsimp [Function.uncurry, F, rescaled]
    have H1 : Measurable (fun p : (W × Bool) × Ω_x => signWeight p.1.2) :=
      measurable_signWeight.comp (measurable_snd.comp measurable_fst)
    have H2 : Measurable (fun p : (W × Bool) × Ω_x => totalMass μ) :=
      measurable_const
    have H3 : Measurable (fun p : (W × Bool) × Ω_x => g p.1.1 p.2) :=
      hg_meas.comp (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd)
    exact (H1.mul H2).mul H3
  have hF_L2 : ∀ z, MemLp (F z) 2 P := by
    intro z
    dsimp [F, rescaled]
    have H := hg_L2 z.1
    exact MemLp.const_mul H (signWeight z.2 * totalMass μ)
  rcases exists_le_integral_sq_of_mean ν P F f_mean hF_meas hF_L2
    hmean hC hN hk with ⟨ws, hws_N, hws_bound⟩
  use ws
  constructor
  · intro i
    have h_not : ws i ∉ N := hws_N i
    by_contra h
    exact h_not h
  · exact hws_bound

end SignedMaurey

/-! ### Barron's full sampling bound -/

open Approximation.InfiniteWidth

lemma thresholdActivation_meas : Measurable thresholdActivation := by
  unfold thresholdActivation
  apply Measurable.ite
  · exact measurableSet_Ici
  · exact measurable_const
  · exact measurable_const

lemma thresholdActivation_bound (x : ℝ) : 0 ≤ thresholdActivation x ∧ thresholdActivation x ≤ 1 := by
  unfold thresholdActivation
  split_ifs <;> norm_num

noncomputable def extractWeights {d : ℕ} (w : Fin (d + 1) → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ w j.castSucc)

noncomputable def extractBias {d : ℕ} (w : Fin (d + 1) → ℝ) : ℝ :=
  w (Fin.last d)

lemma barronSamplingBound_measurability
    {d : ℕ} {Ω_x : Type*} [MeasurableSpace Ω_x]
    (x_embed : Ω_x → EuclideanSpace ℝ (Fin d)) (hx_meas : Measurable x_embed) :
    Measurable (fun (p : (Fin (d + 1) → ℝ) × Ω_x) =>
      thresholdActivation (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ p.1 j.castSucc)) (x_embed p.2) - p.1 (Fin.last d))) := by
  apply thresholdActivation_meas.comp
  have hc : Continuous (fun p : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) => inner ℝ p.1 p.2) := continuous_inner
  have hm_inner : Measurable (fun p : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) => inner ℝ p.1 p.2) := hc.measurable
  have h1 : Measurable (fun p : (Fin (d + 1) → ℝ) × Ω_x => ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ p.1 j.castSucc), x_embed p.2)) := by
    apply Measurable.prod
    · have h_lin : Continuous (fun wb : (Fin (d + 1) → ℝ) => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ wb j.castSucc)) := by
        apply Continuous.comp (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
        apply continuous_pi
        intro j
        exact continuous_apply _
      exact (h_lin.measurable).comp measurable_fst
    · exact hx_meas.comp measurable_snd
  have hm1 : Measurable (fun p : (Fin (d + 1) → ℝ) × Ω_x => inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ p.1 j.castSucc)) (x_embed p.2)) := hm_inner.comp h1
  apply Measurable.sub
  · exact hm1
  · exact (measurable_pi_apply _).comp measurable_fst

lemma barronSamplingBound_L2
    {d : ℕ} {Ω_x : Type*} [MeasurableSpace Ω_x]
    (x_embed : Ω_x → EuclideanSpace ℝ (Fin d)) (hx_meas : Measurable x_embed)
    (P : Measure Ω_x) [IsProbabilityMeasure P]
    (w : Fin (d + 1) → ℝ) :
    MemLp (fun (x : Ω_x) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) 2 P := by
  have h_meas_w : Measurable (fun (x : Ω_x) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) := by
    have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ (extractWeights w) x - extractBias w) := by
      exact (continuous_const.inner continuous_id).sub continuous_const
    exact (thresholdActivation_meas).comp (h1.measurable.comp hx_meas)
  have h_ae : AEStronglyMeasurable (fun (x : Ω_x) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) P := h_meas_w.aestronglyMeasurable
  have h_bound : ∀ᵐ (x : Ω_x) ∂P, ‖thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)‖ ≤ 1 := by
    filter_upwards [] with x
    have h_ta := thresholdActivation_bound (inner ℝ (extractWeights w) (x_embed x) - extractBias w)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h_fin : IsFiniteMeasure P := inferInstance
  exact MemLp.of_bound (f := fun (x : Ω_x) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) (p := 2) (μ := P) (C := 1) h_ae h_bound

lemma barronSamplingBound_integrability_pos
    {d : ℕ} {Ω_x : Type*} [MeasurableSpace Ω_x]
    (x_embed : Ω_x → EuclideanSpace ℝ (Fin d)) (hx_meas : Measurable x_embed)
    (x : Ω_x) (μ : Measure (Fin (d + 1) → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun (w : Fin (d + 1) → ℝ) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) μ := by
  have h_meas_x : Measurable (fun (w : Fin (d + 1) → ℝ) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) := by
    have h1 : Continuous (fun wb : (Fin (d + 1) → ℝ) => inner ℝ (extractWeights wb) (x_embed x) - extractBias wb) := by
      have hcw : Continuous (fun wb : (Fin (d + 1) → ℝ) => extractWeights wb) := by
        apply Continuous.comp (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
        apply continuous_pi
        intro j
        exact continuous_apply _
      have hcb : Continuous (fun wb : (Fin (d + 1) → ℝ) => extractBias wb) := continuous_apply _
      exact (hcw.inner continuous_const).sub hcb
    exact thresholdActivation_meas.comp h1.measurable
  have h_ae : AEStronglyMeasurable (fun (w : Fin (d + 1) → ℝ) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) μ := h_meas_x.aestronglyMeasurable
  have h_bound : ∀ᵐ (w : Fin (d + 1) → ℝ) ∂μ, ‖thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)‖ ≤ 1 := by
    filter_upwards [] with w
    have h_ta := thresholdActivation_bound (inner ℝ (extractWeights w) (x_embed x) - extractBias w)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h_mem : MemLp (fun (w : Fin (d + 1) → ℝ) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) 1 μ :=
    MemLp.of_bound (f := fun (w : Fin (d + 1) → ℝ) => thresholdActivation (inner ℝ (extractWeights w) (x_embed x) - extractBias w)) (p := 1) (μ := μ) (C := 1) h_ae h_bound
  exact h_mem.integrable le_rfl

lemma barronSamplingBound_hB
    {d : ℕ} {Ω_x : Type*} [MeasurableSpace Ω_x]
    (x_embed : Ω_x → EuclideanSpace ℝ (Fin d)) (hx_meas : Measurable x_embed)
    (P : Measure Ω_x) [IsProbabilityMeasure P]
    (w : Fin (d + 1) → ℝ) :
    ∫ (x : Ω_x), (thresholdActivation (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ w j.castSucc)) (x_embed x) - w (Fin.last d))) ^ 2 ∂P ≤ 1 := by
  have h_L2 := barronSamplingBound_L2 x_embed hx_meas P w
  have h_int_bound : ∫ (x : Ω_x), (thresholdActivation (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ w j.castSucc)) (x_embed x) - w (Fin.last d))) ^ 2 ∂P ≤ ∫ (x : Ω_x), (1 : ℝ) ∂P := by
    apply integral_mono
    · exact MemLp.integrable_sq h_L2
    · exact integrable_const 1
    · intro x
      have h1 := thresholdActivation_bound (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ w j.castSucc)) (x_embed x) - w (Fin.last d))
      nlinarith
  have h_int_1 : ∫ (x : Ω_x), (1 : ℝ) ∂P = 1 := by simp
  linarith

/-- **Barron's sampling bound** (combining Theorem 3.1 + Lemma 3.2).
If f has barronNorm f ≤ C and P is a probability measure supported on ‖x‖ ≤ 1, then
for any k ≥ 1 there exist (w₁, b₁, s₁), …, (wₖ, bₖ, sₖ) such that the threshold net

  f̂(x) := f(0) + (2C/k) ∑ᵢ sᵢ · 1[wᵢᵀx ≥ bᵢ]

satisfies the L₂(P) error bound

  ‖f - f̂‖²_{L₂(P)} ≤ 4C² / k.

In particular, to achieve error ε, it suffices to take k ≥ 4C²/ε². -/
theorem barronSamplingBound
    {d : ℕ}
    {f : (EuclideanSpace ℝ (Fin d)) → ℝ}
    {C : ℝ} (hC : 0 < C)
    (hf_cont : Continuous f)
    (hf : f ∈ BarronNorm.BarronClass C d)
    (hf_L1 : Integrable f volume)
    (hfhat_L1 : Integrable (BarronNorm.fourierTransform f) volume)
    {Ω_x : Type*} {mΩ_x : MeasurableSpace Ω_x}
    (P : Measure Ω_x) [IsProbabilityMeasure P]
    (x_embed : Ω_x → EuclideanSpace ℝ (Fin d)) (hx_meas : Measurable x_embed) (hx_unit : ∀ ω, ‖x_embed ω‖ ≤ 1)
    {k : ℕ} (hk : 0 < k) :
    ∃ (weights : Fin k → EuclideanSpace ℝ (Fin d))
      (biases : Fin k → ℝ)
      (signs : Fin k → ℝ),
      (∫ ω, (f (x_embed ω) - (f 0 + (2 * C / k) * ∑ i, signs i *
        thresholdActivation (inner ℝ (weights i) (x_embed ω) - biases i))) ^ 2 ∂P)
          ≤ 4 * C ^ 2 / k := by
  have h_barron := BarronNorm.barronTheorem hf_cont hf_L1 hfhat_L1 hf.1
  rcases h_barron with ⟨net, h_mass, h_eval⟩
  have h_mu_non_zero : net.measure = 0 ∨ net.measure ≠ 0 := eq_or_ne net.measure 0
  rcases h_mu_non_zero with h_mu_zero | h_mu_ne_zero
  · use fun _ => 0, fun _ => 0, fun _ => 0
    simp only [inner_zero_left, sub_self, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    have h_f_eq : ∀ ω, f (x_embed ω) = f 0 := by
      intro ω
      have hx := hx_unit ω
      have heq := h_eval (x_embed ω) hx
      have heval0 : InfiniteWidthNetwork.eval thresholdActivation net (fun (wb : Fin (d + 1) → ℝ) ↦ thresholdActivation (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ wb j.castSucc)) (x_embed ω) - wb (Fin.last d))) = 0 := by
        dsimp [InfiniteWidthNetwork.eval, signedIntegral]
        rw [h_mu_zero, MeasureTheory.SignedMeasure.toJordanDecomposition_zero]
        simp
      rw [heval0] at heq
      linarith
    have h_int_zero : (∫ (ω : Ω_x), (f (x_embed ω) - f 0) ^ 2 ∂P) = 0 := by
      have : (fun ω => (f (x_embed ω) - f 0) ^ 2) = (fun ω => 0) := by
        ext ω
        rw [h_f_eq ω, sub_self, sq, zero_mul]
      rw [this, integral_zero]
    rw [h_int_zero]
    positivity
  · let g : (Fin (d + 1) → ℝ) → Ω_x → ℝ := fun wb ω ↦
      thresholdActivation (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ wb j.castSucc)) (x_embed ω) - wb (Fin.last d))
    have hg_meas : Measurable (Function.uncurry g) := barronSamplingBound_measurability x_embed hx_meas
    have hg_L2 : ∀ w, MemLp (g w) 2 P := barronSamplingBound_L2 x_embed hx_meas P
    have hg_int_pos : ∀ x, Integrable (fun (w : Fin (d + 1) → ℝ) => g w x) net.measure.toJordanDecomposition.posPart := fun x => barronSamplingBound_integrability_pos x_embed hx_meas x _
    have hg_int_neg : ∀ x, Integrable (fun (w : Fin (d + 1) → ℝ) => g w x) net.measure.toJordanDecomposition.negPart := fun x => barronSamplingBound_integrability_pos x_embed hx_meas x _
    have hB : ∀ w ∈ (Set.univ : Set (Fin (d + 1) → ℝ)), ∫ (x : Ω_x), g w x ^ 2 ∂P ≤ 1 := fun (w : Fin (d + 1) → ℝ) _ => barronSamplingBound_hB x_embed hx_meas P w
    have h_maurey := maureySamplingSignedMeasure P h_mu_ne_zero MeasurableSet.univ (by simp) g hg_meas hg_L2 hg_int_pos hg_int_neg hB hk
    rcases h_maurey with ⟨ws, hws_univ, hws_bound⟩
    let M := totalMass net.measure
    let weights : Fin k → EuclideanSpace ℝ (Fin d) := fun i ↦ (EuclideanSpace.equiv (Fin d) ℝ).symm (fun j ↦ (ws i).1 j.castSucc)
    let biases : Fin k → ℝ := fun i ↦ (ws i).1 (Fin.last d)
    let signs : Fin k → ℝ := fun i ↦ signWeight (ws i).2 * M / (2 * C)
    use weights, biases, signs
    have h_integrand_eq : ∀ ω, (f (x_embed ω) - (f 0 + (2 * C / k) * ∑ i, signs i *
        thresholdActivation (inner ℝ (weights i) (x_embed ω) - biases i))) =
        signedIntegral net.measure (fun w => g w ω) - (1 / k : ℝ) * ∑ i, rescaled net.measure (fun w => g w ω) (ws i) := by
      intro ω
      have heq := h_eval (x_embed ω) (hx_unit ω)
      have h_eval_eq : signedIntegral net.measure (fun w => g w ω) = f (x_embed ω) - f 0 := by
        exact heq.symm
      rw [h_eval_eq]
      have h_sum_eq : (2 * C / (k : ℝ)) * ∑ i, signs i * thresholdActivation (inner ℝ (weights i) (x_embed ω) - biases i) =
        (1 / (k : ℝ)) * ∑ i, rescaled net.measure (fun w => g w ω) (ws i) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [rescaled, signs, g, weights, biases, M]
        have hC2 : 2 * C ≠ 0 := by linarith
        have eq1 : (2 * C / ↑k) * (signWeight (ws i).2 * totalMass net.measure / (2 * C) *
          thresholdActivation (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm fun j => (ws i).1 (Fin.castSucc j)) (x_embed ω) - (ws i).1 (Fin.last d))) =
          ((2 * C) * (2 * C)⁻¹) * ((signWeight (ws i).2 * totalMass net.measure) * thresholdActivation (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm fun j => (ws i).1 (Fin.castSucc j)) (x_embed ω) - (ws i).1 (Fin.last d)) / ↑k) := by ring
        rw [eq1, mul_inv_cancel₀ hC2, one_mul]
        ring
      rw [h_sum_eq]
      linarith
    have h_int_eq : (∫ ω, (f (x_embed ω) - (f 0 + (2 * C / k) * ∑ i, signs i *
        thresholdActivation (inner ℝ (weights i) (x_embed ω) - biases i))) ^ 2 ∂P) =
        ∫ ω, (signedIntegral net.measure (fun w => g w ω) - (1 / k : ℝ) * ∑ i, rescaled net.measure (fun w => g w ω) (ws i)) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [h_integrand_eq ω]
    rw [h_int_eq]
    have h_bound1 : M ^ 2 * 1 / k ≤ 4 * C ^ 2 / k := by
      have hm_eq : M = InfiniteWidthNetwork.mass thresholdActivation net := by
        dsimp [M, totalMass, InfiniteWidthNetwork.mass]
        have h_tv : net.measure.totalVariation Set.univ = net.measure.toJordanDecomposition.posPart Set.univ + net.measure.toJordanDecomposition.negPart Set.univ := rfl
        rw [h_tv, ENNReal.toReal_add]
        · exact measure_ne_top net.measure.toJordanDecomposition.posPart Set.univ
        · exact measure_ne_top net.measure.toJordanDecomposition.negPart Set.univ
      have hb : BarronNorm.barronNorm f ≤ C := hf.2
      have hm : M ≤ 2 * C := by linarith
      have hp : 0 ≤ M := totalMass_nonneg net.measure
      have h_sq : M ^ 2 ≤ (2 * C) ^ 2 := by
        apply sq_le_sq.mpr
        rw [abs_of_nonneg hp, abs_of_pos]
        · exact hm
        · linarith
      have : (2 * C) ^ 2 = 4 * C ^ 2 := by ring
      rw [this] at h_sq
      have h_div : M ^ 2 / (k : ℝ) ≤ 4 * C ^ 2 / (k : ℝ) := by
        apply div_le_div_of_nonneg_right h_sq
        positivity
      have : M ^ 2 * 1 / (k : ℝ) = M ^ 2 / (k : ℝ) := by ring
      rw [this]
      exact h_div
    linarith

/-- **Univariate sampling bound** (Example 3.1.1).
If g is differentiable on [0, 1] with g(0) = 0, then a threshold network
with k nodes sampled from its integral representation achieves an L₂(P) error
bounded by (1/k) * (∫₀¹ |g'(x)| dx)². -/
theorem univariateSamplingBound
    {g : ℝ → ℝ}
    (hg_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (deriv g x) x)
    (hg0 : g 0 = 0)
    (hg'_int : IntervalIntegrable (deriv g) MeasureTheory.volume 0 1)
    {Ω_x : Type*} {mΩ_x : MeasurableSpace Ω_x}
    (P : Measure Ω_x) [IsProbabilityMeasure P]
    (x_embed : Ω_x → ℝ) (hx_unit : ∀ ω, x_embed ω ∈ Set.Icc (0 : ℝ) 1)
    {k : ℕ} (hk : 0 < k) :
    ∃ (biases : Fin k → ℝ)
      (signs : Fin k → ℝ),
      (∫ ω, (g (x_embed ω) -
        (Approximation.InfiniteWidth.totalVariationCost (deriv g) / k) *
          ∑ i, signs i * thresholdActivation (x_embed ω - biases i)) ^ 2 ∂P)
        ≤ (Approximation.InfiniteWidth.totalVariationCost (deriv g)) ^ 2 / k := by
  sorry

end Approximation.Sampling

end
