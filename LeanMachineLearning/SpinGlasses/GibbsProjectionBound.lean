/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsProjectionFluctuation
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosChain

/-!
# The general Gibbs fluctuation principle (Talagrand, Theorem 1.7.11): the Taylor step

For a Gibbs measure `μ = count.tilted f` on a finite set `α` with observables `ξ_i`, `|ξ_i| ≤ 1`,
and `m` replicas, let `Q_r(s) = ∫ projSum V (u σ) v r s ∂μ^{⊗m}` where `u_ℓ i = N^{-1/2}
(ξ_i(σ_ℓ) - ⟨ξ_i⟩)`.  Then `Q_r' = sin s cos s Q_{r+1}` (a finite sum of the derivative formula of
`GaussianProjectionPath.lean`), `Q_r(0) = 0` for `r < m` (parity vanishing), and
`|Q_m| ≤ C ∑_p ∫ |pairProd T p|` uniformly in `s`.  The fencing lemma
`Real.abs_chain_zero_le_of_hasDerivAt` then gives `|Q_0(π/2)| ≤ C A / (2^m m!)`, and `Q_0(π/2)`
is `𝔼_y (⟨V(N^{-1/2} ∑ y_i ξ̇_i)⟩)^m`.

## Main declarations

* `SpinGlasses.centeredData`: the centered scaled replica data `u`.
* `SpinGlasses.hasDerivAt_gibbsProjSum`: the derivative of the Gibbs-averaged path functional.
* `SpinGlasses.gibbs_fluctuation_abs_le`: the bound on `|𝔼_y ⟨V(Ṡ)⟩^m|` by the Gibbs average of the
  products of Gram entries.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

section Gibbs

attribute [local instance] Fintype.ofFinite

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ)

/-- The centered scaled replica data `u_ℓ i = N^{-1/2} (ξ_i(σ_ℓ) - ⟨ξ_i⟩)`. -/
noncomputable def centeredData {m : ℕ} (f : α → ℝ) (σ : Fin m → α) : Fin m → Fin N → ℝ :=
  fun l i => (Real.sqrt N)⁻¹ * (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f))

/-- The Gibbs average over `m` replicas of the path functional `projSum`. -/
noncomputable def gibbsProjSum {m : ℕ} (V : ℝ → ℝ) (f : α → ℝ) (v : ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  ∫ σ : Fin m → α, projSum V (centeredData ξ f σ) v r s
    ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f)

variable {m : ℕ} {V : ℝ → ℝ}

omit [Nonempty α] in
theorem hasDerivAt_gibbsProjSum (hV : ExpTame V) (f : α → ℝ) (v : ℝ) (r : ℕ) (s : ℝ) :
    HasDerivAt (gibbsProjSum (m := m) ξ V f v r)
      (Real.sin s * Real.cos s * gibbsProjSum (m := m) ξ V f v (r + 1) s) s := by
  classical
  have hfun : gibbsProjSum (m := m) ξ V f v r = fun s => ∑ σ : Fin m → α,
      (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
        projSum V (centeredData ξ f σ) v r s := by
    funext s
    exact integral_pi_count_tilted f _
  rw [hfun]
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun (σ : Fin m → α) (s : ℝ) => (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
      projSum V (centeredData ξ f σ) v r s)
    (A' := fun σ => (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
      (Real.sin s * Real.cos s * projSum V (centeredData ξ f σ) v (r + 1) s))
    (fun σ _ => (hV.hasDerivAt_projSum (centeredData ξ f σ) v r s).const_mul _)
  refine h.congr_deriv ?_
  unfold gibbsProjSum
  rw [integral_pi_count_tilted, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem gibbsProjSum_zero_eq_zero (hV : ExpTame V) (hm : 0 < m) {r : ℕ} (hr : r < m)
    (f : α → ℝ) (v : ℝ) (hV0 : ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0) :
    gibbsProjSum (m := m) ξ V f v r 0 = 0 :=
  integral_projSum_centered_zero_eq_zero ξ V hV hm hr f v hV0

/-- Coordinates of the centered data are at most `2 / √N` in absolute value, so `u_ℓ ⬝ u_ℓ ≤ 4`. -/
theorem centeredData_dotProduct_le (hξ : ∀ i a, |ξ i a| ≤ 1) (f : α → ℝ) (σ : Fin m → α)
    (l : Fin m) : centeredData ξ f σ l ⬝ᵥ centeredData ξ f σ l ≤ 4 := by
  have hmean : ∀ i, |∫ a, ξ i a ∂(Measure.count.tilted f)| ≤ 1 := fun i => by
    have := norm_integral_le_of_norm_le_const (μ := Measure.count.tilted f) (f := ξ i) (C := 1)
      (ae_of_all _ fun a => by simpa using hξ i a)
    simpa using this
  have hcoord : ∀ i, (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f)) ^ 2 ≤ 4 := fun i => by
    have h1 := hξ i (σ l)
    have h2 := hmean i
    rw [abs_le] at h1 h2
    nlinarith
  unfold centeredData
  simp only [dotProduct]
  have : ∀ i, (Real.sqrt N)⁻¹ * (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f)) *
      ((Real.sqrt N)⁻¹ * (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f))) =
      (N : ℝ)⁻¹ * (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f)) ^ 2 := fun i => by
    rw [show ∀ x y : ℝ, x * y * (x * y) = x ^ 2 * y ^ 2 from fun x y => by ring,
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp_rw [this]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Finset.mul_sum]
    calc (N : ℝ)⁻¹ * ∑ i, (ξ i (σ l) - ∫ a, ξ i a ∂(Measure.count.tilted f)) ^ 2
        ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, (4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoord i) (by positivity)
      _ = 4 := by simp; field_simp

theorem abs_gibbsProjSum_le_of_bound {C : ℝ} {r : ℕ}
    (hC : ∀ (N' : ℕ) (u : Fin m → Fin N' → ℝ) (v s : ℝ), (∀ l, u l ⬝ᵥ u l ≤ 4) → v ^ 2 ≤ 4 →
      |projSum V u v r s| ≤ C * ∑ p : Fin r → Fin m × Fin m, |pairProd (projGram u v) p|)
    (hξ : ∀ i a, |ξ i a| ≤ 1) (f : α → ℝ) (v : ℝ) (hv : v ^ 2 ≤ 4) (s : ℝ) :
    |gibbsProjSum (m := m) ξ V f v r s| ≤
      C * ∑ p : Fin r → Fin m × Fin m, ∫ σ : Fin m → α,
        |pairProd (projGram (centeredData ξ f σ) v) p|
          ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) := by
  unfold gibbsProjSum
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ σ : Fin m → α, |projSum V (centeredData ξ f σ) v r s|
        ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f)
      ≤ ∫ σ : Fin m → α, C * ∑ p : Fin r → Fin m × Fin m,
          |pairProd (projGram (centeredData ξ f σ) v) p|
          ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) :=
        integral_mono Integrable.of_finite Integrable.of_finite fun σ =>
          hC N (centeredData ξ f σ) v s (centeredData_dotProduct_le ξ hξ f σ) hv
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ fun p _ => Integrable.of_finite]

omit [Nonempty α] in
/-- Swapping the finite Gibbs average with an integral over another space. -/
theorem integral_integral_swap_pi_count_tilted {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : α → ℝ) (G : (Fin m → α) → Ω → ℝ) (hG : ∀ σ, Integrable (G σ) P) :
    ∫ σ, ∫ ω, G σ ω ∂P ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) =
      ∫ ω, ∫ σ, G σ ω ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) ∂P := by
  classical
  simp_rw [integral_pi_count_tilted f]
  rw [integral_finsetSum _ fun σ _ => (hG σ).const_mul _]
  exact Finset.sum_congr rfl fun σ _ => (integral_const_mul _ _).symm

theorem projSum_zero_index (u : Fin m → Fin N → ℝ) (v s : ℝ) :
    projSum V u v 0 s = ∫ ω, ∏ l, V (projPath u v s ω l) ∂(projMeasure m N) := by
  simp [projSum, pairProd, pairCount]

omit [Nonempty α] in
/-- **The endpoint of the path is the `m`-th power of the Gibbs average.** -/
theorem gibbsProjSum_zero_index_pi_div_two (hV : ExpTame V) (hm : 0 < m) (f : α → ℝ) (v : ℝ) :
    gibbsProjSum (m := m) ξ V f v 0 (Real.pi / 2) =
      ∫ y : Fin N → ℝ, (∫ a, V ((fun i => (Real.sqrt N)⁻¹ *
        (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f))) ⬝ᵥ y)
          ∂(Measure.count.tilted f)) ^ m ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  classical
  set c : α → Fin N → ℝ := fun a i => (Real.sqrt N)⁻¹ *
    (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) with hc
  have hpath : ∀ (σ : Fin m → α) (ω : (Fin m → ℝ) × (Fin N → ℝ)) (l : Fin m),
      projPath (centeredData ξ f σ) v (Real.pi / 2) ω l = c (σ l) ⬝ᵥ ω.2 := fun σ ω l => by
    simp only [projPath, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add]
    rfl
  have hint : ∀ σ : Fin m → α, Integrable
      (fun ω : (Fin m → ℝ) × (Fin N → ℝ) => ∏ l, V (c (σ l) ⬝ᵥ ω.2)) (projMeasure m N) :=
    fun σ => by
      have := hV.integrable_derivProd_projPath hm (centeredData ξ f σ) v (Real.pi / 2) 0
      simpa [hpath] using this
  unfold gibbsProjSum
  simp_rw [projSum_zero_index, hpath]
  rw [integral_integral_swap_pi_count_tilted (projMeasure m N) f
    (fun σ ω => ∏ l, V (c (σ l) ⬝ᵥ ω.2)) hint]
  have hprod : ∀ ω : (Fin m → ℝ) × (Fin N → ℝ),
      ∫ σ : Fin m → α, ∏ l, V (c (σ l) ⬝ᵥ ω.2)
          ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) =
        (∫ a, V (c a ⬝ᵥ ω.2) ∂(Measure.count.tilted f)) ^ m := fun ω => by
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin m) (a : α) => V (c a ⬝ᵥ ω.2))]
    simp
  simp_rw [hprod]
  exact integral_prod_fun_snd_of_isProbabilityMeasure (Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (fun y => (∫ a, V (c a ⬝ᵥ y) ∂(Measure.count.tilted f)) ^ m)

end Gibbs

/-- **The Taylor step of Theorem 1.7.11, uniformly over a family of observables.**  Let `m ≥ 1`
and let `Cb`, `c` be explicit exponential bounds for the derivatives of order `≤ 2 m`.  There is
`C ≥ 0`, depending only on `m`, `Cb`, `c`, such that for every exponentially tame `V` obeying these
bounds, every `v² ≤ 4` with `∫ V(v t) dγ = 0`, every Gibbs measure `μ = count.tilted f` on a finite
set `α` and observables `|ξ_i| ≤ 1`,
`|𝔼_y (∫ V(N^{-1/2} ∑ y_i (ξ_i - ⟨ξ_i⟩)) dμ)^m| ≤ C ∑_p ∫ |∏_j T_{p_j}| dμ^{⊗m}`,
the sum over lists `p` of `m` pairs of replicas. -/
theorem exists_gibbs_fluctuation_abs_le {m : ℕ} (hm : 0 < m) {Cb : ℕ → ℝ} {c : ℝ}
    (hCb : ∀ j ≤ 2 * m, 0 ≤ Cb j) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℝ), ExpTame V →
      (∀ j ≤ 2 * m, ∀ x, |deriv^[j] V x| ≤ Cb j * Real.exp (c * |x|)) →
      ∀ v : ℝ, v ^ 2 ≤ 4 → ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0 →
      ∀ (N : ℕ) (α : Type) [Fintype α] [Nonempty α] [MeasurableSpace α]
      [MeasurableSingletonClass α] (ξ : Fin N → α → ℝ), (∀ i a, |ξ i a| ≤ 1) → ∀ f : α → ℝ,
      |∫ y : Fin N → ℝ, (∫ a, V ((fun i => (Real.sqrt N)⁻¹ *
          (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f))) ⬝ᵥ y)
            ∂(Measure.count.tilted f)) ^ m ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)| ≤
        C * ∑ p : Fin m → Fin m × Fin m, ∫ σ : Fin m → α,
          |pairProd (projGram (centeredData ξ f σ) v) p|
            ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_abs_projSum_le_of_bound hm m 4 hCb hc
  refine ⟨C₀ / (2 ^ m * (Nat.factorial m : ℝ)), by positivity,
    fun V hV hbd v hv hV0 N α _ _ _ _ ξ hξ f => ?_⟩
  rw [← gibbsProjSum_zero_index_pi_div_two ξ hV hm f v]
  have hchain := Real.abs_chain_zero_le_of_hasDerivAt (n := m)
    (Q := fun r s => gibbsProjSum (m := m) ξ V f v r s)
    (M := C₀ * ∑ p : Fin m → Fin m × Fin m, ∫ σ : Fin m → α,
      |pairProd (projGram (centeredData ξ f σ) v) p|
        ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f))
    (fun r s => hasDerivAt_gibbsProjSum ξ hV f v r s)
    (fun r hr => gibbsProjSum_zero_eq_zero ξ hV hm hr f v hV0)
    (fun s _ => abs_gibbsProjSum_le_of_bound ξ
      (fun N' u v' s' hu hv' => hC V hbd N' u v' s' hu hv') hξ f v hv s)
  refine hchain.trans (le_of_eq ?_)
  ring

/-- **The Taylor step of Theorem 1.7.11.**  Let `V` be exponentially tame, `m ≥ 1` and `v² ≤ 4`
with `∫ V(v t) dγ = 0`.  There is `C ≥ 0`, depending only on `V` and `m`, such that for every Gibbs
measure `μ = count.tilted f` on a finite set `α` and observables `|ξ_i| ≤ 1`,
`|𝔼_y (∫ V(N^{-1/2} ∑ y_i (ξ_i - ⟨ξ_i⟩)) dμ)^m| ≤ C ∑_p ∫ |∏_j T_{p_j}| dμ^{⊗m}`,
the sum over lists `p` of `m` pairs of replicas. -/
theorem ExpTame.gibbs_fluctuation_abs_le {V : ℝ → ℝ} (hV : ExpTame V) {m : ℕ} (hm : 0 < m)
    (v : ℝ) (hv : v ^ 2 ≤ 4) (hV0 : ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (α : Type) [Fintype α] [Nonempty α] [MeasurableSpace α]
      [MeasurableSingletonClass α] (ξ : Fin N → α → ℝ), (∀ i a, |ξ i a| ≤ 1) → ∀ f : α → ℝ,
      |∫ y : Fin N → ℝ, (∫ a, V ((fun i => (Real.sqrt N)⁻¹ *
          (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f))) ⬝ᵥ y)
            ∂(Measure.count.tilted f)) ^ m ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)| ≤
        C * ∑ p : Fin m → Fin m × Fin m, ∫ σ : Fin m → α,
          |pairProd (projGram (centeredData ξ f σ) v) p|
            ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) := by
  obtain ⟨Cb, c, hCb, hc, hbd⟩ := hV.exists_bound_upTo (2 * m)
  obtain ⟨C, hC0, hC⟩ := exists_gibbs_fluctuation_abs_le hm (fun j _ => hCb j) hc
  exact ⟨C, hC0, fun N α _ _ _ _ ξ hξ f => hC V hV hbd v hv hV0 N α ξ hξ f⟩

end SpinGlasses
