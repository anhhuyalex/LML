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

Let `μ = count.tilted f` be a Gibbs measure on a finite set `α` and `u : α → ℝ^N` a vector field
with `μ`-mean zero and `u a ⬝ u a ≤ 4` (in the application `u a i = N^{-1/2} (ξ_i(a) - ⟨ξ_i⟩)` for
observables `|ξ_i| ≤ 1`, see `dotProduct_centered_le`).  For `m` replicas put
`Q_r(s) = ∫ projSum V (u ∘ σ) v r s ∂μ^{⊗m}`.  Then `Q_r' = sin s cos s Q_{r+1}` (a finite sum of
the derivative formula of `GaussianProjectionPath.lean`), `Q_r(0) = 0` for `r < m` (parity
vanishing), and `|Q_m| ≤ C ∑_p ∫ |∏ j, T_{p_j}|` uniformly in `s`, where
`T_{l k} = u(σ_l) ⬝ u(σ_k) - v² δ_{l k}`.  The fencing lemma `Real.abs_chain_zero_le_of_hasDerivAt`
then gives `|Q_0(π/2)| ≤ C A / (2^m m!)`, and `Q_0(π/2)` is `𝔼_y (⟨V(u ⬝ y)⟩)^m`.

## Main declarations

* `SpinGlasses.hasDerivAt_gibbsProjSum`: the derivative of the Gibbs-averaged path functional.
* `SpinGlasses.exists_gibbs_fluctuation_abs_le`: the bound on `|𝔼_y ⟨V(u ⬝ y)⟩^m|` by the Gibbs
  average of the products of Gram entries, with a constant depending only on explicit derivative
  bounds for `V`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

section Gibbs

attribute [local instance] Fintype.ofFinite

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (u : α → Fin N → ℝ)

/-- The Gibbs average over `m` replicas of the path functional `projSum`. -/
noncomputable def gibbsProjSum {m : ℕ} (V : ℝ → ℝ) (f : α → ℝ) (v : ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  ∫ σ : Fin m → α, projSum V (fun l => u (σ l)) v r s
    ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f)

variable {m : ℕ} {V : ℝ → ℝ}

omit [Nonempty α] in
theorem hasDerivAt_gibbsProjSum (hV : ExpTame V) (f : α → ℝ) (v : ℝ) (r : ℕ) (s : ℝ) :
    HasDerivAt (gibbsProjSum (m := m) u V f v r)
      (Real.sin s * Real.cos s * gibbsProjSum (m := m) u V f v (r + 1) s) s := by
  classical
  have hfun : gibbsProjSum (m := m) u V f v r = fun s => ∑ σ : Fin m → α,
      (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) * projSum V (fun l => u (σ l)) v r s := by
    funext s
    exact integral_pi_count_tilted f _
  rw [hfun]
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun (σ : Fin m → α) (s : ℝ) => (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
      projSum V (fun l => u (σ l)) v r s)
    (A' := fun σ => (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
      (Real.sin s * Real.cos s * projSum V (fun l => u (σ l)) v (r + 1) s))
    (fun σ _ => (hV.hasDerivAt_projSum (fun l => u (σ l)) v r s).const_mul _)
  refine h.congr_deriv ?_
  unfold gibbsProjSum
  rw [integral_pi_count_tilted, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

omit [Nonempty α] in
theorem gibbsProjSum_zero_eq_zero (hV : ExpTame V) (hm : 0 < m) {r : ℕ} (hr : r < m)
    (f : α → ℝ) (hu : ∀ j, ∫ a, u a j ∂(Measure.count.tilted f) = 0) (v : ℝ)
    (hV0 : ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0) :
    gibbsProjSum (m := m) u V f v r 0 = 0 :=
  integral_projSum_centered_zero_eq_zero u V hV hm hr f hu v hV0

/-- Coordinates of the centered data are at most `2 / √N` in absolute value, so `u a ⬝ u a ≤ 4`. -/
theorem dotProduct_centered_le (ξ : Fin N → α → ℝ) (hξ : ∀ i a, |ξ i a| ≤ 1) (f : α → ℝ)
    (hu : ∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f)))
    (a : α) : u a ⬝ᵥ u a ≤ 4 := by
  have hmean : ∀ i, |∫ b, ξ i b ∂(Measure.count.tilted f)| ≤ 1 := fun i => by
    have := norm_integral_le_of_norm_le_const (μ := Measure.count.tilted f) (f := ξ i) (C := 1)
      (ae_of_all _ fun a => by simpa using hξ i a)
    simpa using this
  have hcoord : ∀ i, (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) ^ 2 ≤ 4 := fun i => by
    have h1 := hξ i a
    have h2 := hmean i
    rw [abs_le] at h1 h2
    nlinarith
  have : ∀ i, u a i * u a i =
      (N : ℝ)⁻¹ * (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) ^ 2 := fun i => by
    rw [hu, show ∀ x y : ℝ, x * y * (x * y) = x ^ 2 * y ^ 2 from fun x y => by ring,
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp only [dotProduct, this]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Finset.mul_sum]
    calc (N : ℝ)⁻¹ * ∑ i, (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) ^ 2
        ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, (4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoord i) (by positivity)
      _ = 4 := by simp; field_simp

omit [Nonempty α] in
theorem abs_gibbsProjSum_le_of_bound {C : ℝ} {r : ℕ}
    (hC : ∀ (N' : ℕ) (w : Fin m → Fin N' → ℝ) (v s : ℝ), (∀ l, w l ⬝ᵥ w l ≤ 4) → v ^ 2 ≤ 4 →
      |projSum V w v r s| ≤
        C * ∑ p : Fin r → Fin m × Fin m,
          |∏ j, (w (p j).1 ⬝ᵥ w (p j).2 - if (p j).1 = (p j).2 then v ^ 2 else 0)|)
    (hu : ∀ a, u a ⬝ᵥ u a ≤ 4) (f : α → ℝ) (v : ℝ) (hv : v ^ 2 ≤ 4) (s : ℝ) :
    |gibbsProjSum (m := m) u V f v r s| ≤
      C * ∑ p : Fin r → Fin m × Fin m, ∫ σ : Fin m → α,
        |∏ j, (u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0)|
          ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) := by
  unfold gibbsProjSum
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ σ : Fin m → α, |projSum V (fun l => u (σ l)) v r s|
        ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f)
      ≤ ∫ σ : Fin m → α, C * ∑ p : Fin r → Fin m × Fin m,
          |∏ j, (u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0)|
          ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) :=
        integral_mono Integrable.of_finite Integrable.of_finite fun σ =>
          hC N (fun l => u (σ l)) v s (fun l => hu (σ l)) hv
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

theorem projSum_zero_index (w : Fin m → Fin N → ℝ) (v s : ℝ) :
    projSum V w v 0 s = ∫ ω, ∏ l, V
      (Real.cos s * (v * ω.1 l) + Real.sin s * (w l ⬝ᵥ ω.2))
      ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  simp [projSum, pairCount]

omit [Nonempty α] in
/-- **The endpoint of the path is the `m`-th power of the Gibbs average.** -/
theorem gibbsProjSum_zero_index_pi_div_two (hV : ExpTame V) (hm : 0 < m) (f : α → ℝ) (v : ℝ) :
    gibbsProjSum (m := m) u V f v 0 (Real.pi / 2) =
      ∫ y : Fin N → ℝ, (∫ a, V (u a ⬝ᵥ y) ∂(Measure.count.tilted f)) ^ m
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  classical
  have hpath : ∀ (σ : Fin m → α) (ω : (Fin m → ℝ) × (Fin N → ℝ)) (l : Fin m),
      Real.cos (Real.pi / 2) * (v * ω.1 l) + Real.sin (Real.pi / 2) * (u (σ l) ⬝ᵥ ω.2) =
        u (σ l) ⬝ᵥ ω.2 := fun σ ω l => by
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add]
  have hint : ∀ σ : Fin m → α, Integrable
      (fun ω : (Fin m → ℝ) × (Fin N → ℝ) => ∏ l, V (u (σ l) ⬝ᵥ ω.2))
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) :=
    fun σ => by
      have := hV.integrable_derivProd_projPath hm (fun l => u (σ l)) v (Real.pi / 2) 0
      simpa [hpath] using this
  unfold gibbsProjSum
  simp_rw [projSum_zero_index, hpath]
  rw [integral_integral_swap_pi_count_tilted
    ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)) f
    (fun σ ω => ∏ l, V (u (σ l) ⬝ᵥ ω.2)) hint]
  have hprod : ∀ ω : (Fin m → ℝ) × (Fin N → ℝ),
      ∫ σ : Fin m → α, ∏ l, V (u (σ l) ⬝ᵥ ω.2)
          ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) =
        (∫ a, V (u a ⬝ᵥ ω.2) ∂(Measure.count.tilted f)) ^ m := fun ω => by
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin m) (a : α) => V (u a ⬝ᵥ ω.2))]
    simp
  simp_rw [hprod]
  exact integral_prod_fun_snd_of_isProbabilityMeasure (Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (fun y => (∫ a, V (u a ⬝ᵥ y) ∂(Measure.count.tilted f)) ^ m)

end Gibbs

/-- **The Taylor step of Theorem 1.7.11, uniformly over a family of observables.**  Let `m ≥ 1`
and let `Cb`, `c` be explicit exponential bounds for the derivatives of order `≤ 2 m`.  There is
`C ≥ 0`, depending only on `m`, `Cb`, `c`, such that for every exponentially tame `V` obeying these
bounds, every `v² ≤ 4` with `∫ V(v t) dγ = 0`, every Gibbs measure `μ = count.tilted f` on a finite
set `α` and every vector field `u : α → ℝ^N` with `u a ⬝ u a ≤ 4` and `μ`-mean zero,
`|𝔼_y (∫ V(u ⬝ y) dμ)^m| ≤ C ∑_p ∫ |∏_j T_{p_j}| dμ^{⊗m}`,
the sum over lists `p` of `m` pairs of replicas. -/
theorem exists_gibbs_fluctuation_abs_le {m : ℕ} (hm : 0 < m) {Cb : ℕ → ℝ} {c : ℝ}
    (hCb : ∀ j ≤ 2 * m, 0 ≤ Cb j) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℝ), ExpTame V →
      (∀ j ≤ 2 * m, ∀ x, |deriv^[j] V x| ≤ Cb j * Real.exp (c * |x|)) →
      ∀ v : ℝ, v ^ 2 ≤ 4 → ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0 →
      ∀ (N : ℕ) (α : Type) [Fintype α] [Nonempty α] [MeasurableSpace α]
      [MeasurableSingletonClass α] (u : α → Fin N → ℝ), (∀ a, u a ⬝ᵥ u a ≤ 4) → ∀ f : α → ℝ,
      (∀ j, ∫ a, u a j ∂(Measure.count.tilted f) = 0) →
      |∫ y : Fin N → ℝ, (∫ a, V (u a ⬝ᵥ y) ∂(Measure.count.tilted f)) ^ m
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)| ≤
        C * ∑ p : Fin m → Fin m × Fin m, ∫ σ : Fin m → α,
          |∏ j, (u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0)|
            ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_abs_projSum_le_of_bound hm m 4 hCb hc
  refine ⟨C₀ / (2 ^ m * (Nat.factorial m : ℝ)), by positivity,
    fun V hV hbd v hv hV0 N α _ _ _ _ u hu4 f hu0 => ?_⟩
  rw [← gibbsProjSum_zero_index_pi_div_two u hV hm f v]
  have hchain := Real.abs_chain_zero_le_of_hasDerivAt (n := m)
    (Q := fun r s => gibbsProjSum (m := m) u V f v r s)
    (M := C₀ * ∑ p : Fin m → Fin m × Fin m, ∫ σ : Fin m → α,
      |∏ j, (u (σ (p j).1) ⬝ᵥ u (σ (p j).2) - if (p j).1 = (p j).2 then v ^ 2 else 0)|
        ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f))
    (fun r s => hasDerivAt_gibbsProjSum u hV f v r s)
    (fun r hr => gibbsProjSum_zero_eq_zero u hV hm hr f hu0 v hV0)
    (fun s _ => abs_gibbsProjSum_le_of_bound u
      (fun N' w v' s' hw hv' => hC V hbd N' w v' s' hw hv') hu4 f v hv s)
  refine hchain.trans (le_of_eq ?_)
  ring

end SpinGlasses
