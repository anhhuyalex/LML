/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.InnerProductSpace.GramIsometry
public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.CholeskyInfinite
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.ProbabilityMeasureMeasurable
public import LeanMachineLearning.ForMathlib.Probability.EmpiricalConvergence
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Measurable reconstruction of the Dovbysh–Sudakov measure (Panchenko §1.5, Lemma 1.7)

Let `(h_l, a_l)_{l ≥ 0}` be i.i.d. from a probability measure `η` on `H × ℝ` with `a ≥ 0` almost
surely, `H` a separable Hilbert space, and let `R_{l,l'} = ⟪h_l, h_l'⟫ + δ_{l,l'} a_l`.  Lemma 1.7
says that `η` is, up to an isometry of `H`, a measurable function of the array `R` alone.

The proof has three steps, each formalized here.

1. **The diagonal residual `a₀` is a measurable function of `R`.**  With `g_l = (h_l, √a_l e_l)`,
   `e_l` orthonormal, the squared distance from `g₀` to the span of the other `g_l` is `a₀`: the
   point `h₀` of the support of `η` is approximated by averages of many `h_l` close to it, and
   averaging kills the orthonormal jitter.  We do not construct the vectors `g_l`: the quadratic
   form `‖g₀ - ∑ c_j g_{j+1}‖²` equals `a₀ + ‖h₀ - ∑ c_j h_{j+1}‖² + ∑ c_j² a_{j+1}`, which is
   computed from the entries of `R`, and its infimum over rational weights `c` is `a₀`
   (`iInf_quadForm_eq`).  Exchanging the indices `0` and `l` gives every `a_l`; off the diagonal
   `⟪h_l, h_l'⟫ = R_{l,l'}` and on it `⟪h_l, h_l⟫ = R_{l,l} - a_l`
   (`exists_measurable_gram_recovery`).
2. **Realization.**  The Gram matrix `Γ` of the `h_l` is positive semidefinite, so the rows
   `x_l = ∑_{k ≤ l} L_{l,k} ε_k` of its Cholesky factor (`Matrix.cholInf`, placed along an
   orthonormal sequence `ε`) are measurable functions of `R` with Gram matrix `Γ`.  Vectors with
   the same Gram matrix are related by a linear isometry, defined on the whole space once the
   target contains a copy of `H` for the orthogonal complement of their span
   (`exists_linearIsometry_of_inner_eq`).
3. **Limit.**  The empirical measures of the i.i.d. sample converge weakly to `η` almost surely
   (Varadarajan, `ProbabilityTheory.ae_tendsto_empiricalMeasure`), hence those of the reconstructed
   points `(x_l, a_l)` converge to the image of `η` under the isometry.  The weak limit of
   empirical measures of measurable random points in a Polish space is a measurable function of
   the points on the (measurable) set where it exists
   (`MeasureTheory.exists_measurable_tendsto_empiricalMeasure`).

## Main declarations

* `SpinGlasses.exists_measurable_diag_residual`: `a₀ = A R` almost surely, for a Borel `A`.
* `SpinGlasses.exists_measurable_gram_recovery`: the residuals `a_l` and the Gram matrix of the
  `h_l` are Borel functions of `R`.
* `SpinGlasses.exists_measurable_dovbysh_reconstruction`: Lemma 1.7.

## Deviations from the book

The book's `U` is an orthogonal transformation of `H`; here `U` is a linear isometry of `H` into
`H × H'` (with the `ℓ²` product norm), because an isometry `H → H'` need not exist when the
orthogonal complement of the span of the `h_l` is larger than that of the span of the `x_l`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Set TopologicalSpace
open scoped RealInnerProductSpace Topology

namespace SpinGlasses

section Diagonal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The quadratic form `‖g₀ - ∑_j c_j g_{j+1}‖²`, computed from the entries of an array
`R = (⟪g_l, g_l'⟫)`, for rational weights `c` on a finite set `s` of indices (shifted by one). -/
private noncomputable def quadForm (R : ℕ → ℕ → ℝ) (p : Σ s : Finset ℕ, s → ℚ) : ℝ :=
  R 0 0 - 2 * ∑ j : p.1, (p.2 j : ℝ) * R 0 (j + 1) +
    ∑ j : p.1, ∑ k : p.1, (p.2 j : ℝ) * (p.2 k : ℝ) * R (j + 1) (k + 1)

/-- For the Gram array of the vectors `g_l = (h_l, √(a_l) e_l)` (`e_l` orthonormal), the form
`quadForm` is `a₀ + ‖h₀ - ∑ c_j h_{j+1}‖² + ∑ c_j² a_{j+1}`: the orthonormal jitter contributes
the last term. -/
private lemma quadForm_eq (h : ℕ → H) (a : ℕ → ℝ) (p : Σ s : Finset ℕ, s → ℚ) :
    quadForm (fun l l' => ⟪h l, h l'⟫ + if l = l' then a l else 0) p =
      a 0 + ‖h 0 - ∑ j : p.1, (p.2 j : ℝ) • h (j + 1)‖ ^ 2 +
        ∑ j : p.1, (p.2 j : ℝ) ^ 2 * a (j + 1) := by
  obtain ⟨s, c⟩ := p
  have h1 : ‖h 0 - ∑ j : s, (c j : ℝ) • h (j + 1)‖ ^ 2 =
      ⟪h 0, h 0⟫ - 2 * ∑ j : s, (c j : ℝ) * ⟪h 0, h (j + 1)⟫ +
        ∑ j : s, ∑ k : s, (c j : ℝ) * (c k : ℝ) * ⟪h (j + 1), h (k + 1)⟫ := by
    have hs := norm_sum_smul_sq (univ : Finset s) (fun j => (c j : ℝ)) fun j => h (j + 1)
    rw [norm_sub_sq_real, hs, inner_sum]
    simp only [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hdiag : ∑ j : s, ∑ k : s, (c j : ℝ) * (c k : ℝ) *
        ((fun l l' => ⟪h l, h l'⟫ + if l = l' then a l else 0) (j + 1) (k + 1)) =
      ∑ j : s, ∑ k : s, (c j : ℝ) * (c k : ℝ) * ⟪h (j + 1), h (k + 1)⟫ +
        ∑ j : s, (c j : ℝ) ^ 2 * a (j + 1) := by
    simp only [mul_add, sum_add_distrib, Nat.add_right_cancel_iff]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    simp [pow_two, mul_assoc]
  rw [quadForm, h1, hdiag]
  simp only
  simp
  ring

/-- **The diagonal residual is a rational infimum.**  If `(h₀, a₀)` is a cluster point of the
sequence `(h_l, a_l)` (and `a ≥ 0`), then `a₀` is the infimum of `quadForm R` over rational weights,
where `R` is the Gram array of the `h_l` with `a_l` added on the diagonal.  Indeed `quadForm` is
`a₀ + ‖h₀ - ∑ c_j h_{j+1}‖² + ∑ c_j² a_{j+1}` (`quadForm_eq`) and the average of `m` terms close
to `(h₀, a₀)` makes the last two terms small. -/
private lemma iInf_quadForm_eq (h : ℕ → H) (a : ℕ → ℝ) (ha : ∀ l, 0 ≤ a l)
    (hclu : MapClusterPt (h 0, a 0) atTop fun l => (h l, a l)) :
    ⨅ p : (Σ s : Finset ℕ, s → ℚ),
        quadForm (fun l l' => ⟪h l, h l'⟫ + if l = l' then a l else 0) p = a 0 := by
  set R : ℕ → ℕ → ℝ := fun l l' => ⟪h l, h l'⟫ + if l = l' then a l else 0 with hR
  have hge : ∀ p, a 0 ≤ quadForm R p := fun p => by
    rw [hR, quadForm_eq]
    have := sum_nonneg fun j (_ : j ∈ (univ : Finset p.1)) =>
      mul_nonneg (sq_nonneg (p.2 j : ℝ)) (ha (j + 1))
    nlinarith [sq_nonneg ‖h 0 - ∑ j : p.1, (p.2 j : ℝ) • h (j + 1)‖]
  refine le_antisymm ?_ (le_ciInf hge)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  suffices ∃ p, quadForm R p ≤ a 0 + ε from
    let ⟨p, hp⟩ := this
    (ciInf_le ⟨a 0, fun _ ⟨q, hq⟩ => hq ▸ hge q⟩ p).trans hp
  -- a set of `m` indices whose terms are `δ`-close to `(h₀, a₀)`
  set δ : ℝ := min 1 (ε / 3) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_gt (3 * (a 0 + 1) / ε)
  have hmpos : (0 : ℝ) < m := lt_of_le_of_lt (by have := ha 0; positivity) hm
  have hfreq : ∃ᶠ l in atTop, (h l, a l) ∈ Metric.ball (h 0, a 0) δ :=
    mapClusterPt_iff_frequently.1 hclu _ (Metric.ball_mem_nhds _ hδpos)
  have hinf : {i : ℕ | (h (i + 1), a (i + 1)) ∈ Metric.ball (h 0, a 0) δ}.Infinite := by
    rw [← Nat.frequently_atTop_iff_infinite, frequently_atTop]
    rw [frequently_atTop] at hfreq
    intro N
    obtain ⟨l, hl, hlP⟩ := hfreq (N + 1)
    exact ⟨l - 1, by omega, by simpa [Nat.sub_add_cancel (by omega : 1 ≤ l)] using hlP⟩
  obtain ⟨s, hsub, hcard⟩ := hinf.exists_subset_card_eq m
  have hclose : ∀ j : s, ‖h 0 - h (j + 1)‖ < δ ∧ a (j + 1) ≤ a 0 + δ := fun j => by
    have : (h (j + 1), a (j + 1)) ∈ Metric.ball (h 0, a 0) δ := hsub j.2
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, Real.dist_eq] at this
    exact ⟨by rw [norm_sub_rev]; exact this.1, by linarith [(abs_lt.1 this.2).2]⟩
  refine ⟨⟨s, fun _ => (1 / m : ℚ)⟩, ?_⟩
  rw [hR, quadForm_eq]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  have hm0 : (m : ℝ) ≠ 0 := hmpos.ne'
  have hcardR : (Fintype.card s : ℝ) = m := by simp [hcard]
  have hsum1 : ∑ _j : s, (1 / (m : ℝ)) = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul, hcardR]; field_simp
  have hvec : h 0 - ∑ j : s, (1 / (m : ℝ)) • h (j + 1) =
      ∑ j : s, (1 / (m : ℝ)) • (h 0 - h (j + 1)) := by
    simp only [smul_sub, sum_sub_distrib, ← sum_smul, hsum1, one_smul]
  have hnorm : ‖h 0 - ∑ j : s, (1 / (m : ℝ)) • h (j + 1)‖ ≤ δ := by
    rw [hvec]
    exact norm_sum_smul_le (fun j _ => by positivity) hsum1 fun j _ => (hclose j).1.le
  have hsq : ‖h 0 - ∑ j : s, (1 / (m : ℝ)) • h (j + 1)‖ ^ 2 ≤ ε / 3 := by
    have h1 : δ ≤ 1 := min_le_left _ _
    have h2 : δ ≤ ε / 3 := min_le_right _ _
    calc _ ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ δ := by nlinarith
      _ ≤ ε / 3 := h2
  have hja : ∑ j : s, (1 / (m : ℝ)) ^ 2 * a (j + 1) ≤ ε / 3 := by
    calc ∑ j : s, (1 / (m : ℝ)) ^ 2 * a (j + 1)
        ≤ ∑ _j : s, (1 / (m : ℝ)) ^ 2 * (a 0 + 1) := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (by linarith [(hclose j).2, min_le_left 1 (ε / 3)])
            (by positivity)
      _ = (a 0 + 1) / m := by
          rw [sum_const, card_univ, nsmul_eq_mul, hcardR]; field_simp
      _ ≤ ε / 3 := by
          rw [div_le_iff₀ hmpos]
          rw [div_lt_iff₀ hε] at hm
          nlinarith
  linarith

/-- A rational quadratic form in the entries of an array is measurable in the array. -/
private lemma measurable_quadForm (p : Σ s : Finset ℕ, s → ℚ) :
    Measurable fun R : ℕ → ℕ → ℝ => quadForm R p := by
  unfold quadForm
  fun_prop

end Diagonal

section Sample

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H]

/-- **The diagonal residual `a₀` is a measurable function of the array.**  For an i.i.d. sample
`(h_l, a_l)_l` from a law `η` on `H × ℝ` with `a ≥ 0`, let `R_{l,l'} = ⟪h_l, h_l'⟫ + δ_{l,l'} a_l`.
Then `a₀ = A R` almost surely, for an explicit Borel function `A` of the array: the infimum over
rational weights of the quadratic form `‖g₀ - ∑ c_j g_{j+1}‖²` computed from the entries of `R`
(`iInf_quadForm_eq`).  The almost sure input is that `(h₀, a₀)` lies in the support of `η`, hence is
a cluster point of the sample (`ProbabilityTheory.ae_forall_mapClusterPt_of_mem_support`). -/
theorem exists_measurable_diag_residual (η : Measure (H × ℝ)) [IsProbabilityMeasure η]
    (hη : ∀ᵐ q ∂η, 0 ≤ q.2) :
    ∃ A : (ℕ → ℕ → ℝ) → ℝ, Measurable A ∧
      ∀ᵐ ha ∂(Measure.infinitePi fun _ : ℕ => η),
        A (fun l l' => ⟪(ha l).1, (ha l').1⟫ + if l = l' then (ha l).2 else 0) = (ha 0).2 := by
  refine ⟨fun R => ⨅ p : (Σ s : Finset ℕ, s → ℚ), quadForm R p,
    Measurable.iInf measurable_quadForm, ?_⟩
  have hev := fun l : ℕ => measurePreserving_eval_infinitePi (fun _ : ℕ => η) l
  filter_upwards [ae_forall_mapClusterPt_of_mem_support η,
    (hev 0).quasiMeasurePreserving.ae (Measure.support_mem_ae (μ := η)),
    ae_all_iff.2 fun l => (hev l).quasiMeasurePreserving.ae hη] with ha hclu hsupp hnn
  exact iInf_quadForm_eq (fun l => (ha l).1) (fun l => (ha l).2) hnn (hclu _ hsupp)

/-- **The diagonal residuals `a_l` and the Gram matrix of the `h_l` are measurable functions of
the array.**  In the situation of `exists_measurable_diag_residual`, there are Borel functions
`a' l` and `Γ · l l'` of the array with `a' l R = a_l` and `Γ R l l' = ⟪h_l, h_l'⟫` almost
surely: `a' l` applies the function `A` of `exists_measurable_diag_residual` to the array with the
indices `0` and `l` exchanged (the law of the sample is invariant under this exchange), and off the
diagonal `⟪h_l, h_l'⟫ = R l l'` while on the diagonal `⟪h_l, h_l⟫ = R l l - a_l`. -/
theorem exists_measurable_gram_recovery (η : Measure (H × ℝ)) [IsProbabilityMeasure η]
    (hη : ∀ᵐ q ∂η, 0 ≤ q.2) :
    ∃ (a' : ℕ → (ℕ → ℕ → ℝ) → ℝ) (Γ : (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ),
      (∀ l, Measurable (a' l)) ∧ (∀ l l', Measurable fun R => Γ R l l') ∧
      ∀ᵐ ha ∂(Measure.infinitePi fun _ : ℕ => η), ∀ l l',
        (a' l fun l l' => ⟪(ha l).1, (ha l').1⟫ + if l = l' then (ha l).2 else 0) = (ha l).2 ∧
        (Γ (fun l l' => ⟪(ha l).1, (ha l').1⟫ + if l = l' then (ha l).2 else 0) l l') =
          ⟪(ha l).1, (ha l').1⟫ := by
  obtain ⟨A, hA, hAe⟩ := exists_measurable_diag_residual η hη
  refine ⟨fun l R => A fun i j => R (Equiv.swap 0 l i) (Equiv.swap 0 l j),
    fun R l l' => if l = l' then R l l - A (fun i j => R (Equiv.swap 0 l i) (Equiv.swap 0 l j))
      else R l l', fun l => hA.comp (by fun_prop), fun l l' => ?_, ?_⟩
  · by_cases hll : l = l'
    · simp only [hll, ite_true]
      have := hA.comp (show Measurable fun R : ℕ → ℕ → ℝ =>
        fun i j => R (Equiv.swap 0 l i) (Equiv.swap 0 l j) by fun_prop)
      fun_prop
    · simp only [hll, ite_false]
      fun_prop
  · have hall : ∀ l : ℕ, ∀ᵐ ha ∂(Measure.infinitePi fun _ : ℕ => η),
        (A fun i j => ⟪(ha (Equiv.swap 0 l i)).1, (ha (Equiv.swap 0 l j)).1⟫ +
          if i = j then (ha (Equiv.swap 0 l i)).2 else 0) = (ha l).2 := fun l => by
      filter_upwards [(Measure.measurePreserving_comp_equiv_infinitePi η
        (Equiv.swap 0 l)).quasiMeasurePreserving.ae hAe] with ha hha
      simpa using hha
    filter_upwards [ae_all_iff.2 hall] with ha hha l l'
    have hb := hha l
    refine ⟨by simpa using hb, ?_⟩
    by_cases hll : l = l'
    · subst hll
      simp [hb]
    · simp [hll]

end Sample

section Reconstruction

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup H']
  [InnerProductSpace ℝ H'] [CompleteSpace H'] [SeparableSpace H'] [MeasurableSpace H']
  [BorelSpace H']

/-- **Lemma 1.7 (Panchenko §1.5), measurable reconstruction of the Dovbysh–Sudakov measure.**
Let `(h_l, a_l)_l` be i.i.d. from a law `η` on `H × ℝ` with `a ≥ 0` almost surely and let
`R_{l,l'} = ⟪h_l, h_l'⟫ + δ_{l,l'} a_l`.  Then there is a measurable map `η'` from arrays to
probability measures such that, almost surely, `η' R` is the image of `η` under
`(h, a) ↦ (U h, a)` for a linear isometry `U` (depending on the sample).  Thus `η` is recovered, up
to an isometry, as a measurable function of the array `R` alone.

The target `WithLp 2 (H × H')` contains a copy of `H'` (carrying an orthonormal sequence `ε`) in
which the reconstructed vectors are placed: they are the rows `x_l = ∑_{k ≤ l} L_{l,k} ε_k` of the
Cholesky factor of the Gram matrix `Γ` of the `h_l`, and the Gram matrix `Γ` and the residuals `a_l`
are measurable functions of `R` (`exists_measurable_gram_recovery`).  An isometry `H → H'` need not
exist (the orthogonal complement of the span of the `h_l` may be larger than that of the span of
the `x_l`), which is why `H` itself is added as a factor of the target. -/
theorem exists_measurable_dovbysh_reconstruction (ε : ℕ → H') (hε : Orthonormal ℝ ε)
    (η : Measure (H × ℝ)) [IsProbabilityMeasure η] (hη : ∀ᵐ q ∂η, 0 ≤ q.2) :
    ∃ η' : (ℕ → ℕ → ℝ) → ProbabilityMeasure (WithLp 2 (H × H') × ℝ), Measurable η' ∧
      ∀ᵐ ha ∂(Measure.infinitePi fun _ : ℕ => η), ∃ U : H →ₗᵢ[ℝ] WithLp 2 (H × H'),
        (η' fun l l' => ⟪(ha l).1, (ha l').1⟫ + if l = l' then (ha l).2 else 0 : Measure _) =
          η.map fun q => (U q.1, q.2) := by
  obtain ⟨a', Γ, ha'm, hΓm, hrec⟩ := exists_measurable_gram_recovery η hη
  set y : ℕ → (ℕ → ℕ → ℝ) → WithLp 2 (H × H') × ℝ := fun l R =>
    (WithLp.toLp 2 ((0 : H), ∑ k ∈ range (l + 1), Matrix.cholInf (Γ R) l k • ε k), a' l R)
    with hy
  have hΓ : Measurable Γ := measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun l' => hΓm l l'
  have hym : ∀ l, Measurable (y l) := fun l => by
    refine Measurable.prodMk ?_ (ha'm l)
    refine (WithLp.measurable_toLp 2 (H × H')).comp (measurable_const.prodMk ?_)
    exact Finset.measurable_sum _ fun k _ =>
      ((Matrix.measurable_cholInf l k).comp hΓ).smul_const _
  obtain ⟨-, g, hgm, hg⟩ := exists_measurable_tendsto_empiricalMeasure hym
  refine ⟨g, hgm, ?_⟩
  filter_upwards [hrec, ae_tendsto_empiricalMeasure η] with ha hha hconv
  set R : ℕ → ℕ → ℝ := fun l l' => ⟪(ha l).1, (ha l').1⟫ + if l = l' then (ha l).2 else 0 with hR
  have hΓR : ∀ l l', Γ R l l' = ⟪(ha l).1, (ha l').1⟫ := fun l l' => (hha l l').2
  have haR : ∀ l, a' l R = (ha l).2 := fun l => (hha l 0).1
  have hpsd : ∀ k : ℕ, (Matrix.of fun l l' : Fin k => Γ R l l').PosSemidef := fun k => by
    have e : (Matrix.of fun l l' : Fin k => Γ R l l') =
        Matrix.gram ℝ (fun l : Fin k => (ha l).1) := by
      ext l l'
      simp [Matrix.gram, hΓR]
    rw [e]
    exact Matrix.posSemidef_gram ℝ _
  obtain ⟨U, hU⟩ := exists_linearIsometry_of_inner_eq
    (h := fun l => (ha l).1) (x := fun l => ∑ k ∈ range (l + 1), Matrix.cholInf (Γ R) l k • ε k)
    fun l l' => by rw [Matrix.inner_cholInf_realization ε hε hpsd]; exact hΓR l l'
  refine ⟨U, ?_⟩
  set f : H × ℝ → WithLp 2 (H × H') × ℝ := fun q => (U q.1, q.2) with hf
  have hfc : Continuous f := by fun_prop
  have hyl : ∀ l, y l R = f (ha l) := fun l => by simp [hy, hf, hU l, haR l]
  have hfm : Measurable f := hfc.measurable
  -- the empirical measures of the reconstructed points are the images of those of the sample
  have hT : ∀ n : ℕ, (empiricalMeasure fun i : Fin (n + 1) => y i R).toProbabilityMeasure =
      ((empiricalMeasure fun i : Fin (n + 1) => ha i).toProbabilityMeasure).map f := fun n => by
    refine ProbabilityMeasure.toMeasure_injective ?_
    simp only [Measure.coe_toProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
    rw [map_empiricalMeasure _ hfm]
    simp only [Function.comp_def, hyl]
  have hlim : Tendsto
      (fun n : ℕ => (empiricalMeasure fun i : Fin (n + 1) => y i R).toProbabilityMeasure)
      atTop (𝓝 ((η.toProbabilityMeasure).map f)) := by
    simp only [hT]
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv hfc
  have hg' := tendsto_nhds_unique (hg R ⟨_, hlim⟩) hlim
  rw [hg']
  rfl

end Reconstruction

end SpinGlasses
